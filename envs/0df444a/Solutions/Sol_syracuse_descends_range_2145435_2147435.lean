-- Prove2me | solution 1 for syracuse_descends_range_2145435_2147435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:20.686324+00:00
-- url     : https://prove2.me/submissions/38ae8ed6-f97f-49cf-962d-cbeeaacaef0b

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

theorem B5799221 : Blo 2145435 5799221 := bbase (se 5 (by rfl) ⟨271838, by rfl⟩ : syracuseStep 5799221 = 543677) (by norm_num)
theorem B3866147 : Blo 2145435 3866147 := bstep (se 1 (by rfl) ⟨2899610, by rfl⟩ : syracuseStep 3866147 = 5799221) B5799221
theorem B2577431 : Blo 2145435 2577431 := bstep (se 1 (by rfl) ⟨1933073, by rfl⟩ : syracuseStep 2577431 = 3866147) B3866147
theorem B6873149 : Blo 2145435 6873149 := bstep (se 3 (by rfl) ⟨1288715, by rfl⟩ : syracuseStep 6873149 = 2577431) B2577431
theorem B4582099 : Blo 2145435 4582099 := bstep (se 1 (by rfl) ⟨3436574, by rfl⟩ : syracuseStep 4582099 = 6873149) B6873149
theorem B6109465 : Blo 2145435 6109465 := bstep (se 2 (by rfl) ⟨2291049, by rfl⟩ : syracuseStep 6109465 = 4582099) B4582099
theorem B8145953 : Blo 2145435 8145953 := bstep (se 2 (by rfl) ⟨3054732, by rfl⟩ : syracuseStep 8145953 = 6109465) B6109465
theorem B5430635 : Blo 2145435 5430635 := bstep (se 1 (by rfl) ⟨4072976, by rfl⟩ : syracuseStep 5430635 = 8145953) B8145953
theorem B3620423 : Blo 2145435 3620423 := bstep (se 1 (by rfl) ⟨2715317, by rfl⟩ : syracuseStep 3620423 = 5430635) B5430635
theorem B2413615 : Blo 2145435 2413615 := bstep (se 1 (by rfl) ⟨1810211, by rfl⟩ : syracuseStep 2413615 = 3620423) B3620423
theorem B3218153 : Blo 2145435 3218153 := bstep (se 2 (by rfl) ⟨1206807, by rfl⟩ : syracuseStep 3218153 = 2413615) B2413615
theorem B2145435 : Blo 2145435 2145435 := bstep (se 1 (by rfl) ⟨1609076, by rfl⟩ : syracuseStep 2145435 = 3218153) B3218153
theorem B4893101 : Blo 2145435 4893101 := bbase (se 3 (by rfl) ⟨917456, by rfl⟩ : syracuseStep 4893101 = 1834913) (by norm_num)
theorem B3262067 : Blo 2145435 3262067 := bstep (se 1 (by rfl) ⟨2446550, by rfl⟩ : syracuseStep 3262067 = 4893101) B4893101
theorem B2174711 : Blo 2145435 2174711 := bstep (se 1 (by rfl) ⟨1631033, by rfl⟩ : syracuseStep 2174711 = 3262067) B3262067
theorem B23196917 : Blo 2145435 23196917 := bstep (se 5 (by rfl) ⟨1087355, by rfl⟩ : syracuseStep 23196917 = 2174711) B2174711
theorem B15464611 : Blo 2145435 15464611 := bstep (se 1 (by rfl) ⟨11598458, by rfl⟩ : syracuseStep 15464611 = 23196917) B23196917
theorem B20619481 : Blo 2145435 20619481 := bstep (se 2 (by rfl) ⟨7732305, by rfl⟩ : syracuseStep 20619481 = 15464611) B15464611
theorem B27492641 : Blo 2145435 27492641 := bstep (se 2 (by rfl) ⟨10309740, by rfl⟩ : syracuseStep 27492641 = 20619481) B20619481
theorem B18328427 : Blo 2145435 18328427 := bstep (se 1 (by rfl) ⟨13746320, by rfl⟩ : syracuseStep 18328427 = 27492641) B27492641
theorem B12218951 : Blo 2145435 12218951 := bstep (se 1 (by rfl) ⟨9164213, by rfl⟩ : syracuseStep 12218951 = 18328427) B18328427
theorem B8145967 : Blo 2145435 8145967 := bstep (se 1 (by rfl) ⟨6109475, by rfl⟩ : syracuseStep 8145967 = 12218951) B12218951
theorem B10861289 : Blo 2145435 10861289 := bstep (se 2 (by rfl) ⟨4072983, by rfl⟩ : syracuseStep 10861289 = 8145967) B8145967
theorem B7240859 : Blo 2145435 7240859 := bstep (se 1 (by rfl) ⟨5430644, by rfl⟩ : syracuseStep 7240859 = 10861289) B10861289
theorem B4827239 : Blo 2145435 4827239 := bstep (se 1 (by rfl) ⟨3620429, by rfl⟩ : syracuseStep 4827239 = 7240859) B7240859
theorem B3218159 : Blo 2145435 3218159 := bstep (se 1 (by rfl) ⟨2413619, by rfl⟩ : syracuseStep 3218159 = 4827239) B4827239
theorem B2145439 : Blo 2145435 2145439 := bstep (se 1 (by rfl) ⟨1609079, by rfl⟩ : syracuseStep 2145439 = 3218159) B3218159
theorem B3218165 : Blo 2145435 3218165 := bbase (se 5 (by rfl) ⟨150851, by rfl⟩ : syracuseStep 3218165 = 301703) (by norm_num)
theorem B2145443 : Blo 2145435 2145443 := bstep (se 1 (by rfl) ⟨1609082, by rfl⟩ : syracuseStep 2145443 = 3218165) B3218165
theorem B10309781 : Blo 2145435 10309781 := bbase (se 6 (by rfl) ⟨241635, by rfl⟩ : syracuseStep 10309781 = 483271) (by norm_num)
theorem B6873187 : Blo 2145435 6873187 := bstep (se 1 (by rfl) ⟨5154890, by rfl⟩ : syracuseStep 6873187 = 10309781) B10309781
theorem B9164249 : Blo 2145435 9164249 := bstep (se 2 (by rfl) ⟨3436593, by rfl⟩ : syracuseStep 9164249 = 6873187) B6873187
theorem B6109499 : Blo 2145435 6109499 := bstep (se 1 (by rfl) ⟨4582124, by rfl⟩ : syracuseStep 6109499 = 9164249) B9164249
theorem B4072999 : Blo 2145435 4072999 := bstep (se 1 (by rfl) ⟨3054749, by rfl⟩ : syracuseStep 4072999 = 6109499) B6109499
theorem B5430665 : Blo 2145435 5430665 := bstep (se 2 (by rfl) ⟨2036499, by rfl⟩ : syracuseStep 5430665 = 4072999) B4072999
theorem B3620443 : Blo 2145435 3620443 := bstep (se 1 (by rfl) ⟨2715332, by rfl⟩ : syracuseStep 3620443 = 5430665) B5430665
theorem B4827257 : Blo 2145435 4827257 := bstep (se 2 (by rfl) ⟨1810221, by rfl⟩ : syracuseStep 4827257 = 3620443) B3620443
theorem B3218171 : Blo 2145435 3218171 := bstep (se 1 (by rfl) ⟨2413628, by rfl⟩ : syracuseStep 3218171 = 4827257) B4827257
theorem B2145447 : Blo 2145435 2145447 := bstep (se 1 (by rfl) ⟨1609085, by rfl⟩ : syracuseStep 2145447 = 3218171) B3218171
theorem B2413633 : Blo 2145435 2413633 := bbase (se 2 (by rfl) ⟨905112, by rfl⟩ : syracuseStep 2413633 = 1810225) (by norm_num)
theorem B3218177 : Blo 2145435 3218177 := bstep (se 2 (by rfl) ⟨1206816, by rfl⟩ : syracuseStep 3218177 = 2413633) B2413633
theorem B2145451 : Blo 2145435 2145451 := bstep (se 1 (by rfl) ⟨1609088, by rfl⟩ : syracuseStep 2145451 = 3218177) B3218177
theorem B5430685 : Blo 2145435 5430685 := bbase (se 3 (by rfl) ⟨1018253, by rfl⟩ : syracuseStep 5430685 = 2036507) (by norm_num)
theorem B7240913 : Blo 2145435 7240913 := bstep (se 2 (by rfl) ⟨2715342, by rfl⟩ : syracuseStep 7240913 = 5430685) B5430685
theorem B4827275 : Blo 2145435 4827275 := bstep (se 1 (by rfl) ⟨3620456, by rfl⟩ : syracuseStep 4827275 = 7240913) B7240913
theorem B3218183 : Blo 2145435 3218183 := bstep (se 1 (by rfl) ⟨2413637, by rfl⟩ : syracuseStep 3218183 = 4827275) B4827275
theorem B2145455 : Blo 2145435 2145455 := bstep (se 1 (by rfl) ⟨1609091, by rfl⟩ : syracuseStep 2145455 = 3218183) B3218183
theorem B3218189 : Blo 2145435 3218189 := bbase (se 3 (by rfl) ⟨603410, by rfl⟩ : syracuseStep 3218189 = 1206821) (by norm_num)
theorem B2145459 : Blo 2145435 2145459 := bstep (se 1 (by rfl) ⟨1609094, by rfl⟩ : syracuseStep 2145459 = 3218189) B3218189
theorem B4827293 : Blo 2145435 4827293 := bbase (se 3 (by rfl) ⟨905117, by rfl⟩ : syracuseStep 4827293 = 1810235) (by norm_num)
theorem B3218195 : Blo 2145435 3218195 := bstep (se 1 (by rfl) ⟨2413646, by rfl⟩ : syracuseStep 3218195 = 4827293) B4827293
theorem B2145463 : Blo 2145435 2145463 := bstep (se 1 (by rfl) ⟨1609097, by rfl⟩ : syracuseStep 2145463 = 3218195) B3218195
theorem B3620477 : Blo 2145435 3620477 := bbase (se 3 (by rfl) ⟨678839, by rfl⟩ : syracuseStep 3620477 = 1357679) (by norm_num)
theorem B2413651 : Blo 2145435 2413651 := bstep (se 1 (by rfl) ⟨1810238, by rfl⟩ : syracuseStep 2413651 = 3620477) B3620477
theorem B3218201 : Blo 2145435 3218201 := bstep (se 2 (by rfl) ⟨1206825, by rfl⟩ : syracuseStep 3218201 = 2413651) B2413651
theorem B2145467 : Blo 2145435 2145467 := bstep (se 1 (by rfl) ⟨1609100, by rfl⟩ : syracuseStep 2145467 = 3218201) B3218201
theorem B2648285 : Blo 2145435 2648285 := bbase (se 3 (by rfl) ⟨496553, by rfl⟩ : syracuseStep 2648285 = 993107) (by norm_num)
theorem B28248373 : Blo 2145435 28248373 := bstep (se 5 (by rfl) ⟨1324142, by rfl⟩ : syracuseStep 28248373 = 2648285) B2648285
theorem B37664497 : Blo 2145435 37664497 := bstep (se 2 (by rfl) ⟨14124186, by rfl⟩ : syracuseStep 37664497 = 28248373) B28248373
theorem B200877317 : Blo 2145435 200877317 := bstep (se 4 (by rfl) ⟨18832248, by rfl⟩ : syracuseStep 200877317 = 37664497) B37664497
theorem B133918211 : Blo 2145435 133918211 := bstep (se 1 (by rfl) ⟨100438658, by rfl⟩ : syracuseStep 133918211 = 200877317) B200877317
theorem B89278807 : Blo 2145435 89278807 := bstep (se 1 (by rfl) ⟨66959105, by rfl⟩ : syracuseStep 89278807 = 133918211) B133918211
theorem B119038409 : Blo 2145435 119038409 := bstep (se 2 (by rfl) ⟨44639403, by rfl⟩ : syracuseStep 119038409 = 89278807) B89278807
theorem B79358939 : Blo 2145435 79358939 := bstep (se 1 (by rfl) ⟨59519204, by rfl⟩ : syracuseStep 79358939 = 119038409) B119038409
theorem B52905959 : Blo 2145435 52905959 := bstep (se 1 (by rfl) ⟨39679469, by rfl⟩ : syracuseStep 52905959 = 79358939) B79358939
theorem B35270639 : Blo 2145435 35270639 := bstep (se 1 (by rfl) ⟨26452979, by rfl⟩ : syracuseStep 35270639 = 52905959) B52905959
theorem B23513759 : Blo 2145435 23513759 := bstep (se 1 (by rfl) ⟨17635319, by rfl⟩ : syracuseStep 23513759 = 35270639) B35270639
theorem B15675839 : Blo 2145435 15675839 := bstep (se 1 (by rfl) ⟨11756879, by rfl⟩ : syracuseStep 15675839 = 23513759) B23513759
theorem B10450559 : Blo 2145435 10450559 := bstep (se 1 (by rfl) ⟨7837919, by rfl⟩ : syracuseStep 10450559 = 15675839) B15675839
theorem B27868157 : Blo 2145435 27868157 := bstep (se 3 (by rfl) ⟨5225279, by rfl⟩ : syracuseStep 27868157 = 10450559) B10450559
theorem B18578771 : Blo 2145435 18578771 := bstep (se 1 (by rfl) ⟨13934078, by rfl⟩ : syracuseStep 18578771 = 27868157) B27868157
theorem B12385847 : Blo 2145435 12385847 := bstep (se 1 (by rfl) ⟨9289385, by rfl⟩ : syracuseStep 12385847 = 18578771) B18578771
theorem B8257231 : Blo 2145435 8257231 := bstep (se 1 (by rfl) ⟨6192923, by rfl⟩ : syracuseStep 8257231 = 12385847) B12385847
theorem B11009641 : Blo 2145435 11009641 := bstep (se 2 (by rfl) ⟨4128615, by rfl⟩ : syracuseStep 11009641 = 8257231) B8257231
theorem B14679521 : Blo 2145435 14679521 := bstep (se 2 (by rfl) ⟨5504820, by rfl⟩ : syracuseStep 14679521 = 11009641) B11009641
theorem B9786347 : Blo 2145435 9786347 := bstep (se 1 (by rfl) ⟨7339760, by rfl⟩ : syracuseStep 9786347 = 14679521) B14679521
theorem B6524231 : Blo 2145435 6524231 := bstep (se 1 (by rfl) ⟨4893173, by rfl⟩ : syracuseStep 6524231 = 9786347) B9786347
theorem B17397949 : Blo 2145435 17397949 := bstep (se 3 (by rfl) ⟨3262115, by rfl⟩ : syracuseStep 17397949 = 6524231) B6524231
theorem B23197265 : Blo 2145435 23197265 := bstep (se 2 (by rfl) ⟨8698974, by rfl⟩ : syracuseStep 23197265 = 17397949) B17397949
theorem B15464843 : Blo 2145435 15464843 := bstep (se 1 (by rfl) ⟨11598632, by rfl⟩ : syracuseStep 15464843 = 23197265) B23197265
theorem B10309895 : Blo 2145435 10309895 := bstep (se 1 (by rfl) ⟨7732421, by rfl⟩ : syracuseStep 10309895 = 15464843) B15464843
theorem B6873263 : Blo 2145435 6873263 := bstep (se 1 (by rfl) ⟨5154947, by rfl⟩ : syracuseStep 6873263 = 10309895) B10309895
theorem B4582175 : Blo 2145435 4582175 := bstep (se 1 (by rfl) ⟨3436631, by rfl⟩ : syracuseStep 4582175 = 6873263) B6873263
theorem B12219133 : Blo 2145435 12219133 := bstep (se 3 (by rfl) ⟨2291087, by rfl⟩ : syracuseStep 12219133 = 4582175) B4582175
theorem B16292177 : Blo 2145435 16292177 := bstep (se 2 (by rfl) ⟨6109566, by rfl⟩ : syracuseStep 16292177 = 12219133) B12219133
theorem B10861451 : Blo 2145435 10861451 := bstep (se 1 (by rfl) ⟨8146088, by rfl⟩ : syracuseStep 10861451 = 16292177) B16292177
theorem B7240967 : Blo 2145435 7240967 := bstep (se 1 (by rfl) ⟨5430725, by rfl⟩ : syracuseStep 7240967 = 10861451) B10861451
theorem B4827311 : Blo 2145435 4827311 := bstep (se 1 (by rfl) ⟨3620483, by rfl⟩ : syracuseStep 4827311 = 7240967) B7240967
theorem B3218207 : Blo 2145435 3218207 := bstep (se 1 (by rfl) ⟨2413655, by rfl⟩ : syracuseStep 3218207 = 4827311) B4827311
theorem B2145471 : Blo 2145435 2145471 := bstep (se 1 (by rfl) ⟨1609103, by rfl⟩ : syracuseStep 2145471 = 3218207) B3218207
theorem B3218213 : Blo 2145435 3218213 := bbase (se 4 (by rfl) ⟨301707, by rfl⟩ : syracuseStep 3218213 = 603415) (by norm_num)
theorem B2145475 : Blo 2145435 2145475 := bstep (se 1 (by rfl) ⟨1609106, by rfl⟩ : syracuseStep 2145475 = 3218213) B3218213
theorem B2715373 : Blo 2145435 2715373 := bbase (se 3 (by rfl) ⟨509132, by rfl⟩ : syracuseStep 2715373 = 1018265) (by norm_num)
theorem B3620497 : Blo 2145435 3620497 := bstep (se 2 (by rfl) ⟨1357686, by rfl⟩ : syracuseStep 3620497 = 2715373) B2715373
theorem B4827329 : Blo 2145435 4827329 := bstep (se 2 (by rfl) ⟨1810248, by rfl⟩ : syracuseStep 4827329 = 3620497) B3620497
theorem B3218219 : Blo 2145435 3218219 := bstep (se 1 (by rfl) ⟨2413664, by rfl⟩ : syracuseStep 3218219 = 4827329) B4827329
theorem B2145479 : Blo 2145435 2145479 := bstep (se 1 (by rfl) ⟨1609109, by rfl⟩ : syracuseStep 2145479 = 3218219) B3218219
theorem B2413669 : Blo 2145435 2413669 := bbase (se 4 (by rfl) ⟨226281, by rfl⟩ : syracuseStep 2413669 = 452563) (by norm_num)
theorem B3218225 : Blo 2145435 3218225 := bstep (se 2 (by rfl) ⟨1206834, by rfl⟩ : syracuseStep 3218225 = 2413669) B2413669
theorem B2145483 : Blo 2145435 2145483 := bstep (se 1 (by rfl) ⟨1609112, by rfl⟩ : syracuseStep 2145483 = 3218225) B3218225
theorem B2291105 : Blo 2145435 2291105 := bbase (se 2 (by rfl) ⟨859164, by rfl⟩ : syracuseStep 2291105 = 1718329) (by norm_num)
theorem B6109613 : Blo 2145435 6109613 := bstep (se 3 (by rfl) ⟨1145552, by rfl⟩ : syracuseStep 6109613 = 2291105) B2291105
theorem B4073075 : Blo 2145435 4073075 := bstep (se 1 (by rfl) ⟨3054806, by rfl⟩ : syracuseStep 4073075 = 6109613) B6109613
theorem B2715383 : Blo 2145435 2715383 := bstep (se 1 (by rfl) ⟨2036537, by rfl⟩ : syracuseStep 2715383 = 4073075) B4073075
theorem B7241021 : Blo 2145435 7241021 := bstep (se 3 (by rfl) ⟨1357691, by rfl⟩ : syracuseStep 7241021 = 2715383) B2715383
theorem B4827347 : Blo 2145435 4827347 := bstep (se 1 (by rfl) ⟨3620510, by rfl⟩ : syracuseStep 4827347 = 7241021) B7241021
theorem B3218231 : Blo 2145435 3218231 := bstep (se 1 (by rfl) ⟨2413673, by rfl⟩ : syracuseStep 3218231 = 4827347) B4827347
theorem B2145487 : Blo 2145435 2145487 := bstep (se 1 (by rfl) ⟨1609115, by rfl⟩ : syracuseStep 2145487 = 3218231) B3218231
theorem B3218237 : Blo 2145435 3218237 := bbase (se 3 (by rfl) ⟨603419, by rfl⟩ : syracuseStep 3218237 = 1206839) (by norm_num)
theorem B2145491 : Blo 2145435 2145491 := bstep (se 1 (by rfl) ⟨1609118, by rfl⟩ : syracuseStep 2145491 = 3218237) B3218237
theorem B4827365 : Blo 2145435 4827365 := bbase (se 4 (by rfl) ⟨452565, by rfl⟩ : syracuseStep 4827365 = 905131) (by norm_num)
theorem B3218243 : Blo 2145435 3218243 := bstep (se 1 (by rfl) ⟨2413682, by rfl⟩ : syracuseStep 3218243 = 4827365) B4827365
theorem B2145495 : Blo 2145435 2145495 := bstep (se 1 (by rfl) ⟨1609121, by rfl⟩ : syracuseStep 2145495 = 3218243) B3218243
theorem B5430797 : Blo 2145435 5430797 := bbase (se 3 (by rfl) ⟨1018274, by rfl⟩ : syracuseStep 5430797 = 2036549) (by norm_num)
theorem B3620531 : Blo 2145435 3620531 := bstep (se 1 (by rfl) ⟨2715398, by rfl⟩ : syracuseStep 3620531 = 5430797) B5430797
theorem B2413687 : Blo 2145435 2413687 := bstep (se 1 (by rfl) ⟨1810265, by rfl⟩ : syracuseStep 2413687 = 3620531) B3620531
theorem B3218249 : Blo 2145435 3218249 := bstep (se 2 (by rfl) ⟨1206843, by rfl⟩ : syracuseStep 3218249 = 2413687) B2413687
theorem B2145499 : Blo 2145435 2145499 := bstep (se 1 (by rfl) ⟨1609124, by rfl⟩ : syracuseStep 2145499 = 3218249) B3218249
theorem B3054829 : Blo 2145435 3054829 := bbase (se 3 (by rfl) ⟨572780, by rfl⟩ : syracuseStep 3054829 = 1145561) (by norm_num)
theorem B4073105 : Blo 2145435 4073105 := bstep (se 2 (by rfl) ⟨1527414, by rfl⟩ : syracuseStep 4073105 = 3054829) B3054829
theorem B10861613 : Blo 2145435 10861613 := bstep (se 3 (by rfl) ⟨2036552, by rfl⟩ : syracuseStep 10861613 = 4073105) B4073105
theorem B7241075 : Blo 2145435 7241075 := bstep (se 1 (by rfl) ⟨5430806, by rfl⟩ : syracuseStep 7241075 = 10861613) B10861613
theorem B4827383 : Blo 2145435 4827383 := bstep (se 1 (by rfl) ⟨3620537, by rfl⟩ : syracuseStep 4827383 = 7241075) B7241075
theorem B3218255 : Blo 2145435 3218255 := bstep (se 1 (by rfl) ⟨2413691, by rfl⟩ : syracuseStep 3218255 = 4827383) B4827383
theorem B2145503 : Blo 2145435 2145503 := bstep (se 1 (by rfl) ⟨1609127, by rfl⟩ : syracuseStep 2145503 = 3218255) B3218255
theorem B3218261 : Blo 2145435 3218261 := bbase (se 9 (by rfl) ⟨9428, by rfl⟩ : syracuseStep 3218261 = 18857) (by norm_num)
theorem B2145507 : Blo 2145435 2145507 := bstep (se 1 (by rfl) ⟨1609130, by rfl⟩ : syracuseStep 2145507 = 3218261) B3218261
theorem B4582261 : Blo 2145435 4582261 := bbase (se 5 (by rfl) ⟨214793, by rfl⟩ : syracuseStep 4582261 = 429587) (by norm_num)
theorem B6109681 : Blo 2145435 6109681 := bstep (se 2 (by rfl) ⟨2291130, by rfl⟩ : syracuseStep 6109681 = 4582261) B4582261
theorem B8146241 : Blo 2145435 8146241 := bstep (se 2 (by rfl) ⟨3054840, by rfl⟩ : syracuseStep 8146241 = 6109681) B6109681
theorem B5430827 : Blo 2145435 5430827 := bstep (se 1 (by rfl) ⟨4073120, by rfl⟩ : syracuseStep 5430827 = 8146241) B8146241
theorem B3620551 : Blo 2145435 3620551 := bstep (se 1 (by rfl) ⟨2715413, by rfl⟩ : syracuseStep 3620551 = 5430827) B5430827
theorem B4827401 : Blo 2145435 4827401 := bstep (se 2 (by rfl) ⟨1810275, by rfl⟩ : syracuseStep 4827401 = 3620551) B3620551
theorem B3218267 : Blo 2145435 3218267 := bstep (se 1 (by rfl) ⟨2413700, by rfl⟩ : syracuseStep 3218267 = 4827401) B4827401
theorem B2145511 : Blo 2145435 2145511 := bstep (se 1 (by rfl) ⟨1609133, by rfl⟩ : syracuseStep 2145511 = 3218267) B3218267
theorem B2413705 : Blo 2145435 2413705 := bbase (se 2 (by rfl) ⟨905139, by rfl⟩ : syracuseStep 2413705 = 1810279) (by norm_num)
theorem B3218273 : Blo 2145435 3218273 := bstep (se 2 (by rfl) ⟨1206852, by rfl⟩ : syracuseStep 3218273 = 2413705) B2413705
theorem B2145515 : Blo 2145435 2145515 := bstep (se 1 (by rfl) ⟨1609136, by rfl⟩ : syracuseStep 2145515 = 3218273) B3218273
theorem B3262189 : Blo 2145435 3262189 := bbase (se 3 (by rfl) ⟨611660, by rfl⟩ : syracuseStep 3262189 = 1223321) (by norm_num)
theorem B4349585 : Blo 2145435 4349585 := bstep (se 2 (by rfl) ⟨1631094, by rfl⟩ : syracuseStep 4349585 = 3262189) B3262189
theorem B2899723 : Blo 2145435 2899723 := bstep (se 1 (by rfl) ⟨2174792, by rfl⟩ : syracuseStep 2899723 = 4349585) B4349585
theorem B3866297 : Blo 2145435 3866297 := bstep (se 2 (by rfl) ⟨1449861, by rfl⟩ : syracuseStep 3866297 = 2899723) B2899723
theorem B41240501 : Blo 2145435 41240501 := bstep (se 5 (by rfl) ⟨1933148, by rfl⟩ : syracuseStep 41240501 = 3866297) B3866297
theorem B27493667 : Blo 2145435 27493667 := bstep (se 1 (by rfl) ⟨20620250, by rfl⟩ : syracuseStep 27493667 = 41240501) B41240501
theorem B18329111 : Blo 2145435 18329111 := bstep (se 1 (by rfl) ⟨13746833, by rfl⟩ : syracuseStep 18329111 = 27493667) B27493667
theorem B12219407 : Blo 2145435 12219407 := bstep (se 1 (by rfl) ⟨9164555, by rfl⟩ : syracuseStep 12219407 = 18329111) B18329111
theorem B8146271 : Blo 2145435 8146271 := bstep (se 1 (by rfl) ⟨6109703, by rfl⟩ : syracuseStep 8146271 = 12219407) B12219407
theorem B5430847 : Blo 2145435 5430847 := bstep (se 1 (by rfl) ⟨4073135, by rfl⟩ : syracuseStep 5430847 = 8146271) B8146271
theorem B7241129 : Blo 2145435 7241129 := bstep (se 2 (by rfl) ⟨2715423, by rfl⟩ : syracuseStep 7241129 = 5430847) B5430847
theorem B4827419 : Blo 2145435 4827419 := bstep (se 1 (by rfl) ⟨3620564, by rfl⟩ : syracuseStep 4827419 = 7241129) B7241129
theorem B3218279 : Blo 2145435 3218279 := bstep (se 1 (by rfl) ⟨2413709, by rfl⟩ : syracuseStep 3218279 = 4827419) B4827419
theorem B2145519 : Blo 2145435 2145519 := bstep (se 1 (by rfl) ⟨1609139, by rfl⟩ : syracuseStep 2145519 = 3218279) B3218279
theorem B3218285 : Blo 2145435 3218285 := bbase (se 3 (by rfl) ⟨603428, by rfl⟩ : syracuseStep 3218285 = 1206857) (by norm_num)
theorem B2145523 : Blo 2145435 2145523 := bstep (se 1 (by rfl) ⟨1609142, by rfl⟩ : syracuseStep 2145523 = 3218285) B3218285
theorem B4827437 : Blo 2145435 4827437 := bbase (se 3 (by rfl) ⟨905144, by rfl⟩ : syracuseStep 4827437 = 1810289) (by norm_num)
theorem B3218291 : Blo 2145435 3218291 := bstep (se 1 (by rfl) ⟨2413718, by rfl⟩ : syracuseStep 3218291 = 4827437) B4827437
theorem B2145527 : Blo 2145435 2145527 := bstep (se 1 (by rfl) ⟨1609145, by rfl⟩ : syracuseStep 2145527 = 3218291) B3218291
theorem B5155093 : Blo 2145435 5155093 := bbase (se 6 (by rfl) ⟨120822, by rfl⟩ : syracuseStep 5155093 = 241645) (by norm_num)
theorem B6873457 : Blo 2145435 6873457 := bstep (se 2 (by rfl) ⟨2577546, by rfl⟩ : syracuseStep 6873457 = 5155093) B5155093
theorem B9164609 : Blo 2145435 9164609 := bstep (se 2 (by rfl) ⟨3436728, by rfl⟩ : syracuseStep 9164609 = 6873457) B6873457
theorem B6109739 : Blo 2145435 6109739 := bstep (se 1 (by rfl) ⟨4582304, by rfl⟩ : syracuseStep 6109739 = 9164609) B9164609
theorem B4073159 : Blo 2145435 4073159 := bstep (se 1 (by rfl) ⟨3054869, by rfl⟩ : syracuseStep 4073159 = 6109739) B6109739
theorem B2715439 : Blo 2145435 2715439 := bstep (se 1 (by rfl) ⟨2036579, by rfl⟩ : syracuseStep 2715439 = 4073159) B4073159
theorem B3620585 : Blo 2145435 3620585 := bstep (se 2 (by rfl) ⟨1357719, by rfl⟩ : syracuseStep 3620585 = 2715439) B2715439
theorem B2413723 : Blo 2145435 2413723 := bstep (se 1 (by rfl) ⟨1810292, by rfl⟩ : syracuseStep 2413723 = 3620585) B3620585
theorem B3218297 : Blo 2145435 3218297 := bstep (se 2 (by rfl) ⟨1206861, by rfl⟩ : syracuseStep 3218297 = 2413723) B2413723
theorem B2145531 : Blo 2145435 2145531 := bstep (se 1 (by rfl) ⟨1609148, by rfl⟩ : syracuseStep 2145531 = 3218297) B3218297
theorem B8257477 : Blo 2145435 8257477 := bbase (se 4 (by rfl) ⟨774138, by rfl⟩ : syracuseStep 8257477 = 1548277) (by norm_num)
theorem B11009969 : Blo 2145435 11009969 := bstep (se 2 (by rfl) ⟨4128738, by rfl⟩ : syracuseStep 11009969 = 8257477) B8257477
theorem B7339979 : Blo 2145435 7339979 := bstep (se 1 (by rfl) ⟨5504984, by rfl⟩ : syracuseStep 7339979 = 11009969) B11009969
theorem B4893319 : Blo 2145435 4893319 := bstep (se 1 (by rfl) ⟨3669989, by rfl⟩ : syracuseStep 4893319 = 7339979) B7339979
theorem B6524425 : Blo 2145435 6524425 := bstep (se 2 (by rfl) ⟨2446659, by rfl⟩ : syracuseStep 6524425 = 4893319) B4893319
theorem B8699233 : Blo 2145435 8699233 := bstep (se 2 (by rfl) ⟨3262212, by rfl⟩ : syracuseStep 8699233 = 6524425) B6524425
theorem B11598977 : Blo 2145435 11598977 := bstep (se 2 (by rfl) ⟨4349616, by rfl⟩ : syracuseStep 11598977 = 8699233) B8699233
theorem B30930605 : Blo 2145435 30930605 := bstep (se 3 (by rfl) ⟨5799488, by rfl⟩ : syracuseStep 30930605 = 11598977) B11598977
theorem B20620403 : Blo 2145435 20620403 := bstep (se 1 (by rfl) ⟨15465302, by rfl⟩ : syracuseStep 20620403 = 30930605) B30930605
theorem B13746935 : Blo 2145435 13746935 := bstep (se 1 (by rfl) ⟨10310201, by rfl⟩ : syracuseStep 13746935 = 20620403) B20620403
theorem B36658493 : Blo 2145435 36658493 := bstep (se 3 (by rfl) ⟨6873467, by rfl⟩ : syracuseStep 36658493 = 13746935) B13746935
theorem B24438995 : Blo 2145435 24438995 := bstep (se 1 (by rfl) ⟨18329246, by rfl⟩ : syracuseStep 24438995 = 36658493) B36658493
theorem B16292663 : Blo 2145435 16292663 := bstep (se 1 (by rfl) ⟨12219497, by rfl⟩ : syracuseStep 16292663 = 24438995) B24438995
theorem B10861775 : Blo 2145435 10861775 := bstep (se 1 (by rfl) ⟨8146331, by rfl⟩ : syracuseStep 10861775 = 16292663) B16292663
theorem B7241183 : Blo 2145435 7241183 := bstep (se 1 (by rfl) ⟨5430887, by rfl⟩ : syracuseStep 7241183 = 10861775) B10861775
theorem B4827455 : Blo 2145435 4827455 := bstep (se 1 (by rfl) ⟨3620591, by rfl⟩ : syracuseStep 4827455 = 7241183) B7241183
theorem B3218303 : Blo 2145435 3218303 := bstep (se 1 (by rfl) ⟨2413727, by rfl⟩ : syracuseStep 3218303 = 4827455) B4827455
theorem B2145535 : Blo 2145435 2145535 := bstep (se 1 (by rfl) ⟨1609151, by rfl⟩ : syracuseStep 2145535 = 3218303) B3218303
theorem B3218309 : Blo 2145435 3218309 := bbase (se 4 (by rfl) ⟨301716, by rfl⟩ : syracuseStep 3218309 = 603433) (by norm_num)
theorem B2145539 : Blo 2145435 2145539 := bstep (se 1 (by rfl) ⟨1609154, by rfl⟩ : syracuseStep 2145539 = 3218309) B3218309
theorem B3620605 : Blo 2145435 3620605 := bbase (se 3 (by rfl) ⟨678863, by rfl⟩ : syracuseStep 3620605 = 1357727) (by norm_num)
theorem B4827473 : Blo 2145435 4827473 := bstep (se 2 (by rfl) ⟨1810302, by rfl⟩ : syracuseStep 4827473 = 3620605) B3620605
theorem B3218315 : Blo 2145435 3218315 := bstep (se 1 (by rfl) ⟨2413736, by rfl⟩ : syracuseStep 3218315 = 4827473) B4827473
theorem B2145543 : Blo 2145435 2145543 := bstep (se 1 (by rfl) ⟨1609157, by rfl⟩ : syracuseStep 2145543 = 3218315) B3218315
theorem B2413741 : Blo 2145435 2413741 := bbase (se 3 (by rfl) ⟨452576, by rfl⟩ : syracuseStep 2413741 = 905153) (by norm_num)
theorem B3218321 : Blo 2145435 3218321 := bstep (se 2 (by rfl) ⟨1206870, by rfl⟩ : syracuseStep 3218321 = 2413741) B2413741
theorem B2145547 : Blo 2145435 2145547 := bstep (se 1 (by rfl) ⟨1609160, by rfl⟩ : syracuseStep 2145547 = 3218321) B3218321
theorem B7241237 : Blo 2145435 7241237 := bbase (se 6 (by rfl) ⟨169716, by rfl⟩ : syracuseStep 7241237 = 339433) (by norm_num)
theorem B4827491 : Blo 2145435 4827491 := bstep (se 1 (by rfl) ⟨3620618, by rfl⟩ : syracuseStep 4827491 = 7241237) B7241237
theorem B3218327 : Blo 2145435 3218327 := bstep (se 1 (by rfl) ⟨2413745, by rfl⟩ : syracuseStep 3218327 = 4827491) B4827491
theorem B2145551 : Blo 2145435 2145551 := bstep (se 1 (by rfl) ⟨1609163, by rfl⟩ : syracuseStep 2145551 = 3218327) B3218327
theorem B3218333 : Blo 2145435 3218333 := bbase (se 3 (by rfl) ⟨603437, by rfl⟩ : syracuseStep 3218333 = 1206875) (by norm_num)
theorem B2145555 : Blo 2145435 2145555 := bstep (se 1 (by rfl) ⟨1609166, by rfl⟩ : syracuseStep 2145555 = 3218333) B3218333
theorem B4827509 : Blo 2145435 4827509 := bbase (se 5 (by rfl) ⟨226289, by rfl⟩ : syracuseStep 4827509 = 452579) (by norm_num)
theorem B3218339 : Blo 2145435 3218339 := bstep (se 1 (by rfl) ⟨2413754, by rfl⟩ : syracuseStep 3218339 = 4827509) B4827509
theorem B2145559 : Blo 2145435 2145559 := bstep (se 1 (by rfl) ⟨1609169, by rfl⟩ : syracuseStep 2145559 = 3218339) B3218339
theorem B8257589 : Blo 2145435 8257589 := bbase (se 5 (by rfl) ⟨387074, by rfl⟩ : syracuseStep 8257589 = 774149) (by norm_num)
theorem B5505059 : Blo 2145435 5505059 := bstep (se 1 (by rfl) ⟨4128794, by rfl⟩ : syracuseStep 5505059 = 8257589) B8257589
theorem B3670039 : Blo 2145435 3670039 := bstep (se 1 (by rfl) ⟨2752529, by rfl⟩ : syracuseStep 3670039 = 5505059) B5505059
theorem B4893385 : Blo 2145435 4893385 := bstep (se 2 (by rfl) ⟨1835019, by rfl⟩ : syracuseStep 4893385 = 3670039) B3670039
theorem B6524513 : Blo 2145435 6524513 := bstep (se 2 (by rfl) ⟨2446692, by rfl⟩ : syracuseStep 6524513 = 4893385) B4893385
theorem B4349675 : Blo 2145435 4349675 := bstep (se 1 (by rfl) ⟨3262256, by rfl⟩ : syracuseStep 4349675 = 6524513) B6524513
theorem B2899783 : Blo 2145435 2899783 := bstep (se 1 (by rfl) ⟨2174837, by rfl⟩ : syracuseStep 2899783 = 4349675) B4349675
theorem B3866377 : Blo 2145435 3866377 := bstep (se 2 (by rfl) ⟨1449891, by rfl⟩ : syracuseStep 3866377 = 2899783) B2899783
theorem B5155169 : Blo 2145435 5155169 := bstep (se 2 (by rfl) ⟨1933188, by rfl⟩ : syracuseStep 5155169 = 3866377) B3866377
theorem B13747117 : Blo 2145435 13747117 := bstep (se 3 (by rfl) ⟨2577584, by rfl⟩ : syracuseStep 13747117 = 5155169) B5155169
theorem B18329489 : Blo 2145435 18329489 := bstep (se 2 (by rfl) ⟨6873558, by rfl⟩ : syracuseStep 18329489 = 13747117) B13747117
theorem B12219659 : Blo 2145435 12219659 := bstep (se 1 (by rfl) ⟨9164744, by rfl⟩ : syracuseStep 12219659 = 18329489) B18329489
theorem B8146439 : Blo 2145435 8146439 := bstep (se 1 (by rfl) ⟨6109829, by rfl⟩ : syracuseStep 8146439 = 12219659) B12219659
theorem B5430959 : Blo 2145435 5430959 := bstep (se 1 (by rfl) ⟨4073219, by rfl⟩ : syracuseStep 5430959 = 8146439) B8146439
theorem B3620639 : Blo 2145435 3620639 := bstep (se 1 (by rfl) ⟨2715479, by rfl⟩ : syracuseStep 3620639 = 5430959) B5430959
theorem B2413759 : Blo 2145435 2413759 := bstep (se 1 (by rfl) ⟨1810319, by rfl⟩ : syracuseStep 2413759 = 3620639) B3620639
theorem B3218345 : Blo 2145435 3218345 := bstep (se 2 (by rfl) ⟨1206879, by rfl⟩ : syracuseStep 3218345 = 2413759) B2413759
theorem B2145563 : Blo 2145435 2145563 := bstep (se 1 (by rfl) ⟨1609172, by rfl⟩ : syracuseStep 2145563 = 3218345) B3218345
theorem B8146453 : Blo 2145435 8146453 := bbase (se 6 (by rfl) ⟨190932, by rfl⟩ : syracuseStep 8146453 = 381865) (by norm_num)
theorem B10861937 : Blo 2145435 10861937 := bstep (se 2 (by rfl) ⟨4073226, by rfl⟩ : syracuseStep 10861937 = 8146453) B8146453
theorem B7241291 : Blo 2145435 7241291 := bstep (se 1 (by rfl) ⟨5430968, by rfl⟩ : syracuseStep 7241291 = 10861937) B10861937
theorem B4827527 : Blo 2145435 4827527 := bstep (se 1 (by rfl) ⟨3620645, by rfl⟩ : syracuseStep 4827527 = 7241291) B7241291
theorem B3218351 : Blo 2145435 3218351 := bstep (se 1 (by rfl) ⟨2413763, by rfl⟩ : syracuseStep 3218351 = 4827527) B4827527
theorem B2145567 : Blo 2145435 2145567 := bstep (se 1 (by rfl) ⟨1609175, by rfl⟩ : syracuseStep 2145567 = 3218351) B3218351
theorem B3218357 : Blo 2145435 3218357 := bbase (se 5 (by rfl) ⟨150860, by rfl⟩ : syracuseStep 3218357 = 301721) (by norm_num)
theorem B2145571 : Blo 2145435 2145571 := bstep (se 1 (by rfl) ⟨1609178, by rfl⟩ : syracuseStep 2145571 = 3218357) B3218357
theorem B5430989 : Blo 2145435 5430989 := bbase (se 3 (by rfl) ⟨1018310, by rfl⟩ : syracuseStep 5430989 = 2036621) (by norm_num)
theorem B3620659 : Blo 2145435 3620659 := bstep (se 1 (by rfl) ⟨2715494, by rfl⟩ : syracuseStep 3620659 = 5430989) B5430989
theorem B4827545 : Blo 2145435 4827545 := bstep (se 2 (by rfl) ⟨1810329, by rfl⟩ : syracuseStep 4827545 = 3620659) B3620659
theorem B3218363 : Blo 2145435 3218363 := bstep (se 1 (by rfl) ⟨2413772, by rfl⟩ : syracuseStep 3218363 = 4827545) B4827545
theorem B2145575 : Blo 2145435 2145575 := bstep (se 1 (by rfl) ⟨1609181, by rfl⟩ : syracuseStep 2145575 = 3218363) B3218363
theorem B2413777 : Blo 2145435 2413777 := bbase (se 2 (by rfl) ⟨905166, by rfl⟩ : syracuseStep 2413777 = 1810333) (by norm_num)
theorem B3218369 : Blo 2145435 3218369 := bstep (se 2 (by rfl) ⟨1206888, by rfl⟩ : syracuseStep 3218369 = 2413777) B2413777
theorem B2145579 : Blo 2145435 2145579 := bstep (se 1 (by rfl) ⟨1609184, by rfl⟩ : syracuseStep 2145579 = 3218369) B3218369
theorem B15465653 : Blo 2145435 15465653 := bbase (se 5 (by rfl) ⟨724952, by rfl⟩ : syracuseStep 15465653 = 1449905) (by norm_num)
theorem B10310435 : Blo 2145435 10310435 := bstep (se 1 (by rfl) ⟨7732826, by rfl⟩ : syracuseStep 10310435 = 15465653) B15465653
theorem B6873623 : Blo 2145435 6873623 := bstep (se 1 (by rfl) ⟨5155217, by rfl⟩ : syracuseStep 6873623 = 10310435) B10310435
theorem B4582415 : Blo 2145435 4582415 := bstep (se 1 (by rfl) ⟨3436811, by rfl⟩ : syracuseStep 4582415 = 6873623) B6873623
theorem B3054943 : Blo 2145435 3054943 := bstep (se 1 (by rfl) ⟨2291207, by rfl⟩ : syracuseStep 3054943 = 4582415) B4582415
theorem B4073257 : Blo 2145435 4073257 := bstep (se 2 (by rfl) ⟨1527471, by rfl⟩ : syracuseStep 4073257 = 3054943) B3054943
theorem B5431009 : Blo 2145435 5431009 := bstep (se 2 (by rfl) ⟨2036628, by rfl⟩ : syracuseStep 5431009 = 4073257) B4073257
theorem B7241345 : Blo 2145435 7241345 := bstep (se 2 (by rfl) ⟨2715504, by rfl⟩ : syracuseStep 7241345 = 5431009) B5431009
theorem B4827563 : Blo 2145435 4827563 := bstep (se 1 (by rfl) ⟨3620672, by rfl⟩ : syracuseStep 4827563 = 7241345) B7241345
theorem B3218375 : Blo 2145435 3218375 := bstep (se 1 (by rfl) ⟨2413781, by rfl⟩ : syracuseStep 3218375 = 4827563) B4827563
theorem B2145583 : Blo 2145435 2145583 := bstep (se 1 (by rfl) ⟨1609187, by rfl⟩ : syracuseStep 2145583 = 3218375) B3218375
theorem B3218381 : Blo 2145435 3218381 := bbase (se 3 (by rfl) ⟨603446, by rfl⟩ : syracuseStep 3218381 = 1206893) (by norm_num)
theorem B2145587 : Blo 2145435 2145587 := bstep (se 1 (by rfl) ⟨1609190, by rfl⟩ : syracuseStep 2145587 = 3218381) B3218381
theorem B4827581 : Blo 2145435 4827581 := bbase (se 3 (by rfl) ⟨905171, by rfl⟩ : syracuseStep 4827581 = 1810343) (by norm_num)
theorem B3218387 : Blo 2145435 3218387 := bstep (se 1 (by rfl) ⟨2413790, by rfl⟩ : syracuseStep 3218387 = 4827581) B4827581
theorem B2145591 : Blo 2145435 2145591 := bstep (se 1 (by rfl) ⟨1609193, by rfl⟩ : syracuseStep 2145591 = 3218387) B3218387
theorem B3620693 : Blo 2145435 3620693 := bbase (se 9 (by rfl) ⟨10607, by rfl⟩ : syracuseStep 3620693 = 21215) (by norm_num)
theorem B2413795 : Blo 2145435 2413795 := bstep (se 1 (by rfl) ⟨1810346, by rfl⟩ : syracuseStep 2413795 = 3620693) B3620693
theorem B3218393 : Blo 2145435 3218393 := bstep (se 2 (by rfl) ⟨1206897, by rfl⟩ : syracuseStep 3218393 = 2413795) B2413795
theorem B2145595 : Blo 2145435 2145595 := bstep (se 1 (by rfl) ⟨1609196, by rfl⟩ : syracuseStep 2145595 = 3218393) B3218393
theorem B2446733 : Blo 2145435 2446733 := bbase (se 3 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 2446733 = 917525) (by norm_num)
theorem B6524621 : Blo 2145435 6524621 := bstep (se 3 (by rfl) ⟨1223366, by rfl⟩ : syracuseStep 6524621 = 2446733) B2446733
theorem B4349747 : Blo 2145435 4349747 := bstep (se 1 (by rfl) ⟨3262310, by rfl⟩ : syracuseStep 4349747 = 6524621) B6524621
theorem B11599325 : Blo 2145435 11599325 := bstep (se 3 (by rfl) ⟨2174873, by rfl⟩ : syracuseStep 11599325 = 4349747) B4349747
theorem B7732883 : Blo 2145435 7732883 := bstep (se 1 (by rfl) ⟨5799662, by rfl⟩ : syracuseStep 7732883 = 11599325) B11599325
theorem B5155255 : Blo 2145435 5155255 := bstep (se 1 (by rfl) ⟨3866441, by rfl⟩ : syracuseStep 5155255 = 7732883) B7732883
theorem B6873673 : Blo 2145435 6873673 := bstep (se 2 (by rfl) ⟨2577627, by rfl⟩ : syracuseStep 6873673 = 5155255) B5155255
theorem B9164897 : Blo 2145435 9164897 := bstep (se 2 (by rfl) ⟨3436836, by rfl⟩ : syracuseStep 9164897 = 6873673) B6873673
theorem B6109931 : Blo 2145435 6109931 := bstep (se 1 (by rfl) ⟨4582448, by rfl⟩ : syracuseStep 6109931 = 9164897) B9164897
theorem B16293149 : Blo 2145435 16293149 := bstep (se 3 (by rfl) ⟨3054965, by rfl⟩ : syracuseStep 16293149 = 6109931) B6109931
theorem B10862099 : Blo 2145435 10862099 := bstep (se 1 (by rfl) ⟨8146574, by rfl⟩ : syracuseStep 10862099 = 16293149) B16293149
theorem B7241399 : Blo 2145435 7241399 := bstep (se 1 (by rfl) ⟨5431049, by rfl⟩ : syracuseStep 7241399 = 10862099) B10862099
theorem B4827599 : Blo 2145435 4827599 := bstep (se 1 (by rfl) ⟨3620699, by rfl⟩ : syracuseStep 4827599 = 7241399) B7241399
theorem B3218399 : Blo 2145435 3218399 := bstep (se 1 (by rfl) ⟨2413799, by rfl⟩ : syracuseStep 3218399 = 4827599) B4827599
theorem B2145599 : Blo 2145435 2145599 := bstep (se 1 (by rfl) ⟨1609199, by rfl⟩ : syracuseStep 2145599 = 3218399) B3218399
theorem B3218405 : Blo 2145435 3218405 := bbase (se 4 (by rfl) ⟨301725, by rfl⟩ : syracuseStep 3218405 = 603451) (by norm_num)
theorem B2145603 : Blo 2145435 2145603 := bstep (se 1 (by rfl) ⟨1609202, by rfl⟩ : syracuseStep 2145603 = 3218405) B3218405
theorem B9164933 : Blo 2145435 9164933 := bbase (se 4 (by rfl) ⟨859212, by rfl⟩ : syracuseStep 9164933 = 1718425) (by norm_num)
theorem B6109955 : Blo 2145435 6109955 := bstep (se 1 (by rfl) ⟨4582466, by rfl⟩ : syracuseStep 6109955 = 9164933) B9164933
theorem B4073303 : Blo 2145435 4073303 := bstep (se 1 (by rfl) ⟨3054977, by rfl⟩ : syracuseStep 4073303 = 6109955) B6109955
theorem B2715535 : Blo 2145435 2715535 := bstep (se 1 (by rfl) ⟨2036651, by rfl⟩ : syracuseStep 2715535 = 4073303) B4073303
theorem B3620713 : Blo 2145435 3620713 := bstep (se 2 (by rfl) ⟨1357767, by rfl⟩ : syracuseStep 3620713 = 2715535) B2715535
theorem B4827617 : Blo 2145435 4827617 := bstep (se 2 (by rfl) ⟨1810356, by rfl⟩ : syracuseStep 4827617 = 3620713) B3620713
theorem B3218411 : Blo 2145435 3218411 := bstep (se 1 (by rfl) ⟨2413808, by rfl⟩ : syracuseStep 3218411 = 4827617) B4827617
theorem B2145607 : Blo 2145435 2145607 := bstep (se 1 (by rfl) ⟨1609205, by rfl⟩ : syracuseStep 2145607 = 3218411) B3218411
theorem B2413813 : Blo 2145435 2413813 := bbase (se 5 (by rfl) ⟨113147, by rfl⟩ : syracuseStep 2413813 = 226295) (by norm_num)
theorem B3218417 : Blo 2145435 3218417 := bstep (se 2 (by rfl) ⟨1206906, by rfl⟩ : syracuseStep 3218417 = 2413813) B2413813
theorem B2145611 : Blo 2145435 2145611 := bstep (se 1 (by rfl) ⟨1609208, by rfl⟩ : syracuseStep 2145611 = 3218417) B3218417
theorem B2715545 : Blo 2145435 2715545 := bbase (se 2 (by rfl) ⟨1018329, by rfl⟩ : syracuseStep 2715545 = 2036659) (by norm_num)
theorem B7241453 : Blo 2145435 7241453 := bstep (se 3 (by rfl) ⟨1357772, by rfl⟩ : syracuseStep 7241453 = 2715545) B2715545
theorem B4827635 : Blo 2145435 4827635 := bstep (se 1 (by rfl) ⟨3620726, by rfl⟩ : syracuseStep 4827635 = 7241453) B7241453
theorem B3218423 : Blo 2145435 3218423 := bstep (se 1 (by rfl) ⟨2413817, by rfl⟩ : syracuseStep 3218423 = 4827635) B4827635
theorem B2145615 : Blo 2145435 2145615 := bstep (se 1 (by rfl) ⟨1609211, by rfl⟩ : syracuseStep 2145615 = 3218423) B3218423
theorem B3218429 : Blo 2145435 3218429 := bbase (se 3 (by rfl) ⟨603455, by rfl⟩ : syracuseStep 3218429 = 1206911) (by norm_num)
theorem B2145619 : Blo 2145435 2145619 := bstep (se 1 (by rfl) ⟨1609214, by rfl⟩ : syracuseStep 2145619 = 3218429) B3218429
theorem B4827653 : Blo 2145435 4827653 := bbase (se 4 (by rfl) ⟨452592, by rfl⟩ : syracuseStep 4827653 = 905185) (by norm_num)
theorem B3218435 : Blo 2145435 3218435 := bstep (se 1 (by rfl) ⟨2413826, by rfl⟩ : syracuseStep 3218435 = 4827653) B4827653
theorem B2145623 : Blo 2145435 2145623 := bstep (se 1 (by rfl) ⟨1609217, by rfl⟩ : syracuseStep 2145623 = 3218435) B3218435
theorem B4073341 : Blo 2145435 4073341 := bbase (se 3 (by rfl) ⟨763751, by rfl⟩ : syracuseStep 4073341 = 1527503) (by norm_num)
theorem B5431121 : Blo 2145435 5431121 := bstep (se 2 (by rfl) ⟨2036670, by rfl⟩ : syracuseStep 5431121 = 4073341) B4073341
theorem B3620747 : Blo 2145435 3620747 := bstep (se 1 (by rfl) ⟨2715560, by rfl⟩ : syracuseStep 3620747 = 5431121) B5431121
theorem B2413831 : Blo 2145435 2413831 := bstep (se 1 (by rfl) ⟨1810373, by rfl⟩ : syracuseStep 2413831 = 3620747) B3620747
theorem B3218441 : Blo 2145435 3218441 := bstep (se 2 (by rfl) ⟨1206915, by rfl⟩ : syracuseStep 3218441 = 2413831) B2413831
theorem B2145627 : Blo 2145435 2145627 := bstep (se 1 (by rfl) ⟨1609220, by rfl⟩ : syracuseStep 2145627 = 3218441) B3218441
theorem B10862261 : Blo 2145435 10862261 := bbase (se 5 (by rfl) ⟨509168, by rfl⟩ : syracuseStep 10862261 = 1018337) (by norm_num)
theorem B7241507 : Blo 2145435 7241507 := bstep (se 1 (by rfl) ⟨5431130, by rfl⟩ : syracuseStep 7241507 = 10862261) B10862261
theorem B4827671 : Blo 2145435 4827671 := bstep (se 1 (by rfl) ⟨3620753, by rfl⟩ : syracuseStep 4827671 = 7241507) B7241507
theorem B3218447 : Blo 2145435 3218447 := bstep (se 1 (by rfl) ⟨2413835, by rfl⟩ : syracuseStep 3218447 = 4827671) B4827671
theorem B2145631 : Blo 2145435 2145631 := bstep (se 1 (by rfl) ⟨1609223, by rfl⟩ : syracuseStep 2145631 = 3218447) B3218447
theorem B3218453 : Blo 2145435 3218453 := bbase (se 6 (by rfl) ⟨75432, by rfl⟩ : syracuseStep 3218453 = 150865) (by norm_num)
theorem B2145635 : Blo 2145435 2145635 := bstep (se 1 (by rfl) ⟨1609226, by rfl⟩ : syracuseStep 2145635 = 3218453) B3218453
theorem B11599541 : Blo 2145435 11599541 := bbase (se 5 (by rfl) ⟨543728, by rfl⟩ : syracuseStep 11599541 = 1087457) (by norm_num)
theorem B7733027 : Blo 2145435 7733027 := bstep (se 1 (by rfl) ⟨5799770, by rfl⟩ : syracuseStep 7733027 = 11599541) B11599541
theorem B20621405 : Blo 2145435 20621405 := bstep (se 3 (by rfl) ⟨3866513, by rfl⟩ : syracuseStep 20621405 = 7733027) B7733027
theorem B13747603 : Blo 2145435 13747603 := bstep (se 1 (by rfl) ⟨10310702, by rfl⟩ : syracuseStep 13747603 = 20621405) B20621405
theorem B18330137 : Blo 2145435 18330137 := bstep (se 2 (by rfl) ⟨6873801, by rfl⟩ : syracuseStep 18330137 = 13747603) B13747603
theorem B12220091 : Blo 2145435 12220091 := bstep (se 1 (by rfl) ⟨9165068, by rfl⟩ : syracuseStep 12220091 = 18330137) B18330137
theorem B8146727 : Blo 2145435 8146727 := bstep (se 1 (by rfl) ⟨6110045, by rfl⟩ : syracuseStep 8146727 = 12220091) B12220091
theorem B5431151 : Blo 2145435 5431151 := bstep (se 1 (by rfl) ⟨4073363, by rfl⟩ : syracuseStep 5431151 = 8146727) B8146727
theorem B3620767 : Blo 2145435 3620767 := bstep (se 1 (by rfl) ⟨2715575, by rfl⟩ : syracuseStep 3620767 = 5431151) B5431151
theorem B4827689 : Blo 2145435 4827689 := bstep (se 2 (by rfl) ⟨1810383, by rfl⟩ : syracuseStep 4827689 = 3620767) B3620767
theorem B3218459 : Blo 2145435 3218459 := bstep (se 1 (by rfl) ⟨2413844, by rfl⟩ : syracuseStep 3218459 = 4827689) B4827689
theorem B2145639 : Blo 2145435 2145639 := bstep (se 1 (by rfl) ⟨1609229, by rfl⟩ : syracuseStep 2145639 = 3218459) B3218459
theorem B2413849 : Blo 2145435 2413849 := bbase (se 2 (by rfl) ⟨905193, by rfl⟩ : syracuseStep 2413849 = 1810387) (by norm_num)
theorem B3218465 : Blo 2145435 3218465 := bstep (se 2 (by rfl) ⟨1206924, by rfl⟩ : syracuseStep 3218465 = 2413849) B2413849
theorem B2145643 : Blo 2145435 2145643 := bstep (se 1 (by rfl) ⟨1609232, by rfl⟩ : syracuseStep 2145643 = 3218465) B3218465
theorem B8146757 : Blo 2145435 8146757 := bbase (se 4 (by rfl) ⟨763758, by rfl⟩ : syracuseStep 8146757 = 1527517) (by norm_num)
theorem B5431171 : Blo 2145435 5431171 := bstep (se 1 (by rfl) ⟨4073378, by rfl⟩ : syracuseStep 5431171 = 8146757) B8146757
theorem B7241561 : Blo 2145435 7241561 := bstep (se 2 (by rfl) ⟨2715585, by rfl⟩ : syracuseStep 7241561 = 5431171) B5431171
theorem B4827707 : Blo 2145435 4827707 := bstep (se 1 (by rfl) ⟨3620780, by rfl⟩ : syracuseStep 4827707 = 7241561) B7241561
theorem B3218471 : Blo 2145435 3218471 := bstep (se 1 (by rfl) ⟨2413853, by rfl⟩ : syracuseStep 3218471 = 4827707) B4827707
theorem B2145647 : Blo 2145435 2145647 := bstep (se 1 (by rfl) ⟨1609235, by rfl⟩ : syracuseStep 2145647 = 3218471) B3218471
theorem B3218477 : Blo 2145435 3218477 := bbase (se 3 (by rfl) ⟨603464, by rfl⟩ : syracuseStep 3218477 = 1206929) (by norm_num)
theorem B2145651 : Blo 2145435 2145651 := bstep (se 1 (by rfl) ⟨1609238, by rfl⟩ : syracuseStep 2145651 = 3218477) B3218477
theorem B4827725 : Blo 2145435 4827725 := bbase (se 3 (by rfl) ⟨905198, by rfl⟩ : syracuseStep 4827725 = 1810397) (by norm_num)
theorem B3218483 : Blo 2145435 3218483 := bstep (se 1 (by rfl) ⟨2413862, by rfl⟩ : syracuseStep 3218483 = 4827725) B4827725
theorem B2145655 : Blo 2145435 2145655 := bstep (se 1 (by rfl) ⟨1609241, by rfl⟩ : syracuseStep 2145655 = 3218483) B3218483
theorem B2715601 : Blo 2145435 2715601 := bbase (se 2 (by rfl) ⟨1018350, by rfl⟩ : syracuseStep 2715601 = 2036701) (by norm_num)
theorem B3620801 : Blo 2145435 3620801 := bstep (se 2 (by rfl) ⟨1357800, by rfl⟩ : syracuseStep 3620801 = 2715601) B2715601
theorem B2413867 : Blo 2145435 2413867 := bstep (se 1 (by rfl) ⟨1810400, by rfl⟩ : syracuseStep 2413867 = 3620801) B3620801
theorem B3218489 : Blo 2145435 3218489 := bstep (se 2 (by rfl) ⟨1206933, by rfl⟩ : syracuseStep 3218489 = 2413867) B2413867
theorem B2145659 : Blo 2145435 2145659 := bstep (se 1 (by rfl) ⟨1609244, by rfl⟩ : syracuseStep 2145659 = 3218489) B3218489
theorem B3866557 : Blo 2145435 3866557 := bbase (se 3 (by rfl) ⟨724979, by rfl⟩ : syracuseStep 3866557 = 1449959) (by norm_num)
theorem B5155409 : Blo 2145435 5155409 := bstep (se 2 (by rfl) ⟨1933278, by rfl⟩ : syracuseStep 5155409 = 3866557) B3866557
theorem B3436939 : Blo 2145435 3436939 := bstep (se 1 (by rfl) ⟨2577704, by rfl⟩ : syracuseStep 3436939 = 5155409) B5155409
theorem B4582585 : Blo 2145435 4582585 := bstep (se 2 (by rfl) ⟨1718469, by rfl⟩ : syracuseStep 4582585 = 3436939) B3436939
theorem B24440453 : Blo 2145435 24440453 := bstep (se 4 (by rfl) ⟨2291292, by rfl⟩ : syracuseStep 24440453 = 4582585) B4582585
theorem B16293635 : Blo 2145435 16293635 := bstep (se 1 (by rfl) ⟨12220226, by rfl⟩ : syracuseStep 16293635 = 24440453) B24440453
theorem B10862423 : Blo 2145435 10862423 := bstep (se 1 (by rfl) ⟨8146817, by rfl⟩ : syracuseStep 10862423 = 16293635) B16293635
theorem B7241615 : Blo 2145435 7241615 := bstep (se 1 (by rfl) ⟨5431211, by rfl⟩ : syracuseStep 7241615 = 10862423) B10862423
theorem B4827743 : Blo 2145435 4827743 := bstep (se 1 (by rfl) ⟨3620807, by rfl⟩ : syracuseStep 4827743 = 7241615) B7241615
theorem B3218495 : Blo 2145435 3218495 := bstep (se 1 (by rfl) ⟨2413871, by rfl⟩ : syracuseStep 3218495 = 4827743) B4827743
theorem B2145663 : Blo 2145435 2145663 := bstep (se 1 (by rfl) ⟨1609247, by rfl⟩ : syracuseStep 2145663 = 3218495) B3218495
theorem B3218501 : Blo 2145435 3218501 := bbase (se 4 (by rfl) ⟨301734, by rfl⟩ : syracuseStep 3218501 = 603469) (by norm_num)
theorem B2145667 : Blo 2145435 2145667 := bstep (se 1 (by rfl) ⟨1609250, by rfl⟩ : syracuseStep 2145667 = 3218501) B3218501
theorem B3620821 : Blo 2145435 3620821 := bbase (se 7 (by rfl) ⟨42431, by rfl⟩ : syracuseStep 3620821 = 84863) (by norm_num)
theorem B4827761 : Blo 2145435 4827761 := bstep (se 2 (by rfl) ⟨1810410, by rfl⟩ : syracuseStep 4827761 = 3620821) B3620821
theorem B3218507 : Blo 2145435 3218507 := bstep (se 1 (by rfl) ⟨2413880, by rfl⟩ : syracuseStep 3218507 = 4827761) B4827761
theorem B2145671 : Blo 2145435 2145671 := bstep (se 1 (by rfl) ⟨1609253, by rfl⟩ : syracuseStep 2145671 = 3218507) B3218507
theorem B2413885 : Blo 2145435 2413885 := bbase (se 3 (by rfl) ⟨452603, by rfl⟩ : syracuseStep 2413885 = 905207) (by norm_num)
theorem B3218513 : Blo 2145435 3218513 := bstep (se 2 (by rfl) ⟨1206942, by rfl⟩ : syracuseStep 3218513 = 2413885) B2413885
theorem B2145675 : Blo 2145435 2145675 := bstep (se 1 (by rfl) ⟨1609256, by rfl⟩ : syracuseStep 2145675 = 3218513) B3218513
theorem B7241669 : Blo 2145435 7241669 := bbase (se 4 (by rfl) ⟨678906, by rfl⟩ : syracuseStep 7241669 = 1357813) (by norm_num)
theorem B4827779 : Blo 2145435 4827779 := bstep (se 1 (by rfl) ⟨3620834, by rfl⟩ : syracuseStep 4827779 = 7241669) B7241669
theorem B3218519 : Blo 2145435 3218519 := bstep (se 1 (by rfl) ⟨2413889, by rfl⟩ : syracuseStep 3218519 = 4827779) B4827779
theorem B2145679 : Blo 2145435 2145679 := bstep (se 1 (by rfl) ⟨1609259, by rfl⟩ : syracuseStep 2145679 = 3218519) B3218519
theorem B3218525 : Blo 2145435 3218525 := bbase (se 3 (by rfl) ⟨603473, by rfl⟩ : syracuseStep 3218525 = 1206947) (by norm_num)
theorem B2145683 : Blo 2145435 2145683 := bstep (se 1 (by rfl) ⟨1609262, by rfl⟩ : syracuseStep 2145683 = 3218525) B3218525
theorem B4827797 : Blo 2145435 4827797 := bbase (se 6 (by rfl) ⟨113151, by rfl⟩ : syracuseStep 4827797 = 226303) (by norm_num)
theorem B3218531 : Blo 2145435 3218531 := bstep (se 1 (by rfl) ⟨2413898, by rfl⟩ : syracuseStep 3218531 = 4827797) B4827797
theorem B2145687 : Blo 2145435 2145687 := bstep (se 1 (by rfl) ⟨1609265, by rfl⟩ : syracuseStep 2145687 = 3218531) B3218531
theorem B2899957 : Blo 2145435 2899957 := bbase (se 5 (by rfl) ⟨135935, by rfl⟩ : syracuseStep 2899957 = 271871) (by norm_num)
theorem B3866609 : Blo 2145435 3866609 := bstep (se 2 (by rfl) ⟨1449978, by rfl⟩ : syracuseStep 3866609 = 2899957) B2899957
theorem B2577739 : Blo 2145435 2577739 := bstep (se 1 (by rfl) ⟨1933304, by rfl⟩ : syracuseStep 2577739 = 3866609) B3866609
theorem B3436985 : Blo 2145435 3436985 := bstep (se 2 (by rfl) ⟨1288869, by rfl⟩ : syracuseStep 3436985 = 2577739) B2577739
theorem B2291323 : Blo 2145435 2291323 := bstep (se 1 (by rfl) ⟨1718492, by rfl⟩ : syracuseStep 2291323 = 3436985) B3436985
theorem B3055097 : Blo 2145435 3055097 := bstep (se 2 (by rfl) ⟨1145661, by rfl⟩ : syracuseStep 3055097 = 2291323) B2291323
theorem B8146925 : Blo 2145435 8146925 := bstep (se 3 (by rfl) ⟨1527548, by rfl⟩ : syracuseStep 8146925 = 3055097) B3055097
theorem B5431283 : Blo 2145435 5431283 := bstep (se 1 (by rfl) ⟨4073462, by rfl⟩ : syracuseStep 5431283 = 8146925) B8146925
theorem B3620855 : Blo 2145435 3620855 := bstep (se 1 (by rfl) ⟨2715641, by rfl⟩ : syracuseStep 3620855 = 5431283) B5431283
theorem B2413903 : Blo 2145435 2413903 := bstep (se 1 (by rfl) ⟨1810427, by rfl⟩ : syracuseStep 2413903 = 3620855) B3620855
theorem B3218537 : Blo 2145435 3218537 := bstep (se 2 (by rfl) ⟨1206951, by rfl⟩ : syracuseStep 3218537 = 2413903) B2413903
theorem B2145691 : Blo 2145435 2145691 := bstep (se 1 (by rfl) ⟨1609268, by rfl⟩ : syracuseStep 2145691 = 3218537) B3218537
theorem B17399765 : Blo 2145435 17399765 := bbase (se 7 (by rfl) ⟨203903, by rfl⟩ : syracuseStep 17399765 = 407807) (by norm_num)
theorem B11599843 : Blo 2145435 11599843 := bstep (se 1 (by rfl) ⟨8699882, by rfl⟩ : syracuseStep 11599843 = 17399765) B17399765
theorem B15466457 : Blo 2145435 15466457 := bstep (se 2 (by rfl) ⟨5799921, by rfl⟩ : syracuseStep 15466457 = 11599843) B11599843
theorem B10310971 : Blo 2145435 10310971 := bstep (se 1 (by rfl) ⟨7733228, by rfl⟩ : syracuseStep 10310971 = 15466457) B15466457
theorem B13747961 : Blo 2145435 13747961 := bstep (se 2 (by rfl) ⟨5155485, by rfl⟩ : syracuseStep 13747961 = 10310971) B10310971
theorem B9165307 : Blo 2145435 9165307 := bstep (se 1 (by rfl) ⟨6873980, by rfl⟩ : syracuseStep 9165307 = 13747961) B13747961
theorem B12220409 : Blo 2145435 12220409 := bstep (se 2 (by rfl) ⟨4582653, by rfl⟩ : syracuseStep 12220409 = 9165307) B9165307
theorem B8146939 : Blo 2145435 8146939 := bstep (se 1 (by rfl) ⟨6110204, by rfl⟩ : syracuseStep 8146939 = 12220409) B12220409
theorem B10862585 : Blo 2145435 10862585 := bstep (se 2 (by rfl) ⟨4073469, by rfl⟩ : syracuseStep 10862585 = 8146939) B8146939
theorem B7241723 : Blo 2145435 7241723 := bstep (se 1 (by rfl) ⟨5431292, by rfl⟩ : syracuseStep 7241723 = 10862585) B10862585
theorem B4827815 : Blo 2145435 4827815 := bstep (se 1 (by rfl) ⟨3620861, by rfl⟩ : syracuseStep 4827815 = 7241723) B7241723
theorem B3218543 : Blo 2145435 3218543 := bstep (se 1 (by rfl) ⟨2413907, by rfl⟩ : syracuseStep 3218543 = 4827815) B4827815
theorem B2145695 : Blo 2145435 2145695 := bstep (se 1 (by rfl) ⟨1609271, by rfl⟩ : syracuseStep 2145695 = 3218543) B3218543
theorem B3218549 : Blo 2145435 3218549 := bbase (se 5 (by rfl) ⟨150869, by rfl⟩ : syracuseStep 3218549 = 301739) (by norm_num)
theorem B2145699 : Blo 2145435 2145699 := bstep (se 1 (by rfl) ⟨1609274, by rfl⟩ : syracuseStep 2145699 = 3218549) B3218549
theorem B4073485 : Blo 2145435 4073485 := bbase (se 3 (by rfl) ⟨763778, by rfl⟩ : syracuseStep 4073485 = 1527557) (by norm_num)
theorem B5431313 : Blo 2145435 5431313 := bstep (se 2 (by rfl) ⟨2036742, by rfl⟩ : syracuseStep 5431313 = 4073485) B4073485
theorem B3620875 : Blo 2145435 3620875 := bstep (se 1 (by rfl) ⟨2715656, by rfl⟩ : syracuseStep 3620875 = 5431313) B5431313
theorem B4827833 : Blo 2145435 4827833 := bstep (se 2 (by rfl) ⟨1810437, by rfl⟩ : syracuseStep 4827833 = 3620875) B3620875
theorem B3218555 : Blo 2145435 3218555 := bstep (se 1 (by rfl) ⟨2413916, by rfl⟩ : syracuseStep 3218555 = 4827833) B4827833
theorem B2145703 : Blo 2145435 2145703 := bstep (se 1 (by rfl) ⟨1609277, by rfl⟩ : syracuseStep 2145703 = 3218555) B3218555
theorem B2413921 : Blo 2145435 2413921 := bbase (se 2 (by rfl) ⟨905220, by rfl⟩ : syracuseStep 2413921 = 1810441) (by norm_num)
theorem B3218561 : Blo 2145435 3218561 := bstep (se 2 (by rfl) ⟨1206960, by rfl⟩ : syracuseStep 3218561 = 2413921) B2413921
theorem B2145707 : Blo 2145435 2145707 := bstep (se 1 (by rfl) ⟨1609280, by rfl⟩ : syracuseStep 2145707 = 3218561) B3218561
theorem B5431333 : Blo 2145435 5431333 := bbase (se 4 (by rfl) ⟨509187, by rfl⟩ : syracuseStep 5431333 = 1018375) (by norm_num)
theorem B7241777 : Blo 2145435 7241777 := bstep (se 2 (by rfl) ⟨2715666, by rfl⟩ : syracuseStep 7241777 = 5431333) B5431333
theorem B4827851 : Blo 2145435 4827851 := bstep (se 1 (by rfl) ⟨3620888, by rfl⟩ : syracuseStep 4827851 = 7241777) B7241777
theorem B3218567 : Blo 2145435 3218567 := bstep (se 1 (by rfl) ⟨2413925, by rfl⟩ : syracuseStep 3218567 = 4827851) B4827851
theorem B2145711 : Blo 2145435 2145711 := bstep (se 1 (by rfl) ⟨1609283, by rfl⟩ : syracuseStep 2145711 = 3218567) B3218567
theorem B3218573 : Blo 2145435 3218573 := bbase (se 3 (by rfl) ⟨603482, by rfl⟩ : syracuseStep 3218573 = 1206965) (by norm_num)
theorem B2145715 : Blo 2145435 2145715 := bstep (se 1 (by rfl) ⟨1609286, by rfl⟩ : syracuseStep 2145715 = 3218573) B3218573
theorem B4827869 : Blo 2145435 4827869 := bbase (se 3 (by rfl) ⟨905225, by rfl⟩ : syracuseStep 4827869 = 1810451) (by norm_num)
theorem B3218579 : Blo 2145435 3218579 := bstep (se 1 (by rfl) ⟨2413934, by rfl⟩ : syracuseStep 3218579 = 4827869) B4827869
theorem B2145719 : Blo 2145435 2145719 := bstep (se 1 (by rfl) ⟨1609289, by rfl⟩ : syracuseStep 2145719 = 3218579) B3218579
theorem B3620909 : Blo 2145435 3620909 := bbase (se 3 (by rfl) ⟨678920, by rfl⟩ : syracuseStep 3620909 = 1357841) (by norm_num)
theorem B2413939 : Blo 2145435 2413939 := bstep (se 1 (by rfl) ⟨1810454, by rfl⟩ : syracuseStep 2413939 = 3620909) B3620909
theorem B3218585 : Blo 2145435 3218585 := bstep (se 2 (by rfl) ⟨1206969, by rfl⟩ : syracuseStep 3218585 = 2413939) B2413939
theorem B2145723 : Blo 2145435 2145723 := bstep (se 1 (by rfl) ⟨1609292, by rfl⟩ : syracuseStep 2145723 = 3218585) B3218585
theorem B4960525 : Blo 2145435 4960525 := bbase (se 3 (by rfl) ⟨930098, by rfl⟩ : syracuseStep 4960525 = 1860197) (by norm_num)
theorem B6614033 : Blo 2145435 6614033 := bstep (se 2 (by rfl) ⟨2480262, by rfl⟩ : syracuseStep 6614033 = 4960525) B4960525
theorem B17637421 : Blo 2145435 17637421 := bstep (se 3 (by rfl) ⟨3307016, by rfl⟩ : syracuseStep 17637421 = 6614033) B6614033
theorem B23516561 : Blo 2145435 23516561 := bstep (se 2 (by rfl) ⟨8818710, by rfl⟩ : syracuseStep 23516561 = 17637421) B17637421
theorem B15677707 : Blo 2145435 15677707 := bstep (se 1 (by rfl) ⟨11758280, by rfl⟩ : syracuseStep 15677707 = 23516561) B23516561
theorem B20903609 : Blo 2145435 20903609 := bstep (se 2 (by rfl) ⟨7838853, by rfl⟩ : syracuseStep 20903609 = 15677707) B15677707
theorem B13935739 : Blo 2145435 13935739 := bstep (se 1 (by rfl) ⟨10451804, by rfl⟩ : syracuseStep 13935739 = 20903609) B20903609
theorem B18580985 : Blo 2145435 18580985 := bstep (se 2 (by rfl) ⟨6967869, by rfl⟩ : syracuseStep 18580985 = 13935739) B13935739
theorem B12387323 : Blo 2145435 12387323 := bstep (se 1 (by rfl) ⟨9290492, by rfl⟩ : syracuseStep 12387323 = 18580985) B18580985
theorem B8258215 : Blo 2145435 8258215 := bstep (se 1 (by rfl) ⟨6193661, by rfl⟩ : syracuseStep 8258215 = 12387323) B12387323
theorem B11010953 : Blo 2145435 11010953 := bstep (se 2 (by rfl) ⟨4129107, by rfl⟩ : syracuseStep 11010953 = 8258215) B8258215
theorem B7340635 : Blo 2145435 7340635 := bstep (se 1 (by rfl) ⟨5505476, by rfl⟩ : syracuseStep 7340635 = 11010953) B11010953
theorem B39150053 : Blo 2145435 39150053 := bstep (se 4 (by rfl) ⟨3670317, by rfl⟩ : syracuseStep 39150053 = 7340635) B7340635
theorem B26100035 : Blo 2145435 26100035 := bstep (se 1 (by rfl) ⟨19575026, by rfl⟩ : syracuseStep 26100035 = 39150053) B39150053
theorem B17400023 : Blo 2145435 17400023 := bstep (se 1 (by rfl) ⟨13050017, by rfl⟩ : syracuseStep 17400023 = 26100035) B26100035
theorem B11600015 : Blo 2145435 11600015 := bstep (se 1 (by rfl) ⟨8700011, by rfl⟩ : syracuseStep 11600015 = 17400023) B17400023
theorem B30933373 : Blo 2145435 30933373 := bstep (se 3 (by rfl) ⟨5800007, by rfl⟩ : syracuseStep 30933373 = 11600015) B11600015
theorem B41244497 : Blo 2145435 41244497 := bstep (se 2 (by rfl) ⟨15466686, by rfl⟩ : syracuseStep 41244497 = 30933373) B30933373
theorem B27496331 : Blo 2145435 27496331 := bstep (se 1 (by rfl) ⟨20622248, by rfl⟩ : syracuseStep 27496331 = 41244497) B41244497
theorem B18330887 : Blo 2145435 18330887 := bstep (se 1 (by rfl) ⟨13748165, by rfl⟩ : syracuseStep 18330887 = 27496331) B27496331
theorem B12220591 : Blo 2145435 12220591 := bstep (se 1 (by rfl) ⟨9165443, by rfl⟩ : syracuseStep 12220591 = 18330887) B18330887
theorem B16294121 : Blo 2145435 16294121 := bstep (se 2 (by rfl) ⟨6110295, by rfl⟩ : syracuseStep 16294121 = 12220591) B12220591
theorem B10862747 : Blo 2145435 10862747 := bstep (se 1 (by rfl) ⟨8147060, by rfl⟩ : syracuseStep 10862747 = 16294121) B16294121
theorem B7241831 : Blo 2145435 7241831 := bstep (se 1 (by rfl) ⟨5431373, by rfl⟩ : syracuseStep 7241831 = 10862747) B10862747
theorem B4827887 : Blo 2145435 4827887 := bstep (se 1 (by rfl) ⟨3620915, by rfl⟩ : syracuseStep 4827887 = 7241831) B7241831
theorem B3218591 : Blo 2145435 3218591 := bstep (se 1 (by rfl) ⟨2413943, by rfl⟩ : syracuseStep 3218591 = 4827887) B4827887
theorem B2145727 : Blo 2145435 2145727 := bstep (se 1 (by rfl) ⟨1609295, by rfl⟩ : syracuseStep 2145727 = 3218591) B3218591
theorem B3218597 : Blo 2145435 3218597 := bbase (se 4 (by rfl) ⟨301743, by rfl⟩ : syracuseStep 3218597 = 603487) (by norm_num)
theorem B2145731 : Blo 2145435 2145731 := bstep (se 1 (by rfl) ⟨1609298, by rfl⟩ : syracuseStep 2145731 = 3218597) B3218597
theorem B2715697 : Blo 2145435 2715697 := bbase (se 2 (by rfl) ⟨1018386, by rfl⟩ : syracuseStep 2715697 = 2036773) (by norm_num)
theorem B3620929 : Blo 2145435 3620929 := bstep (se 2 (by rfl) ⟨1357848, by rfl⟩ : syracuseStep 3620929 = 2715697) B2715697
theorem B4827905 : Blo 2145435 4827905 := bstep (se 2 (by rfl) ⟨1810464, by rfl⟩ : syracuseStep 4827905 = 3620929) B3620929
theorem B3218603 : Blo 2145435 3218603 := bstep (se 1 (by rfl) ⟨2413952, by rfl⟩ : syracuseStep 3218603 = 4827905) B4827905
theorem B2145735 : Blo 2145435 2145735 := bstep (se 1 (by rfl) ⟨1609301, by rfl⟩ : syracuseStep 2145735 = 3218603) B3218603
theorem B2413957 : Blo 2145435 2413957 := bbase (se 4 (by rfl) ⟨226308, by rfl⟩ : syracuseStep 2413957 = 452617) (by norm_num)
theorem B3218609 : Blo 2145435 3218609 := bstep (se 2 (by rfl) ⟨1206978, by rfl⟩ : syracuseStep 3218609 = 2413957) B2413957
theorem B2145739 : Blo 2145435 2145739 := bstep (se 1 (by rfl) ⟨1609304, by rfl⟩ : syracuseStep 2145739 = 3218609) B3218609
theorem B4582757 : Blo 2145435 4582757 := bbase (se 4 (by rfl) ⟨429633, by rfl⟩ : syracuseStep 4582757 = 859267) (by norm_num)
theorem B3055171 : Blo 2145435 3055171 := bstep (se 1 (by rfl) ⟨2291378, by rfl⟩ : syracuseStep 3055171 = 4582757) B4582757
theorem B4073561 : Blo 2145435 4073561 := bstep (se 2 (by rfl) ⟨1527585, by rfl⟩ : syracuseStep 4073561 = 3055171) B3055171
theorem B2715707 : Blo 2145435 2715707 := bstep (se 1 (by rfl) ⟨2036780, by rfl⟩ : syracuseStep 2715707 = 4073561) B4073561
theorem B7241885 : Blo 2145435 7241885 := bstep (se 3 (by rfl) ⟨1357853, by rfl⟩ : syracuseStep 7241885 = 2715707) B2715707
theorem B4827923 : Blo 2145435 4827923 := bstep (se 1 (by rfl) ⟨3620942, by rfl⟩ : syracuseStep 4827923 = 7241885) B7241885
theorem B3218615 : Blo 2145435 3218615 := bstep (se 1 (by rfl) ⟨2413961, by rfl⟩ : syracuseStep 3218615 = 4827923) B4827923
theorem B2145743 : Blo 2145435 2145743 := bstep (se 1 (by rfl) ⟨1609307, by rfl⟩ : syracuseStep 2145743 = 3218615) B3218615
theorem B3218621 : Blo 2145435 3218621 := bbase (se 3 (by rfl) ⟨603491, by rfl⟩ : syracuseStep 3218621 = 1206983) (by norm_num)
theorem B2145747 : Blo 2145435 2145747 := bstep (se 1 (by rfl) ⟨1609310, by rfl⟩ : syracuseStep 2145747 = 3218621) B3218621
theorem B4827941 : Blo 2145435 4827941 := bbase (se 4 (by rfl) ⟨452619, by rfl⟩ : syracuseStep 4827941 = 905239) (by norm_num)
theorem B3218627 : Blo 2145435 3218627 := bstep (se 1 (by rfl) ⟨2413970, by rfl⟩ : syracuseStep 3218627 = 4827941) B4827941
theorem B2145751 : Blo 2145435 2145751 := bstep (se 1 (by rfl) ⟨1609313, by rfl⟩ : syracuseStep 2145751 = 3218627) B3218627
theorem B5431445 : Blo 2145435 5431445 := bbase (se 6 (by rfl) ⟨127299, by rfl⟩ : syracuseStep 5431445 = 254599) (by norm_num)
theorem B3620963 : Blo 2145435 3620963 := bstep (se 1 (by rfl) ⟨2715722, by rfl⟩ : syracuseStep 3620963 = 5431445) B5431445
theorem B2413975 : Blo 2145435 2413975 := bstep (se 1 (by rfl) ⟨1810481, by rfl⟩ : syracuseStep 2413975 = 3620963) B3620963
theorem B3218633 : Blo 2145435 3218633 := bstep (se 2 (by rfl) ⟨1206987, by rfl⟩ : syracuseStep 3218633 = 2413975) B2413975
theorem B2145755 : Blo 2145435 2145755 := bstep (se 1 (by rfl) ⟨1609316, by rfl⟩ : syracuseStep 2145755 = 3218633) B3218633
theorem B3437093 : Blo 2145435 3437093 := bbase (se 4 (by rfl) ⟨322227, by rfl⟩ : syracuseStep 3437093 = 644455) (by norm_num)
theorem B9165581 : Blo 2145435 9165581 := bstep (se 3 (by rfl) ⟨1718546, by rfl⟩ : syracuseStep 9165581 = 3437093) B3437093
theorem B6110387 : Blo 2145435 6110387 := bstep (se 1 (by rfl) ⟨4582790, by rfl⟩ : syracuseStep 6110387 = 9165581) B9165581
theorem B4073591 : Blo 2145435 4073591 := bstep (se 1 (by rfl) ⟨3055193, by rfl⟩ : syracuseStep 4073591 = 6110387) B6110387
theorem B10862909 : Blo 2145435 10862909 := bstep (se 3 (by rfl) ⟨2036795, by rfl⟩ : syracuseStep 10862909 = 4073591) B4073591
theorem B7241939 : Blo 2145435 7241939 := bstep (se 1 (by rfl) ⟨5431454, by rfl⟩ : syracuseStep 7241939 = 10862909) B10862909
theorem B4827959 : Blo 2145435 4827959 := bstep (se 1 (by rfl) ⟨3620969, by rfl⟩ : syracuseStep 4827959 = 7241939) B7241939
theorem B3218639 : Blo 2145435 3218639 := bstep (se 1 (by rfl) ⟨2413979, by rfl⟩ : syracuseStep 3218639 = 4827959) B4827959
theorem B2145759 : Blo 2145435 2145759 := bstep (se 1 (by rfl) ⟨1609319, by rfl⟩ : syracuseStep 2145759 = 3218639) B3218639
theorem B3218645 : Blo 2145435 3218645 := bbase (se 7 (by rfl) ⟨37718, by rfl⟩ : syracuseStep 3218645 = 75437) (by norm_num)
theorem B2145763 : Blo 2145435 2145763 := bstep (se 1 (by rfl) ⟨1609322, by rfl⟩ : syracuseStep 2145763 = 3218645) B3218645
theorem B3055205 : Blo 2145435 3055205 := bbase (se 4 (by rfl) ⟨286425, by rfl⟩ : syracuseStep 3055205 = 572851) (by norm_num)
theorem B8147213 : Blo 2145435 8147213 := bstep (se 3 (by rfl) ⟨1527602, by rfl⟩ : syracuseStep 8147213 = 3055205) B3055205
theorem B5431475 : Blo 2145435 5431475 := bstep (se 1 (by rfl) ⟨4073606, by rfl⟩ : syracuseStep 5431475 = 8147213) B8147213
theorem B3620983 : Blo 2145435 3620983 := bstep (se 1 (by rfl) ⟨2715737, by rfl⟩ : syracuseStep 3620983 = 5431475) B5431475
theorem B4827977 : Blo 2145435 4827977 := bstep (se 2 (by rfl) ⟨1810491, by rfl⟩ : syracuseStep 4827977 = 3620983) B3620983
theorem B3218651 : Blo 2145435 3218651 := bstep (se 1 (by rfl) ⟨2413988, by rfl⟩ : syracuseStep 3218651 = 4827977) B4827977
theorem B2145767 : Blo 2145435 2145767 := bstep (se 1 (by rfl) ⟨1609325, by rfl⟩ : syracuseStep 2145767 = 3218651) B3218651
theorem B2413993 : Blo 2145435 2413993 := bbase (se 2 (by rfl) ⟨905247, by rfl⟩ : syracuseStep 2413993 = 1810495) (by norm_num)
theorem B3218657 : Blo 2145435 3218657 := bstep (se 2 (by rfl) ⟨1206996, by rfl⟩ : syracuseStep 3218657 = 2413993) B2413993
theorem B2145771 : Blo 2145435 2145771 := bstep (se 1 (by rfl) ⟨1609328, by rfl⟩ : syracuseStep 2145771 = 3218657) B3218657
theorem B6525157 : Blo 2145435 6525157 := bbase (se 4 (by rfl) ⟨611733, by rfl⟩ : syracuseStep 6525157 = 1223467) (by norm_num)
theorem B8700209 : Blo 2145435 8700209 := bstep (se 2 (by rfl) ⟨3262578, by rfl⟩ : syracuseStep 8700209 = 6525157) B6525157
theorem B5800139 : Blo 2145435 5800139 := bstep (se 1 (by rfl) ⟨4350104, by rfl⟩ : syracuseStep 5800139 = 8700209) B8700209
theorem B3866759 : Blo 2145435 3866759 := bstep (se 1 (by rfl) ⟨2900069, by rfl⟩ : syracuseStep 3866759 = 5800139) B5800139
theorem B2577839 : Blo 2145435 2577839 := bstep (se 1 (by rfl) ⟨1933379, by rfl⟩ : syracuseStep 2577839 = 3866759) B3866759
theorem B6874237 : Blo 2145435 6874237 := bstep (se 3 (by rfl) ⟨1288919, by rfl⟩ : syracuseStep 6874237 = 2577839) B2577839
theorem B9165649 : Blo 2145435 9165649 := bstep (se 2 (by rfl) ⟨3437118, by rfl⟩ : syracuseStep 9165649 = 6874237) B6874237
theorem B12220865 : Blo 2145435 12220865 := bstep (se 2 (by rfl) ⟨4582824, by rfl⟩ : syracuseStep 12220865 = 9165649) B9165649
theorem B8147243 : Blo 2145435 8147243 := bstep (se 1 (by rfl) ⟨6110432, by rfl⟩ : syracuseStep 8147243 = 12220865) B12220865
theorem B5431495 : Blo 2145435 5431495 := bstep (se 1 (by rfl) ⟨4073621, by rfl⟩ : syracuseStep 5431495 = 8147243) B8147243
theorem B7241993 : Blo 2145435 7241993 := bstep (se 2 (by rfl) ⟨2715747, by rfl⟩ : syracuseStep 7241993 = 5431495) B5431495
theorem B4827995 : Blo 2145435 4827995 := bstep (se 1 (by rfl) ⟨3620996, by rfl⟩ : syracuseStep 4827995 = 7241993) B7241993
theorem B3218663 : Blo 2145435 3218663 := bstep (se 1 (by rfl) ⟨2413997, by rfl⟩ : syracuseStep 3218663 = 4827995) B4827995
theorem B2145775 : Blo 2145435 2145775 := bstep (se 1 (by rfl) ⟨1609331, by rfl⟩ : syracuseStep 2145775 = 3218663) B3218663
theorem B3218669 : Blo 2145435 3218669 := bbase (se 3 (by rfl) ⟨603500, by rfl⟩ : syracuseStep 3218669 = 1207001) (by norm_num)
theorem B2145779 : Blo 2145435 2145779 := bstep (se 1 (by rfl) ⟨1609334, by rfl⟩ : syracuseStep 2145779 = 3218669) B3218669
theorem B4828013 : Blo 2145435 4828013 := bbase (se 3 (by rfl) ⟨905252, by rfl⟩ : syracuseStep 4828013 = 1810505) (by norm_num)
theorem B3218675 : Blo 2145435 3218675 := bstep (se 1 (by rfl) ⟨2414006, by rfl⟩ : syracuseStep 3218675 = 4828013) B4828013
theorem B2145783 : Blo 2145435 2145783 := bstep (se 1 (by rfl) ⟨1609337, by rfl⟩ : syracuseStep 2145783 = 3218675) B3218675
theorem B4073645 : Blo 2145435 4073645 := bbase (se 3 (by rfl) ⟨763808, by rfl⟩ : syracuseStep 4073645 = 1527617) (by norm_num)
theorem B2715763 : Blo 2145435 2715763 := bstep (se 1 (by rfl) ⟨2036822, by rfl⟩ : syracuseStep 2715763 = 4073645) B4073645
theorem B3621017 : Blo 2145435 3621017 := bstep (se 2 (by rfl) ⟨1357881, by rfl⟩ : syracuseStep 3621017 = 2715763) B2715763
theorem B2414011 : Blo 2145435 2414011 := bstep (se 1 (by rfl) ⟨1810508, by rfl⟩ : syracuseStep 2414011 = 3621017) B3621017
theorem B3218681 : Blo 2145435 3218681 := bstep (se 2 (by rfl) ⟨1207005, by rfl⟩ : syracuseStep 3218681 = 2414011) B2414011
theorem B2145787 : Blo 2145435 2145787 := bstep (se 1 (by rfl) ⟨1609340, by rfl⟩ : syracuseStep 2145787 = 3218681) B3218681
theorem B5879317 : Blo 2145435 5879317 := bbase (se 6 (by rfl) ⟨137796, by rfl⟩ : syracuseStep 5879317 = 275593) (by norm_num)
theorem B7839089 : Blo 2145435 7839089 := bstep (se 2 (by rfl) ⟨2939658, by rfl⟩ : syracuseStep 7839089 = 5879317) B5879317
theorem B5226059 : Blo 2145435 5226059 := bstep (se 1 (by rfl) ⟨3919544, by rfl⟩ : syracuseStep 5226059 = 7839089) B7839089
theorem B13936157 : Blo 2145435 13936157 := bstep (se 3 (by rfl) ⟨2613029, by rfl⟩ : syracuseStep 13936157 = 5226059) B5226059
theorem B9290771 : Blo 2145435 9290771 := bstep (se 1 (by rfl) ⟨6968078, by rfl⟩ : syracuseStep 9290771 = 13936157) B13936157
theorem B6193847 : Blo 2145435 6193847 := bstep (se 1 (by rfl) ⟨4645385, by rfl⟩ : syracuseStep 6193847 = 9290771) B9290771
theorem B4129231 : Blo 2145435 4129231 := bstep (se 1 (by rfl) ⟨3096923, by rfl⟩ : syracuseStep 4129231 = 6193847) B6193847
theorem B5505641 : Blo 2145435 5505641 := bstep (se 2 (by rfl) ⟨2064615, by rfl⟩ : syracuseStep 5505641 = 4129231) B4129231
theorem B3670427 : Blo 2145435 3670427 := bstep (se 1 (by rfl) ⟨2752820, by rfl⟩ : syracuseStep 3670427 = 5505641) B5505641
theorem B9787805 : Blo 2145435 9787805 := bstep (se 3 (by rfl) ⟨1835213, by rfl⟩ : syracuseStep 9787805 = 3670427) B3670427
theorem B6525203 : Blo 2145435 6525203 := bstep (se 1 (by rfl) ⟨4893902, by rfl⟩ : syracuseStep 6525203 = 9787805) B9787805
theorem B69602165 : Blo 2145435 69602165 := bstep (se 5 (by rfl) ⟨3262601, by rfl⟩ : syracuseStep 69602165 = 6525203) B6525203
theorem B46401443 : Blo 2145435 46401443 := bstep (se 1 (by rfl) ⟨34801082, by rfl⟩ : syracuseStep 46401443 = 69602165) B69602165
theorem B30934295 : Blo 2145435 30934295 := bstep (se 1 (by rfl) ⟨23200721, by rfl⟩ : syracuseStep 30934295 = 46401443) B46401443
theorem B20622863 : Blo 2145435 20622863 := bstep (se 1 (by rfl) ⟨15467147, by rfl⟩ : syracuseStep 20622863 = 30934295) B30934295
theorem B54994301 : Blo 2145435 54994301 := bstep (se 3 (by rfl) ⟨10311431, by rfl⟩ : syracuseStep 54994301 = 20622863) B20622863
theorem B36662867 : Blo 2145435 36662867 := bstep (se 1 (by rfl) ⟨27497150, by rfl⟩ : syracuseStep 36662867 = 54994301) B54994301
theorem B24441911 : Blo 2145435 24441911 := bstep (se 1 (by rfl) ⟨18331433, by rfl⟩ : syracuseStep 24441911 = 36662867) B36662867
theorem B16294607 : Blo 2145435 16294607 := bstep (se 1 (by rfl) ⟨12220955, by rfl⟩ : syracuseStep 16294607 = 24441911) B24441911
theorem B10863071 : Blo 2145435 10863071 := bstep (se 1 (by rfl) ⟨8147303, by rfl⟩ : syracuseStep 10863071 = 16294607) B16294607
theorem B7242047 : Blo 2145435 7242047 := bstep (se 1 (by rfl) ⟨5431535, by rfl⟩ : syracuseStep 7242047 = 10863071) B10863071
theorem B4828031 : Blo 2145435 4828031 := bstep (se 1 (by rfl) ⟨3621023, by rfl⟩ : syracuseStep 4828031 = 7242047) B7242047
theorem B3218687 : Blo 2145435 3218687 := bstep (se 1 (by rfl) ⟨2414015, by rfl⟩ : syracuseStep 3218687 = 4828031) B4828031
theorem B2145791 : Blo 2145435 2145791 := bstep (se 1 (by rfl) ⟨1609343, by rfl⟩ : syracuseStep 2145791 = 3218687) B3218687
theorem B3218693 : Blo 2145435 3218693 := bbase (se 4 (by rfl) ⟨301752, by rfl⟩ : syracuseStep 3218693 = 603505) (by norm_num)
theorem B2145795 : Blo 2145435 2145795 := bstep (se 1 (by rfl) ⟨1609346, by rfl⟩ : syracuseStep 2145795 = 3218693) B3218693
theorem B3621037 : Blo 2145435 3621037 := bbase (se 3 (by rfl) ⟨678944, by rfl⟩ : syracuseStep 3621037 = 1357889) (by norm_num)
theorem B4828049 : Blo 2145435 4828049 := bstep (se 2 (by rfl) ⟨1810518, by rfl⟩ : syracuseStep 4828049 = 3621037) B3621037
theorem B3218699 : Blo 2145435 3218699 := bstep (se 1 (by rfl) ⟨2414024, by rfl⟩ : syracuseStep 3218699 = 4828049) B4828049
theorem B2145799 : Blo 2145435 2145799 := bstep (se 1 (by rfl) ⟨1609349, by rfl⟩ : syracuseStep 2145799 = 3218699) B3218699
theorem B2414029 : Blo 2145435 2414029 := bbase (se 3 (by rfl) ⟨452630, by rfl⟩ : syracuseStep 2414029 = 905261) (by norm_num)
theorem B3218705 : Blo 2145435 3218705 := bstep (se 2 (by rfl) ⟨1207014, by rfl⟩ : syracuseStep 3218705 = 2414029) B2414029
theorem B2145803 : Blo 2145435 2145803 := bstep (se 1 (by rfl) ⟨1609352, by rfl⟩ : syracuseStep 2145803 = 3218705) B3218705
theorem B7242101 : Blo 2145435 7242101 := bbase (se 5 (by rfl) ⟨339473, by rfl⟩ : syracuseStep 7242101 = 678947) (by norm_num)
theorem B4828067 : Blo 2145435 4828067 := bstep (se 1 (by rfl) ⟨3621050, by rfl⟩ : syracuseStep 4828067 = 7242101) B7242101
theorem B3218711 : Blo 2145435 3218711 := bstep (se 1 (by rfl) ⟨2414033, by rfl⟩ : syracuseStep 3218711 = 4828067) B4828067
theorem B2145807 : Blo 2145435 2145807 := bstep (se 1 (by rfl) ⟨1609355, by rfl⟩ : syracuseStep 2145807 = 3218711) B3218711
theorem B3218717 : Blo 2145435 3218717 := bbase (se 3 (by rfl) ⟨603509, by rfl⟩ : syracuseStep 3218717 = 1207019) (by norm_num)
theorem B2145811 : Blo 2145435 2145811 := bstep (se 1 (by rfl) ⟨1609358, by rfl⟩ : syracuseStep 2145811 = 3218717) B3218717
theorem B4828085 : Blo 2145435 4828085 := bbase (se 5 (by rfl) ⟨226316, by rfl⟩ : syracuseStep 4828085 = 452633) (by norm_num)
theorem B3218723 : Blo 2145435 3218723 := bstep (se 1 (by rfl) ⟨2414042, by rfl⟩ : syracuseStep 3218723 = 4828085) B4828085
theorem B2145815 : Blo 2145435 2145815 := bstep (se 1 (by rfl) ⟨1609361, by rfl⟩ : syracuseStep 2145815 = 3218723) B3218723
theorem B2175097 : Blo 2145435 2175097 := bbase (se 2 (by rfl) ⟨815661, by rfl⟩ : syracuseStep 2175097 = 1631323) (by norm_num)
theorem B2900129 : Blo 2145435 2900129 := bstep (se 2 (by rfl) ⟨1087548, by rfl⟩ : syracuseStep 2900129 = 2175097) B2175097
theorem B7733677 : Blo 2145435 7733677 := bstep (se 3 (by rfl) ⟨1450064, by rfl⟩ : syracuseStep 7733677 = 2900129) B2900129
theorem B10311569 : Blo 2145435 10311569 := bstep (se 2 (by rfl) ⟨3866838, by rfl⟩ : syracuseStep 10311569 = 7733677) B7733677
theorem B6874379 : Blo 2145435 6874379 := bstep (se 1 (by rfl) ⟨5155784, by rfl⟩ : syracuseStep 6874379 = 10311569) B10311569
theorem B4582919 : Blo 2145435 4582919 := bstep (se 1 (by rfl) ⟨3437189, by rfl⟩ : syracuseStep 4582919 = 6874379) B6874379
theorem B12221117 : Blo 2145435 12221117 := bstep (se 3 (by rfl) ⟨2291459, by rfl⟩ : syracuseStep 12221117 = 4582919) B4582919
theorem B8147411 : Blo 2145435 8147411 := bstep (se 1 (by rfl) ⟨6110558, by rfl⟩ : syracuseStep 8147411 = 12221117) B12221117
theorem B5431607 : Blo 2145435 5431607 := bstep (se 1 (by rfl) ⟨4073705, by rfl⟩ : syracuseStep 5431607 = 8147411) B8147411
theorem B3621071 : Blo 2145435 3621071 := bstep (se 1 (by rfl) ⟨2715803, by rfl⟩ : syracuseStep 3621071 = 5431607) B5431607
theorem B2414047 : Blo 2145435 2414047 := bstep (se 1 (by rfl) ⟨1810535, by rfl⟩ : syracuseStep 2414047 = 3621071) B3621071
theorem B3218729 : Blo 2145435 3218729 := bstep (se 2 (by rfl) ⟨1207023, by rfl⟩ : syracuseStep 3218729 = 2414047) B2414047
theorem B2145819 : Blo 2145435 2145819 := bstep (se 1 (by rfl) ⟨1609364, by rfl⟩ : syracuseStep 2145819 = 3218729) B3218729
theorem B15467381 : Blo 2145435 15467381 := bbase (se 5 (by rfl) ⟨725033, by rfl⟩ : syracuseStep 15467381 = 1450067) (by norm_num)
theorem B10311587 : Blo 2145435 10311587 := bstep (se 1 (by rfl) ⟨7733690, by rfl⟩ : syracuseStep 10311587 = 15467381) B15467381
theorem B6874391 : Blo 2145435 6874391 := bstep (se 1 (by rfl) ⟨5155793, by rfl⟩ : syracuseStep 6874391 = 10311587) B10311587
theorem B4582927 : Blo 2145435 4582927 := bstep (se 1 (by rfl) ⟨3437195, by rfl⟩ : syracuseStep 4582927 = 6874391) B6874391
theorem B6110569 : Blo 2145435 6110569 := bstep (se 2 (by rfl) ⟨2291463, by rfl⟩ : syracuseStep 6110569 = 4582927) B4582927
theorem B8147425 : Blo 2145435 8147425 := bstep (se 2 (by rfl) ⟨3055284, by rfl⟩ : syracuseStep 8147425 = 6110569) B6110569
theorem B10863233 : Blo 2145435 10863233 := bstep (se 2 (by rfl) ⟨4073712, by rfl⟩ : syracuseStep 10863233 = 8147425) B8147425
theorem B7242155 : Blo 2145435 7242155 := bstep (se 1 (by rfl) ⟨5431616, by rfl⟩ : syracuseStep 7242155 = 10863233) B10863233
theorem B4828103 : Blo 2145435 4828103 := bstep (se 1 (by rfl) ⟨3621077, by rfl⟩ : syracuseStep 4828103 = 7242155) B7242155
theorem B3218735 : Blo 2145435 3218735 := bstep (se 1 (by rfl) ⟨2414051, by rfl⟩ : syracuseStep 3218735 = 4828103) B4828103
theorem B2145823 : Blo 2145435 2145823 := bstep (se 1 (by rfl) ⟨1609367, by rfl⟩ : syracuseStep 2145823 = 3218735) B3218735
theorem B3218741 : Blo 2145435 3218741 := bbase (se 5 (by rfl) ⟨150878, by rfl⟩ : syracuseStep 3218741 = 301757) (by norm_num)
theorem B2145827 : Blo 2145435 2145827 := bstep (se 1 (by rfl) ⟨1609370, by rfl⟩ : syracuseStep 2145827 = 3218741) B3218741
theorem B5431637 : Blo 2145435 5431637 := bbase (se 10 (by rfl) ⟨7956, by rfl⟩ : syracuseStep 5431637 = 15913) (by norm_num)
theorem B3621091 : Blo 2145435 3621091 := bstep (se 1 (by rfl) ⟨2715818, by rfl⟩ : syracuseStep 3621091 = 5431637) B5431637
theorem B4828121 : Blo 2145435 4828121 := bstep (se 2 (by rfl) ⟨1810545, by rfl⟩ : syracuseStep 4828121 = 3621091) B3621091
theorem B3218747 : Blo 2145435 3218747 := bstep (se 1 (by rfl) ⟨2414060, by rfl⟩ : syracuseStep 3218747 = 4828121) B4828121
theorem B2145831 : Blo 2145435 2145831 := bstep (se 1 (by rfl) ⟨1609373, by rfl⟩ : syracuseStep 2145831 = 3218747) B3218747
theorem B2414065 : Blo 2145435 2414065 := bbase (se 2 (by rfl) ⟨905274, by rfl⟩ : syracuseStep 2414065 = 1810549) (by norm_num)
theorem B3218753 : Blo 2145435 3218753 := bstep (se 2 (by rfl) ⟨1207032, by rfl⟩ : syracuseStep 3218753 = 2414065) B2414065
theorem B2145835 : Blo 2145435 2145835 := bstep (se 1 (by rfl) ⟨1609376, by rfl⟩ : syracuseStep 2145835 = 3218753) B3218753
theorem B13748885 : Blo 2145435 13748885 := bbase (se 6 (by rfl) ⟨322239, by rfl⟩ : syracuseStep 13748885 = 644479) (by norm_num)
theorem B9165923 : Blo 2145435 9165923 := bstep (se 1 (by rfl) ⟨6874442, by rfl⟩ : syracuseStep 9165923 = 13748885) B13748885
theorem B6110615 : Blo 2145435 6110615 := bstep (se 1 (by rfl) ⟨4582961, by rfl⟩ : syracuseStep 6110615 = 9165923) B9165923
theorem B4073743 : Blo 2145435 4073743 := bstep (se 1 (by rfl) ⟨3055307, by rfl⟩ : syracuseStep 4073743 = 6110615) B6110615
theorem B5431657 : Blo 2145435 5431657 := bstep (se 2 (by rfl) ⟨2036871, by rfl⟩ : syracuseStep 5431657 = 4073743) B4073743
theorem B7242209 : Blo 2145435 7242209 := bstep (se 2 (by rfl) ⟨2715828, by rfl⟩ : syracuseStep 7242209 = 5431657) B5431657
theorem B4828139 : Blo 2145435 4828139 := bstep (se 1 (by rfl) ⟨3621104, by rfl⟩ : syracuseStep 4828139 = 7242209) B7242209
theorem B3218759 : Blo 2145435 3218759 := bstep (se 1 (by rfl) ⟨2414069, by rfl⟩ : syracuseStep 3218759 = 4828139) B4828139
theorem B2145839 : Blo 2145435 2145839 := bstep (se 1 (by rfl) ⟨1609379, by rfl⟩ : syracuseStep 2145839 = 3218759) B3218759
theorem B3218765 : Blo 2145435 3218765 := bbase (se 3 (by rfl) ⟨603518, by rfl⟩ : syracuseStep 3218765 = 1207037) (by norm_num)
theorem B2145843 : Blo 2145435 2145843 := bstep (se 1 (by rfl) ⟨1609382, by rfl⟩ : syracuseStep 2145843 = 3218765) B3218765
theorem B4828157 : Blo 2145435 4828157 := bbase (se 3 (by rfl) ⟨905279, by rfl⟩ : syracuseStep 4828157 = 1810559) (by norm_num)
theorem B3218771 : Blo 2145435 3218771 := bstep (se 1 (by rfl) ⟨2414078, by rfl⟩ : syracuseStep 3218771 = 4828157) B4828157
theorem B2145847 : Blo 2145435 2145847 := bstep (se 1 (by rfl) ⟨1609385, by rfl⟩ : syracuseStep 2145847 = 3218771) B3218771
theorem B3621125 : Blo 2145435 3621125 := bbase (se 4 (by rfl) ⟨339480, by rfl⟩ : syracuseStep 3621125 = 678961) (by norm_num)
theorem B2414083 : Blo 2145435 2414083 := bstep (se 1 (by rfl) ⟨1810562, by rfl⟩ : syracuseStep 2414083 = 3621125) B3621125
theorem B3218777 : Blo 2145435 3218777 := bstep (se 2 (by rfl) ⟨1207041, by rfl⟩ : syracuseStep 3218777 = 2414083) B2414083
theorem B2145851 : Blo 2145435 2145851 := bstep (se 1 (by rfl) ⟨1609388, by rfl⟩ : syracuseStep 2145851 = 3218777) B3218777
theorem B16295093 : Blo 2145435 16295093 := bbase (se 5 (by rfl) ⟨763832, by rfl⟩ : syracuseStep 16295093 = 1527665) (by norm_num)
theorem B10863395 : Blo 2145435 10863395 := bstep (se 1 (by rfl) ⟨8147546, by rfl⟩ : syracuseStep 10863395 = 16295093) B16295093
theorem B7242263 : Blo 2145435 7242263 := bstep (se 1 (by rfl) ⟨5431697, by rfl⟩ : syracuseStep 7242263 = 10863395) B10863395
theorem B4828175 : Blo 2145435 4828175 := bstep (se 1 (by rfl) ⟨3621131, by rfl⟩ : syracuseStep 4828175 = 7242263) B7242263
theorem B3218783 : Blo 2145435 3218783 := bstep (se 1 (by rfl) ⟨2414087, by rfl⟩ : syracuseStep 3218783 = 4828175) B4828175
theorem B2145855 : Blo 2145435 2145855 := bstep (se 1 (by rfl) ⟨1609391, by rfl⟩ : syracuseStep 2145855 = 3218783) B3218783
theorem B3218789 : Blo 2145435 3218789 := bbase (se 4 (by rfl) ⟨301761, by rfl⟩ : syracuseStep 3218789 = 603523) (by norm_num)
theorem B2145859 : Blo 2145435 2145859 := bstep (se 1 (by rfl) ⟨1609394, by rfl⟩ : syracuseStep 2145859 = 3218789) B3218789
theorem B4073789 : Blo 2145435 4073789 := bbase (se 3 (by rfl) ⟨763835, by rfl⟩ : syracuseStep 4073789 = 1527671) (by norm_num)
theorem B2715859 : Blo 2145435 2715859 := bstep (se 1 (by rfl) ⟨2036894, by rfl⟩ : syracuseStep 2715859 = 4073789) B4073789
theorem B3621145 : Blo 2145435 3621145 := bstep (se 2 (by rfl) ⟨1357929, by rfl⟩ : syracuseStep 3621145 = 2715859) B2715859
theorem B4828193 : Blo 2145435 4828193 := bstep (se 2 (by rfl) ⟨1810572, by rfl⟩ : syracuseStep 4828193 = 3621145) B3621145
theorem B3218795 : Blo 2145435 3218795 := bstep (se 1 (by rfl) ⟨2414096, by rfl⟩ : syracuseStep 3218795 = 4828193) B4828193
theorem B2145863 : Blo 2145435 2145863 := bstep (se 1 (by rfl) ⟨1609397, by rfl⟩ : syracuseStep 2145863 = 3218795) B3218795
theorem B2414101 : Blo 2145435 2414101 := bbase (se 6 (by rfl) ⟨56580, by rfl⟩ : syracuseStep 2414101 = 113161) (by norm_num)
theorem B3218801 : Blo 2145435 3218801 := bstep (se 2 (by rfl) ⟨1207050, by rfl⟩ : syracuseStep 3218801 = 2414101) B2414101
theorem B2145867 : Blo 2145435 2145867 := bstep (se 1 (by rfl) ⟨1609400, by rfl⟩ : syracuseStep 2145867 = 3218801) B3218801
theorem B2715869 : Blo 2145435 2715869 := bbase (se 3 (by rfl) ⟨509225, by rfl⟩ : syracuseStep 2715869 = 1018451) (by norm_num)
theorem B7242317 : Blo 2145435 7242317 := bstep (se 3 (by rfl) ⟨1357934, by rfl⟩ : syracuseStep 7242317 = 2715869) B2715869
theorem B4828211 : Blo 2145435 4828211 := bstep (se 1 (by rfl) ⟨3621158, by rfl⟩ : syracuseStep 4828211 = 7242317) B7242317
theorem B3218807 : Blo 2145435 3218807 := bstep (se 1 (by rfl) ⟨2414105, by rfl⟩ : syracuseStep 3218807 = 4828211) B4828211
theorem B2145871 : Blo 2145435 2145871 := bstep (se 1 (by rfl) ⟨1609403, by rfl⟩ : syracuseStep 2145871 = 3218807) B3218807
theorem B3218813 : Blo 2145435 3218813 := bbase (se 3 (by rfl) ⟨603527, by rfl⟩ : syracuseStep 3218813 = 1207055) (by norm_num)
theorem B2145875 : Blo 2145435 2145875 := bstep (se 1 (by rfl) ⟨1609406, by rfl⟩ : syracuseStep 2145875 = 3218813) B3218813
theorem B4828229 : Blo 2145435 4828229 := bbase (se 4 (by rfl) ⟨452646, by rfl⟩ : syracuseStep 4828229 = 905293) (by norm_num)
theorem B3218819 : Blo 2145435 3218819 := bstep (se 1 (by rfl) ⟨2414114, by rfl⟩ : syracuseStep 3218819 = 4828229) B4828229
theorem B2145879 : Blo 2145435 2145879 := bstep (se 1 (by rfl) ⟨1609409, by rfl⟩ : syracuseStep 2145879 = 3218819) B3218819
theorem B6110741 : Blo 2145435 6110741 := bbase (se 6 (by rfl) ⟨143220, by rfl⟩ : syracuseStep 6110741 = 286441) (by norm_num)
theorem B4073827 : Blo 2145435 4073827 := bstep (se 1 (by rfl) ⟨3055370, by rfl⟩ : syracuseStep 4073827 = 6110741) B6110741
theorem B5431769 : Blo 2145435 5431769 := bstep (se 2 (by rfl) ⟨2036913, by rfl⟩ : syracuseStep 5431769 = 4073827) B4073827
theorem B3621179 : Blo 2145435 3621179 := bstep (se 1 (by rfl) ⟨2715884, by rfl⟩ : syracuseStep 3621179 = 5431769) B5431769
theorem B2414119 : Blo 2145435 2414119 := bstep (se 1 (by rfl) ⟨1810589, by rfl⟩ : syracuseStep 2414119 = 3621179) B3621179
theorem B3218825 : Blo 2145435 3218825 := bstep (se 2 (by rfl) ⟨1207059, by rfl⟩ : syracuseStep 3218825 = 2414119) B2414119
theorem B2145883 : Blo 2145435 2145883 := bstep (se 1 (by rfl) ⟨1609412, by rfl⟩ : syracuseStep 2145883 = 3218825) B3218825
theorem B10863557 : Blo 2145435 10863557 := bbase (se 4 (by rfl) ⟨1018458, by rfl⟩ : syracuseStep 10863557 = 2036917) (by norm_num)
theorem B7242371 : Blo 2145435 7242371 := bstep (se 1 (by rfl) ⟨5431778, by rfl⟩ : syracuseStep 7242371 = 10863557) B10863557
theorem B4828247 : Blo 2145435 4828247 := bstep (se 1 (by rfl) ⟨3621185, by rfl⟩ : syracuseStep 4828247 = 7242371) B7242371
theorem B3218831 : Blo 2145435 3218831 := bstep (se 1 (by rfl) ⟨2414123, by rfl⟩ : syracuseStep 3218831 = 4828247) B4828247
theorem B2145887 : Blo 2145435 2145887 := bstep (se 1 (by rfl) ⟨1609415, by rfl⟩ : syracuseStep 2145887 = 3218831) B3218831
theorem B3218837 : Blo 2145435 3218837 := bbase (se 6 (by rfl) ⟨75441, by rfl⟩ : syracuseStep 3218837 = 150883) (by norm_num)
theorem B2145891 : Blo 2145435 2145891 := bstep (se 1 (by rfl) ⟨1609418, by rfl⟩ : syracuseStep 2145891 = 3218837) B3218837
theorem B3973213 : Blo 2145435 3973213 := bbase (se 3 (by rfl) ⟨744977, by rfl⟩ : syracuseStep 3973213 = 1489955) (by norm_num)
theorem B5297617 : Blo 2145435 5297617 := bstep (se 2 (by rfl) ⟨1986606, by rfl⟩ : syracuseStep 5297617 = 3973213) B3973213
theorem B7063489 : Blo 2145435 7063489 := bstep (se 2 (by rfl) ⟨2648808, by rfl⟩ : syracuseStep 7063489 = 5297617) B5297617
theorem B37671941 : Blo 2145435 37671941 := bstep (se 4 (by rfl) ⟨3531744, by rfl⟩ : syracuseStep 37671941 = 7063489) B7063489
theorem B25114627 : Blo 2145435 25114627 := bstep (se 1 (by rfl) ⟨18835970, by rfl⟩ : syracuseStep 25114627 = 37671941) B37671941
theorem B33486169 : Blo 2145435 33486169 := bstep (se 2 (by rfl) ⟨12557313, by rfl⟩ : syracuseStep 33486169 = 25114627) B25114627
theorem B44648225 : Blo 2145435 44648225 := bstep (se 2 (by rfl) ⟨16743084, by rfl⟩ : syracuseStep 44648225 = 33486169) B33486169
theorem B29765483 : Blo 2145435 29765483 := bstep (se 1 (by rfl) ⟨22324112, by rfl⟩ : syracuseStep 29765483 = 44648225) B44648225
theorem B19843655 : Blo 2145435 19843655 := bstep (se 1 (by rfl) ⟨14882741, by rfl⟩ : syracuseStep 19843655 = 29765483) B29765483
theorem B52916413 : Blo 2145435 52916413 := bstep (se 3 (by rfl) ⟨9921827, by rfl⟩ : syracuseStep 52916413 = 19843655) B19843655
theorem B70555217 : Blo 2145435 70555217 := bstep (se 2 (by rfl) ⟨26458206, by rfl⟩ : syracuseStep 70555217 = 52916413) B52916413
theorem B188147245 : Blo 2145435 188147245 := bstep (se 3 (by rfl) ⟨35277608, by rfl⟩ : syracuseStep 188147245 = 70555217) B70555217
theorem B250862993 : Blo 2145435 250862993 := bstep (se 2 (by rfl) ⟨94073622, by rfl⟩ : syracuseStep 250862993 = 188147245) B188147245
theorem B167241995 : Blo 2145435 167241995 := bstep (se 1 (by rfl) ⟨125431496, by rfl⟩ : syracuseStep 167241995 = 250862993) B250862993
theorem B111494663 : Blo 2145435 111494663 := bstep (se 1 (by rfl) ⟨83620997, by rfl⟩ : syracuseStep 111494663 = 167241995) B167241995
theorem B74329775 : Blo 2145435 74329775 := bstep (se 1 (by rfl) ⟨55747331, by rfl⟩ : syracuseStep 74329775 = 111494663) B111494663
theorem B49553183 : Blo 2145435 49553183 := bstep (se 1 (by rfl) ⟨37164887, by rfl⟩ : syracuseStep 49553183 = 74329775) B74329775
theorem B33035455 : Blo 2145435 33035455 := bstep (se 1 (by rfl) ⟨24776591, by rfl⟩ : syracuseStep 33035455 = 49553183) B49553183
theorem B44047273 : Blo 2145435 44047273 := bstep (se 2 (by rfl) ⟨16517727, by rfl⟩ : syracuseStep 44047273 = 33035455) B33035455
theorem B58729697 : Blo 2145435 58729697 := bstep (se 2 (by rfl) ⟨22023636, by rfl⟩ : syracuseStep 58729697 = 44047273) B44047273
theorem B39153131 : Blo 2145435 39153131 := bstep (se 1 (by rfl) ⟨29364848, by rfl⟩ : syracuseStep 39153131 = 58729697) B58729697
theorem B26102087 : Blo 2145435 26102087 := bstep (se 1 (by rfl) ⟨19576565, by rfl⟩ : syracuseStep 26102087 = 39153131) B39153131
theorem B17401391 : Blo 2145435 17401391 := bstep (se 1 (by rfl) ⟨13051043, by rfl⟩ : syracuseStep 17401391 = 26102087) B26102087
theorem B11600927 : Blo 2145435 11600927 := bstep (se 1 (by rfl) ⟨8700695, by rfl⟩ : syracuseStep 11600927 = 17401391) B17401391
theorem B7733951 : Blo 2145435 7733951 := bstep (se 1 (by rfl) ⟨5800463, by rfl⟩ : syracuseStep 7733951 = 11600927) B11600927
theorem B5155967 : Blo 2145435 5155967 := bstep (se 1 (by rfl) ⟨3866975, by rfl⟩ : syracuseStep 5155967 = 7733951) B7733951
theorem B3437311 : Blo 2145435 3437311 := bstep (se 1 (by rfl) ⟨2577983, by rfl⟩ : syracuseStep 3437311 = 5155967) B5155967
theorem B4583081 : Blo 2145435 4583081 := bstep (se 2 (by rfl) ⟨1718655, by rfl⟩ : syracuseStep 4583081 = 3437311) B3437311
theorem B12221549 : Blo 2145435 12221549 := bstep (se 3 (by rfl) ⟨2291540, by rfl⟩ : syracuseStep 12221549 = 4583081) B4583081
theorem B8147699 : Blo 2145435 8147699 := bstep (se 1 (by rfl) ⟨6110774, by rfl⟩ : syracuseStep 8147699 = 12221549) B12221549
theorem B5431799 : Blo 2145435 5431799 := bstep (se 1 (by rfl) ⟨4073849, by rfl⟩ : syracuseStep 5431799 = 8147699) B8147699
theorem B3621199 : Blo 2145435 3621199 := bstep (se 1 (by rfl) ⟨2715899, by rfl⟩ : syracuseStep 3621199 = 5431799) B5431799
theorem B4828265 : Blo 2145435 4828265 := bstep (se 2 (by rfl) ⟨1810599, by rfl⟩ : syracuseStep 4828265 = 3621199) B3621199
theorem B3218843 : Blo 2145435 3218843 := bstep (se 1 (by rfl) ⟨2414132, by rfl⟩ : syracuseStep 3218843 = 4828265) B4828265
theorem B2145895 : Blo 2145435 2145895 := bstep (se 1 (by rfl) ⟨1609421, by rfl⟩ : syracuseStep 2145895 = 3218843) B3218843
theorem B2414137 : Blo 2145435 2414137 := bbase (se 2 (by rfl) ⟨905301, by rfl⟩ : syracuseStep 2414137 = 1810603) (by norm_num)
theorem B3218849 : Blo 2145435 3218849 := bstep (se 2 (by rfl) ⟨1207068, by rfl⟩ : syracuseStep 3218849 = 2414137) B2414137
theorem B2145899 : Blo 2145435 2145899 := bstep (se 1 (by rfl) ⟨1609424, by rfl⟩ : syracuseStep 2145899 = 3218849) B3218849
theorem B2291549 : Blo 2145435 2291549 := bbase (se 3 (by rfl) ⟨429665, by rfl⟩ : syracuseStep 2291549 = 859331) (by norm_num)
theorem B6110797 : Blo 2145435 6110797 := bstep (se 3 (by rfl) ⟨1145774, by rfl⟩ : syracuseStep 6110797 = 2291549) B2291549
theorem B8147729 : Blo 2145435 8147729 := bstep (se 2 (by rfl) ⟨3055398, by rfl⟩ : syracuseStep 8147729 = 6110797) B6110797
theorem B5431819 : Blo 2145435 5431819 := bstep (se 1 (by rfl) ⟨4073864, by rfl⟩ : syracuseStep 5431819 = 8147729) B8147729
theorem B7242425 : Blo 2145435 7242425 := bstep (se 2 (by rfl) ⟨2715909, by rfl⟩ : syracuseStep 7242425 = 5431819) B5431819
theorem B4828283 : Blo 2145435 4828283 := bstep (se 1 (by rfl) ⟨3621212, by rfl⟩ : syracuseStep 4828283 = 7242425) B7242425
theorem B3218855 : Blo 2145435 3218855 := bstep (se 1 (by rfl) ⟨2414141, by rfl⟩ : syracuseStep 3218855 = 4828283) B4828283
theorem B2145903 : Blo 2145435 2145903 := bstep (se 1 (by rfl) ⟨1609427, by rfl⟩ : syracuseStep 2145903 = 3218855) B3218855
theorem B3218861 : Blo 2145435 3218861 := bbase (se 3 (by rfl) ⟨603536, by rfl⟩ : syracuseStep 3218861 = 1207073) (by norm_num)
theorem B2145907 : Blo 2145435 2145907 := bstep (se 1 (by rfl) ⟨1609430, by rfl⟩ : syracuseStep 2145907 = 3218861) B3218861
theorem B4828301 : Blo 2145435 4828301 := bbase (se 3 (by rfl) ⟨905306, by rfl⟩ : syracuseStep 4828301 = 1810613) (by norm_num)
theorem B3218867 : Blo 2145435 3218867 := bstep (se 1 (by rfl) ⟨2414150, by rfl⟩ : syracuseStep 3218867 = 4828301) B4828301
theorem B2145911 : Blo 2145435 2145911 := bstep (se 1 (by rfl) ⟨1609433, by rfl⟩ : syracuseStep 2145911 = 3218867) B3218867
theorem B2715925 : Blo 2145435 2715925 := bbase (se 6 (by rfl) ⟨63654, by rfl⟩ : syracuseStep 2715925 = 127309) (by norm_num)
theorem B3621233 : Blo 2145435 3621233 := bstep (se 2 (by rfl) ⟨1357962, by rfl⟩ : syracuseStep 3621233 = 2715925) B2715925
theorem B2414155 : Blo 2145435 2414155 := bstep (se 1 (by rfl) ⟨1810616, by rfl⟩ : syracuseStep 2414155 = 3621233) B3621233
theorem B3218873 : Blo 2145435 3218873 := bstep (se 2 (by rfl) ⟨1207077, by rfl⟩ : syracuseStep 3218873 = 2414155) B2414155
theorem B2145915 : Blo 2145435 2145915 := bstep (se 1 (by rfl) ⟨1609436, by rfl⟩ : syracuseStep 2145915 = 3218873) B3218873
theorem B2480485 : Blo 2145435 2480485 := bbase (se 4 (by rfl) ⟨232545, by rfl⟩ : syracuseStep 2480485 = 465091) (by norm_num)
theorem B3307313 : Blo 2145435 3307313 := bstep (se 2 (by rfl) ⟨1240242, by rfl⟩ : syracuseStep 3307313 = 2480485) B2480485
theorem B2204875 : Blo 2145435 2204875 := bstep (se 1 (by rfl) ⟨1653656, by rfl⟩ : syracuseStep 2204875 = 3307313) B3307313
theorem B2939833 : Blo 2145435 2939833 := bstep (se 2 (by rfl) ⟨1102437, by rfl⟩ : syracuseStep 2939833 = 2204875) B2204875
theorem B15679109 : Blo 2145435 15679109 := bstep (se 4 (by rfl) ⟨1469916, by rfl⟩ : syracuseStep 15679109 = 2939833) B2939833
theorem B10452739 : Blo 2145435 10452739 := bstep (se 1 (by rfl) ⟨7839554, by rfl⟩ : syracuseStep 10452739 = 15679109) B15679109
theorem B13936985 : Blo 2145435 13936985 := bstep (se 2 (by rfl) ⟨5226369, by rfl⟩ : syracuseStep 13936985 = 10452739) B10452739
theorem B9291323 : Blo 2145435 9291323 := bstep (se 1 (by rfl) ⟨6968492, by rfl⟩ : syracuseStep 9291323 = 13936985) B13936985
theorem B6194215 : Blo 2145435 6194215 := bstep (se 1 (by rfl) ⟨4645661, by rfl⟩ : syracuseStep 6194215 = 9291323) B9291323
theorem B33035813 : Blo 2145435 33035813 := bstep (se 4 (by rfl) ⟨3097107, by rfl⟩ : syracuseStep 33035813 = 6194215) B6194215
theorem B22023875 : Blo 2145435 22023875 := bstep (se 1 (by rfl) ⟨16517906, by rfl⟩ : syracuseStep 22023875 = 33035813) B33035813
theorem B14682583 : Blo 2145435 14682583 := bstep (se 1 (by rfl) ⟨11011937, by rfl⟩ : syracuseStep 14682583 = 22023875) B22023875
theorem B19576777 : Blo 2145435 19576777 := bstep (se 2 (by rfl) ⟨7341291, by rfl⟩ : syracuseStep 19576777 = 14682583) B14682583
theorem B26102369 : Blo 2145435 26102369 := bstep (se 2 (by rfl) ⟨9788388, by rfl⟩ : syracuseStep 26102369 = 19576777) B19576777
theorem B69606317 : Blo 2145435 69606317 := bstep (se 3 (by rfl) ⟨13051184, by rfl⟩ : syracuseStep 69606317 = 26102369) B26102369
theorem B46404211 : Blo 2145435 46404211 := bstep (se 1 (by rfl) ⟨34803158, by rfl⟩ : syracuseStep 46404211 = 69606317) B69606317
theorem B61872281 : Blo 2145435 61872281 := bstep (se 2 (by rfl) ⟨23202105, by rfl⟩ : syracuseStep 61872281 = 46404211) B46404211
theorem B41248187 : Blo 2145435 41248187 := bstep (se 1 (by rfl) ⟨30936140, by rfl⟩ : syracuseStep 41248187 = 61872281) B61872281
theorem B27498791 : Blo 2145435 27498791 := bstep (se 1 (by rfl) ⟨20624093, by rfl⟩ : syracuseStep 27498791 = 41248187) B41248187
theorem B18332527 : Blo 2145435 18332527 := bstep (se 1 (by rfl) ⟨13749395, by rfl⟩ : syracuseStep 18332527 = 27498791) B27498791
theorem B24443369 : Blo 2145435 24443369 := bstep (se 2 (by rfl) ⟨9166263, by rfl⟩ : syracuseStep 24443369 = 18332527) B18332527
theorem B16295579 : Blo 2145435 16295579 := bstep (se 1 (by rfl) ⟨12221684, by rfl⟩ : syracuseStep 16295579 = 24443369) B24443369
theorem B10863719 : Blo 2145435 10863719 := bstep (se 1 (by rfl) ⟨8147789, by rfl⟩ : syracuseStep 10863719 = 16295579) B16295579
theorem B7242479 : Blo 2145435 7242479 := bstep (se 1 (by rfl) ⟨5431859, by rfl⟩ : syracuseStep 7242479 = 10863719) B10863719
theorem B4828319 : Blo 2145435 4828319 := bstep (se 1 (by rfl) ⟨3621239, by rfl⟩ : syracuseStep 4828319 = 7242479) B7242479
theorem B3218879 : Blo 2145435 3218879 := bstep (se 1 (by rfl) ⟨2414159, by rfl⟩ : syracuseStep 3218879 = 4828319) B4828319
theorem B2145919 : Blo 2145435 2145919 := bstep (se 1 (by rfl) ⟨1609439, by rfl⟩ : syracuseStep 2145919 = 3218879) B3218879
theorem B3218885 : Blo 2145435 3218885 := bbase (se 4 (by rfl) ⟨301770, by rfl⟩ : syracuseStep 3218885 = 603541) (by norm_num)
theorem B2145923 : Blo 2145435 2145923 := bstep (se 1 (by rfl) ⟨1609442, by rfl⟩ : syracuseStep 2145923 = 3218885) B3218885
theorem B3621253 : Blo 2145435 3621253 := bbase (se 4 (by rfl) ⟨339492, by rfl⟩ : syracuseStep 3621253 = 678985) (by norm_num)
theorem B4828337 : Blo 2145435 4828337 := bstep (se 2 (by rfl) ⟨1810626, by rfl⟩ : syracuseStep 4828337 = 3621253) B3621253
theorem B3218891 : Blo 2145435 3218891 := bstep (se 1 (by rfl) ⟨2414168, by rfl⟩ : syracuseStep 3218891 = 4828337) B4828337
theorem B2145927 : Blo 2145435 2145927 := bstep (se 1 (by rfl) ⟨1609445, by rfl⟩ : syracuseStep 2145927 = 3218891) B3218891
theorem B2414173 : Blo 2145435 2414173 := bbase (se 3 (by rfl) ⟨452657, by rfl⟩ : syracuseStep 2414173 = 905315) (by norm_num)
theorem B3218897 : Blo 2145435 3218897 := bstep (se 2 (by rfl) ⟨1207086, by rfl⟩ : syracuseStep 3218897 = 2414173) B2414173
theorem B2145931 : Blo 2145435 2145931 := bstep (se 1 (by rfl) ⟨1609448, by rfl⟩ : syracuseStep 2145931 = 3218897) B3218897
theorem B7242533 : Blo 2145435 7242533 := bbase (se 4 (by rfl) ⟨678987, by rfl⟩ : syracuseStep 7242533 = 1357975) (by norm_num)
theorem B4828355 : Blo 2145435 4828355 := bstep (se 1 (by rfl) ⟨3621266, by rfl⟩ : syracuseStep 4828355 = 7242533) B7242533
theorem B3218903 : Blo 2145435 3218903 := bstep (se 1 (by rfl) ⟨2414177, by rfl⟩ : syracuseStep 3218903 = 4828355) B4828355
theorem B2145935 : Blo 2145435 2145935 := bstep (se 1 (by rfl) ⟨1609451, by rfl⟩ : syracuseStep 2145935 = 3218903) B3218903
theorem B3218909 : Blo 2145435 3218909 := bbase (se 3 (by rfl) ⟨603545, by rfl⟩ : syracuseStep 3218909 = 1207091) (by norm_num)
theorem B2145939 : Blo 2145435 2145939 := bstep (se 1 (by rfl) ⟨1609454, by rfl⟩ : syracuseStep 2145939 = 3218909) B3218909
theorem B4828373 : Blo 2145435 4828373 := bbase (se 7 (by rfl) ⟨56582, by rfl⟩ : syracuseStep 4828373 = 113165) (by norm_num)
theorem B3218915 : Blo 2145435 3218915 := bstep (se 1 (by rfl) ⟨2414186, by rfl⟩ : syracuseStep 3218915 = 4828373) B4828373
theorem B2145943 : Blo 2145435 2145943 := bstep (se 1 (by rfl) ⟨1609457, by rfl⟩ : syracuseStep 2145943 = 3218915) B3218915
theorem B6874789 : Blo 2145435 6874789 := bbase (se 4 (by rfl) ⟨644511, by rfl⟩ : syracuseStep 6874789 = 1289023) (by norm_num)
theorem B9166385 : Blo 2145435 9166385 := bstep (se 2 (by rfl) ⟨3437394, by rfl⟩ : syracuseStep 9166385 = 6874789) B6874789
theorem B6110923 : Blo 2145435 6110923 := bstep (se 1 (by rfl) ⟨4583192, by rfl⟩ : syracuseStep 6110923 = 9166385) B9166385
theorem B8147897 : Blo 2145435 8147897 := bstep (se 2 (by rfl) ⟨3055461, by rfl⟩ : syracuseStep 8147897 = 6110923) B6110923
theorem B5431931 : Blo 2145435 5431931 := bstep (se 1 (by rfl) ⟨4073948, by rfl⟩ : syracuseStep 5431931 = 8147897) B8147897
theorem B3621287 : Blo 2145435 3621287 := bstep (se 1 (by rfl) ⟨2715965, by rfl⟩ : syracuseStep 3621287 = 5431931) B5431931
theorem B2414191 : Blo 2145435 2414191 := bstep (se 1 (by rfl) ⟨1810643, by rfl⟩ : syracuseStep 2414191 = 3621287) B3621287
theorem B3218921 : Blo 2145435 3218921 := bstep (se 2 (by rfl) ⟨1207095, by rfl⟩ : syracuseStep 3218921 = 2414191) B2414191
theorem B2145947 : Blo 2145435 2145947 := bstep (se 1 (by rfl) ⟨1609460, by rfl⟩ : syracuseStep 2145947 = 3218921) B3218921
theorem B13051381 : Blo 2145435 13051381 := bbase (se 5 (by rfl) ⟨611783, by rfl⟩ : syracuseStep 13051381 = 1223567) (by norm_num)
theorem B17401841 : Blo 2145435 17401841 := bstep (se 2 (by rfl) ⟨6525690, by rfl⟩ : syracuseStep 17401841 = 13051381) B13051381
theorem B11601227 : Blo 2145435 11601227 := bstep (se 1 (by rfl) ⟨8700920, by rfl⟩ : syracuseStep 11601227 = 17401841) B17401841
theorem B7734151 : Blo 2145435 7734151 := bstep (se 1 (by rfl) ⟨5800613, by rfl⟩ : syracuseStep 7734151 = 11601227) B11601227
theorem B10312201 : Blo 2145435 10312201 := bstep (se 2 (by rfl) ⟨3867075, by rfl⟩ : syracuseStep 10312201 = 7734151) B7734151
theorem B13749601 : Blo 2145435 13749601 := bstep (se 2 (by rfl) ⟨5156100, by rfl⟩ : syracuseStep 13749601 = 10312201) B10312201
theorem B18332801 : Blo 2145435 18332801 := bstep (se 2 (by rfl) ⟨6874800, by rfl⟩ : syracuseStep 18332801 = 13749601) B13749601
theorem B12221867 : Blo 2145435 12221867 := bstep (se 1 (by rfl) ⟨9166400, by rfl⟩ : syracuseStep 12221867 = 18332801) B18332801
theorem B8147911 : Blo 2145435 8147911 := bstep (se 1 (by rfl) ⟨6110933, by rfl⟩ : syracuseStep 8147911 = 12221867) B12221867
theorem B10863881 : Blo 2145435 10863881 := bstep (se 2 (by rfl) ⟨4073955, by rfl⟩ : syracuseStep 10863881 = 8147911) B8147911
theorem B7242587 : Blo 2145435 7242587 := bstep (se 1 (by rfl) ⟨5431940, by rfl⟩ : syracuseStep 7242587 = 10863881) B10863881
theorem B4828391 : Blo 2145435 4828391 := bstep (se 1 (by rfl) ⟨3621293, by rfl⟩ : syracuseStep 4828391 = 7242587) B7242587
theorem B3218927 : Blo 2145435 3218927 := bstep (se 1 (by rfl) ⟨2414195, by rfl⟩ : syracuseStep 3218927 = 4828391) B4828391
theorem B2145951 : Blo 2145435 2145951 := bstep (se 1 (by rfl) ⟨1609463, by rfl⟩ : syracuseStep 2145951 = 3218927) B3218927
theorem B3218933 : Blo 2145435 3218933 := bbase (se 5 (by rfl) ⟨150887, by rfl⟩ : syracuseStep 3218933 = 301775) (by norm_num)
theorem B2145955 : Blo 2145435 2145955 := bstep (se 1 (by rfl) ⟨1609466, by rfl⟩ : syracuseStep 2145955 = 3218933) B3218933
theorem B2291609 : Blo 2145435 2291609 := bbase (se 2 (by rfl) ⟨859353, by rfl⟩ : syracuseStep 2291609 = 1718707) (by norm_num)
theorem B6110957 : Blo 2145435 6110957 := bstep (se 3 (by rfl) ⟨1145804, by rfl⟩ : syracuseStep 6110957 = 2291609) B2291609
theorem B4073971 : Blo 2145435 4073971 := bstep (se 1 (by rfl) ⟨3055478, by rfl⟩ : syracuseStep 4073971 = 6110957) B6110957
theorem B5431961 : Blo 2145435 5431961 := bstep (se 2 (by rfl) ⟨2036985, by rfl⟩ : syracuseStep 5431961 = 4073971) B4073971
theorem B3621307 : Blo 2145435 3621307 := bstep (se 1 (by rfl) ⟨2715980, by rfl⟩ : syracuseStep 3621307 = 5431961) B5431961
theorem B4828409 : Blo 2145435 4828409 := bstep (se 2 (by rfl) ⟨1810653, by rfl⟩ : syracuseStep 4828409 = 3621307) B3621307
theorem B3218939 : Blo 2145435 3218939 := bstep (se 1 (by rfl) ⟨2414204, by rfl⟩ : syracuseStep 3218939 = 4828409) B4828409
theorem B2145959 : Blo 2145435 2145959 := bstep (se 1 (by rfl) ⟨1609469, by rfl⟩ : syracuseStep 2145959 = 3218939) B3218939
theorem B2414209 : Blo 2145435 2414209 := bbase (se 2 (by rfl) ⟨905328, by rfl⟩ : syracuseStep 2414209 = 1810657) (by norm_num)
theorem B3218945 : Blo 2145435 3218945 := bstep (se 2 (by rfl) ⟨1207104, by rfl⟩ : syracuseStep 3218945 = 2414209) B2414209
theorem B2145963 : Blo 2145435 2145963 := bstep (se 1 (by rfl) ⟨1609472, by rfl⟩ : syracuseStep 2145963 = 3218945) B3218945
theorem B5431981 : Blo 2145435 5431981 := bbase (se 3 (by rfl) ⟨1018496, by rfl⟩ : syracuseStep 5431981 = 2036993) (by norm_num)
theorem B7242641 : Blo 2145435 7242641 := bstep (se 2 (by rfl) ⟨2715990, by rfl⟩ : syracuseStep 7242641 = 5431981) B5431981
theorem B4828427 : Blo 2145435 4828427 := bstep (se 1 (by rfl) ⟨3621320, by rfl⟩ : syracuseStep 4828427 = 7242641) B7242641
theorem B3218951 : Blo 2145435 3218951 := bstep (se 1 (by rfl) ⟨2414213, by rfl⟩ : syracuseStep 3218951 = 4828427) B4828427
theorem B2145967 : Blo 2145435 2145967 := bstep (se 1 (by rfl) ⟨1609475, by rfl⟩ : syracuseStep 2145967 = 3218951) B3218951
theorem B3218957 : Blo 2145435 3218957 := bbase (se 3 (by rfl) ⟨603554, by rfl⟩ : syracuseStep 3218957 = 1207109) (by norm_num)
theorem B2145971 : Blo 2145435 2145971 := bstep (se 1 (by rfl) ⟨1609478, by rfl⟩ : syracuseStep 2145971 = 3218957) B3218957
theorem B4828445 : Blo 2145435 4828445 := bbase (se 3 (by rfl) ⟨905333, by rfl⟩ : syracuseStep 4828445 = 1810667) (by norm_num)
theorem B3218963 : Blo 2145435 3218963 := bstep (se 1 (by rfl) ⟨2414222, by rfl⟩ : syracuseStep 3218963 = 4828445) B4828445
theorem B2145975 : Blo 2145435 2145975 := bstep (se 1 (by rfl) ⟨1609481, by rfl⟩ : syracuseStep 2145975 = 3218963) B3218963
theorem B3621341 : Blo 2145435 3621341 := bbase (se 3 (by rfl) ⟨679001, by rfl⟩ : syracuseStep 3621341 = 1358003) (by norm_num)
theorem B2414227 : Blo 2145435 2414227 := bstep (se 1 (by rfl) ⟨1810670, by rfl⟩ : syracuseStep 2414227 = 3621341) B3621341
theorem B3218969 : Blo 2145435 3218969 := bstep (se 2 (by rfl) ⟨1207113, by rfl⟩ : syracuseStep 3218969 = 2414227) B2414227
theorem B2145979 : Blo 2145435 2145979 := bstep (se 1 (by rfl) ⟨1609484, by rfl⟩ : syracuseStep 2145979 = 3218969) B3218969
theorem B15468533 : Blo 2145435 15468533 := bbase (se 5 (by rfl) ⟨725087, by rfl⟩ : syracuseStep 15468533 = 1450175) (by norm_num)
theorem B10312355 : Blo 2145435 10312355 := bstep (se 1 (by rfl) ⟨7734266, by rfl⟩ : syracuseStep 10312355 = 15468533) B15468533
theorem B6874903 : Blo 2145435 6874903 := bstep (se 1 (by rfl) ⟨5156177, by rfl⟩ : syracuseStep 6874903 = 10312355) B10312355
theorem B9166537 : Blo 2145435 9166537 := bstep (se 2 (by rfl) ⟨3437451, by rfl⟩ : syracuseStep 9166537 = 6874903) B6874903
theorem B12222049 : Blo 2145435 12222049 := bstep (se 2 (by rfl) ⟨4583268, by rfl⟩ : syracuseStep 12222049 = 9166537) B9166537
theorem B16296065 : Blo 2145435 16296065 := bstep (se 2 (by rfl) ⟨6111024, by rfl⟩ : syracuseStep 16296065 = 12222049) B12222049
theorem B10864043 : Blo 2145435 10864043 := bstep (se 1 (by rfl) ⟨8148032, by rfl⟩ : syracuseStep 10864043 = 16296065) B16296065
theorem B7242695 : Blo 2145435 7242695 := bstep (se 1 (by rfl) ⟨5432021, by rfl⟩ : syracuseStep 7242695 = 10864043) B10864043
theorem B4828463 : Blo 2145435 4828463 := bstep (se 1 (by rfl) ⟨3621347, by rfl⟩ : syracuseStep 4828463 = 7242695) B7242695
theorem B3218975 : Blo 2145435 3218975 := bstep (se 1 (by rfl) ⟨2414231, by rfl⟩ : syracuseStep 3218975 = 4828463) B4828463
theorem B2145983 : Blo 2145435 2145983 := bstep (se 1 (by rfl) ⟨1609487, by rfl⟩ : syracuseStep 2145983 = 3218975) B3218975
theorem B3218981 : Blo 2145435 3218981 := bbase (se 4 (by rfl) ⟨301779, by rfl⟩ : syracuseStep 3218981 = 603559) (by norm_num)
theorem B2145987 : Blo 2145435 2145987 := bstep (se 1 (by rfl) ⟨1609490, by rfl⟩ : syracuseStep 2145987 = 3218981) B3218981
theorem B2716021 : Blo 2145435 2716021 := bbase (se 5 (by rfl) ⟨127313, by rfl⟩ : syracuseStep 2716021 = 254627) (by norm_num)
theorem B3621361 : Blo 2145435 3621361 := bstep (se 2 (by rfl) ⟨1358010, by rfl⟩ : syracuseStep 3621361 = 2716021) B2716021
theorem B4828481 : Blo 2145435 4828481 := bstep (se 2 (by rfl) ⟨1810680, by rfl⟩ : syracuseStep 4828481 = 3621361) B3621361
theorem B3218987 : Blo 2145435 3218987 := bstep (se 1 (by rfl) ⟨2414240, by rfl⟩ : syracuseStep 3218987 = 4828481) B4828481
theorem B2145991 : Blo 2145435 2145991 := bstep (se 1 (by rfl) ⟨1609493, by rfl⟩ : syracuseStep 2145991 = 3218987) B3218987
theorem B2414245 : Blo 2145435 2414245 := bbase (se 4 (by rfl) ⟨226335, by rfl⟩ : syracuseStep 2414245 = 452671) (by norm_num)
theorem B3218993 : Blo 2145435 3218993 := bstep (se 2 (by rfl) ⟨1207122, by rfl⟩ : syracuseStep 3218993 = 2414245) B2414245
theorem B2145995 : Blo 2145435 2145995 := bstep (se 1 (by rfl) ⟨1609496, by rfl⟩ : syracuseStep 2145995 = 3218993) B3218993
theorem B30937301 : Blo 2145435 30937301 := bbase (se 7 (by rfl) ⟨362546, by rfl⟩ : syracuseStep 30937301 = 725093) (by norm_num)
theorem B20624867 : Blo 2145435 20624867 := bstep (se 1 (by rfl) ⟨15468650, by rfl⟩ : syracuseStep 20624867 = 30937301) B30937301
theorem B13749911 : Blo 2145435 13749911 := bstep (se 1 (by rfl) ⟨10312433, by rfl⟩ : syracuseStep 13749911 = 20624867) B20624867
theorem B9166607 : Blo 2145435 9166607 := bstep (se 1 (by rfl) ⟨6874955, by rfl⟩ : syracuseStep 9166607 = 13749911) B13749911
theorem B6111071 : Blo 2145435 6111071 := bstep (se 1 (by rfl) ⟨4583303, by rfl⟩ : syracuseStep 6111071 = 9166607) B9166607
theorem B4074047 : Blo 2145435 4074047 := bstep (se 1 (by rfl) ⟨3055535, by rfl⟩ : syracuseStep 4074047 = 6111071) B6111071
theorem B2716031 : Blo 2145435 2716031 := bstep (se 1 (by rfl) ⟨2037023, by rfl⟩ : syracuseStep 2716031 = 4074047) B4074047
theorem B7242749 : Blo 2145435 7242749 := bstep (se 3 (by rfl) ⟨1358015, by rfl⟩ : syracuseStep 7242749 = 2716031) B2716031
theorem B4828499 : Blo 2145435 4828499 := bstep (se 1 (by rfl) ⟨3621374, by rfl⟩ : syracuseStep 4828499 = 7242749) B7242749
theorem B3218999 : Blo 2145435 3218999 := bstep (se 1 (by rfl) ⟨2414249, by rfl⟩ : syracuseStep 3218999 = 4828499) B4828499
theorem B2145999 : Blo 2145435 2145999 := bstep (se 1 (by rfl) ⟨1609499, by rfl⟩ : syracuseStep 2145999 = 3218999) B3218999
theorem B3219005 : Blo 2145435 3219005 := bbase (se 3 (by rfl) ⟨603563, by rfl⟩ : syracuseStep 3219005 = 1207127) (by norm_num)
theorem B2146003 : Blo 2145435 2146003 := bstep (se 1 (by rfl) ⟨1609502, by rfl⟩ : syracuseStep 2146003 = 3219005) B3219005
theorem B4828517 : Blo 2145435 4828517 := bbase (se 4 (by rfl) ⟨452673, by rfl⟩ : syracuseStep 4828517 = 905347) (by norm_num)
theorem B3219011 : Blo 2145435 3219011 := bstep (se 1 (by rfl) ⟨2414258, by rfl⟩ : syracuseStep 3219011 = 4828517) B4828517
theorem B2146007 : Blo 2145435 2146007 := bstep (se 1 (by rfl) ⟨1609505, by rfl⟩ : syracuseStep 2146007 = 3219011) B3219011
theorem B5432093 : Blo 2145435 5432093 := bbase (se 3 (by rfl) ⟨1018517, by rfl⟩ : syracuseStep 5432093 = 2037035) (by norm_num)
theorem B3621395 : Blo 2145435 3621395 := bstep (se 1 (by rfl) ⟨2716046, by rfl⟩ : syracuseStep 3621395 = 5432093) B5432093
theorem B2414263 : Blo 2145435 2414263 := bstep (se 1 (by rfl) ⟨1810697, by rfl⟩ : syracuseStep 2414263 = 3621395) B3621395
theorem B3219017 : Blo 2145435 3219017 := bstep (se 2 (by rfl) ⟨1207131, by rfl⟩ : syracuseStep 3219017 = 2414263) B2414263
theorem B2146011 : Blo 2145435 2146011 := bstep (se 1 (by rfl) ⟨1609508, by rfl⟩ : syracuseStep 2146011 = 3219017) B3219017
theorem B4074077 : Blo 2145435 4074077 := bbase (se 3 (by rfl) ⟨763889, by rfl⟩ : syracuseStep 4074077 = 1527779) (by norm_num)
theorem B10864205 : Blo 2145435 10864205 := bstep (se 3 (by rfl) ⟨2037038, by rfl⟩ : syracuseStep 10864205 = 4074077) B4074077
theorem B7242803 : Blo 2145435 7242803 := bstep (se 1 (by rfl) ⟨5432102, by rfl⟩ : syracuseStep 7242803 = 10864205) B10864205
theorem B4828535 : Blo 2145435 4828535 := bstep (se 1 (by rfl) ⟨3621401, by rfl⟩ : syracuseStep 4828535 = 7242803) B7242803
theorem B3219023 : Blo 2145435 3219023 := bstep (se 1 (by rfl) ⟨2414267, by rfl⟩ : syracuseStep 3219023 = 4828535) B4828535
theorem B2146015 : Blo 2145435 2146015 := bstep (se 1 (by rfl) ⟨1609511, by rfl⟩ : syracuseStep 2146015 = 3219023) B3219023
theorem B3219029 : Blo 2145435 3219029 := bbase (se 8 (by rfl) ⟨18861, by rfl⟩ : syracuseStep 3219029 = 37723) (by norm_num)
theorem B2146019 : Blo 2145435 2146019 := bstep (se 1 (by rfl) ⟨1609514, by rfl⟩ : syracuseStep 2146019 = 3219029) B3219029
theorem B9166709 : Blo 2145435 9166709 := bbase (se 5 (by rfl) ⟨429689, by rfl⟩ : syracuseStep 9166709 = 859379) (by norm_num)
theorem B6111139 : Blo 2145435 6111139 := bstep (se 1 (by rfl) ⟨4583354, by rfl⟩ : syracuseStep 6111139 = 9166709) B9166709
theorem B8148185 : Blo 2145435 8148185 := bstep (se 2 (by rfl) ⟨3055569, by rfl⟩ : syracuseStep 8148185 = 6111139) B6111139
theorem B5432123 : Blo 2145435 5432123 := bstep (se 1 (by rfl) ⟨4074092, by rfl⟩ : syracuseStep 5432123 = 8148185) B8148185
theorem B3621415 : Blo 2145435 3621415 := bstep (se 1 (by rfl) ⟨2716061, by rfl⟩ : syracuseStep 3621415 = 5432123) B5432123
theorem B4828553 : Blo 2145435 4828553 := bstep (se 2 (by rfl) ⟨1810707, by rfl⟩ : syracuseStep 4828553 = 3621415) B3621415
theorem B3219035 : Blo 2145435 3219035 := bstep (se 1 (by rfl) ⟨2414276, by rfl⟩ : syracuseStep 3219035 = 4828553) B4828553
theorem B2146023 : Blo 2145435 2146023 := bstep (se 1 (by rfl) ⟨1609517, by rfl⟩ : syracuseStep 2146023 = 3219035) B3219035
theorem B2414281 : Blo 2145435 2414281 := bbase (se 2 (by rfl) ⟨905355, by rfl⟩ : syracuseStep 2414281 = 1810711) (by norm_num)
theorem B3219041 : Blo 2145435 3219041 := bstep (se 2 (by rfl) ⟨1207140, by rfl⟩ : syracuseStep 3219041 = 2414281) B2414281
theorem B2146027 : Blo 2145435 2146027 := bstep (se 1 (by rfl) ⟨1609520, by rfl⟩ : syracuseStep 2146027 = 3219041) B3219041
theorem B5156293 : Blo 2145435 5156293 := bbase (se 4 (by rfl) ⟨483402, by rfl⟩ : syracuseStep 5156293 = 966805) (by norm_num)
theorem B6875057 : Blo 2145435 6875057 := bstep (se 2 (by rfl) ⟨2578146, by rfl⟩ : syracuseStep 6875057 = 5156293) B5156293
theorem B18333485 : Blo 2145435 18333485 := bstep (se 3 (by rfl) ⟨3437528, by rfl⟩ : syracuseStep 18333485 = 6875057) B6875057
theorem B12222323 : Blo 2145435 12222323 := bstep (se 1 (by rfl) ⟨9166742, by rfl⟩ : syracuseStep 12222323 = 18333485) B18333485
theorem B8148215 : Blo 2145435 8148215 := bstep (se 1 (by rfl) ⟨6111161, by rfl⟩ : syracuseStep 8148215 = 12222323) B12222323
theorem B5432143 : Blo 2145435 5432143 := bstep (se 1 (by rfl) ⟨4074107, by rfl⟩ : syracuseStep 5432143 = 8148215) B8148215
theorem B7242857 : Blo 2145435 7242857 := bstep (se 2 (by rfl) ⟨2716071, by rfl⟩ : syracuseStep 7242857 = 5432143) B5432143
theorem B4828571 : Blo 2145435 4828571 := bstep (se 1 (by rfl) ⟨3621428, by rfl⟩ : syracuseStep 4828571 = 7242857) B7242857
theorem B3219047 : Blo 2145435 3219047 := bstep (se 1 (by rfl) ⟨2414285, by rfl⟩ : syracuseStep 3219047 = 4828571) B4828571
theorem B2146031 : Blo 2145435 2146031 := bstep (se 1 (by rfl) ⟨1609523, by rfl⟩ : syracuseStep 2146031 = 3219047) B3219047
theorem B3219053 : Blo 2145435 3219053 := bbase (se 3 (by rfl) ⟨603572, by rfl⟩ : syracuseStep 3219053 = 1207145) (by norm_num)
theorem B2146035 : Blo 2145435 2146035 := bstep (se 1 (by rfl) ⟨1609526, by rfl⟩ : syracuseStep 2146035 = 3219053) B3219053
theorem B4828589 : Blo 2145435 4828589 := bbase (se 3 (by rfl) ⟨905360, by rfl⟩ : syracuseStep 4828589 = 1810721) (by norm_num)
theorem B3219059 : Blo 2145435 3219059 := bstep (se 1 (by rfl) ⟨2414294, by rfl⟩ : syracuseStep 3219059 = 4828589) B4828589
theorem B2146039 : Blo 2145435 2146039 := bstep (se 1 (by rfl) ⟨1609529, by rfl⟩ : syracuseStep 2146039 = 3219059) B3219059
theorem B3437549 : Blo 2145435 3437549 := bbase (se 3 (by rfl) ⟨644540, by rfl⟩ : syracuseStep 3437549 = 1289081) (by norm_num)
theorem B2291699 : Blo 2145435 2291699 := bstep (se 1 (by rfl) ⟨1718774, by rfl⟩ : syracuseStep 2291699 = 3437549) B3437549
theorem B6111197 : Blo 2145435 6111197 := bstep (se 3 (by rfl) ⟨1145849, by rfl⟩ : syracuseStep 6111197 = 2291699) B2291699
theorem B4074131 : Blo 2145435 4074131 := bstep (se 1 (by rfl) ⟨3055598, by rfl⟩ : syracuseStep 4074131 = 6111197) B6111197
theorem B2716087 : Blo 2145435 2716087 := bstep (se 1 (by rfl) ⟨2037065, by rfl⟩ : syracuseStep 2716087 = 4074131) B4074131
theorem B3621449 : Blo 2145435 3621449 := bstep (se 2 (by rfl) ⟨1358043, by rfl⟩ : syracuseStep 3621449 = 2716087) B2716087
theorem B2414299 : Blo 2145435 2414299 := bstep (se 1 (by rfl) ⟨1810724, by rfl⟩ : syracuseStep 2414299 = 3621449) B3621449
theorem B3219065 : Blo 2145435 3219065 := bstep (se 2 (by rfl) ⟨1207149, by rfl⟩ : syracuseStep 3219065 = 2414299) B2414299
theorem B2146043 : Blo 2145435 2146043 := bstep (se 1 (by rfl) ⟨1609532, by rfl⟩ : syracuseStep 2146043 = 3219065) B3219065
theorem B2613341 : Blo 2145435 2613341 := bbase (se 3 (by rfl) ⟨490001, by rfl⟩ : syracuseStep 2613341 = 980003) (by norm_num)
theorem B6968909 : Blo 2145435 6968909 := bstep (se 3 (by rfl) ⟨1306670, by rfl⟩ : syracuseStep 6968909 = 2613341) B2613341
theorem B4645939 : Blo 2145435 4645939 := bstep (se 1 (by rfl) ⟨3484454, by rfl⟩ : syracuseStep 4645939 = 6968909) B6968909
theorem B6194585 : Blo 2145435 6194585 := bstep (se 2 (by rfl) ⟨2322969, by rfl⟩ : syracuseStep 6194585 = 4645939) B4645939
theorem B4129723 : Blo 2145435 4129723 := bstep (se 1 (by rfl) ⟨3097292, by rfl⟩ : syracuseStep 4129723 = 6194585) B6194585
theorem B22025189 : Blo 2145435 22025189 := bstep (se 4 (by rfl) ⟨2064861, by rfl⟩ : syracuseStep 22025189 = 4129723) B4129723
theorem B14683459 : Blo 2145435 14683459 := bstep (se 1 (by rfl) ⟨11012594, by rfl⟩ : syracuseStep 14683459 = 22025189) B22025189
theorem B19577945 : Blo 2145435 19577945 := bstep (se 2 (by rfl) ⟨7341729, by rfl⟩ : syracuseStep 19577945 = 14683459) B14683459
theorem B13051963 : Blo 2145435 13051963 := bstep (se 1 (by rfl) ⟨9788972, by rfl⟩ : syracuseStep 13051963 = 19577945) B19577945
theorem B17402617 : Blo 2145435 17402617 := bstep (se 2 (by rfl) ⟨6525981, by rfl⟩ : syracuseStep 17402617 = 13051963) B13051963
theorem B92813957 : Blo 2145435 92813957 := bstep (se 4 (by rfl) ⟨8701308, by rfl⟩ : syracuseStep 92813957 = 17402617) B17402617
theorem B61875971 : Blo 2145435 61875971 := bstep (se 1 (by rfl) ⟨46406978, by rfl⟩ : syracuseStep 61875971 = 92813957) B92813957
theorem B41250647 : Blo 2145435 41250647 := bstep (se 1 (by rfl) ⟨30937985, by rfl⟩ : syracuseStep 41250647 = 61875971) B61875971
theorem B27500431 : Blo 2145435 27500431 := bstep (se 1 (by rfl) ⟨20625323, by rfl⟩ : syracuseStep 27500431 = 41250647) B41250647
theorem B36667241 : Blo 2145435 36667241 := bstep (se 2 (by rfl) ⟨13750215, by rfl⟩ : syracuseStep 36667241 = 27500431) B27500431
theorem B24444827 : Blo 2145435 24444827 := bstep (se 1 (by rfl) ⟨18333620, by rfl⟩ : syracuseStep 24444827 = 36667241) B36667241
theorem B16296551 : Blo 2145435 16296551 := bstep (se 1 (by rfl) ⟨12222413, by rfl⟩ : syracuseStep 16296551 = 24444827) B24444827
theorem B10864367 : Blo 2145435 10864367 := bstep (se 1 (by rfl) ⟨8148275, by rfl⟩ : syracuseStep 10864367 = 16296551) B16296551
theorem B7242911 : Blo 2145435 7242911 := bstep (se 1 (by rfl) ⟨5432183, by rfl⟩ : syracuseStep 7242911 = 10864367) B10864367
theorem B4828607 : Blo 2145435 4828607 := bstep (se 1 (by rfl) ⟨3621455, by rfl⟩ : syracuseStep 4828607 = 7242911) B7242911
theorem B3219071 : Blo 2145435 3219071 := bstep (se 1 (by rfl) ⟨2414303, by rfl⟩ : syracuseStep 3219071 = 4828607) B4828607
theorem B2146047 : Blo 2145435 2146047 := bstep (se 1 (by rfl) ⟨1609535, by rfl⟩ : syracuseStep 2146047 = 3219071) B3219071
theorem B3219077 : Blo 2145435 3219077 := bbase (se 4 (by rfl) ⟨301788, by rfl⟩ : syracuseStep 3219077 = 603577) (by norm_num)
theorem B2146051 : Blo 2145435 2146051 := bstep (se 1 (by rfl) ⟨1609538, by rfl⟩ : syracuseStep 2146051 = 3219077) B3219077
theorem B3621469 : Blo 2145435 3621469 := bbase (se 3 (by rfl) ⟨679025, by rfl⟩ : syracuseStep 3621469 = 1358051) (by norm_num)
theorem B4828625 : Blo 2145435 4828625 := bstep (se 2 (by rfl) ⟨1810734, by rfl⟩ : syracuseStep 4828625 = 3621469) B3621469
theorem B3219083 : Blo 2145435 3219083 := bstep (se 1 (by rfl) ⟨2414312, by rfl⟩ : syracuseStep 3219083 = 4828625) B4828625
theorem B2146055 : Blo 2145435 2146055 := bstep (se 1 (by rfl) ⟨1609541, by rfl⟩ : syracuseStep 2146055 = 3219083) B3219083
theorem B2414317 : Blo 2145435 2414317 := bbase (se 3 (by rfl) ⟨452684, by rfl⟩ : syracuseStep 2414317 = 905369) (by norm_num)
theorem B3219089 : Blo 2145435 3219089 := bstep (se 2 (by rfl) ⟨1207158, by rfl⟩ : syracuseStep 3219089 = 2414317) B2414317
theorem B2146059 : Blo 2145435 2146059 := bstep (se 1 (by rfl) ⟨1609544, by rfl⟩ : syracuseStep 2146059 = 3219089) B3219089
theorem B7242965 : Blo 2145435 7242965 := bbase (se 7 (by rfl) ⟨84878, by rfl⟩ : syracuseStep 7242965 = 169757) (by norm_num)
theorem B4828643 : Blo 2145435 4828643 := bstep (se 1 (by rfl) ⟨3621482, by rfl⟩ : syracuseStep 4828643 = 7242965) B7242965
theorem B3219095 : Blo 2145435 3219095 := bstep (se 1 (by rfl) ⟨2414321, by rfl⟩ : syracuseStep 3219095 = 4828643) B4828643
theorem B2146063 : Blo 2145435 2146063 := bstep (se 1 (by rfl) ⟨1609547, by rfl⟩ : syracuseStep 2146063 = 3219095) B3219095
theorem B3219101 : Blo 2145435 3219101 := bbase (se 3 (by rfl) ⟨603581, by rfl⟩ : syracuseStep 3219101 = 1207163) (by norm_num)
theorem B2146067 : Blo 2145435 2146067 := bstep (se 1 (by rfl) ⟨1609550, by rfl⟩ : syracuseStep 2146067 = 3219101) B3219101
theorem B4828661 : Blo 2145435 4828661 := bbase (se 5 (by rfl) ⟨226343, by rfl⟩ : syracuseStep 4828661 = 452687) (by norm_num)
theorem B3219107 : Blo 2145435 3219107 := bstep (se 1 (by rfl) ⟨2414330, by rfl⟩ : syracuseStep 3219107 = 4828661) B4828661
theorem B2146071 : Blo 2145435 2146071 := bstep (se 1 (by rfl) ⟨1609553, by rfl⟩ : syracuseStep 2146071 = 3219107) B3219107
theorem B2480665 : Blo 2145435 2480665 := bbase (se 2 (by rfl) ⟨930249, by rfl⟩ : syracuseStep 2480665 = 1860499) (by norm_num)
theorem B3307553 : Blo 2145435 3307553 := bstep (se 2 (by rfl) ⟨1240332, by rfl⟩ : syracuseStep 3307553 = 2480665) B2480665
theorem B2205035 : Blo 2145435 2205035 := bstep (se 1 (by rfl) ⟨1653776, by rfl⟩ : syracuseStep 2205035 = 3307553) B3307553
theorem B94081493 : Blo 2145435 94081493 := bstep (se 7 (by rfl) ⟨1102517, by rfl⟩ : syracuseStep 94081493 = 2205035) B2205035
theorem B62720995 : Blo 2145435 62720995 := bstep (se 1 (by rfl) ⟨47040746, by rfl⟩ : syracuseStep 62720995 = 94081493) B94081493
theorem B83627993 : Blo 2145435 83627993 := bstep (se 2 (by rfl) ⟨31360497, by rfl⟩ : syracuseStep 83627993 = 62720995) B62720995
theorem B55751995 : Blo 2145435 55751995 := bstep (se 1 (by rfl) ⟨41813996, by rfl⟩ : syracuseStep 55751995 = 83627993) B83627993
theorem B297343973 : Blo 2145435 297343973 := bstep (se 4 (by rfl) ⟨27875997, by rfl⟩ : syracuseStep 297343973 = 55751995) B55751995
theorem B198229315 : Blo 2145435 198229315 := bstep (se 1 (by rfl) ⟨148671986, by rfl⟩ : syracuseStep 198229315 = 297343973) B297343973
theorem B264305753 : Blo 2145435 264305753 := bstep (se 2 (by rfl) ⟨99114657, by rfl⟩ : syracuseStep 264305753 = 198229315) B198229315
theorem B176203835 : Blo 2145435 176203835 := bstep (se 1 (by rfl) ⟨132152876, by rfl⟩ : syracuseStep 176203835 = 264305753) B264305753
theorem B117469223 : Blo 2145435 117469223 := bstep (se 1 (by rfl) ⟨88101917, by rfl⟩ : syracuseStep 117469223 = 176203835) B176203835
theorem B78312815 : Blo 2145435 78312815 := bstep (se 1 (by rfl) ⟨58734611, by rfl⟩ : syracuseStep 78312815 = 117469223) B117469223
theorem B52208543 : Blo 2145435 52208543 := bstep (se 1 (by rfl) ⟨39156407, by rfl⟩ : syracuseStep 52208543 = 78312815) B78312815
theorem B34805695 : Blo 2145435 34805695 := bstep (se 1 (by rfl) ⟨26104271, by rfl⟩ : syracuseStep 34805695 = 52208543) B52208543
theorem B46407593 : Blo 2145435 46407593 := bstep (se 2 (by rfl) ⟨17402847, by rfl⟩ : syracuseStep 46407593 = 34805695) B34805695
theorem B30938395 : Blo 2145435 30938395 := bstep (se 1 (by rfl) ⟨23203796, by rfl⟩ : syracuseStep 30938395 = 46407593) B46407593
theorem B41251193 : Blo 2145435 41251193 := bstep (se 2 (by rfl) ⟨15469197, by rfl⟩ : syracuseStep 41251193 = 30938395) B30938395
theorem B27500795 : Blo 2145435 27500795 := bstep (se 1 (by rfl) ⟨20625596, by rfl⟩ : syracuseStep 27500795 = 41251193) B41251193
theorem B18333863 : Blo 2145435 18333863 := bstep (se 1 (by rfl) ⟨13750397, by rfl⟩ : syracuseStep 18333863 = 27500795) B27500795
theorem B12222575 : Blo 2145435 12222575 := bstep (se 1 (by rfl) ⟨9166931, by rfl⟩ : syracuseStep 12222575 = 18333863) B18333863
theorem B8148383 : Blo 2145435 8148383 := bstep (se 1 (by rfl) ⟨6111287, by rfl⟩ : syracuseStep 8148383 = 12222575) B12222575
theorem B5432255 : Blo 2145435 5432255 := bstep (se 1 (by rfl) ⟨4074191, by rfl⟩ : syracuseStep 5432255 = 8148383) B8148383
theorem B3621503 : Blo 2145435 3621503 := bstep (se 1 (by rfl) ⟨2716127, by rfl⟩ : syracuseStep 3621503 = 5432255) B5432255
theorem B2414335 : Blo 2145435 2414335 := bstep (se 1 (by rfl) ⟨1810751, by rfl⟩ : syracuseStep 2414335 = 3621503) B3621503
theorem B3219113 : Blo 2145435 3219113 := bstep (se 2 (by rfl) ⟨1207167, by rfl⟩ : syracuseStep 3219113 = 2414335) B2414335
theorem B2146075 : Blo 2145435 2146075 := bstep (se 1 (by rfl) ⟨1609556, by rfl⟩ : syracuseStep 2146075 = 3219113) B3219113
theorem B2291737 : Blo 2145435 2291737 := bbase (se 2 (by rfl) ⟨859401, by rfl⟩ : syracuseStep 2291737 = 1718803) (by norm_num)
theorem B3055649 : Blo 2145435 3055649 := bstep (se 2 (by rfl) ⟨1145868, by rfl⟩ : syracuseStep 3055649 = 2291737) B2291737
theorem B8148397 : Blo 2145435 8148397 := bstep (se 3 (by rfl) ⟨1527824, by rfl⟩ : syracuseStep 8148397 = 3055649) B3055649
theorem B10864529 : Blo 2145435 10864529 := bstep (se 2 (by rfl) ⟨4074198, by rfl⟩ : syracuseStep 10864529 = 8148397) B8148397
theorem B7243019 : Blo 2145435 7243019 := bstep (se 1 (by rfl) ⟨5432264, by rfl⟩ : syracuseStep 7243019 = 10864529) B10864529
theorem B4828679 : Blo 2145435 4828679 := bstep (se 1 (by rfl) ⟨3621509, by rfl⟩ : syracuseStep 4828679 = 7243019) B7243019
theorem B3219119 : Blo 2145435 3219119 := bstep (se 1 (by rfl) ⟨2414339, by rfl⟩ : syracuseStep 3219119 = 4828679) B4828679
theorem B2146079 : Blo 2145435 2146079 := bstep (se 1 (by rfl) ⟨1609559, by rfl⟩ : syracuseStep 2146079 = 3219119) B3219119
theorem B3219125 : Blo 2145435 3219125 := bbase (se 5 (by rfl) ⟨150896, by rfl⟩ : syracuseStep 3219125 = 301793) (by norm_num)
theorem B2146083 : Blo 2145435 2146083 := bstep (se 1 (by rfl) ⟨1609562, by rfl⟩ : syracuseStep 2146083 = 3219125) B3219125
theorem B5432285 : Blo 2145435 5432285 := bbase (se 3 (by rfl) ⟨1018553, by rfl⟩ : syracuseStep 5432285 = 2037107) (by norm_num)
theorem B3621523 : Blo 2145435 3621523 := bstep (se 1 (by rfl) ⟨2716142, by rfl⟩ : syracuseStep 3621523 = 5432285) B5432285
theorem B4828697 : Blo 2145435 4828697 := bstep (se 2 (by rfl) ⟨1810761, by rfl⟩ : syracuseStep 4828697 = 3621523) B3621523
theorem B3219131 : Blo 2145435 3219131 := bstep (se 1 (by rfl) ⟨2414348, by rfl⟩ : syracuseStep 3219131 = 4828697) B4828697
theorem B2146087 : Blo 2145435 2146087 := bstep (se 1 (by rfl) ⟨1609565, by rfl⟩ : syracuseStep 2146087 = 3219131) B3219131
theorem B2414353 : Blo 2145435 2414353 := bbase (se 2 (by rfl) ⟨905382, by rfl⟩ : syracuseStep 2414353 = 1810765) (by norm_num)
theorem B3219137 : Blo 2145435 3219137 := bstep (se 2 (by rfl) ⟨1207176, by rfl⟩ : syracuseStep 3219137 = 2414353) B2414353
theorem B2146091 : Blo 2145435 2146091 := bstep (se 1 (by rfl) ⟨1609568, by rfl⟩ : syracuseStep 2146091 = 3219137) B3219137
theorem B4074229 : Blo 2145435 4074229 := bbase (se 5 (by rfl) ⟨190979, by rfl⟩ : syracuseStep 4074229 = 381959) (by norm_num)
theorem B5432305 : Blo 2145435 5432305 := bstep (se 2 (by rfl) ⟨2037114, by rfl⟩ : syracuseStep 5432305 = 4074229) B4074229
theorem B7243073 : Blo 2145435 7243073 := bstep (se 2 (by rfl) ⟨2716152, by rfl⟩ : syracuseStep 7243073 = 5432305) B5432305
theorem B4828715 : Blo 2145435 4828715 := bstep (se 1 (by rfl) ⟨3621536, by rfl⟩ : syracuseStep 4828715 = 7243073) B7243073
theorem B3219143 : Blo 2145435 3219143 := bstep (se 1 (by rfl) ⟨2414357, by rfl⟩ : syracuseStep 3219143 = 4828715) B4828715
theorem B2146095 : Blo 2145435 2146095 := bstep (se 1 (by rfl) ⟨1609571, by rfl⟩ : syracuseStep 2146095 = 3219143) B3219143
theorem B3219149 : Blo 2145435 3219149 := bbase (se 3 (by rfl) ⟨603590, by rfl⟩ : syracuseStep 3219149 = 1207181) (by norm_num)
theorem B2146099 : Blo 2145435 2146099 := bstep (se 1 (by rfl) ⟨1609574, by rfl⟩ : syracuseStep 2146099 = 3219149) B3219149
theorem B4828733 : Blo 2145435 4828733 := bbase (se 3 (by rfl) ⟨905387, by rfl⟩ : syracuseStep 4828733 = 1810775) (by norm_num)
theorem B3219155 : Blo 2145435 3219155 := bstep (se 1 (by rfl) ⟨2414366, by rfl⟩ : syracuseStep 3219155 = 4828733) B4828733
theorem B2146103 : Blo 2145435 2146103 := bstep (se 1 (by rfl) ⟨1609577, by rfl⟩ : syracuseStep 2146103 = 3219155) B3219155
theorem B3621557 : Blo 2145435 3621557 := bbase (se 5 (by rfl) ⟨169760, by rfl⟩ : syracuseStep 3621557 = 339521) (by norm_num)
theorem B2414371 : Blo 2145435 2414371 := bstep (se 1 (by rfl) ⟨1810778, by rfl⟩ : syracuseStep 2414371 = 3621557) B3621557
theorem B3219161 : Blo 2145435 3219161 := bstep (se 2 (by rfl) ⟨1207185, by rfl⟩ : syracuseStep 3219161 = 2414371) B2414371
theorem B2146107 : Blo 2145435 2146107 := bstep (se 1 (by rfl) ⟨1609580, by rfl⟩ : syracuseStep 2146107 = 3219161) B3219161
theorem B3867365 : Blo 2145435 3867365 := bbase (se 4 (by rfl) ⟨362565, by rfl⟩ : syracuseStep 3867365 = 725131) (by norm_num)
theorem B2578243 : Blo 2145435 2578243 := bstep (se 1 (by rfl) ⟨1933682, by rfl⟩ : syracuseStep 2578243 = 3867365) B3867365
theorem B3437657 : Blo 2145435 3437657 := bstep (se 2 (by rfl) ⟨1289121, by rfl⟩ : syracuseStep 3437657 = 2578243) B2578243
theorem B2291771 : Blo 2145435 2291771 := bstep (se 1 (by rfl) ⟨1718828, by rfl⟩ : syracuseStep 2291771 = 3437657) B3437657
theorem B6111389 : Blo 2145435 6111389 := bstep (se 3 (by rfl) ⟨1145885, by rfl⟩ : syracuseStep 6111389 = 2291771) B2291771
theorem B16297037 : Blo 2145435 16297037 := bstep (se 3 (by rfl) ⟨3055694, by rfl⟩ : syracuseStep 16297037 = 6111389) B6111389
theorem B10864691 : Blo 2145435 10864691 := bstep (se 1 (by rfl) ⟨8148518, by rfl⟩ : syracuseStep 10864691 = 16297037) B16297037
theorem B7243127 : Blo 2145435 7243127 := bstep (se 1 (by rfl) ⟨5432345, by rfl⟩ : syracuseStep 7243127 = 10864691) B10864691
theorem B4828751 : Blo 2145435 4828751 := bstep (se 1 (by rfl) ⟨3621563, by rfl⟩ : syracuseStep 4828751 = 7243127) B7243127
theorem B3219167 : Blo 2145435 3219167 := bstep (se 1 (by rfl) ⟨2414375, by rfl⟩ : syracuseStep 3219167 = 4828751) B4828751
theorem B2146111 : Blo 2145435 2146111 := bstep (se 1 (by rfl) ⟨1609583, by rfl⟩ : syracuseStep 2146111 = 3219167) B3219167
theorem B3219173 : Blo 2145435 3219173 := bbase (se 4 (by rfl) ⟨301797, by rfl⟩ : syracuseStep 3219173 = 603595) (by norm_num)
theorem B2146115 : Blo 2145435 2146115 := bstep (se 1 (by rfl) ⟨1609586, by rfl⟩ : syracuseStep 2146115 = 3219173) B3219173
theorem B6111413 : Blo 2145435 6111413 := bbase (se 5 (by rfl) ⟨286472, by rfl⟩ : syracuseStep 6111413 = 572945) (by norm_num)
theorem B4074275 : Blo 2145435 4074275 := bstep (se 1 (by rfl) ⟨3055706, by rfl⟩ : syracuseStep 4074275 = 6111413) B6111413
theorem B2716183 : Blo 2145435 2716183 := bstep (se 1 (by rfl) ⟨2037137, by rfl⟩ : syracuseStep 2716183 = 4074275) B4074275
theorem B3621577 : Blo 2145435 3621577 := bstep (se 2 (by rfl) ⟨1358091, by rfl⟩ : syracuseStep 3621577 = 2716183) B2716183
theorem B4828769 : Blo 2145435 4828769 := bstep (se 2 (by rfl) ⟨1810788, by rfl⟩ : syracuseStep 4828769 = 3621577) B3621577
theorem B3219179 : Blo 2145435 3219179 := bstep (se 1 (by rfl) ⟨2414384, by rfl⟩ : syracuseStep 3219179 = 4828769) B4828769
theorem B2146119 : Blo 2145435 2146119 := bstep (se 1 (by rfl) ⟨1609589, by rfl⟩ : syracuseStep 2146119 = 3219179) B3219179
theorem B2414389 : Blo 2145435 2414389 := bbase (se 5 (by rfl) ⟨113174, by rfl⟩ : syracuseStep 2414389 = 226349) (by norm_num)
theorem B3219185 : Blo 2145435 3219185 := bstep (se 2 (by rfl) ⟨1207194, by rfl⟩ : syracuseStep 3219185 = 2414389) B2414389
theorem B2146123 : Blo 2145435 2146123 := bstep (se 1 (by rfl) ⟨1609592, by rfl⟩ : syracuseStep 2146123 = 3219185) B3219185
theorem B2716193 : Blo 2145435 2716193 := bbase (se 2 (by rfl) ⟨1018572, by rfl⟩ : syracuseStep 2716193 = 2037145) (by norm_num)
theorem B7243181 : Blo 2145435 7243181 := bstep (se 3 (by rfl) ⟨1358096, by rfl⟩ : syracuseStep 7243181 = 2716193) B2716193
theorem B4828787 : Blo 2145435 4828787 := bstep (se 1 (by rfl) ⟨3621590, by rfl⟩ : syracuseStep 4828787 = 7243181) B7243181
theorem B3219191 : Blo 2145435 3219191 := bstep (se 1 (by rfl) ⟨2414393, by rfl⟩ : syracuseStep 3219191 = 4828787) B4828787
theorem B2146127 : Blo 2145435 2146127 := bstep (se 1 (by rfl) ⟨1609595, by rfl⟩ : syracuseStep 2146127 = 3219191) B3219191
theorem B3219197 : Blo 2145435 3219197 := bbase (se 3 (by rfl) ⟨603599, by rfl⟩ : syracuseStep 3219197 = 1207199) (by norm_num)
theorem B2146131 : Blo 2145435 2146131 := bstep (se 1 (by rfl) ⟨1609598, by rfl⟩ : syracuseStep 2146131 = 3219197) B3219197
theorem B4828805 : Blo 2145435 4828805 := bbase (se 4 (by rfl) ⟨452700, by rfl⟩ : syracuseStep 4828805 = 905401) (by norm_num)
theorem B3219203 : Blo 2145435 3219203 := bstep (se 1 (by rfl) ⟨2414402, by rfl⟩ : syracuseStep 3219203 = 4828805) B4828805
theorem B2146135 : Blo 2145435 2146135 := bstep (se 1 (by rfl) ⟨1609601, by rfl⟩ : syracuseStep 2146135 = 3219203) B3219203
theorem B2578277 : Blo 2145435 2578277 := bbase (se 4 (by rfl) ⟨241713, by rfl⟩ : syracuseStep 2578277 = 483427) (by norm_num)
theorem B6875405 : Blo 2145435 6875405 := bstep (se 3 (by rfl) ⟨1289138, by rfl⟩ : syracuseStep 6875405 = 2578277) B2578277
theorem B4583603 : Blo 2145435 4583603 := bstep (se 1 (by rfl) ⟨3437702, by rfl⟩ : syracuseStep 4583603 = 6875405) B6875405
theorem B3055735 : Blo 2145435 3055735 := bstep (se 1 (by rfl) ⟨2291801, by rfl⟩ : syracuseStep 3055735 = 4583603) B4583603
theorem B4074313 : Blo 2145435 4074313 := bstep (se 2 (by rfl) ⟨1527867, by rfl⟩ : syracuseStep 4074313 = 3055735) B3055735
theorem B5432417 : Blo 2145435 5432417 := bstep (se 2 (by rfl) ⟨2037156, by rfl⟩ : syracuseStep 5432417 = 4074313) B4074313
theorem B3621611 : Blo 2145435 3621611 := bstep (se 1 (by rfl) ⟨2716208, by rfl⟩ : syracuseStep 3621611 = 5432417) B5432417
theorem B2414407 : Blo 2145435 2414407 := bstep (se 1 (by rfl) ⟨1810805, by rfl⟩ : syracuseStep 2414407 = 3621611) B3621611
theorem B3219209 : Blo 2145435 3219209 := bstep (se 2 (by rfl) ⟨1207203, by rfl⟩ : syracuseStep 3219209 = 2414407) B2414407
theorem B2146139 : Blo 2145435 2146139 := bstep (se 1 (by rfl) ⟨1609604, by rfl⟩ : syracuseStep 2146139 = 3219209) B3219209
theorem B10864853 : Blo 2145435 10864853 := bbase (se 7 (by rfl) ⟨127322, by rfl⟩ : syracuseStep 10864853 = 254645) (by norm_num)
theorem B7243235 : Blo 2145435 7243235 := bstep (se 1 (by rfl) ⟨5432426, by rfl⟩ : syracuseStep 7243235 = 10864853) B10864853
theorem B4828823 : Blo 2145435 4828823 := bstep (se 1 (by rfl) ⟨3621617, by rfl⟩ : syracuseStep 4828823 = 7243235) B7243235
theorem B3219215 : Blo 2145435 3219215 := bstep (se 1 (by rfl) ⟨2414411, by rfl⟩ : syracuseStep 3219215 = 4828823) B4828823
theorem B2146143 : Blo 2145435 2146143 := bstep (se 1 (by rfl) ⟨1609607, by rfl⟩ : syracuseStep 2146143 = 3219215) B3219215
theorem B3219221 : Blo 2145435 3219221 := bbase (se 6 (by rfl) ⟨75450, by rfl⟩ : syracuseStep 3219221 = 150901) (by norm_num)
theorem B2146147 : Blo 2145435 2146147 := bstep (se 1 (by rfl) ⟨1609610, by rfl⟩ : syracuseStep 2146147 = 3219221) B3219221
theorem B13052597 : Blo 2145435 13052597 := bbase (se 5 (by rfl) ⟨611840, by rfl⟩ : syracuseStep 13052597 = 1223681) (by norm_num)
theorem B34806925 : Blo 2145435 34806925 := bstep (se 3 (by rfl) ⟨6526298, by rfl⟩ : syracuseStep 34806925 = 13052597) B13052597
theorem B46409233 : Blo 2145435 46409233 := bstep (se 2 (by rfl) ⟨17403462, by rfl⟩ : syracuseStep 46409233 = 34806925) B34806925
theorem B61878977 : Blo 2145435 61878977 := bstep (se 2 (by rfl) ⟨23204616, by rfl⟩ : syracuseStep 61878977 = 46409233) B46409233
theorem B41252651 : Blo 2145435 41252651 := bstep (se 1 (by rfl) ⟨30939488, by rfl⟩ : syracuseStep 41252651 = 61878977) B61878977
theorem B27501767 : Blo 2145435 27501767 := bstep (se 1 (by rfl) ⟨20626325, by rfl⟩ : syracuseStep 27501767 = 41252651) B41252651
theorem B18334511 : Blo 2145435 18334511 := bstep (se 1 (by rfl) ⟨13750883, by rfl⟩ : syracuseStep 18334511 = 27501767) B27501767
theorem B12223007 : Blo 2145435 12223007 := bstep (se 1 (by rfl) ⟨9167255, by rfl⟩ : syracuseStep 12223007 = 18334511) B18334511
theorem B8148671 : Blo 2145435 8148671 := bstep (se 1 (by rfl) ⟨6111503, by rfl⟩ : syracuseStep 8148671 = 12223007) B12223007
theorem B5432447 : Blo 2145435 5432447 := bstep (se 1 (by rfl) ⟨4074335, by rfl⟩ : syracuseStep 5432447 = 8148671) B8148671
theorem B3621631 : Blo 2145435 3621631 := bstep (se 1 (by rfl) ⟨2716223, by rfl⟩ : syracuseStep 3621631 = 5432447) B5432447
theorem B4828841 : Blo 2145435 4828841 := bstep (se 2 (by rfl) ⟨1810815, by rfl⟩ : syracuseStep 4828841 = 3621631) B3621631
theorem B3219227 : Blo 2145435 3219227 := bstep (se 1 (by rfl) ⟨2414420, by rfl⟩ : syracuseStep 3219227 = 4828841) B4828841
theorem B2146151 : Blo 2145435 2146151 := bstep (se 1 (by rfl) ⟨1609613, by rfl⟩ : syracuseStep 2146151 = 3219227) B3219227
theorem B2414425 : Blo 2145435 2414425 := bbase (se 2 (by rfl) ⟨905409, by rfl⟩ : syracuseStep 2414425 = 1810819) (by norm_num)
theorem B3219233 : Blo 2145435 3219233 := bstep (se 2 (by rfl) ⟨1207212, by rfl⟩ : syracuseStep 3219233 = 2414425) B2414425
theorem B2146155 : Blo 2145435 2146155 := bstep (se 1 (by rfl) ⟨1609616, by rfl⟩ : syracuseStep 2146155 = 3219233) B3219233
theorem B4583645 : Blo 2145435 4583645 := bbase (se 3 (by rfl) ⟨859433, by rfl⟩ : syracuseStep 4583645 = 1718867) (by norm_num)
theorem B3055763 : Blo 2145435 3055763 := bstep (se 1 (by rfl) ⟨2291822, by rfl⟩ : syracuseStep 3055763 = 4583645) B4583645
theorem B8148701 : Blo 2145435 8148701 := bstep (se 3 (by rfl) ⟨1527881, by rfl⟩ : syracuseStep 8148701 = 3055763) B3055763
theorem B5432467 : Blo 2145435 5432467 := bstep (se 1 (by rfl) ⟨4074350, by rfl⟩ : syracuseStep 5432467 = 8148701) B8148701
theorem B7243289 : Blo 2145435 7243289 := bstep (se 2 (by rfl) ⟨2716233, by rfl⟩ : syracuseStep 7243289 = 5432467) B5432467
theorem B4828859 : Blo 2145435 4828859 := bstep (se 1 (by rfl) ⟨3621644, by rfl⟩ : syracuseStep 4828859 = 7243289) B7243289
theorem B3219239 : Blo 2145435 3219239 := bstep (se 1 (by rfl) ⟨2414429, by rfl⟩ : syracuseStep 3219239 = 4828859) B4828859
theorem B2146159 : Blo 2145435 2146159 := bstep (se 1 (by rfl) ⟨1609619, by rfl⟩ : syracuseStep 2146159 = 3219239) B3219239
theorem B3219245 : Blo 2145435 3219245 := bbase (se 3 (by rfl) ⟨603608, by rfl⟩ : syracuseStep 3219245 = 1207217) (by norm_num)
theorem B2146163 : Blo 2145435 2146163 := bstep (se 1 (by rfl) ⟨1609622, by rfl⟩ : syracuseStep 2146163 = 3219245) B3219245
theorem B4828877 : Blo 2145435 4828877 := bbase (se 3 (by rfl) ⟨905414, by rfl⟩ : syracuseStep 4828877 = 1810829) (by norm_num)
theorem B3219251 : Blo 2145435 3219251 := bstep (se 1 (by rfl) ⟨2414438, by rfl⟩ : syracuseStep 3219251 = 4828877) B4828877
theorem B2146167 : Blo 2145435 2146167 := bstep (se 1 (by rfl) ⟨1609625, by rfl⟩ : syracuseStep 2146167 = 3219251) B3219251
theorem B2716249 : Blo 2145435 2716249 := bbase (se 2 (by rfl) ⟨1018593, by rfl⟩ : syracuseStep 2716249 = 2037187) (by norm_num)
theorem B3621665 : Blo 2145435 3621665 := bstep (se 2 (by rfl) ⟨1358124, by rfl⟩ : syracuseStep 3621665 = 2716249) B2716249
theorem B2414443 : Blo 2145435 2414443 := bstep (se 1 (by rfl) ⟨1810832, by rfl⟩ : syracuseStep 2414443 = 3621665) B3621665
theorem B3219257 : Blo 2145435 3219257 := bstep (se 2 (by rfl) ⟨1207221, by rfl⟩ : syracuseStep 3219257 = 2414443) B2414443
theorem B2146171 : Blo 2145435 2146171 := bstep (se 1 (by rfl) ⟨1609628, by rfl⟩ : syracuseStep 2146171 = 3219257) B3219257
theorem B8259941 : Blo 2145435 8259941 := bbase (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) (by norm_num)
theorem B5506627 : Blo 2145435 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B7342169 : Blo 2145435 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B19579117 : Blo 2145435 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B26105489 : Blo 2145435 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B17403659 : Blo 2145435 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B11602439 : Blo 2145435 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B7734959 : Blo 2145435 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B5156639 : Blo 2145435 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B3437759 : Blo 2145435 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B9167357 : Blo 2145435 9167357 := bstep (se 3 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 9167357 = 3437759) B3437759
theorem B24446285 : Blo 2145435 24446285 := bstep (se 3 (by rfl) ⟨4583678, by rfl⟩ : syracuseStep 24446285 = 9167357) B9167357
theorem B16297523 : Blo 2145435 16297523 := bstep (se 1 (by rfl) ⟨12223142, by rfl⟩ : syracuseStep 16297523 = 24446285) B24446285
theorem B10865015 : Blo 2145435 10865015 := bstep (se 1 (by rfl) ⟨8148761, by rfl⟩ : syracuseStep 10865015 = 16297523) B16297523
theorem B7243343 : Blo 2145435 7243343 := bstep (se 1 (by rfl) ⟨5432507, by rfl⟩ : syracuseStep 7243343 = 10865015) B10865015
theorem B4828895 : Blo 2145435 4828895 := bstep (se 1 (by rfl) ⟨3621671, by rfl⟩ : syracuseStep 4828895 = 7243343) B7243343
theorem B3219263 : Blo 2145435 3219263 := bstep (se 1 (by rfl) ⟨2414447, by rfl⟩ : syracuseStep 3219263 = 4828895) B4828895
theorem B2146175 : Blo 2145435 2146175 := bstep (se 1 (by rfl) ⟨1609631, by rfl⟩ : syracuseStep 2146175 = 3219263) B3219263
theorem B3219269 : Blo 2145435 3219269 := bbase (se 4 (by rfl) ⟨301806, by rfl⟩ : syracuseStep 3219269 = 603613) (by norm_num)
theorem B2146179 : Blo 2145435 2146179 := bstep (se 1 (by rfl) ⟨1609634, by rfl⟩ : syracuseStep 2146179 = 3219269) B3219269
theorem B3621685 : Blo 2145435 3621685 := bbase (se 5 (by rfl) ⟨169766, by rfl⟩ : syracuseStep 3621685 = 339533) (by norm_num)
theorem B4828913 : Blo 2145435 4828913 := bstep (se 2 (by rfl) ⟨1810842, by rfl⟩ : syracuseStep 4828913 = 3621685) B3621685
theorem B3219275 : Blo 2145435 3219275 := bstep (se 1 (by rfl) ⟨2414456, by rfl⟩ : syracuseStep 3219275 = 4828913) B4828913
theorem B2146183 : Blo 2145435 2146183 := bstep (se 1 (by rfl) ⟨1609637, by rfl⟩ : syracuseStep 2146183 = 3219275) B3219275
theorem B2414461 : Blo 2145435 2414461 := bbase (se 3 (by rfl) ⟨452711, by rfl⟩ : syracuseStep 2414461 = 905423) (by norm_num)
theorem B3219281 : Blo 2145435 3219281 := bstep (se 2 (by rfl) ⟨1207230, by rfl⟩ : syracuseStep 3219281 = 2414461) B2414461
theorem B2146187 : Blo 2145435 2146187 := bstep (se 1 (by rfl) ⟨1609640, by rfl⟩ : syracuseStep 2146187 = 3219281) B3219281
theorem B7243397 : Blo 2145435 7243397 := bbase (se 4 (by rfl) ⟨679068, by rfl⟩ : syracuseStep 7243397 = 1358137) (by norm_num)
theorem B4828931 : Blo 2145435 4828931 := bstep (se 1 (by rfl) ⟨3621698, by rfl⟩ : syracuseStep 4828931 = 7243397) B7243397
theorem B3219287 : Blo 2145435 3219287 := bstep (se 1 (by rfl) ⟨2414465, by rfl⟩ : syracuseStep 3219287 = 4828931) B4828931
theorem B2146191 : Blo 2145435 2146191 := bstep (se 1 (by rfl) ⟨1609643, by rfl⟩ : syracuseStep 2146191 = 3219287) B3219287
theorem B3219293 : Blo 2145435 3219293 := bbase (se 3 (by rfl) ⟨603617, by rfl⟩ : syracuseStep 3219293 = 1207235) (by norm_num)
theorem B2146195 : Blo 2145435 2146195 := bstep (se 1 (by rfl) ⟨1609646, by rfl⟩ : syracuseStep 2146195 = 3219293) B3219293
theorem B4828949 : Blo 2145435 4828949 := bbase (se 6 (by rfl) ⟨113178, by rfl⟩ : syracuseStep 4828949 = 226357) (by norm_num)
theorem B3219299 : Blo 2145435 3219299 := bstep (se 1 (by rfl) ⟨2414474, by rfl⟩ : syracuseStep 3219299 = 4828949) B4828949
theorem B2146199 : Blo 2145435 2146199 := bstep (se 1 (by rfl) ⟨1609649, by rfl⟩ : syracuseStep 2146199 = 3219299) B3219299
theorem B8148869 : Blo 2145435 8148869 := bbase (se 4 (by rfl) ⟨763956, by rfl⟩ : syracuseStep 8148869 = 1527913) (by norm_num)
theorem B5432579 : Blo 2145435 5432579 := bstep (se 1 (by rfl) ⟨4074434, by rfl⟩ : syracuseStep 5432579 = 8148869) B8148869
theorem B3621719 : Blo 2145435 3621719 := bstep (se 1 (by rfl) ⟨2716289, by rfl⟩ : syracuseStep 3621719 = 5432579) B5432579
theorem B2414479 : Blo 2145435 2414479 := bstep (se 1 (by rfl) ⟨1810859, by rfl⟩ : syracuseStep 2414479 = 3621719) B3621719
theorem B3219305 : Blo 2145435 3219305 := bstep (se 2 (by rfl) ⟨1207239, by rfl⟩ : syracuseStep 3219305 = 2414479) B2414479
theorem B2146203 : Blo 2145435 2146203 := bstep (se 1 (by rfl) ⟨1609652, by rfl⟩ : syracuseStep 2146203 = 3219305) B3219305
theorem B6875621 : Blo 2145435 6875621 := bbase (se 4 (by rfl) ⟨644589, by rfl⟩ : syracuseStep 6875621 = 1289179) (by norm_num)
theorem B4583747 : Blo 2145435 4583747 := bstep (se 1 (by rfl) ⟨3437810, by rfl⟩ : syracuseStep 4583747 = 6875621) B6875621
theorem B12223325 : Blo 2145435 12223325 := bstep (se 3 (by rfl) ⟨2291873, by rfl⟩ : syracuseStep 12223325 = 4583747) B4583747
theorem B8148883 : Blo 2145435 8148883 := bstep (se 1 (by rfl) ⟨6111662, by rfl⟩ : syracuseStep 8148883 = 12223325) B12223325
theorem B10865177 : Blo 2145435 10865177 := bstep (se 2 (by rfl) ⟨4074441, by rfl⟩ : syracuseStep 10865177 = 8148883) B8148883
theorem B7243451 : Blo 2145435 7243451 := bstep (se 1 (by rfl) ⟨5432588, by rfl⟩ : syracuseStep 7243451 = 10865177) B10865177
theorem B4828967 : Blo 2145435 4828967 := bstep (se 1 (by rfl) ⟨3621725, by rfl⟩ : syracuseStep 4828967 = 7243451) B7243451
theorem B3219311 : Blo 2145435 3219311 := bstep (se 1 (by rfl) ⟨2414483, by rfl⟩ : syracuseStep 3219311 = 4828967) B4828967
theorem B2146207 : Blo 2145435 2146207 := bstep (se 1 (by rfl) ⟨1609655, by rfl⟩ : syracuseStep 2146207 = 3219311) B3219311
theorem B3219317 : Blo 2145435 3219317 := bbase (se 5 (by rfl) ⟨150905, by rfl⟩ : syracuseStep 3219317 = 301811) (by norm_num)
theorem B2146211 : Blo 2145435 2146211 := bstep (se 1 (by rfl) ⟨1609658, by rfl⟩ : syracuseStep 2146211 = 3219317) B3219317
theorem B4583765 : Blo 2145435 4583765 := bbase (se 10 (by rfl) ⟨6714, by rfl⟩ : syracuseStep 4583765 = 13429) (by norm_num)
theorem B3055843 : Blo 2145435 3055843 := bstep (se 1 (by rfl) ⟨2291882, by rfl⟩ : syracuseStep 3055843 = 4583765) B4583765
theorem B4074457 : Blo 2145435 4074457 := bstep (se 2 (by rfl) ⟨1527921, by rfl⟩ : syracuseStep 4074457 = 3055843) B3055843
theorem B5432609 : Blo 2145435 5432609 := bstep (se 2 (by rfl) ⟨2037228, by rfl⟩ : syracuseStep 5432609 = 4074457) B4074457
theorem B3621739 : Blo 2145435 3621739 := bstep (se 1 (by rfl) ⟨2716304, by rfl⟩ : syracuseStep 3621739 = 5432609) B5432609
theorem B4828985 : Blo 2145435 4828985 := bstep (se 2 (by rfl) ⟨1810869, by rfl⟩ : syracuseStep 4828985 = 3621739) B3621739
theorem B3219323 : Blo 2145435 3219323 := bstep (se 1 (by rfl) ⟨2414492, by rfl⟩ : syracuseStep 3219323 = 4828985) B4828985
theorem B2146215 : Blo 2145435 2146215 := bstep (se 1 (by rfl) ⟨1609661, by rfl⟩ : syracuseStep 2146215 = 3219323) B3219323
theorem B2414497 : Blo 2145435 2414497 := bbase (se 2 (by rfl) ⟨905436, by rfl⟩ : syracuseStep 2414497 = 1810873) (by norm_num)
theorem B3219329 : Blo 2145435 3219329 := bstep (se 2 (by rfl) ⟨1207248, by rfl⟩ : syracuseStep 3219329 = 2414497) B2414497
theorem B2146219 : Blo 2145435 2146219 := bstep (se 1 (by rfl) ⟨1609664, by rfl⟩ : syracuseStep 2146219 = 3219329) B3219329
theorem B5432629 : Blo 2145435 5432629 := bbase (se 5 (by rfl) ⟨254654, by rfl⟩ : syracuseStep 5432629 = 509309) (by norm_num)
theorem B7243505 : Blo 2145435 7243505 := bstep (se 2 (by rfl) ⟨2716314, by rfl⟩ : syracuseStep 7243505 = 5432629) B5432629
theorem B4829003 : Blo 2145435 4829003 := bstep (se 1 (by rfl) ⟨3621752, by rfl⟩ : syracuseStep 4829003 = 7243505) B7243505
theorem B3219335 : Blo 2145435 3219335 := bstep (se 1 (by rfl) ⟨2414501, by rfl⟩ : syracuseStep 3219335 = 4829003) B4829003
theorem B2146223 : Blo 2145435 2146223 := bstep (se 1 (by rfl) ⟨1609667, by rfl⟩ : syracuseStep 2146223 = 3219335) B3219335
theorem B3219341 : Blo 2145435 3219341 := bbase (se 3 (by rfl) ⟨603626, by rfl⟩ : syracuseStep 3219341 = 1207253) (by norm_num)
theorem B2146227 : Blo 2145435 2146227 := bstep (se 1 (by rfl) ⟨1609670, by rfl⟩ : syracuseStep 2146227 = 3219341) B3219341
theorem B4829021 : Blo 2145435 4829021 := bbase (se 3 (by rfl) ⟨905441, by rfl⟩ : syracuseStep 4829021 = 1810883) (by norm_num)
theorem B3219347 : Blo 2145435 3219347 := bstep (se 1 (by rfl) ⟨2414510, by rfl⟩ : syracuseStep 3219347 = 4829021) B4829021
theorem B2146231 : Blo 2145435 2146231 := bstep (se 1 (by rfl) ⟨1609673, by rfl⟩ : syracuseStep 2146231 = 3219347) B3219347
theorem B3621773 : Blo 2145435 3621773 := bbase (se 3 (by rfl) ⟨679082, by rfl⟩ : syracuseStep 3621773 = 1358165) (by norm_num)
theorem B2414515 : Blo 2145435 2414515 := bstep (se 1 (by rfl) ⟨1810886, by rfl⟩ : syracuseStep 2414515 = 3621773) B3621773
theorem B3219353 : Blo 2145435 3219353 := bstep (se 2 (by rfl) ⟨1207257, by rfl⟩ : syracuseStep 3219353 = 2414515) B2414515
theorem B2146235 : Blo 2145435 2146235 := bstep (se 1 (by rfl) ⟨1609676, by rfl⟩ : syracuseStep 2146235 = 3219353) B3219353
theorem B7735189 : Blo 2145435 7735189 := bbase (se 6 (by rfl) ⟨181293, by rfl⟩ : syracuseStep 7735189 = 362587) (by norm_num)
theorem B10313585 : Blo 2145435 10313585 := bstep (se 2 (by rfl) ⟨3867594, by rfl⟩ : syracuseStep 10313585 = 7735189) B7735189
theorem B6875723 : Blo 2145435 6875723 := bstep (se 1 (by rfl) ⟨5156792, by rfl⟩ : syracuseStep 6875723 = 10313585) B10313585
theorem B18335261 : Blo 2145435 18335261 := bstep (se 3 (by rfl) ⟨3437861, by rfl⟩ : syracuseStep 18335261 = 6875723) B6875723
theorem B12223507 : Blo 2145435 12223507 := bstep (se 1 (by rfl) ⟨9167630, by rfl⟩ : syracuseStep 12223507 = 18335261) B18335261
theorem B16298009 : Blo 2145435 16298009 := bstep (se 2 (by rfl) ⟨6111753, by rfl⟩ : syracuseStep 16298009 = 12223507) B12223507
theorem B10865339 : Blo 2145435 10865339 := bstep (se 1 (by rfl) ⟨8149004, by rfl⟩ : syracuseStep 10865339 = 16298009) B16298009
theorem B7243559 : Blo 2145435 7243559 := bstep (se 1 (by rfl) ⟨5432669, by rfl⟩ : syracuseStep 7243559 = 10865339) B10865339
theorem B4829039 : Blo 2145435 4829039 := bstep (se 1 (by rfl) ⟨3621779, by rfl⟩ : syracuseStep 4829039 = 7243559) B7243559
theorem B3219359 : Blo 2145435 3219359 := bstep (se 1 (by rfl) ⟨2414519, by rfl⟩ : syracuseStep 3219359 = 4829039) B4829039
theorem B2146239 : Blo 2145435 2146239 := bstep (se 1 (by rfl) ⟨1609679, by rfl⟩ : syracuseStep 2146239 = 3219359) B3219359
theorem B3219365 : Blo 2145435 3219365 := bbase (se 4 (by rfl) ⟨301815, by rfl⟩ : syracuseStep 3219365 = 603631) (by norm_num)
theorem B2146243 : Blo 2145435 2146243 := bstep (se 1 (by rfl) ⟨1609682, by rfl⟩ : syracuseStep 2146243 = 3219365) B3219365
theorem B2716345 : Blo 2145435 2716345 := bbase (se 2 (by rfl) ⟨1018629, by rfl⟩ : syracuseStep 2716345 = 2037259) (by norm_num)
theorem B3621793 : Blo 2145435 3621793 := bstep (se 2 (by rfl) ⟨1358172, by rfl⟩ : syracuseStep 3621793 = 2716345) B2716345
theorem B4829057 : Blo 2145435 4829057 := bstep (se 2 (by rfl) ⟨1810896, by rfl⟩ : syracuseStep 4829057 = 3621793) B3621793
theorem B3219371 : Blo 2145435 3219371 := bstep (se 1 (by rfl) ⟨2414528, by rfl⟩ : syracuseStep 3219371 = 4829057) B4829057
theorem B2146247 : Blo 2145435 2146247 := bstep (se 1 (by rfl) ⟨1609685, by rfl⟩ : syracuseStep 2146247 = 3219371) B3219371
theorem B2414533 : Blo 2145435 2414533 := bbase (se 4 (by rfl) ⟨226362, by rfl⟩ : syracuseStep 2414533 = 452725) (by norm_num)
theorem B3219377 : Blo 2145435 3219377 := bstep (se 2 (by rfl) ⟨1207266, by rfl⟩ : syracuseStep 3219377 = 2414533) B2414533
theorem B2146251 : Blo 2145435 2146251 := bstep (se 1 (by rfl) ⟨1609688, by rfl⟩ : syracuseStep 2146251 = 3219377) B3219377
theorem B4074533 : Blo 2145435 4074533 := bbase (se 4 (by rfl) ⟨381987, by rfl⟩ : syracuseStep 4074533 = 763975) (by norm_num)
theorem B2716355 : Blo 2145435 2716355 := bstep (se 1 (by rfl) ⟨2037266, by rfl⟩ : syracuseStep 2716355 = 4074533) B4074533
theorem B7243613 : Blo 2145435 7243613 := bstep (se 3 (by rfl) ⟨1358177, by rfl⟩ : syracuseStep 7243613 = 2716355) B2716355
theorem B4829075 : Blo 2145435 4829075 := bstep (se 1 (by rfl) ⟨3621806, by rfl⟩ : syracuseStep 4829075 = 7243613) B7243613
theorem B3219383 : Blo 2145435 3219383 := bstep (se 1 (by rfl) ⟨2414537, by rfl⟩ : syracuseStep 3219383 = 4829075) B4829075
theorem B2146255 : Blo 2145435 2146255 := bstep (se 1 (by rfl) ⟨1609691, by rfl⟩ : syracuseStep 2146255 = 3219383) B3219383
theorem B3219389 : Blo 2145435 3219389 := bbase (se 3 (by rfl) ⟨603635, by rfl⟩ : syracuseStep 3219389 = 1207271) (by norm_num)
theorem B2146259 : Blo 2145435 2146259 := bstep (se 1 (by rfl) ⟨1609694, by rfl⟩ : syracuseStep 2146259 = 3219389) B3219389
theorem B4829093 : Blo 2145435 4829093 := bbase (se 4 (by rfl) ⟨452727, by rfl⟩ : syracuseStep 4829093 = 905455) (by norm_num)
theorem B3219395 : Blo 2145435 3219395 := bstep (se 1 (by rfl) ⟨2414546, by rfl⟩ : syracuseStep 3219395 = 4829093) B4829093
theorem B2146263 : Blo 2145435 2146263 := bstep (se 1 (by rfl) ⟨1609697, by rfl⟩ : syracuseStep 2146263 = 3219395) B3219395
theorem B5432741 : Blo 2145435 5432741 := bbase (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) (by norm_num)
theorem B3621827 : Blo 2145435 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B2414551 : Blo 2145435 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B3219401 : Blo 2145435 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B2146267 : Blo 2145435 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B6111845 : Blo 2145435 6111845 := bbase (se 4 (by rfl) ⟨572985, by rfl⟩ : syracuseStep 6111845 = 1145971) (by norm_num)
theorem B4074563 : Blo 2145435 4074563 := bstep (se 1 (by rfl) ⟨3055922, by rfl⟩ : syracuseStep 4074563 = 6111845) B6111845
theorem B10865501 : Blo 2145435 10865501 := bstep (se 3 (by rfl) ⟨2037281, by rfl⟩ : syracuseStep 10865501 = 4074563) B4074563
theorem B7243667 : Blo 2145435 7243667 := bstep (se 1 (by rfl) ⟨5432750, by rfl⟩ : syracuseStep 7243667 = 10865501) B10865501
theorem B4829111 : Blo 2145435 4829111 := bstep (se 1 (by rfl) ⟨3621833, by rfl⟩ : syracuseStep 4829111 = 7243667) B7243667
theorem B3219407 : Blo 2145435 3219407 := bstep (se 1 (by rfl) ⟨2414555, by rfl⟩ : syracuseStep 3219407 = 4829111) B4829111
theorem B2146271 : Blo 2145435 2146271 := bstep (se 1 (by rfl) ⟨1609703, by rfl⟩ : syracuseStep 2146271 = 3219407) B3219407
theorem B3219413 : Blo 2145435 3219413 := bbase (se 7 (by rfl) ⟨37727, by rfl⟩ : syracuseStep 3219413 = 75455) (by norm_num)
theorem B2146275 : Blo 2145435 2146275 := bstep (se 1 (by rfl) ⟨1609706, by rfl⟩ : syracuseStep 2146275 = 3219413) B3219413
theorem B8149157 : Blo 2145435 8149157 := bbase (se 4 (by rfl) ⟨763983, by rfl⟩ : syracuseStep 8149157 = 1527967) (by norm_num)
theorem B5432771 : Blo 2145435 5432771 := bstep (se 1 (by rfl) ⟨4074578, by rfl⟩ : syracuseStep 5432771 = 8149157) B8149157
theorem B3621847 : Blo 2145435 3621847 := bstep (se 1 (by rfl) ⟨2716385, by rfl⟩ : syracuseStep 3621847 = 5432771) B5432771
theorem B4829129 : Blo 2145435 4829129 := bstep (se 2 (by rfl) ⟨1810923, by rfl⟩ : syracuseStep 4829129 = 3621847) B3621847
theorem B3219419 : Blo 2145435 3219419 := bstep (se 1 (by rfl) ⟨2414564, by rfl⟩ : syracuseStep 3219419 = 4829129) B4829129
theorem B2146279 : Blo 2145435 2146279 := bstep (se 1 (by rfl) ⟨1609709, by rfl⟩ : syracuseStep 2146279 = 3219419) B3219419
theorem B2414569 : Blo 2145435 2414569 := bbase (se 2 (by rfl) ⟨905463, by rfl⟩ : syracuseStep 2414569 = 1810927) (by norm_num)
theorem B3219425 : Blo 2145435 3219425 := bstep (se 2 (by rfl) ⟨1207284, by rfl⟩ : syracuseStep 3219425 = 2414569) B2414569
theorem B2146283 : Blo 2145435 2146283 := bstep (se 1 (by rfl) ⟨1609712, by rfl⟩ : syracuseStep 2146283 = 3219425) B3219425
theorem B5156909 : Blo 2145435 5156909 := bbase (se 3 (by rfl) ⟨966920, by rfl⟩ : syracuseStep 5156909 = 1933841) (by norm_num)
theorem B3437939 : Blo 2145435 3437939 := bstep (se 1 (by rfl) ⟨2578454, by rfl⟩ : syracuseStep 3437939 = 5156909) B5156909
theorem B2291959 : Blo 2145435 2291959 := bstep (se 1 (by rfl) ⟨1718969, by rfl⟩ : syracuseStep 2291959 = 3437939) B3437939
theorem B12223781 : Blo 2145435 12223781 := bstep (se 4 (by rfl) ⟨1145979, by rfl⟩ : syracuseStep 12223781 = 2291959) B2291959
theorem B8149187 : Blo 2145435 8149187 := bstep (se 1 (by rfl) ⟨6111890, by rfl⟩ : syracuseStep 8149187 = 12223781) B12223781
theorem B5432791 : Blo 2145435 5432791 := bstep (se 1 (by rfl) ⟨4074593, by rfl⟩ : syracuseStep 5432791 = 8149187) B8149187
theorem B7243721 : Blo 2145435 7243721 := bstep (se 2 (by rfl) ⟨2716395, by rfl⟩ : syracuseStep 7243721 = 5432791) B5432791
theorem B4829147 : Blo 2145435 4829147 := bstep (se 1 (by rfl) ⟨3621860, by rfl⟩ : syracuseStep 4829147 = 7243721) B7243721
theorem B3219431 : Blo 2145435 3219431 := bstep (se 1 (by rfl) ⟨2414573, by rfl⟩ : syracuseStep 3219431 = 4829147) B4829147
theorem B2146287 : Blo 2145435 2146287 := bstep (se 1 (by rfl) ⟨1609715, by rfl⟩ : syracuseStep 2146287 = 3219431) B3219431
theorem B3219437 : Blo 2145435 3219437 := bbase (se 3 (by rfl) ⟨603644, by rfl⟩ : syracuseStep 3219437 = 1207289) (by norm_num)
theorem B2146291 : Blo 2145435 2146291 := bstep (se 1 (by rfl) ⟨1609718, by rfl⟩ : syracuseStep 2146291 = 3219437) B3219437
theorem B4829165 : Blo 2145435 4829165 := bbase (se 3 (by rfl) ⟨905468, by rfl⟩ : syracuseStep 4829165 = 1810937) (by norm_num)
theorem B3219443 : Blo 2145435 3219443 := bstep (se 1 (by rfl) ⟨2414582, by rfl⟩ : syracuseStep 3219443 = 4829165) B4829165
theorem B2146295 : Blo 2145435 2146295 := bstep (se 1 (by rfl) ⟨1609721, by rfl⟩ : syracuseStep 2146295 = 3219443) B3219443
theorem B5801557 : Blo 2145435 5801557 := bbase (se 8 (by rfl) ⟨33993, by rfl⟩ : syracuseStep 5801557 = 67987) (by norm_num)
theorem B7735409 : Blo 2145435 7735409 := bstep (se 2 (by rfl) ⟨2900778, by rfl⟩ : syracuseStep 7735409 = 5801557) B5801557
theorem B5156939 : Blo 2145435 5156939 := bstep (se 1 (by rfl) ⟨3867704, by rfl⟩ : syracuseStep 5156939 = 7735409) B7735409
theorem B3437959 : Blo 2145435 3437959 := bstep (se 1 (by rfl) ⟨2578469, by rfl⟩ : syracuseStep 3437959 = 5156939) B5156939
theorem B4583945 : Blo 2145435 4583945 := bstep (se 2 (by rfl) ⟨1718979, by rfl⟩ : syracuseStep 4583945 = 3437959) B3437959
theorem B3055963 : Blo 2145435 3055963 := bstep (se 1 (by rfl) ⟨2291972, by rfl⟩ : syracuseStep 3055963 = 4583945) B4583945
theorem B4074617 : Blo 2145435 4074617 := bstep (se 2 (by rfl) ⟨1527981, by rfl⟩ : syracuseStep 4074617 = 3055963) B3055963
theorem B2716411 : Blo 2145435 2716411 := bstep (se 1 (by rfl) ⟨2037308, by rfl⟩ : syracuseStep 2716411 = 4074617) B4074617
theorem B3621881 : Blo 2145435 3621881 := bstep (se 2 (by rfl) ⟨1358205, by rfl⟩ : syracuseStep 3621881 = 2716411) B2716411
theorem B2414587 : Blo 2145435 2414587 := bstep (se 1 (by rfl) ⟨1810940, by rfl⟩ : syracuseStep 2414587 = 3621881) B3621881
theorem B3219449 : Blo 2145435 3219449 := bstep (se 2 (by rfl) ⟨1207293, by rfl⟩ : syracuseStep 3219449 = 2414587) B2414587
theorem B2146299 : Blo 2145435 2146299 := bstep (se 1 (by rfl) ⟨1609724, by rfl⟩ : syracuseStep 2146299 = 3219449) B3219449
theorem B2791045 : Blo 2145435 2791045 := bbase (se 4 (by rfl) ⟨261660, by rfl⟩ : syracuseStep 2791045 = 523321) (by norm_num)
theorem B3721393 : Blo 2145435 3721393 := bstep (se 2 (by rfl) ⟨1395522, by rfl⟩ : syracuseStep 3721393 = 2791045) B2791045
theorem B4961857 : Blo 2145435 4961857 := bstep (se 2 (by rfl) ⟨1860696, by rfl⟩ : syracuseStep 4961857 = 3721393) B3721393
theorem B6615809 : Blo 2145435 6615809 := bstep (se 2 (by rfl) ⟨2480928, by rfl⟩ : syracuseStep 6615809 = 4961857) B4961857
theorem B4410539 : Blo 2145435 4410539 := bstep (se 1 (by rfl) ⟨3307904, by rfl⟩ : syracuseStep 4410539 = 6615809) B6615809
theorem B2940359 : Blo 2145435 2940359 := bstep (se 1 (by rfl) ⟨2205269, by rfl⟩ : syracuseStep 2940359 = 4410539) B4410539
theorem B7840957 : Blo 2145435 7840957 := bstep (se 3 (by rfl) ⟨1470179, by rfl⟩ : syracuseStep 7840957 = 2940359) B2940359
theorem B10454609 : Blo 2145435 10454609 := bstep (se 2 (by rfl) ⟨3920478, by rfl⟩ : syracuseStep 10454609 = 7840957) B7840957
theorem B6969739 : Blo 2145435 6969739 := bstep (se 1 (by rfl) ⟨5227304, by rfl⟩ : syracuseStep 6969739 = 10454609) B10454609
theorem B9292985 : Blo 2145435 9292985 := bstep (se 2 (by rfl) ⟨3484869, by rfl⟩ : syracuseStep 9292985 = 6969739) B6969739
theorem B6195323 : Blo 2145435 6195323 := bstep (se 1 (by rfl) ⟨4646492, by rfl⟩ : syracuseStep 6195323 = 9292985) B9292985
theorem B16520861 : Blo 2145435 16520861 := bstep (se 3 (by rfl) ⟨3097661, by rfl⟩ : syracuseStep 16520861 = 6195323) B6195323
theorem B44055629 : Blo 2145435 44055629 := bstep (se 3 (by rfl) ⟨8260430, by rfl⟩ : syracuseStep 44055629 = 16520861) B16520861
theorem B29370419 : Blo 2145435 29370419 := bstep (se 1 (by rfl) ⟨22027814, by rfl⟩ : syracuseStep 29370419 = 44055629) B44055629
theorem B313284469 : Blo 2145435 313284469 := bstep (se 5 (by rfl) ⟨14685209, by rfl⟩ : syracuseStep 313284469 = 29370419) B29370419
theorem B417712625 : Blo 2145435 417712625 := bstep (se 2 (by rfl) ⟨156642234, by rfl⟩ : syracuseStep 417712625 = 313284469) B313284469
theorem B278475083 : Blo 2145435 278475083 := bstep (se 1 (by rfl) ⟨208856312, by rfl⟩ : syracuseStep 278475083 = 417712625) B417712625
theorem B185650055 : Blo 2145435 185650055 := bstep (se 1 (by rfl) ⟨139237541, by rfl⟩ : syracuseStep 185650055 = 278475083) B278475083
theorem B123766703 : Blo 2145435 123766703 := bstep (se 1 (by rfl) ⟨92825027, by rfl⟩ : syracuseStep 123766703 = 185650055) B185650055
theorem B82511135 : Blo 2145435 82511135 := bstep (se 1 (by rfl) ⟨61883351, by rfl⟩ : syracuseStep 82511135 = 123766703) B123766703
theorem B55007423 : Blo 2145435 55007423 := bstep (se 1 (by rfl) ⟨41255567, by rfl⟩ : syracuseStep 55007423 = 82511135) B82511135
theorem B36671615 : Blo 2145435 36671615 := bstep (se 1 (by rfl) ⟨27503711, by rfl⟩ : syracuseStep 36671615 = 55007423) B55007423
theorem B24447743 : Blo 2145435 24447743 := bstep (se 1 (by rfl) ⟨18335807, by rfl⟩ : syracuseStep 24447743 = 36671615) B36671615
theorem B16298495 : Blo 2145435 16298495 := bstep (se 1 (by rfl) ⟨12223871, by rfl⟩ : syracuseStep 16298495 = 24447743) B24447743
theorem B10865663 : Blo 2145435 10865663 := bstep (se 1 (by rfl) ⟨8149247, by rfl⟩ : syracuseStep 10865663 = 16298495) B16298495
theorem B7243775 : Blo 2145435 7243775 := bstep (se 1 (by rfl) ⟨5432831, by rfl⟩ : syracuseStep 7243775 = 10865663) B10865663
theorem B4829183 : Blo 2145435 4829183 := bstep (se 1 (by rfl) ⟨3621887, by rfl⟩ : syracuseStep 4829183 = 7243775) B7243775
theorem B3219455 : Blo 2145435 3219455 := bstep (se 1 (by rfl) ⟨2414591, by rfl⟩ : syracuseStep 3219455 = 4829183) B4829183
theorem B2146303 : Blo 2145435 2146303 := bstep (se 1 (by rfl) ⟨1609727, by rfl⟩ : syracuseStep 2146303 = 3219455) B3219455
theorem B3219461 : Blo 2145435 3219461 := bbase (se 4 (by rfl) ⟨301824, by rfl⟩ : syracuseStep 3219461 = 603649) (by norm_num)
theorem B2146307 : Blo 2145435 2146307 := bstep (se 1 (by rfl) ⟨1609730, by rfl⟩ : syracuseStep 2146307 = 3219461) B3219461
theorem B3621901 : Blo 2145435 3621901 := bbase (se 3 (by rfl) ⟨679106, by rfl⟩ : syracuseStep 3621901 = 1358213) (by norm_num)
theorem B4829201 : Blo 2145435 4829201 := bstep (se 2 (by rfl) ⟨1810950, by rfl⟩ : syracuseStep 4829201 = 3621901) B3621901
theorem B3219467 : Blo 2145435 3219467 := bstep (se 1 (by rfl) ⟨2414600, by rfl⟩ : syracuseStep 3219467 = 4829201) B4829201
theorem B2146311 : Blo 2145435 2146311 := bstep (se 1 (by rfl) ⟨1609733, by rfl⟩ : syracuseStep 2146311 = 3219467) B3219467
theorem B2414605 : Blo 2145435 2414605 := bbase (se 3 (by rfl) ⟨452738, by rfl⟩ : syracuseStep 2414605 = 905477) (by norm_num)
theorem B3219473 : Blo 2145435 3219473 := bstep (se 2 (by rfl) ⟨1207302, by rfl⟩ : syracuseStep 3219473 = 2414605) B2414605
theorem B2146315 : Blo 2145435 2146315 := bstep (se 1 (by rfl) ⟨1609736, by rfl⟩ : syracuseStep 2146315 = 3219473) B3219473
theorem B7243829 : Blo 2145435 7243829 := bbase (se 5 (by rfl) ⟨339554, by rfl⟩ : syracuseStep 7243829 = 679109) (by norm_num)
theorem B4829219 : Blo 2145435 4829219 := bstep (se 1 (by rfl) ⟨3621914, by rfl⟩ : syracuseStep 4829219 = 7243829) B7243829
theorem B3219479 : Blo 2145435 3219479 := bstep (se 1 (by rfl) ⟨2414609, by rfl⟩ : syracuseStep 3219479 = 4829219) B4829219
theorem B2146319 : Blo 2145435 2146319 := bstep (se 1 (by rfl) ⟨1609739, by rfl⟩ : syracuseStep 2146319 = 3219479) B3219479
theorem B3219485 : Blo 2145435 3219485 := bbase (se 3 (by rfl) ⟨603653, by rfl⟩ : syracuseStep 3219485 = 1207307) (by norm_num)
theorem B2146323 : Blo 2145435 2146323 := bstep (se 1 (by rfl) ⟨1609742, by rfl⟩ : syracuseStep 2146323 = 3219485) B3219485
theorem B4829237 : Blo 2145435 4829237 := bbase (se 5 (by rfl) ⟨226370, by rfl⟩ : syracuseStep 4829237 = 452741) (by norm_num)
theorem B3219491 : Blo 2145435 3219491 := bstep (se 1 (by rfl) ⟨2414618, by rfl⟩ : syracuseStep 3219491 = 4829237) B4829237
theorem B2146327 : Blo 2145435 2146327 := bstep (se 1 (by rfl) ⟨1609745, by rfl⟩ : syracuseStep 2146327 = 3219491) B3219491
theorem B2900821 : Blo 2145435 2900821 := bbase (se 9 (by rfl) ⟨8498, by rfl⟩ : syracuseStep 2900821 = 16997) (by norm_num)
theorem B3867761 : Blo 2145435 3867761 := bstep (se 2 (by rfl) ⟨1450410, by rfl⟩ : syracuseStep 3867761 = 2900821) B2900821
theorem B10314029 : Blo 2145435 10314029 := bstep (se 3 (by rfl) ⟨1933880, by rfl⟩ : syracuseStep 10314029 = 3867761) B3867761
theorem B6876019 : Blo 2145435 6876019 := bstep (se 1 (by rfl) ⟨5157014, by rfl⟩ : syracuseStep 6876019 = 10314029) B10314029
theorem B9168025 : Blo 2145435 9168025 := bstep (se 2 (by rfl) ⟨3438009, by rfl⟩ : syracuseStep 9168025 = 6876019) B6876019
theorem B12224033 : Blo 2145435 12224033 := bstep (se 2 (by rfl) ⟨4584012, by rfl⟩ : syracuseStep 12224033 = 9168025) B9168025
theorem B8149355 : Blo 2145435 8149355 := bstep (se 1 (by rfl) ⟨6112016, by rfl⟩ : syracuseStep 8149355 = 12224033) B12224033
theorem B5432903 : Blo 2145435 5432903 := bstep (se 1 (by rfl) ⟨4074677, by rfl⟩ : syracuseStep 5432903 = 8149355) B8149355
theorem B3621935 : Blo 2145435 3621935 := bstep (se 1 (by rfl) ⟨2716451, by rfl⟩ : syracuseStep 3621935 = 5432903) B5432903
theorem B2414623 : Blo 2145435 2414623 := bstep (se 1 (by rfl) ⟨1810967, by rfl⟩ : syracuseStep 2414623 = 3621935) B3621935
theorem B3219497 : Blo 2145435 3219497 := bstep (se 2 (by rfl) ⟨1207311, by rfl⟩ : syracuseStep 3219497 = 2414623) B2414623
theorem B2146331 : Blo 2145435 2146331 := bstep (se 1 (by rfl) ⟨1609748, by rfl⟩ : syracuseStep 2146331 = 3219497) B3219497
theorem B2480965 : Blo 2145435 2480965 := bbase (se 4 (by rfl) ⟨232590, by rfl⟩ : syracuseStep 2480965 = 465181) (by norm_num)
theorem B13231813 : Blo 2145435 13231813 := bstep (se 4 (by rfl) ⟨1240482, by rfl⟩ : syracuseStep 13231813 = 2480965) B2480965
theorem B17642417 : Blo 2145435 17642417 := bstep (se 2 (by rfl) ⟨6615906, by rfl⟩ : syracuseStep 17642417 = 13231813) B13231813
theorem B188185781 : Blo 2145435 188185781 := bstep (se 5 (by rfl) ⟨8821208, by rfl⟩ : syracuseStep 188185781 = 17642417) B17642417
theorem B125457187 : Blo 2145435 125457187 := bstep (se 1 (by rfl) ⟨94092890, by rfl⟩ : syracuseStep 125457187 = 188185781) B188185781
theorem B167276249 : Blo 2145435 167276249 := bstep (se 2 (by rfl) ⟨62728593, by rfl⟩ : syracuseStep 167276249 = 125457187) B125457187
theorem B111517499 : Blo 2145435 111517499 := bstep (se 1 (by rfl) ⟨83638124, by rfl⟩ : syracuseStep 111517499 = 167276249) B167276249
theorem B74344999 : Blo 2145435 74344999 := bstep (se 1 (by rfl) ⟨55758749, by rfl⟩ : syracuseStep 74344999 = 111517499) B111517499
theorem B99126665 : Blo 2145435 99126665 := bstep (se 2 (by rfl) ⟨37172499, by rfl⟩ : syracuseStep 99126665 = 74344999) B74344999
theorem B66084443 : Blo 2145435 66084443 := bstep (se 1 (by rfl) ⟨49563332, by rfl⟩ : syracuseStep 66084443 = 99126665) B99126665
theorem B44056295 : Blo 2145435 44056295 := bstep (se 1 (by rfl) ⟨33042221, by rfl⟩ : syracuseStep 44056295 = 66084443) B66084443
theorem B29370863 : Blo 2145435 29370863 := bstep (se 1 (by rfl) ⟨22028147, by rfl⟩ : syracuseStep 29370863 = 44056295) B44056295
theorem B78322301 : Blo 2145435 78322301 := bstep (se 3 (by rfl) ⟨14685431, by rfl⟩ : syracuseStep 78322301 = 29370863) B29370863
theorem B52214867 : Blo 2145435 52214867 := bstep (se 1 (by rfl) ⟨39161150, by rfl⟩ : syracuseStep 52214867 = 78322301) B78322301
theorem B34809911 : Blo 2145435 34809911 := bstep (se 1 (by rfl) ⟨26107433, by rfl⟩ : syracuseStep 34809911 = 52214867) B52214867
theorem B23206607 : Blo 2145435 23206607 := bstep (se 1 (by rfl) ⟨17404955, by rfl⟩ : syracuseStep 23206607 = 34809911) B34809911
theorem B15471071 : Blo 2145435 15471071 := bstep (se 1 (by rfl) ⟨11603303, by rfl⟩ : syracuseStep 15471071 = 23206607) B23206607
theorem B10314047 : Blo 2145435 10314047 := bstep (se 1 (by rfl) ⟨7735535, by rfl⟩ : syracuseStep 10314047 = 15471071) B15471071
theorem B6876031 : Blo 2145435 6876031 := bstep (se 1 (by rfl) ⟨5157023, by rfl⟩ : syracuseStep 6876031 = 10314047) B10314047
theorem B9168041 : Blo 2145435 9168041 := bstep (se 2 (by rfl) ⟨3438015, by rfl⟩ : syracuseStep 9168041 = 6876031) B6876031
theorem B6112027 : Blo 2145435 6112027 := bstep (se 1 (by rfl) ⟨4584020, by rfl⟩ : syracuseStep 6112027 = 9168041) B9168041
theorem B8149369 : Blo 2145435 8149369 := bstep (se 2 (by rfl) ⟨3056013, by rfl⟩ : syracuseStep 8149369 = 6112027) B6112027
theorem B10865825 : Blo 2145435 10865825 := bstep (se 2 (by rfl) ⟨4074684, by rfl⟩ : syracuseStep 10865825 = 8149369) B8149369
theorem B7243883 : Blo 2145435 7243883 := bstep (se 1 (by rfl) ⟨5432912, by rfl⟩ : syracuseStep 7243883 = 10865825) B10865825
theorem B4829255 : Blo 2145435 4829255 := bstep (se 1 (by rfl) ⟨3621941, by rfl⟩ : syracuseStep 4829255 = 7243883) B7243883
theorem B3219503 : Blo 2145435 3219503 := bstep (se 1 (by rfl) ⟨2414627, by rfl⟩ : syracuseStep 3219503 = 4829255) B4829255
theorem B2146335 : Blo 2145435 2146335 := bstep (se 1 (by rfl) ⟨1609751, by rfl⟩ : syracuseStep 2146335 = 3219503) B3219503
theorem B3219509 : Blo 2145435 3219509 := bbase (se 5 (by rfl) ⟨150914, by rfl⟩ : syracuseStep 3219509 = 301829) (by norm_num)
theorem B2146339 : Blo 2145435 2146339 := bstep (se 1 (by rfl) ⟨1609754, by rfl⟩ : syracuseStep 2146339 = 3219509) B3219509
theorem B5432933 : Blo 2145435 5432933 := bbase (se 4 (by rfl) ⟨509337, by rfl⟩ : syracuseStep 5432933 = 1018675) (by norm_num)
theorem B3621955 : Blo 2145435 3621955 := bstep (se 1 (by rfl) ⟨2716466, by rfl⟩ : syracuseStep 3621955 = 5432933) B5432933
theorem B4829273 : Blo 2145435 4829273 := bstep (se 2 (by rfl) ⟨1810977, by rfl⟩ : syracuseStep 4829273 = 3621955) B3621955
theorem B3219515 : Blo 2145435 3219515 := bstep (se 1 (by rfl) ⟨2414636, by rfl⟩ : syracuseStep 3219515 = 4829273) B4829273
theorem B2146343 : Blo 2145435 2146343 := bstep (se 1 (by rfl) ⟨1609757, by rfl⟩ : syracuseStep 2146343 = 3219515) B3219515
theorem B2414641 : Blo 2145435 2414641 := bbase (se 2 (by rfl) ⟨905490, by rfl⟩ : syracuseStep 2414641 = 1810981) (by norm_num)
theorem B3219521 : Blo 2145435 3219521 := bstep (se 2 (by rfl) ⟨1207320, by rfl⟩ : syracuseStep 3219521 = 2414641) B2414641
theorem B2146347 : Blo 2145435 2146347 := bstep (se 1 (by rfl) ⟨1609760, by rfl⟩ : syracuseStep 2146347 = 3219521) B3219521
theorem B3867797 : Blo 2145435 3867797 := bbase (se 6 (by rfl) ⟨90651, by rfl⟩ : syracuseStep 3867797 = 181303) (by norm_num)
theorem B10314125 : Blo 2145435 10314125 := bstep (se 3 (by rfl) ⟨1933898, by rfl⟩ : syracuseStep 10314125 = 3867797) B3867797
theorem B6876083 : Blo 2145435 6876083 := bstep (se 1 (by rfl) ⟨5157062, by rfl⟩ : syracuseStep 6876083 = 10314125) B10314125
theorem B4584055 : Blo 2145435 4584055 := bstep (se 1 (by rfl) ⟨3438041, by rfl⟩ : syracuseStep 4584055 = 6876083) B6876083
theorem B6112073 : Blo 2145435 6112073 := bstep (se 2 (by rfl) ⟨2292027, by rfl⟩ : syracuseStep 6112073 = 4584055) B4584055
theorem B4074715 : Blo 2145435 4074715 := bstep (se 1 (by rfl) ⟨3056036, by rfl⟩ : syracuseStep 4074715 = 6112073) B6112073
theorem B5432953 : Blo 2145435 5432953 := bstep (se 2 (by rfl) ⟨2037357, by rfl⟩ : syracuseStep 5432953 = 4074715) B4074715
theorem B7243937 : Blo 2145435 7243937 := bstep (se 2 (by rfl) ⟨2716476, by rfl⟩ : syracuseStep 7243937 = 5432953) B5432953
theorem B4829291 : Blo 2145435 4829291 := bstep (se 1 (by rfl) ⟨3621968, by rfl⟩ : syracuseStep 4829291 = 7243937) B7243937
theorem B3219527 : Blo 2145435 3219527 := bstep (se 1 (by rfl) ⟨2414645, by rfl⟩ : syracuseStep 3219527 = 4829291) B4829291
theorem B2146351 : Blo 2145435 2146351 := bstep (se 1 (by rfl) ⟨1609763, by rfl⟩ : syracuseStep 2146351 = 3219527) B3219527
theorem B3219533 : Blo 2145435 3219533 := bbase (se 3 (by rfl) ⟨603662, by rfl⟩ : syracuseStep 3219533 = 1207325) (by norm_num)
theorem B2146355 : Blo 2145435 2146355 := bstep (se 1 (by rfl) ⟨1609766, by rfl⟩ : syracuseStep 2146355 = 3219533) B3219533
theorem B4829309 : Blo 2145435 4829309 := bbase (se 3 (by rfl) ⟨905495, by rfl⟩ : syracuseStep 4829309 = 1810991) (by norm_num)
theorem B3219539 : Blo 2145435 3219539 := bstep (se 1 (by rfl) ⟨2414654, by rfl⟩ : syracuseStep 3219539 = 4829309) B4829309
theorem B2146359 : Blo 2145435 2146359 := bstep (se 1 (by rfl) ⟨1609769, by rfl⟩ : syracuseStep 2146359 = 3219539) B3219539
theorem B3621989 : Blo 2145435 3621989 := bbase (se 4 (by rfl) ⟨339561, by rfl⟩ : syracuseStep 3621989 = 679123) (by norm_num)
theorem B2414659 : Blo 2145435 2414659 := bstep (se 1 (by rfl) ⟨1810994, by rfl⟩ : syracuseStep 2414659 = 3621989) B3621989
theorem B3219545 : Blo 2145435 3219545 := bstep (se 2 (by rfl) ⟨1207329, by rfl⟩ : syracuseStep 3219545 = 2414659) B2414659
theorem B2146363 : Blo 2145435 2146363 := bstep (se 1 (by rfl) ⟨1609772, by rfl⟩ : syracuseStep 2146363 = 3219545) B3219545
theorem B5157101 : Blo 2145435 5157101 := bbase (se 3 (by rfl) ⟨966956, by rfl⟩ : syracuseStep 5157101 = 1933913) (by norm_num)
theorem B3438067 : Blo 2145435 3438067 := bstep (se 1 (by rfl) ⟨2578550, by rfl⟩ : syracuseStep 3438067 = 5157101) B5157101
theorem B4584089 : Blo 2145435 4584089 := bstep (se 2 (by rfl) ⟨1719033, by rfl⟩ : syracuseStep 4584089 = 3438067) B3438067
theorem B3056059 : Blo 2145435 3056059 := bstep (se 1 (by rfl) ⟨2292044, by rfl⟩ : syracuseStep 3056059 = 4584089) B4584089
theorem B16298981 : Blo 2145435 16298981 := bstep (se 4 (by rfl) ⟨1528029, by rfl⟩ : syracuseStep 16298981 = 3056059) B3056059
theorem B10865987 : Blo 2145435 10865987 := bstep (se 1 (by rfl) ⟨8149490, by rfl⟩ : syracuseStep 10865987 = 16298981) B16298981
theorem B7243991 : Blo 2145435 7243991 := bstep (se 1 (by rfl) ⟨5432993, by rfl⟩ : syracuseStep 7243991 = 10865987) B10865987
theorem B4829327 : Blo 2145435 4829327 := bstep (se 1 (by rfl) ⟨3621995, by rfl⟩ : syracuseStep 4829327 = 7243991) B7243991
theorem B3219551 : Blo 2145435 3219551 := bstep (se 1 (by rfl) ⟨2414663, by rfl⟩ : syracuseStep 3219551 = 4829327) B4829327
theorem B2146367 : Blo 2145435 2146367 := bstep (se 1 (by rfl) ⟨1609775, by rfl⟩ : syracuseStep 2146367 = 3219551) B3219551
theorem B3219557 : Blo 2145435 3219557 := bbase (se 4 (by rfl) ⟨301833, by rfl⟩ : syracuseStep 3219557 = 603667) (by norm_num)
theorem B2146371 : Blo 2145435 2146371 := bstep (se 1 (by rfl) ⟨1609778, by rfl⟩ : syracuseStep 2146371 = 3219557) B3219557
theorem B2175661 : Blo 2145435 2175661 := bbase (se 3 (by rfl) ⟨407936, by rfl⟩ : syracuseStep 2175661 = 815873) (by norm_num)
theorem B2900881 : Blo 2145435 2900881 := bstep (se 2 (by rfl) ⟨1087830, by rfl⟩ : syracuseStep 2900881 = 2175661) B2175661
theorem B3867841 : Blo 2145435 3867841 := bstep (se 2 (by rfl) ⟨1450440, by rfl⟩ : syracuseStep 3867841 = 2900881) B2900881
theorem B5157121 : Blo 2145435 5157121 := bstep (se 2 (by rfl) ⟨1933920, by rfl⟩ : syracuseStep 5157121 = 3867841) B3867841
theorem B6876161 : Blo 2145435 6876161 := bstep (se 2 (by rfl) ⟨2578560, by rfl⟩ : syracuseStep 6876161 = 5157121) B5157121
theorem B4584107 : Blo 2145435 4584107 := bstep (se 1 (by rfl) ⟨3438080, by rfl⟩ : syracuseStep 4584107 = 6876161) B6876161
theorem B3056071 : Blo 2145435 3056071 := bstep (se 1 (by rfl) ⟨2292053, by rfl⟩ : syracuseStep 3056071 = 4584107) B4584107
theorem B4074761 : Blo 2145435 4074761 := bstep (se 2 (by rfl) ⟨1528035, by rfl⟩ : syracuseStep 4074761 = 3056071) B3056071
theorem B2716507 : Blo 2145435 2716507 := bstep (se 1 (by rfl) ⟨2037380, by rfl⟩ : syracuseStep 2716507 = 4074761) B4074761
theorem B3622009 : Blo 2145435 3622009 := bstep (se 2 (by rfl) ⟨1358253, by rfl⟩ : syracuseStep 3622009 = 2716507) B2716507
theorem B4829345 : Blo 2145435 4829345 := bstep (se 2 (by rfl) ⟨1811004, by rfl⟩ : syracuseStep 4829345 = 3622009) B3622009
theorem B3219563 : Blo 2145435 3219563 := bstep (se 1 (by rfl) ⟨2414672, by rfl⟩ : syracuseStep 3219563 = 4829345) B4829345
theorem B2146375 : Blo 2145435 2146375 := bstep (se 1 (by rfl) ⟨1609781, by rfl⟩ : syracuseStep 2146375 = 3219563) B3219563
theorem B2414677 : Blo 2145435 2414677 := bbase (se 8 (by rfl) ⟨14148, by rfl⟩ : syracuseStep 2414677 = 28297) (by norm_num)
theorem B3219569 : Blo 2145435 3219569 := bstep (se 2 (by rfl) ⟨1207338, by rfl⟩ : syracuseStep 3219569 = 2414677) B2414677
theorem B2146379 : Blo 2145435 2146379 := bstep (se 1 (by rfl) ⟨1609784, by rfl⟩ : syracuseStep 2146379 = 3219569) B3219569
theorem B2716517 : Blo 2145435 2716517 := bbase (se 4 (by rfl) ⟨254673, by rfl⟩ : syracuseStep 2716517 = 509347) (by norm_num)
theorem B7244045 : Blo 2145435 7244045 := bstep (se 3 (by rfl) ⟨1358258, by rfl⟩ : syracuseStep 7244045 = 2716517) B2716517
theorem B4829363 : Blo 2145435 4829363 := bstep (se 1 (by rfl) ⟨3622022, by rfl⟩ : syracuseStep 4829363 = 7244045) B7244045
theorem B3219575 : Blo 2145435 3219575 := bstep (se 1 (by rfl) ⟨2414681, by rfl⟩ : syracuseStep 3219575 = 4829363) B4829363
theorem B2146383 : Blo 2145435 2146383 := bstep (se 1 (by rfl) ⟨1609787, by rfl⟩ : syracuseStep 2146383 = 3219575) B3219575
theorem B3219581 : Blo 2145435 3219581 := bbase (se 3 (by rfl) ⟨603671, by rfl⟩ : syracuseStep 3219581 = 1207343) (by norm_num)
theorem B2146387 : Blo 2145435 2146387 := bstep (se 1 (by rfl) ⟨1609790, by rfl⟩ : syracuseStep 2146387 = 3219581) B3219581
theorem B4829381 : Blo 2145435 4829381 := bbase (se 4 (by rfl) ⟨452754, by rfl⟩ : syracuseStep 4829381 = 905509) (by norm_num)
theorem B3219587 : Blo 2145435 3219587 := bstep (se 1 (by rfl) ⟨2414690, by rfl⟩ : syracuseStep 3219587 = 4829381) B4829381
theorem B2146391 : Blo 2145435 2146391 := bstep (se 1 (by rfl) ⟨1609793, by rfl⟩ : syracuseStep 2146391 = 3219587) B3219587
theorem B2447641 : Blo 2145435 2447641 := bbase (se 2 (by rfl) ⟨917865, by rfl⟩ : syracuseStep 2447641 = 1835731) (by norm_num)
theorem B13054085 : Blo 2145435 13054085 := bstep (se 4 (by rfl) ⟨1223820, by rfl⟩ : syracuseStep 13054085 = 2447641) B2447641
theorem B8702723 : Blo 2145435 8702723 := bstep (se 1 (by rfl) ⟨6527042, by rfl⟩ : syracuseStep 8702723 = 13054085) B13054085
theorem B5801815 : Blo 2145435 5801815 := bstep (se 1 (by rfl) ⟨4351361, by rfl⟩ : syracuseStep 5801815 = 8702723) B8702723
theorem B7735753 : Blo 2145435 7735753 := bstep (se 2 (by rfl) ⟨2900907, by rfl⟩ : syracuseStep 7735753 = 5801815) B5801815
theorem B10314337 : Blo 2145435 10314337 := bstep (se 2 (by rfl) ⟨3867876, by rfl⟩ : syracuseStep 10314337 = 7735753) B7735753
theorem B13752449 : Blo 2145435 13752449 := bstep (se 2 (by rfl) ⟨5157168, by rfl⟩ : syracuseStep 13752449 = 10314337) B10314337
theorem B9168299 : Blo 2145435 9168299 := bstep (se 1 (by rfl) ⟨6876224, by rfl⟩ : syracuseStep 9168299 = 13752449) B13752449
theorem B6112199 : Blo 2145435 6112199 := bstep (se 1 (by rfl) ⟨4584149, by rfl⟩ : syracuseStep 6112199 = 9168299) B9168299
theorem B4074799 : Blo 2145435 4074799 := bstep (se 1 (by rfl) ⟨3056099, by rfl⟩ : syracuseStep 4074799 = 6112199) B6112199
theorem B5433065 : Blo 2145435 5433065 := bstep (se 2 (by rfl) ⟨2037399, by rfl⟩ : syracuseStep 5433065 = 4074799) B4074799
theorem B3622043 : Blo 2145435 3622043 := bstep (se 1 (by rfl) ⟨2716532, by rfl⟩ : syracuseStep 3622043 = 5433065) B5433065
theorem B2414695 : Blo 2145435 2414695 := bstep (se 1 (by rfl) ⟨1811021, by rfl⟩ : syracuseStep 2414695 = 3622043) B3622043
theorem B3219593 : Blo 2145435 3219593 := bstep (se 2 (by rfl) ⟨1207347, by rfl⟩ : syracuseStep 3219593 = 2414695) B2414695
theorem B2146395 : Blo 2145435 2146395 := bstep (se 1 (by rfl) ⟨1609796, by rfl⟩ : syracuseStep 2146395 = 3219593) B3219593
theorem B10866149 : Blo 2145435 10866149 := bbase (se 4 (by rfl) ⟨1018701, by rfl⟩ : syracuseStep 10866149 = 2037403) (by norm_num)
theorem B7244099 : Blo 2145435 7244099 := bstep (se 1 (by rfl) ⟨5433074, by rfl⟩ : syracuseStep 7244099 = 10866149) B10866149
theorem B4829399 : Blo 2145435 4829399 := bstep (se 1 (by rfl) ⟨3622049, by rfl⟩ : syracuseStep 4829399 = 7244099) B7244099
theorem B3219599 : Blo 2145435 3219599 := bstep (se 1 (by rfl) ⟨2414699, by rfl⟩ : syracuseStep 3219599 = 4829399) B4829399
theorem B2146399 : Blo 2145435 2146399 := bstep (se 1 (by rfl) ⟨1609799, by rfl⟩ : syracuseStep 2146399 = 3219599) B3219599
theorem B3219605 : Blo 2145435 3219605 := bbase (se 6 (by rfl) ⟨75459, by rfl⟩ : syracuseStep 3219605 = 150919) (by norm_num)
theorem B2146403 : Blo 2145435 2146403 := bstep (se 1 (by rfl) ⟨1609802, by rfl⟩ : syracuseStep 2146403 = 3219605) B3219605
theorem B5157197 : Blo 2145435 5157197 := bbase (se 3 (by rfl) ⟨966974, by rfl⟩ : syracuseStep 5157197 = 1933949) (by norm_num)
theorem B3438131 : Blo 2145435 3438131 := bstep (se 1 (by rfl) ⟨2578598, by rfl⟩ : syracuseStep 3438131 = 5157197) B5157197
theorem B9168349 : Blo 2145435 9168349 := bstep (se 3 (by rfl) ⟨1719065, by rfl⟩ : syracuseStep 9168349 = 3438131) B3438131
theorem B12224465 : Blo 2145435 12224465 := bstep (se 2 (by rfl) ⟨4584174, by rfl⟩ : syracuseStep 12224465 = 9168349) B9168349
theorem B8149643 : Blo 2145435 8149643 := bstep (se 1 (by rfl) ⟨6112232, by rfl⟩ : syracuseStep 8149643 = 12224465) B12224465
theorem B5433095 : Blo 2145435 5433095 := bstep (se 1 (by rfl) ⟨4074821, by rfl⟩ : syracuseStep 5433095 = 8149643) B8149643
theorem B3622063 : Blo 2145435 3622063 := bstep (se 1 (by rfl) ⟨2716547, by rfl⟩ : syracuseStep 3622063 = 5433095) B5433095
theorem B4829417 : Blo 2145435 4829417 := bstep (se 2 (by rfl) ⟨1811031, by rfl⟩ : syracuseStep 4829417 = 3622063) B3622063
theorem B3219611 : Blo 2145435 3219611 := bstep (se 1 (by rfl) ⟨2414708, by rfl⟩ : syracuseStep 3219611 = 4829417) B4829417
theorem B2146407 : Blo 2145435 2146407 := bstep (se 1 (by rfl) ⟨1609805, by rfl⟩ : syracuseStep 2146407 = 3219611) B3219611
theorem B2414713 : Blo 2145435 2414713 := bbase (se 2 (by rfl) ⟨905517, by rfl⟩ : syracuseStep 2414713 = 1811035) (by norm_num)
theorem B3219617 : Blo 2145435 3219617 := bstep (se 2 (by rfl) ⟨1207356, by rfl⟩ : syracuseStep 3219617 = 2414713) B2414713
theorem B2146411 : Blo 2145435 2146411 := bstep (se 1 (by rfl) ⟨1609808, by rfl⟩ : syracuseStep 2146411 = 3219617) B3219617
theorem B7443173 : Blo 2145435 7443173 := bbase (se 4 (by rfl) ⟨697797, by rfl⟩ : syracuseStep 7443173 = 1395595) (by norm_num)
theorem B4962115 : Blo 2145435 4962115 := bstep (se 1 (by rfl) ⟨3721586, by rfl⟩ : syracuseStep 4962115 = 7443173) B7443173
theorem B6616153 : Blo 2145435 6616153 := bstep (se 2 (by rfl) ⟨2481057, by rfl⟩ : syracuseStep 6616153 = 4962115) B4962115
theorem B8821537 : Blo 2145435 8821537 := bstep (se 2 (by rfl) ⟨3308076, by rfl⟩ : syracuseStep 8821537 = 6616153) B6616153
theorem B47048197 : Blo 2145435 47048197 := bstep (se 4 (by rfl) ⟨4410768, by rfl⟩ : syracuseStep 47048197 = 8821537) B8821537
theorem B62730929 : Blo 2145435 62730929 := bstep (se 2 (by rfl) ⟨23524098, by rfl⟩ : syracuseStep 62730929 = 47048197) B47048197
theorem B41820619 : Blo 2145435 41820619 := bstep (se 1 (by rfl) ⟨31365464, by rfl⟩ : syracuseStep 41820619 = 62730929) B62730929
theorem B55760825 : Blo 2145435 55760825 := bstep (se 2 (by rfl) ⟨20910309, by rfl⟩ : syracuseStep 55760825 = 41820619) B41820619
theorem B148695533 : Blo 2145435 148695533 := bstep (se 3 (by rfl) ⟨27880412, by rfl⟩ : syracuseStep 148695533 = 55760825) B55760825
theorem B99130355 : Blo 2145435 99130355 := bstep (se 1 (by rfl) ⟨74347766, by rfl⟩ : syracuseStep 99130355 = 148695533) B148695533
theorem B66086903 : Blo 2145435 66086903 := bstep (se 1 (by rfl) ⟨49565177, by rfl⟩ : syracuseStep 66086903 = 99130355) B99130355
theorem B44057935 : Blo 2145435 44057935 := bstep (se 1 (by rfl) ⟨33043451, by rfl⟩ : syracuseStep 44057935 = 66086903) B66086903
theorem B234975653 : Blo 2145435 234975653 := bstep (se 4 (by rfl) ⟨22028967, by rfl⟩ : syracuseStep 234975653 = 44057935) B44057935
theorem B156650435 : Blo 2145435 156650435 := bstep (se 1 (by rfl) ⟨117487826, by rfl⟩ : syracuseStep 156650435 = 234975653) B234975653
theorem B104433623 : Blo 2145435 104433623 := bstep (se 1 (by rfl) ⟨78325217, by rfl⟩ : syracuseStep 104433623 = 156650435) B156650435
theorem B69622415 : Blo 2145435 69622415 := bstep (se 1 (by rfl) ⟨52216811, by rfl⟩ : syracuseStep 69622415 = 104433623) B104433623
theorem B46414943 : Blo 2145435 46414943 := bstep (se 1 (by rfl) ⟨34811207, by rfl⟩ : syracuseStep 46414943 = 69622415) B69622415
theorem B30943295 : Blo 2145435 30943295 := bstep (se 1 (by rfl) ⟨23207471, by rfl⟩ : syracuseStep 30943295 = 46414943) B46414943
theorem B20628863 : Blo 2145435 20628863 := bstep (se 1 (by rfl) ⟨15471647, by rfl⟩ : syracuseStep 20628863 = 30943295) B30943295
theorem B13752575 : Blo 2145435 13752575 := bstep (se 1 (by rfl) ⟨10314431, by rfl⟩ : syracuseStep 13752575 = 20628863) B20628863
theorem B9168383 : Blo 2145435 9168383 := bstep (se 1 (by rfl) ⟨6876287, by rfl⟩ : syracuseStep 9168383 = 13752575) B13752575
theorem B6112255 : Blo 2145435 6112255 := bstep (se 1 (by rfl) ⟨4584191, by rfl⟩ : syracuseStep 6112255 = 9168383) B9168383
theorem B8149673 : Blo 2145435 8149673 := bstep (se 2 (by rfl) ⟨3056127, by rfl⟩ : syracuseStep 8149673 = 6112255) B6112255
theorem B5433115 : Blo 2145435 5433115 := bstep (se 1 (by rfl) ⟨4074836, by rfl⟩ : syracuseStep 5433115 = 8149673) B8149673
theorem B7244153 : Blo 2145435 7244153 := bstep (se 2 (by rfl) ⟨2716557, by rfl⟩ : syracuseStep 7244153 = 5433115) B5433115
theorem B4829435 : Blo 2145435 4829435 := bstep (se 1 (by rfl) ⟨3622076, by rfl⟩ : syracuseStep 4829435 = 7244153) B7244153
theorem B3219623 : Blo 2145435 3219623 := bstep (se 1 (by rfl) ⟨2414717, by rfl⟩ : syracuseStep 3219623 = 4829435) B4829435
theorem B2146415 : Blo 2145435 2146415 := bstep (se 1 (by rfl) ⟨1609811, by rfl⟩ : syracuseStep 2146415 = 3219623) B3219623
theorem B3219629 : Blo 2145435 3219629 := bbase (se 3 (by rfl) ⟨603680, by rfl⟩ : syracuseStep 3219629 = 1207361) (by norm_num)
theorem B2146419 : Blo 2145435 2146419 := bstep (se 1 (by rfl) ⟨1609814, by rfl⟩ : syracuseStep 2146419 = 3219629) B3219629
theorem B4829453 : Blo 2145435 4829453 := bbase (se 3 (by rfl) ⟨905522, by rfl⟩ : syracuseStep 4829453 = 1811045) (by norm_num)
theorem B3219635 : Blo 2145435 3219635 := bstep (se 1 (by rfl) ⟨2414726, by rfl⟩ : syracuseStep 3219635 = 4829453) B4829453
theorem B2146423 : Blo 2145435 2146423 := bstep (se 1 (by rfl) ⟨1609817, by rfl⟩ : syracuseStep 2146423 = 3219635) B3219635
theorem B2716573 : Blo 2145435 2716573 := bbase (se 3 (by rfl) ⟨509357, by rfl⟩ : syracuseStep 2716573 = 1018715) (by norm_num)
theorem B3622097 : Blo 2145435 3622097 := bstep (se 2 (by rfl) ⟨1358286, by rfl⟩ : syracuseStep 3622097 = 2716573) B2716573
theorem B2414731 : Blo 2145435 2414731 := bstep (se 1 (by rfl) ⟨1811048, by rfl⟩ : syracuseStep 2414731 = 3622097) B3622097
theorem B3219641 : Blo 2145435 3219641 := bstep (se 2 (by rfl) ⟨1207365, by rfl⟩ : syracuseStep 3219641 = 2414731) B2414731
theorem B2146427 : Blo 2145435 2146427 := bstep (se 1 (by rfl) ⟨1609820, by rfl⟩ : syracuseStep 2146427 = 3219641) B3219641
theorem B3867941 : Blo 2145435 3867941 := bbase (se 4 (by rfl) ⟨362619, by rfl⟩ : syracuseStep 3867941 = 725239) (by norm_num)
theorem B2578627 : Blo 2145435 2578627 := bstep (se 1 (by rfl) ⟨1933970, by rfl⟩ : syracuseStep 2578627 = 3867941) B3867941
theorem B3438169 : Blo 2145435 3438169 := bstep (se 2 (by rfl) ⟨1289313, by rfl⟩ : syracuseStep 3438169 = 2578627) B2578627
theorem B18336901 : Blo 2145435 18336901 := bstep (se 4 (by rfl) ⟨1719084, by rfl⟩ : syracuseStep 18336901 = 3438169) B3438169
theorem B24449201 : Blo 2145435 24449201 := bstep (se 2 (by rfl) ⟨9168450, by rfl⟩ : syracuseStep 24449201 = 18336901) B18336901
theorem B16299467 : Blo 2145435 16299467 := bstep (se 1 (by rfl) ⟨12224600, by rfl⟩ : syracuseStep 16299467 = 24449201) B24449201
theorem B10866311 : Blo 2145435 10866311 := bstep (se 1 (by rfl) ⟨8149733, by rfl⟩ : syracuseStep 10866311 = 16299467) B16299467
theorem B7244207 : Blo 2145435 7244207 := bstep (se 1 (by rfl) ⟨5433155, by rfl⟩ : syracuseStep 7244207 = 10866311) B10866311
theorem B4829471 : Blo 2145435 4829471 := bstep (se 1 (by rfl) ⟨3622103, by rfl⟩ : syracuseStep 4829471 = 7244207) B7244207
theorem B3219647 : Blo 2145435 3219647 := bstep (se 1 (by rfl) ⟨2414735, by rfl⟩ : syracuseStep 3219647 = 4829471) B4829471
theorem B2146431 : Blo 2145435 2146431 := bstep (se 1 (by rfl) ⟨1609823, by rfl⟩ : syracuseStep 2146431 = 3219647) B3219647
theorem B3219653 : Blo 2145435 3219653 := bbase (se 4 (by rfl) ⟨301842, by rfl⟩ : syracuseStep 3219653 = 603685) (by norm_num)
theorem B2146435 : Blo 2145435 2146435 := bstep (se 1 (by rfl) ⟨1609826, by rfl⟩ : syracuseStep 2146435 = 3219653) B3219653
theorem B3622117 : Blo 2145435 3622117 := bbase (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) (by norm_num)
theorem B4829489 : Blo 2145435 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B3219659 : Blo 2145435 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B2146439 : Blo 2145435 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B2414749 : Blo 2145435 2414749 := bbase (se 3 (by rfl) ⟨452765, by rfl⟩ : syracuseStep 2414749 = 905531) (by norm_num)
theorem B3219665 : Blo 2145435 3219665 := bstep (se 2 (by rfl) ⟨1207374, by rfl⟩ : syracuseStep 3219665 = 2414749) B2414749
theorem B2146443 : Blo 2145435 2146443 := bstep (se 1 (by rfl) ⟨1609832, by rfl⟩ : syracuseStep 2146443 = 3219665) B3219665
theorem B7244261 : Blo 2145435 7244261 := bbase (se 4 (by rfl) ⟨679149, by rfl⟩ : syracuseStep 7244261 = 1358299) (by norm_num)
theorem B4829507 : Blo 2145435 4829507 := bstep (se 1 (by rfl) ⟨3622130, by rfl⟩ : syracuseStep 4829507 = 7244261) B7244261
theorem B3219671 : Blo 2145435 3219671 := bstep (se 1 (by rfl) ⟨2414753, by rfl⟩ : syracuseStep 3219671 = 4829507) B4829507
theorem B2146447 : Blo 2145435 2146447 := bstep (se 1 (by rfl) ⟨1609835, by rfl⟩ : syracuseStep 2146447 = 3219671) B3219671
theorem B3219677 : Blo 2145435 3219677 := bbase (se 3 (by rfl) ⟨603689, by rfl⟩ : syracuseStep 3219677 = 1207379) (by norm_num)
theorem B2146451 : Blo 2145435 2146451 := bstep (se 1 (by rfl) ⟨1609838, by rfl⟩ : syracuseStep 2146451 = 3219677) B3219677
theorem B4829525 : Blo 2145435 4829525 := bbase (se 10 (by rfl) ⟨7074, by rfl⟩ : syracuseStep 4829525 = 14149) (by norm_num)
theorem B3219683 : Blo 2145435 3219683 := bstep (se 1 (by rfl) ⟨2414762, by rfl⟩ : syracuseStep 3219683 = 4829525) B4829525
theorem B2146455 : Blo 2145435 2146455 := bstep (se 1 (by rfl) ⟨1609841, by rfl⟩ : syracuseStep 2146455 = 3219683) B3219683
theorem B5801989 : Blo 2145435 5801989 := bbase (se 4 (by rfl) ⟨543936, by rfl⟩ : syracuseStep 5801989 = 1087873) (by norm_num)
theorem B7735985 : Blo 2145435 7735985 := bstep (se 2 (by rfl) ⟨2900994, by rfl⟩ : syracuseStep 7735985 = 5801989) B5801989
theorem B5157323 : Blo 2145435 5157323 := bstep (se 1 (by rfl) ⟨3867992, by rfl⟩ : syracuseStep 5157323 = 7735985) B7735985
theorem B3438215 : Blo 2145435 3438215 := bstep (se 1 (by rfl) ⟨2578661, by rfl⟩ : syracuseStep 3438215 = 5157323) B5157323
theorem B2292143 : Blo 2145435 2292143 := bstep (se 1 (by rfl) ⟨1719107, by rfl⟩ : syracuseStep 2292143 = 3438215) B3438215
theorem B6112381 : Blo 2145435 6112381 := bstep (se 3 (by rfl) ⟨1146071, by rfl⟩ : syracuseStep 6112381 = 2292143) B2292143
theorem B8149841 : Blo 2145435 8149841 := bstep (se 2 (by rfl) ⟨3056190, by rfl⟩ : syracuseStep 8149841 = 6112381) B6112381
theorem B5433227 : Blo 2145435 5433227 := bstep (se 1 (by rfl) ⟨4074920, by rfl⟩ : syracuseStep 5433227 = 8149841) B8149841
theorem B3622151 : Blo 2145435 3622151 := bstep (se 1 (by rfl) ⟨2716613, by rfl⟩ : syracuseStep 3622151 = 5433227) B5433227
theorem B2414767 : Blo 2145435 2414767 := bstep (se 1 (by rfl) ⟨1811075, by rfl⟩ : syracuseStep 2414767 = 3622151) B3622151
theorem B3219689 : Blo 2145435 3219689 := bstep (se 2 (by rfl) ⟨1207383, by rfl⟩ : syracuseStep 3219689 = 2414767) B2414767
theorem B2146459 : Blo 2145435 2146459 := bstep (se 1 (by rfl) ⟨1609844, by rfl⟩ : syracuseStep 2146459 = 3219689) B3219689
theorem B41258645 : Blo 2145435 41258645 := bbase (se 6 (by rfl) ⟨966999, by rfl⟩ : syracuseStep 41258645 = 1933999) (by norm_num)
theorem B27505763 : Blo 2145435 27505763 := bstep (se 1 (by rfl) ⟨20629322, by rfl⟩ : syracuseStep 27505763 = 41258645) B41258645
theorem B18337175 : Blo 2145435 18337175 := bstep (se 1 (by rfl) ⟨13752881, by rfl⟩ : syracuseStep 18337175 = 27505763) B27505763
theorem B12224783 : Blo 2145435 12224783 := bstep (se 1 (by rfl) ⟨9168587, by rfl⟩ : syracuseStep 12224783 = 18337175) B18337175
theorem B8149855 : Blo 2145435 8149855 := bstep (se 1 (by rfl) ⟨6112391, by rfl⟩ : syracuseStep 8149855 = 12224783) B12224783
theorem B10866473 : Blo 2145435 10866473 := bstep (se 2 (by rfl) ⟨4074927, by rfl⟩ : syracuseStep 10866473 = 8149855) B8149855
theorem B7244315 : Blo 2145435 7244315 := bstep (se 1 (by rfl) ⟨5433236, by rfl⟩ : syracuseStep 7244315 = 10866473) B10866473
theorem B4829543 : Blo 2145435 4829543 := bstep (se 1 (by rfl) ⟨3622157, by rfl⟩ : syracuseStep 4829543 = 7244315) B7244315
theorem B3219695 : Blo 2145435 3219695 := bstep (se 1 (by rfl) ⟨2414771, by rfl⟩ : syracuseStep 3219695 = 4829543) B4829543
theorem B2146463 : Blo 2145435 2146463 := bstep (se 1 (by rfl) ⟨1609847, by rfl⟩ : syracuseStep 2146463 = 3219695) B3219695
theorem B3219701 : Blo 2145435 3219701 := bbase (se 5 (by rfl) ⟨150923, by rfl⟩ : syracuseStep 3219701 = 301847) (by norm_num)
theorem B2146467 : Blo 2145435 2146467 := bstep (se 1 (by rfl) ⟨1609850, by rfl⟩ : syracuseStep 2146467 = 3219701) B3219701
theorem B41821717 : Blo 2145435 41821717 := bbase (se 6 (by rfl) ⟨980196, by rfl⟩ : syracuseStep 41821717 = 1960393) (by norm_num)
theorem B55762289 : Blo 2145435 55762289 := bstep (se 2 (by rfl) ⟨20910858, by rfl⟩ : syracuseStep 55762289 = 41821717) B41821717
theorem B37174859 : Blo 2145435 37174859 := bstep (se 1 (by rfl) ⟨27881144, by rfl⟩ : syracuseStep 37174859 = 55762289) B55762289
theorem B24783239 : Blo 2145435 24783239 := bstep (se 1 (by rfl) ⟨18587429, by rfl⟩ : syracuseStep 24783239 = 37174859) B37174859
theorem B16522159 : Blo 2145435 16522159 := bstep (se 1 (by rfl) ⟨12391619, by rfl⟩ : syracuseStep 16522159 = 24783239) B24783239
theorem B22029545 : Blo 2145435 22029545 := bstep (se 2 (by rfl) ⟨8261079, by rfl⟩ : syracuseStep 22029545 = 16522159) B16522159
theorem B14686363 : Blo 2145435 14686363 := bstep (se 1 (by rfl) ⟨11014772, by rfl⟩ : syracuseStep 14686363 = 22029545) B22029545
theorem B78327269 : Blo 2145435 78327269 := bstep (se 4 (by rfl) ⟨7343181, by rfl⟩ : syracuseStep 78327269 = 14686363) B14686363
theorem B52218179 : Blo 2145435 52218179 := bstep (se 1 (by rfl) ⟨39163634, by rfl⟩ : syracuseStep 52218179 = 78327269) B78327269
theorem B34812119 : Blo 2145435 34812119 := bstep (se 1 (by rfl) ⟨26109089, by rfl⟩ : syracuseStep 34812119 = 52218179) B52218179
theorem B23208079 : Blo 2145435 23208079 := bstep (se 1 (by rfl) ⟨17406059, by rfl⟩ : syracuseStep 23208079 = 34812119) B34812119
theorem B30944105 : Blo 2145435 30944105 := bstep (se 2 (by rfl) ⟨11604039, by rfl⟩ : syracuseStep 30944105 = 23208079) B23208079
theorem B20629403 : Blo 2145435 20629403 := bstep (se 1 (by rfl) ⟨15472052, by rfl⟩ : syracuseStep 20629403 = 30944105) B30944105
theorem B13752935 : Blo 2145435 13752935 := bstep (se 1 (by rfl) ⟨10314701, by rfl⟩ : syracuseStep 13752935 = 20629403) B20629403
theorem B9168623 : Blo 2145435 9168623 := bstep (se 1 (by rfl) ⟨6876467, by rfl⟩ : syracuseStep 9168623 = 13752935) B13752935
theorem B6112415 : Blo 2145435 6112415 := bstep (se 1 (by rfl) ⟨4584311, by rfl⟩ : syracuseStep 6112415 = 9168623) B9168623
theorem B4074943 : Blo 2145435 4074943 := bstep (se 1 (by rfl) ⟨3056207, by rfl⟩ : syracuseStep 4074943 = 6112415) B6112415
theorem B5433257 : Blo 2145435 5433257 := bstep (se 2 (by rfl) ⟨2037471, by rfl⟩ : syracuseStep 5433257 = 4074943) B4074943
theorem B3622171 : Blo 2145435 3622171 := bstep (se 1 (by rfl) ⟨2716628, by rfl⟩ : syracuseStep 3622171 = 5433257) B5433257
theorem B4829561 : Blo 2145435 4829561 := bstep (se 2 (by rfl) ⟨1811085, by rfl⟩ : syracuseStep 4829561 = 3622171) B3622171
theorem B3219707 : Blo 2145435 3219707 := bstep (se 1 (by rfl) ⟨2414780, by rfl⟩ : syracuseStep 3219707 = 4829561) B4829561
theorem B2146471 : Blo 2145435 2146471 := bstep (se 1 (by rfl) ⟨1609853, by rfl⟩ : syracuseStep 2146471 = 3219707) B3219707
theorem B2414785 : Blo 2145435 2414785 := bbase (se 2 (by rfl) ⟨905544, by rfl⟩ : syracuseStep 2414785 = 1811089) (by norm_num)
theorem B3219713 : Blo 2145435 3219713 := bstep (se 2 (by rfl) ⟨1207392, by rfl⟩ : syracuseStep 3219713 = 2414785) B2414785
theorem B2146475 : Blo 2145435 2146475 := bstep (se 1 (by rfl) ⟨1609856, by rfl⟩ : syracuseStep 2146475 = 3219713) B3219713
theorem B5433277 : Blo 2145435 5433277 := bbase (se 3 (by rfl) ⟨1018739, by rfl⟩ : syracuseStep 5433277 = 2037479) (by norm_num)
theorem B7244369 : Blo 2145435 7244369 := bstep (se 2 (by rfl) ⟨2716638, by rfl⟩ : syracuseStep 7244369 = 5433277) B5433277
theorem B4829579 : Blo 2145435 4829579 := bstep (se 1 (by rfl) ⟨3622184, by rfl⟩ : syracuseStep 4829579 = 7244369) B7244369
theorem B3219719 : Blo 2145435 3219719 := bstep (se 1 (by rfl) ⟨2414789, by rfl⟩ : syracuseStep 3219719 = 4829579) B4829579
theorem B2146479 : Blo 2145435 2146479 := bstep (se 1 (by rfl) ⟨1609859, by rfl⟩ : syracuseStep 2146479 = 3219719) B3219719
theorem B3219725 : Blo 2145435 3219725 := bbase (se 3 (by rfl) ⟨603698, by rfl⟩ : syracuseStep 3219725 = 1207397) (by norm_num)
theorem B2146483 : Blo 2145435 2146483 := bstep (se 1 (by rfl) ⟨1609862, by rfl⟩ : syracuseStep 2146483 = 3219725) B3219725
theorem B4829597 : Blo 2145435 4829597 := bbase (se 3 (by rfl) ⟨905549, by rfl⟩ : syracuseStep 4829597 = 1811099) (by norm_num)
theorem B3219731 : Blo 2145435 3219731 := bstep (se 1 (by rfl) ⟨2414798, by rfl⟩ : syracuseStep 3219731 = 4829597) B4829597
theorem B2146487 : Blo 2145435 2146487 := bstep (se 1 (by rfl) ⟨1609865, by rfl⟩ : syracuseStep 2146487 = 3219731) B3219731
theorem B3622205 : Blo 2145435 3622205 := bbase (se 3 (by rfl) ⟨679163, by rfl⟩ : syracuseStep 3622205 = 1358327) (by norm_num)
theorem B2414803 : Blo 2145435 2414803 := bstep (se 1 (by rfl) ⟨1811102, by rfl⟩ : syracuseStep 2414803 = 3622205) B3622205
theorem B3219737 : Blo 2145435 3219737 := bstep (se 2 (by rfl) ⟨1207401, by rfl⟩ : syracuseStep 3219737 = 2414803) B2414803
theorem B2146491 : Blo 2145435 2146491 := bstep (se 1 (by rfl) ⟨1609868, by rfl⟩ : syracuseStep 2146491 = 3219737) B3219737
theorem B2292181 : Blo 2145435 2292181 := bbase (se 7 (by rfl) ⟨26861, by rfl⟩ : syracuseStep 2292181 = 53723) (by norm_num)
theorem B12224965 : Blo 2145435 12224965 := bstep (se 4 (by rfl) ⟨1146090, by rfl⟩ : syracuseStep 12224965 = 2292181) B2292181
theorem B16299953 : Blo 2145435 16299953 := bstep (se 2 (by rfl) ⟨6112482, by rfl⟩ : syracuseStep 16299953 = 12224965) B12224965
theorem B10866635 : Blo 2145435 10866635 := bstep (se 1 (by rfl) ⟨8149976, by rfl⟩ : syracuseStep 10866635 = 16299953) B16299953
theorem B7244423 : Blo 2145435 7244423 := bstep (se 1 (by rfl) ⟨5433317, by rfl⟩ : syracuseStep 7244423 = 10866635) B10866635
theorem B4829615 : Blo 2145435 4829615 := bstep (se 1 (by rfl) ⟨3622211, by rfl⟩ : syracuseStep 4829615 = 7244423) B7244423
theorem B3219743 : Blo 2145435 3219743 := bstep (se 1 (by rfl) ⟨2414807, by rfl⟩ : syracuseStep 3219743 = 4829615) B4829615
theorem B2146495 : Blo 2145435 2146495 := bstep (se 1 (by rfl) ⟨1609871, by rfl⟩ : syracuseStep 2146495 = 3219743) B3219743
theorem B3219749 : Blo 2145435 3219749 := bbase (se 4 (by rfl) ⟨301851, by rfl⟩ : syracuseStep 3219749 = 603703) (by norm_num)
theorem B2146499 : Blo 2145435 2146499 := bstep (se 1 (by rfl) ⟨1609874, by rfl⟩ : syracuseStep 2146499 = 3219749) B3219749
theorem B2716669 : Blo 2145435 2716669 := bbase (se 3 (by rfl) ⟨509375, by rfl⟩ : syracuseStep 2716669 = 1018751) (by norm_num)
theorem B3622225 : Blo 2145435 3622225 := bstep (se 2 (by rfl) ⟨1358334, by rfl⟩ : syracuseStep 3622225 = 2716669) B2716669
theorem B4829633 : Blo 2145435 4829633 := bstep (se 2 (by rfl) ⟨1811112, by rfl⟩ : syracuseStep 4829633 = 3622225) B3622225
theorem B3219755 : Blo 2145435 3219755 := bstep (se 1 (by rfl) ⟨2414816, by rfl⟩ : syracuseStep 3219755 = 4829633) B4829633
theorem B2146503 : Blo 2145435 2146503 := bstep (se 1 (by rfl) ⟨1609877, by rfl⟩ : syracuseStep 2146503 = 3219755) B3219755
theorem B2414821 : Blo 2145435 2414821 := bbase (se 4 (by rfl) ⟨226389, by rfl⟩ : syracuseStep 2414821 = 452779) (by norm_num)
theorem B3219761 : Blo 2145435 3219761 := bstep (se 2 (by rfl) ⟨1207410, by rfl⟩ : syracuseStep 3219761 = 2414821) B2414821
theorem B2146507 : Blo 2145435 2146507 := bstep (se 1 (by rfl) ⟨1609880, by rfl⟩ : syracuseStep 2146507 = 3219761) B3219761
theorem B4584397 : Blo 2145435 4584397 := bbase (se 3 (by rfl) ⟨859574, by rfl⟩ : syracuseStep 4584397 = 1719149) (by norm_num)
theorem B6112529 : Blo 2145435 6112529 := bstep (se 2 (by rfl) ⟨2292198, by rfl⟩ : syracuseStep 6112529 = 4584397) B4584397
theorem B4075019 : Blo 2145435 4075019 := bstep (se 1 (by rfl) ⟨3056264, by rfl⟩ : syracuseStep 4075019 = 6112529) B6112529
theorem B2716679 : Blo 2145435 2716679 := bstep (se 1 (by rfl) ⟨2037509, by rfl⟩ : syracuseStep 2716679 = 4075019) B4075019
theorem B7244477 : Blo 2145435 7244477 := bstep (se 3 (by rfl) ⟨1358339, by rfl⟩ : syracuseStep 7244477 = 2716679) B2716679
theorem B4829651 : Blo 2145435 4829651 := bstep (se 1 (by rfl) ⟨3622238, by rfl⟩ : syracuseStep 4829651 = 7244477) B7244477
theorem B3219767 : Blo 2145435 3219767 := bstep (se 1 (by rfl) ⟨2414825, by rfl⟩ : syracuseStep 3219767 = 4829651) B4829651
theorem B2146511 : Blo 2145435 2146511 := bstep (se 1 (by rfl) ⟨1609883, by rfl⟩ : syracuseStep 2146511 = 3219767) B3219767
theorem B3219773 : Blo 2145435 3219773 := bbase (se 3 (by rfl) ⟨603707, by rfl⟩ : syracuseStep 3219773 = 1207415) (by norm_num)
theorem B2146515 : Blo 2145435 2146515 := bstep (se 1 (by rfl) ⟨1609886, by rfl⟩ : syracuseStep 2146515 = 3219773) B3219773
theorem B4829669 : Blo 2145435 4829669 := bbase (se 4 (by rfl) ⟨452781, by rfl⟩ : syracuseStep 4829669 = 905563) (by norm_num)
theorem B3219779 : Blo 2145435 3219779 := bstep (se 1 (by rfl) ⟨2414834, by rfl⟩ : syracuseStep 3219779 = 4829669) B4829669
theorem B2146519 : Blo 2145435 2146519 := bstep (se 1 (by rfl) ⟨1609889, by rfl⟩ : syracuseStep 2146519 = 3219779) B3219779
theorem B5433389 : Blo 2145435 5433389 := bbase (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) (by norm_num)
theorem B3622259 : Blo 2145435 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B2414839 : Blo 2145435 2414839 := bstep (se 1 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 2414839 = 3622259) B3622259
theorem B3219785 : Blo 2145435 3219785 := bstep (se 2 (by rfl) ⟨1207419, by rfl⟩ : syracuseStep 3219785 = 2414839) B2414839
theorem B2146523 : Blo 2145435 2146523 := bstep (se 1 (by rfl) ⟨1609892, by rfl⟩ : syracuseStep 2146523 = 3219785) B3219785
theorem B6195973 : Blo 2145435 6195973 := bbase (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) (by norm_num)
theorem B8261297 : Blo 2145435 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B5507531 : Blo 2145435 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B3671687 : Blo 2145435 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B9791165 : Blo 2145435 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B26109773 : Blo 2145435 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B17406515 : Blo 2145435 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B11604343 : Blo 2145435 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B15472457 : Blo 2145435 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B10314971 : Blo 2145435 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B6876647 : Blo 2145435 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B4584431 : Blo 2145435 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B3056287 : Blo 2145435 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B4075049 : Blo 2145435 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B10866797 : Blo 2145435 10866797 := bstep (se 3 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 10866797 = 4075049) B4075049
theorem B7244531 : Blo 2145435 7244531 := bstep (se 1 (by rfl) ⟨5433398, by rfl⟩ : syracuseStep 7244531 = 10866797) B10866797
theorem B4829687 : Blo 2145435 4829687 := bstep (se 1 (by rfl) ⟨3622265, by rfl⟩ : syracuseStep 4829687 = 7244531) B7244531
theorem B3219791 : Blo 2145435 3219791 := bstep (se 1 (by rfl) ⟨2414843, by rfl⟩ : syracuseStep 3219791 = 4829687) B4829687
theorem B2146527 : Blo 2145435 2146527 := bstep (se 1 (by rfl) ⟨1609895, by rfl⟩ : syracuseStep 2146527 = 3219791) B3219791
theorem B3219797 : Blo 2145435 3219797 := bbase (se 10 (by rfl) ⟨4716, by rfl⟩ : syracuseStep 3219797 = 9433) (by norm_num)
theorem B2146531 : Blo 2145435 2146531 := bstep (se 1 (by rfl) ⟨1609898, by rfl⟩ : syracuseStep 2146531 = 3219797) B3219797
theorem B6112597 : Blo 2145435 6112597 := bbase (se 12 (by rfl) ⟨2238, by rfl⟩ : syracuseStep 6112597 = 4477) (by norm_num)
theorem B8150129 : Blo 2145435 8150129 := bstep (se 2 (by rfl) ⟨3056298, by rfl⟩ : syracuseStep 8150129 = 6112597) B6112597
theorem B5433419 : Blo 2145435 5433419 := bstep (se 1 (by rfl) ⟨4075064, by rfl⟩ : syracuseStep 5433419 = 8150129) B8150129
theorem B3622279 : Blo 2145435 3622279 := bstep (se 1 (by rfl) ⟨2716709, by rfl⟩ : syracuseStep 3622279 = 5433419) B5433419
theorem B4829705 : Blo 2145435 4829705 := bstep (se 2 (by rfl) ⟨1811139, by rfl⟩ : syracuseStep 4829705 = 3622279) B3622279
theorem B3219803 : Blo 2145435 3219803 := bstep (se 1 (by rfl) ⟨2414852, by rfl⟩ : syracuseStep 3219803 = 4829705) B4829705
theorem B2146535 : Blo 2145435 2146535 := bstep (se 1 (by rfl) ⟨1609901, by rfl⟩ : syracuseStep 2146535 = 3219803) B3219803
theorem B2414857 : Blo 2145435 2414857 := bbase (se 2 (by rfl) ⟨905571, by rfl⟩ : syracuseStep 2414857 = 1811143) (by norm_num)
theorem B3219809 : Blo 2145435 3219809 := bstep (se 2 (by rfl) ⟨1207428, by rfl⟩ : syracuseStep 3219809 = 2414857) B2414857
theorem B2146539 : Blo 2145435 2146539 := bstep (se 1 (by rfl) ⟨1609904, by rfl⟩ : syracuseStep 2146539 = 3219809) B3219809
theorem B4351661 : Blo 2145435 4351661 := bbase (se 3 (by rfl) ⟨815936, by rfl⟩ : syracuseStep 4351661 = 1631873) (by norm_num)
theorem B2901107 : Blo 2145435 2901107 := bstep (se 1 (by rfl) ⟨2175830, by rfl⟩ : syracuseStep 2901107 = 4351661) B4351661
theorem B7736285 : Blo 2145435 7736285 := bstep (se 3 (by rfl) ⟨1450553, by rfl⟩ : syracuseStep 7736285 = 2901107) B2901107
theorem B5157523 : Blo 2145435 5157523 := bstep (se 1 (by rfl) ⟨3868142, by rfl⟩ : syracuseStep 5157523 = 7736285) B7736285
theorem B27506789 : Blo 2145435 27506789 := bstep (se 4 (by rfl) ⟨2578761, by rfl⟩ : syracuseStep 27506789 = 5157523) B5157523
theorem B18337859 : Blo 2145435 18337859 := bstep (se 1 (by rfl) ⟨13753394, by rfl⟩ : syracuseStep 18337859 = 27506789) B27506789
theorem B12225239 : Blo 2145435 12225239 := bstep (se 1 (by rfl) ⟨9168929, by rfl⟩ : syracuseStep 12225239 = 18337859) B18337859
theorem B8150159 : Blo 2145435 8150159 := bstep (se 1 (by rfl) ⟨6112619, by rfl⟩ : syracuseStep 8150159 = 12225239) B12225239
theorem B5433439 : Blo 2145435 5433439 := bstep (se 1 (by rfl) ⟨4075079, by rfl⟩ : syracuseStep 5433439 = 8150159) B8150159
theorem B7244585 : Blo 2145435 7244585 := bstep (se 2 (by rfl) ⟨2716719, by rfl⟩ : syracuseStep 7244585 = 5433439) B5433439
theorem B4829723 : Blo 2145435 4829723 := bstep (se 1 (by rfl) ⟨3622292, by rfl⟩ : syracuseStep 4829723 = 7244585) B7244585
theorem B3219815 : Blo 2145435 3219815 := bstep (se 1 (by rfl) ⟨2414861, by rfl⟩ : syracuseStep 3219815 = 4829723) B4829723
theorem B2146543 : Blo 2145435 2146543 := bstep (se 1 (by rfl) ⟨1609907, by rfl⟩ : syracuseStep 2146543 = 3219815) B3219815
theorem B3219821 : Blo 2145435 3219821 := bbase (se 3 (by rfl) ⟨603716, by rfl⟩ : syracuseStep 3219821 = 1207433) (by norm_num)
theorem B2146547 : Blo 2145435 2146547 := bstep (se 1 (by rfl) ⟨1609910, by rfl⟩ : syracuseStep 2146547 = 3219821) B3219821
theorem B4829741 : Blo 2145435 4829741 := bbase (se 3 (by rfl) ⟨905576, by rfl⟩ : syracuseStep 4829741 = 1811153) (by norm_num)
theorem B3219827 : Blo 2145435 3219827 := bstep (se 1 (by rfl) ⟨2414870, by rfl⟩ : syracuseStep 3219827 = 4829741) B4829741
theorem B2146551 : Blo 2145435 2146551 := bstep (se 1 (by rfl) ⟨1609913, by rfl⟩ : syracuseStep 2146551 = 3219827) B3219827
theorem B3868165 : Blo 2145435 3868165 := bbase (se 4 (by rfl) ⟨362640, by rfl⟩ : syracuseStep 3868165 = 725281) (by norm_num)
theorem B20630213 : Blo 2145435 20630213 := bstep (se 4 (by rfl) ⟨1934082, by rfl⟩ : syracuseStep 20630213 = 3868165) B3868165
theorem B13753475 : Blo 2145435 13753475 := bstep (se 1 (by rfl) ⟨10315106, by rfl⟩ : syracuseStep 13753475 = 20630213) B20630213
theorem B9168983 : Blo 2145435 9168983 := bstep (se 1 (by rfl) ⟨6876737, by rfl⟩ : syracuseStep 9168983 = 13753475) B13753475
theorem B6112655 : Blo 2145435 6112655 := bstep (se 1 (by rfl) ⟨4584491, by rfl⟩ : syracuseStep 6112655 = 9168983) B9168983
theorem B4075103 : Blo 2145435 4075103 := bstep (se 1 (by rfl) ⟨3056327, by rfl⟩ : syracuseStep 4075103 = 6112655) B6112655
theorem B2716735 : Blo 2145435 2716735 := bstep (se 1 (by rfl) ⟨2037551, by rfl⟩ : syracuseStep 2716735 = 4075103) B4075103
theorem B3622313 : Blo 2145435 3622313 := bstep (se 2 (by rfl) ⟨1358367, by rfl⟩ : syracuseStep 3622313 = 2716735) B2716735
theorem B2414875 : Blo 2145435 2414875 := bstep (se 1 (by rfl) ⟨1811156, by rfl⟩ : syracuseStep 2414875 = 3622313) B3622313
theorem B3219833 : Blo 2145435 3219833 := bstep (se 2 (by rfl) ⟨1207437, by rfl⟩ : syracuseStep 3219833 = 2414875) B2414875
theorem B2146555 : Blo 2145435 2146555 := bstep (se 1 (by rfl) ⟨1609916, by rfl⟩ : syracuseStep 2146555 = 3219833) B3219833
theorem B36675989 : Blo 2145435 36675989 := bbase (se 6 (by rfl) ⟨859593, by rfl⟩ : syracuseStep 36675989 = 1719187) (by norm_num)
theorem B24450659 : Blo 2145435 24450659 := bstep (se 1 (by rfl) ⟨18337994, by rfl⟩ : syracuseStep 24450659 = 36675989) B36675989
theorem B16300439 : Blo 2145435 16300439 := bstep (se 1 (by rfl) ⟨12225329, by rfl⟩ : syracuseStep 16300439 = 24450659) B24450659
theorem B10866959 : Blo 2145435 10866959 := bstep (se 1 (by rfl) ⟨8150219, by rfl⟩ : syracuseStep 10866959 = 16300439) B16300439
theorem B7244639 : Blo 2145435 7244639 := bstep (se 1 (by rfl) ⟨5433479, by rfl⟩ : syracuseStep 7244639 = 10866959) B10866959
theorem B4829759 : Blo 2145435 4829759 := bstep (se 1 (by rfl) ⟨3622319, by rfl⟩ : syracuseStep 4829759 = 7244639) B7244639
theorem B3219839 : Blo 2145435 3219839 := bstep (se 1 (by rfl) ⟨2414879, by rfl⟩ : syracuseStep 3219839 = 4829759) B4829759
theorem B2146559 : Blo 2145435 2146559 := bstep (se 1 (by rfl) ⟨1609919, by rfl⟩ : syracuseStep 2146559 = 3219839) B3219839
theorem B3219845 : Blo 2145435 3219845 := bbase (se 4 (by rfl) ⟨301860, by rfl⟩ : syracuseStep 3219845 = 603721) (by norm_num)
theorem B2146563 : Blo 2145435 2146563 := bstep (se 1 (by rfl) ⟨1609922, by rfl⟩ : syracuseStep 2146563 = 3219845) B3219845
theorem B3622333 : Blo 2145435 3622333 := bbase (se 3 (by rfl) ⟨679187, by rfl⟩ : syracuseStep 3622333 = 1358375) (by norm_num)
theorem B4829777 : Blo 2145435 4829777 := bstep (se 2 (by rfl) ⟨1811166, by rfl⟩ : syracuseStep 4829777 = 3622333) B3622333
theorem B3219851 : Blo 2145435 3219851 := bstep (se 1 (by rfl) ⟨2414888, by rfl⟩ : syracuseStep 3219851 = 4829777) B4829777
theorem B2146567 : Blo 2145435 2146567 := bstep (se 1 (by rfl) ⟨1609925, by rfl⟩ : syracuseStep 2146567 = 3219851) B3219851
theorem B2414893 : Blo 2145435 2414893 := bbase (se 3 (by rfl) ⟨452792, by rfl⟩ : syracuseStep 2414893 = 905585) (by norm_num)
theorem B3219857 : Blo 2145435 3219857 := bstep (se 2 (by rfl) ⟨1207446, by rfl⟩ : syracuseStep 3219857 = 2414893) B2414893
theorem B2146571 : Blo 2145435 2146571 := bstep (se 1 (by rfl) ⟨1609928, by rfl⟩ : syracuseStep 2146571 = 3219857) B3219857
theorem B7244693 : Blo 2145435 7244693 := bbase (se 6 (by rfl) ⟨169797, by rfl⟩ : syracuseStep 7244693 = 339595) (by norm_num)
theorem B4829795 : Blo 2145435 4829795 := bstep (se 1 (by rfl) ⟨3622346, by rfl⟩ : syracuseStep 4829795 = 7244693) B7244693
theorem B3219863 : Blo 2145435 3219863 := bstep (se 1 (by rfl) ⟨2414897, by rfl⟩ : syracuseStep 3219863 = 4829795) B4829795
theorem B2146575 : Blo 2145435 2146575 := bstep (se 1 (by rfl) ⟨1609931, by rfl⟩ : syracuseStep 2146575 = 3219863) B3219863
theorem B3219869 : Blo 2145435 3219869 := bbase (se 3 (by rfl) ⟨603725, by rfl⟩ : syracuseStep 3219869 = 1207451) (by norm_num)
theorem B2146579 : Blo 2145435 2146579 := bstep (se 1 (by rfl) ⟨1609934, by rfl⟩ : syracuseStep 2146579 = 3219869) B3219869
theorem B4829813 : Blo 2145435 4829813 := bbase (se 5 (by rfl) ⟨226397, by rfl⟩ : syracuseStep 4829813 = 452795) (by norm_num)
theorem B3219875 : Blo 2145435 3219875 := bstep (se 1 (by rfl) ⟨2414906, by rfl⟩ : syracuseStep 3219875 = 4829813) B4829813
theorem B2146583 : Blo 2145435 2146583 := bstep (se 1 (by rfl) ⟨1609937, by rfl⟩ : syracuseStep 2146583 = 3219875) B3219875
theorem B18588437 : Blo 2145435 18588437 := bbase (se 6 (by rfl) ⟨435666, by rfl⟩ : syracuseStep 18588437 = 871333) (by norm_num)
theorem B12392291 : Blo 2145435 12392291 := bstep (se 1 (by rfl) ⟨9294218, by rfl⟩ : syracuseStep 12392291 = 18588437) B18588437
theorem B8261527 : Blo 2145435 8261527 := bstep (se 1 (by rfl) ⟨6196145, by rfl⟩ : syracuseStep 8261527 = 12392291) B12392291
theorem B11015369 : Blo 2145435 11015369 := bstep (se 2 (by rfl) ⟨4130763, by rfl⟩ : syracuseStep 11015369 = 8261527) B8261527
theorem B7343579 : Blo 2145435 7343579 := bstep (se 1 (by rfl) ⟨5507684, by rfl⟩ : syracuseStep 7343579 = 11015369) B11015369
theorem B19582877 : Blo 2145435 19582877 := bstep (se 3 (by rfl) ⟨3671789, by rfl⟩ : syracuseStep 19582877 = 7343579) B7343579
theorem B13055251 : Blo 2145435 13055251 := bstep (se 1 (by rfl) ⟨9791438, by rfl⟩ : syracuseStep 13055251 = 19582877) B19582877
theorem B17407001 : Blo 2145435 17407001 := bstep (se 2 (by rfl) ⟨6527625, by rfl⟩ : syracuseStep 17407001 = 13055251) B13055251
theorem B11604667 : Blo 2145435 11604667 := bstep (se 1 (by rfl) ⟨8703500, by rfl⟩ : syracuseStep 11604667 = 17407001) B17407001
theorem B15472889 : Blo 2145435 15472889 := bstep (se 2 (by rfl) ⟨5802333, by rfl⟩ : syracuseStep 15472889 = 11604667) B11604667
theorem B10315259 : Blo 2145435 10315259 := bstep (se 1 (by rfl) ⟨7736444, by rfl⟩ : syracuseStep 10315259 = 15472889) B15472889
theorem B6876839 : Blo 2145435 6876839 := bstep (se 1 (by rfl) ⟨5157629, by rfl⟩ : syracuseStep 6876839 = 10315259) B10315259
theorem B18338237 : Blo 2145435 18338237 := bstep (se 3 (by rfl) ⟨3438419, by rfl⟩ : syracuseStep 18338237 = 6876839) B6876839
theorem B12225491 : Blo 2145435 12225491 := bstep (se 1 (by rfl) ⟨9169118, by rfl⟩ : syracuseStep 12225491 = 18338237) B18338237
theorem B8150327 : Blo 2145435 8150327 := bstep (se 1 (by rfl) ⟨6112745, by rfl⟩ : syracuseStep 8150327 = 12225491) B12225491
theorem B5433551 : Blo 2145435 5433551 := bstep (se 1 (by rfl) ⟨4075163, by rfl⟩ : syracuseStep 5433551 = 8150327) B8150327
theorem B3622367 : Blo 2145435 3622367 := bstep (se 1 (by rfl) ⟨2716775, by rfl⟩ : syracuseStep 3622367 = 5433551) B5433551
theorem B2414911 : Blo 2145435 2414911 := bstep (se 1 (by rfl) ⟨1811183, by rfl⟩ : syracuseStep 2414911 = 3622367) B3622367
theorem B3219881 : Blo 2145435 3219881 := bstep (se 2 (by rfl) ⟨1207455, by rfl⟩ : syracuseStep 3219881 = 2414911) B2414911
theorem B2146587 : Blo 2145435 2146587 := bstep (se 1 (by rfl) ⟨1609940, by rfl⟩ : syracuseStep 2146587 = 3219881) B3219881
theorem B8150341 : Blo 2145435 8150341 := bbase (se 4 (by rfl) ⟨764094, by rfl⟩ : syracuseStep 8150341 = 1528189) (by norm_num)
theorem B10867121 : Blo 2145435 10867121 := bstep (se 2 (by rfl) ⟨4075170, by rfl⟩ : syracuseStep 10867121 = 8150341) B8150341
theorem B7244747 : Blo 2145435 7244747 := bstep (se 1 (by rfl) ⟨5433560, by rfl⟩ : syracuseStep 7244747 = 10867121) B10867121
theorem B4829831 : Blo 2145435 4829831 := bstep (se 1 (by rfl) ⟨3622373, by rfl⟩ : syracuseStep 4829831 = 7244747) B7244747
theorem B3219887 : Blo 2145435 3219887 := bstep (se 1 (by rfl) ⟨2414915, by rfl⟩ : syracuseStep 3219887 = 4829831) B4829831
theorem B2146591 : Blo 2145435 2146591 := bstep (se 1 (by rfl) ⟨1609943, by rfl⟩ : syracuseStep 2146591 = 3219887) B3219887
theorem B3219893 : Blo 2145435 3219893 := bbase (se 5 (by rfl) ⟨150932, by rfl⟩ : syracuseStep 3219893 = 301865) (by norm_num)
theorem B2146595 : Blo 2145435 2146595 := bstep (se 1 (by rfl) ⟨1609946, by rfl⟩ : syracuseStep 2146595 = 3219893) B3219893
theorem B5433581 : Blo 2145435 5433581 := bbase (se 3 (by rfl) ⟨1018796, by rfl⟩ : syracuseStep 5433581 = 2037593) (by norm_num)
theorem B3622387 : Blo 2145435 3622387 := bstep (se 1 (by rfl) ⟨2716790, by rfl⟩ : syracuseStep 3622387 = 5433581) B5433581
theorem B4829849 : Blo 2145435 4829849 := bstep (se 2 (by rfl) ⟨1811193, by rfl⟩ : syracuseStep 4829849 = 3622387) B3622387
theorem B3219899 : Blo 2145435 3219899 := bstep (se 1 (by rfl) ⟨2414924, by rfl⟩ : syracuseStep 3219899 = 4829849) B4829849
theorem B2146599 : Blo 2145435 2146599 := bstep (se 1 (by rfl) ⟨1609949, by rfl⟩ : syracuseStep 2146599 = 3219899) B3219899
theorem B2414929 : Blo 2145435 2414929 := bbase (se 2 (by rfl) ⟨905598, by rfl⟩ : syracuseStep 2414929 = 1811197) (by norm_num)
theorem B3219905 : Blo 2145435 3219905 := bstep (se 2 (by rfl) ⟨1207464, by rfl⟩ : syracuseStep 3219905 = 2414929) B2414929
theorem B2146603 : Blo 2145435 2146603 := bstep (se 1 (by rfl) ⟨1609952, by rfl⟩ : syracuseStep 2146603 = 3219905) B3219905
theorem B2292301 : Blo 2145435 2292301 := bbase (se 3 (by rfl) ⟨429806, by rfl⟩ : syracuseStep 2292301 = 859613) (by norm_num)
theorem B3056401 : Blo 2145435 3056401 := bstep (se 2 (by rfl) ⟨1146150, by rfl⟩ : syracuseStep 3056401 = 2292301) B2292301
theorem B4075201 : Blo 2145435 4075201 := bstep (se 2 (by rfl) ⟨1528200, by rfl⟩ : syracuseStep 4075201 = 3056401) B3056401
theorem B5433601 : Blo 2145435 5433601 := bstep (se 2 (by rfl) ⟨2037600, by rfl⟩ : syracuseStep 5433601 = 4075201) B4075201
theorem B7244801 : Blo 2145435 7244801 := bstep (se 2 (by rfl) ⟨2716800, by rfl⟩ : syracuseStep 7244801 = 5433601) B5433601
theorem B4829867 : Blo 2145435 4829867 := bstep (se 1 (by rfl) ⟨3622400, by rfl⟩ : syracuseStep 4829867 = 7244801) B7244801
theorem B3219911 : Blo 2145435 3219911 := bstep (se 1 (by rfl) ⟨2414933, by rfl⟩ : syracuseStep 3219911 = 4829867) B4829867
theorem B2146607 : Blo 2145435 2146607 := bstep (se 1 (by rfl) ⟨1609955, by rfl⟩ : syracuseStep 2146607 = 3219911) B3219911
theorem B3219917 : Blo 2145435 3219917 := bbase (se 3 (by rfl) ⟨603734, by rfl⟩ : syracuseStep 3219917 = 1207469) (by norm_num)
theorem B2146611 : Blo 2145435 2146611 := bstep (se 1 (by rfl) ⟨1609958, by rfl⟩ : syracuseStep 2146611 = 3219917) B3219917
theorem B4829885 : Blo 2145435 4829885 := bbase (se 3 (by rfl) ⟨905603, by rfl⟩ : syracuseStep 4829885 = 1811207) (by norm_num)
theorem B3219923 : Blo 2145435 3219923 := bstep (se 1 (by rfl) ⟨2414942, by rfl⟩ : syracuseStep 3219923 = 4829885) B4829885
theorem B2146615 : Blo 2145435 2146615 := bstep (se 1 (by rfl) ⟨1609961, by rfl⟩ : syracuseStep 2146615 = 3219923) B3219923
theorem B3622421 : Blo 2145435 3622421 := bbase (se 6 (by rfl) ⟨84900, by rfl⟩ : syracuseStep 3622421 = 169801) (by norm_num)
theorem B2414947 : Blo 2145435 2414947 := bstep (se 1 (by rfl) ⟨1811210, by rfl⟩ : syracuseStep 2414947 = 3622421) B3622421
theorem B3219929 : Blo 2145435 3219929 := bstep (se 2 (by rfl) ⟨1207473, by rfl⟩ : syracuseStep 3219929 = 2414947) B2414947
theorem B2146619 : Blo 2145435 2146619 := bstep (se 1 (by rfl) ⟨1609964, by rfl⟩ : syracuseStep 2146619 = 3219929) B3219929
theorem B3098125 : Blo 2145435 3098125 := bbase (se 3 (by rfl) ⟨580898, by rfl⟩ : syracuseStep 3098125 = 1161797) (by norm_num)
theorem B4130833 : Blo 2145435 4130833 := bstep (se 2 (by rfl) ⟨1549062, by rfl⟩ : syracuseStep 4130833 = 3098125) B3098125
theorem B5507777 : Blo 2145435 5507777 := bstep (se 2 (by rfl) ⟨2065416, by rfl⟩ : syracuseStep 5507777 = 4130833) B4130833
theorem B14687405 : Blo 2145435 14687405 := bstep (se 3 (by rfl) ⟨2753888, by rfl⟩ : syracuseStep 14687405 = 5507777) B5507777
theorem B9791603 : Blo 2145435 9791603 := bstep (se 1 (by rfl) ⟨7343702, by rfl⟩ : syracuseStep 9791603 = 14687405) B14687405
theorem B6527735 : Blo 2145435 6527735 := bstep (se 1 (by rfl) ⟨4895801, by rfl⟩ : syracuseStep 6527735 = 9791603) B9791603
theorem B4351823 : Blo 2145435 4351823 := bstep (se 1 (by rfl) ⟨3263867, by rfl⟩ : syracuseStep 4351823 = 6527735) B6527735
theorem B2901215 : Blo 2145435 2901215 := bstep (se 1 (by rfl) ⟨2175911, by rfl⟩ : syracuseStep 2901215 = 4351823) B4351823
theorem B7736573 : Blo 2145435 7736573 := bstep (se 3 (by rfl) ⟨1450607, by rfl⟩ : syracuseStep 7736573 = 2901215) B2901215
theorem B20630861 : Blo 2145435 20630861 := bstep (se 3 (by rfl) ⟨3868286, by rfl⟩ : syracuseStep 20630861 = 7736573) B7736573
theorem B13753907 : Blo 2145435 13753907 := bstep (se 1 (by rfl) ⟨10315430, by rfl⟩ : syracuseStep 13753907 = 20630861) B20630861
theorem B9169271 : Blo 2145435 9169271 := bstep (se 1 (by rfl) ⟨6876953, by rfl⟩ : syracuseStep 9169271 = 13753907) B13753907
theorem B6112847 : Blo 2145435 6112847 := bstep (se 1 (by rfl) ⟨4584635, by rfl⟩ : syracuseStep 6112847 = 9169271) B9169271
theorem B16300925 : Blo 2145435 16300925 := bstep (se 3 (by rfl) ⟨3056423, by rfl⟩ : syracuseStep 16300925 = 6112847) B6112847
theorem B10867283 : Blo 2145435 10867283 := bstep (se 1 (by rfl) ⟨8150462, by rfl⟩ : syracuseStep 10867283 = 16300925) B16300925
theorem B7244855 : Blo 2145435 7244855 := bstep (se 1 (by rfl) ⟨5433641, by rfl⟩ : syracuseStep 7244855 = 10867283) B10867283
theorem B4829903 : Blo 2145435 4829903 := bstep (se 1 (by rfl) ⟨3622427, by rfl⟩ : syracuseStep 4829903 = 7244855) B7244855
theorem B3219935 : Blo 2145435 3219935 := bstep (se 1 (by rfl) ⟨2414951, by rfl⟩ : syracuseStep 3219935 = 4829903) B4829903
theorem B2146623 : Blo 2145435 2146623 := bstep (se 1 (by rfl) ⟨1609967, by rfl⟩ : syracuseStep 2146623 = 3219935) B3219935
theorem B3219941 : Blo 2145435 3219941 := bbase (se 4 (by rfl) ⟨301869, by rfl⟩ : syracuseStep 3219941 = 603739) (by norm_num)
theorem B2146627 : Blo 2145435 2146627 := bstep (se 1 (by rfl) ⟨1609970, by rfl⟩ : syracuseStep 2146627 = 3219941) B3219941
theorem B2235701 : Blo 2145435 2235701 := bbase (se 5 (by rfl) ⟨104798, by rfl⟩ : syracuseStep 2235701 = 209597) (by norm_num)
theorem B5961869 : Blo 2145435 5961869 := bstep (se 3 (by rfl) ⟨1117850, by rfl⟩ : syracuseStep 5961869 = 2235701) B2235701
theorem B3974579 : Blo 2145435 3974579 := bstep (se 1 (by rfl) ⟨2980934, by rfl⟩ : syracuseStep 3974579 = 5961869) B5961869
theorem B2649719 : Blo 2145435 2649719 := bstep (se 1 (by rfl) ⟨1987289, by rfl⟩ : syracuseStep 2649719 = 3974579) B3974579
theorem B7065917 : Blo 2145435 7065917 := bstep (se 3 (by rfl) ⟨1324859, by rfl⟩ : syracuseStep 7065917 = 2649719) B2649719
theorem B4710611 : Blo 2145435 4710611 := bstep (se 1 (by rfl) ⟨3532958, by rfl⟩ : syracuseStep 4710611 = 7065917) B7065917
theorem B3140407 : Blo 2145435 3140407 := bstep (se 1 (by rfl) ⟨2355305, by rfl⟩ : syracuseStep 3140407 = 4710611) B4710611
theorem B4187209 : Blo 2145435 4187209 := bstep (se 2 (by rfl) ⟨1570203, by rfl⟩ : syracuseStep 4187209 = 3140407) B3140407
theorem B5582945 : Blo 2145435 5582945 := bstep (se 2 (by rfl) ⟨2093604, by rfl⟩ : syracuseStep 5582945 = 4187209) B4187209
theorem B3721963 : Blo 2145435 3721963 := bstep (se 1 (by rfl) ⟨2791472, by rfl⟩ : syracuseStep 3721963 = 5582945) B5582945
theorem B4962617 : Blo 2145435 4962617 := bstep (se 2 (by rfl) ⟨1860981, by rfl⟩ : syracuseStep 4962617 = 3721963) B3721963
theorem B3308411 : Blo 2145435 3308411 := bstep (se 1 (by rfl) ⟨2481308, by rfl⟩ : syracuseStep 3308411 = 4962617) B4962617
theorem B2205607 : Blo 2145435 2205607 := bstep (se 1 (by rfl) ⟨1654205, by rfl⟩ : syracuseStep 2205607 = 3308411) B3308411
theorem B2940809 : Blo 2145435 2940809 := bstep (se 2 (by rfl) ⟨1102803, by rfl⟩ : syracuseStep 2940809 = 2205607) B2205607
theorem B31368629 : Blo 2145435 31368629 := bstep (se 5 (by rfl) ⟨1470404, by rfl⟩ : syracuseStep 31368629 = 2940809) B2940809
theorem B20912419 : Blo 2145435 20912419 := bstep (se 1 (by rfl) ⟨15684314, by rfl⟩ : syracuseStep 20912419 = 31368629) B31368629
theorem B27883225 : Blo 2145435 27883225 := bstep (se 2 (by rfl) ⟨10456209, by rfl⟩ : syracuseStep 27883225 = 20912419) B20912419
theorem B37177633 : Blo 2145435 37177633 := bstep (se 2 (by rfl) ⟨13941612, by rfl⟩ : syracuseStep 37177633 = 27883225) B27883225
theorem B49570177 : Blo 2145435 49570177 := bstep (se 2 (by rfl) ⟨18588816, by rfl⟩ : syracuseStep 49570177 = 37177633) B37177633
theorem B66093569 : Blo 2145435 66093569 := bstep (se 2 (by rfl) ⟨24785088, by rfl⟩ : syracuseStep 66093569 = 49570177) B49570177
theorem B44062379 : Blo 2145435 44062379 := bstep (se 1 (by rfl) ⟨33046784, by rfl⟩ : syracuseStep 44062379 = 66093569) B66093569
theorem B29374919 : Blo 2145435 29374919 := bstep (se 1 (by rfl) ⟨22031189, by rfl⟩ : syracuseStep 29374919 = 44062379) B44062379
theorem B19583279 : Blo 2145435 19583279 := bstep (se 1 (by rfl) ⟨14687459, by rfl⟩ : syracuseStep 19583279 = 29374919) B29374919
theorem B13055519 : Blo 2145435 13055519 := bstep (se 1 (by rfl) ⟨9791639, by rfl⟩ : syracuseStep 13055519 = 19583279) B19583279
theorem B34814717 : Blo 2145435 34814717 := bstep (se 3 (by rfl) ⟨6527759, by rfl⟩ : syracuseStep 34814717 = 13055519) B13055519
theorem B23209811 : Blo 2145435 23209811 := bstep (se 1 (by rfl) ⟨17407358, by rfl⟩ : syracuseStep 23209811 = 34814717) B34814717
theorem B15473207 : Blo 2145435 15473207 := bstep (se 1 (by rfl) ⟨11604905, by rfl⟩ : syracuseStep 15473207 = 23209811) B23209811
theorem B10315471 : Blo 2145435 10315471 := bstep (se 1 (by rfl) ⟨7736603, by rfl⟩ : syracuseStep 10315471 = 15473207) B15473207
theorem B13753961 : Blo 2145435 13753961 := bstep (se 2 (by rfl) ⟨5157735, by rfl⟩ : syracuseStep 13753961 = 10315471) B10315471
theorem B9169307 : Blo 2145435 9169307 := bstep (se 1 (by rfl) ⟨6876980, by rfl⟩ : syracuseStep 9169307 = 13753961) B13753961
theorem B6112871 : Blo 2145435 6112871 := bstep (se 1 (by rfl) ⟨4584653, by rfl⟩ : syracuseStep 6112871 = 9169307) B9169307
theorem B4075247 : Blo 2145435 4075247 := bstep (se 1 (by rfl) ⟨3056435, by rfl⟩ : syracuseStep 4075247 = 6112871) B6112871
theorem B2716831 : Blo 2145435 2716831 := bstep (se 1 (by rfl) ⟨2037623, by rfl⟩ : syracuseStep 2716831 = 4075247) B4075247
theorem B3622441 : Blo 2145435 3622441 := bstep (se 2 (by rfl) ⟨1358415, by rfl⟩ : syracuseStep 3622441 = 2716831) B2716831
theorem B4829921 : Blo 2145435 4829921 := bstep (se 2 (by rfl) ⟨1811220, by rfl⟩ : syracuseStep 4829921 = 3622441) B3622441
theorem B3219947 : Blo 2145435 3219947 := bstep (se 1 (by rfl) ⟨2414960, by rfl⟩ : syracuseStep 3219947 = 4829921) B4829921
theorem B2146631 : Blo 2145435 2146631 := bstep (se 1 (by rfl) ⟨1609973, by rfl⟩ : syracuseStep 2146631 = 3219947) B3219947
theorem B2414965 : Blo 2145435 2414965 := bbase (se 5 (by rfl) ⟨113201, by rfl⟩ : syracuseStep 2414965 = 226403) (by norm_num)
theorem B3219953 : Blo 2145435 3219953 := bstep (se 2 (by rfl) ⟨1207482, by rfl⟩ : syracuseStep 3219953 = 2414965) B2414965
theorem B2146635 : Blo 2145435 2146635 := bstep (se 1 (by rfl) ⟨1609976, by rfl⟩ : syracuseStep 2146635 = 3219953) B3219953
theorem B2716841 : Blo 2145435 2716841 := bbase (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) (by norm_num)
theorem B7244909 : Blo 2145435 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B4829939 : Blo 2145435 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B3219959 : Blo 2145435 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B2146639 : Blo 2145435 2146639 := bstep (se 1 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 2146639 = 3219959) B3219959
theorem B3219965 : Blo 2145435 3219965 := bbase (se 3 (by rfl) ⟨603743, by rfl⟩ : syracuseStep 3219965 = 1207487) (by norm_num)
theorem B2146643 : Blo 2145435 2146643 := bstep (se 1 (by rfl) ⟨1609982, by rfl⟩ : syracuseStep 2146643 = 3219965) B3219965
theorem B4829957 : Blo 2145435 4829957 := bbase (se 4 (by rfl) ⟨452808, by rfl⟩ : syracuseStep 4829957 = 905617) (by norm_num)
theorem B3219971 : Blo 2145435 3219971 := bstep (se 1 (by rfl) ⟨2414978, by rfl⟩ : syracuseStep 3219971 = 4829957) B4829957
theorem B2146647 : Blo 2145435 2146647 := bstep (se 1 (by rfl) ⟨1609985, by rfl⟩ : syracuseStep 2146647 = 3219971) B3219971
theorem B4075285 : Blo 2145435 4075285 := bbase (se 6 (by rfl) ⟨95514, by rfl⟩ : syracuseStep 4075285 = 191029) (by norm_num)
theorem B5433713 : Blo 2145435 5433713 := bstep (se 2 (by rfl) ⟨2037642, by rfl⟩ : syracuseStep 5433713 = 4075285) B4075285
theorem B3622475 : Blo 2145435 3622475 := bstep (se 1 (by rfl) ⟨2716856, by rfl⟩ : syracuseStep 3622475 = 5433713) B5433713
theorem B2414983 : Blo 2145435 2414983 := bstep (se 1 (by rfl) ⟨1811237, by rfl⟩ : syracuseStep 2414983 = 3622475) B3622475
theorem B3219977 : Blo 2145435 3219977 := bstep (se 2 (by rfl) ⟨1207491, by rfl⟩ : syracuseStep 3219977 = 2414983) B2414983
theorem B2146651 : Blo 2145435 2146651 := bstep (se 1 (by rfl) ⟨1609988, by rfl⟩ : syracuseStep 2146651 = 3219977) B3219977
theorem B10867445 : Blo 2145435 10867445 := bbase (se 5 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 10867445 = 1018823) (by norm_num)
theorem B7244963 : Blo 2145435 7244963 := bstep (se 1 (by rfl) ⟨5433722, by rfl⟩ : syracuseStep 7244963 = 10867445) B10867445
theorem B4829975 : Blo 2145435 4829975 := bstep (se 1 (by rfl) ⟨3622481, by rfl⟩ : syracuseStep 4829975 = 7244963) B7244963
theorem B3219983 : Blo 2145435 3219983 := bstep (se 1 (by rfl) ⟨2414987, by rfl⟩ : syracuseStep 3219983 = 4829975) B4829975
theorem B2146655 : Blo 2145435 2146655 := bstep (se 1 (by rfl) ⟨1609991, by rfl⟩ : syracuseStep 2146655 = 3219983) B3219983
theorem B3219989 : Blo 2145435 3219989 := bbase (se 6 (by rfl) ⟨75468, by rfl⟩ : syracuseStep 3219989 = 150937) (by norm_num)
theorem B2146659 : Blo 2145435 2146659 := bstep (se 1 (by rfl) ⟨1609994, by rfl⟩ : syracuseStep 2146659 = 3219989) B3219989
theorem B3438541 : Blo 2145435 3438541 := bbase (se 3 (by rfl) ⟨644726, by rfl⟩ : syracuseStep 3438541 = 1289453) (by norm_num)
theorem B18338885 : Blo 2145435 18338885 := bstep (se 4 (by rfl) ⟨1719270, by rfl⟩ : syracuseStep 18338885 = 3438541) B3438541
theorem B12225923 : Blo 2145435 12225923 := bstep (se 1 (by rfl) ⟨9169442, by rfl⟩ : syracuseStep 12225923 = 18338885) B18338885
theorem B8150615 : Blo 2145435 8150615 := bstep (se 1 (by rfl) ⟨6112961, by rfl⟩ : syracuseStep 8150615 = 12225923) B12225923
theorem B5433743 : Blo 2145435 5433743 := bstep (se 1 (by rfl) ⟨4075307, by rfl⟩ : syracuseStep 5433743 = 8150615) B8150615
theorem B3622495 : Blo 2145435 3622495 := bstep (se 1 (by rfl) ⟨2716871, by rfl⟩ : syracuseStep 3622495 = 5433743) B5433743
theorem B4829993 : Blo 2145435 4829993 := bstep (se 2 (by rfl) ⟨1811247, by rfl⟩ : syracuseStep 4829993 = 3622495) B3622495
theorem B3219995 : Blo 2145435 3219995 := bstep (se 1 (by rfl) ⟨2414996, by rfl⟩ : syracuseStep 3219995 = 4829993) B4829993
theorem B2146663 : Blo 2145435 2146663 := bstep (se 1 (by rfl) ⟨1609997, by rfl⟩ : syracuseStep 2146663 = 3219995) B3219995
theorem B2415001 : Blo 2145435 2415001 := bbase (se 2 (by rfl) ⟨905625, by rfl⟩ : syracuseStep 2415001 = 1811251) (by norm_num)
theorem B3220001 : Blo 2145435 3220001 := bstep (se 2 (by rfl) ⟨1207500, by rfl⟩ : syracuseStep 3220001 = 2415001) B2415001
theorem B2146667 : Blo 2145435 2146667 := bstep (se 1 (by rfl) ⟨1610000, by rfl⟩ : syracuseStep 2146667 = 3220001) B3220001
theorem B8150645 : Blo 2145435 8150645 := bbase (se 5 (by rfl) ⟨382061, by rfl⟩ : syracuseStep 8150645 = 764123) (by norm_num)
theorem B5433763 : Blo 2145435 5433763 := bstep (se 1 (by rfl) ⟨4075322, by rfl⟩ : syracuseStep 5433763 = 8150645) B8150645
theorem B7245017 : Blo 2145435 7245017 := bstep (se 2 (by rfl) ⟨2716881, by rfl⟩ : syracuseStep 7245017 = 5433763) B5433763
theorem B4830011 : Blo 2145435 4830011 := bstep (se 1 (by rfl) ⟨3622508, by rfl⟩ : syracuseStep 4830011 = 7245017) B7245017
theorem B3220007 : Blo 2145435 3220007 := bstep (se 1 (by rfl) ⟨2415005, by rfl⟩ : syracuseStep 3220007 = 4830011) B4830011
theorem B2146671 : Blo 2145435 2146671 := bstep (se 1 (by rfl) ⟨1610003, by rfl⟩ : syracuseStep 2146671 = 3220007) B3220007
theorem B3220013 : Blo 2145435 3220013 := bbase (se 3 (by rfl) ⟨603752, by rfl⟩ : syracuseStep 3220013 = 1207505) (by norm_num)
theorem B2146675 : Blo 2145435 2146675 := bstep (se 1 (by rfl) ⟨1610006, by rfl⟩ : syracuseStep 2146675 = 3220013) B3220013
theorem B4830029 : Blo 2145435 4830029 := bbase (se 3 (by rfl) ⟨905630, by rfl⟩ : syracuseStep 4830029 = 1811261) (by norm_num)
theorem B3220019 : Blo 2145435 3220019 := bstep (se 1 (by rfl) ⟨2415014, by rfl⟩ : syracuseStep 3220019 = 4830029) B4830029
theorem B2146679 : Blo 2145435 2146679 := bstep (se 1 (by rfl) ⟨1610009, by rfl⟩ : syracuseStep 2146679 = 3220019) B3220019
theorem B2716897 : Blo 2145435 2716897 := bbase (se 2 (by rfl) ⟨1018836, by rfl⟩ : syracuseStep 2716897 = 2037673) (by norm_num)
theorem B3622529 : Blo 2145435 3622529 := bstep (se 2 (by rfl) ⟨1358448, by rfl⟩ : syracuseStep 3622529 = 2716897) B2716897
theorem B2415019 : Blo 2145435 2415019 := bstep (se 1 (by rfl) ⟨1811264, by rfl⟩ : syracuseStep 2415019 = 3622529) B3622529
theorem B3220025 : Blo 2145435 3220025 := bstep (se 2 (by rfl) ⟨1207509, by rfl⟩ : syracuseStep 3220025 = 2415019) B2415019
theorem B2146683 : Blo 2145435 2146683 := bstep (se 1 (by rfl) ⟨1610012, by rfl⟩ : syracuseStep 2146683 = 3220025) B3220025
theorem B24452117 : Blo 2145435 24452117 := bbase (se 6 (by rfl) ⟨573096, by rfl⟩ : syracuseStep 24452117 = 1146193) (by norm_num)
theorem B16301411 : Blo 2145435 16301411 := bstep (se 1 (by rfl) ⟨12226058, by rfl⟩ : syracuseStep 16301411 = 24452117) B24452117
theorem B10867607 : Blo 2145435 10867607 := bstep (se 1 (by rfl) ⟨8150705, by rfl⟩ : syracuseStep 10867607 = 16301411) B16301411
theorem B7245071 : Blo 2145435 7245071 := bstep (se 1 (by rfl) ⟨5433803, by rfl⟩ : syracuseStep 7245071 = 10867607) B10867607
theorem B4830047 : Blo 2145435 4830047 := bstep (se 1 (by rfl) ⟨3622535, by rfl⟩ : syracuseStep 4830047 = 7245071) B7245071
theorem B3220031 : Blo 2145435 3220031 := bstep (se 1 (by rfl) ⟨2415023, by rfl⟩ : syracuseStep 3220031 = 4830047) B4830047
theorem B2146687 : Blo 2145435 2146687 := bstep (se 1 (by rfl) ⟨1610015, by rfl⟩ : syracuseStep 2146687 = 3220031) B3220031
theorem B3220037 : Blo 2145435 3220037 := bbase (se 4 (by rfl) ⟨301878, by rfl⟩ : syracuseStep 3220037 = 603757) (by norm_num)
theorem B2146691 : Blo 2145435 2146691 := bstep (se 1 (by rfl) ⟨1610018, by rfl⟩ : syracuseStep 2146691 = 3220037) B3220037
theorem B3622549 : Blo 2145435 3622549 := bbase (se 6 (by rfl) ⟨84903, by rfl⟩ : syracuseStep 3622549 = 169807) (by norm_num)
theorem B4830065 : Blo 2145435 4830065 := bstep (se 2 (by rfl) ⟨1811274, by rfl⟩ : syracuseStep 4830065 = 3622549) B3622549
theorem B3220043 : Blo 2145435 3220043 := bstep (se 1 (by rfl) ⟨2415032, by rfl⟩ : syracuseStep 3220043 = 4830065) B4830065
theorem B2146695 : Blo 2145435 2146695 := bstep (se 1 (by rfl) ⟨1610021, by rfl⟩ : syracuseStep 2146695 = 3220043) B3220043
theorem B2415037 : Blo 2145435 2415037 := bbase (se 3 (by rfl) ⟨452819, by rfl⟩ : syracuseStep 2415037 = 905639) (by norm_num)
theorem B3220049 : Blo 2145435 3220049 := bstep (se 2 (by rfl) ⟨1207518, by rfl⟩ : syracuseStep 3220049 = 2415037) B2415037
theorem B2146699 : Blo 2145435 2146699 := bstep (se 1 (by rfl) ⟨1610024, by rfl⟩ : syracuseStep 2146699 = 3220049) B3220049
theorem B7245125 : Blo 2145435 7245125 := bbase (se 4 (by rfl) ⟨679230, by rfl⟩ : syracuseStep 7245125 = 1358461) (by norm_num)
theorem B4830083 : Blo 2145435 4830083 := bstep (se 1 (by rfl) ⟨3622562, by rfl⟩ : syracuseStep 4830083 = 7245125) B7245125
theorem B3220055 : Blo 2145435 3220055 := bstep (se 1 (by rfl) ⟨2415041, by rfl⟩ : syracuseStep 3220055 = 4830083) B4830083
theorem B2146703 : Blo 2145435 2146703 := bstep (se 1 (by rfl) ⟨1610027, by rfl⟩ : syracuseStep 2146703 = 3220055) B3220055
theorem B3220061 : Blo 2145435 3220061 := bbase (se 3 (by rfl) ⟨603761, by rfl⟩ : syracuseStep 3220061 = 1207523) (by norm_num)
theorem B2146707 : Blo 2145435 2146707 := bstep (se 1 (by rfl) ⟨1610030, by rfl⟩ : syracuseStep 2146707 = 3220061) B3220061
theorem B4830101 : Blo 2145435 4830101 := bbase (se 6 (by rfl) ⟨113205, by rfl⟩ : syracuseStep 4830101 = 226411) (by norm_num)
theorem B3220067 : Blo 2145435 3220067 := bstep (se 1 (by rfl) ⟨2415050, by rfl⟩ : syracuseStep 3220067 = 4830101) B4830101
theorem B2146711 : Blo 2145435 2146711 := bstep (se 1 (by rfl) ⟨1610033, by rfl⟩ : syracuseStep 2146711 = 3220067) B3220067
theorem B2578969 : Blo 2145435 2578969 := bbase (se 2 (by rfl) ⟨967113, by rfl⟩ : syracuseStep 2578969 = 1934227) (by norm_num)
theorem B3438625 : Blo 2145435 3438625 := bstep (se 2 (by rfl) ⟨1289484, by rfl⟩ : syracuseStep 3438625 = 2578969) B2578969
theorem B4584833 : Blo 2145435 4584833 := bstep (se 2 (by rfl) ⟨1719312, by rfl⟩ : syracuseStep 4584833 = 3438625) B3438625
theorem B3056555 : Blo 2145435 3056555 := bstep (se 1 (by rfl) ⟨2292416, by rfl⟩ : syracuseStep 3056555 = 4584833) B4584833
theorem B8150813 : Blo 2145435 8150813 := bstep (se 3 (by rfl) ⟨1528277, by rfl⟩ : syracuseStep 8150813 = 3056555) B3056555
theorem B5433875 : Blo 2145435 5433875 := bstep (se 1 (by rfl) ⟨4075406, by rfl⟩ : syracuseStep 5433875 = 8150813) B8150813
theorem B3622583 : Blo 2145435 3622583 := bstep (se 1 (by rfl) ⟨2716937, by rfl⟩ : syracuseStep 3622583 = 5433875) B5433875
theorem B2415055 : Blo 2145435 2415055 := bstep (se 1 (by rfl) ⟨1811291, by rfl⟩ : syracuseStep 2415055 = 3622583) B3622583
theorem B3220073 : Blo 2145435 3220073 := bstep (se 2 (by rfl) ⟨1207527, by rfl⟩ : syracuseStep 3220073 = 2415055) B2415055
theorem B2146715 : Blo 2145435 2146715 := bstep (se 1 (by rfl) ⟨1610036, by rfl⟩ : syracuseStep 2146715 = 3220073) B3220073
theorem B2578973 : Blo 2145435 2578973 := bbase (se 3 (by rfl) ⟨483557, by rfl⟩ : syracuseStep 2578973 = 967115) (by norm_num)
theorem B6877261 : Blo 2145435 6877261 := bstep (se 3 (by rfl) ⟨1289486, by rfl⟩ : syracuseStep 6877261 = 2578973) B2578973
theorem B9169681 : Blo 2145435 9169681 := bstep (se 2 (by rfl) ⟨3438630, by rfl⟩ : syracuseStep 9169681 = 6877261) B6877261
theorem B12226241 : Blo 2145435 12226241 := bstep (se 2 (by rfl) ⟨4584840, by rfl⟩ : syracuseStep 12226241 = 9169681) B9169681
theorem B8150827 : Blo 2145435 8150827 := bstep (se 1 (by rfl) ⟨6113120, by rfl⟩ : syracuseStep 8150827 = 12226241) B12226241
theorem B10867769 : Blo 2145435 10867769 := bstep (se 2 (by rfl) ⟨4075413, by rfl⟩ : syracuseStep 10867769 = 8150827) B8150827
theorem B7245179 : Blo 2145435 7245179 := bstep (se 1 (by rfl) ⟨5433884, by rfl⟩ : syracuseStep 7245179 = 10867769) B10867769
theorem B4830119 : Blo 2145435 4830119 := bstep (se 1 (by rfl) ⟨3622589, by rfl⟩ : syracuseStep 4830119 = 7245179) B7245179
theorem B3220079 : Blo 2145435 3220079 := bstep (se 1 (by rfl) ⟨2415059, by rfl⟩ : syracuseStep 3220079 = 4830119) B4830119
theorem B2146719 : Blo 2145435 2146719 := bstep (se 1 (by rfl) ⟨1610039, by rfl⟩ : syracuseStep 2146719 = 3220079) B3220079
theorem B3220085 : Blo 2145435 3220085 := bbase (se 5 (by rfl) ⟨150941, by rfl⟩ : syracuseStep 3220085 = 301883) (by norm_num)
theorem B2146723 : Blo 2145435 2146723 := bstep (se 1 (by rfl) ⟨1610042, by rfl⟩ : syracuseStep 2146723 = 3220085) B3220085
theorem B4075429 : Blo 2145435 4075429 := bbase (se 4 (by rfl) ⟨382071, by rfl⟩ : syracuseStep 4075429 = 764143) (by norm_num)
theorem B5433905 : Blo 2145435 5433905 := bstep (se 2 (by rfl) ⟨2037714, by rfl⟩ : syracuseStep 5433905 = 4075429) B4075429
theorem B3622603 : Blo 2145435 3622603 := bstep (se 1 (by rfl) ⟨2716952, by rfl⟩ : syracuseStep 3622603 = 5433905) B5433905
theorem B4830137 : Blo 2145435 4830137 := bstep (se 2 (by rfl) ⟨1811301, by rfl⟩ : syracuseStep 4830137 = 3622603) B3622603
theorem B3220091 : Blo 2145435 3220091 := bstep (se 1 (by rfl) ⟨2415068, by rfl⟩ : syracuseStep 3220091 = 4830137) B4830137
theorem B2146727 : Blo 2145435 2146727 := bstep (se 1 (by rfl) ⟨1610045, by rfl⟩ : syracuseStep 2146727 = 3220091) B3220091
theorem B2415073 : Blo 2145435 2415073 := bbase (se 2 (by rfl) ⟨905652, by rfl⟩ : syracuseStep 2415073 = 1811305) (by norm_num)
theorem B3220097 : Blo 2145435 3220097 := bstep (se 2 (by rfl) ⟨1207536, by rfl⟩ : syracuseStep 3220097 = 2415073) B2415073
theorem B2146731 : Blo 2145435 2146731 := bstep (se 1 (by rfl) ⟨1610048, by rfl⟩ : syracuseStep 2146731 = 3220097) B3220097
theorem B5433925 : Blo 2145435 5433925 := bbase (se 4 (by rfl) ⟨509430, by rfl⟩ : syracuseStep 5433925 = 1018861) (by norm_num)
theorem B7245233 : Blo 2145435 7245233 := bstep (se 2 (by rfl) ⟨2716962, by rfl⟩ : syracuseStep 7245233 = 5433925) B5433925
theorem B4830155 : Blo 2145435 4830155 := bstep (se 1 (by rfl) ⟨3622616, by rfl⟩ : syracuseStep 4830155 = 7245233) B7245233
theorem B3220103 : Blo 2145435 3220103 := bstep (se 1 (by rfl) ⟨2415077, by rfl⟩ : syracuseStep 3220103 = 4830155) B4830155
theorem B2146735 : Blo 2145435 2146735 := bstep (se 1 (by rfl) ⟨1610051, by rfl⟩ : syracuseStep 2146735 = 3220103) B3220103
theorem B3220109 : Blo 2145435 3220109 := bbase (se 3 (by rfl) ⟨603770, by rfl⟩ : syracuseStep 3220109 = 1207541) (by norm_num)
theorem B2146739 : Blo 2145435 2146739 := bstep (se 1 (by rfl) ⟨1610054, by rfl⟩ : syracuseStep 2146739 = 3220109) B3220109
theorem B4830173 : Blo 2145435 4830173 := bbase (se 3 (by rfl) ⟨905657, by rfl⟩ : syracuseStep 4830173 = 1811315) (by norm_num)
theorem B3220115 : Blo 2145435 3220115 := bstep (se 1 (by rfl) ⟨2415086, by rfl⟩ : syracuseStep 3220115 = 4830173) B4830173
theorem B2146743 : Blo 2145435 2146743 := bstep (se 1 (by rfl) ⟨1610057, by rfl⟩ : syracuseStep 2146743 = 3220115) B3220115
theorem B3622637 : Blo 2145435 3622637 := bbase (se 3 (by rfl) ⟨679244, by rfl⟩ : syracuseStep 3622637 = 1358489) (by norm_num)
theorem B2415091 : Blo 2145435 2415091 := bstep (se 1 (by rfl) ⟨1811318, by rfl⟩ : syracuseStep 2415091 = 3622637) B3622637
theorem B3220121 : Blo 2145435 3220121 := bstep (se 2 (by rfl) ⟨1207545, by rfl⟩ : syracuseStep 3220121 = 2415091) B2415091
theorem B2146747 : Blo 2145435 2146747 := bstep (se 1 (by rfl) ⟨1610060, by rfl⟩ : syracuseStep 2146747 = 3220121) B3220121
theorem B3868517 : Blo 2145435 3868517 := bbase (se 4 (by rfl) ⟨362673, by rfl⟩ : syracuseStep 3868517 = 725347) (by norm_num)
theorem B10316045 : Blo 2145435 10316045 := bstep (se 3 (by rfl) ⟨1934258, by rfl⟩ : syracuseStep 10316045 = 3868517) B3868517
theorem B27509453 : Blo 2145435 27509453 := bstep (se 3 (by rfl) ⟨5158022, by rfl⟩ : syracuseStep 27509453 = 10316045) B10316045
theorem B18339635 : Blo 2145435 18339635 := bstep (se 1 (by rfl) ⟨13754726, by rfl⟩ : syracuseStep 18339635 = 27509453) B27509453
theorem B12226423 : Blo 2145435 12226423 := bstep (se 1 (by rfl) ⟨9169817, by rfl⟩ : syracuseStep 12226423 = 18339635) B18339635
theorem B16301897 : Blo 2145435 16301897 := bstep (se 2 (by rfl) ⟨6113211, by rfl⟩ : syracuseStep 16301897 = 12226423) B12226423
theorem B10867931 : Blo 2145435 10867931 := bstep (se 1 (by rfl) ⟨8150948, by rfl⟩ : syracuseStep 10867931 = 16301897) B16301897
theorem B7245287 : Blo 2145435 7245287 := bstep (se 1 (by rfl) ⟨5433965, by rfl⟩ : syracuseStep 7245287 = 10867931) B10867931
theorem B4830191 : Blo 2145435 4830191 := bstep (se 1 (by rfl) ⟨3622643, by rfl⟩ : syracuseStep 4830191 = 7245287) B7245287
theorem B3220127 : Blo 2145435 3220127 := bstep (se 1 (by rfl) ⟨2415095, by rfl⟩ : syracuseStep 3220127 = 4830191) B4830191
theorem B2146751 : Blo 2145435 2146751 := bstep (se 1 (by rfl) ⟨1610063, by rfl⟩ : syracuseStep 2146751 = 3220127) B3220127
theorem B3220133 : Blo 2145435 3220133 := bbase (se 4 (by rfl) ⟨301887, by rfl⟩ : syracuseStep 3220133 = 603775) (by norm_num)
theorem B2146755 : Blo 2145435 2146755 := bstep (se 1 (by rfl) ⟨1610066, by rfl⟩ : syracuseStep 2146755 = 3220133) B3220133
theorem B2716993 : Blo 2145435 2716993 := bbase (se 2 (by rfl) ⟨1018872, by rfl⟩ : syracuseStep 2716993 = 2037745) (by norm_num)
theorem B3622657 : Blo 2145435 3622657 := bstep (se 2 (by rfl) ⟨1358496, by rfl⟩ : syracuseStep 3622657 = 2716993) B2716993
theorem B4830209 : Blo 2145435 4830209 := bstep (se 2 (by rfl) ⟨1811328, by rfl⟩ : syracuseStep 4830209 = 3622657) B3622657
theorem B3220139 : Blo 2145435 3220139 := bstep (se 1 (by rfl) ⟨2415104, by rfl⟩ : syracuseStep 3220139 = 4830209) B4830209
theorem B2146759 : Blo 2145435 2146759 := bstep (se 1 (by rfl) ⟨1610069, by rfl⟩ : syracuseStep 2146759 = 3220139) B3220139
theorem B2415109 : Blo 2145435 2415109 := bbase (se 4 (by rfl) ⟨226416, by rfl⟩ : syracuseStep 2415109 = 452833) (by norm_num)
theorem B3220145 : Blo 2145435 3220145 := bstep (se 2 (by rfl) ⟨1207554, by rfl⟩ : syracuseStep 3220145 = 2415109) B2415109
theorem B2146763 : Blo 2145435 2146763 := bstep (se 1 (by rfl) ⟨1610072, by rfl⟩ : syracuseStep 2146763 = 3220145) B3220145
theorem B3056629 : Blo 2145435 3056629 := bbase (se 5 (by rfl) ⟨143279, by rfl⟩ : syracuseStep 3056629 = 286559) (by norm_num)
theorem B4075505 : Blo 2145435 4075505 := bstep (se 2 (by rfl) ⟨1528314, by rfl⟩ : syracuseStep 4075505 = 3056629) B3056629
theorem B2717003 : Blo 2145435 2717003 := bstep (se 1 (by rfl) ⟨2037752, by rfl⟩ : syracuseStep 2717003 = 4075505) B4075505
theorem B7245341 : Blo 2145435 7245341 := bstep (se 3 (by rfl) ⟨1358501, by rfl⟩ : syracuseStep 7245341 = 2717003) B2717003
theorem B4830227 : Blo 2145435 4830227 := bstep (se 1 (by rfl) ⟨3622670, by rfl⟩ : syracuseStep 4830227 = 7245341) B7245341
theorem B3220151 : Blo 2145435 3220151 := bstep (se 1 (by rfl) ⟨2415113, by rfl⟩ : syracuseStep 3220151 = 4830227) B4830227
theorem B2146767 : Blo 2145435 2146767 := bstep (se 1 (by rfl) ⟨1610075, by rfl⟩ : syracuseStep 2146767 = 3220151) B3220151
theorem B3220157 : Blo 2145435 3220157 := bbase (se 3 (by rfl) ⟨603779, by rfl⟩ : syracuseStep 3220157 = 1207559) (by norm_num)
theorem B2146771 : Blo 2145435 2146771 := bstep (se 1 (by rfl) ⟨1610078, by rfl⟩ : syracuseStep 2146771 = 3220157) B3220157
theorem B4830245 : Blo 2145435 4830245 := bbase (se 4 (by rfl) ⟨452835, by rfl⟩ : syracuseStep 4830245 = 905671) (by norm_num)
theorem B3220163 : Blo 2145435 3220163 := bstep (se 1 (by rfl) ⟨2415122, by rfl⟩ : syracuseStep 3220163 = 4830245) B4830245
theorem B2146775 : Blo 2145435 2146775 := bstep (se 1 (by rfl) ⟨1610081, by rfl⟩ : syracuseStep 2146775 = 3220163) B3220163
theorem B5434037 : Blo 2145435 5434037 := bbase (se 5 (by rfl) ⟨254720, by rfl⟩ : syracuseStep 5434037 = 509441) (by norm_num)
theorem B3622691 : Blo 2145435 3622691 := bstep (se 1 (by rfl) ⟨2717018, by rfl⟩ : syracuseStep 3622691 = 5434037) B5434037
theorem B2415127 : Blo 2145435 2415127 := bstep (se 1 (by rfl) ⟨1811345, by rfl⟩ : syracuseStep 2415127 = 3622691) B3622691
theorem B3220169 : Blo 2145435 3220169 := bstep (se 2 (by rfl) ⟨1207563, by rfl⟩ : syracuseStep 3220169 = 2415127) B2415127
theorem B2146779 : Blo 2145435 2146779 := bstep (se 1 (by rfl) ⟨1610084, by rfl⟩ : syracuseStep 2146779 = 3220169) B3220169
theorem B13754933 : Blo 2145435 13754933 := bbase (se 5 (by rfl) ⟨644762, by rfl⟩ : syracuseStep 13754933 = 1289525) (by norm_num)
theorem B9169955 : Blo 2145435 9169955 := bstep (se 1 (by rfl) ⟨6877466, by rfl⟩ : syracuseStep 9169955 = 13754933) B13754933
theorem B6113303 : Blo 2145435 6113303 := bstep (se 1 (by rfl) ⟨4584977, by rfl⟩ : syracuseStep 6113303 = 9169955) B9169955
theorem B4075535 : Blo 2145435 4075535 := bstep (se 1 (by rfl) ⟨3056651, by rfl⟩ : syracuseStep 4075535 = 6113303) B6113303
theorem B10868093 : Blo 2145435 10868093 := bstep (se 3 (by rfl) ⟨2037767, by rfl⟩ : syracuseStep 10868093 = 4075535) B4075535
theorem B7245395 : Blo 2145435 7245395 := bstep (se 1 (by rfl) ⟨5434046, by rfl⟩ : syracuseStep 7245395 = 10868093) B10868093
theorem B4830263 : Blo 2145435 4830263 := bstep (se 1 (by rfl) ⟨3622697, by rfl⟩ : syracuseStep 4830263 = 7245395) B7245395
theorem B3220175 : Blo 2145435 3220175 := bstep (se 1 (by rfl) ⟨2415131, by rfl⟩ : syracuseStep 3220175 = 4830263) B4830263
theorem B2146783 : Blo 2145435 2146783 := bstep (se 1 (by rfl) ⟨1610087, by rfl⟩ : syracuseStep 2146783 = 3220175) B3220175
theorem B3220181 : Blo 2145435 3220181 := bbase (se 7 (by rfl) ⟨37736, by rfl⟩ : syracuseStep 3220181 = 75473) (by norm_num)
theorem B2146787 : Blo 2145435 2146787 := bstep (se 1 (by rfl) ⟨1610090, by rfl⟩ : syracuseStep 2146787 = 3220181) B3220181
theorem B6877493 : Blo 2145435 6877493 := bbase (se 5 (by rfl) ⟨322382, by rfl⟩ : syracuseStep 6877493 = 644765) (by norm_num)
theorem B4584995 : Blo 2145435 4584995 := bstep (se 1 (by rfl) ⟨3438746, by rfl⟩ : syracuseStep 4584995 = 6877493) B6877493
theorem B3056663 : Blo 2145435 3056663 := bstep (se 1 (by rfl) ⟨2292497, by rfl⟩ : syracuseStep 3056663 = 4584995) B4584995
theorem B8151101 : Blo 2145435 8151101 := bstep (se 3 (by rfl) ⟨1528331, by rfl⟩ : syracuseStep 8151101 = 3056663) B3056663
theorem B5434067 : Blo 2145435 5434067 := bstep (se 1 (by rfl) ⟨4075550, by rfl⟩ : syracuseStep 5434067 = 8151101) B8151101
theorem B3622711 : Blo 2145435 3622711 := bstep (se 1 (by rfl) ⟨2717033, by rfl⟩ : syracuseStep 3622711 = 5434067) B5434067
theorem B4830281 : Blo 2145435 4830281 := bstep (se 2 (by rfl) ⟨1811355, by rfl⟩ : syracuseStep 4830281 = 3622711) B3622711
theorem B3220187 : Blo 2145435 3220187 := bstep (se 1 (by rfl) ⟨2415140, by rfl⟩ : syracuseStep 3220187 = 4830281) B4830281
theorem B2146791 : Blo 2145435 2146791 := bstep (se 1 (by rfl) ⟨1610093, by rfl⟩ : syracuseStep 2146791 = 3220187) B3220187
theorem B2415145 : Blo 2145435 2415145 := bbase (se 2 (by rfl) ⟨905679, by rfl⟩ : syracuseStep 2415145 = 1811359) (by norm_num)
theorem B3220193 : Blo 2145435 3220193 := bstep (se 2 (by rfl) ⟨1207572, by rfl⟩ : syracuseStep 3220193 = 2415145) B2415145
theorem B2146795 : Blo 2145435 2146795 := bstep (se 1 (by rfl) ⟨1610096, by rfl⟩ : syracuseStep 2146795 = 3220193) B3220193
theorem B3308669 : Blo 2145435 3308669 := bbase (se 3 (by rfl) ⟨620375, by rfl⟩ : syracuseStep 3308669 = 1240751) (by norm_num)
theorem B2205779 : Blo 2145435 2205779 := bstep (se 1 (by rfl) ⟨1654334, by rfl⟩ : syracuseStep 2205779 = 3308669) B3308669
theorem B5882077 : Blo 2145435 5882077 := bstep (se 3 (by rfl) ⟨1102889, by rfl⟩ : syracuseStep 5882077 = 2205779) B2205779
theorem B31371077 : Blo 2145435 31371077 := bstep (se 4 (by rfl) ⟨2941038, by rfl⟩ : syracuseStep 31371077 = 5882077) B5882077
theorem B20914051 : Blo 2145435 20914051 := bstep (se 1 (by rfl) ⟨15685538, by rfl⟩ : syracuseStep 20914051 = 31371077) B31371077
theorem B27885401 : Blo 2145435 27885401 := bstep (se 2 (by rfl) ⟨10457025, by rfl⟩ : syracuseStep 27885401 = 20914051) B20914051
theorem B18590267 : Blo 2145435 18590267 := bstep (se 1 (by rfl) ⟨13942700, by rfl⟩ : syracuseStep 18590267 = 27885401) B27885401
theorem B49574045 : Blo 2145435 49574045 := bstep (se 3 (by rfl) ⟨9295133, by rfl⟩ : syracuseStep 49574045 = 18590267) B18590267
theorem B132197453 : Blo 2145435 132197453 := bstep (se 3 (by rfl) ⟨24787022, by rfl⟩ : syracuseStep 132197453 = 49574045) B49574045
theorem B88131635 : Blo 2145435 88131635 := bstep (se 1 (by rfl) ⟨66098726, by rfl⟩ : syracuseStep 88131635 = 132197453) B132197453
theorem B58754423 : Blo 2145435 58754423 := bstep (se 1 (by rfl) ⟨44065817, by rfl⟩ : syracuseStep 58754423 = 88131635) B88131635
theorem B39169615 : Blo 2145435 39169615 := bstep (se 1 (by rfl) ⟨29377211, by rfl⟩ : syracuseStep 39169615 = 58754423) B58754423
theorem B52226153 : Blo 2145435 52226153 := bstep (se 2 (by rfl) ⟨19584807, by rfl⟩ : syracuseStep 52226153 = 39169615) B39169615
theorem B34817435 : Blo 2145435 34817435 := bstep (se 1 (by rfl) ⟨26113076, by rfl⟩ : syracuseStep 34817435 = 52226153) B52226153
theorem B23211623 : Blo 2145435 23211623 := bstep (se 1 (by rfl) ⟨17408717, by rfl⟩ : syracuseStep 23211623 = 34817435) B34817435
theorem B15474415 : Blo 2145435 15474415 := bstep (se 1 (by rfl) ⟨11605811, by rfl⟩ : syracuseStep 15474415 = 23211623) B23211623
theorem B20632553 : Blo 2145435 20632553 := bstep (se 2 (by rfl) ⟨7737207, by rfl⟩ : syracuseStep 20632553 = 15474415) B15474415
theorem B13755035 : Blo 2145435 13755035 := bstep (se 1 (by rfl) ⟨10316276, by rfl⟩ : syracuseStep 13755035 = 20632553) B20632553
theorem B9170023 : Blo 2145435 9170023 := bstep (se 1 (by rfl) ⟨6877517, by rfl⟩ : syracuseStep 9170023 = 13755035) B13755035
theorem B12226697 : Blo 2145435 12226697 := bstep (se 2 (by rfl) ⟨4585011, by rfl⟩ : syracuseStep 12226697 = 9170023) B9170023
theorem B8151131 : Blo 2145435 8151131 := bstep (se 1 (by rfl) ⟨6113348, by rfl⟩ : syracuseStep 8151131 = 12226697) B12226697
theorem B5434087 : Blo 2145435 5434087 := bstep (se 1 (by rfl) ⟨4075565, by rfl⟩ : syracuseStep 5434087 = 8151131) B8151131
theorem B7245449 : Blo 2145435 7245449 := bstep (se 2 (by rfl) ⟨2717043, by rfl⟩ : syracuseStep 7245449 = 5434087) B5434087
theorem B4830299 : Blo 2145435 4830299 := bstep (se 1 (by rfl) ⟨3622724, by rfl⟩ : syracuseStep 4830299 = 7245449) B7245449
theorem B3220199 : Blo 2145435 3220199 := bstep (se 1 (by rfl) ⟨2415149, by rfl⟩ : syracuseStep 3220199 = 4830299) B4830299
theorem B2146799 : Blo 2145435 2146799 := bstep (se 1 (by rfl) ⟨1610099, by rfl⟩ : syracuseStep 2146799 = 3220199) B3220199
theorem B3220205 : Blo 2145435 3220205 := bbase (se 3 (by rfl) ⟨603788, by rfl⟩ : syracuseStep 3220205 = 1207577) (by norm_num)
theorem B2146803 : Blo 2145435 2146803 := bstep (se 1 (by rfl) ⟨1610102, by rfl⟩ : syracuseStep 2146803 = 3220205) B3220205
theorem B4830317 : Blo 2145435 4830317 := bbase (se 3 (by rfl) ⟨905684, by rfl⟩ : syracuseStep 4830317 = 1811369) (by norm_num)
theorem B3220211 : Blo 2145435 3220211 := bstep (se 1 (by rfl) ⟨2415158, by rfl⟩ : syracuseStep 3220211 = 4830317) B4830317
theorem B2146807 : Blo 2145435 2146807 := bstep (se 1 (by rfl) ⟨1610105, by rfl⟩ : syracuseStep 2146807 = 3220211) B3220211
theorem B4075589 : Blo 2145435 4075589 := bbase (se 4 (by rfl) ⟨382086, by rfl⟩ : syracuseStep 4075589 = 764173) (by norm_num)
theorem B2717059 : Blo 2145435 2717059 := bstep (se 1 (by rfl) ⟨2037794, by rfl⟩ : syracuseStep 2717059 = 4075589) B4075589
theorem B3622745 : Blo 2145435 3622745 := bstep (se 2 (by rfl) ⟨1358529, by rfl⟩ : syracuseStep 3622745 = 2717059) B2717059
theorem B2415163 : Blo 2145435 2415163 := bstep (se 1 (by rfl) ⟨1811372, by rfl⟩ : syracuseStep 2415163 = 3622745) B3622745
theorem B3220217 : Blo 2145435 3220217 := bstep (se 2 (by rfl) ⟨1207581, by rfl⟩ : syracuseStep 3220217 = 2415163) B2415163
theorem B2146811 : Blo 2145435 2146811 := bstep (se 1 (by rfl) ⟨1610108, by rfl⟩ : syracuseStep 2146811 = 3220217) B3220217
theorem B5508269 : Blo 2145435 5508269 := bbase (se 3 (by rfl) ⟨1032800, by rfl⟩ : syracuseStep 5508269 = 2065601) (by norm_num)
theorem B3672179 : Blo 2145435 3672179 := bstep (se 1 (by rfl) ⟨2754134, by rfl⟩ : syracuseStep 3672179 = 5508269) B5508269
theorem B2448119 : Blo 2145435 2448119 := bstep (se 1 (by rfl) ⟨1836089, by rfl⟩ : syracuseStep 2448119 = 3672179) B3672179
theorem B6528317 : Blo 2145435 6528317 := bstep (se 3 (by rfl) ⟨1224059, by rfl⟩ : syracuseStep 6528317 = 2448119) B2448119
theorem B17408845 : Blo 2145435 17408845 := bstep (se 3 (by rfl) ⟨3264158, by rfl⟩ : syracuseStep 17408845 = 6528317) B6528317
theorem B23211793 : Blo 2145435 23211793 := bstep (se 2 (by rfl) ⟨8704422, by rfl⟩ : syracuseStep 23211793 = 17408845) B17408845
theorem B30949057 : Blo 2145435 30949057 := bstep (se 2 (by rfl) ⟨11605896, by rfl⟩ : syracuseStep 30949057 = 23211793) B23211793
theorem B41265409 : Blo 2145435 41265409 := bstep (se 2 (by rfl) ⟨15474528, by rfl⟩ : syracuseStep 41265409 = 30949057) B30949057
theorem B55020545 : Blo 2145435 55020545 := bstep (se 2 (by rfl) ⟨20632704, by rfl⟩ : syracuseStep 55020545 = 41265409) B41265409
theorem B36680363 : Blo 2145435 36680363 := bstep (se 1 (by rfl) ⟨27510272, by rfl⟩ : syracuseStep 36680363 = 55020545) B55020545
theorem B24453575 : Blo 2145435 24453575 := bstep (se 1 (by rfl) ⟨18340181, by rfl⟩ : syracuseStep 24453575 = 36680363) B36680363
theorem B16302383 : Blo 2145435 16302383 := bstep (se 1 (by rfl) ⟨12226787, by rfl⟩ : syracuseStep 16302383 = 24453575) B24453575
theorem B10868255 : Blo 2145435 10868255 := bstep (se 1 (by rfl) ⟨8151191, by rfl⟩ : syracuseStep 10868255 = 16302383) B16302383
theorem B7245503 : Blo 2145435 7245503 := bstep (se 1 (by rfl) ⟨5434127, by rfl⟩ : syracuseStep 7245503 = 10868255) B10868255
theorem B4830335 : Blo 2145435 4830335 := bstep (se 1 (by rfl) ⟨3622751, by rfl⟩ : syracuseStep 4830335 = 7245503) B7245503
theorem B3220223 : Blo 2145435 3220223 := bstep (se 1 (by rfl) ⟨2415167, by rfl⟩ : syracuseStep 3220223 = 4830335) B4830335
theorem B2146815 : Blo 2145435 2146815 := bstep (se 1 (by rfl) ⟨1610111, by rfl⟩ : syracuseStep 2146815 = 3220223) B3220223
theorem B3220229 : Blo 2145435 3220229 := bbase (se 4 (by rfl) ⟨301896, by rfl⟩ : syracuseStep 3220229 = 603793) (by norm_num)
theorem B2146819 : Blo 2145435 2146819 := bstep (se 1 (by rfl) ⟨1610114, by rfl⟩ : syracuseStep 2146819 = 3220229) B3220229
theorem B3622765 : Blo 2145435 3622765 := bbase (se 3 (by rfl) ⟨679268, by rfl⟩ : syracuseStep 3622765 = 1358537) (by norm_num)
theorem B4830353 : Blo 2145435 4830353 := bstep (se 2 (by rfl) ⟨1811382, by rfl⟩ : syracuseStep 4830353 = 3622765) B3622765
theorem B3220235 : Blo 2145435 3220235 := bstep (se 1 (by rfl) ⟨2415176, by rfl⟩ : syracuseStep 3220235 = 4830353) B4830353
theorem B2146823 : Blo 2145435 2146823 := bstep (se 1 (by rfl) ⟨1610117, by rfl⟩ : syracuseStep 2146823 = 3220235) B3220235
theorem B2415181 : Blo 2145435 2415181 := bbase (se 3 (by rfl) ⟨452846, by rfl⟩ : syracuseStep 2415181 = 905693) (by norm_num)
theorem B3220241 : Blo 2145435 3220241 := bstep (se 2 (by rfl) ⟨1207590, by rfl⟩ : syracuseStep 3220241 = 2415181) B2415181
theorem B2146827 : Blo 2145435 2146827 := bstep (se 1 (by rfl) ⟨1610120, by rfl⟩ : syracuseStep 2146827 = 3220241) B3220241
theorem B7245557 : Blo 2145435 7245557 := bbase (se 5 (by rfl) ⟨339635, by rfl⟩ : syracuseStep 7245557 = 679271) (by norm_num)
theorem B4830371 : Blo 2145435 4830371 := bstep (se 1 (by rfl) ⟨3622778, by rfl⟩ : syracuseStep 4830371 = 7245557) B7245557
theorem B3220247 : Blo 2145435 3220247 := bstep (se 1 (by rfl) ⟨2415185, by rfl⟩ : syracuseStep 3220247 = 4830371) B4830371
theorem B2146831 : Blo 2145435 2146831 := bstep (se 1 (by rfl) ⟨1610123, by rfl⟩ : syracuseStep 2146831 = 3220247) B3220247
theorem B3220253 : Blo 2145435 3220253 := bbase (se 3 (by rfl) ⟨603797, by rfl⟩ : syracuseStep 3220253 = 1207595) (by norm_num)
theorem B2146835 : Blo 2145435 2146835 := bstep (se 1 (by rfl) ⟨1610126, by rfl⟩ : syracuseStep 2146835 = 3220253) B3220253
theorem B4830389 : Blo 2145435 4830389 := bbase (se 5 (by rfl) ⟨226424, by rfl⟩ : syracuseStep 4830389 = 452849) (by norm_num)
theorem B3220259 : Blo 2145435 3220259 := bstep (se 1 (by rfl) ⟨2415194, by rfl⟩ : syracuseStep 3220259 = 4830389) B4830389
theorem B2146839 : Blo 2145435 2146839 := bstep (se 1 (by rfl) ⟨1610129, by rfl⟩ : syracuseStep 2146839 = 3220259) B3220259
theorem B2292553 : Blo 2145435 2292553 := bbase (se 2 (by rfl) ⟨859707, by rfl⟩ : syracuseStep 2292553 = 1719415) (by norm_num)
theorem B12226949 : Blo 2145435 12226949 := bstep (se 4 (by rfl) ⟨1146276, by rfl⟩ : syracuseStep 12226949 = 2292553) B2292553
theorem B8151299 : Blo 2145435 8151299 := bstep (se 1 (by rfl) ⟨6113474, by rfl⟩ : syracuseStep 8151299 = 12226949) B12226949
theorem B5434199 : Blo 2145435 5434199 := bstep (se 1 (by rfl) ⟨4075649, by rfl⟩ : syracuseStep 5434199 = 8151299) B8151299
theorem B3622799 : Blo 2145435 3622799 := bstep (se 1 (by rfl) ⟨2717099, by rfl⟩ : syracuseStep 3622799 = 5434199) B5434199
theorem B2415199 : Blo 2145435 2415199 := bstep (se 1 (by rfl) ⟨1811399, by rfl⟩ : syracuseStep 2415199 = 3622799) B3622799
theorem B3220265 : Blo 2145435 3220265 := bstep (se 2 (by rfl) ⟨1207599, by rfl⟩ : syracuseStep 3220265 = 2415199) B2415199
theorem B2146843 : Blo 2145435 2146843 := bstep (se 1 (by rfl) ⟨1610132, by rfl⟩ : syracuseStep 2146843 = 3220265) B3220265
theorem B2292557 : Blo 2145435 2292557 := bbase (se 3 (by rfl) ⟨429854, by rfl⟩ : syracuseStep 2292557 = 859709) (by norm_num)
theorem B6113485 : Blo 2145435 6113485 := bstep (se 3 (by rfl) ⟨1146278, by rfl⟩ : syracuseStep 6113485 = 2292557) B2292557
theorem B8151313 : Blo 2145435 8151313 := bstep (se 2 (by rfl) ⟨3056742, by rfl⟩ : syracuseStep 8151313 = 6113485) B6113485
theorem B10868417 : Blo 2145435 10868417 := bstep (se 2 (by rfl) ⟨4075656, by rfl⟩ : syracuseStep 10868417 = 8151313) B8151313
theorem B7245611 : Blo 2145435 7245611 := bstep (se 1 (by rfl) ⟨5434208, by rfl⟩ : syracuseStep 7245611 = 10868417) B10868417
theorem B4830407 : Blo 2145435 4830407 := bstep (se 1 (by rfl) ⟨3622805, by rfl⟩ : syracuseStep 4830407 = 7245611) B7245611
theorem B3220271 : Blo 2145435 3220271 := bstep (se 1 (by rfl) ⟨2415203, by rfl⟩ : syracuseStep 3220271 = 4830407) B4830407
theorem B2146847 : Blo 2145435 2146847 := bstep (se 1 (by rfl) ⟨1610135, by rfl⟩ : syracuseStep 2146847 = 3220271) B3220271
theorem B3220277 : Blo 2145435 3220277 := bbase (se 5 (by rfl) ⟨150950, by rfl⟩ : syracuseStep 3220277 = 301901) (by norm_num)
theorem B2146851 : Blo 2145435 2146851 := bstep (se 1 (by rfl) ⟨1610138, by rfl⟩ : syracuseStep 2146851 = 3220277) B3220277
theorem B5434229 : Blo 2145435 5434229 := bbase (se 5 (by rfl) ⟨254729, by rfl⟩ : syracuseStep 5434229 = 509459) (by norm_num)
theorem B3622819 : Blo 2145435 3622819 := bstep (se 1 (by rfl) ⟨2717114, by rfl⟩ : syracuseStep 3622819 = 5434229) B5434229
theorem B4830425 : Blo 2145435 4830425 := bstep (se 2 (by rfl) ⟨1811409, by rfl⟩ : syracuseStep 4830425 = 3622819) B3622819
theorem B3220283 : Blo 2145435 3220283 := bstep (se 1 (by rfl) ⟨2415212, by rfl⟩ : syracuseStep 3220283 = 4830425) B4830425
theorem B2146855 : Blo 2145435 2146855 := bstep (se 1 (by rfl) ⟨1610141, by rfl⟩ : syracuseStep 2146855 = 3220283) B3220283
theorem B2415217 : Blo 2145435 2415217 := bbase (se 2 (by rfl) ⟨905706, by rfl⟩ : syracuseStep 2415217 = 1811413) (by norm_num)
theorem B3220289 : Blo 2145435 3220289 := bstep (se 2 (by rfl) ⟨1207608, by rfl⟩ : syracuseStep 3220289 = 2415217) B2415217
theorem B2146859 : Blo 2145435 2146859 := bstep (se 1 (by rfl) ⟨1610144, by rfl⟩ : syracuseStep 2146859 = 3220289) B3220289
theorem B20123477 : Blo 2145435 20123477 := bbase (se 9 (by rfl) ⟨58955, by rfl⟩ : syracuseStep 20123477 = 117911) (by norm_num)
theorem B13415651 : Blo 2145435 13415651 := bstep (se 1 (by rfl) ⟨10061738, by rfl⟩ : syracuseStep 13415651 = 20123477) B20123477
theorem B8943767 : Blo 2145435 8943767 := bstep (se 1 (by rfl) ⟨6707825, by rfl⟩ : syracuseStep 8943767 = 13415651) B13415651
theorem B5962511 : Blo 2145435 5962511 := bstep (se 1 (by rfl) ⟨4471883, by rfl⟩ : syracuseStep 5962511 = 8943767) B8943767
theorem B3975007 : Blo 2145435 3975007 := bstep (se 1 (by rfl) ⟨2981255, by rfl⟩ : syracuseStep 3975007 = 5962511) B5962511
theorem B5300009 : Blo 2145435 5300009 := bstep (se 2 (by rfl) ⟨1987503, by rfl⟩ : syracuseStep 5300009 = 3975007) B3975007
theorem B3533339 : Blo 2145435 3533339 := bstep (se 1 (by rfl) ⟨2650004, by rfl⟩ : syracuseStep 3533339 = 5300009) B5300009
theorem B9422237 : Blo 2145435 9422237 := bstep (se 3 (by rfl) ⟨1766669, by rfl⟩ : syracuseStep 9422237 = 3533339) B3533339
theorem B25125965 : Blo 2145435 25125965 := bstep (se 3 (by rfl) ⟨4711118, by rfl⟩ : syracuseStep 25125965 = 9422237) B9422237
theorem B16750643 : Blo 2145435 16750643 := bstep (se 1 (by rfl) ⟨12562982, by rfl⟩ : syracuseStep 16750643 = 25125965) B25125965
theorem B44668381 : Blo 2145435 44668381 := bstep (se 3 (by rfl) ⟨8375321, by rfl⟩ : syracuseStep 44668381 = 16750643) B16750643
theorem B59557841 : Blo 2145435 59557841 := bstep (se 2 (by rfl) ⟨22334190, by rfl⟩ : syracuseStep 59557841 = 44668381) B44668381
theorem B39705227 : Blo 2145435 39705227 := bstep (se 1 (by rfl) ⟨29778920, by rfl⟩ : syracuseStep 39705227 = 59557841) B59557841
theorem B26470151 : Blo 2145435 26470151 := bstep (se 1 (by rfl) ⟨19852613, by rfl⟩ : syracuseStep 26470151 = 39705227) B39705227
theorem B17646767 : Blo 2145435 17646767 := bstep (se 1 (by rfl) ⟨13235075, by rfl⟩ : syracuseStep 17646767 = 26470151) B26470151
theorem B11764511 : Blo 2145435 11764511 := bstep (se 1 (by rfl) ⟨8823383, by rfl⟩ : syracuseStep 11764511 = 17646767) B17646767
theorem B7843007 : Blo 2145435 7843007 := bstep (se 1 (by rfl) ⟨5882255, by rfl⟩ : syracuseStep 7843007 = 11764511) B11764511
theorem B5228671 : Blo 2145435 5228671 := bstep (se 1 (by rfl) ⟨3921503, by rfl⟩ : syracuseStep 5228671 = 7843007) B7843007
theorem B6971561 : Blo 2145435 6971561 := bstep (se 2 (by rfl) ⟨2614335, by rfl⟩ : syracuseStep 6971561 = 5228671) B5228671
theorem B4647707 : Blo 2145435 4647707 := bstep (se 1 (by rfl) ⟨3485780, by rfl⟩ : syracuseStep 4647707 = 6971561) B6971561
theorem B3098471 : Blo 2145435 3098471 := bstep (se 1 (by rfl) ⟨2323853, by rfl⟩ : syracuseStep 3098471 = 4647707) B4647707
theorem B8262589 : Blo 2145435 8262589 := bstep (se 3 (by rfl) ⟨1549235, by rfl⟩ : syracuseStep 8262589 = 3098471) B3098471
theorem B11016785 : Blo 2145435 11016785 := bstep (se 2 (by rfl) ⟨4131294, by rfl⟩ : syracuseStep 11016785 = 8262589) B8262589
theorem B7344523 : Blo 2145435 7344523 := bstep (se 1 (by rfl) ⟨5508392, by rfl⟩ : syracuseStep 7344523 = 11016785) B11016785
theorem B39170789 : Blo 2145435 39170789 := bstep (se 4 (by rfl) ⟨3672261, by rfl⟩ : syracuseStep 39170789 = 7344523) B7344523
theorem B26113859 : Blo 2145435 26113859 := bstep (se 1 (by rfl) ⟨19585394, by rfl⟩ : syracuseStep 26113859 = 39170789) B39170789
theorem B17409239 : Blo 2145435 17409239 := bstep (se 1 (by rfl) ⟨13056929, by rfl⟩ : syracuseStep 17409239 = 26113859) B26113859
theorem B11606159 : Blo 2145435 11606159 := bstep (se 1 (by rfl) ⟨8704619, by rfl⟩ : syracuseStep 11606159 = 17409239) B17409239
theorem B7737439 : Blo 2145435 7737439 := bstep (se 1 (by rfl) ⟨5803079, by rfl⟩ : syracuseStep 7737439 = 11606159) B11606159
theorem B10316585 : Blo 2145435 10316585 := bstep (se 2 (by rfl) ⟨3868719, by rfl⟩ : syracuseStep 10316585 = 7737439) B7737439
theorem B6877723 : Blo 2145435 6877723 := bstep (se 1 (by rfl) ⟨5158292, by rfl⟩ : syracuseStep 6877723 = 10316585) B10316585
theorem B9170297 : Blo 2145435 9170297 := bstep (se 2 (by rfl) ⟨3438861, by rfl⟩ : syracuseStep 9170297 = 6877723) B6877723
theorem B6113531 : Blo 2145435 6113531 := bstep (se 1 (by rfl) ⟨4585148, by rfl⟩ : syracuseStep 6113531 = 9170297) B9170297
theorem B4075687 : Blo 2145435 4075687 := bstep (se 1 (by rfl) ⟨3056765, by rfl⟩ : syracuseStep 4075687 = 6113531) B6113531
theorem B5434249 : Blo 2145435 5434249 := bstep (se 2 (by rfl) ⟨2037843, by rfl⟩ : syracuseStep 5434249 = 4075687) B4075687
theorem B7245665 : Blo 2145435 7245665 := bstep (se 2 (by rfl) ⟨2717124, by rfl⟩ : syracuseStep 7245665 = 5434249) B5434249
theorem B4830443 : Blo 2145435 4830443 := bstep (se 1 (by rfl) ⟨3622832, by rfl⟩ : syracuseStep 4830443 = 7245665) B7245665
theorem B3220295 : Blo 2145435 3220295 := bstep (se 1 (by rfl) ⟨2415221, by rfl⟩ : syracuseStep 3220295 = 4830443) B4830443
theorem B2146863 : Blo 2145435 2146863 := bstep (se 1 (by rfl) ⟨1610147, by rfl⟩ : syracuseStep 2146863 = 3220295) B3220295
theorem B3220301 : Blo 2145435 3220301 := bbase (se 3 (by rfl) ⟨603806, by rfl⟩ : syracuseStep 3220301 = 1207613) (by norm_num)
theorem B2146867 : Blo 2145435 2146867 := bstep (se 1 (by rfl) ⟨1610150, by rfl⟩ : syracuseStep 2146867 = 3220301) B3220301
theorem B4830461 : Blo 2145435 4830461 := bbase (se 3 (by rfl) ⟨905711, by rfl⟩ : syracuseStep 4830461 = 1811423) (by norm_num)
theorem B3220307 : Blo 2145435 3220307 := bstep (se 1 (by rfl) ⟨2415230, by rfl⟩ : syracuseStep 3220307 = 4830461) B4830461
theorem B2146871 : Blo 2145435 2146871 := bstep (se 1 (by rfl) ⟨1610153, by rfl⟩ : syracuseStep 2146871 = 3220307) B3220307
theorem B3622853 : Blo 2145435 3622853 := bbase (se 4 (by rfl) ⟨339642, by rfl⟩ : syracuseStep 3622853 = 679285) (by norm_num)
theorem B2415235 : Blo 2145435 2415235 := bstep (se 1 (by rfl) ⟨1811426, by rfl⟩ : syracuseStep 2415235 = 3622853) B3622853
theorem B3220313 : Blo 2145435 3220313 := bstep (se 2 (by rfl) ⟨1207617, by rfl⟩ : syracuseStep 3220313 = 2415235) B2415235
theorem B2146875 : Blo 2145435 2146875 := bstep (se 1 (by rfl) ⟨1610156, by rfl⟩ : syracuseStep 2146875 = 3220313) B3220313
theorem B16302869 : Blo 2145435 16302869 := bbase (se 6 (by rfl) ⟨382098, by rfl⟩ : syracuseStep 16302869 = 764197) (by norm_num)
theorem B10868579 : Blo 2145435 10868579 := bstep (se 1 (by rfl) ⟨8151434, by rfl⟩ : syracuseStep 10868579 = 16302869) B16302869
theorem B7245719 : Blo 2145435 7245719 := bstep (se 1 (by rfl) ⟨5434289, by rfl⟩ : syracuseStep 7245719 = 10868579) B10868579
theorem B4830479 : Blo 2145435 4830479 := bstep (se 1 (by rfl) ⟨3622859, by rfl⟩ : syracuseStep 4830479 = 7245719) B7245719
theorem B3220319 : Blo 2145435 3220319 := bstep (se 1 (by rfl) ⟨2415239, by rfl⟩ : syracuseStep 3220319 = 4830479) B4830479
theorem B2146879 : Blo 2145435 2146879 := bstep (se 1 (by rfl) ⟨1610159, by rfl⟩ : syracuseStep 2146879 = 3220319) B3220319
theorem B3220325 : Blo 2145435 3220325 := bbase (se 4 (by rfl) ⟨301905, by rfl⟩ : syracuseStep 3220325 = 603811) (by norm_num)
theorem B2146883 : Blo 2145435 2146883 := bstep (se 1 (by rfl) ⟨1610162, by rfl⟩ : syracuseStep 2146883 = 3220325) B3220325
theorem B4075733 : Blo 2145435 4075733 := bbase (se 7 (by rfl) ⟨47762, by rfl⟩ : syracuseStep 4075733 = 95525) (by norm_num)
theorem B2717155 : Blo 2145435 2717155 := bstep (se 1 (by rfl) ⟨2037866, by rfl⟩ : syracuseStep 2717155 = 4075733) B4075733
theorem B3622873 : Blo 2145435 3622873 := bstep (se 2 (by rfl) ⟨1358577, by rfl⟩ : syracuseStep 3622873 = 2717155) B2717155
theorem B4830497 : Blo 2145435 4830497 := bstep (se 2 (by rfl) ⟨1811436, by rfl⟩ : syracuseStep 4830497 = 3622873) B3622873
theorem B3220331 : Blo 2145435 3220331 := bstep (se 1 (by rfl) ⟨2415248, by rfl⟩ : syracuseStep 3220331 = 4830497) B4830497
theorem B2146887 : Blo 2145435 2146887 := bstep (se 1 (by rfl) ⟨1610165, by rfl⟩ : syracuseStep 2146887 = 3220331) B3220331
theorem B2415253 : Blo 2145435 2415253 := bbase (se 6 (by rfl) ⟨56607, by rfl⟩ : syracuseStep 2415253 = 113215) (by norm_num)
theorem B3220337 : Blo 2145435 3220337 := bstep (se 2 (by rfl) ⟨1207626, by rfl⟩ : syracuseStep 3220337 = 2415253) B2415253
theorem B2146891 : Blo 2145435 2146891 := bstep (se 1 (by rfl) ⟨1610168, by rfl⟩ : syracuseStep 2146891 = 3220337) B3220337
theorem B2717165 : Blo 2145435 2717165 := bbase (se 3 (by rfl) ⟨509468, by rfl⟩ : syracuseStep 2717165 = 1018937) (by norm_num)
theorem B7245773 : Blo 2145435 7245773 := bstep (se 3 (by rfl) ⟨1358582, by rfl⟩ : syracuseStep 7245773 = 2717165) B2717165
theorem B4830515 : Blo 2145435 4830515 := bstep (se 1 (by rfl) ⟨3622886, by rfl⟩ : syracuseStep 4830515 = 7245773) B7245773
theorem B3220343 : Blo 2145435 3220343 := bstep (se 1 (by rfl) ⟨2415257, by rfl⟩ : syracuseStep 3220343 = 4830515) B4830515
theorem B2146895 : Blo 2145435 2146895 := bstep (se 1 (by rfl) ⟨1610171, by rfl⟩ : syracuseStep 2146895 = 3220343) B3220343
theorem B3220349 : Blo 2145435 3220349 := bbase (se 3 (by rfl) ⟨603815, by rfl⟩ : syracuseStep 3220349 = 1207631) (by norm_num)
theorem B2146899 : Blo 2145435 2146899 := bstep (se 1 (by rfl) ⟨1610174, by rfl⟩ : syracuseStep 2146899 = 3220349) B3220349
theorem B4830533 : Blo 2145435 4830533 := bbase (se 4 (by rfl) ⟨452862, by rfl⟩ : syracuseStep 4830533 = 905725) (by norm_num)
theorem B3220355 : Blo 2145435 3220355 := bstep (se 1 (by rfl) ⟨2415266, by rfl⟩ : syracuseStep 3220355 = 4830533) B4830533
theorem B2146903 : Blo 2145435 2146903 := bstep (se 1 (by rfl) ⟨1610177, by rfl⟩ : syracuseStep 2146903 = 3220355) B3220355
theorem B5583661 : Blo 2145435 5583661 := bbase (se 3 (by rfl) ⟨1046936, by rfl⟩ : syracuseStep 5583661 = 2093873) (by norm_num)
theorem B29779525 : Blo 2145435 29779525 := bstep (se 4 (by rfl) ⟨2791830, by rfl⟩ : syracuseStep 29779525 = 5583661) B5583661
theorem B39706033 : Blo 2145435 39706033 := bstep (se 2 (by rfl) ⟨14889762, by rfl⟩ : syracuseStep 39706033 = 29779525) B29779525
theorem B52941377 : Blo 2145435 52941377 := bstep (se 2 (by rfl) ⟨19853016, by rfl⟩ : syracuseStep 52941377 = 39706033) B39706033
theorem B35294251 : Blo 2145435 35294251 := bstep (se 1 (by rfl) ⟨26470688, by rfl⟩ : syracuseStep 35294251 = 52941377) B52941377
theorem B47059001 : Blo 2145435 47059001 := bstep (se 2 (by rfl) ⟨17647125, by rfl⟩ : syracuseStep 47059001 = 35294251) B35294251
theorem B31372667 : Blo 2145435 31372667 := bstep (se 1 (by rfl) ⟨23529500, by rfl⟩ : syracuseStep 31372667 = 47059001) B47059001
theorem B20915111 : Blo 2145435 20915111 := bstep (se 1 (by rfl) ⟨15686333, by rfl⟩ : syracuseStep 20915111 = 31372667) B31372667
theorem B13943407 : Blo 2145435 13943407 := bstep (se 1 (by rfl) ⟨10457555, by rfl⟩ : syracuseStep 13943407 = 20915111) B20915111
theorem B18591209 : Blo 2145435 18591209 := bstep (se 2 (by rfl) ⟨6971703, by rfl⟩ : syracuseStep 18591209 = 13943407) B13943407
theorem B12394139 : Blo 2145435 12394139 := bstep (se 1 (by rfl) ⟨9295604, by rfl⟩ : syracuseStep 12394139 = 18591209) B18591209
theorem B132204149 : Blo 2145435 132204149 := bstep (se 5 (by rfl) ⟨6197069, by rfl⟩ : syracuseStep 132204149 = 12394139) B12394139
theorem B88136099 : Blo 2145435 88136099 := bstep (se 1 (by rfl) ⟨66102074, by rfl⟩ : syracuseStep 88136099 = 132204149) B132204149
theorem B58757399 : Blo 2145435 58757399 := bstep (se 1 (by rfl) ⟨44068049, by rfl⟩ : syracuseStep 58757399 = 88136099) B88136099
theorem B39171599 : Blo 2145435 39171599 := bstep (se 1 (by rfl) ⟨29378699, by rfl⟩ : syracuseStep 39171599 = 58757399) B58757399
theorem B26114399 : Blo 2145435 26114399 := bstep (se 1 (by rfl) ⟨19585799, by rfl⟩ : syracuseStep 26114399 = 39171599) B39171599
theorem B17409599 : Blo 2145435 17409599 := bstep (se 1 (by rfl) ⟨13057199, by rfl⟩ : syracuseStep 17409599 = 26114399) B26114399
theorem B11606399 : Blo 2145435 11606399 := bstep (se 1 (by rfl) ⟨8704799, by rfl⟩ : syracuseStep 11606399 = 17409599) B17409599
theorem B7737599 : Blo 2145435 7737599 := bstep (se 1 (by rfl) ⟨5803199, by rfl⟩ : syracuseStep 7737599 = 11606399) B11606399
theorem B5158399 : Blo 2145435 5158399 := bstep (se 1 (by rfl) ⟨3868799, by rfl⟩ : syracuseStep 5158399 = 7737599) B7737599
theorem B6877865 : Blo 2145435 6877865 := bstep (se 2 (by rfl) ⟨2579199, by rfl⟩ : syracuseStep 6877865 = 5158399) B5158399
theorem B4585243 : Blo 2145435 4585243 := bstep (se 1 (by rfl) ⟨3438932, by rfl⟩ : syracuseStep 4585243 = 6877865) B6877865
theorem B6113657 : Blo 2145435 6113657 := bstep (se 2 (by rfl) ⟨2292621, by rfl⟩ : syracuseStep 6113657 = 4585243) B4585243
theorem B4075771 : Blo 2145435 4075771 := bstep (se 1 (by rfl) ⟨3056828, by rfl⟩ : syracuseStep 4075771 = 6113657) B6113657
theorem B5434361 : Blo 2145435 5434361 := bstep (se 2 (by rfl) ⟨2037885, by rfl⟩ : syracuseStep 5434361 = 4075771) B4075771
theorem B3622907 : Blo 2145435 3622907 := bstep (se 1 (by rfl) ⟨2717180, by rfl⟩ : syracuseStep 3622907 = 5434361) B5434361
theorem B2415271 : Blo 2145435 2415271 := bstep (se 1 (by rfl) ⟨1811453, by rfl⟩ : syracuseStep 2415271 = 3622907) B3622907
theorem B3220361 : Blo 2145435 3220361 := bstep (se 2 (by rfl) ⟨1207635, by rfl⟩ : syracuseStep 3220361 = 2415271) B2415271
theorem B2146907 : Blo 2145435 2146907 := bstep (se 1 (by rfl) ⟨1610180, by rfl⟩ : syracuseStep 2146907 = 3220361) B3220361
theorem B10868741 : Blo 2145435 10868741 := bbase (se 4 (by rfl) ⟨1018944, by rfl⟩ : syracuseStep 10868741 = 2037889) (by norm_num)
theorem B7245827 : Blo 2145435 7245827 := bstep (se 1 (by rfl) ⟨5434370, by rfl⟩ : syracuseStep 7245827 = 10868741) B10868741
theorem B4830551 : Blo 2145435 4830551 := bstep (se 1 (by rfl) ⟨3622913, by rfl⟩ : syracuseStep 4830551 = 7245827) B7245827
theorem B3220367 : Blo 2145435 3220367 := bstep (se 1 (by rfl) ⟨2415275, by rfl⟩ : syracuseStep 3220367 = 4830551) B4830551
theorem B2146911 : Blo 2145435 2146911 := bstep (se 1 (by rfl) ⟨1610183, by rfl⟩ : syracuseStep 2146911 = 3220367) B3220367
theorem B3220373 : Blo 2145435 3220373 := bbase (se 6 (by rfl) ⟨75477, by rfl⟩ : syracuseStep 3220373 = 150955) (by norm_num)
theorem B2146915 : Blo 2145435 2146915 := bstep (se 1 (by rfl) ⟨1610186, by rfl⟩ : syracuseStep 2146915 = 3220373) B3220373
theorem B12227381 : Blo 2145435 12227381 := bbase (se 5 (by rfl) ⟨573158, by rfl⟩ : syracuseStep 12227381 = 1146317) (by norm_num)
theorem B8151587 : Blo 2145435 8151587 := bstep (se 1 (by rfl) ⟨6113690, by rfl⟩ : syracuseStep 8151587 = 12227381) B12227381
theorem B5434391 : Blo 2145435 5434391 := bstep (se 1 (by rfl) ⟨4075793, by rfl⟩ : syracuseStep 5434391 = 8151587) B8151587
theorem B3622927 : Blo 2145435 3622927 := bstep (se 1 (by rfl) ⟨2717195, by rfl⟩ : syracuseStep 3622927 = 5434391) B5434391
theorem B4830569 : Blo 2145435 4830569 := bstep (se 2 (by rfl) ⟨1811463, by rfl⟩ : syracuseStep 4830569 = 3622927) B3622927
theorem B3220379 : Blo 2145435 3220379 := bstep (se 1 (by rfl) ⟨2415284, by rfl⟩ : syracuseStep 3220379 = 4830569) B4830569
theorem B2146919 : Blo 2145435 2146919 := bstep (se 1 (by rfl) ⟨1610189, by rfl⟩ : syracuseStep 2146919 = 3220379) B3220379
theorem B2415289 : Blo 2145435 2415289 := bbase (se 2 (by rfl) ⟨905733, by rfl⟩ : syracuseStep 2415289 = 1811467) (by norm_num)
theorem B3220385 : Blo 2145435 3220385 := bstep (se 2 (by rfl) ⟨1207644, by rfl⟩ : syracuseStep 3220385 = 2415289) B2415289
theorem B2146923 : Blo 2145435 2146923 := bstep (se 1 (by rfl) ⟨1610192, by rfl⟩ : syracuseStep 2146923 = 3220385) B3220385
theorem B4585285 : Blo 2145435 4585285 := bbase (se 4 (by rfl) ⟨429870, by rfl⟩ : syracuseStep 4585285 = 859741) (by norm_num)
theorem B6113713 : Blo 2145435 6113713 := bstep (se 2 (by rfl) ⟨2292642, by rfl⟩ : syracuseStep 6113713 = 4585285) B4585285
theorem B8151617 : Blo 2145435 8151617 := bstep (se 2 (by rfl) ⟨3056856, by rfl⟩ : syracuseStep 8151617 = 6113713) B6113713
theorem B5434411 : Blo 2145435 5434411 := bstep (se 1 (by rfl) ⟨4075808, by rfl⟩ : syracuseStep 5434411 = 8151617) B8151617
theorem B7245881 : Blo 2145435 7245881 := bstep (se 2 (by rfl) ⟨2717205, by rfl⟩ : syracuseStep 7245881 = 5434411) B5434411
theorem B4830587 : Blo 2145435 4830587 := bstep (se 1 (by rfl) ⟨3622940, by rfl⟩ : syracuseStep 4830587 = 7245881) B7245881
theorem B3220391 : Blo 2145435 3220391 := bstep (se 1 (by rfl) ⟨2415293, by rfl⟩ : syracuseStep 3220391 = 4830587) B4830587
theorem B2146927 : Blo 2145435 2146927 := bstep (se 1 (by rfl) ⟨1610195, by rfl⟩ : syracuseStep 2146927 = 3220391) B3220391
theorem B3220397 : Blo 2145435 3220397 := bbase (se 3 (by rfl) ⟨603824, by rfl⟩ : syracuseStep 3220397 = 1207649) (by norm_num)
theorem B2146931 : Blo 2145435 2146931 := bstep (se 1 (by rfl) ⟨1610198, by rfl⟩ : syracuseStep 2146931 = 3220397) B3220397
theorem B4830605 : Blo 2145435 4830605 := bbase (se 3 (by rfl) ⟨905738, by rfl⟩ : syracuseStep 4830605 = 1811477) (by norm_num)
theorem B3220403 : Blo 2145435 3220403 := bstep (se 1 (by rfl) ⟨2415302, by rfl⟩ : syracuseStep 3220403 = 4830605) B4830605
theorem B2146935 : Blo 2145435 2146935 := bstep (se 1 (by rfl) ⟨1610201, by rfl⟩ : syracuseStep 2146935 = 3220403) B3220403
theorem B2717221 : Blo 2145435 2717221 := bbase (se 4 (by rfl) ⟨254739, by rfl⟩ : syracuseStep 2717221 = 509479) (by norm_num)
theorem B3622961 : Blo 2145435 3622961 := bstep (se 2 (by rfl) ⟨1358610, by rfl⟩ : syracuseStep 3622961 = 2717221) B2717221
theorem B2415307 : Blo 2145435 2415307 := bstep (se 1 (by rfl) ⟨1811480, by rfl⟩ : syracuseStep 2415307 = 3622961) B3622961
theorem B3220409 : Blo 2145435 3220409 := bstep (se 2 (by rfl) ⟨1207653, by rfl⟩ : syracuseStep 3220409 = 2415307) B2415307
theorem B2146939 : Blo 2145435 2146939 := bstep (se 1 (by rfl) ⟨1610204, by rfl⟩ : syracuseStep 2146939 = 3220409) B3220409
theorem B3140861 : Blo 2145435 3140861 := bbase (se 3 (by rfl) ⟨588911, by rfl⟩ : syracuseStep 3140861 = 1177823) (by norm_num)
theorem B33502517 : Blo 2145435 33502517 := bstep (se 5 (by rfl) ⟨1570430, by rfl⟩ : syracuseStep 33502517 = 3140861) B3140861
theorem B22335011 : Blo 2145435 22335011 := bstep (se 1 (by rfl) ⟨16751258, by rfl⟩ : syracuseStep 22335011 = 33502517) B33502517
theorem B14890007 : Blo 2145435 14890007 := bstep (se 1 (by rfl) ⟨11167505, by rfl⟩ : syracuseStep 14890007 = 22335011) B22335011
theorem B39706685 : Blo 2145435 39706685 := bstep (se 3 (by rfl) ⟨7445003, by rfl⟩ : syracuseStep 39706685 = 14890007) B14890007
theorem B26471123 : Blo 2145435 26471123 := bstep (se 1 (by rfl) ⟨19853342, by rfl⟩ : syracuseStep 26471123 = 39706685) B39706685
theorem B17647415 : Blo 2145435 17647415 := bstep (se 1 (by rfl) ⟨13235561, by rfl⟩ : syracuseStep 17647415 = 26471123) B26471123
theorem B11764943 : Blo 2145435 11764943 := bstep (se 1 (by rfl) ⟨8823707, by rfl⟩ : syracuseStep 11764943 = 17647415) B17647415
theorem B7843295 : Blo 2145435 7843295 := bstep (se 1 (by rfl) ⟨5882471, by rfl⟩ : syracuseStep 7843295 = 11764943) B11764943
theorem B5228863 : Blo 2145435 5228863 := bstep (se 1 (by rfl) ⟨3921647, by rfl⟩ : syracuseStep 5228863 = 7843295) B7843295
theorem B27887269 : Blo 2145435 27887269 := bstep (se 4 (by rfl) ⟨2614431, by rfl⟩ : syracuseStep 27887269 = 5228863) B5228863
theorem B37183025 : Blo 2145435 37183025 := bstep (se 2 (by rfl) ⟨13943634, by rfl⟩ : syracuseStep 37183025 = 27887269) B27887269
theorem B24788683 : Blo 2145435 24788683 := bstep (se 1 (by rfl) ⟨18591512, by rfl⟩ : syracuseStep 24788683 = 37183025) B37183025
theorem B33051577 : Blo 2145435 33051577 := bstep (se 2 (by rfl) ⟨12394341, by rfl⟩ : syracuseStep 33051577 = 24788683) B24788683
theorem B44068769 : Blo 2145435 44068769 := bstep (se 2 (by rfl) ⟨16525788, by rfl⟩ : syracuseStep 44068769 = 33051577) B33051577
theorem B29379179 : Blo 2145435 29379179 := bstep (se 1 (by rfl) ⟨22034384, by rfl⟩ : syracuseStep 29379179 = 44068769) B44068769
theorem B19586119 : Blo 2145435 19586119 := bstep (se 1 (by rfl) ⟨14689589, by rfl⟩ : syracuseStep 19586119 = 29379179) B29379179
theorem B26114825 : Blo 2145435 26114825 := bstep (se 2 (by rfl) ⟨9793059, by rfl⟩ : syracuseStep 26114825 = 19586119) B19586119
theorem B69639533 : Blo 2145435 69639533 := bstep (se 3 (by rfl) ⟨13057412, by rfl⟩ : syracuseStep 69639533 = 26114825) B26114825
theorem B46426355 : Blo 2145435 46426355 := bstep (se 1 (by rfl) ⟨34819766, by rfl⟩ : syracuseStep 46426355 = 69639533) B69639533
theorem B30950903 : Blo 2145435 30950903 := bstep (se 1 (by rfl) ⟨23213177, by rfl⟩ : syracuseStep 30950903 = 46426355) B46426355
theorem B20633935 : Blo 2145435 20633935 := bstep (se 1 (by rfl) ⟨15475451, by rfl⟩ : syracuseStep 20633935 = 30950903) B30950903
theorem B27511913 : Blo 2145435 27511913 := bstep (se 2 (by rfl) ⟨10316967, by rfl⟩ : syracuseStep 27511913 = 20633935) B20633935
theorem B18341275 : Blo 2145435 18341275 := bstep (se 1 (by rfl) ⟨13755956, by rfl⟩ : syracuseStep 18341275 = 27511913) B27511913
theorem B24455033 : Blo 2145435 24455033 := bstep (se 2 (by rfl) ⟨9170637, by rfl⟩ : syracuseStep 24455033 = 18341275) B18341275
theorem B16303355 : Blo 2145435 16303355 := bstep (se 1 (by rfl) ⟨12227516, by rfl⟩ : syracuseStep 16303355 = 24455033) B24455033
theorem B10868903 : Blo 2145435 10868903 := bstep (se 1 (by rfl) ⟨8151677, by rfl⟩ : syracuseStep 10868903 = 16303355) B16303355
theorem B7245935 : Blo 2145435 7245935 := bstep (se 1 (by rfl) ⟨5434451, by rfl⟩ : syracuseStep 7245935 = 10868903) B10868903
theorem B4830623 : Blo 2145435 4830623 := bstep (se 1 (by rfl) ⟨3622967, by rfl⟩ : syracuseStep 4830623 = 7245935) B7245935
theorem B3220415 : Blo 2145435 3220415 := bstep (se 1 (by rfl) ⟨2415311, by rfl⟩ : syracuseStep 3220415 = 4830623) B4830623
theorem B2146943 : Blo 2145435 2146943 := bstep (se 1 (by rfl) ⟨1610207, by rfl⟩ : syracuseStep 2146943 = 3220415) B3220415
theorem B3220421 : Blo 2145435 3220421 := bbase (se 4 (by rfl) ⟨301914, by rfl⟩ : syracuseStep 3220421 = 603829) (by norm_num)
theorem B2146947 : Blo 2145435 2146947 := bstep (se 1 (by rfl) ⟨1610210, by rfl⟩ : syracuseStep 2146947 = 3220421) B3220421
theorem B3622981 : Blo 2145435 3622981 := bbase (se 4 (by rfl) ⟨339654, by rfl⟩ : syracuseStep 3622981 = 679309) (by norm_num)
theorem B4830641 : Blo 2145435 4830641 := bstep (se 2 (by rfl) ⟨1811490, by rfl⟩ : syracuseStep 4830641 = 3622981) B3622981
theorem B3220427 : Blo 2145435 3220427 := bstep (se 1 (by rfl) ⟨2415320, by rfl⟩ : syracuseStep 3220427 = 4830641) B4830641
theorem B2146951 : Blo 2145435 2146951 := bstep (se 1 (by rfl) ⟨1610213, by rfl⟩ : syracuseStep 2146951 = 3220427) B3220427
theorem B2415325 : Blo 2145435 2415325 := bbase (se 3 (by rfl) ⟨452873, by rfl⟩ : syracuseStep 2415325 = 905747) (by norm_num)
theorem B3220433 : Blo 2145435 3220433 := bstep (se 2 (by rfl) ⟨1207662, by rfl⟩ : syracuseStep 3220433 = 2415325) B2415325
theorem B2146955 : Blo 2145435 2146955 := bstep (se 1 (by rfl) ⟨1610216, by rfl⟩ : syracuseStep 2146955 = 3220433) B3220433
theorem B7245989 : Blo 2145435 7245989 := bbase (se 4 (by rfl) ⟨679311, by rfl⟩ : syracuseStep 7245989 = 1358623) (by norm_num)
theorem B4830659 : Blo 2145435 4830659 := bstep (se 1 (by rfl) ⟨3622994, by rfl⟩ : syracuseStep 4830659 = 7245989) B7245989
theorem B3220439 : Blo 2145435 3220439 := bstep (se 1 (by rfl) ⟨2415329, by rfl⟩ : syracuseStep 3220439 = 4830659) B4830659
theorem B2146959 : Blo 2145435 2146959 := bstep (se 1 (by rfl) ⟨1610219, by rfl⟩ : syracuseStep 2146959 = 3220439) B3220439
theorem B3220445 : Blo 2145435 3220445 := bbase (se 3 (by rfl) ⟨603833, by rfl⟩ : syracuseStep 3220445 = 1207667) (by norm_num)
theorem B2146963 : Blo 2145435 2146963 := bstep (se 1 (by rfl) ⟨1610222, by rfl⟩ : syracuseStep 2146963 = 3220445) B3220445
theorem B4830677 : Blo 2145435 4830677 := bbase (se 7 (by rfl) ⟨56609, by rfl⟩ : syracuseStep 4830677 = 113219) (by norm_num)
theorem B3220451 : Blo 2145435 3220451 := bstep (se 1 (by rfl) ⟨2415338, by rfl⟩ : syracuseStep 3220451 = 4830677) B4830677
theorem B2146967 : Blo 2145435 2146967 := bstep (se 1 (by rfl) ⟨1610225, by rfl⟩ : syracuseStep 2146967 = 3220451) B3220451
theorem B3921701 : Blo 2145435 3921701 := bbase (se 4 (by rfl) ⟨367659, by rfl⟩ : syracuseStep 3921701 = 735319) (by norm_num)
theorem B10457869 : Blo 2145435 10457869 := bstep (se 3 (by rfl) ⟨1960850, by rfl⟩ : syracuseStep 10457869 = 3921701) B3921701
theorem B13943825 : Blo 2145435 13943825 := bstep (se 2 (by rfl) ⟨5228934, by rfl⟩ : syracuseStep 13943825 = 10457869) B10457869
theorem B9295883 : Blo 2145435 9295883 := bstep (se 1 (by rfl) ⟨6971912, by rfl⟩ : syracuseStep 9295883 = 13943825) B13943825
theorem B6197255 : Blo 2145435 6197255 := bstep (se 1 (by rfl) ⟨4647941, by rfl⟩ : syracuseStep 6197255 = 9295883) B9295883
theorem B4131503 : Blo 2145435 4131503 := bstep (se 1 (by rfl) ⟨3098627, by rfl⟩ : syracuseStep 4131503 = 6197255) B6197255
theorem B2754335 : Blo 2145435 2754335 := bstep (se 1 (by rfl) ⟨2065751, by rfl⟩ : syracuseStep 2754335 = 4131503) B4131503
theorem B7344893 : Blo 2145435 7344893 := bstep (se 3 (by rfl) ⟨1377167, by rfl⟩ : syracuseStep 7344893 = 2754335) B2754335
theorem B4896595 : Blo 2145435 4896595 := bstep (se 1 (by rfl) ⟨3672446, by rfl⟩ : syracuseStep 4896595 = 7344893) B7344893
theorem B26115173 : Blo 2145435 26115173 := bstep (se 4 (by rfl) ⟨2448297, by rfl⟩ : syracuseStep 26115173 = 4896595) B4896595
theorem B17410115 : Blo 2145435 17410115 := bstep (se 1 (by rfl) ⟨13057586, by rfl⟩ : syracuseStep 17410115 = 26115173) B26115173
theorem B11606743 : Blo 2145435 11606743 := bstep (se 1 (by rfl) ⟨8705057, by rfl⟩ : syracuseStep 11606743 = 17410115) B17410115
theorem B15475657 : Blo 2145435 15475657 := bstep (se 2 (by rfl) ⟨5803371, by rfl⟩ : syracuseStep 15475657 = 11606743) B11606743
theorem B20634209 : Blo 2145435 20634209 := bstep (se 2 (by rfl) ⟨7737828, by rfl⟩ : syracuseStep 20634209 = 15475657) B15475657
theorem B13756139 : Blo 2145435 13756139 := bstep (se 1 (by rfl) ⟨10317104, by rfl⟩ : syracuseStep 13756139 = 20634209) B20634209
theorem B9170759 : Blo 2145435 9170759 := bstep (se 1 (by rfl) ⟨6878069, by rfl⟩ : syracuseStep 9170759 = 13756139) B13756139
theorem B6113839 : Blo 2145435 6113839 := bstep (se 1 (by rfl) ⟨4585379, by rfl⟩ : syracuseStep 6113839 = 9170759) B9170759
theorem B8151785 : Blo 2145435 8151785 := bstep (se 2 (by rfl) ⟨3056919, by rfl⟩ : syracuseStep 8151785 = 6113839) B6113839
theorem B5434523 : Blo 2145435 5434523 := bstep (se 1 (by rfl) ⟨4075892, by rfl⟩ : syracuseStep 5434523 = 8151785) B8151785
theorem B3623015 : Blo 2145435 3623015 := bstep (se 1 (by rfl) ⟨2717261, by rfl⟩ : syracuseStep 3623015 = 5434523) B5434523
theorem B2415343 : Blo 2145435 2415343 := bstep (se 1 (by rfl) ⟨1811507, by rfl⟩ : syracuseStep 2415343 = 3623015) B3623015
theorem B3220457 : Blo 2145435 3220457 := bstep (se 2 (by rfl) ⟨1207671, by rfl⟩ : syracuseStep 3220457 = 2415343) B2415343
theorem B2146971 : Blo 2145435 2146971 := bstep (se 1 (by rfl) ⟨1610228, by rfl⟩ : syracuseStep 2146971 = 3220457) B3220457
theorem B4896605 : Blo 2145435 4896605 := bbase (se 3 (by rfl) ⟨918113, by rfl⟩ : syracuseStep 4896605 = 1836227) (by norm_num)
theorem B3264403 : Blo 2145435 3264403 := bstep (se 1 (by rfl) ⟨2448302, by rfl⟩ : syracuseStep 3264403 = 4896605) B4896605
theorem B4352537 : Blo 2145435 4352537 := bstep (se 2 (by rfl) ⟨1632201, by rfl⟩ : syracuseStep 4352537 = 3264403) B3264403
theorem B2901691 : Blo 2145435 2901691 := bstep (se 1 (by rfl) ⟨2176268, by rfl⟩ : syracuseStep 2901691 = 4352537) B4352537
theorem B3868921 : Blo 2145435 3868921 := bstep (se 2 (by rfl) ⟨1450845, by rfl⟩ : syracuseStep 3868921 = 2901691) B2901691
theorem B5158561 : Blo 2145435 5158561 := bstep (se 2 (by rfl) ⟨1934460, by rfl⟩ : syracuseStep 5158561 = 3868921) B3868921
theorem B6878081 : Blo 2145435 6878081 := bstep (se 2 (by rfl) ⟨2579280, by rfl⟩ : syracuseStep 6878081 = 5158561) B5158561
theorem B18341549 : Blo 2145435 18341549 := bstep (se 3 (by rfl) ⟨3439040, by rfl⟩ : syracuseStep 18341549 = 6878081) B6878081
theorem B12227699 : Blo 2145435 12227699 := bstep (se 1 (by rfl) ⟨9170774, by rfl⟩ : syracuseStep 12227699 = 18341549) B18341549
theorem B8151799 : Blo 2145435 8151799 := bstep (se 1 (by rfl) ⟨6113849, by rfl⟩ : syracuseStep 8151799 = 12227699) B12227699
theorem B10869065 : Blo 2145435 10869065 := bstep (se 2 (by rfl) ⟨4075899, by rfl⟩ : syracuseStep 10869065 = 8151799) B8151799
theorem B7246043 : Blo 2145435 7246043 := bstep (se 1 (by rfl) ⟨5434532, by rfl⟩ : syracuseStep 7246043 = 10869065) B10869065
theorem B4830695 : Blo 2145435 4830695 := bstep (se 1 (by rfl) ⟨3623021, by rfl⟩ : syracuseStep 4830695 = 7246043) B7246043
theorem B3220463 : Blo 2145435 3220463 := bstep (se 1 (by rfl) ⟨2415347, by rfl⟩ : syracuseStep 3220463 = 4830695) B4830695
theorem B2146975 : Blo 2145435 2146975 := bstep (se 1 (by rfl) ⟨1610231, by rfl⟩ : syracuseStep 2146975 = 3220463) B3220463
theorem B3220469 : Blo 2145435 3220469 := bbase (se 5 (by rfl) ⟨150959, by rfl⟩ : syracuseStep 3220469 = 301919) (by norm_num)
theorem B2146979 : Blo 2145435 2146979 := bstep (se 1 (by rfl) ⟨1610234, by rfl⟩ : syracuseStep 2146979 = 3220469) B3220469
theorem B4585405 : Blo 2145435 4585405 := bbase (se 3 (by rfl) ⟨859763, by rfl⟩ : syracuseStep 4585405 = 1719527) (by norm_num)
theorem B6113873 : Blo 2145435 6113873 := bstep (se 2 (by rfl) ⟨2292702, by rfl⟩ : syracuseStep 6113873 = 4585405) B4585405
theorem B4075915 : Blo 2145435 4075915 := bstep (se 1 (by rfl) ⟨3056936, by rfl⟩ : syracuseStep 4075915 = 6113873) B6113873
theorem B5434553 : Blo 2145435 5434553 := bstep (se 2 (by rfl) ⟨2037957, by rfl⟩ : syracuseStep 5434553 = 4075915) B4075915
theorem B3623035 : Blo 2145435 3623035 := bstep (se 1 (by rfl) ⟨2717276, by rfl⟩ : syracuseStep 3623035 = 5434553) B5434553
theorem B4830713 : Blo 2145435 4830713 := bstep (se 2 (by rfl) ⟨1811517, by rfl⟩ : syracuseStep 4830713 = 3623035) B3623035
theorem B3220475 : Blo 2145435 3220475 := bstep (se 1 (by rfl) ⟨2415356, by rfl⟩ : syracuseStep 3220475 = 4830713) B4830713
theorem B2146983 : Blo 2145435 2146983 := bstep (se 1 (by rfl) ⟨1610237, by rfl⟩ : syracuseStep 2146983 = 3220475) B3220475
theorem B2415361 : Blo 2145435 2415361 := bbase (se 2 (by rfl) ⟨905760, by rfl⟩ : syracuseStep 2415361 = 1811521) (by norm_num)
theorem B3220481 : Blo 2145435 3220481 := bstep (se 2 (by rfl) ⟨1207680, by rfl⟩ : syracuseStep 3220481 = 2415361) B2415361
theorem B2146987 : Blo 2145435 2146987 := bstep (se 1 (by rfl) ⟨1610240, by rfl⟩ : syracuseStep 2146987 = 3220481) B3220481
theorem B5434573 : Blo 2145435 5434573 := bbase (se 3 (by rfl) ⟨1018982, by rfl⟩ : syracuseStep 5434573 = 2037965) (by norm_num)
theorem B7246097 : Blo 2145435 7246097 := bstep (se 2 (by rfl) ⟨2717286, by rfl⟩ : syracuseStep 7246097 = 5434573) B5434573
theorem B4830731 : Blo 2145435 4830731 := bstep (se 1 (by rfl) ⟨3623048, by rfl⟩ : syracuseStep 4830731 = 7246097) B7246097
theorem B3220487 : Blo 2145435 3220487 := bstep (se 1 (by rfl) ⟨2415365, by rfl⟩ : syracuseStep 3220487 = 4830731) B4830731
theorem B2146991 : Blo 2145435 2146991 := bstep (se 1 (by rfl) ⟨1610243, by rfl⟩ : syracuseStep 2146991 = 3220487) B3220487
theorem B3220493 : Blo 2145435 3220493 := bbase (se 3 (by rfl) ⟨603842, by rfl⟩ : syracuseStep 3220493 = 1207685) (by norm_num)
theorem B2146995 : Blo 2145435 2146995 := bstep (se 1 (by rfl) ⟨1610246, by rfl⟩ : syracuseStep 2146995 = 3220493) B3220493
theorem B4830749 : Blo 2145435 4830749 := bbase (se 3 (by rfl) ⟨905765, by rfl⟩ : syracuseStep 4830749 = 1811531) (by norm_num)
theorem B3220499 : Blo 2145435 3220499 := bstep (se 1 (by rfl) ⟨2415374, by rfl⟩ : syracuseStep 3220499 = 4830749) B4830749
theorem B2146999 : Blo 2145435 2146999 := bstep (se 1 (by rfl) ⟨1610249, by rfl⟩ : syracuseStep 2146999 = 3220499) B3220499
theorem B3623069 : Blo 2145435 3623069 := bbase (se 3 (by rfl) ⟨679325, by rfl⟩ : syracuseStep 3623069 = 1358651) (by norm_num)
theorem B2415379 : Blo 2145435 2415379 := bstep (se 1 (by rfl) ⟨1811534, by rfl⟩ : syracuseStep 2415379 = 3623069) B3623069
theorem B3220505 : Blo 2145435 3220505 := bstep (se 2 (by rfl) ⟨1207689, by rfl⟩ : syracuseStep 3220505 = 2415379) B2415379
theorem B2147003 : Blo 2145435 2147003 := bstep (se 1 (by rfl) ⟨1610252, by rfl⟩ : syracuseStep 2147003 = 3220505) B3220505
theorem B26115605 : Blo 2145435 26115605 := bbase (se 6 (by rfl) ⟨612084, by rfl⟩ : syracuseStep 26115605 = 1224169) (by norm_num)
theorem B17410403 : Blo 2145435 17410403 := bstep (se 1 (by rfl) ⟨13057802, by rfl⟩ : syracuseStep 17410403 = 26115605) B26115605
theorem B46427741 : Blo 2145435 46427741 := bstep (se 3 (by rfl) ⟨8705201, by rfl⟩ : syracuseStep 46427741 = 17410403) B17410403
theorem B30951827 : Blo 2145435 30951827 := bstep (se 1 (by rfl) ⟨23213870, by rfl⟩ : syracuseStep 30951827 = 46427741) B46427741
theorem B20634551 : Blo 2145435 20634551 := bstep (se 1 (by rfl) ⟨15475913, by rfl⟩ : syracuseStep 20634551 = 30951827) B30951827
theorem B13756367 : Blo 2145435 13756367 := bstep (se 1 (by rfl) ⟨10317275, by rfl⟩ : syracuseStep 13756367 = 20634551) B20634551
theorem B9170911 : Blo 2145435 9170911 := bstep (se 1 (by rfl) ⟨6878183, by rfl⟩ : syracuseStep 9170911 = 13756367) B13756367
theorem B12227881 : Blo 2145435 12227881 := bstep (se 2 (by rfl) ⟨4585455, by rfl⟩ : syracuseStep 12227881 = 9170911) B9170911
theorem B16303841 : Blo 2145435 16303841 := bstep (se 2 (by rfl) ⟨6113940, by rfl⟩ : syracuseStep 16303841 = 12227881) B12227881
theorem B10869227 : Blo 2145435 10869227 := bstep (se 1 (by rfl) ⟨8151920, by rfl⟩ : syracuseStep 10869227 = 16303841) B16303841
theorem B7246151 : Blo 2145435 7246151 := bstep (se 1 (by rfl) ⟨5434613, by rfl⟩ : syracuseStep 7246151 = 10869227) B10869227
theorem B4830767 : Blo 2145435 4830767 := bstep (se 1 (by rfl) ⟨3623075, by rfl⟩ : syracuseStep 4830767 = 7246151) B7246151
theorem B3220511 : Blo 2145435 3220511 := bstep (se 1 (by rfl) ⟨2415383, by rfl⟩ : syracuseStep 3220511 = 4830767) B4830767
theorem B2147007 : Blo 2145435 2147007 := bstep (se 1 (by rfl) ⟨1610255, by rfl⟩ : syracuseStep 2147007 = 3220511) B3220511
theorem B3220517 : Blo 2145435 3220517 := bbase (se 4 (by rfl) ⟨301923, by rfl⟩ : syracuseStep 3220517 = 603847) (by norm_num)
theorem B2147011 : Blo 2145435 2147011 := bstep (se 1 (by rfl) ⟨1610258, by rfl⟩ : syracuseStep 2147011 = 3220517) B3220517
theorem B2717317 : Blo 2145435 2717317 := bbase (se 4 (by rfl) ⟨254748, by rfl⟩ : syracuseStep 2717317 = 509497) (by norm_num)
theorem B3623089 : Blo 2145435 3623089 := bstep (se 2 (by rfl) ⟨1358658, by rfl⟩ : syracuseStep 3623089 = 2717317) B2717317
theorem B4830785 : Blo 2145435 4830785 := bstep (se 2 (by rfl) ⟨1811544, by rfl⟩ : syracuseStep 4830785 = 3623089) B3623089
theorem B3220523 : Blo 2145435 3220523 := bstep (se 1 (by rfl) ⟨2415392, by rfl⟩ : syracuseStep 3220523 = 4830785) B4830785
theorem B2147015 : Blo 2145435 2147015 := bstep (se 1 (by rfl) ⟨1610261, by rfl⟩ : syracuseStep 2147015 = 3220523) B3220523
theorem B2415397 : Blo 2145435 2415397 := bbase (se 4 (by rfl) ⟨226443, by rfl⟩ : syracuseStep 2415397 = 452887) (by norm_num)
theorem B3220529 : Blo 2145435 3220529 := bstep (se 2 (by rfl) ⟨1207698, by rfl⟩ : syracuseStep 3220529 = 2415397) B2415397
theorem B2147019 : Blo 2145435 2147019 := bstep (se 1 (by rfl) ⟨1610264, by rfl⟩ : syracuseStep 2147019 = 3220529) B3220529
theorem B9170981 : Blo 2145435 9170981 := bbase (se 4 (by rfl) ⟨859779, by rfl⟩ : syracuseStep 9170981 = 1719559) (by norm_num)
theorem B6113987 : Blo 2145435 6113987 := bstep (se 1 (by rfl) ⟨4585490, by rfl⟩ : syracuseStep 6113987 = 9170981) B9170981
theorem B4075991 : Blo 2145435 4075991 := bstep (se 1 (by rfl) ⟨3056993, by rfl⟩ : syracuseStep 4075991 = 6113987) B6113987
theorem B2717327 : Blo 2145435 2717327 := bstep (se 1 (by rfl) ⟨2037995, by rfl⟩ : syracuseStep 2717327 = 4075991) B4075991
theorem B7246205 : Blo 2145435 7246205 := bstep (se 3 (by rfl) ⟨1358663, by rfl⟩ : syracuseStep 7246205 = 2717327) B2717327
theorem B4830803 : Blo 2145435 4830803 := bstep (se 1 (by rfl) ⟨3623102, by rfl⟩ : syracuseStep 4830803 = 7246205) B7246205
theorem B3220535 : Blo 2145435 3220535 := bstep (se 1 (by rfl) ⟨2415401, by rfl⟩ : syracuseStep 3220535 = 4830803) B4830803
theorem B2147023 : Blo 2145435 2147023 := bstep (se 1 (by rfl) ⟨1610267, by rfl⟩ : syracuseStep 2147023 = 3220535) B3220535
theorem B3220541 : Blo 2145435 3220541 := bbase (se 3 (by rfl) ⟨603851, by rfl⟩ : syracuseStep 3220541 = 1207703) (by norm_num)
theorem B2147027 : Blo 2145435 2147027 := bstep (se 1 (by rfl) ⟨1610270, by rfl⟩ : syracuseStep 2147027 = 3220541) B3220541
theorem B4830821 : Blo 2145435 4830821 := bbase (se 4 (by rfl) ⟨452889, by rfl⟩ : syracuseStep 4830821 = 905779) (by norm_num)
theorem B3220547 : Blo 2145435 3220547 := bstep (se 1 (by rfl) ⟨2415410, by rfl⟩ : syracuseStep 3220547 = 4830821) B4830821
theorem B2147031 : Blo 2145435 2147031 := bstep (se 1 (by rfl) ⟨1610273, by rfl⟩ : syracuseStep 2147031 = 3220547) B3220547
theorem B5434685 : Blo 2145435 5434685 := bbase (se 3 (by rfl) ⟨1019003, by rfl⟩ : syracuseStep 5434685 = 2038007) (by norm_num)
theorem B3623123 : Blo 2145435 3623123 := bstep (se 1 (by rfl) ⟨2717342, by rfl⟩ : syracuseStep 3623123 = 5434685) B5434685
theorem B2415415 : Blo 2145435 2415415 := bstep (se 1 (by rfl) ⟨1811561, by rfl⟩ : syracuseStep 2415415 = 3623123) B3623123
theorem B3220553 : Blo 2145435 3220553 := bstep (se 2 (by rfl) ⟨1207707, by rfl⟩ : syracuseStep 3220553 = 2415415) B2415415
theorem B2147035 : Blo 2145435 2147035 := bstep (se 1 (by rfl) ⟨1610276, by rfl⟩ : syracuseStep 2147035 = 3220553) B3220553
theorem B4076021 : Blo 2145435 4076021 := bbase (se 5 (by rfl) ⟨191063, by rfl⟩ : syracuseStep 4076021 = 382127) (by norm_num)
theorem B10869389 : Blo 2145435 10869389 := bstep (se 3 (by rfl) ⟨2038010, by rfl⟩ : syracuseStep 10869389 = 4076021) B4076021
theorem B7246259 : Blo 2145435 7246259 := bstep (se 1 (by rfl) ⟨5434694, by rfl⟩ : syracuseStep 7246259 = 10869389) B10869389
theorem B4830839 : Blo 2145435 4830839 := bstep (se 1 (by rfl) ⟨3623129, by rfl⟩ : syracuseStep 4830839 = 7246259) B7246259
theorem B3220559 : Blo 2145435 3220559 := bstep (se 1 (by rfl) ⟨2415419, by rfl⟩ : syracuseStep 3220559 = 4830839) B4830839
theorem B2147039 : Blo 2145435 2147039 := bstep (se 1 (by rfl) ⟨1610279, by rfl⟩ : syracuseStep 2147039 = 3220559) B3220559
theorem B3220565 : Blo 2145435 3220565 := bbase (se 8 (by rfl) ⟨18870, by rfl⟩ : syracuseStep 3220565 = 37741) (by norm_num)
theorem B2147043 : Blo 2145435 2147043 := bstep (se 1 (by rfl) ⟨1610282, by rfl⟩ : syracuseStep 2147043 = 3220565) B3220565
theorem B2754433 : Blo 2145435 2754433 := bbase (se 2 (by rfl) ⟨1032912, by rfl⟩ : syracuseStep 2754433 = 2065825) (by norm_num)
theorem B3672577 : Blo 2145435 3672577 := bstep (se 2 (by rfl) ⟨1377216, by rfl⟩ : syracuseStep 3672577 = 2754433) B2754433
theorem B4896769 : Blo 2145435 4896769 := bstep (se 2 (by rfl) ⟨1836288, by rfl⟩ : syracuseStep 4896769 = 3672577) B3672577
theorem B6529025 : Blo 2145435 6529025 := bstep (se 2 (by rfl) ⟨2448384, by rfl⟩ : syracuseStep 6529025 = 4896769) B4896769
theorem B4352683 : Blo 2145435 4352683 := bstep (se 1 (by rfl) ⟨3264512, by rfl⟩ : syracuseStep 4352683 = 6529025) B6529025
theorem B5803577 : Blo 2145435 5803577 := bstep (se 2 (by rfl) ⟨2176341, by rfl⟩ : syracuseStep 5803577 = 4352683) B4352683
theorem B3869051 : Blo 2145435 3869051 := bstep (se 1 (by rfl) ⟨2901788, by rfl⟩ : syracuseStep 3869051 = 5803577) B5803577
theorem B10317469 : Blo 2145435 10317469 := bstep (se 3 (by rfl) ⟨1934525, by rfl⟩ : syracuseStep 10317469 = 3869051) B3869051
theorem B13756625 : Blo 2145435 13756625 := bstep (se 2 (by rfl) ⟨5158734, by rfl⟩ : syracuseStep 13756625 = 10317469) B10317469
theorem B9171083 : Blo 2145435 9171083 := bstep (se 1 (by rfl) ⟨6878312, by rfl⟩ : syracuseStep 9171083 = 13756625) B13756625
theorem B6114055 : Blo 2145435 6114055 := bstep (se 1 (by rfl) ⟨4585541, by rfl⟩ : syracuseStep 6114055 = 9171083) B9171083
theorem B8152073 : Blo 2145435 8152073 := bstep (se 2 (by rfl) ⟨3057027, by rfl⟩ : syracuseStep 8152073 = 6114055) B6114055
theorem B5434715 : Blo 2145435 5434715 := bstep (se 1 (by rfl) ⟨4076036, by rfl⟩ : syracuseStep 5434715 = 8152073) B8152073
theorem B3623143 : Blo 2145435 3623143 := bstep (se 1 (by rfl) ⟨2717357, by rfl⟩ : syracuseStep 3623143 = 5434715) B5434715
theorem B4830857 : Blo 2145435 4830857 := bstep (se 2 (by rfl) ⟨1811571, by rfl⟩ : syracuseStep 4830857 = 3623143) B3623143
theorem B3220571 : Blo 2145435 3220571 := bstep (se 1 (by rfl) ⟨2415428, by rfl⟩ : syracuseStep 3220571 = 4830857) B4830857
theorem B2147047 : Blo 2145435 2147047 := bstep (se 1 (by rfl) ⟨1610285, by rfl⟩ : syracuseStep 2147047 = 3220571) B3220571
theorem B2415433 : Blo 2145435 2415433 := bbase (se 2 (by rfl) ⟨905787, by rfl⟩ : syracuseStep 2415433 = 1811575) (by norm_num)
theorem B3220577 : Blo 2145435 3220577 := bstep (se 2 (by rfl) ⟨1207716, by rfl⟩ : syracuseStep 3220577 = 2415433) B2415433
theorem B2147051 : Blo 2145435 2147051 := bstep (se 1 (by rfl) ⟨1610288, by rfl⟩ : syracuseStep 2147051 = 3220577) B3220577
theorem B3098749 : Blo 2145435 3098749 := bbase (se 3 (by rfl) ⟨581015, by rfl⟩ : syracuseStep 3098749 = 1162031) (by norm_num)
theorem B4131665 : Blo 2145435 4131665 := bstep (se 2 (by rfl) ⟨1549374, by rfl⟩ : syracuseStep 4131665 = 3098749) B3098749
theorem B2754443 : Blo 2145435 2754443 := bstep (se 1 (by rfl) ⟨2065832, by rfl⟩ : syracuseStep 2754443 = 4131665) B4131665
theorem B7345181 : Blo 2145435 7345181 := bstep (se 3 (by rfl) ⟨1377221, by rfl⟩ : syracuseStep 7345181 = 2754443) B2754443
theorem B4896787 : Blo 2145435 4896787 := bstep (se 1 (by rfl) ⟨3672590, by rfl⟩ : syracuseStep 4896787 = 7345181) B7345181
theorem B6529049 : Blo 2145435 6529049 := bstep (se 2 (by rfl) ⟨2448393, by rfl⟩ : syracuseStep 6529049 = 4896787) B4896787
theorem B4352699 : Blo 2145435 4352699 := bstep (se 1 (by rfl) ⟨3264524, by rfl⟩ : syracuseStep 4352699 = 6529049) B6529049
theorem B2901799 : Blo 2145435 2901799 := bstep (se 1 (by rfl) ⟨2176349, by rfl⟩ : syracuseStep 2901799 = 4352699) B4352699
theorem B3869065 : Blo 2145435 3869065 := bstep (se 2 (by rfl) ⟨1450899, by rfl⟩ : syracuseStep 3869065 = 2901799) B2901799
theorem B20635013 : Blo 2145435 20635013 := bstep (se 4 (by rfl) ⟨1934532, by rfl⟩ : syracuseStep 20635013 = 3869065) B3869065
theorem B13756675 : Blo 2145435 13756675 := bstep (se 1 (by rfl) ⟨10317506, by rfl⟩ : syracuseStep 13756675 = 20635013) B20635013
theorem B18342233 : Blo 2145435 18342233 := bstep (se 2 (by rfl) ⟨6878337, by rfl⟩ : syracuseStep 18342233 = 13756675) B13756675
theorem B12228155 : Blo 2145435 12228155 := bstep (se 1 (by rfl) ⟨9171116, by rfl⟩ : syracuseStep 12228155 = 18342233) B18342233
theorem B8152103 : Blo 2145435 8152103 := bstep (se 1 (by rfl) ⟨6114077, by rfl⟩ : syracuseStep 8152103 = 12228155) B12228155
theorem B5434735 : Blo 2145435 5434735 := bstep (se 1 (by rfl) ⟨4076051, by rfl⟩ : syracuseStep 5434735 = 8152103) B8152103
theorem B7246313 : Blo 2145435 7246313 := bstep (se 2 (by rfl) ⟨2717367, by rfl⟩ : syracuseStep 7246313 = 5434735) B5434735
theorem B4830875 : Blo 2145435 4830875 := bstep (se 1 (by rfl) ⟨3623156, by rfl⟩ : syracuseStep 4830875 = 7246313) B7246313
theorem B3220583 : Blo 2145435 3220583 := bstep (se 1 (by rfl) ⟨2415437, by rfl⟩ : syracuseStep 3220583 = 4830875) B4830875
theorem B2147055 : Blo 2145435 2147055 := bstep (se 1 (by rfl) ⟨1610291, by rfl⟩ : syracuseStep 2147055 = 3220583) B3220583
theorem B3220589 : Blo 2145435 3220589 := bbase (se 3 (by rfl) ⟨603860, by rfl⟩ : syracuseStep 3220589 = 1207721) (by norm_num)
theorem B2147059 : Blo 2145435 2147059 := bstep (se 1 (by rfl) ⟨1610294, by rfl⟩ : syracuseStep 2147059 = 3220589) B3220589
theorem B4830893 : Blo 2145435 4830893 := bbase (se 3 (by rfl) ⟨905792, by rfl⟩ : syracuseStep 4830893 = 1811585) (by norm_num)
theorem B3220595 : Blo 2145435 3220595 := bstep (se 1 (by rfl) ⟨2415446, by rfl⟩ : syracuseStep 3220595 = 4830893) B4830893
theorem B2147063 : Blo 2145435 2147063 := bstep (se 1 (by rfl) ⟨1610297, by rfl⟩ : syracuseStep 2147063 = 3220595) B3220595
theorem B3439189 : Blo 2145435 3439189 := bbase (se 8 (by rfl) ⟨20151, by rfl⟩ : syracuseStep 3439189 = 40303) (by norm_num)
theorem B4585585 : Blo 2145435 4585585 := bstep (se 2 (by rfl) ⟨1719594, by rfl⟩ : syracuseStep 4585585 = 3439189) B3439189
theorem B6114113 : Blo 2145435 6114113 := bstep (se 2 (by rfl) ⟨2292792, by rfl⟩ : syracuseStep 6114113 = 4585585) B4585585
theorem B4076075 : Blo 2145435 4076075 := bstep (se 1 (by rfl) ⟨3057056, by rfl⟩ : syracuseStep 4076075 = 6114113) B6114113
theorem B2717383 : Blo 2145435 2717383 := bstep (se 1 (by rfl) ⟨2038037, by rfl⟩ : syracuseStep 2717383 = 4076075) B4076075
theorem B3623177 : Blo 2145435 3623177 := bstep (se 2 (by rfl) ⟨1358691, by rfl⟩ : syracuseStep 3623177 = 2717383) B2717383
theorem B2415451 : Blo 2145435 2415451 := bstep (se 1 (by rfl) ⟨1811588, by rfl⟩ : syracuseStep 2415451 = 3623177) B3623177
theorem B3220601 : Blo 2145435 3220601 := bstep (se 2 (by rfl) ⟨1207725, by rfl⟩ : syracuseStep 3220601 = 2415451) B2415451
theorem B2147067 : Blo 2145435 2147067 := bstep (se 1 (by rfl) ⟨1610300, by rfl⟩ : syracuseStep 2147067 = 3220601) B3220601
theorem B8705461 : Blo 2145435 8705461 := bbase (se 5 (by rfl) ⟨408068, by rfl⟩ : syracuseStep 8705461 = 816137) (by norm_num)
theorem B11607281 : Blo 2145435 11607281 := bstep (se 2 (by rfl) ⟨4352730, by rfl⟩ : syracuseStep 11607281 = 8705461) B8705461
theorem B7738187 : Blo 2145435 7738187 := bstep (se 1 (by rfl) ⟨5803640, by rfl⟩ : syracuseStep 7738187 = 11607281) B11607281
theorem B20635165 : Blo 2145435 20635165 := bstep (se 3 (by rfl) ⟨3869093, by rfl⟩ : syracuseStep 20635165 = 7738187) B7738187
theorem B27513553 : Blo 2145435 27513553 := bstep (se 2 (by rfl) ⟨10317582, by rfl⟩ : syracuseStep 27513553 = 20635165) B20635165
theorem B36684737 : Blo 2145435 36684737 := bstep (se 2 (by rfl) ⟨13756776, by rfl⟩ : syracuseStep 36684737 = 27513553) B27513553
theorem B24456491 : Blo 2145435 24456491 := bstep (se 1 (by rfl) ⟨18342368, by rfl⟩ : syracuseStep 24456491 = 36684737) B36684737
theorem B16304327 : Blo 2145435 16304327 := bstep (se 1 (by rfl) ⟨12228245, by rfl⟩ : syracuseStep 16304327 = 24456491) B24456491
theorem B10869551 : Blo 2145435 10869551 := bstep (se 1 (by rfl) ⟨8152163, by rfl⟩ : syracuseStep 10869551 = 16304327) B16304327
theorem B7246367 : Blo 2145435 7246367 := bstep (se 1 (by rfl) ⟨5434775, by rfl⟩ : syracuseStep 7246367 = 10869551) B10869551
theorem B4830911 : Blo 2145435 4830911 := bstep (se 1 (by rfl) ⟨3623183, by rfl⟩ : syracuseStep 4830911 = 7246367) B7246367
theorem B3220607 : Blo 2145435 3220607 := bstep (se 1 (by rfl) ⟨2415455, by rfl⟩ : syracuseStep 3220607 = 4830911) B4830911
theorem B2147071 : Blo 2145435 2147071 := bstep (se 1 (by rfl) ⟨1610303, by rfl⟩ : syracuseStep 2147071 = 3220607) B3220607
theorem B3220613 : Blo 2145435 3220613 := bbase (se 4 (by rfl) ⟨301932, by rfl⟩ : syracuseStep 3220613 = 603865) (by norm_num)
theorem B2147075 : Blo 2145435 2147075 := bstep (se 1 (by rfl) ⟨1610306, by rfl⟩ : syracuseStep 2147075 = 3220613) B3220613
theorem B3623197 : Blo 2145435 3623197 := bbase (se 3 (by rfl) ⟨679349, by rfl⟩ : syracuseStep 3623197 = 1358699) (by norm_num)
theorem B4830929 : Blo 2145435 4830929 := bstep (se 2 (by rfl) ⟨1811598, by rfl⟩ : syracuseStep 4830929 = 3623197) B3623197
theorem B3220619 : Blo 2145435 3220619 := bstep (se 1 (by rfl) ⟨2415464, by rfl⟩ : syracuseStep 3220619 = 4830929) B4830929
theorem B2147079 : Blo 2145435 2147079 := bstep (se 1 (by rfl) ⟨1610309, by rfl⟩ : syracuseStep 2147079 = 3220619) B3220619
theorem B2415469 : Blo 2145435 2415469 := bbase (se 3 (by rfl) ⟨452900, by rfl⟩ : syracuseStep 2415469 = 905801) (by norm_num)
theorem B3220625 : Blo 2145435 3220625 := bstep (se 2 (by rfl) ⟨1207734, by rfl⟩ : syracuseStep 3220625 = 2415469) B2415469
theorem B2147083 : Blo 2145435 2147083 := bstep (se 1 (by rfl) ⟨1610312, by rfl⟩ : syracuseStep 2147083 = 3220625) B3220625
theorem B7246421 : Blo 2145435 7246421 := bbase (se 8 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 7246421 = 84919) (by norm_num)
theorem B4830947 : Blo 2145435 4830947 := bstep (se 1 (by rfl) ⟨3623210, by rfl⟩ : syracuseStep 4830947 = 7246421) B7246421
theorem B3220631 : Blo 2145435 3220631 := bstep (se 1 (by rfl) ⟨2415473, by rfl⟩ : syracuseStep 3220631 = 4830947) B4830947
theorem B2147087 : Blo 2145435 2147087 := bstep (se 1 (by rfl) ⟨1610315, by rfl⟩ : syracuseStep 2147087 = 3220631) B3220631
theorem B3220637 : Blo 2145435 3220637 := bbase (se 3 (by rfl) ⟨603869, by rfl⟩ : syracuseStep 3220637 = 1207739) (by norm_num)
theorem B2147091 : Blo 2145435 2147091 := bstep (se 1 (by rfl) ⟨1610318, by rfl⟩ : syracuseStep 2147091 = 3220637) B3220637
theorem B4830965 : Blo 2145435 4830965 := bbase (se 5 (by rfl) ⟨226451, by rfl⟩ : syracuseStep 4830965 = 452903) (by norm_num)
theorem B3220643 : Blo 2145435 3220643 := bstep (se 1 (by rfl) ⟨2415482, by rfl⟩ : syracuseStep 3220643 = 4830965) B4830965
theorem B2147095 : Blo 2145435 2147095 := bstep (se 1 (by rfl) ⟨1610321, by rfl⟩ : syracuseStep 2147095 = 3220643) B3220643
theorem B23214869 : Blo 2145435 23214869 := bbase (se 6 (by rfl) ⟨544098, by rfl⟩ : syracuseStep 23214869 = 1088197) (by norm_num)
theorem B15476579 : Blo 2145435 15476579 := bstep (se 1 (by rfl) ⟨11607434, by rfl⟩ : syracuseStep 15476579 = 23214869) B23214869
theorem B10317719 : Blo 2145435 10317719 := bstep (se 1 (by rfl) ⟨7738289, by rfl⟩ : syracuseStep 10317719 = 15476579) B15476579
theorem B27513917 : Blo 2145435 27513917 := bstep (se 3 (by rfl) ⟨5158859, by rfl⟩ : syracuseStep 27513917 = 10317719) B10317719
theorem B18342611 : Blo 2145435 18342611 := bstep (se 1 (by rfl) ⟨13756958, by rfl⟩ : syracuseStep 18342611 = 27513917) B27513917
theorem B12228407 : Blo 2145435 12228407 := bstep (se 1 (by rfl) ⟨9171305, by rfl⟩ : syracuseStep 12228407 = 18342611) B18342611
theorem B8152271 : Blo 2145435 8152271 := bstep (se 1 (by rfl) ⟨6114203, by rfl⟩ : syracuseStep 8152271 = 12228407) B12228407
theorem B5434847 : Blo 2145435 5434847 := bstep (se 1 (by rfl) ⟨4076135, by rfl⟩ : syracuseStep 5434847 = 8152271) B8152271
theorem B3623231 : Blo 2145435 3623231 := bstep (se 1 (by rfl) ⟨2717423, by rfl⟩ : syracuseStep 3623231 = 5434847) B5434847
theorem B2415487 : Blo 2145435 2415487 := bstep (se 1 (by rfl) ⟨1811615, by rfl⟩ : syracuseStep 2415487 = 3623231) B3623231
theorem B3220649 : Blo 2145435 3220649 := bstep (se 2 (by rfl) ⟨1207743, by rfl⟩ : syracuseStep 3220649 = 2415487) B2415487
theorem B2147099 : Blo 2145435 2147099 := bstep (se 1 (by rfl) ⟨1610324, by rfl⟩ : syracuseStep 2147099 = 3220649) B3220649
theorem B4585661 : Blo 2145435 4585661 := bbase (se 3 (by rfl) ⟨859811, by rfl⟩ : syracuseStep 4585661 = 1719623) (by norm_num)
theorem B3057107 : Blo 2145435 3057107 := bstep (se 1 (by rfl) ⟨2292830, by rfl⟩ : syracuseStep 3057107 = 4585661) B4585661
theorem B8152285 : Blo 2145435 8152285 := bstep (se 3 (by rfl) ⟨1528553, by rfl⟩ : syracuseStep 8152285 = 3057107) B3057107
theorem B10869713 : Blo 2145435 10869713 := bstep (se 2 (by rfl) ⟨4076142, by rfl⟩ : syracuseStep 10869713 = 8152285) B8152285
theorem B7246475 : Blo 2145435 7246475 := bstep (se 1 (by rfl) ⟨5434856, by rfl⟩ : syracuseStep 7246475 = 10869713) B10869713
theorem B4830983 : Blo 2145435 4830983 := bstep (se 1 (by rfl) ⟨3623237, by rfl⟩ : syracuseStep 4830983 = 7246475) B7246475
theorem B3220655 : Blo 2145435 3220655 := bstep (se 1 (by rfl) ⟨2415491, by rfl⟩ : syracuseStep 3220655 = 4830983) B4830983
theorem B2147103 : Blo 2145435 2147103 := bstep (se 1 (by rfl) ⟨1610327, by rfl⟩ : syracuseStep 2147103 = 3220655) B3220655
theorem B3220661 : Blo 2145435 3220661 := bbase (se 5 (by rfl) ⟨150968, by rfl⟩ : syracuseStep 3220661 = 301937) (by norm_num)
theorem B2147107 : Blo 2145435 2147107 := bstep (se 1 (by rfl) ⟨1610330, by rfl⟩ : syracuseStep 2147107 = 3220661) B3220661
theorem B5434877 : Blo 2145435 5434877 := bbase (se 3 (by rfl) ⟨1019039, by rfl⟩ : syracuseStep 5434877 = 2038079) (by norm_num)
theorem B3623251 : Blo 2145435 3623251 := bstep (se 1 (by rfl) ⟨2717438, by rfl⟩ : syracuseStep 3623251 = 5434877) B5434877
theorem B4831001 : Blo 2145435 4831001 := bstep (se 2 (by rfl) ⟨1811625, by rfl⟩ : syracuseStep 4831001 = 3623251) B3623251
theorem B3220667 : Blo 2145435 3220667 := bstep (se 1 (by rfl) ⟨2415500, by rfl⟩ : syracuseStep 3220667 = 4831001) B4831001
theorem B2147111 : Blo 2145435 2147111 := bstep (se 1 (by rfl) ⟨1610333, by rfl⟩ : syracuseStep 2147111 = 3220667) B3220667
theorem B2415505 : Blo 2145435 2415505 := bbase (se 2 (by rfl) ⟨905814, by rfl⟩ : syracuseStep 2415505 = 1811629) (by norm_num)
theorem B3220673 : Blo 2145435 3220673 := bstep (se 2 (by rfl) ⟨1207752, by rfl⟩ : syracuseStep 3220673 = 2415505) B2415505
theorem B2147115 : Blo 2145435 2147115 := bstep (se 1 (by rfl) ⟨1610336, by rfl⟩ : syracuseStep 2147115 = 3220673) B3220673
theorem B4076173 : Blo 2145435 4076173 := bbase (se 3 (by rfl) ⟨764282, by rfl⟩ : syracuseStep 4076173 = 1528565) (by norm_num)
theorem B5434897 : Blo 2145435 5434897 := bstep (se 2 (by rfl) ⟨2038086, by rfl⟩ : syracuseStep 5434897 = 4076173) B4076173
theorem B7246529 : Blo 2145435 7246529 := bstep (se 2 (by rfl) ⟨2717448, by rfl⟩ : syracuseStep 7246529 = 5434897) B5434897
theorem B4831019 : Blo 2145435 4831019 := bstep (se 1 (by rfl) ⟨3623264, by rfl⟩ : syracuseStep 4831019 = 7246529) B7246529
theorem B3220679 : Blo 2145435 3220679 := bstep (se 1 (by rfl) ⟨2415509, by rfl⟩ : syracuseStep 3220679 = 4831019) B4831019
theorem B2147119 : Blo 2145435 2147119 := bstep (se 1 (by rfl) ⟨1610339, by rfl⟩ : syracuseStep 2147119 = 3220679) B3220679
theorem B3220685 : Blo 2145435 3220685 := bbase (se 3 (by rfl) ⟨603878, by rfl⟩ : syracuseStep 3220685 = 1207757) (by norm_num)
theorem B2147123 : Blo 2145435 2147123 := bstep (se 1 (by rfl) ⟨1610342, by rfl⟩ : syracuseStep 2147123 = 3220685) B3220685
theorem B4831037 : Blo 2145435 4831037 := bbase (se 3 (by rfl) ⟨905819, by rfl⟩ : syracuseStep 4831037 = 1811639) (by norm_num)
theorem B3220691 : Blo 2145435 3220691 := bstep (se 1 (by rfl) ⟨2415518, by rfl⟩ : syracuseStep 3220691 = 4831037) B4831037
theorem B2147127 : Blo 2145435 2147127 := bstep (se 1 (by rfl) ⟨1610345, by rfl⟩ : syracuseStep 2147127 = 3220691) B3220691
theorem B3623285 : Blo 2145435 3623285 := bbase (se 5 (by rfl) ⟨169841, by rfl⟩ : syracuseStep 3623285 = 339683) (by norm_num)
theorem B2415523 : Blo 2145435 2415523 := bstep (se 1 (by rfl) ⟨1811642, by rfl⟩ : syracuseStep 2415523 = 3623285) B3623285
theorem B3220697 : Blo 2145435 3220697 := bstep (se 2 (by rfl) ⟨1207761, by rfl⟩ : syracuseStep 3220697 = 2415523) B2415523
theorem B2147131 : Blo 2145435 2147131 := bstep (se 1 (by rfl) ⟨1610348, by rfl⟩ : syracuseStep 2147131 = 3220697) B3220697
theorem B2579473 : Blo 2145435 2579473 := bbase (se 2 (by rfl) ⟨967302, by rfl⟩ : syracuseStep 2579473 = 1934605) (by norm_num)
theorem B3439297 : Blo 2145435 3439297 := bstep (se 2 (by rfl) ⟨1289736, by rfl⟩ : syracuseStep 3439297 = 2579473) B2579473
theorem B4585729 : Blo 2145435 4585729 := bstep (se 2 (by rfl) ⟨1719648, by rfl⟩ : syracuseStep 4585729 = 3439297) B3439297
theorem B6114305 : Blo 2145435 6114305 := bstep (se 2 (by rfl) ⟨2292864, by rfl⟩ : syracuseStep 6114305 = 4585729) B4585729
theorem B16304813 : Blo 2145435 16304813 := bstep (se 3 (by rfl) ⟨3057152, by rfl⟩ : syracuseStep 16304813 = 6114305) B6114305
theorem B10869875 : Blo 2145435 10869875 := bstep (se 1 (by rfl) ⟨8152406, by rfl⟩ : syracuseStep 10869875 = 16304813) B16304813
theorem B7246583 : Blo 2145435 7246583 := bstep (se 1 (by rfl) ⟨5434937, by rfl⟩ : syracuseStep 7246583 = 10869875) B10869875
theorem B4831055 : Blo 2145435 4831055 := bstep (se 1 (by rfl) ⟨3623291, by rfl⟩ : syracuseStep 4831055 = 7246583) B7246583
theorem B3220703 : Blo 2145435 3220703 := bstep (se 1 (by rfl) ⟨2415527, by rfl⟩ : syracuseStep 3220703 = 4831055) B4831055
theorem B2147135 : Blo 2145435 2147135 := bstep (se 1 (by rfl) ⟨1610351, by rfl⟩ : syracuseStep 2147135 = 3220703) B3220703
theorem B3220709 : Blo 2145435 3220709 := bbase (se 4 (by rfl) ⟨301941, by rfl⟩ : syracuseStep 3220709 = 603883) (by norm_num)
theorem B2147139 : Blo 2145435 2147139 := bstep (se 1 (by rfl) ⟨1610354, by rfl⟩ : syracuseStep 2147139 = 3220709) B3220709
theorem B4412269 : Blo 2145435 4412269 := bbase (se 3 (by rfl) ⟨827300, by rfl⟩ : syracuseStep 4412269 = 1654601) (by norm_num)
theorem B5883025 : Blo 2145435 5883025 := bstep (se 2 (by rfl) ⟨2206134, by rfl⟩ : syracuseStep 5883025 = 4412269) B4412269
theorem B7844033 : Blo 2145435 7844033 := bstep (se 2 (by rfl) ⟨2941512, by rfl⟩ : syracuseStep 7844033 = 5883025) B5883025
theorem B5229355 : Blo 2145435 5229355 := bstep (se 1 (by rfl) ⟨3922016, by rfl⟩ : syracuseStep 5229355 = 7844033) B7844033
theorem B6972473 : Blo 2145435 6972473 := bstep (se 2 (by rfl) ⟨2614677, by rfl⟩ : syracuseStep 6972473 = 5229355) B5229355
theorem B4648315 : Blo 2145435 4648315 := bstep (se 1 (by rfl) ⟨3486236, by rfl⟩ : syracuseStep 4648315 = 6972473) B6972473
theorem B6197753 : Blo 2145435 6197753 := bstep (se 2 (by rfl) ⟨2324157, by rfl⟩ : syracuseStep 6197753 = 4648315) B4648315
theorem B16527341 : Blo 2145435 16527341 := bstep (se 3 (by rfl) ⟨3098876, by rfl⟩ : syracuseStep 16527341 = 6197753) B6197753
theorem B11018227 : Blo 2145435 11018227 := bstep (se 1 (by rfl) ⟨8263670, by rfl⟩ : syracuseStep 11018227 = 16527341) B16527341
theorem B14690969 : Blo 2145435 14690969 := bstep (se 2 (by rfl) ⟨5509113, by rfl⟩ : syracuseStep 14690969 = 11018227) B11018227
theorem B9793979 : Blo 2145435 9793979 := bstep (se 1 (by rfl) ⟨7345484, by rfl⟩ : syracuseStep 9793979 = 14690969) B14690969
theorem B6529319 : Blo 2145435 6529319 := bstep (se 1 (by rfl) ⟨4896989, by rfl⟩ : syracuseStep 6529319 = 9793979) B9793979
theorem B4352879 : Blo 2145435 4352879 := bstep (se 1 (by rfl) ⟨3264659, by rfl⟩ : syracuseStep 4352879 = 6529319) B6529319
theorem B2901919 : Blo 2145435 2901919 := bstep (se 1 (by rfl) ⟨2176439, by rfl⟩ : syracuseStep 2901919 = 4352879) B4352879
theorem B3869225 : Blo 2145435 3869225 := bstep (se 2 (by rfl) ⟨1450959, by rfl⟩ : syracuseStep 3869225 = 2901919) B2901919
theorem B2579483 : Blo 2145435 2579483 := bstep (se 1 (by rfl) ⟨1934612, by rfl⟩ : syracuseStep 2579483 = 3869225) B3869225
theorem B6878621 : Blo 2145435 6878621 := bstep (se 3 (by rfl) ⟨1289741, by rfl⟩ : syracuseStep 6878621 = 2579483) B2579483
theorem B4585747 : Blo 2145435 4585747 := bstep (se 1 (by rfl) ⟨3439310, by rfl⟩ : syracuseStep 4585747 = 6878621) B6878621
theorem B6114329 : Blo 2145435 6114329 := bstep (se 2 (by rfl) ⟨2292873, by rfl⟩ : syracuseStep 6114329 = 4585747) B4585747
theorem B4076219 : Blo 2145435 4076219 := bstep (se 1 (by rfl) ⟨3057164, by rfl⟩ : syracuseStep 4076219 = 6114329) B6114329
theorem B2717479 : Blo 2145435 2717479 := bstep (se 1 (by rfl) ⟨2038109, by rfl⟩ : syracuseStep 2717479 = 4076219) B4076219
theorem B3623305 : Blo 2145435 3623305 := bstep (se 2 (by rfl) ⟨1358739, by rfl⟩ : syracuseStep 3623305 = 2717479) B2717479
theorem B4831073 : Blo 2145435 4831073 := bstep (se 2 (by rfl) ⟨1811652, by rfl⟩ : syracuseStep 4831073 = 3623305) B3623305
theorem B3220715 : Blo 2145435 3220715 := bstep (se 1 (by rfl) ⟨2415536, by rfl⟩ : syracuseStep 3220715 = 4831073) B4831073
theorem B2147143 : Blo 2145435 2147143 := bstep (se 1 (by rfl) ⟨1610357, by rfl⟩ : syracuseStep 2147143 = 3220715) B3220715
theorem B2415541 : Blo 2145435 2415541 := bbase (se 5 (by rfl) ⟨113228, by rfl⟩ : syracuseStep 2415541 = 226457) (by norm_num)
theorem B3220721 : Blo 2145435 3220721 := bstep (se 2 (by rfl) ⟨1207770, by rfl⟩ : syracuseStep 3220721 = 2415541) B2415541
theorem B2147147 : Blo 2145435 2147147 := bstep (se 1 (by rfl) ⟨1610360, by rfl⟩ : syracuseStep 2147147 = 3220721) B3220721
theorem B2717489 : Blo 2145435 2717489 := bbase (se 2 (by rfl) ⟨1019058, by rfl⟩ : syracuseStep 2717489 = 2038117) (by norm_num)
theorem B7246637 : Blo 2145435 7246637 := bstep (se 3 (by rfl) ⟨1358744, by rfl⟩ : syracuseStep 7246637 = 2717489) B2717489
theorem B4831091 : Blo 2145435 4831091 := bstep (se 1 (by rfl) ⟨3623318, by rfl⟩ : syracuseStep 4831091 = 7246637) B7246637
theorem B3220727 : Blo 2145435 3220727 := bstep (se 1 (by rfl) ⟨2415545, by rfl⟩ : syracuseStep 3220727 = 4831091) B4831091
theorem B2147151 : Blo 2145435 2147151 := bstep (se 1 (by rfl) ⟨1610363, by rfl⟩ : syracuseStep 2147151 = 3220727) B3220727
theorem B3220733 : Blo 2145435 3220733 := bbase (se 3 (by rfl) ⟨603887, by rfl⟩ : syracuseStep 3220733 = 1207775) (by norm_num)
theorem B2147155 : Blo 2145435 2147155 := bstep (se 1 (by rfl) ⟨1610366, by rfl⟩ : syracuseStep 2147155 = 3220733) B3220733
theorem B4831109 : Blo 2145435 4831109 := bbase (se 4 (by rfl) ⟨452916, by rfl⟩ : syracuseStep 4831109 = 905833) (by norm_num)
theorem B3220739 : Blo 2145435 3220739 := bstep (se 1 (by rfl) ⟨2415554, by rfl⟩ : syracuseStep 3220739 = 4831109) B4831109
theorem B2147159 : Blo 2145435 2147159 := bstep (se 1 (by rfl) ⟨1610369, by rfl⟩ : syracuseStep 2147159 = 3220739) B3220739
theorem B3486269 : Blo 2145435 3486269 := bbase (se 3 (by rfl) ⟨653675, by rfl⟩ : syracuseStep 3486269 = 1307351) (by norm_num)
theorem B2324179 : Blo 2145435 2324179 := bstep (se 1 (by rfl) ⟨1743134, by rfl⟩ : syracuseStep 2324179 = 3486269) B3486269
theorem B3098905 : Blo 2145435 3098905 := bstep (se 2 (by rfl) ⟨1162089, by rfl⟩ : syracuseStep 3098905 = 2324179) B2324179
theorem B16527493 : Blo 2145435 16527493 := bstep (se 4 (by rfl) ⟨1549452, by rfl⟩ : syracuseStep 16527493 = 3098905) B3098905
theorem B22036657 : Blo 2145435 22036657 := bstep (se 2 (by rfl) ⟨8263746, by rfl⟩ : syracuseStep 22036657 = 16527493) B16527493
theorem B29382209 : Blo 2145435 29382209 := bstep (se 2 (by rfl) ⟨11018328, by rfl⟩ : syracuseStep 29382209 = 22036657) B22036657
theorem B19588139 : Blo 2145435 19588139 := bstep (se 1 (by rfl) ⟨14691104, by rfl⟩ : syracuseStep 19588139 = 29382209) B29382209
theorem B13058759 : Blo 2145435 13058759 := bstep (se 1 (by rfl) ⟨9794069, by rfl⟩ : syracuseStep 13058759 = 19588139) B19588139
theorem B8705839 : Blo 2145435 8705839 := bstep (se 1 (by rfl) ⟨6529379, by rfl⟩ : syracuseStep 8705839 = 13058759) B13058759
theorem B11607785 : Blo 2145435 11607785 := bstep (se 2 (by rfl) ⟨4352919, by rfl⟩ : syracuseStep 11607785 = 8705839) B8705839
theorem B7738523 : Blo 2145435 7738523 := bstep (se 1 (by rfl) ⟨5803892, by rfl⟩ : syracuseStep 7738523 = 11607785) B11607785
theorem B5159015 : Blo 2145435 5159015 := bstep (se 1 (by rfl) ⟨3869261, by rfl⟩ : syracuseStep 5159015 = 7738523) B7738523
theorem B3439343 : Blo 2145435 3439343 := bstep (se 1 (by rfl) ⟨2579507, by rfl⟩ : syracuseStep 3439343 = 5159015) B5159015
theorem B2292895 : Blo 2145435 2292895 := bstep (se 1 (by rfl) ⟨1719671, by rfl⟩ : syracuseStep 2292895 = 3439343) B3439343
theorem B3057193 : Blo 2145435 3057193 := bstep (se 2 (by rfl) ⟨1146447, by rfl⟩ : syracuseStep 3057193 = 2292895) B2292895
theorem B4076257 : Blo 2145435 4076257 := bstep (se 2 (by rfl) ⟨1528596, by rfl⟩ : syracuseStep 4076257 = 3057193) B3057193
theorem B5435009 : Blo 2145435 5435009 := bstep (se 2 (by rfl) ⟨2038128, by rfl⟩ : syracuseStep 5435009 = 4076257) B4076257
theorem B3623339 : Blo 2145435 3623339 := bstep (se 1 (by rfl) ⟨2717504, by rfl⟩ : syracuseStep 3623339 = 5435009) B5435009
theorem B2415559 : Blo 2145435 2415559 := bstep (se 1 (by rfl) ⟨1811669, by rfl⟩ : syracuseStep 2415559 = 3623339) B3623339
theorem B3220745 : Blo 2145435 3220745 := bstep (se 2 (by rfl) ⟨1207779, by rfl⟩ : syracuseStep 3220745 = 2415559) B2415559
theorem B2147163 : Blo 2145435 2147163 := bstep (se 1 (by rfl) ⟨1610372, by rfl⟩ : syracuseStep 2147163 = 3220745) B3220745
theorem B10870037 : Blo 2145435 10870037 := bbase (se 6 (by rfl) ⟨254766, by rfl⟩ : syracuseStep 10870037 = 509533) (by norm_num)
theorem B7246691 : Blo 2145435 7246691 := bstep (se 1 (by rfl) ⟨5435018, by rfl⟩ : syracuseStep 7246691 = 10870037) B10870037
theorem B4831127 : Blo 2145435 4831127 := bstep (se 1 (by rfl) ⟨3623345, by rfl⟩ : syracuseStep 4831127 = 7246691) B7246691
theorem B3220751 : Blo 2145435 3220751 := bstep (se 1 (by rfl) ⟨2415563, by rfl⟩ : syracuseStep 3220751 = 4831127) B4831127
theorem B2147167 : Blo 2145435 2147167 := bstep (se 1 (by rfl) ⟨1610375, by rfl⟩ : syracuseStep 2147167 = 3220751) B3220751
theorem B3220757 : Blo 2145435 3220757 := bbase (se 6 (by rfl) ⟨75486, by rfl⟩ : syracuseStep 3220757 = 150973) (by norm_num)
theorem B2147171 : Blo 2145435 2147171 := bstep (se 1 (by rfl) ⟨1610378, by rfl⟩ : syracuseStep 2147171 = 3220757) B3220757
theorem B18593525 : Blo 2145435 18593525 := bbase (se 5 (by rfl) ⟨871571, by rfl⟩ : syracuseStep 18593525 = 1743143) (by norm_num)
theorem B12395683 : Blo 2145435 12395683 := bstep (se 1 (by rfl) ⟨9296762, by rfl⟩ : syracuseStep 12395683 = 18593525) B18593525
theorem B16527577 : Blo 2145435 16527577 := bstep (se 2 (by rfl) ⟨6197841, by rfl⟩ : syracuseStep 16527577 = 12395683) B12395683
theorem B22036769 : Blo 2145435 22036769 := bstep (se 2 (by rfl) ⟨8263788, by rfl⟩ : syracuseStep 22036769 = 16527577) B16527577
theorem B14691179 : Blo 2145435 14691179 := bstep (se 1 (by rfl) ⟨11018384, by rfl⟩ : syracuseStep 14691179 = 22036769) B22036769
theorem B9794119 : Blo 2145435 9794119 := bstep (se 1 (by rfl) ⟨7345589, by rfl⟩ : syracuseStep 9794119 = 14691179) B14691179
theorem B13058825 : Blo 2145435 13058825 := bstep (se 2 (by rfl) ⟨4897059, by rfl⟩ : syracuseStep 13058825 = 9794119) B9794119
theorem B34823533 : Blo 2145435 34823533 := bstep (se 3 (by rfl) ⟨6529412, by rfl⟩ : syracuseStep 34823533 = 13058825) B13058825
theorem B46431377 : Blo 2145435 46431377 := bstep (se 2 (by rfl) ⟨17411766, by rfl⟩ : syracuseStep 46431377 = 34823533) B34823533
theorem B30954251 : Blo 2145435 30954251 := bstep (se 1 (by rfl) ⟨23215688, by rfl⟩ : syracuseStep 30954251 = 46431377) B46431377
theorem B20636167 : Blo 2145435 20636167 := bstep (se 1 (by rfl) ⟨15477125, by rfl⟩ : syracuseStep 20636167 = 30954251) B30954251
theorem B27514889 : Blo 2145435 27514889 := bstep (se 2 (by rfl) ⟨10318083, by rfl⟩ : syracuseStep 27514889 = 20636167) B20636167
theorem B18343259 : Blo 2145435 18343259 := bstep (se 1 (by rfl) ⟨13757444, by rfl⟩ : syracuseStep 18343259 = 27514889) B27514889
theorem B12228839 : Blo 2145435 12228839 := bstep (se 1 (by rfl) ⟨9171629, by rfl⟩ : syracuseStep 12228839 = 18343259) B18343259
theorem B8152559 : Blo 2145435 8152559 := bstep (se 1 (by rfl) ⟨6114419, by rfl⟩ : syracuseStep 8152559 = 12228839) B12228839
theorem B5435039 : Blo 2145435 5435039 := bstep (se 1 (by rfl) ⟨4076279, by rfl⟩ : syracuseStep 5435039 = 8152559) B8152559
theorem B3623359 : Blo 2145435 3623359 := bstep (se 1 (by rfl) ⟨2717519, by rfl⟩ : syracuseStep 3623359 = 5435039) B5435039
theorem B4831145 : Blo 2145435 4831145 := bstep (se 2 (by rfl) ⟨1811679, by rfl⟩ : syracuseStep 4831145 = 3623359) B3623359
theorem B3220763 : Blo 2145435 3220763 := bstep (se 1 (by rfl) ⟨2415572, by rfl⟩ : syracuseStep 3220763 = 4831145) B4831145
theorem B2147175 : Blo 2145435 2147175 := bstep (se 1 (by rfl) ⟨1610381, by rfl⟩ : syracuseStep 2147175 = 3220763) B3220763
theorem B2415577 : Blo 2145435 2415577 := bbase (se 2 (by rfl) ⟨905841, by rfl⟩ : syracuseStep 2415577 = 1811683) (by norm_num)
theorem B3220769 : Blo 2145435 3220769 := bstep (se 2 (by rfl) ⟨1207788, by rfl⟩ : syracuseStep 3220769 = 2415577) B2415577
theorem B2147179 : Blo 2145435 2147179 := bstep (se 1 (by rfl) ⟨1610384, by rfl⟩ : syracuseStep 2147179 = 3220769) B3220769
theorem B3057221 : Blo 2145435 3057221 := bbase (se 4 (by rfl) ⟨286614, by rfl⟩ : syracuseStep 3057221 = 573229) (by norm_num)
theorem B8152589 : Blo 2145435 8152589 := bstep (se 3 (by rfl) ⟨1528610, by rfl⟩ : syracuseStep 8152589 = 3057221) B3057221
theorem B5435059 : Blo 2145435 5435059 := bstep (se 1 (by rfl) ⟨4076294, by rfl⟩ : syracuseStep 5435059 = 8152589) B8152589
theorem B7246745 : Blo 2145435 7246745 := bstep (se 2 (by rfl) ⟨2717529, by rfl⟩ : syracuseStep 7246745 = 5435059) B5435059
theorem B4831163 : Blo 2145435 4831163 := bstep (se 1 (by rfl) ⟨3623372, by rfl⟩ : syracuseStep 4831163 = 7246745) B7246745
theorem B3220775 : Blo 2145435 3220775 := bstep (se 1 (by rfl) ⟨2415581, by rfl⟩ : syracuseStep 3220775 = 4831163) B4831163
theorem B2147183 : Blo 2145435 2147183 := bstep (se 1 (by rfl) ⟨1610387, by rfl⟩ : syracuseStep 2147183 = 3220775) B3220775
theorem B3220781 : Blo 2145435 3220781 := bbase (se 3 (by rfl) ⟨603896, by rfl⟩ : syracuseStep 3220781 = 1207793) (by norm_num)
theorem B2147187 : Blo 2145435 2147187 := bstep (se 1 (by rfl) ⟨1610390, by rfl⟩ : syracuseStep 2147187 = 3220781) B3220781
theorem B4831181 : Blo 2145435 4831181 := bbase (se 3 (by rfl) ⟨905846, by rfl⟩ : syracuseStep 4831181 = 1811693) (by norm_num)
theorem B3220787 : Blo 2145435 3220787 := bstep (se 1 (by rfl) ⟨2415590, by rfl⟩ : syracuseStep 3220787 = 4831181) B4831181
theorem B2147191 : Blo 2145435 2147191 := bstep (se 1 (by rfl) ⟨1610393, by rfl⟩ : syracuseStep 2147191 = 3220787) B3220787
theorem B2717545 : Blo 2145435 2717545 := bbase (se 2 (by rfl) ⟨1019079, by rfl⟩ : syracuseStep 2717545 = 2038159) (by norm_num)
theorem B3623393 : Blo 2145435 3623393 := bstep (se 2 (by rfl) ⟨1358772, by rfl⟩ : syracuseStep 3623393 = 2717545) B2717545
theorem B2415595 : Blo 2145435 2415595 := bstep (se 1 (by rfl) ⟨1811696, by rfl⟩ : syracuseStep 2415595 = 3623393) B3623393
theorem B3220793 : Blo 2145435 3220793 := bstep (se 2 (by rfl) ⟨1207797, by rfl⟩ : syracuseStep 3220793 = 2415595) B2415595
theorem B2147195 : Blo 2145435 2147195 := bstep (se 1 (by rfl) ⟨1610396, by rfl⟩ : syracuseStep 2147195 = 3220793) B3220793
theorem B9296869 : Blo 2145435 9296869 := bbase (se 4 (by rfl) ⟨871581, by rfl⟩ : syracuseStep 9296869 = 1743163) (by norm_num)
theorem B12395825 : Blo 2145435 12395825 := bstep (se 2 (by rfl) ⟨4648434, by rfl⟩ : syracuseStep 12395825 = 9296869) B9296869
theorem B8263883 : Blo 2145435 8263883 := bstep (se 1 (by rfl) ⟨6197912, by rfl⟩ : syracuseStep 8263883 = 12395825) B12395825
theorem B5509255 : Blo 2145435 5509255 := bstep (se 1 (by rfl) ⟨4131941, by rfl⟩ : syracuseStep 5509255 = 8263883) B8263883
theorem B7345673 : Blo 2145435 7345673 := bstep (se 2 (by rfl) ⟨2754627, by rfl⟩ : syracuseStep 7345673 = 5509255) B5509255
theorem B4897115 : Blo 2145435 4897115 := bstep (se 1 (by rfl) ⟨3672836, by rfl⟩ : syracuseStep 4897115 = 7345673) B7345673
theorem B3264743 : Blo 2145435 3264743 := bstep (se 1 (by rfl) ⟨2448557, by rfl⟩ : syracuseStep 3264743 = 4897115) B4897115
theorem B8705981 : Blo 2145435 8705981 := bstep (se 3 (by rfl) ⟨1632371, by rfl⟩ : syracuseStep 8705981 = 3264743) B3264743
theorem B5803987 : Blo 2145435 5803987 := bstep (se 1 (by rfl) ⟨4352990, by rfl⟩ : syracuseStep 5803987 = 8705981) B8705981
theorem B7738649 : Blo 2145435 7738649 := bstep (se 2 (by rfl) ⟨2901993, by rfl⟩ : syracuseStep 7738649 = 5803987) B5803987
theorem B5159099 : Blo 2145435 5159099 := bstep (se 1 (by rfl) ⟨3869324, by rfl⟩ : syracuseStep 5159099 = 7738649) B7738649
theorem B13757597 : Blo 2145435 13757597 := bstep (se 3 (by rfl) ⟨2579549, by rfl⟩ : syracuseStep 13757597 = 5159099) B5159099
theorem B9171731 : Blo 2145435 9171731 := bstep (se 1 (by rfl) ⟨6878798, by rfl⟩ : syracuseStep 9171731 = 13757597) B13757597
theorem B24457949 : Blo 2145435 24457949 := bstep (se 3 (by rfl) ⟨4585865, by rfl⟩ : syracuseStep 24457949 = 9171731) B9171731
theorem B16305299 : Blo 2145435 16305299 := bstep (se 1 (by rfl) ⟨12228974, by rfl⟩ : syracuseStep 16305299 = 24457949) B24457949
theorem B10870199 : Blo 2145435 10870199 := bstep (se 1 (by rfl) ⟨8152649, by rfl⟩ : syracuseStep 10870199 = 16305299) B16305299
theorem B7246799 : Blo 2145435 7246799 := bstep (se 1 (by rfl) ⟨5435099, by rfl⟩ : syracuseStep 7246799 = 10870199) B10870199
theorem B4831199 : Blo 2145435 4831199 := bstep (se 1 (by rfl) ⟨3623399, by rfl⟩ : syracuseStep 4831199 = 7246799) B7246799
theorem B3220799 : Blo 2145435 3220799 := bstep (se 1 (by rfl) ⟨2415599, by rfl⟩ : syracuseStep 3220799 = 4831199) B4831199
theorem B2147199 : Blo 2145435 2147199 := bstep (se 1 (by rfl) ⟨1610399, by rfl⟩ : syracuseStep 2147199 = 3220799) B3220799
theorem B3220805 : Blo 2145435 3220805 := bbase (se 4 (by rfl) ⟨301950, by rfl⟩ : syracuseStep 3220805 = 603901) (by norm_num)
theorem B2147203 : Blo 2145435 2147203 := bstep (se 1 (by rfl) ⟨1610402, by rfl⟩ : syracuseStep 2147203 = 3220805) B3220805
theorem B3623413 : Blo 2145435 3623413 := bbase (se 5 (by rfl) ⟨169847, by rfl⟩ : syracuseStep 3623413 = 339695) (by norm_num)
theorem B4831217 : Blo 2145435 4831217 := bstep (se 2 (by rfl) ⟨1811706, by rfl⟩ : syracuseStep 4831217 = 3623413) B3623413
theorem B3220811 : Blo 2145435 3220811 := bstep (se 1 (by rfl) ⟨2415608, by rfl⟩ : syracuseStep 3220811 = 4831217) B4831217
theorem B2147207 : Blo 2145435 2147207 := bstep (se 1 (by rfl) ⟨1610405, by rfl⟩ : syracuseStep 2147207 = 3220811) B3220811
theorem B2415613 : Blo 2145435 2415613 := bbase (se 3 (by rfl) ⟨452927, by rfl⟩ : syracuseStep 2415613 = 905855) (by norm_num)
theorem B3220817 : Blo 2145435 3220817 := bstep (se 2 (by rfl) ⟨1207806, by rfl⟩ : syracuseStep 3220817 = 2415613) B2415613
theorem B2147211 : Blo 2145435 2147211 := bstep (se 1 (by rfl) ⟨1610408, by rfl⟩ : syracuseStep 2147211 = 3220817) B3220817
theorem B7246853 : Blo 2145435 7246853 := bbase (se 4 (by rfl) ⟨679392, by rfl⟩ : syracuseStep 7246853 = 1358785) (by norm_num)
theorem B4831235 : Blo 2145435 4831235 := bstep (se 1 (by rfl) ⟨3623426, by rfl⟩ : syracuseStep 4831235 = 7246853) B7246853
theorem B3220823 : Blo 2145435 3220823 := bstep (se 1 (by rfl) ⟨2415617, by rfl⟩ : syracuseStep 3220823 = 4831235) B4831235
theorem B2147215 : Blo 2145435 2147215 := bstep (se 1 (by rfl) ⟨1610411, by rfl⟩ : syracuseStep 2147215 = 3220823) B3220823
theorem B3220829 : Blo 2145435 3220829 := bbase (se 3 (by rfl) ⟨603905, by rfl⟩ : syracuseStep 3220829 = 1207811) (by norm_num)
theorem B2147219 : Blo 2145435 2147219 := bstep (se 1 (by rfl) ⟨1610414, by rfl⟩ : syracuseStep 2147219 = 3220829) B3220829
theorem B4831253 : Blo 2145435 4831253 := bbase (se 6 (by rfl) ⟨113232, by rfl⟩ : syracuseStep 4831253 = 226465) (by norm_num)
theorem B3220835 : Blo 2145435 3220835 := bstep (se 1 (by rfl) ⟨2415626, by rfl⟩ : syracuseStep 3220835 = 4831253) B4831253
theorem B2147223 : Blo 2145435 2147223 := bstep (se 1 (by rfl) ⟨1610417, by rfl⟩ : syracuseStep 2147223 = 3220835) B3220835
theorem B8152757 : Blo 2145435 8152757 := bbase (se 5 (by rfl) ⟨382160, by rfl⟩ : syracuseStep 8152757 = 764321) (by norm_num)
theorem B5435171 : Blo 2145435 5435171 := bstep (se 1 (by rfl) ⟨4076378, by rfl⟩ : syracuseStep 5435171 = 8152757) B8152757
theorem B3623447 : Blo 2145435 3623447 := bstep (se 1 (by rfl) ⟨2717585, by rfl⟩ : syracuseStep 3623447 = 5435171) B5435171
theorem B2415631 : Blo 2145435 2415631 := bstep (se 1 (by rfl) ⟨1811723, by rfl⟩ : syracuseStep 2415631 = 3623447) B3623447
theorem B3220841 : Blo 2145435 3220841 := bstep (se 2 (by rfl) ⟨1207815, by rfl⟩ : syracuseStep 3220841 = 2415631) B2415631
theorem B2147227 : Blo 2145435 2147227 := bstep (se 1 (by rfl) ⟨1610420, by rfl⟩ : syracuseStep 2147227 = 3220841) B3220841
theorem B4897189 : Blo 2145435 4897189 := bbase (se 4 (by rfl) ⟨459111, by rfl⟩ : syracuseStep 4897189 = 918223) (by norm_num)
theorem B6529585 : Blo 2145435 6529585 := bstep (se 2 (by rfl) ⟨2448594, by rfl⟩ : syracuseStep 6529585 = 4897189) B4897189
theorem B8706113 : Blo 2145435 8706113 := bstep (se 2 (by rfl) ⟨3264792, by rfl⟩ : syracuseStep 8706113 = 6529585) B6529585
theorem B5804075 : Blo 2145435 5804075 := bstep (se 1 (by rfl) ⟨4353056, by rfl⟩ : syracuseStep 5804075 = 8706113) B8706113
theorem B3869383 : Blo 2145435 3869383 := bstep (se 1 (by rfl) ⟨2902037, by rfl⟩ : syracuseStep 3869383 = 5804075) B5804075
theorem B5159177 : Blo 2145435 5159177 := bstep (se 2 (by rfl) ⟨1934691, by rfl⟩ : syracuseStep 5159177 = 3869383) B3869383
theorem B3439451 : Blo 2145435 3439451 := bstep (se 1 (by rfl) ⟨2579588, by rfl⟩ : syracuseStep 3439451 = 5159177) B5159177
theorem B2292967 : Blo 2145435 2292967 := bstep (se 1 (by rfl) ⟨1719725, by rfl⟩ : syracuseStep 2292967 = 3439451) B3439451
theorem B12229157 : Blo 2145435 12229157 := bstep (se 4 (by rfl) ⟨1146483, by rfl⟩ : syracuseStep 12229157 = 2292967) B2292967
theorem B8152771 : Blo 2145435 8152771 := bstep (se 1 (by rfl) ⟨6114578, by rfl⟩ : syracuseStep 8152771 = 12229157) B12229157
theorem B10870361 : Blo 2145435 10870361 := bstep (se 2 (by rfl) ⟨4076385, by rfl⟩ : syracuseStep 10870361 = 8152771) B8152771
theorem B7246907 : Blo 2145435 7246907 := bstep (se 1 (by rfl) ⟨5435180, by rfl⟩ : syracuseStep 7246907 = 10870361) B10870361
theorem B4831271 : Blo 2145435 4831271 := bstep (se 1 (by rfl) ⟨3623453, by rfl⟩ : syracuseStep 4831271 = 7246907) B7246907
theorem B3220847 : Blo 2145435 3220847 := bstep (se 1 (by rfl) ⟨2415635, by rfl⟩ : syracuseStep 3220847 = 4831271) B4831271
theorem B2147231 : Blo 2145435 2147231 := bstep (se 1 (by rfl) ⟨1610423, by rfl⟩ : syracuseStep 2147231 = 3220847) B3220847
theorem B3220853 : Blo 2145435 3220853 := bbase (se 5 (by rfl) ⟨150977, by rfl⟩ : syracuseStep 3220853 = 301955) (by norm_num)
theorem B2147235 : Blo 2145435 2147235 := bstep (se 1 (by rfl) ⟨1610426, by rfl⟩ : syracuseStep 2147235 = 3220853) B3220853
theorem B3057301 : Blo 2145435 3057301 := bbase (se 6 (by rfl) ⟨71655, by rfl⟩ : syracuseStep 3057301 = 143311) (by norm_num)
theorem B4076401 : Blo 2145435 4076401 := bstep (se 2 (by rfl) ⟨1528650, by rfl⟩ : syracuseStep 4076401 = 3057301) B3057301
theorem B5435201 : Blo 2145435 5435201 := bstep (se 2 (by rfl) ⟨2038200, by rfl⟩ : syracuseStep 5435201 = 4076401) B4076401
theorem B3623467 : Blo 2145435 3623467 := bstep (se 1 (by rfl) ⟨2717600, by rfl⟩ : syracuseStep 3623467 = 5435201) B5435201
theorem B4831289 : Blo 2145435 4831289 := bstep (se 2 (by rfl) ⟨1811733, by rfl⟩ : syracuseStep 4831289 = 3623467) B3623467
theorem B3220859 : Blo 2145435 3220859 := bstep (se 1 (by rfl) ⟨2415644, by rfl⟩ : syracuseStep 3220859 = 4831289) B4831289
theorem B2147239 : Blo 2145435 2147239 := bstep (se 1 (by rfl) ⟨1610429, by rfl⟩ : syracuseStep 2147239 = 3220859) B3220859
theorem B2415649 : Blo 2145435 2415649 := bbase (se 2 (by rfl) ⟨905868, by rfl⟩ : syracuseStep 2415649 = 1811737) (by norm_num)
theorem B3220865 : Blo 2145435 3220865 := bstep (se 2 (by rfl) ⟨1207824, by rfl⟩ : syracuseStep 3220865 = 2415649) B2415649
theorem B2147243 : Blo 2145435 2147243 := bstep (se 1 (by rfl) ⟨1610432, by rfl⟩ : syracuseStep 2147243 = 3220865) B3220865
theorem B5435221 : Blo 2145435 5435221 := bbase (se 9 (by rfl) ⟨15923, by rfl⟩ : syracuseStep 5435221 = 31847) (by norm_num)
theorem B7246961 : Blo 2145435 7246961 := bstep (se 2 (by rfl) ⟨2717610, by rfl⟩ : syracuseStep 7246961 = 5435221) B5435221
theorem B4831307 : Blo 2145435 4831307 := bstep (se 1 (by rfl) ⟨3623480, by rfl⟩ : syracuseStep 4831307 = 7246961) B7246961
theorem B3220871 : Blo 2145435 3220871 := bstep (se 1 (by rfl) ⟨2415653, by rfl⟩ : syracuseStep 3220871 = 4831307) B4831307
theorem B2147247 : Blo 2145435 2147247 := bstep (se 1 (by rfl) ⟨1610435, by rfl⟩ : syracuseStep 2147247 = 3220871) B3220871
theorem B3220877 : Blo 2145435 3220877 := bbase (se 3 (by rfl) ⟨603914, by rfl⟩ : syracuseStep 3220877 = 1207829) (by norm_num)
theorem B2147251 : Blo 2145435 2147251 := bstep (se 1 (by rfl) ⟨1610438, by rfl⟩ : syracuseStep 2147251 = 3220877) B3220877
theorem B4831325 : Blo 2145435 4831325 := bbase (se 3 (by rfl) ⟨905873, by rfl⟩ : syracuseStep 4831325 = 1811747) (by norm_num)
theorem B3220883 : Blo 2145435 3220883 := bstep (se 1 (by rfl) ⟨2415662, by rfl⟩ : syracuseStep 3220883 = 4831325) B4831325
theorem B2147255 : Blo 2145435 2147255 := bstep (se 1 (by rfl) ⟨1610441, by rfl⟩ : syracuseStep 2147255 = 3220883) B3220883
theorem B3623501 : Blo 2145435 3623501 := bbase (se 3 (by rfl) ⟨679406, by rfl⟩ : syracuseStep 3623501 = 1358813) (by norm_num)
theorem B2415667 : Blo 2145435 2415667 := bstep (se 1 (by rfl) ⟨1811750, by rfl⟩ : syracuseStep 2415667 = 3623501) B3623501
theorem B3220889 : Blo 2145435 3220889 := bstep (se 2 (by rfl) ⟨1207833, by rfl⟩ : syracuseStep 3220889 = 2415667) B2415667
theorem B2147259 : Blo 2145435 2147259 := bstep (se 1 (by rfl) ⟨1610444, by rfl⟩ : syracuseStep 2147259 = 3220889) B3220889
theorem B5883349 : Blo 2145435 5883349 := bbase (se 7 (by rfl) ⟨68945, by rfl⟩ : syracuseStep 5883349 = 137891) (by norm_num)
theorem B7844465 : Blo 2145435 7844465 := bstep (se 2 (by rfl) ⟨2941674, by rfl⟩ : syracuseStep 7844465 = 5883349) B5883349
theorem B5229643 : Blo 2145435 5229643 := bstep (se 1 (by rfl) ⟨3922232, by rfl⟩ : syracuseStep 5229643 = 7844465) B7844465
theorem B6972857 : Blo 2145435 6972857 := bstep (se 2 (by rfl) ⟨2614821, by rfl⟩ : syracuseStep 6972857 = 5229643) B5229643
theorem B4648571 : Blo 2145435 4648571 := bstep (se 1 (by rfl) ⟨3486428, by rfl⟩ : syracuseStep 4648571 = 6972857) B6972857
theorem B198339029 : Blo 2145435 198339029 := bstep (se 7 (by rfl) ⟨2324285, by rfl⟩ : syracuseStep 198339029 = 4648571) B4648571
theorem B132226019 : Blo 2145435 132226019 := bstep (se 1 (by rfl) ⟨99169514, by rfl⟩ : syracuseStep 132226019 = 198339029) B198339029
theorem B88150679 : Blo 2145435 88150679 := bstep (se 1 (by rfl) ⟨66113009, by rfl⟩ : syracuseStep 88150679 = 132226019) B132226019
theorem B58767119 : Blo 2145435 58767119 := bstep (se 1 (by rfl) ⟨44075339, by rfl⟩ : syracuseStep 58767119 = 88150679) B88150679
theorem B39178079 : Blo 2145435 39178079 := bstep (se 1 (by rfl) ⟨29383559, by rfl⟩ : syracuseStep 39178079 = 58767119) B58767119
theorem B26118719 : Blo 2145435 26118719 := bstep (se 1 (by rfl) ⟨19589039, by rfl⟩ : syracuseStep 26118719 = 39178079) B39178079
theorem B17412479 : Blo 2145435 17412479 := bstep (se 1 (by rfl) ⟨13059359, by rfl⟩ : syracuseStep 17412479 = 26118719) B26118719
theorem B11608319 : Blo 2145435 11608319 := bstep (se 1 (by rfl) ⟨8706239, by rfl⟩ : syracuseStep 11608319 = 17412479) B17412479
theorem B30955517 : Blo 2145435 30955517 := bstep (se 3 (by rfl) ⟨5804159, by rfl⟩ : syracuseStep 30955517 = 11608319) B11608319
theorem B20637011 : Blo 2145435 20637011 := bstep (se 1 (by rfl) ⟨15477758, by rfl⟩ : syracuseStep 20637011 = 30955517) B30955517
theorem B13758007 : Blo 2145435 13758007 := bstep (se 1 (by rfl) ⟨10318505, by rfl⟩ : syracuseStep 13758007 = 20637011) B20637011
theorem B18344009 : Blo 2145435 18344009 := bstep (se 2 (by rfl) ⟨6879003, by rfl⟩ : syracuseStep 18344009 = 13758007) B13758007
theorem B12229339 : Blo 2145435 12229339 := bstep (se 1 (by rfl) ⟨9172004, by rfl⟩ : syracuseStep 12229339 = 18344009) B18344009
theorem B16305785 : Blo 2145435 16305785 := bstep (se 2 (by rfl) ⟨6114669, by rfl⟩ : syracuseStep 16305785 = 12229339) B12229339
theorem B10870523 : Blo 2145435 10870523 := bstep (se 1 (by rfl) ⟨8152892, by rfl⟩ : syracuseStep 10870523 = 16305785) B16305785
theorem B7247015 : Blo 2145435 7247015 := bstep (se 1 (by rfl) ⟨5435261, by rfl⟩ : syracuseStep 7247015 = 10870523) B10870523
theorem B4831343 : Blo 2145435 4831343 := bstep (se 1 (by rfl) ⟨3623507, by rfl⟩ : syracuseStep 4831343 = 7247015) B7247015
theorem B3220895 : Blo 2145435 3220895 := bstep (se 1 (by rfl) ⟨2415671, by rfl⟩ : syracuseStep 3220895 = 4831343) B4831343
theorem B2147263 : Blo 2145435 2147263 := bstep (se 1 (by rfl) ⟨1610447, by rfl⟩ : syracuseStep 2147263 = 3220895) B3220895
theorem B3220901 : Blo 2145435 3220901 := bbase (se 4 (by rfl) ⟨301959, by rfl⟩ : syracuseStep 3220901 = 603919) (by norm_num)
theorem B2147267 : Blo 2145435 2147267 := bstep (se 1 (by rfl) ⟨1610450, by rfl⟩ : syracuseStep 2147267 = 3220901) B3220901
theorem B2717641 : Blo 2145435 2717641 := bbase (se 2 (by rfl) ⟨1019115, by rfl⟩ : syracuseStep 2717641 = 2038231) (by norm_num)
theorem B3623521 : Blo 2145435 3623521 := bstep (se 2 (by rfl) ⟨1358820, by rfl⟩ : syracuseStep 3623521 = 2717641) B2717641
theorem B4831361 : Blo 2145435 4831361 := bstep (se 2 (by rfl) ⟨1811760, by rfl⟩ : syracuseStep 4831361 = 3623521) B3623521
theorem B3220907 : Blo 2145435 3220907 := bstep (se 1 (by rfl) ⟨2415680, by rfl⟩ : syracuseStep 3220907 = 4831361) B4831361
theorem B2147271 : Blo 2145435 2147271 := bstep (se 1 (by rfl) ⟨1610453, by rfl⟩ : syracuseStep 2147271 = 3220907) B3220907
theorem B2415685 : Blo 2145435 2415685 := bbase (se 4 (by rfl) ⟨226470, by rfl⟩ : syracuseStep 2415685 = 452941) (by norm_num)
theorem B3220913 : Blo 2145435 3220913 := bstep (se 2 (by rfl) ⟨1207842, by rfl⟩ : syracuseStep 3220913 = 2415685) B2415685
theorem B2147275 : Blo 2145435 2147275 := bstep (se 1 (by rfl) ⟨1610456, by rfl⟩ : syracuseStep 2147275 = 3220913) B3220913
theorem B4076477 : Blo 2145435 4076477 := bbase (se 3 (by rfl) ⟨764339, by rfl⟩ : syracuseStep 4076477 = 1528679) (by norm_num)
theorem B2717651 : Blo 2145435 2717651 := bstep (se 1 (by rfl) ⟨2038238, by rfl⟩ : syracuseStep 2717651 = 4076477) B4076477
theorem B7247069 : Blo 2145435 7247069 := bstep (se 3 (by rfl) ⟨1358825, by rfl⟩ : syracuseStep 7247069 = 2717651) B2717651
theorem B4831379 : Blo 2145435 4831379 := bstep (se 1 (by rfl) ⟨3623534, by rfl⟩ : syracuseStep 4831379 = 7247069) B7247069
theorem B3220919 : Blo 2145435 3220919 := bstep (se 1 (by rfl) ⟨2415689, by rfl⟩ : syracuseStep 3220919 = 4831379) B4831379
theorem B2147279 : Blo 2145435 2147279 := bstep (se 1 (by rfl) ⟨1610459, by rfl⟩ : syracuseStep 2147279 = 3220919) B3220919
theorem B3220925 : Blo 2145435 3220925 := bbase (se 3 (by rfl) ⟨603923, by rfl⟩ : syracuseStep 3220925 = 1207847) (by norm_num)
theorem B2147283 : Blo 2145435 2147283 := bstep (se 1 (by rfl) ⟨1610462, by rfl⟩ : syracuseStep 2147283 = 3220925) B3220925
theorem B4831397 : Blo 2145435 4831397 := bbase (se 4 (by rfl) ⟨452943, by rfl⟩ : syracuseStep 4831397 = 905887) (by norm_num)
theorem B3220931 : Blo 2145435 3220931 := bstep (se 1 (by rfl) ⟨2415698, by rfl⟩ : syracuseStep 3220931 = 4831397) B4831397
theorem B2147287 : Blo 2145435 2147287 := bstep (se 1 (by rfl) ⟨1610465, by rfl⟩ : syracuseStep 2147287 = 3220931) B3220931
theorem B5435333 : Blo 2145435 5435333 := bbase (se 4 (by rfl) ⟨509562, by rfl⟩ : syracuseStep 5435333 = 1019125) (by norm_num)
theorem B3623555 : Blo 2145435 3623555 := bstep (se 1 (by rfl) ⟨2717666, by rfl⟩ : syracuseStep 3623555 = 5435333) B5435333
theorem B2415703 : Blo 2145435 2415703 := bstep (se 1 (by rfl) ⟨1811777, by rfl⟩ : syracuseStep 2415703 = 3623555) B3623555
theorem B3220937 : Blo 2145435 3220937 := bstep (se 2 (by rfl) ⟨1207851, by rfl⟩ : syracuseStep 3220937 = 2415703) B2415703
theorem B2147291 : Blo 2145435 2147291 := bstep (se 1 (by rfl) ⟨1610468, by rfl⟩ : syracuseStep 2147291 = 3220937) B3220937
theorem B10318661 : Blo 2145435 10318661 := bbase (se 4 (by rfl) ⟨967374, by rfl⟩ : syracuseStep 10318661 = 1934749) (by norm_num)
theorem B6879107 : Blo 2145435 6879107 := bstep (se 1 (by rfl) ⟨5159330, by rfl⟩ : syracuseStep 6879107 = 10318661) B10318661
theorem B4586071 : Blo 2145435 4586071 := bstep (se 1 (by rfl) ⟨3439553, by rfl⟩ : syracuseStep 4586071 = 6879107) B6879107
theorem B6114761 : Blo 2145435 6114761 := bstep (se 2 (by rfl) ⟨2293035, by rfl⟩ : syracuseStep 6114761 = 4586071) B4586071
theorem B4076507 : Blo 2145435 4076507 := bstep (se 1 (by rfl) ⟨3057380, by rfl⟩ : syracuseStep 4076507 = 6114761) B6114761
theorem B10870685 : Blo 2145435 10870685 := bstep (se 3 (by rfl) ⟨2038253, by rfl⟩ : syracuseStep 10870685 = 4076507) B4076507
theorem B7247123 : Blo 2145435 7247123 := bstep (se 1 (by rfl) ⟨5435342, by rfl⟩ : syracuseStep 7247123 = 10870685) B10870685
theorem B4831415 : Blo 2145435 4831415 := bstep (se 1 (by rfl) ⟨3623561, by rfl⟩ : syracuseStep 4831415 = 7247123) B7247123
theorem B3220943 : Blo 2145435 3220943 := bstep (se 1 (by rfl) ⟨2415707, by rfl⟩ : syracuseStep 3220943 = 4831415) B4831415
theorem B2147295 : Blo 2145435 2147295 := bstep (se 1 (by rfl) ⟨1610471, by rfl⟩ : syracuseStep 2147295 = 3220943) B3220943
theorem B3220949 : Blo 2145435 3220949 := bbase (se 7 (by rfl) ⟨37745, by rfl⟩ : syracuseStep 3220949 = 75491) (by norm_num)
theorem B2147299 : Blo 2145435 2147299 := bstep (se 1 (by rfl) ⟨1610474, by rfl⟩ : syracuseStep 2147299 = 3220949) B3220949
theorem B8153045 : Blo 2145435 8153045 := bbase (se 7 (by rfl) ⟨95543, by rfl⟩ : syracuseStep 8153045 = 191087) (by norm_num)
theorem B5435363 : Blo 2145435 5435363 := bstep (se 1 (by rfl) ⟨4076522, by rfl⟩ : syracuseStep 5435363 = 8153045) B8153045
theorem B3623575 : Blo 2145435 3623575 := bstep (se 1 (by rfl) ⟨2717681, by rfl⟩ : syracuseStep 3623575 = 5435363) B5435363
theorem B4831433 : Blo 2145435 4831433 := bstep (se 2 (by rfl) ⟨1811787, by rfl⟩ : syracuseStep 4831433 = 3623575) B3623575
theorem B3220955 : Blo 2145435 3220955 := bstep (se 1 (by rfl) ⟨2415716, by rfl⟩ : syracuseStep 3220955 = 4831433) B4831433
theorem B2147303 : Blo 2145435 2147303 := bstep (se 1 (by rfl) ⟨1610477, by rfl⟩ : syracuseStep 2147303 = 3220955) B3220955
theorem B2415721 : Blo 2145435 2415721 := bbase (se 2 (by rfl) ⟨905895, by rfl⟩ : syracuseStep 2415721 = 1811791) (by norm_num)
theorem B3220961 : Blo 2145435 3220961 := bstep (se 2 (by rfl) ⟨1207860, by rfl⟩ : syracuseStep 3220961 = 2415721) B2415721
theorem B2147307 : Blo 2145435 2147307 := bstep (se 1 (by rfl) ⟨1610480, by rfl⟩ : syracuseStep 2147307 = 3220961) B3220961
theorem B8706437 : Blo 2145435 8706437 := bbase (se 4 (by rfl) ⟨816228, by rfl⟩ : syracuseStep 8706437 = 1632457) (by norm_num)
theorem B5804291 : Blo 2145435 5804291 := bstep (se 1 (by rfl) ⟨4353218, by rfl⟩ : syracuseStep 5804291 = 8706437) B8706437
theorem B3869527 : Blo 2145435 3869527 := bstep (se 1 (by rfl) ⟨2902145, by rfl⟩ : syracuseStep 3869527 = 5804291) B5804291
theorem B5159369 : Blo 2145435 5159369 := bstep (se 2 (by rfl) ⟨1934763, by rfl⟩ : syracuseStep 5159369 = 3869527) B3869527
theorem B3439579 : Blo 2145435 3439579 := bstep (se 1 (by rfl) ⟨2579684, by rfl⟩ : syracuseStep 3439579 = 5159369) B5159369
theorem B4586105 : Blo 2145435 4586105 := bstep (se 2 (by rfl) ⟨1719789, by rfl⟩ : syracuseStep 4586105 = 3439579) B3439579
theorem B12229613 : Blo 2145435 12229613 := bstep (se 3 (by rfl) ⟨2293052, by rfl⟩ : syracuseStep 12229613 = 4586105) B4586105
theorem B8153075 : Blo 2145435 8153075 := bstep (se 1 (by rfl) ⟨6114806, by rfl⟩ : syracuseStep 8153075 = 12229613) B12229613
theorem B5435383 : Blo 2145435 5435383 := bstep (se 1 (by rfl) ⟨4076537, by rfl⟩ : syracuseStep 5435383 = 8153075) B8153075
theorem B7247177 : Blo 2145435 7247177 := bstep (se 2 (by rfl) ⟨2717691, by rfl⟩ : syracuseStep 7247177 = 5435383) B5435383
theorem B4831451 : Blo 2145435 4831451 := bstep (se 1 (by rfl) ⟨3623588, by rfl⟩ : syracuseStep 4831451 = 7247177) B7247177
theorem B3220967 : Blo 2145435 3220967 := bstep (se 1 (by rfl) ⟨2415725, by rfl⟩ : syracuseStep 3220967 = 4831451) B4831451
theorem B2147311 : Blo 2145435 2147311 := bstep (se 1 (by rfl) ⟨1610483, by rfl⟩ : syracuseStep 2147311 = 3220967) B3220967
theorem B3220973 : Blo 2145435 3220973 := bbase (se 3 (by rfl) ⟨603932, by rfl⟩ : syracuseStep 3220973 = 1207865) (by norm_num)
theorem B2147315 : Blo 2145435 2147315 := bstep (se 1 (by rfl) ⟨1610486, by rfl⟩ : syracuseStep 2147315 = 3220973) B3220973
theorem B4831469 : Blo 2145435 4831469 := bbase (se 3 (by rfl) ⟨905900, by rfl⟩ : syracuseStep 4831469 = 1811801) (by norm_num)
theorem B3220979 : Blo 2145435 3220979 := bstep (se 1 (by rfl) ⟨2415734, by rfl⟩ : syracuseStep 3220979 = 4831469) B4831469
theorem B2147319 : Blo 2145435 2147319 := bstep (se 1 (by rfl) ⟨1610489, by rfl⟩ : syracuseStep 2147319 = 3220979) B3220979
theorem B3057421 : Blo 2145435 3057421 := bbase (se 3 (by rfl) ⟨573266, by rfl⟩ : syracuseStep 3057421 = 1146533) (by norm_num)
theorem B4076561 : Blo 2145435 4076561 := bstep (se 2 (by rfl) ⟨1528710, by rfl⟩ : syracuseStep 4076561 = 3057421) B3057421
theorem B2717707 : Blo 2145435 2717707 := bstep (se 1 (by rfl) ⟨2038280, by rfl⟩ : syracuseStep 2717707 = 4076561) B4076561
theorem B3623609 : Blo 2145435 3623609 := bstep (se 2 (by rfl) ⟨1358853, by rfl⟩ : syracuseStep 3623609 = 2717707) B2717707
theorem B2415739 : Blo 2145435 2415739 := bstep (se 1 (by rfl) ⟨1811804, by rfl⟩ : syracuseStep 2415739 = 3623609) B3623609
theorem B3220985 : Blo 2145435 3220985 := bstep (se 2 (by rfl) ⟨1207869, by rfl⟩ : syracuseStep 3220985 = 2415739) B2415739
theorem B2147323 : Blo 2145435 2147323 := bstep (se 1 (by rfl) ⟨1610492, by rfl⟩ : syracuseStep 2147323 = 3220985) B3220985
theorem B4412645 : Blo 2145435 4412645 := bbase (se 4 (by rfl) ⟨413685, by rfl⟩ : syracuseStep 4412645 = 827371) (by norm_num)
theorem B2941763 : Blo 2145435 2941763 := bstep (se 1 (by rfl) ⟨2206322, by rfl⟩ : syracuseStep 2941763 = 4412645) B4412645
theorem B7844701 : Blo 2145435 7844701 := bstep (se 3 (by rfl) ⟨1470881, by rfl⟩ : syracuseStep 7844701 = 2941763) B2941763
theorem B10459601 : Blo 2145435 10459601 := bstep (se 2 (by rfl) ⟨3922350, by rfl⟩ : syracuseStep 10459601 = 7844701) B7844701
theorem B6973067 : Blo 2145435 6973067 := bstep (se 1 (by rfl) ⟨5229800, by rfl⟩ : syracuseStep 6973067 = 10459601) B10459601
theorem B18594845 : Blo 2145435 18594845 := bstep (se 3 (by rfl) ⟨3486533, by rfl⟩ : syracuseStep 18594845 = 6973067) B6973067
theorem B12396563 : Blo 2145435 12396563 := bstep (se 1 (by rfl) ⟨9297422, by rfl⟩ : syracuseStep 12396563 = 18594845) B18594845
theorem B8264375 : Blo 2145435 8264375 := bstep (se 1 (by rfl) ⟨6198281, by rfl⟩ : syracuseStep 8264375 = 12396563) B12396563
theorem B5509583 : Blo 2145435 5509583 := bstep (se 1 (by rfl) ⟨4132187, by rfl⟩ : syracuseStep 5509583 = 8264375) B8264375
theorem B3673055 : Blo 2145435 3673055 := bstep (se 1 (by rfl) ⟨2754791, by rfl⟩ : syracuseStep 3673055 = 5509583) B5509583
theorem B2448703 : Blo 2145435 2448703 := bstep (se 1 (by rfl) ⟨1836527, by rfl⟩ : syracuseStep 2448703 = 3673055) B3673055
theorem B3264937 : Blo 2145435 3264937 := bstep (se 2 (by rfl) ⟨1224351, by rfl⟩ : syracuseStep 3264937 = 2448703) B2448703
theorem B17412997 : Blo 2145435 17412997 := bstep (se 4 (by rfl) ⟨1632468, by rfl⟩ : syracuseStep 17412997 = 3264937) B3264937
theorem B23217329 : Blo 2145435 23217329 := bstep (se 2 (by rfl) ⟨8706498, by rfl⟩ : syracuseStep 23217329 = 17412997) B17412997
theorem B15478219 : Blo 2145435 15478219 := bstep (se 1 (by rfl) ⟨11608664, by rfl⟩ : syracuseStep 15478219 = 23217329) B23217329
theorem B82550501 : Blo 2145435 82550501 := bstep (se 4 (by rfl) ⟨7739109, by rfl⟩ : syracuseStep 82550501 = 15478219) B15478219
theorem B55033667 : Blo 2145435 55033667 := bstep (se 1 (by rfl) ⟨41275250, by rfl⟩ : syracuseStep 55033667 = 82550501) B82550501
theorem B36689111 : Blo 2145435 36689111 := bstep (se 1 (by rfl) ⟨27516833, by rfl⟩ : syracuseStep 36689111 = 55033667) B55033667
theorem B24459407 : Blo 2145435 24459407 := bstep (se 1 (by rfl) ⟨18344555, by rfl⟩ : syracuseStep 24459407 = 36689111) B36689111
theorem B16306271 : Blo 2145435 16306271 := bstep (se 1 (by rfl) ⟨12229703, by rfl⟩ : syracuseStep 16306271 = 24459407) B24459407
theorem B10870847 : Blo 2145435 10870847 := bstep (se 1 (by rfl) ⟨8153135, by rfl⟩ : syracuseStep 10870847 = 16306271) B16306271
theorem B7247231 : Blo 2145435 7247231 := bstep (se 1 (by rfl) ⟨5435423, by rfl⟩ : syracuseStep 7247231 = 10870847) B10870847
theorem B4831487 : Blo 2145435 4831487 := bstep (se 1 (by rfl) ⟨3623615, by rfl⟩ : syracuseStep 4831487 = 7247231) B7247231
theorem B3220991 : Blo 2145435 3220991 := bstep (se 1 (by rfl) ⟨2415743, by rfl⟩ : syracuseStep 3220991 = 4831487) B4831487
theorem B2147327 : Blo 2145435 2147327 := bstep (se 1 (by rfl) ⟨1610495, by rfl⟩ : syracuseStep 2147327 = 3220991) B3220991
theorem B3220997 : Blo 2145435 3220997 := bbase (se 4 (by rfl) ⟨301968, by rfl⟩ : syracuseStep 3220997 = 603937) (by norm_num)
theorem B2147331 : Blo 2145435 2147331 := bstep (se 1 (by rfl) ⟨1610498, by rfl⟩ : syracuseStep 2147331 = 3220997) B3220997
theorem B3623629 : Blo 2145435 3623629 := bbase (se 3 (by rfl) ⟨679430, by rfl⟩ : syracuseStep 3623629 = 1358861) (by norm_num)
theorem B4831505 : Blo 2145435 4831505 := bstep (se 2 (by rfl) ⟨1811814, by rfl⟩ : syracuseStep 4831505 = 3623629) B3623629
theorem B3221003 : Blo 2145435 3221003 := bstep (se 1 (by rfl) ⟨2415752, by rfl⟩ : syracuseStep 3221003 = 4831505) B4831505
theorem B2147335 : Blo 2145435 2147335 := bstep (se 1 (by rfl) ⟨1610501, by rfl⟩ : syracuseStep 2147335 = 3221003) B3221003
theorem B2415757 : Blo 2145435 2415757 := bbase (se 3 (by rfl) ⟨452954, by rfl⟩ : syracuseStep 2415757 = 905909) (by norm_num)
theorem B3221009 : Blo 2145435 3221009 := bstep (se 2 (by rfl) ⟨1207878, by rfl⟩ : syracuseStep 3221009 = 2415757) B2415757
theorem B2147339 : Blo 2145435 2147339 := bstep (se 1 (by rfl) ⟨1610504, by rfl⟩ : syracuseStep 2147339 = 3221009) B3221009
theorem B7247285 : Blo 2145435 7247285 := bbase (se 5 (by rfl) ⟨339716, by rfl⟩ : syracuseStep 7247285 = 679433) (by norm_num)
theorem B4831523 : Blo 2145435 4831523 := bstep (se 1 (by rfl) ⟨3623642, by rfl⟩ : syracuseStep 4831523 = 7247285) B7247285
theorem B3221015 : Blo 2145435 3221015 := bstep (se 1 (by rfl) ⟨2415761, by rfl⟩ : syracuseStep 3221015 = 4831523) B4831523
theorem B2147343 : Blo 2145435 2147343 := bstep (se 1 (by rfl) ⟨1610507, by rfl⟩ : syracuseStep 2147343 = 3221015) B3221015
theorem B3221021 : Blo 2145435 3221021 := bbase (se 3 (by rfl) ⟨603941, by rfl⟩ : syracuseStep 3221021 = 1207883) (by norm_num)
theorem B2147347 : Blo 2145435 2147347 := bstep (se 1 (by rfl) ⟨1610510, by rfl⟩ : syracuseStep 2147347 = 3221021) B3221021
theorem B4831541 : Blo 2145435 4831541 := bbase (se 5 (by rfl) ⟨226478, by rfl⟩ : syracuseStep 4831541 = 452957) (by norm_num)
theorem B3221027 : Blo 2145435 3221027 := bstep (se 1 (by rfl) ⟨2415770, by rfl⟩ : syracuseStep 3221027 = 4831541) B4831541
theorem B2147351 : Blo 2145435 2147351 := bstep (se 1 (by rfl) ⟨1610513, by rfl⟩ : syracuseStep 2147351 = 3221027) B3221027
theorem B7446437 : Blo 2145435 7446437 := bbase (se 4 (by rfl) ⟨698103, by rfl⟩ : syracuseStep 7446437 = 1396207) (by norm_num)
theorem B4964291 : Blo 2145435 4964291 := bstep (se 1 (by rfl) ⟨3723218, by rfl⟩ : syracuseStep 4964291 = 7446437) B7446437
theorem B3309527 : Blo 2145435 3309527 := bstep (se 1 (by rfl) ⟨2482145, by rfl⟩ : syracuseStep 3309527 = 4964291) B4964291
theorem B2206351 : Blo 2145435 2206351 := bstep (se 1 (by rfl) ⟨1654763, by rfl⟩ : syracuseStep 2206351 = 3309527) B3309527
theorem B11767205 : Blo 2145435 11767205 := bstep (se 4 (by rfl) ⟨1103175, by rfl⟩ : syracuseStep 11767205 = 2206351) B2206351
theorem B31379213 : Blo 2145435 31379213 := bstep (se 3 (by rfl) ⟨5883602, by rfl⟩ : syracuseStep 31379213 = 11767205) B11767205
theorem B20919475 : Blo 2145435 20919475 := bstep (se 1 (by rfl) ⟨15689606, by rfl⟩ : syracuseStep 20919475 = 31379213) B31379213
theorem B27892633 : Blo 2145435 27892633 := bstep (se 2 (by rfl) ⟨10459737, by rfl⟩ : syracuseStep 27892633 = 20919475) B20919475
theorem B37190177 : Blo 2145435 37190177 := bstep (se 2 (by rfl) ⟨13946316, by rfl⟩ : syracuseStep 37190177 = 27892633) B27892633
theorem B24793451 : Blo 2145435 24793451 := bstep (se 1 (by rfl) ⟨18595088, by rfl⟩ : syracuseStep 24793451 = 37190177) B37190177
theorem B16528967 : Blo 2145435 16528967 := bstep (se 1 (by rfl) ⟨12396725, by rfl⟩ : syracuseStep 16528967 = 24793451) B24793451
theorem B11019311 : Blo 2145435 11019311 := bstep (se 1 (by rfl) ⟨8264483, by rfl⟩ : syracuseStep 11019311 = 16528967) B16528967
theorem B7346207 : Blo 2145435 7346207 := bstep (se 1 (by rfl) ⟨5509655, by rfl⟩ : syracuseStep 7346207 = 11019311) B11019311
theorem B4897471 : Blo 2145435 4897471 := bstep (se 1 (by rfl) ⟨3673103, by rfl⟩ : syracuseStep 4897471 = 7346207) B7346207
theorem B6529961 : Blo 2145435 6529961 := bstep (se 2 (by rfl) ⟨2448735, by rfl⟩ : syracuseStep 6529961 = 4897471) B4897471
theorem B4353307 : Blo 2145435 4353307 := bstep (se 1 (by rfl) ⟨3264980, by rfl⟩ : syracuseStep 4353307 = 6529961) B6529961
theorem B23217637 : Blo 2145435 23217637 := bstep (se 4 (by rfl) ⟨2176653, by rfl⟩ : syracuseStep 23217637 = 4353307) B4353307
theorem B30956849 : Blo 2145435 30956849 := bstep (se 2 (by rfl) ⟨11608818, by rfl⟩ : syracuseStep 30956849 = 23217637) B23217637
theorem B20637899 : Blo 2145435 20637899 := bstep (se 1 (by rfl) ⟨15478424, by rfl⟩ : syracuseStep 20637899 = 30956849) B30956849
theorem B13758599 : Blo 2145435 13758599 := bstep (se 1 (by rfl) ⟨10318949, by rfl⟩ : syracuseStep 13758599 = 20637899) B20637899
theorem B9172399 : Blo 2145435 9172399 := bstep (se 1 (by rfl) ⟨6879299, by rfl⟩ : syracuseStep 9172399 = 13758599) B13758599
theorem B12229865 : Blo 2145435 12229865 := bstep (se 2 (by rfl) ⟨4586199, by rfl⟩ : syracuseStep 12229865 = 9172399) B9172399
theorem B8153243 : Blo 2145435 8153243 := bstep (se 1 (by rfl) ⟨6114932, by rfl⟩ : syracuseStep 8153243 = 12229865) B12229865
theorem B5435495 : Blo 2145435 5435495 := bstep (se 1 (by rfl) ⟨4076621, by rfl⟩ : syracuseStep 5435495 = 8153243) B8153243
theorem B3623663 : Blo 2145435 3623663 := bstep (se 1 (by rfl) ⟨2717747, by rfl⟩ : syracuseStep 3623663 = 5435495) B5435495
theorem B2415775 : Blo 2145435 2415775 := bstep (se 1 (by rfl) ⟨1811831, by rfl⟩ : syracuseStep 2415775 = 3623663) B3623663
theorem B3221033 : Blo 2145435 3221033 := bstep (se 2 (by rfl) ⟨1207887, by rfl⟩ : syracuseStep 3221033 = 2415775) B2415775
theorem B2147355 : Blo 2145435 2147355 := bstep (se 1 (by rfl) ⟨1610516, by rfl⟩ : syracuseStep 2147355 = 3221033) B3221033
theorem B2792417 : Blo 2145435 2792417 := bbase (se 2 (by rfl) ⟨1047156, by rfl⟩ : syracuseStep 2792417 = 2094313) (by norm_num)
theorem B29785781 : Blo 2145435 29785781 := bstep (se 5 (by rfl) ⟨1396208, by rfl⟩ : syracuseStep 29785781 = 2792417) B2792417
theorem B19857187 : Blo 2145435 19857187 := bstep (se 1 (by rfl) ⟨14892890, by rfl⟩ : syracuseStep 19857187 = 29785781) B29785781
theorem B26476249 : Blo 2145435 26476249 := bstep (se 2 (by rfl) ⟨9928593, by rfl⟩ : syracuseStep 26476249 = 19857187) B19857187
theorem B35301665 : Blo 2145435 35301665 := bstep (se 2 (by rfl) ⟨13238124, by rfl⟩ : syracuseStep 35301665 = 26476249) B26476249
theorem B94137773 : Blo 2145435 94137773 := bstep (se 3 (by rfl) ⟨17650832, by rfl⟩ : syracuseStep 94137773 = 35301665) B35301665
theorem B251034061 : Blo 2145435 251034061 := bstep (se 3 (by rfl) ⟨47068886, by rfl⟩ : syracuseStep 251034061 = 94137773) B94137773
theorem B334712081 : Blo 2145435 334712081 := bstep (se 2 (by rfl) ⟨125517030, by rfl⟩ : syracuseStep 334712081 = 251034061) B251034061
theorem B223141387 : Blo 2145435 223141387 := bstep (se 1 (by rfl) ⟨167356040, by rfl⟩ : syracuseStep 223141387 = 334712081) B334712081
theorem B297521849 : Blo 2145435 297521849 := bstep (se 2 (by rfl) ⟨111570693, by rfl⟩ : syracuseStep 297521849 = 223141387) B223141387
theorem B198347899 : Blo 2145435 198347899 := bstep (se 1 (by rfl) ⟨148760924, by rfl⟩ : syracuseStep 198347899 = 297521849) B297521849
theorem B264463865 : Blo 2145435 264463865 := bstep (se 2 (by rfl) ⟨99173949, by rfl⟩ : syracuseStep 264463865 = 198347899) B198347899
theorem B176309243 : Blo 2145435 176309243 := bstep (se 1 (by rfl) ⟨132231932, by rfl⟩ : syracuseStep 176309243 = 264463865) B264463865
theorem B117539495 : Blo 2145435 117539495 := bstep (se 1 (by rfl) ⟨88154621, by rfl⟩ : syracuseStep 117539495 = 176309243) B176309243
theorem B78359663 : Blo 2145435 78359663 := bstep (se 1 (by rfl) ⟨58769747, by rfl⟩ : syracuseStep 78359663 = 117539495) B117539495
theorem B52239775 : Blo 2145435 52239775 := bstep (se 1 (by rfl) ⟨39179831, by rfl⟩ : syracuseStep 52239775 = 78359663) B78359663
theorem B69653033 : Blo 2145435 69653033 := bstep (se 2 (by rfl) ⟨26119887, by rfl⟩ : syracuseStep 69653033 = 52239775) B52239775
theorem B46435355 : Blo 2145435 46435355 := bstep (se 1 (by rfl) ⟨34826516, by rfl⟩ : syracuseStep 46435355 = 69653033) B69653033
theorem B30956903 : Blo 2145435 30956903 := bstep (se 1 (by rfl) ⟨23217677, by rfl⟩ : syracuseStep 30956903 = 46435355) B46435355
theorem B20637935 : Blo 2145435 20637935 := bstep (se 1 (by rfl) ⟨15478451, by rfl⟩ : syracuseStep 20637935 = 30956903) B30956903
theorem B13758623 : Blo 2145435 13758623 := bstep (se 1 (by rfl) ⟨10318967, by rfl⟩ : syracuseStep 13758623 = 20637935) B20637935
theorem B9172415 : Blo 2145435 9172415 := bstep (se 1 (by rfl) ⟨6879311, by rfl⟩ : syracuseStep 9172415 = 13758623) B13758623
theorem B6114943 : Blo 2145435 6114943 := bstep (se 1 (by rfl) ⟨4586207, by rfl⟩ : syracuseStep 6114943 = 9172415) B9172415
theorem B8153257 : Blo 2145435 8153257 := bstep (se 2 (by rfl) ⟨3057471, by rfl⟩ : syracuseStep 8153257 = 6114943) B6114943
theorem B10871009 : Blo 2145435 10871009 := bstep (se 2 (by rfl) ⟨4076628, by rfl⟩ : syracuseStep 10871009 = 8153257) B8153257
theorem B7247339 : Blo 2145435 7247339 := bstep (se 1 (by rfl) ⟨5435504, by rfl⟩ : syracuseStep 7247339 = 10871009) B10871009
theorem B4831559 : Blo 2145435 4831559 := bstep (se 1 (by rfl) ⟨3623669, by rfl⟩ : syracuseStep 4831559 = 7247339) B7247339
theorem B3221039 : Blo 2145435 3221039 := bstep (se 1 (by rfl) ⟨2415779, by rfl⟩ : syracuseStep 3221039 = 4831559) B4831559
theorem B2147359 : Blo 2145435 2147359 := bstep (se 1 (by rfl) ⟨1610519, by rfl⟩ : syracuseStep 2147359 = 3221039) B3221039
theorem B3221045 : Blo 2145435 3221045 := bbase (se 5 (by rfl) ⟨150986, by rfl⟩ : syracuseStep 3221045 = 301973) (by norm_num)
theorem B2147363 : Blo 2145435 2147363 := bstep (se 1 (by rfl) ⟨1610522, by rfl⟩ : syracuseStep 2147363 = 3221045) B3221045
theorem B5435525 : Blo 2145435 5435525 := bbase (se 4 (by rfl) ⟨509580, by rfl⟩ : syracuseStep 5435525 = 1019161) (by norm_num)
theorem B3623683 : Blo 2145435 3623683 := bstep (se 1 (by rfl) ⟨2717762, by rfl⟩ : syracuseStep 3623683 = 5435525) B5435525
theorem B4831577 : Blo 2145435 4831577 := bstep (se 2 (by rfl) ⟨1811841, by rfl⟩ : syracuseStep 4831577 = 3623683) B3623683
theorem B3221051 : Blo 2145435 3221051 := bstep (se 1 (by rfl) ⟨2415788, by rfl⟩ : syracuseStep 3221051 = 4831577) B4831577
theorem B2147367 : Blo 2145435 2147367 := bstep (se 1 (by rfl) ⟨1610525, by rfl⟩ : syracuseStep 2147367 = 3221051) B3221051
theorem B2415793 : Blo 2145435 2415793 := bbase (se 2 (by rfl) ⟨905922, by rfl⟩ : syracuseStep 2415793 = 1811845) (by norm_num)
theorem B3221057 : Blo 2145435 3221057 := bstep (se 2 (by rfl) ⟨1207896, by rfl⟩ : syracuseStep 3221057 = 2415793) B2415793
theorem B2147371 : Blo 2145435 2147371 := bstep (se 1 (by rfl) ⟨1610528, by rfl⟩ : syracuseStep 2147371 = 3221057) B3221057
theorem B2293121 : Blo 2145435 2293121 := bbase (se 2 (by rfl) ⟨859920, by rfl⟩ : syracuseStep 2293121 = 1719841) (by norm_num)
theorem B6114989 : Blo 2145435 6114989 := bstep (se 3 (by rfl) ⟨1146560, by rfl⟩ : syracuseStep 6114989 = 2293121) B2293121
theorem B4076659 : Blo 2145435 4076659 := bstep (se 1 (by rfl) ⟨3057494, by rfl⟩ : syracuseStep 4076659 = 6114989) B6114989
theorem B5435545 : Blo 2145435 5435545 := bstep (se 2 (by rfl) ⟨2038329, by rfl⟩ : syracuseStep 5435545 = 4076659) B4076659
theorem B7247393 : Blo 2145435 7247393 := bstep (se 2 (by rfl) ⟨2717772, by rfl⟩ : syracuseStep 7247393 = 5435545) B5435545
theorem B4831595 : Blo 2145435 4831595 := bstep (se 1 (by rfl) ⟨3623696, by rfl⟩ : syracuseStep 4831595 = 7247393) B7247393
theorem B3221063 : Blo 2145435 3221063 := bstep (se 1 (by rfl) ⟨2415797, by rfl⟩ : syracuseStep 3221063 = 4831595) B4831595
theorem B2147375 : Blo 2145435 2147375 := bstep (se 1 (by rfl) ⟨1610531, by rfl⟩ : syracuseStep 2147375 = 3221063) B3221063
theorem B3221069 : Blo 2145435 3221069 := bbase (se 3 (by rfl) ⟨603950, by rfl⟩ : syracuseStep 3221069 = 1207901) (by norm_num)
theorem B2147379 : Blo 2145435 2147379 := bstep (se 1 (by rfl) ⟨1610534, by rfl⟩ : syracuseStep 2147379 = 3221069) B3221069
theorem B4831613 : Blo 2145435 4831613 := bbase (se 3 (by rfl) ⟨905927, by rfl⟩ : syracuseStep 4831613 = 1811855) (by norm_num)
theorem B3221075 : Blo 2145435 3221075 := bstep (se 1 (by rfl) ⟨2415806, by rfl⟩ : syracuseStep 3221075 = 4831613) B4831613
theorem B2147383 : Blo 2145435 2147383 := bstep (se 1 (by rfl) ⟨1610537, by rfl⟩ : syracuseStep 2147383 = 3221075) B3221075
theorem B3623717 : Blo 2145435 3623717 := bbase (se 4 (by rfl) ⟨339723, by rfl⟩ : syracuseStep 3623717 = 679447) (by norm_num)
theorem B2415811 : Blo 2145435 2415811 := bstep (se 1 (by rfl) ⟨1811858, by rfl⟩ : syracuseStep 2415811 = 3623717) B3623717
theorem B3221081 : Blo 2145435 3221081 := bstep (se 2 (by rfl) ⟨1207905, by rfl⟩ : syracuseStep 3221081 = 2415811) B2415811
theorem B2147387 : Blo 2145435 2147387 := bstep (se 1 (by rfl) ⟨1610540, by rfl⟩ : syracuseStep 2147387 = 3221081) B3221081
theorem B3057517 : Blo 2145435 3057517 := bbase (se 3 (by rfl) ⟨573284, by rfl⟩ : syracuseStep 3057517 = 1146569) (by norm_num)
theorem B16306757 : Blo 2145435 16306757 := bstep (se 4 (by rfl) ⟨1528758, by rfl⟩ : syracuseStep 16306757 = 3057517) B3057517
theorem B10871171 : Blo 2145435 10871171 := bstep (se 1 (by rfl) ⟨8153378, by rfl⟩ : syracuseStep 10871171 = 16306757) B16306757
theorem B7247447 : Blo 2145435 7247447 := bstep (se 1 (by rfl) ⟨5435585, by rfl⟩ : syracuseStep 7247447 = 10871171) B10871171
theorem B4831631 : Blo 2145435 4831631 := bstep (se 1 (by rfl) ⟨3623723, by rfl⟩ : syracuseStep 4831631 = 7247447) B7247447
theorem B3221087 : Blo 2145435 3221087 := bstep (se 1 (by rfl) ⟨2415815, by rfl⟩ : syracuseStep 3221087 = 4831631) B4831631
theorem B2147391 : Blo 2145435 2147391 := bstep (se 1 (by rfl) ⟨1610543, by rfl⟩ : syracuseStep 2147391 = 3221087) B3221087
theorem B3221093 : Blo 2145435 3221093 := bbase (se 4 (by rfl) ⟨301977, by rfl⟩ : syracuseStep 3221093 = 603955) (by norm_num)
theorem B2147395 : Blo 2145435 2147395 := bstep (se 1 (by rfl) ⟨1610546, by rfl⟩ : syracuseStep 2147395 = 3221093) B3221093
theorem B3673181 : Blo 2145435 3673181 := bbase (se 3 (by rfl) ⟨688721, by rfl⟩ : syracuseStep 3673181 = 1377443) (by norm_num)
theorem B2448787 : Blo 2145435 2448787 := bstep (se 1 (by rfl) ⟨1836590, by rfl⟩ : syracuseStep 2448787 = 3673181) B3673181
theorem B3265049 : Blo 2145435 3265049 := bstep (se 2 (by rfl) ⟨1224393, by rfl⟩ : syracuseStep 3265049 = 2448787) B2448787
theorem B8706797 : Blo 2145435 8706797 := bstep (se 3 (by rfl) ⟨1632524, by rfl⟩ : syracuseStep 8706797 = 3265049) B3265049
theorem B5804531 : Blo 2145435 5804531 := bstep (se 1 (by rfl) ⟨4353398, by rfl⟩ : syracuseStep 5804531 = 8706797) B8706797
theorem B3869687 : Blo 2145435 3869687 := bstep (se 1 (by rfl) ⟨2902265, by rfl⟩ : syracuseStep 3869687 = 5804531) B5804531
theorem B2579791 : Blo 2145435 2579791 := bstep (se 1 (by rfl) ⟨1934843, by rfl⟩ : syracuseStep 2579791 = 3869687) B3869687
theorem B3439721 : Blo 2145435 3439721 := bstep (se 2 (by rfl) ⟨1289895, by rfl⟩ : syracuseStep 3439721 = 2579791) B2579791
theorem B2293147 : Blo 2145435 2293147 := bstep (se 1 (by rfl) ⟨1719860, by rfl⟩ : syracuseStep 2293147 = 3439721) B3439721
theorem B3057529 : Blo 2145435 3057529 := bstep (se 2 (by rfl) ⟨1146573, by rfl⟩ : syracuseStep 3057529 = 2293147) B2293147
theorem B4076705 : Blo 2145435 4076705 := bstep (se 2 (by rfl) ⟨1528764, by rfl⟩ : syracuseStep 4076705 = 3057529) B3057529
theorem B2717803 : Blo 2145435 2717803 := bstep (se 1 (by rfl) ⟨2038352, by rfl⟩ : syracuseStep 2717803 = 4076705) B4076705
theorem B3623737 : Blo 2145435 3623737 := bstep (se 2 (by rfl) ⟨1358901, by rfl⟩ : syracuseStep 3623737 = 2717803) B2717803
theorem B4831649 : Blo 2145435 4831649 := bstep (se 2 (by rfl) ⟨1811868, by rfl⟩ : syracuseStep 4831649 = 3623737) B3623737
theorem B3221099 : Blo 2145435 3221099 := bstep (se 1 (by rfl) ⟨2415824, by rfl⟩ : syracuseStep 3221099 = 4831649) B4831649
theorem B2147399 : Blo 2145435 2147399 := bstep (se 1 (by rfl) ⟨1610549, by rfl⟩ : syracuseStep 2147399 = 3221099) B3221099
theorem B2415829 : Blo 2145435 2415829 := bbase (se 7 (by rfl) ⟨28310, by rfl⟩ : syracuseStep 2415829 = 56621) (by norm_num)
theorem B3221105 : Blo 2145435 3221105 := bstep (se 2 (by rfl) ⟨1207914, by rfl⟩ : syracuseStep 3221105 = 2415829) B2415829
theorem B2147403 : Blo 2145435 2147403 := bstep (se 1 (by rfl) ⟨1610552, by rfl⟩ : syracuseStep 2147403 = 3221105) B3221105
theorem B2717813 : Blo 2145435 2717813 := bbase (se 5 (by rfl) ⟨127397, by rfl⟩ : syracuseStep 2717813 = 254795) (by norm_num)
theorem B7247501 : Blo 2145435 7247501 := bstep (se 3 (by rfl) ⟨1358906, by rfl⟩ : syracuseStep 7247501 = 2717813) B2717813
theorem B4831667 : Blo 2145435 4831667 := bstep (se 1 (by rfl) ⟨3623750, by rfl⟩ : syracuseStep 4831667 = 7247501) B7247501
theorem B3221111 : Blo 2145435 3221111 := bstep (se 1 (by rfl) ⟨2415833, by rfl⟩ : syracuseStep 3221111 = 4831667) B4831667
theorem B2147407 : Blo 2145435 2147407 := bstep (se 1 (by rfl) ⟨1610555, by rfl⟩ : syracuseStep 2147407 = 3221111) B3221111
theorem B3221117 : Blo 2145435 3221117 := bbase (se 3 (by rfl) ⟨603959, by rfl⟩ : syracuseStep 3221117 = 1207919) (by norm_num)
theorem B2147411 : Blo 2145435 2147411 := bstep (se 1 (by rfl) ⟨1610558, by rfl⟩ : syracuseStep 2147411 = 3221117) B3221117
theorem B4831685 : Blo 2145435 4831685 := bbase (se 4 (by rfl) ⟨452970, by rfl⟩ : syracuseStep 4831685 = 905941) (by norm_num)
theorem B3221123 : Blo 2145435 3221123 := bstep (se 1 (by rfl) ⟨2415842, by rfl⟩ : syracuseStep 3221123 = 4831685) B4831685
theorem B2147415 : Blo 2145435 2147415 := bstep (se 1 (by rfl) ⟨1610561, by rfl⟩ : syracuseStep 2147415 = 3221123) B3221123
theorem B5159629 : Blo 2145435 5159629 := bbase (se 3 (by rfl) ⟨967430, by rfl⟩ : syracuseStep 5159629 = 1934861) (by norm_num)
theorem B6879505 : Blo 2145435 6879505 := bstep (se 2 (by rfl) ⟨2579814, by rfl⟩ : syracuseStep 6879505 = 5159629) B5159629
theorem B9172673 : Blo 2145435 9172673 := bstep (se 2 (by rfl) ⟨3439752, by rfl⟩ : syracuseStep 9172673 = 6879505) B6879505
theorem B6115115 : Blo 2145435 6115115 := bstep (se 1 (by rfl) ⟨4586336, by rfl⟩ : syracuseStep 6115115 = 9172673) B9172673
theorem B4076743 : Blo 2145435 4076743 := bstep (se 1 (by rfl) ⟨3057557, by rfl⟩ : syracuseStep 4076743 = 6115115) B6115115
theorem B5435657 : Blo 2145435 5435657 := bstep (se 2 (by rfl) ⟨2038371, by rfl⟩ : syracuseStep 5435657 = 4076743) B4076743
theorem B3623771 : Blo 2145435 3623771 := bstep (se 1 (by rfl) ⟨2717828, by rfl⟩ : syracuseStep 3623771 = 5435657) B5435657
theorem B2415847 : Blo 2145435 2415847 := bstep (se 1 (by rfl) ⟨1811885, by rfl⟩ : syracuseStep 2415847 = 3623771) B3623771
theorem B3221129 : Blo 2145435 3221129 := bstep (se 2 (by rfl) ⟨1207923, by rfl⟩ : syracuseStep 3221129 = 2415847) B2415847
theorem B2147419 : Blo 2145435 2147419 := bstep (se 1 (by rfl) ⟨1610564, by rfl⟩ : syracuseStep 2147419 = 3221129) B3221129
theorem B10871333 : Blo 2145435 10871333 := bbase (se 4 (by rfl) ⟨1019187, by rfl⟩ : syracuseStep 10871333 = 2038375) (by norm_num)
theorem B7247555 : Blo 2145435 7247555 := bstep (se 1 (by rfl) ⟨5435666, by rfl⟩ : syracuseStep 7247555 = 10871333) B10871333
theorem B4831703 : Blo 2145435 4831703 := bstep (se 1 (by rfl) ⟨3623777, by rfl⟩ : syracuseStep 4831703 = 7247555) B7247555
theorem B3221135 : Blo 2145435 3221135 := bstep (se 1 (by rfl) ⟨2415851, by rfl⟩ : syracuseStep 3221135 = 4831703) B4831703
theorem B2147423 : Blo 2145435 2147423 := bstep (se 1 (by rfl) ⟨1610567, by rfl⟩ : syracuseStep 2147423 = 3221135) B3221135
theorem B3221141 : Blo 2145435 3221141 := bbase (se 6 (by rfl) ⟨75495, by rfl⟩ : syracuseStep 3221141 = 150991) (by norm_num)
theorem B2147427 : Blo 2145435 2147427 := bstep (se 1 (by rfl) ⟨1610570, by rfl⟩ : syracuseStep 2147427 = 3221141) B3221141
theorem B11019701 : Blo 2145435 11019701 := bbase (se 5 (by rfl) ⟨516548, by rfl⟩ : syracuseStep 11019701 = 1033097) (by norm_num)
theorem B7346467 : Blo 2145435 7346467 := bstep (se 1 (by rfl) ⟨5509850, by rfl⟩ : syracuseStep 7346467 = 11019701) B11019701
theorem B9795289 : Blo 2145435 9795289 := bstep (se 2 (by rfl) ⟨3673233, by rfl⟩ : syracuseStep 9795289 = 7346467) B7346467
theorem B13060385 : Blo 2145435 13060385 := bstep (se 2 (by rfl) ⟨4897644, by rfl⟩ : syracuseStep 13060385 = 9795289) B9795289
theorem B8706923 : Blo 2145435 8706923 := bstep (se 1 (by rfl) ⟨6530192, by rfl⟩ : syracuseStep 8706923 = 13060385) B13060385
theorem B5804615 : Blo 2145435 5804615 := bstep (se 1 (by rfl) ⟨4353461, by rfl⟩ : syracuseStep 5804615 = 8706923) B8706923
theorem B3869743 : Blo 2145435 3869743 := bstep (se 1 (by rfl) ⟨2902307, by rfl⟩ : syracuseStep 3869743 = 5804615) B5804615
theorem B5159657 : Blo 2145435 5159657 := bstep (se 2 (by rfl) ⟨1934871, by rfl⟩ : syracuseStep 5159657 = 3869743) B3869743
theorem B13759085 : Blo 2145435 13759085 := bstep (se 3 (by rfl) ⟨2579828, by rfl⟩ : syracuseStep 13759085 = 5159657) B5159657
theorem B9172723 : Blo 2145435 9172723 := bstep (se 1 (by rfl) ⟨6879542, by rfl⟩ : syracuseStep 9172723 = 13759085) B13759085
theorem B12230297 : Blo 2145435 12230297 := bstep (se 2 (by rfl) ⟨4586361, by rfl⟩ : syracuseStep 12230297 = 9172723) B9172723
theorem B8153531 : Blo 2145435 8153531 := bstep (se 1 (by rfl) ⟨6115148, by rfl⟩ : syracuseStep 8153531 = 12230297) B12230297
theorem B5435687 : Blo 2145435 5435687 := bstep (se 1 (by rfl) ⟨4076765, by rfl⟩ : syracuseStep 5435687 = 8153531) B8153531
theorem B3623791 : Blo 2145435 3623791 := bstep (se 1 (by rfl) ⟨2717843, by rfl⟩ : syracuseStep 3623791 = 5435687) B5435687
theorem B4831721 : Blo 2145435 4831721 := bstep (se 2 (by rfl) ⟨1811895, by rfl⟩ : syracuseStep 4831721 = 3623791) B3623791
theorem B3221147 : Blo 2145435 3221147 := bstep (se 1 (by rfl) ⟨2415860, by rfl⟩ : syracuseStep 3221147 = 4831721) B4831721
theorem B2147431 : Blo 2145435 2147431 := bstep (se 1 (by rfl) ⟨1610573, by rfl⟩ : syracuseStep 2147431 = 3221147) B3221147
theorem B2415865 : Blo 2145435 2415865 := bbase (se 2 (by rfl) ⟨905949, by rfl⟩ : syracuseStep 2415865 = 1811899) (by norm_num)
theorem B3221153 : Blo 2145435 3221153 := bstep (se 2 (by rfl) ⟨1207932, by rfl⟩ : syracuseStep 3221153 = 2415865) B2415865
theorem B2147435 : Blo 2145435 2147435 := bstep (se 1 (by rfl) ⟨1610576, by rfl⟩ : syracuseStep 2147435 = 3221153) B3221153
theorem C0 (j : ℕ) (h1 : 536358 ≤ j) (h2 : j ≤ 536858) : Blo 2145435 (4 * j + 3) := by
  interval_cases j
  · exact B2145435
  · exact B2145439
  · exact B2145443
  · exact B2145447
  · exact B2145451
  · exact B2145455
  · exact B2145459
  · exact B2145463
  · exact B2145467
  · exact B2145471
  · exact B2145475
  · exact B2145479
  · exact B2145483
  · exact B2145487
  · exact B2145491
  · exact B2145495
  · exact B2145499
  · exact B2145503
  · exact B2145507
  · exact B2145511
  · exact B2145515
  · exact B2145519
  · exact B2145523
  · exact B2145527
  · exact B2145531
  · exact B2145535
  · exact B2145539
  · exact B2145543
  · exact B2145547
  · exact B2145551
  · exact B2145555
  · exact B2145559
  · exact B2145563
  · exact B2145567
  · exact B2145571
  · exact B2145575
  · exact B2145579
  · exact B2145583
  · exact B2145587
  · exact B2145591
  · exact B2145595
  · exact B2145599
  · exact B2145603
  · exact B2145607
  · exact B2145611
  · exact B2145615
  · exact B2145619
  · exact B2145623
  · exact B2145627
  · exact B2145631
  · exact B2145635
  · exact B2145639
  · exact B2145643
  · exact B2145647
  · exact B2145651
  · exact B2145655
  · exact B2145659
  · exact B2145663
  · exact B2145667
  · exact B2145671
  · exact B2145675
  · exact B2145679
  · exact B2145683
  · exact B2145687
  · exact B2145691
  · exact B2145695
  · exact B2145699
  · exact B2145703
  · exact B2145707
  · exact B2145711
  · exact B2145715
  · exact B2145719
  · exact B2145723
  · exact B2145727
  · exact B2145731
  · exact B2145735
  · exact B2145739
  · exact B2145743
  · exact B2145747
  · exact B2145751
  · exact B2145755
  · exact B2145759
  · exact B2145763
  · exact B2145767
  · exact B2145771
  · exact B2145775
  · exact B2145779
  · exact B2145783
  · exact B2145787
  · exact B2145791
  · exact B2145795
  · exact B2145799
  · exact B2145803
  · exact B2145807
  · exact B2145811
  · exact B2145815
  · exact B2145819
  · exact B2145823
  · exact B2145827
  · exact B2145831
  · exact B2145835
  · exact B2145839
  · exact B2145843
  · exact B2145847
  · exact B2145851
  · exact B2145855
  · exact B2145859
  · exact B2145863
  · exact B2145867
  · exact B2145871
  · exact B2145875
  · exact B2145879
  · exact B2145883
  · exact B2145887
  · exact B2145891
  · exact B2145895
  · exact B2145899
  · exact B2145903
  · exact B2145907
  · exact B2145911
  · exact B2145915
  · exact B2145919
  · exact B2145923
  · exact B2145927
  · exact B2145931
  · exact B2145935
  · exact B2145939
  · exact B2145943
  · exact B2145947
  · exact B2145951
  · exact B2145955
  · exact B2145959
  · exact B2145963
  · exact B2145967
  · exact B2145971
  · exact B2145975
  · exact B2145979
  · exact B2145983
  · exact B2145987
  · exact B2145991
  · exact B2145995
  · exact B2145999
  · exact B2146003
  · exact B2146007
  · exact B2146011
  · exact B2146015
  · exact B2146019
  · exact B2146023
  · exact B2146027
  · exact B2146031
  · exact B2146035
  · exact B2146039
  · exact B2146043
  · exact B2146047
  · exact B2146051
  · exact B2146055
  · exact B2146059
  · exact B2146063
  · exact B2146067
  · exact B2146071
  · exact B2146075
  · exact B2146079
  · exact B2146083
  · exact B2146087
  · exact B2146091
  · exact B2146095
  · exact B2146099
  · exact B2146103
  · exact B2146107
  · exact B2146111
  · exact B2146115
  · exact B2146119
  · exact B2146123
  · exact B2146127
  · exact B2146131
  · exact B2146135
  · exact B2146139
  · exact B2146143
  · exact B2146147
  · exact B2146151
  · exact B2146155
  · exact B2146159
  · exact B2146163
  · exact B2146167
  · exact B2146171
  · exact B2146175
  · exact B2146179
  · exact B2146183
  · exact B2146187
  · exact B2146191
  · exact B2146195
  · exact B2146199
  · exact B2146203
  · exact B2146207
  · exact B2146211
  · exact B2146215
  · exact B2146219
  · exact B2146223
  · exact B2146227
  · exact B2146231
  · exact B2146235
  · exact B2146239
  · exact B2146243
  · exact B2146247
  · exact B2146251
  · exact B2146255
  · exact B2146259
  · exact B2146263
  · exact B2146267
  · exact B2146271
  · exact B2146275
  · exact B2146279
  · exact B2146283
  · exact B2146287
  · exact B2146291
  · exact B2146295
  · exact B2146299
  · exact B2146303
  · exact B2146307
  · exact B2146311
  · exact B2146315
  · exact B2146319
  · exact B2146323
  · exact B2146327
  · exact B2146331
  · exact B2146335
  · exact B2146339
  · exact B2146343
  · exact B2146347
  · exact B2146351
  · exact B2146355
  · exact B2146359
  · exact B2146363
  · exact B2146367
  · exact B2146371
  · exact B2146375
  · exact B2146379
  · exact B2146383
  · exact B2146387
  · exact B2146391
  · exact B2146395
  · exact B2146399
  · exact B2146403
  · exact B2146407
  · exact B2146411
  · exact B2146415
  · exact B2146419
  · exact B2146423
  · exact B2146427
  · exact B2146431
  · exact B2146435
  · exact B2146439
  · exact B2146443
  · exact B2146447
  · exact B2146451
  · exact B2146455
  · exact B2146459
  · exact B2146463
  · exact B2146467
  · exact B2146471
  · exact B2146475
  · exact B2146479
  · exact B2146483
  · exact B2146487
  · exact B2146491
  · exact B2146495
  · exact B2146499
  · exact B2146503
  · exact B2146507
  · exact B2146511
  · exact B2146515
  · exact B2146519
  · exact B2146523
  · exact B2146527
  · exact B2146531
  · exact B2146535
  · exact B2146539
  · exact B2146543
  · exact B2146547
  · exact B2146551
  · exact B2146555
  · exact B2146559
  · exact B2146563
  · exact B2146567
  · exact B2146571
  · exact B2146575
  · exact B2146579
  · exact B2146583
  · exact B2146587
  · exact B2146591
  · exact B2146595
  · exact B2146599
  · exact B2146603
  · exact B2146607
  · exact B2146611
  · exact B2146615
  · exact B2146619
  · exact B2146623
  · exact B2146627
  · exact B2146631
  · exact B2146635
  · exact B2146639
  · exact B2146643
  · exact B2146647
  · exact B2146651
  · exact B2146655
  · exact B2146659
  · exact B2146663
  · exact B2146667
  · exact B2146671
  · exact B2146675
  · exact B2146679
  · exact B2146683
  · exact B2146687
  · exact B2146691
  · exact B2146695
  · exact B2146699
  · exact B2146703
  · exact B2146707
  · exact B2146711
  · exact B2146715
  · exact B2146719
  · exact B2146723
  · exact B2146727
  · exact B2146731
  · exact B2146735
  · exact B2146739
  · exact B2146743
  · exact B2146747
  · exact B2146751
  · exact B2146755
  · exact B2146759
  · exact B2146763
  · exact B2146767
  · exact B2146771
  · exact B2146775
  · exact B2146779
  · exact B2146783
  · exact B2146787
  · exact B2146791
  · exact B2146795
  · exact B2146799
  · exact B2146803
  · exact B2146807
  · exact B2146811
  · exact B2146815
  · exact B2146819
  · exact B2146823
  · exact B2146827
  · exact B2146831
  · exact B2146835
  · exact B2146839
  · exact B2146843
  · exact B2146847
  · exact B2146851
  · exact B2146855
  · exact B2146859
  · exact B2146863
  · exact B2146867
  · exact B2146871
  · exact B2146875
  · exact B2146879
  · exact B2146883
  · exact B2146887
  · exact B2146891
  · exact B2146895
  · exact B2146899
  · exact B2146903
  · exact B2146907
  · exact B2146911
  · exact B2146915
  · exact B2146919
  · exact B2146923
  · exact B2146927
  · exact B2146931
  · exact B2146935
  · exact B2146939
  · exact B2146943
  · exact B2146947
  · exact B2146951
  · exact B2146955
  · exact B2146959
  · exact B2146963
  · exact B2146967
  · exact B2146971
  · exact B2146975
  · exact B2146979
  · exact B2146983
  · exact B2146987
  · exact B2146991
  · exact B2146995
  · exact B2146999
  · exact B2147003
  · exact B2147007
  · exact B2147011
  · exact B2147015
  · exact B2147019
  · exact B2147023
  · exact B2147027
  · exact B2147031
  · exact B2147035
  · exact B2147039
  · exact B2147043
  · exact B2147047
  · exact B2147051
  · exact B2147055
  · exact B2147059
  · exact B2147063
  · exact B2147067
  · exact B2147071
  · exact B2147075
  · exact B2147079
  · exact B2147083
  · exact B2147087
  · exact B2147091
  · exact B2147095
  · exact B2147099
  · exact B2147103
  · exact B2147107
  · exact B2147111
  · exact B2147115
  · exact B2147119
  · exact B2147123
  · exact B2147127
  · exact B2147131
  · exact B2147135
  · exact B2147139
  · exact B2147143
  · exact B2147147
  · exact B2147151
  · exact B2147155
  · exact B2147159
  · exact B2147163
  · exact B2147167
  · exact B2147171
  · exact B2147175
  · exact B2147179
  · exact B2147183
  · exact B2147187
  · exact B2147191
  · exact B2147195
  · exact B2147199
  · exact B2147203
  · exact B2147207
  · exact B2147211
  · exact B2147215
  · exact B2147219
  · exact B2147223
  · exact B2147227
  · exact B2147231
  · exact B2147235
  · exact B2147239
  · exact B2147243
  · exact B2147247
  · exact B2147251
  · exact B2147255
  · exact B2147259
  · exact B2147263
  · exact B2147267
  · exact B2147271
  · exact B2147275
  · exact B2147279
  · exact B2147283
  · exact B2147287
  · exact B2147291
  · exact B2147295
  · exact B2147299
  · exact B2147303
  · exact B2147307
  · exact B2147311
  · exact B2147315
  · exact B2147319
  · exact B2147323
  · exact B2147327
  · exact B2147331
  · exact B2147335
  · exact B2147339
  · exact B2147343
  · exact B2147347
  · exact B2147351
  · exact B2147355
  · exact B2147359
  · exact B2147363
  · exact B2147367
  · exact B2147371
  · exact B2147375
  · exact B2147379
  · exact B2147383
  · exact B2147387
  · exact B2147391
  · exact B2147395
  · exact B2147399
  · exact B2147403
  · exact B2147407
  · exact B2147411
  · exact B2147415
  · exact B2147419
  · exact B2147423
  · exact B2147427
  · exact B2147431
  · exact B2147435
theorem solution (m : ℕ) (hlo : 2145435 ≤ m) (hhi : m ≤ 2147435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 536358 ≤ j := by omega
    have hj2 : j ≤ 536858 := by omega
    have hb : Blo 2145435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
