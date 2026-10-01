-- Prove2me | solution 1 for syracuse_descends_range_2177435_2179435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:53.770447+00:00
-- url     : https://prove2.me/submissions/602dcabe-59e7-4bdd-805f-94974f38f601

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

theorem B5231749 : Blo 2177435 5231749 := bbase (se 4 (by rfl) ⟨490476, by rfl⟩ : syracuseStep 5231749 = 980953) (by norm_num)
theorem B6975665 : Blo 2177435 6975665 := bstep (se 2 (by rfl) ⟨2615874, by rfl⟩ : syracuseStep 6975665 = 5231749) B5231749
theorem B4650443 : Blo 2177435 4650443 := bstep (se 1 (by rfl) ⟨3487832, by rfl⟩ : syracuseStep 4650443 = 6975665) B6975665
theorem B3100295 : Blo 2177435 3100295 := bstep (se 1 (by rfl) ⟨2325221, by rfl⟩ : syracuseStep 3100295 = 4650443) B4650443
theorem B8267453 : Blo 2177435 8267453 := bstep (se 3 (by rfl) ⟨1550147, by rfl⟩ : syracuseStep 8267453 = 3100295) B3100295
theorem B5511635 : Blo 2177435 5511635 := bstep (se 1 (by rfl) ⟨4133726, by rfl⟩ : syracuseStep 5511635 = 8267453) B8267453
theorem B3674423 : Blo 2177435 3674423 := bstep (se 1 (by rfl) ⟨2755817, by rfl⟩ : syracuseStep 3674423 = 5511635) B5511635
theorem B2449615 : Blo 2177435 2449615 := bstep (se 1 (by rfl) ⟨1837211, by rfl⟩ : syracuseStep 2449615 = 3674423) B3674423
theorem B3266153 : Blo 2177435 3266153 := bstep (se 2 (by rfl) ⟨1224807, by rfl⟩ : syracuseStep 3266153 = 2449615) B2449615
theorem B2177435 : Blo 2177435 2177435 := bstep (se 1 (by rfl) ⟨1633076, by rfl⟩ : syracuseStep 2177435 = 3266153) B3266153
theorem B9300901 : Blo 2177435 9300901 := bbase (se 4 (by rfl) ⟨871959, by rfl⟩ : syracuseStep 9300901 = 1743919) (by norm_num)
theorem B12401201 : Blo 2177435 12401201 := bstep (se 2 (by rfl) ⟨4650450, by rfl⟩ : syracuseStep 12401201 = 9300901) B9300901
theorem B8267467 : Blo 2177435 8267467 := bstep (se 1 (by rfl) ⟨6200600, by rfl⟩ : syracuseStep 8267467 = 12401201) B12401201
theorem B11023289 : Blo 2177435 11023289 := bstep (se 2 (by rfl) ⟨4133733, by rfl⟩ : syracuseStep 11023289 = 8267467) B8267467
theorem B7348859 : Blo 2177435 7348859 := bstep (se 1 (by rfl) ⟨5511644, by rfl⟩ : syracuseStep 7348859 = 11023289) B11023289
theorem B4899239 : Blo 2177435 4899239 := bstep (se 1 (by rfl) ⟨3674429, by rfl⟩ : syracuseStep 4899239 = 7348859) B7348859
theorem B3266159 : Blo 2177435 3266159 := bstep (se 1 (by rfl) ⟨2449619, by rfl⟩ : syracuseStep 3266159 = 4899239) B4899239
theorem B2177439 : Blo 2177435 2177439 := bstep (se 1 (by rfl) ⟨1633079, by rfl⟩ : syracuseStep 2177439 = 3266159) B3266159
theorem B3266165 : Blo 2177435 3266165 := bbase (se 5 (by rfl) ⟨153101, by rfl⟩ : syracuseStep 3266165 = 306203) (by norm_num)
theorem B2177443 : Blo 2177435 2177443 := bstep (se 1 (by rfl) ⟨1633082, by rfl⟩ : syracuseStep 2177443 = 3266165) B3266165
theorem B4133749 : Blo 2177435 4133749 := bbase (se 5 (by rfl) ⟨193769, by rfl⟩ : syracuseStep 4133749 = 387539) (by norm_num)
theorem B5511665 : Blo 2177435 5511665 := bstep (se 2 (by rfl) ⟨2066874, by rfl⟩ : syracuseStep 5511665 = 4133749) B4133749
theorem B3674443 : Blo 2177435 3674443 := bstep (se 1 (by rfl) ⟨2755832, by rfl⟩ : syracuseStep 3674443 = 5511665) B5511665
theorem B4899257 : Blo 2177435 4899257 := bstep (se 2 (by rfl) ⟨1837221, by rfl⟩ : syracuseStep 4899257 = 3674443) B3674443
theorem B3266171 : Blo 2177435 3266171 := bstep (se 1 (by rfl) ⟨2449628, by rfl⟩ : syracuseStep 3266171 = 4899257) B4899257
theorem B2177447 : Blo 2177435 2177447 := bstep (se 1 (by rfl) ⟨1633085, by rfl⟩ : syracuseStep 2177447 = 3266171) B3266171
theorem B2449633 : Blo 2177435 2449633 := bbase (se 2 (by rfl) ⟨918612, by rfl⟩ : syracuseStep 2449633 = 1837225) (by norm_num)
theorem B3266177 : Blo 2177435 3266177 := bstep (se 2 (by rfl) ⟨1224816, by rfl⟩ : syracuseStep 3266177 = 2449633) B2449633
theorem B2177451 : Blo 2177435 2177451 := bstep (se 1 (by rfl) ⟨1633088, by rfl⟩ : syracuseStep 2177451 = 3266177) B3266177
theorem B5511685 : Blo 2177435 5511685 := bbase (se 4 (by rfl) ⟨516720, by rfl⟩ : syracuseStep 5511685 = 1033441) (by norm_num)
theorem B7348913 : Blo 2177435 7348913 := bstep (se 2 (by rfl) ⟨2755842, by rfl⟩ : syracuseStep 7348913 = 5511685) B5511685
theorem B4899275 : Blo 2177435 4899275 := bstep (se 1 (by rfl) ⟨3674456, by rfl⟩ : syracuseStep 4899275 = 7348913) B7348913
theorem B3266183 : Blo 2177435 3266183 := bstep (se 1 (by rfl) ⟨2449637, by rfl⟩ : syracuseStep 3266183 = 4899275) B4899275
theorem B2177455 : Blo 2177435 2177455 := bstep (se 1 (by rfl) ⟨1633091, by rfl⟩ : syracuseStep 2177455 = 3266183) B3266183
theorem B3266189 : Blo 2177435 3266189 := bbase (se 3 (by rfl) ⟨612410, by rfl⟩ : syracuseStep 3266189 = 1224821) (by norm_num)
theorem B2177459 : Blo 2177435 2177459 := bstep (se 1 (by rfl) ⟨1633094, by rfl⟩ : syracuseStep 2177459 = 3266189) B3266189
theorem B4899293 : Blo 2177435 4899293 := bbase (se 3 (by rfl) ⟨918617, by rfl⟩ : syracuseStep 4899293 = 1837235) (by norm_num)
theorem B3266195 : Blo 2177435 3266195 := bstep (se 1 (by rfl) ⟨2449646, by rfl⟩ : syracuseStep 3266195 = 4899293) B4899293
theorem B2177463 : Blo 2177435 2177463 := bstep (se 1 (by rfl) ⟨1633097, by rfl⟩ : syracuseStep 2177463 = 3266195) B3266195
theorem B3674477 : Blo 2177435 3674477 := bbase (se 3 (by rfl) ⟨688964, by rfl⟩ : syracuseStep 3674477 = 1377929) (by norm_num)
theorem B2449651 : Blo 2177435 2449651 := bstep (se 1 (by rfl) ⟨1837238, by rfl⟩ : syracuseStep 2449651 = 3674477) B3674477
theorem B3266201 : Blo 2177435 3266201 := bstep (se 2 (by rfl) ⟨1224825, by rfl⟩ : syracuseStep 3266201 = 2449651) B2449651
theorem B2177467 : Blo 2177435 2177467 := bstep (se 1 (by rfl) ⟨1633100, by rfl⟩ : syracuseStep 2177467 = 3266201) B3266201
theorem B2389141 : Blo 2177435 2389141 := bbase (se 6 (by rfl) ⟨55995, by rfl⟩ : syracuseStep 2389141 = 111991) (by norm_num)
theorem B12742085 : Blo 2177435 12742085 := bstep (se 4 (by rfl) ⟨1194570, by rfl⟩ : syracuseStep 12742085 = 2389141) B2389141
theorem B8494723 : Blo 2177435 8494723 := bstep (se 1 (by rfl) ⟨6371042, by rfl⟩ : syracuseStep 8494723 = 12742085) B12742085
theorem B45305189 : Blo 2177435 45305189 := bstep (se 4 (by rfl) ⟨4247361, by rfl⟩ : syracuseStep 45305189 = 8494723) B8494723
theorem B30203459 : Blo 2177435 30203459 := bstep (se 1 (by rfl) ⟨22652594, by rfl⟩ : syracuseStep 30203459 = 45305189) B45305189
theorem B20135639 : Blo 2177435 20135639 := bstep (se 1 (by rfl) ⟨15101729, by rfl⟩ : syracuseStep 20135639 = 30203459) B30203459
theorem B53695037 : Blo 2177435 53695037 := bstep (se 3 (by rfl) ⟨10067819, by rfl⟩ : syracuseStep 53695037 = 20135639) B20135639
theorem B35796691 : Blo 2177435 35796691 := bstep (se 1 (by rfl) ⟨26847518, by rfl⟩ : syracuseStep 35796691 = 53695037) B53695037
theorem B47728921 : Blo 2177435 47728921 := bstep (se 2 (by rfl) ⟨17898345, by rfl⟩ : syracuseStep 47728921 = 35796691) B35796691
theorem B63638561 : Blo 2177435 63638561 := bstep (se 2 (by rfl) ⟨23864460, by rfl⟩ : syracuseStep 63638561 = 47728921) B47728921
theorem B169702829 : Blo 2177435 169702829 := bstep (se 3 (by rfl) ⟨31819280, by rfl⟩ : syracuseStep 169702829 = 63638561) B63638561
theorem B113135219 : Blo 2177435 113135219 := bstep (se 1 (by rfl) ⟨84851414, by rfl⟩ : syracuseStep 113135219 = 169702829) B169702829
theorem B75423479 : Blo 2177435 75423479 := bstep (se 1 (by rfl) ⟨56567609, by rfl⟩ : syracuseStep 75423479 = 113135219) B113135219
theorem B201129277 : Blo 2177435 201129277 := bstep (se 3 (by rfl) ⟨37711739, by rfl⟩ : syracuseStep 201129277 = 75423479) B75423479
theorem B268172369 : Blo 2177435 268172369 := bstep (se 2 (by rfl) ⟨100564638, by rfl⟩ : syracuseStep 268172369 = 201129277) B201129277
theorem B178781579 : Blo 2177435 178781579 := bstep (se 1 (by rfl) ⟨134086184, by rfl⟩ : syracuseStep 178781579 = 268172369) B268172369
theorem B119187719 : Blo 2177435 119187719 := bstep (se 1 (by rfl) ⟨89390789, by rfl⟩ : syracuseStep 119187719 = 178781579) B178781579
theorem B79458479 : Blo 2177435 79458479 := bstep (se 1 (by rfl) ⟨59593859, by rfl⟩ : syracuseStep 79458479 = 119187719) B119187719
theorem B52972319 : Blo 2177435 52972319 := bstep (se 1 (by rfl) ⟨39729239, by rfl⟩ : syracuseStep 52972319 = 79458479) B79458479
theorem B35314879 : Blo 2177435 35314879 := bstep (se 1 (by rfl) ⟨26486159, by rfl⟩ : syracuseStep 35314879 = 52972319) B52972319
theorem B47086505 : Blo 2177435 47086505 := bstep (se 2 (by rfl) ⟨17657439, by rfl⟩ : syracuseStep 47086505 = 35314879) B35314879
theorem B31391003 : Blo 2177435 31391003 := bstep (se 1 (by rfl) ⟨23543252, by rfl⟩ : syracuseStep 31391003 = 47086505) B47086505
theorem B20927335 : Blo 2177435 20927335 := bstep (se 1 (by rfl) ⟨15695501, by rfl⟩ : syracuseStep 20927335 = 31391003) B31391003
theorem B27903113 : Blo 2177435 27903113 := bstep (se 2 (by rfl) ⟨10463667, by rfl⟩ : syracuseStep 27903113 = 20927335) B20927335
theorem B18602075 : Blo 2177435 18602075 := bstep (se 1 (by rfl) ⟨13951556, by rfl⟩ : syracuseStep 18602075 = 27903113) B27903113
theorem B12401383 : Blo 2177435 12401383 := bstep (se 1 (by rfl) ⟨9301037, by rfl⟩ : syracuseStep 12401383 = 18602075) B18602075
theorem B16535177 : Blo 2177435 16535177 := bstep (se 2 (by rfl) ⟨6200691, by rfl⟩ : syracuseStep 16535177 = 12401383) B12401383
theorem B11023451 : Blo 2177435 11023451 := bstep (se 1 (by rfl) ⟨8267588, by rfl⟩ : syracuseStep 11023451 = 16535177) B16535177
theorem B7348967 : Blo 2177435 7348967 := bstep (se 1 (by rfl) ⟨5511725, by rfl⟩ : syracuseStep 7348967 = 11023451) B11023451
theorem B4899311 : Blo 2177435 4899311 := bstep (se 1 (by rfl) ⟨3674483, by rfl⟩ : syracuseStep 4899311 = 7348967) B7348967
theorem B3266207 : Blo 2177435 3266207 := bstep (se 1 (by rfl) ⟨2449655, by rfl⟩ : syracuseStep 3266207 = 4899311) B4899311
theorem B2177471 : Blo 2177435 2177471 := bstep (se 1 (by rfl) ⟨1633103, by rfl⟩ : syracuseStep 2177471 = 3266207) B3266207
theorem B3266213 : Blo 2177435 3266213 := bbase (se 4 (by rfl) ⟨306207, by rfl⟩ : syracuseStep 3266213 = 612415) (by norm_num)
theorem B2177475 : Blo 2177435 2177475 := bstep (se 1 (by rfl) ⟨1633106, by rfl⟩ : syracuseStep 2177475 = 3266213) B3266213
theorem B2755873 : Blo 2177435 2755873 := bbase (se 2 (by rfl) ⟨1033452, by rfl⟩ : syracuseStep 2755873 = 2066905) (by norm_num)
theorem B3674497 : Blo 2177435 3674497 := bstep (se 2 (by rfl) ⟨1377936, by rfl⟩ : syracuseStep 3674497 = 2755873) B2755873
theorem B4899329 : Blo 2177435 4899329 := bstep (se 2 (by rfl) ⟨1837248, by rfl⟩ : syracuseStep 4899329 = 3674497) B3674497
theorem B3266219 : Blo 2177435 3266219 := bstep (se 1 (by rfl) ⟨2449664, by rfl⟩ : syracuseStep 3266219 = 4899329) B4899329
theorem B2177479 : Blo 2177435 2177479 := bstep (se 1 (by rfl) ⟨1633109, by rfl⟩ : syracuseStep 2177479 = 3266219) B3266219
theorem B2449669 : Blo 2177435 2449669 := bbase (se 4 (by rfl) ⟨229656, by rfl⟩ : syracuseStep 2449669 = 459313) (by norm_num)
theorem B3266225 : Blo 2177435 3266225 := bstep (se 2 (by rfl) ⟨1224834, by rfl⟩ : syracuseStep 3266225 = 2449669) B2449669
theorem B2177483 : Blo 2177435 2177483 := bstep (se 1 (by rfl) ⟨1633112, by rfl⟩ : syracuseStep 2177483 = 3266225) B3266225
theorem B2325277 : Blo 2177435 2325277 := bbase (se 3 (by rfl) ⟨435989, by rfl⟩ : syracuseStep 2325277 = 871979) (by norm_num)
theorem B3100369 : Blo 2177435 3100369 := bstep (se 2 (by rfl) ⟨1162638, by rfl⟩ : syracuseStep 3100369 = 2325277) B2325277
theorem B4133825 : Blo 2177435 4133825 := bstep (se 2 (by rfl) ⟨1550184, by rfl⟩ : syracuseStep 4133825 = 3100369) B3100369
theorem B2755883 : Blo 2177435 2755883 := bstep (se 1 (by rfl) ⟨2066912, by rfl⟩ : syracuseStep 2755883 = 4133825) B4133825
theorem B7349021 : Blo 2177435 7349021 := bstep (se 3 (by rfl) ⟨1377941, by rfl⟩ : syracuseStep 7349021 = 2755883) B2755883
theorem B4899347 : Blo 2177435 4899347 := bstep (se 1 (by rfl) ⟨3674510, by rfl⟩ : syracuseStep 4899347 = 7349021) B7349021
theorem B3266231 : Blo 2177435 3266231 := bstep (se 1 (by rfl) ⟨2449673, by rfl⟩ : syracuseStep 3266231 = 4899347) B4899347
theorem B2177487 : Blo 2177435 2177487 := bstep (se 1 (by rfl) ⟨1633115, by rfl⟩ : syracuseStep 2177487 = 3266231) B3266231
theorem B3266237 : Blo 2177435 3266237 := bbase (se 3 (by rfl) ⟨612419, by rfl⟩ : syracuseStep 3266237 = 1224839) (by norm_num)
theorem B2177491 : Blo 2177435 2177491 := bstep (se 1 (by rfl) ⟨1633118, by rfl⟩ : syracuseStep 2177491 = 3266237) B3266237
theorem B4899365 : Blo 2177435 4899365 := bbase (se 4 (by rfl) ⟨459315, by rfl⟩ : syracuseStep 4899365 = 918631) (by norm_num)
theorem B3266243 : Blo 2177435 3266243 := bstep (se 1 (by rfl) ⟨2449682, by rfl⟩ : syracuseStep 3266243 = 4899365) B4899365
theorem B2177495 : Blo 2177435 2177495 := bstep (se 1 (by rfl) ⟨1633121, by rfl⟩ : syracuseStep 2177495 = 3266243) B3266243
theorem B5511797 : Blo 2177435 5511797 := bbase (se 5 (by rfl) ⟨258365, by rfl⟩ : syracuseStep 5511797 = 516731) (by norm_num)
theorem B3674531 : Blo 2177435 3674531 := bstep (se 1 (by rfl) ⟨2755898, by rfl⟩ : syracuseStep 3674531 = 5511797) B5511797
theorem B2449687 : Blo 2177435 2449687 := bstep (se 1 (by rfl) ⟨1837265, by rfl⟩ : syracuseStep 2449687 = 3674531) B3674531
theorem B3266249 : Blo 2177435 3266249 := bstep (se 2 (by rfl) ⟨1224843, by rfl⟩ : syracuseStep 3266249 = 2449687) B2449687
theorem B2177499 : Blo 2177435 2177499 := bstep (se 1 (by rfl) ⟨1633124, by rfl⟩ : syracuseStep 2177499 = 3266249) B3266249
theorem B4966229 : Blo 2177435 4966229 := bbase (se 9 (by rfl) ⟨14549, by rfl⟩ : syracuseStep 4966229 = 29099) (by norm_num)
theorem B13243277 : Blo 2177435 13243277 := bstep (se 3 (by rfl) ⟨2483114, by rfl⟩ : syracuseStep 13243277 = 4966229) B4966229
theorem B8828851 : Blo 2177435 8828851 := bstep (se 1 (by rfl) ⟨6621638, by rfl⟩ : syracuseStep 8828851 = 13243277) B13243277
theorem B11771801 : Blo 2177435 11771801 := bstep (se 2 (by rfl) ⟨4414425, by rfl⟩ : syracuseStep 11771801 = 8828851) B8828851
theorem B7847867 : Blo 2177435 7847867 := bstep (se 1 (by rfl) ⟨5885900, by rfl⟩ : syracuseStep 7847867 = 11771801) B11771801
theorem B20927645 : Blo 2177435 20927645 := bstep (se 3 (by rfl) ⟨3923933, by rfl⟩ : syracuseStep 20927645 = 7847867) B7847867
theorem B13951763 : Blo 2177435 13951763 := bstep (se 1 (by rfl) ⟨10463822, by rfl⟩ : syracuseStep 13951763 = 20927645) B20927645
theorem B9301175 : Blo 2177435 9301175 := bstep (se 1 (by rfl) ⟨6975881, by rfl⟩ : syracuseStep 9301175 = 13951763) B13951763
theorem B6200783 : Blo 2177435 6200783 := bstep (se 1 (by rfl) ⟨4650587, by rfl⟩ : syracuseStep 6200783 = 9301175) B9301175
theorem B4133855 : Blo 2177435 4133855 := bstep (se 1 (by rfl) ⟨3100391, by rfl⟩ : syracuseStep 4133855 = 6200783) B6200783
theorem B11023613 : Blo 2177435 11023613 := bstep (se 3 (by rfl) ⟨2066927, by rfl⟩ : syracuseStep 11023613 = 4133855) B4133855
theorem B7349075 : Blo 2177435 7349075 := bstep (se 1 (by rfl) ⟨5511806, by rfl⟩ : syracuseStep 7349075 = 11023613) B11023613
theorem B4899383 : Blo 2177435 4899383 := bstep (se 1 (by rfl) ⟨3674537, by rfl⟩ : syracuseStep 4899383 = 7349075) B7349075
theorem B3266255 : Blo 2177435 3266255 := bstep (se 1 (by rfl) ⟨2449691, by rfl⟩ : syracuseStep 3266255 = 4899383) B4899383
theorem B2177503 : Blo 2177435 2177503 := bstep (se 1 (by rfl) ⟨1633127, by rfl⟩ : syracuseStep 2177503 = 3266255) B3266255
theorem B3266261 : Blo 2177435 3266261 := bbase (se 7 (by rfl) ⟨38276, by rfl⟩ : syracuseStep 3266261 = 76553) (by norm_num)
theorem B2177507 : Blo 2177435 2177507 := bstep (se 1 (by rfl) ⟨1633130, by rfl⟩ : syracuseStep 2177507 = 3266261) B3266261
theorem B4650605 : Blo 2177435 4650605 := bbase (se 3 (by rfl) ⟨871988, by rfl⟩ : syracuseStep 4650605 = 1743977) (by norm_num)
theorem B3100403 : Blo 2177435 3100403 := bstep (se 1 (by rfl) ⟨2325302, by rfl⟩ : syracuseStep 3100403 = 4650605) B4650605
theorem B8267741 : Blo 2177435 8267741 := bstep (se 3 (by rfl) ⟨1550201, by rfl⟩ : syracuseStep 8267741 = 3100403) B3100403
theorem B5511827 : Blo 2177435 5511827 := bstep (se 1 (by rfl) ⟨4133870, by rfl⟩ : syracuseStep 5511827 = 8267741) B8267741
theorem B3674551 : Blo 2177435 3674551 := bstep (se 1 (by rfl) ⟨2755913, by rfl⟩ : syracuseStep 3674551 = 5511827) B5511827
theorem B4899401 : Blo 2177435 4899401 := bstep (se 2 (by rfl) ⟨1837275, by rfl⟩ : syracuseStep 4899401 = 3674551) B3674551
theorem B3266267 : Blo 2177435 3266267 := bstep (se 1 (by rfl) ⟨2449700, by rfl⟩ : syracuseStep 3266267 = 4899401) B4899401
theorem B2177511 : Blo 2177435 2177511 := bstep (se 1 (by rfl) ⟨1633133, by rfl⟩ : syracuseStep 2177511 = 3266267) B3266267
theorem B2449705 : Blo 2177435 2449705 := bbase (se 2 (by rfl) ⟨918639, by rfl⟩ : syracuseStep 2449705 = 1837279) (by norm_num)
theorem B3266273 : Blo 2177435 3266273 := bstep (se 2 (by rfl) ⟨1224852, by rfl⟩ : syracuseStep 3266273 = 2449705) B2449705
theorem B2177515 : Blo 2177435 2177515 := bstep (se 1 (by rfl) ⟨1633136, by rfl⟩ : syracuseStep 2177515 = 3266273) B3266273
theorem B4778389 : Blo 2177435 4778389 := bbase (se 6 (by rfl) ⟨111993, by rfl⟩ : syracuseStep 4778389 = 223987) (by norm_num)
theorem B6371185 : Blo 2177435 6371185 := bstep (se 2 (by rfl) ⟨2389194, by rfl⟩ : syracuseStep 6371185 = 4778389) B4778389
theorem B8494913 : Blo 2177435 8494913 := bstep (se 2 (by rfl) ⟨3185592, by rfl⟩ : syracuseStep 8494913 = 6371185) B6371185
theorem B22653101 : Blo 2177435 22653101 := bstep (se 3 (by rfl) ⟨4247456, by rfl⟩ : syracuseStep 22653101 = 8494913) B8494913
theorem B15102067 : Blo 2177435 15102067 := bstep (se 1 (by rfl) ⟨11326550, by rfl⟩ : syracuseStep 15102067 = 22653101) B22653101
theorem B20136089 : Blo 2177435 20136089 := bstep (se 2 (by rfl) ⟨7551033, by rfl⟩ : syracuseStep 20136089 = 15102067) B15102067
theorem B13424059 : Blo 2177435 13424059 := bstep (se 1 (by rfl) ⟨10068044, by rfl⟩ : syracuseStep 13424059 = 20136089) B20136089
theorem B17898745 : Blo 2177435 17898745 := bstep (se 2 (by rfl) ⟨6712029, by rfl⟩ : syracuseStep 17898745 = 13424059) B13424059
theorem B23864993 : Blo 2177435 23864993 := bstep (se 2 (by rfl) ⟨8949372, by rfl⟩ : syracuseStep 23864993 = 17898745) B17898745
theorem B15909995 : Blo 2177435 15909995 := bstep (se 1 (by rfl) ⟨11932496, by rfl⟩ : syracuseStep 15909995 = 23864993) B23864993
theorem B10606663 : Blo 2177435 10606663 := bstep (se 1 (by rfl) ⟨7954997, by rfl⟩ : syracuseStep 10606663 = 15909995) B15909995
theorem B14142217 : Blo 2177435 14142217 := bstep (se 2 (by rfl) ⟨5303331, by rfl⟩ : syracuseStep 14142217 = 10606663) B10606663
theorem B18856289 : Blo 2177435 18856289 := bstep (se 2 (by rfl) ⟨7071108, by rfl⟩ : syracuseStep 18856289 = 14142217) B14142217
theorem B12570859 : Blo 2177435 12570859 := bstep (se 1 (by rfl) ⟨9428144, by rfl⟩ : syracuseStep 12570859 = 18856289) B18856289
theorem B67044581 : Blo 2177435 67044581 := bstep (se 4 (by rfl) ⟨6285429, by rfl⟩ : syracuseStep 67044581 = 12570859) B12570859
theorem B44696387 : Blo 2177435 44696387 := bstep (se 1 (by rfl) ⟨33522290, by rfl⟩ : syracuseStep 44696387 = 67044581) B67044581
theorem B29797591 : Blo 2177435 29797591 := bstep (se 1 (by rfl) ⟨22348193, by rfl⟩ : syracuseStep 29797591 = 44696387) B44696387
theorem B39730121 : Blo 2177435 39730121 := bstep (se 2 (by rfl) ⟨14898795, by rfl⟩ : syracuseStep 39730121 = 29797591) B29797591
theorem B26486747 : Blo 2177435 26486747 := bstep (se 1 (by rfl) ⟨19865060, by rfl⟩ : syracuseStep 26486747 = 39730121) B39730121
theorem B17657831 : Blo 2177435 17657831 := bstep (se 1 (by rfl) ⟨13243373, by rfl⟩ : syracuseStep 17657831 = 26486747) B26486747
theorem B11771887 : Blo 2177435 11771887 := bstep (se 1 (by rfl) ⟨8828915, by rfl⟩ : syracuseStep 11771887 = 17657831) B17657831
theorem B15695849 : Blo 2177435 15695849 := bstep (se 2 (by rfl) ⟨5885943, by rfl⟩ : syracuseStep 15695849 = 11771887) B11771887
theorem B10463899 : Blo 2177435 10463899 := bstep (se 1 (by rfl) ⟨7847924, by rfl⟩ : syracuseStep 10463899 = 15695849) B15695849
theorem B13951865 : Blo 2177435 13951865 := bstep (se 2 (by rfl) ⟨5231949, by rfl⟩ : syracuseStep 13951865 = 10463899) B10463899
theorem B9301243 : Blo 2177435 9301243 := bstep (se 1 (by rfl) ⟨6975932, by rfl⟩ : syracuseStep 9301243 = 13951865) B13951865
theorem B12401657 : Blo 2177435 12401657 := bstep (se 2 (by rfl) ⟨4650621, by rfl⟩ : syracuseStep 12401657 = 9301243) B9301243
theorem B8267771 : Blo 2177435 8267771 := bstep (se 1 (by rfl) ⟨6200828, by rfl⟩ : syracuseStep 8267771 = 12401657) B12401657
theorem B5511847 : Blo 2177435 5511847 := bstep (se 1 (by rfl) ⟨4133885, by rfl⟩ : syracuseStep 5511847 = 8267771) B8267771
theorem B7349129 : Blo 2177435 7349129 := bstep (se 2 (by rfl) ⟨2755923, by rfl⟩ : syracuseStep 7349129 = 5511847) B5511847
theorem B4899419 : Blo 2177435 4899419 := bstep (se 1 (by rfl) ⟨3674564, by rfl⟩ : syracuseStep 4899419 = 7349129) B7349129
theorem B3266279 : Blo 2177435 3266279 := bstep (se 1 (by rfl) ⟨2449709, by rfl⟩ : syracuseStep 3266279 = 4899419) B4899419
theorem B2177519 : Blo 2177435 2177519 := bstep (se 1 (by rfl) ⟨1633139, by rfl⟩ : syracuseStep 2177519 = 3266279) B3266279
theorem B3266285 : Blo 2177435 3266285 := bbase (se 3 (by rfl) ⟨612428, by rfl⟩ : syracuseStep 3266285 = 1224857) (by norm_num)
theorem B2177523 : Blo 2177435 2177523 := bstep (se 1 (by rfl) ⟨1633142, by rfl⟩ : syracuseStep 2177523 = 3266285) B3266285
theorem B4899437 : Blo 2177435 4899437 := bbase (se 3 (by rfl) ⟨918644, by rfl⟩ : syracuseStep 4899437 = 1837289) (by norm_num)
theorem B3266291 : Blo 2177435 3266291 := bstep (se 1 (by rfl) ⟨2449718, by rfl⟩ : syracuseStep 3266291 = 4899437) B4899437
theorem B2177527 : Blo 2177435 2177527 := bstep (se 1 (by rfl) ⟨1633145, by rfl⟩ : syracuseStep 2177527 = 3266291) B3266291
theorem B4133909 : Blo 2177435 4133909 := bbase (se 6 (by rfl) ⟨96888, by rfl⟩ : syracuseStep 4133909 = 193777) (by norm_num)
theorem B2755939 : Blo 2177435 2755939 := bstep (se 1 (by rfl) ⟨2066954, by rfl⟩ : syracuseStep 2755939 = 4133909) B4133909
theorem B3674585 : Blo 2177435 3674585 := bstep (se 2 (by rfl) ⟨1377969, by rfl⟩ : syracuseStep 3674585 = 2755939) B2755939
theorem B2449723 : Blo 2177435 2449723 := bstep (se 1 (by rfl) ⟨1837292, by rfl⟩ : syracuseStep 2449723 = 3674585) B3674585
theorem B3266297 : Blo 2177435 3266297 := bstep (se 2 (by rfl) ⟨1224861, by rfl⟩ : syracuseStep 3266297 = 2449723) B2449723
theorem B2177531 : Blo 2177435 2177531 := bstep (se 1 (by rfl) ⟨1633148, by rfl⟩ : syracuseStep 2177531 = 3266297) B3266297
theorem B9428213 : Blo 2177435 9428213 := bbase (se 5 (by rfl) ⟨441947, by rfl⟩ : syracuseStep 9428213 = 883895) (by norm_num)
theorem B6285475 : Blo 2177435 6285475 := bstep (se 1 (by rfl) ⟨4714106, by rfl⟩ : syracuseStep 6285475 = 9428213) B9428213
theorem B8380633 : Blo 2177435 8380633 := bstep (se 2 (by rfl) ⟨3142737, by rfl⟩ : syracuseStep 8380633 = 6285475) B6285475
theorem B11174177 : Blo 2177435 11174177 := bstep (se 2 (by rfl) ⟨4190316, by rfl⟩ : syracuseStep 11174177 = 8380633) B8380633
theorem B7449451 : Blo 2177435 7449451 := bstep (se 1 (by rfl) ⟨5587088, by rfl⟩ : syracuseStep 7449451 = 11174177) B11174177
theorem B158921621 : Blo 2177435 158921621 := bstep (se 6 (by rfl) ⟨3724725, by rfl⟩ : syracuseStep 158921621 = 7449451) B7449451
theorem B105947747 : Blo 2177435 105947747 := bstep (se 1 (by rfl) ⟨79460810, by rfl⟩ : syracuseStep 105947747 = 158921621) B158921621
theorem B70631831 : Blo 2177435 70631831 := bstep (se 1 (by rfl) ⟨52973873, by rfl⟩ : syracuseStep 70631831 = 105947747) B105947747
theorem B47087887 : Blo 2177435 47087887 := bstep (se 1 (by rfl) ⟨35315915, by rfl⟩ : syracuseStep 47087887 = 70631831) B70631831
theorem B62783849 : Blo 2177435 62783849 := bstep (se 2 (by rfl) ⟨23543943, by rfl⟩ : syracuseStep 62783849 = 47087887) B47087887
theorem B41855899 : Blo 2177435 41855899 := bstep (se 1 (by rfl) ⟨31391924, by rfl⟩ : syracuseStep 41855899 = 62783849) B62783849
theorem B55807865 : Blo 2177435 55807865 := bstep (se 2 (by rfl) ⟨20927949, by rfl⟩ : syracuseStep 55807865 = 41855899) B41855899
theorem B37205243 : Blo 2177435 37205243 := bstep (se 1 (by rfl) ⟨27903932, by rfl⟩ : syracuseStep 37205243 = 55807865) B55807865
theorem B24803495 : Blo 2177435 24803495 := bstep (se 1 (by rfl) ⟨18602621, by rfl⟩ : syracuseStep 24803495 = 37205243) B37205243
theorem B16535663 : Blo 2177435 16535663 := bstep (se 1 (by rfl) ⟨12401747, by rfl⟩ : syracuseStep 16535663 = 24803495) B24803495
theorem B11023775 : Blo 2177435 11023775 := bstep (se 1 (by rfl) ⟨8267831, by rfl⟩ : syracuseStep 11023775 = 16535663) B16535663
theorem B7349183 : Blo 2177435 7349183 := bstep (se 1 (by rfl) ⟨5511887, by rfl⟩ : syracuseStep 7349183 = 11023775) B11023775
theorem B4899455 : Blo 2177435 4899455 := bstep (se 1 (by rfl) ⟨3674591, by rfl⟩ : syracuseStep 4899455 = 7349183) B7349183
theorem B3266303 : Blo 2177435 3266303 := bstep (se 1 (by rfl) ⟨2449727, by rfl⟩ : syracuseStep 3266303 = 4899455) B4899455
theorem B2177535 : Blo 2177435 2177535 := bstep (se 1 (by rfl) ⟨1633151, by rfl⟩ : syracuseStep 2177535 = 3266303) B3266303
theorem B3266309 : Blo 2177435 3266309 := bbase (se 4 (by rfl) ⟨306216, by rfl⟩ : syracuseStep 3266309 = 612433) (by norm_num)
theorem B2177539 : Blo 2177435 2177539 := bstep (se 1 (by rfl) ⟨1633154, by rfl⟩ : syracuseStep 2177539 = 3266309) B3266309
theorem B3674605 : Blo 2177435 3674605 := bbase (se 3 (by rfl) ⟨688988, by rfl⟩ : syracuseStep 3674605 = 1377977) (by norm_num)
theorem B4899473 : Blo 2177435 4899473 := bstep (se 2 (by rfl) ⟨1837302, by rfl⟩ : syracuseStep 4899473 = 3674605) B3674605
theorem B3266315 : Blo 2177435 3266315 := bstep (se 1 (by rfl) ⟨2449736, by rfl⟩ : syracuseStep 3266315 = 4899473) B4899473
theorem B2177543 : Blo 2177435 2177543 := bstep (se 1 (by rfl) ⟨1633157, by rfl⟩ : syracuseStep 2177543 = 3266315) B3266315
theorem B2449741 : Blo 2177435 2449741 := bbase (se 3 (by rfl) ⟨459326, by rfl⟩ : syracuseStep 2449741 = 918653) (by norm_num)
theorem B3266321 : Blo 2177435 3266321 := bstep (se 2 (by rfl) ⟨1224870, by rfl⟩ : syracuseStep 3266321 = 2449741) B2449741
theorem B2177547 : Blo 2177435 2177547 := bstep (se 1 (by rfl) ⟨1633160, by rfl⟩ : syracuseStep 2177547 = 3266321) B3266321
theorem B7349237 : Blo 2177435 7349237 := bbase (se 5 (by rfl) ⟨344495, by rfl⟩ : syracuseStep 7349237 = 688991) (by norm_num)
theorem B4899491 : Blo 2177435 4899491 := bstep (se 1 (by rfl) ⟨3674618, by rfl⟩ : syracuseStep 4899491 = 7349237) B7349237
theorem B3266327 : Blo 2177435 3266327 := bstep (se 1 (by rfl) ⟨2449745, by rfl⟩ : syracuseStep 3266327 = 4899491) B4899491
theorem B2177551 : Blo 2177435 2177551 := bstep (se 1 (by rfl) ⟨1633163, by rfl⟩ : syracuseStep 2177551 = 3266327) B3266327
theorem B3266333 : Blo 2177435 3266333 := bbase (se 3 (by rfl) ⟨612437, by rfl⟩ : syracuseStep 3266333 = 1224875) (by norm_num)
theorem B2177555 : Blo 2177435 2177555 := bstep (se 1 (by rfl) ⟨1633166, by rfl⟩ : syracuseStep 2177555 = 3266333) B3266333
theorem B4899509 : Blo 2177435 4899509 := bbase (se 5 (by rfl) ⟨229664, by rfl⟩ : syracuseStep 4899509 = 459329) (by norm_num)
theorem B3266339 : Blo 2177435 3266339 := bstep (se 1 (by rfl) ⟨2449754, by rfl⟩ : syracuseStep 3266339 = 4899509) B4899509
theorem B2177559 : Blo 2177435 2177559 := bstep (se 1 (by rfl) ⟨1633169, by rfl⟩ : syracuseStep 2177559 = 3266339) B3266339
theorem B12401909 : Blo 2177435 12401909 := bbase (se 5 (by rfl) ⟨581339, by rfl⟩ : syracuseStep 12401909 = 1162679) (by norm_num)
theorem B8267939 : Blo 2177435 8267939 := bstep (se 1 (by rfl) ⟨6200954, by rfl⟩ : syracuseStep 8267939 = 12401909) B12401909
theorem B5511959 : Blo 2177435 5511959 := bstep (se 1 (by rfl) ⟨4133969, by rfl⟩ : syracuseStep 5511959 = 8267939) B8267939
theorem B3674639 : Blo 2177435 3674639 := bstep (se 1 (by rfl) ⟨2755979, by rfl⟩ : syracuseStep 3674639 = 5511959) B5511959
theorem B2449759 : Blo 2177435 2449759 := bstep (se 1 (by rfl) ⟨1837319, by rfl⟩ : syracuseStep 2449759 = 3674639) B3674639
theorem B3266345 : Blo 2177435 3266345 := bstep (se 2 (by rfl) ⟨1224879, by rfl⟩ : syracuseStep 3266345 = 2449759) B2449759
theorem B2177563 : Blo 2177435 2177563 := bstep (se 1 (by rfl) ⟨1633172, by rfl⟩ : syracuseStep 2177563 = 3266345) B3266345
theorem B6200965 : Blo 2177435 6200965 := bbase (se 4 (by rfl) ⟨581340, by rfl⟩ : syracuseStep 6200965 = 1162681) (by norm_num)
theorem B8267953 : Blo 2177435 8267953 := bstep (se 2 (by rfl) ⟨3100482, by rfl⟩ : syracuseStep 8267953 = 6200965) B6200965
theorem B11023937 : Blo 2177435 11023937 := bstep (se 2 (by rfl) ⟨4133976, by rfl⟩ : syracuseStep 11023937 = 8267953) B8267953
theorem B7349291 : Blo 2177435 7349291 := bstep (se 1 (by rfl) ⟨5511968, by rfl⟩ : syracuseStep 7349291 = 11023937) B11023937
theorem B4899527 : Blo 2177435 4899527 := bstep (se 1 (by rfl) ⟨3674645, by rfl⟩ : syracuseStep 4899527 = 7349291) B7349291
theorem B3266351 : Blo 2177435 3266351 := bstep (se 1 (by rfl) ⟨2449763, by rfl⟩ : syracuseStep 3266351 = 4899527) B4899527
theorem B2177567 : Blo 2177435 2177567 := bstep (se 1 (by rfl) ⟨1633175, by rfl⟩ : syracuseStep 2177567 = 3266351) B3266351
theorem B3266357 : Blo 2177435 3266357 := bbase (se 5 (by rfl) ⟨153110, by rfl⟩ : syracuseStep 3266357 = 306221) (by norm_num)
theorem B2177571 : Blo 2177435 2177571 := bstep (se 1 (by rfl) ⟨1633178, by rfl⟩ : syracuseStep 2177571 = 3266357) B3266357
theorem B5511989 : Blo 2177435 5511989 := bbase (se 5 (by rfl) ⟨258374, by rfl⟩ : syracuseStep 5511989 = 516749) (by norm_num)
theorem B3674659 : Blo 2177435 3674659 := bstep (se 1 (by rfl) ⟨2755994, by rfl⟩ : syracuseStep 3674659 = 5511989) B5511989
theorem B4899545 : Blo 2177435 4899545 := bstep (se 2 (by rfl) ⟨1837329, by rfl⟩ : syracuseStep 4899545 = 3674659) B3674659
theorem B3266363 : Blo 2177435 3266363 := bstep (se 1 (by rfl) ⟨2449772, by rfl⟩ : syracuseStep 3266363 = 4899545) B4899545
theorem B2177575 : Blo 2177435 2177575 := bstep (se 1 (by rfl) ⟨1633181, by rfl⟩ : syracuseStep 2177575 = 3266363) B3266363
theorem B2449777 : Blo 2177435 2449777 := bbase (se 2 (by rfl) ⟨918666, by rfl⟩ : syracuseStep 2449777 = 1837333) (by norm_num)
theorem B3266369 : Blo 2177435 3266369 := bstep (se 2 (by rfl) ⟨1224888, by rfl⟩ : syracuseStep 3266369 = 2449777) B2449777
theorem B2177579 : Blo 2177435 2177579 := bstep (se 1 (by rfl) ⟨1633184, by rfl⟩ : syracuseStep 2177579 = 3266369) B3266369
theorem B3488069 : Blo 2177435 3488069 := bbase (se 4 (by rfl) ⟨327006, by rfl⟩ : syracuseStep 3488069 = 654013) (by norm_num)
theorem B9301517 : Blo 2177435 9301517 := bstep (se 3 (by rfl) ⟨1744034, by rfl⟩ : syracuseStep 9301517 = 3488069) B3488069
theorem B6201011 : Blo 2177435 6201011 := bstep (se 1 (by rfl) ⟨4650758, by rfl⟩ : syracuseStep 6201011 = 9301517) B9301517
theorem B4134007 : Blo 2177435 4134007 := bstep (se 1 (by rfl) ⟨3100505, by rfl⟩ : syracuseStep 4134007 = 6201011) B6201011
theorem B5512009 : Blo 2177435 5512009 := bstep (se 2 (by rfl) ⟨2067003, by rfl⟩ : syracuseStep 5512009 = 4134007) B4134007
theorem B7349345 : Blo 2177435 7349345 := bstep (se 2 (by rfl) ⟨2756004, by rfl⟩ : syracuseStep 7349345 = 5512009) B5512009
theorem B4899563 : Blo 2177435 4899563 := bstep (se 1 (by rfl) ⟨3674672, by rfl⟩ : syracuseStep 4899563 = 7349345) B7349345
theorem B3266375 : Blo 2177435 3266375 := bstep (se 1 (by rfl) ⟨2449781, by rfl⟩ : syracuseStep 3266375 = 4899563) B4899563
theorem B2177583 : Blo 2177435 2177583 := bstep (se 1 (by rfl) ⟨1633187, by rfl⟩ : syracuseStep 2177583 = 3266375) B3266375
theorem B3266381 : Blo 2177435 3266381 := bbase (se 3 (by rfl) ⟨612446, by rfl⟩ : syracuseStep 3266381 = 1224893) (by norm_num)
theorem B2177587 : Blo 2177435 2177587 := bstep (se 1 (by rfl) ⟨1633190, by rfl⟩ : syracuseStep 2177587 = 3266381) B3266381
theorem B4899581 : Blo 2177435 4899581 := bbase (se 3 (by rfl) ⟨918671, by rfl⟩ : syracuseStep 4899581 = 1837343) (by norm_num)
theorem B3266387 : Blo 2177435 3266387 := bstep (se 1 (by rfl) ⟨2449790, by rfl⟩ : syracuseStep 3266387 = 4899581) B4899581
theorem B2177591 : Blo 2177435 2177591 := bstep (se 1 (by rfl) ⟨1633193, by rfl⟩ : syracuseStep 2177591 = 3266387) B3266387
theorem B3674693 : Blo 2177435 3674693 := bbase (se 4 (by rfl) ⟨344502, by rfl⟩ : syracuseStep 3674693 = 689005) (by norm_num)
theorem B2449795 : Blo 2177435 2449795 := bstep (se 1 (by rfl) ⟨1837346, by rfl⟩ : syracuseStep 2449795 = 3674693) B3674693
theorem B3266393 : Blo 2177435 3266393 := bstep (se 2 (by rfl) ⟨1224897, by rfl⟩ : syracuseStep 3266393 = 2449795) B2449795
theorem B2177595 : Blo 2177435 2177595 := bstep (se 1 (by rfl) ⟨1633196, by rfl⟩ : syracuseStep 2177595 = 3266393) B3266393
theorem B16536149 : Blo 2177435 16536149 := bbase (se 8 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 16536149 = 193783) (by norm_num)
theorem B11024099 : Blo 2177435 11024099 := bstep (se 1 (by rfl) ⟨8268074, by rfl⟩ : syracuseStep 11024099 = 16536149) B16536149
theorem B7349399 : Blo 2177435 7349399 := bstep (se 1 (by rfl) ⟨5512049, by rfl⟩ : syracuseStep 7349399 = 11024099) B11024099
theorem B4899599 : Blo 2177435 4899599 := bstep (se 1 (by rfl) ⟨3674699, by rfl⟩ : syracuseStep 4899599 = 7349399) B7349399
theorem B3266399 : Blo 2177435 3266399 := bstep (se 1 (by rfl) ⟨2449799, by rfl⟩ : syracuseStep 3266399 = 4899599) B4899599
theorem B2177599 : Blo 2177435 2177599 := bstep (se 1 (by rfl) ⟨1633199, by rfl⟩ : syracuseStep 2177599 = 3266399) B3266399
theorem B3266405 : Blo 2177435 3266405 := bbase (se 4 (by rfl) ⟨306225, by rfl⟩ : syracuseStep 3266405 = 612451) (by norm_num)
theorem B2177603 : Blo 2177435 2177603 := bstep (se 1 (by rfl) ⟨1633202, by rfl⟩ : syracuseStep 2177603 = 3266405) B3266405
theorem B4134053 : Blo 2177435 4134053 := bbase (se 4 (by rfl) ⟨387567, by rfl⟩ : syracuseStep 4134053 = 775135) (by norm_num)
theorem B2756035 : Blo 2177435 2756035 := bstep (se 1 (by rfl) ⟨2067026, by rfl⟩ : syracuseStep 2756035 = 4134053) B4134053
theorem B3674713 : Blo 2177435 3674713 := bstep (se 2 (by rfl) ⟨1378017, by rfl⟩ : syracuseStep 3674713 = 2756035) B2756035
theorem B4899617 : Blo 2177435 4899617 := bstep (se 2 (by rfl) ⟨1837356, by rfl⟩ : syracuseStep 4899617 = 3674713) B3674713
theorem B3266411 : Blo 2177435 3266411 := bstep (se 1 (by rfl) ⟨2449808, by rfl⟩ : syracuseStep 3266411 = 4899617) B4899617
theorem B2177607 : Blo 2177435 2177607 := bstep (se 1 (by rfl) ⟨1633205, by rfl⟩ : syracuseStep 2177607 = 3266411) B3266411
theorem B2449813 : Blo 2177435 2449813 := bbase (se 6 (by rfl) ⟨57417, by rfl⟩ : syracuseStep 2449813 = 114835) (by norm_num)
theorem B3266417 : Blo 2177435 3266417 := bstep (se 2 (by rfl) ⟨1224906, by rfl⟩ : syracuseStep 3266417 = 2449813) B2449813
theorem B2177611 : Blo 2177435 2177611 := bstep (se 1 (by rfl) ⟨1633208, by rfl⟩ : syracuseStep 2177611 = 3266417) B3266417
theorem B2756045 : Blo 2177435 2756045 := bbase (se 3 (by rfl) ⟨516758, by rfl⟩ : syracuseStep 2756045 = 1033517) (by norm_num)
theorem B7349453 : Blo 2177435 7349453 := bstep (se 3 (by rfl) ⟨1378022, by rfl⟩ : syracuseStep 7349453 = 2756045) B2756045
theorem B4899635 : Blo 2177435 4899635 := bstep (se 1 (by rfl) ⟨3674726, by rfl⟩ : syracuseStep 4899635 = 7349453) B7349453
theorem B3266423 : Blo 2177435 3266423 := bstep (se 1 (by rfl) ⟨2449817, by rfl⟩ : syracuseStep 3266423 = 4899635) B4899635
theorem B2177615 : Blo 2177435 2177615 := bstep (se 1 (by rfl) ⟨1633211, by rfl⟩ : syracuseStep 2177615 = 3266423) B3266423
theorem B3266429 : Blo 2177435 3266429 := bbase (se 3 (by rfl) ⟨612455, by rfl⟩ : syracuseStep 3266429 = 1224911) (by norm_num)
theorem B2177619 : Blo 2177435 2177619 := bstep (se 1 (by rfl) ⟨1633214, by rfl⟩ : syracuseStep 2177619 = 3266429) B3266429
theorem B4899653 : Blo 2177435 4899653 := bbase (se 4 (by rfl) ⟨459342, by rfl⟩ : syracuseStep 4899653 = 918685) (by norm_num)
theorem B3266435 : Blo 2177435 3266435 := bstep (se 1 (by rfl) ⟨2449826, by rfl⟩ : syracuseStep 3266435 = 4899653) B4899653
theorem B2177623 : Blo 2177435 2177623 := bstep (se 1 (by rfl) ⟨1633217, by rfl⟩ : syracuseStep 2177623 = 3266435) B3266435
theorem B4650853 : Blo 2177435 4650853 := bbase (se 4 (by rfl) ⟨436017, by rfl⟩ : syracuseStep 4650853 = 872035) (by norm_num)
theorem B6201137 : Blo 2177435 6201137 := bstep (se 2 (by rfl) ⟨2325426, by rfl⟩ : syracuseStep 6201137 = 4650853) B4650853
theorem B4134091 : Blo 2177435 4134091 := bstep (se 1 (by rfl) ⟨3100568, by rfl⟩ : syracuseStep 4134091 = 6201137) B6201137
theorem B5512121 : Blo 2177435 5512121 := bstep (se 2 (by rfl) ⟨2067045, by rfl⟩ : syracuseStep 5512121 = 4134091) B4134091
theorem B3674747 : Blo 2177435 3674747 := bstep (se 1 (by rfl) ⟨2756060, by rfl⟩ : syracuseStep 3674747 = 5512121) B5512121
theorem B2449831 : Blo 2177435 2449831 := bstep (se 1 (by rfl) ⟨1837373, by rfl⟩ : syracuseStep 2449831 = 3674747) B3674747
theorem B3266441 : Blo 2177435 3266441 := bstep (se 2 (by rfl) ⟨1224915, by rfl⟩ : syracuseStep 3266441 = 2449831) B2449831
theorem B2177627 : Blo 2177435 2177627 := bstep (se 1 (by rfl) ⟨1633220, by rfl⟩ : syracuseStep 2177627 = 3266441) B3266441
theorem B11024261 : Blo 2177435 11024261 := bbase (se 4 (by rfl) ⟨1033524, by rfl⟩ : syracuseStep 11024261 = 2067049) (by norm_num)
theorem B7349507 : Blo 2177435 7349507 := bstep (se 1 (by rfl) ⟨5512130, by rfl⟩ : syracuseStep 7349507 = 11024261) B11024261
theorem B4899671 : Blo 2177435 4899671 := bstep (se 1 (by rfl) ⟨3674753, by rfl⟩ : syracuseStep 4899671 = 7349507) B7349507
theorem B3266447 : Blo 2177435 3266447 := bstep (se 1 (by rfl) ⟨2449835, by rfl⟩ : syracuseStep 3266447 = 4899671) B4899671
theorem B2177631 : Blo 2177435 2177631 := bstep (se 1 (by rfl) ⟨1633223, by rfl⟩ : syracuseStep 2177631 = 3266447) B3266447
theorem B3266453 : Blo 2177435 3266453 := bbase (se 6 (by rfl) ⟨76557, by rfl⟩ : syracuseStep 3266453 = 153115) (by norm_num)
theorem B2177635 : Blo 2177435 2177635 := bstep (se 1 (by rfl) ⟨1633226, by rfl⟩ : syracuseStep 2177635 = 3266453) B3266453
theorem B5966581 : Blo 2177435 5966581 := bbase (se 5 (by rfl) ⟨279683, by rfl⟩ : syracuseStep 5966581 = 559367) (by norm_num)
theorem B7955441 : Blo 2177435 7955441 := bstep (se 2 (by rfl) ⟨2983290, by rfl⟩ : syracuseStep 7955441 = 5966581) B5966581
theorem B5303627 : Blo 2177435 5303627 := bstep (se 1 (by rfl) ⟨3977720, by rfl⟩ : syracuseStep 5303627 = 7955441) B7955441
theorem B3535751 : Blo 2177435 3535751 := bstep (se 1 (by rfl) ⟨2651813, by rfl⟩ : syracuseStep 3535751 = 5303627) B5303627
theorem B9428669 : Blo 2177435 9428669 := bstep (se 3 (by rfl) ⟨1767875, by rfl⟩ : syracuseStep 9428669 = 3535751) B3535751
theorem B6285779 : Blo 2177435 6285779 := bstep (se 1 (by rfl) ⟨4714334, by rfl⟩ : syracuseStep 6285779 = 9428669) B9428669
theorem B4190519 : Blo 2177435 4190519 := bstep (se 1 (by rfl) ⟨3142889, by rfl⟩ : syracuseStep 4190519 = 6285779) B6285779
theorem B2793679 : Blo 2177435 2793679 := bstep (se 1 (by rfl) ⟨2095259, by rfl⟩ : syracuseStep 2793679 = 4190519) B4190519
theorem B14899621 : Blo 2177435 14899621 := bstep (se 4 (by rfl) ⟨1396839, by rfl⟩ : syracuseStep 14899621 = 2793679) B2793679
theorem B19866161 : Blo 2177435 19866161 := bstep (se 2 (by rfl) ⟨7449810, by rfl⟩ : syracuseStep 19866161 = 14899621) B14899621
theorem B13244107 : Blo 2177435 13244107 := bstep (se 1 (by rfl) ⟨9933080, by rfl⟩ : syracuseStep 13244107 = 19866161) B19866161
theorem B17658809 : Blo 2177435 17658809 := bstep (se 2 (by rfl) ⟨6622053, by rfl⟩ : syracuseStep 17658809 = 13244107) B13244107
theorem B11772539 : Blo 2177435 11772539 := bstep (se 1 (by rfl) ⟨8829404, by rfl⟩ : syracuseStep 11772539 = 17658809) B17658809
theorem B7848359 : Blo 2177435 7848359 := bstep (se 1 (by rfl) ⟨5886269, by rfl⟩ : syracuseStep 7848359 = 11772539) B11772539
theorem B5232239 : Blo 2177435 5232239 := bstep (se 1 (by rfl) ⟨3924179, by rfl⟩ : syracuseStep 5232239 = 7848359) B7848359
theorem B3488159 : Blo 2177435 3488159 := bstep (se 1 (by rfl) ⟨2616119, by rfl⟩ : syracuseStep 3488159 = 5232239) B5232239
theorem B2325439 : Blo 2177435 2325439 := bstep (se 1 (by rfl) ⟨1744079, by rfl⟩ : syracuseStep 2325439 = 3488159) B3488159
theorem B12402341 : Blo 2177435 12402341 := bstep (se 4 (by rfl) ⟨1162719, by rfl⟩ : syracuseStep 12402341 = 2325439) B2325439
theorem B8268227 : Blo 2177435 8268227 := bstep (se 1 (by rfl) ⟨6201170, by rfl⟩ : syracuseStep 8268227 = 12402341) B12402341
theorem B5512151 : Blo 2177435 5512151 := bstep (se 1 (by rfl) ⟨4134113, by rfl⟩ : syracuseStep 5512151 = 8268227) B8268227
theorem B3674767 : Blo 2177435 3674767 := bstep (se 1 (by rfl) ⟨2756075, by rfl⟩ : syracuseStep 3674767 = 5512151) B5512151
theorem B4899689 : Blo 2177435 4899689 := bstep (se 2 (by rfl) ⟨1837383, by rfl⟩ : syracuseStep 4899689 = 3674767) B3674767
theorem B3266459 : Blo 2177435 3266459 := bstep (se 1 (by rfl) ⟨2449844, by rfl⟩ : syracuseStep 3266459 = 4899689) B4899689
theorem B2177639 : Blo 2177435 2177639 := bstep (se 1 (by rfl) ⟨1633229, by rfl⟩ : syracuseStep 2177639 = 3266459) B3266459
theorem B2449849 : Blo 2177435 2449849 := bbase (se 2 (by rfl) ⟨918693, by rfl⟩ : syracuseStep 2449849 = 1837387) (by norm_num)
theorem B3266465 : Blo 2177435 3266465 := bstep (se 2 (by rfl) ⟨1224924, by rfl⟩ : syracuseStep 3266465 = 2449849) B2449849
theorem B2177643 : Blo 2177435 2177643 := bstep (se 1 (by rfl) ⟨1633232, by rfl⟩ : syracuseStep 2177643 = 3266465) B3266465
theorem B7364933 : Blo 2177435 7364933 := bbase (se 4 (by rfl) ⟨690462, by rfl⟩ : syracuseStep 7364933 = 1380925) (by norm_num)
theorem B4909955 : Blo 2177435 4909955 := bstep (se 1 (by rfl) ⟨3682466, by rfl⟩ : syracuseStep 4909955 = 7364933) B7364933
theorem B13093213 : Blo 2177435 13093213 := bstep (se 3 (by rfl) ⟨2454977, by rfl⟩ : syracuseStep 13093213 = 4909955) B4909955
theorem B17457617 : Blo 2177435 17457617 := bstep (se 2 (by rfl) ⟨6546606, by rfl⟩ : syracuseStep 17457617 = 13093213) B13093213
theorem B11638411 : Blo 2177435 11638411 := bstep (se 1 (by rfl) ⟨8728808, by rfl⟩ : syracuseStep 11638411 = 17457617) B17457617
theorem B62071525 : Blo 2177435 62071525 := bstep (se 4 (by rfl) ⟨5819205, by rfl⟩ : syracuseStep 62071525 = 11638411) B11638411
theorem B82762033 : Blo 2177435 82762033 := bstep (se 2 (by rfl) ⟨31035762, by rfl⟩ : syracuseStep 82762033 = 62071525) B62071525
theorem B110349377 : Blo 2177435 110349377 := bstep (se 2 (by rfl) ⟨41381016, by rfl⟩ : syracuseStep 110349377 = 82762033) B82762033
theorem B73566251 : Blo 2177435 73566251 := bstep (se 1 (by rfl) ⟨55174688, by rfl⟩ : syracuseStep 73566251 = 110349377) B110349377
theorem B49044167 : Blo 2177435 49044167 := bstep (se 1 (by rfl) ⟨36783125, by rfl⟩ : syracuseStep 49044167 = 73566251) B73566251
theorem B32696111 : Blo 2177435 32696111 := bstep (se 1 (by rfl) ⟨24522083, by rfl⟩ : syracuseStep 32696111 = 49044167) B49044167
theorem B21797407 : Blo 2177435 21797407 := bstep (se 1 (by rfl) ⟨16348055, by rfl⟩ : syracuseStep 21797407 = 32696111) B32696111
theorem B29063209 : Blo 2177435 29063209 := bstep (se 2 (by rfl) ⟨10898703, by rfl⟩ : syracuseStep 29063209 = 21797407) B21797407
theorem B38750945 : Blo 2177435 38750945 := bstep (se 2 (by rfl) ⟨14531604, by rfl⟩ : syracuseStep 38750945 = 29063209) B29063209
theorem B103335853 : Blo 2177435 103335853 := bstep (se 3 (by rfl) ⟨19375472, by rfl⟩ : syracuseStep 103335853 = 38750945) B38750945
theorem B137781137 : Blo 2177435 137781137 := bstep (se 2 (by rfl) ⟨51667926, by rfl⟩ : syracuseStep 137781137 = 103335853) B103335853
theorem B91854091 : Blo 2177435 91854091 := bstep (se 1 (by rfl) ⟨68890568, by rfl⟩ : syracuseStep 91854091 = 137781137) B137781137
theorem B122472121 : Blo 2177435 122472121 := bstep (se 2 (by rfl) ⟨45927045, by rfl⟩ : syracuseStep 122472121 = 91854091) B91854091
theorem B163296161 : Blo 2177435 163296161 := bstep (se 2 (by rfl) ⟨61236060, by rfl⟩ : syracuseStep 163296161 = 122472121) B122472121
theorem B108864107 : Blo 2177435 108864107 := bstep (se 1 (by rfl) ⟨81648080, by rfl⟩ : syracuseStep 108864107 = 163296161) B163296161
theorem B72576071 : Blo 2177435 72576071 := bstep (se 1 (by rfl) ⟨54432053, by rfl⟩ : syracuseStep 72576071 = 108864107) B108864107
theorem B48384047 : Blo 2177435 48384047 := bstep (se 1 (by rfl) ⟨36288035, by rfl⟩ : syracuseStep 48384047 = 72576071) B72576071
theorem B32256031 : Blo 2177435 32256031 := bstep (se 1 (by rfl) ⟨24192023, by rfl⟩ : syracuseStep 32256031 = 48384047) B48384047
theorem B43008041 : Blo 2177435 43008041 := bstep (se 2 (by rfl) ⟨16128015, by rfl⟩ : syracuseStep 43008041 = 32256031) B32256031
theorem B114688109 : Blo 2177435 114688109 := bstep (se 3 (by rfl) ⟨21504020, by rfl⟩ : syracuseStep 114688109 = 43008041) B43008041
theorem B76458739 : Blo 2177435 76458739 := bstep (se 1 (by rfl) ⟨57344054, by rfl⟩ : syracuseStep 76458739 = 114688109) B114688109
theorem B101944985 : Blo 2177435 101944985 := bstep (se 2 (by rfl) ⟨38229369, by rfl⟩ : syracuseStep 101944985 = 76458739) B76458739
theorem B271853293 : Blo 2177435 271853293 := bstep (se 3 (by rfl) ⟨50972492, by rfl⟩ : syracuseStep 271853293 = 101944985) B101944985
theorem B362471057 : Blo 2177435 362471057 := bstep (se 2 (by rfl) ⟨135926646, by rfl⟩ : syracuseStep 362471057 = 271853293) B271853293
theorem B241647371 : Blo 2177435 241647371 := bstep (se 1 (by rfl) ⟨181235528, by rfl⟩ : syracuseStep 241647371 = 362471057) B362471057
theorem B161098247 : Blo 2177435 161098247 := bstep (se 1 (by rfl) ⟨120823685, by rfl⟩ : syracuseStep 161098247 = 241647371) B241647371
theorem B107398831 : Blo 2177435 107398831 := bstep (se 1 (by rfl) ⟨80549123, by rfl⟩ : syracuseStep 107398831 = 161098247) B161098247
theorem B143198441 : Blo 2177435 143198441 := bstep (se 2 (by rfl) ⟨53699415, by rfl⟩ : syracuseStep 143198441 = 107398831) B107398831
theorem B95465627 : Blo 2177435 95465627 := bstep (se 1 (by rfl) ⟨71599220, by rfl⟩ : syracuseStep 95465627 = 143198441) B143198441
theorem B63643751 : Blo 2177435 63643751 := bstep (se 1 (by rfl) ⟨47732813, by rfl⟩ : syracuseStep 63643751 = 95465627) B95465627
theorem B42429167 : Blo 2177435 42429167 := bstep (se 1 (by rfl) ⟨31821875, by rfl⟩ : syracuseStep 42429167 = 63643751) B63643751
theorem B28286111 : Blo 2177435 28286111 := bstep (se 1 (by rfl) ⟨21214583, by rfl⟩ : syracuseStep 28286111 = 42429167) B42429167
theorem B18857407 : Blo 2177435 18857407 := bstep (se 1 (by rfl) ⟨14143055, by rfl⟩ : syracuseStep 18857407 = 28286111) B28286111
theorem B25143209 : Blo 2177435 25143209 := bstep (se 2 (by rfl) ⟨9428703, by rfl⟩ : syracuseStep 25143209 = 18857407) B18857407
theorem B16762139 : Blo 2177435 16762139 := bstep (se 1 (by rfl) ⟨12571604, by rfl⟩ : syracuseStep 16762139 = 25143209) B25143209
theorem B11174759 : Blo 2177435 11174759 := bstep (se 1 (by rfl) ⟨8381069, by rfl⟩ : syracuseStep 11174759 = 16762139) B16762139
theorem B7449839 : Blo 2177435 7449839 := bstep (se 1 (by rfl) ⟨5587379, by rfl⟩ : syracuseStep 7449839 = 11174759) B11174759
theorem B4966559 : Blo 2177435 4966559 := bstep (se 1 (by rfl) ⟨3724919, by rfl⟩ : syracuseStep 4966559 = 7449839) B7449839
theorem B3311039 : Blo 2177435 3311039 := bstep (se 1 (by rfl) ⟨2483279, by rfl⟩ : syracuseStep 3311039 = 4966559) B4966559
theorem B2207359 : Blo 2177435 2207359 := bstep (se 1 (by rfl) ⟨1655519, by rfl⟩ : syracuseStep 2207359 = 3311039) B3311039
theorem B2943145 : Blo 2177435 2943145 := bstep (se 2 (by rfl) ⟨1103679, by rfl⟩ : syracuseStep 2943145 = 2207359) B2207359
theorem B15696773 : Blo 2177435 15696773 := bstep (se 4 (by rfl) ⟨1471572, by rfl⟩ : syracuseStep 15696773 = 2943145) B2943145
theorem B10464515 : Blo 2177435 10464515 := bstep (se 1 (by rfl) ⟨7848386, by rfl⟩ : syracuseStep 10464515 = 15696773) B15696773
theorem B6976343 : Blo 2177435 6976343 := bstep (se 1 (by rfl) ⟨5232257, by rfl⟩ : syracuseStep 6976343 = 10464515) B10464515
theorem B4650895 : Blo 2177435 4650895 := bstep (se 1 (by rfl) ⟨3488171, by rfl⟩ : syracuseStep 4650895 = 6976343) B6976343
theorem B6201193 : Blo 2177435 6201193 := bstep (se 2 (by rfl) ⟨2325447, by rfl⟩ : syracuseStep 6201193 = 4650895) B4650895
theorem B8268257 : Blo 2177435 8268257 := bstep (se 2 (by rfl) ⟨3100596, by rfl⟩ : syracuseStep 8268257 = 6201193) B6201193
theorem B5512171 : Blo 2177435 5512171 := bstep (se 1 (by rfl) ⟨4134128, by rfl⟩ : syracuseStep 5512171 = 8268257) B8268257
theorem B7349561 : Blo 2177435 7349561 := bstep (se 2 (by rfl) ⟨2756085, by rfl⟩ : syracuseStep 7349561 = 5512171) B5512171
theorem B4899707 : Blo 2177435 4899707 := bstep (se 1 (by rfl) ⟨3674780, by rfl⟩ : syracuseStep 4899707 = 7349561) B7349561
theorem B3266471 : Blo 2177435 3266471 := bstep (se 1 (by rfl) ⟨2449853, by rfl⟩ : syracuseStep 3266471 = 4899707) B4899707
theorem B2177647 : Blo 2177435 2177647 := bstep (se 1 (by rfl) ⟨1633235, by rfl⟩ : syracuseStep 2177647 = 3266471) B3266471
theorem B3266477 : Blo 2177435 3266477 := bbase (se 3 (by rfl) ⟨612464, by rfl⟩ : syracuseStep 3266477 = 1224929) (by norm_num)
theorem B2177651 : Blo 2177435 2177651 := bstep (se 1 (by rfl) ⟨1633238, by rfl⟩ : syracuseStep 2177651 = 3266477) B3266477
theorem B4899725 : Blo 2177435 4899725 := bbase (se 3 (by rfl) ⟨918698, by rfl⟩ : syracuseStep 4899725 = 1837397) (by norm_num)
theorem B3266483 : Blo 2177435 3266483 := bstep (se 1 (by rfl) ⟨2449862, by rfl⟩ : syracuseStep 3266483 = 4899725) B4899725
theorem B2177655 : Blo 2177435 2177655 := bstep (se 1 (by rfl) ⟨1633241, by rfl⟩ : syracuseStep 2177655 = 3266483) B3266483
theorem B2756101 : Blo 2177435 2756101 := bbase (se 4 (by rfl) ⟨258384, by rfl⟩ : syracuseStep 2756101 = 516769) (by norm_num)
theorem B3674801 : Blo 2177435 3674801 := bstep (se 2 (by rfl) ⟨1378050, by rfl⟩ : syracuseStep 3674801 = 2756101) B2756101
theorem B2449867 : Blo 2177435 2449867 := bstep (se 1 (by rfl) ⟨1837400, by rfl⟩ : syracuseStep 2449867 = 3674801) B3674801
theorem B3266489 : Blo 2177435 3266489 := bstep (se 2 (by rfl) ⟨1224933, by rfl⟩ : syracuseStep 3266489 = 2449867) B2449867
theorem B2177659 : Blo 2177435 2177659 := bstep (se 1 (by rfl) ⟨1633244, by rfl⟩ : syracuseStep 2177659 = 3266489) B3266489
theorem B2793709 : Blo 2177435 2793709 := bbase (se 3 (by rfl) ⟨523820, by rfl⟩ : syracuseStep 2793709 = 1047641) (by norm_num)
theorem B14899781 : Blo 2177435 14899781 := bstep (se 4 (by rfl) ⟨1396854, by rfl⟩ : syracuseStep 14899781 = 2793709) B2793709
theorem B9933187 : Blo 2177435 9933187 := bstep (se 1 (by rfl) ⟨7449890, by rfl⟩ : syracuseStep 9933187 = 14899781) B14899781
theorem B13244249 : Blo 2177435 13244249 := bstep (se 2 (by rfl) ⟨4966593, by rfl⟩ : syracuseStep 13244249 = 9933187) B9933187
theorem B8829499 : Blo 2177435 8829499 := bstep (se 1 (by rfl) ⟨6622124, by rfl⟩ : syracuseStep 8829499 = 13244249) B13244249
theorem B11772665 : Blo 2177435 11772665 := bstep (se 2 (by rfl) ⟨4414749, by rfl⟩ : syracuseStep 11772665 = 8829499) B8829499
theorem B7848443 : Blo 2177435 7848443 := bstep (se 1 (by rfl) ⟨5886332, by rfl⟩ : syracuseStep 7848443 = 11772665) B11772665
theorem B5232295 : Blo 2177435 5232295 := bstep (se 1 (by rfl) ⟨3924221, by rfl⟩ : syracuseStep 5232295 = 7848443) B7848443
theorem B27905573 : Blo 2177435 27905573 := bstep (se 4 (by rfl) ⟨2616147, by rfl⟩ : syracuseStep 27905573 = 5232295) B5232295
theorem B18603715 : Blo 2177435 18603715 := bstep (se 1 (by rfl) ⟨13952786, by rfl⟩ : syracuseStep 18603715 = 27905573) B27905573
theorem B24804953 : Blo 2177435 24804953 := bstep (se 2 (by rfl) ⟨9301857, by rfl⟩ : syracuseStep 24804953 = 18603715) B18603715
theorem B16536635 : Blo 2177435 16536635 := bstep (se 1 (by rfl) ⟨12402476, by rfl⟩ : syracuseStep 16536635 = 24804953) B24804953
theorem B11024423 : Blo 2177435 11024423 := bstep (se 1 (by rfl) ⟨8268317, by rfl⟩ : syracuseStep 11024423 = 16536635) B16536635
theorem B7349615 : Blo 2177435 7349615 := bstep (se 1 (by rfl) ⟨5512211, by rfl⟩ : syracuseStep 7349615 = 11024423) B11024423
theorem B4899743 : Blo 2177435 4899743 := bstep (se 1 (by rfl) ⟨3674807, by rfl⟩ : syracuseStep 4899743 = 7349615) B7349615
theorem B3266495 : Blo 2177435 3266495 := bstep (se 1 (by rfl) ⟨2449871, by rfl⟩ : syracuseStep 3266495 = 4899743) B4899743
theorem B2177663 : Blo 2177435 2177663 := bstep (se 1 (by rfl) ⟨1633247, by rfl⟩ : syracuseStep 2177663 = 3266495) B3266495
theorem B3266501 : Blo 2177435 3266501 := bbase (se 4 (by rfl) ⟨306234, by rfl⟩ : syracuseStep 3266501 = 612469) (by norm_num)
theorem B2177667 : Blo 2177435 2177667 := bstep (se 1 (by rfl) ⟨1633250, by rfl⟩ : syracuseStep 2177667 = 3266501) B3266501
theorem B3674821 : Blo 2177435 3674821 := bbase (se 4 (by rfl) ⟨344514, by rfl⟩ : syracuseStep 3674821 = 689029) (by norm_num)
theorem B4899761 : Blo 2177435 4899761 := bstep (se 2 (by rfl) ⟨1837410, by rfl⟩ : syracuseStep 4899761 = 3674821) B3674821
theorem B3266507 : Blo 2177435 3266507 := bstep (se 1 (by rfl) ⟨2449880, by rfl⟩ : syracuseStep 3266507 = 4899761) B4899761
theorem B2177671 : Blo 2177435 2177671 := bstep (se 1 (by rfl) ⟨1633253, by rfl⟩ : syracuseStep 2177671 = 3266507) B3266507
theorem B2449885 : Blo 2177435 2449885 := bbase (se 3 (by rfl) ⟨459353, by rfl⟩ : syracuseStep 2449885 = 918707) (by norm_num)
theorem B3266513 : Blo 2177435 3266513 := bstep (se 2 (by rfl) ⟨1224942, by rfl⟩ : syracuseStep 3266513 = 2449885) B2449885
theorem B2177675 : Blo 2177435 2177675 := bstep (se 1 (by rfl) ⟨1633256, by rfl⟩ : syracuseStep 2177675 = 3266513) B3266513
theorem B7349669 : Blo 2177435 7349669 := bbase (se 4 (by rfl) ⟨689031, by rfl⟩ : syracuseStep 7349669 = 1378063) (by norm_num)
theorem B4899779 : Blo 2177435 4899779 := bstep (se 1 (by rfl) ⟨3674834, by rfl⟩ : syracuseStep 4899779 = 7349669) B7349669
theorem B3266519 : Blo 2177435 3266519 := bstep (se 1 (by rfl) ⟨2449889, by rfl⟩ : syracuseStep 3266519 = 4899779) B4899779
theorem B2177679 : Blo 2177435 2177679 := bstep (se 1 (by rfl) ⟨1633259, by rfl⟩ : syracuseStep 2177679 = 3266519) B3266519
theorem B3266525 : Blo 2177435 3266525 := bbase (se 3 (by rfl) ⟨612473, by rfl⟩ : syracuseStep 3266525 = 1224947) (by norm_num)
theorem B2177683 : Blo 2177435 2177683 := bstep (se 1 (by rfl) ⟨1633262, by rfl⟩ : syracuseStep 2177683 = 3266525) B3266525
theorem B4899797 : Blo 2177435 4899797 := bbase (se 7 (by rfl) ⟨57419, by rfl⟩ : syracuseStep 4899797 = 114839) (by norm_num)
theorem B3266531 : Blo 2177435 3266531 := bstep (se 1 (by rfl) ⟨2449898, by rfl⟩ : syracuseStep 3266531 = 4899797) B4899797
theorem B2177687 : Blo 2177435 2177687 := bstep (se 1 (by rfl) ⟨1633265, by rfl⟩ : syracuseStep 2177687 = 3266531) B3266531
theorem B9933317 : Blo 2177435 9933317 := bbase (se 4 (by rfl) ⟨931248, by rfl⟩ : syracuseStep 9933317 = 1862497) (by norm_num)
theorem B6622211 : Blo 2177435 6622211 := bstep (se 1 (by rfl) ⟨4966658, by rfl⟩ : syracuseStep 6622211 = 9933317) B9933317
theorem B4414807 : Blo 2177435 4414807 := bstep (se 1 (by rfl) ⟨3311105, by rfl⟩ : syracuseStep 4414807 = 6622211) B6622211
theorem B23545637 : Blo 2177435 23545637 := bstep (se 4 (by rfl) ⟨2207403, by rfl⟩ : syracuseStep 23545637 = 4414807) B4414807
theorem B15697091 : Blo 2177435 15697091 := bstep (se 1 (by rfl) ⟨11772818, by rfl⟩ : syracuseStep 15697091 = 23545637) B23545637
theorem B10464727 : Blo 2177435 10464727 := bstep (se 1 (by rfl) ⟨7848545, by rfl⟩ : syracuseStep 10464727 = 15697091) B15697091
theorem B13952969 : Blo 2177435 13952969 := bstep (se 2 (by rfl) ⟨5232363, by rfl⟩ : syracuseStep 13952969 = 10464727) B10464727
theorem B9301979 : Blo 2177435 9301979 := bstep (se 1 (by rfl) ⟨6976484, by rfl⟩ : syracuseStep 9301979 = 13952969) B13952969
theorem B6201319 : Blo 2177435 6201319 := bstep (se 1 (by rfl) ⟨4650989, by rfl⟩ : syracuseStep 6201319 = 9301979) B9301979
theorem B8268425 : Blo 2177435 8268425 := bstep (se 2 (by rfl) ⟨3100659, by rfl⟩ : syracuseStep 8268425 = 6201319) B6201319
theorem B5512283 : Blo 2177435 5512283 := bstep (se 1 (by rfl) ⟨4134212, by rfl⟩ : syracuseStep 5512283 = 8268425) B8268425
theorem B3674855 : Blo 2177435 3674855 := bstep (se 1 (by rfl) ⟨2756141, by rfl⟩ : syracuseStep 3674855 = 5512283) B5512283
theorem B2449903 : Blo 2177435 2449903 := bstep (se 1 (by rfl) ⟨1837427, by rfl⟩ : syracuseStep 2449903 = 3674855) B3674855
theorem B3266537 : Blo 2177435 3266537 := bstep (se 2 (by rfl) ⟨1224951, by rfl⟩ : syracuseStep 3266537 = 2449903) B2449903
theorem B2177691 : Blo 2177435 2177691 := bstep (se 1 (by rfl) ⟨1633268, by rfl⟩ : syracuseStep 2177691 = 3266537) B3266537
theorem B18603989 : Blo 2177435 18603989 := bbase (se 7 (by rfl) ⟨218015, by rfl⟩ : syracuseStep 18603989 = 436031) (by norm_num)
theorem B12402659 : Blo 2177435 12402659 := bstep (se 1 (by rfl) ⟨9301994, by rfl⟩ : syracuseStep 12402659 = 18603989) B18603989
theorem B8268439 : Blo 2177435 8268439 := bstep (se 1 (by rfl) ⟨6201329, by rfl⟩ : syracuseStep 8268439 = 12402659) B12402659
theorem B11024585 : Blo 2177435 11024585 := bstep (se 2 (by rfl) ⟨4134219, by rfl⟩ : syracuseStep 11024585 = 8268439) B8268439
theorem B7349723 : Blo 2177435 7349723 := bstep (se 1 (by rfl) ⟨5512292, by rfl⟩ : syracuseStep 7349723 = 11024585) B11024585
theorem B4899815 : Blo 2177435 4899815 := bstep (se 1 (by rfl) ⟨3674861, by rfl⟩ : syracuseStep 4899815 = 7349723) B7349723
theorem B3266543 : Blo 2177435 3266543 := bstep (se 1 (by rfl) ⟨2449907, by rfl⟩ : syracuseStep 3266543 = 4899815) B4899815
theorem B2177695 : Blo 2177435 2177695 := bstep (se 1 (by rfl) ⟨1633271, by rfl⟩ : syracuseStep 2177695 = 3266543) B3266543
theorem B3266549 : Blo 2177435 3266549 := bbase (se 5 (by rfl) ⟨153119, by rfl⟩ : syracuseStep 3266549 = 306239) (by norm_num)
theorem B2177699 : Blo 2177435 2177699 := bstep (se 1 (by rfl) ⟨1633274, by rfl⟩ : syracuseStep 2177699 = 3266549) B3266549
theorem B2943221 : Blo 2177435 2943221 := bbase (se 5 (by rfl) ⟨137963, by rfl⟩ : syracuseStep 2943221 = 275927) (by norm_num)
theorem B7848589 : Blo 2177435 7848589 := bstep (se 3 (by rfl) ⟨1471610, by rfl⟩ : syracuseStep 7848589 = 2943221) B2943221
theorem B10464785 : Blo 2177435 10464785 := bstep (se 2 (by rfl) ⟨3924294, by rfl⟩ : syracuseStep 10464785 = 7848589) B7848589
theorem B6976523 : Blo 2177435 6976523 := bstep (se 1 (by rfl) ⟨5232392, by rfl⟩ : syracuseStep 6976523 = 10464785) B10464785
theorem B4651015 : Blo 2177435 4651015 := bstep (se 1 (by rfl) ⟨3488261, by rfl⟩ : syracuseStep 4651015 = 6976523) B6976523
theorem B6201353 : Blo 2177435 6201353 := bstep (se 2 (by rfl) ⟨2325507, by rfl⟩ : syracuseStep 6201353 = 4651015) B4651015
theorem B4134235 : Blo 2177435 4134235 := bstep (se 1 (by rfl) ⟨3100676, by rfl⟩ : syracuseStep 4134235 = 6201353) B6201353
theorem B5512313 : Blo 2177435 5512313 := bstep (se 2 (by rfl) ⟨2067117, by rfl⟩ : syracuseStep 5512313 = 4134235) B4134235
theorem B3674875 : Blo 2177435 3674875 := bstep (se 1 (by rfl) ⟨2756156, by rfl⟩ : syracuseStep 3674875 = 5512313) B5512313
theorem B4899833 : Blo 2177435 4899833 := bstep (se 2 (by rfl) ⟨1837437, by rfl⟩ : syracuseStep 4899833 = 3674875) B3674875
theorem B3266555 : Blo 2177435 3266555 := bstep (se 1 (by rfl) ⟨2449916, by rfl⟩ : syracuseStep 3266555 = 4899833) B4899833
theorem B2177703 : Blo 2177435 2177703 := bstep (se 1 (by rfl) ⟨1633277, by rfl⟩ : syracuseStep 2177703 = 3266555) B3266555
theorem B2449921 : Blo 2177435 2449921 := bbase (se 2 (by rfl) ⟨918720, by rfl⟩ : syracuseStep 2449921 = 1837441) (by norm_num)
theorem B3266561 : Blo 2177435 3266561 := bstep (se 2 (by rfl) ⟨1224960, by rfl⟩ : syracuseStep 3266561 = 2449921) B2449921
theorem B2177707 : Blo 2177435 2177707 := bstep (se 1 (by rfl) ⟨1633280, by rfl⟩ : syracuseStep 2177707 = 3266561) B3266561
theorem B5512333 : Blo 2177435 5512333 := bbase (se 3 (by rfl) ⟨1033562, by rfl⟩ : syracuseStep 5512333 = 2067125) (by norm_num)
theorem B7349777 : Blo 2177435 7349777 := bstep (se 2 (by rfl) ⟨2756166, by rfl⟩ : syracuseStep 7349777 = 5512333) B5512333
theorem B4899851 : Blo 2177435 4899851 := bstep (se 1 (by rfl) ⟨3674888, by rfl⟩ : syracuseStep 4899851 = 7349777) B7349777
theorem B3266567 : Blo 2177435 3266567 := bstep (se 1 (by rfl) ⟨2449925, by rfl⟩ : syracuseStep 3266567 = 4899851) B4899851
theorem B2177711 : Blo 2177435 2177711 := bstep (se 1 (by rfl) ⟨1633283, by rfl⟩ : syracuseStep 2177711 = 3266567) B3266567
theorem B3266573 : Blo 2177435 3266573 := bbase (se 3 (by rfl) ⟨612482, by rfl⟩ : syracuseStep 3266573 = 1224965) (by norm_num)
theorem B2177715 : Blo 2177435 2177715 := bstep (se 1 (by rfl) ⟨1633286, by rfl⟩ : syracuseStep 2177715 = 3266573) B3266573
theorem B4899869 : Blo 2177435 4899869 := bbase (se 3 (by rfl) ⟨918725, by rfl⟩ : syracuseStep 4899869 = 1837451) (by norm_num)
theorem B3266579 : Blo 2177435 3266579 := bstep (se 1 (by rfl) ⟨2449934, by rfl⟩ : syracuseStep 3266579 = 4899869) B4899869
theorem B2177719 : Blo 2177435 2177719 := bstep (se 1 (by rfl) ⟨1633289, by rfl⟩ : syracuseStep 2177719 = 3266579) B3266579
theorem B3674909 : Blo 2177435 3674909 := bbase (se 3 (by rfl) ⟨689045, by rfl⟩ : syracuseStep 3674909 = 1378091) (by norm_num)
theorem B2449939 : Blo 2177435 2449939 := bstep (se 1 (by rfl) ⟨1837454, by rfl⟩ : syracuseStep 2449939 = 3674909) B3674909
theorem B3266585 : Blo 2177435 3266585 := bstep (se 2 (by rfl) ⟨1224969, by rfl⟩ : syracuseStep 3266585 = 2449939) B2449939
theorem B2177723 : Blo 2177435 2177723 := bstep (se 1 (by rfl) ⟨1633292, by rfl⟩ : syracuseStep 2177723 = 3266585) B3266585
theorem B2943253 : Blo 2177435 2943253 := bbase (se 6 (by rfl) ⟨68982, by rfl⟩ : syracuseStep 2943253 = 137965) (by norm_num)
theorem B3924337 : Blo 2177435 3924337 := bstep (se 2 (by rfl) ⟨1471626, by rfl⟩ : syracuseStep 3924337 = 2943253) B2943253
theorem B5232449 : Blo 2177435 5232449 := bstep (se 2 (by rfl) ⟨1962168, by rfl⟩ : syracuseStep 5232449 = 3924337) B3924337
theorem B13953197 : Blo 2177435 13953197 := bstep (se 3 (by rfl) ⟨2616224, by rfl⟩ : syracuseStep 13953197 = 5232449) B5232449
theorem B9302131 : Blo 2177435 9302131 := bstep (se 1 (by rfl) ⟨6976598, by rfl⟩ : syracuseStep 9302131 = 13953197) B13953197
theorem B12402841 : Blo 2177435 12402841 := bstep (se 2 (by rfl) ⟨4651065, by rfl⟩ : syracuseStep 12402841 = 9302131) B9302131
theorem B16537121 : Blo 2177435 16537121 := bstep (se 2 (by rfl) ⟨6201420, by rfl⟩ : syracuseStep 16537121 = 12402841) B12402841
theorem B11024747 : Blo 2177435 11024747 := bstep (se 1 (by rfl) ⟨8268560, by rfl⟩ : syracuseStep 11024747 = 16537121) B16537121
theorem B7349831 : Blo 2177435 7349831 := bstep (se 1 (by rfl) ⟨5512373, by rfl⟩ : syracuseStep 7349831 = 11024747) B11024747
theorem B4899887 : Blo 2177435 4899887 := bstep (se 1 (by rfl) ⟨3674915, by rfl⟩ : syracuseStep 4899887 = 7349831) B7349831
theorem B3266591 : Blo 2177435 3266591 := bstep (se 1 (by rfl) ⟨2449943, by rfl⟩ : syracuseStep 3266591 = 4899887) B4899887
theorem B2177727 : Blo 2177435 2177727 := bstep (se 1 (by rfl) ⟨1633295, by rfl⟩ : syracuseStep 2177727 = 3266591) B3266591
theorem B3266597 : Blo 2177435 3266597 := bbase (se 4 (by rfl) ⟨306243, by rfl⟩ : syracuseStep 3266597 = 612487) (by norm_num)
theorem B2177731 : Blo 2177435 2177731 := bstep (se 1 (by rfl) ⟨1633298, by rfl⟩ : syracuseStep 2177731 = 3266597) B3266597
theorem B2756197 : Blo 2177435 2756197 := bbase (se 4 (by rfl) ⟨258393, by rfl⟩ : syracuseStep 2756197 = 516787) (by norm_num)
theorem B3674929 : Blo 2177435 3674929 := bstep (se 2 (by rfl) ⟨1378098, by rfl⟩ : syracuseStep 3674929 = 2756197) B2756197
theorem B4899905 : Blo 2177435 4899905 := bstep (se 2 (by rfl) ⟨1837464, by rfl⟩ : syracuseStep 4899905 = 3674929) B3674929
theorem B3266603 : Blo 2177435 3266603 := bstep (se 1 (by rfl) ⟨2449952, by rfl⟩ : syracuseStep 3266603 = 4899905) B4899905
theorem B2177735 : Blo 2177435 2177735 := bstep (se 1 (by rfl) ⟨1633301, by rfl⟩ : syracuseStep 2177735 = 3266603) B3266603
theorem B2449957 : Blo 2177435 2449957 := bbase (se 4 (by rfl) ⟨229683, by rfl⟩ : syracuseStep 2449957 = 459367) (by norm_num)
theorem B3266609 : Blo 2177435 3266609 := bstep (se 2 (by rfl) ⟨1224978, by rfl⟩ : syracuseStep 3266609 = 2449957) B2449957
theorem B2177739 : Blo 2177435 2177739 := bstep (se 1 (by rfl) ⟨1633304, by rfl⟩ : syracuseStep 2177739 = 3266609) B3266609
theorem B2483389 : Blo 2177435 2483389 := bbase (se 3 (by rfl) ⟨465635, by rfl⟩ : syracuseStep 2483389 = 931271) (by norm_num)
theorem B3311185 : Blo 2177435 3311185 := bstep (se 2 (by rfl) ⟨1241694, by rfl⟩ : syracuseStep 3311185 = 2483389) B2483389
theorem B4414913 : Blo 2177435 4414913 := bstep (se 2 (by rfl) ⟨1655592, by rfl⟩ : syracuseStep 4414913 = 3311185) B3311185
theorem B2943275 : Blo 2177435 2943275 := bstep (se 1 (by rfl) ⟨2207456, by rfl⟩ : syracuseStep 2943275 = 4414913) B4414913
theorem B7848733 : Blo 2177435 7848733 := bstep (se 3 (by rfl) ⟨1471637, by rfl⟩ : syracuseStep 7848733 = 2943275) B2943275
theorem B10464977 : Blo 2177435 10464977 := bstep (se 2 (by rfl) ⟨3924366, by rfl⟩ : syracuseStep 10464977 = 7848733) B7848733
theorem B6976651 : Blo 2177435 6976651 := bstep (se 1 (by rfl) ⟨5232488, by rfl⟩ : syracuseStep 6976651 = 10464977) B10464977
theorem B9302201 : Blo 2177435 9302201 := bstep (se 2 (by rfl) ⟨3488325, by rfl⟩ : syracuseStep 9302201 = 6976651) B6976651
theorem B6201467 : Blo 2177435 6201467 := bstep (se 1 (by rfl) ⟨4651100, by rfl⟩ : syracuseStep 6201467 = 9302201) B9302201
theorem B4134311 : Blo 2177435 4134311 := bstep (se 1 (by rfl) ⟨3100733, by rfl⟩ : syracuseStep 4134311 = 6201467) B6201467
theorem B2756207 : Blo 2177435 2756207 := bstep (se 1 (by rfl) ⟨2067155, by rfl⟩ : syracuseStep 2756207 = 4134311) B4134311
theorem B7349885 : Blo 2177435 7349885 := bstep (se 3 (by rfl) ⟨1378103, by rfl⟩ : syracuseStep 7349885 = 2756207) B2756207
theorem B4899923 : Blo 2177435 4899923 := bstep (se 1 (by rfl) ⟨3674942, by rfl⟩ : syracuseStep 4899923 = 7349885) B7349885
theorem B3266615 : Blo 2177435 3266615 := bstep (se 1 (by rfl) ⟨2449961, by rfl⟩ : syracuseStep 3266615 = 4899923) B4899923
theorem B2177743 : Blo 2177435 2177743 := bstep (se 1 (by rfl) ⟨1633307, by rfl⟩ : syracuseStep 2177743 = 3266615) B3266615
theorem B3266621 : Blo 2177435 3266621 := bbase (se 3 (by rfl) ⟨612491, by rfl⟩ : syracuseStep 3266621 = 1224983) (by norm_num)
theorem B2177747 : Blo 2177435 2177747 := bstep (se 1 (by rfl) ⟨1633310, by rfl⟩ : syracuseStep 2177747 = 3266621) B3266621
theorem B4899941 : Blo 2177435 4899941 := bbase (se 4 (by rfl) ⟨459369, by rfl⟩ : syracuseStep 4899941 = 918739) (by norm_num)
theorem B3266627 : Blo 2177435 3266627 := bstep (se 1 (by rfl) ⟨2449970, by rfl⟩ : syracuseStep 3266627 = 4899941) B4899941
theorem B2177751 : Blo 2177435 2177751 := bstep (se 1 (by rfl) ⟨1633313, by rfl⟩ : syracuseStep 2177751 = 3266627) B3266627
theorem B5512445 : Blo 2177435 5512445 := bbase (se 3 (by rfl) ⟨1033583, by rfl⟩ : syracuseStep 5512445 = 2067167) (by norm_num)
theorem B3674963 : Blo 2177435 3674963 := bstep (se 1 (by rfl) ⟨2756222, by rfl⟩ : syracuseStep 3674963 = 5512445) B5512445
theorem B2449975 : Blo 2177435 2449975 := bstep (se 1 (by rfl) ⟨1837481, by rfl⟩ : syracuseStep 2449975 = 3674963) B3674963
theorem B3266633 : Blo 2177435 3266633 := bstep (se 2 (by rfl) ⟨1224987, by rfl⟩ : syracuseStep 3266633 = 2449975) B2449975
theorem B2177755 : Blo 2177435 2177755 := bstep (se 1 (by rfl) ⟨1633316, by rfl⟩ : syracuseStep 2177755 = 3266633) B3266633
theorem B4134341 : Blo 2177435 4134341 := bbase (se 4 (by rfl) ⟨387594, by rfl⟩ : syracuseStep 4134341 = 775189) (by norm_num)
theorem B11024909 : Blo 2177435 11024909 := bstep (se 3 (by rfl) ⟨2067170, by rfl⟩ : syracuseStep 11024909 = 4134341) B4134341
theorem B7349939 : Blo 2177435 7349939 := bstep (se 1 (by rfl) ⟨5512454, by rfl⟩ : syracuseStep 7349939 = 11024909) B11024909
theorem B4899959 : Blo 2177435 4899959 := bstep (se 1 (by rfl) ⟨3674969, by rfl⟩ : syracuseStep 4899959 = 7349939) B7349939
theorem B3266639 : Blo 2177435 3266639 := bstep (se 1 (by rfl) ⟨2449979, by rfl⟩ : syracuseStep 3266639 = 4899959) B4899959
theorem B2177759 : Blo 2177435 2177759 := bstep (se 1 (by rfl) ⟨1633319, by rfl⟩ : syracuseStep 2177759 = 3266639) B3266639
theorem B3266645 : Blo 2177435 3266645 := bbase (se 8 (by rfl) ⟨19140, by rfl⟩ : syracuseStep 3266645 = 38281) (by norm_num)
theorem B2177763 : Blo 2177435 2177763 := bstep (se 1 (by rfl) ⟨1633322, by rfl⟩ : syracuseStep 2177763 = 3266645) B3266645
theorem B2357305 : Blo 2177435 2357305 := bbase (se 2 (by rfl) ⟨883989, by rfl⟩ : syracuseStep 2357305 = 1767979) (by norm_num)
theorem B12572293 : Blo 2177435 12572293 := bstep (se 4 (by rfl) ⟨1178652, by rfl⟩ : syracuseStep 12572293 = 2357305) B2357305
theorem B16763057 : Blo 2177435 16763057 := bstep (se 2 (by rfl) ⟨6286146, by rfl⟩ : syracuseStep 16763057 = 12572293) B12572293
theorem B11175371 : Blo 2177435 11175371 := bstep (se 1 (by rfl) ⟨8381528, by rfl⟩ : syracuseStep 11175371 = 16763057) B16763057
theorem B7450247 : Blo 2177435 7450247 := bstep (se 1 (by rfl) ⟨5587685, by rfl⟩ : syracuseStep 7450247 = 11175371) B11175371
theorem B4966831 : Blo 2177435 4966831 := bstep (se 1 (by rfl) ⟨3725123, by rfl⟩ : syracuseStep 4966831 = 7450247) B7450247
theorem B6622441 : Blo 2177435 6622441 := bstep (se 2 (by rfl) ⟨2483415, by rfl⟩ : syracuseStep 6622441 = 4966831) B4966831
theorem B35319685 : Blo 2177435 35319685 := bstep (se 4 (by rfl) ⟨3311220, by rfl⟩ : syracuseStep 35319685 = 6622441) B6622441
theorem B47092913 : Blo 2177435 47092913 := bstep (se 2 (by rfl) ⟨17659842, by rfl⟩ : syracuseStep 47092913 = 35319685) B35319685
theorem B31395275 : Blo 2177435 31395275 := bstep (se 1 (by rfl) ⟨23546456, by rfl⟩ : syracuseStep 31395275 = 47092913) B47092913
theorem B20930183 : Blo 2177435 20930183 := bstep (se 1 (by rfl) ⟨15697637, by rfl⟩ : syracuseStep 20930183 = 31395275) B31395275
theorem B13953455 : Blo 2177435 13953455 := bstep (se 1 (by rfl) ⟨10465091, by rfl⟩ : syracuseStep 13953455 = 20930183) B20930183
theorem B9302303 : Blo 2177435 9302303 := bstep (se 1 (by rfl) ⟨6976727, by rfl⟩ : syracuseStep 9302303 = 13953455) B13953455
theorem B6201535 : Blo 2177435 6201535 := bstep (se 1 (by rfl) ⟨4651151, by rfl⟩ : syracuseStep 6201535 = 9302303) B9302303
theorem B8268713 : Blo 2177435 8268713 := bstep (se 2 (by rfl) ⟨3100767, by rfl⟩ : syracuseStep 8268713 = 6201535) B6201535
theorem B5512475 : Blo 2177435 5512475 := bstep (se 1 (by rfl) ⟨4134356, by rfl⟩ : syracuseStep 5512475 = 8268713) B8268713
theorem B3674983 : Blo 2177435 3674983 := bstep (se 1 (by rfl) ⟨2756237, by rfl⟩ : syracuseStep 3674983 = 5512475) B5512475
theorem B4899977 : Blo 2177435 4899977 := bstep (se 2 (by rfl) ⟨1837491, by rfl⟩ : syracuseStep 4899977 = 3674983) B3674983
theorem B3266651 : Blo 2177435 3266651 := bstep (se 1 (by rfl) ⟨2449988, by rfl⟩ : syracuseStep 3266651 = 4899977) B4899977
theorem B2177767 : Blo 2177435 2177767 := bstep (se 1 (by rfl) ⟨1633325, by rfl⟩ : syracuseStep 2177767 = 3266651) B3266651
theorem B2449993 : Blo 2177435 2449993 := bbase (se 2 (by rfl) ⟨918747, by rfl⟩ : syracuseStep 2449993 = 1837495) (by norm_num)
theorem B3266657 : Blo 2177435 3266657 := bstep (se 2 (by rfl) ⟨1224996, by rfl⟩ : syracuseStep 3266657 = 2449993) B2449993
theorem B2177771 : Blo 2177435 2177771 := bstep (se 1 (by rfl) ⟨1633328, by rfl⟩ : syracuseStep 2177771 = 3266657) B3266657
theorem B2793853 : Blo 2177435 2793853 := bbase (se 3 (by rfl) ⟨523847, by rfl⟩ : syracuseStep 2793853 = 1047695) (by norm_num)
theorem B3725137 : Blo 2177435 3725137 := bstep (se 2 (by rfl) ⟨1396926, by rfl⟩ : syracuseStep 3725137 = 2793853) B2793853
theorem B4966849 : Blo 2177435 4966849 := bstep (se 2 (by rfl) ⟨1862568, by rfl⟩ : syracuseStep 4966849 = 3725137) B3725137
theorem B26489861 : Blo 2177435 26489861 := bstep (se 4 (by rfl) ⟨2483424, by rfl⟩ : syracuseStep 26489861 = 4966849) B4966849
theorem B17659907 : Blo 2177435 17659907 := bstep (se 1 (by rfl) ⟨13244930, by rfl⟩ : syracuseStep 17659907 = 26489861) B26489861
theorem B11773271 : Blo 2177435 11773271 := bstep (se 1 (by rfl) ⟨8829953, by rfl⟩ : syracuseStep 11773271 = 17659907) B17659907
theorem B7848847 : Blo 2177435 7848847 := bstep (se 1 (by rfl) ⟨5886635, by rfl⟩ : syracuseStep 7848847 = 11773271) B11773271
theorem B10465129 : Blo 2177435 10465129 := bstep (se 2 (by rfl) ⟨3924423, by rfl⟩ : syracuseStep 10465129 = 7848847) B7848847
theorem B13953505 : Blo 2177435 13953505 := bstep (se 2 (by rfl) ⟨5232564, by rfl⟩ : syracuseStep 13953505 = 10465129) B10465129
theorem B18604673 : Blo 2177435 18604673 := bstep (se 2 (by rfl) ⟨6976752, by rfl⟩ : syracuseStep 18604673 = 13953505) B13953505
theorem B12403115 : Blo 2177435 12403115 := bstep (se 1 (by rfl) ⟨9302336, by rfl⟩ : syracuseStep 12403115 = 18604673) B18604673
theorem B8268743 : Blo 2177435 8268743 := bstep (se 1 (by rfl) ⟨6201557, by rfl⟩ : syracuseStep 8268743 = 12403115) B12403115
theorem B5512495 : Blo 2177435 5512495 := bstep (se 1 (by rfl) ⟨4134371, by rfl⟩ : syracuseStep 5512495 = 8268743) B8268743
theorem B7349993 : Blo 2177435 7349993 := bstep (se 2 (by rfl) ⟨2756247, by rfl⟩ : syracuseStep 7349993 = 5512495) B5512495
theorem B4899995 : Blo 2177435 4899995 := bstep (se 1 (by rfl) ⟨3674996, by rfl⟩ : syracuseStep 4899995 = 7349993) B7349993
theorem B3266663 : Blo 2177435 3266663 := bstep (se 1 (by rfl) ⟨2449997, by rfl⟩ : syracuseStep 3266663 = 4899995) B4899995
theorem B2177775 : Blo 2177435 2177775 := bstep (se 1 (by rfl) ⟨1633331, by rfl⟩ : syracuseStep 2177775 = 3266663) B3266663
theorem B3266669 : Blo 2177435 3266669 := bbase (se 3 (by rfl) ⟨612500, by rfl⟩ : syracuseStep 3266669 = 1225001) (by norm_num)
theorem B2177779 : Blo 2177435 2177779 := bstep (se 1 (by rfl) ⟨1633334, by rfl⟩ : syracuseStep 2177779 = 3266669) B3266669
theorem B4900013 : Blo 2177435 4900013 := bbase (se 3 (by rfl) ⟨918752, by rfl⟩ : syracuseStep 4900013 = 1837505) (by norm_num)
theorem B3266675 : Blo 2177435 3266675 := bstep (se 1 (by rfl) ⟨2450006, by rfl⟩ : syracuseStep 3266675 = 4900013) B4900013
theorem B2177783 : Blo 2177435 2177783 := bstep (se 1 (by rfl) ⟨1633337, by rfl⟩ : syracuseStep 2177783 = 3266675) B3266675
theorem B2762029 : Blo 2177435 2762029 := bbase (se 3 (by rfl) ⟨517880, by rfl⟩ : syracuseStep 2762029 = 1035761) (by norm_num)
theorem B14730821 : Blo 2177435 14730821 := bstep (se 4 (by rfl) ⟨1381014, by rfl⟩ : syracuseStep 14730821 = 2762029) B2762029
theorem B9820547 : Blo 2177435 9820547 := bstep (se 1 (by rfl) ⟨7365410, by rfl⟩ : syracuseStep 9820547 = 14730821) B14730821
theorem B6547031 : Blo 2177435 6547031 := bstep (se 1 (by rfl) ⟨4910273, by rfl⟩ : syracuseStep 6547031 = 9820547) B9820547
theorem B4364687 : Blo 2177435 4364687 := bstep (se 1 (by rfl) ⟨3273515, by rfl⟩ : syracuseStep 4364687 = 6547031) B6547031
theorem B2909791 : Blo 2177435 2909791 := bstep (se 1 (by rfl) ⟨2182343, by rfl⟩ : syracuseStep 2909791 = 4364687) B4364687
theorem B3879721 : Blo 2177435 3879721 := bstep (se 2 (by rfl) ⟨1454895, by rfl⟩ : syracuseStep 3879721 = 2909791) B2909791
theorem B20691845 : Blo 2177435 20691845 := bstep (se 4 (by rfl) ⟨1939860, by rfl⟩ : syracuseStep 20691845 = 3879721) B3879721
theorem B13794563 : Blo 2177435 13794563 := bstep (se 1 (by rfl) ⟨10345922, by rfl⟩ : syracuseStep 13794563 = 20691845) B20691845
theorem B36785501 : Blo 2177435 36785501 := bstep (se 3 (by rfl) ⟨6897281, by rfl⟩ : syracuseStep 36785501 = 13794563) B13794563
theorem B24523667 : Blo 2177435 24523667 := bstep (se 1 (by rfl) ⟨18392750, by rfl⟩ : syracuseStep 24523667 = 36785501) B36785501
theorem B16349111 : Blo 2177435 16349111 := bstep (se 1 (by rfl) ⟨12261833, by rfl⟩ : syracuseStep 16349111 = 24523667) B24523667
theorem B10899407 : Blo 2177435 10899407 := bstep (se 1 (by rfl) ⟨8174555, by rfl⟩ : syracuseStep 10899407 = 16349111) B16349111
theorem B7266271 : Blo 2177435 7266271 := bstep (se 1 (by rfl) ⟨5449703, by rfl⟩ : syracuseStep 7266271 = 10899407) B10899407
theorem B9688361 : Blo 2177435 9688361 := bstep (se 2 (by rfl) ⟨3633135, by rfl⟩ : syracuseStep 9688361 = 7266271) B7266271
theorem B25835629 : Blo 2177435 25835629 := bstep (se 3 (by rfl) ⟨4844180, by rfl⟩ : syracuseStep 25835629 = 9688361) B9688361
theorem B551160085 : Blo 2177435 551160085 := bstep (se 6 (by rfl) ⟨12917814, by rfl⟩ : syracuseStep 551160085 = 25835629) B25835629
theorem B734880113 : Blo 2177435 734880113 := bstep (se 2 (by rfl) ⟨275580042, by rfl⟩ : syracuseStep 734880113 = 551160085) B551160085
theorem B489920075 : Blo 2177435 489920075 := bstep (se 1 (by rfl) ⟨367440056, by rfl⟩ : syracuseStep 489920075 = 734880113) B734880113
theorem B326613383 : Blo 2177435 326613383 := bstep (se 1 (by rfl) ⟨244960037, by rfl⟩ : syracuseStep 326613383 = 489920075) B489920075
theorem B217742255 : Blo 2177435 217742255 := bstep (se 1 (by rfl) ⟨163306691, by rfl⟩ : syracuseStep 217742255 = 326613383) B326613383
theorem B145161503 : Blo 2177435 145161503 := bstep (se 1 (by rfl) ⟨108871127, by rfl⟩ : syracuseStep 145161503 = 217742255) B217742255
theorem B96774335 : Blo 2177435 96774335 := bstep (se 1 (by rfl) ⟨72580751, by rfl⟩ : syracuseStep 96774335 = 145161503) B145161503
theorem B64516223 : Blo 2177435 64516223 := bstep (se 1 (by rfl) ⟨48387167, by rfl⟩ : syracuseStep 64516223 = 96774335) B96774335
theorem B172043261 : Blo 2177435 172043261 := bstep (se 3 (by rfl) ⟨32258111, by rfl⟩ : syracuseStep 172043261 = 64516223) B64516223
theorem B114695507 : Blo 2177435 114695507 := bstep (se 1 (by rfl) ⟨86021630, by rfl⟩ : syracuseStep 114695507 = 172043261) B172043261
theorem B76463671 : Blo 2177435 76463671 := bstep (se 1 (by rfl) ⟨57347753, by rfl⟩ : syracuseStep 76463671 = 114695507) B114695507
theorem B101951561 : Blo 2177435 101951561 := bstep (se 2 (by rfl) ⟨38231835, by rfl⟩ : syracuseStep 101951561 = 76463671) B76463671
theorem B67967707 : Blo 2177435 67967707 := bstep (se 1 (by rfl) ⟨50975780, by rfl⟩ : syracuseStep 67967707 = 101951561) B101951561
theorem B90623609 : Blo 2177435 90623609 := bstep (se 2 (by rfl) ⟨33983853, by rfl⟩ : syracuseStep 90623609 = 67967707) B67967707
theorem B60415739 : Blo 2177435 60415739 := bstep (se 1 (by rfl) ⟨45311804, by rfl⟩ : syracuseStep 60415739 = 90623609) B90623609
theorem B40277159 : Blo 2177435 40277159 := bstep (se 1 (by rfl) ⟨30207869, by rfl⟩ : syracuseStep 40277159 = 60415739) B60415739
theorem B26851439 : Blo 2177435 26851439 := bstep (se 1 (by rfl) ⟨20138579, by rfl⟩ : syracuseStep 26851439 = 40277159) B40277159
theorem B71603837 : Blo 2177435 71603837 := bstep (se 3 (by rfl) ⟨13425719, by rfl⟩ : syracuseStep 71603837 = 26851439) B26851439
theorem B47735891 : Blo 2177435 47735891 := bstep (se 1 (by rfl) ⟨35801918, by rfl⟩ : syracuseStep 47735891 = 71603837) B71603837
theorem B31823927 : Blo 2177435 31823927 := bstep (se 1 (by rfl) ⟨23867945, by rfl⟩ : syracuseStep 31823927 = 47735891) B47735891
theorem B21215951 : Blo 2177435 21215951 := bstep (se 1 (by rfl) ⟨15911963, by rfl⟩ : syracuseStep 21215951 = 31823927) B31823927
theorem B14143967 : Blo 2177435 14143967 := bstep (se 1 (by rfl) ⟨10607975, by rfl⟩ : syracuseStep 14143967 = 21215951) B21215951
theorem B9429311 : Blo 2177435 9429311 := bstep (se 1 (by rfl) ⟨7071983, by rfl⟩ : syracuseStep 9429311 = 14143967) B14143967
theorem B25144829 : Blo 2177435 25144829 := bstep (se 3 (by rfl) ⟨4714655, by rfl⟩ : syracuseStep 25144829 = 9429311) B9429311
theorem B16763219 : Blo 2177435 16763219 := bstep (se 1 (by rfl) ⟨12572414, by rfl⟩ : syracuseStep 16763219 = 25144829) B25144829
theorem B11175479 : Blo 2177435 11175479 := bstep (se 1 (by rfl) ⟨8381609, by rfl⟩ : syracuseStep 11175479 = 16763219) B16763219
theorem B7450319 : Blo 2177435 7450319 := bstep (se 1 (by rfl) ⟨5587739, by rfl⟩ : syracuseStep 7450319 = 11175479) B11175479
theorem B4966879 : Blo 2177435 4966879 := bstep (se 1 (by rfl) ⟨3725159, by rfl⟩ : syracuseStep 4966879 = 7450319) B7450319
theorem B6622505 : Blo 2177435 6622505 := bstep (se 2 (by rfl) ⟨2483439, by rfl⟩ : syracuseStep 6622505 = 4966879) B4966879
theorem B4415003 : Blo 2177435 4415003 := bstep (se 1 (by rfl) ⟨3311252, by rfl⟩ : syracuseStep 4415003 = 6622505) B6622505
theorem B2943335 : Blo 2177435 2943335 := bstep (se 1 (by rfl) ⟨2207501, by rfl⟩ : syracuseStep 2943335 = 4415003) B4415003
theorem B7848893 : Blo 2177435 7848893 := bstep (se 3 (by rfl) ⟨1471667, by rfl⟩ : syracuseStep 7848893 = 2943335) B2943335
theorem B5232595 : Blo 2177435 5232595 := bstep (se 1 (by rfl) ⟨3924446, by rfl⟩ : syracuseStep 5232595 = 7848893) B7848893
theorem B6976793 : Blo 2177435 6976793 := bstep (se 2 (by rfl) ⟨2616297, by rfl⟩ : syracuseStep 6976793 = 5232595) B5232595
theorem B4651195 : Blo 2177435 4651195 := bstep (se 1 (by rfl) ⟨3488396, by rfl⟩ : syracuseStep 4651195 = 6976793) B6976793
theorem B6201593 : Blo 2177435 6201593 := bstep (se 2 (by rfl) ⟨2325597, by rfl⟩ : syracuseStep 6201593 = 4651195) B4651195
theorem B4134395 : Blo 2177435 4134395 := bstep (se 1 (by rfl) ⟨3100796, by rfl⟩ : syracuseStep 4134395 = 6201593) B6201593
theorem B2756263 : Blo 2177435 2756263 := bstep (se 1 (by rfl) ⟨2067197, by rfl⟩ : syracuseStep 2756263 = 4134395) B4134395
theorem B3675017 : Blo 2177435 3675017 := bstep (se 2 (by rfl) ⟨1378131, by rfl⟩ : syracuseStep 3675017 = 2756263) B2756263
theorem B2450011 : Blo 2177435 2450011 := bstep (se 1 (by rfl) ⟨1837508, by rfl⟩ : syracuseStep 2450011 = 3675017) B3675017
theorem B3266681 : Blo 2177435 3266681 := bstep (se 2 (by rfl) ⟨1225005, by rfl⟩ : syracuseStep 3266681 = 2450011) B2450011
theorem B2177787 : Blo 2177435 2177787 := bstep (se 1 (by rfl) ⟨1633340, by rfl⟩ : syracuseStep 2177787 = 3266681) B3266681
theorem B10465205 : Blo 2177435 10465205 := bbase (se 5 (by rfl) ⟨490556, by rfl⟩ : syracuseStep 10465205 = 981113) (by norm_num)
theorem B27907213 : Blo 2177435 27907213 := bstep (se 3 (by rfl) ⟨5232602, by rfl⟩ : syracuseStep 27907213 = 10465205) B10465205
theorem B37209617 : Blo 2177435 37209617 := bstep (se 2 (by rfl) ⟨13953606, by rfl⟩ : syracuseStep 37209617 = 27907213) B27907213
theorem B24806411 : Blo 2177435 24806411 := bstep (se 1 (by rfl) ⟨18604808, by rfl⟩ : syracuseStep 24806411 = 37209617) B37209617
theorem B16537607 : Blo 2177435 16537607 := bstep (se 1 (by rfl) ⟨12403205, by rfl⟩ : syracuseStep 16537607 = 24806411) B24806411
theorem B11025071 : Blo 2177435 11025071 := bstep (se 1 (by rfl) ⟨8268803, by rfl⟩ : syracuseStep 11025071 = 16537607) B16537607
theorem B7350047 : Blo 2177435 7350047 := bstep (se 1 (by rfl) ⟨5512535, by rfl⟩ : syracuseStep 7350047 = 11025071) B11025071
theorem B4900031 : Blo 2177435 4900031 := bstep (se 1 (by rfl) ⟨3675023, by rfl⟩ : syracuseStep 4900031 = 7350047) B7350047
theorem B3266687 : Blo 2177435 3266687 := bstep (se 1 (by rfl) ⟨2450015, by rfl⟩ : syracuseStep 3266687 = 4900031) B4900031
theorem B2177791 : Blo 2177435 2177791 := bstep (se 1 (by rfl) ⟨1633343, by rfl⟩ : syracuseStep 2177791 = 3266687) B3266687
theorem B3266693 : Blo 2177435 3266693 := bbase (se 4 (by rfl) ⟨306252, by rfl⟩ : syracuseStep 3266693 = 612505) (by norm_num)
theorem B2177795 : Blo 2177435 2177795 := bstep (se 1 (by rfl) ⟨1633346, by rfl⟩ : syracuseStep 2177795 = 3266693) B3266693
theorem B3675037 : Blo 2177435 3675037 := bbase (se 3 (by rfl) ⟨689069, by rfl⟩ : syracuseStep 3675037 = 1378139) (by norm_num)
theorem B4900049 : Blo 2177435 4900049 := bstep (se 2 (by rfl) ⟨1837518, by rfl⟩ : syracuseStep 4900049 = 3675037) B3675037
theorem B3266699 : Blo 2177435 3266699 := bstep (se 1 (by rfl) ⟨2450024, by rfl⟩ : syracuseStep 3266699 = 4900049) B4900049
theorem B2177799 : Blo 2177435 2177799 := bstep (se 1 (by rfl) ⟨1633349, by rfl⟩ : syracuseStep 2177799 = 3266699) B3266699
theorem B2450029 : Blo 2177435 2450029 := bbase (se 3 (by rfl) ⟨459380, by rfl⟩ : syracuseStep 2450029 = 918761) (by norm_num)
theorem B3266705 : Blo 2177435 3266705 := bstep (se 2 (by rfl) ⟨1225014, by rfl⟩ : syracuseStep 3266705 = 2450029) B2450029
theorem B2177803 : Blo 2177435 2177803 := bstep (se 1 (by rfl) ⟨1633352, by rfl⟩ : syracuseStep 2177803 = 3266705) B3266705
theorem B7350101 : Blo 2177435 7350101 := bbase (se 9 (by rfl) ⟨21533, by rfl⟩ : syracuseStep 7350101 = 43067) (by norm_num)
theorem B4900067 : Blo 2177435 4900067 := bstep (se 1 (by rfl) ⟨3675050, by rfl⟩ : syracuseStep 4900067 = 7350101) B7350101
theorem B3266711 : Blo 2177435 3266711 := bstep (se 1 (by rfl) ⟨2450033, by rfl⟩ : syracuseStep 3266711 = 4900067) B4900067
theorem B2177807 : Blo 2177435 2177807 := bstep (se 1 (by rfl) ⟨1633355, by rfl⟩ : syracuseStep 2177807 = 3266711) B3266711
theorem B3266717 : Blo 2177435 3266717 := bbase (se 3 (by rfl) ⟨612509, by rfl⟩ : syracuseStep 3266717 = 1225019) (by norm_num)
theorem B2177811 : Blo 2177435 2177811 := bstep (se 1 (by rfl) ⟨1633358, by rfl⟩ : syracuseStep 2177811 = 3266717) B3266717
theorem B4900085 : Blo 2177435 4900085 := bbase (se 5 (by rfl) ⟨229691, by rfl⟩ : syracuseStep 4900085 = 459383) (by norm_num)
theorem B3266723 : Blo 2177435 3266723 := bstep (se 1 (by rfl) ⟨2450042, by rfl⟩ : syracuseStep 3266723 = 4900085) B4900085
theorem B2177815 : Blo 2177435 2177815 := bstep (se 1 (by rfl) ⟨1633361, by rfl⟩ : syracuseStep 2177815 = 3266723) B3266723
theorem B11175637 : Blo 2177435 11175637 := bbase (se 7 (by rfl) ⟨130964, by rfl⟩ : syracuseStep 11175637 = 261929) (by norm_num)
theorem B14900849 : Blo 2177435 14900849 := bstep (se 2 (by rfl) ⟨5587818, by rfl⟩ : syracuseStep 14900849 = 11175637) B11175637
theorem B9933899 : Blo 2177435 9933899 := bstep (se 1 (by rfl) ⟨7450424, by rfl⟩ : syracuseStep 9933899 = 14900849) B14900849
theorem B26490397 : Blo 2177435 26490397 := bstep (se 3 (by rfl) ⟨4966949, by rfl⟩ : syracuseStep 26490397 = 9933899) B9933899
theorem B35320529 : Blo 2177435 35320529 := bstep (se 2 (by rfl) ⟨13245198, by rfl⟩ : syracuseStep 35320529 = 26490397) B26490397
theorem B23547019 : Blo 2177435 23547019 := bstep (se 1 (by rfl) ⟨17660264, by rfl⟩ : syracuseStep 23547019 = 35320529) B35320529
theorem B31396025 : Blo 2177435 31396025 := bstep (se 2 (by rfl) ⟨11773509, by rfl⟩ : syracuseStep 31396025 = 23547019) B23547019
theorem B20930683 : Blo 2177435 20930683 := bstep (se 1 (by rfl) ⟨15698012, by rfl⟩ : syracuseStep 20930683 = 31396025) B31396025
theorem B27907577 : Blo 2177435 27907577 := bstep (se 2 (by rfl) ⟨10465341, by rfl⟩ : syracuseStep 27907577 = 20930683) B20930683
theorem B18605051 : Blo 2177435 18605051 := bstep (se 1 (by rfl) ⟨13953788, by rfl⟩ : syracuseStep 18605051 = 27907577) B27907577
theorem B12403367 : Blo 2177435 12403367 := bstep (se 1 (by rfl) ⟨9302525, by rfl⟩ : syracuseStep 12403367 = 18605051) B18605051
theorem B8268911 : Blo 2177435 8268911 := bstep (se 1 (by rfl) ⟨6201683, by rfl⟩ : syracuseStep 8268911 = 12403367) B12403367
theorem B5512607 : Blo 2177435 5512607 := bstep (se 1 (by rfl) ⟨4134455, by rfl⟩ : syracuseStep 5512607 = 8268911) B8268911
theorem B3675071 : Blo 2177435 3675071 := bstep (se 1 (by rfl) ⟨2756303, by rfl⟩ : syracuseStep 3675071 = 5512607) B5512607
theorem B2450047 : Blo 2177435 2450047 := bstep (se 1 (by rfl) ⟨1837535, by rfl⟩ : syracuseStep 2450047 = 3675071) B3675071
theorem B3266729 : Blo 2177435 3266729 := bstep (se 2 (by rfl) ⟨1225023, by rfl⟩ : syracuseStep 3266729 = 2450047) B2450047
theorem B2177819 : Blo 2177435 2177819 := bstep (se 1 (by rfl) ⟨1633364, by rfl⟩ : syracuseStep 2177819 = 3266729) B3266729
theorem B6622613 : Blo 2177435 6622613 := bbase (se 6 (by rfl) ⟨155217, by rfl⟩ : syracuseStep 6622613 = 310435) (by norm_num)
theorem B4415075 : Blo 2177435 4415075 := bstep (se 1 (by rfl) ⟨3311306, by rfl⟩ : syracuseStep 4415075 = 6622613) B6622613
theorem B2943383 : Blo 2177435 2943383 := bstep (se 1 (by rfl) ⟨2207537, by rfl⟩ : syracuseStep 2943383 = 4415075) B4415075
theorem B7849021 : Blo 2177435 7849021 := bstep (se 3 (by rfl) ⟨1471691, by rfl⟩ : syracuseStep 7849021 = 2943383) B2943383
theorem B10465361 : Blo 2177435 10465361 := bstep (se 2 (by rfl) ⟨3924510, by rfl⟩ : syracuseStep 10465361 = 7849021) B7849021
theorem B6976907 : Blo 2177435 6976907 := bstep (se 1 (by rfl) ⟨5232680, by rfl⟩ : syracuseStep 6976907 = 10465361) B10465361
theorem B4651271 : Blo 2177435 4651271 := bstep (se 1 (by rfl) ⟨3488453, by rfl⟩ : syracuseStep 4651271 = 6976907) B6976907
theorem B3100847 : Blo 2177435 3100847 := bstep (se 1 (by rfl) ⟨2325635, by rfl⟩ : syracuseStep 3100847 = 4651271) B4651271
theorem B8268925 : Blo 2177435 8268925 := bstep (se 3 (by rfl) ⟨1550423, by rfl⟩ : syracuseStep 8268925 = 3100847) B3100847
theorem B11025233 : Blo 2177435 11025233 := bstep (se 2 (by rfl) ⟨4134462, by rfl⟩ : syracuseStep 11025233 = 8268925) B8268925
theorem B7350155 : Blo 2177435 7350155 := bstep (se 1 (by rfl) ⟨5512616, by rfl⟩ : syracuseStep 7350155 = 11025233) B11025233
theorem B4900103 : Blo 2177435 4900103 := bstep (se 1 (by rfl) ⟨3675077, by rfl⟩ : syracuseStep 4900103 = 7350155) B7350155
theorem B3266735 : Blo 2177435 3266735 := bstep (se 1 (by rfl) ⟨2450051, by rfl⟩ : syracuseStep 3266735 = 4900103) B4900103
theorem B2177823 : Blo 2177435 2177823 := bstep (se 1 (by rfl) ⟨1633367, by rfl⟩ : syracuseStep 2177823 = 3266735) B3266735
theorem B3266741 : Blo 2177435 3266741 := bbase (se 5 (by rfl) ⟨153128, by rfl⟩ : syracuseStep 3266741 = 306257) (by norm_num)
theorem B2177827 : Blo 2177435 2177827 := bstep (se 1 (by rfl) ⟨1633370, by rfl⟩ : syracuseStep 2177827 = 3266741) B3266741
theorem B5512637 : Blo 2177435 5512637 := bbase (se 3 (by rfl) ⟨1033619, by rfl⟩ : syracuseStep 5512637 = 2067239) (by norm_num)
theorem B3675091 : Blo 2177435 3675091 := bstep (se 1 (by rfl) ⟨2756318, by rfl⟩ : syracuseStep 3675091 = 5512637) B5512637
theorem B4900121 : Blo 2177435 4900121 := bstep (se 2 (by rfl) ⟨1837545, by rfl⟩ : syracuseStep 4900121 = 3675091) B3675091
theorem B3266747 : Blo 2177435 3266747 := bstep (se 1 (by rfl) ⟨2450060, by rfl⟩ : syracuseStep 3266747 = 4900121) B4900121
theorem B2177831 : Blo 2177435 2177831 := bstep (se 1 (by rfl) ⟨1633373, by rfl⟩ : syracuseStep 2177831 = 3266747) B3266747
theorem B2450065 : Blo 2177435 2450065 := bbase (se 2 (by rfl) ⟨918774, by rfl⟩ : syracuseStep 2450065 = 1837549) (by norm_num)
theorem B3266753 : Blo 2177435 3266753 := bstep (se 2 (by rfl) ⟨1225032, by rfl⟩ : syracuseStep 3266753 = 2450065) B2450065
theorem B2177835 : Blo 2177435 2177835 := bstep (se 1 (by rfl) ⟨1633376, by rfl⟩ : syracuseStep 2177835 = 3266753) B3266753
theorem B4134493 : Blo 2177435 4134493 := bbase (se 3 (by rfl) ⟨775217, by rfl⟩ : syracuseStep 4134493 = 1550435) (by norm_num)
theorem B5512657 : Blo 2177435 5512657 := bstep (se 2 (by rfl) ⟨2067246, by rfl⟩ : syracuseStep 5512657 = 4134493) B4134493
theorem B7350209 : Blo 2177435 7350209 := bstep (se 2 (by rfl) ⟨2756328, by rfl⟩ : syracuseStep 7350209 = 5512657) B5512657
theorem B4900139 : Blo 2177435 4900139 := bstep (se 1 (by rfl) ⟨3675104, by rfl⟩ : syracuseStep 4900139 = 7350209) B7350209
theorem B3266759 : Blo 2177435 3266759 := bstep (se 1 (by rfl) ⟨2450069, by rfl⟩ : syracuseStep 3266759 = 4900139) B4900139
theorem B2177839 : Blo 2177435 2177839 := bstep (se 1 (by rfl) ⟨1633379, by rfl⟩ : syracuseStep 2177839 = 3266759) B3266759
theorem B3266765 : Blo 2177435 3266765 := bbase (se 3 (by rfl) ⟨612518, by rfl⟩ : syracuseStep 3266765 = 1225037) (by norm_num)
theorem B2177843 : Blo 2177435 2177843 := bstep (se 1 (by rfl) ⟨1633382, by rfl⟩ : syracuseStep 2177843 = 3266765) B3266765
theorem B4900157 : Blo 2177435 4900157 := bbase (se 3 (by rfl) ⟨918779, by rfl⟩ : syracuseStep 4900157 = 1837559) (by norm_num)
theorem B3266771 : Blo 2177435 3266771 := bstep (se 1 (by rfl) ⟨2450078, by rfl⟩ : syracuseStep 3266771 = 4900157) B4900157
theorem B2177847 : Blo 2177435 2177847 := bstep (se 1 (by rfl) ⟨1633385, by rfl⟩ : syracuseStep 2177847 = 3266771) B3266771
theorem B3675125 : Blo 2177435 3675125 := bbase (se 5 (by rfl) ⟨172271, by rfl⟩ : syracuseStep 3675125 = 344543) (by norm_num)
theorem B2450083 : Blo 2177435 2450083 := bstep (se 1 (by rfl) ⟨1837562, by rfl⟩ : syracuseStep 2450083 = 3675125) B3675125
theorem B3266777 : Blo 2177435 3266777 := bstep (se 2 (by rfl) ⟨1225041, by rfl⟩ : syracuseStep 3266777 = 2450083) B2450083
theorem B2177851 : Blo 2177435 2177851 := bstep (se 1 (by rfl) ⟨1633388, by rfl⟩ : syracuseStep 2177851 = 3266777) B3266777
theorem B5232757 : Blo 2177435 5232757 := bbase (se 5 (by rfl) ⟨245285, by rfl⟩ : syracuseStep 5232757 = 490571) (by norm_num)
theorem B6977009 : Blo 2177435 6977009 := bstep (se 2 (by rfl) ⟨2616378, by rfl⟩ : syracuseStep 6977009 = 5232757) B5232757
theorem B4651339 : Blo 2177435 4651339 := bstep (se 1 (by rfl) ⟨3488504, by rfl⟩ : syracuseStep 4651339 = 6977009) B6977009
theorem B6201785 : Blo 2177435 6201785 := bstep (se 2 (by rfl) ⟨2325669, by rfl⟩ : syracuseStep 6201785 = 4651339) B4651339
theorem B16538093 : Blo 2177435 16538093 := bstep (se 3 (by rfl) ⟨3100892, by rfl⟩ : syracuseStep 16538093 = 6201785) B6201785
theorem B11025395 : Blo 2177435 11025395 := bstep (se 1 (by rfl) ⟨8269046, by rfl⟩ : syracuseStep 11025395 = 16538093) B16538093
theorem B7350263 : Blo 2177435 7350263 := bstep (se 1 (by rfl) ⟨5512697, by rfl⟩ : syracuseStep 7350263 = 11025395) B11025395
theorem B4900175 : Blo 2177435 4900175 := bstep (se 1 (by rfl) ⟨3675131, by rfl⟩ : syracuseStep 4900175 = 7350263) B7350263
theorem B3266783 : Blo 2177435 3266783 := bstep (se 1 (by rfl) ⟨2450087, by rfl⟩ : syracuseStep 3266783 = 4900175) B4900175
theorem B2177855 : Blo 2177435 2177855 := bstep (se 1 (by rfl) ⟨1633391, by rfl⟩ : syracuseStep 2177855 = 3266783) B3266783
theorem B3266789 : Blo 2177435 3266789 := bbase (se 4 (by rfl) ⟨306261, by rfl⟩ : syracuseStep 3266789 = 612523) (by norm_num)
theorem B2177859 : Blo 2177435 2177859 := bstep (se 1 (by rfl) ⟨1633394, by rfl⟩ : syracuseStep 2177859 = 3266789) B3266789
theorem B4651357 : Blo 2177435 4651357 := bbase (se 3 (by rfl) ⟨872129, by rfl⟩ : syracuseStep 4651357 = 1744259) (by norm_num)
theorem B6201809 : Blo 2177435 6201809 := bstep (se 2 (by rfl) ⟨2325678, by rfl⟩ : syracuseStep 6201809 = 4651357) B4651357
theorem B4134539 : Blo 2177435 4134539 := bstep (se 1 (by rfl) ⟨3100904, by rfl⟩ : syracuseStep 4134539 = 6201809) B6201809
theorem B2756359 : Blo 2177435 2756359 := bstep (se 1 (by rfl) ⟨2067269, by rfl⟩ : syracuseStep 2756359 = 4134539) B4134539
theorem B3675145 : Blo 2177435 3675145 := bstep (se 2 (by rfl) ⟨1378179, by rfl⟩ : syracuseStep 3675145 = 2756359) B2756359
theorem B4900193 : Blo 2177435 4900193 := bstep (se 2 (by rfl) ⟨1837572, by rfl⟩ : syracuseStep 4900193 = 3675145) B3675145
theorem B3266795 : Blo 2177435 3266795 := bstep (se 1 (by rfl) ⟨2450096, by rfl⟩ : syracuseStep 3266795 = 4900193) B4900193
theorem B2177863 : Blo 2177435 2177863 := bstep (se 1 (by rfl) ⟨1633397, by rfl⟩ : syracuseStep 2177863 = 3266795) B3266795
theorem B2450101 : Blo 2177435 2450101 := bbase (se 5 (by rfl) ⟨114848, by rfl⟩ : syracuseStep 2450101 = 229697) (by norm_num)
theorem B3266801 : Blo 2177435 3266801 := bstep (se 2 (by rfl) ⟨1225050, by rfl⟩ : syracuseStep 3266801 = 2450101) B2450101
theorem B2177867 : Blo 2177435 2177867 := bstep (se 1 (by rfl) ⟨1633400, by rfl⟩ : syracuseStep 2177867 = 3266801) B3266801
theorem B2756369 : Blo 2177435 2756369 := bbase (se 2 (by rfl) ⟨1033638, by rfl⟩ : syracuseStep 2756369 = 2067277) (by norm_num)
theorem B7350317 : Blo 2177435 7350317 := bstep (se 3 (by rfl) ⟨1378184, by rfl⟩ : syracuseStep 7350317 = 2756369) B2756369
theorem B4900211 : Blo 2177435 4900211 := bstep (se 1 (by rfl) ⟨3675158, by rfl⟩ : syracuseStep 4900211 = 7350317) B7350317
theorem B3266807 : Blo 2177435 3266807 := bstep (se 1 (by rfl) ⟨2450105, by rfl⟩ : syracuseStep 3266807 = 4900211) B4900211
theorem B2177871 : Blo 2177435 2177871 := bstep (se 1 (by rfl) ⟨1633403, by rfl⟩ : syracuseStep 2177871 = 3266807) B3266807
theorem B3266813 : Blo 2177435 3266813 := bbase (se 3 (by rfl) ⟨612527, by rfl⟩ : syracuseStep 3266813 = 1225055) (by norm_num)
theorem B2177875 : Blo 2177435 2177875 := bstep (se 1 (by rfl) ⟨1633406, by rfl⟩ : syracuseStep 2177875 = 3266813) B3266813
theorem B4900229 : Blo 2177435 4900229 := bbase (se 4 (by rfl) ⟨459396, by rfl⟩ : syracuseStep 4900229 = 918793) (by norm_num)
theorem B3266819 : Blo 2177435 3266819 := bstep (se 1 (by rfl) ⟨2450114, by rfl⟩ : syracuseStep 3266819 = 4900229) B4900229
theorem B2177879 : Blo 2177435 2177879 := bstep (se 1 (by rfl) ⟨1633409, by rfl⟩ : syracuseStep 2177879 = 3266819) B3266819
theorem B3100933 : Blo 2177435 3100933 := bbase (se 4 (by rfl) ⟨290712, by rfl⟩ : syracuseStep 3100933 = 581425) (by norm_num)
theorem B4134577 : Blo 2177435 4134577 := bstep (se 2 (by rfl) ⟨1550466, by rfl⟩ : syracuseStep 4134577 = 3100933) B3100933
theorem B5512769 : Blo 2177435 5512769 := bstep (se 2 (by rfl) ⟨2067288, by rfl⟩ : syracuseStep 5512769 = 4134577) B4134577
theorem B3675179 : Blo 2177435 3675179 := bstep (se 1 (by rfl) ⟨2756384, by rfl⟩ : syracuseStep 3675179 = 5512769) B5512769
theorem B2450119 : Blo 2177435 2450119 := bstep (se 1 (by rfl) ⟨1837589, by rfl⟩ : syracuseStep 2450119 = 3675179) B3675179
theorem B3266825 : Blo 2177435 3266825 := bstep (se 2 (by rfl) ⟨1225059, by rfl⟩ : syracuseStep 3266825 = 2450119) B2450119
theorem B2177883 : Blo 2177435 2177883 := bstep (se 1 (by rfl) ⟨1633412, by rfl⟩ : syracuseStep 2177883 = 3266825) B3266825
theorem B11025557 : Blo 2177435 11025557 := bbase (se 6 (by rfl) ⟨258411, by rfl⟩ : syracuseStep 11025557 = 516823) (by norm_num)
theorem B7350371 : Blo 2177435 7350371 := bstep (se 1 (by rfl) ⟨5512778, by rfl⟩ : syracuseStep 7350371 = 11025557) B11025557
theorem B4900247 : Blo 2177435 4900247 := bstep (se 1 (by rfl) ⟨3675185, by rfl⟩ : syracuseStep 4900247 = 7350371) B7350371
theorem B3266831 : Blo 2177435 3266831 := bstep (se 1 (by rfl) ⟨2450123, by rfl⟩ : syracuseStep 3266831 = 4900247) B4900247
theorem B2177887 : Blo 2177435 2177887 := bstep (se 1 (by rfl) ⟨1633415, by rfl⟩ : syracuseStep 2177887 = 3266831) B3266831
theorem B3266837 : Blo 2177435 3266837 := bbase (se 6 (by rfl) ⟨76566, by rfl⟩ : syracuseStep 3266837 = 153133) (by norm_num)
theorem B2177891 : Blo 2177435 2177891 := bstep (se 1 (by rfl) ⟨1633418, by rfl⟩ : syracuseStep 2177891 = 3266837) B3266837
theorem B5232853 : Blo 2177435 5232853 := bbase (se 7 (by rfl) ⟨61322, by rfl⟩ : syracuseStep 5232853 = 122645) (by norm_num)
theorem B27908549 : Blo 2177435 27908549 := bstep (se 4 (by rfl) ⟨2616426, by rfl⟩ : syracuseStep 27908549 = 5232853) B5232853
theorem B18605699 : Blo 2177435 18605699 := bstep (se 1 (by rfl) ⟨13954274, by rfl⟩ : syracuseStep 18605699 = 27908549) B27908549
theorem B12403799 : Blo 2177435 12403799 := bstep (se 1 (by rfl) ⟨9302849, by rfl⟩ : syracuseStep 12403799 = 18605699) B18605699
theorem B8269199 : Blo 2177435 8269199 := bstep (se 1 (by rfl) ⟨6201899, by rfl⟩ : syracuseStep 8269199 = 12403799) B12403799
theorem B5512799 : Blo 2177435 5512799 := bstep (se 1 (by rfl) ⟨4134599, by rfl⟩ : syracuseStep 5512799 = 8269199) B8269199
theorem B3675199 : Blo 2177435 3675199 := bstep (se 1 (by rfl) ⟨2756399, by rfl⟩ : syracuseStep 3675199 = 5512799) B5512799
theorem B4900265 : Blo 2177435 4900265 := bstep (se 2 (by rfl) ⟨1837599, by rfl⟩ : syracuseStep 4900265 = 3675199) B3675199
theorem B3266843 : Blo 2177435 3266843 := bstep (se 1 (by rfl) ⟨2450132, by rfl⟩ : syracuseStep 3266843 = 4900265) B4900265
theorem B2177895 : Blo 2177435 2177895 := bstep (se 1 (by rfl) ⟨1633421, by rfl⟩ : syracuseStep 2177895 = 3266843) B3266843
theorem B2450137 : Blo 2177435 2450137 := bbase (se 2 (by rfl) ⟨918801, by rfl⟩ : syracuseStep 2450137 = 1837603) (by norm_num)
theorem B3266849 : Blo 2177435 3266849 := bstep (se 2 (by rfl) ⟨1225068, by rfl⟩ : syracuseStep 3266849 = 2450137) B2450137
theorem B2177899 : Blo 2177435 2177899 := bstep (se 1 (by rfl) ⟨1633424, by rfl⟩ : syracuseStep 2177899 = 3266849) B3266849
theorem B2325721 : Blo 2177435 2325721 := bbase (se 2 (by rfl) ⟨872145, by rfl⟩ : syracuseStep 2325721 = 1744291) (by norm_num)
theorem B3100961 : Blo 2177435 3100961 := bstep (se 2 (by rfl) ⟨1162860, by rfl⟩ : syracuseStep 3100961 = 2325721) B2325721
theorem B8269229 : Blo 2177435 8269229 := bstep (se 3 (by rfl) ⟨1550480, by rfl⟩ : syracuseStep 8269229 = 3100961) B3100961
theorem B5512819 : Blo 2177435 5512819 := bstep (se 1 (by rfl) ⟨4134614, by rfl⟩ : syracuseStep 5512819 = 8269229) B8269229
theorem B7350425 : Blo 2177435 7350425 := bstep (se 2 (by rfl) ⟨2756409, by rfl⟩ : syracuseStep 7350425 = 5512819) B5512819
theorem B4900283 : Blo 2177435 4900283 := bstep (se 1 (by rfl) ⟨3675212, by rfl⟩ : syracuseStep 4900283 = 7350425) B7350425
theorem B3266855 : Blo 2177435 3266855 := bstep (se 1 (by rfl) ⟨2450141, by rfl⟩ : syracuseStep 3266855 = 4900283) B4900283
theorem B2177903 : Blo 2177435 2177903 := bstep (se 1 (by rfl) ⟨1633427, by rfl⟩ : syracuseStep 2177903 = 3266855) B3266855
theorem B3266861 : Blo 2177435 3266861 := bbase (se 3 (by rfl) ⟨612536, by rfl⟩ : syracuseStep 3266861 = 1225073) (by norm_num)
theorem B2177907 : Blo 2177435 2177907 := bstep (se 1 (by rfl) ⟨1633430, by rfl⟩ : syracuseStep 2177907 = 3266861) B3266861
theorem B4900301 : Blo 2177435 4900301 := bbase (se 3 (by rfl) ⟨918806, by rfl⟩ : syracuseStep 4900301 = 1837613) (by norm_num)
theorem B3266867 : Blo 2177435 3266867 := bstep (se 1 (by rfl) ⟨2450150, by rfl⟩ : syracuseStep 3266867 = 4900301) B4900301
theorem B2177911 : Blo 2177435 2177911 := bstep (se 1 (by rfl) ⟨1633433, by rfl⟩ : syracuseStep 2177911 = 3266867) B3266867
theorem B2756425 : Blo 2177435 2756425 := bbase (se 2 (by rfl) ⟨1033659, by rfl⟩ : syracuseStep 2756425 = 2067319) (by norm_num)
theorem B3675233 : Blo 2177435 3675233 := bstep (se 2 (by rfl) ⟨1378212, by rfl⟩ : syracuseStep 3675233 = 2756425) B2756425
theorem B2450155 : Blo 2177435 2450155 := bstep (se 1 (by rfl) ⟨1837616, by rfl⟩ : syracuseStep 2450155 = 3675233) B3675233
theorem B3266873 : Blo 2177435 3266873 := bstep (se 2 (by rfl) ⟨1225077, by rfl⟩ : syracuseStep 3266873 = 2450155) B2450155
theorem B2177915 : Blo 2177435 2177915 := bstep (se 1 (by rfl) ⟨1633436, by rfl⟩ : syracuseStep 2177915 = 3266873) B3266873
theorem B3776213 : Blo 2177435 3776213 := bbase (se 7 (by rfl) ⟨44252, by rfl⟩ : syracuseStep 3776213 = 88505) (by norm_num)
theorem B2517475 : Blo 2177435 2517475 := bstep (se 1 (by rfl) ⟨1888106, by rfl⟩ : syracuseStep 2517475 = 3776213) B3776213
theorem B3356633 : Blo 2177435 3356633 := bstep (se 2 (by rfl) ⟨1258737, by rfl⟩ : syracuseStep 3356633 = 2517475) B2517475
theorem B2237755 : Blo 2177435 2237755 := bstep (se 1 (by rfl) ⟨1678316, by rfl⟩ : syracuseStep 2237755 = 3356633) B3356633
theorem B2983673 : Blo 2177435 2983673 := bstep (se 2 (by rfl) ⟨1118877, by rfl⟩ : syracuseStep 2983673 = 2237755) B2237755
theorem B7956461 : Blo 2177435 7956461 := bstep (se 3 (by rfl) ⟨1491836, by rfl⟩ : syracuseStep 7956461 = 2983673) B2983673
theorem B5304307 : Blo 2177435 5304307 := bstep (se 1 (by rfl) ⟨3978230, by rfl⟩ : syracuseStep 5304307 = 7956461) B7956461
theorem B7072409 : Blo 2177435 7072409 := bstep (se 2 (by rfl) ⟨2652153, by rfl⟩ : syracuseStep 7072409 = 5304307) B5304307
theorem B4714939 : Blo 2177435 4714939 := bstep (se 1 (by rfl) ⟨3536204, by rfl⟩ : syracuseStep 4714939 = 7072409) B7072409
theorem B6286585 : Blo 2177435 6286585 := bstep (se 2 (by rfl) ⟨2357469, by rfl⟩ : syracuseStep 6286585 = 4714939) B4714939
theorem B8382113 : Blo 2177435 8382113 := bstep (se 2 (by rfl) ⟨3143292, by rfl⟩ : syracuseStep 8382113 = 6286585) B6286585
theorem B5588075 : Blo 2177435 5588075 := bstep (se 1 (by rfl) ⟨4191056, by rfl⟩ : syracuseStep 5588075 = 8382113) B8382113
theorem B3725383 : Blo 2177435 3725383 := bstep (se 1 (by rfl) ⟨2794037, by rfl⟩ : syracuseStep 3725383 = 5588075) B5588075
theorem B4967177 : Blo 2177435 4967177 := bstep (se 2 (by rfl) ⟨1862691, by rfl⟩ : syracuseStep 4967177 = 3725383) B3725383
theorem B13245805 : Blo 2177435 13245805 := bstep (se 3 (by rfl) ⟨2483588, by rfl⟩ : syracuseStep 13245805 = 4967177) B4967177
theorem B17661073 : Blo 2177435 17661073 := bstep (se 2 (by rfl) ⟨6622902, by rfl⟩ : syracuseStep 17661073 = 13245805) B13245805
theorem B23548097 : Blo 2177435 23548097 := bstep (se 2 (by rfl) ⟨8830536, by rfl⟩ : syracuseStep 23548097 = 17661073) B17661073
theorem B15698731 : Blo 2177435 15698731 := bstep (se 1 (by rfl) ⟨11774048, by rfl⟩ : syracuseStep 15698731 = 23548097) B23548097
theorem B20931641 : Blo 2177435 20931641 := bstep (se 2 (by rfl) ⟨7849365, by rfl⟩ : syracuseStep 20931641 = 15698731) B15698731
theorem B13954427 : Blo 2177435 13954427 := bstep (se 1 (by rfl) ⟨10465820, by rfl⟩ : syracuseStep 13954427 = 20931641) B20931641
theorem B9302951 : Blo 2177435 9302951 := bstep (se 1 (by rfl) ⟨6977213, by rfl⟩ : syracuseStep 9302951 = 13954427) B13954427
theorem B24807869 : Blo 2177435 24807869 := bstep (se 3 (by rfl) ⟨4651475, by rfl⟩ : syracuseStep 24807869 = 9302951) B9302951
theorem B16538579 : Blo 2177435 16538579 := bstep (se 1 (by rfl) ⟨12403934, by rfl⟩ : syracuseStep 16538579 = 24807869) B24807869
theorem B11025719 : Blo 2177435 11025719 := bstep (se 1 (by rfl) ⟨8269289, by rfl⟩ : syracuseStep 11025719 = 16538579) B16538579
theorem B7350479 : Blo 2177435 7350479 := bstep (se 1 (by rfl) ⟨5512859, by rfl⟩ : syracuseStep 7350479 = 11025719) B11025719
theorem B4900319 : Blo 2177435 4900319 := bstep (se 1 (by rfl) ⟨3675239, by rfl⟩ : syracuseStep 4900319 = 7350479) B7350479
theorem B3266879 : Blo 2177435 3266879 := bstep (se 1 (by rfl) ⟨2450159, by rfl⟩ : syracuseStep 3266879 = 4900319) B4900319
theorem B2177919 : Blo 2177435 2177919 := bstep (se 1 (by rfl) ⟨1633439, by rfl⟩ : syracuseStep 2177919 = 3266879) B3266879
theorem B3266885 : Blo 2177435 3266885 := bbase (se 4 (by rfl) ⟨306270, by rfl⟩ : syracuseStep 3266885 = 612541) (by norm_num)
theorem B2177923 : Blo 2177435 2177923 := bstep (se 1 (by rfl) ⟨1633442, by rfl⟩ : syracuseStep 2177923 = 3266885) B3266885
theorem B3675253 : Blo 2177435 3675253 := bbase (se 5 (by rfl) ⟨172277, by rfl⟩ : syracuseStep 3675253 = 344555) (by norm_num)
theorem B4900337 : Blo 2177435 4900337 := bstep (se 2 (by rfl) ⟨1837626, by rfl⟩ : syracuseStep 4900337 = 3675253) B3675253
theorem B3266891 : Blo 2177435 3266891 := bstep (se 1 (by rfl) ⟨2450168, by rfl⟩ : syracuseStep 3266891 = 4900337) B4900337
theorem B2177927 : Blo 2177435 2177927 := bstep (se 1 (by rfl) ⟨1633445, by rfl⟩ : syracuseStep 2177927 = 3266891) B3266891
theorem B2450173 : Blo 2177435 2450173 := bbase (se 3 (by rfl) ⟨459407, by rfl⟩ : syracuseStep 2450173 = 918815) (by norm_num)
theorem B3266897 : Blo 2177435 3266897 := bstep (se 2 (by rfl) ⟨1225086, by rfl⟩ : syracuseStep 3266897 = 2450173) B2450173
theorem B2177931 : Blo 2177435 2177931 := bstep (se 1 (by rfl) ⟨1633448, by rfl⟩ : syracuseStep 2177931 = 3266897) B3266897
theorem B7350533 : Blo 2177435 7350533 := bbase (se 4 (by rfl) ⟨689112, by rfl⟩ : syracuseStep 7350533 = 1378225) (by norm_num)
theorem B4900355 : Blo 2177435 4900355 := bstep (se 1 (by rfl) ⟨3675266, by rfl⟩ : syracuseStep 4900355 = 7350533) B7350533
theorem B3266903 : Blo 2177435 3266903 := bstep (se 1 (by rfl) ⟨2450177, by rfl⟩ : syracuseStep 3266903 = 4900355) B4900355
theorem B2177935 : Blo 2177435 2177935 := bstep (se 1 (by rfl) ⟨1633451, by rfl⟩ : syracuseStep 2177935 = 3266903) B3266903
theorem B3266909 : Blo 2177435 3266909 := bbase (se 3 (by rfl) ⟨612545, by rfl⟩ : syracuseStep 3266909 = 1225091) (by norm_num)
theorem B2177939 : Blo 2177435 2177939 := bstep (se 1 (by rfl) ⟨1633454, by rfl⟩ : syracuseStep 2177939 = 3266909) B3266909
theorem B4900373 : Blo 2177435 4900373 := bbase (se 6 (by rfl) ⟨114852, by rfl⟩ : syracuseStep 4900373 = 229705) (by norm_num)
theorem B3266915 : Blo 2177435 3266915 := bstep (se 1 (by rfl) ⟨2450186, by rfl⟩ : syracuseStep 3266915 = 4900373) B4900373
theorem B2177943 : Blo 2177435 2177943 := bstep (se 1 (by rfl) ⟨1633457, by rfl⟩ : syracuseStep 2177943 = 3266915) B3266915
theorem B8269397 : Blo 2177435 8269397 := bbase (se 8 (by rfl) ⟨48453, by rfl⟩ : syracuseStep 8269397 = 96907) (by norm_num)
theorem B5512931 : Blo 2177435 5512931 := bstep (se 1 (by rfl) ⟨4134698, by rfl⟩ : syracuseStep 5512931 = 8269397) B8269397
theorem B3675287 : Blo 2177435 3675287 := bstep (se 1 (by rfl) ⟨2756465, by rfl⟩ : syracuseStep 3675287 = 5512931) B5512931
theorem B2450191 : Blo 2177435 2450191 := bstep (se 1 (by rfl) ⟨1837643, by rfl⟩ : syracuseStep 2450191 = 3675287) B3675287
theorem B3266921 : Blo 2177435 3266921 := bstep (se 2 (by rfl) ⟨1225095, by rfl⟩ : syracuseStep 3266921 = 2450191) B2450191
theorem B2177947 : Blo 2177435 2177947 := bstep (se 1 (by rfl) ⟨1633460, by rfl⟩ : syracuseStep 2177947 = 3266921) B3266921
theorem B12404117 : Blo 2177435 12404117 := bbase (se 6 (by rfl) ⟨290721, by rfl⟩ : syracuseStep 12404117 = 581443) (by norm_num)
theorem B8269411 : Blo 2177435 8269411 := bstep (se 1 (by rfl) ⟨6202058, by rfl⟩ : syracuseStep 8269411 = 12404117) B12404117
theorem B11025881 : Blo 2177435 11025881 := bstep (se 2 (by rfl) ⟨4134705, by rfl⟩ : syracuseStep 11025881 = 8269411) B8269411
theorem B7350587 : Blo 2177435 7350587 := bstep (se 1 (by rfl) ⟨5512940, by rfl⟩ : syracuseStep 7350587 = 11025881) B11025881
theorem B4900391 : Blo 2177435 4900391 := bstep (se 1 (by rfl) ⟨3675293, by rfl⟩ : syracuseStep 4900391 = 7350587) B7350587
theorem B3266927 : Blo 2177435 3266927 := bstep (se 1 (by rfl) ⟨2450195, by rfl⟩ : syracuseStep 3266927 = 4900391) B4900391
theorem B2177951 : Blo 2177435 2177951 := bstep (se 1 (by rfl) ⟨1633463, by rfl⟩ : syracuseStep 2177951 = 3266927) B3266927
theorem B3266933 : Blo 2177435 3266933 := bbase (se 5 (by rfl) ⟨153137, by rfl⟩ : syracuseStep 3266933 = 306275) (by norm_num)
theorem B2177955 : Blo 2177435 2177955 := bstep (se 1 (by rfl) ⟨1633466, by rfl⟩ : syracuseStep 2177955 = 3266933) B3266933
theorem B2325781 : Blo 2177435 2325781 := bbase (se 6 (by rfl) ⟨54510, by rfl⟩ : syracuseStep 2325781 = 109021) (by norm_num)
theorem B3101041 : Blo 2177435 3101041 := bstep (se 2 (by rfl) ⟨1162890, by rfl⟩ : syracuseStep 3101041 = 2325781) B2325781
theorem B4134721 : Blo 2177435 4134721 := bstep (se 2 (by rfl) ⟨1550520, by rfl⟩ : syracuseStep 4134721 = 3101041) B3101041
theorem B5512961 : Blo 2177435 5512961 := bstep (se 2 (by rfl) ⟨2067360, by rfl⟩ : syracuseStep 5512961 = 4134721) B4134721
theorem B3675307 : Blo 2177435 3675307 := bstep (se 1 (by rfl) ⟨2756480, by rfl⟩ : syracuseStep 3675307 = 5512961) B5512961
theorem B4900409 : Blo 2177435 4900409 := bstep (se 2 (by rfl) ⟨1837653, by rfl⟩ : syracuseStep 4900409 = 3675307) B3675307
theorem B3266939 : Blo 2177435 3266939 := bstep (se 1 (by rfl) ⟨2450204, by rfl⟩ : syracuseStep 3266939 = 4900409) B4900409
theorem B2177959 : Blo 2177435 2177959 := bstep (se 1 (by rfl) ⟨1633469, by rfl⟩ : syracuseStep 2177959 = 3266939) B3266939
theorem B2450209 : Blo 2177435 2450209 := bbase (se 2 (by rfl) ⟨918828, by rfl⟩ : syracuseStep 2450209 = 1837657) (by norm_num)
theorem B3266945 : Blo 2177435 3266945 := bstep (se 2 (by rfl) ⟨1225104, by rfl⟩ : syracuseStep 3266945 = 2450209) B2450209
theorem B2177963 : Blo 2177435 2177963 := bstep (se 1 (by rfl) ⟨1633472, by rfl⟩ : syracuseStep 2177963 = 3266945) B3266945
theorem B5512981 : Blo 2177435 5512981 := bbase (se 6 (by rfl) ⟨129210, by rfl⟩ : syracuseStep 5512981 = 258421) (by norm_num)
theorem B7350641 : Blo 2177435 7350641 := bstep (se 2 (by rfl) ⟨2756490, by rfl⟩ : syracuseStep 7350641 = 5512981) B5512981
theorem B4900427 : Blo 2177435 4900427 := bstep (se 1 (by rfl) ⟨3675320, by rfl⟩ : syracuseStep 4900427 = 7350641) B7350641
theorem B3266951 : Blo 2177435 3266951 := bstep (se 1 (by rfl) ⟨2450213, by rfl⟩ : syracuseStep 3266951 = 4900427) B4900427
theorem B2177967 : Blo 2177435 2177967 := bstep (se 1 (by rfl) ⟨1633475, by rfl⟩ : syracuseStep 2177967 = 3266951) B3266951
theorem B3266957 : Blo 2177435 3266957 := bbase (se 3 (by rfl) ⟨612554, by rfl⟩ : syracuseStep 3266957 = 1225109) (by norm_num)
theorem B2177971 : Blo 2177435 2177971 := bstep (se 1 (by rfl) ⟨1633478, by rfl⟩ : syracuseStep 2177971 = 3266957) B3266957
theorem B4900445 : Blo 2177435 4900445 := bbase (se 3 (by rfl) ⟨918833, by rfl⟩ : syracuseStep 4900445 = 1837667) (by norm_num)
theorem B3266963 : Blo 2177435 3266963 := bstep (se 1 (by rfl) ⟨2450222, by rfl⟩ : syracuseStep 3266963 = 4900445) B4900445
theorem B2177975 : Blo 2177435 2177975 := bstep (se 1 (by rfl) ⟨1633481, by rfl⟩ : syracuseStep 2177975 = 3266963) B3266963
theorem B3675341 : Blo 2177435 3675341 := bbase (se 3 (by rfl) ⟨689126, by rfl⟩ : syracuseStep 3675341 = 1378253) (by norm_num)
theorem B2450227 : Blo 2177435 2450227 := bstep (se 1 (by rfl) ⟨1837670, by rfl⟩ : syracuseStep 2450227 = 3675341) B3675341
theorem B3266969 : Blo 2177435 3266969 := bstep (se 2 (by rfl) ⟨1225113, by rfl⟩ : syracuseStep 3266969 = 2450227) B2450227
theorem B2177979 : Blo 2177435 2177979 := bstep (se 1 (by rfl) ⟨1633484, by rfl⟩ : syracuseStep 2177979 = 3266969) B3266969
theorem B13954837 : Blo 2177435 13954837 := bbase (se 6 (by rfl) ⟨327066, by rfl⟩ : syracuseStep 13954837 = 654133) (by norm_num)
theorem B18606449 : Blo 2177435 18606449 := bstep (se 2 (by rfl) ⟨6977418, by rfl⟩ : syracuseStep 18606449 = 13954837) B13954837
theorem B12404299 : Blo 2177435 12404299 := bstep (se 1 (by rfl) ⟨9303224, by rfl⟩ : syracuseStep 12404299 = 18606449) B18606449
theorem B16539065 : Blo 2177435 16539065 := bstep (se 2 (by rfl) ⟨6202149, by rfl⟩ : syracuseStep 16539065 = 12404299) B12404299
theorem B11026043 : Blo 2177435 11026043 := bstep (se 1 (by rfl) ⟨8269532, by rfl⟩ : syracuseStep 11026043 = 16539065) B16539065
theorem B7350695 : Blo 2177435 7350695 := bstep (se 1 (by rfl) ⟨5513021, by rfl⟩ : syracuseStep 7350695 = 11026043) B11026043
theorem B4900463 : Blo 2177435 4900463 := bstep (se 1 (by rfl) ⟨3675347, by rfl⟩ : syracuseStep 4900463 = 7350695) B7350695
theorem B3266975 : Blo 2177435 3266975 := bstep (se 1 (by rfl) ⟨2450231, by rfl⟩ : syracuseStep 3266975 = 4900463) B4900463
theorem B2177983 : Blo 2177435 2177983 := bstep (se 1 (by rfl) ⟨1633487, by rfl⟩ : syracuseStep 2177983 = 3266975) B3266975
theorem B3266981 : Blo 2177435 3266981 := bbase (se 4 (by rfl) ⟨306279, by rfl⟩ : syracuseStep 3266981 = 612559) (by norm_num)
theorem B2177987 : Blo 2177435 2177987 := bstep (se 1 (by rfl) ⟨1633490, by rfl⟩ : syracuseStep 2177987 = 3266981) B3266981
theorem B2756521 : Blo 2177435 2756521 := bbase (se 2 (by rfl) ⟨1033695, by rfl⟩ : syracuseStep 2756521 = 2067391) (by norm_num)
theorem B3675361 : Blo 2177435 3675361 := bstep (se 2 (by rfl) ⟨1378260, by rfl⟩ : syracuseStep 3675361 = 2756521) B2756521
theorem B4900481 : Blo 2177435 4900481 := bstep (se 2 (by rfl) ⟨1837680, by rfl⟩ : syracuseStep 4900481 = 3675361) B3675361
theorem B3266987 : Blo 2177435 3266987 := bstep (se 1 (by rfl) ⟨2450240, by rfl⟩ : syracuseStep 3266987 = 4900481) B4900481
theorem B2177991 : Blo 2177435 2177991 := bstep (se 1 (by rfl) ⟨1633493, by rfl⟩ : syracuseStep 2177991 = 3266987) B3266987
theorem B2450245 : Blo 2177435 2450245 := bbase (se 4 (by rfl) ⟨229710, by rfl⟩ : syracuseStep 2450245 = 459421) (by norm_num)
theorem B3266993 : Blo 2177435 3266993 := bstep (se 2 (by rfl) ⟨1225122, by rfl⟩ : syracuseStep 3266993 = 2450245) B2450245
theorem B2177995 : Blo 2177435 2177995 := bstep (se 1 (by rfl) ⟨1633496, by rfl⟩ : syracuseStep 2177995 = 3266993) B3266993
theorem B4134797 : Blo 2177435 4134797 := bbase (se 3 (by rfl) ⟨775274, by rfl⟩ : syracuseStep 4134797 = 1550549) (by norm_num)
theorem B2756531 : Blo 2177435 2756531 := bstep (se 1 (by rfl) ⟨2067398, by rfl⟩ : syracuseStep 2756531 = 4134797) B4134797
theorem B7350749 : Blo 2177435 7350749 := bstep (se 3 (by rfl) ⟨1378265, by rfl⟩ : syracuseStep 7350749 = 2756531) B2756531
theorem B4900499 : Blo 2177435 4900499 := bstep (se 1 (by rfl) ⟨3675374, by rfl⟩ : syracuseStep 4900499 = 7350749) B7350749
theorem B3266999 : Blo 2177435 3266999 := bstep (se 1 (by rfl) ⟨2450249, by rfl⟩ : syracuseStep 3266999 = 4900499) B4900499
theorem B2177999 : Blo 2177435 2177999 := bstep (se 1 (by rfl) ⟨1633499, by rfl⟩ : syracuseStep 2177999 = 3266999) B3266999
theorem B3267005 : Blo 2177435 3267005 := bbase (se 3 (by rfl) ⟨612563, by rfl⟩ : syracuseStep 3267005 = 1225127) (by norm_num)
theorem B2178003 : Blo 2177435 2178003 := bstep (se 1 (by rfl) ⟨1633502, by rfl⟩ : syracuseStep 2178003 = 3267005) B3267005
theorem B4900517 : Blo 2177435 4900517 := bbase (se 4 (by rfl) ⟨459423, by rfl⟩ : syracuseStep 4900517 = 918847) (by norm_num)
theorem B3267011 : Blo 2177435 3267011 := bstep (se 1 (by rfl) ⟨2450258, by rfl⟩ : syracuseStep 3267011 = 4900517) B4900517
theorem B2178007 : Blo 2177435 2178007 := bstep (se 1 (by rfl) ⟨1633505, by rfl⟩ : syracuseStep 2178007 = 3267011) B3267011
theorem B5513093 : Blo 2177435 5513093 := bbase (se 4 (by rfl) ⟨516852, by rfl⟩ : syracuseStep 5513093 = 1033705) (by norm_num)
theorem B3675395 : Blo 2177435 3675395 := bstep (se 1 (by rfl) ⟨2756546, by rfl⟩ : syracuseStep 3675395 = 5513093) B5513093
theorem B2450263 : Blo 2177435 2450263 := bstep (se 1 (by rfl) ⟨1837697, by rfl⟩ : syracuseStep 2450263 = 3675395) B3675395
theorem B3267017 : Blo 2177435 3267017 := bstep (se 2 (by rfl) ⟨1225131, by rfl⟩ : syracuseStep 3267017 = 2450263) B2450263
theorem B2178011 : Blo 2177435 2178011 := bstep (se 1 (by rfl) ⟨1633508, by rfl⟩ : syracuseStep 2178011 = 3267017) B3267017
theorem B18860597 : Blo 2177435 18860597 := bbase (se 5 (by rfl) ⟨884090, by rfl⟩ : syracuseStep 18860597 = 1768181) (by norm_num)
theorem B12573731 : Blo 2177435 12573731 := bstep (se 1 (by rfl) ⟨9430298, by rfl⟩ : syracuseStep 12573731 = 18860597) B18860597
theorem B8382487 : Blo 2177435 8382487 := bstep (se 1 (by rfl) ⟨6286865, by rfl⟩ : syracuseStep 8382487 = 12573731) B12573731
theorem B11176649 : Blo 2177435 11176649 := bstep (se 2 (by rfl) ⟨4191243, by rfl⟩ : syracuseStep 11176649 = 8382487) B8382487
theorem B7451099 : Blo 2177435 7451099 := bstep (se 1 (by rfl) ⟨5588324, by rfl⟩ : syracuseStep 7451099 = 11176649) B11176649
theorem B4967399 : Blo 2177435 4967399 := bstep (se 1 (by rfl) ⟨3725549, by rfl⟩ : syracuseStep 4967399 = 7451099) B7451099
theorem B3311599 : Blo 2177435 3311599 := bstep (se 1 (by rfl) ⟨2483699, by rfl⟩ : syracuseStep 3311599 = 4967399) B4967399
theorem B4415465 : Blo 2177435 4415465 := bstep (se 2 (by rfl) ⟨1655799, by rfl⟩ : syracuseStep 4415465 = 3311599) B3311599
theorem B2943643 : Blo 2177435 2943643 := bstep (se 1 (by rfl) ⟨2207732, by rfl⟩ : syracuseStep 2943643 = 4415465) B4415465
theorem B3924857 : Blo 2177435 3924857 := bstep (se 2 (by rfl) ⟨1471821, by rfl⟩ : syracuseStep 3924857 = 2943643) B2943643
theorem B2616571 : Blo 2177435 2616571 := bstep (se 1 (by rfl) ⟨1962428, by rfl⟩ : syracuseStep 2616571 = 3924857) B3924857
theorem B3488761 : Blo 2177435 3488761 := bstep (se 2 (by rfl) ⟨1308285, by rfl⟩ : syracuseStep 3488761 = 2616571) B2616571
theorem B4651681 : Blo 2177435 4651681 := bstep (se 2 (by rfl) ⟨1744380, by rfl⟩ : syracuseStep 4651681 = 3488761) B3488761
theorem B6202241 : Blo 2177435 6202241 := bstep (se 2 (by rfl) ⟨2325840, by rfl⟩ : syracuseStep 6202241 = 4651681) B4651681
theorem B4134827 : Blo 2177435 4134827 := bstep (se 1 (by rfl) ⟨3101120, by rfl⟩ : syracuseStep 4134827 = 6202241) B6202241
theorem B11026205 : Blo 2177435 11026205 := bstep (se 3 (by rfl) ⟨2067413, by rfl⟩ : syracuseStep 11026205 = 4134827) B4134827
theorem B7350803 : Blo 2177435 7350803 := bstep (se 1 (by rfl) ⟨5513102, by rfl⟩ : syracuseStep 7350803 = 11026205) B11026205
theorem B4900535 : Blo 2177435 4900535 := bstep (se 1 (by rfl) ⟨3675401, by rfl⟩ : syracuseStep 4900535 = 7350803) B7350803
theorem B3267023 : Blo 2177435 3267023 := bstep (se 1 (by rfl) ⟨2450267, by rfl⟩ : syracuseStep 3267023 = 4900535) B4900535
theorem B2178015 : Blo 2177435 2178015 := bstep (se 1 (by rfl) ⟨1633511, by rfl⟩ : syracuseStep 2178015 = 3267023) B3267023
theorem B3267029 : Blo 2177435 3267029 := bbase (se 7 (by rfl) ⟨38285, by rfl⟩ : syracuseStep 3267029 = 76571) (by norm_num)
theorem B2178019 : Blo 2177435 2178019 := bstep (se 1 (by rfl) ⟨1633514, by rfl⟩ : syracuseStep 2178019 = 3267029) B3267029
theorem B8269685 : Blo 2177435 8269685 := bbase (se 5 (by rfl) ⟨387641, by rfl⟩ : syracuseStep 8269685 = 775283) (by norm_num)
theorem B5513123 : Blo 2177435 5513123 := bstep (se 1 (by rfl) ⟨4134842, by rfl⟩ : syracuseStep 5513123 = 8269685) B8269685
theorem B3675415 : Blo 2177435 3675415 := bstep (se 1 (by rfl) ⟨2756561, by rfl⟩ : syracuseStep 3675415 = 5513123) B5513123
theorem B4900553 : Blo 2177435 4900553 := bstep (se 2 (by rfl) ⟨1837707, by rfl⟩ : syracuseStep 4900553 = 3675415) B3675415
theorem B3267035 : Blo 2177435 3267035 := bstep (se 1 (by rfl) ⟨2450276, by rfl⟩ : syracuseStep 3267035 = 4900553) B4900553
theorem B2178023 : Blo 2177435 2178023 := bstep (se 1 (by rfl) ⟨1633517, by rfl⟩ : syracuseStep 2178023 = 3267035) B3267035
theorem B2450281 : Blo 2177435 2450281 := bbase (se 2 (by rfl) ⟨918855, by rfl⟩ : syracuseStep 2450281 = 1837711) (by norm_num)
theorem B3267041 : Blo 2177435 3267041 := bstep (se 2 (by rfl) ⟨1225140, by rfl⟩ : syracuseStep 3267041 = 2450281) B2450281
theorem B2178027 : Blo 2177435 2178027 := bstep (se 1 (by rfl) ⟨1633520, by rfl⟩ : syracuseStep 2178027 = 3267041) B3267041
theorem B6977573 : Blo 2177435 6977573 := bbase (se 4 (by rfl) ⟨654147, by rfl⟩ : syracuseStep 6977573 = 1308295) (by norm_num)
theorem B4651715 : Blo 2177435 4651715 := bstep (se 1 (by rfl) ⟨3488786, by rfl⟩ : syracuseStep 4651715 = 6977573) B6977573
theorem B12404573 : Blo 2177435 12404573 := bstep (se 3 (by rfl) ⟨2325857, by rfl⟩ : syracuseStep 12404573 = 4651715) B4651715
theorem B8269715 : Blo 2177435 8269715 := bstep (se 1 (by rfl) ⟨6202286, by rfl⟩ : syracuseStep 8269715 = 12404573) B12404573
theorem B5513143 : Blo 2177435 5513143 := bstep (se 1 (by rfl) ⟨4134857, by rfl⟩ : syracuseStep 5513143 = 8269715) B8269715
theorem B7350857 : Blo 2177435 7350857 := bstep (se 2 (by rfl) ⟨2756571, by rfl⟩ : syracuseStep 7350857 = 5513143) B5513143
theorem B4900571 : Blo 2177435 4900571 := bstep (se 1 (by rfl) ⟨3675428, by rfl⟩ : syracuseStep 4900571 = 7350857) B7350857
theorem B3267047 : Blo 2177435 3267047 := bstep (se 1 (by rfl) ⟨2450285, by rfl⟩ : syracuseStep 3267047 = 4900571) B4900571
theorem B2178031 : Blo 2177435 2178031 := bstep (se 1 (by rfl) ⟨1633523, by rfl⟩ : syracuseStep 2178031 = 3267047) B3267047
theorem B3267053 : Blo 2177435 3267053 := bbase (se 3 (by rfl) ⟨612572, by rfl⟩ : syracuseStep 3267053 = 1225145) (by norm_num)
theorem B2178035 : Blo 2177435 2178035 := bstep (se 1 (by rfl) ⟨1633526, by rfl⟩ : syracuseStep 2178035 = 3267053) B3267053
theorem B4900589 : Blo 2177435 4900589 := bbase (se 3 (by rfl) ⟨918860, by rfl⟩ : syracuseStep 4900589 = 1837721) (by norm_num)
theorem B3267059 : Blo 2177435 3267059 := bstep (se 1 (by rfl) ⟨2450294, by rfl⟩ : syracuseStep 3267059 = 4900589) B4900589
theorem B2178039 : Blo 2177435 2178039 := bstep (se 1 (by rfl) ⟨1633529, by rfl⟩ : syracuseStep 2178039 = 3267059) B3267059
theorem B8831045 : Blo 2177435 8831045 := bbase (se 4 (by rfl) ⟨827910, by rfl⟩ : syracuseStep 8831045 = 1655821) (by norm_num)
theorem B5887363 : Blo 2177435 5887363 := bstep (se 1 (by rfl) ⟨4415522, by rfl⟩ : syracuseStep 5887363 = 8831045) B8831045
theorem B7849817 : Blo 2177435 7849817 := bstep (se 2 (by rfl) ⟨2943681, by rfl⟩ : syracuseStep 7849817 = 5887363) B5887363
theorem B5233211 : Blo 2177435 5233211 := bstep (se 1 (by rfl) ⟨3924908, by rfl⟩ : syracuseStep 5233211 = 7849817) B7849817
theorem B3488807 : Blo 2177435 3488807 := bstep (se 1 (by rfl) ⟨2616605, by rfl⟩ : syracuseStep 3488807 = 5233211) B5233211
theorem B2325871 : Blo 2177435 2325871 := bstep (se 1 (by rfl) ⟨1744403, by rfl⟩ : syracuseStep 2325871 = 3488807) B3488807
theorem B3101161 : Blo 2177435 3101161 := bstep (se 2 (by rfl) ⟨1162935, by rfl⟩ : syracuseStep 3101161 = 2325871) B2325871
theorem B4134881 : Blo 2177435 4134881 := bstep (se 2 (by rfl) ⟨1550580, by rfl⟩ : syracuseStep 4134881 = 3101161) B3101161
theorem B2756587 : Blo 2177435 2756587 := bstep (se 1 (by rfl) ⟨2067440, by rfl⟩ : syracuseStep 2756587 = 4134881) B4134881
theorem B3675449 : Blo 2177435 3675449 := bstep (se 2 (by rfl) ⟨1378293, by rfl⟩ : syracuseStep 3675449 = 2756587) B2756587
theorem B2450299 : Blo 2177435 2450299 := bstep (se 1 (by rfl) ⟨1837724, by rfl⟩ : syracuseStep 2450299 = 3675449) B3675449
theorem B3267065 : Blo 2177435 3267065 := bstep (se 2 (by rfl) ⟨1225149, by rfl⟩ : syracuseStep 3267065 = 2450299) B2450299
theorem B2178043 : Blo 2177435 2178043 := bstep (se 1 (by rfl) ⟨1633532, by rfl⟩ : syracuseStep 2178043 = 3267065) B3267065
theorem B2794201 : Blo 2177435 2794201 := bbase (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) (by norm_num)
theorem B59609621 : Blo 2177435 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B39739747 : Blo 2177435 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B52986329 : Blo 2177435 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B35324219 : Blo 2177435 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B94197917 : Blo 2177435 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B62798611 : Blo 2177435 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B83731481 : Blo 2177435 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B55820987 : Blo 2177435 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B37213991 : Blo 2177435 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B24809327 : Blo 2177435 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B16539551 : Blo 2177435 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B11026367 : Blo 2177435 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B7350911 : Blo 2177435 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B4900607 : Blo 2177435 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B3267071 : Blo 2177435 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B2178047 : Blo 2177435 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B3267077 : Blo 2177435 3267077 := bbase (se 4 (by rfl) ⟨306288, by rfl⟩ : syracuseStep 3267077 = 612577) (by norm_num)
theorem B2178051 : Blo 2177435 2178051 := bstep (se 1 (by rfl) ⟨1633538, by rfl⟩ : syracuseStep 2178051 = 3267077) B3267077
theorem B3675469 : Blo 2177435 3675469 := bbase (se 3 (by rfl) ⟨689150, by rfl⟩ : syracuseStep 3675469 = 1378301) (by norm_num)
theorem B4900625 : Blo 2177435 4900625 := bstep (se 2 (by rfl) ⟨1837734, by rfl⟩ : syracuseStep 4900625 = 3675469) B3675469
theorem B3267083 : Blo 2177435 3267083 := bstep (se 1 (by rfl) ⟨2450312, by rfl⟩ : syracuseStep 3267083 = 4900625) B4900625
theorem B2178055 : Blo 2177435 2178055 := bstep (se 1 (by rfl) ⟨1633541, by rfl⟩ : syracuseStep 2178055 = 3267083) B3267083
theorem B2450317 : Blo 2177435 2450317 := bbase (se 3 (by rfl) ⟨459434, by rfl⟩ : syracuseStep 2450317 = 918869) (by norm_num)
theorem B3267089 : Blo 2177435 3267089 := bstep (se 2 (by rfl) ⟨1225158, by rfl⟩ : syracuseStep 3267089 = 2450317) B2450317
theorem B2178059 : Blo 2177435 2178059 := bstep (se 1 (by rfl) ⟨1633544, by rfl⟩ : syracuseStep 2178059 = 3267089) B3267089
theorem B7350965 : Blo 2177435 7350965 := bbase (se 5 (by rfl) ⟨344576, by rfl⟩ : syracuseStep 7350965 = 689153) (by norm_num)
theorem B4900643 : Blo 2177435 4900643 := bstep (se 1 (by rfl) ⟨3675482, by rfl⟩ : syracuseStep 4900643 = 7350965) B7350965
theorem B3267095 : Blo 2177435 3267095 := bstep (se 1 (by rfl) ⟨2450321, by rfl⟩ : syracuseStep 3267095 = 4900643) B4900643
theorem B2178063 : Blo 2177435 2178063 := bstep (se 1 (by rfl) ⟨1633547, by rfl⟩ : syracuseStep 2178063 = 3267095) B3267095
theorem B3267101 : Blo 2177435 3267101 := bbase (se 3 (by rfl) ⟨612581, by rfl⟩ : syracuseStep 3267101 = 1225163) (by norm_num)
theorem B2178067 : Blo 2177435 2178067 := bstep (se 1 (by rfl) ⟨1633550, by rfl⟩ : syracuseStep 2178067 = 3267101) B3267101
theorem B4900661 : Blo 2177435 4900661 := bbase (se 5 (by rfl) ⟨229718, by rfl⟩ : syracuseStep 4900661 = 459437) (by norm_num)
theorem B3267107 : Blo 2177435 3267107 := bstep (se 1 (by rfl) ⟨2450330, by rfl⟩ : syracuseStep 3267107 = 4900661) B4900661
theorem B2178071 : Blo 2177435 2178071 := bstep (se 1 (by rfl) ⟨1633553, by rfl⟩ : syracuseStep 2178071 = 3267107) B3267107
theorem B3924965 : Blo 2177435 3924965 := bbase (se 4 (by rfl) ⟨367965, by rfl⟩ : syracuseStep 3924965 = 735931) (by norm_num)
theorem B2616643 : Blo 2177435 2616643 := bstep (se 1 (by rfl) ⟨1962482, by rfl⟩ : syracuseStep 2616643 = 3924965) B3924965
theorem B13955429 : Blo 2177435 13955429 := bstep (se 4 (by rfl) ⟨1308321, by rfl⟩ : syracuseStep 13955429 = 2616643) B2616643
theorem B9303619 : Blo 2177435 9303619 := bstep (se 1 (by rfl) ⟨6977714, by rfl⟩ : syracuseStep 9303619 = 13955429) B13955429
theorem B12404825 : Blo 2177435 12404825 := bstep (se 2 (by rfl) ⟨4651809, by rfl⟩ : syracuseStep 12404825 = 9303619) B9303619
theorem B8269883 : Blo 2177435 8269883 := bstep (se 1 (by rfl) ⟨6202412, by rfl⟩ : syracuseStep 8269883 = 12404825) B12404825
theorem B5513255 : Blo 2177435 5513255 := bstep (se 1 (by rfl) ⟨4134941, by rfl⟩ : syracuseStep 5513255 = 8269883) B8269883
theorem B3675503 : Blo 2177435 3675503 := bstep (se 1 (by rfl) ⟨2756627, by rfl⟩ : syracuseStep 3675503 = 5513255) B5513255
theorem B2450335 : Blo 2177435 2450335 := bstep (se 1 (by rfl) ⟨1837751, by rfl⟩ : syracuseStep 2450335 = 3675503) B3675503
theorem B3267113 : Blo 2177435 3267113 := bstep (se 2 (by rfl) ⟨1225167, by rfl⟩ : syracuseStep 3267113 = 2450335) B2450335
theorem B2178075 : Blo 2177435 2178075 := bstep (se 1 (by rfl) ⟨1633556, by rfl⟩ : syracuseStep 2178075 = 3267113) B3267113
theorem B4191365 : Blo 2177435 4191365 := bbase (se 4 (by rfl) ⟨392940, by rfl⟩ : syracuseStep 4191365 = 785881) (by norm_num)
theorem B11176973 : Blo 2177435 11176973 := bstep (se 3 (by rfl) ⟨2095682, by rfl⟩ : syracuseStep 11176973 = 4191365) B4191365
theorem B7451315 : Blo 2177435 7451315 := bstep (se 1 (by rfl) ⟨5588486, by rfl⟩ : syracuseStep 7451315 = 11176973) B11176973
theorem B4967543 : Blo 2177435 4967543 := bstep (se 1 (by rfl) ⟨3725657, by rfl⟩ : syracuseStep 4967543 = 7451315) B7451315
theorem B3311695 : Blo 2177435 3311695 := bstep (se 1 (by rfl) ⟨2483771, by rfl⟩ : syracuseStep 3311695 = 4967543) B4967543
theorem B17662373 : Blo 2177435 17662373 := bstep (se 4 (by rfl) ⟨1655847, by rfl⟩ : syracuseStep 17662373 = 3311695) B3311695
theorem B11774915 : Blo 2177435 11774915 := bstep (se 1 (by rfl) ⟨8831186, by rfl⟩ : syracuseStep 11774915 = 17662373) B17662373
theorem B7849943 : Blo 2177435 7849943 := bstep (se 1 (by rfl) ⟨5887457, by rfl⟩ : syracuseStep 7849943 = 11774915) B11774915
theorem B5233295 : Blo 2177435 5233295 := bstep (se 1 (by rfl) ⟨3924971, by rfl⟩ : syracuseStep 5233295 = 7849943) B7849943
theorem B13955453 : Blo 2177435 13955453 := bstep (se 3 (by rfl) ⟨2616647, by rfl⟩ : syracuseStep 13955453 = 5233295) B5233295
theorem B9303635 : Blo 2177435 9303635 := bstep (se 1 (by rfl) ⟨6977726, by rfl⟩ : syracuseStep 9303635 = 13955453) B13955453
theorem B6202423 : Blo 2177435 6202423 := bstep (se 1 (by rfl) ⟨4651817, by rfl⟩ : syracuseStep 6202423 = 9303635) B9303635
theorem B8269897 : Blo 2177435 8269897 := bstep (se 2 (by rfl) ⟨3101211, by rfl⟩ : syracuseStep 8269897 = 6202423) B6202423
theorem B11026529 : Blo 2177435 11026529 := bstep (se 2 (by rfl) ⟨4134948, by rfl⟩ : syracuseStep 11026529 = 8269897) B8269897
theorem B7351019 : Blo 2177435 7351019 := bstep (se 1 (by rfl) ⟨5513264, by rfl⟩ : syracuseStep 7351019 = 11026529) B11026529
theorem B4900679 : Blo 2177435 4900679 := bstep (se 1 (by rfl) ⟨3675509, by rfl⟩ : syracuseStep 4900679 = 7351019) B7351019
theorem B3267119 : Blo 2177435 3267119 := bstep (se 1 (by rfl) ⟨2450339, by rfl⟩ : syracuseStep 3267119 = 4900679) B4900679
theorem B2178079 : Blo 2177435 2178079 := bstep (se 1 (by rfl) ⟨1633559, by rfl⟩ : syracuseStep 2178079 = 3267119) B3267119
theorem B3267125 : Blo 2177435 3267125 := bbase (se 5 (by rfl) ⟨153146, by rfl⟩ : syracuseStep 3267125 = 306293) (by norm_num)
theorem B2178083 : Blo 2177435 2178083 := bstep (se 1 (by rfl) ⟨1633562, by rfl⟩ : syracuseStep 2178083 = 3267125) B3267125
theorem B5513285 : Blo 2177435 5513285 := bbase (se 4 (by rfl) ⟨516870, by rfl⟩ : syracuseStep 5513285 = 1033741) (by norm_num)
theorem B3675523 : Blo 2177435 3675523 := bstep (se 1 (by rfl) ⟨2756642, by rfl⟩ : syracuseStep 3675523 = 5513285) B5513285
theorem B4900697 : Blo 2177435 4900697 := bstep (se 2 (by rfl) ⟨1837761, by rfl⟩ : syracuseStep 4900697 = 3675523) B3675523
theorem B3267131 : Blo 2177435 3267131 := bstep (se 1 (by rfl) ⟨2450348, by rfl⟩ : syracuseStep 3267131 = 4900697) B4900697
theorem B2178087 : Blo 2177435 2178087 := bstep (se 1 (by rfl) ⟨1633565, by rfl⟩ : syracuseStep 2178087 = 3267131) B3267131
theorem B2450353 : Blo 2177435 2450353 := bbase (se 2 (by rfl) ⟨918882, by rfl⟩ : syracuseStep 2450353 = 1837765) (by norm_num)
theorem B3267137 : Blo 2177435 3267137 := bstep (se 2 (by rfl) ⟨1225176, by rfl⟩ : syracuseStep 3267137 = 2450353) B2450353
theorem B2178091 : Blo 2177435 2178091 := bstep (se 1 (by rfl) ⟨1633568, by rfl⟩ : syracuseStep 2178091 = 3267137) B3267137
theorem B6202469 : Blo 2177435 6202469 := bbase (se 4 (by rfl) ⟨581481, by rfl⟩ : syracuseStep 6202469 = 1162963) (by norm_num)
theorem B4134979 : Blo 2177435 4134979 := bstep (se 1 (by rfl) ⟨3101234, by rfl⟩ : syracuseStep 4134979 = 6202469) B6202469
theorem B5513305 : Blo 2177435 5513305 := bstep (se 2 (by rfl) ⟨2067489, by rfl⟩ : syracuseStep 5513305 = 4134979) B4134979
theorem B7351073 : Blo 2177435 7351073 := bstep (se 2 (by rfl) ⟨2756652, by rfl⟩ : syracuseStep 7351073 = 5513305) B5513305
theorem B4900715 : Blo 2177435 4900715 := bstep (se 1 (by rfl) ⟨3675536, by rfl⟩ : syracuseStep 4900715 = 7351073) B7351073
theorem B3267143 : Blo 2177435 3267143 := bstep (se 1 (by rfl) ⟨2450357, by rfl⟩ : syracuseStep 3267143 = 4900715) B4900715
theorem B2178095 : Blo 2177435 2178095 := bstep (se 1 (by rfl) ⟨1633571, by rfl⟩ : syracuseStep 2178095 = 3267143) B3267143
theorem B3267149 : Blo 2177435 3267149 := bbase (se 3 (by rfl) ⟨612590, by rfl⟩ : syracuseStep 3267149 = 1225181) (by norm_num)
theorem B2178099 : Blo 2177435 2178099 := bstep (se 1 (by rfl) ⟨1633574, by rfl⟩ : syracuseStep 2178099 = 3267149) B3267149
theorem B4900733 : Blo 2177435 4900733 := bbase (se 3 (by rfl) ⟨918887, by rfl⟩ : syracuseStep 4900733 = 1837775) (by norm_num)
theorem B3267155 : Blo 2177435 3267155 := bstep (se 1 (by rfl) ⟨2450366, by rfl⟩ : syracuseStep 3267155 = 4900733) B4900733
theorem B2178103 : Blo 2177435 2178103 := bstep (se 1 (by rfl) ⟨1633577, by rfl⟩ : syracuseStep 2178103 = 3267155) B3267155
theorem B3675557 : Blo 2177435 3675557 := bbase (se 4 (by rfl) ⟨344583, by rfl⟩ : syracuseStep 3675557 = 689167) (by norm_num)
theorem B2450371 : Blo 2177435 2450371 := bstep (se 1 (by rfl) ⟨1837778, by rfl⟩ : syracuseStep 2450371 = 3675557) B3675557
theorem B3267161 : Blo 2177435 3267161 := bstep (se 2 (by rfl) ⟨1225185, by rfl⟩ : syracuseStep 3267161 = 2450371) B2450371
theorem B2178107 : Blo 2177435 2178107 := bstep (se 1 (by rfl) ⟨1633580, by rfl⟩ : syracuseStep 2178107 = 3267161) B3267161
theorem B5233373 : Blo 2177435 5233373 := bbase (se 3 (by rfl) ⟨981257, by rfl⟩ : syracuseStep 5233373 = 1962515) (by norm_num)
theorem B3488915 : Blo 2177435 3488915 := bstep (se 1 (by rfl) ⟨2616686, by rfl⟩ : syracuseStep 3488915 = 5233373) B5233373
theorem B2325943 : Blo 2177435 2325943 := bstep (se 1 (by rfl) ⟨1744457, by rfl⟩ : syracuseStep 2325943 = 3488915) B3488915
theorem B3101257 : Blo 2177435 3101257 := bstep (se 2 (by rfl) ⟨1162971, by rfl⟩ : syracuseStep 3101257 = 2325943) B2325943
theorem B16540037 : Blo 2177435 16540037 := bstep (se 4 (by rfl) ⟨1550628, by rfl⟩ : syracuseStep 16540037 = 3101257) B3101257
theorem B11026691 : Blo 2177435 11026691 := bstep (se 1 (by rfl) ⟨8270018, by rfl⟩ : syracuseStep 11026691 = 16540037) B16540037
theorem B7351127 : Blo 2177435 7351127 := bstep (se 1 (by rfl) ⟨5513345, by rfl⟩ : syracuseStep 7351127 = 11026691) B11026691
theorem B4900751 : Blo 2177435 4900751 := bstep (se 1 (by rfl) ⟨3675563, by rfl⟩ : syracuseStep 4900751 = 7351127) B7351127
theorem B3267167 : Blo 2177435 3267167 := bstep (se 1 (by rfl) ⟨2450375, by rfl⟩ : syracuseStep 3267167 = 4900751) B4900751
theorem B2178111 : Blo 2177435 2178111 := bstep (se 1 (by rfl) ⟨1633583, by rfl⟩ : syracuseStep 2178111 = 3267167) B3267167
theorem B3267173 : Blo 2177435 3267173 := bbase (se 4 (by rfl) ⟨306297, by rfl⟩ : syracuseStep 3267173 = 612595) (by norm_num)
theorem B2178115 : Blo 2177435 2178115 := bstep (se 1 (by rfl) ⟨1633586, by rfl⟩ : syracuseStep 2178115 = 3267173) B3267173
theorem B3101269 : Blo 2177435 3101269 := bbase (se 8 (by rfl) ⟨18171, by rfl⟩ : syracuseStep 3101269 = 36343) (by norm_num)
theorem B4135025 : Blo 2177435 4135025 := bstep (se 2 (by rfl) ⟨1550634, by rfl⟩ : syracuseStep 4135025 = 3101269) B3101269
theorem B2756683 : Blo 2177435 2756683 := bstep (se 1 (by rfl) ⟨2067512, by rfl⟩ : syracuseStep 2756683 = 4135025) B4135025
theorem B3675577 : Blo 2177435 3675577 := bstep (se 2 (by rfl) ⟨1378341, by rfl⟩ : syracuseStep 3675577 = 2756683) B2756683
theorem B4900769 : Blo 2177435 4900769 := bstep (se 2 (by rfl) ⟨1837788, by rfl⟩ : syracuseStep 4900769 = 3675577) B3675577
theorem B3267179 : Blo 2177435 3267179 := bstep (se 1 (by rfl) ⟨2450384, by rfl⟩ : syracuseStep 3267179 = 4900769) B4900769
theorem B2178119 : Blo 2177435 2178119 := bstep (se 1 (by rfl) ⟨1633589, by rfl⟩ : syracuseStep 2178119 = 3267179) B3267179
theorem B2450389 : Blo 2177435 2450389 := bbase (se 7 (by rfl) ⟨28715, by rfl⟩ : syracuseStep 2450389 = 57431) (by norm_num)
theorem B3267185 : Blo 2177435 3267185 := bstep (se 2 (by rfl) ⟨1225194, by rfl⟩ : syracuseStep 3267185 = 2450389) B2450389
theorem B2178123 : Blo 2177435 2178123 := bstep (se 1 (by rfl) ⟨1633592, by rfl⟩ : syracuseStep 2178123 = 3267185) B3267185
theorem B2756693 : Blo 2177435 2756693 := bbase (se 8 (by rfl) ⟨16152, by rfl⟩ : syracuseStep 2756693 = 32305) (by norm_num)
theorem B7351181 : Blo 2177435 7351181 := bstep (se 3 (by rfl) ⟨1378346, by rfl⟩ : syracuseStep 7351181 = 2756693) B2756693
theorem B4900787 : Blo 2177435 4900787 := bstep (se 1 (by rfl) ⟨3675590, by rfl⟩ : syracuseStep 4900787 = 7351181) B7351181
theorem B3267191 : Blo 2177435 3267191 := bstep (se 1 (by rfl) ⟨2450393, by rfl⟩ : syracuseStep 3267191 = 4900787) B4900787
theorem B2178127 : Blo 2177435 2178127 := bstep (se 1 (by rfl) ⟨1633595, by rfl⟩ : syracuseStep 2178127 = 3267191) B3267191
theorem B3267197 : Blo 2177435 3267197 := bbase (se 3 (by rfl) ⟨612599, by rfl⟩ : syracuseStep 3267197 = 1225199) (by norm_num)
theorem B2178131 : Blo 2177435 2178131 := bstep (se 1 (by rfl) ⟨1633598, by rfl⟩ : syracuseStep 2178131 = 3267197) B3267197
theorem B4900805 : Blo 2177435 4900805 := bbase (se 4 (by rfl) ⟨459450, by rfl⟩ : syracuseStep 4900805 = 918901) (by norm_num)
theorem B3267203 : Blo 2177435 3267203 := bstep (se 1 (by rfl) ⟨2450402, by rfl⟩ : syracuseStep 3267203 = 4900805) B4900805
theorem B2178135 : Blo 2177435 2178135 := bstep (se 1 (by rfl) ⟨1633601, by rfl⟩ : syracuseStep 2178135 = 3267203) B3267203
theorem B9303893 : Blo 2177435 9303893 := bbase (se 9 (by rfl) ⟨27257, by rfl⟩ : syracuseStep 9303893 = 54515) (by norm_num)
theorem B6202595 : Blo 2177435 6202595 := bstep (se 1 (by rfl) ⟨4651946, by rfl⟩ : syracuseStep 6202595 = 9303893) B9303893
theorem B4135063 : Blo 2177435 4135063 := bstep (se 1 (by rfl) ⟨3101297, by rfl⟩ : syracuseStep 4135063 = 6202595) B6202595
theorem B5513417 : Blo 2177435 5513417 := bstep (se 2 (by rfl) ⟨2067531, by rfl⟩ : syracuseStep 5513417 = 4135063) B4135063
theorem B3675611 : Blo 2177435 3675611 := bstep (se 1 (by rfl) ⟨2756708, by rfl⟩ : syracuseStep 3675611 = 5513417) B5513417
theorem B2450407 : Blo 2177435 2450407 := bstep (se 1 (by rfl) ⟨1837805, by rfl⟩ : syracuseStep 2450407 = 3675611) B3675611
theorem B3267209 : Blo 2177435 3267209 := bstep (se 2 (by rfl) ⟨1225203, by rfl⟩ : syracuseStep 3267209 = 2450407) B2450407
theorem B2178139 : Blo 2177435 2178139 := bstep (se 1 (by rfl) ⟨1633604, by rfl⟩ : syracuseStep 2178139 = 3267209) B3267209
theorem B11026853 : Blo 2177435 11026853 := bbase (se 4 (by rfl) ⟨1033767, by rfl⟩ : syracuseStep 11026853 = 2067535) (by norm_num)
theorem B7351235 : Blo 2177435 7351235 := bstep (se 1 (by rfl) ⟨5513426, by rfl⟩ : syracuseStep 7351235 = 11026853) B11026853
theorem B4900823 : Blo 2177435 4900823 := bstep (se 1 (by rfl) ⟨3675617, by rfl⟩ : syracuseStep 4900823 = 7351235) B7351235
theorem B3267215 : Blo 2177435 3267215 := bstep (se 1 (by rfl) ⟨2450411, by rfl⟩ : syracuseStep 3267215 = 4900823) B4900823
theorem B2178143 : Blo 2177435 2178143 := bstep (se 1 (by rfl) ⟨1633607, by rfl⟩ : syracuseStep 2178143 = 3267215) B3267215
theorem B3267221 : Blo 2177435 3267221 := bbase (se 6 (by rfl) ⟨76575, by rfl⟩ : syracuseStep 3267221 = 153151) (by norm_num)
theorem B2178147 : Blo 2177435 2178147 := bstep (se 1 (by rfl) ⟨1633610, by rfl⟩ : syracuseStep 2178147 = 3267221) B3267221
theorem B15700405 : Blo 2177435 15700405 := bbase (se 5 (by rfl) ⟨735956, by rfl⟩ : syracuseStep 15700405 = 1471913) (by norm_num)
theorem B20933873 : Blo 2177435 20933873 := bstep (se 2 (by rfl) ⟨7850202, by rfl⟩ : syracuseStep 20933873 = 15700405) B15700405
theorem B13955915 : Blo 2177435 13955915 := bstep (se 1 (by rfl) ⟨10466936, by rfl⟩ : syracuseStep 13955915 = 20933873) B20933873
theorem B9303943 : Blo 2177435 9303943 := bstep (se 1 (by rfl) ⟨6977957, by rfl⟩ : syracuseStep 9303943 = 13955915) B13955915
theorem B12405257 : Blo 2177435 12405257 := bstep (se 2 (by rfl) ⟨4651971, by rfl⟩ : syracuseStep 12405257 = 9303943) B9303943
theorem B8270171 : Blo 2177435 8270171 := bstep (se 1 (by rfl) ⟨6202628, by rfl⟩ : syracuseStep 8270171 = 12405257) B12405257
theorem B5513447 : Blo 2177435 5513447 := bstep (se 1 (by rfl) ⟨4135085, by rfl⟩ : syracuseStep 5513447 = 8270171) B8270171
theorem B3675631 : Blo 2177435 3675631 := bstep (se 1 (by rfl) ⟨2756723, by rfl⟩ : syracuseStep 3675631 = 5513447) B5513447
theorem B4900841 : Blo 2177435 4900841 := bstep (se 2 (by rfl) ⟨1837815, by rfl⟩ : syracuseStep 4900841 = 3675631) B3675631
theorem B3267227 : Blo 2177435 3267227 := bstep (se 1 (by rfl) ⟨2450420, by rfl⟩ : syracuseStep 3267227 = 4900841) B4900841
theorem B2178151 : Blo 2177435 2178151 := bstep (se 1 (by rfl) ⟨1633613, by rfl⟩ : syracuseStep 2178151 = 3267227) B3267227
theorem B2450425 : Blo 2177435 2450425 := bbase (se 2 (by rfl) ⟨918909, by rfl⟩ : syracuseStep 2450425 = 1837819) (by norm_num)
theorem B3267233 : Blo 2177435 3267233 := bstep (se 2 (by rfl) ⟨1225212, by rfl⟩ : syracuseStep 3267233 = 2450425) B2450425
theorem B2178155 : Blo 2177435 2178155 := bstep (se 1 (by rfl) ⟨1633616, by rfl⟩ : syracuseStep 2178155 = 3267233) B3267233
theorem B10208405 : Blo 2177435 10208405 := bbase (se 6 (by rfl) ⟨239259, by rfl⟩ : syracuseStep 10208405 = 478519) (by norm_num)
theorem B6805603 : Blo 2177435 6805603 := bstep (se 1 (by rfl) ⟨5104202, by rfl⟩ : syracuseStep 6805603 = 10208405) B10208405
theorem B9074137 : Blo 2177435 9074137 := bstep (se 2 (by rfl) ⟨3402801, by rfl⟩ : syracuseStep 9074137 = 6805603) B6805603
theorem B12098849 : Blo 2177435 12098849 := bstep (se 2 (by rfl) ⟨4537068, by rfl⟩ : syracuseStep 12098849 = 9074137) B9074137
theorem B32263597 : Blo 2177435 32263597 := bstep (se 3 (by rfl) ⟨6049424, by rfl⟩ : syracuseStep 32263597 = 12098849) B12098849
theorem B43018129 : Blo 2177435 43018129 := bstep (se 2 (by rfl) ⟨16131798, by rfl⟩ : syracuseStep 43018129 = 32263597) B32263597
theorem B57357505 : Blo 2177435 57357505 := bstep (se 2 (by rfl) ⟨21509064, by rfl⟩ : syracuseStep 57357505 = 43018129) B43018129
theorem B76476673 : Blo 2177435 76476673 := bstep (se 2 (by rfl) ⟨28678752, by rfl⟩ : syracuseStep 76476673 = 57357505) B57357505
theorem B101968897 : Blo 2177435 101968897 := bstep (se 2 (by rfl) ⟨38238336, by rfl⟩ : syracuseStep 101968897 = 76476673) B76476673
theorem B135958529 : Blo 2177435 135958529 := bstep (se 2 (by rfl) ⟨50984448, by rfl⟩ : syracuseStep 135958529 = 101968897) B101968897
theorem B90639019 : Blo 2177435 90639019 := bstep (se 1 (by rfl) ⟨67979264, by rfl⟩ : syracuseStep 90639019 = 135958529) B135958529
theorem B483408101 : Blo 2177435 483408101 := bstep (se 4 (by rfl) ⟨45319509, by rfl⟩ : syracuseStep 483408101 = 90639019) B90639019
theorem B322272067 : Blo 2177435 322272067 := bstep (se 1 (by rfl) ⟨241704050, by rfl⟩ : syracuseStep 322272067 = 483408101) B483408101
theorem B429696089 : Blo 2177435 429696089 := bstep (se 2 (by rfl) ⟨161136033, by rfl⟩ : syracuseStep 429696089 = 322272067) B322272067
theorem B286464059 : Blo 2177435 286464059 := bstep (se 1 (by rfl) ⟨214848044, by rfl⟩ : syracuseStep 286464059 = 429696089) B429696089
theorem B190976039 : Blo 2177435 190976039 := bstep (se 1 (by rfl) ⟨143232029, by rfl⟩ : syracuseStep 190976039 = 286464059) B286464059
theorem B127317359 : Blo 2177435 127317359 := bstep (se 1 (by rfl) ⟨95488019, by rfl⟩ : syracuseStep 127317359 = 190976039) B190976039
theorem B339512957 : Blo 2177435 339512957 := bstep (se 3 (by rfl) ⟨63658679, by rfl⟩ : syracuseStep 339512957 = 127317359) B127317359
theorem B226341971 : Blo 2177435 226341971 := bstep (se 1 (by rfl) ⟨169756478, by rfl⟩ : syracuseStep 226341971 = 339512957) B339512957
theorem B150894647 : Blo 2177435 150894647 := bstep (se 1 (by rfl) ⟨113170985, by rfl⟩ : syracuseStep 150894647 = 226341971) B226341971
theorem B100596431 : Blo 2177435 100596431 := bstep (se 1 (by rfl) ⟨75447323, by rfl⟩ : syracuseStep 100596431 = 150894647) B150894647
theorem B67064287 : Blo 2177435 67064287 := bstep (se 1 (by rfl) ⟨50298215, by rfl⟩ : syracuseStep 67064287 = 100596431) B100596431
theorem B89419049 : Blo 2177435 89419049 := bstep (se 2 (by rfl) ⟨33532143, by rfl⟩ : syracuseStep 89419049 = 67064287) B67064287
theorem B59612699 : Blo 2177435 59612699 := bstep (se 1 (by rfl) ⟨44709524, by rfl⟩ : syracuseStep 59612699 = 89419049) B89419049
theorem B39741799 : Blo 2177435 39741799 := bstep (se 1 (by rfl) ⟨29806349, by rfl⟩ : syracuseStep 39741799 = 59612699) B59612699
theorem B52989065 : Blo 2177435 52989065 := bstep (se 2 (by rfl) ⟨19870899, by rfl⟩ : syracuseStep 52989065 = 39741799) B39741799
theorem B35326043 : Blo 2177435 35326043 := bstep (se 1 (by rfl) ⟨26494532, by rfl⟩ : syracuseStep 35326043 = 52989065) B52989065
theorem B23550695 : Blo 2177435 23550695 := bstep (se 1 (by rfl) ⟨17663021, by rfl⟩ : syracuseStep 23550695 = 35326043) B35326043
theorem B15700463 : Blo 2177435 15700463 := bstep (se 1 (by rfl) ⟨11775347, by rfl⟩ : syracuseStep 15700463 = 23550695) B23550695
theorem B10466975 : Blo 2177435 10466975 := bstep (se 1 (by rfl) ⟨7850231, by rfl⟩ : syracuseStep 10466975 = 15700463) B15700463
theorem B6977983 : Blo 2177435 6977983 := bstep (se 1 (by rfl) ⟨5233487, by rfl⟩ : syracuseStep 6977983 = 10466975) B10466975
theorem B9303977 : Blo 2177435 9303977 := bstep (se 2 (by rfl) ⟨3488991, by rfl⟩ : syracuseStep 9303977 = 6977983) B6977983
theorem B6202651 : Blo 2177435 6202651 := bstep (se 1 (by rfl) ⟨4651988, by rfl⟩ : syracuseStep 6202651 = 9303977) B9303977
theorem B8270201 : Blo 2177435 8270201 := bstep (se 2 (by rfl) ⟨3101325, by rfl⟩ : syracuseStep 8270201 = 6202651) B6202651
theorem B5513467 : Blo 2177435 5513467 := bstep (se 1 (by rfl) ⟨4135100, by rfl⟩ : syracuseStep 5513467 = 8270201) B8270201
theorem B7351289 : Blo 2177435 7351289 := bstep (se 2 (by rfl) ⟨2756733, by rfl⟩ : syracuseStep 7351289 = 5513467) B5513467
theorem B4900859 : Blo 2177435 4900859 := bstep (se 1 (by rfl) ⟨3675644, by rfl⟩ : syracuseStep 4900859 = 7351289) B7351289
theorem B3267239 : Blo 2177435 3267239 := bstep (se 1 (by rfl) ⟨2450429, by rfl⟩ : syracuseStep 3267239 = 4900859) B4900859
theorem B2178159 : Blo 2177435 2178159 := bstep (se 1 (by rfl) ⟨1633619, by rfl⟩ : syracuseStep 2178159 = 3267239) B3267239
theorem B3267245 : Blo 2177435 3267245 := bbase (se 3 (by rfl) ⟨612608, by rfl⟩ : syracuseStep 3267245 = 1225217) (by norm_num)
theorem B2178163 : Blo 2177435 2178163 := bstep (se 1 (by rfl) ⟨1633622, by rfl⟩ : syracuseStep 2178163 = 3267245) B3267245
theorem B4900877 : Blo 2177435 4900877 := bbase (se 3 (by rfl) ⟨918914, by rfl⟩ : syracuseStep 4900877 = 1837829) (by norm_num)
theorem B3267251 : Blo 2177435 3267251 := bstep (se 1 (by rfl) ⟨2450438, by rfl⟩ : syracuseStep 3267251 = 4900877) B4900877
theorem B2178167 : Blo 2177435 2178167 := bstep (se 1 (by rfl) ⟨1633625, by rfl⟩ : syracuseStep 2178167 = 3267251) B3267251
theorem B2756749 : Blo 2177435 2756749 := bbase (se 3 (by rfl) ⟨516890, by rfl⟩ : syracuseStep 2756749 = 1033781) (by norm_num)
theorem B3675665 : Blo 2177435 3675665 := bstep (se 2 (by rfl) ⟨1378374, by rfl⟩ : syracuseStep 3675665 = 2756749) B2756749
theorem B2450443 : Blo 2177435 2450443 := bstep (se 1 (by rfl) ⟨1837832, by rfl⟩ : syracuseStep 2450443 = 3675665) B3675665
theorem B3267257 : Blo 2177435 3267257 := bstep (se 2 (by rfl) ⟨1225221, by rfl⟩ : syracuseStep 3267257 = 2450443) B2450443
theorem B2178171 : Blo 2177435 2178171 := bstep (se 1 (by rfl) ⟨1633628, by rfl⟩ : syracuseStep 2178171 = 3267257) B3267257
theorem B20934101 : Blo 2177435 20934101 := bbase (se 7 (by rfl) ⟨245321, by rfl⟩ : syracuseStep 20934101 = 490643) (by norm_num)
theorem B13956067 : Blo 2177435 13956067 := bstep (se 1 (by rfl) ⟨10467050, by rfl⟩ : syracuseStep 13956067 = 20934101) B20934101
theorem B18608089 : Blo 2177435 18608089 := bstep (se 2 (by rfl) ⟨6978033, by rfl⟩ : syracuseStep 18608089 = 13956067) B13956067
theorem B24810785 : Blo 2177435 24810785 := bstep (se 2 (by rfl) ⟨9304044, by rfl⟩ : syracuseStep 24810785 = 18608089) B18608089
theorem B16540523 : Blo 2177435 16540523 := bstep (se 1 (by rfl) ⟨12405392, by rfl⟩ : syracuseStep 16540523 = 24810785) B24810785
theorem B11027015 : Blo 2177435 11027015 := bstep (se 1 (by rfl) ⟨8270261, by rfl⟩ : syracuseStep 11027015 = 16540523) B16540523
theorem B7351343 : Blo 2177435 7351343 := bstep (se 1 (by rfl) ⟨5513507, by rfl⟩ : syracuseStep 7351343 = 11027015) B11027015
theorem B4900895 : Blo 2177435 4900895 := bstep (se 1 (by rfl) ⟨3675671, by rfl⟩ : syracuseStep 4900895 = 7351343) B7351343
theorem B3267263 : Blo 2177435 3267263 := bstep (se 1 (by rfl) ⟨2450447, by rfl⟩ : syracuseStep 3267263 = 4900895) B4900895
theorem B2178175 : Blo 2177435 2178175 := bstep (se 1 (by rfl) ⟨1633631, by rfl⟩ : syracuseStep 2178175 = 3267263) B3267263
theorem B3267269 : Blo 2177435 3267269 := bbase (se 4 (by rfl) ⟨306306, by rfl⟩ : syracuseStep 3267269 = 612613) (by norm_num)
theorem B2178179 : Blo 2177435 2178179 := bstep (se 1 (by rfl) ⟨1633634, by rfl⟩ : syracuseStep 2178179 = 3267269) B3267269
theorem B3675685 : Blo 2177435 3675685 := bbase (se 4 (by rfl) ⟨344595, by rfl⟩ : syracuseStep 3675685 = 689191) (by norm_num)
theorem B4900913 : Blo 2177435 4900913 := bstep (se 2 (by rfl) ⟨1837842, by rfl⟩ : syracuseStep 4900913 = 3675685) B3675685
theorem B3267275 : Blo 2177435 3267275 := bstep (se 1 (by rfl) ⟨2450456, by rfl⟩ : syracuseStep 3267275 = 4900913) B4900913
theorem B2178183 : Blo 2177435 2178183 := bstep (se 1 (by rfl) ⟨1633637, by rfl⟩ : syracuseStep 2178183 = 3267275) B3267275
theorem B2450461 : Blo 2177435 2450461 := bbase (se 3 (by rfl) ⟨459461, by rfl⟩ : syracuseStep 2450461 = 918923) (by norm_num)
theorem B3267281 : Blo 2177435 3267281 := bstep (se 2 (by rfl) ⟨1225230, by rfl⟩ : syracuseStep 3267281 = 2450461) B2450461
theorem B2178187 : Blo 2177435 2178187 := bstep (se 1 (by rfl) ⟨1633640, by rfl⟩ : syracuseStep 2178187 = 3267281) B3267281
theorem B7351397 : Blo 2177435 7351397 := bbase (se 4 (by rfl) ⟨689193, by rfl⟩ : syracuseStep 7351397 = 1378387) (by norm_num)
theorem B4900931 : Blo 2177435 4900931 := bstep (se 1 (by rfl) ⟨3675698, by rfl⟩ : syracuseStep 4900931 = 7351397) B7351397
theorem B3267287 : Blo 2177435 3267287 := bstep (se 1 (by rfl) ⟨2450465, by rfl⟩ : syracuseStep 3267287 = 4900931) B4900931
theorem B2178191 : Blo 2177435 2178191 := bstep (se 1 (by rfl) ⟨1633643, by rfl⟩ : syracuseStep 2178191 = 3267287) B3267287
theorem B3267293 : Blo 2177435 3267293 := bbase (se 3 (by rfl) ⟨612617, by rfl⟩ : syracuseStep 3267293 = 1225235) (by norm_num)
theorem B2178195 : Blo 2177435 2178195 := bstep (se 1 (by rfl) ⟨1633646, by rfl⟩ : syracuseStep 2178195 = 3267293) B3267293
theorem B4900949 : Blo 2177435 4900949 := bbase (se 8 (by rfl) ⟨28716, by rfl⟩ : syracuseStep 4900949 = 57433) (by norm_num)
theorem B3267299 : Blo 2177435 3267299 := bstep (se 1 (by rfl) ⟨2450474, by rfl⟩ : syracuseStep 3267299 = 4900949) B4900949
theorem B2178199 : Blo 2177435 2178199 := bstep (se 1 (by rfl) ⟨1633649, by rfl⟩ : syracuseStep 2178199 = 3267299) B3267299
theorem B2616797 : Blo 2177435 2616797 := bbase (se 3 (by rfl) ⟨490649, by rfl⟩ : syracuseStep 2616797 = 981299) (by norm_num)
theorem B6978125 : Blo 2177435 6978125 := bstep (se 3 (by rfl) ⟨1308398, by rfl⟩ : syracuseStep 6978125 = 2616797) B2616797
theorem B4652083 : Blo 2177435 4652083 := bstep (se 1 (by rfl) ⟨3489062, by rfl⟩ : syracuseStep 4652083 = 6978125) B6978125
theorem B6202777 : Blo 2177435 6202777 := bstep (se 2 (by rfl) ⟨2326041, by rfl⟩ : syracuseStep 6202777 = 4652083) B4652083
theorem B8270369 : Blo 2177435 8270369 := bstep (se 2 (by rfl) ⟨3101388, by rfl⟩ : syracuseStep 8270369 = 6202777) B6202777
theorem B5513579 : Blo 2177435 5513579 := bstep (se 1 (by rfl) ⟨4135184, by rfl⟩ : syracuseStep 5513579 = 8270369) B8270369
theorem B3675719 : Blo 2177435 3675719 := bstep (se 1 (by rfl) ⟨2756789, by rfl⟩ : syracuseStep 3675719 = 5513579) B5513579
theorem B2450479 : Blo 2177435 2450479 := bstep (se 1 (by rfl) ⟨1837859, by rfl⟩ : syracuseStep 2450479 = 3675719) B3675719
theorem B3267305 : Blo 2177435 3267305 := bstep (se 2 (by rfl) ⟨1225239, by rfl⟩ : syracuseStep 3267305 = 2450479) B2450479
theorem B2178203 : Blo 2177435 2178203 := bstep (se 1 (by rfl) ⟨1633652, by rfl⟩ : syracuseStep 2178203 = 3267305) B3267305
theorem B6714149 : Blo 2177435 6714149 := bbase (se 4 (by rfl) ⟨629451, by rfl⟩ : syracuseStep 6714149 = 1258903) (by norm_num)
theorem B17904397 : Blo 2177435 17904397 := bstep (se 3 (by rfl) ⟨3357074, by rfl⟩ : syracuseStep 17904397 = 6714149) B6714149
theorem B23872529 : Blo 2177435 23872529 := bstep (se 2 (by rfl) ⟨8952198, by rfl⟩ : syracuseStep 23872529 = 17904397) B17904397
theorem B63660077 : Blo 2177435 63660077 := bstep (se 3 (by rfl) ⟨11936264, by rfl⟩ : syracuseStep 63660077 = 23872529) B23872529
theorem B42440051 : Blo 2177435 42440051 := bstep (se 1 (by rfl) ⟨31830038, by rfl⟩ : syracuseStep 42440051 = 63660077) B63660077
theorem B113173469 : Blo 2177435 113173469 := bstep (se 3 (by rfl) ⟨21220025, by rfl⟩ : syracuseStep 113173469 = 42440051) B42440051
theorem B75448979 : Blo 2177435 75448979 := bstep (se 1 (by rfl) ⟨56586734, by rfl⟩ : syracuseStep 75448979 = 113173469) B113173469
theorem B50299319 : Blo 2177435 50299319 := bstep (se 1 (by rfl) ⟨37724489, by rfl⟩ : syracuseStep 50299319 = 75448979) B75448979
theorem B33532879 : Blo 2177435 33532879 := bstep (se 1 (by rfl) ⟨25149659, by rfl⟩ : syracuseStep 33532879 = 50299319) B50299319
theorem B44710505 : Blo 2177435 44710505 := bstep (se 2 (by rfl) ⟨16766439, by rfl⟩ : syracuseStep 44710505 = 33532879) B33532879
theorem B29807003 : Blo 2177435 29807003 := bstep (se 1 (by rfl) ⟨22355252, by rfl⟩ : syracuseStep 29807003 = 44710505) B44710505
theorem B19871335 : Blo 2177435 19871335 := bstep (se 1 (by rfl) ⟨14903501, by rfl⟩ : syracuseStep 19871335 = 29807003) B29807003
theorem B26495113 : Blo 2177435 26495113 := bstep (se 2 (by rfl) ⟨9935667, by rfl⟩ : syracuseStep 26495113 = 19871335) B19871335
theorem B35326817 : Blo 2177435 35326817 := bstep (se 2 (by rfl) ⟨13247556, by rfl⟩ : syracuseStep 35326817 = 26495113) B26495113
theorem B23551211 : Blo 2177435 23551211 := bstep (se 1 (by rfl) ⟨17663408, by rfl⟩ : syracuseStep 23551211 = 35326817) B35326817
theorem B15700807 : Blo 2177435 15700807 := bstep (se 1 (by rfl) ⟨11775605, by rfl⟩ : syracuseStep 15700807 = 23551211) B23551211
theorem B20934409 : Blo 2177435 20934409 := bstep (se 2 (by rfl) ⟨7850403, by rfl⟩ : syracuseStep 20934409 = 15700807) B15700807
theorem B27912545 : Blo 2177435 27912545 := bstep (se 2 (by rfl) ⟨10467204, by rfl⟩ : syracuseStep 27912545 = 20934409) B20934409
theorem B18608363 : Blo 2177435 18608363 := bstep (se 1 (by rfl) ⟨13956272, by rfl⟩ : syracuseStep 18608363 = 27912545) B27912545
theorem B12405575 : Blo 2177435 12405575 := bstep (se 1 (by rfl) ⟨9304181, by rfl⟩ : syracuseStep 12405575 = 18608363) B18608363
theorem B8270383 : Blo 2177435 8270383 := bstep (se 1 (by rfl) ⟨6202787, by rfl⟩ : syracuseStep 8270383 = 12405575) B12405575
theorem B11027177 : Blo 2177435 11027177 := bstep (se 2 (by rfl) ⟨4135191, by rfl⟩ : syracuseStep 11027177 = 8270383) B8270383
theorem B7351451 : Blo 2177435 7351451 := bstep (se 1 (by rfl) ⟨5513588, by rfl⟩ : syracuseStep 7351451 = 11027177) B11027177
theorem B4900967 : Blo 2177435 4900967 := bstep (se 1 (by rfl) ⟨3675725, by rfl⟩ : syracuseStep 4900967 = 7351451) B7351451
theorem B3267311 : Blo 2177435 3267311 := bstep (se 1 (by rfl) ⟨2450483, by rfl⟩ : syracuseStep 3267311 = 4900967) B4900967
theorem B2178207 : Blo 2177435 2178207 := bstep (se 1 (by rfl) ⟨1633655, by rfl⟩ : syracuseStep 2178207 = 3267311) B3267311
theorem B3267317 : Blo 2177435 3267317 := bbase (se 5 (by rfl) ⟨153155, by rfl⟩ : syracuseStep 3267317 = 306311) (by norm_num)
theorem B2178211 : Blo 2177435 2178211 := bstep (se 1 (by rfl) ⟨1633658, by rfl⟩ : syracuseStep 2178211 = 3267317) B3267317
theorem B6714181 : Blo 2177435 6714181 := bbase (se 4 (by rfl) ⟨629454, by rfl⟩ : syracuseStep 6714181 = 1258909) (by norm_num)
theorem B8952241 : Blo 2177435 8952241 := bstep (se 2 (by rfl) ⟨3357090, by rfl⟩ : syracuseStep 8952241 = 6714181) B6714181
theorem B11936321 : Blo 2177435 11936321 := bstep (se 2 (by rfl) ⟨4476120, by rfl⟩ : syracuseStep 11936321 = 8952241) B8952241
theorem B7957547 : Blo 2177435 7957547 := bstep (se 1 (by rfl) ⟨5968160, by rfl⟩ : syracuseStep 7957547 = 11936321) B11936321
theorem B5305031 : Blo 2177435 5305031 := bstep (se 1 (by rfl) ⟨3978773, by rfl⟩ : syracuseStep 5305031 = 7957547) B7957547
theorem B3536687 : Blo 2177435 3536687 := bstep (se 1 (by rfl) ⟨2652515, by rfl⟩ : syracuseStep 3536687 = 5305031) B5305031
theorem B2357791 : Blo 2177435 2357791 := bstep (se 1 (by rfl) ⟨1768343, by rfl⟩ : syracuseStep 2357791 = 3536687) B3536687
theorem B12574885 : Blo 2177435 12574885 := bstep (se 4 (by rfl) ⟨1178895, by rfl⟩ : syracuseStep 12574885 = 2357791) B2357791
theorem B16766513 : Blo 2177435 16766513 := bstep (se 2 (by rfl) ⟨6287442, by rfl⟩ : syracuseStep 16766513 = 12574885) B12574885
theorem B11177675 : Blo 2177435 11177675 := bstep (se 1 (by rfl) ⟨8383256, by rfl⟩ : syracuseStep 11177675 = 16766513) B16766513
theorem B7451783 : Blo 2177435 7451783 := bstep (se 1 (by rfl) ⟨5588837, by rfl⟩ : syracuseStep 7451783 = 11177675) B11177675
theorem B4967855 : Blo 2177435 4967855 := bstep (se 1 (by rfl) ⟨3725891, by rfl⟩ : syracuseStep 4967855 = 7451783) B7451783
theorem B3311903 : Blo 2177435 3311903 := bstep (se 1 (by rfl) ⟨2483927, by rfl⟩ : syracuseStep 3311903 = 4967855) B4967855
theorem B2207935 : Blo 2177435 2207935 := bstep (se 1 (by rfl) ⟨1655951, by rfl⟩ : syracuseStep 2207935 = 3311903) B3311903
theorem B2943913 : Blo 2177435 2943913 := bstep (se 2 (by rfl) ⟨1103967, by rfl⟩ : syracuseStep 2943913 = 2207935) B2207935
theorem B3925217 : Blo 2177435 3925217 := bstep (se 2 (by rfl) ⟨1471956, by rfl⟩ : syracuseStep 3925217 = 2943913) B2943913
theorem B10467245 : Blo 2177435 10467245 := bstep (se 3 (by rfl) ⟨1962608, by rfl⟩ : syracuseStep 10467245 = 3925217) B3925217
theorem B6978163 : Blo 2177435 6978163 := bstep (se 1 (by rfl) ⟨5233622, by rfl⟩ : syracuseStep 6978163 = 10467245) B10467245
theorem B9304217 : Blo 2177435 9304217 := bstep (se 2 (by rfl) ⟨3489081, by rfl⟩ : syracuseStep 9304217 = 6978163) B6978163
theorem B6202811 : Blo 2177435 6202811 := bstep (se 1 (by rfl) ⟨4652108, by rfl⟩ : syracuseStep 6202811 = 9304217) B9304217
theorem B4135207 : Blo 2177435 4135207 := bstep (se 1 (by rfl) ⟨3101405, by rfl⟩ : syracuseStep 4135207 = 6202811) B6202811
theorem B5513609 : Blo 2177435 5513609 := bstep (se 2 (by rfl) ⟨2067603, by rfl⟩ : syracuseStep 5513609 = 4135207) B4135207
theorem B3675739 : Blo 2177435 3675739 := bstep (se 1 (by rfl) ⟨2756804, by rfl⟩ : syracuseStep 3675739 = 5513609) B5513609
theorem B4900985 : Blo 2177435 4900985 := bstep (se 2 (by rfl) ⟨1837869, by rfl⟩ : syracuseStep 4900985 = 3675739) B3675739
theorem B3267323 : Blo 2177435 3267323 := bstep (se 1 (by rfl) ⟨2450492, by rfl⟩ : syracuseStep 3267323 = 4900985) B4900985
theorem B2178215 : Blo 2177435 2178215 := bstep (se 1 (by rfl) ⟨1633661, by rfl⟩ : syracuseStep 2178215 = 3267323) B3267323
theorem B2450497 : Blo 2177435 2450497 := bbase (se 2 (by rfl) ⟨918936, by rfl⟩ : syracuseStep 2450497 = 1837873) (by norm_num)
theorem B3267329 : Blo 2177435 3267329 := bstep (se 2 (by rfl) ⟨1225248, by rfl⟩ : syracuseStep 3267329 = 2450497) B2450497
theorem B2178219 : Blo 2177435 2178219 := bstep (se 1 (by rfl) ⟨1633664, by rfl⟩ : syracuseStep 2178219 = 3267329) B3267329
theorem B5513629 : Blo 2177435 5513629 := bbase (se 3 (by rfl) ⟨1033805, by rfl⟩ : syracuseStep 5513629 = 2067611) (by norm_num)
theorem B7351505 : Blo 2177435 7351505 := bstep (se 2 (by rfl) ⟨2756814, by rfl⟩ : syracuseStep 7351505 = 5513629) B5513629
theorem B4901003 : Blo 2177435 4901003 := bstep (se 1 (by rfl) ⟨3675752, by rfl⟩ : syracuseStep 4901003 = 7351505) B7351505
theorem B3267335 : Blo 2177435 3267335 := bstep (se 1 (by rfl) ⟨2450501, by rfl⟩ : syracuseStep 3267335 = 4901003) B4901003
theorem B2178223 : Blo 2177435 2178223 := bstep (se 1 (by rfl) ⟨1633667, by rfl⟩ : syracuseStep 2178223 = 3267335) B3267335
theorem B3267341 : Blo 2177435 3267341 := bbase (se 3 (by rfl) ⟨612626, by rfl⟩ : syracuseStep 3267341 = 1225253) (by norm_num)
theorem B2178227 : Blo 2177435 2178227 := bstep (se 1 (by rfl) ⟨1633670, by rfl⟩ : syracuseStep 2178227 = 3267341) B3267341
theorem B4901021 : Blo 2177435 4901021 := bbase (se 3 (by rfl) ⟨918941, by rfl⟩ : syracuseStep 4901021 = 1837883) (by norm_num)
theorem B3267347 : Blo 2177435 3267347 := bstep (se 1 (by rfl) ⟨2450510, by rfl⟩ : syracuseStep 3267347 = 4901021) B4901021
theorem B2178231 : Blo 2177435 2178231 := bstep (se 1 (by rfl) ⟨1633673, by rfl⟩ : syracuseStep 2178231 = 3267347) B3267347
theorem B3675773 : Blo 2177435 3675773 := bbase (se 3 (by rfl) ⟨689207, by rfl⟩ : syracuseStep 3675773 = 1378415) (by norm_num)
theorem B2450515 : Blo 2177435 2450515 := bstep (se 1 (by rfl) ⟨1837886, by rfl⟩ : syracuseStep 2450515 = 3675773) B3675773
theorem B3267353 : Blo 2177435 3267353 := bstep (se 2 (by rfl) ⟨1225257, by rfl⟩ : syracuseStep 3267353 = 2450515) B2450515
theorem B2178235 : Blo 2177435 2178235 := bstep (se 1 (by rfl) ⟨1633676, by rfl⟩ : syracuseStep 2178235 = 3267353) B3267353
theorem B3776765 : Blo 2177435 3776765 := bbase (se 3 (by rfl) ⟨708143, by rfl⟩ : syracuseStep 3776765 = 1416287) (by norm_num)
theorem B10071373 : Blo 2177435 10071373 := bstep (se 3 (by rfl) ⟨1888382, by rfl⟩ : syracuseStep 10071373 = 3776765) B3776765
theorem B13428497 : Blo 2177435 13428497 := bstep (se 2 (by rfl) ⟨5035686, by rfl⟩ : syracuseStep 13428497 = 10071373) B10071373
theorem B8952331 : Blo 2177435 8952331 := bstep (se 1 (by rfl) ⟨6714248, by rfl⟩ : syracuseStep 8952331 = 13428497) B13428497
theorem B11936441 : Blo 2177435 11936441 := bstep (se 2 (by rfl) ⟨4476165, by rfl⟩ : syracuseStep 11936441 = 8952331) B8952331
theorem B31830509 : Blo 2177435 31830509 := bstep (se 3 (by rfl) ⟨5968220, by rfl⟩ : syracuseStep 31830509 = 11936441) B11936441
theorem B84881357 : Blo 2177435 84881357 := bstep (se 3 (by rfl) ⟨15915254, by rfl⟩ : syracuseStep 84881357 = 31830509) B31830509
theorem B56587571 : Blo 2177435 56587571 := bstep (se 1 (by rfl) ⟨42440678, by rfl⟩ : syracuseStep 56587571 = 84881357) B84881357
theorem B37725047 : Blo 2177435 37725047 := bstep (se 1 (by rfl) ⟨28293785, by rfl⟩ : syracuseStep 37725047 = 56587571) B56587571
theorem B25150031 : Blo 2177435 25150031 := bstep (se 1 (by rfl) ⟨18862523, by rfl⟩ : syracuseStep 25150031 = 37725047) B37725047
theorem B16766687 : Blo 2177435 16766687 := bstep (se 1 (by rfl) ⟨12575015, by rfl⟩ : syracuseStep 16766687 = 25150031) B25150031
theorem B44711165 : Blo 2177435 44711165 := bstep (se 3 (by rfl) ⟨8383343, by rfl⟩ : syracuseStep 44711165 = 16766687) B16766687
theorem B29807443 : Blo 2177435 29807443 := bstep (se 1 (by rfl) ⟨22355582, by rfl⟩ : syracuseStep 29807443 = 44711165) B44711165
theorem B39743257 : Blo 2177435 39743257 := bstep (se 2 (by rfl) ⟨14903721, by rfl⟩ : syracuseStep 39743257 = 29807443) B29807443
theorem B52991009 : Blo 2177435 52991009 := bstep (se 2 (by rfl) ⟨19871628, by rfl⟩ : syracuseStep 52991009 = 39743257) B39743257
theorem B35327339 : Blo 2177435 35327339 := bstep (se 1 (by rfl) ⟨26495504, by rfl⟩ : syracuseStep 35327339 = 52991009) B52991009
theorem B23551559 : Blo 2177435 23551559 := bstep (se 1 (by rfl) ⟨17663669, by rfl⟩ : syracuseStep 23551559 = 35327339) B35327339
theorem B15701039 : Blo 2177435 15701039 := bstep (se 1 (by rfl) ⟨11775779, by rfl⟩ : syracuseStep 15701039 = 23551559) B23551559
theorem B10467359 : Blo 2177435 10467359 := bstep (se 1 (by rfl) ⟨7850519, by rfl⟩ : syracuseStep 10467359 = 15701039) B15701039
theorem B6978239 : Blo 2177435 6978239 := bstep (se 1 (by rfl) ⟨5233679, by rfl⟩ : syracuseStep 6978239 = 10467359) B10467359
theorem B4652159 : Blo 2177435 4652159 := bstep (se 1 (by rfl) ⟨3489119, by rfl⟩ : syracuseStep 4652159 = 6978239) B6978239
theorem B12405757 : Blo 2177435 12405757 := bstep (se 3 (by rfl) ⟨2326079, by rfl⟩ : syracuseStep 12405757 = 4652159) B4652159
theorem B16541009 : Blo 2177435 16541009 := bstep (se 2 (by rfl) ⟨6202878, by rfl⟩ : syracuseStep 16541009 = 12405757) B12405757
theorem B11027339 : Blo 2177435 11027339 := bstep (se 1 (by rfl) ⟨8270504, by rfl⟩ : syracuseStep 11027339 = 16541009) B16541009
theorem B7351559 : Blo 2177435 7351559 := bstep (se 1 (by rfl) ⟨5513669, by rfl⟩ : syracuseStep 7351559 = 11027339) B11027339
theorem B4901039 : Blo 2177435 4901039 := bstep (se 1 (by rfl) ⟨3675779, by rfl⟩ : syracuseStep 4901039 = 7351559) B7351559
theorem B3267359 : Blo 2177435 3267359 := bstep (se 1 (by rfl) ⟨2450519, by rfl⟩ : syracuseStep 3267359 = 4901039) B4901039
theorem B2178239 : Blo 2177435 2178239 := bstep (se 1 (by rfl) ⟨1633679, by rfl⟩ : syracuseStep 2178239 = 3267359) B3267359
theorem B3267365 : Blo 2177435 3267365 := bbase (se 4 (by rfl) ⟨306315, by rfl⟩ : syracuseStep 3267365 = 612631) (by norm_num)
theorem B2178243 : Blo 2177435 2178243 := bstep (se 1 (by rfl) ⟨1633682, by rfl⟩ : syracuseStep 2178243 = 3267365) B3267365
theorem B2756845 : Blo 2177435 2756845 := bbase (se 3 (by rfl) ⟨516908, by rfl⟩ : syracuseStep 2756845 = 1033817) (by norm_num)
theorem B3675793 : Blo 2177435 3675793 := bstep (se 2 (by rfl) ⟨1378422, by rfl⟩ : syracuseStep 3675793 = 2756845) B2756845
theorem B4901057 : Blo 2177435 4901057 := bstep (se 2 (by rfl) ⟨1837896, by rfl⟩ : syracuseStep 4901057 = 3675793) B3675793
theorem B3267371 : Blo 2177435 3267371 := bstep (se 1 (by rfl) ⟨2450528, by rfl⟩ : syracuseStep 3267371 = 4901057) B4901057
theorem B2178247 : Blo 2177435 2178247 := bstep (se 1 (by rfl) ⟨1633685, by rfl⟩ : syracuseStep 2178247 = 3267371) B3267371
theorem B2450533 : Blo 2177435 2450533 := bbase (se 4 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 2450533 = 459475) (by norm_num)
theorem B3267377 : Blo 2177435 3267377 := bstep (se 2 (by rfl) ⟨1225266, by rfl⟩ : syracuseStep 3267377 = 2450533) B2450533
theorem B2178251 : Blo 2177435 2178251 := bstep (se 1 (by rfl) ⟨1633688, by rfl⟩ : syracuseStep 2178251 = 3267377) B3267377
theorem B2326097 : Blo 2177435 2326097 := bbase (se 2 (by rfl) ⟨872286, by rfl⟩ : syracuseStep 2326097 = 1744573) (by norm_num)
theorem B6202925 : Blo 2177435 6202925 := bstep (se 3 (by rfl) ⟨1163048, by rfl⟩ : syracuseStep 6202925 = 2326097) B2326097
theorem B4135283 : Blo 2177435 4135283 := bstep (se 1 (by rfl) ⟨3101462, by rfl⟩ : syracuseStep 4135283 = 6202925) B6202925
theorem B2756855 : Blo 2177435 2756855 := bstep (se 1 (by rfl) ⟨2067641, by rfl⟩ : syracuseStep 2756855 = 4135283) B4135283
theorem B7351613 : Blo 2177435 7351613 := bstep (se 3 (by rfl) ⟨1378427, by rfl⟩ : syracuseStep 7351613 = 2756855) B2756855
theorem B4901075 : Blo 2177435 4901075 := bstep (se 1 (by rfl) ⟨3675806, by rfl⟩ : syracuseStep 4901075 = 7351613) B7351613
theorem B3267383 : Blo 2177435 3267383 := bstep (se 1 (by rfl) ⟨2450537, by rfl⟩ : syracuseStep 3267383 = 4901075) B4901075
theorem B2178255 : Blo 2177435 2178255 := bstep (se 1 (by rfl) ⟨1633691, by rfl⟩ : syracuseStep 2178255 = 3267383) B3267383
theorem B3267389 : Blo 2177435 3267389 := bbase (se 3 (by rfl) ⟨612635, by rfl⟩ : syracuseStep 3267389 = 1225271) (by norm_num)
theorem B2178259 : Blo 2177435 2178259 := bstep (se 1 (by rfl) ⟨1633694, by rfl⟩ : syracuseStep 2178259 = 3267389) B3267389
theorem B4901093 : Blo 2177435 4901093 := bbase (se 4 (by rfl) ⟨459477, by rfl⟩ : syracuseStep 4901093 = 918955) (by norm_num)
theorem B3267395 : Blo 2177435 3267395 := bstep (se 1 (by rfl) ⟨2450546, by rfl⟩ : syracuseStep 3267395 = 4901093) B4901093
theorem B2178263 : Blo 2177435 2178263 := bstep (se 1 (by rfl) ⟨1633697, by rfl⟩ : syracuseStep 2178263 = 3267395) B3267395
theorem B5513741 : Blo 2177435 5513741 := bbase (se 3 (by rfl) ⟨1033826, by rfl⟩ : syracuseStep 5513741 = 2067653) (by norm_num)
theorem B3675827 : Blo 2177435 3675827 := bstep (se 1 (by rfl) ⟨2756870, by rfl⟩ : syracuseStep 3675827 = 5513741) B5513741
theorem B2450551 : Blo 2177435 2450551 := bstep (se 1 (by rfl) ⟨1837913, by rfl⟩ : syracuseStep 2450551 = 3675827) B3675827
theorem B3267401 : Blo 2177435 3267401 := bstep (se 2 (by rfl) ⟨1225275, by rfl⟩ : syracuseStep 3267401 = 2450551) B2450551
theorem B2178267 : Blo 2177435 2178267 := bstep (se 1 (by rfl) ⟨1633700, by rfl⟩ : syracuseStep 2178267 = 3267401) B3267401
theorem B3101485 : Blo 2177435 3101485 := bbase (se 3 (by rfl) ⟨581528, by rfl⟩ : syracuseStep 3101485 = 1163057) (by norm_num)
theorem B4135313 : Blo 2177435 4135313 := bstep (se 2 (by rfl) ⟨1550742, by rfl⟩ : syracuseStep 4135313 = 3101485) B3101485
theorem B11027501 : Blo 2177435 11027501 := bstep (se 3 (by rfl) ⟨2067656, by rfl⟩ : syracuseStep 11027501 = 4135313) B4135313
theorem B7351667 : Blo 2177435 7351667 := bstep (se 1 (by rfl) ⟨5513750, by rfl⟩ : syracuseStep 7351667 = 11027501) B11027501
theorem B4901111 : Blo 2177435 4901111 := bstep (se 1 (by rfl) ⟨3675833, by rfl⟩ : syracuseStep 4901111 = 7351667) B7351667
theorem B3267407 : Blo 2177435 3267407 := bstep (se 1 (by rfl) ⟨2450555, by rfl⟩ : syracuseStep 3267407 = 4901111) B4901111
theorem B2178271 : Blo 2177435 2178271 := bstep (se 1 (by rfl) ⟨1633703, by rfl⟩ : syracuseStep 2178271 = 3267407) B3267407
theorem B3267413 : Blo 2177435 3267413 := bbase (se 9 (by rfl) ⟨9572, by rfl⟩ : syracuseStep 3267413 = 19145) (by norm_num)
theorem B2178275 : Blo 2177435 2178275 := bstep (se 1 (by rfl) ⟨1633706, by rfl⟩ : syracuseStep 2178275 = 3267413) B3267413
theorem B4652245 : Blo 2177435 4652245 := bbase (se 7 (by rfl) ⟨54518, by rfl⟩ : syracuseStep 4652245 = 109037) (by norm_num)
theorem B6202993 : Blo 2177435 6202993 := bstep (se 2 (by rfl) ⟨2326122, by rfl⟩ : syracuseStep 6202993 = 4652245) B4652245
theorem B8270657 : Blo 2177435 8270657 := bstep (se 2 (by rfl) ⟨3101496, by rfl⟩ : syracuseStep 8270657 = 6202993) B6202993
theorem B5513771 : Blo 2177435 5513771 := bstep (se 1 (by rfl) ⟨4135328, by rfl⟩ : syracuseStep 5513771 = 8270657) B8270657
theorem B3675847 : Blo 2177435 3675847 := bstep (se 1 (by rfl) ⟨2756885, by rfl⟩ : syracuseStep 3675847 = 5513771) B5513771
theorem B4901129 : Blo 2177435 4901129 := bstep (se 2 (by rfl) ⟨1837923, by rfl⟩ : syracuseStep 4901129 = 3675847) B3675847
theorem B3267419 : Blo 2177435 3267419 := bstep (se 1 (by rfl) ⟨2450564, by rfl⟩ : syracuseStep 3267419 = 4901129) B4901129
theorem B2178279 : Blo 2177435 2178279 := bstep (se 1 (by rfl) ⟨1633709, by rfl⟩ : syracuseStep 2178279 = 3267419) B3267419
theorem B2450569 : Blo 2177435 2450569 := bbase (se 2 (by rfl) ⟨918963, by rfl⟩ : syracuseStep 2450569 = 1837927) (by norm_num)
theorem B3267425 : Blo 2177435 3267425 := bstep (se 2 (by rfl) ⟨1225284, by rfl⟩ : syracuseStep 3267425 = 2450569) B2450569
theorem B2178283 : Blo 2177435 2178283 := bstep (se 1 (by rfl) ⟨1633712, by rfl⟩ : syracuseStep 2178283 = 3267425) B3267425
theorem B41870357 : Blo 2177435 41870357 := bbase (se 6 (by rfl) ⟨981336, by rfl⟩ : syracuseStep 41870357 = 1962673) (by norm_num)
theorem B27913571 : Blo 2177435 27913571 := bstep (se 1 (by rfl) ⟨20935178, by rfl⟩ : syracuseStep 27913571 = 41870357) B41870357
theorem B18609047 : Blo 2177435 18609047 := bstep (se 1 (by rfl) ⟨13956785, by rfl⟩ : syracuseStep 18609047 = 27913571) B27913571
theorem B12406031 : Blo 2177435 12406031 := bstep (se 1 (by rfl) ⟨9304523, by rfl⟩ : syracuseStep 12406031 = 18609047) B18609047
theorem B8270687 : Blo 2177435 8270687 := bstep (se 1 (by rfl) ⟨6203015, by rfl⟩ : syracuseStep 8270687 = 12406031) B12406031
theorem B5513791 : Blo 2177435 5513791 := bstep (se 1 (by rfl) ⟨4135343, by rfl⟩ : syracuseStep 5513791 = 8270687) B8270687
theorem B7351721 : Blo 2177435 7351721 := bstep (se 2 (by rfl) ⟨2756895, by rfl⟩ : syracuseStep 7351721 = 5513791) B5513791
theorem B4901147 : Blo 2177435 4901147 := bstep (se 1 (by rfl) ⟨3675860, by rfl⟩ : syracuseStep 4901147 = 7351721) B7351721
theorem B3267431 : Blo 2177435 3267431 := bstep (se 1 (by rfl) ⟨2450573, by rfl⟩ : syracuseStep 3267431 = 4901147) B4901147
theorem B2178287 : Blo 2177435 2178287 := bstep (se 1 (by rfl) ⟨1633715, by rfl⟩ : syracuseStep 2178287 = 3267431) B3267431
theorem B3267437 : Blo 2177435 3267437 := bbase (se 3 (by rfl) ⟨612644, by rfl⟩ : syracuseStep 3267437 = 1225289) (by norm_num)
theorem B2178291 : Blo 2177435 2178291 := bstep (se 1 (by rfl) ⟨1633718, by rfl⟩ : syracuseStep 2178291 = 3267437) B3267437
theorem B4901165 : Blo 2177435 4901165 := bbase (se 3 (by rfl) ⟨918968, by rfl⟩ : syracuseStep 4901165 = 1837937) (by norm_num)
theorem B3267443 : Blo 2177435 3267443 := bstep (se 1 (by rfl) ⟨2450582, by rfl⟩ : syracuseStep 3267443 = 4901165) B4901165
theorem B2178295 : Blo 2177435 2178295 := bstep (se 1 (by rfl) ⟨1633721, by rfl⟩ : syracuseStep 2178295 = 3267443) B3267443
theorem B4476293 : Blo 2177435 4476293 := bbase (se 4 (by rfl) ⟨419652, by rfl⟩ : syracuseStep 4476293 = 839305) (by norm_num)
theorem B2984195 : Blo 2177435 2984195 := bstep (se 1 (by rfl) ⟨2238146, by rfl⟩ : syracuseStep 2984195 = 4476293) B4476293
theorem B7957853 : Blo 2177435 7957853 := bstep (se 3 (by rfl) ⟨1492097, by rfl⟩ : syracuseStep 7957853 = 2984195) B2984195
theorem B5305235 : Blo 2177435 5305235 := bstep (se 1 (by rfl) ⟨3978926, by rfl⟩ : syracuseStep 5305235 = 7957853) B7957853
theorem B14147293 : Blo 2177435 14147293 := bstep (se 3 (by rfl) ⟨2652617, by rfl⟩ : syracuseStep 14147293 = 5305235) B5305235
theorem B18863057 : Blo 2177435 18863057 := bstep (se 2 (by rfl) ⟨7073646, by rfl⟩ : syracuseStep 18863057 = 14147293) B14147293
theorem B12575371 : Blo 2177435 12575371 := bstep (se 1 (by rfl) ⟨9431528, by rfl⟩ : syracuseStep 12575371 = 18863057) B18863057
theorem B16767161 : Blo 2177435 16767161 := bstep (se 2 (by rfl) ⟨6287685, by rfl⟩ : syracuseStep 16767161 = 12575371) B12575371
theorem B11178107 : Blo 2177435 11178107 := bstep (se 1 (by rfl) ⟨8383580, by rfl⟩ : syracuseStep 11178107 = 16767161) B16767161
theorem B7452071 : Blo 2177435 7452071 := bstep (se 1 (by rfl) ⟨5589053, by rfl⟩ : syracuseStep 7452071 = 11178107) B11178107
theorem B4968047 : Blo 2177435 4968047 := bstep (se 1 (by rfl) ⟨3726035, by rfl⟩ : syracuseStep 4968047 = 7452071) B7452071
theorem B3312031 : Blo 2177435 3312031 := bstep (se 1 (by rfl) ⟨2484023, by rfl⟩ : syracuseStep 3312031 = 4968047) B4968047
theorem B4416041 : Blo 2177435 4416041 := bstep (se 2 (by rfl) ⟨1656015, by rfl⟩ : syracuseStep 4416041 = 3312031) B3312031
theorem B2944027 : Blo 2177435 2944027 := bstep (se 1 (by rfl) ⟨2208020, by rfl⟩ : syracuseStep 2944027 = 4416041) B4416041
theorem B3925369 : Blo 2177435 3925369 := bstep (se 2 (by rfl) ⟨1472013, by rfl⟩ : syracuseStep 3925369 = 2944027) B2944027
theorem B5233825 : Blo 2177435 5233825 := bstep (se 2 (by rfl) ⟨1962684, by rfl⟩ : syracuseStep 5233825 = 3925369) B3925369
theorem B6978433 : Blo 2177435 6978433 := bstep (se 2 (by rfl) ⟨2616912, by rfl⟩ : syracuseStep 6978433 = 5233825) B5233825
theorem B9304577 : Blo 2177435 9304577 := bstep (se 2 (by rfl) ⟨3489216, by rfl⟩ : syracuseStep 9304577 = 6978433) B6978433
theorem B6203051 : Blo 2177435 6203051 := bstep (se 1 (by rfl) ⟨4652288, by rfl⟩ : syracuseStep 6203051 = 9304577) B9304577
theorem B4135367 : Blo 2177435 4135367 := bstep (se 1 (by rfl) ⟨3101525, by rfl⟩ : syracuseStep 4135367 = 6203051) B6203051
theorem B2756911 : Blo 2177435 2756911 := bstep (se 1 (by rfl) ⟨2067683, by rfl⟩ : syracuseStep 2756911 = 4135367) B4135367
theorem B3675881 : Blo 2177435 3675881 := bstep (se 2 (by rfl) ⟨1378455, by rfl⟩ : syracuseStep 3675881 = 2756911) B2756911
theorem B2450587 : Blo 2177435 2450587 := bstep (se 1 (by rfl) ⟨1837940, by rfl⟩ : syracuseStep 2450587 = 3675881) B3675881
theorem B3267449 : Blo 2177435 3267449 := bstep (se 2 (by rfl) ⟨1225293, by rfl⟩ : syracuseStep 3267449 = 2450587) B2450587
theorem B2178299 : Blo 2177435 2178299 := bstep (se 1 (by rfl) ⟨1633724, by rfl⟩ : syracuseStep 2178299 = 3267449) B3267449
theorem B45322517 : Blo 2177435 45322517 := bbase (se 6 (by rfl) ⟨1062246, by rfl⟩ : syracuseStep 45322517 = 2124493) (by norm_num)
theorem B120860045 : Blo 2177435 120860045 := bstep (se 3 (by rfl) ⟨22661258, by rfl⟩ : syracuseStep 120860045 = 45322517) B45322517
theorem B80573363 : Blo 2177435 80573363 := bstep (se 1 (by rfl) ⟨60430022, by rfl⟩ : syracuseStep 80573363 = 120860045) B120860045
theorem B53715575 : Blo 2177435 53715575 := bstep (se 1 (by rfl) ⟨40286681, by rfl⟩ : syracuseStep 53715575 = 80573363) B80573363
theorem B35810383 : Blo 2177435 35810383 := bstep (se 1 (by rfl) ⟨26857787, by rfl⟩ : syracuseStep 35810383 = 53715575) B53715575
theorem B47747177 : Blo 2177435 47747177 := bstep (se 2 (by rfl) ⟨17905191, by rfl⟩ : syracuseStep 47747177 = 35810383) B35810383
theorem B31831451 : Blo 2177435 31831451 := bstep (se 1 (by rfl) ⟨23873588, by rfl⟩ : syracuseStep 31831451 = 47747177) B47747177
theorem B21220967 : Blo 2177435 21220967 := bstep (se 1 (by rfl) ⟨15915725, by rfl⟩ : syracuseStep 21220967 = 31831451) B31831451
theorem B14147311 : Blo 2177435 14147311 := bstep (se 1 (by rfl) ⟨10610483, by rfl⟩ : syracuseStep 14147311 = 21220967) B21220967
theorem B18863081 : Blo 2177435 18863081 := bstep (se 2 (by rfl) ⟨7073655, by rfl⟩ : syracuseStep 18863081 = 14147311) B14147311
theorem B12575387 : Blo 2177435 12575387 := bstep (se 1 (by rfl) ⟨9431540, by rfl⟩ : syracuseStep 12575387 = 18863081) B18863081
theorem B8383591 : Blo 2177435 8383591 := bstep (se 1 (by rfl) ⟨6287693, by rfl⟩ : syracuseStep 8383591 = 12575387) B12575387
theorem B11178121 : Blo 2177435 11178121 := bstep (se 2 (by rfl) ⟨4191795, by rfl⟩ : syracuseStep 11178121 = 8383591) B8383591
theorem B14904161 : Blo 2177435 14904161 := bstep (se 2 (by rfl) ⟨5589060, by rfl⟩ : syracuseStep 14904161 = 11178121) B11178121
theorem B9936107 : Blo 2177435 9936107 := bstep (se 1 (by rfl) ⟨7452080, by rfl⟩ : syracuseStep 9936107 = 14904161) B14904161
theorem B6624071 : Blo 2177435 6624071 := bstep (se 1 (by rfl) ⟨4968053, by rfl⟩ : syracuseStep 6624071 = 9936107) B9936107
theorem B4416047 : Blo 2177435 4416047 := bstep (se 1 (by rfl) ⟨3312035, by rfl⟩ : syracuseStep 4416047 = 6624071) B6624071
theorem B2944031 : Blo 2177435 2944031 := bstep (se 1 (by rfl) ⟨2208023, by rfl⟩ : syracuseStep 2944031 = 4416047) B4416047
theorem B31402997 : Blo 2177435 31402997 := bstep (se 5 (by rfl) ⟨1472015, by rfl⟩ : syracuseStep 31402997 = 2944031) B2944031
theorem B20935331 : Blo 2177435 20935331 := bstep (se 1 (by rfl) ⟨15701498, by rfl⟩ : syracuseStep 20935331 = 31402997) B31402997
theorem B13956887 : Blo 2177435 13956887 := bstep (se 1 (by rfl) ⟨10467665, by rfl⟩ : syracuseStep 13956887 = 20935331) B20935331
theorem B37218365 : Blo 2177435 37218365 := bstep (se 3 (by rfl) ⟨6978443, by rfl⟩ : syracuseStep 37218365 = 13956887) B13956887
theorem B24812243 : Blo 2177435 24812243 := bstep (se 1 (by rfl) ⟨18609182, by rfl⟩ : syracuseStep 24812243 = 37218365) B37218365
theorem B16541495 : Blo 2177435 16541495 := bstep (se 1 (by rfl) ⟨12406121, by rfl⟩ : syracuseStep 16541495 = 24812243) B24812243
theorem B11027663 : Blo 2177435 11027663 := bstep (se 1 (by rfl) ⟨8270747, by rfl⟩ : syracuseStep 11027663 = 16541495) B16541495
theorem B7351775 : Blo 2177435 7351775 := bstep (se 1 (by rfl) ⟨5513831, by rfl⟩ : syracuseStep 7351775 = 11027663) B11027663
theorem B4901183 : Blo 2177435 4901183 := bstep (se 1 (by rfl) ⟨3675887, by rfl⟩ : syracuseStep 4901183 = 7351775) B7351775
theorem B3267455 : Blo 2177435 3267455 := bstep (se 1 (by rfl) ⟨2450591, by rfl⟩ : syracuseStep 3267455 = 4901183) B4901183
theorem B2178303 : Blo 2177435 2178303 := bstep (se 1 (by rfl) ⟨1633727, by rfl⟩ : syracuseStep 2178303 = 3267455) B3267455
theorem B3267461 : Blo 2177435 3267461 := bbase (se 4 (by rfl) ⟨306324, by rfl⟩ : syracuseStep 3267461 = 612649) (by norm_num)
theorem B2178307 : Blo 2177435 2178307 := bstep (se 1 (by rfl) ⟨1633730, by rfl⟩ : syracuseStep 2178307 = 3267461) B3267461
theorem B3675901 : Blo 2177435 3675901 := bbase (se 3 (by rfl) ⟨689231, by rfl⟩ : syracuseStep 3675901 = 1378463) (by norm_num)
theorem B4901201 : Blo 2177435 4901201 := bstep (se 2 (by rfl) ⟨1837950, by rfl⟩ : syracuseStep 4901201 = 3675901) B3675901
theorem B3267467 : Blo 2177435 3267467 := bstep (se 1 (by rfl) ⟨2450600, by rfl⟩ : syracuseStep 3267467 = 4901201) B4901201
theorem B2178311 : Blo 2177435 2178311 := bstep (se 1 (by rfl) ⟨1633733, by rfl⟩ : syracuseStep 2178311 = 3267467) B3267467
theorem B2450605 : Blo 2177435 2450605 := bbase (se 3 (by rfl) ⟨459488, by rfl⟩ : syracuseStep 2450605 = 918977) (by norm_num)
theorem B3267473 : Blo 2177435 3267473 := bstep (se 2 (by rfl) ⟨1225302, by rfl⟩ : syracuseStep 3267473 = 2450605) B2450605
theorem B2178315 : Blo 2177435 2178315 := bstep (se 1 (by rfl) ⟨1633736, by rfl⟩ : syracuseStep 2178315 = 3267473) B3267473
theorem B7351829 : Blo 2177435 7351829 := bbase (se 6 (by rfl) ⟨172308, by rfl⟩ : syracuseStep 7351829 = 344617) (by norm_num)
theorem B4901219 : Blo 2177435 4901219 := bstep (se 1 (by rfl) ⟨3675914, by rfl⟩ : syracuseStep 4901219 = 7351829) B7351829
theorem B3267479 : Blo 2177435 3267479 := bstep (se 1 (by rfl) ⟨2450609, by rfl⟩ : syracuseStep 3267479 = 4901219) B4901219
theorem B2178319 : Blo 2177435 2178319 := bstep (se 1 (by rfl) ⟨1633739, by rfl⟩ : syracuseStep 2178319 = 3267479) B3267479
theorem B3267485 : Blo 2177435 3267485 := bbase (se 3 (by rfl) ⟨612653, by rfl⟩ : syracuseStep 3267485 = 1225307) (by norm_num)
theorem B2178323 : Blo 2177435 2178323 := bstep (se 1 (by rfl) ⟨1633742, by rfl⟩ : syracuseStep 2178323 = 3267485) B3267485
theorem B4901237 : Blo 2177435 4901237 := bbase (se 5 (by rfl) ⟨229745, by rfl⟩ : syracuseStep 4901237 = 459491) (by norm_num)
theorem B3267491 : Blo 2177435 3267491 := bstep (se 1 (by rfl) ⟨2450618, by rfl⟩ : syracuseStep 3267491 = 4901237) B4901237
theorem B2178327 : Blo 2177435 2178327 := bstep (se 1 (by rfl) ⟨1633745, by rfl⟩ : syracuseStep 2178327 = 3267491) B3267491
theorem B5233901 : Blo 2177435 5233901 := bbase (se 3 (by rfl) ⟨981356, by rfl⟩ : syracuseStep 5233901 = 1962713) (by norm_num)
theorem B13957069 : Blo 2177435 13957069 := bstep (se 3 (by rfl) ⟨2616950, by rfl⟩ : syracuseStep 13957069 = 5233901) B5233901
theorem B18609425 : Blo 2177435 18609425 := bstep (se 2 (by rfl) ⟨6978534, by rfl⟩ : syracuseStep 18609425 = 13957069) B13957069
theorem B12406283 : Blo 2177435 12406283 := bstep (se 1 (by rfl) ⟨9304712, by rfl⟩ : syracuseStep 12406283 = 18609425) B18609425
theorem B8270855 : Blo 2177435 8270855 := bstep (se 1 (by rfl) ⟨6203141, by rfl⟩ : syracuseStep 8270855 = 12406283) B12406283
theorem B5513903 : Blo 2177435 5513903 := bstep (se 1 (by rfl) ⟨4135427, by rfl⟩ : syracuseStep 5513903 = 8270855) B8270855
theorem B3675935 : Blo 2177435 3675935 := bstep (se 1 (by rfl) ⟨2756951, by rfl⟩ : syracuseStep 3675935 = 5513903) B5513903
theorem B2450623 : Blo 2177435 2450623 := bstep (se 1 (by rfl) ⟨1837967, by rfl⟩ : syracuseStep 2450623 = 3675935) B3675935
theorem B3267497 : Blo 2177435 3267497 := bstep (se 2 (by rfl) ⟨1225311, by rfl⟩ : syracuseStep 3267497 = 2450623) B2450623
theorem B2178331 : Blo 2177435 2178331 := bstep (se 1 (by rfl) ⟨1633748, by rfl⟩ : syracuseStep 2178331 = 3267497) B3267497
theorem B8270869 : Blo 2177435 8270869 := bbase (se 6 (by rfl) ⟨193848, by rfl⟩ : syracuseStep 8270869 = 387697) (by norm_num)
theorem B11027825 : Blo 2177435 11027825 := bstep (se 2 (by rfl) ⟨4135434, by rfl⟩ : syracuseStep 11027825 = 8270869) B8270869
theorem B7351883 : Blo 2177435 7351883 := bstep (se 1 (by rfl) ⟨5513912, by rfl⟩ : syracuseStep 7351883 = 11027825) B11027825
theorem B4901255 : Blo 2177435 4901255 := bstep (se 1 (by rfl) ⟨3675941, by rfl⟩ : syracuseStep 4901255 = 7351883) B7351883
theorem B3267503 : Blo 2177435 3267503 := bstep (se 1 (by rfl) ⟨2450627, by rfl⟩ : syracuseStep 3267503 = 4901255) B4901255
theorem B2178335 : Blo 2177435 2178335 := bstep (se 1 (by rfl) ⟨1633751, by rfl⟩ : syracuseStep 2178335 = 3267503) B3267503
theorem B3267509 : Blo 2177435 3267509 := bbase (se 5 (by rfl) ⟨153164, by rfl⟩ : syracuseStep 3267509 = 306329) (by norm_num)
theorem B2178339 : Blo 2177435 2178339 := bstep (se 1 (by rfl) ⟨1633754, by rfl⟩ : syracuseStep 2178339 = 3267509) B3267509
theorem B5513933 : Blo 2177435 5513933 := bbase (se 3 (by rfl) ⟨1033862, by rfl⟩ : syracuseStep 5513933 = 2067725) (by norm_num)
theorem B3675955 : Blo 2177435 3675955 := bstep (se 1 (by rfl) ⟨2756966, by rfl⟩ : syracuseStep 3675955 = 5513933) B5513933
theorem B4901273 : Blo 2177435 4901273 := bstep (se 2 (by rfl) ⟨1837977, by rfl⟩ : syracuseStep 4901273 = 3675955) B3675955
theorem B3267515 : Blo 2177435 3267515 := bstep (se 1 (by rfl) ⟨2450636, by rfl⟩ : syracuseStep 3267515 = 4901273) B4901273
theorem B2178343 : Blo 2177435 2178343 := bstep (se 1 (by rfl) ⟨1633757, by rfl⟩ : syracuseStep 2178343 = 3267515) B3267515
theorem B2450641 : Blo 2177435 2450641 := bbase (se 2 (by rfl) ⟨918990, by rfl⟩ : syracuseStep 2450641 = 1837981) (by norm_num)
theorem B3267521 : Blo 2177435 3267521 := bstep (se 2 (by rfl) ⟨1225320, by rfl⟩ : syracuseStep 3267521 = 2450641) B2450641
theorem B2178347 : Blo 2177435 2178347 := bstep (se 1 (by rfl) ⟨1633760, by rfl⟩ : syracuseStep 2178347 = 3267521) B3267521
theorem B3312109 : Blo 2177435 3312109 := bbase (se 3 (by rfl) ⟨621020, by rfl⟩ : syracuseStep 3312109 = 1242041) (by norm_num)
theorem B17664581 : Blo 2177435 17664581 := bstep (se 4 (by rfl) ⟨1656054, by rfl⟩ : syracuseStep 17664581 = 3312109) B3312109
theorem B11776387 : Blo 2177435 11776387 := bstep (se 1 (by rfl) ⟨8832290, by rfl⟩ : syracuseStep 11776387 = 17664581) B17664581
theorem B15701849 : Blo 2177435 15701849 := bstep (se 2 (by rfl) ⟨5888193, by rfl⟩ : syracuseStep 15701849 = 11776387) B11776387
theorem B10467899 : Blo 2177435 10467899 := bstep (se 1 (by rfl) ⟨7850924, by rfl⟩ : syracuseStep 10467899 = 15701849) B15701849
theorem B6978599 : Blo 2177435 6978599 := bstep (se 1 (by rfl) ⟨5233949, by rfl⟩ : syracuseStep 6978599 = 10467899) B10467899
theorem B4652399 : Blo 2177435 4652399 := bstep (se 1 (by rfl) ⟨3489299, by rfl⟩ : syracuseStep 4652399 = 6978599) B6978599
theorem B3101599 : Blo 2177435 3101599 := bstep (se 1 (by rfl) ⟨2326199, by rfl⟩ : syracuseStep 3101599 = 4652399) B4652399
theorem B4135465 : Blo 2177435 4135465 := bstep (se 2 (by rfl) ⟨1550799, by rfl⟩ : syracuseStep 4135465 = 3101599) B3101599
theorem B5513953 : Blo 2177435 5513953 := bstep (se 2 (by rfl) ⟨2067732, by rfl⟩ : syracuseStep 5513953 = 4135465) B4135465
theorem B7351937 : Blo 2177435 7351937 := bstep (se 2 (by rfl) ⟨2756976, by rfl⟩ : syracuseStep 7351937 = 5513953) B5513953
theorem B4901291 : Blo 2177435 4901291 := bstep (se 1 (by rfl) ⟨3675968, by rfl⟩ : syracuseStep 4901291 = 7351937) B7351937
theorem B3267527 : Blo 2177435 3267527 := bstep (se 1 (by rfl) ⟨2450645, by rfl⟩ : syracuseStep 3267527 = 4901291) B4901291
theorem B2178351 : Blo 2177435 2178351 := bstep (se 1 (by rfl) ⟨1633763, by rfl⟩ : syracuseStep 2178351 = 3267527) B3267527
theorem B3267533 : Blo 2177435 3267533 := bbase (se 3 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 3267533 = 1225325) (by norm_num)
theorem B2178355 : Blo 2177435 2178355 := bstep (se 1 (by rfl) ⟨1633766, by rfl⟩ : syracuseStep 2178355 = 3267533) B3267533
theorem B4901309 : Blo 2177435 4901309 := bbase (se 3 (by rfl) ⟨918995, by rfl⟩ : syracuseStep 4901309 = 1837991) (by norm_num)
theorem B3267539 : Blo 2177435 3267539 := bstep (se 1 (by rfl) ⟨2450654, by rfl⟩ : syracuseStep 3267539 = 4901309) B4901309
theorem B2178359 : Blo 2177435 2178359 := bstep (se 1 (by rfl) ⟨1633769, by rfl⟩ : syracuseStep 2178359 = 3267539) B3267539
theorem B3675989 : Blo 2177435 3675989 := bbase (se 9 (by rfl) ⟨10769, by rfl⟩ : syracuseStep 3675989 = 21539) (by norm_num)
theorem B2450659 : Blo 2177435 2450659 := bstep (se 1 (by rfl) ⟨1837994, by rfl⟩ : syracuseStep 2450659 = 3675989) B3675989
theorem B3267545 : Blo 2177435 3267545 := bstep (se 2 (by rfl) ⟨1225329, by rfl⟩ : syracuseStep 3267545 = 2450659) B2450659
theorem B2178363 : Blo 2177435 2178363 := bstep (se 1 (by rfl) ⟨1633772, by rfl⟩ : syracuseStep 2178363 = 3267545) B3267545
theorem B7850981 : Blo 2177435 7850981 := bbase (se 4 (by rfl) ⟨736029, by rfl⟩ : syracuseStep 7850981 = 1472059) (by norm_num)
theorem B5233987 : Blo 2177435 5233987 := bstep (se 1 (by rfl) ⟨3925490, by rfl⟩ : syracuseStep 5233987 = 7850981) B7850981
theorem B6978649 : Blo 2177435 6978649 := bstep (se 2 (by rfl) ⟨2616993, by rfl⟩ : syracuseStep 6978649 = 5233987) B5233987
theorem B9304865 : Blo 2177435 9304865 := bstep (se 2 (by rfl) ⟨3489324, by rfl⟩ : syracuseStep 9304865 = 6978649) B6978649
theorem B6203243 : Blo 2177435 6203243 := bstep (se 1 (by rfl) ⟨4652432, by rfl⟩ : syracuseStep 6203243 = 9304865) B9304865
theorem B16541981 : Blo 2177435 16541981 := bstep (se 3 (by rfl) ⟨3101621, by rfl⟩ : syracuseStep 16541981 = 6203243) B6203243
theorem B11027987 : Blo 2177435 11027987 := bstep (se 1 (by rfl) ⟨8270990, by rfl⟩ : syracuseStep 11027987 = 16541981) B16541981
theorem B7351991 : Blo 2177435 7351991 := bstep (se 1 (by rfl) ⟨5513993, by rfl⟩ : syracuseStep 7351991 = 11027987) B11027987
theorem B4901327 : Blo 2177435 4901327 := bstep (se 1 (by rfl) ⟨3675995, by rfl⟩ : syracuseStep 4901327 = 7351991) B7351991
theorem B3267551 : Blo 2177435 3267551 := bstep (se 1 (by rfl) ⟨2450663, by rfl⟩ : syracuseStep 3267551 = 4901327) B4901327
theorem B2178367 : Blo 2177435 2178367 := bstep (se 1 (by rfl) ⟨1633775, by rfl⟩ : syracuseStep 2178367 = 3267551) B3267551
theorem B3267557 : Blo 2177435 3267557 := bbase (se 4 (by rfl) ⟨306333, by rfl⟩ : syracuseStep 3267557 = 612667) (by norm_num)
theorem B2178371 : Blo 2177435 2178371 := bstep (se 1 (by rfl) ⟨1633778, by rfl⟩ : syracuseStep 2178371 = 3267557) B3267557
theorem B9304901 : Blo 2177435 9304901 := bbase (se 4 (by rfl) ⟨872334, by rfl⟩ : syracuseStep 9304901 = 1744669) (by norm_num)
theorem B6203267 : Blo 2177435 6203267 := bstep (se 1 (by rfl) ⟨4652450, by rfl⟩ : syracuseStep 6203267 = 9304901) B9304901
theorem B4135511 : Blo 2177435 4135511 := bstep (se 1 (by rfl) ⟨3101633, by rfl⟩ : syracuseStep 4135511 = 6203267) B6203267
theorem B2757007 : Blo 2177435 2757007 := bstep (se 1 (by rfl) ⟨2067755, by rfl⟩ : syracuseStep 2757007 = 4135511) B4135511
theorem B3676009 : Blo 2177435 3676009 := bstep (se 2 (by rfl) ⟨1378503, by rfl⟩ : syracuseStep 3676009 = 2757007) B2757007
theorem B4901345 : Blo 2177435 4901345 := bstep (se 2 (by rfl) ⟨1838004, by rfl⟩ : syracuseStep 4901345 = 3676009) B3676009
theorem B3267563 : Blo 2177435 3267563 := bstep (se 1 (by rfl) ⟨2450672, by rfl⟩ : syracuseStep 3267563 = 4901345) B4901345
theorem B2178375 : Blo 2177435 2178375 := bstep (se 1 (by rfl) ⟨1633781, by rfl⟩ : syracuseStep 2178375 = 3267563) B3267563
theorem B2450677 : Blo 2177435 2450677 := bbase (se 5 (by rfl) ⟨114875, by rfl⟩ : syracuseStep 2450677 = 229751) (by norm_num)
theorem B3267569 : Blo 2177435 3267569 := bstep (se 2 (by rfl) ⟨1225338, by rfl⟩ : syracuseStep 3267569 = 2450677) B2450677
theorem B2178379 : Blo 2177435 2178379 := bstep (se 1 (by rfl) ⟨1633784, by rfl⟩ : syracuseStep 2178379 = 3267569) B3267569
theorem B2757017 : Blo 2177435 2757017 := bbase (se 2 (by rfl) ⟨1033881, by rfl⟩ : syracuseStep 2757017 = 2067763) (by norm_num)
theorem B7352045 : Blo 2177435 7352045 := bstep (se 3 (by rfl) ⟨1378508, by rfl⟩ : syracuseStep 7352045 = 2757017) B2757017
theorem B4901363 : Blo 2177435 4901363 := bstep (se 1 (by rfl) ⟨3676022, by rfl⟩ : syracuseStep 4901363 = 7352045) B7352045
theorem B3267575 : Blo 2177435 3267575 := bstep (se 1 (by rfl) ⟨2450681, by rfl⟩ : syracuseStep 3267575 = 4901363) B4901363
theorem B2178383 : Blo 2177435 2178383 := bstep (se 1 (by rfl) ⟨1633787, by rfl⟩ : syracuseStep 2178383 = 3267575) B3267575
theorem B3267581 : Blo 2177435 3267581 := bbase (se 3 (by rfl) ⟨612671, by rfl⟩ : syracuseStep 3267581 = 1225343) (by norm_num)
theorem B2178387 : Blo 2177435 2178387 := bstep (se 1 (by rfl) ⟨1633790, by rfl⟩ : syracuseStep 2178387 = 3267581) B3267581
theorem B4901381 : Blo 2177435 4901381 := bbase (se 4 (by rfl) ⟨459504, by rfl⟩ : syracuseStep 4901381 = 919009) (by norm_num)
theorem B3267587 : Blo 2177435 3267587 := bstep (se 1 (by rfl) ⟨2450690, by rfl⟩ : syracuseStep 3267587 = 4901381) B4901381
theorem B2178391 : Blo 2177435 2178391 := bstep (se 1 (by rfl) ⟨1633793, by rfl⟩ : syracuseStep 2178391 = 3267587) B3267587
theorem B4135549 : Blo 2177435 4135549 := bbase (se 3 (by rfl) ⟨775415, by rfl⟩ : syracuseStep 4135549 = 1550831) (by norm_num)
theorem B5514065 : Blo 2177435 5514065 := bstep (se 2 (by rfl) ⟨2067774, by rfl⟩ : syracuseStep 5514065 = 4135549) B4135549
theorem B3676043 : Blo 2177435 3676043 := bstep (se 1 (by rfl) ⟨2757032, by rfl⟩ : syracuseStep 3676043 = 5514065) B5514065
theorem B2450695 : Blo 2177435 2450695 := bstep (se 1 (by rfl) ⟨1838021, by rfl⟩ : syracuseStep 2450695 = 3676043) B3676043
theorem B3267593 : Blo 2177435 3267593 := bstep (se 2 (by rfl) ⟨1225347, by rfl⟩ : syracuseStep 3267593 = 2450695) B2450695
theorem B2178395 : Blo 2177435 2178395 := bstep (se 1 (by rfl) ⟨1633796, by rfl⟩ : syracuseStep 2178395 = 3267593) B3267593
theorem B11028149 : Blo 2177435 11028149 := bbase (se 5 (by rfl) ⟨516944, by rfl⟩ : syracuseStep 11028149 = 1033889) (by norm_num)
theorem B7352099 : Blo 2177435 7352099 := bstep (se 1 (by rfl) ⟨5514074, by rfl⟩ : syracuseStep 7352099 = 11028149) B11028149
theorem B4901399 : Blo 2177435 4901399 := bstep (se 1 (by rfl) ⟨3676049, by rfl⟩ : syracuseStep 4901399 = 7352099) B7352099
theorem B3267599 : Blo 2177435 3267599 := bstep (se 1 (by rfl) ⟨2450699, by rfl⟩ : syracuseStep 3267599 = 4901399) B4901399
theorem B2178399 : Blo 2177435 2178399 := bstep (se 1 (by rfl) ⟨1633799, by rfl⟩ : syracuseStep 2178399 = 3267599) B3267599
theorem B3267605 : Blo 2177435 3267605 := bbase (se 6 (by rfl) ⟨76584, by rfl⟩ : syracuseStep 3267605 = 153169) (by norm_num)
theorem B2178403 : Blo 2177435 2178403 := bstep (se 1 (by rfl) ⟨1633802, by rfl⟩ : syracuseStep 2178403 = 3267605) B3267605
theorem B7851125 : Blo 2177435 7851125 := bbase (se 5 (by rfl) ⟨368021, by rfl⟩ : syracuseStep 7851125 = 736043) (by norm_num)
theorem B20936333 : Blo 2177435 20936333 := bstep (se 3 (by rfl) ⟨3925562, by rfl⟩ : syracuseStep 20936333 = 7851125) B7851125
theorem B13957555 : Blo 2177435 13957555 := bstep (se 1 (by rfl) ⟨10468166, by rfl⟩ : syracuseStep 13957555 = 20936333) B20936333
theorem B18610073 : Blo 2177435 18610073 := bstep (se 2 (by rfl) ⟨6978777, by rfl⟩ : syracuseStep 18610073 = 13957555) B13957555
theorem B12406715 : Blo 2177435 12406715 := bstep (se 1 (by rfl) ⟨9305036, by rfl⟩ : syracuseStep 12406715 = 18610073) B18610073
theorem B8271143 : Blo 2177435 8271143 := bstep (se 1 (by rfl) ⟨6203357, by rfl⟩ : syracuseStep 8271143 = 12406715) B12406715
theorem B5514095 : Blo 2177435 5514095 := bstep (se 1 (by rfl) ⟨4135571, by rfl⟩ : syracuseStep 5514095 = 8271143) B8271143
theorem B3676063 : Blo 2177435 3676063 := bstep (se 1 (by rfl) ⟨2757047, by rfl⟩ : syracuseStep 3676063 = 5514095) B5514095
theorem B4901417 : Blo 2177435 4901417 := bstep (se 2 (by rfl) ⟨1838031, by rfl⟩ : syracuseStep 4901417 = 3676063) B3676063
theorem B3267611 : Blo 2177435 3267611 := bstep (se 1 (by rfl) ⟨2450708, by rfl⟩ : syracuseStep 3267611 = 4901417) B4901417
theorem B2178407 : Blo 2177435 2178407 := bstep (se 1 (by rfl) ⟨1633805, by rfl⟩ : syracuseStep 2178407 = 3267611) B3267611
theorem B2450713 : Blo 2177435 2450713 := bbase (se 2 (by rfl) ⟨919017, by rfl⟩ : syracuseStep 2450713 = 1838035) (by norm_num)
theorem B3267617 : Blo 2177435 3267617 := bstep (se 2 (by rfl) ⟨1225356, by rfl⟩ : syracuseStep 3267617 = 2450713) B2450713
theorem B2178411 : Blo 2177435 2178411 := bstep (se 1 (by rfl) ⟨1633808, by rfl⟩ : syracuseStep 2178411 = 3267617) B3267617
theorem B8271173 : Blo 2177435 8271173 := bbase (se 4 (by rfl) ⟨775422, by rfl⟩ : syracuseStep 8271173 = 1550845) (by norm_num)
theorem B5514115 : Blo 2177435 5514115 := bstep (se 1 (by rfl) ⟨4135586, by rfl⟩ : syracuseStep 5514115 = 8271173) B8271173
theorem B7352153 : Blo 2177435 7352153 := bstep (se 2 (by rfl) ⟨2757057, by rfl⟩ : syracuseStep 7352153 = 5514115) B5514115
theorem B4901435 : Blo 2177435 4901435 := bstep (se 1 (by rfl) ⟨3676076, by rfl⟩ : syracuseStep 4901435 = 7352153) B7352153
theorem B3267623 : Blo 2177435 3267623 := bstep (se 1 (by rfl) ⟨2450717, by rfl⟩ : syracuseStep 3267623 = 4901435) B4901435
theorem B2178415 : Blo 2177435 2178415 := bstep (se 1 (by rfl) ⟨1633811, by rfl⟩ : syracuseStep 2178415 = 3267623) B3267623
theorem B3267629 : Blo 2177435 3267629 := bbase (se 3 (by rfl) ⟨612680, by rfl⟩ : syracuseStep 3267629 = 1225361) (by norm_num)
theorem B2178419 : Blo 2177435 2178419 := bstep (se 1 (by rfl) ⟨1633814, by rfl⟩ : syracuseStep 2178419 = 3267629) B3267629
theorem B4901453 : Blo 2177435 4901453 := bbase (se 3 (by rfl) ⟨919022, by rfl⟩ : syracuseStep 4901453 = 1838045) (by norm_num)
theorem B3267635 : Blo 2177435 3267635 := bstep (se 1 (by rfl) ⟨2450726, by rfl⟩ : syracuseStep 3267635 = 4901453) B4901453
theorem B2178423 : Blo 2177435 2178423 := bstep (se 1 (by rfl) ⟨1633817, by rfl⟩ : syracuseStep 2178423 = 3267635) B3267635
theorem B2757073 : Blo 2177435 2757073 := bbase (se 2 (by rfl) ⟨1033902, by rfl⟩ : syracuseStep 2757073 = 2067805) (by norm_num)
theorem B3676097 : Blo 2177435 3676097 := bstep (se 2 (by rfl) ⟨1378536, by rfl⟩ : syracuseStep 3676097 = 2757073) B2757073
theorem B2450731 : Blo 2177435 2450731 := bstep (se 1 (by rfl) ⟨1838048, by rfl⟩ : syracuseStep 2450731 = 3676097) B3676097
theorem B3267641 : Blo 2177435 3267641 := bstep (se 2 (by rfl) ⟨1225365, by rfl⟩ : syracuseStep 3267641 = 2450731) B2450731
theorem B2178427 : Blo 2177435 2178427 := bstep (se 1 (by rfl) ⟨1633820, by rfl⟩ : syracuseStep 2178427 = 3267641) B3267641
theorem B5234141 : Blo 2177435 5234141 := bbase (se 3 (by rfl) ⟨981401, by rfl⟩ : syracuseStep 5234141 = 1962803) (by norm_num)
theorem B3489427 : Blo 2177435 3489427 := bstep (se 1 (by rfl) ⟨2617070, by rfl⟩ : syracuseStep 3489427 = 5234141) B5234141
theorem B4652569 : Blo 2177435 4652569 := bstep (se 2 (by rfl) ⟨1744713, by rfl⟩ : syracuseStep 4652569 = 3489427) B3489427
theorem B24813701 : Blo 2177435 24813701 := bstep (se 4 (by rfl) ⟨2326284, by rfl⟩ : syracuseStep 24813701 = 4652569) B4652569
theorem B16542467 : Blo 2177435 16542467 := bstep (se 1 (by rfl) ⟨12406850, by rfl⟩ : syracuseStep 16542467 = 24813701) B24813701
theorem B11028311 : Blo 2177435 11028311 := bstep (se 1 (by rfl) ⟨8271233, by rfl⟩ : syracuseStep 11028311 = 16542467) B16542467
theorem B7352207 : Blo 2177435 7352207 := bstep (se 1 (by rfl) ⟨5514155, by rfl⟩ : syracuseStep 7352207 = 11028311) B11028311
theorem B4901471 : Blo 2177435 4901471 := bstep (se 1 (by rfl) ⟨3676103, by rfl⟩ : syracuseStep 4901471 = 7352207) B7352207
theorem B3267647 : Blo 2177435 3267647 := bstep (se 1 (by rfl) ⟨2450735, by rfl⟩ : syracuseStep 3267647 = 4901471) B4901471
theorem B2178431 : Blo 2177435 2178431 := bstep (se 1 (by rfl) ⟨1633823, by rfl⟩ : syracuseStep 2178431 = 3267647) B3267647
theorem B3267653 : Blo 2177435 3267653 := bbase (se 4 (by rfl) ⟨306342, by rfl⟩ : syracuseStep 3267653 = 612685) (by norm_num)
theorem B2178435 : Blo 2177435 2178435 := bstep (se 1 (by rfl) ⟨1633826, by rfl⟩ : syracuseStep 2178435 = 3267653) B3267653
theorem B3676117 : Blo 2177435 3676117 := bbase (se 7 (by rfl) ⟨43079, by rfl⟩ : syracuseStep 3676117 = 86159) (by norm_num)
theorem B4901489 : Blo 2177435 4901489 := bstep (se 2 (by rfl) ⟨1838058, by rfl⟩ : syracuseStep 4901489 = 3676117) B3676117
theorem B3267659 : Blo 2177435 3267659 := bstep (se 1 (by rfl) ⟨2450744, by rfl⟩ : syracuseStep 3267659 = 4901489) B4901489
theorem B2178439 : Blo 2177435 2178439 := bstep (se 1 (by rfl) ⟨1633829, by rfl⟩ : syracuseStep 2178439 = 3267659) B3267659
theorem B2450749 : Blo 2177435 2450749 := bbase (se 3 (by rfl) ⟨459515, by rfl⟩ : syracuseStep 2450749 = 919031) (by norm_num)
theorem B3267665 : Blo 2177435 3267665 := bstep (se 2 (by rfl) ⟨1225374, by rfl⟩ : syracuseStep 3267665 = 2450749) B2450749
theorem B2178443 : Blo 2177435 2178443 := bstep (se 1 (by rfl) ⟨1633832, by rfl⟩ : syracuseStep 2178443 = 3267665) B3267665
theorem B7352261 : Blo 2177435 7352261 := bbase (se 4 (by rfl) ⟨689274, by rfl⟩ : syracuseStep 7352261 = 1378549) (by norm_num)
theorem B4901507 : Blo 2177435 4901507 := bstep (se 1 (by rfl) ⟨3676130, by rfl⟩ : syracuseStep 4901507 = 7352261) B7352261
theorem B3267671 : Blo 2177435 3267671 := bstep (se 1 (by rfl) ⟨2450753, by rfl⟩ : syracuseStep 3267671 = 4901507) B4901507
theorem B2178447 : Blo 2177435 2178447 := bstep (se 1 (by rfl) ⟨1633835, by rfl⟩ : syracuseStep 2178447 = 3267671) B3267671
theorem B3267677 : Blo 2177435 3267677 := bbase (se 3 (by rfl) ⟨612689, by rfl⟩ : syracuseStep 3267677 = 1225379) (by norm_num)
theorem B2178451 : Blo 2177435 2178451 := bstep (se 1 (by rfl) ⟨1633838, by rfl⟩ : syracuseStep 2178451 = 3267677) B3267677
theorem B4901525 : Blo 2177435 4901525 := bbase (se 6 (by rfl) ⟨114879, by rfl⟩ : syracuseStep 4901525 = 229759) (by norm_num)
theorem B3267683 : Blo 2177435 3267683 := bstep (se 1 (by rfl) ⟨2450762, by rfl⟩ : syracuseStep 3267683 = 4901525) B4901525
theorem B2178455 : Blo 2177435 2178455 := bstep (se 1 (by rfl) ⟨1633841, by rfl⟩ : syracuseStep 2178455 = 3267683) B3267683
theorem B2617105 : Blo 2177435 2617105 := bbase (se 2 (by rfl) ⟨981414, by rfl⟩ : syracuseStep 2617105 = 1962829) (by norm_num)
theorem B3489473 : Blo 2177435 3489473 := bstep (se 2 (by rfl) ⟨1308552, by rfl⟩ : syracuseStep 3489473 = 2617105) B2617105
theorem B2326315 : Blo 2177435 2326315 := bstep (se 1 (by rfl) ⟨1744736, by rfl⟩ : syracuseStep 2326315 = 3489473) B3489473
theorem B3101753 : Blo 2177435 3101753 := bstep (se 2 (by rfl) ⟨1163157, by rfl⟩ : syracuseStep 3101753 = 2326315) B2326315
theorem B8271341 : Blo 2177435 8271341 := bstep (se 3 (by rfl) ⟨1550876, by rfl⟩ : syracuseStep 8271341 = 3101753) B3101753
theorem B5514227 : Blo 2177435 5514227 := bstep (se 1 (by rfl) ⟨4135670, by rfl⟩ : syracuseStep 5514227 = 8271341) B8271341
theorem B3676151 : Blo 2177435 3676151 := bstep (se 1 (by rfl) ⟨2757113, by rfl⟩ : syracuseStep 3676151 = 5514227) B5514227
theorem B2450767 : Blo 2177435 2450767 := bstep (se 1 (by rfl) ⟨1838075, by rfl⟩ : syracuseStep 2450767 = 3676151) B3676151
theorem B3267689 : Blo 2177435 3267689 := bstep (se 2 (by rfl) ⟨1225383, by rfl⟩ : syracuseStep 3267689 = 2450767) B2450767
theorem B2178459 : Blo 2177435 2178459 := bstep (se 1 (by rfl) ⟨1633844, by rfl⟩ : syracuseStep 2178459 = 3267689) B3267689
theorem B11331461 : Blo 2177435 11331461 := bbase (se 4 (by rfl) ⟨1062324, by rfl⟩ : syracuseStep 11331461 = 2124649) (by norm_num)
theorem B7554307 : Blo 2177435 7554307 := bstep (se 1 (by rfl) ⟨5665730, by rfl⟩ : syracuseStep 7554307 = 11331461) B11331461
theorem B10072409 : Blo 2177435 10072409 := bstep (se 2 (by rfl) ⟨3777153, by rfl⟩ : syracuseStep 10072409 = 7554307) B7554307
theorem B26859757 : Blo 2177435 26859757 := bstep (se 3 (by rfl) ⟨5036204, by rfl⟩ : syracuseStep 26859757 = 10072409) B10072409
theorem B35813009 : Blo 2177435 35813009 := bstep (se 2 (by rfl) ⟨13429878, by rfl⟩ : syracuseStep 35813009 = 26859757) B26859757
theorem B23875339 : Blo 2177435 23875339 := bstep (se 1 (by rfl) ⟨17906504, by rfl⟩ : syracuseStep 23875339 = 35813009) B35813009
theorem B31833785 : Blo 2177435 31833785 := bstep (se 2 (by rfl) ⟨11937669, by rfl⟩ : syracuseStep 31833785 = 23875339) B23875339
theorem B21222523 : Blo 2177435 21222523 := bstep (se 1 (by rfl) ⟨15916892, by rfl⟩ : syracuseStep 21222523 = 31833785) B31833785
theorem B28296697 : Blo 2177435 28296697 := bstep (se 2 (by rfl) ⟨10611261, by rfl⟩ : syracuseStep 28296697 = 21222523) B21222523
theorem B37728929 : Blo 2177435 37728929 := bstep (se 2 (by rfl) ⟨14148348, by rfl⟩ : syracuseStep 37728929 = 28296697) B28296697
theorem B25152619 : Blo 2177435 25152619 := bstep (se 1 (by rfl) ⟨18864464, by rfl⟩ : syracuseStep 25152619 = 37728929) B37728929
theorem B33536825 : Blo 2177435 33536825 := bstep (se 2 (by rfl) ⟨12576309, by rfl⟩ : syracuseStep 33536825 = 25152619) B25152619
theorem B22357883 : Blo 2177435 22357883 := bstep (se 1 (by rfl) ⟨16768412, by rfl⟩ : syracuseStep 22357883 = 33536825) B33536825
theorem B14905255 : Blo 2177435 14905255 := bstep (se 1 (by rfl) ⟨11178941, by rfl⟩ : syracuseStep 14905255 = 22357883) B22357883
theorem B19873673 : Blo 2177435 19873673 := bstep (se 2 (by rfl) ⟨7452627, by rfl⟩ : syracuseStep 19873673 = 14905255) B14905255
theorem B13249115 : Blo 2177435 13249115 := bstep (se 1 (by rfl) ⟨9936836, by rfl⟩ : syracuseStep 13249115 = 19873673) B19873673
theorem B8832743 : Blo 2177435 8832743 := bstep (se 1 (by rfl) ⟨6624557, by rfl⟩ : syracuseStep 8832743 = 13249115) B13249115
theorem B5888495 : Blo 2177435 5888495 := bstep (se 1 (by rfl) ⟨4416371, by rfl⟩ : syracuseStep 5888495 = 8832743) B8832743
theorem B15702653 : Blo 2177435 15702653 := bstep (se 3 (by rfl) ⟨2944247, by rfl⟩ : syracuseStep 15702653 = 5888495) B5888495
theorem B10468435 : Blo 2177435 10468435 := bstep (se 1 (by rfl) ⟨7851326, by rfl⟩ : syracuseStep 10468435 = 15702653) B15702653
theorem B13957913 : Blo 2177435 13957913 := bstep (se 2 (by rfl) ⟨5234217, by rfl⟩ : syracuseStep 13957913 = 10468435) B10468435
theorem B9305275 : Blo 2177435 9305275 := bstep (se 1 (by rfl) ⟨6978956, by rfl⟩ : syracuseStep 9305275 = 13957913) B13957913
theorem B12407033 : Blo 2177435 12407033 := bstep (se 2 (by rfl) ⟨4652637, by rfl⟩ : syracuseStep 12407033 = 9305275) B9305275
theorem B8271355 : Blo 2177435 8271355 := bstep (se 1 (by rfl) ⟨6203516, by rfl⟩ : syracuseStep 8271355 = 12407033) B12407033
theorem B11028473 : Blo 2177435 11028473 := bstep (se 2 (by rfl) ⟨4135677, by rfl⟩ : syracuseStep 11028473 = 8271355) B8271355
theorem B7352315 : Blo 2177435 7352315 := bstep (se 1 (by rfl) ⟨5514236, by rfl⟩ : syracuseStep 7352315 = 11028473) B11028473
theorem B4901543 : Blo 2177435 4901543 := bstep (se 1 (by rfl) ⟨3676157, by rfl⟩ : syracuseStep 4901543 = 7352315) B7352315
theorem B3267695 : Blo 2177435 3267695 := bstep (se 1 (by rfl) ⟨2450771, by rfl⟩ : syracuseStep 3267695 = 4901543) B4901543
theorem B2178463 : Blo 2177435 2178463 := bstep (se 1 (by rfl) ⟨1633847, by rfl⟩ : syracuseStep 2178463 = 3267695) B3267695
theorem B3267701 : Blo 2177435 3267701 := bbase (se 5 (by rfl) ⟨153173, by rfl⟩ : syracuseStep 3267701 = 306347) (by norm_num)
theorem B2178467 : Blo 2177435 2178467 := bstep (se 1 (by rfl) ⟨1633850, by rfl⟩ : syracuseStep 2178467 = 3267701) B3267701
theorem B4135693 : Blo 2177435 4135693 := bbase (se 3 (by rfl) ⟨775442, by rfl⟩ : syracuseStep 4135693 = 1550885) (by norm_num)
theorem B5514257 : Blo 2177435 5514257 := bstep (se 2 (by rfl) ⟨2067846, by rfl⟩ : syracuseStep 5514257 = 4135693) B4135693
theorem B3676171 : Blo 2177435 3676171 := bstep (se 1 (by rfl) ⟨2757128, by rfl⟩ : syracuseStep 3676171 = 5514257) B5514257
theorem B4901561 : Blo 2177435 4901561 := bstep (se 2 (by rfl) ⟨1838085, by rfl⟩ : syracuseStep 4901561 = 3676171) B3676171
theorem B3267707 : Blo 2177435 3267707 := bstep (se 1 (by rfl) ⟨2450780, by rfl⟩ : syracuseStep 3267707 = 4901561) B4901561
theorem B2178471 : Blo 2177435 2178471 := bstep (se 1 (by rfl) ⟨1633853, by rfl⟩ : syracuseStep 2178471 = 3267707) B3267707
theorem B2450785 : Blo 2177435 2450785 := bbase (se 2 (by rfl) ⟨919044, by rfl⟩ : syracuseStep 2450785 = 1838089) (by norm_num)
theorem B3267713 : Blo 2177435 3267713 := bstep (se 2 (by rfl) ⟨1225392, by rfl⟩ : syracuseStep 3267713 = 2450785) B2450785
theorem B2178475 : Blo 2177435 2178475 := bstep (se 1 (by rfl) ⟨1633856, by rfl⟩ : syracuseStep 2178475 = 3267713) B3267713
theorem B5514277 : Blo 2177435 5514277 := bbase (se 4 (by rfl) ⟨516963, by rfl⟩ : syracuseStep 5514277 = 1033927) (by norm_num)
theorem B7352369 : Blo 2177435 7352369 := bstep (se 2 (by rfl) ⟨2757138, by rfl⟩ : syracuseStep 7352369 = 5514277) B5514277
theorem B4901579 : Blo 2177435 4901579 := bstep (se 1 (by rfl) ⟨3676184, by rfl⟩ : syracuseStep 4901579 = 7352369) B7352369
theorem B3267719 : Blo 2177435 3267719 := bstep (se 1 (by rfl) ⟨2450789, by rfl⟩ : syracuseStep 3267719 = 4901579) B4901579
theorem B2178479 : Blo 2177435 2178479 := bstep (se 1 (by rfl) ⟨1633859, by rfl⟩ : syracuseStep 2178479 = 3267719) B3267719
theorem B3267725 : Blo 2177435 3267725 := bbase (se 3 (by rfl) ⟨612698, by rfl⟩ : syracuseStep 3267725 = 1225397) (by norm_num)
theorem B2178483 : Blo 2177435 2178483 := bstep (se 1 (by rfl) ⟨1633862, by rfl⟩ : syracuseStep 2178483 = 3267725) B3267725
theorem B4901597 : Blo 2177435 4901597 := bbase (se 3 (by rfl) ⟨919049, by rfl⟩ : syracuseStep 4901597 = 1838099) (by norm_num)
theorem B3267731 : Blo 2177435 3267731 := bstep (se 1 (by rfl) ⟨2450798, by rfl⟩ : syracuseStep 3267731 = 4901597) B4901597
theorem B2178487 : Blo 2177435 2178487 := bstep (se 1 (by rfl) ⟨1633865, by rfl⟩ : syracuseStep 2178487 = 3267731) B3267731
theorem B3676205 : Blo 2177435 3676205 := bbase (se 3 (by rfl) ⟨689288, by rfl⟩ : syracuseStep 3676205 = 1378577) (by norm_num)
theorem B2450803 : Blo 2177435 2450803 := bstep (se 1 (by rfl) ⟨1838102, by rfl⟩ : syracuseStep 2450803 = 3676205) B3676205
theorem B3267737 : Blo 2177435 3267737 := bstep (se 2 (by rfl) ⟨1225401, by rfl⟩ : syracuseStep 3267737 = 2450803) B2450803
theorem B2178491 : Blo 2177435 2178491 := bstep (se 1 (by rfl) ⟨1633868, by rfl⟩ : syracuseStep 2178491 = 3267737) B3267737
theorem B5888581 : Blo 2177435 5888581 := bbase (se 4 (by rfl) ⟨552054, by rfl⟩ : syracuseStep 5888581 = 1104109) (by norm_num)
theorem B31405765 : Blo 2177435 31405765 := bstep (se 4 (by rfl) ⟨2944290, by rfl⟩ : syracuseStep 31405765 = 5888581) B5888581
theorem B41874353 : Blo 2177435 41874353 := bstep (se 2 (by rfl) ⟨15702882, by rfl⟩ : syracuseStep 41874353 = 31405765) B31405765
theorem B27916235 : Blo 2177435 27916235 := bstep (se 1 (by rfl) ⟨20937176, by rfl⟩ : syracuseStep 27916235 = 41874353) B41874353
theorem B18610823 : Blo 2177435 18610823 := bstep (se 1 (by rfl) ⟨13958117, by rfl⟩ : syracuseStep 18610823 = 27916235) B27916235
theorem B12407215 : Blo 2177435 12407215 := bstep (se 1 (by rfl) ⟨9305411, by rfl⟩ : syracuseStep 12407215 = 18610823) B18610823
theorem B16542953 : Blo 2177435 16542953 := bstep (se 2 (by rfl) ⟨6203607, by rfl⟩ : syracuseStep 16542953 = 12407215) B12407215
theorem B11028635 : Blo 2177435 11028635 := bstep (se 1 (by rfl) ⟨8271476, by rfl⟩ : syracuseStep 11028635 = 16542953) B16542953
theorem B7352423 : Blo 2177435 7352423 := bstep (se 1 (by rfl) ⟨5514317, by rfl⟩ : syracuseStep 7352423 = 11028635) B11028635
theorem B4901615 : Blo 2177435 4901615 := bstep (se 1 (by rfl) ⟨3676211, by rfl⟩ : syracuseStep 4901615 = 7352423) B7352423
theorem B3267743 : Blo 2177435 3267743 := bstep (se 1 (by rfl) ⟨2450807, by rfl⟩ : syracuseStep 3267743 = 4901615) B4901615
theorem B2178495 : Blo 2177435 2178495 := bstep (se 1 (by rfl) ⟨1633871, by rfl⟩ : syracuseStep 2178495 = 3267743) B3267743
theorem B3267749 : Blo 2177435 3267749 := bbase (se 4 (by rfl) ⟨306351, by rfl⟩ : syracuseStep 3267749 = 612703) (by norm_num)
theorem B2178499 : Blo 2177435 2178499 := bstep (se 1 (by rfl) ⟨1633874, by rfl⟩ : syracuseStep 2178499 = 3267749) B3267749
theorem B2757169 : Blo 2177435 2757169 := bbase (se 2 (by rfl) ⟨1033938, by rfl⟩ : syracuseStep 2757169 = 2067877) (by norm_num)
theorem B3676225 : Blo 2177435 3676225 := bstep (se 2 (by rfl) ⟨1378584, by rfl⟩ : syracuseStep 3676225 = 2757169) B2757169
theorem B4901633 : Blo 2177435 4901633 := bstep (se 2 (by rfl) ⟨1838112, by rfl⟩ : syracuseStep 4901633 = 3676225) B3676225
theorem B3267755 : Blo 2177435 3267755 := bstep (se 1 (by rfl) ⟨2450816, by rfl⟩ : syracuseStep 3267755 = 4901633) B4901633
theorem B2178503 : Blo 2177435 2178503 := bstep (se 1 (by rfl) ⟨1633877, by rfl⟩ : syracuseStep 2178503 = 3267755) B3267755
theorem B2450821 : Blo 2177435 2450821 := bbase (se 4 (by rfl) ⟨229764, by rfl⟩ : syracuseStep 2450821 = 459529) (by norm_num)
theorem B3267761 : Blo 2177435 3267761 := bstep (se 2 (by rfl) ⟨1225410, by rfl⟩ : syracuseStep 3267761 = 2450821) B2450821
theorem B2178507 : Blo 2177435 2178507 := bstep (se 1 (by rfl) ⟨1633880, by rfl⟩ : syracuseStep 2178507 = 3267761) B3267761
theorem B4652741 : Blo 2177435 4652741 := bbase (se 4 (by rfl) ⟨436194, by rfl⟩ : syracuseStep 4652741 = 872389) (by norm_num)
theorem B3101827 : Blo 2177435 3101827 := bstep (se 1 (by rfl) ⟨2326370, by rfl⟩ : syracuseStep 3101827 = 4652741) B4652741
theorem B4135769 : Blo 2177435 4135769 := bstep (se 2 (by rfl) ⟨1550913, by rfl⟩ : syracuseStep 4135769 = 3101827) B3101827
theorem B2757179 : Blo 2177435 2757179 := bstep (se 1 (by rfl) ⟨2067884, by rfl⟩ : syracuseStep 2757179 = 4135769) B4135769
theorem B7352477 : Blo 2177435 7352477 := bstep (se 3 (by rfl) ⟨1378589, by rfl⟩ : syracuseStep 7352477 = 2757179) B2757179
theorem B4901651 : Blo 2177435 4901651 := bstep (se 1 (by rfl) ⟨3676238, by rfl⟩ : syracuseStep 4901651 = 7352477) B7352477
theorem B3267767 : Blo 2177435 3267767 := bstep (se 1 (by rfl) ⟨2450825, by rfl⟩ : syracuseStep 3267767 = 4901651) B4901651
theorem B2178511 : Blo 2177435 2178511 := bstep (se 1 (by rfl) ⟨1633883, by rfl⟩ : syracuseStep 2178511 = 3267767) B3267767
theorem B3267773 : Blo 2177435 3267773 := bbase (se 3 (by rfl) ⟨612707, by rfl⟩ : syracuseStep 3267773 = 1225415) (by norm_num)
theorem B2178515 : Blo 2177435 2178515 := bstep (se 1 (by rfl) ⟨1633886, by rfl⟩ : syracuseStep 2178515 = 3267773) B3267773
theorem B4901669 : Blo 2177435 4901669 := bbase (se 4 (by rfl) ⟨459531, by rfl⟩ : syracuseStep 4901669 = 919063) (by norm_num)
theorem B3267779 : Blo 2177435 3267779 := bstep (se 1 (by rfl) ⟨2450834, by rfl⟩ : syracuseStep 3267779 = 4901669) B4901669
theorem B2178519 : Blo 2177435 2178519 := bstep (se 1 (by rfl) ⟨1633889, by rfl⟩ : syracuseStep 2178519 = 3267779) B3267779
theorem B5514389 : Blo 2177435 5514389 := bbase (se 6 (by rfl) ⟨129243, by rfl⟩ : syracuseStep 5514389 = 258487) (by norm_num)
theorem B3676259 : Blo 2177435 3676259 := bstep (se 1 (by rfl) ⟨2757194, by rfl⟩ : syracuseStep 3676259 = 5514389) B5514389
theorem B2450839 : Blo 2177435 2450839 := bstep (se 1 (by rfl) ⟨1838129, by rfl⟩ : syracuseStep 2450839 = 3676259) B3676259
theorem B3267785 : Blo 2177435 3267785 := bstep (se 2 (by rfl) ⟨1225419, by rfl⟩ : syracuseStep 3267785 = 2450839) B2450839
theorem B2178523 : Blo 2177435 2178523 := bstep (se 1 (by rfl) ⟨1633892, by rfl⟩ : syracuseStep 2178523 = 3267785) B3267785
theorem B3489581 : Blo 2177435 3489581 := bbase (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) (by norm_num)
theorem B9305549 : Blo 2177435 9305549 := bstep (se 3 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 9305549 = 3489581) B3489581
theorem B6203699 : Blo 2177435 6203699 := bstep (se 1 (by rfl) ⟨4652774, by rfl⟩ : syracuseStep 6203699 = 9305549) B9305549
theorem B4135799 : Blo 2177435 4135799 := bstep (se 1 (by rfl) ⟨3101849, by rfl⟩ : syracuseStep 4135799 = 6203699) B6203699
theorem B11028797 : Blo 2177435 11028797 := bstep (se 3 (by rfl) ⟨2067899, by rfl⟩ : syracuseStep 11028797 = 4135799) B4135799
theorem B7352531 : Blo 2177435 7352531 := bstep (se 1 (by rfl) ⟨5514398, by rfl⟩ : syracuseStep 7352531 = 11028797) B11028797
theorem B4901687 : Blo 2177435 4901687 := bstep (se 1 (by rfl) ⟨3676265, by rfl⟩ : syracuseStep 4901687 = 7352531) B7352531
theorem B3267791 : Blo 2177435 3267791 := bstep (se 1 (by rfl) ⟨2450843, by rfl⟩ : syracuseStep 3267791 = 4901687) B4901687
theorem B2178527 : Blo 2177435 2178527 := bstep (se 1 (by rfl) ⟨1633895, by rfl⟩ : syracuseStep 2178527 = 3267791) B3267791
theorem B3267797 : Blo 2177435 3267797 := bbase (se 7 (by rfl) ⟨38294, by rfl⟩ : syracuseStep 3267797 = 76589) (by norm_num)
theorem B2178531 : Blo 2177435 2178531 := bstep (se 1 (by rfl) ⟨1633898, by rfl⟩ : syracuseStep 2178531 = 3267797) B3267797
theorem B3101861 : Blo 2177435 3101861 := bbase (se 4 (by rfl) ⟨290799, by rfl⟩ : syracuseStep 3101861 = 581599) (by norm_num)
theorem B8271629 : Blo 2177435 8271629 := bstep (se 3 (by rfl) ⟨1550930, by rfl⟩ : syracuseStep 8271629 = 3101861) B3101861
theorem B5514419 : Blo 2177435 5514419 := bstep (se 1 (by rfl) ⟨4135814, by rfl⟩ : syracuseStep 5514419 = 8271629) B8271629
theorem B3676279 : Blo 2177435 3676279 := bstep (se 1 (by rfl) ⟨2757209, by rfl⟩ : syracuseStep 3676279 = 5514419) B5514419
theorem B4901705 : Blo 2177435 4901705 := bstep (se 2 (by rfl) ⟨1838139, by rfl⟩ : syracuseStep 4901705 = 3676279) B3676279
theorem B3267803 : Blo 2177435 3267803 := bstep (se 1 (by rfl) ⟨2450852, by rfl⟩ : syracuseStep 3267803 = 4901705) B4901705
theorem B2178535 : Blo 2177435 2178535 := bstep (se 1 (by rfl) ⟨1633901, by rfl⟩ : syracuseStep 2178535 = 3267803) B3267803
theorem B2450857 : Blo 2177435 2450857 := bbase (se 2 (by rfl) ⟨919071, by rfl⟩ : syracuseStep 2450857 = 1838143) (by norm_num)
theorem B3267809 : Blo 2177435 3267809 := bstep (se 2 (by rfl) ⟨1225428, by rfl⟩ : syracuseStep 3267809 = 2450857) B2450857
theorem B2178539 : Blo 2177435 2178539 := bstep (se 1 (by rfl) ⟨1633904, by rfl⟩ : syracuseStep 2178539 = 3267809) B3267809
theorem B2617205 : Blo 2177435 2617205 := bbase (se 5 (by rfl) ⟨122681, by rfl⟩ : syracuseStep 2617205 = 245363) (by norm_num)
theorem B6979213 : Blo 2177435 6979213 := bstep (se 3 (by rfl) ⟨1308602, by rfl⟩ : syracuseStep 6979213 = 2617205) B2617205
theorem B9305617 : Blo 2177435 9305617 := bstep (se 2 (by rfl) ⟨3489606, by rfl⟩ : syracuseStep 9305617 = 6979213) B6979213
theorem B12407489 : Blo 2177435 12407489 := bstep (se 2 (by rfl) ⟨4652808, by rfl⟩ : syracuseStep 12407489 = 9305617) B9305617
theorem B8271659 : Blo 2177435 8271659 := bstep (se 1 (by rfl) ⟨6203744, by rfl⟩ : syracuseStep 8271659 = 12407489) B12407489
theorem B5514439 : Blo 2177435 5514439 := bstep (se 1 (by rfl) ⟨4135829, by rfl⟩ : syracuseStep 5514439 = 8271659) B8271659
theorem B7352585 : Blo 2177435 7352585 := bstep (se 2 (by rfl) ⟨2757219, by rfl⟩ : syracuseStep 7352585 = 5514439) B5514439
theorem B4901723 : Blo 2177435 4901723 := bstep (se 1 (by rfl) ⟨3676292, by rfl⟩ : syracuseStep 4901723 = 7352585) B7352585
theorem B3267815 : Blo 2177435 3267815 := bstep (se 1 (by rfl) ⟨2450861, by rfl⟩ : syracuseStep 3267815 = 4901723) B4901723
theorem B2178543 : Blo 2177435 2178543 := bstep (se 1 (by rfl) ⟨1633907, by rfl⟩ : syracuseStep 2178543 = 3267815) B3267815
theorem B3267821 : Blo 2177435 3267821 := bbase (se 3 (by rfl) ⟨612716, by rfl⟩ : syracuseStep 3267821 = 1225433) (by norm_num)
theorem B2178547 : Blo 2177435 2178547 := bstep (se 1 (by rfl) ⟨1633910, by rfl⟩ : syracuseStep 2178547 = 3267821) B3267821
theorem B4901741 : Blo 2177435 4901741 := bbase (se 3 (by rfl) ⟨919076, by rfl⟩ : syracuseStep 4901741 = 1838153) (by norm_num)
theorem B3267827 : Blo 2177435 3267827 := bstep (se 1 (by rfl) ⟨2450870, by rfl⟩ : syracuseStep 3267827 = 4901741) B4901741
theorem B2178551 : Blo 2177435 2178551 := bstep (se 1 (by rfl) ⟨1633913, by rfl⟩ : syracuseStep 2178551 = 3267827) B3267827
theorem B4135853 : Blo 2177435 4135853 := bbase (se 3 (by rfl) ⟨775472, by rfl⟩ : syracuseStep 4135853 = 1550945) (by norm_num)
theorem B2757235 : Blo 2177435 2757235 := bstep (se 1 (by rfl) ⟨2067926, by rfl⟩ : syracuseStep 2757235 = 4135853) B4135853
theorem B3676313 : Blo 2177435 3676313 := bstep (se 2 (by rfl) ⟨1378617, by rfl⟩ : syracuseStep 3676313 = 2757235) B2757235
theorem B2450875 : Blo 2177435 2450875 := bstep (se 1 (by rfl) ⟨1838156, by rfl⟩ : syracuseStep 2450875 = 3676313) B3676313
theorem B3267833 : Blo 2177435 3267833 := bstep (se 2 (by rfl) ⟨1225437, by rfl⟩ : syracuseStep 3267833 = 2450875) B2450875
theorem B2178555 : Blo 2177435 2178555 := bstep (se 1 (by rfl) ⟨1633916, by rfl⟩ : syracuseStep 2178555 = 3267833) B3267833
theorem B2518213 : Blo 2177435 2518213 := bbase (se 4 (by rfl) ⟨236082, by rfl⟩ : syracuseStep 2518213 = 472165) (by norm_num)
theorem B3357617 : Blo 2177435 3357617 := bstep (se 2 (by rfl) ⟨1259106, by rfl⟩ : syracuseStep 3357617 = 2518213) B2518213
theorem B8953645 : Blo 2177435 8953645 := bstep (se 3 (by rfl) ⟨1678808, by rfl⟩ : syracuseStep 8953645 = 3357617) B3357617
theorem B11938193 : Blo 2177435 11938193 := bstep (se 2 (by rfl) ⟨4476822, by rfl⟩ : syracuseStep 11938193 = 8953645) B8953645
theorem B7958795 : Blo 2177435 7958795 := bstep (se 1 (by rfl) ⟨5969096, by rfl⟩ : syracuseStep 7958795 = 11938193) B11938193
theorem B21223453 : Blo 2177435 21223453 := bstep (se 3 (by rfl) ⟨3979397, by rfl⟩ : syracuseStep 21223453 = 7958795) B7958795
theorem B28297937 : Blo 2177435 28297937 := bstep (se 2 (by rfl) ⟨10611726, by rfl⟩ : syracuseStep 28297937 = 21223453) B21223453
theorem B75461165 : Blo 2177435 75461165 := bstep (se 3 (by rfl) ⟨14148968, by rfl⟩ : syracuseStep 75461165 = 28297937) B28297937
theorem B50307443 : Blo 2177435 50307443 := bstep (se 1 (by rfl) ⟨37730582, by rfl⟩ : syracuseStep 50307443 = 75461165) B75461165
theorem B33538295 : Blo 2177435 33538295 := bstep (se 1 (by rfl) ⟨25153721, by rfl⟩ : syracuseStep 33538295 = 50307443) B50307443
theorem B22358863 : Blo 2177435 22358863 := bstep (se 1 (by rfl) ⟨16769147, by rfl⟩ : syracuseStep 22358863 = 33538295) B33538295
theorem B29811817 : Blo 2177435 29811817 := bstep (se 2 (by rfl) ⟨11179431, by rfl⟩ : syracuseStep 29811817 = 22358863) B22358863
theorem B158996357 : Blo 2177435 158996357 := bstep (se 4 (by rfl) ⟨14905908, by rfl⟩ : syracuseStep 158996357 = 29811817) B29811817
theorem B105997571 : Blo 2177435 105997571 := bstep (se 1 (by rfl) ⟨79498178, by rfl⟩ : syracuseStep 105997571 = 158996357) B158996357
theorem B70665047 : Blo 2177435 70665047 := bstep (se 1 (by rfl) ⟨52998785, by rfl⟩ : syracuseStep 70665047 = 105997571) B105997571
theorem B47110031 : Blo 2177435 47110031 := bstep (se 1 (by rfl) ⟨35332523, by rfl⟩ : syracuseStep 47110031 = 70665047) B70665047
theorem B31406687 : Blo 2177435 31406687 := bstep (se 1 (by rfl) ⟨23555015, by rfl⟩ : syracuseStep 31406687 = 47110031) B47110031
theorem B20937791 : Blo 2177435 20937791 := bstep (se 1 (by rfl) ⟨15703343, by rfl⟩ : syracuseStep 20937791 = 31406687) B31406687
theorem B55834109 : Blo 2177435 55834109 := bstep (se 3 (by rfl) ⟨10468895, by rfl⟩ : syracuseStep 55834109 = 20937791) B20937791
theorem B37222739 : Blo 2177435 37222739 := bstep (se 1 (by rfl) ⟨27917054, by rfl⟩ : syracuseStep 37222739 = 55834109) B55834109
theorem B24815159 : Blo 2177435 24815159 := bstep (se 1 (by rfl) ⟨18611369, by rfl⟩ : syracuseStep 24815159 = 37222739) B37222739
theorem B16543439 : Blo 2177435 16543439 := bstep (se 1 (by rfl) ⟨12407579, by rfl⟩ : syracuseStep 16543439 = 24815159) B24815159
theorem B11028959 : Blo 2177435 11028959 := bstep (se 1 (by rfl) ⟨8271719, by rfl⟩ : syracuseStep 11028959 = 16543439) B16543439
theorem B7352639 : Blo 2177435 7352639 := bstep (se 1 (by rfl) ⟨5514479, by rfl⟩ : syracuseStep 7352639 = 11028959) B11028959
theorem B4901759 : Blo 2177435 4901759 := bstep (se 1 (by rfl) ⟨3676319, by rfl⟩ : syracuseStep 4901759 = 7352639) B7352639
theorem B3267839 : Blo 2177435 3267839 := bstep (se 1 (by rfl) ⟨2450879, by rfl⟩ : syracuseStep 3267839 = 4901759) B4901759
theorem B2178559 : Blo 2177435 2178559 := bstep (se 1 (by rfl) ⟨1633919, by rfl⟩ : syracuseStep 2178559 = 3267839) B3267839
theorem B3267845 : Blo 2177435 3267845 := bbase (se 4 (by rfl) ⟨306360, by rfl⟩ : syracuseStep 3267845 = 612721) (by norm_num)
theorem B2178563 : Blo 2177435 2178563 := bstep (se 1 (by rfl) ⟨1633922, by rfl⟩ : syracuseStep 2178563 = 3267845) B3267845
theorem B3676333 : Blo 2177435 3676333 := bbase (se 3 (by rfl) ⟨689312, by rfl⟩ : syracuseStep 3676333 = 1378625) (by norm_num)
theorem B4901777 : Blo 2177435 4901777 := bstep (se 2 (by rfl) ⟨1838166, by rfl⟩ : syracuseStep 4901777 = 3676333) B3676333
theorem B3267851 : Blo 2177435 3267851 := bstep (se 1 (by rfl) ⟨2450888, by rfl⟩ : syracuseStep 3267851 = 4901777) B4901777
theorem B2178567 : Blo 2177435 2178567 := bstep (se 1 (by rfl) ⟨1633925, by rfl⟩ : syracuseStep 2178567 = 3267851) B3267851
theorem B2450893 : Blo 2177435 2450893 := bbase (se 3 (by rfl) ⟨459542, by rfl⟩ : syracuseStep 2450893 = 919085) (by norm_num)
theorem B3267857 : Blo 2177435 3267857 := bstep (se 2 (by rfl) ⟨1225446, by rfl⟩ : syracuseStep 3267857 = 2450893) B2450893
theorem B2178571 : Blo 2177435 2178571 := bstep (se 1 (by rfl) ⟨1633928, by rfl⟩ : syracuseStep 2178571 = 3267857) B3267857
theorem B7352693 : Blo 2177435 7352693 := bbase (se 5 (by rfl) ⟨344657, by rfl⟩ : syracuseStep 7352693 = 689315) (by norm_num)
theorem B4901795 : Blo 2177435 4901795 := bstep (se 1 (by rfl) ⟨3676346, by rfl⟩ : syracuseStep 4901795 = 7352693) B7352693
theorem B3267863 : Blo 2177435 3267863 := bstep (se 1 (by rfl) ⟨2450897, by rfl⟩ : syracuseStep 3267863 = 4901795) B4901795
theorem B2178575 : Blo 2177435 2178575 := bstep (se 1 (by rfl) ⟨1633931, by rfl⟩ : syracuseStep 2178575 = 3267863) B3267863
theorem B3267869 : Blo 2177435 3267869 := bbase (se 3 (by rfl) ⟨612725, by rfl⟩ : syracuseStep 3267869 = 1225451) (by norm_num)
theorem B2178579 : Blo 2177435 2178579 := bstep (se 1 (by rfl) ⟨1633934, by rfl⟩ : syracuseStep 2178579 = 3267869) B3267869
theorem B4901813 : Blo 2177435 4901813 := bbase (se 5 (by rfl) ⟨229772, by rfl⟩ : syracuseStep 4901813 = 459545) (by norm_num)
theorem B3267875 : Blo 2177435 3267875 := bstep (se 1 (by rfl) ⟨2450906, by rfl⟩ : syracuseStep 3267875 = 4901813) B4901813
theorem B2178583 : Blo 2177435 2178583 := bstep (se 1 (by rfl) ⟨1633937, by rfl⟩ : syracuseStep 2178583 = 3267875) B3267875
theorem B21223733 : Blo 2177435 21223733 := bbase (se 5 (by rfl) ⟨994862, by rfl⟩ : syracuseStep 21223733 = 1989725) (by norm_num)
theorem B226386485 : Blo 2177435 226386485 := bstep (se 5 (by rfl) ⟨10611866, by rfl⟩ : syracuseStep 226386485 = 21223733) B21223733
theorem B150924323 : Blo 2177435 150924323 := bstep (se 1 (by rfl) ⟨113193242, by rfl⟩ : syracuseStep 150924323 = 226386485) B226386485
theorem B100616215 : Blo 2177435 100616215 := bstep (se 1 (by rfl) ⟨75462161, by rfl⟩ : syracuseStep 100616215 = 150924323) B150924323
theorem B134154953 : Blo 2177435 134154953 := bstep (se 2 (by rfl) ⟨50308107, by rfl⟩ : syracuseStep 134154953 = 100616215) B100616215
theorem B89436635 : Blo 2177435 89436635 := bstep (se 1 (by rfl) ⟨67077476, by rfl⟩ : syracuseStep 89436635 = 134154953) B134154953
theorem B59624423 : Blo 2177435 59624423 := bstep (se 1 (by rfl) ⟨44718317, by rfl⟩ : syracuseStep 59624423 = 89436635) B89436635
theorem B39749615 : Blo 2177435 39749615 := bstep (se 1 (by rfl) ⟨29812211, by rfl⟩ : syracuseStep 39749615 = 59624423) B59624423
theorem B26499743 : Blo 2177435 26499743 := bstep (se 1 (by rfl) ⟨19874807, by rfl⟩ : syracuseStep 26499743 = 39749615) B39749615
theorem B17666495 : Blo 2177435 17666495 := bstep (se 1 (by rfl) ⟨13249871, by rfl⟩ : syracuseStep 17666495 = 26499743) B26499743
theorem B11777663 : Blo 2177435 11777663 := bstep (se 1 (by rfl) ⟨8833247, by rfl⟩ : syracuseStep 11777663 = 17666495) B17666495
theorem B7851775 : Blo 2177435 7851775 := bstep (se 1 (by rfl) ⟨5888831, by rfl⟩ : syracuseStep 7851775 = 11777663) B11777663
theorem B10469033 : Blo 2177435 10469033 := bstep (se 2 (by rfl) ⟨3925887, by rfl⟩ : syracuseStep 10469033 = 7851775) B7851775
theorem B6979355 : Blo 2177435 6979355 := bstep (se 1 (by rfl) ⟨5234516, by rfl⟩ : syracuseStep 6979355 = 10469033) B10469033
theorem B4652903 : Blo 2177435 4652903 := bstep (se 1 (by rfl) ⟨3489677, by rfl⟩ : syracuseStep 4652903 = 6979355) B6979355
theorem B12407741 : Blo 2177435 12407741 := bstep (se 3 (by rfl) ⟨2326451, by rfl⟩ : syracuseStep 12407741 = 4652903) B4652903
theorem B8271827 : Blo 2177435 8271827 := bstep (se 1 (by rfl) ⟨6203870, by rfl⟩ : syracuseStep 8271827 = 12407741) B12407741
theorem B5514551 : Blo 2177435 5514551 := bstep (se 1 (by rfl) ⟨4135913, by rfl⟩ : syracuseStep 5514551 = 8271827) B8271827
theorem B3676367 : Blo 2177435 3676367 := bstep (se 1 (by rfl) ⟨2757275, by rfl⟩ : syracuseStep 3676367 = 5514551) B5514551
theorem B2450911 : Blo 2177435 2450911 := bstep (se 1 (by rfl) ⟨1838183, by rfl⟩ : syracuseStep 2450911 = 3676367) B3676367
theorem B3267881 : Blo 2177435 3267881 := bstep (se 2 (by rfl) ⟨1225455, by rfl⟩ : syracuseStep 3267881 = 2450911) B2450911
theorem B2178587 : Blo 2177435 2178587 := bstep (se 1 (by rfl) ⟨1633940, by rfl⟩ : syracuseStep 2178587 = 3267881) B3267881
theorem B3726533 : Blo 2177435 3726533 := bbase (se 4 (by rfl) ⟨349362, by rfl⟩ : syracuseStep 3726533 = 698725) (by norm_num)
theorem B9937421 : Blo 2177435 9937421 := bstep (se 3 (by rfl) ⟨1863266, by rfl⟩ : syracuseStep 9937421 = 3726533) B3726533
theorem B6624947 : Blo 2177435 6624947 := bstep (se 1 (by rfl) ⟨4968710, by rfl⟩ : syracuseStep 6624947 = 9937421) B9937421
theorem B17666525 : Blo 2177435 17666525 := bstep (se 3 (by rfl) ⟨3312473, by rfl⟩ : syracuseStep 17666525 = 6624947) B6624947
theorem B11777683 : Blo 2177435 11777683 := bstep (se 1 (by rfl) ⟨8833262, by rfl⟩ : syracuseStep 11777683 = 17666525) B17666525
theorem B15703577 : Blo 2177435 15703577 := bstep (se 2 (by rfl) ⟨5888841, by rfl⟩ : syracuseStep 15703577 = 11777683) B11777683
theorem B10469051 : Blo 2177435 10469051 := bstep (se 1 (by rfl) ⟨7851788, by rfl⟩ : syracuseStep 10469051 = 15703577) B15703577
theorem B6979367 : Blo 2177435 6979367 := bstep (se 1 (by rfl) ⟨5234525, by rfl⟩ : syracuseStep 6979367 = 10469051) B10469051
theorem B4652911 : Blo 2177435 4652911 := bstep (se 1 (by rfl) ⟨3489683, by rfl⟩ : syracuseStep 4652911 = 6979367) B6979367
theorem B6203881 : Blo 2177435 6203881 := bstep (se 2 (by rfl) ⟨2326455, by rfl⟩ : syracuseStep 6203881 = 4652911) B4652911
theorem B8271841 : Blo 2177435 8271841 := bstep (se 2 (by rfl) ⟨3101940, by rfl⟩ : syracuseStep 8271841 = 6203881) B6203881
theorem B11029121 : Blo 2177435 11029121 := bstep (se 2 (by rfl) ⟨4135920, by rfl⟩ : syracuseStep 11029121 = 8271841) B8271841
theorem B7352747 : Blo 2177435 7352747 := bstep (se 1 (by rfl) ⟨5514560, by rfl⟩ : syracuseStep 7352747 = 11029121) B11029121
theorem B4901831 : Blo 2177435 4901831 := bstep (se 1 (by rfl) ⟨3676373, by rfl⟩ : syracuseStep 4901831 = 7352747) B7352747
theorem B3267887 : Blo 2177435 3267887 := bstep (se 1 (by rfl) ⟨2450915, by rfl⟩ : syracuseStep 3267887 = 4901831) B4901831
theorem B2178591 : Blo 2177435 2178591 := bstep (se 1 (by rfl) ⟨1633943, by rfl⟩ : syracuseStep 2178591 = 3267887) B3267887
theorem B3267893 : Blo 2177435 3267893 := bbase (se 5 (by rfl) ⟨153182, by rfl⟩ : syracuseStep 3267893 = 306365) (by norm_num)
theorem B2178595 : Blo 2177435 2178595 := bstep (se 1 (by rfl) ⟨1633946, by rfl⟩ : syracuseStep 2178595 = 3267893) B3267893
theorem B5514581 : Blo 2177435 5514581 := bbase (se 12 (by rfl) ⟨2019, by rfl⟩ : syracuseStep 5514581 = 4039) (by norm_num)
theorem B3676387 : Blo 2177435 3676387 := bstep (se 1 (by rfl) ⟨2757290, by rfl⟩ : syracuseStep 3676387 = 5514581) B5514581
theorem B4901849 : Blo 2177435 4901849 := bstep (se 2 (by rfl) ⟨1838193, by rfl⟩ : syracuseStep 4901849 = 3676387) B3676387
theorem B3267899 : Blo 2177435 3267899 := bstep (se 1 (by rfl) ⟨2450924, by rfl⟩ : syracuseStep 3267899 = 4901849) B4901849
theorem B2178599 : Blo 2177435 2178599 := bstep (se 1 (by rfl) ⟨1633949, by rfl⟩ : syracuseStep 2178599 = 3267899) B3267899
theorem B2450929 : Blo 2177435 2450929 := bbase (se 2 (by rfl) ⟨919098, by rfl⟩ : syracuseStep 2450929 = 1838197) (by norm_num)
theorem B3267905 : Blo 2177435 3267905 := bstep (se 2 (by rfl) ⟨1225464, by rfl⟩ : syracuseStep 3267905 = 2450929) B2450929
theorem B2178603 : Blo 2177435 2178603 := bstep (se 1 (by rfl) ⟨1633952, by rfl⟩ : syracuseStep 2178603 = 3267905) B3267905
theorem B13958837 : Blo 2177435 13958837 := bbase (se 5 (by rfl) ⟨654320, by rfl⟩ : syracuseStep 13958837 = 1308641) (by norm_num)
theorem B9305891 : Blo 2177435 9305891 := bstep (se 1 (by rfl) ⟨6979418, by rfl⟩ : syracuseStep 9305891 = 13958837) B13958837
theorem B6203927 : Blo 2177435 6203927 := bstep (se 1 (by rfl) ⟨4652945, by rfl⟩ : syracuseStep 6203927 = 9305891) B9305891
theorem B4135951 : Blo 2177435 4135951 := bstep (se 1 (by rfl) ⟨3101963, by rfl⟩ : syracuseStep 4135951 = 6203927) B6203927
theorem B5514601 : Blo 2177435 5514601 := bstep (se 2 (by rfl) ⟨2067975, by rfl⟩ : syracuseStep 5514601 = 4135951) B4135951
theorem B7352801 : Blo 2177435 7352801 := bstep (se 2 (by rfl) ⟨2757300, by rfl⟩ : syracuseStep 7352801 = 5514601) B5514601
theorem B4901867 : Blo 2177435 4901867 := bstep (se 1 (by rfl) ⟨3676400, by rfl⟩ : syracuseStep 4901867 = 7352801) B7352801
theorem B3267911 : Blo 2177435 3267911 := bstep (se 1 (by rfl) ⟨2450933, by rfl⟩ : syracuseStep 3267911 = 4901867) B4901867
theorem B2178607 : Blo 2177435 2178607 := bstep (se 1 (by rfl) ⟨1633955, by rfl⟩ : syracuseStep 2178607 = 3267911) B3267911
theorem B3267917 : Blo 2177435 3267917 := bbase (se 3 (by rfl) ⟨612734, by rfl⟩ : syracuseStep 3267917 = 1225469) (by norm_num)
theorem B2178611 : Blo 2177435 2178611 := bstep (se 1 (by rfl) ⟨1633958, by rfl⟩ : syracuseStep 2178611 = 3267917) B3267917
theorem B4901885 : Blo 2177435 4901885 := bbase (se 3 (by rfl) ⟨919103, by rfl⟩ : syracuseStep 4901885 = 1838207) (by norm_num)
theorem B3267923 : Blo 2177435 3267923 := bstep (se 1 (by rfl) ⟨2450942, by rfl⟩ : syracuseStep 3267923 = 4901885) B4901885
theorem B2178615 : Blo 2177435 2178615 := bstep (se 1 (by rfl) ⟨1633961, by rfl⟩ : syracuseStep 2178615 = 3267923) B3267923
theorem B3676421 : Blo 2177435 3676421 := bbase (se 4 (by rfl) ⟨344664, by rfl⟩ : syracuseStep 3676421 = 689329) (by norm_num)
theorem B2450947 : Blo 2177435 2450947 := bstep (se 1 (by rfl) ⟨1838210, by rfl⟩ : syracuseStep 2450947 = 3676421) B3676421
theorem B3267929 : Blo 2177435 3267929 := bstep (se 2 (by rfl) ⟨1225473, by rfl⟩ : syracuseStep 3267929 = 2450947) B2450947
theorem B2178619 : Blo 2177435 2178619 := bstep (se 1 (by rfl) ⟨1633964, by rfl⟩ : syracuseStep 2178619 = 3267929) B3267929
theorem B16543925 : Blo 2177435 16543925 := bbase (se 5 (by rfl) ⟨775496, by rfl⟩ : syracuseStep 16543925 = 1550993) (by norm_num)
theorem B11029283 : Blo 2177435 11029283 := bstep (se 1 (by rfl) ⟨8271962, by rfl⟩ : syracuseStep 11029283 = 16543925) B16543925
theorem B7352855 : Blo 2177435 7352855 := bstep (se 1 (by rfl) ⟨5514641, by rfl⟩ : syracuseStep 7352855 = 11029283) B11029283
theorem B4901903 : Blo 2177435 4901903 := bstep (se 1 (by rfl) ⟨3676427, by rfl⟩ : syracuseStep 4901903 = 7352855) B7352855
theorem B3267935 : Blo 2177435 3267935 := bstep (se 1 (by rfl) ⟨2450951, by rfl⟩ : syracuseStep 3267935 = 4901903) B4901903
theorem B2178623 : Blo 2177435 2178623 := bstep (se 1 (by rfl) ⟨1633967, by rfl⟩ : syracuseStep 2178623 = 3267935) B3267935
theorem B3267941 : Blo 2177435 3267941 := bbase (se 4 (by rfl) ⟨306369, by rfl⟩ : syracuseStep 3267941 = 612739) (by norm_num)
theorem B2178627 : Blo 2177435 2178627 := bstep (se 1 (by rfl) ⟨1633970, by rfl⟩ : syracuseStep 2178627 = 3267941) B3267941
theorem B4135997 : Blo 2177435 4135997 := bbase (se 3 (by rfl) ⟨775499, by rfl⟩ : syracuseStep 4135997 = 1550999) (by norm_num)
theorem B2757331 : Blo 2177435 2757331 := bstep (se 1 (by rfl) ⟨2067998, by rfl⟩ : syracuseStep 2757331 = 4135997) B4135997
theorem B3676441 : Blo 2177435 3676441 := bstep (se 2 (by rfl) ⟨1378665, by rfl⟩ : syracuseStep 3676441 = 2757331) B2757331
theorem B4901921 : Blo 2177435 4901921 := bstep (se 2 (by rfl) ⟨1838220, by rfl⟩ : syracuseStep 4901921 = 3676441) B3676441
theorem B3267947 : Blo 2177435 3267947 := bstep (se 1 (by rfl) ⟨2450960, by rfl⟩ : syracuseStep 3267947 = 4901921) B4901921
theorem B2178631 : Blo 2177435 2178631 := bstep (se 1 (by rfl) ⟨1633973, by rfl⟩ : syracuseStep 2178631 = 3267947) B3267947
theorem B2450965 : Blo 2177435 2450965 := bbase (se 6 (by rfl) ⟨57444, by rfl⟩ : syracuseStep 2450965 = 114889) (by norm_num)
theorem B3267953 : Blo 2177435 3267953 := bstep (se 2 (by rfl) ⟨1225482, by rfl⟩ : syracuseStep 3267953 = 2450965) B2450965
theorem B2178635 : Blo 2177435 2178635 := bstep (se 1 (by rfl) ⟨1633976, by rfl⟩ : syracuseStep 2178635 = 3267953) B3267953
theorem B2757341 : Blo 2177435 2757341 := bbase (se 3 (by rfl) ⟨517001, by rfl⟩ : syracuseStep 2757341 = 1034003) (by norm_num)
theorem B7352909 : Blo 2177435 7352909 := bstep (se 3 (by rfl) ⟨1378670, by rfl⟩ : syracuseStep 7352909 = 2757341) B2757341
theorem B4901939 : Blo 2177435 4901939 := bstep (se 1 (by rfl) ⟨3676454, by rfl⟩ : syracuseStep 4901939 = 7352909) B7352909
theorem B3267959 : Blo 2177435 3267959 := bstep (se 1 (by rfl) ⟨2450969, by rfl⟩ : syracuseStep 3267959 = 4901939) B4901939
theorem B2178639 : Blo 2177435 2178639 := bstep (se 1 (by rfl) ⟨1633979, by rfl⟩ : syracuseStep 2178639 = 3267959) B3267959
theorem B3267965 : Blo 2177435 3267965 := bbase (se 3 (by rfl) ⟨612743, by rfl⟩ : syracuseStep 3267965 = 1225487) (by norm_num)
theorem B2178643 : Blo 2177435 2178643 := bstep (se 1 (by rfl) ⟨1633982, by rfl⟩ : syracuseStep 2178643 = 3267965) B3267965
theorem B4901957 : Blo 2177435 4901957 := bbase (se 4 (by rfl) ⟨459558, by rfl⟩ : syracuseStep 4901957 = 919117) (by norm_num)
theorem B3267971 : Blo 2177435 3267971 := bstep (se 1 (by rfl) ⟨2450978, by rfl⟩ : syracuseStep 3267971 = 4901957) B4901957
theorem B2178647 : Blo 2177435 2178647 := bstep (se 1 (by rfl) ⟨1633985, by rfl⟩ : syracuseStep 2178647 = 3267971) B3267971
theorem B6204053 : Blo 2177435 6204053 := bbase (se 6 (by rfl) ⟨145407, by rfl⟩ : syracuseStep 6204053 = 290815) (by norm_num)
theorem B4136035 : Blo 2177435 4136035 := bstep (se 1 (by rfl) ⟨3102026, by rfl⟩ : syracuseStep 4136035 = 6204053) B6204053
theorem B5514713 : Blo 2177435 5514713 := bstep (se 2 (by rfl) ⟨2068017, by rfl⟩ : syracuseStep 5514713 = 4136035) B4136035
theorem B3676475 : Blo 2177435 3676475 := bstep (se 1 (by rfl) ⟨2757356, by rfl⟩ : syracuseStep 3676475 = 5514713) B5514713
theorem B2450983 : Blo 2177435 2450983 := bstep (se 1 (by rfl) ⟨1838237, by rfl⟩ : syracuseStep 2450983 = 3676475) B3676475
theorem B3267977 : Blo 2177435 3267977 := bstep (se 2 (by rfl) ⟨1225491, by rfl⟩ : syracuseStep 3267977 = 2450983) B2450983
theorem B2178651 : Blo 2177435 2178651 := bstep (se 1 (by rfl) ⟨1633988, by rfl⟩ : syracuseStep 2178651 = 3267977) B3267977
theorem B11029445 : Blo 2177435 11029445 := bbase (se 4 (by rfl) ⟨1034010, by rfl⟩ : syracuseStep 11029445 = 2068021) (by norm_num)
theorem B7352963 : Blo 2177435 7352963 := bstep (se 1 (by rfl) ⟨5514722, by rfl⟩ : syracuseStep 7352963 = 11029445) B11029445
theorem B4901975 : Blo 2177435 4901975 := bstep (se 1 (by rfl) ⟨3676481, by rfl⟩ : syracuseStep 4901975 = 7352963) B7352963
theorem B3267983 : Blo 2177435 3267983 := bstep (se 1 (by rfl) ⟨2450987, by rfl⟩ : syracuseStep 3267983 = 4901975) B4901975
theorem B2178655 : Blo 2177435 2178655 := bstep (se 1 (by rfl) ⟨1633991, by rfl⟩ : syracuseStep 2178655 = 3267983) B3267983
theorem B3267989 : Blo 2177435 3267989 := bbase (se 6 (by rfl) ⟨76593, by rfl⟩ : syracuseStep 3267989 = 153187) (by norm_num)
theorem B2178659 : Blo 2177435 2178659 := bstep (se 1 (by rfl) ⟨1633994, by rfl⟩ : syracuseStep 2178659 = 3267989) B3267989
theorem B2208389 : Blo 2177435 2208389 := bbase (se 4 (by rfl) ⟨207036, by rfl⟩ : syracuseStep 2208389 = 414073) (by norm_num)
theorem B5889037 : Blo 2177435 5889037 := bstep (se 3 (by rfl) ⟨1104194, by rfl⟩ : syracuseStep 5889037 = 2208389) B2208389
theorem B7852049 : Blo 2177435 7852049 := bstep (se 2 (by rfl) ⟨2944518, by rfl⟩ : syracuseStep 7852049 = 5889037) B5889037
theorem B5234699 : Blo 2177435 5234699 := bstep (se 1 (by rfl) ⟨3926024, by rfl⟩ : syracuseStep 5234699 = 7852049) B7852049
theorem B3489799 : Blo 2177435 3489799 := bstep (se 1 (by rfl) ⟨2617349, by rfl⟩ : syracuseStep 3489799 = 5234699) B5234699
theorem B4653065 : Blo 2177435 4653065 := bstep (se 2 (by rfl) ⟨1744899, by rfl⟩ : syracuseStep 4653065 = 3489799) B3489799
theorem B12408173 : Blo 2177435 12408173 := bstep (se 3 (by rfl) ⟨2326532, by rfl⟩ : syracuseStep 12408173 = 4653065) B4653065
theorem B8272115 : Blo 2177435 8272115 := bstep (se 1 (by rfl) ⟨6204086, by rfl⟩ : syracuseStep 8272115 = 12408173) B12408173
theorem B5514743 : Blo 2177435 5514743 := bstep (se 1 (by rfl) ⟨4136057, by rfl⟩ : syracuseStep 5514743 = 8272115) B8272115
theorem B3676495 : Blo 2177435 3676495 := bstep (se 1 (by rfl) ⟨2757371, by rfl⟩ : syracuseStep 3676495 = 5514743) B5514743
theorem B4901993 : Blo 2177435 4901993 := bstep (se 2 (by rfl) ⟨1838247, by rfl⟩ : syracuseStep 4901993 = 3676495) B3676495
theorem B3267995 : Blo 2177435 3267995 := bstep (se 1 (by rfl) ⟨2450996, by rfl⟩ : syracuseStep 3267995 = 4901993) B4901993
theorem B2178663 : Blo 2177435 2178663 := bstep (se 1 (by rfl) ⟨1633997, by rfl⟩ : syracuseStep 2178663 = 3267995) B3267995
theorem B2451001 : Blo 2177435 2451001 := bbase (se 2 (by rfl) ⟨919125, by rfl⟩ : syracuseStep 2451001 = 1838251) (by norm_num)
theorem B3268001 : Blo 2177435 3268001 := bstep (se 2 (by rfl) ⟨1225500, by rfl⟩ : syracuseStep 3268001 = 2451001) B2451001
theorem B2178667 : Blo 2177435 2178667 := bstep (se 1 (by rfl) ⟨1634000, by rfl⟩ : syracuseStep 2178667 = 3268001) B3268001
theorem B2326541 : Blo 2177435 2326541 := bbase (se 3 (by rfl) ⟨436226, by rfl⟩ : syracuseStep 2326541 = 872453) (by norm_num)
theorem B6204109 : Blo 2177435 6204109 := bstep (se 3 (by rfl) ⟨1163270, by rfl⟩ : syracuseStep 6204109 = 2326541) B2326541
theorem B8272145 : Blo 2177435 8272145 := bstep (se 2 (by rfl) ⟨3102054, by rfl⟩ : syracuseStep 8272145 = 6204109) B6204109
theorem B5514763 : Blo 2177435 5514763 := bstep (se 1 (by rfl) ⟨4136072, by rfl⟩ : syracuseStep 5514763 = 8272145) B8272145
theorem B7353017 : Blo 2177435 7353017 := bstep (se 2 (by rfl) ⟨2757381, by rfl⟩ : syracuseStep 7353017 = 5514763) B5514763
theorem B4902011 : Blo 2177435 4902011 := bstep (se 1 (by rfl) ⟨3676508, by rfl⟩ : syracuseStep 4902011 = 7353017) B7353017
theorem B3268007 : Blo 2177435 3268007 := bstep (se 1 (by rfl) ⟨2451005, by rfl⟩ : syracuseStep 3268007 = 4902011) B4902011
theorem B2178671 : Blo 2177435 2178671 := bstep (se 1 (by rfl) ⟨1634003, by rfl⟩ : syracuseStep 2178671 = 3268007) B3268007
theorem B3268013 : Blo 2177435 3268013 := bbase (se 3 (by rfl) ⟨612752, by rfl⟩ : syracuseStep 3268013 = 1225505) (by norm_num)
theorem B2178675 : Blo 2177435 2178675 := bstep (se 1 (by rfl) ⟨1634006, by rfl⟩ : syracuseStep 2178675 = 3268013) B3268013
theorem B4902029 : Blo 2177435 4902029 := bbase (se 3 (by rfl) ⟨919130, by rfl⟩ : syracuseStep 4902029 = 1838261) (by norm_num)
theorem B3268019 : Blo 2177435 3268019 := bstep (se 1 (by rfl) ⟨2451014, by rfl⟩ : syracuseStep 3268019 = 4902029) B4902029
theorem B2178679 : Blo 2177435 2178679 := bstep (se 1 (by rfl) ⟨1634009, by rfl⟩ : syracuseStep 2178679 = 3268019) B3268019
theorem B2757397 : Blo 2177435 2757397 := bbase (se 6 (by rfl) ⟨64626, by rfl⟩ : syracuseStep 2757397 = 129253) (by norm_num)
theorem B3676529 : Blo 2177435 3676529 := bstep (se 2 (by rfl) ⟨1378698, by rfl⟩ : syracuseStep 3676529 = 2757397) B2757397
theorem B2451019 : Blo 2177435 2451019 := bstep (se 1 (by rfl) ⟨1838264, by rfl⟩ : syracuseStep 2451019 = 3676529) B3676529
theorem B3268025 : Blo 2177435 3268025 := bstep (se 2 (by rfl) ⟨1225509, by rfl⟩ : syracuseStep 3268025 = 2451019) B2451019
theorem B2178683 : Blo 2177435 2178683 := bstep (se 1 (by rfl) ⟨1634012, by rfl⟩ : syracuseStep 2178683 = 3268025) B3268025
theorem B6133445 : Blo 2177435 6133445 := bbase (se 4 (by rfl) ⟨575010, by rfl⟩ : syracuseStep 6133445 = 1150021) (by norm_num)
theorem B4088963 : Blo 2177435 4088963 := bstep (se 1 (by rfl) ⟨3066722, by rfl⟩ : syracuseStep 4088963 = 6133445) B6133445
theorem B10903901 : Blo 2177435 10903901 := bstep (se 3 (by rfl) ⟨2044481, by rfl⟩ : syracuseStep 10903901 = 4088963) B4088963
theorem B29077069 : Blo 2177435 29077069 := bstep (se 3 (by rfl) ⟨5451950, by rfl⟩ : syracuseStep 29077069 = 10903901) B10903901
theorem B38769425 : Blo 2177435 38769425 := bstep (se 2 (by rfl) ⟨14538534, by rfl⟩ : syracuseStep 38769425 = 29077069) B29077069
theorem B25846283 : Blo 2177435 25846283 := bstep (se 1 (by rfl) ⟨19384712, by rfl⟩ : syracuseStep 25846283 = 38769425) B38769425
theorem B17230855 : Blo 2177435 17230855 := bstep (se 1 (by rfl) ⟨12923141, by rfl⟩ : syracuseStep 17230855 = 25846283) B25846283
theorem B22974473 : Blo 2177435 22974473 := bstep (se 2 (by rfl) ⟨8615427, by rfl⟩ : syracuseStep 22974473 = 17230855) B17230855
theorem B61265261 : Blo 2177435 61265261 := bstep (se 3 (by rfl) ⟨11487236, by rfl⟩ : syracuseStep 61265261 = 22974473) B22974473
theorem B40843507 : Blo 2177435 40843507 := bstep (se 1 (by rfl) ⟨30632630, by rfl⟩ : syracuseStep 40843507 = 61265261) B61265261
theorem B54458009 : Blo 2177435 54458009 := bstep (se 2 (by rfl) ⟨20421753, by rfl⟩ : syracuseStep 54458009 = 40843507) B40843507
theorem B36305339 : Blo 2177435 36305339 := bstep (se 1 (by rfl) ⟨27229004, by rfl⟩ : syracuseStep 36305339 = 54458009) B54458009
theorem B96814237 : Blo 2177435 96814237 := bstep (se 3 (by rfl) ⟨18152669, by rfl⟩ : syracuseStep 96814237 = 36305339) B36305339
theorem B129085649 : Blo 2177435 129085649 := bstep (se 2 (by rfl) ⟨48407118, by rfl⟩ : syracuseStep 129085649 = 96814237) B96814237
theorem B86057099 : Blo 2177435 86057099 := bstep (se 1 (by rfl) ⟨64542824, by rfl⟩ : syracuseStep 86057099 = 129085649) B129085649
theorem B57371399 : Blo 2177435 57371399 := bstep (se 1 (by rfl) ⟨43028549, by rfl⟩ : syracuseStep 57371399 = 86057099) B86057099
theorem B38247599 : Blo 2177435 38247599 := bstep (se 1 (by rfl) ⟨28685699, by rfl⟩ : syracuseStep 38247599 = 57371399) B57371399
theorem B101993597 : Blo 2177435 101993597 := bstep (se 3 (by rfl) ⟨19123799, by rfl⟩ : syracuseStep 101993597 = 38247599) B38247599
theorem B67995731 : Blo 2177435 67995731 := bstep (se 1 (by rfl) ⟨50996798, by rfl⟩ : syracuseStep 67995731 = 101993597) B101993597
theorem B181321949 : Blo 2177435 181321949 := bstep (se 3 (by rfl) ⟨33997865, by rfl⟩ : syracuseStep 181321949 = 67995731) B67995731
theorem B483525197 : Blo 2177435 483525197 := bstep (se 3 (by rfl) ⟨90660974, by rfl⟩ : syracuseStep 483525197 = 181321949) B181321949
theorem B322350131 : Blo 2177435 322350131 := bstep (se 1 (by rfl) ⟨241762598, by rfl⟩ : syracuseStep 322350131 = 483525197) B483525197
theorem B214900087 : Blo 2177435 214900087 := bstep (se 1 (by rfl) ⟨161175065, by rfl⟩ : syracuseStep 214900087 = 322350131) B322350131
theorem B286533449 : Blo 2177435 286533449 := bstep (se 2 (by rfl) ⟨107450043, by rfl⟩ : syracuseStep 286533449 = 214900087) B214900087
theorem B191022299 : Blo 2177435 191022299 := bstep (se 1 (by rfl) ⟨143266724, by rfl⟩ : syracuseStep 191022299 = 286533449) B286533449
theorem B127348199 : Blo 2177435 127348199 := bstep (se 1 (by rfl) ⟨95511149, by rfl⟩ : syracuseStep 127348199 = 191022299) B191022299
theorem B84898799 : Blo 2177435 84898799 := bstep (se 1 (by rfl) ⟨63674099, by rfl⟩ : syracuseStep 84898799 = 127348199) B127348199
theorem B56599199 : Blo 2177435 56599199 := bstep (se 1 (by rfl) ⟨42449399, by rfl⟩ : syracuseStep 56599199 = 84898799) B84898799
theorem B37732799 : Blo 2177435 37732799 := bstep (se 1 (by rfl) ⟨28299599, by rfl⟩ : syracuseStep 37732799 = 56599199) B56599199
theorem B25155199 : Blo 2177435 25155199 := bstep (se 1 (by rfl) ⟨18866399, by rfl⟩ : syracuseStep 25155199 = 37732799) B37732799
theorem B33540265 : Blo 2177435 33540265 := bstep (se 2 (by rfl) ⟨12577599, by rfl⟩ : syracuseStep 33540265 = 25155199) B25155199
theorem B44720353 : Blo 2177435 44720353 := bstep (se 2 (by rfl) ⟨16770132, by rfl⟩ : syracuseStep 44720353 = 33540265) B33540265
theorem B238508549 : Blo 2177435 238508549 := bstep (se 4 (by rfl) ⟨22360176, by rfl⟩ : syracuseStep 238508549 = 44720353) B44720353
theorem B159005699 : Blo 2177435 159005699 := bstep (se 1 (by rfl) ⟨119254274, by rfl⟩ : syracuseStep 159005699 = 238508549) B238508549
theorem B106003799 : Blo 2177435 106003799 := bstep (se 1 (by rfl) ⟨79502849, by rfl⟩ : syracuseStep 106003799 = 159005699) B159005699
theorem B70669199 : Blo 2177435 70669199 := bstep (se 1 (by rfl) ⟨53001899, by rfl⟩ : syracuseStep 70669199 = 106003799) B106003799
theorem B47112799 : Blo 2177435 47112799 := bstep (se 1 (by rfl) ⟨35334599, by rfl⟩ : syracuseStep 47112799 = 70669199) B70669199
theorem B62817065 : Blo 2177435 62817065 := bstep (se 2 (by rfl) ⟨23556399, by rfl⟩ : syracuseStep 62817065 = 47112799) B47112799
theorem B41878043 : Blo 2177435 41878043 := bstep (se 1 (by rfl) ⟨31408532, by rfl⟩ : syracuseStep 41878043 = 62817065) B62817065
theorem B27918695 : Blo 2177435 27918695 := bstep (se 1 (by rfl) ⟨20939021, by rfl⟩ : syracuseStep 27918695 = 41878043) B41878043
theorem B18612463 : Blo 2177435 18612463 := bstep (se 1 (by rfl) ⟨13959347, by rfl⟩ : syracuseStep 18612463 = 27918695) B27918695
theorem B24816617 : Blo 2177435 24816617 := bstep (se 2 (by rfl) ⟨9306231, by rfl⟩ : syracuseStep 24816617 = 18612463) B18612463
theorem B16544411 : Blo 2177435 16544411 := bstep (se 1 (by rfl) ⟨12408308, by rfl⟩ : syracuseStep 16544411 = 24816617) B24816617
theorem B11029607 : Blo 2177435 11029607 := bstep (se 1 (by rfl) ⟨8272205, by rfl⟩ : syracuseStep 11029607 = 16544411) B16544411
theorem B7353071 : Blo 2177435 7353071 := bstep (se 1 (by rfl) ⟨5514803, by rfl⟩ : syracuseStep 7353071 = 11029607) B11029607
theorem B4902047 : Blo 2177435 4902047 := bstep (se 1 (by rfl) ⟨3676535, by rfl⟩ : syracuseStep 4902047 = 7353071) B7353071
theorem B3268031 : Blo 2177435 3268031 := bstep (se 1 (by rfl) ⟨2451023, by rfl⟩ : syracuseStep 3268031 = 4902047) B4902047
theorem B2178687 : Blo 2177435 2178687 := bstep (se 1 (by rfl) ⟨1634015, by rfl⟩ : syracuseStep 2178687 = 3268031) B3268031
theorem B3268037 : Blo 2177435 3268037 := bbase (se 4 (by rfl) ⟨306378, by rfl⟩ : syracuseStep 3268037 = 612757) (by norm_num)
theorem B2178691 : Blo 2177435 2178691 := bstep (se 1 (by rfl) ⟨1634018, by rfl⟩ : syracuseStep 2178691 = 3268037) B3268037
theorem B3676549 : Blo 2177435 3676549 := bbase (se 4 (by rfl) ⟨344676, by rfl⟩ : syracuseStep 3676549 = 689353) (by norm_num)
theorem B4902065 : Blo 2177435 4902065 := bstep (se 2 (by rfl) ⟨1838274, by rfl⟩ : syracuseStep 4902065 = 3676549) B3676549
theorem B3268043 : Blo 2177435 3268043 := bstep (se 1 (by rfl) ⟨2451032, by rfl⟩ : syracuseStep 3268043 = 4902065) B4902065
theorem B2178695 : Blo 2177435 2178695 := bstep (se 1 (by rfl) ⟨1634021, by rfl⟩ : syracuseStep 2178695 = 3268043) B3268043
theorem B2451037 : Blo 2177435 2451037 := bbase (se 3 (by rfl) ⟨459569, by rfl⟩ : syracuseStep 2451037 = 919139) (by norm_num)
theorem B3268049 : Blo 2177435 3268049 := bstep (se 2 (by rfl) ⟨1225518, by rfl⟩ : syracuseStep 3268049 = 2451037) B2451037
theorem B2178699 : Blo 2177435 2178699 := bstep (se 1 (by rfl) ⟨1634024, by rfl⟩ : syracuseStep 2178699 = 3268049) B3268049
theorem B7353125 : Blo 2177435 7353125 := bbase (se 4 (by rfl) ⟨689355, by rfl⟩ : syracuseStep 7353125 = 1378711) (by norm_num)
theorem B4902083 : Blo 2177435 4902083 := bstep (se 1 (by rfl) ⟨3676562, by rfl⟩ : syracuseStep 4902083 = 7353125) B7353125
theorem B3268055 : Blo 2177435 3268055 := bstep (se 1 (by rfl) ⟨2451041, by rfl⟩ : syracuseStep 3268055 = 4902083) B4902083
theorem B2178703 : Blo 2177435 2178703 := bstep (se 1 (by rfl) ⟨1634027, by rfl⟩ : syracuseStep 2178703 = 3268055) B3268055
theorem B3268061 : Blo 2177435 3268061 := bbase (se 3 (by rfl) ⟨612761, by rfl⟩ : syracuseStep 3268061 = 1225523) (by norm_num)
theorem B2178707 : Blo 2177435 2178707 := bstep (se 1 (by rfl) ⟨1634030, by rfl⟩ : syracuseStep 2178707 = 3268061) B3268061
theorem B4902101 : Blo 2177435 4902101 := bbase (se 7 (by rfl) ⟨57446, by rfl⟩ : syracuseStep 4902101 = 114893) (by norm_num)
theorem B3268067 : Blo 2177435 3268067 := bstep (se 1 (by rfl) ⟨2451050, by rfl⟩ : syracuseStep 3268067 = 4902101) B4902101
theorem B2178711 : Blo 2177435 2178711 := bstep (se 1 (by rfl) ⟨1634033, by rfl⟩ : syracuseStep 2178711 = 3268067) B3268067
theorem B6979765 : Blo 2177435 6979765 := bbase (se 5 (by rfl) ⟨327176, by rfl⟩ : syracuseStep 6979765 = 654353) (by norm_num)
theorem B9306353 : Blo 2177435 9306353 := bstep (se 2 (by rfl) ⟨3489882, by rfl⟩ : syracuseStep 9306353 = 6979765) B6979765
theorem B6204235 : Blo 2177435 6204235 := bstep (se 1 (by rfl) ⟨4653176, by rfl⟩ : syracuseStep 6204235 = 9306353) B9306353
theorem B8272313 : Blo 2177435 8272313 := bstep (se 2 (by rfl) ⟨3102117, by rfl⟩ : syracuseStep 8272313 = 6204235) B6204235
theorem B5514875 : Blo 2177435 5514875 := bstep (se 1 (by rfl) ⟨4136156, by rfl⟩ : syracuseStep 5514875 = 8272313) B8272313
theorem B3676583 : Blo 2177435 3676583 := bstep (se 1 (by rfl) ⟨2757437, by rfl⟩ : syracuseStep 3676583 = 5514875) B5514875
theorem B2451055 : Blo 2177435 2451055 := bstep (se 1 (by rfl) ⟨1838291, by rfl⟩ : syracuseStep 2451055 = 3676583) B3676583
theorem B3268073 : Blo 2177435 3268073 := bstep (se 2 (by rfl) ⟨1225527, by rfl⟩ : syracuseStep 3268073 = 2451055) B2451055
theorem B2178715 : Blo 2177435 2178715 := bstep (se 1 (by rfl) ⟨1634036, by rfl⟩ : syracuseStep 2178715 = 3268073) B3268073
theorem B8833781 : Blo 2177435 8833781 := bbase (se 5 (by rfl) ⟨414083, by rfl⟩ : syracuseStep 8833781 = 828167) (by norm_num)
theorem B5889187 : Blo 2177435 5889187 := bstep (se 1 (by rfl) ⟨4416890, by rfl⟩ : syracuseStep 5889187 = 8833781) B8833781
theorem B7852249 : Blo 2177435 7852249 := bstep (se 2 (by rfl) ⟨2944593, by rfl⟩ : syracuseStep 7852249 = 5889187) B5889187
theorem B10469665 : Blo 2177435 10469665 := bstep (se 2 (by rfl) ⟨3926124, by rfl⟩ : syracuseStep 10469665 = 7852249) B7852249
theorem B13959553 : Blo 2177435 13959553 := bstep (se 2 (by rfl) ⟨5234832, by rfl⟩ : syracuseStep 13959553 = 10469665) B10469665
theorem B18612737 : Blo 2177435 18612737 := bstep (se 2 (by rfl) ⟨6979776, by rfl⟩ : syracuseStep 18612737 = 13959553) B13959553
theorem B12408491 : Blo 2177435 12408491 := bstep (se 1 (by rfl) ⟨9306368, by rfl⟩ : syracuseStep 12408491 = 18612737) B18612737
theorem B8272327 : Blo 2177435 8272327 := bstep (se 1 (by rfl) ⟨6204245, by rfl⟩ : syracuseStep 8272327 = 12408491) B12408491
theorem B11029769 : Blo 2177435 11029769 := bstep (se 2 (by rfl) ⟨4136163, by rfl⟩ : syracuseStep 11029769 = 8272327) B8272327
theorem B7353179 : Blo 2177435 7353179 := bstep (se 1 (by rfl) ⟨5514884, by rfl⟩ : syracuseStep 7353179 = 11029769) B11029769
theorem B4902119 : Blo 2177435 4902119 := bstep (se 1 (by rfl) ⟨3676589, by rfl⟩ : syracuseStep 4902119 = 7353179) B7353179
theorem B3268079 : Blo 2177435 3268079 := bstep (se 1 (by rfl) ⟨2451059, by rfl⟩ : syracuseStep 3268079 = 4902119) B4902119
theorem B2178719 : Blo 2177435 2178719 := bstep (se 1 (by rfl) ⟨1634039, by rfl⟩ : syracuseStep 2178719 = 3268079) B3268079
theorem B3268085 : Blo 2177435 3268085 := bbase (se 5 (by rfl) ⟨153191, by rfl⟩ : syracuseStep 3268085 = 306383) (by norm_num)
theorem B2178723 : Blo 2177435 2178723 := bstep (se 1 (by rfl) ⟨1634042, by rfl⟩ : syracuseStep 2178723 = 3268085) B3268085
theorem B2326601 : Blo 2177435 2326601 := bbase (se 2 (by rfl) ⟨872475, by rfl⟩ : syracuseStep 2326601 = 1744951) (by norm_num)
theorem B6204269 : Blo 2177435 6204269 := bstep (se 3 (by rfl) ⟨1163300, by rfl⟩ : syracuseStep 6204269 = 2326601) B2326601
theorem B4136179 : Blo 2177435 4136179 := bstep (se 1 (by rfl) ⟨3102134, by rfl⟩ : syracuseStep 4136179 = 6204269) B6204269
theorem B5514905 : Blo 2177435 5514905 := bstep (se 2 (by rfl) ⟨2068089, by rfl⟩ : syracuseStep 5514905 = 4136179) B4136179
theorem B3676603 : Blo 2177435 3676603 := bstep (se 1 (by rfl) ⟨2757452, by rfl⟩ : syracuseStep 3676603 = 5514905) B5514905
theorem B4902137 : Blo 2177435 4902137 := bstep (se 2 (by rfl) ⟨1838301, by rfl⟩ : syracuseStep 4902137 = 3676603) B3676603
theorem B3268091 : Blo 2177435 3268091 := bstep (se 1 (by rfl) ⟨2451068, by rfl⟩ : syracuseStep 3268091 = 4902137) B4902137
theorem B2178727 : Blo 2177435 2178727 := bstep (se 1 (by rfl) ⟨1634045, by rfl⟩ : syracuseStep 2178727 = 3268091) B3268091
theorem B2451073 : Blo 2177435 2451073 := bbase (se 2 (by rfl) ⟨919152, by rfl⟩ : syracuseStep 2451073 = 1838305) (by norm_num)
theorem B3268097 : Blo 2177435 3268097 := bstep (se 2 (by rfl) ⟨1225536, by rfl⟩ : syracuseStep 3268097 = 2451073) B2451073
theorem B2178731 : Blo 2177435 2178731 := bstep (se 1 (by rfl) ⟨1634048, by rfl⟩ : syracuseStep 2178731 = 3268097) B3268097
theorem B5514925 : Blo 2177435 5514925 := bbase (se 3 (by rfl) ⟨1034048, by rfl⟩ : syracuseStep 5514925 = 2068097) (by norm_num)
theorem B7353233 : Blo 2177435 7353233 := bstep (se 2 (by rfl) ⟨2757462, by rfl⟩ : syracuseStep 7353233 = 5514925) B5514925
theorem B4902155 : Blo 2177435 4902155 := bstep (se 1 (by rfl) ⟨3676616, by rfl⟩ : syracuseStep 4902155 = 7353233) B7353233
theorem B3268103 : Blo 2177435 3268103 := bstep (se 1 (by rfl) ⟨2451077, by rfl⟩ : syracuseStep 3268103 = 4902155) B4902155
theorem B2178735 : Blo 2177435 2178735 := bstep (se 1 (by rfl) ⟨1634051, by rfl⟩ : syracuseStep 2178735 = 3268103) B3268103
theorem B3268109 : Blo 2177435 3268109 := bbase (se 3 (by rfl) ⟨612770, by rfl⟩ : syracuseStep 3268109 = 1225541) (by norm_num)
theorem B2178739 : Blo 2177435 2178739 := bstep (se 1 (by rfl) ⟨1634054, by rfl⟩ : syracuseStep 2178739 = 3268109) B3268109
theorem B4902173 : Blo 2177435 4902173 := bbase (se 3 (by rfl) ⟨919157, by rfl⟩ : syracuseStep 4902173 = 1838315) (by norm_num)
theorem B3268115 : Blo 2177435 3268115 := bstep (se 1 (by rfl) ⟨2451086, by rfl⟩ : syracuseStep 3268115 = 4902173) B4902173
theorem B2178743 : Blo 2177435 2178743 := bstep (se 1 (by rfl) ⟨1634057, by rfl⟩ : syracuseStep 2178743 = 3268115) B3268115
theorem B3676637 : Blo 2177435 3676637 := bbase (se 3 (by rfl) ⟨689369, by rfl⟩ : syracuseStep 3676637 = 1378739) (by norm_num)
theorem B2451091 : Blo 2177435 2451091 := bstep (se 1 (by rfl) ⟨1838318, by rfl⟩ : syracuseStep 2451091 = 3676637) B3676637
theorem B3268121 : Blo 2177435 3268121 := bstep (se 2 (by rfl) ⟨1225545, by rfl⟩ : syracuseStep 3268121 = 2451091) B2451091
theorem B2178747 : Blo 2177435 2178747 := bstep (se 1 (by rfl) ⟨1634060, by rfl⟩ : syracuseStep 2178747 = 3268121) B3268121
theorem B2795105 : Blo 2177435 2795105 := bbase (se 2 (by rfl) ⟨1048164, by rfl⟩ : syracuseStep 2795105 = 2096329) (by norm_num)
theorem B7453613 : Blo 2177435 7453613 := bstep (se 3 (by rfl) ⟨1397552, by rfl⟩ : syracuseStep 7453613 = 2795105) B2795105
theorem B4969075 : Blo 2177435 4969075 := bstep (se 1 (by rfl) ⟨3726806, by rfl⟩ : syracuseStep 4969075 = 7453613) B7453613
theorem B6625433 : Blo 2177435 6625433 := bstep (se 2 (by rfl) ⟨2484537, by rfl⟩ : syracuseStep 6625433 = 4969075) B4969075
theorem B17667821 : Blo 2177435 17667821 := bstep (se 3 (by rfl) ⟨3312716, by rfl⟩ : syracuseStep 17667821 = 6625433) B6625433
theorem B11778547 : Blo 2177435 11778547 := bstep (se 1 (by rfl) ⟨8833910, by rfl⟩ : syracuseStep 11778547 = 17667821) B17667821
theorem B15704729 : Blo 2177435 15704729 := bstep (se 2 (by rfl) ⟨5889273, by rfl⟩ : syracuseStep 15704729 = 11778547) B11778547
theorem B10469819 : Blo 2177435 10469819 := bstep (se 1 (by rfl) ⟨7852364, by rfl⟩ : syracuseStep 10469819 = 15704729) B15704729
theorem B6979879 : Blo 2177435 6979879 := bstep (se 1 (by rfl) ⟨5234909, by rfl⟩ : syracuseStep 6979879 = 10469819) B10469819
theorem B9306505 : Blo 2177435 9306505 := bstep (se 2 (by rfl) ⟨3489939, by rfl⟩ : syracuseStep 9306505 = 6979879) B6979879
theorem B12408673 : Blo 2177435 12408673 := bstep (se 2 (by rfl) ⟨4653252, by rfl⟩ : syracuseStep 12408673 = 9306505) B9306505
theorem B16544897 : Blo 2177435 16544897 := bstep (se 2 (by rfl) ⟨6204336, by rfl⟩ : syracuseStep 16544897 = 12408673) B12408673
theorem B11029931 : Blo 2177435 11029931 := bstep (se 1 (by rfl) ⟨8272448, by rfl⟩ : syracuseStep 11029931 = 16544897) B16544897
theorem B7353287 : Blo 2177435 7353287 := bstep (se 1 (by rfl) ⟨5514965, by rfl⟩ : syracuseStep 7353287 = 11029931) B11029931
theorem B4902191 : Blo 2177435 4902191 := bstep (se 1 (by rfl) ⟨3676643, by rfl⟩ : syracuseStep 4902191 = 7353287) B7353287
theorem B3268127 : Blo 2177435 3268127 := bstep (se 1 (by rfl) ⟨2451095, by rfl⟩ : syracuseStep 3268127 = 4902191) B4902191
theorem B2178751 : Blo 2177435 2178751 := bstep (se 1 (by rfl) ⟨1634063, by rfl⟩ : syracuseStep 2178751 = 3268127) B3268127
theorem B3268133 : Blo 2177435 3268133 := bbase (se 4 (by rfl) ⟨306387, by rfl⟩ : syracuseStep 3268133 = 612775) (by norm_num)
theorem B2178755 : Blo 2177435 2178755 := bstep (se 1 (by rfl) ⟨1634066, by rfl⟩ : syracuseStep 2178755 = 3268133) B3268133
theorem B2757493 : Blo 2177435 2757493 := bbase (se 5 (by rfl) ⟨129257, by rfl⟩ : syracuseStep 2757493 = 258515) (by norm_num)
theorem B3676657 : Blo 2177435 3676657 := bstep (se 2 (by rfl) ⟨1378746, by rfl⟩ : syracuseStep 3676657 = 2757493) B2757493
theorem B4902209 : Blo 2177435 4902209 := bstep (se 2 (by rfl) ⟨1838328, by rfl⟩ : syracuseStep 4902209 = 3676657) B3676657
theorem B3268139 : Blo 2177435 3268139 := bstep (se 1 (by rfl) ⟨2451104, by rfl⟩ : syracuseStep 3268139 = 4902209) B4902209
theorem B2178759 : Blo 2177435 2178759 := bstep (se 1 (by rfl) ⟨1634069, by rfl⟩ : syracuseStep 2178759 = 3268139) B3268139
theorem B2451109 : Blo 2177435 2451109 := bbase (se 4 (by rfl) ⟨229791, by rfl⟩ : syracuseStep 2451109 = 459583) (by norm_num)
theorem B3268145 : Blo 2177435 3268145 := bstep (se 2 (by rfl) ⟨1225554, by rfl⟩ : syracuseStep 3268145 = 2451109) B2451109
theorem B2178763 : Blo 2177435 2178763 := bstep (se 1 (by rfl) ⟨1634072, by rfl⟩ : syracuseStep 2178763 = 3268145) B3268145
theorem B13250965 : Blo 2177435 13250965 := bbase (se 6 (by rfl) ⟨310569, by rfl⟩ : syracuseStep 13250965 = 621139) (by norm_num)
theorem B17667953 : Blo 2177435 17667953 := bstep (se 2 (by rfl) ⟨6625482, by rfl⟩ : syracuseStep 17667953 = 13250965) B13250965
theorem B11778635 : Blo 2177435 11778635 := bstep (se 1 (by rfl) ⟨8833976, by rfl⟩ : syracuseStep 11778635 = 17667953) B17667953
theorem B31409693 : Blo 2177435 31409693 := bstep (se 3 (by rfl) ⟨5889317, by rfl⟩ : syracuseStep 31409693 = 11778635) B11778635
theorem B20939795 : Blo 2177435 20939795 := bstep (se 1 (by rfl) ⟨15704846, by rfl⟩ : syracuseStep 20939795 = 31409693) B31409693
theorem B13959863 : Blo 2177435 13959863 := bstep (se 1 (by rfl) ⟨10469897, by rfl⟩ : syracuseStep 13959863 = 20939795) B20939795
theorem B9306575 : Blo 2177435 9306575 := bstep (se 1 (by rfl) ⟨6979931, by rfl⟩ : syracuseStep 9306575 = 13959863) B13959863
theorem B6204383 : Blo 2177435 6204383 := bstep (se 1 (by rfl) ⟨4653287, by rfl⟩ : syracuseStep 6204383 = 9306575) B9306575
theorem B4136255 : Blo 2177435 4136255 := bstep (se 1 (by rfl) ⟨3102191, by rfl⟩ : syracuseStep 4136255 = 6204383) B6204383
theorem B2757503 : Blo 2177435 2757503 := bstep (se 1 (by rfl) ⟨2068127, by rfl⟩ : syracuseStep 2757503 = 4136255) B4136255
theorem B7353341 : Blo 2177435 7353341 := bstep (se 3 (by rfl) ⟨1378751, by rfl⟩ : syracuseStep 7353341 = 2757503) B2757503
theorem B4902227 : Blo 2177435 4902227 := bstep (se 1 (by rfl) ⟨3676670, by rfl⟩ : syracuseStep 4902227 = 7353341) B7353341
theorem B3268151 : Blo 2177435 3268151 := bstep (se 1 (by rfl) ⟨2451113, by rfl⟩ : syracuseStep 3268151 = 4902227) B4902227
theorem B2178767 : Blo 2177435 2178767 := bstep (se 1 (by rfl) ⟨1634075, by rfl⟩ : syracuseStep 2178767 = 3268151) B3268151
theorem B3268157 : Blo 2177435 3268157 := bbase (se 3 (by rfl) ⟨612779, by rfl⟩ : syracuseStep 3268157 = 1225559) (by norm_num)
theorem B2178771 : Blo 2177435 2178771 := bstep (se 1 (by rfl) ⟨1634078, by rfl⟩ : syracuseStep 2178771 = 3268157) B3268157
theorem B4902245 : Blo 2177435 4902245 := bbase (se 4 (by rfl) ⟨459585, by rfl⟩ : syracuseStep 4902245 = 919171) (by norm_num)
theorem B3268163 : Blo 2177435 3268163 := bstep (se 1 (by rfl) ⟨2451122, by rfl⟩ : syracuseStep 3268163 = 4902245) B4902245
theorem B2178775 : Blo 2177435 2178775 := bstep (se 1 (by rfl) ⟨1634081, by rfl⟩ : syracuseStep 2178775 = 3268163) B3268163
theorem B5515037 : Blo 2177435 5515037 := bbase (se 3 (by rfl) ⟨1034069, by rfl⟩ : syracuseStep 5515037 = 2068139) (by norm_num)
theorem B3676691 : Blo 2177435 3676691 := bstep (se 1 (by rfl) ⟨2757518, by rfl⟩ : syracuseStep 3676691 = 5515037) B5515037
theorem B2451127 : Blo 2177435 2451127 := bstep (se 1 (by rfl) ⟨1838345, by rfl⟩ : syracuseStep 2451127 = 3676691) B3676691
theorem B3268169 : Blo 2177435 3268169 := bstep (se 2 (by rfl) ⟨1225563, by rfl⟩ : syracuseStep 3268169 = 2451127) B2451127
theorem B2178779 : Blo 2177435 2178779 := bstep (se 1 (by rfl) ⟨1634084, by rfl⟩ : syracuseStep 2178779 = 3268169) B3268169
theorem B4136285 : Blo 2177435 4136285 := bbase (se 3 (by rfl) ⟨775553, by rfl⟩ : syracuseStep 4136285 = 1551107) (by norm_num)
theorem B11030093 : Blo 2177435 11030093 := bstep (se 3 (by rfl) ⟨2068142, by rfl⟩ : syracuseStep 11030093 = 4136285) B4136285
theorem B7353395 : Blo 2177435 7353395 := bstep (se 1 (by rfl) ⟨5515046, by rfl⟩ : syracuseStep 7353395 = 11030093) B11030093
theorem B4902263 : Blo 2177435 4902263 := bstep (se 1 (by rfl) ⟨3676697, by rfl⟩ : syracuseStep 4902263 = 7353395) B7353395
theorem B3268175 : Blo 2177435 3268175 := bstep (se 1 (by rfl) ⟨2451131, by rfl⟩ : syracuseStep 3268175 = 4902263) B4902263
theorem B2178783 : Blo 2177435 2178783 := bstep (se 1 (by rfl) ⟨1634087, by rfl⟩ : syracuseStep 2178783 = 3268175) B3268175
theorem B3268181 : Blo 2177435 3268181 := bbase (se 8 (by rfl) ⟨19149, by rfl⟩ : syracuseStep 3268181 = 38299) (by norm_num)
theorem B2178787 : Blo 2177435 2178787 := bstep (se 1 (by rfl) ⟨1634090, by rfl⟩ : syracuseStep 2178787 = 3268181) B3268181
theorem B9306677 : Blo 2177435 9306677 := bbase (se 5 (by rfl) ⟨436250, by rfl⟩ : syracuseStep 9306677 = 872501) (by norm_num)
theorem B6204451 : Blo 2177435 6204451 := bstep (se 1 (by rfl) ⟨4653338, by rfl⟩ : syracuseStep 6204451 = 9306677) B9306677
theorem B8272601 : Blo 2177435 8272601 := bstep (se 2 (by rfl) ⟨3102225, by rfl⟩ : syracuseStep 8272601 = 6204451) B6204451
theorem B5515067 : Blo 2177435 5515067 := bstep (se 1 (by rfl) ⟨4136300, by rfl⟩ : syracuseStep 5515067 = 8272601) B8272601
theorem B3676711 : Blo 2177435 3676711 := bstep (se 1 (by rfl) ⟨2757533, by rfl⟩ : syracuseStep 3676711 = 5515067) B5515067
theorem B4902281 : Blo 2177435 4902281 := bstep (se 2 (by rfl) ⟨1838355, by rfl⟩ : syracuseStep 4902281 = 3676711) B3676711
theorem B3268187 : Blo 2177435 3268187 := bstep (se 1 (by rfl) ⟨2451140, by rfl⟩ : syracuseStep 3268187 = 4902281) B4902281
theorem B2178791 : Blo 2177435 2178791 := bstep (se 1 (by rfl) ⟨1634093, by rfl⟩ : syracuseStep 2178791 = 3268187) B3268187
theorem B2451145 : Blo 2177435 2451145 := bbase (se 2 (by rfl) ⟨919179, by rfl⟩ : syracuseStep 2451145 = 1838359) (by norm_num)
theorem B3268193 : Blo 2177435 3268193 := bstep (se 2 (by rfl) ⟨1225572, by rfl⟩ : syracuseStep 3268193 = 2451145) B2451145
theorem B2178795 : Blo 2177435 2178795 := bstep (se 1 (by rfl) ⟨1634096, by rfl⟩ : syracuseStep 2178795 = 3268193) B3268193
theorem B3926269 : Blo 2177435 3926269 := bbase (se 3 (by rfl) ⟨736175, by rfl⟩ : syracuseStep 3926269 = 1472351) (by norm_num)
theorem B5235025 : Blo 2177435 5235025 := bstep (se 2 (by rfl) ⟨1963134, by rfl⟩ : syracuseStep 5235025 = 3926269) B3926269
theorem B6980033 : Blo 2177435 6980033 := bstep (se 2 (by rfl) ⟨2617512, by rfl⟩ : syracuseStep 6980033 = 5235025) B5235025
theorem B18613421 : Blo 2177435 18613421 := bstep (se 3 (by rfl) ⟨3490016, by rfl⟩ : syracuseStep 18613421 = 6980033) B6980033
theorem B12408947 : Blo 2177435 12408947 := bstep (se 1 (by rfl) ⟨9306710, by rfl⟩ : syracuseStep 12408947 = 18613421) B18613421
theorem B8272631 : Blo 2177435 8272631 := bstep (se 1 (by rfl) ⟨6204473, by rfl⟩ : syracuseStep 8272631 = 12408947) B12408947
theorem B5515087 : Blo 2177435 5515087 := bstep (se 1 (by rfl) ⟨4136315, by rfl⟩ : syracuseStep 5515087 = 8272631) B8272631
theorem B7353449 : Blo 2177435 7353449 := bstep (se 2 (by rfl) ⟨2757543, by rfl⟩ : syracuseStep 7353449 = 5515087) B5515087
theorem B4902299 : Blo 2177435 4902299 := bstep (se 1 (by rfl) ⟨3676724, by rfl⟩ : syracuseStep 4902299 = 7353449) B7353449
theorem B3268199 : Blo 2177435 3268199 := bstep (se 1 (by rfl) ⟨2451149, by rfl⟩ : syracuseStep 3268199 = 4902299) B4902299
theorem B2178799 : Blo 2177435 2178799 := bstep (se 1 (by rfl) ⟨1634099, by rfl⟩ : syracuseStep 2178799 = 3268199) B3268199
theorem B3268205 : Blo 2177435 3268205 := bbase (se 3 (by rfl) ⟨612788, by rfl⟩ : syracuseStep 3268205 = 1225577) (by norm_num)
theorem B2178803 : Blo 2177435 2178803 := bstep (se 1 (by rfl) ⟨1634102, by rfl⟩ : syracuseStep 2178803 = 3268205) B3268205
theorem B4902317 : Blo 2177435 4902317 := bbase (se 3 (by rfl) ⟨919184, by rfl⟩ : syracuseStep 4902317 = 1838369) (by norm_num)
theorem B3268211 : Blo 2177435 3268211 := bstep (se 1 (by rfl) ⟨2451158, by rfl⟩ : syracuseStep 3268211 = 4902317) B4902317
theorem B2178807 : Blo 2177435 2178807 := bstep (se 1 (by rfl) ⟨1634105, by rfl⟩ : syracuseStep 2178807 = 3268211) B3268211
theorem B3490037 : Blo 2177435 3490037 := bbase (se 5 (by rfl) ⟨163595, by rfl⟩ : syracuseStep 3490037 = 327191) (by norm_num)
theorem B2326691 : Blo 2177435 2326691 := bstep (se 1 (by rfl) ⟨1745018, by rfl⟩ : syracuseStep 2326691 = 3490037) B3490037
theorem B6204509 : Blo 2177435 6204509 := bstep (se 3 (by rfl) ⟨1163345, by rfl⟩ : syracuseStep 6204509 = 2326691) B2326691
theorem B4136339 : Blo 2177435 4136339 := bstep (se 1 (by rfl) ⟨3102254, by rfl⟩ : syracuseStep 4136339 = 6204509) B6204509
theorem B2757559 : Blo 2177435 2757559 := bstep (se 1 (by rfl) ⟨2068169, by rfl⟩ : syracuseStep 2757559 = 4136339) B4136339
theorem B3676745 : Blo 2177435 3676745 := bstep (se 2 (by rfl) ⟨1378779, by rfl⟩ : syracuseStep 3676745 = 2757559) B2757559
theorem B2451163 : Blo 2177435 2451163 := bstep (se 1 (by rfl) ⟨1838372, by rfl⟩ : syracuseStep 2451163 = 3676745) B3676745
theorem B3268217 : Blo 2177435 3268217 := bstep (se 2 (by rfl) ⟨1225581, by rfl⟩ : syracuseStep 3268217 = 2451163) B2451163
theorem B2178811 : Blo 2177435 2178811 := bstep (se 1 (by rfl) ⟨1634108, by rfl⟩ : syracuseStep 2178811 = 3268217) B3268217
theorem B53005013 : Blo 2177435 53005013 := bbase (se 7 (by rfl) ⟨621152, by rfl⟩ : syracuseStep 53005013 = 1242305) (by norm_num)
theorem B35336675 : Blo 2177435 35336675 := bstep (se 1 (by rfl) ⟨26502506, by rfl⟩ : syracuseStep 35336675 = 53005013) B53005013
theorem B94231133 : Blo 2177435 94231133 := bstep (se 3 (by rfl) ⟨17668337, by rfl⟩ : syracuseStep 94231133 = 35336675) B35336675
theorem B62820755 : Blo 2177435 62820755 := bstep (se 1 (by rfl) ⟨47115566, by rfl⟩ : syracuseStep 62820755 = 94231133) B94231133
theorem B41880503 : Blo 2177435 41880503 := bstep (se 1 (by rfl) ⟨31410377, by rfl⟩ : syracuseStep 41880503 = 62820755) B62820755
theorem B27920335 : Blo 2177435 27920335 := bstep (se 1 (by rfl) ⟨20940251, by rfl⟩ : syracuseStep 27920335 = 41880503) B41880503
theorem B37227113 : Blo 2177435 37227113 := bstep (se 2 (by rfl) ⟨13960167, by rfl⟩ : syracuseStep 37227113 = 27920335) B27920335
theorem B24818075 : Blo 2177435 24818075 := bstep (se 1 (by rfl) ⟨18613556, by rfl⟩ : syracuseStep 24818075 = 37227113) B37227113
theorem B16545383 : Blo 2177435 16545383 := bstep (se 1 (by rfl) ⟨12409037, by rfl⟩ : syracuseStep 16545383 = 24818075) B24818075
theorem B11030255 : Blo 2177435 11030255 := bstep (se 1 (by rfl) ⟨8272691, by rfl⟩ : syracuseStep 11030255 = 16545383) B16545383
theorem B7353503 : Blo 2177435 7353503 := bstep (se 1 (by rfl) ⟨5515127, by rfl⟩ : syracuseStep 7353503 = 11030255) B11030255
theorem B4902335 : Blo 2177435 4902335 := bstep (se 1 (by rfl) ⟨3676751, by rfl⟩ : syracuseStep 4902335 = 7353503) B7353503
theorem B3268223 : Blo 2177435 3268223 := bstep (se 1 (by rfl) ⟨2451167, by rfl⟩ : syracuseStep 3268223 = 4902335) B4902335
theorem B2178815 : Blo 2177435 2178815 := bstep (se 1 (by rfl) ⟨1634111, by rfl⟩ : syracuseStep 2178815 = 3268223) B3268223
theorem B3268229 : Blo 2177435 3268229 := bbase (se 4 (by rfl) ⟨306396, by rfl⟩ : syracuseStep 3268229 = 612793) (by norm_num)
theorem B2178819 : Blo 2177435 2178819 := bstep (se 1 (by rfl) ⟨1634114, by rfl⟩ : syracuseStep 2178819 = 3268229) B3268229
theorem B3676765 : Blo 2177435 3676765 := bbase (se 3 (by rfl) ⟨689393, by rfl⟩ : syracuseStep 3676765 = 1378787) (by norm_num)
theorem B4902353 : Blo 2177435 4902353 := bstep (se 2 (by rfl) ⟨1838382, by rfl⟩ : syracuseStep 4902353 = 3676765) B3676765
theorem B3268235 : Blo 2177435 3268235 := bstep (se 1 (by rfl) ⟨2451176, by rfl⟩ : syracuseStep 3268235 = 4902353) B4902353
theorem B2178823 : Blo 2177435 2178823 := bstep (se 1 (by rfl) ⟨1634117, by rfl⟩ : syracuseStep 2178823 = 3268235) B3268235
theorem B2451181 : Blo 2177435 2451181 := bbase (se 3 (by rfl) ⟨459596, by rfl⟩ : syracuseStep 2451181 = 919193) (by norm_num)
theorem B3268241 : Blo 2177435 3268241 := bstep (se 2 (by rfl) ⟨1225590, by rfl⟩ : syracuseStep 3268241 = 2451181) B2451181
theorem B2178827 : Blo 2177435 2178827 := bstep (se 1 (by rfl) ⟨1634120, by rfl⟩ : syracuseStep 2178827 = 3268241) B3268241
theorem B7353557 : Blo 2177435 7353557 := bbase (se 7 (by rfl) ⟨86174, by rfl⟩ : syracuseStep 7353557 = 172349) (by norm_num)
theorem B4902371 : Blo 2177435 4902371 := bstep (se 1 (by rfl) ⟨3676778, by rfl⟩ : syracuseStep 4902371 = 7353557) B7353557
theorem B3268247 : Blo 2177435 3268247 := bstep (se 1 (by rfl) ⟨2451185, by rfl⟩ : syracuseStep 3268247 = 4902371) B4902371
theorem B2178831 : Blo 2177435 2178831 := bstep (se 1 (by rfl) ⟨1634123, by rfl⟩ : syracuseStep 2178831 = 3268247) B3268247
theorem B3268253 : Blo 2177435 3268253 := bbase (se 3 (by rfl) ⟨612797, by rfl⟩ : syracuseStep 3268253 = 1225595) (by norm_num)
theorem B2178835 : Blo 2177435 2178835 := bstep (se 1 (by rfl) ⟨1634126, by rfl⟩ : syracuseStep 2178835 = 3268253) B3268253
theorem B4902389 : Blo 2177435 4902389 := bbase (se 5 (by rfl) ⟨229799, by rfl⟩ : syracuseStep 4902389 = 459599) (by norm_num)
theorem B3268259 : Blo 2177435 3268259 := bstep (se 1 (by rfl) ⟨2451194, by rfl⟩ : syracuseStep 3268259 = 4902389) B4902389
theorem B2178839 : Blo 2177435 2178839 := bstep (se 1 (by rfl) ⟨1634129, by rfl⟩ : syracuseStep 2178839 = 3268259) B3268259
theorem B3726965 : Blo 2177435 3726965 := bbase (se 5 (by rfl) ⟨174701, by rfl⟩ : syracuseStep 3726965 = 349403) (by norm_num)
theorem B2484643 : Blo 2177435 2484643 := bstep (se 1 (by rfl) ⟨1863482, by rfl⟩ : syracuseStep 2484643 = 3726965) B3726965
theorem B3312857 : Blo 2177435 3312857 := bstep (se 2 (by rfl) ⟨1242321, by rfl⟩ : syracuseStep 3312857 = 2484643) B2484643
theorem B2208571 : Blo 2177435 2208571 := bstep (se 1 (by rfl) ⟨1656428, by rfl⟩ : syracuseStep 2208571 = 3312857) B3312857
theorem B47116181 : Blo 2177435 47116181 := bstep (se 6 (by rfl) ⟨1104285, by rfl⟩ : syracuseStep 47116181 = 2208571) B2208571
theorem B31410787 : Blo 2177435 31410787 := bstep (se 1 (by rfl) ⟨23558090, by rfl⟩ : syracuseStep 31410787 = 47116181) B47116181
theorem B41881049 : Blo 2177435 41881049 := bstep (se 2 (by rfl) ⟨15705393, by rfl⟩ : syracuseStep 41881049 = 31410787) B31410787
theorem B27920699 : Blo 2177435 27920699 := bstep (se 1 (by rfl) ⟨20940524, by rfl⟩ : syracuseStep 27920699 = 41881049) B41881049
theorem B18613799 : Blo 2177435 18613799 := bstep (se 1 (by rfl) ⟨13960349, by rfl⟩ : syracuseStep 18613799 = 27920699) B27920699
theorem B12409199 : Blo 2177435 12409199 := bstep (se 1 (by rfl) ⟨9306899, by rfl⟩ : syracuseStep 12409199 = 18613799) B18613799
theorem B8272799 : Blo 2177435 8272799 := bstep (se 1 (by rfl) ⟨6204599, by rfl⟩ : syracuseStep 8272799 = 12409199) B12409199
theorem B5515199 : Blo 2177435 5515199 := bstep (se 1 (by rfl) ⟨4136399, by rfl⟩ : syracuseStep 5515199 = 8272799) B8272799
theorem B3676799 : Blo 2177435 3676799 := bstep (se 1 (by rfl) ⟨2757599, by rfl⟩ : syracuseStep 3676799 = 5515199) B5515199
theorem B2451199 : Blo 2177435 2451199 := bstep (se 1 (by rfl) ⟨1838399, by rfl⟩ : syracuseStep 2451199 = 3676799) B3676799
theorem B3268265 : Blo 2177435 3268265 := bstep (se 2 (by rfl) ⟨1225599, by rfl⟩ : syracuseStep 3268265 = 2451199) B2451199
theorem B2178843 : Blo 2177435 2178843 := bstep (se 1 (by rfl) ⟨1634132, by rfl⟩ : syracuseStep 2178843 = 3268265) B3268265
theorem B2326729 : Blo 2177435 2326729 := bbase (se 2 (by rfl) ⟨872523, by rfl⟩ : syracuseStep 2326729 = 1745047) (by norm_num)
theorem B3102305 : Blo 2177435 3102305 := bstep (se 2 (by rfl) ⟨1163364, by rfl⟩ : syracuseStep 3102305 = 2326729) B2326729
theorem B8272813 : Blo 2177435 8272813 := bstep (se 3 (by rfl) ⟨1551152, by rfl⟩ : syracuseStep 8272813 = 3102305) B3102305
theorem B11030417 : Blo 2177435 11030417 := bstep (se 2 (by rfl) ⟨4136406, by rfl⟩ : syracuseStep 11030417 = 8272813) B8272813
theorem B7353611 : Blo 2177435 7353611 := bstep (se 1 (by rfl) ⟨5515208, by rfl⟩ : syracuseStep 7353611 = 11030417) B11030417
theorem B4902407 : Blo 2177435 4902407 := bstep (se 1 (by rfl) ⟨3676805, by rfl⟩ : syracuseStep 4902407 = 7353611) B7353611
theorem B3268271 : Blo 2177435 3268271 := bstep (se 1 (by rfl) ⟨2451203, by rfl⟩ : syracuseStep 3268271 = 4902407) B4902407
theorem B2178847 : Blo 2177435 2178847 := bstep (se 1 (by rfl) ⟨1634135, by rfl⟩ : syracuseStep 2178847 = 3268271) B3268271
theorem B3268277 : Blo 2177435 3268277 := bbase (se 5 (by rfl) ⟨153200, by rfl⟩ : syracuseStep 3268277 = 306401) (by norm_num)
theorem B2178851 : Blo 2177435 2178851 := bstep (se 1 (by rfl) ⟨1634138, by rfl⟩ : syracuseStep 2178851 = 3268277) B3268277
theorem B5515229 : Blo 2177435 5515229 := bbase (se 3 (by rfl) ⟨1034105, by rfl⟩ : syracuseStep 5515229 = 2068211) (by norm_num)
theorem B3676819 : Blo 2177435 3676819 := bstep (se 1 (by rfl) ⟨2757614, by rfl⟩ : syracuseStep 3676819 = 5515229) B5515229
theorem B4902425 : Blo 2177435 4902425 := bstep (se 2 (by rfl) ⟨1838409, by rfl⟩ : syracuseStep 4902425 = 3676819) B3676819
theorem B3268283 : Blo 2177435 3268283 := bstep (se 1 (by rfl) ⟨2451212, by rfl⟩ : syracuseStep 3268283 = 4902425) B4902425
theorem B2178855 : Blo 2177435 2178855 := bstep (se 1 (by rfl) ⟨1634141, by rfl⟩ : syracuseStep 2178855 = 3268283) B3268283
theorem B2451217 : Blo 2177435 2451217 := bbase (se 2 (by rfl) ⟨919206, by rfl⟩ : syracuseStep 2451217 = 1838413) (by norm_num)
theorem B3268289 : Blo 2177435 3268289 := bstep (se 2 (by rfl) ⟨1225608, by rfl⟩ : syracuseStep 3268289 = 2451217) B2451217
theorem B2178859 : Blo 2177435 2178859 := bstep (se 1 (by rfl) ⟨1634144, by rfl⟩ : syracuseStep 2178859 = 3268289) B3268289
theorem B4136437 : Blo 2177435 4136437 := bbase (se 5 (by rfl) ⟨193895, by rfl⟩ : syracuseStep 4136437 = 387791) (by norm_num)
theorem B5515249 : Blo 2177435 5515249 := bstep (se 2 (by rfl) ⟨2068218, by rfl⟩ : syracuseStep 5515249 = 4136437) B4136437
theorem B7353665 : Blo 2177435 7353665 := bstep (se 2 (by rfl) ⟨2757624, by rfl⟩ : syracuseStep 7353665 = 5515249) B5515249
theorem B4902443 : Blo 2177435 4902443 := bstep (se 1 (by rfl) ⟨3676832, by rfl⟩ : syracuseStep 4902443 = 7353665) B7353665
theorem B3268295 : Blo 2177435 3268295 := bstep (se 1 (by rfl) ⟨2451221, by rfl⟩ : syracuseStep 3268295 = 4902443) B4902443
theorem B2178863 : Blo 2177435 2178863 := bstep (se 1 (by rfl) ⟨1634147, by rfl⟩ : syracuseStep 2178863 = 3268295) B3268295
theorem B3268301 : Blo 2177435 3268301 := bbase (se 3 (by rfl) ⟨612806, by rfl⟩ : syracuseStep 3268301 = 1225613) (by norm_num)
theorem B2178867 : Blo 2177435 2178867 := bstep (se 1 (by rfl) ⟨1634150, by rfl⟩ : syracuseStep 2178867 = 3268301) B3268301
theorem B4902461 : Blo 2177435 4902461 := bbase (se 3 (by rfl) ⟨919211, by rfl⟩ : syracuseStep 4902461 = 1838423) (by norm_num)
theorem B3268307 : Blo 2177435 3268307 := bstep (se 1 (by rfl) ⟨2451230, by rfl⟩ : syracuseStep 3268307 = 4902461) B4902461
theorem B2178871 : Blo 2177435 2178871 := bstep (se 1 (by rfl) ⟨1634153, by rfl⟩ : syracuseStep 2178871 = 3268307) B3268307
theorem B3676853 : Blo 2177435 3676853 := bbase (se 5 (by rfl) ⟨172352, by rfl⟩ : syracuseStep 3676853 = 344705) (by norm_num)
theorem B2451235 : Blo 2177435 2451235 := bstep (se 1 (by rfl) ⟨1838426, by rfl⟩ : syracuseStep 2451235 = 3676853) B3676853
theorem B3268313 : Blo 2177435 3268313 := bstep (se 2 (by rfl) ⟨1225617, by rfl⟩ : syracuseStep 3268313 = 2451235) B2451235
theorem B2178875 : Blo 2177435 2178875 := bstep (se 1 (by rfl) ⟨1634156, by rfl⟩ : syracuseStep 2178875 = 3268313) B3268313
theorem B2617609 : Blo 2177435 2617609 := bbase (se 2 (by rfl) ⟨981603, by rfl⟩ : syracuseStep 2617609 = 1963207) (by norm_num)
theorem B3490145 : Blo 2177435 3490145 := bstep (se 2 (by rfl) ⟨1308804, by rfl⟩ : syracuseStep 3490145 = 2617609) B2617609
theorem B2326763 : Blo 2177435 2326763 := bstep (se 1 (by rfl) ⟨1745072, by rfl⟩ : syracuseStep 2326763 = 3490145) B3490145
theorem B6204701 : Blo 2177435 6204701 := bstep (se 3 (by rfl) ⟨1163381, by rfl⟩ : syracuseStep 6204701 = 2326763) B2326763
theorem B16545869 : Blo 2177435 16545869 := bstep (se 3 (by rfl) ⟨3102350, by rfl⟩ : syracuseStep 16545869 = 6204701) B6204701
theorem B11030579 : Blo 2177435 11030579 := bstep (se 1 (by rfl) ⟨8272934, by rfl⟩ : syracuseStep 11030579 = 16545869) B16545869
theorem B7353719 : Blo 2177435 7353719 := bstep (se 1 (by rfl) ⟨5515289, by rfl⟩ : syracuseStep 7353719 = 11030579) B11030579
theorem B4902479 : Blo 2177435 4902479 := bstep (se 1 (by rfl) ⟨3676859, by rfl⟩ : syracuseStep 4902479 = 7353719) B7353719
theorem B3268319 : Blo 2177435 3268319 := bstep (se 1 (by rfl) ⟨2451239, by rfl⟩ : syracuseStep 3268319 = 4902479) B4902479
theorem B2178879 : Blo 2177435 2178879 := bstep (se 1 (by rfl) ⟨1634159, by rfl⟩ : syracuseStep 2178879 = 3268319) B3268319
theorem B3268325 : Blo 2177435 3268325 := bbase (se 4 (by rfl) ⟨306405, by rfl⟩ : syracuseStep 3268325 = 612811) (by norm_num)
theorem B2178883 : Blo 2177435 2178883 := bstep (se 1 (by rfl) ⟨1634162, by rfl⟩ : syracuseStep 2178883 = 3268325) B3268325
theorem B6204725 : Blo 2177435 6204725 := bbase (se 5 (by rfl) ⟨290846, by rfl⟩ : syracuseStep 6204725 = 581693) (by norm_num)
theorem B4136483 : Blo 2177435 4136483 := bstep (se 1 (by rfl) ⟨3102362, by rfl⟩ : syracuseStep 4136483 = 6204725) B6204725
theorem B2757655 : Blo 2177435 2757655 := bstep (se 1 (by rfl) ⟨2068241, by rfl⟩ : syracuseStep 2757655 = 4136483) B4136483
theorem B3676873 : Blo 2177435 3676873 := bstep (se 2 (by rfl) ⟨1378827, by rfl⟩ : syracuseStep 3676873 = 2757655) B2757655
theorem B4902497 : Blo 2177435 4902497 := bstep (se 2 (by rfl) ⟨1838436, by rfl⟩ : syracuseStep 4902497 = 3676873) B3676873
theorem B3268331 : Blo 2177435 3268331 := bstep (se 1 (by rfl) ⟨2451248, by rfl⟩ : syracuseStep 3268331 = 4902497) B4902497
theorem B2178887 : Blo 2177435 2178887 := bstep (se 1 (by rfl) ⟨1634165, by rfl⟩ : syracuseStep 2178887 = 3268331) B3268331
theorem B2451253 : Blo 2177435 2451253 := bbase (se 5 (by rfl) ⟨114902, by rfl⟩ : syracuseStep 2451253 = 229805) (by norm_num)
theorem B3268337 : Blo 2177435 3268337 := bstep (se 2 (by rfl) ⟨1225626, by rfl⟩ : syracuseStep 3268337 = 2451253) B2451253
theorem B2178891 : Blo 2177435 2178891 := bstep (se 1 (by rfl) ⟨1634168, by rfl⟩ : syracuseStep 2178891 = 3268337) B3268337
theorem B2757665 : Blo 2177435 2757665 := bbase (se 2 (by rfl) ⟨1034124, by rfl⟩ : syracuseStep 2757665 = 2068249) (by norm_num)
theorem B7353773 : Blo 2177435 7353773 := bstep (se 3 (by rfl) ⟨1378832, by rfl⟩ : syracuseStep 7353773 = 2757665) B2757665
theorem B4902515 : Blo 2177435 4902515 := bstep (se 1 (by rfl) ⟨3676886, by rfl⟩ : syracuseStep 4902515 = 7353773) B7353773
theorem B3268343 : Blo 2177435 3268343 := bstep (se 1 (by rfl) ⟨2451257, by rfl⟩ : syracuseStep 3268343 = 4902515) B4902515
theorem B2178895 : Blo 2177435 2178895 := bstep (se 1 (by rfl) ⟨1634171, by rfl⟩ : syracuseStep 2178895 = 3268343) B3268343
theorem B3268349 : Blo 2177435 3268349 := bbase (se 3 (by rfl) ⟨612815, by rfl⟩ : syracuseStep 3268349 = 1225631) (by norm_num)
theorem B2178899 : Blo 2177435 2178899 := bstep (se 1 (by rfl) ⟨1634174, by rfl⟩ : syracuseStep 2178899 = 3268349) B3268349
theorem B4902533 : Blo 2177435 4902533 := bbase (se 4 (by rfl) ⟨459612, by rfl⟩ : syracuseStep 4902533 = 919225) (by norm_num)
theorem B3268355 : Blo 2177435 3268355 := bstep (se 1 (by rfl) ⟨2451266, by rfl⟩ : syracuseStep 3268355 = 4902533) B4902533
theorem B2178903 : Blo 2177435 2178903 := bstep (se 1 (by rfl) ⟨1634177, by rfl⟩ : syracuseStep 2178903 = 3268355) B3268355
theorem B2208637 : Blo 2177435 2208637 := bbase (se 3 (by rfl) ⟨414119, by rfl⟩ : syracuseStep 2208637 = 828239) (by norm_num)
theorem B2944849 : Blo 2177435 2944849 := bstep (se 2 (by rfl) ⟨1104318, by rfl⟩ : syracuseStep 2944849 = 2208637) B2208637
theorem B3926465 : Blo 2177435 3926465 := bstep (se 2 (by rfl) ⟨1472424, by rfl⟩ : syracuseStep 3926465 = 2944849) B2944849
theorem B2617643 : Blo 2177435 2617643 := bstep (se 1 (by rfl) ⟨1963232, by rfl⟩ : syracuseStep 2617643 = 3926465) B3926465
theorem B6980381 : Blo 2177435 6980381 := bstep (se 3 (by rfl) ⟨1308821, by rfl⟩ : syracuseStep 6980381 = 2617643) B2617643
theorem B4653587 : Blo 2177435 4653587 := bstep (se 1 (by rfl) ⟨3490190, by rfl⟩ : syracuseStep 4653587 = 6980381) B6980381
theorem B3102391 : Blo 2177435 3102391 := bstep (se 1 (by rfl) ⟨2326793, by rfl⟩ : syracuseStep 3102391 = 4653587) B4653587
theorem B4136521 : Blo 2177435 4136521 := bstep (se 2 (by rfl) ⟨1551195, by rfl⟩ : syracuseStep 4136521 = 3102391) B3102391
theorem B5515361 : Blo 2177435 5515361 := bstep (se 2 (by rfl) ⟨2068260, by rfl⟩ : syracuseStep 5515361 = 4136521) B4136521
theorem B3676907 : Blo 2177435 3676907 := bstep (se 1 (by rfl) ⟨2757680, by rfl⟩ : syracuseStep 3676907 = 5515361) B5515361
theorem B2451271 : Blo 2177435 2451271 := bstep (se 1 (by rfl) ⟨1838453, by rfl⟩ : syracuseStep 2451271 = 3676907) B3676907
theorem B3268361 : Blo 2177435 3268361 := bstep (se 2 (by rfl) ⟨1225635, by rfl⟩ : syracuseStep 3268361 = 2451271) B2451271
theorem B2178907 : Blo 2177435 2178907 := bstep (se 1 (by rfl) ⟨1634180, by rfl⟩ : syracuseStep 2178907 = 3268361) B3268361
theorem B11030741 : Blo 2177435 11030741 := bbase (se 7 (by rfl) ⟨129266, by rfl⟩ : syracuseStep 11030741 = 258533) (by norm_num)
theorem B7353827 : Blo 2177435 7353827 := bstep (se 1 (by rfl) ⟨5515370, by rfl⟩ : syracuseStep 7353827 = 11030741) B11030741
theorem B4902551 : Blo 2177435 4902551 := bstep (se 1 (by rfl) ⟨3676913, by rfl⟩ : syracuseStep 4902551 = 7353827) B7353827
theorem B3268367 : Blo 2177435 3268367 := bstep (se 1 (by rfl) ⟨2451275, by rfl⟩ : syracuseStep 3268367 = 4902551) B4902551
theorem B2178911 : Blo 2177435 2178911 := bstep (se 1 (by rfl) ⟨1634183, by rfl⟩ : syracuseStep 2178911 = 3268367) B3268367
theorem B3268373 : Blo 2177435 3268373 := bbase (se 6 (by rfl) ⟨76602, by rfl⟩ : syracuseStep 3268373 = 153205) (by norm_num)
theorem B2178915 : Blo 2177435 2178915 := bstep (se 1 (by rfl) ⟨1634186, by rfl⟩ : syracuseStep 2178915 = 3268373) B3268373
theorem B2587825 : Blo 2177435 2587825 := bbase (se 2 (by rfl) ⟨970434, by rfl⟩ : syracuseStep 2587825 = 1940869) (by norm_num)
theorem B3450433 : Blo 2177435 3450433 := bstep (se 2 (by rfl) ⟨1293912, by rfl⟩ : syracuseStep 3450433 = 2587825) B2587825
theorem B4600577 : Blo 2177435 4600577 := bstep (se 2 (by rfl) ⟨1725216, by rfl⟩ : syracuseStep 4600577 = 3450433) B3450433
theorem B12268205 : Blo 2177435 12268205 := bstep (se 3 (by rfl) ⟨2300288, by rfl⟩ : syracuseStep 12268205 = 4600577) B4600577
theorem B8178803 : Blo 2177435 8178803 := bstep (se 1 (by rfl) ⟨6134102, by rfl⟩ : syracuseStep 8178803 = 12268205) B12268205
theorem B5452535 : Blo 2177435 5452535 := bstep (se 1 (by rfl) ⟨4089401, by rfl⟩ : syracuseStep 5452535 = 8178803) B8178803
theorem B14540093 : Blo 2177435 14540093 := bstep (se 3 (by rfl) ⟨2726267, by rfl⟩ : syracuseStep 14540093 = 5452535) B5452535
theorem B9693395 : Blo 2177435 9693395 := bstep (se 1 (by rfl) ⟨7270046, by rfl⟩ : syracuseStep 9693395 = 14540093) B14540093
theorem B6462263 : Blo 2177435 6462263 := bstep (se 1 (by rfl) ⟨4846697, by rfl⟩ : syracuseStep 6462263 = 9693395) B9693395
theorem B4308175 : Blo 2177435 4308175 := bstep (se 1 (by rfl) ⟨3231131, by rfl⟩ : syracuseStep 4308175 = 6462263) B6462263
theorem B5744233 : Blo 2177435 5744233 := bstep (se 2 (by rfl) ⟨2154087, by rfl⟩ : syracuseStep 5744233 = 4308175) B4308175
theorem B7658977 : Blo 2177435 7658977 := bstep (se 2 (by rfl) ⟨2872116, by rfl⟩ : syracuseStep 7658977 = 5744233) B5744233
theorem B10211969 : Blo 2177435 10211969 := bstep (se 2 (by rfl) ⟨3829488, by rfl⟩ : syracuseStep 10211969 = 7658977) B7658977
theorem B6807979 : Blo 2177435 6807979 := bstep (se 1 (by rfl) ⟨5105984, by rfl⟩ : syracuseStep 6807979 = 10211969) B10211969
theorem B9077305 : Blo 2177435 9077305 := bstep (se 2 (by rfl) ⟨3403989, by rfl⟩ : syracuseStep 9077305 = 6807979) B6807979
theorem B12103073 : Blo 2177435 12103073 := bstep (se 2 (by rfl) ⟨4538652, by rfl⟩ : syracuseStep 12103073 = 9077305) B9077305
theorem B8068715 : Blo 2177435 8068715 := bstep (se 1 (by rfl) ⟨6051536, by rfl⟩ : syracuseStep 8068715 = 12103073) B12103073
theorem B5379143 : Blo 2177435 5379143 := bstep (se 1 (by rfl) ⟨4034357, by rfl⟩ : syracuseStep 5379143 = 8068715) B8068715
theorem B14344381 : Blo 2177435 14344381 := bstep (se 3 (by rfl) ⟨2689571, by rfl⟩ : syracuseStep 14344381 = 5379143) B5379143
theorem B76503365 : Blo 2177435 76503365 := bstep (se 4 (by rfl) ⟨7172190, by rfl⟩ : syracuseStep 76503365 = 14344381) B14344381
theorem B51002243 : Blo 2177435 51002243 := bstep (se 1 (by rfl) ⟨38251682, by rfl⟩ : syracuseStep 51002243 = 76503365) B76503365
theorem B34001495 : Blo 2177435 34001495 := bstep (se 1 (by rfl) ⟨25501121, by rfl⟩ : syracuseStep 34001495 = 51002243) B51002243
theorem B22667663 : Blo 2177435 22667663 := bstep (se 1 (by rfl) ⟨17000747, by rfl⟩ : syracuseStep 22667663 = 34001495) B34001495
theorem B15111775 : Blo 2177435 15111775 := bstep (se 1 (by rfl) ⟨11333831, by rfl⟩ : syracuseStep 15111775 = 22667663) B22667663
theorem B20149033 : Blo 2177435 20149033 := bstep (se 2 (by rfl) ⟨7555887, by rfl⟩ : syracuseStep 20149033 = 15111775) B15111775
theorem B26865377 : Blo 2177435 26865377 := bstep (se 2 (by rfl) ⟨10074516, by rfl⟩ : syracuseStep 26865377 = 20149033) B20149033
theorem B17910251 : Blo 2177435 17910251 := bstep (se 1 (by rfl) ⟨13432688, by rfl⟩ : syracuseStep 17910251 = 26865377) B26865377
theorem B11940167 : Blo 2177435 11940167 := bstep (se 1 (by rfl) ⟨8955125, by rfl⟩ : syracuseStep 11940167 = 17910251) B17910251
theorem B31840445 : Blo 2177435 31840445 := bstep (se 3 (by rfl) ⟨5970083, by rfl⟩ : syracuseStep 31840445 = 11940167) B11940167
theorem B21226963 : Blo 2177435 21226963 := bstep (se 1 (by rfl) ⟨15920222, by rfl⟩ : syracuseStep 21226963 = 31840445) B31840445
theorem B28302617 : Blo 2177435 28302617 := bstep (se 2 (by rfl) ⟨10613481, by rfl⟩ : syracuseStep 28302617 = 21226963) B21226963
theorem B18868411 : Blo 2177435 18868411 := bstep (se 1 (by rfl) ⟨14151308, by rfl⟩ : syracuseStep 18868411 = 28302617) B28302617
theorem B25157881 : Blo 2177435 25157881 := bstep (se 2 (by rfl) ⟨9434205, by rfl⟩ : syracuseStep 25157881 = 18868411) B18868411
theorem B134175365 : Blo 2177435 134175365 := bstep (se 4 (by rfl) ⟨12578940, by rfl⟩ : syracuseStep 134175365 = 25157881) B25157881
theorem B89450243 : Blo 2177435 89450243 := bstep (se 1 (by rfl) ⟨67087682, by rfl⟩ : syracuseStep 89450243 = 134175365) B134175365
theorem B59633495 : Blo 2177435 59633495 := bstep (se 1 (by rfl) ⟨44725121, by rfl⟩ : syracuseStep 59633495 = 89450243) B89450243
theorem B39755663 : Blo 2177435 39755663 := bstep (se 1 (by rfl) ⟨29816747, by rfl⟩ : syracuseStep 39755663 = 59633495) B59633495
theorem B26503775 : Blo 2177435 26503775 := bstep (se 1 (by rfl) ⟨19877831, by rfl⟩ : syracuseStep 26503775 = 39755663) B39755663
theorem B17669183 : Blo 2177435 17669183 := bstep (se 1 (by rfl) ⟨13251887, by rfl⟩ : syracuseStep 17669183 = 26503775) B26503775
theorem B47117821 : Blo 2177435 47117821 := bstep (se 3 (by rfl) ⟨8834591, by rfl⟩ : syracuseStep 47117821 = 17669183) B17669183
theorem B62823761 : Blo 2177435 62823761 := bstep (se 2 (by rfl) ⟨23558910, by rfl⟩ : syracuseStep 62823761 = 47117821) B47117821
theorem B41882507 : Blo 2177435 41882507 := bstep (se 1 (by rfl) ⟨31411880, by rfl⟩ : syracuseStep 41882507 = 62823761) B62823761
theorem B27921671 : Blo 2177435 27921671 := bstep (se 1 (by rfl) ⟨20941253, by rfl⟩ : syracuseStep 27921671 = 41882507) B41882507
theorem B18614447 : Blo 2177435 18614447 := bstep (se 1 (by rfl) ⟨13960835, by rfl⟩ : syracuseStep 18614447 = 27921671) B27921671
theorem B12409631 : Blo 2177435 12409631 := bstep (se 1 (by rfl) ⟨9307223, by rfl⟩ : syracuseStep 12409631 = 18614447) B18614447
theorem B8273087 : Blo 2177435 8273087 := bstep (se 1 (by rfl) ⟨6204815, by rfl⟩ : syracuseStep 8273087 = 12409631) B12409631
theorem B5515391 : Blo 2177435 5515391 := bstep (se 1 (by rfl) ⟨4136543, by rfl⟩ : syracuseStep 5515391 = 8273087) B8273087
theorem B3676927 : Blo 2177435 3676927 := bstep (se 1 (by rfl) ⟨2757695, by rfl⟩ : syracuseStep 3676927 = 5515391) B5515391
theorem B4902569 : Blo 2177435 4902569 := bstep (se 2 (by rfl) ⟨1838463, by rfl⟩ : syracuseStep 4902569 = 3676927) B3676927
theorem B3268379 : Blo 2177435 3268379 := bstep (se 1 (by rfl) ⟨2451284, by rfl⟩ : syracuseStep 3268379 = 4902569) B4902569
theorem B2178919 : Blo 2177435 2178919 := bstep (se 1 (by rfl) ⟨1634189, by rfl⟩ : syracuseStep 2178919 = 3268379) B3268379
theorem B2451289 : Blo 2177435 2451289 := bbase (se 2 (by rfl) ⟨919233, by rfl⟩ : syracuseStep 2451289 = 1838467) (by norm_num)
theorem B3268385 : Blo 2177435 3268385 := bstep (se 2 (by rfl) ⟨1225644, by rfl⟩ : syracuseStep 3268385 = 2451289) B2451289
theorem B2178923 : Blo 2177435 2178923 := bstep (se 1 (by rfl) ⟨1634192, by rfl⟩ : syracuseStep 2178923 = 3268385) B3268385
theorem B4653629 : Blo 2177435 4653629 := bbase (se 3 (by rfl) ⟨872555, by rfl⟩ : syracuseStep 4653629 = 1745111) (by norm_num)
theorem B3102419 : Blo 2177435 3102419 := bstep (se 1 (by rfl) ⟨2326814, by rfl⟩ : syracuseStep 3102419 = 4653629) B4653629
theorem B8273117 : Blo 2177435 8273117 := bstep (se 3 (by rfl) ⟨1551209, by rfl⟩ : syracuseStep 8273117 = 3102419) B3102419
theorem B5515411 : Blo 2177435 5515411 := bstep (se 1 (by rfl) ⟨4136558, by rfl⟩ : syracuseStep 5515411 = 8273117) B8273117
theorem B7353881 : Blo 2177435 7353881 := bstep (se 2 (by rfl) ⟨2757705, by rfl⟩ : syracuseStep 7353881 = 5515411) B5515411
theorem B4902587 : Blo 2177435 4902587 := bstep (se 1 (by rfl) ⟨3676940, by rfl⟩ : syracuseStep 4902587 = 7353881) B7353881
theorem B3268391 : Blo 2177435 3268391 := bstep (se 1 (by rfl) ⟨2451293, by rfl⟩ : syracuseStep 3268391 = 4902587) B4902587
theorem B2178927 : Blo 2177435 2178927 := bstep (se 1 (by rfl) ⟨1634195, by rfl⟩ : syracuseStep 2178927 = 3268391) B3268391
theorem B3268397 : Blo 2177435 3268397 := bbase (se 3 (by rfl) ⟨612824, by rfl⟩ : syracuseStep 3268397 = 1225649) (by norm_num)
theorem B2178931 : Blo 2177435 2178931 := bstep (se 1 (by rfl) ⟨1634198, by rfl⟩ : syracuseStep 2178931 = 3268397) B3268397
theorem B4902605 : Blo 2177435 4902605 := bbase (se 3 (by rfl) ⟨919238, by rfl⟩ : syracuseStep 4902605 = 1838477) (by norm_num)
theorem B3268403 : Blo 2177435 3268403 := bstep (se 1 (by rfl) ⟨2451302, by rfl⟩ : syracuseStep 3268403 = 4902605) B4902605
theorem B2178935 : Blo 2177435 2178935 := bstep (se 1 (by rfl) ⟨1634201, by rfl⟩ : syracuseStep 2178935 = 3268403) B3268403
theorem B2757721 : Blo 2177435 2757721 := bbase (se 2 (by rfl) ⟨1034145, by rfl⟩ : syracuseStep 2757721 = 2068291) (by norm_num)
theorem B3676961 : Blo 2177435 3676961 := bstep (se 2 (by rfl) ⟨1378860, by rfl⟩ : syracuseStep 3676961 = 2757721) B2757721
theorem B2451307 : Blo 2177435 2451307 := bstep (se 1 (by rfl) ⟨1838480, by rfl⟩ : syracuseStep 2451307 = 3676961) B3676961
theorem B3268409 : Blo 2177435 3268409 := bstep (se 2 (by rfl) ⟨1225653, by rfl⟩ : syracuseStep 3268409 = 2451307) B2451307
theorem B2178939 : Blo 2177435 2178939 := bstep (se 1 (by rfl) ⟨1634204, by rfl⟩ : syracuseStep 2178939 = 3268409) B3268409
theorem B2484757 : Blo 2177435 2484757 := bbase (se 6 (by rfl) ⟨58236, by rfl⟩ : syracuseStep 2484757 = 116473) (by norm_num)
theorem B3313009 : Blo 2177435 3313009 := bstep (se 2 (by rfl) ⟨1242378, by rfl⟩ : syracuseStep 3313009 = 2484757) B2484757
theorem B4417345 : Blo 2177435 4417345 := bstep (se 2 (by rfl) ⟨1656504, by rfl⟩ : syracuseStep 4417345 = 3313009) B3313009
theorem B5889793 : Blo 2177435 5889793 := bstep (se 2 (by rfl) ⟨2208672, by rfl⟩ : syracuseStep 5889793 = 4417345) B4417345
theorem B7853057 : Blo 2177435 7853057 := bstep (se 2 (by rfl) ⟨2944896, by rfl⟩ : syracuseStep 7853057 = 5889793) B5889793
theorem B5235371 : Blo 2177435 5235371 := bstep (se 1 (by rfl) ⟨3926528, by rfl⟩ : syracuseStep 5235371 = 7853057) B7853057
theorem B3490247 : Blo 2177435 3490247 := bstep (se 1 (by rfl) ⟨2617685, by rfl⟩ : syracuseStep 3490247 = 5235371) B5235371
theorem B9307325 : Blo 2177435 9307325 := bstep (se 3 (by rfl) ⟨1745123, by rfl⟩ : syracuseStep 9307325 = 3490247) B3490247
theorem B24819533 : Blo 2177435 24819533 := bstep (se 3 (by rfl) ⟨4653662, by rfl⟩ : syracuseStep 24819533 = 9307325) B9307325
theorem B16546355 : Blo 2177435 16546355 := bstep (se 1 (by rfl) ⟨12409766, by rfl⟩ : syracuseStep 16546355 = 24819533) B24819533
theorem B11030903 : Blo 2177435 11030903 := bstep (se 1 (by rfl) ⟨8273177, by rfl⟩ : syracuseStep 11030903 = 16546355) B16546355
theorem B7353935 : Blo 2177435 7353935 := bstep (se 1 (by rfl) ⟨5515451, by rfl⟩ : syracuseStep 7353935 = 11030903) B11030903
theorem B4902623 : Blo 2177435 4902623 := bstep (se 1 (by rfl) ⟨3676967, by rfl⟩ : syracuseStep 4902623 = 7353935) B7353935
theorem B3268415 : Blo 2177435 3268415 := bstep (se 1 (by rfl) ⟨2451311, by rfl⟩ : syracuseStep 3268415 = 4902623) B4902623
theorem B2178943 : Blo 2177435 2178943 := bstep (se 1 (by rfl) ⟨1634207, by rfl⟩ : syracuseStep 2178943 = 3268415) B3268415
theorem B3268421 : Blo 2177435 3268421 := bbase (se 4 (by rfl) ⟨306414, by rfl⟩ : syracuseStep 3268421 = 612829) (by norm_num)
theorem B2178947 : Blo 2177435 2178947 := bstep (se 1 (by rfl) ⟨1634210, by rfl⟩ : syracuseStep 2178947 = 3268421) B3268421
theorem B3676981 : Blo 2177435 3676981 := bbase (se 5 (by rfl) ⟨172358, by rfl⟩ : syracuseStep 3676981 = 344717) (by norm_num)
theorem B4902641 : Blo 2177435 4902641 := bstep (se 2 (by rfl) ⟨1838490, by rfl⟩ : syracuseStep 4902641 = 3676981) B3676981
theorem B3268427 : Blo 2177435 3268427 := bstep (se 1 (by rfl) ⟨2451320, by rfl⟩ : syracuseStep 3268427 = 4902641) B4902641
theorem B2178951 : Blo 2177435 2178951 := bstep (se 1 (by rfl) ⟨1634213, by rfl⟩ : syracuseStep 2178951 = 3268427) B3268427
theorem B2451325 : Blo 2177435 2451325 := bbase (se 3 (by rfl) ⟨459623, by rfl⟩ : syracuseStep 2451325 = 919247) (by norm_num)
theorem B3268433 : Blo 2177435 3268433 := bstep (se 2 (by rfl) ⟨1225662, by rfl⟩ : syracuseStep 3268433 = 2451325) B2451325
theorem B2178955 : Blo 2177435 2178955 := bstep (se 1 (by rfl) ⟨1634216, by rfl⟩ : syracuseStep 2178955 = 3268433) B3268433
theorem B7353989 : Blo 2177435 7353989 := bbase (se 4 (by rfl) ⟨689436, by rfl⟩ : syracuseStep 7353989 = 1378873) (by norm_num)
theorem B4902659 : Blo 2177435 4902659 := bstep (se 1 (by rfl) ⟨3676994, by rfl⟩ : syracuseStep 4902659 = 7353989) B7353989
theorem B3268439 : Blo 2177435 3268439 := bstep (se 1 (by rfl) ⟨2451329, by rfl⟩ : syracuseStep 3268439 = 4902659) B4902659
theorem B2178959 : Blo 2177435 2178959 := bstep (se 1 (by rfl) ⟨1634219, by rfl⟩ : syracuseStep 2178959 = 3268439) B3268439
theorem B3268445 : Blo 2177435 3268445 := bbase (se 3 (by rfl) ⟨612833, by rfl⟩ : syracuseStep 3268445 = 1225667) (by norm_num)
theorem B2178963 : Blo 2177435 2178963 := bstep (se 1 (by rfl) ⟨1634222, by rfl⟩ : syracuseStep 2178963 = 3268445) B3268445
theorem B4902677 : Blo 2177435 4902677 := bbase (se 6 (by rfl) ⟨114906, by rfl⟩ : syracuseStep 4902677 = 229813) (by norm_num)
theorem B3268451 : Blo 2177435 3268451 := bstep (se 1 (by rfl) ⟨2451338, by rfl⟩ : syracuseStep 3268451 = 4902677) B4902677
theorem B2178967 : Blo 2177435 2178967 := bstep (se 1 (by rfl) ⟨1634225, by rfl⟩ : syracuseStep 2178967 = 3268451) B3268451
theorem B8273285 : Blo 2177435 8273285 := bbase (se 4 (by rfl) ⟨775620, by rfl⟩ : syracuseStep 8273285 = 1551241) (by norm_num)
theorem B5515523 : Blo 2177435 5515523 := bstep (se 1 (by rfl) ⟨4136642, by rfl⟩ : syracuseStep 5515523 = 8273285) B8273285
theorem B3677015 : Blo 2177435 3677015 := bstep (se 1 (by rfl) ⟨2757761, by rfl⟩ : syracuseStep 3677015 = 5515523) B5515523
theorem B2451343 : Blo 2177435 2451343 := bstep (se 1 (by rfl) ⟨1838507, by rfl⟩ : syracuseStep 2451343 = 3677015) B3677015
theorem B3268457 : Blo 2177435 3268457 := bstep (se 2 (by rfl) ⟨1225671, by rfl⟩ : syracuseStep 3268457 = 2451343) B2451343
theorem B2178971 : Blo 2177435 2178971 := bstep (se 1 (by rfl) ⟨1634228, by rfl⟩ : syracuseStep 2178971 = 3268457) B3268457
theorem B6980597 : Blo 2177435 6980597 := bbase (se 5 (by rfl) ⟨327215, by rfl⟩ : syracuseStep 6980597 = 654431) (by norm_num)
theorem B4653731 : Blo 2177435 4653731 := bstep (se 1 (by rfl) ⟨3490298, by rfl⟩ : syracuseStep 4653731 = 6980597) B6980597
theorem B12409949 : Blo 2177435 12409949 := bstep (se 3 (by rfl) ⟨2326865, by rfl⟩ : syracuseStep 12409949 = 4653731) B4653731
theorem B8273299 : Blo 2177435 8273299 := bstep (se 1 (by rfl) ⟨6204974, by rfl⟩ : syracuseStep 8273299 = 12409949) B12409949
theorem B11031065 : Blo 2177435 11031065 := bstep (se 2 (by rfl) ⟨4136649, by rfl⟩ : syracuseStep 11031065 = 8273299) B8273299
theorem B7354043 : Blo 2177435 7354043 := bstep (se 1 (by rfl) ⟨5515532, by rfl⟩ : syracuseStep 7354043 = 11031065) B11031065
theorem B4902695 : Blo 2177435 4902695 := bstep (se 1 (by rfl) ⟨3677021, by rfl⟩ : syracuseStep 4902695 = 7354043) B7354043
theorem B3268463 : Blo 2177435 3268463 := bstep (se 1 (by rfl) ⟨2451347, by rfl⟩ : syracuseStep 3268463 = 4902695) B4902695
theorem B2178975 : Blo 2177435 2178975 := bstep (se 1 (by rfl) ⟨1634231, by rfl⟩ : syracuseStep 2178975 = 3268463) B3268463
theorem B3268469 : Blo 2177435 3268469 := bbase (se 5 (by rfl) ⟨153209, by rfl⟩ : syracuseStep 3268469 = 306419) (by norm_num)
theorem B2178979 : Blo 2177435 2178979 := bstep (se 1 (by rfl) ⟨1634234, by rfl⟩ : syracuseStep 2178979 = 3268469) B3268469
theorem B4653749 : Blo 2177435 4653749 := bbase (se 5 (by rfl) ⟨218144, by rfl⟩ : syracuseStep 4653749 = 436289) (by norm_num)
theorem B3102499 : Blo 2177435 3102499 := bstep (se 1 (by rfl) ⟨2326874, by rfl⟩ : syracuseStep 3102499 = 4653749) B4653749
theorem B4136665 : Blo 2177435 4136665 := bstep (se 2 (by rfl) ⟨1551249, by rfl⟩ : syracuseStep 4136665 = 3102499) B3102499
theorem B5515553 : Blo 2177435 5515553 := bstep (se 2 (by rfl) ⟨2068332, by rfl⟩ : syracuseStep 5515553 = 4136665) B4136665
theorem B3677035 : Blo 2177435 3677035 := bstep (se 1 (by rfl) ⟨2757776, by rfl⟩ : syracuseStep 3677035 = 5515553) B5515553
theorem B4902713 : Blo 2177435 4902713 := bstep (se 2 (by rfl) ⟨1838517, by rfl⟩ : syracuseStep 4902713 = 3677035) B3677035
theorem B3268475 : Blo 2177435 3268475 := bstep (se 1 (by rfl) ⟨2451356, by rfl⟩ : syracuseStep 3268475 = 4902713) B4902713
theorem B2178983 : Blo 2177435 2178983 := bstep (se 1 (by rfl) ⟨1634237, by rfl⟩ : syracuseStep 2178983 = 3268475) B3268475
theorem B2451361 : Blo 2177435 2451361 := bbase (se 2 (by rfl) ⟨919260, by rfl⟩ : syracuseStep 2451361 = 1838521) (by norm_num)
theorem B3268481 : Blo 2177435 3268481 := bstep (se 2 (by rfl) ⟨1225680, by rfl⟩ : syracuseStep 3268481 = 2451361) B2451361
theorem B2178987 : Blo 2177435 2178987 := bstep (se 1 (by rfl) ⟨1634240, by rfl⟩ : syracuseStep 2178987 = 3268481) B3268481
theorem B5515573 : Blo 2177435 5515573 := bbase (se 5 (by rfl) ⟨258542, by rfl⟩ : syracuseStep 5515573 = 517085) (by norm_num)
theorem B7354097 : Blo 2177435 7354097 := bstep (se 2 (by rfl) ⟨2757786, by rfl⟩ : syracuseStep 7354097 = 5515573) B5515573
theorem B4902731 : Blo 2177435 4902731 := bstep (se 1 (by rfl) ⟨3677048, by rfl⟩ : syracuseStep 4902731 = 7354097) B7354097
theorem B3268487 : Blo 2177435 3268487 := bstep (se 1 (by rfl) ⟨2451365, by rfl⟩ : syracuseStep 3268487 = 4902731) B4902731
theorem B2178991 : Blo 2177435 2178991 := bstep (se 1 (by rfl) ⟨1634243, by rfl⟩ : syracuseStep 2178991 = 3268487) B3268487
theorem B3268493 : Blo 2177435 3268493 := bbase (se 3 (by rfl) ⟨612842, by rfl⟩ : syracuseStep 3268493 = 1225685) (by norm_num)
theorem B2178995 : Blo 2177435 2178995 := bstep (se 1 (by rfl) ⟨1634246, by rfl⟩ : syracuseStep 2178995 = 3268493) B3268493
theorem B4902749 : Blo 2177435 4902749 := bbase (se 3 (by rfl) ⟨919265, by rfl⟩ : syracuseStep 4902749 = 1838531) (by norm_num)
theorem B3268499 : Blo 2177435 3268499 := bstep (se 1 (by rfl) ⟨2451374, by rfl⟩ : syracuseStep 3268499 = 4902749) B4902749
theorem B2178999 : Blo 2177435 2178999 := bstep (se 1 (by rfl) ⟨1634249, by rfl⟩ : syracuseStep 2178999 = 3268499) B3268499
theorem B3677069 : Blo 2177435 3677069 := bbase (se 3 (by rfl) ⟨689450, by rfl⟩ : syracuseStep 3677069 = 1378901) (by norm_num)
theorem B2451379 : Blo 2177435 2451379 := bstep (se 1 (by rfl) ⟨1838534, by rfl⟩ : syracuseStep 2451379 = 3677069) B3677069
theorem B3268505 : Blo 2177435 3268505 := bstep (se 2 (by rfl) ⟨1225689, by rfl⟩ : syracuseStep 3268505 = 2451379) B2451379
theorem B2179003 : Blo 2177435 2179003 := bstep (se 1 (by rfl) ⟨1634252, by rfl⟩ : syracuseStep 2179003 = 3268505) B3268505
theorem B23881301 : Blo 2177435 23881301 := bbase (se 8 (by rfl) ⟨139929, by rfl⟩ : syracuseStep 23881301 = 279859) (by norm_num)
theorem B15920867 : Blo 2177435 15920867 := bstep (se 1 (by rfl) ⟨11940650, by rfl⟩ : syracuseStep 15920867 = 23881301) B23881301
theorem B10613911 : Blo 2177435 10613911 := bstep (se 1 (by rfl) ⟨7960433, by rfl⟩ : syracuseStep 10613911 = 15920867) B15920867
theorem B14151881 : Blo 2177435 14151881 := bstep (se 2 (by rfl) ⟨5306955, by rfl⟩ : syracuseStep 14151881 = 10613911) B10613911
theorem B37738349 : Blo 2177435 37738349 := bstep (se 3 (by rfl) ⟨7075940, by rfl⟩ : syracuseStep 37738349 = 14151881) B14151881
theorem B25158899 : Blo 2177435 25158899 := bstep (se 1 (by rfl) ⟨18869174, by rfl⟩ : syracuseStep 25158899 = 37738349) B37738349
theorem B16772599 : Blo 2177435 16772599 := bstep (se 1 (by rfl) ⟨12579449, by rfl⟩ : syracuseStep 16772599 = 25158899) B25158899
theorem B22363465 : Blo 2177435 22363465 := bstep (se 2 (by rfl) ⟨8386299, by rfl⟩ : syracuseStep 22363465 = 16772599) B16772599
theorem B29817953 : Blo 2177435 29817953 := bstep (se 2 (by rfl) ⟨11181732, by rfl⟩ : syracuseStep 29817953 = 22363465) B22363465
theorem B19878635 : Blo 2177435 19878635 := bstep (se 1 (by rfl) ⟨14908976, by rfl⟩ : syracuseStep 19878635 = 29817953) B29817953
theorem B13252423 : Blo 2177435 13252423 := bstep (se 1 (by rfl) ⟨9939317, by rfl⟩ : syracuseStep 13252423 = 19878635) B19878635
theorem B17669897 : Blo 2177435 17669897 := bstep (se 2 (by rfl) ⟨6626211, by rfl⟩ : syracuseStep 17669897 = 13252423) B13252423
theorem B11779931 : Blo 2177435 11779931 := bstep (se 1 (by rfl) ⟨8834948, by rfl⟩ : syracuseStep 11779931 = 17669897) B17669897
theorem B7853287 : Blo 2177435 7853287 := bstep (se 1 (by rfl) ⟨5889965, by rfl⟩ : syracuseStep 7853287 = 11779931) B11779931
theorem B10471049 : Blo 2177435 10471049 := bstep (se 2 (by rfl) ⟨3926643, by rfl⟩ : syracuseStep 10471049 = 7853287) B7853287
theorem B6980699 : Blo 2177435 6980699 := bstep (se 1 (by rfl) ⟨5235524, by rfl⟩ : syracuseStep 6980699 = 10471049) B10471049
theorem B18615197 : Blo 2177435 18615197 := bstep (se 3 (by rfl) ⟨3490349, by rfl⟩ : syracuseStep 18615197 = 6980699) B6980699
theorem B12410131 : Blo 2177435 12410131 := bstep (se 1 (by rfl) ⟨9307598, by rfl⟩ : syracuseStep 12410131 = 18615197) B18615197
theorem B16546841 : Blo 2177435 16546841 := bstep (se 2 (by rfl) ⟨6205065, by rfl⟩ : syracuseStep 16546841 = 12410131) B12410131
theorem B11031227 : Blo 2177435 11031227 := bstep (se 1 (by rfl) ⟨8273420, by rfl⟩ : syracuseStep 11031227 = 16546841) B16546841
theorem B7354151 : Blo 2177435 7354151 := bstep (se 1 (by rfl) ⟨5515613, by rfl⟩ : syracuseStep 7354151 = 11031227) B11031227
theorem B4902767 : Blo 2177435 4902767 := bstep (se 1 (by rfl) ⟨3677075, by rfl⟩ : syracuseStep 4902767 = 7354151) B7354151
theorem B3268511 : Blo 2177435 3268511 := bstep (se 1 (by rfl) ⟨2451383, by rfl⟩ : syracuseStep 3268511 = 4902767) B4902767
theorem B2179007 : Blo 2177435 2179007 := bstep (se 1 (by rfl) ⟨1634255, by rfl⟩ : syracuseStep 2179007 = 3268511) B3268511
theorem B3268517 : Blo 2177435 3268517 := bbase (se 4 (by rfl) ⟨306423, by rfl⟩ : syracuseStep 3268517 = 612847) (by norm_num)
theorem B2179011 : Blo 2177435 2179011 := bstep (se 1 (by rfl) ⟨1634258, by rfl⟩ : syracuseStep 2179011 = 3268517) B3268517
theorem B2757817 : Blo 2177435 2757817 := bbase (se 2 (by rfl) ⟨1034181, by rfl⟩ : syracuseStep 2757817 = 2068363) (by norm_num)
theorem B3677089 : Blo 2177435 3677089 := bstep (se 2 (by rfl) ⟨1378908, by rfl⟩ : syracuseStep 3677089 = 2757817) B2757817
theorem B4902785 : Blo 2177435 4902785 := bstep (se 2 (by rfl) ⟨1838544, by rfl⟩ : syracuseStep 4902785 = 3677089) B3677089
theorem B3268523 : Blo 2177435 3268523 := bstep (se 1 (by rfl) ⟨2451392, by rfl⟩ : syracuseStep 3268523 = 4902785) B4902785
theorem B2179015 : Blo 2177435 2179015 := bstep (se 1 (by rfl) ⟨1634261, by rfl⟩ : syracuseStep 2179015 = 3268523) B3268523
theorem B2451397 : Blo 2177435 2451397 := bbase (se 4 (by rfl) ⟨229818, by rfl⟩ : syracuseStep 2451397 = 459637) (by norm_num)
theorem B3268529 : Blo 2177435 3268529 := bstep (se 2 (by rfl) ⟨1225698, by rfl⟩ : syracuseStep 3268529 = 2451397) B2451397
theorem B2179019 : Blo 2177435 2179019 := bstep (se 1 (by rfl) ⟨1634264, by rfl⟩ : syracuseStep 2179019 = 3268529) B3268529
theorem B4136741 : Blo 2177435 4136741 := bbase (se 4 (by rfl) ⟨387819, by rfl⟩ : syracuseStep 4136741 = 775639) (by norm_num)
theorem B2757827 : Blo 2177435 2757827 := bstep (se 1 (by rfl) ⟨2068370, by rfl⟩ : syracuseStep 2757827 = 4136741) B4136741
theorem B7354205 : Blo 2177435 7354205 := bstep (se 3 (by rfl) ⟨1378913, by rfl⟩ : syracuseStep 7354205 = 2757827) B2757827
theorem B4902803 : Blo 2177435 4902803 := bstep (se 1 (by rfl) ⟨3677102, by rfl⟩ : syracuseStep 4902803 = 7354205) B7354205
theorem B3268535 : Blo 2177435 3268535 := bstep (se 1 (by rfl) ⟨2451401, by rfl⟩ : syracuseStep 3268535 = 4902803) B4902803
theorem B2179023 : Blo 2177435 2179023 := bstep (se 1 (by rfl) ⟨1634267, by rfl⟩ : syracuseStep 2179023 = 3268535) B3268535
theorem B3268541 : Blo 2177435 3268541 := bbase (se 3 (by rfl) ⟨612851, by rfl⟩ : syracuseStep 3268541 = 1225703) (by norm_num)
theorem B2179027 : Blo 2177435 2179027 := bstep (se 1 (by rfl) ⟨1634270, by rfl⟩ : syracuseStep 2179027 = 3268541) B3268541
theorem B4902821 : Blo 2177435 4902821 := bbase (se 4 (by rfl) ⟨459639, by rfl⟩ : syracuseStep 4902821 = 919279) (by norm_num)
theorem B3268547 : Blo 2177435 3268547 := bstep (se 1 (by rfl) ⟨2451410, by rfl⟩ : syracuseStep 3268547 = 4902821) B4902821
theorem B2179031 : Blo 2177435 2179031 := bstep (se 1 (by rfl) ⟨1634273, by rfl⟩ : syracuseStep 2179031 = 3268547) B3268547
theorem B5515685 : Blo 2177435 5515685 := bbase (se 4 (by rfl) ⟨517095, by rfl⟩ : syracuseStep 5515685 = 1034191) (by norm_num)
theorem B3677123 : Blo 2177435 3677123 := bstep (se 1 (by rfl) ⟨2757842, by rfl⟩ : syracuseStep 3677123 = 5515685) B5515685
theorem B2451415 : Blo 2177435 2451415 := bstep (se 1 (by rfl) ⟨1838561, by rfl⟩ : syracuseStep 2451415 = 3677123) B3677123
theorem B3268553 : Blo 2177435 3268553 := bstep (se 2 (by rfl) ⟨1225707, by rfl⟩ : syracuseStep 3268553 = 2451415) B2451415
theorem B2179035 : Blo 2177435 2179035 := bstep (se 1 (by rfl) ⟨1634276, by rfl⟩ : syracuseStep 2179035 = 3268553) B3268553
theorem B6205157 : Blo 2177435 6205157 := bbase (se 4 (by rfl) ⟨581733, by rfl⟩ : syracuseStep 6205157 = 1163467) (by norm_num)
theorem B4136771 : Blo 2177435 4136771 := bstep (se 1 (by rfl) ⟨3102578, by rfl⟩ : syracuseStep 4136771 = 6205157) B6205157
theorem B11031389 : Blo 2177435 11031389 := bstep (se 3 (by rfl) ⟨2068385, by rfl⟩ : syracuseStep 11031389 = 4136771) B4136771
theorem B7354259 : Blo 2177435 7354259 := bstep (se 1 (by rfl) ⟨5515694, by rfl⟩ : syracuseStep 7354259 = 11031389) B11031389
theorem B4902839 : Blo 2177435 4902839 := bstep (se 1 (by rfl) ⟨3677129, by rfl⟩ : syracuseStep 4902839 = 7354259) B7354259
theorem B3268559 : Blo 2177435 3268559 := bstep (se 1 (by rfl) ⟨2451419, by rfl⟩ : syracuseStep 3268559 = 4902839) B4902839
theorem B2179039 : Blo 2177435 2179039 := bstep (se 1 (by rfl) ⟨1634279, by rfl⟩ : syracuseStep 2179039 = 3268559) B3268559
theorem B3268565 : Blo 2177435 3268565 := bbase (se 7 (by rfl) ⟨38303, by rfl⟩ : syracuseStep 3268565 = 76607) (by norm_num)
theorem B2179043 : Blo 2177435 2179043 := bstep (se 1 (by rfl) ⟨1634282, by rfl⟩ : syracuseStep 2179043 = 3268565) B3268565
theorem B8273573 : Blo 2177435 8273573 := bbase (se 4 (by rfl) ⟨775647, by rfl⟩ : syracuseStep 8273573 = 1551295) (by norm_num)
theorem B5515715 : Blo 2177435 5515715 := bstep (se 1 (by rfl) ⟨4136786, by rfl⟩ : syracuseStep 5515715 = 8273573) B8273573
theorem B3677143 : Blo 2177435 3677143 := bstep (se 1 (by rfl) ⟨2757857, by rfl⟩ : syracuseStep 3677143 = 5515715) B5515715
theorem B4902857 : Blo 2177435 4902857 := bstep (se 2 (by rfl) ⟨1838571, by rfl⟩ : syracuseStep 4902857 = 3677143) B3677143
theorem B3268571 : Blo 2177435 3268571 := bstep (se 1 (by rfl) ⟨2451428, by rfl⟩ : syracuseStep 3268571 = 4902857) B4902857
theorem B2179047 : Blo 2177435 2179047 := bstep (se 1 (by rfl) ⟨1634285, by rfl⟩ : syracuseStep 2179047 = 3268571) B3268571
theorem B2451433 : Blo 2177435 2451433 := bbase (se 2 (by rfl) ⟨919287, by rfl⟩ : syracuseStep 2451433 = 1838575) (by norm_num)
theorem B3268577 : Blo 2177435 3268577 := bstep (se 2 (by rfl) ⟨1225716, by rfl⟩ : syracuseStep 3268577 = 2451433) B2451433
theorem B2179051 : Blo 2177435 2179051 := bstep (se 1 (by rfl) ⟨1634288, by rfl⟩ : syracuseStep 2179051 = 3268577) B3268577
theorem B4417573 : Blo 2177435 4417573 := bbase (se 4 (by rfl) ⟨414147, by rfl⟩ : syracuseStep 4417573 = 828295) (by norm_num)
theorem B5890097 : Blo 2177435 5890097 := bstep (se 2 (by rfl) ⟨2208786, by rfl⟩ : syracuseStep 5890097 = 4417573) B4417573
theorem B3926731 : Blo 2177435 3926731 := bstep (se 1 (by rfl) ⟨2945048, by rfl⟩ : syracuseStep 3926731 = 5890097) B5890097
theorem B5235641 : Blo 2177435 5235641 := bstep (se 2 (by rfl) ⟨1963365, by rfl⟩ : syracuseStep 5235641 = 3926731) B3926731
theorem B3490427 : Blo 2177435 3490427 := bstep (se 1 (by rfl) ⟨2617820, by rfl⟩ : syracuseStep 3490427 = 5235641) B5235641
theorem B2326951 : Blo 2177435 2326951 := bstep (se 1 (by rfl) ⟨1745213, by rfl⟩ : syracuseStep 2326951 = 3490427) B3490427
theorem B12410405 : Blo 2177435 12410405 := bstep (se 4 (by rfl) ⟨1163475, by rfl⟩ : syracuseStep 12410405 = 2326951) B2326951
theorem B8273603 : Blo 2177435 8273603 := bstep (se 1 (by rfl) ⟨6205202, by rfl⟩ : syracuseStep 8273603 = 12410405) B12410405
theorem B5515735 : Blo 2177435 5515735 := bstep (se 1 (by rfl) ⟨4136801, by rfl⟩ : syracuseStep 5515735 = 8273603) B8273603
theorem B7354313 : Blo 2177435 7354313 := bstep (se 2 (by rfl) ⟨2757867, by rfl⟩ : syracuseStep 7354313 = 5515735) B5515735
theorem B4902875 : Blo 2177435 4902875 := bstep (se 1 (by rfl) ⟨3677156, by rfl⟩ : syracuseStep 4902875 = 7354313) B7354313
theorem B3268583 : Blo 2177435 3268583 := bstep (se 1 (by rfl) ⟨2451437, by rfl⟩ : syracuseStep 3268583 = 4902875) B4902875
theorem B2179055 : Blo 2177435 2179055 := bstep (se 1 (by rfl) ⟨1634291, by rfl⟩ : syracuseStep 2179055 = 3268583) B3268583
theorem B3268589 : Blo 2177435 3268589 := bbase (se 3 (by rfl) ⟨612860, by rfl⟩ : syracuseStep 3268589 = 1225721) (by norm_num)
theorem B2179059 : Blo 2177435 2179059 := bstep (se 1 (by rfl) ⟨1634294, by rfl⟩ : syracuseStep 2179059 = 3268589) B3268589
theorem B4902893 : Blo 2177435 4902893 := bbase (se 3 (by rfl) ⟨919292, by rfl⟩ : syracuseStep 4902893 = 1838585) (by norm_num)
theorem B3268595 : Blo 2177435 3268595 := bstep (se 1 (by rfl) ⟨2451446, by rfl⟩ : syracuseStep 3268595 = 4902893) B4902893
theorem B2179063 : Blo 2177435 2179063 := bstep (se 1 (by rfl) ⟨1634297, by rfl⟩ : syracuseStep 2179063 = 3268595) B3268595
theorem B12269045 : Blo 2177435 12269045 := bbase (se 5 (by rfl) ⟨575111, by rfl⟩ : syracuseStep 12269045 = 1150223) (by norm_num)
theorem B8179363 : Blo 2177435 8179363 := bstep (se 1 (by rfl) ⟨6134522, by rfl⟩ : syracuseStep 8179363 = 12269045) B12269045
theorem B43623269 : Blo 2177435 43623269 := bstep (se 4 (by rfl) ⟨4089681, by rfl⟩ : syracuseStep 43623269 = 8179363) B8179363
theorem B29082179 : Blo 2177435 29082179 := bstep (se 1 (by rfl) ⟨21811634, by rfl⟩ : syracuseStep 29082179 = 43623269) B43623269
theorem B19388119 : Blo 2177435 19388119 := bstep (se 1 (by rfl) ⟨14541089, by rfl⟩ : syracuseStep 19388119 = 29082179) B29082179
theorem B25850825 : Blo 2177435 25850825 := bstep (se 2 (by rfl) ⟨9694059, by rfl⟩ : syracuseStep 25850825 = 19388119) B19388119
theorem B17233883 : Blo 2177435 17233883 := bstep (se 1 (by rfl) ⟨12925412, by rfl⟩ : syracuseStep 17233883 = 25850825) B25850825
theorem B11489255 : Blo 2177435 11489255 := bstep (se 1 (by rfl) ⟨8616941, by rfl⟩ : syracuseStep 11489255 = 17233883) B17233883
theorem B7659503 : Blo 2177435 7659503 := bstep (se 1 (by rfl) ⟨5744627, by rfl⟩ : syracuseStep 7659503 = 11489255) B11489255
theorem B5106335 : Blo 2177435 5106335 := bstep (se 1 (by rfl) ⟨3829751, by rfl⟩ : syracuseStep 5106335 = 7659503) B7659503
theorem B13616893 : Blo 2177435 13616893 := bstep (se 3 (by rfl) ⟨2553167, by rfl⟩ : syracuseStep 13616893 = 5106335) B5106335
theorem B72623429 : Blo 2177435 72623429 := bstep (se 4 (by rfl) ⟨6808446, by rfl⟩ : syracuseStep 72623429 = 13616893) B13616893
theorem B48415619 : Blo 2177435 48415619 := bstep (se 1 (by rfl) ⟨36311714, by rfl⟩ : syracuseStep 48415619 = 72623429) B72623429
theorem B32277079 : Blo 2177435 32277079 := bstep (se 1 (by rfl) ⟨24207809, by rfl⟩ : syracuseStep 32277079 = 48415619) B48415619
theorem B43036105 : Blo 2177435 43036105 := bstep (se 2 (by rfl) ⟨16138539, by rfl⟩ : syracuseStep 43036105 = 32277079) B32277079
theorem B57381473 : Blo 2177435 57381473 := bstep (se 2 (by rfl) ⟨21518052, by rfl⟩ : syracuseStep 57381473 = 43036105) B43036105
theorem B153017261 : Blo 2177435 153017261 := bstep (se 3 (by rfl) ⟨28690736, by rfl⟩ : syracuseStep 153017261 = 57381473) B57381473
theorem B102011507 : Blo 2177435 102011507 := bstep (se 1 (by rfl) ⟨76508630, by rfl⟩ : syracuseStep 102011507 = 153017261) B153017261
theorem B68007671 : Blo 2177435 68007671 := bstep (se 1 (by rfl) ⟨51005753, by rfl⟩ : syracuseStep 68007671 = 102011507) B102011507
theorem B45338447 : Blo 2177435 45338447 := bstep (se 1 (by rfl) ⟨34003835, by rfl⟩ : syracuseStep 45338447 = 68007671) B68007671
theorem B30225631 : Blo 2177435 30225631 := bstep (se 1 (by rfl) ⟨22669223, by rfl⟩ : syracuseStep 30225631 = 45338447) B45338447
theorem B40300841 : Blo 2177435 40300841 := bstep (se 2 (by rfl) ⟨15112815, by rfl⟩ : syracuseStep 40300841 = 30225631) B30225631
theorem B26867227 : Blo 2177435 26867227 := bstep (se 1 (by rfl) ⟨20150420, by rfl⟩ : syracuseStep 26867227 = 40300841) B40300841
theorem B35822969 : Blo 2177435 35822969 := bstep (se 2 (by rfl) ⟨13433613, by rfl⟩ : syracuseStep 35822969 = 26867227) B26867227
theorem B23881979 : Blo 2177435 23881979 := bstep (se 1 (by rfl) ⟨17911484, by rfl⟩ : syracuseStep 23881979 = 35822969) B35822969
theorem B15921319 : Blo 2177435 15921319 := bstep (se 1 (by rfl) ⟨11940989, by rfl⟩ : syracuseStep 15921319 = 23881979) B23881979
theorem B21228425 : Blo 2177435 21228425 := bstep (se 2 (by rfl) ⟨7960659, by rfl⟩ : syracuseStep 21228425 = 15921319) B15921319
theorem B14152283 : Blo 2177435 14152283 := bstep (se 1 (by rfl) ⟨10614212, by rfl⟩ : syracuseStep 14152283 = 21228425) B21228425
theorem B9434855 : Blo 2177435 9434855 := bstep (se 1 (by rfl) ⟨7076141, by rfl⟩ : syracuseStep 9434855 = 14152283) B14152283
theorem B6289903 : Blo 2177435 6289903 := bstep (se 1 (by rfl) ⟨4717427, by rfl⟩ : syracuseStep 6289903 = 9434855) B9434855
theorem B8386537 : Blo 2177435 8386537 := bstep (se 2 (by rfl) ⟨3144951, by rfl⟩ : syracuseStep 8386537 = 6289903) B6289903
theorem B11182049 : Blo 2177435 11182049 := bstep (se 2 (by rfl) ⟨4193268, by rfl⟩ : syracuseStep 11182049 = 8386537) B8386537
theorem B7454699 : Blo 2177435 7454699 := bstep (se 1 (by rfl) ⟨5591024, by rfl⟩ : syracuseStep 7454699 = 11182049) B11182049
theorem B4969799 : Blo 2177435 4969799 := bstep (se 1 (by rfl) ⟨3727349, by rfl⟩ : syracuseStep 4969799 = 7454699) B7454699
theorem B3313199 : Blo 2177435 3313199 := bstep (se 1 (by rfl) ⟨2484899, by rfl⟩ : syracuseStep 3313199 = 4969799) B4969799
theorem B2208799 : Blo 2177435 2208799 := bstep (se 1 (by rfl) ⟨1656599, by rfl⟩ : syracuseStep 2208799 = 3313199) B3313199
theorem B11780261 : Blo 2177435 11780261 := bstep (se 4 (by rfl) ⟨1104399, by rfl⟩ : syracuseStep 11780261 = 2208799) B2208799
theorem B7853507 : Blo 2177435 7853507 := bstep (se 1 (by rfl) ⟨5890130, by rfl⟩ : syracuseStep 7853507 = 11780261) B11780261
theorem B5235671 : Blo 2177435 5235671 := bstep (se 1 (by rfl) ⟨3926753, by rfl⟩ : syracuseStep 5235671 = 7853507) B7853507
theorem B3490447 : Blo 2177435 3490447 := bstep (se 1 (by rfl) ⟨2617835, by rfl⟩ : syracuseStep 3490447 = 5235671) B5235671
theorem B4653929 : Blo 2177435 4653929 := bstep (se 2 (by rfl) ⟨1745223, by rfl⟩ : syracuseStep 4653929 = 3490447) B3490447
theorem B3102619 : Blo 2177435 3102619 := bstep (se 1 (by rfl) ⟨2326964, by rfl⟩ : syracuseStep 3102619 = 4653929) B4653929
theorem B4136825 : Blo 2177435 4136825 := bstep (se 2 (by rfl) ⟨1551309, by rfl⟩ : syracuseStep 4136825 = 3102619) B3102619
theorem B2757883 : Blo 2177435 2757883 := bstep (se 1 (by rfl) ⟨2068412, by rfl⟩ : syracuseStep 2757883 = 4136825) B4136825
theorem B3677177 : Blo 2177435 3677177 := bstep (se 2 (by rfl) ⟨1378941, by rfl⟩ : syracuseStep 3677177 = 2757883) B2757883
theorem B2451451 : Blo 2177435 2451451 := bstep (se 1 (by rfl) ⟨1838588, by rfl⟩ : syracuseStep 2451451 = 3677177) B3677177
theorem B3268601 : Blo 2177435 3268601 := bstep (se 2 (by rfl) ⟨1225725, by rfl⟩ : syracuseStep 3268601 = 2451451) B2451451
theorem B2179067 : Blo 2177435 2179067 := bstep (se 1 (by rfl) ⟨1634300, by rfl⟩ : syracuseStep 2179067 = 3268601) B3268601
theorem B6462709 : Blo 2177435 6462709 := bbase (se 5 (by rfl) ⟨302939, by rfl⟩ : syracuseStep 6462709 = 605879) (by norm_num)
theorem B34467781 : Blo 2177435 34467781 := bstep (se 4 (by rfl) ⟨3231354, by rfl⟩ : syracuseStep 34467781 = 6462709) B6462709
theorem B45957041 : Blo 2177435 45957041 := bstep (se 2 (by rfl) ⟨17233890, by rfl⟩ : syracuseStep 45957041 = 34467781) B34467781
theorem B30638027 : Blo 2177435 30638027 := bstep (se 1 (by rfl) ⟨22978520, by rfl⟩ : syracuseStep 30638027 = 45957041) B45957041
theorem B81701405 : Blo 2177435 81701405 := bstep (se 3 (by rfl) ⟨15319013, by rfl⟩ : syracuseStep 81701405 = 30638027) B30638027
theorem B54467603 : Blo 2177435 54467603 := bstep (se 1 (by rfl) ⟨40850702, by rfl⟩ : syracuseStep 54467603 = 81701405) B81701405
theorem B36311735 : Blo 2177435 36311735 := bstep (se 1 (by rfl) ⟨27233801, by rfl⟩ : syracuseStep 36311735 = 54467603) B54467603
theorem B96831293 : Blo 2177435 96831293 := bstep (se 3 (by rfl) ⟨18155867, by rfl⟩ : syracuseStep 96831293 = 36311735) B36311735
theorem B258216781 : Blo 2177435 258216781 := bstep (se 3 (by rfl) ⟨48415646, by rfl⟩ : syracuseStep 258216781 = 96831293) B96831293
theorem B344289041 : Blo 2177435 344289041 := bstep (se 2 (by rfl) ⟨129108390, by rfl⟩ : syracuseStep 344289041 = 258216781) B258216781
theorem B229526027 : Blo 2177435 229526027 := bstep (se 1 (by rfl) ⟨172144520, by rfl⟩ : syracuseStep 229526027 = 344289041) B344289041
theorem B153017351 : Blo 2177435 153017351 := bstep (se 1 (by rfl) ⟨114763013, by rfl⟩ : syracuseStep 153017351 = 229526027) B229526027
theorem B102011567 : Blo 2177435 102011567 := bstep (se 1 (by rfl) ⟨76508675, by rfl⟩ : syracuseStep 102011567 = 153017351) B153017351
theorem B272030845 : Blo 2177435 272030845 := bstep (se 3 (by rfl) ⟨51005783, by rfl⟩ : syracuseStep 272030845 = 102011567) B102011567
theorem B362707793 : Blo 2177435 362707793 := bstep (se 2 (by rfl) ⟨136015422, by rfl⟩ : syracuseStep 362707793 = 272030845) B272030845
theorem B241805195 : Blo 2177435 241805195 := bstep (se 1 (by rfl) ⟨181353896, by rfl⟩ : syracuseStep 241805195 = 362707793) B362707793
theorem B161203463 : Blo 2177435 161203463 := bstep (se 1 (by rfl) ⟨120902597, by rfl⟩ : syracuseStep 161203463 = 241805195) B241805195
theorem B107468975 : Blo 2177435 107468975 := bstep (se 1 (by rfl) ⟨80601731, by rfl⟩ : syracuseStep 107468975 = 161203463) B161203463
theorem B286583933 : Blo 2177435 286583933 := bstep (se 3 (by rfl) ⟨53734487, by rfl⟩ : syracuseStep 286583933 = 107468975) B107468975
theorem B191055955 : Blo 2177435 191055955 := bstep (se 1 (by rfl) ⟨143291966, by rfl⟩ : syracuseStep 191055955 = 286583933) B286583933
theorem B254741273 : Blo 2177435 254741273 := bstep (se 2 (by rfl) ⟨95527977, by rfl⟩ : syracuseStep 254741273 = 191055955) B191055955
theorem B169827515 : Blo 2177435 169827515 := bstep (se 1 (by rfl) ⟨127370636, by rfl⟩ : syracuseStep 169827515 = 254741273) B254741273
theorem B113218343 : Blo 2177435 113218343 := bstep (se 1 (by rfl) ⟨84913757, by rfl⟩ : syracuseStep 113218343 = 169827515) B169827515
theorem B75478895 : Blo 2177435 75478895 := bstep (se 1 (by rfl) ⟨56609171, by rfl⟩ : syracuseStep 75478895 = 113218343) B113218343
theorem B50319263 : Blo 2177435 50319263 := bstep (se 1 (by rfl) ⟨37739447, by rfl⟩ : syracuseStep 50319263 = 75478895) B75478895
theorem B134184701 : Blo 2177435 134184701 := bstep (se 3 (by rfl) ⟨25159631, by rfl⟩ : syracuseStep 134184701 = 50319263) B50319263
theorem B357825869 : Blo 2177435 357825869 := bstep (se 3 (by rfl) ⟨67092350, by rfl⟩ : syracuseStep 357825869 = 134184701) B134184701
theorem B238550579 : Blo 2177435 238550579 := bstep (se 1 (by rfl) ⟨178912934, by rfl⟩ : syracuseStep 238550579 = 357825869) B357825869
theorem B159033719 : Blo 2177435 159033719 := bstep (se 1 (by rfl) ⟨119275289, by rfl⟩ : syracuseStep 159033719 = 238550579) B238550579
theorem B424089917 : Blo 2177435 424089917 := bstep (se 3 (by rfl) ⟨79516859, by rfl⟩ : syracuseStep 424089917 = 159033719) B159033719
theorem B282726611 : Blo 2177435 282726611 := bstep (se 1 (by rfl) ⟨212044958, by rfl⟩ : syracuseStep 282726611 = 424089917) B424089917
theorem B188484407 : Blo 2177435 188484407 := bstep (se 1 (by rfl) ⟨141363305, by rfl⟩ : syracuseStep 188484407 = 282726611) B282726611
theorem B125656271 : Blo 2177435 125656271 := bstep (se 1 (by rfl) ⟨94242203, by rfl⟩ : syracuseStep 125656271 = 188484407) B188484407
theorem B83770847 : Blo 2177435 83770847 := bstep (se 1 (by rfl) ⟨62828135, by rfl⟩ : syracuseStep 83770847 = 125656271) B125656271
theorem B55847231 : Blo 2177435 55847231 := bstep (se 1 (by rfl) ⟨41885423, by rfl⟩ : syracuseStep 55847231 = 83770847) B83770847
theorem B37231487 : Blo 2177435 37231487 := bstep (se 1 (by rfl) ⟨27923615, by rfl⟩ : syracuseStep 37231487 = 55847231) B55847231
theorem B24820991 : Blo 2177435 24820991 := bstep (se 1 (by rfl) ⟨18615743, by rfl⟩ : syracuseStep 24820991 = 37231487) B37231487
theorem B16547327 : Blo 2177435 16547327 := bstep (se 1 (by rfl) ⟨12410495, by rfl⟩ : syracuseStep 16547327 = 24820991) B24820991
theorem B11031551 : Blo 2177435 11031551 := bstep (se 1 (by rfl) ⟨8273663, by rfl⟩ : syracuseStep 11031551 = 16547327) B16547327
theorem B7354367 : Blo 2177435 7354367 := bstep (se 1 (by rfl) ⟨5515775, by rfl⟩ : syracuseStep 7354367 = 11031551) B11031551
theorem B4902911 : Blo 2177435 4902911 := bstep (se 1 (by rfl) ⟨3677183, by rfl⟩ : syracuseStep 4902911 = 7354367) B7354367
theorem B3268607 : Blo 2177435 3268607 := bstep (se 1 (by rfl) ⟨2451455, by rfl⟩ : syracuseStep 3268607 = 4902911) B4902911
theorem B2179071 : Blo 2177435 2179071 := bstep (se 1 (by rfl) ⟨1634303, by rfl⟩ : syracuseStep 2179071 = 3268607) B3268607
theorem B3268613 : Blo 2177435 3268613 := bbase (se 4 (by rfl) ⟨306432, by rfl⟩ : syracuseStep 3268613 = 612865) (by norm_num)
theorem B2179075 : Blo 2177435 2179075 := bstep (se 1 (by rfl) ⟨1634306, by rfl⟩ : syracuseStep 2179075 = 3268613) B3268613
theorem B3677197 : Blo 2177435 3677197 := bbase (se 3 (by rfl) ⟨689474, by rfl⟩ : syracuseStep 3677197 = 1378949) (by norm_num)
theorem B4902929 : Blo 2177435 4902929 := bstep (se 2 (by rfl) ⟨1838598, by rfl⟩ : syracuseStep 4902929 = 3677197) B3677197
theorem B3268619 : Blo 2177435 3268619 := bstep (se 1 (by rfl) ⟨2451464, by rfl⟩ : syracuseStep 3268619 = 4902929) B4902929
theorem B2179079 : Blo 2177435 2179079 := bstep (se 1 (by rfl) ⟨1634309, by rfl⟩ : syracuseStep 2179079 = 3268619) B3268619
theorem B2451469 : Blo 2177435 2451469 := bbase (se 3 (by rfl) ⟨459650, by rfl⟩ : syracuseStep 2451469 = 919301) (by norm_num)
theorem B3268625 : Blo 2177435 3268625 := bstep (se 2 (by rfl) ⟨1225734, by rfl⟩ : syracuseStep 3268625 = 2451469) B2451469
theorem B2179083 : Blo 2177435 2179083 := bstep (se 1 (by rfl) ⟨1634312, by rfl⟩ : syracuseStep 2179083 = 3268625) B3268625
theorem B7354421 : Blo 2177435 7354421 := bbase (se 5 (by rfl) ⟨344738, by rfl⟩ : syracuseStep 7354421 = 689477) (by norm_num)
theorem B4902947 : Blo 2177435 4902947 := bstep (se 1 (by rfl) ⟨3677210, by rfl⟩ : syracuseStep 4902947 = 7354421) B7354421
theorem B3268631 : Blo 2177435 3268631 := bstep (se 1 (by rfl) ⟨2451473, by rfl⟩ : syracuseStep 3268631 = 4902947) B4902947
theorem B2179087 : Blo 2177435 2179087 := bstep (se 1 (by rfl) ⟨1634315, by rfl⟩ : syracuseStep 2179087 = 3268631) B3268631
theorem B3268637 : Blo 2177435 3268637 := bbase (se 3 (by rfl) ⟨612869, by rfl⟩ : syracuseStep 3268637 = 1225739) (by norm_num)
theorem B2179091 : Blo 2177435 2179091 := bstep (se 1 (by rfl) ⟨1634318, by rfl⟩ : syracuseStep 2179091 = 3268637) B3268637
theorem B4902965 : Blo 2177435 4902965 := bbase (se 5 (by rfl) ⟨229826, by rfl⟩ : syracuseStep 4902965 = 459653) (by norm_num)
theorem B3268643 : Blo 2177435 3268643 := bstep (se 1 (by rfl) ⟨2451482, by rfl⟩ : syracuseStep 3268643 = 4902965) B4902965
theorem B2179095 : Blo 2177435 2179095 := bstep (se 1 (by rfl) ⟨1634321, by rfl⟩ : syracuseStep 2179095 = 3268643) B3268643
theorem B10471493 : Blo 2177435 10471493 := bbase (se 4 (by rfl) ⟨981702, by rfl⟩ : syracuseStep 10471493 = 1963405) (by norm_num)
theorem B6980995 : Blo 2177435 6980995 := bstep (se 1 (by rfl) ⟨5235746, by rfl⟩ : syracuseStep 6980995 = 10471493) B10471493
theorem B9307993 : Blo 2177435 9307993 := bstep (se 2 (by rfl) ⟨3490497, by rfl⟩ : syracuseStep 9307993 = 6980995) B6980995
theorem B12410657 : Blo 2177435 12410657 := bstep (se 2 (by rfl) ⟨4653996, by rfl⟩ : syracuseStep 12410657 = 9307993) B9307993
theorem B8273771 : Blo 2177435 8273771 := bstep (se 1 (by rfl) ⟨6205328, by rfl⟩ : syracuseStep 8273771 = 12410657) B12410657
theorem B5515847 : Blo 2177435 5515847 := bstep (se 1 (by rfl) ⟨4136885, by rfl⟩ : syracuseStep 5515847 = 8273771) B8273771
theorem B3677231 : Blo 2177435 3677231 := bstep (se 1 (by rfl) ⟨2757923, by rfl⟩ : syracuseStep 3677231 = 5515847) B5515847
theorem B2451487 : Blo 2177435 2451487 := bstep (se 1 (by rfl) ⟨1838615, by rfl⟩ : syracuseStep 2451487 = 3677231) B3677231
theorem B3268649 : Blo 2177435 3268649 := bstep (se 2 (by rfl) ⟨1225743, by rfl⟩ : syracuseStep 3268649 = 2451487) B2451487
theorem B2179099 : Blo 2177435 2179099 := bstep (se 1 (by rfl) ⟨1634324, by rfl⟩ : syracuseStep 2179099 = 3268649) B3268649
theorem B4417669 : Blo 2177435 4417669 := bbase (se 4 (by rfl) ⟨414156, by rfl⟩ : syracuseStep 4417669 = 828313) (by norm_num)
theorem B23560901 : Blo 2177435 23560901 := bstep (se 4 (by rfl) ⟨2208834, by rfl⟩ : syracuseStep 23560901 = 4417669) B4417669
theorem B15707267 : Blo 2177435 15707267 := bstep (se 1 (by rfl) ⟨11780450, by rfl⟩ : syracuseStep 15707267 = 23560901) B23560901
theorem B10471511 : Blo 2177435 10471511 := bstep (se 1 (by rfl) ⟨7853633, by rfl⟩ : syracuseStep 10471511 = 15707267) B15707267
theorem B6981007 : Blo 2177435 6981007 := bstep (se 1 (by rfl) ⟨5235755, by rfl⟩ : syracuseStep 6981007 = 10471511) B10471511
theorem B9308009 : Blo 2177435 9308009 := bstep (se 2 (by rfl) ⟨3490503, by rfl⟩ : syracuseStep 9308009 = 6981007) B6981007
theorem B6205339 : Blo 2177435 6205339 := bstep (se 1 (by rfl) ⟨4654004, by rfl⟩ : syracuseStep 6205339 = 9308009) B9308009
theorem B8273785 : Blo 2177435 8273785 := bstep (se 2 (by rfl) ⟨3102669, by rfl⟩ : syracuseStep 8273785 = 6205339) B6205339
theorem B11031713 : Blo 2177435 11031713 := bstep (se 2 (by rfl) ⟨4136892, by rfl⟩ : syracuseStep 11031713 = 8273785) B8273785
theorem B7354475 : Blo 2177435 7354475 := bstep (se 1 (by rfl) ⟨5515856, by rfl⟩ : syracuseStep 7354475 = 11031713) B11031713
theorem B4902983 : Blo 2177435 4902983 := bstep (se 1 (by rfl) ⟨3677237, by rfl⟩ : syracuseStep 4902983 = 7354475) B7354475
theorem B3268655 : Blo 2177435 3268655 := bstep (se 1 (by rfl) ⟨2451491, by rfl⟩ : syracuseStep 3268655 = 4902983) B4902983
theorem B2179103 : Blo 2177435 2179103 := bstep (se 1 (by rfl) ⟨1634327, by rfl⟩ : syracuseStep 2179103 = 3268655) B3268655
theorem B3268661 : Blo 2177435 3268661 := bbase (se 5 (by rfl) ⟨153218, by rfl⟩ : syracuseStep 3268661 = 306437) (by norm_num)
theorem B2179107 : Blo 2177435 2179107 := bstep (se 1 (by rfl) ⟨1634330, by rfl⟩ : syracuseStep 2179107 = 3268661) B3268661
theorem B5515877 : Blo 2177435 5515877 := bbase (se 4 (by rfl) ⟨517113, by rfl⟩ : syracuseStep 5515877 = 1034227) (by norm_num)
theorem B3677251 : Blo 2177435 3677251 := bstep (se 1 (by rfl) ⟨2757938, by rfl⟩ : syracuseStep 3677251 = 5515877) B5515877
theorem B4903001 : Blo 2177435 4903001 := bstep (se 2 (by rfl) ⟨1838625, by rfl⟩ : syracuseStep 4903001 = 3677251) B3677251
theorem B3268667 : Blo 2177435 3268667 := bstep (se 1 (by rfl) ⟨2451500, by rfl⟩ : syracuseStep 3268667 = 4903001) B4903001
theorem B2179111 : Blo 2177435 2179111 := bstep (se 1 (by rfl) ⟨1634333, by rfl⟩ : syracuseStep 2179111 = 3268667) B3268667
theorem B2451505 : Blo 2177435 2451505 := bbase (se 2 (by rfl) ⟨919314, by rfl⟩ : syracuseStep 2451505 = 1838629) (by norm_num)
theorem B3268673 : Blo 2177435 3268673 := bstep (se 2 (by rfl) ⟨1225752, by rfl⟩ : syracuseStep 3268673 = 2451505) B2451505
theorem B2179115 : Blo 2177435 2179115 := bstep (se 1 (by rfl) ⟨1634336, by rfl⟩ : syracuseStep 2179115 = 3268673) B3268673
theorem B10471589 : Blo 2177435 10471589 := bbase (se 4 (by rfl) ⟨981711, by rfl⟩ : syracuseStep 10471589 = 1963423) (by norm_num)
theorem B6981059 : Blo 2177435 6981059 := bstep (se 1 (by rfl) ⟨5235794, by rfl⟩ : syracuseStep 6981059 = 10471589) B10471589
theorem B4654039 : Blo 2177435 4654039 := bstep (se 1 (by rfl) ⟨3490529, by rfl⟩ : syracuseStep 4654039 = 6981059) B6981059
theorem B6205385 : Blo 2177435 6205385 := bstep (se 2 (by rfl) ⟨2327019, by rfl⟩ : syracuseStep 6205385 = 4654039) B4654039
theorem B4136923 : Blo 2177435 4136923 := bstep (se 1 (by rfl) ⟨3102692, by rfl⟩ : syracuseStep 4136923 = 6205385) B6205385
theorem B5515897 : Blo 2177435 5515897 := bstep (se 2 (by rfl) ⟨2068461, by rfl⟩ : syracuseStep 5515897 = 4136923) B4136923
theorem B7354529 : Blo 2177435 7354529 := bstep (se 2 (by rfl) ⟨2757948, by rfl⟩ : syracuseStep 7354529 = 5515897) B5515897
theorem B4903019 : Blo 2177435 4903019 := bstep (se 1 (by rfl) ⟨3677264, by rfl⟩ : syracuseStep 4903019 = 7354529) B7354529
theorem B3268679 : Blo 2177435 3268679 := bstep (se 1 (by rfl) ⟨2451509, by rfl⟩ : syracuseStep 3268679 = 4903019) B4903019
theorem B2179119 : Blo 2177435 2179119 := bstep (se 1 (by rfl) ⟨1634339, by rfl⟩ : syracuseStep 2179119 = 3268679) B3268679
theorem B3268685 : Blo 2177435 3268685 := bbase (se 3 (by rfl) ⟨612878, by rfl⟩ : syracuseStep 3268685 = 1225757) (by norm_num)
theorem B2179123 : Blo 2177435 2179123 := bstep (se 1 (by rfl) ⟨1634342, by rfl⟩ : syracuseStep 2179123 = 3268685) B3268685
theorem B4903037 : Blo 2177435 4903037 := bbase (se 3 (by rfl) ⟨919319, by rfl⟩ : syracuseStep 4903037 = 1838639) (by norm_num)
theorem B3268691 : Blo 2177435 3268691 := bstep (se 1 (by rfl) ⟨2451518, by rfl⟩ : syracuseStep 3268691 = 4903037) B4903037
theorem B2179127 : Blo 2177435 2179127 := bstep (se 1 (by rfl) ⟨1634345, by rfl⟩ : syracuseStep 2179127 = 3268691) B3268691
theorem B3677285 : Blo 2177435 3677285 := bbase (se 4 (by rfl) ⟨344745, by rfl⟩ : syracuseStep 3677285 = 689491) (by norm_num)
theorem B2451523 : Blo 2177435 2451523 := bstep (se 1 (by rfl) ⟨1838642, by rfl⟩ : syracuseStep 2451523 = 3677285) B3677285
theorem B3268697 : Blo 2177435 3268697 := bstep (se 2 (by rfl) ⟨1225761, by rfl⟩ : syracuseStep 3268697 = 2451523) B2451523
theorem B2179131 : Blo 2177435 2179131 := bstep (se 1 (by rfl) ⟨1634348, by rfl⟩ : syracuseStep 2179131 = 3268697) B3268697
theorem B5591197 : Blo 2177435 5591197 := bbase (se 3 (by rfl) ⟨1048349, by rfl⟩ : syracuseStep 5591197 = 2096699) (by norm_num)
theorem B7454929 : Blo 2177435 7454929 := bstep (se 2 (by rfl) ⟨2795598, by rfl⟩ : syracuseStep 7454929 = 5591197) B5591197
theorem B9939905 : Blo 2177435 9939905 := bstep (se 2 (by rfl) ⟨3727464, by rfl⟩ : syracuseStep 9939905 = 7454929) B7454929
theorem B6626603 : Blo 2177435 6626603 := bstep (se 1 (by rfl) ⟨4969952, by rfl⟩ : syracuseStep 6626603 = 9939905) B9939905
theorem B4417735 : Blo 2177435 4417735 := bstep (se 1 (by rfl) ⟨3313301, by rfl⟩ : syracuseStep 4417735 = 6626603) B6626603
theorem B5890313 : Blo 2177435 5890313 := bstep (se 2 (by rfl) ⟨2208867, by rfl⟩ : syracuseStep 5890313 = 4417735) B4417735
theorem B3926875 : Blo 2177435 3926875 := bstep (se 1 (by rfl) ⟨2945156, by rfl⟩ : syracuseStep 3926875 = 5890313) B5890313
theorem B5235833 : Blo 2177435 5235833 := bstep (se 2 (by rfl) ⟨1963437, by rfl⟩ : syracuseStep 5235833 = 3926875) B3926875
theorem B3490555 : Blo 2177435 3490555 := bstep (se 1 (by rfl) ⟨2617916, by rfl⟩ : syracuseStep 3490555 = 5235833) B5235833
theorem B4654073 : Blo 2177435 4654073 := bstep (se 2 (by rfl) ⟨1745277, by rfl⟩ : syracuseStep 4654073 = 3490555) B3490555
theorem B3102715 : Blo 2177435 3102715 := bstep (se 1 (by rfl) ⟨2327036, by rfl⟩ : syracuseStep 3102715 = 4654073) B4654073
theorem B16547813 : Blo 2177435 16547813 := bstep (se 4 (by rfl) ⟨1551357, by rfl⟩ : syracuseStep 16547813 = 3102715) B3102715
theorem B11031875 : Blo 2177435 11031875 := bstep (se 1 (by rfl) ⟨8273906, by rfl⟩ : syracuseStep 11031875 = 16547813) B16547813
theorem B7354583 : Blo 2177435 7354583 := bstep (se 1 (by rfl) ⟨5515937, by rfl⟩ : syracuseStep 7354583 = 11031875) B11031875
theorem B4903055 : Blo 2177435 4903055 := bstep (se 1 (by rfl) ⟨3677291, by rfl⟩ : syracuseStep 4903055 = 7354583) B7354583
theorem B3268703 : Blo 2177435 3268703 := bstep (se 1 (by rfl) ⟨2451527, by rfl⟩ : syracuseStep 3268703 = 4903055) B4903055
theorem B2179135 : Blo 2177435 2179135 := bstep (se 1 (by rfl) ⟨1634351, by rfl⟩ : syracuseStep 2179135 = 3268703) B3268703
theorem B3268709 : Blo 2177435 3268709 := bbase (se 4 (by rfl) ⟨306441, by rfl⟩ : syracuseStep 3268709 = 612883) (by norm_num)
theorem B2179139 : Blo 2177435 2179139 := bstep (se 1 (by rfl) ⟨1634354, by rfl⟩ : syracuseStep 2179139 = 3268709) B3268709
theorem B5235853 : Blo 2177435 5235853 := bbase (se 3 (by rfl) ⟨981722, by rfl⟩ : syracuseStep 5235853 = 1963445) (by norm_num)
theorem B6981137 : Blo 2177435 6981137 := bstep (se 2 (by rfl) ⟨2617926, by rfl⟩ : syracuseStep 6981137 = 5235853) B5235853
theorem B4654091 : Blo 2177435 4654091 := bstep (se 1 (by rfl) ⟨3490568, by rfl⟩ : syracuseStep 4654091 = 6981137) B6981137
theorem B3102727 : Blo 2177435 3102727 := bstep (se 1 (by rfl) ⟨2327045, by rfl⟩ : syracuseStep 3102727 = 4654091) B4654091
theorem B4136969 : Blo 2177435 4136969 := bstep (se 2 (by rfl) ⟨1551363, by rfl⟩ : syracuseStep 4136969 = 3102727) B3102727
theorem B2757979 : Blo 2177435 2757979 := bstep (se 1 (by rfl) ⟨2068484, by rfl⟩ : syracuseStep 2757979 = 4136969) B4136969
theorem B3677305 : Blo 2177435 3677305 := bstep (se 2 (by rfl) ⟨1378989, by rfl⟩ : syracuseStep 3677305 = 2757979) B2757979
theorem B4903073 : Blo 2177435 4903073 := bstep (se 2 (by rfl) ⟨1838652, by rfl⟩ : syracuseStep 4903073 = 3677305) B3677305
theorem B3268715 : Blo 2177435 3268715 := bstep (se 1 (by rfl) ⟨2451536, by rfl⟩ : syracuseStep 3268715 = 4903073) B4903073
theorem B2179143 : Blo 2177435 2179143 := bstep (se 1 (by rfl) ⟨1634357, by rfl⟩ : syracuseStep 2179143 = 3268715) B3268715
theorem B2451541 : Blo 2177435 2451541 := bbase (se 8 (by rfl) ⟨14364, by rfl⟩ : syracuseStep 2451541 = 28729) (by norm_num)
theorem B3268721 : Blo 2177435 3268721 := bstep (se 2 (by rfl) ⟨1225770, by rfl⟩ : syracuseStep 3268721 = 2451541) B2451541
theorem B2179147 : Blo 2177435 2179147 := bstep (se 1 (by rfl) ⟨1634360, by rfl⟩ : syracuseStep 2179147 = 3268721) B3268721
theorem B2757989 : Blo 2177435 2757989 := bbase (se 4 (by rfl) ⟨258561, by rfl⟩ : syracuseStep 2757989 = 517123) (by norm_num)
theorem B7354637 : Blo 2177435 7354637 := bstep (se 3 (by rfl) ⟨1378994, by rfl⟩ : syracuseStep 7354637 = 2757989) B2757989
theorem B4903091 : Blo 2177435 4903091 := bstep (se 1 (by rfl) ⟨3677318, by rfl⟩ : syracuseStep 4903091 = 7354637) B7354637
theorem B3268727 : Blo 2177435 3268727 := bstep (se 1 (by rfl) ⟨2451545, by rfl⟩ : syracuseStep 3268727 = 4903091) B4903091
theorem B2179151 : Blo 2177435 2179151 := bstep (se 1 (by rfl) ⟨1634363, by rfl⟩ : syracuseStep 2179151 = 3268727) B3268727
theorem B3268733 : Blo 2177435 3268733 := bbase (se 3 (by rfl) ⟨612887, by rfl⟩ : syracuseStep 3268733 = 1225775) (by norm_num)
theorem B2179155 : Blo 2177435 2179155 := bstep (se 1 (by rfl) ⟨1634366, by rfl⟩ : syracuseStep 2179155 = 3268733) B3268733
theorem B4903109 : Blo 2177435 4903109 := bbase (se 4 (by rfl) ⟨459666, by rfl⟩ : syracuseStep 4903109 = 919333) (by norm_num)
theorem B3268739 : Blo 2177435 3268739 := bstep (se 1 (by rfl) ⟨2451554, by rfl⟩ : syracuseStep 3268739 = 4903109) B4903109
theorem B2179159 : Blo 2177435 2179159 := bstep (se 1 (by rfl) ⟨1634369, by rfl⟩ : syracuseStep 2179159 = 3268739) B3268739
theorem B3358549 : Blo 2177435 3358549 := bbase (se 9 (by rfl) ⟨9839, by rfl⟩ : syracuseStep 3358549 = 19679) (by norm_num)
theorem B17912261 : Blo 2177435 17912261 := bstep (se 4 (by rfl) ⟨1679274, by rfl⟩ : syracuseStep 17912261 = 3358549) B3358549
theorem B11941507 : Blo 2177435 11941507 := bstep (se 1 (by rfl) ⟨8956130, by rfl⟩ : syracuseStep 11941507 = 17912261) B17912261
theorem B63688037 : Blo 2177435 63688037 := bstep (se 4 (by rfl) ⟨5970753, by rfl⟩ : syracuseStep 63688037 = 11941507) B11941507
theorem B169834765 : Blo 2177435 169834765 := bstep (se 3 (by rfl) ⟨31844018, by rfl⟩ : syracuseStep 169834765 = 63688037) B63688037
theorem B226446353 : Blo 2177435 226446353 := bstep (se 2 (by rfl) ⟨84917382, by rfl⟩ : syracuseStep 226446353 = 169834765) B169834765
theorem B150964235 : Blo 2177435 150964235 := bstep (se 1 (by rfl) ⟨113223176, by rfl⟩ : syracuseStep 150964235 = 226446353) B226446353
theorem B100642823 : Blo 2177435 100642823 := bstep (se 1 (by rfl) ⟨75482117, by rfl⟩ : syracuseStep 100642823 = 150964235) B150964235
theorem B67095215 : Blo 2177435 67095215 := bstep (se 1 (by rfl) ⟨50321411, by rfl⟩ : syracuseStep 67095215 = 100642823) B100642823
theorem B44730143 : Blo 2177435 44730143 := bstep (se 1 (by rfl) ⟨33547607, by rfl⟩ : syracuseStep 44730143 = 67095215) B67095215
theorem B29820095 : Blo 2177435 29820095 := bstep (se 1 (by rfl) ⟨22365071, by rfl⟩ : syracuseStep 29820095 = 44730143) B44730143
theorem B19880063 : Blo 2177435 19880063 := bstep (se 1 (by rfl) ⟨14910047, by rfl⟩ : syracuseStep 19880063 = 29820095) B29820095
theorem B13253375 : Blo 2177435 13253375 := bstep (se 1 (by rfl) ⟨9940031, by rfl⟩ : syracuseStep 13253375 = 19880063) B19880063
theorem B8835583 : Blo 2177435 8835583 := bstep (se 1 (by rfl) ⟨6626687, by rfl⟩ : syracuseStep 8835583 = 13253375) B13253375
theorem B11780777 : Blo 2177435 11780777 := bstep (se 2 (by rfl) ⟨4417791, by rfl⟩ : syracuseStep 11780777 = 8835583) B8835583
theorem B7853851 : Blo 2177435 7853851 := bstep (se 1 (by rfl) ⟨5890388, by rfl⟩ : syracuseStep 7853851 = 11780777) B11780777
theorem B10471801 : Blo 2177435 10471801 := bstep (se 2 (by rfl) ⟨3926925, by rfl⟩ : syracuseStep 10471801 = 7853851) B7853851
theorem B13962401 : Blo 2177435 13962401 := bstep (se 2 (by rfl) ⟨5235900, by rfl⟩ : syracuseStep 13962401 = 10471801) B10471801
theorem B9308267 : Blo 2177435 9308267 := bstep (se 1 (by rfl) ⟨6981200, by rfl⟩ : syracuseStep 9308267 = 13962401) B13962401
theorem B6205511 : Blo 2177435 6205511 := bstep (se 1 (by rfl) ⟨4654133, by rfl⟩ : syracuseStep 6205511 = 9308267) B9308267
theorem B4137007 : Blo 2177435 4137007 := bstep (se 1 (by rfl) ⟨3102755, by rfl⟩ : syracuseStep 4137007 = 6205511) B6205511
theorem B5516009 : Blo 2177435 5516009 := bstep (se 2 (by rfl) ⟨2068503, by rfl⟩ : syracuseStep 5516009 = 4137007) B4137007
theorem B3677339 : Blo 2177435 3677339 := bstep (se 1 (by rfl) ⟨2758004, by rfl⟩ : syracuseStep 3677339 = 5516009) B5516009
theorem B2451559 : Blo 2177435 2451559 := bstep (se 1 (by rfl) ⟨1838669, by rfl⟩ : syracuseStep 2451559 = 3677339) B3677339
theorem B3268745 : Blo 2177435 3268745 := bstep (se 2 (by rfl) ⟨1225779, by rfl⟩ : syracuseStep 3268745 = 2451559) B2451559
theorem B2179163 : Blo 2177435 2179163 := bstep (se 1 (by rfl) ⟨1634372, by rfl⟩ : syracuseStep 2179163 = 3268745) B3268745
theorem B11032037 : Blo 2177435 11032037 := bbase (se 4 (by rfl) ⟨1034253, by rfl⟩ : syracuseStep 11032037 = 2068507) (by norm_num)
theorem B7354691 : Blo 2177435 7354691 := bstep (se 1 (by rfl) ⟨5516018, by rfl⟩ : syracuseStep 7354691 = 11032037) B11032037
theorem B4903127 : Blo 2177435 4903127 := bstep (se 1 (by rfl) ⟨3677345, by rfl⟩ : syracuseStep 4903127 = 7354691) B7354691
theorem B3268751 : Blo 2177435 3268751 := bstep (se 1 (by rfl) ⟨2451563, by rfl⟩ : syracuseStep 3268751 = 4903127) B4903127
theorem B2179167 : Blo 2177435 2179167 := bstep (se 1 (by rfl) ⟨1634375, by rfl⟩ : syracuseStep 2179167 = 3268751) B3268751
theorem B3268757 : Blo 2177435 3268757 := bbase (se 6 (by rfl) ⟨76611, by rfl⟩ : syracuseStep 3268757 = 153223) (by norm_num)
theorem B2179171 : Blo 2177435 2179171 := bstep (se 1 (by rfl) ⟨1634378, by rfl⟩ : syracuseStep 2179171 = 3268757) B3268757
theorem B5890421 : Blo 2177435 5890421 := bbase (se 5 (by rfl) ⟨276113, by rfl⟩ : syracuseStep 5890421 = 552227) (by norm_num)
theorem B3926947 : Blo 2177435 3926947 := bstep (se 1 (by rfl) ⟨2945210, by rfl⟩ : syracuseStep 3926947 = 5890421) B5890421
theorem B5235929 : Blo 2177435 5235929 := bstep (se 2 (by rfl) ⟨1963473, by rfl⟩ : syracuseStep 5235929 = 3926947) B3926947
theorem B3490619 : Blo 2177435 3490619 := bstep (se 1 (by rfl) ⟨2617964, by rfl⟩ : syracuseStep 3490619 = 5235929) B5235929
theorem B9308317 : Blo 2177435 9308317 := bstep (se 3 (by rfl) ⟨1745309, by rfl⟩ : syracuseStep 9308317 = 3490619) B3490619
theorem B12411089 : Blo 2177435 12411089 := bstep (se 2 (by rfl) ⟨4654158, by rfl⟩ : syracuseStep 12411089 = 9308317) B9308317
theorem B8274059 : Blo 2177435 8274059 := bstep (se 1 (by rfl) ⟨6205544, by rfl⟩ : syracuseStep 8274059 = 12411089) B12411089
theorem B5516039 : Blo 2177435 5516039 := bstep (se 1 (by rfl) ⟨4137029, by rfl⟩ : syracuseStep 5516039 = 8274059) B8274059
theorem B3677359 : Blo 2177435 3677359 := bstep (se 1 (by rfl) ⟨2758019, by rfl⟩ : syracuseStep 3677359 = 5516039) B5516039
theorem B4903145 : Blo 2177435 4903145 := bstep (se 2 (by rfl) ⟨1838679, by rfl⟩ : syracuseStep 4903145 = 3677359) B3677359
theorem B3268763 : Blo 2177435 3268763 := bstep (se 1 (by rfl) ⟨2451572, by rfl⟩ : syracuseStep 3268763 = 4903145) B4903145
theorem B2179175 : Blo 2177435 2179175 := bstep (se 1 (by rfl) ⟨1634381, by rfl⟩ : syracuseStep 2179175 = 3268763) B3268763
theorem B2451577 : Blo 2177435 2451577 := bbase (se 2 (by rfl) ⟨919341, by rfl⟩ : syracuseStep 2451577 = 1838683) (by norm_num)
theorem B3268769 : Blo 2177435 3268769 := bstep (se 2 (by rfl) ⟨1225788, by rfl⟩ : syracuseStep 3268769 = 2451577) B2451577
theorem B2179179 : Blo 2177435 2179179 := bstep (se 1 (by rfl) ⟨1634384, by rfl⟩ : syracuseStep 2179179 = 3268769) B3268769
theorem B53013973 : Blo 2177435 53013973 := bbase (se 7 (by rfl) ⟨621257, by rfl⟩ : syracuseStep 53013973 = 1242515) (by norm_num)
theorem B70685297 : Blo 2177435 70685297 := bstep (se 2 (by rfl) ⟨26506986, by rfl⟩ : syracuseStep 70685297 = 53013973) B53013973
theorem B47123531 : Blo 2177435 47123531 := bstep (se 1 (by rfl) ⟨35342648, by rfl⟩ : syracuseStep 47123531 = 70685297) B70685297
theorem B31415687 : Blo 2177435 31415687 := bstep (se 1 (by rfl) ⟨23561765, by rfl⟩ : syracuseStep 31415687 = 47123531) B47123531
theorem B20943791 : Blo 2177435 20943791 := bstep (se 1 (by rfl) ⟨15707843, by rfl⟩ : syracuseStep 20943791 = 31415687) B31415687
theorem B13962527 : Blo 2177435 13962527 := bstep (se 1 (by rfl) ⟨10471895, by rfl⟩ : syracuseStep 13962527 = 20943791) B20943791
theorem B9308351 : Blo 2177435 9308351 := bstep (se 1 (by rfl) ⟨6981263, by rfl⟩ : syracuseStep 9308351 = 13962527) B13962527
theorem B6205567 : Blo 2177435 6205567 := bstep (se 1 (by rfl) ⟨4654175, by rfl⟩ : syracuseStep 6205567 = 9308351) B9308351
theorem B8274089 : Blo 2177435 8274089 := bstep (se 2 (by rfl) ⟨3102783, by rfl⟩ : syracuseStep 8274089 = 6205567) B6205567
theorem B5516059 : Blo 2177435 5516059 := bstep (se 1 (by rfl) ⟨4137044, by rfl⟩ : syracuseStep 5516059 = 8274089) B8274089
theorem B7354745 : Blo 2177435 7354745 := bstep (se 2 (by rfl) ⟨2758029, by rfl⟩ : syracuseStep 7354745 = 5516059) B5516059
theorem B4903163 : Blo 2177435 4903163 := bstep (se 1 (by rfl) ⟨3677372, by rfl⟩ : syracuseStep 4903163 = 7354745) B7354745
theorem B3268775 : Blo 2177435 3268775 := bstep (se 1 (by rfl) ⟨2451581, by rfl⟩ : syracuseStep 3268775 = 4903163) B4903163
theorem B2179183 : Blo 2177435 2179183 := bstep (se 1 (by rfl) ⟨1634387, by rfl⟩ : syracuseStep 2179183 = 3268775) B3268775
theorem B3268781 : Blo 2177435 3268781 := bbase (se 3 (by rfl) ⟨612896, by rfl⟩ : syracuseStep 3268781 = 1225793) (by norm_num)
theorem B2179187 : Blo 2177435 2179187 := bstep (se 1 (by rfl) ⟨1634390, by rfl⟩ : syracuseStep 2179187 = 3268781) B3268781
theorem B4903181 : Blo 2177435 4903181 := bbase (se 3 (by rfl) ⟨919346, by rfl⟩ : syracuseStep 4903181 = 1838693) (by norm_num)
theorem B3268787 : Blo 2177435 3268787 := bstep (se 1 (by rfl) ⟨2451590, by rfl⟩ : syracuseStep 3268787 = 4903181) B4903181
theorem B2179191 : Blo 2177435 2179191 := bstep (se 1 (by rfl) ⟨1634393, by rfl⟩ : syracuseStep 2179191 = 3268787) B3268787
theorem B2758045 : Blo 2177435 2758045 := bbase (se 3 (by rfl) ⟨517133, by rfl⟩ : syracuseStep 2758045 = 1034267) (by norm_num)
theorem B3677393 : Blo 2177435 3677393 := bstep (se 2 (by rfl) ⟨1379022, by rfl⟩ : syracuseStep 3677393 = 2758045) B2758045
theorem B2451595 : Blo 2177435 2451595 := bstep (se 1 (by rfl) ⟨1838696, by rfl⟩ : syracuseStep 2451595 = 3677393) B3677393
theorem B3268793 : Blo 2177435 3268793 := bstep (se 2 (by rfl) ⟨1225797, by rfl⟩ : syracuseStep 3268793 = 2451595) B2451595
theorem B2179195 : Blo 2177435 2179195 := bstep (se 1 (by rfl) ⟨1634396, by rfl⟩ : syracuseStep 2179195 = 3268793) B3268793
theorem B2617993 : Blo 2177435 2617993 := bbase (se 2 (by rfl) ⟨981747, by rfl⟩ : syracuseStep 2617993 = 1963495) (by norm_num)
theorem B3490657 : Blo 2177435 3490657 := bstep (se 2 (by rfl) ⟨1308996, by rfl⟩ : syracuseStep 3490657 = 2617993) B2617993
theorem B18616837 : Blo 2177435 18616837 := bstep (se 4 (by rfl) ⟨1745328, by rfl⟩ : syracuseStep 18616837 = 3490657) B3490657
theorem B24822449 : Blo 2177435 24822449 := bstep (se 2 (by rfl) ⟨9308418, by rfl⟩ : syracuseStep 24822449 = 18616837) B18616837
theorem B16548299 : Blo 2177435 16548299 := bstep (se 1 (by rfl) ⟨12411224, by rfl⟩ : syracuseStep 16548299 = 24822449) B24822449
theorem B11032199 : Blo 2177435 11032199 := bstep (se 1 (by rfl) ⟨8274149, by rfl⟩ : syracuseStep 11032199 = 16548299) B16548299
theorem B7354799 : Blo 2177435 7354799 := bstep (se 1 (by rfl) ⟨5516099, by rfl⟩ : syracuseStep 7354799 = 11032199) B11032199
theorem B4903199 : Blo 2177435 4903199 := bstep (se 1 (by rfl) ⟨3677399, by rfl⟩ : syracuseStep 4903199 = 7354799) B7354799
theorem B3268799 : Blo 2177435 3268799 := bstep (se 1 (by rfl) ⟨2451599, by rfl⟩ : syracuseStep 3268799 = 4903199) B4903199
theorem B2179199 : Blo 2177435 2179199 := bstep (se 1 (by rfl) ⟨1634399, by rfl⟩ : syracuseStep 2179199 = 3268799) B3268799
theorem B3268805 : Blo 2177435 3268805 := bbase (se 4 (by rfl) ⟨306450, by rfl⟩ : syracuseStep 3268805 = 612901) (by norm_num)
theorem B2179203 : Blo 2177435 2179203 := bstep (se 1 (by rfl) ⟨1634402, by rfl⟩ : syracuseStep 2179203 = 3268805) B3268805
theorem B3677413 : Blo 2177435 3677413 := bbase (se 4 (by rfl) ⟨344757, by rfl⟩ : syracuseStep 3677413 = 689515) (by norm_num)
theorem B4903217 : Blo 2177435 4903217 := bstep (se 2 (by rfl) ⟨1838706, by rfl⟩ : syracuseStep 4903217 = 3677413) B3677413
theorem B3268811 : Blo 2177435 3268811 := bstep (se 1 (by rfl) ⟨2451608, by rfl⟩ : syracuseStep 3268811 = 4903217) B4903217
theorem B2179207 : Blo 2177435 2179207 := bstep (se 1 (by rfl) ⟨1634405, by rfl⟩ : syracuseStep 2179207 = 3268811) B3268811
theorem B2451613 : Blo 2177435 2451613 := bbase (se 3 (by rfl) ⟨459677, by rfl⟩ : syracuseStep 2451613 = 919355) (by norm_num)
theorem B3268817 : Blo 2177435 3268817 := bstep (se 2 (by rfl) ⟨1225806, by rfl⟩ : syracuseStep 3268817 = 2451613) B2451613
theorem B2179211 : Blo 2177435 2179211 := bstep (se 1 (by rfl) ⟨1634408, by rfl⟩ : syracuseStep 2179211 = 3268817) B3268817
theorem B7354853 : Blo 2177435 7354853 := bbase (se 4 (by rfl) ⟨689517, by rfl⟩ : syracuseStep 7354853 = 1379035) (by norm_num)
theorem B4903235 : Blo 2177435 4903235 := bstep (se 1 (by rfl) ⟨3677426, by rfl⟩ : syracuseStep 4903235 = 7354853) B7354853
theorem B3268823 : Blo 2177435 3268823 := bstep (se 1 (by rfl) ⟨2451617, by rfl⟩ : syracuseStep 3268823 = 4903235) B4903235
theorem B2179215 : Blo 2177435 2179215 := bstep (se 1 (by rfl) ⟨1634411, by rfl⟩ : syracuseStep 2179215 = 3268823) B3268823
theorem B3268829 : Blo 2177435 3268829 := bbase (se 3 (by rfl) ⟨612905, by rfl⟩ : syracuseStep 3268829 = 1225811) (by norm_num)
theorem B2179219 : Blo 2177435 2179219 := bstep (se 1 (by rfl) ⟨1634414, by rfl⟩ : syracuseStep 2179219 = 3268829) B3268829
theorem B4903253 : Blo 2177435 4903253 := bbase (se 10 (by rfl) ⟨7182, by rfl⟩ : syracuseStep 4903253 = 14365) (by norm_num)
theorem B3268835 : Blo 2177435 3268835 := bstep (se 1 (by rfl) ⟨2451626, by rfl⟩ : syracuseStep 3268835 = 4903253) B4903253
theorem B2179223 : Blo 2177435 2179223 := bstep (se 1 (by rfl) ⟨1634417, by rfl⟩ : syracuseStep 2179223 = 3268835) B3268835
theorem B2208961 : Blo 2177435 2208961 := bbase (se 2 (by rfl) ⟨828360, by rfl⟩ : syracuseStep 2208961 = 1656721) (by norm_num)
theorem B11781125 : Blo 2177435 11781125 := bstep (se 4 (by rfl) ⟨1104480, by rfl⟩ : syracuseStep 11781125 = 2208961) B2208961
theorem B7854083 : Blo 2177435 7854083 := bstep (se 1 (by rfl) ⟨5890562, by rfl⟩ : syracuseStep 7854083 = 11781125) B11781125
theorem B5236055 : Blo 2177435 5236055 := bstep (se 1 (by rfl) ⟨3927041, by rfl⟩ : syracuseStep 5236055 = 7854083) B7854083
theorem B3490703 : Blo 2177435 3490703 := bstep (se 1 (by rfl) ⟨2618027, by rfl⟩ : syracuseStep 3490703 = 5236055) B5236055
theorem B2327135 : Blo 2177435 2327135 := bstep (se 1 (by rfl) ⟨1745351, by rfl⟩ : syracuseStep 2327135 = 3490703) B3490703
theorem B6205693 : Blo 2177435 6205693 := bstep (se 3 (by rfl) ⟨1163567, by rfl⟩ : syracuseStep 6205693 = 2327135) B2327135
theorem B8274257 : Blo 2177435 8274257 := bstep (se 2 (by rfl) ⟨3102846, by rfl⟩ : syracuseStep 8274257 = 6205693) B6205693
theorem B5516171 : Blo 2177435 5516171 := bstep (se 1 (by rfl) ⟨4137128, by rfl⟩ : syracuseStep 5516171 = 8274257) B8274257
theorem B3677447 : Blo 2177435 3677447 := bstep (se 1 (by rfl) ⟨2758085, by rfl⟩ : syracuseStep 3677447 = 5516171) B5516171
theorem B2451631 : Blo 2177435 2451631 := bstep (se 1 (by rfl) ⟨1838723, by rfl⟩ : syracuseStep 2451631 = 3677447) B3677447
theorem B3268841 : Blo 2177435 3268841 := bstep (se 2 (by rfl) ⟨1225815, by rfl⟩ : syracuseStep 3268841 = 2451631) B2451631
theorem B2179227 : Blo 2177435 2179227 := bstep (se 1 (by rfl) ⟨1634420, by rfl⟩ : syracuseStep 2179227 = 3268841) B3268841
theorem B2485085 : Blo 2177435 2485085 := bbase (se 3 (by rfl) ⟨465953, by rfl⟩ : syracuseStep 2485085 = 931907) (by norm_num)
theorem B6626893 : Blo 2177435 6626893 := bstep (se 3 (by rfl) ⟨1242542, by rfl⟩ : syracuseStep 6626893 = 2485085) B2485085
theorem B8835857 : Blo 2177435 8835857 := bstep (se 2 (by rfl) ⟨3313446, by rfl⟩ : syracuseStep 8835857 = 6626893) B6626893
theorem B5890571 : Blo 2177435 5890571 := bstep (se 1 (by rfl) ⟨4417928, by rfl⟩ : syracuseStep 5890571 = 8835857) B8835857
theorem B3927047 : Blo 2177435 3927047 := bstep (se 1 (by rfl) ⟨2945285, by rfl⟩ : syracuseStep 3927047 = 5890571) B5890571
theorem B41888501 : Blo 2177435 41888501 := bstep (se 5 (by rfl) ⟨1963523, by rfl⟩ : syracuseStep 41888501 = 3927047) B3927047
theorem B27925667 : Blo 2177435 27925667 := bstep (se 1 (by rfl) ⟨20944250, by rfl⟩ : syracuseStep 27925667 = 41888501) B41888501
theorem B18617111 : Blo 2177435 18617111 := bstep (se 1 (by rfl) ⟨13962833, by rfl⟩ : syracuseStep 18617111 = 27925667) B27925667
theorem B12411407 : Blo 2177435 12411407 := bstep (se 1 (by rfl) ⟨9308555, by rfl⟩ : syracuseStep 12411407 = 18617111) B18617111
theorem B8274271 : Blo 2177435 8274271 := bstep (se 1 (by rfl) ⟨6205703, by rfl⟩ : syracuseStep 8274271 = 12411407) B12411407
theorem B11032361 : Blo 2177435 11032361 := bstep (se 2 (by rfl) ⟨4137135, by rfl⟩ : syracuseStep 11032361 = 8274271) B8274271
theorem B7354907 : Blo 2177435 7354907 := bstep (se 1 (by rfl) ⟨5516180, by rfl⟩ : syracuseStep 7354907 = 11032361) B11032361
theorem B4903271 : Blo 2177435 4903271 := bstep (se 1 (by rfl) ⟨3677453, by rfl⟩ : syracuseStep 4903271 = 7354907) B7354907
theorem B3268847 : Blo 2177435 3268847 := bstep (se 1 (by rfl) ⟨2451635, by rfl⟩ : syracuseStep 3268847 = 4903271) B4903271
theorem B2179231 : Blo 2177435 2179231 := bstep (se 1 (by rfl) ⟨1634423, by rfl⟩ : syracuseStep 2179231 = 3268847) B3268847
theorem B3268853 : Blo 2177435 3268853 := bbase (se 5 (by rfl) ⟨153227, by rfl⟩ : syracuseStep 3268853 = 306455) (by norm_num)
theorem B2179235 : Blo 2177435 2179235 := bstep (se 1 (by rfl) ⟨1634426, by rfl⟩ : syracuseStep 2179235 = 3268853) B3268853
theorem B4970189 : Blo 2177435 4970189 := bbase (se 3 (by rfl) ⟨931910, by rfl⟩ : syracuseStep 4970189 = 1863821) (by norm_num)
theorem B3313459 : Blo 2177435 3313459 := bstep (se 1 (by rfl) ⟨2485094, by rfl⟩ : syracuseStep 3313459 = 4970189) B4970189
theorem B4417945 : Blo 2177435 4417945 := bstep (se 2 (by rfl) ⟨1656729, by rfl⟩ : syracuseStep 4417945 = 3313459) B3313459
theorem B23562373 : Blo 2177435 23562373 := bstep (se 4 (by rfl) ⟨2208972, by rfl⟩ : syracuseStep 23562373 = 4417945) B4417945
theorem B31416497 : Blo 2177435 31416497 := bstep (se 2 (by rfl) ⟨11781186, by rfl⟩ : syracuseStep 31416497 = 23562373) B23562373
theorem B20944331 : Blo 2177435 20944331 := bstep (se 1 (by rfl) ⟨15708248, by rfl⟩ : syracuseStep 20944331 = 31416497) B31416497
theorem B13962887 : Blo 2177435 13962887 := bstep (se 1 (by rfl) ⟨10472165, by rfl⟩ : syracuseStep 13962887 = 20944331) B20944331
theorem B9308591 : Blo 2177435 9308591 := bstep (se 1 (by rfl) ⟨6981443, by rfl⟩ : syracuseStep 9308591 = 13962887) B13962887
theorem B6205727 : Blo 2177435 6205727 := bstep (se 1 (by rfl) ⟨4654295, by rfl⟩ : syracuseStep 6205727 = 9308591) B9308591
theorem B4137151 : Blo 2177435 4137151 := bstep (se 1 (by rfl) ⟨3102863, by rfl⟩ : syracuseStep 4137151 = 6205727) B6205727
theorem B5516201 : Blo 2177435 5516201 := bstep (se 2 (by rfl) ⟨2068575, by rfl⟩ : syracuseStep 5516201 = 4137151) B4137151
theorem B3677467 : Blo 2177435 3677467 := bstep (se 1 (by rfl) ⟨2758100, by rfl⟩ : syracuseStep 3677467 = 5516201) B5516201
theorem B4903289 : Blo 2177435 4903289 := bstep (se 2 (by rfl) ⟨1838733, by rfl⟩ : syracuseStep 4903289 = 3677467) B3677467
theorem B3268859 : Blo 2177435 3268859 := bstep (se 1 (by rfl) ⟨2451644, by rfl⟩ : syracuseStep 3268859 = 4903289) B4903289
theorem B2179239 : Blo 2177435 2179239 := bstep (se 1 (by rfl) ⟨1634429, by rfl⟩ : syracuseStep 2179239 = 3268859) B3268859
theorem B2451649 : Blo 2177435 2451649 := bbase (se 2 (by rfl) ⟨919368, by rfl⟩ : syracuseStep 2451649 = 1838737) (by norm_num)
theorem B3268865 : Blo 2177435 3268865 := bstep (se 2 (by rfl) ⟨1225824, by rfl⟩ : syracuseStep 3268865 = 2451649) B2451649
theorem B2179243 : Blo 2177435 2179243 := bstep (se 1 (by rfl) ⟨1634432, by rfl⟩ : syracuseStep 2179243 = 3268865) B3268865
theorem B5516221 : Blo 2177435 5516221 := bbase (se 3 (by rfl) ⟨1034291, by rfl⟩ : syracuseStep 5516221 = 2068583) (by norm_num)
theorem B7354961 : Blo 2177435 7354961 := bstep (se 2 (by rfl) ⟨2758110, by rfl⟩ : syracuseStep 7354961 = 5516221) B5516221
theorem B4903307 : Blo 2177435 4903307 := bstep (se 1 (by rfl) ⟨3677480, by rfl⟩ : syracuseStep 4903307 = 7354961) B7354961
theorem B3268871 : Blo 2177435 3268871 := bstep (se 1 (by rfl) ⟨2451653, by rfl⟩ : syracuseStep 3268871 = 4903307) B4903307
theorem B2179247 : Blo 2177435 2179247 := bstep (se 1 (by rfl) ⟨1634435, by rfl⟩ : syracuseStep 2179247 = 3268871) B3268871
theorem B3268877 : Blo 2177435 3268877 := bbase (se 3 (by rfl) ⟨612914, by rfl⟩ : syracuseStep 3268877 = 1225829) (by norm_num)
theorem B2179251 : Blo 2177435 2179251 := bstep (se 1 (by rfl) ⟨1634438, by rfl⟩ : syracuseStep 2179251 = 3268877) B3268877
theorem B4903325 : Blo 2177435 4903325 := bbase (se 3 (by rfl) ⟨919373, by rfl⟩ : syracuseStep 4903325 = 1838747) (by norm_num)
theorem B3268883 : Blo 2177435 3268883 := bstep (se 1 (by rfl) ⟨2451662, by rfl⟩ : syracuseStep 3268883 = 4903325) B4903325
theorem B2179255 : Blo 2177435 2179255 := bstep (se 1 (by rfl) ⟨1634441, by rfl⟩ : syracuseStep 2179255 = 3268883) B3268883
theorem B3677501 : Blo 2177435 3677501 := bbase (se 3 (by rfl) ⟨689531, by rfl⟩ : syracuseStep 3677501 = 1379063) (by norm_num)
theorem B2451667 : Blo 2177435 2451667 := bstep (se 1 (by rfl) ⟨1838750, by rfl⟩ : syracuseStep 2451667 = 3677501) B3677501
theorem B3268889 : Blo 2177435 3268889 := bstep (se 2 (by rfl) ⟨1225833, by rfl⟩ : syracuseStep 3268889 = 2451667) B2451667
theorem B2179259 : Blo 2177435 2179259 := bstep (se 1 (by rfl) ⟨1634444, by rfl⟩ : syracuseStep 2179259 = 3268889) B3268889
theorem B2327173 : Blo 2177435 2327173 := bbase (se 4 (by rfl) ⟨218172, by rfl⟩ : syracuseStep 2327173 = 436345) (by norm_num)
theorem B12411589 : Blo 2177435 12411589 := bstep (se 4 (by rfl) ⟨1163586, by rfl⟩ : syracuseStep 12411589 = 2327173) B2327173
theorem B16548785 : Blo 2177435 16548785 := bstep (se 2 (by rfl) ⟨6205794, by rfl⟩ : syracuseStep 16548785 = 12411589) B12411589
theorem B11032523 : Blo 2177435 11032523 := bstep (se 1 (by rfl) ⟨8274392, by rfl⟩ : syracuseStep 11032523 = 16548785) B16548785
theorem B7355015 : Blo 2177435 7355015 := bstep (se 1 (by rfl) ⟨5516261, by rfl⟩ : syracuseStep 7355015 = 11032523) B11032523
theorem B4903343 : Blo 2177435 4903343 := bstep (se 1 (by rfl) ⟨3677507, by rfl⟩ : syracuseStep 4903343 = 7355015) B7355015
theorem B3268895 : Blo 2177435 3268895 := bstep (se 1 (by rfl) ⟨2451671, by rfl⟩ : syracuseStep 3268895 = 4903343) B4903343
theorem B2179263 : Blo 2177435 2179263 := bstep (se 1 (by rfl) ⟨1634447, by rfl⟩ : syracuseStep 2179263 = 3268895) B3268895
theorem B3268901 : Blo 2177435 3268901 := bbase (se 4 (by rfl) ⟨306459, by rfl⟩ : syracuseStep 3268901 = 612919) (by norm_num)
theorem B2179267 : Blo 2177435 2179267 := bstep (se 1 (by rfl) ⟨1634450, by rfl⟩ : syracuseStep 2179267 = 3268901) B3268901
theorem B2758141 : Blo 2177435 2758141 := bbase (se 3 (by rfl) ⟨517151, by rfl⟩ : syracuseStep 2758141 = 1034303) (by norm_num)
theorem B3677521 : Blo 2177435 3677521 := bstep (se 2 (by rfl) ⟨1379070, by rfl⟩ : syracuseStep 3677521 = 2758141) B2758141
theorem B4903361 : Blo 2177435 4903361 := bstep (se 2 (by rfl) ⟨1838760, by rfl⟩ : syracuseStep 4903361 = 3677521) B3677521
theorem B3268907 : Blo 2177435 3268907 := bstep (se 1 (by rfl) ⟨2451680, by rfl⟩ : syracuseStep 3268907 = 4903361) B4903361
theorem B2179271 : Blo 2177435 2179271 := bstep (se 1 (by rfl) ⟨1634453, by rfl⟩ : syracuseStep 2179271 = 3268907) B3268907
theorem B2451685 : Blo 2177435 2451685 := bbase (se 4 (by rfl) ⟨229845, by rfl⟩ : syracuseStep 2451685 = 459691) (by norm_num)
theorem B3268913 : Blo 2177435 3268913 := bstep (se 2 (by rfl) ⟨1225842, by rfl⟩ : syracuseStep 3268913 = 2451685) B2451685
theorem B2179275 : Blo 2177435 2179275 := bstep (se 1 (by rfl) ⟨1634456, by rfl⟩ : syracuseStep 2179275 = 3268913) B3268913
theorem B4654381 : Blo 2177435 4654381 := bbase (se 3 (by rfl) ⟨872696, by rfl⟩ : syracuseStep 4654381 = 1745393) (by norm_num)
theorem B6205841 : Blo 2177435 6205841 := bstep (se 2 (by rfl) ⟨2327190, by rfl⟩ : syracuseStep 6205841 = 4654381) B4654381
theorem B4137227 : Blo 2177435 4137227 := bstep (se 1 (by rfl) ⟨3102920, by rfl⟩ : syracuseStep 4137227 = 6205841) B6205841
theorem B2758151 : Blo 2177435 2758151 := bstep (se 1 (by rfl) ⟨2068613, by rfl⟩ : syracuseStep 2758151 = 4137227) B4137227
theorem B7355069 : Blo 2177435 7355069 := bstep (se 3 (by rfl) ⟨1379075, by rfl⟩ : syracuseStep 7355069 = 2758151) B2758151
theorem B4903379 : Blo 2177435 4903379 := bstep (se 1 (by rfl) ⟨3677534, by rfl⟩ : syracuseStep 4903379 = 7355069) B7355069
theorem B3268919 : Blo 2177435 3268919 := bstep (se 1 (by rfl) ⟨2451689, by rfl⟩ : syracuseStep 3268919 = 4903379) B4903379
theorem B2179279 : Blo 2177435 2179279 := bstep (se 1 (by rfl) ⟨1634459, by rfl⟩ : syracuseStep 2179279 = 3268919) B3268919
theorem B3268925 : Blo 2177435 3268925 := bbase (se 3 (by rfl) ⟨612923, by rfl⟩ : syracuseStep 3268925 = 1225847) (by norm_num)
theorem B2179283 : Blo 2177435 2179283 := bstep (se 1 (by rfl) ⟨1634462, by rfl⟩ : syracuseStep 2179283 = 3268925) B3268925
theorem B4903397 : Blo 2177435 4903397 := bbase (se 4 (by rfl) ⟨459693, by rfl⟩ : syracuseStep 4903397 = 919387) (by norm_num)
theorem B3268931 : Blo 2177435 3268931 := bstep (se 1 (by rfl) ⟨2451698, by rfl⟩ : syracuseStep 3268931 = 4903397) B4903397
theorem B2179287 : Blo 2177435 2179287 := bstep (se 1 (by rfl) ⟨1634465, by rfl⟩ : syracuseStep 2179287 = 3268931) B3268931
theorem B5516333 : Blo 2177435 5516333 := bbase (se 3 (by rfl) ⟨1034312, by rfl⟩ : syracuseStep 5516333 = 2068625) (by norm_num)
theorem B3677555 : Blo 2177435 3677555 := bstep (se 1 (by rfl) ⟨2758166, by rfl⟩ : syracuseStep 3677555 = 5516333) B5516333
theorem B2451703 : Blo 2177435 2451703 := bstep (se 1 (by rfl) ⟨1838777, by rfl⟩ : syracuseStep 2451703 = 3677555) B3677555
theorem B3268937 : Blo 2177435 3268937 := bstep (se 2 (by rfl) ⟨1225851, by rfl⟩ : syracuseStep 3268937 = 2451703) B2451703
theorem B2179291 : Blo 2177435 2179291 := bstep (se 1 (by rfl) ⟨1634468, by rfl⟩ : syracuseStep 2179291 = 3268937) B3268937
theorem B4970317 : Blo 2177435 4970317 := bbase (se 3 (by rfl) ⟨931934, by rfl⟩ : syracuseStep 4970317 = 1863869) (by norm_num)
theorem B6627089 : Blo 2177435 6627089 := bstep (se 2 (by rfl) ⟨2485158, by rfl⟩ : syracuseStep 6627089 = 4970317) B4970317
theorem B4418059 : Blo 2177435 4418059 := bstep (se 1 (by rfl) ⟨3313544, by rfl⟩ : syracuseStep 4418059 = 6627089) B6627089
theorem B5890745 : Blo 2177435 5890745 := bstep (se 2 (by rfl) ⟨2209029, by rfl⟩ : syracuseStep 5890745 = 4418059) B4418059
theorem B15708653 : Blo 2177435 15708653 := bstep (se 3 (by rfl) ⟨2945372, by rfl⟩ : syracuseStep 15708653 = 5890745) B5890745
theorem B10472435 : Blo 2177435 10472435 := bstep (se 1 (by rfl) ⟨7854326, by rfl⟩ : syracuseStep 10472435 = 15708653) B15708653
theorem B6981623 : Blo 2177435 6981623 := bstep (se 1 (by rfl) ⟨5236217, by rfl⟩ : syracuseStep 6981623 = 10472435) B10472435
theorem B4654415 : Blo 2177435 4654415 := bstep (se 1 (by rfl) ⟨3490811, by rfl⟩ : syracuseStep 4654415 = 6981623) B6981623
theorem B3102943 : Blo 2177435 3102943 := bstep (se 1 (by rfl) ⟨2327207, by rfl⟩ : syracuseStep 3102943 = 4654415) B4654415
theorem B4137257 : Blo 2177435 4137257 := bstep (se 2 (by rfl) ⟨1551471, by rfl⟩ : syracuseStep 4137257 = 3102943) B3102943
theorem B11032685 : Blo 2177435 11032685 := bstep (se 3 (by rfl) ⟨2068628, by rfl⟩ : syracuseStep 11032685 = 4137257) B4137257
theorem B7355123 : Blo 2177435 7355123 := bstep (se 1 (by rfl) ⟨5516342, by rfl⟩ : syracuseStep 7355123 = 11032685) B11032685
theorem B4903415 : Blo 2177435 4903415 := bstep (se 1 (by rfl) ⟨3677561, by rfl⟩ : syracuseStep 4903415 = 7355123) B7355123
theorem B3268943 : Blo 2177435 3268943 := bstep (se 1 (by rfl) ⟨2451707, by rfl⟩ : syracuseStep 3268943 = 4903415) B4903415
theorem B2179295 : Blo 2177435 2179295 := bstep (se 1 (by rfl) ⟨1634471, by rfl⟩ : syracuseStep 2179295 = 3268943) B3268943
theorem B3268949 : Blo 2177435 3268949 := bbase (se 10 (by rfl) ⟨4788, by rfl⟩ : syracuseStep 3268949 = 9577) (by norm_num)
theorem B2179299 : Blo 2177435 2179299 := bstep (se 1 (by rfl) ⟨1634474, by rfl⟩ : syracuseStep 2179299 = 3268949) B3268949
theorem B6205909 : Blo 2177435 6205909 := bbase (se 7 (by rfl) ⟨72725, by rfl⟩ : syracuseStep 6205909 = 145451) (by norm_num)
theorem B8274545 : Blo 2177435 8274545 := bstep (se 2 (by rfl) ⟨3102954, by rfl⟩ : syracuseStep 8274545 = 6205909) B6205909
theorem B5516363 : Blo 2177435 5516363 := bstep (se 1 (by rfl) ⟨4137272, by rfl⟩ : syracuseStep 5516363 = 8274545) B8274545
theorem B3677575 : Blo 2177435 3677575 := bstep (se 1 (by rfl) ⟨2758181, by rfl⟩ : syracuseStep 3677575 = 5516363) B5516363
theorem B4903433 : Blo 2177435 4903433 := bstep (se 2 (by rfl) ⟨1838787, by rfl⟩ : syracuseStep 4903433 = 3677575) B3677575
theorem B3268955 : Blo 2177435 3268955 := bstep (se 1 (by rfl) ⟨2451716, by rfl⟩ : syracuseStep 3268955 = 4903433) B4903433
theorem B2179303 : Blo 2177435 2179303 := bstep (se 1 (by rfl) ⟨1634477, by rfl⟩ : syracuseStep 2179303 = 3268955) B3268955
theorem B2451721 : Blo 2177435 2451721 := bbase (se 2 (by rfl) ⟨919395, by rfl⟩ : syracuseStep 2451721 = 1838791) (by norm_num)
theorem B3268961 : Blo 2177435 3268961 := bstep (se 2 (by rfl) ⟨1225860, by rfl⟩ : syracuseStep 3268961 = 2451721) B2451721
theorem B2179307 : Blo 2177435 2179307 := bstep (se 1 (by rfl) ⟨1634480, by rfl⟩ : syracuseStep 2179307 = 3268961) B3268961
theorem B3980773 : Blo 2177435 3980773 := bbase (se 4 (by rfl) ⟨373197, by rfl⟩ : syracuseStep 3980773 = 746395) (by norm_num)
theorem B5307697 : Blo 2177435 5307697 := bstep (se 2 (by rfl) ⟨1990386, by rfl⟩ : syracuseStep 5307697 = 3980773) B3980773
theorem B7076929 : Blo 2177435 7076929 := bstep (se 2 (by rfl) ⟨2653848, by rfl⟩ : syracuseStep 7076929 = 5307697) B5307697
theorem B9435905 : Blo 2177435 9435905 := bstep (se 2 (by rfl) ⟨3538464, by rfl⟩ : syracuseStep 9435905 = 7076929) B7076929
theorem B6290603 : Blo 2177435 6290603 := bstep (se 1 (by rfl) ⟨4717952, by rfl⟩ : syracuseStep 6290603 = 9435905) B9435905
theorem B4193735 : Blo 2177435 4193735 := bstep (se 1 (by rfl) ⟨3145301, by rfl⟩ : syracuseStep 4193735 = 6290603) B6290603
theorem B11183293 : Blo 2177435 11183293 := bstep (se 3 (by rfl) ⟨2096867, by rfl⟩ : syracuseStep 11183293 = 4193735) B4193735
theorem B14911057 : Blo 2177435 14911057 := bstep (se 2 (by rfl) ⟨5591646, by rfl⟩ : syracuseStep 14911057 = 11183293) B11183293
theorem B19881409 : Blo 2177435 19881409 := bstep (se 2 (by rfl) ⟨7455528, by rfl⟩ : syracuseStep 19881409 = 14911057) B14911057
theorem B26508545 : Blo 2177435 26508545 := bstep (se 2 (by rfl) ⟨9940704, by rfl⟩ : syracuseStep 26508545 = 19881409) B19881409
theorem B17672363 : Blo 2177435 17672363 := bstep (se 1 (by rfl) ⟨13254272, by rfl⟩ : syracuseStep 17672363 = 26508545) B26508545
theorem B11781575 : Blo 2177435 11781575 := bstep (se 1 (by rfl) ⟨8836181, by rfl⟩ : syracuseStep 11781575 = 17672363) B17672363
theorem B7854383 : Blo 2177435 7854383 := bstep (se 1 (by rfl) ⟨5890787, by rfl⟩ : syracuseStep 7854383 = 11781575) B11781575
theorem B5236255 : Blo 2177435 5236255 := bstep (se 1 (by rfl) ⟨3927191, by rfl⟩ : syracuseStep 5236255 = 7854383) B7854383
theorem B27926693 : Blo 2177435 27926693 := bstep (se 4 (by rfl) ⟨2618127, by rfl⟩ : syracuseStep 27926693 = 5236255) B5236255
theorem B18617795 : Blo 2177435 18617795 := bstep (se 1 (by rfl) ⟨13963346, by rfl⟩ : syracuseStep 18617795 = 27926693) B27926693
theorem B12411863 : Blo 2177435 12411863 := bstep (se 1 (by rfl) ⟨9308897, by rfl⟩ : syracuseStep 12411863 = 18617795) B18617795
theorem B8274575 : Blo 2177435 8274575 := bstep (se 1 (by rfl) ⟨6205931, by rfl⟩ : syracuseStep 8274575 = 12411863) B12411863
theorem B5516383 : Blo 2177435 5516383 := bstep (se 1 (by rfl) ⟨4137287, by rfl⟩ : syracuseStep 5516383 = 8274575) B8274575
theorem B7355177 : Blo 2177435 7355177 := bstep (se 2 (by rfl) ⟨2758191, by rfl⟩ : syracuseStep 7355177 = 5516383) B5516383
theorem B4903451 : Blo 2177435 4903451 := bstep (se 1 (by rfl) ⟨3677588, by rfl⟩ : syracuseStep 4903451 = 7355177) B7355177
theorem B3268967 : Blo 2177435 3268967 := bstep (se 1 (by rfl) ⟨2451725, by rfl⟩ : syracuseStep 3268967 = 4903451) B4903451
theorem B2179311 : Blo 2177435 2179311 := bstep (se 1 (by rfl) ⟨1634483, by rfl⟩ : syracuseStep 2179311 = 3268967) B3268967
theorem B3268973 : Blo 2177435 3268973 := bbase (se 3 (by rfl) ⟨612932, by rfl⟩ : syracuseStep 3268973 = 1225865) (by norm_num)
theorem B2179315 : Blo 2177435 2179315 := bstep (se 1 (by rfl) ⟨1634486, by rfl⟩ : syracuseStep 2179315 = 3268973) B3268973
theorem B4903469 : Blo 2177435 4903469 := bbase (se 3 (by rfl) ⟨919400, by rfl⟩ : syracuseStep 4903469 = 1838801) (by norm_num)
theorem B3268979 : Blo 2177435 3268979 := bstep (se 1 (by rfl) ⟨2451734, by rfl⟩ : syracuseStep 3268979 = 4903469) B4903469
theorem B2179319 : Blo 2177435 2179319 := bstep (se 1 (by rfl) ⟨1634489, by rfl⟩ : syracuseStep 2179319 = 3268979) B3268979
theorem B20945141 : Blo 2177435 20945141 := bbase (se 5 (by rfl) ⟨981803, by rfl⟩ : syracuseStep 20945141 = 1963607) (by norm_num)
theorem B13963427 : Blo 2177435 13963427 := bstep (se 1 (by rfl) ⟨10472570, by rfl⟩ : syracuseStep 13963427 = 20945141) B20945141
theorem B9308951 : Blo 2177435 9308951 := bstep (se 1 (by rfl) ⟨6981713, by rfl⟩ : syracuseStep 9308951 = 13963427) B13963427
theorem B6205967 : Blo 2177435 6205967 := bstep (se 1 (by rfl) ⟨4654475, by rfl⟩ : syracuseStep 6205967 = 9308951) B9308951
theorem B4137311 : Blo 2177435 4137311 := bstep (se 1 (by rfl) ⟨3102983, by rfl⟩ : syracuseStep 4137311 = 6205967) B6205967
theorem B2758207 : Blo 2177435 2758207 := bstep (se 1 (by rfl) ⟨2068655, by rfl⟩ : syracuseStep 2758207 = 4137311) B4137311
theorem B3677609 : Blo 2177435 3677609 := bstep (se 2 (by rfl) ⟨1379103, by rfl⟩ : syracuseStep 3677609 = 2758207) B2758207
theorem B2451739 : Blo 2177435 2451739 := bstep (se 1 (by rfl) ⟨1838804, by rfl⟩ : syracuseStep 2451739 = 3677609) B3677609
theorem B3268985 : Blo 2177435 3268985 := bstep (se 2 (by rfl) ⟨1225869, by rfl⟩ : syracuseStep 3268985 = 2451739) B2451739
theorem B2179323 : Blo 2177435 2179323 := bstep (se 1 (by rfl) ⟨1634492, by rfl⟩ : syracuseStep 2179323 = 3268985) B3268985
theorem B37235861 : Blo 2177435 37235861 := bbase (se 6 (by rfl) ⟨872715, by rfl⟩ : syracuseStep 37235861 = 1745431) (by norm_num)
theorem B24823907 : Blo 2177435 24823907 := bstep (se 1 (by rfl) ⟨18617930, by rfl⟩ : syracuseStep 24823907 = 37235861) B37235861
theorem B16549271 : Blo 2177435 16549271 := bstep (se 1 (by rfl) ⟨12411953, by rfl⟩ : syracuseStep 16549271 = 24823907) B24823907
theorem B11032847 : Blo 2177435 11032847 := bstep (se 1 (by rfl) ⟨8274635, by rfl⟩ : syracuseStep 11032847 = 16549271) B16549271
theorem B7355231 : Blo 2177435 7355231 := bstep (se 1 (by rfl) ⟨5516423, by rfl⟩ : syracuseStep 7355231 = 11032847) B11032847
theorem B4903487 : Blo 2177435 4903487 := bstep (se 1 (by rfl) ⟨3677615, by rfl⟩ : syracuseStep 4903487 = 7355231) B7355231
theorem B3268991 : Blo 2177435 3268991 := bstep (se 1 (by rfl) ⟨2451743, by rfl⟩ : syracuseStep 3268991 = 4903487) B4903487
theorem B2179327 : Blo 2177435 2179327 := bstep (se 1 (by rfl) ⟨1634495, by rfl⟩ : syracuseStep 2179327 = 3268991) B3268991
theorem B3268997 : Blo 2177435 3268997 := bbase (se 4 (by rfl) ⟨306468, by rfl⟩ : syracuseStep 3268997 = 612937) (by norm_num)
theorem B2179331 : Blo 2177435 2179331 := bstep (se 1 (by rfl) ⟨1634498, by rfl⟩ : syracuseStep 2179331 = 3268997) B3268997
theorem B3677629 : Blo 2177435 3677629 := bbase (se 3 (by rfl) ⟨689555, by rfl⟩ : syracuseStep 3677629 = 1379111) (by norm_num)
theorem B4903505 : Blo 2177435 4903505 := bstep (se 2 (by rfl) ⟨1838814, by rfl⟩ : syracuseStep 4903505 = 3677629) B3677629
theorem B3269003 : Blo 2177435 3269003 := bstep (se 1 (by rfl) ⟨2451752, by rfl⟩ : syracuseStep 3269003 = 4903505) B4903505
theorem B2179335 : Blo 2177435 2179335 := bstep (se 1 (by rfl) ⟨1634501, by rfl⟩ : syracuseStep 2179335 = 3269003) B3269003
theorem B2451757 : Blo 2177435 2451757 := bbase (se 3 (by rfl) ⟨459704, by rfl⟩ : syracuseStep 2451757 = 919409) (by norm_num)
theorem B3269009 : Blo 2177435 3269009 := bstep (se 2 (by rfl) ⟨1225878, by rfl⟩ : syracuseStep 3269009 = 2451757) B2451757
theorem B2179339 : Blo 2177435 2179339 := bstep (se 1 (by rfl) ⟨1634504, by rfl⟩ : syracuseStep 2179339 = 3269009) B3269009
theorem B7355285 : Blo 2177435 7355285 := bbase (se 6 (by rfl) ⟨172389, by rfl⟩ : syracuseStep 7355285 = 344779) (by norm_num)
theorem B4903523 : Blo 2177435 4903523 := bstep (se 1 (by rfl) ⟨3677642, by rfl⟩ : syracuseStep 4903523 = 7355285) B7355285
theorem B3269015 : Blo 2177435 3269015 := bstep (se 1 (by rfl) ⟨2451761, by rfl⟩ : syracuseStep 3269015 = 4903523) B4903523
theorem B2179343 : Blo 2177435 2179343 := bstep (se 1 (by rfl) ⟨1634507, by rfl⟩ : syracuseStep 2179343 = 3269015) B3269015
theorem B3269021 : Blo 2177435 3269021 := bbase (se 3 (by rfl) ⟨612941, by rfl⟩ : syracuseStep 3269021 = 1225883) (by norm_num)
theorem B2179347 : Blo 2177435 2179347 := bstep (se 1 (by rfl) ⟨1634510, by rfl⟩ : syracuseStep 2179347 = 3269021) B3269021
theorem B4903541 : Blo 2177435 4903541 := bbase (se 5 (by rfl) ⟨229853, by rfl⟩ : syracuseStep 4903541 = 459707) (by norm_num)
theorem B3269027 : Blo 2177435 3269027 := bstep (se 1 (by rfl) ⟨2451770, by rfl⟩ : syracuseStep 3269027 = 4903541) B4903541
theorem B2179351 : Blo 2177435 2179351 := bstep (se 1 (by rfl) ⟨1634513, by rfl⟩ : syracuseStep 2179351 = 3269027) B3269027
theorem B5307805 : Blo 2177435 5307805 := bbase (se 3 (by rfl) ⟨995213, by rfl⟩ : syracuseStep 5307805 = 1990427) (by norm_num)
theorem B7077073 : Blo 2177435 7077073 := bstep (se 2 (by rfl) ⟨2653902, by rfl⟩ : syracuseStep 7077073 = 5307805) B5307805
theorem B9436097 : Blo 2177435 9436097 := bstep (se 2 (by rfl) ⟨3538536, by rfl⟩ : syracuseStep 9436097 = 7077073) B7077073
theorem B6290731 : Blo 2177435 6290731 := bstep (se 1 (by rfl) ⟨4718048, by rfl⟩ : syracuseStep 6290731 = 9436097) B9436097
theorem B8387641 : Blo 2177435 8387641 := bstep (se 2 (by rfl) ⟨3145365, by rfl⟩ : syracuseStep 8387641 = 6290731) B6290731
theorem B11183521 : Blo 2177435 11183521 := bstep (se 2 (by rfl) ⟨4193820, by rfl⟩ : syracuseStep 11183521 = 8387641) B8387641
theorem B14911361 : Blo 2177435 14911361 := bstep (se 2 (by rfl) ⟨5591760, by rfl⟩ : syracuseStep 14911361 = 11183521) B11183521
theorem B9940907 : Blo 2177435 9940907 := bstep (se 1 (by rfl) ⟨7455680, by rfl⟩ : syracuseStep 9940907 = 14911361) B14911361
theorem B6627271 : Blo 2177435 6627271 := bstep (se 1 (by rfl) ⟨4970453, by rfl⟩ : syracuseStep 6627271 = 9940907) B9940907
theorem B8836361 : Blo 2177435 8836361 := bstep (se 2 (by rfl) ⟨3313635, by rfl⟩ : syracuseStep 8836361 = 6627271) B6627271
theorem B5890907 : Blo 2177435 5890907 := bstep (se 1 (by rfl) ⟨4418180, by rfl⟩ : syracuseStep 5890907 = 8836361) B8836361
theorem B15709085 : Blo 2177435 15709085 := bstep (se 3 (by rfl) ⟨2945453, by rfl⟩ : syracuseStep 15709085 = 5890907) B5890907
theorem B10472723 : Blo 2177435 10472723 := bstep (se 1 (by rfl) ⟨7854542, by rfl⟩ : syracuseStep 10472723 = 15709085) B15709085
theorem B6981815 : Blo 2177435 6981815 := bstep (se 1 (by rfl) ⟨5236361, by rfl⟩ : syracuseStep 6981815 = 10472723) B10472723
theorem B18618173 : Blo 2177435 18618173 := bstep (se 3 (by rfl) ⟨3490907, by rfl⟩ : syracuseStep 18618173 = 6981815) B6981815
theorem B12412115 : Blo 2177435 12412115 := bstep (se 1 (by rfl) ⟨9309086, by rfl⟩ : syracuseStep 12412115 = 18618173) B18618173
theorem B8274743 : Blo 2177435 8274743 := bstep (se 1 (by rfl) ⟨6206057, by rfl⟩ : syracuseStep 8274743 = 12412115) B12412115
theorem B5516495 : Blo 2177435 5516495 := bstep (se 1 (by rfl) ⟨4137371, by rfl⟩ : syracuseStep 5516495 = 8274743) B8274743
theorem B3677663 : Blo 2177435 3677663 := bstep (se 1 (by rfl) ⟨2758247, by rfl⟩ : syracuseStep 3677663 = 5516495) B5516495
theorem B2451775 : Blo 2177435 2451775 := bstep (se 1 (by rfl) ⟨1838831, by rfl⟩ : syracuseStep 2451775 = 3677663) B3677663
theorem B3269033 : Blo 2177435 3269033 := bstep (se 2 (by rfl) ⟨1225887, by rfl⟩ : syracuseStep 3269033 = 2451775) B2451775
theorem B2179355 : Blo 2177435 2179355 := bstep (se 1 (by rfl) ⟨1634516, by rfl⟩ : syracuseStep 2179355 = 3269033) B3269033
theorem B8274757 : Blo 2177435 8274757 := bbase (se 4 (by rfl) ⟨775758, by rfl⟩ : syracuseStep 8274757 = 1551517) (by norm_num)
theorem B11033009 : Blo 2177435 11033009 := bstep (se 2 (by rfl) ⟨4137378, by rfl⟩ : syracuseStep 11033009 = 8274757) B8274757
theorem B7355339 : Blo 2177435 7355339 := bstep (se 1 (by rfl) ⟨5516504, by rfl⟩ : syracuseStep 7355339 = 11033009) B11033009
theorem B4903559 : Blo 2177435 4903559 := bstep (se 1 (by rfl) ⟨3677669, by rfl⟩ : syracuseStep 4903559 = 7355339) B7355339
theorem B3269039 : Blo 2177435 3269039 := bstep (se 1 (by rfl) ⟨2451779, by rfl⟩ : syracuseStep 3269039 = 4903559) B4903559
theorem B2179359 : Blo 2177435 2179359 := bstep (se 1 (by rfl) ⟨1634519, by rfl⟩ : syracuseStep 2179359 = 3269039) B3269039
theorem B3269045 : Blo 2177435 3269045 := bbase (se 5 (by rfl) ⟨153236, by rfl⟩ : syracuseStep 3269045 = 306473) (by norm_num)
theorem B2179363 : Blo 2177435 2179363 := bstep (se 1 (by rfl) ⟨1634522, by rfl⟩ : syracuseStep 2179363 = 3269045) B3269045
theorem B5516525 : Blo 2177435 5516525 := bbase (se 3 (by rfl) ⟨1034348, by rfl⟩ : syracuseStep 5516525 = 2068697) (by norm_num)
theorem B3677683 : Blo 2177435 3677683 := bstep (se 1 (by rfl) ⟨2758262, by rfl⟩ : syracuseStep 3677683 = 5516525) B5516525
theorem B4903577 : Blo 2177435 4903577 := bstep (se 2 (by rfl) ⟨1838841, by rfl⟩ : syracuseStep 4903577 = 3677683) B3677683
theorem B3269051 : Blo 2177435 3269051 := bstep (se 1 (by rfl) ⟨2451788, by rfl⟩ : syracuseStep 3269051 = 4903577) B4903577
theorem B2179367 : Blo 2177435 2179367 := bstep (se 1 (by rfl) ⟨1634525, by rfl⟩ : syracuseStep 2179367 = 3269051) B3269051
theorem B2451793 : Blo 2177435 2451793 := bbase (se 2 (by rfl) ⟨919422, by rfl⟩ : syracuseStep 2451793 = 1838845) (by norm_num)
theorem B3269057 : Blo 2177435 3269057 := bstep (se 2 (by rfl) ⟨1225896, by rfl⟩ : syracuseStep 3269057 = 2451793) B2451793
theorem B2179371 : Blo 2177435 2179371 := bstep (se 1 (by rfl) ⟨1634528, by rfl⟩ : syracuseStep 2179371 = 3269057) B3269057
theorem B2327293 : Blo 2177435 2327293 := bbase (se 3 (by rfl) ⟨436367, by rfl⟩ : syracuseStep 2327293 = 872735) (by norm_num)
theorem B3103057 : Blo 2177435 3103057 := bstep (se 2 (by rfl) ⟨1163646, by rfl⟩ : syracuseStep 3103057 = 2327293) B2327293
theorem B4137409 : Blo 2177435 4137409 := bstep (se 2 (by rfl) ⟨1551528, by rfl⟩ : syracuseStep 4137409 = 3103057) B3103057
theorem B5516545 : Blo 2177435 5516545 := bstep (se 2 (by rfl) ⟨2068704, by rfl⟩ : syracuseStep 5516545 = 4137409) B4137409
theorem B7355393 : Blo 2177435 7355393 := bstep (se 2 (by rfl) ⟨2758272, by rfl⟩ : syracuseStep 7355393 = 5516545) B5516545
theorem B4903595 : Blo 2177435 4903595 := bstep (se 1 (by rfl) ⟨3677696, by rfl⟩ : syracuseStep 4903595 = 7355393) B7355393
theorem B3269063 : Blo 2177435 3269063 := bstep (se 1 (by rfl) ⟨2451797, by rfl⟩ : syracuseStep 3269063 = 4903595) B4903595
theorem B2179375 : Blo 2177435 2179375 := bstep (se 1 (by rfl) ⟨1634531, by rfl⟩ : syracuseStep 2179375 = 3269063) B3269063
theorem B3269069 : Blo 2177435 3269069 := bbase (se 3 (by rfl) ⟨612950, by rfl⟩ : syracuseStep 3269069 = 1225901) (by norm_num)
theorem B2179379 : Blo 2177435 2179379 := bstep (se 1 (by rfl) ⟨1634534, by rfl⟩ : syracuseStep 2179379 = 3269069) B3269069
theorem B4903613 : Blo 2177435 4903613 := bbase (se 3 (by rfl) ⟨919427, by rfl⟩ : syracuseStep 4903613 = 1838855) (by norm_num)
theorem B3269075 : Blo 2177435 3269075 := bstep (se 1 (by rfl) ⟨2451806, by rfl⟩ : syracuseStep 3269075 = 4903613) B4903613
theorem B2179383 : Blo 2177435 2179383 := bstep (se 1 (by rfl) ⟨1634537, by rfl⟩ : syracuseStep 2179383 = 3269075) B3269075
theorem B3677717 : Blo 2177435 3677717 := bbase (se 6 (by rfl) ⟨86196, by rfl⟩ : syracuseStep 3677717 = 172393) (by norm_num)
theorem B2451811 : Blo 2177435 2451811 := bstep (se 1 (by rfl) ⟨1838858, by rfl⟩ : syracuseStep 2451811 = 3677717) B3677717
theorem B3269081 : Blo 2177435 3269081 := bstep (se 2 (by rfl) ⟨1225905, by rfl⟩ : syracuseStep 3269081 = 2451811) B2451811
theorem B2179387 : Blo 2177435 2179387 := bstep (se 1 (by rfl) ⟨1634540, by rfl⟩ : syracuseStep 2179387 = 3269081) B3269081
theorem B3727901 : Blo 2177435 3727901 := bbase (se 3 (by rfl) ⟨698981, by rfl⟩ : syracuseStep 3727901 = 1397963) (by norm_num)
theorem B9941069 : Blo 2177435 9941069 := bstep (se 3 (by rfl) ⟨1863950, by rfl⟩ : syracuseStep 9941069 = 3727901) B3727901
theorem B26509517 : Blo 2177435 26509517 := bstep (se 3 (by rfl) ⟨4970534, by rfl⟩ : syracuseStep 26509517 = 9941069) B9941069
theorem B17673011 : Blo 2177435 17673011 := bstep (se 1 (by rfl) ⟨13254758, by rfl⟩ : syracuseStep 17673011 = 26509517) B26509517
theorem B11782007 : Blo 2177435 11782007 := bstep (se 1 (by rfl) ⟨8836505, by rfl⟩ : syracuseStep 11782007 = 17673011) B17673011
theorem B7854671 : Blo 2177435 7854671 := bstep (se 1 (by rfl) ⟨5891003, by rfl⟩ : syracuseStep 7854671 = 11782007) B11782007
theorem B20945789 : Blo 2177435 20945789 := bstep (se 3 (by rfl) ⟨3927335, by rfl⟩ : syracuseStep 20945789 = 7854671) B7854671
theorem B13963859 : Blo 2177435 13963859 := bstep (se 1 (by rfl) ⟨10472894, by rfl⟩ : syracuseStep 13963859 = 20945789) B20945789
theorem B9309239 : Blo 2177435 9309239 := bstep (se 1 (by rfl) ⟨6981929, by rfl⟩ : syracuseStep 9309239 = 13963859) B13963859
theorem B6206159 : Blo 2177435 6206159 := bstep (se 1 (by rfl) ⟨4654619, by rfl⟩ : syracuseStep 6206159 = 9309239) B9309239
theorem B16549757 : Blo 2177435 16549757 := bstep (se 3 (by rfl) ⟨3103079, by rfl⟩ : syracuseStep 16549757 = 6206159) B6206159
theorem B11033171 : Blo 2177435 11033171 := bstep (se 1 (by rfl) ⟨8274878, by rfl⟩ : syracuseStep 11033171 = 16549757) B16549757
theorem B7355447 : Blo 2177435 7355447 := bstep (se 1 (by rfl) ⟨5516585, by rfl⟩ : syracuseStep 7355447 = 11033171) B11033171
theorem B4903631 : Blo 2177435 4903631 := bstep (se 1 (by rfl) ⟨3677723, by rfl⟩ : syracuseStep 4903631 = 7355447) B7355447
theorem B3269087 : Blo 2177435 3269087 := bstep (se 1 (by rfl) ⟨2451815, by rfl⟩ : syracuseStep 3269087 = 4903631) B4903631
theorem B2179391 : Blo 2177435 2179391 := bstep (se 1 (by rfl) ⟨1634543, by rfl⟩ : syracuseStep 2179391 = 3269087) B3269087
theorem B3269093 : Blo 2177435 3269093 := bbase (se 4 (by rfl) ⟨306477, by rfl⟩ : syracuseStep 3269093 = 612955) (by norm_num)
theorem B2179395 : Blo 2177435 2179395 := bstep (se 1 (by rfl) ⟨1634546, by rfl⟩ : syracuseStep 2179395 = 3269093) B3269093
theorem B3145429 : Blo 2177435 3145429 := bbase (se 7 (by rfl) ⟨36860, by rfl⟩ : syracuseStep 3145429 = 73721) (by norm_num)
theorem B4193905 : Blo 2177435 4193905 := bstep (se 2 (by rfl) ⟨1572714, by rfl⟩ : syracuseStep 4193905 = 3145429) B3145429
theorem B5591873 : Blo 2177435 5591873 := bstep (se 2 (by rfl) ⟨2096952, by rfl⟩ : syracuseStep 5591873 = 4193905) B4193905
theorem B14911661 : Blo 2177435 14911661 := bstep (se 3 (by rfl) ⟨2795936, by rfl⟩ : syracuseStep 14911661 = 5591873) B5591873
theorem B39764429 : Blo 2177435 39764429 := bstep (se 3 (by rfl) ⟨7455830, by rfl⟩ : syracuseStep 39764429 = 14911661) B14911661
theorem B26509619 : Blo 2177435 26509619 := bstep (se 1 (by rfl) ⟨19882214, by rfl⟩ : syracuseStep 26509619 = 39764429) B39764429
theorem B17673079 : Blo 2177435 17673079 := bstep (se 1 (by rfl) ⟨13254809, by rfl⟩ : syracuseStep 17673079 = 26509619) B26509619
theorem B23564105 : Blo 2177435 23564105 := bstep (se 2 (by rfl) ⟨8836539, by rfl⟩ : syracuseStep 23564105 = 17673079) B17673079
theorem B15709403 : Blo 2177435 15709403 := bstep (se 1 (by rfl) ⟨11782052, by rfl⟩ : syracuseStep 15709403 = 23564105) B23564105
theorem B10472935 : Blo 2177435 10472935 := bstep (se 1 (by rfl) ⟨7854701, by rfl⟩ : syracuseStep 10472935 = 15709403) B15709403
theorem B13963913 : Blo 2177435 13963913 := bstep (se 2 (by rfl) ⟨5236467, by rfl⟩ : syracuseStep 13963913 = 10472935) B10472935
theorem B9309275 : Blo 2177435 9309275 := bstep (se 1 (by rfl) ⟨6981956, by rfl⟩ : syracuseStep 9309275 = 13963913) B13963913
theorem B6206183 : Blo 2177435 6206183 := bstep (se 1 (by rfl) ⟨4654637, by rfl⟩ : syracuseStep 6206183 = 9309275) B9309275
theorem B4137455 : Blo 2177435 4137455 := bstep (se 1 (by rfl) ⟨3103091, by rfl⟩ : syracuseStep 4137455 = 6206183) B6206183
theorem B2758303 : Blo 2177435 2758303 := bstep (se 1 (by rfl) ⟨2068727, by rfl⟩ : syracuseStep 2758303 = 4137455) B4137455
theorem B3677737 : Blo 2177435 3677737 := bstep (se 2 (by rfl) ⟨1379151, by rfl⟩ : syracuseStep 3677737 = 2758303) B2758303
theorem B4903649 : Blo 2177435 4903649 := bstep (se 2 (by rfl) ⟨1838868, by rfl⟩ : syracuseStep 4903649 = 3677737) B3677737
theorem B3269099 : Blo 2177435 3269099 := bstep (se 1 (by rfl) ⟨2451824, by rfl⟩ : syracuseStep 3269099 = 4903649) B4903649
theorem B2179399 : Blo 2177435 2179399 := bstep (se 1 (by rfl) ⟨1634549, by rfl⟩ : syracuseStep 2179399 = 3269099) B3269099
theorem B2451829 : Blo 2177435 2451829 := bbase (se 5 (by rfl) ⟨114929, by rfl⟩ : syracuseStep 2451829 = 229859) (by norm_num)
theorem B3269105 : Blo 2177435 3269105 := bstep (se 2 (by rfl) ⟨1225914, by rfl⟩ : syracuseStep 3269105 = 2451829) B2451829
theorem B2179403 : Blo 2177435 2179403 := bstep (se 1 (by rfl) ⟨1634552, by rfl⟩ : syracuseStep 2179403 = 3269105) B3269105
theorem B2758313 : Blo 2177435 2758313 := bbase (se 2 (by rfl) ⟨1034367, by rfl⟩ : syracuseStep 2758313 = 2068735) (by norm_num)
theorem B7355501 : Blo 2177435 7355501 := bstep (se 3 (by rfl) ⟨1379156, by rfl⟩ : syracuseStep 7355501 = 2758313) B2758313
theorem B4903667 : Blo 2177435 4903667 := bstep (se 1 (by rfl) ⟨3677750, by rfl⟩ : syracuseStep 4903667 = 7355501) B7355501
theorem B3269111 : Blo 2177435 3269111 := bstep (se 1 (by rfl) ⟨2451833, by rfl⟩ : syracuseStep 3269111 = 4903667) B4903667
theorem B2179407 : Blo 2177435 2179407 := bstep (se 1 (by rfl) ⟨1634555, by rfl⟩ : syracuseStep 2179407 = 3269111) B3269111
theorem B3269117 : Blo 2177435 3269117 := bbase (se 3 (by rfl) ⟨612959, by rfl⟩ : syracuseStep 3269117 = 1225919) (by norm_num)
theorem B2179411 : Blo 2177435 2179411 := bstep (se 1 (by rfl) ⟨1634558, by rfl⟩ : syracuseStep 2179411 = 3269117) B3269117
theorem B4903685 : Blo 2177435 4903685 := bbase (se 4 (by rfl) ⟨459720, by rfl⟩ : syracuseStep 4903685 = 919441) (by norm_num)
theorem B3269123 : Blo 2177435 3269123 := bstep (se 1 (by rfl) ⟨2451842, by rfl⟩ : syracuseStep 3269123 = 4903685) B4903685
theorem B2179415 : Blo 2177435 2179415 := bstep (se 1 (by rfl) ⟨1634561, by rfl⟩ : syracuseStep 2179415 = 3269123) B3269123
theorem B4137493 : Blo 2177435 4137493 := bbase (se 6 (by rfl) ⟨96972, by rfl⟩ : syracuseStep 4137493 = 193945) (by norm_num)
theorem B5516657 : Blo 2177435 5516657 := bstep (se 2 (by rfl) ⟨2068746, by rfl⟩ : syracuseStep 5516657 = 4137493) B4137493
theorem B3677771 : Blo 2177435 3677771 := bstep (se 1 (by rfl) ⟨2758328, by rfl⟩ : syracuseStep 3677771 = 5516657) B5516657
theorem B2451847 : Blo 2177435 2451847 := bstep (se 1 (by rfl) ⟨1838885, by rfl⟩ : syracuseStep 2451847 = 3677771) B3677771
theorem B3269129 : Blo 2177435 3269129 := bstep (se 2 (by rfl) ⟨1225923, by rfl⟩ : syracuseStep 3269129 = 2451847) B2451847
theorem B2179419 : Blo 2177435 2179419 := bstep (se 1 (by rfl) ⟨1634564, by rfl⟩ : syracuseStep 2179419 = 3269129) B3269129
theorem B11033333 : Blo 2177435 11033333 := bbase (se 5 (by rfl) ⟨517187, by rfl⟩ : syracuseStep 11033333 = 1034375) (by norm_num)
theorem B7355555 : Blo 2177435 7355555 := bstep (se 1 (by rfl) ⟨5516666, by rfl⟩ : syracuseStep 7355555 = 11033333) B11033333
theorem B4903703 : Blo 2177435 4903703 := bstep (se 1 (by rfl) ⟨3677777, by rfl⟩ : syracuseStep 4903703 = 7355555) B7355555
theorem B3269135 : Blo 2177435 3269135 := bstep (se 1 (by rfl) ⟨2451851, by rfl⟩ : syracuseStep 3269135 = 4903703) B4903703
theorem B2179423 : Blo 2177435 2179423 := bstep (se 1 (by rfl) ⟨1634567, by rfl⟩ : syracuseStep 2179423 = 3269135) B3269135
theorem B3269141 : Blo 2177435 3269141 := bbase (se 6 (by rfl) ⟨76620, by rfl⟩ : syracuseStep 3269141 = 153241) (by norm_num)
theorem B2179427 : Blo 2177435 2179427 := bstep (se 1 (by rfl) ⟨1634570, by rfl⟩ : syracuseStep 2179427 = 3269141) B3269141
theorem B3491029 : Blo 2177435 3491029 := bbase (se 7 (by rfl) ⟨40910, by rfl⟩ : syracuseStep 3491029 = 81821) (by norm_num)
theorem B18618821 : Blo 2177435 18618821 := bstep (se 4 (by rfl) ⟨1745514, by rfl⟩ : syracuseStep 18618821 = 3491029) B3491029
theorem B12412547 : Blo 2177435 12412547 := bstep (se 1 (by rfl) ⟨9309410, by rfl⟩ : syracuseStep 12412547 = 18618821) B18618821
theorem B8275031 : Blo 2177435 8275031 := bstep (se 1 (by rfl) ⟨6206273, by rfl⟩ : syracuseStep 8275031 = 12412547) B12412547
theorem B5516687 : Blo 2177435 5516687 := bstep (se 1 (by rfl) ⟨4137515, by rfl⟩ : syracuseStep 5516687 = 8275031) B8275031
theorem B3677791 : Blo 2177435 3677791 := bstep (se 1 (by rfl) ⟨2758343, by rfl⟩ : syracuseStep 3677791 = 5516687) B5516687
theorem B4903721 : Blo 2177435 4903721 := bstep (se 2 (by rfl) ⟨1838895, by rfl⟩ : syracuseStep 4903721 = 3677791) B3677791
theorem B3269147 : Blo 2177435 3269147 := bstep (se 1 (by rfl) ⟨2451860, by rfl⟩ : syracuseStep 3269147 = 4903721) B4903721
theorem B2179431 : Blo 2177435 2179431 := bstep (se 1 (by rfl) ⟨1634573, by rfl⟩ : syracuseStep 2179431 = 3269147) B3269147
theorem B2451865 : Blo 2177435 2451865 := bbase (se 2 (by rfl) ⟨919449, by rfl⟩ : syracuseStep 2451865 = 1838899) (by norm_num)
theorem B3269153 : Blo 2177435 3269153 := bstep (se 2 (by rfl) ⟨1225932, by rfl⟩ : syracuseStep 3269153 = 2451865) B2451865
theorem B2179435 : Blo 2177435 2179435 := bstep (se 1 (by rfl) ⟨1634576, by rfl⟩ : syracuseStep 2179435 = 3269153) B3269153
theorem C0 (j : ℕ) (h1 : 544358 ≤ j) (h2 : j ≤ 544858) : Blo 2177435 (4 * j + 3) := by
  interval_cases j
  · exact B2177435
  · exact B2177439
  · exact B2177443
  · exact B2177447
  · exact B2177451
  · exact B2177455
  · exact B2177459
  · exact B2177463
  · exact B2177467
  · exact B2177471
  · exact B2177475
  · exact B2177479
  · exact B2177483
  · exact B2177487
  · exact B2177491
  · exact B2177495
  · exact B2177499
  · exact B2177503
  · exact B2177507
  · exact B2177511
  · exact B2177515
  · exact B2177519
  · exact B2177523
  · exact B2177527
  · exact B2177531
  · exact B2177535
  · exact B2177539
  · exact B2177543
  · exact B2177547
  · exact B2177551
  · exact B2177555
  · exact B2177559
  · exact B2177563
  · exact B2177567
  · exact B2177571
  · exact B2177575
  · exact B2177579
  · exact B2177583
  · exact B2177587
  · exact B2177591
  · exact B2177595
  · exact B2177599
  · exact B2177603
  · exact B2177607
  · exact B2177611
  · exact B2177615
  · exact B2177619
  · exact B2177623
  · exact B2177627
  · exact B2177631
  · exact B2177635
  · exact B2177639
  · exact B2177643
  · exact B2177647
  · exact B2177651
  · exact B2177655
  · exact B2177659
  · exact B2177663
  · exact B2177667
  · exact B2177671
  · exact B2177675
  · exact B2177679
  · exact B2177683
  · exact B2177687
  · exact B2177691
  · exact B2177695
  · exact B2177699
  · exact B2177703
  · exact B2177707
  · exact B2177711
  · exact B2177715
  · exact B2177719
  · exact B2177723
  · exact B2177727
  · exact B2177731
  · exact B2177735
  · exact B2177739
  · exact B2177743
  · exact B2177747
  · exact B2177751
  · exact B2177755
  · exact B2177759
  · exact B2177763
  · exact B2177767
  · exact B2177771
  · exact B2177775
  · exact B2177779
  · exact B2177783
  · exact B2177787
  · exact B2177791
  · exact B2177795
  · exact B2177799
  · exact B2177803
  · exact B2177807
  · exact B2177811
  · exact B2177815
  · exact B2177819
  · exact B2177823
  · exact B2177827
  · exact B2177831
  · exact B2177835
  · exact B2177839
  · exact B2177843
  · exact B2177847
  · exact B2177851
  · exact B2177855
  · exact B2177859
  · exact B2177863
  · exact B2177867
  · exact B2177871
  · exact B2177875
  · exact B2177879
  · exact B2177883
  · exact B2177887
  · exact B2177891
  · exact B2177895
  · exact B2177899
  · exact B2177903
  · exact B2177907
  · exact B2177911
  · exact B2177915
  · exact B2177919
  · exact B2177923
  · exact B2177927
  · exact B2177931
  · exact B2177935
  · exact B2177939
  · exact B2177943
  · exact B2177947
  · exact B2177951
  · exact B2177955
  · exact B2177959
  · exact B2177963
  · exact B2177967
  · exact B2177971
  · exact B2177975
  · exact B2177979
  · exact B2177983
  · exact B2177987
  · exact B2177991
  · exact B2177995
  · exact B2177999
  · exact B2178003
  · exact B2178007
  · exact B2178011
  · exact B2178015
  · exact B2178019
  · exact B2178023
  · exact B2178027
  · exact B2178031
  · exact B2178035
  · exact B2178039
  · exact B2178043
  · exact B2178047
  · exact B2178051
  · exact B2178055
  · exact B2178059
  · exact B2178063
  · exact B2178067
  · exact B2178071
  · exact B2178075
  · exact B2178079
  · exact B2178083
  · exact B2178087
  · exact B2178091
  · exact B2178095
  · exact B2178099
  · exact B2178103
  · exact B2178107
  · exact B2178111
  · exact B2178115
  · exact B2178119
  · exact B2178123
  · exact B2178127
  · exact B2178131
  · exact B2178135
  · exact B2178139
  · exact B2178143
  · exact B2178147
  · exact B2178151
  · exact B2178155
  · exact B2178159
  · exact B2178163
  · exact B2178167
  · exact B2178171
  · exact B2178175
  · exact B2178179
  · exact B2178183
  · exact B2178187
  · exact B2178191
  · exact B2178195
  · exact B2178199
  · exact B2178203
  · exact B2178207
  · exact B2178211
  · exact B2178215
  · exact B2178219
  · exact B2178223
  · exact B2178227
  · exact B2178231
  · exact B2178235
  · exact B2178239
  · exact B2178243
  · exact B2178247
  · exact B2178251
  · exact B2178255
  · exact B2178259
  · exact B2178263
  · exact B2178267
  · exact B2178271
  · exact B2178275
  · exact B2178279
  · exact B2178283
  · exact B2178287
  · exact B2178291
  · exact B2178295
  · exact B2178299
  · exact B2178303
  · exact B2178307
  · exact B2178311
  · exact B2178315
  · exact B2178319
  · exact B2178323
  · exact B2178327
  · exact B2178331
  · exact B2178335
  · exact B2178339
  · exact B2178343
  · exact B2178347
  · exact B2178351
  · exact B2178355
  · exact B2178359
  · exact B2178363
  · exact B2178367
  · exact B2178371
  · exact B2178375
  · exact B2178379
  · exact B2178383
  · exact B2178387
  · exact B2178391
  · exact B2178395
  · exact B2178399
  · exact B2178403
  · exact B2178407
  · exact B2178411
  · exact B2178415
  · exact B2178419
  · exact B2178423
  · exact B2178427
  · exact B2178431
  · exact B2178435
  · exact B2178439
  · exact B2178443
  · exact B2178447
  · exact B2178451
  · exact B2178455
  · exact B2178459
  · exact B2178463
  · exact B2178467
  · exact B2178471
  · exact B2178475
  · exact B2178479
  · exact B2178483
  · exact B2178487
  · exact B2178491
  · exact B2178495
  · exact B2178499
  · exact B2178503
  · exact B2178507
  · exact B2178511
  · exact B2178515
  · exact B2178519
  · exact B2178523
  · exact B2178527
  · exact B2178531
  · exact B2178535
  · exact B2178539
  · exact B2178543
  · exact B2178547
  · exact B2178551
  · exact B2178555
  · exact B2178559
  · exact B2178563
  · exact B2178567
  · exact B2178571
  · exact B2178575
  · exact B2178579
  · exact B2178583
  · exact B2178587
  · exact B2178591
  · exact B2178595
  · exact B2178599
  · exact B2178603
  · exact B2178607
  · exact B2178611
  · exact B2178615
  · exact B2178619
  · exact B2178623
  · exact B2178627
  · exact B2178631
  · exact B2178635
  · exact B2178639
  · exact B2178643
  · exact B2178647
  · exact B2178651
  · exact B2178655
  · exact B2178659
  · exact B2178663
  · exact B2178667
  · exact B2178671
  · exact B2178675
  · exact B2178679
  · exact B2178683
  · exact B2178687
  · exact B2178691
  · exact B2178695
  · exact B2178699
  · exact B2178703
  · exact B2178707
  · exact B2178711
  · exact B2178715
  · exact B2178719
  · exact B2178723
  · exact B2178727
  · exact B2178731
  · exact B2178735
  · exact B2178739
  · exact B2178743
  · exact B2178747
  · exact B2178751
  · exact B2178755
  · exact B2178759
  · exact B2178763
  · exact B2178767
  · exact B2178771
  · exact B2178775
  · exact B2178779
  · exact B2178783
  · exact B2178787
  · exact B2178791
  · exact B2178795
  · exact B2178799
  · exact B2178803
  · exact B2178807
  · exact B2178811
  · exact B2178815
  · exact B2178819
  · exact B2178823
  · exact B2178827
  · exact B2178831
  · exact B2178835
  · exact B2178839
  · exact B2178843
  · exact B2178847
  · exact B2178851
  · exact B2178855
  · exact B2178859
  · exact B2178863
  · exact B2178867
  · exact B2178871
  · exact B2178875
  · exact B2178879
  · exact B2178883
  · exact B2178887
  · exact B2178891
  · exact B2178895
  · exact B2178899
  · exact B2178903
  · exact B2178907
  · exact B2178911
  · exact B2178915
  · exact B2178919
  · exact B2178923
  · exact B2178927
  · exact B2178931
  · exact B2178935
  · exact B2178939
  · exact B2178943
  · exact B2178947
  · exact B2178951
  · exact B2178955
  · exact B2178959
  · exact B2178963
  · exact B2178967
  · exact B2178971
  · exact B2178975
  · exact B2178979
  · exact B2178983
  · exact B2178987
  · exact B2178991
  · exact B2178995
  · exact B2178999
  · exact B2179003
  · exact B2179007
  · exact B2179011
  · exact B2179015
  · exact B2179019
  · exact B2179023
  · exact B2179027
  · exact B2179031
  · exact B2179035
  · exact B2179039
  · exact B2179043
  · exact B2179047
  · exact B2179051
  · exact B2179055
  · exact B2179059
  · exact B2179063
  · exact B2179067
  · exact B2179071
  · exact B2179075
  · exact B2179079
  · exact B2179083
  · exact B2179087
  · exact B2179091
  · exact B2179095
  · exact B2179099
  · exact B2179103
  · exact B2179107
  · exact B2179111
  · exact B2179115
  · exact B2179119
  · exact B2179123
  · exact B2179127
  · exact B2179131
  · exact B2179135
  · exact B2179139
  · exact B2179143
  · exact B2179147
  · exact B2179151
  · exact B2179155
  · exact B2179159
  · exact B2179163
  · exact B2179167
  · exact B2179171
  · exact B2179175
  · exact B2179179
  · exact B2179183
  · exact B2179187
  · exact B2179191
  · exact B2179195
  · exact B2179199
  · exact B2179203
  · exact B2179207
  · exact B2179211
  · exact B2179215
  · exact B2179219
  · exact B2179223
  · exact B2179227
  · exact B2179231
  · exact B2179235
  · exact B2179239
  · exact B2179243
  · exact B2179247
  · exact B2179251
  · exact B2179255
  · exact B2179259
  · exact B2179263
  · exact B2179267
  · exact B2179271
  · exact B2179275
  · exact B2179279
  · exact B2179283
  · exact B2179287
  · exact B2179291
  · exact B2179295
  · exact B2179299
  · exact B2179303
  · exact B2179307
  · exact B2179311
  · exact B2179315
  · exact B2179319
  · exact B2179323
  · exact B2179327
  · exact B2179331
  · exact B2179335
  · exact B2179339
  · exact B2179343
  · exact B2179347
  · exact B2179351
  · exact B2179355
  · exact B2179359
  · exact B2179363
  · exact B2179367
  · exact B2179371
  · exact B2179375
  · exact B2179379
  · exact B2179383
  · exact B2179387
  · exact B2179391
  · exact B2179395
  · exact B2179399
  · exact B2179403
  · exact B2179407
  · exact B2179411
  · exact B2179415
  · exact B2179419
  · exact B2179423
  · exact B2179427
  · exact B2179431
  · exact B2179435
theorem solution (m : ℕ) (hlo : 2177435 ≤ m) (hhi : m ≤ 2179435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 544358 ≤ j := by omega
    have hj2 : j ≤ 544858 := by omega
    have hb : Blo 2177435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
