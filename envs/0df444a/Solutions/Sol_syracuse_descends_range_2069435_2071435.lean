-- Prove2me | solution 1 for syracuse_descends_range_2069435_2071435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:04.16391+00:00
-- url     : https://prove2.me/submissions/1e44b9fe-61dc-45a7-8a95-4d36f26edbb0

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

theorem B3492173 : Blo 2069435 3492173 := bbase (se 3 (by rfl) ⟨654782, by rfl⟩ : syracuseStep 3492173 = 1309565) (by norm_num)
theorem B2328115 : Blo 2069435 2328115 := bstep (se 1 (by rfl) ⟨1746086, by rfl⟩ : syracuseStep 2328115 = 3492173) B3492173
theorem B3104153 : Blo 2069435 3104153 := bstep (se 2 (by rfl) ⟨1164057, by rfl⟩ : syracuseStep 3104153 = 2328115) B2328115
theorem B2069435 : Blo 2069435 2069435 := bstep (se 1 (by rfl) ⟨1552076, by rfl⟩ : syracuseStep 2069435 = 3104153) B3104153
theorem B10619477 : Blo 2069435 10619477 := bbase (se 8 (by rfl) ⟨62223, by rfl⟩ : syracuseStep 10619477 = 124447) (by norm_num)
theorem B7079651 : Blo 2069435 7079651 := bstep (se 1 (by rfl) ⟨5309738, by rfl⟩ : syracuseStep 7079651 = 10619477) B10619477
theorem B4719767 : Blo 2069435 4719767 := bstep (se 1 (by rfl) ⟨3539825, by rfl⟩ : syracuseStep 4719767 = 7079651) B7079651
theorem B12586045 : Blo 2069435 12586045 := bstep (se 3 (by rfl) ⟨2359883, by rfl⟩ : syracuseStep 12586045 = 4719767) B4719767
theorem B16781393 : Blo 2069435 16781393 := bstep (se 2 (by rfl) ⟨6293022, by rfl⟩ : syracuseStep 16781393 = 12586045) B12586045
theorem B11187595 : Blo 2069435 11187595 := bstep (se 1 (by rfl) ⟨8390696, by rfl⟩ : syracuseStep 11187595 = 16781393) B16781393
theorem B14916793 : Blo 2069435 14916793 := bstep (se 2 (by rfl) ⟨5593797, by rfl⟩ : syracuseStep 14916793 = 11187595) B11187595
theorem B19889057 : Blo 2069435 19889057 := bstep (se 2 (by rfl) ⟨7458396, by rfl⟩ : syracuseStep 19889057 = 14916793) B14916793
theorem B13259371 : Blo 2069435 13259371 := bstep (se 1 (by rfl) ⟨9944528, by rfl⟩ : syracuseStep 13259371 = 19889057) B19889057
theorem B17679161 : Blo 2069435 17679161 := bstep (se 2 (by rfl) ⟨6629685, by rfl⟩ : syracuseStep 17679161 = 13259371) B13259371
theorem B11786107 : Blo 2069435 11786107 := bstep (se 1 (by rfl) ⟨8839580, by rfl⟩ : syracuseStep 11786107 = 17679161) B17679161
theorem B15714809 : Blo 2069435 15714809 := bstep (se 2 (by rfl) ⟨5893053, by rfl⟩ : syracuseStep 15714809 = 11786107) B11786107
theorem B10476539 : Blo 2069435 10476539 := bstep (se 1 (by rfl) ⟨7857404, by rfl⟩ : syracuseStep 10476539 = 15714809) B15714809
theorem B6984359 : Blo 2069435 6984359 := bstep (se 1 (by rfl) ⟨5238269, by rfl⟩ : syracuseStep 6984359 = 10476539) B10476539
theorem B4656239 : Blo 2069435 4656239 := bstep (se 1 (by rfl) ⟨3492179, by rfl⟩ : syracuseStep 4656239 = 6984359) B6984359
theorem B3104159 : Blo 2069435 3104159 := bstep (se 1 (by rfl) ⟨2328119, by rfl⟩ : syracuseStep 3104159 = 4656239) B4656239
theorem B2069439 : Blo 2069435 2069439 := bstep (se 1 (by rfl) ⟨1552079, by rfl⟩ : syracuseStep 2069439 = 3104159) B3104159
theorem B3104165 : Blo 2069435 3104165 := bbase (se 4 (by rfl) ⟨291015, by rfl⟩ : syracuseStep 3104165 = 582031) (by norm_num)
theorem B2069443 : Blo 2069435 2069443 := bstep (se 1 (by rfl) ⟨1552082, by rfl⟩ : syracuseStep 2069443 = 3104165) B3104165
theorem B2619145 : Blo 2069435 2619145 := bbase (se 2 (by rfl) ⟨982179, by rfl⟩ : syracuseStep 2619145 = 1964359) (by norm_num)
theorem B3492193 : Blo 2069435 3492193 := bstep (se 2 (by rfl) ⟨1309572, by rfl⟩ : syracuseStep 3492193 = 2619145) B2619145
theorem B4656257 : Blo 2069435 4656257 := bstep (se 2 (by rfl) ⟨1746096, by rfl⟩ : syracuseStep 4656257 = 3492193) B3492193
theorem B3104171 : Blo 2069435 3104171 := bstep (se 1 (by rfl) ⟨2328128, by rfl⟩ : syracuseStep 3104171 = 4656257) B4656257
theorem B2069447 : Blo 2069435 2069447 := bstep (se 1 (by rfl) ⟨1552085, by rfl⟩ : syracuseStep 2069447 = 3104171) B3104171
theorem B2328133 : Blo 2069435 2328133 := bbase (se 4 (by rfl) ⟨218262, by rfl⟩ : syracuseStep 2328133 = 436525) (by norm_num)
theorem B3104177 : Blo 2069435 3104177 := bstep (se 2 (by rfl) ⟨1164066, by rfl⟩ : syracuseStep 3104177 = 2328133) B2328133
theorem B2069451 : Blo 2069435 2069451 := bstep (se 1 (by rfl) ⟨1552088, by rfl⟩ : syracuseStep 2069451 = 3104177) B3104177
theorem B3928733 : Blo 2069435 3928733 := bbase (se 3 (by rfl) ⟨736637, by rfl⟩ : syracuseStep 3928733 = 1473275) (by norm_num)
theorem B2619155 : Blo 2069435 2619155 := bstep (se 1 (by rfl) ⟨1964366, by rfl⟩ : syracuseStep 2619155 = 3928733) B3928733
theorem B6984413 : Blo 2069435 6984413 := bstep (se 3 (by rfl) ⟨1309577, by rfl⟩ : syracuseStep 6984413 = 2619155) B2619155
theorem B4656275 : Blo 2069435 4656275 := bstep (se 1 (by rfl) ⟨3492206, by rfl⟩ : syracuseStep 4656275 = 6984413) B6984413
theorem B3104183 : Blo 2069435 3104183 := bstep (se 1 (by rfl) ⟨2328137, by rfl⟩ : syracuseStep 3104183 = 4656275) B4656275
theorem B2069455 : Blo 2069435 2069455 := bstep (se 1 (by rfl) ⟨1552091, by rfl⟩ : syracuseStep 2069455 = 3104183) B3104183
theorem B3104189 : Blo 2069435 3104189 := bbase (se 3 (by rfl) ⟨582035, by rfl⟩ : syracuseStep 3104189 = 1164071) (by norm_num)
theorem B2069459 : Blo 2069435 2069459 := bstep (se 1 (by rfl) ⟨1552094, by rfl⟩ : syracuseStep 2069459 = 3104189) B3104189
theorem B4656293 : Blo 2069435 4656293 := bbase (se 4 (by rfl) ⟨436527, by rfl⟩ : syracuseStep 4656293 = 873055) (by norm_num)
theorem B3104195 : Blo 2069435 3104195 := bstep (se 1 (by rfl) ⟨2328146, by rfl⟩ : syracuseStep 3104195 = 4656293) B4656293
theorem B2069463 : Blo 2069435 2069463 := bstep (se 1 (by rfl) ⟨1552097, by rfl⟩ : syracuseStep 2069463 = 3104195) B3104195
theorem B5238341 : Blo 2069435 5238341 := bbase (se 4 (by rfl) ⟨491094, by rfl⟩ : syracuseStep 5238341 = 982189) (by norm_num)
theorem B3492227 : Blo 2069435 3492227 := bstep (se 1 (by rfl) ⟨2619170, by rfl⟩ : syracuseStep 3492227 = 5238341) B5238341
theorem B2328151 : Blo 2069435 2328151 := bstep (se 1 (by rfl) ⟨1746113, by rfl⟩ : syracuseStep 2328151 = 3492227) B3492227
theorem B3104201 : Blo 2069435 3104201 := bstep (se 2 (by rfl) ⟨1164075, by rfl⟩ : syracuseStep 3104201 = 2328151) B2328151
theorem B2069467 : Blo 2069435 2069467 := bstep (se 1 (by rfl) ⟨1552100, by rfl⟩ : syracuseStep 2069467 = 3104201) B3104201
theorem B9439685 : Blo 2069435 9439685 := bbase (se 4 (by rfl) ⟨884970, by rfl⟩ : syracuseStep 9439685 = 1769941) (by norm_num)
theorem B6293123 : Blo 2069435 6293123 := bstep (se 1 (by rfl) ⟨4719842, by rfl⟩ : syracuseStep 6293123 = 9439685) B9439685
theorem B4195415 : Blo 2069435 4195415 := bstep (se 1 (by rfl) ⟨3146561, by rfl⟩ : syracuseStep 4195415 = 6293123) B6293123
theorem B2796943 : Blo 2069435 2796943 := bstep (se 1 (by rfl) ⟨2097707, by rfl⟩ : syracuseStep 2796943 = 4195415) B4195415
theorem B3729257 : Blo 2069435 3729257 := bstep (se 2 (by rfl) ⟨1398471, by rfl⟩ : syracuseStep 3729257 = 2796943) B2796943
theorem B2486171 : Blo 2069435 2486171 := bstep (se 1 (by rfl) ⟨1864628, by rfl⟩ : syracuseStep 2486171 = 3729257) B3729257
theorem B6629789 : Blo 2069435 6629789 := bstep (se 3 (by rfl) ⟨1243085, by rfl⟩ : syracuseStep 6629789 = 2486171) B2486171
theorem B4419859 : Blo 2069435 4419859 := bstep (se 1 (by rfl) ⟨3314894, by rfl⟩ : syracuseStep 4419859 = 6629789) B6629789
theorem B5893145 : Blo 2069435 5893145 := bstep (se 2 (by rfl) ⟨2209929, by rfl⟩ : syracuseStep 5893145 = 4419859) B4419859
theorem B3928763 : Blo 2069435 3928763 := bstep (se 1 (by rfl) ⟨2946572, by rfl⟩ : syracuseStep 3928763 = 5893145) B5893145
theorem B10476701 : Blo 2069435 10476701 := bstep (se 3 (by rfl) ⟨1964381, by rfl⟩ : syracuseStep 10476701 = 3928763) B3928763
theorem B6984467 : Blo 2069435 6984467 := bstep (se 1 (by rfl) ⟨5238350, by rfl⟩ : syracuseStep 6984467 = 10476701) B10476701
theorem B4656311 : Blo 2069435 4656311 := bstep (se 1 (by rfl) ⟨3492233, by rfl⟩ : syracuseStep 4656311 = 6984467) B6984467
theorem B3104207 : Blo 2069435 3104207 := bstep (se 1 (by rfl) ⟨2328155, by rfl⟩ : syracuseStep 3104207 = 4656311) B4656311
theorem B2069471 : Blo 2069435 2069471 := bstep (se 1 (by rfl) ⟨1552103, by rfl⟩ : syracuseStep 2069471 = 3104207) B3104207
theorem B3104213 : Blo 2069435 3104213 := bbase (se 7 (by rfl) ⟨36377, by rfl⟩ : syracuseStep 3104213 = 72755) (by norm_num)
theorem B2069475 : Blo 2069435 2069475 := bstep (se 1 (by rfl) ⟨1552106, by rfl⟩ : syracuseStep 2069475 = 3104213) B3104213
theorem B7857557 : Blo 2069435 7857557 := bbase (se 6 (by rfl) ⟨184161, by rfl⟩ : syracuseStep 7857557 = 368323) (by norm_num)
theorem B5238371 : Blo 2069435 5238371 := bstep (se 1 (by rfl) ⟨3928778, by rfl⟩ : syracuseStep 5238371 = 7857557) B7857557
theorem B3492247 : Blo 2069435 3492247 := bstep (se 1 (by rfl) ⟨2619185, by rfl⟩ : syracuseStep 3492247 = 5238371) B5238371
theorem B4656329 : Blo 2069435 4656329 := bstep (se 2 (by rfl) ⟨1746123, by rfl⟩ : syracuseStep 4656329 = 3492247) B3492247
theorem B3104219 : Blo 2069435 3104219 := bstep (se 1 (by rfl) ⟨2328164, by rfl⟩ : syracuseStep 3104219 = 4656329) B4656329
theorem B2069479 : Blo 2069435 2069479 := bstep (se 1 (by rfl) ⟨1552109, by rfl⟩ : syracuseStep 2069479 = 3104219) B3104219
theorem B2328169 : Blo 2069435 2328169 := bbase (se 2 (by rfl) ⟨873063, by rfl⟩ : syracuseStep 2328169 = 1746127) (by norm_num)
theorem B3104225 : Blo 2069435 3104225 := bstep (se 2 (by rfl) ⟨1164084, by rfl⟩ : syracuseStep 3104225 = 2328169) B2328169
theorem B2069483 : Blo 2069435 2069483 := bstep (se 1 (by rfl) ⟨1552112, by rfl⟩ : syracuseStep 2069483 = 3104225) B3104225
theorem B4419893 : Blo 2069435 4419893 := bbase (se 5 (by rfl) ⟨207182, by rfl⟩ : syracuseStep 4419893 = 414365) (by norm_num)
theorem B11786381 : Blo 2069435 11786381 := bstep (se 3 (by rfl) ⟨2209946, by rfl⟩ : syracuseStep 11786381 = 4419893) B4419893
theorem B7857587 : Blo 2069435 7857587 := bstep (se 1 (by rfl) ⟨5893190, by rfl⟩ : syracuseStep 7857587 = 11786381) B11786381
theorem B5238391 : Blo 2069435 5238391 := bstep (se 1 (by rfl) ⟨3928793, by rfl⟩ : syracuseStep 5238391 = 7857587) B7857587
theorem B6984521 : Blo 2069435 6984521 := bstep (se 2 (by rfl) ⟨2619195, by rfl⟩ : syracuseStep 6984521 = 5238391) B5238391
theorem B4656347 : Blo 2069435 4656347 := bstep (se 1 (by rfl) ⟨3492260, by rfl⟩ : syracuseStep 4656347 = 6984521) B6984521
theorem B3104231 : Blo 2069435 3104231 := bstep (se 1 (by rfl) ⟨2328173, by rfl⟩ : syracuseStep 3104231 = 4656347) B4656347
theorem B2069487 : Blo 2069435 2069487 := bstep (se 1 (by rfl) ⟨1552115, by rfl⟩ : syracuseStep 2069487 = 3104231) B3104231
theorem B3104237 : Blo 2069435 3104237 := bbase (se 3 (by rfl) ⟨582044, by rfl⟩ : syracuseStep 3104237 = 1164089) (by norm_num)
theorem B2069491 : Blo 2069435 2069491 := bstep (se 1 (by rfl) ⟨1552118, by rfl⟩ : syracuseStep 2069491 = 3104237) B3104237
theorem B4656365 : Blo 2069435 4656365 := bbase (se 3 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 4656365 = 1746137) (by norm_num)
theorem B3104243 : Blo 2069435 3104243 := bstep (se 1 (by rfl) ⟨2328182, by rfl⟩ : syracuseStep 3104243 = 4656365) B4656365
theorem B2069495 : Blo 2069435 2069495 := bstep (se 1 (by rfl) ⟨1552121, by rfl⟩ : syracuseStep 2069495 = 3104243) B3104243
theorem B2946613 : Blo 2069435 2946613 := bbase (se 5 (by rfl) ⟨138122, by rfl⟩ : syracuseStep 2946613 = 276245) (by norm_num)
theorem B3928817 : Blo 2069435 3928817 := bstep (se 2 (by rfl) ⟨1473306, by rfl⟩ : syracuseStep 3928817 = 2946613) B2946613
theorem B2619211 : Blo 2069435 2619211 := bstep (se 1 (by rfl) ⟨1964408, by rfl⟩ : syracuseStep 2619211 = 3928817) B3928817
theorem B3492281 : Blo 2069435 3492281 := bstep (se 2 (by rfl) ⟨1309605, by rfl⟩ : syracuseStep 3492281 = 2619211) B2619211
theorem B2328187 : Blo 2069435 2328187 := bstep (se 1 (by rfl) ⟨1746140, by rfl⟩ : syracuseStep 2328187 = 3492281) B3492281
theorem B3104249 : Blo 2069435 3104249 := bstep (se 2 (by rfl) ⟨1164093, by rfl⟩ : syracuseStep 3104249 = 2328187) B2328187
theorem B2069499 : Blo 2069435 2069499 := bstep (se 1 (by rfl) ⟨1552124, by rfl⟩ : syracuseStep 2069499 = 3104249) B3104249
theorem B11495317 : Blo 2069435 11495317 := bbase (se 6 (by rfl) ⟨269421, by rfl⟩ : syracuseStep 11495317 = 538843) (by norm_num)
theorem B15327089 : Blo 2069435 15327089 := bstep (se 2 (by rfl) ⟨5747658, by rfl⟩ : syracuseStep 15327089 = 11495317) B11495317
theorem B10218059 : Blo 2069435 10218059 := bstep (se 1 (by rfl) ⟨7663544, by rfl⟩ : syracuseStep 10218059 = 15327089) B15327089
theorem B6812039 : Blo 2069435 6812039 := bstep (se 1 (by rfl) ⟨5109029, by rfl⟩ : syracuseStep 6812039 = 10218059) B10218059
theorem B4541359 : Blo 2069435 4541359 := bstep (se 1 (by rfl) ⟨3406019, by rfl⟩ : syracuseStep 4541359 = 6812039) B6812039
theorem B6055145 : Blo 2069435 6055145 := bstep (se 2 (by rfl) ⟨2270679, by rfl⟩ : syracuseStep 6055145 = 4541359) B4541359
theorem B4036763 : Blo 2069435 4036763 := bstep (se 1 (by rfl) ⟨3027572, by rfl⟩ : syracuseStep 4036763 = 6055145) B6055145
theorem B2691175 : Blo 2069435 2691175 := bstep (se 1 (by rfl) ⟨2018381, by rfl⟩ : syracuseStep 2691175 = 4036763) B4036763
theorem B3588233 : Blo 2069435 3588233 := bstep (se 2 (by rfl) ⟨1345587, by rfl⟩ : syracuseStep 3588233 = 2691175) B2691175
theorem B9568621 : Blo 2069435 9568621 := bstep (se 3 (by rfl) ⟨1794116, by rfl⟩ : syracuseStep 9568621 = 3588233) B3588233
theorem B12758161 : Blo 2069435 12758161 := bstep (se 2 (by rfl) ⟨4784310, by rfl⟩ : syracuseStep 12758161 = 9568621) B9568621
theorem B17010881 : Blo 2069435 17010881 := bstep (se 2 (by rfl) ⟨6379080, by rfl⟩ : syracuseStep 17010881 = 12758161) B12758161
theorem B11340587 : Blo 2069435 11340587 := bstep (se 1 (by rfl) ⟨8505440, by rfl⟩ : syracuseStep 11340587 = 17010881) B17010881
theorem B7560391 : Blo 2069435 7560391 := bstep (se 1 (by rfl) ⟨5670293, by rfl⟩ : syracuseStep 7560391 = 11340587) B11340587
theorem B10080521 : Blo 2069435 10080521 := bstep (se 2 (by rfl) ⟨3780195, by rfl⟩ : syracuseStep 10080521 = 7560391) B7560391
theorem B6720347 : Blo 2069435 6720347 := bstep (se 1 (by rfl) ⟨5040260, by rfl⟩ : syracuseStep 6720347 = 10080521) B10080521
theorem B4480231 : Blo 2069435 4480231 := bstep (se 1 (by rfl) ⟨3360173, by rfl⟩ : syracuseStep 4480231 = 6720347) B6720347
theorem B5973641 : Blo 2069435 5973641 := bstep (se 2 (by rfl) ⟨2240115, by rfl⟩ : syracuseStep 5973641 = 4480231) B4480231
theorem B3982427 : Blo 2069435 3982427 := bstep (se 1 (by rfl) ⟨2986820, by rfl⟩ : syracuseStep 3982427 = 5973641) B5973641
theorem B2654951 : Blo 2069435 2654951 := bstep (se 1 (by rfl) ⟨1991213, by rfl⟩ : syracuseStep 2654951 = 3982427) B3982427
theorem B7079869 : Blo 2069435 7079869 := bstep (se 3 (by rfl) ⟨1327475, by rfl⟩ : syracuseStep 7079869 = 2654951) B2654951
theorem B9439825 : Blo 2069435 9439825 := bstep (se 2 (by rfl) ⟨3539934, by rfl⟩ : syracuseStep 9439825 = 7079869) B7079869
theorem B12586433 : Blo 2069435 12586433 := bstep (se 2 (by rfl) ⟨4719912, by rfl⟩ : syracuseStep 12586433 = 9439825) B9439825
theorem B33563821 : Blo 2069435 33563821 := bstep (se 3 (by rfl) ⟨6293216, by rfl⟩ : syracuseStep 33563821 = 12586433) B12586433
theorem B44751761 : Blo 2069435 44751761 := bstep (se 2 (by rfl) ⟨16781910, by rfl⟩ : syracuseStep 44751761 = 33563821) B33563821
theorem B29834507 : Blo 2069435 29834507 := bstep (se 1 (by rfl) ⟨22375880, by rfl⟩ : syracuseStep 29834507 = 44751761) B44751761
theorem B79558685 : Blo 2069435 79558685 := bstep (se 3 (by rfl) ⟨14917253, by rfl⟩ : syracuseStep 79558685 = 29834507) B29834507
theorem B53039123 : Blo 2069435 53039123 := bstep (se 1 (by rfl) ⟨39779342, by rfl⟩ : syracuseStep 53039123 = 79558685) B79558685
theorem B35359415 : Blo 2069435 35359415 := bstep (se 1 (by rfl) ⟨26519561, by rfl⟩ : syracuseStep 35359415 = 53039123) B53039123
theorem B23572943 : Blo 2069435 23572943 := bstep (se 1 (by rfl) ⟨17679707, by rfl⟩ : syracuseStep 23572943 = 35359415) B35359415
theorem B15715295 : Blo 2069435 15715295 := bstep (se 1 (by rfl) ⟨11786471, by rfl⟩ : syracuseStep 15715295 = 23572943) B23572943
theorem B10476863 : Blo 2069435 10476863 := bstep (se 1 (by rfl) ⟨7857647, by rfl⟩ : syracuseStep 10476863 = 15715295) B15715295
theorem B6984575 : Blo 2069435 6984575 := bstep (se 1 (by rfl) ⟨5238431, by rfl⟩ : syracuseStep 6984575 = 10476863) B10476863
theorem B4656383 : Blo 2069435 4656383 := bstep (se 1 (by rfl) ⟨3492287, by rfl⟩ : syracuseStep 4656383 = 6984575) B6984575
theorem B3104255 : Blo 2069435 3104255 := bstep (se 1 (by rfl) ⟨2328191, by rfl⟩ : syracuseStep 3104255 = 4656383) B4656383
theorem B2069503 : Blo 2069435 2069503 := bstep (se 1 (by rfl) ⟨1552127, by rfl⟩ : syracuseStep 2069503 = 3104255) B3104255
theorem B3104261 : Blo 2069435 3104261 := bbase (se 4 (by rfl) ⟨291024, by rfl⟩ : syracuseStep 3104261 = 582049) (by norm_num)
theorem B2069507 : Blo 2069435 2069507 := bstep (se 1 (by rfl) ⟨1552130, by rfl⟩ : syracuseStep 2069507 = 3104261) B3104261
theorem B3492301 : Blo 2069435 3492301 := bbase (se 3 (by rfl) ⟨654806, by rfl⟩ : syracuseStep 3492301 = 1309613) (by norm_num)
theorem B4656401 : Blo 2069435 4656401 := bstep (se 2 (by rfl) ⟨1746150, by rfl⟩ : syracuseStep 4656401 = 3492301) B3492301
theorem B3104267 : Blo 2069435 3104267 := bstep (se 1 (by rfl) ⟨2328200, by rfl⟩ : syracuseStep 3104267 = 4656401) B4656401
theorem B2069511 : Blo 2069435 2069511 := bstep (se 1 (by rfl) ⟨1552133, by rfl⟩ : syracuseStep 2069511 = 3104267) B3104267
theorem B2328205 : Blo 2069435 2328205 := bbase (se 3 (by rfl) ⟨436538, by rfl⟩ : syracuseStep 2328205 = 873077) (by norm_num)
theorem B3104273 : Blo 2069435 3104273 := bstep (se 2 (by rfl) ⟨1164102, by rfl⟩ : syracuseStep 3104273 = 2328205) B2328205
theorem B2069515 : Blo 2069435 2069515 := bstep (se 1 (by rfl) ⟨1552136, by rfl⟩ : syracuseStep 2069515 = 3104273) B3104273
theorem B6984629 : Blo 2069435 6984629 := bbase (se 5 (by rfl) ⟨327404, by rfl⟩ : syracuseStep 6984629 = 654809) (by norm_num)
theorem B4656419 : Blo 2069435 4656419 := bstep (se 1 (by rfl) ⟨3492314, by rfl⟩ : syracuseStep 4656419 = 6984629) B6984629
theorem B3104279 : Blo 2069435 3104279 := bstep (se 1 (by rfl) ⟨2328209, by rfl⟩ : syracuseStep 3104279 = 4656419) B4656419
theorem B2069519 : Blo 2069435 2069519 := bstep (se 1 (by rfl) ⟨1552139, by rfl⟩ : syracuseStep 2069519 = 3104279) B3104279
theorem B3104285 : Blo 2069435 3104285 := bbase (se 3 (by rfl) ⟨582053, by rfl⟩ : syracuseStep 3104285 = 1164107) (by norm_num)
theorem B2069523 : Blo 2069435 2069523 := bstep (se 1 (by rfl) ⟨1552142, by rfl⟩ : syracuseStep 2069523 = 3104285) B3104285
theorem B4656437 : Blo 2069435 4656437 := bbase (se 5 (by rfl) ⟨218270, by rfl⟩ : syracuseStep 4656437 = 436541) (by norm_num)
theorem B3104291 : Blo 2069435 3104291 := bstep (se 1 (by rfl) ⟨2328218, by rfl⟩ : syracuseStep 3104291 = 4656437) B4656437
theorem B2069527 : Blo 2069435 2069527 := bstep (se 1 (by rfl) ⟨1552145, by rfl⟩ : syracuseStep 2069527 = 3104291) B3104291
theorem B3027613 : Blo 2069435 3027613 := bbase (se 3 (by rfl) ⟨567677, by rfl⟩ : syracuseStep 3027613 = 1135355) (by norm_num)
theorem B4036817 : Blo 2069435 4036817 := bstep (se 2 (by rfl) ⟨1513806, by rfl⟩ : syracuseStep 4036817 = 3027613) B3027613
theorem B10764845 : Blo 2069435 10764845 := bstep (se 3 (by rfl) ⟨2018408, by rfl⟩ : syracuseStep 10764845 = 4036817) B4036817
theorem B7176563 : Blo 2069435 7176563 := bstep (se 1 (by rfl) ⟨5382422, by rfl⟩ : syracuseStep 7176563 = 10764845) B10764845
theorem B4784375 : Blo 2069435 4784375 := bstep (se 1 (by rfl) ⟨3588281, by rfl⟩ : syracuseStep 4784375 = 7176563) B7176563
theorem B3189583 : Blo 2069435 3189583 := bstep (se 1 (by rfl) ⟨2392187, by rfl⟩ : syracuseStep 3189583 = 4784375) B4784375
theorem B17011109 : Blo 2069435 17011109 := bstep (se 4 (by rfl) ⟨1594791, by rfl⟩ : syracuseStep 17011109 = 3189583) B3189583
theorem B11340739 : Blo 2069435 11340739 := bstep (se 1 (by rfl) ⟨8505554, by rfl⟩ : syracuseStep 11340739 = 17011109) B17011109
theorem B15120985 : Blo 2069435 15120985 := bstep (se 2 (by rfl) ⟨5670369, by rfl⟩ : syracuseStep 15120985 = 11340739) B11340739
theorem B20161313 : Blo 2069435 20161313 := bstep (se 2 (by rfl) ⟨7560492, by rfl⟩ : syracuseStep 20161313 = 15120985) B15120985
theorem B13440875 : Blo 2069435 13440875 := bstep (se 1 (by rfl) ⟨10080656, by rfl⟩ : syracuseStep 13440875 = 20161313) B20161313
theorem B35842333 : Blo 2069435 35842333 := bstep (se 3 (by rfl) ⟨6720437, by rfl⟩ : syracuseStep 35842333 = 13440875) B13440875
theorem B47789777 : Blo 2069435 47789777 := bstep (se 2 (by rfl) ⟨17921166, by rfl⟩ : syracuseStep 47789777 = 35842333) B35842333
theorem B31859851 : Blo 2069435 31859851 := bstep (se 1 (by rfl) ⟨23894888, by rfl⟩ : syracuseStep 31859851 = 47789777) B47789777
theorem B42479801 : Blo 2069435 42479801 := bstep (se 2 (by rfl) ⟨15929925, by rfl⟩ : syracuseStep 42479801 = 31859851) B31859851
theorem B28319867 : Blo 2069435 28319867 := bstep (se 1 (by rfl) ⟨21239900, by rfl⟩ : syracuseStep 28319867 = 42479801) B42479801
theorem B18879911 : Blo 2069435 18879911 := bstep (se 1 (by rfl) ⟨14159933, by rfl⟩ : syracuseStep 18879911 = 28319867) B28319867
theorem B12586607 : Blo 2069435 12586607 := bstep (se 1 (by rfl) ⟨9439955, by rfl⟩ : syracuseStep 12586607 = 18879911) B18879911
theorem B8391071 : Blo 2069435 8391071 := bstep (se 1 (by rfl) ⟨6293303, by rfl⟩ : syracuseStep 8391071 = 12586607) B12586607
theorem B22376189 : Blo 2069435 22376189 := bstep (se 3 (by rfl) ⟨4195535, by rfl⟩ : syracuseStep 22376189 = 8391071) B8391071
theorem B14917459 : Blo 2069435 14917459 := bstep (se 1 (by rfl) ⟨11188094, by rfl⟩ : syracuseStep 14917459 = 22376189) B22376189
theorem B19889945 : Blo 2069435 19889945 := bstep (se 2 (by rfl) ⟨7458729, by rfl⟩ : syracuseStep 19889945 = 14917459) B14917459
theorem B13259963 : Blo 2069435 13259963 := bstep (se 1 (by rfl) ⟨9944972, by rfl⟩ : syracuseStep 13259963 = 19889945) B19889945
theorem B8839975 : Blo 2069435 8839975 := bstep (se 1 (by rfl) ⟨6629981, by rfl⟩ : syracuseStep 8839975 = 13259963) B13259963
theorem B11786633 : Blo 2069435 11786633 := bstep (se 2 (by rfl) ⟨4419987, by rfl⟩ : syracuseStep 11786633 = 8839975) B8839975
theorem B7857755 : Blo 2069435 7857755 := bstep (se 1 (by rfl) ⟨5893316, by rfl⟩ : syracuseStep 7857755 = 11786633) B11786633
theorem B5238503 : Blo 2069435 5238503 := bstep (se 1 (by rfl) ⟨3928877, by rfl⟩ : syracuseStep 5238503 = 7857755) B7857755
theorem B3492335 : Blo 2069435 3492335 := bstep (se 1 (by rfl) ⟨2619251, by rfl⟩ : syracuseStep 3492335 = 5238503) B5238503
theorem B2328223 : Blo 2069435 2328223 := bstep (se 1 (by rfl) ⟨1746167, by rfl⟩ : syracuseStep 2328223 = 3492335) B3492335
theorem B3104297 : Blo 2069435 3104297 := bstep (se 2 (by rfl) ⟨1164111, by rfl⟩ : syracuseStep 3104297 = 2328223) B2328223
theorem B2069531 : Blo 2069435 2069531 := bstep (se 1 (by rfl) ⟨1552148, by rfl⟩ : syracuseStep 2069531 = 3104297) B3104297
theorem B9439973 : Blo 2069435 9439973 := bbase (se 4 (by rfl) ⟨884997, by rfl⟩ : syracuseStep 9439973 = 1769995) (by norm_num)
theorem B6293315 : Blo 2069435 6293315 := bstep (se 1 (by rfl) ⟨4719986, by rfl⟩ : syracuseStep 6293315 = 9439973) B9439973
theorem B16782173 : Blo 2069435 16782173 := bstep (se 3 (by rfl) ⟨3146657, by rfl⟩ : syracuseStep 16782173 = 6293315) B6293315
theorem B11188115 : Blo 2069435 11188115 := bstep (se 1 (by rfl) ⟨8391086, by rfl⟩ : syracuseStep 11188115 = 16782173) B16782173
theorem B7458743 : Blo 2069435 7458743 := bstep (se 1 (by rfl) ⟨5594057, by rfl⟩ : syracuseStep 7458743 = 11188115) B11188115
theorem B19889981 : Blo 2069435 19889981 := bstep (se 3 (by rfl) ⟨3729371, by rfl⟩ : syracuseStep 19889981 = 7458743) B7458743
theorem B13259987 : Blo 2069435 13259987 := bstep (se 1 (by rfl) ⟨9944990, by rfl⟩ : syracuseStep 13259987 = 19889981) B19889981
theorem B8839991 : Blo 2069435 8839991 := bstep (se 1 (by rfl) ⟨6629993, by rfl⟩ : syracuseStep 8839991 = 13259987) B13259987
theorem B5893327 : Blo 2069435 5893327 := bstep (se 1 (by rfl) ⟨4419995, by rfl⟩ : syracuseStep 5893327 = 8839991) B8839991
theorem B7857769 : Blo 2069435 7857769 := bstep (se 2 (by rfl) ⟨2946663, by rfl⟩ : syracuseStep 7857769 = 5893327) B5893327
theorem B10477025 : Blo 2069435 10477025 := bstep (se 2 (by rfl) ⟨3928884, by rfl⟩ : syracuseStep 10477025 = 7857769) B7857769
theorem B6984683 : Blo 2069435 6984683 := bstep (se 1 (by rfl) ⟨5238512, by rfl⟩ : syracuseStep 6984683 = 10477025) B10477025
theorem B4656455 : Blo 2069435 4656455 := bstep (se 1 (by rfl) ⟨3492341, by rfl⟩ : syracuseStep 4656455 = 6984683) B6984683
theorem B3104303 : Blo 2069435 3104303 := bstep (se 1 (by rfl) ⟨2328227, by rfl⟩ : syracuseStep 3104303 = 4656455) B4656455
theorem B2069535 : Blo 2069435 2069535 := bstep (se 1 (by rfl) ⟨1552151, by rfl⟩ : syracuseStep 2069535 = 3104303) B3104303
theorem B3104309 : Blo 2069435 3104309 := bbase (se 5 (by rfl) ⟨145514, by rfl⟩ : syracuseStep 3104309 = 291029) (by norm_num)
theorem B2069539 : Blo 2069435 2069539 := bstep (se 1 (by rfl) ⟨1552154, by rfl⟩ : syracuseStep 2069539 = 3104309) B3104309
theorem B5238533 : Blo 2069435 5238533 := bbase (se 4 (by rfl) ⟨491112, by rfl⟩ : syracuseStep 5238533 = 982225) (by norm_num)
theorem B3492355 : Blo 2069435 3492355 := bstep (se 1 (by rfl) ⟨2619266, by rfl⟩ : syracuseStep 3492355 = 5238533) B5238533
theorem B4656473 : Blo 2069435 4656473 := bstep (se 2 (by rfl) ⟨1746177, by rfl⟩ : syracuseStep 4656473 = 3492355) B3492355
theorem B3104315 : Blo 2069435 3104315 := bstep (se 1 (by rfl) ⟨2328236, by rfl⟩ : syracuseStep 3104315 = 4656473) B4656473
theorem B2069543 : Blo 2069435 2069543 := bstep (se 1 (by rfl) ⟨1552157, by rfl⟩ : syracuseStep 2069543 = 3104315) B3104315
theorem B2328241 : Blo 2069435 2328241 := bbase (se 2 (by rfl) ⟨873090, by rfl⟩ : syracuseStep 2328241 = 1746181) (by norm_num)
theorem B3104321 : Blo 2069435 3104321 := bstep (se 2 (by rfl) ⟨1164120, by rfl⟩ : syracuseStep 3104321 = 2328241) B2328241
theorem B2069547 : Blo 2069435 2069547 := bstep (se 1 (by rfl) ⟨1552160, by rfl⟩ : syracuseStep 2069547 = 3104321) B3104321
theorem B5310029 : Blo 2069435 5310029 := bbase (se 3 (by rfl) ⟨995630, by rfl⟩ : syracuseStep 5310029 = 1991261) (by norm_num)
theorem B3540019 : Blo 2069435 3540019 := bstep (se 1 (by rfl) ⟨2655014, by rfl⟩ : syracuseStep 3540019 = 5310029) B5310029
theorem B4720025 : Blo 2069435 4720025 := bstep (se 2 (by rfl) ⟨1770009, by rfl⟩ : syracuseStep 4720025 = 3540019) B3540019
theorem B3146683 : Blo 2069435 3146683 := bstep (se 1 (by rfl) ⟨2360012, by rfl⟩ : syracuseStep 3146683 = 4720025) B4720025
theorem B4195577 : Blo 2069435 4195577 := bstep (se 2 (by rfl) ⟨1573341, by rfl⟩ : syracuseStep 4195577 = 3146683) B3146683
theorem B11188205 : Blo 2069435 11188205 := bstep (se 3 (by rfl) ⟨2097788, by rfl⟩ : syracuseStep 11188205 = 4195577) B4195577
theorem B7458803 : Blo 2069435 7458803 := bstep (se 1 (by rfl) ⟨5594102, by rfl⟩ : syracuseStep 7458803 = 11188205) B11188205
theorem B4972535 : Blo 2069435 4972535 := bstep (se 1 (by rfl) ⟨3729401, by rfl⟩ : syracuseStep 4972535 = 7458803) B7458803
theorem B3315023 : Blo 2069435 3315023 := bstep (se 1 (by rfl) ⟨2486267, by rfl⟩ : syracuseStep 3315023 = 4972535) B4972535
theorem B2210015 : Blo 2069435 2210015 := bstep (se 1 (by rfl) ⟨1657511, by rfl⟩ : syracuseStep 2210015 = 3315023) B3315023
theorem B5893373 : Blo 2069435 5893373 := bstep (se 3 (by rfl) ⟨1105007, by rfl⟩ : syracuseStep 5893373 = 2210015) B2210015
theorem B3928915 : Blo 2069435 3928915 := bstep (se 1 (by rfl) ⟨2946686, by rfl⟩ : syracuseStep 3928915 = 5893373) B5893373
theorem B5238553 : Blo 2069435 5238553 := bstep (se 2 (by rfl) ⟨1964457, by rfl⟩ : syracuseStep 5238553 = 3928915) B3928915
theorem B6984737 : Blo 2069435 6984737 := bstep (se 2 (by rfl) ⟨2619276, by rfl⟩ : syracuseStep 6984737 = 5238553) B5238553
theorem B4656491 : Blo 2069435 4656491 := bstep (se 1 (by rfl) ⟨3492368, by rfl⟩ : syracuseStep 4656491 = 6984737) B6984737
theorem B3104327 : Blo 2069435 3104327 := bstep (se 1 (by rfl) ⟨2328245, by rfl⟩ : syracuseStep 3104327 = 4656491) B4656491
theorem B2069551 : Blo 2069435 2069551 := bstep (se 1 (by rfl) ⟨1552163, by rfl⟩ : syracuseStep 2069551 = 3104327) B3104327
theorem B3104333 : Blo 2069435 3104333 := bbase (se 3 (by rfl) ⟨582062, by rfl⟩ : syracuseStep 3104333 = 1164125) (by norm_num)
theorem B2069555 : Blo 2069435 2069555 := bstep (se 1 (by rfl) ⟨1552166, by rfl⟩ : syracuseStep 2069555 = 3104333) B3104333
theorem B4656509 : Blo 2069435 4656509 := bbase (se 3 (by rfl) ⟨873095, by rfl⟩ : syracuseStep 4656509 = 1746191) (by norm_num)
theorem B3104339 : Blo 2069435 3104339 := bstep (se 1 (by rfl) ⟨2328254, by rfl⟩ : syracuseStep 3104339 = 4656509) B4656509
theorem B2069559 : Blo 2069435 2069559 := bstep (se 1 (by rfl) ⟨1552169, by rfl⟩ : syracuseStep 2069559 = 3104339) B3104339
theorem B3492389 : Blo 2069435 3492389 := bbase (se 4 (by rfl) ⟨327411, by rfl⟩ : syracuseStep 3492389 = 654823) (by norm_num)
theorem B2328259 : Blo 2069435 2328259 := bstep (se 1 (by rfl) ⟨1746194, by rfl⟩ : syracuseStep 2328259 = 3492389) B3492389
theorem B3104345 : Blo 2069435 3104345 := bstep (se 2 (by rfl) ⟨1164129, by rfl⟩ : syracuseStep 3104345 = 2328259) B2328259
theorem B2069563 : Blo 2069435 2069563 := bstep (se 1 (by rfl) ⟨1552172, by rfl⟩ : syracuseStep 2069563 = 3104345) B3104345
theorem B2946709 : Blo 2069435 2946709 := bbase (se 6 (by rfl) ⟨69063, by rfl⟩ : syracuseStep 2946709 = 138127) (by norm_num)
theorem B15715781 : Blo 2069435 15715781 := bstep (se 4 (by rfl) ⟨1473354, by rfl⟩ : syracuseStep 15715781 = 2946709) B2946709
theorem B10477187 : Blo 2069435 10477187 := bstep (se 1 (by rfl) ⟨7857890, by rfl⟩ : syracuseStep 10477187 = 15715781) B15715781
theorem B6984791 : Blo 2069435 6984791 := bstep (se 1 (by rfl) ⟨5238593, by rfl⟩ : syracuseStep 6984791 = 10477187) B10477187
theorem B4656527 : Blo 2069435 4656527 := bstep (se 1 (by rfl) ⟨3492395, by rfl⟩ : syracuseStep 4656527 = 6984791) B6984791
theorem B3104351 : Blo 2069435 3104351 := bstep (se 1 (by rfl) ⟨2328263, by rfl⟩ : syracuseStep 3104351 = 4656527) B4656527
theorem B2069567 : Blo 2069435 2069567 := bstep (se 1 (by rfl) ⟨1552175, by rfl⟩ : syracuseStep 2069567 = 3104351) B3104351
theorem B3104357 : Blo 2069435 3104357 := bbase (se 4 (by rfl) ⟨291033, by rfl⟩ : syracuseStep 3104357 = 582067) (by norm_num)
theorem B2069571 : Blo 2069435 2069571 := bstep (se 1 (by rfl) ⟨1552178, by rfl⟩ : syracuseStep 2069571 = 3104357) B3104357
theorem B2210041 : Blo 2069435 2210041 := bbase (se 2 (by rfl) ⟨828765, by rfl⟩ : syracuseStep 2210041 = 1657531) (by norm_num)
theorem B2946721 : Blo 2069435 2946721 := bstep (se 2 (by rfl) ⟨1105020, by rfl⟩ : syracuseStep 2946721 = 2210041) B2210041
theorem B3928961 : Blo 2069435 3928961 := bstep (se 2 (by rfl) ⟨1473360, by rfl⟩ : syracuseStep 3928961 = 2946721) B2946721
theorem B2619307 : Blo 2069435 2619307 := bstep (se 1 (by rfl) ⟨1964480, by rfl⟩ : syracuseStep 2619307 = 3928961) B3928961
theorem B3492409 : Blo 2069435 3492409 := bstep (se 2 (by rfl) ⟨1309653, by rfl⟩ : syracuseStep 3492409 = 2619307) B2619307
theorem B4656545 : Blo 2069435 4656545 := bstep (se 2 (by rfl) ⟨1746204, by rfl⟩ : syracuseStep 4656545 = 3492409) B3492409
theorem B3104363 : Blo 2069435 3104363 := bstep (se 1 (by rfl) ⟨2328272, by rfl⟩ : syracuseStep 3104363 = 4656545) B4656545
theorem B2069575 : Blo 2069435 2069575 := bstep (se 1 (by rfl) ⟨1552181, by rfl⟩ : syracuseStep 2069575 = 3104363) B3104363
theorem B2328277 : Blo 2069435 2328277 := bbase (se 7 (by rfl) ⟨27284, by rfl⟩ : syracuseStep 2328277 = 54569) (by norm_num)
theorem B3104369 : Blo 2069435 3104369 := bstep (se 2 (by rfl) ⟨1164138, by rfl⟩ : syracuseStep 3104369 = 2328277) B2328277
theorem B2069579 : Blo 2069435 2069579 := bstep (se 1 (by rfl) ⟨1552184, by rfl⟩ : syracuseStep 2069579 = 3104369) B3104369
theorem B2619317 : Blo 2069435 2619317 := bbase (se 5 (by rfl) ⟨122780, by rfl⟩ : syracuseStep 2619317 = 245561) (by norm_num)
theorem B6984845 : Blo 2069435 6984845 := bstep (se 3 (by rfl) ⟨1309658, by rfl⟩ : syracuseStep 6984845 = 2619317) B2619317
theorem B4656563 : Blo 2069435 4656563 := bstep (se 1 (by rfl) ⟨3492422, by rfl⟩ : syracuseStep 4656563 = 6984845) B6984845
theorem B3104375 : Blo 2069435 3104375 := bstep (se 1 (by rfl) ⟨2328281, by rfl⟩ : syracuseStep 3104375 = 4656563) B4656563
theorem B2069583 : Blo 2069435 2069583 := bstep (se 1 (by rfl) ⟨1552187, by rfl⟩ : syracuseStep 2069583 = 3104375) B3104375
theorem B3104381 : Blo 2069435 3104381 := bbase (se 3 (by rfl) ⟨582071, by rfl⟩ : syracuseStep 3104381 = 1164143) (by norm_num)
theorem B2069587 : Blo 2069435 2069587 := bstep (se 1 (by rfl) ⟨1552190, by rfl⟩ : syracuseStep 2069587 = 3104381) B3104381
theorem B4656581 : Blo 2069435 4656581 := bbase (se 4 (by rfl) ⟨436554, by rfl⟩ : syracuseStep 4656581 = 873109) (by norm_num)
theorem B3104387 : Blo 2069435 3104387 := bstep (se 1 (by rfl) ⟨2328290, by rfl⟩ : syracuseStep 3104387 = 4656581) B4656581
theorem B2069591 : Blo 2069435 2069591 := bstep (se 1 (by rfl) ⟨1552193, by rfl⟩ : syracuseStep 2069591 = 3104387) B3104387
theorem B2097833 : Blo 2069435 2097833 := bbase (se 2 (by rfl) ⟨786687, by rfl⟩ : syracuseStep 2097833 = 1573375) (by norm_num)
theorem B5594221 : Blo 2069435 5594221 := bstep (se 3 (by rfl) ⟨1048916, by rfl⟩ : syracuseStep 5594221 = 2097833) B2097833
theorem B7458961 : Blo 2069435 7458961 := bstep (se 2 (by rfl) ⟨2797110, by rfl⟩ : syracuseStep 7458961 = 5594221) B5594221
theorem B9945281 : Blo 2069435 9945281 := bstep (se 2 (by rfl) ⟨3729480, by rfl⟩ : syracuseStep 9945281 = 7458961) B7458961
theorem B6630187 : Blo 2069435 6630187 := bstep (se 1 (by rfl) ⟨4972640, by rfl⟩ : syracuseStep 6630187 = 9945281) B9945281
theorem B8840249 : Blo 2069435 8840249 := bstep (se 2 (by rfl) ⟨3315093, by rfl⟩ : syracuseStep 8840249 = 6630187) B6630187
theorem B5893499 : Blo 2069435 5893499 := bstep (se 1 (by rfl) ⟨4420124, by rfl⟩ : syracuseStep 5893499 = 8840249) B8840249
theorem B3928999 : Blo 2069435 3928999 := bstep (se 1 (by rfl) ⟨2946749, by rfl⟩ : syracuseStep 3928999 = 5893499) B5893499
theorem B5238665 : Blo 2069435 5238665 := bstep (se 2 (by rfl) ⟨1964499, by rfl⟩ : syracuseStep 5238665 = 3928999) B3928999
theorem B3492443 : Blo 2069435 3492443 := bstep (se 1 (by rfl) ⟨2619332, by rfl⟩ : syracuseStep 3492443 = 5238665) B5238665
theorem B2328295 : Blo 2069435 2328295 := bstep (se 1 (by rfl) ⟨1746221, by rfl⟩ : syracuseStep 2328295 = 3492443) B3492443
theorem B3104393 : Blo 2069435 3104393 := bstep (se 2 (by rfl) ⟨1164147, by rfl⟩ : syracuseStep 3104393 = 2328295) B2328295
theorem B2069595 : Blo 2069435 2069595 := bstep (se 1 (by rfl) ⟨1552196, by rfl⟩ : syracuseStep 2069595 = 3104393) B3104393
theorem B10477349 : Blo 2069435 10477349 := bbase (se 4 (by rfl) ⟨982251, by rfl⟩ : syracuseStep 10477349 = 1964503) (by norm_num)
theorem B6984899 : Blo 2069435 6984899 := bstep (se 1 (by rfl) ⟨5238674, by rfl⟩ : syracuseStep 6984899 = 10477349) B10477349
theorem B4656599 : Blo 2069435 4656599 := bstep (se 1 (by rfl) ⟨3492449, by rfl⟩ : syracuseStep 4656599 = 6984899) B6984899
theorem B3104399 : Blo 2069435 3104399 := bstep (se 1 (by rfl) ⟨2328299, by rfl⟩ : syracuseStep 3104399 = 4656599) B4656599
theorem B2069599 : Blo 2069435 2069599 := bstep (se 1 (by rfl) ⟨1552199, by rfl⟩ : syracuseStep 2069599 = 3104399) B3104399
theorem B3104405 : Blo 2069435 3104405 := bbase (se 6 (by rfl) ⟨72759, by rfl⟩ : syracuseStep 3104405 = 145519) (by norm_num)
theorem B2069603 : Blo 2069435 2069603 := bstep (se 1 (by rfl) ⟨1552202, by rfl⟩ : syracuseStep 2069603 = 3104405) B3104405
theorem B10620341 : Blo 2069435 10620341 := bbase (se 5 (by rfl) ⟨497828, by rfl⟩ : syracuseStep 10620341 = 995657) (by norm_num)
theorem B7080227 : Blo 2069435 7080227 := bstep (se 1 (by rfl) ⟨5310170, by rfl⟩ : syracuseStep 7080227 = 10620341) B10620341
theorem B4720151 : Blo 2069435 4720151 := bstep (se 1 (by rfl) ⟨3540113, by rfl⟩ : syracuseStep 4720151 = 7080227) B7080227
theorem B12587069 : Blo 2069435 12587069 := bstep (se 3 (by rfl) ⟨2360075, by rfl⟩ : syracuseStep 12587069 = 4720151) B4720151
theorem B8391379 : Blo 2069435 8391379 := bstep (se 1 (by rfl) ⟨6293534, by rfl⟩ : syracuseStep 8391379 = 12587069) B12587069
theorem B11188505 : Blo 2069435 11188505 := bstep (se 2 (by rfl) ⟨4195689, by rfl⟩ : syracuseStep 11188505 = 8391379) B8391379
theorem B7459003 : Blo 2069435 7459003 := bstep (se 1 (by rfl) ⟨5594252, by rfl⟩ : syracuseStep 7459003 = 11188505) B11188505
theorem B9945337 : Blo 2069435 9945337 := bstep (se 2 (by rfl) ⟨3729501, by rfl⟩ : syracuseStep 9945337 = 7459003) B7459003
theorem B13260449 : Blo 2069435 13260449 := bstep (se 2 (by rfl) ⟨4972668, by rfl⟩ : syracuseStep 13260449 = 9945337) B9945337
theorem B8840299 : Blo 2069435 8840299 := bstep (se 1 (by rfl) ⟨6630224, by rfl⟩ : syracuseStep 8840299 = 13260449) B13260449
theorem B11787065 : Blo 2069435 11787065 := bstep (se 2 (by rfl) ⟨4420149, by rfl⟩ : syracuseStep 11787065 = 8840299) B8840299
theorem B7858043 : Blo 2069435 7858043 := bstep (se 1 (by rfl) ⟨5893532, by rfl⟩ : syracuseStep 7858043 = 11787065) B11787065
theorem B5238695 : Blo 2069435 5238695 := bstep (se 1 (by rfl) ⟨3929021, by rfl⟩ : syracuseStep 5238695 = 7858043) B7858043
theorem B3492463 : Blo 2069435 3492463 := bstep (se 1 (by rfl) ⟨2619347, by rfl⟩ : syracuseStep 3492463 = 5238695) B5238695
theorem B4656617 : Blo 2069435 4656617 := bstep (se 2 (by rfl) ⟨1746231, by rfl⟩ : syracuseStep 4656617 = 3492463) B3492463
theorem B3104411 : Blo 2069435 3104411 := bstep (se 1 (by rfl) ⟨2328308, by rfl⟩ : syracuseStep 3104411 = 4656617) B4656617
theorem B2069607 : Blo 2069435 2069607 := bstep (se 1 (by rfl) ⟨1552205, by rfl⟩ : syracuseStep 2069607 = 3104411) B3104411
theorem B2328313 : Blo 2069435 2328313 := bbase (se 2 (by rfl) ⟨873117, by rfl⟩ : syracuseStep 2328313 = 1746235) (by norm_num)
theorem B3104417 : Blo 2069435 3104417 := bstep (se 2 (by rfl) ⟨1164156, by rfl⟩ : syracuseStep 3104417 = 2328313) B2328313
theorem B2069611 : Blo 2069435 2069611 := bstep (se 1 (by rfl) ⟨1552208, by rfl⟩ : syracuseStep 2069611 = 3104417) B3104417
theorem B3315125 : Blo 2069435 3315125 := bbase (se 5 (by rfl) ⟨155396, by rfl⟩ : syracuseStep 3315125 = 310793) (by norm_num)
theorem B8840333 : Blo 2069435 8840333 := bstep (se 3 (by rfl) ⟨1657562, by rfl⟩ : syracuseStep 8840333 = 3315125) B3315125
theorem B5893555 : Blo 2069435 5893555 := bstep (se 1 (by rfl) ⟨4420166, by rfl⟩ : syracuseStep 5893555 = 8840333) B8840333
theorem B7858073 : Blo 2069435 7858073 := bstep (se 2 (by rfl) ⟨2946777, by rfl⟩ : syracuseStep 7858073 = 5893555) B5893555
theorem B5238715 : Blo 2069435 5238715 := bstep (se 1 (by rfl) ⟨3929036, by rfl⟩ : syracuseStep 5238715 = 7858073) B7858073
theorem B6984953 : Blo 2069435 6984953 := bstep (se 2 (by rfl) ⟨2619357, by rfl⟩ : syracuseStep 6984953 = 5238715) B5238715
theorem B4656635 : Blo 2069435 4656635 := bstep (se 1 (by rfl) ⟨3492476, by rfl⟩ : syracuseStep 4656635 = 6984953) B6984953
theorem B3104423 : Blo 2069435 3104423 := bstep (se 1 (by rfl) ⟨2328317, by rfl⟩ : syracuseStep 3104423 = 4656635) B4656635
theorem B2069615 : Blo 2069435 2069615 := bstep (se 1 (by rfl) ⟨1552211, by rfl⟩ : syracuseStep 2069615 = 3104423) B3104423
theorem B3104429 : Blo 2069435 3104429 := bbase (se 3 (by rfl) ⟨582080, by rfl⟩ : syracuseStep 3104429 = 1164161) (by norm_num)
theorem B2069619 : Blo 2069435 2069619 := bstep (se 1 (by rfl) ⟨1552214, by rfl⟩ : syracuseStep 2069619 = 3104429) B3104429
theorem B4656653 : Blo 2069435 4656653 := bbase (se 3 (by rfl) ⟨873122, by rfl⟩ : syracuseStep 4656653 = 1746245) (by norm_num)
theorem B3104435 : Blo 2069435 3104435 := bstep (se 1 (by rfl) ⟨2328326, by rfl⟩ : syracuseStep 3104435 = 4656653) B4656653
theorem B2069623 : Blo 2069435 2069623 := bstep (se 1 (by rfl) ⟨1552217, by rfl⟩ : syracuseStep 2069623 = 3104435) B3104435
theorem B2619373 : Blo 2069435 2619373 := bbase (se 3 (by rfl) ⟨491132, by rfl⟩ : syracuseStep 2619373 = 982265) (by norm_num)
theorem B3492497 : Blo 2069435 3492497 := bstep (se 2 (by rfl) ⟨1309686, by rfl⟩ : syracuseStep 3492497 = 2619373) B2619373
theorem B2328331 : Blo 2069435 2328331 := bstep (se 1 (by rfl) ⟨1746248, by rfl⟩ : syracuseStep 2328331 = 3492497) B3492497
theorem B3104441 : Blo 2069435 3104441 := bstep (se 2 (by rfl) ⟨1164165, by rfl⟩ : syracuseStep 3104441 = 2328331) B2328331
theorem B2069627 : Blo 2069435 2069627 := bstep (se 1 (by rfl) ⟨1552220, by rfl⟩ : syracuseStep 2069627 = 3104441) B3104441
theorem B4720205 : Blo 2069435 4720205 := bbase (se 3 (by rfl) ⟨885038, by rfl⟩ : syracuseStep 4720205 = 1770077) (by norm_num)
theorem B12587213 : Blo 2069435 12587213 := bstep (se 3 (by rfl) ⟨2360102, by rfl⟩ : syracuseStep 12587213 = 4720205) B4720205
theorem B8391475 : Blo 2069435 8391475 := bstep (se 1 (by rfl) ⟨6293606, by rfl⟩ : syracuseStep 8391475 = 12587213) B12587213
theorem B11188633 : Blo 2069435 11188633 := bstep (se 2 (by rfl) ⟨4195737, by rfl⟩ : syracuseStep 11188633 = 8391475) B8391475
theorem B14918177 : Blo 2069435 14918177 := bstep (se 2 (by rfl) ⟨5594316, by rfl⟩ : syracuseStep 14918177 = 11188633) B11188633
theorem B9945451 : Blo 2069435 9945451 := bstep (se 1 (by rfl) ⟨7459088, by rfl⟩ : syracuseStep 9945451 = 14918177) B14918177
theorem B13260601 : Blo 2069435 13260601 := bstep (se 2 (by rfl) ⟨4972725, by rfl⟩ : syracuseStep 13260601 = 9945451) B9945451
theorem B17680801 : Blo 2069435 17680801 := bstep (se 2 (by rfl) ⟨6630300, by rfl⟩ : syracuseStep 17680801 = 13260601) B13260601
theorem B23574401 : Blo 2069435 23574401 := bstep (se 2 (by rfl) ⟨8840400, by rfl⟩ : syracuseStep 23574401 = 17680801) B17680801
theorem B15716267 : Blo 2069435 15716267 := bstep (se 1 (by rfl) ⟨11787200, by rfl⟩ : syracuseStep 15716267 = 23574401) B23574401
theorem B10477511 : Blo 2069435 10477511 := bstep (se 1 (by rfl) ⟨7858133, by rfl⟩ : syracuseStep 10477511 = 15716267) B15716267
theorem B6985007 : Blo 2069435 6985007 := bstep (se 1 (by rfl) ⟨5238755, by rfl⟩ : syracuseStep 6985007 = 10477511) B10477511
theorem B4656671 : Blo 2069435 4656671 := bstep (se 1 (by rfl) ⟨3492503, by rfl⟩ : syracuseStep 4656671 = 6985007) B6985007
theorem B3104447 : Blo 2069435 3104447 := bstep (se 1 (by rfl) ⟨2328335, by rfl⟩ : syracuseStep 3104447 = 4656671) B4656671
theorem B2069631 : Blo 2069435 2069631 := bstep (se 1 (by rfl) ⟨1552223, by rfl⟩ : syracuseStep 2069631 = 3104447) B3104447
theorem B3104453 : Blo 2069435 3104453 := bbase (se 4 (by rfl) ⟨291042, by rfl⟩ : syracuseStep 3104453 = 582085) (by norm_num)
theorem B2069635 : Blo 2069435 2069635 := bstep (se 1 (by rfl) ⟨1552226, by rfl⟩ : syracuseStep 2069635 = 3104453) B3104453
theorem B3492517 : Blo 2069435 3492517 := bbase (se 4 (by rfl) ⟨327423, by rfl⟩ : syracuseStep 3492517 = 654847) (by norm_num)
theorem B4656689 : Blo 2069435 4656689 := bstep (se 2 (by rfl) ⟨1746258, by rfl⟩ : syracuseStep 4656689 = 3492517) B3492517
theorem B3104459 : Blo 2069435 3104459 := bstep (se 1 (by rfl) ⟨2328344, by rfl⟩ : syracuseStep 3104459 = 4656689) B4656689
theorem B2069639 : Blo 2069435 2069639 := bstep (se 1 (by rfl) ⟨1552229, by rfl⟩ : syracuseStep 2069639 = 3104459) B3104459
theorem B2328349 : Blo 2069435 2328349 := bbase (se 3 (by rfl) ⟨436565, by rfl⟩ : syracuseStep 2328349 = 873131) (by norm_num)
theorem B3104465 : Blo 2069435 3104465 := bstep (se 2 (by rfl) ⟨1164174, by rfl⟩ : syracuseStep 3104465 = 2328349) B2328349
theorem B2069643 : Blo 2069435 2069643 := bstep (se 1 (by rfl) ⟨1552232, by rfl⟩ : syracuseStep 2069643 = 3104465) B3104465
theorem B6985061 : Blo 2069435 6985061 := bbase (se 4 (by rfl) ⟨654849, by rfl⟩ : syracuseStep 6985061 = 1309699) (by norm_num)
theorem B4656707 : Blo 2069435 4656707 := bstep (se 1 (by rfl) ⟨3492530, by rfl⟩ : syracuseStep 4656707 = 6985061) B6985061
theorem B3104471 : Blo 2069435 3104471 := bstep (se 1 (by rfl) ⟨2328353, by rfl⟩ : syracuseStep 3104471 = 4656707) B4656707
theorem B2069647 : Blo 2069435 2069647 := bstep (se 1 (by rfl) ⟨1552235, by rfl⟩ : syracuseStep 2069647 = 3104471) B3104471
theorem B3104477 : Blo 2069435 3104477 := bbase (se 3 (by rfl) ⟨582089, by rfl⟩ : syracuseStep 3104477 = 1164179) (by norm_num)
theorem B2069651 : Blo 2069435 2069651 := bstep (se 1 (by rfl) ⟨1552238, by rfl⟩ : syracuseStep 2069651 = 3104477) B3104477
theorem B4656725 : Blo 2069435 4656725 := bbase (se 8 (by rfl) ⟨27285, by rfl⟩ : syracuseStep 4656725 = 54571) (by norm_num)
theorem B3104483 : Blo 2069435 3104483 := bstep (se 1 (by rfl) ⟨2328362, by rfl⟩ : syracuseStep 3104483 = 4656725) B4656725
theorem B2069655 : Blo 2069435 2069655 := bstep (se 1 (by rfl) ⟨1552241, by rfl⟩ : syracuseStep 2069655 = 3104483) B3104483
theorem B4420261 : Blo 2069435 4420261 := bbase (se 4 (by rfl) ⟨414399, by rfl⟩ : syracuseStep 4420261 = 828799) (by norm_num)
theorem B5893681 : Blo 2069435 5893681 := bstep (se 2 (by rfl) ⟨2210130, by rfl⟩ : syracuseStep 5893681 = 4420261) B4420261
theorem B7858241 : Blo 2069435 7858241 := bstep (se 2 (by rfl) ⟨2946840, by rfl⟩ : syracuseStep 7858241 = 5893681) B5893681
theorem B5238827 : Blo 2069435 5238827 := bstep (se 1 (by rfl) ⟨3929120, by rfl⟩ : syracuseStep 5238827 = 7858241) B7858241
theorem B3492551 : Blo 2069435 3492551 := bstep (se 1 (by rfl) ⟨2619413, by rfl⟩ : syracuseStep 3492551 = 5238827) B5238827
theorem B2328367 : Blo 2069435 2328367 := bstep (se 1 (by rfl) ⟨1746275, by rfl⟩ : syracuseStep 2328367 = 3492551) B3492551
theorem B3104489 : Blo 2069435 3104489 := bstep (se 2 (by rfl) ⟨1164183, by rfl⟩ : syracuseStep 3104489 = 2328367) B2328367
theorem B2069659 : Blo 2069435 2069659 := bstep (se 1 (by rfl) ⟨1552244, by rfl⟩ : syracuseStep 2069659 = 3104489) B3104489
theorem B9945605 : Blo 2069435 9945605 := bbase (se 4 (by rfl) ⟨932400, by rfl⟩ : syracuseStep 9945605 = 1864801) (by norm_num)
theorem B26521613 : Blo 2069435 26521613 := bstep (se 3 (by rfl) ⟨4972802, by rfl⟩ : syracuseStep 26521613 = 9945605) B9945605
theorem B17681075 : Blo 2069435 17681075 := bstep (se 1 (by rfl) ⟨13260806, by rfl⟩ : syracuseStep 17681075 = 26521613) B26521613
theorem B11787383 : Blo 2069435 11787383 := bstep (se 1 (by rfl) ⟨8840537, by rfl⟩ : syracuseStep 11787383 = 17681075) B17681075
theorem B7858255 : Blo 2069435 7858255 := bstep (se 1 (by rfl) ⟨5893691, by rfl⟩ : syracuseStep 7858255 = 11787383) B11787383
theorem B10477673 : Blo 2069435 10477673 := bstep (se 2 (by rfl) ⟨3929127, by rfl⟩ : syracuseStep 10477673 = 7858255) B7858255
theorem B6985115 : Blo 2069435 6985115 := bstep (se 1 (by rfl) ⟨5238836, by rfl⟩ : syracuseStep 6985115 = 10477673) B10477673
theorem B4656743 : Blo 2069435 4656743 := bstep (se 1 (by rfl) ⟨3492557, by rfl⟩ : syracuseStep 4656743 = 6985115) B6985115
theorem B3104495 : Blo 2069435 3104495 := bstep (se 1 (by rfl) ⟨2328371, by rfl⟩ : syracuseStep 3104495 = 4656743) B4656743
theorem B2069663 : Blo 2069435 2069663 := bstep (se 1 (by rfl) ⟨1552247, by rfl⟩ : syracuseStep 2069663 = 3104495) B3104495
theorem B3104501 : Blo 2069435 3104501 := bbase (se 5 (by rfl) ⟨145523, by rfl⟩ : syracuseStep 3104501 = 291047) (by norm_num)
theorem B2069667 : Blo 2069435 2069667 := bstep (se 1 (by rfl) ⟨1552250, by rfl⟩ : syracuseStep 2069667 = 3104501) B3104501
theorem B11188853 : Blo 2069435 11188853 := bbase (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) (by norm_num)
theorem B7459235 : Blo 2069435 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B4972823 : Blo 2069435 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B3315215 : Blo 2069435 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B8840573 : Blo 2069435 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B5893715 : Blo 2069435 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B3929143 : Blo 2069435 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B5238857 : Blo 2069435 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B3492571 : Blo 2069435 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B4656761 : Blo 2069435 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B3104507 : Blo 2069435 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B2069671 : Blo 2069435 2069671 := bstep (se 1 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 2069671 = 3104507) B3104507
theorem B2328385 : Blo 2069435 2328385 := bbase (se 2 (by rfl) ⟨873144, by rfl⟩ : syracuseStep 2328385 = 1746289) (by norm_num)
theorem B3104513 : Blo 2069435 3104513 := bstep (se 2 (by rfl) ⟨1164192, by rfl⟩ : syracuseStep 3104513 = 2328385) B2328385
theorem B2069675 : Blo 2069435 2069675 := bstep (se 1 (by rfl) ⟨1552256, by rfl⟩ : syracuseStep 2069675 = 3104513) B3104513
theorem B5238877 : Blo 2069435 5238877 := bbase (se 3 (by rfl) ⟨982289, by rfl⟩ : syracuseStep 5238877 = 1964579) (by norm_num)
theorem B6985169 : Blo 2069435 6985169 := bstep (se 2 (by rfl) ⟨2619438, by rfl⟩ : syracuseStep 6985169 = 5238877) B5238877
theorem B4656779 : Blo 2069435 4656779 := bstep (se 1 (by rfl) ⟨3492584, by rfl⟩ : syracuseStep 4656779 = 6985169) B6985169
theorem B3104519 : Blo 2069435 3104519 := bstep (se 1 (by rfl) ⟨2328389, by rfl⟩ : syracuseStep 3104519 = 4656779) B4656779
theorem B2069679 : Blo 2069435 2069679 := bstep (se 1 (by rfl) ⟨1552259, by rfl⟩ : syracuseStep 2069679 = 3104519) B3104519
theorem B3104525 : Blo 2069435 3104525 := bbase (se 3 (by rfl) ⟨582098, by rfl⟩ : syracuseStep 3104525 = 1164197) (by norm_num)
theorem B2069683 : Blo 2069435 2069683 := bstep (se 1 (by rfl) ⟨1552262, by rfl⟩ : syracuseStep 2069683 = 3104525) B3104525
theorem B4656797 : Blo 2069435 4656797 := bbase (se 3 (by rfl) ⟨873149, by rfl⟩ : syracuseStep 4656797 = 1746299) (by norm_num)
theorem B3104531 : Blo 2069435 3104531 := bstep (se 1 (by rfl) ⟨2328398, by rfl⟩ : syracuseStep 3104531 = 4656797) B4656797
theorem B2069687 : Blo 2069435 2069687 := bstep (se 1 (by rfl) ⟨1552265, by rfl⟩ : syracuseStep 2069687 = 3104531) B3104531
theorem B3492605 : Blo 2069435 3492605 := bbase (se 3 (by rfl) ⟨654863, by rfl⟩ : syracuseStep 3492605 = 1309727) (by norm_num)
theorem B2328403 : Blo 2069435 2328403 := bstep (se 1 (by rfl) ⟨1746302, by rfl⟩ : syracuseStep 2328403 = 3492605) B3492605
theorem B3104537 : Blo 2069435 3104537 := bstep (se 2 (by rfl) ⟨1164201, by rfl⟩ : syracuseStep 3104537 = 2328403) B2328403
theorem B2069691 : Blo 2069435 2069691 := bstep (se 1 (by rfl) ⟨1552268, by rfl⟩ : syracuseStep 2069691 = 3104537) B3104537
theorem B3315253 : Blo 2069435 3315253 := bbase (se 5 (by rfl) ⟨155402, by rfl⟩ : syracuseStep 3315253 = 310805) (by norm_num)
theorem B4420337 : Blo 2069435 4420337 := bstep (se 2 (by rfl) ⟨1657626, by rfl⟩ : syracuseStep 4420337 = 3315253) B3315253
theorem B11787565 : Blo 2069435 11787565 := bstep (se 3 (by rfl) ⟨2210168, by rfl⟩ : syracuseStep 11787565 = 4420337) B4420337
theorem B15716753 : Blo 2069435 15716753 := bstep (se 2 (by rfl) ⟨5893782, by rfl⟩ : syracuseStep 15716753 = 11787565) B11787565
theorem B10477835 : Blo 2069435 10477835 := bstep (se 1 (by rfl) ⟨7858376, by rfl⟩ : syracuseStep 10477835 = 15716753) B15716753
theorem B6985223 : Blo 2069435 6985223 := bstep (se 1 (by rfl) ⟨5238917, by rfl⟩ : syracuseStep 6985223 = 10477835) B10477835
theorem B4656815 : Blo 2069435 4656815 := bstep (se 1 (by rfl) ⟨3492611, by rfl⟩ : syracuseStep 4656815 = 6985223) B6985223
theorem B3104543 : Blo 2069435 3104543 := bstep (se 1 (by rfl) ⟨2328407, by rfl⟩ : syracuseStep 3104543 = 4656815) B4656815
theorem B2069695 : Blo 2069435 2069695 := bstep (se 1 (by rfl) ⟨1552271, by rfl⟩ : syracuseStep 2069695 = 3104543) B3104543
theorem B3104549 : Blo 2069435 3104549 := bbase (se 4 (by rfl) ⟨291051, by rfl⟩ : syracuseStep 3104549 = 582103) (by norm_num)
theorem B2069699 : Blo 2069435 2069699 := bstep (se 1 (by rfl) ⟨1552274, by rfl⟩ : syracuseStep 2069699 = 3104549) B3104549
theorem B2619469 : Blo 2069435 2619469 := bbase (se 3 (by rfl) ⟨491150, by rfl⟩ : syracuseStep 2619469 = 982301) (by norm_num)
theorem B3492625 : Blo 2069435 3492625 := bstep (se 2 (by rfl) ⟨1309734, by rfl⟩ : syracuseStep 3492625 = 2619469) B2619469
theorem B4656833 : Blo 2069435 4656833 := bstep (se 2 (by rfl) ⟨1746312, by rfl⟩ : syracuseStep 4656833 = 3492625) B3492625
theorem B3104555 : Blo 2069435 3104555 := bstep (se 1 (by rfl) ⟨2328416, by rfl⟩ : syracuseStep 3104555 = 4656833) B4656833
theorem B2069703 : Blo 2069435 2069703 := bstep (se 1 (by rfl) ⟨1552277, by rfl⟩ : syracuseStep 2069703 = 3104555) B3104555
theorem B2328421 : Blo 2069435 2328421 := bbase (se 4 (by rfl) ⟨218289, by rfl⟩ : syracuseStep 2328421 = 436579) (by norm_num)
theorem B3104561 : Blo 2069435 3104561 := bstep (se 2 (by rfl) ⟨1164210, by rfl⟩ : syracuseStep 3104561 = 2328421) B2328421
theorem B2069707 : Blo 2069435 2069707 := bstep (se 1 (by rfl) ⟨1552280, by rfl⟩ : syracuseStep 2069707 = 3104561) B3104561
theorem B5893829 : Blo 2069435 5893829 := bbase (se 4 (by rfl) ⟨552546, by rfl⟩ : syracuseStep 5893829 = 1105093) (by norm_num)
theorem B3929219 : Blo 2069435 3929219 := bstep (se 1 (by rfl) ⟨2946914, by rfl⟩ : syracuseStep 3929219 = 5893829) B5893829
theorem B2619479 : Blo 2069435 2619479 := bstep (se 1 (by rfl) ⟨1964609, by rfl⟩ : syracuseStep 2619479 = 3929219) B3929219
theorem B6985277 : Blo 2069435 6985277 := bstep (se 3 (by rfl) ⟨1309739, by rfl⟩ : syracuseStep 6985277 = 2619479) B2619479
theorem B4656851 : Blo 2069435 4656851 := bstep (se 1 (by rfl) ⟨3492638, by rfl⟩ : syracuseStep 4656851 = 6985277) B6985277
theorem B3104567 : Blo 2069435 3104567 := bstep (se 1 (by rfl) ⟨2328425, by rfl⟩ : syracuseStep 3104567 = 4656851) B4656851
theorem B2069711 : Blo 2069435 2069711 := bstep (se 1 (by rfl) ⟨1552283, by rfl⟩ : syracuseStep 2069711 = 3104567) B3104567
theorem B3104573 : Blo 2069435 3104573 := bbase (se 3 (by rfl) ⟨582107, by rfl⟩ : syracuseStep 3104573 = 1164215) (by norm_num)
theorem B2069715 : Blo 2069435 2069715 := bstep (se 1 (by rfl) ⟨1552286, by rfl⟩ : syracuseStep 2069715 = 3104573) B3104573
theorem B4656869 : Blo 2069435 4656869 := bbase (se 4 (by rfl) ⟨436581, by rfl⟩ : syracuseStep 4656869 = 873163) (by norm_num)
theorem B3104579 : Blo 2069435 3104579 := bstep (se 1 (by rfl) ⟨2328434, by rfl⟩ : syracuseStep 3104579 = 4656869) B4656869
theorem B2069719 : Blo 2069435 2069719 := bstep (se 1 (by rfl) ⟨1552289, by rfl⟩ : syracuseStep 2069719 = 3104579) B3104579
theorem B5238989 : Blo 2069435 5238989 := bbase (se 3 (by rfl) ⟨982310, by rfl⟩ : syracuseStep 5238989 = 1964621) (by norm_num)
theorem B3492659 : Blo 2069435 3492659 := bstep (se 1 (by rfl) ⟨2619494, by rfl⟩ : syracuseStep 3492659 = 5238989) B5238989
theorem B2328439 : Blo 2069435 2328439 := bstep (se 1 (by rfl) ⟨1746329, by rfl⟩ : syracuseStep 2328439 = 3492659) B3492659
theorem B3104585 : Blo 2069435 3104585 := bstep (se 2 (by rfl) ⟨1164219, by rfl⟩ : syracuseStep 3104585 = 2328439) B2328439
theorem B2069723 : Blo 2069435 2069723 := bstep (se 1 (by rfl) ⟨1552292, by rfl⟩ : syracuseStep 2069723 = 3104585) B3104585
theorem B3982861 : Blo 2069435 3982861 := bbase (se 3 (by rfl) ⟨746786, by rfl⟩ : syracuseStep 3982861 = 1493573) (by norm_num)
theorem B5310481 : Blo 2069435 5310481 := bstep (se 2 (by rfl) ⟨1991430, by rfl⟩ : syracuseStep 5310481 = 3982861) B3982861
theorem B7080641 : Blo 2069435 7080641 := bstep (se 2 (by rfl) ⟨2655240, by rfl⟩ : syracuseStep 7080641 = 5310481) B5310481
theorem B4720427 : Blo 2069435 4720427 := bstep (se 1 (by rfl) ⟨3540320, by rfl⟩ : syracuseStep 4720427 = 7080641) B7080641
theorem B3146951 : Blo 2069435 3146951 := bstep (se 1 (by rfl) ⟨2360213, by rfl⟩ : syracuseStep 3146951 = 4720427) B4720427
theorem B8391869 : Blo 2069435 8391869 := bstep (se 3 (by rfl) ⟨1573475, by rfl⟩ : syracuseStep 8391869 = 3146951) B3146951
theorem B5594579 : Blo 2069435 5594579 := bstep (se 1 (by rfl) ⟨4195934, by rfl⟩ : syracuseStep 5594579 = 8391869) B8391869
theorem B3729719 : Blo 2069435 3729719 := bstep (se 1 (by rfl) ⟨2797289, by rfl⟩ : syracuseStep 3729719 = 5594579) B5594579
theorem B2486479 : Blo 2069435 2486479 := bstep (se 1 (by rfl) ⟨1864859, by rfl⟩ : syracuseStep 2486479 = 3729719) B3729719
theorem B3315305 : Blo 2069435 3315305 := bstep (se 2 (by rfl) ⟨1243239, by rfl⟩ : syracuseStep 3315305 = 2486479) B2486479
theorem B2210203 : Blo 2069435 2210203 := bstep (se 1 (by rfl) ⟨1657652, by rfl⟩ : syracuseStep 2210203 = 3315305) B3315305
theorem B2946937 : Blo 2069435 2946937 := bstep (se 2 (by rfl) ⟨1105101, by rfl⟩ : syracuseStep 2946937 = 2210203) B2210203
theorem B3929249 : Blo 2069435 3929249 := bstep (se 2 (by rfl) ⟨1473468, by rfl⟩ : syracuseStep 3929249 = 2946937) B2946937
theorem B10477997 : Blo 2069435 10477997 := bstep (se 3 (by rfl) ⟨1964624, by rfl⟩ : syracuseStep 10477997 = 3929249) B3929249
theorem B6985331 : Blo 2069435 6985331 := bstep (se 1 (by rfl) ⟨5238998, by rfl⟩ : syracuseStep 6985331 = 10477997) B10477997
theorem B4656887 : Blo 2069435 4656887 := bstep (se 1 (by rfl) ⟨3492665, by rfl⟩ : syracuseStep 4656887 = 6985331) B6985331
theorem B3104591 : Blo 2069435 3104591 := bstep (se 1 (by rfl) ⟨2328443, by rfl⟩ : syracuseStep 3104591 = 4656887) B4656887
theorem B2069727 : Blo 2069435 2069727 := bstep (se 1 (by rfl) ⟨1552295, by rfl⟩ : syracuseStep 2069727 = 3104591) B3104591
theorem B3104597 : Blo 2069435 3104597 := bbase (se 9 (by rfl) ⟨9095, by rfl⟩ : syracuseStep 3104597 = 18191) (by norm_num)
theorem B2069731 : Blo 2069435 2069731 := bstep (se 1 (by rfl) ⟨1552298, by rfl⟩ : syracuseStep 2069731 = 3104597) B3104597
theorem B7965749 : Blo 2069435 7965749 := bbase (se 5 (by rfl) ⟨373394, by rfl⟩ : syracuseStep 7965749 = 746789) (by norm_num)
theorem B21241997 : Blo 2069435 21241997 := bstep (se 3 (by rfl) ⟨3982874, by rfl⟩ : syracuseStep 21241997 = 7965749) B7965749
theorem B14161331 : Blo 2069435 14161331 := bstep (se 1 (by rfl) ⟨10620998, by rfl⟩ : syracuseStep 14161331 = 21241997) B21241997
theorem B9440887 : Blo 2069435 9440887 := bstep (se 1 (by rfl) ⟨7080665, by rfl⟩ : syracuseStep 9440887 = 14161331) B14161331
theorem B12587849 : Blo 2069435 12587849 := bstep (se 2 (by rfl) ⟨4720443, by rfl⟩ : syracuseStep 12587849 = 9440887) B9440887
theorem B8391899 : Blo 2069435 8391899 := bstep (se 1 (by rfl) ⟨6293924, by rfl⟩ : syracuseStep 8391899 = 12587849) B12587849
theorem B5594599 : Blo 2069435 5594599 := bstep (se 1 (by rfl) ⟨4195949, by rfl⟩ : syracuseStep 5594599 = 8391899) B8391899
theorem B7459465 : Blo 2069435 7459465 := bstep (se 2 (by rfl) ⟨2797299, by rfl⟩ : syracuseStep 7459465 = 5594599) B5594599
theorem B9945953 : Blo 2069435 9945953 := bstep (se 2 (by rfl) ⟨3729732, by rfl⟩ : syracuseStep 9945953 = 7459465) B7459465
theorem B6630635 : Blo 2069435 6630635 := bstep (se 1 (by rfl) ⟨4972976, by rfl⟩ : syracuseStep 6630635 = 9945953) B9945953
theorem B4420423 : Blo 2069435 4420423 := bstep (se 1 (by rfl) ⟨3315317, by rfl⟩ : syracuseStep 4420423 = 6630635) B6630635
theorem B5893897 : Blo 2069435 5893897 := bstep (se 2 (by rfl) ⟨2210211, by rfl⟩ : syracuseStep 5893897 = 4420423) B4420423
theorem B7858529 : Blo 2069435 7858529 := bstep (se 2 (by rfl) ⟨2946948, by rfl⟩ : syracuseStep 7858529 = 5893897) B5893897
theorem B5239019 : Blo 2069435 5239019 := bstep (se 1 (by rfl) ⟨3929264, by rfl⟩ : syracuseStep 5239019 = 7858529) B7858529
theorem B3492679 : Blo 2069435 3492679 := bstep (se 1 (by rfl) ⟨2619509, by rfl⟩ : syracuseStep 3492679 = 5239019) B5239019
theorem B4656905 : Blo 2069435 4656905 := bstep (se 2 (by rfl) ⟨1746339, by rfl⟩ : syracuseStep 4656905 = 3492679) B3492679
theorem B3104603 : Blo 2069435 3104603 := bstep (se 1 (by rfl) ⟨2328452, by rfl⟩ : syracuseStep 3104603 = 4656905) B4656905
theorem B2069735 : Blo 2069435 2069735 := bstep (se 1 (by rfl) ⟨1552301, by rfl⟩ : syracuseStep 2069735 = 3104603) B3104603
theorem B2328457 : Blo 2069435 2328457 := bbase (se 2 (by rfl) ⟨873171, by rfl⟩ : syracuseStep 2328457 = 1746343) (by norm_num)
theorem B3104609 : Blo 2069435 3104609 := bstep (se 2 (by rfl) ⟨1164228, by rfl⟩ : syracuseStep 3104609 = 2328457) B2328457
theorem B2069739 : Blo 2069435 2069739 := bstep (se 1 (by rfl) ⟨1552304, by rfl⟩ : syracuseStep 2069739 = 3104609) B3104609
theorem B19400597 : Blo 2069435 19400597 := bbase (se 6 (by rfl) ⟨454701, by rfl⟩ : syracuseStep 19400597 = 909403) (by norm_num)
theorem B12933731 : Blo 2069435 12933731 := bstep (se 1 (by rfl) ⟨9700298, by rfl⟩ : syracuseStep 12933731 = 19400597) B19400597
theorem B8622487 : Blo 2069435 8622487 := bstep (se 1 (by rfl) ⟨6466865, by rfl⟩ : syracuseStep 8622487 = 12933731) B12933731
theorem B11496649 : Blo 2069435 11496649 := bstep (se 2 (by rfl) ⟨4311243, by rfl⟩ : syracuseStep 11496649 = 8622487) B8622487
theorem B15328865 : Blo 2069435 15328865 := bstep (se 2 (by rfl) ⟨5748324, by rfl⟩ : syracuseStep 15328865 = 11496649) B11496649
theorem B10219243 : Blo 2069435 10219243 := bstep (se 1 (by rfl) ⟨7664432, by rfl⟩ : syracuseStep 10219243 = 15328865) B15328865
theorem B13625657 : Blo 2069435 13625657 := bstep (se 2 (by rfl) ⟨5109621, by rfl⟩ : syracuseStep 13625657 = 10219243) B10219243
theorem B9083771 : Blo 2069435 9083771 := bstep (se 1 (by rfl) ⟨6812828, by rfl⟩ : syracuseStep 9083771 = 13625657) B13625657
theorem B6055847 : Blo 2069435 6055847 := bstep (se 1 (by rfl) ⟨4541885, by rfl⟩ : syracuseStep 6055847 = 9083771) B9083771
theorem B4037231 : Blo 2069435 4037231 := bstep (se 1 (by rfl) ⟨3027923, by rfl⟩ : syracuseStep 4037231 = 6055847) B6055847
theorem B2691487 : Blo 2069435 2691487 := bstep (se 1 (by rfl) ⟨2018615, by rfl⟩ : syracuseStep 2691487 = 4037231) B4037231
theorem B14354597 : Blo 2069435 14354597 := bstep (se 4 (by rfl) ⟨1345743, by rfl⟩ : syracuseStep 14354597 = 2691487) B2691487
theorem B38278925 : Blo 2069435 38278925 := bstep (se 3 (by rfl) ⟨7177298, by rfl⟩ : syracuseStep 38278925 = 14354597) B14354597
theorem B25519283 : Blo 2069435 25519283 := bstep (se 1 (by rfl) ⟨19139462, by rfl⟩ : syracuseStep 25519283 = 38278925) B38278925
theorem B17012855 : Blo 2069435 17012855 := bstep (se 1 (by rfl) ⟨12759641, by rfl⟩ : syracuseStep 17012855 = 25519283) B25519283
theorem B11341903 : Blo 2069435 11341903 := bstep (se 1 (by rfl) ⟨8506427, by rfl⟩ : syracuseStep 11341903 = 17012855) B17012855
theorem B15122537 : Blo 2069435 15122537 := bstep (se 2 (by rfl) ⟨5670951, by rfl⟩ : syracuseStep 15122537 = 11341903) B11341903
theorem B10081691 : Blo 2069435 10081691 := bstep (se 1 (by rfl) ⟨7561268, by rfl⟩ : syracuseStep 10081691 = 15122537) B15122537
theorem B6721127 : Blo 2069435 6721127 := bstep (se 1 (by rfl) ⟨5040845, by rfl⟩ : syracuseStep 6721127 = 10081691) B10081691
theorem B4480751 : Blo 2069435 4480751 := bstep (se 1 (by rfl) ⟨3360563, by rfl⟩ : syracuseStep 4480751 = 6721127) B6721127
theorem B2987167 : Blo 2069435 2987167 := bstep (se 1 (by rfl) ⟨2240375, by rfl⟩ : syracuseStep 2987167 = 4480751) B4480751
theorem B3982889 : Blo 2069435 3982889 := bstep (se 2 (by rfl) ⟨1493583, by rfl⟩ : syracuseStep 3982889 = 2987167) B2987167
theorem B10621037 : Blo 2069435 10621037 := bstep (se 3 (by rfl) ⟨1991444, by rfl⟩ : syracuseStep 10621037 = 3982889) B3982889
theorem B7080691 : Blo 2069435 7080691 := bstep (se 1 (by rfl) ⟨5310518, by rfl⟩ : syracuseStep 7080691 = 10621037) B10621037
theorem B9440921 : Blo 2069435 9440921 := bstep (se 2 (by rfl) ⟨3540345, by rfl⟩ : syracuseStep 9440921 = 7080691) B7080691
theorem B6293947 : Blo 2069435 6293947 := bstep (se 1 (by rfl) ⟨4720460, by rfl⟩ : syracuseStep 6293947 = 9440921) B9440921
theorem B8391929 : Blo 2069435 8391929 := bstep (se 2 (by rfl) ⟨3146973, by rfl⟩ : syracuseStep 8391929 = 6293947) B6293947
theorem B89513909 : Blo 2069435 89513909 := bstep (se 5 (by rfl) ⟨4195964, by rfl⟩ : syracuseStep 89513909 = 8391929) B8391929
theorem B59675939 : Blo 2069435 59675939 := bstep (se 1 (by rfl) ⟨44756954, by rfl⟩ : syracuseStep 59675939 = 89513909) B89513909
theorem B39783959 : Blo 2069435 39783959 := bstep (se 1 (by rfl) ⟨29837969, by rfl⟩ : syracuseStep 39783959 = 59675939) B59675939
theorem B26522639 : Blo 2069435 26522639 := bstep (se 1 (by rfl) ⟨19891979, by rfl⟩ : syracuseStep 26522639 = 39783959) B39783959
theorem B17681759 : Blo 2069435 17681759 := bstep (se 1 (by rfl) ⟨13261319, by rfl⟩ : syracuseStep 17681759 = 26522639) B26522639
theorem B11787839 : Blo 2069435 11787839 := bstep (se 1 (by rfl) ⟨8840879, by rfl⟩ : syracuseStep 11787839 = 17681759) B17681759
theorem B7858559 : Blo 2069435 7858559 := bstep (se 1 (by rfl) ⟨5893919, by rfl⟩ : syracuseStep 7858559 = 11787839) B11787839
theorem B5239039 : Blo 2069435 5239039 := bstep (se 1 (by rfl) ⟨3929279, by rfl⟩ : syracuseStep 5239039 = 7858559) B7858559
theorem B6985385 : Blo 2069435 6985385 := bstep (se 2 (by rfl) ⟨2619519, by rfl⟩ : syracuseStep 6985385 = 5239039) B5239039
theorem B4656923 : Blo 2069435 4656923 := bstep (se 1 (by rfl) ⟨3492692, by rfl⟩ : syracuseStep 4656923 = 6985385) B6985385
theorem B3104615 : Blo 2069435 3104615 := bstep (se 1 (by rfl) ⟨2328461, by rfl⟩ : syracuseStep 3104615 = 4656923) B4656923
theorem B2069743 : Blo 2069435 2069743 := bstep (se 1 (by rfl) ⟨1552307, by rfl⟩ : syracuseStep 2069743 = 3104615) B3104615
theorem B3104621 : Blo 2069435 3104621 := bbase (se 3 (by rfl) ⟨582116, by rfl⟩ : syracuseStep 3104621 = 1164233) (by norm_num)
theorem B2069747 : Blo 2069435 2069747 := bstep (se 1 (by rfl) ⟨1552310, by rfl⟩ : syracuseStep 2069747 = 3104621) B3104621
theorem B4656941 : Blo 2069435 4656941 := bbase (se 3 (by rfl) ⟨873176, by rfl⟩ : syracuseStep 4656941 = 1746353) (by norm_num)
theorem B3104627 : Blo 2069435 3104627 := bstep (se 1 (by rfl) ⟨2328470, by rfl⟩ : syracuseStep 3104627 = 4656941) B4656941
theorem B2069751 : Blo 2069435 2069751 := bstep (se 1 (by rfl) ⟨1552313, by rfl⟩ : syracuseStep 2069751 = 3104627) B3104627
theorem B8840933 : Blo 2069435 8840933 := bbase (se 4 (by rfl) ⟨828837, by rfl⟩ : syracuseStep 8840933 = 1657675) (by norm_num)
theorem B5893955 : Blo 2069435 5893955 := bstep (se 1 (by rfl) ⟨4420466, by rfl⟩ : syracuseStep 5893955 = 8840933) B8840933
theorem B3929303 : Blo 2069435 3929303 := bstep (se 1 (by rfl) ⟨2946977, by rfl⟩ : syracuseStep 3929303 = 5893955) B5893955
theorem B2619535 : Blo 2069435 2619535 := bstep (se 1 (by rfl) ⟨1964651, by rfl⟩ : syracuseStep 2619535 = 3929303) B3929303
theorem B3492713 : Blo 2069435 3492713 := bstep (se 2 (by rfl) ⟨1309767, by rfl⟩ : syracuseStep 3492713 = 2619535) B2619535
theorem B2328475 : Blo 2069435 2328475 := bstep (se 1 (by rfl) ⟨1746356, by rfl⟩ : syracuseStep 2328475 = 3492713) B3492713
theorem B3104633 : Blo 2069435 3104633 := bstep (se 2 (by rfl) ⟨1164237, by rfl⟩ : syracuseStep 3104633 = 2328475) B2328475
theorem B2069755 : Blo 2069435 2069755 := bstep (se 1 (by rfl) ⟨1552316, by rfl⟩ : syracuseStep 2069755 = 3104633) B3104633
theorem B14161493 : Blo 2069435 14161493 := bbase (se 8 (by rfl) ⟨82977, by rfl⟩ : syracuseStep 14161493 = 165955) (by norm_num)
theorem B9440995 : Blo 2069435 9440995 := bstep (se 1 (by rfl) ⟨7080746, by rfl⟩ : syracuseStep 9440995 = 14161493) B14161493
theorem B12587993 : Blo 2069435 12587993 := bstep (se 2 (by rfl) ⟨4720497, by rfl⟩ : syracuseStep 12587993 = 9440995) B9440995
theorem B8391995 : Blo 2069435 8391995 := bstep (se 1 (by rfl) ⟨6293996, by rfl⟩ : syracuseStep 8391995 = 12587993) B12587993
theorem B5594663 : Blo 2069435 5594663 := bstep (se 1 (by rfl) ⟨4195997, by rfl⟩ : syracuseStep 5594663 = 8391995) B8391995
theorem B3729775 : Blo 2069435 3729775 := bstep (se 1 (by rfl) ⟨2797331, by rfl⟩ : syracuseStep 3729775 = 5594663) B5594663
theorem B4973033 : Blo 2069435 4973033 := bstep (se 2 (by rfl) ⟨1864887, by rfl⟩ : syracuseStep 4973033 = 3729775) B3729775
theorem B13261421 : Blo 2069435 13261421 := bstep (se 3 (by rfl) ⟨2486516, by rfl⟩ : syracuseStep 13261421 = 4973033) B4973033
theorem B35363789 : Blo 2069435 35363789 := bstep (se 3 (by rfl) ⟨6630710, by rfl⟩ : syracuseStep 35363789 = 13261421) B13261421
theorem B23575859 : Blo 2069435 23575859 := bstep (se 1 (by rfl) ⟨17681894, by rfl⟩ : syracuseStep 23575859 = 35363789) B35363789
theorem B15717239 : Blo 2069435 15717239 := bstep (se 1 (by rfl) ⟨11787929, by rfl⟩ : syracuseStep 15717239 = 23575859) B23575859
theorem B10478159 : Blo 2069435 10478159 := bstep (se 1 (by rfl) ⟨7858619, by rfl⟩ : syracuseStep 10478159 = 15717239) B15717239
theorem B6985439 : Blo 2069435 6985439 := bstep (se 1 (by rfl) ⟨5239079, by rfl⟩ : syracuseStep 6985439 = 10478159) B10478159
theorem B4656959 : Blo 2069435 4656959 := bstep (se 1 (by rfl) ⟨3492719, by rfl⟩ : syracuseStep 4656959 = 6985439) B6985439
theorem B3104639 : Blo 2069435 3104639 := bstep (se 1 (by rfl) ⟨2328479, by rfl⟩ : syracuseStep 3104639 = 4656959) B4656959
theorem B2069759 : Blo 2069435 2069759 := bstep (se 1 (by rfl) ⟨1552319, by rfl⟩ : syracuseStep 2069759 = 3104639) B3104639
theorem B3104645 : Blo 2069435 3104645 := bbase (se 4 (by rfl) ⟨291060, by rfl⟩ : syracuseStep 3104645 = 582121) (by norm_num)
theorem B2069763 : Blo 2069435 2069763 := bstep (se 1 (by rfl) ⟨1552322, by rfl⟩ : syracuseStep 2069763 = 3104645) B3104645
theorem B3492733 : Blo 2069435 3492733 := bbase (se 3 (by rfl) ⟨654887, by rfl⟩ : syracuseStep 3492733 = 1309775) (by norm_num)
theorem B4656977 : Blo 2069435 4656977 := bstep (se 2 (by rfl) ⟨1746366, by rfl⟩ : syracuseStep 4656977 = 3492733) B3492733
theorem B3104651 : Blo 2069435 3104651 := bstep (se 1 (by rfl) ⟨2328488, by rfl⟩ : syracuseStep 3104651 = 4656977) B4656977
theorem B2069767 : Blo 2069435 2069767 := bstep (se 1 (by rfl) ⟨1552325, by rfl⟩ : syracuseStep 2069767 = 3104651) B3104651
theorem B2328493 : Blo 2069435 2328493 := bbase (se 3 (by rfl) ⟨436592, by rfl⟩ : syracuseStep 2328493 = 873185) (by norm_num)
theorem B3104657 : Blo 2069435 3104657 := bstep (se 2 (by rfl) ⟨1164246, by rfl⟩ : syracuseStep 3104657 = 2328493) B2328493
theorem B2069771 : Blo 2069435 2069771 := bstep (se 1 (by rfl) ⟨1552328, by rfl⟩ : syracuseStep 2069771 = 3104657) B3104657
theorem B6985493 : Blo 2069435 6985493 := bbase (se 6 (by rfl) ⟨163722, by rfl⟩ : syracuseStep 6985493 = 327445) (by norm_num)
theorem B4656995 : Blo 2069435 4656995 := bstep (se 1 (by rfl) ⟨3492746, by rfl⟩ : syracuseStep 4656995 = 6985493) B6985493
theorem B3104663 : Blo 2069435 3104663 := bstep (se 1 (by rfl) ⟨2328497, by rfl⟩ : syracuseStep 3104663 = 4656995) B4656995
theorem B2069775 : Blo 2069435 2069775 := bstep (se 1 (by rfl) ⟨1552331, by rfl⟩ : syracuseStep 2069775 = 3104663) B3104663
theorem B3104669 : Blo 2069435 3104669 := bbase (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) (by norm_num)
theorem B2069779 : Blo 2069435 2069779 := bstep (se 1 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 2069779 = 3104669) B3104669
theorem B4657013 : Blo 2069435 4657013 := bbase (se 5 (by rfl) ⟨218297, by rfl⟩ : syracuseStep 4657013 = 436595) (by norm_num)
theorem B3104675 : Blo 2069435 3104675 := bstep (se 1 (by rfl) ⟨2328506, by rfl⟩ : syracuseStep 3104675 = 4657013) B4657013
theorem B2069783 : Blo 2069435 2069783 := bstep (se 1 (by rfl) ⟨1552337, by rfl⟩ : syracuseStep 2069783 = 3104675) B3104675
theorem B19892405 : Blo 2069435 19892405 := bbase (se 5 (by rfl) ⟨932456, by rfl⟩ : syracuseStep 19892405 = 1864913) (by norm_num)
theorem B13261603 : Blo 2069435 13261603 := bstep (se 1 (by rfl) ⟨9946202, by rfl⟩ : syracuseStep 13261603 = 19892405) B19892405
theorem B17682137 : Blo 2069435 17682137 := bstep (se 2 (by rfl) ⟨6630801, by rfl⟩ : syracuseStep 17682137 = 13261603) B13261603
theorem B11788091 : Blo 2069435 11788091 := bstep (se 1 (by rfl) ⟨8841068, by rfl⟩ : syracuseStep 11788091 = 17682137) B17682137
theorem B7858727 : Blo 2069435 7858727 := bstep (se 1 (by rfl) ⟨5894045, by rfl⟩ : syracuseStep 7858727 = 11788091) B11788091
theorem B5239151 : Blo 2069435 5239151 := bstep (se 1 (by rfl) ⟨3929363, by rfl⟩ : syracuseStep 5239151 = 7858727) B7858727
theorem B3492767 : Blo 2069435 3492767 := bstep (se 1 (by rfl) ⟨2619575, by rfl⟩ : syracuseStep 3492767 = 5239151) B5239151
theorem B2328511 : Blo 2069435 2328511 := bstep (se 1 (by rfl) ⟨1746383, by rfl⟩ : syracuseStep 2328511 = 3492767) B3492767
theorem B3104681 : Blo 2069435 3104681 := bstep (se 2 (by rfl) ⟨1164255, by rfl⟩ : syracuseStep 3104681 = 2328511) B2328511
theorem B2069787 : Blo 2069435 2069787 := bstep (se 1 (by rfl) ⟨1552340, by rfl⟩ : syracuseStep 2069787 = 3104681) B3104681
theorem B7858741 : Blo 2069435 7858741 := bbase (se 5 (by rfl) ⟨368378, by rfl⟩ : syracuseStep 7858741 = 736757) (by norm_num)
theorem B10478321 : Blo 2069435 10478321 := bstep (se 2 (by rfl) ⟨3929370, by rfl⟩ : syracuseStep 10478321 = 7858741) B7858741
theorem B6985547 : Blo 2069435 6985547 := bstep (se 1 (by rfl) ⟨5239160, by rfl⟩ : syracuseStep 6985547 = 10478321) B10478321
theorem B4657031 : Blo 2069435 4657031 := bstep (se 1 (by rfl) ⟨3492773, by rfl⟩ : syracuseStep 4657031 = 6985547) B6985547
theorem B3104687 : Blo 2069435 3104687 := bstep (se 1 (by rfl) ⟨2328515, by rfl⟩ : syracuseStep 3104687 = 4657031) B4657031
theorem B2069791 : Blo 2069435 2069791 := bstep (se 1 (by rfl) ⟨1552343, by rfl⟩ : syracuseStep 2069791 = 3104687) B3104687
theorem B3104693 : Blo 2069435 3104693 := bbase (se 5 (by rfl) ⟨145532, by rfl⟩ : syracuseStep 3104693 = 291065) (by norm_num)
theorem B2069795 : Blo 2069435 2069795 := bstep (se 1 (by rfl) ⟨1552346, by rfl⟩ : syracuseStep 2069795 = 3104693) B3104693
theorem B5239181 : Blo 2069435 5239181 := bbase (se 3 (by rfl) ⟨982346, by rfl⟩ : syracuseStep 5239181 = 1964693) (by norm_num)
theorem B3492787 : Blo 2069435 3492787 := bstep (se 1 (by rfl) ⟨2619590, by rfl⟩ : syracuseStep 3492787 = 5239181) B5239181
theorem B4657049 : Blo 2069435 4657049 := bstep (se 2 (by rfl) ⟨1746393, by rfl⟩ : syracuseStep 4657049 = 3492787) B3492787
theorem B3104699 : Blo 2069435 3104699 := bstep (se 1 (by rfl) ⟨2328524, by rfl⟩ : syracuseStep 3104699 = 4657049) B4657049
theorem B2069799 : Blo 2069435 2069799 := bstep (se 1 (by rfl) ⟨1552349, by rfl⟩ : syracuseStep 2069799 = 3104699) B3104699
theorem B2328529 : Blo 2069435 2328529 := bbase (se 2 (by rfl) ⟨873198, by rfl⟩ : syracuseStep 2328529 = 1746397) (by norm_num)
theorem B3104705 : Blo 2069435 3104705 := bstep (se 2 (by rfl) ⟨1164264, by rfl⟩ : syracuseStep 3104705 = 2328529) B2328529
theorem B2069803 : Blo 2069435 2069803 := bstep (se 1 (by rfl) ⟨1552352, by rfl⟩ : syracuseStep 2069803 = 3104705) B3104705
theorem B11342261 : Blo 2069435 11342261 := bbase (se 5 (by rfl) ⟨531668, by rfl⟩ : syracuseStep 11342261 = 1063337) (by norm_num)
theorem B7561507 : Blo 2069435 7561507 := bstep (se 1 (by rfl) ⟨5671130, by rfl⟩ : syracuseStep 7561507 = 11342261) B11342261
theorem B10082009 : Blo 2069435 10082009 := bstep (se 2 (by rfl) ⟨3780753, by rfl⟩ : syracuseStep 10082009 = 7561507) B7561507
theorem B6721339 : Blo 2069435 6721339 := bstep (se 1 (by rfl) ⟨5041004, by rfl⟩ : syracuseStep 6721339 = 10082009) B10082009
theorem B8961785 : Blo 2069435 8961785 := bstep (se 2 (by rfl) ⟨3360669, by rfl⟩ : syracuseStep 8961785 = 6721339) B6721339
theorem B5974523 : Blo 2069435 5974523 := bstep (se 1 (by rfl) ⟨4480892, by rfl⟩ : syracuseStep 5974523 = 8961785) B8961785
theorem B3983015 : Blo 2069435 3983015 := bstep (se 1 (by rfl) ⟨2987261, by rfl⟩ : syracuseStep 3983015 = 5974523) B5974523
theorem B2655343 : Blo 2069435 2655343 := bstep (se 1 (by rfl) ⟨1991507, by rfl⟩ : syracuseStep 2655343 = 3983015) B3983015
theorem B3540457 : Blo 2069435 3540457 := bstep (se 2 (by rfl) ⟨1327671, by rfl⟩ : syracuseStep 3540457 = 2655343) B2655343
theorem B4720609 : Blo 2069435 4720609 := bstep (se 2 (by rfl) ⟨1770228, by rfl⟩ : syracuseStep 4720609 = 3540457) B3540457
theorem B6294145 : Blo 2069435 6294145 := bstep (se 2 (by rfl) ⟨2360304, by rfl⟩ : syracuseStep 6294145 = 4720609) B4720609
theorem B8392193 : Blo 2069435 8392193 := bstep (se 2 (by rfl) ⟨3147072, by rfl⟩ : syracuseStep 8392193 = 6294145) B6294145
theorem B5594795 : Blo 2069435 5594795 := bstep (se 1 (by rfl) ⟨4196096, by rfl⟩ : syracuseStep 5594795 = 8392193) B8392193
theorem B3729863 : Blo 2069435 3729863 := bstep (se 1 (by rfl) ⟨2797397, by rfl⟩ : syracuseStep 3729863 = 5594795) B5594795
theorem B2486575 : Blo 2069435 2486575 := bstep (se 1 (by rfl) ⟨1864931, by rfl⟩ : syracuseStep 2486575 = 3729863) B3729863
theorem B3315433 : Blo 2069435 3315433 := bstep (se 2 (by rfl) ⟨1243287, by rfl⟩ : syracuseStep 3315433 = 2486575) B2486575
theorem B4420577 : Blo 2069435 4420577 := bstep (se 2 (by rfl) ⟨1657716, by rfl⟩ : syracuseStep 4420577 = 3315433) B3315433
theorem B2947051 : Blo 2069435 2947051 := bstep (se 1 (by rfl) ⟨2210288, by rfl⟩ : syracuseStep 2947051 = 4420577) B4420577
theorem B3929401 : Blo 2069435 3929401 := bstep (se 2 (by rfl) ⟨1473525, by rfl⟩ : syracuseStep 3929401 = 2947051) B2947051
theorem B5239201 : Blo 2069435 5239201 := bstep (se 2 (by rfl) ⟨1964700, by rfl⟩ : syracuseStep 5239201 = 3929401) B3929401
theorem B6985601 : Blo 2069435 6985601 := bstep (se 2 (by rfl) ⟨2619600, by rfl⟩ : syracuseStep 6985601 = 5239201) B5239201
theorem B4657067 : Blo 2069435 4657067 := bstep (se 1 (by rfl) ⟨3492800, by rfl⟩ : syracuseStep 4657067 = 6985601) B6985601
theorem B3104711 : Blo 2069435 3104711 := bstep (se 1 (by rfl) ⟨2328533, by rfl⟩ : syracuseStep 3104711 = 4657067) B4657067
theorem B2069807 : Blo 2069435 2069807 := bstep (se 1 (by rfl) ⟨1552355, by rfl⟩ : syracuseStep 2069807 = 3104711) B3104711
theorem B3104717 : Blo 2069435 3104717 := bbase (se 3 (by rfl) ⟨582134, by rfl⟩ : syracuseStep 3104717 = 1164269) (by norm_num)
theorem B2069811 : Blo 2069435 2069811 := bstep (se 1 (by rfl) ⟨1552358, by rfl⟩ : syracuseStep 2069811 = 3104717) B3104717
theorem B4657085 : Blo 2069435 4657085 := bbase (se 3 (by rfl) ⟨873203, by rfl⟩ : syracuseStep 4657085 = 1746407) (by norm_num)
theorem B3104723 : Blo 2069435 3104723 := bstep (se 1 (by rfl) ⟨2328542, by rfl⟩ : syracuseStep 3104723 = 4657085) B4657085
theorem B2069815 : Blo 2069435 2069815 := bstep (se 1 (by rfl) ⟨1552361, by rfl⟩ : syracuseStep 2069815 = 3104723) B3104723
theorem B3492821 : Blo 2069435 3492821 := bbase (se 7 (by rfl) ⟨40931, by rfl⟩ : syracuseStep 3492821 = 81863) (by norm_num)
theorem B2328547 : Blo 2069435 2328547 := bstep (se 1 (by rfl) ⟨1746410, by rfl⟩ : syracuseStep 2328547 = 3492821) B3492821
theorem B3104729 : Blo 2069435 3104729 := bstep (se 2 (by rfl) ⟨1164273, by rfl⟩ : syracuseStep 3104729 = 2328547) B2328547
theorem B2069819 : Blo 2069435 2069819 := bstep (se 1 (by rfl) ⟨1552364, by rfl⟩ : syracuseStep 2069819 = 3104729) B3104729
theorem B8841221 : Blo 2069435 8841221 := bbase (se 4 (by rfl) ⟨828864, by rfl⟩ : syracuseStep 8841221 = 1657729) (by norm_num)
theorem B5894147 : Blo 2069435 5894147 := bstep (se 1 (by rfl) ⟨4420610, by rfl⟩ : syracuseStep 5894147 = 8841221) B8841221
theorem B15717725 : Blo 2069435 15717725 := bstep (se 3 (by rfl) ⟨2947073, by rfl⟩ : syracuseStep 15717725 = 5894147) B5894147
theorem B10478483 : Blo 2069435 10478483 := bstep (se 1 (by rfl) ⟨7858862, by rfl⟩ : syracuseStep 10478483 = 15717725) B15717725
theorem B6985655 : Blo 2069435 6985655 := bstep (se 1 (by rfl) ⟨5239241, by rfl⟩ : syracuseStep 6985655 = 10478483) B10478483
theorem B4657103 : Blo 2069435 4657103 := bstep (se 1 (by rfl) ⟨3492827, by rfl⟩ : syracuseStep 4657103 = 6985655) B6985655
theorem B3104735 : Blo 2069435 3104735 := bstep (se 1 (by rfl) ⟨2328551, by rfl⟩ : syracuseStep 3104735 = 4657103) B4657103
theorem B2069823 : Blo 2069435 2069823 := bstep (se 1 (by rfl) ⟨1552367, by rfl⟩ : syracuseStep 2069823 = 3104735) B3104735
theorem B3104741 : Blo 2069435 3104741 := bbase (se 4 (by rfl) ⟨291069, by rfl⟩ : syracuseStep 3104741 = 582139) (by norm_num)
theorem B2069827 : Blo 2069435 2069827 := bstep (se 1 (by rfl) ⟨1552370, by rfl⟩ : syracuseStep 2069827 = 3104741) B3104741
theorem B5041061 : Blo 2069435 5041061 := bbase (se 4 (by rfl) ⟨472599, by rfl⟩ : syracuseStep 5041061 = 945199) (by norm_num)
theorem B3360707 : Blo 2069435 3360707 := bstep (se 1 (by rfl) ⟨2520530, by rfl⟩ : syracuseStep 3360707 = 5041061) B5041061
theorem B2240471 : Blo 2069435 2240471 := bstep (se 1 (by rfl) ⟨1680353, by rfl⟩ : syracuseStep 2240471 = 3360707) B3360707
theorem B5974589 : Blo 2069435 5974589 := bstep (se 3 (by rfl) ⟨1120235, by rfl⟩ : syracuseStep 5974589 = 2240471) B2240471
theorem B3983059 : Blo 2069435 3983059 := bstep (se 1 (by rfl) ⟨2987294, by rfl⟩ : syracuseStep 3983059 = 5974589) B5974589
theorem B21242981 : Blo 2069435 21242981 := bstep (se 4 (by rfl) ⟨1991529, by rfl⟩ : syracuseStep 21242981 = 3983059) B3983059
theorem B14161987 : Blo 2069435 14161987 := bstep (se 1 (by rfl) ⟨10621490, by rfl⟩ : syracuseStep 14161987 = 21242981) B21242981
theorem B18882649 : Blo 2069435 18882649 := bstep (se 2 (by rfl) ⟨7080993, by rfl⟩ : syracuseStep 18882649 = 14161987) B14161987
theorem B25176865 : Blo 2069435 25176865 := bstep (se 2 (by rfl) ⟨9441324, by rfl⟩ : syracuseStep 25176865 = 18882649) B18882649
theorem B33569153 : Blo 2069435 33569153 := bstep (se 2 (by rfl) ⟨12588432, by rfl⟩ : syracuseStep 33569153 = 25176865) B25176865
theorem B22379435 : Blo 2069435 22379435 := bstep (se 1 (by rfl) ⟨16784576, by rfl⟩ : syracuseStep 22379435 = 33569153) B33569153
theorem B14919623 : Blo 2069435 14919623 := bstep (se 1 (by rfl) ⟨11189717, by rfl⟩ : syracuseStep 14919623 = 22379435) B22379435
theorem B9946415 : Blo 2069435 9946415 := bstep (se 1 (by rfl) ⟨7459811, by rfl⟩ : syracuseStep 9946415 = 14919623) B14919623
theorem B6630943 : Blo 2069435 6630943 := bstep (se 1 (by rfl) ⟨4973207, by rfl⟩ : syracuseStep 6630943 = 9946415) B9946415
theorem B8841257 : Blo 2069435 8841257 := bstep (se 2 (by rfl) ⟨3315471, by rfl⟩ : syracuseStep 8841257 = 6630943) B6630943
theorem B5894171 : Blo 2069435 5894171 := bstep (se 1 (by rfl) ⟨4420628, by rfl⟩ : syracuseStep 5894171 = 8841257) B8841257
theorem B3929447 : Blo 2069435 3929447 := bstep (se 1 (by rfl) ⟨2947085, by rfl⟩ : syracuseStep 3929447 = 5894171) B5894171
theorem B2619631 : Blo 2069435 2619631 := bstep (se 1 (by rfl) ⟨1964723, by rfl⟩ : syracuseStep 2619631 = 3929447) B3929447
theorem B3492841 : Blo 2069435 3492841 := bstep (se 2 (by rfl) ⟨1309815, by rfl⟩ : syracuseStep 3492841 = 2619631) B2619631
theorem B4657121 : Blo 2069435 4657121 := bstep (se 2 (by rfl) ⟨1746420, by rfl⟩ : syracuseStep 4657121 = 3492841) B3492841
theorem B3104747 : Blo 2069435 3104747 := bstep (se 1 (by rfl) ⟨2328560, by rfl⟩ : syracuseStep 3104747 = 4657121) B4657121
theorem B2069831 : Blo 2069435 2069831 := bstep (se 1 (by rfl) ⟨1552373, by rfl⟩ : syracuseStep 2069831 = 3104747) B3104747
theorem B2328565 : Blo 2069435 2328565 := bbase (se 5 (by rfl) ⟨109151, by rfl⟩ : syracuseStep 2328565 = 218303) (by norm_num)
theorem B3104753 : Blo 2069435 3104753 := bstep (se 2 (by rfl) ⟨1164282, by rfl⟩ : syracuseStep 3104753 = 2328565) B2328565
theorem B2069835 : Blo 2069435 2069835 := bstep (se 1 (by rfl) ⟨1552376, by rfl⟩ : syracuseStep 2069835 = 3104753) B3104753
theorem B2619641 : Blo 2069435 2619641 := bbase (se 2 (by rfl) ⟨982365, by rfl⟩ : syracuseStep 2619641 = 1964731) (by norm_num)
theorem B6985709 : Blo 2069435 6985709 := bstep (se 3 (by rfl) ⟨1309820, by rfl⟩ : syracuseStep 6985709 = 2619641) B2619641
theorem B4657139 : Blo 2069435 4657139 := bstep (se 1 (by rfl) ⟨3492854, by rfl⟩ : syracuseStep 4657139 = 6985709) B6985709
theorem B3104759 : Blo 2069435 3104759 := bstep (se 1 (by rfl) ⟨2328569, by rfl⟩ : syracuseStep 3104759 = 4657139) B4657139
theorem B2069839 : Blo 2069435 2069839 := bstep (se 1 (by rfl) ⟨1552379, by rfl⟩ : syracuseStep 2069839 = 3104759) B3104759
theorem B3104765 : Blo 2069435 3104765 := bbase (se 3 (by rfl) ⟨582143, by rfl⟩ : syracuseStep 3104765 = 1164287) (by norm_num)
theorem B2069843 : Blo 2069435 2069843 := bstep (se 1 (by rfl) ⟨1552382, by rfl⟩ : syracuseStep 2069843 = 3104765) B3104765
theorem B4657157 : Blo 2069435 4657157 := bbase (se 4 (by rfl) ⟨436608, by rfl⟩ : syracuseStep 4657157 = 873217) (by norm_num)
theorem B3104771 : Blo 2069435 3104771 := bstep (se 1 (by rfl) ⟨2328578, by rfl⟩ : syracuseStep 3104771 = 4657157) B4657157
theorem B2069847 : Blo 2069435 2069847 := bstep (se 1 (by rfl) ⟨1552385, by rfl⟩ : syracuseStep 2069847 = 3104771) B3104771
theorem B3929485 : Blo 2069435 3929485 := bbase (se 3 (by rfl) ⟨736778, by rfl⟩ : syracuseStep 3929485 = 1473557) (by norm_num)
theorem B5239313 : Blo 2069435 5239313 := bstep (se 2 (by rfl) ⟨1964742, by rfl⟩ : syracuseStep 5239313 = 3929485) B3929485
theorem B3492875 : Blo 2069435 3492875 := bstep (se 1 (by rfl) ⟨2619656, by rfl⟩ : syracuseStep 3492875 = 5239313) B5239313
theorem B2328583 : Blo 2069435 2328583 := bstep (se 1 (by rfl) ⟨1746437, by rfl⟩ : syracuseStep 2328583 = 3492875) B3492875
theorem B3104777 : Blo 2069435 3104777 := bstep (se 2 (by rfl) ⟨1164291, by rfl⟩ : syracuseStep 3104777 = 2328583) B2328583
theorem B2069851 : Blo 2069435 2069851 := bstep (se 1 (by rfl) ⟨1552388, by rfl⟩ : syracuseStep 2069851 = 3104777) B3104777
theorem B10478645 : Blo 2069435 10478645 := bbase (se 5 (by rfl) ⟨491186, by rfl⟩ : syracuseStep 10478645 = 982373) (by norm_num)
theorem B6985763 : Blo 2069435 6985763 := bstep (se 1 (by rfl) ⟨5239322, by rfl⟩ : syracuseStep 6985763 = 10478645) B10478645
theorem B4657175 : Blo 2069435 4657175 := bstep (se 1 (by rfl) ⟨3492881, by rfl⟩ : syracuseStep 4657175 = 6985763) B6985763
theorem B3104783 : Blo 2069435 3104783 := bstep (se 1 (by rfl) ⟨2328587, by rfl⟩ : syracuseStep 3104783 = 4657175) B4657175
theorem B2069855 : Blo 2069435 2069855 := bstep (se 1 (by rfl) ⟨1552391, by rfl⟩ : syracuseStep 2069855 = 3104783) B3104783
theorem B3104789 : Blo 2069435 3104789 := bbase (se 6 (by rfl) ⟨72768, by rfl⟩ : syracuseStep 3104789 = 145537) (by norm_num)
theorem B2069859 : Blo 2069435 2069859 := bstep (se 1 (by rfl) ⟨1552394, by rfl⟩ : syracuseStep 2069859 = 3104789) B3104789
theorem B2520569 : Blo 2069435 2520569 := bbase (se 2 (by rfl) ⟨945213, by rfl⟩ : syracuseStep 2520569 = 1890427) (by norm_num)
theorem B6721517 : Blo 2069435 6721517 := bstep (se 3 (by rfl) ⟨1260284, by rfl⟩ : syracuseStep 6721517 = 2520569) B2520569
theorem B4481011 : Blo 2069435 4481011 := bstep (se 1 (by rfl) ⟨3360758, by rfl⟩ : syracuseStep 4481011 = 6721517) B6721517
theorem B5974681 : Blo 2069435 5974681 := bstep (se 2 (by rfl) ⟨2240505, by rfl⟩ : syracuseStep 5974681 = 4481011) B4481011
theorem B7966241 : Blo 2069435 7966241 := bstep (se 2 (by rfl) ⟨2987340, by rfl⟩ : syracuseStep 7966241 = 5974681) B5974681
theorem B5310827 : Blo 2069435 5310827 := bstep (se 1 (by rfl) ⟨3983120, by rfl⟩ : syracuseStep 5310827 = 7966241) B7966241
theorem B3540551 : Blo 2069435 3540551 := bstep (se 1 (by rfl) ⟨2655413, by rfl⟩ : syracuseStep 3540551 = 5310827) B5310827
theorem B9441469 : Blo 2069435 9441469 := bstep (se 3 (by rfl) ⟨1770275, by rfl⟩ : syracuseStep 9441469 = 3540551) B3540551
theorem B12588625 : Blo 2069435 12588625 := bstep (se 2 (by rfl) ⟨4720734, by rfl⟩ : syracuseStep 12588625 = 9441469) B9441469
theorem B16784833 : Blo 2069435 16784833 := bstep (se 2 (by rfl) ⟨6294312, by rfl⟩ : syracuseStep 16784833 = 12588625) B12588625
theorem B22379777 : Blo 2069435 22379777 := bstep (se 2 (by rfl) ⟨8392416, by rfl⟩ : syracuseStep 22379777 = 16784833) B16784833
theorem B14919851 : Blo 2069435 14919851 := bstep (se 1 (by rfl) ⟨11189888, by rfl⟩ : syracuseStep 14919851 = 22379777) B22379777
theorem B9946567 : Blo 2069435 9946567 := bstep (se 1 (by rfl) ⟨7459925, by rfl⟩ : syracuseStep 9946567 = 14919851) B14919851
theorem B13262089 : Blo 2069435 13262089 := bstep (se 2 (by rfl) ⟨4973283, by rfl⟩ : syracuseStep 13262089 = 9946567) B9946567
theorem B17682785 : Blo 2069435 17682785 := bstep (se 2 (by rfl) ⟨6631044, by rfl⟩ : syracuseStep 17682785 = 13262089) B13262089
theorem B11788523 : Blo 2069435 11788523 := bstep (se 1 (by rfl) ⟨8841392, by rfl⟩ : syracuseStep 11788523 = 17682785) B17682785
theorem B7859015 : Blo 2069435 7859015 := bstep (se 1 (by rfl) ⟨5894261, by rfl⟩ : syracuseStep 7859015 = 11788523) B11788523
theorem B5239343 : Blo 2069435 5239343 := bstep (se 1 (by rfl) ⟨3929507, by rfl⟩ : syracuseStep 5239343 = 7859015) B7859015
theorem B3492895 : Blo 2069435 3492895 := bstep (se 1 (by rfl) ⟨2619671, by rfl⟩ : syracuseStep 3492895 = 5239343) B5239343
theorem B4657193 : Blo 2069435 4657193 := bstep (se 2 (by rfl) ⟨1746447, by rfl⟩ : syracuseStep 4657193 = 3492895) B3492895
theorem B3104795 : Blo 2069435 3104795 := bstep (se 1 (by rfl) ⟨2328596, by rfl⟩ : syracuseStep 3104795 = 4657193) B4657193
theorem B2069863 : Blo 2069435 2069863 := bstep (se 1 (by rfl) ⟨1552397, by rfl⟩ : syracuseStep 2069863 = 3104795) B3104795
theorem B2328601 : Blo 2069435 2328601 := bbase (se 2 (by rfl) ⟨873225, by rfl⟩ : syracuseStep 2328601 = 1746451) (by norm_num)
theorem B3104801 : Blo 2069435 3104801 := bstep (se 2 (by rfl) ⟨1164300, by rfl⟩ : syracuseStep 3104801 = 2328601) B2328601
theorem B2069867 : Blo 2069435 2069867 := bstep (se 1 (by rfl) ⟨1552400, by rfl⟩ : syracuseStep 2069867 = 3104801) B3104801
theorem B7859045 : Blo 2069435 7859045 := bbase (se 4 (by rfl) ⟨736785, by rfl⟩ : syracuseStep 7859045 = 1473571) (by norm_num)
theorem B5239363 : Blo 2069435 5239363 := bstep (se 1 (by rfl) ⟨3929522, by rfl⟩ : syracuseStep 5239363 = 7859045) B7859045
theorem B6985817 : Blo 2069435 6985817 := bstep (se 2 (by rfl) ⟨2619681, by rfl⟩ : syracuseStep 6985817 = 5239363) B5239363
theorem B4657211 : Blo 2069435 4657211 := bstep (se 1 (by rfl) ⟨3492908, by rfl⟩ : syracuseStep 4657211 = 6985817) B6985817
theorem B3104807 : Blo 2069435 3104807 := bstep (se 1 (by rfl) ⟨2328605, by rfl⟩ : syracuseStep 3104807 = 4657211) B4657211
theorem B2069871 : Blo 2069435 2069871 := bstep (se 1 (by rfl) ⟨1552403, by rfl⟩ : syracuseStep 2069871 = 3104807) B3104807
theorem B3104813 : Blo 2069435 3104813 := bbase (se 3 (by rfl) ⟨582152, by rfl⟩ : syracuseStep 3104813 = 1164305) (by norm_num)
theorem B2069875 : Blo 2069435 2069875 := bstep (se 1 (by rfl) ⟨1552406, by rfl⟩ : syracuseStep 2069875 = 3104813) B3104813
theorem B4657229 : Blo 2069435 4657229 := bbase (se 3 (by rfl) ⟨873230, by rfl⟩ : syracuseStep 4657229 = 1746461) (by norm_num)
theorem B3104819 : Blo 2069435 3104819 := bstep (se 1 (by rfl) ⟨2328614, by rfl⟩ : syracuseStep 3104819 = 4657229) B4657229
theorem B2069879 : Blo 2069435 2069879 := bstep (se 1 (by rfl) ⟨1552409, by rfl⟩ : syracuseStep 2069879 = 3104819) B3104819
theorem B2619697 : Blo 2069435 2619697 := bbase (se 2 (by rfl) ⟨982386, by rfl⟩ : syracuseStep 2619697 = 1964773) (by norm_num)
theorem B3492929 : Blo 2069435 3492929 := bstep (se 2 (by rfl) ⟨1309848, by rfl⟩ : syracuseStep 3492929 = 2619697) B2619697
theorem B2328619 : Blo 2069435 2328619 := bstep (se 1 (by rfl) ⟨1746464, by rfl⟩ : syracuseStep 2328619 = 3492929) B3492929
theorem B3104825 : Blo 2069435 3104825 := bstep (se 2 (by rfl) ⟨1164309, by rfl⟩ : syracuseStep 3104825 = 2328619) B2328619
theorem B2069883 : Blo 2069435 2069883 := bstep (se 1 (by rfl) ⟨1552412, by rfl⟩ : syracuseStep 2069883 = 3104825) B3104825
theorem B4973341 : Blo 2069435 4973341 := bbase (se 3 (by rfl) ⟨932501, by rfl⟩ : syracuseStep 4973341 = 1865003) (by norm_num)
theorem B6631121 : Blo 2069435 6631121 := bstep (se 2 (by rfl) ⟨2486670, by rfl⟩ : syracuseStep 6631121 = 4973341) B4973341
theorem B4420747 : Blo 2069435 4420747 := bstep (se 1 (by rfl) ⟨3315560, by rfl⟩ : syracuseStep 4420747 = 6631121) B6631121
theorem B23577317 : Blo 2069435 23577317 := bstep (se 4 (by rfl) ⟨2210373, by rfl⟩ : syracuseStep 23577317 = 4420747) B4420747
theorem B15718211 : Blo 2069435 15718211 := bstep (se 1 (by rfl) ⟨11788658, by rfl⟩ : syracuseStep 15718211 = 23577317) B23577317
theorem B10478807 : Blo 2069435 10478807 := bstep (se 1 (by rfl) ⟨7859105, by rfl⟩ : syracuseStep 10478807 = 15718211) B15718211
theorem B6985871 : Blo 2069435 6985871 := bstep (se 1 (by rfl) ⟨5239403, by rfl⟩ : syracuseStep 6985871 = 10478807) B10478807
theorem B4657247 : Blo 2069435 4657247 := bstep (se 1 (by rfl) ⟨3492935, by rfl⟩ : syracuseStep 4657247 = 6985871) B6985871
theorem B3104831 : Blo 2069435 3104831 := bstep (se 1 (by rfl) ⟨2328623, by rfl⟩ : syracuseStep 3104831 = 4657247) B4657247
theorem B2069887 : Blo 2069435 2069887 := bstep (se 1 (by rfl) ⟨1552415, by rfl⟩ : syracuseStep 2069887 = 3104831) B3104831
theorem B3104837 : Blo 2069435 3104837 := bbase (se 4 (by rfl) ⟨291078, by rfl⟩ : syracuseStep 3104837 = 582157) (by norm_num)
theorem B2069891 : Blo 2069435 2069891 := bstep (se 1 (by rfl) ⟨1552418, by rfl⟩ : syracuseStep 2069891 = 3104837) B3104837
theorem B3492949 : Blo 2069435 3492949 := bbase (se 8 (by rfl) ⟨20466, by rfl⟩ : syracuseStep 3492949 = 40933) (by norm_num)
theorem B4657265 : Blo 2069435 4657265 := bstep (se 2 (by rfl) ⟨1746474, by rfl⟩ : syracuseStep 4657265 = 3492949) B3492949
theorem B3104843 : Blo 2069435 3104843 := bstep (se 1 (by rfl) ⟨2328632, by rfl⟩ : syracuseStep 3104843 = 4657265) B4657265
theorem B2069895 : Blo 2069435 2069895 := bstep (se 1 (by rfl) ⟨1552421, by rfl⟩ : syracuseStep 2069895 = 3104843) B3104843
theorem B2328637 : Blo 2069435 2328637 := bbase (se 3 (by rfl) ⟨436619, by rfl⟩ : syracuseStep 2328637 = 873239) (by norm_num)
theorem B3104849 : Blo 2069435 3104849 := bstep (se 2 (by rfl) ⟨1164318, by rfl⟩ : syracuseStep 3104849 = 2328637) B2328637
theorem B2069899 : Blo 2069435 2069899 := bstep (se 1 (by rfl) ⟨1552424, by rfl⟩ : syracuseStep 2069899 = 3104849) B3104849
theorem B6985925 : Blo 2069435 6985925 := bbase (se 4 (by rfl) ⟨654930, by rfl⟩ : syracuseStep 6985925 = 1309861) (by norm_num)
theorem B4657283 : Blo 2069435 4657283 := bstep (se 1 (by rfl) ⟨3492962, by rfl⟩ : syracuseStep 4657283 = 6985925) B6985925
theorem B3104855 : Blo 2069435 3104855 := bstep (se 1 (by rfl) ⟨2328641, by rfl⟩ : syracuseStep 3104855 = 4657283) B4657283
theorem B2069903 : Blo 2069435 2069903 := bstep (se 1 (by rfl) ⟨1552427, by rfl⟩ : syracuseStep 2069903 = 3104855) B3104855
theorem B3104861 : Blo 2069435 3104861 := bbase (se 3 (by rfl) ⟨582161, by rfl⟩ : syracuseStep 3104861 = 1164323) (by norm_num)
theorem B2069907 : Blo 2069435 2069907 := bstep (se 1 (by rfl) ⟨1552430, by rfl⟩ : syracuseStep 2069907 = 3104861) B3104861
theorem B4657301 : Blo 2069435 4657301 := bbase (se 6 (by rfl) ⟨109155, by rfl⟩ : syracuseStep 4657301 = 218311) (by norm_num)
theorem B3104867 : Blo 2069435 3104867 := bstep (se 1 (by rfl) ⟨2328650, by rfl⟩ : syracuseStep 3104867 = 4657301) B4657301
theorem B2069911 : Blo 2069435 2069911 := bstep (se 1 (by rfl) ⟨1552433, by rfl⟩ : syracuseStep 2069911 = 3104867) B3104867
theorem B2947205 : Blo 2069435 2947205 := bbase (se 4 (by rfl) ⟨276300, by rfl⟩ : syracuseStep 2947205 = 552601) (by norm_num)
theorem B7859213 : Blo 2069435 7859213 := bstep (se 3 (by rfl) ⟨1473602, by rfl⟩ : syracuseStep 7859213 = 2947205) B2947205
theorem B5239475 : Blo 2069435 5239475 := bstep (se 1 (by rfl) ⟨3929606, by rfl⟩ : syracuseStep 5239475 = 7859213) B7859213
theorem B3492983 : Blo 2069435 3492983 := bstep (se 1 (by rfl) ⟨2619737, by rfl⟩ : syracuseStep 3492983 = 5239475) B5239475
theorem B2328655 : Blo 2069435 2328655 := bstep (se 1 (by rfl) ⟨1746491, by rfl⟩ : syracuseStep 2328655 = 3492983) B3492983
theorem B3104873 : Blo 2069435 3104873 := bstep (se 2 (by rfl) ⟨1164327, by rfl⟩ : syracuseStep 3104873 = 2328655) B2328655
theorem B2069915 : Blo 2069435 2069915 := bstep (se 1 (by rfl) ⟨1552436, by rfl⟩ : syracuseStep 2069915 = 3104873) B3104873
theorem B7177909 : Blo 2069435 7177909 := bbase (se 5 (by rfl) ⟨336464, by rfl⟩ : syracuseStep 7177909 = 672929) (by norm_num)
theorem B9570545 : Blo 2069435 9570545 := bstep (se 2 (by rfl) ⟨3588954, by rfl⟩ : syracuseStep 9570545 = 7177909) B7177909
theorem B6380363 : Blo 2069435 6380363 := bstep (se 1 (by rfl) ⟨4785272, by rfl⟩ : syracuseStep 6380363 = 9570545) B9570545
theorem B4253575 : Blo 2069435 4253575 := bstep (se 1 (by rfl) ⟨3190181, by rfl⟩ : syracuseStep 4253575 = 6380363) B6380363
theorem B5671433 : Blo 2069435 5671433 := bstep (se 2 (by rfl) ⟨2126787, by rfl⟩ : syracuseStep 5671433 = 4253575) B4253575
theorem B3780955 : Blo 2069435 3780955 := bstep (se 1 (by rfl) ⟨2835716, by rfl⟩ : syracuseStep 3780955 = 5671433) B5671433
theorem B5041273 : Blo 2069435 5041273 := bstep (se 2 (by rfl) ⟨1890477, by rfl⟩ : syracuseStep 5041273 = 3780955) B3780955
theorem B6721697 : Blo 2069435 6721697 := bstep (se 2 (by rfl) ⟨2520636, by rfl⟩ : syracuseStep 6721697 = 5041273) B5041273
theorem B4481131 : Blo 2069435 4481131 := bstep (se 1 (by rfl) ⟨3360848, by rfl⟩ : syracuseStep 4481131 = 6721697) B6721697
theorem B5974841 : Blo 2069435 5974841 := bstep (se 2 (by rfl) ⟨2240565, by rfl⟩ : syracuseStep 5974841 = 4481131) B4481131
theorem B15932909 : Blo 2069435 15932909 := bstep (se 3 (by rfl) ⟨2987420, by rfl⟩ : syracuseStep 15932909 = 5974841) B5974841
theorem B10621939 : Blo 2069435 10621939 := bstep (se 1 (by rfl) ⟨7966454, by rfl⟩ : syracuseStep 10621939 = 15932909) B15932909
theorem B14162585 : Blo 2069435 14162585 := bstep (se 2 (by rfl) ⟨5310969, by rfl⟩ : syracuseStep 14162585 = 10621939) B10621939
theorem B37766893 : Blo 2069435 37766893 := bstep (se 3 (by rfl) ⟨7081292, by rfl⟩ : syracuseStep 37766893 = 14162585) B14162585
theorem B50355857 : Blo 2069435 50355857 := bstep (se 2 (by rfl) ⟨18883446, by rfl⟩ : syracuseStep 50355857 = 37766893) B37766893
theorem B33570571 : Blo 2069435 33570571 := bstep (se 1 (by rfl) ⟨25177928, by rfl⟩ : syracuseStep 33570571 = 50355857) B50355857
theorem B44760761 : Blo 2069435 44760761 := bstep (se 2 (by rfl) ⟨16785285, by rfl⟩ : syracuseStep 44760761 = 33570571) B33570571
theorem B29840507 : Blo 2069435 29840507 := bstep (se 1 (by rfl) ⟨22380380, by rfl⟩ : syracuseStep 29840507 = 44760761) B44760761
theorem B19893671 : Blo 2069435 19893671 := bstep (se 1 (by rfl) ⟨14920253, by rfl⟩ : syracuseStep 19893671 = 29840507) B29840507
theorem B13262447 : Blo 2069435 13262447 := bstep (se 1 (by rfl) ⟨9946835, by rfl⟩ : syracuseStep 13262447 = 19893671) B19893671
theorem B8841631 : Blo 2069435 8841631 := bstep (se 1 (by rfl) ⟨6631223, by rfl⟩ : syracuseStep 8841631 = 13262447) B13262447
theorem B11788841 : Blo 2069435 11788841 := bstep (se 2 (by rfl) ⟨4420815, by rfl⟩ : syracuseStep 11788841 = 8841631) B8841631
theorem B7859227 : Blo 2069435 7859227 := bstep (se 1 (by rfl) ⟨5894420, by rfl⟩ : syracuseStep 7859227 = 11788841) B11788841
theorem B10478969 : Blo 2069435 10478969 := bstep (se 2 (by rfl) ⟨3929613, by rfl⟩ : syracuseStep 10478969 = 7859227) B7859227
theorem B6985979 : Blo 2069435 6985979 := bstep (se 1 (by rfl) ⟨5239484, by rfl⟩ : syracuseStep 6985979 = 10478969) B10478969
theorem B4657319 : Blo 2069435 4657319 := bstep (se 1 (by rfl) ⟨3492989, by rfl⟩ : syracuseStep 4657319 = 6985979) B6985979
theorem B3104879 : Blo 2069435 3104879 := bstep (se 1 (by rfl) ⟨2328659, by rfl⟩ : syracuseStep 3104879 = 4657319) B4657319
theorem B2069919 : Blo 2069435 2069919 := bstep (se 1 (by rfl) ⟨1552439, by rfl⟩ : syracuseStep 2069919 = 3104879) B3104879
theorem B3104885 : Blo 2069435 3104885 := bbase (se 5 (by rfl) ⟨145541, by rfl⟩ : syracuseStep 3104885 = 291083) (by norm_num)
theorem B2069923 : Blo 2069435 2069923 := bstep (se 1 (by rfl) ⟨1552442, by rfl⟩ : syracuseStep 2069923 = 3104885) B3104885
theorem B3929629 : Blo 2069435 3929629 := bbase (se 3 (by rfl) ⟨736805, by rfl⟩ : syracuseStep 3929629 = 1473611) (by norm_num)
theorem B5239505 : Blo 2069435 5239505 := bstep (se 2 (by rfl) ⟨1964814, by rfl⟩ : syracuseStep 5239505 = 3929629) B3929629
theorem B3493003 : Blo 2069435 3493003 := bstep (se 1 (by rfl) ⟨2619752, by rfl⟩ : syracuseStep 3493003 = 5239505) B5239505
theorem B4657337 : Blo 2069435 4657337 := bstep (se 2 (by rfl) ⟨1746501, by rfl⟩ : syracuseStep 4657337 = 3493003) B3493003
theorem B3104891 : Blo 2069435 3104891 := bstep (se 1 (by rfl) ⟨2328668, by rfl⟩ : syracuseStep 3104891 = 4657337) B4657337
theorem B2069927 : Blo 2069435 2069927 := bstep (se 1 (by rfl) ⟨1552445, by rfl⟩ : syracuseStep 2069927 = 3104891) B3104891
theorem B2328673 : Blo 2069435 2328673 := bbase (se 2 (by rfl) ⟨873252, by rfl⟩ : syracuseStep 2328673 = 1746505) (by norm_num)
theorem B3104897 : Blo 2069435 3104897 := bstep (se 2 (by rfl) ⟨1164336, by rfl⟩ : syracuseStep 3104897 = 2328673) B2328673
theorem B2069931 : Blo 2069435 2069931 := bstep (se 1 (by rfl) ⟨1552448, by rfl⟩ : syracuseStep 2069931 = 3104897) B3104897
theorem B5239525 : Blo 2069435 5239525 := bbase (se 4 (by rfl) ⟨491205, by rfl⟩ : syracuseStep 5239525 = 982411) (by norm_num)
theorem B6986033 : Blo 2069435 6986033 := bstep (se 2 (by rfl) ⟨2619762, by rfl⟩ : syracuseStep 6986033 = 5239525) B5239525
theorem B4657355 : Blo 2069435 4657355 := bstep (se 1 (by rfl) ⟨3493016, by rfl⟩ : syracuseStep 4657355 = 6986033) B6986033
theorem B3104903 : Blo 2069435 3104903 := bstep (se 1 (by rfl) ⟨2328677, by rfl⟩ : syracuseStep 3104903 = 4657355) B4657355
theorem B2069935 : Blo 2069435 2069935 := bstep (se 1 (by rfl) ⟨1552451, by rfl⟩ : syracuseStep 2069935 = 3104903) B3104903
theorem B3104909 : Blo 2069435 3104909 := bbase (se 3 (by rfl) ⟨582170, by rfl⟩ : syracuseStep 3104909 = 1164341) (by norm_num)
theorem B2069939 : Blo 2069435 2069939 := bstep (se 1 (by rfl) ⟨1552454, by rfl⟩ : syracuseStep 2069939 = 3104909) B3104909
theorem B4657373 : Blo 2069435 4657373 := bbase (se 3 (by rfl) ⟨873257, by rfl⟩ : syracuseStep 4657373 = 1746515) (by norm_num)
theorem B3104915 : Blo 2069435 3104915 := bstep (se 1 (by rfl) ⟨2328686, by rfl⟩ : syracuseStep 3104915 = 4657373) B4657373
theorem B2069943 : Blo 2069435 2069943 := bstep (se 1 (by rfl) ⟨1552457, by rfl⟩ : syracuseStep 2069943 = 3104915) B3104915
theorem B3493037 : Blo 2069435 3493037 := bbase (se 3 (by rfl) ⟨654944, by rfl⟩ : syracuseStep 3493037 = 1309889) (by norm_num)
theorem B2328691 : Blo 2069435 2328691 := bstep (se 1 (by rfl) ⟨1746518, by rfl⟩ : syracuseStep 2328691 = 3493037) B3493037
theorem B3104921 : Blo 2069435 3104921 := bstep (se 2 (by rfl) ⟨1164345, by rfl⟩ : syracuseStep 3104921 = 2328691) B2328691
theorem B2069947 : Blo 2069435 2069947 := bstep (se 1 (by rfl) ⟨1552460, by rfl⟩ : syracuseStep 2069947 = 3104921) B3104921
theorem B2098193 : Blo 2069435 2098193 := bbase (se 2 (by rfl) ⟨786822, by rfl⟩ : syracuseStep 2098193 = 1573645) (by norm_num)
theorem B22380725 : Blo 2069435 22380725 := bstep (se 5 (by rfl) ⟨1049096, by rfl⟩ : syracuseStep 22380725 = 2098193) B2098193
theorem B59681933 : Blo 2069435 59681933 := bstep (se 3 (by rfl) ⟨11190362, by rfl⟩ : syracuseStep 59681933 = 22380725) B22380725
theorem B39787955 : Blo 2069435 39787955 := bstep (se 1 (by rfl) ⟨29840966, by rfl⟩ : syracuseStep 39787955 = 59681933) B59681933
theorem B26525303 : Blo 2069435 26525303 := bstep (se 1 (by rfl) ⟨19893977, by rfl⟩ : syracuseStep 26525303 = 39787955) B39787955
theorem B17683535 : Blo 2069435 17683535 := bstep (se 1 (by rfl) ⟨13262651, by rfl⟩ : syracuseStep 17683535 = 26525303) B26525303
theorem B11789023 : Blo 2069435 11789023 := bstep (se 1 (by rfl) ⟨8841767, by rfl⟩ : syracuseStep 11789023 = 17683535) B17683535
theorem B15718697 : Blo 2069435 15718697 := bstep (se 2 (by rfl) ⟨5894511, by rfl⟩ : syracuseStep 15718697 = 11789023) B11789023
theorem B10479131 : Blo 2069435 10479131 := bstep (se 1 (by rfl) ⟨7859348, by rfl⟩ : syracuseStep 10479131 = 15718697) B15718697
theorem B6986087 : Blo 2069435 6986087 := bstep (se 1 (by rfl) ⟨5239565, by rfl⟩ : syracuseStep 6986087 = 10479131) B10479131
theorem B4657391 : Blo 2069435 4657391 := bstep (se 1 (by rfl) ⟨3493043, by rfl⟩ : syracuseStep 4657391 = 6986087) B6986087
theorem B3104927 : Blo 2069435 3104927 := bstep (se 1 (by rfl) ⟨2328695, by rfl⟩ : syracuseStep 3104927 = 4657391) B4657391
theorem B2069951 : Blo 2069435 2069951 := bstep (se 1 (by rfl) ⟨1552463, by rfl⟩ : syracuseStep 2069951 = 3104927) B3104927
theorem B3104933 : Blo 2069435 3104933 := bbase (se 4 (by rfl) ⟨291087, by rfl⟩ : syracuseStep 3104933 = 582175) (by norm_num)
theorem B2069955 : Blo 2069435 2069955 := bstep (se 1 (by rfl) ⟨1552466, by rfl⟩ : syracuseStep 2069955 = 3104933) B3104933
theorem B2619793 : Blo 2069435 2619793 := bbase (se 2 (by rfl) ⟨982422, by rfl⟩ : syracuseStep 2619793 = 1964845) (by norm_num)
theorem B3493057 : Blo 2069435 3493057 := bstep (se 2 (by rfl) ⟨1309896, by rfl⟩ : syracuseStep 3493057 = 2619793) B2619793
theorem B4657409 : Blo 2069435 4657409 := bstep (se 2 (by rfl) ⟨1746528, by rfl⟩ : syracuseStep 4657409 = 3493057) B3493057
theorem B3104939 : Blo 2069435 3104939 := bstep (se 1 (by rfl) ⟨2328704, by rfl⟩ : syracuseStep 3104939 = 4657409) B4657409
theorem B2069959 : Blo 2069435 2069959 := bstep (se 1 (by rfl) ⟨1552469, by rfl⟩ : syracuseStep 2069959 = 3104939) B3104939
theorem B2328709 : Blo 2069435 2328709 := bbase (se 4 (by rfl) ⟨218316, by rfl⟩ : syracuseStep 2328709 = 436633) (by norm_num)
theorem B3104945 : Blo 2069435 3104945 := bstep (se 2 (by rfl) ⟨1164354, by rfl⟩ : syracuseStep 3104945 = 2328709) B2328709
theorem B2069963 : Blo 2069435 2069963 := bstep (se 1 (by rfl) ⟨1552472, by rfl⟩ : syracuseStep 2069963 = 3104945) B3104945
theorem B4148597 : Blo 2069435 4148597 := bbase (se 5 (by rfl) ⟨194465, by rfl⟩ : syracuseStep 4148597 = 388931) (by norm_num)
theorem B11062925 : Blo 2069435 11062925 := bstep (se 3 (by rfl) ⟨2074298, by rfl⟩ : syracuseStep 11062925 = 4148597) B4148597
theorem B7375283 : Blo 2069435 7375283 := bstep (se 1 (by rfl) ⟨5531462, by rfl⟩ : syracuseStep 7375283 = 11062925) B11062925
theorem B4916855 : Blo 2069435 4916855 := bstep (se 1 (by rfl) ⟨3687641, by rfl⟩ : syracuseStep 4916855 = 7375283) B7375283
theorem B3277903 : Blo 2069435 3277903 := bstep (se 1 (by rfl) ⟨2458427, by rfl⟩ : syracuseStep 3277903 = 4916855) B4916855
theorem B4370537 : Blo 2069435 4370537 := bstep (se 2 (by rfl) ⟨1638951, by rfl⟩ : syracuseStep 4370537 = 3277903) B3277903
theorem B11654765 : Blo 2069435 11654765 := bstep (se 3 (by rfl) ⟨2185268, by rfl⟩ : syracuseStep 11654765 = 4370537) B4370537
theorem B7769843 : Blo 2069435 7769843 := bstep (se 1 (by rfl) ⟨5827382, by rfl⟩ : syracuseStep 7769843 = 11654765) B11654765
theorem B5179895 : Blo 2069435 5179895 := bstep (se 1 (by rfl) ⟨3884921, by rfl⟩ : syracuseStep 5179895 = 7769843) B7769843
theorem B3453263 : Blo 2069435 3453263 := bstep (se 1 (by rfl) ⟨2589947, by rfl⟩ : syracuseStep 3453263 = 5179895) B5179895
theorem B2302175 : Blo 2069435 2302175 := bstep (se 1 (by rfl) ⟨1726631, by rfl⟩ : syracuseStep 2302175 = 3453263) B3453263
theorem B6139133 : Blo 2069435 6139133 := bstep (se 3 (by rfl) ⟨1151087, by rfl⟩ : syracuseStep 6139133 = 2302175) B2302175
theorem B4092755 : Blo 2069435 4092755 := bstep (se 1 (by rfl) ⟨3069566, by rfl⟩ : syracuseStep 4092755 = 6139133) B6139133
theorem B10914013 : Blo 2069435 10914013 := bstep (se 3 (by rfl) ⟨2046377, by rfl⟩ : syracuseStep 10914013 = 4092755) B4092755
theorem B14552017 : Blo 2069435 14552017 := bstep (se 2 (by rfl) ⟨5457006, by rfl⟩ : syracuseStep 14552017 = 10914013) B10914013
theorem B77610757 : Blo 2069435 77610757 := bstep (se 4 (by rfl) ⟨7276008, by rfl⟩ : syracuseStep 77610757 = 14552017) B14552017
theorem B103481009 : Blo 2069435 103481009 := bstep (se 2 (by rfl) ⟨38805378, by rfl⟩ : syracuseStep 103481009 = 77610757) B77610757
theorem B68987339 : Blo 2069435 68987339 := bstep (se 1 (by rfl) ⟨51740504, by rfl⟩ : syracuseStep 68987339 = 103481009) B103481009
theorem B45991559 : Blo 2069435 45991559 := bstep (se 1 (by rfl) ⟨34493669, by rfl⟩ : syracuseStep 45991559 = 68987339) B68987339
theorem B30661039 : Blo 2069435 30661039 := bstep (se 1 (by rfl) ⟨22995779, by rfl⟩ : syracuseStep 30661039 = 45991559) B45991559
theorem B40881385 : Blo 2069435 40881385 := bstep (se 2 (by rfl) ⟨15330519, by rfl⟩ : syracuseStep 40881385 = 30661039) B30661039
theorem B54508513 : Blo 2069435 54508513 := bstep (se 2 (by rfl) ⟨20440692, by rfl⟩ : syracuseStep 54508513 = 40881385) B40881385
theorem B72678017 : Blo 2069435 72678017 := bstep (se 2 (by rfl) ⟨27254256, by rfl⟩ : syracuseStep 72678017 = 54508513) B54508513
theorem B193808045 : Blo 2069435 193808045 := bstep (se 3 (by rfl) ⟨36339008, by rfl⟩ : syracuseStep 193808045 = 72678017) B72678017
theorem B129205363 : Blo 2069435 129205363 := bstep (se 1 (by rfl) ⟨96904022, by rfl⟩ : syracuseStep 129205363 = 193808045) B193808045
theorem B172273817 : Blo 2069435 172273817 := bstep (se 2 (by rfl) ⟨64602681, by rfl⟩ : syracuseStep 172273817 = 129205363) B129205363
theorem B459396845 : Blo 2069435 459396845 := bstep (se 3 (by rfl) ⟨86136908, by rfl⟩ : syracuseStep 459396845 = 172273817) B172273817
theorem B306264563 : Blo 2069435 306264563 := bstep (se 1 (by rfl) ⟨229698422, by rfl⟩ : syracuseStep 306264563 = 459396845) B459396845
theorem B204176375 : Blo 2069435 204176375 := bstep (se 1 (by rfl) ⟨153132281, by rfl⟩ : syracuseStep 204176375 = 306264563) B306264563
theorem B136117583 : Blo 2069435 136117583 := bstep (se 1 (by rfl) ⟨102088187, by rfl⟩ : syracuseStep 136117583 = 204176375) B204176375
theorem B90745055 : Blo 2069435 90745055 := bstep (se 1 (by rfl) ⟨68058791, by rfl⟩ : syracuseStep 90745055 = 136117583) B136117583
theorem B60496703 : Blo 2069435 60496703 := bstep (se 1 (by rfl) ⟨45372527, by rfl⟩ : syracuseStep 60496703 = 90745055) B90745055
theorem B40331135 : Blo 2069435 40331135 := bstep (se 1 (by rfl) ⟨30248351, by rfl⟩ : syracuseStep 40331135 = 60496703) B60496703
theorem B26887423 : Blo 2069435 26887423 := bstep (se 1 (by rfl) ⟨20165567, by rfl⟩ : syracuseStep 26887423 = 40331135) B40331135
theorem B35849897 : Blo 2069435 35849897 := bstep (se 2 (by rfl) ⟨13443711, by rfl⟩ : syracuseStep 35849897 = 26887423) B26887423
theorem B23899931 : Blo 2069435 23899931 := bstep (se 1 (by rfl) ⟨17924948, by rfl⟩ : syracuseStep 23899931 = 35849897) B35849897
theorem B15933287 : Blo 2069435 15933287 := bstep (se 1 (by rfl) ⟨11949965, by rfl⟩ : syracuseStep 15933287 = 23899931) B23899931
theorem B10622191 : Blo 2069435 10622191 := bstep (se 1 (by rfl) ⟨7966643, by rfl⟩ : syracuseStep 10622191 = 15933287) B15933287
theorem B14162921 : Blo 2069435 14162921 := bstep (se 2 (by rfl) ⟨5311095, by rfl⟩ : syracuseStep 14162921 = 10622191) B10622191
theorem B9441947 : Blo 2069435 9441947 := bstep (se 1 (by rfl) ⟨7081460, by rfl⟩ : syracuseStep 9441947 = 14162921) B14162921
theorem B6294631 : Blo 2069435 6294631 := bstep (se 1 (by rfl) ⟨4720973, by rfl⟩ : syracuseStep 6294631 = 9441947) B9441947
theorem B8392841 : Blo 2069435 8392841 := bstep (se 2 (by rfl) ⟨3147315, by rfl⟩ : syracuseStep 8392841 = 6294631) B6294631
theorem B5595227 : Blo 2069435 5595227 := bstep (se 1 (by rfl) ⟨4196420, by rfl⟩ : syracuseStep 5595227 = 8392841) B8392841
theorem B3730151 : Blo 2069435 3730151 := bstep (se 1 (by rfl) ⟨2797613, by rfl⟩ : syracuseStep 3730151 = 5595227) B5595227
theorem B9947069 : Blo 2069435 9947069 := bstep (se 3 (by rfl) ⟨1865075, by rfl⟩ : syracuseStep 9947069 = 3730151) B3730151
theorem B6631379 : Blo 2069435 6631379 := bstep (se 1 (by rfl) ⟨4973534, by rfl⟩ : syracuseStep 6631379 = 9947069) B9947069
theorem B4420919 : Blo 2069435 4420919 := bstep (se 1 (by rfl) ⟨3315689, by rfl⟩ : syracuseStep 4420919 = 6631379) B6631379
theorem B2947279 : Blo 2069435 2947279 := bstep (se 1 (by rfl) ⟨2210459, by rfl⟩ : syracuseStep 2947279 = 4420919) B4420919
theorem B3929705 : Blo 2069435 3929705 := bstep (se 2 (by rfl) ⟨1473639, by rfl⟩ : syracuseStep 3929705 = 2947279) B2947279
theorem B2619803 : Blo 2069435 2619803 := bstep (se 1 (by rfl) ⟨1964852, by rfl⟩ : syracuseStep 2619803 = 3929705) B3929705
theorem B6986141 : Blo 2069435 6986141 := bstep (se 3 (by rfl) ⟨1309901, by rfl⟩ : syracuseStep 6986141 = 2619803) B2619803
theorem B4657427 : Blo 2069435 4657427 := bstep (se 1 (by rfl) ⟨3493070, by rfl⟩ : syracuseStep 4657427 = 6986141) B6986141
theorem B3104951 : Blo 2069435 3104951 := bstep (se 1 (by rfl) ⟨2328713, by rfl⟩ : syracuseStep 3104951 = 4657427) B4657427
theorem B2069967 : Blo 2069435 2069967 := bstep (se 1 (by rfl) ⟨1552475, by rfl⟩ : syracuseStep 2069967 = 3104951) B3104951
theorem B3104957 : Blo 2069435 3104957 := bbase (se 3 (by rfl) ⟨582179, by rfl⟩ : syracuseStep 3104957 = 1164359) (by norm_num)
theorem B2069971 : Blo 2069435 2069971 := bstep (se 1 (by rfl) ⟨1552478, by rfl⟩ : syracuseStep 2069971 = 3104957) B3104957
theorem B4657445 : Blo 2069435 4657445 := bbase (se 4 (by rfl) ⟨436635, by rfl⟩ : syracuseStep 4657445 = 873271) (by norm_num)
theorem B3104963 : Blo 2069435 3104963 := bstep (se 1 (by rfl) ⟨2328722, by rfl⟩ : syracuseStep 3104963 = 4657445) B4657445
theorem B2069975 : Blo 2069435 2069975 := bstep (se 1 (by rfl) ⟨1552481, by rfl⟩ : syracuseStep 2069975 = 3104963) B3104963
theorem B5239637 : Blo 2069435 5239637 := bbase (se 9 (by rfl) ⟨15350, by rfl⟩ : syracuseStep 5239637 = 30701) (by norm_num)
theorem B3493091 : Blo 2069435 3493091 := bstep (se 1 (by rfl) ⟨2619818, by rfl⟩ : syracuseStep 3493091 = 5239637) B5239637
theorem B2328727 : Blo 2069435 2328727 := bstep (se 1 (by rfl) ⟨1746545, by rfl⟩ : syracuseStep 2328727 = 3493091) B3493091
theorem B3104969 : Blo 2069435 3104969 := bstep (se 2 (by rfl) ⟨1164363, by rfl⟩ : syracuseStep 3104969 = 2328727) B2328727
theorem B2069979 : Blo 2069435 2069979 := bstep (se 1 (by rfl) ⟨1552484, by rfl⟩ : syracuseStep 2069979 = 3104969) B3104969
theorem B6631429 : Blo 2069435 6631429 := bbase (se 4 (by rfl) ⟨621696, by rfl⟩ : syracuseStep 6631429 = 1243393) (by norm_num)
theorem B8841905 : Blo 2069435 8841905 := bstep (se 2 (by rfl) ⟨3315714, by rfl⟩ : syracuseStep 8841905 = 6631429) B6631429
theorem B5894603 : Blo 2069435 5894603 := bstep (se 1 (by rfl) ⟨4420952, by rfl⟩ : syracuseStep 5894603 = 8841905) B8841905
theorem B3929735 : Blo 2069435 3929735 := bstep (se 1 (by rfl) ⟨2947301, by rfl⟩ : syracuseStep 3929735 = 5894603) B5894603
theorem B10479293 : Blo 2069435 10479293 := bstep (se 3 (by rfl) ⟨1964867, by rfl⟩ : syracuseStep 10479293 = 3929735) B3929735
theorem B6986195 : Blo 2069435 6986195 := bstep (se 1 (by rfl) ⟨5239646, by rfl⟩ : syracuseStep 6986195 = 10479293) B10479293
theorem B4657463 : Blo 2069435 4657463 := bstep (se 1 (by rfl) ⟨3493097, by rfl⟩ : syracuseStep 4657463 = 6986195) B6986195
theorem B3104975 : Blo 2069435 3104975 := bstep (se 1 (by rfl) ⟨2328731, by rfl⟩ : syracuseStep 3104975 = 4657463) B4657463
theorem B2069983 : Blo 2069435 2069983 := bstep (se 1 (by rfl) ⟨1552487, by rfl⟩ : syracuseStep 2069983 = 3104975) B3104975
theorem B3104981 : Blo 2069435 3104981 := bbase (se 7 (by rfl) ⟨36386, by rfl⟩ : syracuseStep 3104981 = 72773) (by norm_num)
theorem B2069987 : Blo 2069435 2069987 := bstep (se 1 (by rfl) ⟨1552490, by rfl⟩ : syracuseStep 2069987 = 3104981) B3104981
theorem B2210485 : Blo 2069435 2210485 := bbase (se 5 (by rfl) ⟨103616, by rfl⟩ : syracuseStep 2210485 = 207233) (by norm_num)
theorem B2947313 : Blo 2069435 2947313 := bstep (se 2 (by rfl) ⟨1105242, by rfl⟩ : syracuseStep 2947313 = 2210485) B2210485
theorem B7859501 : Blo 2069435 7859501 := bstep (se 3 (by rfl) ⟨1473656, by rfl⟩ : syracuseStep 7859501 = 2947313) B2947313
theorem B5239667 : Blo 2069435 5239667 := bstep (se 1 (by rfl) ⟨3929750, by rfl⟩ : syracuseStep 5239667 = 7859501) B7859501
theorem B3493111 : Blo 2069435 3493111 := bstep (se 1 (by rfl) ⟨2619833, by rfl⟩ : syracuseStep 3493111 = 5239667) B5239667
theorem B4657481 : Blo 2069435 4657481 := bstep (se 2 (by rfl) ⟨1746555, by rfl⟩ : syracuseStep 4657481 = 3493111) B3493111
theorem B3104987 : Blo 2069435 3104987 := bstep (se 1 (by rfl) ⟨2328740, by rfl⟩ : syracuseStep 3104987 = 4657481) B4657481
theorem B2069991 : Blo 2069435 2069991 := bstep (se 1 (by rfl) ⟨1552493, by rfl⟩ : syracuseStep 2069991 = 3104987) B3104987
theorem B2328745 : Blo 2069435 2328745 := bbase (se 2 (by rfl) ⟨873279, by rfl⟩ : syracuseStep 2328745 = 1746559) (by norm_num)
theorem B3104993 : Blo 2069435 3104993 := bstep (se 2 (by rfl) ⟨1164372, by rfl⟩ : syracuseStep 3104993 = 2328745) B2328745
theorem B2069995 : Blo 2069435 2069995 := bstep (se 1 (by rfl) ⟨1552496, by rfl⟩ : syracuseStep 2069995 = 3104993) B3104993
theorem B8841973 : Blo 2069435 8841973 := bbase (se 5 (by rfl) ⟨414467, by rfl⟩ : syracuseStep 8841973 = 828935) (by norm_num)
theorem B11789297 : Blo 2069435 11789297 := bstep (se 2 (by rfl) ⟨4420986, by rfl⟩ : syracuseStep 11789297 = 8841973) B8841973
theorem B7859531 : Blo 2069435 7859531 := bstep (se 1 (by rfl) ⟨5894648, by rfl⟩ : syracuseStep 7859531 = 11789297) B11789297
theorem B5239687 : Blo 2069435 5239687 := bstep (se 1 (by rfl) ⟨3929765, by rfl⟩ : syracuseStep 5239687 = 7859531) B7859531
theorem B6986249 : Blo 2069435 6986249 := bstep (se 2 (by rfl) ⟨2619843, by rfl⟩ : syracuseStep 6986249 = 5239687) B5239687
theorem B4657499 : Blo 2069435 4657499 := bstep (se 1 (by rfl) ⟨3493124, by rfl⟩ : syracuseStep 4657499 = 6986249) B6986249
theorem B3104999 : Blo 2069435 3104999 := bstep (se 1 (by rfl) ⟨2328749, by rfl⟩ : syracuseStep 3104999 = 4657499) B4657499
theorem B2069999 : Blo 2069435 2069999 := bstep (se 1 (by rfl) ⟨1552499, by rfl⟩ : syracuseStep 2069999 = 3104999) B3104999
theorem B3105005 : Blo 2069435 3105005 := bbase (se 3 (by rfl) ⟨582188, by rfl⟩ : syracuseStep 3105005 = 1164377) (by norm_num)
theorem B2070003 : Blo 2069435 2070003 := bstep (se 1 (by rfl) ⟨1552502, by rfl⟩ : syracuseStep 2070003 = 3105005) B3105005
theorem B4657517 : Blo 2069435 4657517 := bbase (se 3 (by rfl) ⟨873284, by rfl⟩ : syracuseStep 4657517 = 1746569) (by norm_num)
theorem B3105011 : Blo 2069435 3105011 := bstep (se 1 (by rfl) ⟨2328758, by rfl⟩ : syracuseStep 3105011 = 4657517) B4657517
theorem B2070007 : Blo 2069435 2070007 := bstep (se 1 (by rfl) ⟨1552505, by rfl⟩ : syracuseStep 2070007 = 3105011) B3105011
theorem B3929789 : Blo 2069435 3929789 := bbase (se 3 (by rfl) ⟨736835, by rfl⟩ : syracuseStep 3929789 = 1473671) (by norm_num)
theorem B2619859 : Blo 2069435 2619859 := bstep (se 1 (by rfl) ⟨1964894, by rfl⟩ : syracuseStep 2619859 = 3929789) B3929789
theorem B3493145 : Blo 2069435 3493145 := bstep (se 2 (by rfl) ⟨1309929, by rfl⟩ : syracuseStep 3493145 = 2619859) B2619859
theorem B2328763 : Blo 2069435 2328763 := bstep (se 1 (by rfl) ⟨1746572, by rfl⟩ : syracuseStep 2328763 = 3493145) B3493145
theorem B3105017 : Blo 2069435 3105017 := bstep (se 2 (by rfl) ⟨1164381, by rfl⟩ : syracuseStep 3105017 = 2328763) B2328763
theorem B2070011 : Blo 2069435 2070011 := bstep (se 1 (by rfl) ⟨1552508, by rfl⟩ : syracuseStep 2070011 = 3105017) B3105017
theorem B53052245 : Blo 2069435 53052245 := bbase (se 9 (by rfl) ⟨155426, by rfl⟩ : syracuseStep 53052245 = 310853) (by norm_num)
theorem B35368163 : Blo 2069435 35368163 := bstep (se 1 (by rfl) ⟨26526122, by rfl⟩ : syracuseStep 35368163 = 53052245) B53052245
theorem B23578775 : Blo 2069435 23578775 := bstep (se 1 (by rfl) ⟨17684081, by rfl⟩ : syracuseStep 23578775 = 35368163) B35368163
theorem B15719183 : Blo 2069435 15719183 := bstep (se 1 (by rfl) ⟨11789387, by rfl⟩ : syracuseStep 15719183 = 23578775) B23578775
theorem B10479455 : Blo 2069435 10479455 := bstep (se 1 (by rfl) ⟨7859591, by rfl⟩ : syracuseStep 10479455 = 15719183) B15719183
theorem B6986303 : Blo 2069435 6986303 := bstep (se 1 (by rfl) ⟨5239727, by rfl⟩ : syracuseStep 6986303 = 10479455) B10479455
theorem B4657535 : Blo 2069435 4657535 := bstep (se 1 (by rfl) ⟨3493151, by rfl⟩ : syracuseStep 4657535 = 6986303) B6986303
theorem B3105023 : Blo 2069435 3105023 := bstep (se 1 (by rfl) ⟨2328767, by rfl⟩ : syracuseStep 3105023 = 4657535) B4657535
theorem B2070015 : Blo 2069435 2070015 := bstep (se 1 (by rfl) ⟨1552511, by rfl⟩ : syracuseStep 2070015 = 3105023) B3105023
theorem B3105029 : Blo 2069435 3105029 := bbase (se 4 (by rfl) ⟨291096, by rfl⟩ : syracuseStep 3105029 = 582193) (by norm_num)
theorem B2070019 : Blo 2069435 2070019 := bstep (se 1 (by rfl) ⟨1552514, by rfl⟩ : syracuseStep 2070019 = 3105029) B3105029
theorem B3493165 : Blo 2069435 3493165 := bbase (se 3 (by rfl) ⟨654968, by rfl⟩ : syracuseStep 3493165 = 1309937) (by norm_num)
theorem B4657553 : Blo 2069435 4657553 := bstep (se 2 (by rfl) ⟨1746582, by rfl⟩ : syracuseStep 4657553 = 3493165) B3493165
theorem B3105035 : Blo 2069435 3105035 := bstep (se 1 (by rfl) ⟨2328776, by rfl⟩ : syracuseStep 3105035 = 4657553) B4657553
theorem B2070023 : Blo 2069435 2070023 := bstep (se 1 (by rfl) ⟨1552517, by rfl⟩ : syracuseStep 2070023 = 3105035) B3105035
theorem B2328781 : Blo 2069435 2328781 := bbase (se 3 (by rfl) ⟨436646, by rfl⟩ : syracuseStep 2328781 = 873293) (by norm_num)
theorem B3105041 : Blo 2069435 3105041 := bstep (se 2 (by rfl) ⟨1164390, by rfl⟩ : syracuseStep 3105041 = 2328781) B2328781
theorem B2070027 : Blo 2069435 2070027 := bstep (se 1 (by rfl) ⟨1552520, by rfl⟩ : syracuseStep 2070027 = 3105041) B3105041
theorem B6986357 : Blo 2069435 6986357 := bbase (se 5 (by rfl) ⟨327485, by rfl⟩ : syracuseStep 6986357 = 654971) (by norm_num)
theorem B4657571 : Blo 2069435 4657571 := bstep (se 1 (by rfl) ⟨3493178, by rfl⟩ : syracuseStep 4657571 = 6986357) B6986357
theorem B3105047 : Blo 2069435 3105047 := bstep (se 1 (by rfl) ⟨2328785, by rfl⟩ : syracuseStep 3105047 = 4657571) B4657571
theorem B2070031 : Blo 2069435 2070031 := bstep (se 1 (by rfl) ⟨1552523, by rfl⟩ : syracuseStep 2070031 = 3105047) B3105047
theorem B3105053 : Blo 2069435 3105053 := bbase (se 3 (by rfl) ⟨582197, by rfl⟩ : syracuseStep 3105053 = 1164395) (by norm_num)
theorem B2070035 : Blo 2069435 2070035 := bstep (se 1 (by rfl) ⟨1552526, by rfl⟩ : syracuseStep 2070035 = 3105053) B3105053
theorem B4657589 : Blo 2069435 4657589 := bbase (se 5 (by rfl) ⟨218324, by rfl⟩ : syracuseStep 4657589 = 436649) (by norm_num)
theorem B3105059 : Blo 2069435 3105059 := bstep (se 1 (by rfl) ⟨2328794, by rfl⟩ : syracuseStep 3105059 = 4657589) B4657589
theorem B2070039 : Blo 2069435 2070039 := bstep (se 1 (by rfl) ⟨1552529, by rfl⟩ : syracuseStep 2070039 = 3105059) B3105059
theorem B4973717 : Blo 2069435 4973717 := bbase (se 6 (by rfl) ⟨116571, by rfl⟩ : syracuseStep 4973717 = 233143) (by norm_num)
theorem B3315811 : Blo 2069435 3315811 := bstep (se 1 (by rfl) ⟨2486858, by rfl⟩ : syracuseStep 3315811 = 4973717) B4973717
theorem B4421081 : Blo 2069435 4421081 := bstep (se 2 (by rfl) ⟨1657905, by rfl⟩ : syracuseStep 4421081 = 3315811) B3315811
theorem B11789549 : Blo 2069435 11789549 := bstep (se 3 (by rfl) ⟨2210540, by rfl⟩ : syracuseStep 11789549 = 4421081) B4421081
theorem B7859699 : Blo 2069435 7859699 := bstep (se 1 (by rfl) ⟨5894774, by rfl⟩ : syracuseStep 7859699 = 11789549) B11789549
theorem B5239799 : Blo 2069435 5239799 := bstep (se 1 (by rfl) ⟨3929849, by rfl⟩ : syracuseStep 5239799 = 7859699) B7859699
theorem B3493199 : Blo 2069435 3493199 := bstep (se 1 (by rfl) ⟨2619899, by rfl⟩ : syracuseStep 3493199 = 5239799) B5239799
theorem B2328799 : Blo 2069435 2328799 := bstep (se 1 (by rfl) ⟨1746599, by rfl⟩ : syracuseStep 2328799 = 3493199) B3493199
theorem B3105065 : Blo 2069435 3105065 := bstep (se 2 (by rfl) ⟨1164399, by rfl⟩ : syracuseStep 3105065 = 2328799) B2328799
theorem B2070043 : Blo 2069435 2070043 := bstep (se 1 (by rfl) ⟨1552532, by rfl⟩ : syracuseStep 2070043 = 3105065) B3105065
theorem B3147437 : Blo 2069435 3147437 := bbase (se 3 (by rfl) ⟨590144, by rfl⟩ : syracuseStep 3147437 = 1180289) (by norm_num)
theorem B8393165 : Blo 2069435 8393165 := bstep (se 3 (by rfl) ⟨1573718, by rfl⟩ : syracuseStep 8393165 = 3147437) B3147437
theorem B5595443 : Blo 2069435 5595443 := bstep (se 1 (by rfl) ⟨4196582, by rfl⟩ : syracuseStep 5595443 = 8393165) B8393165
theorem B3730295 : Blo 2069435 3730295 := bstep (se 1 (by rfl) ⟨2797721, by rfl⟩ : syracuseStep 3730295 = 5595443) B5595443
theorem B2486863 : Blo 2069435 2486863 := bstep (se 1 (by rfl) ⟨1865147, by rfl⟩ : syracuseStep 2486863 = 3730295) B3730295
theorem B3315817 : Blo 2069435 3315817 := bstep (se 2 (by rfl) ⟨1243431, by rfl⟩ : syracuseStep 3315817 = 2486863) B2486863
theorem B4421089 : Blo 2069435 4421089 := bstep (se 2 (by rfl) ⟨1657908, by rfl⟩ : syracuseStep 4421089 = 3315817) B3315817
theorem B5894785 : Blo 2069435 5894785 := bstep (se 2 (by rfl) ⟨2210544, by rfl⟩ : syracuseStep 5894785 = 4421089) B4421089
theorem B7859713 : Blo 2069435 7859713 := bstep (se 2 (by rfl) ⟨2947392, by rfl⟩ : syracuseStep 7859713 = 5894785) B5894785
theorem B10479617 : Blo 2069435 10479617 := bstep (se 2 (by rfl) ⟨3929856, by rfl⟩ : syracuseStep 10479617 = 7859713) B7859713
theorem B6986411 : Blo 2069435 6986411 := bstep (se 1 (by rfl) ⟨5239808, by rfl⟩ : syracuseStep 6986411 = 10479617) B10479617
theorem B4657607 : Blo 2069435 4657607 := bstep (se 1 (by rfl) ⟨3493205, by rfl⟩ : syracuseStep 4657607 = 6986411) B6986411
theorem B3105071 : Blo 2069435 3105071 := bstep (se 1 (by rfl) ⟨2328803, by rfl⟩ : syracuseStep 3105071 = 4657607) B4657607
theorem B2070047 : Blo 2069435 2070047 := bstep (se 1 (by rfl) ⟨1552535, by rfl⟩ : syracuseStep 2070047 = 3105071) B3105071
theorem B3105077 : Blo 2069435 3105077 := bbase (se 5 (by rfl) ⟨145550, by rfl⟩ : syracuseStep 3105077 = 291101) (by norm_num)
theorem B2070051 : Blo 2069435 2070051 := bstep (se 1 (by rfl) ⟨1552538, by rfl⟩ : syracuseStep 2070051 = 3105077) B3105077
theorem B5239829 : Blo 2069435 5239829 := bbase (se 6 (by rfl) ⟨122808, by rfl⟩ : syracuseStep 5239829 = 245617) (by norm_num)
theorem B3493219 : Blo 2069435 3493219 := bstep (se 1 (by rfl) ⟨2619914, by rfl⟩ : syracuseStep 3493219 = 5239829) B5239829
theorem B4657625 : Blo 2069435 4657625 := bstep (se 2 (by rfl) ⟨1746609, by rfl⟩ : syracuseStep 4657625 = 3493219) B3493219
theorem B3105083 : Blo 2069435 3105083 := bstep (se 1 (by rfl) ⟨2328812, by rfl⟩ : syracuseStep 3105083 = 4657625) B4657625
theorem B2070055 : Blo 2069435 2070055 := bstep (se 1 (by rfl) ⟨1552541, by rfl⟩ : syracuseStep 2070055 = 3105083) B3105083
theorem B2328817 : Blo 2069435 2328817 := bbase (se 2 (by rfl) ⟨873306, by rfl⟩ : syracuseStep 2328817 = 1746613) (by norm_num)
theorem B3105089 : Blo 2069435 3105089 := bstep (se 2 (by rfl) ⟨1164408, by rfl⟩ : syracuseStep 3105089 = 2328817) B2328817
theorem B2070059 : Blo 2069435 2070059 := bstep (se 1 (by rfl) ⟨1552544, by rfl⟩ : syracuseStep 2070059 = 3105089) B3105089
theorem B3147461 : Blo 2069435 3147461 := bbase (se 4 (by rfl) ⟨295074, by rfl⟩ : syracuseStep 3147461 = 590149) (by norm_num)
theorem B2098307 : Blo 2069435 2098307 := bstep (se 1 (by rfl) ⟨1573730, by rfl⟩ : syracuseStep 2098307 = 3147461) B3147461
theorem B5595485 : Blo 2069435 5595485 := bstep (se 3 (by rfl) ⟨1049153, by rfl⟩ : syracuseStep 5595485 = 2098307) B2098307
theorem B14921293 : Blo 2069435 14921293 := bstep (se 3 (by rfl) ⟨2797742, by rfl⟩ : syracuseStep 14921293 = 5595485) B5595485
theorem B19895057 : Blo 2069435 19895057 := bstep (se 2 (by rfl) ⟨7460646, by rfl⟩ : syracuseStep 19895057 = 14921293) B14921293
theorem B13263371 : Blo 2069435 13263371 := bstep (se 1 (by rfl) ⟨9947528, by rfl⟩ : syracuseStep 13263371 = 19895057) B19895057
theorem B8842247 : Blo 2069435 8842247 := bstep (se 1 (by rfl) ⟨6631685, by rfl⟩ : syracuseStep 8842247 = 13263371) B13263371
theorem B5894831 : Blo 2069435 5894831 := bstep (se 1 (by rfl) ⟨4421123, by rfl⟩ : syracuseStep 5894831 = 8842247) B8842247
theorem B3929887 : Blo 2069435 3929887 := bstep (se 1 (by rfl) ⟨2947415, by rfl⟩ : syracuseStep 3929887 = 5894831) B5894831
theorem B5239849 : Blo 2069435 5239849 := bstep (se 2 (by rfl) ⟨1964943, by rfl⟩ : syracuseStep 5239849 = 3929887) B3929887
theorem B6986465 : Blo 2069435 6986465 := bstep (se 2 (by rfl) ⟨2619924, by rfl⟩ : syracuseStep 6986465 = 5239849) B5239849
theorem B4657643 : Blo 2069435 4657643 := bstep (se 1 (by rfl) ⟨3493232, by rfl⟩ : syracuseStep 4657643 = 6986465) B6986465
theorem B3105095 : Blo 2069435 3105095 := bstep (se 1 (by rfl) ⟨2328821, by rfl⟩ : syracuseStep 3105095 = 4657643) B4657643
theorem B2070063 : Blo 2069435 2070063 := bstep (se 1 (by rfl) ⟨1552547, by rfl⟩ : syracuseStep 2070063 = 3105095) B3105095
theorem B3105101 : Blo 2069435 3105101 := bbase (se 3 (by rfl) ⟨582206, by rfl⟩ : syracuseStep 3105101 = 1164413) (by norm_num)
theorem B2070067 : Blo 2069435 2070067 := bstep (se 1 (by rfl) ⟨1552550, by rfl⟩ : syracuseStep 2070067 = 3105101) B3105101
theorem B4657661 : Blo 2069435 4657661 := bbase (se 3 (by rfl) ⟨873311, by rfl⟩ : syracuseStep 4657661 = 1746623) (by norm_num)
theorem B3105107 : Blo 2069435 3105107 := bstep (se 1 (by rfl) ⟨2328830, by rfl⟩ : syracuseStep 3105107 = 4657661) B4657661
theorem B2070071 : Blo 2069435 2070071 := bstep (se 1 (by rfl) ⟨1552553, by rfl⟩ : syracuseStep 2070071 = 3105107) B3105107
theorem B3493253 : Blo 2069435 3493253 := bbase (se 4 (by rfl) ⟨327492, by rfl⟩ : syracuseStep 3493253 = 654985) (by norm_num)
theorem B2328835 : Blo 2069435 2328835 := bstep (se 1 (by rfl) ⟨1746626, by rfl⟩ : syracuseStep 2328835 = 3493253) B3493253
theorem B3105113 : Blo 2069435 3105113 := bstep (se 2 (by rfl) ⟨1164417, by rfl⟩ : syracuseStep 3105113 = 2328835) B2328835
theorem B2070075 : Blo 2069435 2070075 := bstep (se 1 (by rfl) ⟨1552556, by rfl⟩ : syracuseStep 2070075 = 3105113) B3105113
theorem B15719669 : Blo 2069435 15719669 := bbase (se 5 (by rfl) ⟨736859, by rfl⟩ : syracuseStep 15719669 = 1473719) (by norm_num)
theorem B10479779 : Blo 2069435 10479779 := bstep (se 1 (by rfl) ⟨7859834, by rfl⟩ : syracuseStep 10479779 = 15719669) B15719669
theorem B6986519 : Blo 2069435 6986519 := bstep (se 1 (by rfl) ⟨5239889, by rfl⟩ : syracuseStep 6986519 = 10479779) B10479779
theorem B4657679 : Blo 2069435 4657679 := bstep (se 1 (by rfl) ⟨3493259, by rfl⟩ : syracuseStep 4657679 = 6986519) B6986519
theorem B3105119 : Blo 2069435 3105119 := bstep (se 1 (by rfl) ⟨2328839, by rfl⟩ : syracuseStep 3105119 = 4657679) B4657679
theorem B2070079 : Blo 2069435 2070079 := bstep (se 1 (by rfl) ⟨1552559, by rfl⟩ : syracuseStep 2070079 = 3105119) B3105119
theorem B3105125 : Blo 2069435 3105125 := bbase (se 4 (by rfl) ⟨291105, by rfl⟩ : syracuseStep 3105125 = 582211) (by norm_num)
theorem B2070083 : Blo 2069435 2070083 := bstep (se 1 (by rfl) ⟨1552562, by rfl⟩ : syracuseStep 2070083 = 3105125) B3105125
theorem B3929933 : Blo 2069435 3929933 := bbase (se 3 (by rfl) ⟨736862, by rfl⟩ : syracuseStep 3929933 = 1473725) (by norm_num)
theorem B2619955 : Blo 2069435 2619955 := bstep (se 1 (by rfl) ⟨1964966, by rfl⟩ : syracuseStep 2619955 = 3929933) B3929933
theorem B3493273 : Blo 2069435 3493273 := bstep (se 2 (by rfl) ⟨1309977, by rfl⟩ : syracuseStep 3493273 = 2619955) B2619955
theorem B4657697 : Blo 2069435 4657697 := bstep (se 2 (by rfl) ⟨1746636, by rfl⟩ : syracuseStep 4657697 = 3493273) B3493273
theorem B3105131 : Blo 2069435 3105131 := bstep (se 1 (by rfl) ⟨2328848, by rfl⟩ : syracuseStep 3105131 = 4657697) B4657697
theorem B2070087 : Blo 2069435 2070087 := bstep (se 1 (by rfl) ⟨1552565, by rfl⟩ : syracuseStep 2070087 = 3105131) B3105131
theorem B2328853 : Blo 2069435 2328853 := bbase (se 6 (by rfl) ⟨54582, by rfl⟩ : syracuseStep 2328853 = 109165) (by norm_num)
theorem B3105137 : Blo 2069435 3105137 := bstep (se 2 (by rfl) ⟨1164426, by rfl⟩ : syracuseStep 3105137 = 2328853) B2328853
theorem B2070091 : Blo 2069435 2070091 := bstep (se 1 (by rfl) ⟨1552568, by rfl⟩ : syracuseStep 2070091 = 3105137) B3105137
theorem B2619965 : Blo 2069435 2619965 := bbase (se 3 (by rfl) ⟨491243, by rfl⟩ : syracuseStep 2619965 = 982487) (by norm_num)
theorem B6986573 : Blo 2069435 6986573 := bstep (se 3 (by rfl) ⟨1309982, by rfl⟩ : syracuseStep 6986573 = 2619965) B2619965
theorem B4657715 : Blo 2069435 4657715 := bstep (se 1 (by rfl) ⟨3493286, by rfl⟩ : syracuseStep 4657715 = 6986573) B6986573
theorem B3105143 : Blo 2069435 3105143 := bstep (se 1 (by rfl) ⟨2328857, by rfl⟩ : syracuseStep 3105143 = 4657715) B4657715
theorem B2070095 : Blo 2069435 2070095 := bstep (se 1 (by rfl) ⟨1552571, by rfl⟩ : syracuseStep 2070095 = 3105143) B3105143
theorem B3105149 : Blo 2069435 3105149 := bbase (se 3 (by rfl) ⟨582215, by rfl⟩ : syracuseStep 3105149 = 1164431) (by norm_num)
theorem B2070099 : Blo 2069435 2070099 := bstep (se 1 (by rfl) ⟨1552574, by rfl⟩ : syracuseStep 2070099 = 3105149) B3105149
theorem B4657733 : Blo 2069435 4657733 := bbase (se 4 (by rfl) ⟨436662, by rfl⟩ : syracuseStep 4657733 = 873325) (by norm_num)
theorem B3105155 : Blo 2069435 3105155 := bstep (se 1 (by rfl) ⟨2328866, by rfl⟩ : syracuseStep 3105155 = 4657733) B4657733
theorem B2070103 : Blo 2069435 2070103 := bstep (se 1 (by rfl) ⟨1552577, by rfl⟩ : syracuseStep 2070103 = 3105155) B3105155
theorem B2210609 : Blo 2069435 2210609 := bbase (se 2 (by rfl) ⟨828978, by rfl⟩ : syracuseStep 2210609 = 1657957) (by norm_num)
theorem B5894957 : Blo 2069435 5894957 := bstep (se 3 (by rfl) ⟨1105304, by rfl⟩ : syracuseStep 5894957 = 2210609) B2210609
theorem B3929971 : Blo 2069435 3929971 := bstep (se 1 (by rfl) ⟨2947478, by rfl⟩ : syracuseStep 3929971 = 5894957) B5894957
theorem B5239961 : Blo 2069435 5239961 := bstep (se 2 (by rfl) ⟨1964985, by rfl⟩ : syracuseStep 5239961 = 3929971) B3929971
theorem B3493307 : Blo 2069435 3493307 := bstep (se 1 (by rfl) ⟨2619980, by rfl⟩ : syracuseStep 3493307 = 5239961) B5239961
theorem B2328871 : Blo 2069435 2328871 := bstep (se 1 (by rfl) ⟨1746653, by rfl⟩ : syracuseStep 2328871 = 3493307) B3493307
theorem B3105161 : Blo 2069435 3105161 := bstep (se 2 (by rfl) ⟨1164435, by rfl⟩ : syracuseStep 3105161 = 2328871) B2328871
theorem B2070107 : Blo 2069435 2070107 := bstep (se 1 (by rfl) ⟨1552580, by rfl⟩ : syracuseStep 2070107 = 3105161) B3105161
theorem B10479941 : Blo 2069435 10479941 := bbase (se 4 (by rfl) ⟨982494, by rfl⟩ : syracuseStep 10479941 = 1964989) (by norm_num)
theorem B6986627 : Blo 2069435 6986627 := bstep (se 1 (by rfl) ⟨5239970, by rfl⟩ : syracuseStep 6986627 = 10479941) B10479941
theorem B4657751 : Blo 2069435 4657751 := bstep (se 1 (by rfl) ⟨3493313, by rfl⟩ : syracuseStep 4657751 = 6986627) B6986627
theorem B3105167 : Blo 2069435 3105167 := bstep (se 1 (by rfl) ⟨2328875, by rfl⟩ : syracuseStep 3105167 = 4657751) B4657751
theorem B2070111 : Blo 2069435 2070111 := bstep (se 1 (by rfl) ⟨1552583, by rfl⟩ : syracuseStep 2070111 = 3105167) B3105167
theorem B3105173 : Blo 2069435 3105173 := bbase (se 6 (by rfl) ⟨72777, by rfl⟩ : syracuseStep 3105173 = 145555) (by norm_num)
theorem B2070115 : Blo 2069435 2070115 := bstep (se 1 (by rfl) ⟨1552586, by rfl⟩ : syracuseStep 2070115 = 3105173) B3105173
theorem B5595637 : Blo 2069435 5595637 := bbase (se 5 (by rfl) ⟨262295, by rfl⟩ : syracuseStep 5595637 = 524591) (by norm_num)
theorem B7460849 : Blo 2069435 7460849 := bstep (se 2 (by rfl) ⟨2797818, by rfl⟩ : syracuseStep 7460849 = 5595637) B5595637
theorem B4973899 : Blo 2069435 4973899 := bstep (se 1 (by rfl) ⟨3730424, by rfl⟩ : syracuseStep 4973899 = 7460849) B7460849
theorem B6631865 : Blo 2069435 6631865 := bstep (se 2 (by rfl) ⟨2486949, by rfl⟩ : syracuseStep 6631865 = 4973899) B4973899
theorem B4421243 : Blo 2069435 4421243 := bstep (se 1 (by rfl) ⟨3315932, by rfl⟩ : syracuseStep 4421243 = 6631865) B6631865
theorem B11789981 : Blo 2069435 11789981 := bstep (se 3 (by rfl) ⟨2210621, by rfl⟩ : syracuseStep 11789981 = 4421243) B4421243
theorem B7859987 : Blo 2069435 7859987 := bstep (se 1 (by rfl) ⟨5894990, by rfl⟩ : syracuseStep 7859987 = 11789981) B11789981
theorem B5239991 : Blo 2069435 5239991 := bstep (se 1 (by rfl) ⟨3929993, by rfl⟩ : syracuseStep 5239991 = 7859987) B7859987
theorem B3493327 : Blo 2069435 3493327 := bstep (se 1 (by rfl) ⟨2619995, by rfl⟩ : syracuseStep 3493327 = 5239991) B5239991
theorem B4657769 : Blo 2069435 4657769 := bstep (se 2 (by rfl) ⟨1746663, by rfl⟩ : syracuseStep 4657769 = 3493327) B3493327
theorem B3105179 : Blo 2069435 3105179 := bstep (se 1 (by rfl) ⟨2328884, by rfl⟩ : syracuseStep 3105179 = 4657769) B4657769
theorem B2070119 : Blo 2069435 2070119 := bstep (se 1 (by rfl) ⟨1552589, by rfl⟩ : syracuseStep 2070119 = 3105179) B3105179
theorem B2328889 : Blo 2069435 2328889 := bbase (se 2 (by rfl) ⟨873333, by rfl⟩ : syracuseStep 2328889 = 1746667) (by norm_num)
theorem B3105185 : Blo 2069435 3105185 := bstep (se 2 (by rfl) ⟨1164444, by rfl⟩ : syracuseStep 3105185 = 2328889) B2328889
theorem B2070123 : Blo 2069435 2070123 := bstep (se 1 (by rfl) ⟨1552592, by rfl⟩ : syracuseStep 2070123 = 3105185) B3105185
theorem B5895013 : Blo 2069435 5895013 := bbase (se 4 (by rfl) ⟨552657, by rfl⟩ : syracuseStep 5895013 = 1105315) (by norm_num)
theorem B7860017 : Blo 2069435 7860017 := bstep (se 2 (by rfl) ⟨2947506, by rfl⟩ : syracuseStep 7860017 = 5895013) B5895013
theorem B5240011 : Blo 2069435 5240011 := bstep (se 1 (by rfl) ⟨3930008, by rfl⟩ : syracuseStep 5240011 = 7860017) B7860017
theorem B6986681 : Blo 2069435 6986681 := bstep (se 2 (by rfl) ⟨2620005, by rfl⟩ : syracuseStep 6986681 = 5240011) B5240011
theorem B4657787 : Blo 2069435 4657787 := bstep (se 1 (by rfl) ⟨3493340, by rfl⟩ : syracuseStep 4657787 = 6986681) B6986681
theorem B3105191 : Blo 2069435 3105191 := bstep (se 1 (by rfl) ⟨2328893, by rfl⟩ : syracuseStep 3105191 = 4657787) B4657787
theorem B2070127 : Blo 2069435 2070127 := bstep (se 1 (by rfl) ⟨1552595, by rfl⟩ : syracuseStep 2070127 = 3105191) B3105191
theorem B3105197 : Blo 2069435 3105197 := bbase (se 3 (by rfl) ⟨582224, by rfl⟩ : syracuseStep 3105197 = 1164449) (by norm_num)
theorem B2070131 : Blo 2069435 2070131 := bstep (se 1 (by rfl) ⟨1552598, by rfl⟩ : syracuseStep 2070131 = 3105197) B3105197
theorem B4657805 : Blo 2069435 4657805 := bbase (se 3 (by rfl) ⟨873338, by rfl⟩ : syracuseStep 4657805 = 1746677) (by norm_num)
theorem B3105203 : Blo 2069435 3105203 := bstep (se 1 (by rfl) ⟨2328902, by rfl⟩ : syracuseStep 3105203 = 4657805) B4657805
theorem B2070135 : Blo 2069435 2070135 := bstep (se 1 (by rfl) ⟨1552601, by rfl⟩ : syracuseStep 2070135 = 3105203) B3105203
theorem B2620021 : Blo 2069435 2620021 := bbase (se 5 (by rfl) ⟨122813, by rfl⟩ : syracuseStep 2620021 = 245627) (by norm_num)
theorem B3493361 : Blo 2069435 3493361 := bstep (se 2 (by rfl) ⟨1310010, by rfl⟩ : syracuseStep 3493361 = 2620021) B2620021
theorem B2328907 : Blo 2069435 2328907 := bstep (se 1 (by rfl) ⟨1746680, by rfl⟩ : syracuseStep 2328907 = 3493361) B3493361
theorem B3105209 : Blo 2069435 3105209 := bstep (se 2 (by rfl) ⟨1164453, by rfl⟩ : syracuseStep 3105209 = 2328907) B2328907
theorem B2070139 : Blo 2069435 2070139 := bstep (se 1 (by rfl) ⟨1552604, by rfl⟩ : syracuseStep 2070139 = 3105209) B3105209
theorem B7967317 : Blo 2069435 7967317 := bbase (se 8 (by rfl) ⟨46683, by rfl⟩ : syracuseStep 7967317 = 93367) (by norm_num)
theorem B10623089 : Blo 2069435 10623089 := bstep (se 2 (by rfl) ⟨3983658, by rfl⟩ : syracuseStep 10623089 = 7967317) B7967317
theorem B7082059 : Blo 2069435 7082059 := bstep (se 1 (by rfl) ⟨5311544, by rfl⟩ : syracuseStep 7082059 = 10623089) B10623089
theorem B9442745 : Blo 2069435 9442745 := bstep (se 2 (by rfl) ⟨3541029, by rfl⟩ : syracuseStep 9442745 = 7082059) B7082059
theorem B6295163 : Blo 2069435 6295163 := bstep (se 1 (by rfl) ⟨4721372, by rfl⟩ : syracuseStep 6295163 = 9442745) B9442745
theorem B16787101 : Blo 2069435 16787101 := bstep (se 3 (by rfl) ⟨3147581, by rfl⟩ : syracuseStep 16787101 = 6295163) B6295163
theorem B22382801 : Blo 2069435 22382801 := bstep (se 2 (by rfl) ⟨8393550, by rfl⟩ : syracuseStep 22382801 = 16787101) B16787101
theorem B14921867 : Blo 2069435 14921867 := bstep (se 1 (by rfl) ⟨11191400, by rfl⟩ : syracuseStep 14921867 = 22382801) B22382801
theorem B39791645 : Blo 2069435 39791645 := bstep (se 3 (by rfl) ⟨7460933, by rfl⟩ : syracuseStep 39791645 = 14921867) B14921867
theorem B26527763 : Blo 2069435 26527763 := bstep (se 1 (by rfl) ⟨19895822, by rfl⟩ : syracuseStep 26527763 = 39791645) B39791645
theorem B17685175 : Blo 2069435 17685175 := bstep (se 1 (by rfl) ⟨13263881, by rfl⟩ : syracuseStep 17685175 = 26527763) B26527763
theorem B23580233 : Blo 2069435 23580233 := bstep (se 2 (by rfl) ⟨8842587, by rfl⟩ : syracuseStep 23580233 = 17685175) B17685175
theorem B15720155 : Blo 2069435 15720155 := bstep (se 1 (by rfl) ⟨11790116, by rfl⟩ : syracuseStep 15720155 = 23580233) B23580233
theorem B10480103 : Blo 2069435 10480103 := bstep (se 1 (by rfl) ⟨7860077, by rfl⟩ : syracuseStep 10480103 = 15720155) B15720155
theorem B6986735 : Blo 2069435 6986735 := bstep (se 1 (by rfl) ⟨5240051, by rfl⟩ : syracuseStep 6986735 = 10480103) B10480103
theorem B4657823 : Blo 2069435 4657823 := bstep (se 1 (by rfl) ⟨3493367, by rfl⟩ : syracuseStep 4657823 = 6986735) B6986735
theorem B3105215 : Blo 2069435 3105215 := bstep (se 1 (by rfl) ⟨2328911, by rfl⟩ : syracuseStep 3105215 = 4657823) B4657823
theorem B2070143 : Blo 2069435 2070143 := bstep (se 1 (by rfl) ⟨1552607, by rfl⟩ : syracuseStep 2070143 = 3105215) B3105215
theorem B3105221 : Blo 2069435 3105221 := bbase (se 4 (by rfl) ⟨291114, by rfl⟩ : syracuseStep 3105221 = 582229) (by norm_num)
theorem B2070147 : Blo 2069435 2070147 := bstep (se 1 (by rfl) ⟨1552610, by rfl⟩ : syracuseStep 2070147 = 3105221) B3105221
theorem B3493381 : Blo 2069435 3493381 := bbase (se 4 (by rfl) ⟨327504, by rfl⟩ : syracuseStep 3493381 = 655009) (by norm_num)
theorem B4657841 : Blo 2069435 4657841 := bstep (se 2 (by rfl) ⟨1746690, by rfl⟩ : syracuseStep 4657841 = 3493381) B3493381
theorem B3105227 : Blo 2069435 3105227 := bstep (se 1 (by rfl) ⟨2328920, by rfl⟩ : syracuseStep 3105227 = 4657841) B4657841
theorem B2070151 : Blo 2069435 2070151 := bstep (se 1 (by rfl) ⟨1552613, by rfl⟩ : syracuseStep 2070151 = 3105227) B3105227
theorem B2328925 : Blo 2069435 2328925 := bbase (se 3 (by rfl) ⟨436673, by rfl⟩ : syracuseStep 2328925 = 873347) (by norm_num)
theorem B3105233 : Blo 2069435 3105233 := bstep (se 2 (by rfl) ⟨1164462, by rfl⟩ : syracuseStep 3105233 = 2328925) B2328925
theorem B2070155 : Blo 2069435 2070155 := bstep (se 1 (by rfl) ⟨1552616, by rfl⟩ : syracuseStep 2070155 = 3105233) B3105233
theorem B6986789 : Blo 2069435 6986789 := bbase (se 4 (by rfl) ⟨655011, by rfl⟩ : syracuseStep 6986789 = 1310023) (by norm_num)
theorem B4657859 : Blo 2069435 4657859 := bstep (se 1 (by rfl) ⟨3493394, by rfl⟩ : syracuseStep 4657859 = 6986789) B6986789
theorem B3105239 : Blo 2069435 3105239 := bstep (se 1 (by rfl) ⟨2328929, by rfl⟩ : syracuseStep 3105239 = 4657859) B4657859
theorem B2070159 : Blo 2069435 2070159 := bstep (se 1 (by rfl) ⟨1552619, by rfl⟩ : syracuseStep 2070159 = 3105239) B3105239
theorem B3105245 : Blo 2069435 3105245 := bbase (se 3 (by rfl) ⟨582233, by rfl⟩ : syracuseStep 3105245 = 1164467) (by norm_num)
theorem B2070163 : Blo 2069435 2070163 := bstep (se 1 (by rfl) ⟨1552622, by rfl⟩ : syracuseStep 2070163 = 3105245) B3105245
theorem B4657877 : Blo 2069435 4657877 := bbase (se 7 (by rfl) ⟨54584, by rfl⟩ : syracuseStep 4657877 = 109169) (by norm_num)
theorem B3105251 : Blo 2069435 3105251 := bstep (se 1 (by rfl) ⟨2328938, by rfl⟩ : syracuseStep 3105251 = 4657877) B4657877
theorem B2070167 : Blo 2069435 2070167 := bstep (se 1 (by rfl) ⟨1552625, by rfl⟩ : syracuseStep 2070167 = 3105251) B3105251
theorem B8842709 : Blo 2069435 8842709 := bbase (se 7 (by rfl) ⟨103625, by rfl⟩ : syracuseStep 8842709 = 207251) (by norm_num)
theorem B5895139 : Blo 2069435 5895139 := bstep (se 1 (by rfl) ⟨4421354, by rfl⟩ : syracuseStep 5895139 = 8842709) B8842709
theorem B7860185 : Blo 2069435 7860185 := bstep (se 2 (by rfl) ⟨2947569, by rfl⟩ : syracuseStep 7860185 = 5895139) B5895139
theorem B5240123 : Blo 2069435 5240123 := bstep (se 1 (by rfl) ⟨3930092, by rfl⟩ : syracuseStep 5240123 = 7860185) B7860185
theorem B3493415 : Blo 2069435 3493415 := bstep (se 1 (by rfl) ⟨2620061, by rfl⟩ : syracuseStep 3493415 = 5240123) B5240123
theorem B2328943 : Blo 2069435 2328943 := bstep (se 1 (by rfl) ⟨1746707, by rfl⟩ : syracuseStep 2328943 = 3493415) B3493415
theorem B3105257 : Blo 2069435 3105257 := bstep (se 2 (by rfl) ⟨1164471, by rfl⟩ : syracuseStep 3105257 = 2328943) B2328943
theorem B2070171 : Blo 2069435 2070171 := bstep (se 1 (by rfl) ⟨1552628, by rfl⟩ : syracuseStep 2070171 = 3105257) B3105257
theorem B3541085 : Blo 2069435 3541085 := bbase (se 3 (by rfl) ⟨663953, by rfl⟩ : syracuseStep 3541085 = 1327907) (by norm_num)
theorem B2360723 : Blo 2069435 2360723 := bstep (se 1 (by rfl) ⟨1770542, by rfl⟩ : syracuseStep 2360723 = 3541085) B3541085
theorem B6295261 : Blo 2069435 6295261 := bstep (se 3 (by rfl) ⟨1180361, by rfl⟩ : syracuseStep 6295261 = 2360723) B2360723
theorem B8393681 : Blo 2069435 8393681 := bstep (se 2 (by rfl) ⟨3147630, by rfl⟩ : syracuseStep 8393681 = 6295261) B6295261
theorem B5595787 : Blo 2069435 5595787 := bstep (se 1 (by rfl) ⟨4196840, by rfl⟩ : syracuseStep 5595787 = 8393681) B8393681
theorem B29844197 : Blo 2069435 29844197 := bstep (se 4 (by rfl) ⟨2797893, by rfl⟩ : syracuseStep 29844197 = 5595787) B5595787
theorem B19896131 : Blo 2069435 19896131 := bstep (se 1 (by rfl) ⟨14922098, by rfl⟩ : syracuseStep 19896131 = 29844197) B29844197
theorem B13264087 : Blo 2069435 13264087 := bstep (se 1 (by rfl) ⟨9948065, by rfl⟩ : syracuseStep 13264087 = 19896131) B19896131
theorem B17685449 : Blo 2069435 17685449 := bstep (se 2 (by rfl) ⟨6632043, by rfl⟩ : syracuseStep 17685449 = 13264087) B13264087
theorem B11790299 : Blo 2069435 11790299 := bstep (se 1 (by rfl) ⟨8842724, by rfl⟩ : syracuseStep 11790299 = 17685449) B17685449
theorem B7860199 : Blo 2069435 7860199 := bstep (se 1 (by rfl) ⟨5895149, by rfl⟩ : syracuseStep 7860199 = 11790299) B11790299
theorem B10480265 : Blo 2069435 10480265 := bstep (se 2 (by rfl) ⟨3930099, by rfl⟩ : syracuseStep 10480265 = 7860199) B7860199
theorem B6986843 : Blo 2069435 6986843 := bstep (se 1 (by rfl) ⟨5240132, by rfl⟩ : syracuseStep 6986843 = 10480265) B10480265
theorem B4657895 : Blo 2069435 4657895 := bstep (se 1 (by rfl) ⟨3493421, by rfl⟩ : syracuseStep 4657895 = 6986843) B6986843
theorem B3105263 : Blo 2069435 3105263 := bstep (se 1 (by rfl) ⟨2328947, by rfl⟩ : syracuseStep 3105263 = 4657895) B4657895
theorem B2070175 : Blo 2069435 2070175 := bstep (se 1 (by rfl) ⟨1552631, by rfl⟩ : syracuseStep 2070175 = 3105263) B3105263
theorem B3105269 : Blo 2069435 3105269 := bbase (se 5 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 3105269 = 291119) (by norm_num)
theorem B2070179 : Blo 2069435 2070179 := bstep (se 1 (by rfl) ⟨1552634, by rfl⟩ : syracuseStep 2070179 = 3105269) B3105269
theorem B5895173 : Blo 2069435 5895173 := bbase (se 4 (by rfl) ⟨552672, by rfl⟩ : syracuseStep 5895173 = 1105345) (by norm_num)
theorem B3930115 : Blo 2069435 3930115 := bstep (se 1 (by rfl) ⟨2947586, by rfl⟩ : syracuseStep 3930115 = 5895173) B5895173
theorem B5240153 : Blo 2069435 5240153 := bstep (se 2 (by rfl) ⟨1965057, by rfl⟩ : syracuseStep 5240153 = 3930115) B3930115
theorem B3493435 : Blo 2069435 3493435 := bstep (se 1 (by rfl) ⟨2620076, by rfl⟩ : syracuseStep 3493435 = 5240153) B5240153
theorem B4657913 : Blo 2069435 4657913 := bstep (se 2 (by rfl) ⟨1746717, by rfl⟩ : syracuseStep 4657913 = 3493435) B3493435
theorem B3105275 : Blo 2069435 3105275 := bstep (se 1 (by rfl) ⟨2328956, by rfl⟩ : syracuseStep 3105275 = 4657913) B4657913
theorem B2070183 : Blo 2069435 2070183 := bstep (se 1 (by rfl) ⟨1552637, by rfl⟩ : syracuseStep 2070183 = 3105275) B3105275
theorem B2328961 : Blo 2069435 2328961 := bbase (se 2 (by rfl) ⟨873360, by rfl⟩ : syracuseStep 2328961 = 1746721) (by norm_num)
theorem B3105281 : Blo 2069435 3105281 := bstep (se 2 (by rfl) ⟨1164480, by rfl⟩ : syracuseStep 3105281 = 2328961) B2328961
theorem B2070187 : Blo 2069435 2070187 := bstep (se 1 (by rfl) ⟨1552640, by rfl⟩ : syracuseStep 2070187 = 3105281) B3105281
theorem B5240173 : Blo 2069435 5240173 := bbase (se 3 (by rfl) ⟨982532, by rfl⟩ : syracuseStep 5240173 = 1965065) (by norm_num)
theorem B6986897 : Blo 2069435 6986897 := bstep (se 2 (by rfl) ⟨2620086, by rfl⟩ : syracuseStep 6986897 = 5240173) B5240173
theorem B4657931 : Blo 2069435 4657931 := bstep (se 1 (by rfl) ⟨3493448, by rfl⟩ : syracuseStep 4657931 = 6986897) B6986897
theorem B3105287 : Blo 2069435 3105287 := bstep (se 1 (by rfl) ⟨2328965, by rfl⟩ : syracuseStep 3105287 = 4657931) B4657931
theorem B2070191 : Blo 2069435 2070191 := bstep (se 1 (by rfl) ⟨1552643, by rfl⟩ : syracuseStep 2070191 = 3105287) B3105287
theorem B3105293 : Blo 2069435 3105293 := bbase (se 3 (by rfl) ⟨582242, by rfl⟩ : syracuseStep 3105293 = 1164485) (by norm_num)
theorem B2070195 : Blo 2069435 2070195 := bstep (se 1 (by rfl) ⟨1552646, by rfl⟩ : syracuseStep 2070195 = 3105293) B3105293
theorem B4657949 : Blo 2069435 4657949 := bbase (se 3 (by rfl) ⟨873365, by rfl⟩ : syracuseStep 4657949 = 1746731) (by norm_num)
theorem B3105299 : Blo 2069435 3105299 := bstep (se 1 (by rfl) ⟨2328974, by rfl⟩ : syracuseStep 3105299 = 4657949) B4657949
theorem B2070199 : Blo 2069435 2070199 := bstep (se 1 (by rfl) ⟨1552649, by rfl⟩ : syracuseStep 2070199 = 3105299) B3105299
theorem B3493469 : Blo 2069435 3493469 := bbase (se 3 (by rfl) ⟨655025, by rfl⟩ : syracuseStep 3493469 = 1310051) (by norm_num)
theorem B2328979 : Blo 2069435 2328979 := bstep (se 1 (by rfl) ⟨1746734, by rfl⟩ : syracuseStep 2328979 = 3493469) B3493469
theorem B3105305 : Blo 2069435 3105305 := bstep (se 2 (by rfl) ⟨1164489, by rfl⟩ : syracuseStep 3105305 = 2328979) B2328979
theorem B2070203 : Blo 2069435 2070203 := bstep (se 1 (by rfl) ⟨1552652, by rfl⟩ : syracuseStep 2070203 = 3105305) B3105305
theorem B8393813 : Blo 2069435 8393813 := bbase (se 8 (by rfl) ⟨49182, by rfl⟩ : syracuseStep 8393813 = 98365) (by norm_num)
theorem B5595875 : Blo 2069435 5595875 := bstep (se 1 (by rfl) ⟨4196906, by rfl⟩ : syracuseStep 5595875 = 8393813) B8393813
theorem B3730583 : Blo 2069435 3730583 := bstep (se 1 (by rfl) ⟨2797937, by rfl⟩ : syracuseStep 3730583 = 5595875) B5595875
theorem B2487055 : Blo 2069435 2487055 := bstep (se 1 (by rfl) ⟨1865291, by rfl⟩ : syracuseStep 2487055 = 3730583) B3730583
theorem B3316073 : Blo 2069435 3316073 := bstep (se 2 (by rfl) ⟨1243527, by rfl⟩ : syracuseStep 3316073 = 2487055) B2487055
theorem B8842861 : Blo 2069435 8842861 := bstep (se 3 (by rfl) ⟨1658036, by rfl⟩ : syracuseStep 8842861 = 3316073) B3316073
theorem B11790481 : Blo 2069435 11790481 := bstep (se 2 (by rfl) ⟨4421430, by rfl⟩ : syracuseStep 11790481 = 8842861) B8842861
theorem B15720641 : Blo 2069435 15720641 := bstep (se 2 (by rfl) ⟨5895240, by rfl⟩ : syracuseStep 15720641 = 11790481) B11790481
theorem B10480427 : Blo 2069435 10480427 := bstep (se 1 (by rfl) ⟨7860320, by rfl⟩ : syracuseStep 10480427 = 15720641) B15720641
theorem B6986951 : Blo 2069435 6986951 := bstep (se 1 (by rfl) ⟨5240213, by rfl⟩ : syracuseStep 6986951 = 10480427) B10480427
theorem B4657967 : Blo 2069435 4657967 := bstep (se 1 (by rfl) ⟨3493475, by rfl⟩ : syracuseStep 4657967 = 6986951) B6986951
theorem B3105311 : Blo 2069435 3105311 := bstep (se 1 (by rfl) ⟨2328983, by rfl⟩ : syracuseStep 3105311 = 4657967) B4657967
theorem B2070207 : Blo 2069435 2070207 := bstep (se 1 (by rfl) ⟨1552655, by rfl⟩ : syracuseStep 2070207 = 3105311) B3105311
theorem B3105317 : Blo 2069435 3105317 := bbase (se 4 (by rfl) ⟨291123, by rfl⟩ : syracuseStep 3105317 = 582247) (by norm_num)
theorem B2070211 : Blo 2069435 2070211 := bstep (se 1 (by rfl) ⟨1552658, by rfl⟩ : syracuseStep 2070211 = 3105317) B3105317
theorem B2620117 : Blo 2069435 2620117 := bbase (se 7 (by rfl) ⟨30704, by rfl⟩ : syracuseStep 2620117 = 61409) (by norm_num)
theorem B3493489 : Blo 2069435 3493489 := bstep (se 2 (by rfl) ⟨1310058, by rfl⟩ : syracuseStep 3493489 = 2620117) B2620117
theorem B4657985 : Blo 2069435 4657985 := bstep (se 2 (by rfl) ⟨1746744, by rfl⟩ : syracuseStep 4657985 = 3493489) B3493489
theorem B3105323 : Blo 2069435 3105323 := bstep (se 1 (by rfl) ⟨2328992, by rfl⟩ : syracuseStep 3105323 = 4657985) B4657985
theorem B2070215 : Blo 2069435 2070215 := bstep (se 1 (by rfl) ⟨1552661, by rfl⟩ : syracuseStep 2070215 = 3105323) B3105323
theorem B2328997 : Blo 2069435 2328997 := bbase (se 4 (by rfl) ⟨218343, by rfl⟩ : syracuseStep 2328997 = 436687) (by norm_num)
theorem B3105329 : Blo 2069435 3105329 := bstep (se 2 (by rfl) ⟨1164498, by rfl⟩ : syracuseStep 3105329 = 2328997) B2328997
theorem B2070219 : Blo 2069435 2070219 := bstep (se 1 (by rfl) ⟨1552664, by rfl⟩ : syracuseStep 2070219 = 3105329) B3105329
theorem B4974149 : Blo 2069435 4974149 := bbase (se 4 (by rfl) ⟨466326, by rfl⟩ : syracuseStep 4974149 = 932653) (by norm_num)
theorem B13264397 : Blo 2069435 13264397 := bstep (se 3 (by rfl) ⟨2487074, by rfl⟩ : syracuseStep 13264397 = 4974149) B4974149
theorem B8842931 : Blo 2069435 8842931 := bstep (se 1 (by rfl) ⟨6632198, by rfl⟩ : syracuseStep 8842931 = 13264397) B13264397
theorem B5895287 : Blo 2069435 5895287 := bstep (se 1 (by rfl) ⟨4421465, by rfl⟩ : syracuseStep 5895287 = 8842931) B8842931
theorem B3930191 : Blo 2069435 3930191 := bstep (se 1 (by rfl) ⟨2947643, by rfl⟩ : syracuseStep 3930191 = 5895287) B5895287
theorem B2620127 : Blo 2069435 2620127 := bstep (se 1 (by rfl) ⟨1965095, by rfl⟩ : syracuseStep 2620127 = 3930191) B3930191
theorem B6987005 : Blo 2069435 6987005 := bstep (se 3 (by rfl) ⟨1310063, by rfl⟩ : syracuseStep 6987005 = 2620127) B2620127
theorem B4658003 : Blo 2069435 4658003 := bstep (se 1 (by rfl) ⟨3493502, by rfl⟩ : syracuseStep 4658003 = 6987005) B6987005
theorem B3105335 : Blo 2069435 3105335 := bstep (se 1 (by rfl) ⟨2329001, by rfl⟩ : syracuseStep 3105335 = 4658003) B4658003
theorem B2070223 : Blo 2069435 2070223 := bstep (se 1 (by rfl) ⟨1552667, by rfl⟩ : syracuseStep 2070223 = 3105335) B3105335
theorem B3105341 : Blo 2069435 3105341 := bbase (se 3 (by rfl) ⟨582251, by rfl⟩ : syracuseStep 3105341 = 1164503) (by norm_num)
theorem B2070227 : Blo 2069435 2070227 := bstep (se 1 (by rfl) ⟨1552670, by rfl⟩ : syracuseStep 2070227 = 3105341) B3105341
theorem B4658021 : Blo 2069435 4658021 := bbase (se 4 (by rfl) ⟨436689, by rfl⟩ : syracuseStep 4658021 = 873379) (by norm_num)
theorem B3105347 : Blo 2069435 3105347 := bstep (se 1 (by rfl) ⟨2329010, by rfl⟩ : syracuseStep 3105347 = 4658021) B4658021
theorem B2070231 : Blo 2069435 2070231 := bstep (se 1 (by rfl) ⟨1552673, by rfl⟩ : syracuseStep 2070231 = 3105347) B3105347
theorem B5240285 : Blo 2069435 5240285 := bbase (se 3 (by rfl) ⟨982553, by rfl⟩ : syracuseStep 5240285 = 1965107) (by norm_num)
theorem B3493523 : Blo 2069435 3493523 := bstep (se 1 (by rfl) ⟨2620142, by rfl⟩ : syracuseStep 3493523 = 5240285) B5240285
theorem B2329015 : Blo 2069435 2329015 := bstep (se 1 (by rfl) ⟨1746761, by rfl⟩ : syracuseStep 2329015 = 3493523) B3493523
theorem B3105353 : Blo 2069435 3105353 := bstep (se 2 (by rfl) ⟨1164507, by rfl⟩ : syracuseStep 3105353 = 2329015) B2329015
theorem B2070235 : Blo 2069435 2070235 := bstep (se 1 (by rfl) ⟨1552676, by rfl⟩ : syracuseStep 2070235 = 3105353) B3105353
theorem B3930221 : Blo 2069435 3930221 := bbase (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) (by norm_num)
theorem B10480589 : Blo 2069435 10480589 := bstep (se 3 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 10480589 = 3930221) B3930221
theorem B6987059 : Blo 2069435 6987059 := bstep (se 1 (by rfl) ⟨5240294, by rfl⟩ : syracuseStep 6987059 = 10480589) B10480589
theorem B4658039 : Blo 2069435 4658039 := bstep (se 1 (by rfl) ⟨3493529, by rfl⟩ : syracuseStep 4658039 = 6987059) B6987059
theorem B3105359 : Blo 2069435 3105359 := bstep (se 1 (by rfl) ⟨2329019, by rfl⟩ : syracuseStep 3105359 = 4658039) B4658039
theorem B2070239 : Blo 2069435 2070239 := bstep (se 1 (by rfl) ⟨1552679, by rfl⟩ : syracuseStep 2070239 = 3105359) B3105359
theorem B3105365 : Blo 2069435 3105365 := bbase (se 8 (by rfl) ⟨18195, by rfl⟩ : syracuseStep 3105365 = 36391) (by norm_num)
theorem B2070243 : Blo 2069435 2070243 := bstep (se 1 (by rfl) ⟨1552682, by rfl⟩ : syracuseStep 2070243 = 3105365) B3105365
theorem B5311813 : Blo 2069435 5311813 := bbase (se 4 (by rfl) ⟨497982, by rfl⟩ : syracuseStep 5311813 = 995965) (by norm_num)
theorem B7082417 : Blo 2069435 7082417 := bstep (se 2 (by rfl) ⟨2655906, by rfl⟩ : syracuseStep 7082417 = 5311813) B5311813
theorem B18886445 : Blo 2069435 18886445 := bstep (se 3 (by rfl) ⟨3541208, by rfl⟩ : syracuseStep 18886445 = 7082417) B7082417
theorem B12590963 : Blo 2069435 12590963 := bstep (se 1 (by rfl) ⟨9443222, by rfl⟩ : syracuseStep 12590963 = 18886445) B18886445
theorem B8393975 : Blo 2069435 8393975 := bstep (se 1 (by rfl) ⟨6295481, by rfl⟩ : syracuseStep 8393975 = 12590963) B12590963
theorem B5595983 : Blo 2069435 5595983 := bstep (se 1 (by rfl) ⟨4196987, by rfl⟩ : syracuseStep 5595983 = 8393975) B8393975
theorem B3730655 : Blo 2069435 3730655 := bstep (se 1 (by rfl) ⟨2797991, by rfl⟩ : syracuseStep 3730655 = 5595983) B5595983
theorem B9948413 : Blo 2069435 9948413 := bstep (se 3 (by rfl) ⟨1865327, by rfl⟩ : syracuseStep 9948413 = 3730655) B3730655
theorem B6632275 : Blo 2069435 6632275 := bstep (se 1 (by rfl) ⟨4974206, by rfl⟩ : syracuseStep 6632275 = 9948413) B9948413
theorem B8843033 : Blo 2069435 8843033 := bstep (se 2 (by rfl) ⟨3316137, by rfl⟩ : syracuseStep 8843033 = 6632275) B6632275
theorem B5895355 : Blo 2069435 5895355 := bstep (se 1 (by rfl) ⟨4421516, by rfl⟩ : syracuseStep 5895355 = 8843033) B8843033
theorem B7860473 : Blo 2069435 7860473 := bstep (se 2 (by rfl) ⟨2947677, by rfl⟩ : syracuseStep 7860473 = 5895355) B5895355
theorem B5240315 : Blo 2069435 5240315 := bstep (se 1 (by rfl) ⟨3930236, by rfl⟩ : syracuseStep 5240315 = 7860473) B7860473
theorem B3493543 : Blo 2069435 3493543 := bstep (se 1 (by rfl) ⟨2620157, by rfl⟩ : syracuseStep 3493543 = 5240315) B5240315
theorem B4658057 : Blo 2069435 4658057 := bstep (se 2 (by rfl) ⟨1746771, by rfl⟩ : syracuseStep 4658057 = 3493543) B3493543
theorem B3105371 : Blo 2069435 3105371 := bstep (se 1 (by rfl) ⟨2329028, by rfl⟩ : syracuseStep 3105371 = 4658057) B4658057
theorem B2070247 : Blo 2069435 2070247 := bstep (se 1 (by rfl) ⟨1552685, by rfl⟩ : syracuseStep 2070247 = 3105371) B3105371
theorem B2329033 : Blo 2069435 2329033 := bbase (se 2 (by rfl) ⟨873387, by rfl⟩ : syracuseStep 2329033 = 1746775) (by norm_num)
theorem B3105377 : Blo 2069435 3105377 := bstep (se 2 (by rfl) ⟨1164516, by rfl⟩ : syracuseStep 3105377 = 2329033) B2329033
theorem B2070251 : Blo 2069435 2070251 := bstep (se 1 (by rfl) ⟨1552688, by rfl⟩ : syracuseStep 2070251 = 3105377) B3105377
theorem B17686133 : Blo 2069435 17686133 := bbase (se 5 (by rfl) ⟨829037, by rfl⟩ : syracuseStep 17686133 = 1658075) (by norm_num)
theorem B11790755 : Blo 2069435 11790755 := bstep (se 1 (by rfl) ⟨8843066, by rfl⟩ : syracuseStep 11790755 = 17686133) B17686133
theorem B7860503 : Blo 2069435 7860503 := bstep (se 1 (by rfl) ⟨5895377, by rfl⟩ : syracuseStep 7860503 = 11790755) B11790755
theorem B5240335 : Blo 2069435 5240335 := bstep (se 1 (by rfl) ⟨3930251, by rfl⟩ : syracuseStep 5240335 = 7860503) B7860503
theorem B6987113 : Blo 2069435 6987113 := bstep (se 2 (by rfl) ⟨2620167, by rfl⟩ : syracuseStep 6987113 = 5240335) B5240335
theorem B4658075 : Blo 2069435 4658075 := bstep (se 1 (by rfl) ⟨3493556, by rfl⟩ : syracuseStep 4658075 = 6987113) B6987113
theorem B3105383 : Blo 2069435 3105383 := bstep (se 1 (by rfl) ⟨2329037, by rfl⟩ : syracuseStep 3105383 = 4658075) B4658075
theorem B2070255 : Blo 2069435 2070255 := bstep (se 1 (by rfl) ⟨1552691, by rfl⟩ : syracuseStep 2070255 = 3105383) B3105383
theorem B3105389 : Blo 2069435 3105389 := bbase (se 3 (by rfl) ⟨582260, by rfl⟩ : syracuseStep 3105389 = 1164521) (by norm_num)
theorem B2070259 : Blo 2069435 2070259 := bstep (se 1 (by rfl) ⟨1552694, by rfl⟩ : syracuseStep 2070259 = 3105389) B3105389
theorem B4658093 : Blo 2069435 4658093 := bbase (se 3 (by rfl) ⟨873392, by rfl⟩ : syracuseStep 4658093 = 1746785) (by norm_num)
theorem B3105395 : Blo 2069435 3105395 := bstep (se 1 (by rfl) ⟨2329046, by rfl⟩ : syracuseStep 3105395 = 4658093) B4658093
theorem B2070263 : Blo 2069435 2070263 := bstep (se 1 (by rfl) ⟨1552697, by rfl⟩ : syracuseStep 2070263 = 3105395) B3105395
theorem B5895413 : Blo 2069435 5895413 := bbase (se 5 (by rfl) ⟨276347, by rfl⟩ : syracuseStep 5895413 = 552695) (by norm_num)
theorem B3930275 : Blo 2069435 3930275 := bstep (se 1 (by rfl) ⟨2947706, by rfl⟩ : syracuseStep 3930275 = 5895413) B5895413
theorem B2620183 : Blo 2069435 2620183 := bstep (se 1 (by rfl) ⟨1965137, by rfl⟩ : syracuseStep 2620183 = 3930275) B3930275
theorem B3493577 : Blo 2069435 3493577 := bstep (se 2 (by rfl) ⟨1310091, by rfl⟩ : syracuseStep 3493577 = 2620183) B2620183
theorem B2329051 : Blo 2069435 2329051 := bstep (se 1 (by rfl) ⟨1746788, by rfl⟩ : syracuseStep 2329051 = 3493577) B3493577
theorem B3105401 : Blo 2069435 3105401 := bstep (se 2 (by rfl) ⟨1164525, by rfl⟩ : syracuseStep 3105401 = 2329051) B2329051
theorem B2070267 : Blo 2069435 2070267 := bstep (se 1 (by rfl) ⟨1552700, by rfl⟩ : syracuseStep 2070267 = 3105401) B3105401
theorem B33576277 : Blo 2069435 33576277 := bbase (se 16 (by rfl) ⟨768, by rfl⟩ : syracuseStep 33576277 = 1537) (by norm_num)
theorem B44768369 : Blo 2069435 44768369 := bstep (se 2 (by rfl) ⟨16788138, by rfl⟩ : syracuseStep 44768369 = 33576277) B33576277
theorem B29845579 : Blo 2069435 29845579 := bstep (se 1 (by rfl) ⟨22384184, by rfl⟩ : syracuseStep 29845579 = 44768369) B44768369
theorem B39794105 : Blo 2069435 39794105 := bstep (se 2 (by rfl) ⟨14922789, by rfl⟩ : syracuseStep 39794105 = 29845579) B29845579
theorem B26529403 : Blo 2069435 26529403 := bstep (se 1 (by rfl) ⟨19897052, by rfl⟩ : syracuseStep 26529403 = 39794105) B39794105
theorem B35372537 : Blo 2069435 35372537 := bstep (se 2 (by rfl) ⟨13264701, by rfl⟩ : syracuseStep 35372537 = 26529403) B26529403
theorem B23581691 : Blo 2069435 23581691 := bstep (se 1 (by rfl) ⟨17686268, by rfl⟩ : syracuseStep 23581691 = 35372537) B35372537
theorem B15721127 : Blo 2069435 15721127 := bstep (se 1 (by rfl) ⟨11790845, by rfl⟩ : syracuseStep 15721127 = 23581691) B23581691
theorem B10480751 : Blo 2069435 10480751 := bstep (se 1 (by rfl) ⟨7860563, by rfl⟩ : syracuseStep 10480751 = 15721127) B15721127
theorem B6987167 : Blo 2069435 6987167 := bstep (se 1 (by rfl) ⟨5240375, by rfl⟩ : syracuseStep 6987167 = 10480751) B10480751
theorem B4658111 : Blo 2069435 4658111 := bstep (se 1 (by rfl) ⟨3493583, by rfl⟩ : syracuseStep 4658111 = 6987167) B6987167
theorem B3105407 : Blo 2069435 3105407 := bstep (se 1 (by rfl) ⟨2329055, by rfl⟩ : syracuseStep 3105407 = 4658111) B4658111
theorem B2070271 : Blo 2069435 2070271 := bstep (se 1 (by rfl) ⟨1552703, by rfl⟩ : syracuseStep 2070271 = 3105407) B3105407
theorem B3105413 : Blo 2069435 3105413 := bbase (se 4 (by rfl) ⟨291132, by rfl⟩ : syracuseStep 3105413 = 582265) (by norm_num)
theorem B2070275 : Blo 2069435 2070275 := bstep (se 1 (by rfl) ⟨1552706, by rfl⟩ : syracuseStep 2070275 = 3105413) B3105413
theorem B3493597 : Blo 2069435 3493597 := bbase (se 3 (by rfl) ⟨655049, by rfl⟩ : syracuseStep 3493597 = 1310099) (by norm_num)
theorem B4658129 : Blo 2069435 4658129 := bstep (se 2 (by rfl) ⟨1746798, by rfl⟩ : syracuseStep 4658129 = 3493597) B3493597
theorem B3105419 : Blo 2069435 3105419 := bstep (se 1 (by rfl) ⟨2329064, by rfl⟩ : syracuseStep 3105419 = 4658129) B4658129
theorem B2070279 : Blo 2069435 2070279 := bstep (se 1 (by rfl) ⟨1552709, by rfl⟩ : syracuseStep 2070279 = 3105419) B3105419
theorem B2329069 : Blo 2069435 2329069 := bbase (se 3 (by rfl) ⟨436700, by rfl⟩ : syracuseStep 2329069 = 873401) (by norm_num)
theorem B3105425 : Blo 2069435 3105425 := bstep (se 2 (by rfl) ⟨1164534, by rfl⟩ : syracuseStep 3105425 = 2329069) B2329069
theorem B2070283 : Blo 2069435 2070283 := bstep (se 1 (by rfl) ⟨1552712, by rfl⟩ : syracuseStep 2070283 = 3105425) B3105425
theorem B6987221 : Blo 2069435 6987221 := bbase (se 7 (by rfl) ⟨81881, by rfl⟩ : syracuseStep 6987221 = 163763) (by norm_num)
theorem B4658147 : Blo 2069435 4658147 := bstep (se 1 (by rfl) ⟨3493610, by rfl⟩ : syracuseStep 4658147 = 6987221) B6987221
theorem B3105431 : Blo 2069435 3105431 := bstep (se 1 (by rfl) ⟨2329073, by rfl⟩ : syracuseStep 3105431 = 4658147) B4658147
theorem B2070287 : Blo 2069435 2070287 := bstep (se 1 (by rfl) ⟨1552715, by rfl⟩ : syracuseStep 2070287 = 3105431) B3105431
theorem B3105437 : Blo 2069435 3105437 := bbase (se 3 (by rfl) ⟨582269, by rfl⟩ : syracuseStep 3105437 = 1164539) (by norm_num)
theorem B2070291 : Blo 2069435 2070291 := bstep (se 1 (by rfl) ⟨1552718, by rfl⟩ : syracuseStep 2070291 = 3105437) B3105437
theorem B4658165 : Blo 2069435 4658165 := bbase (se 5 (by rfl) ⟨218351, by rfl⟩ : syracuseStep 4658165 = 436703) (by norm_num)
theorem B3105443 : Blo 2069435 3105443 := bstep (se 1 (by rfl) ⟨2329082, by rfl⟩ : syracuseStep 3105443 = 4658165) B4658165
theorem B2070295 : Blo 2069435 2070295 := bstep (se 1 (by rfl) ⟨1552721, by rfl⟩ : syracuseStep 2070295 = 3105443) B3105443
theorem B8963909 : Blo 2069435 8963909 := bbase (se 4 (by rfl) ⟨840366, by rfl⟩ : syracuseStep 8963909 = 1680733) (by norm_num)
theorem B5975939 : Blo 2069435 5975939 := bstep (se 1 (by rfl) ⟨4481954, by rfl⟩ : syracuseStep 5975939 = 8963909) B8963909
theorem B3983959 : Blo 2069435 3983959 := bstep (se 1 (by rfl) ⟨2987969, by rfl⟩ : syracuseStep 3983959 = 5975939) B5975939
theorem B5311945 : Blo 2069435 5311945 := bstep (se 2 (by rfl) ⟨1991979, by rfl⟩ : syracuseStep 5311945 = 3983959) B3983959
theorem B28330373 : Blo 2069435 28330373 := bstep (se 4 (by rfl) ⟨2655972, by rfl⟩ : syracuseStep 28330373 = 5311945) B5311945
theorem B18886915 : Blo 2069435 18886915 := bstep (se 1 (by rfl) ⟨14165186, by rfl⟩ : syracuseStep 18886915 = 28330373) B28330373
theorem B100730213 : Blo 2069435 100730213 := bstep (se 4 (by rfl) ⟨9443457, by rfl⟩ : syracuseStep 100730213 = 18886915) B18886915
theorem B67153475 : Blo 2069435 67153475 := bstep (se 1 (by rfl) ⟨50365106, by rfl⟩ : syracuseStep 67153475 = 100730213) B100730213
theorem B44768983 : Blo 2069435 44768983 := bstep (se 1 (by rfl) ⟨33576737, by rfl⟩ : syracuseStep 44768983 = 67153475) B67153475
theorem B59691977 : Blo 2069435 59691977 := bstep (se 2 (by rfl) ⟨22384491, by rfl⟩ : syracuseStep 59691977 = 44768983) B44768983
theorem B39794651 : Blo 2069435 39794651 := bstep (se 1 (by rfl) ⟨29845988, by rfl⟩ : syracuseStep 39794651 = 59691977) B59691977
theorem B26529767 : Blo 2069435 26529767 := bstep (se 1 (by rfl) ⟨19897325, by rfl⟩ : syracuseStep 26529767 = 39794651) B39794651
theorem B17686511 : Blo 2069435 17686511 := bstep (se 1 (by rfl) ⟨13264883, by rfl⟩ : syracuseStep 17686511 = 26529767) B26529767
theorem B11791007 : Blo 2069435 11791007 := bstep (se 1 (by rfl) ⟨8843255, by rfl⟩ : syracuseStep 11791007 = 17686511) B17686511
theorem B7860671 : Blo 2069435 7860671 := bstep (se 1 (by rfl) ⟨5895503, by rfl⟩ : syracuseStep 7860671 = 11791007) B11791007
theorem B5240447 : Blo 2069435 5240447 := bstep (se 1 (by rfl) ⟨3930335, by rfl⟩ : syracuseStep 5240447 = 7860671) B7860671
theorem B3493631 : Blo 2069435 3493631 := bstep (se 1 (by rfl) ⟨2620223, by rfl⟩ : syracuseStep 3493631 = 5240447) B5240447
theorem B2329087 : Blo 2069435 2329087 := bstep (se 1 (by rfl) ⟨1746815, by rfl⟩ : syracuseStep 2329087 = 3493631) B3493631
theorem B3105449 : Blo 2069435 3105449 := bstep (se 2 (by rfl) ⟨1164543, by rfl⟩ : syracuseStep 3105449 = 2329087) B2329087
theorem B2070299 : Blo 2069435 2070299 := bstep (se 1 (by rfl) ⟨1552724, by rfl⟩ : syracuseStep 2070299 = 3105449) B3105449
theorem B2947757 : Blo 2069435 2947757 := bbase (se 3 (by rfl) ⟨552704, by rfl⟩ : syracuseStep 2947757 = 1105409) (by norm_num)
theorem B7860685 : Blo 2069435 7860685 := bstep (se 3 (by rfl) ⟨1473878, by rfl⟩ : syracuseStep 7860685 = 2947757) B2947757
theorem B10480913 : Blo 2069435 10480913 := bstep (se 2 (by rfl) ⟨3930342, by rfl⟩ : syracuseStep 10480913 = 7860685) B7860685
theorem B6987275 : Blo 2069435 6987275 := bstep (se 1 (by rfl) ⟨5240456, by rfl⟩ : syracuseStep 6987275 = 10480913) B10480913
theorem B4658183 : Blo 2069435 4658183 := bstep (se 1 (by rfl) ⟨3493637, by rfl⟩ : syracuseStep 4658183 = 6987275) B6987275
theorem B3105455 : Blo 2069435 3105455 := bstep (se 1 (by rfl) ⟨2329091, by rfl⟩ : syracuseStep 3105455 = 4658183) B4658183
theorem B2070303 : Blo 2069435 2070303 := bstep (se 1 (by rfl) ⟨1552727, by rfl⟩ : syracuseStep 2070303 = 3105455) B3105455
theorem B3105461 : Blo 2069435 3105461 := bbase (se 5 (by rfl) ⟨145568, by rfl⟩ : syracuseStep 3105461 = 291137) (by norm_num)
theorem B2070307 : Blo 2069435 2070307 := bstep (se 1 (by rfl) ⟨1552730, by rfl⟩ : syracuseStep 2070307 = 3105461) B3105461
theorem B5240477 : Blo 2069435 5240477 := bbase (se 3 (by rfl) ⟨982589, by rfl⟩ : syracuseStep 5240477 = 1965179) (by norm_num)
theorem B3493651 : Blo 2069435 3493651 := bstep (se 1 (by rfl) ⟨2620238, by rfl⟩ : syracuseStep 3493651 = 5240477) B5240477
theorem B4658201 : Blo 2069435 4658201 := bstep (se 2 (by rfl) ⟨1746825, by rfl⟩ : syracuseStep 4658201 = 3493651) B3493651
theorem B3105467 : Blo 2069435 3105467 := bstep (se 1 (by rfl) ⟨2329100, by rfl⟩ : syracuseStep 3105467 = 4658201) B4658201
theorem B2070311 : Blo 2069435 2070311 := bstep (se 1 (by rfl) ⟨1552733, by rfl⟩ : syracuseStep 2070311 = 3105467) B3105467
theorem B2329105 : Blo 2069435 2329105 := bbase (se 2 (by rfl) ⟨873414, by rfl⟩ : syracuseStep 2329105 = 1746829) (by norm_num)
theorem B3105473 : Blo 2069435 3105473 := bstep (se 2 (by rfl) ⟨1164552, by rfl⟩ : syracuseStep 3105473 = 2329105) B2329105
theorem B2070315 : Blo 2069435 2070315 := bstep (se 1 (by rfl) ⟨1552736, by rfl⟩ : syracuseStep 2070315 = 3105473) B3105473
theorem B3930373 : Blo 2069435 3930373 := bbase (se 4 (by rfl) ⟨368472, by rfl⟩ : syracuseStep 3930373 = 736945) (by norm_num)
theorem B5240497 : Blo 2069435 5240497 := bstep (se 2 (by rfl) ⟨1965186, by rfl⟩ : syracuseStep 5240497 = 3930373) B3930373
theorem B6987329 : Blo 2069435 6987329 := bstep (se 2 (by rfl) ⟨2620248, by rfl⟩ : syracuseStep 6987329 = 5240497) B5240497
theorem B4658219 : Blo 2069435 4658219 := bstep (se 1 (by rfl) ⟨3493664, by rfl⟩ : syracuseStep 4658219 = 6987329) B6987329
theorem B3105479 : Blo 2069435 3105479 := bstep (se 1 (by rfl) ⟨2329109, by rfl⟩ : syracuseStep 3105479 = 4658219) B4658219
theorem B2070319 : Blo 2069435 2070319 := bstep (se 1 (by rfl) ⟨1552739, by rfl⟩ : syracuseStep 2070319 = 3105479) B3105479
theorem B3105485 : Blo 2069435 3105485 := bbase (se 3 (by rfl) ⟨582278, by rfl⟩ : syracuseStep 3105485 = 1164557) (by norm_num)
theorem B2070323 : Blo 2069435 2070323 := bstep (se 1 (by rfl) ⟨1552742, by rfl⟩ : syracuseStep 2070323 = 3105485) B3105485
theorem B4658237 : Blo 2069435 4658237 := bbase (se 3 (by rfl) ⟨873419, by rfl⟩ : syracuseStep 4658237 = 1746839) (by norm_num)
theorem B3105491 : Blo 2069435 3105491 := bstep (se 1 (by rfl) ⟨2329118, by rfl⟩ : syracuseStep 3105491 = 4658237) B4658237
theorem B2070327 : Blo 2069435 2070327 := bstep (se 1 (by rfl) ⟨1552745, by rfl⟩ : syracuseStep 2070327 = 3105491) B3105491
theorem B3493685 : Blo 2069435 3493685 := bbase (se 5 (by rfl) ⟨163766, by rfl⟩ : syracuseStep 3493685 = 327533) (by norm_num)
theorem B2329123 : Blo 2069435 2329123 := bstep (se 1 (by rfl) ⟨1746842, by rfl⟩ : syracuseStep 2329123 = 3493685) B3493685
theorem B3105497 : Blo 2069435 3105497 := bstep (se 2 (by rfl) ⟨1164561, by rfl⟩ : syracuseStep 3105497 = 2329123) B2329123
theorem B2070331 : Blo 2069435 2070331 := bstep (se 1 (by rfl) ⟨1552748, by rfl⟩ : syracuseStep 2070331 = 3105497) B3105497
theorem B5895605 : Blo 2069435 5895605 := bbase (se 5 (by rfl) ⟨276356, by rfl⟩ : syracuseStep 5895605 = 552713) (by norm_num)
theorem B15721613 : Blo 2069435 15721613 := bstep (se 3 (by rfl) ⟨2947802, by rfl⟩ : syracuseStep 15721613 = 5895605) B5895605
theorem B10481075 : Blo 2069435 10481075 := bstep (se 1 (by rfl) ⟨7860806, by rfl⟩ : syracuseStep 10481075 = 15721613) B15721613
theorem B6987383 : Blo 2069435 6987383 := bstep (se 1 (by rfl) ⟨5240537, by rfl⟩ : syracuseStep 6987383 = 10481075) B10481075
theorem B4658255 : Blo 2069435 4658255 := bstep (se 1 (by rfl) ⟨3493691, by rfl⟩ : syracuseStep 4658255 = 6987383) B6987383
theorem B3105503 : Blo 2069435 3105503 := bstep (se 1 (by rfl) ⟨2329127, by rfl⟩ : syracuseStep 3105503 = 4658255) B4658255
theorem B2070335 : Blo 2069435 2070335 := bstep (se 1 (by rfl) ⟨1552751, by rfl⟩ : syracuseStep 2070335 = 3105503) B3105503
theorem B3105509 : Blo 2069435 3105509 := bbase (se 4 (by rfl) ⟨291141, by rfl⟩ : syracuseStep 3105509 = 582283) (by norm_num)
theorem B2070339 : Blo 2069435 2070339 := bstep (se 1 (by rfl) ⟨1552754, by rfl⟩ : syracuseStep 2070339 = 3105509) B3105509
theorem B2210861 : Blo 2069435 2210861 := bbase (se 3 (by rfl) ⟨414536, by rfl⟩ : syracuseStep 2210861 = 829073) (by norm_num)
theorem B5895629 : Blo 2069435 5895629 := bstep (se 3 (by rfl) ⟨1105430, by rfl⟩ : syracuseStep 5895629 = 2210861) B2210861
theorem B3930419 : Blo 2069435 3930419 := bstep (se 1 (by rfl) ⟨2947814, by rfl⟩ : syracuseStep 3930419 = 5895629) B5895629
theorem B2620279 : Blo 2069435 2620279 := bstep (se 1 (by rfl) ⟨1965209, by rfl⟩ : syracuseStep 2620279 = 3930419) B3930419
theorem B3493705 : Blo 2069435 3493705 := bstep (se 2 (by rfl) ⟨1310139, by rfl⟩ : syracuseStep 3493705 = 2620279) B2620279
theorem B4658273 : Blo 2069435 4658273 := bstep (se 2 (by rfl) ⟨1746852, by rfl⟩ : syracuseStep 4658273 = 3493705) B3493705
theorem B3105515 : Blo 2069435 3105515 := bstep (se 1 (by rfl) ⟨2329136, by rfl⟩ : syracuseStep 3105515 = 4658273) B4658273
theorem B2070343 : Blo 2069435 2070343 := bstep (se 1 (by rfl) ⟨1552757, by rfl⟩ : syracuseStep 2070343 = 3105515) B3105515
theorem B2329141 : Blo 2069435 2329141 := bbase (se 5 (by rfl) ⟨109178, by rfl⟩ : syracuseStep 2329141 = 218357) (by norm_num)
theorem B3105521 : Blo 2069435 3105521 := bstep (se 2 (by rfl) ⟨1164570, by rfl⟩ : syracuseStep 3105521 = 2329141) B2329141
theorem B2070347 : Blo 2069435 2070347 := bstep (se 1 (by rfl) ⟨1552760, by rfl⟩ : syracuseStep 2070347 = 3105521) B3105521
theorem B2620289 : Blo 2069435 2620289 := bbase (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) (by norm_num)
theorem B6987437 : Blo 2069435 6987437 := bstep (se 3 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 6987437 = 2620289) B2620289
theorem B4658291 : Blo 2069435 4658291 := bstep (se 1 (by rfl) ⟨3493718, by rfl⟩ : syracuseStep 4658291 = 6987437) B6987437
theorem B3105527 : Blo 2069435 3105527 := bstep (se 1 (by rfl) ⟨2329145, by rfl⟩ : syracuseStep 3105527 = 4658291) B4658291
theorem B2070351 : Blo 2069435 2070351 := bstep (se 1 (by rfl) ⟨1552763, by rfl⟩ : syracuseStep 2070351 = 3105527) B3105527
theorem B3105533 : Blo 2069435 3105533 := bbase (se 3 (by rfl) ⟨582287, by rfl⟩ : syracuseStep 3105533 = 1164575) (by norm_num)
theorem B2070355 : Blo 2069435 2070355 := bstep (se 1 (by rfl) ⟨1552766, by rfl⟩ : syracuseStep 2070355 = 3105533) B3105533
theorem B4658309 : Blo 2069435 4658309 := bbase (se 4 (by rfl) ⟨436716, by rfl⟩ : syracuseStep 4658309 = 873433) (by norm_num)
theorem B3105539 : Blo 2069435 3105539 := bstep (se 1 (by rfl) ⟨2329154, by rfl⟩ : syracuseStep 3105539 = 4658309) B4658309
theorem B2070359 : Blo 2069435 2070359 := bstep (se 1 (by rfl) ⟨1552769, by rfl⟩ : syracuseStep 2070359 = 3105539) B3105539
theorem B4421765 : Blo 2069435 4421765 := bbase (se 4 (by rfl) ⟨414540, by rfl⟩ : syracuseStep 4421765 = 829081) (by norm_num)
theorem B2947843 : Blo 2069435 2947843 := bstep (se 1 (by rfl) ⟨2210882, by rfl⟩ : syracuseStep 2947843 = 4421765) B4421765
theorem B3930457 : Blo 2069435 3930457 := bstep (se 2 (by rfl) ⟨1473921, by rfl⟩ : syracuseStep 3930457 = 2947843) B2947843
theorem B5240609 : Blo 2069435 5240609 := bstep (se 2 (by rfl) ⟨1965228, by rfl⟩ : syracuseStep 5240609 = 3930457) B3930457
theorem B3493739 : Blo 2069435 3493739 := bstep (se 1 (by rfl) ⟨2620304, by rfl⟩ : syracuseStep 3493739 = 5240609) B5240609
theorem B2329159 : Blo 2069435 2329159 := bstep (se 1 (by rfl) ⟨1746869, by rfl⟩ : syracuseStep 2329159 = 3493739) B3493739
theorem B3105545 : Blo 2069435 3105545 := bstep (se 2 (by rfl) ⟨1164579, by rfl⟩ : syracuseStep 3105545 = 2329159) B2329159
theorem B2070363 : Blo 2069435 2070363 := bstep (se 1 (by rfl) ⟨1552772, by rfl⟩ : syracuseStep 2070363 = 3105545) B3105545
theorem B10481237 : Blo 2069435 10481237 := bbase (se 8 (by rfl) ⟨61413, by rfl⟩ : syracuseStep 10481237 = 122827) (by norm_num)
theorem B6987491 : Blo 2069435 6987491 := bstep (se 1 (by rfl) ⟨5240618, by rfl⟩ : syracuseStep 6987491 = 10481237) B10481237
theorem B4658327 : Blo 2069435 4658327 := bstep (se 1 (by rfl) ⟨3493745, by rfl⟩ : syracuseStep 4658327 = 6987491) B6987491
theorem B3105551 : Blo 2069435 3105551 := bstep (se 1 (by rfl) ⟨2329163, by rfl⟩ : syracuseStep 3105551 = 4658327) B4658327
theorem B2070367 : Blo 2069435 2070367 := bstep (se 1 (by rfl) ⟨1552775, by rfl⟩ : syracuseStep 2070367 = 3105551) B3105551
theorem B3105557 : Blo 2069435 3105557 := bbase (se 6 (by rfl) ⟨72786, by rfl⟩ : syracuseStep 3105557 = 145573) (by norm_num)
theorem B2070371 : Blo 2069435 2070371 := bstep (se 1 (by rfl) ⟨1552778, by rfl⟩ : syracuseStep 2070371 = 3105557) B3105557
theorem B14923541 : Blo 2069435 14923541 := bbase (se 6 (by rfl) ⟨349770, by rfl⟩ : syracuseStep 14923541 = 699541) (by norm_num)
theorem B39796109 : Blo 2069435 39796109 := bstep (se 3 (by rfl) ⟨7461770, by rfl⟩ : syracuseStep 39796109 = 14923541) B14923541
theorem B26530739 : Blo 2069435 26530739 := bstep (se 1 (by rfl) ⟨19898054, by rfl⟩ : syracuseStep 26530739 = 39796109) B39796109
theorem B17687159 : Blo 2069435 17687159 := bstep (se 1 (by rfl) ⟨13265369, by rfl⟩ : syracuseStep 17687159 = 26530739) B26530739
theorem B11791439 : Blo 2069435 11791439 := bstep (se 1 (by rfl) ⟨8843579, by rfl⟩ : syracuseStep 11791439 = 17687159) B17687159
theorem B7860959 : Blo 2069435 7860959 := bstep (se 1 (by rfl) ⟨5895719, by rfl⟩ : syracuseStep 7860959 = 11791439) B11791439
theorem B5240639 : Blo 2069435 5240639 := bstep (se 1 (by rfl) ⟨3930479, by rfl⟩ : syracuseStep 5240639 = 7860959) B7860959
theorem B3493759 : Blo 2069435 3493759 := bstep (se 1 (by rfl) ⟨2620319, by rfl⟩ : syracuseStep 3493759 = 5240639) B5240639
theorem B4658345 : Blo 2069435 4658345 := bstep (se 2 (by rfl) ⟨1746879, by rfl⟩ : syracuseStep 4658345 = 3493759) B3493759
theorem B3105563 : Blo 2069435 3105563 := bstep (se 1 (by rfl) ⟨2329172, by rfl⟩ : syracuseStep 3105563 = 4658345) B4658345
theorem B2070375 : Blo 2069435 2070375 := bstep (se 1 (by rfl) ⟨1552781, by rfl⟩ : syracuseStep 2070375 = 3105563) B3105563
theorem B2329177 : Blo 2069435 2329177 := bbase (se 2 (by rfl) ⟨873441, by rfl⟩ : syracuseStep 2329177 = 1746883) (by norm_num)
theorem B3105569 : Blo 2069435 3105569 := bstep (se 2 (by rfl) ⟨1164588, by rfl⟩ : syracuseStep 3105569 = 2329177) B2329177
theorem B2070379 : Blo 2069435 2070379 := bstep (se 1 (by rfl) ⟨1552784, by rfl⟩ : syracuseStep 2070379 = 3105569) B3105569
theorem B2656081 : Blo 2069435 2656081 := bbase (se 2 (by rfl) ⟨996030, by rfl⟩ : syracuseStep 2656081 = 1992061) (by norm_num)
theorem B14165765 : Blo 2069435 14165765 := bstep (se 4 (by rfl) ⟨1328040, by rfl⟩ : syracuseStep 14165765 = 2656081) B2656081
theorem B9443843 : Blo 2069435 9443843 := bstep (se 1 (by rfl) ⟨7082882, by rfl⟩ : syracuseStep 9443843 = 14165765) B14165765
theorem B6295895 : Blo 2069435 6295895 := bstep (se 1 (by rfl) ⟨4721921, by rfl⟩ : syracuseStep 6295895 = 9443843) B9443843
theorem B4197263 : Blo 2069435 4197263 := bstep (se 1 (by rfl) ⟨3147947, by rfl⟩ : syracuseStep 4197263 = 6295895) B6295895
theorem B11192701 : Blo 2069435 11192701 := bstep (se 3 (by rfl) ⟨2098631, by rfl⟩ : syracuseStep 11192701 = 4197263) B4197263
theorem B14923601 : Blo 2069435 14923601 := bstep (se 2 (by rfl) ⟨5596350, by rfl⟩ : syracuseStep 14923601 = 11192701) B11192701
theorem B9949067 : Blo 2069435 9949067 := bstep (se 1 (by rfl) ⟨7461800, by rfl⟩ : syracuseStep 9949067 = 14923601) B14923601
theorem B6632711 : Blo 2069435 6632711 := bstep (se 1 (by rfl) ⟨4974533, by rfl⟩ : syracuseStep 6632711 = 9949067) B9949067
theorem B4421807 : Blo 2069435 4421807 := bstep (se 1 (by rfl) ⟨3316355, by rfl⟩ : syracuseStep 4421807 = 6632711) B6632711
theorem B2947871 : Blo 2069435 2947871 := bstep (se 1 (by rfl) ⟨2210903, by rfl⟩ : syracuseStep 2947871 = 4421807) B4421807
theorem B7860989 : Blo 2069435 7860989 := bstep (se 3 (by rfl) ⟨1473935, by rfl⟩ : syracuseStep 7860989 = 2947871) B2947871
theorem B5240659 : Blo 2069435 5240659 := bstep (se 1 (by rfl) ⟨3930494, by rfl⟩ : syracuseStep 5240659 = 7860989) B7860989
theorem B6987545 : Blo 2069435 6987545 := bstep (se 2 (by rfl) ⟨2620329, by rfl⟩ : syracuseStep 6987545 = 5240659) B5240659
theorem B4658363 : Blo 2069435 4658363 := bstep (se 1 (by rfl) ⟨3493772, by rfl⟩ : syracuseStep 4658363 = 6987545) B6987545
theorem B3105575 : Blo 2069435 3105575 := bstep (se 1 (by rfl) ⟨2329181, by rfl⟩ : syracuseStep 3105575 = 4658363) B4658363
theorem B2070383 : Blo 2069435 2070383 := bstep (se 1 (by rfl) ⟨1552787, by rfl⟩ : syracuseStep 2070383 = 3105575) B3105575
theorem B3105581 : Blo 2069435 3105581 := bbase (se 3 (by rfl) ⟨582296, by rfl⟩ : syracuseStep 3105581 = 1164593) (by norm_num)
theorem B2070387 : Blo 2069435 2070387 := bstep (se 1 (by rfl) ⟨1552790, by rfl⟩ : syracuseStep 2070387 = 3105581) B3105581
theorem B4658381 : Blo 2069435 4658381 := bbase (se 3 (by rfl) ⟨873446, by rfl⟩ : syracuseStep 4658381 = 1746893) (by norm_num)
theorem B3105587 : Blo 2069435 3105587 := bstep (se 1 (by rfl) ⟨2329190, by rfl⟩ : syracuseStep 3105587 = 4658381) B4658381
theorem B2070391 : Blo 2069435 2070391 := bstep (se 1 (by rfl) ⟨1552793, by rfl⟩ : syracuseStep 2070391 = 3105587) B3105587
theorem B2620345 : Blo 2069435 2620345 := bbase (se 2 (by rfl) ⟨982629, by rfl⟩ : syracuseStep 2620345 = 1965259) (by norm_num)
theorem B3493793 : Blo 2069435 3493793 := bstep (se 2 (by rfl) ⟨1310172, by rfl⟩ : syracuseStep 3493793 = 2620345) B2620345
theorem B2329195 : Blo 2069435 2329195 := bstep (se 1 (by rfl) ⟨1746896, by rfl⟩ : syracuseStep 2329195 = 3493793) B3493793
theorem B3105593 : Blo 2069435 3105593 := bstep (se 2 (by rfl) ⟨1164597, by rfl⟩ : syracuseStep 3105593 = 2329195) B2329195
theorem B2070395 : Blo 2069435 2070395 := bstep (se 1 (by rfl) ⟨1552796, by rfl⟩ : syracuseStep 2070395 = 3105593) B3105593
theorem B10624405 : Blo 2069435 10624405 := bbase (se 6 (by rfl) ⟨249009, by rfl⟩ : syracuseStep 10624405 = 498019) (by norm_num)
theorem B14165873 : Blo 2069435 14165873 := bstep (se 2 (by rfl) ⟨5312202, by rfl⟩ : syracuseStep 14165873 = 10624405) B10624405
theorem B9443915 : Blo 2069435 9443915 := bstep (se 1 (by rfl) ⟨7082936, by rfl⟩ : syracuseStep 9443915 = 14165873) B14165873
theorem B6295943 : Blo 2069435 6295943 := bstep (se 1 (by rfl) ⟨4721957, by rfl⟩ : syracuseStep 6295943 = 9443915) B9443915
theorem B4197295 : Blo 2069435 4197295 := bstep (se 1 (by rfl) ⟨3147971, by rfl⟩ : syracuseStep 4197295 = 6295943) B6295943
theorem B5596393 : Blo 2069435 5596393 := bstep (se 2 (by rfl) ⟨2098647, by rfl⟩ : syracuseStep 5596393 = 4197295) B4197295
theorem B7461857 : Blo 2069435 7461857 := bstep (se 2 (by rfl) ⟨2798196, by rfl⟩ : syracuseStep 7461857 = 5596393) B5596393
theorem B4974571 : Blo 2069435 4974571 := bstep (se 1 (by rfl) ⟨3730928, by rfl⟩ : syracuseStep 4974571 = 7461857) B7461857
theorem B6632761 : Blo 2069435 6632761 := bstep (se 2 (by rfl) ⟨2487285, by rfl⟩ : syracuseStep 6632761 = 4974571) B4974571
theorem B8843681 : Blo 2069435 8843681 := bstep (se 2 (by rfl) ⟨3316380, by rfl⟩ : syracuseStep 8843681 = 6632761) B6632761
theorem B23583149 : Blo 2069435 23583149 := bstep (se 3 (by rfl) ⟨4421840, by rfl⟩ : syracuseStep 23583149 = 8843681) B8843681
theorem B15722099 : Blo 2069435 15722099 := bstep (se 1 (by rfl) ⟨11791574, by rfl⟩ : syracuseStep 15722099 = 23583149) B23583149
theorem B10481399 : Blo 2069435 10481399 := bstep (se 1 (by rfl) ⟨7861049, by rfl⟩ : syracuseStep 10481399 = 15722099) B15722099
theorem B6987599 : Blo 2069435 6987599 := bstep (se 1 (by rfl) ⟨5240699, by rfl⟩ : syracuseStep 6987599 = 10481399) B10481399
theorem B4658399 : Blo 2069435 4658399 := bstep (se 1 (by rfl) ⟨3493799, by rfl⟩ : syracuseStep 4658399 = 6987599) B6987599
theorem B3105599 : Blo 2069435 3105599 := bstep (se 1 (by rfl) ⟨2329199, by rfl⟩ : syracuseStep 3105599 = 4658399) B4658399
theorem B2070399 : Blo 2069435 2070399 := bstep (se 1 (by rfl) ⟨1552799, by rfl⟩ : syracuseStep 2070399 = 3105599) B3105599
theorem B3105605 : Blo 2069435 3105605 := bbase (se 4 (by rfl) ⟨291150, by rfl⟩ : syracuseStep 3105605 = 582301) (by norm_num)
theorem B2070403 : Blo 2069435 2070403 := bstep (se 1 (by rfl) ⟨1552802, by rfl⟩ : syracuseStep 2070403 = 3105605) B3105605
theorem B3493813 : Blo 2069435 3493813 := bbase (se 5 (by rfl) ⟨163772, by rfl⟩ : syracuseStep 3493813 = 327545) (by norm_num)
theorem B4658417 : Blo 2069435 4658417 := bstep (se 2 (by rfl) ⟨1746906, by rfl⟩ : syracuseStep 4658417 = 3493813) B3493813
theorem B3105611 : Blo 2069435 3105611 := bstep (se 1 (by rfl) ⟨2329208, by rfl⟩ : syracuseStep 3105611 = 4658417) B4658417
theorem B2070407 : Blo 2069435 2070407 := bstep (se 1 (by rfl) ⟨1552805, by rfl⟩ : syracuseStep 2070407 = 3105611) B3105611
theorem B2329213 : Blo 2069435 2329213 := bbase (se 3 (by rfl) ⟨436727, by rfl⟩ : syracuseStep 2329213 = 873455) (by norm_num)
theorem B3105617 : Blo 2069435 3105617 := bstep (se 2 (by rfl) ⟨1164606, by rfl⟩ : syracuseStep 3105617 = 2329213) B2329213
theorem B2070411 : Blo 2069435 2070411 := bstep (se 1 (by rfl) ⟨1552808, by rfl⟩ : syracuseStep 2070411 = 3105617) B3105617
theorem B6987653 : Blo 2069435 6987653 := bbase (se 4 (by rfl) ⟨655092, by rfl⟩ : syracuseStep 6987653 = 1310185) (by norm_num)
theorem B4658435 : Blo 2069435 4658435 := bstep (se 1 (by rfl) ⟨3493826, by rfl⟩ : syracuseStep 4658435 = 6987653) B6987653
theorem B3105623 : Blo 2069435 3105623 := bstep (se 1 (by rfl) ⟨2329217, by rfl⟩ : syracuseStep 3105623 = 4658435) B4658435
theorem B2070415 : Blo 2069435 2070415 := bstep (se 1 (by rfl) ⟨1552811, by rfl⟩ : syracuseStep 2070415 = 3105623) B3105623
theorem B3105629 : Blo 2069435 3105629 := bbase (se 3 (by rfl) ⟨582305, by rfl⟩ : syracuseStep 3105629 = 1164611) (by norm_num)
theorem B2070419 : Blo 2069435 2070419 := bstep (se 1 (by rfl) ⟨1552814, by rfl⟩ : syracuseStep 2070419 = 3105629) B3105629
theorem B4658453 : Blo 2069435 4658453 := bbase (se 6 (by rfl) ⟨109182, by rfl⟩ : syracuseStep 4658453 = 218365) (by norm_num)
theorem B3105635 : Blo 2069435 3105635 := bstep (se 1 (by rfl) ⟨2329226, by rfl⟩ : syracuseStep 3105635 = 4658453) B4658453
theorem B2070423 : Blo 2069435 2070423 := bstep (se 1 (by rfl) ⟨1552817, by rfl⟩ : syracuseStep 2070423 = 3105635) B3105635
theorem B7861157 : Blo 2069435 7861157 := bbase (se 4 (by rfl) ⟨736983, by rfl⟩ : syracuseStep 7861157 = 1473967) (by norm_num)
theorem B5240771 : Blo 2069435 5240771 := bstep (se 1 (by rfl) ⟨3930578, by rfl⟩ : syracuseStep 5240771 = 7861157) B7861157
theorem B3493847 : Blo 2069435 3493847 := bstep (se 1 (by rfl) ⟨2620385, by rfl⟩ : syracuseStep 3493847 = 5240771) B5240771
theorem B2329231 : Blo 2069435 2329231 := bstep (se 1 (by rfl) ⟨1746923, by rfl⟩ : syracuseStep 2329231 = 3493847) B3493847
theorem B3105641 : Blo 2069435 3105641 := bstep (se 2 (by rfl) ⟨1164615, by rfl⟩ : syracuseStep 3105641 = 2329231) B2329231
theorem B2070427 : Blo 2069435 2070427 := bstep (se 1 (by rfl) ⟨1552820, by rfl⟩ : syracuseStep 2070427 = 3105641) B3105641
theorem B4421909 : Blo 2069435 4421909 := bbase (se 6 (by rfl) ⟨103638, by rfl⟩ : syracuseStep 4421909 = 207277) (by norm_num)
theorem B11791757 : Blo 2069435 11791757 := bstep (se 3 (by rfl) ⟨2210954, by rfl⟩ : syracuseStep 11791757 = 4421909) B4421909
theorem B7861171 : Blo 2069435 7861171 := bstep (se 1 (by rfl) ⟨5895878, by rfl⟩ : syracuseStep 7861171 = 11791757) B11791757
theorem B10481561 : Blo 2069435 10481561 := bstep (se 2 (by rfl) ⟨3930585, by rfl⟩ : syracuseStep 10481561 = 7861171) B7861171
theorem B6987707 : Blo 2069435 6987707 := bstep (se 1 (by rfl) ⟨5240780, by rfl⟩ : syracuseStep 6987707 = 10481561) B10481561
theorem B4658471 : Blo 2069435 4658471 := bstep (se 1 (by rfl) ⟨3493853, by rfl⟩ : syracuseStep 4658471 = 6987707) B6987707
theorem B3105647 : Blo 2069435 3105647 := bstep (se 1 (by rfl) ⟨2329235, by rfl⟩ : syracuseStep 3105647 = 4658471) B4658471
theorem B2070431 : Blo 2069435 2070431 := bstep (se 1 (by rfl) ⟨1552823, by rfl⟩ : syracuseStep 2070431 = 3105647) B3105647
theorem B3105653 : Blo 2069435 3105653 := bbase (se 5 (by rfl) ⟨145577, by rfl⟩ : syracuseStep 3105653 = 291155) (by norm_num)
theorem B2070435 : Blo 2069435 2070435 := bstep (se 1 (by rfl) ⟨1552826, by rfl⟩ : syracuseStep 2070435 = 3105653) B3105653
theorem B2361025 : Blo 2069435 2361025 := bbase (se 2 (by rfl) ⟨885384, by rfl⟩ : syracuseStep 2361025 = 1770769) (by norm_num)
theorem B3148033 : Blo 2069435 3148033 := bstep (se 2 (by rfl) ⟨1180512, by rfl⟩ : syracuseStep 3148033 = 2361025) B2361025
theorem B4197377 : Blo 2069435 4197377 := bstep (se 2 (by rfl) ⟨1574016, by rfl⟩ : syracuseStep 4197377 = 3148033) B3148033
theorem B11193005 : Blo 2069435 11193005 := bstep (se 3 (by rfl) ⟨2098688, by rfl⟩ : syracuseStep 11193005 = 4197377) B4197377
theorem B7462003 : Blo 2069435 7462003 := bstep (se 1 (by rfl) ⟨5596502, by rfl⟩ : syracuseStep 7462003 = 11193005) B11193005
theorem B9949337 : Blo 2069435 9949337 := bstep (se 2 (by rfl) ⟨3731001, by rfl⟩ : syracuseStep 9949337 = 7462003) B7462003
theorem B6632891 : Blo 2069435 6632891 := bstep (se 1 (by rfl) ⟨4974668, by rfl⟩ : syracuseStep 6632891 = 9949337) B9949337
theorem B4421927 : Blo 2069435 4421927 := bstep (se 1 (by rfl) ⟨3316445, by rfl⟩ : syracuseStep 4421927 = 6632891) B6632891
theorem B2947951 : Blo 2069435 2947951 := bstep (se 1 (by rfl) ⟨2210963, by rfl⟩ : syracuseStep 2947951 = 4421927) B4421927
theorem B3930601 : Blo 2069435 3930601 := bstep (se 2 (by rfl) ⟨1473975, by rfl⟩ : syracuseStep 3930601 = 2947951) B2947951
theorem B5240801 : Blo 2069435 5240801 := bstep (se 2 (by rfl) ⟨1965300, by rfl⟩ : syracuseStep 5240801 = 3930601) B3930601
theorem B3493867 : Blo 2069435 3493867 := bstep (se 1 (by rfl) ⟨2620400, by rfl⟩ : syracuseStep 3493867 = 5240801) B5240801
theorem B4658489 : Blo 2069435 4658489 := bstep (se 2 (by rfl) ⟨1746933, by rfl⟩ : syracuseStep 4658489 = 3493867) B3493867
theorem B3105659 : Blo 2069435 3105659 := bstep (se 1 (by rfl) ⟨2329244, by rfl⟩ : syracuseStep 3105659 = 4658489) B4658489
theorem B2070439 : Blo 2069435 2070439 := bstep (se 1 (by rfl) ⟨1552829, by rfl⟩ : syracuseStep 2070439 = 3105659) B3105659
theorem B2329249 : Blo 2069435 2329249 := bbase (se 2 (by rfl) ⟨873468, by rfl⟩ : syracuseStep 2329249 = 1746937) (by norm_num)
theorem B3105665 : Blo 2069435 3105665 := bstep (se 2 (by rfl) ⟨1164624, by rfl⟩ : syracuseStep 3105665 = 2329249) B2329249
theorem B2070443 : Blo 2069435 2070443 := bstep (se 1 (by rfl) ⟨1552832, by rfl⟩ : syracuseStep 2070443 = 3105665) B3105665
theorem B5240821 : Blo 2069435 5240821 := bbase (se 5 (by rfl) ⟨245663, by rfl⟩ : syracuseStep 5240821 = 491327) (by norm_num)
theorem B6987761 : Blo 2069435 6987761 := bstep (se 2 (by rfl) ⟨2620410, by rfl⟩ : syracuseStep 6987761 = 5240821) B5240821
theorem B4658507 : Blo 2069435 4658507 := bstep (se 1 (by rfl) ⟨3493880, by rfl⟩ : syracuseStep 4658507 = 6987761) B6987761
theorem B3105671 : Blo 2069435 3105671 := bstep (se 1 (by rfl) ⟨2329253, by rfl⟩ : syracuseStep 3105671 = 4658507) B4658507
theorem B2070447 : Blo 2069435 2070447 := bstep (se 1 (by rfl) ⟨1552835, by rfl⟩ : syracuseStep 2070447 = 3105671) B3105671
theorem B3105677 : Blo 2069435 3105677 := bbase (se 3 (by rfl) ⟨582314, by rfl⟩ : syracuseStep 3105677 = 1164629) (by norm_num)
theorem B2070451 : Blo 2069435 2070451 := bstep (se 1 (by rfl) ⟨1552838, by rfl⟩ : syracuseStep 2070451 = 3105677) B3105677
theorem B4658525 : Blo 2069435 4658525 := bbase (se 3 (by rfl) ⟨873473, by rfl⟩ : syracuseStep 4658525 = 1746947) (by norm_num)
theorem B3105683 : Blo 2069435 3105683 := bstep (se 1 (by rfl) ⟨2329262, by rfl⟩ : syracuseStep 3105683 = 4658525) B4658525
theorem B2070455 : Blo 2069435 2070455 := bstep (se 1 (by rfl) ⟨1552841, by rfl⟩ : syracuseStep 2070455 = 3105683) B3105683
theorem B3493901 : Blo 2069435 3493901 := bbase (se 3 (by rfl) ⟨655106, by rfl⟩ : syracuseStep 3493901 = 1310213) (by norm_num)
theorem B2329267 : Blo 2069435 2329267 := bstep (se 1 (by rfl) ⟨1746950, by rfl⟩ : syracuseStep 2329267 = 3493901) B3493901
theorem B3105689 : Blo 2069435 3105689 := bstep (se 2 (by rfl) ⟨1164633, by rfl⟩ : syracuseStep 3105689 = 2329267) B2329267
theorem B2070459 : Blo 2069435 2070459 := bstep (se 1 (by rfl) ⟨1552844, by rfl⟩ : syracuseStep 2070459 = 3105689) B3105689
theorem B4974725 : Blo 2069435 4974725 := bbase (se 4 (by rfl) ⟨466380, by rfl⟩ : syracuseStep 4974725 = 932761) (by norm_num)
theorem B3316483 : Blo 2069435 3316483 := bstep (se 1 (by rfl) ⟨2487362, by rfl⟩ : syracuseStep 3316483 = 4974725) B4974725
theorem B17687909 : Blo 2069435 17687909 := bstep (se 4 (by rfl) ⟨1658241, by rfl⟩ : syracuseStep 17687909 = 3316483) B3316483
theorem B11791939 : Blo 2069435 11791939 := bstep (se 1 (by rfl) ⟨8843954, by rfl⟩ : syracuseStep 11791939 = 17687909) B17687909
theorem B15722585 : Blo 2069435 15722585 := bstep (se 2 (by rfl) ⟨5895969, by rfl⟩ : syracuseStep 15722585 = 11791939) B11791939
theorem B10481723 : Blo 2069435 10481723 := bstep (se 1 (by rfl) ⟨7861292, by rfl⟩ : syracuseStep 10481723 = 15722585) B15722585
theorem B6987815 : Blo 2069435 6987815 := bstep (se 1 (by rfl) ⟨5240861, by rfl⟩ : syracuseStep 6987815 = 10481723) B10481723
theorem B4658543 : Blo 2069435 4658543 := bstep (se 1 (by rfl) ⟨3493907, by rfl⟩ : syracuseStep 4658543 = 6987815) B6987815
theorem B3105695 : Blo 2069435 3105695 := bstep (se 1 (by rfl) ⟨2329271, by rfl⟩ : syracuseStep 3105695 = 4658543) B4658543
theorem B2070463 : Blo 2069435 2070463 := bstep (se 1 (by rfl) ⟨1552847, by rfl⟩ : syracuseStep 2070463 = 3105695) B3105695
theorem B3105701 : Blo 2069435 3105701 := bbase (se 4 (by rfl) ⟨291159, by rfl⟩ : syracuseStep 3105701 = 582319) (by norm_num)
theorem B2070467 : Blo 2069435 2070467 := bstep (se 1 (by rfl) ⟨1552850, by rfl⟩ : syracuseStep 2070467 = 3105701) B3105701
theorem B2620441 : Blo 2069435 2620441 := bbase (se 2 (by rfl) ⟨982665, by rfl⟩ : syracuseStep 2620441 = 1965331) (by norm_num)
theorem B3493921 : Blo 2069435 3493921 := bstep (se 2 (by rfl) ⟨1310220, by rfl⟩ : syracuseStep 3493921 = 2620441) B2620441
theorem B4658561 : Blo 2069435 4658561 := bstep (se 2 (by rfl) ⟨1746960, by rfl⟩ : syracuseStep 4658561 = 3493921) B3493921
theorem B3105707 : Blo 2069435 3105707 := bstep (se 1 (by rfl) ⟨2329280, by rfl⟩ : syracuseStep 3105707 = 4658561) B4658561
theorem B2070471 : Blo 2069435 2070471 := bstep (se 1 (by rfl) ⟨1552853, by rfl⟩ : syracuseStep 2070471 = 3105707) B3105707
theorem B2329285 : Blo 2069435 2329285 := bbase (se 4 (by rfl) ⟨218370, by rfl⟩ : syracuseStep 2329285 = 436741) (by norm_num)
theorem B3105713 : Blo 2069435 3105713 := bstep (se 2 (by rfl) ⟨1164642, by rfl⟩ : syracuseStep 3105713 = 2329285) B2329285
theorem B2070475 : Blo 2069435 2070475 := bstep (se 1 (by rfl) ⟨1552856, by rfl⟩ : syracuseStep 2070475 = 3105713) B3105713
theorem B3930677 : Blo 2069435 3930677 := bbase (se 5 (by rfl) ⟨184250, by rfl⟩ : syracuseStep 3930677 = 368501) (by norm_num)
theorem B2620451 : Blo 2069435 2620451 := bstep (se 1 (by rfl) ⟨1965338, by rfl⟩ : syracuseStep 2620451 = 3930677) B3930677
theorem B6987869 : Blo 2069435 6987869 := bstep (se 3 (by rfl) ⟨1310225, by rfl⟩ : syracuseStep 6987869 = 2620451) B2620451
theorem B4658579 : Blo 2069435 4658579 := bstep (se 1 (by rfl) ⟨3493934, by rfl⟩ : syracuseStep 4658579 = 6987869) B6987869
theorem B3105719 : Blo 2069435 3105719 := bstep (se 1 (by rfl) ⟨2329289, by rfl⟩ : syracuseStep 3105719 = 4658579) B4658579
theorem B2070479 : Blo 2069435 2070479 := bstep (se 1 (by rfl) ⟨1552859, by rfl⟩ : syracuseStep 2070479 = 3105719) B3105719
theorem B3105725 : Blo 2069435 3105725 := bbase (se 3 (by rfl) ⟨582323, by rfl⟩ : syracuseStep 3105725 = 1164647) (by norm_num)
theorem B2070483 : Blo 2069435 2070483 := bstep (se 1 (by rfl) ⟨1552862, by rfl⟩ : syracuseStep 2070483 = 3105725) B3105725
theorem B4658597 : Blo 2069435 4658597 := bbase (se 4 (by rfl) ⟨436743, by rfl⟩ : syracuseStep 4658597 = 873487) (by norm_num)
theorem B3105731 : Blo 2069435 3105731 := bstep (se 1 (by rfl) ⟨2329298, by rfl⟩ : syracuseStep 3105731 = 4658597) B4658597
theorem B2070487 : Blo 2069435 2070487 := bstep (se 1 (by rfl) ⟨1552865, by rfl⟩ : syracuseStep 2070487 = 3105731) B3105731
theorem B5240933 : Blo 2069435 5240933 := bbase (se 4 (by rfl) ⟨491337, by rfl⟩ : syracuseStep 5240933 = 982675) (by norm_num)
theorem B3493955 : Blo 2069435 3493955 := bstep (se 1 (by rfl) ⟨2620466, by rfl⟩ : syracuseStep 3493955 = 5240933) B5240933
theorem B2329303 : Blo 2069435 2329303 := bstep (se 1 (by rfl) ⟨1746977, by rfl⟩ : syracuseStep 2329303 = 3493955) B3493955
theorem B3105737 : Blo 2069435 3105737 := bstep (se 2 (by rfl) ⟨1164651, by rfl⟩ : syracuseStep 3105737 = 2329303) B2329303
theorem B2070491 : Blo 2069435 2070491 := bstep (se 1 (by rfl) ⟨1552868, by rfl⟩ : syracuseStep 2070491 = 3105737) B3105737
theorem B2361089 : Blo 2069435 2361089 := bbase (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) (by norm_num)
theorem B6296237 : Blo 2069435 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B4197491 : Blo 2069435 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B2798327 : Blo 2069435 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B7462205 : Blo 2069435 7462205 := bstep (se 3 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 7462205 = 2798327) B2798327
theorem B4974803 : Blo 2069435 4974803 := bstep (se 1 (by rfl) ⟨3731102, by rfl⟩ : syracuseStep 4974803 = 7462205) B7462205
theorem B3316535 : Blo 2069435 3316535 := bstep (se 1 (by rfl) ⟨2487401, by rfl⟩ : syracuseStep 3316535 = 4974803) B4974803
theorem B2211023 : Blo 2069435 2211023 := bstep (se 1 (by rfl) ⟨1658267, by rfl⟩ : syracuseStep 2211023 = 3316535) B3316535
theorem B5896061 : Blo 2069435 5896061 := bstep (se 3 (by rfl) ⟨1105511, by rfl⟩ : syracuseStep 5896061 = 2211023) B2211023
theorem B3930707 : Blo 2069435 3930707 := bstep (se 1 (by rfl) ⟨2948030, by rfl⟩ : syracuseStep 3930707 = 5896061) B5896061
theorem B10481885 : Blo 2069435 10481885 := bstep (se 3 (by rfl) ⟨1965353, by rfl⟩ : syracuseStep 10481885 = 3930707) B3930707
theorem B6987923 : Blo 2069435 6987923 := bstep (se 1 (by rfl) ⟨5240942, by rfl⟩ : syracuseStep 6987923 = 10481885) B10481885
theorem B4658615 : Blo 2069435 4658615 := bstep (se 1 (by rfl) ⟨3493961, by rfl⟩ : syracuseStep 4658615 = 6987923) B6987923
theorem B3105743 : Blo 2069435 3105743 := bstep (se 1 (by rfl) ⟨2329307, by rfl⟩ : syracuseStep 3105743 = 4658615) B4658615
theorem B2070495 : Blo 2069435 2070495 := bstep (se 1 (by rfl) ⟨1552871, by rfl⟩ : syracuseStep 2070495 = 3105743) B3105743
theorem B3105749 : Blo 2069435 3105749 := bbase (se 7 (by rfl) ⟨36395, by rfl⟩ : syracuseStep 3105749 = 72791) (by norm_num)
theorem B2070499 : Blo 2069435 2070499 := bstep (se 1 (by rfl) ⟨1552874, by rfl⟩ : syracuseStep 2070499 = 3105749) B3105749
theorem B7861445 : Blo 2069435 7861445 := bbase (se 4 (by rfl) ⟨737010, by rfl⟩ : syracuseStep 7861445 = 1474021) (by norm_num)
theorem B5240963 : Blo 2069435 5240963 := bstep (se 1 (by rfl) ⟨3930722, by rfl⟩ : syracuseStep 5240963 = 7861445) B7861445
theorem B3493975 : Blo 2069435 3493975 := bstep (se 1 (by rfl) ⟨2620481, by rfl⟩ : syracuseStep 3493975 = 5240963) B5240963
theorem B4658633 : Blo 2069435 4658633 := bstep (se 2 (by rfl) ⟨1746987, by rfl⟩ : syracuseStep 4658633 = 3493975) B3493975
theorem B3105755 : Blo 2069435 3105755 := bstep (se 1 (by rfl) ⟨2329316, by rfl⟩ : syracuseStep 3105755 = 4658633) B4658633
theorem B2070503 : Blo 2069435 2070503 := bstep (se 1 (by rfl) ⟨1552877, by rfl⟩ : syracuseStep 2070503 = 3105755) B3105755
theorem B2329321 : Blo 2069435 2329321 := bbase (se 2 (by rfl) ⟨873495, by rfl⟩ : syracuseStep 2329321 = 1746991) (by norm_num)
theorem B3105761 : Blo 2069435 3105761 := bstep (se 2 (by rfl) ⟨1164660, by rfl⟩ : syracuseStep 3105761 = 2329321) B2329321
theorem B2070507 : Blo 2069435 2070507 := bstep (se 1 (by rfl) ⟨1552880, by rfl⟩ : syracuseStep 2070507 = 3105761) B3105761
theorem B11792213 : Blo 2069435 11792213 := bbase (se 9 (by rfl) ⟨34547, by rfl⟩ : syracuseStep 11792213 = 69095) (by norm_num)
theorem B7861475 : Blo 2069435 7861475 := bstep (se 1 (by rfl) ⟨5896106, by rfl⟩ : syracuseStep 7861475 = 11792213) B11792213
theorem B5240983 : Blo 2069435 5240983 := bstep (se 1 (by rfl) ⟨3930737, by rfl⟩ : syracuseStep 5240983 = 7861475) B7861475
theorem B6987977 : Blo 2069435 6987977 := bstep (se 2 (by rfl) ⟨2620491, by rfl⟩ : syracuseStep 6987977 = 5240983) B5240983
theorem B4658651 : Blo 2069435 4658651 := bstep (se 1 (by rfl) ⟨3493988, by rfl⟩ : syracuseStep 4658651 = 6987977) B6987977
theorem B3105767 : Blo 2069435 3105767 := bstep (se 1 (by rfl) ⟨2329325, by rfl⟩ : syracuseStep 3105767 = 4658651) B4658651
theorem B2070511 : Blo 2069435 2070511 := bstep (se 1 (by rfl) ⟨1552883, by rfl⟩ : syracuseStep 2070511 = 3105767) B3105767
theorem B3105773 : Blo 2069435 3105773 := bbase (se 3 (by rfl) ⟨582332, by rfl⟩ : syracuseStep 3105773 = 1164665) (by norm_num)
theorem B2070515 : Blo 2069435 2070515 := bstep (se 1 (by rfl) ⟨1552886, by rfl⟩ : syracuseStep 2070515 = 3105773) B3105773
theorem B4658669 : Blo 2069435 4658669 := bbase (se 3 (by rfl) ⟨873500, by rfl⟩ : syracuseStep 4658669 = 1747001) (by norm_num)
theorem B3105779 : Blo 2069435 3105779 := bstep (se 1 (by rfl) ⟨2329334, by rfl⟩ : syracuseStep 3105779 = 4658669) B4658669
theorem B2070519 : Blo 2069435 2070519 := bstep (se 1 (by rfl) ⟨1552889, by rfl⟩ : syracuseStep 2070519 = 3105779) B3105779
theorem B11193461 : Blo 2069435 11193461 := bbase (se 5 (by rfl) ⟨524693, by rfl⟩ : syracuseStep 11193461 = 1049387) (by norm_num)
theorem B7462307 : Blo 2069435 7462307 := bstep (se 1 (by rfl) ⟨5596730, by rfl⟩ : syracuseStep 7462307 = 11193461) B11193461
theorem B4974871 : Blo 2069435 4974871 := bstep (se 1 (by rfl) ⟨3731153, by rfl⟩ : syracuseStep 4974871 = 7462307) B7462307
theorem B6633161 : Blo 2069435 6633161 := bstep (se 2 (by rfl) ⟨2487435, by rfl⟩ : syracuseStep 6633161 = 4974871) B4974871
theorem B4422107 : Blo 2069435 4422107 := bstep (se 1 (by rfl) ⟨3316580, by rfl⟩ : syracuseStep 4422107 = 6633161) B6633161
theorem B2948071 : Blo 2069435 2948071 := bstep (se 1 (by rfl) ⟨2211053, by rfl⟩ : syracuseStep 2948071 = 4422107) B4422107
theorem B3930761 : Blo 2069435 3930761 := bstep (se 2 (by rfl) ⟨1474035, by rfl⟩ : syracuseStep 3930761 = 2948071) B2948071
theorem B2620507 : Blo 2069435 2620507 := bstep (se 1 (by rfl) ⟨1965380, by rfl⟩ : syracuseStep 2620507 = 3930761) B3930761
theorem B3494009 : Blo 2069435 3494009 := bstep (se 2 (by rfl) ⟨1310253, by rfl⟩ : syracuseStep 3494009 = 2620507) B2620507
theorem B2329339 : Blo 2069435 2329339 := bstep (se 1 (by rfl) ⟨1747004, by rfl⟩ : syracuseStep 2329339 = 3494009) B3494009
theorem B3105785 : Blo 2069435 3105785 := bstep (se 2 (by rfl) ⟨1164669, by rfl⟩ : syracuseStep 3105785 = 2329339) B2329339
theorem B2070523 : Blo 2069435 2070523 := bstep (se 1 (by rfl) ⟨1552892, by rfl⟩ : syracuseStep 2070523 = 3105785) B3105785
theorem B2098777 : Blo 2069435 2098777 := bbase (se 2 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 2098777 = 1574083) (by norm_num)
theorem B2798369 : Blo 2069435 2798369 := bstep (se 2 (by rfl) ⟨1049388, by rfl⟩ : syracuseStep 2798369 = 2098777) B2098777
theorem B119397077 : Blo 2069435 119397077 := bstep (se 7 (by rfl) ⟨1399184, by rfl⟩ : syracuseStep 119397077 = 2798369) B2798369
theorem B79598051 : Blo 2069435 79598051 := bstep (se 1 (by rfl) ⟨59698538, by rfl⟩ : syracuseStep 79598051 = 119397077) B119397077
theorem B53065367 : Blo 2069435 53065367 := bstep (se 1 (by rfl) ⟨39799025, by rfl⟩ : syracuseStep 53065367 = 79598051) B79598051
theorem B35376911 : Blo 2069435 35376911 := bstep (se 1 (by rfl) ⟨26532683, by rfl⟩ : syracuseStep 35376911 = 53065367) B53065367
theorem B23584607 : Blo 2069435 23584607 := bstep (se 1 (by rfl) ⟨17688455, by rfl⟩ : syracuseStep 23584607 = 35376911) B35376911
theorem B15723071 : Blo 2069435 15723071 := bstep (se 1 (by rfl) ⟨11792303, by rfl⟩ : syracuseStep 15723071 = 23584607) B23584607
theorem B10482047 : Blo 2069435 10482047 := bstep (se 1 (by rfl) ⟨7861535, by rfl⟩ : syracuseStep 10482047 = 15723071) B15723071
theorem B6988031 : Blo 2069435 6988031 := bstep (se 1 (by rfl) ⟨5241023, by rfl⟩ : syracuseStep 6988031 = 10482047) B10482047
theorem B4658687 : Blo 2069435 4658687 := bstep (se 1 (by rfl) ⟨3494015, by rfl⟩ : syracuseStep 4658687 = 6988031) B6988031
theorem B3105791 : Blo 2069435 3105791 := bstep (se 1 (by rfl) ⟨2329343, by rfl⟩ : syracuseStep 3105791 = 4658687) B4658687
theorem B2070527 : Blo 2069435 2070527 := bstep (se 1 (by rfl) ⟨1552895, by rfl⟩ : syracuseStep 2070527 = 3105791) B3105791
theorem B3105797 : Blo 2069435 3105797 := bbase (se 4 (by rfl) ⟨291168, by rfl⟩ : syracuseStep 3105797 = 582337) (by norm_num)
theorem B2070531 : Blo 2069435 2070531 := bstep (se 1 (by rfl) ⟨1552898, by rfl⟩ : syracuseStep 2070531 = 3105797) B3105797
theorem B3494029 : Blo 2069435 3494029 := bbase (se 3 (by rfl) ⟨655130, by rfl⟩ : syracuseStep 3494029 = 1310261) (by norm_num)
theorem B4658705 : Blo 2069435 4658705 := bstep (se 2 (by rfl) ⟨1747014, by rfl⟩ : syracuseStep 4658705 = 3494029) B3494029
theorem B3105803 : Blo 2069435 3105803 := bstep (se 1 (by rfl) ⟨2329352, by rfl⟩ : syracuseStep 3105803 = 4658705) B4658705
theorem B2070535 : Blo 2069435 2070535 := bstep (se 1 (by rfl) ⟨1552901, by rfl⟩ : syracuseStep 2070535 = 3105803) B3105803
theorem B2329357 : Blo 2069435 2329357 := bbase (se 3 (by rfl) ⟨436754, by rfl⟩ : syracuseStep 2329357 = 873509) (by norm_num)
theorem B3105809 : Blo 2069435 3105809 := bstep (se 2 (by rfl) ⟨1164678, by rfl⟩ : syracuseStep 3105809 = 2329357) B2329357
theorem B2070539 : Blo 2069435 2070539 := bstep (se 1 (by rfl) ⟨1552904, by rfl⟩ : syracuseStep 2070539 = 3105809) B3105809
theorem B6988085 : Blo 2069435 6988085 := bbase (se 5 (by rfl) ⟨327566, by rfl⟩ : syracuseStep 6988085 = 655133) (by norm_num)
theorem B4658723 : Blo 2069435 4658723 := bstep (se 1 (by rfl) ⟨3494042, by rfl⟩ : syracuseStep 4658723 = 6988085) B6988085
theorem B3105815 : Blo 2069435 3105815 := bstep (se 1 (by rfl) ⟨2329361, by rfl⟩ : syracuseStep 3105815 = 4658723) B4658723
theorem B2070543 : Blo 2069435 2070543 := bstep (se 1 (by rfl) ⟨1552907, by rfl⟩ : syracuseStep 2070543 = 3105815) B3105815
theorem B3105821 : Blo 2069435 3105821 := bbase (se 3 (by rfl) ⟨582341, by rfl⟩ : syracuseStep 3105821 = 1164683) (by norm_num)
theorem B2070547 : Blo 2069435 2070547 := bstep (se 1 (by rfl) ⟨1552910, by rfl⟩ : syracuseStep 2070547 = 3105821) B3105821
theorem B4658741 : Blo 2069435 4658741 := bbase (se 5 (by rfl) ⟨218378, by rfl⟩ : syracuseStep 4658741 = 436757) (by norm_num)
theorem B3105827 : Blo 2069435 3105827 := bstep (se 1 (by rfl) ⟨2329370, by rfl⟩ : syracuseStep 3105827 = 4658741) B4658741
theorem B2070551 : Blo 2069435 2070551 := bstep (se 1 (by rfl) ⟨1552913, by rfl⟩ : syracuseStep 2070551 = 3105827) B3105827
theorem B7462421 : Blo 2069435 7462421 := bbase (se 6 (by rfl) ⟨174900, by rfl⟩ : syracuseStep 7462421 = 349801) (by norm_num)
theorem B4974947 : Blo 2069435 4974947 := bstep (se 1 (by rfl) ⟨3731210, by rfl⟩ : syracuseStep 4974947 = 7462421) B7462421
theorem B3316631 : Blo 2069435 3316631 := bstep (se 1 (by rfl) ⟨2487473, by rfl⟩ : syracuseStep 3316631 = 4974947) B4974947
theorem B8844349 : Blo 2069435 8844349 := bstep (se 3 (by rfl) ⟨1658315, by rfl⟩ : syracuseStep 8844349 = 3316631) B3316631
theorem B11792465 : Blo 2069435 11792465 := bstep (se 2 (by rfl) ⟨4422174, by rfl⟩ : syracuseStep 11792465 = 8844349) B8844349
theorem B7861643 : Blo 2069435 7861643 := bstep (se 1 (by rfl) ⟨5896232, by rfl⟩ : syracuseStep 7861643 = 11792465) B11792465
theorem B5241095 : Blo 2069435 5241095 := bstep (se 1 (by rfl) ⟨3930821, by rfl⟩ : syracuseStep 5241095 = 7861643) B7861643
theorem B3494063 : Blo 2069435 3494063 := bstep (se 1 (by rfl) ⟨2620547, by rfl⟩ : syracuseStep 3494063 = 5241095) B5241095
theorem B2329375 : Blo 2069435 2329375 := bstep (se 1 (by rfl) ⟨1747031, by rfl⟩ : syracuseStep 2329375 = 3494063) B3494063
theorem B3105833 : Blo 2069435 3105833 := bstep (se 2 (by rfl) ⟨1164687, by rfl⟩ : syracuseStep 3105833 = 2329375) B2329375
theorem B2070555 : Blo 2069435 2070555 := bstep (se 1 (by rfl) ⟨1552916, by rfl⟩ : syracuseStep 2070555 = 3105833) B3105833
theorem B3316637 : Blo 2069435 3316637 := bbase (se 3 (by rfl) ⟨621869, by rfl⟩ : syracuseStep 3316637 = 1243739) (by norm_num)
theorem B8844365 : Blo 2069435 8844365 := bstep (se 3 (by rfl) ⟨1658318, by rfl⟩ : syracuseStep 8844365 = 3316637) B3316637
theorem B5896243 : Blo 2069435 5896243 := bstep (se 1 (by rfl) ⟨4422182, by rfl⟩ : syracuseStep 5896243 = 8844365) B8844365
theorem B7861657 : Blo 2069435 7861657 := bstep (se 2 (by rfl) ⟨2948121, by rfl⟩ : syracuseStep 7861657 = 5896243) B5896243
theorem B10482209 : Blo 2069435 10482209 := bstep (se 2 (by rfl) ⟨3930828, by rfl⟩ : syracuseStep 10482209 = 7861657) B7861657
theorem B6988139 : Blo 2069435 6988139 := bstep (se 1 (by rfl) ⟨5241104, by rfl⟩ : syracuseStep 6988139 = 10482209) B10482209
theorem B4658759 : Blo 2069435 4658759 := bstep (se 1 (by rfl) ⟨3494069, by rfl⟩ : syracuseStep 4658759 = 6988139) B6988139
theorem B3105839 : Blo 2069435 3105839 := bstep (se 1 (by rfl) ⟨2329379, by rfl⟩ : syracuseStep 3105839 = 4658759) B4658759
theorem B2070559 : Blo 2069435 2070559 := bstep (se 1 (by rfl) ⟨1552919, by rfl⟩ : syracuseStep 2070559 = 3105839) B3105839
theorem B3105845 : Blo 2069435 3105845 := bbase (se 5 (by rfl) ⟨145586, by rfl⟩ : syracuseStep 3105845 = 291173) (by norm_num)
theorem B2070563 : Blo 2069435 2070563 := bstep (se 1 (by rfl) ⟨1552922, by rfl⟩ : syracuseStep 2070563 = 3105845) B3105845
theorem B5241125 : Blo 2069435 5241125 := bbase (se 4 (by rfl) ⟨491355, by rfl⟩ : syracuseStep 5241125 = 982711) (by norm_num)
theorem B3494083 : Blo 2069435 3494083 := bstep (se 1 (by rfl) ⟨2620562, by rfl⟩ : syracuseStep 3494083 = 5241125) B5241125
theorem B4658777 : Blo 2069435 4658777 := bstep (se 2 (by rfl) ⟨1747041, by rfl⟩ : syracuseStep 4658777 = 3494083) B3494083
theorem B3105851 : Blo 2069435 3105851 := bstep (se 1 (by rfl) ⟨2329388, by rfl⟩ : syracuseStep 3105851 = 4658777) B4658777
theorem B2070567 : Blo 2069435 2070567 := bstep (se 1 (by rfl) ⟨1552925, by rfl⟩ : syracuseStep 2070567 = 3105851) B3105851
theorem B2329393 : Blo 2069435 2329393 := bbase (se 2 (by rfl) ⟨873522, by rfl⟩ : syracuseStep 2329393 = 1747045) (by norm_num)
theorem B3105857 : Blo 2069435 3105857 := bstep (se 2 (by rfl) ⟨1164696, by rfl⟩ : syracuseStep 3105857 = 2329393) B2329393
theorem B2070571 : Blo 2069435 2070571 := bstep (se 1 (by rfl) ⟨1552928, by rfl⟩ : syracuseStep 2070571 = 3105857) B3105857
theorem B4197653 : Blo 2069435 4197653 := bbase (se 6 (by rfl) ⟨98382, by rfl⟩ : syracuseStep 4197653 = 196765) (by norm_num)
theorem B2798435 : Blo 2069435 2798435 := bstep (se 1 (by rfl) ⟨2098826, by rfl⟩ : syracuseStep 2798435 = 4197653) B4197653
theorem B7462493 : Blo 2069435 7462493 := bstep (se 3 (by rfl) ⟨1399217, by rfl⟩ : syracuseStep 7462493 = 2798435) B2798435
theorem B4974995 : Blo 2069435 4974995 := bstep (se 1 (by rfl) ⟨3731246, by rfl⟩ : syracuseStep 4974995 = 7462493) B7462493
theorem B3316663 : Blo 2069435 3316663 := bstep (se 1 (by rfl) ⟨2487497, by rfl⟩ : syracuseStep 3316663 = 4974995) B4974995
theorem B4422217 : Blo 2069435 4422217 := bstep (se 2 (by rfl) ⟨1658331, by rfl⟩ : syracuseStep 4422217 = 3316663) B3316663
theorem B5896289 : Blo 2069435 5896289 := bstep (se 2 (by rfl) ⟨2211108, by rfl⟩ : syracuseStep 5896289 = 4422217) B4422217
theorem B3930859 : Blo 2069435 3930859 := bstep (se 1 (by rfl) ⟨2948144, by rfl⟩ : syracuseStep 3930859 = 5896289) B5896289
theorem B5241145 : Blo 2069435 5241145 := bstep (se 2 (by rfl) ⟨1965429, by rfl⟩ : syracuseStep 5241145 = 3930859) B3930859
theorem B6988193 : Blo 2069435 6988193 := bstep (se 2 (by rfl) ⟨2620572, by rfl⟩ : syracuseStep 6988193 = 5241145) B5241145
theorem B4658795 : Blo 2069435 4658795 := bstep (se 1 (by rfl) ⟨3494096, by rfl⟩ : syracuseStep 4658795 = 6988193) B6988193
theorem B3105863 : Blo 2069435 3105863 := bstep (se 1 (by rfl) ⟨2329397, by rfl⟩ : syracuseStep 3105863 = 4658795) B4658795
theorem B2070575 : Blo 2069435 2070575 := bstep (se 1 (by rfl) ⟨1552931, by rfl⟩ : syracuseStep 2070575 = 3105863) B3105863
theorem B3105869 : Blo 2069435 3105869 := bbase (se 3 (by rfl) ⟨582350, by rfl⟩ : syracuseStep 3105869 = 1164701) (by norm_num)
theorem B2070579 : Blo 2069435 2070579 := bstep (se 1 (by rfl) ⟨1552934, by rfl⟩ : syracuseStep 2070579 = 3105869) B3105869
theorem B4658813 : Blo 2069435 4658813 := bbase (se 3 (by rfl) ⟨873527, by rfl⟩ : syracuseStep 4658813 = 1747055) (by norm_num)
theorem B3105875 : Blo 2069435 3105875 := bstep (se 1 (by rfl) ⟨2329406, by rfl⟩ : syracuseStep 3105875 = 4658813) B4658813
theorem B2070583 : Blo 2069435 2070583 := bstep (se 1 (by rfl) ⟨1552937, by rfl⟩ : syracuseStep 2070583 = 3105875) B3105875
theorem B3494117 : Blo 2069435 3494117 := bbase (se 4 (by rfl) ⟨327573, by rfl⟩ : syracuseStep 3494117 = 655147) (by norm_num)
theorem B2329411 : Blo 2069435 2329411 := bstep (se 1 (by rfl) ⟨1747058, by rfl⟩ : syracuseStep 2329411 = 3494117) B3494117
theorem B3105881 : Blo 2069435 3105881 := bstep (se 2 (by rfl) ⟨1164705, by rfl⟩ : syracuseStep 3105881 = 2329411) B2329411
theorem B2070587 : Blo 2069435 2070587 := bstep (se 1 (by rfl) ⟨1552940, by rfl⟩ : syracuseStep 2070587 = 3105881) B3105881
theorem B4197685 : Blo 2069435 4197685 := bbase (se 5 (by rfl) ⟨196766, by rfl⟩ : syracuseStep 4197685 = 393533) (by norm_num)
theorem B5596913 : Blo 2069435 5596913 := bstep (se 2 (by rfl) ⟨2098842, by rfl⟩ : syracuseStep 5596913 = 4197685) B4197685
theorem B3731275 : Blo 2069435 3731275 := bstep (se 1 (by rfl) ⟨2798456, by rfl⟩ : syracuseStep 3731275 = 5596913) B5596913
theorem B4975033 : Blo 2069435 4975033 := bstep (se 2 (by rfl) ⟨1865637, by rfl⟩ : syracuseStep 4975033 = 3731275) B3731275
theorem B6633377 : Blo 2069435 6633377 := bstep (se 2 (by rfl) ⟨2487516, by rfl⟩ : syracuseStep 6633377 = 4975033) B4975033
theorem B4422251 : Blo 2069435 4422251 := bstep (se 1 (by rfl) ⟨3316688, by rfl⟩ : syracuseStep 4422251 = 6633377) B6633377
theorem B2948167 : Blo 2069435 2948167 := bstep (se 1 (by rfl) ⟨2211125, by rfl⟩ : syracuseStep 2948167 = 4422251) B4422251
theorem B15723557 : Blo 2069435 15723557 := bstep (se 4 (by rfl) ⟨1474083, by rfl⟩ : syracuseStep 15723557 = 2948167) B2948167
theorem B10482371 : Blo 2069435 10482371 := bstep (se 1 (by rfl) ⟨7861778, by rfl⟩ : syracuseStep 10482371 = 15723557) B15723557
theorem B6988247 : Blo 2069435 6988247 := bstep (se 1 (by rfl) ⟨5241185, by rfl⟩ : syracuseStep 6988247 = 10482371) B10482371
theorem B4658831 : Blo 2069435 4658831 := bstep (se 1 (by rfl) ⟨3494123, by rfl⟩ : syracuseStep 4658831 = 6988247) B6988247
theorem B3105887 : Blo 2069435 3105887 := bstep (se 1 (by rfl) ⟨2329415, by rfl⟩ : syracuseStep 3105887 = 4658831) B4658831
theorem B2070591 : Blo 2069435 2070591 := bstep (se 1 (by rfl) ⟨1552943, by rfl⟩ : syracuseStep 2070591 = 3105887) B3105887
theorem B3105893 : Blo 2069435 3105893 := bbase (se 4 (by rfl) ⟨291177, by rfl⟩ : syracuseStep 3105893 = 582355) (by norm_num)
theorem B2070595 : Blo 2069435 2070595 := bstep (se 1 (by rfl) ⟨1552946, by rfl⟩ : syracuseStep 2070595 = 3105893) B3105893
theorem B4422269 : Blo 2069435 4422269 := bbase (se 3 (by rfl) ⟨829175, by rfl⟩ : syracuseStep 4422269 = 1658351) (by norm_num)
theorem B2948179 : Blo 2069435 2948179 := bstep (se 1 (by rfl) ⟨2211134, by rfl⟩ : syracuseStep 2948179 = 4422269) B4422269
theorem B3930905 : Blo 2069435 3930905 := bstep (se 2 (by rfl) ⟨1474089, by rfl⟩ : syracuseStep 3930905 = 2948179) B2948179
theorem B2620603 : Blo 2069435 2620603 := bstep (se 1 (by rfl) ⟨1965452, by rfl⟩ : syracuseStep 2620603 = 3930905) B3930905
theorem B3494137 : Blo 2069435 3494137 := bstep (se 2 (by rfl) ⟨1310301, by rfl⟩ : syracuseStep 3494137 = 2620603) B2620603
theorem B4658849 : Blo 2069435 4658849 := bstep (se 2 (by rfl) ⟨1747068, by rfl⟩ : syracuseStep 4658849 = 3494137) B3494137
theorem B3105899 : Blo 2069435 3105899 := bstep (se 1 (by rfl) ⟨2329424, by rfl⟩ : syracuseStep 3105899 = 4658849) B4658849
theorem B2070599 : Blo 2069435 2070599 := bstep (se 1 (by rfl) ⟨1552949, by rfl⟩ : syracuseStep 2070599 = 3105899) B3105899
theorem B2329429 : Blo 2069435 2329429 := bbase (se 9 (by rfl) ⟨6824, by rfl⟩ : syracuseStep 2329429 = 13649) (by norm_num)
theorem B3105905 : Blo 2069435 3105905 := bstep (se 2 (by rfl) ⟨1164714, by rfl⟩ : syracuseStep 3105905 = 2329429) B2329429
theorem B2070603 : Blo 2069435 2070603 := bstep (se 1 (by rfl) ⟨1552952, by rfl⟩ : syracuseStep 2070603 = 3105905) B3105905
theorem B2620613 : Blo 2069435 2620613 := bbase (se 4 (by rfl) ⟨245682, by rfl⟩ : syracuseStep 2620613 = 491365) (by norm_num)
theorem B6988301 : Blo 2069435 6988301 := bstep (se 3 (by rfl) ⟨1310306, by rfl⟩ : syracuseStep 6988301 = 2620613) B2620613
theorem B4658867 : Blo 2069435 4658867 := bstep (se 1 (by rfl) ⟨3494150, by rfl⟩ : syracuseStep 4658867 = 6988301) B6988301
theorem B3105911 : Blo 2069435 3105911 := bstep (se 1 (by rfl) ⟨2329433, by rfl⟩ : syracuseStep 3105911 = 4658867) B4658867
theorem B2070607 : Blo 2069435 2070607 := bstep (se 1 (by rfl) ⟨1552955, by rfl⟩ : syracuseStep 2070607 = 3105911) B3105911
theorem B3105917 : Blo 2069435 3105917 := bbase (se 3 (by rfl) ⟨582359, by rfl⟩ : syracuseStep 3105917 = 1164719) (by norm_num)
theorem B2070611 : Blo 2069435 2070611 := bstep (se 1 (by rfl) ⟨1552958, by rfl⟩ : syracuseStep 2070611 = 3105917) B3105917
theorem B4658885 : Blo 2069435 4658885 := bbase (se 4 (by rfl) ⟨436770, by rfl⟩ : syracuseStep 4658885 = 873541) (by norm_num)
theorem B3105923 : Blo 2069435 3105923 := bstep (se 1 (by rfl) ⟨2329442, by rfl⟩ : syracuseStep 3105923 = 4658885) B4658885
theorem B2070615 : Blo 2069435 2070615 := bstep (se 1 (by rfl) ⟨1552961, by rfl⟩ : syracuseStep 2070615 = 3105923) B3105923
theorem B9573781 : Blo 2069435 9573781 := bbase (se 6 (by rfl) ⟨224385, by rfl⟩ : syracuseStep 9573781 = 448771) (by norm_num)
theorem B12765041 : Blo 2069435 12765041 := bstep (se 2 (by rfl) ⟨4786890, by rfl⟩ : syracuseStep 12765041 = 9573781) B9573781
theorem B8510027 : Blo 2069435 8510027 := bstep (se 1 (by rfl) ⟨6382520, by rfl⟩ : syracuseStep 8510027 = 12765041) B12765041
theorem B90773621 : Blo 2069435 90773621 := bstep (se 5 (by rfl) ⟨4255013, by rfl⟩ : syracuseStep 90773621 = 8510027) B8510027
theorem B60515747 : Blo 2069435 60515747 := bstep (se 1 (by rfl) ⟨45386810, by rfl⟩ : syracuseStep 60515747 = 90773621) B90773621
theorem B40343831 : Blo 2069435 40343831 := bstep (se 1 (by rfl) ⟨30257873, by rfl⟩ : syracuseStep 40343831 = 60515747) B60515747
theorem B26895887 : Blo 2069435 26895887 := bstep (se 1 (by rfl) ⟨20171915, by rfl⟩ : syracuseStep 26895887 = 40343831) B40343831
theorem B17930591 : Blo 2069435 17930591 := bstep (se 1 (by rfl) ⟨13447943, by rfl⟩ : syracuseStep 17930591 = 26895887) B26895887
theorem B11953727 : Blo 2069435 11953727 := bstep (se 1 (by rfl) ⟨8965295, by rfl⟩ : syracuseStep 11953727 = 17930591) B17930591
theorem B7969151 : Blo 2069435 7969151 := bstep (se 1 (by rfl) ⟨5976863, by rfl⟩ : syracuseStep 7969151 = 11953727) B11953727
theorem B21251069 : Blo 2069435 21251069 := bstep (se 3 (by rfl) ⟨3984575, by rfl⟩ : syracuseStep 21251069 = 7969151) B7969151
theorem B14167379 : Blo 2069435 14167379 := bstep (se 1 (by rfl) ⟨10625534, by rfl⟩ : syracuseStep 14167379 = 21251069) B21251069
theorem B9444919 : Blo 2069435 9444919 := bstep (se 1 (by rfl) ⟨7083689, by rfl⟩ : syracuseStep 9444919 = 14167379) B14167379
theorem B12593225 : Blo 2069435 12593225 := bstep (se 2 (by rfl) ⟨4722459, by rfl⟩ : syracuseStep 12593225 = 9444919) B9444919
theorem B8395483 : Blo 2069435 8395483 := bstep (se 1 (by rfl) ⟨6296612, by rfl⟩ : syracuseStep 8395483 = 12593225) B12593225
theorem B11193977 : Blo 2069435 11193977 := bstep (se 2 (by rfl) ⟨4197741, by rfl⟩ : syracuseStep 11193977 = 8395483) B8395483
theorem B29850605 : Blo 2069435 29850605 := bstep (se 3 (by rfl) ⟨5596988, by rfl⟩ : syracuseStep 29850605 = 11193977) B11193977
theorem B19900403 : Blo 2069435 19900403 := bstep (se 1 (by rfl) ⟨14925302, by rfl⟩ : syracuseStep 19900403 = 29850605) B29850605
theorem B13266935 : Blo 2069435 13266935 := bstep (se 1 (by rfl) ⟨9950201, by rfl⟩ : syracuseStep 13266935 = 19900403) B19900403
theorem B8844623 : Blo 2069435 8844623 := bstep (se 1 (by rfl) ⟨6633467, by rfl⟩ : syracuseStep 8844623 = 13266935) B13266935
theorem B5896415 : Blo 2069435 5896415 := bstep (se 1 (by rfl) ⟨4422311, by rfl⟩ : syracuseStep 5896415 = 8844623) B8844623
theorem B3930943 : Blo 2069435 3930943 := bstep (se 1 (by rfl) ⟨2948207, by rfl⟩ : syracuseStep 3930943 = 5896415) B5896415
theorem B5241257 : Blo 2069435 5241257 := bstep (se 2 (by rfl) ⟨1965471, by rfl⟩ : syracuseStep 5241257 = 3930943) B3930943
theorem B3494171 : Blo 2069435 3494171 := bstep (se 1 (by rfl) ⟨2620628, by rfl⟩ : syracuseStep 3494171 = 5241257) B5241257
theorem B2329447 : Blo 2069435 2329447 := bstep (se 1 (by rfl) ⟨1747085, by rfl⟩ : syracuseStep 2329447 = 3494171) B3494171
theorem B3105929 : Blo 2069435 3105929 := bstep (se 2 (by rfl) ⟨1164723, by rfl⟩ : syracuseStep 3105929 = 2329447) B2329447
theorem B2070619 : Blo 2069435 2070619 := bstep (se 1 (by rfl) ⟨1552964, by rfl⟩ : syracuseStep 2070619 = 3105929) B3105929
theorem B10482533 : Blo 2069435 10482533 := bbase (se 4 (by rfl) ⟨982737, by rfl⟩ : syracuseStep 10482533 = 1965475) (by norm_num)
theorem B6988355 : Blo 2069435 6988355 := bstep (se 1 (by rfl) ⟨5241266, by rfl⟩ : syracuseStep 6988355 = 10482533) B10482533
theorem B4658903 : Blo 2069435 4658903 := bstep (se 1 (by rfl) ⟨3494177, by rfl⟩ : syracuseStep 4658903 = 6988355) B6988355
theorem B3105935 : Blo 2069435 3105935 := bstep (se 1 (by rfl) ⟨2329451, by rfl⟩ : syracuseStep 3105935 = 4658903) B4658903
theorem B2070623 : Blo 2069435 2070623 := bstep (se 1 (by rfl) ⟨1552967, by rfl⟩ : syracuseStep 2070623 = 3105935) B3105935
theorem B3105941 : Blo 2069435 3105941 := bbase (se 6 (by rfl) ⟨72795, by rfl⟩ : syracuseStep 3105941 = 145591) (by norm_num)
theorem B2070627 : Blo 2069435 2070627 := bstep (se 1 (by rfl) ⟨1552970, by rfl⟩ : syracuseStep 2070627 = 3105941) B3105941
theorem B3148325 : Blo 2069435 3148325 := bbase (se 4 (by rfl) ⟨295155, by rfl⟩ : syracuseStep 3148325 = 590311) (by norm_num)
theorem B2098883 : Blo 2069435 2098883 := bstep (se 1 (by rfl) ⟨1574162, by rfl⟩ : syracuseStep 2098883 = 3148325) B3148325
theorem B5597021 : Blo 2069435 5597021 := bstep (se 3 (by rfl) ⟨1049441, by rfl⟩ : syracuseStep 5597021 = 2098883) B2098883
theorem B3731347 : Blo 2069435 3731347 := bstep (se 1 (by rfl) ⟨2798510, by rfl⟩ : syracuseStep 3731347 = 5597021) B5597021
theorem B4975129 : Blo 2069435 4975129 := bstep (se 2 (by rfl) ⟨1865673, by rfl⟩ : syracuseStep 4975129 = 3731347) B3731347
theorem B6633505 : Blo 2069435 6633505 := bstep (se 2 (by rfl) ⟨2487564, by rfl⟩ : syracuseStep 6633505 = 4975129) B4975129
theorem B8844673 : Blo 2069435 8844673 := bstep (se 2 (by rfl) ⟨3316752, by rfl⟩ : syracuseStep 8844673 = 6633505) B6633505
theorem B11792897 : Blo 2069435 11792897 := bstep (se 2 (by rfl) ⟨4422336, by rfl⟩ : syracuseStep 11792897 = 8844673) B8844673
theorem B7861931 : Blo 2069435 7861931 := bstep (se 1 (by rfl) ⟨5896448, by rfl⟩ : syracuseStep 7861931 = 11792897) B11792897
theorem B5241287 : Blo 2069435 5241287 := bstep (se 1 (by rfl) ⟨3930965, by rfl⟩ : syracuseStep 5241287 = 7861931) B7861931
theorem B3494191 : Blo 2069435 3494191 := bstep (se 1 (by rfl) ⟨2620643, by rfl⟩ : syracuseStep 3494191 = 5241287) B5241287
theorem B4658921 : Blo 2069435 4658921 := bstep (se 2 (by rfl) ⟨1747095, by rfl⟩ : syracuseStep 4658921 = 3494191) B3494191
theorem B3105947 : Blo 2069435 3105947 := bstep (se 1 (by rfl) ⟨2329460, by rfl⟩ : syracuseStep 3105947 = 4658921) B4658921
theorem B2070631 : Blo 2069435 2070631 := bstep (se 1 (by rfl) ⟨1552973, by rfl⟩ : syracuseStep 2070631 = 3105947) B3105947
theorem B2329465 : Blo 2069435 2329465 := bbase (se 2 (by rfl) ⟨873549, by rfl⟩ : syracuseStep 2329465 = 1747099) (by norm_num)
theorem B3105953 : Blo 2069435 3105953 := bstep (se 2 (by rfl) ⟨1164732, by rfl⟩ : syracuseStep 3105953 = 2329465) B2329465
theorem B2070635 : Blo 2069435 2070635 := bstep (se 1 (by rfl) ⟨1552976, by rfl⟩ : syracuseStep 2070635 = 3105953) B3105953
theorem B13267061 : Blo 2069435 13267061 := bbase (se 5 (by rfl) ⟨621893, by rfl⟩ : syracuseStep 13267061 = 1243787) (by norm_num)
theorem B8844707 : Blo 2069435 8844707 := bstep (se 1 (by rfl) ⟨6633530, by rfl⟩ : syracuseStep 8844707 = 13267061) B13267061
theorem B5896471 : Blo 2069435 5896471 := bstep (se 1 (by rfl) ⟨4422353, by rfl⟩ : syracuseStep 5896471 = 8844707) B8844707
theorem B7861961 : Blo 2069435 7861961 := bstep (se 2 (by rfl) ⟨2948235, by rfl⟩ : syracuseStep 7861961 = 5896471) B5896471
theorem B5241307 : Blo 2069435 5241307 := bstep (se 1 (by rfl) ⟨3930980, by rfl⟩ : syracuseStep 5241307 = 7861961) B7861961
theorem B6988409 : Blo 2069435 6988409 := bstep (se 2 (by rfl) ⟨2620653, by rfl⟩ : syracuseStep 6988409 = 5241307) B5241307
theorem B4658939 : Blo 2069435 4658939 := bstep (se 1 (by rfl) ⟨3494204, by rfl⟩ : syracuseStep 4658939 = 6988409) B6988409
theorem B3105959 : Blo 2069435 3105959 := bstep (se 1 (by rfl) ⟨2329469, by rfl⟩ : syracuseStep 3105959 = 4658939) B4658939
theorem B2070639 : Blo 2069435 2070639 := bstep (se 1 (by rfl) ⟨1552979, by rfl⟩ : syracuseStep 2070639 = 3105959) B3105959
theorem B3105965 : Blo 2069435 3105965 := bbase (se 3 (by rfl) ⟨582368, by rfl⟩ : syracuseStep 3105965 = 1164737) (by norm_num)
theorem B2070643 : Blo 2069435 2070643 := bstep (se 1 (by rfl) ⟨1552982, by rfl⟩ : syracuseStep 2070643 = 3105965) B3105965
theorem B4658957 : Blo 2069435 4658957 := bbase (se 3 (by rfl) ⟨873554, by rfl⟩ : syracuseStep 4658957 = 1747109) (by norm_num)
theorem B3105971 : Blo 2069435 3105971 := bstep (se 1 (by rfl) ⟨2329478, by rfl⟩ : syracuseStep 3105971 = 4658957) B4658957
theorem B2070647 : Blo 2069435 2070647 := bstep (se 1 (by rfl) ⟨1552985, by rfl⟩ : syracuseStep 2070647 = 3105971) B3105971
theorem B2620669 : Blo 2069435 2620669 := bbase (se 3 (by rfl) ⟨491375, by rfl⟩ : syracuseStep 2620669 = 982751) (by norm_num)
theorem B3494225 : Blo 2069435 3494225 := bstep (se 2 (by rfl) ⟨1310334, by rfl⟩ : syracuseStep 3494225 = 2620669) B2620669
theorem B2329483 : Blo 2069435 2329483 := bstep (se 1 (by rfl) ⟨1747112, by rfl⟩ : syracuseStep 2329483 = 3494225) B3494225
theorem B3105977 : Blo 2069435 3105977 := bstep (se 2 (by rfl) ⟨1164741, by rfl⟩ : syracuseStep 3105977 = 2329483) B2329483
theorem B2070651 : Blo 2069435 2070651 := bstep (se 1 (by rfl) ⟨1552988, by rfl⟩ : syracuseStep 2070651 = 3105977) B3105977
theorem B2487593 : Blo 2069435 2487593 := bbase (se 2 (by rfl) ⟨932847, by rfl⟩ : syracuseStep 2487593 = 1865695) (by norm_num)
theorem B6633581 : Blo 2069435 6633581 := bstep (se 3 (by rfl) ⟨1243796, by rfl⟩ : syracuseStep 6633581 = 2487593) B2487593
theorem B17689549 : Blo 2069435 17689549 := bstep (se 3 (by rfl) ⟨3316790, by rfl⟩ : syracuseStep 17689549 = 6633581) B6633581
theorem B23586065 : Blo 2069435 23586065 := bstep (se 2 (by rfl) ⟨8844774, by rfl⟩ : syracuseStep 23586065 = 17689549) B17689549
theorem B15724043 : Blo 2069435 15724043 := bstep (se 1 (by rfl) ⟨11793032, by rfl⟩ : syracuseStep 15724043 = 23586065) B23586065
theorem B10482695 : Blo 2069435 10482695 := bstep (se 1 (by rfl) ⟨7862021, by rfl⟩ : syracuseStep 10482695 = 15724043) B15724043
theorem B6988463 : Blo 2069435 6988463 := bstep (se 1 (by rfl) ⟨5241347, by rfl⟩ : syracuseStep 6988463 = 10482695) B10482695
theorem B4658975 : Blo 2069435 4658975 := bstep (se 1 (by rfl) ⟨3494231, by rfl⟩ : syracuseStep 4658975 = 6988463) B6988463
theorem B3105983 : Blo 2069435 3105983 := bstep (se 1 (by rfl) ⟨2329487, by rfl⟩ : syracuseStep 3105983 = 4658975) B4658975
theorem B2070655 : Blo 2069435 2070655 := bstep (se 1 (by rfl) ⟨1552991, by rfl⟩ : syracuseStep 2070655 = 3105983) B3105983
theorem B3105989 : Blo 2069435 3105989 := bbase (se 4 (by rfl) ⟨291186, by rfl⟩ : syracuseStep 3105989 = 582373) (by norm_num)
theorem B2070659 : Blo 2069435 2070659 := bstep (se 1 (by rfl) ⟨1552994, by rfl⟩ : syracuseStep 2070659 = 3105989) B3105989
theorem B3494245 : Blo 2069435 3494245 := bbase (se 4 (by rfl) ⟨327585, by rfl⟩ : syracuseStep 3494245 = 655171) (by norm_num)
theorem B4658993 : Blo 2069435 4658993 := bstep (se 2 (by rfl) ⟨1747122, by rfl⟩ : syracuseStep 4658993 = 3494245) B3494245
theorem B3105995 : Blo 2069435 3105995 := bstep (se 1 (by rfl) ⟨2329496, by rfl⟩ : syracuseStep 3105995 = 4658993) B4658993
theorem B2070663 : Blo 2069435 2070663 := bstep (se 1 (by rfl) ⟨1552997, by rfl⟩ : syracuseStep 2070663 = 3105995) B3105995
theorem B2329501 : Blo 2069435 2329501 := bbase (se 3 (by rfl) ⟨436781, by rfl⟩ : syracuseStep 2329501 = 873563) (by norm_num)
theorem B3106001 : Blo 2069435 3106001 := bstep (se 2 (by rfl) ⟨1164750, by rfl⟩ : syracuseStep 3106001 = 2329501) B2329501
theorem B2070667 : Blo 2069435 2070667 := bstep (se 1 (by rfl) ⟨1553000, by rfl⟩ : syracuseStep 2070667 = 3106001) B3106001
theorem B6988517 : Blo 2069435 6988517 := bbase (se 4 (by rfl) ⟨655173, by rfl⟩ : syracuseStep 6988517 = 1310347) (by norm_num)
theorem B4659011 : Blo 2069435 4659011 := bstep (se 1 (by rfl) ⟨3494258, by rfl⟩ : syracuseStep 4659011 = 6988517) B6988517
theorem B3106007 : Blo 2069435 3106007 := bstep (se 1 (by rfl) ⟨2329505, by rfl⟩ : syracuseStep 3106007 = 4659011) B4659011
theorem B2070671 : Blo 2069435 2070671 := bstep (se 1 (by rfl) ⟨1553003, by rfl⟩ : syracuseStep 2070671 = 3106007) B3106007
theorem B3106013 : Blo 2069435 3106013 := bbase (se 3 (by rfl) ⟨582377, by rfl⟩ : syracuseStep 3106013 = 1164755) (by norm_num)
theorem B2070675 : Blo 2069435 2070675 := bstep (se 1 (by rfl) ⟨1553006, by rfl⟩ : syracuseStep 2070675 = 3106013) B3106013
theorem B4659029 : Blo 2069435 4659029 := bbase (se 9 (by rfl) ⟨13649, by rfl⟩ : syracuseStep 4659029 = 27299) (by norm_num)
theorem B3106019 : Blo 2069435 3106019 := bstep (se 1 (by rfl) ⟨2329514, by rfl⟩ : syracuseStep 3106019 = 4659029) B4659029
theorem B2070679 : Blo 2069435 2070679 := bstep (se 1 (by rfl) ⟨1553009, by rfl⟩ : syracuseStep 2070679 = 3106019) B3106019
theorem B5896597 : Blo 2069435 5896597 := bbase (se 6 (by rfl) ⟨138201, by rfl⟩ : syracuseStep 5896597 = 276403) (by norm_num)
theorem B7862129 : Blo 2069435 7862129 := bstep (se 2 (by rfl) ⟨2948298, by rfl⟩ : syracuseStep 7862129 = 5896597) B5896597
theorem B5241419 : Blo 2069435 5241419 := bstep (se 1 (by rfl) ⟨3931064, by rfl⟩ : syracuseStep 5241419 = 7862129) B7862129
theorem B3494279 : Blo 2069435 3494279 := bstep (se 1 (by rfl) ⟨2620709, by rfl⟩ : syracuseStep 3494279 = 5241419) B5241419
theorem B2329519 : Blo 2069435 2329519 := bstep (se 1 (by rfl) ⟨1747139, by rfl⟩ : syracuseStep 2329519 = 3494279) B3494279
theorem B3106025 : Blo 2069435 3106025 := bstep (se 2 (by rfl) ⟨1164759, by rfl⟩ : syracuseStep 3106025 = 2329519) B2329519
theorem B2070683 : Blo 2069435 2070683 := bstep (se 1 (by rfl) ⟨1553012, by rfl⟩ : syracuseStep 2070683 = 3106025) B3106025
theorem B4722613 : Blo 2069435 4722613 := bbase (se 5 (by rfl) ⟨221372, by rfl⟩ : syracuseStep 4722613 = 442745) (by norm_num)
theorem B25187269 : Blo 2069435 25187269 := bstep (se 4 (by rfl) ⟨2361306, by rfl⟩ : syracuseStep 25187269 = 4722613) B4722613
theorem B33583025 : Blo 2069435 33583025 := bstep (se 2 (by rfl) ⟨12593634, by rfl⟩ : syracuseStep 33583025 = 25187269) B25187269
theorem B89554733 : Blo 2069435 89554733 := bstep (se 3 (by rfl) ⟨16791512, by rfl⟩ : syracuseStep 89554733 = 33583025) B33583025
theorem B59703155 : Blo 2069435 59703155 := bstep (se 1 (by rfl) ⟨44777366, by rfl⟩ : syracuseStep 59703155 = 89554733) B89554733
theorem B39802103 : Blo 2069435 39802103 := bstep (se 1 (by rfl) ⟨29851577, by rfl⟩ : syracuseStep 39802103 = 59703155) B59703155
theorem B26534735 : Blo 2069435 26534735 := bstep (se 1 (by rfl) ⟨19901051, by rfl⟩ : syracuseStep 26534735 = 39802103) B39802103
theorem B17689823 : Blo 2069435 17689823 := bstep (se 1 (by rfl) ⟨13267367, by rfl⟩ : syracuseStep 17689823 = 26534735) B26534735
theorem B11793215 : Blo 2069435 11793215 := bstep (se 1 (by rfl) ⟨8844911, by rfl⟩ : syracuseStep 11793215 = 17689823) B17689823
theorem B7862143 : Blo 2069435 7862143 := bstep (se 1 (by rfl) ⟨5896607, by rfl⟩ : syracuseStep 7862143 = 11793215) B11793215
theorem B10482857 : Blo 2069435 10482857 := bstep (se 2 (by rfl) ⟨3931071, by rfl⟩ : syracuseStep 10482857 = 7862143) B7862143
theorem B6988571 : Blo 2069435 6988571 := bstep (se 1 (by rfl) ⟨5241428, by rfl⟩ : syracuseStep 6988571 = 10482857) B10482857
theorem B4659047 : Blo 2069435 4659047 := bstep (se 1 (by rfl) ⟨3494285, by rfl⟩ : syracuseStep 4659047 = 6988571) B6988571
theorem B3106031 : Blo 2069435 3106031 := bstep (se 1 (by rfl) ⟨2329523, by rfl⟩ : syracuseStep 3106031 = 4659047) B4659047
theorem B2070687 : Blo 2069435 2070687 := bstep (se 1 (by rfl) ⟨1553015, by rfl⟩ : syracuseStep 2070687 = 3106031) B3106031
theorem B3106037 : Blo 2069435 3106037 := bbase (se 5 (by rfl) ⟨145595, by rfl⟩ : syracuseStep 3106037 = 291191) (by norm_num)
theorem B2070691 : Blo 2069435 2070691 := bstep (se 1 (by rfl) ⟨1553018, by rfl⟩ : syracuseStep 2070691 = 3106037) B3106037
theorem B2798597 : Blo 2069435 2798597 := bbase (se 4 (by rfl) ⟨262368, by rfl⟩ : syracuseStep 2798597 = 524737) (by norm_num)
theorem B7462925 : Blo 2069435 7462925 := bstep (se 3 (by rfl) ⟨1399298, by rfl⟩ : syracuseStep 7462925 = 2798597) B2798597
theorem B4975283 : Blo 2069435 4975283 := bstep (se 1 (by rfl) ⟨3731462, by rfl⟩ : syracuseStep 4975283 = 7462925) B7462925
theorem B13267421 : Blo 2069435 13267421 := bstep (se 3 (by rfl) ⟨2487641, by rfl⟩ : syracuseStep 13267421 = 4975283) B4975283
theorem B8844947 : Blo 2069435 8844947 := bstep (se 1 (by rfl) ⟨6633710, by rfl⟩ : syracuseStep 8844947 = 13267421) B13267421
theorem B5896631 : Blo 2069435 5896631 := bstep (se 1 (by rfl) ⟨4422473, by rfl⟩ : syracuseStep 5896631 = 8844947) B8844947
theorem B3931087 : Blo 2069435 3931087 := bstep (se 1 (by rfl) ⟨2948315, by rfl⟩ : syracuseStep 3931087 = 5896631) B5896631
theorem B5241449 : Blo 2069435 5241449 := bstep (se 2 (by rfl) ⟨1965543, by rfl⟩ : syracuseStep 5241449 = 3931087) B3931087
theorem B3494299 : Blo 2069435 3494299 := bstep (se 1 (by rfl) ⟨2620724, by rfl⟩ : syracuseStep 3494299 = 5241449) B5241449
theorem B4659065 : Blo 2069435 4659065 := bstep (se 2 (by rfl) ⟨1747149, by rfl⟩ : syracuseStep 4659065 = 3494299) B3494299
theorem B3106043 : Blo 2069435 3106043 := bstep (se 1 (by rfl) ⟨2329532, by rfl⟩ : syracuseStep 3106043 = 4659065) B4659065
theorem B2070695 : Blo 2069435 2070695 := bstep (se 1 (by rfl) ⟨1553021, by rfl⟩ : syracuseStep 2070695 = 3106043) B3106043
theorem B2329537 : Blo 2069435 2329537 := bbase (se 2 (by rfl) ⟨873576, by rfl⟩ : syracuseStep 2329537 = 1747153) (by norm_num)
theorem B3106049 : Blo 2069435 3106049 := bstep (se 2 (by rfl) ⟨1164768, by rfl⟩ : syracuseStep 3106049 = 2329537) B2329537
theorem B2070699 : Blo 2069435 2070699 := bstep (se 1 (by rfl) ⟨1553024, by rfl⟩ : syracuseStep 2070699 = 3106049) B3106049
theorem B5241469 : Blo 2069435 5241469 := bbase (se 3 (by rfl) ⟨982775, by rfl⟩ : syracuseStep 5241469 = 1965551) (by norm_num)
theorem B6988625 : Blo 2069435 6988625 := bstep (se 2 (by rfl) ⟨2620734, by rfl⟩ : syracuseStep 6988625 = 5241469) B5241469
theorem B4659083 : Blo 2069435 4659083 := bstep (se 1 (by rfl) ⟨3494312, by rfl⟩ : syracuseStep 4659083 = 6988625) B6988625
theorem B3106055 : Blo 2069435 3106055 := bstep (se 1 (by rfl) ⟨2329541, by rfl⟩ : syracuseStep 3106055 = 4659083) B4659083
theorem B2070703 : Blo 2069435 2070703 := bstep (se 1 (by rfl) ⟨1553027, by rfl⟩ : syracuseStep 2070703 = 3106055) B3106055
theorem B3106061 : Blo 2069435 3106061 := bbase (se 3 (by rfl) ⟨582386, by rfl⟩ : syracuseStep 3106061 = 1164773) (by norm_num)
theorem B2070707 : Blo 2069435 2070707 := bstep (se 1 (by rfl) ⟨1553030, by rfl⟩ : syracuseStep 2070707 = 3106061) B3106061
theorem B4659101 : Blo 2069435 4659101 := bbase (se 3 (by rfl) ⟨873581, by rfl⟩ : syracuseStep 4659101 = 1747163) (by norm_num)
theorem B3106067 : Blo 2069435 3106067 := bstep (se 1 (by rfl) ⟨2329550, by rfl⟩ : syracuseStep 3106067 = 4659101) B4659101
theorem B2070711 : Blo 2069435 2070711 := bstep (se 1 (by rfl) ⟨1553033, by rfl⟩ : syracuseStep 2070711 = 3106067) B3106067
theorem B3494333 : Blo 2069435 3494333 := bbase (se 3 (by rfl) ⟨655187, by rfl⟩ : syracuseStep 3494333 = 1310375) (by norm_num)
theorem B2329555 : Blo 2069435 2329555 := bstep (se 1 (by rfl) ⟨1747166, by rfl⟩ : syracuseStep 2329555 = 3494333) B3494333
theorem B3106073 : Blo 2069435 3106073 := bstep (se 2 (by rfl) ⟨1164777, by rfl⟩ : syracuseStep 3106073 = 2329555) B2329555
theorem B2070715 : Blo 2069435 2070715 := bstep (se 1 (by rfl) ⟨1553036, by rfl⟩ : syracuseStep 2070715 = 3106073) B3106073
theorem B11793397 : Blo 2069435 11793397 := bbase (se 5 (by rfl) ⟨552815, by rfl⟩ : syracuseStep 11793397 = 1105631) (by norm_num)
theorem B15724529 : Blo 2069435 15724529 := bstep (se 2 (by rfl) ⟨5896698, by rfl⟩ : syracuseStep 15724529 = 11793397) B11793397
theorem B10483019 : Blo 2069435 10483019 := bstep (se 1 (by rfl) ⟨7862264, by rfl⟩ : syracuseStep 10483019 = 15724529) B15724529
theorem B6988679 : Blo 2069435 6988679 := bstep (se 1 (by rfl) ⟨5241509, by rfl⟩ : syracuseStep 6988679 = 10483019) B10483019
theorem B4659119 : Blo 2069435 4659119 := bstep (se 1 (by rfl) ⟨3494339, by rfl⟩ : syracuseStep 4659119 = 6988679) B6988679
theorem B3106079 : Blo 2069435 3106079 := bstep (se 1 (by rfl) ⟨2329559, by rfl⟩ : syracuseStep 3106079 = 4659119) B4659119
theorem B2070719 : Blo 2069435 2070719 := bstep (se 1 (by rfl) ⟨1553039, by rfl⟩ : syracuseStep 2070719 = 3106079) B3106079
theorem B3106085 : Blo 2069435 3106085 := bbase (se 4 (by rfl) ⟨291195, by rfl⟩ : syracuseStep 3106085 = 582391) (by norm_num)
theorem B2070723 : Blo 2069435 2070723 := bstep (se 1 (by rfl) ⟨1553042, by rfl⟩ : syracuseStep 2070723 = 3106085) B3106085
theorem B2620765 : Blo 2069435 2620765 := bbase (se 3 (by rfl) ⟨491393, by rfl⟩ : syracuseStep 2620765 = 982787) (by norm_num)
theorem B3494353 : Blo 2069435 3494353 := bstep (se 2 (by rfl) ⟨1310382, by rfl⟩ : syracuseStep 3494353 = 2620765) B2620765
theorem B4659137 : Blo 2069435 4659137 := bstep (se 2 (by rfl) ⟨1747176, by rfl⟩ : syracuseStep 4659137 = 3494353) B3494353
theorem B3106091 : Blo 2069435 3106091 := bstep (se 1 (by rfl) ⟨2329568, by rfl⟩ : syracuseStep 3106091 = 4659137) B4659137
theorem B2070727 : Blo 2069435 2070727 := bstep (se 1 (by rfl) ⟨1553045, by rfl⟩ : syracuseStep 2070727 = 3106091) B3106091
theorem B2329573 : Blo 2069435 2329573 := bbase (se 4 (by rfl) ⟨218397, by rfl⟩ : syracuseStep 2329573 = 436795) (by norm_num)
theorem B3106097 : Blo 2069435 3106097 := bstep (se 2 (by rfl) ⟨1164786, by rfl⟩ : syracuseStep 3106097 = 2329573) B2329573
theorem B2070731 : Blo 2069435 2070731 := bstep (se 1 (by rfl) ⟨1553048, by rfl⟩ : syracuseStep 2070731 = 3106097) B3106097
theorem B25187861 : Blo 2069435 25187861 := bbase (se 6 (by rfl) ⟨590340, by rfl⟩ : syracuseStep 25187861 = 1180681) (by norm_num)
theorem B16791907 : Blo 2069435 16791907 := bstep (se 1 (by rfl) ⟨12593930, by rfl⟩ : syracuseStep 16791907 = 25187861) B25187861
theorem B22389209 : Blo 2069435 22389209 := bstep (se 2 (by rfl) ⟨8395953, by rfl⟩ : syracuseStep 22389209 = 16791907) B16791907
theorem B14926139 : Blo 2069435 14926139 := bstep (se 1 (by rfl) ⟨11194604, by rfl⟩ : syracuseStep 14926139 = 22389209) B22389209
theorem B9950759 : Blo 2069435 9950759 := bstep (se 1 (by rfl) ⟨7463069, by rfl⟩ : syracuseStep 9950759 = 14926139) B14926139
theorem B6633839 : Blo 2069435 6633839 := bstep (se 1 (by rfl) ⟨4975379, by rfl⟩ : syracuseStep 6633839 = 9950759) B9950759
theorem B4422559 : Blo 2069435 4422559 := bstep (se 1 (by rfl) ⟨3316919, by rfl⟩ : syracuseStep 4422559 = 6633839) B6633839
theorem B5896745 : Blo 2069435 5896745 := bstep (se 2 (by rfl) ⟨2211279, by rfl⟩ : syracuseStep 5896745 = 4422559) B4422559
theorem B3931163 : Blo 2069435 3931163 := bstep (se 1 (by rfl) ⟨2948372, by rfl⟩ : syracuseStep 3931163 = 5896745) B5896745
theorem B2620775 : Blo 2069435 2620775 := bstep (se 1 (by rfl) ⟨1965581, by rfl⟩ : syracuseStep 2620775 = 3931163) B3931163
theorem B6988733 : Blo 2069435 6988733 := bstep (se 3 (by rfl) ⟨1310387, by rfl⟩ : syracuseStep 6988733 = 2620775) B2620775
theorem B4659155 : Blo 2069435 4659155 := bstep (se 1 (by rfl) ⟨3494366, by rfl⟩ : syracuseStep 4659155 = 6988733) B6988733
theorem B3106103 : Blo 2069435 3106103 := bstep (se 1 (by rfl) ⟨2329577, by rfl⟩ : syracuseStep 3106103 = 4659155) B4659155
theorem B2070735 : Blo 2069435 2070735 := bstep (se 1 (by rfl) ⟨1553051, by rfl⟩ : syracuseStep 2070735 = 3106103) B3106103
theorem B3106109 : Blo 2069435 3106109 := bbase (se 3 (by rfl) ⟨582395, by rfl⟩ : syracuseStep 3106109 = 1164791) (by norm_num)
theorem B2070739 : Blo 2069435 2070739 := bstep (se 1 (by rfl) ⟨1553054, by rfl⟩ : syracuseStep 2070739 = 3106109) B3106109
theorem B4659173 : Blo 2069435 4659173 := bbase (se 4 (by rfl) ⟨436797, by rfl⟩ : syracuseStep 4659173 = 873595) (by norm_num)
theorem B3106115 : Blo 2069435 3106115 := bstep (se 1 (by rfl) ⟨2329586, by rfl⟩ : syracuseStep 3106115 = 4659173) B4659173
theorem B2070743 : Blo 2069435 2070743 := bstep (se 1 (by rfl) ⟨1553057, by rfl⟩ : syracuseStep 2070743 = 3106115) B3106115
theorem B5241581 : Blo 2069435 5241581 := bbase (se 3 (by rfl) ⟨982796, by rfl⟩ : syracuseStep 5241581 = 1965593) (by norm_num)
theorem B3494387 : Blo 2069435 3494387 := bstep (se 1 (by rfl) ⟨2620790, by rfl⟩ : syracuseStep 3494387 = 5241581) B5241581
theorem B2329591 : Blo 2069435 2329591 := bstep (se 1 (by rfl) ⟨1747193, by rfl⟩ : syracuseStep 2329591 = 3494387) B3494387
theorem B3106121 : Blo 2069435 3106121 := bstep (se 2 (by rfl) ⟨1164795, by rfl⟩ : syracuseStep 3106121 = 2329591) B2329591
theorem B2070747 : Blo 2069435 2070747 := bstep (se 1 (by rfl) ⟨1553060, by rfl⟩ : syracuseStep 2070747 = 3106121) B3106121
theorem B2487709 : Blo 2069435 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B3316945 : Blo 2069435 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B4422593 : Blo 2069435 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B2948395 : Blo 2069435 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B3931193 : Blo 2069435 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B10483181 : Blo 2069435 10483181 := bstep (se 3 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 10483181 = 3931193) B3931193
theorem B6988787 : Blo 2069435 6988787 := bstep (se 1 (by rfl) ⟨5241590, by rfl⟩ : syracuseStep 6988787 = 10483181) B10483181
theorem B4659191 : Blo 2069435 4659191 := bstep (se 1 (by rfl) ⟨3494393, by rfl⟩ : syracuseStep 4659191 = 6988787) B6988787
theorem B3106127 : Blo 2069435 3106127 := bstep (se 1 (by rfl) ⟨2329595, by rfl⟩ : syracuseStep 3106127 = 4659191) B4659191
theorem B2070751 : Blo 2069435 2070751 := bstep (se 1 (by rfl) ⟨1553063, by rfl⟩ : syracuseStep 2070751 = 3106127) B3106127
theorem B3106133 : Blo 2069435 3106133 := bbase (se 12 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 3106133 = 2275) (by norm_num)
theorem B2070755 : Blo 2069435 2070755 := bstep (se 1 (by rfl) ⟨1553066, by rfl⟩ : syracuseStep 2070755 = 3106133) B3106133
theorem B2211305 : Blo 2069435 2211305 := bbase (se 2 (by rfl) ⟨829239, by rfl⟩ : syracuseStep 2211305 = 1658479) (by norm_num)
theorem B5896813 : Blo 2069435 5896813 := bstep (se 3 (by rfl) ⟨1105652, by rfl⟩ : syracuseStep 5896813 = 2211305) B2211305
theorem B7862417 : Blo 2069435 7862417 := bstep (se 2 (by rfl) ⟨2948406, by rfl⟩ : syracuseStep 7862417 = 5896813) B5896813
theorem B5241611 : Blo 2069435 5241611 := bstep (se 1 (by rfl) ⟨3931208, by rfl⟩ : syracuseStep 5241611 = 7862417) B7862417
theorem B3494407 : Blo 2069435 3494407 := bstep (se 1 (by rfl) ⟨2620805, by rfl⟩ : syracuseStep 3494407 = 5241611) B5241611
theorem B4659209 : Blo 2069435 4659209 := bstep (se 2 (by rfl) ⟨1747203, by rfl⟩ : syracuseStep 4659209 = 3494407) B3494407
theorem B3106139 : Blo 2069435 3106139 := bstep (se 1 (by rfl) ⟨2329604, by rfl⟩ : syracuseStep 3106139 = 4659209) B4659209
theorem B2070759 : Blo 2069435 2070759 := bstep (se 1 (by rfl) ⟨1553069, by rfl⟩ : syracuseStep 2070759 = 3106139) B3106139
theorem B2329609 : Blo 2069435 2329609 := bbase (se 2 (by rfl) ⟨873603, by rfl⟩ : syracuseStep 2329609 = 1747207) (by norm_num)
theorem B3106145 : Blo 2069435 3106145 := bstep (se 2 (by rfl) ⟨1164804, by rfl⟩ : syracuseStep 3106145 = 2329609) B2329609
theorem B2070763 : Blo 2069435 2070763 := bstep (se 1 (by rfl) ⟨1553072, by rfl⟩ : syracuseStep 2070763 = 3106145) B3106145
theorem B25188245 : Blo 2069435 25188245 := bbase (se 6 (by rfl) ⟨590349, by rfl⟩ : syracuseStep 25188245 = 1180699) (by norm_num)
theorem B16792163 : Blo 2069435 16792163 := bstep (se 1 (by rfl) ⟨12594122, by rfl⟩ : syracuseStep 16792163 = 25188245) B25188245
theorem B11194775 : Blo 2069435 11194775 := bstep (se 1 (by rfl) ⟨8396081, by rfl⟩ : syracuseStep 11194775 = 16792163) B16792163
theorem B7463183 : Blo 2069435 7463183 := bstep (se 1 (by rfl) ⟨5597387, by rfl⟩ : syracuseStep 7463183 = 11194775) B11194775
theorem B19901821 : Blo 2069435 19901821 := bstep (se 3 (by rfl) ⟨3731591, by rfl⟩ : syracuseStep 19901821 = 7463183) B7463183
theorem B26535761 : Blo 2069435 26535761 := bstep (se 2 (by rfl) ⟨9950910, by rfl⟩ : syracuseStep 26535761 = 19901821) B19901821
theorem B17690507 : Blo 2069435 17690507 := bstep (se 1 (by rfl) ⟨13267880, by rfl⟩ : syracuseStep 17690507 = 26535761) B26535761
theorem B11793671 : Blo 2069435 11793671 := bstep (se 1 (by rfl) ⟨8845253, by rfl⟩ : syracuseStep 11793671 = 17690507) B17690507
theorem B7862447 : Blo 2069435 7862447 := bstep (se 1 (by rfl) ⟨5896835, by rfl⟩ : syracuseStep 7862447 = 11793671) B11793671
theorem B5241631 : Blo 2069435 5241631 := bstep (se 1 (by rfl) ⟨3931223, by rfl⟩ : syracuseStep 5241631 = 7862447) B7862447
theorem B6988841 : Blo 2069435 6988841 := bstep (se 2 (by rfl) ⟨2620815, by rfl⟩ : syracuseStep 6988841 = 5241631) B5241631
theorem B4659227 : Blo 2069435 4659227 := bstep (se 1 (by rfl) ⟨3494420, by rfl⟩ : syracuseStep 4659227 = 6988841) B6988841
theorem B3106151 : Blo 2069435 3106151 := bstep (se 1 (by rfl) ⟨2329613, by rfl⟩ : syracuseStep 3106151 = 4659227) B4659227
theorem B2070767 : Blo 2069435 2070767 := bstep (se 1 (by rfl) ⟨1553075, by rfl⟩ : syracuseStep 2070767 = 3106151) B3106151
theorem B3106157 : Blo 2069435 3106157 := bbase (se 3 (by rfl) ⟨582404, by rfl⟩ : syracuseStep 3106157 = 1164809) (by norm_num)
theorem B2070771 : Blo 2069435 2070771 := bstep (se 1 (by rfl) ⟨1553078, by rfl⟩ : syracuseStep 2070771 = 3106157) B3106157
theorem B4659245 : Blo 2069435 4659245 := bbase (se 3 (by rfl) ⟨873608, by rfl⟩ : syracuseStep 4659245 = 1747217) (by norm_num)
theorem B3106163 : Blo 2069435 3106163 := bstep (se 1 (by rfl) ⟨2329622, by rfl⟩ : syracuseStep 3106163 = 4659245) B4659245
theorem B2070775 : Blo 2069435 2070775 := bstep (se 1 (by rfl) ⟨1553081, by rfl⟩ : syracuseStep 2070775 = 3106163) B3106163
theorem B2656589 : Blo 2069435 2656589 := bbase (se 3 (by rfl) ⟨498110, by rfl⟩ : syracuseStep 2656589 = 996221) (by norm_num)
theorem B28336949 : Blo 2069435 28336949 := bstep (se 5 (by rfl) ⟨1328294, by rfl⟩ : syracuseStep 28336949 = 2656589) B2656589
theorem B18891299 : Blo 2069435 18891299 := bstep (se 1 (by rfl) ⟨14168474, by rfl⟩ : syracuseStep 18891299 = 28336949) B28336949
theorem B12594199 : Blo 2069435 12594199 := bstep (se 1 (by rfl) ⟨9445649, by rfl⟩ : syracuseStep 12594199 = 18891299) B18891299
theorem B16792265 : Blo 2069435 16792265 := bstep (se 2 (by rfl) ⟨6297099, by rfl⟩ : syracuseStep 16792265 = 12594199) B12594199
theorem B11194843 : Blo 2069435 11194843 := bstep (se 1 (by rfl) ⟨8396132, by rfl⟩ : syracuseStep 11194843 = 16792265) B16792265
theorem B14926457 : Blo 2069435 14926457 := bstep (se 2 (by rfl) ⟨5597421, by rfl⟩ : syracuseStep 14926457 = 11194843) B11194843
theorem B9950971 : Blo 2069435 9950971 := bstep (se 1 (by rfl) ⟨7463228, by rfl⟩ : syracuseStep 9950971 = 14926457) B14926457
theorem B13267961 : Blo 2069435 13267961 := bstep (se 2 (by rfl) ⟨4975485, by rfl⟩ : syracuseStep 13267961 = 9950971) B9950971
theorem B8845307 : Blo 2069435 8845307 := bstep (se 1 (by rfl) ⟨6633980, by rfl⟩ : syracuseStep 8845307 = 13267961) B13267961
theorem B5896871 : Blo 2069435 5896871 := bstep (se 1 (by rfl) ⟨4422653, by rfl⟩ : syracuseStep 5896871 = 8845307) B8845307
theorem B3931247 : Blo 2069435 3931247 := bstep (se 1 (by rfl) ⟨2948435, by rfl⟩ : syracuseStep 3931247 = 5896871) B5896871
theorem B2620831 : Blo 2069435 2620831 := bstep (se 1 (by rfl) ⟨1965623, by rfl⟩ : syracuseStep 2620831 = 3931247) B3931247
theorem B3494441 : Blo 2069435 3494441 := bstep (se 2 (by rfl) ⟨1310415, by rfl⟩ : syracuseStep 3494441 = 2620831) B2620831
theorem B2329627 : Blo 2069435 2329627 := bstep (se 1 (by rfl) ⟨1747220, by rfl⟩ : syracuseStep 2329627 = 3494441) B3494441
theorem B3106169 : Blo 2069435 3106169 := bstep (se 2 (by rfl) ⟨1164813, by rfl⟩ : syracuseStep 3106169 = 2329627) B2329627
theorem B2070779 : Blo 2069435 2070779 := bstep (se 1 (by rfl) ⟨1553084, by rfl⟩ : syracuseStep 2070779 = 3106169) B3106169
theorem B3542125 : Blo 2069435 3542125 := bbase (se 3 (by rfl) ⟨664148, by rfl⟩ : syracuseStep 3542125 = 1328297) (by norm_num)
theorem B4722833 : Blo 2069435 4722833 := bstep (se 2 (by rfl) ⟨1771062, by rfl⟩ : syracuseStep 4722833 = 3542125) B3542125
theorem B3148555 : Blo 2069435 3148555 := bstep (se 1 (by rfl) ⟨2361416, by rfl⟩ : syracuseStep 3148555 = 4722833) B4722833
theorem B4198073 : Blo 2069435 4198073 := bstep (se 2 (by rfl) ⟨1574277, by rfl⟩ : syracuseStep 4198073 = 3148555) B3148555
theorem B11194861 : Blo 2069435 11194861 := bstep (se 3 (by rfl) ⟨2099036, by rfl⟩ : syracuseStep 11194861 = 4198073) B4198073
theorem B14926481 : Blo 2069435 14926481 := bstep (se 2 (by rfl) ⟨5597430, by rfl⟩ : syracuseStep 14926481 = 11194861) B11194861
theorem B9950987 : Blo 2069435 9950987 := bstep (se 1 (by rfl) ⟨7463240, by rfl⟩ : syracuseStep 9950987 = 14926481) B14926481
theorem B6633991 : Blo 2069435 6633991 := bstep (se 1 (by rfl) ⟨4975493, by rfl⟩ : syracuseStep 6633991 = 9950987) B9950987
theorem B35381285 : Blo 2069435 35381285 := bstep (se 4 (by rfl) ⟨3316995, by rfl⟩ : syracuseStep 35381285 = 6633991) B6633991
theorem B23587523 : Blo 2069435 23587523 := bstep (se 1 (by rfl) ⟨17690642, by rfl⟩ : syracuseStep 23587523 = 35381285) B35381285
theorem B15725015 : Blo 2069435 15725015 := bstep (se 1 (by rfl) ⟨11793761, by rfl⟩ : syracuseStep 15725015 = 23587523) B23587523
theorem B10483343 : Blo 2069435 10483343 := bstep (se 1 (by rfl) ⟨7862507, by rfl⟩ : syracuseStep 10483343 = 15725015) B15725015
theorem B6988895 : Blo 2069435 6988895 := bstep (se 1 (by rfl) ⟨5241671, by rfl⟩ : syracuseStep 6988895 = 10483343) B10483343
theorem B4659263 : Blo 2069435 4659263 := bstep (se 1 (by rfl) ⟨3494447, by rfl⟩ : syracuseStep 4659263 = 6988895) B6988895
theorem B3106175 : Blo 2069435 3106175 := bstep (se 1 (by rfl) ⟨2329631, by rfl⟩ : syracuseStep 3106175 = 4659263) B4659263
theorem B2070783 : Blo 2069435 2070783 := bstep (se 1 (by rfl) ⟨1553087, by rfl⟩ : syracuseStep 2070783 = 3106175) B3106175
theorem B3106181 : Blo 2069435 3106181 := bbase (se 4 (by rfl) ⟨291204, by rfl⟩ : syracuseStep 3106181 = 582409) (by norm_num)
theorem B2070787 : Blo 2069435 2070787 := bstep (se 1 (by rfl) ⟨1553090, by rfl⟩ : syracuseStep 2070787 = 3106181) B3106181
theorem B3494461 : Blo 2069435 3494461 := bbase (se 3 (by rfl) ⟨655211, by rfl⟩ : syracuseStep 3494461 = 1310423) (by norm_num)
theorem B4659281 : Blo 2069435 4659281 := bstep (se 2 (by rfl) ⟨1747230, by rfl⟩ : syracuseStep 4659281 = 3494461) B3494461
theorem B3106187 : Blo 2069435 3106187 := bstep (se 1 (by rfl) ⟨2329640, by rfl⟩ : syracuseStep 3106187 = 4659281) B4659281
theorem B2070791 : Blo 2069435 2070791 := bstep (se 1 (by rfl) ⟨1553093, by rfl⟩ : syracuseStep 2070791 = 3106187) B3106187
theorem B2329645 : Blo 2069435 2329645 := bbase (se 3 (by rfl) ⟨436808, by rfl⟩ : syracuseStep 2329645 = 873617) (by norm_num)
theorem B3106193 : Blo 2069435 3106193 := bstep (se 2 (by rfl) ⟨1164822, by rfl⟩ : syracuseStep 3106193 = 2329645) B2329645
theorem B2070795 : Blo 2069435 2070795 := bstep (se 1 (by rfl) ⟨1553096, by rfl⟩ : syracuseStep 2070795 = 3106193) B3106193
theorem B6988949 : Blo 2069435 6988949 := bbase (se 6 (by rfl) ⟨163803, by rfl⟩ : syracuseStep 6988949 = 327607) (by norm_num)
theorem B4659299 : Blo 2069435 4659299 := bstep (se 1 (by rfl) ⟨3494474, by rfl⟩ : syracuseStep 4659299 = 6988949) B6988949
theorem B3106199 : Blo 2069435 3106199 := bstep (se 1 (by rfl) ⟨2329649, by rfl⟩ : syracuseStep 3106199 = 4659299) B4659299
theorem B2070799 : Blo 2069435 2070799 := bstep (se 1 (by rfl) ⟨1553099, by rfl⟩ : syracuseStep 2070799 = 3106199) B3106199
theorem B3106205 : Blo 2069435 3106205 := bbase (se 3 (by rfl) ⟨582413, by rfl⟩ : syracuseStep 3106205 = 1164827) (by norm_num)
theorem B2070803 : Blo 2069435 2070803 := bstep (se 1 (by rfl) ⟨1553102, by rfl⟩ : syracuseStep 2070803 = 3106205) B3106205
theorem B4659317 : Blo 2069435 4659317 := bbase (se 5 (by rfl) ⟨218405, by rfl⟩ : syracuseStep 4659317 = 436811) (by norm_num)
theorem B3106211 : Blo 2069435 3106211 := bstep (se 1 (by rfl) ⟨2329658, by rfl⟩ : syracuseStep 3106211 = 4659317) B4659317
theorem B2070807 : Blo 2069435 2070807 := bstep (se 1 (by rfl) ⟨1553105, by rfl⟩ : syracuseStep 2070807 = 3106211) B3106211
theorem B2487781 : Blo 2069435 2487781 := bbase (se 4 (by rfl) ⟨233229, by rfl⟩ : syracuseStep 2487781 = 466459) (by norm_num)
theorem B3317041 : Blo 2069435 3317041 := bstep (se 2 (by rfl) ⟨1243890, by rfl⟩ : syracuseStep 3317041 = 2487781) B2487781
theorem B17690885 : Blo 2069435 17690885 := bstep (se 4 (by rfl) ⟨1658520, by rfl⟩ : syracuseStep 17690885 = 3317041) B3317041
theorem B11793923 : Blo 2069435 11793923 := bstep (se 1 (by rfl) ⟨8845442, by rfl⟩ : syracuseStep 11793923 = 17690885) B17690885
theorem B7862615 : Blo 2069435 7862615 := bstep (se 1 (by rfl) ⟨5896961, by rfl⟩ : syracuseStep 7862615 = 11793923) B11793923
theorem B5241743 : Blo 2069435 5241743 := bstep (se 1 (by rfl) ⟨3931307, by rfl⟩ : syracuseStep 5241743 = 7862615) B7862615
theorem B3494495 : Blo 2069435 3494495 := bstep (se 1 (by rfl) ⟨2620871, by rfl⟩ : syracuseStep 3494495 = 5241743) B5241743
theorem B2329663 : Blo 2069435 2329663 := bstep (se 1 (by rfl) ⟨1747247, by rfl⟩ : syracuseStep 2329663 = 3494495) B3494495
theorem B3106217 : Blo 2069435 3106217 := bstep (se 2 (by rfl) ⟨1164831, by rfl⟩ : syracuseStep 3106217 = 2329663) B2329663
theorem B2070811 : Blo 2069435 2070811 := bstep (se 1 (by rfl) ⟨1553108, by rfl⟩ : syracuseStep 2070811 = 3106217) B3106217
theorem B7862629 : Blo 2069435 7862629 := bbase (se 4 (by rfl) ⟨737121, by rfl⟩ : syracuseStep 7862629 = 1474243) (by norm_num)
theorem B10483505 : Blo 2069435 10483505 := bstep (se 2 (by rfl) ⟨3931314, by rfl⟩ : syracuseStep 10483505 = 7862629) B7862629
theorem B6989003 : Blo 2069435 6989003 := bstep (se 1 (by rfl) ⟨5241752, by rfl⟩ : syracuseStep 6989003 = 10483505) B10483505
theorem B4659335 : Blo 2069435 4659335 := bstep (se 1 (by rfl) ⟨3494501, by rfl⟩ : syracuseStep 4659335 = 6989003) B6989003
theorem B3106223 : Blo 2069435 3106223 := bstep (se 1 (by rfl) ⟨2329667, by rfl⟩ : syracuseStep 3106223 = 4659335) B4659335
theorem B2070815 : Blo 2069435 2070815 := bstep (se 1 (by rfl) ⟨1553111, by rfl⟩ : syracuseStep 2070815 = 3106223) B3106223
theorem B3106229 : Blo 2069435 3106229 := bbase (se 5 (by rfl) ⟨145604, by rfl⟩ : syracuseStep 3106229 = 291209) (by norm_num)
theorem B2070819 : Blo 2069435 2070819 := bstep (se 1 (by rfl) ⟨1553114, by rfl⟩ : syracuseStep 2070819 = 3106229) B3106229
theorem B5241773 : Blo 2069435 5241773 := bbase (se 3 (by rfl) ⟨982832, by rfl⟩ : syracuseStep 5241773 = 1965665) (by norm_num)
theorem B3494515 : Blo 2069435 3494515 := bstep (se 1 (by rfl) ⟨2620886, by rfl⟩ : syracuseStep 3494515 = 5241773) B5241773
theorem B4659353 : Blo 2069435 4659353 := bstep (se 2 (by rfl) ⟨1747257, by rfl⟩ : syracuseStep 4659353 = 3494515) B3494515
theorem B3106235 : Blo 2069435 3106235 := bstep (se 1 (by rfl) ⟨2329676, by rfl⟩ : syracuseStep 3106235 = 4659353) B4659353
theorem B2070823 : Blo 2069435 2070823 := bstep (se 1 (by rfl) ⟨1553117, by rfl⟩ : syracuseStep 2070823 = 3106235) B3106235
theorem B2329681 : Blo 2069435 2329681 := bbase (se 2 (by rfl) ⟨873630, by rfl⟩ : syracuseStep 2329681 = 1747261) (by norm_num)
theorem B3106241 : Blo 2069435 3106241 := bstep (se 2 (by rfl) ⟨1164840, by rfl⟩ : syracuseStep 3106241 = 2329681) B2329681
theorem B2070827 : Blo 2069435 2070827 := bstep (se 1 (by rfl) ⟨1553120, by rfl⟩ : syracuseStep 2070827 = 3106241) B3106241
theorem B2948509 : Blo 2069435 2948509 := bbase (se 3 (by rfl) ⟨552845, by rfl⟩ : syracuseStep 2948509 = 1105691) (by norm_num)
theorem B3931345 : Blo 2069435 3931345 := bstep (se 2 (by rfl) ⟨1474254, by rfl⟩ : syracuseStep 3931345 = 2948509) B2948509
theorem B5241793 : Blo 2069435 5241793 := bstep (se 2 (by rfl) ⟨1965672, by rfl⟩ : syracuseStep 5241793 = 3931345) B3931345
theorem B6989057 : Blo 2069435 6989057 := bstep (se 2 (by rfl) ⟨2620896, by rfl⟩ : syracuseStep 6989057 = 5241793) B5241793
theorem B4659371 : Blo 2069435 4659371 := bstep (se 1 (by rfl) ⟨3494528, by rfl⟩ : syracuseStep 4659371 = 6989057) B6989057
theorem B3106247 : Blo 2069435 3106247 := bstep (se 1 (by rfl) ⟨2329685, by rfl⟩ : syracuseStep 3106247 = 4659371) B4659371
theorem B2070831 : Blo 2069435 2070831 := bstep (se 1 (by rfl) ⟨1553123, by rfl⟩ : syracuseStep 2070831 = 3106247) B3106247
theorem B3106253 : Blo 2069435 3106253 := bbase (se 3 (by rfl) ⟨582422, by rfl⟩ : syracuseStep 3106253 = 1164845) (by norm_num)
theorem B2070835 : Blo 2069435 2070835 := bstep (se 1 (by rfl) ⟨1553126, by rfl⟩ : syracuseStep 2070835 = 3106253) B3106253
theorem B4659389 : Blo 2069435 4659389 := bbase (se 3 (by rfl) ⟨873635, by rfl⟩ : syracuseStep 4659389 = 1747271) (by norm_num)
theorem B3106259 : Blo 2069435 3106259 := bstep (se 1 (by rfl) ⟨2329694, by rfl⟩ : syracuseStep 3106259 = 4659389) B4659389
theorem B2070839 : Blo 2069435 2070839 := bstep (se 1 (by rfl) ⟨1553129, by rfl⟩ : syracuseStep 2070839 = 3106259) B3106259
theorem B3494549 : Blo 2069435 3494549 := bbase (se 6 (by rfl) ⟨81903, by rfl⟩ : syracuseStep 3494549 = 163807) (by norm_num)
theorem B2329699 : Blo 2069435 2329699 := bstep (se 1 (by rfl) ⟨1747274, by rfl⟩ : syracuseStep 2329699 = 3494549) B3494549
theorem B3106265 : Blo 2069435 3106265 := bstep (se 2 (by rfl) ⟨1164849, by rfl⟩ : syracuseStep 3106265 = 2329699) B2329699
theorem B2070843 : Blo 2069435 2070843 := bstep (se 1 (by rfl) ⟨1553132, by rfl⟩ : syracuseStep 2070843 = 3106265) B3106265
theorem B3408229 : Blo 2069435 3408229 := bbase (se 4 (by rfl) ⟨319521, by rfl⟩ : syracuseStep 3408229 = 639043) (by norm_num)
theorem B4544305 : Blo 2069435 4544305 := bstep (se 2 (by rfl) ⟨1704114, by rfl⟩ : syracuseStep 4544305 = 3408229) B3408229
theorem B24236293 : Blo 2069435 24236293 := bstep (se 4 (by rfl) ⟨2272152, by rfl⟩ : syracuseStep 24236293 = 4544305) B4544305
theorem B32315057 : Blo 2069435 32315057 := bstep (se 2 (by rfl) ⟨12118146, by rfl⟩ : syracuseStep 32315057 = 24236293) B24236293
theorem B21543371 : Blo 2069435 21543371 := bstep (se 1 (by rfl) ⟨16157528, by rfl⟩ : syracuseStep 21543371 = 32315057) B32315057
theorem B14362247 : Blo 2069435 14362247 := bstep (se 1 (by rfl) ⟨10771685, by rfl⟩ : syracuseStep 14362247 = 21543371) B21543371
theorem B38299325 : Blo 2069435 38299325 := bstep (se 3 (by rfl) ⟨7181123, by rfl⟩ : syracuseStep 38299325 = 14362247) B14362247
theorem B102131533 : Blo 2069435 102131533 := bstep (se 3 (by rfl) ⟨19149662, by rfl⟩ : syracuseStep 102131533 = 38299325) B38299325
theorem B136175377 : Blo 2069435 136175377 := bstep (se 2 (by rfl) ⟨51065766, by rfl⟩ : syracuseStep 136175377 = 102131533) B102131533
theorem B181567169 : Blo 2069435 181567169 := bstep (se 2 (by rfl) ⟨68087688, by rfl⟩ : syracuseStep 181567169 = 136175377) B136175377
theorem B121044779 : Blo 2069435 121044779 := bstep (se 1 (by rfl) ⟨90783584, by rfl⟩ : syracuseStep 121044779 = 181567169) B181567169
theorem B80696519 : Blo 2069435 80696519 := bstep (se 1 (by rfl) ⟨60522389, by rfl⟩ : syracuseStep 80696519 = 121044779) B121044779
theorem B53797679 : Blo 2069435 53797679 := bstep (se 1 (by rfl) ⟨40348259, by rfl⟩ : syracuseStep 53797679 = 80696519) B80696519
theorem B35865119 : Blo 2069435 35865119 := bstep (se 1 (by rfl) ⟨26898839, by rfl⟩ : syracuseStep 35865119 = 53797679) B53797679
theorem B23910079 : Blo 2069435 23910079 := bstep (se 1 (by rfl) ⟨17932559, by rfl⟩ : syracuseStep 23910079 = 35865119) B35865119
theorem B31880105 : Blo 2069435 31880105 := bstep (se 2 (by rfl) ⟨11955039, by rfl⟩ : syracuseStep 31880105 = 23910079) B23910079
theorem B21253403 : Blo 2069435 21253403 := bstep (se 1 (by rfl) ⟨15940052, by rfl⟩ : syracuseStep 21253403 = 31880105) B31880105
theorem B14168935 : Blo 2069435 14168935 := bstep (se 1 (by rfl) ⟨10626701, by rfl⟩ : syracuseStep 14168935 = 21253403) B21253403
theorem B75567653 : Blo 2069435 75567653 := bstep (se 4 (by rfl) ⟨7084467, by rfl⟩ : syracuseStep 75567653 = 14168935) B14168935
theorem B50378435 : Blo 2069435 50378435 := bstep (se 1 (by rfl) ⟨37783826, by rfl⟩ : syracuseStep 50378435 = 75567653) B75567653
theorem B33585623 : Blo 2069435 33585623 := bstep (se 1 (by rfl) ⟨25189217, by rfl⟩ : syracuseStep 33585623 = 50378435) B50378435
theorem B22390415 : Blo 2069435 22390415 := bstep (se 1 (by rfl) ⟨16792811, by rfl⟩ : syracuseStep 22390415 = 33585623) B33585623
theorem B14926943 : Blo 2069435 14926943 := bstep (se 1 (by rfl) ⟨11195207, by rfl⟩ : syracuseStep 14926943 = 22390415) B22390415
theorem B9951295 : Blo 2069435 9951295 := bstep (se 1 (by rfl) ⟨7463471, by rfl⟩ : syracuseStep 9951295 = 14926943) B14926943
theorem B13268393 : Blo 2069435 13268393 := bstep (se 2 (by rfl) ⟨4975647, by rfl⟩ : syracuseStep 13268393 = 9951295) B9951295
theorem B8845595 : Blo 2069435 8845595 := bstep (se 1 (by rfl) ⟨6634196, by rfl⟩ : syracuseStep 8845595 = 13268393) B13268393
theorem B5897063 : Blo 2069435 5897063 := bstep (se 1 (by rfl) ⟨4422797, by rfl⟩ : syracuseStep 5897063 = 8845595) B8845595
theorem B15725501 : Blo 2069435 15725501 := bstep (se 3 (by rfl) ⟨2948531, by rfl⟩ : syracuseStep 15725501 = 5897063) B5897063
theorem B10483667 : Blo 2069435 10483667 := bstep (se 1 (by rfl) ⟨7862750, by rfl⟩ : syracuseStep 10483667 = 15725501) B15725501
theorem B6989111 : Blo 2069435 6989111 := bstep (se 1 (by rfl) ⟨5241833, by rfl⟩ : syracuseStep 6989111 = 10483667) B10483667
theorem B4659407 : Blo 2069435 4659407 := bstep (se 1 (by rfl) ⟨3494555, by rfl⟩ : syracuseStep 4659407 = 6989111) B6989111
theorem B3106271 : Blo 2069435 3106271 := bstep (se 1 (by rfl) ⟨2329703, by rfl⟩ : syracuseStep 3106271 = 4659407) B4659407
theorem B2070847 : Blo 2069435 2070847 := bstep (se 1 (by rfl) ⟨1553135, by rfl⟩ : syracuseStep 2070847 = 3106271) B3106271
theorem B3106277 : Blo 2069435 3106277 := bbase (se 4 (by rfl) ⟨291213, by rfl⟩ : syracuseStep 3106277 = 582427) (by norm_num)
theorem B2070851 : Blo 2069435 2070851 := bstep (se 1 (by rfl) ⟨1553138, by rfl⟩ : syracuseStep 2070851 = 3106277) B3106277
theorem B14756885 : Blo 2069435 14756885 := bbase (se 6 (by rfl) ⟨345864, by rfl⟩ : syracuseStep 14756885 = 691729) (by norm_num)
theorem B157406773 : Blo 2069435 157406773 := bstep (se 5 (by rfl) ⟨7378442, by rfl⟩ : syracuseStep 157406773 = 14756885) B14756885
theorem B209875697 : Blo 2069435 209875697 := bstep (se 2 (by rfl) ⟨78703386, by rfl⟩ : syracuseStep 209875697 = 157406773) B157406773
theorem B139917131 : Blo 2069435 139917131 := bstep (se 1 (by rfl) ⟨104937848, by rfl⟩ : syracuseStep 139917131 = 209875697) B209875697
theorem B93278087 : Blo 2069435 93278087 := bstep (se 1 (by rfl) ⟨69958565, by rfl⟩ : syracuseStep 93278087 = 139917131) B139917131
theorem B62185391 : Blo 2069435 62185391 := bstep (se 1 (by rfl) ⟨46639043, by rfl⟩ : syracuseStep 62185391 = 93278087) B93278087
theorem B41456927 : Blo 2069435 41456927 := bstep (se 1 (by rfl) ⟨31092695, by rfl⟩ : syracuseStep 41456927 = 62185391) B62185391
theorem B27637951 : Blo 2069435 27637951 := bstep (se 1 (by rfl) ⟨20728463, by rfl⟩ : syracuseStep 27637951 = 41456927) B41456927
theorem B36850601 : Blo 2069435 36850601 := bstep (se 2 (by rfl) ⟨13818975, by rfl⟩ : syracuseStep 36850601 = 27637951) B27637951
theorem B24567067 : Blo 2069435 24567067 := bstep (se 1 (by rfl) ⟨18425300, by rfl⟩ : syracuseStep 24567067 = 36850601) B36850601
theorem B32756089 : Blo 2069435 32756089 := bstep (se 2 (by rfl) ⟨12283533, by rfl⟩ : syracuseStep 32756089 = 24567067) B24567067
theorem B43674785 : Blo 2069435 43674785 := bstep (se 2 (by rfl) ⟨16378044, by rfl⟩ : syracuseStep 43674785 = 32756089) B32756089
theorem B29116523 : Blo 2069435 29116523 := bstep (se 1 (by rfl) ⟨21837392, by rfl⟩ : syracuseStep 29116523 = 43674785) B43674785
theorem B19411015 : Blo 2069435 19411015 := bstep (se 1 (by rfl) ⟨14558261, by rfl⟩ : syracuseStep 19411015 = 29116523) B29116523
theorem B25881353 : Blo 2069435 25881353 := bstep (se 2 (by rfl) ⟨9705507, by rfl⟩ : syracuseStep 25881353 = 19411015) B19411015
theorem B17254235 : Blo 2069435 17254235 := bstep (se 1 (by rfl) ⟨12940676, by rfl⟩ : syracuseStep 17254235 = 25881353) B25881353
theorem B11502823 : Blo 2069435 11502823 := bstep (se 1 (by rfl) ⟨8627117, by rfl⟩ : syracuseStep 11502823 = 17254235) B17254235
theorem B15337097 : Blo 2069435 15337097 := bstep (se 2 (by rfl) ⟨5751411, by rfl⟩ : syracuseStep 15337097 = 11502823) B11502823
theorem B10224731 : Blo 2069435 10224731 := bstep (se 1 (by rfl) ⟨7668548, by rfl⟩ : syracuseStep 10224731 = 15337097) B15337097
theorem B6816487 : Blo 2069435 6816487 := bstep (se 1 (by rfl) ⟨5112365, by rfl⟩ : syracuseStep 6816487 = 10224731) B10224731
theorem B9088649 : Blo 2069435 9088649 := bstep (se 2 (by rfl) ⟨3408243, by rfl⟩ : syracuseStep 9088649 = 6816487) B6816487
theorem B6059099 : Blo 2069435 6059099 := bstep (se 1 (by rfl) ⟨4544324, by rfl⟩ : syracuseStep 6059099 = 9088649) B9088649
theorem B4039399 : Blo 2069435 4039399 := bstep (se 1 (by rfl) ⟨3029549, by rfl⟩ : syracuseStep 4039399 = 6059099) B6059099
theorem B5385865 : Blo 2069435 5385865 := bstep (se 2 (by rfl) ⟨2019699, by rfl⟩ : syracuseStep 5385865 = 4039399) B4039399
theorem B7181153 : Blo 2069435 7181153 := bstep (se 2 (by rfl) ⟨2692932, by rfl⟩ : syracuseStep 7181153 = 5385865) B5385865
theorem B4787435 : Blo 2069435 4787435 := bstep (se 1 (by rfl) ⟨3590576, by rfl⟩ : syracuseStep 4787435 = 7181153) B7181153
theorem B12766493 : Blo 2069435 12766493 := bstep (se 3 (by rfl) ⟨2393717, by rfl⟩ : syracuseStep 12766493 = 4787435) B4787435
theorem B34043981 : Blo 2069435 34043981 := bstep (se 3 (by rfl) ⟨6383246, by rfl⟩ : syracuseStep 34043981 = 12766493) B12766493
theorem B90783949 : Blo 2069435 90783949 := bstep (se 3 (by rfl) ⟨17021990, by rfl⟩ : syracuseStep 90783949 = 34043981) B34043981
theorem B121045265 : Blo 2069435 121045265 := bstep (se 2 (by rfl) ⟨45391974, by rfl⟩ : syracuseStep 121045265 = 90783949) B90783949
theorem B80696843 : Blo 2069435 80696843 := bstep (se 1 (by rfl) ⟨60522632, by rfl⟩ : syracuseStep 80696843 = 121045265) B121045265
theorem B53797895 : Blo 2069435 53797895 := bstep (se 1 (by rfl) ⟨40348421, by rfl⟩ : syracuseStep 53797895 = 80696843) B80696843
theorem B35865263 : Blo 2069435 35865263 := bstep (se 1 (by rfl) ⟨26898947, by rfl⟩ : syracuseStep 35865263 = 53797895) B53797895
theorem B23910175 : Blo 2069435 23910175 := bstep (se 1 (by rfl) ⟨17932631, by rfl⟩ : syracuseStep 23910175 = 35865263) B35865263
theorem B31880233 : Blo 2069435 31880233 := bstep (se 2 (by rfl) ⟨11955087, by rfl⟩ : syracuseStep 31880233 = 23910175) B23910175
theorem B42506977 : Blo 2069435 42506977 := bstep (se 2 (by rfl) ⟨15940116, by rfl⟩ : syracuseStep 42506977 = 31880233) B31880233
theorem B56675969 : Blo 2069435 56675969 := bstep (se 2 (by rfl) ⟨21253488, by rfl⟩ : syracuseStep 56675969 = 42506977) B42506977
theorem B37783979 : Blo 2069435 37783979 := bstep (se 1 (by rfl) ⟨28337984, by rfl⟩ : syracuseStep 37783979 = 56675969) B56675969
theorem B25189319 : Blo 2069435 25189319 := bstep (se 1 (by rfl) ⟨18891989, by rfl⟩ : syracuseStep 25189319 = 37783979) B37783979
theorem B67171517 : Blo 2069435 67171517 := bstep (se 3 (by rfl) ⟨12594659, by rfl⟩ : syracuseStep 67171517 = 25189319) B25189319
theorem B44781011 : Blo 2069435 44781011 := bstep (se 1 (by rfl) ⟨33585758, by rfl⟩ : syracuseStep 44781011 = 67171517) B67171517
theorem B29854007 : Blo 2069435 29854007 := bstep (se 1 (by rfl) ⟨22390505, by rfl⟩ : syracuseStep 29854007 = 44781011) B44781011
theorem B19902671 : Blo 2069435 19902671 := bstep (se 1 (by rfl) ⟨14927003, by rfl⟩ : syracuseStep 19902671 = 29854007) B29854007
theorem B13268447 : Blo 2069435 13268447 := bstep (se 1 (by rfl) ⟨9951335, by rfl⟩ : syracuseStep 13268447 = 19902671) B19902671
theorem B8845631 : Blo 2069435 8845631 := bstep (se 1 (by rfl) ⟨6634223, by rfl⟩ : syracuseStep 8845631 = 13268447) B13268447
theorem B5897087 : Blo 2069435 5897087 := bstep (se 1 (by rfl) ⟨4422815, by rfl⟩ : syracuseStep 5897087 = 8845631) B8845631
theorem B3931391 : Blo 2069435 3931391 := bstep (se 1 (by rfl) ⟨2948543, by rfl⟩ : syracuseStep 3931391 = 5897087) B5897087
theorem B2620927 : Blo 2069435 2620927 := bstep (se 1 (by rfl) ⟨1965695, by rfl⟩ : syracuseStep 2620927 = 3931391) B3931391
theorem B3494569 : Blo 2069435 3494569 := bstep (se 2 (by rfl) ⟨1310463, by rfl⟩ : syracuseStep 3494569 = 2620927) B2620927
theorem B4659425 : Blo 2069435 4659425 := bstep (se 2 (by rfl) ⟨1747284, by rfl⟩ : syracuseStep 4659425 = 3494569) B3494569
theorem B3106283 : Blo 2069435 3106283 := bstep (se 1 (by rfl) ⟨2329712, by rfl⟩ : syracuseStep 3106283 = 4659425) B4659425
theorem B2070855 : Blo 2069435 2070855 := bstep (se 1 (by rfl) ⟨1553141, by rfl⟩ : syracuseStep 2070855 = 3106283) B3106283
theorem B2329717 : Blo 2069435 2329717 := bbase (se 5 (by rfl) ⟨109205, by rfl⟩ : syracuseStep 2329717 = 218411) (by norm_num)
theorem B3106289 : Blo 2069435 3106289 := bstep (se 2 (by rfl) ⟨1164858, by rfl⟩ : syracuseStep 3106289 = 2329717) B2329717
theorem B2070859 : Blo 2069435 2070859 := bstep (se 1 (by rfl) ⟨1553144, by rfl⟩ : syracuseStep 2070859 = 3106289) B3106289
theorem B2620937 : Blo 2069435 2620937 := bbase (se 2 (by rfl) ⟨982851, by rfl⟩ : syracuseStep 2620937 = 1965703) (by norm_num)
theorem B6989165 : Blo 2069435 6989165 := bstep (se 3 (by rfl) ⟨1310468, by rfl⟩ : syracuseStep 6989165 = 2620937) B2620937
theorem B4659443 : Blo 2069435 4659443 := bstep (se 1 (by rfl) ⟨3494582, by rfl⟩ : syracuseStep 4659443 = 6989165) B6989165
theorem B3106295 : Blo 2069435 3106295 := bstep (se 1 (by rfl) ⟨2329721, by rfl⟩ : syracuseStep 3106295 = 4659443) B4659443
theorem B2070863 : Blo 2069435 2070863 := bstep (se 1 (by rfl) ⟨1553147, by rfl⟩ : syracuseStep 2070863 = 3106295) B3106295
theorem B3106301 : Blo 2069435 3106301 := bbase (se 3 (by rfl) ⟨582431, by rfl⟩ : syracuseStep 3106301 = 1164863) (by norm_num)
theorem B2070867 : Blo 2069435 2070867 := bstep (se 1 (by rfl) ⟨1553150, by rfl⟩ : syracuseStep 2070867 = 3106301) B3106301
theorem B4659461 : Blo 2069435 4659461 := bbase (se 4 (by rfl) ⟨436824, by rfl⟩ : syracuseStep 4659461 = 873649) (by norm_num)
theorem B3106307 : Blo 2069435 3106307 := bstep (se 1 (by rfl) ⟨2329730, by rfl⟩ : syracuseStep 3106307 = 4659461) B4659461
theorem B2070871 : Blo 2069435 2070871 := bstep (se 1 (by rfl) ⟨1553153, by rfl⟩ : syracuseStep 2070871 = 3106307) B3106307
theorem B3931429 : Blo 2069435 3931429 := bbase (se 4 (by rfl) ⟨368571, by rfl⟩ : syracuseStep 3931429 = 737143) (by norm_num)
theorem B5241905 : Blo 2069435 5241905 := bstep (se 2 (by rfl) ⟨1965714, by rfl⟩ : syracuseStep 5241905 = 3931429) B3931429
theorem B3494603 : Blo 2069435 3494603 := bstep (se 1 (by rfl) ⟨2620952, by rfl⟩ : syracuseStep 3494603 = 5241905) B5241905
theorem B2329735 : Blo 2069435 2329735 := bstep (se 1 (by rfl) ⟨1747301, by rfl⟩ : syracuseStep 2329735 = 3494603) B3494603
theorem B3106313 : Blo 2069435 3106313 := bstep (se 2 (by rfl) ⟨1164867, by rfl⟩ : syracuseStep 3106313 = 2329735) B2329735
theorem B2070875 : Blo 2069435 2070875 := bstep (se 1 (by rfl) ⟨1553156, by rfl⟩ : syracuseStep 2070875 = 3106313) B3106313
theorem B10483829 : Blo 2069435 10483829 := bbase (se 5 (by rfl) ⟨491429, by rfl⟩ : syracuseStep 10483829 = 982859) (by norm_num)
theorem B6989219 : Blo 2069435 6989219 := bstep (se 1 (by rfl) ⟨5241914, by rfl⟩ : syracuseStep 6989219 = 10483829) B10483829
theorem B4659479 : Blo 2069435 4659479 := bstep (se 1 (by rfl) ⟨3494609, by rfl⟩ : syracuseStep 4659479 = 6989219) B6989219
theorem B3106319 : Blo 2069435 3106319 := bstep (se 1 (by rfl) ⟨2329739, by rfl⟩ : syracuseStep 3106319 = 4659479) B4659479
theorem B2070879 : Blo 2069435 2070879 := bstep (se 1 (by rfl) ⟨1553159, by rfl⟩ : syracuseStep 2070879 = 3106319) B3106319
theorem B3106325 : Blo 2069435 3106325 := bbase (se 6 (by rfl) ⟨72804, by rfl⟩ : syracuseStep 3106325 = 145609) (by norm_num)
theorem B2070883 : Blo 2069435 2070883 := bstep (se 1 (by rfl) ⟨1553162, by rfl⟩ : syracuseStep 2070883 = 3106325) B3106325
theorem B6634325 : Blo 2069435 6634325 := bbase (se 9 (by rfl) ⟨19436, by rfl⟩ : syracuseStep 6634325 = 38873) (by norm_num)
theorem B17691533 : Blo 2069435 17691533 := bstep (se 3 (by rfl) ⟨3317162, by rfl⟩ : syracuseStep 17691533 = 6634325) B6634325
theorem B11794355 : Blo 2069435 11794355 := bstep (se 1 (by rfl) ⟨8845766, by rfl⟩ : syracuseStep 11794355 = 17691533) B17691533
theorem B7862903 : Blo 2069435 7862903 := bstep (se 1 (by rfl) ⟨5897177, by rfl⟩ : syracuseStep 7862903 = 11794355) B11794355
theorem B5241935 : Blo 2069435 5241935 := bstep (se 1 (by rfl) ⟨3931451, by rfl⟩ : syracuseStep 5241935 = 7862903) B7862903
theorem B3494623 : Blo 2069435 3494623 := bstep (se 1 (by rfl) ⟨2620967, by rfl⟩ : syracuseStep 3494623 = 5241935) B5241935
theorem B4659497 : Blo 2069435 4659497 := bstep (se 2 (by rfl) ⟨1747311, by rfl⟩ : syracuseStep 4659497 = 3494623) B3494623
theorem B3106331 : Blo 2069435 3106331 := bstep (se 1 (by rfl) ⟨2329748, by rfl⟩ : syracuseStep 3106331 = 4659497) B4659497
theorem B2070887 : Blo 2069435 2070887 := bstep (se 1 (by rfl) ⟨1553165, by rfl⟩ : syracuseStep 2070887 = 3106331) B3106331
theorem B2329753 : Blo 2069435 2329753 := bbase (se 2 (by rfl) ⟨873657, by rfl⟩ : syracuseStep 2329753 = 1747315) (by norm_num)
theorem B3106337 : Blo 2069435 3106337 := bstep (se 2 (by rfl) ⟨1164876, by rfl⟩ : syracuseStep 3106337 = 2329753) B2329753
theorem B2070891 : Blo 2069435 2070891 := bstep (se 1 (by rfl) ⟨1553168, by rfl⟩ : syracuseStep 2070891 = 3106337) B3106337
theorem B7862933 : Blo 2069435 7862933 := bbase (se 6 (by rfl) ⟨184287, by rfl⟩ : syracuseStep 7862933 = 368575) (by norm_num)
theorem B5241955 : Blo 2069435 5241955 := bstep (se 1 (by rfl) ⟨3931466, by rfl⟩ : syracuseStep 5241955 = 7862933) B7862933
theorem B6989273 : Blo 2069435 6989273 := bstep (se 2 (by rfl) ⟨2620977, by rfl⟩ : syracuseStep 6989273 = 5241955) B5241955
theorem B4659515 : Blo 2069435 4659515 := bstep (se 1 (by rfl) ⟨3494636, by rfl⟩ : syracuseStep 4659515 = 6989273) B6989273
theorem B3106343 : Blo 2069435 3106343 := bstep (se 1 (by rfl) ⟨2329757, by rfl⟩ : syracuseStep 3106343 = 4659515) B4659515
theorem B2070895 : Blo 2069435 2070895 := bstep (se 1 (by rfl) ⟨1553171, by rfl⟩ : syracuseStep 2070895 = 3106343) B3106343
theorem B3106349 : Blo 2069435 3106349 := bbase (se 3 (by rfl) ⟨582440, by rfl⟩ : syracuseStep 3106349 = 1164881) (by norm_num)
theorem B2070899 : Blo 2069435 2070899 := bstep (se 1 (by rfl) ⟨1553174, by rfl⟩ : syracuseStep 2070899 = 3106349) B3106349
theorem B4659533 : Blo 2069435 4659533 := bbase (se 3 (by rfl) ⟨873662, by rfl⟩ : syracuseStep 4659533 = 1747325) (by norm_num)
theorem B3106355 : Blo 2069435 3106355 := bstep (se 1 (by rfl) ⟨2329766, by rfl⟩ : syracuseStep 3106355 = 4659533) B4659533
theorem B2070903 : Blo 2069435 2070903 := bstep (se 1 (by rfl) ⟨1553177, by rfl⟩ : syracuseStep 2070903 = 3106355) B3106355
theorem B2620993 : Blo 2069435 2620993 := bbase (se 2 (by rfl) ⟨982872, by rfl⟩ : syracuseStep 2620993 = 1965745) (by norm_num)
theorem B3494657 : Blo 2069435 3494657 := bstep (se 2 (by rfl) ⟨1310496, by rfl⟩ : syracuseStep 3494657 = 2620993) B2620993
theorem B2329771 : Blo 2069435 2329771 := bstep (se 1 (by rfl) ⟨1747328, by rfl⟩ : syracuseStep 2329771 = 3494657) B3494657
theorem B3106361 : Blo 2069435 3106361 := bstep (se 2 (by rfl) ⟨1164885, by rfl⟩ : syracuseStep 3106361 = 2329771) B2329771
theorem B2070907 : Blo 2069435 2070907 := bstep (se 1 (by rfl) ⟨1553180, by rfl⟩ : syracuseStep 2070907 = 3106361) B3106361
theorem B2487901 : Blo 2069435 2487901 := bbase (se 3 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 2487901 = 932963) (by norm_num)
theorem B3317201 : Blo 2069435 3317201 := bstep (se 2 (by rfl) ⟨1243950, by rfl⟩ : syracuseStep 3317201 = 2487901) B2487901
theorem B2211467 : Blo 2069435 2211467 := bstep (se 1 (by rfl) ⟨1658600, by rfl⟩ : syracuseStep 2211467 = 3317201) B3317201
theorem B23588981 : Blo 2069435 23588981 := bstep (se 5 (by rfl) ⟨1105733, by rfl⟩ : syracuseStep 23588981 = 2211467) B2211467
theorem B15725987 : Blo 2069435 15725987 := bstep (se 1 (by rfl) ⟨11794490, by rfl⟩ : syracuseStep 15725987 = 23588981) B23588981
theorem B10483991 : Blo 2069435 10483991 := bstep (se 1 (by rfl) ⟨7862993, by rfl⟩ : syracuseStep 10483991 = 15725987) B15725987
theorem B6989327 : Blo 2069435 6989327 := bstep (se 1 (by rfl) ⟨5241995, by rfl⟩ : syracuseStep 6989327 = 10483991) B10483991
theorem B4659551 : Blo 2069435 4659551 := bstep (se 1 (by rfl) ⟨3494663, by rfl⟩ : syracuseStep 4659551 = 6989327) B6989327
theorem B3106367 : Blo 2069435 3106367 := bstep (se 1 (by rfl) ⟨2329775, by rfl⟩ : syracuseStep 3106367 = 4659551) B4659551
theorem B2070911 : Blo 2069435 2070911 := bstep (se 1 (by rfl) ⟨1553183, by rfl⟩ : syracuseStep 2070911 = 3106367) B3106367
theorem B3106373 : Blo 2069435 3106373 := bbase (se 4 (by rfl) ⟨291222, by rfl⟩ : syracuseStep 3106373 = 582445) (by norm_num)
theorem B2070915 : Blo 2069435 2070915 := bstep (se 1 (by rfl) ⟨1553186, by rfl⟩ : syracuseStep 2070915 = 3106373) B3106373
theorem B3494677 : Blo 2069435 3494677 := bbase (se 6 (by rfl) ⟨81906, by rfl⟩ : syracuseStep 3494677 = 163813) (by norm_num)
theorem B4659569 : Blo 2069435 4659569 := bstep (se 2 (by rfl) ⟨1747338, by rfl⟩ : syracuseStep 4659569 = 3494677) B3494677
theorem B3106379 : Blo 2069435 3106379 := bstep (se 1 (by rfl) ⟨2329784, by rfl⟩ : syracuseStep 3106379 = 4659569) B4659569
theorem B2070919 : Blo 2069435 2070919 := bstep (se 1 (by rfl) ⟨1553189, by rfl⟩ : syracuseStep 2070919 = 3106379) B3106379
theorem B2329789 : Blo 2069435 2329789 := bbase (se 3 (by rfl) ⟨436835, by rfl⟩ : syracuseStep 2329789 = 873671) (by norm_num)
theorem B3106385 : Blo 2069435 3106385 := bstep (se 2 (by rfl) ⟨1164894, by rfl⟩ : syracuseStep 3106385 = 2329789) B2329789
theorem B2070923 : Blo 2069435 2070923 := bstep (se 1 (by rfl) ⟨1553192, by rfl⟩ : syracuseStep 2070923 = 3106385) B3106385
theorem B6989381 : Blo 2069435 6989381 := bbase (se 4 (by rfl) ⟨655254, by rfl⟩ : syracuseStep 6989381 = 1310509) (by norm_num)
theorem B4659587 : Blo 2069435 4659587 := bstep (se 1 (by rfl) ⟨3494690, by rfl⟩ : syracuseStep 4659587 = 6989381) B6989381
theorem B3106391 : Blo 2069435 3106391 := bstep (se 1 (by rfl) ⟨2329793, by rfl⟩ : syracuseStep 3106391 = 4659587) B4659587
theorem B2070927 : Blo 2069435 2070927 := bstep (se 1 (by rfl) ⟨1553195, by rfl⟩ : syracuseStep 2070927 = 3106391) B3106391
theorem B3106397 : Blo 2069435 3106397 := bbase (se 3 (by rfl) ⟨582449, by rfl⟩ : syracuseStep 3106397 = 1164899) (by norm_num)
theorem B2070931 : Blo 2069435 2070931 := bstep (se 1 (by rfl) ⟨1553198, by rfl⟩ : syracuseStep 2070931 = 3106397) B3106397
theorem B4659605 : Blo 2069435 4659605 := bbase (se 6 (by rfl) ⟨109209, by rfl⟩ : syracuseStep 4659605 = 218419) (by norm_num)
theorem B3106403 : Blo 2069435 3106403 := bstep (se 1 (by rfl) ⟨2329802, by rfl⟩ : syracuseStep 3106403 = 4659605) B4659605
theorem B2070935 : Blo 2069435 2070935 := bstep (se 1 (by rfl) ⟨1553201, by rfl⟩ : syracuseStep 2070935 = 3106403) B3106403
theorem B2303257 : Blo 2069435 2303257 := bbase (se 2 (by rfl) ⟨863721, by rfl⟩ : syracuseStep 2303257 = 1727443) (by norm_num)
theorem B49136149 : Blo 2069435 49136149 := bstep (se 6 (by rfl) ⟨1151628, by rfl⟩ : syracuseStep 49136149 = 2303257) B2303257
theorem B65514865 : Blo 2069435 65514865 := bstep (se 2 (by rfl) ⟨24568074, by rfl⟩ : syracuseStep 65514865 = 49136149) B49136149
theorem B87353153 : Blo 2069435 87353153 := bstep (se 2 (by rfl) ⟨32757432, by rfl⟩ : syracuseStep 87353153 = 65514865) B65514865
theorem B58235435 : Blo 2069435 58235435 := bstep (se 1 (by rfl) ⟨43676576, by rfl⟩ : syracuseStep 58235435 = 87353153) B87353153
theorem B38823623 : Blo 2069435 38823623 := bstep (se 1 (by rfl) ⟨29117717, by rfl⟩ : syracuseStep 38823623 = 58235435) B58235435
theorem B25882415 : Blo 2069435 25882415 := bstep (se 1 (by rfl) ⟨19411811, by rfl⟩ : syracuseStep 25882415 = 38823623) B38823623
theorem B17254943 : Blo 2069435 17254943 := bstep (se 1 (by rfl) ⟨12941207, by rfl⟩ : syracuseStep 17254943 = 25882415) B25882415
theorem B11503295 : Blo 2069435 11503295 := bstep (se 1 (by rfl) ⟨8627471, by rfl⟩ : syracuseStep 11503295 = 17254943) B17254943
theorem B7668863 : Blo 2069435 7668863 := bstep (se 1 (by rfl) ⟨5751647, by rfl⟩ : syracuseStep 7668863 = 11503295) B11503295
theorem B5112575 : Blo 2069435 5112575 := bstep (se 1 (by rfl) ⟨3834431, by rfl⟩ : syracuseStep 5112575 = 7668863) B7668863
theorem B3408383 : Blo 2069435 3408383 := bstep (se 1 (by rfl) ⟨2556287, by rfl⟩ : syracuseStep 3408383 = 5112575) B5112575
theorem B2272255 : Blo 2069435 2272255 := bstep (se 1 (by rfl) ⟨1704191, by rfl⟩ : syracuseStep 2272255 = 3408383) B3408383
theorem B48474773 : Blo 2069435 48474773 := bstep (se 6 (by rfl) ⟨1136127, by rfl⟩ : syracuseStep 48474773 = 2272255) B2272255
theorem B32316515 : Blo 2069435 32316515 := bstep (se 1 (by rfl) ⟨24237386, by rfl⟩ : syracuseStep 32316515 = 48474773) B48474773
theorem B21544343 : Blo 2069435 21544343 := bstep (se 1 (by rfl) ⟨16158257, by rfl⟩ : syracuseStep 21544343 = 32316515) B32316515
theorem B14362895 : Blo 2069435 14362895 := bstep (se 1 (by rfl) ⟨10772171, by rfl⟩ : syracuseStep 14362895 = 21544343) B21544343
theorem B9575263 : Blo 2069435 9575263 := bstep (se 1 (by rfl) ⟨7181447, by rfl⟩ : syracuseStep 9575263 = 14362895) B14362895
theorem B51068069 : Blo 2069435 51068069 := bstep (se 4 (by rfl) ⟨4787631, by rfl⟩ : syracuseStep 51068069 = 9575263) B9575263
theorem B34045379 : Blo 2069435 34045379 := bstep (se 1 (by rfl) ⟨25534034, by rfl⟩ : syracuseStep 34045379 = 51068069) B51068069
theorem B22696919 : Blo 2069435 22696919 := bstep (se 1 (by rfl) ⟨17022689, by rfl⟩ : syracuseStep 22696919 = 34045379) B34045379
theorem B15131279 : Blo 2069435 15131279 := bstep (se 1 (by rfl) ⟨11348459, by rfl⟩ : syracuseStep 15131279 = 22696919) B22696919
theorem B10087519 : Blo 2069435 10087519 := bstep (se 1 (by rfl) ⟨7565639, by rfl⟩ : syracuseStep 10087519 = 15131279) B15131279
theorem B13450025 : Blo 2069435 13450025 := bstep (se 2 (by rfl) ⟨5043759, by rfl⟩ : syracuseStep 13450025 = 10087519) B10087519
theorem B8966683 : Blo 2069435 8966683 := bstep (se 1 (by rfl) ⟨6725012, by rfl⟩ : syracuseStep 8966683 = 13450025) B13450025
theorem B47822309 : Blo 2069435 47822309 := bstep (se 4 (by rfl) ⟨4483341, by rfl⟩ : syracuseStep 47822309 = 8966683) B8966683
theorem B31881539 : Blo 2069435 31881539 := bstep (se 1 (by rfl) ⟨23911154, by rfl⟩ : syracuseStep 31881539 = 47822309) B47822309
theorem B21254359 : Blo 2069435 21254359 := bstep (se 1 (by rfl) ⟨15940769, by rfl⟩ : syracuseStep 21254359 = 31881539) B31881539
theorem B28339145 : Blo 2069435 28339145 := bstep (se 2 (by rfl) ⟨10627179, by rfl⟩ : syracuseStep 28339145 = 21254359) B21254359
theorem B18892763 : Blo 2069435 18892763 := bstep (se 1 (by rfl) ⟨14169572, by rfl⟩ : syracuseStep 18892763 = 28339145) B28339145
theorem B12595175 : Blo 2069435 12595175 := bstep (se 1 (by rfl) ⟨9446381, by rfl⟩ : syracuseStep 12595175 = 18892763) B18892763
theorem B8396783 : Blo 2069435 8396783 := bstep (se 1 (by rfl) ⟨6297587, by rfl⟩ : syracuseStep 8396783 = 12595175) B12595175
theorem B5597855 : Blo 2069435 5597855 := bstep (se 1 (by rfl) ⟨4198391, by rfl⟩ : syracuseStep 5597855 = 8396783) B8396783
theorem B3731903 : Blo 2069435 3731903 := bstep (se 1 (by rfl) ⟨2798927, by rfl⟩ : syracuseStep 3731903 = 5597855) B5597855
theorem B2487935 : Blo 2069435 2487935 := bstep (se 1 (by rfl) ⟨1865951, by rfl⟩ : syracuseStep 2487935 = 3731903) B3731903
theorem B6634493 : Blo 2069435 6634493 := bstep (se 3 (by rfl) ⟨1243967, by rfl⟩ : syracuseStep 6634493 = 2487935) B2487935
theorem B4422995 : Blo 2069435 4422995 := bstep (se 1 (by rfl) ⟨3317246, by rfl⟩ : syracuseStep 4422995 = 6634493) B6634493
theorem B2948663 : Blo 2069435 2948663 := bstep (se 1 (by rfl) ⟨2211497, by rfl⟩ : syracuseStep 2948663 = 4422995) B4422995
theorem B7863101 : Blo 2069435 7863101 := bstep (se 3 (by rfl) ⟨1474331, by rfl⟩ : syracuseStep 7863101 = 2948663) B2948663
theorem B5242067 : Blo 2069435 5242067 := bstep (se 1 (by rfl) ⟨3931550, by rfl⟩ : syracuseStep 5242067 = 7863101) B7863101
theorem B3494711 : Blo 2069435 3494711 := bstep (se 1 (by rfl) ⟨2621033, by rfl⟩ : syracuseStep 3494711 = 5242067) B5242067
theorem B2329807 : Blo 2069435 2329807 := bstep (se 1 (by rfl) ⟨1747355, by rfl⟩ : syracuseStep 2329807 = 3494711) B3494711
theorem B3106409 : Blo 2069435 3106409 := bstep (se 2 (by rfl) ⟨1164903, by rfl⟩ : syracuseStep 3106409 = 2329807) B2329807
theorem B2070939 : Blo 2069435 2070939 := bstep (se 1 (by rfl) ⟨1553204, by rfl⟩ : syracuseStep 2070939 = 3106409) B3106409
theorem B8846005 : Blo 2069435 8846005 := bbase (se 5 (by rfl) ⟨414656, by rfl⟩ : syracuseStep 8846005 = 829313) (by norm_num)
theorem B11794673 : Blo 2069435 11794673 := bstep (se 2 (by rfl) ⟨4423002, by rfl⟩ : syracuseStep 11794673 = 8846005) B8846005
theorem B7863115 : Blo 2069435 7863115 := bstep (se 1 (by rfl) ⟨5897336, by rfl⟩ : syracuseStep 7863115 = 11794673) B11794673
theorem B10484153 : Blo 2069435 10484153 := bstep (se 2 (by rfl) ⟨3931557, by rfl⟩ : syracuseStep 10484153 = 7863115) B7863115
theorem B6989435 : Blo 2069435 6989435 := bstep (se 1 (by rfl) ⟨5242076, by rfl⟩ : syracuseStep 6989435 = 10484153) B10484153
theorem B4659623 : Blo 2069435 4659623 := bstep (se 1 (by rfl) ⟨3494717, by rfl⟩ : syracuseStep 4659623 = 6989435) B6989435
theorem B3106415 : Blo 2069435 3106415 := bstep (se 1 (by rfl) ⟨2329811, by rfl⟩ : syracuseStep 3106415 = 4659623) B4659623
theorem B2070943 : Blo 2069435 2070943 := bstep (se 1 (by rfl) ⟨1553207, by rfl⟩ : syracuseStep 2070943 = 3106415) B3106415
theorem B3106421 : Blo 2069435 3106421 := bbase (se 5 (by rfl) ⟨145613, by rfl⟩ : syracuseStep 3106421 = 291227) (by norm_num)
theorem B2070947 : Blo 2069435 2070947 := bstep (se 1 (by rfl) ⟨1553210, by rfl⟩ : syracuseStep 2070947 = 3106421) B3106421
theorem B3931573 : Blo 2069435 3931573 := bbase (se 5 (by rfl) ⟨184292, by rfl⟩ : syracuseStep 3931573 = 368585) (by norm_num)
theorem B5242097 : Blo 2069435 5242097 := bstep (se 2 (by rfl) ⟨1965786, by rfl⟩ : syracuseStep 5242097 = 3931573) B3931573
theorem B3494731 : Blo 2069435 3494731 := bstep (se 1 (by rfl) ⟨2621048, by rfl⟩ : syracuseStep 3494731 = 5242097) B5242097
theorem B4659641 : Blo 2069435 4659641 := bstep (se 2 (by rfl) ⟨1747365, by rfl⟩ : syracuseStep 4659641 = 3494731) B3494731
theorem B3106427 : Blo 2069435 3106427 := bstep (se 1 (by rfl) ⟨2329820, by rfl⟩ : syracuseStep 3106427 = 4659641) B4659641
theorem B2070951 : Blo 2069435 2070951 := bstep (se 1 (by rfl) ⟨1553213, by rfl⟩ : syracuseStep 2070951 = 3106427) B3106427
theorem B2329825 : Blo 2069435 2329825 := bbase (se 2 (by rfl) ⟨873684, by rfl⟩ : syracuseStep 2329825 = 1747369) (by norm_num)
theorem B3106433 : Blo 2069435 3106433 := bstep (se 2 (by rfl) ⟨1164912, by rfl⟩ : syracuseStep 3106433 = 2329825) B2329825
theorem B2070955 : Blo 2069435 2070955 := bstep (se 1 (by rfl) ⟨1553216, by rfl⟩ : syracuseStep 2070955 = 3106433) B3106433
theorem B5242117 : Blo 2069435 5242117 := bbase (se 4 (by rfl) ⟨491448, by rfl⟩ : syracuseStep 5242117 = 982897) (by norm_num)
theorem B6989489 : Blo 2069435 6989489 := bstep (se 2 (by rfl) ⟨2621058, by rfl⟩ : syracuseStep 6989489 = 5242117) B5242117
theorem B4659659 : Blo 2069435 4659659 := bstep (se 1 (by rfl) ⟨3494744, by rfl⟩ : syracuseStep 4659659 = 6989489) B6989489
theorem B3106439 : Blo 2069435 3106439 := bstep (se 1 (by rfl) ⟨2329829, by rfl⟩ : syracuseStep 3106439 = 4659659) B4659659
theorem B2070959 : Blo 2069435 2070959 := bstep (se 1 (by rfl) ⟨1553219, by rfl⟩ : syracuseStep 2070959 = 3106439) B3106439
theorem B3106445 : Blo 2069435 3106445 := bbase (se 3 (by rfl) ⟨582458, by rfl⟩ : syracuseStep 3106445 = 1164917) (by norm_num)
theorem B2070963 : Blo 2069435 2070963 := bstep (se 1 (by rfl) ⟨1553222, by rfl⟩ : syracuseStep 2070963 = 3106445) B3106445
theorem B4659677 : Blo 2069435 4659677 := bbase (se 3 (by rfl) ⟨873689, by rfl⟩ : syracuseStep 4659677 = 1747379) (by norm_num)
theorem B3106451 : Blo 2069435 3106451 := bstep (se 1 (by rfl) ⟨2329838, by rfl⟩ : syracuseStep 3106451 = 4659677) B4659677
theorem B2070967 : Blo 2069435 2070967 := bstep (se 1 (by rfl) ⟨1553225, by rfl⟩ : syracuseStep 2070967 = 3106451) B3106451
theorem B3494765 : Blo 2069435 3494765 := bbase (se 3 (by rfl) ⟨655268, by rfl⟩ : syracuseStep 3494765 = 1310537) (by norm_num)
theorem B2329843 : Blo 2069435 2329843 := bstep (se 1 (by rfl) ⟨1747382, by rfl⟩ : syracuseStep 2329843 = 3494765) B3494765
theorem B3106457 : Blo 2069435 3106457 := bstep (se 2 (by rfl) ⟨1164921, by rfl⟩ : syracuseStep 3106457 = 2329843) B2329843
theorem B2070971 : Blo 2069435 2070971 := bstep (se 1 (by rfl) ⟨1553228, by rfl⟩ : syracuseStep 2070971 = 3106457) B3106457
theorem B8966837 : Blo 2069435 8966837 := bbase (se 5 (by rfl) ⟨420320, by rfl⟩ : syracuseStep 8966837 = 840641) (by norm_num)
theorem B5977891 : Blo 2069435 5977891 := bstep (se 1 (by rfl) ⟨4483418, by rfl⟩ : syracuseStep 5977891 = 8966837) B8966837
theorem B7970521 : Blo 2069435 7970521 := bstep (se 2 (by rfl) ⟨2988945, by rfl⟩ : syracuseStep 7970521 = 5977891) B5977891
theorem B10627361 : Blo 2069435 10627361 := bstep (se 2 (by rfl) ⟨3985260, by rfl⟩ : syracuseStep 10627361 = 7970521) B7970521
theorem B7084907 : Blo 2069435 7084907 := bstep (se 1 (by rfl) ⟨5313680, by rfl⟩ : syracuseStep 7084907 = 10627361) B10627361
theorem B4723271 : Blo 2069435 4723271 := bstep (se 1 (by rfl) ⟨3542453, by rfl⟩ : syracuseStep 4723271 = 7084907) B7084907
theorem B3148847 : Blo 2069435 3148847 := bstep (se 1 (by rfl) ⟨2361635, by rfl⟩ : syracuseStep 3148847 = 4723271) B4723271
theorem B2099231 : Blo 2069435 2099231 := bstep (se 1 (by rfl) ⟨1574423, by rfl⟩ : syracuseStep 2099231 = 3148847) B3148847
theorem B22391797 : Blo 2069435 22391797 := bstep (se 5 (by rfl) ⟨1049615, by rfl⟩ : syracuseStep 22391797 = 2099231) B2099231
theorem B29855729 : Blo 2069435 29855729 := bstep (se 2 (by rfl) ⟨11195898, by rfl⟩ : syracuseStep 29855729 = 22391797) B22391797
theorem B19903819 : Blo 2069435 19903819 := bstep (se 1 (by rfl) ⟨14927864, by rfl⟩ : syracuseStep 19903819 = 29855729) B29855729
theorem B26538425 : Blo 2069435 26538425 := bstep (se 2 (by rfl) ⟨9951909, by rfl⟩ : syracuseStep 26538425 = 19903819) B19903819
theorem B17692283 : Blo 2069435 17692283 := bstep (se 1 (by rfl) ⟨13269212, by rfl⟩ : syracuseStep 17692283 = 26538425) B26538425
theorem B11794855 : Blo 2069435 11794855 := bstep (se 1 (by rfl) ⟨8846141, by rfl⟩ : syracuseStep 11794855 = 17692283) B17692283
theorem B15726473 : Blo 2069435 15726473 := bstep (se 2 (by rfl) ⟨5897427, by rfl⟩ : syracuseStep 15726473 = 11794855) B11794855
theorem B10484315 : Blo 2069435 10484315 := bstep (se 1 (by rfl) ⟨7863236, by rfl⟩ : syracuseStep 10484315 = 15726473) B15726473
theorem B6989543 : Blo 2069435 6989543 := bstep (se 1 (by rfl) ⟨5242157, by rfl⟩ : syracuseStep 6989543 = 10484315) B10484315
theorem B4659695 : Blo 2069435 4659695 := bstep (se 1 (by rfl) ⟨3494771, by rfl⟩ : syracuseStep 4659695 = 6989543) B6989543
theorem B3106463 : Blo 2069435 3106463 := bstep (se 1 (by rfl) ⟨2329847, by rfl⟩ : syracuseStep 3106463 = 4659695) B4659695
theorem B2070975 : Blo 2069435 2070975 := bstep (se 1 (by rfl) ⟨1553231, by rfl⟩ : syracuseStep 2070975 = 3106463) B3106463
theorem B3106469 : Blo 2069435 3106469 := bbase (se 4 (by rfl) ⟨291231, by rfl⟩ : syracuseStep 3106469 = 582463) (by norm_num)
theorem B2070979 : Blo 2069435 2070979 := bstep (se 1 (by rfl) ⟨1553234, by rfl⟩ : syracuseStep 2070979 = 3106469) B3106469
theorem B2621089 : Blo 2069435 2621089 := bbase (se 2 (by rfl) ⟨982908, by rfl⟩ : syracuseStep 2621089 = 1965817) (by norm_num)
theorem B3494785 : Blo 2069435 3494785 := bstep (se 2 (by rfl) ⟨1310544, by rfl⟩ : syracuseStep 3494785 = 2621089) B2621089
theorem B4659713 : Blo 2069435 4659713 := bstep (se 2 (by rfl) ⟨1747392, by rfl⟩ : syracuseStep 4659713 = 3494785) B3494785
theorem B3106475 : Blo 2069435 3106475 := bstep (se 1 (by rfl) ⟨2329856, by rfl⟩ : syracuseStep 3106475 = 4659713) B4659713
theorem B2070983 : Blo 2069435 2070983 := bstep (se 1 (by rfl) ⟨1553237, by rfl⟩ : syracuseStep 2070983 = 3106475) B3106475
theorem B2329861 : Blo 2069435 2329861 := bbase (se 4 (by rfl) ⟨218424, by rfl⟩ : syracuseStep 2329861 = 436849) (by norm_num)
theorem B3106481 : Blo 2069435 3106481 := bstep (se 2 (by rfl) ⟨1164930, by rfl⟩ : syracuseStep 3106481 = 2329861) B2329861
theorem B2070987 : Blo 2069435 2070987 := bstep (se 1 (by rfl) ⟨1553240, by rfl⟩ : syracuseStep 2070987 = 3106481) B3106481
theorem B2211553 : Blo 2069435 2211553 := bbase (se 2 (by rfl) ⟨829332, by rfl⟩ : syracuseStep 2211553 = 1658665) (by norm_num)
theorem B2948737 : Blo 2069435 2948737 := bstep (se 2 (by rfl) ⟨1105776, by rfl⟩ : syracuseStep 2948737 = 2211553) B2211553
theorem B3931649 : Blo 2069435 3931649 := bstep (se 2 (by rfl) ⟨1474368, by rfl⟩ : syracuseStep 3931649 = 2948737) B2948737
theorem B2621099 : Blo 2069435 2621099 := bstep (se 1 (by rfl) ⟨1965824, by rfl⟩ : syracuseStep 2621099 = 3931649) B3931649
theorem B6989597 : Blo 2069435 6989597 := bstep (se 3 (by rfl) ⟨1310549, by rfl⟩ : syracuseStep 6989597 = 2621099) B2621099
theorem B4659731 : Blo 2069435 4659731 := bstep (se 1 (by rfl) ⟨3494798, by rfl⟩ : syracuseStep 4659731 = 6989597) B6989597
theorem B3106487 : Blo 2069435 3106487 := bstep (se 1 (by rfl) ⟨2329865, by rfl⟩ : syracuseStep 3106487 = 4659731) B4659731
theorem B2070991 : Blo 2069435 2070991 := bstep (se 1 (by rfl) ⟨1553243, by rfl⟩ : syracuseStep 2070991 = 3106487) B3106487
theorem B3106493 : Blo 2069435 3106493 := bbase (se 3 (by rfl) ⟨582467, by rfl⟩ : syracuseStep 3106493 = 1164935) (by norm_num)
theorem B2070995 : Blo 2069435 2070995 := bstep (se 1 (by rfl) ⟨1553246, by rfl⟩ : syracuseStep 2070995 = 3106493) B3106493
theorem B4659749 : Blo 2069435 4659749 := bbase (se 4 (by rfl) ⟨436851, by rfl⟩ : syracuseStep 4659749 = 873703) (by norm_num)
theorem B3106499 : Blo 2069435 3106499 := bstep (se 1 (by rfl) ⟨2329874, by rfl⟩ : syracuseStep 3106499 = 4659749) B4659749
theorem B2070999 : Blo 2069435 2070999 := bstep (se 1 (by rfl) ⟨1553249, by rfl⟩ : syracuseStep 2070999 = 3106499) B3106499
theorem B5242229 : Blo 2069435 5242229 := bbase (se 5 (by rfl) ⟨245729, by rfl⟩ : syracuseStep 5242229 = 491459) (by norm_num)
theorem B3494819 : Blo 2069435 3494819 := bstep (se 1 (by rfl) ⟨2621114, by rfl⟩ : syracuseStep 3494819 = 5242229) B5242229
theorem B2329879 : Blo 2069435 2329879 := bstep (se 1 (by rfl) ⟨1747409, by rfl⟩ : syracuseStep 2329879 = 3494819) B3494819
theorem B3106505 : Blo 2069435 3106505 := bstep (se 2 (by rfl) ⟨1164939, by rfl⟩ : syracuseStep 3106505 = 2329879) B2329879
theorem B2071003 : Blo 2069435 2071003 := bstep (se 1 (by rfl) ⟨1553252, by rfl⟩ : syracuseStep 2071003 = 3106505) B3106505
theorem B6383717 : Blo 2069435 6383717 := bbase (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) (by norm_num)
theorem B4255811 : Blo 2069435 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B2837207 : Blo 2069435 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B7565885 : Blo 2069435 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B5043923 : Blo 2069435 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B3362615 : Blo 2069435 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B143471573 : Blo 2069435 143471573 := bstep (se 7 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 143471573 = 3362615) B3362615
theorem B95647715 : Blo 2069435 95647715 := bstep (se 1 (by rfl) ⟨71735786, by rfl⟩ : syracuseStep 95647715 = 143471573) B143471573
theorem B63765143 : Blo 2069435 63765143 := bstep (se 1 (by rfl) ⟨47823857, by rfl⟩ : syracuseStep 63765143 = 95647715) B95647715
theorem B42510095 : Blo 2069435 42510095 := bstep (se 1 (by rfl) ⟨31882571, by rfl⟩ : syracuseStep 42510095 = 63765143) B63765143
theorem B28340063 : Blo 2069435 28340063 := bstep (se 1 (by rfl) ⟨21255047, by rfl⟩ : syracuseStep 28340063 = 42510095) B42510095
theorem B18893375 : Blo 2069435 18893375 := bstep (se 1 (by rfl) ⟨14170031, by rfl⟩ : syracuseStep 18893375 = 28340063) B28340063
theorem B12595583 : Blo 2069435 12595583 := bstep (se 1 (by rfl) ⟨9446687, by rfl⟩ : syracuseStep 12595583 = 18893375) B18893375
theorem B8397055 : Blo 2069435 8397055 := bstep (se 1 (by rfl) ⟨6297791, by rfl⟩ : syracuseStep 8397055 = 12595583) B12595583
theorem B11196073 : Blo 2069435 11196073 := bstep (se 2 (by rfl) ⟨4198527, by rfl⟩ : syracuseStep 11196073 = 8397055) B8397055
theorem B14928097 : Blo 2069435 14928097 := bstep (se 2 (by rfl) ⟨5598036, by rfl⟩ : syracuseStep 14928097 = 11196073) B11196073
theorem B19904129 : Blo 2069435 19904129 := bstep (se 2 (by rfl) ⟨7464048, by rfl⟩ : syracuseStep 19904129 = 14928097) B14928097
theorem B13269419 : Blo 2069435 13269419 := bstep (se 1 (by rfl) ⟨9952064, by rfl⟩ : syracuseStep 13269419 = 19904129) B19904129
theorem B8846279 : Blo 2069435 8846279 := bstep (se 1 (by rfl) ⟨6634709, by rfl⟩ : syracuseStep 8846279 = 13269419) B13269419
theorem B5897519 : Blo 2069435 5897519 := bstep (se 1 (by rfl) ⟨4423139, by rfl⟩ : syracuseStep 5897519 = 8846279) B8846279
theorem B3931679 : Blo 2069435 3931679 := bstep (se 1 (by rfl) ⟨2948759, by rfl⟩ : syracuseStep 3931679 = 5897519) B5897519
theorem B10484477 : Blo 2069435 10484477 := bstep (se 3 (by rfl) ⟨1965839, by rfl⟩ : syracuseStep 10484477 = 3931679) B3931679
theorem B6989651 : Blo 2069435 6989651 := bstep (se 1 (by rfl) ⟨5242238, by rfl⟩ : syracuseStep 6989651 = 10484477) B10484477
theorem B4659767 : Blo 2069435 4659767 := bstep (se 1 (by rfl) ⟨3494825, by rfl⟩ : syracuseStep 4659767 = 6989651) B6989651
theorem B3106511 : Blo 2069435 3106511 := bstep (se 1 (by rfl) ⟨2329883, by rfl⟩ : syracuseStep 3106511 = 4659767) B4659767
theorem B2071007 : Blo 2069435 2071007 := bstep (se 1 (by rfl) ⟨1553255, by rfl⟩ : syracuseStep 2071007 = 3106511) B3106511
theorem B3106517 : Blo 2069435 3106517 := bbase (se 7 (by rfl) ⟨36404, by rfl⟩ : syracuseStep 3106517 = 72809) (by norm_num)
theorem B2071011 : Blo 2069435 2071011 := bstep (se 1 (by rfl) ⟨1553258, by rfl⟩ : syracuseStep 2071011 = 3106517) B3106517
theorem B4423157 : Blo 2069435 4423157 := bbase (se 5 (by rfl) ⟨207335, by rfl⟩ : syracuseStep 4423157 = 414671) (by norm_num)
theorem B2948771 : Blo 2069435 2948771 := bstep (se 1 (by rfl) ⟨2211578, by rfl⟩ : syracuseStep 2948771 = 4423157) B4423157
theorem B7863389 : Blo 2069435 7863389 := bstep (se 3 (by rfl) ⟨1474385, by rfl⟩ : syracuseStep 7863389 = 2948771) B2948771
theorem B5242259 : Blo 2069435 5242259 := bstep (se 1 (by rfl) ⟨3931694, by rfl⟩ : syracuseStep 5242259 = 7863389) B7863389
theorem B3494839 : Blo 2069435 3494839 := bstep (se 1 (by rfl) ⟨2621129, by rfl⟩ : syracuseStep 3494839 = 5242259) B5242259
theorem B4659785 : Blo 2069435 4659785 := bstep (se 2 (by rfl) ⟨1747419, by rfl⟩ : syracuseStep 4659785 = 3494839) B3494839
theorem B3106523 : Blo 2069435 3106523 := bstep (se 1 (by rfl) ⟨2329892, by rfl⟩ : syracuseStep 3106523 = 4659785) B4659785
theorem B2071015 : Blo 2069435 2071015 := bstep (se 1 (by rfl) ⟨1553261, by rfl⟩ : syracuseStep 2071015 = 3106523) B3106523
theorem B2329897 : Blo 2069435 2329897 := bbase (se 2 (by rfl) ⟨873711, by rfl⟩ : syracuseStep 2329897 = 1747423) (by norm_num)
theorem B3106529 : Blo 2069435 3106529 := bstep (se 2 (by rfl) ⟨1164948, by rfl⟩ : syracuseStep 3106529 = 2329897) B2329897
theorem B2071019 : Blo 2069435 2071019 := bstep (se 1 (by rfl) ⟨1553264, by rfl⟩ : syracuseStep 2071019 = 3106529) B3106529
theorem B3732053 : Blo 2069435 3732053 := bbase (se 8 (by rfl) ⟨21867, by rfl⟩ : syracuseStep 3732053 = 43735) (by norm_num)
theorem B9952141 : Blo 2069435 9952141 := bstep (se 3 (by rfl) ⟨1866026, by rfl⟩ : syracuseStep 9952141 = 3732053) B3732053
theorem B13269521 : Blo 2069435 13269521 := bstep (se 2 (by rfl) ⟨4976070, by rfl⟩ : syracuseStep 13269521 = 9952141) B9952141
theorem B8846347 : Blo 2069435 8846347 := bstep (se 1 (by rfl) ⟨6634760, by rfl⟩ : syracuseStep 8846347 = 13269521) B13269521
theorem B11795129 : Blo 2069435 11795129 := bstep (se 2 (by rfl) ⟨4423173, by rfl⟩ : syracuseStep 11795129 = 8846347) B8846347
theorem B7863419 : Blo 2069435 7863419 := bstep (se 1 (by rfl) ⟨5897564, by rfl⟩ : syracuseStep 7863419 = 11795129) B11795129
theorem B5242279 : Blo 2069435 5242279 := bstep (se 1 (by rfl) ⟨3931709, by rfl⟩ : syracuseStep 5242279 = 7863419) B7863419
theorem B6989705 : Blo 2069435 6989705 := bstep (se 2 (by rfl) ⟨2621139, by rfl⟩ : syracuseStep 6989705 = 5242279) B5242279
theorem B4659803 : Blo 2069435 4659803 := bstep (se 1 (by rfl) ⟨3494852, by rfl⟩ : syracuseStep 4659803 = 6989705) B6989705
theorem B3106535 : Blo 2069435 3106535 := bstep (se 1 (by rfl) ⟨2329901, by rfl⟩ : syracuseStep 3106535 = 4659803) B4659803
theorem B2071023 : Blo 2069435 2071023 := bstep (se 1 (by rfl) ⟨1553267, by rfl⟩ : syracuseStep 2071023 = 3106535) B3106535
theorem B3106541 : Blo 2069435 3106541 := bbase (se 3 (by rfl) ⟨582476, by rfl⟩ : syracuseStep 3106541 = 1164953) (by norm_num)
theorem B2071027 : Blo 2069435 2071027 := bstep (se 1 (by rfl) ⟨1553270, by rfl⟩ : syracuseStep 2071027 = 3106541) B3106541
theorem B4659821 : Blo 2069435 4659821 := bbase (se 3 (by rfl) ⟨873716, by rfl⟩ : syracuseStep 4659821 = 1747433) (by norm_num)
theorem B3106547 : Blo 2069435 3106547 := bstep (se 1 (by rfl) ⟨2329910, by rfl⟩ : syracuseStep 3106547 = 4659821) B4659821
theorem B2071031 : Blo 2069435 2071031 := bstep (se 1 (by rfl) ⟨1553273, by rfl⟩ : syracuseStep 2071031 = 3106547) B3106547
theorem B3931733 : Blo 2069435 3931733 := bbase (se 8 (by rfl) ⟨23037, by rfl⟩ : syracuseStep 3931733 = 46075) (by norm_num)
theorem B2621155 : Blo 2069435 2621155 := bstep (se 1 (by rfl) ⟨1965866, by rfl⟩ : syracuseStep 2621155 = 3931733) B3931733
theorem B3494873 : Blo 2069435 3494873 := bstep (se 2 (by rfl) ⟨1310577, by rfl⟩ : syracuseStep 3494873 = 2621155) B2621155
theorem B2329915 : Blo 2069435 2329915 := bstep (se 1 (by rfl) ⟨1747436, by rfl⟩ : syracuseStep 2329915 = 3494873) B3494873
theorem B3106553 : Blo 2069435 3106553 := bstep (se 2 (by rfl) ⟨1164957, by rfl⟩ : syracuseStep 3106553 = 2329915) B2329915
theorem B2071035 : Blo 2069435 2071035 := bstep (se 1 (by rfl) ⟨1553276, by rfl⟩ : syracuseStep 2071035 = 3106553) B3106553
theorem B2799061 : Blo 2069435 2799061 := bbase (se 7 (by rfl) ⟨32801, by rfl⟩ : syracuseStep 2799061 = 65603) (by norm_num)
theorem B59713301 : Blo 2069435 59713301 := bstep (se 6 (by rfl) ⟨1399530, by rfl⟩ : syracuseStep 59713301 = 2799061) B2799061
theorem B39808867 : Blo 2069435 39808867 := bstep (se 1 (by rfl) ⟨29856650, by rfl⟩ : syracuseStep 39808867 = 59713301) B59713301
theorem B53078489 : Blo 2069435 53078489 := bstep (se 2 (by rfl) ⟨19904433, by rfl⟩ : syracuseStep 53078489 = 39808867) B39808867
theorem B35385659 : Blo 2069435 35385659 := bstep (se 1 (by rfl) ⟨26539244, by rfl⟩ : syracuseStep 35385659 = 53078489) B53078489
theorem B23590439 : Blo 2069435 23590439 := bstep (se 1 (by rfl) ⟨17692829, by rfl⟩ : syracuseStep 23590439 = 35385659) B35385659
theorem B15726959 : Blo 2069435 15726959 := bstep (se 1 (by rfl) ⟨11795219, by rfl⟩ : syracuseStep 15726959 = 23590439) B23590439
theorem B10484639 : Blo 2069435 10484639 := bstep (se 1 (by rfl) ⟨7863479, by rfl⟩ : syracuseStep 10484639 = 15726959) B15726959
theorem B6989759 : Blo 2069435 6989759 := bstep (se 1 (by rfl) ⟨5242319, by rfl⟩ : syracuseStep 6989759 = 10484639) B10484639
theorem B4659839 : Blo 2069435 4659839 := bstep (se 1 (by rfl) ⟨3494879, by rfl⟩ : syracuseStep 4659839 = 6989759) B6989759
theorem B3106559 : Blo 2069435 3106559 := bstep (se 1 (by rfl) ⟨2329919, by rfl⟩ : syracuseStep 3106559 = 4659839) B4659839
theorem B2071039 : Blo 2069435 2071039 := bstep (se 1 (by rfl) ⟨1553279, by rfl⟩ : syracuseStep 2071039 = 3106559) B3106559
theorem B3106565 : Blo 2069435 3106565 := bbase (se 4 (by rfl) ⟨291240, by rfl⟩ : syracuseStep 3106565 = 582481) (by norm_num)
theorem B2071043 : Blo 2069435 2071043 := bstep (se 1 (by rfl) ⟨1553282, by rfl⟩ : syracuseStep 2071043 = 3106565) B3106565
theorem B3494893 : Blo 2069435 3494893 := bbase (se 3 (by rfl) ⟨655292, by rfl⟩ : syracuseStep 3494893 = 1310585) (by norm_num)
theorem B4659857 : Blo 2069435 4659857 := bstep (se 2 (by rfl) ⟨1747446, by rfl⟩ : syracuseStep 4659857 = 3494893) B3494893
theorem B3106571 : Blo 2069435 3106571 := bstep (se 1 (by rfl) ⟨2329928, by rfl⟩ : syracuseStep 3106571 = 4659857) B4659857
theorem B2071047 : Blo 2069435 2071047 := bstep (se 1 (by rfl) ⟨1553285, by rfl⟩ : syracuseStep 2071047 = 3106571) B3106571
theorem B2329933 : Blo 2069435 2329933 := bbase (se 3 (by rfl) ⟨436862, by rfl⟩ : syracuseStep 2329933 = 873725) (by norm_num)
theorem B3106577 : Blo 2069435 3106577 := bstep (se 2 (by rfl) ⟨1164966, by rfl⟩ : syracuseStep 3106577 = 2329933) B2329933
theorem B2071051 : Blo 2069435 2071051 := bstep (se 1 (by rfl) ⟨1553288, by rfl⟩ : syracuseStep 2071051 = 3106577) B3106577
theorem B6989813 : Blo 2069435 6989813 := bbase (se 5 (by rfl) ⟨327647, by rfl⟩ : syracuseStep 6989813 = 655295) (by norm_num)
theorem B4659875 : Blo 2069435 4659875 := bstep (se 1 (by rfl) ⟨3494906, by rfl⟩ : syracuseStep 4659875 = 6989813) B6989813
theorem B3106583 : Blo 2069435 3106583 := bstep (se 1 (by rfl) ⟨2329937, by rfl⟩ : syracuseStep 3106583 = 4659875) B4659875
theorem B2071055 : Blo 2069435 2071055 := bstep (se 1 (by rfl) ⟨1553291, by rfl⟩ : syracuseStep 2071055 = 3106583) B3106583
theorem B3106589 : Blo 2069435 3106589 := bbase (se 3 (by rfl) ⟨582485, by rfl⟩ : syracuseStep 3106589 = 1164971) (by norm_num)
theorem B2071059 : Blo 2069435 2071059 := bstep (se 1 (by rfl) ⟨1553294, by rfl⟩ : syracuseStep 2071059 = 3106589) B3106589
theorem B4659893 : Blo 2069435 4659893 := bbase (se 5 (by rfl) ⟨218432, by rfl⟩ : syracuseStep 4659893 = 436865) (by norm_num)
theorem B3106595 : Blo 2069435 3106595 := bstep (se 1 (by rfl) ⟨2329946, by rfl⟩ : syracuseStep 3106595 = 4659893) B4659893
theorem B2071063 : Blo 2069435 2071063 := bstep (se 1 (by rfl) ⟨1553297, by rfl⟩ : syracuseStep 2071063 = 3106595) B3106595
theorem B11795381 : Blo 2069435 11795381 := bbase (se 5 (by rfl) ⟨552908, by rfl⟩ : syracuseStep 11795381 = 1105817) (by norm_num)
theorem B7863587 : Blo 2069435 7863587 := bstep (se 1 (by rfl) ⟨5897690, by rfl⟩ : syracuseStep 7863587 = 11795381) B11795381
theorem B5242391 : Blo 2069435 5242391 := bstep (se 1 (by rfl) ⟨3931793, by rfl⟩ : syracuseStep 5242391 = 7863587) B7863587
theorem B3494927 : Blo 2069435 3494927 := bstep (se 1 (by rfl) ⟨2621195, by rfl⟩ : syracuseStep 3494927 = 5242391) B5242391
theorem B2329951 : Blo 2069435 2329951 := bstep (se 1 (by rfl) ⟨1747463, by rfl⟩ : syracuseStep 2329951 = 3494927) B3494927
theorem B3106601 : Blo 2069435 3106601 := bstep (se 2 (by rfl) ⟨1164975, by rfl⟩ : syracuseStep 3106601 = 2329951) B2329951
theorem B2071067 : Blo 2069435 2071067 := bstep (se 1 (by rfl) ⟨1553300, by rfl⟩ : syracuseStep 2071067 = 3106601) B3106601
theorem B5897701 : Blo 2069435 5897701 := bbase (se 4 (by rfl) ⟨552909, by rfl⟩ : syracuseStep 5897701 = 1105819) (by norm_num)
theorem B7863601 : Blo 2069435 7863601 := bstep (se 2 (by rfl) ⟨2948850, by rfl⟩ : syracuseStep 7863601 = 5897701) B5897701
theorem B10484801 : Blo 2069435 10484801 := bstep (se 2 (by rfl) ⟨3931800, by rfl⟩ : syracuseStep 10484801 = 7863601) B7863601
theorem B6989867 : Blo 2069435 6989867 := bstep (se 1 (by rfl) ⟨5242400, by rfl⟩ : syracuseStep 6989867 = 10484801) B10484801
theorem B4659911 : Blo 2069435 4659911 := bstep (se 1 (by rfl) ⟨3494933, by rfl⟩ : syracuseStep 4659911 = 6989867) B6989867
theorem B3106607 : Blo 2069435 3106607 := bstep (se 1 (by rfl) ⟨2329955, by rfl⟩ : syracuseStep 3106607 = 4659911) B4659911
theorem B2071071 : Blo 2069435 2071071 := bstep (se 1 (by rfl) ⟨1553303, by rfl⟩ : syracuseStep 2071071 = 3106607) B3106607
theorem B3106613 : Blo 2069435 3106613 := bbase (se 5 (by rfl) ⟨145622, by rfl⟩ : syracuseStep 3106613 = 291245) (by norm_num)
theorem B2071075 : Blo 2069435 2071075 := bstep (se 1 (by rfl) ⟨1553306, by rfl⟩ : syracuseStep 2071075 = 3106613) B3106613
theorem B5242421 : Blo 2069435 5242421 := bbase (se 5 (by rfl) ⟨245738, by rfl⟩ : syracuseStep 5242421 = 491477) (by norm_num)
theorem B3494947 : Blo 2069435 3494947 := bstep (se 1 (by rfl) ⟨2621210, by rfl⟩ : syracuseStep 3494947 = 5242421) B5242421
theorem B4659929 : Blo 2069435 4659929 := bstep (se 2 (by rfl) ⟨1747473, by rfl⟩ : syracuseStep 4659929 = 3494947) B3494947
theorem B3106619 : Blo 2069435 3106619 := bstep (se 1 (by rfl) ⟨2329964, by rfl⟩ : syracuseStep 3106619 = 4659929) B4659929
theorem B2071079 : Blo 2069435 2071079 := bstep (se 1 (by rfl) ⟨1553309, by rfl⟩ : syracuseStep 2071079 = 3106619) B3106619
theorem B2329969 : Blo 2069435 2329969 := bbase (se 2 (by rfl) ⟨873738, by rfl⟩ : syracuseStep 2329969 = 1747477) (by norm_num)
theorem B3106625 : Blo 2069435 3106625 := bstep (se 2 (by rfl) ⟨1164984, by rfl⟩ : syracuseStep 3106625 = 2329969) B2329969
theorem B2071083 : Blo 2069435 2071083 := bstep (se 1 (by rfl) ⟨1553312, by rfl⟩ : syracuseStep 2071083 = 3106625) B3106625
theorem B6298037 : Blo 2069435 6298037 := bbase (se 5 (by rfl) ⟨295220, by rfl⟩ : syracuseStep 6298037 = 590441) (by norm_num)
theorem B4198691 : Blo 2069435 4198691 := bstep (se 1 (by rfl) ⟨3149018, by rfl⟩ : syracuseStep 4198691 = 6298037) B6298037
theorem B2799127 : Blo 2069435 2799127 := bstep (se 1 (by rfl) ⟨2099345, by rfl⟩ : syracuseStep 2799127 = 4198691) B4198691
theorem B3732169 : Blo 2069435 3732169 := bstep (se 2 (by rfl) ⟨1399563, by rfl⟩ : syracuseStep 3732169 = 2799127) B2799127
theorem B4976225 : Blo 2069435 4976225 := bstep (se 2 (by rfl) ⟨1866084, by rfl⟩ : syracuseStep 4976225 = 3732169) B3732169
theorem B3317483 : Blo 2069435 3317483 := bstep (se 1 (by rfl) ⟨2488112, by rfl⟩ : syracuseStep 3317483 = 4976225) B4976225
theorem B8846621 : Blo 2069435 8846621 := bstep (se 3 (by rfl) ⟨1658741, by rfl⟩ : syracuseStep 8846621 = 3317483) B3317483
theorem B5897747 : Blo 2069435 5897747 := bstep (se 1 (by rfl) ⟨4423310, by rfl⟩ : syracuseStep 5897747 = 8846621) B8846621
theorem B3931831 : Blo 2069435 3931831 := bstep (se 1 (by rfl) ⟨2948873, by rfl⟩ : syracuseStep 3931831 = 5897747) B5897747
theorem B5242441 : Blo 2069435 5242441 := bstep (se 2 (by rfl) ⟨1965915, by rfl⟩ : syracuseStep 5242441 = 3931831) B3931831
theorem B6989921 : Blo 2069435 6989921 := bstep (se 2 (by rfl) ⟨2621220, by rfl⟩ : syracuseStep 6989921 = 5242441) B5242441
theorem B4659947 : Blo 2069435 4659947 := bstep (se 1 (by rfl) ⟨3494960, by rfl⟩ : syracuseStep 4659947 = 6989921) B6989921
theorem B3106631 : Blo 2069435 3106631 := bstep (se 1 (by rfl) ⟨2329973, by rfl⟩ : syracuseStep 3106631 = 4659947) B4659947
theorem B2071087 : Blo 2069435 2071087 := bstep (se 1 (by rfl) ⟨1553315, by rfl⟩ : syracuseStep 2071087 = 3106631) B3106631
theorem B3106637 : Blo 2069435 3106637 := bbase (se 3 (by rfl) ⟨582494, by rfl⟩ : syracuseStep 3106637 = 1164989) (by norm_num)
theorem B2071091 : Blo 2069435 2071091 := bstep (se 1 (by rfl) ⟨1553318, by rfl⟩ : syracuseStep 2071091 = 3106637) B3106637
theorem B4659965 : Blo 2069435 4659965 := bbase (se 3 (by rfl) ⟨873743, by rfl⟩ : syracuseStep 4659965 = 1747487) (by norm_num)
theorem B3106643 : Blo 2069435 3106643 := bstep (se 1 (by rfl) ⟨2329982, by rfl⟩ : syracuseStep 3106643 = 4659965) B4659965
theorem B2071095 : Blo 2069435 2071095 := bstep (se 1 (by rfl) ⟨1553321, by rfl⟩ : syracuseStep 2071095 = 3106643) B3106643
theorem B3494981 : Blo 2069435 3494981 := bbase (se 4 (by rfl) ⟨327654, by rfl⟩ : syracuseStep 3494981 = 655309) (by norm_num)
theorem B2329987 : Blo 2069435 2329987 := bstep (se 1 (by rfl) ⟨1747490, by rfl⟩ : syracuseStep 2329987 = 3494981) B3494981
theorem B3106649 : Blo 2069435 3106649 := bstep (se 2 (by rfl) ⟨1164993, by rfl⟩ : syracuseStep 3106649 = 2329987) B2329987
theorem B2071099 : Blo 2069435 2071099 := bstep (se 1 (by rfl) ⟨1553324, by rfl⟩ : syracuseStep 2071099 = 3106649) B3106649
theorem B15727445 : Blo 2069435 15727445 := bbase (se 9 (by rfl) ⟨46076, by rfl⟩ : syracuseStep 15727445 = 92153) (by norm_num)
theorem B10484963 : Blo 2069435 10484963 := bstep (se 1 (by rfl) ⟨7863722, by rfl⟩ : syracuseStep 10484963 = 15727445) B15727445
theorem B6989975 : Blo 2069435 6989975 := bstep (se 1 (by rfl) ⟨5242481, by rfl⟩ : syracuseStep 6989975 = 10484963) B10484963
theorem B4659983 : Blo 2069435 4659983 := bstep (se 1 (by rfl) ⟨3494987, by rfl⟩ : syracuseStep 4659983 = 6989975) B6989975
theorem B3106655 : Blo 2069435 3106655 := bstep (se 1 (by rfl) ⟨2329991, by rfl⟩ : syracuseStep 3106655 = 4659983) B4659983
theorem B2071103 : Blo 2069435 2071103 := bstep (se 1 (by rfl) ⟨1553327, by rfl⟩ : syracuseStep 2071103 = 3106655) B3106655
theorem B3106661 : Blo 2069435 3106661 := bbase (se 4 (by rfl) ⟨291249, by rfl⟩ : syracuseStep 3106661 = 582499) (by norm_num)
theorem B2071107 : Blo 2069435 2071107 := bstep (se 1 (by rfl) ⟨1553330, by rfl⟩ : syracuseStep 2071107 = 3106661) B3106661
theorem B3931877 : Blo 2069435 3931877 := bbase (se 4 (by rfl) ⟨368613, by rfl⟩ : syracuseStep 3931877 = 737227) (by norm_num)
theorem B2621251 : Blo 2069435 2621251 := bstep (se 1 (by rfl) ⟨1965938, by rfl⟩ : syracuseStep 2621251 = 3931877) B3931877
theorem B3495001 : Blo 2069435 3495001 := bstep (se 2 (by rfl) ⟨1310625, by rfl⟩ : syracuseStep 3495001 = 2621251) B2621251
theorem B4660001 : Blo 2069435 4660001 := bstep (se 2 (by rfl) ⟨1747500, by rfl⟩ : syracuseStep 4660001 = 3495001) B3495001
theorem B3106667 : Blo 2069435 3106667 := bstep (se 1 (by rfl) ⟨2330000, by rfl⟩ : syracuseStep 3106667 = 4660001) B4660001
theorem B2071111 : Blo 2069435 2071111 := bstep (se 1 (by rfl) ⟨1553333, by rfl⟩ : syracuseStep 2071111 = 3106667) B3106667
theorem B2330005 : Blo 2069435 2330005 := bbase (se 6 (by rfl) ⟨54609, by rfl⟩ : syracuseStep 2330005 = 109219) (by norm_num)
theorem B3106673 : Blo 2069435 3106673 := bstep (se 2 (by rfl) ⟨1165002, by rfl⟩ : syracuseStep 3106673 = 2330005) B2330005
theorem B2071115 : Blo 2069435 2071115 := bstep (se 1 (by rfl) ⟨1553336, by rfl⟩ : syracuseStep 2071115 = 3106673) B3106673
theorem B2621261 : Blo 2069435 2621261 := bbase (se 3 (by rfl) ⟨491486, by rfl⟩ : syracuseStep 2621261 = 982973) (by norm_num)
theorem B6990029 : Blo 2069435 6990029 := bstep (se 3 (by rfl) ⟨1310630, by rfl⟩ : syracuseStep 6990029 = 2621261) B2621261
theorem B4660019 : Blo 2069435 4660019 := bstep (se 1 (by rfl) ⟨3495014, by rfl⟩ : syracuseStep 4660019 = 6990029) B6990029
theorem B3106679 : Blo 2069435 3106679 := bstep (se 1 (by rfl) ⟨2330009, by rfl⟩ : syracuseStep 3106679 = 4660019) B4660019
theorem B2071119 : Blo 2069435 2071119 := bstep (se 1 (by rfl) ⟨1553339, by rfl⟩ : syracuseStep 2071119 = 3106679) B3106679
theorem B3106685 : Blo 2069435 3106685 := bbase (se 3 (by rfl) ⟨582503, by rfl⟩ : syracuseStep 3106685 = 1165007) (by norm_num)
theorem B2071123 : Blo 2069435 2071123 := bstep (se 1 (by rfl) ⟨1553342, by rfl⟩ : syracuseStep 2071123 = 3106685) B3106685
theorem B4660037 : Blo 2069435 4660037 := bbase (se 4 (by rfl) ⟨436878, by rfl⟩ : syracuseStep 4660037 = 873757) (by norm_num)
theorem B3106691 : Blo 2069435 3106691 := bstep (se 1 (by rfl) ⟨2330018, by rfl⟩ : syracuseStep 3106691 = 4660037) B4660037
theorem B2071127 : Blo 2069435 2071127 := bstep (se 1 (by rfl) ⟨1553345, by rfl⟩ : syracuseStep 2071127 = 3106691) B3106691
theorem B4423405 : Blo 2069435 4423405 := bbase (se 3 (by rfl) ⟨829388, by rfl⟩ : syracuseStep 4423405 = 1658777) (by norm_num)
theorem B5897873 : Blo 2069435 5897873 := bstep (se 2 (by rfl) ⟨2211702, by rfl⟩ : syracuseStep 5897873 = 4423405) B4423405
theorem B3931915 : Blo 2069435 3931915 := bstep (se 1 (by rfl) ⟨2948936, by rfl⟩ : syracuseStep 3931915 = 5897873) B5897873
theorem B5242553 : Blo 2069435 5242553 := bstep (se 2 (by rfl) ⟨1965957, by rfl⟩ : syracuseStep 5242553 = 3931915) B3931915
theorem B3495035 : Blo 2069435 3495035 := bstep (se 1 (by rfl) ⟨2621276, by rfl⟩ : syracuseStep 3495035 = 5242553) B5242553
theorem B2330023 : Blo 2069435 2330023 := bstep (se 1 (by rfl) ⟨1747517, by rfl⟩ : syracuseStep 2330023 = 3495035) B3495035
theorem B3106697 : Blo 2069435 3106697 := bstep (se 2 (by rfl) ⟨1165011, by rfl⟩ : syracuseStep 3106697 = 2330023) B2330023
theorem B2071131 : Blo 2069435 2071131 := bstep (se 1 (by rfl) ⟨1553348, by rfl⟩ : syracuseStep 2071131 = 3106697) B3106697
theorem B10485125 : Blo 2069435 10485125 := bbase (se 4 (by rfl) ⟨982980, by rfl⟩ : syracuseStep 10485125 = 1965961) (by norm_num)
theorem B6990083 : Blo 2069435 6990083 := bstep (se 1 (by rfl) ⟨5242562, by rfl⟩ : syracuseStep 6990083 = 10485125) B10485125
theorem B4660055 : Blo 2069435 4660055 := bstep (se 1 (by rfl) ⟨3495041, by rfl⟩ : syracuseStep 4660055 = 6990083) B6990083
theorem B3106703 : Blo 2069435 3106703 := bstep (se 1 (by rfl) ⟨2330027, by rfl⟩ : syracuseStep 3106703 = 4660055) B4660055
theorem B2071135 : Blo 2069435 2071135 := bstep (se 1 (by rfl) ⟨1553351, by rfl⟩ : syracuseStep 2071135 = 3106703) B3106703
theorem B3106709 : Blo 2069435 3106709 := bbase (se 6 (by rfl) ⟨72813, by rfl⟩ : syracuseStep 3106709 = 145627) (by norm_num)
theorem B2071139 : Blo 2069435 2071139 := bstep (se 1 (by rfl) ⟨1553354, by rfl⟩ : syracuseStep 2071139 = 3106709) B3106709
theorem B3317573 : Blo 2069435 3317573 := bbase (se 4 (by rfl) ⟨311022, by rfl⟩ : syracuseStep 3317573 = 622045) (by norm_num)
theorem B2211715 : Blo 2069435 2211715 := bstep (se 1 (by rfl) ⟨1658786, by rfl⟩ : syracuseStep 2211715 = 3317573) B3317573
theorem B11795813 : Blo 2069435 11795813 := bstep (se 4 (by rfl) ⟨1105857, by rfl⟩ : syracuseStep 11795813 = 2211715) B2211715
theorem B7863875 : Blo 2069435 7863875 := bstep (se 1 (by rfl) ⟨5897906, by rfl⟩ : syracuseStep 7863875 = 11795813) B11795813
theorem B5242583 : Blo 2069435 5242583 := bstep (se 1 (by rfl) ⟨3931937, by rfl⟩ : syracuseStep 5242583 = 7863875) B7863875
theorem B3495055 : Blo 2069435 3495055 := bstep (se 1 (by rfl) ⟨2621291, by rfl⟩ : syracuseStep 3495055 = 5242583) B5242583
theorem B4660073 : Blo 2069435 4660073 := bstep (se 2 (by rfl) ⟨1747527, by rfl⟩ : syracuseStep 4660073 = 3495055) B3495055
theorem B3106715 : Blo 2069435 3106715 := bstep (se 1 (by rfl) ⟨2330036, by rfl⟩ : syracuseStep 3106715 = 4660073) B4660073
theorem B2071143 : Blo 2069435 2071143 := bstep (se 1 (by rfl) ⟨1553357, by rfl⟩ : syracuseStep 2071143 = 3106715) B3106715
theorem B2330041 : Blo 2069435 2330041 := bbase (se 2 (by rfl) ⟨873765, by rfl⟩ : syracuseStep 2330041 = 1747531) (by norm_num)
theorem B3106721 : Blo 2069435 3106721 := bstep (se 2 (by rfl) ⟨1165020, by rfl⟩ : syracuseStep 3106721 = 2330041) B2330041
theorem B2071147 : Blo 2069435 2071147 := bstep (se 1 (by rfl) ⟨1553360, by rfl⟩ : syracuseStep 2071147 = 3106721) B3106721
theorem B9952757 : Blo 2069435 9952757 := bbase (se 5 (by rfl) ⟨466535, by rfl⟩ : syracuseStep 9952757 = 933071) (by norm_num)
theorem B6635171 : Blo 2069435 6635171 := bstep (se 1 (by rfl) ⟨4976378, by rfl⟩ : syracuseStep 6635171 = 9952757) B9952757
theorem B4423447 : Blo 2069435 4423447 := bstep (se 1 (by rfl) ⟨3317585, by rfl⟩ : syracuseStep 4423447 = 6635171) B6635171
theorem B5897929 : Blo 2069435 5897929 := bstep (se 2 (by rfl) ⟨2211723, by rfl⟩ : syracuseStep 5897929 = 4423447) B4423447
theorem B7863905 : Blo 2069435 7863905 := bstep (se 2 (by rfl) ⟨2948964, by rfl⟩ : syracuseStep 7863905 = 5897929) B5897929
theorem B5242603 : Blo 2069435 5242603 := bstep (se 1 (by rfl) ⟨3931952, by rfl⟩ : syracuseStep 5242603 = 7863905) B7863905
theorem B6990137 : Blo 2069435 6990137 := bstep (se 2 (by rfl) ⟨2621301, by rfl⟩ : syracuseStep 6990137 = 5242603) B5242603
theorem B4660091 : Blo 2069435 4660091 := bstep (se 1 (by rfl) ⟨3495068, by rfl⟩ : syracuseStep 4660091 = 6990137) B6990137
theorem B3106727 : Blo 2069435 3106727 := bstep (se 1 (by rfl) ⟨2330045, by rfl⟩ : syracuseStep 3106727 = 4660091) B4660091
theorem B2071151 : Blo 2069435 2071151 := bstep (se 1 (by rfl) ⟨1553363, by rfl⟩ : syracuseStep 2071151 = 3106727) B3106727
theorem B3106733 : Blo 2069435 3106733 := bbase (se 3 (by rfl) ⟨582512, by rfl⟩ : syracuseStep 3106733 = 1165025) (by norm_num)
theorem B2071155 : Blo 2069435 2071155 := bstep (se 1 (by rfl) ⟨1553366, by rfl⟩ : syracuseStep 2071155 = 3106733) B3106733
theorem B4660109 : Blo 2069435 4660109 := bbase (se 3 (by rfl) ⟨873770, by rfl⟩ : syracuseStep 4660109 = 1747541) (by norm_num)
theorem B3106739 : Blo 2069435 3106739 := bstep (se 1 (by rfl) ⟨2330054, by rfl⟩ : syracuseStep 3106739 = 4660109) B4660109
theorem B2071159 : Blo 2069435 2071159 := bstep (se 1 (by rfl) ⟨1553369, by rfl⟩ : syracuseStep 2071159 = 3106739) B3106739
theorem B2621317 : Blo 2069435 2621317 := bbase (se 4 (by rfl) ⟨245748, by rfl⟩ : syracuseStep 2621317 = 491497) (by norm_num)
theorem B3495089 : Blo 2069435 3495089 := bstep (se 2 (by rfl) ⟨1310658, by rfl⟩ : syracuseStep 3495089 = 2621317) B2621317
theorem B2330059 : Blo 2069435 2330059 := bstep (se 1 (by rfl) ⟨1747544, by rfl⟩ : syracuseStep 2330059 = 3495089) B3495089
theorem B3106745 : Blo 2069435 3106745 := bstep (se 2 (by rfl) ⟨1165029, by rfl⟩ : syracuseStep 3106745 = 2330059) B2330059
theorem B2071163 : Blo 2069435 2071163 := bstep (se 1 (by rfl) ⟨1553372, by rfl⟩ : syracuseStep 2071163 = 3106745) B3106745
theorem B26540885 : Blo 2069435 26540885 := bbase (se 9 (by rfl) ⟨77756, by rfl⟩ : syracuseStep 26540885 = 155513) (by norm_num)
theorem B17693923 : Blo 2069435 17693923 := bstep (se 1 (by rfl) ⟨13270442, by rfl⟩ : syracuseStep 17693923 = 26540885) B26540885
theorem B23591897 : Blo 2069435 23591897 := bstep (se 2 (by rfl) ⟨8846961, by rfl⟩ : syracuseStep 23591897 = 17693923) B17693923
theorem B15727931 : Blo 2069435 15727931 := bstep (se 1 (by rfl) ⟨11795948, by rfl⟩ : syracuseStep 15727931 = 23591897) B23591897
theorem B10485287 : Blo 2069435 10485287 := bstep (se 1 (by rfl) ⟨7863965, by rfl⟩ : syracuseStep 10485287 = 15727931) B15727931
theorem B6990191 : Blo 2069435 6990191 := bstep (se 1 (by rfl) ⟨5242643, by rfl⟩ : syracuseStep 6990191 = 10485287) B10485287
theorem B4660127 : Blo 2069435 4660127 := bstep (se 1 (by rfl) ⟨3495095, by rfl⟩ : syracuseStep 4660127 = 6990191) B6990191
theorem B3106751 : Blo 2069435 3106751 := bstep (se 1 (by rfl) ⟨2330063, by rfl⟩ : syracuseStep 3106751 = 4660127) B4660127
theorem B2071167 : Blo 2069435 2071167 := bstep (se 1 (by rfl) ⟨1553375, by rfl⟩ : syracuseStep 2071167 = 3106751) B3106751
theorem B3106757 : Blo 2069435 3106757 := bbase (se 4 (by rfl) ⟨291258, by rfl⟩ : syracuseStep 3106757 = 582517) (by norm_num)
theorem B2071171 : Blo 2069435 2071171 := bstep (se 1 (by rfl) ⟨1553378, by rfl⟩ : syracuseStep 2071171 = 3106757) B3106757
theorem B3495109 : Blo 2069435 3495109 := bbase (se 4 (by rfl) ⟨327666, by rfl⟩ : syracuseStep 3495109 = 655333) (by norm_num)
theorem B4660145 : Blo 2069435 4660145 := bstep (se 2 (by rfl) ⟨1747554, by rfl⟩ : syracuseStep 4660145 = 3495109) B3495109
theorem B3106763 : Blo 2069435 3106763 := bstep (se 1 (by rfl) ⟨2330072, by rfl⟩ : syracuseStep 3106763 = 4660145) B4660145
theorem B2071175 : Blo 2069435 2071175 := bstep (se 1 (by rfl) ⟨1553381, by rfl⟩ : syracuseStep 2071175 = 3106763) B3106763
theorem B2330077 : Blo 2069435 2330077 := bbase (se 3 (by rfl) ⟨436889, by rfl⟩ : syracuseStep 2330077 = 873779) (by norm_num)
theorem B3106769 : Blo 2069435 3106769 := bstep (se 2 (by rfl) ⟨1165038, by rfl⟩ : syracuseStep 3106769 = 2330077) B2330077
theorem B2071179 : Blo 2069435 2071179 := bstep (se 1 (by rfl) ⟨1553384, by rfl⟩ : syracuseStep 2071179 = 3106769) B3106769
theorem B6990245 : Blo 2069435 6990245 := bbase (se 4 (by rfl) ⟨655335, by rfl⟩ : syracuseStep 6990245 = 1310671) (by norm_num)
theorem B4660163 : Blo 2069435 4660163 := bstep (se 1 (by rfl) ⟨3495122, by rfl⟩ : syracuseStep 4660163 = 6990245) B6990245
theorem B3106775 : Blo 2069435 3106775 := bstep (se 1 (by rfl) ⟨2330081, by rfl⟩ : syracuseStep 3106775 = 4660163) B4660163
theorem B2071183 : Blo 2069435 2071183 := bstep (se 1 (by rfl) ⟨1553387, by rfl⟩ : syracuseStep 2071183 = 3106775) B3106775
theorem B3106781 : Blo 2069435 3106781 := bbase (se 3 (by rfl) ⟨582521, by rfl⟩ : syracuseStep 3106781 = 1165043) (by norm_num)
theorem B2071187 : Blo 2069435 2071187 := bstep (se 1 (by rfl) ⟨1553390, by rfl⟩ : syracuseStep 2071187 = 3106781) B3106781
theorem B4660181 : Blo 2069435 4660181 := bbase (se 7 (by rfl) ⟨54611, by rfl⟩ : syracuseStep 4660181 = 109223) (by norm_num)
theorem B3106787 : Blo 2069435 3106787 := bstep (se 1 (by rfl) ⟨2330090, by rfl⟩ : syracuseStep 3106787 = 4660181) B4660181
theorem B2071191 : Blo 2069435 2071191 := bstep (se 1 (by rfl) ⟨1553393, by rfl⟩ : syracuseStep 2071191 = 3106787) B3106787
theorem B16795637 : Blo 2069435 16795637 := bbase (se 5 (by rfl) ⟨787295, by rfl⟩ : syracuseStep 16795637 = 1574591) (by norm_num)
theorem B11197091 : Blo 2069435 11197091 := bstep (se 1 (by rfl) ⟨8397818, by rfl⟩ : syracuseStep 11197091 = 16795637) B16795637
theorem B7464727 : Blo 2069435 7464727 := bstep (se 1 (by rfl) ⟨5598545, by rfl⟩ : syracuseStep 7464727 = 11197091) B11197091
theorem B9952969 : Blo 2069435 9952969 := bstep (se 2 (by rfl) ⟨3732363, by rfl⟩ : syracuseStep 9952969 = 7464727) B7464727
theorem B13270625 : Blo 2069435 13270625 := bstep (se 2 (by rfl) ⟨4976484, by rfl⟩ : syracuseStep 13270625 = 9952969) B9952969
theorem B8847083 : Blo 2069435 8847083 := bstep (se 1 (by rfl) ⟨6635312, by rfl⟩ : syracuseStep 8847083 = 13270625) B13270625
theorem B5898055 : Blo 2069435 5898055 := bstep (se 1 (by rfl) ⟨4423541, by rfl⟩ : syracuseStep 5898055 = 8847083) B8847083
theorem B7864073 : Blo 2069435 7864073 := bstep (se 2 (by rfl) ⟨2949027, by rfl⟩ : syracuseStep 7864073 = 5898055) B5898055
theorem B5242715 : Blo 2069435 5242715 := bstep (se 1 (by rfl) ⟨3932036, by rfl⟩ : syracuseStep 5242715 = 7864073) B7864073
theorem B3495143 : Blo 2069435 3495143 := bstep (se 1 (by rfl) ⟨2621357, by rfl⟩ : syracuseStep 3495143 = 5242715) B5242715
theorem B2330095 : Blo 2069435 2330095 := bstep (se 1 (by rfl) ⟨1747571, by rfl⟩ : syracuseStep 2330095 = 3495143) B3495143
theorem B3106793 : Blo 2069435 3106793 := bstep (se 2 (by rfl) ⟨1165047, by rfl⟩ : syracuseStep 3106793 = 2330095) B2330095
theorem B2071195 : Blo 2069435 2071195 := bstep (se 1 (by rfl) ⟨1553396, by rfl⟩ : syracuseStep 2071195 = 3106793) B3106793
theorem B17694197 : Blo 2069435 17694197 := bbase (se 5 (by rfl) ⟨829415, by rfl⟩ : syracuseStep 17694197 = 1658831) (by norm_num)
theorem B11796131 : Blo 2069435 11796131 := bstep (se 1 (by rfl) ⟨8847098, by rfl⟩ : syracuseStep 11796131 = 17694197) B17694197
theorem B7864087 : Blo 2069435 7864087 := bstep (se 1 (by rfl) ⟨5898065, by rfl⟩ : syracuseStep 7864087 = 11796131) B11796131
theorem B10485449 : Blo 2069435 10485449 := bstep (se 2 (by rfl) ⟨3932043, by rfl⟩ : syracuseStep 10485449 = 7864087) B7864087
theorem B6990299 : Blo 2069435 6990299 := bstep (se 1 (by rfl) ⟨5242724, by rfl⟩ : syracuseStep 6990299 = 10485449) B10485449
theorem B4660199 : Blo 2069435 4660199 := bstep (se 1 (by rfl) ⟨3495149, by rfl⟩ : syracuseStep 4660199 = 6990299) B6990299
theorem B3106799 : Blo 2069435 3106799 := bstep (se 1 (by rfl) ⟨2330099, by rfl⟩ : syracuseStep 3106799 = 4660199) B4660199
theorem B2071199 : Blo 2069435 2071199 := bstep (se 1 (by rfl) ⟨1553399, by rfl⟩ : syracuseStep 2071199 = 3106799) B3106799
theorem B3106805 : Blo 2069435 3106805 := bbase (se 5 (by rfl) ⟨145631, by rfl⟩ : syracuseStep 3106805 = 291263) (by norm_num)
theorem B2071203 : Blo 2069435 2071203 := bstep (se 1 (by rfl) ⟨1553402, by rfl⟩ : syracuseStep 2071203 = 3106805) B3106805
theorem B2361901 : Blo 2069435 2361901 := bbase (se 3 (by rfl) ⟨442856, by rfl⟩ : syracuseStep 2361901 = 885713) (by norm_num)
theorem B3149201 : Blo 2069435 3149201 := bstep (se 2 (by rfl) ⟨1180950, by rfl⟩ : syracuseStep 3149201 = 2361901) B2361901
theorem B2099467 : Blo 2069435 2099467 := bstep (se 1 (by rfl) ⟨1574600, by rfl⟩ : syracuseStep 2099467 = 3149201) B3149201
theorem B2799289 : Blo 2069435 2799289 := bstep (se 2 (by rfl) ⟨1049733, by rfl⟩ : syracuseStep 2799289 = 2099467) B2099467
theorem B14929541 : Blo 2069435 14929541 := bstep (se 4 (by rfl) ⟨1399644, by rfl⟩ : syracuseStep 14929541 = 2799289) B2799289
theorem B9953027 : Blo 2069435 9953027 := bstep (se 1 (by rfl) ⟨7464770, by rfl⟩ : syracuseStep 9953027 = 14929541) B14929541
theorem B6635351 : Blo 2069435 6635351 := bstep (se 1 (by rfl) ⟨4976513, by rfl⟩ : syracuseStep 6635351 = 9953027) B9953027
theorem B4423567 : Blo 2069435 4423567 := bstep (se 1 (by rfl) ⟨3317675, by rfl⟩ : syracuseStep 4423567 = 6635351) B6635351
theorem B5898089 : Blo 2069435 5898089 := bstep (se 2 (by rfl) ⟨2211783, by rfl⟩ : syracuseStep 5898089 = 4423567) B4423567
theorem B3932059 : Blo 2069435 3932059 := bstep (se 1 (by rfl) ⟨2949044, by rfl⟩ : syracuseStep 3932059 = 5898089) B5898089
theorem B5242745 : Blo 2069435 5242745 := bstep (se 2 (by rfl) ⟨1966029, by rfl⟩ : syracuseStep 5242745 = 3932059) B3932059
theorem B3495163 : Blo 2069435 3495163 := bstep (se 1 (by rfl) ⟨2621372, by rfl⟩ : syracuseStep 3495163 = 5242745) B5242745
theorem B4660217 : Blo 2069435 4660217 := bstep (se 2 (by rfl) ⟨1747581, by rfl⟩ : syracuseStep 4660217 = 3495163) B3495163
theorem B3106811 : Blo 2069435 3106811 := bstep (se 1 (by rfl) ⟨2330108, by rfl⟩ : syracuseStep 3106811 = 4660217) B4660217
theorem B2071207 : Blo 2069435 2071207 := bstep (se 1 (by rfl) ⟨1553405, by rfl⟩ : syracuseStep 2071207 = 3106811) B3106811
theorem B2330113 : Blo 2069435 2330113 := bbase (se 2 (by rfl) ⟨873792, by rfl⟩ : syracuseStep 2330113 = 1747585) (by norm_num)
theorem B3106817 : Blo 2069435 3106817 := bstep (se 2 (by rfl) ⟨1165056, by rfl⟩ : syracuseStep 3106817 = 2330113) B2330113
theorem B2071211 : Blo 2069435 2071211 := bstep (se 1 (by rfl) ⟨1553408, by rfl⟩ : syracuseStep 2071211 = 3106817) B3106817
theorem B5242765 : Blo 2069435 5242765 := bbase (se 3 (by rfl) ⟨983018, by rfl⟩ : syracuseStep 5242765 = 1966037) (by norm_num)
theorem B6990353 : Blo 2069435 6990353 := bstep (se 2 (by rfl) ⟨2621382, by rfl⟩ : syracuseStep 6990353 = 5242765) B5242765
theorem B4660235 : Blo 2069435 4660235 := bstep (se 1 (by rfl) ⟨3495176, by rfl⟩ : syracuseStep 4660235 = 6990353) B6990353
theorem B3106823 : Blo 2069435 3106823 := bstep (se 1 (by rfl) ⟨2330117, by rfl⟩ : syracuseStep 3106823 = 4660235) B4660235
theorem B2071215 : Blo 2069435 2071215 := bstep (se 1 (by rfl) ⟨1553411, by rfl⟩ : syracuseStep 2071215 = 3106823) B3106823
theorem B3106829 : Blo 2069435 3106829 := bbase (se 3 (by rfl) ⟨582530, by rfl⟩ : syracuseStep 3106829 = 1165061) (by norm_num)
theorem B2071219 : Blo 2069435 2071219 := bstep (se 1 (by rfl) ⟨1553414, by rfl⟩ : syracuseStep 2071219 = 3106829) B3106829
theorem B4660253 : Blo 2069435 4660253 := bbase (se 3 (by rfl) ⟨873797, by rfl⟩ : syracuseStep 4660253 = 1747595) (by norm_num)
theorem B3106835 : Blo 2069435 3106835 := bstep (se 1 (by rfl) ⟨2330126, by rfl⟩ : syracuseStep 3106835 = 4660253) B4660253
theorem B2071223 : Blo 2069435 2071223 := bstep (se 1 (by rfl) ⟨1553417, by rfl⟩ : syracuseStep 2071223 = 3106835) B3106835
theorem B3495197 : Blo 2069435 3495197 := bbase (se 3 (by rfl) ⟨655349, by rfl⟩ : syracuseStep 3495197 = 1310699) (by norm_num)
theorem B2330131 : Blo 2069435 2330131 := bstep (se 1 (by rfl) ⟨1747598, by rfl⟩ : syracuseStep 2330131 = 3495197) B3495197
theorem B3106841 : Blo 2069435 3106841 := bstep (se 2 (by rfl) ⟨1165065, by rfl⟩ : syracuseStep 3106841 = 2330131) B2330131
theorem B2071227 : Blo 2069435 2071227 := bstep (se 1 (by rfl) ⟨1553420, by rfl⟩ : syracuseStep 2071227 = 3106841) B3106841
theorem B2488285 : Blo 2069435 2488285 := bbase (se 3 (by rfl) ⟨466553, by rfl⟩ : syracuseStep 2488285 = 933107) (by norm_num)
theorem B13270853 : Blo 2069435 13270853 := bstep (se 4 (by rfl) ⟨1244142, by rfl⟩ : syracuseStep 13270853 = 2488285) B2488285
theorem B8847235 : Blo 2069435 8847235 := bstep (se 1 (by rfl) ⟨6635426, by rfl⟩ : syracuseStep 8847235 = 13270853) B13270853
theorem B11796313 : Blo 2069435 11796313 := bstep (se 2 (by rfl) ⟨4423617, by rfl⟩ : syracuseStep 11796313 = 8847235) B8847235
theorem B15728417 : Blo 2069435 15728417 := bstep (se 2 (by rfl) ⟨5898156, by rfl⟩ : syracuseStep 15728417 = 11796313) B11796313
theorem B10485611 : Blo 2069435 10485611 := bstep (se 1 (by rfl) ⟨7864208, by rfl⟩ : syracuseStep 10485611 = 15728417) B15728417
theorem B6990407 : Blo 2069435 6990407 := bstep (se 1 (by rfl) ⟨5242805, by rfl⟩ : syracuseStep 6990407 = 10485611) B10485611
theorem B4660271 : Blo 2069435 4660271 := bstep (se 1 (by rfl) ⟨3495203, by rfl⟩ : syracuseStep 4660271 = 6990407) B6990407
theorem B3106847 : Blo 2069435 3106847 := bstep (se 1 (by rfl) ⟨2330135, by rfl⟩ : syracuseStep 3106847 = 4660271) B4660271
theorem B2071231 : Blo 2069435 2071231 := bstep (se 1 (by rfl) ⟨1553423, by rfl⟩ : syracuseStep 2071231 = 3106847) B3106847
theorem B3106853 : Blo 2069435 3106853 := bbase (se 4 (by rfl) ⟨291267, by rfl⟩ : syracuseStep 3106853 = 582535) (by norm_num)
theorem B2071235 : Blo 2069435 2071235 := bstep (se 1 (by rfl) ⟨1553426, by rfl⟩ : syracuseStep 2071235 = 3106853) B3106853
theorem B2621413 : Blo 2069435 2621413 := bbase (se 4 (by rfl) ⟨245757, by rfl⟩ : syracuseStep 2621413 = 491515) (by norm_num)
theorem B3495217 : Blo 2069435 3495217 := bstep (se 2 (by rfl) ⟨1310706, by rfl⟩ : syracuseStep 3495217 = 2621413) B2621413
theorem B4660289 : Blo 2069435 4660289 := bstep (se 2 (by rfl) ⟨1747608, by rfl⟩ : syracuseStep 4660289 = 3495217) B3495217
theorem B3106859 : Blo 2069435 3106859 := bstep (se 1 (by rfl) ⟨2330144, by rfl⟩ : syracuseStep 3106859 = 4660289) B4660289
theorem B2071239 : Blo 2069435 2071239 := bstep (se 1 (by rfl) ⟨1553429, by rfl⟩ : syracuseStep 2071239 = 3106859) B3106859
theorem B2330149 : Blo 2069435 2330149 := bbase (se 4 (by rfl) ⟨218451, by rfl⟩ : syracuseStep 2330149 = 436903) (by norm_num)
theorem B3106865 : Blo 2069435 3106865 := bstep (se 2 (by rfl) ⟨1165074, by rfl⟩ : syracuseStep 3106865 = 2330149) B2330149
theorem B2071243 : Blo 2069435 2071243 := bstep (se 1 (by rfl) ⟨1553432, by rfl⟩ : syracuseStep 2071243 = 3106865) B3106865
theorem B23914709 : Blo 2069435 23914709 := bbase (se 7 (by rfl) ⟨280250, by rfl⟩ : syracuseStep 23914709 = 560501) (by norm_num)
theorem B15943139 : Blo 2069435 15943139 := bstep (se 1 (by rfl) ⟨11957354, by rfl⟩ : syracuseStep 15943139 = 23914709) B23914709
theorem B10628759 : Blo 2069435 10628759 := bstep (se 1 (by rfl) ⟨7971569, by rfl⟩ : syracuseStep 10628759 = 15943139) B15943139
theorem B7085839 : Blo 2069435 7085839 := bstep (se 1 (by rfl) ⟨5314379, by rfl⟩ : syracuseStep 7085839 = 10628759) B10628759
theorem B9447785 : Blo 2069435 9447785 := bstep (se 2 (by rfl) ⟨3542919, by rfl⟩ : syracuseStep 9447785 = 7085839) B7085839
theorem B6298523 : Blo 2069435 6298523 := bstep (se 1 (by rfl) ⟨4723892, by rfl⟩ : syracuseStep 6298523 = 9447785) B9447785
theorem B4199015 : Blo 2069435 4199015 := bstep (se 1 (by rfl) ⟨3149261, by rfl⟩ : syracuseStep 4199015 = 6298523) B6298523
theorem B2799343 : Blo 2069435 2799343 := bstep (se 1 (by rfl) ⟨2099507, by rfl⟩ : syracuseStep 2799343 = 4199015) B4199015
theorem B14929829 : Blo 2069435 14929829 := bstep (se 4 (by rfl) ⟨1399671, by rfl⟩ : syracuseStep 14929829 = 2799343) B2799343
theorem B9953219 : Blo 2069435 9953219 := bstep (se 1 (by rfl) ⟨7464914, by rfl⟩ : syracuseStep 9953219 = 14929829) B14929829
theorem B6635479 : Blo 2069435 6635479 := bstep (se 1 (by rfl) ⟨4976609, by rfl⟩ : syracuseStep 6635479 = 9953219) B9953219
theorem B8847305 : Blo 2069435 8847305 := bstep (se 2 (by rfl) ⟨3317739, by rfl⟩ : syracuseStep 8847305 = 6635479) B6635479
theorem B5898203 : Blo 2069435 5898203 := bstep (se 1 (by rfl) ⟨4423652, by rfl⟩ : syracuseStep 5898203 = 8847305) B8847305
theorem B3932135 : Blo 2069435 3932135 := bstep (se 1 (by rfl) ⟨2949101, by rfl⟩ : syracuseStep 3932135 = 5898203) B5898203
theorem B2621423 : Blo 2069435 2621423 := bstep (se 1 (by rfl) ⟨1966067, by rfl⟩ : syracuseStep 2621423 = 3932135) B3932135
theorem B6990461 : Blo 2069435 6990461 := bstep (se 3 (by rfl) ⟨1310711, by rfl⟩ : syracuseStep 6990461 = 2621423) B2621423
theorem B4660307 : Blo 2069435 4660307 := bstep (se 1 (by rfl) ⟨3495230, by rfl⟩ : syracuseStep 4660307 = 6990461) B6990461
theorem B3106871 : Blo 2069435 3106871 := bstep (se 1 (by rfl) ⟨2330153, by rfl⟩ : syracuseStep 3106871 = 4660307) B4660307
theorem B2071247 : Blo 2069435 2071247 := bstep (se 1 (by rfl) ⟨1553435, by rfl⟩ : syracuseStep 2071247 = 3106871) B3106871
theorem B3106877 : Blo 2069435 3106877 := bbase (se 3 (by rfl) ⟨582539, by rfl⟩ : syracuseStep 3106877 = 1165079) (by norm_num)
theorem B2071251 : Blo 2069435 2071251 := bstep (se 1 (by rfl) ⟨1553438, by rfl⟩ : syracuseStep 2071251 = 3106877) B3106877
theorem B4660325 : Blo 2069435 4660325 := bbase (se 4 (by rfl) ⟨436905, by rfl⟩ : syracuseStep 4660325 = 873811) (by norm_num)
theorem B3106883 : Blo 2069435 3106883 := bstep (se 1 (by rfl) ⟨2330162, by rfl⟩ : syracuseStep 3106883 = 4660325) B4660325
theorem B2071255 : Blo 2069435 2071255 := bstep (se 1 (by rfl) ⟨1553441, by rfl⟩ : syracuseStep 2071255 = 3106883) B3106883
theorem B5242877 : Blo 2069435 5242877 := bbase (se 3 (by rfl) ⟨983039, by rfl⟩ : syracuseStep 5242877 = 1966079) (by norm_num)
theorem B3495251 : Blo 2069435 3495251 := bstep (se 1 (by rfl) ⟨2621438, by rfl⟩ : syracuseStep 3495251 = 5242877) B5242877
theorem B2330167 : Blo 2069435 2330167 := bstep (se 1 (by rfl) ⟨1747625, by rfl⟩ : syracuseStep 2330167 = 3495251) B3495251
theorem B3106889 : Blo 2069435 3106889 := bstep (se 2 (by rfl) ⟨1165083, by rfl⟩ : syracuseStep 3106889 = 2330167) B2330167
theorem B2071259 : Blo 2069435 2071259 := bstep (se 1 (by rfl) ⟨1553444, by rfl⟩ : syracuseStep 2071259 = 3106889) B3106889
theorem B3932165 : Blo 2069435 3932165 := bbase (se 4 (by rfl) ⟨368640, by rfl⟩ : syracuseStep 3932165 = 737281) (by norm_num)
theorem B10485773 : Blo 2069435 10485773 := bstep (se 3 (by rfl) ⟨1966082, by rfl⟩ : syracuseStep 10485773 = 3932165) B3932165
theorem B6990515 : Blo 2069435 6990515 := bstep (se 1 (by rfl) ⟨5242886, by rfl⟩ : syracuseStep 6990515 = 10485773) B10485773
theorem B4660343 : Blo 2069435 4660343 := bstep (se 1 (by rfl) ⟨3495257, by rfl⟩ : syracuseStep 4660343 = 6990515) B6990515
theorem B3106895 : Blo 2069435 3106895 := bstep (se 1 (by rfl) ⟨2330171, by rfl⟩ : syracuseStep 3106895 = 4660343) B4660343
theorem B2071263 : Blo 2069435 2071263 := bstep (se 1 (by rfl) ⟨1553447, by rfl⟩ : syracuseStep 2071263 = 3106895) B3106895
theorem B3106901 : Blo 2069435 3106901 := bbase (se 8 (by rfl) ⟨18204, by rfl⟩ : syracuseStep 3106901 = 36409) (by norm_num)
theorem B2071267 : Blo 2069435 2071267 := bstep (se 1 (by rfl) ⟨1553450, by rfl⟩ : syracuseStep 2071267 = 3106901) B3106901
theorem B4788397 : Blo 2069435 4788397 := bbase (se 3 (by rfl) ⟨897824, by rfl⟩ : syracuseStep 4788397 = 1795649) (by norm_num)
theorem B6384529 : Blo 2069435 6384529 := bstep (se 2 (by rfl) ⟨2394198, by rfl⟩ : syracuseStep 6384529 = 4788397) B4788397
theorem B8512705 : Blo 2069435 8512705 := bstep (se 2 (by rfl) ⟨3192264, by rfl⟩ : syracuseStep 8512705 = 6384529) B6384529
theorem B11350273 : Blo 2069435 11350273 := bstep (se 2 (by rfl) ⟨4256352, by rfl⟩ : syracuseStep 11350273 = 8512705) B8512705
theorem B15133697 : Blo 2069435 15133697 := bstep (se 2 (by rfl) ⟨5675136, by rfl⟩ : syracuseStep 15133697 = 11350273) B11350273
theorem B10089131 : Blo 2069435 10089131 := bstep (se 1 (by rfl) ⟨7566848, by rfl⟩ : syracuseStep 10089131 = 15133697) B15133697
theorem B26904349 : Blo 2069435 26904349 := bstep (se 3 (by rfl) ⟨5044565, by rfl⟩ : syracuseStep 26904349 = 10089131) B10089131
theorem B35872465 : Blo 2069435 35872465 := bstep (se 2 (by rfl) ⟨13452174, by rfl⟩ : syracuseStep 35872465 = 26904349) B26904349
theorem B47829953 : Blo 2069435 47829953 := bstep (se 2 (by rfl) ⟨17936232, by rfl⟩ : syracuseStep 47829953 = 35872465) B35872465
theorem B31886635 : Blo 2069435 31886635 := bstep (se 1 (by rfl) ⟨23914976, by rfl⟩ : syracuseStep 31886635 = 47829953) B47829953
theorem B42515513 : Blo 2069435 42515513 := bstep (se 2 (by rfl) ⟨15943317, by rfl⟩ : syracuseStep 42515513 = 31886635) B31886635
theorem B28343675 : Blo 2069435 28343675 := bstep (se 1 (by rfl) ⟨21257756, by rfl⟩ : syracuseStep 28343675 = 42515513) B42515513
theorem B18895783 : Blo 2069435 18895783 := bstep (se 1 (by rfl) ⟨14171837, by rfl⟩ : syracuseStep 18895783 = 28343675) B28343675
theorem B25194377 : Blo 2069435 25194377 := bstep (se 2 (by rfl) ⟨9447891, by rfl⟩ : syracuseStep 25194377 = 18895783) B18895783
theorem B16796251 : Blo 2069435 16796251 := bstep (se 1 (by rfl) ⟨12597188, by rfl⟩ : syracuseStep 16796251 = 25194377) B25194377
theorem B22395001 : Blo 2069435 22395001 := bstep (se 2 (by rfl) ⟨8398125, by rfl⟩ : syracuseStep 22395001 = 16796251) B16796251
theorem B29860001 : Blo 2069435 29860001 := bstep (se 2 (by rfl) ⟨11197500, by rfl⟩ : syracuseStep 29860001 = 22395001) B22395001
theorem B19906667 : Blo 2069435 19906667 := bstep (se 1 (by rfl) ⟨14930000, by rfl⟩ : syracuseStep 19906667 = 29860001) B29860001
theorem B13271111 : Blo 2069435 13271111 := bstep (se 1 (by rfl) ⟨9953333, by rfl⟩ : syracuseStep 13271111 = 19906667) B19906667
theorem B8847407 : Blo 2069435 8847407 := bstep (se 1 (by rfl) ⟨6635555, by rfl⟩ : syracuseStep 8847407 = 13271111) B13271111
theorem B5898271 : Blo 2069435 5898271 := bstep (se 1 (by rfl) ⟨4423703, by rfl⟩ : syracuseStep 5898271 = 8847407) B8847407
theorem B7864361 : Blo 2069435 7864361 := bstep (se 2 (by rfl) ⟨2949135, by rfl⟩ : syracuseStep 7864361 = 5898271) B5898271
theorem B5242907 : Blo 2069435 5242907 := bstep (se 1 (by rfl) ⟨3932180, by rfl⟩ : syracuseStep 5242907 = 7864361) B7864361
theorem B3495271 : Blo 2069435 3495271 := bstep (se 1 (by rfl) ⟨2621453, by rfl⟩ : syracuseStep 3495271 = 5242907) B5242907
theorem B4660361 : Blo 2069435 4660361 := bstep (se 2 (by rfl) ⟨1747635, by rfl⟩ : syracuseStep 4660361 = 3495271) B3495271
theorem B3106907 : Blo 2069435 3106907 := bstep (se 1 (by rfl) ⟨2330180, by rfl⟩ : syracuseStep 3106907 = 4660361) B4660361
theorem B2071271 : Blo 2069435 2071271 := bstep (se 1 (by rfl) ⟨1553453, by rfl⟩ : syracuseStep 2071271 = 3106907) B3106907
theorem B2330185 : Blo 2069435 2330185 := bbase (se 2 (by rfl) ⟨873819, by rfl⟩ : syracuseStep 2330185 = 1747639) (by norm_num)
theorem B3106913 : Blo 2069435 3106913 := bstep (se 2 (by rfl) ⟨1165092, by rfl⟩ : syracuseStep 3106913 = 2330185) B2330185
theorem B2071275 : Blo 2069435 2071275 := bstep (se 1 (by rfl) ⟨1553456, by rfl⟩ : syracuseStep 2071275 = 3106913) B3106913
theorem B3192277 : Blo 2069435 3192277 := bbase (se 7 (by rfl) ⟨37409, by rfl⟩ : syracuseStep 3192277 = 74819) (by norm_num)
theorem B4256369 : Blo 2069435 4256369 := bstep (se 2 (by rfl) ⟨1596138, by rfl⟩ : syracuseStep 4256369 = 3192277) B3192277
theorem B2837579 : Blo 2069435 2837579 := bstep (se 1 (by rfl) ⟨2128184, by rfl⟩ : syracuseStep 2837579 = 4256369) B4256369
theorem B7566877 : Blo 2069435 7566877 := bstep (se 3 (by rfl) ⟨1418789, by rfl⟩ : syracuseStep 7566877 = 2837579) B2837579
theorem B40356677 : Blo 2069435 40356677 := bstep (se 4 (by rfl) ⟨3783438, by rfl⟩ : syracuseStep 40356677 = 7566877) B7566877
theorem B107617805 : Blo 2069435 107617805 := bstep (se 3 (by rfl) ⟨20178338, by rfl⟩ : syracuseStep 107617805 = 40356677) B40356677
theorem B71745203 : Blo 2069435 71745203 := bstep (se 1 (by rfl) ⟨53808902, by rfl⟩ : syracuseStep 71745203 = 107617805) B107617805
theorem B47830135 : Blo 2069435 47830135 := bstep (se 1 (by rfl) ⟨35872601, by rfl⟩ : syracuseStep 47830135 = 71745203) B71745203
theorem B63773513 : Blo 2069435 63773513 := bstep (se 2 (by rfl) ⟨23915067, by rfl⟩ : syracuseStep 63773513 = 47830135) B47830135
theorem B42515675 : Blo 2069435 42515675 := bstep (se 1 (by rfl) ⟨31886756, by rfl⟩ : syracuseStep 42515675 = 63773513) B63773513
theorem B28343783 : Blo 2069435 28343783 := bstep (se 1 (by rfl) ⟨21257837, by rfl⟩ : syracuseStep 28343783 = 42515675) B42515675
theorem B18895855 : Blo 2069435 18895855 := bstep (se 1 (by rfl) ⟨14171891, by rfl⟩ : syracuseStep 18895855 = 28343783) B28343783
theorem B25194473 : Blo 2069435 25194473 := bstep (se 2 (by rfl) ⟨9447927, by rfl⟩ : syracuseStep 25194473 = 18895855) B18895855
theorem B16796315 : Blo 2069435 16796315 := bstep (se 1 (by rfl) ⟨12597236, by rfl⟩ : syracuseStep 16796315 = 25194473) B25194473
theorem B11197543 : Blo 2069435 11197543 := bstep (se 1 (by rfl) ⟨8398157, by rfl⟩ : syracuseStep 11197543 = 16796315) B16796315
theorem B14930057 : Blo 2069435 14930057 := bstep (se 2 (by rfl) ⟨5598771, by rfl⟩ : syracuseStep 14930057 = 11197543) B11197543
theorem B9953371 : Blo 2069435 9953371 := bstep (se 1 (by rfl) ⟨7465028, by rfl⟩ : syracuseStep 9953371 = 14930057) B14930057
theorem B13271161 : Blo 2069435 13271161 := bstep (se 2 (by rfl) ⟨4976685, by rfl⟩ : syracuseStep 13271161 = 9953371) B9953371
theorem B17694881 : Blo 2069435 17694881 := bstep (se 2 (by rfl) ⟨6635580, by rfl⟩ : syracuseStep 17694881 = 13271161) B13271161
theorem B11796587 : Blo 2069435 11796587 := bstep (se 1 (by rfl) ⟨8847440, by rfl⟩ : syracuseStep 11796587 = 17694881) B17694881
theorem B7864391 : Blo 2069435 7864391 := bstep (se 1 (by rfl) ⟨5898293, by rfl⟩ : syracuseStep 7864391 = 11796587) B11796587
theorem B5242927 : Blo 2069435 5242927 := bstep (se 1 (by rfl) ⟨3932195, by rfl⟩ : syracuseStep 5242927 = 7864391) B7864391
theorem B6990569 : Blo 2069435 6990569 := bstep (se 2 (by rfl) ⟨2621463, by rfl⟩ : syracuseStep 6990569 = 5242927) B5242927
theorem B4660379 : Blo 2069435 4660379 := bstep (se 1 (by rfl) ⟨3495284, by rfl⟩ : syracuseStep 4660379 = 6990569) B6990569
theorem B3106919 : Blo 2069435 3106919 := bstep (se 1 (by rfl) ⟨2330189, by rfl⟩ : syracuseStep 3106919 = 4660379) B4660379
theorem B2071279 : Blo 2069435 2071279 := bstep (se 1 (by rfl) ⟨1553459, by rfl⟩ : syracuseStep 2071279 = 3106919) B3106919
theorem B3106925 : Blo 2069435 3106925 := bbase (se 3 (by rfl) ⟨582548, by rfl⟩ : syracuseStep 3106925 = 1165097) (by norm_num)
theorem B2071283 : Blo 2069435 2071283 := bstep (se 1 (by rfl) ⟨1553462, by rfl⟩ : syracuseStep 2071283 = 3106925) B3106925
theorem B4660397 : Blo 2069435 4660397 := bbase (se 3 (by rfl) ⟨873824, by rfl⟩ : syracuseStep 4660397 = 1747649) (by norm_num)
theorem B3106931 : Blo 2069435 3106931 := bstep (se 1 (by rfl) ⟨2330198, by rfl⟩ : syracuseStep 3106931 = 4660397) B4660397
theorem B2071287 : Blo 2069435 2071287 := bstep (se 1 (by rfl) ⟨1553465, by rfl⟩ : syracuseStep 2071287 = 3106931) B3106931
theorem B6635621 : Blo 2069435 6635621 := bbase (se 4 (by rfl) ⟨622089, by rfl⟩ : syracuseStep 6635621 = 1244179) (by norm_num)
theorem B4423747 : Blo 2069435 4423747 := bstep (se 1 (by rfl) ⟨3317810, by rfl⟩ : syracuseStep 4423747 = 6635621) B6635621
theorem B5898329 : Blo 2069435 5898329 := bstep (se 2 (by rfl) ⟨2211873, by rfl⟩ : syracuseStep 5898329 = 4423747) B4423747
theorem B3932219 : Blo 2069435 3932219 := bstep (se 1 (by rfl) ⟨2949164, by rfl⟩ : syracuseStep 3932219 = 5898329) B5898329
theorem B2621479 : Blo 2069435 2621479 := bstep (se 1 (by rfl) ⟨1966109, by rfl⟩ : syracuseStep 2621479 = 3932219) B3932219
theorem B3495305 : Blo 2069435 3495305 := bstep (se 2 (by rfl) ⟨1310739, by rfl⟩ : syracuseStep 3495305 = 2621479) B2621479
theorem B2330203 : Blo 2069435 2330203 := bstep (se 1 (by rfl) ⟨1747652, by rfl⟩ : syracuseStep 2330203 = 3495305) B3495305
theorem B3106937 : Blo 2069435 3106937 := bstep (se 2 (by rfl) ⟨1165101, by rfl⟩ : syracuseStep 3106937 = 2330203) B2330203
theorem B2071291 : Blo 2069435 2071291 := bstep (se 1 (by rfl) ⟨1553468, by rfl⟩ : syracuseStep 2071291 = 3106937) B3106937
theorem B26240021 : Blo 2069435 26240021 := bbase (se 6 (by rfl) ⟨615000, by rfl⟩ : syracuseStep 26240021 = 1230001) (by norm_num)
theorem B17493347 : Blo 2069435 17493347 := bstep (se 1 (by rfl) ⟨13120010, by rfl⟩ : syracuseStep 17493347 = 26240021) B26240021
theorem B11662231 : Blo 2069435 11662231 := bstep (se 1 (by rfl) ⟨8746673, by rfl⟩ : syracuseStep 11662231 = 17493347) B17493347
theorem B15549641 : Blo 2069435 15549641 := bstep (se 2 (by rfl) ⟨5831115, by rfl⟩ : syracuseStep 15549641 = 11662231) B11662231
theorem B10366427 : Blo 2069435 10366427 := bstep (se 1 (by rfl) ⟨7774820, by rfl⟩ : syracuseStep 10366427 = 15549641) B15549641
theorem B6910951 : Blo 2069435 6910951 := bstep (se 1 (by rfl) ⟨5183213, by rfl⟩ : syracuseStep 6910951 = 10366427) B10366427
theorem B147433621 : Blo 2069435 147433621 := bstep (se 6 (by rfl) ⟨3455475, by rfl⟩ : syracuseStep 147433621 = 6910951) B6910951
theorem B196578161 : Blo 2069435 196578161 := bstep (se 2 (by rfl) ⟨73716810, by rfl⟩ : syracuseStep 196578161 = 147433621) B147433621
theorem B131052107 : Blo 2069435 131052107 := bstep (se 1 (by rfl) ⟨98289080, by rfl⟩ : syracuseStep 131052107 = 196578161) B196578161
theorem B87368071 : Blo 2069435 87368071 := bstep (se 1 (by rfl) ⟨65526053, by rfl⟩ : syracuseStep 87368071 = 131052107) B131052107
theorem B116490761 : Blo 2069435 116490761 := bstep (se 2 (by rfl) ⟨43684035, by rfl⟩ : syracuseStep 116490761 = 87368071) B87368071
theorem B77660507 : Blo 2069435 77660507 := bstep (se 1 (by rfl) ⟨58245380, by rfl⟩ : syracuseStep 77660507 = 116490761) B116490761
theorem B51773671 : Blo 2069435 51773671 := bstep (se 1 (by rfl) ⟨38830253, by rfl⟩ : syracuseStep 51773671 = 77660507) B77660507
theorem B69031561 : Blo 2069435 69031561 := bstep (se 2 (by rfl) ⟨25886835, by rfl⟩ : syracuseStep 69031561 = 51773671) B51773671
theorem B92042081 : Blo 2069435 92042081 := bstep (se 2 (by rfl) ⟨34515780, by rfl⟩ : syracuseStep 92042081 = 69031561) B69031561
theorem B61361387 : Blo 2069435 61361387 := bstep (se 1 (by rfl) ⟨46021040, by rfl⟩ : syracuseStep 61361387 = 92042081) B92042081
theorem B40907591 : Blo 2069435 40907591 := bstep (se 1 (by rfl) ⟨30680693, by rfl⟩ : syracuseStep 40907591 = 61361387) B61361387
theorem B27271727 : Blo 2069435 27271727 := bstep (se 1 (by rfl) ⟨20453795, by rfl⟩ : syracuseStep 27271727 = 40907591) B40907591
theorem B18181151 : Blo 2069435 18181151 := bstep (se 1 (by rfl) ⟨13635863, by rfl⟩ : syracuseStep 18181151 = 27271727) B27271727
theorem B12120767 : Blo 2069435 12120767 := bstep (se 1 (by rfl) ⟨9090575, by rfl⟩ : syracuseStep 12120767 = 18181151) B18181151
theorem B8080511 : Blo 2069435 8080511 := bstep (se 1 (by rfl) ⟨6060383, by rfl⟩ : syracuseStep 8080511 = 12120767) B12120767
theorem B21548029 : Blo 2069435 21548029 := bstep (se 3 (by rfl) ⟨4040255, by rfl⟩ : syracuseStep 21548029 = 8080511) B8080511
theorem B28730705 : Blo 2069435 28730705 := bstep (se 2 (by rfl) ⟨10774014, by rfl⟩ : syracuseStep 28730705 = 21548029) B21548029
theorem B306460853 : Blo 2069435 306460853 := bstep (se 5 (by rfl) ⟨14365352, by rfl⟩ : syracuseStep 306460853 = 28730705) B28730705
theorem B204307235 : Blo 2069435 204307235 := bstep (se 1 (by rfl) ⟨153230426, by rfl⟩ : syracuseStep 204307235 = 306460853) B306460853
theorem B136204823 : Blo 2069435 136204823 := bstep (se 1 (by rfl) ⟨102153617, by rfl⟩ : syracuseStep 136204823 = 204307235) B204307235
theorem B90803215 : Blo 2069435 90803215 := bstep (se 1 (by rfl) ⟨68102411, by rfl⟩ : syracuseStep 90803215 = 136204823) B136204823
theorem B121070953 : Blo 2069435 121070953 := bstep (se 2 (by rfl) ⟨45401607, by rfl⟩ : syracuseStep 121070953 = 90803215) B90803215
theorem B161427937 : Blo 2069435 161427937 := bstep (se 2 (by rfl) ⟨60535476, by rfl⟩ : syracuseStep 161427937 = 121070953) B121070953
theorem B215237249 : Blo 2069435 215237249 := bstep (se 2 (by rfl) ⟨80713968, by rfl⟩ : syracuseStep 215237249 = 161427937) B161427937
theorem B143491499 : Blo 2069435 143491499 := bstep (se 1 (by rfl) ⟨107618624, by rfl⟩ : syracuseStep 143491499 = 215237249) B215237249
theorem B95660999 : Blo 2069435 95660999 := bstep (se 1 (by rfl) ⟨71745749, by rfl⟩ : syracuseStep 95660999 = 143491499) B143491499
theorem B63773999 : Blo 2069435 63773999 := bstep (se 1 (by rfl) ⟨47830499, by rfl⟩ : syracuseStep 63773999 = 95660999) B95660999
theorem B42515999 : Blo 2069435 42515999 := bstep (se 1 (by rfl) ⟨31886999, by rfl⟩ : syracuseStep 42515999 = 63773999) B63773999
theorem B28343999 : Blo 2069435 28343999 := bstep (se 1 (by rfl) ⟨21257999, by rfl⟩ : syracuseStep 28343999 = 42515999) B42515999
theorem B18895999 : Blo 2069435 18895999 := bstep (se 1 (by rfl) ⟨14171999, by rfl⟩ : syracuseStep 18895999 = 28343999) B28343999
theorem B25194665 : Blo 2069435 25194665 := bstep (se 2 (by rfl) ⟨9447999, by rfl⟩ : syracuseStep 25194665 = 18895999) B18895999
theorem B16796443 : Blo 2069435 16796443 := bstep (se 1 (by rfl) ⟨12597332, by rfl⟩ : syracuseStep 16796443 = 25194665) B25194665
theorem B22395257 : Blo 2069435 22395257 := bstep (se 2 (by rfl) ⟨8398221, by rfl⟩ : syracuseStep 22395257 = 16796443) B16796443
theorem B14930171 : Blo 2069435 14930171 := bstep (se 1 (by rfl) ⟨11197628, by rfl⟩ : syracuseStep 14930171 = 22395257) B22395257
theorem B9953447 : Blo 2069435 9953447 := bstep (se 1 (by rfl) ⟨7465085, by rfl⟩ : syracuseStep 9953447 = 14930171) B14930171
theorem B26542525 : Blo 2069435 26542525 := bstep (se 3 (by rfl) ⟨4976723, by rfl⟩ : syracuseStep 26542525 = 9953447) B9953447
theorem B35390033 : Blo 2069435 35390033 := bstep (se 2 (by rfl) ⟨13271262, by rfl⟩ : syracuseStep 35390033 = 26542525) B26542525
theorem B23593355 : Blo 2069435 23593355 := bstep (se 1 (by rfl) ⟨17695016, by rfl⟩ : syracuseStep 23593355 = 35390033) B35390033
theorem B15728903 : Blo 2069435 15728903 := bstep (se 1 (by rfl) ⟨11796677, by rfl⟩ : syracuseStep 15728903 = 23593355) B23593355
theorem B10485935 : Blo 2069435 10485935 := bstep (se 1 (by rfl) ⟨7864451, by rfl⟩ : syracuseStep 10485935 = 15728903) B15728903
theorem B6990623 : Blo 2069435 6990623 := bstep (se 1 (by rfl) ⟨5242967, by rfl⟩ : syracuseStep 6990623 = 10485935) B10485935
theorem B4660415 : Blo 2069435 4660415 := bstep (se 1 (by rfl) ⟨3495311, by rfl⟩ : syracuseStep 4660415 = 6990623) B6990623
theorem B3106943 : Blo 2069435 3106943 := bstep (se 1 (by rfl) ⟨2330207, by rfl⟩ : syracuseStep 3106943 = 4660415) B4660415
theorem B2071295 : Blo 2069435 2071295 := bstep (se 1 (by rfl) ⟨1553471, by rfl⟩ : syracuseStep 2071295 = 3106943) B3106943
theorem B3106949 : Blo 2069435 3106949 := bbase (se 4 (by rfl) ⟨291276, by rfl⟩ : syracuseStep 3106949 = 582553) (by norm_num)
theorem B2071299 : Blo 2069435 2071299 := bstep (se 1 (by rfl) ⟨1553474, by rfl⟩ : syracuseStep 2071299 = 3106949) B3106949
theorem B3495325 : Blo 2069435 3495325 := bbase (se 3 (by rfl) ⟨655373, by rfl⟩ : syracuseStep 3495325 = 1310747) (by norm_num)
theorem B4660433 : Blo 2069435 4660433 := bstep (se 2 (by rfl) ⟨1747662, by rfl⟩ : syracuseStep 4660433 = 3495325) B3495325
theorem B3106955 : Blo 2069435 3106955 := bstep (se 1 (by rfl) ⟨2330216, by rfl⟩ : syracuseStep 3106955 = 4660433) B4660433
theorem B2071303 : Blo 2069435 2071303 := bstep (se 1 (by rfl) ⟨1553477, by rfl⟩ : syracuseStep 2071303 = 3106955) B3106955
theorem B2330221 : Blo 2069435 2330221 := bbase (se 3 (by rfl) ⟨436916, by rfl⟩ : syracuseStep 2330221 = 873833) (by norm_num)
theorem B3106961 : Blo 2069435 3106961 := bstep (se 2 (by rfl) ⟨1165110, by rfl⟩ : syracuseStep 3106961 = 2330221) B2330221
theorem B2071307 : Blo 2069435 2071307 := bstep (se 1 (by rfl) ⟨1553480, by rfl⟩ : syracuseStep 2071307 = 3106961) B3106961
theorem B6990677 : Blo 2069435 6990677 := bbase (se 9 (by rfl) ⟨20480, by rfl⟩ : syracuseStep 6990677 = 40961) (by norm_num)
theorem B4660451 : Blo 2069435 4660451 := bstep (se 1 (by rfl) ⟨3495338, by rfl⟩ : syracuseStep 4660451 = 6990677) B6990677
theorem B3106967 : Blo 2069435 3106967 := bstep (se 1 (by rfl) ⟨2330225, by rfl⟩ : syracuseStep 3106967 = 4660451) B4660451
theorem B2071311 : Blo 2069435 2071311 := bstep (se 1 (by rfl) ⟨1553483, by rfl⟩ : syracuseStep 2071311 = 3106967) B3106967
theorem B3106973 : Blo 2069435 3106973 := bbase (se 3 (by rfl) ⟨582557, by rfl⟩ : syracuseStep 3106973 = 1165115) (by norm_num)
theorem B2071315 : Blo 2069435 2071315 := bstep (se 1 (by rfl) ⟨1553486, by rfl⟩ : syracuseStep 2071315 = 3106973) B3106973
theorem B4660469 : Blo 2069435 4660469 := bbase (se 5 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 4660469 = 436919) (by norm_num)
theorem B3106979 : Blo 2069435 3106979 := bstep (se 1 (by rfl) ⟨2330234, by rfl⟩ : syracuseStep 3106979 = 4660469) B4660469
theorem B2071319 : Blo 2069435 2071319 := bstep (se 1 (by rfl) ⟨1553489, by rfl⟩ : syracuseStep 2071319 = 3106979) B3106979
theorem B5044693 : Blo 2069435 5044693 := bbase (se 7 (by rfl) ⟨59117, by rfl⟩ : syracuseStep 5044693 = 118235) (by norm_num)
theorem B6726257 : Blo 2069435 6726257 := bstep (se 2 (by rfl) ⟨2522346, by rfl⟩ : syracuseStep 6726257 = 5044693) B5044693
theorem B4484171 : Blo 2069435 4484171 := bstep (se 1 (by rfl) ⟨3363128, by rfl⟩ : syracuseStep 4484171 = 6726257) B6726257
theorem B11957789 : Blo 2069435 11957789 := bstep (se 3 (by rfl) ⟨2242085, by rfl⟩ : syracuseStep 11957789 = 4484171) B4484171
theorem B7971859 : Blo 2069435 7971859 := bstep (se 1 (by rfl) ⟨5978894, by rfl⟩ : syracuseStep 7971859 = 11957789) B11957789
theorem B10629145 : Blo 2069435 10629145 := bstep (se 2 (by rfl) ⟨3985929, by rfl⟩ : syracuseStep 10629145 = 7971859) B7971859
theorem B14172193 : Blo 2069435 14172193 := bstep (se 2 (by rfl) ⟨5314572, by rfl⟩ : syracuseStep 14172193 = 10629145) B10629145
theorem B18896257 : Blo 2069435 18896257 := bstep (se 2 (by rfl) ⟨7086096, by rfl⟩ : syracuseStep 18896257 = 14172193) B14172193
theorem B100780037 : Blo 2069435 100780037 := bstep (se 4 (by rfl) ⟨9448128, by rfl⟩ : syracuseStep 100780037 = 18896257) B18896257
theorem B67186691 : Blo 2069435 67186691 := bstep (se 1 (by rfl) ⟨50390018, by rfl⟩ : syracuseStep 67186691 = 100780037) B100780037
theorem B44791127 : Blo 2069435 44791127 := bstep (se 1 (by rfl) ⟨33593345, by rfl⟩ : syracuseStep 44791127 = 67186691) B67186691
theorem B29860751 : Blo 2069435 29860751 := bstep (se 1 (by rfl) ⟨22395563, by rfl⟩ : syracuseStep 29860751 = 44791127) B44791127
theorem B19907167 : Blo 2069435 19907167 := bstep (se 1 (by rfl) ⟨14930375, by rfl⟩ : syracuseStep 19907167 = 29860751) B29860751
theorem B26542889 : Blo 2069435 26542889 := bstep (se 2 (by rfl) ⟨9953583, by rfl⟩ : syracuseStep 26542889 = 19907167) B19907167
theorem B17695259 : Blo 2069435 17695259 := bstep (se 1 (by rfl) ⟨13271444, by rfl⟩ : syracuseStep 17695259 = 26542889) B26542889
theorem B11796839 : Blo 2069435 11796839 := bstep (se 1 (by rfl) ⟨8847629, by rfl⟩ : syracuseStep 11796839 = 17695259) B17695259
theorem B7864559 : Blo 2069435 7864559 := bstep (se 1 (by rfl) ⟨5898419, by rfl⟩ : syracuseStep 7864559 = 11796839) B11796839
theorem B5243039 : Blo 2069435 5243039 := bstep (se 1 (by rfl) ⟨3932279, by rfl⟩ : syracuseStep 5243039 = 7864559) B7864559
theorem B3495359 : Blo 2069435 3495359 := bstep (se 1 (by rfl) ⟨2621519, by rfl⟩ : syracuseStep 3495359 = 5243039) B5243039
theorem B2330239 : Blo 2069435 2330239 := bstep (se 1 (by rfl) ⟨1747679, by rfl⟩ : syracuseStep 2330239 = 3495359) B3495359
theorem B3106985 : Blo 2069435 3106985 := bstep (se 2 (by rfl) ⟨1165119, by rfl⟩ : syracuseStep 3106985 = 2330239) B2330239
theorem B2071323 : Blo 2069435 2071323 := bstep (se 1 (by rfl) ⟨1553492, by rfl⟩ : syracuseStep 2071323 = 3106985) B3106985
theorem B2522353 : Blo 2069435 2522353 := bbase (se 2 (by rfl) ⟨945882, by rfl⟩ : syracuseStep 2522353 = 1891765) (by norm_num)
theorem B3363137 : Blo 2069435 3363137 := bstep (se 2 (by rfl) ⟨1261176, by rfl⟩ : syracuseStep 3363137 = 2522353) B2522353
theorem B2242091 : Blo 2069435 2242091 := bstep (se 1 (by rfl) ⟨1681568, by rfl⟩ : syracuseStep 2242091 = 3363137) B3363137
theorem B5978909 : Blo 2069435 5978909 := bstep (se 3 (by rfl) ⟨1121045, by rfl⟩ : syracuseStep 5978909 = 2242091) B2242091
theorem B3985939 : Blo 2069435 3985939 := bstep (se 1 (by rfl) ⟨2989454, by rfl⟩ : syracuseStep 3985939 = 5978909) B5978909
theorem B5314585 : Blo 2069435 5314585 := bstep (se 2 (by rfl) ⟨1992969, by rfl⟩ : syracuseStep 5314585 = 3985939) B3985939
theorem B7086113 : Blo 2069435 7086113 := bstep (se 2 (by rfl) ⟨2657292, by rfl⟩ : syracuseStep 7086113 = 5314585) B5314585
theorem B4724075 : Blo 2069435 4724075 := bstep (se 1 (by rfl) ⟨3543056, by rfl⟩ : syracuseStep 4724075 = 7086113) B7086113
theorem B3149383 : Blo 2069435 3149383 := bstep (se 1 (by rfl) ⟨2362037, by rfl⟩ : syracuseStep 3149383 = 4724075) B4724075
theorem B4199177 : Blo 2069435 4199177 := bstep (se 2 (by rfl) ⟨1574691, by rfl⟩ : syracuseStep 4199177 = 3149383) B3149383
theorem B2799451 : Blo 2069435 2799451 := bstep (se 1 (by rfl) ⟨2099588, by rfl⟩ : syracuseStep 2799451 = 4199177) B4199177
theorem B14930405 : Blo 2069435 14930405 := bstep (se 4 (by rfl) ⟨1399725, by rfl⟩ : syracuseStep 14930405 = 2799451) B2799451
theorem B9953603 : Blo 2069435 9953603 := bstep (se 1 (by rfl) ⟨7465202, by rfl⟩ : syracuseStep 9953603 = 14930405) B14930405
theorem B6635735 : Blo 2069435 6635735 := bstep (se 1 (by rfl) ⟨4976801, by rfl⟩ : syracuseStep 6635735 = 9953603) B9953603
theorem B4423823 : Blo 2069435 4423823 := bstep (se 1 (by rfl) ⟨3317867, by rfl⟩ : syracuseStep 4423823 = 6635735) B6635735
theorem B2949215 : Blo 2069435 2949215 := bstep (se 1 (by rfl) ⟨2211911, by rfl⟩ : syracuseStep 2949215 = 4423823) B4423823
theorem B7864573 : Blo 2069435 7864573 := bstep (se 3 (by rfl) ⟨1474607, by rfl⟩ : syracuseStep 7864573 = 2949215) B2949215
theorem B10486097 : Blo 2069435 10486097 := bstep (se 2 (by rfl) ⟨3932286, by rfl⟩ : syracuseStep 10486097 = 7864573) B7864573
theorem B6990731 : Blo 2069435 6990731 := bstep (se 1 (by rfl) ⟨5243048, by rfl⟩ : syracuseStep 6990731 = 10486097) B10486097
theorem B4660487 : Blo 2069435 4660487 := bstep (se 1 (by rfl) ⟨3495365, by rfl⟩ : syracuseStep 4660487 = 6990731) B6990731
theorem B3106991 : Blo 2069435 3106991 := bstep (se 1 (by rfl) ⟨2330243, by rfl⟩ : syracuseStep 3106991 = 4660487) B4660487
theorem B2071327 : Blo 2069435 2071327 := bstep (se 1 (by rfl) ⟨1553495, by rfl⟩ : syracuseStep 2071327 = 3106991) B3106991
theorem B3106997 : Blo 2069435 3106997 := bbase (se 5 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 3106997 = 291281) (by norm_num)
theorem B2071331 : Blo 2069435 2071331 := bstep (se 1 (by rfl) ⟨1553498, by rfl⟩ : syracuseStep 2071331 = 3106997) B3106997
theorem B5243069 : Blo 2069435 5243069 := bbase (se 3 (by rfl) ⟨983075, by rfl⟩ : syracuseStep 5243069 = 1966151) (by norm_num)
theorem B3495379 : Blo 2069435 3495379 := bstep (se 1 (by rfl) ⟨2621534, by rfl⟩ : syracuseStep 3495379 = 5243069) B5243069
theorem B4660505 : Blo 2069435 4660505 := bstep (se 2 (by rfl) ⟨1747689, by rfl⟩ : syracuseStep 4660505 = 3495379) B3495379
theorem B3107003 : Blo 2069435 3107003 := bstep (se 1 (by rfl) ⟨2330252, by rfl⟩ : syracuseStep 3107003 = 4660505) B4660505
theorem B2071335 : Blo 2069435 2071335 := bstep (se 1 (by rfl) ⟨1553501, by rfl⟩ : syracuseStep 2071335 = 3107003) B3107003
theorem B2330257 : Blo 2069435 2330257 := bbase (se 2 (by rfl) ⟨873846, by rfl⟩ : syracuseStep 2330257 = 1747693) (by norm_num)
theorem B3107009 : Blo 2069435 3107009 := bstep (se 2 (by rfl) ⟨1165128, by rfl⟩ : syracuseStep 3107009 = 2330257) B2330257
theorem B2071339 : Blo 2069435 2071339 := bstep (se 1 (by rfl) ⟨1553504, by rfl⟩ : syracuseStep 2071339 = 3107009) B3107009
theorem B3932317 : Blo 2069435 3932317 := bbase (se 3 (by rfl) ⟨737309, by rfl⟩ : syracuseStep 3932317 = 1474619) (by norm_num)
theorem B5243089 : Blo 2069435 5243089 := bstep (se 2 (by rfl) ⟨1966158, by rfl⟩ : syracuseStep 5243089 = 3932317) B3932317
theorem B6990785 : Blo 2069435 6990785 := bstep (se 2 (by rfl) ⟨2621544, by rfl⟩ : syracuseStep 6990785 = 5243089) B5243089
theorem B4660523 : Blo 2069435 4660523 := bstep (se 1 (by rfl) ⟨3495392, by rfl⟩ : syracuseStep 4660523 = 6990785) B6990785
theorem B3107015 : Blo 2069435 3107015 := bstep (se 1 (by rfl) ⟨2330261, by rfl⟩ : syracuseStep 3107015 = 4660523) B4660523
theorem B2071343 : Blo 2069435 2071343 := bstep (se 1 (by rfl) ⟨1553507, by rfl⟩ : syracuseStep 2071343 = 3107015) B3107015
theorem B3107021 : Blo 2069435 3107021 := bbase (se 3 (by rfl) ⟨582566, by rfl⟩ : syracuseStep 3107021 = 1165133) (by norm_num)
theorem B2071347 : Blo 2069435 2071347 := bstep (se 1 (by rfl) ⟨1553510, by rfl⟩ : syracuseStep 2071347 = 3107021) B3107021
theorem B4660541 : Blo 2069435 4660541 := bbase (se 3 (by rfl) ⟨873851, by rfl⟩ : syracuseStep 4660541 = 1747703) (by norm_num)
theorem B3107027 : Blo 2069435 3107027 := bstep (se 1 (by rfl) ⟨2330270, by rfl⟩ : syracuseStep 3107027 = 4660541) B4660541
theorem B2071351 : Blo 2069435 2071351 := bstep (se 1 (by rfl) ⟨1553513, by rfl⟩ : syracuseStep 2071351 = 3107027) B3107027
theorem B3495413 : Blo 2069435 3495413 := bbase (se 5 (by rfl) ⟨163847, by rfl⟩ : syracuseStep 3495413 = 327695) (by norm_num)
theorem B2330275 : Blo 2069435 2330275 := bstep (se 1 (by rfl) ⟨1747706, by rfl⟩ : syracuseStep 2330275 = 3495413) B3495413
theorem B3107033 : Blo 2069435 3107033 := bstep (se 2 (by rfl) ⟨1165137, by rfl⟩ : syracuseStep 3107033 = 2330275) B2330275
theorem B2071355 : Blo 2069435 2071355 := bstep (se 1 (by rfl) ⟨1553516, by rfl⟩ : syracuseStep 2071355 = 3107033) B3107033
theorem B2099621 : Blo 2069435 2099621 := bbase (se 4 (by rfl) ⟨196839, by rfl⟩ : syracuseStep 2099621 = 393679) (by norm_num)
theorem B5598989 : Blo 2069435 5598989 := bstep (se 3 (by rfl) ⟨1049810, by rfl⟩ : syracuseStep 5598989 = 2099621) B2099621
theorem B3732659 : Blo 2069435 3732659 := bstep (se 1 (by rfl) ⟨2799494, by rfl⟩ : syracuseStep 3732659 = 5598989) B5598989
theorem B2488439 : Blo 2069435 2488439 := bstep (se 1 (by rfl) ⟨1866329, by rfl⟩ : syracuseStep 2488439 = 3732659) B3732659
theorem B6635837 : Blo 2069435 6635837 := bstep (se 3 (by rfl) ⟨1244219, by rfl⟩ : syracuseStep 6635837 = 2488439) B2488439
theorem B4423891 : Blo 2069435 4423891 := bstep (se 1 (by rfl) ⟨3317918, by rfl⟩ : syracuseStep 4423891 = 6635837) B6635837
theorem B5898521 : Blo 2069435 5898521 := bstep (se 2 (by rfl) ⟨2211945, by rfl⟩ : syracuseStep 5898521 = 4423891) B4423891
theorem B15729389 : Blo 2069435 15729389 := bstep (se 3 (by rfl) ⟨2949260, by rfl⟩ : syracuseStep 15729389 = 5898521) B5898521
theorem B10486259 : Blo 2069435 10486259 := bstep (se 1 (by rfl) ⟨7864694, by rfl⟩ : syracuseStep 10486259 = 15729389) B15729389
theorem B6990839 : Blo 2069435 6990839 := bstep (se 1 (by rfl) ⟨5243129, by rfl⟩ : syracuseStep 6990839 = 10486259) B10486259
theorem B4660559 : Blo 2069435 4660559 := bstep (se 1 (by rfl) ⟨3495419, by rfl⟩ : syracuseStep 4660559 = 6990839) B6990839
theorem B3107039 : Blo 2069435 3107039 := bstep (se 1 (by rfl) ⟨2330279, by rfl⟩ : syracuseStep 3107039 = 4660559) B4660559
theorem B2071359 : Blo 2069435 2071359 := bstep (se 1 (by rfl) ⟨1553519, by rfl⟩ : syracuseStep 2071359 = 3107039) B3107039
theorem B3107045 : Blo 2069435 3107045 := bbase (se 4 (by rfl) ⟨291285, by rfl⟩ : syracuseStep 3107045 = 582571) (by norm_num)
theorem B2071363 : Blo 2069435 2071363 := bstep (se 1 (by rfl) ⟨1553522, by rfl⟩ : syracuseStep 2071363 = 3107045) B3107045
theorem B4423909 : Blo 2069435 4423909 := bbase (se 4 (by rfl) ⟨414741, by rfl⟩ : syracuseStep 4423909 = 829483) (by norm_num)
theorem B5898545 : Blo 2069435 5898545 := bstep (se 2 (by rfl) ⟨2211954, by rfl⟩ : syracuseStep 5898545 = 4423909) B4423909
theorem B3932363 : Blo 2069435 3932363 := bstep (se 1 (by rfl) ⟨2949272, by rfl⟩ : syracuseStep 3932363 = 5898545) B5898545
theorem B2621575 : Blo 2069435 2621575 := bstep (se 1 (by rfl) ⟨1966181, by rfl⟩ : syracuseStep 2621575 = 3932363) B3932363
theorem B3495433 : Blo 2069435 3495433 := bstep (se 2 (by rfl) ⟨1310787, by rfl⟩ : syracuseStep 3495433 = 2621575) B2621575
theorem B4660577 : Blo 2069435 4660577 := bstep (se 2 (by rfl) ⟨1747716, by rfl⟩ : syracuseStep 4660577 = 3495433) B3495433
theorem B3107051 : Blo 2069435 3107051 := bstep (se 1 (by rfl) ⟨2330288, by rfl⟩ : syracuseStep 3107051 = 4660577) B4660577
theorem B2071367 : Blo 2069435 2071367 := bstep (se 1 (by rfl) ⟨1553525, by rfl⟩ : syracuseStep 2071367 = 3107051) B3107051
theorem B2330293 : Blo 2069435 2330293 := bbase (se 5 (by rfl) ⟨109232, by rfl⟩ : syracuseStep 2330293 = 218465) (by norm_num)
theorem B3107057 : Blo 2069435 3107057 := bstep (se 2 (by rfl) ⟨1165146, by rfl⟩ : syracuseStep 3107057 = 2330293) B2330293
theorem B2071371 : Blo 2069435 2071371 := bstep (se 1 (by rfl) ⟨1553528, by rfl⟩ : syracuseStep 2071371 = 3107057) B3107057
theorem B2621585 : Blo 2069435 2621585 := bbase (se 2 (by rfl) ⟨983094, by rfl⟩ : syracuseStep 2621585 = 1966189) (by norm_num)
theorem B6990893 : Blo 2069435 6990893 := bstep (se 3 (by rfl) ⟨1310792, by rfl⟩ : syracuseStep 6990893 = 2621585) B2621585
theorem B4660595 : Blo 2069435 4660595 := bstep (se 1 (by rfl) ⟨3495446, by rfl⟩ : syracuseStep 4660595 = 6990893) B6990893
theorem B3107063 : Blo 2069435 3107063 := bstep (se 1 (by rfl) ⟨2330297, by rfl⟩ : syracuseStep 3107063 = 4660595) B4660595
theorem B2071375 : Blo 2069435 2071375 := bstep (se 1 (by rfl) ⟨1553531, by rfl⟩ : syracuseStep 2071375 = 3107063) B3107063
theorem B3107069 : Blo 2069435 3107069 := bbase (se 3 (by rfl) ⟨582575, by rfl⟩ : syracuseStep 3107069 = 1165151) (by norm_num)
theorem B2071379 : Blo 2069435 2071379 := bstep (se 1 (by rfl) ⟨1553534, by rfl⟩ : syracuseStep 2071379 = 3107069) B3107069
theorem B4660613 : Blo 2069435 4660613 := bbase (se 4 (by rfl) ⟨436932, by rfl⟩ : syracuseStep 4660613 = 873865) (by norm_num)
theorem B3107075 : Blo 2069435 3107075 := bstep (se 1 (by rfl) ⟨2330306, by rfl⟩ : syracuseStep 3107075 = 4660613) B4660613
theorem B2071383 : Blo 2069435 2071383 := bstep (se 1 (by rfl) ⟨1553537, by rfl⟩ : syracuseStep 2071383 = 3107075) B3107075
theorem B2949301 : Blo 2069435 2949301 := bbase (se 5 (by rfl) ⟨138248, by rfl⟩ : syracuseStep 2949301 = 276497) (by norm_num)
theorem B3932401 : Blo 2069435 3932401 := bstep (se 2 (by rfl) ⟨1474650, by rfl⟩ : syracuseStep 3932401 = 2949301) B2949301
theorem B5243201 : Blo 2069435 5243201 := bstep (se 2 (by rfl) ⟨1966200, by rfl⟩ : syracuseStep 5243201 = 3932401) B3932401
theorem B3495467 : Blo 2069435 3495467 := bstep (se 1 (by rfl) ⟨2621600, by rfl⟩ : syracuseStep 3495467 = 5243201) B5243201
theorem B2330311 : Blo 2069435 2330311 := bstep (se 1 (by rfl) ⟨1747733, by rfl⟩ : syracuseStep 2330311 = 3495467) B3495467
theorem B3107081 : Blo 2069435 3107081 := bstep (se 2 (by rfl) ⟨1165155, by rfl⟩ : syracuseStep 3107081 = 2330311) B2330311
theorem B2071387 : Blo 2069435 2071387 := bstep (se 1 (by rfl) ⟨1553540, by rfl⟩ : syracuseStep 2071387 = 3107081) B3107081
theorem B10486421 : Blo 2069435 10486421 := bbase (se 6 (by rfl) ⟨245775, by rfl⟩ : syracuseStep 10486421 = 491551) (by norm_num)
theorem B6990947 : Blo 2069435 6990947 := bstep (se 1 (by rfl) ⟨5243210, by rfl⟩ : syracuseStep 6990947 = 10486421) B10486421
theorem B4660631 : Blo 2069435 4660631 := bstep (se 1 (by rfl) ⟨3495473, by rfl⟩ : syracuseStep 4660631 = 6990947) B6990947
theorem B3107087 : Blo 2069435 3107087 := bstep (se 1 (by rfl) ⟨2330315, by rfl⟩ : syracuseStep 3107087 = 4660631) B4660631
theorem B2071391 : Blo 2069435 2071391 := bstep (se 1 (by rfl) ⟨1553543, by rfl⟩ : syracuseStep 2071391 = 3107087) B3107087
theorem B3107093 : Blo 2069435 3107093 := bbase (se 6 (by rfl) ⟨72822, by rfl⟩ : syracuseStep 3107093 = 145645) (by norm_num)
theorem B2071395 : Blo 2069435 2071395 := bstep (se 1 (by rfl) ⟨1553546, by rfl⟩ : syracuseStep 2071395 = 3107093) B3107093
theorem B15944309 : Blo 2069435 15944309 := bbase (se 5 (by rfl) ⟨747389, by rfl⟩ : syracuseStep 15944309 = 1494779) (by norm_num)
theorem B10629539 : Blo 2069435 10629539 := bstep (se 1 (by rfl) ⟨7972154, by rfl⟩ : syracuseStep 10629539 = 15944309) B15944309
theorem B7086359 : Blo 2069435 7086359 := bstep (se 1 (by rfl) ⟨5314769, by rfl⟩ : syracuseStep 7086359 = 10629539) B10629539
theorem B4724239 : Blo 2069435 4724239 := bstep (se 1 (by rfl) ⟨3543179, by rfl⟩ : syracuseStep 4724239 = 7086359) B7086359
theorem B6298985 : Blo 2069435 6298985 := bstep (se 2 (by rfl) ⟨2362119, by rfl⟩ : syracuseStep 6298985 = 4724239) B4724239
theorem B4199323 : Blo 2069435 4199323 := bstep (se 1 (by rfl) ⟨3149492, by rfl⟩ : syracuseStep 4199323 = 6298985) B6298985
theorem B5599097 : Blo 2069435 5599097 := bstep (se 2 (by rfl) ⟨2099661, by rfl⟩ : syracuseStep 5599097 = 4199323) B4199323
theorem B3732731 : Blo 2069435 3732731 := bstep (se 1 (by rfl) ⟨2799548, by rfl⟩ : syracuseStep 3732731 = 5599097) B5599097
theorem B2488487 : Blo 2069435 2488487 := bstep (se 1 (by rfl) ⟨1866365, by rfl⟩ : syracuseStep 2488487 = 3732731) B3732731
theorem B26543861 : Blo 2069435 26543861 := bstep (se 5 (by rfl) ⟨1244243, by rfl⟩ : syracuseStep 26543861 = 2488487) B2488487
theorem B17695907 : Blo 2069435 17695907 := bstep (se 1 (by rfl) ⟨13271930, by rfl⟩ : syracuseStep 17695907 = 26543861) B26543861
theorem B11797271 : Blo 2069435 11797271 := bstep (se 1 (by rfl) ⟨8847953, by rfl⟩ : syracuseStep 11797271 = 17695907) B17695907
theorem B7864847 : Blo 2069435 7864847 := bstep (se 1 (by rfl) ⟨5898635, by rfl⟩ : syracuseStep 7864847 = 11797271) B11797271
theorem B5243231 : Blo 2069435 5243231 := bstep (se 1 (by rfl) ⟨3932423, by rfl⟩ : syracuseStep 5243231 = 7864847) B7864847
theorem B3495487 : Blo 2069435 3495487 := bstep (se 1 (by rfl) ⟨2621615, by rfl⟩ : syracuseStep 3495487 = 5243231) B5243231
theorem B4660649 : Blo 2069435 4660649 := bstep (se 2 (by rfl) ⟨1747743, by rfl⟩ : syracuseStep 4660649 = 3495487) B3495487
theorem B3107099 : Blo 2069435 3107099 := bstep (se 1 (by rfl) ⟨2330324, by rfl⟩ : syracuseStep 3107099 = 4660649) B4660649
theorem B2071399 : Blo 2069435 2071399 := bstep (se 1 (by rfl) ⟨1553549, by rfl⟩ : syracuseStep 2071399 = 3107099) B3107099
theorem B2330329 : Blo 2069435 2330329 := bbase (se 2 (by rfl) ⟨873873, by rfl⟩ : syracuseStep 2330329 = 1747747) (by norm_num)
theorem B3107105 : Blo 2069435 3107105 := bstep (se 2 (by rfl) ⟨1165164, by rfl⟩ : syracuseStep 3107105 = 2330329) B2330329
theorem B2071403 : Blo 2069435 2071403 := bstep (se 1 (by rfl) ⟨1553552, by rfl⟩ : syracuseStep 2071403 = 3107105) B3107105
theorem B2211997 : Blo 2069435 2211997 := bbase (se 3 (by rfl) ⟨414749, by rfl⟩ : syracuseStep 2211997 = 829499) (by norm_num)
theorem B2949329 : Blo 2069435 2949329 := bstep (se 2 (by rfl) ⟨1105998, by rfl⟩ : syracuseStep 2949329 = 2211997) B2211997
theorem B7864877 : Blo 2069435 7864877 := bstep (se 3 (by rfl) ⟨1474664, by rfl⟩ : syracuseStep 7864877 = 2949329) B2949329
theorem B5243251 : Blo 2069435 5243251 := bstep (se 1 (by rfl) ⟨3932438, by rfl⟩ : syracuseStep 5243251 = 7864877) B7864877
theorem B6991001 : Blo 2069435 6991001 := bstep (se 2 (by rfl) ⟨2621625, by rfl⟩ : syracuseStep 6991001 = 5243251) B5243251
theorem B4660667 : Blo 2069435 4660667 := bstep (se 1 (by rfl) ⟨3495500, by rfl⟩ : syracuseStep 4660667 = 6991001) B6991001
theorem B3107111 : Blo 2069435 3107111 := bstep (se 1 (by rfl) ⟨2330333, by rfl⟩ : syracuseStep 3107111 = 4660667) B4660667
theorem B2071407 : Blo 2069435 2071407 := bstep (se 1 (by rfl) ⟨1553555, by rfl⟩ : syracuseStep 2071407 = 3107111) B3107111
theorem B3107117 : Blo 2069435 3107117 := bbase (se 3 (by rfl) ⟨582584, by rfl⟩ : syracuseStep 3107117 = 1165169) (by norm_num)
theorem B2071411 : Blo 2069435 2071411 := bstep (se 1 (by rfl) ⟨1553558, by rfl⟩ : syracuseStep 2071411 = 3107117) B3107117
theorem B4660685 : Blo 2069435 4660685 := bbase (se 3 (by rfl) ⟨873878, by rfl⟩ : syracuseStep 4660685 = 1747757) (by norm_num)
theorem B3107123 : Blo 2069435 3107123 := bstep (se 1 (by rfl) ⟨2330342, by rfl⟩ : syracuseStep 3107123 = 4660685) B4660685
theorem B2071415 : Blo 2069435 2071415 := bstep (se 1 (by rfl) ⟨1553561, by rfl⟩ : syracuseStep 2071415 = 3107123) B3107123
theorem B2621641 : Blo 2069435 2621641 := bbase (se 2 (by rfl) ⟨983115, by rfl⟩ : syracuseStep 2621641 = 1966231) (by norm_num)
theorem B3495521 : Blo 2069435 3495521 := bstep (se 2 (by rfl) ⟨1310820, by rfl⟩ : syracuseStep 3495521 = 2621641) B2621641
theorem B2330347 : Blo 2069435 2330347 := bstep (se 1 (by rfl) ⟨1747760, by rfl⟩ : syracuseStep 2330347 = 3495521) B3495521
theorem B3107129 : Blo 2069435 3107129 := bstep (se 2 (by rfl) ⟨1165173, by rfl⟩ : syracuseStep 3107129 = 2330347) B2330347
theorem B2071419 : Blo 2069435 2071419 := bstep (se 1 (by rfl) ⟨1553564, by rfl⟩ : syracuseStep 2071419 = 3107129) B3107129
theorem B8398741 : Blo 2069435 8398741 := bbase (se 6 (by rfl) ⟨196845, by rfl⟩ : syracuseStep 8398741 = 393691) (by norm_num)
theorem B11198321 : Blo 2069435 11198321 := bstep (se 2 (by rfl) ⟨4199370, by rfl⟩ : syracuseStep 11198321 = 8398741) B8398741
theorem B7465547 : Blo 2069435 7465547 := bstep (se 1 (by rfl) ⟨5599160, by rfl⟩ : syracuseStep 7465547 = 11198321) B11198321
theorem B19908125 : Blo 2069435 19908125 := bstep (se 3 (by rfl) ⟨3732773, by rfl⟩ : syracuseStep 19908125 = 7465547) B7465547
theorem B13272083 : Blo 2069435 13272083 := bstep (se 1 (by rfl) ⟨9954062, by rfl⟩ : syracuseStep 13272083 = 19908125) B19908125
theorem B8848055 : Blo 2069435 8848055 := bstep (se 1 (by rfl) ⟨6636041, by rfl⟩ : syracuseStep 8848055 = 13272083) B13272083
theorem B23594813 : Blo 2069435 23594813 := bstep (se 3 (by rfl) ⟨4424027, by rfl⟩ : syracuseStep 23594813 = 8848055) B8848055
theorem B15729875 : Blo 2069435 15729875 := bstep (se 1 (by rfl) ⟨11797406, by rfl⟩ : syracuseStep 15729875 = 23594813) B23594813
theorem B10486583 : Blo 2069435 10486583 := bstep (se 1 (by rfl) ⟨7864937, by rfl⟩ : syracuseStep 10486583 = 15729875) B15729875
theorem B6991055 : Blo 2069435 6991055 := bstep (se 1 (by rfl) ⟨5243291, by rfl⟩ : syracuseStep 6991055 = 10486583) B10486583
theorem B4660703 : Blo 2069435 4660703 := bstep (se 1 (by rfl) ⟨3495527, by rfl⟩ : syracuseStep 4660703 = 6991055) B6991055
theorem B3107135 : Blo 2069435 3107135 := bstep (se 1 (by rfl) ⟨2330351, by rfl⟩ : syracuseStep 3107135 = 4660703) B4660703
theorem B2071423 : Blo 2069435 2071423 := bstep (se 1 (by rfl) ⟨1553567, by rfl⟩ : syracuseStep 2071423 = 3107135) B3107135
theorem B3107141 : Blo 2069435 3107141 := bbase (se 4 (by rfl) ⟨291294, by rfl⟩ : syracuseStep 3107141 = 582589) (by norm_num)
theorem B2071427 : Blo 2069435 2071427 := bstep (se 1 (by rfl) ⟨1553570, by rfl⟩ : syracuseStep 2071427 = 3107141) B3107141
theorem B3495541 : Blo 2069435 3495541 := bbase (se 5 (by rfl) ⟨163853, by rfl⟩ : syracuseStep 3495541 = 327707) (by norm_num)
theorem B4660721 : Blo 2069435 4660721 := bstep (se 2 (by rfl) ⟨1747770, by rfl⟩ : syracuseStep 4660721 = 3495541) B3495541
theorem B3107147 : Blo 2069435 3107147 := bstep (se 1 (by rfl) ⟨2330360, by rfl⟩ : syracuseStep 3107147 = 4660721) B4660721
theorem B2071431 : Blo 2069435 2071431 := bstep (se 1 (by rfl) ⟨1553573, by rfl⟩ : syracuseStep 2071431 = 3107147) B3107147
theorem B2330365 : Blo 2069435 2330365 := bbase (se 3 (by rfl) ⟨436943, by rfl⟩ : syracuseStep 2330365 = 873887) (by norm_num)
theorem B3107153 : Blo 2069435 3107153 := bstep (se 2 (by rfl) ⟨1165182, by rfl⟩ : syracuseStep 3107153 = 2330365) B2330365
theorem B2071435 : Blo 2069435 2071435 := bstep (se 1 (by rfl) ⟨1553576, by rfl⟩ : syracuseStep 2071435 = 3107153) B3107153
theorem C0 (j : ℕ) (h1 : 517358 ≤ j) (h2 : j ≤ 517858) : Blo 2069435 (4 * j + 3) := by
  interval_cases j
  · exact B2069435
  · exact B2069439
  · exact B2069443
  · exact B2069447
  · exact B2069451
  · exact B2069455
  · exact B2069459
  · exact B2069463
  · exact B2069467
  · exact B2069471
  · exact B2069475
  · exact B2069479
  · exact B2069483
  · exact B2069487
  · exact B2069491
  · exact B2069495
  · exact B2069499
  · exact B2069503
  · exact B2069507
  · exact B2069511
  · exact B2069515
  · exact B2069519
  · exact B2069523
  · exact B2069527
  · exact B2069531
  · exact B2069535
  · exact B2069539
  · exact B2069543
  · exact B2069547
  · exact B2069551
  · exact B2069555
  · exact B2069559
  · exact B2069563
  · exact B2069567
  · exact B2069571
  · exact B2069575
  · exact B2069579
  · exact B2069583
  · exact B2069587
  · exact B2069591
  · exact B2069595
  · exact B2069599
  · exact B2069603
  · exact B2069607
  · exact B2069611
  · exact B2069615
  · exact B2069619
  · exact B2069623
  · exact B2069627
  · exact B2069631
  · exact B2069635
  · exact B2069639
  · exact B2069643
  · exact B2069647
  · exact B2069651
  · exact B2069655
  · exact B2069659
  · exact B2069663
  · exact B2069667
  · exact B2069671
  · exact B2069675
  · exact B2069679
  · exact B2069683
  · exact B2069687
  · exact B2069691
  · exact B2069695
  · exact B2069699
  · exact B2069703
  · exact B2069707
  · exact B2069711
  · exact B2069715
  · exact B2069719
  · exact B2069723
  · exact B2069727
  · exact B2069731
  · exact B2069735
  · exact B2069739
  · exact B2069743
  · exact B2069747
  · exact B2069751
  · exact B2069755
  · exact B2069759
  · exact B2069763
  · exact B2069767
  · exact B2069771
  · exact B2069775
  · exact B2069779
  · exact B2069783
  · exact B2069787
  · exact B2069791
  · exact B2069795
  · exact B2069799
  · exact B2069803
  · exact B2069807
  · exact B2069811
  · exact B2069815
  · exact B2069819
  · exact B2069823
  · exact B2069827
  · exact B2069831
  · exact B2069835
  · exact B2069839
  · exact B2069843
  · exact B2069847
  · exact B2069851
  · exact B2069855
  · exact B2069859
  · exact B2069863
  · exact B2069867
  · exact B2069871
  · exact B2069875
  · exact B2069879
  · exact B2069883
  · exact B2069887
  · exact B2069891
  · exact B2069895
  · exact B2069899
  · exact B2069903
  · exact B2069907
  · exact B2069911
  · exact B2069915
  · exact B2069919
  · exact B2069923
  · exact B2069927
  · exact B2069931
  · exact B2069935
  · exact B2069939
  · exact B2069943
  · exact B2069947
  · exact B2069951
  · exact B2069955
  · exact B2069959
  · exact B2069963
  · exact B2069967
  · exact B2069971
  · exact B2069975
  · exact B2069979
  · exact B2069983
  · exact B2069987
  · exact B2069991
  · exact B2069995
  · exact B2069999
  · exact B2070003
  · exact B2070007
  · exact B2070011
  · exact B2070015
  · exact B2070019
  · exact B2070023
  · exact B2070027
  · exact B2070031
  · exact B2070035
  · exact B2070039
  · exact B2070043
  · exact B2070047
  · exact B2070051
  · exact B2070055
  · exact B2070059
  · exact B2070063
  · exact B2070067
  · exact B2070071
  · exact B2070075
  · exact B2070079
  · exact B2070083
  · exact B2070087
  · exact B2070091
  · exact B2070095
  · exact B2070099
  · exact B2070103
  · exact B2070107
  · exact B2070111
  · exact B2070115
  · exact B2070119
  · exact B2070123
  · exact B2070127
  · exact B2070131
  · exact B2070135
  · exact B2070139
  · exact B2070143
  · exact B2070147
  · exact B2070151
  · exact B2070155
  · exact B2070159
  · exact B2070163
  · exact B2070167
  · exact B2070171
  · exact B2070175
  · exact B2070179
  · exact B2070183
  · exact B2070187
  · exact B2070191
  · exact B2070195
  · exact B2070199
  · exact B2070203
  · exact B2070207
  · exact B2070211
  · exact B2070215
  · exact B2070219
  · exact B2070223
  · exact B2070227
  · exact B2070231
  · exact B2070235
  · exact B2070239
  · exact B2070243
  · exact B2070247
  · exact B2070251
  · exact B2070255
  · exact B2070259
  · exact B2070263
  · exact B2070267
  · exact B2070271
  · exact B2070275
  · exact B2070279
  · exact B2070283
  · exact B2070287
  · exact B2070291
  · exact B2070295
  · exact B2070299
  · exact B2070303
  · exact B2070307
  · exact B2070311
  · exact B2070315
  · exact B2070319
  · exact B2070323
  · exact B2070327
  · exact B2070331
  · exact B2070335
  · exact B2070339
  · exact B2070343
  · exact B2070347
  · exact B2070351
  · exact B2070355
  · exact B2070359
  · exact B2070363
  · exact B2070367
  · exact B2070371
  · exact B2070375
  · exact B2070379
  · exact B2070383
  · exact B2070387
  · exact B2070391
  · exact B2070395
  · exact B2070399
  · exact B2070403
  · exact B2070407
  · exact B2070411
  · exact B2070415
  · exact B2070419
  · exact B2070423
  · exact B2070427
  · exact B2070431
  · exact B2070435
  · exact B2070439
  · exact B2070443
  · exact B2070447
  · exact B2070451
  · exact B2070455
  · exact B2070459
  · exact B2070463
  · exact B2070467
  · exact B2070471
  · exact B2070475
  · exact B2070479
  · exact B2070483
  · exact B2070487
  · exact B2070491
  · exact B2070495
  · exact B2070499
  · exact B2070503
  · exact B2070507
  · exact B2070511
  · exact B2070515
  · exact B2070519
  · exact B2070523
  · exact B2070527
  · exact B2070531
  · exact B2070535
  · exact B2070539
  · exact B2070543
  · exact B2070547
  · exact B2070551
  · exact B2070555
  · exact B2070559
  · exact B2070563
  · exact B2070567
  · exact B2070571
  · exact B2070575
  · exact B2070579
  · exact B2070583
  · exact B2070587
  · exact B2070591
  · exact B2070595
  · exact B2070599
  · exact B2070603
  · exact B2070607
  · exact B2070611
  · exact B2070615
  · exact B2070619
  · exact B2070623
  · exact B2070627
  · exact B2070631
  · exact B2070635
  · exact B2070639
  · exact B2070643
  · exact B2070647
  · exact B2070651
  · exact B2070655
  · exact B2070659
  · exact B2070663
  · exact B2070667
  · exact B2070671
  · exact B2070675
  · exact B2070679
  · exact B2070683
  · exact B2070687
  · exact B2070691
  · exact B2070695
  · exact B2070699
  · exact B2070703
  · exact B2070707
  · exact B2070711
  · exact B2070715
  · exact B2070719
  · exact B2070723
  · exact B2070727
  · exact B2070731
  · exact B2070735
  · exact B2070739
  · exact B2070743
  · exact B2070747
  · exact B2070751
  · exact B2070755
  · exact B2070759
  · exact B2070763
  · exact B2070767
  · exact B2070771
  · exact B2070775
  · exact B2070779
  · exact B2070783
  · exact B2070787
  · exact B2070791
  · exact B2070795
  · exact B2070799
  · exact B2070803
  · exact B2070807
  · exact B2070811
  · exact B2070815
  · exact B2070819
  · exact B2070823
  · exact B2070827
  · exact B2070831
  · exact B2070835
  · exact B2070839
  · exact B2070843
  · exact B2070847
  · exact B2070851
  · exact B2070855
  · exact B2070859
  · exact B2070863
  · exact B2070867
  · exact B2070871
  · exact B2070875
  · exact B2070879
  · exact B2070883
  · exact B2070887
  · exact B2070891
  · exact B2070895
  · exact B2070899
  · exact B2070903
  · exact B2070907
  · exact B2070911
  · exact B2070915
  · exact B2070919
  · exact B2070923
  · exact B2070927
  · exact B2070931
  · exact B2070935
  · exact B2070939
  · exact B2070943
  · exact B2070947
  · exact B2070951
  · exact B2070955
  · exact B2070959
  · exact B2070963
  · exact B2070967
  · exact B2070971
  · exact B2070975
  · exact B2070979
  · exact B2070983
  · exact B2070987
  · exact B2070991
  · exact B2070995
  · exact B2070999
  · exact B2071003
  · exact B2071007
  · exact B2071011
  · exact B2071015
  · exact B2071019
  · exact B2071023
  · exact B2071027
  · exact B2071031
  · exact B2071035
  · exact B2071039
  · exact B2071043
  · exact B2071047
  · exact B2071051
  · exact B2071055
  · exact B2071059
  · exact B2071063
  · exact B2071067
  · exact B2071071
  · exact B2071075
  · exact B2071079
  · exact B2071083
  · exact B2071087
  · exact B2071091
  · exact B2071095
  · exact B2071099
  · exact B2071103
  · exact B2071107
  · exact B2071111
  · exact B2071115
  · exact B2071119
  · exact B2071123
  · exact B2071127
  · exact B2071131
  · exact B2071135
  · exact B2071139
  · exact B2071143
  · exact B2071147
  · exact B2071151
  · exact B2071155
  · exact B2071159
  · exact B2071163
  · exact B2071167
  · exact B2071171
  · exact B2071175
  · exact B2071179
  · exact B2071183
  · exact B2071187
  · exact B2071191
  · exact B2071195
  · exact B2071199
  · exact B2071203
  · exact B2071207
  · exact B2071211
  · exact B2071215
  · exact B2071219
  · exact B2071223
  · exact B2071227
  · exact B2071231
  · exact B2071235
  · exact B2071239
  · exact B2071243
  · exact B2071247
  · exact B2071251
  · exact B2071255
  · exact B2071259
  · exact B2071263
  · exact B2071267
  · exact B2071271
  · exact B2071275
  · exact B2071279
  · exact B2071283
  · exact B2071287
  · exact B2071291
  · exact B2071295
  · exact B2071299
  · exact B2071303
  · exact B2071307
  · exact B2071311
  · exact B2071315
  · exact B2071319
  · exact B2071323
  · exact B2071327
  · exact B2071331
  · exact B2071335
  · exact B2071339
  · exact B2071343
  · exact B2071347
  · exact B2071351
  · exact B2071355
  · exact B2071359
  · exact B2071363
  · exact B2071367
  · exact B2071371
  · exact B2071375
  · exact B2071379
  · exact B2071383
  · exact B2071387
  · exact B2071391
  · exact B2071395
  · exact B2071399
  · exact B2071403
  · exact B2071407
  · exact B2071411
  · exact B2071415
  · exact B2071419
  · exact B2071423
  · exact B2071427
  · exact B2071431
  · exact B2071435
theorem solution (m : ℕ) (hlo : 2069435 ≤ m) (hhi : m ≤ 2071435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 517358 ≤ j := by omega
    have hj2 : j ≤ 517858 := by omega
    have hb : Blo 2069435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
