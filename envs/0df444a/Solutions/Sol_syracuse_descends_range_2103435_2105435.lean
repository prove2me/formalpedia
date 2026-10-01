-- Prove2me | solution 1 for syracuse_descends_range_2103435_2105435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:37.687688+00:00
-- url     : https://prove2.me/submissions/d4478319-2f5d-4144-864b-c6c8812ccbfa

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

theorem B2366365 : Blo 2103435 2366365 := bbase (se 3 (by rfl) ⟨443693, by rfl⟩ : syracuseStep 2366365 = 887387) (by norm_num)
theorem B3155153 : Blo 2103435 3155153 := bstep (se 2 (by rfl) ⟨1183182, by rfl⟩ : syracuseStep 3155153 = 2366365) B2366365
theorem B2103435 : Blo 2103435 2103435 := bstep (se 1 (by rfl) ⟨1577576, by rfl⟩ : syracuseStep 2103435 = 3155153) B3155153
theorem B7099109 : Blo 2103435 7099109 := bbase (se 4 (by rfl) ⟨665541, by rfl⟩ : syracuseStep 7099109 = 1331083) (by norm_num)
theorem B4732739 : Blo 2103435 4732739 := bstep (se 1 (by rfl) ⟨3549554, by rfl⟩ : syracuseStep 4732739 = 7099109) B7099109
theorem B3155159 : Blo 2103435 3155159 := bstep (se 1 (by rfl) ⟨2366369, by rfl⟩ : syracuseStep 3155159 = 4732739) B4732739
theorem B2103439 : Blo 2103435 2103439 := bstep (se 1 (by rfl) ⟨1577579, by rfl⟩ : syracuseStep 2103439 = 3155159) B3155159
theorem B3155165 : Blo 2103435 3155165 := bbase (se 3 (by rfl) ⟨591593, by rfl⟩ : syracuseStep 3155165 = 1183187) (by norm_num)
theorem B2103443 : Blo 2103435 2103443 := bstep (se 1 (by rfl) ⟨1577582, by rfl⟩ : syracuseStep 2103443 = 3155165) B3155165
theorem B4732757 : Blo 2103435 4732757 := bbase (se 9 (by rfl) ⟨13865, by rfl⟩ : syracuseStep 4732757 = 27731) (by norm_num)
theorem B3155171 : Blo 2103435 3155171 := bstep (se 1 (by rfl) ⟨2366378, by rfl⟩ : syracuseStep 3155171 = 4732757) B4732757
theorem B2103447 : Blo 2103435 2103447 := bstep (se 1 (by rfl) ⟨1577585, by rfl⟩ : syracuseStep 2103447 = 3155171) B3155171
theorem B5989909 : Blo 2103435 5989909 := bbase (se 6 (by rfl) ⟨140388, by rfl⟩ : syracuseStep 5989909 = 280777) (by norm_num)
theorem B7986545 : Blo 2103435 7986545 := bstep (se 2 (by rfl) ⟨2994954, by rfl⟩ : syracuseStep 7986545 = 5989909) B5989909
theorem B5324363 : Blo 2103435 5324363 := bstep (se 1 (by rfl) ⟨3993272, by rfl⟩ : syracuseStep 5324363 = 7986545) B7986545
theorem B3549575 : Blo 2103435 3549575 := bstep (se 1 (by rfl) ⟨2662181, by rfl⟩ : syracuseStep 3549575 = 5324363) B5324363
theorem B2366383 : Blo 2103435 2366383 := bstep (se 1 (by rfl) ⟨1774787, by rfl⟩ : syracuseStep 2366383 = 3549575) B3549575
theorem B3155177 : Blo 2103435 3155177 := bstep (se 2 (by rfl) ⟨1183191, by rfl⟩ : syracuseStep 3155177 = 2366383) B2366383
theorem B2103451 : Blo 2103435 2103451 := bstep (se 1 (by rfl) ⟨1577588, by rfl⟩ : syracuseStep 2103451 = 3155177) B3155177
theorem B7196021 : Blo 2103435 7196021 := bbase (se 5 (by rfl) ⟨337313, by rfl⟩ : syracuseStep 7196021 = 674627) (by norm_num)
theorem B4797347 : Blo 2103435 4797347 := bstep (se 1 (by rfl) ⟨3598010, by rfl⟩ : syracuseStep 4797347 = 7196021) B7196021
theorem B12792925 : Blo 2103435 12792925 := bstep (se 3 (by rfl) ⟨2398673, by rfl⟩ : syracuseStep 12792925 = 4797347) B4797347
theorem B17057233 : Blo 2103435 17057233 := bstep (se 2 (by rfl) ⟨6396462, by rfl⟩ : syracuseStep 17057233 = 12792925) B12792925
theorem B90971909 : Blo 2103435 90971909 := bstep (se 4 (by rfl) ⟨8528616, by rfl⟩ : syracuseStep 90971909 = 17057233) B17057233
theorem B60647939 : Blo 2103435 60647939 := bstep (se 1 (by rfl) ⟨45485954, by rfl⟩ : syracuseStep 60647939 = 90971909) B90971909
theorem B40431959 : Blo 2103435 40431959 := bstep (se 1 (by rfl) ⟨30323969, by rfl⟩ : syracuseStep 40431959 = 60647939) B60647939
theorem B26954639 : Blo 2103435 26954639 := bstep (se 1 (by rfl) ⟨20215979, by rfl⟩ : syracuseStep 26954639 = 40431959) B40431959
theorem B17969759 : Blo 2103435 17969759 := bstep (se 1 (by rfl) ⟨13477319, by rfl⟩ : syracuseStep 17969759 = 26954639) B26954639
theorem B11979839 : Blo 2103435 11979839 := bstep (se 1 (by rfl) ⟨8984879, by rfl⟩ : syracuseStep 11979839 = 17969759) B17969759
theorem B7986559 : Blo 2103435 7986559 := bstep (se 1 (by rfl) ⟨5989919, by rfl⟩ : syracuseStep 7986559 = 11979839) B11979839
theorem B10648745 : Blo 2103435 10648745 := bstep (se 2 (by rfl) ⟨3993279, by rfl⟩ : syracuseStep 10648745 = 7986559) B7986559
theorem B7099163 : Blo 2103435 7099163 := bstep (se 1 (by rfl) ⟨5324372, by rfl⟩ : syracuseStep 7099163 = 10648745) B10648745
theorem B4732775 : Blo 2103435 4732775 := bstep (se 1 (by rfl) ⟨3549581, by rfl⟩ : syracuseStep 4732775 = 7099163) B7099163
theorem B3155183 : Blo 2103435 3155183 := bstep (se 1 (by rfl) ⟨2366387, by rfl⟩ : syracuseStep 3155183 = 4732775) B4732775
theorem B2103455 : Blo 2103435 2103455 := bstep (se 1 (by rfl) ⟨1577591, by rfl⟩ : syracuseStep 2103455 = 3155183) B3155183
theorem B3155189 : Blo 2103435 3155189 := bbase (se 5 (by rfl) ⟨147899, by rfl⟩ : syracuseStep 3155189 = 295799) (by norm_num)
theorem B2103459 : Blo 2103435 2103459 := bstep (se 1 (by rfl) ⟨1577594, by rfl⟩ : syracuseStep 2103459 = 3155189) B3155189
theorem B6071669 : Blo 2103435 6071669 := bbase (se 5 (by rfl) ⟨284609, by rfl⟩ : syracuseStep 6071669 = 569219) (by norm_num)
theorem B4047779 : Blo 2103435 4047779 := bstep (se 1 (by rfl) ⟨3035834, by rfl⟩ : syracuseStep 4047779 = 6071669) B6071669
theorem B2698519 : Blo 2103435 2698519 := bstep (se 1 (by rfl) ⟨2023889, by rfl⟩ : syracuseStep 2698519 = 4047779) B4047779
theorem B3598025 : Blo 2103435 3598025 := bstep (se 2 (by rfl) ⟨1349259, by rfl⟩ : syracuseStep 3598025 = 2698519) B2698519
theorem B38378933 : Blo 2103435 38378933 := bstep (se 5 (by rfl) ⟨1799012, by rfl⟩ : syracuseStep 38378933 = 3598025) B3598025
theorem B25585955 : Blo 2103435 25585955 := bstep (se 1 (by rfl) ⟨19189466, by rfl⟩ : syracuseStep 25585955 = 38378933) B38378933
theorem B17057303 : Blo 2103435 17057303 := bstep (se 1 (by rfl) ⟨12792977, by rfl⟩ : syracuseStep 17057303 = 25585955) B25585955
theorem B11371535 : Blo 2103435 11371535 := bstep (se 1 (by rfl) ⟨8528651, by rfl⟩ : syracuseStep 11371535 = 17057303) B17057303
theorem B7581023 : Blo 2103435 7581023 := bstep (se 1 (by rfl) ⟨5685767, by rfl⟩ : syracuseStep 7581023 = 11371535) B11371535
theorem B5054015 : Blo 2103435 5054015 := bstep (se 1 (by rfl) ⟨3790511, by rfl⟩ : syracuseStep 5054015 = 7581023) B7581023
theorem B13477373 : Blo 2103435 13477373 := bstep (se 3 (by rfl) ⟨2527007, by rfl⟩ : syracuseStep 13477373 = 5054015) B5054015
theorem B8984915 : Blo 2103435 8984915 := bstep (se 1 (by rfl) ⟨6738686, by rfl⟩ : syracuseStep 8984915 = 13477373) B13477373
theorem B5989943 : Blo 2103435 5989943 := bstep (se 1 (by rfl) ⟨4492457, by rfl⟩ : syracuseStep 5989943 = 8984915) B8984915
theorem B3993295 : Blo 2103435 3993295 := bstep (se 1 (by rfl) ⟨2994971, by rfl⟩ : syracuseStep 3993295 = 5989943) B5989943
theorem B5324393 : Blo 2103435 5324393 := bstep (se 2 (by rfl) ⟨1996647, by rfl⟩ : syracuseStep 5324393 = 3993295) B3993295
theorem B3549595 : Blo 2103435 3549595 := bstep (se 1 (by rfl) ⟨2662196, by rfl⟩ : syracuseStep 3549595 = 5324393) B5324393
theorem B4732793 : Blo 2103435 4732793 := bstep (se 2 (by rfl) ⟨1774797, by rfl⟩ : syracuseStep 4732793 = 3549595) B3549595
theorem B3155195 : Blo 2103435 3155195 := bstep (se 1 (by rfl) ⟨2366396, by rfl⟩ : syracuseStep 3155195 = 4732793) B4732793
theorem B2103463 : Blo 2103435 2103463 := bstep (se 1 (by rfl) ⟨1577597, by rfl⟩ : syracuseStep 2103463 = 3155195) B3155195
theorem B2366401 : Blo 2103435 2366401 := bbase (se 2 (by rfl) ⟨887400, by rfl⟩ : syracuseStep 2366401 = 1774801) (by norm_num)
theorem B3155201 : Blo 2103435 3155201 := bstep (se 2 (by rfl) ⟨1183200, by rfl⟩ : syracuseStep 3155201 = 2366401) B2366401
theorem B2103467 : Blo 2103435 2103467 := bstep (se 1 (by rfl) ⟨1577600, by rfl⟩ : syracuseStep 2103467 = 3155201) B3155201
theorem B5324413 : Blo 2103435 5324413 := bbase (se 3 (by rfl) ⟨998327, by rfl⟩ : syracuseStep 5324413 = 1996655) (by norm_num)
theorem B7099217 : Blo 2103435 7099217 := bstep (se 2 (by rfl) ⟨2662206, by rfl⟩ : syracuseStep 7099217 = 5324413) B5324413
theorem B4732811 : Blo 2103435 4732811 := bstep (se 1 (by rfl) ⟨3549608, by rfl⟩ : syracuseStep 4732811 = 7099217) B7099217
theorem B3155207 : Blo 2103435 3155207 := bstep (se 1 (by rfl) ⟨2366405, by rfl⟩ : syracuseStep 3155207 = 4732811) B4732811
theorem B2103471 : Blo 2103435 2103471 := bstep (se 1 (by rfl) ⟨1577603, by rfl⟩ : syracuseStep 2103471 = 3155207) B3155207
theorem B3155213 : Blo 2103435 3155213 := bbase (se 3 (by rfl) ⟨591602, by rfl⟩ : syracuseStep 3155213 = 1183205) (by norm_num)
theorem B2103475 : Blo 2103435 2103475 := bstep (se 1 (by rfl) ⟨1577606, by rfl⟩ : syracuseStep 2103475 = 3155213) B3155213
theorem B4732829 : Blo 2103435 4732829 := bbase (se 3 (by rfl) ⟨887405, by rfl⟩ : syracuseStep 4732829 = 1774811) (by norm_num)
theorem B3155219 : Blo 2103435 3155219 := bstep (se 1 (by rfl) ⟨2366414, by rfl⟩ : syracuseStep 3155219 = 4732829) B4732829
theorem B2103479 : Blo 2103435 2103479 := bstep (se 1 (by rfl) ⟨1577609, by rfl⟩ : syracuseStep 2103479 = 3155219) B3155219
theorem B3549629 : Blo 2103435 3549629 := bbase (se 3 (by rfl) ⟨665555, by rfl⟩ : syracuseStep 3549629 = 1331111) (by norm_num)
theorem B2366419 : Blo 2103435 2366419 := bstep (se 1 (by rfl) ⟨1774814, by rfl⟩ : syracuseStep 2366419 = 3549629) B3549629
theorem B3155225 : Blo 2103435 3155225 := bstep (se 2 (by rfl) ⟨1183209, by rfl⟩ : syracuseStep 3155225 = 2366419) B2366419
theorem B2103483 : Blo 2103435 2103483 := bstep (se 1 (by rfl) ⟨1577612, by rfl⟩ : syracuseStep 2103483 = 3155225) B3155225
theorem B11980021 : Blo 2103435 11980021 := bbase (se 5 (by rfl) ⟨561563, by rfl⟩ : syracuseStep 11980021 = 1123127) (by norm_num)
theorem B15973361 : Blo 2103435 15973361 := bstep (se 2 (by rfl) ⟨5990010, by rfl⟩ : syracuseStep 15973361 = 11980021) B11980021
theorem B10648907 : Blo 2103435 10648907 := bstep (se 1 (by rfl) ⟨7986680, by rfl⟩ : syracuseStep 10648907 = 15973361) B15973361
theorem B7099271 : Blo 2103435 7099271 := bstep (se 1 (by rfl) ⟨5324453, by rfl⟩ : syracuseStep 7099271 = 10648907) B10648907
theorem B4732847 : Blo 2103435 4732847 := bstep (se 1 (by rfl) ⟨3549635, by rfl⟩ : syracuseStep 4732847 = 7099271) B7099271
theorem B3155231 : Blo 2103435 3155231 := bstep (se 1 (by rfl) ⟨2366423, by rfl⟩ : syracuseStep 3155231 = 4732847) B4732847
theorem B2103487 : Blo 2103435 2103487 := bstep (se 1 (by rfl) ⟨1577615, by rfl⟩ : syracuseStep 2103487 = 3155231) B3155231
theorem B3155237 : Blo 2103435 3155237 := bbase (se 4 (by rfl) ⟨295803, by rfl⟩ : syracuseStep 3155237 = 591607) (by norm_num)
theorem B2103491 : Blo 2103435 2103491 := bstep (se 1 (by rfl) ⟨1577618, by rfl⟩ : syracuseStep 2103491 = 3155237) B3155237
theorem B2662237 : Blo 2103435 2662237 := bbase (se 3 (by rfl) ⟨499169, by rfl⟩ : syracuseStep 2662237 = 998339) (by norm_num)
theorem B3549649 : Blo 2103435 3549649 := bstep (se 2 (by rfl) ⟨1331118, by rfl⟩ : syracuseStep 3549649 = 2662237) B2662237
theorem B4732865 : Blo 2103435 4732865 := bstep (se 2 (by rfl) ⟨1774824, by rfl⟩ : syracuseStep 4732865 = 3549649) B3549649
theorem B3155243 : Blo 2103435 3155243 := bstep (se 1 (by rfl) ⟨2366432, by rfl⟩ : syracuseStep 3155243 = 4732865) B4732865
theorem B2103495 : Blo 2103435 2103495 := bstep (se 1 (by rfl) ⟨1577621, by rfl⟩ : syracuseStep 2103495 = 3155243) B3155243
theorem B2366437 : Blo 2103435 2366437 := bbase (se 4 (by rfl) ⟨221853, by rfl⟩ : syracuseStep 2366437 = 443707) (by norm_num)
theorem B3155249 : Blo 2103435 3155249 := bstep (se 2 (by rfl) ⟨1183218, by rfl⟩ : syracuseStep 3155249 = 2366437) B2366437
theorem B2103499 : Blo 2103435 2103499 := bstep (se 1 (by rfl) ⟨1577624, by rfl⟩ : syracuseStep 2103499 = 3155249) B3155249
theorem B8763125 : Blo 2103435 8763125 := bbase (se 5 (by rfl) ⟨410771, by rfl⟩ : syracuseStep 8763125 = 821543) (by norm_num)
theorem B23368333 : Blo 2103435 23368333 := bstep (se 3 (by rfl) ⟨4381562, by rfl⟩ : syracuseStep 23368333 = 8763125) B8763125
theorem B31157777 : Blo 2103435 31157777 := bstep (se 2 (by rfl) ⟨11684166, by rfl⟩ : syracuseStep 31157777 = 23368333) B23368333
theorem B20771851 : Blo 2103435 20771851 := bstep (se 1 (by rfl) ⟨15578888, by rfl⟩ : syracuseStep 20771851 = 31157777) B31157777
theorem B27695801 : Blo 2103435 27695801 := bstep (se 2 (by rfl) ⟨10385925, by rfl⟩ : syracuseStep 27695801 = 20771851) B20771851
theorem B73855469 : Blo 2103435 73855469 := bstep (se 3 (by rfl) ⟨13847900, by rfl⟩ : syracuseStep 73855469 = 27695801) B27695801
theorem B49236979 : Blo 2103435 49236979 := bstep (se 1 (by rfl) ⟨36927734, by rfl⟩ : syracuseStep 49236979 = 73855469) B73855469
theorem B65649305 : Blo 2103435 65649305 := bstep (se 2 (by rfl) ⟨24618489, by rfl⟩ : syracuseStep 65649305 = 49236979) B49236979
theorem B43766203 : Blo 2103435 43766203 := bstep (se 1 (by rfl) ⟨32824652, by rfl⟩ : syracuseStep 43766203 = 65649305) B65649305
theorem B58354937 : Blo 2103435 58354937 := bstep (se 2 (by rfl) ⟨21883101, by rfl⟩ : syracuseStep 58354937 = 43766203) B43766203
theorem B38903291 : Blo 2103435 38903291 := bstep (se 1 (by rfl) ⟨29177468, by rfl⟩ : syracuseStep 38903291 = 58354937) B58354937
theorem B25935527 : Blo 2103435 25935527 := bstep (se 1 (by rfl) ⟨19451645, by rfl⟩ : syracuseStep 25935527 = 38903291) B38903291
theorem B17290351 : Blo 2103435 17290351 := bstep (se 1 (by rfl) ⟨12967763, by rfl⟩ : syracuseStep 17290351 = 25935527) B25935527
theorem B92215205 : Blo 2103435 92215205 := bstep (se 4 (by rfl) ⟨8645175, by rfl⟩ : syracuseStep 92215205 = 17290351) B17290351
theorem B61476803 : Blo 2103435 61476803 := bstep (se 1 (by rfl) ⟨46107602, by rfl⟩ : syracuseStep 61476803 = 92215205) B92215205
theorem B40984535 : Blo 2103435 40984535 := bstep (se 1 (by rfl) ⟨30738401, by rfl⟩ : syracuseStep 40984535 = 61476803) B61476803
theorem B27323023 : Blo 2103435 27323023 := bstep (se 1 (by rfl) ⟨20492267, by rfl⟩ : syracuseStep 27323023 = 40984535) B40984535
theorem B36430697 : Blo 2103435 36430697 := bstep (se 2 (by rfl) ⟨13661511, by rfl⟩ : syracuseStep 36430697 = 27323023) B27323023
theorem B24287131 : Blo 2103435 24287131 := bstep (se 1 (by rfl) ⟨18215348, by rfl⟩ : syracuseStep 24287131 = 36430697) B36430697
theorem B32382841 : Blo 2103435 32382841 := bstep (se 2 (by rfl) ⟨12143565, by rfl⟩ : syracuseStep 32382841 = 24287131) B24287131
theorem B43177121 : Blo 2103435 43177121 := bstep (se 2 (by rfl) ⟨16191420, by rfl⟩ : syracuseStep 43177121 = 32382841) B32382841
theorem B28784747 : Blo 2103435 28784747 := bstep (se 1 (by rfl) ⟨21588560, by rfl⟩ : syracuseStep 28784747 = 43177121) B43177121
theorem B76759325 : Blo 2103435 76759325 := bstep (se 3 (by rfl) ⟨14392373, by rfl⟩ : syracuseStep 76759325 = 28784747) B28784747
theorem B51172883 : Blo 2103435 51172883 := bstep (se 1 (by rfl) ⟨38379662, by rfl⟩ : syracuseStep 51172883 = 76759325) B76759325
theorem B34115255 : Blo 2103435 34115255 := bstep (se 1 (by rfl) ⟨25586441, by rfl⟩ : syracuseStep 34115255 = 51172883) B51172883
theorem B22743503 : Blo 2103435 22743503 := bstep (se 1 (by rfl) ⟨17057627, by rfl⟩ : syracuseStep 22743503 = 34115255) B34115255
theorem B15162335 : Blo 2103435 15162335 := bstep (se 1 (by rfl) ⟨11371751, by rfl⟩ : syracuseStep 15162335 = 22743503) B22743503
theorem B10108223 : Blo 2103435 10108223 := bstep (se 1 (by rfl) ⟨7581167, by rfl⟩ : syracuseStep 10108223 = 15162335) B15162335
theorem B6738815 : Blo 2103435 6738815 := bstep (se 1 (by rfl) ⟨5054111, by rfl⟩ : syracuseStep 6738815 = 10108223) B10108223
theorem B4492543 : Blo 2103435 4492543 := bstep (se 1 (by rfl) ⟨3369407, by rfl⟩ : syracuseStep 4492543 = 6738815) B6738815
theorem B5990057 : Blo 2103435 5990057 := bstep (se 2 (by rfl) ⟨2246271, by rfl⟩ : syracuseStep 5990057 = 4492543) B4492543
theorem B3993371 : Blo 2103435 3993371 := bstep (se 1 (by rfl) ⟨2995028, by rfl⟩ : syracuseStep 3993371 = 5990057) B5990057
theorem B2662247 : Blo 2103435 2662247 := bstep (se 1 (by rfl) ⟨1996685, by rfl⟩ : syracuseStep 2662247 = 3993371) B3993371
theorem B7099325 : Blo 2103435 7099325 := bstep (se 3 (by rfl) ⟨1331123, by rfl⟩ : syracuseStep 7099325 = 2662247) B2662247
theorem B4732883 : Blo 2103435 4732883 := bstep (se 1 (by rfl) ⟨3549662, by rfl⟩ : syracuseStep 4732883 = 7099325) B7099325
theorem B3155255 : Blo 2103435 3155255 := bstep (se 1 (by rfl) ⟨2366441, by rfl⟩ : syracuseStep 3155255 = 4732883) B4732883
theorem B2103503 : Blo 2103435 2103503 := bstep (se 1 (by rfl) ⟨1577627, by rfl⟩ : syracuseStep 2103503 = 3155255) B3155255
theorem B3155261 : Blo 2103435 3155261 := bbase (se 3 (by rfl) ⟨591611, by rfl⟩ : syracuseStep 3155261 = 1183223) (by norm_num)
theorem B2103507 : Blo 2103435 2103507 := bstep (se 1 (by rfl) ⟨1577630, by rfl⟩ : syracuseStep 2103507 = 3155261) B3155261
theorem B4732901 : Blo 2103435 4732901 := bbase (se 4 (by rfl) ⟨443709, by rfl⟩ : syracuseStep 4732901 = 887419) (by norm_num)
theorem B3155267 : Blo 2103435 3155267 := bstep (se 1 (by rfl) ⟨2366450, by rfl⟩ : syracuseStep 3155267 = 4732901) B4732901
theorem B2103511 : Blo 2103435 2103511 := bstep (se 1 (by rfl) ⟨1577633, by rfl⟩ : syracuseStep 2103511 = 3155267) B3155267
theorem B5324525 : Blo 2103435 5324525 := bbase (se 3 (by rfl) ⟨998348, by rfl⟩ : syracuseStep 5324525 = 1996697) (by norm_num)
theorem B3549683 : Blo 2103435 3549683 := bstep (se 1 (by rfl) ⟨2662262, by rfl⟩ : syracuseStep 3549683 = 5324525) B5324525
theorem B2366455 : Blo 2103435 2366455 := bstep (se 1 (by rfl) ⟨1774841, by rfl⟩ : syracuseStep 2366455 = 3549683) B3549683
theorem B3155273 : Blo 2103435 3155273 := bstep (se 2 (by rfl) ⟨1183227, by rfl⟩ : syracuseStep 3155273 = 2366455) B2366455
theorem B2103515 : Blo 2103435 2103515 := bstep (se 1 (by rfl) ⟨1577636, by rfl⟩ : syracuseStep 2103515 = 3155273) B3155273
theorem B3790613 : Blo 2103435 3790613 := bbase (se 6 (by rfl) ⟨88842, by rfl⟩ : syracuseStep 3790613 = 177685) (by norm_num)
theorem B2527075 : Blo 2103435 2527075 := bstep (se 1 (by rfl) ⟨1895306, by rfl⟩ : syracuseStep 2527075 = 3790613) B3790613
theorem B3369433 : Blo 2103435 3369433 := bstep (se 2 (by rfl) ⟨1263537, by rfl⟩ : syracuseStep 3369433 = 2527075) B2527075
theorem B4492577 : Blo 2103435 4492577 := bstep (se 2 (by rfl) ⟨1684716, by rfl⟩ : syracuseStep 4492577 = 3369433) B3369433
theorem B2995051 : Blo 2103435 2995051 := bstep (se 1 (by rfl) ⟨2246288, by rfl⟩ : syracuseStep 2995051 = 4492577) B4492577
theorem B3993401 : Blo 2103435 3993401 := bstep (se 2 (by rfl) ⟨1497525, by rfl⟩ : syracuseStep 3993401 = 2995051) B2995051
theorem B10649069 : Blo 2103435 10649069 := bstep (se 3 (by rfl) ⟨1996700, by rfl⟩ : syracuseStep 10649069 = 3993401) B3993401
theorem B7099379 : Blo 2103435 7099379 := bstep (se 1 (by rfl) ⟨5324534, by rfl⟩ : syracuseStep 7099379 = 10649069) B10649069
theorem B4732919 : Blo 2103435 4732919 := bstep (se 1 (by rfl) ⟨3549689, by rfl⟩ : syracuseStep 4732919 = 7099379) B7099379
theorem B3155279 : Blo 2103435 3155279 := bstep (se 1 (by rfl) ⟨2366459, by rfl⟩ : syracuseStep 3155279 = 4732919) B4732919
theorem B2103519 : Blo 2103435 2103519 := bstep (se 1 (by rfl) ⟨1577639, by rfl⟩ : syracuseStep 2103519 = 3155279) B3155279
theorem B3155285 : Blo 2103435 3155285 := bbase (se 12 (by rfl) ⟨1155, by rfl⟩ : syracuseStep 3155285 = 2311) (by norm_num)
theorem B2103523 : Blo 2103435 2103523 := bstep (se 1 (by rfl) ⟨1577642, by rfl⟩ : syracuseStep 2103523 = 3155285) B3155285
theorem B2246297 : Blo 2103435 2246297 := bbase (se 2 (by rfl) ⟨842361, by rfl⟩ : syracuseStep 2246297 = 1684723) (by norm_num)
theorem B5990125 : Blo 2103435 5990125 := bstep (se 3 (by rfl) ⟨1123148, by rfl⟩ : syracuseStep 5990125 = 2246297) B2246297
theorem B7986833 : Blo 2103435 7986833 := bstep (se 2 (by rfl) ⟨2995062, by rfl⟩ : syracuseStep 7986833 = 5990125) B5990125
theorem B5324555 : Blo 2103435 5324555 := bstep (se 1 (by rfl) ⟨3993416, by rfl⟩ : syracuseStep 5324555 = 7986833) B7986833
theorem B3549703 : Blo 2103435 3549703 := bstep (se 1 (by rfl) ⟨2662277, by rfl⟩ : syracuseStep 3549703 = 5324555) B5324555
theorem B4732937 : Blo 2103435 4732937 := bstep (se 2 (by rfl) ⟨1774851, by rfl⟩ : syracuseStep 4732937 = 3549703) B3549703
theorem B3155291 : Blo 2103435 3155291 := bstep (se 1 (by rfl) ⟨2366468, by rfl⟩ : syracuseStep 3155291 = 4732937) B4732937
theorem B2103527 : Blo 2103435 2103527 := bstep (se 1 (by rfl) ⟨1577645, by rfl⟩ : syracuseStep 2103527 = 3155291) B3155291
theorem B2366473 : Blo 2103435 2366473 := bbase (se 2 (by rfl) ⟨887427, by rfl⟩ : syracuseStep 2366473 = 1774855) (by norm_num)
theorem B3155297 : Blo 2103435 3155297 := bstep (se 2 (by rfl) ⟨1183236, by rfl⟩ : syracuseStep 3155297 = 2366473) B2366473
theorem B2103531 : Blo 2103435 2103531 := bstep (se 1 (by rfl) ⟨1577648, by rfl⟩ : syracuseStep 2103531 = 3155297) B3155297
theorem B9595061 : Blo 2103435 9595061 := bbase (se 5 (by rfl) ⟨449768, by rfl⟩ : syracuseStep 9595061 = 899537) (by norm_num)
theorem B6396707 : Blo 2103435 6396707 := bstep (se 1 (by rfl) ⟨4797530, by rfl⟩ : syracuseStep 6396707 = 9595061) B9595061
theorem B4264471 : Blo 2103435 4264471 := bstep (se 1 (by rfl) ⟨3198353, by rfl⟩ : syracuseStep 4264471 = 6396707) B6396707
theorem B5685961 : Blo 2103435 5685961 := bstep (se 2 (by rfl) ⟨2132235, by rfl⟩ : syracuseStep 5685961 = 4264471) B4264471
theorem B7581281 : Blo 2103435 7581281 := bstep (se 2 (by rfl) ⟨2842980, by rfl⟩ : syracuseStep 7581281 = 5685961) B5685961
theorem B20216749 : Blo 2103435 20216749 := bstep (se 3 (by rfl) ⟨3790640, by rfl⟩ : syracuseStep 20216749 = 7581281) B7581281
theorem B26955665 : Blo 2103435 26955665 := bstep (se 2 (by rfl) ⟨10108374, by rfl⟩ : syracuseStep 26955665 = 20216749) B20216749
theorem B17970443 : Blo 2103435 17970443 := bstep (se 1 (by rfl) ⟨13477832, by rfl⟩ : syracuseStep 17970443 = 26955665) B26955665
theorem B11980295 : Blo 2103435 11980295 := bstep (se 1 (by rfl) ⟨8985221, by rfl⟩ : syracuseStep 11980295 = 17970443) B17970443
theorem B7986863 : Blo 2103435 7986863 := bstep (se 1 (by rfl) ⟨5990147, by rfl⟩ : syracuseStep 7986863 = 11980295) B11980295
theorem B5324575 : Blo 2103435 5324575 := bstep (se 1 (by rfl) ⟨3993431, by rfl⟩ : syracuseStep 5324575 = 7986863) B7986863
theorem B7099433 : Blo 2103435 7099433 := bstep (se 2 (by rfl) ⟨2662287, by rfl⟩ : syracuseStep 7099433 = 5324575) B5324575
theorem B4732955 : Blo 2103435 4732955 := bstep (se 1 (by rfl) ⟨3549716, by rfl⟩ : syracuseStep 4732955 = 7099433) B7099433
theorem B3155303 : Blo 2103435 3155303 := bstep (se 1 (by rfl) ⟨2366477, by rfl⟩ : syracuseStep 3155303 = 4732955) B4732955
theorem B2103535 : Blo 2103435 2103535 := bstep (se 1 (by rfl) ⟨1577651, by rfl⟩ : syracuseStep 2103535 = 3155303) B3155303
theorem B3155309 : Blo 2103435 3155309 := bbase (se 3 (by rfl) ⟨591620, by rfl⟩ : syracuseStep 3155309 = 1183241) (by norm_num)
theorem B2103539 : Blo 2103435 2103539 := bstep (se 1 (by rfl) ⟨1577654, by rfl⟩ : syracuseStep 2103539 = 3155309) B3155309
theorem B4732973 : Blo 2103435 4732973 := bbase (se 3 (by rfl) ⟨887432, by rfl⟩ : syracuseStep 4732973 = 1774865) (by norm_num)
theorem B3155315 : Blo 2103435 3155315 := bstep (se 1 (by rfl) ⟨2366486, by rfl⟩ : syracuseStep 3155315 = 4732973) B4732973
theorem B2103543 : Blo 2103435 2103543 := bstep (se 1 (by rfl) ⟨1577657, by rfl⟩ : syracuseStep 2103543 = 3155315) B3155315
theorem B4047941 : Blo 2103435 4047941 := bbase (se 4 (by rfl) ⟨379494, by rfl⟩ : syracuseStep 4047941 = 758989) (by norm_num)
theorem B10794509 : Blo 2103435 10794509 := bstep (se 3 (by rfl) ⟨2023970, by rfl⟩ : syracuseStep 10794509 = 4047941) B4047941
theorem B7196339 : Blo 2103435 7196339 := bstep (se 1 (by rfl) ⟨5397254, by rfl⟩ : syracuseStep 7196339 = 10794509) B10794509
theorem B4797559 : Blo 2103435 4797559 := bstep (se 1 (by rfl) ⟨3598169, by rfl⟩ : syracuseStep 4797559 = 7196339) B7196339
theorem B6396745 : Blo 2103435 6396745 := bstep (se 2 (by rfl) ⟨2398779, by rfl⟩ : syracuseStep 6396745 = 4797559) B4797559
theorem B8528993 : Blo 2103435 8528993 := bstep (se 2 (by rfl) ⟨3198372, by rfl⟩ : syracuseStep 8528993 = 6396745) B6396745
theorem B5685995 : Blo 2103435 5685995 := bstep (se 1 (by rfl) ⟨4264496, by rfl⟩ : syracuseStep 5685995 = 8528993) B8528993
theorem B15162653 : Blo 2103435 15162653 := bstep (se 3 (by rfl) ⟨2842997, by rfl⟩ : syracuseStep 15162653 = 5685995) B5685995
theorem B10108435 : Blo 2103435 10108435 := bstep (se 1 (by rfl) ⟨7581326, by rfl⟩ : syracuseStep 10108435 = 15162653) B15162653
theorem B13477913 : Blo 2103435 13477913 := bstep (se 2 (by rfl) ⟨5054217, by rfl⟩ : syracuseStep 13477913 = 10108435) B10108435
theorem B8985275 : Blo 2103435 8985275 := bstep (se 1 (by rfl) ⟨6738956, by rfl⟩ : syracuseStep 8985275 = 13477913) B13477913
theorem B5990183 : Blo 2103435 5990183 := bstep (se 1 (by rfl) ⟨4492637, by rfl⟩ : syracuseStep 5990183 = 8985275) B8985275
theorem B3993455 : Blo 2103435 3993455 := bstep (se 1 (by rfl) ⟨2995091, by rfl⟩ : syracuseStep 3993455 = 5990183) B5990183
theorem B2662303 : Blo 2103435 2662303 := bstep (se 1 (by rfl) ⟨1996727, by rfl⟩ : syracuseStep 2662303 = 3993455) B3993455
theorem B3549737 : Blo 2103435 3549737 := bstep (se 2 (by rfl) ⟨1331151, by rfl⟩ : syracuseStep 3549737 = 2662303) B2662303
theorem B2366491 : Blo 2103435 2366491 := bstep (se 1 (by rfl) ⟨1774868, by rfl⟩ : syracuseStep 2366491 = 3549737) B3549737
theorem B3155321 : Blo 2103435 3155321 := bstep (se 2 (by rfl) ⟨1183245, by rfl⟩ : syracuseStep 3155321 = 2366491) B2366491
theorem B2103547 : Blo 2103435 2103547 := bstep (se 1 (by rfl) ⟨1577660, by rfl⟩ : syracuseStep 2103547 = 3155321) B3155321
theorem B15162677 : Blo 2103435 15162677 := bbase (se 5 (by rfl) ⟨710750, by rfl⟩ : syracuseStep 15162677 = 1421501) (by norm_num)
theorem B10108451 : Blo 2103435 10108451 := bstep (se 1 (by rfl) ⟨7581338, by rfl⟩ : syracuseStep 10108451 = 15162677) B15162677
theorem B6738967 : Blo 2103435 6738967 := bstep (se 1 (by rfl) ⟨5054225, by rfl⟩ : syracuseStep 6738967 = 10108451) B10108451
theorem B35941157 : Blo 2103435 35941157 := bstep (se 4 (by rfl) ⟨3369483, by rfl⟩ : syracuseStep 35941157 = 6738967) B6738967
theorem B23960771 : Blo 2103435 23960771 := bstep (se 1 (by rfl) ⟨17970578, by rfl⟩ : syracuseStep 23960771 = 35941157) B35941157
theorem B15973847 : Blo 2103435 15973847 := bstep (se 1 (by rfl) ⟨11980385, by rfl⟩ : syracuseStep 15973847 = 23960771) B23960771
theorem B10649231 : Blo 2103435 10649231 := bstep (se 1 (by rfl) ⟨7986923, by rfl⟩ : syracuseStep 10649231 = 15973847) B15973847
theorem B7099487 : Blo 2103435 7099487 := bstep (se 1 (by rfl) ⟨5324615, by rfl⟩ : syracuseStep 7099487 = 10649231) B10649231
theorem B4732991 : Blo 2103435 4732991 := bstep (se 1 (by rfl) ⟨3549743, by rfl⟩ : syracuseStep 4732991 = 7099487) B7099487
theorem B3155327 : Blo 2103435 3155327 := bstep (se 1 (by rfl) ⟨2366495, by rfl⟩ : syracuseStep 3155327 = 4732991) B4732991
theorem B2103551 : Blo 2103435 2103551 := bstep (se 1 (by rfl) ⟨1577663, by rfl⟩ : syracuseStep 2103551 = 3155327) B3155327
theorem B3155333 : Blo 2103435 3155333 := bbase (se 4 (by rfl) ⟨295812, by rfl⟩ : syracuseStep 3155333 = 591625) (by norm_num)
theorem B2103555 : Blo 2103435 2103555 := bstep (se 1 (by rfl) ⟨1577666, by rfl⟩ : syracuseStep 2103555 = 3155333) B3155333
theorem B3549757 : Blo 2103435 3549757 := bbase (se 3 (by rfl) ⟨665579, by rfl⟩ : syracuseStep 3549757 = 1331159) (by norm_num)
theorem B4733009 : Blo 2103435 4733009 := bstep (se 2 (by rfl) ⟨1774878, by rfl⟩ : syracuseStep 4733009 = 3549757) B3549757
theorem B3155339 : Blo 2103435 3155339 := bstep (se 1 (by rfl) ⟨2366504, by rfl⟩ : syracuseStep 3155339 = 4733009) B4733009
theorem B2103559 : Blo 2103435 2103559 := bstep (se 1 (by rfl) ⟨1577669, by rfl⟩ : syracuseStep 2103559 = 3155339) B3155339
theorem B2366509 : Blo 2103435 2366509 := bbase (se 3 (by rfl) ⟨443720, by rfl⟩ : syracuseStep 2366509 = 887441) (by norm_num)
theorem B3155345 : Blo 2103435 3155345 := bstep (se 2 (by rfl) ⟨1183254, by rfl⟩ : syracuseStep 3155345 = 2366509) B2366509
theorem B2103563 : Blo 2103435 2103563 := bstep (se 1 (by rfl) ⟨1577672, by rfl⟩ : syracuseStep 2103563 = 3155345) B3155345
theorem B7099541 : Blo 2103435 7099541 := bbase (se 6 (by rfl) ⟨166395, by rfl⟩ : syracuseStep 7099541 = 332791) (by norm_num)
theorem B4733027 : Blo 2103435 4733027 := bstep (se 1 (by rfl) ⟨3549770, by rfl⟩ : syracuseStep 4733027 = 7099541) B7099541
theorem B3155351 : Blo 2103435 3155351 := bstep (se 1 (by rfl) ⟨2366513, by rfl⟩ : syracuseStep 3155351 = 4733027) B4733027
theorem B2103567 : Blo 2103435 2103567 := bstep (se 1 (by rfl) ⟨1577675, by rfl⟩ : syracuseStep 2103567 = 3155351) B3155351
theorem B3155357 : Blo 2103435 3155357 := bbase (se 3 (by rfl) ⟨591629, by rfl⟩ : syracuseStep 3155357 = 1183259) (by norm_num)
theorem B2103571 : Blo 2103435 2103571 := bstep (se 1 (by rfl) ⟨1577678, by rfl⟩ : syracuseStep 2103571 = 3155357) B3155357
theorem B4733045 : Blo 2103435 4733045 := bbase (se 5 (by rfl) ⟨221861, by rfl⟩ : syracuseStep 4733045 = 443723) (by norm_num)
theorem B3155363 : Blo 2103435 3155363 := bstep (se 1 (by rfl) ⟨2366522, by rfl⟩ : syracuseStep 3155363 = 4733045) B4733045
theorem B2103575 : Blo 2103435 2103575 := bstep (se 1 (by rfl) ⟨1577681, by rfl⟩ : syracuseStep 2103575 = 3155363) B3155363
theorem B2132281 : Blo 2103435 2132281 := bbase (se 2 (by rfl) ⟨799605, by rfl⟩ : syracuseStep 2132281 = 1599211) (by norm_num)
theorem B2843041 : Blo 2103435 2843041 := bstep (se 2 (by rfl) ⟨1066140, by rfl⟩ : syracuseStep 2843041 = 2132281) B2132281
theorem B3790721 : Blo 2103435 3790721 := bstep (se 2 (by rfl) ⟨1421520, by rfl⟩ : syracuseStep 3790721 = 2843041) B2843041
theorem B2527147 : Blo 2103435 2527147 := bstep (se 1 (by rfl) ⟨1895360, by rfl⟩ : syracuseStep 2527147 = 3790721) B3790721
theorem B3369529 : Blo 2103435 3369529 := bstep (se 2 (by rfl) ⟨1263573, by rfl⟩ : syracuseStep 3369529 = 2527147) B2527147
theorem B17970821 : Blo 2103435 17970821 := bstep (se 4 (by rfl) ⟨1684764, by rfl⟩ : syracuseStep 17970821 = 3369529) B3369529
theorem B11980547 : Blo 2103435 11980547 := bstep (se 1 (by rfl) ⟨8985410, by rfl⟩ : syracuseStep 11980547 = 17970821) B17970821
theorem B7987031 : Blo 2103435 7987031 := bstep (se 1 (by rfl) ⟨5990273, by rfl⟩ : syracuseStep 7987031 = 11980547) B11980547
theorem B5324687 : Blo 2103435 5324687 := bstep (se 1 (by rfl) ⟨3993515, by rfl⟩ : syracuseStep 5324687 = 7987031) B7987031
theorem B3549791 : Blo 2103435 3549791 := bstep (se 1 (by rfl) ⟨2662343, by rfl⟩ : syracuseStep 3549791 = 5324687) B5324687
theorem B2366527 : Blo 2103435 2366527 := bstep (se 1 (by rfl) ⟨1774895, by rfl⟩ : syracuseStep 2366527 = 3549791) B3549791
theorem B3155369 : Blo 2103435 3155369 := bstep (se 2 (by rfl) ⟨1183263, by rfl⟩ : syracuseStep 3155369 = 2366527) B2366527
theorem B2103579 : Blo 2103435 2103579 := bstep (se 1 (by rfl) ⟨1577684, by rfl⟩ : syracuseStep 2103579 = 3155369) B3155369
theorem B7987045 : Blo 2103435 7987045 := bbase (se 4 (by rfl) ⟨748785, by rfl⟩ : syracuseStep 7987045 = 1497571) (by norm_num)
theorem B10649393 : Blo 2103435 10649393 := bstep (se 2 (by rfl) ⟨3993522, by rfl⟩ : syracuseStep 10649393 = 7987045) B7987045
theorem B7099595 : Blo 2103435 7099595 := bstep (se 1 (by rfl) ⟨5324696, by rfl⟩ : syracuseStep 7099595 = 10649393) B10649393
theorem B4733063 : Blo 2103435 4733063 := bstep (se 1 (by rfl) ⟨3549797, by rfl⟩ : syracuseStep 4733063 = 7099595) B7099595
theorem B3155375 : Blo 2103435 3155375 := bstep (se 1 (by rfl) ⟨2366531, by rfl⟩ : syracuseStep 3155375 = 4733063) B4733063
theorem B2103583 : Blo 2103435 2103583 := bstep (se 1 (by rfl) ⟨1577687, by rfl⟩ : syracuseStep 2103583 = 3155375) B3155375
theorem B3155381 : Blo 2103435 3155381 := bbase (se 5 (by rfl) ⟨147908, by rfl⟩ : syracuseStep 3155381 = 295817) (by norm_num)
theorem B2103587 : Blo 2103435 2103587 := bstep (se 1 (by rfl) ⟨1577690, by rfl⟩ : syracuseStep 2103587 = 3155381) B3155381
theorem B5324717 : Blo 2103435 5324717 := bbase (se 3 (by rfl) ⟨998384, by rfl⟩ : syracuseStep 5324717 = 1996769) (by norm_num)
theorem B3549811 : Blo 2103435 3549811 := bstep (se 1 (by rfl) ⟨2662358, by rfl⟩ : syracuseStep 3549811 = 5324717) B5324717
theorem B4733081 : Blo 2103435 4733081 := bstep (se 2 (by rfl) ⟨1774905, by rfl⟩ : syracuseStep 4733081 = 3549811) B3549811
theorem B3155387 : Blo 2103435 3155387 := bstep (se 1 (by rfl) ⟨2366540, by rfl⟩ : syracuseStep 3155387 = 4733081) B4733081
theorem B2103591 : Blo 2103435 2103591 := bstep (se 1 (by rfl) ⟨1577693, by rfl⟩ : syracuseStep 2103591 = 3155387) B3155387
theorem B2366545 : Blo 2103435 2366545 := bbase (se 2 (by rfl) ⟨887454, by rfl⟩ : syracuseStep 2366545 = 1774909) (by norm_num)
theorem B3155393 : Blo 2103435 3155393 := bstep (se 2 (by rfl) ⟨1183272, by rfl⟩ : syracuseStep 3155393 = 2366545) B2366545
theorem B2103595 : Blo 2103435 2103595 := bstep (se 1 (by rfl) ⟨1577696, by rfl⟩ : syracuseStep 2103595 = 3155393) B3155393
theorem B2995165 : Blo 2103435 2995165 := bbase (se 3 (by rfl) ⟨561593, by rfl⟩ : syracuseStep 2995165 = 1123187) (by norm_num)
theorem B3993553 : Blo 2103435 3993553 := bstep (se 2 (by rfl) ⟨1497582, by rfl⟩ : syracuseStep 3993553 = 2995165) B2995165
theorem B5324737 : Blo 2103435 5324737 := bstep (se 2 (by rfl) ⟨1996776, by rfl⟩ : syracuseStep 5324737 = 3993553) B3993553
theorem B7099649 : Blo 2103435 7099649 := bstep (se 2 (by rfl) ⟨2662368, by rfl⟩ : syracuseStep 7099649 = 5324737) B5324737
theorem B4733099 : Blo 2103435 4733099 := bstep (se 1 (by rfl) ⟨3549824, by rfl⟩ : syracuseStep 4733099 = 7099649) B7099649
theorem B3155399 : Blo 2103435 3155399 := bstep (se 1 (by rfl) ⟨2366549, by rfl⟩ : syracuseStep 3155399 = 4733099) B4733099
theorem B2103599 : Blo 2103435 2103599 := bstep (se 1 (by rfl) ⟨1577699, by rfl⟩ : syracuseStep 2103599 = 3155399) B3155399
theorem B3155405 : Blo 2103435 3155405 := bbase (se 3 (by rfl) ⟨591638, by rfl⟩ : syracuseStep 3155405 = 1183277) (by norm_num)
theorem B2103603 : Blo 2103435 2103603 := bstep (se 1 (by rfl) ⟨1577702, by rfl⟩ : syracuseStep 2103603 = 3155405) B3155405
theorem B4733117 : Blo 2103435 4733117 := bbase (se 3 (by rfl) ⟨887459, by rfl⟩ : syracuseStep 4733117 = 1774919) (by norm_num)
theorem B3155411 : Blo 2103435 3155411 := bstep (se 1 (by rfl) ⟨2366558, by rfl⟩ : syracuseStep 3155411 = 4733117) B4733117
theorem B2103607 : Blo 2103435 2103607 := bstep (se 1 (by rfl) ⟨1577705, by rfl⟩ : syracuseStep 2103607 = 3155411) B3155411
theorem B3549845 : Blo 2103435 3549845 := bbase (se 6 (by rfl) ⟨83199, by rfl⟩ : syracuseStep 3549845 = 166399) (by norm_num)
theorem B2366563 : Blo 2103435 2366563 := bstep (se 1 (by rfl) ⟨1774922, by rfl⟩ : syracuseStep 2366563 = 3549845) B3549845
theorem B3155417 : Blo 2103435 3155417 := bstep (se 2 (by rfl) ⟨1183281, by rfl⟩ : syracuseStep 3155417 = 2366563) B2366563
theorem B2103611 : Blo 2103435 2103611 := bstep (se 1 (by rfl) ⟨1577708, by rfl⟩ : syracuseStep 2103611 = 3155417) B3155417
theorem B3598285 : Blo 2103435 3598285 := bbase (se 3 (by rfl) ⟨674678, by rfl⟩ : syracuseStep 3598285 = 1349357) (by norm_num)
theorem B4797713 : Blo 2103435 4797713 := bstep (se 2 (by rfl) ⟨1799142, by rfl⟩ : syracuseStep 4797713 = 3598285) B3598285
theorem B3198475 : Blo 2103435 3198475 := bstep (se 1 (by rfl) ⟨2398856, by rfl⟩ : syracuseStep 3198475 = 4797713) B4797713
theorem B4264633 : Blo 2103435 4264633 := bstep (se 2 (by rfl) ⟨1599237, by rfl⟩ : syracuseStep 4264633 = 3198475) B3198475
theorem B22744709 : Blo 2103435 22744709 := bstep (se 4 (by rfl) ⟨2132316, by rfl⟩ : syracuseStep 22744709 = 4264633) B4264633
theorem B15163139 : Blo 2103435 15163139 := bstep (se 1 (by rfl) ⟨11372354, by rfl⟩ : syracuseStep 15163139 = 22744709) B22744709
theorem B10108759 : Blo 2103435 10108759 := bstep (se 1 (by rfl) ⟨7581569, by rfl⟩ : syracuseStep 10108759 = 15163139) B15163139
theorem B13478345 : Blo 2103435 13478345 := bstep (se 2 (by rfl) ⟨5054379, by rfl⟩ : syracuseStep 13478345 = 10108759) B10108759
theorem B8985563 : Blo 2103435 8985563 := bstep (se 1 (by rfl) ⟨6739172, by rfl⟩ : syracuseStep 8985563 = 13478345) B13478345
theorem B5990375 : Blo 2103435 5990375 := bstep (se 1 (by rfl) ⟨4492781, by rfl⟩ : syracuseStep 5990375 = 8985563) B8985563
theorem B15974333 : Blo 2103435 15974333 := bstep (se 3 (by rfl) ⟨2995187, by rfl⟩ : syracuseStep 15974333 = 5990375) B5990375
theorem B10649555 : Blo 2103435 10649555 := bstep (se 1 (by rfl) ⟨7987166, by rfl⟩ : syracuseStep 10649555 = 15974333) B15974333
theorem B7099703 : Blo 2103435 7099703 := bstep (se 1 (by rfl) ⟨5324777, by rfl⟩ : syracuseStep 7099703 = 10649555) B10649555
theorem B4733135 : Blo 2103435 4733135 := bstep (se 1 (by rfl) ⟨3549851, by rfl⟩ : syracuseStep 4733135 = 7099703) B7099703
theorem B3155423 : Blo 2103435 3155423 := bstep (se 1 (by rfl) ⟨2366567, by rfl⟩ : syracuseStep 3155423 = 4733135) B4733135
theorem B2103615 : Blo 2103435 2103615 := bstep (se 1 (by rfl) ⟨1577711, by rfl⟩ : syracuseStep 2103615 = 3155423) B3155423
theorem B3155429 : Blo 2103435 3155429 := bbase (se 4 (by rfl) ⟨295821, by rfl⟩ : syracuseStep 3155429 = 591643) (by norm_num)
theorem B2103619 : Blo 2103435 2103619 := bstep (se 1 (by rfl) ⟨1577714, by rfl⟩ : syracuseStep 2103619 = 3155429) B3155429
theorem B207496021 : Blo 2103435 207496021 := bbase (se 9 (by rfl) ⟨607898, by rfl⟩ : syracuseStep 207496021 = 1215797) (by norm_num)
theorem B276661361 : Blo 2103435 276661361 := bstep (se 2 (by rfl) ⟨103748010, by rfl⟩ : syracuseStep 276661361 = 207496021) B207496021
theorem B184440907 : Blo 2103435 184440907 := bstep (se 1 (by rfl) ⟨138330680, by rfl⟩ : syracuseStep 184440907 = 276661361) B276661361
theorem B983684837 : Blo 2103435 983684837 := bstep (se 4 (by rfl) ⟨92220453, by rfl⟩ : syracuseStep 983684837 = 184440907) B184440907
theorem B655789891 : Blo 2103435 655789891 := bstep (se 1 (by rfl) ⟨491842418, by rfl⟩ : syracuseStep 655789891 = 983684837) B983684837
theorem B874386521 : Blo 2103435 874386521 := bstep (se 2 (by rfl) ⟨327894945, by rfl⟩ : syracuseStep 874386521 = 655789891) B655789891
theorem B582924347 : Blo 2103435 582924347 := bstep (se 1 (by rfl) ⟨437193260, by rfl⟩ : syracuseStep 582924347 = 874386521) B874386521
theorem B388616231 : Blo 2103435 388616231 := bstep (se 1 (by rfl) ⟨291462173, by rfl⟩ : syracuseStep 388616231 = 582924347) B582924347
theorem B259077487 : Blo 2103435 259077487 := bstep (se 1 (by rfl) ⟨194308115, by rfl⟩ : syracuseStep 259077487 = 388616231) B388616231
theorem B345436649 : Blo 2103435 345436649 := bstep (se 2 (by rfl) ⟨129538743, by rfl⟩ : syracuseStep 345436649 = 259077487) B259077487
theorem B230291099 : Blo 2103435 230291099 := bstep (se 1 (by rfl) ⟨172718324, by rfl⟩ : syracuseStep 230291099 = 345436649) B345436649
theorem B153527399 : Blo 2103435 153527399 := bstep (se 1 (by rfl) ⟨115145549, by rfl⟩ : syracuseStep 153527399 = 230291099) B230291099
theorem B102351599 : Blo 2103435 102351599 := bstep (se 1 (by rfl) ⟨76763699, by rfl⟩ : syracuseStep 102351599 = 153527399) B153527399
theorem B68234399 : Blo 2103435 68234399 := bstep (se 1 (by rfl) ⟨51175799, by rfl⟩ : syracuseStep 68234399 = 102351599) B102351599
theorem B45489599 : Blo 2103435 45489599 := bstep (se 1 (by rfl) ⟨34117199, by rfl⟩ : syracuseStep 45489599 = 68234399) B68234399
theorem B30326399 : Blo 2103435 30326399 := bstep (se 1 (by rfl) ⟨22744799, by rfl⟩ : syracuseStep 30326399 = 45489599) B45489599
theorem B20217599 : Blo 2103435 20217599 := bstep (se 1 (by rfl) ⟨15163199, by rfl⟩ : syracuseStep 20217599 = 30326399) B30326399
theorem B13478399 : Blo 2103435 13478399 := bstep (se 1 (by rfl) ⟨10108799, by rfl⟩ : syracuseStep 13478399 = 20217599) B20217599
theorem B8985599 : Blo 2103435 8985599 := bstep (se 1 (by rfl) ⟨6739199, by rfl⟩ : syracuseStep 8985599 = 13478399) B13478399
theorem B5990399 : Blo 2103435 5990399 := bstep (se 1 (by rfl) ⟨4492799, by rfl⟩ : syracuseStep 5990399 = 8985599) B8985599
theorem B3993599 : Blo 2103435 3993599 := bstep (se 1 (by rfl) ⟨2995199, by rfl⟩ : syracuseStep 3993599 = 5990399) B5990399
theorem B2662399 : Blo 2103435 2662399 := bstep (se 1 (by rfl) ⟨1996799, by rfl⟩ : syracuseStep 2662399 = 3993599) B3993599
theorem B3549865 : Blo 2103435 3549865 := bstep (se 2 (by rfl) ⟨1331199, by rfl⟩ : syracuseStep 3549865 = 2662399) B2662399
theorem B4733153 : Blo 2103435 4733153 := bstep (se 2 (by rfl) ⟨1774932, by rfl⟩ : syracuseStep 4733153 = 3549865) B3549865
theorem B3155435 : Blo 2103435 3155435 := bstep (se 1 (by rfl) ⟨2366576, by rfl⟩ : syracuseStep 3155435 = 4733153) B4733153
theorem B2103623 : Blo 2103435 2103623 := bstep (se 1 (by rfl) ⟨1577717, by rfl⟩ : syracuseStep 2103623 = 3155435) B3155435
theorem B2366581 : Blo 2103435 2366581 := bbase (se 5 (by rfl) ⟨110933, by rfl⟩ : syracuseStep 2366581 = 221867) (by norm_num)
theorem B3155441 : Blo 2103435 3155441 := bstep (se 2 (by rfl) ⟨1183290, by rfl⟩ : syracuseStep 3155441 = 2366581) B2366581
theorem B2103627 : Blo 2103435 2103627 := bstep (se 1 (by rfl) ⟨1577720, by rfl⟩ : syracuseStep 2103627 = 3155441) B3155441
theorem B2662409 : Blo 2103435 2662409 := bbase (se 2 (by rfl) ⟨998403, by rfl⟩ : syracuseStep 2662409 = 1996807) (by norm_num)
theorem B7099757 : Blo 2103435 7099757 := bstep (se 3 (by rfl) ⟨1331204, by rfl⟩ : syracuseStep 7099757 = 2662409) B2662409
theorem B4733171 : Blo 2103435 4733171 := bstep (se 1 (by rfl) ⟨3549878, by rfl⟩ : syracuseStep 4733171 = 7099757) B7099757
theorem B3155447 : Blo 2103435 3155447 := bstep (se 1 (by rfl) ⟨2366585, by rfl⟩ : syracuseStep 3155447 = 4733171) B4733171
theorem B2103631 : Blo 2103435 2103631 := bstep (se 1 (by rfl) ⟨1577723, by rfl⟩ : syracuseStep 2103631 = 3155447) B3155447
theorem B3155453 : Blo 2103435 3155453 := bbase (se 3 (by rfl) ⟨591647, by rfl⟩ : syracuseStep 3155453 = 1183295) (by norm_num)
theorem B2103635 : Blo 2103435 2103635 := bstep (se 1 (by rfl) ⟨1577726, by rfl⟩ : syracuseStep 2103635 = 3155453) B3155453
theorem B4733189 : Blo 2103435 4733189 := bbase (se 4 (by rfl) ⟨443736, by rfl⟩ : syracuseStep 4733189 = 887473) (by norm_num)
theorem B3155459 : Blo 2103435 3155459 := bstep (se 1 (by rfl) ⟨2366594, by rfl⟩ : syracuseStep 3155459 = 4733189) B4733189
theorem B2103639 : Blo 2103435 2103639 := bstep (se 1 (by rfl) ⟨1577729, by rfl⟩ : syracuseStep 2103639 = 3155459) B3155459
theorem B3993637 : Blo 2103435 3993637 := bbase (se 4 (by rfl) ⟨374403, by rfl⟩ : syracuseStep 3993637 = 748807) (by norm_num)
theorem B5324849 : Blo 2103435 5324849 := bstep (se 2 (by rfl) ⟨1996818, by rfl⟩ : syracuseStep 5324849 = 3993637) B3993637
theorem B3549899 : Blo 2103435 3549899 := bstep (se 1 (by rfl) ⟨2662424, by rfl⟩ : syracuseStep 3549899 = 5324849) B5324849
theorem B2366599 : Blo 2103435 2366599 := bstep (se 1 (by rfl) ⟨1774949, by rfl⟩ : syracuseStep 2366599 = 3549899) B3549899
theorem B3155465 : Blo 2103435 3155465 := bstep (se 2 (by rfl) ⟨1183299, by rfl⟩ : syracuseStep 3155465 = 2366599) B2366599
theorem B2103643 : Blo 2103435 2103643 := bstep (se 1 (by rfl) ⟨1577732, by rfl⟩ : syracuseStep 2103643 = 3155465) B3155465
theorem B10649717 : Blo 2103435 10649717 := bbase (se 5 (by rfl) ⟨499205, by rfl⟩ : syracuseStep 10649717 = 998411) (by norm_num)
theorem B7099811 : Blo 2103435 7099811 := bstep (se 1 (by rfl) ⟨5324858, by rfl⟩ : syracuseStep 7099811 = 10649717) B10649717
theorem B4733207 : Blo 2103435 4733207 := bstep (se 1 (by rfl) ⟨3549905, by rfl⟩ : syracuseStep 4733207 = 7099811) B7099811
theorem B3155471 : Blo 2103435 3155471 := bstep (se 1 (by rfl) ⟨2366603, by rfl⟩ : syracuseStep 3155471 = 4733207) B4733207
theorem B2103647 : Blo 2103435 2103647 := bstep (se 1 (by rfl) ⟨1577735, by rfl⟩ : syracuseStep 2103647 = 3155471) B3155471
theorem B3155477 : Blo 2103435 3155477 := bbase (se 6 (by rfl) ⟨73956, by rfl⟩ : syracuseStep 3155477 = 147913) (by norm_num)
theorem B2103651 : Blo 2103435 2103651 := bstep (se 1 (by rfl) ⟨1577738, by rfl⟩ : syracuseStep 2103651 = 3155477) B3155477
theorem B6739301 : Blo 2103435 6739301 := bbase (se 4 (by rfl) ⟨631809, by rfl⟩ : syracuseStep 6739301 = 1263619) (by norm_num)
theorem B17971469 : Blo 2103435 17971469 := bstep (se 3 (by rfl) ⟨3369650, by rfl⟩ : syracuseStep 17971469 = 6739301) B6739301
theorem B11980979 : Blo 2103435 11980979 := bstep (se 1 (by rfl) ⟨8985734, by rfl⟩ : syracuseStep 11980979 = 17971469) B17971469
theorem B7987319 : Blo 2103435 7987319 := bstep (se 1 (by rfl) ⟨5990489, by rfl⟩ : syracuseStep 7987319 = 11980979) B11980979
theorem B5324879 : Blo 2103435 5324879 := bstep (se 1 (by rfl) ⟨3993659, by rfl⟩ : syracuseStep 5324879 = 7987319) B7987319
theorem B3549919 : Blo 2103435 3549919 := bstep (se 1 (by rfl) ⟨2662439, by rfl⟩ : syracuseStep 3549919 = 5324879) B5324879
theorem B4733225 : Blo 2103435 4733225 := bstep (se 2 (by rfl) ⟨1774959, by rfl⟩ : syracuseStep 4733225 = 3549919) B3549919
theorem B3155483 : Blo 2103435 3155483 := bstep (se 1 (by rfl) ⟨2366612, by rfl⟩ : syracuseStep 3155483 = 4733225) B4733225
theorem B2103655 : Blo 2103435 2103655 := bstep (se 1 (by rfl) ⟨1577741, by rfl⟩ : syracuseStep 2103655 = 3155483) B3155483
theorem B2366617 : Blo 2103435 2366617 := bbase (se 2 (by rfl) ⟨887481, by rfl⟩ : syracuseStep 2366617 = 1774963) (by norm_num)
theorem B3155489 : Blo 2103435 3155489 := bstep (se 2 (by rfl) ⟨1183308, by rfl⟩ : syracuseStep 3155489 = 2366617) B2366617
theorem B2103659 : Blo 2103435 2103659 := bstep (se 1 (by rfl) ⟨1577744, by rfl⟩ : syracuseStep 2103659 = 3155489) B3155489
theorem B7987349 : Blo 2103435 7987349 := bbase (se 6 (by rfl) ⟨187203, by rfl⟩ : syracuseStep 7987349 = 374407) (by norm_num)
theorem B5324899 : Blo 2103435 5324899 := bstep (se 1 (by rfl) ⟨3993674, by rfl⟩ : syracuseStep 5324899 = 7987349) B7987349
theorem B7099865 : Blo 2103435 7099865 := bstep (se 2 (by rfl) ⟨2662449, by rfl⟩ : syracuseStep 7099865 = 5324899) B5324899
theorem B4733243 : Blo 2103435 4733243 := bstep (se 1 (by rfl) ⟨3549932, by rfl⟩ : syracuseStep 4733243 = 7099865) B7099865
theorem B3155495 : Blo 2103435 3155495 := bstep (se 1 (by rfl) ⟨2366621, by rfl⟩ : syracuseStep 3155495 = 4733243) B4733243
theorem B2103663 : Blo 2103435 2103663 := bstep (se 1 (by rfl) ⟨1577747, by rfl⟩ : syracuseStep 2103663 = 3155495) B3155495
theorem B3155501 : Blo 2103435 3155501 := bbase (se 3 (by rfl) ⟨591656, by rfl⟩ : syracuseStep 3155501 = 1183313) (by norm_num)
theorem B2103667 : Blo 2103435 2103667 := bstep (se 1 (by rfl) ⟨1577750, by rfl⟩ : syracuseStep 2103667 = 3155501) B3155501
theorem B4733261 : Blo 2103435 4733261 := bbase (se 3 (by rfl) ⟨887486, by rfl⟩ : syracuseStep 4733261 = 1774973) (by norm_num)
theorem B3155507 : Blo 2103435 3155507 := bstep (se 1 (by rfl) ⟨2366630, by rfl⟩ : syracuseStep 3155507 = 4733261) B4733261
theorem B2103671 : Blo 2103435 2103671 := bstep (se 1 (by rfl) ⟨1577753, by rfl⟩ : syracuseStep 2103671 = 3155507) B3155507
theorem B2662465 : Blo 2103435 2662465 := bbase (se 2 (by rfl) ⟨998424, by rfl⟩ : syracuseStep 2662465 = 1996849) (by norm_num)
theorem B3549953 : Blo 2103435 3549953 := bstep (se 2 (by rfl) ⟨1331232, by rfl⟩ : syracuseStep 3549953 = 2662465) B2662465
theorem B2366635 : Blo 2103435 2366635 := bstep (se 1 (by rfl) ⟨1774976, by rfl⟩ : syracuseStep 2366635 = 3549953) B3549953
theorem B3155513 : Blo 2103435 3155513 := bstep (se 2 (by rfl) ⟨1183317, by rfl⟩ : syracuseStep 3155513 = 2366635) B2366635
theorem B2103675 : Blo 2103435 2103675 := bstep (se 1 (by rfl) ⟨1577756, by rfl⟩ : syracuseStep 2103675 = 3155513) B3155513
theorem B3790901 : Blo 2103435 3790901 := bbase (se 5 (by rfl) ⟨177698, by rfl⟩ : syracuseStep 3790901 = 355397) (by norm_num)
theorem B2527267 : Blo 2103435 2527267 := bstep (se 1 (by rfl) ⟨1895450, by rfl⟩ : syracuseStep 2527267 = 3790901) B3790901
theorem B3369689 : Blo 2103435 3369689 := bstep (se 2 (by rfl) ⟨1263633, by rfl⟩ : syracuseStep 3369689 = 2527267) B2527267
theorem B2246459 : Blo 2103435 2246459 := bstep (se 1 (by rfl) ⟨1684844, by rfl⟩ : syracuseStep 2246459 = 3369689) B3369689
theorem B23962229 : Blo 2103435 23962229 := bstep (se 5 (by rfl) ⟨1123229, by rfl⟩ : syracuseStep 23962229 = 2246459) B2246459
theorem B15974819 : Blo 2103435 15974819 := bstep (se 1 (by rfl) ⟨11981114, by rfl⟩ : syracuseStep 15974819 = 23962229) B23962229
theorem B10649879 : Blo 2103435 10649879 := bstep (se 1 (by rfl) ⟨7987409, by rfl⟩ : syracuseStep 10649879 = 15974819) B15974819
theorem B7099919 : Blo 2103435 7099919 := bstep (se 1 (by rfl) ⟨5324939, by rfl⟩ : syracuseStep 7099919 = 10649879) B10649879
theorem B4733279 : Blo 2103435 4733279 := bstep (se 1 (by rfl) ⟨3549959, by rfl⟩ : syracuseStep 4733279 = 7099919) B7099919
theorem B3155519 : Blo 2103435 3155519 := bstep (se 1 (by rfl) ⟨2366639, by rfl⟩ : syracuseStep 3155519 = 4733279) B4733279
theorem B2103679 : Blo 2103435 2103679 := bstep (se 1 (by rfl) ⟨1577759, by rfl⟩ : syracuseStep 2103679 = 3155519) B3155519
theorem B3155525 : Blo 2103435 3155525 := bbase (se 4 (by rfl) ⟨295830, by rfl⟩ : syracuseStep 3155525 = 591661) (by norm_num)
theorem B2103683 : Blo 2103435 2103683 := bstep (se 1 (by rfl) ⟨1577762, by rfl⟩ : syracuseStep 2103683 = 3155525) B3155525
theorem B3549973 : Blo 2103435 3549973 := bbase (se 6 (by rfl) ⟨83202, by rfl⟩ : syracuseStep 3549973 = 166405) (by norm_num)
theorem B4733297 : Blo 2103435 4733297 := bstep (se 2 (by rfl) ⟨1774986, by rfl⟩ : syracuseStep 4733297 = 3549973) B3549973
theorem B3155531 : Blo 2103435 3155531 := bstep (se 1 (by rfl) ⟨2366648, by rfl⟩ : syracuseStep 3155531 = 4733297) B4733297
theorem B2103687 : Blo 2103435 2103687 := bstep (se 1 (by rfl) ⟨1577765, by rfl⟩ : syracuseStep 2103687 = 3155531) B3155531
theorem B2366653 : Blo 2103435 2366653 := bbase (se 3 (by rfl) ⟨443747, by rfl⟩ : syracuseStep 2366653 = 887495) (by norm_num)
theorem B3155537 : Blo 2103435 3155537 := bstep (se 2 (by rfl) ⟨1183326, by rfl⟩ : syracuseStep 3155537 = 2366653) B2366653
theorem B2103691 : Blo 2103435 2103691 := bstep (se 1 (by rfl) ⟨1577768, by rfl⟩ : syracuseStep 2103691 = 3155537) B3155537
theorem B7099973 : Blo 2103435 7099973 := bbase (se 4 (by rfl) ⟨665622, by rfl⟩ : syracuseStep 7099973 = 1331245) (by norm_num)
theorem B4733315 : Blo 2103435 4733315 := bstep (se 1 (by rfl) ⟨3549986, by rfl⟩ : syracuseStep 4733315 = 7099973) B7099973
theorem B3155543 : Blo 2103435 3155543 := bstep (se 1 (by rfl) ⟨2366657, by rfl⟩ : syracuseStep 3155543 = 4733315) B4733315
theorem B2103695 : Blo 2103435 2103695 := bstep (se 1 (by rfl) ⟨1577771, by rfl⟩ : syracuseStep 2103695 = 3155543) B3155543
theorem B3155549 : Blo 2103435 3155549 := bbase (se 3 (by rfl) ⟨591665, by rfl⟩ : syracuseStep 3155549 = 1183331) (by norm_num)
theorem B2103699 : Blo 2103435 2103699 := bstep (se 1 (by rfl) ⟨1577774, by rfl⟩ : syracuseStep 2103699 = 3155549) B3155549
theorem B4733333 : Blo 2103435 4733333 := bbase (se 6 (by rfl) ⟨110937, by rfl⟩ : syracuseStep 4733333 = 221875) (by norm_num)
theorem B3155555 : Blo 2103435 3155555 := bstep (se 1 (by rfl) ⟨2366666, by rfl⟩ : syracuseStep 3155555 = 4733333) B4733333
theorem B2103703 : Blo 2103435 2103703 := bstep (se 1 (by rfl) ⟨1577777, by rfl⟩ : syracuseStep 2103703 = 3155555) B3155555
theorem B2527301 : Blo 2103435 2527301 := bbase (se 4 (by rfl) ⟨236934, by rfl⟩ : syracuseStep 2527301 = 473869) (by norm_num)
theorem B6739469 : Blo 2103435 6739469 := bstep (se 3 (by rfl) ⟨1263650, by rfl⟩ : syracuseStep 6739469 = 2527301) B2527301
theorem B4492979 : Blo 2103435 4492979 := bstep (se 1 (by rfl) ⟨3369734, by rfl⟩ : syracuseStep 4492979 = 6739469) B6739469
theorem B2995319 : Blo 2103435 2995319 := bstep (se 1 (by rfl) ⟨2246489, by rfl⟩ : syracuseStep 2995319 = 4492979) B4492979
theorem B7987517 : Blo 2103435 7987517 := bstep (se 3 (by rfl) ⟨1497659, by rfl⟩ : syracuseStep 7987517 = 2995319) B2995319
theorem B5325011 : Blo 2103435 5325011 := bstep (se 1 (by rfl) ⟨3993758, by rfl⟩ : syracuseStep 5325011 = 7987517) B7987517
theorem B3550007 : Blo 2103435 3550007 := bstep (se 1 (by rfl) ⟨2662505, by rfl⟩ : syracuseStep 3550007 = 5325011) B5325011
theorem B2366671 : Blo 2103435 2366671 := bstep (se 1 (by rfl) ⟨1775003, by rfl⟩ : syracuseStep 2366671 = 3550007) B3550007
theorem B3155561 : Blo 2103435 3155561 := bstep (se 2 (by rfl) ⟨1183335, by rfl⟩ : syracuseStep 3155561 = 2366671) B2366671
theorem B2103707 : Blo 2103435 2103707 := bstep (se 1 (by rfl) ⟨1577780, by rfl⟩ : syracuseStep 2103707 = 3155561) B3155561
theorem B8985973 : Blo 2103435 8985973 := bbase (se 5 (by rfl) ⟨421217, by rfl⟩ : syracuseStep 8985973 = 842435) (by norm_num)
theorem B11981297 : Blo 2103435 11981297 := bstep (se 2 (by rfl) ⟨4492986, by rfl⟩ : syracuseStep 11981297 = 8985973) B8985973
theorem B7987531 : Blo 2103435 7987531 := bstep (se 1 (by rfl) ⟨5990648, by rfl⟩ : syracuseStep 7987531 = 11981297) B11981297
theorem B10650041 : Blo 2103435 10650041 := bstep (se 2 (by rfl) ⟨3993765, by rfl⟩ : syracuseStep 10650041 = 7987531) B7987531
theorem B7100027 : Blo 2103435 7100027 := bstep (se 1 (by rfl) ⟨5325020, by rfl⟩ : syracuseStep 7100027 = 10650041) B10650041
theorem B4733351 : Blo 2103435 4733351 := bstep (se 1 (by rfl) ⟨3550013, by rfl⟩ : syracuseStep 4733351 = 7100027) B7100027
theorem B3155567 : Blo 2103435 3155567 := bstep (se 1 (by rfl) ⟨2366675, by rfl⟩ : syracuseStep 3155567 = 4733351) B4733351
theorem B2103711 : Blo 2103435 2103711 := bstep (se 1 (by rfl) ⟨1577783, by rfl⟩ : syracuseStep 2103711 = 3155567) B3155567
theorem B3155573 : Blo 2103435 3155573 := bbase (se 5 (by rfl) ⟨147917, by rfl⟩ : syracuseStep 3155573 = 295835) (by norm_num)
theorem B2103715 : Blo 2103435 2103715 := bstep (se 1 (by rfl) ⟨1577786, by rfl⟩ : syracuseStep 2103715 = 3155573) B3155573
theorem B3993781 : Blo 2103435 3993781 := bbase (se 5 (by rfl) ⟨187208, by rfl⟩ : syracuseStep 3993781 = 374417) (by norm_num)
theorem B5325041 : Blo 2103435 5325041 := bstep (se 2 (by rfl) ⟨1996890, by rfl⟩ : syracuseStep 5325041 = 3993781) B3993781
theorem B3550027 : Blo 2103435 3550027 := bstep (se 1 (by rfl) ⟨2662520, by rfl⟩ : syracuseStep 3550027 = 5325041) B5325041
theorem B4733369 : Blo 2103435 4733369 := bstep (se 2 (by rfl) ⟨1775013, by rfl⟩ : syracuseStep 4733369 = 3550027) B3550027
theorem B3155579 : Blo 2103435 3155579 := bstep (se 1 (by rfl) ⟨2366684, by rfl⟩ : syracuseStep 3155579 = 4733369) B4733369
theorem B2103719 : Blo 2103435 2103719 := bstep (se 1 (by rfl) ⟨1577789, by rfl⟩ : syracuseStep 2103719 = 3155579) B3155579
theorem B2366689 : Blo 2103435 2366689 := bbase (se 2 (by rfl) ⟨887508, by rfl⟩ : syracuseStep 2366689 = 1775017) (by norm_num)
theorem B3155585 : Blo 2103435 3155585 := bstep (se 2 (by rfl) ⟨1183344, by rfl⟩ : syracuseStep 3155585 = 2366689) B2366689
theorem B2103723 : Blo 2103435 2103723 := bstep (se 1 (by rfl) ⟨1577792, by rfl⟩ : syracuseStep 2103723 = 3155585) B3155585
theorem B5325061 : Blo 2103435 5325061 := bbase (se 4 (by rfl) ⟨499224, by rfl⟩ : syracuseStep 5325061 = 998449) (by norm_num)
theorem B7100081 : Blo 2103435 7100081 := bstep (se 2 (by rfl) ⟨2662530, by rfl⟩ : syracuseStep 7100081 = 5325061) B5325061
theorem B4733387 : Blo 2103435 4733387 := bstep (se 1 (by rfl) ⟨3550040, by rfl⟩ : syracuseStep 4733387 = 7100081) B7100081
theorem B3155591 : Blo 2103435 3155591 := bstep (se 1 (by rfl) ⟨2366693, by rfl⟩ : syracuseStep 3155591 = 4733387) B4733387
theorem B2103727 : Blo 2103435 2103727 := bstep (se 1 (by rfl) ⟨1577795, by rfl⟩ : syracuseStep 2103727 = 3155591) B3155591
theorem B3155597 : Blo 2103435 3155597 := bbase (se 3 (by rfl) ⟨591674, by rfl⟩ : syracuseStep 3155597 = 1183349) (by norm_num)
theorem B2103731 : Blo 2103435 2103731 := bstep (se 1 (by rfl) ⟨1577798, by rfl⟩ : syracuseStep 2103731 = 3155597) B3155597
theorem B4733405 : Blo 2103435 4733405 := bbase (se 3 (by rfl) ⟨887513, by rfl⟩ : syracuseStep 4733405 = 1775027) (by norm_num)
theorem B3155603 : Blo 2103435 3155603 := bstep (se 1 (by rfl) ⟨2366702, by rfl⟩ : syracuseStep 3155603 = 4733405) B4733405
theorem B2103735 : Blo 2103435 2103735 := bstep (se 1 (by rfl) ⟨1577801, by rfl⟩ : syracuseStep 2103735 = 3155603) B3155603
theorem B3550061 : Blo 2103435 3550061 := bbase (se 3 (by rfl) ⟨665636, by rfl⟩ : syracuseStep 3550061 = 1331273) (by norm_num)
theorem B2366707 : Blo 2103435 2366707 := bstep (se 1 (by rfl) ⟨1775030, by rfl⟩ : syracuseStep 2366707 = 3550061) B3550061
theorem B3155609 : Blo 2103435 3155609 := bstep (se 2 (by rfl) ⟨1183353, by rfl⟩ : syracuseStep 3155609 = 2366707) B2366707
theorem B2103739 : Blo 2103435 2103739 := bstep (se 1 (by rfl) ⟨1577804, by rfl⟩ : syracuseStep 2103739 = 3155609) B3155609
theorem B4103549 : Blo 2103435 4103549 := bbase (se 3 (by rfl) ⟨769415, by rfl⟩ : syracuseStep 4103549 = 1538831) (by norm_num)
theorem B2735699 : Blo 2103435 2735699 := bstep (se 1 (by rfl) ⟨2051774, by rfl⟩ : syracuseStep 2735699 = 4103549) B4103549
theorem B29180789 : Blo 2103435 29180789 := bstep (se 5 (by rfl) ⟨1367849, by rfl⟩ : syracuseStep 29180789 = 2735699) B2735699
theorem B19453859 : Blo 2103435 19453859 := bstep (se 1 (by rfl) ⟨14590394, by rfl⟩ : syracuseStep 19453859 = 29180789) B29180789
theorem B12969239 : Blo 2103435 12969239 := bstep (se 1 (by rfl) ⟨9726929, by rfl⟩ : syracuseStep 12969239 = 19453859) B19453859
theorem B138338549 : Blo 2103435 138338549 := bstep (se 5 (by rfl) ⟨6484619, by rfl⟩ : syracuseStep 138338549 = 12969239) B12969239
theorem B92225699 : Blo 2103435 92225699 := bstep (se 1 (by rfl) ⟨69169274, by rfl⟩ : syracuseStep 92225699 = 138338549) B138338549
theorem B61483799 : Blo 2103435 61483799 := bstep (se 1 (by rfl) ⟨46112849, by rfl⟩ : syracuseStep 61483799 = 92225699) B92225699
theorem B40989199 : Blo 2103435 40989199 := bstep (se 1 (by rfl) ⟨30741899, by rfl⟩ : syracuseStep 40989199 = 61483799) B61483799
theorem B54652265 : Blo 2103435 54652265 := bstep (se 2 (by rfl) ⟨20494599, by rfl⟩ : syracuseStep 54652265 = 40989199) B40989199
theorem B36434843 : Blo 2103435 36434843 := bstep (se 1 (by rfl) ⟨27326132, by rfl⟩ : syracuseStep 36434843 = 54652265) B54652265
theorem B24289895 : Blo 2103435 24289895 := bstep (se 1 (by rfl) ⟨18217421, by rfl⟩ : syracuseStep 24289895 = 36434843) B36434843
theorem B64773053 : Blo 2103435 64773053 := bstep (se 3 (by rfl) ⟨12144947, by rfl⟩ : syracuseStep 64773053 = 24289895) B24289895
theorem B43182035 : Blo 2103435 43182035 := bstep (se 1 (by rfl) ⟨32386526, by rfl⟩ : syracuseStep 43182035 = 64773053) B64773053
theorem B28788023 : Blo 2103435 28788023 := bstep (se 1 (by rfl) ⟨21591017, by rfl⟩ : syracuseStep 28788023 = 43182035) B43182035
theorem B19192015 : Blo 2103435 19192015 := bstep (se 1 (by rfl) ⟨14394011, by rfl⟩ : syracuseStep 19192015 = 28788023) B28788023
theorem B25589353 : Blo 2103435 25589353 := bstep (se 2 (by rfl) ⟨9596007, by rfl⟩ : syracuseStep 25589353 = 19192015) B19192015
theorem B34119137 : Blo 2103435 34119137 := bstep (se 2 (by rfl) ⟨12794676, by rfl⟩ : syracuseStep 34119137 = 25589353) B25589353
theorem B22746091 : Blo 2103435 22746091 := bstep (se 1 (by rfl) ⟨17059568, by rfl⟩ : syracuseStep 22746091 = 34119137) B34119137
theorem B30328121 : Blo 2103435 30328121 := bstep (se 2 (by rfl) ⟨11373045, by rfl⟩ : syracuseStep 30328121 = 22746091) B22746091
theorem B20218747 : Blo 2103435 20218747 := bstep (se 1 (by rfl) ⟨15164060, by rfl⟩ : syracuseStep 20218747 = 30328121) B30328121
theorem B26958329 : Blo 2103435 26958329 := bstep (se 2 (by rfl) ⟨10109373, by rfl⟩ : syracuseStep 26958329 = 20218747) B20218747
theorem B17972219 : Blo 2103435 17972219 := bstep (se 1 (by rfl) ⟨13479164, by rfl⟩ : syracuseStep 17972219 = 26958329) B26958329
theorem B11981479 : Blo 2103435 11981479 := bstep (se 1 (by rfl) ⟨8986109, by rfl⟩ : syracuseStep 11981479 = 17972219) B17972219
theorem B15975305 : Blo 2103435 15975305 := bstep (se 2 (by rfl) ⟨5990739, by rfl⟩ : syracuseStep 15975305 = 11981479) B11981479
theorem B10650203 : Blo 2103435 10650203 := bstep (se 1 (by rfl) ⟨7987652, by rfl⟩ : syracuseStep 10650203 = 15975305) B15975305
theorem B7100135 : Blo 2103435 7100135 := bstep (se 1 (by rfl) ⟨5325101, by rfl⟩ : syracuseStep 7100135 = 10650203) B10650203
theorem B4733423 : Blo 2103435 4733423 := bstep (se 1 (by rfl) ⟨3550067, by rfl⟩ : syracuseStep 4733423 = 7100135) B7100135
theorem B3155615 : Blo 2103435 3155615 := bstep (se 1 (by rfl) ⟨2366711, by rfl⟩ : syracuseStep 3155615 = 4733423) B4733423
theorem B2103743 : Blo 2103435 2103743 := bstep (se 1 (by rfl) ⟨1577807, by rfl⟩ : syracuseStep 2103743 = 3155615) B3155615
theorem B3155621 : Blo 2103435 3155621 := bbase (se 4 (by rfl) ⟨295839, by rfl⟩ : syracuseStep 3155621 = 591679) (by norm_num)
theorem B2103747 : Blo 2103435 2103747 := bstep (se 1 (by rfl) ⟨1577810, by rfl⟩ : syracuseStep 2103747 = 3155621) B3155621
theorem B2662561 : Blo 2103435 2662561 := bbase (se 2 (by rfl) ⟨998460, by rfl⟩ : syracuseStep 2662561 = 1996921) (by norm_num)
theorem B3550081 : Blo 2103435 3550081 := bstep (se 2 (by rfl) ⟨1331280, by rfl⟩ : syracuseStep 3550081 = 2662561) B2662561
theorem B4733441 : Blo 2103435 4733441 := bstep (se 2 (by rfl) ⟨1775040, by rfl⟩ : syracuseStep 4733441 = 3550081) B3550081
theorem B3155627 : Blo 2103435 3155627 := bstep (se 1 (by rfl) ⟨2366720, by rfl⟩ : syracuseStep 3155627 = 4733441) B4733441
theorem B2103751 : Blo 2103435 2103751 := bstep (se 1 (by rfl) ⟨1577813, by rfl⟩ : syracuseStep 2103751 = 3155627) B3155627
theorem B2366725 : Blo 2103435 2366725 := bbase (se 4 (by rfl) ⟨221880, by rfl⟩ : syracuseStep 2366725 = 443761) (by norm_num)
theorem B3155633 : Blo 2103435 3155633 := bstep (se 2 (by rfl) ⟨1183362, by rfl⟩ : syracuseStep 3155633 = 2366725) B2366725
theorem B2103755 : Blo 2103435 2103755 := bstep (se 1 (by rfl) ⟨1577816, by rfl⟩ : syracuseStep 2103755 = 3155633) B3155633
theorem B2246545 : Blo 2103435 2246545 := bbase (se 2 (by rfl) ⟨842454, by rfl⟩ : syracuseStep 2246545 = 1684909) (by norm_num)
theorem B2995393 : Blo 2103435 2995393 := bstep (se 2 (by rfl) ⟨1123272, by rfl⟩ : syracuseStep 2995393 = 2246545) B2246545
theorem B3993857 : Blo 2103435 3993857 := bstep (se 2 (by rfl) ⟨1497696, by rfl⟩ : syracuseStep 3993857 = 2995393) B2995393
theorem B2662571 : Blo 2103435 2662571 := bstep (se 1 (by rfl) ⟨1996928, by rfl⟩ : syracuseStep 2662571 = 3993857) B3993857
theorem B7100189 : Blo 2103435 7100189 := bstep (se 3 (by rfl) ⟨1331285, by rfl⟩ : syracuseStep 7100189 = 2662571) B2662571
theorem B4733459 : Blo 2103435 4733459 := bstep (se 1 (by rfl) ⟨3550094, by rfl⟩ : syracuseStep 4733459 = 7100189) B7100189
theorem B3155639 : Blo 2103435 3155639 := bstep (se 1 (by rfl) ⟨2366729, by rfl⟩ : syracuseStep 3155639 = 4733459) B4733459
theorem B2103759 : Blo 2103435 2103759 := bstep (se 1 (by rfl) ⟨1577819, by rfl⟩ : syracuseStep 2103759 = 3155639) B3155639
theorem B3155645 : Blo 2103435 3155645 := bbase (se 3 (by rfl) ⟨591683, by rfl⟩ : syracuseStep 3155645 = 1183367) (by norm_num)
theorem B2103763 : Blo 2103435 2103763 := bstep (se 1 (by rfl) ⟨1577822, by rfl⟩ : syracuseStep 2103763 = 3155645) B3155645
theorem B4733477 : Blo 2103435 4733477 := bbase (se 4 (by rfl) ⟨443763, by rfl⟩ : syracuseStep 4733477 = 887527) (by norm_num)
theorem B3155651 : Blo 2103435 3155651 := bstep (se 1 (by rfl) ⟨2366738, by rfl⟩ : syracuseStep 3155651 = 4733477) B4733477
theorem B2103767 : Blo 2103435 2103767 := bstep (se 1 (by rfl) ⟨1577825, by rfl⟩ : syracuseStep 2103767 = 3155651) B3155651
theorem B5325173 : Blo 2103435 5325173 := bbase (se 5 (by rfl) ⟨249617, by rfl⟩ : syracuseStep 5325173 = 499235) (by norm_num)
theorem B3550115 : Blo 2103435 3550115 := bstep (se 1 (by rfl) ⟨2662586, by rfl⟩ : syracuseStep 3550115 = 5325173) B5325173
theorem B2366743 : Blo 2103435 2366743 := bstep (se 1 (by rfl) ⟨1775057, by rfl⟩ : syracuseStep 2366743 = 3550115) B3550115
theorem B3155657 : Blo 2103435 3155657 := bstep (se 2 (by rfl) ⟨1183371, by rfl⟩ : syracuseStep 3155657 = 2366743) B2366743
theorem B2103771 : Blo 2103435 2103771 := bstep (se 1 (by rfl) ⟨1577828, by rfl⟩ : syracuseStep 2103771 = 3155657) B3155657
theorem B92227157 : Blo 2103435 92227157 := bbase (se 8 (by rfl) ⟨540393, by rfl⟩ : syracuseStep 92227157 = 1080787) (by norm_num)
theorem B61484771 : Blo 2103435 61484771 := bstep (se 1 (by rfl) ⟨46113578, by rfl⟩ : syracuseStep 61484771 = 92227157) B92227157
theorem B40989847 : Blo 2103435 40989847 := bstep (se 1 (by rfl) ⟨30742385, by rfl⟩ : syracuseStep 40989847 = 61484771) B61484771
theorem B54653129 : Blo 2103435 54653129 := bstep (se 2 (by rfl) ⟨20494923, by rfl⟩ : syracuseStep 54653129 = 40989847) B40989847
theorem B36435419 : Blo 2103435 36435419 := bstep (se 1 (by rfl) ⟨27326564, by rfl⟩ : syracuseStep 36435419 = 54653129) B54653129
theorem B24290279 : Blo 2103435 24290279 := bstep (se 1 (by rfl) ⟨18217709, by rfl⟩ : syracuseStep 24290279 = 36435419) B36435419
theorem B16193519 : Blo 2103435 16193519 := bstep (se 1 (by rfl) ⟨12145139, by rfl⟩ : syracuseStep 16193519 = 24290279) B24290279
theorem B10795679 : Blo 2103435 10795679 := bstep (se 1 (by rfl) ⟨8096759, by rfl⟩ : syracuseStep 10795679 = 16193519) B16193519
theorem B7197119 : Blo 2103435 7197119 := bstep (se 1 (by rfl) ⟨5397839, by rfl⟩ : syracuseStep 7197119 = 10795679) B10795679
theorem B4798079 : Blo 2103435 4798079 := bstep (se 1 (by rfl) ⟨3598559, by rfl⟩ : syracuseStep 4798079 = 7197119) B7197119
theorem B3198719 : Blo 2103435 3198719 := bstep (se 1 (by rfl) ⟨2399039, by rfl⟩ : syracuseStep 3198719 = 4798079) B4798079
theorem B2132479 : Blo 2103435 2132479 := bstep (se 1 (by rfl) ⟨1599359, by rfl⟩ : syracuseStep 2132479 = 3198719) B3198719
theorem B2843305 : Blo 2103435 2843305 := bstep (se 2 (by rfl) ⟨1066239, by rfl⟩ : syracuseStep 2843305 = 2132479) B2132479
theorem B15164293 : Blo 2103435 15164293 := bstep (se 4 (by rfl) ⟨1421652, by rfl⟩ : syracuseStep 15164293 = 2843305) B2843305
theorem B20219057 : Blo 2103435 20219057 := bstep (se 2 (by rfl) ⟨7582146, by rfl⟩ : syracuseStep 20219057 = 15164293) B15164293
theorem B13479371 : Blo 2103435 13479371 := bstep (se 1 (by rfl) ⟨10109528, by rfl⟩ : syracuseStep 13479371 = 20219057) B20219057
theorem B8986247 : Blo 2103435 8986247 := bstep (se 1 (by rfl) ⟨6739685, by rfl⟩ : syracuseStep 8986247 = 13479371) B13479371
theorem B5990831 : Blo 2103435 5990831 := bstep (se 1 (by rfl) ⟨4493123, by rfl⟩ : syracuseStep 5990831 = 8986247) B8986247
theorem B3993887 : Blo 2103435 3993887 := bstep (se 1 (by rfl) ⟨2995415, by rfl⟩ : syracuseStep 3993887 = 5990831) B5990831
theorem B10650365 : Blo 2103435 10650365 := bstep (se 3 (by rfl) ⟨1996943, by rfl⟩ : syracuseStep 10650365 = 3993887) B3993887
theorem B7100243 : Blo 2103435 7100243 := bstep (se 1 (by rfl) ⟨5325182, by rfl⟩ : syracuseStep 7100243 = 10650365) B10650365
theorem B4733495 : Blo 2103435 4733495 := bstep (se 1 (by rfl) ⟨3550121, by rfl⟩ : syracuseStep 4733495 = 7100243) B7100243
theorem B3155663 : Blo 2103435 3155663 := bstep (se 1 (by rfl) ⟨2366747, by rfl⟩ : syracuseStep 3155663 = 4733495) B4733495
theorem B2103775 : Blo 2103435 2103775 := bstep (se 1 (by rfl) ⟨1577831, by rfl⟩ : syracuseStep 2103775 = 3155663) B3155663
theorem B3155669 : Blo 2103435 3155669 := bbase (se 7 (by rfl) ⟨36980, by rfl⟩ : syracuseStep 3155669 = 73961) (by norm_num)
theorem B2103779 : Blo 2103435 2103779 := bstep (se 1 (by rfl) ⟨1577834, by rfl⟩ : syracuseStep 2103779 = 3155669) B3155669
theorem B4493141 : Blo 2103435 4493141 := bbase (se 9 (by rfl) ⟨13163, by rfl⟩ : syracuseStep 4493141 = 26327) (by norm_num)
theorem B2995427 : Blo 2103435 2995427 := bstep (se 1 (by rfl) ⟨2246570, by rfl⟩ : syracuseStep 2995427 = 4493141) B4493141
theorem B7987805 : Blo 2103435 7987805 := bstep (se 3 (by rfl) ⟨1497713, by rfl⟩ : syracuseStep 7987805 = 2995427) B2995427
theorem B5325203 : Blo 2103435 5325203 := bstep (se 1 (by rfl) ⟨3993902, by rfl⟩ : syracuseStep 5325203 = 7987805) B7987805
theorem B3550135 : Blo 2103435 3550135 := bstep (se 1 (by rfl) ⟨2662601, by rfl⟩ : syracuseStep 3550135 = 5325203) B5325203
theorem B4733513 : Blo 2103435 4733513 := bstep (se 2 (by rfl) ⟨1775067, by rfl⟩ : syracuseStep 4733513 = 3550135) B3550135
theorem B3155675 : Blo 2103435 3155675 := bstep (se 1 (by rfl) ⟨2366756, by rfl⟩ : syracuseStep 3155675 = 4733513) B4733513
theorem B2103783 : Blo 2103435 2103783 := bstep (se 1 (by rfl) ⟨1577837, by rfl⟩ : syracuseStep 2103783 = 3155675) B3155675
theorem B2366761 : Blo 2103435 2366761 := bbase (se 2 (by rfl) ⟨887535, by rfl⟩ : syracuseStep 2366761 = 1775071) (by norm_num)
theorem B3155681 : Blo 2103435 3155681 := bstep (se 2 (by rfl) ⟨1183380, by rfl⟩ : syracuseStep 3155681 = 2366761) B2366761
theorem B2103787 : Blo 2103435 2103787 := bstep (se 1 (by rfl) ⟨1577840, by rfl⟩ : syracuseStep 2103787 = 3155681) B3155681
theorem B10109605 : Blo 2103435 10109605 := bbase (se 4 (by rfl) ⟨947775, by rfl⟩ : syracuseStep 10109605 = 1895551) (by norm_num)
theorem B13479473 : Blo 2103435 13479473 := bstep (se 2 (by rfl) ⟨5054802, by rfl⟩ : syracuseStep 13479473 = 10109605) B10109605
theorem B8986315 : Blo 2103435 8986315 := bstep (se 1 (by rfl) ⟨6739736, by rfl⟩ : syracuseStep 8986315 = 13479473) B13479473
theorem B11981753 : Blo 2103435 11981753 := bstep (se 2 (by rfl) ⟨4493157, by rfl⟩ : syracuseStep 11981753 = 8986315) B8986315
theorem B7987835 : Blo 2103435 7987835 := bstep (se 1 (by rfl) ⟨5990876, by rfl⟩ : syracuseStep 7987835 = 11981753) B11981753
theorem B5325223 : Blo 2103435 5325223 := bstep (se 1 (by rfl) ⟨3993917, by rfl⟩ : syracuseStep 5325223 = 7987835) B7987835
theorem B7100297 : Blo 2103435 7100297 := bstep (se 2 (by rfl) ⟨2662611, by rfl⟩ : syracuseStep 7100297 = 5325223) B5325223
theorem B4733531 : Blo 2103435 4733531 := bstep (se 1 (by rfl) ⟨3550148, by rfl⟩ : syracuseStep 4733531 = 7100297) B7100297
theorem B3155687 : Blo 2103435 3155687 := bstep (se 1 (by rfl) ⟨2366765, by rfl⟩ : syracuseStep 3155687 = 4733531) B4733531
theorem B2103791 : Blo 2103435 2103791 := bstep (se 1 (by rfl) ⟨1577843, by rfl⟩ : syracuseStep 2103791 = 3155687) B3155687
theorem B3155693 : Blo 2103435 3155693 := bbase (se 3 (by rfl) ⟨591692, by rfl⟩ : syracuseStep 3155693 = 1183385) (by norm_num)
theorem B2103795 : Blo 2103435 2103795 := bstep (se 1 (by rfl) ⟨1577846, by rfl⟩ : syracuseStep 2103795 = 3155693) B3155693
theorem B4733549 : Blo 2103435 4733549 := bbase (se 3 (by rfl) ⟨887540, by rfl⟩ : syracuseStep 4733549 = 1775081) (by norm_num)
theorem B3155699 : Blo 2103435 3155699 := bstep (se 1 (by rfl) ⟨2366774, by rfl⟩ : syracuseStep 3155699 = 4733549) B4733549
theorem B2103799 : Blo 2103435 2103799 := bstep (se 1 (by rfl) ⟨1577849, by rfl⟩ : syracuseStep 2103799 = 3155699) B3155699
theorem B3993941 : Blo 2103435 3993941 := bbase (se 10 (by rfl) ⟨5850, by rfl⟩ : syracuseStep 3993941 = 11701) (by norm_num)
theorem B2662627 : Blo 2103435 2662627 := bstep (se 1 (by rfl) ⟨1996970, by rfl⟩ : syracuseStep 2662627 = 3993941) B3993941
theorem B3550169 : Blo 2103435 3550169 := bstep (se 2 (by rfl) ⟨1331313, by rfl⟩ : syracuseStep 3550169 = 2662627) B2662627
theorem B2366779 : Blo 2103435 2366779 := bstep (se 1 (by rfl) ⟨1775084, by rfl⟩ : syracuseStep 2366779 = 3550169) B3550169
theorem B3155705 : Blo 2103435 3155705 := bstep (se 2 (by rfl) ⟨1183389, by rfl⟩ : syracuseStep 3155705 = 2366779) B2366779
theorem B2103803 : Blo 2103435 2103803 := bstep (se 1 (by rfl) ⟨1577852, by rfl⟩ : syracuseStep 2103803 = 3155705) B3155705
theorem B2339813 : Blo 2103435 2339813 := bbase (se 4 (by rfl) ⟨219357, by rfl⟩ : syracuseStep 2339813 = 438715) (by norm_num)
theorem B6239501 : Blo 2103435 6239501 := bstep (se 3 (by rfl) ⟨1169906, by rfl⟩ : syracuseStep 6239501 = 2339813) B2339813
theorem B4159667 : Blo 2103435 4159667 := bstep (se 1 (by rfl) ⟨3119750, by rfl⟩ : syracuseStep 4159667 = 6239501) B6239501
theorem B2773111 : Blo 2103435 2773111 := bstep (se 1 (by rfl) ⟨2079833, by rfl⟩ : syracuseStep 2773111 = 4159667) B4159667
theorem B3697481 : Blo 2103435 3697481 := bstep (se 2 (by rfl) ⟨1386555, by rfl⟩ : syracuseStep 3697481 = 2773111) B2773111
theorem B2464987 : Blo 2103435 2464987 := bstep (se 1 (by rfl) ⟨1848740, by rfl⟩ : syracuseStep 2464987 = 3697481) B3697481
theorem B3286649 : Blo 2103435 3286649 := bstep (se 2 (by rfl) ⟨1232493, by rfl⟩ : syracuseStep 3286649 = 2464987) B2464987
theorem B2191099 : Blo 2103435 2191099 := bstep (se 1 (by rfl) ⟨1643324, by rfl⟩ : syracuseStep 2191099 = 3286649) B3286649
theorem B2921465 : Blo 2103435 2921465 := bstep (se 2 (by rfl) ⟨1095549, by rfl⟩ : syracuseStep 2921465 = 2191099) B2191099
theorem B7790573 : Blo 2103435 7790573 := bstep (se 3 (by rfl) ⟨1460732, by rfl⟩ : syracuseStep 7790573 = 2921465) B2921465
theorem B5193715 : Blo 2103435 5193715 := bstep (se 1 (by rfl) ⟨3895286, by rfl⟩ : syracuseStep 5193715 = 7790573) B7790573
theorem B6924953 : Blo 2103435 6924953 := bstep (se 2 (by rfl) ⟨2596857, by rfl⟩ : syracuseStep 6924953 = 5193715) B5193715
theorem B18466541 : Blo 2103435 18466541 := bstep (se 3 (by rfl) ⟨3462476, by rfl⟩ : syracuseStep 18466541 = 6924953) B6924953
theorem B12311027 : Blo 2103435 12311027 := bstep (se 1 (by rfl) ⟨9233270, by rfl⟩ : syracuseStep 12311027 = 18466541) B18466541
theorem B8207351 : Blo 2103435 8207351 := bstep (se 1 (by rfl) ⟨6155513, by rfl⟩ : syracuseStep 8207351 = 12311027) B12311027
theorem B5471567 : Blo 2103435 5471567 := bstep (se 1 (by rfl) ⟨4103675, by rfl⟩ : syracuseStep 5471567 = 8207351) B8207351
theorem B3647711 : Blo 2103435 3647711 := bstep (se 1 (by rfl) ⟨2735783, by rfl⟩ : syracuseStep 3647711 = 5471567) B5471567
theorem B9727229 : Blo 2103435 9727229 := bstep (se 3 (by rfl) ⟨1823855, by rfl⟩ : syracuseStep 9727229 = 3647711) B3647711
theorem B25939277 : Blo 2103435 25939277 := bstep (se 3 (by rfl) ⟨4863614, by rfl⟩ : syracuseStep 25939277 = 9727229) B9727229
theorem B17292851 : Blo 2103435 17292851 := bstep (se 1 (by rfl) ⟨12969638, by rfl⟩ : syracuseStep 17292851 = 25939277) B25939277
theorem B11528567 : Blo 2103435 11528567 := bstep (se 1 (by rfl) ⟨8646425, by rfl⟩ : syracuseStep 11528567 = 17292851) B17292851
theorem B7685711 : Blo 2103435 7685711 := bstep (se 1 (by rfl) ⟨5764283, by rfl⟩ : syracuseStep 7685711 = 11528567) B11528567
theorem B5123807 : Blo 2103435 5123807 := bstep (se 1 (by rfl) ⟨3842855, by rfl⟩ : syracuseStep 5123807 = 7685711) B7685711
theorem B3415871 : Blo 2103435 3415871 := bstep (se 1 (by rfl) ⟨2561903, by rfl⟩ : syracuseStep 3415871 = 5123807) B5123807
theorem B9108989 : Blo 2103435 9108989 := bstep (se 3 (by rfl) ⟨1707935, by rfl⟩ : syracuseStep 9108989 = 3415871) B3415871
theorem B6072659 : Blo 2103435 6072659 := bstep (se 1 (by rfl) ⟨4554494, by rfl⟩ : syracuseStep 6072659 = 9108989) B9108989
theorem B4048439 : Blo 2103435 4048439 := bstep (se 1 (by rfl) ⟨3036329, by rfl⟩ : syracuseStep 4048439 = 6072659) B6072659
theorem B10795837 : Blo 2103435 10795837 := bstep (se 3 (by rfl) ⟨2024219, by rfl⟩ : syracuseStep 10795837 = 4048439) B4048439
theorem B14394449 : Blo 2103435 14394449 := bstep (se 2 (by rfl) ⟨5397918, by rfl⟩ : syracuseStep 14394449 = 10795837) B10795837
theorem B38385197 : Blo 2103435 38385197 := bstep (se 3 (by rfl) ⟨7197224, by rfl⟩ : syracuseStep 38385197 = 14394449) B14394449
theorem B25590131 : Blo 2103435 25590131 := bstep (se 1 (by rfl) ⟨19192598, by rfl⟩ : syracuseStep 25590131 = 38385197) B38385197
theorem B17060087 : Blo 2103435 17060087 := bstep (se 1 (by rfl) ⟨12795065, by rfl⟩ : syracuseStep 17060087 = 25590131) B25590131
theorem B11373391 : Blo 2103435 11373391 := bstep (se 1 (by rfl) ⟨8530043, by rfl⟩ : syracuseStep 11373391 = 17060087) B17060087
theorem B60658085 : Blo 2103435 60658085 := bstep (se 4 (by rfl) ⟨5686695, by rfl⟩ : syracuseStep 60658085 = 11373391) B11373391
theorem B40438723 : Blo 2103435 40438723 := bstep (se 1 (by rfl) ⟨30329042, by rfl⟩ : syracuseStep 40438723 = 60658085) B60658085
theorem B53918297 : Blo 2103435 53918297 := bstep (se 2 (by rfl) ⟨20219361, by rfl⟩ : syracuseStep 53918297 = 40438723) B40438723
theorem B35945531 : Blo 2103435 35945531 := bstep (se 1 (by rfl) ⟨26959148, by rfl⟩ : syracuseStep 35945531 = 53918297) B53918297
theorem B23963687 : Blo 2103435 23963687 := bstep (se 1 (by rfl) ⟨17972765, by rfl⟩ : syracuseStep 23963687 = 35945531) B35945531
theorem B15975791 : Blo 2103435 15975791 := bstep (se 1 (by rfl) ⟨11981843, by rfl⟩ : syracuseStep 15975791 = 23963687) B23963687
theorem B10650527 : Blo 2103435 10650527 := bstep (se 1 (by rfl) ⟨7987895, by rfl⟩ : syracuseStep 10650527 = 15975791) B15975791
theorem B7100351 : Blo 2103435 7100351 := bstep (se 1 (by rfl) ⟨5325263, by rfl⟩ : syracuseStep 7100351 = 10650527) B10650527
theorem B4733567 : Blo 2103435 4733567 := bstep (se 1 (by rfl) ⟨3550175, by rfl⟩ : syracuseStep 4733567 = 7100351) B7100351
theorem B3155711 : Blo 2103435 3155711 := bstep (se 1 (by rfl) ⟨2366783, by rfl⟩ : syracuseStep 3155711 = 4733567) B4733567
theorem B2103807 : Blo 2103435 2103807 := bstep (se 1 (by rfl) ⟨1577855, by rfl⟩ : syracuseStep 2103807 = 3155711) B3155711
theorem B3155717 : Blo 2103435 3155717 := bbase (se 4 (by rfl) ⟨295848, by rfl⟩ : syracuseStep 3155717 = 591697) (by norm_num)
theorem B2103811 : Blo 2103435 2103811 := bstep (se 1 (by rfl) ⟨1577858, by rfl⟩ : syracuseStep 2103811 = 3155717) B3155717
theorem B3550189 : Blo 2103435 3550189 := bbase (se 3 (by rfl) ⟨665660, by rfl⟩ : syracuseStep 3550189 = 1331321) (by norm_num)
theorem B4733585 : Blo 2103435 4733585 := bstep (se 2 (by rfl) ⟨1775094, by rfl⟩ : syracuseStep 4733585 = 3550189) B3550189
theorem B3155723 : Blo 2103435 3155723 := bstep (se 1 (by rfl) ⟨2366792, by rfl⟩ : syracuseStep 3155723 = 4733585) B4733585
theorem B2103815 : Blo 2103435 2103815 := bstep (se 1 (by rfl) ⟨1577861, by rfl⟩ : syracuseStep 2103815 = 3155723) B3155723
theorem B2366797 : Blo 2103435 2366797 := bbase (se 3 (by rfl) ⟨443774, by rfl⟩ : syracuseStep 2366797 = 887549) (by norm_num)
theorem B3155729 : Blo 2103435 3155729 := bstep (se 2 (by rfl) ⟨1183398, by rfl⟩ : syracuseStep 3155729 = 2366797) B2366797
theorem B2103819 : Blo 2103435 2103819 := bstep (se 1 (by rfl) ⟨1577864, by rfl⟩ : syracuseStep 2103819 = 3155729) B3155729
theorem B7100405 : Blo 2103435 7100405 := bbase (se 5 (by rfl) ⟨332831, by rfl⟩ : syracuseStep 7100405 = 665663) (by norm_num)
theorem B4733603 : Blo 2103435 4733603 := bstep (se 1 (by rfl) ⟨3550202, by rfl⟩ : syracuseStep 4733603 = 7100405) B7100405
theorem B3155735 : Blo 2103435 3155735 := bstep (se 1 (by rfl) ⟨2366801, by rfl⟩ : syracuseStep 3155735 = 4733603) B4733603
theorem B2103823 : Blo 2103435 2103823 := bstep (se 1 (by rfl) ⟨1577867, by rfl⟩ : syracuseStep 2103823 = 3155735) B3155735
theorem B3155741 : Blo 2103435 3155741 := bbase (se 3 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 3155741 = 1183403) (by norm_num)
theorem B2103827 : Blo 2103435 2103827 := bstep (se 1 (by rfl) ⟨1577870, by rfl⟩ : syracuseStep 2103827 = 3155741) B3155741
theorem B4733621 : Blo 2103435 4733621 := bbase (se 5 (by rfl) ⟨221888, by rfl⟩ : syracuseStep 4733621 = 443777) (by norm_num)
theorem B3155747 : Blo 2103435 3155747 := bstep (se 1 (by rfl) ⟨2366810, by rfl⟩ : syracuseStep 3155747 = 4733621) B4733621
theorem B2103831 : Blo 2103435 2103831 := bstep (se 1 (by rfl) ⟨1577873, by rfl⟩ : syracuseStep 2103831 = 3155747) B3155747
theorem B11982005 : Blo 2103435 11982005 := bbase (se 5 (by rfl) ⟨561656, by rfl⟩ : syracuseStep 11982005 = 1123313) (by norm_num)
theorem B7988003 : Blo 2103435 7988003 := bstep (se 1 (by rfl) ⟨5991002, by rfl⟩ : syracuseStep 7988003 = 11982005) B11982005
theorem B5325335 : Blo 2103435 5325335 := bstep (se 1 (by rfl) ⟨3994001, by rfl⟩ : syracuseStep 5325335 = 7988003) B7988003
theorem B3550223 : Blo 2103435 3550223 := bstep (se 1 (by rfl) ⟨2662667, by rfl⟩ : syracuseStep 3550223 = 5325335) B5325335
theorem B2366815 : Blo 2103435 2366815 := bstep (se 1 (by rfl) ⟨1775111, by rfl⟩ : syracuseStep 2366815 = 3550223) B3550223
theorem B3155753 : Blo 2103435 3155753 := bstep (se 2 (by rfl) ⟨1183407, by rfl⟩ : syracuseStep 3155753 = 2366815) B2366815
theorem B2103835 : Blo 2103435 2103835 := bstep (se 1 (by rfl) ⟨1577876, by rfl⟩ : syracuseStep 2103835 = 3155753) B3155753
theorem B5991013 : Blo 2103435 5991013 := bbase (se 4 (by rfl) ⟨561657, by rfl⟩ : syracuseStep 5991013 = 1123315) (by norm_num)
theorem B7988017 : Blo 2103435 7988017 := bstep (se 2 (by rfl) ⟨2995506, by rfl⟩ : syracuseStep 7988017 = 5991013) B5991013
theorem B10650689 : Blo 2103435 10650689 := bstep (se 2 (by rfl) ⟨3994008, by rfl⟩ : syracuseStep 10650689 = 7988017) B7988017
theorem B7100459 : Blo 2103435 7100459 := bstep (se 1 (by rfl) ⟨5325344, by rfl⟩ : syracuseStep 7100459 = 10650689) B10650689
theorem B4733639 : Blo 2103435 4733639 := bstep (se 1 (by rfl) ⟨3550229, by rfl⟩ : syracuseStep 4733639 = 7100459) B7100459
theorem B3155759 : Blo 2103435 3155759 := bstep (se 1 (by rfl) ⟨2366819, by rfl⟩ : syracuseStep 3155759 = 4733639) B4733639
theorem B2103839 : Blo 2103435 2103839 := bstep (se 1 (by rfl) ⟨1577879, by rfl⟩ : syracuseStep 2103839 = 3155759) B3155759
theorem B3155765 : Blo 2103435 3155765 := bbase (se 5 (by rfl) ⟨147926, by rfl⟩ : syracuseStep 3155765 = 295853) (by norm_num)
theorem B2103843 : Blo 2103435 2103843 := bstep (se 1 (by rfl) ⟨1577882, by rfl⟩ : syracuseStep 2103843 = 3155765) B3155765
theorem B5325365 : Blo 2103435 5325365 := bbase (se 5 (by rfl) ⟨249626, by rfl⟩ : syracuseStep 5325365 = 499253) (by norm_num)
theorem B3550243 : Blo 2103435 3550243 := bstep (se 1 (by rfl) ⟨2662682, by rfl⟩ : syracuseStep 3550243 = 5325365) B5325365
theorem B4733657 : Blo 2103435 4733657 := bstep (se 2 (by rfl) ⟨1775121, by rfl⟩ : syracuseStep 4733657 = 3550243) B3550243
theorem B3155771 : Blo 2103435 3155771 := bstep (se 1 (by rfl) ⟨2366828, by rfl⟩ : syracuseStep 3155771 = 4733657) B4733657
theorem B2103847 : Blo 2103435 2103847 := bstep (se 1 (by rfl) ⟨1577885, by rfl⟩ : syracuseStep 2103847 = 3155771) B3155771
theorem B2366833 : Blo 2103435 2366833 := bbase (se 2 (by rfl) ⟨887562, by rfl⟩ : syracuseStep 2366833 = 1775125) (by norm_num)
theorem B3155777 : Blo 2103435 3155777 := bstep (se 2 (by rfl) ⟨1183416, by rfl⟩ : syracuseStep 3155777 = 2366833) B2366833
theorem B2103851 : Blo 2103435 2103851 := bstep (se 1 (by rfl) ⟨1577888, by rfl⟩ : syracuseStep 2103851 = 3155777) B3155777
theorem B5054957 : Blo 2103435 5054957 := bbase (se 3 (by rfl) ⟨947804, by rfl⟩ : syracuseStep 5054957 = 1895609) (by norm_num)
theorem B3369971 : Blo 2103435 3369971 := bstep (se 1 (by rfl) ⟨2527478, by rfl⟩ : syracuseStep 3369971 = 5054957) B5054957
theorem B8986589 : Blo 2103435 8986589 := bstep (se 3 (by rfl) ⟨1684985, by rfl⟩ : syracuseStep 8986589 = 3369971) B3369971
theorem B5991059 : Blo 2103435 5991059 := bstep (se 1 (by rfl) ⟨4493294, by rfl⟩ : syracuseStep 5991059 = 8986589) B8986589
theorem B3994039 : Blo 2103435 3994039 := bstep (se 1 (by rfl) ⟨2995529, by rfl⟩ : syracuseStep 3994039 = 5991059) B5991059
theorem B5325385 : Blo 2103435 5325385 := bstep (se 2 (by rfl) ⟨1997019, by rfl⟩ : syracuseStep 5325385 = 3994039) B3994039
theorem B7100513 : Blo 2103435 7100513 := bstep (se 2 (by rfl) ⟨2662692, by rfl⟩ : syracuseStep 7100513 = 5325385) B5325385
theorem B4733675 : Blo 2103435 4733675 := bstep (se 1 (by rfl) ⟨3550256, by rfl⟩ : syracuseStep 4733675 = 7100513) B7100513
theorem B3155783 : Blo 2103435 3155783 := bstep (se 1 (by rfl) ⟨2366837, by rfl⟩ : syracuseStep 3155783 = 4733675) B4733675
theorem B2103855 : Blo 2103435 2103855 := bstep (se 1 (by rfl) ⟨1577891, by rfl⟩ : syracuseStep 2103855 = 3155783) B3155783
theorem B3155789 : Blo 2103435 3155789 := bbase (se 3 (by rfl) ⟨591710, by rfl⟩ : syracuseStep 3155789 = 1183421) (by norm_num)
theorem B2103859 : Blo 2103435 2103859 := bstep (se 1 (by rfl) ⟨1577894, by rfl⟩ : syracuseStep 2103859 = 3155789) B3155789
theorem B4733693 : Blo 2103435 4733693 := bbase (se 3 (by rfl) ⟨887567, by rfl⟩ : syracuseStep 4733693 = 1775135) (by norm_num)
theorem B3155795 : Blo 2103435 3155795 := bstep (se 1 (by rfl) ⟨2366846, by rfl⟩ : syracuseStep 3155795 = 4733693) B4733693
theorem B2103863 : Blo 2103435 2103863 := bstep (se 1 (by rfl) ⟨1577897, by rfl⟩ : syracuseStep 2103863 = 3155795) B3155795
theorem B3550277 : Blo 2103435 3550277 := bbase (se 4 (by rfl) ⟨332838, by rfl⟩ : syracuseStep 3550277 = 665677) (by norm_num)
theorem B2366851 : Blo 2103435 2366851 := bstep (se 1 (by rfl) ⟨1775138, by rfl⟩ : syracuseStep 2366851 = 3550277) B3550277
theorem B3155801 : Blo 2103435 3155801 := bstep (se 2 (by rfl) ⟨1183425, by rfl⟩ : syracuseStep 3155801 = 2366851) B2366851
theorem B2103867 : Blo 2103435 2103867 := bstep (se 1 (by rfl) ⟨1577900, by rfl⟩ : syracuseStep 2103867 = 3155801) B3155801
theorem B15976277 : Blo 2103435 15976277 := bbase (se 9 (by rfl) ⟨46805, by rfl⟩ : syracuseStep 15976277 = 93611) (by norm_num)
theorem B10650851 : Blo 2103435 10650851 := bstep (se 1 (by rfl) ⟨7988138, by rfl⟩ : syracuseStep 10650851 = 15976277) B15976277
theorem B7100567 : Blo 2103435 7100567 := bstep (se 1 (by rfl) ⟨5325425, by rfl⟩ : syracuseStep 7100567 = 10650851) B10650851
theorem B4733711 : Blo 2103435 4733711 := bstep (se 1 (by rfl) ⟨3550283, by rfl⟩ : syracuseStep 4733711 = 7100567) B7100567
theorem B3155807 : Blo 2103435 3155807 := bstep (se 1 (by rfl) ⟨2366855, by rfl⟩ : syracuseStep 3155807 = 4733711) B4733711
theorem B2103871 : Blo 2103435 2103871 := bstep (se 1 (by rfl) ⟨1577903, by rfl⟩ : syracuseStep 2103871 = 3155807) B3155807
theorem B3155813 : Blo 2103435 3155813 := bbase (se 4 (by rfl) ⟨295857, by rfl⟩ : syracuseStep 3155813 = 591715) (by norm_num)
theorem B2103875 : Blo 2103435 2103875 := bstep (se 1 (by rfl) ⟨1577906, by rfl⟩ : syracuseStep 2103875 = 3155813) B3155813
theorem B3994085 : Blo 2103435 3994085 := bbase (se 4 (by rfl) ⟨374445, by rfl⟩ : syracuseStep 3994085 = 748891) (by norm_num)
theorem B2662723 : Blo 2103435 2662723 := bstep (se 1 (by rfl) ⟨1997042, by rfl⟩ : syracuseStep 2662723 = 3994085) B3994085
theorem B3550297 : Blo 2103435 3550297 := bstep (se 2 (by rfl) ⟨1331361, by rfl⟩ : syracuseStep 3550297 = 2662723) B2662723
theorem B4733729 : Blo 2103435 4733729 := bstep (se 2 (by rfl) ⟨1775148, by rfl⟩ : syracuseStep 4733729 = 3550297) B3550297
theorem B3155819 : Blo 2103435 3155819 := bstep (se 1 (by rfl) ⟨2366864, by rfl⟩ : syracuseStep 3155819 = 4733729) B4733729
theorem B2103879 : Blo 2103435 2103879 := bstep (se 1 (by rfl) ⟨1577909, by rfl⟩ : syracuseStep 2103879 = 3155819) B3155819
theorem B2366869 : Blo 2103435 2366869 := bbase (se 6 (by rfl) ⟨55473, by rfl⟩ : syracuseStep 2366869 = 110947) (by norm_num)
theorem B3155825 : Blo 2103435 3155825 := bstep (se 2 (by rfl) ⟨1183434, by rfl⟩ : syracuseStep 3155825 = 2366869) B2366869
theorem B2103883 : Blo 2103435 2103883 := bstep (se 1 (by rfl) ⟨1577912, by rfl⟩ : syracuseStep 2103883 = 3155825) B3155825
theorem B2662733 : Blo 2103435 2662733 := bbase (se 3 (by rfl) ⟨499262, by rfl⟩ : syracuseStep 2662733 = 998525) (by norm_num)
theorem B7100621 : Blo 2103435 7100621 := bstep (se 3 (by rfl) ⟨1331366, by rfl⟩ : syracuseStep 7100621 = 2662733) B2662733
theorem B4733747 : Blo 2103435 4733747 := bstep (se 1 (by rfl) ⟨3550310, by rfl⟩ : syracuseStep 4733747 = 7100621) B7100621
theorem B3155831 : Blo 2103435 3155831 := bstep (se 1 (by rfl) ⟨2366873, by rfl⟩ : syracuseStep 3155831 = 4733747) B4733747
theorem B2103887 : Blo 2103435 2103887 := bstep (se 1 (by rfl) ⟨1577915, by rfl⟩ : syracuseStep 2103887 = 3155831) B3155831
theorem B3155837 : Blo 2103435 3155837 := bbase (se 3 (by rfl) ⟨591719, by rfl⟩ : syracuseStep 3155837 = 1183439) (by norm_num)
theorem B2103891 : Blo 2103435 2103891 := bstep (se 1 (by rfl) ⟨1577918, by rfl⟩ : syracuseStep 2103891 = 3155837) B3155837
theorem B4733765 : Blo 2103435 4733765 := bbase (se 4 (by rfl) ⟨443790, by rfl⟩ : syracuseStep 4733765 = 887581) (by norm_num)
theorem B3155843 : Blo 2103435 3155843 := bstep (se 1 (by rfl) ⟨2366882, by rfl⟩ : syracuseStep 3155843 = 4733765) B4733765
theorem B2103895 : Blo 2103435 2103895 := bstep (se 1 (by rfl) ⟨1577921, by rfl⟩ : syracuseStep 2103895 = 3155843) B3155843
theorem B4493389 : Blo 2103435 4493389 := bbase (se 3 (by rfl) ⟨842510, by rfl⟩ : syracuseStep 4493389 = 1685021) (by norm_num)
theorem B5991185 : Blo 2103435 5991185 := bstep (se 2 (by rfl) ⟨2246694, by rfl⟩ : syracuseStep 5991185 = 4493389) B4493389
theorem B3994123 : Blo 2103435 3994123 := bstep (se 1 (by rfl) ⟨2995592, by rfl⟩ : syracuseStep 3994123 = 5991185) B5991185
theorem B5325497 : Blo 2103435 5325497 := bstep (se 2 (by rfl) ⟨1997061, by rfl⟩ : syracuseStep 5325497 = 3994123) B3994123
theorem B3550331 : Blo 2103435 3550331 := bstep (se 1 (by rfl) ⟨2662748, by rfl⟩ : syracuseStep 3550331 = 5325497) B5325497
theorem B2366887 : Blo 2103435 2366887 := bstep (se 1 (by rfl) ⟨1775165, by rfl⟩ : syracuseStep 2366887 = 3550331) B3550331
theorem B3155849 : Blo 2103435 3155849 := bstep (se 2 (by rfl) ⟨1183443, by rfl⟩ : syracuseStep 3155849 = 2366887) B2366887
theorem B2103899 : Blo 2103435 2103899 := bstep (se 1 (by rfl) ⟨1577924, by rfl⟩ : syracuseStep 2103899 = 3155849) B3155849
theorem B10651013 : Blo 2103435 10651013 := bbase (se 4 (by rfl) ⟨998532, by rfl⟩ : syracuseStep 10651013 = 1997065) (by norm_num)
theorem B7100675 : Blo 2103435 7100675 := bstep (se 1 (by rfl) ⟨5325506, by rfl⟩ : syracuseStep 7100675 = 10651013) B10651013
theorem B4733783 : Blo 2103435 4733783 := bstep (se 1 (by rfl) ⟨3550337, by rfl⟩ : syracuseStep 4733783 = 7100675) B7100675
theorem B3155855 : Blo 2103435 3155855 := bstep (se 1 (by rfl) ⟨2366891, by rfl⟩ : syracuseStep 3155855 = 4733783) B4733783
theorem B2103903 : Blo 2103435 2103903 := bstep (se 1 (by rfl) ⟨1577927, by rfl⟩ : syracuseStep 2103903 = 3155855) B3155855
theorem B3155861 : Blo 2103435 3155861 := bbase (se 6 (by rfl) ⟨73965, by rfl⟩ : syracuseStep 3155861 = 147931) (by norm_num)
theorem B2103907 : Blo 2103435 2103907 := bstep (se 1 (by rfl) ⟨1577930, by rfl⟩ : syracuseStep 2103907 = 3155861) B3155861
theorem B3370061 : Blo 2103435 3370061 := bbase (se 3 (by rfl) ⟨631886, by rfl⟩ : syracuseStep 3370061 = 1263773) (by norm_num)
theorem B2246707 : Blo 2103435 2246707 := bstep (se 1 (by rfl) ⟨1685030, by rfl⟩ : syracuseStep 2246707 = 3370061) B3370061
theorem B11982437 : Blo 2103435 11982437 := bstep (se 4 (by rfl) ⟨1123353, by rfl⟩ : syracuseStep 11982437 = 2246707) B2246707
theorem B7988291 : Blo 2103435 7988291 := bstep (se 1 (by rfl) ⟨5991218, by rfl⟩ : syracuseStep 7988291 = 11982437) B11982437
theorem B5325527 : Blo 2103435 5325527 := bstep (se 1 (by rfl) ⟨3994145, by rfl⟩ : syracuseStep 5325527 = 7988291) B7988291
theorem B3550351 : Blo 2103435 3550351 := bstep (se 1 (by rfl) ⟨2662763, by rfl⟩ : syracuseStep 3550351 = 5325527) B5325527
theorem B4733801 : Blo 2103435 4733801 := bstep (se 2 (by rfl) ⟨1775175, by rfl⟩ : syracuseStep 4733801 = 3550351) B3550351
theorem B3155867 : Blo 2103435 3155867 := bstep (se 1 (by rfl) ⟨2366900, by rfl⟩ : syracuseStep 3155867 = 4733801) B4733801
theorem B2103911 : Blo 2103435 2103911 := bstep (se 1 (by rfl) ⟨1577933, by rfl⟩ : syracuseStep 2103911 = 3155867) B3155867
theorem B2366905 : Blo 2103435 2366905 := bbase (se 2 (by rfl) ⟨887589, by rfl⟩ : syracuseStep 2366905 = 1775179) (by norm_num)
theorem B3155873 : Blo 2103435 3155873 := bstep (se 2 (by rfl) ⟨1183452, by rfl⟩ : syracuseStep 3155873 = 2366905) B2366905
theorem B2103915 : Blo 2103435 2103915 := bstep (se 1 (by rfl) ⟨1577936, by rfl⟩ : syracuseStep 2103915 = 3155873) B3155873
theorem B3791333 : Blo 2103435 3791333 := bbase (se 4 (by rfl) ⟨355437, by rfl⟩ : syracuseStep 3791333 = 710875) (by norm_num)
theorem B10110221 : Blo 2103435 10110221 := bstep (se 3 (by rfl) ⟨1895666, by rfl⟩ : syracuseStep 10110221 = 3791333) B3791333
theorem B6740147 : Blo 2103435 6740147 := bstep (se 1 (by rfl) ⟨5055110, by rfl⟩ : syracuseStep 6740147 = 10110221) B10110221
theorem B4493431 : Blo 2103435 4493431 := bstep (se 1 (by rfl) ⟨3370073, by rfl⟩ : syracuseStep 4493431 = 6740147) B6740147
theorem B5991241 : Blo 2103435 5991241 := bstep (se 2 (by rfl) ⟨2246715, by rfl⟩ : syracuseStep 5991241 = 4493431) B4493431
theorem B7988321 : Blo 2103435 7988321 := bstep (se 2 (by rfl) ⟨2995620, by rfl⟩ : syracuseStep 7988321 = 5991241) B5991241
theorem B5325547 : Blo 2103435 5325547 := bstep (se 1 (by rfl) ⟨3994160, by rfl⟩ : syracuseStep 5325547 = 7988321) B7988321
theorem B7100729 : Blo 2103435 7100729 := bstep (se 2 (by rfl) ⟨2662773, by rfl⟩ : syracuseStep 7100729 = 5325547) B5325547
theorem B4733819 : Blo 2103435 4733819 := bstep (se 1 (by rfl) ⟨3550364, by rfl⟩ : syracuseStep 4733819 = 7100729) B7100729
theorem B3155879 : Blo 2103435 3155879 := bstep (se 1 (by rfl) ⟨2366909, by rfl⟩ : syracuseStep 3155879 = 4733819) B4733819
theorem B2103919 : Blo 2103435 2103919 := bstep (se 1 (by rfl) ⟨1577939, by rfl⟩ : syracuseStep 2103919 = 3155879) B3155879
theorem B3155885 : Blo 2103435 3155885 := bbase (se 3 (by rfl) ⟨591728, by rfl⟩ : syracuseStep 3155885 = 1183457) (by norm_num)
theorem B2103923 : Blo 2103435 2103923 := bstep (se 1 (by rfl) ⟨1577942, by rfl⟩ : syracuseStep 2103923 = 3155885) B3155885
theorem B4733837 : Blo 2103435 4733837 := bbase (se 3 (by rfl) ⟨887594, by rfl⟩ : syracuseStep 4733837 = 1775189) (by norm_num)
theorem B3155891 : Blo 2103435 3155891 := bstep (se 1 (by rfl) ⟨2366918, by rfl⟩ : syracuseStep 3155891 = 4733837) B4733837
theorem B2103927 : Blo 2103435 2103927 := bstep (se 1 (by rfl) ⟨1577945, by rfl⟩ : syracuseStep 2103927 = 3155891) B3155891
theorem B2662789 : Blo 2103435 2662789 := bbase (se 4 (by rfl) ⟨249636, by rfl⟩ : syracuseStep 2662789 = 499273) (by norm_num)
theorem B3550385 : Blo 2103435 3550385 := bstep (se 2 (by rfl) ⟨1331394, by rfl⟩ : syracuseStep 3550385 = 2662789) B2662789
theorem B2366923 : Blo 2103435 2366923 := bstep (se 1 (by rfl) ⟨1775192, by rfl⟩ : syracuseStep 2366923 = 3550385) B3550385
theorem B3155897 : Blo 2103435 3155897 := bstep (se 2 (by rfl) ⟨1183461, by rfl⟩ : syracuseStep 3155897 = 2366923) B2366923
theorem B2103931 : Blo 2103435 2103931 := bstep (se 1 (by rfl) ⟨1577948, by rfl⟩ : syracuseStep 2103931 = 3155897) B3155897
theorem B26960789 : Blo 2103435 26960789 := bbase (se 6 (by rfl) ⟨631893, by rfl⟩ : syracuseStep 26960789 = 1263787) (by norm_num)
theorem B17973859 : Blo 2103435 17973859 := bstep (se 1 (by rfl) ⟨13480394, by rfl⟩ : syracuseStep 17973859 = 26960789) B26960789
theorem B23965145 : Blo 2103435 23965145 := bstep (se 2 (by rfl) ⟨8986929, by rfl⟩ : syracuseStep 23965145 = 17973859) B17973859
theorem B15976763 : Blo 2103435 15976763 := bstep (se 1 (by rfl) ⟨11982572, by rfl⟩ : syracuseStep 15976763 = 23965145) B23965145
theorem B10651175 : Blo 2103435 10651175 := bstep (se 1 (by rfl) ⟨7988381, by rfl⟩ : syracuseStep 10651175 = 15976763) B15976763
theorem B7100783 : Blo 2103435 7100783 := bstep (se 1 (by rfl) ⟨5325587, by rfl⟩ : syracuseStep 7100783 = 10651175) B10651175
theorem B4733855 : Blo 2103435 4733855 := bstep (se 1 (by rfl) ⟨3550391, by rfl⟩ : syracuseStep 4733855 = 7100783) B7100783
theorem B3155903 : Blo 2103435 3155903 := bstep (se 1 (by rfl) ⟨2366927, by rfl⟩ : syracuseStep 3155903 = 4733855) B4733855
theorem B2103935 : Blo 2103435 2103935 := bstep (se 1 (by rfl) ⟨1577951, by rfl⟩ : syracuseStep 2103935 = 3155903) B3155903
theorem B3155909 : Blo 2103435 3155909 := bbase (se 4 (by rfl) ⟨295866, by rfl⟩ : syracuseStep 3155909 = 591733) (by norm_num)
theorem B2103939 : Blo 2103435 2103939 := bstep (se 1 (by rfl) ⟨1577954, by rfl⟩ : syracuseStep 2103939 = 3155909) B3155909
theorem B3550405 : Blo 2103435 3550405 := bbase (se 4 (by rfl) ⟨332850, by rfl⟩ : syracuseStep 3550405 = 665701) (by norm_num)
theorem B4733873 : Blo 2103435 4733873 := bstep (se 2 (by rfl) ⟨1775202, by rfl⟩ : syracuseStep 4733873 = 3550405) B3550405
theorem B3155915 : Blo 2103435 3155915 := bstep (se 1 (by rfl) ⟨2366936, by rfl⟩ : syracuseStep 3155915 = 4733873) B4733873
theorem B2103943 : Blo 2103435 2103943 := bstep (se 1 (by rfl) ⟨1577957, by rfl⟩ : syracuseStep 2103943 = 3155915) B3155915
theorem B2366941 : Blo 2103435 2366941 := bbase (se 3 (by rfl) ⟨443801, by rfl⟩ : syracuseStep 2366941 = 887603) (by norm_num)
theorem B3155921 : Blo 2103435 3155921 := bstep (se 2 (by rfl) ⟨1183470, by rfl⟩ : syracuseStep 3155921 = 2366941) B2366941
theorem B2103947 : Blo 2103435 2103947 := bstep (se 1 (by rfl) ⟨1577960, by rfl⟩ : syracuseStep 2103947 = 3155921) B3155921
theorem B7100837 : Blo 2103435 7100837 := bbase (se 4 (by rfl) ⟨665703, by rfl⟩ : syracuseStep 7100837 = 1331407) (by norm_num)
theorem B4733891 : Blo 2103435 4733891 := bstep (se 1 (by rfl) ⟨3550418, by rfl⟩ : syracuseStep 4733891 = 7100837) B7100837
theorem B3155927 : Blo 2103435 3155927 := bstep (se 1 (by rfl) ⟨2366945, by rfl⟩ : syracuseStep 3155927 = 4733891) B4733891
theorem B2103951 : Blo 2103435 2103951 := bstep (se 1 (by rfl) ⟨1577963, by rfl⟩ : syracuseStep 2103951 = 3155927) B3155927
theorem B3155933 : Blo 2103435 3155933 := bbase (se 3 (by rfl) ⟨591737, by rfl⟩ : syracuseStep 3155933 = 1183475) (by norm_num)
theorem B2103955 : Blo 2103435 2103955 := bstep (se 1 (by rfl) ⟨1577966, by rfl⟩ : syracuseStep 2103955 = 3155933) B3155933
theorem B4733909 : Blo 2103435 4733909 := bbase (se 7 (by rfl) ⟨55475, by rfl⟩ : syracuseStep 4733909 = 110951) (by norm_num)
theorem B3155939 : Blo 2103435 3155939 := bstep (se 1 (by rfl) ⟨2366954, by rfl⟩ : syracuseStep 3155939 = 4733909) B4733909
theorem B2103959 : Blo 2103435 2103959 := bstep (se 1 (by rfl) ⟨1577969, by rfl⟩ : syracuseStep 2103959 = 3155939) B3155939
theorem B4048741 : Blo 2103435 4048741 := bbase (se 4 (by rfl) ⟨379569, by rfl⟩ : syracuseStep 4048741 = 759139) (by norm_num)
theorem B5398321 : Blo 2103435 5398321 := bstep (se 2 (by rfl) ⟨2024370, by rfl⟩ : syracuseStep 5398321 = 4048741) B4048741
theorem B7197761 : Blo 2103435 7197761 := bstep (se 2 (by rfl) ⟨2699160, by rfl⟩ : syracuseStep 7197761 = 5398321) B5398321
theorem B19194029 : Blo 2103435 19194029 := bstep (se 3 (by rfl) ⟨3598880, by rfl⟩ : syracuseStep 19194029 = 7197761) B7197761
theorem B12796019 : Blo 2103435 12796019 := bstep (se 1 (by rfl) ⟨9597014, by rfl⟩ : syracuseStep 12796019 = 19194029) B19194029
theorem B8530679 : Blo 2103435 8530679 := bstep (se 1 (by rfl) ⟨6398009, by rfl⟩ : syracuseStep 8530679 = 12796019) B12796019
theorem B5687119 : Blo 2103435 5687119 := bstep (se 1 (by rfl) ⟨4265339, by rfl⟩ : syracuseStep 5687119 = 8530679) B8530679
theorem B7582825 : Blo 2103435 7582825 := bstep (se 2 (by rfl) ⟨2843559, by rfl⟩ : syracuseStep 7582825 = 5687119) B5687119
theorem B10110433 : Blo 2103435 10110433 := bstep (se 2 (by rfl) ⟨3791412, by rfl⟩ : syracuseStep 10110433 = 7582825) B7582825
theorem B13480577 : Blo 2103435 13480577 := bstep (se 2 (by rfl) ⟨5055216, by rfl⟩ : syracuseStep 13480577 = 10110433) B10110433
theorem B8987051 : Blo 2103435 8987051 := bstep (se 1 (by rfl) ⟨6740288, by rfl⟩ : syracuseStep 8987051 = 13480577) B13480577
theorem B5991367 : Blo 2103435 5991367 := bstep (se 1 (by rfl) ⟨4493525, by rfl⟩ : syracuseStep 5991367 = 8987051) B8987051
theorem B7988489 : Blo 2103435 7988489 := bstep (se 2 (by rfl) ⟨2995683, by rfl⟩ : syracuseStep 7988489 = 5991367) B5991367
theorem B5325659 : Blo 2103435 5325659 := bstep (se 1 (by rfl) ⟨3994244, by rfl⟩ : syracuseStep 5325659 = 7988489) B7988489
theorem B3550439 : Blo 2103435 3550439 := bstep (se 1 (by rfl) ⟨2662829, by rfl⟩ : syracuseStep 3550439 = 5325659) B5325659
theorem B2366959 : Blo 2103435 2366959 := bstep (se 1 (by rfl) ⟨1775219, by rfl⟩ : syracuseStep 2366959 = 3550439) B3550439
theorem B3155945 : Blo 2103435 3155945 := bstep (se 2 (by rfl) ⟨1183479, by rfl⟩ : syracuseStep 3155945 = 2366959) B2366959
theorem B2103963 : Blo 2103435 2103963 := bstep (se 1 (by rfl) ⟨1577972, by rfl⟩ : syracuseStep 2103963 = 3155945) B3155945
theorem B17974133 : Blo 2103435 17974133 := bbase (se 5 (by rfl) ⟨842537, by rfl⟩ : syracuseStep 17974133 = 1685075) (by norm_num)
theorem B11982755 : Blo 2103435 11982755 := bstep (se 1 (by rfl) ⟨8987066, by rfl⟩ : syracuseStep 11982755 = 17974133) B17974133
theorem B7988503 : Blo 2103435 7988503 := bstep (se 1 (by rfl) ⟨5991377, by rfl⟩ : syracuseStep 7988503 = 11982755) B11982755
theorem B10651337 : Blo 2103435 10651337 := bstep (se 2 (by rfl) ⟨3994251, by rfl⟩ : syracuseStep 10651337 = 7988503) B7988503
theorem B7100891 : Blo 2103435 7100891 := bstep (se 1 (by rfl) ⟨5325668, by rfl⟩ : syracuseStep 7100891 = 10651337) B10651337
theorem B4733927 : Blo 2103435 4733927 := bstep (se 1 (by rfl) ⟨3550445, by rfl⟩ : syracuseStep 4733927 = 7100891) B7100891
theorem B3155951 : Blo 2103435 3155951 := bstep (se 1 (by rfl) ⟨2366963, by rfl⟩ : syracuseStep 3155951 = 4733927) B4733927
theorem B2103967 : Blo 2103435 2103967 := bstep (se 1 (by rfl) ⟨1577975, by rfl⟩ : syracuseStep 2103967 = 3155951) B3155951
theorem B3155957 : Blo 2103435 3155957 := bbase (se 5 (by rfl) ⟨147935, by rfl⟩ : syracuseStep 3155957 = 295871) (by norm_num)
theorem B2103971 : Blo 2103435 2103971 := bstep (se 1 (by rfl) ⟨1577978, by rfl⟩ : syracuseStep 2103971 = 3155957) B3155957
theorem B4617005 : Blo 2103435 4617005 := bbase (se 3 (by rfl) ⟨865688, by rfl⟩ : syracuseStep 4617005 = 1731377) (by norm_num)
theorem B12312013 : Blo 2103435 12312013 := bstep (se 3 (by rfl) ⟨2308502, by rfl⟩ : syracuseStep 12312013 = 4617005) B4617005
theorem B16416017 : Blo 2103435 16416017 := bstep (se 2 (by rfl) ⟨6156006, by rfl⟩ : syracuseStep 16416017 = 12312013) B12312013
theorem B10944011 : Blo 2103435 10944011 := bstep (se 1 (by rfl) ⟨8208008, by rfl⟩ : syracuseStep 10944011 = 16416017) B16416017
theorem B7296007 : Blo 2103435 7296007 := bstep (se 1 (by rfl) ⟨5472005, by rfl⟩ : syracuseStep 7296007 = 10944011) B10944011
theorem B9728009 : Blo 2103435 9728009 := bstep (se 2 (by rfl) ⟨3648003, by rfl⟩ : syracuseStep 9728009 = 7296007) B7296007
theorem B6485339 : Blo 2103435 6485339 := bstep (se 1 (by rfl) ⟨4864004, by rfl⟩ : syracuseStep 6485339 = 9728009) B9728009
theorem B4323559 : Blo 2103435 4323559 := bstep (se 1 (by rfl) ⟨3242669, by rfl⟩ : syracuseStep 4323559 = 6485339) B6485339
theorem B5764745 : Blo 2103435 5764745 := bstep (se 2 (by rfl) ⟨2161779, by rfl⟩ : syracuseStep 5764745 = 4323559) B4323559
theorem B3843163 : Blo 2103435 3843163 := bstep (se 1 (by rfl) ⟨2882372, by rfl⟩ : syracuseStep 3843163 = 5764745) B5764745
theorem B5124217 : Blo 2103435 5124217 := bstep (se 2 (by rfl) ⟨1921581, by rfl⟩ : syracuseStep 5124217 = 3843163) B3843163
theorem B6832289 : Blo 2103435 6832289 := bstep (se 2 (by rfl) ⟨2562108, by rfl⟩ : syracuseStep 6832289 = 5124217) B5124217
theorem B18219437 : Blo 2103435 18219437 := bstep (se 3 (by rfl) ⟨3416144, by rfl⟩ : syracuseStep 18219437 = 6832289) B6832289
theorem B12146291 : Blo 2103435 12146291 := bstep (se 1 (by rfl) ⟨9109718, by rfl⟩ : syracuseStep 12146291 = 18219437) B18219437
theorem B8097527 : Blo 2103435 8097527 := bstep (se 1 (by rfl) ⟨6073145, by rfl⟩ : syracuseStep 8097527 = 12146291) B12146291
theorem B21593405 : Blo 2103435 21593405 := bstep (se 3 (by rfl) ⟨4048763, by rfl⟩ : syracuseStep 21593405 = 8097527) B8097527
theorem B57582413 : Blo 2103435 57582413 := bstep (se 3 (by rfl) ⟨10796702, by rfl⟩ : syracuseStep 57582413 = 21593405) B21593405
theorem B38388275 : Blo 2103435 38388275 := bstep (se 1 (by rfl) ⟨28791206, by rfl⟩ : syracuseStep 38388275 = 57582413) B57582413
theorem B25592183 : Blo 2103435 25592183 := bstep (se 1 (by rfl) ⟨19194137, by rfl⟩ : syracuseStep 25592183 = 38388275) B38388275
theorem B17061455 : Blo 2103435 17061455 := bstep (se 1 (by rfl) ⟨12796091, by rfl⟩ : syracuseStep 17061455 = 25592183) B25592183
theorem B11374303 : Blo 2103435 11374303 := bstep (se 1 (by rfl) ⟨8530727, by rfl⟩ : syracuseStep 11374303 = 17061455) B17061455
theorem B15165737 : Blo 2103435 15165737 := bstep (se 2 (by rfl) ⟨5687151, by rfl⟩ : syracuseStep 15165737 = 11374303) B11374303
theorem B10110491 : Blo 2103435 10110491 := bstep (se 1 (by rfl) ⟨7582868, by rfl⟩ : syracuseStep 10110491 = 15165737) B15165737
theorem B6740327 : Blo 2103435 6740327 := bstep (se 1 (by rfl) ⟨5055245, by rfl⟩ : syracuseStep 6740327 = 10110491) B10110491
theorem B4493551 : Blo 2103435 4493551 := bstep (se 1 (by rfl) ⟨3370163, by rfl⟩ : syracuseStep 4493551 = 6740327) B6740327
theorem B5991401 : Blo 2103435 5991401 := bstep (se 2 (by rfl) ⟨2246775, by rfl⟩ : syracuseStep 5991401 = 4493551) B4493551
theorem B3994267 : Blo 2103435 3994267 := bstep (se 1 (by rfl) ⟨2995700, by rfl⟩ : syracuseStep 3994267 = 5991401) B5991401
theorem B5325689 : Blo 2103435 5325689 := bstep (se 2 (by rfl) ⟨1997133, by rfl⟩ : syracuseStep 5325689 = 3994267) B3994267
theorem B3550459 : Blo 2103435 3550459 := bstep (se 1 (by rfl) ⟨2662844, by rfl⟩ : syracuseStep 3550459 = 5325689) B5325689
theorem B4733945 : Blo 2103435 4733945 := bstep (se 2 (by rfl) ⟨1775229, by rfl⟩ : syracuseStep 4733945 = 3550459) B3550459
theorem B3155963 : Blo 2103435 3155963 := bstep (se 1 (by rfl) ⟨2366972, by rfl⟩ : syracuseStep 3155963 = 4733945) B4733945
theorem B2103975 : Blo 2103435 2103975 := bstep (se 1 (by rfl) ⟨1577981, by rfl⟩ : syracuseStep 2103975 = 3155963) B3155963
theorem B2366977 : Blo 2103435 2366977 := bbase (se 2 (by rfl) ⟨887616, by rfl⟩ : syracuseStep 2366977 = 1775233) (by norm_num)
theorem B3155969 : Blo 2103435 3155969 := bstep (se 2 (by rfl) ⟨1183488, by rfl⟩ : syracuseStep 3155969 = 2366977) B2366977
theorem B2103979 : Blo 2103435 2103979 := bstep (se 1 (by rfl) ⟨1577984, by rfl⟩ : syracuseStep 2103979 = 3155969) B3155969
theorem B5325709 : Blo 2103435 5325709 := bbase (se 3 (by rfl) ⟨998570, by rfl⟩ : syracuseStep 5325709 = 1997141) (by norm_num)
theorem B7100945 : Blo 2103435 7100945 := bstep (se 2 (by rfl) ⟨2662854, by rfl⟩ : syracuseStep 7100945 = 5325709) B5325709
theorem B4733963 : Blo 2103435 4733963 := bstep (se 1 (by rfl) ⟨3550472, by rfl⟩ : syracuseStep 4733963 = 7100945) B7100945
theorem B3155975 : Blo 2103435 3155975 := bstep (se 1 (by rfl) ⟨2366981, by rfl⟩ : syracuseStep 3155975 = 4733963) B4733963
theorem B2103983 : Blo 2103435 2103983 := bstep (se 1 (by rfl) ⟨1577987, by rfl⟩ : syracuseStep 2103983 = 3155975) B3155975
theorem B3155981 : Blo 2103435 3155981 := bbase (se 3 (by rfl) ⟨591746, by rfl⟩ : syracuseStep 3155981 = 1183493) (by norm_num)
theorem B2103987 : Blo 2103435 2103987 := bstep (se 1 (by rfl) ⟨1577990, by rfl⟩ : syracuseStep 2103987 = 3155981) B3155981
theorem B4733981 : Blo 2103435 4733981 := bbase (se 3 (by rfl) ⟨887621, by rfl⟩ : syracuseStep 4733981 = 1775243) (by norm_num)
theorem B3155987 : Blo 2103435 3155987 := bstep (se 1 (by rfl) ⟨2366990, by rfl⟩ : syracuseStep 3155987 = 4733981) B4733981
theorem B2103991 : Blo 2103435 2103991 := bstep (se 1 (by rfl) ⟨1577993, by rfl⟩ : syracuseStep 2103991 = 3155987) B3155987
theorem B3550493 : Blo 2103435 3550493 := bbase (se 3 (by rfl) ⟨665717, by rfl⟩ : syracuseStep 3550493 = 1331435) (by norm_num)
theorem B2366995 : Blo 2103435 2366995 := bstep (se 1 (by rfl) ⟨1775246, by rfl⟩ : syracuseStep 2366995 = 3550493) B3550493
theorem B3155993 : Blo 2103435 3155993 := bstep (se 2 (by rfl) ⟨1183497, by rfl⟩ : syracuseStep 3155993 = 2366995) B2366995
theorem B2103995 : Blo 2103435 2103995 := bstep (se 1 (by rfl) ⟨1577996, by rfl⟩ : syracuseStep 2103995 = 3155993) B3155993
theorem B3791477 : Blo 2103435 3791477 := bbase (se 5 (by rfl) ⟨177725, by rfl⟩ : syracuseStep 3791477 = 355451) (by norm_num)
theorem B2527651 : Blo 2103435 2527651 := bstep (se 1 (by rfl) ⟨1895738, by rfl⟩ : syracuseStep 2527651 = 3791477) B3791477
theorem B13480805 : Blo 2103435 13480805 := bstep (se 4 (by rfl) ⟨1263825, by rfl⟩ : syracuseStep 13480805 = 2527651) B2527651
theorem B8987203 : Blo 2103435 8987203 := bstep (se 1 (by rfl) ⟨6740402, by rfl⟩ : syracuseStep 8987203 = 13480805) B13480805
theorem B11982937 : Blo 2103435 11982937 := bstep (se 2 (by rfl) ⟨4493601, by rfl⟩ : syracuseStep 11982937 = 8987203) B8987203
theorem B15977249 : Blo 2103435 15977249 := bstep (se 2 (by rfl) ⟨5991468, by rfl⟩ : syracuseStep 15977249 = 11982937) B11982937
theorem B10651499 : Blo 2103435 10651499 := bstep (se 1 (by rfl) ⟨7988624, by rfl⟩ : syracuseStep 10651499 = 15977249) B15977249
theorem B7100999 : Blo 2103435 7100999 := bstep (se 1 (by rfl) ⟨5325749, by rfl⟩ : syracuseStep 7100999 = 10651499) B10651499
theorem B4733999 : Blo 2103435 4733999 := bstep (se 1 (by rfl) ⟨3550499, by rfl⟩ : syracuseStep 4733999 = 7100999) B7100999
theorem B3155999 : Blo 2103435 3155999 := bstep (se 1 (by rfl) ⟨2366999, by rfl⟩ : syracuseStep 3155999 = 4733999) B4733999
theorem B2103999 : Blo 2103435 2103999 := bstep (se 1 (by rfl) ⟨1577999, by rfl⟩ : syracuseStep 2103999 = 3155999) B3155999
theorem B3156005 : Blo 2103435 3156005 := bbase (se 4 (by rfl) ⟨295875, by rfl⟩ : syracuseStep 3156005 = 591751) (by norm_num)
theorem B2104003 : Blo 2103435 2104003 := bstep (se 1 (by rfl) ⟨1578002, by rfl⟩ : syracuseStep 2104003 = 3156005) B3156005
theorem B2662885 : Blo 2103435 2662885 := bbase (se 4 (by rfl) ⟨249645, by rfl⟩ : syracuseStep 2662885 = 499291) (by norm_num)
theorem B3550513 : Blo 2103435 3550513 := bstep (se 2 (by rfl) ⟨1331442, by rfl⟩ : syracuseStep 3550513 = 2662885) B2662885
theorem B4734017 : Blo 2103435 4734017 := bstep (se 2 (by rfl) ⟨1775256, by rfl⟩ : syracuseStep 4734017 = 3550513) B3550513
theorem B3156011 : Blo 2103435 3156011 := bstep (se 1 (by rfl) ⟨2367008, by rfl⟩ : syracuseStep 3156011 = 4734017) B4734017
theorem B2104007 : Blo 2103435 2104007 := bstep (se 1 (by rfl) ⟨1578005, by rfl⟩ : syracuseStep 2104007 = 3156011) B3156011
theorem B2367013 : Blo 2103435 2367013 := bbase (se 4 (by rfl) ⟨221907, by rfl⟩ : syracuseStep 2367013 = 443815) (by norm_num)
theorem B3156017 : Blo 2103435 3156017 := bstep (se 2 (by rfl) ⟨1183506, by rfl⟩ : syracuseStep 3156017 = 2367013) B2367013
theorem B2104011 : Blo 2103435 2104011 := bstep (se 1 (by rfl) ⟨1578008, by rfl⟩ : syracuseStep 2104011 = 3156017) B3156017
theorem B6832421 : Blo 2103435 6832421 := bbase (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) (by norm_num)
theorem B4554947 : Blo 2103435 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B3036631 : Blo 2103435 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B4048841 : Blo 2103435 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B2699227 : Blo 2103435 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B14395877 : Blo 2103435 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B9597251 : Blo 2103435 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B25592669 : Blo 2103435 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B17061779 : Blo 2103435 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B11374519 : Blo 2103435 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B15166025 : Blo 2103435 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B10110683 : Blo 2103435 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B6740455 : Blo 2103435 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B8987273 : Blo 2103435 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B5991515 : Blo 2103435 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B3994343 : Blo 2103435 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B2662895 : Blo 2103435 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B7101053 : Blo 2103435 7101053 := bstep (se 3 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 7101053 = 2662895) B2662895
theorem B4734035 : Blo 2103435 4734035 := bstep (se 1 (by rfl) ⟨3550526, by rfl⟩ : syracuseStep 4734035 = 7101053) B7101053
theorem B3156023 : Blo 2103435 3156023 := bstep (se 1 (by rfl) ⟨2367017, by rfl⟩ : syracuseStep 3156023 = 4734035) B4734035
theorem B2104015 : Blo 2103435 2104015 := bstep (se 1 (by rfl) ⟨1578011, by rfl⟩ : syracuseStep 2104015 = 3156023) B3156023
theorem B3156029 : Blo 2103435 3156029 := bbase (se 3 (by rfl) ⟨591755, by rfl⟩ : syracuseStep 3156029 = 1183511) (by norm_num)
theorem B2104019 : Blo 2103435 2104019 := bstep (se 1 (by rfl) ⟨1578014, by rfl⟩ : syracuseStep 2104019 = 3156029) B3156029
theorem B4734053 : Blo 2103435 4734053 := bbase (se 4 (by rfl) ⟨443817, by rfl⟩ : syracuseStep 4734053 = 887635) (by norm_num)
theorem B3156035 : Blo 2103435 3156035 := bstep (se 1 (by rfl) ⟨2367026, by rfl⟩ : syracuseStep 3156035 = 4734053) B4734053
theorem B2104023 : Blo 2103435 2104023 := bstep (se 1 (by rfl) ⟨1578017, by rfl⟩ : syracuseStep 2104023 = 3156035) B3156035
theorem B5325821 : Blo 2103435 5325821 := bbase (se 3 (by rfl) ⟨998591, by rfl⟩ : syracuseStep 5325821 = 1997183) (by norm_num)
theorem B3550547 : Blo 2103435 3550547 := bstep (se 1 (by rfl) ⟨2662910, by rfl⟩ : syracuseStep 3550547 = 5325821) B5325821
theorem B2367031 : Blo 2103435 2367031 := bstep (se 1 (by rfl) ⟨1775273, by rfl⟩ : syracuseStep 2367031 = 3550547) B3550547
theorem B3156041 : Blo 2103435 3156041 := bstep (se 2 (by rfl) ⟨1183515, by rfl⟩ : syracuseStep 3156041 = 2367031) B2367031
theorem B2104027 : Blo 2103435 2104027 := bstep (se 1 (by rfl) ⟨1578020, by rfl⟩ : syracuseStep 2104027 = 3156041) B3156041
theorem B3994373 : Blo 2103435 3994373 := bbase (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) (by norm_num)
theorem B10651661 : Blo 2103435 10651661 := bstep (se 3 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 10651661 = 3994373) B3994373
theorem B7101107 : Blo 2103435 7101107 := bstep (se 1 (by rfl) ⟨5325830, by rfl⟩ : syracuseStep 7101107 = 10651661) B10651661
theorem B4734071 : Blo 2103435 4734071 := bstep (se 1 (by rfl) ⟨3550553, by rfl⟩ : syracuseStep 4734071 = 7101107) B7101107
theorem B3156047 : Blo 2103435 3156047 := bstep (se 1 (by rfl) ⟨2367035, by rfl⟩ : syracuseStep 3156047 = 4734071) B4734071
theorem B2104031 : Blo 2103435 2104031 := bstep (se 1 (by rfl) ⟨1578023, by rfl⟩ : syracuseStep 2104031 = 3156047) B3156047
theorem B3156053 : Blo 2103435 3156053 := bbase (se 8 (by rfl) ⟨18492, by rfl⟩ : syracuseStep 3156053 = 36985) (by norm_num)
theorem B2104035 : Blo 2103435 2104035 := bstep (se 1 (by rfl) ⟨1578026, by rfl⟩ : syracuseStep 2104035 = 3156053) B3156053
theorem B10944341 : Blo 2103435 10944341 := bbase (se 9 (by rfl) ⟨32063, by rfl⟩ : syracuseStep 10944341 = 64127) (by norm_num)
theorem B7296227 : Blo 2103435 7296227 := bstep (se 1 (by rfl) ⟨5472170, by rfl⟩ : syracuseStep 7296227 = 10944341) B10944341
theorem B4864151 : Blo 2103435 4864151 := bstep (se 1 (by rfl) ⟨3648113, by rfl⟩ : syracuseStep 4864151 = 7296227) B7296227
theorem B3242767 : Blo 2103435 3242767 := bstep (se 1 (by rfl) ⟨2432075, by rfl⟩ : syracuseStep 3242767 = 4864151) B4864151
theorem B4323689 : Blo 2103435 4323689 := bstep (se 2 (by rfl) ⟨1621383, by rfl⟩ : syracuseStep 4323689 = 3242767) B3242767
theorem B2882459 : Blo 2103435 2882459 := bstep (se 1 (by rfl) ⟨2161844, by rfl⟩ : syracuseStep 2882459 = 4323689) B4323689
theorem B7686557 : Blo 2103435 7686557 := bstep (se 3 (by rfl) ⟨1441229, by rfl⟩ : syracuseStep 7686557 = 2882459) B2882459
theorem B327959765 : Blo 2103435 327959765 := bstep (se 7 (by rfl) ⟨3843278, by rfl⟩ : syracuseStep 327959765 = 7686557) B7686557
theorem B218639843 : Blo 2103435 218639843 := bstep (se 1 (by rfl) ⟨163979882, by rfl⟩ : syracuseStep 218639843 = 327959765) B327959765
theorem B145759895 : Blo 2103435 145759895 := bstep (se 1 (by rfl) ⟨109319921, by rfl⟩ : syracuseStep 145759895 = 218639843) B218639843
theorem B97173263 : Blo 2103435 97173263 := bstep (se 1 (by rfl) ⟨72879947, by rfl⟩ : syracuseStep 97173263 = 145759895) B145759895
theorem B64782175 : Blo 2103435 64782175 := bstep (se 1 (by rfl) ⟨48586631, by rfl⟩ : syracuseStep 64782175 = 97173263) B97173263
theorem B86376233 : Blo 2103435 86376233 := bstep (se 2 (by rfl) ⟨32391087, by rfl⟩ : syracuseStep 86376233 = 64782175) B64782175
theorem B57584155 : Blo 2103435 57584155 := bstep (se 1 (by rfl) ⟨43188116, by rfl⟩ : syracuseStep 57584155 = 86376233) B86376233
theorem B76778873 : Blo 2103435 76778873 := bstep (se 2 (by rfl) ⟨28792077, by rfl⟩ : syracuseStep 76778873 = 57584155) B57584155
theorem B51185915 : Blo 2103435 51185915 := bstep (se 1 (by rfl) ⟨38389436, by rfl⟩ : syracuseStep 51185915 = 76778873) B76778873
theorem B34123943 : Blo 2103435 34123943 := bstep (se 1 (by rfl) ⟨25592957, by rfl⟩ : syracuseStep 34123943 = 51185915) B51185915
theorem B22749295 : Blo 2103435 22749295 := bstep (se 1 (by rfl) ⟨17061971, by rfl⟩ : syracuseStep 22749295 = 34123943) B34123943
theorem B30332393 : Blo 2103435 30332393 := bstep (se 2 (by rfl) ⟨11374647, by rfl⟩ : syracuseStep 30332393 = 22749295) B22749295
theorem B20221595 : Blo 2103435 20221595 := bstep (se 1 (by rfl) ⟨15166196, by rfl⟩ : syracuseStep 20221595 = 30332393) B30332393
theorem B13481063 : Blo 2103435 13481063 := bstep (se 1 (by rfl) ⟨10110797, by rfl⟩ : syracuseStep 13481063 = 20221595) B20221595
theorem B8987375 : Blo 2103435 8987375 := bstep (se 1 (by rfl) ⟨6740531, by rfl⟩ : syracuseStep 8987375 = 13481063) B13481063
theorem B5991583 : Blo 2103435 5991583 := bstep (se 1 (by rfl) ⟨4493687, by rfl⟩ : syracuseStep 5991583 = 8987375) B8987375
theorem B7988777 : Blo 2103435 7988777 := bstep (se 2 (by rfl) ⟨2995791, by rfl⟩ : syracuseStep 7988777 = 5991583) B5991583
theorem B5325851 : Blo 2103435 5325851 := bstep (se 1 (by rfl) ⟨3994388, by rfl⟩ : syracuseStep 5325851 = 7988777) B7988777
theorem B3550567 : Blo 2103435 3550567 := bstep (se 1 (by rfl) ⟨2662925, by rfl⟩ : syracuseStep 3550567 = 5325851) B5325851
theorem B4734089 : Blo 2103435 4734089 := bstep (se 2 (by rfl) ⟨1775283, by rfl⟩ : syracuseStep 4734089 = 3550567) B3550567
theorem B3156059 : Blo 2103435 3156059 := bstep (se 1 (by rfl) ⟨2367044, by rfl⟩ : syracuseStep 3156059 = 4734089) B4734089
theorem B2104039 : Blo 2103435 2104039 := bstep (se 1 (by rfl) ⟨1578029, by rfl⟩ : syracuseStep 2104039 = 3156059) B3156059
theorem B2367049 : Blo 2103435 2367049 := bbase (se 2 (by rfl) ⟨887643, by rfl⟩ : syracuseStep 2367049 = 1775287) (by norm_num)
theorem B3156065 : Blo 2103435 3156065 := bstep (se 2 (by rfl) ⟨1183524, by rfl⟩ : syracuseStep 3156065 = 2367049) B2367049
theorem B2104043 : Blo 2103435 2104043 := bstep (se 1 (by rfl) ⟨1578032, by rfl⟩ : syracuseStep 2104043 = 3156065) B3156065
theorem B4265509 : Blo 2103435 4265509 := bbase (se 4 (by rfl) ⟨399891, by rfl⟩ : syracuseStep 4265509 = 799783) (by norm_num)
theorem B5687345 : Blo 2103435 5687345 := bstep (se 2 (by rfl) ⟨2132754, by rfl⟩ : syracuseStep 5687345 = 4265509) B4265509
theorem B15166253 : Blo 2103435 15166253 := bstep (se 3 (by rfl) ⟨2843672, by rfl⟩ : syracuseStep 15166253 = 5687345) B5687345
theorem B10110835 : Blo 2103435 10110835 := bstep (se 1 (by rfl) ⟨7583126, by rfl⟩ : syracuseStep 10110835 = 15166253) B15166253
theorem B13481113 : Blo 2103435 13481113 := bstep (se 2 (by rfl) ⟨5055417, by rfl⟩ : syracuseStep 13481113 = 10110835) B10110835
theorem B17974817 : Blo 2103435 17974817 := bstep (se 2 (by rfl) ⟨6740556, by rfl⟩ : syracuseStep 17974817 = 13481113) B13481113
theorem B11983211 : Blo 2103435 11983211 := bstep (se 1 (by rfl) ⟨8987408, by rfl⟩ : syracuseStep 11983211 = 17974817) B17974817
theorem B7988807 : Blo 2103435 7988807 := bstep (se 1 (by rfl) ⟨5991605, by rfl⟩ : syracuseStep 7988807 = 11983211) B11983211
theorem B5325871 : Blo 2103435 5325871 := bstep (se 1 (by rfl) ⟨3994403, by rfl⟩ : syracuseStep 5325871 = 7988807) B7988807
theorem B7101161 : Blo 2103435 7101161 := bstep (se 2 (by rfl) ⟨2662935, by rfl⟩ : syracuseStep 7101161 = 5325871) B5325871
theorem B4734107 : Blo 2103435 4734107 := bstep (se 1 (by rfl) ⟨3550580, by rfl⟩ : syracuseStep 4734107 = 7101161) B7101161
theorem B3156071 : Blo 2103435 3156071 := bstep (se 1 (by rfl) ⟨2367053, by rfl⟩ : syracuseStep 3156071 = 4734107) B4734107
theorem B2104047 : Blo 2103435 2104047 := bstep (se 1 (by rfl) ⟨1578035, by rfl⟩ : syracuseStep 2104047 = 3156071) B3156071
theorem B3156077 : Blo 2103435 3156077 := bbase (se 3 (by rfl) ⟨591764, by rfl⟩ : syracuseStep 3156077 = 1183529) (by norm_num)
theorem B2104051 : Blo 2103435 2104051 := bstep (se 1 (by rfl) ⟨1578038, by rfl⟩ : syracuseStep 2104051 = 3156077) B3156077
theorem B4734125 : Blo 2103435 4734125 := bbase (se 3 (by rfl) ⟨887648, by rfl⟩ : syracuseStep 4734125 = 1775297) (by norm_num)
theorem B3156083 : Blo 2103435 3156083 := bstep (se 1 (by rfl) ⟨2367062, by rfl⟩ : syracuseStep 3156083 = 4734125) B4734125
theorem B2104055 : Blo 2103435 2104055 := bstep (se 1 (by rfl) ⟨1578041, by rfl⟩ : syracuseStep 2104055 = 3156083) B3156083
theorem B6740597 : Blo 2103435 6740597 := bbase (se 5 (by rfl) ⟨315965, by rfl⟩ : syracuseStep 6740597 = 631931) (by norm_num)
theorem B4493731 : Blo 2103435 4493731 := bstep (se 1 (by rfl) ⟨3370298, by rfl⟩ : syracuseStep 4493731 = 6740597) B6740597
theorem B5991641 : Blo 2103435 5991641 := bstep (se 2 (by rfl) ⟨2246865, by rfl⟩ : syracuseStep 5991641 = 4493731) B4493731
theorem B3994427 : Blo 2103435 3994427 := bstep (se 1 (by rfl) ⟨2995820, by rfl⟩ : syracuseStep 3994427 = 5991641) B5991641
theorem B2662951 : Blo 2103435 2662951 := bstep (se 1 (by rfl) ⟨1997213, by rfl⟩ : syracuseStep 2662951 = 3994427) B3994427
theorem B3550601 : Blo 2103435 3550601 := bstep (se 2 (by rfl) ⟨1331475, by rfl⟩ : syracuseStep 3550601 = 2662951) B2662951
theorem B2367067 : Blo 2103435 2367067 := bstep (se 1 (by rfl) ⟨1775300, by rfl⟩ : syracuseStep 2367067 = 3550601) B3550601
theorem B3156089 : Blo 2103435 3156089 := bstep (se 2 (by rfl) ⟨1183533, by rfl⟩ : syracuseStep 3156089 = 2367067) B2367067
theorem B2104059 : Blo 2103435 2104059 := bstep (se 1 (by rfl) ⟨1578044, by rfl⟩ : syracuseStep 2104059 = 3156089) B3156089
theorem B14993525 : Blo 2103435 14993525 := bbase (se 5 (by rfl) ⟨702821, by rfl⟩ : syracuseStep 14993525 = 1405643) (by norm_num)
theorem B39982733 : Blo 2103435 39982733 := bstep (se 3 (by rfl) ⟨7496762, by rfl⟩ : syracuseStep 39982733 = 14993525) B14993525
theorem B26655155 : Blo 2103435 26655155 := bstep (se 1 (by rfl) ⟨19991366, by rfl⟩ : syracuseStep 26655155 = 39982733) B39982733
theorem B17770103 : Blo 2103435 17770103 := bstep (se 1 (by rfl) ⟨13327577, by rfl⟩ : syracuseStep 17770103 = 26655155) B26655155
theorem B11846735 : Blo 2103435 11846735 := bstep (se 1 (by rfl) ⟨8885051, by rfl⟩ : syracuseStep 11846735 = 17770103) B17770103
theorem B7897823 : Blo 2103435 7897823 := bstep (se 1 (by rfl) ⟨5923367, by rfl⟩ : syracuseStep 7897823 = 11846735) B11846735
theorem B5265215 : Blo 2103435 5265215 := bstep (se 1 (by rfl) ⟨3948911, by rfl⟩ : syracuseStep 5265215 = 7897823) B7897823
theorem B3510143 : Blo 2103435 3510143 := bstep (se 1 (by rfl) ⟨2632607, by rfl⟩ : syracuseStep 3510143 = 5265215) B5265215
theorem B2340095 : Blo 2103435 2340095 := bstep (se 1 (by rfl) ⟨1755071, by rfl⟩ : syracuseStep 2340095 = 3510143) B3510143
theorem B6240253 : Blo 2103435 6240253 := bstep (se 3 (by rfl) ⟨1170047, by rfl⟩ : syracuseStep 6240253 = 2340095) B2340095
theorem B8320337 : Blo 2103435 8320337 := bstep (se 2 (by rfl) ⟨3120126, by rfl⟩ : syracuseStep 8320337 = 6240253) B6240253
theorem B5546891 : Blo 2103435 5546891 := bstep (se 1 (by rfl) ⟨4160168, by rfl⟩ : syracuseStep 5546891 = 8320337) B8320337
theorem B14791709 : Blo 2103435 14791709 := bstep (se 3 (by rfl) ⟨2773445, by rfl⟩ : syracuseStep 14791709 = 5546891) B5546891
theorem B9861139 : Blo 2103435 9861139 := bstep (se 1 (by rfl) ⟨7395854, by rfl⟩ : syracuseStep 9861139 = 14791709) B14791709
theorem B13148185 : Blo 2103435 13148185 := bstep (se 2 (by rfl) ⟨4930569, by rfl⟩ : syracuseStep 13148185 = 9861139) B9861139
theorem B17530913 : Blo 2103435 17530913 := bstep (se 2 (by rfl) ⟨6574092, by rfl⟩ : syracuseStep 17530913 = 13148185) B13148185
theorem B11687275 : Blo 2103435 11687275 := bstep (se 1 (by rfl) ⟨8765456, by rfl⟩ : syracuseStep 11687275 = 17530913) B17530913
theorem B15583033 : Blo 2103435 15583033 := bstep (se 2 (by rfl) ⟨5843637, by rfl⟩ : syracuseStep 15583033 = 11687275) B11687275
theorem B83109509 : Blo 2103435 83109509 := bstep (se 4 (by rfl) ⟨7791516, by rfl⟩ : syracuseStep 83109509 = 15583033) B15583033
theorem B55406339 : Blo 2103435 55406339 := bstep (se 1 (by rfl) ⟨41554754, by rfl⟩ : syracuseStep 55406339 = 83109509) B83109509
theorem B36937559 : Blo 2103435 36937559 := bstep (se 1 (by rfl) ⟨27703169, by rfl⟩ : syracuseStep 36937559 = 55406339) B55406339
theorem B98500157 : Blo 2103435 98500157 := bstep (se 3 (by rfl) ⟨18468779, by rfl⟩ : syracuseStep 98500157 = 36937559) B36937559
theorem B65666771 : Blo 2103435 65666771 := bstep (se 1 (by rfl) ⟨49250078, by rfl⟩ : syracuseStep 65666771 = 98500157) B98500157
theorem B43777847 : Blo 2103435 43777847 := bstep (se 1 (by rfl) ⟨32833385, by rfl⟩ : syracuseStep 43777847 = 65666771) B65666771
theorem B29185231 : Blo 2103435 29185231 := bstep (se 1 (by rfl) ⟨21888923, by rfl⟩ : syracuseStep 29185231 = 43777847) B43777847
theorem B38913641 : Blo 2103435 38913641 := bstep (se 2 (by rfl) ⟨14592615, by rfl⟩ : syracuseStep 38913641 = 29185231) B29185231
theorem B25942427 : Blo 2103435 25942427 := bstep (se 1 (by rfl) ⟨19456820, by rfl⟩ : syracuseStep 25942427 = 38913641) B38913641
theorem B17294951 : Blo 2103435 17294951 := bstep (se 1 (by rfl) ⟨12971213, by rfl⟩ : syracuseStep 17294951 = 25942427) B25942427
theorem B11529967 : Blo 2103435 11529967 := bstep (se 1 (by rfl) ⟨8647475, by rfl⟩ : syracuseStep 11529967 = 17294951) B17294951
theorem B15373289 : Blo 2103435 15373289 := bstep (se 2 (by rfl) ⟨5764983, by rfl⟩ : syracuseStep 15373289 = 11529967) B11529967
theorem B10248859 : Blo 2103435 10248859 := bstep (se 1 (by rfl) ⟨7686644, by rfl⟩ : syracuseStep 10248859 = 15373289) B15373289
theorem B13665145 : Blo 2103435 13665145 := bstep (se 2 (by rfl) ⟨5124429, by rfl⟩ : syracuseStep 13665145 = 10248859) B10248859
theorem B18220193 : Blo 2103435 18220193 := bstep (se 2 (by rfl) ⟨6832572, by rfl⟩ : syracuseStep 18220193 = 13665145) B13665145
theorem B12146795 : Blo 2103435 12146795 := bstep (se 1 (by rfl) ⟨9110096, by rfl⟩ : syracuseStep 12146795 = 18220193) B18220193
theorem B8097863 : Blo 2103435 8097863 := bstep (se 1 (by rfl) ⟨6073397, by rfl⟩ : syracuseStep 8097863 = 12146795) B12146795
theorem B86377205 : Blo 2103435 86377205 := bstep (se 5 (by rfl) ⟨4048931, by rfl⟩ : syracuseStep 86377205 = 8097863) B8097863
theorem B57584803 : Blo 2103435 57584803 := bstep (se 1 (by rfl) ⟨43188602, by rfl⟩ : syracuseStep 57584803 = 86377205) B86377205
theorem B76779737 : Blo 2103435 76779737 := bstep (se 2 (by rfl) ⟨28792401, by rfl⟩ : syracuseStep 76779737 = 57584803) B57584803
theorem B51186491 : Blo 2103435 51186491 := bstep (se 1 (by rfl) ⟨38389868, by rfl⟩ : syracuseStep 51186491 = 76779737) B76779737
theorem B34124327 : Blo 2103435 34124327 := bstep (se 1 (by rfl) ⟨25593245, by rfl⟩ : syracuseStep 34124327 = 51186491) B51186491
theorem B22749551 : Blo 2103435 22749551 := bstep (se 1 (by rfl) ⟨17062163, by rfl⟩ : syracuseStep 22749551 = 34124327) B34124327
theorem B15166367 : Blo 2103435 15166367 := bstep (se 1 (by rfl) ⟨11374775, by rfl⟩ : syracuseStep 15166367 = 22749551) B22749551
theorem B10110911 : Blo 2103435 10110911 := bstep (se 1 (by rfl) ⟨7583183, by rfl⟩ : syracuseStep 10110911 = 15166367) B15166367
theorem B26962429 : Blo 2103435 26962429 := bstep (se 3 (by rfl) ⟨5055455, by rfl⟩ : syracuseStep 26962429 = 10110911) B10110911
theorem B35949905 : Blo 2103435 35949905 := bstep (se 2 (by rfl) ⟨13481214, by rfl⟩ : syracuseStep 35949905 = 26962429) B26962429
theorem B23966603 : Blo 2103435 23966603 := bstep (se 1 (by rfl) ⟨17974952, by rfl⟩ : syracuseStep 23966603 = 35949905) B35949905
theorem B15977735 : Blo 2103435 15977735 := bstep (se 1 (by rfl) ⟨11983301, by rfl⟩ : syracuseStep 15977735 = 23966603) B23966603
theorem B10651823 : Blo 2103435 10651823 := bstep (se 1 (by rfl) ⟨7988867, by rfl⟩ : syracuseStep 10651823 = 15977735) B15977735
theorem B7101215 : Blo 2103435 7101215 := bstep (se 1 (by rfl) ⟨5325911, by rfl⟩ : syracuseStep 7101215 = 10651823) B10651823
theorem B4734143 : Blo 2103435 4734143 := bstep (se 1 (by rfl) ⟨3550607, by rfl⟩ : syracuseStep 4734143 = 7101215) B7101215
theorem B3156095 : Blo 2103435 3156095 := bstep (se 1 (by rfl) ⟨2367071, by rfl⟩ : syracuseStep 3156095 = 4734143) B4734143
theorem B2104063 : Blo 2103435 2104063 := bstep (se 1 (by rfl) ⟨1578047, by rfl⟩ : syracuseStep 2104063 = 3156095) B3156095
theorem B3156101 : Blo 2103435 3156101 := bbase (se 4 (by rfl) ⟨295884, by rfl⟩ : syracuseStep 3156101 = 591769) (by norm_num)
theorem B2104067 : Blo 2103435 2104067 := bstep (se 1 (by rfl) ⟨1578050, by rfl⟩ : syracuseStep 2104067 = 3156101) B3156101
theorem B3550621 : Blo 2103435 3550621 := bbase (se 3 (by rfl) ⟨665741, by rfl⟩ : syracuseStep 3550621 = 1331483) (by norm_num)
theorem B4734161 : Blo 2103435 4734161 := bstep (se 2 (by rfl) ⟨1775310, by rfl⟩ : syracuseStep 4734161 = 3550621) B3550621
theorem B3156107 : Blo 2103435 3156107 := bstep (se 1 (by rfl) ⟨2367080, by rfl⟩ : syracuseStep 3156107 = 4734161) B4734161
theorem B2104071 : Blo 2103435 2104071 := bstep (se 1 (by rfl) ⟨1578053, by rfl⟩ : syracuseStep 2104071 = 3156107) B3156107
theorem B2367085 : Blo 2103435 2367085 := bbase (se 3 (by rfl) ⟨443828, by rfl⟩ : syracuseStep 2367085 = 887657) (by norm_num)
theorem B3156113 : Blo 2103435 3156113 := bstep (se 2 (by rfl) ⟨1183542, by rfl⟩ : syracuseStep 3156113 = 2367085) B2367085
theorem B2104075 : Blo 2103435 2104075 := bstep (se 1 (by rfl) ⟨1578056, by rfl⟩ : syracuseStep 2104075 = 3156113) B3156113
theorem B7101269 : Blo 2103435 7101269 := bbase (se 9 (by rfl) ⟨20804, by rfl⟩ : syracuseStep 7101269 = 41609) (by norm_num)
theorem B4734179 : Blo 2103435 4734179 := bstep (se 1 (by rfl) ⟨3550634, by rfl⟩ : syracuseStep 4734179 = 7101269) B7101269
theorem B3156119 : Blo 2103435 3156119 := bstep (se 1 (by rfl) ⟨2367089, by rfl⟩ : syracuseStep 3156119 = 4734179) B4734179
theorem B2104079 : Blo 2103435 2104079 := bstep (se 1 (by rfl) ⟨1578059, by rfl⟩ : syracuseStep 2104079 = 3156119) B3156119
theorem B3156125 : Blo 2103435 3156125 := bbase (se 3 (by rfl) ⟨591773, by rfl⟩ : syracuseStep 3156125 = 1183547) (by norm_num)
theorem B2104083 : Blo 2103435 2104083 := bstep (se 1 (by rfl) ⟨1578062, by rfl⟩ : syracuseStep 2104083 = 3156125) B3156125
theorem B4734197 : Blo 2103435 4734197 := bbase (se 5 (by rfl) ⟨221915, by rfl⟩ : syracuseStep 4734197 = 443831) (by norm_num)
theorem B3156131 : Blo 2103435 3156131 := bstep (se 1 (by rfl) ⟨2367098, by rfl⟩ : syracuseStep 3156131 = 4734197) B4734197
theorem B2104087 : Blo 2103435 2104087 := bstep (se 1 (by rfl) ⟨1578065, by rfl⟩ : syracuseStep 2104087 = 3156131) B3156131
theorem B40995989 : Blo 2103435 40995989 := bbase (se 6 (by rfl) ⟨960843, by rfl⟩ : syracuseStep 40995989 = 1921687) (by norm_num)
theorem B27330659 : Blo 2103435 27330659 := bstep (se 1 (by rfl) ⟨20497994, by rfl⟩ : syracuseStep 27330659 = 40995989) B40995989
theorem B18220439 : Blo 2103435 18220439 := bstep (se 1 (by rfl) ⟨13665329, by rfl⟩ : syracuseStep 18220439 = 27330659) B27330659
theorem B12146959 : Blo 2103435 12146959 := bstep (se 1 (by rfl) ⟨9110219, by rfl⟩ : syracuseStep 12146959 = 18220439) B18220439
theorem B16195945 : Blo 2103435 16195945 := bstep (se 2 (by rfl) ⟨6073479, by rfl⟩ : syracuseStep 16195945 = 12146959) B12146959
theorem B21594593 : Blo 2103435 21594593 := bstep (se 2 (by rfl) ⟨8097972, by rfl⟩ : syracuseStep 21594593 = 16195945) B16195945
theorem B14396395 : Blo 2103435 14396395 := bstep (se 1 (by rfl) ⟨10797296, by rfl⟩ : syracuseStep 14396395 = 21594593) B21594593
theorem B19195193 : Blo 2103435 19195193 := bstep (se 2 (by rfl) ⟨7198197, by rfl⟩ : syracuseStep 19195193 = 14396395) B14396395
theorem B12796795 : Blo 2103435 12796795 := bstep (se 1 (by rfl) ⟨9597596, by rfl⟩ : syracuseStep 12796795 = 19195193) B19195193
theorem B68249573 : Blo 2103435 68249573 := bstep (se 4 (by rfl) ⟨6398397, by rfl⟩ : syracuseStep 68249573 = 12796795) B12796795
theorem B45499715 : Blo 2103435 45499715 := bstep (se 1 (by rfl) ⟨34124786, by rfl⟩ : syracuseStep 45499715 = 68249573) B68249573
theorem B30333143 : Blo 2103435 30333143 := bstep (se 1 (by rfl) ⟨22749857, by rfl⟩ : syracuseStep 30333143 = 45499715) B45499715
theorem B20222095 : Blo 2103435 20222095 := bstep (se 1 (by rfl) ⟨15166571, by rfl⟩ : syracuseStep 20222095 = 30333143) B30333143
theorem B26962793 : Blo 2103435 26962793 := bstep (se 2 (by rfl) ⟨10111047, by rfl⟩ : syracuseStep 26962793 = 20222095) B20222095
theorem B17975195 : Blo 2103435 17975195 := bstep (se 1 (by rfl) ⟨13481396, by rfl⟩ : syracuseStep 17975195 = 26962793) B26962793
theorem B11983463 : Blo 2103435 11983463 := bstep (se 1 (by rfl) ⟨8987597, by rfl⟩ : syracuseStep 11983463 = 17975195) B17975195
theorem B7988975 : Blo 2103435 7988975 := bstep (se 1 (by rfl) ⟨5991731, by rfl⟩ : syracuseStep 7988975 = 11983463) B11983463
theorem B5325983 : Blo 2103435 5325983 := bstep (se 1 (by rfl) ⟨3994487, by rfl⟩ : syracuseStep 5325983 = 7988975) B7988975
theorem B3550655 : Blo 2103435 3550655 := bstep (se 1 (by rfl) ⟨2662991, by rfl⟩ : syracuseStep 3550655 = 5325983) B5325983
theorem B2367103 : Blo 2103435 2367103 := bstep (se 1 (by rfl) ⟨1775327, by rfl⟩ : syracuseStep 2367103 = 3550655) B3550655
theorem B3156137 : Blo 2103435 3156137 := bstep (se 2 (by rfl) ⟨1183551, by rfl⟩ : syracuseStep 3156137 = 2367103) B2367103
theorem B2104091 : Blo 2103435 2104091 := bstep (se 1 (by rfl) ⟨1578068, by rfl⟩ : syracuseStep 2104091 = 3156137) B3156137
theorem B5124509 : Blo 2103435 5124509 := bbase (se 3 (by rfl) ⟨960845, by rfl⟩ : syracuseStep 5124509 = 1921691) (by norm_num)
theorem B3416339 : Blo 2103435 3416339 := bstep (se 1 (by rfl) ⟨2562254, by rfl⟩ : syracuseStep 3416339 = 5124509) B5124509
theorem B9110237 : Blo 2103435 9110237 := bstep (se 3 (by rfl) ⟨1708169, by rfl⟩ : syracuseStep 9110237 = 3416339) B3416339
theorem B97175861 : Blo 2103435 97175861 := bstep (se 5 (by rfl) ⟨4555118, by rfl⟩ : syracuseStep 97175861 = 9110237) B9110237
theorem B64783907 : Blo 2103435 64783907 := bstep (se 1 (by rfl) ⟨48587930, by rfl⟩ : syracuseStep 64783907 = 97175861) B97175861
theorem B43189271 : Blo 2103435 43189271 := bstep (se 1 (by rfl) ⟨32391953, by rfl⟩ : syracuseStep 43189271 = 64783907) B64783907
theorem B28792847 : Blo 2103435 28792847 := bstep (se 1 (by rfl) ⟨21594635, by rfl⟩ : syracuseStep 28792847 = 43189271) B43189271
theorem B19195231 : Blo 2103435 19195231 := bstep (se 1 (by rfl) ⟨14396423, by rfl⟩ : syracuseStep 19195231 = 28792847) B28792847
theorem B25593641 : Blo 2103435 25593641 := bstep (se 2 (by rfl) ⟨9597615, by rfl⟩ : syracuseStep 25593641 = 19195231) B19195231
theorem B17062427 : Blo 2103435 17062427 := bstep (se 1 (by rfl) ⟨12796820, by rfl⟩ : syracuseStep 17062427 = 25593641) B25593641
theorem B11374951 : Blo 2103435 11374951 := bstep (se 1 (by rfl) ⟨8531213, by rfl⟩ : syracuseStep 11374951 = 17062427) B17062427
theorem B15166601 : Blo 2103435 15166601 := bstep (se 2 (by rfl) ⟨5687475, by rfl⟩ : syracuseStep 15166601 = 11374951) B11374951
theorem B10111067 : Blo 2103435 10111067 := bstep (se 1 (by rfl) ⟨7583300, by rfl⟩ : syracuseStep 10111067 = 15166601) B15166601
theorem B6740711 : Blo 2103435 6740711 := bstep (se 1 (by rfl) ⟨5055533, by rfl⟩ : syracuseStep 6740711 = 10111067) B10111067
theorem B4493807 : Blo 2103435 4493807 := bstep (se 1 (by rfl) ⟨3370355, by rfl⟩ : syracuseStep 4493807 = 6740711) B6740711
theorem B2995871 : Blo 2103435 2995871 := bstep (se 1 (by rfl) ⟨2246903, by rfl⟩ : syracuseStep 2995871 = 4493807) B4493807
theorem B7988989 : Blo 2103435 7988989 := bstep (se 3 (by rfl) ⟨1497935, by rfl⟩ : syracuseStep 7988989 = 2995871) B2995871
theorem B10651985 : Blo 2103435 10651985 := bstep (se 2 (by rfl) ⟨3994494, by rfl⟩ : syracuseStep 10651985 = 7988989) B7988989
theorem B7101323 : Blo 2103435 7101323 := bstep (se 1 (by rfl) ⟨5325992, by rfl⟩ : syracuseStep 7101323 = 10651985) B10651985
theorem B4734215 : Blo 2103435 4734215 := bstep (se 1 (by rfl) ⟨3550661, by rfl⟩ : syracuseStep 4734215 = 7101323) B7101323
theorem B3156143 : Blo 2103435 3156143 := bstep (se 1 (by rfl) ⟨2367107, by rfl⟩ : syracuseStep 3156143 = 4734215) B4734215
theorem B2104095 : Blo 2103435 2104095 := bstep (se 1 (by rfl) ⟨1578071, by rfl⟩ : syracuseStep 2104095 = 3156143) B3156143
theorem B3156149 : Blo 2103435 3156149 := bbase (se 5 (by rfl) ⟨147944, by rfl⟩ : syracuseStep 3156149 = 295889) (by norm_num)
theorem B2104099 : Blo 2103435 2104099 := bstep (se 1 (by rfl) ⟨1578074, by rfl⟩ : syracuseStep 2104099 = 3156149) B3156149
theorem B5326013 : Blo 2103435 5326013 := bbase (se 3 (by rfl) ⟨998627, by rfl⟩ : syracuseStep 5326013 = 1997255) (by norm_num)
theorem B3550675 : Blo 2103435 3550675 := bstep (se 1 (by rfl) ⟨2663006, by rfl⟩ : syracuseStep 3550675 = 5326013) B5326013
theorem B4734233 : Blo 2103435 4734233 := bstep (se 2 (by rfl) ⟨1775337, by rfl⟩ : syracuseStep 4734233 = 3550675) B3550675
theorem B3156155 : Blo 2103435 3156155 := bstep (se 1 (by rfl) ⟨2367116, by rfl⟩ : syracuseStep 3156155 = 4734233) B4734233
theorem B2104103 : Blo 2103435 2104103 := bstep (se 1 (by rfl) ⟨1578077, by rfl⟩ : syracuseStep 2104103 = 3156155) B3156155
theorem B2367121 : Blo 2103435 2367121 := bbase (se 2 (by rfl) ⟨887670, by rfl⟩ : syracuseStep 2367121 = 1775341) (by norm_num)
theorem B3156161 : Blo 2103435 3156161 := bstep (se 2 (by rfl) ⟨1183560, by rfl⟩ : syracuseStep 3156161 = 2367121) B2367121
theorem B2104107 : Blo 2103435 2104107 := bstep (se 1 (by rfl) ⟨1578080, by rfl⟩ : syracuseStep 2104107 = 3156161) B3156161
theorem B3994525 : Blo 2103435 3994525 := bbase (se 3 (by rfl) ⟨748973, by rfl⟩ : syracuseStep 3994525 = 1497947) (by norm_num)
theorem B5326033 : Blo 2103435 5326033 := bstep (se 2 (by rfl) ⟨1997262, by rfl⟩ : syracuseStep 5326033 = 3994525) B3994525
theorem B7101377 : Blo 2103435 7101377 := bstep (se 2 (by rfl) ⟨2663016, by rfl⟩ : syracuseStep 7101377 = 5326033) B5326033
theorem B4734251 : Blo 2103435 4734251 := bstep (se 1 (by rfl) ⟨3550688, by rfl⟩ : syracuseStep 4734251 = 7101377) B7101377
theorem B3156167 : Blo 2103435 3156167 := bstep (se 1 (by rfl) ⟨2367125, by rfl⟩ : syracuseStep 3156167 = 4734251) B4734251
theorem B2104111 : Blo 2103435 2104111 := bstep (se 1 (by rfl) ⟨1578083, by rfl⟩ : syracuseStep 2104111 = 3156167) B3156167
theorem B3156173 : Blo 2103435 3156173 := bbase (se 3 (by rfl) ⟨591782, by rfl⟩ : syracuseStep 3156173 = 1183565) (by norm_num)
theorem B2104115 : Blo 2103435 2104115 := bstep (se 1 (by rfl) ⟨1578086, by rfl⟩ : syracuseStep 2104115 = 3156173) B3156173
theorem B4734269 : Blo 2103435 4734269 := bbase (se 3 (by rfl) ⟨887675, by rfl⟩ : syracuseStep 4734269 = 1775351) (by norm_num)
theorem B3156179 : Blo 2103435 3156179 := bstep (se 1 (by rfl) ⟨2367134, by rfl⟩ : syracuseStep 3156179 = 4734269) B4734269
theorem B2104119 : Blo 2103435 2104119 := bstep (se 1 (by rfl) ⟨1578089, by rfl⟩ : syracuseStep 2104119 = 3156179) B3156179
theorem B3550709 : Blo 2103435 3550709 := bbase (se 5 (by rfl) ⟨166439, by rfl⟩ : syracuseStep 3550709 = 332879) (by norm_num)
theorem B2367139 : Blo 2103435 2367139 := bstep (se 1 (by rfl) ⟨1775354, by rfl⟩ : syracuseStep 2367139 = 3550709) B3550709
theorem B3156185 : Blo 2103435 3156185 := bstep (se 2 (by rfl) ⟨1183569, by rfl⟩ : syracuseStep 3156185 = 2367139) B2367139
theorem B2104123 : Blo 2103435 2104123 := bstep (se 1 (by rfl) ⟨1578092, by rfl⟩ : syracuseStep 2104123 = 3156185) B3156185
theorem B2527805 : Blo 2103435 2527805 := bbase (se 3 (by rfl) ⟨473963, by rfl⟩ : syracuseStep 2527805 = 947927) (by norm_num)
theorem B6740813 : Blo 2103435 6740813 := bstep (se 3 (by rfl) ⟨1263902, by rfl⟩ : syracuseStep 6740813 = 2527805) B2527805
theorem B4493875 : Blo 2103435 4493875 := bstep (se 1 (by rfl) ⟨3370406, by rfl⟩ : syracuseStep 4493875 = 6740813) B6740813
theorem B5991833 : Blo 2103435 5991833 := bstep (se 2 (by rfl) ⟨2246937, by rfl⟩ : syracuseStep 5991833 = 4493875) B4493875
theorem B15978221 : Blo 2103435 15978221 := bstep (se 3 (by rfl) ⟨2995916, by rfl⟩ : syracuseStep 15978221 = 5991833) B5991833
theorem B10652147 : Blo 2103435 10652147 := bstep (se 1 (by rfl) ⟨7989110, by rfl⟩ : syracuseStep 10652147 = 15978221) B15978221
theorem B7101431 : Blo 2103435 7101431 := bstep (se 1 (by rfl) ⟨5326073, by rfl⟩ : syracuseStep 7101431 = 10652147) B10652147
theorem B4734287 : Blo 2103435 4734287 := bstep (se 1 (by rfl) ⟨3550715, by rfl⟩ : syracuseStep 4734287 = 7101431) B7101431
theorem B3156191 : Blo 2103435 3156191 := bstep (se 1 (by rfl) ⟨2367143, by rfl⟩ : syracuseStep 3156191 = 4734287) B4734287
theorem B2104127 : Blo 2103435 2104127 := bstep (se 1 (by rfl) ⟨1578095, by rfl⟩ : syracuseStep 2104127 = 3156191) B3156191
theorem B3156197 : Blo 2103435 3156197 := bbase (se 4 (by rfl) ⟨295893, by rfl⟩ : syracuseStep 3156197 = 591787) (by norm_num)
theorem B2104131 : Blo 2103435 2104131 := bstep (se 1 (by rfl) ⟨1578098, by rfl⟩ : syracuseStep 2104131 = 3156197) B3156197
theorem B4493893 : Blo 2103435 4493893 := bbase (se 4 (by rfl) ⟨421302, by rfl⟩ : syracuseStep 4493893 = 842605) (by norm_num)
theorem B5991857 : Blo 2103435 5991857 := bstep (se 2 (by rfl) ⟨2246946, by rfl⟩ : syracuseStep 5991857 = 4493893) B4493893
theorem B3994571 : Blo 2103435 3994571 := bstep (se 1 (by rfl) ⟨2995928, by rfl⟩ : syracuseStep 3994571 = 5991857) B5991857
theorem B2663047 : Blo 2103435 2663047 := bstep (se 1 (by rfl) ⟨1997285, by rfl⟩ : syracuseStep 2663047 = 3994571) B3994571
theorem B3550729 : Blo 2103435 3550729 := bstep (se 2 (by rfl) ⟨1331523, by rfl⟩ : syracuseStep 3550729 = 2663047) B2663047
theorem B4734305 : Blo 2103435 4734305 := bstep (se 2 (by rfl) ⟨1775364, by rfl⟩ : syracuseStep 4734305 = 3550729) B3550729
theorem B3156203 : Blo 2103435 3156203 := bstep (se 1 (by rfl) ⟨2367152, by rfl⟩ : syracuseStep 3156203 = 4734305) B4734305
theorem B2104135 : Blo 2103435 2104135 := bstep (se 1 (by rfl) ⟨1578101, by rfl⟩ : syracuseStep 2104135 = 3156203) B3156203
theorem B2367157 : Blo 2103435 2367157 := bbase (se 5 (by rfl) ⟨110960, by rfl⟩ : syracuseStep 2367157 = 221921) (by norm_num)
theorem B3156209 : Blo 2103435 3156209 := bstep (se 2 (by rfl) ⟨1183578, by rfl⟩ : syracuseStep 3156209 = 2367157) B2367157
theorem B2104139 : Blo 2103435 2104139 := bstep (se 1 (by rfl) ⟨1578104, by rfl⟩ : syracuseStep 2104139 = 3156209) B3156209
theorem B2663057 : Blo 2103435 2663057 := bbase (se 2 (by rfl) ⟨998646, by rfl⟩ : syracuseStep 2663057 = 1997293) (by norm_num)
theorem B7101485 : Blo 2103435 7101485 := bstep (se 3 (by rfl) ⟨1331528, by rfl⟩ : syracuseStep 7101485 = 2663057) B2663057
theorem B4734323 : Blo 2103435 4734323 := bstep (se 1 (by rfl) ⟨3550742, by rfl⟩ : syracuseStep 4734323 = 7101485) B7101485
theorem B3156215 : Blo 2103435 3156215 := bstep (se 1 (by rfl) ⟨2367161, by rfl⟩ : syracuseStep 3156215 = 4734323) B4734323
theorem B2104143 : Blo 2103435 2104143 := bstep (se 1 (by rfl) ⟨1578107, by rfl⟩ : syracuseStep 2104143 = 3156215) B3156215
theorem B3156221 : Blo 2103435 3156221 := bbase (se 3 (by rfl) ⟨591791, by rfl⟩ : syracuseStep 3156221 = 1183583) (by norm_num)
theorem B2104147 : Blo 2103435 2104147 := bstep (se 1 (by rfl) ⟨1578110, by rfl⟩ : syracuseStep 2104147 = 3156221) B3156221
theorem B4734341 : Blo 2103435 4734341 := bbase (se 4 (by rfl) ⟨443844, by rfl⟩ : syracuseStep 4734341 = 887689) (by norm_num)
theorem B3156227 : Blo 2103435 3156227 := bstep (se 1 (by rfl) ⟨2367170, by rfl⟩ : syracuseStep 3156227 = 4734341) B4734341
theorem B2104151 : Blo 2103435 2104151 := bstep (se 1 (by rfl) ⟨1578113, by rfl⟩ : syracuseStep 2104151 = 3156227) B3156227
theorem B2995957 : Blo 2103435 2995957 := bbase (se 5 (by rfl) ⟨140435, by rfl⟩ : syracuseStep 2995957 = 280871) (by norm_num)
theorem B3994609 : Blo 2103435 3994609 := bstep (se 2 (by rfl) ⟨1497978, by rfl⟩ : syracuseStep 3994609 = 2995957) B2995957
theorem B5326145 : Blo 2103435 5326145 := bstep (se 2 (by rfl) ⟨1997304, by rfl⟩ : syracuseStep 5326145 = 3994609) B3994609
theorem B3550763 : Blo 2103435 3550763 := bstep (se 1 (by rfl) ⟨2663072, by rfl⟩ : syracuseStep 3550763 = 5326145) B5326145
theorem B2367175 : Blo 2103435 2367175 := bstep (se 1 (by rfl) ⟨1775381, by rfl⟩ : syracuseStep 2367175 = 3550763) B3550763
theorem B3156233 : Blo 2103435 3156233 := bstep (se 2 (by rfl) ⟨1183587, by rfl⟩ : syracuseStep 3156233 = 2367175) B2367175
theorem B2104155 : Blo 2103435 2104155 := bstep (se 1 (by rfl) ⟨1578116, by rfl⟩ : syracuseStep 2104155 = 3156233) B3156233
theorem B10652309 : Blo 2103435 10652309 := bbase (se 6 (by rfl) ⟨249663, by rfl⟩ : syracuseStep 10652309 = 499327) (by norm_num)
theorem B7101539 : Blo 2103435 7101539 := bstep (se 1 (by rfl) ⟨5326154, by rfl⟩ : syracuseStep 7101539 = 10652309) B10652309
theorem B4734359 : Blo 2103435 4734359 := bstep (se 1 (by rfl) ⟨3550769, by rfl⟩ : syracuseStep 4734359 = 7101539) B7101539
theorem B3156239 : Blo 2103435 3156239 := bstep (se 1 (by rfl) ⟨2367179, by rfl⟩ : syracuseStep 3156239 = 4734359) B4734359
theorem B2104159 : Blo 2103435 2104159 := bstep (se 1 (by rfl) ⟨1578119, by rfl⟩ : syracuseStep 2104159 = 3156239) B3156239
theorem B3156245 : Blo 2103435 3156245 := bbase (se 6 (by rfl) ⟨73974, by rfl⟩ : syracuseStep 3156245 = 147949) (by norm_num)
theorem B2104163 : Blo 2103435 2104163 := bstep (se 1 (by rfl) ⟨1578122, by rfl⟩ : syracuseStep 2104163 = 3156245) B3156245
theorem B2527853 : Blo 2103435 2527853 := bbase (se 3 (by rfl) ⟨473972, by rfl⟩ : syracuseStep 2527853 = 947945) (by norm_num)
theorem B26963765 : Blo 2103435 26963765 := bstep (se 5 (by rfl) ⟨1263926, by rfl⟩ : syracuseStep 26963765 = 2527853) B2527853
theorem B17975843 : Blo 2103435 17975843 := bstep (se 1 (by rfl) ⟨13481882, by rfl⟩ : syracuseStep 17975843 = 26963765) B26963765
theorem B11983895 : Blo 2103435 11983895 := bstep (se 1 (by rfl) ⟨8987921, by rfl⟩ : syracuseStep 11983895 = 17975843) B17975843
theorem B7989263 : Blo 2103435 7989263 := bstep (se 1 (by rfl) ⟨5991947, by rfl⟩ : syracuseStep 7989263 = 11983895) B11983895
theorem B5326175 : Blo 2103435 5326175 := bstep (se 1 (by rfl) ⟨3994631, by rfl⟩ : syracuseStep 5326175 = 7989263) B7989263
theorem B3550783 : Blo 2103435 3550783 := bstep (se 1 (by rfl) ⟨2663087, by rfl⟩ : syracuseStep 3550783 = 5326175) B5326175
theorem B4734377 : Blo 2103435 4734377 := bstep (se 2 (by rfl) ⟨1775391, by rfl⟩ : syracuseStep 4734377 = 3550783) B3550783
theorem B3156251 : Blo 2103435 3156251 := bstep (se 1 (by rfl) ⟨2367188, by rfl⟩ : syracuseStep 3156251 = 4734377) B4734377
theorem B2104167 : Blo 2103435 2104167 := bstep (se 1 (by rfl) ⟨1578125, by rfl⟩ : syracuseStep 2104167 = 3156251) B3156251
theorem B2367193 : Blo 2103435 2367193 := bbase (se 2 (by rfl) ⟨887697, by rfl⟩ : syracuseStep 2367193 = 1775395) (by norm_num)
theorem B3156257 : Blo 2103435 3156257 := bstep (se 2 (by rfl) ⟨1183596, by rfl⟩ : syracuseStep 3156257 = 2367193) B2367193
theorem B2104171 : Blo 2103435 2104171 := bstep (se 1 (by rfl) ⟨1578128, by rfl⟩ : syracuseStep 2104171 = 3156257) B3156257
theorem B2246989 : Blo 2103435 2246989 := bbase (se 3 (by rfl) ⟨421310, by rfl⟩ : syracuseStep 2246989 = 842621) (by norm_num)
theorem B2995985 : Blo 2103435 2995985 := bstep (se 2 (by rfl) ⟨1123494, by rfl⟩ : syracuseStep 2995985 = 2246989) B2246989
theorem B7989293 : Blo 2103435 7989293 := bstep (se 3 (by rfl) ⟨1497992, by rfl⟩ : syracuseStep 7989293 = 2995985) B2995985
theorem B5326195 : Blo 2103435 5326195 := bstep (se 1 (by rfl) ⟨3994646, by rfl⟩ : syracuseStep 5326195 = 7989293) B7989293
theorem B7101593 : Blo 2103435 7101593 := bstep (se 2 (by rfl) ⟨2663097, by rfl⟩ : syracuseStep 7101593 = 5326195) B5326195
theorem B4734395 : Blo 2103435 4734395 := bstep (se 1 (by rfl) ⟨3550796, by rfl⟩ : syracuseStep 4734395 = 7101593) B7101593
theorem B3156263 : Blo 2103435 3156263 := bstep (se 1 (by rfl) ⟨2367197, by rfl⟩ : syracuseStep 3156263 = 4734395) B4734395
theorem B2104175 : Blo 2103435 2104175 := bstep (se 1 (by rfl) ⟨1578131, by rfl⟩ : syracuseStep 2104175 = 3156263) B3156263
theorem B3156269 : Blo 2103435 3156269 := bbase (se 3 (by rfl) ⟨591800, by rfl⟩ : syracuseStep 3156269 = 1183601) (by norm_num)
theorem B2104179 : Blo 2103435 2104179 := bstep (se 1 (by rfl) ⟨1578134, by rfl⟩ : syracuseStep 2104179 = 3156269) B3156269
theorem B4734413 : Blo 2103435 4734413 := bbase (se 3 (by rfl) ⟨887702, by rfl⟩ : syracuseStep 4734413 = 1775405) (by norm_num)
theorem B3156275 : Blo 2103435 3156275 := bstep (se 1 (by rfl) ⟨2367206, by rfl⟩ : syracuseStep 3156275 = 4734413) B4734413
theorem B2104183 : Blo 2103435 2104183 := bstep (se 1 (by rfl) ⟨1578137, by rfl⟩ : syracuseStep 2104183 = 3156275) B3156275
theorem B2663113 : Blo 2103435 2663113 := bbase (se 2 (by rfl) ⟨998667, by rfl⟩ : syracuseStep 2663113 = 1997335) (by norm_num)
theorem B3550817 : Blo 2103435 3550817 := bstep (se 2 (by rfl) ⟨1331556, by rfl⟩ : syracuseStep 3550817 = 2663113) B2663113
theorem B2367211 : Blo 2103435 2367211 := bstep (se 1 (by rfl) ⟨1775408, by rfl⟩ : syracuseStep 2367211 = 3550817) B3550817
theorem B3156281 : Blo 2103435 3156281 := bstep (se 2 (by rfl) ⟨1183605, by rfl⟩ : syracuseStep 3156281 = 2367211) B2367211
theorem B2104187 : Blo 2103435 2104187 := bstep (se 1 (by rfl) ⟨1578140, by rfl⟩ : syracuseStep 2104187 = 3156281) B3156281
theorem B2699453 : Blo 2103435 2699453 := bbase (se 3 (by rfl) ⟨506147, by rfl⟩ : syracuseStep 2699453 = 1012295) (by norm_num)
theorem B7198541 : Blo 2103435 7198541 := bstep (se 3 (by rfl) ⟨1349726, by rfl⟩ : syracuseStep 7198541 = 2699453) B2699453
theorem B4799027 : Blo 2103435 4799027 := bstep (se 1 (by rfl) ⟨3599270, by rfl⟩ : syracuseStep 4799027 = 7198541) B7198541
theorem B3199351 : Blo 2103435 3199351 := bstep (se 1 (by rfl) ⟨2399513, by rfl⟩ : syracuseStep 3199351 = 4799027) B4799027
theorem B4265801 : Blo 2103435 4265801 := bstep (se 2 (by rfl) ⟨1599675, by rfl⟩ : syracuseStep 4265801 = 3199351) B3199351
theorem B2843867 : Blo 2103435 2843867 := bstep (se 1 (by rfl) ⟨2132900, by rfl⟩ : syracuseStep 2843867 = 4265801) B4265801
theorem B7583645 : Blo 2103435 7583645 := bstep (se 3 (by rfl) ⟨1421933, by rfl⟩ : syracuseStep 7583645 = 2843867) B2843867
theorem B20223053 : Blo 2103435 20223053 := bstep (se 3 (by rfl) ⟨3791822, by rfl⟩ : syracuseStep 20223053 = 7583645) B7583645
theorem B13482035 : Blo 2103435 13482035 := bstep (se 1 (by rfl) ⟨10111526, by rfl⟩ : syracuseStep 13482035 = 20223053) B20223053
theorem B8988023 : Blo 2103435 8988023 := bstep (se 1 (by rfl) ⟨6741017, by rfl⟩ : syracuseStep 8988023 = 13482035) B13482035
theorem B23968061 : Blo 2103435 23968061 := bstep (se 3 (by rfl) ⟨4494011, by rfl⟩ : syracuseStep 23968061 = 8988023) B8988023
theorem B15978707 : Blo 2103435 15978707 := bstep (se 1 (by rfl) ⟨11984030, by rfl⟩ : syracuseStep 15978707 = 23968061) B23968061
theorem B10652471 : Blo 2103435 10652471 := bstep (se 1 (by rfl) ⟨7989353, by rfl⟩ : syracuseStep 10652471 = 15978707) B15978707
theorem B7101647 : Blo 2103435 7101647 := bstep (se 1 (by rfl) ⟨5326235, by rfl⟩ : syracuseStep 7101647 = 10652471) B10652471
theorem B4734431 : Blo 2103435 4734431 := bstep (se 1 (by rfl) ⟨3550823, by rfl⟩ : syracuseStep 4734431 = 7101647) B7101647
theorem B3156287 : Blo 2103435 3156287 := bstep (se 1 (by rfl) ⟨2367215, by rfl⟩ : syracuseStep 3156287 = 4734431) B4734431
theorem B2104191 : Blo 2103435 2104191 := bstep (se 1 (by rfl) ⟨1578143, by rfl⟩ : syracuseStep 2104191 = 3156287) B3156287
theorem B3156293 : Blo 2103435 3156293 := bbase (se 4 (by rfl) ⟨295902, by rfl⟩ : syracuseStep 3156293 = 591805) (by norm_num)
theorem B2104195 : Blo 2103435 2104195 := bstep (se 1 (by rfl) ⟨1578146, by rfl⟩ : syracuseStep 2104195 = 3156293) B3156293
theorem B3550837 : Blo 2103435 3550837 := bbase (se 5 (by rfl) ⟨166445, by rfl⟩ : syracuseStep 3550837 = 332891) (by norm_num)
theorem B4734449 : Blo 2103435 4734449 := bstep (se 2 (by rfl) ⟨1775418, by rfl⟩ : syracuseStep 4734449 = 3550837) B3550837
theorem B3156299 : Blo 2103435 3156299 := bstep (se 1 (by rfl) ⟨2367224, by rfl⟩ : syracuseStep 3156299 = 4734449) B4734449
theorem B2104199 : Blo 2103435 2104199 := bstep (se 1 (by rfl) ⟨1578149, by rfl⟩ : syracuseStep 2104199 = 3156299) B3156299
theorem B2367229 : Blo 2103435 2367229 := bbase (se 3 (by rfl) ⟨443855, by rfl⟩ : syracuseStep 2367229 = 887711) (by norm_num)
theorem B3156305 : Blo 2103435 3156305 := bstep (se 2 (by rfl) ⟨1183614, by rfl⟩ : syracuseStep 3156305 = 2367229) B2367229
theorem B2104203 : Blo 2103435 2104203 := bstep (se 1 (by rfl) ⟨1578152, by rfl⟩ : syracuseStep 2104203 = 3156305) B3156305
theorem B7101701 : Blo 2103435 7101701 := bbase (se 4 (by rfl) ⟨665784, by rfl⟩ : syracuseStep 7101701 = 1331569) (by norm_num)
theorem B4734467 : Blo 2103435 4734467 := bstep (se 1 (by rfl) ⟨3550850, by rfl⟩ : syracuseStep 4734467 = 7101701) B7101701
theorem B3156311 : Blo 2103435 3156311 := bstep (se 1 (by rfl) ⟨2367233, by rfl⟩ : syracuseStep 3156311 = 4734467) B4734467
theorem B2104207 : Blo 2103435 2104207 := bstep (se 1 (by rfl) ⟨1578155, by rfl⟩ : syracuseStep 2104207 = 3156311) B3156311
theorem B3156317 : Blo 2103435 3156317 := bbase (se 3 (by rfl) ⟨591809, by rfl⟩ : syracuseStep 3156317 = 1183619) (by norm_num)
theorem B2104211 : Blo 2103435 2104211 := bstep (se 1 (by rfl) ⟨1578158, by rfl⟩ : syracuseStep 2104211 = 3156317) B3156317
theorem B4734485 : Blo 2103435 4734485 := bbase (se 6 (by rfl) ⟨110964, by rfl⟩ : syracuseStep 4734485 = 221929) (by norm_num)
theorem B3156323 : Blo 2103435 3156323 := bstep (se 1 (by rfl) ⟨2367242, by rfl⟩ : syracuseStep 3156323 = 4734485) B4734485
theorem B2104215 : Blo 2103435 2104215 := bstep (se 1 (by rfl) ⟨1578161, by rfl⟩ : syracuseStep 2104215 = 3156323) B3156323
theorem B7989461 : Blo 2103435 7989461 := bbase (se 7 (by rfl) ⟨93626, by rfl⟩ : syracuseStep 7989461 = 187253) (by norm_num)
theorem B5326307 : Blo 2103435 5326307 := bstep (se 1 (by rfl) ⟨3994730, by rfl⟩ : syracuseStep 5326307 = 7989461) B7989461
theorem B3550871 : Blo 2103435 3550871 := bstep (se 1 (by rfl) ⟨2663153, by rfl⟩ : syracuseStep 3550871 = 5326307) B5326307
theorem B2367247 : Blo 2103435 2367247 := bstep (se 1 (by rfl) ⟨1775435, by rfl⟩ : syracuseStep 2367247 = 3550871) B3550871
theorem B3156329 : Blo 2103435 3156329 := bstep (se 2 (by rfl) ⟨1183623, by rfl⟩ : syracuseStep 3156329 = 2367247) B2367247
theorem B2104219 : Blo 2103435 2104219 := bstep (se 1 (by rfl) ⟨1578164, by rfl⟩ : syracuseStep 2104219 = 3156329) B3156329
theorem B11984213 : Blo 2103435 11984213 := bbase (se 11 (by rfl) ⟨8777, by rfl⟩ : syracuseStep 11984213 = 17555) (by norm_num)
theorem B7989475 : Blo 2103435 7989475 := bstep (se 1 (by rfl) ⟨5992106, by rfl⟩ : syracuseStep 7989475 = 11984213) B11984213
theorem B10652633 : Blo 2103435 10652633 := bstep (se 2 (by rfl) ⟨3994737, by rfl⟩ : syracuseStep 10652633 = 7989475) B7989475
theorem B7101755 : Blo 2103435 7101755 := bstep (se 1 (by rfl) ⟨5326316, by rfl⟩ : syracuseStep 7101755 = 10652633) B10652633
theorem B4734503 : Blo 2103435 4734503 := bstep (se 1 (by rfl) ⟨3550877, by rfl⟩ : syracuseStep 4734503 = 7101755) B7101755
theorem B3156335 : Blo 2103435 3156335 := bstep (se 1 (by rfl) ⟨2367251, by rfl⟩ : syracuseStep 3156335 = 4734503) B4734503
theorem B2104223 : Blo 2103435 2104223 := bstep (se 1 (by rfl) ⟨1578167, by rfl⟩ : syracuseStep 2104223 = 3156335) B3156335
theorem B3156341 : Blo 2103435 3156341 := bbase (se 5 (by rfl) ⟨147953, by rfl⟩ : syracuseStep 3156341 = 295907) (by norm_num)
theorem B2104227 : Blo 2103435 2104227 := bstep (se 1 (by rfl) ⟨1578170, by rfl⟩ : syracuseStep 2104227 = 3156341) B3156341
theorem B2247049 : Blo 2103435 2247049 := bbase (se 2 (by rfl) ⟨842643, by rfl⟩ : syracuseStep 2247049 = 1685287) (by norm_num)
theorem B2996065 : Blo 2103435 2996065 := bstep (se 2 (by rfl) ⟨1123524, by rfl⟩ : syracuseStep 2996065 = 2247049) B2247049
theorem B3994753 : Blo 2103435 3994753 := bstep (se 2 (by rfl) ⟨1498032, by rfl⟩ : syracuseStep 3994753 = 2996065) B2996065
theorem B5326337 : Blo 2103435 5326337 := bstep (se 2 (by rfl) ⟨1997376, by rfl⟩ : syracuseStep 5326337 = 3994753) B3994753
theorem B3550891 : Blo 2103435 3550891 := bstep (se 1 (by rfl) ⟨2663168, by rfl⟩ : syracuseStep 3550891 = 5326337) B5326337
theorem B4734521 : Blo 2103435 4734521 := bstep (se 2 (by rfl) ⟨1775445, by rfl⟩ : syracuseStep 4734521 = 3550891) B3550891
theorem B3156347 : Blo 2103435 3156347 := bstep (se 1 (by rfl) ⟨2367260, by rfl⟩ : syracuseStep 3156347 = 4734521) B4734521
theorem B2104231 : Blo 2103435 2104231 := bstep (se 1 (by rfl) ⟨1578173, by rfl⟩ : syracuseStep 2104231 = 3156347) B3156347
theorem B2367265 : Blo 2103435 2367265 := bbase (se 2 (by rfl) ⟨887724, by rfl⟩ : syracuseStep 2367265 = 1775449) (by norm_num)
theorem B3156353 : Blo 2103435 3156353 := bstep (se 2 (by rfl) ⟨1183632, by rfl⟩ : syracuseStep 3156353 = 2367265) B2367265
theorem B2104235 : Blo 2103435 2104235 := bstep (se 1 (by rfl) ⟨1578176, by rfl⟩ : syracuseStep 2104235 = 3156353) B3156353
theorem B5326357 : Blo 2103435 5326357 := bbase (se 6 (by rfl) ⟨124836, by rfl⟩ : syracuseStep 5326357 = 249673) (by norm_num)
theorem B7101809 : Blo 2103435 7101809 := bstep (se 2 (by rfl) ⟨2663178, by rfl⟩ : syracuseStep 7101809 = 5326357) B5326357
theorem B4734539 : Blo 2103435 4734539 := bstep (se 1 (by rfl) ⟨3550904, by rfl⟩ : syracuseStep 4734539 = 7101809) B7101809
theorem B3156359 : Blo 2103435 3156359 := bstep (se 1 (by rfl) ⟨2367269, by rfl⟩ : syracuseStep 3156359 = 4734539) B4734539
theorem B2104239 : Blo 2103435 2104239 := bstep (se 1 (by rfl) ⟨1578179, by rfl⟩ : syracuseStep 2104239 = 3156359) B3156359
theorem B3156365 : Blo 2103435 3156365 := bbase (se 3 (by rfl) ⟨591818, by rfl⟩ : syracuseStep 3156365 = 1183637) (by norm_num)
theorem B2104243 : Blo 2103435 2104243 := bstep (se 1 (by rfl) ⟨1578182, by rfl⟩ : syracuseStep 2104243 = 3156365) B3156365
theorem B4734557 : Blo 2103435 4734557 := bbase (se 3 (by rfl) ⟨887729, by rfl⟩ : syracuseStep 4734557 = 1775459) (by norm_num)
theorem B3156371 : Blo 2103435 3156371 := bstep (se 1 (by rfl) ⟨2367278, by rfl⟩ : syracuseStep 3156371 = 4734557) B4734557
theorem B2104247 : Blo 2103435 2104247 := bstep (se 1 (by rfl) ⟨1578185, by rfl⟩ : syracuseStep 2104247 = 3156371) B3156371
theorem B3550925 : Blo 2103435 3550925 := bbase (se 3 (by rfl) ⟨665798, by rfl⟩ : syracuseStep 3550925 = 1331597) (by norm_num)
theorem B2367283 : Blo 2103435 2367283 := bstep (se 1 (by rfl) ⟨1775462, by rfl⟩ : syracuseStep 2367283 = 3550925) B3550925
theorem B3156377 : Blo 2103435 3156377 := bstep (se 2 (by rfl) ⟨1183641, by rfl⟩ : syracuseStep 3156377 = 2367283) B2367283
theorem B2104251 : Blo 2103435 2104251 := bstep (se 1 (by rfl) ⟨1578188, by rfl⟩ : syracuseStep 2104251 = 3156377) B3156377
theorem B5055917 : Blo 2103435 5055917 := bbase (se 3 (by rfl) ⟨947984, by rfl⟩ : syracuseStep 5055917 = 1895969) (by norm_num)
theorem B13482445 : Blo 2103435 13482445 := bstep (se 3 (by rfl) ⟨2527958, by rfl⟩ : syracuseStep 13482445 = 5055917) B5055917
theorem B17976593 : Blo 2103435 17976593 := bstep (se 2 (by rfl) ⟨6741222, by rfl⟩ : syracuseStep 17976593 = 13482445) B13482445
theorem B11984395 : Blo 2103435 11984395 := bstep (se 1 (by rfl) ⟨8988296, by rfl⟩ : syracuseStep 11984395 = 17976593) B17976593
theorem B15979193 : Blo 2103435 15979193 := bstep (se 2 (by rfl) ⟨5992197, by rfl⟩ : syracuseStep 15979193 = 11984395) B11984395
theorem B10652795 : Blo 2103435 10652795 := bstep (se 1 (by rfl) ⟨7989596, by rfl⟩ : syracuseStep 10652795 = 15979193) B15979193
theorem B7101863 : Blo 2103435 7101863 := bstep (se 1 (by rfl) ⟨5326397, by rfl⟩ : syracuseStep 7101863 = 10652795) B10652795
theorem B4734575 : Blo 2103435 4734575 := bstep (se 1 (by rfl) ⟨3550931, by rfl⟩ : syracuseStep 4734575 = 7101863) B7101863
theorem B3156383 : Blo 2103435 3156383 := bstep (se 1 (by rfl) ⟨2367287, by rfl⟩ : syracuseStep 3156383 = 4734575) B4734575
theorem B2104255 : Blo 2103435 2104255 := bstep (se 1 (by rfl) ⟨1578191, by rfl⟩ : syracuseStep 2104255 = 3156383) B3156383
theorem B3156389 : Blo 2103435 3156389 := bbase (se 4 (by rfl) ⟨295911, by rfl⟩ : syracuseStep 3156389 = 591823) (by norm_num)
theorem B2104259 : Blo 2103435 2104259 := bstep (se 1 (by rfl) ⟨1578194, by rfl⟩ : syracuseStep 2104259 = 3156389) B3156389
theorem B2663209 : Blo 2103435 2663209 := bbase (se 2 (by rfl) ⟨998703, by rfl⟩ : syracuseStep 2663209 = 1997407) (by norm_num)
theorem B3550945 : Blo 2103435 3550945 := bstep (se 2 (by rfl) ⟨1331604, by rfl⟩ : syracuseStep 3550945 = 2663209) B2663209
theorem B4734593 : Blo 2103435 4734593 := bstep (se 2 (by rfl) ⟨1775472, by rfl⟩ : syracuseStep 4734593 = 3550945) B3550945
theorem B3156395 : Blo 2103435 3156395 := bstep (se 1 (by rfl) ⟨2367296, by rfl⟩ : syracuseStep 3156395 = 4734593) B4734593
theorem B2104263 : Blo 2103435 2104263 := bstep (se 1 (by rfl) ⟨1578197, by rfl⟩ : syracuseStep 2104263 = 3156395) B3156395
theorem B2367301 : Blo 2103435 2367301 := bbase (se 4 (by rfl) ⟨221934, by rfl⟩ : syracuseStep 2367301 = 443869) (by norm_num)
theorem B3156401 : Blo 2103435 3156401 := bstep (se 2 (by rfl) ⟨1183650, by rfl⟩ : syracuseStep 3156401 = 2367301) B2367301
theorem B2104267 : Blo 2103435 2104267 := bstep (se 1 (by rfl) ⟨1578200, by rfl⟩ : syracuseStep 2104267 = 3156401) B3156401
theorem B3994829 : Blo 2103435 3994829 := bbase (se 3 (by rfl) ⟨749030, by rfl⟩ : syracuseStep 3994829 = 1498061) (by norm_num)
theorem B2663219 : Blo 2103435 2663219 := bstep (se 1 (by rfl) ⟨1997414, by rfl⟩ : syracuseStep 2663219 = 3994829) B3994829
theorem B7101917 : Blo 2103435 7101917 := bstep (se 3 (by rfl) ⟨1331609, by rfl⟩ : syracuseStep 7101917 = 2663219) B2663219
theorem B4734611 : Blo 2103435 4734611 := bstep (se 1 (by rfl) ⟨3550958, by rfl⟩ : syracuseStep 4734611 = 7101917) B7101917
theorem B3156407 : Blo 2103435 3156407 := bstep (se 1 (by rfl) ⟨2367305, by rfl⟩ : syracuseStep 3156407 = 4734611) B4734611
theorem B2104271 : Blo 2103435 2104271 := bstep (se 1 (by rfl) ⟨1578203, by rfl⟩ : syracuseStep 2104271 = 3156407) B3156407
theorem B3156413 : Blo 2103435 3156413 := bbase (se 3 (by rfl) ⟨591827, by rfl⟩ : syracuseStep 3156413 = 1183655) (by norm_num)
theorem B2104275 : Blo 2103435 2104275 := bstep (se 1 (by rfl) ⟨1578206, by rfl⟩ : syracuseStep 2104275 = 3156413) B3156413
theorem B4734629 : Blo 2103435 4734629 := bbase (se 4 (by rfl) ⟨443871, by rfl⟩ : syracuseStep 4734629 = 887743) (by norm_num)
theorem B3156419 : Blo 2103435 3156419 := bstep (se 1 (by rfl) ⟨2367314, by rfl⟩ : syracuseStep 3156419 = 4734629) B4734629
theorem B2104279 : Blo 2103435 2104279 := bstep (se 1 (by rfl) ⟨1578209, by rfl⟩ : syracuseStep 2104279 = 3156419) B3156419
theorem B5326469 : Blo 2103435 5326469 := bbase (se 4 (by rfl) ⟨499356, by rfl⟩ : syracuseStep 5326469 = 998713) (by norm_num)
theorem B3550979 : Blo 2103435 3550979 := bstep (se 1 (by rfl) ⟨2663234, by rfl⟩ : syracuseStep 3550979 = 5326469) B5326469
theorem B2367319 : Blo 2103435 2367319 := bstep (se 1 (by rfl) ⟨1775489, by rfl⟩ : syracuseStep 2367319 = 3550979) B3550979
theorem B3156425 : Blo 2103435 3156425 := bstep (se 2 (by rfl) ⟨1183659, by rfl⟩ : syracuseStep 3156425 = 2367319) B2367319
theorem B2104283 : Blo 2103435 2104283 := bstep (se 1 (by rfl) ⟨1578212, by rfl⟩ : syracuseStep 2104283 = 3156425) B3156425
theorem B4049365 : Blo 2103435 4049365 := bbase (se 7 (by rfl) ⟨47453, by rfl⟩ : syracuseStep 4049365 = 94907) (by norm_num)
theorem B5399153 : Blo 2103435 5399153 := bstep (se 2 (by rfl) ⟨2024682, by rfl⟩ : syracuseStep 5399153 = 4049365) B4049365
theorem B3599435 : Blo 2103435 3599435 := bstep (se 1 (by rfl) ⟨2699576, by rfl⟩ : syracuseStep 3599435 = 5399153) B5399153
theorem B9598493 : Blo 2103435 9598493 := bstep (se 3 (by rfl) ⟨1799717, by rfl⟩ : syracuseStep 9598493 = 3599435) B3599435
theorem B6398995 : Blo 2103435 6398995 := bstep (se 1 (by rfl) ⟨4799246, by rfl⟩ : syracuseStep 6398995 = 9598493) B9598493
theorem B8531993 : Blo 2103435 8531993 := bstep (se 2 (by rfl) ⟨3199497, by rfl⟩ : syracuseStep 8531993 = 6398995) B6398995
theorem B5687995 : Blo 2103435 5687995 := bstep (se 1 (by rfl) ⟨4265996, by rfl⟩ : syracuseStep 5687995 = 8531993) B8531993
theorem B7583993 : Blo 2103435 7583993 := bstep (se 2 (by rfl) ⟨2843997, by rfl⟩ : syracuseStep 7583993 = 5687995) B5687995
theorem B5055995 : Blo 2103435 5055995 := bstep (se 1 (by rfl) ⟨3791996, by rfl⟩ : syracuseStep 5055995 = 7583993) B7583993
theorem B3370663 : Blo 2103435 3370663 := bstep (se 1 (by rfl) ⟨2527997, by rfl⟩ : syracuseStep 3370663 = 5055995) B5055995
theorem B4494217 : Blo 2103435 4494217 := bstep (se 2 (by rfl) ⟨1685331, by rfl⟩ : syracuseStep 4494217 = 3370663) B3370663
theorem B5992289 : Blo 2103435 5992289 := bstep (se 2 (by rfl) ⟨2247108, by rfl⟩ : syracuseStep 5992289 = 4494217) B4494217
theorem B3994859 : Blo 2103435 3994859 := bstep (se 1 (by rfl) ⟨2996144, by rfl⟩ : syracuseStep 3994859 = 5992289) B5992289
theorem B10652957 : Blo 2103435 10652957 := bstep (se 3 (by rfl) ⟨1997429, by rfl⟩ : syracuseStep 10652957 = 3994859) B3994859
theorem B7101971 : Blo 2103435 7101971 := bstep (se 1 (by rfl) ⟨5326478, by rfl⟩ : syracuseStep 7101971 = 10652957) B10652957
theorem B4734647 : Blo 2103435 4734647 := bstep (se 1 (by rfl) ⟨3550985, by rfl⟩ : syracuseStep 4734647 = 7101971) B7101971
theorem B3156431 : Blo 2103435 3156431 := bstep (se 1 (by rfl) ⟨2367323, by rfl⟩ : syracuseStep 3156431 = 4734647) B4734647
theorem B2104287 : Blo 2103435 2104287 := bstep (se 1 (by rfl) ⟨1578215, by rfl⟩ : syracuseStep 2104287 = 3156431) B3156431
theorem B3156437 : Blo 2103435 3156437 := bbase (se 7 (by rfl) ⟨36989, by rfl⟩ : syracuseStep 3156437 = 73979) (by norm_num)
theorem B2104291 : Blo 2103435 2104291 := bstep (se 1 (by rfl) ⟨1578218, by rfl⟩ : syracuseStep 2104291 = 3156437) B3156437
theorem B7989749 : Blo 2103435 7989749 := bbase (se 5 (by rfl) ⟨374519, by rfl⟩ : syracuseStep 7989749 = 749039) (by norm_num)
theorem B5326499 : Blo 2103435 5326499 := bstep (se 1 (by rfl) ⟨3994874, by rfl⟩ : syracuseStep 5326499 = 7989749) B7989749
theorem B3550999 : Blo 2103435 3550999 := bstep (se 1 (by rfl) ⟨2663249, by rfl⟩ : syracuseStep 3550999 = 5326499) B5326499
theorem B4734665 : Blo 2103435 4734665 := bstep (se 2 (by rfl) ⟨1775499, by rfl⟩ : syracuseStep 4734665 = 3550999) B3550999
theorem B3156443 : Blo 2103435 3156443 := bstep (se 1 (by rfl) ⟨2367332, by rfl⟩ : syracuseStep 3156443 = 4734665) B4734665
theorem B2104295 : Blo 2103435 2104295 := bstep (se 1 (by rfl) ⟨1578221, by rfl⟩ : syracuseStep 2104295 = 3156443) B3156443
theorem B2367337 : Blo 2103435 2367337 := bbase (se 2 (by rfl) ⟨887751, by rfl⟩ : syracuseStep 2367337 = 1775503) (by norm_num)
theorem B3156449 : Blo 2103435 3156449 := bstep (se 2 (by rfl) ⟨1183668, by rfl⟩ : syracuseStep 3156449 = 2367337) B2367337
theorem B2104299 : Blo 2103435 2104299 := bstep (se 1 (by rfl) ⟨1578224, by rfl⟩ : syracuseStep 2104299 = 3156449) B3156449
theorem B4266029 : Blo 2103435 4266029 := bbase (se 3 (by rfl) ⟨799880, by rfl⟩ : syracuseStep 4266029 = 1599761) (by norm_num)
theorem B2844019 : Blo 2103435 2844019 := bstep (se 1 (by rfl) ⟨2133014, by rfl⟩ : syracuseStep 2844019 = 4266029) B4266029
theorem B3792025 : Blo 2103435 3792025 := bstep (se 2 (by rfl) ⟨1422009, by rfl⟩ : syracuseStep 3792025 = 2844019) B2844019
theorem B5056033 : Blo 2103435 5056033 := bstep (se 2 (by rfl) ⟨1896012, by rfl⟩ : syracuseStep 5056033 = 3792025) B3792025
theorem B6741377 : Blo 2103435 6741377 := bstep (se 2 (by rfl) ⟨2528016, by rfl⟩ : syracuseStep 6741377 = 5056033) B5056033
theorem B4494251 : Blo 2103435 4494251 := bstep (se 1 (by rfl) ⟨3370688, by rfl⟩ : syracuseStep 4494251 = 6741377) B6741377
theorem B11984669 : Blo 2103435 11984669 := bstep (se 3 (by rfl) ⟨2247125, by rfl⟩ : syracuseStep 11984669 = 4494251) B4494251
theorem B7989779 : Blo 2103435 7989779 := bstep (se 1 (by rfl) ⟨5992334, by rfl⟩ : syracuseStep 7989779 = 11984669) B11984669
theorem B5326519 : Blo 2103435 5326519 := bstep (se 1 (by rfl) ⟨3994889, by rfl⟩ : syracuseStep 5326519 = 7989779) B7989779
theorem B7102025 : Blo 2103435 7102025 := bstep (se 2 (by rfl) ⟨2663259, by rfl⟩ : syracuseStep 7102025 = 5326519) B5326519
theorem B4734683 : Blo 2103435 4734683 := bstep (se 1 (by rfl) ⟨3551012, by rfl⟩ : syracuseStep 4734683 = 7102025) B7102025
theorem B3156455 : Blo 2103435 3156455 := bstep (se 1 (by rfl) ⟨2367341, by rfl⟩ : syracuseStep 3156455 = 4734683) B4734683
theorem B2104303 : Blo 2103435 2104303 := bstep (se 1 (by rfl) ⟨1578227, by rfl⟩ : syracuseStep 2104303 = 3156455) B3156455
theorem B3156461 : Blo 2103435 3156461 := bbase (se 3 (by rfl) ⟨591836, by rfl⟩ : syracuseStep 3156461 = 1183673) (by norm_num)
theorem B2104307 : Blo 2103435 2104307 := bstep (se 1 (by rfl) ⟨1578230, by rfl⟩ : syracuseStep 2104307 = 3156461) B3156461
theorem B4734701 : Blo 2103435 4734701 := bbase (se 3 (by rfl) ⟨887756, by rfl⟩ : syracuseStep 4734701 = 1775513) (by norm_num)
theorem B3156467 : Blo 2103435 3156467 := bstep (se 1 (by rfl) ⟨2367350, by rfl⟩ : syracuseStep 3156467 = 4734701) B4734701
theorem B2104311 : Blo 2103435 2104311 := bstep (se 1 (by rfl) ⟨1578233, by rfl⟩ : syracuseStep 2104311 = 3156467) B3156467
theorem B3370709 : Blo 2103435 3370709 := bbase (se 7 (by rfl) ⟨39500, by rfl⟩ : syracuseStep 3370709 = 79001) (by norm_num)
theorem B2247139 : Blo 2103435 2247139 := bstep (se 1 (by rfl) ⟨1685354, by rfl⟩ : syracuseStep 2247139 = 3370709) B3370709
theorem B2996185 : Blo 2103435 2996185 := bstep (se 2 (by rfl) ⟨1123569, by rfl⟩ : syracuseStep 2996185 = 2247139) B2247139
theorem B3994913 : Blo 2103435 3994913 := bstep (se 2 (by rfl) ⟨1498092, by rfl⟩ : syracuseStep 3994913 = 2996185) B2996185
theorem B2663275 : Blo 2103435 2663275 := bstep (se 1 (by rfl) ⟨1997456, by rfl⟩ : syracuseStep 2663275 = 3994913) B3994913
theorem B3551033 : Blo 2103435 3551033 := bstep (se 2 (by rfl) ⟨1331637, by rfl⟩ : syracuseStep 3551033 = 2663275) B2663275
theorem B2367355 : Blo 2103435 2367355 := bstep (se 1 (by rfl) ⟨1775516, by rfl⟩ : syracuseStep 2367355 = 3551033) B3551033
theorem B3156473 : Blo 2103435 3156473 := bstep (se 2 (by rfl) ⟨1183677, by rfl⟩ : syracuseStep 3156473 = 2367355) B2367355
theorem B2104315 : Blo 2103435 2104315 := bstep (se 1 (by rfl) ⟨1578236, by rfl⟩ : syracuseStep 2104315 = 3156473) B3156473
theorem B5547565 : Blo 2103435 5547565 := bbase (se 3 (by rfl) ⟨1040168, by rfl⟩ : syracuseStep 5547565 = 2080337) (by norm_num)
theorem B7396753 : Blo 2103435 7396753 := bstep (se 2 (by rfl) ⟨2773782, by rfl⟩ : syracuseStep 7396753 = 5547565) B5547565
theorem B9862337 : Blo 2103435 9862337 := bstep (se 2 (by rfl) ⟨3698376, by rfl⟩ : syracuseStep 9862337 = 7396753) B7396753
theorem B6574891 : Blo 2103435 6574891 := bstep (se 1 (by rfl) ⟨4931168, by rfl⟩ : syracuseStep 6574891 = 9862337) B9862337
theorem B8766521 : Blo 2103435 8766521 := bstep (se 2 (by rfl) ⟨3287445, by rfl⟩ : syracuseStep 8766521 = 6574891) B6574891
theorem B5844347 : Blo 2103435 5844347 := bstep (se 1 (by rfl) ⟨4383260, by rfl⟩ : syracuseStep 5844347 = 8766521) B8766521
theorem B62339701 : Blo 2103435 62339701 := bstep (se 5 (by rfl) ⟨2922173, by rfl⟩ : syracuseStep 62339701 = 5844347) B5844347
theorem B83119601 : Blo 2103435 83119601 := bstep (se 2 (by rfl) ⟨31169850, by rfl⟩ : syracuseStep 83119601 = 62339701) B62339701
theorem B55413067 : Blo 2103435 55413067 := bstep (se 1 (by rfl) ⟨41559800, by rfl⟩ : syracuseStep 55413067 = 83119601) B83119601
theorem B73884089 : Blo 2103435 73884089 := bstep (se 2 (by rfl) ⟨27706533, by rfl⟩ : syracuseStep 73884089 = 55413067) B55413067
theorem B49256059 : Blo 2103435 49256059 := bstep (se 1 (by rfl) ⟨36942044, by rfl⟩ : syracuseStep 49256059 = 73884089) B73884089
theorem B65674745 : Blo 2103435 65674745 := bstep (se 2 (by rfl) ⟨24628029, by rfl⟩ : syracuseStep 65674745 = 49256059) B49256059
theorem B43783163 : Blo 2103435 43783163 := bstep (se 1 (by rfl) ⟨32837372, by rfl⟩ : syracuseStep 43783163 = 65674745) B65674745
theorem B29188775 : Blo 2103435 29188775 := bstep (se 1 (by rfl) ⟨21891581, by rfl⟩ : syracuseStep 29188775 = 43783163) B43783163
theorem B19459183 : Blo 2103435 19459183 := bstep (se 1 (by rfl) ⟨14594387, by rfl⟩ : syracuseStep 19459183 = 29188775) B29188775
theorem B25945577 : Blo 2103435 25945577 := bstep (se 2 (by rfl) ⟨9729591, by rfl⟩ : syracuseStep 25945577 = 19459183) B19459183
theorem B276752821 : Blo 2103435 276752821 := bstep (se 5 (by rfl) ⟨12972788, by rfl⟩ : syracuseStep 276752821 = 25945577) B25945577
theorem B369003761 : Blo 2103435 369003761 := bstep (se 2 (by rfl) ⟨138376410, by rfl⟩ : syracuseStep 369003761 = 276752821) B276752821
theorem B246002507 : Blo 2103435 246002507 := bstep (se 1 (by rfl) ⟨184501880, by rfl⟩ : syracuseStep 246002507 = 369003761) B369003761
theorem B164001671 : Blo 2103435 164001671 := bstep (se 1 (by rfl) ⟨123001253, by rfl⟩ : syracuseStep 164001671 = 246002507) B246002507
theorem B109334447 : Blo 2103435 109334447 := bstep (se 1 (by rfl) ⟨82000835, by rfl⟩ : syracuseStep 109334447 = 164001671) B164001671
theorem B72889631 : Blo 2103435 72889631 := bstep (se 1 (by rfl) ⟨54667223, by rfl⟩ : syracuseStep 72889631 = 109334447) B109334447
theorem B48593087 : Blo 2103435 48593087 := bstep (se 1 (by rfl) ⟨36444815, by rfl⟩ : syracuseStep 48593087 = 72889631) B72889631
theorem B32395391 : Blo 2103435 32395391 := bstep (se 1 (by rfl) ⟨24296543, by rfl⟩ : syracuseStep 32395391 = 48593087) B48593087
theorem B21596927 : Blo 2103435 21596927 := bstep (se 1 (by rfl) ⟨16197695, by rfl⟩ : syracuseStep 21596927 = 32395391) B32395391
theorem B57591805 : Blo 2103435 57591805 := bstep (se 3 (by rfl) ⟨10798463, by rfl⟩ : syracuseStep 57591805 = 21596927) B21596927
theorem B76789073 : Blo 2103435 76789073 := bstep (se 2 (by rfl) ⟨28795902, by rfl⟩ : syracuseStep 76789073 = 57591805) B57591805
theorem B204770861 : Blo 2103435 204770861 := bstep (se 3 (by rfl) ⟨38394536, by rfl⟩ : syracuseStep 204770861 = 76789073) B76789073
theorem B136513907 : Blo 2103435 136513907 := bstep (se 1 (by rfl) ⟨102385430, by rfl⟩ : syracuseStep 136513907 = 204770861) B204770861
theorem B91009271 : Blo 2103435 91009271 := bstep (se 1 (by rfl) ⟨68256953, by rfl⟩ : syracuseStep 91009271 = 136513907) B136513907
theorem B60672847 : Blo 2103435 60672847 := bstep (se 1 (by rfl) ⟨45504635, by rfl⟩ : syracuseStep 60672847 = 91009271) B91009271
theorem B80897129 : Blo 2103435 80897129 := bstep (se 2 (by rfl) ⟨30336423, by rfl⟩ : syracuseStep 80897129 = 60672847) B60672847
theorem B53931419 : Blo 2103435 53931419 := bstep (se 1 (by rfl) ⟨40448564, by rfl⟩ : syracuseStep 53931419 = 80897129) B80897129
theorem B35954279 : Blo 2103435 35954279 := bstep (se 1 (by rfl) ⟨26965709, by rfl⟩ : syracuseStep 35954279 = 53931419) B53931419
theorem B23969519 : Blo 2103435 23969519 := bstep (se 1 (by rfl) ⟨17977139, by rfl⟩ : syracuseStep 23969519 = 35954279) B35954279
theorem B15979679 : Blo 2103435 15979679 := bstep (se 1 (by rfl) ⟨11984759, by rfl⟩ : syracuseStep 15979679 = 23969519) B23969519
theorem B10653119 : Blo 2103435 10653119 := bstep (se 1 (by rfl) ⟨7989839, by rfl⟩ : syracuseStep 10653119 = 15979679) B15979679
theorem B7102079 : Blo 2103435 7102079 := bstep (se 1 (by rfl) ⟨5326559, by rfl⟩ : syracuseStep 7102079 = 10653119) B10653119
theorem B4734719 : Blo 2103435 4734719 := bstep (se 1 (by rfl) ⟨3551039, by rfl⟩ : syracuseStep 4734719 = 7102079) B7102079
theorem B3156479 : Blo 2103435 3156479 := bstep (se 1 (by rfl) ⟨2367359, by rfl⟩ : syracuseStep 3156479 = 4734719) B4734719
theorem B2104319 : Blo 2103435 2104319 := bstep (se 1 (by rfl) ⟨1578239, by rfl⟩ : syracuseStep 2104319 = 3156479) B3156479
theorem B3156485 : Blo 2103435 3156485 := bbase (se 4 (by rfl) ⟨295920, by rfl⟩ : syracuseStep 3156485 = 591841) (by norm_num)
theorem B2104323 : Blo 2103435 2104323 := bstep (se 1 (by rfl) ⟨1578242, by rfl⟩ : syracuseStep 2104323 = 3156485) B3156485
theorem B3551053 : Blo 2103435 3551053 := bbase (se 3 (by rfl) ⟨665822, by rfl⟩ : syracuseStep 3551053 = 1331645) (by norm_num)
theorem B4734737 : Blo 2103435 4734737 := bstep (se 2 (by rfl) ⟨1775526, by rfl⟩ : syracuseStep 4734737 = 3551053) B3551053
theorem B3156491 : Blo 2103435 3156491 := bstep (se 1 (by rfl) ⟨2367368, by rfl⟩ : syracuseStep 3156491 = 4734737) B4734737
theorem B2104327 : Blo 2103435 2104327 := bstep (se 1 (by rfl) ⟨1578245, by rfl⟩ : syracuseStep 2104327 = 3156491) B3156491
theorem B2367373 : Blo 2103435 2367373 := bbase (se 3 (by rfl) ⟨443882, by rfl⟩ : syracuseStep 2367373 = 887765) (by norm_num)
theorem B3156497 : Blo 2103435 3156497 := bstep (se 2 (by rfl) ⟨1183686, by rfl⟩ : syracuseStep 3156497 = 2367373) B2367373
theorem B2104331 : Blo 2103435 2104331 := bstep (se 1 (by rfl) ⟨1578248, by rfl⟩ : syracuseStep 2104331 = 3156497) B3156497
theorem B7102133 : Blo 2103435 7102133 := bbase (se 5 (by rfl) ⟨332912, by rfl⟩ : syracuseStep 7102133 = 665825) (by norm_num)
theorem B4734755 : Blo 2103435 4734755 := bstep (se 1 (by rfl) ⟨3551066, by rfl⟩ : syracuseStep 4734755 = 7102133) B7102133
theorem B3156503 : Blo 2103435 3156503 := bstep (se 1 (by rfl) ⟨2367377, by rfl⟩ : syracuseStep 3156503 = 4734755) B4734755
theorem B2104335 : Blo 2103435 2104335 := bstep (se 1 (by rfl) ⟨1578251, by rfl⟩ : syracuseStep 2104335 = 3156503) B3156503
theorem B3156509 : Blo 2103435 3156509 := bbase (se 3 (by rfl) ⟨591845, by rfl⟩ : syracuseStep 3156509 = 1183691) (by norm_num)
theorem B2104339 : Blo 2103435 2104339 := bstep (se 1 (by rfl) ⟨1578254, by rfl⟩ : syracuseStep 2104339 = 3156509) B3156509
theorem B4734773 : Blo 2103435 4734773 := bbase (se 5 (by rfl) ⟨221942, by rfl⟩ : syracuseStep 4734773 = 443885) (by norm_num)
theorem B3156515 : Blo 2103435 3156515 := bstep (se 1 (by rfl) ⟨2367386, by rfl⟩ : syracuseStep 3156515 = 4734773) B4734773
theorem B2104343 : Blo 2103435 2104343 := bstep (se 1 (by rfl) ⟨1578257, by rfl⟩ : syracuseStep 2104343 = 3156515) B3156515
theorem B3199589 : Blo 2103435 3199589 := bbase (se 4 (by rfl) ⟨299961, by rfl⟩ : syracuseStep 3199589 = 599923) (by norm_num)
theorem B2133059 : Blo 2103435 2133059 := bstep (se 1 (by rfl) ⟨1599794, by rfl⟩ : syracuseStep 2133059 = 3199589) B3199589
theorem B5688157 : Blo 2103435 5688157 := bstep (se 3 (by rfl) ⟨1066529, by rfl⟩ : syracuseStep 5688157 = 2133059) B2133059
theorem B7584209 : Blo 2103435 7584209 := bstep (se 2 (by rfl) ⟨2844078, by rfl⟩ : syracuseStep 7584209 = 5688157) B5688157
theorem B5056139 : Blo 2103435 5056139 := bstep (se 1 (by rfl) ⟨3792104, by rfl⟩ : syracuseStep 5056139 = 7584209) B7584209
theorem B13483037 : Blo 2103435 13483037 := bstep (se 3 (by rfl) ⟨2528069, by rfl⟩ : syracuseStep 13483037 = 5056139) B5056139
theorem B8988691 : Blo 2103435 8988691 := bstep (se 1 (by rfl) ⟨6741518, by rfl⟩ : syracuseStep 8988691 = 13483037) B13483037
theorem B11984921 : Blo 2103435 11984921 := bstep (se 2 (by rfl) ⟨4494345, by rfl⟩ : syracuseStep 11984921 = 8988691) B8988691
theorem B7989947 : Blo 2103435 7989947 := bstep (se 1 (by rfl) ⟨5992460, by rfl⟩ : syracuseStep 7989947 = 11984921) B11984921
theorem B5326631 : Blo 2103435 5326631 := bstep (se 1 (by rfl) ⟨3994973, by rfl⟩ : syracuseStep 5326631 = 7989947) B7989947
theorem B3551087 : Blo 2103435 3551087 := bstep (se 1 (by rfl) ⟨2663315, by rfl⟩ : syracuseStep 3551087 = 5326631) B5326631
theorem B2367391 : Blo 2103435 2367391 := bstep (se 1 (by rfl) ⟨1775543, by rfl⟩ : syracuseStep 2367391 = 3551087) B3551087
theorem B3156521 : Blo 2103435 3156521 := bstep (se 2 (by rfl) ⟨1183695, by rfl⟩ : syracuseStep 3156521 = 2367391) B2367391
theorem B2104347 : Blo 2103435 2104347 := bstep (se 1 (by rfl) ⟨1578260, by rfl⟩ : syracuseStep 2104347 = 3156521) B3156521
theorem B13483061 : Blo 2103435 13483061 := bbase (se 5 (by rfl) ⟨632018, by rfl⟩ : syracuseStep 13483061 = 1264037) (by norm_num)
theorem B8988707 : Blo 2103435 8988707 := bstep (se 1 (by rfl) ⟨6741530, by rfl⟩ : syracuseStep 8988707 = 13483061) B13483061
theorem B5992471 : Blo 2103435 5992471 := bstep (se 1 (by rfl) ⟨4494353, by rfl⟩ : syracuseStep 5992471 = 8988707) B8988707
theorem B7989961 : Blo 2103435 7989961 := bstep (se 2 (by rfl) ⟨2996235, by rfl⟩ : syracuseStep 7989961 = 5992471) B5992471
theorem B10653281 : Blo 2103435 10653281 := bstep (se 2 (by rfl) ⟨3994980, by rfl⟩ : syracuseStep 10653281 = 7989961) B7989961
theorem B7102187 : Blo 2103435 7102187 := bstep (se 1 (by rfl) ⟨5326640, by rfl⟩ : syracuseStep 7102187 = 10653281) B10653281
theorem B4734791 : Blo 2103435 4734791 := bstep (se 1 (by rfl) ⟨3551093, by rfl⟩ : syracuseStep 4734791 = 7102187) B7102187
theorem B3156527 : Blo 2103435 3156527 := bstep (se 1 (by rfl) ⟨2367395, by rfl⟩ : syracuseStep 3156527 = 4734791) B4734791
theorem B2104351 : Blo 2103435 2104351 := bstep (se 1 (by rfl) ⟨1578263, by rfl⟩ : syracuseStep 2104351 = 3156527) B3156527
theorem B3156533 : Blo 2103435 3156533 := bbase (se 5 (by rfl) ⟨147962, by rfl⟩ : syracuseStep 3156533 = 295925) (by norm_num)
theorem B2104355 : Blo 2103435 2104355 := bstep (se 1 (by rfl) ⟨1578266, by rfl⟩ : syracuseStep 2104355 = 3156533) B3156533
theorem B5326661 : Blo 2103435 5326661 := bbase (se 4 (by rfl) ⟨499374, by rfl⟩ : syracuseStep 5326661 = 998749) (by norm_num)
theorem B3551107 : Blo 2103435 3551107 := bstep (se 1 (by rfl) ⟨2663330, by rfl⟩ : syracuseStep 3551107 = 5326661) B5326661
theorem B4734809 : Blo 2103435 4734809 := bstep (se 2 (by rfl) ⟨1775553, by rfl⟩ : syracuseStep 4734809 = 3551107) B3551107
theorem B3156539 : Blo 2103435 3156539 := bstep (se 1 (by rfl) ⟨2367404, by rfl⟩ : syracuseStep 3156539 = 4734809) B4734809
theorem B2104359 : Blo 2103435 2104359 := bstep (se 1 (by rfl) ⟨1578269, by rfl⟩ : syracuseStep 2104359 = 3156539) B3156539
theorem B2367409 : Blo 2103435 2367409 := bbase (se 2 (by rfl) ⟨887778, by rfl⟩ : syracuseStep 2367409 = 1775557) (by norm_num)
theorem B3156545 : Blo 2103435 3156545 := bstep (se 2 (by rfl) ⟨1183704, by rfl⟩ : syracuseStep 3156545 = 2367409) B2367409
theorem B2104363 : Blo 2103435 2104363 := bstep (se 1 (by rfl) ⟨1578272, by rfl⟩ : syracuseStep 2104363 = 3156545) B3156545
theorem B5992517 : Blo 2103435 5992517 := bbase (se 4 (by rfl) ⟨561798, by rfl⟩ : syracuseStep 5992517 = 1123597) (by norm_num)
theorem B3995011 : Blo 2103435 3995011 := bstep (se 1 (by rfl) ⟨2996258, by rfl⟩ : syracuseStep 3995011 = 5992517) B5992517
theorem B5326681 : Blo 2103435 5326681 := bstep (se 2 (by rfl) ⟨1997505, by rfl⟩ : syracuseStep 5326681 = 3995011) B3995011
theorem B7102241 : Blo 2103435 7102241 := bstep (se 2 (by rfl) ⟨2663340, by rfl⟩ : syracuseStep 7102241 = 5326681) B5326681
theorem B4734827 : Blo 2103435 4734827 := bstep (se 1 (by rfl) ⟨3551120, by rfl⟩ : syracuseStep 4734827 = 7102241) B7102241
theorem B3156551 : Blo 2103435 3156551 := bstep (se 1 (by rfl) ⟨2367413, by rfl⟩ : syracuseStep 3156551 = 4734827) B4734827
theorem B2104367 : Blo 2103435 2104367 := bstep (se 1 (by rfl) ⟨1578275, by rfl⟩ : syracuseStep 2104367 = 3156551) B3156551
theorem B3156557 : Blo 2103435 3156557 := bbase (se 3 (by rfl) ⟨591854, by rfl⟩ : syracuseStep 3156557 = 1183709) (by norm_num)
theorem B2104371 : Blo 2103435 2104371 := bstep (se 1 (by rfl) ⟨1578278, by rfl⟩ : syracuseStep 2104371 = 3156557) B3156557
theorem B4734845 : Blo 2103435 4734845 := bbase (se 3 (by rfl) ⟨887783, by rfl⟩ : syracuseStep 4734845 = 1775567) (by norm_num)
theorem B3156563 : Blo 2103435 3156563 := bstep (se 1 (by rfl) ⟨2367422, by rfl⟩ : syracuseStep 3156563 = 4734845) B4734845
theorem B2104375 : Blo 2103435 2104375 := bstep (se 1 (by rfl) ⟨1578281, by rfl⟩ : syracuseStep 2104375 = 3156563) B3156563
theorem B3551141 : Blo 2103435 3551141 := bbase (se 4 (by rfl) ⟨332919, by rfl⟩ : syracuseStep 3551141 = 665839) (by norm_num)
theorem B2367427 : Blo 2103435 2367427 := bstep (se 1 (by rfl) ⟨1775570, by rfl⟩ : syracuseStep 2367427 = 3551141) B3551141
theorem B3156569 : Blo 2103435 3156569 := bstep (se 2 (by rfl) ⟨1183713, by rfl⟩ : syracuseStep 3156569 = 2367427) B2367427
theorem B2104379 : Blo 2103435 2104379 := bstep (se 1 (by rfl) ⟨1578284, by rfl⟩ : syracuseStep 2104379 = 3156569) B3156569
theorem B2528113 : Blo 2103435 2528113 := bbase (se 2 (by rfl) ⟨948042, by rfl⟩ : syracuseStep 2528113 = 1896085) (by norm_num)
theorem B3370817 : Blo 2103435 3370817 := bstep (se 2 (by rfl) ⟨1264056, by rfl⟩ : syracuseStep 3370817 = 2528113) B2528113
theorem B2247211 : Blo 2103435 2247211 := bstep (se 1 (by rfl) ⟨1685408, by rfl⟩ : syracuseStep 2247211 = 3370817) B3370817
theorem B2996281 : Blo 2103435 2996281 := bstep (se 2 (by rfl) ⟨1123605, by rfl⟩ : syracuseStep 2996281 = 2247211) B2247211
theorem B15980165 : Blo 2103435 15980165 := bstep (se 4 (by rfl) ⟨1498140, by rfl⟩ : syracuseStep 15980165 = 2996281) B2996281
theorem B10653443 : Blo 2103435 10653443 := bstep (se 1 (by rfl) ⟨7990082, by rfl⟩ : syracuseStep 10653443 = 15980165) B15980165
theorem B7102295 : Blo 2103435 7102295 := bstep (se 1 (by rfl) ⟨5326721, by rfl⟩ : syracuseStep 7102295 = 10653443) B10653443
theorem B4734863 : Blo 2103435 4734863 := bstep (se 1 (by rfl) ⟨3551147, by rfl⟩ : syracuseStep 4734863 = 7102295) B7102295
theorem B3156575 : Blo 2103435 3156575 := bstep (se 1 (by rfl) ⟨2367431, by rfl⟩ : syracuseStep 3156575 = 4734863) B4734863
theorem B2104383 : Blo 2103435 2104383 := bstep (se 1 (by rfl) ⟨1578287, by rfl⟩ : syracuseStep 2104383 = 3156575) B3156575
theorem B3156581 : Blo 2103435 3156581 := bbase (se 4 (by rfl) ⟨295929, by rfl⟩ : syracuseStep 3156581 = 591859) (by norm_num)
theorem B2104387 : Blo 2103435 2104387 := bstep (se 1 (by rfl) ⟨1578290, by rfl⟩ : syracuseStep 2104387 = 3156581) B3156581
theorem B2996293 : Blo 2103435 2996293 := bbase (se 4 (by rfl) ⟨280902, by rfl⟩ : syracuseStep 2996293 = 561805) (by norm_num)
theorem B3995057 : Blo 2103435 3995057 := bstep (se 2 (by rfl) ⟨1498146, by rfl⟩ : syracuseStep 3995057 = 2996293) B2996293
theorem B2663371 : Blo 2103435 2663371 := bstep (se 1 (by rfl) ⟨1997528, by rfl⟩ : syracuseStep 2663371 = 3995057) B3995057
theorem B3551161 : Blo 2103435 3551161 := bstep (se 2 (by rfl) ⟨1331685, by rfl⟩ : syracuseStep 3551161 = 2663371) B2663371
theorem B4734881 : Blo 2103435 4734881 := bstep (se 2 (by rfl) ⟨1775580, by rfl⟩ : syracuseStep 4734881 = 3551161) B3551161
theorem B3156587 : Blo 2103435 3156587 := bstep (se 1 (by rfl) ⟨2367440, by rfl⟩ : syracuseStep 3156587 = 4734881) B4734881
theorem B2104391 : Blo 2103435 2104391 := bstep (se 1 (by rfl) ⟨1578293, by rfl⟩ : syracuseStep 2104391 = 3156587) B3156587
theorem B2367445 : Blo 2103435 2367445 := bbase (se 7 (by rfl) ⟨27743, by rfl⟩ : syracuseStep 2367445 = 55487) (by norm_num)
theorem B3156593 : Blo 2103435 3156593 := bstep (se 2 (by rfl) ⟨1183722, by rfl⟩ : syracuseStep 3156593 = 2367445) B2367445
theorem B2104395 : Blo 2103435 2104395 := bstep (se 1 (by rfl) ⟨1578296, by rfl⟩ : syracuseStep 2104395 = 3156593) B3156593
theorem B2663381 : Blo 2103435 2663381 := bbase (se 7 (by rfl) ⟨31211, by rfl⟩ : syracuseStep 2663381 = 62423) (by norm_num)
theorem B7102349 : Blo 2103435 7102349 := bstep (se 3 (by rfl) ⟨1331690, by rfl⟩ : syracuseStep 7102349 = 2663381) B2663381
theorem B4734899 : Blo 2103435 4734899 := bstep (se 1 (by rfl) ⟨3551174, by rfl⟩ : syracuseStep 4734899 = 7102349) B7102349
theorem B3156599 : Blo 2103435 3156599 := bstep (se 1 (by rfl) ⟨2367449, by rfl⟩ : syracuseStep 3156599 = 4734899) B4734899
theorem B2104399 : Blo 2103435 2104399 := bstep (se 1 (by rfl) ⟨1578299, by rfl⟩ : syracuseStep 2104399 = 3156599) B3156599
theorem B3156605 : Blo 2103435 3156605 := bbase (se 3 (by rfl) ⟨591863, by rfl⟩ : syracuseStep 3156605 = 1183727) (by norm_num)
theorem B2104403 : Blo 2103435 2104403 := bstep (se 1 (by rfl) ⟨1578302, by rfl⟩ : syracuseStep 2104403 = 3156605) B3156605
theorem B4734917 : Blo 2103435 4734917 := bbase (se 4 (by rfl) ⟨443898, by rfl⟩ : syracuseStep 4734917 = 887797) (by norm_num)
theorem B3156611 : Blo 2103435 3156611 := bstep (se 1 (by rfl) ⟨2367458, by rfl⟩ : syracuseStep 3156611 = 4734917) B4734917
theorem B2104407 : Blo 2103435 2104407 := bstep (se 1 (by rfl) ⟨1578305, by rfl⟩ : syracuseStep 2104407 = 3156611) B3156611
theorem B8988965 : Blo 2103435 8988965 := bbase (se 4 (by rfl) ⟨842715, by rfl⟩ : syracuseStep 8988965 = 1685431) (by norm_num)
theorem B5992643 : Blo 2103435 5992643 := bstep (se 1 (by rfl) ⟨4494482, by rfl⟩ : syracuseStep 5992643 = 8988965) B8988965
theorem B3995095 : Blo 2103435 3995095 := bstep (se 1 (by rfl) ⟨2996321, by rfl⟩ : syracuseStep 3995095 = 5992643) B5992643
theorem B5326793 : Blo 2103435 5326793 := bstep (se 2 (by rfl) ⟨1997547, by rfl⟩ : syracuseStep 5326793 = 3995095) B3995095
theorem B3551195 : Blo 2103435 3551195 := bstep (se 1 (by rfl) ⟨2663396, by rfl⟩ : syracuseStep 3551195 = 5326793) B5326793
theorem B2367463 : Blo 2103435 2367463 := bstep (se 1 (by rfl) ⟨1775597, by rfl⟩ : syracuseStep 2367463 = 3551195) B3551195
theorem B3156617 : Blo 2103435 3156617 := bstep (se 2 (by rfl) ⟨1183731, by rfl⟩ : syracuseStep 3156617 = 2367463) B2367463
theorem B2104411 : Blo 2103435 2104411 := bstep (se 1 (by rfl) ⟨1578308, by rfl⟩ : syracuseStep 2104411 = 3156617) B3156617
theorem B10653605 : Blo 2103435 10653605 := bbase (se 4 (by rfl) ⟨998775, by rfl⟩ : syracuseStep 10653605 = 1997551) (by norm_num)
theorem B7102403 : Blo 2103435 7102403 := bstep (se 1 (by rfl) ⟨5326802, by rfl⟩ : syracuseStep 7102403 = 10653605) B10653605
theorem B4734935 : Blo 2103435 4734935 := bstep (se 1 (by rfl) ⟨3551201, by rfl⟩ : syracuseStep 4734935 = 7102403) B7102403
theorem B3156623 : Blo 2103435 3156623 := bstep (se 1 (by rfl) ⟨2367467, by rfl⟩ : syracuseStep 3156623 = 4734935) B4734935
theorem B2104415 : Blo 2103435 2104415 := bstep (se 1 (by rfl) ⟨1578311, by rfl⟩ : syracuseStep 2104415 = 3156623) B3156623
theorem B3156629 : Blo 2103435 3156629 := bbase (se 6 (by rfl) ⟨73983, by rfl⟩ : syracuseStep 3156629 = 147967) (by norm_num)
theorem B2104419 : Blo 2103435 2104419 := bstep (se 1 (by rfl) ⟨1578314, by rfl⟩ : syracuseStep 2104419 = 3156629) B3156629
theorem B2844181 : Blo 2103435 2844181 := bbase (se 6 (by rfl) ⟨66660, by rfl⟩ : syracuseStep 2844181 = 133321) (by norm_num)
theorem B3792241 : Blo 2103435 3792241 := bstep (se 2 (by rfl) ⟨1422090, by rfl⟩ : syracuseStep 3792241 = 2844181) B2844181
theorem B20225285 : Blo 2103435 20225285 := bstep (se 4 (by rfl) ⟨1896120, by rfl⟩ : syracuseStep 20225285 = 3792241) B3792241
theorem B13483523 : Blo 2103435 13483523 := bstep (se 1 (by rfl) ⟨10112642, by rfl⟩ : syracuseStep 13483523 = 20225285) B20225285
theorem B8989015 : Blo 2103435 8989015 := bstep (se 1 (by rfl) ⟨6741761, by rfl⟩ : syracuseStep 8989015 = 13483523) B13483523
theorem B11985353 : Blo 2103435 11985353 := bstep (se 2 (by rfl) ⟨4494507, by rfl⟩ : syracuseStep 11985353 = 8989015) B8989015
theorem B7990235 : Blo 2103435 7990235 := bstep (se 1 (by rfl) ⟨5992676, by rfl⟩ : syracuseStep 7990235 = 11985353) B11985353
theorem B5326823 : Blo 2103435 5326823 := bstep (se 1 (by rfl) ⟨3995117, by rfl⟩ : syracuseStep 5326823 = 7990235) B7990235
theorem B3551215 : Blo 2103435 3551215 := bstep (se 1 (by rfl) ⟨2663411, by rfl⟩ : syracuseStep 3551215 = 5326823) B5326823
theorem B4734953 : Blo 2103435 4734953 := bstep (se 2 (by rfl) ⟨1775607, by rfl⟩ : syracuseStep 4734953 = 3551215) B3551215
theorem B3156635 : Blo 2103435 3156635 := bstep (se 1 (by rfl) ⟨2367476, by rfl⟩ : syracuseStep 3156635 = 4734953) B4734953
theorem B2104423 : Blo 2103435 2104423 := bstep (se 1 (by rfl) ⟨1578317, by rfl⟩ : syracuseStep 2104423 = 3156635) B3156635
theorem B2367481 : Blo 2103435 2367481 := bbase (se 2 (by rfl) ⟨887805, by rfl⟩ : syracuseStep 2367481 = 1775611) (by norm_num)
theorem B3156641 : Blo 2103435 3156641 := bstep (se 2 (by rfl) ⟨1183740, by rfl⟩ : syracuseStep 3156641 = 2367481) B2367481
theorem B2104427 : Blo 2103435 2104427 := bstep (se 1 (by rfl) ⟨1578320, by rfl⟩ : syracuseStep 2104427 = 3156641) B3156641
theorem B4104893 : Blo 2103435 4104893 := bbase (se 3 (by rfl) ⟨769667, by rfl⟩ : syracuseStep 4104893 = 1539335) (by norm_num)
theorem B2736595 : Blo 2103435 2736595 := bstep (se 1 (by rfl) ⟨2052446, by rfl⟩ : syracuseStep 2736595 = 4104893) B4104893
theorem B14595173 : Blo 2103435 14595173 := bstep (se 4 (by rfl) ⟨1368297, by rfl⟩ : syracuseStep 14595173 = 2736595) B2736595
theorem B9730115 : Blo 2103435 9730115 := bstep (se 1 (by rfl) ⟨7297586, by rfl⟩ : syracuseStep 9730115 = 14595173) B14595173
theorem B6486743 : Blo 2103435 6486743 := bstep (se 1 (by rfl) ⟨4865057, by rfl⟩ : syracuseStep 6486743 = 9730115) B9730115
theorem B4324495 : Blo 2103435 4324495 := bstep (se 1 (by rfl) ⟨3243371, by rfl⟩ : syracuseStep 4324495 = 6486743) B6486743
theorem B5765993 : Blo 2103435 5765993 := bstep (se 2 (by rfl) ⟨2162247, by rfl⟩ : syracuseStep 5765993 = 4324495) B4324495
theorem B3843995 : Blo 2103435 3843995 := bstep (se 1 (by rfl) ⟨2882996, by rfl⟩ : syracuseStep 3843995 = 5765993) B5765993
theorem B10250653 : Blo 2103435 10250653 := bstep (se 3 (by rfl) ⟨1921997, by rfl⟩ : syracuseStep 10250653 = 3843995) B3843995
theorem B13667537 : Blo 2103435 13667537 := bstep (se 2 (by rfl) ⟨5125326, by rfl⟩ : syracuseStep 13667537 = 10250653) B10250653
theorem B36446765 : Blo 2103435 36446765 := bstep (se 3 (by rfl) ⟨6833768, by rfl⟩ : syracuseStep 36446765 = 13667537) B13667537
theorem B97191373 : Blo 2103435 97191373 := bstep (se 3 (by rfl) ⟨18223382, by rfl⟩ : syracuseStep 97191373 = 36446765) B36446765
theorem B129588497 : Blo 2103435 129588497 := bstep (se 2 (by rfl) ⟨48595686, by rfl⟩ : syracuseStep 129588497 = 97191373) B97191373
theorem B86392331 : Blo 2103435 86392331 := bstep (se 1 (by rfl) ⟨64794248, by rfl⟩ : syracuseStep 86392331 = 129588497) B129588497
theorem B57594887 : Blo 2103435 57594887 := bstep (se 1 (by rfl) ⟨43196165, by rfl⟩ : syracuseStep 57594887 = 86392331) B86392331
theorem B38396591 : Blo 2103435 38396591 := bstep (se 1 (by rfl) ⟨28797443, by rfl⟩ : syracuseStep 38396591 = 57594887) B57594887
theorem B25597727 : Blo 2103435 25597727 := bstep (se 1 (by rfl) ⟨19198295, by rfl⟩ : syracuseStep 25597727 = 38396591) B38396591
theorem B17065151 : Blo 2103435 17065151 := bstep (se 1 (by rfl) ⟨12798863, by rfl⟩ : syracuseStep 17065151 = 25597727) B25597727
theorem B11376767 : Blo 2103435 11376767 := bstep (se 1 (by rfl) ⟨8532575, by rfl⟩ : syracuseStep 11376767 = 17065151) B17065151
theorem B7584511 : Blo 2103435 7584511 := bstep (se 1 (by rfl) ⟨5688383, by rfl⟩ : syracuseStep 7584511 = 11376767) B11376767
theorem B10112681 : Blo 2103435 10112681 := bstep (se 2 (by rfl) ⟨3792255, by rfl⟩ : syracuseStep 10112681 = 7584511) B7584511
theorem B6741787 : Blo 2103435 6741787 := bstep (se 1 (by rfl) ⟨5056340, by rfl⟩ : syracuseStep 6741787 = 10112681) B10112681
theorem B8989049 : Blo 2103435 8989049 := bstep (se 2 (by rfl) ⟨3370893, by rfl⟩ : syracuseStep 8989049 = 6741787) B6741787
theorem B5992699 : Blo 2103435 5992699 := bstep (se 1 (by rfl) ⟨4494524, by rfl⟩ : syracuseStep 5992699 = 8989049) B8989049
theorem B7990265 : Blo 2103435 7990265 := bstep (se 2 (by rfl) ⟨2996349, by rfl⟩ : syracuseStep 7990265 = 5992699) B5992699
theorem B5326843 : Blo 2103435 5326843 := bstep (se 1 (by rfl) ⟨3995132, by rfl⟩ : syracuseStep 5326843 = 7990265) B7990265
theorem B7102457 : Blo 2103435 7102457 := bstep (se 2 (by rfl) ⟨2663421, by rfl⟩ : syracuseStep 7102457 = 5326843) B5326843
theorem B4734971 : Blo 2103435 4734971 := bstep (se 1 (by rfl) ⟨3551228, by rfl⟩ : syracuseStep 4734971 = 7102457) B7102457
theorem B3156647 : Blo 2103435 3156647 := bstep (se 1 (by rfl) ⟨2367485, by rfl⟩ : syracuseStep 3156647 = 4734971) B4734971
theorem B2104431 : Blo 2103435 2104431 := bstep (se 1 (by rfl) ⟨1578323, by rfl⟩ : syracuseStep 2104431 = 3156647) B3156647
theorem B3156653 : Blo 2103435 3156653 := bbase (se 3 (by rfl) ⟨591872, by rfl⟩ : syracuseStep 3156653 = 1183745) (by norm_num)
theorem B2104435 : Blo 2103435 2104435 := bstep (se 1 (by rfl) ⟨1578326, by rfl⟩ : syracuseStep 2104435 = 3156653) B3156653
theorem B4734989 : Blo 2103435 4734989 := bbase (se 3 (by rfl) ⟨887810, by rfl⟩ : syracuseStep 4734989 = 1775621) (by norm_num)
theorem B3156659 : Blo 2103435 3156659 := bstep (se 1 (by rfl) ⟨2367494, by rfl⟩ : syracuseStep 3156659 = 4734989) B4734989
theorem B2104439 : Blo 2103435 2104439 := bstep (se 1 (by rfl) ⟨1578329, by rfl⟩ : syracuseStep 2104439 = 3156659) B3156659
theorem B2663437 : Blo 2103435 2663437 := bbase (se 3 (by rfl) ⟨499394, by rfl⟩ : syracuseStep 2663437 = 998789) (by norm_num)
theorem B3551249 : Blo 2103435 3551249 := bstep (se 2 (by rfl) ⟨1331718, by rfl⟩ : syracuseStep 3551249 = 2663437) B2663437
theorem B2367499 : Blo 2103435 2367499 := bstep (se 1 (by rfl) ⟨1775624, by rfl⟩ : syracuseStep 2367499 = 3551249) B3551249
theorem B3156665 : Blo 2103435 3156665 := bstep (se 2 (by rfl) ⟨1183749, by rfl⟩ : syracuseStep 3156665 = 2367499) B2367499
theorem B2104443 : Blo 2103435 2104443 := bstep (se 1 (by rfl) ⟨1578332, by rfl⟩ : syracuseStep 2104443 = 3156665) B3156665
theorem B3037253 : Blo 2103435 3037253 := bbase (se 4 (by rfl) ⟨284742, by rfl⟩ : syracuseStep 3037253 = 569485) (by norm_num)
theorem B8099341 : Blo 2103435 8099341 := bstep (se 3 (by rfl) ⟨1518626, by rfl⟩ : syracuseStep 8099341 = 3037253) B3037253
theorem B43196485 : Blo 2103435 43196485 := bstep (se 4 (by rfl) ⟨4049670, by rfl⟩ : syracuseStep 43196485 = 8099341) B8099341
theorem B57595313 : Blo 2103435 57595313 := bstep (se 2 (by rfl) ⟨21598242, by rfl⟩ : syracuseStep 57595313 = 43196485) B43196485
theorem B38396875 : Blo 2103435 38396875 := bstep (se 1 (by rfl) ⟨28797656, by rfl⟩ : syracuseStep 38396875 = 57595313) B57595313
theorem B51195833 : Blo 2103435 51195833 := bstep (se 2 (by rfl) ⟨19198437, by rfl⟩ : syracuseStep 51195833 = 38396875) B38396875
theorem B34130555 : Blo 2103435 34130555 := bstep (se 1 (by rfl) ⟨25597916, by rfl⟩ : syracuseStep 34130555 = 51195833) B51195833
theorem B22753703 : Blo 2103435 22753703 := bstep (se 1 (by rfl) ⟨17065277, by rfl⟩ : syracuseStep 22753703 = 34130555) B34130555
theorem B15169135 : Blo 2103435 15169135 := bstep (se 1 (by rfl) ⟨11376851, by rfl⟩ : syracuseStep 15169135 = 22753703) B22753703
theorem B20225513 : Blo 2103435 20225513 := bstep (se 2 (by rfl) ⟨7584567, by rfl⟩ : syracuseStep 20225513 = 15169135) B15169135
theorem B13483675 : Blo 2103435 13483675 := bstep (se 1 (by rfl) ⟨10112756, by rfl⟩ : syracuseStep 13483675 = 20225513) B20225513
theorem B17978233 : Blo 2103435 17978233 := bstep (se 2 (by rfl) ⟨6741837, by rfl⟩ : syracuseStep 17978233 = 13483675) B13483675
theorem B23970977 : Blo 2103435 23970977 := bstep (se 2 (by rfl) ⟨8989116, by rfl⟩ : syracuseStep 23970977 = 17978233) B17978233
theorem B15980651 : Blo 2103435 15980651 := bstep (se 1 (by rfl) ⟨11985488, by rfl⟩ : syracuseStep 15980651 = 23970977) B23970977
theorem B10653767 : Blo 2103435 10653767 := bstep (se 1 (by rfl) ⟨7990325, by rfl⟩ : syracuseStep 10653767 = 15980651) B15980651
theorem B7102511 : Blo 2103435 7102511 := bstep (se 1 (by rfl) ⟨5326883, by rfl⟩ : syracuseStep 7102511 = 10653767) B10653767
theorem B4735007 : Blo 2103435 4735007 := bstep (se 1 (by rfl) ⟨3551255, by rfl⟩ : syracuseStep 4735007 = 7102511) B7102511
theorem B3156671 : Blo 2103435 3156671 := bstep (se 1 (by rfl) ⟨2367503, by rfl⟩ : syracuseStep 3156671 = 4735007) B4735007
theorem B2104447 : Blo 2103435 2104447 := bstep (se 1 (by rfl) ⟨1578335, by rfl⟩ : syracuseStep 2104447 = 3156671) B3156671
theorem B3156677 : Blo 2103435 3156677 := bbase (se 4 (by rfl) ⟨295938, by rfl⟩ : syracuseStep 3156677 = 591877) (by norm_num)
theorem B2104451 : Blo 2103435 2104451 := bstep (se 1 (by rfl) ⟨1578338, by rfl⟩ : syracuseStep 2104451 = 3156677) B3156677
theorem B3551269 : Blo 2103435 3551269 := bbase (se 4 (by rfl) ⟨332931, by rfl⟩ : syracuseStep 3551269 = 665863) (by norm_num)
theorem B4735025 : Blo 2103435 4735025 := bstep (se 2 (by rfl) ⟨1775634, by rfl⟩ : syracuseStep 4735025 = 3551269) B3551269
theorem B3156683 : Blo 2103435 3156683 := bstep (se 1 (by rfl) ⟨2367512, by rfl⟩ : syracuseStep 3156683 = 4735025) B4735025
theorem B2104455 : Blo 2103435 2104455 := bstep (se 1 (by rfl) ⟨1578341, by rfl⟩ : syracuseStep 2104455 = 3156683) B3156683
theorem B2367517 : Blo 2103435 2367517 := bbase (se 3 (by rfl) ⟨443909, by rfl⟩ : syracuseStep 2367517 = 887819) (by norm_num)
theorem B3156689 : Blo 2103435 3156689 := bstep (se 2 (by rfl) ⟨1183758, by rfl⟩ : syracuseStep 3156689 = 2367517) B2367517
theorem B2104459 : Blo 2103435 2104459 := bstep (se 1 (by rfl) ⟨1578344, by rfl⟩ : syracuseStep 2104459 = 3156689) B3156689
theorem B7102565 : Blo 2103435 7102565 := bbase (se 4 (by rfl) ⟨665865, by rfl⟩ : syracuseStep 7102565 = 1331731) (by norm_num)
theorem B4735043 : Blo 2103435 4735043 := bstep (se 1 (by rfl) ⟨3551282, by rfl⟩ : syracuseStep 4735043 = 7102565) B7102565
theorem B3156695 : Blo 2103435 3156695 := bstep (se 1 (by rfl) ⟨2367521, by rfl⟩ : syracuseStep 3156695 = 4735043) B4735043
theorem B2104463 : Blo 2103435 2104463 := bstep (se 1 (by rfl) ⟨1578347, by rfl⟩ : syracuseStep 2104463 = 3156695) B3156695
theorem B3156701 : Blo 2103435 3156701 := bbase (se 3 (by rfl) ⟨591881, by rfl⟩ : syracuseStep 3156701 = 1183763) (by norm_num)
theorem B2104467 : Blo 2103435 2104467 := bstep (se 1 (by rfl) ⟨1578350, by rfl⟩ : syracuseStep 2104467 = 3156701) B3156701
theorem B4735061 : Blo 2103435 4735061 := bbase (se 8 (by rfl) ⟨27744, by rfl⟩ : syracuseStep 4735061 = 55489) (by norm_num)
theorem B3156707 : Blo 2103435 3156707 := bstep (se 1 (by rfl) ⟨2367530, by rfl⟩ : syracuseStep 3156707 = 4735061) B4735061
theorem B2104471 : Blo 2103435 2104471 := bstep (se 1 (by rfl) ⟨1578353, by rfl⟩ : syracuseStep 2104471 = 3156707) B3156707
theorem B43197077 : Blo 2103435 43197077 := bbase (se 6 (by rfl) ⟨1012431, by rfl⟩ : syracuseStep 43197077 = 2024863) (by norm_num)
theorem B28798051 : Blo 2103435 28798051 := bstep (se 1 (by rfl) ⟨21598538, by rfl⟩ : syracuseStep 28798051 = 43197077) B43197077
theorem B38397401 : Blo 2103435 38397401 := bstep (se 2 (by rfl) ⟨14399025, by rfl⟩ : syracuseStep 38397401 = 28798051) B28798051
theorem B25598267 : Blo 2103435 25598267 := bstep (se 1 (by rfl) ⟨19198700, by rfl⟩ : syracuseStep 25598267 = 38397401) B38397401
theorem B17065511 : Blo 2103435 17065511 := bstep (se 1 (by rfl) ⟨12799133, by rfl⟩ : syracuseStep 17065511 = 25598267) B25598267
theorem B11377007 : Blo 2103435 11377007 := bstep (se 1 (by rfl) ⟨8532755, by rfl⟩ : syracuseStep 11377007 = 17065511) B17065511
theorem B7584671 : Blo 2103435 7584671 := bstep (se 1 (by rfl) ⟨5688503, by rfl⟩ : syracuseStep 7584671 = 11377007) B11377007
theorem B5056447 : Blo 2103435 5056447 := bstep (se 1 (by rfl) ⟨3792335, by rfl⟩ : syracuseStep 5056447 = 7584671) B7584671
theorem B6741929 : Blo 2103435 6741929 := bstep (se 2 (by rfl) ⟨2528223, by rfl⟩ : syracuseStep 6741929 = 5056447) B5056447
theorem B4494619 : Blo 2103435 4494619 := bstep (se 1 (by rfl) ⟨3370964, by rfl⟩ : syracuseStep 4494619 = 6741929) B6741929
theorem B5992825 : Blo 2103435 5992825 := bstep (se 2 (by rfl) ⟨2247309, by rfl⟩ : syracuseStep 5992825 = 4494619) B4494619
theorem B7990433 : Blo 2103435 7990433 := bstep (se 2 (by rfl) ⟨2996412, by rfl⟩ : syracuseStep 7990433 = 5992825) B5992825
theorem B5326955 : Blo 2103435 5326955 := bstep (se 1 (by rfl) ⟨3995216, by rfl⟩ : syracuseStep 5326955 = 7990433) B7990433
theorem B3551303 : Blo 2103435 3551303 := bstep (se 1 (by rfl) ⟨2663477, by rfl⟩ : syracuseStep 3551303 = 5326955) B5326955
theorem B2367535 : Blo 2103435 2367535 := bstep (se 1 (by rfl) ⟨1775651, by rfl⟩ : syracuseStep 2367535 = 3551303) B3551303
theorem B3156713 : Blo 2103435 3156713 := bstep (se 2 (by rfl) ⟨1183767, by rfl⟩ : syracuseStep 3156713 = 2367535) B2367535
theorem B2104475 : Blo 2103435 2104475 := bstep (se 1 (by rfl) ⟨1578356, by rfl⟩ : syracuseStep 2104475 = 3156713) B3156713
theorem B7199525 : Blo 2103435 7199525 := bbase (se 4 (by rfl) ⟨674955, by rfl⟩ : syracuseStep 7199525 = 1349911) (by norm_num)
theorem B4799683 : Blo 2103435 4799683 := bstep (se 1 (by rfl) ⟨3599762, by rfl⟩ : syracuseStep 4799683 = 7199525) B7199525
theorem B6399577 : Blo 2103435 6399577 := bstep (se 2 (by rfl) ⟨2399841, by rfl⟩ : syracuseStep 6399577 = 4799683) B4799683
theorem B8532769 : Blo 2103435 8532769 := bstep (se 2 (by rfl) ⟨3199788, by rfl⟩ : syracuseStep 8532769 = 6399577) B6399577
theorem B11377025 : Blo 2103435 11377025 := bstep (se 2 (by rfl) ⟨4266384, by rfl⟩ : syracuseStep 11377025 = 8532769) B8532769
theorem B7584683 : Blo 2103435 7584683 := bstep (se 1 (by rfl) ⟨5688512, by rfl⟩ : syracuseStep 7584683 = 11377025) B11377025
theorem B20225821 : Blo 2103435 20225821 := bstep (se 3 (by rfl) ⟨3792341, by rfl⟩ : syracuseStep 20225821 = 7584683) B7584683
theorem B26967761 : Blo 2103435 26967761 := bstep (se 2 (by rfl) ⟨10112910, by rfl⟩ : syracuseStep 26967761 = 20225821) B20225821
theorem B17978507 : Blo 2103435 17978507 := bstep (se 1 (by rfl) ⟨13483880, by rfl⟩ : syracuseStep 17978507 = 26967761) B26967761
theorem B11985671 : Blo 2103435 11985671 := bstep (se 1 (by rfl) ⟨8989253, by rfl⟩ : syracuseStep 11985671 = 17978507) B17978507
theorem B7990447 : Blo 2103435 7990447 := bstep (se 1 (by rfl) ⟨5992835, by rfl⟩ : syracuseStep 7990447 = 11985671) B11985671
theorem B10653929 : Blo 2103435 10653929 := bstep (se 2 (by rfl) ⟨3995223, by rfl⟩ : syracuseStep 10653929 = 7990447) B7990447
theorem B7102619 : Blo 2103435 7102619 := bstep (se 1 (by rfl) ⟨5326964, by rfl⟩ : syracuseStep 7102619 = 10653929) B10653929
theorem B4735079 : Blo 2103435 4735079 := bstep (se 1 (by rfl) ⟨3551309, by rfl⟩ : syracuseStep 4735079 = 7102619) B7102619
theorem B3156719 : Blo 2103435 3156719 := bstep (se 1 (by rfl) ⟨2367539, by rfl⟩ : syracuseStep 3156719 = 4735079) B4735079
theorem B2104479 : Blo 2103435 2104479 := bstep (se 1 (by rfl) ⟨1578359, by rfl⟩ : syracuseStep 2104479 = 3156719) B3156719
theorem B3156725 : Blo 2103435 3156725 := bbase (se 5 (by rfl) ⟨147971, by rfl⟩ : syracuseStep 3156725 = 295943) (by norm_num)
theorem B2104483 : Blo 2103435 2104483 := bstep (se 1 (by rfl) ⟨1578362, by rfl⟩ : syracuseStep 2104483 = 3156725) B3156725
theorem B2699833 : Blo 2103435 2699833 := bbase (se 2 (by rfl) ⟨1012437, by rfl⟩ : syracuseStep 2699833 = 2024875) (by norm_num)
theorem B3599777 : Blo 2103435 3599777 := bstep (se 2 (by rfl) ⟨1349916, by rfl⟩ : syracuseStep 3599777 = 2699833) B2699833
theorem B2399851 : Blo 2103435 2399851 := bstep (se 1 (by rfl) ⟨1799888, by rfl⟩ : syracuseStep 2399851 = 3599777) B3599777
theorem B12799205 : Blo 2103435 12799205 := bstep (se 4 (by rfl) ⟨1199925, by rfl⟩ : syracuseStep 12799205 = 2399851) B2399851
theorem B8532803 : Blo 2103435 8532803 := bstep (se 1 (by rfl) ⟨6399602, by rfl⟩ : syracuseStep 8532803 = 12799205) B12799205
theorem B22754141 : Blo 2103435 22754141 := bstep (se 3 (by rfl) ⟨4266401, by rfl⟩ : syracuseStep 22754141 = 8532803) B8532803
theorem B15169427 : Blo 2103435 15169427 := bstep (se 1 (by rfl) ⟨11377070, by rfl⟩ : syracuseStep 15169427 = 22754141) B22754141
theorem B10112951 : Blo 2103435 10112951 := bstep (se 1 (by rfl) ⟨7584713, by rfl⟩ : syracuseStep 10112951 = 15169427) B15169427
theorem B6741967 : Blo 2103435 6741967 := bstep (se 1 (by rfl) ⟨5056475, by rfl⟩ : syracuseStep 6741967 = 10112951) B10112951
theorem B8989289 : Blo 2103435 8989289 := bstep (se 2 (by rfl) ⟨3370983, by rfl⟩ : syracuseStep 8989289 = 6741967) B6741967
theorem B5992859 : Blo 2103435 5992859 := bstep (se 1 (by rfl) ⟨4494644, by rfl⟩ : syracuseStep 5992859 = 8989289) B8989289
theorem B3995239 : Blo 2103435 3995239 := bstep (se 1 (by rfl) ⟨2996429, by rfl⟩ : syracuseStep 3995239 = 5992859) B5992859
theorem B5326985 : Blo 2103435 5326985 := bstep (se 2 (by rfl) ⟨1997619, by rfl⟩ : syracuseStep 5326985 = 3995239) B3995239
theorem B3551323 : Blo 2103435 3551323 := bstep (se 1 (by rfl) ⟨2663492, by rfl⟩ : syracuseStep 3551323 = 5326985) B5326985
theorem B4735097 : Blo 2103435 4735097 := bstep (se 2 (by rfl) ⟨1775661, by rfl⟩ : syracuseStep 4735097 = 3551323) B3551323
theorem B3156731 : Blo 2103435 3156731 := bstep (se 1 (by rfl) ⟨2367548, by rfl⟩ : syracuseStep 3156731 = 4735097) B4735097
theorem B2104487 : Blo 2103435 2104487 := bstep (se 1 (by rfl) ⟨1578365, by rfl⟩ : syracuseStep 2104487 = 3156731) B3156731
theorem B2367553 : Blo 2103435 2367553 := bbase (se 2 (by rfl) ⟨887832, by rfl⟩ : syracuseStep 2367553 = 1775665) (by norm_num)
theorem B3156737 : Blo 2103435 3156737 := bstep (se 2 (by rfl) ⟨1183776, by rfl⟩ : syracuseStep 3156737 = 2367553) B2367553
theorem B2104491 : Blo 2103435 2104491 := bstep (se 1 (by rfl) ⟨1578368, by rfl⟩ : syracuseStep 2104491 = 3156737) B3156737
theorem B5327005 : Blo 2103435 5327005 := bbase (se 3 (by rfl) ⟨998813, by rfl⟩ : syracuseStep 5327005 = 1997627) (by norm_num)
theorem B7102673 : Blo 2103435 7102673 := bstep (se 2 (by rfl) ⟨2663502, by rfl⟩ : syracuseStep 7102673 = 5327005) B5327005
theorem B4735115 : Blo 2103435 4735115 := bstep (se 1 (by rfl) ⟨3551336, by rfl⟩ : syracuseStep 4735115 = 7102673) B7102673
theorem B3156743 : Blo 2103435 3156743 := bstep (se 1 (by rfl) ⟨2367557, by rfl⟩ : syracuseStep 3156743 = 4735115) B4735115
theorem B2104495 : Blo 2103435 2104495 := bstep (se 1 (by rfl) ⟨1578371, by rfl⟩ : syracuseStep 2104495 = 3156743) B3156743
theorem B3156749 : Blo 2103435 3156749 := bbase (se 3 (by rfl) ⟨591890, by rfl⟩ : syracuseStep 3156749 = 1183781) (by norm_num)
theorem B2104499 : Blo 2103435 2104499 := bstep (se 1 (by rfl) ⟨1578374, by rfl⟩ : syracuseStep 2104499 = 3156749) B3156749
theorem B4735133 : Blo 2103435 4735133 := bbase (se 3 (by rfl) ⟨887837, by rfl⟩ : syracuseStep 4735133 = 1775675) (by norm_num)
theorem B3156755 : Blo 2103435 3156755 := bstep (se 1 (by rfl) ⟨2367566, by rfl⟩ : syracuseStep 3156755 = 4735133) B4735133
theorem B2104503 : Blo 2103435 2104503 := bstep (se 1 (by rfl) ⟨1578377, by rfl⟩ : syracuseStep 2104503 = 3156755) B3156755
theorem B3551357 : Blo 2103435 3551357 := bbase (se 3 (by rfl) ⟨665879, by rfl⟩ : syracuseStep 3551357 = 1331759) (by norm_num)
theorem B2367571 : Blo 2103435 2367571 := bstep (se 1 (by rfl) ⟨1775678, by rfl⟩ : syracuseStep 2367571 = 3551357) B3551357
theorem B3156761 : Blo 2103435 3156761 := bstep (se 2 (by rfl) ⟨1183785, by rfl⟩ : syracuseStep 3156761 = 2367571) B2367571
theorem B2104507 : Blo 2103435 2104507 := bstep (se 1 (by rfl) ⟨1578380, by rfl⟩ : syracuseStep 2104507 = 3156761) B3156761
theorem B3844141 : Blo 2103435 3844141 := bbase (se 3 (by rfl) ⟨720776, by rfl⟩ : syracuseStep 3844141 = 1441553) (by norm_num)
theorem B20502085 : Blo 2103435 20502085 := bstep (se 4 (by rfl) ⟨1922070, by rfl⟩ : syracuseStep 20502085 = 3844141) B3844141
theorem B27336113 : Blo 2103435 27336113 := bstep (se 2 (by rfl) ⟨10251042, by rfl⟩ : syracuseStep 27336113 = 20502085) B20502085
theorem B18224075 : Blo 2103435 18224075 := bstep (se 1 (by rfl) ⟨13668056, by rfl⟩ : syracuseStep 18224075 = 27336113) B27336113
theorem B48597533 : Blo 2103435 48597533 := bstep (se 3 (by rfl) ⟨9112037, by rfl⟩ : syracuseStep 48597533 = 18224075) B18224075
theorem B32398355 : Blo 2103435 32398355 := bstep (se 1 (by rfl) ⟨24298766, by rfl⟩ : syracuseStep 32398355 = 48597533) B48597533
theorem B21598903 : Blo 2103435 21598903 := bstep (se 1 (by rfl) ⟨16199177, by rfl⟩ : syracuseStep 21598903 = 32398355) B32398355
theorem B28798537 : Blo 2103435 28798537 := bstep (se 2 (by rfl) ⟨10799451, by rfl⟩ : syracuseStep 28798537 = 21598903) B21598903
theorem B38398049 : Blo 2103435 38398049 := bstep (se 2 (by rfl) ⟨14399268, by rfl⟩ : syracuseStep 38398049 = 28798537) B28798537
theorem B25598699 : Blo 2103435 25598699 := bstep (se 1 (by rfl) ⟨19199024, by rfl⟩ : syracuseStep 25598699 = 38398049) B38398049
theorem B17065799 : Blo 2103435 17065799 := bstep (se 1 (by rfl) ⟨12799349, by rfl⟩ : syracuseStep 17065799 = 25598699) B25598699
theorem B11377199 : Blo 2103435 11377199 := bstep (se 1 (by rfl) ⟨8532899, by rfl⟩ : syracuseStep 11377199 = 17065799) B17065799
theorem B7584799 : Blo 2103435 7584799 := bstep (se 1 (by rfl) ⟨5688599, by rfl⟩ : syracuseStep 7584799 = 11377199) B11377199
theorem B10113065 : Blo 2103435 10113065 := bstep (se 2 (by rfl) ⟨3792399, by rfl⟩ : syracuseStep 10113065 = 7584799) B7584799
theorem B6742043 : Blo 2103435 6742043 := bstep (se 1 (by rfl) ⟨5056532, by rfl⟩ : syracuseStep 6742043 = 10113065) B10113065
theorem B4494695 : Blo 2103435 4494695 := bstep (se 1 (by rfl) ⟨3371021, by rfl⟩ : syracuseStep 4494695 = 6742043) B6742043
theorem B11985853 : Blo 2103435 11985853 := bstep (se 3 (by rfl) ⟨2247347, by rfl⟩ : syracuseStep 11985853 = 4494695) B4494695
theorem B15981137 : Blo 2103435 15981137 := bstep (se 2 (by rfl) ⟨5992926, by rfl⟩ : syracuseStep 15981137 = 11985853) B11985853
theorem B10654091 : Blo 2103435 10654091 := bstep (se 1 (by rfl) ⟨7990568, by rfl⟩ : syracuseStep 10654091 = 15981137) B15981137
theorem B7102727 : Blo 2103435 7102727 := bstep (se 1 (by rfl) ⟨5327045, by rfl⟩ : syracuseStep 7102727 = 10654091) B10654091
theorem B4735151 : Blo 2103435 4735151 := bstep (se 1 (by rfl) ⟨3551363, by rfl⟩ : syracuseStep 4735151 = 7102727) B7102727
theorem B3156767 : Blo 2103435 3156767 := bstep (se 1 (by rfl) ⟨2367575, by rfl⟩ : syracuseStep 3156767 = 4735151) B4735151
theorem B2104511 : Blo 2103435 2104511 := bstep (se 1 (by rfl) ⟨1578383, by rfl⟩ : syracuseStep 2104511 = 3156767) B3156767
theorem B3156773 : Blo 2103435 3156773 := bbase (se 4 (by rfl) ⟨295947, by rfl⟩ : syracuseStep 3156773 = 591895) (by norm_num)
theorem B2104515 : Blo 2103435 2104515 := bstep (se 1 (by rfl) ⟨1578386, by rfl⟩ : syracuseStep 2104515 = 3156773) B3156773
theorem B2663533 : Blo 2103435 2663533 := bbase (se 3 (by rfl) ⟨499412, by rfl⟩ : syracuseStep 2663533 = 998825) (by norm_num)
theorem B3551377 : Blo 2103435 3551377 := bstep (se 2 (by rfl) ⟨1331766, by rfl⟩ : syracuseStep 3551377 = 2663533) B2663533
theorem B4735169 : Blo 2103435 4735169 := bstep (se 2 (by rfl) ⟨1775688, by rfl⟩ : syracuseStep 4735169 = 3551377) B3551377
theorem B3156779 : Blo 2103435 3156779 := bstep (se 1 (by rfl) ⟨2367584, by rfl⟩ : syracuseStep 3156779 = 4735169) B4735169
theorem B2104519 : Blo 2103435 2104519 := bstep (se 1 (by rfl) ⟨1578389, by rfl⟩ : syracuseStep 2104519 = 3156779) B3156779
theorem B2367589 : Blo 2103435 2367589 := bbase (se 4 (by rfl) ⟨221961, by rfl⟩ : syracuseStep 2367589 = 443923) (by norm_num)
theorem B3156785 : Blo 2103435 3156785 := bstep (se 2 (by rfl) ⟨1183794, by rfl⟩ : syracuseStep 3156785 = 2367589) B2367589
theorem B2104523 : Blo 2103435 2104523 := bstep (se 1 (by rfl) ⟨1578392, by rfl⟩ : syracuseStep 2104523 = 3156785) B3156785
theorem B2247365 : Blo 2103435 2247365 := bbase (se 4 (by rfl) ⟨210690, by rfl⟩ : syracuseStep 2247365 = 421381) (by norm_num)
theorem B5992973 : Blo 2103435 5992973 := bstep (se 3 (by rfl) ⟨1123682, by rfl⟩ : syracuseStep 5992973 = 2247365) B2247365
theorem B3995315 : Blo 2103435 3995315 := bstep (se 1 (by rfl) ⟨2996486, by rfl⟩ : syracuseStep 3995315 = 5992973) B5992973
theorem B2663543 : Blo 2103435 2663543 := bstep (se 1 (by rfl) ⟨1997657, by rfl⟩ : syracuseStep 2663543 = 3995315) B3995315
theorem B7102781 : Blo 2103435 7102781 := bstep (se 3 (by rfl) ⟨1331771, by rfl⟩ : syracuseStep 7102781 = 2663543) B2663543
theorem B4735187 : Blo 2103435 4735187 := bstep (se 1 (by rfl) ⟨3551390, by rfl⟩ : syracuseStep 4735187 = 7102781) B7102781
theorem B3156791 : Blo 2103435 3156791 := bstep (se 1 (by rfl) ⟨2367593, by rfl⟩ : syracuseStep 3156791 = 4735187) B4735187
theorem B2104527 : Blo 2103435 2104527 := bstep (se 1 (by rfl) ⟨1578395, by rfl⟩ : syracuseStep 2104527 = 3156791) B3156791
theorem B3156797 : Blo 2103435 3156797 := bbase (se 3 (by rfl) ⟨591899, by rfl⟩ : syracuseStep 3156797 = 1183799) (by norm_num)
theorem B2104531 : Blo 2103435 2104531 := bstep (se 1 (by rfl) ⟨1578398, by rfl⟩ : syracuseStep 2104531 = 3156797) B3156797
theorem B4735205 : Blo 2103435 4735205 := bbase (se 4 (by rfl) ⟨443925, by rfl⟩ : syracuseStep 4735205 = 887851) (by norm_num)
theorem B3156803 : Blo 2103435 3156803 := bstep (se 1 (by rfl) ⟨2367602, by rfl⟩ : syracuseStep 3156803 = 4735205) B4735205
theorem B2104535 : Blo 2103435 2104535 := bstep (se 1 (by rfl) ⟨1578401, by rfl⟩ : syracuseStep 2104535 = 3156803) B3156803
theorem B5327117 : Blo 2103435 5327117 := bbase (se 3 (by rfl) ⟨998834, by rfl⟩ : syracuseStep 5327117 = 1997669) (by norm_num)
theorem B3551411 : Blo 2103435 3551411 := bstep (se 1 (by rfl) ⟨2663558, by rfl⟩ : syracuseStep 3551411 = 5327117) B5327117
theorem B2367607 : Blo 2103435 2367607 := bstep (se 1 (by rfl) ⟨1775705, by rfl⟩ : syracuseStep 2367607 = 3551411) B3551411
theorem B3156809 : Blo 2103435 3156809 := bstep (se 2 (by rfl) ⟨1183803, by rfl⟩ : syracuseStep 3156809 = 2367607) B2367607
theorem B2104539 : Blo 2103435 2104539 := bstep (se 1 (by rfl) ⟨1578404, by rfl⟩ : syracuseStep 2104539 = 3156809) B3156809
theorem B2996509 : Blo 2103435 2996509 := bbase (se 3 (by rfl) ⟨561845, by rfl⟩ : syracuseStep 2996509 = 1123691) (by norm_num)
theorem B3995345 : Blo 2103435 3995345 := bstep (se 2 (by rfl) ⟨1498254, by rfl⟩ : syracuseStep 3995345 = 2996509) B2996509
theorem B10654253 : Blo 2103435 10654253 := bstep (se 3 (by rfl) ⟨1997672, by rfl⟩ : syracuseStep 10654253 = 3995345) B3995345
theorem B7102835 : Blo 2103435 7102835 := bstep (se 1 (by rfl) ⟨5327126, by rfl⟩ : syracuseStep 7102835 = 10654253) B10654253
theorem B4735223 : Blo 2103435 4735223 := bstep (se 1 (by rfl) ⟨3551417, by rfl⟩ : syracuseStep 4735223 = 7102835) B7102835
theorem B3156815 : Blo 2103435 3156815 := bstep (se 1 (by rfl) ⟨2367611, by rfl⟩ : syracuseStep 3156815 = 4735223) B4735223
theorem B2104543 : Blo 2103435 2104543 := bstep (se 1 (by rfl) ⟨1578407, by rfl⟩ : syracuseStep 2104543 = 3156815) B3156815
theorem B3156821 : Blo 2103435 3156821 := bbase (se 9 (by rfl) ⟨9248, by rfl⟩ : syracuseStep 3156821 = 18497) (by norm_num)
theorem B2104547 : Blo 2103435 2104547 := bstep (se 1 (by rfl) ⟨1578410, by rfl⟩ : syracuseStep 2104547 = 3156821) B3156821
theorem B4494781 : Blo 2103435 4494781 := bbase (se 3 (by rfl) ⟨842771, by rfl⟩ : syracuseStep 4494781 = 1685543) (by norm_num)
theorem B5993041 : Blo 2103435 5993041 := bstep (se 2 (by rfl) ⟨2247390, by rfl⟩ : syracuseStep 5993041 = 4494781) B4494781
theorem B7990721 : Blo 2103435 7990721 := bstep (se 2 (by rfl) ⟨2996520, by rfl⟩ : syracuseStep 7990721 = 5993041) B5993041
theorem B5327147 : Blo 2103435 5327147 := bstep (se 1 (by rfl) ⟨3995360, by rfl⟩ : syracuseStep 5327147 = 7990721) B7990721
theorem B3551431 : Blo 2103435 3551431 := bstep (se 1 (by rfl) ⟨2663573, by rfl⟩ : syracuseStep 3551431 = 5327147) B5327147
theorem B4735241 : Blo 2103435 4735241 := bstep (se 2 (by rfl) ⟨1775715, by rfl⟩ : syracuseStep 4735241 = 3551431) B3551431
theorem B3156827 : Blo 2103435 3156827 := bstep (se 1 (by rfl) ⟨2367620, by rfl⟩ : syracuseStep 3156827 = 4735241) B4735241
theorem B2104551 : Blo 2103435 2104551 := bstep (se 1 (by rfl) ⟨1578413, by rfl⟩ : syracuseStep 2104551 = 3156827) B3156827
theorem B2367625 : Blo 2103435 2367625 := bbase (se 2 (by rfl) ⟨887859, by rfl⟩ : syracuseStep 2367625 = 1775719) (by norm_num)
theorem B3156833 : Blo 2103435 3156833 := bstep (se 2 (by rfl) ⟨1183812, by rfl⟩ : syracuseStep 3156833 = 2367625) B2367625
theorem B2104555 : Blo 2103435 2104555 := bstep (se 1 (by rfl) ⟨1578416, by rfl⟩ : syracuseStep 2104555 = 3156833) B3156833
theorem B34132373 : Blo 2103435 34132373 := bbase (se 6 (by rfl) ⟨799977, by rfl⟩ : syracuseStep 34132373 = 1599955) (by norm_num)
theorem B22754915 : Blo 2103435 22754915 := bstep (se 1 (by rfl) ⟨17066186, by rfl⟩ : syracuseStep 22754915 = 34132373) B34132373
theorem B15169943 : Blo 2103435 15169943 := bstep (se 1 (by rfl) ⟨11377457, by rfl⟩ : syracuseStep 15169943 = 22754915) B22754915
theorem B40453181 : Blo 2103435 40453181 := bstep (se 3 (by rfl) ⟨7584971, by rfl⟩ : syracuseStep 40453181 = 15169943) B15169943
theorem B26968787 : Blo 2103435 26968787 := bstep (se 1 (by rfl) ⟨20226590, by rfl⟩ : syracuseStep 26968787 = 40453181) B40453181
theorem B17979191 : Blo 2103435 17979191 := bstep (se 1 (by rfl) ⟨13484393, by rfl⟩ : syracuseStep 17979191 = 26968787) B26968787
theorem B11986127 : Blo 2103435 11986127 := bstep (se 1 (by rfl) ⟨8989595, by rfl⟩ : syracuseStep 11986127 = 17979191) B17979191
theorem B7990751 : Blo 2103435 7990751 := bstep (se 1 (by rfl) ⟨5993063, by rfl⟩ : syracuseStep 7990751 = 11986127) B11986127
theorem B5327167 : Blo 2103435 5327167 := bstep (se 1 (by rfl) ⟨3995375, by rfl⟩ : syracuseStep 5327167 = 7990751) B7990751
theorem B7102889 : Blo 2103435 7102889 := bstep (se 2 (by rfl) ⟨2663583, by rfl⟩ : syracuseStep 7102889 = 5327167) B5327167
theorem B4735259 : Blo 2103435 4735259 := bstep (se 1 (by rfl) ⟨3551444, by rfl⟩ : syracuseStep 4735259 = 7102889) B7102889
theorem B3156839 : Blo 2103435 3156839 := bstep (se 1 (by rfl) ⟨2367629, by rfl⟩ : syracuseStep 3156839 = 4735259) B4735259
theorem B2104559 : Blo 2103435 2104559 := bstep (se 1 (by rfl) ⟨1578419, by rfl⟩ : syracuseStep 2104559 = 3156839) B3156839
theorem B3156845 : Blo 2103435 3156845 := bbase (se 3 (by rfl) ⟨591908, by rfl⟩ : syracuseStep 3156845 = 1183817) (by norm_num)
theorem B2104563 : Blo 2103435 2104563 := bstep (se 1 (by rfl) ⟨1578422, by rfl⟩ : syracuseStep 2104563 = 3156845) B3156845
theorem B4735277 : Blo 2103435 4735277 := bbase (se 3 (by rfl) ⟨887864, by rfl⟩ : syracuseStep 4735277 = 1775729) (by norm_num)
theorem B3156851 : Blo 2103435 3156851 := bstep (se 1 (by rfl) ⟨2367638, by rfl⟩ : syracuseStep 3156851 = 4735277) B4735277
theorem B2104567 : Blo 2103435 2104567 := bstep (se 1 (by rfl) ⟨1578425, by rfl⟩ : syracuseStep 2104567 = 3156851) B3156851
theorem B3792509 : Blo 2103435 3792509 := bbase (se 3 (by rfl) ⟨711095, by rfl⟩ : syracuseStep 3792509 = 1422191) (by norm_num)
theorem B2528339 : Blo 2103435 2528339 := bstep (se 1 (by rfl) ⟨1896254, by rfl⟩ : syracuseStep 2528339 = 3792509) B3792509
theorem B6742237 : Blo 2103435 6742237 := bstep (se 3 (by rfl) ⟨1264169, by rfl⟩ : syracuseStep 6742237 = 2528339) B2528339
theorem B8989649 : Blo 2103435 8989649 := bstep (se 2 (by rfl) ⟨3371118, by rfl⟩ : syracuseStep 8989649 = 6742237) B6742237
theorem B5993099 : Blo 2103435 5993099 := bstep (se 1 (by rfl) ⟨4494824, by rfl⟩ : syracuseStep 5993099 = 8989649) B8989649
theorem B3995399 : Blo 2103435 3995399 := bstep (se 1 (by rfl) ⟨2996549, by rfl⟩ : syracuseStep 3995399 = 5993099) B5993099
theorem B2663599 : Blo 2103435 2663599 := bstep (se 1 (by rfl) ⟨1997699, by rfl⟩ : syracuseStep 2663599 = 3995399) B3995399
theorem B3551465 : Blo 2103435 3551465 := bstep (se 2 (by rfl) ⟨1331799, by rfl⟩ : syracuseStep 3551465 = 2663599) B2663599
theorem B2367643 : Blo 2103435 2367643 := bstep (se 1 (by rfl) ⟨1775732, by rfl⟩ : syracuseStep 2367643 = 3551465) B3551465
theorem B3156857 : Blo 2103435 3156857 := bstep (se 2 (by rfl) ⟨1183821, by rfl⟩ : syracuseStep 3156857 = 2367643) B2367643
theorem B2104571 : Blo 2103435 2104571 := bstep (se 1 (by rfl) ⟨1578428, by rfl⟩ : syracuseStep 2104571 = 3156857) B3156857
theorem B19199605 : Blo 2103435 19199605 := bbase (se 5 (by rfl) ⟨899981, by rfl⟩ : syracuseStep 19199605 = 1799963) (by norm_num)
theorem B25599473 : Blo 2103435 25599473 := bstep (se 2 (by rfl) ⟨9599802, by rfl⟩ : syracuseStep 25599473 = 19199605) B19199605
theorem B17066315 : Blo 2103435 17066315 := bstep (se 1 (by rfl) ⟨12799736, by rfl⟩ : syracuseStep 17066315 = 25599473) B25599473
theorem B45510173 : Blo 2103435 45510173 := bstep (se 3 (by rfl) ⟨8533157, by rfl⟩ : syracuseStep 45510173 = 17066315) B17066315
theorem B30340115 : Blo 2103435 30340115 := bstep (se 1 (by rfl) ⟨22755086, by rfl⟩ : syracuseStep 30340115 = 45510173) B45510173
theorem B20226743 : Blo 2103435 20226743 := bstep (se 1 (by rfl) ⟨15170057, by rfl⟩ : syracuseStep 20226743 = 30340115) B30340115
theorem B13484495 : Blo 2103435 13484495 := bstep (se 1 (by rfl) ⟨10113371, by rfl⟩ : syracuseStep 13484495 = 20226743) B20226743
theorem B35958653 : Blo 2103435 35958653 := bstep (se 3 (by rfl) ⟨6742247, by rfl⟩ : syracuseStep 35958653 = 13484495) B13484495
theorem B23972435 : Blo 2103435 23972435 := bstep (se 1 (by rfl) ⟨17979326, by rfl⟩ : syracuseStep 23972435 = 35958653) B35958653
theorem B15981623 : Blo 2103435 15981623 := bstep (se 1 (by rfl) ⟨11986217, by rfl⟩ : syracuseStep 15981623 = 23972435) B23972435
theorem B10654415 : Blo 2103435 10654415 := bstep (se 1 (by rfl) ⟨7990811, by rfl⟩ : syracuseStep 10654415 = 15981623) B15981623
theorem B7102943 : Blo 2103435 7102943 := bstep (se 1 (by rfl) ⟨5327207, by rfl⟩ : syracuseStep 7102943 = 10654415) B10654415
theorem B4735295 : Blo 2103435 4735295 := bstep (se 1 (by rfl) ⟨3551471, by rfl⟩ : syracuseStep 4735295 = 7102943) B7102943
theorem B3156863 : Blo 2103435 3156863 := bstep (se 1 (by rfl) ⟨2367647, by rfl⟩ : syracuseStep 3156863 = 4735295) B4735295
theorem B2104575 : Blo 2103435 2104575 := bstep (se 1 (by rfl) ⟨1578431, by rfl⟩ : syracuseStep 2104575 = 3156863) B3156863
theorem B3156869 : Blo 2103435 3156869 := bbase (se 4 (by rfl) ⟨295956, by rfl⟩ : syracuseStep 3156869 = 591913) (by norm_num)
theorem B2104579 : Blo 2103435 2104579 := bstep (se 1 (by rfl) ⟨1578434, by rfl⟩ : syracuseStep 2104579 = 3156869) B3156869
theorem B3551485 : Blo 2103435 3551485 := bbase (se 3 (by rfl) ⟨665903, by rfl⟩ : syracuseStep 3551485 = 1331807) (by norm_num)
theorem B4735313 : Blo 2103435 4735313 := bstep (se 2 (by rfl) ⟨1775742, by rfl⟩ : syracuseStep 4735313 = 3551485) B3551485
theorem B3156875 : Blo 2103435 3156875 := bstep (se 1 (by rfl) ⟨2367656, by rfl⟩ : syracuseStep 3156875 = 4735313) B4735313
theorem B2104583 : Blo 2103435 2104583 := bstep (se 1 (by rfl) ⟨1578437, by rfl⟩ : syracuseStep 2104583 = 3156875) B3156875
theorem B2367661 : Blo 2103435 2367661 := bbase (se 3 (by rfl) ⟨443936, by rfl⟩ : syracuseStep 2367661 = 887873) (by norm_num)
theorem B3156881 : Blo 2103435 3156881 := bstep (se 2 (by rfl) ⟨1183830, by rfl⟩ : syracuseStep 3156881 = 2367661) B2367661
theorem B2104587 : Blo 2103435 2104587 := bstep (se 1 (by rfl) ⟨1578440, by rfl⟩ : syracuseStep 2104587 = 3156881) B3156881
theorem B7102997 : Blo 2103435 7102997 := bbase (se 6 (by rfl) ⟨166476, by rfl⟩ : syracuseStep 7102997 = 332953) (by norm_num)
theorem B4735331 : Blo 2103435 4735331 := bstep (se 1 (by rfl) ⟨3551498, by rfl⟩ : syracuseStep 4735331 = 7102997) B7102997
theorem B3156887 : Blo 2103435 3156887 := bstep (se 1 (by rfl) ⟨2367665, by rfl⟩ : syracuseStep 3156887 = 4735331) B4735331
theorem B2104591 : Blo 2103435 2104591 := bstep (se 1 (by rfl) ⟨1578443, by rfl⟩ : syracuseStep 2104591 = 3156887) B3156887
theorem B3156893 : Blo 2103435 3156893 := bbase (se 3 (by rfl) ⟨591917, by rfl⟩ : syracuseStep 3156893 = 1183835) (by norm_num)
theorem B2104595 : Blo 2103435 2104595 := bstep (se 1 (by rfl) ⟨1578446, by rfl⟩ : syracuseStep 2104595 = 3156893) B3156893
theorem B4735349 : Blo 2103435 4735349 := bbase (se 5 (by rfl) ⟨221969, by rfl⟩ : syracuseStep 4735349 = 443939) (by norm_num)
theorem B3156899 : Blo 2103435 3156899 := bstep (se 1 (by rfl) ⟨2367674, by rfl⟩ : syracuseStep 3156899 = 4735349) B4735349
theorem B2104599 : Blo 2103435 2104599 := bstep (se 1 (by rfl) ⟨1578449, by rfl⟩ : syracuseStep 2104599 = 3156899) B3156899
theorem B2528377 : Blo 2103435 2528377 := bbase (se 2 (by rfl) ⟨948141, by rfl⟩ : syracuseStep 2528377 = 1896283) (by norm_num)
theorem B13484677 : Blo 2103435 13484677 := bstep (se 4 (by rfl) ⟨1264188, by rfl⟩ : syracuseStep 13484677 = 2528377) B2528377
theorem B17979569 : Blo 2103435 17979569 := bstep (se 2 (by rfl) ⟨6742338, by rfl⟩ : syracuseStep 17979569 = 13484677) B13484677
theorem B11986379 : Blo 2103435 11986379 := bstep (se 1 (by rfl) ⟨8989784, by rfl⟩ : syracuseStep 11986379 = 17979569) B17979569
theorem B7990919 : Blo 2103435 7990919 := bstep (se 1 (by rfl) ⟨5993189, by rfl⟩ : syracuseStep 7990919 = 11986379) B11986379
theorem B5327279 : Blo 2103435 5327279 := bstep (se 1 (by rfl) ⟨3995459, by rfl⟩ : syracuseStep 5327279 = 7990919) B7990919
theorem B3551519 : Blo 2103435 3551519 := bstep (se 1 (by rfl) ⟨2663639, by rfl⟩ : syracuseStep 3551519 = 5327279) B5327279
theorem B2367679 : Blo 2103435 2367679 := bstep (se 1 (by rfl) ⟨1775759, by rfl⟩ : syracuseStep 2367679 = 3551519) B3551519
theorem B3156905 : Blo 2103435 3156905 := bstep (se 2 (by rfl) ⟨1183839, by rfl⟩ : syracuseStep 3156905 = 2367679) B2367679
theorem B2104603 : Blo 2103435 2104603 := bstep (se 1 (by rfl) ⟨1578452, by rfl⟩ : syracuseStep 2104603 = 3156905) B3156905
theorem B7990933 : Blo 2103435 7990933 := bbase (se 6 (by rfl) ⟨187287, by rfl⟩ : syracuseStep 7990933 = 374575) (by norm_num)
theorem B10654577 : Blo 2103435 10654577 := bstep (se 2 (by rfl) ⟨3995466, by rfl⟩ : syracuseStep 10654577 = 7990933) B7990933
theorem B7103051 : Blo 2103435 7103051 := bstep (se 1 (by rfl) ⟨5327288, by rfl⟩ : syracuseStep 7103051 = 10654577) B10654577
theorem B4735367 : Blo 2103435 4735367 := bstep (se 1 (by rfl) ⟨3551525, by rfl⟩ : syracuseStep 4735367 = 7103051) B7103051
theorem B3156911 : Blo 2103435 3156911 := bstep (se 1 (by rfl) ⟨2367683, by rfl⟩ : syracuseStep 3156911 = 4735367) B4735367
theorem B2104607 : Blo 2103435 2104607 := bstep (se 1 (by rfl) ⟨1578455, by rfl⟩ : syracuseStep 2104607 = 3156911) B3156911
theorem B3156917 : Blo 2103435 3156917 := bbase (se 5 (by rfl) ⟨147980, by rfl⟩ : syracuseStep 3156917 = 295961) (by norm_num)
theorem B2104611 : Blo 2103435 2104611 := bstep (se 1 (by rfl) ⟨1578458, by rfl⟩ : syracuseStep 2104611 = 3156917) B3156917
theorem B5327309 : Blo 2103435 5327309 := bbase (se 3 (by rfl) ⟨998870, by rfl⟩ : syracuseStep 5327309 = 1997741) (by norm_num)
theorem B3551539 : Blo 2103435 3551539 := bstep (se 1 (by rfl) ⟨2663654, by rfl⟩ : syracuseStep 3551539 = 5327309) B5327309
theorem B4735385 : Blo 2103435 4735385 := bstep (se 2 (by rfl) ⟨1775769, by rfl⟩ : syracuseStep 4735385 = 3551539) B3551539
theorem B3156923 : Blo 2103435 3156923 := bstep (se 1 (by rfl) ⟨2367692, by rfl⟩ : syracuseStep 3156923 = 4735385) B4735385
theorem B2104615 : Blo 2103435 2104615 := bstep (se 1 (by rfl) ⟨1578461, by rfl⟩ : syracuseStep 2104615 = 3156923) B3156923
theorem B2367697 : Blo 2103435 2367697 := bbase (se 2 (by rfl) ⟨887886, by rfl⟩ : syracuseStep 2367697 = 1775773) (by norm_num)
theorem B3156929 : Blo 2103435 3156929 := bstep (se 2 (by rfl) ⟨1183848, by rfl⟩ : syracuseStep 3156929 = 2367697) B2367697
theorem B2104619 : Blo 2103435 2104619 := bstep (se 1 (by rfl) ⟨1578464, by rfl⟩ : syracuseStep 2104619 = 3156929) B3156929
theorem B10113605 : Blo 2103435 10113605 := bbase (se 4 (by rfl) ⟨948150, by rfl⟩ : syracuseStep 10113605 = 1896301) (by norm_num)
theorem B6742403 : Blo 2103435 6742403 := bstep (se 1 (by rfl) ⟨5056802, by rfl⟩ : syracuseStep 6742403 = 10113605) B10113605
theorem B4494935 : Blo 2103435 4494935 := bstep (se 1 (by rfl) ⟨3371201, by rfl⟩ : syracuseStep 4494935 = 6742403) B6742403
theorem B2996623 : Blo 2103435 2996623 := bstep (se 1 (by rfl) ⟨2247467, by rfl⟩ : syracuseStep 2996623 = 4494935) B4494935
theorem B3995497 : Blo 2103435 3995497 := bstep (se 2 (by rfl) ⟨1498311, by rfl⟩ : syracuseStep 3995497 = 2996623) B2996623
theorem B5327329 : Blo 2103435 5327329 := bstep (se 2 (by rfl) ⟨1997748, by rfl⟩ : syracuseStep 5327329 = 3995497) B3995497
theorem B7103105 : Blo 2103435 7103105 := bstep (se 2 (by rfl) ⟨2663664, by rfl⟩ : syracuseStep 7103105 = 5327329) B5327329
theorem B4735403 : Blo 2103435 4735403 := bstep (se 1 (by rfl) ⟨3551552, by rfl⟩ : syracuseStep 4735403 = 7103105) B7103105
theorem B3156935 : Blo 2103435 3156935 := bstep (se 1 (by rfl) ⟨2367701, by rfl⟩ : syracuseStep 3156935 = 4735403) B4735403
theorem B2104623 : Blo 2103435 2104623 := bstep (se 1 (by rfl) ⟨1578467, by rfl⟩ : syracuseStep 2104623 = 3156935) B3156935
theorem B3156941 : Blo 2103435 3156941 := bbase (se 3 (by rfl) ⟨591926, by rfl⟩ : syracuseStep 3156941 = 1183853) (by norm_num)
theorem B2104627 : Blo 2103435 2104627 := bstep (se 1 (by rfl) ⟨1578470, by rfl⟩ : syracuseStep 2104627 = 3156941) B3156941
theorem B4735421 : Blo 2103435 4735421 := bbase (se 3 (by rfl) ⟨887891, by rfl⟩ : syracuseStep 4735421 = 1775783) (by norm_num)
theorem B3156947 : Blo 2103435 3156947 := bstep (se 1 (by rfl) ⟨2367710, by rfl⟩ : syracuseStep 3156947 = 4735421) B4735421
theorem B2104631 : Blo 2103435 2104631 := bstep (se 1 (by rfl) ⟨1578473, by rfl⟩ : syracuseStep 2104631 = 3156947) B3156947
theorem B3551573 : Blo 2103435 3551573 := bbase (se 10 (by rfl) ⟨5202, by rfl⟩ : syracuseStep 3551573 = 10405) (by norm_num)
theorem B2367715 : Blo 2103435 2367715 := bstep (se 1 (by rfl) ⟨1775786, by rfl⟩ : syracuseStep 2367715 = 3551573) B3551573
theorem B3156953 : Blo 2103435 3156953 := bstep (se 2 (by rfl) ⟨1183857, by rfl⟩ : syracuseStep 3156953 = 2367715) B2367715
theorem B2104635 : Blo 2103435 2104635 := bstep (se 1 (by rfl) ⟨1578476, by rfl⟩ : syracuseStep 2104635 = 3156953) B3156953
theorem B6742453 : Blo 2103435 6742453 := bbase (se 5 (by rfl) ⟨316052, by rfl⟩ : syracuseStep 6742453 = 632105) (by norm_num)
theorem B8989937 : Blo 2103435 8989937 := bstep (se 2 (by rfl) ⟨3371226, by rfl⟩ : syracuseStep 8989937 = 6742453) B6742453
theorem B5993291 : Blo 2103435 5993291 := bstep (se 1 (by rfl) ⟨4494968, by rfl⟩ : syracuseStep 5993291 = 8989937) B8989937
theorem B15982109 : Blo 2103435 15982109 := bstep (se 3 (by rfl) ⟨2996645, by rfl⟩ : syracuseStep 15982109 = 5993291) B5993291
theorem B10654739 : Blo 2103435 10654739 := bstep (se 1 (by rfl) ⟨7991054, by rfl⟩ : syracuseStep 10654739 = 15982109) B15982109
theorem B7103159 : Blo 2103435 7103159 := bstep (se 1 (by rfl) ⟨5327369, by rfl⟩ : syracuseStep 7103159 = 10654739) B10654739
theorem B4735439 : Blo 2103435 4735439 := bstep (se 1 (by rfl) ⟨3551579, by rfl⟩ : syracuseStep 4735439 = 7103159) B7103159
theorem B3156959 : Blo 2103435 3156959 := bstep (se 1 (by rfl) ⟨2367719, by rfl⟩ : syracuseStep 3156959 = 4735439) B4735439
theorem B2104639 : Blo 2103435 2104639 := bstep (se 1 (by rfl) ⟨1578479, by rfl⟩ : syracuseStep 2104639 = 3156959) B3156959
theorem B3156965 : Blo 2103435 3156965 := bbase (se 4 (by rfl) ⟨295965, by rfl⟩ : syracuseStep 3156965 = 591931) (by norm_num)
theorem B2104643 : Blo 2103435 2104643 := bstep (se 1 (by rfl) ⟨1578482, by rfl⟩ : syracuseStep 2104643 = 3156965) B3156965
theorem B8989973 : Blo 2103435 8989973 := bbase (se 6 (by rfl) ⟨210702, by rfl⟩ : syracuseStep 8989973 = 421405) (by norm_num)
theorem B5993315 : Blo 2103435 5993315 := bstep (se 1 (by rfl) ⟨4494986, by rfl⟩ : syracuseStep 5993315 = 8989973) B8989973
theorem B3995543 : Blo 2103435 3995543 := bstep (se 1 (by rfl) ⟨2996657, by rfl⟩ : syracuseStep 3995543 = 5993315) B5993315
theorem B2663695 : Blo 2103435 2663695 := bstep (se 1 (by rfl) ⟨1997771, by rfl⟩ : syracuseStep 2663695 = 3995543) B3995543
theorem B3551593 : Blo 2103435 3551593 := bstep (se 2 (by rfl) ⟨1331847, by rfl⟩ : syracuseStep 3551593 = 2663695) B2663695
theorem B4735457 : Blo 2103435 4735457 := bstep (se 2 (by rfl) ⟨1775796, by rfl⟩ : syracuseStep 4735457 = 3551593) B3551593
theorem B3156971 : Blo 2103435 3156971 := bstep (se 1 (by rfl) ⟨2367728, by rfl⟩ : syracuseStep 3156971 = 4735457) B4735457
theorem B2104647 : Blo 2103435 2104647 := bstep (se 1 (by rfl) ⟨1578485, by rfl⟩ : syracuseStep 2104647 = 3156971) B3156971
theorem B2367733 : Blo 2103435 2367733 := bbase (se 5 (by rfl) ⟨110987, by rfl⟩ : syracuseStep 2367733 = 221975) (by norm_num)
theorem B3156977 : Blo 2103435 3156977 := bstep (se 2 (by rfl) ⟨1183866, by rfl⟩ : syracuseStep 3156977 = 2367733) B2367733
theorem B2104651 : Blo 2103435 2104651 := bstep (se 1 (by rfl) ⟨1578488, by rfl⟩ : syracuseStep 2104651 = 3156977) B3156977
theorem B2663705 : Blo 2103435 2663705 := bbase (se 2 (by rfl) ⟨998889, by rfl⟩ : syracuseStep 2663705 = 1997779) (by norm_num)
theorem B7103213 : Blo 2103435 7103213 := bstep (se 3 (by rfl) ⟨1331852, by rfl⟩ : syracuseStep 7103213 = 2663705) B2663705
theorem B4735475 : Blo 2103435 4735475 := bstep (se 1 (by rfl) ⟨3551606, by rfl⟩ : syracuseStep 4735475 = 7103213) B7103213
theorem B3156983 : Blo 2103435 3156983 := bstep (se 1 (by rfl) ⟨2367737, by rfl⟩ : syracuseStep 3156983 = 4735475) B4735475
theorem B2104655 : Blo 2103435 2104655 := bstep (se 1 (by rfl) ⟨1578491, by rfl⟩ : syracuseStep 2104655 = 3156983) B3156983
theorem B3156989 : Blo 2103435 3156989 := bbase (se 3 (by rfl) ⟨591935, by rfl⟩ : syracuseStep 3156989 = 1183871) (by norm_num)
theorem B2104659 : Blo 2103435 2104659 := bstep (se 1 (by rfl) ⟨1578494, by rfl⟩ : syracuseStep 2104659 = 3156989) B3156989
theorem B4735493 : Blo 2103435 4735493 := bbase (se 4 (by rfl) ⟨443952, by rfl⟩ : syracuseStep 4735493 = 887905) (by norm_num)
theorem B3156995 : Blo 2103435 3156995 := bstep (se 1 (by rfl) ⟨2367746, by rfl⟩ : syracuseStep 3156995 = 4735493) B4735493
theorem B2104663 : Blo 2103435 2104663 := bstep (se 1 (by rfl) ⟨1578497, by rfl⟩ : syracuseStep 2104663 = 3156995) B3156995
theorem B3995581 : Blo 2103435 3995581 := bbase (se 3 (by rfl) ⟨749171, by rfl⟩ : syracuseStep 3995581 = 1498343) (by norm_num)
theorem B5327441 : Blo 2103435 5327441 := bstep (se 2 (by rfl) ⟨1997790, by rfl⟩ : syracuseStep 5327441 = 3995581) B3995581
theorem B3551627 : Blo 2103435 3551627 := bstep (se 1 (by rfl) ⟨2663720, by rfl⟩ : syracuseStep 3551627 = 5327441) B5327441
theorem B2367751 : Blo 2103435 2367751 := bstep (se 1 (by rfl) ⟨1775813, by rfl⟩ : syracuseStep 2367751 = 3551627) B3551627
theorem B3157001 : Blo 2103435 3157001 := bstep (se 2 (by rfl) ⟨1183875, by rfl⟩ : syracuseStep 3157001 = 2367751) B2367751
theorem B2104667 : Blo 2103435 2104667 := bstep (se 1 (by rfl) ⟨1578500, by rfl⟩ : syracuseStep 2104667 = 3157001) B3157001
theorem B10654901 : Blo 2103435 10654901 := bbase (se 5 (by rfl) ⟨499448, by rfl⟩ : syracuseStep 10654901 = 998897) (by norm_num)
theorem B7103267 : Blo 2103435 7103267 := bstep (se 1 (by rfl) ⟨5327450, by rfl⟩ : syracuseStep 7103267 = 10654901) B10654901
theorem B4735511 : Blo 2103435 4735511 := bstep (se 1 (by rfl) ⟨3551633, by rfl⟩ : syracuseStep 4735511 = 7103267) B7103267
theorem B3157007 : Blo 2103435 3157007 := bstep (se 1 (by rfl) ⟨2367755, by rfl⟩ : syracuseStep 3157007 = 4735511) B4735511
theorem B2104671 : Blo 2103435 2104671 := bstep (se 1 (by rfl) ⟨1578503, by rfl⟩ : syracuseStep 2104671 = 3157007) B3157007
theorem B3157013 : Blo 2103435 3157013 := bbase (se 6 (by rfl) ⟨73992, by rfl⟩ : syracuseStep 3157013 = 147985) (by norm_num)
theorem B2104675 : Blo 2103435 2104675 := bstep (se 1 (by rfl) ⟨1578506, by rfl⟩ : syracuseStep 2104675 = 3157013) B3157013
theorem B5400157 : Blo 2103435 5400157 := bbase (se 3 (by rfl) ⟨1012529, by rfl⟩ : syracuseStep 5400157 = 2025059) (by norm_num)
theorem B7200209 : Blo 2103435 7200209 := bstep (se 2 (by rfl) ⟨2700078, by rfl⟩ : syracuseStep 7200209 = 5400157) B5400157
theorem B19200557 : Blo 2103435 19200557 := bstep (se 3 (by rfl) ⟨3600104, by rfl⟩ : syracuseStep 19200557 = 7200209) B7200209
theorem B12800371 : Blo 2103435 12800371 := bstep (se 1 (by rfl) ⟨9600278, by rfl⟩ : syracuseStep 12800371 = 19200557) B19200557
theorem B17067161 : Blo 2103435 17067161 := bstep (se 2 (by rfl) ⟨6400185, by rfl⟩ : syracuseStep 17067161 = 12800371) B12800371
theorem B11378107 : Blo 2103435 11378107 := bstep (se 1 (by rfl) ⟨8533580, by rfl⟩ : syracuseStep 11378107 = 17067161) B17067161
theorem B15170809 : Blo 2103435 15170809 := bstep (se 2 (by rfl) ⟨5689053, by rfl⟩ : syracuseStep 15170809 = 11378107) B11378107
theorem B20227745 : Blo 2103435 20227745 := bstep (se 2 (by rfl) ⟨7585404, by rfl⟩ : syracuseStep 20227745 = 15170809) B15170809
theorem B13485163 : Blo 2103435 13485163 := bstep (se 1 (by rfl) ⟨10113872, by rfl⟩ : syracuseStep 13485163 = 20227745) B20227745
theorem B17980217 : Blo 2103435 17980217 := bstep (se 2 (by rfl) ⟨6742581, by rfl⟩ : syracuseStep 17980217 = 13485163) B13485163
theorem B11986811 : Blo 2103435 11986811 := bstep (se 1 (by rfl) ⟨8990108, by rfl⟩ : syracuseStep 11986811 = 17980217) B17980217
theorem B7991207 : Blo 2103435 7991207 := bstep (se 1 (by rfl) ⟨5993405, by rfl⟩ : syracuseStep 7991207 = 11986811) B11986811
theorem B5327471 : Blo 2103435 5327471 := bstep (se 1 (by rfl) ⟨3995603, by rfl⟩ : syracuseStep 5327471 = 7991207) B7991207
theorem B3551647 : Blo 2103435 3551647 := bstep (se 1 (by rfl) ⟨2663735, by rfl⟩ : syracuseStep 3551647 = 5327471) B5327471
theorem B4735529 : Blo 2103435 4735529 := bstep (se 2 (by rfl) ⟨1775823, by rfl⟩ : syracuseStep 4735529 = 3551647) B3551647
theorem B3157019 : Blo 2103435 3157019 := bstep (se 1 (by rfl) ⟨2367764, by rfl⟩ : syracuseStep 3157019 = 4735529) B4735529
theorem B2104679 : Blo 2103435 2104679 := bstep (se 1 (by rfl) ⟨1578509, by rfl⟩ : syracuseStep 2104679 = 3157019) B3157019
theorem B2367769 : Blo 2103435 2367769 := bbase (se 2 (by rfl) ⟨887913, by rfl⟩ : syracuseStep 2367769 = 1775827) (by norm_num)
theorem B3157025 : Blo 2103435 3157025 := bstep (se 2 (by rfl) ⟨1183884, by rfl⟩ : syracuseStep 3157025 = 2367769) B2367769
theorem B2104683 : Blo 2103435 2104683 := bstep (se 1 (by rfl) ⟨1578512, by rfl⟩ : syracuseStep 2104683 = 3157025) B3157025
theorem B7991237 : Blo 2103435 7991237 := bbase (se 4 (by rfl) ⟨749178, by rfl⟩ : syracuseStep 7991237 = 1498357) (by norm_num)
theorem B5327491 : Blo 2103435 5327491 := bstep (se 1 (by rfl) ⟨3995618, by rfl⟩ : syracuseStep 5327491 = 7991237) B7991237
theorem B7103321 : Blo 2103435 7103321 := bstep (se 2 (by rfl) ⟨2663745, by rfl⟩ : syracuseStep 7103321 = 5327491) B5327491
theorem B4735547 : Blo 2103435 4735547 := bstep (se 1 (by rfl) ⟨3551660, by rfl⟩ : syracuseStep 4735547 = 7103321) B7103321
theorem B3157031 : Blo 2103435 3157031 := bstep (se 1 (by rfl) ⟨2367773, by rfl⟩ : syracuseStep 3157031 = 4735547) B4735547
theorem B2104687 : Blo 2103435 2104687 := bstep (se 1 (by rfl) ⟨1578515, by rfl⟩ : syracuseStep 2104687 = 3157031) B3157031
theorem B3157037 : Blo 2103435 3157037 := bbase (se 3 (by rfl) ⟨591944, by rfl⟩ : syracuseStep 3157037 = 1183889) (by norm_num)
theorem B2104691 : Blo 2103435 2104691 := bstep (se 1 (by rfl) ⟨1578518, by rfl⟩ : syracuseStep 2104691 = 3157037) B3157037
theorem B4735565 : Blo 2103435 4735565 := bbase (se 3 (by rfl) ⟨887918, by rfl⟩ : syracuseStep 4735565 = 1775837) (by norm_num)
theorem B3157043 : Blo 2103435 3157043 := bstep (se 1 (by rfl) ⟨2367782, by rfl⟩ : syracuseStep 3157043 = 4735565) B4735565
theorem B2104695 : Blo 2103435 2104695 := bstep (se 1 (by rfl) ⟨1578521, by rfl⟩ : syracuseStep 2104695 = 3157043) B3157043
theorem B2663761 : Blo 2103435 2663761 := bbase (se 2 (by rfl) ⟨998910, by rfl⟩ : syracuseStep 2663761 = 1997821) (by norm_num)
theorem B3551681 : Blo 2103435 3551681 := bstep (se 2 (by rfl) ⟨1331880, by rfl⟩ : syracuseStep 3551681 = 2663761) B2663761
theorem B2367787 : Blo 2103435 2367787 := bstep (se 1 (by rfl) ⟨1775840, by rfl⟩ : syracuseStep 2367787 = 3551681) B3551681
theorem B3157049 : Blo 2103435 3157049 := bstep (se 2 (by rfl) ⟨1183893, by rfl⟩ : syracuseStep 3157049 = 2367787) B2367787
theorem B2104699 : Blo 2103435 2104699 := bstep (se 1 (by rfl) ⟨1578524, by rfl⟩ : syracuseStep 2104699 = 3157049) B3157049
theorem B2528497 : Blo 2103435 2528497 := bbase (se 2 (by rfl) ⟨948186, by rfl⟩ : syracuseStep 2528497 = 1896373) (by norm_num)
theorem B3371329 : Blo 2103435 3371329 := bstep (se 2 (by rfl) ⟨1264248, by rfl⟩ : syracuseStep 3371329 = 2528497) B2528497
theorem B4495105 : Blo 2103435 4495105 := bstep (se 2 (by rfl) ⟨1685664, by rfl⟩ : syracuseStep 4495105 = 3371329) B3371329
theorem B23973893 : Blo 2103435 23973893 := bstep (se 4 (by rfl) ⟨2247552, by rfl⟩ : syracuseStep 23973893 = 4495105) B4495105
theorem B15982595 : Blo 2103435 15982595 := bstep (se 1 (by rfl) ⟨11986946, by rfl⟩ : syracuseStep 15982595 = 23973893) B23973893
theorem B10655063 : Blo 2103435 10655063 := bstep (se 1 (by rfl) ⟨7991297, by rfl⟩ : syracuseStep 10655063 = 15982595) B15982595
theorem B7103375 : Blo 2103435 7103375 := bstep (se 1 (by rfl) ⟨5327531, by rfl⟩ : syracuseStep 7103375 = 10655063) B10655063
theorem B4735583 : Blo 2103435 4735583 := bstep (se 1 (by rfl) ⟨3551687, by rfl⟩ : syracuseStep 4735583 = 7103375) B7103375
theorem B3157055 : Blo 2103435 3157055 := bstep (se 1 (by rfl) ⟨2367791, by rfl⟩ : syracuseStep 3157055 = 4735583) B4735583
theorem B2104703 : Blo 2103435 2104703 := bstep (se 1 (by rfl) ⟨1578527, by rfl⟩ : syracuseStep 2104703 = 3157055) B3157055
theorem B3157061 : Blo 2103435 3157061 := bbase (se 4 (by rfl) ⟨295974, by rfl⟩ : syracuseStep 3157061 = 591949) (by norm_num)
theorem B2104707 : Blo 2103435 2104707 := bstep (se 1 (by rfl) ⟨1578530, by rfl⟩ : syracuseStep 2104707 = 3157061) B3157061
theorem B3551701 : Blo 2103435 3551701 := bbase (se 7 (by rfl) ⟨41621, by rfl⟩ : syracuseStep 3551701 = 83243) (by norm_num)
theorem B4735601 : Blo 2103435 4735601 := bstep (se 2 (by rfl) ⟨1775850, by rfl⟩ : syracuseStep 4735601 = 3551701) B3551701
theorem B3157067 : Blo 2103435 3157067 := bstep (se 1 (by rfl) ⟨2367800, by rfl⟩ : syracuseStep 3157067 = 4735601) B4735601
theorem B2104711 : Blo 2103435 2104711 := bstep (se 1 (by rfl) ⟨1578533, by rfl⟩ : syracuseStep 2104711 = 3157067) B3157067
theorem B2367805 : Blo 2103435 2367805 := bbase (se 3 (by rfl) ⟨443963, by rfl⟩ : syracuseStep 2367805 = 887927) (by norm_num)
theorem B3157073 : Blo 2103435 3157073 := bstep (se 2 (by rfl) ⟨1183902, by rfl⟩ : syracuseStep 3157073 = 2367805) B2367805
theorem B2104715 : Blo 2103435 2104715 := bstep (se 1 (by rfl) ⟨1578536, by rfl⟩ : syracuseStep 2104715 = 3157073) B3157073
theorem B7103429 : Blo 2103435 7103429 := bbase (se 4 (by rfl) ⟨665946, by rfl⟩ : syracuseStep 7103429 = 1331893) (by norm_num)
theorem B4735619 : Blo 2103435 4735619 := bstep (se 1 (by rfl) ⟨3551714, by rfl⟩ : syracuseStep 4735619 = 7103429) B7103429
theorem B3157079 : Blo 2103435 3157079 := bstep (se 1 (by rfl) ⟨2367809, by rfl⟩ : syracuseStep 3157079 = 4735619) B4735619
theorem B2104719 : Blo 2103435 2104719 := bstep (se 1 (by rfl) ⟨1578539, by rfl⟩ : syracuseStep 2104719 = 3157079) B3157079
theorem B3157085 : Blo 2103435 3157085 := bbase (se 3 (by rfl) ⟨591953, by rfl⟩ : syracuseStep 3157085 = 1183907) (by norm_num)
theorem B2104723 : Blo 2103435 2104723 := bstep (se 1 (by rfl) ⟨1578542, by rfl⟩ : syracuseStep 2104723 = 3157085) B3157085
theorem B4735637 : Blo 2103435 4735637 := bbase (se 6 (by rfl) ⟨110991, by rfl⟩ : syracuseStep 4735637 = 221983) (by norm_num)
theorem B3157091 : Blo 2103435 3157091 := bstep (se 1 (by rfl) ⟨2367818, by rfl⟩ : syracuseStep 3157091 = 4735637) B4735637
theorem B2104727 : Blo 2103435 2104727 := bstep (se 1 (by rfl) ⟨1578545, by rfl⟩ : syracuseStep 2104727 = 3157091) B3157091
theorem B12800693 : Blo 2103435 12800693 := bbase (se 5 (by rfl) ⟨600032, by rfl⟩ : syracuseStep 12800693 = 1200065) (by norm_num)
theorem B8533795 : Blo 2103435 8533795 := bstep (se 1 (by rfl) ⟨6400346, by rfl⟩ : syracuseStep 8533795 = 12800693) B12800693
theorem B11378393 : Blo 2103435 11378393 := bstep (se 2 (by rfl) ⟨4266897, by rfl⟩ : syracuseStep 11378393 = 8533795) B8533795
theorem B7585595 : Blo 2103435 7585595 := bstep (se 1 (by rfl) ⟨5689196, by rfl⟩ : syracuseStep 7585595 = 11378393) B11378393
theorem B5057063 : Blo 2103435 5057063 := bstep (se 1 (by rfl) ⟨3792797, by rfl⟩ : syracuseStep 5057063 = 7585595) B7585595
theorem B3371375 : Blo 2103435 3371375 := bstep (se 1 (by rfl) ⟨2528531, by rfl⟩ : syracuseStep 3371375 = 5057063) B5057063
theorem B2247583 : Blo 2103435 2247583 := bstep (se 1 (by rfl) ⟨1685687, by rfl⟩ : syracuseStep 2247583 = 3371375) B3371375
theorem B2996777 : Blo 2103435 2996777 := bstep (se 2 (by rfl) ⟨1123791, by rfl⟩ : syracuseStep 2996777 = 2247583) B2247583
theorem B7991405 : Blo 2103435 7991405 := bstep (se 3 (by rfl) ⟨1498388, by rfl⟩ : syracuseStep 7991405 = 2996777) B2996777
theorem B5327603 : Blo 2103435 5327603 := bstep (se 1 (by rfl) ⟨3995702, by rfl⟩ : syracuseStep 5327603 = 7991405) B7991405
theorem B3551735 : Blo 2103435 3551735 := bstep (se 1 (by rfl) ⟨2663801, by rfl⟩ : syracuseStep 3551735 = 5327603) B5327603
theorem B2367823 : Blo 2103435 2367823 := bstep (se 1 (by rfl) ⟨1775867, by rfl⟩ : syracuseStep 2367823 = 3551735) B3551735
theorem B3157097 : Blo 2103435 3157097 := bstep (se 2 (by rfl) ⟨1183911, by rfl⟩ : syracuseStep 3157097 = 2367823) B2367823
theorem B2104731 : Blo 2103435 2104731 := bstep (se 1 (by rfl) ⟨1578548, by rfl⟩ : syracuseStep 2104731 = 3157097) B3157097
theorem B5689205 : Blo 2103435 5689205 := bbase (se 5 (by rfl) ⟨266681, by rfl⟩ : syracuseStep 5689205 = 533363) (by norm_num)
theorem B3792803 : Blo 2103435 3792803 := bstep (se 1 (by rfl) ⟨2844602, by rfl⟩ : syracuseStep 3792803 = 5689205) B5689205
theorem B10114141 : Blo 2103435 10114141 := bstep (se 3 (by rfl) ⟨1896401, by rfl⟩ : syracuseStep 10114141 = 3792803) B3792803
theorem B13485521 : Blo 2103435 13485521 := bstep (se 2 (by rfl) ⟨5057070, by rfl⟩ : syracuseStep 13485521 = 10114141) B10114141
theorem B8990347 : Blo 2103435 8990347 := bstep (se 1 (by rfl) ⟨6742760, by rfl⟩ : syracuseStep 8990347 = 13485521) B13485521
theorem B11987129 : Blo 2103435 11987129 := bstep (se 2 (by rfl) ⟨4495173, by rfl⟩ : syracuseStep 11987129 = 8990347) B8990347
theorem B7991419 : Blo 2103435 7991419 := bstep (se 1 (by rfl) ⟨5993564, by rfl⟩ : syracuseStep 7991419 = 11987129) B11987129
theorem B10655225 : Blo 2103435 10655225 := bstep (se 2 (by rfl) ⟨3995709, by rfl⟩ : syracuseStep 10655225 = 7991419) B7991419
theorem B7103483 : Blo 2103435 7103483 := bstep (se 1 (by rfl) ⟨5327612, by rfl⟩ : syracuseStep 7103483 = 10655225) B10655225
theorem B4735655 : Blo 2103435 4735655 := bstep (se 1 (by rfl) ⟨3551741, by rfl⟩ : syracuseStep 4735655 = 7103483) B7103483
theorem B3157103 : Blo 2103435 3157103 := bstep (se 1 (by rfl) ⟨2367827, by rfl⟩ : syracuseStep 3157103 = 4735655) B4735655
theorem B2104735 : Blo 2103435 2104735 := bstep (se 1 (by rfl) ⟨1578551, by rfl⟩ : syracuseStep 2104735 = 3157103) B3157103
theorem B3157109 : Blo 2103435 3157109 := bbase (se 5 (by rfl) ⟨147989, by rfl⟩ : syracuseStep 3157109 = 295979) (by norm_num)
theorem B2104739 : Blo 2103435 2104739 := bstep (se 1 (by rfl) ⟨1578554, by rfl⟩ : syracuseStep 2104739 = 3157109) B3157109
theorem B3995725 : Blo 2103435 3995725 := bbase (se 3 (by rfl) ⟨749198, by rfl⟩ : syracuseStep 3995725 = 1498397) (by norm_num)
theorem B5327633 : Blo 2103435 5327633 := bstep (se 2 (by rfl) ⟨1997862, by rfl⟩ : syracuseStep 5327633 = 3995725) B3995725
theorem B3551755 : Blo 2103435 3551755 := bstep (se 1 (by rfl) ⟨2663816, by rfl⟩ : syracuseStep 3551755 = 5327633) B5327633
theorem B4735673 : Blo 2103435 4735673 := bstep (se 2 (by rfl) ⟨1775877, by rfl⟩ : syracuseStep 4735673 = 3551755) B3551755
theorem B3157115 : Blo 2103435 3157115 := bstep (se 1 (by rfl) ⟨2367836, by rfl⟩ : syracuseStep 3157115 = 4735673) B4735673
theorem B2104743 : Blo 2103435 2104743 := bstep (se 1 (by rfl) ⟨1578557, by rfl⟩ : syracuseStep 2104743 = 3157115) B3157115
theorem B2367841 : Blo 2103435 2367841 := bbase (se 2 (by rfl) ⟨887940, by rfl⟩ : syracuseStep 2367841 = 1775881) (by norm_num)
theorem B3157121 : Blo 2103435 3157121 := bstep (se 2 (by rfl) ⟨1183920, by rfl⟩ : syracuseStep 3157121 = 2367841) B2367841
theorem B2104747 : Blo 2103435 2104747 := bstep (se 1 (by rfl) ⟨1578560, by rfl⟩ : syracuseStep 2104747 = 3157121) B3157121
theorem B5327653 : Blo 2103435 5327653 := bbase (se 4 (by rfl) ⟨499467, by rfl⟩ : syracuseStep 5327653 = 998935) (by norm_num)
theorem B7103537 : Blo 2103435 7103537 := bstep (se 2 (by rfl) ⟨2663826, by rfl⟩ : syracuseStep 7103537 = 5327653) B5327653
theorem B4735691 : Blo 2103435 4735691 := bstep (se 1 (by rfl) ⟨3551768, by rfl⟩ : syracuseStep 4735691 = 7103537) B7103537
theorem B3157127 : Blo 2103435 3157127 := bstep (se 1 (by rfl) ⟨2367845, by rfl⟩ : syracuseStep 3157127 = 4735691) B4735691
theorem B2104751 : Blo 2103435 2104751 := bstep (se 1 (by rfl) ⟨1578563, by rfl⟩ : syracuseStep 2104751 = 3157127) B3157127
theorem B3157133 : Blo 2103435 3157133 := bbase (se 3 (by rfl) ⟨591962, by rfl⟩ : syracuseStep 3157133 = 1183925) (by norm_num)
theorem B2104755 : Blo 2103435 2104755 := bstep (se 1 (by rfl) ⟨1578566, by rfl⟩ : syracuseStep 2104755 = 3157133) B3157133
theorem B4735709 : Blo 2103435 4735709 := bbase (se 3 (by rfl) ⟨887945, by rfl⟩ : syracuseStep 4735709 = 1775891) (by norm_num)
theorem B3157139 : Blo 2103435 3157139 := bstep (se 1 (by rfl) ⟨2367854, by rfl⟩ : syracuseStep 3157139 = 4735709) B4735709
theorem B2104759 : Blo 2103435 2104759 := bstep (se 1 (by rfl) ⟨1578569, by rfl⟩ : syracuseStep 2104759 = 3157139) B3157139
theorem B3551789 : Blo 2103435 3551789 := bbase (se 3 (by rfl) ⟨665960, by rfl⟩ : syracuseStep 3551789 = 1331921) (by norm_num)
theorem B2367859 : Blo 2103435 2367859 := bstep (se 1 (by rfl) ⟨1775894, by rfl⟩ : syracuseStep 2367859 = 3551789) B3551789
theorem B3157145 : Blo 2103435 3157145 := bstep (se 2 (by rfl) ⟨1183929, by rfl⟩ : syracuseStep 3157145 = 2367859) B2367859
theorem B2104763 : Blo 2103435 2104763 := bstep (se 1 (by rfl) ⟨1578572, by rfl⟩ : syracuseStep 2104763 = 3157145) B3157145
theorem B45514325 : Blo 2103435 45514325 := bbase (se 8 (by rfl) ⟨266685, by rfl⟩ : syracuseStep 45514325 = 533371) (by norm_num)
theorem B30342883 : Blo 2103435 30342883 := bstep (se 1 (by rfl) ⟨22757162, by rfl⟩ : syracuseStep 30342883 = 45514325) B45514325
theorem B40457177 : Blo 2103435 40457177 := bstep (se 2 (by rfl) ⟨15171441, by rfl⟩ : syracuseStep 40457177 = 30342883) B30342883
theorem B26971451 : Blo 2103435 26971451 := bstep (se 1 (by rfl) ⟨20228588, by rfl⟩ : syracuseStep 26971451 = 40457177) B40457177
theorem B17980967 : Blo 2103435 17980967 := bstep (se 1 (by rfl) ⟨13485725, by rfl⟩ : syracuseStep 17980967 = 26971451) B26971451
theorem B11987311 : Blo 2103435 11987311 := bstep (se 1 (by rfl) ⟨8990483, by rfl⟩ : syracuseStep 11987311 = 17980967) B17980967
theorem B15983081 : Blo 2103435 15983081 := bstep (se 2 (by rfl) ⟨5993655, by rfl⟩ : syracuseStep 15983081 = 11987311) B11987311
theorem B10655387 : Blo 2103435 10655387 := bstep (se 1 (by rfl) ⟨7991540, by rfl⟩ : syracuseStep 10655387 = 15983081) B15983081
theorem B7103591 : Blo 2103435 7103591 := bstep (se 1 (by rfl) ⟨5327693, by rfl⟩ : syracuseStep 7103591 = 10655387) B10655387
theorem B4735727 : Blo 2103435 4735727 := bstep (se 1 (by rfl) ⟨3551795, by rfl⟩ : syracuseStep 4735727 = 7103591) B7103591
theorem B3157151 : Blo 2103435 3157151 := bstep (se 1 (by rfl) ⟨2367863, by rfl⟩ : syracuseStep 3157151 = 4735727) B4735727
theorem B2104767 : Blo 2103435 2104767 := bstep (se 1 (by rfl) ⟨1578575, by rfl⟩ : syracuseStep 2104767 = 3157151) B3157151
theorem B3157157 : Blo 2103435 3157157 := bbase (se 4 (by rfl) ⟨295983, by rfl⟩ : syracuseStep 3157157 = 591967) (by norm_num)
theorem B2104771 : Blo 2103435 2104771 := bstep (se 1 (by rfl) ⟨1578578, by rfl⟩ : syracuseStep 2104771 = 3157157) B3157157
theorem B2663857 : Blo 2103435 2663857 := bbase (se 2 (by rfl) ⟨998946, by rfl⟩ : syracuseStep 2663857 = 1997893) (by norm_num)
theorem B3551809 : Blo 2103435 3551809 := bstep (se 2 (by rfl) ⟨1331928, by rfl⟩ : syracuseStep 3551809 = 2663857) B2663857
theorem B4735745 : Blo 2103435 4735745 := bstep (se 2 (by rfl) ⟨1775904, by rfl⟩ : syracuseStep 4735745 = 3551809) B3551809
theorem B3157163 : Blo 2103435 3157163 := bstep (se 1 (by rfl) ⟨2367872, by rfl⟩ : syracuseStep 3157163 = 4735745) B4735745
theorem B2104775 : Blo 2103435 2104775 := bstep (se 1 (by rfl) ⟨1578581, by rfl⟩ : syracuseStep 2104775 = 3157163) B3157163
theorem B2367877 : Blo 2103435 2367877 := bbase (se 4 (by rfl) ⟨221988, by rfl⟩ : syracuseStep 2367877 = 443977) (by norm_num)
theorem B3157169 : Blo 2103435 3157169 := bstep (se 2 (by rfl) ⟨1183938, by rfl⟩ : syracuseStep 3157169 = 2367877) B2367877
theorem B2104779 : Blo 2103435 2104779 := bstep (se 1 (by rfl) ⟨1578584, by rfl⟩ : syracuseStep 2104779 = 3157169) B3157169
theorem B4495277 : Blo 2103435 4495277 := bbase (se 3 (by rfl) ⟨842864, by rfl⟩ : syracuseStep 4495277 = 1685729) (by norm_num)
theorem B2996851 : Blo 2103435 2996851 := bstep (se 1 (by rfl) ⟨2247638, by rfl⟩ : syracuseStep 2996851 = 4495277) B4495277
theorem B3995801 : Blo 2103435 3995801 := bstep (se 2 (by rfl) ⟨1498425, by rfl⟩ : syracuseStep 3995801 = 2996851) B2996851
theorem B2663867 : Blo 2103435 2663867 := bstep (se 1 (by rfl) ⟨1997900, by rfl⟩ : syracuseStep 2663867 = 3995801) B3995801
theorem B7103645 : Blo 2103435 7103645 := bstep (se 3 (by rfl) ⟨1331933, by rfl⟩ : syracuseStep 7103645 = 2663867) B2663867
theorem B4735763 : Blo 2103435 4735763 := bstep (se 1 (by rfl) ⟨3551822, by rfl⟩ : syracuseStep 4735763 = 7103645) B7103645
theorem B3157175 : Blo 2103435 3157175 := bstep (se 1 (by rfl) ⟨2367881, by rfl⟩ : syracuseStep 3157175 = 4735763) B4735763
theorem B2104783 : Blo 2103435 2104783 := bstep (se 1 (by rfl) ⟨1578587, by rfl⟩ : syracuseStep 2104783 = 3157175) B3157175
theorem B3157181 : Blo 2103435 3157181 := bbase (se 3 (by rfl) ⟨591971, by rfl⟩ : syracuseStep 3157181 = 1183943) (by norm_num)
theorem B2104787 : Blo 2103435 2104787 := bstep (se 1 (by rfl) ⟨1578590, by rfl⟩ : syracuseStep 2104787 = 3157181) B3157181
theorem B4735781 : Blo 2103435 4735781 := bbase (se 4 (by rfl) ⟨443979, by rfl⟩ : syracuseStep 4735781 = 887959) (by norm_num)
theorem B3157187 : Blo 2103435 3157187 := bstep (se 1 (by rfl) ⟨2367890, by rfl⟩ : syracuseStep 3157187 = 4735781) B4735781
theorem B2104791 : Blo 2103435 2104791 := bstep (se 1 (by rfl) ⟨1578593, by rfl⟩ : syracuseStep 2104791 = 3157187) B3157187
theorem B5327765 : Blo 2103435 5327765 := bbase (se 6 (by rfl) ⟨124869, by rfl⟩ : syracuseStep 5327765 = 249739) (by norm_num)
theorem B3551843 : Blo 2103435 3551843 := bstep (se 1 (by rfl) ⟨2663882, by rfl⟩ : syracuseStep 3551843 = 5327765) B5327765
theorem B2367895 : Blo 2103435 2367895 := bstep (se 1 (by rfl) ⟨1775921, by rfl⟩ : syracuseStep 2367895 = 3551843) B3551843
theorem B3157193 : Blo 2103435 3157193 := bstep (se 2 (by rfl) ⟨1183947, by rfl⟩ : syracuseStep 3157193 = 2367895) B2367895
theorem B2104795 : Blo 2103435 2104795 := bstep (se 1 (by rfl) ⟨1578596, by rfl⟩ : syracuseStep 2104795 = 3157193) B3157193
theorem B8534069 : Blo 2103435 8534069 := bbase (se 5 (by rfl) ⟨400034, by rfl⟩ : syracuseStep 8534069 = 800069) (by norm_num)
theorem B5689379 : Blo 2103435 5689379 := bstep (se 1 (by rfl) ⟨4267034, by rfl⟩ : syracuseStep 5689379 = 8534069) B8534069
theorem B3792919 : Blo 2103435 3792919 := bstep (se 1 (by rfl) ⟨2844689, by rfl⟩ : syracuseStep 3792919 = 5689379) B5689379
theorem B5057225 : Blo 2103435 5057225 := bstep (se 2 (by rfl) ⟨1896459, by rfl⟩ : syracuseStep 5057225 = 3792919) B3792919
theorem B3371483 : Blo 2103435 3371483 := bstep (se 1 (by rfl) ⟨2528612, by rfl⟩ : syracuseStep 3371483 = 5057225) B5057225
theorem B8990621 : Blo 2103435 8990621 := bstep (se 3 (by rfl) ⟨1685741, by rfl⟩ : syracuseStep 8990621 = 3371483) B3371483
theorem B5993747 : Blo 2103435 5993747 := bstep (se 1 (by rfl) ⟨4495310, by rfl⟩ : syracuseStep 5993747 = 8990621) B8990621
theorem B3995831 : Blo 2103435 3995831 := bstep (se 1 (by rfl) ⟨2996873, by rfl⟩ : syracuseStep 3995831 = 5993747) B5993747
theorem B10655549 : Blo 2103435 10655549 := bstep (se 3 (by rfl) ⟨1997915, by rfl⟩ : syracuseStep 10655549 = 3995831) B3995831
theorem B7103699 : Blo 2103435 7103699 := bstep (se 1 (by rfl) ⟨5327774, by rfl⟩ : syracuseStep 7103699 = 10655549) B10655549
theorem B4735799 : Blo 2103435 4735799 := bstep (se 1 (by rfl) ⟨3551849, by rfl⟩ : syracuseStep 4735799 = 7103699) B7103699
theorem B3157199 : Blo 2103435 3157199 := bstep (se 1 (by rfl) ⟨2367899, by rfl⟩ : syracuseStep 3157199 = 4735799) B4735799
theorem B2104799 : Blo 2103435 2104799 := bstep (se 1 (by rfl) ⟨1578599, by rfl⟩ : syracuseStep 2104799 = 3157199) B3157199
theorem B3157205 : Blo 2103435 3157205 := bbase (se 7 (by rfl) ⟨36998, by rfl⟩ : syracuseStep 3157205 = 73997) (by norm_num)
theorem B2104803 : Blo 2103435 2104803 := bstep (se 1 (by rfl) ⟨1578602, by rfl⟩ : syracuseStep 2104803 = 3157205) B3157205
theorem B2996885 : Blo 2103435 2996885 := bbase (se 6 (by rfl) ⟨70239, by rfl⟩ : syracuseStep 2996885 = 140479) (by norm_num)
theorem B7991693 : Blo 2103435 7991693 := bstep (se 3 (by rfl) ⟨1498442, by rfl⟩ : syracuseStep 7991693 = 2996885) B2996885
theorem B5327795 : Blo 2103435 5327795 := bstep (se 1 (by rfl) ⟨3995846, by rfl⟩ : syracuseStep 5327795 = 7991693) B7991693
theorem B3551863 : Blo 2103435 3551863 := bstep (se 1 (by rfl) ⟨2663897, by rfl⟩ : syracuseStep 3551863 = 5327795) B5327795
theorem B4735817 : Blo 2103435 4735817 := bstep (se 2 (by rfl) ⟨1775931, by rfl⟩ : syracuseStep 4735817 = 3551863) B3551863
theorem B3157211 : Blo 2103435 3157211 := bstep (se 1 (by rfl) ⟨2367908, by rfl⟩ : syracuseStep 3157211 = 4735817) B4735817
theorem B2104807 : Blo 2103435 2104807 := bstep (se 1 (by rfl) ⟨1578605, by rfl⟩ : syracuseStep 2104807 = 3157211) B3157211
theorem B2367913 : Blo 2103435 2367913 := bbase (se 2 (by rfl) ⟨887967, by rfl⟩ : syracuseStep 2367913 = 1775935) (by norm_num)
theorem B3157217 : Blo 2103435 3157217 := bstep (se 2 (by rfl) ⟨1183956, by rfl⟩ : syracuseStep 3157217 = 2367913) B2367913
theorem B2104811 : Blo 2103435 2104811 := bstep (se 1 (by rfl) ⟨1578608, by rfl⟩ : syracuseStep 2104811 = 3157217) B3157217
theorem B18226709 : Blo 2103435 18226709 := bbase (se 6 (by rfl) ⟨427188, by rfl⟩ : syracuseStep 18226709 = 854377) (by norm_num)
theorem B12151139 : Blo 2103435 12151139 := bstep (se 1 (by rfl) ⟨9113354, by rfl⟩ : syracuseStep 12151139 = 18226709) B18226709
theorem B32403037 : Blo 2103435 32403037 := bstep (se 3 (by rfl) ⟨6075569, by rfl⟩ : syracuseStep 32403037 = 12151139) B12151139
theorem B43204049 : Blo 2103435 43204049 := bstep (se 2 (by rfl) ⟨16201518, by rfl⟩ : syracuseStep 43204049 = 32403037) B32403037
theorem B28802699 : Blo 2103435 28802699 := bstep (se 1 (by rfl) ⟨21602024, by rfl⟩ : syracuseStep 28802699 = 43204049) B43204049
theorem B19201799 : Blo 2103435 19201799 := bstep (se 1 (by rfl) ⟨14401349, by rfl⟩ : syracuseStep 19201799 = 28802699) B28802699
theorem B12801199 : Blo 2103435 12801199 := bstep (se 1 (by rfl) ⟨9600899, by rfl⟩ : syracuseStep 12801199 = 19201799) B19201799
theorem B17068265 : Blo 2103435 17068265 := bstep (se 2 (by rfl) ⟨6400599, by rfl⟩ : syracuseStep 17068265 = 12801199) B12801199
theorem B11378843 : Blo 2103435 11378843 := bstep (se 1 (by rfl) ⟨8534132, by rfl⟩ : syracuseStep 11378843 = 17068265) B17068265
theorem B7585895 : Blo 2103435 7585895 := bstep (se 1 (by rfl) ⟨5689421, by rfl⟩ : syracuseStep 7585895 = 11378843) B11378843
theorem B5057263 : Blo 2103435 5057263 := bstep (se 1 (by rfl) ⟨3792947, by rfl⟩ : syracuseStep 5057263 = 7585895) B7585895
theorem B6743017 : Blo 2103435 6743017 := bstep (se 2 (by rfl) ⟨2528631, by rfl⟩ : syracuseStep 6743017 = 5057263) B5057263
theorem B8990689 : Blo 2103435 8990689 := bstep (se 2 (by rfl) ⟨3371508, by rfl⟩ : syracuseStep 8990689 = 6743017) B6743017
theorem B11987585 : Blo 2103435 11987585 := bstep (se 2 (by rfl) ⟨4495344, by rfl⟩ : syracuseStep 11987585 = 8990689) B8990689
theorem B7991723 : Blo 2103435 7991723 := bstep (se 1 (by rfl) ⟨5993792, by rfl⟩ : syracuseStep 7991723 = 11987585) B11987585
theorem B5327815 : Blo 2103435 5327815 := bstep (se 1 (by rfl) ⟨3995861, by rfl⟩ : syracuseStep 5327815 = 7991723) B7991723
theorem B7103753 : Blo 2103435 7103753 := bstep (se 2 (by rfl) ⟨2663907, by rfl⟩ : syracuseStep 7103753 = 5327815) B5327815
theorem B4735835 : Blo 2103435 4735835 := bstep (se 1 (by rfl) ⟨3551876, by rfl⟩ : syracuseStep 4735835 = 7103753) B7103753
theorem B3157223 : Blo 2103435 3157223 := bstep (se 1 (by rfl) ⟨2367917, by rfl⟩ : syracuseStep 3157223 = 4735835) B4735835
theorem B2104815 : Blo 2103435 2104815 := bstep (se 1 (by rfl) ⟨1578611, by rfl⟩ : syracuseStep 2104815 = 3157223) B3157223
theorem B3157229 : Blo 2103435 3157229 := bbase (se 3 (by rfl) ⟨591980, by rfl⟩ : syracuseStep 3157229 = 1183961) (by norm_num)
theorem B2104819 : Blo 2103435 2104819 := bstep (se 1 (by rfl) ⟨1578614, by rfl⟩ : syracuseStep 2104819 = 3157229) B3157229
theorem B4735853 : Blo 2103435 4735853 := bbase (se 3 (by rfl) ⟨887972, by rfl⟩ : syracuseStep 4735853 = 1775945) (by norm_num)
theorem B3157235 : Blo 2103435 3157235 := bstep (se 1 (by rfl) ⟨2367926, by rfl⟩ : syracuseStep 3157235 = 4735853) B4735853
theorem B2104823 : Blo 2103435 2104823 := bstep (se 1 (by rfl) ⟨1578617, by rfl⟩ : syracuseStep 2104823 = 3157235) B3157235
theorem B3995885 : Blo 2103435 3995885 := bbase (se 3 (by rfl) ⟨749228, by rfl⟩ : syracuseStep 3995885 = 1498457) (by norm_num)
theorem B2663923 : Blo 2103435 2663923 := bstep (se 1 (by rfl) ⟨1997942, by rfl⟩ : syracuseStep 2663923 = 3995885) B3995885
theorem B3551897 : Blo 2103435 3551897 := bstep (se 2 (by rfl) ⟨1331961, by rfl⟩ : syracuseStep 3551897 = 2663923) B2663923
theorem B2367931 : Blo 2103435 2367931 := bstep (se 1 (by rfl) ⟨1775948, by rfl⟩ : syracuseStep 2367931 = 3551897) B3551897
theorem B3157241 : Blo 2103435 3157241 := bstep (se 2 (by rfl) ⟨1183965, by rfl⟩ : syracuseStep 3157241 = 2367931) B2367931
theorem B2104827 : Blo 2103435 2104827 := bstep (se 1 (by rfl) ⟨1578620, by rfl⟩ : syracuseStep 2104827 = 3157241) B3157241
theorem B3417533 : Blo 2103435 3417533 := bbase (se 3 (by rfl) ⟨640787, by rfl⟩ : syracuseStep 3417533 = 1281575) (by norm_num)
theorem B145814741 : Blo 2103435 145814741 := bstep (se 7 (by rfl) ⟨1708766, by rfl⟩ : syracuseStep 145814741 = 3417533) B3417533
theorem B97209827 : Blo 2103435 97209827 := bstep (se 1 (by rfl) ⟨72907370, by rfl⟩ : syracuseStep 97209827 = 145814741) B145814741
theorem B64806551 : Blo 2103435 64806551 := bstep (se 1 (by rfl) ⟨48604913, by rfl⟩ : syracuseStep 64806551 = 97209827) B97209827
theorem B43204367 : Blo 2103435 43204367 := bstep (se 1 (by rfl) ⟨32403275, by rfl⟩ : syracuseStep 43204367 = 64806551) B64806551
theorem B28802911 : Blo 2103435 28802911 := bstep (se 1 (by rfl) ⟨21602183, by rfl⟩ : syracuseStep 28802911 = 43204367) B43204367
theorem B38403881 : Blo 2103435 38403881 := bstep (se 2 (by rfl) ⟨14401455, by rfl⟩ : syracuseStep 38403881 = 28802911) B28802911
theorem B25602587 : Blo 2103435 25602587 := bstep (se 1 (by rfl) ⟨19201940, by rfl⟩ : syracuseStep 25602587 = 38403881) B38403881
theorem B17068391 : Blo 2103435 17068391 := bstep (se 1 (by rfl) ⟨12801293, by rfl⟩ : syracuseStep 17068391 = 25602587) B25602587
theorem B11378927 : Blo 2103435 11378927 := bstep (se 1 (by rfl) ⟨8534195, by rfl⟩ : syracuseStep 11378927 = 17068391) B17068391
theorem B30343805 : Blo 2103435 30343805 := bstep (se 3 (by rfl) ⟨5689463, by rfl⟩ : syracuseStep 30343805 = 11378927) B11378927
theorem B20229203 : Blo 2103435 20229203 := bstep (se 1 (by rfl) ⟨15171902, by rfl⟩ : syracuseStep 20229203 = 30343805) B30343805
theorem B53944541 : Blo 2103435 53944541 := bstep (se 3 (by rfl) ⟨10114601, by rfl⟩ : syracuseStep 53944541 = 20229203) B20229203
theorem B35963027 : Blo 2103435 35963027 := bstep (se 1 (by rfl) ⟨26972270, by rfl⟩ : syracuseStep 35963027 = 53944541) B53944541
theorem B23975351 : Blo 2103435 23975351 := bstep (se 1 (by rfl) ⟨17981513, by rfl⟩ : syracuseStep 23975351 = 35963027) B35963027
theorem B15983567 : Blo 2103435 15983567 := bstep (se 1 (by rfl) ⟨11987675, by rfl⟩ : syracuseStep 15983567 = 23975351) B23975351
theorem B10655711 : Blo 2103435 10655711 := bstep (se 1 (by rfl) ⟨7991783, by rfl⟩ : syracuseStep 10655711 = 15983567) B15983567
theorem B7103807 : Blo 2103435 7103807 := bstep (se 1 (by rfl) ⟨5327855, by rfl⟩ : syracuseStep 7103807 = 10655711) B10655711
theorem B4735871 : Blo 2103435 4735871 := bstep (se 1 (by rfl) ⟨3551903, by rfl⟩ : syracuseStep 4735871 = 7103807) B7103807
theorem B3157247 : Blo 2103435 3157247 := bstep (se 1 (by rfl) ⟨2367935, by rfl⟩ : syracuseStep 3157247 = 4735871) B4735871
theorem B2104831 : Blo 2103435 2104831 := bstep (se 1 (by rfl) ⟨1578623, by rfl⟩ : syracuseStep 2104831 = 3157247) B3157247
theorem B3157253 : Blo 2103435 3157253 := bbase (se 4 (by rfl) ⟨295992, by rfl⟩ : syracuseStep 3157253 = 591985) (by norm_num)
theorem B2104835 : Blo 2103435 2104835 := bstep (se 1 (by rfl) ⟨1578626, by rfl⟩ : syracuseStep 2104835 = 3157253) B3157253
theorem B3551917 : Blo 2103435 3551917 := bbase (se 3 (by rfl) ⟨665984, by rfl⟩ : syracuseStep 3551917 = 1331969) (by norm_num)
theorem B4735889 : Blo 2103435 4735889 := bstep (se 2 (by rfl) ⟨1775958, by rfl⟩ : syracuseStep 4735889 = 3551917) B3551917
theorem B3157259 : Blo 2103435 3157259 := bstep (se 1 (by rfl) ⟨2367944, by rfl⟩ : syracuseStep 3157259 = 4735889) B4735889
theorem B2104839 : Blo 2103435 2104839 := bstep (se 1 (by rfl) ⟨1578629, by rfl⟩ : syracuseStep 2104839 = 3157259) B3157259
theorem B2367949 : Blo 2103435 2367949 := bbase (se 3 (by rfl) ⟨443990, by rfl⟩ : syracuseStep 2367949 = 887981) (by norm_num)
theorem B3157265 : Blo 2103435 3157265 := bstep (se 2 (by rfl) ⟨1183974, by rfl⟩ : syracuseStep 3157265 = 2367949) B2367949
theorem B2104843 : Blo 2103435 2104843 := bstep (se 1 (by rfl) ⟨1578632, by rfl⟩ : syracuseStep 2104843 = 3157265) B3157265
theorem B7103861 : Blo 2103435 7103861 := bbase (se 5 (by rfl) ⟨332993, by rfl⟩ : syracuseStep 7103861 = 665987) (by norm_num)
theorem B4735907 : Blo 2103435 4735907 := bstep (se 1 (by rfl) ⟨3551930, by rfl⟩ : syracuseStep 4735907 = 7103861) B7103861
theorem B3157271 : Blo 2103435 3157271 := bstep (se 1 (by rfl) ⟨2367953, by rfl⟩ : syracuseStep 3157271 = 4735907) B4735907
theorem B2104847 : Blo 2103435 2104847 := bstep (se 1 (by rfl) ⟨1578635, by rfl⟩ : syracuseStep 2104847 = 3157271) B3157271
theorem B3157277 : Blo 2103435 3157277 := bbase (se 3 (by rfl) ⟨591989, by rfl⟩ : syracuseStep 3157277 = 1183979) (by norm_num)
theorem B2104851 : Blo 2103435 2104851 := bstep (se 1 (by rfl) ⟨1578638, by rfl⟩ : syracuseStep 2104851 = 3157277) B3157277
theorem B4735925 : Blo 2103435 4735925 := bbase (se 5 (by rfl) ⟨221996, by rfl⟩ : syracuseStep 4735925 = 443993) (by norm_num)
theorem B3157283 : Blo 2103435 3157283 := bstep (se 1 (by rfl) ⟨2367962, by rfl⟩ : syracuseStep 3157283 = 4735925) B4735925
theorem B2104855 : Blo 2103435 2104855 := bstep (se 1 (by rfl) ⟨1578641, by rfl⟩ : syracuseStep 2104855 = 3157283) B3157283
theorem B5689541 : Blo 2103435 5689541 := bbase (se 4 (by rfl) ⟨533394, by rfl⟩ : syracuseStep 5689541 = 1066789) (by norm_num)
theorem B15172109 : Blo 2103435 15172109 := bstep (se 3 (by rfl) ⟨2844770, by rfl⟩ : syracuseStep 15172109 = 5689541) B5689541
theorem B10114739 : Blo 2103435 10114739 := bstep (se 1 (by rfl) ⟨7586054, by rfl⟩ : syracuseStep 10114739 = 15172109) B15172109
theorem B6743159 : Blo 2103435 6743159 := bstep (se 1 (by rfl) ⟨5057369, by rfl⟩ : syracuseStep 6743159 = 10114739) B10114739
theorem B4495439 : Blo 2103435 4495439 := bstep (se 1 (by rfl) ⟨3371579, by rfl⟩ : syracuseStep 4495439 = 6743159) B6743159
theorem B11987837 : Blo 2103435 11987837 := bstep (se 3 (by rfl) ⟨2247719, by rfl⟩ : syracuseStep 11987837 = 4495439) B4495439
theorem B7991891 : Blo 2103435 7991891 := bstep (se 1 (by rfl) ⟨5993918, by rfl⟩ : syracuseStep 7991891 = 11987837) B11987837
theorem B5327927 : Blo 2103435 5327927 := bstep (se 1 (by rfl) ⟨3995945, by rfl⟩ : syracuseStep 5327927 = 7991891) B7991891
theorem B3551951 : Blo 2103435 3551951 := bstep (se 1 (by rfl) ⟨2663963, by rfl⟩ : syracuseStep 3551951 = 5327927) B5327927
theorem B2367967 : Blo 2103435 2367967 := bstep (se 1 (by rfl) ⟨1775975, by rfl⟩ : syracuseStep 2367967 = 3551951) B3551951
theorem B3157289 : Blo 2103435 3157289 := bstep (se 2 (by rfl) ⟨1183983, by rfl⟩ : syracuseStep 3157289 = 2367967) B2367967
theorem B2104859 : Blo 2103435 2104859 := bstep (se 1 (by rfl) ⟨1578644, by rfl⟩ : syracuseStep 2104859 = 3157289) B3157289
theorem B10114757 : Blo 2103435 10114757 := bbase (se 4 (by rfl) ⟨948258, by rfl⟩ : syracuseStep 10114757 = 1896517) (by norm_num)
theorem B6743171 : Blo 2103435 6743171 := bstep (se 1 (by rfl) ⟨5057378, by rfl⟩ : syracuseStep 6743171 = 10114757) B10114757
theorem B4495447 : Blo 2103435 4495447 := bstep (se 1 (by rfl) ⟨3371585, by rfl⟩ : syracuseStep 4495447 = 6743171) B6743171
theorem B5993929 : Blo 2103435 5993929 := bstep (se 2 (by rfl) ⟨2247723, by rfl⟩ : syracuseStep 5993929 = 4495447) B4495447
theorem B7991905 : Blo 2103435 7991905 := bstep (se 2 (by rfl) ⟨2996964, by rfl⟩ : syracuseStep 7991905 = 5993929) B5993929
theorem B10655873 : Blo 2103435 10655873 := bstep (se 2 (by rfl) ⟨3995952, by rfl⟩ : syracuseStep 10655873 = 7991905) B7991905
theorem B7103915 : Blo 2103435 7103915 := bstep (se 1 (by rfl) ⟨5327936, by rfl⟩ : syracuseStep 7103915 = 10655873) B10655873
theorem B4735943 : Blo 2103435 4735943 := bstep (se 1 (by rfl) ⟨3551957, by rfl⟩ : syracuseStep 4735943 = 7103915) B7103915
theorem B3157295 : Blo 2103435 3157295 := bstep (se 1 (by rfl) ⟨2367971, by rfl⟩ : syracuseStep 3157295 = 4735943) B4735943
theorem B2104863 : Blo 2103435 2104863 := bstep (se 1 (by rfl) ⟨1578647, by rfl⟩ : syracuseStep 2104863 = 3157295) B3157295
theorem B3157301 : Blo 2103435 3157301 := bbase (se 5 (by rfl) ⟨147998, by rfl⟩ : syracuseStep 3157301 = 295997) (by norm_num)
theorem B2104867 : Blo 2103435 2104867 := bstep (se 1 (by rfl) ⟨1578650, by rfl⟩ : syracuseStep 2104867 = 3157301) B3157301
theorem B5327957 : Blo 2103435 5327957 := bbase (se 8 (by rfl) ⟨31218, by rfl⟩ : syracuseStep 5327957 = 62437) (by norm_num)
theorem B3551971 : Blo 2103435 3551971 := bstep (se 1 (by rfl) ⟨2663978, by rfl⟩ : syracuseStep 3551971 = 5327957) B5327957
theorem B4735961 : Blo 2103435 4735961 := bstep (se 2 (by rfl) ⟨1775985, by rfl⟩ : syracuseStep 4735961 = 3551971) B3551971
theorem B3157307 : Blo 2103435 3157307 := bstep (se 1 (by rfl) ⟨2367980, by rfl⟩ : syracuseStep 3157307 = 4735961) B4735961
theorem B2104871 : Blo 2103435 2104871 := bstep (se 1 (by rfl) ⟨1578653, by rfl⟩ : syracuseStep 2104871 = 3157307) B3157307
theorem B2367985 : Blo 2103435 2367985 := bbase (se 2 (by rfl) ⟨887994, by rfl⟩ : syracuseStep 2367985 = 1775989) (by norm_num)
theorem B3157313 : Blo 2103435 3157313 := bstep (se 2 (by rfl) ⟨1183992, by rfl⟩ : syracuseStep 3157313 = 2367985) B2367985
theorem B2104875 : Blo 2103435 2104875 := bstep (se 1 (by rfl) ⟨1578656, by rfl⟩ : syracuseStep 2104875 = 3157313) B3157313
theorem B4932485 : Blo 2103435 4932485 := bbase (se 4 (by rfl) ⟨462420, by rfl⟩ : syracuseStep 4932485 = 924841) (by norm_num)
theorem B3288323 : Blo 2103435 3288323 := bstep (se 1 (by rfl) ⟨2466242, by rfl⟩ : syracuseStep 3288323 = 4932485) B4932485
theorem B2192215 : Blo 2103435 2192215 := bstep (se 1 (by rfl) ⟨1644161, by rfl⟩ : syracuseStep 2192215 = 3288323) B3288323
theorem B46767253 : Blo 2103435 46767253 := bstep (se 6 (by rfl) ⟨1096107, by rfl⟩ : syracuseStep 46767253 = 2192215) B2192215
theorem B62356337 : Blo 2103435 62356337 := bstep (se 2 (by rfl) ⟨23383626, by rfl⟩ : syracuseStep 62356337 = 46767253) B46767253
theorem B41570891 : Blo 2103435 41570891 := bstep (se 1 (by rfl) ⟨31178168, by rfl⟩ : syracuseStep 41570891 = 62356337) B62356337
theorem B27713927 : Blo 2103435 27713927 := bstep (se 1 (by rfl) ⟨20785445, by rfl⟩ : syracuseStep 27713927 = 41570891) B41570891
theorem B18475951 : Blo 2103435 18475951 := bstep (se 1 (by rfl) ⟨13856963, by rfl⟩ : syracuseStep 18475951 = 27713927) B27713927
theorem B24634601 : Blo 2103435 24634601 := bstep (se 2 (by rfl) ⟨9237975, by rfl⟩ : syracuseStep 24634601 = 18475951) B18475951
theorem B16423067 : Blo 2103435 16423067 := bstep (se 1 (by rfl) ⟨12317300, by rfl⟩ : syracuseStep 16423067 = 24634601) B24634601
theorem B10948711 : Blo 2103435 10948711 := bstep (se 1 (by rfl) ⟨8211533, by rfl⟩ : syracuseStep 10948711 = 16423067) B16423067
theorem B14598281 : Blo 2103435 14598281 := bstep (se 2 (by rfl) ⟨5474355, by rfl⟩ : syracuseStep 14598281 = 10948711) B10948711
theorem B9732187 : Blo 2103435 9732187 := bstep (se 1 (by rfl) ⟨7299140, by rfl⟩ : syracuseStep 9732187 = 14598281) B14598281
theorem B12976249 : Blo 2103435 12976249 := bstep (se 2 (by rfl) ⟨4866093, by rfl⟩ : syracuseStep 12976249 = 9732187) B9732187
theorem B17301665 : Blo 2103435 17301665 := bstep (se 2 (by rfl) ⟨6488124, by rfl⟩ : syracuseStep 17301665 = 12976249) B12976249
theorem B11534443 : Blo 2103435 11534443 := bstep (se 1 (by rfl) ⟨8650832, by rfl⟩ : syracuseStep 11534443 = 17301665) B17301665
theorem B61517029 : Blo 2103435 61517029 := bstep (se 4 (by rfl) ⟨5767221, by rfl⟩ : syracuseStep 61517029 = 11534443) B11534443
theorem B82022705 : Blo 2103435 82022705 := bstep (se 2 (by rfl) ⟨30758514, by rfl⟩ : syracuseStep 82022705 = 61517029) B61517029
theorem B54681803 : Blo 2103435 54681803 := bstep (se 1 (by rfl) ⟨41011352, by rfl⟩ : syracuseStep 54681803 = 82022705) B82022705
theorem B36454535 : Blo 2103435 36454535 := bstep (se 1 (by rfl) ⟨27340901, by rfl⟩ : syracuseStep 36454535 = 54681803) B54681803
theorem B24303023 : Blo 2103435 24303023 := bstep (se 1 (by rfl) ⟨18227267, by rfl⟩ : syracuseStep 24303023 = 36454535) B36454535
theorem B16202015 : Blo 2103435 16202015 := bstep (se 1 (by rfl) ⟨12151511, by rfl⟩ : syracuseStep 16202015 = 24303023) B24303023
theorem B10801343 : Blo 2103435 10801343 := bstep (se 1 (by rfl) ⟨8101007, by rfl⟩ : syracuseStep 10801343 = 16202015) B16202015
theorem B7200895 : Blo 2103435 7200895 := bstep (se 1 (by rfl) ⟨5400671, by rfl⟩ : syracuseStep 7200895 = 10801343) B10801343
theorem B9601193 : Blo 2103435 9601193 := bstep (se 2 (by rfl) ⟨3600447, by rfl⟩ : syracuseStep 9601193 = 7200895) B7200895
theorem B6400795 : Blo 2103435 6400795 := bstep (se 1 (by rfl) ⟨4800596, by rfl⟩ : syracuseStep 6400795 = 9601193) B9601193
theorem B8534393 : Blo 2103435 8534393 := bstep (se 2 (by rfl) ⟨3200397, by rfl⟩ : syracuseStep 8534393 = 6400795) B6400795
theorem B5689595 : Blo 2103435 5689595 := bstep (se 1 (by rfl) ⟨4267196, by rfl⟩ : syracuseStep 5689595 = 8534393) B8534393
theorem B3793063 : Blo 2103435 3793063 := bstep (se 1 (by rfl) ⟨2844797, by rfl⟩ : syracuseStep 3793063 = 5689595) B5689595
theorem B5057417 : Blo 2103435 5057417 := bstep (se 2 (by rfl) ⟨1896531, by rfl⟩ : syracuseStep 5057417 = 3793063) B3793063
theorem B13486445 : Blo 2103435 13486445 := bstep (se 3 (by rfl) ⟨2528708, by rfl⟩ : syracuseStep 13486445 = 5057417) B5057417
theorem B8990963 : Blo 2103435 8990963 := bstep (se 1 (by rfl) ⟨6743222, by rfl⟩ : syracuseStep 8990963 = 13486445) B13486445
theorem B5993975 : Blo 2103435 5993975 := bstep (se 1 (by rfl) ⟨4495481, by rfl⟩ : syracuseStep 5993975 = 8990963) B8990963
theorem B3995983 : Blo 2103435 3995983 := bstep (se 1 (by rfl) ⟨2996987, by rfl⟩ : syracuseStep 3995983 = 5993975) B5993975
theorem B5327977 : Blo 2103435 5327977 := bstep (se 2 (by rfl) ⟨1997991, by rfl⟩ : syracuseStep 5327977 = 3995983) B3995983
theorem B7103969 : Blo 2103435 7103969 := bstep (se 2 (by rfl) ⟨2663988, by rfl⟩ : syracuseStep 7103969 = 5327977) B5327977
theorem B4735979 : Blo 2103435 4735979 := bstep (se 1 (by rfl) ⟨3551984, by rfl⟩ : syracuseStep 4735979 = 7103969) B7103969
theorem B3157319 : Blo 2103435 3157319 := bstep (se 1 (by rfl) ⟨2367989, by rfl⟩ : syracuseStep 3157319 = 4735979) B4735979
theorem B2104879 : Blo 2103435 2104879 := bstep (se 1 (by rfl) ⟨1578659, by rfl⟩ : syracuseStep 2104879 = 3157319) B3157319
theorem B3157325 : Blo 2103435 3157325 := bbase (se 3 (by rfl) ⟨591998, by rfl⟩ : syracuseStep 3157325 = 1183997) (by norm_num)
theorem B2104883 : Blo 2103435 2104883 := bstep (se 1 (by rfl) ⟨1578662, by rfl⟩ : syracuseStep 2104883 = 3157325) B3157325
theorem B4735997 : Blo 2103435 4735997 := bbase (se 3 (by rfl) ⟨887999, by rfl⟩ : syracuseStep 4735997 = 1775999) (by norm_num)
theorem B3157331 : Blo 2103435 3157331 := bstep (se 1 (by rfl) ⟨2367998, by rfl⟩ : syracuseStep 3157331 = 4735997) B4735997
theorem B2104887 : Blo 2103435 2104887 := bstep (se 1 (by rfl) ⟨1578665, by rfl⟩ : syracuseStep 2104887 = 3157331) B3157331
theorem B3552005 : Blo 2103435 3552005 := bbase (se 4 (by rfl) ⟨333000, by rfl⟩ : syracuseStep 3552005 = 666001) (by norm_num)
theorem B2368003 : Blo 2103435 2368003 := bstep (se 1 (by rfl) ⟨1776002, by rfl⟩ : syracuseStep 2368003 = 3552005) B3552005
theorem B3157337 : Blo 2103435 3157337 := bstep (se 2 (by rfl) ⟨1184001, by rfl⟩ : syracuseStep 3157337 = 2368003) B2368003
theorem B2104891 : Blo 2103435 2104891 := bstep (se 1 (by rfl) ⟨1578668, by rfl⟩ : syracuseStep 2104891 = 3157337) B3157337
theorem B15984053 : Blo 2103435 15984053 := bbase (se 5 (by rfl) ⟨749252, by rfl⟩ : syracuseStep 15984053 = 1498505) (by norm_num)
theorem B10656035 : Blo 2103435 10656035 := bstep (se 1 (by rfl) ⟨7992026, by rfl⟩ : syracuseStep 10656035 = 15984053) B15984053
theorem B7104023 : Blo 2103435 7104023 := bstep (se 1 (by rfl) ⟨5328017, by rfl⟩ : syracuseStep 7104023 = 10656035) B10656035
theorem B4736015 : Blo 2103435 4736015 := bstep (se 1 (by rfl) ⟨3552011, by rfl⟩ : syracuseStep 4736015 = 7104023) B7104023
theorem B3157343 : Blo 2103435 3157343 := bstep (se 1 (by rfl) ⟨2368007, by rfl⟩ : syracuseStep 3157343 = 4736015) B4736015
theorem B2104895 : Blo 2103435 2104895 := bstep (se 1 (by rfl) ⟨1578671, by rfl⟩ : syracuseStep 2104895 = 3157343) B3157343
theorem B3157349 : Blo 2103435 3157349 := bbase (se 4 (by rfl) ⟨296001, by rfl⟩ : syracuseStep 3157349 = 592003) (by norm_num)
theorem B2104899 : Blo 2103435 2104899 := bstep (se 1 (by rfl) ⟨1578674, by rfl⟩ : syracuseStep 2104899 = 3157349) B3157349
theorem B3996029 : Blo 2103435 3996029 := bbase (se 3 (by rfl) ⟨749255, by rfl⟩ : syracuseStep 3996029 = 1498511) (by norm_num)
theorem B2664019 : Blo 2103435 2664019 := bstep (se 1 (by rfl) ⟨1998014, by rfl⟩ : syracuseStep 2664019 = 3996029) B3996029
theorem B3552025 : Blo 2103435 3552025 := bstep (se 2 (by rfl) ⟨1332009, by rfl⟩ : syracuseStep 3552025 = 2664019) B2664019
theorem B4736033 : Blo 2103435 4736033 := bstep (se 2 (by rfl) ⟨1776012, by rfl⟩ : syracuseStep 4736033 = 3552025) B3552025
theorem B3157355 : Blo 2103435 3157355 := bstep (se 1 (by rfl) ⟨2368016, by rfl⟩ : syracuseStep 3157355 = 4736033) B4736033
theorem B2104903 : Blo 2103435 2104903 := bstep (se 1 (by rfl) ⟨1578677, by rfl⟩ : syracuseStep 2104903 = 3157355) B3157355
theorem B2368021 : Blo 2103435 2368021 := bbase (se 6 (by rfl) ⟨55500, by rfl⟩ : syracuseStep 2368021 = 111001) (by norm_num)
theorem B3157361 : Blo 2103435 3157361 := bstep (se 2 (by rfl) ⟨1184010, by rfl⟩ : syracuseStep 3157361 = 2368021) B2368021
theorem B2104907 : Blo 2103435 2104907 := bstep (se 1 (by rfl) ⟨1578680, by rfl⟩ : syracuseStep 2104907 = 3157361) B3157361
theorem B2664029 : Blo 2103435 2664029 := bbase (se 3 (by rfl) ⟨499505, by rfl⟩ : syracuseStep 2664029 = 999011) (by norm_num)
theorem B7104077 : Blo 2103435 7104077 := bstep (se 3 (by rfl) ⟨1332014, by rfl⟩ : syracuseStep 7104077 = 2664029) B2664029
theorem B4736051 : Blo 2103435 4736051 := bstep (se 1 (by rfl) ⟨3552038, by rfl⟩ : syracuseStep 4736051 = 7104077) B7104077
theorem B3157367 : Blo 2103435 3157367 := bstep (se 1 (by rfl) ⟨2368025, by rfl⟩ : syracuseStep 3157367 = 4736051) B4736051
theorem B2104911 : Blo 2103435 2104911 := bstep (se 1 (by rfl) ⟨1578683, by rfl⟩ : syracuseStep 2104911 = 3157367) B3157367
theorem B3157373 : Blo 2103435 3157373 := bbase (se 3 (by rfl) ⟨592007, by rfl⟩ : syracuseStep 3157373 = 1184015) (by norm_num)
theorem B2104915 : Blo 2103435 2104915 := bstep (se 1 (by rfl) ⟨1578686, by rfl⟩ : syracuseStep 2104915 = 3157373) B3157373
theorem B4736069 : Blo 2103435 4736069 := bbase (se 4 (by rfl) ⟨444006, by rfl⟩ : syracuseStep 4736069 = 888013) (by norm_num)
theorem B3157379 : Blo 2103435 3157379 := bstep (se 1 (by rfl) ⟨2368034, by rfl⟩ : syracuseStep 3157379 = 4736069) B4736069
theorem B2104919 : Blo 2103435 2104919 := bstep (se 1 (by rfl) ⟨1578689, by rfl⟩ : syracuseStep 2104919 = 3157379) B3157379
theorem B5994101 : Blo 2103435 5994101 := bbase (se 5 (by rfl) ⟨280973, by rfl⟩ : syracuseStep 5994101 = 561947) (by norm_num)
theorem B3996067 : Blo 2103435 3996067 := bstep (se 1 (by rfl) ⟨2997050, by rfl⟩ : syracuseStep 3996067 = 5994101) B5994101
theorem B5328089 : Blo 2103435 5328089 := bstep (se 2 (by rfl) ⟨1998033, by rfl⟩ : syracuseStep 5328089 = 3996067) B3996067
theorem B3552059 : Blo 2103435 3552059 := bstep (se 1 (by rfl) ⟨2664044, by rfl⟩ : syracuseStep 3552059 = 5328089) B5328089
theorem B2368039 : Blo 2103435 2368039 := bstep (se 1 (by rfl) ⟨1776029, by rfl⟩ : syracuseStep 2368039 = 3552059) B3552059
theorem B3157385 : Blo 2103435 3157385 := bstep (se 2 (by rfl) ⟨1184019, by rfl⟩ : syracuseStep 3157385 = 2368039) B2368039
theorem B2104923 : Blo 2103435 2104923 := bstep (se 1 (by rfl) ⟨1578692, by rfl⟩ : syracuseStep 2104923 = 3157385) B3157385
theorem B10656197 : Blo 2103435 10656197 := bbase (se 4 (by rfl) ⟨999018, by rfl⟩ : syracuseStep 10656197 = 1998037) (by norm_num)
theorem B7104131 : Blo 2103435 7104131 := bstep (se 1 (by rfl) ⟨5328098, by rfl⟩ : syracuseStep 7104131 = 10656197) B10656197
theorem B4736087 : Blo 2103435 4736087 := bstep (se 1 (by rfl) ⟨3552065, by rfl⟩ : syracuseStep 4736087 = 7104131) B7104131
theorem B3157391 : Blo 2103435 3157391 := bstep (se 1 (by rfl) ⟨2368043, by rfl⟩ : syracuseStep 3157391 = 4736087) B4736087
theorem B2104927 : Blo 2103435 2104927 := bstep (se 1 (by rfl) ⟨1578695, by rfl⟩ : syracuseStep 2104927 = 3157391) B3157391
theorem B3157397 : Blo 2103435 3157397 := bbase (se 6 (by rfl) ⟨74001, by rfl⟩ : syracuseStep 3157397 = 148003) (by norm_num)
theorem B2104931 : Blo 2103435 2104931 := bstep (se 1 (by rfl) ⟨1578698, by rfl⟩ : syracuseStep 2104931 = 3157397) B3157397
theorem B3371701 : Blo 2103435 3371701 := bbase (se 5 (by rfl) ⟨158048, by rfl⟩ : syracuseStep 3371701 = 316097) (by norm_num)
theorem B4495601 : Blo 2103435 4495601 := bstep (se 2 (by rfl) ⟨1685850, by rfl⟩ : syracuseStep 4495601 = 3371701) B3371701
theorem B11988269 : Blo 2103435 11988269 := bstep (se 3 (by rfl) ⟨2247800, by rfl⟩ : syracuseStep 11988269 = 4495601) B4495601
theorem B7992179 : Blo 2103435 7992179 := bstep (se 1 (by rfl) ⟨5994134, by rfl⟩ : syracuseStep 7992179 = 11988269) B11988269
theorem B5328119 : Blo 2103435 5328119 := bstep (se 1 (by rfl) ⟨3996089, by rfl⟩ : syracuseStep 5328119 = 7992179) B7992179
theorem B3552079 : Blo 2103435 3552079 := bstep (se 1 (by rfl) ⟨2664059, by rfl⟩ : syracuseStep 3552079 = 5328119) B5328119
theorem B4736105 : Blo 2103435 4736105 := bstep (se 2 (by rfl) ⟨1776039, by rfl⟩ : syracuseStep 4736105 = 3552079) B3552079
theorem B3157403 : Blo 2103435 3157403 := bstep (se 1 (by rfl) ⟨2368052, by rfl⟩ : syracuseStep 3157403 = 4736105) B4736105
theorem B2104935 : Blo 2103435 2104935 := bstep (se 1 (by rfl) ⟨1578701, by rfl⟩ : syracuseStep 2104935 = 3157403) B3157403
theorem B2368057 : Blo 2103435 2368057 := bbase (se 2 (by rfl) ⟨888021, by rfl⟩ : syracuseStep 2368057 = 1776043) (by norm_num)
theorem B3157409 : Blo 2103435 3157409 := bstep (se 2 (by rfl) ⟨1184028, by rfl⟩ : syracuseStep 3157409 = 2368057) B2368057
theorem B2104939 : Blo 2103435 2104939 := bstep (se 1 (by rfl) ⟨1578704, by rfl⟩ : syracuseStep 2104939 = 3157409) B3157409
theorem B2247809 : Blo 2103435 2247809 := bbase (se 2 (by rfl) ⟨842928, by rfl⟩ : syracuseStep 2247809 = 1685857) (by norm_num)
theorem B5994157 : Blo 2103435 5994157 := bstep (se 3 (by rfl) ⟨1123904, by rfl⟩ : syracuseStep 5994157 = 2247809) B2247809
theorem B7992209 : Blo 2103435 7992209 := bstep (se 2 (by rfl) ⟨2997078, by rfl⟩ : syracuseStep 7992209 = 5994157) B5994157
theorem B5328139 : Blo 2103435 5328139 := bstep (se 1 (by rfl) ⟨3996104, by rfl⟩ : syracuseStep 5328139 = 7992209) B7992209
theorem B7104185 : Blo 2103435 7104185 := bstep (se 2 (by rfl) ⟨2664069, by rfl⟩ : syracuseStep 7104185 = 5328139) B5328139
theorem B4736123 : Blo 2103435 4736123 := bstep (se 1 (by rfl) ⟨3552092, by rfl⟩ : syracuseStep 4736123 = 7104185) B7104185
theorem B3157415 : Blo 2103435 3157415 := bstep (se 1 (by rfl) ⟨2368061, by rfl⟩ : syracuseStep 3157415 = 4736123) B4736123
theorem B2104943 : Blo 2103435 2104943 := bstep (se 1 (by rfl) ⟨1578707, by rfl⟩ : syracuseStep 2104943 = 3157415) B3157415
theorem B3157421 : Blo 2103435 3157421 := bbase (se 3 (by rfl) ⟨592016, by rfl⟩ : syracuseStep 3157421 = 1184033) (by norm_num)
theorem B2104947 : Blo 2103435 2104947 := bstep (se 1 (by rfl) ⟨1578710, by rfl⟩ : syracuseStep 2104947 = 3157421) B3157421
theorem B4736141 : Blo 2103435 4736141 := bbase (se 3 (by rfl) ⟨888026, by rfl⟩ : syracuseStep 4736141 = 1776053) (by norm_num)
theorem B3157427 : Blo 2103435 3157427 := bstep (se 1 (by rfl) ⟨2368070, by rfl⟩ : syracuseStep 3157427 = 4736141) B4736141
theorem B2104951 : Blo 2103435 2104951 := bstep (se 1 (by rfl) ⟨1578713, by rfl⟩ : syracuseStep 2104951 = 3157427) B3157427
theorem B2664085 : Blo 2103435 2664085 := bbase (se 6 (by rfl) ⟨62439, by rfl⟩ : syracuseStep 2664085 = 124879) (by norm_num)
theorem B3552113 : Blo 2103435 3552113 := bstep (se 2 (by rfl) ⟨1332042, by rfl⟩ : syracuseStep 3552113 = 2664085) B2664085
theorem B2368075 : Blo 2103435 2368075 := bstep (se 1 (by rfl) ⟨1776056, by rfl⟩ : syracuseStep 2368075 = 3552113) B3552113
theorem B3157433 : Blo 2103435 3157433 := bstep (se 2 (by rfl) ⟨1184037, by rfl⟩ : syracuseStep 3157433 = 2368075) B2368075
theorem B2104955 : Blo 2103435 2104955 := bstep (se 1 (by rfl) ⟨1578716, by rfl⟩ : syracuseStep 2104955 = 3157433) B3157433
theorem B17069429 : Blo 2103435 17069429 := bbase (se 5 (by rfl) ⟨800129, by rfl⟩ : syracuseStep 17069429 = 1600259) (by norm_num)
theorem B11379619 : Blo 2103435 11379619 := bstep (se 1 (by rfl) ⟨8534714, by rfl⟩ : syracuseStep 11379619 = 17069429) B17069429
theorem B60691301 : Blo 2103435 60691301 := bstep (se 4 (by rfl) ⟨5689809, by rfl⟩ : syracuseStep 60691301 = 11379619) B11379619
theorem B40460867 : Blo 2103435 40460867 := bstep (se 1 (by rfl) ⟨30345650, by rfl⟩ : syracuseStep 40460867 = 60691301) B60691301
theorem B26973911 : Blo 2103435 26973911 := bstep (se 1 (by rfl) ⟨20230433, by rfl⟩ : syracuseStep 26973911 = 40460867) B40460867
theorem B17982607 : Blo 2103435 17982607 := bstep (se 1 (by rfl) ⟨13486955, by rfl⟩ : syracuseStep 17982607 = 26973911) B26973911
theorem B23976809 : Blo 2103435 23976809 := bstep (se 2 (by rfl) ⟨8991303, by rfl⟩ : syracuseStep 23976809 = 17982607) B17982607
theorem B15984539 : Blo 2103435 15984539 := bstep (se 1 (by rfl) ⟨11988404, by rfl⟩ : syracuseStep 15984539 = 23976809) B23976809
theorem B10656359 : Blo 2103435 10656359 := bstep (se 1 (by rfl) ⟨7992269, by rfl⟩ : syracuseStep 10656359 = 15984539) B15984539
theorem B7104239 : Blo 2103435 7104239 := bstep (se 1 (by rfl) ⟨5328179, by rfl⟩ : syracuseStep 7104239 = 10656359) B10656359
theorem B4736159 : Blo 2103435 4736159 := bstep (se 1 (by rfl) ⟨3552119, by rfl⟩ : syracuseStep 4736159 = 7104239) B7104239
theorem B3157439 : Blo 2103435 3157439 := bstep (se 1 (by rfl) ⟨2368079, by rfl⟩ : syracuseStep 3157439 = 4736159) B4736159
theorem B2104959 : Blo 2103435 2104959 := bstep (se 1 (by rfl) ⟨1578719, by rfl⟩ : syracuseStep 2104959 = 3157439) B3157439
theorem B3157445 : Blo 2103435 3157445 := bbase (se 4 (by rfl) ⟨296010, by rfl⟩ : syracuseStep 3157445 = 592021) (by norm_num)
theorem B2104963 : Blo 2103435 2104963 := bstep (se 1 (by rfl) ⟨1578722, by rfl⟩ : syracuseStep 2104963 = 3157445) B3157445
theorem B3552133 : Blo 2103435 3552133 := bbase (se 4 (by rfl) ⟨333012, by rfl⟩ : syracuseStep 3552133 = 666025) (by norm_num)
theorem B4736177 : Blo 2103435 4736177 := bstep (se 2 (by rfl) ⟨1776066, by rfl⟩ : syracuseStep 4736177 = 3552133) B3552133
theorem B3157451 : Blo 2103435 3157451 := bstep (se 1 (by rfl) ⟨2368088, by rfl⟩ : syracuseStep 3157451 = 4736177) B4736177
theorem B2104967 : Blo 2103435 2104967 := bstep (se 1 (by rfl) ⟨1578725, by rfl⟩ : syracuseStep 2104967 = 3157451) B3157451
theorem B2368093 : Blo 2103435 2368093 := bbase (se 3 (by rfl) ⟨444017, by rfl⟩ : syracuseStep 2368093 = 888035) (by norm_num)
theorem B3157457 : Blo 2103435 3157457 := bstep (se 2 (by rfl) ⟨1184046, by rfl⟩ : syracuseStep 3157457 = 2368093) B2368093
theorem B2104971 : Blo 2103435 2104971 := bstep (se 1 (by rfl) ⟨1578728, by rfl⟩ : syracuseStep 2104971 = 3157457) B3157457
theorem B7104293 : Blo 2103435 7104293 := bbase (se 4 (by rfl) ⟨666027, by rfl⟩ : syracuseStep 7104293 = 1332055) (by norm_num)
theorem B4736195 : Blo 2103435 4736195 := bstep (se 1 (by rfl) ⟨3552146, by rfl⟩ : syracuseStep 4736195 = 7104293) B7104293
theorem B3157463 : Blo 2103435 3157463 := bstep (se 1 (by rfl) ⟨2368097, by rfl⟩ : syracuseStep 3157463 = 4736195) B4736195
theorem B2104975 : Blo 2103435 2104975 := bstep (se 1 (by rfl) ⟨1578731, by rfl⟩ : syracuseStep 2104975 = 3157463) B3157463
theorem B3157469 : Blo 2103435 3157469 := bbase (se 3 (by rfl) ⟨592025, by rfl⟩ : syracuseStep 3157469 = 1184051) (by norm_num)
theorem B2104979 : Blo 2103435 2104979 := bstep (se 1 (by rfl) ⟨1578734, by rfl⟩ : syracuseStep 2104979 = 3157469) B3157469
theorem B4736213 : Blo 2103435 4736213 := bbase (se 7 (by rfl) ⟨55502, by rfl⟩ : syracuseStep 4736213 = 111005) (by norm_num)
theorem B3157475 : Blo 2103435 3157475 := bstep (se 1 (by rfl) ⟨2368106, by rfl⟩ : syracuseStep 3157475 = 4736213) B4736213
theorem B2104983 : Blo 2103435 2104983 := bstep (se 1 (by rfl) ⟨1578737, by rfl⟩ : syracuseStep 2104983 = 3157475) B3157475
theorem B5057677 : Blo 2103435 5057677 := bbase (se 3 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 5057677 = 1896629) (by norm_num)
theorem B6743569 : Blo 2103435 6743569 := bstep (se 2 (by rfl) ⟨2528838, by rfl⟩ : syracuseStep 6743569 = 5057677) B5057677
theorem B8991425 : Blo 2103435 8991425 := bstep (se 2 (by rfl) ⟨3371784, by rfl⟩ : syracuseStep 8991425 = 6743569) B6743569
theorem B5994283 : Blo 2103435 5994283 := bstep (se 1 (by rfl) ⟨4495712, by rfl⟩ : syracuseStep 5994283 = 8991425) B8991425
theorem B7992377 : Blo 2103435 7992377 := bstep (se 2 (by rfl) ⟨2997141, by rfl⟩ : syracuseStep 7992377 = 5994283) B5994283
theorem B5328251 : Blo 2103435 5328251 := bstep (se 1 (by rfl) ⟨3996188, by rfl⟩ : syracuseStep 5328251 = 7992377) B7992377
theorem B3552167 : Blo 2103435 3552167 := bstep (se 1 (by rfl) ⟨2664125, by rfl⟩ : syracuseStep 3552167 = 5328251) B5328251
theorem B2368111 : Blo 2103435 2368111 := bstep (se 1 (by rfl) ⟨1776083, by rfl⟩ : syracuseStep 2368111 = 3552167) B3552167
theorem B3157481 : Blo 2103435 3157481 := bstep (se 2 (by rfl) ⟨1184055, by rfl⟩ : syracuseStep 3157481 = 2368111) B2368111
theorem B2104987 : Blo 2103435 2104987 := bstep (se 1 (by rfl) ⟨1578740, by rfl⟩ : syracuseStep 2104987 = 3157481) B3157481
theorem B14599061 : Blo 2103435 14599061 := bbase (se 6 (by rfl) ⟨342165, by rfl⟩ : syracuseStep 14599061 = 684331) (by norm_num)
theorem B9732707 : Blo 2103435 9732707 := bstep (se 1 (by rfl) ⟨7299530, by rfl⟩ : syracuseStep 9732707 = 14599061) B14599061
theorem B6488471 : Blo 2103435 6488471 := bstep (se 1 (by rfl) ⟨4866353, by rfl⟩ : syracuseStep 6488471 = 9732707) B9732707
theorem B4325647 : Blo 2103435 4325647 := bstep (se 1 (by rfl) ⟨3244235, by rfl⟩ : syracuseStep 4325647 = 6488471) B6488471
theorem B5767529 : Blo 2103435 5767529 := bstep (se 2 (by rfl) ⟨2162823, by rfl⟩ : syracuseStep 5767529 = 4325647) B4325647
theorem B15380077 : Blo 2103435 15380077 := bstep (se 3 (by rfl) ⟨2883764, by rfl⟩ : syracuseStep 15380077 = 5767529) B5767529
theorem B20506769 : Blo 2103435 20506769 := bstep (se 2 (by rfl) ⟨7690038, by rfl⟩ : syracuseStep 20506769 = 15380077) B15380077
theorem B13671179 : Blo 2103435 13671179 := bstep (se 1 (by rfl) ⟨10253384, by rfl⟩ : syracuseStep 13671179 = 20506769) B20506769
theorem B9114119 : Blo 2103435 9114119 := bstep (se 1 (by rfl) ⟨6835589, by rfl⟩ : syracuseStep 9114119 = 13671179) B13671179
theorem B6076079 : Blo 2103435 6076079 := bstep (se 1 (by rfl) ⟨4557059, by rfl⟩ : syracuseStep 6076079 = 9114119) B9114119
theorem B4050719 : Blo 2103435 4050719 := bstep (se 1 (by rfl) ⟨3038039, by rfl⟩ : syracuseStep 4050719 = 6076079) B6076079
theorem B2700479 : Blo 2103435 2700479 := bstep (se 1 (by rfl) ⟨2025359, by rfl⟩ : syracuseStep 2700479 = 4050719) B4050719
theorem B7201277 : Blo 2103435 7201277 := bstep (se 3 (by rfl) ⟨1350239, by rfl⟩ : syracuseStep 7201277 = 2700479) B2700479
theorem B4800851 : Blo 2103435 4800851 := bstep (se 1 (by rfl) ⟨3600638, by rfl⟩ : syracuseStep 4800851 = 7201277) B7201277
theorem B3200567 : Blo 2103435 3200567 := bstep (se 1 (by rfl) ⟨2400425, by rfl⟩ : syracuseStep 3200567 = 4800851) B4800851
theorem B8534845 : Blo 2103435 8534845 := bstep (se 3 (by rfl) ⟨1600283, by rfl⟩ : syracuseStep 8534845 = 3200567) B3200567
theorem B11379793 : Blo 2103435 11379793 := bstep (se 2 (by rfl) ⟨4267422, by rfl⟩ : syracuseStep 11379793 = 8534845) B8534845
theorem B15173057 : Blo 2103435 15173057 := bstep (se 2 (by rfl) ⟨5689896, by rfl⟩ : syracuseStep 15173057 = 11379793) B11379793
theorem B10115371 : Blo 2103435 10115371 := bstep (se 1 (by rfl) ⟨7586528, by rfl⟩ : syracuseStep 10115371 = 15173057) B15173057
theorem B13487161 : Blo 2103435 13487161 := bstep (se 2 (by rfl) ⟨5057685, by rfl⟩ : syracuseStep 13487161 = 10115371) B10115371
theorem B17982881 : Blo 2103435 17982881 := bstep (se 2 (by rfl) ⟨6743580, by rfl⟩ : syracuseStep 17982881 = 13487161) B13487161
theorem B11988587 : Blo 2103435 11988587 := bstep (se 1 (by rfl) ⟨8991440, by rfl⟩ : syracuseStep 11988587 = 17982881) B17982881
theorem B7992391 : Blo 2103435 7992391 := bstep (se 1 (by rfl) ⟨5994293, by rfl⟩ : syracuseStep 7992391 = 11988587) B11988587
theorem B10656521 : Blo 2103435 10656521 := bstep (se 2 (by rfl) ⟨3996195, by rfl⟩ : syracuseStep 10656521 = 7992391) B7992391
theorem B7104347 : Blo 2103435 7104347 := bstep (se 1 (by rfl) ⟨5328260, by rfl⟩ : syracuseStep 7104347 = 10656521) B10656521
theorem B4736231 : Blo 2103435 4736231 := bstep (se 1 (by rfl) ⟨3552173, by rfl⟩ : syracuseStep 4736231 = 7104347) B7104347
theorem B3157487 : Blo 2103435 3157487 := bstep (se 1 (by rfl) ⟨2368115, by rfl⟩ : syracuseStep 3157487 = 4736231) B4736231
theorem B2104991 : Blo 2103435 2104991 := bstep (se 1 (by rfl) ⟨1578743, by rfl⟩ : syracuseStep 2104991 = 3157487) B3157487
theorem B3157493 : Blo 2103435 3157493 := bbase (se 5 (by rfl) ⟨148007, by rfl⟩ : syracuseStep 3157493 = 296015) (by norm_num)
theorem B2104995 : Blo 2103435 2104995 := bstep (se 1 (by rfl) ⟨1578746, by rfl⟩ : syracuseStep 2104995 = 3157493) B3157493
theorem B2247869 : Blo 2103435 2247869 := bbase (se 3 (by rfl) ⟨421475, by rfl⟩ : syracuseStep 2247869 = 842951) (by norm_num)
theorem B5994317 : Blo 2103435 5994317 := bstep (se 3 (by rfl) ⟨1123934, by rfl⟩ : syracuseStep 5994317 = 2247869) B2247869
theorem B3996211 : Blo 2103435 3996211 := bstep (se 1 (by rfl) ⟨2997158, by rfl⟩ : syracuseStep 3996211 = 5994317) B5994317
theorem B5328281 : Blo 2103435 5328281 := bstep (se 2 (by rfl) ⟨1998105, by rfl⟩ : syracuseStep 5328281 = 3996211) B3996211
theorem B3552187 : Blo 2103435 3552187 := bstep (se 1 (by rfl) ⟨2664140, by rfl⟩ : syracuseStep 3552187 = 5328281) B5328281
theorem B4736249 : Blo 2103435 4736249 := bstep (se 2 (by rfl) ⟨1776093, by rfl⟩ : syracuseStep 4736249 = 3552187) B3552187
theorem B3157499 : Blo 2103435 3157499 := bstep (se 1 (by rfl) ⟨2368124, by rfl⟩ : syracuseStep 3157499 = 4736249) B4736249
theorem B2104999 : Blo 2103435 2104999 := bstep (se 1 (by rfl) ⟨1578749, by rfl⟩ : syracuseStep 2104999 = 3157499) B3157499
theorem B2368129 : Blo 2103435 2368129 := bbase (se 2 (by rfl) ⟨888048, by rfl⟩ : syracuseStep 2368129 = 1776097) (by norm_num)
theorem B3157505 : Blo 2103435 3157505 := bstep (se 2 (by rfl) ⟨1184064, by rfl⟩ : syracuseStep 3157505 = 2368129) B2368129
theorem B2105003 : Blo 2103435 2105003 := bstep (se 1 (by rfl) ⟨1578752, by rfl⟩ : syracuseStep 2105003 = 3157505) B3157505
theorem B5328301 : Blo 2103435 5328301 := bbase (se 3 (by rfl) ⟨999056, by rfl⟩ : syracuseStep 5328301 = 1998113) (by norm_num)
theorem B7104401 : Blo 2103435 7104401 := bstep (se 2 (by rfl) ⟨2664150, by rfl⟩ : syracuseStep 7104401 = 5328301) B5328301
theorem B4736267 : Blo 2103435 4736267 := bstep (se 1 (by rfl) ⟨3552200, by rfl⟩ : syracuseStep 4736267 = 7104401) B7104401
theorem B3157511 : Blo 2103435 3157511 := bstep (se 1 (by rfl) ⟨2368133, by rfl⟩ : syracuseStep 3157511 = 4736267) B4736267
theorem B2105007 : Blo 2103435 2105007 := bstep (se 1 (by rfl) ⟨1578755, by rfl⟩ : syracuseStep 2105007 = 3157511) B3157511
theorem B3157517 : Blo 2103435 3157517 := bbase (se 3 (by rfl) ⟨592034, by rfl⟩ : syracuseStep 3157517 = 1184069) (by norm_num)
theorem B2105011 : Blo 2103435 2105011 := bstep (se 1 (by rfl) ⟨1578758, by rfl⟩ : syracuseStep 2105011 = 3157517) B3157517
theorem B4736285 : Blo 2103435 4736285 := bbase (se 3 (by rfl) ⟨888053, by rfl⟩ : syracuseStep 4736285 = 1776107) (by norm_num)
theorem B3157523 : Blo 2103435 3157523 := bstep (se 1 (by rfl) ⟨2368142, by rfl⟩ : syracuseStep 3157523 = 4736285) B4736285
theorem B2105015 : Blo 2103435 2105015 := bstep (se 1 (by rfl) ⟨1578761, by rfl⟩ : syracuseStep 2105015 = 3157523) B3157523
theorem B3552221 : Blo 2103435 3552221 := bbase (se 3 (by rfl) ⟨666041, by rfl⟩ : syracuseStep 3552221 = 1332083) (by norm_num)
theorem B2368147 : Blo 2103435 2368147 := bstep (se 1 (by rfl) ⟨1776110, by rfl⟩ : syracuseStep 2368147 = 3552221) B3552221
theorem B3157529 : Blo 2103435 3157529 := bstep (se 2 (by rfl) ⟨1184073, by rfl⟩ : syracuseStep 3157529 = 2368147) B2368147
theorem B2105019 : Blo 2103435 2105019 := bstep (se 1 (by rfl) ⟨1578764, by rfl⟩ : syracuseStep 2105019 = 3157529) B3157529
theorem B10115525 : Blo 2103435 10115525 := bbase (se 4 (by rfl) ⟨948330, by rfl⟩ : syracuseStep 10115525 = 1896661) (by norm_num)
theorem B6743683 : Blo 2103435 6743683 := bstep (se 1 (by rfl) ⟨5057762, by rfl⟩ : syracuseStep 6743683 = 10115525) B10115525
theorem B8991577 : Blo 2103435 8991577 := bstep (se 2 (by rfl) ⟨3371841, by rfl⟩ : syracuseStep 8991577 = 6743683) B6743683
theorem B11988769 : Blo 2103435 11988769 := bstep (se 2 (by rfl) ⟨4495788, by rfl⟩ : syracuseStep 11988769 = 8991577) B8991577
theorem B15985025 : Blo 2103435 15985025 := bstep (se 2 (by rfl) ⟨5994384, by rfl⟩ : syracuseStep 15985025 = 11988769) B11988769
theorem B10656683 : Blo 2103435 10656683 := bstep (se 1 (by rfl) ⟨7992512, by rfl⟩ : syracuseStep 10656683 = 15985025) B15985025
theorem B7104455 : Blo 2103435 7104455 := bstep (se 1 (by rfl) ⟨5328341, by rfl⟩ : syracuseStep 7104455 = 10656683) B10656683
theorem B4736303 : Blo 2103435 4736303 := bstep (se 1 (by rfl) ⟨3552227, by rfl⟩ : syracuseStep 4736303 = 7104455) B7104455
theorem B3157535 : Blo 2103435 3157535 := bstep (se 1 (by rfl) ⟨2368151, by rfl⟩ : syracuseStep 3157535 = 4736303) B4736303
theorem B2105023 : Blo 2103435 2105023 := bstep (se 1 (by rfl) ⟨1578767, by rfl⟩ : syracuseStep 2105023 = 3157535) B3157535
theorem B3157541 : Blo 2103435 3157541 := bbase (se 4 (by rfl) ⟨296019, by rfl⟩ : syracuseStep 3157541 = 592039) (by norm_num)
theorem B2105027 : Blo 2103435 2105027 := bstep (se 1 (by rfl) ⟨1578770, by rfl⟩ : syracuseStep 2105027 = 3157541) B3157541
theorem B2664181 : Blo 2103435 2664181 := bbase (se 5 (by rfl) ⟨124883, by rfl⟩ : syracuseStep 2664181 = 249767) (by norm_num)
theorem B3552241 : Blo 2103435 3552241 := bstep (se 2 (by rfl) ⟨1332090, by rfl⟩ : syracuseStep 3552241 = 2664181) B2664181
theorem B4736321 : Blo 2103435 4736321 := bstep (se 2 (by rfl) ⟨1776120, by rfl⟩ : syracuseStep 4736321 = 3552241) B3552241
theorem B3157547 : Blo 2103435 3157547 := bstep (se 1 (by rfl) ⟨2368160, by rfl⟩ : syracuseStep 3157547 = 4736321) B4736321
theorem B2105031 : Blo 2103435 2105031 := bstep (se 1 (by rfl) ⟨1578773, by rfl⟩ : syracuseStep 2105031 = 3157547) B3157547
theorem B2368165 : Blo 2103435 2368165 := bbase (se 4 (by rfl) ⟨222015, by rfl⟩ : syracuseStep 2368165 = 444031) (by norm_num)
theorem B3157553 : Blo 2103435 3157553 := bstep (se 2 (by rfl) ⟨1184082, by rfl⟩ : syracuseStep 3157553 = 2368165) B2368165
theorem B2105035 : Blo 2103435 2105035 := bstep (se 1 (by rfl) ⟨1578776, by rfl⟩ : syracuseStep 2105035 = 3157553) B3157553
theorem B2162873 : Blo 2103435 2162873 := bbase (se 2 (by rfl) ⟨811077, by rfl⟩ : syracuseStep 2162873 = 1622155) (by norm_num)
theorem B5767661 : Blo 2103435 5767661 := bstep (se 3 (by rfl) ⟨1081436, by rfl⟩ : syracuseStep 5767661 = 2162873) B2162873
theorem B3845107 : Blo 2103435 3845107 := bstep (se 1 (by rfl) ⟨2883830, by rfl⟩ : syracuseStep 3845107 = 5767661) B5767661
theorem B5126809 : Blo 2103435 5126809 := bstep (se 2 (by rfl) ⟨1922553, by rfl⟩ : syracuseStep 5126809 = 3845107) B3845107
theorem B6835745 : Blo 2103435 6835745 := bstep (se 2 (by rfl) ⟨2563404, by rfl⟩ : syracuseStep 6835745 = 5126809) B5126809
theorem B4557163 : Blo 2103435 4557163 := bstep (se 1 (by rfl) ⟨3417872, by rfl⟩ : syracuseStep 4557163 = 6835745) B6835745
theorem B6076217 : Blo 2103435 6076217 := bstep (se 2 (by rfl) ⟨2278581, by rfl⟩ : syracuseStep 6076217 = 4557163) B4557163
theorem B4050811 : Blo 2103435 4050811 := bstep (se 1 (by rfl) ⟨3038108, by rfl⟩ : syracuseStep 4050811 = 6076217) B6076217
theorem B5401081 : Blo 2103435 5401081 := bstep (se 2 (by rfl) ⟨2025405, by rfl⟩ : syracuseStep 5401081 = 4050811) B4050811
theorem B7201441 : Blo 2103435 7201441 := bstep (se 2 (by rfl) ⟨2700540, by rfl⟩ : syracuseStep 7201441 = 5401081) B5401081
theorem B9601921 : Blo 2103435 9601921 := bstep (se 2 (by rfl) ⟨3600720, by rfl⟩ : syracuseStep 9601921 = 7201441) B7201441
theorem B51210245 : Blo 2103435 51210245 := bstep (se 4 (by rfl) ⟨4800960, by rfl⟩ : syracuseStep 51210245 = 9601921) B9601921
theorem B34140163 : Blo 2103435 34140163 := bstep (se 1 (by rfl) ⟨25605122, by rfl⟩ : syracuseStep 34140163 = 51210245) B51210245
theorem B45520217 : Blo 2103435 45520217 := bstep (se 2 (by rfl) ⟨17070081, by rfl⟩ : syracuseStep 45520217 = 34140163) B34140163
theorem B30346811 : Blo 2103435 30346811 := bstep (se 1 (by rfl) ⟨22760108, by rfl⟩ : syracuseStep 30346811 = 45520217) B45520217
theorem B20231207 : Blo 2103435 20231207 := bstep (se 1 (by rfl) ⟨15173405, by rfl⟩ : syracuseStep 20231207 = 30346811) B30346811
theorem B13487471 : Blo 2103435 13487471 := bstep (se 1 (by rfl) ⟨10115603, by rfl⟩ : syracuseStep 13487471 = 20231207) B20231207
theorem B8991647 : Blo 2103435 8991647 := bstep (se 1 (by rfl) ⟨6743735, by rfl⟩ : syracuseStep 8991647 = 13487471) B13487471
theorem B5994431 : Blo 2103435 5994431 := bstep (se 1 (by rfl) ⟨4495823, by rfl⟩ : syracuseStep 5994431 = 8991647) B8991647
theorem B3996287 : Blo 2103435 3996287 := bstep (se 1 (by rfl) ⟨2997215, by rfl⟩ : syracuseStep 3996287 = 5994431) B5994431
theorem B2664191 : Blo 2103435 2664191 := bstep (se 1 (by rfl) ⟨1998143, by rfl⟩ : syracuseStep 2664191 = 3996287) B3996287
theorem B7104509 : Blo 2103435 7104509 := bstep (se 3 (by rfl) ⟨1332095, by rfl⟩ : syracuseStep 7104509 = 2664191) B2664191
theorem B4736339 : Blo 2103435 4736339 := bstep (se 1 (by rfl) ⟨3552254, by rfl⟩ : syracuseStep 4736339 = 7104509) B7104509
theorem B3157559 : Blo 2103435 3157559 := bstep (se 1 (by rfl) ⟨2368169, by rfl⟩ : syracuseStep 3157559 = 4736339) B4736339
theorem B2105039 : Blo 2103435 2105039 := bstep (se 1 (by rfl) ⟨1578779, by rfl⟩ : syracuseStep 2105039 = 3157559) B3157559
theorem B3157565 : Blo 2103435 3157565 := bbase (se 3 (by rfl) ⟨592043, by rfl⟩ : syracuseStep 3157565 = 1184087) (by norm_num)
theorem B2105043 : Blo 2103435 2105043 := bstep (se 1 (by rfl) ⟨1578782, by rfl⟩ : syracuseStep 2105043 = 3157565) B3157565
theorem B4736357 : Blo 2103435 4736357 := bbase (se 4 (by rfl) ⟨444033, by rfl⟩ : syracuseStep 4736357 = 888067) (by norm_num)
theorem B3157571 : Blo 2103435 3157571 := bstep (se 1 (by rfl) ⟨2368178, by rfl⟩ : syracuseStep 3157571 = 4736357) B4736357
theorem B2105047 : Blo 2103435 2105047 := bstep (se 1 (by rfl) ⟨1578785, by rfl⟩ : syracuseStep 2105047 = 3157571) B3157571
theorem B5328413 : Blo 2103435 5328413 := bbase (se 3 (by rfl) ⟨999077, by rfl⟩ : syracuseStep 5328413 = 1998155) (by norm_num)
theorem B3552275 : Blo 2103435 3552275 := bstep (se 1 (by rfl) ⟨2664206, by rfl⟩ : syracuseStep 3552275 = 5328413) B5328413
theorem B2368183 : Blo 2103435 2368183 := bstep (se 1 (by rfl) ⟨1776137, by rfl⟩ : syracuseStep 2368183 = 3552275) B3552275
theorem B3157577 : Blo 2103435 3157577 := bstep (se 2 (by rfl) ⟨1184091, by rfl⟩ : syracuseStep 3157577 = 2368183) B2368183
theorem B2105051 : Blo 2103435 2105051 := bstep (se 1 (by rfl) ⟨1578788, by rfl⟩ : syracuseStep 2105051 = 3157577) B3157577
theorem B3996317 : Blo 2103435 3996317 := bbase (se 3 (by rfl) ⟨749309, by rfl⟩ : syracuseStep 3996317 = 1498619) (by norm_num)
theorem B10656845 : Blo 2103435 10656845 := bstep (se 3 (by rfl) ⟨1998158, by rfl⟩ : syracuseStep 10656845 = 3996317) B3996317
theorem B7104563 : Blo 2103435 7104563 := bstep (se 1 (by rfl) ⟨5328422, by rfl⟩ : syracuseStep 7104563 = 10656845) B10656845
theorem B4736375 : Blo 2103435 4736375 := bstep (se 1 (by rfl) ⟨3552281, by rfl⟩ : syracuseStep 4736375 = 7104563) B7104563
theorem B3157583 : Blo 2103435 3157583 := bstep (se 1 (by rfl) ⟨2368187, by rfl⟩ : syracuseStep 3157583 = 4736375) B4736375
theorem B2105055 : Blo 2103435 2105055 := bstep (se 1 (by rfl) ⟨1578791, by rfl⟩ : syracuseStep 2105055 = 3157583) B3157583
theorem B3157589 : Blo 2103435 3157589 := bbase (se 8 (by rfl) ⟨18501, by rfl⟩ : syracuseStep 3157589 = 37003) (by norm_num)
theorem B2105059 : Blo 2103435 2105059 := bstep (se 1 (by rfl) ⟨1578794, by rfl⟩ : syracuseStep 2105059 = 3157589) B3157589
theorem B8991749 : Blo 2103435 8991749 := bbase (se 4 (by rfl) ⟨842976, by rfl⟩ : syracuseStep 8991749 = 1685953) (by norm_num)
theorem B5994499 : Blo 2103435 5994499 := bstep (se 1 (by rfl) ⟨4495874, by rfl⟩ : syracuseStep 5994499 = 8991749) B8991749
theorem B7992665 : Blo 2103435 7992665 := bstep (se 2 (by rfl) ⟨2997249, by rfl⟩ : syracuseStep 7992665 = 5994499) B5994499
theorem B5328443 : Blo 2103435 5328443 := bstep (se 1 (by rfl) ⟨3996332, by rfl⟩ : syracuseStep 5328443 = 7992665) B7992665
theorem B3552295 : Blo 2103435 3552295 := bstep (se 1 (by rfl) ⟨2664221, by rfl⟩ : syracuseStep 3552295 = 5328443) B5328443
theorem B4736393 : Blo 2103435 4736393 := bstep (se 2 (by rfl) ⟨1776147, by rfl⟩ : syracuseStep 4736393 = 3552295) B3552295
theorem B3157595 : Blo 2103435 3157595 := bstep (se 1 (by rfl) ⟨2368196, by rfl⟩ : syracuseStep 3157595 = 4736393) B4736393
theorem B2105063 : Blo 2103435 2105063 := bstep (se 1 (by rfl) ⟨1578797, by rfl⟩ : syracuseStep 2105063 = 3157595) B3157595
theorem B2368201 : Blo 2103435 2368201 := bbase (se 2 (by rfl) ⟨888075, by rfl⟩ : syracuseStep 2368201 = 1776151) (by norm_num)
theorem B3157601 : Blo 2103435 3157601 := bstep (se 2 (by rfl) ⟨1184100, by rfl⟩ : syracuseStep 3157601 = 2368201) B2368201
theorem B2105067 : Blo 2103435 2105067 := bstep (se 1 (by rfl) ⟨1578800, by rfl⟩ : syracuseStep 2105067 = 3157601) B3157601
theorem B2133793 : Blo 2103435 2133793 := bbase (se 2 (by rfl) ⟨800172, by rfl⟩ : syracuseStep 2133793 = 1600345) (by norm_num)
theorem B2845057 : Blo 2103435 2845057 := bstep (se 2 (by rfl) ⟨1066896, by rfl⟩ : syracuseStep 2845057 = 2133793) B2133793
theorem B3793409 : Blo 2103435 3793409 := bstep (se 2 (by rfl) ⟨1422528, by rfl⟩ : syracuseStep 3793409 = 2845057) B2845057
theorem B2528939 : Blo 2103435 2528939 := bstep (se 1 (by rfl) ⟨1896704, by rfl⟩ : syracuseStep 2528939 = 3793409) B3793409
theorem B6743837 : Blo 2103435 6743837 := bstep (se 3 (by rfl) ⟨1264469, by rfl⟩ : syracuseStep 6743837 = 2528939) B2528939
theorem B17983565 : Blo 2103435 17983565 := bstep (se 3 (by rfl) ⟨3371918, by rfl⟩ : syracuseStep 17983565 = 6743837) B6743837
theorem B11989043 : Blo 2103435 11989043 := bstep (se 1 (by rfl) ⟨8991782, by rfl⟩ : syracuseStep 11989043 = 17983565) B17983565
theorem B7992695 : Blo 2103435 7992695 := bstep (se 1 (by rfl) ⟨5994521, by rfl⟩ : syracuseStep 7992695 = 11989043) B11989043
theorem B5328463 : Blo 2103435 5328463 := bstep (se 1 (by rfl) ⟨3996347, by rfl⟩ : syracuseStep 5328463 = 7992695) B7992695
theorem B7104617 : Blo 2103435 7104617 := bstep (se 2 (by rfl) ⟨2664231, by rfl⟩ : syracuseStep 7104617 = 5328463) B5328463
theorem B4736411 : Blo 2103435 4736411 := bstep (se 1 (by rfl) ⟨3552308, by rfl⟩ : syracuseStep 4736411 = 7104617) B7104617
theorem B3157607 : Blo 2103435 3157607 := bstep (se 1 (by rfl) ⟨2368205, by rfl⟩ : syracuseStep 3157607 = 4736411) B4736411
theorem B2105071 : Blo 2103435 2105071 := bstep (se 1 (by rfl) ⟨1578803, by rfl⟩ : syracuseStep 2105071 = 3157607) B3157607
theorem B3157613 : Blo 2103435 3157613 := bbase (se 3 (by rfl) ⟨592052, by rfl⟩ : syracuseStep 3157613 = 1184105) (by norm_num)
theorem B2105075 : Blo 2103435 2105075 := bstep (se 1 (by rfl) ⟨1578806, by rfl⟩ : syracuseStep 2105075 = 3157613) B3157613
theorem B4736429 : Blo 2103435 4736429 := bbase (se 3 (by rfl) ⟨888080, by rfl⟩ : syracuseStep 4736429 = 1776161) (by norm_num)
theorem B3157619 : Blo 2103435 3157619 := bstep (se 1 (by rfl) ⟨2368214, by rfl⟩ : syracuseStep 3157619 = 4736429) B4736429
theorem B2105079 : Blo 2103435 2105079 := bstep (se 1 (by rfl) ⟨1578809, by rfl⟩ : syracuseStep 2105079 = 3157619) B3157619
theorem B5057909 : Blo 2103435 5057909 := bbase (se 5 (by rfl) ⟨237089, by rfl⟩ : syracuseStep 5057909 = 474179) (by norm_num)
theorem B3371939 : Blo 2103435 3371939 := bstep (se 1 (by rfl) ⟨2528954, by rfl⟩ : syracuseStep 3371939 = 5057909) B5057909
theorem B2247959 : Blo 2103435 2247959 := bstep (se 1 (by rfl) ⟨1685969, by rfl⟩ : syracuseStep 2247959 = 3371939) B3371939
theorem B5994557 : Blo 2103435 5994557 := bstep (se 3 (by rfl) ⟨1123979, by rfl⟩ : syracuseStep 5994557 = 2247959) B2247959
theorem B3996371 : Blo 2103435 3996371 := bstep (se 1 (by rfl) ⟨2997278, by rfl⟩ : syracuseStep 3996371 = 5994557) B5994557
theorem B2664247 : Blo 2103435 2664247 := bstep (se 1 (by rfl) ⟨1998185, by rfl⟩ : syracuseStep 2664247 = 3996371) B3996371
theorem B3552329 : Blo 2103435 3552329 := bstep (se 2 (by rfl) ⟨1332123, by rfl⟩ : syracuseStep 3552329 = 2664247) B2664247
theorem B2368219 : Blo 2103435 2368219 := bstep (se 1 (by rfl) ⟨1776164, by rfl⟩ : syracuseStep 2368219 = 3552329) B3552329
theorem B3157625 : Blo 2103435 3157625 := bstep (se 2 (by rfl) ⟨1184109, by rfl⟩ : syracuseStep 3157625 = 2368219) B2368219
theorem B2105083 : Blo 2103435 2105083 := bstep (se 1 (by rfl) ⟨1578812, by rfl⟩ : syracuseStep 2105083 = 3157625) B3157625
theorem B2162921 : Blo 2103435 2162921 := bbase (se 2 (by rfl) ⟨811095, by rfl⟩ : syracuseStep 2162921 = 1622191) (by norm_num)
theorem B5767789 : Blo 2103435 5767789 := bstep (se 3 (by rfl) ⟨1081460, by rfl⟩ : syracuseStep 5767789 = 2162921) B2162921
theorem B7690385 : Blo 2103435 7690385 := bstep (se 2 (by rfl) ⟨2883894, by rfl⟩ : syracuseStep 7690385 = 5767789) B5767789
theorem B5126923 : Blo 2103435 5126923 := bstep (se 1 (by rfl) ⟨3845192, by rfl⟩ : syracuseStep 5126923 = 7690385) B7690385
theorem B6835897 : Blo 2103435 6835897 := bstep (se 2 (by rfl) ⟨2563461, by rfl⟩ : syracuseStep 6835897 = 5126923) B5126923
theorem B36458117 : Blo 2103435 36458117 := bstep (se 4 (by rfl) ⟨3417948, by rfl⟩ : syracuseStep 36458117 = 6835897) B6835897
theorem B24305411 : Blo 2103435 24305411 := bstep (se 1 (by rfl) ⟨18229058, by rfl⟩ : syracuseStep 24305411 = 36458117) B36458117
theorem B16203607 : Blo 2103435 16203607 := bstep (se 1 (by rfl) ⟨12152705, by rfl⟩ : syracuseStep 16203607 = 24305411) B24305411
theorem B86419237 : Blo 2103435 86419237 := bstep (se 4 (by rfl) ⟨8101803, by rfl⟩ : syracuseStep 86419237 = 16203607) B16203607
theorem B115225649 : Blo 2103435 115225649 := bstep (se 2 (by rfl) ⟨43209618, by rfl⟩ : syracuseStep 115225649 = 86419237) B86419237
theorem B76817099 : Blo 2103435 76817099 := bstep (se 1 (by rfl) ⟨57612824, by rfl⟩ : syracuseStep 76817099 = 115225649) B115225649
theorem B204845597 : Blo 2103435 204845597 := bstep (se 3 (by rfl) ⟨38408549, by rfl⟩ : syracuseStep 204845597 = 76817099) B76817099
theorem B136563731 : Blo 2103435 136563731 := bstep (se 1 (by rfl) ⟨102422798, by rfl⟩ : syracuseStep 136563731 = 204845597) B204845597
theorem B91042487 : Blo 2103435 91042487 := bstep (se 1 (by rfl) ⟨68281865, by rfl⟩ : syracuseStep 91042487 = 136563731) B136563731
theorem B60694991 : Blo 2103435 60694991 := bstep (se 1 (by rfl) ⟨45521243, by rfl⟩ : syracuseStep 60694991 = 91042487) B91042487
theorem B40463327 : Blo 2103435 40463327 := bstep (se 1 (by rfl) ⟨30347495, by rfl⟩ : syracuseStep 40463327 = 60694991) B60694991
theorem B26975551 : Blo 2103435 26975551 := bstep (se 1 (by rfl) ⟨20231663, by rfl⟩ : syracuseStep 26975551 = 40463327) B40463327
theorem B35967401 : Blo 2103435 35967401 := bstep (se 2 (by rfl) ⟨13487775, by rfl⟩ : syracuseStep 35967401 = 26975551) B26975551
theorem B23978267 : Blo 2103435 23978267 := bstep (se 1 (by rfl) ⟨17983700, by rfl⟩ : syracuseStep 23978267 = 35967401) B35967401
theorem B15985511 : Blo 2103435 15985511 := bstep (se 1 (by rfl) ⟨11989133, by rfl⟩ : syracuseStep 15985511 = 23978267) B23978267
theorem B10657007 : Blo 2103435 10657007 := bstep (se 1 (by rfl) ⟨7992755, by rfl⟩ : syracuseStep 10657007 = 15985511) B15985511
theorem B7104671 : Blo 2103435 7104671 := bstep (se 1 (by rfl) ⟨5328503, by rfl⟩ : syracuseStep 7104671 = 10657007) B10657007
theorem B4736447 : Blo 2103435 4736447 := bstep (se 1 (by rfl) ⟨3552335, by rfl⟩ : syracuseStep 4736447 = 7104671) B7104671
theorem B3157631 : Blo 2103435 3157631 := bstep (se 1 (by rfl) ⟨2368223, by rfl⟩ : syracuseStep 3157631 = 4736447) B4736447
theorem B2105087 : Blo 2103435 2105087 := bstep (se 1 (by rfl) ⟨1578815, by rfl⟩ : syracuseStep 2105087 = 3157631) B3157631
theorem B3157637 : Blo 2103435 3157637 := bbase (se 4 (by rfl) ⟨296028, by rfl⟩ : syracuseStep 3157637 = 592057) (by norm_num)
theorem B2105091 : Blo 2103435 2105091 := bstep (se 1 (by rfl) ⟨1578818, by rfl⟩ : syracuseStep 2105091 = 3157637) B3157637
theorem B3552349 : Blo 2103435 3552349 := bbase (se 3 (by rfl) ⟨666065, by rfl⟩ : syracuseStep 3552349 = 1332131) (by norm_num)
theorem B4736465 : Blo 2103435 4736465 := bstep (se 2 (by rfl) ⟨1776174, by rfl⟩ : syracuseStep 4736465 = 3552349) B3552349
theorem B3157643 : Blo 2103435 3157643 := bstep (se 1 (by rfl) ⟨2368232, by rfl⟩ : syracuseStep 3157643 = 4736465) B4736465
theorem B2105095 : Blo 2103435 2105095 := bstep (se 1 (by rfl) ⟨1578821, by rfl⟩ : syracuseStep 2105095 = 3157643) B3157643
theorem B2368237 : Blo 2103435 2368237 := bbase (se 3 (by rfl) ⟨444044, by rfl⟩ : syracuseStep 2368237 = 888089) (by norm_num)
theorem B3157649 : Blo 2103435 3157649 := bstep (se 2 (by rfl) ⟨1184118, by rfl⟩ : syracuseStep 3157649 = 2368237) B2368237
theorem B2105099 : Blo 2103435 2105099 := bstep (se 1 (by rfl) ⟨1578824, by rfl⟩ : syracuseStep 2105099 = 3157649) B3157649
theorem B7104725 : Blo 2103435 7104725 := bbase (se 7 (by rfl) ⟨83258, by rfl⟩ : syracuseStep 7104725 = 166517) (by norm_num)
theorem B4736483 : Blo 2103435 4736483 := bstep (se 1 (by rfl) ⟨3552362, by rfl⟩ : syracuseStep 4736483 = 7104725) B7104725
theorem B3157655 : Blo 2103435 3157655 := bstep (se 1 (by rfl) ⟨2368241, by rfl⟩ : syracuseStep 3157655 = 4736483) B4736483
theorem B2105103 : Blo 2103435 2105103 := bstep (se 1 (by rfl) ⟨1578827, by rfl⟩ : syracuseStep 2105103 = 3157655) B3157655
theorem B3157661 : Blo 2103435 3157661 := bbase (se 3 (by rfl) ⟨592061, by rfl⟩ : syracuseStep 3157661 = 1184123) (by norm_num)
theorem B2105107 : Blo 2103435 2105107 := bstep (se 1 (by rfl) ⟨1578830, by rfl⟩ : syracuseStep 2105107 = 3157661) B3157661
theorem B4736501 : Blo 2103435 4736501 := bbase (se 5 (by rfl) ⟨222023, by rfl⟩ : syracuseStep 4736501 = 444047) (by norm_num)
theorem B3157667 : Blo 2103435 3157667 := bstep (se 1 (by rfl) ⟨2368250, by rfl⟩ : syracuseStep 3157667 = 4736501) B4736501
theorem B2105111 : Blo 2103435 2105111 := bstep (se 1 (by rfl) ⟨1578833, by rfl⟩ : syracuseStep 2105111 = 3157667) B3157667
theorem B3845245 : Blo 2103435 3845245 := bbase (se 3 (by rfl) ⟨720983, by rfl⟩ : syracuseStep 3845245 = 1441967) (by norm_num)
theorem B5126993 : Blo 2103435 5126993 := bstep (se 2 (by rfl) ⟨1922622, by rfl⟩ : syracuseStep 5126993 = 3845245) B3845245
theorem B3417995 : Blo 2103435 3417995 := bstep (se 1 (by rfl) ⟨2563496, by rfl⟩ : syracuseStep 3417995 = 5126993) B5126993
theorem B9114653 : Blo 2103435 9114653 := bstep (se 3 (by rfl) ⟨1708997, by rfl⟩ : syracuseStep 9114653 = 3417995) B3417995
theorem B24305741 : Blo 2103435 24305741 := bstep (se 3 (by rfl) ⟨4557326, by rfl⟩ : syracuseStep 24305741 = 9114653) B9114653
theorem B16203827 : Blo 2103435 16203827 := bstep (se 1 (by rfl) ⟨12152870, by rfl⟩ : syracuseStep 16203827 = 24305741) B24305741
theorem B43210205 : Blo 2103435 43210205 := bstep (se 3 (by rfl) ⟨8101913, by rfl⟩ : syracuseStep 43210205 = 16203827) B16203827
theorem B28806803 : Blo 2103435 28806803 := bstep (se 1 (by rfl) ⟨21605102, by rfl⟩ : syracuseStep 28806803 = 43210205) B43210205
theorem B19204535 : Blo 2103435 19204535 := bstep (se 1 (by rfl) ⟨14403401, by rfl⟩ : syracuseStep 19204535 = 28806803) B28806803
theorem B12803023 : Blo 2103435 12803023 := bstep (se 1 (by rfl) ⟨9602267, by rfl⟩ : syracuseStep 12803023 = 19204535) B19204535
theorem B17070697 : Blo 2103435 17070697 := bstep (se 2 (by rfl) ⟨6401511, by rfl⟩ : syracuseStep 17070697 = 12803023) B12803023
theorem B22760929 : Blo 2103435 22760929 := bstep (se 2 (by rfl) ⟨8535348, by rfl⟩ : syracuseStep 22760929 = 17070697) B17070697
theorem B30347905 : Blo 2103435 30347905 := bstep (se 2 (by rfl) ⟨11380464, by rfl⟩ : syracuseStep 30347905 = 22760929) B22760929
theorem B40463873 : Blo 2103435 40463873 := bstep (se 2 (by rfl) ⟨15173952, by rfl⟩ : syracuseStep 40463873 = 30347905) B30347905
theorem B26975915 : Blo 2103435 26975915 := bstep (se 1 (by rfl) ⟨20231936, by rfl⟩ : syracuseStep 26975915 = 40463873) B40463873
theorem B17983943 : Blo 2103435 17983943 := bstep (se 1 (by rfl) ⟨13487957, by rfl⟩ : syracuseStep 17983943 = 26975915) B26975915
theorem B11989295 : Blo 2103435 11989295 := bstep (se 1 (by rfl) ⟨8991971, by rfl⟩ : syracuseStep 11989295 = 17983943) B17983943
theorem B7992863 : Blo 2103435 7992863 := bstep (se 1 (by rfl) ⟨5994647, by rfl⟩ : syracuseStep 7992863 = 11989295) B11989295
theorem B5328575 : Blo 2103435 5328575 := bstep (se 1 (by rfl) ⟨3996431, by rfl⟩ : syracuseStep 5328575 = 7992863) B7992863
theorem B3552383 : Blo 2103435 3552383 := bstep (se 1 (by rfl) ⟨2664287, by rfl⟩ : syracuseStep 3552383 = 5328575) B5328575
theorem B2368255 : Blo 2103435 2368255 := bstep (se 1 (by rfl) ⟨1776191, by rfl⟩ : syracuseStep 2368255 = 3552383) B3552383
theorem B3157673 : Blo 2103435 3157673 := bstep (se 2 (by rfl) ⟨1184127, by rfl⟩ : syracuseStep 3157673 = 2368255) B2368255
theorem B2105115 : Blo 2103435 2105115 := bstep (se 1 (by rfl) ⟨1578836, by rfl⟩ : syracuseStep 2105115 = 3157673) B3157673
theorem B2247997 : Blo 2103435 2247997 := bbase (se 3 (by rfl) ⟨421499, by rfl⟩ : syracuseStep 2247997 = 842999) (by norm_num)
theorem B2997329 : Blo 2103435 2997329 := bstep (se 2 (by rfl) ⟨1123998, by rfl⟩ : syracuseStep 2997329 = 2247997) B2247997
theorem B7992877 : Blo 2103435 7992877 := bstep (se 3 (by rfl) ⟨1498664, by rfl⟩ : syracuseStep 7992877 = 2997329) B2997329
theorem B10657169 : Blo 2103435 10657169 := bstep (se 2 (by rfl) ⟨3996438, by rfl⟩ : syracuseStep 10657169 = 7992877) B7992877
theorem B7104779 : Blo 2103435 7104779 := bstep (se 1 (by rfl) ⟨5328584, by rfl⟩ : syracuseStep 7104779 = 10657169) B10657169
theorem B4736519 : Blo 2103435 4736519 := bstep (se 1 (by rfl) ⟨3552389, by rfl⟩ : syracuseStep 4736519 = 7104779) B7104779
theorem B3157679 : Blo 2103435 3157679 := bstep (se 1 (by rfl) ⟨2368259, by rfl⟩ : syracuseStep 3157679 = 4736519) B4736519
theorem B2105119 : Blo 2103435 2105119 := bstep (se 1 (by rfl) ⟨1578839, by rfl⟩ : syracuseStep 2105119 = 3157679) B3157679
theorem B3157685 : Blo 2103435 3157685 := bbase (se 5 (by rfl) ⟨148016, by rfl⟩ : syracuseStep 3157685 = 296033) (by norm_num)
theorem B2105123 : Blo 2103435 2105123 := bstep (se 1 (by rfl) ⟨1578842, by rfl⟩ : syracuseStep 2105123 = 3157685) B3157685
theorem B5328605 : Blo 2103435 5328605 := bbase (se 3 (by rfl) ⟨999113, by rfl⟩ : syracuseStep 5328605 = 1998227) (by norm_num)
theorem B3552403 : Blo 2103435 3552403 := bstep (se 1 (by rfl) ⟨2664302, by rfl⟩ : syracuseStep 3552403 = 5328605) B5328605
theorem B4736537 : Blo 2103435 4736537 := bstep (se 2 (by rfl) ⟨1776201, by rfl⟩ : syracuseStep 4736537 = 3552403) B3552403
theorem B3157691 : Blo 2103435 3157691 := bstep (se 1 (by rfl) ⟨2368268, by rfl⟩ : syracuseStep 3157691 = 4736537) B4736537
theorem B2105127 : Blo 2103435 2105127 := bstep (se 1 (by rfl) ⟨1578845, by rfl⟩ : syracuseStep 2105127 = 3157691) B3157691
theorem B2368273 : Blo 2103435 2368273 := bbase (se 2 (by rfl) ⟨888102, by rfl⟩ : syracuseStep 2368273 = 1776205) (by norm_num)
theorem B3157697 : Blo 2103435 3157697 := bstep (se 2 (by rfl) ⟨1184136, by rfl⟩ : syracuseStep 3157697 = 2368273) B2368273
theorem B2105131 : Blo 2103435 2105131 := bstep (se 1 (by rfl) ⟨1578848, by rfl⟩ : syracuseStep 2105131 = 3157697) B3157697
theorem B3996469 : Blo 2103435 3996469 := bbase (se 5 (by rfl) ⟨187334, by rfl⟩ : syracuseStep 3996469 = 374669) (by norm_num)
theorem B5328625 : Blo 2103435 5328625 := bstep (se 2 (by rfl) ⟨1998234, by rfl⟩ : syracuseStep 5328625 = 3996469) B3996469
theorem B7104833 : Blo 2103435 7104833 := bstep (se 2 (by rfl) ⟨2664312, by rfl⟩ : syracuseStep 7104833 = 5328625) B5328625
theorem B4736555 : Blo 2103435 4736555 := bstep (se 1 (by rfl) ⟨3552416, by rfl⟩ : syracuseStep 4736555 = 7104833) B7104833
theorem B3157703 : Blo 2103435 3157703 := bstep (se 1 (by rfl) ⟨2368277, by rfl⟩ : syracuseStep 3157703 = 4736555) B4736555
theorem B2105135 : Blo 2103435 2105135 := bstep (se 1 (by rfl) ⟨1578851, by rfl⟩ : syracuseStep 2105135 = 3157703) B3157703
theorem B3157709 : Blo 2103435 3157709 := bbase (se 3 (by rfl) ⟨592070, by rfl⟩ : syracuseStep 3157709 = 1184141) (by norm_num)
theorem B2105139 : Blo 2103435 2105139 := bstep (se 1 (by rfl) ⟨1578854, by rfl⟩ : syracuseStep 2105139 = 3157709) B3157709
theorem B4736573 : Blo 2103435 4736573 := bbase (se 3 (by rfl) ⟨888107, by rfl⟩ : syracuseStep 4736573 = 1776215) (by norm_num)
theorem B3157715 : Blo 2103435 3157715 := bstep (se 1 (by rfl) ⟨2368286, by rfl⟩ : syracuseStep 3157715 = 4736573) B4736573
theorem B2105143 : Blo 2103435 2105143 := bstep (se 1 (by rfl) ⟨1578857, by rfl⟩ : syracuseStep 2105143 = 3157715) B3157715
theorem B3552437 : Blo 2103435 3552437 := bbase (se 5 (by rfl) ⟨166520, by rfl⟩ : syracuseStep 3552437 = 333041) (by norm_num)
theorem B2368291 : Blo 2103435 2368291 := bstep (se 1 (by rfl) ⟨1776218, by rfl⟩ : syracuseStep 2368291 = 3552437) B3552437
theorem B3157721 : Blo 2103435 3157721 := bstep (se 2 (by rfl) ⟨1184145, by rfl⟩ : syracuseStep 3157721 = 2368291) B2368291
theorem B2105147 : Blo 2103435 2105147 := bstep (se 1 (by rfl) ⟨1578860, by rfl⟩ : syracuseStep 2105147 = 3157721) B3157721
theorem B11380661 : Blo 2103435 11380661 := bbase (se 5 (by rfl) ⟨533468, by rfl⟩ : syracuseStep 11380661 = 1066937) (by norm_num)
theorem B7587107 : Blo 2103435 7587107 := bstep (se 1 (by rfl) ⟨5690330, by rfl⟩ : syracuseStep 7587107 = 11380661) B11380661
theorem B5058071 : Blo 2103435 5058071 := bstep (se 1 (by rfl) ⟨3793553, by rfl⟩ : syracuseStep 5058071 = 7587107) B7587107
theorem B3372047 : Blo 2103435 3372047 := bstep (se 1 (by rfl) ⟨2529035, by rfl⟩ : syracuseStep 3372047 = 5058071) B5058071
theorem B2248031 : Blo 2103435 2248031 := bstep (se 1 (by rfl) ⟨1686023, by rfl⟩ : syracuseStep 2248031 = 3372047) B3372047
theorem B5994749 : Blo 2103435 5994749 := bstep (se 3 (by rfl) ⟨1124015, by rfl⟩ : syracuseStep 5994749 = 2248031) B2248031
theorem B15985997 : Blo 2103435 15985997 := bstep (se 3 (by rfl) ⟨2997374, by rfl⟩ : syracuseStep 15985997 = 5994749) B5994749
theorem B10657331 : Blo 2103435 10657331 := bstep (se 1 (by rfl) ⟨7992998, by rfl⟩ : syracuseStep 10657331 = 15985997) B15985997
theorem B7104887 : Blo 2103435 7104887 := bstep (se 1 (by rfl) ⟨5328665, by rfl⟩ : syracuseStep 7104887 = 10657331) B10657331
theorem B4736591 : Blo 2103435 4736591 := bstep (se 1 (by rfl) ⟨3552443, by rfl⟩ : syracuseStep 4736591 = 7104887) B7104887
theorem B3157727 : Blo 2103435 3157727 := bstep (se 1 (by rfl) ⟨2368295, by rfl⟩ : syracuseStep 3157727 = 4736591) B4736591
theorem B2105151 : Blo 2103435 2105151 := bstep (se 1 (by rfl) ⟨1578863, by rfl⟩ : syracuseStep 2105151 = 3157727) B3157727
theorem B3157733 : Blo 2103435 3157733 := bbase (se 4 (by rfl) ⟨296037, by rfl⟩ : syracuseStep 3157733 = 592075) (by norm_num)
theorem B2105155 : Blo 2103435 2105155 := bstep (se 1 (by rfl) ⟨1578866, by rfl⟩ : syracuseStep 2105155 = 3157733) B3157733
theorem B5994773 : Blo 2103435 5994773 := bbase (se 6 (by rfl) ⟨140502, by rfl⟩ : syracuseStep 5994773 = 281005) (by norm_num)
theorem B3996515 : Blo 2103435 3996515 := bstep (se 1 (by rfl) ⟨2997386, by rfl⟩ : syracuseStep 3996515 = 5994773) B5994773
theorem B2664343 : Blo 2103435 2664343 := bstep (se 1 (by rfl) ⟨1998257, by rfl⟩ : syracuseStep 2664343 = 3996515) B3996515
theorem B3552457 : Blo 2103435 3552457 := bstep (se 2 (by rfl) ⟨1332171, by rfl⟩ : syracuseStep 3552457 = 2664343) B2664343
theorem B4736609 : Blo 2103435 4736609 := bstep (se 2 (by rfl) ⟨1776228, by rfl⟩ : syracuseStep 4736609 = 3552457) B3552457
theorem B3157739 : Blo 2103435 3157739 := bstep (se 1 (by rfl) ⟨2368304, by rfl⟩ : syracuseStep 3157739 = 4736609) B4736609
theorem B2105159 : Blo 2103435 2105159 := bstep (se 1 (by rfl) ⟨1578869, by rfl⟩ : syracuseStep 2105159 = 3157739) B3157739
theorem B2368309 : Blo 2103435 2368309 := bbase (se 5 (by rfl) ⟨111014, by rfl⟩ : syracuseStep 2368309 = 222029) (by norm_num)
theorem B3157745 : Blo 2103435 3157745 := bstep (se 2 (by rfl) ⟨1184154, by rfl⟩ : syracuseStep 3157745 = 2368309) B2368309
theorem B2105163 : Blo 2103435 2105163 := bstep (se 1 (by rfl) ⟨1578872, by rfl⟩ : syracuseStep 2105163 = 3157745) B3157745
theorem B2664353 : Blo 2103435 2664353 := bbase (se 2 (by rfl) ⟨999132, by rfl⟩ : syracuseStep 2664353 = 1998265) (by norm_num)
theorem B7104941 : Blo 2103435 7104941 := bstep (se 3 (by rfl) ⟨1332176, by rfl⟩ : syracuseStep 7104941 = 2664353) B2664353
theorem B4736627 : Blo 2103435 4736627 := bstep (se 1 (by rfl) ⟨3552470, by rfl⟩ : syracuseStep 4736627 = 7104941) B7104941
theorem B3157751 : Blo 2103435 3157751 := bstep (se 1 (by rfl) ⟨2368313, by rfl⟩ : syracuseStep 3157751 = 4736627) B4736627
theorem B2105167 : Blo 2103435 2105167 := bstep (se 1 (by rfl) ⟨1578875, by rfl⟩ : syracuseStep 2105167 = 3157751) B3157751
theorem B3157757 : Blo 2103435 3157757 := bbase (se 3 (by rfl) ⟨592079, by rfl⟩ : syracuseStep 3157757 = 1184159) (by norm_num)
theorem B2105171 : Blo 2103435 2105171 := bstep (se 1 (by rfl) ⟨1578878, by rfl⟩ : syracuseStep 2105171 = 3157757) B3157757
theorem B4736645 : Blo 2103435 4736645 := bbase (se 4 (by rfl) ⟨444060, by rfl⟩ : syracuseStep 4736645 = 888121) (by norm_num)
theorem B3157763 : Blo 2103435 3157763 := bstep (se 1 (by rfl) ⟨2368322, by rfl⟩ : syracuseStep 3157763 = 4736645) B4736645
theorem B2105175 : Blo 2103435 2105175 := bstep (se 1 (by rfl) ⟨1578881, by rfl⟩ : syracuseStep 2105175 = 3157763) B3157763
theorem B2700721 : Blo 2103435 2700721 := bbase (se 2 (by rfl) ⟨1012770, by rfl⟩ : syracuseStep 2700721 = 2025541) (by norm_num)
theorem B14403845 : Blo 2103435 14403845 := bstep (se 4 (by rfl) ⟨1350360, by rfl⟩ : syracuseStep 14403845 = 2700721) B2700721
theorem B9602563 : Blo 2103435 9602563 := bstep (se 1 (by rfl) ⟨7201922, by rfl⟩ : syracuseStep 9602563 = 14403845) B14403845
theorem B12803417 : Blo 2103435 12803417 := bstep (se 2 (by rfl) ⟨4801281, by rfl⟩ : syracuseStep 12803417 = 9602563) B9602563
theorem B8535611 : Blo 2103435 8535611 := bstep (se 1 (by rfl) ⟨6401708, by rfl⟩ : syracuseStep 8535611 = 12803417) B12803417
theorem B5690407 : Blo 2103435 5690407 := bstep (se 1 (by rfl) ⟨4267805, by rfl⟩ : syracuseStep 5690407 = 8535611) B8535611
theorem B7587209 : Blo 2103435 7587209 := bstep (se 2 (by rfl) ⟨2845203, by rfl⟩ : syracuseStep 7587209 = 5690407) B5690407
theorem B5058139 : Blo 2103435 5058139 := bstep (se 1 (by rfl) ⟨3793604, by rfl⟩ : syracuseStep 5058139 = 7587209) B7587209
theorem B6744185 : Blo 2103435 6744185 := bstep (se 2 (by rfl) ⟨2529069, by rfl⟩ : syracuseStep 6744185 = 5058139) B5058139
theorem B4496123 : Blo 2103435 4496123 := bstep (se 1 (by rfl) ⟨3372092, by rfl⟩ : syracuseStep 4496123 = 6744185) B6744185
theorem B2997415 : Blo 2103435 2997415 := bstep (se 1 (by rfl) ⟨2248061, by rfl⟩ : syracuseStep 2997415 = 4496123) B4496123
theorem B3996553 : Blo 2103435 3996553 := bstep (se 2 (by rfl) ⟨1498707, by rfl⟩ : syracuseStep 3996553 = 2997415) B2997415
theorem B5328737 : Blo 2103435 5328737 := bstep (se 2 (by rfl) ⟨1998276, by rfl⟩ : syracuseStep 5328737 = 3996553) B3996553
theorem B3552491 : Blo 2103435 3552491 := bstep (se 1 (by rfl) ⟨2664368, by rfl⟩ : syracuseStep 3552491 = 5328737) B5328737
theorem B2368327 : Blo 2103435 2368327 := bstep (se 1 (by rfl) ⟨1776245, by rfl⟩ : syracuseStep 2368327 = 3552491) B3552491
theorem B3157769 : Blo 2103435 3157769 := bstep (se 2 (by rfl) ⟨1184163, by rfl⟩ : syracuseStep 3157769 = 2368327) B2368327
theorem B2105179 : Blo 2103435 2105179 := bstep (se 1 (by rfl) ⟨1578884, by rfl⟩ : syracuseStep 2105179 = 3157769) B3157769
theorem B10657493 : Blo 2103435 10657493 := bbase (se 7 (by rfl) ⟨124892, by rfl⟩ : syracuseStep 10657493 = 249785) (by norm_num)
theorem B7104995 : Blo 2103435 7104995 := bstep (se 1 (by rfl) ⟨5328746, by rfl⟩ : syracuseStep 7104995 = 10657493) B10657493
theorem B4736663 : Blo 2103435 4736663 := bstep (se 1 (by rfl) ⟨3552497, by rfl⟩ : syracuseStep 4736663 = 7104995) B7104995
theorem B3157775 : Blo 2103435 3157775 := bstep (se 1 (by rfl) ⟨2368331, by rfl⟩ : syracuseStep 3157775 = 4736663) B4736663
theorem B2105183 : Blo 2103435 2105183 := bstep (se 1 (by rfl) ⟨1578887, by rfl⟩ : syracuseStep 2105183 = 3157775) B3157775
theorem B3157781 : Blo 2103435 3157781 := bbase (se 6 (by rfl) ⟨74010, by rfl⟩ : syracuseStep 3157781 = 148021) (by norm_num)
theorem B2105187 : Blo 2103435 2105187 := bstep (se 1 (by rfl) ⟨1578890, by rfl⟩ : syracuseStep 2105187 = 3157781) B3157781
theorem B22761749 : Blo 2103435 22761749 := bbase (se 6 (by rfl) ⟨533478, by rfl⟩ : syracuseStep 22761749 = 1066957) (by norm_num)
theorem B60697997 : Blo 2103435 60697997 := bstep (se 3 (by rfl) ⟨11380874, by rfl⟩ : syracuseStep 60697997 = 22761749) B22761749
theorem B40465331 : Blo 2103435 40465331 := bstep (se 1 (by rfl) ⟨30348998, by rfl⟩ : syracuseStep 40465331 = 60697997) B60697997
theorem B26976887 : Blo 2103435 26976887 := bstep (se 1 (by rfl) ⟨20232665, by rfl⟩ : syracuseStep 26976887 = 40465331) B40465331
theorem B17984591 : Blo 2103435 17984591 := bstep (se 1 (by rfl) ⟨13488443, by rfl⟩ : syracuseStep 17984591 = 26976887) B26976887
theorem B11989727 : Blo 2103435 11989727 := bstep (se 1 (by rfl) ⟨8992295, by rfl⟩ : syracuseStep 11989727 = 17984591) B17984591
theorem B7993151 : Blo 2103435 7993151 := bstep (se 1 (by rfl) ⟨5994863, by rfl⟩ : syracuseStep 7993151 = 11989727) B11989727
theorem B5328767 : Blo 2103435 5328767 := bstep (se 1 (by rfl) ⟨3996575, by rfl⟩ : syracuseStep 5328767 = 7993151) B7993151
theorem B3552511 : Blo 2103435 3552511 := bstep (se 1 (by rfl) ⟨2664383, by rfl⟩ : syracuseStep 3552511 = 5328767) B5328767
theorem B4736681 : Blo 2103435 4736681 := bstep (se 2 (by rfl) ⟨1776255, by rfl⟩ : syracuseStep 4736681 = 3552511) B3552511
theorem B3157787 : Blo 2103435 3157787 := bstep (se 1 (by rfl) ⟨2368340, by rfl⟩ : syracuseStep 3157787 = 4736681) B4736681
theorem B2105191 : Blo 2103435 2105191 := bstep (se 1 (by rfl) ⟨1578893, by rfl⟩ : syracuseStep 2105191 = 3157787) B3157787
theorem B2368345 : Blo 2103435 2368345 := bbase (se 2 (by rfl) ⟨888129, by rfl⟩ : syracuseStep 2368345 = 1776259) (by norm_num)
theorem B3157793 : Blo 2103435 3157793 := bstep (se 2 (by rfl) ⟨1184172, by rfl⟩ : syracuseStep 3157793 = 2368345) B2368345
theorem B2105195 : Blo 2103435 2105195 := bstep (se 1 (by rfl) ⟨1578896, by rfl⟩ : syracuseStep 2105195 = 3157793) B3157793
theorem B4496165 : Blo 2103435 4496165 := bbase (se 4 (by rfl) ⟨421515, by rfl⟩ : syracuseStep 4496165 = 843031) (by norm_num)
theorem B2997443 : Blo 2103435 2997443 := bstep (se 1 (by rfl) ⟨2248082, by rfl⟩ : syracuseStep 2997443 = 4496165) B4496165
theorem B7993181 : Blo 2103435 7993181 := bstep (se 3 (by rfl) ⟨1498721, by rfl⟩ : syracuseStep 7993181 = 2997443) B2997443
theorem B5328787 : Blo 2103435 5328787 := bstep (se 1 (by rfl) ⟨3996590, by rfl⟩ : syracuseStep 5328787 = 7993181) B7993181
theorem B7105049 : Blo 2103435 7105049 := bstep (se 2 (by rfl) ⟨2664393, by rfl⟩ : syracuseStep 7105049 = 5328787) B5328787
theorem B4736699 : Blo 2103435 4736699 := bstep (se 1 (by rfl) ⟨3552524, by rfl⟩ : syracuseStep 4736699 = 7105049) B7105049
theorem B3157799 : Blo 2103435 3157799 := bstep (se 1 (by rfl) ⟨2368349, by rfl⟩ : syracuseStep 3157799 = 4736699) B4736699
theorem B2105199 : Blo 2103435 2105199 := bstep (se 1 (by rfl) ⟨1578899, by rfl⟩ : syracuseStep 2105199 = 3157799) B3157799
theorem B3157805 : Blo 2103435 3157805 := bbase (se 3 (by rfl) ⟨592088, by rfl⟩ : syracuseStep 3157805 = 1184177) (by norm_num)
theorem B2105203 : Blo 2103435 2105203 := bstep (se 1 (by rfl) ⟨1578902, by rfl⟩ : syracuseStep 2105203 = 3157805) B3157805
theorem B4736717 : Blo 2103435 4736717 := bbase (se 3 (by rfl) ⟨888134, by rfl⟩ : syracuseStep 4736717 = 1776269) (by norm_num)
theorem B3157811 : Blo 2103435 3157811 := bstep (se 1 (by rfl) ⟨2368358, by rfl⟩ : syracuseStep 3157811 = 4736717) B4736717
theorem B2105207 : Blo 2103435 2105207 := bstep (se 1 (by rfl) ⟨1578905, by rfl⟩ : syracuseStep 2105207 = 3157811) B3157811
theorem B2664409 : Blo 2103435 2664409 := bbase (se 2 (by rfl) ⟨999153, by rfl⟩ : syracuseStep 2664409 = 1998307) (by norm_num)
theorem B3552545 : Blo 2103435 3552545 := bstep (se 2 (by rfl) ⟨1332204, by rfl⟩ : syracuseStep 3552545 = 2664409) B2664409
theorem B2368363 : Blo 2103435 2368363 := bstep (se 1 (by rfl) ⟨1776272, by rfl⟩ : syracuseStep 2368363 = 3552545) B3552545
theorem B3157817 : Blo 2103435 3157817 := bstep (se 2 (by rfl) ⟨1184181, by rfl⟩ : syracuseStep 3157817 = 2368363) B2368363
theorem B2105211 : Blo 2103435 2105211 := bstep (se 1 (by rfl) ⟨1578908, by rfl⟩ : syracuseStep 2105211 = 3157817) B3157817
theorem B3372149 : Blo 2103435 3372149 := bbase (se 5 (by rfl) ⟨158069, by rfl⟩ : syracuseStep 3372149 = 316139) (by norm_num)
theorem B8992397 : Blo 2103435 8992397 := bstep (se 3 (by rfl) ⟨1686074, by rfl⟩ : syracuseStep 8992397 = 3372149) B3372149
theorem B23979725 : Blo 2103435 23979725 := bstep (se 3 (by rfl) ⟨4496198, by rfl⟩ : syracuseStep 23979725 = 8992397) B8992397
theorem B15986483 : Blo 2103435 15986483 := bstep (se 1 (by rfl) ⟨11989862, by rfl⟩ : syracuseStep 15986483 = 23979725) B23979725
theorem B10657655 : Blo 2103435 10657655 := bstep (se 1 (by rfl) ⟨7993241, by rfl⟩ : syracuseStep 10657655 = 15986483) B15986483
theorem B7105103 : Blo 2103435 7105103 := bstep (se 1 (by rfl) ⟨5328827, by rfl⟩ : syracuseStep 7105103 = 10657655) B10657655
theorem B4736735 : Blo 2103435 4736735 := bstep (se 1 (by rfl) ⟨3552551, by rfl⟩ : syracuseStep 4736735 = 7105103) B7105103
theorem B3157823 : Blo 2103435 3157823 := bstep (se 1 (by rfl) ⟨2368367, by rfl⟩ : syracuseStep 3157823 = 4736735) B4736735
theorem B2105215 : Blo 2103435 2105215 := bstep (se 1 (by rfl) ⟨1578911, by rfl⟩ : syracuseStep 2105215 = 3157823) B3157823
theorem B3157829 : Blo 2103435 3157829 := bbase (se 4 (by rfl) ⟨296046, by rfl⟩ : syracuseStep 3157829 = 592093) (by norm_num)
theorem B2105219 : Blo 2103435 2105219 := bstep (se 1 (by rfl) ⟨1578914, by rfl⟩ : syracuseStep 2105219 = 3157829) B3157829
theorem B3552565 : Blo 2103435 3552565 := bbase (se 5 (by rfl) ⟨166526, by rfl⟩ : syracuseStep 3552565 = 333053) (by norm_num)
theorem B4736753 : Blo 2103435 4736753 := bstep (se 2 (by rfl) ⟨1776282, by rfl⟩ : syracuseStep 4736753 = 3552565) B3552565
theorem B3157835 : Blo 2103435 3157835 := bstep (se 1 (by rfl) ⟨2368376, by rfl⟩ : syracuseStep 3157835 = 4736753) B4736753
theorem B2105223 : Blo 2103435 2105223 := bstep (se 1 (by rfl) ⟨1578917, by rfl⟩ : syracuseStep 2105223 = 3157835) B3157835
theorem B2368381 : Blo 2103435 2368381 := bbase (se 3 (by rfl) ⟨444071, by rfl⟩ : syracuseStep 2368381 = 888143) (by norm_num)
theorem B3157841 : Blo 2103435 3157841 := bstep (se 2 (by rfl) ⟨1184190, by rfl⟩ : syracuseStep 3157841 = 2368381) B2368381
theorem B2105227 : Blo 2103435 2105227 := bstep (se 1 (by rfl) ⟨1578920, by rfl⟩ : syracuseStep 2105227 = 3157841) B3157841
theorem B7105157 : Blo 2103435 7105157 := bbase (se 4 (by rfl) ⟨666108, by rfl⟩ : syracuseStep 7105157 = 1332217) (by norm_num)
theorem B4736771 : Blo 2103435 4736771 := bstep (se 1 (by rfl) ⟨3552578, by rfl⟩ : syracuseStep 4736771 = 7105157) B7105157
theorem B3157847 : Blo 2103435 3157847 := bstep (se 1 (by rfl) ⟨2368385, by rfl⟩ : syracuseStep 3157847 = 4736771) B4736771
theorem B2105231 : Blo 2103435 2105231 := bstep (se 1 (by rfl) ⟨1578923, by rfl⟩ : syracuseStep 2105231 = 3157847) B3157847
theorem B3157853 : Blo 2103435 3157853 := bbase (se 3 (by rfl) ⟨592097, by rfl⟩ : syracuseStep 3157853 = 1184195) (by norm_num)
theorem B2105235 : Blo 2103435 2105235 := bstep (se 1 (by rfl) ⟨1578926, by rfl⟩ : syracuseStep 2105235 = 3157853) B3157853
theorem B4736789 : Blo 2103435 4736789 := bbase (se 6 (by rfl) ⟨111018, by rfl⟩ : syracuseStep 4736789 = 222037) (by norm_num)
theorem B3157859 : Blo 2103435 3157859 := bstep (se 1 (by rfl) ⟨2368394, by rfl⟩ : syracuseStep 3157859 = 4736789) B4736789
theorem B2105239 : Blo 2103435 2105239 := bstep (se 1 (by rfl) ⟨1578929, by rfl⟩ : syracuseStep 2105239 = 3157859) B3157859
theorem B7993349 : Blo 2103435 7993349 := bbase (se 4 (by rfl) ⟨749376, by rfl⟩ : syracuseStep 7993349 = 1498753) (by norm_num)
theorem B5328899 : Blo 2103435 5328899 := bstep (se 1 (by rfl) ⟨3996674, by rfl⟩ : syracuseStep 5328899 = 7993349) B7993349
theorem B3552599 : Blo 2103435 3552599 := bstep (se 1 (by rfl) ⟨2664449, by rfl⟩ : syracuseStep 3552599 = 5328899) B5328899
theorem B2368399 : Blo 2103435 2368399 := bstep (se 1 (by rfl) ⟨1776299, by rfl⟩ : syracuseStep 2368399 = 3552599) B3552599
theorem B3157865 : Blo 2103435 3157865 := bstep (se 2 (by rfl) ⟨1184199, by rfl⟩ : syracuseStep 3157865 = 2368399) B2368399
theorem B2105243 : Blo 2103435 2105243 := bstep (se 1 (by rfl) ⟨1578932, by rfl⟩ : syracuseStep 2105243 = 3157865) B3157865
theorem B5058301 : Blo 2103435 5058301 := bbase (se 3 (by rfl) ⟨948431, by rfl⟩ : syracuseStep 5058301 = 1896863) (by norm_num)
theorem B6744401 : Blo 2103435 6744401 := bstep (se 2 (by rfl) ⟨2529150, by rfl⟩ : syracuseStep 6744401 = 5058301) B5058301
theorem B4496267 : Blo 2103435 4496267 := bstep (se 1 (by rfl) ⟨3372200, by rfl⟩ : syracuseStep 4496267 = 6744401) B6744401
theorem B11990045 : Blo 2103435 11990045 := bstep (se 3 (by rfl) ⟨2248133, by rfl⟩ : syracuseStep 11990045 = 4496267) B4496267
theorem B7993363 : Blo 2103435 7993363 := bstep (se 1 (by rfl) ⟨5995022, by rfl⟩ : syracuseStep 7993363 = 11990045) B11990045
theorem B10657817 : Blo 2103435 10657817 := bstep (se 2 (by rfl) ⟨3996681, by rfl⟩ : syracuseStep 10657817 = 7993363) B7993363
theorem B7105211 : Blo 2103435 7105211 := bstep (se 1 (by rfl) ⟨5328908, by rfl⟩ : syracuseStep 7105211 = 10657817) B10657817
theorem B4736807 : Blo 2103435 4736807 := bstep (se 1 (by rfl) ⟨3552605, by rfl⟩ : syracuseStep 4736807 = 7105211) B7105211
theorem B3157871 : Blo 2103435 3157871 := bstep (se 1 (by rfl) ⟨2368403, by rfl⟩ : syracuseStep 3157871 = 4736807) B4736807
theorem B2105247 : Blo 2103435 2105247 := bstep (se 1 (by rfl) ⟨1578935, by rfl⟩ : syracuseStep 2105247 = 3157871) B3157871
theorem B3157877 : Blo 2103435 3157877 := bbase (se 5 (by rfl) ⟨148025, by rfl⟩ : syracuseStep 3157877 = 296051) (by norm_num)
theorem B2105251 : Blo 2103435 2105251 := bstep (se 1 (by rfl) ⟨1578938, by rfl⟩ : syracuseStep 2105251 = 3157877) B3157877
theorem B4496285 : Blo 2103435 4496285 := bbase (se 3 (by rfl) ⟨843053, by rfl⟩ : syracuseStep 4496285 = 1686107) (by norm_num)
theorem B2997523 : Blo 2103435 2997523 := bstep (se 1 (by rfl) ⟨2248142, by rfl⟩ : syracuseStep 2997523 = 4496285) B4496285
theorem B3996697 : Blo 2103435 3996697 := bstep (se 2 (by rfl) ⟨1498761, by rfl⟩ : syracuseStep 3996697 = 2997523) B2997523
theorem B5328929 : Blo 2103435 5328929 := bstep (se 2 (by rfl) ⟨1998348, by rfl⟩ : syracuseStep 5328929 = 3996697) B3996697
theorem B3552619 : Blo 2103435 3552619 := bstep (se 1 (by rfl) ⟨2664464, by rfl⟩ : syracuseStep 3552619 = 5328929) B5328929
theorem B4736825 : Blo 2103435 4736825 := bstep (se 2 (by rfl) ⟨1776309, by rfl⟩ : syracuseStep 4736825 = 3552619) B3552619
theorem B3157883 : Blo 2103435 3157883 := bstep (se 1 (by rfl) ⟨2368412, by rfl⟩ : syracuseStep 3157883 = 4736825) B4736825
theorem B2105255 : Blo 2103435 2105255 := bstep (se 1 (by rfl) ⟨1578941, by rfl⟩ : syracuseStep 2105255 = 3157883) B3157883
theorem B2368417 : Blo 2103435 2368417 := bbase (se 2 (by rfl) ⟨888156, by rfl⟩ : syracuseStep 2368417 = 1776313) (by norm_num)
theorem B3157889 : Blo 2103435 3157889 := bstep (se 2 (by rfl) ⟨1184208, by rfl⟩ : syracuseStep 3157889 = 2368417) B2368417
theorem B2105259 : Blo 2103435 2105259 := bstep (se 1 (by rfl) ⟨1578944, by rfl⟩ : syracuseStep 2105259 = 3157889) B3157889
theorem B5328949 : Blo 2103435 5328949 := bbase (se 5 (by rfl) ⟨249794, by rfl⟩ : syracuseStep 5328949 = 499589) (by norm_num)
theorem B7105265 : Blo 2103435 7105265 := bstep (se 2 (by rfl) ⟨2664474, by rfl⟩ : syracuseStep 7105265 = 5328949) B5328949
theorem B4736843 : Blo 2103435 4736843 := bstep (se 1 (by rfl) ⟨3552632, by rfl⟩ : syracuseStep 4736843 = 7105265) B7105265
theorem B3157895 : Blo 2103435 3157895 := bstep (se 1 (by rfl) ⟨2368421, by rfl⟩ : syracuseStep 3157895 = 4736843) B4736843
theorem B2105263 : Blo 2103435 2105263 := bstep (se 1 (by rfl) ⟨1578947, by rfl⟩ : syracuseStep 2105263 = 3157895) B3157895
theorem B3157901 : Blo 2103435 3157901 := bbase (se 3 (by rfl) ⟨592106, by rfl⟩ : syracuseStep 3157901 = 1184213) (by norm_num)
theorem B2105267 : Blo 2103435 2105267 := bstep (se 1 (by rfl) ⟨1578950, by rfl⟩ : syracuseStep 2105267 = 3157901) B3157901
theorem B4736861 : Blo 2103435 4736861 := bbase (se 3 (by rfl) ⟨888161, by rfl⟩ : syracuseStep 4736861 = 1776323) (by norm_num)
theorem B3157907 : Blo 2103435 3157907 := bstep (se 1 (by rfl) ⟨2368430, by rfl⟩ : syracuseStep 3157907 = 4736861) B4736861
theorem B2105271 : Blo 2103435 2105271 := bstep (se 1 (by rfl) ⟨1578953, by rfl⟩ : syracuseStep 2105271 = 3157907) B3157907
theorem B3552653 : Blo 2103435 3552653 := bbase (se 3 (by rfl) ⟨666122, by rfl⟩ : syracuseStep 3552653 = 1332245) (by norm_num)
theorem B2368435 : Blo 2103435 2368435 := bstep (se 1 (by rfl) ⟨1776326, by rfl⟩ : syracuseStep 2368435 = 3552653) B3552653
theorem B3157913 : Blo 2103435 3157913 := bstep (se 2 (by rfl) ⟨1184217, by rfl⟩ : syracuseStep 3157913 = 2368435) B2368435
theorem B2105275 : Blo 2103435 2105275 := bstep (se 1 (by rfl) ⟨1578956, by rfl⟩ : syracuseStep 2105275 = 3157913) B3157913
theorem B3201005 : Blo 2103435 3201005 := bbase (se 3 (by rfl) ⟨600188, by rfl⟩ : syracuseStep 3201005 = 1200377) (by norm_num)
theorem B8536013 : Blo 2103435 8536013 := bstep (se 3 (by rfl) ⟨1600502, by rfl⟩ : syracuseStep 8536013 = 3201005) B3201005
theorem B5690675 : Blo 2103435 5690675 := bstep (se 1 (by rfl) ⟨4268006, by rfl⟩ : syracuseStep 5690675 = 8536013) B8536013
theorem B15175133 : Blo 2103435 15175133 := bstep (se 3 (by rfl) ⟨2845337, by rfl⟩ : syracuseStep 15175133 = 5690675) B5690675
theorem B10116755 : Blo 2103435 10116755 := bstep (se 1 (by rfl) ⟨7587566, by rfl⟩ : syracuseStep 10116755 = 15175133) B15175133
theorem B6744503 : Blo 2103435 6744503 := bstep (se 1 (by rfl) ⟨5058377, by rfl⟩ : syracuseStep 6744503 = 10116755) B10116755
theorem B17985341 : Blo 2103435 17985341 := bstep (se 3 (by rfl) ⟨3372251, by rfl⟩ : syracuseStep 17985341 = 6744503) B6744503
theorem B11990227 : Blo 2103435 11990227 := bstep (se 1 (by rfl) ⟨8992670, by rfl⟩ : syracuseStep 11990227 = 17985341) B17985341
theorem B15986969 : Blo 2103435 15986969 := bstep (se 2 (by rfl) ⟨5995113, by rfl⟩ : syracuseStep 15986969 = 11990227) B11990227
theorem B10657979 : Blo 2103435 10657979 := bstep (se 1 (by rfl) ⟨7993484, by rfl⟩ : syracuseStep 10657979 = 15986969) B15986969
theorem B7105319 : Blo 2103435 7105319 := bstep (se 1 (by rfl) ⟨5328989, by rfl⟩ : syracuseStep 7105319 = 10657979) B10657979
theorem B4736879 : Blo 2103435 4736879 := bstep (se 1 (by rfl) ⟨3552659, by rfl⟩ : syracuseStep 4736879 = 7105319) B7105319
theorem B3157919 : Blo 2103435 3157919 := bstep (se 1 (by rfl) ⟨2368439, by rfl⟩ : syracuseStep 3157919 = 4736879) B4736879
theorem B2105279 : Blo 2103435 2105279 := bstep (se 1 (by rfl) ⟨1578959, by rfl⟩ : syracuseStep 2105279 = 3157919) B3157919
theorem B3157925 : Blo 2103435 3157925 := bbase (se 4 (by rfl) ⟨296055, by rfl⟩ : syracuseStep 3157925 = 592111) (by norm_num)
theorem B2105283 : Blo 2103435 2105283 := bstep (se 1 (by rfl) ⟨1578962, by rfl⟩ : syracuseStep 2105283 = 3157925) B3157925
theorem B2664505 : Blo 2103435 2664505 := bbase (se 2 (by rfl) ⟨999189, by rfl⟩ : syracuseStep 2664505 = 1998379) (by norm_num)
theorem B3552673 : Blo 2103435 3552673 := bstep (se 2 (by rfl) ⟨1332252, by rfl⟩ : syracuseStep 3552673 = 2664505) B2664505
theorem B4736897 : Blo 2103435 4736897 := bstep (se 2 (by rfl) ⟨1776336, by rfl⟩ : syracuseStep 4736897 = 3552673) B3552673
theorem B3157931 : Blo 2103435 3157931 := bstep (se 1 (by rfl) ⟨2368448, by rfl⟩ : syracuseStep 3157931 = 4736897) B4736897
theorem B2105287 : Blo 2103435 2105287 := bstep (se 1 (by rfl) ⟨1578965, by rfl⟩ : syracuseStep 2105287 = 3157931) B3157931
theorem B2368453 : Blo 2103435 2368453 := bbase (se 4 (by rfl) ⟨222042, by rfl⟩ : syracuseStep 2368453 = 444085) (by norm_num)
theorem B3157937 : Blo 2103435 3157937 := bstep (se 2 (by rfl) ⟨1184226, by rfl⟩ : syracuseStep 3157937 = 2368453) B2368453
theorem B2105291 : Blo 2103435 2105291 := bstep (se 1 (by rfl) ⟨1578968, by rfl⟩ : syracuseStep 2105291 = 3157937) B3157937
theorem B3996773 : Blo 2103435 3996773 := bbase (se 4 (by rfl) ⟨374697, by rfl⟩ : syracuseStep 3996773 = 749395) (by norm_num)
theorem B2664515 : Blo 2103435 2664515 := bstep (se 1 (by rfl) ⟨1998386, by rfl⟩ : syracuseStep 2664515 = 3996773) B3996773
theorem B7105373 : Blo 2103435 7105373 := bstep (se 3 (by rfl) ⟨1332257, by rfl⟩ : syracuseStep 7105373 = 2664515) B2664515
theorem B4736915 : Blo 2103435 4736915 := bstep (se 1 (by rfl) ⟨3552686, by rfl⟩ : syracuseStep 4736915 = 7105373) B7105373
theorem B3157943 : Blo 2103435 3157943 := bstep (se 1 (by rfl) ⟨2368457, by rfl⟩ : syracuseStep 3157943 = 4736915) B4736915
theorem B2105295 : Blo 2103435 2105295 := bstep (se 1 (by rfl) ⟨1578971, by rfl⟩ : syracuseStep 2105295 = 3157943) B3157943
theorem B3157949 : Blo 2103435 3157949 := bbase (se 3 (by rfl) ⟨592115, by rfl⟩ : syracuseStep 3157949 = 1184231) (by norm_num)
theorem B2105299 : Blo 2103435 2105299 := bstep (se 1 (by rfl) ⟨1578974, by rfl⟩ : syracuseStep 2105299 = 3157949) B3157949
theorem B4736933 : Blo 2103435 4736933 := bbase (se 4 (by rfl) ⟨444087, by rfl⟩ : syracuseStep 4736933 = 888175) (by norm_num)
theorem B3157955 : Blo 2103435 3157955 := bstep (se 1 (by rfl) ⟨2368466, by rfl⟩ : syracuseStep 3157955 = 4736933) B4736933
theorem B2105303 : Blo 2103435 2105303 := bstep (se 1 (by rfl) ⟨1578977, by rfl⟩ : syracuseStep 2105303 = 3157955) B3157955
theorem B5329061 : Blo 2103435 5329061 := bbase (se 4 (by rfl) ⟨499599, by rfl⟩ : syracuseStep 5329061 = 999199) (by norm_num)
theorem B3552707 : Blo 2103435 3552707 := bstep (se 1 (by rfl) ⟨2664530, by rfl⟩ : syracuseStep 3552707 = 5329061) B5329061
theorem B2368471 : Blo 2103435 2368471 := bstep (se 1 (by rfl) ⟨1776353, by rfl⟩ : syracuseStep 2368471 = 3552707) B3552707
theorem B3157961 : Blo 2103435 3157961 := bstep (se 2 (by rfl) ⟨1184235, by rfl⟩ : syracuseStep 3157961 = 2368471) B2368471
theorem B2105307 : Blo 2103435 2105307 := bstep (se 1 (by rfl) ⟨1578980, by rfl⟩ : syracuseStep 2105307 = 3157961) B3157961
theorem B5995205 : Blo 2103435 5995205 := bbase (se 4 (by rfl) ⟨562050, by rfl⟩ : syracuseStep 5995205 = 1124101) (by norm_num)
theorem B3996803 : Blo 2103435 3996803 := bstep (se 1 (by rfl) ⟨2997602, by rfl⟩ : syracuseStep 3996803 = 5995205) B5995205
theorem B10658141 : Blo 2103435 10658141 := bstep (se 3 (by rfl) ⟨1998401, by rfl⟩ : syracuseStep 10658141 = 3996803) B3996803
theorem B7105427 : Blo 2103435 7105427 := bstep (se 1 (by rfl) ⟨5329070, by rfl⟩ : syracuseStep 7105427 = 10658141) B10658141
theorem B4736951 : Blo 2103435 4736951 := bstep (se 1 (by rfl) ⟨3552713, by rfl⟩ : syracuseStep 4736951 = 7105427) B7105427
theorem B3157967 : Blo 2103435 3157967 := bstep (se 1 (by rfl) ⟨2368475, by rfl⟩ : syracuseStep 3157967 = 4736951) B4736951
theorem B2105311 : Blo 2103435 2105311 := bstep (se 1 (by rfl) ⟨1578983, by rfl⟩ : syracuseStep 2105311 = 3157967) B3157967
theorem B3157973 : Blo 2103435 3157973 := bbase (se 7 (by rfl) ⟨37007, by rfl⟩ : syracuseStep 3157973 = 74015) (by norm_num)
theorem B2105315 : Blo 2103435 2105315 := bstep (se 1 (by rfl) ⟨1578986, by rfl⟩ : syracuseStep 2105315 = 3157973) B3157973
theorem B7993637 : Blo 2103435 7993637 := bbase (se 4 (by rfl) ⟨749403, by rfl⟩ : syracuseStep 7993637 = 1498807) (by norm_num)
theorem B5329091 : Blo 2103435 5329091 := bstep (se 1 (by rfl) ⟨3996818, by rfl⟩ : syracuseStep 5329091 = 7993637) B7993637
theorem B3552727 : Blo 2103435 3552727 := bstep (se 1 (by rfl) ⟨2664545, by rfl⟩ : syracuseStep 3552727 = 5329091) B5329091
theorem B4736969 : Blo 2103435 4736969 := bstep (se 2 (by rfl) ⟨1776363, by rfl⟩ : syracuseStep 4736969 = 3552727) B3552727
theorem B3157979 : Blo 2103435 3157979 := bstep (se 1 (by rfl) ⟨2368484, by rfl⟩ : syracuseStep 3157979 = 4736969) B4736969
theorem B2105319 : Blo 2103435 2105319 := bstep (se 1 (by rfl) ⟨1578989, by rfl⟩ : syracuseStep 2105319 = 3157979) B3157979
theorem B2368489 : Blo 2103435 2368489 := bbase (se 2 (by rfl) ⟨888183, by rfl⟩ : syracuseStep 2368489 = 1776367) (by norm_num)
theorem B3157985 : Blo 2103435 3157985 := bstep (se 2 (by rfl) ⟨1184244, by rfl⟩ : syracuseStep 3157985 = 2368489) B2368489
theorem B2105323 : Blo 2103435 2105323 := bstep (se 1 (by rfl) ⟨1578992, by rfl⟩ : syracuseStep 2105323 = 3157985) B3157985
theorem B7691269 : Blo 2103435 7691269 := bbase (se 4 (by rfl) ⟨721056, by rfl⟩ : syracuseStep 7691269 = 1442113) (by norm_num)
theorem B10255025 : Blo 2103435 10255025 := bstep (se 2 (by rfl) ⟨3845634, by rfl⟩ : syracuseStep 10255025 = 7691269) B7691269
theorem B6836683 : Blo 2103435 6836683 := bstep (se 1 (by rfl) ⟨5127512, by rfl⟩ : syracuseStep 6836683 = 10255025) B10255025
theorem B9115577 : Blo 2103435 9115577 := bstep (se 2 (by rfl) ⟨3418341, by rfl⟩ : syracuseStep 9115577 = 6836683) B6836683
theorem B6077051 : Blo 2103435 6077051 := bstep (se 1 (by rfl) ⟨4557788, by rfl⟩ : syracuseStep 6077051 = 9115577) B9115577
theorem B4051367 : Blo 2103435 4051367 := bstep (se 1 (by rfl) ⟨3038525, by rfl⟩ : syracuseStep 4051367 = 6077051) B6077051
theorem B2700911 : Blo 2103435 2700911 := bstep (se 1 (by rfl) ⟨2025683, by rfl⟩ : syracuseStep 2700911 = 4051367) B4051367
theorem B7202429 : Blo 2103435 7202429 := bstep (se 3 (by rfl) ⟨1350455, by rfl⟩ : syracuseStep 7202429 = 2700911) B2700911
theorem B4801619 : Blo 2103435 4801619 := bstep (se 1 (by rfl) ⟨3601214, by rfl⟩ : syracuseStep 4801619 = 7202429) B7202429
theorem B12804317 : Blo 2103435 12804317 := bstep (se 3 (by rfl) ⟨2400809, by rfl⟩ : syracuseStep 12804317 = 4801619) B4801619
theorem B8536211 : Blo 2103435 8536211 := bstep (se 1 (by rfl) ⟨6402158, by rfl⟩ : syracuseStep 8536211 = 12804317) B12804317
theorem B5690807 : Blo 2103435 5690807 := bstep (se 1 (by rfl) ⟨4268105, by rfl⟩ : syracuseStep 5690807 = 8536211) B8536211
theorem B3793871 : Blo 2103435 3793871 := bstep (se 1 (by rfl) ⟨2845403, by rfl⟩ : syracuseStep 3793871 = 5690807) B5690807
theorem B2529247 : Blo 2103435 2529247 := bstep (se 1 (by rfl) ⟨1896935, by rfl⟩ : syracuseStep 2529247 = 3793871) B3793871
theorem B3372329 : Blo 2103435 3372329 := bstep (se 2 (by rfl) ⟨1264623, by rfl⟩ : syracuseStep 3372329 = 2529247) B2529247
theorem B2248219 : Blo 2103435 2248219 := bstep (se 1 (by rfl) ⟨1686164, by rfl⟩ : syracuseStep 2248219 = 3372329) B3372329
theorem B11990501 : Blo 2103435 11990501 := bstep (se 4 (by rfl) ⟨1124109, by rfl⟩ : syracuseStep 11990501 = 2248219) B2248219
theorem B7993667 : Blo 2103435 7993667 := bstep (se 1 (by rfl) ⟨5995250, by rfl⟩ : syracuseStep 7993667 = 11990501) B11990501
theorem B5329111 : Blo 2103435 5329111 := bstep (se 1 (by rfl) ⟨3996833, by rfl⟩ : syracuseStep 5329111 = 7993667) B7993667
theorem B7105481 : Blo 2103435 7105481 := bstep (se 2 (by rfl) ⟨2664555, by rfl⟩ : syracuseStep 7105481 = 5329111) B5329111
theorem B4736987 : Blo 2103435 4736987 := bstep (se 1 (by rfl) ⟨3552740, by rfl⟩ : syracuseStep 4736987 = 7105481) B7105481
theorem B3157991 : Blo 2103435 3157991 := bstep (se 1 (by rfl) ⟨2368493, by rfl⟩ : syracuseStep 3157991 = 4736987) B4736987
theorem B2105327 : Blo 2103435 2105327 := bstep (se 1 (by rfl) ⟨1578995, by rfl⟩ : syracuseStep 2105327 = 3157991) B3157991
theorem B3157997 : Blo 2103435 3157997 := bbase (se 3 (by rfl) ⟨592124, by rfl⟩ : syracuseStep 3157997 = 1184249) (by norm_num)
theorem B2105331 : Blo 2103435 2105331 := bstep (se 1 (by rfl) ⟨1578998, by rfl⟩ : syracuseStep 2105331 = 3157997) B3157997
theorem B4737005 : Blo 2103435 4737005 := bbase (se 3 (by rfl) ⟨888188, by rfl⟩ : syracuseStep 4737005 = 1776377) (by norm_num)
theorem B3158003 : Blo 2103435 3158003 := bstep (se 1 (by rfl) ⟨2368502, by rfl⟩ : syracuseStep 3158003 = 4737005) B4737005
theorem B2105335 : Blo 2103435 2105335 := bstep (se 1 (by rfl) ⟨1579001, by rfl⟩ : syracuseStep 2105335 = 3158003) B3158003
theorem B3372349 : Blo 2103435 3372349 := bbase (se 3 (by rfl) ⟨632315, by rfl⟩ : syracuseStep 3372349 = 1264631) (by norm_num)
theorem B4496465 : Blo 2103435 4496465 := bstep (se 2 (by rfl) ⟨1686174, by rfl⟩ : syracuseStep 4496465 = 3372349) B3372349
theorem B2997643 : Blo 2103435 2997643 := bstep (se 1 (by rfl) ⟨2248232, by rfl⟩ : syracuseStep 2997643 = 4496465) B4496465
theorem B3996857 : Blo 2103435 3996857 := bstep (se 2 (by rfl) ⟨1498821, by rfl⟩ : syracuseStep 3996857 = 2997643) B2997643
theorem B2664571 : Blo 2103435 2664571 := bstep (se 1 (by rfl) ⟨1998428, by rfl⟩ : syracuseStep 2664571 = 3996857) B3996857
theorem B3552761 : Blo 2103435 3552761 := bstep (se 2 (by rfl) ⟨1332285, by rfl⟩ : syracuseStep 3552761 = 2664571) B2664571
theorem B2368507 : Blo 2103435 2368507 := bstep (se 1 (by rfl) ⟨1776380, by rfl⟩ : syracuseStep 2368507 = 3552761) B3552761
theorem B3158009 : Blo 2103435 3158009 := bstep (se 2 (by rfl) ⟨1184253, by rfl⟩ : syracuseStep 3158009 = 2368507) B2368507
theorem B2105339 : Blo 2103435 2105339 := bstep (se 1 (by rfl) ⟨1579004, by rfl⟩ : syracuseStep 2105339 = 3158009) B3158009
theorem B9240005 : Blo 2103435 9240005 := bbase (se 4 (by rfl) ⟨866250, by rfl⟩ : syracuseStep 9240005 = 1732501) (by norm_num)
theorem B6160003 : Blo 2103435 6160003 := bstep (se 1 (by rfl) ⟨4620002, by rfl⟩ : syracuseStep 6160003 = 9240005) B9240005
theorem B32853349 : Blo 2103435 32853349 := bstep (se 4 (by rfl) ⟨3080001, by rfl⟩ : syracuseStep 32853349 = 6160003) B6160003
theorem B175217861 : Blo 2103435 175217861 := bstep (se 4 (by rfl) ⟨16426674, by rfl⟩ : syracuseStep 175217861 = 32853349) B32853349
theorem B467247629 : Blo 2103435 467247629 := bstep (se 3 (by rfl) ⟨87608930, by rfl⟩ : syracuseStep 467247629 = 175217861) B175217861
theorem B311498419 : Blo 2103435 311498419 := bstep (se 1 (by rfl) ⟨233623814, by rfl⟩ : syracuseStep 311498419 = 467247629) B467247629
theorem B415331225 : Blo 2103435 415331225 := bstep (se 2 (by rfl) ⟨155749209, by rfl⟩ : syracuseStep 415331225 = 311498419) B311498419
theorem B276887483 : Blo 2103435 276887483 := bstep (se 1 (by rfl) ⟨207665612, by rfl⟩ : syracuseStep 276887483 = 415331225) B415331225
theorem B184591655 : Blo 2103435 184591655 := bstep (se 1 (by rfl) ⟨138443741, by rfl⟩ : syracuseStep 184591655 = 276887483) B276887483
theorem B123061103 : Blo 2103435 123061103 := bstep (se 1 (by rfl) ⟨92295827, by rfl⟩ : syracuseStep 123061103 = 184591655) B184591655
theorem B82040735 : Blo 2103435 82040735 := bstep (se 1 (by rfl) ⟨61530551, by rfl⟩ : syracuseStep 82040735 = 123061103) B123061103
theorem B218775293 : Blo 2103435 218775293 := bstep (se 3 (by rfl) ⟨41020367, by rfl⟩ : syracuseStep 218775293 = 82040735) B82040735
theorem B145850195 : Blo 2103435 145850195 := bstep (se 1 (by rfl) ⟨109387646, by rfl⟩ : syracuseStep 145850195 = 218775293) B218775293
theorem B97233463 : Blo 2103435 97233463 := bstep (se 1 (by rfl) ⟨72925097, by rfl⟩ : syracuseStep 97233463 = 145850195) B145850195
theorem B518578469 : Blo 2103435 518578469 := bstep (se 4 (by rfl) ⟨48616731, by rfl⟩ : syracuseStep 518578469 = 97233463) B97233463
theorem B345718979 : Blo 2103435 345718979 := bstep (se 1 (by rfl) ⟨259289234, by rfl⟩ : syracuseStep 345718979 = 518578469) B518578469
theorem B230479319 : Blo 2103435 230479319 := bstep (se 1 (by rfl) ⟨172859489, by rfl⟩ : syracuseStep 230479319 = 345718979) B345718979
theorem B153652879 : Blo 2103435 153652879 := bstep (se 1 (by rfl) ⟨115239659, by rfl⟩ : syracuseStep 153652879 = 230479319) B230479319
theorem B204870505 : Blo 2103435 204870505 := bstep (se 2 (by rfl) ⟨76826439, by rfl⟩ : syracuseStep 204870505 = 153652879) B153652879
theorem B273160673 : Blo 2103435 273160673 := bstep (se 2 (by rfl) ⟨102435252, by rfl⟩ : syracuseStep 273160673 = 204870505) B204870505
theorem B182107115 : Blo 2103435 182107115 := bstep (se 1 (by rfl) ⟨136580336, by rfl⟩ : syracuseStep 182107115 = 273160673) B273160673
theorem B121404743 : Blo 2103435 121404743 := bstep (se 1 (by rfl) ⟨91053557, by rfl⟩ : syracuseStep 121404743 = 182107115) B182107115
theorem B80936495 : Blo 2103435 80936495 := bstep (se 1 (by rfl) ⟨60702371, by rfl⟩ : syracuseStep 80936495 = 121404743) B121404743
theorem B53957663 : Blo 2103435 53957663 := bstep (se 1 (by rfl) ⟨40468247, by rfl⟩ : syracuseStep 53957663 = 80936495) B80936495
theorem B35971775 : Blo 2103435 35971775 := bstep (se 1 (by rfl) ⟨26978831, by rfl⟩ : syracuseStep 35971775 = 53957663) B53957663
theorem B23981183 : Blo 2103435 23981183 := bstep (se 1 (by rfl) ⟨17985887, by rfl⟩ : syracuseStep 23981183 = 35971775) B35971775
theorem B15987455 : Blo 2103435 15987455 := bstep (se 1 (by rfl) ⟨11990591, by rfl⟩ : syracuseStep 15987455 = 23981183) B23981183
theorem B10658303 : Blo 2103435 10658303 := bstep (se 1 (by rfl) ⟨7993727, by rfl⟩ : syracuseStep 10658303 = 15987455) B15987455
theorem B7105535 : Blo 2103435 7105535 := bstep (se 1 (by rfl) ⟨5329151, by rfl⟩ : syracuseStep 7105535 = 10658303) B10658303
theorem B4737023 : Blo 2103435 4737023 := bstep (se 1 (by rfl) ⟨3552767, by rfl⟩ : syracuseStep 4737023 = 7105535) B7105535
theorem B3158015 : Blo 2103435 3158015 := bstep (se 1 (by rfl) ⟨2368511, by rfl⟩ : syracuseStep 3158015 = 4737023) B4737023
theorem B2105343 : Blo 2103435 2105343 := bstep (se 1 (by rfl) ⟨1579007, by rfl⟩ : syracuseStep 2105343 = 3158015) B3158015
theorem B3158021 : Blo 2103435 3158021 := bbase (se 4 (by rfl) ⟨296064, by rfl⟩ : syracuseStep 3158021 = 592129) (by norm_num)
theorem B2105347 : Blo 2103435 2105347 := bstep (se 1 (by rfl) ⟨1579010, by rfl⟩ : syracuseStep 2105347 = 3158021) B3158021
theorem B3552781 : Blo 2103435 3552781 := bbase (se 3 (by rfl) ⟨666146, by rfl⟩ : syracuseStep 3552781 = 1332293) (by norm_num)
theorem B4737041 : Blo 2103435 4737041 := bstep (se 2 (by rfl) ⟨1776390, by rfl⟩ : syracuseStep 4737041 = 3552781) B3552781
theorem B3158027 : Blo 2103435 3158027 := bstep (se 1 (by rfl) ⟨2368520, by rfl⟩ : syracuseStep 3158027 = 4737041) B4737041
theorem B2105351 : Blo 2103435 2105351 := bstep (se 1 (by rfl) ⟨1579013, by rfl⟩ : syracuseStep 2105351 = 3158027) B3158027
theorem B2368525 : Blo 2103435 2368525 := bbase (se 3 (by rfl) ⟨444098, by rfl⟩ : syracuseStep 2368525 = 888197) (by norm_num)
theorem B3158033 : Blo 2103435 3158033 := bstep (se 2 (by rfl) ⟨1184262, by rfl⟩ : syracuseStep 3158033 = 2368525) B2368525
theorem B2105355 : Blo 2103435 2105355 := bstep (se 1 (by rfl) ⟨1579016, by rfl⟩ : syracuseStep 2105355 = 3158033) B3158033
theorem B7105589 : Blo 2103435 7105589 := bbase (se 5 (by rfl) ⟨333074, by rfl⟩ : syracuseStep 7105589 = 666149) (by norm_num)
theorem B4737059 : Blo 2103435 4737059 := bstep (se 1 (by rfl) ⟨3552794, by rfl⟩ : syracuseStep 4737059 = 7105589) B7105589
theorem B3158039 : Blo 2103435 3158039 := bstep (se 1 (by rfl) ⟨2368529, by rfl⟩ : syracuseStep 3158039 = 4737059) B4737059
theorem B2105359 : Blo 2103435 2105359 := bstep (se 1 (by rfl) ⟨1579019, by rfl⟩ : syracuseStep 2105359 = 3158039) B3158039
theorem B3158045 : Blo 2103435 3158045 := bbase (se 3 (by rfl) ⟨592133, by rfl⟩ : syracuseStep 3158045 = 1184267) (by norm_num)
theorem B2105363 : Blo 2103435 2105363 := bstep (se 1 (by rfl) ⟨1579022, by rfl⟩ : syracuseStep 2105363 = 3158045) B3158045
theorem B4737077 : Blo 2103435 4737077 := bbase (se 5 (by rfl) ⟨222050, by rfl⟩ : syracuseStep 4737077 = 444101) (by norm_num)
theorem B3158051 : Blo 2103435 3158051 := bstep (se 1 (by rfl) ⟨2368538, by rfl⟩ : syracuseStep 3158051 = 4737077) B4737077
theorem B2105367 : Blo 2103435 2105367 := bstep (se 1 (by rfl) ⟨1579025, by rfl⟩ : syracuseStep 2105367 = 3158051) B3158051
theorem B7691429 : Blo 2103435 7691429 := bbase (se 4 (by rfl) ⟨721071, by rfl⟩ : syracuseStep 7691429 = 1442143) (by norm_num)
theorem B5127619 : Blo 2103435 5127619 := bstep (se 1 (by rfl) ⟨3845714, by rfl⟩ : syracuseStep 5127619 = 7691429) B7691429
theorem B6836825 : Blo 2103435 6836825 := bstep (se 2 (by rfl) ⟨2563809, by rfl⟩ : syracuseStep 6836825 = 5127619) B5127619
theorem B4557883 : Blo 2103435 4557883 := bstep (se 1 (by rfl) ⟨3418412, by rfl⟩ : syracuseStep 4557883 = 6836825) B6836825
theorem B6077177 : Blo 2103435 6077177 := bstep (se 2 (by rfl) ⟨2278941, by rfl⟩ : syracuseStep 6077177 = 4557883) B4557883
theorem B4051451 : Blo 2103435 4051451 := bstep (se 1 (by rfl) ⟨3038588, by rfl⟩ : syracuseStep 4051451 = 6077177) B6077177
theorem B2700967 : Blo 2103435 2700967 := bstep (se 1 (by rfl) ⟨2025725, by rfl⟩ : syracuseStep 2700967 = 4051451) B4051451
theorem B3601289 : Blo 2103435 3601289 := bstep (se 2 (by rfl) ⟨1350483, by rfl⟩ : syracuseStep 3601289 = 2700967) B2700967
theorem B2400859 : Blo 2103435 2400859 := bstep (se 1 (by rfl) ⟨1800644, by rfl⟩ : syracuseStep 2400859 = 3601289) B3601289
theorem B12804581 : Blo 2103435 12804581 := bstep (se 4 (by rfl) ⟨1200429, by rfl⟩ : syracuseStep 12804581 = 2400859) B2400859
theorem B34145549 : Blo 2103435 34145549 := bstep (se 3 (by rfl) ⟨6402290, by rfl⟩ : syracuseStep 34145549 = 12804581) B12804581
theorem B22763699 : Blo 2103435 22763699 := bstep (se 1 (by rfl) ⟨17072774, by rfl⟩ : syracuseStep 22763699 = 34145549) B34145549
theorem B15175799 : Blo 2103435 15175799 := bstep (se 1 (by rfl) ⟨11381849, by rfl⟩ : syracuseStep 15175799 = 22763699) B22763699
theorem B10117199 : Blo 2103435 10117199 := bstep (se 1 (by rfl) ⟨7587899, by rfl⟩ : syracuseStep 10117199 = 15175799) B15175799
theorem B6744799 : Blo 2103435 6744799 := bstep (se 1 (by rfl) ⟨5058599, by rfl⟩ : syracuseStep 6744799 = 10117199) B10117199
theorem B8993065 : Blo 2103435 8993065 := bstep (se 2 (by rfl) ⟨3372399, by rfl⟩ : syracuseStep 8993065 = 6744799) B6744799
theorem B11990753 : Blo 2103435 11990753 := bstep (se 2 (by rfl) ⟨4496532, by rfl⟩ : syracuseStep 11990753 = 8993065) B8993065
theorem B7993835 : Blo 2103435 7993835 := bstep (se 1 (by rfl) ⟨5995376, by rfl⟩ : syracuseStep 7993835 = 11990753) B11990753
theorem B5329223 : Blo 2103435 5329223 := bstep (se 1 (by rfl) ⟨3996917, by rfl⟩ : syracuseStep 5329223 = 7993835) B7993835
theorem B3552815 : Blo 2103435 3552815 := bstep (se 1 (by rfl) ⟨2664611, by rfl⟩ : syracuseStep 3552815 = 5329223) B5329223
theorem B2368543 : Blo 2103435 2368543 := bstep (se 1 (by rfl) ⟨1776407, by rfl⟩ : syracuseStep 2368543 = 3552815) B3552815
theorem B3158057 : Blo 2103435 3158057 := bstep (se 2 (by rfl) ⟨1184271, by rfl⟩ : syracuseStep 3158057 = 2368543) B2368543
theorem B2105371 : Blo 2103435 2105371 := bstep (se 1 (by rfl) ⟨1579028, by rfl⟩ : syracuseStep 2105371 = 3158057) B3158057
theorem B10255253 : Blo 2103435 10255253 := bbase (se 6 (by rfl) ⟨240357, by rfl⟩ : syracuseStep 10255253 = 480715) (by norm_num)
theorem B27347341 : Blo 2103435 27347341 := bstep (se 3 (by rfl) ⟨5127626, by rfl⟩ : syracuseStep 27347341 = 10255253) B10255253
theorem B36463121 : Blo 2103435 36463121 := bstep (se 2 (by rfl) ⟨13673670, by rfl⟩ : syracuseStep 36463121 = 27347341) B27347341
theorem B24308747 : Blo 2103435 24308747 := bstep (se 1 (by rfl) ⟨18231560, by rfl⟩ : syracuseStep 24308747 = 36463121) B36463121
theorem B16205831 : Blo 2103435 16205831 := bstep (se 1 (by rfl) ⟨12154373, by rfl⟩ : syracuseStep 16205831 = 24308747) B24308747
theorem B10803887 : Blo 2103435 10803887 := bstep (se 1 (by rfl) ⟨8102915, by rfl⟩ : syracuseStep 10803887 = 16205831) B16205831
theorem B7202591 : Blo 2103435 7202591 := bstep (se 1 (by rfl) ⟨5401943, by rfl⟩ : syracuseStep 7202591 = 10803887) B10803887
theorem B4801727 : Blo 2103435 4801727 := bstep (se 1 (by rfl) ⟨3601295, by rfl⟩ : syracuseStep 4801727 = 7202591) B7202591
theorem B12804605 : Blo 2103435 12804605 := bstep (se 3 (by rfl) ⟨2400863, by rfl⟩ : syracuseStep 12804605 = 4801727) B4801727
theorem B8536403 : Blo 2103435 8536403 := bstep (se 1 (by rfl) ⟨6402302, by rfl⟩ : syracuseStep 8536403 = 12804605) B12804605
theorem B5690935 : Blo 2103435 5690935 := bstep (se 1 (by rfl) ⟨4268201, by rfl⟩ : syracuseStep 5690935 = 8536403) B8536403
theorem B7587913 : Blo 2103435 7587913 := bstep (se 2 (by rfl) ⟨2845467, by rfl⟩ : syracuseStep 7587913 = 5690935) B5690935
theorem B10117217 : Blo 2103435 10117217 := bstep (se 2 (by rfl) ⟨3793956, by rfl⟩ : syracuseStep 10117217 = 7587913) B7587913
theorem B6744811 : Blo 2103435 6744811 := bstep (se 1 (by rfl) ⟨5058608, by rfl⟩ : syracuseStep 6744811 = 10117217) B10117217
theorem B8993081 : Blo 2103435 8993081 := bstep (se 2 (by rfl) ⟨3372405, by rfl⟩ : syracuseStep 8993081 = 6744811) B6744811
theorem B5995387 : Blo 2103435 5995387 := bstep (se 1 (by rfl) ⟨4496540, by rfl⟩ : syracuseStep 5995387 = 8993081) B8993081
theorem B7993849 : Blo 2103435 7993849 := bstep (se 2 (by rfl) ⟨2997693, by rfl⟩ : syracuseStep 7993849 = 5995387) B5995387
theorem B10658465 : Blo 2103435 10658465 := bstep (se 2 (by rfl) ⟨3996924, by rfl⟩ : syracuseStep 10658465 = 7993849) B7993849
theorem B7105643 : Blo 2103435 7105643 := bstep (se 1 (by rfl) ⟨5329232, by rfl⟩ : syracuseStep 7105643 = 10658465) B10658465
theorem B4737095 : Blo 2103435 4737095 := bstep (se 1 (by rfl) ⟨3552821, by rfl⟩ : syracuseStep 4737095 = 7105643) B7105643
theorem B3158063 : Blo 2103435 3158063 := bstep (se 1 (by rfl) ⟨2368547, by rfl⟩ : syracuseStep 3158063 = 4737095) B4737095
theorem B2105375 : Blo 2103435 2105375 := bstep (se 1 (by rfl) ⟨1579031, by rfl⟩ : syracuseStep 2105375 = 3158063) B3158063
theorem B3158069 : Blo 2103435 3158069 := bbase (se 5 (by rfl) ⟨148034, by rfl⟩ : syracuseStep 3158069 = 296069) (by norm_num)
theorem B2105379 : Blo 2103435 2105379 := bstep (se 1 (by rfl) ⟨1579034, by rfl⟩ : syracuseStep 2105379 = 3158069) B3158069
theorem B5329253 : Blo 2103435 5329253 := bbase (se 4 (by rfl) ⟨499617, by rfl⟩ : syracuseStep 5329253 = 999235) (by norm_num)
theorem B3552835 : Blo 2103435 3552835 := bstep (se 1 (by rfl) ⟨2664626, by rfl⟩ : syracuseStep 3552835 = 5329253) B5329253
theorem B4737113 : Blo 2103435 4737113 := bstep (se 2 (by rfl) ⟨1776417, by rfl⟩ : syracuseStep 4737113 = 3552835) B3552835
theorem B3158075 : Blo 2103435 3158075 := bstep (se 1 (by rfl) ⟨2368556, by rfl⟩ : syracuseStep 3158075 = 4737113) B4737113
theorem B2105383 : Blo 2103435 2105383 := bstep (se 1 (by rfl) ⟨1579037, by rfl⟩ : syracuseStep 2105383 = 3158075) B3158075
theorem B2368561 : Blo 2103435 2368561 := bbase (se 2 (by rfl) ⟨888210, by rfl⟩ : syracuseStep 2368561 = 1776421) (by norm_num)
theorem B3158081 : Blo 2103435 3158081 := bstep (se 2 (by rfl) ⟨1184280, by rfl⟩ : syracuseStep 3158081 = 2368561) B2368561
theorem B2105387 : Blo 2103435 2105387 := bstep (se 1 (by rfl) ⟨1579040, by rfl⟩ : syracuseStep 2105387 = 3158081) B3158081
theorem B15382997 : Blo 2103435 15382997 := bbase (se 7 (by rfl) ⟨180269, by rfl⟩ : syracuseStep 15382997 = 360539) (by norm_num)
theorem B10255331 : Blo 2103435 10255331 := bstep (se 1 (by rfl) ⟨7691498, by rfl⟩ : syracuseStep 10255331 = 15382997) B15382997
theorem B6836887 : Blo 2103435 6836887 := bstep (se 1 (by rfl) ⟨5127665, by rfl⟩ : syracuseStep 6836887 = 10255331) B10255331
theorem B9115849 : Blo 2103435 9115849 := bstep (se 2 (by rfl) ⟨3418443, by rfl⟩ : syracuseStep 9115849 = 6836887) B6836887
theorem B12154465 : Blo 2103435 12154465 := bstep (se 2 (by rfl) ⟨4557924, by rfl⟩ : syracuseStep 12154465 = 9115849) B9115849
theorem B16205953 : Blo 2103435 16205953 := bstep (se 2 (by rfl) ⟨6077232, by rfl⟩ : syracuseStep 16205953 = 12154465) B12154465
theorem B21607937 : Blo 2103435 21607937 := bstep (se 2 (by rfl) ⟨8102976, by rfl⟩ : syracuseStep 21607937 = 16205953) B16205953
theorem B14405291 : Blo 2103435 14405291 := bstep (se 1 (by rfl) ⟨10803968, by rfl⟩ : syracuseStep 14405291 = 21607937) B21607937
theorem B9603527 : Blo 2103435 9603527 := bstep (se 1 (by rfl) ⟨7202645, by rfl⟩ : syracuseStep 9603527 = 14405291) B14405291
theorem B25609405 : Blo 2103435 25609405 := bstep (se 3 (by rfl) ⟨4801763, by rfl⟩ : syracuseStep 25609405 = 9603527) B9603527
theorem B34145873 : Blo 2103435 34145873 := bstep (se 2 (by rfl) ⟨12804702, by rfl⟩ : syracuseStep 34145873 = 25609405) B25609405
theorem B22763915 : Blo 2103435 22763915 := bstep (se 1 (by rfl) ⟨17072936, by rfl⟩ : syracuseStep 22763915 = 34145873) B34145873
theorem B15175943 : Blo 2103435 15175943 := bstep (se 1 (by rfl) ⟨11381957, by rfl⟩ : syracuseStep 15175943 = 22763915) B22763915
theorem B10117295 : Blo 2103435 10117295 := bstep (se 1 (by rfl) ⟨7587971, by rfl⟩ : syracuseStep 10117295 = 15175943) B15175943
theorem B6744863 : Blo 2103435 6744863 := bstep (se 1 (by rfl) ⟨5058647, by rfl⟩ : syracuseStep 6744863 = 10117295) B10117295
theorem B4496575 : Blo 2103435 4496575 := bstep (se 1 (by rfl) ⟨3372431, by rfl⟩ : syracuseStep 4496575 = 6744863) B6744863
theorem B5995433 : Blo 2103435 5995433 := bstep (se 2 (by rfl) ⟨2248287, by rfl⟩ : syracuseStep 5995433 = 4496575) B4496575
theorem B3996955 : Blo 2103435 3996955 := bstep (se 1 (by rfl) ⟨2997716, by rfl⟩ : syracuseStep 3996955 = 5995433) B5995433
theorem B5329273 : Blo 2103435 5329273 := bstep (se 2 (by rfl) ⟨1998477, by rfl⟩ : syracuseStep 5329273 = 3996955) B3996955
theorem B7105697 : Blo 2103435 7105697 := bstep (se 2 (by rfl) ⟨2664636, by rfl⟩ : syracuseStep 7105697 = 5329273) B5329273
theorem B4737131 : Blo 2103435 4737131 := bstep (se 1 (by rfl) ⟨3552848, by rfl⟩ : syracuseStep 4737131 = 7105697) B7105697
theorem B3158087 : Blo 2103435 3158087 := bstep (se 1 (by rfl) ⟨2368565, by rfl⟩ : syracuseStep 3158087 = 4737131) B4737131
theorem B2105391 : Blo 2103435 2105391 := bstep (se 1 (by rfl) ⟨1579043, by rfl⟩ : syracuseStep 2105391 = 3158087) B3158087
theorem B3158093 : Blo 2103435 3158093 := bbase (se 3 (by rfl) ⟨592142, by rfl⟩ : syracuseStep 3158093 = 1184285) (by norm_num)
theorem B2105395 : Blo 2103435 2105395 := bstep (se 1 (by rfl) ⟨1579046, by rfl⟩ : syracuseStep 2105395 = 3158093) B3158093
theorem B4737149 : Blo 2103435 4737149 := bbase (se 3 (by rfl) ⟨888215, by rfl⟩ : syracuseStep 4737149 = 1776431) (by norm_num)
theorem B3158099 : Blo 2103435 3158099 := bstep (se 1 (by rfl) ⟨2368574, by rfl⟩ : syracuseStep 3158099 = 4737149) B4737149
theorem B2105399 : Blo 2103435 2105399 := bstep (se 1 (by rfl) ⟨1579049, by rfl⟩ : syracuseStep 2105399 = 3158099) B3158099
theorem B3552869 : Blo 2103435 3552869 := bbase (se 4 (by rfl) ⟨333081, by rfl⟩ : syracuseStep 3552869 = 666163) (by norm_num)
theorem B2368579 : Blo 2103435 2368579 := bstep (se 1 (by rfl) ⟨1776434, by rfl⟩ : syracuseStep 2368579 = 3552869) B3552869
theorem B3158105 : Blo 2103435 3158105 := bstep (se 2 (by rfl) ⟨1184289, by rfl⟩ : syracuseStep 3158105 = 2368579) B2368579
theorem B2105403 : Blo 2103435 2105403 := bstep (se 1 (by rfl) ⟨1579052, by rfl⟩ : syracuseStep 2105403 = 3158105) B3158105
theorem B13156597 : Blo 2103435 13156597 := bbase (se 5 (by rfl) ⟨616715, by rfl⟩ : syracuseStep 13156597 = 1233431) (by norm_num)
theorem B17542129 : Blo 2103435 17542129 := bstep (se 2 (by rfl) ⟨6578298, by rfl⟩ : syracuseStep 17542129 = 13156597) B13156597
theorem B23389505 : Blo 2103435 23389505 := bstep (se 2 (by rfl) ⟨8771064, by rfl⟩ : syracuseStep 23389505 = 17542129) B17542129
theorem B15593003 : Blo 2103435 15593003 := bstep (se 1 (by rfl) ⟨11694752, by rfl⟩ : syracuseStep 15593003 = 23389505) B23389505
theorem B10395335 : Blo 2103435 10395335 := bstep (se 1 (by rfl) ⟨7796501, by rfl⟩ : syracuseStep 10395335 = 15593003) B15593003
theorem B27720893 : Blo 2103435 27720893 := bstep (se 3 (by rfl) ⟨5197667, by rfl⟩ : syracuseStep 27720893 = 10395335) B10395335
theorem B18480595 : Blo 2103435 18480595 := bstep (se 1 (by rfl) ⟨13860446, by rfl⟩ : syracuseStep 18480595 = 27720893) B27720893
theorem B24640793 : Blo 2103435 24640793 := bstep (se 2 (by rfl) ⟨9240297, by rfl⟩ : syracuseStep 24640793 = 18480595) B18480595
theorem B16427195 : Blo 2103435 16427195 := bstep (se 1 (by rfl) ⟨12320396, by rfl⟩ : syracuseStep 16427195 = 24640793) B24640793
theorem B10951463 : Blo 2103435 10951463 := bstep (se 1 (by rfl) ⟨8213597, by rfl⟩ : syracuseStep 10951463 = 16427195) B16427195
theorem B29203901 : Blo 2103435 29203901 := bstep (se 3 (by rfl) ⟨5475731, by rfl⟩ : syracuseStep 29203901 = 10951463) B10951463
theorem B19469267 : Blo 2103435 19469267 := bstep (se 1 (by rfl) ⟨14601950, by rfl⟩ : syracuseStep 19469267 = 29203901) B29203901
theorem B12979511 : Blo 2103435 12979511 := bstep (se 1 (by rfl) ⟨9734633, by rfl⟩ : syracuseStep 12979511 = 19469267) B19469267
theorem B8653007 : Blo 2103435 8653007 := bstep (se 1 (by rfl) ⟨6489755, by rfl⟩ : syracuseStep 8653007 = 12979511) B12979511
theorem B5768671 : Blo 2103435 5768671 := bstep (se 1 (by rfl) ⟨4326503, by rfl⟩ : syracuseStep 5768671 = 8653007) B8653007
theorem B7691561 : Blo 2103435 7691561 := bstep (se 2 (by rfl) ⟨2884335, by rfl⟩ : syracuseStep 7691561 = 5768671) B5768671
theorem B5127707 : Blo 2103435 5127707 := bstep (se 1 (by rfl) ⟨3845780, by rfl⟩ : syracuseStep 5127707 = 7691561) B7691561
theorem B3418471 : Blo 2103435 3418471 := bstep (se 1 (by rfl) ⟨2563853, by rfl⟩ : syracuseStep 3418471 = 5127707) B5127707
theorem B4557961 : Blo 2103435 4557961 := bstep (se 2 (by rfl) ⟨1709235, by rfl⟩ : syracuseStep 4557961 = 3418471) B3418471
theorem B6077281 : Blo 2103435 6077281 := bstep (se 2 (by rfl) ⟨2278980, by rfl⟩ : syracuseStep 6077281 = 4557961) B4557961
theorem B8103041 : Blo 2103435 8103041 := bstep (se 2 (by rfl) ⟨3038640, by rfl⟩ : syracuseStep 8103041 = 6077281) B6077281
theorem B5402027 : Blo 2103435 5402027 := bstep (se 1 (by rfl) ⟨4051520, by rfl⟩ : syracuseStep 5402027 = 8103041) B8103041
theorem B3601351 : Blo 2103435 3601351 := bstep (se 1 (by rfl) ⟨2701013, by rfl⟩ : syracuseStep 3601351 = 5402027) B5402027
theorem B19207205 : Blo 2103435 19207205 := bstep (se 4 (by rfl) ⟨1800675, by rfl⟩ : syracuseStep 19207205 = 3601351) B3601351
theorem B12804803 : Blo 2103435 12804803 := bstep (se 1 (by rfl) ⟨9603602, by rfl⟩ : syracuseStep 12804803 = 19207205) B19207205
theorem B8536535 : Blo 2103435 8536535 := bstep (se 1 (by rfl) ⟨6402401, by rfl⟩ : syracuseStep 8536535 = 12804803) B12804803
theorem B5691023 : Blo 2103435 5691023 := bstep (se 1 (by rfl) ⟨4268267, by rfl⟩ : syracuseStep 5691023 = 8536535) B8536535
theorem B3794015 : Blo 2103435 3794015 := bstep (se 1 (by rfl) ⟨2845511, by rfl⟩ : syracuseStep 3794015 = 5691023) B5691023
theorem B2529343 : Blo 2103435 2529343 := bstep (se 1 (by rfl) ⟨1897007, by rfl⟩ : syracuseStep 2529343 = 3794015) B3794015
theorem B3372457 : Blo 2103435 3372457 := bstep (se 2 (by rfl) ⟨1264671, by rfl⟩ : syracuseStep 3372457 = 2529343) B2529343
theorem B4496609 : Blo 2103435 4496609 := bstep (se 2 (by rfl) ⟨1686228, by rfl⟩ : syracuseStep 4496609 = 3372457) B3372457
theorem B2997739 : Blo 2103435 2997739 := bstep (se 1 (by rfl) ⟨2248304, by rfl⟩ : syracuseStep 2997739 = 4496609) B4496609
theorem B15987941 : Blo 2103435 15987941 := bstep (se 4 (by rfl) ⟨1498869, by rfl⟩ : syracuseStep 15987941 = 2997739) B2997739
theorem B10658627 : Blo 2103435 10658627 := bstep (se 1 (by rfl) ⟨7993970, by rfl⟩ : syracuseStep 10658627 = 15987941) B15987941
theorem B7105751 : Blo 2103435 7105751 := bstep (se 1 (by rfl) ⟨5329313, by rfl⟩ : syracuseStep 7105751 = 10658627) B10658627
theorem B4737167 : Blo 2103435 4737167 := bstep (se 1 (by rfl) ⟨3552875, by rfl⟩ : syracuseStep 4737167 = 7105751) B7105751
theorem B3158111 : Blo 2103435 3158111 := bstep (se 1 (by rfl) ⟨2368583, by rfl⟩ : syracuseStep 3158111 = 4737167) B4737167
theorem B2105407 : Blo 2103435 2105407 := bstep (se 1 (by rfl) ⟨1579055, by rfl⟩ : syracuseStep 2105407 = 3158111) B3158111
theorem B3158117 : Blo 2103435 3158117 := bbase (se 4 (by rfl) ⟨296073, by rfl⟩ : syracuseStep 3158117 = 592147) (by norm_num)
theorem B2105411 : Blo 2103435 2105411 := bstep (se 1 (by rfl) ⟨1579058, by rfl⟩ : syracuseStep 2105411 = 3158117) B3158117
theorem B2529353 : Blo 2103435 2529353 := bbase (se 2 (by rfl) ⟨948507, by rfl⟩ : syracuseStep 2529353 = 1897015) (by norm_num)
theorem B6744941 : Blo 2103435 6744941 := bstep (se 3 (by rfl) ⟨1264676, by rfl⟩ : syracuseStep 6744941 = 2529353) B2529353
theorem B4496627 : Blo 2103435 4496627 := bstep (se 1 (by rfl) ⟨3372470, by rfl⟩ : syracuseStep 4496627 = 6744941) B6744941
theorem B2997751 : Blo 2103435 2997751 := bstep (se 1 (by rfl) ⟨2248313, by rfl⟩ : syracuseStep 2997751 = 4496627) B4496627
theorem B3997001 : Blo 2103435 3997001 := bstep (se 2 (by rfl) ⟨1498875, by rfl⟩ : syracuseStep 3997001 = 2997751) B2997751
theorem B2664667 : Blo 2103435 2664667 := bstep (se 1 (by rfl) ⟨1998500, by rfl⟩ : syracuseStep 2664667 = 3997001) B3997001
theorem B3552889 : Blo 2103435 3552889 := bstep (se 2 (by rfl) ⟨1332333, by rfl⟩ : syracuseStep 3552889 = 2664667) B2664667
theorem B4737185 : Blo 2103435 4737185 := bstep (se 2 (by rfl) ⟨1776444, by rfl⟩ : syracuseStep 4737185 = 3552889) B3552889
theorem B3158123 : Blo 2103435 3158123 := bstep (se 1 (by rfl) ⟨2368592, by rfl⟩ : syracuseStep 3158123 = 4737185) B4737185
theorem B2105415 : Blo 2103435 2105415 := bstep (se 1 (by rfl) ⟨1579061, by rfl⟩ : syracuseStep 2105415 = 3158123) B3158123
theorem B2368597 : Blo 2103435 2368597 := bbase (se 8 (by rfl) ⟨13878, by rfl⟩ : syracuseStep 2368597 = 27757) (by norm_num)
theorem B3158129 : Blo 2103435 3158129 := bstep (se 2 (by rfl) ⟨1184298, by rfl⟩ : syracuseStep 3158129 = 2368597) B2368597
theorem B2105419 : Blo 2103435 2105419 := bstep (se 1 (by rfl) ⟨1579064, by rfl⟩ : syracuseStep 2105419 = 3158129) B3158129
theorem B2664677 : Blo 2103435 2664677 := bbase (se 4 (by rfl) ⟨249813, by rfl⟩ : syracuseStep 2664677 = 499627) (by norm_num)
theorem B7105805 : Blo 2103435 7105805 := bstep (se 3 (by rfl) ⟨1332338, by rfl⟩ : syracuseStep 7105805 = 2664677) B2664677
theorem B4737203 : Blo 2103435 4737203 := bstep (se 1 (by rfl) ⟨3552902, by rfl⟩ : syracuseStep 4737203 = 7105805) B7105805
theorem B3158135 : Blo 2103435 3158135 := bstep (se 1 (by rfl) ⟨2368601, by rfl⟩ : syracuseStep 3158135 = 4737203) B4737203
theorem B2105423 : Blo 2103435 2105423 := bstep (se 1 (by rfl) ⟨1579067, by rfl⟩ : syracuseStep 2105423 = 3158135) B3158135
theorem B3158141 : Blo 2103435 3158141 := bbase (se 3 (by rfl) ⟨592151, by rfl⟩ : syracuseStep 3158141 = 1184303) (by norm_num)
theorem B2105427 : Blo 2103435 2105427 := bstep (se 1 (by rfl) ⟨1579070, by rfl⟩ : syracuseStep 2105427 = 3158141) B3158141
theorem B4737221 : Blo 2103435 4737221 := bbase (se 4 (by rfl) ⟨444114, by rfl⟩ : syracuseStep 4737221 = 888229) (by norm_num)
theorem B3158147 : Blo 2103435 3158147 := bstep (se 1 (by rfl) ⟨2368610, by rfl⟩ : syracuseStep 3158147 = 4737221) B4737221
theorem B2105431 : Blo 2103435 2105431 := bstep (se 1 (by rfl) ⟨1579073, by rfl⟩ : syracuseStep 2105431 = 3158147) B3158147
theorem B2845549 : Blo 2103435 2845549 := bbase (se 3 (by rfl) ⟨533540, by rfl⟩ : syracuseStep 2845549 = 1067081) (by norm_num)
theorem B15176261 : Blo 2103435 15176261 := bstep (se 4 (by rfl) ⟨1422774, by rfl⟩ : syracuseStep 15176261 = 2845549) B2845549
theorem B10117507 : Blo 2103435 10117507 := bstep (se 1 (by rfl) ⟨7588130, by rfl⟩ : syracuseStep 10117507 = 15176261) B15176261
theorem B13490009 : Blo 2103435 13490009 := bstep (se 2 (by rfl) ⟨5058753, by rfl⟩ : syracuseStep 13490009 = 10117507) B10117507
theorem B8993339 : Blo 2103435 8993339 := bstep (se 1 (by rfl) ⟨6745004, by rfl⟩ : syracuseStep 8993339 = 13490009) B13490009
theorem B5995559 : Blo 2103435 5995559 := bstep (se 1 (by rfl) ⟨4496669, by rfl⟩ : syracuseStep 5995559 = 8993339) B8993339
theorem B3997039 : Blo 2103435 3997039 := bstep (se 1 (by rfl) ⟨2997779, by rfl⟩ : syracuseStep 3997039 = 5995559) B5995559
theorem B5329385 : Blo 2103435 5329385 := bstep (se 2 (by rfl) ⟨1998519, by rfl⟩ : syracuseStep 5329385 = 3997039) B3997039
theorem B3552923 : Blo 2103435 3552923 := bstep (se 1 (by rfl) ⟨2664692, by rfl⟩ : syracuseStep 3552923 = 5329385) B5329385
theorem B2368615 : Blo 2103435 2368615 := bstep (se 1 (by rfl) ⟨1776461, by rfl⟩ : syracuseStep 2368615 = 3552923) B3552923
theorem B3158153 : Blo 2103435 3158153 := bstep (se 2 (by rfl) ⟨1184307, by rfl⟩ : syracuseStep 3158153 = 2368615) B2368615
theorem B2105435 : Blo 2103435 2105435 := bstep (se 1 (by rfl) ⟨1579076, by rfl⟩ : syracuseStep 2105435 = 3158153) B3158153
theorem C0 (j : ℕ) (h1 : 525858 ≤ j) (h2 : j ≤ 526358) : Blo 2103435 (4 * j + 3) := by
  interval_cases j
  · exact B2103435
  · exact B2103439
  · exact B2103443
  · exact B2103447
  · exact B2103451
  · exact B2103455
  · exact B2103459
  · exact B2103463
  · exact B2103467
  · exact B2103471
  · exact B2103475
  · exact B2103479
  · exact B2103483
  · exact B2103487
  · exact B2103491
  · exact B2103495
  · exact B2103499
  · exact B2103503
  · exact B2103507
  · exact B2103511
  · exact B2103515
  · exact B2103519
  · exact B2103523
  · exact B2103527
  · exact B2103531
  · exact B2103535
  · exact B2103539
  · exact B2103543
  · exact B2103547
  · exact B2103551
  · exact B2103555
  · exact B2103559
  · exact B2103563
  · exact B2103567
  · exact B2103571
  · exact B2103575
  · exact B2103579
  · exact B2103583
  · exact B2103587
  · exact B2103591
  · exact B2103595
  · exact B2103599
  · exact B2103603
  · exact B2103607
  · exact B2103611
  · exact B2103615
  · exact B2103619
  · exact B2103623
  · exact B2103627
  · exact B2103631
  · exact B2103635
  · exact B2103639
  · exact B2103643
  · exact B2103647
  · exact B2103651
  · exact B2103655
  · exact B2103659
  · exact B2103663
  · exact B2103667
  · exact B2103671
  · exact B2103675
  · exact B2103679
  · exact B2103683
  · exact B2103687
  · exact B2103691
  · exact B2103695
  · exact B2103699
  · exact B2103703
  · exact B2103707
  · exact B2103711
  · exact B2103715
  · exact B2103719
  · exact B2103723
  · exact B2103727
  · exact B2103731
  · exact B2103735
  · exact B2103739
  · exact B2103743
  · exact B2103747
  · exact B2103751
  · exact B2103755
  · exact B2103759
  · exact B2103763
  · exact B2103767
  · exact B2103771
  · exact B2103775
  · exact B2103779
  · exact B2103783
  · exact B2103787
  · exact B2103791
  · exact B2103795
  · exact B2103799
  · exact B2103803
  · exact B2103807
  · exact B2103811
  · exact B2103815
  · exact B2103819
  · exact B2103823
  · exact B2103827
  · exact B2103831
  · exact B2103835
  · exact B2103839
  · exact B2103843
  · exact B2103847
  · exact B2103851
  · exact B2103855
  · exact B2103859
  · exact B2103863
  · exact B2103867
  · exact B2103871
  · exact B2103875
  · exact B2103879
  · exact B2103883
  · exact B2103887
  · exact B2103891
  · exact B2103895
  · exact B2103899
  · exact B2103903
  · exact B2103907
  · exact B2103911
  · exact B2103915
  · exact B2103919
  · exact B2103923
  · exact B2103927
  · exact B2103931
  · exact B2103935
  · exact B2103939
  · exact B2103943
  · exact B2103947
  · exact B2103951
  · exact B2103955
  · exact B2103959
  · exact B2103963
  · exact B2103967
  · exact B2103971
  · exact B2103975
  · exact B2103979
  · exact B2103983
  · exact B2103987
  · exact B2103991
  · exact B2103995
  · exact B2103999
  · exact B2104003
  · exact B2104007
  · exact B2104011
  · exact B2104015
  · exact B2104019
  · exact B2104023
  · exact B2104027
  · exact B2104031
  · exact B2104035
  · exact B2104039
  · exact B2104043
  · exact B2104047
  · exact B2104051
  · exact B2104055
  · exact B2104059
  · exact B2104063
  · exact B2104067
  · exact B2104071
  · exact B2104075
  · exact B2104079
  · exact B2104083
  · exact B2104087
  · exact B2104091
  · exact B2104095
  · exact B2104099
  · exact B2104103
  · exact B2104107
  · exact B2104111
  · exact B2104115
  · exact B2104119
  · exact B2104123
  · exact B2104127
  · exact B2104131
  · exact B2104135
  · exact B2104139
  · exact B2104143
  · exact B2104147
  · exact B2104151
  · exact B2104155
  · exact B2104159
  · exact B2104163
  · exact B2104167
  · exact B2104171
  · exact B2104175
  · exact B2104179
  · exact B2104183
  · exact B2104187
  · exact B2104191
  · exact B2104195
  · exact B2104199
  · exact B2104203
  · exact B2104207
  · exact B2104211
  · exact B2104215
  · exact B2104219
  · exact B2104223
  · exact B2104227
  · exact B2104231
  · exact B2104235
  · exact B2104239
  · exact B2104243
  · exact B2104247
  · exact B2104251
  · exact B2104255
  · exact B2104259
  · exact B2104263
  · exact B2104267
  · exact B2104271
  · exact B2104275
  · exact B2104279
  · exact B2104283
  · exact B2104287
  · exact B2104291
  · exact B2104295
  · exact B2104299
  · exact B2104303
  · exact B2104307
  · exact B2104311
  · exact B2104315
  · exact B2104319
  · exact B2104323
  · exact B2104327
  · exact B2104331
  · exact B2104335
  · exact B2104339
  · exact B2104343
  · exact B2104347
  · exact B2104351
  · exact B2104355
  · exact B2104359
  · exact B2104363
  · exact B2104367
  · exact B2104371
  · exact B2104375
  · exact B2104379
  · exact B2104383
  · exact B2104387
  · exact B2104391
  · exact B2104395
  · exact B2104399
  · exact B2104403
  · exact B2104407
  · exact B2104411
  · exact B2104415
  · exact B2104419
  · exact B2104423
  · exact B2104427
  · exact B2104431
  · exact B2104435
  · exact B2104439
  · exact B2104443
  · exact B2104447
  · exact B2104451
  · exact B2104455
  · exact B2104459
  · exact B2104463
  · exact B2104467
  · exact B2104471
  · exact B2104475
  · exact B2104479
  · exact B2104483
  · exact B2104487
  · exact B2104491
  · exact B2104495
  · exact B2104499
  · exact B2104503
  · exact B2104507
  · exact B2104511
  · exact B2104515
  · exact B2104519
  · exact B2104523
  · exact B2104527
  · exact B2104531
  · exact B2104535
  · exact B2104539
  · exact B2104543
  · exact B2104547
  · exact B2104551
  · exact B2104555
  · exact B2104559
  · exact B2104563
  · exact B2104567
  · exact B2104571
  · exact B2104575
  · exact B2104579
  · exact B2104583
  · exact B2104587
  · exact B2104591
  · exact B2104595
  · exact B2104599
  · exact B2104603
  · exact B2104607
  · exact B2104611
  · exact B2104615
  · exact B2104619
  · exact B2104623
  · exact B2104627
  · exact B2104631
  · exact B2104635
  · exact B2104639
  · exact B2104643
  · exact B2104647
  · exact B2104651
  · exact B2104655
  · exact B2104659
  · exact B2104663
  · exact B2104667
  · exact B2104671
  · exact B2104675
  · exact B2104679
  · exact B2104683
  · exact B2104687
  · exact B2104691
  · exact B2104695
  · exact B2104699
  · exact B2104703
  · exact B2104707
  · exact B2104711
  · exact B2104715
  · exact B2104719
  · exact B2104723
  · exact B2104727
  · exact B2104731
  · exact B2104735
  · exact B2104739
  · exact B2104743
  · exact B2104747
  · exact B2104751
  · exact B2104755
  · exact B2104759
  · exact B2104763
  · exact B2104767
  · exact B2104771
  · exact B2104775
  · exact B2104779
  · exact B2104783
  · exact B2104787
  · exact B2104791
  · exact B2104795
  · exact B2104799
  · exact B2104803
  · exact B2104807
  · exact B2104811
  · exact B2104815
  · exact B2104819
  · exact B2104823
  · exact B2104827
  · exact B2104831
  · exact B2104835
  · exact B2104839
  · exact B2104843
  · exact B2104847
  · exact B2104851
  · exact B2104855
  · exact B2104859
  · exact B2104863
  · exact B2104867
  · exact B2104871
  · exact B2104875
  · exact B2104879
  · exact B2104883
  · exact B2104887
  · exact B2104891
  · exact B2104895
  · exact B2104899
  · exact B2104903
  · exact B2104907
  · exact B2104911
  · exact B2104915
  · exact B2104919
  · exact B2104923
  · exact B2104927
  · exact B2104931
  · exact B2104935
  · exact B2104939
  · exact B2104943
  · exact B2104947
  · exact B2104951
  · exact B2104955
  · exact B2104959
  · exact B2104963
  · exact B2104967
  · exact B2104971
  · exact B2104975
  · exact B2104979
  · exact B2104983
  · exact B2104987
  · exact B2104991
  · exact B2104995
  · exact B2104999
  · exact B2105003
  · exact B2105007
  · exact B2105011
  · exact B2105015
  · exact B2105019
  · exact B2105023
  · exact B2105027
  · exact B2105031
  · exact B2105035
  · exact B2105039
  · exact B2105043
  · exact B2105047
  · exact B2105051
  · exact B2105055
  · exact B2105059
  · exact B2105063
  · exact B2105067
  · exact B2105071
  · exact B2105075
  · exact B2105079
  · exact B2105083
  · exact B2105087
  · exact B2105091
  · exact B2105095
  · exact B2105099
  · exact B2105103
  · exact B2105107
  · exact B2105111
  · exact B2105115
  · exact B2105119
  · exact B2105123
  · exact B2105127
  · exact B2105131
  · exact B2105135
  · exact B2105139
  · exact B2105143
  · exact B2105147
  · exact B2105151
  · exact B2105155
  · exact B2105159
  · exact B2105163
  · exact B2105167
  · exact B2105171
  · exact B2105175
  · exact B2105179
  · exact B2105183
  · exact B2105187
  · exact B2105191
  · exact B2105195
  · exact B2105199
  · exact B2105203
  · exact B2105207
  · exact B2105211
  · exact B2105215
  · exact B2105219
  · exact B2105223
  · exact B2105227
  · exact B2105231
  · exact B2105235
  · exact B2105239
  · exact B2105243
  · exact B2105247
  · exact B2105251
  · exact B2105255
  · exact B2105259
  · exact B2105263
  · exact B2105267
  · exact B2105271
  · exact B2105275
  · exact B2105279
  · exact B2105283
  · exact B2105287
  · exact B2105291
  · exact B2105295
  · exact B2105299
  · exact B2105303
  · exact B2105307
  · exact B2105311
  · exact B2105315
  · exact B2105319
  · exact B2105323
  · exact B2105327
  · exact B2105331
  · exact B2105335
  · exact B2105339
  · exact B2105343
  · exact B2105347
  · exact B2105351
  · exact B2105355
  · exact B2105359
  · exact B2105363
  · exact B2105367
  · exact B2105371
  · exact B2105375
  · exact B2105379
  · exact B2105383
  · exact B2105387
  · exact B2105391
  · exact B2105395
  · exact B2105399
  · exact B2105403
  · exact B2105407
  · exact B2105411
  · exact B2105415
  · exact B2105419
  · exact B2105423
  · exact B2105427
  · exact B2105431
  · exact B2105435
theorem solution (m : ℕ) (hlo : 2103435 ≤ m) (hhi : m ≤ 2105435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 525858 ≤ j := by omega
    have hj2 : j ≤ 526358 := by omega
    have hb : Blo 2103435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
