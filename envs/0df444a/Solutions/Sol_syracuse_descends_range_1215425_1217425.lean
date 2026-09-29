-- Prove2me | solution 1 for syracuse_descends_range_1215425_1217425
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:54.294322+00:00
-- url     : https://prove2.me/submissions/90cc1af8-91aa-451d-8c5e-2de76f2ffadc

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


theorem B1368085 : Blo 1215425 1368085 := bbase (se 6 (by rfl) ⟨32064, by rfl⟩ : syracuseStep 1368085 = 64129) (by norm_num)
theorem B1540129 : Blo 1215425 1540129 := bbase (se 2 (by rfl) ⟨577548, by rfl⟩ : syracuseStep 1540129 = 1155097) (by norm_num)
theorem B10395701 : Blo 1215425 10395701 := bbase (se 5 (by rfl) ⟨487298, by rfl⟩ : syracuseStep 10395701 = 974597) (by norm_num)
theorem B4620341 : Blo 1215425 4620341 := bbase (se 5 (by rfl) ⟨216578, by rfl⟩ : syracuseStep 4620341 = 433157) (by norm_num)
theorem B1368121 : Blo 1215425 1368121 := bbase (se 2 (by rfl) ⟨513045, by rfl⟩ : syracuseStep 1368121 = 1026091) (by norm_num)
theorem B2736197 : Blo 1215425 2736197 := bbase (se 4 (by rfl) ⟨256518, by rfl⟩ : syracuseStep 2736197 = 513037) (by norm_num)
theorem B2744389 : Blo 1215425 2744389 := bbase (se 4 (by rfl) ⟨257286, by rfl⟩ : syracuseStep 2744389 = 514573) (by norm_num)
theorem B1368157 : Blo 1215425 1368157 := bbase (se 3 (by rfl) ⟨256529, by rfl⟩ : syracuseStep 1368157 = 513059) (by norm_num)
theorem B1368193 : Blo 1215425 1368193 := bbase (se 2 (by rfl) ⟨513072, by rfl⟩ : syracuseStep 1368193 = 1026145) (by norm_num)
theorem B1540225 : Blo 1215425 1540225 := bbase (se 2 (by rfl) ⟨577584, by rfl⟩ : syracuseStep 1540225 = 1155169) (by norm_num)
theorem B2310277 : Blo 1215425 2310277 := bbase (se 4 (by rfl) ⟨216588, by rfl⟩ : syracuseStep 2310277 = 433177) (by norm_num)
theorem B2736269 : Blo 1215425 2736269 := bbase (se 3 (by rfl) ⟨513050, by rfl⟩ : syracuseStep 2736269 = 1026101) (by norm_num)
theorem B1368229 : Blo 1215425 1368229 := bbase (se 4 (by rfl) ⟨128271, by rfl⟩ : syracuseStep 1368229 = 256543) (by norm_num)
theorem B3080389 : Blo 1215425 3080389 := bbase (se 4 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 3080389 = 577573) (by norm_num)
theorem B1368265 : Blo 1215425 1368265 := bbase (se 2 (by rfl) ⟨513099, by rfl⟩ : syracuseStep 1368265 = 1026199) (by norm_num)
theorem B2736341 : Blo 1215425 2736341 := bbase (se 7 (by rfl) ⟨32066, by rfl⟩ : syracuseStep 2736341 = 64133) (by norm_num)
theorem B1368301 : Blo 1215425 1368301 := bbase (se 3 (by rfl) ⟨256556, by rfl⟩ : syracuseStep 1368301 = 513113) (by norm_num)
theorem B5193989 : Blo 1215425 5193989 := bbase (se 4 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 5193989 = 973873) (by norm_num)
theorem B1368337 : Blo 1215425 1368337 := bbase (se 2 (by rfl) ⟨513126, by rfl⟩ : syracuseStep 1368337 = 1026253) (by norm_num)
theorem B2736413 : Blo 1215425 2736413 := bbase (se 3 (by rfl) ⟨513077, by rfl⟩ : syracuseStep 2736413 = 1026155) (by norm_num)
theorem B4104485 : Blo 1215425 4104485 := bbase (se 4 (by rfl) ⟨384795, by rfl⟩ : syracuseStep 4104485 = 769591) (by norm_num)
theorem B2310437 : Blo 1215425 2310437 := bbase (se 4 (by rfl) ⟨216603, by rfl⟩ : syracuseStep 2310437 = 433207) (by norm_num)
theorem B1540397 : Blo 1215425 1540397 := bbase (se 3 (by rfl) ⟨288824, by rfl⟩ : syracuseStep 1540397 = 577649) (by norm_num)
theorem B1368373 : Blo 1215425 1368373 := bbase (se 5 (by rfl) ⟨64142, by rfl⟩ : syracuseStep 1368373 = 128285) (by norm_num)
theorem B3080501 : Blo 1215425 3080501 := bbase (se 5 (by rfl) ⟨144398, by rfl⟩ : syracuseStep 3080501 = 288797) (by norm_num)
theorem B13861205 : Blo 1215425 13861205 := bbase (se 10 (by rfl) ⟨20304, by rfl⟩ : syracuseStep 13861205 = 40609) (by norm_num)
theorem B1368409 : Blo 1215425 1368409 := bbase (se 2 (by rfl) ⟨513153, by rfl⟩ : syracuseStep 1368409 = 1026307) (by norm_num)
theorem B2736485 : Blo 1215425 2736485 := bbase (se 4 (by rfl) ⟨256545, by rfl⟩ : syracuseStep 2736485 = 513091) (by norm_num)
theorem B1540453 : Blo 1215425 1540453 := bbase (se 4 (by rfl) ⟨144417, by rfl⟩ : syracuseStep 1540453 = 288835) (by norm_num)
theorem B1368445 : Blo 1215425 1368445 := bbase (se 3 (by rfl) ⟨256583, by rfl⟩ : syracuseStep 1368445 = 513167) (by norm_num)
theorem B1368481 : Blo 1215425 1368481 := bbase (se 2 (by rfl) ⟨513180, by rfl⟩ : syracuseStep 1368481 = 1026361) (by norm_num)
theorem B2597285 : Blo 1215425 2597285 := bbase (se 4 (by rfl) ⟨243495, by rfl⟩ : syracuseStep 2597285 = 486991) (by norm_num)
theorem B2736557 : Blo 1215425 2736557 := bbase (se 3 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 2736557 = 1026209) (by norm_num)
theorem B2310581 : Blo 1215425 2310581 := bbase (se 5 (by rfl) ⟨108308, by rfl⟩ : syracuseStep 2310581 = 216617) (by norm_num)
theorem B1368517 : Blo 1215425 1368517 := bbase (se 4 (by rfl) ⟨128298, by rfl⟩ : syracuseStep 1368517 = 256597) (by norm_num)
theorem B1540549 : Blo 1215425 1540549 := bbase (se 4 (by rfl) ⟨144426, by rfl⟩ : syracuseStep 1540549 = 288853) (by norm_num)
theorem B1368553 : Blo 1215425 1368553 := bbase (se 2 (by rfl) ⟨513207, by rfl⟩ : syracuseStep 1368553 = 1026415) (by norm_num)
theorem B2736629 : Blo 1215425 2736629 := bbase (se 5 (by rfl) ⟨128279, by rfl⟩ : syracuseStep 2736629 = 256559) (by norm_num)
theorem B3080693 : Blo 1215425 3080693 := bbase (se 5 (by rfl) ⟨144407, by rfl⟩ : syracuseStep 3080693 = 288815) (by norm_num)
theorem B1368589 : Blo 1215425 1368589 := bbase (se 3 (by rfl) ⟨256610, by rfl⟩ : syracuseStep 1368589 = 513221) (by norm_num)
theorem B1368625 : Blo 1215425 1368625 := bbase (se 2 (by rfl) ⟨513234, by rfl⟩ : syracuseStep 1368625 = 1026469) (by norm_num)
theorem B2736701 : Blo 1215425 2736701 := bbase (se 3 (by rfl) ⟨513131, by rfl⟩ : syracuseStep 2736701 = 1026263) (by norm_num)
theorem B1368661 : Blo 1215425 1368661 := bbase (se 8 (by rfl) ⟨8019, by rfl⟩ : syracuseStep 1368661 = 16039) (by norm_num)
theorem B1540721 : Blo 1215425 1540721 := bbase (se 2 (by rfl) ⟨577770, by rfl⟩ : syracuseStep 1540721 = 1155541) (by norm_num)
theorem B1368697 : Blo 1215425 1368697 := bbase (se 2 (by rfl) ⟨513261, by rfl⟩ : syracuseStep 1368697 = 1026523) (by norm_num)
theorem B2736773 : Blo 1215425 2736773 := bbase (se 4 (by rfl) ⟨256572, by rfl⟩ : syracuseStep 2736773 = 513145) (by norm_num)
theorem B9355925 : Blo 1215425 9355925 := bbase (se 6 (by rfl) ⟨219279, by rfl⟩ : syracuseStep 9355925 = 438559) (by norm_num)
theorem B1368733 : Blo 1215425 1368733 := bbase (se 3 (by rfl) ⟨256637, by rfl⟩ : syracuseStep 1368733 = 513275) (by norm_num)
theorem B1540777 : Blo 1215425 1540777 := bbase (se 2 (by rfl) ⟨577791, by rfl⟩ : syracuseStep 1540777 = 1155583) (by norm_num)
theorem B1368769 : Blo 1215425 1368769 := bbase (se 2 (by rfl) ⟨513288, by rfl⟩ : syracuseStep 1368769 = 1026577) (by norm_num)
theorem B3949253 : Blo 1215425 3949253 := bbase (se 4 (by rfl) ⟨370242, by rfl⟩ : syracuseStep 3949253 = 740485) (by norm_num)
theorem B2736845 : Blo 1215425 2736845 := bbase (se 3 (by rfl) ⟨513158, by rfl⟩ : syracuseStep 2736845 = 1026317) (by norm_num)
theorem B4104917 : Blo 1215425 4104917 := bbase (se 7 (by rfl) ⟨48104, by rfl⟩ : syracuseStep 4104917 = 96209) (by norm_num)
theorem B2310869 : Blo 1215425 2310869 := bbase (se 7 (by rfl) ⟨27080, by rfl⟩ : syracuseStep 2310869 = 54161) (by norm_num)
theorem B1368805 : Blo 1215425 1368805 := bbase (se 4 (by rfl) ⟨128325, by rfl⟩ : syracuseStep 1368805 = 256651) (by norm_num)
theorem B1368841 : Blo 1215425 1368841 := bbase (se 2 (by rfl) ⟨513315, by rfl⟩ : syracuseStep 1368841 = 1026631) (by norm_num)
theorem B2736917 : Blo 1215425 2736917 := bbase (se 6 (by rfl) ⟨64146, by rfl⟩ : syracuseStep 2736917 = 128293) (by norm_num)
theorem B17539861 : Blo 1215425 17539861 := bbase (se 6 (by rfl) ⟨411090, by rfl⟩ : syracuseStep 17539861 = 822181) (by norm_num)
theorem B1368877 : Blo 1215425 1368877 := bbase (se 3 (by rfl) ⟨256664, by rfl⟩ : syracuseStep 1368877 = 513329) (by norm_num)
theorem B3081037 : Blo 1215425 3081037 := bbase (se 3 (by rfl) ⟨577694, by rfl⟩ : syracuseStep 3081037 = 1155389) (by norm_num)
theorem B1368913 : Blo 1215425 1368913 := bbase (se 2 (by rfl) ⟨513342, by rfl⟩ : syracuseStep 1368913 = 1026685) (by norm_num)
theorem B2736989 : Blo 1215425 2736989 := bbase (se 3 (by rfl) ⟨513185, by rfl⟩ : syracuseStep 2736989 = 1026371) (by norm_num)
theorem B2311021 : Blo 1215425 2311021 := bbase (se 3 (by rfl) ⟨433316, by rfl⟩ : syracuseStep 2311021 = 866633) (by norm_num)
theorem B1368949 : Blo 1215425 1368949 := bbase (se 5 (by rfl) ⟨64169, by rfl⟩ : syracuseStep 1368949 = 128339) (by norm_num)
theorem B1368985 : Blo 1215425 1368985 := bbase (se 2 (by rfl) ⟨513369, by rfl⟩ : syracuseStep 1368985 = 1026739) (by norm_num)
theorem B2737061 : Blo 1215425 2737061 := bbase (se 4 (by rfl) ⟨256599, by rfl⟩ : syracuseStep 2737061 = 513199) (by norm_num)
theorem B1369021 : Blo 1215425 1369021 := bbase (se 3 (by rfl) ⟨256691, by rfl⟩ : syracuseStep 1369021 = 513383) (by norm_num)
theorem B3081149 : Blo 1215425 3081149 := bbase (se 3 (by rfl) ⟨577715, by rfl⟩ : syracuseStep 3081149 = 1155431) (by norm_num)
theorem B1369057 : Blo 1215425 1369057 := bbase (se 2 (by rfl) ⟨513396, by rfl⟩ : syracuseStep 1369057 = 1026793) (by norm_num)
theorem B2737133 : Blo 1215425 2737133 := bbase (se 3 (by rfl) ⟨513212, by rfl⟩ : syracuseStep 2737133 = 1026425) (by norm_num)
theorem B1369093 : Blo 1215425 1369093 := bbase (se 4 (by rfl) ⟨128352, by rfl⟩ : syracuseStep 1369093 = 256705) (by norm_num)
theorem B2221085 : Blo 1215425 2221085 := bbase (se 3 (by rfl) ⟨416453, by rfl⟩ : syracuseStep 2221085 = 832907) (by norm_num)
theorem B1369129 : Blo 1215425 1369129 := bbase (se 2 (by rfl) ⟨513423, by rfl⟩ : syracuseStep 1369129 = 1026847) (by norm_num)
theorem B2737205 : Blo 1215425 2737205 := bbase (se 5 (by rfl) ⟨128306, by rfl⟩ : syracuseStep 2737205 = 256613) (by norm_num)
theorem B1369165 : Blo 1215425 1369165 := bbase (se 3 (by rfl) ⟨256718, by rfl⟩ : syracuseStep 1369165 = 513437) (by norm_num)
theorem B1369201 : Blo 1215425 1369201 := bbase (se 2 (by rfl) ⟨513450, by rfl⟩ : syracuseStep 1369201 = 1026901) (by norm_num)
theorem B2737277 : Blo 1215425 2737277 := bbase (se 3 (by rfl) ⟨513239, by rfl⟩ : syracuseStep 2737277 = 1026479) (by norm_num)
theorem B3081341 : Blo 1215425 3081341 := bbase (se 3 (by rfl) ⟨577751, by rfl⟩ : syracuseStep 3081341 = 1155503) (by norm_num)
theorem B4105349 : Blo 1215425 4105349 := bbase (se 4 (by rfl) ⟨384876, by rfl⟩ : syracuseStep 4105349 = 769753) (by norm_num)
theorem B1369237 : Blo 1215425 1369237 := bbase (se 6 (by rfl) ⟨32091, by rfl⟩ : syracuseStep 1369237 = 64183) (by norm_num)
theorem B1975477 : Blo 1215425 1975477 := bbase (se 5 (by rfl) ⟨92600, by rfl⟩ : syracuseStep 1975477 = 185201) (by norm_num)
theorem B8774837 : Blo 1215425 8774837 := bbase (se 5 (by rfl) ⟨411320, by rfl⟩ : syracuseStep 8774837 = 822641) (by norm_num)
theorem B1369273 : Blo 1215425 1369273 := bbase (se 2 (by rfl) ⟨513477, by rfl⟩ : syracuseStep 1369273 = 1026955) (by norm_num)
theorem B2737349 : Blo 1215425 2737349 := bbase (se 4 (by rfl) ⟨256626, by rfl⟩ : syracuseStep 2737349 = 513253) (by norm_num)
theorem B1369309 : Blo 1215425 1369309 := bbase (se 3 (by rfl) ⟨256745, by rfl⟩ : syracuseStep 1369309 = 513491) (by norm_num)
theorem B1369345 : Blo 1215425 1369345 := bbase (se 2 (by rfl) ⟨513504, by rfl⟩ : syracuseStep 1369345 = 1027009) (by norm_num)
theorem B2598149 : Blo 1215425 2598149 := bbase (se 4 (by rfl) ⟨243576, by rfl⟩ : syracuseStep 2598149 = 487153) (by norm_num)
theorem B6161669 : Blo 1215425 6161669 := bbase (se 4 (by rfl) ⟨577656, by rfl⟩ : syracuseStep 6161669 = 1155313) (by norm_num)
theorem B2737421 : Blo 1215425 2737421 := bbase (se 3 (by rfl) ⟨513266, by rfl⟩ : syracuseStep 2737421 = 1026533) (by norm_num)
theorem B1369381 : Blo 1215425 1369381 := bbase (se 4 (by rfl) ⟨128379, by rfl⟩ : syracuseStep 1369381 = 256759) (by norm_num)
theorem B1369417 : Blo 1215425 1369417 := bbase (se 2 (by rfl) ⟨513531, by rfl⟩ : syracuseStep 1369417 = 1027063) (by norm_num)
theorem B2737493 : Blo 1215425 2737493 := bbase (se 12 (by rfl) ⟨1002, by rfl⟩ : syracuseStep 2737493 = 2005) (by norm_num)
theorem B1369453 : Blo 1215425 1369453 := bbase (se 3 (by rfl) ⟨256772, by rfl⟩ : syracuseStep 1369453 = 513545) (by norm_num)
theorem B1369489 : Blo 1215425 1369489 := bbase (se 2 (by rfl) ⟨513558, by rfl⟩ : syracuseStep 1369489 = 1027117) (by norm_num)
theorem B2598293 : Blo 1215425 2598293 := bbase (se 6 (by rfl) ⟨60897, by rfl⟩ : syracuseStep 2598293 = 121795) (by norm_num)
theorem B2737565 : Blo 1215425 2737565 := bbase (se 3 (by rfl) ⟨513293, by rfl⟩ : syracuseStep 2737565 = 1026587) (by norm_num)
theorem B1369525 : Blo 1215425 1369525 := bbase (se 5 (by rfl) ⟨64196, by rfl⟩ : syracuseStep 1369525 = 128393) (by norm_num)
theorem B6931925 : Blo 1215425 6931925 := bbase (se 7 (by rfl) ⟨81233, by rfl⟩ : syracuseStep 6931925 = 162467) (by norm_num)
theorem B1369561 : Blo 1215425 1369561 := bbase (se 2 (by rfl) ⟨513585, by rfl⟩ : syracuseStep 1369561 = 1027171) (by norm_num)
theorem B2737637 : Blo 1215425 2737637 := bbase (se 4 (by rfl) ⟨256653, by rfl⟩ : syracuseStep 2737637 = 513307) (by norm_num)
theorem B1754605 : Blo 1215425 1754605 := bbase (se 3 (by rfl) ⟨328988, by rfl⟩ : syracuseStep 1754605 = 657977) (by norm_num)
theorem B1369597 : Blo 1215425 1369597 := bbase (se 3 (by rfl) ⟨256799, by rfl⟩ : syracuseStep 1369597 = 513599) (by norm_num)
theorem B5842469 : Blo 1215425 5842469 := bbase (se 4 (by rfl) ⟨547731, by rfl⟩ : syracuseStep 5842469 = 1095463) (by norm_num)
theorem B2737709 : Blo 1215425 2737709 := bbase (se 3 (by rfl) ⟨513320, by rfl⟩ : syracuseStep 2737709 = 1026641) (by norm_num)
theorem B4105781 : Blo 1215425 4105781 := bbase (se 5 (by rfl) ⟨192458, by rfl⟩ : syracuseStep 4105781 = 384917) (by norm_num)
theorem B7792213 : Blo 1215425 7792213 := bbase (se 8 (by rfl) ⟨45657, by rfl⟩ : syracuseStep 7792213 = 91315) (by norm_num)
theorem B2737781 : Blo 1215425 2737781 := bbase (se 5 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 2737781 = 256667) (by norm_num)
theorem B1386113 : Blo 1215425 1386113 := bbase (se 2 (by rfl) ⟨519792, by rfl⟩ : syracuseStep 1386113 = 1039585) (by norm_num)
theorem B9242261 : Blo 1215425 9242261 := bbase (se 6 (by rfl) ⟨216615, by rfl⟩ : syracuseStep 9242261 = 433231) (by norm_num)
theorem B6153893 : Blo 1215425 6153893 := bbase (se 4 (by rfl) ⟨576927, by rfl⟩ : syracuseStep 6153893 = 1153855) (by norm_num)
theorem B2737853 : Blo 1215425 2737853 := bbase (se 3 (by rfl) ⟨513347, by rfl⟩ : syracuseStep 2737853 = 1026695) (by norm_num)
theorem B4933349 : Blo 1215425 4933349 := bbase (se 4 (by rfl) ⟨462501, by rfl⟩ : syracuseStep 4933349 = 925003) (by norm_num)
theorem B2737925 : Blo 1215425 2737925 := bbase (se 4 (by rfl) ⟨256680, by rfl⟩ : syracuseStep 2737925 = 513361) (by norm_num)
theorem B2737997 : Blo 1215425 2737997 := bbase (se 3 (by rfl) ⟨513374, by rfl⟩ : syracuseStep 2737997 = 1026749) (by norm_num)
theorem B11700085 : Blo 1215425 11700085 := bbase (se 5 (by rfl) ⟨548441, by rfl⟩ : syracuseStep 11700085 = 1096883) (by norm_num)
theorem B2738069 : Blo 1215425 2738069 := bbase (se 6 (by rfl) ⟨64173, by rfl⟩ : syracuseStep 2738069 = 128347) (by norm_num)
theorem B2631613 : Blo 1215425 2631613 := bbase (se 3 (by rfl) ⟨493427, by rfl⟩ : syracuseStep 2631613 = 986855) (by norm_num)
theorem B2738141 : Blo 1215425 2738141 := bbase (se 3 (by rfl) ⟨513401, by rfl⟩ : syracuseStep 2738141 = 1026803) (by norm_num)
theorem B4106213 : Blo 1215425 4106213 := bbase (se 4 (by rfl) ⟨384957, by rfl⟩ : syracuseStep 4106213 = 769915) (by norm_num)
theorem B5195765 : Blo 1215425 5195765 := bbase (se 5 (by rfl) ⟨243551, by rfl⟩ : syracuseStep 5195765 = 487103) (by norm_num)
theorem B2738213 : Blo 1215425 2738213 := bbase (se 4 (by rfl) ⟨256707, by rfl⟩ : syracuseStep 2738213 = 513415) (by norm_num)
theorem B9234485 : Blo 1215425 9234485 := bbase (se 5 (by rfl) ⟨432866, by rfl⟩ : syracuseStep 9234485 = 865733) (by norm_num)
theorem B2738285 : Blo 1215425 2738285 := bbase (se 3 (by rfl) ⟨513428, by rfl⟩ : syracuseStep 2738285 = 1026857) (by norm_num)
theorem B2599037 : Blo 1215425 2599037 := bbase (se 3 (by rfl) ⟨487319, by rfl⟩ : syracuseStep 2599037 = 974639) (by norm_num)
theorem B2738357 : Blo 1215425 2738357 := bbase (se 5 (by rfl) ⟨128360, by rfl⟩ : syracuseStep 2738357 = 256721) (by norm_num)
theorem B1730749 : Blo 1215425 1730749 := bbase (se 3 (by rfl) ⟨324515, by rfl⟩ : syracuseStep 1730749 = 649031) (by norm_num)
theorem B2738429 : Blo 1215425 2738429 := bbase (se 3 (by rfl) ⟨513455, by rfl⟩ : syracuseStep 2738429 = 1026911) (by norm_num)
theorem B2738501 : Blo 1215425 2738501 := bbase (se 4 (by rfl) ⟨256734, by rfl⟩ : syracuseStep 2738501 = 513469) (by norm_num)
theorem B2107765 : Blo 1215425 2107765 := bbase (se 5 (by rfl) ⟨98801, by rfl⟩ : syracuseStep 2107765 = 197603) (by norm_num)
theorem B4385141 : Blo 1215425 4385141 := bbase (se 5 (by rfl) ⟨205553, by rfl⟩ : syracuseStep 4385141 = 411107) (by norm_num)
theorem B1755517 : Blo 1215425 1755517 := bbase (se 3 (by rfl) ⟨329159, by rfl⟩ : syracuseStep 1755517 = 658319) (by norm_num)
theorem B2738573 : Blo 1215425 2738573 := bbase (se 3 (by rfl) ⟨513482, by rfl⟩ : syracuseStep 2738573 = 1026965) (by norm_num)
theorem B1730965 : Blo 1215425 1730965 := bbase (se 6 (by rfl) ⟨40569, by rfl⟩ : syracuseStep 1730965 = 81139) (by norm_num)
theorem B4106645 : Blo 1215425 4106645 := bbase (se 6 (by rfl) ⟨96249, by rfl⟩ : syracuseStep 4106645 = 192499) (by norm_num)
theorem B2738645 : Blo 1215425 2738645 := bbase (se 7 (by rfl) ⟨32093, by rfl⟩ : syracuseStep 2738645 = 64187) (by norm_num)
theorem B3287557 : Blo 1215425 3287557 := bbase (se 4 (by rfl) ⟨308208, by rfl⟩ : syracuseStep 3287557 = 616417) (by norm_num)
theorem B6162965 : Blo 1215425 6162965 := bbase (se 6 (by rfl) ⟨144444, by rfl⟩ : syracuseStep 6162965 = 288889) (by norm_num)
theorem B2738717 : Blo 1215425 2738717 := bbase (se 3 (by rfl) ⟨513509, by rfl⟩ : syracuseStep 2738717 = 1027019) (by norm_num)
theorem B2738789 : Blo 1215425 2738789 := bbase (se 4 (by rfl) ⟨256761, by rfl⟩ : syracuseStep 2738789 = 513523) (by norm_num)
theorem B2738861 : Blo 1215425 2738861 := bbase (se 3 (by rfl) ⟨513536, by rfl⟩ : syracuseStep 2738861 = 1027073) (by norm_num)
theorem B2738933 : Blo 1215425 2738933 := bbase (se 5 (by rfl) ⟨128387, by rfl⟩ : syracuseStep 2738933 = 256775) (by norm_num)
theorem B1731341 : Blo 1215425 1731341 := bbase (se 3 (by rfl) ⟨324626, by rfl⟩ : syracuseStep 1731341 = 649253) (by norm_num)
theorem B4385573 : Blo 1215425 4385573 := bbase (se 4 (by rfl) ⟨411147, by rfl⟩ : syracuseStep 4385573 = 822295) (by norm_num)
theorem B1559341 : Blo 1215425 1559341 := bbase (se 3 (by rfl) ⟨292376, by rfl⟩ : syracuseStep 1559341 = 584753) (by norm_num)
theorem B4614965 : Blo 1215425 4614965 := bbase (se 5 (by rfl) ⟨216326, by rfl⟩ : syracuseStep 4614965 = 432653) (by norm_num)
theorem B2739005 : Blo 1215425 2739005 := bbase (se 3 (by rfl) ⟨513563, by rfl⟩ : syracuseStep 2739005 = 1027127) (by norm_num)
theorem B4107077 : Blo 1215425 4107077 := bbase (se 4 (by rfl) ⟨385038, by rfl⟩ : syracuseStep 4107077 = 770077) (by norm_num)
theorem B2599789 : Blo 1215425 2599789 := bbase (se 3 (by rfl) ⟨487460, by rfl⟩ : syracuseStep 2599789 = 974921) (by norm_num)
theorem B2739077 : Blo 1215425 2739077 := bbase (se 4 (by rfl) ⟨256788, by rfl⟩ : syracuseStep 2739077 = 513577) (by norm_num)
theorem B6155189 : Blo 1215425 6155189 := bbase (se 5 (by rfl) ⟨288524, by rfl⟩ : syracuseStep 6155189 = 577049) (by norm_num)
theorem B1559485 : Blo 1215425 1559485 := bbase (se 3 (by rfl) ⟨292403, by rfl⟩ : syracuseStep 1559485 = 584807) (by norm_num)
theorem B2739149 : Blo 1215425 2739149 := bbase (se 3 (by rfl) ⟨513590, by rfl⟩ : syracuseStep 2739149 = 1027181) (by norm_num)
theorem B5196757 : Blo 1215425 5196757 := bbase (se 7 (by rfl) ⟨60899, by rfl⟩ : syracuseStep 5196757 = 121799) (by norm_num)
theorem B2599933 : Blo 1215425 2599933 := bbase (se 3 (by rfl) ⟨487487, by rfl⟩ : syracuseStep 2599933 = 974975) (by norm_num)
theorem B2051149 : Blo 1215425 2051149 := bbase (se 3 (by rfl) ⟨384590, by rfl⟩ : syracuseStep 2051149 = 769181) (by norm_num)
theorem B5549141 : Blo 1215425 5549141 := bbase (se 8 (by rfl) ⟨32514, by rfl⟩ : syracuseStep 5549141 = 65029) (by norm_num)
theorem B1559669 : Blo 1215425 1559669 := bbase (se 5 (by rfl) ⟨73109, by rfl⟩ : syracuseStep 1559669 = 146219) (by norm_num)
theorem B2051237 : Blo 1215425 2051237 := bbase (se 4 (by rfl) ⟨192303, by rfl⟩ : syracuseStep 2051237 = 384607) (by norm_num)
theorem B4107509 : Blo 1215425 4107509 := bbase (se 5 (by rfl) ⟨192539, by rfl⟩ : syracuseStep 4107509 = 385079) (by norm_num)
theorem B1461497 : Blo 1215425 1461497 := bbase (se 2 (by rfl) ⟨548061, by rfl⟩ : syracuseStep 1461497 = 1096123) (by norm_num)
theorem B1461521 : Blo 1215425 1461521 := bbase (se 2 (by rfl) ⟨548070, by rfl⟩ : syracuseStep 1461521 = 1096141) (by norm_num)
theorem B2051365 : Blo 1215425 2051365 := bbase (se 4 (by rfl) ⟨192315, by rfl⟩ : syracuseStep 2051365 = 384631) (by norm_num)
theorem B2190653 : Blo 1215425 2190653 := bbase (se 3 (by rfl) ⟨410747, by rfl⟩ : syracuseStep 2190653 = 821495) (by norm_num)
theorem B6663509 : Blo 1215425 6663509 := bbase (se 11 (by rfl) ⟨4880, by rfl⟩ : syracuseStep 6663509 = 9761) (by norm_num)
theorem B52596053 : Blo 1215425 52596053 := bbase (se 11 (by rfl) ⟨38522, by rfl⟩ : syracuseStep 52596053 = 77045) (by norm_num)
theorem B2051453 : Blo 1215425 2051453 := bbase (se 3 (by rfl) ⟨384647, by rfl⟩ : syracuseStep 2051453 = 769295) (by norm_num)
theorem B5336549 : Blo 1215425 5336549 := bbase (se 4 (by rfl) ⟨500301, by rfl⟩ : syracuseStep 5336549 = 1000603) (by norm_num)
theorem B2051581 : Blo 1215425 2051581 := bbase (se 3 (by rfl) ⟨384671, by rfl⟩ : syracuseStep 2051581 = 769343) (by norm_num)
theorem B1297981 : Blo 1215425 1297981 := bbase (se 3 (by rfl) ⟨243371, by rfl⟩ : syracuseStep 1297981 = 486743) (by norm_num)
theorem B1461829 : Blo 1215425 1461829 := bbase (se 4 (by rfl) ⟨137046, by rfl⟩ : syracuseStep 1461829 = 274093) (by norm_num)
theorem B2051669 : Blo 1215425 2051669 := bbase (se 8 (by rfl) ⟨12021, by rfl⟩ : syracuseStep 2051669 = 24043) (by norm_num)
theorem B1298053 : Blo 1215425 1298053 := bbase (se 4 (by rfl) ⟨121692, by rfl⟩ : syracuseStep 1298053 = 243385) (by norm_num)
theorem B4107941 : Blo 1215425 4107941 := bbase (se 4 (by rfl) ⟨385119, by rfl⟩ : syracuseStep 4107941 = 770239) (by norm_num)
theorem B1560265 : Blo 1215425 1560265 := bbase (se 2 (by rfl) ⟨585099, by rfl⟩ : syracuseStep 1560265 = 1170199) (by norm_num)
theorem B2051797 : Blo 1215425 2051797 := bbase (se 7 (by rfl) ⟨24044, by rfl⟩ : syracuseStep 2051797 = 48089) (by norm_num)
theorem B1462001 : Blo 1215425 1462001 := bbase (se 2 (by rfl) ⟨548250, by rfl⟩ : syracuseStep 1462001 = 1096501) (by norm_num)
theorem B2051885 : Blo 1215425 2051885 := bbase (se 3 (by rfl) ⟨384728, by rfl⟩ : syracuseStep 2051885 = 769457) (by norm_num)
theorem B1232705 : Blo 1215425 1232705 := bbase (se 2 (by rfl) ⟨462264, by rfl⟩ : syracuseStep 1232705 = 924529) (by norm_num)
theorem B1462117 : Blo 1215425 1462117 := bbase (se 4 (by rfl) ⟨137073, by rfl⟩ : syracuseStep 1462117 = 274147) (by norm_num)
theorem B2052013 : Blo 1215425 2052013 := bbase (se 3 (by rfl) ⟨384752, by rfl⟩ : syracuseStep 2052013 = 769505) (by norm_num)
theorem B1462213 : Blo 1215425 1462213 := bbase (se 4 (by rfl) ⟨137082, by rfl⟩ : syracuseStep 1462213 = 274165) (by norm_num)
theorem B4616149 : Blo 1215425 4616149 := bbase (se 7 (by rfl) ⟨54095, by rfl⟩ : syracuseStep 4616149 = 108191) (by norm_num)
theorem B3289061 : Blo 1215425 3289061 := bbase (se 4 (by rfl) ⟨308349, by rfl⟩ : syracuseStep 3289061 = 616699) (by norm_num)
theorem B1298425 : Blo 1215425 1298425 := bbase (se 2 (by rfl) ⟨486909, by rfl⟩ : syracuseStep 1298425 = 973819) (by norm_num)
theorem B2052101 : Blo 1215425 2052101 := bbase (se 4 (by rfl) ⟨192384, by rfl⟩ : syracuseStep 2052101 = 384769) (by norm_num)
theorem B21082133 : Blo 1215425 21082133 := bbase (se 6 (by rfl) ⟨494112, by rfl⟩ : syracuseStep 21082133 = 988225) (by norm_num)
theorem B1462357 : Blo 1215425 1462357 := bbase (se 8 (by rfl) ⟨8568, by rfl⟩ : syracuseStep 1462357 = 17137) (by norm_num)
theorem B4108373 : Blo 1215425 4108373 := bbase (se 8 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 4108373 = 48145) (by norm_num)
theorem B2052229 : Blo 1215425 2052229 := bbase (se 4 (by rfl) ⟨192396, by rfl⟩ : syracuseStep 2052229 = 384793) (by norm_num)
theorem B1732765 : Blo 1215425 1732765 := bbase (se 3 (by rfl) ⟨324893, by rfl⟩ : syracuseStep 1732765 = 649787) (by norm_num)
theorem B1249457 : Blo 1215425 1249457 := bbase (se 2 (by rfl) ⟨468546, by rfl⟩ : syracuseStep 1249457 = 937093) (by norm_num)
theorem B6156485 : Blo 1215425 6156485 := bbase (se 4 (by rfl) ⟨577170, by rfl⟩ : syracuseStep 6156485 = 1154341) (by norm_num)
theorem B2052317 : Blo 1215425 2052317 := bbase (se 3 (by rfl) ⟨384809, by rfl⟩ : syracuseStep 2052317 = 769619) (by norm_num)
theorem B4616453 : Blo 1215425 4616453 := bbase (se 4 (by rfl) ⟨432792, by rfl⟩ : syracuseStep 4616453 = 865585) (by norm_num)
theorem B3461429 : Blo 1215425 3461429 := bbase (se 5 (by rfl) ⟨162254, by rfl⟩ : syracuseStep 3461429 = 324509) (by norm_num)
theorem B2052445 : Blo 1215425 2052445 := bbase (se 3 (by rfl) ⟨384833, by rfl⟩ : syracuseStep 2052445 = 769667) (by norm_num)
theorem B1298801 : Blo 1215425 1298801 := bbase (se 2 (by rfl) ⟨487050, by rfl⟩ : syracuseStep 1298801 = 974101) (by norm_num)
theorem B7795061 : Blo 1215425 7795061 := bbase (se 5 (by rfl) ⟨365393, by rfl⟩ : syracuseStep 7795061 = 730787) (by norm_num)
theorem B3895685 : Blo 1215425 3895685 := bbase (se 4 (by rfl) ⟨365220, by rfl⟩ : syracuseStep 3895685 = 730441) (by norm_num)
theorem B1823141 : Blo 1215425 1823141 := bbase (se 4 (by rfl) ⟨170919, by rfl⟩ : syracuseStep 1823141 = 341839) (by norm_num)
theorem B2052533 : Blo 1215425 2052533 := bbase (se 5 (by rfl) ⟨96212, by rfl⟩ : syracuseStep 2052533 = 192425) (by norm_num)
theorem B1298873 : Blo 1215425 1298873 := bbase (se 2 (by rfl) ⟨487077, by rfl⟩ : syracuseStep 1298873 = 974155) (by norm_num)
theorem B1823165 : Blo 1215425 1823165 := bbase (se 3 (by rfl) ⟨341843, by rfl⟩ : syracuseStep 1823165 = 683687) (by norm_num)
theorem B1266121 : Blo 1215425 1266121 := bbase (se 2 (by rfl) ⟨474795, by rfl⟩ : syracuseStep 1266121 = 949591) (by norm_num)
theorem B1233353 : Blo 1215425 1233353 := bbase (se 2 (by rfl) ⟨462507, by rfl⟩ : syracuseStep 1233353 = 925015) (by norm_num)
theorem B1823189 : Blo 1215425 1823189 := bbase (se 7 (by rfl) ⟨21365, by rfl⟩ : syracuseStep 1823189 = 42731) (by norm_num)
theorem B1823213 : Blo 1215425 1823213 := bbase (se 3 (by rfl) ⟨341852, by rfl⟩ : syracuseStep 1823213 = 683705) (by norm_num)
theorem B3076613 : Blo 1215425 3076613 := bbase (se 4 (by rfl) ⟨288432, by rfl⟩ : syracuseStep 3076613 = 576865) (by norm_num)
theorem B1823237 : Blo 1215425 1823237 := bbase (se 4 (by rfl) ⟨170928, by rfl⟩ : syracuseStep 1823237 = 341857) (by norm_num)
theorem B4682245 : Blo 1215425 4682245 := bbase (se 4 (by rfl) ⟨438960, by rfl⟩ : syracuseStep 4682245 = 877921) (by norm_num)
theorem B4108805 : Blo 1215425 4108805 := bbase (se 4 (by rfl) ⟨385200, by rfl⟩ : syracuseStep 4108805 = 770401) (by norm_num)
theorem B1823261 : Blo 1215425 1823261 := bbase (se 3 (by rfl) ⟨341861, by rfl⟩ : syracuseStep 1823261 = 683723) (by norm_num)
theorem B1823285 : Blo 1215425 1823285 := bbase (se 5 (by rfl) ⟨85466, by rfl⟩ : syracuseStep 1823285 = 170933) (by norm_num)
theorem B2052661 : Blo 1215425 2052661 := bbase (se 5 (by rfl) ⟨96218, by rfl⟩ : syracuseStep 2052661 = 192437) (by norm_num)
theorem B1823309 : Blo 1215425 1823309 := bbase (se 3 (by rfl) ⟨341870, by rfl⟩ : syracuseStep 1823309 = 683741) (by norm_num)
theorem B1823333 : Blo 1215425 1823333 := bbase (se 4 (by rfl) ⟨170937, by rfl⟩ : syracuseStep 1823333 = 341875) (by norm_num)
theorem B1561189 : Blo 1215425 1561189 := bbase (se 4 (by rfl) ⟨146361, by rfl⟩ : syracuseStep 1561189 = 292723) (by norm_num)
theorem B1299061 : Blo 1215425 1299061 := bbase (se 5 (by rfl) ⟨60893, by rfl⟩ : syracuseStep 1299061 = 121787) (by norm_num)
theorem B1823357 : Blo 1215425 1823357 := bbase (se 3 (by rfl) ⟨341879, by rfl⟩ : syracuseStep 1823357 = 683759) (by norm_num)
theorem B2052749 : Blo 1215425 2052749 := bbase (se 3 (by rfl) ⟨384890, by rfl⟩ : syracuseStep 2052749 = 769781) (by norm_num)
theorem B1249933 : Blo 1215425 1249933 := bbase (se 3 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 1249933 = 468725) (by norm_num)
theorem B1823381 : Blo 1215425 1823381 := bbase (se 6 (by rfl) ⟨42735, by rfl⟩ : syracuseStep 1823381 = 85471) (by norm_num)
theorem B1823405 : Blo 1215425 1823405 := bbase (se 3 (by rfl) ⟨341888, by rfl⟩ : syracuseStep 1823405 = 683777) (by norm_num)
theorem B3076805 : Blo 1215425 3076805 := bbase (se 4 (by rfl) ⟨288450, by rfl⟩ : syracuseStep 3076805 = 576901) (by norm_num)
theorem B1823429 : Blo 1215425 1823429 := bbase (se 4 (by rfl) ⟨170946, by rfl⟩ : syracuseStep 1823429 = 341893) (by norm_num)
theorem B1823453 : Blo 1215425 1823453 := bbase (se 3 (by rfl) ⟨341897, by rfl⟩ : syracuseStep 1823453 = 683795) (by norm_num)
theorem B2921197 : Blo 1215425 2921197 := bbase (se 3 (by rfl) ⟨547724, by rfl⟩ : syracuseStep 2921197 = 1095449) (by norm_num)
theorem B1733357 : Blo 1215425 1733357 := bbase (se 3 (by rfl) ⟨325004, by rfl⟩ : syracuseStep 1733357 = 650009) (by norm_num)
theorem B1823477 : Blo 1215425 1823477 := bbase (se 5 (by rfl) ⟨85475, by rfl⟩ : syracuseStep 1823477 = 170951) (by norm_num)
theorem B1823501 : Blo 1215425 1823501 := bbase (se 3 (by rfl) ⟨341906, by rfl⟩ : syracuseStep 1823501 = 683813) (by norm_num)
theorem B2052877 : Blo 1215425 2052877 := bbase (se 3 (by rfl) ⟨384914, by rfl⟩ : syracuseStep 2052877 = 769829) (by norm_num)
theorem B1823525 : Blo 1215425 1823525 := bbase (se 4 (by rfl) ⟨170955, by rfl⟩ : syracuseStep 1823525 = 341911) (by norm_num)
theorem B1299245 : Blo 1215425 1299245 := bbase (se 3 (by rfl) ⟨243608, by rfl⟩ : syracuseStep 1299245 = 487217) (by norm_num)
theorem B1823549 : Blo 1215425 1823549 := bbase (se 3 (by rfl) ⟨341915, by rfl⟩ : syracuseStep 1823549 = 683831) (by norm_num)
theorem B1823573 : Blo 1215425 1823573 := bbase (se 9 (by rfl) ⟨5342, by rfl⟩ : syracuseStep 1823573 = 10685) (by norm_num)
theorem B2052965 : Blo 1215425 2052965 := bbase (se 4 (by rfl) ⟨192465, by rfl⟩ : syracuseStep 2052965 = 384931) (by norm_num)
theorem B1823597 : Blo 1215425 1823597 := bbase (se 3 (by rfl) ⟨341924, by rfl⟩ : syracuseStep 1823597 = 683849) (by norm_num)
theorem B1823621 : Blo 1215425 1823621 := bbase (se 4 (by rfl) ⟨170964, by rfl⟩ : syracuseStep 1823621 = 341929) (by norm_num)
theorem B1823645 : Blo 1215425 1823645 := bbase (se 3 (by rfl) ⟨341933, by rfl⟩ : syracuseStep 1823645 = 683867) (by norm_num)
theorem B1823669 : Blo 1215425 1823669 := bbase (se 5 (by rfl) ⟨85484, by rfl⟩ : syracuseStep 1823669 = 170969) (by norm_num)
theorem B1823693 : Blo 1215425 1823693 := bbase (se 3 (by rfl) ⟨341942, by rfl⟩ : syracuseStep 1823693 = 683885) (by norm_num)
theorem B1823717 : Blo 1215425 1823717 := bbase (se 4 (by rfl) ⟨170973, by rfl⟩ : syracuseStep 1823717 = 341947) (by norm_num)
theorem B2339813 : Blo 1215425 2339813 := bbase (se 4 (by rfl) ⟨219357, by rfl⟩ : syracuseStep 2339813 = 438715) (by norm_num)
theorem B2053093 : Blo 1215425 2053093 := bbase (se 4 (by rfl) ⟨192477, by rfl⟩ : syracuseStep 2053093 = 384955) (by norm_num)
theorem B1823741 : Blo 1215425 1823741 := bbase (se 3 (by rfl) ⟨341951, by rfl⟩ : syracuseStep 1823741 = 683903) (by norm_num)
theorem B1823765 : Blo 1215425 1823765 := bbase (se 6 (by rfl) ⟨42744, by rfl⟩ : syracuseStep 1823765 = 85489) (by norm_num)
theorem B3077149 : Blo 1215425 3077149 := bbase (se 3 (by rfl) ⟨576965, by rfl⟩ : syracuseStep 3077149 = 1153931) (by norm_num)
theorem B1823789 : Blo 1215425 1823789 := bbase (se 3 (by rfl) ⟨341960, by rfl⟩ : syracuseStep 1823789 = 683921) (by norm_num)
theorem B7025717 : Blo 1215425 7025717 := bbase (se 5 (by rfl) ⟨329330, by rfl⟩ : syracuseStep 7025717 = 658661) (by norm_num)
theorem B7402549 : Blo 1215425 7402549 := bbase (se 5 (by rfl) ⟨346994, by rfl⟩ : syracuseStep 7402549 = 693989) (by norm_num)
theorem B2053181 : Blo 1215425 2053181 := bbase (se 3 (by rfl) ⟨384971, by rfl⟩ : syracuseStep 2053181 = 769943) (by norm_num)
theorem B1823813 : Blo 1215425 1823813 := bbase (se 4 (by rfl) ⟨170982, by rfl⟩ : syracuseStep 1823813 = 341965) (by norm_num)
theorem B1315921 : Blo 1215425 1315921 := bbase (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) (by norm_num)
theorem B1823837 : Blo 1215425 1823837 := bbase (se 3 (by rfl) ⟨341969, by rfl⟩ : syracuseStep 1823837 = 683939) (by norm_num)
theorem B1823861 : Blo 1215425 1823861 := bbase (se 5 (by rfl) ⟨85493, by rfl⟩ : syracuseStep 1823861 = 170987) (by norm_num)
theorem B3077261 : Blo 1215425 3077261 := bbase (se 3 (by rfl) ⟨576986, by rfl⟩ : syracuseStep 3077261 = 1153973) (by norm_num)
theorem B1823885 : Blo 1215425 1823885 := bbase (se 3 (by rfl) ⟨341978, by rfl⟩ : syracuseStep 1823885 = 683957) (by norm_num)
theorem B1823909 : Blo 1215425 1823909 := bbase (se 4 (by rfl) ⟨170991, by rfl⟩ : syracuseStep 1823909 = 341983) (by norm_num)
theorem B1823933 : Blo 1215425 1823933 := bbase (se 3 (by rfl) ⟨341987, by rfl⟩ : syracuseStep 1823933 = 683975) (by norm_num)
theorem B2053309 : Blo 1215425 2053309 := bbase (se 3 (by rfl) ⟨384995, by rfl⟩ : syracuseStep 2053309 = 769991) (by norm_num)
theorem B1823957 : Blo 1215425 1823957 := bbase (se 7 (by rfl) ⟨21374, by rfl⟩ : syracuseStep 1823957 = 42749) (by norm_num)
theorem B1823981 : Blo 1215425 1823981 := bbase (se 3 (by rfl) ⟨341996, by rfl⟩ : syracuseStep 1823981 = 683993) (by norm_num)
theorem B1824005 : Blo 1215425 1824005 := bbase (se 4 (by rfl) ⟨171000, by rfl⟩ : syracuseStep 1824005 = 342001) (by norm_num)
theorem B2053397 : Blo 1215425 2053397 := bbase (se 6 (by rfl) ⟨48126, by rfl⟩ : syracuseStep 2053397 = 96253) (by norm_num)
theorem B1824029 : Blo 1215425 1824029 := bbase (se 3 (by rfl) ⟨342005, by rfl⟩ : syracuseStep 1824029 = 684011) (by norm_num)
theorem B2921773 : Blo 1215425 2921773 := bbase (se 3 (by rfl) ⟨547832, by rfl⟩ : syracuseStep 2921773 = 1095665) (by norm_num)
theorem B1824053 : Blo 1215425 1824053 := bbase (se 5 (by rfl) ⟨85502, by rfl⟩ : syracuseStep 1824053 = 171005) (by norm_num)
theorem B2667845 : Blo 1215425 2667845 := bbase (se 4 (by rfl) ⟨250110, by rfl⟩ : syracuseStep 2667845 = 500221) (by norm_num)
theorem B3077453 : Blo 1215425 3077453 := bbase (se 3 (by rfl) ⟨577022, by rfl⟩ : syracuseStep 3077453 = 1154045) (by norm_num)
theorem B1824077 : Blo 1215425 1824077 := bbase (se 3 (by rfl) ⟨342014, by rfl⟩ : syracuseStep 1824077 = 684029) (by norm_num)
theorem B1824101 : Blo 1215425 1824101 := bbase (se 4 (by rfl) ⟨171009, by rfl⟩ : syracuseStep 1824101 = 342019) (by norm_num)
theorem B2307437 : Blo 1215425 2307437 := bbase (se 3 (by rfl) ⟨432644, by rfl⟩ : syracuseStep 2307437 = 865289) (by norm_num)
theorem B1824125 : Blo 1215425 1824125 := bbase (se 3 (by rfl) ⟨342023, by rfl⟩ : syracuseStep 1824125 = 684047) (by norm_num)
theorem B1824149 : Blo 1215425 1824149 := bbase (se 6 (by rfl) ⟨42753, by rfl⟩ : syracuseStep 1824149 = 85507) (by norm_num)
theorem B2053525 : Blo 1215425 2053525 := bbase (se 6 (by rfl) ⟨48129, by rfl⟩ : syracuseStep 2053525 = 96259) (by norm_num)
theorem B4216229 : Blo 1215425 4216229 := bbase (se 4 (by rfl) ⟨395271, by rfl⟩ : syracuseStep 4216229 = 790543) (by norm_num)
theorem B1824173 : Blo 1215425 1824173 := bbase (se 3 (by rfl) ⟨342032, by rfl⟩ : syracuseStep 1824173 = 684065) (by norm_num)
theorem B1824197 : Blo 1215425 1824197 := bbase (se 4 (by rfl) ⟨171018, by rfl⟩ : syracuseStep 1824197 = 342037) (by norm_num)
theorem B6157781 : Blo 1215425 6157781 := bbase (se 7 (by rfl) ⟨72161, by rfl⟩ : syracuseStep 6157781 = 144323) (by norm_num)
theorem B1824221 : Blo 1215425 1824221 := bbase (se 3 (by rfl) ⟨342041, by rfl⟩ : syracuseStep 1824221 = 684083) (by norm_num)
theorem B2053613 : Blo 1215425 2053613 := bbase (se 3 (by rfl) ⟨385052, by rfl⟩ : syracuseStep 2053613 = 770105) (by norm_num)
theorem B1947125 : Blo 1215425 1947125 := bbase (se 5 (by rfl) ⟨91271, by rfl⟩ : syracuseStep 1947125 = 182543) (by norm_num)
theorem B1824245 : Blo 1215425 1824245 := bbase (se 5 (by rfl) ⟨85511, by rfl⟩ : syracuseStep 1824245 = 171023) (by norm_num)
theorem B1824269 : Blo 1215425 1824269 := bbase (se 3 (by rfl) ⟨342050, by rfl⟩ : syracuseStep 1824269 = 684101) (by norm_num)
theorem B1299997 : Blo 1215425 1299997 := bbase (se 3 (by rfl) ⟨243749, by rfl⟩ : syracuseStep 1299997 = 487499) (by norm_num)
theorem B1824293 : Blo 1215425 1824293 := bbase (se 4 (by rfl) ⟨171027, by rfl⟩ : syracuseStep 1824293 = 342055) (by norm_num)
theorem B1824317 : Blo 1215425 1824317 := bbase (se 3 (by rfl) ⟨342059, by rfl⟩ : syracuseStep 1824317 = 684119) (by norm_num)
theorem B1824341 : Blo 1215425 1824341 := bbase (se 8 (by rfl) ⟨10689, by rfl⟩ : syracuseStep 1824341 = 21379) (by norm_num)
theorem B6575701 : Blo 1215425 6575701 := bbase (se 8 (by rfl) ⟨38529, by rfl⟩ : syracuseStep 6575701 = 77059) (by norm_num)
theorem B1824365 : Blo 1215425 1824365 := bbase (se 3 (by rfl) ⟨342068, by rfl⟩ : syracuseStep 1824365 = 684137) (by norm_num)
theorem B2053741 : Blo 1215425 2053741 := bbase (se 3 (by rfl) ⟨385076, by rfl⟩ : syracuseStep 2053741 = 770153) (by norm_num)
theorem B2922101 : Blo 1215425 2922101 := bbase (se 5 (by rfl) ⟨136973, by rfl⟩ : syracuseStep 2922101 = 273947) (by norm_num)
theorem B1824389 : Blo 1215425 1824389 := bbase (se 4 (by rfl) ⟨171036, by rfl⟩ : syracuseStep 1824389 = 342073) (by norm_num)
theorem B1824413 : Blo 1215425 1824413 := bbase (se 3 (by rfl) ⟨342077, by rfl⟩ : syracuseStep 1824413 = 684155) (by norm_num)
theorem B3077797 : Blo 1215425 3077797 := bbase (se 4 (by rfl) ⟨288543, by rfl⟩ : syracuseStep 3077797 = 577087) (by norm_num)
theorem B3118765 : Blo 1215425 3118765 := bbase (se 3 (by rfl) ⟨584768, by rfl⟩ : syracuseStep 3118765 = 1169537) (by norm_num)
theorem B2922157 : Blo 1215425 2922157 := bbase (se 3 (by rfl) ⟨547904, by rfl⟩ : syracuseStep 2922157 = 1095809) (by norm_num)
theorem B1316525 : Blo 1215425 1316525 := bbase (se 3 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 1316525 = 493697) (by norm_num)
theorem B1824437 : Blo 1215425 1824437 := bbase (se 5 (by rfl) ⟨85520, by rfl⟩ : syracuseStep 1824437 = 171041) (by norm_num)
theorem B3897029 : Blo 1215425 3897029 := bbase (se 4 (by rfl) ⟨365346, by rfl⟩ : syracuseStep 3897029 = 730693) (by norm_num)
theorem B2053829 : Blo 1215425 2053829 := bbase (se 4 (by rfl) ⟨192546, by rfl⟩ : syracuseStep 2053829 = 385093) (by norm_num)
theorem B1824461 : Blo 1215425 1824461 := bbase (se 3 (by rfl) ⟨342086, by rfl⟩ : syracuseStep 1824461 = 684173) (by norm_num)
theorem B1947349 : Blo 1215425 1947349 := bbase (se 7 (by rfl) ⟨22820, by rfl⟩ : syracuseStep 1947349 = 45641) (by norm_num)
theorem B1824485 : Blo 1215425 1824485 := bbase (se 4 (by rfl) ⟨171045, by rfl⟩ : syracuseStep 1824485 = 342091) (by norm_num)
theorem B1824509 : Blo 1215425 1824509 := bbase (se 3 (by rfl) ⟨342095, by rfl⟩ : syracuseStep 1824509 = 684191) (by norm_num)
theorem B3077909 : Blo 1215425 3077909 := bbase (se 6 (by rfl) ⟨72138, by rfl⟩ : syracuseStep 3077909 = 144277) (by norm_num)
theorem B1824533 : Blo 1215425 1824533 := bbase (se 6 (by rfl) ⟨42762, by rfl⟩ : syracuseStep 1824533 = 85525) (by norm_num)
theorem B1824557 : Blo 1215425 1824557 := bbase (se 3 (by rfl) ⟨342104, by rfl⟩ : syracuseStep 1824557 = 684209) (by norm_num)
theorem B1824581 : Blo 1215425 1824581 := bbase (se 4 (by rfl) ⟨171054, by rfl⟩ : syracuseStep 1824581 = 342109) (by norm_num)
theorem B2053957 : Blo 1215425 2053957 := bbase (se 4 (by rfl) ⟨192558, by rfl⟩ : syracuseStep 2053957 = 385117) (by norm_num)
theorem B1824605 : Blo 1215425 1824605 := bbase (se 3 (by rfl) ⟨342113, by rfl⟩ : syracuseStep 1824605 = 684227) (by norm_num)
theorem B3463013 : Blo 1215425 3463013 := bbase (se 4 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 3463013 = 649315) (by norm_num)
theorem B1824629 : Blo 1215425 1824629 := bbase (se 5 (by rfl) ⟨85529, by rfl⟩ : syracuseStep 1824629 = 171059) (by norm_num)
theorem B1824653 : Blo 1215425 1824653 := bbase (se 3 (by rfl) ⟨342122, by rfl⟩ : syracuseStep 1824653 = 684245) (by norm_num)
theorem B2922389 : Blo 1215425 2922389 := bbase (se 6 (by rfl) ⟨68493, by rfl⟩ : syracuseStep 2922389 = 136987) (by norm_num)
theorem B2054045 : Blo 1215425 2054045 := bbase (se 3 (by rfl) ⟨385133, by rfl⟩ : syracuseStep 2054045 = 770267) (by norm_num)
theorem B1824677 : Blo 1215425 1824677 := bbase (se 4 (by rfl) ⟨171063, by rfl⟩ : syracuseStep 1824677 = 342127) (by norm_num)
theorem B1824701 : Blo 1215425 1824701 := bbase (se 3 (by rfl) ⟨342131, by rfl⟩ : syracuseStep 1824701 = 684263) (by norm_num)
theorem B3078101 : Blo 1215425 3078101 := bbase (se 7 (by rfl) ⟨36071, by rfl⟩ : syracuseStep 3078101 = 72143) (by norm_num)
theorem B1824725 : Blo 1215425 1824725 := bbase (se 7 (by rfl) ⟨21383, by rfl⟩ : syracuseStep 1824725 = 42767) (by norm_num)
theorem B1824749 : Blo 1215425 1824749 := bbase (se 3 (by rfl) ⟨342140, by rfl⟩ : syracuseStep 1824749 = 684281) (by norm_num)
theorem B1824773 : Blo 1215425 1824773 := bbase (se 4 (by rfl) ⟨171072, by rfl⟩ : syracuseStep 1824773 = 342145) (by norm_num)
theorem B2193421 : Blo 1215425 2193421 := bbase (se 3 (by rfl) ⟨411266, by rfl⟩ : syracuseStep 2193421 = 822533) (by norm_num)
theorem B1824797 : Blo 1215425 1824797 := bbase (se 3 (by rfl) ⟨342149, by rfl⟩ : syracuseStep 1824797 = 684299) (by norm_num)
theorem B2054173 : Blo 1215425 2054173 := bbase (se 3 (by rfl) ⟨385157, by rfl⟩ : syracuseStep 2054173 = 770315) (by norm_num)
theorem B1824821 : Blo 1215425 1824821 := bbase (se 5 (by rfl) ⟨85538, by rfl⟩ : syracuseStep 1824821 = 171077) (by norm_num)
theorem B4683845 : Blo 1215425 4683845 := bbase (se 4 (by rfl) ⟨439110, by rfl⟩ : syracuseStep 4683845 = 878221) (by norm_num)
theorem B1824845 : Blo 1215425 1824845 := bbase (se 3 (by rfl) ⟨342158, by rfl⟩ : syracuseStep 1824845 = 684317) (by norm_num)
theorem B2922581 : Blo 1215425 2922581 := bbase (se 8 (by rfl) ⟨17124, by rfl⟩ : syracuseStep 2922581 = 34249) (by norm_num)
theorem B2193493 : Blo 1215425 2193493 := bbase (se 8 (by rfl) ⟨12852, by rfl⟩ : syracuseStep 2193493 = 25705) (by norm_num)
theorem B2308189 : Blo 1215425 2308189 := bbase (se 3 (by rfl) ⟨432785, by rfl⟩ : syracuseStep 2308189 = 865571) (by norm_num)
theorem B1824869 : Blo 1215425 1824869 := bbase (se 4 (by rfl) ⟨171081, by rfl⟩ : syracuseStep 1824869 = 342163) (by norm_num)
theorem B3700837 : Blo 1215425 3700837 := bbase (se 4 (by rfl) ⟨346953, by rfl⟩ : syracuseStep 3700837 = 693907) (by norm_num)
theorem B10393717 : Blo 1215425 10393717 := bbase (se 5 (by rfl) ⟨487205, by rfl⟩ : syracuseStep 10393717 = 974411) (by norm_num)
theorem B2054261 : Blo 1215425 2054261 := bbase (se 5 (by rfl) ⟨96293, by rfl⟩ : syracuseStep 2054261 = 192587) (by norm_num)
theorem B1824893 : Blo 1215425 1824893 := bbase (se 3 (by rfl) ⟨342167, by rfl⟩ : syracuseStep 1824893 = 684335) (by norm_num)
theorem B1824917 : Blo 1215425 1824917 := bbase (se 6 (by rfl) ⟨42771, by rfl⟩ : syracuseStep 1824917 = 85543) (by norm_num)
theorem B3700885 : Blo 1215425 3700885 := bbase (se 6 (by rfl) ⟨86739, by rfl⟩ : syracuseStep 3700885 = 173479) (by norm_num)
theorem B1824941 : Blo 1215425 1824941 := bbase (se 3 (by rfl) ⟨342176, by rfl⟩ : syracuseStep 1824941 = 684353) (by norm_num)
theorem B4102325 : Blo 1215425 4102325 := bbase (se 5 (by rfl) ⟨192296, by rfl⟩ : syracuseStep 4102325 = 384593) (by norm_num)
theorem B1824965 : Blo 1215425 1824965 := bbase (se 4 (by rfl) ⟨171090, by rfl⟩ : syracuseStep 1824965 = 342181) (by norm_num)
theorem B1824989 : Blo 1215425 1824989 := bbase (se 3 (by rfl) ⟨342185, by rfl⟩ : syracuseStep 1824989 = 684371) (by norm_num)
theorem B2193637 : Blo 1215425 2193637 := bbase (se 4 (by rfl) ⟨205653, by rfl⟩ : syracuseStep 2193637 = 411307) (by norm_num)
theorem B1538281 : Blo 1215425 1538281 := bbase (se 2 (by rfl) ⟨576855, by rfl⟩ : syracuseStep 1538281 = 1153711) (by norm_num)
theorem B2308333 : Blo 1215425 2308333 := bbase (se 3 (by rfl) ⟨432812, by rfl⟩ : syracuseStep 2308333 = 865625) (by norm_num)
theorem B1825013 : Blo 1215425 1825013 := bbase (se 5 (by rfl) ⟨85547, by rfl⟩ : syracuseStep 1825013 = 171095) (by norm_num)
theorem B2054389 : Blo 1215425 2054389 := bbase (se 5 (by rfl) ⟨96299, by rfl⟩ : syracuseStep 2054389 = 192599) (by norm_num)
theorem B1825037 : Blo 1215425 1825037 := bbase (se 3 (by rfl) ⟨342194, by rfl⟩ : syracuseStep 1825037 = 684389) (by norm_num)
theorem B1825061 : Blo 1215425 1825061 := bbase (se 4 (by rfl) ⟨171099, by rfl⟩ : syracuseStep 1825061 = 342199) (by norm_num)
theorem B3078445 : Blo 1215425 3078445 := bbase (se 3 (by rfl) ⟨577208, by rfl⟩ : syracuseStep 3078445 = 1154417) (by norm_num)
theorem B1825085 : Blo 1215425 1825085 := bbase (se 3 (by rfl) ⟨342203, by rfl⟩ : syracuseStep 1825085 = 684407) (by norm_num)
theorem B4618565 : Blo 1215425 4618565 := bbase (se 4 (by rfl) ⟨432990, by rfl⟩ : syracuseStep 4618565 = 865981) (by norm_num)
theorem B5626181 : Blo 1215425 5626181 := bbase (se 4 (by rfl) ⟨527454, by rfl⟩ : syracuseStep 5626181 = 1054909) (by norm_num)
theorem B1644877 : Blo 1215425 1644877 := bbase (se 3 (by rfl) ⟨308414, by rfl⟩ : syracuseStep 1644877 = 616829) (by norm_num)
theorem B1825109 : Blo 1215425 1825109 := bbase (se 10 (by rfl) ⟨2673, by rfl⟩ : syracuseStep 1825109 = 5347) (by norm_num)
theorem B1825133 : Blo 1215425 1825133 := bbase (se 3 (by rfl) ⟨342212, by rfl⟩ : syracuseStep 1825133 = 684425) (by norm_num)
theorem B1825157 : Blo 1215425 1825157 := bbase (se 4 (by rfl) ⟨171108, by rfl⟩ : syracuseStep 1825157 = 342217) (by norm_num)
theorem B2308493 : Blo 1215425 2308493 := bbase (se 3 (by rfl) ⟨432842, by rfl⟩ : syracuseStep 2308493 = 865685) (by norm_num)
theorem B1538453 : Blo 1215425 1538453 := bbase (se 6 (by rfl) ⟨36057, by rfl⟩ : syracuseStep 1538453 = 72115) (by norm_num)
theorem B3078557 : Blo 1215425 3078557 := bbase (se 3 (by rfl) ⟨577229, by rfl⟩ : syracuseStep 3078557 = 1154459) (by norm_num)
theorem B1825181 : Blo 1215425 1825181 := bbase (se 3 (by rfl) ⟨342221, by rfl⟩ : syracuseStep 1825181 = 684443) (by norm_num)
theorem B7018933 : Blo 1215425 7018933 := bbase (se 5 (by rfl) ⟨329012, by rfl⟩ : syracuseStep 7018933 = 658025) (by norm_num)
theorem B5339573 : Blo 1215425 5339573 := bbase (se 5 (by rfl) ⟨250292, by rfl⟩ : syracuseStep 5339573 = 500585) (by norm_num)
theorem B1825205 : Blo 1215425 1825205 := bbase (se 5 (by rfl) ⟨85556, by rfl⟩ : syracuseStep 1825205 = 171113) (by norm_num)
theorem B1538509 : Blo 1215425 1538509 := bbase (se 3 (by rfl) ⟨288470, by rfl⟩ : syracuseStep 1538509 = 576941) (by norm_num)
theorem B1825229 : Blo 1215425 1825229 := bbase (se 3 (by rfl) ⟨342230, by rfl⟩ : syracuseStep 1825229 = 684461) (by norm_num)
theorem B1825253 : Blo 1215425 1825253 := bbase (se 4 (by rfl) ⟨171117, by rfl⟩ : syracuseStep 1825253 = 342235) (by norm_num)
theorem B1825277 : Blo 1215425 1825277 := bbase (se 3 (by rfl) ⟨342239, by rfl⟩ : syracuseStep 1825277 = 684479) (by norm_num)
theorem B3463685 : Blo 1215425 3463685 := bbase (se 4 (by rfl) ⟨324720, by rfl⟩ : syracuseStep 3463685 = 649441) (by norm_num)
theorem B1825301 : Blo 1215425 1825301 := bbase (se 6 (by rfl) ⟨42780, by rfl⟩ : syracuseStep 1825301 = 85561) (by norm_num)
theorem B2308637 : Blo 1215425 2308637 := bbase (se 3 (by rfl) ⟨432869, by rfl⟩ : syracuseStep 2308637 = 865739) (by norm_num)
theorem B1538605 : Blo 1215425 1538605 := bbase (se 3 (by rfl) ⟨288488, by rfl⟩ : syracuseStep 1538605 = 576977) (by norm_num)
theorem B1825325 : Blo 1215425 1825325 := bbase (se 3 (by rfl) ⟨342248, by rfl⟩ : syracuseStep 1825325 = 684497) (by norm_num)
theorem B1825349 : Blo 1215425 1825349 := bbase (se 4 (by rfl) ⟨171126, by rfl⟩ : syracuseStep 1825349 = 342253) (by norm_num)
theorem B3078749 : Blo 1215425 3078749 := bbase (se 3 (by rfl) ⟨577265, by rfl⟩ : syracuseStep 3078749 = 1154531) (by norm_num)
theorem B2341469 : Blo 1215425 2341469 := bbase (se 3 (by rfl) ⟨439025, by rfl⟩ : syracuseStep 2341469 = 878051) (by norm_num)
theorem B1825373 : Blo 1215425 1825373 := bbase (se 3 (by rfl) ⟨342257, by rfl⟩ : syracuseStep 1825373 = 684515) (by norm_num)
theorem B4102757 : Blo 1215425 4102757 := bbase (se 4 (by rfl) ⟨384633, by rfl⟩ : syracuseStep 4102757 = 769267) (by norm_num)
theorem B4618853 : Blo 1215425 4618853 := bbase (se 4 (by rfl) ⟨433017, by rfl⟩ : syracuseStep 4618853 = 866035) (by norm_num)
theorem B1825397 : Blo 1215425 1825397 := bbase (se 5 (by rfl) ⟨85565, by rfl⟩ : syracuseStep 1825397 = 171131) (by norm_num)
theorem B1825421 : Blo 1215425 1825421 := bbase (se 3 (by rfl) ⟨342266, by rfl⟩ : syracuseStep 1825421 = 684533) (by norm_num)
theorem B2079389 : Blo 1215425 2079389 := bbase (se 3 (by rfl) ⟨389885, by rfl⟩ : syracuseStep 2079389 = 779771) (by norm_num)
theorem B2734757 : Blo 1215425 2734757 := bbase (se 4 (by rfl) ⟨256383, by rfl⟩ : syracuseStep 2734757 = 512767) (by norm_num)
theorem B1825445 : Blo 1215425 1825445 := bbase (se 4 (by rfl) ⟨171135, by rfl⟩ : syracuseStep 1825445 = 342271) (by norm_num)
theorem B1825469 : Blo 1215425 1825469 := bbase (se 3 (by rfl) ⟨342275, by rfl⟩ : syracuseStep 1825469 = 684551) (by norm_num)
theorem B1317565 : Blo 1215425 1317565 := bbase (se 3 (by rfl) ⟨247043, by rfl⟩ : syracuseStep 1317565 = 494087) (by norm_num)
theorem B1825493 : Blo 1215425 1825493 := bbase (se 7 (by rfl) ⟨21392, by rfl⟩ : syracuseStep 1825493 = 42785) (by norm_num)
theorem B1538777 : Blo 1215425 1538777 := bbase (se 2 (by rfl) ⟨577041, by rfl⟩ : syracuseStep 1538777 = 1154083) (by norm_num)
theorem B6159077 : Blo 1215425 6159077 := bbase (se 4 (by rfl) ⟨577413, by rfl⟩ : syracuseStep 6159077 = 1154827) (by norm_num)
theorem B2734829 : Blo 1215425 2734829 := bbase (se 3 (by rfl) ⟨512780, by rfl⟩ : syracuseStep 2734829 = 1025561) (by norm_num)
theorem B1825517 : Blo 1215425 1825517 := bbase (se 3 (by rfl) ⟨342284, by rfl⟩ : syracuseStep 1825517 = 684569) (by norm_num)
theorem B1825541 : Blo 1215425 1825541 := bbase (se 4 (by rfl) ⟨171144, by rfl⟩ : syracuseStep 1825541 = 342289) (by norm_num)
theorem B1538833 : Blo 1215425 1538833 := bbase (se 2 (by rfl) ⟨577062, by rfl⟩ : syracuseStep 1538833 = 1154125) (by norm_num)
theorem B1825565 : Blo 1215425 1825565 := bbase (se 3 (by rfl) ⟨342293, by rfl⟩ : syracuseStep 1825565 = 684587) (by norm_num)
theorem B1317665 : Blo 1215425 1317665 := bbase (se 2 (by rfl) ⟨494124, by rfl⟩ : syracuseStep 1317665 = 988249) (by norm_num)
theorem B1645357 : Blo 1215425 1645357 := bbase (se 3 (by rfl) ⟨308504, by rfl⟩ : syracuseStep 1645357 = 617009) (by norm_num)
theorem B2734901 : Blo 1215425 2734901 := bbase (se 5 (by rfl) ⟨128198, by rfl⟩ : syracuseStep 2734901 = 256397) (by norm_num)
theorem B1825589 : Blo 1215425 1825589 := bbase (se 5 (by rfl) ⟨85574, by rfl⟩ : syracuseStep 1825589 = 171149) (by norm_num)
theorem B2308925 : Blo 1215425 2308925 := bbase (se 3 (by rfl) ⟨432923, by rfl⟩ : syracuseStep 2308925 = 865847) (by norm_num)
theorem B1948477 : Blo 1215425 1948477 := bbase (se 3 (by rfl) ⟨365339, by rfl⟩ : syracuseStep 1948477 = 730679) (by norm_num)
theorem B1825613 : Blo 1215425 1825613 := bbase (se 3 (by rfl) ⟨342302, by rfl⟩ : syracuseStep 1825613 = 684605) (by norm_num)
theorem B1825637 : Blo 1215425 1825637 := bbase (se 4 (by rfl) ⟨171153, by rfl⟩ : syracuseStep 1825637 = 342307) (by norm_num)
theorem B1538929 : Blo 1215425 1538929 := bbase (se 2 (by rfl) ⟨577098, by rfl⟩ : syracuseStep 1538929 = 1154197) (by norm_num)
theorem B2734973 : Blo 1215425 2734973 := bbase (se 3 (by rfl) ⟨512807, by rfl⟩ : syracuseStep 2734973 = 1025615) (by norm_num)
theorem B1825661 : Blo 1215425 1825661 := bbase (se 3 (by rfl) ⟨342311, by rfl⟩ : syracuseStep 1825661 = 684623) (by norm_num)
theorem B1825685 : Blo 1215425 1825685 := bbase (se 6 (by rfl) ⟨42789, by rfl⟩ : syracuseStep 1825685 = 85579) (by norm_num)
theorem B1825709 : Blo 1215425 1825709 := bbase (se 3 (by rfl) ⟨342320, by rfl⟩ : syracuseStep 1825709 = 684641) (by norm_num)
theorem B3079093 : Blo 1215425 3079093 := bbase (se 5 (by rfl) ⟨144332, by rfl⟩ : syracuseStep 3079093 = 288665) (by norm_num)
theorem B3464117 : Blo 1215425 3464117 := bbase (se 5 (by rfl) ⟨162380, by rfl⟩ : syracuseStep 3464117 = 324761) (by norm_num)
theorem B2735045 : Blo 1215425 2735045 := bbase (se 4 (by rfl) ⟨256410, by rfl⟩ : syracuseStep 2735045 = 512821) (by norm_num)
theorem B1825733 : Blo 1215425 1825733 := bbase (se 4 (by rfl) ⟨171162, by rfl⟩ : syracuseStep 1825733 = 342325) (by norm_num)
theorem B2309077 : Blo 1215425 2309077 := bbase (se 7 (by rfl) ⟨27059, by rfl⟩ : syracuseStep 2309077 = 54119) (by norm_num)
theorem B1825757 : Blo 1215425 1825757 := bbase (se 3 (by rfl) ⟨342329, by rfl⟩ : syracuseStep 1825757 = 684659) (by norm_num)
theorem B1825781 : Blo 1215425 1825781 := bbase (se 5 (by rfl) ⟨85583, by rfl⟩ : syracuseStep 1825781 = 171167) (by norm_num)
theorem B2735117 : Blo 1215425 2735117 := bbase (se 3 (by rfl) ⟨512834, by rfl⟩ : syracuseStep 2735117 = 1025669) (by norm_num)
theorem B1825805 : Blo 1215425 1825805 := bbase (se 3 (by rfl) ⟨342338, by rfl⟩ : syracuseStep 1825805 = 684677) (by norm_num)
theorem B4103189 : Blo 1215425 4103189 := bbase (se 6 (by rfl) ⟨96168, by rfl⟩ : syracuseStep 4103189 = 192337) (by norm_num)
theorem B2923541 : Blo 1215425 2923541 := bbase (se 6 (by rfl) ⟨68520, by rfl⟩ : syracuseStep 2923541 = 137041) (by norm_num)
theorem B1539101 : Blo 1215425 1539101 := bbase (se 3 (by rfl) ⟨288581, by rfl⟩ : syracuseStep 1539101 = 577163) (by norm_num)
theorem B3079205 : Blo 1215425 3079205 := bbase (se 4 (by rfl) ⟨288675, by rfl⟩ : syracuseStep 3079205 = 577351) (by norm_num)
theorem B1825829 : Blo 1215425 1825829 := bbase (se 4 (by rfl) ⟨171171, by rfl⟩ : syracuseStep 1825829 = 342343) (by norm_num)
theorem B2595901 : Blo 1215425 2595901 := bbase (se 3 (by rfl) ⟨486731, by rfl⟩ : syracuseStep 2595901 = 973463) (by norm_num)
theorem B1825853 : Blo 1215425 1825853 := bbase (se 3 (by rfl) ⟨342347, by rfl⟩ : syracuseStep 1825853 = 684695) (by norm_num)
theorem B3513413 : Blo 1215425 3513413 := bbase (se 4 (by rfl) ⟨329382, by rfl⟩ : syracuseStep 3513413 = 658765) (by norm_num)
theorem B2735189 : Blo 1215425 2735189 := bbase (se 8 (by rfl) ⟨16026, by rfl⟩ : syracuseStep 2735189 = 32053) (by norm_num)
theorem B1539157 : Blo 1215425 1539157 := bbase (se 8 (by rfl) ⟨9018, by rfl⟩ : syracuseStep 1539157 = 18037) (by norm_num)
theorem B23379029 : Blo 1215425 23379029 := bbase (se 8 (by rfl) ⟨136986, by rfl⟩ : syracuseStep 23379029 = 273973) (by norm_num)
theorem B1825877 : Blo 1215425 1825877 := bbase (se 8 (by rfl) ⟨10698, by rfl⟩ : syracuseStep 1825877 = 21397) (by norm_num)
theorem B1825901 : Blo 1215425 1825901 := bbase (se 3 (by rfl) ⟨342356, by rfl⟩ : syracuseStep 1825901 = 684713) (by norm_num)
theorem B1825925 : Blo 1215425 1825925 := bbase (se 4 (by rfl) ⟨171180, by rfl⟩ : syracuseStep 1825925 = 342361) (by norm_num)
theorem B2735261 : Blo 1215425 2735261 := bbase (se 3 (by rfl) ⟨512861, by rfl⟩ : syracuseStep 2735261 = 1025723) (by norm_num)
theorem B2964637 : Blo 1215425 2964637 := bbase (se 3 (by rfl) ⟨555869, by rfl⟩ : syracuseStep 2964637 = 1111739) (by norm_num)
theorem B1825949 : Blo 1215425 1825949 := bbase (se 3 (by rfl) ⟨342365, by rfl⟩ : syracuseStep 1825949 = 684731) (by norm_num)
theorem B1539253 : Blo 1215425 1539253 := bbase (se 5 (by rfl) ⟨72152, by rfl⟩ : syracuseStep 1539253 = 144305) (by norm_num)
theorem B1825973 : Blo 1215425 1825973 := bbase (se 5 (by rfl) ⟨85592, by rfl⟩ : syracuseStep 1825973 = 171185) (by norm_num)
theorem B1825997 : Blo 1215425 1825997 := bbase (se 3 (by rfl) ⟨342374, by rfl⟩ : syracuseStep 1825997 = 684749) (by norm_num)
theorem B2735333 : Blo 1215425 2735333 := bbase (se 4 (by rfl) ⟨256437, by rfl⟩ : syracuseStep 2735333 = 512875) (by norm_num)
theorem B3079397 : Blo 1215425 3079397 := bbase (se 4 (by rfl) ⟨288693, by rfl⟩ : syracuseStep 3079397 = 577387) (by norm_num)
theorem B1826021 : Blo 1215425 1826021 := bbase (se 4 (by rfl) ⟨171189, by rfl⟩ : syracuseStep 1826021 = 342379) (by norm_num)
theorem B1948925 : Blo 1215425 1948925 := bbase (se 3 (by rfl) ⟨365423, by rfl⟩ : syracuseStep 1948925 = 730847) (by norm_num)
theorem B1826045 : Blo 1215425 1826045 := bbase (se 3 (by rfl) ⟨342383, by rfl⟩ : syracuseStep 1826045 = 684767) (by norm_num)
theorem B2309381 : Blo 1215425 2309381 := bbase (se 4 (by rfl) ⟨216504, by rfl⟩ : syracuseStep 2309381 = 433009) (by norm_num)
theorem B1826069 : Blo 1215425 1826069 := bbase (se 6 (by rfl) ⟨42798, by rfl⟩ : syracuseStep 1826069 = 85597) (by norm_num)
theorem B2735405 : Blo 1215425 2735405 := bbase (se 3 (by rfl) ⟨512888, by rfl⟩ : syracuseStep 2735405 = 1025777) (by norm_num)
theorem B1826093 : Blo 1215425 1826093 := bbase (se 3 (by rfl) ⟨342392, by rfl⟩ : syracuseStep 1826093 = 684785) (by norm_num)
theorem B1367365 : Blo 1215425 1367365 := bbase (se 4 (by rfl) ⟨128190, by rfl⟩ : syracuseStep 1367365 = 256381) (by norm_num)
theorem B1826117 : Blo 1215425 1826117 := bbase (se 4 (by rfl) ⟨171198, by rfl⟩ : syracuseStep 1826117 = 342397) (by norm_num)
theorem B1539425 : Blo 1215425 1539425 := bbase (se 2 (by rfl) ⟨577284, by rfl⟩ : syracuseStep 1539425 = 1154569) (by norm_num)
theorem B1367401 : Blo 1215425 1367401 := bbase (se 2 (by rfl) ⟨512775, by rfl⟩ : syracuseStep 1367401 = 1025551) (by norm_num)
theorem B2735477 : Blo 1215425 2735477 := bbase (se 5 (by rfl) ⟨128225, by rfl⟩ : syracuseStep 2735477 = 256451) (by norm_num)
theorem B2465149 : Blo 1215425 2465149 := bbase (se 3 (by rfl) ⟨462215, by rfl⟩ : syracuseStep 2465149 = 924431) (by norm_num)
theorem B1367437 : Blo 1215425 1367437 := bbase (se 3 (by rfl) ⟨256394, by rfl⟩ : syracuseStep 1367437 = 512789) (by norm_num)
theorem B1539481 : Blo 1215425 1539481 := bbase (se 2 (by rfl) ⟨577305, by rfl⟩ : syracuseStep 1539481 = 1154611) (by norm_num)
theorem B1367473 : Blo 1215425 1367473 := bbase (se 2 (by rfl) ⟨512802, by rfl⟩ : syracuseStep 1367473 = 1025605) (by norm_num)
theorem B2735549 : Blo 1215425 2735549 := bbase (se 3 (by rfl) ⟨512915, by rfl⟩ : syracuseStep 2735549 = 1025831) (by norm_num)
theorem B4103621 : Blo 1215425 4103621 := bbase (se 4 (by rfl) ⟨384714, by rfl⟩ : syracuseStep 4103621 = 769429) (by norm_num)
theorem B1367509 : Blo 1215425 1367509 := bbase (se 7 (by rfl) ⟨16025, by rfl⟩ : syracuseStep 1367509 = 32051) (by norm_num)
theorem B3948005 : Blo 1215425 3948005 := bbase (se 4 (by rfl) ⟨370125, by rfl⟩ : syracuseStep 3948005 = 740251) (by norm_num)
theorem B1973749 : Blo 1215425 1973749 := bbase (se 5 (by rfl) ⟨92519, by rfl⟩ : syracuseStep 1973749 = 185039) (by norm_num)
theorem B1367545 : Blo 1215425 1367545 := bbase (se 2 (by rfl) ⟨512829, by rfl⟩ : syracuseStep 1367545 = 1025659) (by norm_num)
theorem B1539577 : Blo 1215425 1539577 := bbase (se 2 (by rfl) ⟨577341, by rfl⟩ : syracuseStep 1539577 = 1154683) (by norm_num)
theorem B2735621 : Blo 1215425 2735621 := bbase (se 4 (by rfl) ⟨256464, by rfl⟩ : syracuseStep 2735621 = 512929) (by norm_num)
theorem B1367581 : Blo 1215425 1367581 := bbase (se 3 (by rfl) ⟨256421, by rfl⟩ : syracuseStep 1367581 = 512843) (by norm_num)
theorem B3079741 : Blo 1215425 3079741 := bbase (se 3 (by rfl) ⟨577451, by rfl⟩ : syracuseStep 3079741 = 1154903) (by norm_num)
theorem B1367617 : Blo 1215425 1367617 := bbase (se 2 (by rfl) ⟨512856, by rfl⟩ : syracuseStep 1367617 = 1025713) (by norm_num)
theorem B2735693 : Blo 1215425 2735693 := bbase (se 3 (by rfl) ⟨512942, by rfl⟩ : syracuseStep 2735693 = 1025885) (by norm_num)
theorem B1367653 : Blo 1215425 1367653 := bbase (se 4 (by rfl) ⟨128217, by rfl⟩ : syracuseStep 1367653 = 256435) (by norm_num)
theorem B1367689 : Blo 1215425 1367689 := bbase (se 2 (by rfl) ⟨512883, by rfl⟩ : syracuseStep 1367689 = 1025767) (by norm_num)
theorem B2735765 : Blo 1215425 2735765 := bbase (se 6 (by rfl) ⟨64119, by rfl⟩ : syracuseStep 2735765 = 128239) (by norm_num)
theorem B3899029 : Blo 1215425 3899029 := bbase (se 6 (by rfl) ⟨91383, by rfl⟩ : syracuseStep 3899029 = 182767) (by norm_num)
theorem B1539749 : Blo 1215425 1539749 := bbase (se 4 (by rfl) ⟨144351, by rfl⟩ : syracuseStep 1539749 = 288703) (by norm_num)
theorem B3464869 : Blo 1215425 3464869 := bbase (se 4 (by rfl) ⟨324831, by rfl⟩ : syracuseStep 3464869 = 649663) (by norm_num)
theorem B1367725 : Blo 1215425 1367725 := bbase (se 3 (by rfl) ⟨256448, by rfl⟩ : syracuseStep 1367725 = 512897) (by norm_num)
theorem B3079853 : Blo 1215425 3079853 := bbase (se 3 (by rfl) ⟨577472, by rfl⟩ : syracuseStep 3079853 = 1154945) (by norm_num)
theorem B5848757 : Blo 1215425 5848757 := bbase (se 5 (by rfl) ⟨274160, by rfl⟩ : syracuseStep 5848757 = 548321) (by norm_num)
theorem B1367761 : Blo 1215425 1367761 := bbase (se 2 (by rfl) ⟨512910, by rfl⟩ : syracuseStep 1367761 = 1025821) (by norm_num)
theorem B2735837 : Blo 1215425 2735837 := bbase (se 3 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 2735837 = 1025939) (by norm_num)
theorem B1539805 : Blo 1215425 1539805 := bbase (se 3 (by rfl) ⟨288713, by rfl⟩ : syracuseStep 1539805 = 577427) (by norm_num)
theorem B1367797 : Blo 1215425 1367797 := bbase (se 5 (by rfl) ⟨64115, by rfl⟩ : syracuseStep 1367797 = 128231) (by norm_num)
theorem B4620037 : Blo 1215425 4620037 := bbase (se 4 (by rfl) ⟨433128, by rfl⟩ : syracuseStep 4620037 = 866257) (by norm_num)
theorem B1367833 : Blo 1215425 1367833 := bbase (se 2 (by rfl) ⟨512937, by rfl⟩ : syracuseStep 1367833 = 1025875) (by norm_num)
theorem B2735909 : Blo 1215425 2735909 := bbase (se 4 (by rfl) ⟨256491, by rfl⟩ : syracuseStep 2735909 = 512983) (by norm_num)
theorem B1367869 : Blo 1215425 1367869 := bbase (se 3 (by rfl) ⟨256475, by rfl⟩ : syracuseStep 1367869 = 512951) (by norm_num)
theorem B1539901 : Blo 1215425 1539901 := bbase (se 3 (by rfl) ⟨288731, by rfl⟩ : syracuseStep 1539901 = 577463) (by norm_num)
theorem B1367905 : Blo 1215425 1367905 := bbase (se 2 (by rfl) ⟨512964, by rfl⟩ : syracuseStep 1367905 = 1025929) (by norm_num)
theorem B2735981 : Blo 1215425 2735981 := bbase (se 3 (by rfl) ⟨512996, by rfl⟩ : syracuseStep 2735981 = 1025993) (by norm_num)
theorem B3080045 : Blo 1215425 3080045 := bbase (se 3 (by rfl) ⟨577508, by rfl⟩ : syracuseStep 3080045 = 1155017) (by norm_num)
theorem B4104053 : Blo 1215425 4104053 := bbase (se 5 (by rfl) ⟨192377, by rfl⟩ : syracuseStep 4104053 = 384755) (by norm_num)
theorem B2465653 : Blo 1215425 2465653 := bbase (se 5 (by rfl) ⟨115577, by rfl⟩ : syracuseStep 2465653 = 231155) (by norm_num)
theorem B1367941 : Blo 1215425 1367941 := bbase (se 4 (by rfl) ⟨128244, by rfl⟩ : syracuseStep 1367941 = 256489) (by norm_num)
theorem B1367977 : Blo 1215425 1367977 := bbase (se 2 (by rfl) ⟨512991, by rfl⟩ : syracuseStep 1367977 = 1025983) (by norm_num)
theorem B2596789 : Blo 1215425 2596789 := bbase (se 5 (by rfl) ⟨121724, by rfl⟩ : syracuseStep 2596789 = 243449) (by norm_num)
theorem B2736053 : Blo 1215425 2736053 := bbase (se 5 (by rfl) ⟨128252, by rfl⟩ : syracuseStep 2736053 = 256505) (by norm_num)
theorem B2080709 : Blo 1215425 2080709 := bbase (se 4 (by rfl) ⟨195066, by rfl⟩ : syracuseStep 2080709 = 390133) (by norm_num)
theorem B1368013 : Blo 1215425 1368013 := bbase (se 3 (by rfl) ⟨256502, by rfl⟩ : syracuseStep 1368013 = 513005) (by norm_num)
theorem B1540073 : Blo 1215425 1540073 := bbase (se 2 (by rfl) ⟨577527, by rfl⟩ : syracuseStep 1540073 = 1155055) (by norm_num)
theorem B1368049 : Blo 1215425 1368049 := bbase (se 2 (by rfl) ⟨513018, by rfl⟩ : syracuseStep 1368049 = 1026037) (by norm_num)
theorem B2310133 : Blo 1215425 2310133 := bbase (se 5 (by rfl) ⟨108287, by rfl⟩ : syracuseStep 2310133 = 216575) (by norm_num)
theorem B6160373 : Blo 1215425 6160373 := bbase (se 5 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 6160373 = 577535) (by norm_num)
theorem B2736125 : Blo 1215425 2736125 := bbase (se 3 (by rfl) ⟨513023, by rfl⟩ : syracuseStep 2736125 = 1026047) (by norm_num)
theorem B1368067 : Blo 1215425 1368067 := bstep (se 1 (by rfl) ⟨1026050, by rfl⟩ : syracuseStep 1368067 = 2052101) B2052101
theorem B2924561 : Blo 1215425 2924561 := bstep (se 2 (by rfl) ⟨1096710, by rfl⟩ : syracuseStep 2924561 = 2193421) B2193421
theorem B6930467 : Blo 1215425 6930467 := bstep (se 1 (by rfl) ⟨5197850, by rfl⟩ : syracuseStep 6930467 = 10395701) B10395701
theorem B3080227 : Blo 1215425 3080227 := bstep (se 1 (by rfl) ⟨2310170, by rfl⟩ : syracuseStep 3080227 = 4620341) B4620341
theorem B4104269 : Blo 1215425 4104269 := bstep (se 3 (by rfl) ⟨769550, by rfl⟩ : syracuseStep 4104269 = 1539101) B1539101
theorem B2924657 : Blo 1215425 2924657 := bstep (se 2 (by rfl) ⟨1096746, by rfl⟩ : syracuseStep 2924657 = 2193493) B2193493
theorem B4104323 : Blo 1215425 4104323 := bstep (se 1 (by rfl) ⟨3078242, by rfl⟩ : syracuseStep 4104323 = 6156485) B6156485
theorem B18735245 : Blo 1215425 18735245 := bstep (se 3 (by rfl) ⟨3512858, by rfl⟩ : syracuseStep 18735245 = 7025717) B7025717
theorem B1368211 : Blo 1215425 1368211 := bstep (se 1 (by rfl) ⟨1026158, by rfl⟩ : syracuseStep 1368211 = 2052317) B2052317
theorem B2736305 : Blo 1215425 2736305 := bstep (se 2 (by rfl) ⟨1026114, by rfl⟩ : syracuseStep 2736305 = 2052229) B2052229
theorem B3080369 : Blo 1215425 3080369 := bstep (se 2 (by rfl) ⟨1155138, by rfl⟩ : syracuseStep 3080369 = 2310277) B2310277
theorem B2736323 : Blo 1215425 2736323 := bstep (se 1 (by rfl) ⟨2052242, by rfl⟩ : syracuseStep 2736323 = 4104485) B4104485
theorem B1540291 : Blo 1215425 1540291 := bstep (se 1 (by rfl) ⟨1155218, by rfl⟩ : syracuseStep 1540291 = 2310437) B2310437
theorem B2310353 : Blo 1215425 2310353 := bstep (se 2 (by rfl) ⟨866382, by rfl⟩ : syracuseStep 2310353 = 1732765) B1732765
theorem B9240803 : Blo 1215425 9240803 := bstep (se 1 (by rfl) ⟨6930602, by rfl⟩ : syracuseStep 9240803 = 13861205) B13861205
theorem B2597123 : Blo 1215425 2597123 := bstep (se 1 (by rfl) ⟨1947842, by rfl⟩ : syracuseStep 2597123 = 3895685) B3895685
theorem B26665237 : Blo 1215425 26665237 := bstep (se 6 (by rfl) ⟨624966, by rfl⟩ : syracuseStep 26665237 = 1249933) B1249933
theorem B1368355 : Blo 1215425 1368355 := bstep (se 1 (by rfl) ⟨1026266, by rfl⟩ : syracuseStep 1368355 = 2052533) B2052533
theorem B1540387 : Blo 1215425 1540387 := bstep (se 1 (by rfl) ⟨1155290, by rfl⟩ : syracuseStep 1540387 = 2310581) B2310581
theorem B2924849 : Blo 1215425 2924849 := bstep (se 2 (by rfl) ⟨1096818, by rfl⟩ : syracuseStep 2924849 = 2193637) B2193637
theorem B4104593 : Blo 1215425 4104593 := bstep (se 2 (by rfl) ⟨1539222, by rfl⟩ : syracuseStep 4104593 = 3078445) B3078445
theorem B1368499 : Blo 1215425 1368499 := bstep (se 1 (by rfl) ⟨1026374, by rfl⟩ : syracuseStep 1368499 = 2052749) B2052749
theorem B7799237 : Blo 1215425 7799237 := bstep (se 4 (by rfl) ⟨731178, by rfl⟩ : syracuseStep 7799237 = 1462357) B1462357
theorem B2736593 : Blo 1215425 2736593 := bstep (se 2 (by rfl) ⟨1026222, by rfl⟩ : syracuseStep 2736593 = 2052445) B2052445
theorem B2736611 : Blo 1215425 2736611 := bstep (se 1 (by rfl) ⟨2052458, by rfl⟩ : syracuseStep 2736611 = 4104917) B4104917
theorem B1368643 : Blo 1215425 1368643 := bstep (se 1 (by rfl) ⟨1026482, by rfl⟩ : syracuseStep 1368643 = 2052965) B2052965
theorem B4383409 : Blo 1215425 4383409 := bstep (se 2 (by rfl) ⟨1643778, by rfl⟩ : syracuseStep 4383409 = 3287557) B3287557
theorem B6242993 : Blo 1215425 6242993 := bstep (se 2 (by rfl) ⟨2341122, by rfl⟩ : syracuseStep 6242993 = 4682245) B4682245
theorem B1368787 : Blo 1215425 1368787 := bstep (se 1 (by rfl) ⟨1026590, by rfl⟩ : syracuseStep 1368787 = 2053181) B2053181
theorem B2736881 : Blo 1215425 2736881 := bstep (se 2 (by rfl) ⟨1026330, by rfl⟩ : syracuseStep 2736881 = 2052661) B2052661
theorem B2736899 : Blo 1215425 2736899 := bstep (se 1 (by rfl) ⟨2052674, by rfl⟩ : syracuseStep 2736899 = 4105349) B4105349
theorem B5849891 : Blo 1215425 5849891 := bstep (se 1 (by rfl) ⟨4387418, by rfl⟩ : syracuseStep 5849891 = 8774837) B8774837
theorem B2081585 : Blo 1215425 2081585 := bstep (se 2 (by rfl) ⟨780594, by rfl⟩ : syracuseStep 2081585 = 1561189) B1561189
theorem B1368931 : Blo 1215425 1368931 := bstep (se 1 (by rfl) ⟨1026698, by rfl⟩ : syracuseStep 1368931 = 2053397) B2053397
theorem B1778563 : Blo 1215425 1778563 := bstep (se 1 (by rfl) ⟨1333922, by rfl⟩ : syracuseStep 1778563 = 2667845) B2667845
theorem B4105133 : Blo 1215425 4105133 := bstep (se 3 (by rfl) ⟨769712, by rfl⟩ : syracuseStep 4105133 = 1539425) B1539425
theorem B2810819 : Blo 1215425 2810819 := bstep (se 1 (by rfl) ⟨2108114, by rfl⟩ : syracuseStep 2810819 = 4216229) B4216229
theorem B4105187 : Blo 1215425 4105187 := bstep (se 1 (by rfl) ⟨3078890, by rfl⟩ : syracuseStep 4105187 = 6157781) B6157781
theorem B4621283 : Blo 1215425 4621283 := bstep (se 1 (by rfl) ⟨3465962, by rfl⟩ : syracuseStep 4621283 = 6931925) B6931925
theorem B1369075 : Blo 1215425 1369075 := bstep (se 1 (by rfl) ⟨1026806, by rfl⟩ : syracuseStep 1369075 = 2053613) B2053613
theorem B2737169 : Blo 1215425 2737169 := bstep (se 2 (by rfl) ⟨1026438, by rfl⟩ : syracuseStep 2737169 = 2052877) B2052877
theorem B2737187 : Blo 1215425 2737187 := bstep (se 1 (by rfl) ⟨2052890, by rfl⟩ : syracuseStep 2737187 = 4105781) B4105781
theorem B2597969 : Blo 1215425 2597969 := bstep (se 2 (by rfl) ⟨974238, by rfl⟩ : syracuseStep 2597969 = 1948477) B1948477
theorem B6161507 : Blo 1215425 6161507 := bstep (se 1 (by rfl) ⟨4621130, by rfl⟩ : syracuseStep 6161507 = 9242261) B9242261
theorem B1369219 : Blo 1215425 1369219 := bstep (se 1 (by rfl) ⟨1026914, by rfl⟩ : syracuseStep 1369219 = 2053829) B2053829
theorem B3466385 : Blo 1215425 3466385 := bstep (se 2 (by rfl) ⟨1299894, by rfl⟩ : syracuseStep 3466385 = 2599789) B2599789
theorem B3081361 : Blo 1215425 3081361 := bstep (se 2 (by rfl) ⟨1155510, by rfl⟩ : syracuseStep 3081361 = 2311021) B2311021
theorem B4105457 : Blo 1215425 4105457 := bstep (se 2 (by rfl) ⟨1539546, by rfl⟩ : syracuseStep 4105457 = 3079093) B3079093
theorem B10528013 : Blo 1215425 10528013 := bstep (se 3 (by rfl) ⟨1974002, by rfl⟩ : syracuseStep 10528013 = 3948005) B3948005
theorem B1369363 : Blo 1215425 1369363 := bstep (se 1 (by rfl) ⟨1027022, by rfl⟩ : syracuseStep 1369363 = 2054045) B2054045
theorem B2737457 : Blo 1215425 2737457 := bstep (se 2 (by rfl) ⟨1026546, by rfl⟩ : syracuseStep 2737457 = 2053093) B2053093
theorem B2737475 : Blo 1215425 2737475 := bstep (se 1 (by rfl) ⟨2053106, by rfl⟩ : syracuseStep 2737475 = 4106213) B4106213
theorem B3466577 : Blo 1215425 3466577 := bstep (se 2 (by rfl) ⟨1299966, by rfl⟩ : syracuseStep 3466577 = 2599933) B2599933
theorem B3122563 : Blo 1215425 3122563 := bstep (se 1 (by rfl) ⟨2341922, by rfl⟩ : syracuseStep 3122563 = 4683845) B4683845
theorem B1369507 : Blo 1215425 1369507 := bstep (se 1 (by rfl) ⟨1027130, by rfl⟩ : syracuseStep 1369507 = 2054261) B2054261
theorem B1754561 : Blo 1215425 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B2737745 : Blo 1215425 2737745 := bstep (se 2 (by rfl) ⟨1026654, by rfl⟩ : syracuseStep 2737745 = 2053309) B2053309
theorem B2737763 : Blo 1215425 2737763 := bstep (se 1 (by rfl) ⟨2053322, by rfl⟩ : syracuseStep 2737763 = 4106645) B4106645
theorem B3696301 : Blo 1215425 3696301 := bstep (se 3 (by rfl) ⟨693056, by rfl⟩ : syracuseStep 3696301 = 1386113) B1386113
theorem B4105997 : Blo 1215425 4105997 := bstep (se 3 (by rfl) ⟨769874, by rfl⟩ : syracuseStep 4105997 = 1539749) B1539749
theorem B14042933 : Blo 1215425 14042933 := bstep (se 5 (by rfl) ⟨658262, by rfl⟩ : syracuseStep 14042933 = 1316525) B1316525
theorem B4106051 : Blo 1215425 4106051 := bstep (se 1 (by rfl) ⟨3079538, by rfl⟩ : syracuseStep 4106051 = 6159077) B6159077
theorem B3286865 : Blo 1215425 3286865 := bstep (se 2 (by rfl) ⟨1232574, by rfl⟩ : syracuseStep 3286865 = 2465149) B2465149
theorem B2738033 : Blo 1215425 2738033 := bstep (se 2 (by rfl) ⟨1026762, by rfl⟩ : syracuseStep 2738033 = 2053525) B2053525
theorem B2738051 : Blo 1215425 2738051 := bstep (se 1 (by rfl) ⟨2053538, by rfl⟩ : syracuseStep 2738051 = 4107077) B4107077
theorem B6162317 : Blo 1215425 6162317 := bstep (se 3 (by rfl) ⟨1155434, by rfl⟩ : syracuseStep 6162317 = 2310869) B2310869
theorem B11241413 : Blo 1215425 11241413 := bstep (se 4 (by rfl) ⟨1053882, by rfl⟩ : syracuseStep 11241413 = 2107765) B2107765
theorem B4622285 : Blo 1215425 4622285 := bstep (se 3 (by rfl) ⟨866678, by rfl⟩ : syracuseStep 4622285 = 1733357) B1733357
theorem B2631665 : Blo 1215425 2631665 := bstep (se 2 (by rfl) ⟨986874, by rfl⟩ : syracuseStep 2631665 = 1973749) B1973749
theorem B1730641 : Blo 1215425 1730641 := bstep (se 2 (by rfl) ⟨648990, by rfl⟩ : syracuseStep 1730641 = 1297981) B1297981
theorem B4106321 : Blo 1215425 4106321 := bstep (se 2 (by rfl) ⟨1539870, by rfl⟩ : syracuseStep 4106321 = 3079741) B3079741
theorem B10389617 : Blo 1215425 10389617 := bstep (se 2 (by rfl) ⟨3896106, by rfl⟩ : syracuseStep 10389617 = 7792213) B7792213
theorem B8767601 : Blo 1215425 8767601 := bstep (se 2 (by rfl) ⟨3287850, by rfl⟩ : syracuseStep 8767601 = 6575701) B6575701
theorem B2738321 : Blo 1215425 2738321 := bstep (se 2 (by rfl) ⟨1026870, by rfl⟩ : syracuseStep 2738321 = 2053741) B2053741
theorem B2738339 : Blo 1215425 2738339 := bstep (se 1 (by rfl) ⟨2053754, by rfl⟩ : syracuseStep 2738339 = 4107509) B4107509
theorem B3287213 : Blo 1215425 3287213 := bstep (se 3 (by rfl) ⟨616352, by rfl⟩ : syracuseStep 3287213 = 1232705) B1232705
theorem B1730737 : Blo 1215425 1730737 := bstep (se 2 (by rfl) ⟨649026, by rfl⟩ : syracuseStep 1730737 = 1298053) B1298053
theorem B1460435 : Blo 1215425 1460435 := bstep (se 1 (by rfl) ⟨1095326, by rfl⟩ : syracuseStep 1460435 = 2190653) B2190653
theorem B4442339 : Blo 1215425 4442339 := bstep (se 1 (by rfl) ⟨3331754, by rfl⟩ : syracuseStep 4442339 = 6663509) B6663509
theorem B35064035 : Blo 1215425 35064035 := bstep (se 1 (by rfl) ⟨26298026, by rfl⟩ : syracuseStep 35064035 = 52596053) B52596053
theorem B3557699 : Blo 1215425 3557699 := bstep (se 1 (by rfl) ⟨2668274, by rfl⟩ : syracuseStep 3557699 = 5336549) B5336549
theorem B6752645 : Blo 1215425 6752645 := bstep (se 4 (by rfl) ⟨633060, by rfl⟩ : syracuseStep 6752645 = 1266121) B1266121
theorem B2738609 : Blo 1215425 2738609 := bstep (se 2 (by rfl) ⟨1026978, by rfl⟩ : syracuseStep 2738609 = 2053957) B2053957
theorem B2738627 : Blo 1215425 2738627 := bstep (se 1 (by rfl) ⟨2053970, by rfl⟩ : syracuseStep 2738627 = 4107941) B4107941
theorem B3287537 : Blo 1215425 3287537 := bstep (se 2 (by rfl) ⟨1232826, by rfl⟩ : syracuseStep 3287537 = 2465653) B2465653
theorem B15600113 : Blo 1215425 15600113 := bstep (se 2 (by rfl) ⟨5850042, by rfl⟩ : syracuseStep 15600113 = 11700085) B11700085
theorem B9357893 : Blo 1215425 9357893 := bstep (se 4 (by rfl) ⟨877302, by rfl⟩ : syracuseStep 9357893 = 1754605) B1754605
theorem B3508817 : Blo 1215425 3508817 := bstep (se 2 (by rfl) ⟨1315806, by rfl⟩ : syracuseStep 3508817 = 2631613) B2631613
theorem B4106861 : Blo 1215425 4106861 := bstep (se 3 (by rfl) ⟨770036, by rfl⟩ : syracuseStep 4106861 = 1540073) B1540073
theorem B6154865 : Blo 1215425 6154865 := bstep (se 2 (by rfl) ⟨2308074, by rfl⟩ : syracuseStep 6154865 = 4616149) B4616149
theorem B1387139 : Blo 1215425 1387139 := bstep (se 1 (by rfl) ⟨1040354, by rfl⟩ : syracuseStep 1387139 = 2080709) B2080709
theorem B13855373 : Blo 1215425 13855373 := bstep (se 3 (by rfl) ⟨2597882, by rfl⟩ : syracuseStep 13855373 = 5195765) B5195765
theorem B1731233 : Blo 1215425 1731233 := bstep (se 2 (by rfl) ⟨649212, by rfl⟩ : syracuseStep 1731233 = 1298425) B1298425
theorem B4106915 : Blo 1215425 4106915 := bstep (se 1 (by rfl) ⟨3080186, by rfl⟩ : syracuseStep 4106915 = 6160373) B6160373
theorem B2738897 : Blo 1215425 2738897 := bstep (se 2 (by rfl) ⟨1027086, by rfl⟩ : syracuseStep 2738897 = 2054173) B2054173
theorem B2738915 : Blo 1215425 2738915 := bstep (se 1 (by rfl) ⟨2054186, by rfl⟩ : syracuseStep 2738915 = 4108373) B4108373
theorem B4934449 : Blo 1215425 4934449 := bstep (se 2 (by rfl) ⟨1850418, by rfl⟩ : syracuseStep 4934449 = 3700837) B3700837
theorem B4934513 : Blo 1215425 4934513 := bstep (se 2 (by rfl) ⟨1850442, by rfl⟩ : syracuseStep 4934513 = 3700885) B3700885
theorem B5196707 : Blo 1215425 5196707 := bstep (se 1 (by rfl) ⟨3897530, by rfl⟩ : syracuseStep 5196707 = 7795061) B7795061
theorem B4107185 : Blo 1215425 4107185 := bstep (se 2 (by rfl) ⟨1540194, by rfl⟩ : syracuseStep 4107185 = 3080389) B3080389
theorem B1215427 : Blo 1215425 1215427 := bstep (se 1 (by rfl) ⟨911570, by rfl⟩ : syracuseStep 1215427 = 1823141) B1823141
theorem B1215443 : Blo 1215425 1215443 := bstep (se 1 (by rfl) ⟨911582, by rfl⟩ : syracuseStep 1215443 = 1823165) B1823165
theorem B2051041 : Blo 1215425 2051041 := bstep (se 2 (by rfl) ⟨769140, by rfl⟩ : syracuseStep 2051041 = 1538281) B1538281
theorem B1215459 : Blo 1215425 1215459 := bstep (se 1 (by rfl) ⟨911594, by rfl⟩ : syracuseStep 1215459 = 1823189) B1823189
theorem B2739185 : Blo 1215425 2739185 := bstep (se 2 (by rfl) ⟨1027194, by rfl⟩ : syracuseStep 2739185 = 2054389) B2054389
theorem B1215475 : Blo 1215425 1215475 := bstep (se 1 (by rfl) ⟨911606, by rfl⟩ : syracuseStep 1215475 = 1823213) B1823213
theorem B2051075 : Blo 1215425 2051075 := bstep (se 1 (by rfl) ⟨1538306, by rfl⟩ : syracuseStep 2051075 = 3076613) B3076613
theorem B1215491 : Blo 1215425 1215491 := bstep (se 1 (by rfl) ⟨911618, by rfl⟩ : syracuseStep 1215491 = 1823237) B1823237
theorem B2739203 : Blo 1215425 2739203 := bstep (se 1 (by rfl) ⟨2054402, by rfl⟩ : syracuseStep 2739203 = 4108805) B4108805
theorem B1215507 : Blo 1215425 1215507 := bstep (se 1 (by rfl) ⟨911630, by rfl⟩ : syracuseStep 1215507 = 1823261) B1823261
theorem B1215523 : Blo 1215425 1215523 := bstep (se 1 (by rfl) ⟨911642, by rfl⟩ : syracuseStep 1215523 = 1823285) B1823285
theorem B1215539 : Blo 1215425 1215539 := bstep (se 1 (by rfl) ⟨911654, by rfl⟩ : syracuseStep 1215539 = 1823309) B1823309
theorem B1215555 : Blo 1215425 1215555 := bstep (se 1 (by rfl) ⟨911666, by rfl⟩ : syracuseStep 1215555 = 1823333) B1823333
theorem B1215571 : Blo 1215425 1215571 := bstep (se 1 (by rfl) ⟨911678, by rfl⟩ : syracuseStep 1215571 = 1823357) B1823357
theorem B6237283 : Blo 1215425 6237283 := bstep (se 1 (by rfl) ⟨4677962, by rfl⟩ : syracuseStep 6237283 = 9355925) B9355925
theorem B1215587 : Blo 1215425 1215587 := bstep (se 1 (by rfl) ⟨911690, by rfl⟩ : syracuseStep 1215587 = 1823381) B1823381
theorem B1215603 : Blo 1215425 1215603 := bstep (se 1 (by rfl) ⟨911702, by rfl⟩ : syracuseStep 1215603 = 1823405) B1823405
theorem B2051203 : Blo 1215425 2051203 := bstep (se 1 (by rfl) ⟨1538402, by rfl⟩ : syracuseStep 2051203 = 3076805) B3076805
theorem B1215619 : Blo 1215425 1215619 := bstep (se 1 (by rfl) ⟨911714, by rfl⟩ : syracuseStep 1215619 = 1823429) B1823429
theorem B2632835 : Blo 1215425 2632835 := bstep (se 1 (by rfl) ⟨1974626, by rfl⟩ : syracuseStep 2632835 = 3949253) B3949253
theorem B1215635 : Blo 1215425 1215635 := bstep (se 1 (by rfl) ⟨911726, by rfl⟩ : syracuseStep 1215635 = 1823453) B1823453
theorem B1215651 : Blo 1215425 1215651 := bstep (se 1 (by rfl) ⟨911738, by rfl⟩ : syracuseStep 1215651 = 1823477) B1823477
theorem B1215667 : Blo 1215425 1215667 := bstep (se 1 (by rfl) ⟨911750, by rfl⟩ : syracuseStep 1215667 = 1823501) B1823501
theorem B1215683 : Blo 1215425 1215683 := bstep (se 1 (by rfl) ⟨911762, by rfl⟩ : syracuseStep 1215683 = 1823525) B1823525
theorem B1215699 : Blo 1215425 1215699 := bstep (se 1 (by rfl) ⟨911774, by rfl⟩ : syracuseStep 1215699 = 1823549) B1823549
theorem B1215715 : Blo 1215425 1215715 := bstep (se 1 (by rfl) ⟨911786, by rfl⟩ : syracuseStep 1215715 = 1823573) B1823573
theorem B9358577 : Blo 1215425 9358577 := bstep (se 2 (by rfl) ⟨3509466, by rfl⟩ : syracuseStep 9358577 = 7018933) B7018933
theorem B1215731 : Blo 1215425 1215731 := bstep (se 1 (by rfl) ⟨911798, by rfl⟩ : syracuseStep 1215731 = 1823597) B1823597
theorem B1215747 : Blo 1215425 1215747 := bstep (se 1 (by rfl) ⟨911810, by rfl⟩ : syracuseStep 1215747 = 1823621) B1823621
theorem B2051345 : Blo 1215425 2051345 := bstep (se 2 (by rfl) ⟨769254, by rfl⟩ : syracuseStep 2051345 = 1538509) B1538509
theorem B1215763 : Blo 1215425 1215763 := bstep (se 1 (by rfl) ⟨911822, by rfl⟩ : syracuseStep 1215763 = 1823645) B1823645
theorem B1215779 : Blo 1215425 1215779 := bstep (se 1 (by rfl) ⟨911834, by rfl⟩ : syracuseStep 1215779 = 1823669) B1823669
theorem B1215795 : Blo 1215425 1215795 := bstep (se 1 (by rfl) ⟨911846, by rfl⟩ : syracuseStep 1215795 = 1823693) B1823693
theorem B1215811 : Blo 1215425 1215811 := bstep (se 1 (by rfl) ⟨911858, by rfl⟩ : syracuseStep 1215811 = 1823717) B1823717
theorem B1215827 : Blo 1215425 1215827 := bstep (se 1 (by rfl) ⟨911870, by rfl⟩ : syracuseStep 1215827 = 1823741) B1823741
theorem B1215843 : Blo 1215425 1215843 := bstep (se 1 (by rfl) ⟨911882, by rfl⟩ : syracuseStep 1215843 = 1823765) B1823765
theorem B1215859 : Blo 1215425 1215859 := bstep (se 1 (by rfl) ⟨911894, by rfl⟩ : syracuseStep 1215859 = 1823789) B1823789
theorem B1215875 : Blo 1215425 1215875 := bstep (se 1 (by rfl) ⟨911906, by rfl⟩ : syracuseStep 1215875 = 1823813) B1823813
theorem B2051473 : Blo 1215425 2051473 := bstep (se 2 (by rfl) ⟨769302, by rfl⟩ : syracuseStep 2051473 = 1538605) B1538605
theorem B1215891 : Blo 1215425 1215891 := bstep (se 1 (by rfl) ⟨911918, by rfl⟩ : syracuseStep 1215891 = 1823837) B1823837
theorem B1215907 : Blo 1215425 1215907 := bstep (se 1 (by rfl) ⟨911930, by rfl⟩ : syracuseStep 1215907 = 1823861) B1823861
theorem B2051507 : Blo 1215425 2051507 := bstep (se 1 (by rfl) ⟨1538630, by rfl⟩ : syracuseStep 2051507 = 3077261) B3077261
theorem B1215923 : Blo 1215425 1215923 := bstep (se 1 (by rfl) ⟨911942, by rfl⟩ : syracuseStep 1215923 = 1823885) B1823885
theorem B1215939 : Blo 1215425 1215939 := bstep (se 1 (by rfl) ⟨911954, by rfl⟩ : syracuseStep 1215939 = 1823909) B1823909
theorem B4107725 : Blo 1215425 4107725 := bstep (se 3 (by rfl) ⟨770198, by rfl⟩ : syracuseStep 4107725 = 1540397) B1540397
theorem B1215955 : Blo 1215425 1215955 := bstep (se 1 (by rfl) ⟨911966, by rfl⟩ : syracuseStep 1215955 = 1823933) B1823933
theorem B1215971 : Blo 1215425 1215971 := bstep (se 1 (by rfl) ⟨911978, by rfl⟩ : syracuseStep 1215971 = 1823957) B1823957
theorem B1215987 : Blo 1215425 1215987 := bstep (se 1 (by rfl) ⟨911990, by rfl⟩ : syracuseStep 1215987 = 1823981) B1823981
theorem B1216003 : Blo 1215425 1216003 := bstep (se 1 (by rfl) ⟨912002, by rfl⟩ : syracuseStep 1216003 = 1824005) B1824005
theorem B1732099 : Blo 1215425 1732099 := bstep (se 1 (by rfl) ⟨1299074, by rfl⟩ : syracuseStep 1732099 = 2598149) B2598149
theorem B4107779 : Blo 1215425 4107779 := bstep (se 1 (by rfl) ⟨3080834, by rfl⟩ : syracuseStep 4107779 = 6161669) B6161669
theorem B1216019 : Blo 1215425 1216019 := bstep (se 1 (by rfl) ⟨912014, by rfl⟩ : syracuseStep 1216019 = 1824029) B1824029
theorem B1216035 : Blo 1215425 1216035 := bstep (se 1 (by rfl) ⟨912026, by rfl⟩ : syracuseStep 1216035 = 1824053) B1824053
theorem B2051635 : Blo 1215425 2051635 := bstep (se 1 (by rfl) ⟨1538726, by rfl⟩ : syracuseStep 2051635 = 3077453) B3077453
theorem B1216051 : Blo 1215425 1216051 := bstep (se 1 (by rfl) ⟨912038, by rfl⟩ : syracuseStep 1216051 = 1824077) B1824077
theorem B1216067 : Blo 1215425 1216067 := bstep (se 1 (by rfl) ⟨912050, by rfl⟩ : syracuseStep 1216067 = 1824101) B1824101
theorem B1216083 : Blo 1215425 1216083 := bstep (se 1 (by rfl) ⟨912062, by rfl⟩ : syracuseStep 1216083 = 1824125) B1824125
theorem B1216099 : Blo 1215425 1216099 := bstep (se 1 (by rfl) ⟨912074, by rfl⟩ : syracuseStep 1216099 = 1824149) B1824149
theorem B1732195 : Blo 1215425 1732195 := bstep (se 1 (by rfl) ⟨1299146, by rfl⟩ : syracuseStep 1732195 = 2598293) B2598293
theorem B1216115 : Blo 1215425 1216115 := bstep (se 1 (by rfl) ⟨912086, by rfl⟩ : syracuseStep 1216115 = 1824173) B1824173
theorem B1216131 : Blo 1215425 1216131 := bstep (se 1 (by rfl) ⟨912098, by rfl⟩ : syracuseStep 1216131 = 1824197) B1824197
theorem B3894929 : Blo 1215425 3894929 := bstep (se 2 (by rfl) ⟨1460598, by rfl⟩ : syracuseStep 3894929 = 2921197) B2921197
theorem B1216147 : Blo 1215425 1216147 := bstep (se 1 (by rfl) ⟨912110, by rfl⟩ : syracuseStep 1216147 = 1824221) B1824221
theorem B1216163 : Blo 1215425 1216163 := bstep (se 1 (by rfl) ⟨912122, by rfl⟩ : syracuseStep 1216163 = 1824245) B1824245
theorem B1216179 : Blo 1215425 1216179 := bstep (se 1 (by rfl) ⟨912134, by rfl⟩ : syracuseStep 1216179 = 1824269) B1824269
theorem B2051777 : Blo 1215425 2051777 := bstep (se 2 (by rfl) ⟨769416, by rfl⟩ : syracuseStep 2051777 = 1538833) B1538833
theorem B3894979 : Blo 1215425 3894979 := bstep (se 1 (by rfl) ⟨2921234, by rfl⟩ : syracuseStep 3894979 = 5842469) B5842469
theorem B1216195 : Blo 1215425 1216195 := bstep (se 1 (by rfl) ⟨912146, by rfl⟩ : syracuseStep 1216195 = 1824293) B1824293
theorem B1216211 : Blo 1215425 1216211 := bstep (se 1 (by rfl) ⟨912158, by rfl⟩ : syracuseStep 1216211 = 1824317) B1824317
theorem B1216227 : Blo 1215425 1216227 := bstep (se 1 (by rfl) ⟨912170, by rfl⟩ : syracuseStep 1216227 = 1824341) B1824341
theorem B1216243 : Blo 1215425 1216243 := bstep (se 1 (by rfl) ⟨912182, by rfl⟩ : syracuseStep 1216243 = 1824365) B1824365
theorem B1216259 : Blo 1215425 1216259 := bstep (se 1 (by rfl) ⟨912194, by rfl⟩ : syracuseStep 1216259 = 1824389) B1824389
theorem B6926093 : Blo 1215425 6926093 := bstep (se 3 (by rfl) ⟨1298642, by rfl⟩ : syracuseStep 6926093 = 2597285) B2597285
theorem B4108049 : Blo 1215425 4108049 := bstep (se 2 (by rfl) ⟨1540518, by rfl⟩ : syracuseStep 4108049 = 3081037) B3081037
theorem B1216275 : Blo 1215425 1216275 := bstep (se 1 (by rfl) ⟨912206, by rfl⟩ : syracuseStep 1216275 = 1824413) B1824413
theorem B1216291 : Blo 1215425 1216291 := bstep (se 1 (by rfl) ⟨912218, by rfl⟩ : syracuseStep 1216291 = 1824437) B1824437
theorem B1216307 : Blo 1215425 1216307 := bstep (se 1 (by rfl) ⟨912230, by rfl⟩ : syracuseStep 1216307 = 1824461) B1824461
theorem B2051905 : Blo 1215425 2051905 := bstep (se 2 (by rfl) ⟨769464, by rfl⟩ : syracuseStep 2051905 = 1538929) B1538929
theorem B1216323 : Blo 1215425 1216323 := bstep (se 1 (by rfl) ⟨912242, by rfl⟩ : syracuseStep 1216323 = 1824485) B1824485
theorem B3288899 : Blo 1215425 3288899 := bstep (se 1 (by rfl) ⟨2466674, by rfl⟩ : syracuseStep 3288899 = 4933349) B4933349
theorem B1216339 : Blo 1215425 1216339 := bstep (se 1 (by rfl) ⟨912254, by rfl⟩ : syracuseStep 1216339 = 1824509) B1824509
theorem B2051939 : Blo 1215425 2051939 := bstep (se 1 (by rfl) ⟨1538954, by rfl⟩ : syracuseStep 2051939 = 3077909) B3077909
theorem B1216355 : Blo 1215425 1216355 := bstep (se 1 (by rfl) ⟨912266, by rfl⟩ : syracuseStep 1216355 = 1824533) B1824533
theorem B3288941 : Blo 1215425 3288941 := bstep (se 3 (by rfl) ⟨616676, by rfl⟩ : syracuseStep 3288941 = 1233353) B1233353
theorem B1216371 : Blo 1215425 1216371 := bstep (se 1 (by rfl) ⟨912278, by rfl⟩ : syracuseStep 1216371 = 1824557) B1824557
theorem B1216387 : Blo 1215425 1216387 := bstep (se 1 (by rfl) ⟨912290, by rfl⟩ : syracuseStep 1216387 = 1824581) B1824581
theorem B1216403 : Blo 1215425 1216403 := bstep (se 1 (by rfl) ⟨912302, by rfl⟩ : syracuseStep 1216403 = 1824605) B1824605
theorem B1216419 : Blo 1215425 1216419 := bstep (se 1 (by rfl) ⟨912314, by rfl⟩ : syracuseStep 1216419 = 1824629) B1824629
theorem B1216435 : Blo 1215425 1216435 := bstep (se 1 (by rfl) ⟨912326, by rfl⟩ : syracuseStep 1216435 = 1824653) B1824653
theorem B1216451 : Blo 1215425 1216451 := bstep (se 1 (by rfl) ⟨912338, by rfl⟩ : syracuseStep 1216451 = 1824677) B1824677
theorem B1216467 : Blo 1215425 1216467 := bstep (se 1 (by rfl) ⟨912350, by rfl⟩ : syracuseStep 1216467 = 1824701) B1824701
theorem B2052067 : Blo 1215425 2052067 := bstep (se 1 (by rfl) ⟨1539050, by rfl⟩ : syracuseStep 2052067 = 3078101) B3078101
theorem B1216483 : Blo 1215425 1216483 := bstep (se 1 (by rfl) ⟨912362, by rfl⟩ : syracuseStep 1216483 = 1824725) B1824725
theorem B1216499 : Blo 1215425 1216499 := bstep (se 1 (by rfl) ⟨912374, by rfl⟩ : syracuseStep 1216499 = 1824749) B1824749
theorem B1216515 : Blo 1215425 1216515 := bstep (se 1 (by rfl) ⟨912386, by rfl⟩ : syracuseStep 1216515 = 1824773) B1824773
theorem B1216531 : Blo 1215425 1216531 := bstep (se 1 (by rfl) ⟨912398, by rfl⟩ : syracuseStep 1216531 = 1824797) B1824797
theorem B6156323 : Blo 1215425 6156323 := bstep (se 1 (by rfl) ⟨4617242, by rfl⟩ : syracuseStep 6156323 = 9234485) B9234485
theorem B1216547 : Blo 1215425 1216547 := bstep (se 1 (by rfl) ⟨912410, by rfl⟩ : syracuseStep 1216547 = 1824821) B1824821
theorem B1216563 : Blo 1215425 1216563 := bstep (se 1 (by rfl) ⟨912422, by rfl⟩ : syracuseStep 1216563 = 1824845) B1824845
theorem B1216579 : Blo 1215425 1216579 := bstep (se 1 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 1216579 = 1824869) B1824869
theorem B3461201 : Blo 1215425 3461201 := bstep (se 2 (by rfl) ⟨1297950, by rfl⟩ : syracuseStep 3461201 = 2595901) B2595901
theorem B1216595 : Blo 1215425 1216595 := bstep (se 1 (by rfl) ⟨912446, by rfl⟩ : syracuseStep 1216595 = 1824893) B1824893
theorem B1732691 : Blo 1215425 1732691 := bstep (se 1 (by rfl) ⟨1299518, by rfl⟩ : syracuseStep 1732691 = 2599037) B2599037
theorem B1216611 : Blo 1215425 1216611 := bstep (se 1 (by rfl) ⟨912458, by rfl⟩ : syracuseStep 1216611 = 1824917) B1824917
theorem B2052209 : Blo 1215425 2052209 := bstep (se 2 (by rfl) ⟨769578, by rfl⟩ : syracuseStep 2052209 = 1539157) B1539157
theorem B1216627 : Blo 1215425 1216627 := bstep (se 1 (by rfl) ⟨912470, by rfl⟩ : syracuseStep 1216627 = 1824941) B1824941
theorem B1216643 : Blo 1215425 1216643 := bstep (se 1 (by rfl) ⟨912482, by rfl⟩ : syracuseStep 1216643 = 1824965) B1824965
theorem B1216659 : Blo 1215425 1216659 := bstep (se 1 (by rfl) ⟨912494, by rfl⟩ : syracuseStep 1216659 = 1824989) B1824989
theorem B1216675 : Blo 1215425 1216675 := bstep (se 1 (by rfl) ⟨912506, by rfl⟩ : syracuseStep 1216675 = 1825013) B1825013
theorem B1216691 : Blo 1215425 1216691 := bstep (se 1 (by rfl) ⟨912518, by rfl⟩ : syracuseStep 1216691 = 1825037) B1825037
theorem B1216707 : Blo 1215425 1216707 := bstep (se 1 (by rfl) ⟨912530, by rfl⟩ : syracuseStep 1216707 = 1825061) B1825061
theorem B3952849 : Blo 1215425 3952849 := bstep (se 2 (by rfl) ⟨1482318, by rfl⟩ : syracuseStep 3952849 = 2964637) B2964637
theorem B1216723 : Blo 1215425 1216723 := bstep (se 1 (by rfl) ⟨912542, by rfl⟩ : syracuseStep 1216723 = 1825085) B1825085
theorem B1216739 : Blo 1215425 1216739 := bstep (se 1 (by rfl) ⟨912554, by rfl⟩ : syracuseStep 1216739 = 1825109) B1825109
theorem B2052337 : Blo 1215425 2052337 := bstep (se 2 (by rfl) ⟨769626, by rfl⟩ : syracuseStep 2052337 = 1539253) B1539253
theorem B2633969 : Blo 1215425 2633969 := bstep (se 2 (by rfl) ⟨987738, by rfl⟩ : syracuseStep 2633969 = 1975477) B1975477
theorem B1216755 : Blo 1215425 1216755 := bstep (se 1 (by rfl) ⟨912566, by rfl⟩ : syracuseStep 1216755 = 1825133) B1825133
theorem B1216771 : Blo 1215425 1216771 := bstep (se 1 (by rfl) ⟨912578, by rfl⟩ : syracuseStep 1216771 = 1825157) B1825157
theorem B2052371 : Blo 1215425 2052371 := bstep (se 1 (by rfl) ⟨1539278, by rfl⟩ : syracuseStep 2052371 = 3078557) B3078557
theorem B1216787 : Blo 1215425 1216787 := bstep (se 1 (by rfl) ⟨912590, by rfl⟩ : syracuseStep 1216787 = 1825181) B1825181
theorem B3559715 : Blo 1215425 3559715 := bstep (se 1 (by rfl) ⟨2669786, by rfl⟩ : syracuseStep 3559715 = 5339573) B5339573
theorem B1216803 : Blo 1215425 1216803 := bstep (se 1 (by rfl) ⟨912602, by rfl⟩ : syracuseStep 1216803 = 1825205) B1825205
theorem B4108589 : Blo 1215425 4108589 := bstep (se 3 (by rfl) ⟨770360, by rfl⟩ : syracuseStep 4108589 = 1540721) B1540721
theorem B1216819 : Blo 1215425 1216819 := bstep (se 1 (by rfl) ⟨912614, by rfl⟩ : syracuseStep 1216819 = 1825229) B1825229
theorem B1216835 : Blo 1215425 1216835 := bstep (se 1 (by rfl) ⟨912626, by rfl⟩ : syracuseStep 1216835 = 1825253) B1825253
theorem B1216851 : Blo 1215425 1216851 := bstep (se 1 (by rfl) ⟨912638, by rfl⟩ : syracuseStep 1216851 = 1825277) B1825277
theorem B1216867 : Blo 1215425 1216867 := bstep (se 1 (by rfl) ⟨912650, by rfl⟩ : syracuseStep 1216867 = 1825301) B1825301
theorem B4108643 : Blo 1215425 4108643 := bstep (se 1 (by rfl) ⟨3081482, by rfl⟩ : syracuseStep 4108643 = 6162965) B6162965
theorem B1216883 : Blo 1215425 1216883 := bstep (se 1 (by rfl) ⟨912662, by rfl⟩ : syracuseStep 1216883 = 1825325) B1825325
theorem B1216899 : Blo 1215425 1216899 := bstep (se 1 (by rfl) ⟨912674, by rfl⟩ : syracuseStep 1216899 = 1825349) B1825349
theorem B3895697 : Blo 1215425 3895697 := bstep (se 2 (by rfl) ⟨1460886, by rfl⟩ : syracuseStep 3895697 = 2921773) B2921773
theorem B2052499 : Blo 1215425 2052499 := bstep (se 1 (by rfl) ⟨1539374, by rfl⟩ : syracuseStep 2052499 = 3078749) B3078749
theorem B1560979 : Blo 1215425 1560979 := bstep (se 1 (by rfl) ⟨1170734, by rfl⟩ : syracuseStep 1560979 = 2341469) B2341469
theorem B1216915 : Blo 1215425 1216915 := bstep (se 1 (by rfl) ⟨912686, by rfl⟩ : syracuseStep 1216915 = 1825373) B1825373
theorem B1216931 : Blo 1215425 1216931 := bstep (se 1 (by rfl) ⟨912698, by rfl⟩ : syracuseStep 1216931 = 1825397) B1825397
theorem B1823153 : Blo 1215425 1823153 := bstep (se 2 (by rfl) ⟨683682, by rfl⟩ : syracuseStep 1823153 = 1367365) B1367365
theorem B1216947 : Blo 1215425 1216947 := bstep (se 1 (by rfl) ⟨912710, by rfl⟩ : syracuseStep 1216947 = 1825421) B1825421
theorem B1823171 : Blo 1215425 1823171 := bstep (se 1 (by rfl) ⟨1367378, by rfl⟩ : syracuseStep 1823171 = 2734757) B2734757
theorem B1216963 : Blo 1215425 1216963 := bstep (se 1 (by rfl) ⟨912722, by rfl⟩ : syracuseStep 1216963 = 1825445) B1825445
theorem B1216979 : Blo 1215425 1216979 := bstep (se 1 (by rfl) ⟨912734, by rfl⟩ : syracuseStep 1216979 = 1825469) B1825469
theorem B1823201 : Blo 1215425 1823201 := bstep (se 2 (by rfl) ⟨683700, by rfl⟩ : syracuseStep 1823201 = 1367401) B1367401
theorem B1216995 : Blo 1215425 1216995 := bstep (se 1 (by rfl) ⟨912746, by rfl⟩ : syracuseStep 1216995 = 1825493) B1825493
theorem B1823219 : Blo 1215425 1823219 := bstep (se 1 (by rfl) ⟨1367414, by rfl⟩ : syracuseStep 1823219 = 2734829) B2734829
theorem B1217011 : Blo 1215425 1217011 := bstep (se 1 (by rfl) ⟨912758, by rfl⟩ : syracuseStep 1217011 = 1825517) B1825517
theorem B1217027 : Blo 1215425 1217027 := bstep (se 1 (by rfl) ⟨912770, by rfl⟩ : syracuseStep 1217027 = 1825541) B1825541
theorem B10392077 : Blo 1215425 10392077 := bstep (se 3 (by rfl) ⟨1948514, by rfl⟩ : syracuseStep 10392077 = 3897029) B3897029
theorem B1823249 : Blo 1215425 1823249 := bstep (se 2 (by rfl) ⟨683718, by rfl⟩ : syracuseStep 1823249 = 1367437) B1367437
theorem B1217043 : Blo 1215425 1217043 := bstep (se 1 (by rfl) ⟨912782, by rfl⟩ : syracuseStep 1217043 = 1825565) B1825565
theorem B2052641 : Blo 1215425 2052641 := bstep (se 2 (by rfl) ⟨769740, by rfl⟩ : syracuseStep 2052641 = 1539481) B1539481
theorem B3076643 : Blo 1215425 3076643 := bstep (se 1 (by rfl) ⟨2307482, by rfl⟩ : syracuseStep 3076643 = 4614965) B4614965
theorem B1823267 : Blo 1215425 1823267 := bstep (se 1 (by rfl) ⟨1367450, by rfl⟩ : syracuseStep 1823267 = 2734901) B2734901
theorem B1217059 : Blo 1215425 1217059 := bstep (se 1 (by rfl) ⟨912794, by rfl⟩ : syracuseStep 1217059 = 1825589) B1825589
theorem B1217075 : Blo 1215425 1217075 := bstep (se 1 (by rfl) ⟨912806, by rfl⟩ : syracuseStep 1217075 = 1825613) B1825613
theorem B1823297 : Blo 1215425 1823297 := bstep (se 2 (by rfl) ⟨683736, by rfl⟩ : syracuseStep 1823297 = 1367473) B1367473
theorem B1217091 : Blo 1215425 1217091 := bstep (se 1 (by rfl) ⟨912818, by rfl⟩ : syracuseStep 1217091 = 1825637) B1825637
theorem B1823315 : Blo 1215425 1823315 := bstep (se 1 (by rfl) ⟨1367486, by rfl⟩ : syracuseStep 1823315 = 2734973) B2734973
theorem B1217107 : Blo 1215425 1217107 := bstep (se 1 (by rfl) ⟨912830, by rfl⟩ : syracuseStep 1217107 = 1825661) B1825661
theorem B1217123 : Blo 1215425 1217123 := bstep (se 1 (by rfl) ⟨912842, by rfl⟩ : syracuseStep 1217123 = 1825685) B1825685
theorem B1823345 : Blo 1215425 1823345 := bstep (se 2 (by rfl) ⟨683754, by rfl⟩ : syracuseStep 1823345 = 1367509) B1367509
theorem B1217139 : Blo 1215425 1217139 := bstep (se 1 (by rfl) ⟨912854, by rfl⟩ : syracuseStep 1217139 = 1825709) B1825709
theorem B1823363 : Blo 1215425 1823363 := bstep (se 1 (by rfl) ⟨1367522, by rfl⟩ : syracuseStep 1823363 = 2735045) B2735045
theorem B1217155 : Blo 1215425 1217155 := bstep (se 1 (by rfl) ⟨912866, by rfl⟩ : syracuseStep 1217155 = 1825733) B1825733
theorem B1217171 : Blo 1215425 1217171 := bstep (se 1 (by rfl) ⟨912878, by rfl⟩ : syracuseStep 1217171 = 1825757) B1825757
theorem B1823393 : Blo 1215425 1823393 := bstep (se 2 (by rfl) ⟨683772, by rfl⟩ : syracuseStep 1823393 = 1367545) B1367545
theorem B2052769 : Blo 1215425 2052769 := bstep (se 2 (by rfl) ⟨769788, by rfl⟩ : syracuseStep 2052769 = 1539577) B1539577
theorem B1217187 : Blo 1215425 1217187 := bstep (se 1 (by rfl) ⟨912890, by rfl⟩ : syracuseStep 1217187 = 1825781) B1825781
theorem B1823411 : Blo 1215425 1823411 := bstep (se 1 (by rfl) ⟨1367558, by rfl⟩ : syracuseStep 1823411 = 2735117) B2735117
theorem B1217203 : Blo 1215425 1217203 := bstep (se 1 (by rfl) ⟨912902, by rfl⟩ : syracuseStep 1217203 = 1825805) B1825805
theorem B2052803 : Blo 1215425 2052803 := bstep (se 1 (by rfl) ⟨1539602, by rfl⟩ : syracuseStep 2052803 = 3079205) B3079205
theorem B1217219 : Blo 1215425 1217219 := bstep (se 1 (by rfl) ⟨912914, by rfl⟩ : syracuseStep 1217219 = 1825829) B1825829
theorem B4616909 : Blo 1215425 4616909 := bstep (se 3 (by rfl) ⟨865670, by rfl⟩ : syracuseStep 4616909 = 1731341) B1731341
theorem B1823441 : Blo 1215425 1823441 := bstep (se 2 (by rfl) ⟨683790, by rfl⟩ : syracuseStep 1823441 = 1367581) B1367581
theorem B1733329 : Blo 1215425 1733329 := bstep (se 2 (by rfl) ⟨649998, by rfl⟩ : syracuseStep 1733329 = 1299997) B1299997
theorem B1217235 : Blo 1215425 1217235 := bstep (se 1 (by rfl) ⟨912926, by rfl⟩ : syracuseStep 1217235 = 1825853) B1825853
theorem B1823459 : Blo 1215425 1823459 := bstep (se 1 (by rfl) ⟨1367594, by rfl⟩ : syracuseStep 1823459 = 2735189) B2735189
theorem B15586019 : Blo 1215425 15586019 := bstep (se 1 (by rfl) ⟨11689514, by rfl⟩ : syracuseStep 15586019 = 23379029) B23379029
theorem B3699427 : Blo 1215425 3699427 := bstep (se 1 (by rfl) ⟨2774570, by rfl⟩ : syracuseStep 3699427 = 5549141) B5549141
theorem B1217251 : Blo 1215425 1217251 := bstep (se 1 (by rfl) ⟨912938, by rfl⟩ : syracuseStep 1217251 = 1825877) B1825877
theorem B1217267 : Blo 1215425 1217267 := bstep (se 1 (by rfl) ⟨912950, by rfl⟩ : syracuseStep 1217267 = 1825901) B1825901
theorem B1823489 : Blo 1215425 1823489 := bstep (se 2 (by rfl) ⟨683808, by rfl⟩ : syracuseStep 1823489 = 1367617) B1367617
theorem B1217283 : Blo 1215425 1217283 := bstep (se 1 (by rfl) ⟨912962, by rfl⟩ : syracuseStep 1217283 = 1825925) B1825925
theorem B1823507 : Blo 1215425 1823507 := bstep (se 1 (by rfl) ⟨1367630, by rfl⟩ : syracuseStep 1823507 = 2735261) B2735261
theorem B1217299 : Blo 1215425 1217299 := bstep (se 1 (by rfl) ⟨912974, by rfl⟩ : syracuseStep 1217299 = 1825949) B1825949
theorem B1217315 : Blo 1215425 1217315 := bstep (se 1 (by rfl) ⟨912986, by rfl⟩ : syracuseStep 1217315 = 1825973) B1825973
theorem B1823537 : Blo 1215425 1823537 := bstep (se 2 (by rfl) ⟨683826, by rfl⟩ : syracuseStep 1823537 = 1367653) B1367653
theorem B1217331 : Blo 1215425 1217331 := bstep (se 1 (by rfl) ⟨912998, by rfl⟩ : syracuseStep 1217331 = 1825997) B1825997
theorem B1823555 : Blo 1215425 1823555 := bstep (se 1 (by rfl) ⟨1367666, by rfl⟩ : syracuseStep 1823555 = 2735333) B2735333
theorem B2052931 : Blo 1215425 2052931 := bstep (se 1 (by rfl) ⟨1539698, by rfl⟩ : syracuseStep 2052931 = 3079397) B3079397
theorem B1217347 : Blo 1215425 1217347 := bstep (se 1 (by rfl) ⟨913010, by rfl⟩ : syracuseStep 1217347 = 1826021) B1826021
theorem B6157133 : Blo 1215425 6157133 := bstep (se 3 (by rfl) ⟨1154462, by rfl⟩ : syracuseStep 6157133 = 2308925) B2308925
theorem B1299283 : Blo 1215425 1299283 := bstep (se 1 (by rfl) ⟨974462, by rfl⟩ : syracuseStep 1299283 = 1948925) B1948925
theorem B1217363 : Blo 1215425 1217363 := bstep (se 1 (by rfl) ⟨913022, by rfl⟩ : syracuseStep 1217363 = 1826045) B1826045
theorem B1823585 : Blo 1215425 1823585 := bstep (se 2 (by rfl) ⟨683844, by rfl⟩ : syracuseStep 1823585 = 1367689) B1367689
theorem B1217379 : Blo 1215425 1217379 := bstep (se 1 (by rfl) ⟨913034, by rfl⟩ : syracuseStep 1217379 = 1826069) B1826069
theorem B5198705 : Blo 1215425 5198705 := bstep (se 2 (by rfl) ⟨1949514, by rfl⟩ : syracuseStep 5198705 = 3899029) B3899029
theorem B1823603 : Blo 1215425 1823603 := bstep (se 1 (by rfl) ⟨1367702, by rfl⟩ : syracuseStep 1823603 = 2735405) B2735405
theorem B1217395 : Blo 1215425 1217395 := bstep (se 1 (by rfl) ⟨913046, by rfl⟩ : syracuseStep 1217395 = 1826093) B1826093
theorem B1217411 : Blo 1215425 1217411 := bstep (se 1 (by rfl) ⟨913058, by rfl⟩ : syracuseStep 1217411 = 1826117) B1826117
theorem B4158353 : Blo 1215425 4158353 := bstep (se 2 (by rfl) ⟨1559382, by rfl⟩ : syracuseStep 4158353 = 3118765) B3118765
theorem B1823633 : Blo 1215425 1823633 := bstep (se 2 (by rfl) ⟨683862, by rfl⟩ : syracuseStep 1823633 = 1367725) B1367725
theorem B3896209 : Blo 1215425 3896209 := bstep (se 2 (by rfl) ⟨1461078, by rfl⟩ : syracuseStep 3896209 = 2922157) B2922157
theorem B1823651 : Blo 1215425 1823651 := bstep (se 1 (by rfl) ⟨1367738, by rfl⟩ : syracuseStep 1823651 = 2735477) B2735477
theorem B1823681 : Blo 1215425 1823681 := bstep (se 2 (by rfl) ⟨683880, by rfl⟩ : syracuseStep 1823681 = 1367761) B1367761
theorem B13849541 : Blo 1215425 13849541 := bstep (se 4 (by rfl) ⟨1298394, by rfl⟩ : syracuseStep 13849541 = 2596789) B2596789
theorem B2053073 : Blo 1215425 2053073 := bstep (se 2 (by rfl) ⟨769902, by rfl⟩ : syracuseStep 2053073 = 1539805) B1539805
theorem B1823699 : Blo 1215425 1823699 := bstep (se 1 (by rfl) ⟨1367774, by rfl⟩ : syracuseStep 1823699 = 2735549) B2735549
theorem B1823729 : Blo 1215425 1823729 := bstep (se 2 (by rfl) ⟨683898, by rfl⟩ : syracuseStep 1823729 = 1367797) B1367797
theorem B1823747 : Blo 1215425 1823747 := bstep (se 1 (by rfl) ⟨1367810, by rfl⟩ : syracuseStep 1823747 = 2735621) B2735621
theorem B1823777 : Blo 1215425 1823777 := bstep (se 2 (by rfl) ⟨683916, by rfl⟩ : syracuseStep 1823777 = 1367833) B1367833
theorem B1823795 : Blo 1215425 1823795 := bstep (se 1 (by rfl) ⟨1367846, by rfl⟩ : syracuseStep 1823795 = 2735693) B2735693
theorem B1823825 : Blo 1215425 1823825 := bstep (se 2 (by rfl) ⟨683934, by rfl⟩ : syracuseStep 1823825 = 1367869) B1367869
theorem B2053201 : Blo 1215425 2053201 := bstep (se 2 (by rfl) ⟨769950, by rfl⟩ : syracuseStep 2053201 = 1539901) B1539901
theorem B1823843 : Blo 1215425 1823843 := bstep (se 1 (by rfl) ⟨1367882, by rfl⟩ : syracuseStep 1823843 = 2735765) B2735765
theorem B2053235 : Blo 1215425 2053235 := bstep (se 1 (by rfl) ⟨1539926, by rfl⟩ : syracuseStep 2053235 = 3079853) B3079853
theorem B1823873 : Blo 1215425 1823873 := bstep (se 2 (by rfl) ⟨683952, by rfl⟩ : syracuseStep 1823873 = 1367905) B1367905
theorem B1823891 : Blo 1215425 1823891 := bstep (se 1 (by rfl) ⟨1367918, by rfl⟩ : syracuseStep 1823891 = 2735837) B2735837
theorem B1823921 : Blo 1215425 1823921 := bstep (se 2 (by rfl) ⟨683970, by rfl⟩ : syracuseStep 1823921 = 1367941) B1367941
theorem B15594677 : Blo 1215425 15594677 := bstep (se 5 (by rfl) ⟨731000, by rfl⟩ : syracuseStep 15594677 = 1462001) B1462001
theorem B1823939 : Blo 1215425 1823939 := bstep (se 1 (by rfl) ⟨1367954, by rfl⟩ : syracuseStep 1823939 = 2735909) B2735909
theorem B1823969 : Blo 1215425 1823969 := bstep (se 2 (by rfl) ⟨683988, by rfl⟩ : syracuseStep 1823969 = 1367977) B1367977
theorem B1823987 : Blo 1215425 1823987 := bstep (se 1 (by rfl) ⟨1367990, by rfl⟩ : syracuseStep 1823987 = 2735981) B2735981
theorem B2053363 : Blo 1215425 2053363 := bstep (se 1 (by rfl) ⟨1540022, by rfl⟩ : syracuseStep 2053363 = 3080045) B3080045
theorem B6239501 : Blo 1215425 6239501 := bstep (se 3 (by rfl) ⟨1169906, by rfl⟩ : syracuseStep 6239501 = 2339813) B2339813
theorem B1824017 : Blo 1215425 1824017 := bstep (se 2 (by rfl) ⟨684006, by rfl⟩ : syracuseStep 1824017 = 1368013) B1368013
theorem B1824035 : Blo 1215425 1824035 := bstep (se 1 (by rfl) ⟨1368026, by rfl⟩ : syracuseStep 1824035 = 2736053) B2736053
theorem B1824065 : Blo 1215425 1824065 := bstep (se 2 (by rfl) ⟨684024, by rfl⟩ : syracuseStep 1824065 = 1368049) B1368049
theorem B2192707 : Blo 1215425 2192707 := bstep (se 1 (by rfl) ⟨1644530, by rfl⟩ : syracuseStep 2192707 = 3289061) B3289061
theorem B1824083 : Blo 1215425 1824083 := bstep (se 1 (by rfl) ⟨1368062, by rfl⟩ : syracuseStep 1824083 = 2736125) B2736125
theorem B1824113 : Blo 1215425 1824113 := bstep (se 2 (by rfl) ⟨684042, by rfl⟩ : syracuseStep 1824113 = 1368085) B1368085
theorem B2053505 : Blo 1215425 2053505 := bstep (se 2 (by rfl) ⟨770064, by rfl⟩ : syracuseStep 2053505 = 1540129) B1540129
theorem B1824131 : Blo 1215425 1824131 := bstep (se 1 (by rfl) ⟨1368098, by rfl⟩ : syracuseStep 1824131 = 2736197) B2736197
theorem B56219021 : Blo 1215425 56219021 := bstep (se 3 (by rfl) ⟨10541066, by rfl⟩ : syracuseStep 56219021 = 21082133) B21082133
theorem B1824161 : Blo 1215425 1824161 := bstep (se 2 (by rfl) ⟨684060, by rfl⟩ : syracuseStep 1824161 = 1368121) B1368121
theorem B3659185 : Blo 1215425 3659185 := bstep (se 2 (by rfl) ⟨1372194, by rfl⟩ : syracuseStep 3659185 = 2744389) B2744389
theorem B1824179 : Blo 1215425 1824179 := bstep (se 1 (by rfl) ⟨1368134, by rfl⟩ : syracuseStep 1824179 = 2736269) B2736269
theorem B3077585 : Blo 1215425 3077585 := bstep (se 2 (by rfl) ⟨1154094, by rfl⟩ : syracuseStep 3077585 = 2308189) B2308189
theorem B1824209 : Blo 1215425 1824209 := bstep (se 2 (by rfl) ⟨684078, by rfl⟩ : syracuseStep 1824209 = 1368157) B1368157
theorem B1824227 : Blo 1215425 1824227 := bstep (se 1 (by rfl) ⟨1368170, by rfl⟩ : syracuseStep 1824227 = 2736341) B2736341
theorem B13858289 : Blo 1215425 13858289 := bstep (se 2 (by rfl) ⟨5196858, by rfl⟩ : syracuseStep 13858289 = 10393717) B10393717
theorem B1824257 : Blo 1215425 1824257 := bstep (se 2 (by rfl) ⟨684096, by rfl⟩ : syracuseStep 1824257 = 1368193) B1368193
theorem B2053633 : Blo 1215425 2053633 := bstep (se 2 (by rfl) ⟨770112, by rfl⟩ : syracuseStep 2053633 = 1540225) B1540225
theorem B3077635 : Blo 1215425 3077635 := bstep (se 1 (by rfl) ⟨2308226, by rfl⟩ : syracuseStep 3077635 = 4616453) B4616453
theorem B3462659 : Blo 1215425 3462659 := bstep (se 1 (by rfl) ⟨2596994, by rfl⟩ : syracuseStep 3462659 = 5193989) B5193989
theorem B9369101 : Blo 1215425 9369101 := bstep (se 3 (by rfl) ⟨1756706, by rfl⟩ : syracuseStep 9369101 = 3513413) B3513413
theorem B1824275 : Blo 1215425 1824275 := bstep (se 1 (by rfl) ⟨1368206, by rfl⟩ : syracuseStep 1824275 = 2736413) B2736413
theorem B2307619 : Blo 1215425 2307619 := bstep (se 1 (by rfl) ⟨1730714, by rfl⟩ : syracuseStep 2307619 = 3461429) B3461429
theorem B2053667 : Blo 1215425 2053667 := bstep (se 1 (by rfl) ⟨1540250, by rfl⟩ : syracuseStep 2053667 = 3080501) B3080501
theorem B1824305 : Blo 1215425 1824305 := bstep (se 2 (by rfl) ⟨684114, by rfl⟩ : syracuseStep 1824305 = 1368229) B1368229
theorem B1824323 : Blo 1215425 1824323 := bstep (se 1 (by rfl) ⟨1368242, by rfl⟩ : syracuseStep 1824323 = 2736485) B2736485
theorem B2307665 : Blo 1215425 2307665 := bstep (se 2 (by rfl) ⟨865374, by rfl⟩ : syracuseStep 2307665 = 1730749) B1730749
theorem B1824353 : Blo 1215425 1824353 := bstep (se 2 (by rfl) ⟨684132, by rfl⟩ : syracuseStep 1824353 = 1368265) B1368265
theorem B1824371 : Blo 1215425 1824371 := bstep (se 1 (by rfl) ⟨1368278, by rfl⟩ : syracuseStep 1824371 = 2736557) B2736557
theorem B4159117 : Blo 1215425 4159117 := bstep (se 3 (by rfl) ⟨779834, by rfl⟩ : syracuseStep 4159117 = 1559669) B1559669
theorem B3077777 : Blo 1215425 3077777 := bstep (se 2 (by rfl) ⟨1154166, by rfl⟩ : syracuseStep 3077777 = 2308333) B2308333
theorem B1824401 : Blo 1215425 1824401 := bstep (se 2 (by rfl) ⟨684150, by rfl⟩ : syracuseStep 1824401 = 1368301) B1368301
theorem B1824419 : Blo 1215425 1824419 := bstep (se 1 (by rfl) ⟨1368314, by rfl⟩ : syracuseStep 1824419 = 2736629) B2736629
theorem B2053795 : Blo 1215425 2053795 := bstep (se 1 (by rfl) ⟨1540346, by rfl⟩ : syracuseStep 2053795 = 3080693) B3080693
theorem B1824449 : Blo 1215425 1824449 := bstep (se 2 (by rfl) ⟨684168, by rfl⟩ : syracuseStep 1824449 = 1368337) B1368337
theorem B1824467 : Blo 1215425 1824467 := bstep (se 1 (by rfl) ⟨1368350, by rfl⟩ : syracuseStep 1824467 = 2736701) B2736701
theorem B1824497 : Blo 1215425 1824497 := bstep (se 2 (by rfl) ⟨684186, by rfl⟩ : syracuseStep 1824497 = 1368373) B1368373
theorem B1824515 : Blo 1215425 1824515 := bstep (se 1 (by rfl) ⟨1368386, by rfl⟩ : syracuseStep 1824515 = 2736773) B2736773
theorem B2193169 : Blo 1215425 2193169 := bstep (se 2 (by rfl) ⟨822438, by rfl⟩ : syracuseStep 2193169 = 1644877) B1644877
theorem B1824545 : Blo 1215425 1824545 := bstep (se 2 (by rfl) ⟨684204, by rfl⟩ : syracuseStep 1824545 = 1368409) B1368409
theorem B2053937 : Blo 1215425 2053937 := bstep (se 2 (by rfl) ⟨770226, by rfl⟩ : syracuseStep 2053937 = 1540453) B1540453
theorem B1824563 : Blo 1215425 1824563 := bstep (se 1 (by rfl) ⟨1368422, by rfl⟩ : syracuseStep 1824563 = 2736845) B2736845
theorem B2340689 : Blo 1215425 2340689 := bstep (se 2 (by rfl) ⟨877758, by rfl⟩ : syracuseStep 2340689 = 1755517) B1755517
theorem B1824593 : Blo 1215425 1824593 := bstep (se 2 (by rfl) ⟨684222, by rfl⟩ : syracuseStep 1824593 = 1368445) B1368445
theorem B1824611 : Blo 1215425 1824611 := bstep (se 1 (by rfl) ⟨1368458, by rfl⟩ : syracuseStep 1824611 = 2736917) B2736917
theorem B2307953 : Blo 1215425 2307953 := bstep (se 2 (by rfl) ⟨865482, by rfl⟩ : syracuseStep 2307953 = 1730965) B1730965
theorem B1824641 : Blo 1215425 1824641 := bstep (se 2 (by rfl) ⟨684240, by rfl⟩ : syracuseStep 1824641 = 1368481) B1368481
theorem B1824659 : Blo 1215425 1824659 := bstep (se 1 (by rfl) ⟨1368494, by rfl⟩ : syracuseStep 1824659 = 2736989) B2736989
theorem B1824689 : Blo 1215425 1824689 := bstep (se 2 (by rfl) ⟨684258, by rfl⟩ : syracuseStep 1824689 = 1368517) B1368517
theorem B2054065 : Blo 1215425 2054065 := bstep (se 2 (by rfl) ⟨770274, by rfl⟩ : syracuseStep 2054065 = 1540549) B1540549
theorem B1824707 : Blo 1215425 1824707 := bstep (se 1 (by rfl) ⟨1368530, by rfl⟩ : syracuseStep 1824707 = 2737061) B2737061
theorem B6928325 : Blo 1215425 6928325 := bstep (se 4 (by rfl) ⟨649530, by rfl⟩ : syracuseStep 6928325 = 1299061) B1299061
theorem B2054099 : Blo 1215425 2054099 := bstep (se 1 (by rfl) ⟨1540574, by rfl⟩ : syracuseStep 2054099 = 3081149) B3081149
theorem B1824737 : Blo 1215425 1824737 := bstep (se 2 (by rfl) ⟨684276, by rfl⟩ : syracuseStep 1824737 = 1368553) B1368553
theorem B3897325 : Blo 1215425 3897325 := bstep (se 3 (by rfl) ⟨730748, by rfl⟩ : syracuseStep 3897325 = 1461497) B1461497
theorem B1824755 : Blo 1215425 1824755 := bstep (se 1 (by rfl) ⟨1368566, by rfl⟩ : syracuseStep 1824755 = 2737133) B2737133
theorem B1824785 : Blo 1215425 1824785 := bstep (se 2 (by rfl) ⟨684294, by rfl⟩ : syracuseStep 1824785 = 1368589) B1368589
theorem B1480723 : Blo 1215425 1480723 := bstep (se 1 (by rfl) ⟨1110542, by rfl⟩ : syracuseStep 1480723 = 2221085) B2221085
theorem B1824803 : Blo 1215425 1824803 := bstep (se 1 (by rfl) ⟨1368602, by rfl⟩ : syracuseStep 1824803 = 2737205) B2737205
theorem B3897389 : Blo 1215425 3897389 := bstep (se 3 (by rfl) ⟨730760, by rfl⟩ : syracuseStep 3897389 = 1461521) B1461521
theorem B1824833 : Blo 1215425 1824833 := bstep (se 2 (by rfl) ⟨684312, by rfl⟩ : syracuseStep 1824833 = 1368625) B1368625
theorem B1824851 : Blo 1215425 1824851 := bstep (se 1 (by rfl) ⟨1368638, by rfl⟩ : syracuseStep 1824851 = 2737277) B2737277
theorem B2054227 : Blo 1215425 2054227 := bstep (se 1 (by rfl) ⟨1540670, by rfl⟩ : syracuseStep 2054227 = 3081341) B3081341
theorem B1824881 : Blo 1215425 1824881 := bstep (se 2 (by rfl) ⟨684330, by rfl⟩ : syracuseStep 1824881 = 1368661) B1368661
theorem B1824899 : Blo 1215425 1824899 := bstep (se 1 (by rfl) ⟨1368674, by rfl⟩ : syracuseStep 1824899 = 2737349) B2737349
theorem B1824929 : Blo 1215425 1824929 := bstep (se 2 (by rfl) ⟨684348, by rfl⟩ : syracuseStep 1824929 = 1368697) B1368697
theorem B1824947 : Blo 1215425 1824947 := bstep (se 1 (by rfl) ⟨1368710, by rfl⟩ : syracuseStep 1824947 = 2737421) B2737421
theorem B1824977 : Blo 1215425 1824977 := bstep (se 2 (by rfl) ⟨684366, by rfl⟩ : syracuseStep 1824977 = 1368733) B1368733
theorem B2054369 : Blo 1215425 2054369 := bstep (se 2 (by rfl) ⟨770388, by rfl⟩ : syracuseStep 2054369 = 1540777) B1540777
theorem B1824995 : Blo 1215425 1824995 := bstep (se 1 (by rfl) ⟨1368746, by rfl⟩ : syracuseStep 1824995 = 2737493) B2737493
theorem B1538291 : Blo 1215425 1538291 := bstep (se 1 (by rfl) ⟨1153718, by rfl⟩ : syracuseStep 1538291 = 2307437) B2307437
theorem B1825025 : Blo 1215425 1825025 := bstep (se 2 (by rfl) ⟨684384, by rfl⟩ : syracuseStep 1825025 = 1368769) B1368769
theorem B1825043 : Blo 1215425 1825043 := bstep (se 1 (by rfl) ⟨1368782, by rfl⟩ : syracuseStep 1825043 = 2737565) B2737565
theorem B3463469 : Blo 1215425 3463469 := bstep (se 3 (by rfl) ⟨649400, by rfl⟩ : syracuseStep 3463469 = 1298801) B1298801
theorem B1825073 : Blo 1215425 1825073 := bstep (se 2 (by rfl) ⟨684402, by rfl⟩ : syracuseStep 1825073 = 1368805) B1368805
theorem B1825091 : Blo 1215425 1825091 := bstep (se 1 (by rfl) ⟨1368818, by rfl⟩ : syracuseStep 1825091 = 2737637) B2737637
theorem B7027013 : Blo 1215425 7027013 := bstep (se 4 (by rfl) ⟨658782, by rfl⟩ : syracuseStep 7027013 = 1317565) B1317565
theorem B1825121 : Blo 1215425 1825121 := bstep (se 2 (by rfl) ⟨684420, by rfl⟩ : syracuseStep 1825121 = 1368841) B1368841
theorem B23386481 : Blo 1215425 23386481 := bstep (se 2 (by rfl) ⟨8769930, by rfl⟩ : syracuseStep 23386481 = 17539861) B17539861
theorem B1825139 : Blo 1215425 1825139 := bstep (se 1 (by rfl) ⟨1368854, by rfl⟩ : syracuseStep 1825139 = 2737709) B2737709
theorem B8321413 : Blo 1215425 8321413 := bstep (se 4 (by rfl) ⟨780132, by rfl⟩ : syracuseStep 8321413 = 1560265) B1560265
theorem B4102541 : Blo 1215425 4102541 := bstep (se 3 (by rfl) ⟨769226, by rfl⟩ : syracuseStep 4102541 = 1538453) B1538453
theorem B2079121 : Blo 1215425 2079121 := bstep (se 2 (by rfl) ⟨779670, by rfl⟩ : syracuseStep 2079121 = 1559341) B1559341
theorem B1825169 : Blo 1215425 1825169 := bstep (se 2 (by rfl) ⟨684438, by rfl⟩ : syracuseStep 1825169 = 1368877) B1368877
theorem B2193809 : Blo 1215425 2193809 := bstep (se 2 (by rfl) ⟨822678, by rfl⟩ : syracuseStep 2193809 = 1645357) B1645357
theorem B1948067 : Blo 1215425 1948067 := bstep (se 1 (by rfl) ⟨1461050, by rfl⟩ : syracuseStep 1948067 = 2922101) B2922101
theorem B1825187 : Blo 1215425 1825187 := bstep (se 1 (by rfl) ⟨1368890, by rfl⟩ : syracuseStep 1825187 = 2737781) B2737781
theorem B1825217 : Blo 1215425 1825217 := bstep (se 2 (by rfl) ⟨684456, by rfl⟩ : syracuseStep 1825217 = 1368913) B1368913
theorem B4102595 : Blo 1215425 4102595 := bstep (se 1 (by rfl) ⟨3076946, by rfl⟩ : syracuseStep 4102595 = 6153893) B6153893
theorem B1825235 : Blo 1215425 1825235 := bstep (se 1 (by rfl) ⟨1368926, by rfl⟩ : syracuseStep 1825235 = 2737853) B2737853
theorem B3463661 : Blo 1215425 3463661 := bstep (se 3 (by rfl) ⟨649436, by rfl⟩ : syracuseStep 3463661 = 1298873) B1298873
theorem B1825265 : Blo 1215425 1825265 := bstep (se 2 (by rfl) ⟨684474, by rfl⟩ : syracuseStep 1825265 = 1368949) B1368949
theorem B1825283 : Blo 1215425 1825283 := bstep (se 1 (by rfl) ⟨1368962, by rfl⟩ : syracuseStep 1825283 = 2737925) B2737925
theorem B1825313 : Blo 1215425 1825313 := bstep (se 2 (by rfl) ⟨684492, by rfl⟩ : syracuseStep 1825313 = 1368985) B1368985
theorem B1825331 : Blo 1215425 1825331 := bstep (se 1 (by rfl) ⟨1368998, by rfl⟩ : syracuseStep 1825331 = 2737997) B2737997
theorem B2308675 : Blo 1215425 2308675 := bstep (se 1 (by rfl) ⟨1731506, by rfl⟩ : syracuseStep 2308675 = 3463013) B3463013
theorem B2079313 : Blo 1215425 2079313 := bstep (se 2 (by rfl) ⟨779742, by rfl⟩ : syracuseStep 2079313 = 1559485) B1559485
theorem B1825361 : Blo 1215425 1825361 := bstep (se 2 (by rfl) ⟨684510, by rfl⟩ : syracuseStep 1825361 = 1369021) B1369021
theorem B1948259 : Blo 1215425 1948259 := bstep (se 1 (by rfl) ⟨1461194, by rfl⟩ : syracuseStep 1948259 = 2922389) B2922389
theorem B1825379 : Blo 1215425 1825379 := bstep (se 1 (by rfl) ⟨1369034, by rfl⟩ : syracuseStep 1825379 = 2738069) B2738069
theorem B3078769 : Blo 1215425 3078769 := bstep (se 2 (by rfl) ⟨1154538, by rfl⟩ : syracuseStep 3078769 = 2309077) B2309077
theorem B6929009 : Blo 1215425 6929009 := bstep (se 2 (by rfl) ⟨2598378, by rfl⟩ : syracuseStep 6929009 = 5196757) B5196757
theorem B1825409 : Blo 1215425 1825409 := bstep (se 2 (by rfl) ⟨684528, by rfl⟩ : syracuseStep 1825409 = 1369057) B1369057
theorem B5192333 : Blo 1215425 5192333 := bstep (se 3 (by rfl) ⟨973562, by rfl⟩ : syracuseStep 5192333 = 1947125) B1947125
theorem B1825427 : Blo 1215425 1825427 := bstep (se 1 (by rfl) ⟨1369070, by rfl⟩ : syracuseStep 1825427 = 2738141) B2738141
theorem B1825457 : Blo 1215425 1825457 := bstep (se 2 (by rfl) ⟨684546, by rfl⟩ : syracuseStep 1825457 = 1369093) B1369093
theorem B1825475 : Blo 1215425 1825475 := bstep (se 1 (by rfl) ⟨1369106, by rfl⟩ : syracuseStep 1825475 = 2738213) B2738213
theorem B4102865 : Blo 1215425 4102865 := bstep (se 2 (by rfl) ⟨1538574, by rfl⟩ : syracuseStep 4102865 = 3077149) B3077149
theorem B1948387 : Blo 1215425 1948387 := bstep (se 1 (by rfl) ⟨1461290, by rfl⟩ : syracuseStep 1948387 = 2922581) B2922581
theorem B1825505 : Blo 1215425 1825505 := bstep (se 2 (by rfl) ⟨684564, by rfl⟩ : syracuseStep 1825505 = 1369129) B1369129
theorem B9870065 : Blo 1215425 9870065 := bstep (se 2 (by rfl) ⟨3701274, by rfl⟩ : syracuseStep 9870065 = 7402549) B7402549
theorem B1825523 : Blo 1215425 1825523 := bstep (se 1 (by rfl) ⟨1369142, by rfl⟩ : syracuseStep 1825523 = 2738285) B2738285
theorem B2734865 : Blo 1215425 2734865 := bstep (se 2 (by rfl) ⟨1025574, by rfl⟩ : syracuseStep 2734865 = 2051149) B2051149
theorem B1825553 : Blo 1215425 1825553 := bstep (se 2 (by rfl) ⟨684582, by rfl⟩ : syracuseStep 1825553 = 1369165) B1369165
theorem B2734883 : Blo 1215425 2734883 := bstep (se 1 (by rfl) ⟨2051162, by rfl⟩ : syracuseStep 2734883 = 4102325) B4102325
theorem B1825571 : Blo 1215425 1825571 := bstep (se 1 (by rfl) ⟨1369178, by rfl⟩ : syracuseStep 1825571 = 2738357) B2738357
theorem B1825601 : Blo 1215425 1825601 := bstep (se 2 (by rfl) ⟨684600, by rfl⟩ : syracuseStep 1825601 = 1369201) B1369201
theorem B1825619 : Blo 1215425 1825619 := bstep (se 1 (by rfl) ⟨1369214, by rfl⟩ : syracuseStep 1825619 = 2738429) B2738429
theorem B1825649 : Blo 1215425 1825649 := bstep (se 2 (by rfl) ⟨684618, by rfl⟩ : syracuseStep 1825649 = 1369237) B1369237
theorem B3079043 : Blo 1215425 3079043 := bstep (se 1 (by rfl) ⟨2309282, by rfl⟩ : syracuseStep 3079043 = 4618565) B4618565
theorem B3750787 : Blo 1215425 3750787 := bstep (se 1 (by rfl) ⟨2813090, by rfl⟩ : syracuseStep 3750787 = 5626181) B5626181
theorem B1825667 : Blo 1215425 1825667 := bstep (se 1 (by rfl) ⟨1369250, by rfl⟩ : syracuseStep 1825667 = 2738501) B2738501
theorem B2923427 : Blo 1215425 2923427 := bstep (se 1 (by rfl) ⟨2192570, by rfl⟩ : syracuseStep 2923427 = 4385141) B4385141
theorem B1825697 : Blo 1215425 1825697 := bstep (se 2 (by rfl) ⟨684636, by rfl⟩ : syracuseStep 1825697 = 1369273) B1369273
theorem B1538995 : Blo 1215425 1538995 := bstep (se 1 (by rfl) ⟨1154246, by rfl⟩ : syracuseStep 1538995 = 2308493) B2308493
theorem B1825715 : Blo 1215425 1825715 := bstep (se 1 (by rfl) ⟨1369286, by rfl⟩ : syracuseStep 1825715 = 2738573) B2738573
theorem B1825745 : Blo 1215425 1825745 := bstep (se 2 (by rfl) ⟨684654, by rfl⟩ : syracuseStep 1825745 = 1369309) B1369309
theorem B1825763 : Blo 1215425 1825763 := bstep (se 1 (by rfl) ⟨1369322, by rfl⟩ : syracuseStep 1825763 = 2738645) B2738645
theorem B1825793 : Blo 1215425 1825793 := bstep (se 2 (by rfl) ⟨684672, by rfl⟩ : syracuseStep 1825793 = 1369345) B1369345
theorem B2309123 : Blo 1215425 2309123 := bstep (se 1 (by rfl) ⟨1731842, by rfl⟩ : syracuseStep 2309123 = 3463685) B3463685
theorem B1539091 : Blo 1215425 1539091 := bstep (se 1 (by rfl) ⟨1154318, by rfl⟩ : syracuseStep 1539091 = 2308637) B2308637
theorem B1825811 : Blo 1215425 1825811 := bstep (se 1 (by rfl) ⟨1369358, by rfl⟩ : syracuseStep 1825811 = 2738717) B2738717
theorem B2735153 : Blo 1215425 2735153 := bstep (se 2 (by rfl) ⟨1025682, by rfl⟩ : syracuseStep 2735153 = 2051365) B2051365
theorem B1825841 : Blo 1215425 1825841 := bstep (se 2 (by rfl) ⟨684690, by rfl⟩ : syracuseStep 1825841 = 1369381) B1369381
theorem B2735171 : Blo 1215425 2735171 := bstep (se 1 (by rfl) ⟨2051378, by rfl⟩ : syracuseStep 2735171 = 4102757) B4102757
theorem B3079235 : Blo 1215425 3079235 := bstep (se 1 (by rfl) ⟨2309426, by rfl⟩ : syracuseStep 3079235 = 4618853) B4618853
theorem B1825859 : Blo 1215425 1825859 := bstep (se 1 (by rfl) ⟨1369394, by rfl⟩ : syracuseStep 1825859 = 2738789) B2738789
theorem B5545037 : Blo 1215425 5545037 := bstep (se 3 (by rfl) ⟨1039694, by rfl⟩ : syracuseStep 5545037 = 2079389) B2079389
theorem B1825889 : Blo 1215425 1825889 := bstep (se 2 (by rfl) ⟨684708, by rfl⟩ : syracuseStep 1825889 = 1369417) B1369417
theorem B1825907 : Blo 1215425 1825907 := bstep (se 1 (by rfl) ⟨1369430, by rfl⟩ : syracuseStep 1825907 = 2738861) B2738861
theorem B1825937 : Blo 1215425 1825937 := bstep (se 2 (by rfl) ⟨684726, by rfl⟩ : syracuseStep 1825937 = 1369453) B1369453
theorem B1825955 : Blo 1215425 1825955 := bstep (se 1 (by rfl) ⟨1369466, by rfl⟩ : syracuseStep 1825955 = 2738933) B2738933
theorem B13327541 : Blo 1215425 13327541 := bstep (se 5 (by rfl) ⟨624728, by rfl⟩ : syracuseStep 13327541 = 1249457) B1249457
theorem B1825985 : Blo 1215425 1825985 := bstep (se 2 (by rfl) ⟨684744, by rfl⟩ : syracuseStep 1825985 = 1369489) B1369489
theorem B2923715 : Blo 1215425 2923715 := bstep (se 1 (by rfl) ⟨2192786, by rfl⟩ : syracuseStep 2923715 = 4385573) B4385573
theorem B1826003 : Blo 1215425 1826003 := bstep (se 1 (by rfl) ⟨1369502, by rfl⟩ : syracuseStep 1826003 = 2739005) B2739005
theorem B4103405 : Blo 1215425 4103405 := bstep (se 3 (by rfl) ⟨769388, by rfl⟩ : syracuseStep 4103405 = 1538777) B1538777
theorem B1826033 : Blo 1215425 1826033 := bstep (se 2 (by rfl) ⟨684762, by rfl⟩ : syracuseStep 1826033 = 1369525) B1369525
theorem B1826051 : Blo 1215425 1826051 := bstep (se 1 (by rfl) ⟨1369538, by rfl⟩ : syracuseStep 1826051 = 2739077) B2739077
theorem B1826081 : Blo 1215425 1826081 := bstep (se 2 (by rfl) ⟨684780, by rfl⟩ : syracuseStep 1826081 = 1369561) B1369561
theorem B4103459 : Blo 1215425 4103459 := bstep (se 1 (by rfl) ⟨3077594, by rfl⟩ : syracuseStep 4103459 = 6155189) B6155189
theorem B2309411 : Blo 1215425 2309411 := bstep (se 1 (by rfl) ⟨1732058, by rfl⟩ : syracuseStep 2309411 = 3464117) B3464117
theorem B1826099 : Blo 1215425 1826099 := bstep (se 1 (by rfl) ⟨1369574, by rfl⟩ : syracuseStep 1826099 = 2739149) B2739149
theorem B2735441 : Blo 1215425 2735441 := bstep (se 2 (by rfl) ⟨1025790, by rfl⟩ : syracuseStep 2735441 = 2051581) B2051581
theorem B1826129 : Blo 1215425 1826129 := bstep (se 2 (by rfl) ⟨684798, by rfl⟩ : syracuseStep 1826129 = 1369597) B1369597
theorem B2735459 : Blo 1215425 2735459 := bstep (se 1 (by rfl) ⟨2051594, by rfl⟩ : syracuseStep 2735459 = 4103189) B4103189
theorem B1949027 : Blo 1215425 1949027 := bstep (se 1 (by rfl) ⟨1461770, by rfl⟩ : syracuseStep 1949027 = 2923541) B2923541
theorem B3513773 : Blo 1215425 3513773 := bstep (se 3 (by rfl) ⟨658832, by rfl⟩ : syracuseStep 3513773 = 1317665) B1317665
theorem B1949105 : Blo 1215425 1949105 := bstep (se 2 (by rfl) ⟨730914, by rfl⟩ : syracuseStep 1949105 = 1461829) B1461829
theorem B1367491 : Blo 1215425 1367491 := bstep (se 1 (by rfl) ⟨1025618, by rfl⟩ : syracuseStep 1367491 = 2051237) B2051237
theorem B3464653 : Blo 1215425 3464653 := bstep (se 3 (by rfl) ⟨649622, by rfl⟩ : syracuseStep 3464653 = 1299245) B1299245
theorem B1539587 : Blo 1215425 1539587 := bstep (se 1 (by rfl) ⟨1154690, by rfl⟩ : syracuseStep 1539587 = 2309381) B2309381
theorem B4103729 : Blo 1215425 4103729 := bstep (se 2 (by rfl) ⟨1538898, by rfl⟩ : syracuseStep 4103729 = 3077797) B3077797
theorem B4619825 : Blo 1215425 4619825 := bstep (se 2 (by rfl) ⟨1732434, by rfl⟩ : syracuseStep 4619825 = 3464869) B3464869
theorem B1367635 : Blo 1215425 1367635 := bstep (se 1 (by rfl) ⟨1025726, by rfl⟩ : syracuseStep 1367635 = 2051453) B2051453
theorem B2596465 : Blo 1215425 2596465 := bstep (se 2 (by rfl) ⟨973674, by rfl⟩ : syracuseStep 2596465 = 1947349) B1947349
theorem B2735729 : Blo 1215425 2735729 := bstep (se 2 (by rfl) ⟨1025898, by rfl⟩ : syracuseStep 2735729 = 2051797) B2051797
theorem B2735747 : Blo 1215425 2735747 := bstep (se 1 (by rfl) ⟨2051810, by rfl⟩ : syracuseStep 2735747 = 4103621) B4103621
theorem B6160049 : Blo 1215425 6160049 := bstep (se 2 (by rfl) ⟨2310018, by rfl⟩ : syracuseStep 6160049 = 4620037) B4620037
theorem B1367779 : Blo 1215425 1367779 := bstep (se 1 (by rfl) ⟨1025834, by rfl⟩ : syracuseStep 1367779 = 2051669) B2051669
theorem B3899171 : Blo 1215425 3899171 := bstep (se 1 (by rfl) ⟨2924378, by rfl⟩ : syracuseStep 3899171 = 5848757) B5848757
theorem B1949489 : Blo 1215425 1949489 := bstep (se 2 (by rfl) ⟨731058, by rfl⟩ : syracuseStep 1949489 = 1462117) B1462117
theorem B1367923 : Blo 1215425 1367923 := bstep (se 1 (by rfl) ⟨1025942, by rfl⟩ : syracuseStep 1367923 = 2051885) B2051885
theorem B2736017 : Blo 1215425 2736017 := bstep (se 2 (by rfl) ⟨1026006, by rfl⟩ : syracuseStep 2736017 = 2052013) B2052013
theorem B2736035 : Blo 1215425 2736035 := bstep (se 1 (by rfl) ⟨2052026, by rfl⟩ : syracuseStep 2736035 = 4104053) B4104053
theorem B1949617 : Blo 1215425 1949617 := bstep (se 2 (by rfl) ⟨731106, by rfl⟩ : syracuseStep 1949617 = 1462213) B1462213
theorem B3080177 : Blo 1215425 3080177 := bstep (se 2 (by rfl) ⟨1155066, by rfl⟩ : syracuseStep 3080177 = 2310133) B2310133
theorem B1949707 : Blo 1215425 1949707 := bstep (se 1 (by rfl) ⟨1462280, by rfl⟩ : syracuseStep 1949707 = 2924561) B2924561
theorem B4104215 : Blo 1215425 4104215 := bstep (se 1 (by rfl) ⟨3078161, by rfl⟩ : syracuseStep 4104215 = 6156323) B6156323
theorem B4620311 : Blo 1215425 4620311 := bstep (se 1 (by rfl) ⟨3465233, by rfl⟩ : syracuseStep 4620311 = 6930467) B6930467
theorem B2736179 : Blo 1215425 2736179 := bstep (se 1 (by rfl) ⟨2052134, by rfl⟩ : syracuseStep 2736179 = 4104269) B4104269
theorem B1368139 : Blo 1215425 1368139 := bstep (se 1 (by rfl) ⟨1026104, by rfl⟩ : syracuseStep 1368139 = 2052209) B2052209
theorem B1949771 : Blo 1215425 1949771 := bstep (se 1 (by rfl) ⟨1462328, by rfl⟩ : syracuseStep 1949771 = 2924657) B2924657
theorem B2736215 : Blo 1215425 2736215 := bstep (se 1 (by rfl) ⟨2052161, by rfl⟩ : syracuseStep 2736215 = 4104323) B4104323
theorem B7897189 : Blo 1215425 7897189 := bstep (se 4 (by rfl) ⟨740361, by rfl⟩ : syracuseStep 7897189 = 1480723) B1480723
theorem B1540235 : Blo 1215425 1540235 := bstep (se 1 (by rfl) ⟨1155176, by rfl⟩ : syracuseStep 1540235 = 2310353) B2310353
theorem B6160535 : Blo 1215425 6160535 := bstep (se 1 (by rfl) ⟨4620401, by rfl⟩ : syracuseStep 6160535 = 9240803) B9240803
theorem B1368247 : Blo 1215425 1368247 := bstep (se 1 (by rfl) ⟨1026185, by rfl⟩ : syracuseStep 1368247 = 2052371) B2052371
theorem B1949899 : Blo 1215425 1949899 := bstep (se 1 (by rfl) ⟨1462424, by rfl⟩ : syracuseStep 1949899 = 2924849) B2924849
theorem B4620509 : Blo 1215425 4620509 := bstep (se 3 (by rfl) ⟨866345, by rfl⟩ : syracuseStep 4620509 = 1732691) B1732691
theorem B2597131 : Blo 1215425 2597131 := bstep (se 1 (by rfl) ⟨1947848, by rfl⟩ : syracuseStep 2597131 = 3895697) B3895697
theorem B2736395 : Blo 1215425 2736395 := bstep (se 1 (by rfl) ⟨2052296, by rfl⟩ : syracuseStep 2736395 = 4104593) B4104593
theorem B2736449 : Blo 1215425 2736449 := bstep (se 2 (by rfl) ⟨1026168, by rfl⟩ : syracuseStep 2736449 = 2052337) B2052337
theorem B7020893 : Blo 1215425 7020893 := bstep (se 3 (by rfl) ⟨1316417, by rfl⟩ : syracuseStep 7020893 = 2632835) B2632835
theorem B1368427 : Blo 1215425 1368427 := bstep (se 1 (by rfl) ⟨1026320, by rfl⟩ : syracuseStep 1368427 = 2052641) B2052641
theorem B35553649 : Blo 1215425 35553649 := bstep (se 2 (by rfl) ⟨13332618, by rfl⟩ : syracuseStep 35553649 = 26665237) B26665237
theorem B4161995 : Blo 1215425 4161995 := bstep (se 1 (by rfl) ⟨3121496, by rfl⟩ : syracuseStep 4161995 = 6242993) B6242993
theorem B1368535 : Blo 1215425 1368535 := bstep (se 1 (by rfl) ⟨1026401, by rfl⟩ : syracuseStep 1368535 = 2052803) B2052803
theorem B2736665 : Blo 1215425 2736665 := bstep (se 2 (by rfl) ⟨1026249, by rfl⟩ : syracuseStep 2736665 = 2052499) B2052499
theorem B2081305 : Blo 1215425 2081305 := bstep (se 2 (by rfl) ⟨780489, by rfl⟩ : syracuseStep 2081305 = 1560979) B1560979
theorem B3899927 : Blo 1215425 3899927 := bstep (se 1 (by rfl) ⟨2924945, by rfl⟩ : syracuseStep 3899927 = 5849891) B5849891
theorem B4104755 : Blo 1215425 4104755 := bstep (se 1 (by rfl) ⟨3078566, by rfl⟩ : syracuseStep 4104755 = 6157133) B6157133
theorem B3465803 : Blo 1215425 3465803 := bstep (se 1 (by rfl) ⟨2599352, by rfl⟩ : syracuseStep 3465803 = 5198705) B5198705
theorem B2736755 : Blo 1215425 2736755 := bstep (se 1 (by rfl) ⟨2052566, by rfl⟩ : syracuseStep 2736755 = 4105133) B4105133
theorem B9233027 : Blo 1215425 9233027 := bstep (se 1 (by rfl) ⟨6924770, by rfl⟩ : syracuseStep 9233027 = 13849541) B13849541
theorem B1368715 : Blo 1215425 1368715 := bstep (se 1 (by rfl) ⟨1026536, by rfl⟩ : syracuseStep 1368715 = 2053073) B2053073
theorem B2736791 : Blo 1215425 2736791 := bstep (se 1 (by rfl) ⟨2052593, by rfl⟩ : syracuseStep 2736791 = 4105187) B4105187
theorem B3080855 : Blo 1215425 3080855 := bstep (se 1 (by rfl) ⟨2310641, by rfl⟩ : syracuseStep 3080855 = 4621283) B4621283
theorem B28074701 : Blo 1215425 28074701 := bstep (se 3 (by rfl) ⟨5264006, by rfl⟩ : syracuseStep 28074701 = 10528013) B10528013
theorem B1368823 : Blo 1215425 1368823 := bstep (se 1 (by rfl) ⟨1026617, by rfl⟩ : syracuseStep 1368823 = 2053235) B2053235
theorem B2310923 : Blo 1215425 2310923 := bstep (se 1 (by rfl) ⟨1733192, by rfl⟩ : syracuseStep 2310923 = 3466385) B3466385
theorem B10396451 : Blo 1215425 10396451 := bstep (se 1 (by rfl) ⟨7797338, by rfl⟩ : syracuseStep 10396451 = 15594677) B15594677
theorem B4105025 : Blo 1215425 4105025 := bstep (se 2 (by rfl) ⟨1539384, by rfl⟩ : syracuseStep 4105025 = 3078769) B3078769
theorem B2736971 : Blo 1215425 2736971 := bstep (se 1 (by rfl) ⟨2052728, by rfl⟩ : syracuseStep 2736971 = 4105457) B4105457
theorem B2737025 : Blo 1215425 2737025 := bstep (se 2 (by rfl) ⟨1026384, by rfl⟩ : syracuseStep 2737025 = 2052769) B2052769
theorem B1369003 : Blo 1215425 1369003 := bstep (se 1 (by rfl) ⟨1026752, by rfl⟩ : syracuseStep 1369003 = 2053505) B2053505
theorem B37479347 : Blo 1215425 37479347 := bstep (se 1 (by rfl) ⟨28109510, by rfl⟩ : syracuseStep 37479347 = 56219021) B56219021
theorem B2311105 : Blo 1215425 2311105 := bstep (se 2 (by rfl) ⟨866664, by rfl⟩ : syracuseStep 2311105 = 1733329) B1733329
theorem B2597849 : Blo 1215425 2597849 := bstep (se 2 (by rfl) ⟨974193, by rfl⟩ : syracuseStep 2597849 = 1948387) B1948387
theorem B4932569 : Blo 1215425 4932569 := bstep (se 2 (by rfl) ⟨1849713, by rfl⟩ : syracuseStep 4932569 = 3699427) B3699427
theorem B1369111 : Blo 1215425 1369111 := bstep (se 1 (by rfl) ⟨1026833, by rfl⟩ : syracuseStep 1369111 = 2053667) B2053667
theorem B5850157 : Blo 1215425 5850157 := bstep (se 3 (by rfl) ⟨1096904, by rfl⟩ : syracuseStep 5850157 = 2193809) B2193809
theorem B2737241 : Blo 1215425 2737241 := bstep (se 2 (by rfl) ⟨1026465, by rfl⟩ : syracuseStep 2737241 = 2052931) B2052931
theorem B4678829 : Blo 1215425 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B2737331 : Blo 1215425 2737331 := bstep (se 1 (by rfl) ⟨2052998, by rfl⟩ : syracuseStep 2737331 = 4105997) B4105997
theorem B5194945 : Blo 1215425 5194945 := bstep (se 2 (by rfl) ⟨1948104, by rfl⟩ : syracuseStep 5194945 = 3896209) B3896209
theorem B1369291 : Blo 1215425 1369291 := bstep (se 1 (by rfl) ⟨1026968, by rfl⟩ : syracuseStep 1369291 = 2053937) B2053937
theorem B2737367 : Blo 1215425 2737367 := bstep (se 1 (by rfl) ⟨2053025, by rfl⟩ : syracuseStep 2737367 = 4106051) B4106051
theorem B3081523 : Blo 1215425 3081523 := bstep (se 1 (by rfl) ⟨2311142, by rfl⟩ : syracuseStep 3081523 = 4622285) B4622285
theorem B1369399 : Blo 1215425 1369399 := bstep (se 1 (by rfl) ⟨1027049, by rfl⟩ : syracuseStep 1369399 = 2054099) B2054099
theorem B1754443 : Blo 1215425 1754443 := bstep (se 1 (by rfl) ⟨1315832, by rfl⟩ : syracuseStep 1754443 = 2631665) B2631665
theorem B4105565 : Blo 1215425 4105565 := bstep (se 3 (by rfl) ⟨769793, by rfl⟩ : syracuseStep 4105565 = 1539587) B1539587
theorem B2598259 : Blo 1215425 2598259 := bstep (se 1 (by rfl) ⟨1948694, by rfl⟩ : syracuseStep 2598259 = 3897389) B3897389
theorem B2737547 : Blo 1215425 2737547 := bstep (se 1 (by rfl) ⟨2053160, by rfl⟩ : syracuseStep 2737547 = 4106321) B4106321
theorem B2737601 : Blo 1215425 2737601 := bstep (se 2 (by rfl) ⟨1026600, by rfl⟩ : syracuseStep 2737601 = 2053201) B2053201
theorem B8316377 : Blo 1215425 8316377 := bstep (se 2 (by rfl) ⟨3118641, by rfl⟩ : syracuseStep 8316377 = 6237283) B6237283
theorem B1369579 : Blo 1215425 1369579 := bstep (se 1 (by rfl) ⟨1027184, by rfl⟩ : syracuseStep 1369579 = 2054369) B2054369
theorem B9356845 : Blo 1215425 9356845 := bstep (se 3 (by rfl) ⟨1754408, by rfl⟩ : syracuseStep 9356845 = 3508817) B3508817
theorem B15590987 : Blo 1215425 15590987 := bstep (se 1 (by rfl) ⟨11693240, by rfl⟩ : syracuseStep 15590987 = 23386481) B23386481
theorem B2737817 : Blo 1215425 2737817 := bstep (se 2 (by rfl) ⟨1026681, by rfl⟩ : syracuseStep 2737817 = 2053363) B2053363
theorem B2737907 : Blo 1215425 2737907 := bstep (se 1 (by rfl) ⟨2053430, by rfl⟩ : syracuseStep 2737907 = 4106861) B4106861
theorem B2737943 : Blo 1215425 2737943 := bstep (se 1 (by rfl) ⟨2053457, by rfl⟩ : syracuseStep 2737943 = 4106915) B4106915
theorem B6580043 : Blo 1215425 6580043 := bstep (se 1 (by rfl) ⟨4935032, by rfl⟩ : syracuseStep 6580043 = 9870065) B9870065
theorem B4163417 : Blo 1215425 4163417 := bstep (se 2 (by rfl) ⟨1561281, by rfl⟩ : syracuseStep 4163417 = 3122563) B3122563
theorem B2738123 : Blo 1215425 2738123 := bstep (se 1 (by rfl) ⟨2053592, by rfl⟩ : syracuseStep 2738123 = 4107185) B4107185
theorem B2738177 : Blo 1215425 2738177 := bstep (se 2 (by rfl) ⟨1026816, by rfl⟩ : syracuseStep 2738177 = 2053633) B2053633
theorem B3696691 : Blo 1215425 3696691 := bstep (se 1 (by rfl) ⟨2772518, by rfl⟩ : syracuseStep 3696691 = 5545037) B5545037
theorem B2738393 : Blo 1215425 2738393 := bstep (se 2 (by rfl) ⟨1026897, by rfl⟩ : syracuseStep 2738393 = 2053795) B2053795
theorem B6154541 : Blo 1215425 6154541 := bstep (se 3 (by rfl) ⟨1153976, by rfl⟩ : syracuseStep 6154541 = 2307953) B2307953
theorem B13158701 : Blo 1215425 13158701 := bstep (se 3 (by rfl) ⟨2467256, by rfl⟩ : syracuseStep 13158701 = 4934513) B4934513
theorem B2738483 : Blo 1215425 2738483 := bstep (se 1 (by rfl) ⟨2053862, by rfl⟩ : syracuseStep 2738483 = 4107725) B4107725
theorem B2738519 : Blo 1215425 2738519 := bstep (se 1 (by rfl) ⟨2053889, by rfl⟩ : syracuseStep 2738519 = 4107779) B4107779
theorem B4106699 : Blo 1215425 4106699 := bstep (se 1 (by rfl) ⟨3080024, by rfl⟩ : syracuseStep 4106699 = 6160049) B6160049
theorem B2738699 : Blo 1215425 2738699 := bstep (se 1 (by rfl) ⟨2054024, by rfl⟩ : syracuseStep 2738699 = 4108049) B4108049
theorem B2599447 : Blo 1215425 2599447 := bstep (se 1 (by rfl) ⟨1949585, by rfl⟩ : syracuseStep 2599447 = 3899171) B3899171
theorem B2599489 : Blo 1215425 2599489 := bstep (se 2 (by rfl) ⟨974808, by rfl⟩ : syracuseStep 2599489 = 1949617) B1949617
theorem B2738753 : Blo 1215425 2738753 := bstep (se 2 (by rfl) ⟨1027032, by rfl⟩ : syracuseStep 2738753 = 2054065) B2054065
theorem B5196433 : Blo 1215425 5196433 := bstep (se 2 (by rfl) ⟨1948662, by rfl⟩ : syracuseStep 5196433 = 3897325) B3897325
theorem B4106969 : Blo 1215425 4106969 := bstep (se 2 (by rfl) ⟨1540113, by rfl⟩ : syracuseStep 4106969 = 3080227) B3080227
theorem B2738969 : Blo 1215425 2738969 := bstep (se 2 (by rfl) ⟨1027113, by rfl⟩ : syracuseStep 2738969 = 2054227) B2054227
theorem B2739059 : Blo 1215425 2739059 := bstep (se 1 (by rfl) ⟨2054294, by rfl⟩ : syracuseStep 2739059 = 4108589) B4108589
theorem B2739095 : Blo 1215425 2739095 := bstep (se 1 (by rfl) ⟨2054321, by rfl⟩ : syracuseStep 2739095 = 4108643) B4108643
theorem B5270465 : Blo 1215425 5270465 := bstep (se 2 (by rfl) ⟨1976424, by rfl⟩ : syracuseStep 5270465 = 3952849) B3952849
theorem B1215435 : Blo 1215425 1215435 := bstep (se 1 (by rfl) ⟨911576, by rfl⟩ : syracuseStep 1215435 = 1823153) B1823153
theorem B1215447 : Blo 1215425 1215447 := bstep (se 1 (by rfl) ⟨911585, by rfl⟩ : syracuseStep 1215447 = 1823171) B1823171
theorem B1215467 : Blo 1215425 1215467 := bstep (se 1 (by rfl) ⟨911600, by rfl⟩ : syracuseStep 1215467 = 1823201) B1823201
theorem B1215479 : Blo 1215425 1215479 := bstep (se 1 (by rfl) ⟨911609, by rfl⟩ : syracuseStep 1215479 = 1823219) B1823219
theorem B1215499 : Blo 1215425 1215499 := bstep (se 1 (by rfl) ⟨911624, by rfl⟩ : syracuseStep 1215499 = 1823249) B1823249
theorem B2051095 : Blo 1215425 2051095 := bstep (se 1 (by rfl) ⟨1538321, by rfl⟩ : syracuseStep 2051095 = 3076643) B3076643
theorem B1215511 : Blo 1215425 1215511 := bstep (se 1 (by rfl) ⟨911633, by rfl⟩ : syracuseStep 1215511 = 1823267) B1823267
theorem B1215531 : Blo 1215425 1215531 := bstep (se 1 (by rfl) ⟨911648, by rfl⟩ : syracuseStep 1215531 = 1823297) B1823297
theorem B1215543 : Blo 1215425 1215543 := bstep (se 1 (by rfl) ⟨911657, by rfl⟩ : syracuseStep 1215543 = 1823315) B1823315
theorem B1215563 : Blo 1215425 1215563 := bstep (se 1 (by rfl) ⟨911672, by rfl⟩ : syracuseStep 1215563 = 1823345) B1823345
theorem B1215575 : Blo 1215425 1215575 := bstep (se 1 (by rfl) ⟨911681, by rfl⟩ : syracuseStep 1215575 = 1823363) B1823363
theorem B1215595 : Blo 1215425 1215595 := bstep (se 1 (by rfl) ⟨911696, by rfl⟩ : syracuseStep 1215595 = 1823393) B1823393
theorem B1215607 : Blo 1215425 1215607 := bstep (se 1 (by rfl) ⟨911705, by rfl⟩ : syracuseStep 1215607 = 1823411) B1823411
theorem B1215627 : Blo 1215425 1215627 := bstep (se 1 (by rfl) ⟨911720, by rfl⟩ : syracuseStep 1215627 = 1823441) B1823441
theorem B1215639 : Blo 1215425 1215639 := bstep (se 1 (by rfl) ⟨911729, by rfl⟩ : syracuseStep 1215639 = 1823459) B1823459
theorem B10390679 : Blo 1215425 10390679 := bstep (se 1 (by rfl) ⟨7793009, by rfl⟩ : syracuseStep 10390679 = 15586019) B15586019
theorem B1215659 : Blo 1215425 1215659 := bstep (se 1 (by rfl) ⟨911744, by rfl⟩ : syracuseStep 1215659 = 1823489) B1823489
theorem B11095217 : Blo 1215425 11095217 := bstep (se 2 (by rfl) ⟨4160706, by rfl⟩ : syracuseStep 11095217 = 8321413) B8321413
theorem B1215671 : Blo 1215425 1215671 := bstep (se 1 (by rfl) ⟨911753, by rfl⟩ : syracuseStep 1215671 = 1823507) B1823507
theorem B2772161 : Blo 1215425 2772161 := bstep (se 2 (by rfl) ⟨1039560, by rfl⟩ : syracuseStep 2772161 = 2079121) B2079121
theorem B1215691 : Blo 1215425 1215691 := bstep (se 1 (by rfl) ⟨911768, by rfl⟩ : syracuseStep 1215691 = 1823537) B1823537
theorem B1387723 : Blo 1215425 1387723 := bstep (se 1 (by rfl) ⟨1040792, by rfl⟩ : syracuseStep 1387723 = 2081585) B2081585
theorem B1215703 : Blo 1215425 1215703 := bstep (se 1 (by rfl) ⟨911777, by rfl⟩ : syracuseStep 1215703 = 1823555) B1823555
theorem B3894493 : Blo 1215425 3894493 := bstep (se 3 (by rfl) ⟨730217, by rfl⟩ : syracuseStep 3894493 = 1460435) B1460435
theorem B1215723 : Blo 1215425 1215723 := bstep (se 1 (by rfl) ⟨911792, by rfl⟩ : syracuseStep 1215723 = 1823585) B1823585
theorem B1215735 : Blo 1215425 1215735 := bstep (se 1 (by rfl) ⟨911801, by rfl⟩ : syracuseStep 1215735 = 1823603) B1823603
theorem B2772235 : Blo 1215425 2772235 := bstep (se 1 (by rfl) ⟨2079176, by rfl⟩ : syracuseStep 2772235 = 4158353) B4158353
theorem B1215755 : Blo 1215425 1215755 := bstep (se 1 (by rfl) ⟨911816, by rfl⟩ : syracuseStep 1215755 = 1823633) B1823633
theorem B1215767 : Blo 1215425 1215767 := bstep (se 1 (by rfl) ⟨911825, by rfl⟩ : syracuseStep 1215767 = 1823651) B1823651
theorem B1215787 : Blo 1215425 1215787 := bstep (se 1 (by rfl) ⟨911840, by rfl⟩ : syracuseStep 1215787 = 1823681) B1823681
theorem B7023917 : Blo 1215425 7023917 := bstep (se 3 (by rfl) ⟨1316984, by rfl⟩ : syracuseStep 7023917 = 2633969) B2633969
theorem B1215799 : Blo 1215425 1215799 := bstep (se 1 (by rfl) ⟨911849, by rfl⟩ : syracuseStep 1215799 = 1823699) B1823699
theorem B1215819 : Blo 1215425 1215819 := bstep (se 1 (by rfl) ⟨911864, by rfl⟩ : syracuseStep 1215819 = 1823729) B1823729
theorem B1215831 : Blo 1215425 1215831 := bstep (se 1 (by rfl) ⟨911873, by rfl⟩ : syracuseStep 1215831 = 1823747) B1823747
theorem B6925661 : Blo 1215425 6925661 := bstep (se 3 (by rfl) ⟨1298561, by rfl⟩ : syracuseStep 6925661 = 2597123) B2597123
theorem B1215851 : Blo 1215425 1215851 := bstep (se 1 (by rfl) ⟨911888, by rfl⟩ : syracuseStep 1215851 = 1823777) B1823777
theorem B1215863 : Blo 1215425 1215863 := bstep (se 1 (by rfl) ⟨911897, by rfl⟩ : syracuseStep 1215863 = 1823795) B1823795
theorem B1215883 : Blo 1215425 1215883 := bstep (se 1 (by rfl) ⟨911912, by rfl⟩ : syracuseStep 1215883 = 1823825) B1823825
theorem B1731979 : Blo 1215425 1731979 := bstep (se 1 (by rfl) ⟨1298984, by rfl⟩ : syracuseStep 1731979 = 2597969) B2597969
theorem B1215895 : Blo 1215425 1215895 := bstep (se 1 (by rfl) ⟨911921, by rfl⟩ : syracuseStep 1215895 = 1823843) B1823843
theorem B4107671 : Blo 1215425 4107671 := bstep (se 1 (by rfl) ⟨3080753, by rfl⟩ : syracuseStep 4107671 = 6161507) B6161507
theorem B1215915 : Blo 1215425 1215915 := bstep (se 1 (by rfl) ⟨911936, by rfl⟩ : syracuseStep 1215915 = 1823873) B1823873
theorem B1215927 : Blo 1215425 1215927 := bstep (se 1 (by rfl) ⟨911945, by rfl⟩ : syracuseStep 1215927 = 1823891) B1823891
theorem B1215947 : Blo 1215425 1215947 := bstep (se 1 (by rfl) ⟨911960, by rfl⟩ : syracuseStep 1215947 = 1823921) B1823921
theorem B1215959 : Blo 1215425 1215959 := bstep (se 1 (by rfl) ⟨911969, by rfl⟩ : syracuseStep 1215959 = 1823939) B1823939
theorem B1215979 : Blo 1215425 1215979 := bstep (se 1 (by rfl) ⟨911984, by rfl⟩ : syracuseStep 1215979 = 1823969) B1823969
theorem B1215991 : Blo 1215425 1215991 := bstep (se 1 (by rfl) ⟨911993, by rfl⟩ : syracuseStep 1215991 = 1823987) B1823987
theorem B1216011 : Blo 1215425 1216011 := bstep (se 1 (by rfl) ⟨912008, by rfl⟩ : syracuseStep 1216011 = 1824017) B1824017
theorem B1216023 : Blo 1215425 1216023 := bstep (se 1 (by rfl) ⟨912017, by rfl⟩ : syracuseStep 1216023 = 1824035) B1824035
theorem B1216043 : Blo 1215425 1216043 := bstep (se 1 (by rfl) ⟨912032, by rfl⟩ : syracuseStep 1216043 = 1824065) B1824065
theorem B9244205 : Blo 1215425 9244205 := bstep (se 3 (by rfl) ⟨1733288, by rfl⟩ : syracuseStep 9244205 = 3466577) B3466577
theorem B1216055 : Blo 1215425 1216055 := bstep (se 1 (by rfl) ⟨912041, by rfl⟩ : syracuseStep 1216055 = 1824083) B1824083
theorem B5844545 : Blo 1215425 5844545 := bstep (se 2 (by rfl) ⟨2191704, by rfl⟩ : syracuseStep 5844545 = 4383409) B4383409
theorem B1216075 : Blo 1215425 1216075 := bstep (se 1 (by rfl) ⟨912056, by rfl⟩ : syracuseStep 1216075 = 1824113) B1824113
theorem B1216087 : Blo 1215425 1216087 := bstep (se 1 (by rfl) ⟨912065, by rfl⟩ : syracuseStep 1216087 = 1824131) B1824131
theorem B1216107 : Blo 1215425 1216107 := bstep (se 1 (by rfl) ⟨912080, by rfl⟩ : syracuseStep 1216107 = 1824161) B1824161
theorem B1216119 : Blo 1215425 1216119 := bstep (se 1 (by rfl) ⟨912089, by rfl⟩ : syracuseStep 1216119 = 1824179) B1824179
theorem B2051723 : Blo 1215425 2051723 := bstep (se 1 (by rfl) ⟨1538792, by rfl⟩ : syracuseStep 2051723 = 3077585) B3077585
theorem B1216139 : Blo 1215425 1216139 := bstep (se 1 (by rfl) ⟨912104, by rfl⟩ : syracuseStep 1216139 = 1824209) B1824209
theorem B1216151 : Blo 1215425 1216151 := bstep (se 1 (by rfl) ⟨912113, by rfl⟩ : syracuseStep 1216151 = 1824227) B1824227
theorem B1216171 : Blo 1215425 1216171 := bstep (se 1 (by rfl) ⟨912128, by rfl⟩ : syracuseStep 1216171 = 1824257) B1824257
theorem B6246067 : Blo 1215425 6246067 := bstep (se 1 (by rfl) ⟨4684550, by rfl⟩ : syracuseStep 6246067 = 9369101) B9369101
theorem B1216183 : Blo 1215425 1216183 := bstep (se 1 (by rfl) ⟨912137, by rfl⟩ : syracuseStep 1216183 = 1824275) B1824275
theorem B1216203 : Blo 1215425 1216203 := bstep (se 1 (by rfl) ⟨912152, by rfl⟩ : syracuseStep 1216203 = 1824305) B1824305
theorem B1216215 : Blo 1215425 1216215 := bstep (se 1 (by rfl) ⟨912161, by rfl⟩ : syracuseStep 1216215 = 1824323) B1824323
theorem B1216235 : Blo 1215425 1216235 := bstep (se 1 (by rfl) ⟨912176, by rfl⟩ : syracuseStep 1216235 = 1824353) B1824353
theorem B1216247 : Blo 1215425 1216247 := bstep (se 1 (by rfl) ⟨912185, by rfl⟩ : syracuseStep 1216247 = 1824371) B1824371
theorem B2051851 : Blo 1215425 2051851 := bstep (se 1 (by rfl) ⟨1538888, by rfl⟩ : syracuseStep 2051851 = 3077777) B3077777
theorem B1216267 : Blo 1215425 1216267 := bstep (se 1 (by rfl) ⟨912200, by rfl⟩ : syracuseStep 1216267 = 1824401) B1824401
theorem B1216279 : Blo 1215425 1216279 := bstep (se 1 (by rfl) ⟨912209, by rfl⟩ : syracuseStep 1216279 = 1824419) B1824419
theorem B1216299 : Blo 1215425 1216299 := bstep (se 1 (by rfl) ⟨912224, by rfl⟩ : syracuseStep 1216299 = 1824449) B1824449
theorem B1216311 : Blo 1215425 1216311 := bstep (se 1 (by rfl) ⟨912233, by rfl⟩ : syracuseStep 1216311 = 1824467) B1824467
theorem B1216331 : Blo 1215425 1216331 := bstep (se 1 (by rfl) ⟨912248, by rfl⟩ : syracuseStep 1216331 = 1824497) B1824497
theorem B1216343 : Blo 1215425 1216343 := bstep (se 1 (by rfl) ⟨912257, by rfl⟩ : syracuseStep 1216343 = 1824515) B1824515
theorem B5001049 : Blo 1215425 5001049 := bstep (se 2 (by rfl) ⟨1875393, by rfl⟩ : syracuseStep 5001049 = 3750787) B3750787
theorem B1216363 : Blo 1215425 1216363 := bstep (se 1 (by rfl) ⟨912272, by rfl⟩ : syracuseStep 1216363 = 1824545) B1824545
theorem B1216375 : Blo 1215425 1216375 := bstep (se 1 (by rfl) ⟨912281, by rfl⟩ : syracuseStep 1216375 = 1824563) B1824563
theorem B1216395 : Blo 1215425 1216395 := bstep (se 1 (by rfl) ⟨912296, by rfl⟩ : syracuseStep 1216395 = 1824593) B1824593
theorem B1216407 : Blo 1215425 1216407 := bstep (se 1 (by rfl) ⟨912305, by rfl⟩ : syracuseStep 1216407 = 1824611) B1824611
theorem B2051993 : Blo 1215425 2051993 := bstep (se 2 (by rfl) ⟨769497, by rfl⟩ : syracuseStep 2051993 = 1538995) B1538995
theorem B1216427 : Blo 1215425 1216427 := bstep (se 1 (by rfl) ⟨912320, by rfl⟩ : syracuseStep 1216427 = 1824641) B1824641
theorem B4108211 : Blo 1215425 4108211 := bstep (se 1 (by rfl) ⟨3081158, by rfl⟩ : syracuseStep 4108211 = 6162317) B6162317
theorem B1216439 : Blo 1215425 1216439 := bstep (se 1 (by rfl) ⟨912329, by rfl⟩ : syracuseStep 1216439 = 1824659) B1824659
theorem B1216459 : Blo 1215425 1216459 := bstep (se 1 (by rfl) ⟨912344, by rfl⟩ : syracuseStep 1216459 = 1824689) B1824689
theorem B9236429 : Blo 1215425 9236429 := bstep (se 3 (by rfl) ⟨1731830, by rfl⟩ : syracuseStep 9236429 = 3463661) B3463661
theorem B1216471 : Blo 1215425 1216471 := bstep (se 1 (by rfl) ⟨912353, by rfl⟩ : syracuseStep 1216471 = 1824707) B1824707
theorem B1216491 : Blo 1215425 1216491 := bstep (se 1 (by rfl) ⟨912368, by rfl⟩ : syracuseStep 1216491 = 1824737) B1824737
theorem B1216503 : Blo 1215425 1216503 := bstep (se 1 (by rfl) ⟨912377, by rfl⟩ : syracuseStep 1216503 = 1824755) B1824755
theorem B1216523 : Blo 1215425 1216523 := bstep (se 1 (by rfl) ⟨912392, by rfl⟩ : syracuseStep 1216523 = 1824785) B1824785
theorem B1216535 : Blo 1215425 1216535 := bstep (se 1 (by rfl) ⟨912401, by rfl⟩ : syracuseStep 1216535 = 1824803) B1824803
theorem B2052121 : Blo 1215425 2052121 := bstep (se 2 (by rfl) ⟨769545, by rfl⟩ : syracuseStep 2052121 = 1539091) B1539091
theorem B1216555 : Blo 1215425 1216555 := bstep (se 1 (by rfl) ⟨912416, by rfl⟩ : syracuseStep 1216555 = 1824833) B1824833
theorem B1216567 : Blo 1215425 1216567 := bstep (se 1 (by rfl) ⟨912425, by rfl⟩ : syracuseStep 1216567 = 1824851) B1824851
theorem B6926411 : Blo 1215425 6926411 := bstep (se 1 (by rfl) ⟨5194808, by rfl⟩ : syracuseStep 6926411 = 10389617) B10389617
theorem B5845067 : Blo 1215425 5845067 := bstep (se 1 (by rfl) ⟨4383800, by rfl⟩ : syracuseStep 5845067 = 8767601) B8767601
theorem B1216587 : Blo 1215425 1216587 := bstep (se 1 (by rfl) ⟨912440, by rfl⟩ : syracuseStep 1216587 = 1824881) B1824881
theorem B1216599 : Blo 1215425 1216599 := bstep (se 1 (by rfl) ⟨912449, by rfl⟩ : syracuseStep 1216599 = 1824899) B1824899
theorem B1216619 : Blo 1215425 1216619 := bstep (se 1 (by rfl) ⟨912464, by rfl⟩ : syracuseStep 1216619 = 1824929) B1824929
theorem B2191475 : Blo 1215425 2191475 := bstep (se 1 (by rfl) ⟨1643606, by rfl⟩ : syracuseStep 2191475 = 3287213) B3287213
theorem B1216631 : Blo 1215425 1216631 := bstep (se 1 (by rfl) ⟨912473, by rfl⟩ : syracuseStep 1216631 = 1824947) B1824947
theorem B1216651 : Blo 1215425 1216651 := bstep (se 1 (by rfl) ⟨912488, by rfl⟩ : syracuseStep 1216651 = 1824977) B1824977
theorem B2961559 : Blo 1215425 2961559 := bstep (se 1 (by rfl) ⟨2221169, by rfl⟩ : syracuseStep 2961559 = 4442339) B4442339
theorem B23376023 : Blo 1215425 23376023 := bstep (se 1 (by rfl) ⟨17532017, by rfl⟩ : syracuseStep 23376023 = 35064035) B35064035
theorem B1216663 : Blo 1215425 1216663 := bstep (se 1 (by rfl) ⟨912497, by rfl⟩ : syracuseStep 1216663 = 1824995) B1824995
theorem B1216683 : Blo 1215425 1216683 := bstep (se 1 (by rfl) ⟨912512, by rfl⟩ : syracuseStep 1216683 = 1825025) B1825025
theorem B1216695 : Blo 1215425 1216695 := bstep (se 1 (by rfl) ⟨912521, by rfl⟩ : syracuseStep 1216695 = 1825043) B1825043
theorem B4108481 : Blo 1215425 4108481 := bstep (se 2 (by rfl) ⟨1540680, by rfl⟩ : syracuseStep 4108481 = 3081361) B3081361
theorem B1216715 : Blo 1215425 1216715 := bstep (se 1 (by rfl) ⟨912536, by rfl⟩ : syracuseStep 1216715 = 1825073) B1825073
theorem B2371799 : Blo 1215425 2371799 := bstep (se 1 (by rfl) ⟨1778849, by rfl⟩ : syracuseStep 2371799 = 3557699) B3557699
theorem B1216727 : Blo 1215425 1216727 := bstep (se 1 (by rfl) ⟨912545, by rfl⟩ : syracuseStep 1216727 = 1825091) B1825091
theorem B1216747 : Blo 1215425 1216747 := bstep (se 1 (by rfl) ⟨912560, by rfl⟩ : syracuseStep 1216747 = 1825121) B1825121
theorem B1216759 : Blo 1215425 1216759 := bstep (se 1 (by rfl) ⟨912569, by rfl⟩ : syracuseStep 1216759 = 1825139) B1825139
theorem B4501763 : Blo 1215425 4501763 := bstep (se 1 (by rfl) ⟨3376322, by rfl⟩ : syracuseStep 4501763 = 6752645) B6752645
theorem B26317061 : Blo 1215425 26317061 := bstep (se 4 (by rfl) ⟨2467224, by rfl⟩ : syracuseStep 26317061 = 4934449) B4934449
theorem B1216779 : Blo 1215425 1216779 := bstep (se 1 (by rfl) ⟨912584, by rfl⟩ : syracuseStep 1216779 = 1825169) B1825169
theorem B1298711 : Blo 1215425 1298711 := bstep (se 1 (by rfl) ⟨974033, by rfl⟩ : syracuseStep 1298711 = 1948067) B1948067
theorem B1216791 : Blo 1215425 1216791 := bstep (se 1 (by rfl) ⟨912593, by rfl⟩ : syracuseStep 1216791 = 1825187) B1825187
theorem B1216811 : Blo 1215425 1216811 := bstep (se 1 (by rfl) ⟨912608, by rfl⟩ : syracuseStep 1216811 = 1825217) B1825217
theorem B1216823 : Blo 1215425 1216823 := bstep (se 1 (by rfl) ⟨912617, by rfl⟩ : syracuseStep 1216823 = 1825235) B1825235
theorem B2191691 : Blo 1215425 2191691 := bstep (se 1 (by rfl) ⟨1643768, by rfl⟩ : syracuseStep 2191691 = 3287537) B3287537
theorem B1216843 : Blo 1215425 1216843 := bstep (se 1 (by rfl) ⟨912632, by rfl⟩ : syracuseStep 1216843 = 1825265) B1825265
theorem B10400075 : Blo 1215425 10400075 := bstep (se 1 (by rfl) ⟨7800056, by rfl⟩ : syracuseStep 10400075 = 15600113) B15600113
theorem B1216855 : Blo 1215425 1216855 := bstep (se 1 (by rfl) ⟨912641, by rfl⟩ : syracuseStep 1216855 = 1825283) B1825283
theorem B3699037 : Blo 1215425 3699037 := bstep (se 3 (by rfl) ⟨693569, by rfl⟩ : syracuseStep 3699037 = 1387139) B1387139
theorem B1216875 : Blo 1215425 1216875 := bstep (se 1 (by rfl) ⟨912656, by rfl⟩ : syracuseStep 1216875 = 1825313) B1825313
theorem B1216887 : Blo 1215425 1216887 := bstep (se 1 (by rfl) ⟨912665, by rfl⟩ : syracuseStep 1216887 = 1825331) B1825331
theorem B6238595 : Blo 1215425 6238595 := bstep (se 1 (by rfl) ⟨4678946, by rfl⟩ : syracuseStep 6238595 = 9357893) B9357893
theorem B1216907 : Blo 1215425 1216907 := bstep (se 1 (by rfl) ⟨912680, by rfl⟩ : syracuseStep 1216907 = 1825361) B1825361
theorem B1298839 : Blo 1215425 1298839 := bstep (se 1 (by rfl) ⟨974129, by rfl⟩ : syracuseStep 1298839 = 1948259) B1948259
theorem B1216919 : Blo 1215425 1216919 := bstep (se 1 (by rfl) ⟨912689, by rfl⟩ : syracuseStep 1216919 = 1825379) B1825379
theorem B1216939 : Blo 1215425 1216939 := bstep (se 1 (by rfl) ⟨912704, by rfl⟩ : syracuseStep 1216939 = 1825409) B1825409
theorem B4616621 : Blo 1215425 4616621 := bstep (se 3 (by rfl) ⟨865616, by rfl⟩ : syracuseStep 4616621 = 1731233) B1731233
theorem B3461555 : Blo 1215425 3461555 := bstep (se 1 (by rfl) ⟨2596166, by rfl⟩ : syracuseStep 3461555 = 5192333) B5192333
theorem B9236915 : Blo 1215425 9236915 := bstep (se 1 (by rfl) ⟨6927686, by rfl⟩ : syracuseStep 9236915 = 13855373) B13855373
theorem B1216951 : Blo 1215425 1216951 := bstep (se 1 (by rfl) ⟨912713, by rfl⟩ : syracuseStep 1216951 = 1825427) B1825427
theorem B1216971 : Blo 1215425 1216971 := bstep (se 1 (by rfl) ⟨912728, by rfl⟩ : syracuseStep 1216971 = 1825457) B1825457
theorem B1216983 : Blo 1215425 1216983 := bstep (se 1 (by rfl) ⟨912737, by rfl⟩ : syracuseStep 1216983 = 1825475) B1825475
theorem B1217003 : Blo 1215425 1217003 := bstep (se 1 (by rfl) ⟨912752, by rfl⟩ : syracuseStep 1217003 = 1825505) B1825505
theorem B1217015 : Blo 1215425 1217015 := bstep (se 1 (by rfl) ⟨912761, by rfl⟩ : syracuseStep 1217015 = 1825523) B1825523
theorem B1823243 : Blo 1215425 1823243 := bstep (se 1 (by rfl) ⟨1367432, by rfl⟩ : syracuseStep 1823243 = 2734865) B2734865
theorem B1217035 : Blo 1215425 1217035 := bstep (se 1 (by rfl) ⟨912776, by rfl⟩ : syracuseStep 1217035 = 1825553) B1825553
theorem B1823255 : Blo 1215425 1823255 := bstep (se 1 (by rfl) ⟨1367441, by rfl⟩ : syracuseStep 1823255 = 2734883) B2734883
theorem B1217047 : Blo 1215425 1217047 := bstep (se 1 (by rfl) ⟨912785, by rfl⟩ : syracuseStep 1217047 = 1825571) B1825571
theorem B1217067 : Blo 1215425 1217067 := bstep (se 1 (by rfl) ⟨912800, by rfl⟩ : syracuseStep 1217067 = 1825601) B1825601
theorem B1217079 : Blo 1215425 1217079 := bstep (se 1 (by rfl) ⟨912809, by rfl⟩ : syracuseStep 1217079 = 1825619) B1825619
theorem B4878913 : Blo 1215425 4878913 := bstep (se 2 (by rfl) ⟨1829592, by rfl⟩ : syracuseStep 4878913 = 3659185) B3659185
theorem B1217099 : Blo 1215425 1217099 := bstep (se 1 (by rfl) ⟨912824, by rfl⟩ : syracuseStep 1217099 = 1825649) B1825649
theorem B2052695 : Blo 1215425 2052695 := bstep (se 1 (by rfl) ⟨1539521, by rfl⟩ : syracuseStep 2052695 = 3079043) B3079043
theorem B1217111 : Blo 1215425 1217111 := bstep (se 1 (by rfl) ⟨912833, by rfl⟩ : syracuseStep 1217111 = 1825667) B1825667
theorem B1823321 : Blo 1215425 1823321 := bstep (se 2 (by rfl) ⟨683745, by rfl⟩ : syracuseStep 1823321 = 1367491) B1367491
theorem B1217131 : Blo 1215425 1217131 := bstep (se 1 (by rfl) ⟨912848, by rfl⟩ : syracuseStep 1217131 = 1825697) B1825697
theorem B1217143 : Blo 1215425 1217143 := bstep (se 1 (by rfl) ⟨912857, by rfl⟩ : syracuseStep 1217143 = 1825715) B1825715
theorem B1217163 : Blo 1215425 1217163 := bstep (se 1 (by rfl) ⟨912872, by rfl⟩ : syracuseStep 1217163 = 1825745) B1825745
theorem B1217175 : Blo 1215425 1217175 := bstep (se 1 (by rfl) ⟨912881, by rfl⟩ : syracuseStep 1217175 = 1825763) B1825763
theorem B1217195 : Blo 1215425 1217195 := bstep (se 1 (by rfl) ⟨912896, by rfl⟩ : syracuseStep 1217195 = 1825793) B1825793
theorem B1217207 : Blo 1215425 1217207 := bstep (se 1 (by rfl) ⟨912905, by rfl⟩ : syracuseStep 1217207 = 1825811) B1825811
theorem B1823435 : Blo 1215425 1823435 := bstep (se 1 (by rfl) ⟨1367576, by rfl⟩ : syracuseStep 1823435 = 2735153) B2735153
theorem B1217227 : Blo 1215425 1217227 := bstep (se 1 (by rfl) ⟨912920, by rfl⟩ : syracuseStep 1217227 = 1825841) B1825841
theorem B1823447 : Blo 1215425 1823447 := bstep (se 1 (by rfl) ⟨1367585, by rfl⟩ : syracuseStep 1823447 = 2735171) B2735171
theorem B2052823 : Blo 1215425 2052823 := bstep (se 1 (by rfl) ⟨1539617, by rfl⟩ : syracuseStep 2052823 = 3079235) B3079235
theorem B3076825 : Blo 1215425 3076825 := bstep (se 2 (by rfl) ⟨1153809, by rfl⟩ : syracuseStep 3076825 = 2307619) B2307619
theorem B1217239 : Blo 1215425 1217239 := bstep (se 1 (by rfl) ⟨912929, by rfl⟩ : syracuseStep 1217239 = 1825859) B1825859
theorem B1217259 : Blo 1215425 1217259 := bstep (se 1 (by rfl) ⟨912944, by rfl⟩ : syracuseStep 1217259 = 1825889) B1825889
theorem B1217271 : Blo 1215425 1217271 := bstep (se 1 (by rfl) ⟨912953, by rfl⟩ : syracuseStep 1217271 = 1825907) B1825907
theorem B1217291 : Blo 1215425 1217291 := bstep (se 1 (by rfl) ⟨912968, by rfl⟩ : syracuseStep 1217291 = 1825937) B1825937
theorem B1217303 : Blo 1215425 1217303 := bstep (se 1 (by rfl) ⟨912977, by rfl⟩ : syracuseStep 1217303 = 1825955) B1825955
theorem B1823513 : Blo 1215425 1823513 := bstep (se 2 (by rfl) ⟨683817, by rfl⟩ : syracuseStep 1823513 = 1367635) B1367635
theorem B8885027 : Blo 1215425 8885027 := bstep (se 1 (by rfl) ⟨6663770, by rfl⟩ : syracuseStep 8885027 = 13327541) B13327541
theorem B1217323 : Blo 1215425 1217323 := bstep (se 1 (by rfl) ⟨912992, by rfl⟩ : syracuseStep 1217323 = 1825985) B1825985
theorem B1217335 : Blo 1215425 1217335 := bstep (se 1 (by rfl) ⟨913001, by rfl⟩ : syracuseStep 1217335 = 1826003) B1826003
theorem B3461953 : Blo 1215425 3461953 := bstep (se 2 (by rfl) ⟨1298232, by rfl⟩ : syracuseStep 3461953 = 2596465) B2596465
theorem B6239051 : Blo 1215425 6239051 := bstep (se 1 (by rfl) ⟨4679288, by rfl⟩ : syracuseStep 6239051 = 9358577) B9358577
theorem B1217355 : Blo 1215425 1217355 := bstep (se 1 (by rfl) ⟨913016, by rfl⟩ : syracuseStep 1217355 = 1826033) B1826033
theorem B1217367 : Blo 1215425 1217367 := bstep (se 1 (by rfl) ⟨913025, by rfl⟩ : syracuseStep 1217367 = 1826051) B1826051
theorem B1217387 : Blo 1215425 1217387 := bstep (se 1 (by rfl) ⟨913040, by rfl⟩ : syracuseStep 1217387 = 1826081) B1826081
theorem B1217399 : Blo 1215425 1217399 := bstep (se 1 (by rfl) ⟨913049, by rfl⟩ : syracuseStep 1217399 = 1826099) B1826099
theorem B1823627 : Blo 1215425 1823627 := bstep (se 1 (by rfl) ⟨1367720, by rfl⟩ : syracuseStep 1823627 = 2735441) B2735441
theorem B1217419 : Blo 1215425 1217419 := bstep (se 1 (by rfl) ⟨913064, by rfl⟩ : syracuseStep 1217419 = 1826129) B1826129
theorem B4928401 : Blo 1215425 4928401 := bstep (se 2 (by rfl) ⟨1848150, by rfl⟩ : syracuseStep 4928401 = 3696301) B3696301
theorem B1823639 : Blo 1215425 1823639 := bstep (se 1 (by rfl) ⟨1367729, by rfl⟩ : syracuseStep 1823639 = 2735459) B2735459
theorem B1299403 : Blo 1215425 1299403 := bstep (se 1 (by rfl) ⟨974552, by rfl⟩ : syracuseStep 1299403 = 1949105) B1949105
theorem B1823705 : Blo 1215425 1823705 := bstep (se 2 (by rfl) ⟨683889, by rfl⟩ : syracuseStep 1823705 = 1367779) B1367779
theorem B1823819 : Blo 1215425 1823819 := bstep (se 1 (by rfl) ⟨1367864, by rfl⟩ : syracuseStep 1823819 = 2735729) B2735729
theorem B1823831 : Blo 1215425 1823831 := bstep (se 1 (by rfl) ⟨1367873, by rfl⟩ : syracuseStep 1823831 = 2735747) B2735747
theorem B1823897 : Blo 1215425 1823897 := bstep (se 2 (by rfl) ⟨683961, by rfl⟩ : syracuseStep 1823897 = 1367923) B1367923
theorem B4617395 : Blo 1215425 4617395 := bstep (se 1 (by rfl) ⟨3463046, by rfl⟩ : syracuseStep 4617395 = 6926093) B6926093
theorem B1299659 : Blo 1215425 1299659 := bstep (se 1 (by rfl) ⟨974744, by rfl⟩ : syracuseStep 1299659 = 1949489) B1949489
theorem B2192599 : Blo 1215425 2192599 := bstep (se 1 (by rfl) ⟨1644449, by rfl⟩ : syracuseStep 2192599 = 3288899) B3288899
theorem B2192627 : Blo 1215425 2192627 := bstep (se 1 (by rfl) ⟨1644470, by rfl⟩ : syracuseStep 2192627 = 3288941) B3288941
theorem B1824011 : Blo 1215425 1824011 := bstep (se 1 (by rfl) ⟨1368008, by rfl⟩ : syracuseStep 1824011 = 2736017) B2736017
theorem B1824023 : Blo 1215425 1824023 := bstep (se 1 (by rfl) ⟨1368017, by rfl⟩ : syracuseStep 1824023 = 2736035) B2736035
theorem B2053451 : Blo 1215425 2053451 := bstep (se 1 (by rfl) ⟨1540088, by rfl⟩ : syracuseStep 2053451 = 3080177) B3080177
theorem B1824089 : Blo 1215425 1824089 := bstep (se 2 (by rfl) ⟨684033, by rfl⟩ : syracuseStep 1824089 = 1368067) B1368067
theorem B2307467 : Blo 1215425 2307467 := bstep (se 1 (by rfl) ⟨1730600, by rfl⟩ : syracuseStep 2307467 = 3461201) B3461201
theorem B12490163 : Blo 1215425 12490163 := bstep (se 1 (by rfl) ⟨9367622, by rfl⟩ : syracuseStep 12490163 = 18735245) B18735245
theorem B2307521 : Blo 1215425 2307521 := bstep (se 2 (by rfl) ⟨865320, by rfl⟩ : syracuseStep 2307521 = 1730641) B1730641
theorem B1824203 : Blo 1215425 1824203 := bstep (se 1 (by rfl) ⟨1368152, by rfl⟩ : syracuseStep 1824203 = 2736305) B2736305
theorem B2053579 : Blo 1215425 2053579 := bstep (se 1 (by rfl) ⟨1540184, by rfl⟩ : syracuseStep 2053579 = 3080369) B3080369
theorem B1824215 : Blo 1215425 1824215 := bstep (se 1 (by rfl) ⟨1368161, by rfl⟩ : syracuseStep 1824215 = 2736323) B2736323
theorem B2373143 : Blo 1215425 2373143 := bstep (se 1 (by rfl) ⟨1779857, by rfl⟩ : syracuseStep 2373143 = 3559715) B3559715
theorem B1824281 : Blo 1215425 1824281 := bstep (se 2 (by rfl) ⟨684105, by rfl⟩ : syracuseStep 1824281 = 1368211) B1368211
theorem B2053721 : Blo 1215425 2053721 := bstep (se 2 (by rfl) ⟨770145, by rfl⟩ : syracuseStep 2053721 = 1540291) B1540291
theorem B5199491 : Blo 1215425 5199491 := bstep (se 1 (by rfl) ⟨3899618, by rfl⟩ : syracuseStep 5199491 = 7799237) B7799237
theorem B1824395 : Blo 1215425 1824395 := bstep (se 1 (by rfl) ⟨1368296, by rfl⟩ : syracuseStep 1824395 = 2736593) B2736593
theorem B1824407 : Blo 1215425 1824407 := bstep (se 1 (by rfl) ⟨1368305, by rfl⟩ : syracuseStep 1824407 = 2736611) B2736611
theorem B6928051 : Blo 1215425 6928051 := bstep (se 1 (by rfl) ⟨5196038, by rfl⟩ : syracuseStep 6928051 = 10392077) B10392077
theorem B1824473 : Blo 1215425 1824473 := bstep (se 2 (by rfl) ⟨684177, by rfl⟩ : syracuseStep 1824473 = 1368355) B1368355
theorem B2053849 : Blo 1215425 2053849 := bstep (se 2 (by rfl) ⟨770193, by rfl⟩ : syracuseStep 2053849 = 1540387) B1540387
theorem B11089669 : Blo 1215425 11089669 := bstep (se 4 (by rfl) ⟨1039656, by rfl⟩ : syracuseStep 11089669 = 2079313) B2079313
theorem B3077939 : Blo 1215425 3077939 := bstep (se 1 (by rfl) ⟨2308454, by rfl⟩ : syracuseStep 3077939 = 4616909) B4616909
theorem B1824587 : Blo 1215425 1824587 := bstep (se 1 (by rfl) ⟨1368440, by rfl⟩ : syracuseStep 1824587 = 2736881) B2736881
theorem B1824599 : Blo 1215425 1824599 := bstep (se 1 (by rfl) ⟨1368449, by rfl⟩ : syracuseStep 1824599 = 2736899) B2736899
theorem B7796573 : Blo 1215425 7796573 := bstep (se 3 (by rfl) ⟨1461857, by rfl⟩ : syracuseStep 7796573 = 2923715) B2923715
theorem B9238373 : Blo 1215425 9238373 := bstep (se 4 (by rfl) ⟨866097, by rfl⟩ : syracuseStep 9238373 = 1732195) B1732195
theorem B1824665 : Blo 1215425 1824665 := bstep (se 2 (by rfl) ⟨684249, by rfl⟩ : syracuseStep 1824665 = 1368499) B1368499
theorem B4102109 : Blo 1215425 4102109 := bstep (se 3 (by rfl) ⟨769145, by rfl⟩ : syracuseStep 4102109 = 1538291) B1538291
theorem B1824779 : Blo 1215425 1824779 := bstep (se 1 (by rfl) ⟨1368584, by rfl⟩ : syracuseStep 1824779 = 2737169) B2737169
theorem B1824791 : Blo 1215425 1824791 := bstep (se 1 (by rfl) ⟨1368593, by rfl⟩ : syracuseStep 1824791 = 2737187) B2737187
theorem B22181957 : Blo 1215425 22181957 := bstep (se 4 (by rfl) ⟨2079558, by rfl⟩ : syracuseStep 22181957 = 4159117) B4159117
theorem B3078233 : Blo 1215425 3078233 := bstep (se 2 (by rfl) ⟨1154337, by rfl⟩ : syracuseStep 3078233 = 2308675) B2308675
theorem B1824857 : Blo 1215425 1824857 := bstep (se 2 (by rfl) ⟨684321, by rfl⟩ : syracuseStep 1824857 = 1368643) B1368643
theorem B6158429 : Blo 1215425 6158429 := bstep (se 3 (by rfl) ⟨1154705, by rfl⟩ : syracuseStep 6158429 = 2309411) B2309411
theorem B4159667 : Blo 1215425 4159667 := bstep (se 1 (by rfl) ⟨3119750, by rfl⟩ : syracuseStep 4159667 = 6239501) B6239501
theorem B24967349 : Blo 1215425 24967349 := bstep (se 5 (by rfl) ⟨1170344, by rfl⟩ : syracuseStep 24967349 = 2340689) B2340689
theorem B1824971 : Blo 1215425 1824971 := bstep (se 1 (by rfl) ⟨1368728, by rfl⟩ : syracuseStep 1824971 = 2737457) B2737457
theorem B1824983 : Blo 1215425 1824983 := bstep (se 1 (by rfl) ⟨1368737, by rfl⟩ : syracuseStep 1824983 = 2737475) B2737475
theorem B9230597 : Blo 1215425 9230597 := bstep (se 4 (by rfl) ⟨865368, by rfl⟩ : syracuseStep 9230597 = 1730737) B1730737
theorem B1825049 : Blo 1215425 1825049 := bstep (se 2 (by rfl) ⟨684393, by rfl⟩ : syracuseStep 1825049 = 1368787) B1368787
theorem B9238859 : Blo 1215425 9238859 := bstep (se 1 (by rfl) ⟨6929144, by rfl⟩ : syracuseStep 9238859 = 13858289) B13858289
theorem B2308439 : Blo 1215425 2308439 := bstep (se 1 (by rfl) ⟨1731329, by rfl⟩ : syracuseStep 2308439 = 3462659) B3462659
theorem B20789621 : Blo 1215425 20789621 := bstep (se 5 (by rfl) ⟨974513, by rfl⟩ : syracuseStep 20789621 = 1949027) B1949027
theorem B1538443 : Blo 1215425 1538443 := bstep (se 1 (by rfl) ⟨1153832, by rfl⟩ : syracuseStep 1538443 = 2307665) B2307665
theorem B1825163 : Blo 1215425 1825163 := bstep (se 1 (by rfl) ⟨1368872, by rfl⟩ : syracuseStep 1825163 = 2737745) B2737745
theorem B1825175 : Blo 1215425 1825175 := bstep (se 1 (by rfl) ⟨1368881, by rfl⟩ : syracuseStep 1825175 = 2737763) B2737763
theorem B1825241 : Blo 1215425 1825241 := bstep (se 2 (by rfl) ⟨684465, by rfl⟩ : syracuseStep 1825241 = 1368931) B1368931
theorem B9361955 : Blo 1215425 9361955 := bstep (se 1 (by rfl) ⟨7021466, by rfl⟩ : syracuseStep 9361955 = 14042933) B14042933
theorem B1825355 : Blo 1215425 1825355 := bstep (se 1 (by rfl) ⟨1369016, by rfl⟩ : syracuseStep 1825355 = 2738033) B2738033
theorem B1825367 : Blo 1215425 1825367 := bstep (se 1 (by rfl) ⟨1369025, by rfl⟩ : syracuseStep 1825367 = 2738051) B2738051
theorem B2734721 : Blo 1215425 2734721 := bstep (se 2 (by rfl) ⟨1025520, by rfl⟩ : syracuseStep 2734721 = 2051041) B2051041
theorem B7494275 : Blo 1215425 7494275 := bstep (se 1 (by rfl) ⟨5620706, by rfl⟩ : syracuseStep 7494275 = 11241413) B11241413
theorem B4618883 : Blo 1215425 4618883 := bstep (se 1 (by rfl) ⟨3464162, by rfl⟩ : syracuseStep 4618883 = 6928325) B6928325
theorem B1825433 : Blo 1215425 1825433 := bstep (se 2 (by rfl) ⟨684537, by rfl⟩ : syracuseStep 1825433 = 1369075) B1369075
theorem B1825547 : Blo 1215425 1825547 := bstep (se 1 (by rfl) ⟨1369160, by rfl⟩ : syracuseStep 1825547 = 2738321) B2738321
theorem B1825559 : Blo 1215425 1825559 := bstep (se 1 (by rfl) ⟨1369169, by rfl⟩ : syracuseStep 1825559 = 2738339) B2738339
theorem B2734937 : Blo 1215425 2734937 := bstep (se 2 (by rfl) ⟨1025601, by rfl⟩ : syracuseStep 2734937 = 2051203) B2051203
theorem B1825625 : Blo 1215425 1825625 := bstep (se 2 (by rfl) ⟨684609, by rfl⟩ : syracuseStep 1825625 = 1369219) B1369219
theorem B2308979 : Blo 1215425 2308979 := bstep (se 1 (by rfl) ⟨1731734, by rfl⟩ : syracuseStep 2308979 = 3463469) B3463469
theorem B4684675 : Blo 1215425 4684675 := bstep (se 1 (by rfl) ⟨3513506, by rfl⟩ : syracuseStep 4684675 = 7027013) B7027013
theorem B2735027 : Blo 1215425 2735027 := bstep (se 1 (by rfl) ⟨2051270, by rfl⟩ : syracuseStep 2735027 = 4102541) B4102541
theorem B1825739 : Blo 1215425 1825739 := bstep (se 1 (by rfl) ⟨1369304, by rfl⟩ : syracuseStep 1825739 = 2738609) B2738609
theorem B2735063 : Blo 1215425 2735063 := bstep (se 1 (by rfl) ⟨2051297, by rfl⟩ : syracuseStep 2735063 = 4102595) B4102595
theorem B1825751 : Blo 1215425 1825751 := bstep (se 1 (by rfl) ⟨1369313, by rfl⟩ : syracuseStep 1825751 = 2738627) B2738627
theorem B1825817 : Blo 1215425 1825817 := bstep (se 2 (by rfl) ⟨684681, by rfl⟩ : syracuseStep 1825817 = 1369363) B1369363
theorem B4103243 : Blo 1215425 4103243 := bstep (se 1 (by rfl) ⟨3077432, by rfl⟩ : syracuseStep 4103243 = 6154865) B6154865
theorem B4619339 : Blo 1215425 4619339 := bstep (se 1 (by rfl) ⟨3464504, by rfl⟩ : syracuseStep 4619339 = 6929009) B6929009
theorem B2923609 : Blo 1215425 2923609 := bstep (se 2 (by rfl) ⟨1096353, by rfl⟩ : syracuseStep 2923609 = 2192707) B2192707
theorem B6929509 : Blo 1215425 6929509 := bstep (se 4 (by rfl) ⟨649641, by rfl⟩ : syracuseStep 6929509 = 1299283) B1299283
theorem B2735243 : Blo 1215425 2735243 := bstep (se 1 (by rfl) ⟨2051432, by rfl⟩ : syracuseStep 2735243 = 4102865) B4102865
theorem B1825931 : Blo 1215425 1825931 := bstep (se 1 (by rfl) ⟨1369448, by rfl⟩ : syracuseStep 1825931 = 2738897) B2738897
theorem B1825943 : Blo 1215425 1825943 := bstep (se 1 (by rfl) ⟨1369457, by rfl⟩ : syracuseStep 1825943 = 2738915) B2738915
theorem B2735297 : Blo 1215425 2735297 := bstep (se 2 (by rfl) ⟨1025736, by rfl⟩ : syracuseStep 2735297 = 2051473) B2051473
theorem B1826009 : Blo 1215425 1826009 := bstep (se 2 (by rfl) ⟨684753, by rfl⟩ : syracuseStep 1826009 = 1369507) B1369507
theorem B4619537 : Blo 1215425 4619537 := bstep (se 2 (by rfl) ⟨1732326, by rfl⟩ : syracuseStep 4619537 = 3464653) B3464653
theorem B3464471 : Blo 1215425 3464471 := bstep (se 1 (by rfl) ⟨2598353, by rfl⟩ : syracuseStep 3464471 = 5196707) B5196707
theorem B1948951 : Blo 1215425 1948951 := bstep (se 1 (by rfl) ⟨1461713, by rfl⟩ : syracuseStep 1948951 = 2923427) B2923427
theorem B1826123 : Blo 1215425 1826123 := bstep (se 1 (by rfl) ⟨1369592, by rfl⟩ : syracuseStep 1826123 = 2739185) B2739185
theorem B1367383 : Blo 1215425 1367383 := bstep (se 1 (by rfl) ⟨1025537, by rfl⟩ : syracuseStep 1367383 = 2051075) B2051075
theorem B1539415 : Blo 1215425 1539415 := bstep (se 1 (by rfl) ⟨1154561, by rfl⟩ : syracuseStep 1539415 = 2309123) B2309123
theorem B4103513 : Blo 1215425 4103513 := bstep (se 2 (by rfl) ⟨1538817, by rfl⟩ : syracuseStep 4103513 = 3077635) B3077635
theorem B2309465 : Blo 1215425 2309465 := bstep (se 2 (by rfl) ⟨866049, by rfl⟩ : syracuseStep 2309465 = 1732099) B1732099
theorem B1826135 : Blo 1215425 1826135 := bstep (se 1 (by rfl) ⟨1369601, by rfl⟩ : syracuseStep 1826135 = 2739203) B2739203
theorem B9485669 : Blo 1215425 9485669 := bstep (se 4 (by rfl) ⟨889281, by rfl⟩ : syracuseStep 9485669 = 1778563) B1778563
theorem B2735513 : Blo 1215425 2735513 := bstep (se 2 (by rfl) ⟨1025817, by rfl⟩ : syracuseStep 2735513 = 2051635) B2051635
theorem B2735603 : Blo 1215425 2735603 := bstep (se 1 (by rfl) ⟨2051702, by rfl⟩ : syracuseStep 2735603 = 4103405) B4103405
theorem B1367563 : Blo 1215425 1367563 := bstep (se 1 (by rfl) ⟨1025672, by rfl⟩ : syracuseStep 1367563 = 2051345) B2051345
theorem B2735639 : Blo 1215425 2735639 := bstep (se 1 (by rfl) ⟨2051729, by rfl⟩ : syracuseStep 2735639 = 4103459) B4103459
theorem B8764973 : Blo 1215425 8764973 := bstep (se 3 (by rfl) ⟨1643432, by rfl⟩ : syracuseStep 8764973 = 3286865) B3286865
theorem B5193305 : Blo 1215425 5193305 := bstep (se 2 (by rfl) ⟨1947489, by rfl⟩ : syracuseStep 5193305 = 3894979) B3894979
theorem B2342515 : Blo 1215425 2342515 := bstep (se 1 (by rfl) ⟨1756886, by rfl⟩ : syracuseStep 2342515 = 3513773) B3513773
theorem B1367671 : Blo 1215425 1367671 := bstep (se 1 (by rfl) ⟨1025753, by rfl⟩ : syracuseStep 1367671 = 2051507) B2051507
theorem B2924225 : Blo 1215425 2924225 := bstep (se 2 (by rfl) ⟨1096584, by rfl⟩ : syracuseStep 2924225 = 2193169) B2193169
theorem B2735819 : Blo 1215425 2735819 := bstep (se 1 (by rfl) ⟨2051864, by rfl⟩ : syracuseStep 2735819 = 4103729) B4103729
theorem B3079883 : Blo 1215425 3079883 := bstep (se 1 (by rfl) ⟨2309912, by rfl⟩ : syracuseStep 3079883 = 4619825) B4619825
theorem B2735873 : Blo 1215425 2735873 := bstep (se 2 (by rfl) ⟨1025952, by rfl⟩ : syracuseStep 2735873 = 2051905) B2051905
theorem B2596619 : Blo 1215425 2596619 := bstep (se 1 (by rfl) ⟨1947464, by rfl⟩ : syracuseStep 2596619 = 3894929) B3894929
theorem B1367851 : Blo 1215425 1367851 := bstep (se 1 (by rfl) ⟨1025888, by rfl⟩ : syracuseStep 1367851 = 2051777) B2051777
theorem B7495517 : Blo 1215425 7495517 := bstep (se 3 (by rfl) ⟨1405409, by rfl⟩ : syracuseStep 7495517 = 2810819) B2810819
theorem B1367959 : Blo 1215425 1367959 := bstep (se 1 (by rfl) ⟨1025969, by rfl⟩ : syracuseStep 1367959 = 2051939) B2051939
theorem B2736089 : Blo 1215425 2736089 := bstep (se 2 (by rfl) ⟨1026033, by rfl⟩ : syracuseStep 2736089 = 2052067) B2052067
theorem B2736143 : Blo 1215425 2736143 := bstep (se 1 (by rfl) ⟨2052107, by rfl⟩ : syracuseStep 2736143 = 4104215) B4104215
theorem B3080207 : Blo 1215425 3080207 := bstep (se 1 (by rfl) ⟨2310155, by rfl⟩ : syracuseStep 3080207 = 4620311) B4620311
theorem B2736161 : Blo 1215425 2736161 := bstep (se 2 (by rfl) ⟨1026060, by rfl⟩ : syracuseStep 2736161 = 2052121) B2052121
theorem B3080339 : Blo 1215425 3080339 := bstep (se 1 (by rfl) ⟨2310254, by rfl⟩ : syracuseStep 3080339 = 4620509) B4620509
theorem B3948745 : Blo 1215425 3948745 := bstep (se 2 (by rfl) ⟨1480779, by rfl⟩ : syracuseStep 3948745 = 2961559) B2961559
theorem B2736503 : Blo 1215425 2736503 := bstep (se 1 (by rfl) ⟨2052377, by rfl⟩ : syracuseStep 2736503 = 4104755) B4104755
theorem B2310535 : Blo 1215425 2310535 := bstep (se 1 (by rfl) ⟨1732901, by rfl⟩ : syracuseStep 2310535 = 3465803) B3465803
theorem B1368463 : Blo 1215425 1368463 := bstep (se 1 (by rfl) ⟨1026347, by rfl⟩ : syracuseStep 1368463 = 2052695) B2052695
theorem B1540615 : Blo 1215425 1540615 := bstep (se 1 (by rfl) ⟨1155461, by rfl⟩ : syracuseStep 1540615 = 2310923) B2310923
theorem B5923351 : Blo 1215425 5923351 := bstep (se 1 (by rfl) ⟨4442513, by rfl⟩ : syracuseStep 5923351 = 8885027) B8885027
theorem B6930967 : Blo 1215425 6930967 := bstep (se 1 (by rfl) ⟨5198225, by rfl⟩ : syracuseStep 6930967 = 10396451) B10396451
theorem B3465757 : Blo 1215425 3465757 := bstep (se 3 (by rfl) ⟨649829, by rfl⟩ : syracuseStep 3465757 = 1299659) B1299659
theorem B2736683 : Blo 1215425 2736683 := bstep (se 1 (by rfl) ⟨2052512, by rfl⟩ : syracuseStep 2736683 = 4105025) B4105025
theorem B6324797 : Blo 1215425 6324797 := bstep (se 3 (by rfl) ⟨1185899, by rfl⟩ : syracuseStep 6324797 = 2371799) B2371799
theorem B24986231 : Blo 1215425 24986231 := bstep (se 1 (by rfl) ⟨18739673, by rfl⟩ : syracuseStep 24986231 = 37479347) B37479347
theorem B3465929 : Blo 1215425 3465929 := bstep (se 2 (by rfl) ⟨1299723, by rfl⟩ : syracuseStep 3465929 = 2599447) B2599447
theorem B3465985 : Blo 1215425 3465985 := bstep (se 2 (by rfl) ⟨1299744, by rfl⟩ : syracuseStep 3465985 = 2599489) B2599489
theorem B6505217 : Blo 1215425 6505217 := bstep (se 2 (by rfl) ⟨2439456, by rfl⟩ : syracuseStep 6505217 = 4878913) B4878913
theorem B1368967 : Blo 1215425 1368967 := bstep (se 1 (by rfl) ⟨1026725, by rfl⟩ : syracuseStep 1368967 = 2053451) B2053451
theorem B2737043 : Blo 1215425 2737043 := bstep (se 1 (by rfl) ⟨2052782, by rfl⟩ : syracuseStep 2737043 = 4105565) B4105565
theorem B2737097 : Blo 1215425 2737097 := bstep (se 2 (by rfl) ⟨1026411, by rfl⟩ : syracuseStep 2737097 = 2052823) B2052823
theorem B6153245 : Blo 1215425 6153245 := bstep (se 3 (by rfl) ⟨1153733, by rfl⟩ : syracuseStep 6153245 = 2307467) B2307467
theorem B1369147 : Blo 1215425 1369147 := bstep (se 1 (by rfl) ⟨1026860, by rfl⟩ : syracuseStep 1369147 = 2053721) B2053721
theorem B3466327 : Blo 1215425 3466327 := bstep (se 1 (by rfl) ⟨2599745, by rfl⟩ : syracuseStep 3466327 = 5199491) B5199491
theorem B6571201 : Blo 1215425 6571201 := bstep (se 2 (by rfl) ⟨2464200, by rfl⟩ : syracuseStep 6571201 = 4928401) B4928401
theorem B3081473 : Blo 1215425 3081473 := bstep (se 2 (by rfl) ⟨1155552, by rfl⟩ : syracuseStep 3081473 = 2311105) B2311105
theorem B14787971 : Blo 1215425 14787971 := bstep (se 1 (by rfl) ⟨11090978, by rfl⟩ : syracuseStep 14787971 = 22181957) B22181957
theorem B7800209 : Blo 1215425 7800209 := bstep (se 2 (by rfl) ⟨2925078, by rfl⟩ : syracuseStep 7800209 = 5850157) B5850157
theorem B4105619 : Blo 1215425 4105619 := bstep (se 1 (by rfl) ⟨3079214, by rfl⟩ : syracuseStep 4105619 = 6158429) B6158429
theorem B6153731 : Blo 1215425 6153731 := bstep (se 1 (by rfl) ⟨4615298, by rfl⟩ : syracuseStep 6153731 = 9230597) B9230597
theorem B2737799 : Blo 1215425 2737799 := bstep (se 1 (by rfl) ⟨2053349, by rfl⟩ : syracuseStep 2737799 = 4106699) B4106699
theorem B3696313 : Blo 1215425 3696313 := bstep (se 2 (by rfl) ⟨1386117, by rfl⟩ : syracuseStep 3696313 = 2772235) B2772235
theorem B2598601 : Blo 1215425 2598601 := bstep (se 2 (by rfl) ⟨974475, by rfl⟩ : syracuseStep 2598601 = 1948951) B1948951
theorem B9357029 : Blo 1215425 9357029 := bstep (se 4 (by rfl) ⟨877221, by rfl⟩ : syracuseStep 9357029 = 1754443) B1754443
theorem B2737979 : Blo 1215425 2737979 := bstep (se 1 (by rfl) ⟨2053484, by rfl⟩ : syracuseStep 2737979 = 4106969) B4106969
theorem B19728197 : Blo 1215425 19728197 := bstep (se 4 (by rfl) ⟨1849518, by rfl⟩ : syracuseStep 19728197 = 3699037) B3699037
theorem B2738105 : Blo 1215425 2738105 := bstep (se 2 (by rfl) ⟨1026789, by rfl⟩ : syracuseStep 2738105 = 2053579) B2053579
theorem B3123353 : Blo 1215425 3123353 := bstep (se 2 (by rfl) ⟨1171257, by rfl⟩ : syracuseStep 3123353 = 2342515) B2342515
theorem B2738447 : Blo 1215425 2738447 := bstep (se 1 (by rfl) ⟨2053835, by rfl⟩ : syracuseStep 2738447 = 4107671) B4107671
theorem B2738465 : Blo 1215425 2738465 := bstep (se 2 (by rfl) ⟨1026924, by rfl⟩ : syracuseStep 2738465 = 2053849) B2053849
theorem B5843315 : Blo 1215425 5843315 := bstep (se 1 (by rfl) ⟨4382486, by rfl⟩ : syracuseStep 5843315 = 8764973) B8764973
theorem B6162803 : Blo 1215425 6162803 := bstep (se 1 (by rfl) ⟨4622102, by rfl⟩ : syracuseStep 6162803 = 9244205) B9244205
theorem B1731079 : Blo 1215425 1731079 := bstep (se 1 (by rfl) ⟨1298309, by rfl⟩ : syracuseStep 1731079 = 2596619) B2596619
theorem B2738807 : Blo 1215425 2738807 := bstep (se 1 (by rfl) ⟨2054105, by rfl⟩ : syracuseStep 2738807 = 4108211) B4108211
theorem B2599609 : Blo 1215425 2599609 := bstep (se 2 (by rfl) ⟨974853, by rfl⟩ : syracuseStep 2599609 = 1949707) B1949707
theorem B1460983 : Blo 1215425 1460983 := bstep (se 1 (by rfl) ⟨1095737, by rfl⟩ : syracuseStep 1460983 = 2191475) B2191475
theorem B15584015 : Blo 1215425 15584015 := bstep (se 1 (by rfl) ⟨11688011, by rfl⟩ : syracuseStep 15584015 = 23376023) B23376023
theorem B4107023 : Blo 1215425 4107023 := bstep (se 1 (by rfl) ⟨3080267, by rfl⟩ : syracuseStep 4107023 = 6160535) B6160535
theorem B2738987 : Blo 1215425 2738987 := bstep (se 1 (by rfl) ⟨2054240, by rfl⟩ : syracuseStep 2738987 = 4108481) B4108481
theorem B10529585 : Blo 1215425 10529585 := bstep (se 2 (by rfl) ⟨3948594, by rfl⟩ : syracuseStep 10529585 = 7897189) B7897189
theorem B3001175 : Blo 1215425 3001175 := bstep (se 1 (by rfl) ⟨2250881, by rfl⟩ : syracuseStep 3001175 = 4501763) B4501763
theorem B1461127 : Blo 1215425 1461127 := bstep (se 1 (by rfl) ⟨1095845, by rfl⟩ : syracuseStep 1461127 = 2191691) B2191691
theorem B6933383 : Blo 1215425 6933383 := bstep (se 1 (by rfl) ⟨5200037, by rfl⟩ : syracuseStep 6933383 = 10400075) B10400075
theorem B4680595 : Blo 1215425 4680595 := bstep (se 1 (by rfl) ⟨3510446, by rfl⟩ : syracuseStep 4680595 = 7020893) B7020893
theorem B2599865 : Blo 1215425 2599865 := bstep (se 2 (by rfl) ⟨974949, by rfl⟩ : syracuseStep 2599865 = 1949899) B1949899
theorem B1215495 : Blo 1215425 1215495 := bstep (se 1 (by rfl) ⟨911621, by rfl⟩ : syracuseStep 1215495 = 1823243) B1823243
theorem B1215503 : Blo 1215425 1215503 := bstep (se 1 (by rfl) ⟨911627, by rfl⟩ : syracuseStep 1215503 = 1823255) B1823255
theorem B2599951 : Blo 1215425 2599951 := bstep (se 1 (by rfl) ⟨1949963, by rfl⟩ : syracuseStep 2599951 = 3899927) B3899927
theorem B4107293 : Blo 1215425 4107293 := bstep (se 3 (by rfl) ⟨770117, by rfl⟩ : syracuseStep 4107293 = 1540235) B1540235
theorem B1215547 : Blo 1215425 1215547 := bstep (se 1 (by rfl) ⟨911660, by rfl⟩ : syracuseStep 1215547 = 1823321) B1823321
theorem B6155351 : Blo 1215425 6155351 := bstep (se 1 (by rfl) ⟨4616513, by rfl⟩ : syracuseStep 6155351 = 9233027) B9233027
theorem B1215623 : Blo 1215425 1215623 := bstep (se 1 (by rfl) ⟨911717, by rfl⟩ : syracuseStep 1215623 = 1823435) B1823435
theorem B1215631 : Blo 1215425 1215631 := bstep (se 1 (by rfl) ⟨911723, by rfl⟩ : syracuseStep 1215631 = 1823447) B1823447
theorem B2051257 : Blo 1215425 2051257 := bstep (se 2 (by rfl) ⟨769221, by rfl⟩ : syracuseStep 2051257 = 1538443) B1538443
theorem B1215675 : Blo 1215425 1215675 := bstep (se 1 (by rfl) ⟨911756, by rfl⟩ : syracuseStep 1215675 = 1823513) B1823513
theorem B1731785 : Blo 1215425 1731785 := bstep (se 2 (by rfl) ⟨649419, by rfl⟩ : syracuseStep 1731785 = 1298839) B1298839
theorem B1215751 : Blo 1215425 1215751 := bstep (se 1 (by rfl) ⟨911813, by rfl⟩ : syracuseStep 1215751 = 1823627) B1823627
theorem B1215759 : Blo 1215425 1215759 := bstep (se 1 (by rfl) ⟨911819, by rfl⟩ : syracuseStep 1215759 = 1823639) B1823639
theorem B1215803 : Blo 1215425 1215803 := bstep (se 1 (by rfl) ⟨911852, by rfl⟩ : syracuseStep 1215803 = 1823705) B1823705
theorem B1731899 : Blo 1215425 1731899 := bstep (se 1 (by rfl) ⟨1298924, by rfl⟩ : syracuseStep 1731899 = 2597849) B2597849
theorem B3288379 : Blo 1215425 3288379 := bstep (se 1 (by rfl) ⟨2466284, by rfl⟩ : syracuseStep 3288379 = 4932569) B4932569
theorem B1215879 : Blo 1215425 1215879 := bstep (se 1 (by rfl) ⟨911909, by rfl⟩ : syracuseStep 1215879 = 1823819) B1823819
theorem B1215887 : Blo 1215425 1215887 := bstep (se 1 (by rfl) ⟨911915, by rfl⟩ : syracuseStep 1215887 = 1823831) B1823831
theorem B1215931 : Blo 1215425 1215931 := bstep (se 1 (by rfl) ⟨911948, by rfl⟩ : syracuseStep 1215931 = 1823897) B1823897
theorem B1216007 : Blo 1215425 1216007 := bstep (se 1 (by rfl) ⟨912005, by rfl⟩ : syracuseStep 1216007 = 1824011) B1824011
theorem B1216015 : Blo 1215425 1216015 := bstep (se 1 (by rfl) ⟨912011, by rfl⟩ : syracuseStep 1216015 = 1824023) B1824023
theorem B1216059 : Blo 1215425 1216059 := bstep (se 1 (by rfl) ⟨912044, by rfl⟩ : syracuseStep 1216059 = 1824089) B1824089
theorem B6155837 : Blo 1215425 6155837 := bstep (se 3 (by rfl) ⟨1154219, by rfl⟩ : syracuseStep 6155837 = 2308439) B2308439
theorem B8326775 : Blo 1215425 8326775 := bstep (se 1 (by rfl) ⟨6245081, by rfl⟩ : syracuseStep 8326775 = 12490163) B12490163
theorem B1216135 : Blo 1215425 1216135 := bstep (se 1 (by rfl) ⟨912101, by rfl⟩ : syracuseStep 1216135 = 1824203) B1824203
theorem B1216143 : Blo 1215425 1216143 := bstep (se 1 (by rfl) ⟨912107, by rfl⟩ : syracuseStep 1216143 = 1824215) B1824215
theorem B1216187 : Blo 1215425 1216187 := bstep (se 1 (by rfl) ⟨912140, by rfl⟩ : syracuseStep 1216187 = 1824281) B1824281
theorem B4615937 : Blo 1215425 4615937 := bstep (se 2 (by rfl) ⟨1730976, by rfl⟩ : syracuseStep 4615937 = 3461953) B3461953
theorem B1216263 : Blo 1215425 1216263 := bstep (se 1 (by rfl) ⟨912197, by rfl⟩ : syracuseStep 1216263 = 1824395) B1824395
theorem B1216271 : Blo 1215425 1216271 := bstep (se 1 (by rfl) ⟨912203, by rfl⟩ : syracuseStep 1216271 = 1824407) B1824407
theorem B1216315 : Blo 1215425 1216315 := bstep (se 1 (by rfl) ⟨912236, by rfl⟩ : syracuseStep 1216315 = 1824473) B1824473
theorem B6246233 : Blo 1215425 6246233 := bstep (se 2 (by rfl) ⟨2342337, by rfl⟩ : syracuseStep 6246233 = 4684675) B4684675
theorem B2051959 : Blo 1215425 2051959 := bstep (se 1 (by rfl) ⟨1538969, by rfl⟩ : syracuseStep 2051959 = 3077939) B3077939
theorem B1216391 : Blo 1215425 1216391 := bstep (se 1 (by rfl) ⟨912293, by rfl⟩ : syracuseStep 1216391 = 1824587) B1824587
theorem B4386695 : Blo 1215425 4386695 := bstep (se 1 (by rfl) ⟨3290021, by rfl⟩ : syracuseStep 4386695 = 6580043) B6580043
theorem B1216399 : Blo 1215425 1216399 := bstep (se 1 (by rfl) ⟨912299, by rfl⟩ : syracuseStep 1216399 = 1824599) B1824599
theorem B5197715 : Blo 1215425 5197715 := bstep (se 1 (by rfl) ⟨3898286, by rfl⟩ : syracuseStep 5197715 = 7796573) B7796573
theorem B1732537 : Blo 1215425 1732537 := bstep (se 2 (by rfl) ⟨649701, by rfl⟩ : syracuseStep 1732537 = 1299403) B1299403
theorem B1216443 : Blo 1215425 1216443 := bstep (se 1 (by rfl) ⟨912332, by rfl⟩ : syracuseStep 1216443 = 1824665) B1824665
theorem B1216519 : Blo 1215425 1216519 := bstep (se 1 (by rfl) ⟨912389, by rfl⟩ : syracuseStep 1216519 = 1824779) B1824779
theorem B1216527 : Blo 1215425 1216527 := bstep (se 1 (by rfl) ⟨912395, by rfl⟩ : syracuseStep 1216527 = 1824791) B1824791
theorem B2052155 : Blo 1215425 2052155 := bstep (se 1 (by rfl) ⟨1539116, by rfl⟩ : syracuseStep 2052155 = 3078233) B3078233
theorem B1216571 : Blo 1215425 1216571 := bstep (se 1 (by rfl) ⟨912428, by rfl⟩ : syracuseStep 1216571 = 1824857) B1824857
theorem B6328381 : Blo 1215425 6328381 := bstep (se 3 (by rfl) ⟨1186571, by rfl⟩ : syracuseStep 6328381 = 2373143) B2373143
theorem B2773111 : Blo 1215425 2773111 := bstep (se 1 (by rfl) ⟨2079833, by rfl⟩ : syracuseStep 2773111 = 4159667) B4159667
theorem B1216647 : Blo 1215425 1216647 := bstep (se 1 (by rfl) ⟨912485, by rfl⟩ : syracuseStep 1216647 = 1824971) B1824971
theorem B1216655 : Blo 1215425 1216655 := bstep (se 1 (by rfl) ⟨912491, by rfl⟩ : syracuseStep 1216655 = 1824983) B1824983
theorem B1216699 : Blo 1215425 1216699 := bstep (se 1 (by rfl) ⟨912524, by rfl⟩ : syracuseStep 1216699 = 1825049) B1825049
theorem B6926593 : Blo 1215425 6926593 := bstep (se 2 (by rfl) ⟨2597472, by rfl⟩ : syracuseStep 6926593 = 5194945) B5194945
theorem B1216775 : Blo 1215425 1216775 := bstep (se 1 (by rfl) ⟨912581, by rfl⟩ : syracuseStep 1216775 = 1825163) B1825163
theorem B1216783 : Blo 1215425 1216783 := bstep (se 1 (by rfl) ⟨912587, by rfl⟩ : syracuseStep 1216783 = 1825175) B1825175
theorem B1216827 : Blo 1215425 1216827 := bstep (se 1 (by rfl) ⟨912620, by rfl⟩ : syracuseStep 1216827 = 1825241) B1825241
theorem B1216903 : Blo 1215425 1216903 := bstep (se 1 (by rfl) ⟨912677, by rfl⟩ : syracuseStep 1216903 = 1825355) B1825355
theorem B1216911 : Blo 1215425 1216911 := bstep (se 1 (by rfl) ⟨912683, by rfl⟩ : syracuseStep 1216911 = 1825367) B1825367
theorem B4108697 : Blo 1215425 4108697 := bstep (se 2 (by rfl) ⟨1540761, by rfl⟩ : syracuseStep 4108697 = 3081523) B3081523
theorem B1823147 : Blo 1215425 1823147 := bstep (se 1 (by rfl) ⟨1367360, by rfl⟩ : syracuseStep 1823147 = 2734721) B2734721
theorem B1216955 : Blo 1215425 1216955 := bstep (se 1 (by rfl) ⟨912716, by rfl⟩ : syracuseStep 1216955 = 1825433) B1825433
theorem B1823177 : Blo 1215425 1823177 := bstep (se 2 (by rfl) ⟨683691, by rfl⟩ : syracuseStep 1823177 = 1367383) B1367383
theorem B2052553 : Blo 1215425 2052553 := bstep (se 2 (by rfl) ⟨769707, by rfl⟩ : syracuseStep 2052553 = 1539415) B1539415
theorem B1217031 : Blo 1215425 1217031 := bstep (se 1 (by rfl) ⟨912773, by rfl⟩ : syracuseStep 1217031 = 1825547) B1825547
theorem B1217039 : Blo 1215425 1217039 := bstep (se 1 (by rfl) ⟨912779, by rfl⟩ : syracuseStep 1217039 = 1825559) B1825559
theorem B1823291 : Blo 1215425 1823291 := bstep (se 1 (by rfl) ⟨1367468, by rfl⟩ : syracuseStep 1823291 = 2734937) B2734937
theorem B1217083 : Blo 1215425 1217083 := bstep (se 1 (by rfl) ⟨912812, by rfl⟩ : syracuseStep 1217083 = 1825625) B1825625
theorem B1823351 : Blo 1215425 1823351 := bstep (se 1 (by rfl) ⟨1367513, by rfl⟩ : syracuseStep 1823351 = 2735027) B2735027
theorem B1217159 : Blo 1215425 1217159 := bstep (se 1 (by rfl) ⟨912869, by rfl⟩ : syracuseStep 1217159 = 1825739) B1825739
theorem B1823375 : Blo 1215425 1823375 := bstep (se 1 (by rfl) ⟨1367531, by rfl⟩ : syracuseStep 1823375 = 2735063) B2735063
theorem B1217167 : Blo 1215425 1217167 := bstep (se 1 (by rfl) ⟨912875, by rfl⟩ : syracuseStep 1217167 = 1825751) B1825751
theorem B1823417 : Blo 1215425 1823417 := bstep (se 2 (by rfl) ⟨683781, by rfl⟩ : syracuseStep 1823417 = 1367563) B1367563
theorem B1217211 : Blo 1215425 1217211 := bstep (se 1 (by rfl) ⟨912908, by rfl⟩ : syracuseStep 1217211 = 1825817) B1825817
theorem B1823495 : Blo 1215425 1823495 := bstep (se 1 (by rfl) ⟨1367621, by rfl⟩ : syracuseStep 1823495 = 2735243) B2735243
theorem B1217287 : Blo 1215425 1217287 := bstep (se 1 (by rfl) ⟨912965, by rfl⟩ : syracuseStep 1217287 = 1825931) B1825931
theorem B6927119 : Blo 1215425 6927119 := bstep (se 1 (by rfl) ⟨5195339, by rfl⟩ : syracuseStep 6927119 = 10390679) B10390679
theorem B1217295 : Blo 1215425 1217295 := bstep (se 1 (by rfl) ⟨912971, by rfl⟩ : syracuseStep 1217295 = 1825943) B1825943
theorem B1848107 : Blo 1215425 1848107 := bstep (se 1 (by rfl) ⟨1386080, by rfl⟩ : syracuseStep 1848107 = 2772161) B2772161
theorem B1823531 : Blo 1215425 1823531 := bstep (se 1 (by rfl) ⟨1367648, by rfl⟩ : syracuseStep 1823531 = 2735297) B2735297
theorem B1217339 : Blo 1215425 1217339 := bstep (se 1 (by rfl) ⟨913004, by rfl⟩ : syracuseStep 1217339 = 1826009) B1826009
theorem B1823561 : Blo 1215425 1823561 := bstep (se 2 (by rfl) ⟨683835, by rfl⟩ : syracuseStep 1823561 = 1367671) B1367671
theorem B4682611 : Blo 1215425 4682611 := bstep (se 1 (by rfl) ⟨3511958, by rfl⟩ : syracuseStep 4682611 = 7023917) B7023917
theorem B1217415 : Blo 1215425 1217415 := bstep (se 1 (by rfl) ⟨913061, by rfl⟩ : syracuseStep 1217415 = 1826123) B1826123
theorem B1217423 : Blo 1215425 1217423 := bstep (se 1 (by rfl) ⟨913067, by rfl⟩ : syracuseStep 1217423 = 1826135) B1826135
theorem B4617107 : Blo 1215425 4617107 := bstep (se 1 (by rfl) ⟨3462830, by rfl⟩ : syracuseStep 4617107 = 6925661) B6925661
theorem B9237401 : Blo 1215425 9237401 := bstep (se 2 (by rfl) ⟨3464025, by rfl⟩ : syracuseStep 9237401 = 6928051) B6928051
theorem B8328089 : Blo 1215425 8328089 := bstep (se 2 (by rfl) ⟨3123033, by rfl⟩ : syracuseStep 8328089 = 6246067) B6246067
theorem B1823675 : Blo 1215425 1823675 := bstep (se 1 (by rfl) ⟨1367756, by rfl⟩ : syracuseStep 1823675 = 2735513) B2735513
theorem B1823735 : Blo 1215425 1823735 := bstep (se 1 (by rfl) ⟨1367801, by rfl⟩ : syracuseStep 1823735 = 2735603) B2735603
theorem B1823759 : Blo 1215425 1823759 := bstep (se 1 (by rfl) ⟨1367819, by rfl⟩ : syracuseStep 1823759 = 2735639) B2735639
theorem B3896363 : Blo 1215425 3896363 := bstep (se 1 (by rfl) ⟨2922272, by rfl⟩ : syracuseStep 3896363 = 5844545) B5844545
theorem B1823801 : Blo 1215425 1823801 := bstep (se 2 (by rfl) ⟨683925, by rfl⟩ : syracuseStep 1823801 = 1367851) B1367851
theorem B3462203 : Blo 1215425 3462203 := bstep (se 1 (by rfl) ⟨2596652, by rfl⟩ : syracuseStep 3462203 = 5193305) B5193305
theorem B1823879 : Blo 1215425 1823879 := bstep (se 1 (by rfl) ⟨1367909, by rfl⟩ : syracuseStep 1823879 = 2735819) B2735819
theorem B2053255 : Blo 1215425 2053255 := bstep (se 1 (by rfl) ⟨1539941, by rfl⟩ : syracuseStep 2053255 = 3079883) B3079883
theorem B1823915 : Blo 1215425 1823915 := bstep (se 1 (by rfl) ⟨1367936, by rfl⟩ : syracuseStep 1823915 = 2735873) B2735873
theorem B14054573 : Blo 1215425 14054573 := bstep (se 3 (by rfl) ⟨2635232, by rfl⟩ : syracuseStep 14054573 = 5270465) B5270465
theorem B1823945 : Blo 1215425 1823945 := bstep (se 2 (by rfl) ⟨683979, by rfl⟩ : syracuseStep 1823945 = 1367959) B1367959
theorem B6157619 : Blo 1215425 6157619 := bstep (se 1 (by rfl) ⟨4618214, by rfl⟩ : syracuseStep 6157619 = 9236429) B9236429
theorem B1824059 : Blo 1215425 1824059 := bstep (se 1 (by rfl) ⟨1368044, by rfl⟩ : syracuseStep 1824059 = 2736089) B2736089
theorem B1824119 : Blo 1215425 1824119 := bstep (se 1 (by rfl) ⟨1368089, by rfl⟩ : syracuseStep 1824119 = 2736179) B2736179
theorem B4617607 : Blo 1215425 4617607 := bstep (se 1 (by rfl) ⟨3463205, by rfl⟩ : syracuseStep 4617607 = 6926411) B6926411
theorem B3896711 : Blo 1215425 3896711 := bstep (se 1 (by rfl) ⟨2922533, by rfl⟩ : syracuseStep 3896711 = 5845067) B5845067
theorem B1824143 : Blo 1215425 1824143 := bstep (se 1 (by rfl) ⟨1368107, by rfl⟩ : syracuseStep 1824143 = 2736215) B2736215
theorem B4928921 : Blo 1215425 4928921 := bstep (se 2 (by rfl) ⟨1848345, by rfl⟩ : syracuseStep 4928921 = 3696691) B3696691
theorem B1824185 : Blo 1215425 1824185 := bstep (se 2 (by rfl) ⟨684069, by rfl⟩ : syracuseStep 1824185 = 1368139) B1368139
theorem B17544707 : Blo 1215425 17544707 := bstep (se 1 (by rfl) ⟨13158530, by rfl⟩ : syracuseStep 17544707 = 26317061) B26317061
theorem B1824263 : Blo 1215425 1824263 := bstep (se 1 (by rfl) ⟨1368197, by rfl⟩ : syracuseStep 1824263 = 2736395) B2736395
theorem B5199389 : Blo 1215425 5199389 := bstep (se 3 (by rfl) ⟨974885, by rfl⟩ : syracuseStep 5199389 = 1949771) B1949771
theorem B1824299 : Blo 1215425 1824299 := bstep (se 1 (by rfl) ⟨1368224, by rfl⟩ : syracuseStep 1824299 = 2736449) B2736449
theorem B1824329 : Blo 1215425 1824329 := bstep (se 2 (by rfl) ⟨684123, by rfl⟩ : syracuseStep 1824329 = 1368247) B1368247
theorem B4159063 : Blo 1215425 4159063 := bstep (se 1 (by rfl) ⟨3119297, by rfl⟩ : syracuseStep 4159063 = 6238595) B6238595
theorem B3077747 : Blo 1215425 3077747 := bstep (se 1 (by rfl) ⟨2308310, by rfl⟩ : syracuseStep 3077747 = 4616621) B4616621
theorem B2307703 : Blo 1215425 2307703 := bstep (se 1 (by rfl) ⟨1730777, by rfl⟩ : syracuseStep 2307703 = 3461555) B3461555
theorem B6157943 : Blo 1215425 6157943 := bstep (se 1 (by rfl) ⟨4618457, by rfl⟩ : syracuseStep 6157943 = 9236915) B9236915
theorem B2774663 : Blo 1215425 2774663 := bstep (se 1 (by rfl) ⟨2080997, by rfl⟩ : syracuseStep 2774663 = 4161995) B4161995
theorem B3462841 : Blo 1215425 3462841 := bstep (se 2 (by rfl) ⟨1298565, by rfl⟩ : syracuseStep 3462841 = 2597131) B2597131
theorem B1824443 : Blo 1215425 1824443 := bstep (se 1 (by rfl) ⟨1368332, by rfl⟩ : syracuseStep 1824443 = 2736665) B2736665
theorem B1824503 : Blo 1215425 1824503 := bstep (se 1 (by rfl) ⟨1368377, by rfl⟩ : syracuseStep 1824503 = 2736755) B2736755
theorem B1824527 : Blo 1215425 1824527 := bstep (se 1 (by rfl) ⟨1368395, by rfl⟩ : syracuseStep 1824527 = 2736791) B2736791
theorem B2053903 : Blo 1215425 2053903 := bstep (se 1 (by rfl) ⟨1540427, by rfl⟩ : syracuseStep 2053903 = 3080855) B3080855
theorem B18716467 : Blo 1215425 18716467 := bstep (se 1 (by rfl) ⟨14037350, by rfl⟩ : syracuseStep 18716467 = 28074701) B28074701
theorem B1824569 : Blo 1215425 1824569 := bstep (se 2 (by rfl) ⟨684213, by rfl⟩ : syracuseStep 1824569 = 1368427) B1368427
theorem B47404865 : Blo 1215425 47404865 := bstep (se 2 (by rfl) ⟨17776824, by rfl⟩ : syracuseStep 47404865 = 35553649) B35553649
theorem B4159367 : Blo 1215425 4159367 := bstep (se 1 (by rfl) ⟨3119525, by rfl⟩ : syracuseStep 4159367 = 6239051) B6239051
theorem B1824647 : Blo 1215425 1824647 := bstep (se 1 (by rfl) ⟨1368485, by rfl⟩ : syracuseStep 1824647 = 2736971) B2736971
theorem B1824683 : Blo 1215425 1824683 := bstep (se 1 (by rfl) ⟨1368512, by rfl⟩ : syracuseStep 1824683 = 2737025) B2737025
theorem B1824713 : Blo 1215425 1824713 := bstep (se 2 (by rfl) ⟨684267, by rfl⟩ : syracuseStep 1824713 = 1368535) B1368535
theorem B5847005 : Blo 1215425 5847005 := bstep (se 3 (by rfl) ⟨1096313, by rfl⟩ : syracuseStep 5847005 = 2192627) B2192627
theorem B2775073 : Blo 1215425 2775073 := bstep (se 2 (by rfl) ⟨1040652, by rfl⟩ : syracuseStep 2775073 = 2081305) B2081305
theorem B1824827 : Blo 1215425 1824827 := bstep (se 1 (by rfl) ⟨1368620, by rfl⟩ : syracuseStep 1824827 = 2737241) B2737241
theorem B3463229 : Blo 1215425 3463229 := bstep (se 3 (by rfl) ⟨649355, by rfl⟩ : syracuseStep 3463229 = 1298711) B1298711
theorem B3119219 : Blo 1215425 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B3078263 : Blo 1215425 3078263 := bstep (se 1 (by rfl) ⟨2308697, by rfl⟩ : syracuseStep 3078263 = 4617395) B4617395
theorem B1824887 : Blo 1215425 1824887 := bstep (se 1 (by rfl) ⟨1368665, by rfl⟩ : syracuseStep 1824887 = 2737331) B2737331
theorem B1824911 : Blo 1215425 1824911 := bstep (se 1 (by rfl) ⟨1368683, by rfl⟩ : syracuseStep 1824911 = 2737367) B2737367
theorem B1824953 : Blo 1215425 1824953 := bstep (se 2 (by rfl) ⟨684357, by rfl⟩ : syracuseStep 1824953 = 1368715) B1368715
theorem B6928577 : Blo 1215425 6928577 := bstep (se 2 (by rfl) ⟨2598216, by rfl⟩ : syracuseStep 6928577 = 5196433) B5196433
theorem B1825031 : Blo 1215425 1825031 := bstep (se 1 (by rfl) ⟨1368773, by rfl⟩ : syracuseStep 1825031 = 2737547) B2737547
theorem B4102433 : Blo 1215425 4102433 := bstep (se 2 (by rfl) ⟨1538412, by rfl⟩ : syracuseStep 4102433 = 3076825) B3076825
theorem B1538347 : Blo 1215425 1538347 := bstep (se 1 (by rfl) ⟨1153760, by rfl⟩ : syracuseStep 1538347 = 2307521) B2307521
theorem B1825067 : Blo 1215425 1825067 := bstep (se 1 (by rfl) ⟨1368800, by rfl⟩ : syracuseStep 1825067 = 2737601) B2737601
theorem B5544251 : Blo 1215425 5544251 := bstep (se 1 (by rfl) ⟨4158188, by rfl⟩ : syracuseStep 5544251 = 8316377) B8316377
theorem B1825097 : Blo 1215425 1825097 := bstep (se 2 (by rfl) ⟨684411, by rfl⟩ : syracuseStep 1825097 = 1368823) B1368823
theorem B10393991 : Blo 1215425 10393991 := bstep (se 1 (by rfl) ⟨7795493, by rfl⟩ : syracuseStep 10393991 = 15590987) B15590987
theorem B1825211 : Blo 1215425 1825211 := bstep (se 1 (by rfl) ⟨1368908, by rfl⟩ : syracuseStep 1825211 = 2737817) B2737817
theorem B1825271 : Blo 1215425 1825271 := bstep (se 1 (by rfl) ⟨1368953, by rfl⟩ : syracuseStep 1825271 = 2737907) B2737907
theorem B1825295 : Blo 1215425 1825295 := bstep (se 1 (by rfl) ⟨1368971, by rfl⟩ : syracuseStep 1825295 = 2737943) B2737943
theorem B1825337 : Blo 1215425 1825337 := bstep (se 2 (by rfl) ⟨684501, by rfl⟩ : syracuseStep 1825337 = 1369003) B1369003
theorem B2775611 : Blo 1215425 2775611 := bstep (se 1 (by rfl) ⟨2081708, by rfl⟩ : syracuseStep 2775611 = 4163417) B4163417
theorem B6158915 : Blo 1215425 6158915 := bstep (se 1 (by rfl) ⟨4619186, by rfl⟩ : syracuseStep 6158915 = 9238373) B9238373
theorem B1825415 : Blo 1215425 1825415 := bstep (se 1 (by rfl) ⟨1369061, by rfl⟩ : syracuseStep 1825415 = 2738123) B2738123
theorem B2734739 : Blo 1215425 2734739 := bstep (se 1 (by rfl) ⟨2051054, by rfl⟩ : syracuseStep 2734739 = 4102109) B4102109
theorem B1825451 : Blo 1215425 1825451 := bstep (se 1 (by rfl) ⟨1369088, by rfl⟩ : syracuseStep 1825451 = 2738177) B2738177
theorem B2734793 : Blo 1215425 2734793 := bstep (se 2 (by rfl) ⟨1025547, by rfl⟩ : syracuseStep 2734793 = 2051095) B2051095
theorem B1825481 : Blo 1215425 1825481 := bstep (se 2 (by rfl) ⟨684555, by rfl⟩ : syracuseStep 1825481 = 1369111) B1369111
theorem B3898145 : Blo 1215425 3898145 := bstep (se 2 (by rfl) ⟨1461804, by rfl⟩ : syracuseStep 3898145 = 2923609) B2923609
theorem B16644899 : Blo 1215425 16644899 := bstep (se 1 (by rfl) ⟨12483674, by rfl⟩ : syracuseStep 16644899 = 24967349) B24967349
theorem B9239345 : Blo 1215425 9239345 := bstep (se 2 (by rfl) ⟨3464754, by rfl⟩ : syracuseStep 9239345 = 6929509) B6929509
theorem B1825595 : Blo 1215425 1825595 := bstep (se 1 (by rfl) ⟨1369196, by rfl⟩ : syracuseStep 1825595 = 2738393) B2738393
theorem B4103027 : Blo 1215425 4103027 := bstep (se 1 (by rfl) ⟨3077270, by rfl⟩ : syracuseStep 4103027 = 6154541) B6154541
theorem B8772467 : Blo 1215425 8772467 := bstep (se 1 (by rfl) ⟨6579350, by rfl⟩ : syracuseStep 8772467 = 13158701) B13158701
theorem B1825655 : Blo 1215425 1825655 := bstep (se 1 (by rfl) ⟨1369241, by rfl⟩ : syracuseStep 1825655 = 2738483) B2738483
theorem B6159239 : Blo 1215425 6159239 := bstep (se 1 (by rfl) ⟨4619429, by rfl⟩ : syracuseStep 6159239 = 9238859) B9238859
theorem B1825679 : Blo 1215425 1825679 := bstep (se 1 (by rfl) ⟨1369259, by rfl⟩ : syracuseStep 1825679 = 2738519) B2738519
theorem B13859747 : Blo 1215425 13859747 := bstep (se 1 (by rfl) ⟨10394810, by rfl⟩ : syracuseStep 13859747 = 20789621) B20789621
theorem B1850297 : Blo 1215425 1850297 := bstep (se 2 (by rfl) ⟨693861, by rfl⟩ : syracuseStep 1850297 = 1387723) B1387723
theorem B1825721 : Blo 1215425 1825721 := bstep (se 2 (by rfl) ⟨684645, by rfl⟩ : syracuseStep 1825721 = 1369291) B1369291
theorem B2923465 : Blo 1215425 2923465 := bstep (se 2 (by rfl) ⟨1096299, by rfl⟩ : syracuseStep 2923465 = 2192599) B2192599
theorem B5192657 : Blo 1215425 5192657 := bstep (se 2 (by rfl) ⟨1947246, by rfl⟩ : syracuseStep 5192657 = 3894493) B3894493
theorem B1825799 : Blo 1215425 1825799 := bstep (se 1 (by rfl) ⟨1369349, by rfl⟩ : syracuseStep 1825799 = 2738699) B2738699
theorem B6241303 : Blo 1215425 6241303 := bstep (se 1 (by rfl) ⟨4680977, by rfl⟩ : syracuseStep 6241303 = 9361955) B9361955
theorem B1825835 : Blo 1215425 1825835 := bstep (se 1 (by rfl) ⟨1369376, by rfl⟩ : syracuseStep 1825835 = 2738753) B2738753
theorem B1825865 : Blo 1215425 1825865 := bstep (se 2 (by rfl) ⟨684699, by rfl⟩ : syracuseStep 1825865 = 1369399) B1369399
theorem B4996183 : Blo 1215425 4996183 := bstep (se 1 (by rfl) ⟨3747137, by rfl⟩ : syracuseStep 4996183 = 7494275) B7494275
theorem B3079255 : Blo 1215425 3079255 := bstep (se 1 (by rfl) ⟨2309441, by rfl⟩ : syracuseStep 3079255 = 4618883) B4618883
theorem B3464345 : Blo 1215425 3464345 := bstep (se 2 (by rfl) ⟨1299129, by rfl⟩ : syracuseStep 3464345 = 2598259) B2598259
theorem B2309305 : Blo 1215425 2309305 := bstep (se 2 (by rfl) ⟨865989, by rfl⟩ : syracuseStep 2309305 = 1731979) B1731979
theorem B1825979 : Blo 1215425 1825979 := bstep (se 1 (by rfl) ⟨1369484, by rfl⟩ : syracuseStep 1825979 = 2738969) B2738969
theorem B1539319 : Blo 1215425 1539319 := bstep (se 1 (by rfl) ⟨1154489, by rfl⟩ : syracuseStep 1539319 = 2308979) B2308979
theorem B1826039 : Blo 1215425 1826039 := bstep (se 1 (by rfl) ⟨1369529, by rfl⟩ : syracuseStep 1826039 = 2739059) B2739059
theorem B1826063 : Blo 1215425 1826063 := bstep (se 1 (by rfl) ⟨1369547, by rfl⟩ : syracuseStep 1826063 = 2739095) B2739095
theorem B1826105 : Blo 1215425 1826105 := bstep (se 2 (by rfl) ⟨684789, by rfl⟩ : syracuseStep 1826105 = 1369579) B1369579
theorem B2735495 : Blo 1215425 2735495 := bstep (se 1 (by rfl) ⟨2051621, by rfl⟩ : syracuseStep 2735495 = 4103243) B4103243
theorem B3079559 : Blo 1215425 3079559 := bstep (se 1 (by rfl) ⟨2309669, by rfl⟩ : syracuseStep 3079559 = 4619339) B4619339
theorem B12475793 : Blo 1215425 12475793 := bstep (se 2 (by rfl) ⟨4678422, by rfl⟩ : syracuseStep 12475793 = 9356845) B9356845
theorem B7396811 : Blo 1215425 7396811 := bstep (se 1 (by rfl) ⟨5547608, by rfl⟩ : syracuseStep 7396811 = 11095217) B11095217
theorem B3079691 : Blo 1215425 3079691 := bstep (se 1 (by rfl) ⟨2309768, by rfl⟩ : syracuseStep 3079691 = 4619537) B4619537
theorem B2309647 : Blo 1215425 2309647 := bstep (se 1 (by rfl) ⟨1732235, by rfl⟩ : syracuseStep 2309647 = 3464471) B3464471
theorem B2735675 : Blo 1215425 2735675 := bstep (se 1 (by rfl) ⟨2051756, by rfl⟩ : syracuseStep 2735675 = 4103513) B4103513
theorem B1539643 : Blo 1215425 1539643 := bstep (se 1 (by rfl) ⟨1154732, by rfl⟩ : syracuseStep 1539643 = 2309465) B2309465
theorem B6323779 : Blo 1215425 6323779 := bstep (se 1 (by rfl) ⟨4742834, by rfl⟩ : syracuseStep 6323779 = 9485669) B9485669
theorem B14786225 : Blo 1215425 14786225 := bstep (se 2 (by rfl) ⟨5544834, by rfl⟩ : syracuseStep 14786225 = 11089669) B11089669
theorem B2735801 : Blo 1215425 2735801 := bstep (se 2 (by rfl) ⟨1025925, by rfl⟩ : syracuseStep 2735801 = 2051851) B2051851
theorem B1367815 : Blo 1215425 1367815 := bstep (se 1 (by rfl) ⟨1025861, by rfl⟩ : syracuseStep 1367815 = 2051723) B2051723
theorem B6668065 : Blo 1215425 6668065 := bstep (se 2 (by rfl) ⟨2500524, by rfl⟩ : syracuseStep 6668065 = 5001049) B5001049
theorem B1949483 : Blo 1215425 1949483 := bstep (se 1 (by rfl) ⟨1462112, by rfl⟩ : syracuseStep 1949483 = 2924225) B2924225
theorem B4997011 : Blo 1215425 4997011 := bstep (se 1 (by rfl) ⟨3747758, by rfl⟩ : syracuseStep 4997011 = 7495517) B7495517
theorem B1367995 : Blo 1215425 1367995 := bstep (se 1 (by rfl) ⟨1025996, by rfl⟩ : syracuseStep 1367995 = 2051993) B2051993
theorem B1368103 : Blo 1215425 1368103 := bstep (se 1 (by rfl) ⟨1026077, by rfl⟩ : syracuseStep 1368103 = 2052155) B2052155
theorem B8437841 : Blo 1215425 8437841 := bstep (se 2 (by rfl) ⟨3164190, by rfl⟩ : syracuseStep 8437841 = 6328381) B6328381
theorem B9232541 : Blo 1215425 9232541 := bstep (se 3 (by rfl) ⟨1731101, by rfl⟩ : syracuseStep 9232541 = 3462203) B3462203
theorem B37478861 : Blo 1215425 37478861 := bstep (se 3 (by rfl) ⟨7027286, by rfl⟩ : syracuseStep 37478861 = 14054573) B14054573
theorem B2310619 : Blo 1215425 2310619 := bstep (se 1 (by rfl) ⟨1732964, by rfl⟩ : syracuseStep 2310619 = 3465929) B3465929
theorem B3080713 : Blo 1215425 3080713 := bstep (se 2 (by rfl) ⟨1155267, by rfl⟩ : syracuseStep 3080713 = 2310535) B2310535
theorem B2736737 : Blo 1215425 2736737 := bstep (se 2 (by rfl) ⟨1026276, by rfl⟩ : syracuseStep 2736737 = 2052553) B2052553
theorem B9241289 : Blo 1215425 9241289 := bstep (se 2 (by rfl) ⟨3465483, by rfl⟩ : syracuseStep 9241289 = 6930967) B6930967
theorem B4621009 : Blo 1215425 4621009 := bstep (se 2 (by rfl) ⟨1732878, by rfl⟩ : syracuseStep 4621009 = 3465757) B3465757
theorem B4105079 : Blo 1215425 4105079 := bstep (se 1 (by rfl) ⟨3078809, by rfl⟩ : syracuseStep 4105079 = 6157619) B6157619
theorem B3466145 : Blo 1215425 3466145 := bstep (se 2 (by rfl) ⟨1299804, by rfl⟩ : syracuseStep 3466145 = 2599609) B2599609
theorem B2597807 : Blo 1215425 2597807 := bstep (se 1 (by rfl) ⟨1948355, by rfl⟩ : syracuseStep 2597807 = 3896711) B3896711
theorem B2737079 : Blo 1215425 2737079 := bstep (se 1 (by rfl) ⟨2052809, by rfl⟩ : syracuseStep 2737079 = 4105619) B4105619
theorem B3285947 : Blo 1215425 3285947 := bstep (se 1 (by rfl) ⟨2464460, by rfl⟩ : syracuseStep 3285947 = 4928921) B4928921
theorem B4621313 : Blo 1215425 4621313 := bstep (se 2 (by rfl) ⟨1732992, by rfl⟩ : syracuseStep 4621313 = 3465985) B3465985
theorem B3466259 : Blo 1215425 3466259 := bstep (se 1 (by rfl) ⟨2599694, by rfl⟩ : syracuseStep 3466259 = 5199389) B5199389
theorem B33268781 : Blo 1215425 33268781 := bstep (se 3 (by rfl) ⟨6237896, by rfl⟩ : syracuseStep 33268781 = 12475793) B12475793
theorem B4105295 : Blo 1215425 4105295 := bstep (se 1 (by rfl) ⟨3078971, by rfl⟩ : syracuseStep 4105295 = 6157943) B6157943
theorem B6243481 : Blo 1215425 6243481 := bstep (se 2 (by rfl) ⟨2341305, by rfl⟩ : syracuseStep 6243481 = 4682611) B4682611
theorem B3466601 : Blo 1215425 3466601 := bstep (se 2 (by rfl) ⟨1299975, by rfl⟩ : syracuseStep 3466601 = 2599951) B2599951
theorem B2082235 : Blo 1215425 2082235 := bstep (se 1 (by rfl) ⟨1561676, by rfl⟩ : syracuseStep 2082235 = 3123353) B3123353
theorem B6661577 : Blo 1215425 6661577 := bstep (se 2 (by rfl) ⟨2498091, by rfl⟩ : syracuseStep 6661577 = 4996183) B4996183
theorem B4105673 : Blo 1215425 4105673 := bstep (se 2 (by rfl) ⟨1539627, by rfl⟩ : syracuseStep 4105673 = 3079255) B3079255
theorem B4621769 : Blo 1215425 4621769 := bstep (se 2 (by rfl) ⟨1733163, by rfl⟩ : syracuseStep 4621769 = 3466327) B3466327
theorem B35563013 : Blo 1215425 35563013 := bstep (se 4 (by rfl) ⟨3334032, by rfl⟩ : syracuseStep 35563013 = 6668065) B6668065
theorem B2737673 : Blo 1215425 2737673 := bstep (se 2 (by rfl) ⟨1026627, by rfl⟩ : syracuseStep 2737673 = 2053255) B2053255
theorem B3696167 : Blo 1215425 3696167 := bstep (se 1 (by rfl) ⟨2772125, by rfl⟩ : syracuseStep 3696167 = 5544251) B5544251
theorem B4105943 : Blo 1215425 4105943 := bstep (se 1 (by rfl) ⟨3079457, by rfl⟩ : syracuseStep 4105943 = 6158915) B6158915
theorem B4384505 : Blo 1215425 4384505 := bstep (se 2 (by rfl) ⟨1644189, by rfl⟩ : syracuseStep 4384505 = 3288379) B3288379
theorem B10389343 : Blo 1215425 10389343 := bstep (se 1 (by rfl) ⟨7792007, by rfl⟩ : syracuseStep 10389343 = 15584015) B15584015
theorem B2738015 : Blo 1215425 2738015 := bstep (se 1 (by rfl) ⟨2053511, by rfl⟩ : syracuseStep 2738015 = 4107023) B4107023
theorem B2000783 : Blo 1215425 2000783 := bstep (se 1 (by rfl) ⟨1500587, by rfl⟩ : syracuseStep 2000783 = 3001175) B3001175
theorem B4106159 : Blo 1215425 4106159 := bstep (se 1 (by rfl) ⟨3079619, by rfl⟩ : syracuseStep 4106159 = 6159239) B6159239
theorem B4622255 : Blo 1215425 4622255 := bstep (se 1 (by rfl) ⟨3466691, by rfl⟩ : syracuseStep 4622255 = 6933383) B6933383
theorem B2738195 : Blo 1215425 2738195 := bstep (se 1 (by rfl) ⟨2053646, by rfl⟩ : syracuseStep 2738195 = 4107293) B4107293
theorem B8431705 : Blo 1215425 8431705 := bstep (se 2 (by rfl) ⟨3161889, by rfl⟩ : syracuseStep 8431705 = 6323779) B6323779
theorem B126412973 : Blo 1215425 126412973 := bstep (se 3 (by rfl) ⟨23702432, by rfl⟩ : syracuseStep 126412973 = 47404865) B47404865
theorem B2738537 : Blo 1215425 2738537 := bstep (se 2 (by rfl) ⟨1026951, by rfl⟩ : syracuseStep 2738537 = 2053903) B2053903
theorem B24955289 : Blo 1215425 24955289 := bstep (se 2 (by rfl) ⟨9358233, by rfl⟩ : syracuseStep 24955289 = 18716467) B18716467
theorem B9857483 : Blo 1215425 9857483 := bstep (se 1 (by rfl) ⟨7393112, by rfl⟩ : syracuseStep 9857483 = 14786225) B14786225
theorem B4934125 : Blo 1215425 4934125 := bstep (se 3 (by rfl) ⟨925148, by rfl⟩ : syracuseStep 4934125 = 1850297) B1850297
theorem B6662681 : Blo 1215425 6662681 := bstep (se 2 (by rfl) ⟨2498505, by rfl⟩ : syracuseStep 6662681 = 4997011) B4997011
theorem B4164155 : Blo 1215425 4164155 := bstep (se 1 (by rfl) ⟨3123116, by rfl⟩ : syracuseStep 4164155 = 6246233) B6246233
theorem B15592013 : Blo 1215425 15592013 := bstep (se 3 (by rfl) ⟨2923502, by rfl⟩ : syracuseStep 15592013 = 5847005) B5847005
theorem B10390301 : Blo 1215425 10390301 := bstep (se 3 (by rfl) ⟨1948181, by rfl⟩ : syracuseStep 10390301 = 3896363) B3896363
theorem B31591205 : Blo 1215425 31591205 := bstep (se 4 (by rfl) ⟨2961675, by rfl⟩ : syracuseStep 31591205 = 5923351) B5923351
theorem B3697481 : Blo 1215425 3697481 := bstep (se 2 (by rfl) ⟨1386555, by rfl⟩ : syracuseStep 3697481 = 2773111) B2773111
theorem B2739131 : Blo 1215425 2739131 := bstep (se 1 (by rfl) ⟨2054348, by rfl⟩ : syracuseStep 2739131 = 4108697) B4108697
theorem B1215431 : Blo 1215425 1215431 := bstep (se 1 (by rfl) ⟨911573, by rfl⟩ : syracuseStep 1215431 = 1823147) B1823147
theorem B1215451 : Blo 1215425 1215451 := bstep (se 1 (by rfl) ⟨911588, by rfl⟩ : syracuseStep 1215451 = 1823177) B1823177
theorem B9235457 : Blo 1215425 9235457 := bstep (se 2 (by rfl) ⟨3463296, by rfl⟩ : syracuseStep 9235457 = 6926593) B6926593
theorem B1215527 : Blo 1215425 1215527 := bstep (se 1 (by rfl) ⟨911645, by rfl⟩ : syracuseStep 1215527 = 1823291) B1823291
theorem B2051129 : Blo 1215425 2051129 := bstep (se 2 (by rfl) ⟨769173, by rfl⟩ : syracuseStep 2051129 = 1538347) B1538347
theorem B1215567 : Blo 1215425 1215567 := bstep (se 1 (by rfl) ⟨911675, by rfl⟩ : syracuseStep 1215567 = 1823351) B1823351
theorem B16657487 : Blo 1215425 16657487 := bstep (se 1 (by rfl) ⟨12493115, by rfl⟩ : syracuseStep 16657487 = 24986231) B24986231
theorem B1215583 : Blo 1215425 1215583 := bstep (se 1 (by rfl) ⟨911687, by rfl⟩ : syracuseStep 1215583 = 1823375) B1823375
theorem B1215611 : Blo 1215425 1215611 := bstep (se 1 (by rfl) ⟨911708, by rfl⟩ : syracuseStep 1215611 = 1823417) B1823417
theorem B4336811 : Blo 1215425 4336811 := bstep (se 1 (by rfl) ⟨3252608, by rfl⟩ : syracuseStep 4336811 = 6505217) B6505217
theorem B1215663 : Blo 1215425 1215663 := bstep (se 1 (by rfl) ⟨911747, by rfl⟩ : syracuseStep 1215663 = 1823495) B1823495
theorem B1215687 : Blo 1215425 1215687 := bstep (se 1 (by rfl) ⟨911765, by rfl⟩ : syracuseStep 1215687 = 1823531) B1823531
theorem B1215707 : Blo 1215425 1215707 := bstep (se 1 (by rfl) ⟨911780, by rfl⟩ : syracuseStep 1215707 = 1823561) B1823561
theorem B1215783 : Blo 1215425 1215783 := bstep (se 1 (by rfl) ⟨911837, by rfl⟩ : syracuseStep 1215783 = 1823675) B1823675
theorem B1215823 : Blo 1215425 1215823 := bstep (se 1 (by rfl) ⟨911867, by rfl⟩ : syracuseStep 1215823 = 1823735) B1823735
theorem B1215839 : Blo 1215425 1215839 := bstep (se 1 (by rfl) ⟨911879, by rfl⟩ : syracuseStep 1215839 = 1823759) B1823759
theorem B1215867 : Blo 1215425 1215867 := bstep (se 1 (by rfl) ⟨911900, by rfl⟩ : syracuseStep 1215867 = 1823801) B1823801
theorem B1215919 : Blo 1215425 1215919 := bstep (se 1 (by rfl) ⟨911939, by rfl⟩ : syracuseStep 1215919 = 1823879) B1823879
theorem B1215943 : Blo 1215425 1215943 := bstep (se 1 (by rfl) ⟨911957, by rfl⟩ : syracuseStep 1215943 = 1823915) B1823915
theorem B1215963 : Blo 1215425 1215963 := bstep (se 1 (by rfl) ⟨911972, by rfl⟩ : syracuseStep 1215963 = 1823945) B1823945
theorem B1216039 : Blo 1215425 1216039 := bstep (se 1 (by rfl) ⟨912029, by rfl⟩ : syracuseStep 1216039 = 1824059) B1824059
theorem B1216079 : Blo 1215425 1216079 := bstep (se 1 (by rfl) ⟨912059, by rfl⟩ : syracuseStep 1216079 = 1824119) B1824119
theorem B9858647 : Blo 1215425 9858647 := bstep (se 1 (by rfl) ⟨7393985, by rfl⟩ : syracuseStep 9858647 = 14787971) B14787971
theorem B1216095 : Blo 1215425 1216095 := bstep (se 1 (by rfl) ⟨912071, by rfl⟩ : syracuseStep 1216095 = 1824143) B1824143
theorem B1216123 : Blo 1215425 1216123 := bstep (se 1 (by rfl) ⟨912092, by rfl⟩ : syracuseStep 1216123 = 1824185) B1824185
theorem B1216175 : Blo 1215425 1216175 := bstep (se 1 (by rfl) ⟨912131, by rfl⟩ : syracuseStep 1216175 = 1824263) B1824263
theorem B1216199 : Blo 1215425 1216199 := bstep (se 1 (by rfl) ⟨912149, by rfl⟩ : syracuseStep 1216199 = 1824299) B1824299
theorem B1216219 : Blo 1215425 1216219 := bstep (se 1 (by rfl) ⟨912164, by rfl⟩ : syracuseStep 1216219 = 1824329) B1824329
theorem B2051831 : Blo 1215425 2051831 := bstep (se 1 (by rfl) ⟨1538873, by rfl⟩ : syracuseStep 2051831 = 3077747) B3077747
theorem B1216295 : Blo 1215425 1216295 := bstep (se 1 (by rfl) ⟨912221, by rfl⟩ : syracuseStep 1216295 = 1824443) B1824443
theorem B6238019 : Blo 1215425 6238019 := bstep (se 1 (by rfl) ⟨4678514, by rfl⟩ : syracuseStep 6238019 = 9357029) B9357029
theorem B1216335 : Blo 1215425 1216335 := bstep (se 1 (by rfl) ⟨912251, by rfl⟩ : syracuseStep 1216335 = 1824503) B1824503
theorem B1216351 : Blo 1215425 1216351 := bstep (se 1 (by rfl) ⟨912263, by rfl⟩ : syracuseStep 1216351 = 1824527) B1824527
theorem B1216379 : Blo 1215425 1216379 := bstep (se 1 (by rfl) ⟨912284, by rfl⟩ : syracuseStep 1216379 = 1824569) B1824569
theorem B13152131 : Blo 1215425 13152131 := bstep (se 1 (by rfl) ⟨9864098, by rfl⟩ : syracuseStep 13152131 = 19728197) B19728197
theorem B2772911 : Blo 1215425 2772911 := bstep (se 1 (by rfl) ⟨2079683, by rfl⟩ : syracuseStep 2772911 = 4159367) B4159367
theorem B1216431 : Blo 1215425 1216431 := bstep (se 1 (by rfl) ⟨912323, by rfl⟩ : syracuseStep 1216431 = 1824647) B1824647
theorem B1216455 : Blo 1215425 1216455 := bstep (se 1 (by rfl) ⟨912341, by rfl⟩ : syracuseStep 1216455 = 1824683) B1824683
theorem B1216475 : Blo 1215425 1216475 := bstep (se 1 (by rfl) ⟨912356, by rfl⟩ : syracuseStep 1216475 = 1824713) B1824713
theorem B1216551 : Blo 1215425 1216551 := bstep (se 1 (by rfl) ⟨912413, by rfl⟩ : syracuseStep 1216551 = 1824827) B1824827
theorem B2052175 : Blo 1215425 2052175 := bstep (se 1 (by rfl) ⟨1539131, by rfl⟩ : syracuseStep 2052175 = 3078263) B3078263
theorem B1216591 : Blo 1215425 1216591 := bstep (se 1 (by rfl) ⟨912443, by rfl⟩ : syracuseStep 1216591 = 1824887) B1824887
theorem B1216607 : Blo 1215425 1216607 := bstep (se 1 (by rfl) ⟨912455, by rfl⟩ : syracuseStep 1216607 = 1824911) B1824911
theorem B1216635 : Blo 1215425 1216635 := bstep (se 1 (by rfl) ⟨912476, by rfl⟩ : syracuseStep 1216635 = 1824953) B1824953
theorem B1216687 : Blo 1215425 1216687 := bstep (se 1 (by rfl) ⟨912515, by rfl⟩ : syracuseStep 1216687 = 1825031) B1825031
theorem B1216711 : Blo 1215425 1216711 := bstep (se 1 (by rfl) ⟨912533, by rfl⟩ : syracuseStep 1216711 = 1825067) B1825067
theorem B1216731 : Blo 1215425 1216731 := bstep (se 1 (by rfl) ⟨912548, by rfl⟩ : syracuseStep 1216731 = 1825097) B1825097
theorem B3895543 : Blo 1215425 3895543 := bstep (se 1 (by rfl) ⟨2921657, by rfl⟩ : syracuseStep 3895543 = 5843315) B5843315
theorem B4108535 : Blo 1215425 4108535 := bstep (se 1 (by rfl) ⟨3081401, by rfl⟩ : syracuseStep 4108535 = 6162803) B6162803
theorem B8761601 : Blo 1215425 8761601 := bstep (se 2 (by rfl) ⟨3285600, by rfl⟩ : syracuseStep 8761601 = 6571201) B6571201
theorem B1216807 : Blo 1215425 1216807 := bstep (se 1 (by rfl) ⟨912605, by rfl⟩ : syracuseStep 1216807 = 1825211) B1825211
theorem B2052425 : Blo 1215425 2052425 := bstep (se 2 (by rfl) ⟨769659, by rfl⟩ : syracuseStep 2052425 = 1539319) B1539319
theorem B1216847 : Blo 1215425 1216847 := bstep (se 1 (by rfl) ⟨912635, by rfl⟩ : syracuseStep 1216847 = 1825271) B1825271
theorem B1216863 : Blo 1215425 1216863 := bstep (se 1 (by rfl) ⟨912647, by rfl⟩ : syracuseStep 1216863 = 1825295) B1825295
theorem B1216891 : Blo 1215425 1216891 := bstep (se 1 (by rfl) ⟨912668, by rfl⟩ : syracuseStep 1216891 = 1825337) B1825337
theorem B1216943 : Blo 1215425 1216943 := bstep (se 1 (by rfl) ⟨912707, by rfl⟩ : syracuseStep 1216943 = 1825415) B1825415
theorem B1823159 : Blo 1215425 1823159 := bstep (se 1 (by rfl) ⟨1367369, by rfl⟩ : syracuseStep 1823159 = 2734739) B2734739
theorem B1216967 : Blo 1215425 1216967 := bstep (se 1 (by rfl) ⟨912725, by rfl⟩ : syracuseStep 1216967 = 1825451) B1825451
theorem B1823195 : Blo 1215425 1823195 := bstep (se 1 (by rfl) ⟨1367396, by rfl⟩ : syracuseStep 1823195 = 2734793) B2734793
theorem B1216987 : Blo 1215425 1216987 := bstep (se 1 (by rfl) ⟨912740, by rfl⟩ : syracuseStep 1216987 = 1825481) B1825481
theorem B6156809 : Blo 1215425 6156809 := bstep (se 2 (by rfl) ⟨2308803, by rfl⟩ : syracuseStep 6156809 = 4617607) B4617607
theorem B11096599 : Blo 1215425 11096599 := bstep (se 1 (by rfl) ⟨8322449, by rfl⟩ : syracuseStep 11096599 = 16644899) B16644899
theorem B1217063 : Blo 1215425 1217063 := bstep (se 1 (by rfl) ⟨912797, by rfl⟩ : syracuseStep 1217063 = 1825595) B1825595
theorem B1217103 : Blo 1215425 1217103 := bstep (se 1 (by rfl) ⟨912827, by rfl⟩ : syracuseStep 1217103 = 1825655) B1825655
theorem B1217119 : Blo 1215425 1217119 := bstep (se 1 (by rfl) ⟨912839, by rfl⟩ : syracuseStep 1217119 = 1825679) B1825679
theorem B1217147 : Blo 1215425 1217147 := bstep (se 1 (by rfl) ⟨912860, by rfl⟩ : syracuseStep 1217147 = 1825721) B1825721
theorem B1733243 : Blo 1215425 1733243 := bstep (se 1 (by rfl) ⟨1299932, by rfl⟩ : syracuseStep 1733243 = 2599865) B2599865
theorem B3461771 : Blo 1215425 3461771 := bstep (se 1 (by rfl) ⟨2596328, by rfl⟩ : syracuseStep 3461771 = 5192657) B5192657
theorem B1217199 : Blo 1215425 1217199 := bstep (se 1 (by rfl) ⟨912899, by rfl⟩ : syracuseStep 1217199 = 1825799) B1825799
theorem B1217223 : Blo 1215425 1217223 := bstep (se 1 (by rfl) ⟨912917, by rfl⟩ : syracuseStep 1217223 = 1825835) B1825835
theorem B1217243 : Blo 1215425 1217243 := bstep (se 1 (by rfl) ⟨912932, by rfl⟩ : syracuseStep 1217243 = 1825865) B1825865
theorem B2052857 : Blo 1215425 2052857 := bstep (se 2 (by rfl) ⟨769821, by rfl⟩ : syracuseStep 2052857 = 1539643) B1539643
theorem B4928285 : Blo 1215425 4928285 := bstep (se 3 (by rfl) ⟨924053, by rfl⟩ : syracuseStep 4928285 = 1848107) B1848107
theorem B1217319 : Blo 1215425 1217319 := bstep (se 1 (by rfl) ⟨912989, by rfl⟩ : syracuseStep 1217319 = 1825979) B1825979
theorem B3076937 : Blo 1215425 3076937 := bstep (se 2 (by rfl) ⟨1153851, by rfl⟩ : syracuseStep 3076937 = 2307703) B2307703
theorem B1217359 : Blo 1215425 1217359 := bstep (se 1 (by rfl) ⟨913019, by rfl⟩ : syracuseStep 1217359 = 1826039) B1826039
theorem B1217375 : Blo 1215425 1217375 := bstep (se 1 (by rfl) ⟨913031, by rfl⟩ : syracuseStep 1217375 = 1826063) B1826063
theorem B1217403 : Blo 1215425 1217403 := bstep (se 1 (by rfl) ⟨913052, by rfl⟩ : syracuseStep 1217403 = 1826105) B1826105
theorem B4928417 : Blo 1215425 4928417 := bstep (se 2 (by rfl) ⟨1848156, by rfl⟩ : syracuseStep 4928417 = 3696313) B3696313
theorem B4617121 : Blo 1215425 4617121 := bstep (se 2 (by rfl) ⟨1731420, by rfl⟩ : syracuseStep 4617121 = 3462841) B3462841
theorem B1823663 : Blo 1215425 1823663 := bstep (se 1 (by rfl) ⟨1367747, by rfl⟩ : syracuseStep 1823663 = 2735495) B2735495
theorem B2053039 : Blo 1215425 2053039 := bstep (se 1 (by rfl) ⟨1539779, by rfl⟩ : syracuseStep 2053039 = 3079559) B3079559
theorem B23393245 : Blo 1215425 23393245 := bstep (se 3 (by rfl) ⟨4386233, by rfl⟩ : syracuseStep 23393245 = 8772467) B8772467
theorem B2053127 : Blo 1215425 2053127 := bstep (se 1 (by rfl) ⟨1539845, by rfl⟩ : syracuseStep 2053127 = 3079691) B3079691
theorem B1823753 : Blo 1215425 1823753 := bstep (se 2 (by rfl) ⟨683907, by rfl⟩ : syracuseStep 1823753 = 1367815) B1367815
theorem B1823783 : Blo 1215425 1823783 := bstep (se 1 (by rfl) ⟨1367837, by rfl⟩ : syracuseStep 1823783 = 2735675) B2735675
theorem B5551183 : Blo 1215425 5551183 := bstep (se 1 (by rfl) ⟨4163387, by rfl⟩ : syracuseStep 5551183 = 8326775) B8326775
theorem B1823867 : Blo 1215425 1823867 := bstep (se 1 (by rfl) ⟨1367900, by rfl⟩ : syracuseStep 1823867 = 2735801) B2735801
theorem B3077291 : Blo 1215425 3077291 := bstep (se 1 (by rfl) ⟨2307968, by rfl⟩ : syracuseStep 3077291 = 4615937) B4615937
theorem B1299655 : Blo 1215425 1299655 := bstep (se 1 (by rfl) ⟨974741, by rfl⟩ : syracuseStep 1299655 = 1949483) B1949483
theorem B1823993 : Blo 1215425 1823993 := bstep (se 2 (by rfl) ⟨683997, by rfl⟩ : syracuseStep 1823993 = 1367995) B1367995
theorem B1824095 : Blo 1215425 1824095 := bstep (se 1 (by rfl) ⟨1368071, by rfl⟩ : syracuseStep 1824095 = 2736143) B2736143
theorem B2053471 : Blo 1215425 2053471 := bstep (se 1 (by rfl) ⟨1540103, by rfl⟩ : syracuseStep 2053471 = 3080207) B3080207
theorem B1824107 : Blo 1215425 1824107 := bstep (se 1 (by rfl) ⟨1368080, by rfl⟩ : syracuseStep 1824107 = 2736161) B2736161
theorem B3700097 : Blo 1215425 3700097 := bstep (se 2 (by rfl) ⟨1387536, by rfl⟩ : syracuseStep 3700097 = 2775073) B2775073
theorem B2053559 : Blo 1215425 2053559 := bstep (se 1 (by rfl) ⟨1540169, by rfl⟩ : syracuseStep 2053559 = 3080339) B3080339
theorem B1824335 : Blo 1215425 1824335 := bstep (se 1 (by rfl) ⟨1368251, by rfl⟩ : syracuseStep 1824335 = 2736503) B2736503
theorem B5264993 : Blo 1215425 5264993 := bstep (se 2 (by rfl) ⟨1974372, by rfl⟩ : syracuseStep 5264993 = 3948745) B3948745
theorem B1824455 : Blo 1215425 1824455 := bstep (se 1 (by rfl) ⟨1368341, by rfl⟩ : syracuseStep 1824455 = 2736683) B2736683
theorem B4216531 : Blo 1215425 4216531 := bstep (se 1 (by rfl) ⟨3162398, by rfl⟩ : syracuseStep 4216531 = 6324797) B6324797
theorem B4618079 : Blo 1215425 4618079 := bstep (se 1 (by rfl) ⟨3463559, by rfl⟩ : syracuseStep 4618079 = 6927119) B6927119
theorem B1824617 : Blo 1215425 1824617 := bstep (se 2 (by rfl) ⟨684231, by rfl⟩ : syracuseStep 1824617 = 1368463) B1368463
theorem B4618093 : Blo 1215425 4618093 := bstep (se 3 (by rfl) ⟨865892, by rfl⟩ : syracuseStep 4618093 = 1731785) B1731785
theorem B3078071 : Blo 1215425 3078071 := bstep (se 1 (by rfl) ⟨2308553, by rfl⟩ : syracuseStep 3078071 = 4617107) B4617107
theorem B1824695 : Blo 1215425 1824695 := bstep (se 1 (by rfl) ⟨1368521, by rfl⟩ : syracuseStep 1824695 = 2737043) B2737043
theorem B6158267 : Blo 1215425 6158267 := bstep (se 1 (by rfl) ⟨4618700, by rfl⟩ : syracuseStep 6158267 = 9237401) B9237401
theorem B5552059 : Blo 1215425 5552059 := bstep (se 1 (by rfl) ⟨4164044, by rfl⟩ : syracuseStep 5552059 = 8328089) B8328089
theorem B1824731 : Blo 1215425 1824731 := bstep (se 1 (by rfl) ⟨1368548, by rfl⟩ : syracuseStep 1824731 = 2737097) B2737097
theorem B2308105 : Blo 1215425 2308105 := bstep (se 2 (by rfl) ⟨865539, by rfl⟩ : syracuseStep 2308105 = 1731079) B1731079
theorem B2054153 : Blo 1215425 2054153 := bstep (se 2 (by rfl) ⟨770307, by rfl⟩ : syracuseStep 2054153 = 1540615) B1540615
theorem B4102163 : Blo 1215425 4102163 := bstep (se 1 (by rfl) ⟨3076622, by rfl⟩ : syracuseStep 4102163 = 6153245) B6153245
theorem B4618397 : Blo 1215425 4618397 := bstep (se 3 (by rfl) ⟨865949, by rfl⟩ : syracuseStep 4618397 = 1731899) B1731899
theorem B2054315 : Blo 1215425 2054315 := bstep (se 1 (by rfl) ⟨1540736, by rfl⟩ : syracuseStep 2054315 = 3081473) B3081473
theorem B5200139 : Blo 1215425 5200139 := bstep (se 1 (by rfl) ⟨3900104, by rfl⟩ : syracuseStep 5200139 = 7800209) B7800209
theorem B1947977 : Blo 1215425 1947977 := bstep (se 2 (by rfl) ⟨730491, by rfl⟩ : syracuseStep 1947977 = 1460983) B1460983
theorem B4102487 : Blo 1215425 4102487 := bstep (se 1 (by rfl) ⟨3076865, by rfl⟩ : syracuseStep 4102487 = 6153731) B6153731
theorem B11696471 : Blo 1215425 11696471 := bstep (se 1 (by rfl) ⟨8772353, by rfl⟩ : syracuseStep 11696471 = 17544707) B17544707
theorem B1849775 : Blo 1215425 1849775 := bstep (se 1 (by rfl) ⟨1387331, by rfl⟩ : syracuseStep 1849775 = 2774663) B2774663
theorem B1825199 : Blo 1215425 1825199 := bstep (se 1 (by rfl) ⟨1368899, by rfl⟩ : syracuseStep 1825199 = 2737799) B2737799
theorem B1948169 : Blo 1215425 1948169 := bstep (se 2 (by rfl) ⟨730563, by rfl⟩ : syracuseStep 1948169 = 1461127) B1461127
theorem B1825289 : Blo 1215425 1825289 := bstep (se 2 (by rfl) ⟨684483, by rfl⟩ : syracuseStep 1825289 = 1368967) B1368967
theorem B6240793 : Blo 1215425 6240793 := bstep (se 2 (by rfl) ⟨2340297, by rfl⟩ : syracuseStep 6240793 = 4680595) B4680595
theorem B1825319 : Blo 1215425 1825319 := bstep (se 1 (by rfl) ⟨1368989, by rfl⟩ : syracuseStep 1825319 = 2737979) B2737979
theorem B3897953 : Blo 1215425 3897953 := bstep (se 2 (by rfl) ⟨1461732, by rfl⟩ : syracuseStep 3897953 = 2923465) B2923465
theorem B1825403 : Blo 1215425 1825403 := bstep (se 1 (by rfl) ⟨1369052, by rfl⟩ : syracuseStep 1825403 = 2738105) B2738105
theorem B8321737 : Blo 1215425 8321737 := bstep (se 2 (by rfl) ⟨3120651, by rfl⟩ : syracuseStep 8321737 = 6241303) B6241303
theorem B2308819 : Blo 1215425 2308819 := bstep (se 1 (by rfl) ⟨1731614, by rfl⟩ : syracuseStep 2308819 = 3463229) B3463229
theorem B2079479 : Blo 1215425 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B1825529 : Blo 1215425 1825529 := bstep (se 2 (by rfl) ⟨684573, by rfl⟩ : syracuseStep 1825529 = 1369147) B1369147
theorem B4619051 : Blo 1215425 4619051 := bstep (se 1 (by rfl) ⟨3464288, by rfl⟩ : syracuseStep 4619051 = 6928577) B6928577
theorem B1825631 : Blo 1215425 1825631 := bstep (se 1 (by rfl) ⟨1369223, by rfl⟩ : syracuseStep 1825631 = 2738447) B2738447
theorem B2734955 : Blo 1215425 2734955 := bstep (se 1 (by rfl) ⟨2051216, by rfl⟩ : syracuseStep 2734955 = 4102433) B4102433
theorem B1825643 : Blo 1215425 1825643 := bstep (se 1 (by rfl) ⟨1369232, by rfl⟩ : syracuseStep 1825643 = 2738465) B2738465
theorem B2735009 : Blo 1215425 2735009 := bstep (se 2 (by rfl) ⟨1025628, by rfl⟩ : syracuseStep 2735009 = 2051257) B2051257
theorem B3079073 : Blo 1215425 3079073 := bstep (se 2 (by rfl) ⟨1154652, by rfl⟩ : syracuseStep 3079073 = 2309305) B2309305
theorem B6929327 : Blo 1215425 6929327 := bstep (se 1 (by rfl) ⟨5196995, by rfl⟩ : syracuseStep 6929327 = 10393991) B10393991
theorem B1850407 : Blo 1215425 1850407 := bstep (se 1 (by rfl) ⟨1387805, by rfl⟩ : syracuseStep 1850407 = 2775611) B2775611
theorem B1825871 : Blo 1215425 1825871 := bstep (se 1 (by rfl) ⟨1369403, by rfl⟩ : syracuseStep 1825871 = 2738807) B2738807
theorem B1825991 : Blo 1215425 1825991 := bstep (se 1 (by rfl) ⟨1369493, by rfl⟩ : syracuseStep 1825991 = 2738987) B2738987
theorem B7019723 : Blo 1215425 7019723 := bstep (se 1 (by rfl) ⟨5264792, by rfl⟩ : syracuseStep 7019723 = 10529585) B10529585
theorem B6159563 : Blo 1215425 6159563 := bstep (se 1 (by rfl) ⟨4619672, by rfl⟩ : syracuseStep 6159563 = 9239345) B9239345
theorem B2735351 : Blo 1215425 2735351 := bstep (se 1 (by rfl) ⟨2051513, by rfl⟩ : syracuseStep 2735351 = 4103027) B4103027
theorem B9239831 : Blo 1215425 9239831 := bstep (se 1 (by rfl) ⟨6929873, by rfl⟩ : syracuseStep 9239831 = 13859747) B13859747
theorem B3079529 : Blo 1215425 3079529 := bstep (se 2 (by rfl) ⟨1154823, by rfl⟩ : syracuseStep 3079529 = 2309647) B2309647
theorem B4103567 : Blo 1215425 4103567 := bstep (se 1 (by rfl) ⟨3077675, by rfl⟩ : syracuseStep 4103567 = 6155351) B6155351
theorem B10395053 : Blo 1215425 10395053 := bstep (se 3 (by rfl) ⟨1949072, by rfl⟩ : syracuseStep 10395053 = 3898145) B3898145
theorem B2309563 : Blo 1215425 2309563 := bstep (se 1 (by rfl) ⟨1732172, by rfl⟩ : syracuseStep 2309563 = 3464345) B3464345
theorem B5545417 : Blo 1215425 5545417 := bstep (se 2 (by rfl) ⟨2079531, by rfl⟩ : syracuseStep 5545417 = 4159063) B4159063
theorem B3464801 : Blo 1215425 3464801 := bstep (se 2 (by rfl) ⟨1299300, by rfl⟩ : syracuseStep 3464801 = 2598601) B2598601
theorem B4931207 : Blo 1215425 4931207 := bstep (se 1 (by rfl) ⟨3698405, by rfl⟩ : syracuseStep 4931207 = 7396811) B7396811
theorem B11697853 : Blo 1215425 11697853 := bstep (se 3 (by rfl) ⟨2193347, by rfl⟩ : syracuseStep 11697853 = 4386695) B4386695
theorem B4103891 : Blo 1215425 4103891 := bstep (se 1 (by rfl) ⟨3077918, by rfl⟩ : syracuseStep 4103891 = 6155837) B6155837
theorem B2735945 : Blo 1215425 2735945 := bstep (se 2 (by rfl) ⟨1025979, by rfl⟩ : syracuseStep 2735945 = 2051959) B2051959
theorem B2310049 : Blo 1215425 2310049 := bstep (se 2 (by rfl) ⟨866268, by rfl⟩ : syracuseStep 2310049 = 1732537) B1732537
theorem B3465143 : Blo 1215425 3465143 := bstep (se 1 (by rfl) ⟨2598857, by rfl⟩ : syracuseStep 3465143 = 5197715) B5197715
theorem B2736233 : Blo 1215425 2736233 := bstep (se 2 (by rfl) ⟨1026087, by rfl⟩ : syracuseStep 2736233 = 2052175) B2052175
theorem B5841067 : Blo 1215425 5841067 := bstep (se 1 (by rfl) ⟨4380800, by rfl⟩ : syracuseStep 5841067 = 8761601) B8761601
theorem B1368283 : Blo 1215425 1368283 := bstep (se 1 (by rfl) ⟨1026212, by rfl⟩ : syracuseStep 1368283 = 2052425) B2052425
theorem B24985907 : Blo 1215425 24985907 := bstep (se 1 (by rfl) ⟨18739430, by rfl⟩ : syracuseStep 24985907 = 37478861) B37478861
theorem B5194057 : Blo 1215425 5194057 := bstep (se 2 (by rfl) ⟨1947771, by rfl⟩ : syracuseStep 5194057 = 3895543) B3895543
theorem B4104539 : Blo 1215425 4104539 := bstep (se 1 (by rfl) ⟨3078404, by rfl⟩ : syracuseStep 4104539 = 6156809) B6156809
theorem B29606309 : Blo 1215425 29606309 := bstep (se 4 (by rfl) ⟨2775591, by rfl⟩ : syracuseStep 29606309 = 5551183) B5551183
theorem B6160859 : Blo 1215425 6160859 := bstep (se 1 (by rfl) ⟨4620644, by rfl⟩ : syracuseStep 6160859 = 9241289) B9241289
theorem B1368571 : Blo 1215425 1368571 := bstep (se 1 (by rfl) ⟨1026428, by rfl⟩ : syracuseStep 1368571 = 2052857) B2052857
theorem B2736719 : Blo 1215425 2736719 := bstep (se 1 (by rfl) ⟨2052539, by rfl⟩ : syracuseStep 2736719 = 4105079) B4105079
theorem B3285611 : Blo 1215425 3285611 := bstep (se 1 (by rfl) ⟨2464208, by rfl⟩ : syracuseStep 3285611 = 4928417) B4928417
theorem B2310763 : Blo 1215425 2310763 := bstep (se 1 (by rfl) ⟨1733072, by rfl⟩ : syracuseStep 2310763 = 3466145) B3466145
theorem B3080825 : Blo 1215425 3080825 := bstep (se 2 (by rfl) ⟨1155309, by rfl⟩ : syracuseStep 3080825 = 2310619) B2310619
theorem B6578833 : Blo 1215425 6578833 := bstep (se 2 (by rfl) ⟨2467062, by rfl⟩ : syracuseStep 6578833 = 4934125) B4934125
theorem B3080875 : Blo 1215425 3080875 := bstep (se 1 (by rfl) ⟨2310656, by rfl⟩ : syracuseStep 3080875 = 4621313) B4621313
theorem B1368751 : Blo 1215425 1368751 := bstep (se 1 (by rfl) ⟨1026563, by rfl⟩ : syracuseStep 1368751 = 2053127) B2053127
theorem B2310839 : Blo 1215425 2310839 := bstep (se 1 (by rfl) ⟨1733129, by rfl⟩ : syracuseStep 2310839 = 3466259) B3466259
theorem B14795465 : Blo 1215425 14795465 := bstep (se 2 (by rfl) ⟨5548299, by rfl⟩ : syracuseStep 14795465 = 11096599) B11096599
theorem B2736863 : Blo 1215425 2736863 := bstep (se 1 (by rfl) ⟨2052647, by rfl⟩ : syracuseStep 2736863 = 4105295) B4105295
theorem B2311067 : Blo 1215425 2311067 := bstep (se 1 (by rfl) ⟨1733300, by rfl⟩ : syracuseStep 2311067 = 3466601) B3466601
theorem B2466731 : Blo 1215425 2466731 := bstep (se 1 (by rfl) ⟨1850048, by rfl⟩ : syracuseStep 2466731 = 3700097) B3700097
theorem B6161345 : Blo 1215425 6161345 := bstep (se 2 (by rfl) ⟨2310504, by rfl⟩ : syracuseStep 6161345 = 4621009) B4621009
theorem B1369039 : Blo 1215425 1369039 := bstep (se 1 (by rfl) ⟨1026779, by rfl⟩ : syracuseStep 1369039 = 2053559) B2053559
theorem B4441051 : Blo 1215425 4441051 := bstep (se 1 (by rfl) ⟨3330788, by rfl⟩ : syracuseStep 4441051 = 6661577) B6661577
theorem B2737115 : Blo 1215425 2737115 := bstep (se 1 (by rfl) ⟨2052836, by rfl⟩ : syracuseStep 2737115 = 4105673) B4105673
theorem B3081179 : Blo 1215425 3081179 := bstep (se 1 (by rfl) ⟨2310884, by rfl⟩ : syracuseStep 3081179 = 4621769) B4621769
theorem B23708675 : Blo 1215425 23708675 := bstep (se 1 (by rfl) ⟨17781506, by rfl⟩ : syracuseStep 23708675 = 35563013) B35563013
theorem B6931493 : Blo 1215425 6931493 := bstep (se 4 (by rfl) ⟨649827, by rfl⟩ : syracuseStep 6931493 = 1299655) B1299655
theorem B4932733 : Blo 1215425 4932733 := bstep (se 3 (by rfl) ⟨924887, by rfl⟩ : syracuseStep 4932733 = 1849775) B1849775
theorem B2737295 : Blo 1215425 2737295 := bstep (se 1 (by rfl) ⟨2052971, by rfl⟩ : syracuseStep 2737295 = 4105943) B4105943
theorem B2737385 : Blo 1215425 2737385 := bstep (se 2 (by rfl) ⟨1026519, by rfl⟩ : syracuseStep 2737385 = 2053039) B2053039
theorem B2737439 : Blo 1215425 2737439 := bstep (se 1 (by rfl) ⟨2053079, by rfl⟩ : syracuseStep 2737439 = 4106159) B4106159
theorem B3081503 : Blo 1215425 3081503 := bstep (se 1 (by rfl) ⟨2311127, by rfl⟩ : syracuseStep 3081503 = 4622255) B4622255
theorem B4105511 : Blo 1215425 4105511 := bstep (se 1 (by rfl) ⟨3079133, by rfl⟩ : syracuseStep 4105511 = 6158267) B6158267
theorem B1369435 : Blo 1215425 1369435 := bstep (se 1 (by rfl) ⟨1027076, by rfl⟩ : syracuseStep 1369435 = 2054153) B2054153
theorem B5195117 : Blo 1215425 5195117 := bstep (se 3 (by rfl) ⟨974084, by rfl⟩ : syracuseStep 5195117 = 1948169) B1948169
theorem B1369543 : Blo 1215425 1369543 := bstep (se 1 (by rfl) ⟨1027157, by rfl⟩ : syracuseStep 1369543 = 2054315) B2054315
theorem B8324641 : Blo 1215425 8324641 := bstep (se 2 (by rfl) ⟨3121740, by rfl⟩ : syracuseStep 8324641 = 6243481) B6243481
theorem B6571655 : Blo 1215425 6571655 := bstep (se 1 (by rfl) ⟨4928741, by rfl⟩ : syracuseStep 6571655 = 9857483) B9857483
theorem B4621981 : Blo 1215425 4621981 := bstep (se 3 (by rfl) ⟨866621, by rfl⟩ : syracuseStep 4621981 = 1733243) B1733243
theorem B4441787 : Blo 1215425 4441787 := bstep (se 1 (by rfl) ⟨3331340, by rfl⟩ : syracuseStep 4441787 = 6662681) B6662681
theorem B2598635 : Blo 1215425 2598635 := bstep (se 1 (by rfl) ⟨1948976, by rfl⟩ : syracuseStep 2598635 = 3897953) B3897953
theorem B2737961 : Blo 1215425 2737961 := bstep (se 2 (by rfl) ⟨1026735, by rfl⟩ : syracuseStep 2737961 = 2053471) B2053471
theorem B1386319 : Blo 1215425 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B13142093 : Blo 1215425 13142093 := bstep (se 3 (by rfl) ⟨2464142, by rfl⟩ : syracuseStep 13142093 = 4928285) B4928285
theorem B4679815 : Blo 1215425 4679815 := bstep (se 1 (by rfl) ⟨3509861, by rfl⟩ : syracuseStep 4679815 = 7019723) B7019723
theorem B4106375 : Blo 1215425 4106375 := bstep (se 1 (by rfl) ⟨3079781, by rfl⟩ : syracuseStep 4106375 = 6159563) B6159563
theorem B5622041 : Blo 1215425 5622041 := bstep (se 2 (by rfl) ⟨2108265, by rfl⟩ : syracuseStep 5622041 = 4216531) B4216531
theorem B5335421 : Blo 1215425 5335421 := bstep (se 3 (by rfl) ⟨1000391, by rfl⟩ : syracuseStep 5335421 = 2000783) B2000783
theorem B6572431 : Blo 1215425 6572431 := bstep (se 1 (by rfl) ⟨4929323, by rfl⟩ : syracuseStep 6572431 = 9858647) B9858647
theorem B3287471 : Blo 1215425 3287471 := bstep (se 1 (by rfl) ⟨2465603, by rfl⟩ : syracuseStep 3287471 = 4931207) B4931207
theorem B8768087 : Blo 1215425 8768087 := bstep (se 1 (by rfl) ⟨6576065, by rfl⟩ : syracuseStep 8768087 = 13152131) B13152131
theorem B6155027 : Blo 1215425 6155027 := bstep (se 1 (by rfl) ⟨4616270, by rfl⟩ : syracuseStep 6155027 = 9232541) B9232541
theorem B2739023 : Blo 1215425 2739023 := bstep (se 1 (by rfl) ⟨2054267, by rfl⟩ : syracuseStep 2739023 = 4108535) B4108535
theorem B1215439 : Blo 1215425 1215439 := bstep (se 1 (by rfl) ⟨911579, by rfl⟩ : syracuseStep 1215439 = 1823159) B1823159
theorem B1215463 : Blo 1215425 1215463 := bstep (se 1 (by rfl) ⟨911597, by rfl⟩ : syracuseStep 1215463 = 1823195) B1823195
theorem B44969093 : Blo 1215425 44969093 := bstep (se 4 (by rfl) ⟨4215852, by rfl⟩ : syracuseStep 44969093 = 8431705) B8431705
theorem B2051291 : Blo 1215425 2051291 := bstep (se 1 (by rfl) ⟨1538468, by rfl⟩ : syracuseStep 2051291 = 3076937) B3076937
theorem B1215775 : Blo 1215425 1215775 := bstep (se 1 (by rfl) ⟨911831, by rfl⟩ : syracuseStep 1215775 = 1823663) B1823663
theorem B1731871 : Blo 1215425 1731871 := bstep (se 1 (by rfl) ⟨1298903, by rfl⟩ : syracuseStep 1731871 = 2597807) B2597807
theorem B1215835 : Blo 1215425 1215835 := bstep (se 1 (by rfl) ⟨911876, by rfl⟩ : syracuseStep 1215835 = 1823753) B1823753
theorem B4107617 : Blo 1215425 4107617 := bstep (se 2 (by rfl) ⟨1540356, by rfl⟩ : syracuseStep 4107617 = 3080713) B3080713
theorem B1215855 : Blo 1215425 1215855 := bstep (se 1 (by rfl) ⟨911891, by rfl⟩ : syracuseStep 1215855 = 1823783) B1823783
theorem B22179187 : Blo 1215425 22179187 := bstep (se 1 (by rfl) ⟨16634390, by rfl⟩ : syracuseStep 22179187 = 33268781) B33268781
theorem B1215911 : Blo 1215425 1215911 := bstep (se 1 (by rfl) ⟨911933, by rfl⟩ : syracuseStep 1215911 = 1823867) B1823867
theorem B2051527 : Blo 1215425 2051527 := bstep (se 1 (by rfl) ⟨1538645, by rfl⟩ : syracuseStep 2051527 = 3077291) B3077291
theorem B1215995 : Blo 1215425 1215995 := bstep (se 1 (by rfl) ⟨911996, by rfl⟩ : syracuseStep 1215995 = 1823993) B1823993
theorem B1216063 : Blo 1215425 1216063 := bstep (se 1 (by rfl) ⟨912047, by rfl⟩ : syracuseStep 1216063 = 1824095) B1824095
theorem B1216071 : Blo 1215425 1216071 := bstep (se 1 (by rfl) ⟨912053, by rfl⟩ : syracuseStep 1216071 = 1824107) B1824107
theorem B11095649 : Blo 1215425 11095649 := bstep (se 2 (by rfl) ⟨4160868, by rfl⟩ : syracuseStep 11095649 = 8321737) B8321737
theorem B1216223 : Blo 1215425 1216223 := bstep (se 1 (by rfl) ⟨912167, by rfl⟩ : syracuseStep 1216223 = 1824335) B1824335
theorem B3509995 : Blo 1215425 3509995 := bstep (se 1 (by rfl) ⟨2632496, by rfl⟩ : syracuseStep 3509995 = 5264993) B5264993
theorem B1216303 : Blo 1215425 1216303 := bstep (se 1 (by rfl) ⟨912227, by rfl⟩ : syracuseStep 1216303 = 1824455) B1824455
theorem B6156161 : Blo 1215425 6156161 := bstep (se 2 (by rfl) ⟨2308560, by rfl⟩ : syracuseStep 6156161 = 4617121) B4617121
theorem B1216411 : Blo 1215425 1216411 := bstep (se 1 (by rfl) ⟨912308, by rfl⟩ : syracuseStep 1216411 = 1824617) B1824617
theorem B2052047 : Blo 1215425 2052047 := bstep (se 1 (by rfl) ⟨1539035, by rfl⟩ : syracuseStep 2052047 = 3078071) B3078071
theorem B1216463 : Blo 1215425 1216463 := bstep (se 1 (by rfl) ⟨912347, by rfl⟩ : syracuseStep 1216463 = 1824695) B1824695
theorem B31190993 : Blo 1215425 31190993 := bstep (se 2 (by rfl) ⟨11696622, by rfl⟩ : syracuseStep 31190993 = 23393245) B23393245
theorem B1216487 : Blo 1215425 1216487 := bstep (se 1 (by rfl) ⟨912365, by rfl⟩ : syracuseStep 1216487 = 1824731) B1824731
theorem B84275315 : Blo 1215425 84275315 := bstep (se 1 (by rfl) ⟨63206486, by rfl⟩ : syracuseStep 84275315 = 126412973) B126412973
theorem B1298651 : Blo 1215425 1298651 := bstep (se 1 (by rfl) ⟨973988, by rfl⟩ : syracuseStep 1298651 = 1947977) B1947977
theorem B1216799 : Blo 1215425 1216799 := bstep (se 1 (by rfl) ⟨912599, by rfl⟩ : syracuseStep 1216799 = 1825199) B1825199
theorem B1216859 : Blo 1215425 1216859 := bstep (se 1 (by rfl) ⟨912644, by rfl⟩ : syracuseStep 1216859 = 1825289) B1825289
theorem B1216879 : Blo 1215425 1216879 := bstep (se 1 (by rfl) ⟨912659, by rfl⟩ : syracuseStep 1216879 = 1825319) B1825319
theorem B1216935 : Blo 1215425 1216935 := bstep (se 1 (by rfl) ⟨912701, by rfl⟩ : syracuseStep 1216935 = 1825403) B1825403
theorem B1217019 : Blo 1215425 1217019 := bstep (se 1 (by rfl) ⟨912764, by rfl⟩ : syracuseStep 1217019 = 1825529) B1825529
theorem B6926867 : Blo 1215425 6926867 := bstep (se 1 (by rfl) ⟨5195150, by rfl⟩ : syracuseStep 6926867 = 10390301) B10390301
theorem B1217087 : Blo 1215425 1217087 := bstep (se 1 (by rfl) ⟨912815, by rfl⟩ : syracuseStep 1217087 = 1825631) B1825631
theorem B1823303 : Blo 1215425 1823303 := bstep (se 1 (by rfl) ⟨1367477, by rfl⟩ : syracuseStep 1823303 = 2734955) B2734955
theorem B1217095 : Blo 1215425 1217095 := bstep (se 1 (by rfl) ⟨912821, by rfl⟩ : syracuseStep 1217095 = 1825643) B1825643
theorem B7393889 : Blo 1215425 7393889 := bstep (se 2 (by rfl) ⟨2772708, by rfl⟩ : syracuseStep 7393889 = 5545417) B5545417
theorem B1823339 : Blo 1215425 1823339 := bstep (se 1 (by rfl) ⟨1367504, by rfl⟩ : syracuseStep 1823339 = 2735009) B2735009
theorem B2052715 : Blo 1215425 2052715 := bstep (se 1 (by rfl) ⟨1539536, by rfl⟩ : syracuseStep 2052715 = 3079073) B3079073
theorem B6156971 : Blo 1215425 6156971 := bstep (se 1 (by rfl) ⟨4617728, by rfl⟩ : syracuseStep 6156971 = 9235457) B9235457
theorem B1217247 : Blo 1215425 1217247 := bstep (se 1 (by rfl) ⟨912935, by rfl⟩ : syracuseStep 1217247 = 1825871) B1825871
theorem B11104991 : Blo 1215425 11104991 := bstep (se 1 (by rfl) ⟨8328743, by rfl⟩ : syracuseStep 11104991 = 16657487) B16657487
theorem B1217327 : Blo 1215425 1217327 := bstep (se 1 (by rfl) ⟨912995, by rfl⟩ : syracuseStep 1217327 = 1825991) B1825991
theorem B1823567 : Blo 1215425 1823567 := bstep (se 1 (by rfl) ⟨1367675, by rfl⟩ : syracuseStep 1823567 = 2735351) B2735351
theorem B16634717 : Blo 1215425 16634717 := bstep (se 3 (by rfl) ⟨3119009, by rfl⟩ : syracuseStep 16634717 = 6238019) B6238019
theorem B2053019 : Blo 1215425 2053019 := bstep (se 1 (by rfl) ⟨1539764, by rfl⟩ : syracuseStep 2053019 = 3079529) B3079529
theorem B7394429 : Blo 1215425 7394429 := bstep (se 3 (by rfl) ⟨1386455, by rfl⟩ : syracuseStep 7394429 = 2772911) B2772911
theorem B6157457 : Blo 1215425 6157457 := bstep (se 2 (by rfl) ⟨2309046, by rfl⟩ : syracuseStep 6157457 = 4618093) B4618093
theorem B8762525 : Blo 1215425 8762525 := bstep (se 3 (by rfl) ⟨1642973, by rfl⟩ : syracuseStep 8762525 = 3285947) B3285947
theorem B1823963 : Blo 1215425 1823963 := bstep (se 1 (by rfl) ⟨1367972, by rfl⟩ : syracuseStep 1823963 = 2735945) B2735945
theorem B7402745 : Blo 1215425 7402745 := bstep (se 2 (by rfl) ⟨2776029, by rfl⟩ : syracuseStep 7402745 = 5552059) B5552059
theorem B3077473 : Blo 1215425 3077473 := bstep (se 2 (by rfl) ⟨1154052, by rfl⟩ : syracuseStep 3077473 = 2308105) B2308105
theorem B1824137 : Blo 1215425 1824137 := bstep (se 2 (by rfl) ⟨684051, by rfl⟩ : syracuseStep 1824137 = 1368103) B1368103
theorem B5625227 : Blo 1215425 5625227 := bstep (se 1 (by rfl) ⟨4218920, by rfl⟩ : syracuseStep 5625227 = 8437841) B8437841
theorem B9868837 : Blo 1215425 9868837 := bstep (se 4 (by rfl) ⟨925203, by rfl⟩ : syracuseStep 9868837 = 1850407) B1850407
theorem B1824491 : Blo 1215425 1824491 := bstep (se 1 (by rfl) ⟨1368368, by rfl⟩ : syracuseStep 1824491 = 2736737) B2736737
theorem B2307847 : Blo 1215425 2307847 := bstep (se 1 (by rfl) ⟨1730885, by rfl⟩ : syracuseStep 2307847 = 3461771) B3461771
theorem B1824719 : Blo 1215425 1824719 := bstep (se 1 (by rfl) ⟨1368539, by rfl⟩ : syracuseStep 1824719 = 2737079) B2737079
theorem B13867037 : Blo 1215425 13867037 := bstep (se 3 (by rfl) ⟨2600069, by rfl⟩ : syracuseStep 13867037 = 5200139) B5200139
theorem B8321057 : Blo 1215425 8321057 := bstep (se 2 (by rfl) ⟨3120396, by rfl⟩ : syracuseStep 8321057 = 6240793) B6240793
theorem B3078425 : Blo 1215425 3078425 := bstep (se 2 (by rfl) ⟨1154409, by rfl⟩ : syracuseStep 3078425 = 2308819) B2308819
theorem B1825115 : Blo 1215425 1825115 := bstep (se 1 (by rfl) ⟨1368836, by rfl⟩ : syracuseStep 1825115 = 2737673) B2737673
theorem B2464111 : Blo 1215425 2464111 := bstep (se 1 (by rfl) ⟨1848083, by rfl⟩ : syracuseStep 2464111 = 3696167) B3696167
theorem B2923003 : Blo 1215425 2923003 := bstep (se 1 (by rfl) ⟨2192252, by rfl⟩ : syracuseStep 2923003 = 4384505) B4384505
theorem B3078719 : Blo 1215425 3078719 := bstep (se 1 (by rfl) ⟨2309039, by rfl⟩ : syracuseStep 3078719 = 4618079) B4618079
theorem B1825343 : Blo 1215425 1825343 := bstep (se 1 (by rfl) ⟨1369007, by rfl⟩ : syracuseStep 1825343 = 2738015) B2738015
theorem B2734775 : Blo 1215425 2734775 := bstep (se 1 (by rfl) ⟨2051081, by rfl⟩ : syracuseStep 2734775 = 4102163) B4102163
theorem B1825463 : Blo 1215425 1825463 := bstep (se 1 (by rfl) ⟨1369097, by rfl⟩ : syracuseStep 1825463 = 2738195) B2738195
theorem B3078931 : Blo 1215425 3078931 := bstep (se 1 (by rfl) ⟨2309198, by rfl⟩ : syracuseStep 3078931 = 4618397) B4618397
theorem B2734991 : Blo 1215425 2734991 := bstep (se 1 (by rfl) ⟨2051243, by rfl⟩ : syracuseStep 2734991 = 4102487) B4102487
theorem B7797647 : Blo 1215425 7797647 := bstep (se 1 (by rfl) ⟨5848235, by rfl⟩ : syracuseStep 7797647 = 11696471) B11696471
theorem B1825691 : Blo 1215425 1825691 := bstep (se 1 (by rfl) ⟨1369268, by rfl⟩ : syracuseStep 1825691 = 2738537) B2738537
theorem B16636859 : Blo 1215425 16636859 := bstep (se 1 (by rfl) ⟨12477644, by rfl⟩ : syracuseStep 16636859 = 24955289) B24955289
theorem B2776103 : Blo 1215425 2776103 := bstep (se 1 (by rfl) ⟨2082077, by rfl⟩ : syracuseStep 2776103 = 4164155) B4164155
theorem B10394675 : Blo 1215425 10394675 := bstep (se 1 (by rfl) ⟨7796006, by rfl⟩ : syracuseStep 10394675 = 15592013) B15592013
theorem B21060803 : Blo 1215425 21060803 := bstep (se 1 (by rfl) ⟨15795602, by rfl⟩ : syracuseStep 21060803 = 31591205) B31591205
theorem B3079367 : Blo 1215425 3079367 := bstep (se 1 (by rfl) ⟨2309525, by rfl⟩ : syracuseStep 3079367 = 4619051) B4619051
theorem B2464987 : Blo 1215425 2464987 := bstep (se 1 (by rfl) ⟨1848740, by rfl⟩ : syracuseStep 2464987 = 3697481) B3697481
theorem B3079417 : Blo 1215425 3079417 := bstep (se 2 (by rfl) ⟨1154781, by rfl⟩ : syracuseStep 3079417 = 2309563) B2309563
theorem B2776313 : Blo 1215425 2776313 := bstep (se 2 (by rfl) ⟨1041117, by rfl⟩ : syracuseStep 2776313 = 2082235) B2082235
theorem B4619551 : Blo 1215425 4619551 := bstep (se 1 (by rfl) ⟨3464663, by rfl⟩ : syracuseStep 4619551 = 6929327) B6929327
theorem B1826087 : Blo 1215425 1826087 := bstep (se 1 (by rfl) ⟨1369565, by rfl⟩ : syracuseStep 1826087 = 2739131) B2739131
theorem B1367419 : Blo 1215425 1367419 := bstep (se 1 (by rfl) ⟨1025564, by rfl⟩ : syracuseStep 1367419 = 2051129) B2051129
theorem B2891207 : Blo 1215425 2891207 := bstep (se 1 (by rfl) ⟨2168405, by rfl⟩ : syracuseStep 2891207 = 4336811) B4336811
theorem B6159887 : Blo 1215425 6159887 := bstep (se 1 (by rfl) ⟨4619915, by rfl⟩ : syracuseStep 6159887 = 9239831) B9239831
theorem B15597137 : Blo 1215425 15597137 := bstep (se 2 (by rfl) ⟨5848926, by rfl⟩ : syracuseStep 15597137 = 11697853) B11697853
theorem B2735711 : Blo 1215425 2735711 := bstep (se 1 (by rfl) ⟨2051783, by rfl⟩ : syracuseStep 2735711 = 4103567) B4103567
theorem B6930035 : Blo 1215425 6930035 := bstep (se 1 (by rfl) ⟨5197526, by rfl⟩ : syracuseStep 6930035 = 10395053) B10395053
theorem B2309867 : Blo 1215425 2309867 := bstep (se 1 (by rfl) ⟨1732400, by rfl⟩ : syracuseStep 2309867 = 3464801) B3464801
theorem B13852457 : Blo 1215425 13852457 := bstep (se 2 (by rfl) ⟨5194671, by rfl⟩ : syracuseStep 13852457 = 10389343) B10389343
theorem B2735927 : Blo 1215425 2735927 := bstep (se 1 (by rfl) ⟨2051945, by rfl⟩ : syracuseStep 2735927 = 4103891) B4103891
theorem B1367887 : Blo 1215425 1367887 := bstep (se 1 (by rfl) ⟨1025915, by rfl⟩ : syracuseStep 1367887 = 2051831) B2051831
theorem B3080065 : Blo 1215425 3080065 := bstep (se 2 (by rfl) ⟨1155024, by rfl⟩ : syracuseStep 3080065 = 2310049) B2310049
theorem B2310095 : Blo 1215425 2310095 := bstep (se 1 (by rfl) ⟨1732571, by rfl⟩ : syracuseStep 2310095 = 3465143) B3465143
theorem B35045581 : Blo 1215425 35045581 := bstep (se 3 (by rfl) ⟨6571046, by rfl⟩ : syracuseStep 35045581 = 13142093) B13142093
theorem B2736359 : Blo 1215425 2736359 := bstep (se 1 (by rfl) ⟨2052269, by rfl⟩ : syracuseStep 2736359 = 4104539) B4104539
theorem B4104647 : Blo 1215425 4104647 := bstep (se 1 (by rfl) ⟨3078485, by rfl⟩ : syracuseStep 4104647 = 6156971) B6156971
theorem B1540559 : Blo 1215425 1540559 := bstep (se 1 (by rfl) ⟨1155419, by rfl⟩ : syracuseStep 1540559 = 2310839) B2310839
theorem B1368679 : Blo 1215425 1368679 := bstep (se 1 (by rfl) ⟨1026509, by rfl⟩ : syracuseStep 1368679 = 2053019) B2053019
theorem B1540711 : Blo 1215425 1540711 := bstep (se 1 (by rfl) ⟨1155533, by rfl⟩ : syracuseStep 1540711 = 2311067) B2311067
theorem B4620995 : Blo 1215425 4620995 := bstep (se 1 (by rfl) ⟨3465746, by rfl⟩ : syracuseStep 4620995 = 6931493) B6931493
theorem B4104971 : Blo 1215425 4104971 := bstep (se 1 (by rfl) ⟨3078728, by rfl⟩ : syracuseStep 4104971 = 6157457) B6157457
theorem B5841683 : Blo 1215425 5841683 := bstep (se 1 (by rfl) ⟨4381262, by rfl⟩ : syracuseStep 5841683 = 8762525) B8762525
theorem B2736953 : Blo 1215425 2736953 := bstep (se 2 (by rfl) ⟨1026357, by rfl⟩ : syracuseStep 2736953 = 2052715) B2052715
theorem B3081017 : Blo 1215425 3081017 := bstep (se 2 (by rfl) ⟨1155381, by rfl⟩ : syracuseStep 3081017 = 2310763) B2310763
theorem B2737007 : Blo 1215425 2737007 := bstep (se 1 (by rfl) ⟨2052755, by rfl⟩ : syracuseStep 2737007 = 4105511) B4105511
theorem B4105241 : Blo 1215425 4105241 := bstep (se 2 (by rfl) ⟨1539465, by rfl⟩ : syracuseStep 4105241 = 3078931) B3078931
theorem B8766589 : Blo 1215425 8766589 := bstep (se 3 (by rfl) ⟨1643735, by rfl⟩ : syracuseStep 8766589 = 3287471) B3287471
theorem B56911157 : Blo 1215425 56911157 := bstep (se 5 (by rfl) ⟨2667710, by rfl⟩ : syracuseStep 56911157 = 5335421) B5335421
theorem B5547371 : Blo 1215425 5547371 := bstep (se 1 (by rfl) ⟨4160528, by rfl⟩ : syracuseStep 5547371 = 8321057) B8321057
theorem B2737583 : Blo 1215425 2737583 := bstep (se 1 (by rfl) ⟨2053187, by rfl⟩ : syracuseStep 2737583 = 4106375) B4106375
theorem B3286649 : Blo 1215425 3286649 := bstep (se 2 (by rfl) ⟨1232493, by rfl⟩ : syracuseStep 3286649 = 2464987) B2464987
theorem B4105889 : Blo 1215425 4105889 := bstep (se 2 (by rfl) ⟨1539708, by rfl⟩ : syracuseStep 4105889 = 3079417) B3079417
theorem B39454573 : Blo 1215425 39454573 := bstep (se 3 (by rfl) ⟨7397732, by rfl⟩ : syracuseStep 39454573 = 14795465) B14795465
theorem B13141925 : Blo 1215425 13141925 := bstep (se 4 (by rfl) ⟨1232055, by rfl⟩ : syracuseStep 13141925 = 2464111) B2464111
theorem B13158449 : Blo 1215425 13158449 := bstep (se 2 (by rfl) ⟨4934418, by rfl⟩ : syracuseStep 13158449 = 9868837) B9868837
theorem B6162641 : Blo 1215425 6162641 := bstep (se 2 (by rfl) ⟨2310990, by rfl⟩ : syracuseStep 6162641 = 4621981) B4621981
theorem B2738411 : Blo 1215425 2738411 := bstep (se 1 (by rfl) ⟨2053808, by rfl⟩ : syracuseStep 2738411 = 4107617) B4107617
theorem B1927471 : Blo 1215425 1927471 := bstep (se 1 (by rfl) ⟨1445603, by rfl⟩ : syracuseStep 1927471 = 2891207) B2891207
theorem B4679993 : Blo 1215425 4679993 := bstep (se 2 (by rfl) ⟨1754997, by rfl⟩ : syracuseStep 4679993 = 3509995) B3509995
theorem B4106591 : Blo 1215425 4106591 := bstep (se 1 (by rfl) ⟨3079943, by rfl⟩ : syracuseStep 4106591 = 6159887) B6159887
theorem B10398091 : Blo 1215425 10398091 := bstep (se 1 (by rfl) ⟨7798568, by rfl⟩ : syracuseStep 10398091 = 15597137) B15597137
theorem B23685605 : Blo 1215425 23685605 := bstep (se 4 (by rfl) ⟨2220525, by rfl⟩ : syracuseStep 23685605 = 4441051) B4441051
theorem B4106753 : Blo 1215425 4106753 := bstep (se 2 (by rfl) ⟨1540032, by rfl⟩ : syracuseStep 4106753 = 3080065) B3080065
theorem B9234971 : Blo 1215425 9234971 := bstep (se 1 (by rfl) ⟨6926228, by rfl⟩ : syracuseStep 9234971 = 13852457) B13852457
theorem B20793995 : Blo 1215425 20793995 := bstep (se 1 (by rfl) ⟨15595496, by rfl⟩ : syracuseStep 20793995 = 31190993) B31190993
theorem B56183543 : Blo 1215425 56183543 := bstep (se 1 (by rfl) ⟨42137657, by rfl⟩ : syracuseStep 56183543 = 84275315) B84275315
theorem B16657271 : Blo 1215425 16657271 := bstep (se 1 (by rfl) ⟨12492953, by rfl⟩ : syracuseStep 16657271 = 24985907) B24985907
theorem B19737539 : Blo 1215425 19737539 := bstep (se 1 (by rfl) ⟨14803154, by rfl⟩ : syracuseStep 19737539 = 29606309) B29606309
theorem B4107239 : Blo 1215425 4107239 := bstep (se 1 (by rfl) ⟨3080429, by rfl⟩ : syracuseStep 4107239 = 6160859) B6160859
theorem B1215535 : Blo 1215425 1215535 := bstep (se 1 (by rfl) ⟨911651, by rfl⟩ : syracuseStep 1215535 = 1823303) B1823303
theorem B2190407 : Blo 1215425 2190407 := bstep (se 1 (by rfl) ⟨1642805, by rfl⟩ : syracuseStep 2190407 = 3285611) B3285611
theorem B1215559 : Blo 1215425 1215559 := bstep (se 1 (by rfl) ⟨911669, by rfl⟩ : syracuseStep 1215559 = 1823339) B1823339
theorem B6925409 : Blo 1215425 6925409 := bstep (se 2 (by rfl) ⟨2597028, by rfl⟩ : syracuseStep 6925409 = 5194057) B5194057
theorem B1215711 : Blo 1215425 1215711 := bstep (se 1 (by rfl) ⟨911783, by rfl⟩ : syracuseStep 1215711 = 1823567) B1823567
theorem B4107563 : Blo 1215425 4107563 := bstep (se 1 (by rfl) ⟨3080672, by rfl⟩ : syracuseStep 4107563 = 6161345) B6161345
theorem B15805783 : Blo 1215425 15805783 := bstep (se 1 (by rfl) ⟨11854337, by rfl⟩ : syracuseStep 15805783 = 23708675) B23708675
theorem B1215975 : Blo 1215425 1215975 := bstep (se 1 (by rfl) ⟨911981, by rfl⟩ : syracuseStep 1215975 = 1823963) B1823963
theorem B4935163 : Blo 1215425 4935163 := bstep (se 1 (by rfl) ⟨3701372, by rfl⟩ : syracuseStep 4935163 = 7402745) B7402745
theorem B4107833 : Blo 1215425 4107833 := bstep (se 2 (by rfl) ⟨1540437, by rfl⟩ : syracuseStep 4107833 = 3080875) B3080875
theorem B1216091 : Blo 1215425 1216091 := bstep (se 1 (by rfl) ⟨912068, by rfl⟩ : syracuseStep 1216091 = 1824137) B1824137
theorem B2961191 : Blo 1215425 2961191 := bstep (se 1 (by rfl) ⟨2220893, by rfl⟩ : syracuseStep 2961191 = 4441787) B4441787
theorem B1216327 : Blo 1215425 1216327 := bstep (se 1 (by rfl) ⟨912245, by rfl⟩ : syracuseStep 1216327 = 1824491) B1824491
theorem B1732423 : Blo 1215425 1732423 := bstep (se 1 (by rfl) ⟨1299317, by rfl⟩ : syracuseStep 1732423 = 2598635) B2598635
theorem B1216479 : Blo 1215425 1216479 := bstep (se 1 (by rfl) ⟨912359, by rfl⟩ : syracuseStep 1216479 = 1824719) B1824719
theorem B9244691 : Blo 1215425 9244691 := bstep (se 1 (by rfl) ⟨6933518, by rfl⟩ : syracuseStep 9244691 = 13867037) B13867037
theorem B3748027 : Blo 1215425 3748027 := bstep (se 1 (by rfl) ⟨2811020, by rfl⟩ : syracuseStep 3748027 = 5622041) B5622041
theorem B2052283 : Blo 1215425 2052283 := bstep (se 1 (by rfl) ⟨1539212, by rfl⟩ : syracuseStep 2052283 = 3078425) B3078425
theorem B1216743 : Blo 1215425 1216743 := bstep (se 1 (by rfl) ⟨912557, by rfl⟩ : syracuseStep 1216743 = 1825115) B1825115
theorem B2052479 : Blo 1215425 2052479 := bstep (se 1 (by rfl) ⟨1539359, by rfl⟩ : syracuseStep 2052479 = 3078719) B3078719
theorem B1216895 : Blo 1215425 1216895 := bstep (se 1 (by rfl) ⟨912671, by rfl⟩ : syracuseStep 1216895 = 1825343) B1825343
theorem B5845391 : Blo 1215425 5845391 := bstep (se 1 (by rfl) ⟨4384043, by rfl⟩ : syracuseStep 5845391 = 8768087) B8768087
theorem B1823183 : Blo 1215425 1823183 := bstep (se 1 (by rfl) ⟨1367387, by rfl⟩ : syracuseStep 1823183 = 2734775) B2734775
theorem B1216975 : Blo 1215425 1216975 := bstep (se 1 (by rfl) ⟨912731, by rfl⟩ : syracuseStep 1216975 = 1825463) B1825463
theorem B1823225 : Blo 1215425 1823225 := bstep (se 2 (by rfl) ⟨683709, by rfl⟩ : syracuseStep 1823225 = 1367419) B1367419
theorem B1823327 : Blo 1215425 1823327 := bstep (se 1 (by rfl) ⟨1367495, by rfl⟩ : syracuseStep 1823327 = 2734991) B2734991
theorem B5198431 : Blo 1215425 5198431 := bstep (se 1 (by rfl) ⟨3898823, by rfl⟩ : syracuseStep 5198431 = 7797647) B7797647
theorem B1217127 : Blo 1215425 1217127 := bstep (se 1 (by rfl) ⟨912845, by rfl⟩ : syracuseStep 1217127 = 1825691) B1825691
theorem B29979395 : Blo 1215425 29979395 := bstep (se 1 (by rfl) ⟨22484546, by rfl⟩ : syracuseStep 29979395 = 44969093) B44969093
theorem B2052911 : Blo 1215425 2052911 := bstep (se 1 (by rfl) ⟨1539683, by rfl⟩ : syracuseStep 2052911 = 3079367) B3079367
theorem B1217391 : Blo 1215425 1217391 := bstep (se 1 (by rfl) ⟨913043, by rfl⟩ : syracuseStep 1217391 = 1826087) B1826087
theorem B3077129 : Blo 1215425 3077129 := bstep (se 2 (by rfl) ⟨1153923, by rfl⟩ : syracuseStep 3077129 = 2307847) B2307847
theorem B1823807 : Blo 1215425 1823807 := bstep (se 1 (by rfl) ⟨1367855, by rfl⟩ : syracuseStep 1823807 = 2735711) B2735711
theorem B1848425 : Blo 1215425 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B1823849 : Blo 1215425 1823849 := bstep (se 2 (by rfl) ⟨683943, by rfl⟩ : syracuseStep 1823849 = 1367887) B1367887
theorem B1823951 : Blo 1215425 1823951 := bstep (se 1 (by rfl) ⟨1367963, by rfl⟩ : syracuseStep 1823951 = 2735927) B2735927
theorem B1824155 : Blo 1215425 1824155 := bstep (se 1 (by rfl) ⟨1368116, by rfl⟩ : syracuseStep 1824155 = 2736233) B2736233
theorem B6239753 : Blo 1215425 6239753 := bstep (se 2 (by rfl) ⟨2339907, by rfl⟩ : syracuseStep 6239753 = 4679815) B4679815
theorem B7788089 : Blo 1215425 7788089 := bstep (se 2 (by rfl) ⟨2920533, by rfl⟩ : syracuseStep 7788089 = 5841067) B5841067
theorem B1824377 : Blo 1215425 1824377 := bstep (se 2 (by rfl) ⟨684141, by rfl⟩ : syracuseStep 1824377 = 1368283) B1368283
theorem B4617911 : Blo 1215425 4617911 := bstep (se 1 (by rfl) ⟨3463433, by rfl⟩ : syracuseStep 4617911 = 6926867) B6926867
theorem B1824479 : Blo 1215425 1824479 := bstep (se 1 (by rfl) ⟨1368359, by rfl⟩ : syracuseStep 1824479 = 2736719) B2736719
theorem B4929259 : Blo 1215425 4929259 := bstep (se 1 (by rfl) ⟨3696944, by rfl⟩ : syracuseStep 4929259 = 7393889) B7393889
theorem B2053883 : Blo 1215425 2053883 := bstep (se 1 (by rfl) ⟨1540412, by rfl⟩ : syracuseStep 2053883 = 3080825) B3080825
theorem B1824575 : Blo 1215425 1824575 := bstep (se 1 (by rfl) ⟨1368431, by rfl⟩ : syracuseStep 1824575 = 2736863) B2736863
theorem B7403327 : Blo 1215425 7403327 := bstep (se 1 (by rfl) ⟨5552495, by rfl⟩ : syracuseStep 7403327 = 11104991) B11104991
theorem B8763241 : Blo 1215425 8763241 := bstep (se 2 (by rfl) ⟨3286215, by rfl⟩ : syracuseStep 8763241 = 6572431) B6572431
theorem B11089811 : Blo 1215425 11089811 := bstep (se 1 (by rfl) ⟨8317358, by rfl⟩ : syracuseStep 11089811 = 16634717) B16634717
theorem B3463069 : Blo 1215425 3463069 := bstep (se 3 (by rfl) ⟨649325, by rfl⟩ : syracuseStep 3463069 = 1298651) B1298651
theorem B1824743 : Blo 1215425 1824743 := bstep (se 1 (by rfl) ⟨1368557, by rfl⟩ : syracuseStep 1824743 = 2737115) B2737115
theorem B2054119 : Blo 1215425 2054119 := bstep (se 1 (by rfl) ⟨1540589, by rfl⟩ : syracuseStep 2054119 = 3081179) B3081179
theorem B7403501 : Blo 1215425 7403501 := bstep (se 3 (by rfl) ⟨1388156, by rfl⟩ : syracuseStep 7403501 = 2776313) B2776313
theorem B1824761 : Blo 1215425 1824761 := bstep (se 2 (by rfl) ⟨684285, by rfl⟩ : syracuseStep 1824761 = 1368571) B1368571
theorem B3897337 : Blo 1215425 3897337 := bstep (se 2 (by rfl) ⟨1461501, by rfl⟩ : syracuseStep 3897337 = 2923003) B2923003
theorem B4929619 : Blo 1215425 4929619 := bstep (se 1 (by rfl) ⟨3697214, by rfl⟩ : syracuseStep 4929619 = 7394429) B7394429
theorem B1824863 : Blo 1215425 1824863 := bstep (se 1 (by rfl) ⟨1368647, by rfl⟩ : syracuseStep 1824863 = 2737295) B2737295
theorem B1824923 : Blo 1215425 1824923 := bstep (se 1 (by rfl) ⟨1368692, by rfl⟩ : syracuseStep 1824923 = 2737385) B2737385
theorem B1824959 : Blo 1215425 1824959 := bstep (se 1 (by rfl) ⟨1368719, by rfl⟩ : syracuseStep 1824959 = 2737439) B2737439
theorem B2054335 : Blo 1215425 2054335 := bstep (se 1 (by rfl) ⟨1540751, by rfl⟩ : syracuseStep 2054335 = 3081503) B3081503
theorem B8771777 : Blo 1215425 8771777 := bstep (se 2 (by rfl) ⟨3289416, by rfl⟩ : syracuseStep 8771777 = 6578833) B6578833
theorem B1825001 : Blo 1215425 1825001 := bstep (se 2 (by rfl) ⟨684375, by rfl⟩ : syracuseStep 1825001 = 1368751) B1368751
theorem B3463411 : Blo 1215425 3463411 := bstep (se 1 (by rfl) ⟨2597558, by rfl⟩ : syracuseStep 3463411 = 5195117) B5195117
theorem B3750151 : Blo 1215425 3750151 := bstep (se 1 (by rfl) ⟨2812613, by rfl⟩ : syracuseStep 3750151 = 5625227) B5625227
theorem B4381103 : Blo 1215425 4381103 := bstep (se 1 (by rfl) ⟨3285827, by rfl⟩ : syracuseStep 4381103 = 6571655) B6571655
theorem B1825307 : Blo 1215425 1825307 := bstep (se 1 (by rfl) ⟨1368980, by rfl⟩ : syracuseStep 1825307 = 2737961) B2737961
theorem B1825385 : Blo 1215425 1825385 := bstep (se 2 (by rfl) ⟨684519, by rfl⟩ : syracuseStep 1825385 = 1369039) B1369039
theorem B6576977 : Blo 1215425 6576977 := bstep (se 2 (by rfl) ⟨2466366, by rfl⟩ : syracuseStep 6576977 = 4932733) B4932733
theorem B2309161 : Blo 1215425 2309161 := bstep (se 2 (by rfl) ⟨865935, by rfl⟩ : syracuseStep 2309161 = 1731871) B1731871
theorem B6159401 : Blo 1215425 6159401 := bstep (se 2 (by rfl) ⟨2309775, by rfl⟩ : syracuseStep 6159401 = 4619551) B4619551
theorem B1825913 : Blo 1215425 1825913 := bstep (se 2 (by rfl) ⟨684717, by rfl⟩ : syracuseStep 1825913 = 1369435) B1369435
theorem B4103297 : Blo 1215425 4103297 := bstep (se 2 (by rfl) ⟨1538736, by rfl⟩ : syracuseStep 4103297 = 3077473) B3077473
theorem B29572249 : Blo 1215425 29572249 := bstep (se 2 (by rfl) ⟨11089593, by rfl⟩ : syracuseStep 29572249 = 22179187) B22179187
theorem B4103351 : Blo 1215425 4103351 := bstep (se 1 (by rfl) ⟨3077513, by rfl⟩ : syracuseStep 4103351 = 6155027) B6155027
theorem B1826015 : Blo 1215425 1826015 := bstep (se 1 (by rfl) ⟨1369511, by rfl⟩ : syracuseStep 1826015 = 2739023) B2739023
theorem B2735369 : Blo 1215425 2735369 := bstep (se 2 (by rfl) ⟨1025763, by rfl⟩ : syracuseStep 2735369 = 2051527) B2051527
theorem B1826057 : Blo 1215425 1826057 := bstep (se 2 (by rfl) ⟨684771, by rfl⟩ : syracuseStep 1826057 = 1369543) B1369543
theorem B11091239 : Blo 1215425 11091239 := bstep (se 1 (by rfl) ⟨8318429, by rfl⟩ : syracuseStep 11091239 = 16636859) B16636859
theorem B1850735 : Blo 1215425 1850735 := bstep (se 1 (by rfl) ⟨1388051, by rfl⟩ : syracuseStep 1850735 = 2776103) B2776103
theorem B6929783 : Blo 1215425 6929783 := bstep (se 1 (by rfl) ⟨5197337, by rfl⟩ : syracuseStep 6929783 = 10394675) B10394675
theorem B11099521 : Blo 1215425 11099521 := bstep (se 2 (by rfl) ⟨4162320, by rfl⟩ : syracuseStep 11099521 = 8324641) B8324641
theorem B14040535 : Blo 1215425 14040535 := bstep (se 1 (by rfl) ⟨10530401, by rfl⟩ : syracuseStep 14040535 = 21060803) B21060803
theorem B1367527 : Blo 1215425 1367527 := bstep (se 1 (by rfl) ⟨1025645, by rfl⟩ : syracuseStep 1367527 = 2051291) B2051291
theorem B7397099 : Blo 1215425 7397099 := bstep (se 1 (by rfl) ⟨5547824, by rfl⟩ : syracuseStep 7397099 = 11095649) B11095649
theorem B4620023 : Blo 1215425 4620023 := bstep (se 1 (by rfl) ⟨3465017, by rfl⟩ : syracuseStep 4620023 = 6930035) B6930035
theorem B6577949 : Blo 1215425 6577949 := bstep (se 3 (by rfl) ⟨1233365, by rfl⟩ : syracuseStep 6577949 = 2466731) B2466731
theorem B1539911 : Blo 1215425 1539911 := bstep (se 1 (by rfl) ⟨1154933, by rfl⟩ : syracuseStep 1539911 = 2309867) B2309867
theorem B4104107 : Blo 1215425 4104107 := bstep (se 1 (by rfl) ⟨3078080, by rfl⟩ : syracuseStep 4104107 = 6156161) B6156161
theorem B1368031 : Blo 1215425 1368031 := bstep (se 1 (by rfl) ⟨1026023, by rfl⟩ : syracuseStep 1368031 = 2052047) B2052047
theorem B1540063 : Blo 1215425 1540063 := bstep (se 1 (by rfl) ⟨1155047, by rfl⟩ : syracuseStep 1540063 = 2310095) B2310095
theorem B5841085 : Blo 1215425 5841085 := bstep (se 3 (by rfl) ⟨1095203, by rfl⟩ : syracuseStep 5841085 = 2190407) B2190407
theorem B4997369 : Blo 1215425 4997369 := bstep (se 2 (by rfl) ⟨1874013, by rfl⟩ : syracuseStep 4997369 = 3748027) B3748027
theorem B2736377 : Blo 1215425 2736377 := bstep (se 2 (by rfl) ⟨1026141, by rfl⟩ : syracuseStep 2736377 = 2052283) B2052283
theorem B1368319 : Blo 1215425 1368319 := bstep (se 1 (by rfl) ⟨1026239, by rfl⟩ : syracuseStep 1368319 = 2052479) B2052479
theorem B46727441 : Blo 1215425 46727441 := bstep (se 2 (by rfl) ⟨17522790, by rfl⟩ : syracuseStep 46727441 = 35045581) B35045581
theorem B2736431 : Blo 1215425 2736431 := bstep (se 1 (by rfl) ⟨2052323, by rfl⟩ : syracuseStep 2736431 = 4104647) B4104647
theorem B3080663 : Blo 1215425 3080663 := bstep (se 1 (by rfl) ⟨2310497, by rfl⟩ : syracuseStep 3080663 = 4620995) B4620995
theorem B2736647 : Blo 1215425 2736647 := bstep (se 1 (by rfl) ⟨2052485, by rfl⟩ : syracuseStep 2736647 = 4104971) B4104971
theorem B1368607 : Blo 1215425 1368607 := bstep (se 1 (by rfl) ⟨1026455, by rfl⟩ : syracuseStep 1368607 = 2052911) B2052911
theorem B2736827 : Blo 1215425 2736827 := bstep (se 1 (by rfl) ⟨2052620, by rfl⟩ : syracuseStep 2736827 = 4105241) B4105241
theorem B6931241 : Blo 1215425 6931241 := bstep (se 2 (by rfl) ⟨2599215, by rfl⟩ : syracuseStep 6931241 = 5198431) B5198431
theorem B2737259 : Blo 1215425 2737259 := bstep (se 1 (by rfl) ⟨2052944, by rfl⟩ : syracuseStep 2737259 = 4105889) B4105889
theorem B1369255 : Blo 1215425 1369255 := bstep (se 1 (by rfl) ⟨1026941, by rfl⟩ : syracuseStep 1369255 = 2053883) B2053883
theorem B39429665 : Blo 1215425 39429665 := bstep (se 2 (by rfl) ⟨14786124, by rfl⟩ : syracuseStep 39429665 = 29572249) B29572249
theorem B2737727 : Blo 1215425 2737727 := bstep (se 1 (by rfl) ⟨2053295, by rfl⟩ : syracuseStep 2737727 = 4106591) B4106591
theorem B2737835 : Blo 1215425 2737835 := bstep (se 1 (by rfl) ⟨2053376, by rfl⟩ : syracuseStep 2737835 = 4106753) B4106753
theorem B13862663 : Blo 1215425 13862663 := bstep (se 1 (by rfl) ⟨10396997, by rfl⟩ : syracuseStep 13862663 = 20793995) B20793995
theorem B37455695 : Blo 1215425 37455695 := bstep (se 1 (by rfl) ⟨28091771, by rfl⟩ : syracuseStep 37455695 = 56183543) B56183543
theorem B4384651 : Blo 1215425 4384651 := bstep (se 1 (by rfl) ⟨3288488, by rfl⟩ : syracuseStep 4384651 = 6576977) B6576977
theorem B18720713 : Blo 1215425 18720713 := bstep (se 2 (by rfl) ⟨7020267, by rfl⟩ : syracuseStep 18720713 = 14040535) B14040535
theorem B13158359 : Blo 1215425 13158359 := bstep (se 1 (by rfl) ⟨9868769, by rfl⟩ : syracuseStep 13158359 = 19737539) B19737539
theorem B2738159 : Blo 1215425 2738159 := bstep (se 1 (by rfl) ⟨2053619, by rfl⟩ : syracuseStep 2738159 = 4107239) B4107239
theorem B6580217 : Blo 1215425 6580217 := bstep (se 2 (by rfl) ⟨2467581, by rfl⟩ : syracuseStep 6580217 = 4935163) B4935163
theorem B4106267 : Blo 1215425 4106267 := bstep (se 1 (by rfl) ⟨3079700, by rfl⟩ : syracuseStep 4106267 = 6159401) B6159401
theorem B17541197 : Blo 1215425 17541197 := bstep (se 3 (by rfl) ⟨3288974, by rfl⟩ : syracuseStep 17541197 = 6577949) B6577949
theorem B4106429 : Blo 1215425 4106429 := bstep (se 3 (by rfl) ⟨769955, by rfl⟩ : syracuseStep 4106429 = 1539911) B1539911
theorem B2738375 : Blo 1215425 2738375 := bstep (se 1 (by rfl) ⟨2053781, by rfl⟩ : syracuseStep 2738375 = 4107563) B4107563
theorem B6572345 : Blo 1215425 6572345 := bstep (se 2 (by rfl) ⟨2464629, by rfl⟩ : syracuseStep 6572345 = 4929259) B4929259
theorem B2738555 : Blo 1215425 2738555 := bstep (se 1 (by rfl) ⟨2053916, by rfl⟩ : syracuseStep 2738555 = 4107833) B4107833
theorem B11684321 : Blo 1215425 11684321 := bstep (se 2 (by rfl) ⟨4381620, by rfl⟩ : syracuseStep 11684321 = 8763241) B8763241
theorem B2738825 : Blo 1215425 2738825 := bstep (se 2 (by rfl) ⟨1027059, by rfl⟩ : syracuseStep 2738825 = 2054119) B2054119
theorem B5196449 : Blo 1215425 5196449 := bstep (se 2 (by rfl) ⟨1948668, by rfl⟩ : syracuseStep 5196449 = 3897337) B3897337
theorem B6163127 : Blo 1215425 6163127 := bstep (se 1 (by rfl) ⟨4622345, by rfl⟩ : syracuseStep 6163127 = 9244691) B9244691
theorem B6572825 : Blo 1215425 6572825 := bstep (se 2 (by rfl) ⟨2464809, by rfl⟩ : syracuseStep 6572825 = 4929619) B4929619
theorem B2739113 : Blo 1215425 2739113 := bstep (se 2 (by rfl) ⟨1027167, by rfl⟩ : syracuseStep 2739113 = 2054335) B2054335
theorem B1215455 : Blo 1215425 1215455 := bstep (se 1 (by rfl) ⟨911591, by rfl⟩ : syracuseStep 1215455 = 1823183) B1823183
theorem B1215483 : Blo 1215425 1215483 := bstep (se 1 (by rfl) ⟨911612, by rfl⟩ : syracuseStep 1215483 = 1823225) B1823225
theorem B5000201 : Blo 1215425 5000201 := bstep (se 2 (by rfl) ⟨1875075, by rfl⟩ : syracuseStep 5000201 = 3750151) B3750151
theorem B1215551 : Blo 1215425 1215551 := bstep (se 1 (by rfl) ⟨911663, by rfl⟩ : syracuseStep 1215551 = 1823327) B1823327
theorem B3894455 : Blo 1215425 3894455 := bstep (se 1 (by rfl) ⟨2920841, by rfl⟩ : syracuseStep 3894455 = 5841683) B5841683
theorem B13864121 : Blo 1215425 13864121 := bstep (se 2 (by rfl) ⟨5199045, by rfl⟩ : syracuseStep 13864121 = 10398091) B10398091
theorem B2051419 : Blo 1215425 2051419 := bstep (se 1 (by rfl) ⟨1538564, by rfl⟩ : syracuseStep 2051419 = 3077129) B3077129
theorem B1215871 : Blo 1215425 1215871 := bstep (se 1 (by rfl) ⟨911903, by rfl⟩ : syracuseStep 1215871 = 1823807) B1823807
theorem B1215899 : Blo 1215425 1215899 := bstep (se 1 (by rfl) ⟨911924, by rfl⟩ : syracuseStep 1215899 = 1823849) B1823849
theorem B1215967 : Blo 1215425 1215967 := bstep (se 1 (by rfl) ⟨911975, by rfl⟩ : syracuseStep 1215967 = 1823951) B1823951
theorem B37940771 : Blo 1215425 37940771 := bstep (se 1 (by rfl) ⟨28455578, by rfl⟩ : syracuseStep 37940771 = 56911157) B56911157
theorem B1216103 : Blo 1215425 1216103 := bstep (se 1 (by rfl) ⟨912077, by rfl⟩ : syracuseStep 1216103 = 1824155) B1824155
theorem B4935293 : Blo 1215425 4935293 := bstep (se 3 (by rfl) ⟨925367, by rfl⟩ : syracuseStep 4935293 = 1850735) B1850735
theorem B2191099 : Blo 1215425 2191099 := bstep (se 1 (by rfl) ⟨1643324, by rfl⟩ : syracuseStep 2191099 = 3286649) B3286649
theorem B1216251 : Blo 1215425 1216251 := bstep (se 1 (by rfl) ⟨912188, by rfl⟩ : syracuseStep 1216251 = 1824377) B1824377
theorem B1216319 : Blo 1215425 1216319 := bstep (se 1 (by rfl) ⟨912239, by rfl⟩ : syracuseStep 1216319 = 1824479) B1824479
theorem B4108157 : Blo 1215425 4108157 := bstep (se 3 (by rfl) ⟨770279, by rfl⟩ : syracuseStep 4108157 = 1540559) B1540559
theorem B1216383 : Blo 1215425 1216383 := bstep (se 1 (by rfl) ⟨912287, by rfl⟩ : syracuseStep 1216383 = 1824575) B1824575
theorem B4935551 : Blo 1215425 4935551 := bstep (se 1 (by rfl) ⟨3701663, by rfl⟩ : syracuseStep 4935551 = 7403327) B7403327
theorem B7393207 : Blo 1215425 7393207 := bstep (se 1 (by rfl) ⟨5544905, by rfl⟩ : syracuseStep 7393207 = 11089811) B11089811
theorem B8761283 : Blo 1215425 8761283 := bstep (se 1 (by rfl) ⟨6570962, by rfl⟩ : syracuseStep 8761283 = 13141925) B13141925
theorem B1216495 : Blo 1215425 1216495 := bstep (se 1 (by rfl) ⟨912371, by rfl⟩ : syracuseStep 1216495 = 1824743) B1824743
theorem B4935667 : Blo 1215425 4935667 := bstep (se 1 (by rfl) ⟨3701750, by rfl⟩ : syracuseStep 4935667 = 7403501) B7403501
theorem B1216507 : Blo 1215425 1216507 := bstep (se 1 (by rfl) ⟨912380, by rfl⟩ : syracuseStep 1216507 = 1824761) B1824761
theorem B1216575 : Blo 1215425 1216575 := bstep (se 1 (by rfl) ⟨912431, by rfl⟩ : syracuseStep 1216575 = 1824863) B1824863
theorem B1216615 : Blo 1215425 1216615 := bstep (se 1 (by rfl) ⟨912461, by rfl⟩ : syracuseStep 1216615 = 1824923) B1824923
theorem B1216639 : Blo 1215425 1216639 := bstep (se 1 (by rfl) ⟨912479, by rfl⟩ : syracuseStep 1216639 = 1824959) B1824959
theorem B4108427 : Blo 1215425 4108427 := bstep (se 1 (by rfl) ⟨3081320, by rfl⟩ : syracuseStep 4108427 = 6162641) B6162641
theorem B1216667 : Blo 1215425 1216667 := bstep (se 1 (by rfl) ⟨912500, by rfl⟩ : syracuseStep 1216667 = 1825001) B1825001
theorem B2920735 : Blo 1215425 2920735 := bstep (se 1 (by rfl) ⟨2190551, by rfl⟩ : syracuseStep 2920735 = 4381103) B4381103
theorem B15790403 : Blo 1215425 15790403 := bstep (se 1 (by rfl) ⟨11842802, by rfl⟩ : syracuseStep 15790403 = 23685605) B23685605
theorem B6156647 : Blo 1215425 6156647 := bstep (se 1 (by rfl) ⟨4617485, by rfl⟩ : syracuseStep 6156647 = 9234971) B9234971
theorem B1216871 : Blo 1215425 1216871 := bstep (se 1 (by rfl) ⟨912653, by rfl⟩ : syracuseStep 1216871 = 1825307) B1825307
theorem B1216923 : Blo 1215425 1216923 := bstep (se 1 (by rfl) ⟨912692, by rfl⟩ : syracuseStep 1216923 = 1825385) B1825385
theorem B21074377 : Blo 1215425 21074377 := bstep (se 2 (by rfl) ⟨7902891, by rfl⟩ : syracuseStep 21074377 = 15805783) B15805783
theorem B14799361 : Blo 1215425 14799361 := bstep (se 2 (by rfl) ⟨5549760, by rfl⟩ : syracuseStep 14799361 = 11099521) B11099521
theorem B11104847 : Blo 1215425 11104847 := bstep (se 1 (by rfl) ⟨8328635, by rfl⟩ : syracuseStep 11104847 = 16657271) B16657271
theorem B1823369 : Blo 1215425 1823369 := bstep (se 2 (by rfl) ⟨683763, by rfl⟩ : syracuseStep 1823369 = 1367527) B1367527
theorem B4616939 : Blo 1215425 4616939 := bstep (se 1 (by rfl) ⟨3462704, by rfl⟩ : syracuseStep 4616939 = 6925409) B6925409
theorem B1217275 : Blo 1215425 1217275 := bstep (se 1 (by rfl) ⟨912956, by rfl⟩ : syracuseStep 1217275 = 1825913) B1825913
theorem B1217343 : Blo 1215425 1217343 := bstep (se 1 (by rfl) ⟨913007, by rfl⟩ : syracuseStep 1217343 = 1826015) B1826015
theorem B1823579 : Blo 1215425 1823579 := bstep (se 1 (by rfl) ⟨1367684, by rfl⟩ : syracuseStep 1823579 = 2735369) B2735369
theorem B1217371 : Blo 1215425 1217371 := bstep (se 1 (by rfl) ⟨913028, by rfl⟩ : syracuseStep 1217371 = 1826057) B1826057
theorem B7394159 : Blo 1215425 7394159 := bstep (se 1 (by rfl) ⟨5545619, by rfl⟩ : syracuseStep 7394159 = 11091239) B11091239
theorem B52606097 : Blo 1215425 52606097 := bstep (se 2 (by rfl) ⟨19727286, by rfl⟩ : syracuseStep 52606097 = 39454573) B39454573
theorem B4617425 : Blo 1215425 4617425 := bstep (se 2 (by rfl) ⟨1731534, by rfl⟩ : syracuseStep 4617425 = 3463069) B3463069
theorem B1824041 : Blo 1215425 1824041 := bstep (se 2 (by rfl) ⟨684015, by rfl⟩ : syracuseStep 1824041 = 1368031) B1368031
theorem B2053417 : Blo 1215425 2053417 := bstep (se 2 (by rfl) ⟨770031, by rfl⟩ : syracuseStep 2053417 = 1540063) B1540063
theorem B1824239 : Blo 1215425 1824239 := bstep (se 1 (by rfl) ⟨1368179, by rfl⟩ : syracuseStep 1824239 = 2736359) B2736359
theorem B3896927 : Blo 1215425 3896927 := bstep (se 1 (by rfl) ⟨2922695, by rfl⟩ : syracuseStep 3896927 = 5845391) B5845391
theorem B4929133 : Blo 1215425 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B4617881 : Blo 1215425 4617881 := bstep (se 2 (by rfl) ⟨1731705, by rfl⟩ : syracuseStep 4617881 = 3463411) B3463411
theorem B2569961 : Blo 1215425 2569961 := bstep (se 2 (by rfl) ⟨963735, by rfl⟩ : syracuseStep 2569961 = 1927471) B1927471
theorem B19986263 : Blo 1215425 19986263 := bstep (se 1 (by rfl) ⟨14989697, by rfl⟩ : syracuseStep 19986263 = 29979395) B29979395
theorem B1824635 : Blo 1215425 1824635 := bstep (se 1 (by rfl) ⟨1368476, by rfl⟩ : syracuseStep 1824635 = 2736953) B2736953
theorem B2054011 : Blo 1215425 2054011 := bstep (se 1 (by rfl) ⟨1540508, by rfl⟩ : syracuseStep 2054011 = 3081017) B3081017
theorem B1824671 : Blo 1215425 1824671 := bstep (se 1 (by rfl) ⟨1368503, by rfl⟩ : syracuseStep 1824671 = 2737007) B2737007
theorem B1824905 : Blo 1215425 1824905 := bstep (se 2 (by rfl) ⟨684339, by rfl⟩ : syracuseStep 1824905 = 1368679) B1368679
theorem B2054281 : Blo 1215425 2054281 := bstep (se 2 (by rfl) ⟨770355, by rfl⟩ : syracuseStep 2054281 = 1540711) B1540711
theorem B14792989 : Blo 1215425 14792989 := bstep (se 3 (by rfl) ⟨2773685, by rfl⟩ : syracuseStep 14792989 = 5547371) B5547371
theorem B1825055 : Blo 1215425 1825055 := bstep (se 1 (by rfl) ⟨1368791, by rfl⟩ : syracuseStep 1825055 = 2737583) B2737583
theorem B4159835 : Blo 1215425 4159835 := bstep (se 1 (by rfl) ⟨3119876, by rfl⟩ : syracuseStep 4159835 = 6239753) B6239753
theorem B5192059 : Blo 1215425 5192059 := bstep (se 1 (by rfl) ⟨3894044, by rfl⟩ : syracuseStep 5192059 = 7788089) B7788089
theorem B3078607 : Blo 1215425 3078607 := bstep (se 1 (by rfl) ⟨2308955, by rfl⟩ : syracuseStep 3078607 = 4617911) B4617911
theorem B8772299 : Blo 1215425 8772299 := bstep (se 1 (by rfl) ⟨6579224, by rfl⟩ : syracuseStep 8772299 = 13158449) B13158449
theorem B3078881 : Blo 1215425 3078881 := bstep (se 2 (by rfl) ⟨1154580, by rfl⟩ : syracuseStep 3078881 = 2309161) B2309161
theorem B5847851 : Blo 1215425 5847851 := bstep (se 1 (by rfl) ⟨4385888, by rfl⟩ : syracuseStep 5847851 = 8771777) B8771777
theorem B1825607 : Blo 1215425 1825607 := bstep (se 1 (by rfl) ⟨1369205, by rfl⟩ : syracuseStep 1825607 = 2738411) B2738411
theorem B11688785 : Blo 1215425 11688785 := bstep (se 2 (by rfl) ⟨4383294, by rfl⟩ : syracuseStep 11688785 = 8766589) B8766589
theorem B3119995 : Blo 1215425 3119995 := bstep (se 1 (by rfl) ⟨2339996, by rfl⟩ : syracuseStep 3119995 = 4679993) B4679993
theorem B2735531 : Blo 1215425 2735531 := bstep (se 1 (by rfl) ⟨2051648, by rfl⟩ : syracuseStep 2735531 = 4103297) B4103297
theorem B2735567 : Blo 1215425 2735567 := bstep (se 1 (by rfl) ⟨2051675, by rfl⟩ : syracuseStep 2735567 = 4103351) B4103351
theorem B4619855 : Blo 1215425 4619855 := bstep (se 1 (by rfl) ⟨3464891, by rfl⟩ : syracuseStep 4619855 = 6929783) B6929783
theorem B2309897 : Blo 1215425 2309897 := bstep (se 2 (by rfl) ⟨866211, by rfl⟩ : syracuseStep 2309897 = 1732423) B1732423
theorem B4931399 : Blo 1215425 4931399 := bstep (se 1 (by rfl) ⟨3698549, by rfl⟩ : syracuseStep 4931399 = 7397099) B7397099
theorem B3080015 : Blo 1215425 3080015 := bstep (se 1 (by rfl) ⟨2310011, by rfl⟩ : syracuseStep 3080015 = 4620023) B4620023
theorem B1974127 : Blo 1215425 1974127 := bstep (se 1 (by rfl) ⟨1480595, by rfl⟩ : syracuseStep 1974127 = 2961191) B2961191
theorem B2736071 : Blo 1215425 2736071 := bstep (se 1 (by rfl) ⟨2052053, by rfl⟩ : syracuseStep 2736071 = 4104107) B4104107
theorem B10526935 : Blo 1215425 10526935 := bstep (se 1 (by rfl) ⟨7895201, by rfl⟩ : syracuseStep 10526935 = 15790403) B15790403
theorem B4104431 : Blo 1215425 4104431 := bstep (se 1 (by rfl) ⟨3078323, by rfl⟩ : syracuseStep 4104431 = 6156647) B6156647
theorem B6922745 : Blo 1215425 6922745 := bstep (se 2 (by rfl) ⟨2596029, by rfl⟩ : syracuseStep 6922745 = 5192059) B5192059
theorem B4620827 : Blo 1215425 4620827 := bstep (se 1 (by rfl) ⟨3465620, by rfl⟩ : syracuseStep 4620827 = 6931241) B6931241
theorem B28099169 : Blo 1215425 28099169 := bstep (se 2 (by rfl) ⟨10537188, by rfl⟩ : syracuseStep 28099169 = 21074377) B21074377
theorem B4104809 : Blo 1215425 4104809 := bstep (se 2 (by rfl) ⟨1539303, by rfl⟩ : syracuseStep 4104809 = 3078607) B3078607
theorem B35070731 : Blo 1215425 35070731 := bstep (se 1 (by rfl) ⟨26303048, by rfl⟩ : syracuseStep 35070731 = 52606097) B52606097
theorem B2597951 : Blo 1215425 2597951 := bstep (se 1 (by rfl) ⟨1948463, by rfl⟩ : syracuseStep 2597951 = 3896927) B3896927
theorem B1713307 : Blo 1215425 1713307 := bstep (se 1 (by rfl) ⟨1284980, by rfl⟩ : syracuseStep 1713307 = 2569961) B2569961
theorem B9241775 : Blo 1215425 9241775 := bstep (se 1 (by rfl) ⟨6931331, by rfl⟩ : syracuseStep 9241775 = 13862663) B13862663
theorem B24970463 : Blo 1215425 24970463 := bstep (se 1 (by rfl) ⟨18727847, by rfl⟩ : syracuseStep 24970463 = 37455695) B37455695
theorem B2737511 : Blo 1215425 2737511 := bstep (se 1 (by rfl) ⟨2053133, by rfl⟩ : syracuseStep 2737511 = 4106267) B4106267
theorem B2737619 : Blo 1215425 2737619 := bstep (se 1 (by rfl) ⟨2053214, by rfl⟩ : syracuseStep 2737619 = 4106429) B4106429
theorem B2737889 : Blo 1215425 2737889 := bstep (se 2 (by rfl) ⟨1026708, by rfl⟩ : syracuseStep 2737889 = 2053417) B2053417
theorem B7792523 : Blo 1215425 7792523 := bstep (se 1 (by rfl) ⟨5844392, by rfl⟩ : syracuseStep 7792523 = 11688785) B11688785
theorem B9242747 : Blo 1215425 9242747 := bstep (se 1 (by rfl) ⟨6932060, by rfl⟩ : syracuseStep 9242747 = 13864121) B13864121
theorem B6572177 : Blo 1215425 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B13150397 : Blo 1215425 13150397 := bstep (se 3 (by rfl) ⟨2465699, by rfl⟩ : syracuseStep 13150397 = 4931399) B4931399
theorem B2632169 : Blo 1215425 2632169 := bstep (se 2 (by rfl) ⟨987063, by rfl⟩ : syracuseStep 2632169 = 1974127) B1974127
theorem B2738681 : Blo 1215425 2738681 := bstep (se 2 (by rfl) ⟨1027005, by rfl⟩ : syracuseStep 2738681 = 2054011) B2054011
theorem B9857609 : Blo 1215425 9857609 := bstep (se 2 (by rfl) ⟨3696603, by rfl⟩ : syracuseStep 9857609 = 7393207) B7393207
theorem B2738771 : Blo 1215425 2738771 := bstep (se 1 (by rfl) ⟨2054078, by rfl⟩ : syracuseStep 2738771 = 4108157) B4108157
theorem B6580889 : Blo 1215425 6580889 := bstep (se 2 (by rfl) ⟨2467833, by rfl⟩ : syracuseStep 6580889 = 4935667) B4935667
theorem B2738951 : Blo 1215425 2738951 := bstep (se 1 (by rfl) ⟨2054213, by rfl⟩ : syracuseStep 2738951 = 4108427) B4108427
theorem B2739041 : Blo 1215425 2739041 := bstep (se 2 (by rfl) ⟨1027140, by rfl⟩ : syracuseStep 2739041 = 2054281) B2054281
theorem B3894313 : Blo 1215425 3894313 := bstep (se 2 (by rfl) ⟨1460367, by rfl⟩ : syracuseStep 3894313 = 2920735) B2920735
theorem B1215579 : Blo 1215425 1215579 := bstep (se 1 (by rfl) ⟨911684, by rfl⟩ : syracuseStep 1215579 = 1823369) B1823369
theorem B1215719 : Blo 1215425 1215719 := bstep (se 1 (by rfl) ⟨911789, by rfl⟩ : syracuseStep 1215719 = 1823579) B1823579
theorem B17526253 : Blo 1215425 17526253 := bstep (se 3 (by rfl) ⟨3286172, by rfl⟩ : syracuseStep 17526253 = 6572345) B6572345
theorem B1216027 : Blo 1215425 1216027 := bstep (se 1 (by rfl) ⟨912020, by rfl⟩ : syracuseStep 1216027 = 1824041) B1824041
theorem B1216159 : Blo 1215425 1216159 := bstep (se 1 (by rfl) ⟨912119, by rfl⟩ : syracuseStep 1216159 = 1824239) B1824239
theorem B13324175 : Blo 1215425 13324175 := bstep (se 1 (by rfl) ⟨9993131, by rfl⟩ : syracuseStep 13324175 = 19986263) B19986263
theorem B1216423 : Blo 1215425 1216423 := bstep (se 1 (by rfl) ⟨912317, by rfl⟩ : syracuseStep 1216423 = 1824635) B1824635
theorem B1216447 : Blo 1215425 1216447 := bstep (se 1 (by rfl) ⟨912335, by rfl⟩ : syracuseStep 1216447 = 1824671) B1824671
theorem B12480475 : Blo 1215425 12480475 := bstep (se 1 (by rfl) ⟨9360356, by rfl⟩ : syracuseStep 12480475 = 18720713) B18720713
theorem B4386811 : Blo 1215425 4386811 := bstep (se 1 (by rfl) ⟨3290108, by rfl⟩ : syracuseStep 4386811 = 6580217) B6580217
theorem B11694131 : Blo 1215425 11694131 := bstep (se 1 (by rfl) ⟨8770598, by rfl⟩ : syracuseStep 11694131 = 17541197) B17541197
theorem B1216603 : Blo 1215425 1216603 := bstep (se 1 (by rfl) ⟨912452, by rfl⟩ : syracuseStep 1216603 = 1824905) B1824905
theorem B101175389 : Blo 1215425 101175389 := bstep (se 3 (by rfl) ⟨18970385, by rfl⟩ : syracuseStep 101175389 = 37940771) B37940771
theorem B1216703 : Blo 1215425 1216703 := bstep (se 1 (by rfl) ⟨912527, by rfl⟩ : syracuseStep 1216703 = 1825055) B1825055
theorem B2773223 : Blo 1215425 2773223 := bstep (se 1 (by rfl) ⟨2079917, by rfl⟩ : syracuseStep 2773223 = 4159835) B4159835
theorem B4108751 : Blo 1215425 4108751 := bstep (se 1 (by rfl) ⟨3081563, by rfl⟩ : syracuseStep 4108751 = 6163127) B6163127
theorem B2052587 : Blo 1215425 2052587 := bstep (se 1 (by rfl) ⟨1539440, by rfl⟩ : syracuseStep 2052587 = 3078881) B3078881
theorem B1217071 : Blo 1215425 1217071 := bstep (se 1 (by rfl) ⟨912803, by rfl⟩ : syracuseStep 1217071 = 1825607) B1825607
theorem B1823687 : Blo 1215425 1823687 := bstep (se 1 (by rfl) ⟨1367765, by rfl⟩ : syracuseStep 1823687 = 2735531) B2735531
theorem B1823711 : Blo 1215425 1823711 := bstep (se 1 (by rfl) ⟨1367783, by rfl⟩ : syracuseStep 1823711 = 2735567) B2735567
theorem B2921465 : Blo 1215425 2921465 := bstep (se 2 (by rfl) ⟨1095549, by rfl⟩ : syracuseStep 2921465 = 2191099) B2191099
theorem B13161469 : Blo 1215425 13161469 := bstep (se 3 (by rfl) ⟨2467775, by rfl⟩ : syracuseStep 13161469 = 4935551) B4935551
theorem B3290195 : Blo 1215425 3290195 := bstep (se 1 (by rfl) ⟨2467646, by rfl⟩ : syracuseStep 3290195 = 4935293) B4935293
theorem B5846201 : Blo 1215425 5846201 := bstep (se 2 (by rfl) ⟨2192325, by rfl⟩ : syracuseStep 5846201 = 4384651) B4384651
theorem B2053343 : Blo 1215425 2053343 := bstep (se 1 (by rfl) ⟨1540007, by rfl⟩ : syracuseStep 2053343 = 3080015) B3080015
theorem B1824047 : Blo 1215425 1824047 := bstep (se 1 (by rfl) ⟨1368035, by rfl⟩ : syracuseStep 1824047 = 2736071) B2736071
theorem B3331579 : Blo 1215425 3331579 := bstep (se 1 (by rfl) ⟨2498684, by rfl⟩ : syracuseStep 3331579 = 4997369) B4997369
theorem B1824251 : Blo 1215425 1824251 := bstep (se 1 (by rfl) ⟨1368188, by rfl⟩ : syracuseStep 1824251 = 2736377) B2736377
theorem B31151627 : Blo 1215425 31151627 := bstep (se 1 (by rfl) ⟨23363720, by rfl⟩ : syracuseStep 31151627 = 46727441) B46727441
theorem B1824287 : Blo 1215425 1824287 := bstep (se 1 (by rfl) ⟨1368215, by rfl⟩ : syracuseStep 1824287 = 2736431) B2736431
theorem B7788113 : Blo 1215425 7788113 := bstep (se 2 (by rfl) ⟨2920542, by rfl⟩ : syracuseStep 7788113 = 5841085) B5841085
theorem B2053775 : Blo 1215425 2053775 := bstep (se 1 (by rfl) ⟨1540331, by rfl⟩ : syracuseStep 2053775 = 3080663) B3080663
theorem B1824425 : Blo 1215425 1824425 := bstep (se 2 (by rfl) ⟨684159, by rfl⟩ : syracuseStep 1824425 = 1368319) B1368319
theorem B1824431 : Blo 1215425 1824431 := bstep (se 1 (by rfl) ⟨1368323, by rfl⟩ : syracuseStep 1824431 = 2736647) B2736647
theorem B19723985 : Blo 1215425 19723985 := bstep (se 2 (by rfl) ⟨7396494, by rfl⟩ : syracuseStep 19723985 = 14792989) B14792989
theorem B7403231 : Blo 1215425 7403231 := bstep (se 1 (by rfl) ⟨5552423, by rfl⟩ : syracuseStep 7403231 = 11104847) B11104847
theorem B1824551 : Blo 1215425 1824551 := bstep (se 1 (by rfl) ⟨1368413, by rfl⟩ : syracuseStep 1824551 = 2736827) B2736827
theorem B3077959 : Blo 1215425 3077959 := bstep (se 1 (by rfl) ⟨2308469, by rfl⟩ : syracuseStep 3077959 = 4616939) B4616939
theorem B4929439 : Blo 1215425 4929439 := bstep (se 1 (by rfl) ⟨3697079, by rfl⟩ : syracuseStep 4929439 = 7394159) B7394159
theorem B19732481 : Blo 1215425 19732481 := bstep (se 2 (by rfl) ⟨7399680, by rfl⟩ : syracuseStep 19732481 = 14799361) B14799361
theorem B1824809 : Blo 1215425 1824809 := bstep (se 2 (by rfl) ⟨684303, by rfl⟩ : syracuseStep 1824809 = 1368607) B1368607
theorem B1824839 : Blo 1215425 1824839 := bstep (se 1 (by rfl) ⟨1368629, by rfl⟩ : syracuseStep 1824839 = 2737259) B2737259
theorem B3078283 : Blo 1215425 3078283 := bstep (se 1 (by rfl) ⟨2308712, by rfl⟩ : syracuseStep 3078283 = 4617425) B4617425
theorem B26286443 : Blo 1215425 26286443 := bstep (se 1 (by rfl) ⟨19714832, by rfl⟩ : syracuseStep 26286443 = 39429665) B39429665
theorem B1825151 : Blo 1215425 1825151 := bstep (se 1 (by rfl) ⟨1368863, by rfl⟩ : syracuseStep 1825151 = 2737727) B2737727
theorem B3078587 : Blo 1215425 3078587 := bstep (se 1 (by rfl) ⟨2308940, by rfl⟩ : syracuseStep 3078587 = 4617881) B4617881
theorem B1825223 : Blo 1215425 1825223 := bstep (se 1 (by rfl) ⟨1368917, by rfl⟩ : syracuseStep 1825223 = 2737835) B2737835
theorem B4159993 : Blo 1215425 4159993 := bstep (se 2 (by rfl) ⟨1559997, by rfl⟩ : syracuseStep 4159993 = 3119995) B3119995
theorem B8772239 : Blo 1215425 8772239 := bstep (se 1 (by rfl) ⟨6579179, by rfl⟩ : syracuseStep 8772239 = 13158359) B13158359
theorem B1825439 : Blo 1215425 1825439 := bstep (se 1 (by rfl) ⟨1369079, by rfl⟩ : syracuseStep 1825439 = 2738159) B2738159
theorem B1825583 : Blo 1215425 1825583 := bstep (se 1 (by rfl) ⟨1369187, by rfl⟩ : syracuseStep 1825583 = 2738375) B2738375
theorem B1825673 : Blo 1215425 1825673 := bstep (se 2 (by rfl) ⟨684627, by rfl⟩ : syracuseStep 1825673 = 1369255) B1369255
theorem B1825703 : Blo 1215425 1825703 := bstep (se 1 (by rfl) ⟨1369277, by rfl⟩ : syracuseStep 1825703 = 2738555) B2738555
theorem B7789547 : Blo 1215425 7789547 := bstep (se 1 (by rfl) ⟨5842160, by rfl⟩ : syracuseStep 7789547 = 11684321) B11684321
theorem B1825883 : Blo 1215425 1825883 := bstep (se 1 (by rfl) ⟨1369412, by rfl⟩ : syracuseStep 1825883 = 2738825) B2738825
theorem B3464299 : Blo 1215425 3464299 := bstep (se 1 (by rfl) ⟨2598224, by rfl⟩ : syracuseStep 3464299 = 5196449) B5196449
theorem B2735225 : Blo 1215425 2735225 := bstep (se 2 (by rfl) ⟨1025709, by rfl⟩ : syracuseStep 2735225 = 2051419) B2051419
theorem B5848199 : Blo 1215425 5848199 := bstep (se 1 (by rfl) ⟨4386149, by rfl⟩ : syracuseStep 5848199 = 8772299) B8772299
theorem B4381883 : Blo 1215425 4381883 := bstep (se 1 (by rfl) ⟨3286412, by rfl⟩ : syracuseStep 4381883 = 6572825) B6572825
theorem B3898567 : Blo 1215425 3898567 := bstep (se 1 (by rfl) ⟨2923925, by rfl⟩ : syracuseStep 3898567 = 5847851) B5847851
theorem B1826075 : Blo 1215425 1826075 := bstep (se 1 (by rfl) ⟨1369556, by rfl⟩ : syracuseStep 1826075 = 2739113) B2739113
theorem B3333467 : Blo 1215425 3333467 := bstep (se 1 (by rfl) ⟨2500100, by rfl⟩ : syracuseStep 3333467 = 5000201) B5000201
theorem B6159725 : Blo 1215425 6159725 := bstep (se 3 (by rfl) ⟨1154948, by rfl⟩ : syracuseStep 6159725 = 2309897) B2309897
theorem B2596303 : Blo 1215425 2596303 := bstep (se 1 (by rfl) ⟨1947227, by rfl⟩ : syracuseStep 2596303 = 3894455) B3894455
theorem B3079903 : Blo 1215425 3079903 := bstep (se 1 (by rfl) ⟨2309927, by rfl⟩ : syracuseStep 3079903 = 4619855) B4619855
theorem B5840855 : Blo 1215425 5840855 := bstep (se 1 (by rfl) ⟨4380641, by rfl⟩ : syracuseStep 5840855 = 8761283) B8761283
theorem B2736287 : Blo 1215425 2736287 := bstep (se 1 (by rfl) ⟨2052215, by rfl⟩ : syracuseStep 2736287 = 4104431) B4104431
theorem B4104377 : Blo 1215425 4104377 := bstep (se 2 (by rfl) ⟨1539141, by rfl⟩ : syracuseStep 4104377 = 3078283) B3078283
theorem B1368391 : Blo 1215425 1368391 := bstep (se 1 (by rfl) ⟨1026293, by rfl⟩ : syracuseStep 1368391 = 2052587) B2052587
theorem B3080551 : Blo 1215425 3080551 := bstep (se 1 (by rfl) ⟨2310413, by rfl⟩ : syracuseStep 3080551 = 4620827) B4620827
theorem B2736539 : Blo 1215425 2736539 := bstep (se 1 (by rfl) ⟨2052404, by rfl⟩ : syracuseStep 2736539 = 4104809) B4104809
theorem B23380487 : Blo 1215425 23380487 := bstep (se 1 (by rfl) ⟨17535365, by rfl⟩ : syracuseStep 23380487 = 35070731) B35070731
theorem B5546657 : Blo 1215425 5546657 := bstep (se 2 (by rfl) ⟨2079996, by rfl⟩ : syracuseStep 5546657 = 4159993) B4159993
theorem B6161183 : Blo 1215425 6161183 := bstep (se 1 (by rfl) ⟨4620887, by rfl⟩ : syracuseStep 6161183 = 9241775) B9241775
theorem B16646975 : Blo 1215425 16646975 := bstep (se 1 (by rfl) ⟨12485231, by rfl⟩ : syracuseStep 16646975 = 24970463) B24970463
theorem B1368895 : Blo 1215425 1368895 := bstep (se 1 (by rfl) ⟨1026671, by rfl⟩ : syracuseStep 1368895 = 2053343) B2053343
theorem B20767751 : Blo 1215425 20767751 := bstep (se 1 (by rfl) ⟨15575813, by rfl⟩ : syracuseStep 20767751 = 31151627) B31151627
theorem B1369183 : Blo 1215425 1369183 := bstep (se 1 (by rfl) ⟨1026887, by rfl⟩ : syracuseStep 1369183 = 2053775) B2053775
theorem B13149323 : Blo 1215425 13149323 := bstep (se 1 (by rfl) ⟨9861992, by rfl⟩ : syracuseStep 13149323 = 19723985) B19723985
theorem B5195015 : Blo 1215425 5195015 := bstep (se 1 (by rfl) ⟨3896261, by rfl⟩ : syracuseStep 5195015 = 7792523) B7792523
theorem B17548625 : Blo 1215425 17548625 := bstep (se 2 (by rfl) ⟨6580734, by rfl⟩ : syracuseStep 17548625 = 13161469) B13161469
theorem B6161831 : Blo 1215425 6161831 := bstep (se 1 (by rfl) ⟨4621373, by rfl⟩ : syracuseStep 6161831 = 9242747) B9242747
theorem B17524295 : Blo 1215425 17524295 := bstep (se 1 (by rfl) ⟨13143221, by rfl⟩ : syracuseStep 17524295 = 26286443) B26286443
theorem B1754779 : Blo 1215425 1754779 := bstep (se 1 (by rfl) ⟨1316084, by rfl⟩ : syracuseStep 1754779 = 2632169) B2632169
theorem B6571739 : Blo 1215425 6571739 := bstep (se 1 (by rfl) ⟨4928804, by rfl⟩ : syracuseStep 6571739 = 9857609) B9857609
theorem B4442105 : Blo 1215425 4442105 := bstep (se 2 (by rfl) ⟨1665789, by rfl⟩ : syracuseStep 4442105 = 3331579) B3331579
theorem B2222311 : Blo 1215425 2222311 := bstep (se 1 (by rfl) ⟨1666733, by rfl⟩ : syracuseStep 2222311 = 3333467) B3333467
theorem B4106483 : Blo 1215425 4106483 := bstep (se 1 (by rfl) ⟨3079862, by rfl⟩ : syracuseStep 4106483 = 6159725) B6159725
theorem B4106537 : Blo 1215425 4106537 := bstep (se 2 (by rfl) ⟨1539951, by rfl⟩ : syracuseStep 4106537 = 3079903) B3079903
theorem B5849081 : Blo 1215425 5849081 := bstep (se 2 (by rfl) ⟨2193405, by rfl⟩ : syracuseStep 5849081 = 4386811) B4386811
theorem B6572585 : Blo 1215425 6572585 := bstep (se 2 (by rfl) ⟨2464719, by rfl⟩ : syracuseStep 6572585 = 4929439) B4929439
theorem B8882783 : Blo 1215425 8882783 := bstep (se 1 (by rfl) ⟨6662087, by rfl⟩ : syracuseStep 8882783 = 13324175) B13324175
theorem B16640633 : Blo 1215425 16640633 := bstep (se 2 (by rfl) ⟨6240237, by rfl⟩ : syracuseStep 16640633 = 12480475) B12480475
theorem B3893903 : Blo 1215425 3893903 := bstep (se 1 (by rfl) ⟨2920427, by rfl⟩ : syracuseStep 3893903 = 5840855) B5840855
theorem B14035913 : Blo 1215425 14035913 := bstep (se 2 (by rfl) ⟨5263467, by rfl⟩ : syracuseStep 14035913 = 10526935) B10526935
theorem B2739167 : Blo 1215425 2739167 := bstep (se 1 (by rfl) ⟨2054375, by rfl⟩ : syracuseStep 2739167 = 4108751) B4108751
theorem B4615163 : Blo 1215425 4615163 := bstep (se 1 (by rfl) ⟨3461372, by rfl⟩ : syracuseStep 4615163 = 6922745) B6922745
theorem B1215791 : Blo 1215425 1215791 := bstep (se 1 (by rfl) ⟨911843, by rfl⟩ : syracuseStep 1215791 = 1823687) B1823687
theorem B1215807 : Blo 1215425 1215807 := bstep (se 1 (by rfl) ⟨911855, by rfl⟩ : syracuseStep 1215807 = 1823711) B1823711
theorem B1216031 : Blo 1215425 1216031 := bstep (se 1 (by rfl) ⟨912023, by rfl⟩ : syracuseStep 1216031 = 1824047) B1824047
theorem B1216167 : Blo 1215425 1216167 := bstep (se 1 (by rfl) ⟨912125, by rfl⟩ : syracuseStep 1216167 = 1824251) B1824251
theorem B1216191 : Blo 1215425 1216191 := bstep (se 1 (by rfl) ⟨912143, by rfl⟩ : syracuseStep 1216191 = 1824287) B1824287
theorem B1216283 : Blo 1215425 1216283 := bstep (se 1 (by rfl) ⟨912212, by rfl⟩ : syracuseStep 1216283 = 1824425) B1824425
theorem B1216287 : Blo 1215425 1216287 := bstep (se 1 (by rfl) ⟨912215, by rfl⟩ : syracuseStep 1216287 = 1824431) B1824431
theorem B4935487 : Blo 1215425 4935487 := bstep (se 1 (by rfl) ⟨3701615, by rfl⟩ : syracuseStep 4935487 = 7403231) B7403231
theorem B1216367 : Blo 1215425 1216367 := bstep (se 1 (by rfl) ⟨912275, by rfl⟩ : syracuseStep 1216367 = 1824551) B1824551
theorem B1216539 : Blo 1215425 1216539 := bstep (se 1 (by rfl) ⟨912404, by rfl⟩ : syracuseStep 1216539 = 1824809) B1824809
theorem B1216559 : Blo 1215425 1216559 := bstep (se 1 (by rfl) ⟨912419, by rfl⟩ : syracuseStep 1216559 = 1824839) B1824839
theorem B1216767 : Blo 1215425 1216767 := bstep (se 1 (by rfl) ⟨912575, by rfl⟩ : syracuseStep 1216767 = 1825151) B1825151
theorem B5198089 : Blo 1215425 5198089 := bstep (se 2 (by rfl) ⟨1949283, by rfl⟩ : syracuseStep 5198089 = 3898567) B3898567
theorem B2052391 : Blo 1215425 2052391 := bstep (se 1 (by rfl) ⟨1539293, by rfl⟩ : syracuseStep 2052391 = 3078587) B3078587
theorem B1216815 : Blo 1215425 1216815 := bstep (se 1 (by rfl) ⟨912611, by rfl⟩ : syracuseStep 1216815 = 1825223) B1825223
theorem B4387259 : Blo 1215425 4387259 := bstep (se 1 (by rfl) ⟨3290444, by rfl⟩ : syracuseStep 4387259 = 6580889) B6580889
theorem B1216959 : Blo 1215425 1216959 := bstep (se 1 (by rfl) ⟨912719, by rfl⟩ : syracuseStep 1216959 = 1825439) B1825439
theorem B1217055 : Blo 1215425 1217055 := bstep (se 1 (by rfl) ⟨912791, by rfl⟩ : syracuseStep 1217055 = 1825583) B1825583
theorem B1217115 : Blo 1215425 1217115 := bstep (se 1 (by rfl) ⟨912836, by rfl⟩ : syracuseStep 1217115 = 1825673) B1825673
theorem B3461737 : Blo 1215425 3461737 := bstep (se 2 (by rfl) ⟨1298151, by rfl⟩ : syracuseStep 3461737 = 2596303) B2596303
theorem B1217135 : Blo 1215425 1217135 := bstep (se 1 (by rfl) ⟨912851, by rfl⟩ : syracuseStep 1217135 = 1825703) B1825703
theorem B23368337 : Blo 1215425 23368337 := bstep (se 2 (by rfl) ⟨8763126, by rfl⟩ : syracuseStep 23368337 = 17526253) B17526253
theorem B1217255 : Blo 1215425 1217255 := bstep (se 1 (by rfl) ⟨912941, by rfl⟩ : syracuseStep 1217255 = 1825883) B1825883
theorem B1823483 : Blo 1215425 1823483 := bstep (se 1 (by rfl) ⟨1367612, by rfl⟩ : syracuseStep 1823483 = 2735225) B2735225
theorem B2921255 : Blo 1215425 2921255 := bstep (se 1 (by rfl) ⟨2190941, by rfl⟩ : syracuseStep 2921255 = 4381883) B4381883
theorem B1217383 : Blo 1215425 1217383 := bstep (se 1 (by rfl) ⟨913037, by rfl⟩ : syracuseStep 1217383 = 1826075) B1826075
theorem B20772125 : Blo 1215425 20772125 := bstep (se 3 (by rfl) ⟨3894773, by rfl⟩ : syracuseStep 20772125 = 7789547) B7789547
theorem B7796087 : Blo 1215425 7796087 := bstep (se 1 (by rfl) ⟨5847065, by rfl⟩ : syracuseStep 7796087 = 11694131) B11694131
theorem B67450259 : Blo 1215425 67450259 := bstep (se 1 (by rfl) ⟨50587694, by rfl⟩ : syracuseStep 67450259 = 101175389) B101175389
theorem B1848815 : Blo 1215425 1848815 := bstep (se 1 (by rfl) ⟨1386611, by rfl⟩ : syracuseStep 1848815 = 2773223) B2773223
theorem B6927869 : Blo 1215425 6927869 := bstep (se 3 (by rfl) ⟨1298975, by rfl⟩ : syracuseStep 6927869 = 2597951) B2597951
theorem B18732779 : Blo 1215425 18732779 := bstep (se 1 (by rfl) ⟨14049584, by rfl⟩ : syracuseStep 18732779 = 28099169) B28099169
theorem B35067725 : Blo 1215425 35067725 := bstep (se 3 (by rfl) ⟨6575198, by rfl⟩ : syracuseStep 35067725 = 13150397) B13150397
theorem B2193463 : Blo 1215425 2193463 := bstep (se 1 (by rfl) ⟨1645097, by rfl⟩ : syracuseStep 2193463 = 3290195) B3290195
theorem B3897467 : Blo 1215425 3897467 := bstep (se 1 (by rfl) ⟨2923100, by rfl⟩ : syracuseStep 3897467 = 5846201) B5846201
theorem B1825007 : Blo 1215425 1825007 := bstep (se 1 (by rfl) ⟨1368755, by rfl⟩ : syracuseStep 1825007 = 2737511) B2737511
theorem B1825079 : Blo 1215425 1825079 := bstep (se 1 (by rfl) ⟨1368809, by rfl⟩ : syracuseStep 1825079 = 2737619) B2737619
theorem B5192075 : Blo 1215425 5192075 := bstep (se 1 (by rfl) ⟨3894056, by rfl⟩ : syracuseStep 5192075 = 7788113) B7788113
theorem B1825259 : Blo 1215425 1825259 := bstep (se 1 (by rfl) ⟨1368944, by rfl⟩ : syracuseStep 1825259 = 2737889) B2737889
theorem B13154987 : Blo 1215425 13154987 := bstep (se 1 (by rfl) ⟨9866240, by rfl⟩ : syracuseStep 13154987 = 19732481) B19732481
theorem B5192417 : Blo 1215425 5192417 := bstep (se 2 (by rfl) ⟨1947156, by rfl⟩ : syracuseStep 5192417 = 3894313) B3894313
theorem B4381451 : Blo 1215425 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B4619065 : Blo 1215425 4619065 := bstep (se 2 (by rfl) ⟨1732149, by rfl⟩ : syracuseStep 4619065 = 3464299) B3464299
theorem B2284409 : Blo 1215425 2284409 := bstep (se 2 (by rfl) ⟨856653, by rfl⟩ : syracuseStep 2284409 = 1713307) B1713307
theorem B1825787 : Blo 1215425 1825787 := bstep (se 1 (by rfl) ⟨1369340, by rfl⟩ : syracuseStep 1825787 = 2738681) B2738681
theorem B1825847 : Blo 1215425 1825847 := bstep (se 1 (by rfl) ⟨1369385, by rfl⟩ : syracuseStep 1825847 = 2738771) B2738771
theorem B5848159 : Blo 1215425 5848159 := bstep (se 1 (by rfl) ⟨4386119, by rfl⟩ : syracuseStep 5848159 = 8772239) B8772239
theorem B1825967 : Blo 1215425 1825967 := bstep (se 1 (by rfl) ⟨1369475, by rfl⟩ : syracuseStep 1825967 = 2738951) B2738951
theorem B1826027 : Blo 1215425 1826027 := bstep (se 1 (by rfl) ⟨1369520, by rfl⟩ : syracuseStep 1826027 = 2739041) B2739041
theorem B3898799 : Blo 1215425 3898799 := bstep (se 1 (by rfl) ⟨2924099, by rfl⟩ : syracuseStep 3898799 = 5848199) B5848199
theorem B4103945 : Blo 1215425 4103945 := bstep (se 2 (by rfl) ⟨1538979, by rfl⟩ : syracuseStep 4103945 = 3077959) B3077959
theorem B7790573 : Blo 1215425 7790573 := bstep (se 3 (by rfl) ⟨1460732, by rfl⟩ : syracuseStep 7790573 = 2921465) B2921465
theorem B2736251 : Blo 1215425 2736251 := bstep (se 1 (by rfl) ⟨2052188, by rfl⟩ : syracuseStep 2736251 = 4104377) B4104377
theorem B11698469 : Blo 1215425 11698469 := bstep (se 4 (by rfl) ⟨1096731, by rfl⟩ : syracuseStep 11698469 = 2193463) B2193463
theorem B2924839 : Blo 1215425 2924839 := bstep (se 1 (by rfl) ⟨2193629, by rfl⟩ : syracuseStep 2924839 = 4387259) B4387259
theorem B6930785 : Blo 1215425 6930785 := bstep (se 2 (by rfl) ⟨2599044, by rfl⟩ : syracuseStep 6930785 = 5198089) B5198089
theorem B2736521 : Blo 1215425 2736521 := bstep (se 2 (by rfl) ⟨1026195, by rfl⟩ : syracuseStep 2736521 = 2052391) B2052391
theorem B13845167 : Blo 1215425 13845167 := bstep (se 1 (by rfl) ⟨10383875, by rfl⟩ : syracuseStep 13845167 = 20767751) B20767751
theorem B8766215 : Blo 1215425 8766215 := bstep (se 1 (by rfl) ⟨6574661, by rfl⟩ : syracuseStep 8766215 = 13149323) B13149323
theorem B11699083 : Blo 1215425 11699083 := bstep (se 1 (by rfl) ⟨8774312, by rfl⟩ : syracuseStep 11699083 = 17548625) B17548625
theorem B44966839 : Blo 1215425 44966839 := bstep (se 1 (by rfl) ⟨33725129, by rfl⟩ : syracuseStep 44966839 = 67450259) B67450259
theorem B11682863 : Blo 1215425 11682863 := bstep (se 1 (by rfl) ⟨8762147, by rfl⟩ : syracuseStep 11682863 = 17524295) B17524295
theorem B2598311 : Blo 1215425 2598311 := bstep (se 1 (by rfl) ⟨1948733, by rfl⟩ : syracuseStep 2598311 = 3897467) B3897467
theorem B2737655 : Blo 1215425 2737655 := bstep (se 1 (by rfl) ⟨2053241, by rfl⟩ : syracuseStep 2737655 = 4106483) B4106483
theorem B2737691 : Blo 1215425 2737691 := bstep (se 1 (by rfl) ⟨2053268, by rfl⟩ : syracuseStep 2737691 = 4106537) B4106537
theorem B11093755 : Blo 1215425 11093755 := bstep (se 1 (by rfl) ⟨8320316, by rfl⟩ : syracuseStep 11093755 = 16640633) B16640633
theorem B17524637 : Blo 1215425 17524637 := bstep (se 3 (by rfl) ⟨3285869, by rfl⟩ : syracuseStep 17524637 = 6571739) B6571739
theorem B9357275 : Blo 1215425 9357275 := bstep (se 1 (by rfl) ⟨7017956, by rfl⟩ : syracuseStep 9357275 = 14035913) B14035913
theorem B2599199 : Blo 1215425 2599199 := bstep (se 1 (by rfl) ⟨1949399, by rfl⟩ : syracuseStep 2599199 = 3898799) B3898799
theorem B6580649 : Blo 1215425 6580649 := bstep (se 2 (by rfl) ⟨2467743, by rfl⟩ : syracuseStep 6580649 = 4935487) B4935487
theorem B4107401 : Blo 1215425 4107401 := bstep (se 2 (by rfl) ⟨1540275, by rfl⟩ : syracuseStep 4107401 = 3080551) B3080551
theorem B1215655 : Blo 1215425 1215655 := bstep (se 1 (by rfl) ⟨911741, by rfl⟩ : syracuseStep 1215655 = 1823483) B1823483
theorem B4107455 : Blo 1215425 4107455 := bstep (se 1 (by rfl) ⟨3080591, by rfl⟩ : syracuseStep 4107455 = 6161183) B6161183
theorem B4615649 : Blo 1215425 4615649 := bstep (se 2 (by rfl) ⟨1730868, by rfl⟩ : syracuseStep 4615649 = 3461737) B3461737
theorem B13848083 : Blo 1215425 13848083 := bstep (se 1 (by rfl) ⟨10386062, by rfl⟩ : syracuseStep 13848083 = 20772125) B20772125
theorem B5197391 : Blo 1215425 5197391 := bstep (se 1 (by rfl) ⟨3898043, by rfl⟩ : syracuseStep 5197391 = 7796087) B7796087
theorem B4107887 : Blo 1215425 4107887 := bstep (se 1 (by rfl) ⟨3080915, by rfl⟩ : syracuseStep 4107887 = 6161831) B6161831
theorem B1232543 : Blo 1215425 1232543 := bstep (se 1 (by rfl) ⟨924407, by rfl⟩ : syracuseStep 1232543 = 1848815) B1848815
theorem B12488519 : Blo 1215425 12488519 := bstep (se 1 (by rfl) ⟨9366389, by rfl⟩ : syracuseStep 12488519 = 18732779) B18732779
theorem B2961403 : Blo 1215425 2961403 := bstep (se 1 (by rfl) ⟨2221052, by rfl⟩ : syracuseStep 2961403 = 4442105) B4442105
theorem B1216671 : Blo 1215425 1216671 := bstep (se 1 (by rfl) ⟨912503, by rfl⟩ : syracuseStep 1216671 = 1825007) B1825007
theorem B1216719 : Blo 1215425 1216719 := bstep (se 1 (by rfl) ⟨912539, by rfl⟩ : syracuseStep 1216719 = 1825079) B1825079
theorem B3461383 : Blo 1215425 3461383 := bstep (se 1 (by rfl) ⟨2596037, by rfl⟩ : syracuseStep 3461383 = 5192075) B5192075
theorem B1216839 : Blo 1215425 1216839 := bstep (se 1 (by rfl) ⟨912629, by rfl⟩ : syracuseStep 1216839 = 1825259) B1825259
theorem B14791085 : Blo 1215425 14791085 := bstep (se 3 (by rfl) ⟨2773328, by rfl⟩ : syracuseStep 14791085 = 5546657) B5546657
theorem B8769991 : Blo 1215425 8769991 := bstep (se 1 (by rfl) ⟨6577493, by rfl⟩ : syracuseStep 8769991 = 13154987) B13154987
theorem B3461611 : Blo 1215425 3461611 := bstep (se 1 (by rfl) ⟨2596208, by rfl⟩ : syracuseStep 3461611 = 5192417) B5192417
theorem B2920967 : Blo 1215425 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B3076775 : Blo 1215425 3076775 := bstep (se 1 (by rfl) ⟨2307581, by rfl⟩ : syracuseStep 3076775 = 4615163) B4615163
theorem B1217191 : Blo 1215425 1217191 := bstep (se 1 (by rfl) ⟨912893, by rfl⟩ : syracuseStep 1217191 = 1825787) B1825787
theorem B1217231 : Blo 1215425 1217231 := bstep (se 1 (by rfl) ⟨912923, by rfl⟩ : syracuseStep 1217231 = 1825847) B1825847
theorem B1217311 : Blo 1215425 1217311 := bstep (se 1 (by rfl) ⟨912983, by rfl⟩ : syracuseStep 1217311 = 1825967) B1825967
theorem B1217351 : Blo 1215425 1217351 := bstep (se 1 (by rfl) ⟨913013, by rfl⟩ : syracuseStep 1217351 = 1826027) B1826027
theorem B2339705 : Blo 1215425 2339705 := bstep (se 2 (by rfl) ⟨877389, by rfl⟩ : syracuseStep 2339705 = 1754779) B1754779
theorem B6091757 : Blo 1215425 6091757 := bstep (se 3 (by rfl) ⟨1142204, by rfl⟩ : syracuseStep 6091757 = 2284409) B2284409
theorem B1824191 : Blo 1215425 1824191 := bstep (se 1 (by rfl) ⟨1368143, by rfl⟩ : syracuseStep 1824191 = 2736287) B2736287
theorem B1824359 : Blo 1215425 1824359 := bstep (se 1 (by rfl) ⟨1368269, by rfl⟩ : syracuseStep 1824359 = 2736539) B2736539
theorem B2963081 : Blo 1215425 2963081 := bstep (se 2 (by rfl) ⟨1111155, by rfl⟩ : syracuseStep 2963081 = 2222311) B2222311
theorem B15586991 : Blo 1215425 15586991 := bstep (se 1 (by rfl) ⟨11690243, by rfl⟩ : syracuseStep 15586991 = 23380487) B23380487
theorem B1824521 : Blo 1215425 1824521 := bstep (se 2 (by rfl) ⟨684195, by rfl⟩ : syracuseStep 1824521 = 1368391) B1368391
theorem B15578891 : Blo 1215425 15578891 := bstep (se 1 (by rfl) ⟨11684168, by rfl⟩ : syracuseStep 15578891 = 23368337) B23368337
theorem B1947503 : Blo 1215425 1947503 := bstep (se 1 (by rfl) ⟨1460627, by rfl⟩ : syracuseStep 1947503 = 2921255) B2921255
theorem B11097983 : Blo 1215425 11097983 := bstep (se 1 (by rfl) ⟨8323487, by rfl⟩ : syracuseStep 11097983 = 16646975) B16646975
theorem B3463343 : Blo 1215425 3463343 := bstep (se 1 (by rfl) ⟨2597507, by rfl⟩ : syracuseStep 3463343 = 5195015) B5195015
theorem B4618579 : Blo 1215425 4618579 := bstep (se 1 (by rfl) ⟨3463934, by rfl⟩ : syracuseStep 4618579 = 6927869) B6927869
theorem B6158753 : Blo 1215425 6158753 := bstep (se 2 (by rfl) ⟨2309532, by rfl⟩ : syracuseStep 6158753 = 4619065) B4619065
theorem B1825193 : Blo 1215425 1825193 := bstep (se 2 (by rfl) ⟨684447, by rfl⟩ : syracuseStep 1825193 = 1368895) B1368895
theorem B23378483 : Blo 1215425 23378483 := bstep (se 1 (by rfl) ⟨17533862, by rfl⟩ : syracuseStep 23378483 = 35067725) B35067725
theorem B7797545 : Blo 1215425 7797545 := bstep (se 2 (by rfl) ⟨2924079, by rfl⟩ : syracuseStep 7797545 = 5848159) B5848159
theorem B1825577 : Blo 1215425 1825577 := bstep (se 2 (by rfl) ⟨684591, by rfl⟩ : syracuseStep 1825577 = 1369183) B1369183
theorem B3899387 : Blo 1215425 3899387 := bstep (se 1 (by rfl) ⟨2924540, by rfl⟩ : syracuseStep 3899387 = 5849081) B5849081
theorem B4381723 : Blo 1215425 4381723 := bstep (se 1 (by rfl) ⟨3286292, by rfl⟩ : syracuseStep 4381723 = 6572585) B6572585
theorem B5921855 : Blo 1215425 5921855 := bstep (se 1 (by rfl) ⟨4441391, by rfl⟩ : syracuseStep 5921855 = 8882783) B8882783
theorem B2595935 : Blo 1215425 2595935 := bstep (se 1 (by rfl) ⟨1946951, by rfl⟩ : syracuseStep 2595935 = 3893903) B3893903
theorem B1826111 : Blo 1215425 1826111 := bstep (se 1 (by rfl) ⟨1369583, by rfl⟩ : syracuseStep 1826111 = 2739167) B2739167
theorem B2735963 : Blo 1215425 2735963 := bstep (se 1 (by rfl) ⟨2051972, by rfl⟩ : syracuseStep 2735963 = 4103945) B4103945
theorem B5193715 : Blo 1215425 5193715 := bstep (se 1 (by rfl) ⟨3895286, by rfl⟩ : syracuseStep 5193715 = 7790573) B7790573
theorem B7798979 : Blo 1215425 7798979 := bstep (se 1 (by rfl) ⟨5849234, by rfl⟩ : syracuseStep 7798979 = 11698469) B11698469
theorem B4620523 : Blo 1215425 4620523 := bstep (se 1 (by rfl) ⟨3465392, by rfl⟩ : syracuseStep 4620523 = 6930785) B6930785
theorem B6922493 : Blo 1215425 6922493 := bstep (se 3 (by rfl) ⟨1297967, by rfl⟩ : syracuseStep 6922493 = 2595935) B2595935
theorem B17548397 : Blo 1215425 17548397 := bstep (se 3 (by rfl) ⟨3290324, by rfl⟩ : syracuseStep 17548397 = 6580649) B6580649
theorem B15598777 : Blo 1215425 15598777 := bstep (se 2 (by rfl) ⟨5849541, by rfl⟩ : syracuseStep 15598777 = 11699083) B11699083
theorem B11683091 : Blo 1215425 11683091 := bstep (se 1 (by rfl) ⟨8762318, by rfl⟩ : syracuseStep 11683091 = 17524637) B17524637
theorem B5842297 : Blo 1215425 5842297 := bstep (se 2 (by rfl) ⟨2190861, by rfl⟩ : syracuseStep 5842297 = 4381723) B4381723
theorem B15599141 : Blo 1215425 15599141 := bstep (se 4 (by rfl) ⟨1462419, by rfl⟩ : syracuseStep 15599141 = 2924839) B2924839
theorem B4105835 : Blo 1215425 4105835 := bstep (se 1 (by rfl) ⟨3079376, by rfl⟩ : syracuseStep 4105835 = 6158753) B6158753
theorem B3286781 : Blo 1215425 3286781 := bstep (se 3 (by rfl) ⟨616271, by rfl⟩ : syracuseStep 3286781 = 1232543) B1232543
theorem B2738267 : Blo 1215425 2738267 := bstep (se 1 (by rfl) ⟨2053700, by rfl⟩ : syracuseStep 2738267 = 4107401) B4107401
theorem B2738303 : Blo 1215425 2738303 := bstep (se 1 (by rfl) ⟨2053727, by rfl⟩ : syracuseStep 2738303 = 4107455) B4107455
theorem B2738591 : Blo 1215425 2738591 := bstep (se 1 (by rfl) ⟨2053943, by rfl⟩ : syracuseStep 2738591 = 4107887) B4107887
theorem B8325679 : Blo 1215425 8325679 := bstep (se 1 (by rfl) ⟨6244259, by rfl⟩ : syracuseStep 8325679 = 12488519) B12488519
theorem B6924953 : Blo 1215425 6924953 := bstep (se 2 (by rfl) ⟨2596857, by rfl⟩ : syracuseStep 6924953 = 5193715) B5193715
theorem B10398365 : Blo 1215425 10398365 := bstep (se 3 (by rfl) ⟨1949693, by rfl⟩ : syracuseStep 10398365 = 3899387) B3899387
theorem B4615177 : Blo 1215425 4615177 := bstep (se 2 (by rfl) ⟨1730691, by rfl⟩ : syracuseStep 4615177 = 3461383) B3461383
theorem B2051183 : Blo 1215425 2051183 := bstep (se 1 (by rfl) ⟨1538387, by rfl⟩ : syracuseStep 2051183 = 3076775) B3076775
theorem B5844143 : Blo 1215425 5844143 := bstep (se 1 (by rfl) ⟨4383107, by rfl⟩ : syracuseStep 5844143 = 8766215) B8766215
theorem B11693321 : Blo 1215425 11693321 := bstep (se 2 (by rfl) ⟨4384995, by rfl⟩ : syracuseStep 11693321 = 8769991) B8769991
theorem B4615481 : Blo 1215425 4615481 := bstep (se 2 (by rfl) ⟨1730805, by rfl⟩ : syracuseStep 4615481 = 3461611) B3461611
theorem B1732207 : Blo 1215425 1732207 := bstep (se 1 (by rfl) ⟨1299155, by rfl⟩ : syracuseStep 1732207 = 2598311) B2598311
theorem B1216127 : Blo 1215425 1216127 := bstep (se 1 (by rfl) ⟨912095, by rfl⟩ : syracuseStep 1216127 = 1824191) B1824191
theorem B1216239 : Blo 1215425 1216239 := bstep (se 1 (by rfl) ⟨912179, by rfl⟩ : syracuseStep 1216239 = 1824359) B1824359
theorem B10391327 : Blo 1215425 10391327 := bstep (se 1 (by rfl) ⟨7793495, by rfl⟩ : syracuseStep 10391327 = 15586991) B15586991
theorem B1216347 : Blo 1215425 1216347 := bstep (se 1 (by rfl) ⟨912260, by rfl⟩ : syracuseStep 1216347 = 1824521) B1824521
theorem B6238183 : Blo 1215425 6238183 := bstep (se 1 (by rfl) ⟨4678637, by rfl⟩ : syracuseStep 6238183 = 9357275) B9357275
theorem B1732799 : Blo 1215425 1732799 := bstep (se 1 (by rfl) ⟨1299599, by rfl⟩ : syracuseStep 1732799 = 2599199) B2599199
theorem B1216795 : Blo 1215425 1216795 := bstep (se 1 (by rfl) ⟨912596, by rfl⟩ : syracuseStep 1216795 = 1825193) B1825193
theorem B7901549 : Blo 1215425 7901549 := bstep (se 3 (by rfl) ⟨1481540, by rfl⟩ : syracuseStep 7901549 = 2963081) B2963081
theorem B15585655 : Blo 1215425 15585655 := bstep (se 1 (by rfl) ⟨11689241, by rfl⟩ : syracuseStep 15585655 = 23378483) B23378483
theorem B5198363 : Blo 1215425 5198363 := bstep (se 1 (by rfl) ⟨3898772, by rfl⟩ : syracuseStep 5198363 = 7797545) B7797545
theorem B1217051 : Blo 1215425 1217051 := bstep (se 1 (by rfl) ⟨912788, by rfl⟩ : syracuseStep 1217051 = 1825577) B1825577
theorem B1217407 : Blo 1215425 1217407 := bstep (se 1 (by rfl) ⟨913055, by rfl⟩ : syracuseStep 1217407 = 1826111) B1826111
theorem B3077099 : Blo 1215425 3077099 := bstep (se 1 (by rfl) ⟨2307824, by rfl⟩ : syracuseStep 3077099 = 4615649) B4615649
theorem B6239213 : Blo 1215425 6239213 := bstep (se 3 (by rfl) ⟨1169852, by rfl⟩ : syracuseStep 6239213 = 2339705) B2339705
theorem B14791673 : Blo 1215425 14791673 := bstep (se 2 (by rfl) ⟨5546877, by rfl⟩ : syracuseStep 14791673 = 11093755) B11093755
theorem B29594621 : Blo 1215425 29594621 := bstep (se 3 (by rfl) ⟨5548991, by rfl⟩ : syracuseStep 29594621 = 11097983) B11097983
theorem B1823975 : Blo 1215425 1823975 := bstep (se 1 (by rfl) ⟨1367981, by rfl⟩ : syracuseStep 1823975 = 2735963) B2735963
theorem B1824167 : Blo 1215425 1824167 := bstep (se 1 (by rfl) ⟨1368125, by rfl⟩ : syracuseStep 1824167 = 2736251) B2736251
theorem B1824347 : Blo 1215425 1824347 := bstep (se 1 (by rfl) ⟨1368260, by rfl⟩ : syracuseStep 1824347 = 2736521) B2736521
theorem B9860723 : Blo 1215425 9860723 := bstep (se 1 (by rfl) ⟨7395542, by rfl⟩ : syracuseStep 9860723 = 14791085) B14791085
theorem B1947311 : Blo 1215425 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B6158105 : Blo 1215425 6158105 := bstep (se 2 (by rfl) ⟨2309289, by rfl⟩ : syracuseStep 6158105 = 4618579) B4618579
theorem B9230111 : Blo 1215425 9230111 := bstep (se 1 (by rfl) ⟨6922583, by rfl⟩ : syracuseStep 9230111 = 13845167) B13845167
theorem B4061171 : Blo 1215425 4061171 := bstep (se 1 (by rfl) ⟨3045878, by rfl⟩ : syracuseStep 4061171 = 6091757) B6091757
theorem B7788575 : Blo 1215425 7788575 := bstep (se 1 (by rfl) ⟨5841431, by rfl⟩ : syracuseStep 7788575 = 11682863) B11682863
theorem B1825103 : Blo 1215425 1825103 := bstep (se 1 (by rfl) ⟨1368827, by rfl⟩ : syracuseStep 1825103 = 2737655) B2737655
theorem B1825127 : Blo 1215425 1825127 := bstep (se 1 (by rfl) ⟨1368845, by rfl⟩ : syracuseStep 1825127 = 2737691) B2737691
theorem B10385927 : Blo 1215425 10385927 := bstep (se 1 (by rfl) ⟨7789445, by rfl⟩ : syracuseStep 10385927 = 15578891) B15578891
theorem B59955785 : Blo 1215425 59955785 := bstep (se 2 (by rfl) ⟨22483419, by rfl⟩ : syracuseStep 59955785 = 44966839) B44966839
theorem B2308895 : Blo 1215425 2308895 := bstep (se 1 (by rfl) ⟨1731671, by rfl⟩ : syracuseStep 2308895 = 3463343) B3463343
theorem B3947903 : Blo 1215425 3947903 := bstep (se 1 (by rfl) ⟨2960927, by rfl⟩ : syracuseStep 3947903 = 5921855) B5921855
theorem B5193341 : Blo 1215425 5193341 := bstep (se 3 (by rfl) ⟨973751, by rfl⟩ : syracuseStep 5193341 = 1947503) B1947503
theorem B9232055 : Blo 1215425 9232055 := bstep (se 1 (by rfl) ⟨6924041, by rfl⟩ : syracuseStep 9232055 = 13848083) B13848083
theorem B3464927 : Blo 1215425 3464927 := bstep (se 1 (by rfl) ⟨2598695, by rfl⟩ : syracuseStep 3464927 = 5197391) B5197391
theorem B15794149 : Blo 1215425 15794149 := bstep (se 4 (by rfl) ⟨1480701, by rfl⟩ : syracuseStep 15794149 = 2961403) B2961403
theorem B5267699 : Blo 1215425 5267699 := bstep (se 1 (by rfl) ⟨3950774, by rfl⟩ : syracuseStep 5267699 = 7901549) B7901549
theorem B6160697 : Blo 1215425 6160697 := bstep (se 2 (by rfl) ⟨2310261, by rfl⟩ : syracuseStep 6160697 = 4620523) B4620523
theorem B3465575 : Blo 1215425 3465575 := bstep (se 1 (by rfl) ⟨2599181, by rfl⟩ : syracuseStep 3465575 = 5198363) B5198363
theorem B4620797 : Blo 1215425 4620797 := bstep (se 3 (by rfl) ⟨866399, by rfl⟩ : syracuseStep 4620797 = 1732799) B1732799
theorem B11100905 : Blo 1215425 11100905 := bstep (se 2 (by rfl) ⟨4162839, by rfl⟩ : syracuseStep 11100905 = 8325679) B8325679
theorem B11698931 : Blo 1215425 11698931 := bstep (se 1 (by rfl) ⟨8774198, by rfl⟩ : syracuseStep 11698931 = 17548397) B17548397
theorem B2737223 : Blo 1215425 2737223 := bstep (se 1 (by rfl) ⟨2052917, by rfl⟩ : syracuseStep 2737223 = 4105835) B4105835
theorem B4105403 : Blo 1215425 4105403 := bstep (se 1 (by rfl) ⟨3079052, by rfl⟩ : syracuseStep 4105403 = 6158105) B6158105
theorem B6153407 : Blo 1215425 6153407 := bstep (se 1 (by rfl) ⟨4615055, by rfl⟩ : syracuseStep 6153407 = 9230111) B9230111
theorem B6153569 : Blo 1215425 6153569 := bstep (se 2 (by rfl) ⟨2307588, by rfl⟩ : syracuseStep 6153569 = 4615177) B4615177
theorem B6923951 : Blo 1215425 6923951 := bstep (se 1 (by rfl) ⟨5192963, by rfl⟩ : syracuseStep 6923951 = 10385927) B10385927
theorem B39970523 : Blo 1215425 39970523 := bstep (se 1 (by rfl) ⟨29977892, by rfl⟩ : syracuseStep 39970523 = 59955785) B59955785
theorem B6932243 : Blo 1215425 6932243 := bstep (se 1 (by rfl) ⟨5199182, by rfl⟩ : syracuseStep 6932243 = 10398365) B10398365
theorem B2631935 : Blo 1215425 2631935 := bstep (se 1 (by rfl) ⟨1973951, by rfl⟩ : syracuseStep 2631935 = 3947903) B3947903
theorem B6154703 : Blo 1215425 6154703 := bstep (se 1 (by rfl) ⟨4616027, by rfl⟩ : syracuseStep 6154703 = 9232055) B9232055
theorem B8317577 : Blo 1215425 8317577 := bstep (se 2 (by rfl) ⟨3119091, by rfl⟩ : syracuseStep 8317577 = 6238183) B6238183
theorem B4614995 : Blo 1215425 4614995 := bstep (se 1 (by rfl) ⟨3461246, by rfl⟩ : syracuseStep 4614995 = 6922493) B6922493
theorem B2051399 : Blo 1215425 2051399 := bstep (se 1 (by rfl) ⟨1538549, by rfl⟩ : syracuseStep 2051399 = 3077099) B3077099
theorem B19729747 : Blo 1215425 19729747 := bstep (se 1 (by rfl) ⟨14797310, by rfl⟩ : syracuseStep 19729747 = 29594621) B29594621
theorem B1215983 : Blo 1215425 1215983 := bstep (se 1 (by rfl) ⟨911987, by rfl⟩ : syracuseStep 1215983 = 1823975) B1823975
theorem B1216111 : Blo 1215425 1216111 := bstep (se 1 (by rfl) ⟨912083, by rfl⟩ : syracuseStep 1216111 = 1824167) B1824167
theorem B10399427 : Blo 1215425 10399427 := bstep (se 1 (by rfl) ⟨7799570, by rfl⟩ : syracuseStep 10399427 = 15599141) B15599141
theorem B1216231 : Blo 1215425 1216231 := bstep (se 1 (by rfl) ⟨912173, by rfl⟩ : syracuseStep 1216231 = 1824347) B1824347
theorem B6573815 : Blo 1215425 6573815 := bstep (se 1 (by rfl) ⟨4930361, by rfl⟩ : syracuseStep 6573815 = 9860723) B9860723
theorem B1298207 : Blo 1215425 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B2191187 : Blo 1215425 2191187 := bstep (se 1 (by rfl) ⟨1643390, by rfl⟩ : syracuseStep 2191187 = 3286781) B3286781
theorem B2707447 : Blo 1215425 2707447 := bstep (se 1 (by rfl) ⟨2030585, by rfl⟩ : syracuseStep 2707447 = 4061171) B4061171
theorem B1216735 : Blo 1215425 1216735 := bstep (se 1 (by rfl) ⟨912551, by rfl⟩ : syracuseStep 1216735 = 1825103) B1825103
theorem B1216751 : Blo 1215425 1216751 := bstep (se 1 (by rfl) ⟨912563, by rfl⟩ : syracuseStep 1216751 = 1825127) B1825127
theorem B4616635 : Blo 1215425 4616635 := bstep (se 1 (by rfl) ⟨3462476, by rfl⟩ : syracuseStep 4616635 = 6924953) B6924953
theorem B3896095 : Blo 1215425 3896095 := bstep (se 1 (by rfl) ⟨2922071, by rfl⟩ : syracuseStep 3896095 = 5844143) B5844143
theorem B7795547 : Blo 1215425 7795547 := bstep (se 1 (by rfl) ⟨5846660, by rfl⟩ : syracuseStep 7795547 = 11693321) B11693321
theorem B3076987 : Blo 1215425 3076987 := bstep (se 1 (by rfl) ⟨2307740, by rfl⟩ : syracuseStep 3076987 = 4615481) B4615481
theorem B3462227 : Blo 1215425 3462227 := bstep (se 1 (by rfl) ⟨2596670, by rfl⟩ : syracuseStep 3462227 = 5193341) B5193341
theorem B6927551 : Blo 1215425 6927551 := bstep (se 1 (by rfl) ⟨5195663, by rfl⟩ : syracuseStep 6927551 = 10391327) B10391327
theorem B21058865 : Blo 1215425 21058865 := bstep (se 2 (by rfl) ⟨7897074, by rfl⟩ : syracuseStep 21058865 = 15794149) B15794149
theorem B5199319 : Blo 1215425 5199319 := bstep (se 1 (by rfl) ⟨3899489, by rfl⟩ : syracuseStep 5199319 = 7798979) B7798979
theorem B20780873 : Blo 1215425 20780873 := bstep (se 2 (by rfl) ⟨7792827, by rfl⟩ : syracuseStep 20780873 = 15585655) B15585655
theorem B4159475 : Blo 1215425 4159475 := bstep (se 1 (by rfl) ⟨3119606, by rfl⟩ : syracuseStep 4159475 = 6239213) B6239213
theorem B9861115 : Blo 1215425 9861115 := bstep (se 1 (by rfl) ⟨7395836, by rfl⟩ : syracuseStep 9861115 = 14791673) B14791673
theorem B7788727 : Blo 1215425 7788727 := bstep (se 1 (by rfl) ⟨5841545, by rfl⟩ : syracuseStep 7788727 = 11683091) B11683091
theorem B5192383 : Blo 1215425 5192383 := bstep (se 1 (by rfl) ⟨3894287, by rfl⟩ : syracuseStep 5192383 = 7788575) B7788575
theorem B1825511 : Blo 1215425 1825511 := bstep (se 1 (by rfl) ⟨1369133, by rfl⟩ : syracuseStep 1825511 = 2738267) B2738267
theorem B1825535 : Blo 1215425 1825535 := bstep (se 1 (by rfl) ⟨1369151, by rfl⟩ : syracuseStep 1825535 = 2738303) B2738303
theorem B20798369 : Blo 1215425 20798369 := bstep (se 2 (by rfl) ⟨7799388, by rfl⟩ : syracuseStep 20798369 = 15598777) B15598777
theorem B1825727 : Blo 1215425 1825727 := bstep (se 1 (by rfl) ⟨1369295, by rfl⟩ : syracuseStep 1825727 = 2738591) B2738591
theorem B7789729 : Blo 1215425 7789729 := bstep (se 2 (by rfl) ⟨2921148, by rfl⟩ : syracuseStep 7789729 = 5842297) B5842297
theorem B1539263 : Blo 1215425 1539263 := bstep (se 1 (by rfl) ⟨1154447, by rfl⟩ : syracuseStep 1539263 = 2308895) B2308895
theorem B1367455 : Blo 1215425 1367455 := bstep (se 1 (by rfl) ⟨1025591, by rfl⟩ : syracuseStep 1367455 = 2051183) B2051183
theorem B2309609 : Blo 1215425 2309609 := bstep (se 2 (by rfl) ⟨866103, by rfl⟩ : syracuseStep 2309609 = 1732207) B1732207
theorem B2309951 : Blo 1215425 2309951 := bstep (se 1 (by rfl) ⟨1732463, by rfl⟩ : syracuseStep 2309951 = 3464927) B3464927
theorem B2310383 : Blo 1215425 2310383 := bstep (se 1 (by rfl) ⟨1732787, by rfl⟩ : syracuseStep 2310383 = 3465575) B3465575
theorem B3080531 : Blo 1215425 3080531 := bstep (se 1 (by rfl) ⟨2310398, by rfl⟩ : syracuseStep 3080531 = 4620797) B4620797
theorem B7799287 : Blo 1215425 7799287 := bstep (se 1 (by rfl) ⟨5849465, by rfl⟩ : syracuseStep 7799287 = 11698931) B11698931
theorem B4104701 : Blo 1215425 4104701 := bstep (se 3 (by rfl) ⟨769631, by rfl⟩ : syracuseStep 4104701 = 1539263) B1539263
theorem B2736935 : Blo 1215425 2736935 := bstep (se 1 (by rfl) ⟨2052701, by rfl⟩ : syracuseStep 2736935 = 4105403) B4105403
theorem B6923177 : Blo 1215425 6923177 := bstep (se 2 (by rfl) ⟨2596191, by rfl⟩ : syracuseStep 6923177 = 5192383) B5192383
theorem B5194793 : Blo 1215425 5194793 := bstep (se 2 (by rfl) ⟨1948047, by rfl⟩ : syracuseStep 5194793 = 3896095) B3896095
theorem B4621495 : Blo 1215425 4621495 := bstep (se 1 (by rfl) ⟨3466121, by rfl⟩ : syracuseStep 4621495 = 6932243) B6932243
theorem B13853915 : Blo 1215425 13853915 := bstep (se 1 (by rfl) ⟨10390436, by rfl⟩ : syracuseStep 13853915 = 20780873) B20780873
theorem B106588061 : Blo 1215425 106588061 := bstep (se 3 (by rfl) ⟨19985261, by rfl⟩ : syracuseStep 106588061 = 39970523) B39970523
theorem B6932425 : Blo 1215425 6932425 := bstep (se 2 (by rfl) ⟨2599659, by rfl⟩ : syracuseStep 6932425 = 5199319) B5199319
theorem B6932951 : Blo 1215425 6932951 := bstep (se 1 (by rfl) ⟨5199713, by rfl⟩ : syracuseStep 6932951 = 10399427) B10399427
theorem B1460791 : Blo 1215425 1460791 := bstep (se 1 (by rfl) ⟨1095593, by rfl⟩ : syracuseStep 1460791 = 2191187) B2191187
theorem B4107131 : Blo 1215425 4107131 := bstep (se 1 (by rfl) ⟨3080348, by rfl⟩ : syracuseStep 4107131 = 6160697) B6160697
theorem B7400603 : Blo 1215425 7400603 := bstep (se 1 (by rfl) ⟨5550452, by rfl⟩ : syracuseStep 7400603 = 11100905) B11100905
theorem B5197031 : Blo 1215425 5197031 := bstep (se 1 (by rfl) ⟨3897773, by rfl⟩ : syracuseStep 5197031 = 7795547) B7795547
theorem B6155513 : Blo 1215425 6155513 := bstep (se 2 (by rfl) ⟨2308317, by rfl⟩ : syracuseStep 6155513 = 4616635) B4616635
theorem B4615967 : Blo 1215425 4615967 := bstep (se 1 (by rfl) ⟨3461975, by rfl⟩ : syracuseStep 4615967 = 6923951) B6923951
theorem B2772983 : Blo 1215425 2772983 := bstep (se 1 (by rfl) ⟨2079737, by rfl⟩ : syracuseStep 2772983 = 4159475) B4159475
theorem B22180205 : Blo 1215425 22180205 := bstep (se 3 (by rfl) ⟨4158788, by rfl⟩ : syracuseStep 22180205 = 8317577) B8317577
theorem B1217007 : Blo 1215425 1217007 := bstep (se 1 (by rfl) ⟨912755, by rfl⟩ : syracuseStep 1217007 = 1825511) B1825511
theorem B1217023 : Blo 1215425 1217023 := bstep (se 1 (by rfl) ⟨912767, by rfl⟩ : syracuseStep 1217023 = 1825535) B1825535
theorem B1823273 : Blo 1215425 1823273 := bstep (se 2 (by rfl) ⟨683727, by rfl⟩ : syracuseStep 1823273 = 1367455) B1367455
theorem B3076663 : Blo 1215425 3076663 := bstep (se 1 (by rfl) ⟨2307497, by rfl⟩ : syracuseStep 3076663 = 4614995) B4614995
theorem B13865579 : Blo 1215425 13865579 := bstep (se 1 (by rfl) ⟨10399184, by rfl⟩ : syracuseStep 13865579 = 20798369) B20798369
theorem B1217151 : Blo 1215425 1217151 := bstep (se 1 (by rfl) ⟨912863, by rfl⟩ : syracuseStep 1217151 = 1825727) B1825727
theorem B3461885 : Blo 1215425 3461885 := bstep (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) B1298207
theorem B3609929 : Blo 1215425 3609929 := bstep (se 2 (by rfl) ⟨1353723, by rfl⟩ : syracuseStep 3609929 = 2707447) B2707447
theorem B3511799 : Blo 1215425 3511799 := bstep (se 1 (by rfl) ⟨2633849, by rfl⟩ : syracuseStep 3511799 = 5267699) B5267699
theorem B10384969 : Blo 1215425 10384969 := bstep (se 2 (by rfl) ⟨3894363, by rfl⟩ : syracuseStep 10384969 = 7788727) B7788727
theorem B7018493 : Blo 1215425 7018493 := bstep (se 3 (by rfl) ⟨1315967, by rfl⟩ : syracuseStep 7018493 = 2631935) B2631935
theorem B1824815 : Blo 1215425 1824815 := bstep (se 1 (by rfl) ⟨1368611, by rfl⟩ : syracuseStep 1824815 = 2737223) B2737223
theorem B2308151 : Blo 1215425 2308151 := bstep (se 1 (by rfl) ⟨1731113, by rfl⟩ : syracuseStep 2308151 = 3462227) B3462227
theorem B4102271 : Blo 1215425 4102271 := bstep (se 1 (by rfl) ⟨3076703, by rfl⟩ : syracuseStep 4102271 = 6153407) B6153407
theorem B4618367 : Blo 1215425 4618367 := bstep (se 1 (by rfl) ⟨3463775, by rfl⟩ : syracuseStep 4618367 = 6927551) B6927551
theorem B14039243 : Blo 1215425 14039243 := bstep (se 1 (by rfl) ⟨10529432, by rfl⟩ : syracuseStep 14039243 = 21058865) B21058865
theorem B4102379 : Blo 1215425 4102379 := bstep (se 1 (by rfl) ⟨3076784, by rfl⟩ : syracuseStep 4102379 = 6153569) B6153569
theorem B4102649 : Blo 1215425 4102649 := bstep (se 2 (by rfl) ⟨1538493, by rfl⟩ : syracuseStep 4102649 = 3076987) B3076987
theorem B10386305 : Blo 1215425 10386305 := bstep (se 2 (by rfl) ⟨3894864, by rfl⟩ : syracuseStep 10386305 = 7789729) B7789729
theorem B4103135 : Blo 1215425 4103135 := bstep (se 1 (by rfl) ⟨3077351, by rfl⟩ : syracuseStep 4103135 = 6154703) B6154703
theorem B105225317 : Blo 1215425 105225317 := bstep (se 4 (by rfl) ⟨9864873, by rfl⟩ : syracuseStep 105225317 = 19729747) B19729747
theorem B1367599 : Blo 1215425 1367599 := bstep (se 1 (by rfl) ⟨1025699, by rfl⟩ : syracuseStep 1367599 = 2051399) B2051399
theorem B1539739 : Blo 1215425 1539739 := bstep (se 1 (by rfl) ⟨1154804, by rfl⟩ : syracuseStep 1539739 = 2309609) B2309609
theorem B4382543 : Blo 1215425 4382543 := bstep (se 1 (by rfl) ⟨3286907, by rfl⟩ : syracuseStep 4382543 = 6573815) B6573815
theorem B1539967 : Blo 1215425 1539967 := bstep (se 1 (by rfl) ⟨1154975, by rfl⟩ : syracuseStep 1539967 = 2309951) B2309951
theorem B13148153 : Blo 1215425 13148153 := bstep (se 2 (by rfl) ⟨4930557, by rfl⟩ : syracuseStep 13148153 = 9861115) B9861115
theorem B14786803 : Blo 1215425 14786803 := bstep (se 1 (by rfl) ⟨11090102, by rfl⟩ : syracuseStep 14786803 = 22180205) B22180205
theorem B2736467 : Blo 1215425 2736467 := bstep (se 1 (by rfl) ⟨2052350, by rfl⟩ : syracuseStep 2736467 = 4104701) B4104701
theorem B19734941 : Blo 1215425 19734941 := bstep (se 3 (by rfl) ⟨3700301, by rfl⟩ : syracuseStep 19734941 = 7400603) B7400603
theorem B6161021 : Blo 1215425 6161021 := bstep (se 3 (by rfl) ⟨1155191, by rfl⟩ : syracuseStep 6161021 = 2310383) B2310383
theorem B71058707 : Blo 1215425 71058707 := bstep (se 1 (by rfl) ⟨53294030, by rfl⟩ : syracuseStep 71058707 = 106588061) B106588061
theorem B6161993 : Blo 1215425 6161993 := bstep (se 2 (by rfl) ⟨2310747, by rfl⟩ : syracuseStep 6161993 = 4621495) B4621495
theorem B4621967 : Blo 1215425 4621967 := bstep (se 1 (by rfl) ⟨3466475, by rfl⟩ : syracuseStep 4621967 = 6932951) B6932951
theorem B2738087 : Blo 1215425 2738087 := bstep (se 1 (by rfl) ⟨2053565, by rfl⟩ : syracuseStep 2738087 = 4107131) B4107131
theorem B6924203 : Blo 1215425 6924203 := bstep (se 1 (by rfl) ⟨5193152, by rfl⟩ : syracuseStep 6924203 = 10386305) B10386305
theorem B70150211 : Blo 1215425 70150211 := bstep (se 1 (by rfl) ⟨52612658, by rfl⟩ : syracuseStep 70150211 = 105225317) B105225317
theorem B13846625 : Blo 1215425 13846625 := bstep (se 2 (by rfl) ⟨5192484, by rfl⟩ : syracuseStep 13846625 = 10384969) B10384969
theorem B9243233 : Blo 1215425 9243233 := bstep (se 2 (by rfl) ⟨3466212, by rfl⟩ : syracuseStep 9243233 = 6932425) B6932425
theorem B1215515 : Blo 1215425 1215515 := bstep (se 1 (by rfl) ⟨911636, by rfl⟩ : syracuseStep 1215515 = 1823273) B1823273
theorem B9243719 : Blo 1215425 9243719 := bstep (se 1 (by rfl) ⟨6932789, by rfl⟩ : syracuseStep 9243719 = 13865579) B13865579
theorem B4615451 : Blo 1215425 4615451 := bstep (se 1 (by rfl) ⟨3461588, by rfl⟩ : syracuseStep 4615451 = 6923177) B6923177
theorem B10399049 : Blo 1215425 10399049 := bstep (se 2 (by rfl) ⟨3899643, by rfl⟩ : syracuseStep 10399049 = 7799287) B7799287
theorem B9235943 : Blo 1215425 9235943 := bstep (se 1 (by rfl) ⟨6926957, by rfl⟩ : syracuseStep 9235943 = 13853915) B13853915
theorem B1216543 : Blo 1215425 1216543 := bstep (se 1 (by rfl) ⟨912407, by rfl⟩ : syracuseStep 1216543 = 1824815) B1824815
theorem B9359495 : Blo 1215425 9359495 := bstep (se 1 (by rfl) ⟨7019621, by rfl⟩ : syracuseStep 9359495 = 14039243) B14039243
theorem B1823465 : Blo 1215425 1823465 := bstep (se 2 (by rfl) ⟨683799, by rfl⟩ : syracuseStep 1823465 = 1367599) B1367599
theorem B11686781 : Blo 1215425 11686781 := bstep (se 3 (by rfl) ⟨2191271, by rfl⟩ : syracuseStep 11686781 = 4382543) B4382543
theorem B2052985 : Blo 1215425 2052985 := bstep (se 2 (by rfl) ⟨769869, by rfl⟩ : syracuseStep 2052985 = 1539739) B1539739
theorem B2053289 : Blo 1215425 2053289 := bstep (se 2 (by rfl) ⟨769983, by rfl⟩ : syracuseStep 2053289 = 1539967) B1539967
theorem B3077311 : Blo 1215425 3077311 := bstep (se 1 (by rfl) ⟨2307983, by rfl⟩ : syracuseStep 3077311 = 4615967) B4615967
theorem B18715981 : Blo 1215425 18715981 := bstep (se 3 (by rfl) ⟨3509246, by rfl⟩ : syracuseStep 18715981 = 7018493) B7018493
theorem B1848655 : Blo 1215425 1848655 := bstep (se 1 (by rfl) ⟨1386491, by rfl⟩ : syracuseStep 1848655 = 2772983) B2772983
theorem B2053687 : Blo 1215425 2053687 := bstep (se 1 (by rfl) ⟨1540265, by rfl⟩ : syracuseStep 2053687 = 3080531) B3080531
theorem B2307923 : Blo 1215425 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B1824623 : Blo 1215425 1824623 := bstep (se 1 (by rfl) ⟨1368467, by rfl⟩ : syracuseStep 1824623 = 2736935) B2736935
theorem B3463195 : Blo 1215425 3463195 := bstep (se 1 (by rfl) ⟨2597396, by rfl⟩ : syracuseStep 3463195 = 5194793) B5194793
theorem B4102217 : Blo 1215425 4102217 := bstep (se 2 (by rfl) ⟨1538331, by rfl⟩ : syracuseStep 4102217 = 3076663) B3076663
theorem B1947721 : Blo 1215425 1947721 := bstep (se 2 (by rfl) ⟨730395, by rfl⟩ : syracuseStep 1947721 = 1460791) B1460791
theorem B2406619 : Blo 1215425 2406619 := bstep (se 1 (by rfl) ⟨1804964, by rfl⟩ : syracuseStep 2406619 = 3609929) B3609929
theorem B2341199 : Blo 1215425 2341199 := bstep (se 1 (by rfl) ⟨1755899, by rfl⟩ : syracuseStep 2341199 = 3511799) B3511799
theorem B1538767 : Blo 1215425 1538767 := bstep (se 1 (by rfl) ⟨1154075, by rfl⟩ : syracuseStep 1538767 = 2308151) B2308151
theorem B2734847 : Blo 1215425 2734847 := bstep (se 1 (by rfl) ⟨2051135, by rfl⟩ : syracuseStep 2734847 = 4102271) B4102271
theorem B3078911 : Blo 1215425 3078911 := bstep (se 1 (by rfl) ⟨2309183, by rfl⟩ : syracuseStep 3078911 = 4618367) B4618367
theorem B2734919 : Blo 1215425 2734919 := bstep (se 1 (by rfl) ⟨2051189, by rfl⟩ : syracuseStep 2734919 = 4102379) B4102379
theorem B2735099 : Blo 1215425 2735099 := bstep (se 1 (by rfl) ⟨2051324, by rfl⟩ : syracuseStep 2735099 = 4102649) B4102649
theorem B2735423 : Blo 1215425 2735423 := bstep (se 1 (by rfl) ⟨2051567, by rfl⟩ : syracuseStep 2735423 = 4103135) B4103135
theorem B3464687 : Blo 1215425 3464687 := bstep (se 1 (by rfl) ⟨2598515, by rfl⟩ : syracuseStep 3464687 = 5197031) B5197031
theorem B4103675 : Blo 1215425 4103675 := bstep (se 1 (by rfl) ⟨3077756, by rfl⟩ : syracuseStep 4103675 = 6155513) B6155513
theorem B8765435 : Blo 1215425 8765435 := bstep (se 1 (by rfl) ⟨6574076, by rfl⟩ : syracuseStep 8765435 = 13148153) B13148153
theorem B2596961 : Blo 1215425 2596961 := bstep (se 2 (by rfl) ⟨973860, by rfl⟩ : syracuseStep 2596961 = 1947721) B1947721
theorem B13156627 : Blo 1215425 13156627 := bstep (se 1 (by rfl) ⟨9867470, by rfl⟩ : syracuseStep 13156627 = 19734941) B19734941
theorem B1368859 : Blo 1215425 1368859 := bstep (se 1 (by rfl) ⟨1026644, by rfl⟩ : syracuseStep 1368859 = 2053289) B2053289
theorem B3081311 : Blo 1215425 3081311 := bstep (se 1 (by rfl) ⟨2310983, by rfl⟩ : syracuseStep 3081311 = 4621967) B4621967
theorem B2737313 : Blo 1215425 2737313 := bstep (se 2 (by rfl) ⟨1026492, by rfl⟩ : syracuseStep 2737313 = 2052985) B2052985
theorem B6162155 : Blo 1215425 6162155 := bstep (se 1 (by rfl) ⟨4621616, by rfl⟩ : syracuseStep 6162155 = 9243233) B9243233
theorem B24954641 : Blo 1215425 24954641 := bstep (se 2 (by rfl) ⟨9357990, by rfl⟩ : syracuseStep 24954641 = 18715981) B18715981
theorem B6162479 : Blo 1215425 6162479 := bstep (se 1 (by rfl) ⟨4621859, by rfl⟩ : syracuseStep 6162479 = 9243719) B9243719
theorem B2738249 : Blo 1215425 2738249 := bstep (se 2 (by rfl) ⟨1026843, by rfl⟩ : syracuseStep 2738249 = 2053687) B2053687
theorem B6932699 : Blo 1215425 6932699 := bstep (se 1 (by rfl) ⟨5199524, by rfl⟩ : syracuseStep 6932699 = 10399049) B10399049
theorem B31164749 : Blo 1215425 31164749 := bstep (se 3 (by rfl) ⟨5843390, by rfl⟩ : syracuseStep 31164749 = 11686781) B11686781
theorem B5843623 : Blo 1215425 5843623 := bstep (se 1 (by rfl) ⟨4382717, by rfl⟩ : syracuseStep 5843623 = 8765435) B8765435
theorem B4107347 : Blo 1215425 4107347 := bstep (se 1 (by rfl) ⟨3080510, by rfl⟩ : syracuseStep 4107347 = 6161021) B6161021
theorem B1215643 : Blo 1215425 1215643 := bstep (se 1 (by rfl) ⟨911732, by rfl⟩ : syracuseStep 1215643 = 1823465) B1823465
theorem B2051689 : Blo 1215425 2051689 := bstep (se 2 (by rfl) ⟨769383, by rfl⟩ : syracuseStep 2051689 = 1538767) B1538767
theorem B4107995 : Blo 1215425 4107995 := bstep (se 1 (by rfl) ⟨3080996, by rfl⟩ : syracuseStep 4107995 = 6161993) B6161993
theorem B1216415 : Blo 1215425 1216415 := bstep (se 1 (by rfl) ⟨912311, by rfl⟩ : syracuseStep 1216415 = 1824623) B1824623
theorem B4616135 : Blo 1215425 4616135 := bstep (se 1 (by rfl) ⟨3462101, by rfl⟩ : syracuseStep 4616135 = 6924203) B6924203
theorem B1560799 : Blo 1215425 1560799 := bstep (se 1 (by rfl) ⟨1170599, by rfl⟩ : syracuseStep 1560799 = 2341199) B2341199
theorem B1823231 : Blo 1215425 1823231 := bstep (se 1 (by rfl) ⟨1367423, by rfl⟩ : syracuseStep 1823231 = 2734847) B2734847
theorem B2052607 : Blo 1215425 2052607 := bstep (se 1 (by rfl) ⟨1539455, by rfl⟩ : syracuseStep 2052607 = 3078911) B3078911
theorem B1823279 : Blo 1215425 1823279 := bstep (se 1 (by rfl) ⟨1367459, by rfl⟩ : syracuseStep 1823279 = 2734919) B2734919
theorem B1823399 : Blo 1215425 1823399 := bstep (se 1 (by rfl) ⟨1367549, by rfl⟩ : syracuseStep 1823399 = 2735099) B2735099
theorem B3076967 : Blo 1215425 3076967 := bstep (se 1 (by rfl) ⟨2307725, by rfl⟩ : syracuseStep 3076967 = 4615451) B4615451
theorem B1823615 : Blo 1215425 1823615 := bstep (se 1 (by rfl) ⟨1367711, by rfl⟩ : syracuseStep 1823615 = 2735423) B2735423
theorem B6157295 : Blo 1215425 6157295 := bstep (se 1 (by rfl) ⟨4617971, by rfl⟩ : syracuseStep 6157295 = 9235943) B9235943
theorem B4617593 : Blo 1215425 4617593 := bstep (se 2 (by rfl) ⟨1731597, by rfl⟩ : syracuseStep 4617593 = 3463195) B3463195
theorem B6239663 : Blo 1215425 6239663 := bstep (se 1 (by rfl) ⟨4679747, by rfl⟩ : syracuseStep 6239663 = 9359495) B9359495
theorem B1824311 : Blo 1215425 1824311 := bstep (se 1 (by rfl) ⟨1368233, by rfl⟩ : syracuseStep 1824311 = 2736467) B2736467
theorem B3208825 : Blo 1215425 3208825 := bstep (se 2 (by rfl) ⟨1203309, by rfl⟩ : syracuseStep 3208825 = 2406619) B2406619
theorem B19715737 : Blo 1215425 19715737 := bstep (se 2 (by rfl) ⟨7393401, by rfl⟩ : syracuseStep 19715737 = 14786803) B14786803
theorem B47372471 : Blo 1215425 47372471 := bstep (se 1 (by rfl) ⟨35529353, by rfl⟩ : syracuseStep 47372471 = 71058707) B71058707
theorem B1538615 : Blo 1215425 1538615 := bstep (se 1 (by rfl) ⟨1153961, by rfl⟩ : syracuseStep 1538615 = 2307923) B2307923
theorem B1825391 : Blo 1215425 1825391 := bstep (se 1 (by rfl) ⟨1369043, by rfl⟩ : syracuseStep 1825391 = 2738087) B2738087
theorem B46766807 : Blo 1215425 46766807 := bstep (se 1 (by rfl) ⟨35075105, by rfl⟩ : syracuseStep 46766807 = 70150211) B70150211
theorem B2734811 : Blo 1215425 2734811 := bstep (se 1 (by rfl) ⟨2051108, by rfl⟩ : syracuseStep 2734811 = 4102217) B4102217
theorem B9231083 : Blo 1215425 9231083 := bstep (se 1 (by rfl) ⟨6923312, by rfl⟩ : syracuseStep 9231083 = 13846625) B13846625
theorem B4103081 : Blo 1215425 4103081 := bstep (se 2 (by rfl) ⟨1538655, by rfl⟩ : syracuseStep 4103081 = 3077311) B3077311
theorem B2464873 : Blo 1215425 2464873 := bstep (se 2 (by rfl) ⟨924327, by rfl⟩ : syracuseStep 2464873 = 1848655) B1848655
theorem B2309791 : Blo 1215425 2309791 := bstep (se 1 (by rfl) ⟨1732343, by rfl⟩ : syracuseStep 2309791 = 3464687) B3464687
theorem B2735783 : Blo 1215425 2735783 := bstep (se 1 (by rfl) ⟨2051837, by rfl⟩ : syracuseStep 2735783 = 4103675) B4103675
theorem B2081065 : Blo 1215425 2081065 := bstep (se 2 (by rfl) ⟨780399, by rfl⟩ : syracuseStep 2081065 = 1560799) B1560799
theorem B4104863 : Blo 1215425 4104863 := bstep (se 1 (by rfl) ⟨3078647, by rfl⟩ : syracuseStep 4104863 = 6157295) B6157295
theorem B2736809 : Blo 1215425 2736809 := bstep (se 2 (by rfl) ⟨1026303, by rfl⟩ : syracuseStep 2736809 = 2052607) B2052607
theorem B7791497 : Blo 1215425 7791497 := bstep (se 2 (by rfl) ⟨2921811, by rfl⟩ : syracuseStep 7791497 = 5843623) B5843623
theorem B31581647 : Blo 1215425 31581647 := bstep (se 1 (by rfl) ⟨23686235, by rfl⟩ : syracuseStep 31581647 = 47372471) B47372471
theorem B4621799 : Blo 1215425 4621799 := bstep (se 1 (by rfl) ⟨3466349, by rfl⟩ : syracuseStep 4621799 = 6932699) B6932699
theorem B20776499 : Blo 1215425 20776499 := bstep (se 1 (by rfl) ⟨15582374, by rfl⟩ : syracuseStep 20776499 = 31164749) B31164749
theorem B6154055 : Blo 1215425 6154055 := bstep (se 1 (by rfl) ⟨4615541, by rfl⟩ : syracuseStep 6154055 = 9231083) B9231083
theorem B2738231 : Blo 1215425 2738231 := bstep (se 1 (by rfl) ⟨2053673, by rfl⟩ : syracuseStep 2738231 = 4107347) B4107347
theorem B4278433 : Blo 1215425 4278433 := bstep (se 2 (by rfl) ⟨1604412, by rfl⟩ : syracuseStep 4278433 = 3208825) B3208825
theorem B2738663 : Blo 1215425 2738663 := bstep (se 1 (by rfl) ⟨2053997, by rfl⟩ : syracuseStep 2738663 = 4107995) B4107995
theorem B1731307 : Blo 1215425 1731307 := bstep (se 1 (by rfl) ⟨1298480, by rfl⟩ : syracuseStep 1731307 = 2596961) B2596961
theorem B1215487 : Blo 1215425 1215487 := bstep (se 1 (by rfl) ⟨911615, by rfl⟩ : syracuseStep 1215487 = 1823231) B1823231
theorem B17542169 : Blo 1215425 17542169 := bstep (se 2 (by rfl) ⟨6578313, by rfl⟩ : syracuseStep 17542169 = 13156627) B13156627
theorem B1215519 : Blo 1215425 1215519 := bstep (se 1 (by rfl) ⟨911639, by rfl⟩ : syracuseStep 1215519 = 1823279) B1823279
theorem B1215599 : Blo 1215425 1215599 := bstep (se 1 (by rfl) ⟨911699, by rfl⟩ : syracuseStep 1215599 = 1823399) B1823399
theorem B2051311 : Blo 1215425 2051311 := bstep (se 1 (by rfl) ⟨1538483, by rfl⟩ : syracuseStep 2051311 = 3076967) B3076967
theorem B1215743 : Blo 1215425 1215743 := bstep (se 1 (by rfl) ⟨911807, by rfl⟩ : syracuseStep 1215743 = 1823615) B1823615
theorem B1216207 : Blo 1215425 1216207 := bstep (se 1 (by rfl) ⟨912155, by rfl⟩ : syracuseStep 1216207 = 1824311) B1824311
theorem B4108103 : Blo 1215425 4108103 := bstep (se 1 (by rfl) ⟨3081077, by rfl⟩ : syracuseStep 4108103 = 6162155) B6162155
theorem B4108319 : Blo 1215425 4108319 := bstep (se 1 (by rfl) ⟨3081239, by rfl⟩ : syracuseStep 4108319 = 6162479) B6162479
theorem B1216927 : Blo 1215425 1216927 := bstep (se 1 (by rfl) ⟨912695, by rfl⟩ : syracuseStep 1216927 = 1825391) B1825391
theorem B1823207 : Blo 1215425 1823207 := bstep (se 1 (by rfl) ⟨1367405, by rfl⟩ : syracuseStep 1823207 = 2734811) B2734811
theorem B1823855 : Blo 1215425 1823855 := bstep (se 1 (by rfl) ⟨1367891, by rfl⟩ : syracuseStep 1823855 = 2735783) B2735783
theorem B3077423 : Blo 1215425 3077423 := bstep (se 1 (by rfl) ⟨2308067, by rfl⟩ : syracuseStep 3077423 = 4616135) B4616135
theorem B13145989 : Blo 1215425 13145989 := bstep (se 4 (by rfl) ⟨1232436, by rfl⟩ : syracuseStep 13145989 = 2464873) B2464873
theorem B2054207 : Blo 1215425 2054207 := bstep (se 1 (by rfl) ⟨1540655, by rfl⟩ : syracuseStep 2054207 = 3081311) B3081311
theorem B1824875 : Blo 1215425 1824875 := bstep (se 1 (by rfl) ⟨1368656, by rfl⟩ : syracuseStep 1824875 = 2737313) B2737313
theorem B3078395 : Blo 1215425 3078395 := bstep (se 1 (by rfl) ⟨2308796, by rfl⟩ : syracuseStep 3078395 = 4617593) B4617593
theorem B4159775 : Blo 1215425 4159775 := bstep (se 1 (by rfl) ⟨3119831, by rfl⟩ : syracuseStep 4159775 = 6239663) B6239663
theorem B1825145 : Blo 1215425 1825145 := bstep (se 2 (by rfl) ⟨684429, by rfl⟩ : syracuseStep 1825145 = 1368859) B1368859
theorem B16636427 : Blo 1215425 16636427 := bstep (se 1 (by rfl) ⟨12477320, by rfl⟩ : syracuseStep 16636427 = 24954641) B24954641
theorem B1825499 : Blo 1215425 1825499 := bstep (se 1 (by rfl) ⟨1369124, by rfl⟩ : syracuseStep 1825499 = 2738249) B2738249
theorem B4102973 : Blo 1215425 4102973 := bstep (se 3 (by rfl) ⟨769307, by rfl⟩ : syracuseStep 4102973 = 1538615) B1538615
theorem B31177871 : Blo 1215425 31177871 := bstep (se 1 (by rfl) ⟨23383403, by rfl⟩ : syracuseStep 31177871 = 46766807) B46766807
theorem B2735387 : Blo 1215425 2735387 := bstep (se 1 (by rfl) ⟨2051540, by rfl⟩ : syracuseStep 2735387 = 4103081) B4103081
theorem B2735585 : Blo 1215425 2735585 := bstep (se 2 (by rfl) ⟨1025844, by rfl⟩ : syracuseStep 2735585 = 2051689) B2051689
theorem B26287649 : Blo 1215425 26287649 := bstep (se 2 (by rfl) ⟨9857868, by rfl⟩ : syracuseStep 26287649 = 19715737) B19715737
theorem B3079721 : Blo 1215425 3079721 := bstep (se 2 (by rfl) ⟨1154895, by rfl⟩ : syracuseStep 3079721 = 2309791) B2309791
theorem B2736575 : Blo 1215425 2736575 := bstep (se 1 (by rfl) ⟨2052431, by rfl⟩ : syracuseStep 2736575 = 4104863) B4104863
theorem B5194331 : Blo 1215425 5194331 := bstep (se 1 (by rfl) ⟨3895748, by rfl⟩ : syracuseStep 5194331 = 7791497) B7791497
theorem B21054431 : Blo 1215425 21054431 := bstep (se 1 (by rfl) ⟨15790823, by rfl⟩ : syracuseStep 21054431 = 31581647) B31581647
theorem B3081199 : Blo 1215425 3081199 := bstep (se 1 (by rfl) ⟨2310899, by rfl⟩ : syracuseStep 3081199 = 4621799) B4621799
theorem B1369471 : Blo 1215425 1369471 := bstep (se 1 (by rfl) ⟨1027103, by rfl⟩ : syracuseStep 1369471 = 2054207) B2054207
theorem B20785247 : Blo 1215425 20785247 := bstep (se 1 (by rfl) ⟨15588935, by rfl⟩ : syracuseStep 20785247 = 31177871) B31177871
theorem B17525099 : Blo 1215425 17525099 := bstep (se 1 (by rfl) ⟨13143824, by rfl⟩ : syracuseStep 17525099 = 26287649) B26287649
theorem B2738735 : Blo 1215425 2738735 := bstep (se 1 (by rfl) ⟨2054051, by rfl⟩ : syracuseStep 2738735 = 4108103) B4108103
theorem B2738879 : Blo 1215425 2738879 := bstep (se 1 (by rfl) ⟨2054159, by rfl⟩ : syracuseStep 2738879 = 4108319) B4108319
theorem B5704577 : Blo 1215425 5704577 := bstep (se 2 (by rfl) ⟨2139216, by rfl⟩ : syracuseStep 5704577 = 4278433) B4278433
theorem B1215471 : Blo 1215425 1215471 := bstep (se 1 (by rfl) ⟨911603, by rfl⟩ : syracuseStep 1215471 = 1823207) B1823207
theorem B1215903 : Blo 1215425 1215903 := bstep (se 1 (by rfl) ⟨911927, by rfl⟩ : syracuseStep 1215903 = 1823855) B1823855
theorem B2051615 : Blo 1215425 2051615 := bstep (se 1 (by rfl) ⟨1538711, by rfl⟩ : syracuseStep 2051615 = 3077423) B3077423
theorem B1216583 : Blo 1215425 1216583 := bstep (se 1 (by rfl) ⟨912437, by rfl⟩ : syracuseStep 1216583 = 1824875) B1824875
theorem B2052263 : Blo 1215425 2052263 := bstep (se 1 (by rfl) ⟨1539197, by rfl⟩ : syracuseStep 2052263 = 3078395) B3078395
theorem B2773183 : Blo 1215425 2773183 := bstep (se 1 (by rfl) ⟨2079887, by rfl⟩ : syracuseStep 2773183 = 4159775) B4159775
theorem B1216763 : Blo 1215425 1216763 := bstep (se 1 (by rfl) ⟨912572, by rfl⟩ : syracuseStep 1216763 = 1825145) B1825145
theorem B1216999 : Blo 1215425 1216999 := bstep (se 1 (by rfl) ⟨912749, by rfl⟩ : syracuseStep 1216999 = 1825499) B1825499
theorem B11694779 : Blo 1215425 11694779 := bstep (se 1 (by rfl) ⟨8771084, by rfl⟩ : syracuseStep 11694779 = 17542169) B17542169
theorem B1823591 : Blo 1215425 1823591 := bstep (se 1 (by rfl) ⟨1367693, by rfl⟩ : syracuseStep 1823591 = 2735387) B2735387
theorem B1823723 : Blo 1215425 1823723 := bstep (se 1 (by rfl) ⟨1367792, by rfl⟩ : syracuseStep 1823723 = 2735585) B2735585
theorem B2053147 : Blo 1215425 2053147 := bstep (se 1 (by rfl) ⟨1539860, by rfl⟩ : syracuseStep 2053147 = 3079721) B3079721
theorem B17527985 : Blo 1215425 17527985 := bstep (se 2 (by rfl) ⟨6572994, by rfl⟩ : syracuseStep 17527985 = 13145989) B13145989
theorem B2774753 : Blo 1215425 2774753 := bstep (se 2 (by rfl) ⟨1040532, by rfl⟩ : syracuseStep 2774753 = 2081065) B2081065
theorem B1824539 : Blo 1215425 1824539 := bstep (se 1 (by rfl) ⟨1368404, by rfl⟩ : syracuseStep 1824539 = 2736809) B2736809
theorem B2308409 : Blo 1215425 2308409 := bstep (se 2 (by rfl) ⟨865653, by rfl⟩ : syracuseStep 2308409 = 1731307) B1731307
theorem B13850999 : Blo 1215425 13850999 := bstep (se 1 (by rfl) ⟨10388249, by rfl⟩ : syracuseStep 13850999 = 20776499) B20776499
theorem B4102703 : Blo 1215425 4102703 := bstep (se 1 (by rfl) ⟨3077027, by rfl⟩ : syracuseStep 4102703 = 6154055) B6154055
theorem B1825487 : Blo 1215425 1825487 := bstep (se 1 (by rfl) ⟨1369115, by rfl⟩ : syracuseStep 1825487 = 2738231) B2738231
theorem B2735081 : Blo 1215425 2735081 := bstep (se 2 (by rfl) ⟨1025655, by rfl⟩ : syracuseStep 2735081 = 2051311) B2051311
theorem B1825775 : Blo 1215425 1825775 := bstep (se 1 (by rfl) ⟨1369331, by rfl⟩ : syracuseStep 1825775 = 2738663) B2738663
theorem B11090951 : Blo 1215425 11090951 := bstep (se 1 (by rfl) ⟨8318213, by rfl⟩ : syracuseStep 11090951 = 16636427) B16636427
theorem B2735315 : Blo 1215425 2735315 := bstep (se 1 (by rfl) ⟨2051486, by rfl⟩ : syracuseStep 2735315 = 4102973) B4102973
theorem B1368175 : Blo 1215425 1368175 := bstep (se 1 (by rfl) ⟨1026131, by rfl⟩ : syracuseStep 1368175 = 2052263) B2052263
theorem B2737529 : Blo 1215425 2737529 := bstep (se 2 (by rfl) ⟨1026573, by rfl⟩ : syracuseStep 2737529 = 2053147) B2053147
theorem B11683399 : Blo 1215425 11683399 := bstep (se 1 (by rfl) ⟨8762549, by rfl⟩ : syracuseStep 11683399 = 17525099) B17525099
theorem B9233999 : Blo 1215425 9233999 := bstep (se 1 (by rfl) ⟨6925499, by rfl⟩ : syracuseStep 9233999 = 13850999) B13850999
theorem B3803051 : Blo 1215425 3803051 := bstep (se 1 (by rfl) ⟨2852288, by rfl⟩ : syracuseStep 3803051 = 5704577) B5704577
theorem B3697577 : Blo 1215425 3697577 := bstep (se 2 (by rfl) ⟨1386591, by rfl⟩ : syracuseStep 3697577 = 2773183) B2773183
theorem B1215727 : Blo 1215425 1215727 := bstep (se 1 (by rfl) ⟨911795, by rfl⟩ : syracuseStep 1215727 = 1823591) B1823591
theorem B14036287 : Blo 1215425 14036287 := bstep (se 1 (by rfl) ⟨10527215, by rfl⟩ : syracuseStep 14036287 = 21054431) B21054431
theorem B1215815 : Blo 1215425 1215815 := bstep (se 1 (by rfl) ⟨911861, by rfl⟩ : syracuseStep 1215815 = 1823723) B1823723
theorem B11685323 : Blo 1215425 11685323 := bstep (se 1 (by rfl) ⟨8763992, by rfl⟩ : syracuseStep 11685323 = 17527985) B17527985
theorem B1216359 : Blo 1215425 1216359 := bstep (se 1 (by rfl) ⟨912269, by rfl⟩ : syracuseStep 1216359 = 1824539) B1824539
theorem B4108265 : Blo 1215425 4108265 := bstep (se 2 (by rfl) ⟨1540599, by rfl⟩ : syracuseStep 4108265 = 3081199) B3081199
theorem B13856831 : Blo 1215425 13856831 := bstep (se 1 (by rfl) ⟨10392623, by rfl⟩ : syracuseStep 13856831 = 20785247) B20785247
theorem B1216991 : Blo 1215425 1216991 := bstep (se 1 (by rfl) ⟨912743, by rfl⟩ : syracuseStep 1216991 = 1825487) B1825487
theorem B1823387 : Blo 1215425 1823387 := bstep (se 1 (by rfl) ⟨1367540, by rfl⟩ : syracuseStep 1823387 = 2735081) B2735081
theorem B1217183 : Blo 1215425 1217183 := bstep (se 1 (by rfl) ⟨912887, by rfl⟩ : syracuseStep 1217183 = 1825775) B1825775
theorem B7393967 : Blo 1215425 7393967 := bstep (se 1 (by rfl) ⟨5545475, by rfl⟩ : syracuseStep 7393967 = 11090951) B11090951
theorem B1823543 : Blo 1215425 1823543 := bstep (se 1 (by rfl) ⟨1367657, by rfl⟩ : syracuseStep 1823543 = 2735315) B2735315
theorem B1824383 : Blo 1215425 1824383 := bstep (se 1 (by rfl) ⟨1368287, by rfl⟩ : syracuseStep 1824383 = 2736575) B2736575
theorem B3462887 : Blo 1215425 3462887 := bstep (se 1 (by rfl) ⟨2597165, by rfl⟩ : syracuseStep 3462887 = 5194331) B5194331
theorem B7796519 : Blo 1215425 7796519 := bstep (se 1 (by rfl) ⟨5847389, by rfl⟩ : syracuseStep 7796519 = 11694779) B11694779
theorem B1849835 : Blo 1215425 1849835 := bstep (se 1 (by rfl) ⟨1387376, by rfl⟩ : syracuseStep 1849835 = 2774753) B2774753
theorem B1538939 : Blo 1215425 1538939 := bstep (se 1 (by rfl) ⟨1154204, by rfl⟩ : syracuseStep 1538939 = 2308409) B2308409
theorem B2735135 : Blo 1215425 2735135 := bstep (se 1 (by rfl) ⟨2051351, by rfl⟩ : syracuseStep 2735135 = 4102703) B4102703
theorem B1825823 : Blo 1215425 1825823 := bstep (se 1 (by rfl) ⟨1369367, by rfl⟩ : syracuseStep 1825823 = 2738735) B2738735
theorem B1825919 : Blo 1215425 1825919 := bstep (se 1 (by rfl) ⟨1369439, by rfl⟩ : syracuseStep 1825919 = 2738879) B2738879
theorem B1825961 : Blo 1215425 1825961 := bstep (se 2 (by rfl) ⟨684735, by rfl⟩ : syracuseStep 1825961 = 1369471) B1369471
theorem B1367743 : Blo 1215425 1367743 := bstep (se 1 (by rfl) ⟨1025807, by rfl⟩ : syracuseStep 1367743 = 2051615) B2051615
theorem B4932893 : Blo 1215425 4932893 := bstep (se 3 (by rfl) ⟨924917, by rfl⟩ : syracuseStep 4932893 = 1849835) B1849835
theorem B2738843 : Blo 1215425 2738843 := bstep (se 1 (by rfl) ⟨2054132, by rfl⟩ : syracuseStep 2738843 = 4108265) B4108265
theorem B1215591 : Blo 1215425 1215591 := bstep (se 1 (by rfl) ⟨911693, by rfl⟩ : syracuseStep 1215591 = 1823387) B1823387
theorem B1215695 : Blo 1215425 1215695 := bstep (se 1 (by rfl) ⟨911771, by rfl⟩ : syracuseStep 1215695 = 1823543) B1823543
theorem B6155999 : Blo 1215425 6155999 := bstep (se 1 (by rfl) ⟨4616999, by rfl⟩ : syracuseStep 6155999 = 9233999) B9233999
theorem B1216255 : Blo 1215425 1216255 := bstep (se 1 (by rfl) ⟨912191, by rfl⟩ : syracuseStep 1216255 = 1824383) B1824383
theorem B5197679 : Blo 1215425 5197679 := bstep (se 1 (by rfl) ⟨3898259, by rfl⟩ : syracuseStep 5197679 = 7796519) B7796519
theorem B18715049 : Blo 1215425 18715049 := bstep (se 2 (by rfl) ⟨7018143, by rfl⟩ : syracuseStep 18715049 = 14036287) B14036287
theorem B1823423 : Blo 1215425 1823423 := bstep (se 1 (by rfl) ⟨1367567, by rfl⟩ : syracuseStep 1823423 = 2735135) B2735135
theorem B1217215 : Blo 1215425 1217215 := bstep (se 1 (by rfl) ⟨912911, by rfl⟩ : syracuseStep 1217215 = 1825823) B1825823
theorem B1217279 : Blo 1215425 1217279 := bstep (se 1 (by rfl) ⟨912959, by rfl⟩ : syracuseStep 1217279 = 1825919) B1825919
theorem B15577865 : Blo 1215425 15577865 := bstep (se 2 (by rfl) ⟨5841699, by rfl⟩ : syracuseStep 15577865 = 11683399) B11683399
theorem B1217307 : Blo 1215425 1217307 := bstep (se 1 (by rfl) ⟨912980, by rfl⟩ : syracuseStep 1217307 = 1825961) B1825961
theorem B1823657 : Blo 1215425 1823657 := bstep (se 2 (by rfl) ⟨683871, by rfl⟩ : syracuseStep 1823657 = 1367743) B1367743
theorem B9237887 : Blo 1215425 9237887 := bstep (se 1 (by rfl) ⟨6928415, by rfl⟩ : syracuseStep 9237887 = 13856831) B13856831
theorem B1824233 : Blo 1215425 1824233 := bstep (se 2 (by rfl) ⟨684087, by rfl⟩ : syracuseStep 1824233 = 1368175) B1368175
theorem B4929311 : Blo 1215425 4929311 := bstep (se 1 (by rfl) ⟨3696983, by rfl⟩ : syracuseStep 4929311 = 7393967) B7393967
theorem B1825019 : Blo 1215425 1825019 := bstep (se 1 (by rfl) ⟨1368764, by rfl⟩ : syracuseStep 1825019 = 2737529) B2737529
theorem B2308591 : Blo 1215425 2308591 := bstep (se 1 (by rfl) ⟨1731443, by rfl⟩ : syracuseStep 2308591 = 3462887) B3462887
theorem B2465051 : Blo 1215425 2465051 := bstep (se 1 (by rfl) ⟨1848788, by rfl⟩ : syracuseStep 2465051 = 3697577) B3697577
theorem B7790215 : Blo 1215425 7790215 := bstep (se 1 (by rfl) ⟨5842661, by rfl⟩ : syracuseStep 7790215 = 11685323) B11685323
theorem B4103837 : Blo 1215425 4103837 := bstep (se 3 (by rfl) ⟨769469, by rfl⟩ : syracuseStep 4103837 = 1538939) B1538939
theorem B10141469 : Blo 1215425 10141469 := bstep (se 3 (by rfl) ⟨1901525, by rfl⟩ : syracuseStep 10141469 = 3803051) B3803051
theorem B12476699 : Blo 1215425 12476699 := bstep (se 1 (by rfl) ⟨9357524, by rfl⟩ : syracuseStep 12476699 = 18715049) B18715049
theorem B3286207 : Blo 1215425 3286207 := bstep (se 1 (by rfl) ⟨2464655, by rfl⟩ : syracuseStep 3286207 = 4929311) B4929311
theorem B6760979 : Blo 1215425 6760979 := bstep (se 1 (by rfl) ⟨5070734, by rfl⟩ : syracuseStep 6760979 = 10141469) B10141469
theorem B1215615 : Blo 1215425 1215615 := bstep (se 1 (by rfl) ⟨911711, by rfl⟩ : syracuseStep 1215615 = 1823423) B1823423
theorem B1215771 : Blo 1215425 1215771 := bstep (se 1 (by rfl) ⟨911828, by rfl⟩ : syracuseStep 1215771 = 1823657) B1823657
theorem B6573469 : Blo 1215425 6573469 := bstep (se 3 (by rfl) ⟨1232525, by rfl⟩ : syracuseStep 6573469 = 2465051) B2465051
theorem B3288595 : Blo 1215425 3288595 := bstep (se 1 (by rfl) ⟨2466446, by rfl⟩ : syracuseStep 3288595 = 4932893) B4932893
theorem B1216155 : Blo 1215425 1216155 := bstep (se 1 (by rfl) ⟨912116, by rfl⟩ : syracuseStep 1216155 = 1824233) B1824233
theorem B1216679 : Blo 1215425 1216679 := bstep (se 1 (by rfl) ⟨912509, by rfl⟩ : syracuseStep 1216679 = 1825019) B1825019
theorem B10385243 : Blo 1215425 10385243 := bstep (se 1 (by rfl) ⟨7788932, by rfl⟩ : syracuseStep 10385243 = 15577865) B15577865
theorem B3078121 : Blo 1215425 3078121 := bstep (se 2 (by rfl) ⟨1154295, by rfl⟩ : syracuseStep 3078121 = 2308591) B2308591
theorem B6158591 : Blo 1215425 6158591 := bstep (se 1 (by rfl) ⟨4618943, by rfl⟩ : syracuseStep 6158591 = 9237887) B9237887
theorem B1825895 : Blo 1215425 1825895 := bstep (se 1 (by rfl) ⟨1369421, by rfl⟩ : syracuseStep 1825895 = 2738843) B2738843
theorem B10386953 : Blo 1215425 10386953 := bstep (se 2 (by rfl) ⟨3895107, by rfl⟩ : syracuseStep 10386953 = 7790215) B7790215
theorem B2735891 : Blo 1215425 2735891 := bstep (se 1 (by rfl) ⟨2051918, by rfl⟩ : syracuseStep 2735891 = 4103837) B4103837
theorem B4103999 : Blo 1215425 4103999 := bstep (se 1 (by rfl) ⟨3077999, by rfl⟩ : syracuseStep 4103999 = 6155999) B6155999
theorem B3465119 : Blo 1215425 3465119 := bstep (se 1 (by rfl) ⟨2598839, by rfl⟩ : syracuseStep 3465119 = 5197679) B5197679
theorem B6923495 : Blo 1215425 6923495 := bstep (se 1 (by rfl) ⟨5192621, by rfl⟩ : syracuseStep 6923495 = 10385243) B10385243
theorem B4105727 : Blo 1215425 4105727 := bstep (se 1 (by rfl) ⟨3079295, by rfl⟩ : syracuseStep 4105727 = 6158591) B6158591
theorem B4507319 : Blo 1215425 4507319 := bstep (se 1 (by rfl) ⟨3380489, by rfl⟩ : syracuseStep 4507319 = 6760979) B6760979
theorem B4384793 : Blo 1215425 4384793 := bstep (se 2 (by rfl) ⟨1644297, by rfl⟩ : syracuseStep 4384793 = 3288595) B3288595
theorem B6924635 : Blo 1215425 6924635 := bstep (se 1 (by rfl) ⟨5193476, by rfl⟩ : syracuseStep 6924635 = 10386953) B10386953
theorem B8317799 : Blo 1215425 8317799 := bstep (se 1 (by rfl) ⟨6238349, by rfl⟩ : syracuseStep 8317799 = 12476699) B12476699
theorem B1217263 : Blo 1215425 1217263 := bstep (se 1 (by rfl) ⟨912947, by rfl⟩ : syracuseStep 1217263 = 1825895) B1825895
theorem B1823927 : Blo 1215425 1823927 := bstep (se 1 (by rfl) ⟨1367945, by rfl⟩ : syracuseStep 1823927 = 2735891) B2735891
theorem B4381609 : Blo 1215425 4381609 := bstep (se 2 (by rfl) ⟨1643103, by rfl⟩ : syracuseStep 4381609 = 3286207) B3286207
theorem B8764625 : Blo 1215425 8764625 := bstep (se 2 (by rfl) ⟨3286734, by rfl⟩ : syracuseStep 8764625 = 6573469) B6573469
theorem B9240317 : Blo 1215425 9240317 := bstep (se 3 (by rfl) ⟨1732559, by rfl⟩ : syracuseStep 9240317 = 3465119) B3465119
theorem B2735999 : Blo 1215425 2735999 := bstep (se 1 (by rfl) ⟨2051999, by rfl⟩ : syracuseStep 2735999 = 4103999) B4103999
theorem B4104161 : Blo 1215425 4104161 := bstep (se 2 (by rfl) ⟨1539060, by rfl⟩ : syracuseStep 4104161 = 3078121) B3078121
theorem B23372333 : Blo 1215425 23372333 := bstep (se 3 (by rfl) ⟨4382312, by rfl⟩ : syracuseStep 23372333 = 8764625) B8764625
theorem B2737151 : Blo 1215425 2737151 := bstep (se 1 (by rfl) ⟨2052863, by rfl⟩ : syracuseStep 2737151 = 4105727) B4105727
theorem B5842145 : Blo 1215425 5842145 := bstep (se 2 (by rfl) ⟨2190804, by rfl⟩ : syracuseStep 5842145 = 4381609) B4381609
theorem B11692781 : Blo 1215425 11692781 := bstep (se 3 (by rfl) ⟨2192396, by rfl⟩ : syracuseStep 11692781 = 4384793) B4384793
theorem B1215951 : Blo 1215425 1215951 := bstep (se 1 (by rfl) ⟨911963, by rfl⟩ : syracuseStep 1215951 = 1823927) B1823927
theorem B4615663 : Blo 1215425 4615663 := bstep (se 1 (by rfl) ⟨3461747, by rfl⟩ : syracuseStep 4615663 = 6923495) B6923495
theorem B4616423 : Blo 1215425 4616423 := bstep (se 1 (by rfl) ⟨3462317, by rfl⟩ : syracuseStep 4616423 = 6924635) B6924635
theorem B1823999 : Blo 1215425 1823999 := bstep (se 1 (by rfl) ⟨1367999, by rfl⟩ : syracuseStep 1823999 = 2735999) B2735999
theorem B3004879 : Blo 1215425 3004879 := bstep (se 1 (by rfl) ⟨2253659, by rfl⟩ : syracuseStep 3004879 = 4507319) B4507319
theorem B5545199 : Blo 1215425 5545199 := bstep (se 1 (by rfl) ⟨4158899, by rfl⟩ : syracuseStep 5545199 = 8317799) B8317799
theorem B6160211 : Blo 1215425 6160211 := bstep (se 1 (by rfl) ⟨4620158, by rfl⟩ : syracuseStep 6160211 = 9240317) B9240317
theorem B2736107 : Blo 1215425 2736107 := bstep (se 1 (by rfl) ⟨2052080, by rfl⟩ : syracuseStep 2736107 = 4104161) B4104161
theorem B15581555 : Blo 1215425 15581555 := bstep (se 1 (by rfl) ⟨11686166, by rfl⟩ : syracuseStep 15581555 = 23372333) B23372333
theorem B4006505 : Blo 1215425 4006505 := bstep (se 2 (by rfl) ⟨1502439, by rfl⟩ : syracuseStep 4006505 = 3004879) B3004879
theorem B14787197 : Blo 1215425 14787197 := bstep (se 3 (by rfl) ⟨2772599, by rfl⟩ : syracuseStep 14787197 = 5545199) B5545199
theorem B6154217 : Blo 1215425 6154217 := bstep (se 2 (by rfl) ⟨2307831, by rfl⟩ : syracuseStep 6154217 = 4615663) B4615663
theorem B4106807 : Blo 1215425 4106807 := bstep (se 1 (by rfl) ⟨3080105, by rfl⟩ : syracuseStep 4106807 = 6160211) B6160211
theorem B3894763 : Blo 1215425 3894763 := bstep (se 1 (by rfl) ⟨2921072, by rfl⟩ : syracuseStep 3894763 = 5842145) B5842145
theorem B1215999 : Blo 1215425 1215999 := bstep (se 1 (by rfl) ⟨911999, by rfl⟩ : syracuseStep 1215999 = 1823999) B1823999
theorem B7795187 : Blo 1215425 7795187 := bstep (se 1 (by rfl) ⟨5846390, by rfl⟩ : syracuseStep 7795187 = 11692781) B11692781
theorem B1824071 : Blo 1215425 1824071 := bstep (se 1 (by rfl) ⟨1368053, by rfl⟩ : syracuseStep 1824071 = 2736107) B2736107
theorem B3077615 : Blo 1215425 3077615 := bstep (se 1 (by rfl) ⟨2308211, by rfl⟩ : syracuseStep 3077615 = 4616423) B4616423
theorem B1824767 : Blo 1215425 1824767 := bstep (se 1 (by rfl) ⟨1368575, by rfl⟩ : syracuseStep 1824767 = 2737151) B2737151
theorem B10387703 : Blo 1215425 10387703 := bstep (se 1 (by rfl) ⟨7790777, by rfl⟩ : syracuseStep 10387703 = 15581555) B15581555
theorem B2671003 : Blo 1215425 2671003 := bstep (se 1 (by rfl) ⟨2003252, by rfl⟩ : syracuseStep 2671003 = 4006505) B4006505
theorem B2737871 : Blo 1215425 2737871 := bstep (se 1 (by rfl) ⟨2053403, by rfl⟩ : syracuseStep 2737871 = 4106807) B4106807
theorem B5196791 : Blo 1215425 5196791 := bstep (se 1 (by rfl) ⟨3897593, by rfl⟩ : syracuseStep 5196791 = 7795187) B7795187
theorem B9858131 : Blo 1215425 9858131 := bstep (se 1 (by rfl) ⟨7393598, by rfl⟩ : syracuseStep 9858131 = 14787197) B14787197
theorem B1216047 : Blo 1215425 1216047 := bstep (se 1 (by rfl) ⟨912035, by rfl⟩ : syracuseStep 1216047 = 1824071) B1824071
theorem B2051743 : Blo 1215425 2051743 := bstep (se 1 (by rfl) ⟨1538807, by rfl⟩ : syracuseStep 2051743 = 3077615) B3077615
theorem B1216511 : Blo 1215425 1216511 := bstep (se 1 (by rfl) ⟨912383, by rfl⟩ : syracuseStep 1216511 = 1824767) B1824767
theorem B4102811 : Blo 1215425 4102811 := bstep (se 1 (by rfl) ⟨3077108, by rfl⟩ : syracuseStep 4102811 = 6154217) B6154217
theorem B5193017 : Blo 1215425 5193017 := bstep (se 2 (by rfl) ⟨1947381, by rfl⟩ : syracuseStep 5193017 = 3894763) B3894763
theorem B6572087 : Blo 1215425 6572087 := bstep (se 1 (by rfl) ⟨4929065, by rfl⟩ : syracuseStep 6572087 = 9858131) B9858131
theorem B6925135 : Blo 1215425 6925135 := bstep (se 1 (by rfl) ⟨5193851, by rfl⟩ : syracuseStep 6925135 = 10387703) B10387703
theorem B3462011 : Blo 1215425 3462011 := bstep (se 1 (by rfl) ⟨2596508, by rfl⟩ : syracuseStep 3462011 = 5193017) B5193017
theorem B3561337 : Blo 1215425 3561337 := bstep (se 2 (by rfl) ⟨1335501, by rfl⟩ : syracuseStep 3561337 = 2671003) B2671003
theorem B1825247 : Blo 1215425 1825247 := bstep (se 1 (by rfl) ⟨1368935, by rfl⟩ : syracuseStep 1825247 = 2737871) B2737871
theorem B2735207 : Blo 1215425 2735207 := bstep (se 1 (by rfl) ⟨2051405, by rfl⟩ : syracuseStep 2735207 = 4102811) B4102811
theorem B3464527 : Blo 1215425 3464527 := bstep (se 1 (by rfl) ⟨2598395, by rfl⟩ : syracuseStep 3464527 = 5196791) B5196791
theorem B2735657 : Blo 1215425 2735657 := bstep (se 2 (by rfl) ⟨1025871, by rfl⟩ : syracuseStep 2735657 = 2051743) B2051743
theorem B9233513 : Blo 1215425 9233513 := bstep (se 2 (by rfl) ⟨3462567, by rfl⟩ : syracuseStep 9233513 = 6925135) B6925135
theorem B1216831 : Blo 1215425 1216831 := bstep (se 1 (by rfl) ⟨912623, by rfl⟩ : syracuseStep 1216831 = 1825247) B1825247
theorem B18993797 : Blo 1215425 18993797 := bstep (se 4 (by rfl) ⟨1780668, by rfl⟩ : syracuseStep 18993797 = 3561337) B3561337
theorem B1823471 : Blo 1215425 1823471 := bstep (se 1 (by rfl) ⟨1367603, by rfl⟩ : syracuseStep 1823471 = 2735207) B2735207
theorem B1823771 : Blo 1215425 1823771 := bstep (se 1 (by rfl) ⟨1367828, by rfl⟩ : syracuseStep 1823771 = 2735657) B2735657
theorem B2308007 : Blo 1215425 2308007 := bstep (se 1 (by rfl) ⟨1731005, by rfl⟩ : syracuseStep 2308007 = 3462011) B3462011
theorem B4381391 : Blo 1215425 4381391 := bstep (se 1 (by rfl) ⟨3286043, by rfl⟩ : syracuseStep 4381391 = 6572087) B6572087
theorem B4619369 : Blo 1215425 4619369 := bstep (se 2 (by rfl) ⟨1732263, by rfl⟩ : syracuseStep 4619369 = 3464527) B3464527
theorem B1215647 : Blo 1215425 1215647 := bstep (se 1 (by rfl) ⟨911735, by rfl⟩ : syracuseStep 1215647 = 1823471) B1823471
theorem B1215847 : Blo 1215425 1215847 := bstep (se 1 (by rfl) ⟨911885, by rfl⟩ : syracuseStep 1215847 = 1823771) B1823771
theorem B6155675 : Blo 1215425 6155675 := bstep (se 1 (by rfl) ⟨4616756, by rfl⟩ : syracuseStep 6155675 = 9233513) B9233513
theorem B2920927 : Blo 1215425 2920927 := bstep (se 1 (by rfl) ⟨2190695, by rfl⟩ : syracuseStep 2920927 = 4381391) B4381391
theorem B12662531 : Blo 1215425 12662531 := bstep (se 1 (by rfl) ⟨9496898, by rfl⟩ : syracuseStep 12662531 = 18993797) B18993797
theorem B1538671 : Blo 1215425 1538671 := bstep (se 1 (by rfl) ⟨1154003, by rfl⟩ : syracuseStep 1538671 = 2308007) B2308007
theorem B3079579 : Blo 1215425 3079579 := bstep (se 1 (by rfl) ⟨2309684, by rfl⟩ : syracuseStep 3079579 = 4619369) B4619369
theorem B4106105 : Blo 1215425 4106105 := bstep (se 2 (by rfl) ⟨1539789, by rfl⟩ : syracuseStep 4106105 = 3079579) B3079579
theorem B3894569 : Blo 1215425 3894569 := bstep (se 2 (by rfl) ⟨1460463, by rfl⟩ : syracuseStep 3894569 = 2920927) B2920927
theorem B2051561 : Blo 1215425 2051561 := bstep (se 2 (by rfl) ⟨769335, by rfl⟩ : syracuseStep 2051561 = 1538671) B1538671
theorem B8441687 : Blo 1215425 8441687 := bstep (se 1 (by rfl) ⟨6331265, by rfl⟩ : syracuseStep 8441687 = 12662531) B12662531
theorem B4103783 : Blo 1215425 4103783 := bstep (se 1 (by rfl) ⟨3077837, by rfl⟩ : syracuseStep 4103783 = 6155675) B6155675
theorem B2737403 : Blo 1215425 2737403 := bstep (se 1 (by rfl) ⟨2053052, by rfl⟩ : syracuseStep 2737403 = 4106105) B4106105
theorem B2596379 : Blo 1215425 2596379 := bstep (se 1 (by rfl) ⟨1947284, by rfl⟩ : syracuseStep 2596379 = 3894569) B3894569
theorem B1367707 : Blo 1215425 1367707 := bstep (se 1 (by rfl) ⟨1025780, by rfl⟩ : syracuseStep 1367707 = 2051561) B2051561
theorem B2735855 : Blo 1215425 2735855 := bstep (se 1 (by rfl) ⟨2051891, by rfl⟩ : syracuseStep 2735855 = 4103783) B4103783
theorem B5627791 : Blo 1215425 5627791 := bstep (se 1 (by rfl) ⟨4220843, by rfl⟩ : syracuseStep 5627791 = 8441687) B8441687
theorem B6923677 : Blo 1215425 6923677 := bstep (se 3 (by rfl) ⟨1298189, by rfl⟩ : syracuseStep 6923677 = 2596379) B2596379
theorem B1823609 : Blo 1215425 1823609 := bstep (se 2 (by rfl) ⟨683853, by rfl⟩ : syracuseStep 1823609 = 1367707) B1367707
theorem B1823903 : Blo 1215425 1823903 := bstep (se 1 (by rfl) ⟨1367927, by rfl⟩ : syracuseStep 1823903 = 2735855) B2735855
theorem B1824935 : Blo 1215425 1824935 := bstep (se 1 (by rfl) ⟨1368701, by rfl⟩ : syracuseStep 1824935 = 2737403) B2737403
theorem B7503721 : Blo 1215425 7503721 := bstep (se 2 (by rfl) ⟨2813895, by rfl⟩ : syracuseStep 7503721 = 5627791) B5627791
theorem B40019845 : Blo 1215425 40019845 := bstep (se 4 (by rfl) ⟨3751860, by rfl⟩ : syracuseStep 40019845 = 7503721) B7503721
theorem B1215739 : Blo 1215425 1215739 := bstep (se 1 (by rfl) ⟨911804, by rfl⟩ : syracuseStep 1215739 = 1823609) B1823609
theorem B1215935 : Blo 1215425 1215935 := bstep (se 1 (by rfl) ⟨911951, by rfl⟩ : syracuseStep 1215935 = 1823903) B1823903
theorem B1216623 : Blo 1215425 1216623 := bstep (se 1 (by rfl) ⟨912467, by rfl⟩ : syracuseStep 1216623 = 1824935) B1824935
theorem B9231569 : Blo 1215425 9231569 := bstep (se 2 (by rfl) ⟨3461838, by rfl⟩ : syracuseStep 9231569 = 6923677) B6923677
theorem B6154379 : Blo 1215425 6154379 := bstep (se 1 (by rfl) ⟨4615784, by rfl⟩ : syracuseStep 6154379 = 9231569) B9231569
theorem B53359793 : Blo 1215425 53359793 := bstep (se 2 (by rfl) ⟨20009922, by rfl⟩ : syracuseStep 53359793 = 40019845) B40019845
theorem B35573195 : Blo 1215425 35573195 := bstep (se 1 (by rfl) ⟨26679896, by rfl⟩ : syracuseStep 35573195 = 53359793) B53359793
theorem B4102919 : Blo 1215425 4102919 := bstep (se 1 (by rfl) ⟨3077189, by rfl⟩ : syracuseStep 4102919 = 6154379) B6154379
theorem B2735279 : Blo 1215425 2735279 := bstep (se 1 (by rfl) ⟨2051459, by rfl⟩ : syracuseStep 2735279 = 4102919) B4102919
theorem B23715463 : Blo 1215425 23715463 := bstep (se 1 (by rfl) ⟨17786597, by rfl⟩ : syracuseStep 23715463 = 35573195) B35573195
theorem B1823519 : Blo 1215425 1823519 := bstep (se 1 (by rfl) ⟨1367639, by rfl⟩ : syracuseStep 1823519 = 2735279) B2735279
theorem B31620617 : Blo 1215425 31620617 := bstep (se 2 (by rfl) ⟨11857731, by rfl⟩ : syracuseStep 31620617 = 23715463) B23715463
theorem B21080411 : Blo 1215425 21080411 := bstep (se 1 (by rfl) ⟨15810308, by rfl⟩ : syracuseStep 21080411 = 31620617) B31620617
theorem B1215679 : Blo 1215425 1215679 := bstep (se 1 (by rfl) ⟨911759, by rfl⟩ : syracuseStep 1215679 = 1823519) B1823519
theorem B14053607 : Blo 1215425 14053607 := bstep (se 1 (by rfl) ⟨10540205, by rfl⟩ : syracuseStep 14053607 = 21080411) B21080411
theorem B9369071 : Blo 1215425 9369071 := bstep (se 1 (by rfl) ⟨7026803, by rfl⟩ : syracuseStep 9369071 = 14053607) B14053607
theorem B6246047 : Blo 1215425 6246047 := bstep (se 1 (by rfl) ⟨4684535, by rfl⟩ : syracuseStep 6246047 = 9369071) B9369071
theorem B4164031 : Blo 1215425 4164031 := bstep (se 1 (by rfl) ⟨3123023, by rfl⟩ : syracuseStep 4164031 = 6246047) B6246047
theorem B22208165 : Blo 1215425 22208165 := bstep (se 4 (by rfl) ⟨2082015, by rfl⟩ : syracuseStep 22208165 = 4164031) B4164031
theorem B14805443 : Blo 1215425 14805443 := bstep (se 1 (by rfl) ⟨11104082, by rfl⟩ : syracuseStep 14805443 = 22208165) B22208165
theorem B39481181 : Blo 1215425 39481181 := bstep (se 3 (by rfl) ⟨7402721, by rfl⟩ : syracuseStep 39481181 = 14805443) B14805443
theorem B26320787 : Blo 1215425 26320787 := bstep (se 1 (by rfl) ⟨19740590, by rfl⟩ : syracuseStep 26320787 = 39481181) B39481181
theorem B17547191 : Blo 1215425 17547191 := bstep (se 1 (by rfl) ⟨13160393, by rfl⟩ : syracuseStep 17547191 = 26320787) B26320787
theorem B11698127 : Blo 1215425 11698127 := bstep (se 1 (by rfl) ⟨8773595, by rfl⟩ : syracuseStep 11698127 = 17547191) B17547191
theorem B7798751 : Blo 1215425 7798751 := bstep (se 1 (by rfl) ⟨5849063, by rfl⟩ : syracuseStep 7798751 = 11698127) B11698127
theorem B5199167 : Blo 1215425 5199167 := bstep (se 1 (by rfl) ⟨3899375, by rfl⟩ : syracuseStep 5199167 = 7798751) B7798751
theorem B3466111 : Blo 1215425 3466111 := bstep (se 1 (by rfl) ⟨2599583, by rfl⟩ : syracuseStep 3466111 = 5199167) B5199167
theorem B4621481 : Blo 1215425 4621481 := bstep (se 2 (by rfl) ⟨1733055, by rfl⟩ : syracuseStep 4621481 = 3466111) B3466111
theorem B3080987 : Blo 1215425 3080987 := bstep (se 1 (by rfl) ⟨2310740, by rfl⟩ : syracuseStep 3080987 = 4621481) B4621481
theorem B2053991 : Blo 1215425 2053991 := bstep (se 1 (by rfl) ⟨1540493, by rfl⟩ : syracuseStep 2053991 = 3080987) B3080987
theorem B1369327 : Blo 1215425 1369327 := bstep (se 1 (by rfl) ⟨1026995, by rfl⟩ : syracuseStep 1369327 = 2053991) B2053991
theorem B1825769 : Blo 1215425 1825769 := bstep (se 2 (by rfl) ⟨684663, by rfl⟩ : syracuseStep 1825769 = 1369327) B1369327
theorem B1217179 : Blo 1215425 1217179 := bstep (se 1 (by rfl) ⟨912884, by rfl⟩ : syracuseStep 1217179 = 1825769) B1825769

theorem C0 (j : ℕ) (h1 : 303856 ≤ j) (h2 : j ≤ 304355) : Blo 1215425 (4 * j + 3) := by
  interval_cases j
  · exact B1215427
  · exact B1215431
  · exact B1215435
  · exact B1215439
  · exact B1215443
  · exact B1215447
  · exact B1215451
  · exact B1215455
  · exact B1215459
  · exact B1215463
  · exact B1215467
  · exact B1215471
  · exact B1215475
  · exact B1215479
  · exact B1215483
  · exact B1215487
  · exact B1215491
  · exact B1215495
  · exact B1215499
  · exact B1215503
  · exact B1215507
  · exact B1215511
  · exact B1215515
  · exact B1215519
  · exact B1215523
  · exact B1215527
  · exact B1215531
  · exact B1215535
  · exact B1215539
  · exact B1215543
  · exact B1215547
  · exact B1215551
  · exact B1215555
  · exact B1215559
  · exact B1215563
  · exact B1215567
  · exact B1215571
  · exact B1215575
  · exact B1215579
  · exact B1215583
  · exact B1215587
  · exact B1215591
  · exact B1215595
  · exact B1215599
  · exact B1215603
  · exact B1215607
  · exact B1215611
  · exact B1215615
  · exact B1215619
  · exact B1215623
  · exact B1215627
  · exact B1215631
  · exact B1215635
  · exact B1215639
  · exact B1215643
  · exact B1215647
  · exact B1215651
  · exact B1215655
  · exact B1215659
  · exact B1215663
  · exact B1215667
  · exact B1215671
  · exact B1215675
  · exact B1215679
  · exact B1215683
  · exact B1215687
  · exact B1215691
  · exact B1215695
  · exact B1215699
  · exact B1215703
  · exact B1215707
  · exact B1215711
  · exact B1215715
  · exact B1215719
  · exact B1215723
  · exact B1215727
  · exact B1215731
  · exact B1215735
  · exact B1215739
  · exact B1215743
  · exact B1215747
  · exact B1215751
  · exact B1215755
  · exact B1215759
  · exact B1215763
  · exact B1215767
  · exact B1215771
  · exact B1215775
  · exact B1215779
  · exact B1215783
  · exact B1215787
  · exact B1215791
  · exact B1215795
  · exact B1215799
  · exact B1215803
  · exact B1215807
  · exact B1215811
  · exact B1215815
  · exact B1215819
  · exact B1215823
  · exact B1215827
  · exact B1215831
  · exact B1215835
  · exact B1215839
  · exact B1215843
  · exact B1215847
  · exact B1215851
  · exact B1215855
  · exact B1215859
  · exact B1215863
  · exact B1215867
  · exact B1215871
  · exact B1215875
  · exact B1215879
  · exact B1215883
  · exact B1215887
  · exact B1215891
  · exact B1215895
  · exact B1215899
  · exact B1215903
  · exact B1215907
  · exact B1215911
  · exact B1215915
  · exact B1215919
  · exact B1215923
  · exact B1215927
  · exact B1215931
  · exact B1215935
  · exact B1215939
  · exact B1215943
  · exact B1215947
  · exact B1215951
  · exact B1215955
  · exact B1215959
  · exact B1215963
  · exact B1215967
  · exact B1215971
  · exact B1215975
  · exact B1215979
  · exact B1215983
  · exact B1215987
  · exact B1215991
  · exact B1215995
  · exact B1215999
  · exact B1216003
  · exact B1216007
  · exact B1216011
  · exact B1216015
  · exact B1216019
  · exact B1216023
  · exact B1216027
  · exact B1216031
  · exact B1216035
  · exact B1216039
  · exact B1216043
  · exact B1216047
  · exact B1216051
  · exact B1216055
  · exact B1216059
  · exact B1216063
  · exact B1216067
  · exact B1216071
  · exact B1216075
  · exact B1216079
  · exact B1216083
  · exact B1216087
  · exact B1216091
  · exact B1216095
  · exact B1216099
  · exact B1216103
  · exact B1216107
  · exact B1216111
  · exact B1216115
  · exact B1216119
  · exact B1216123
  · exact B1216127
  · exact B1216131
  · exact B1216135
  · exact B1216139
  · exact B1216143
  · exact B1216147
  · exact B1216151
  · exact B1216155
  · exact B1216159
  · exact B1216163
  · exact B1216167
  · exact B1216171
  · exact B1216175
  · exact B1216179
  · exact B1216183
  · exact B1216187
  · exact B1216191
  · exact B1216195
  · exact B1216199
  · exact B1216203
  · exact B1216207
  · exact B1216211
  · exact B1216215
  · exact B1216219
  · exact B1216223
  · exact B1216227
  · exact B1216231
  · exact B1216235
  · exact B1216239
  · exact B1216243
  · exact B1216247
  · exact B1216251
  · exact B1216255
  · exact B1216259
  · exact B1216263
  · exact B1216267
  · exact B1216271
  · exact B1216275
  · exact B1216279
  · exact B1216283
  · exact B1216287
  · exact B1216291
  · exact B1216295
  · exact B1216299
  · exact B1216303
  · exact B1216307
  · exact B1216311
  · exact B1216315
  · exact B1216319
  · exact B1216323
  · exact B1216327
  · exact B1216331
  · exact B1216335
  · exact B1216339
  · exact B1216343
  · exact B1216347
  · exact B1216351
  · exact B1216355
  · exact B1216359
  · exact B1216363
  · exact B1216367
  · exact B1216371
  · exact B1216375
  · exact B1216379
  · exact B1216383
  · exact B1216387
  · exact B1216391
  · exact B1216395
  · exact B1216399
  · exact B1216403
  · exact B1216407
  · exact B1216411
  · exact B1216415
  · exact B1216419
  · exact B1216423
  · exact B1216427
  · exact B1216431
  · exact B1216435
  · exact B1216439
  · exact B1216443
  · exact B1216447
  · exact B1216451
  · exact B1216455
  · exact B1216459
  · exact B1216463
  · exact B1216467
  · exact B1216471
  · exact B1216475
  · exact B1216479
  · exact B1216483
  · exact B1216487
  · exact B1216491
  · exact B1216495
  · exact B1216499
  · exact B1216503
  · exact B1216507
  · exact B1216511
  · exact B1216515
  · exact B1216519
  · exact B1216523
  · exact B1216527
  · exact B1216531
  · exact B1216535
  · exact B1216539
  · exact B1216543
  · exact B1216547
  · exact B1216551
  · exact B1216555
  · exact B1216559
  · exact B1216563
  · exact B1216567
  · exact B1216571
  · exact B1216575
  · exact B1216579
  · exact B1216583
  · exact B1216587
  · exact B1216591
  · exact B1216595
  · exact B1216599
  · exact B1216603
  · exact B1216607
  · exact B1216611
  · exact B1216615
  · exact B1216619
  · exact B1216623
  · exact B1216627
  · exact B1216631
  · exact B1216635
  · exact B1216639
  · exact B1216643
  · exact B1216647
  · exact B1216651
  · exact B1216655
  · exact B1216659
  · exact B1216663
  · exact B1216667
  · exact B1216671
  · exact B1216675
  · exact B1216679
  · exact B1216683
  · exact B1216687
  · exact B1216691
  · exact B1216695
  · exact B1216699
  · exact B1216703
  · exact B1216707
  · exact B1216711
  · exact B1216715
  · exact B1216719
  · exact B1216723
  · exact B1216727
  · exact B1216731
  · exact B1216735
  · exact B1216739
  · exact B1216743
  · exact B1216747
  · exact B1216751
  · exact B1216755
  · exact B1216759
  · exact B1216763
  · exact B1216767
  · exact B1216771
  · exact B1216775
  · exact B1216779
  · exact B1216783
  · exact B1216787
  · exact B1216791
  · exact B1216795
  · exact B1216799
  · exact B1216803
  · exact B1216807
  · exact B1216811
  · exact B1216815
  · exact B1216819
  · exact B1216823
  · exact B1216827
  · exact B1216831
  · exact B1216835
  · exact B1216839
  · exact B1216843
  · exact B1216847
  · exact B1216851
  · exact B1216855
  · exact B1216859
  · exact B1216863
  · exact B1216867
  · exact B1216871
  · exact B1216875
  · exact B1216879
  · exact B1216883
  · exact B1216887
  · exact B1216891
  · exact B1216895
  · exact B1216899
  · exact B1216903
  · exact B1216907
  · exact B1216911
  · exact B1216915
  · exact B1216919
  · exact B1216923
  · exact B1216927
  · exact B1216931
  · exact B1216935
  · exact B1216939
  · exact B1216943
  · exact B1216947
  · exact B1216951
  · exact B1216955
  · exact B1216959
  · exact B1216963
  · exact B1216967
  · exact B1216971
  · exact B1216975
  · exact B1216979
  · exact B1216983
  · exact B1216987
  · exact B1216991
  · exact B1216995
  · exact B1216999
  · exact B1217003
  · exact B1217007
  · exact B1217011
  · exact B1217015
  · exact B1217019
  · exact B1217023
  · exact B1217027
  · exact B1217031
  · exact B1217035
  · exact B1217039
  · exact B1217043
  · exact B1217047
  · exact B1217051
  · exact B1217055
  · exact B1217059
  · exact B1217063
  · exact B1217067
  · exact B1217071
  · exact B1217075
  · exact B1217079
  · exact B1217083
  · exact B1217087
  · exact B1217091
  · exact B1217095
  · exact B1217099
  · exact B1217103
  · exact B1217107
  · exact B1217111
  · exact B1217115
  · exact B1217119
  · exact B1217123
  · exact B1217127
  · exact B1217131
  · exact B1217135
  · exact B1217139
  · exact B1217143
  · exact B1217147
  · exact B1217151
  · exact B1217155
  · exact B1217159
  · exact B1217163
  · exact B1217167
  · exact B1217171
  · exact B1217175
  · exact B1217179
  · exact B1217183
  · exact B1217187
  · exact B1217191
  · exact B1217195
  · exact B1217199
  · exact B1217203
  · exact B1217207
  · exact B1217211
  · exact B1217215
  · exact B1217219
  · exact B1217223
  · exact B1217227
  · exact B1217231
  · exact B1217235
  · exact B1217239
  · exact B1217243
  · exact B1217247
  · exact B1217251
  · exact B1217255
  · exact B1217259
  · exact B1217263
  · exact B1217267
  · exact B1217271
  · exact B1217275
  · exact B1217279
  · exact B1217283
  · exact B1217287
  · exact B1217291
  · exact B1217295
  · exact B1217299
  · exact B1217303
  · exact B1217307
  · exact B1217311
  · exact B1217315
  · exact B1217319
  · exact B1217323
  · exact B1217327
  · exact B1217331
  · exact B1217335
  · exact B1217339
  · exact B1217343
  · exact B1217347
  · exact B1217351
  · exact B1217355
  · exact B1217359
  · exact B1217363
  · exact B1217367
  · exact B1217371
  · exact B1217375
  · exact B1217379
  · exact B1217383
  · exact B1217387
  · exact B1217391
  · exact B1217395
  · exact B1217399
  · exact B1217403
  · exact B1217407
  · exact B1217411
  · exact B1217415
  · exact B1217419
  · exact B1217423

theorem solution (m : ℕ) (hlo : 1215425 ≤ m) (hhi : m ≤ 1217425) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 303856 ≤ j := by omega
    have hj2 : j ≤ 304355 := by omega
    have hb : Blo 1215425 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
