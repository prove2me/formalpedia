-- Prove2me | solution 1 for syracuse_reaches_one_below_99781
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T07:01:29.899352+00:00
-- url     : https://prove2.me/submissions/ab7c190d-a1bb-4e3c-85cd-9df5f2a33e4b

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_99132

set_option maxHeartbeats 1000000

open Nat

abbrev Reach (n : ℕ) : Prop := ∃ j : ℕ, syracuseStep^[j] n = 1

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]

theorem rs {x y : ℕ} (h : syracuseStep x = y) (hy : Reach y) : Reach x := by
  obtain ⟨j, hj⟩ := hy
  exact ⟨j + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact hj⟩

/-- Everything below the previously verified bound is already known to reach 1. -/
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 99131) : Reach n :=
  syracuse_reaches_one_below_99132 n h1 h2 h3
theorem R223253 : Reach 223253 := rs (se 6 (by rfl) ⟨5232, by rfl⟩) (B 10465 (by norm_num) ⟨5232, by rfl⟩ (by norm_num))
theorem R149525 : Reach 149525 := rs (se 6 (by rfl) ⟨3504, by rfl⟩) (B 7009 (by norm_num) ⟨3504, by rfl⟩ (by norm_num))
theorem R149549 : Reach 149549 := rs (se 3 (by rfl) ⟨28040, by rfl⟩) (B 56081 (by norm_num) ⟨28040, by rfl⟩ (by norm_num))
theorem R188477 : Reach 188477 := rs (se 3 (by rfl) ⟨35339, by rfl⟩) (B 70679 (by norm_num) ⟨35339, by rfl⟩ (by norm_num))
theorem R149573 : Reach 149573 := rs (se 4 (by rfl) ⟨14022, by rfl⟩) (B 28045 (by norm_num) ⟨14022, by rfl⟩ (by norm_num))
theorem R251981 : Reach 251981 := rs (se 3 (by rfl) ⟨47246, by rfl⟩) (B 94493 (by norm_num) ⟨47246, by rfl⟩ (by norm_num))
theorem R286805 : Reach 286805 := rs (se 8 (by rfl) ⟨1680, by rfl⟩) (B 3361 (by norm_num) ⟨1680, by rfl⟩ (by norm_num))
theorem R223325 : Reach 223325 := rs (se 3 (by rfl) ⟨41873, by rfl⟩) (B 83747 (by norm_num) ⟨41873, by rfl⟩ (by norm_num))
theorem R149597 : Reach 149597 := rs (se 3 (by rfl) ⟨28049, by rfl⟩) (B 56099 (by norm_num) ⟨28049, by rfl⟩ (by norm_num))
theorem R114797 : Reach 114797 := rs (se 3 (by rfl) ⟨21524, by rfl⟩) (B 43049 (by norm_num) ⟨21524, by rfl⟩ (by norm_num))
theorem R141421 : Reach 141421 := rs (se 3 (by rfl) ⟨26516, by rfl⟩) (B 53033 (by norm_num) ⟨26516, by rfl⟩ (by norm_num))
theorem R149621 : Reach 149621 := rs (se 5 (by rfl) ⟨7013, by rfl⟩) (B 14027 (by norm_num) ⟨7013, by rfl⟩ (by norm_num))
theorem R168061 : Reach 168061 := rs (se 3 (by rfl) ⟨31511, by rfl⟩) (B 63023 (by norm_num) ⟨31511, by rfl⟩ (by norm_num))
theorem R149645 : Reach 149645 := rs (se 3 (by rfl) ⟨28058, by rfl⟩) (B 56117 (by norm_num) ⟨28058, by rfl⟩ (by norm_num))
theorem R223397 : Reach 223397 := rs (se 4 (by rfl) ⟨20943, by rfl⟩) (B 41887 (by norm_num) ⟨20943, by rfl⟩ (by norm_num))
theorem R149669 : Reach 149669 := rs (se 4 (by rfl) ⟨14031, by rfl⟩) (B 28063 (by norm_num) ⟨14031, by rfl⟩ (by norm_num))
theorem R317621 : Reach 317621 := rs (se 5 (by rfl) ⟨14888, by rfl⟩) (B 29777 (by norm_num) ⟨14888, by rfl⟩ (by norm_num))
theorem R141517 : Reach 141517 := rs (se 3 (by rfl) ⟨26534, by rfl⟩) (B 53069 (by norm_num) ⟨26534, by rfl⟩ (by norm_num))
theorem R377045 : Reach 377045 := rs (se 7 (by rfl) ⟨4418, by rfl⟩) (B 8837 (by norm_num) ⟨4418, by rfl⟩ (by norm_num))
theorem R168149 : Reach 168149 := rs (se 7 (by rfl) ⟨1970, by rfl⟩) (B 3941 (by norm_num) ⟨1970, by rfl⟩ (by norm_num))
theorem R223469 : Reach 223469 := rs (se 3 (by rfl) ⟨41900, by rfl⟩) (B 83801 (by norm_num) ⟨41900, by rfl⟩ (by norm_num))
theorem R252173 : Reach 252173 := rs (se 3 (by rfl) ⟨47282, by rfl⟩) (B 94565 (by norm_num) ⟨47282, by rfl⟩ (by norm_num))
theorem R502037 : Reach 502037 := rs (se 6 (by rfl) ⟨11766, by rfl⟩) (B 23533 (by norm_num) ⟨11766, by rfl⟩ (by norm_num))
theorem R336149 : Reach 336149 := rs (se 6 (by rfl) ⟨7878, by rfl⟩) (B 15757 (by norm_num) ⟨7878, by rfl⟩ (by norm_num))
theorem R223541 : Reach 223541 := rs (se 5 (by rfl) ⟨10478, by rfl⟩) (B 20957 (by norm_num) ⟨10478, by rfl⟩ (by norm_num))
theorem R637237 : Reach 637237 := rs (se 5 (by rfl) ⟨29870, by rfl⟩) (B 59741 (by norm_num) ⟨29870, by rfl⟩ (by norm_num))
theorem R201037 : Reach 201037 := rs (se 3 (by rfl) ⟨37694, by rfl⟩) (B 75389 (by norm_num) ⟨37694, by rfl⟩ (by norm_num))
theorem R168277 : Reach 168277 := rs (se 10 (by rfl) ⟨246, by rfl⟩) (B 493 (by norm_num) ⟨246, by rfl⟩ (by norm_num))
theorem R223613 : Reach 223613 := rs (se 3 (by rfl) ⟨41927, by rfl⟩) (B 83855 (by norm_num) ⟨41927, by rfl⟩ (by norm_num))
theorem R168365 : Reach 168365 := rs (se 3 (by rfl) ⟨31568, by rfl⟩) (B 63137 (by norm_num) ⟨31568, by rfl⟩ (by norm_num))
theorem R223685 : Reach 223685 := rs (se 4 (by rfl) ⟨20970, by rfl⟩) (B 41941 (by norm_num) ⟨20970, by rfl⟩ (by norm_num))
theorem R807413 : Reach 807413 := rs (se 5 (by rfl) ⟨37847, by rfl⟩) (B 75695 (by norm_num) ⟨37847, by rfl⟩ (by norm_num))
theorem R223757 : Reach 223757 := rs (se 3 (by rfl) ⟨41954, by rfl⟩) (B 83909 (by norm_num) ⟨41954, by rfl⟩ (by norm_num))
theorem R125489 : Reach 125489 := rs (se 2 (by rfl) ⟨47058, by rfl⟩) (B 94117 (by norm_num) ⟨47058, by rfl⟩ (by norm_num))
theorem R149501 : Reach 149501 := rs (se 3 (by rfl) ⟨28031, by rfl⟩) (B 56063 (by norm_num) ⟨28031, by rfl⟩ (by norm_num))
theorem R453205 : Reach 453205 := rs (se 8 (by rfl) ⟨2655, by rfl⟩) (B 5311 (by norm_num) ⟨2655, by rfl⟩ (by norm_num))
theorem R223829 : Reach 223829 := rs (se 8 (by rfl) ⟨1311, by rfl⟩) (B 2623 (by norm_num) ⟨1311, by rfl⟩ (by norm_num))
theorem R252517 : Reach 252517 := rs (se 4 (by rfl) ⟨23673, by rfl⟩) (B 47347 (by norm_num) ⟨23673, by rfl⟩ (by norm_num))
theorem R125545 : Reach 125545 := rs (se 2 (by rfl) ⟨47079, by rfl⟩) (B 94159 (by norm_num) ⟨47079, by rfl⟩ (by norm_num))
theorem R113269 : Reach 113269 := rs (se 5 (by rfl) ⟨5309, by rfl⟩) (B 10619 (by norm_num) ⟨5309, by rfl⟩ (by norm_num))
theorem R101017 : Reach 101017 := rs (se 2 (by rfl) ⟨37881, by rfl⟩) (B 75763 (by norm_num) ⟨37881, by rfl⟩ (by norm_num))
theorem R223901 : Reach 223901 := rs (se 3 (by rfl) ⟨41981, by rfl⟩) (B 83963 (by norm_num) ⟨41981, by rfl⟩ (by norm_num))
theorem R221869 : Reach 221869 := rs (se 3 (by rfl) ⟨41600, by rfl⟩) (B 83201 (by norm_num) ⟨41600, by rfl⟩ (by norm_num))
theorem R142013 : Reach 142013 := rs (se 3 (by rfl) ⟨26627, by rfl⟩) (B 53255 (by norm_num) ⟨26627, by rfl⟩ (by norm_num))
theorem R336581 : Reach 336581 := rs (se 4 (by rfl) ⟨31554, by rfl⟩) (B 63109 (by norm_num) ⟨31554, by rfl⟩ (by norm_num))
theorem R125641 : Reach 125641 := rs (se 2 (by rfl) ⟨47115, by rfl⟩) (B 94231 (by norm_num) ⟨47115, by rfl⟩ (by norm_num))
theorem R2730709 : Reach 2730709 := rs (se 7 (by rfl) ⟨32000, by rfl⟩) (B 64001 (by norm_num) ⟨32000, by rfl⟩ (by norm_num))
theorem R223973 : Reach 223973 := rs (se 4 (by rfl) ⟨20997, by rfl⟩) (B 41995 (by norm_num) ⟨20997, by rfl⟩ (by norm_num))
theorem R238349 : Reach 238349 := rs (se 3 (by rfl) ⟨44690, by rfl⟩) (B 89381 (by norm_num) ⟨44690, by rfl⟩ (by norm_num))
theorem R224045 : Reach 224045 := rs (se 3 (by rfl) ⟨42008, by rfl⟩) (B 84017 (by norm_num) ⟨42008, by rfl⟩ (by norm_num))
theorem R189229 : Reach 189229 := rs (se 3 (by rfl) ⟨35480, by rfl⟩) (B 70961 (by norm_num) ⟨35480, by rfl⟩ (by norm_num))
theorem R424757 : Reach 424757 := rs (se 5 (by rfl) ⟨19910, by rfl⟩) (B 39821 (by norm_num) ⟨19910, by rfl⟩ (by norm_num))
theorem R283445 : Reach 283445 := rs (se 5 (by rfl) ⟨13286, by rfl⟩) (B 26573 (by norm_num) ⟨13286, by rfl⟩ (by norm_num))
theorem R504629 : Reach 504629 := rs (se 5 (by rfl) ⟨23654, by rfl⟩) (B 47309 (by norm_num) ⟨23654, by rfl⟩ (by norm_num))
theorem R99133 : Reach 99133 := rs (se 3 (by rfl) ⟨18587, by rfl⟩) (B 37175 (by norm_num) ⟨18587, by rfl⟩ (by norm_num))
theorem R99137 : Reach 99137 := rs (se 2 (by rfl) ⟨37176, by rfl⟩) (B 74353 (by norm_num) ⟨37176, by rfl⟩ (by norm_num))
theorem R99141 : Reach 99141 := rs (se 4 (by rfl) ⟨9294, by rfl⟩) (B 18589 (by norm_num) ⟨9294, by rfl⟩ (by norm_num))
theorem R99145 : Reach 99145 := rs (se 2 (by rfl) ⟨37179, by rfl⟩) (B 74359 (by norm_num) ⟨37179, by rfl⟩ (by norm_num))
theorem R99149 : Reach 99149 := rs (se 3 (by rfl) ⟨18590, by rfl⟩) (B 37181 (by norm_num) ⟨18590, by rfl⟩ (by norm_num))
theorem R99153 : Reach 99153 := rs (se 2 (by rfl) ⟨37182, by rfl⟩) (B 74365 (by norm_num) ⟨37182, by rfl⟩ (by norm_num))
theorem R99157 : Reach 99157 := rs (se 9 (by rfl) ⟨290, by rfl⟩) (B 581 (by norm_num) ⟨290, by rfl⟩ (by norm_num))
theorem R99161 : Reach 99161 := rs (se 2 (by rfl) ⟨37185, by rfl⟩) (B 74371 (by norm_num) ⟨37185, by rfl⟩ (by norm_num))
theorem R107353 : Reach 107353 := rs (se 2 (by rfl) ⟨40257, by rfl⟩) (B 80515 (by norm_num) ⟨40257, by rfl⟩ (by norm_num))
theorem R99165 : Reach 99165 := rs (se 3 (by rfl) ⟨18593, by rfl⟩) (B 37187 (by norm_num) ⟨18593, by rfl⟩ (by norm_num))
theorem R99169 : Reach 99169 := rs (se 2 (by rfl) ⟨37188, by rfl⟩) (B 74377 (by norm_num) ⟨37188, by rfl⟩ (by norm_num))
theorem R99173 : Reach 99173 := rs (se 4 (by rfl) ⟨9297, by rfl⟩) (B 18595 (by norm_num) ⟨9297, by rfl⟩ (by norm_num))
theorem R99177 : Reach 99177 := rs (se 2 (by rfl) ⟨37191, by rfl⟩) (B 74383 (by norm_num) ⟨37191, by rfl⟩ (by norm_num))
theorem R99181 : Reach 99181 := rs (se 3 (by rfl) ⟨18596, by rfl⟩) (B 37193 (by norm_num) ⟨18596, by rfl⟩ (by norm_num))
theorem R99185 : Reach 99185 := rs (se 2 (by rfl) ⟨37194, by rfl⟩) (B 74389 (by norm_num) ⟨37194, by rfl⟩ (by norm_num))
theorem R99189 : Reach 99189 := rs (se 5 (by rfl) ⟨4649, by rfl⟩) (B 9299 (by norm_num) ⟨4649, by rfl⟩ (by norm_num))
theorem R125813 : Reach 125813 := rs (se 5 (by rfl) ⟨5897, by rfl⟩) (B 11795 (by norm_num) ⟨5897, by rfl⟩ (by norm_num))
theorem R224117 : Reach 224117 := rs (se 5 (by rfl) ⟨10505, by rfl⟩) (B 21011 (by norm_num) ⟨10505, by rfl⟩ (by norm_num))
theorem R99193 : Reach 99193 := rs (se 2 (by rfl) ⟨37197, by rfl⟩) (B 74395 (by norm_num) ⟨37197, by rfl⟩ (by norm_num))
theorem R99197 : Reach 99197 := rs (se 3 (by rfl) ⟨18599, by rfl⟩) (B 37199 (by norm_num) ⟨18599, by rfl⟩ (by norm_num))
theorem R99201 : Reach 99201 := rs (se 2 (by rfl) ⟨37200, by rfl⟩) (B 74401 (by norm_num) ⟨37200, by rfl⟩ (by norm_num))
theorem R99205 : Reach 99205 := rs (se 4 (by rfl) ⟨9300, by rfl⟩) (B 18601 (by norm_num) ⟨9300, by rfl⟩ (by norm_num))
theorem R99209 : Reach 99209 := rs (se 2 (by rfl) ⟨37203, by rfl⟩) (B 74407 (by norm_num) ⟨37203, by rfl⟩ (by norm_num))
theorem R99213 : Reach 99213 := rs (se 3 (by rfl) ⟨18602, by rfl⟩) (B 37205 (by norm_num) ⟨18602, by rfl⟩ (by norm_num))
theorem R99217 : Reach 99217 := rs (se 2 (by rfl) ⟨37206, by rfl⟩) (B 74413 (by norm_num) ⟨37206, by rfl⟩ (by norm_num))
theorem R99221 : Reach 99221 := rs (se 6 (by rfl) ⟨2325, by rfl⟩) (B 4651 (by norm_num) ⟨2325, by rfl⟩ (by norm_num))
theorem R99225 : Reach 99225 := rs (se 2 (by rfl) ⟨37209, by rfl⟩) (B 74419 (by norm_num) ⟨37209, by rfl⟩ (by norm_num))
theorem R99229 : Reach 99229 := rs (se 3 (by rfl) ⟨18605, by rfl⟩) (B 37211 (by norm_num) ⟨18605, by rfl⟩ (by norm_num))
theorem R99233 : Reach 99233 := rs (se 2 (by rfl) ⟨37212, by rfl⟩) (B 74425 (by norm_num) ⟨37212, by rfl⟩ (by norm_num))
theorem R119713 : Reach 119713 := rs (se 2 (by rfl) ⟨44892, by rfl⟩) (B 89785 (by norm_num) ⟨44892, by rfl⟩ (by norm_num))
theorem R99237 : Reach 99237 := rs (se 4 (by rfl) ⟨9303, by rfl⟩) (B 18607 (by norm_num) ⟨9303, by rfl⟩ (by norm_num))
theorem R99241 : Reach 99241 := rs (se 2 (by rfl) ⟨37215, by rfl⟩) (B 74431 (by norm_num) ⟨37215, by rfl⟩ (by norm_num))
theorem R99245 : Reach 99245 := rs (se 3 (by rfl) ⟨18608, by rfl⟩) (B 37217 (by norm_num) ⟨18608, by rfl⟩ (by norm_num))
theorem R125869 : Reach 125869 := rs (se 3 (by rfl) ⟨23600, by rfl⟩) (B 47201 (by norm_num) ⟨23600, by rfl⟩ (by norm_num))
theorem R99249 : Reach 99249 := rs (se 2 (by rfl) ⟨37218, by rfl⟩) (B 74437 (by norm_num) ⟨37218, by rfl⟩ (by norm_num))
theorem R111541 : Reach 111541 := rs (se 5 (by rfl) ⟨5228, by rfl⟩) (B 10457 (by norm_num) ⟨5228, by rfl⟩ (by norm_num))
theorem R99253 : Reach 99253 := rs (se 5 (by rfl) ⟨4652, by rfl⟩) (B 9305 (by norm_num) ⟨4652, by rfl⟩ (by norm_num))
theorem R127921 : Reach 127921 := rs (se 2 (by rfl) ⟨47970, by rfl⟩) (B 95941 (by norm_num) ⟨47970, by rfl⟩ (by norm_num))
theorem R99257 : Reach 99257 := rs (se 2 (by rfl) ⟨37221, by rfl⟩) (B 74443 (by norm_num) ⟨37221, by rfl⟩ (by norm_num))
theorem R113593 : Reach 113593 := rs (se 2 (by rfl) ⟨42597, by rfl⟩) (B 85195 (by norm_num) ⟨42597, by rfl⟩ (by norm_num))
theorem R99261 : Reach 99261 := rs (se 3 (by rfl) ⟨18611, by rfl⟩) (B 37223 (by norm_num) ⟨18611, by rfl⟩ (by norm_num))
theorem R224189 : Reach 224189 := rs (se 3 (by rfl) ⟨42035, by rfl⟩) (B 84071 (by norm_num) ⟨42035, by rfl⟩ (by norm_num))
theorem R189373 : Reach 189373 := rs (se 3 (by rfl) ⟨35507, by rfl⟩) (B 71015 (by norm_num) ⟨35507, by rfl⟩ (by norm_num))
theorem R99265 : Reach 99265 := rs (se 2 (by rfl) ⟨37224, by rfl⟩) (B 74449 (by norm_num) ⟨37224, by rfl⟩ (by norm_num))
theorem R99269 : Reach 99269 := rs (se 4 (by rfl) ⟨9306, by rfl⟩) (B 18613 (by norm_num) ⟨9306, by rfl⟩ (by norm_num))
theorem R99273 : Reach 99273 := rs (se 2 (by rfl) ⟨37227, by rfl⟩) (B 74455 (by norm_num) ⟨37227, by rfl⟩ (by norm_num))
theorem R99277 : Reach 99277 := rs (se 3 (by rfl) ⟨18614, by rfl⟩) (B 37229 (by norm_num) ⟨18614, by rfl⟩ (by norm_num))
theorem R99281 : Reach 99281 := rs (se 2 (by rfl) ⟨37230, by rfl⟩) (B 74461 (by norm_num) ⟨37230, by rfl⟩ (by norm_num))
theorem R119761 : Reach 119761 := rs (se 2 (by rfl) ⟨44910, by rfl⟩) (B 89821 (by norm_num) ⟨44910, by rfl⟩ (by norm_num))
theorem R99285 : Reach 99285 := rs (se 7 (by rfl) ⟨1163, by rfl⟩) (B 2327 (by norm_num) ⟨1163, by rfl⟩ (by norm_num))
theorem R201685 : Reach 201685 := rs (se 7 (by rfl) ⟨2363, by rfl⟩) (B 4727 (by norm_num) ⟨2363, by rfl⟩ (by norm_num))
theorem R111577 : Reach 111577 := rs (se 2 (by rfl) ⟨41841, by rfl⟩) (B 83683 (by norm_num) ⟨41841, by rfl⟩ (by norm_num))
theorem R99289 : Reach 99289 := rs (se 2 (by rfl) ⟨37233, by rfl⟩) (B 74467 (by norm_num) ⟨37233, by rfl⟩ (by norm_num))
theorem R99293 : Reach 99293 := rs (se 3 (by rfl) ⟨18617, by rfl⟩) (B 37235 (by norm_num) ⟨18617, by rfl⟩ (by norm_num))
theorem R99297 : Reach 99297 := rs (se 2 (by rfl) ⟨37236, by rfl⟩) (B 74473 (by norm_num) ⟨37236, by rfl⟩ (by norm_num))
theorem R99301 : Reach 99301 := rs (se 4 (by rfl) ⟨9309, by rfl⟩) (B 18619 (by norm_num) ⟨9309, by rfl⟩ (by norm_num))
theorem R99305 : Reach 99305 := rs (se 2 (by rfl) ⟨37239, by rfl⟩) (B 74479 (by norm_num) ⟨37239, by rfl⟩ (by norm_num))
theorem R99309 : Reach 99309 := rs (se 3 (by rfl) ⟨18620, by rfl⟩) (B 37241 (by norm_num) ⟨18620, by rfl⟩ (by norm_num))
theorem R99313 : Reach 99313 := rs (se 2 (by rfl) ⟨37242, by rfl⟩) (B 74485 (by norm_num) ⟨37242, by rfl⟩ (by norm_num))
theorem R99317 : Reach 99317 := rs (se 5 (by rfl) ⟨4655, by rfl⟩) (B 9311 (by norm_num) ⟨4655, by rfl⟩ (by norm_num))
theorem R99321 : Reach 99321 := rs (se 2 (by rfl) ⟨37245, by rfl⟩) (B 74491 (by norm_num) ⟨37245, by rfl⟩ (by norm_num))
theorem R111613 : Reach 111613 := rs (se 3 (by rfl) ⟨20927, by rfl⟩) (B 41855 (by norm_num) ⟨20927, by rfl⟩ (by norm_num))
theorem R99325 : Reach 99325 := rs (se 3 (by rfl) ⟨18623, by rfl⟩) (B 37247 (by norm_num) ⟨18623, by rfl⟩ (by norm_num))
theorem R99329 : Reach 99329 := rs (se 2 (by rfl) ⟨37248, by rfl⟩) (B 74497 (by norm_num) ⟨37248, by rfl⟩ (by norm_num))
theorem R334853 : Reach 334853 := rs (se 4 (by rfl) ⟨31392, by rfl⟩) (B 62785 (by norm_num) ⟨31392, by rfl⟩ (by norm_num))
theorem R99333 : Reach 99333 := rs (se 4 (by rfl) ⟨9312, by rfl⟩) (B 18625 (by norm_num) ⟨9312, by rfl⟩ (by norm_num))
theorem R99337 : Reach 99337 := rs (se 2 (by rfl) ⟨37251, by rfl⟩) (B 74503 (by norm_num) ⟨37251, by rfl⟩ (by norm_num))
theorem R99341 : Reach 99341 := rs (se 3 (by rfl) ⟨18626, by rfl⟩) (B 37253 (by norm_num) ⟨18626, by rfl⟩ (by norm_num))
theorem R125965 : Reach 125965 := rs (se 3 (by rfl) ⟨23618, by rfl⟩) (B 47237 (by norm_num) ⟨23618, by rfl⟩ (by norm_num))
theorem R99345 : Reach 99345 := rs (se 2 (by rfl) ⟨37254, by rfl⟩) (B 74509 (by norm_num) ⟨37254, by rfl⟩ (by norm_num))
theorem R99349 : Reach 99349 := rs (se 6 (by rfl) ⟨2328, by rfl⟩) (B 4657 (by norm_num) ⟨2328, by rfl⟩ (by norm_num))
theorem R99353 : Reach 99353 := rs (se 2 (by rfl) ⟨37257, by rfl⟩) (B 74515 (by norm_num) ⟨37257, by rfl⟩ (by norm_num))
theorem R99357 : Reach 99357 := rs (se 3 (by rfl) ⟨18629, by rfl⟩) (B 37259 (by norm_num) ⟨18629, by rfl⟩ (by norm_num))
theorem R111649 : Reach 111649 := rs (se 2 (by rfl) ⟨41868, by rfl⟩) (B 83737 (by norm_num) ⟨41868, by rfl⟩ (by norm_num))
theorem R99361 : Reach 99361 := rs (se 2 (by rfl) ⟨37260, by rfl⟩) (B 74521 (by norm_num) ⟨37260, by rfl⟩ (by norm_num))
theorem R99365 : Reach 99365 := rs (se 4 (by rfl) ⟨9315, by rfl⟩) (B 18631 (by norm_num) ⟨9315, by rfl⟩ (by norm_num))
theorem R424997 : Reach 424997 := rs (se 4 (by rfl) ⟨39843, by rfl⟩) (B 79687 (by norm_num) ⟨39843, by rfl⟩ (by norm_num))
theorem R99369 : Reach 99369 := rs (se 2 (by rfl) ⟨37263, by rfl⟩) (B 74527 (by norm_num) ⟨37263, by rfl⟩ (by norm_num))
theorem R99373 : Reach 99373 := rs (se 3 (by rfl) ⟨18632, by rfl⟩) (B 37265 (by norm_num) ⟨18632, by rfl⟩ (by norm_num))
theorem R99377 : Reach 99377 := rs (se 2 (by rfl) ⟨37266, by rfl⟩) (B 74533 (by norm_num) ⟨37266, by rfl⟩ (by norm_num))
theorem R99381 : Reach 99381 := rs (se 5 (by rfl) ⟨4658, by rfl⟩) (B 9317 (by norm_num) ⟨4658, by rfl⟩ (by norm_num))
theorem R99385 : Reach 99385 := rs (se 2 (by rfl) ⟨37269, by rfl⟩) (B 74539 (by norm_num) ⟨37269, by rfl⟩ (by norm_num))
theorem R99389 : Reach 99389 := rs (se 3 (by rfl) ⟨18635, by rfl⟩) (B 37271 (by norm_num) ⟨18635, by rfl⟩ (by norm_num))
theorem R99393 : Reach 99393 := rs (se 2 (by rfl) ⟨37272, by rfl⟩) (B 74545 (by norm_num) ⟨37272, by rfl⟩ (by norm_num))
theorem R111685 : Reach 111685 := rs (se 4 (by rfl) ⟨10470, by rfl⟩) (B 20941 (by norm_num) ⟨10470, by rfl⟩ (by norm_num))
theorem R99397 : Reach 99397 := rs (se 4 (by rfl) ⟨9318, by rfl⟩) (B 18637 (by norm_num) ⟨9318, by rfl⟩ (by norm_num))
theorem R99401 : Reach 99401 := rs (se 2 (by rfl) ⟨37275, by rfl⟩) (B 74551 (by norm_num) ⟨37275, by rfl⟩ (by norm_num))
theorem R158797 : Reach 158797 := rs (se 3 (by rfl) ⟨29774, by rfl⟩) (B 59549 (by norm_num) ⟨29774, by rfl⟩ (by norm_num))
theorem R99405 : Reach 99405 := rs (se 3 (by rfl) ⟨18638, by rfl⟩) (B 37277 (by norm_num) ⟨18638, by rfl⟩ (by norm_num))
theorem R99409 : Reach 99409 := rs (se 2 (by rfl) ⟨37278, by rfl⟩) (B 74557 (by norm_num) ⟨37278, by rfl⟩ (by norm_num))
theorem R224333 : Reach 224333 := rs (se 3 (by rfl) ⟨42062, by rfl⟩) (B 84125 (by norm_num) ⟨42062, by rfl⟩ (by norm_num))
theorem R326741 : Reach 326741 := rs (se 8 (by rfl) ⟨1914, by rfl⟩) (B 3829 (by norm_num) ⟨1914, by rfl⟩ (by norm_num))
theorem R99413 : Reach 99413 := rs (se 8 (by rfl) ⟨582, by rfl⟩) (B 1165 (by norm_num) ⟨582, by rfl⟩ (by norm_num))
theorem R99417 : Reach 99417 := rs (se 2 (by rfl) ⟨37281, by rfl⟩) (B 74563 (by norm_num) ⟨37281, by rfl⟩ (by norm_num))
theorem R99421 : Reach 99421 := rs (se 3 (by rfl) ⟨18641, by rfl⟩) (B 37283 (by norm_num) ⟨18641, by rfl⟩ (by norm_num))
theorem R99425 : Reach 99425 := rs (se 2 (by rfl) ⟨37284, by rfl⟩) (B 74569 (by norm_num) ⟨37284, by rfl⟩ (by norm_num))
theorem R99429 : Reach 99429 := rs (se 4 (by rfl) ⟨9321, by rfl⟩) (B 18643 (by norm_num) ⟨9321, by rfl⟩ (by norm_num))
theorem R111721 : Reach 111721 := rs (se 2 (by rfl) ⟨41895, by rfl⟩) (B 83791 (by norm_num) ⟨41895, by rfl⟩ (by norm_num))
theorem R99433 : Reach 99433 := rs (se 2 (by rfl) ⟨37287, by rfl⟩) (B 74575 (by norm_num) ⟨37287, by rfl⟩ (by norm_num))
theorem R99437 : Reach 99437 := rs (se 3 (by rfl) ⟨18644, by rfl⟩) (B 37289 (by norm_num) ⟨18644, by rfl⟩ (by norm_num))
theorem R99441 : Reach 99441 := rs (se 2 (by rfl) ⟨37290, by rfl⟩) (B 74581 (by norm_num) ⟨37290, by rfl⟩ (by norm_num))
theorem R99445 : Reach 99445 := rs (se 5 (by rfl) ⟨4661, by rfl⟩) (B 9323 (by norm_num) ⟨4661, by rfl⟩ (by norm_num))
theorem R99449 : Reach 99449 := rs (se 2 (by rfl) ⟨37293, by rfl⟩) (B 74587 (by norm_num) ⟨37293, by rfl⟩ (by norm_num))
theorem R99453 : Reach 99453 := rs (se 3 (by rfl) ⟨18647, by rfl⟩) (B 37295 (by norm_num) ⟨18647, by rfl⟩ (by norm_num))
theorem R99457 : Reach 99457 := rs (se 2 (by rfl) ⟨37296, by rfl⟩) (B 74593 (by norm_num) ⟨37296, by rfl⟩ (by norm_num))
theorem R99461 : Reach 99461 := rs (se 4 (by rfl) ⟨9324, by rfl⟩) (B 18649 (by norm_num) ⟨9324, by rfl⟩ (by norm_num))
theorem R99465 : Reach 99465 := rs (se 2 (by rfl) ⟨37299, by rfl⟩) (B 74599 (by norm_num) ⟨37299, by rfl⟩ (by norm_num))
theorem R111757 : Reach 111757 := rs (se 3 (by rfl) ⟨20954, by rfl⟩) (B 41909 (by norm_num) ⟨20954, by rfl⟩ (by norm_num))
theorem R99469 : Reach 99469 := rs (se 3 (by rfl) ⟨18650, by rfl⟩) (B 37301 (by norm_num) ⟨18650, by rfl⟩ (by norm_num))
theorem R99473 : Reach 99473 := rs (se 2 (by rfl) ⟨37302, by rfl⟩) (B 74605 (by norm_num) ⟨37302, by rfl⟩ (by norm_num))
theorem R99477 : Reach 99477 := rs (se 6 (by rfl) ⟨2331, by rfl⟩) (B 4663 (by norm_num) ⟨2331, by rfl⟩ (by norm_num))
theorem R224405 : Reach 224405 := rs (se 6 (by rfl) ⟨5259, by rfl⟩) (B 10519 (by norm_num) ⟨5259, by rfl⟩ (by norm_num))
theorem R99481 : Reach 99481 := rs (se 2 (by rfl) ⟨37305, by rfl⟩) (B 74611 (by norm_num) ⟨37305, by rfl⟩ (by norm_num))
theorem R99485 : Reach 99485 := rs (se 3 (by rfl) ⟨18653, by rfl⟩) (B 37307 (by norm_num) ⟨18653, by rfl⟩ (by norm_num))
theorem R99489 : Reach 99489 := rs (se 2 (by rfl) ⟨37308, by rfl⟩) (B 74617 (by norm_num) ⟨37308, by rfl⟩ (by norm_num))
theorem R99493 : Reach 99493 := rs (se 4 (by rfl) ⟨9327, by rfl⟩) (B 18655 (by norm_num) ⟨9327, by rfl⟩ (by norm_num))
theorem R99497 : Reach 99497 := rs (se 2 (by rfl) ⟨37311, by rfl⟩) (B 74623 (by norm_num) ⟨37311, by rfl⟩ (by norm_num))
theorem R99501 : Reach 99501 := rs (se 3 (by rfl) ⟨18656, by rfl⟩) (B 37313 (by norm_num) ⟨18656, by rfl⟩ (by norm_num))
theorem R111793 : Reach 111793 := rs (se 2 (by rfl) ⟨41922, by rfl⟩) (B 83845 (by norm_num) ⟨41922, by rfl⟩ (by norm_num))
theorem R99505 : Reach 99505 := rs (se 2 (by rfl) ⟨37314, by rfl⟩) (B 74629 (by norm_num) ⟨37314, by rfl⟩ (by norm_num))
theorem R99509 : Reach 99509 := rs (se 5 (by rfl) ⟨4664, by rfl⟩) (B 9329 (by norm_num) ⟨4664, by rfl⟩ (by norm_num))
theorem R99513 : Reach 99513 := rs (se 2 (by rfl) ⟨37317, by rfl⟩) (B 74635 (by norm_num) ⟨37317, by rfl⟩ (by norm_num))
theorem R126137 : Reach 126137 := rs (se 2 (by rfl) ⟨47301, by rfl⟩) (B 94603 (by norm_num) ⟨47301, by rfl⟩ (by norm_num))
theorem R99517 : Reach 99517 := rs (se 3 (by rfl) ⟨18659, by rfl⟩) (B 37319 (by norm_num) ⟨18659, by rfl⟩ (by norm_num))
theorem R99521 : Reach 99521 := rs (se 2 (by rfl) ⟨37320, by rfl⟩) (B 74641 (by norm_num) ⟨37320, by rfl⟩ (by norm_num))
theorem R99525 : Reach 99525 := rs (se 4 (by rfl) ⟨9330, by rfl⟩) (B 18661 (by norm_num) ⟨9330, by rfl⟩ (by norm_num))
theorem R99529 : Reach 99529 := rs (se 2 (by rfl) ⟨37323, by rfl⟩) (B 74647 (by norm_num) ⟨37323, by rfl⟩ (by norm_num))
theorem R99533 : Reach 99533 := rs (se 3 (by rfl) ⟨18662, by rfl⟩) (B 37325 (by norm_num) ⟨18662, by rfl⟩ (by norm_num))
theorem R99537 : Reach 99537 := rs (se 2 (by rfl) ⟨37326, by rfl⟩) (B 74653 (by norm_num) ⟨37326, by rfl⟩ (by norm_num))
theorem R111829 : Reach 111829 := rs (se 7 (by rfl) ⟨1310, by rfl⟩) (B 2621 (by norm_num) ⟨1310, by rfl⟩ (by norm_num))
theorem R99541 : Reach 99541 := rs (se 7 (by rfl) ⟨1166, by rfl⟩) (B 2333 (by norm_num) ⟨1166, by rfl⟩ (by norm_num))
theorem R99545 : Reach 99545 := rs (se 2 (by rfl) ⟨37329, by rfl⟩) (B 74659 (by norm_num) ⟨37329, by rfl⟩ (by norm_num))
theorem R99549 : Reach 99549 := rs (se 3 (by rfl) ⟨18665, by rfl⟩) (B 37331 (by norm_num) ⟨18665, by rfl⟩ (by norm_num))
theorem R99553 : Reach 99553 := rs (se 2 (by rfl) ⟨37332, by rfl⟩) (B 74665 (by norm_num) ⟨37332, by rfl⟩ (by norm_num))
theorem R224477 : Reach 224477 := rs (se 3 (by rfl) ⟨42089, by rfl⟩) (B 84179 (by norm_num) ⟨42089, by rfl⟩ (by norm_num))
theorem R148709 : Reach 148709 := rs (se 4 (by rfl) ⟨13941, by rfl⟩) (B 27883 (by norm_num) ⟨13941, by rfl⟩ (by norm_num))
theorem R99557 : Reach 99557 := rs (se 4 (by rfl) ⟨9333, by rfl⟩) (B 18667 (by norm_num) ⟨9333, by rfl⟩ (by norm_num))
theorem R99561 : Reach 99561 := rs (se 2 (by rfl) ⟨37335, by rfl⟩) (B 74671 (by norm_num) ⟨37335, by rfl⟩ (by norm_num))
theorem R99565 : Reach 99565 := rs (se 3 (by rfl) ⟨18668, by rfl⟩) (B 37337 (by norm_num) ⟨18668, by rfl⟩ (by norm_num))
theorem R99569 : Reach 99569 := rs (se 2 (by rfl) ⟨37338, by rfl⟩) (B 74677 (by norm_num) ⟨37338, by rfl⟩ (by norm_num))
theorem R126193 : Reach 126193 := rs (se 2 (by rfl) ⟨47322, by rfl⟩) (B 94645 (by norm_num) ⟨47322, by rfl⟩ (by norm_num))
theorem R681205 : Reach 681205 := rs (se 5 (by rfl) ⟨31931, by rfl⟩) (B 63863 (by norm_num) ⟨31931, by rfl⟩ (by norm_num))
theorem R99573 : Reach 99573 := rs (se 5 (by rfl) ⟨4667, by rfl⟩) (B 9335 (by norm_num) ⟨4667, by rfl⟩ (by norm_num))
theorem R111865 : Reach 111865 := rs (se 2 (by rfl) ⟨41949, by rfl⟩) (B 83899 (by norm_num) ⟨41949, by rfl⟩ (by norm_num))
theorem R99577 : Reach 99577 := rs (se 2 (by rfl) ⟨37341, by rfl⟩) (B 74683 (by norm_num) ⟨37341, by rfl⟩ (by norm_num))
theorem R148733 : Reach 148733 := rs (se 3 (by rfl) ⟨27887, by rfl⟩) (B 55775 (by norm_num) ⟨27887, by rfl⟩ (by norm_num))
theorem R99581 : Reach 99581 := rs (se 3 (by rfl) ⟨18671, by rfl⟩) (B 37343 (by norm_num) ⟨18671, by rfl⟩ (by norm_num))
theorem R99585 : Reach 99585 := rs (se 2 (by rfl) ⟨37344, by rfl⟩) (B 74689 (by norm_num) ⟨37344, by rfl⟩ (by norm_num))
theorem R99589 : Reach 99589 := rs (se 4 (by rfl) ⟨9336, by rfl⟩) (B 18673 (by norm_num) ⟨9336, by rfl⟩ (by norm_num))
theorem R99593 : Reach 99593 := rs (se 2 (by rfl) ⟨37347, by rfl⟩) (B 74695 (by norm_num) ⟨37347, by rfl⟩ (by norm_num))
theorem R99597 : Reach 99597 := rs (se 3 (by rfl) ⟨18674, by rfl⟩) (B 37349 (by norm_num) ⟨18674, by rfl⟩ (by norm_num))
theorem R99601 : Reach 99601 := rs (se 2 (by rfl) ⟨37350, by rfl⟩) (B 74701 (by norm_num) ⟨37350, by rfl⟩ (by norm_num))
theorem R148757 : Reach 148757 := rs (se 6 (by rfl) ⟨3486, by rfl⟩) (B 6973 (by norm_num) ⟨3486, by rfl⟩ (by norm_num))
theorem R99605 : Reach 99605 := rs (se 6 (by rfl) ⟨2334, by rfl⟩) (B 4669 (by norm_num) ⟨2334, by rfl⟩ (by norm_num))
theorem R99609 : Reach 99609 := rs (se 2 (by rfl) ⟨37353, by rfl⟩) (B 74707 (by norm_num) ⟨37353, by rfl⟩ (by norm_num))
theorem R111901 : Reach 111901 := rs (se 3 (by rfl) ⟨20981, by rfl⟩) (B 41963 (by norm_num) ⟨20981, by rfl⟩ (by norm_num))
theorem R99613 : Reach 99613 := rs (se 3 (by rfl) ⟨18677, by rfl⟩) (B 37355 (by norm_num) ⟨18677, by rfl⟩ (by norm_num))
theorem R99617 : Reach 99617 := rs (se 2 (by rfl) ⟨37356, by rfl⟩) (B 74713 (by norm_num) ⟨37356, by rfl⟩ (by norm_num))
theorem R99621 : Reach 99621 := rs (se 4 (by rfl) ⟨9339, by rfl⟩) (B 18679 (by norm_num) ⟨9339, by rfl⟩ (by norm_num))
theorem R99625 : Reach 99625 := rs (se 2 (by rfl) ⟨37359, by rfl⟩) (B 74719 (by norm_num) ⟨37359, by rfl⟩ (by norm_num))
theorem R148781 : Reach 148781 := rs (se 3 (by rfl) ⟨27896, by rfl⟩) (B 55793 (by norm_num) ⟨27896, by rfl⟩ (by norm_num))
theorem R99629 : Reach 99629 := rs (se 3 (by rfl) ⟨18680, by rfl⟩) (B 37361 (by norm_num) ⟨18680, by rfl⟩ (by norm_num))
theorem R99633 : Reach 99633 := rs (se 2 (by rfl) ⟨37362, by rfl⟩) (B 74725 (by norm_num) ⟨37362, by rfl⟩ (by norm_num))
theorem R99637 : Reach 99637 := rs (se 5 (by rfl) ⟨4670, by rfl⟩) (B 9341 (by norm_num) ⟨4670, by rfl⟩ (by norm_num))
theorem R99641 : Reach 99641 := rs (se 2 (by rfl) ⟨37365, by rfl⟩) (B 74731 (by norm_num) ⟨37365, by rfl⟩ (by norm_num))
theorem R134461 : Reach 134461 := rs (se 3 (by rfl) ⟨25211, by rfl⟩) (B 50423 (by norm_num) ⟨25211, by rfl⟩ (by norm_num))
theorem R99645 : Reach 99645 := rs (se 3 (by rfl) ⟨18683, by rfl⟩) (B 37367 (by norm_num) ⟨18683, by rfl⟩ (by norm_num))
theorem R111937 : Reach 111937 := rs (se 2 (by rfl) ⟨41976, by rfl⟩) (B 83953 (by norm_num) ⟨41976, by rfl⟩ (by norm_num))
theorem R99649 : Reach 99649 := rs (se 2 (by rfl) ⟨37368, by rfl⟩) (B 74737 (by norm_num) ⟨37368, by rfl⟩ (by norm_num))
theorem R148805 : Reach 148805 := rs (se 4 (by rfl) ⟨13950, by rfl⟩) (B 27901 (by norm_num) ⟨13950, by rfl⟩ (by norm_num))
theorem R99653 : Reach 99653 := rs (se 4 (by rfl) ⟨9342, by rfl⟩) (B 18685 (by norm_num) ⟨9342, by rfl⟩ (by norm_num))
theorem R99657 : Reach 99657 := rs (se 2 (by rfl) ⟨37371, by rfl⟩) (B 74743 (by norm_num) ⟨37371, by rfl⟩ (by norm_num))
theorem R99661 : Reach 99661 := rs (se 3 (by rfl) ⟨18686, by rfl⟩) (B 37373 (by norm_num) ⟨18686, by rfl⟩ (by norm_num))
theorem R99665 : Reach 99665 := rs (se 2 (by rfl) ⟨37374, by rfl⟩) (B 74749 (by norm_num) ⟨37374, by rfl⟩ (by norm_num))
theorem R251221 : Reach 251221 := rs (se 15 (by rfl) ⟨11, by rfl⟩) (B 23 (by norm_num) ⟨11, by rfl⟩ (by norm_num))
theorem R99669 : Reach 99669 := rs (se 12 (by rfl) ⟨36, by rfl⟩) (B 73 (by norm_num) ⟨36, by rfl⟩ (by norm_num))
theorem R148829 : Reach 148829 := rs (se 3 (by rfl) ⟨27905, by rfl⟩) (B 55811 (by norm_num) ⟨27905, by rfl⟩ (by norm_num))
theorem R99673 : Reach 99673 := rs (se 2 (by rfl) ⟨37377, by rfl⟩) (B 74755 (by norm_num) ⟨37377, by rfl⟩ (by norm_num))
theorem R99677 : Reach 99677 := rs (se 3 (by rfl) ⟨18689, by rfl⟩) (B 37379 (by norm_num) ⟨18689, by rfl⟩ (by norm_num))
theorem R99681 : Reach 99681 := rs (se 2 (by rfl) ⟨37380, by rfl⟩) (B 74761 (by norm_num) ⟨37380, by rfl⟩ (by norm_num))
theorem R111973 : Reach 111973 := rs (se 4 (by rfl) ⟨10497, by rfl⟩) (B 20995 (by norm_num) ⟨10497, by rfl⟩ (by norm_num))
theorem R99685 : Reach 99685 := rs (se 4 (by rfl) ⟨9345, by rfl⟩) (B 18691 (by norm_num) ⟨9345, by rfl⟩ (by norm_num))
theorem R99689 : Reach 99689 := rs (se 2 (by rfl) ⟨37383, by rfl⟩) (B 74767 (by norm_num) ⟨37383, by rfl⟩ (by norm_num))
theorem R99693 : Reach 99693 := rs (se 3 (by rfl) ⟨18692, by rfl⟩) (B 37385 (by norm_num) ⟨18692, by rfl⟩ (by norm_num))
theorem R99697 : Reach 99697 := rs (se 2 (by rfl) ⟨37386, by rfl⟩) (B 74773 (by norm_num) ⟨37386, by rfl⟩ (by norm_num))
theorem R148853 : Reach 148853 := rs (se 5 (by rfl) ⟨6977, by rfl⟩) (B 13955 (by norm_num) ⟨6977, by rfl⟩ (by norm_num))
theorem R378229 : Reach 378229 := rs (se 5 (by rfl) ⟨17729, by rfl⟩) (B 35459 (by norm_num) ⟨17729, by rfl⟩ (by norm_num))
theorem R99701 : Reach 99701 := rs (se 5 (by rfl) ⟨4673, by rfl⟩) (B 9347 (by norm_num) ⟨4673, by rfl⟩ (by norm_num))
theorem R99705 : Reach 99705 := rs (se 2 (by rfl) ⟨37389, by rfl⟩) (B 74779 (by norm_num) ⟨37389, by rfl⟩ (by norm_num))
theorem R99709 : Reach 99709 := rs (se 3 (by rfl) ⟨18695, by rfl⟩) (B 37391 (by norm_num) ⟨18695, by rfl⟩ (by norm_num))
theorem R99713 : Reach 99713 := rs (se 2 (by rfl) ⟨37392, by rfl⟩) (B 74785 (by norm_num) ⟨37392, by rfl⟩ (by norm_num))
theorem R112009 : Reach 112009 := rs (se 2 (by rfl) ⟨42003, by rfl⟩) (B 84007 (by norm_num) ⟨42003, by rfl⟩ (by norm_num))
theorem R99717 : Reach 99717 := rs (se 4 (by rfl) ⟨9348, by rfl⟩) (B 18697 (by norm_num) ⟨9348, by rfl⟩ (by norm_num))
theorem R148877 : Reach 148877 := rs (se 3 (by rfl) ⟨27914, by rfl⟩) (B 55829 (by norm_num) ⟨27914, by rfl⟩ (by norm_num))
theorem R99721 : Reach 99721 := rs (se 2 (by rfl) ⟨37395, by rfl⟩) (B 74791 (by norm_num) ⟨37395, by rfl⟩ (by norm_num))
theorem R99725 : Reach 99725 := rs (se 3 (by rfl) ⟨18698, by rfl⟩) (B 37397 (by norm_num) ⟨18698, by rfl⟩ (by norm_num))
theorem R681365 : Reach 681365 := rs (se 6 (by rfl) ⟨15969, by rfl⟩) (B 31939 (by norm_num) ⟨15969, by rfl⟩ (by norm_num))
theorem R99729 : Reach 99729 := rs (se 2 (by rfl) ⟨37398, by rfl⟩) (B 74797 (by norm_num) ⟨37398, by rfl⟩ (by norm_num))
theorem R99733 : Reach 99733 := rs (se 6 (by rfl) ⟨2337, by rfl⟩) (B 4675 (by norm_num) ⟨2337, by rfl⟩ (by norm_num))
theorem R99737 : Reach 99737 := rs (se 2 (by rfl) ⟨37401, by rfl⟩) (B 74803 (by norm_num) ⟨37401, by rfl⟩ (by norm_num))
theorem R99741 : Reach 99741 := rs (se 3 (by rfl) ⟨18701, by rfl⟩) (B 37403 (by norm_num) ⟨18701, by rfl⟩ (by norm_num))
theorem R99745 : Reach 99745 := rs (se 2 (by rfl) ⟨37404, by rfl⟩) (B 74809 (by norm_num) ⟨37404, by rfl⟩ (by norm_num))
theorem R148901 : Reach 148901 := rs (se 4 (by rfl) ⟨13959, by rfl⟩) (B 27919 (by norm_num) ⟨13959, by rfl⟩ (by norm_num))
theorem R99749 : Reach 99749 := rs (se 4 (by rfl) ⟨9351, by rfl⟩) (B 18703 (by norm_num) ⟨9351, by rfl⟩ (by norm_num))
theorem R99753 : Reach 99753 := rs (se 2 (by rfl) ⟨37407, by rfl⟩) (B 74815 (by norm_num) ⟨37407, by rfl⟩ (by norm_num))
theorem R112045 : Reach 112045 := rs (se 3 (by rfl) ⟨21008, by rfl⟩) (B 42017 (by norm_num) ⟨21008, by rfl⟩ (by norm_num))
theorem R99757 : Reach 99757 := rs (se 3 (by rfl) ⟨18704, by rfl⟩) (B 37409 (by norm_num) ⟨18704, by rfl⟩ (by norm_num))
theorem R99761 : Reach 99761 := rs (se 2 (by rfl) ⟨37410, by rfl⟩) (B 74821 (by norm_num) ⟨37410, by rfl⟩ (by norm_num))
theorem R335285 : Reach 335285 := rs (se 5 (by rfl) ⟨15716, by rfl⟩) (B 31433 (by norm_num) ⟨15716, by rfl⟩ (by norm_num))
theorem R99765 : Reach 99765 := rs (se 5 (by rfl) ⟨4676, by rfl⟩) (B 9353 (by norm_num) ⟨4676, by rfl⟩ (by norm_num))
theorem R99769 : Reach 99769 := rs (se 2 (by rfl) ⟨37413, by rfl⟩) (B 74827 (by norm_num) ⟨37413, by rfl⟩ (by norm_num))
theorem R148925 : Reach 148925 := rs (se 3 (by rfl) ⟨27923, by rfl⟩) (B 55847 (by norm_num) ⟨27923, by rfl⟩ (by norm_num))
theorem R99773 : Reach 99773 := rs (se 3 (by rfl) ⟨18707, by rfl⟩) (B 37415 (by norm_num) ⟨18707, by rfl⟩ (by norm_num))
theorem R251333 : Reach 251333 := rs (se 4 (by rfl) ⟨23562, by rfl⟩) (B 47125 (by norm_num) ⟨23562, by rfl⟩ (by norm_num))
theorem R99777 : Reach 99777 := rs (se 2 (by rfl) ⟨37416, by rfl⟩) (B 74833 (by norm_num) ⟨37416, by rfl⟩ (by norm_num))
theorem R112081 : Reach 112081 := rs (se 2 (by rfl) ⟨42030, by rfl⟩) (B 84061 (by norm_num) ⟨42030, by rfl⟩ (by norm_num))
theorem R148949 : Reach 148949 := rs (se 7 (by rfl) ⟨1745, by rfl⟩) (B 3491 (by norm_num) ⟨1745, by rfl⟩ (by norm_num))
theorem R148973 : Reach 148973 := rs (se 3 (by rfl) ⟨27932, by rfl⟩) (B 55865 (by norm_num) ⟨27932, by rfl⟩ (by norm_num))
theorem R167413 : Reach 167413 := rs (se 5 (by rfl) ⟨7847, by rfl⟩) (B 15695 (by norm_num) ⟨7847, by rfl⟩ (by norm_num))
theorem R159221 : Reach 159221 := rs (se 5 (by rfl) ⟨7463, by rfl⟩) (B 14927 (by norm_num) ⟨7463, by rfl⟩ (by norm_num))
theorem R112117 : Reach 112117 := rs (se 5 (by rfl) ⟨5255, by rfl⟩) (B 10511 (by norm_num) ⟨5255, by rfl⟩ (by norm_num))
theorem R148997 : Reach 148997 := rs (se 4 (by rfl) ⟨13968, by rfl⟩) (B 27937 (by norm_num) ⟨13968, by rfl⟩ (by norm_num))
theorem R112153 : Reach 112153 := rs (se 2 (by rfl) ⟨42057, by rfl⟩) (B 84115 (by norm_num) ⟨42057, by rfl⟩ (by norm_num))
theorem R149021 : Reach 149021 := rs (se 3 (by rfl) ⟨27941, by rfl⟩) (B 55883 (by norm_num) ⟨27941, by rfl⟩ (by norm_num))
theorem R503333 : Reach 503333 := rs (se 4 (by rfl) ⟨47187, by rfl⟩) (B 94375 (by norm_num) ⟨47187, by rfl⟩ (by norm_num))
theorem R149045 : Reach 149045 := rs (se 5 (by rfl) ⟨6986, by rfl⟩) (B 13973 (by norm_num) ⟨6986, by rfl⟩ (by norm_num))
theorem R112189 : Reach 112189 := rs (se 3 (by rfl) ⟨21035, by rfl⟩) (B 42071 (by norm_num) ⟨21035, by rfl⟩ (by norm_num))
theorem R212549 : Reach 212549 := rs (se 4 (by rfl) ⟨19926, by rfl⟩) (B 39853 (by norm_num) ⟨19926, by rfl⟩ (by norm_num))
theorem R167501 : Reach 167501 := rs (se 3 (by rfl) ⟨31406, by rfl⟩) (B 62813 (by norm_num) ⟨31406, by rfl⟩ (by norm_num))
theorem R149069 : Reach 149069 := rs (se 3 (by rfl) ⟨27950, by rfl⟩) (B 55901 (by norm_num) ⟨27950, by rfl⟩ (by norm_num))
theorem R112225 : Reach 112225 := rs (se 2 (by rfl) ⟨42084, by rfl⟩) (B 84169 (by norm_num) ⟨42084, by rfl⟩ (by norm_num))
theorem R149093 : Reach 149093 := rs (se 4 (by rfl) ⟨13977, by rfl⟩) (B 27955 (by norm_num) ⟨13977, by rfl⟩ (by norm_num))
theorem R149117 : Reach 149117 := rs (se 3 (by rfl) ⟨27959, by rfl⟩) (B 55919 (by norm_num) ⟨27959, by rfl⟩ (by norm_num))
theorem R251525 : Reach 251525 := rs (se 4 (by rfl) ⟨23580, by rfl⟩) (B 47161 (by norm_num) ⟨23580, by rfl⟩ (by norm_num))
theorem R106121 : Reach 106121 := rs (se 2 (by rfl) ⟨39795, by rfl⟩) (B 79591 (by norm_num) ⟨39795, by rfl⟩ (by norm_num))
theorem R149141 : Reach 149141 := rs (se 6 (by rfl) ⟨3495, by rfl⟩) (B 6991 (by norm_num) ⟨3495, by rfl⟩ (by norm_num))
theorem R378533 : Reach 378533 := rs (se 4 (by rfl) ⟨35487, by rfl⟩) (B 70975 (by norm_num) ⟨35487, by rfl⟩ (by norm_num))
theorem R149165 : Reach 149165 := rs (se 3 (by rfl) ⟨27968, by rfl⟩) (B 55937 (by norm_num) ⟨27968, by rfl⟩ (by norm_num))
theorem R272069 : Reach 272069 := rs (se 4 (by rfl) ⟨25506, by rfl⟩) (B 51013 (by norm_num) ⟨25506, by rfl⟩ (by norm_num))
theorem R149189 : Reach 149189 := rs (se 4 (by rfl) ⟨13986, by rfl⟩) (B 27973 (by norm_num) ⟨13986, by rfl⟩ (by norm_num))
theorem R167629 : Reach 167629 := rs (se 3 (by rfl) ⟨31430, by rfl⟩) (B 62861 (by norm_num) ⟨31430, by rfl⟩ (by norm_num))
theorem R403157 : Reach 403157 := rs (se 7 (by rfl) ⟨4724, by rfl⟩) (B 9449 (by norm_num) ⟨4724, by rfl⟩ (by norm_num))
theorem R149213 : Reach 149213 := rs (se 3 (by rfl) ⟨27977, by rfl⟩) (B 55955 (by norm_num) ⟨27977, by rfl⟩ (by norm_num))
theorem R906997 : Reach 906997 := rs (se 5 (by rfl) ⟨42515, by rfl⟩) (B 85031 (by norm_num) ⟨42515, by rfl⟩ (by norm_num))
theorem R149237 : Reach 149237 := rs (se 5 (by rfl) ⟨6995, by rfl⟩) (B 13991 (by norm_num) ⟨6995, by rfl⟩ (by norm_num))
theorem R149261 : Reach 149261 := rs (se 3 (by rfl) ⟨27986, by rfl⟩) (B 55973 (by norm_num) ⟨27986, by rfl⟩ (by norm_num))
theorem R159509 : Reach 159509 := rs (se 6 (by rfl) ⟨3738, by rfl⟩) (B 7477 (by norm_num) ⟨3738, by rfl⟩ (by norm_num))
theorem R167717 : Reach 167717 := rs (se 4 (by rfl) ⟨15723, by rfl⟩) (B 31447 (by norm_num) ⟨15723, by rfl⟩ (by norm_num))
theorem R149285 : Reach 149285 := rs (se 4 (by rfl) ⟨13995, by rfl⟩) (B 27991 (by norm_num) ⟨13995, by rfl⟩ (by norm_num))
theorem R214829 : Reach 214829 := rs (se 3 (by rfl) ⟨40280, by rfl⟩) (B 80561 (by norm_num) ⟨40280, by rfl⟩ (by norm_num))
theorem R212789 : Reach 212789 := rs (se 5 (by rfl) ⟨9974, by rfl⟩) (B 19949 (by norm_num) ⟨9974, by rfl⟩ (by norm_num))
theorem R149309 : Reach 149309 := rs (se 3 (by rfl) ⟨27995, by rfl⟩) (B 55991 (by norm_num) ⟨27995, by rfl⟩ (by norm_num))
theorem R106309 : Reach 106309 := rs (se 4 (by rfl) ⟨9966, by rfl⟩) (B 19933 (by norm_num) ⟨9966, by rfl⟩ (by norm_num))
theorem R149333 : Reach 149333 := rs (se 9 (by rfl) ⟨437, by rfl⟩) (B 875 (by norm_num) ⟨437, by rfl⟩ (by norm_num))
theorem R335717 : Reach 335717 := rs (se 4 (by rfl) ⟨31473, by rfl⟩) (B 62947 (by norm_num) ⟨31473, by rfl⟩ (by norm_num))
theorem R149357 : Reach 149357 := rs (se 3 (by rfl) ⟨28004, by rfl⟩) (B 56009 (by norm_num) ⟨28004, by rfl⟩ (by norm_num))
theorem R224261 : Reach 224261 := rs (se 4 (by rfl) ⟨21024, by rfl⟩) (B 42049 (by norm_num) ⟨21024, by rfl⟩ (by norm_num))
theorem R223109 : Reach 223109 := rs (se 4 (by rfl) ⟨20916, by rfl⟩) (B 41833 (by norm_num) ⟨20916, by rfl⟩ (by norm_num))
theorem R149381 : Reach 149381 := rs (se 4 (by rfl) ⟨14004, by rfl⟩) (B 28009 (by norm_num) ⟨14004, by rfl⟩ (by norm_num))
theorem R149405 : Reach 149405 := rs (se 3 (by rfl) ⟨28013, by rfl⟩) (B 56027 (by norm_num) ⟨28013, by rfl⟩ (by norm_num))
theorem R141221 : Reach 141221 := rs (se 4 (by rfl) ⟨13239, by rfl⟩) (B 26479 (by norm_num) ⟨13239, by rfl⟩ (by norm_num))
theorem R167845 : Reach 167845 := rs (se 4 (by rfl) ⟨15735, by rfl⟩) (B 31471 (by norm_num) ⟨15735, by rfl⟩ (by norm_num))
theorem R376757 : Reach 376757 := rs (se 5 (by rfl) ⟨17660, by rfl⟩) (B 35321 (by norm_num) ⟨17660, by rfl⟩ (by norm_num))
theorem R149429 : Reach 149429 := rs (se 5 (by rfl) ⟨7004, by rfl⟩) (B 14009 (by norm_num) ⟨7004, by rfl⟩ (by norm_num))
theorem R223181 : Reach 223181 := rs (se 3 (by rfl) ⟨41846, by rfl⟩) (B 83693 (by norm_num) ⟨41846, by rfl⟩ (by norm_num))
theorem R149453 : Reach 149453 := rs (se 3 (by rfl) ⟨28022, by rfl⟩) (B 56045 (by norm_num) ⟨28022, by rfl⟩ (by norm_num))
theorem R251869 : Reach 251869 := rs (se 3 (by rfl) ⟨47225, by rfl⟩) (B 94451 (by norm_num) ⟨47225, by rfl⟩ (by norm_num))
theorem R149477 : Reach 149477 := rs (se 4 (by rfl) ⟨14013, by rfl⟩) (B 28027 (by norm_num) ⟨14013, by rfl⟩ (by norm_num))
theorem R141301 : Reach 141301 := rs (se 5 (by rfl) ⟨6623, by rfl⟩) (B 13247 (by norm_num) ⟨6623, by rfl⟩ (by norm_num))
theorem R167933 : Reach 167933 := rs (se 3 (by rfl) ⟨31487, by rfl⟩) (B 62975 (by norm_num) ⟨31487, by rfl⟩ (by norm_num))
theorem R223235 : Reach 223235 := rs (se 1 (by rfl) ⟨167426, by rfl⟩) R334853
theorem R149507 : Reach 149507 := rs (se 1 (by rfl) ⟨112130, by rfl⟩) R224261
theorem R167953 : Reach 167953 := rs (se 2 (by rfl) ⟨62982, by rfl⟩) R125965
theorem R149537 : Reach 149537 := rs (se 2 (by rfl) ⟨56076, by rfl⟩) R112153
theorem R167987 : Reach 167987 := rs (se 1 (by rfl) ⟨125990, by rfl⟩) R251981
theorem R149555 : Reach 149555 := rs (se 1 (by rfl) ⟨112166, by rfl⟩) R224333
theorem R149585 : Reach 149585 := rs (se 2 (by rfl) ⟨56094, by rfl⟩) R112189
theorem R149603 : Reach 149603 := rs (se 1 (by rfl) ⟨112202, by rfl⟩) R224405
theorem R604273 : Reach 604273 := rs (se 2 (by rfl) ⟨226602, by rfl⟩) R453205
theorem R149633 : Reach 149633 := rs (se 2 (by rfl) ⟨56112, by rfl⟩) R112225
theorem R188561 : Reach 188561 := rs (se 2 (by rfl) ⟨70710, by rfl⟩) R141421
theorem R149651 : Reach 149651 := rs (se 1 (by rfl) ⟨112238, by rfl⟩) R224477
theorem R168115 : Reach 168115 := rs (se 1 (by rfl) ⟨126086, by rfl⟩) R252173
theorem R223505 : Reach 223505 := rs (se 2 (by rfl) ⟨83814, by rfl⟩) R167629
theorem R223523 : Reach 223523 := rs (se 1 (by rfl) ⟨167642, by rfl⟩) R335285
theorem R168257 : Reach 168257 := rs (se 2 (by rfl) ⟨63096, by rfl⟩) R126193
theorem R282989 : Reach 282989 := rs (se 3 (by rfl) ⟨53060, by rfl⟩) R106121
theorem R252305 : Reach 252305 := rs (se 2 (by rfl) ⟨94614, by rfl⟩) R189229
theorem R141745 : Reach 141745 := rs (se 2 (by rfl) ⟨53154, by rfl⟩) R106309
theorem R252355 : Reach 252355 := rs (se 1 (by rfl) ⟨189266, by rfl⟩) R378533
theorem R268771 : Reach 268771 := rs (se 1 (by rfl) ⟨201578, by rfl⟩) R403157
theorem R336365 : Reach 336365 := rs (se 3 (by rfl) ⟨63068, by rfl⟩) R126137
theorem R504305 : Reach 504305 := rs (se 2 (by rfl) ⟨189114, by rfl⟩) R378229
theorem R2423317 : Reach 2423317 := rs (se 6 (by rfl) ⟨56796, by rfl⟩) R113593
theorem R283171 : Reach 283171 := rs (se 1 (by rfl) ⟨212378, by rfl⟩) R424757
theorem R188963 : Reach 188963 := rs (se 1 (by rfl) ⟨141722, by rfl⟩) R283445
theorem R141859 : Reach 141859 := rs (se 1 (by rfl) ⟨106394, by rfl⟩) R212789
theorem R336419 : Reach 336419 := rs (se 1 (by rfl) ⟨252314, by rfl⟩) R504629
theorem R223793 : Reach 223793 := rs (se 2 (by rfl) ⟨83922, by rfl⟩) R167845
theorem R170561 : Reach 170561 := rs (se 2 (by rfl) ⟨63960, by rfl⟩) R127921
theorem R223811 : Reach 223811 := rs (se 1 (by rfl) ⟨167858, by rfl⟩) R335717
theorem R252497 : Reach 252497 := rs (se 2 (by rfl) ⟨94686, by rfl⟩) R189373
theorem R268913 : Reach 268913 := rs (se 2 (by rfl) ⟨100842, by rfl⟩) R201685
theorem R2153101 : Reach 2153101 := rs (se 3 (by rfl) ⟨403706, by rfl⟩) R807413
theorem R283331 : Reach 283331 := rs (se 1 (by rfl) ⟨212498, by rfl⟩) R424997
theorem R635597 : Reach 635597 := rs (se 3 (by rfl) ⟨119174, by rfl⟩) R238349
theorem R125651 : Reach 125651 := rs (se 1 (by rfl) ⟨94238, by rfl⟩) R188477
theorem R191203 : Reach 191203 := rs (se 1 (by rfl) ⟨143402, by rfl⟩) R286805
theorem R211729 : Reach 211729 := rs (se 2 (by rfl) ⟨79398, by rfl⟩) R158797
theorem R211747 : Reach 211747 := rs (se 1 (by rfl) ⟨158810, by rfl⟩) R317621
theorem R334637 : Reach 334637 := rs (se 3 (by rfl) ⟨62744, by rfl⟩) R125489
theorem R336689 : Reach 336689 := rs (se 2 (by rfl) ⟨126258, by rfl⟩) R252517
theorem R99139 : Reach 99139 := rs (se 1 (by rfl) ⟨74354, by rfl⟩) R148709
theorem R224081 : Reach 224081 := rs (se 2 (by rfl) ⟨84030, by rfl⟩) R168061
theorem R99155 : Reach 99155 := rs (se 1 (by rfl) ⟨74366, by rfl⟩) R148733
theorem R334691 : Reach 334691 := rs (se 1 (by rfl) ⟨251018, by rfl⟩) R502037
theorem R99171 : Reach 99171 := rs (se 1 (by rfl) ⟨74378, by rfl⟩) R148757
theorem R224099 : Reach 224099 := rs (se 1 (by rfl) ⟨168074, by rfl⟩) R336149
theorem R99187 : Reach 99187 := rs (se 1 (by rfl) ⟨74390, by rfl⟩) R148781
theorem R99203 : Reach 99203 := rs (se 1 (by rfl) ⟨74402, by rfl⟩) R148805
theorem R871309 : Reach 871309 := rs (se 3 (by rfl) ⟨163370, by rfl⟩) R326741
theorem R99219 : Reach 99219 := rs (se 1 (by rfl) ⟨74414, by rfl⟩) R148829
theorem R295825 : Reach 295825 := rs (se 2 (by rfl) ⟨110934, by rfl⟩) R221869
theorem R99235 : Reach 99235 := rs (se 1 (by rfl) ⟨74426, by rfl⟩) R148853
theorem R99251 : Reach 99251 := rs (se 1 (by rfl) ⟨74438, by rfl⟩) R148877
theorem R99267 : Reach 99267 := rs (se 1 (by rfl) ⟨74450, by rfl⟩) R148901
theorem R306125 : Reach 306125 := rs (se 3 (by rfl) ⟨57398, by rfl⟩) R114797
theorem R99283 : Reach 99283 := rs (se 1 (by rfl) ⟨74462, by rfl⟩) R148925
theorem R99299 : Reach 99299 := rs (se 1 (by rfl) ⟨74474, by rfl⟩) R148949
theorem R1209329 : Reach 1209329 := rs (se 2 (by rfl) ⟨453498, by rfl⟩) R906997
theorem R99315 : Reach 99315 := rs (se 1 (by rfl) ⟨74486, by rfl⟩) R148973
theorem R908273 : Reach 908273 := rs (se 2 (by rfl) ⟨340602, by rfl⟩) R681205
theorem R99331 : Reach 99331 := rs (se 1 (by rfl) ⟨74498, by rfl⟩) R148997
theorem R99347 : Reach 99347 := rs (se 1 (by rfl) ⟨74510, by rfl⟩) R149021
theorem R99363 : Reach 99363 := rs (se 1 (by rfl) ⟨74522, by rfl⟩) R149045
theorem R111667 : Reach 111667 := rs (se 1 (by rfl) ⟨83750, by rfl⟩) R167501
theorem R99379 : Reach 99379 := rs (se 1 (by rfl) ⟨74534, by rfl⟩) R149069
theorem R99395 : Reach 99395 := rs (se 1 (by rfl) ⟨74546, by rfl⟩) R149093
theorem R754757 : Reach 754757 := rs (se 4 (by rfl) ⟨70758, by rfl⟩) R141517
theorem R179281 : Reach 179281 := rs (se 2 (by rfl) ⟨67230, by rfl⟩) R134461
theorem R99411 : Reach 99411 := rs (se 1 (by rfl) ⟨74558, by rfl⟩) R149117
theorem R99427 : Reach 99427 := rs (se 1 (by rfl) ⟨74570, by rfl⟩) R149141
theorem R334961 : Reach 334961 := rs (se 2 (by rfl) ⟨125610, by rfl⟩) R251221
theorem R99443 : Reach 99443 := rs (se 1 (by rfl) ⟨74582, by rfl⟩) R149165
theorem R224369 : Reach 224369 := rs (se 2 (by rfl) ⟨84138, by rfl⟩) R168277
theorem R181379 : Reach 181379 := rs (se 1 (by rfl) ⟨136034, by rfl⟩) R272069
theorem R99459 : Reach 99459 := rs (se 1 (by rfl) ⟨74594, by rfl⟩) R149189
theorem R224387 : Reach 224387 := rs (se 1 (by rfl) ⟨168290, by rfl⟩) R336581
theorem R99475 : Reach 99475 := rs (se 1 (by rfl) ⟨74606, by rfl⟩) R149213
theorem R99491 : Reach 99491 := rs (se 1 (by rfl) ⟨74618, by rfl⟩) R149237
theorem R99507 : Reach 99507 := rs (se 1 (by rfl) ⟨74630, by rfl⟩) R149261
theorem R111811 : Reach 111811 := rs (se 1 (by rfl) ⟨83858, by rfl⟩) R167717
theorem R99523 : Reach 99523 := rs (se 1 (by rfl) ⟨74642, by rfl⟩) R149285
theorem R99539 : Reach 99539 := rs (se 1 (by rfl) ⟨74654, by rfl⟩) R149309
theorem R99555 : Reach 99555 := rs (se 1 (by rfl) ⟨74666, by rfl⟩) R149333
theorem R148721 : Reach 148721 := rs (se 2 (by rfl) ⟨55770, by rfl⟩) R111541
theorem R99571 : Reach 99571 := rs (se 1 (by rfl) ⟨74678, by rfl⟩) R149357
theorem R148739 : Reach 148739 := rs (se 1 (by rfl) ⟨111554, by rfl⟩) R223109
theorem R99587 : Reach 99587 := rs (se 1 (by rfl) ⟨74690, by rfl⟩) R149381
theorem R99603 : Reach 99603 := rs (se 1 (by rfl) ⟨74702, by rfl⟩) R149405
theorem R148769 : Reach 148769 := rs (se 2 (by rfl) ⟨55788, by rfl⟩) R111577
theorem R251171 : Reach 251171 := rs (se 1 (by rfl) ⟨188378, by rfl⟩) R376757
theorem R99619 : Reach 99619 := rs (se 1 (by rfl) ⟨74714, by rfl⟩) R149429
theorem R148787 : Reach 148787 := rs (se 1 (by rfl) ⟨111590, by rfl⟩) R223181
theorem R99635 : Reach 99635 := rs (se 1 (by rfl) ⟨74726, by rfl⟩) R149453
theorem R99651 : Reach 99651 := rs (se 1 (by rfl) ⟨74738, by rfl⟩) R149477
theorem R148817 : Reach 148817 := rs (se 2 (by rfl) ⟨55806, by rfl⟩) R111613
theorem R111955 : Reach 111955 := rs (se 1 (by rfl) ⟨83966, by rfl⟩) R167933
theorem R99667 : Reach 99667 := rs (se 1 (by rfl) ⟨74750, by rfl⟩) R149501
theorem R148835 : Reach 148835 := rs (se 1 (by rfl) ⟨111626, by rfl⟩) R223253
theorem R99683 : Reach 99683 := rs (se 1 (by rfl) ⟨74762, by rfl⟩) R149525
theorem R99699 : Reach 99699 := rs (se 1 (by rfl) ⟨74774, by rfl⟩) R149549
theorem R148865 : Reach 148865 := rs (se 2 (by rfl) ⟨55824, by rfl⟩) R111649
theorem R99715 : Reach 99715 := rs (se 1 (by rfl) ⟨74786, by rfl⟩) R149573
theorem R425357 : Reach 425357 := rs (se 3 (by rfl) ⟨79754, by rfl⟩) R159509
theorem R148883 : Reach 148883 := rs (se 1 (by rfl) ⟨111662, by rfl⟩) R223325
theorem R99731 : Reach 99731 := rs (se 1 (by rfl) ⟨74798, by rfl⟩) R149597
theorem R99747 : Reach 99747 := rs (se 1 (by rfl) ⟨74810, by rfl⟩) R149621
theorem R148913 : Reach 148913 := rs (se 2 (by rfl) ⟨55842, by rfl⟩) R111685
theorem R99763 : Reach 99763 := rs (se 1 (by rfl) ⟨74822, by rfl⟩) R149645
theorem R148931 : Reach 148931 := rs (se 1 (by rfl) ⟨111698, by rfl⟩) R223397
theorem R99779 : Reach 99779 := rs (se 1 (by rfl) ⟨74834, by rfl⟩) R149669
theorem R167393 : Reach 167393 := rs (se 2 (by rfl) ⟨62772, by rfl⟩) R125545
theorem R148961 : Reach 148961 := rs (se 2 (by rfl) ⟨55860, by rfl⟩) R111721
theorem R251363 : Reach 251363 := rs (se 1 (by rfl) ⟨188522, by rfl⟩) R377045
theorem R112099 : Reach 112099 := rs (se 1 (by rfl) ⟨84074, by rfl⟩) R168149
theorem R151025 : Reach 151025 := rs (se 2 (by rfl) ⟨56634, by rfl⟩) R113269
theorem R148979 : Reach 148979 := rs (se 1 (by rfl) ⟨111734, by rfl⟩) R223469
theorem R566797 : Reach 566797 := rs (se 3 (by rfl) ⟨106274, by rfl⟩) R212549
theorem R149009 : Reach 149009 := rs (se 2 (by rfl) ⟨55878, by rfl⟩) R111757
theorem R134689 : Reach 134689 := rs (se 2 (by rfl) ⟨50508, by rfl⟩) R101017
theorem R149027 : Reach 149027 := rs (se 1 (by rfl) ⟨111770, by rfl⟩) R223541
theorem R149057 : Reach 149057 := rs (se 2 (by rfl) ⟨55896, by rfl⟩) R111793
theorem R149075 : Reach 149075 := rs (se 1 (by rfl) ⟨111806, by rfl⟩) R223613
theorem R167521 : Reach 167521 := rs (se 2 (by rfl) ⟨62820, by rfl⟩) R125641
theorem R454243 : Reach 454243 := rs (se 1 (by rfl) ⟨340682, by rfl⟩) R681365
theorem R149105 : Reach 149105 := rs (se 2 (by rfl) ⟨55914, by rfl⟩) R111829
theorem R3640945 : Reach 3640945 := rs (se 2 (by rfl) ⟨1365354, by rfl⟩) R2730709
theorem R112243 : Reach 112243 := rs (se 1 (by rfl) ⟨84182, by rfl⟩) R168365
theorem R167555 : Reach 167555 := rs (se 1 (by rfl) ⟨125666, by rfl⟩) R251333
theorem R149123 : Reach 149123 := rs (se 1 (by rfl) ⟨111842, by rfl⟩) R223685
theorem R335501 : Reach 335501 := rs (se 3 (by rfl) ⟨62906, by rfl⟩) R125813
theorem R149153 : Reach 149153 := rs (se 2 (by rfl) ⟨55932, by rfl⟩) R111865
theorem R106147 : Reach 106147 := rs (se 1 (by rfl) ⟨79610, by rfl⟩) R159221
theorem R149171 : Reach 149171 := rs (se 1 (by rfl) ⟨111878, by rfl⟩) R223757
theorem R335555 : Reach 335555 := rs (se 1 (by rfl) ⟨251666, by rfl⟩) R503333
theorem R149201 : Reach 149201 := rs (se 2 (by rfl) ⟨55950, by rfl⟩) R111901
theorem R149219 : Reach 149219 := rs (se 1 (by rfl) ⟨111914, by rfl⟩) R223829
theorem R849649 : Reach 849649 := rs (se 2 (by rfl) ⟨318618, by rfl⟩) R637237
theorem R149249 : Reach 149249 := rs (se 2 (by rfl) ⟨55968, by rfl⟩) R111937
theorem R167683 : Reach 167683 := rs (se 1 (by rfl) ⟨125762, by rfl⟩) R251525
theorem R638725 : Reach 638725 := rs (se 4 (by rfl) ⟨59880, by rfl⟩) R119761
theorem R376589 : Reach 376589 := rs (se 3 (by rfl) ⟨70610, by rfl⟩) R141221
theorem R268049 : Reach 268049 := rs (se 2 (by rfl) ⟨100518, by rfl⟩) R201037
theorem R149267 : Reach 149267 := rs (se 1 (by rfl) ⟨111950, by rfl⟩) R223901
theorem R143137 : Reach 143137 := rs (se 2 (by rfl) ⟨53676, by rfl⟩) R107353
theorem R149297 : Reach 149297 := rs (se 2 (by rfl) ⟨55986, by rfl⟩) R111973
theorem R149315 : Reach 149315 := rs (se 1 (by rfl) ⟨111986, by rfl⟩) R223973
theorem R378701 : Reach 378701 := rs (se 3 (by rfl) ⟨71006, by rfl⟩) R142013
theorem R149345 : Reach 149345 := rs (se 2 (by rfl) ⟨56004, by rfl⟩) R112009
theorem R143219 : Reach 143219 := rs (se 1 (by rfl) ⟨107414, by rfl⟩) R214829
theorem R149363 : Reach 149363 := rs (se 1 (by rfl) ⟨112022, by rfl⟩) R224045
theorem R159617 : Reach 159617 := rs (se 2 (by rfl) ⟨59856, by rfl⟩) R119713
theorem R167825 : Reach 167825 := rs (se 2 (by rfl) ⟨62934, by rfl⟩) R125869
theorem R149393 : Reach 149393 := rs (se 2 (by rfl) ⟨56022, by rfl⟩) R112045
theorem R149411 : Reach 149411 := rs (se 1 (by rfl) ⟨112058, by rfl⟩) R224117
theorem R149441 : Reach 149441 := rs (se 2 (by rfl) ⟨56040, by rfl⟩) R112081
theorem R335825 : Reach 335825 := rs (se 2 (by rfl) ⟨125934, by rfl⟩) R251869
theorem R149459 : Reach 149459 := rs (se 1 (by rfl) ⟨112094, by rfl⟩) R224189
theorem R223217 : Reach 223217 := rs (se 2 (by rfl) ⟨83706, by rfl⟩) R167413
theorem R188401 : Reach 188401 := rs (se 2 (by rfl) ⟨70650, by rfl⟩) R141301
theorem R149489 : Reach 149489 := rs (se 2 (by rfl) ⟨56058, by rfl⟩) R112117
theorem R755729 : Reach 755729 := rs (se 2 (by rfl) ⟨283398, by rfl⟩) R566797
theorem R223307 : Reach 223307 := rs (se 1 (by rfl) ⟨167480, by rfl⟩) R334961
theorem R149579 : Reach 149579 := rs (se 1 (by rfl) ⟨112184, by rfl⟩) R224369
theorem R120919 : Reach 120919 := rs (se 1 (by rfl) ⟨90689, by rfl⟩) R181379
theorem R149591 : Reach 149591 := rs (se 1 (by rfl) ⟨112193, by rfl⟩) R224387
theorem R223361 : Reach 223361 := rs (se 2 (by rfl) ⟨83760, by rfl⟩) R167521
theorem R149657 : Reach 149657 := rs (se 2 (by rfl) ⟨56121, by rfl⟩) R112243
theorem R141529 : Reach 141529 := rs (se 2 (by rfl) ⟨53073, by rfl⟩) R106147
theorem R188659 : Reach 188659 := rs (se 1 (by rfl) ⟨141494, by rfl⟩) R282989
theorem R168203 : Reach 168203 := rs (se 1 (by rfl) ⟨126152, by rfl⟩) R252305
theorem R1132865 : Reach 1132865 := rs (se 2 (by rfl) ⟨424824, by rfl⟩) R849649
theorem R336203 : Reach 336203 := rs (se 1 (by rfl) ⟨252152, by rfl⟩) R504305
theorem R223577 : Reach 223577 := rs (se 2 (by rfl) ⟨83841, by rfl⟩) R167683
theorem R168331 : Reach 168331 := rs (se 1 (by rfl) ⟨126248, by rfl⟩) R252497
theorem R223667 : Reach 223667 := rs (se 1 (by rfl) ⟨167750, by rfl⟩) R335501
theorem R223703 : Reach 223703 := rs (se 1 (by rfl) ⟨167777, by rfl⟩) R335555
theorem R188887 : Reach 188887 := rs (se 1 (by rfl) ⟨141665, by rfl⟩) R283331
theorem R178699 : Reach 178699 := rs (se 1 (by rfl) ⟨134024, by rfl⟩) R268049
theorem R1161745 : Reach 1161745 := rs (se 2 (by rfl) ⟨435654, by rfl⟩) R871309
theorem R252467 : Reach 252467 := rs (se 1 (by rfl) ⟨189350, by rfl⟩) R378701
theorem R188993 : Reach 188993 := rs (se 2 (by rfl) ⟨70872, by rfl⟩) R141745
theorem R336473 : Reach 336473 := rs (se 2 (by rfl) ⟨126177, by rfl⟩) R252355
theorem R223883 : Reach 223883 := rs (se 1 (by rfl) ⟨167912, by rfl⟩) R335825
theorem R223937 : Reach 223937 := rs (se 2 (by rfl) ⟨83976, by rfl⟩) R167953
theorem R377561 : Reach 377561 := rs (se 2 (by rfl) ⟨141585, by rfl⟩) R283171
theorem R189145 : Reach 189145 := rs (se 2 (by rfl) ⟨70929, by rfl⟩) R141859
theorem R125707 : Reach 125707 := rs (se 1 (by rfl) ⟨94280, by rfl⟩) R188561
theorem R805697 : Reach 805697 := rs (se 2 (by rfl) ⟨302136, by rfl⟩) R604273
theorem R4854593 : Reach 4854593 := rs (se 2 (by rfl) ⟨1820472, by rfl⟩) R3640945
theorem R99147 : Reach 99147 := rs (se 1 (by rfl) ⟨74360, by rfl⟩) R148721
theorem R99159 : Reach 99159 := rs (se 1 (by rfl) ⟨74369, by rfl⟩) R148739
theorem R99179 : Reach 99179 := rs (se 1 (by rfl) ⟨74384, by rfl⟩) R148769
theorem R99191 : Reach 99191 := rs (se 1 (by rfl) ⟨74393, by rfl⟩) R148787
theorem R99211 : Reach 99211 := rs (se 1 (by rfl) ⟨74408, by rfl⟩) R148817
theorem R99223 : Reach 99223 := rs (se 1 (by rfl) ⟨74417, by rfl⟩) R148835
theorem R224153 : Reach 224153 := rs (se 2 (by rfl) ⟨84057, by rfl⟩) R168115
theorem R99243 : Reach 99243 := rs (se 1 (by rfl) ⟨74432, by rfl⟩) R148865
theorem R283571 : Reach 283571 := rs (se 1 (by rfl) ⟨212678, by rfl⟩) R425357
theorem R99255 : Reach 99255 := rs (se 1 (by rfl) ⟨74441, by rfl⟩) R148883
theorem R99275 : Reach 99275 := rs (se 1 (by rfl) ⟨74456, by rfl⟩) R148913
theorem R99287 : Reach 99287 := rs (se 1 (by rfl) ⟨74465, by rfl⟩) R148931
theorem R381917 : Reach 381917 := rs (se 3 (by rfl) ⟨71609, by rfl⟩) R143219
theorem R111595 : Reach 111595 := rs (se 1 (by rfl) ⟨83696, by rfl⟩) R167393
theorem R99307 : Reach 99307 := rs (se 1 (by rfl) ⟨74480, by rfl⟩) R148961
theorem R224243 : Reach 224243 := rs (se 1 (by rfl) ⟨168182, by rfl⟩) R336365
theorem R99319 : Reach 99319 := rs (se 1 (by rfl) ⟨74489, by rfl⟩) R148979
theorem R99339 : Reach 99339 := rs (se 1 (by rfl) ⟨74504, by rfl⟩) R149009
theorem R99351 : Reach 99351 := rs (se 1 (by rfl) ⟨74513, by rfl⟩) R149027
theorem R125975 : Reach 125975 := rs (se 1 (by rfl) ⟨94481, by rfl⟩) R188963
theorem R224279 : Reach 224279 := rs (se 1 (by rfl) ⟨168209, by rfl⟩) R336419
theorem R99371 : Reach 99371 := rs (se 1 (by rfl) ⟨74528, by rfl⟩) R149057
theorem R113707 : Reach 113707 := rs (se 1 (by rfl) ⟨85280, by rfl⟩) R170561
theorem R99383 : Reach 99383 := rs (se 1 (by rfl) ⟨74537, by rfl⟩) R149075
theorem R99403 : Reach 99403 := rs (se 1 (by rfl) ⟨74552, by rfl⟩) R149105
theorem R179275 : Reach 179275 := rs (se 1 (by rfl) ⟨134456, by rfl⟩) R268913
theorem R111703 : Reach 111703 := rs (se 1 (by rfl) ⟨83777, by rfl⟩) R167555
theorem R99415 : Reach 99415 := rs (se 1 (by rfl) ⟨74561, by rfl⟩) R149123
theorem R99435 : Reach 99435 := rs (se 1 (by rfl) ⟨74576, by rfl⟩) R149153
theorem R99447 : Reach 99447 := rs (se 1 (by rfl) ⟨74585, by rfl⟩) R149171
theorem R99467 : Reach 99467 := rs (se 1 (by rfl) ⟨74600, by rfl⟩) R149201
theorem R99479 : Reach 99479 := rs (se 1 (by rfl) ⟨74609, by rfl⟩) R149219
theorem R99499 : Reach 99499 := rs (se 1 (by rfl) ⟨74624, by rfl⟩) R149249
theorem R251059 : Reach 251059 := rs (se 1 (by rfl) ⟨188294, by rfl⟩) R376589
theorem R99511 : Reach 99511 := rs (se 1 (by rfl) ⟨74633, by rfl⟩) R149267
theorem R394433 : Reach 394433 := rs (se 2 (by rfl) ⟨147912, by rfl⟩) R295825
theorem R99531 : Reach 99531 := rs (se 1 (by rfl) ⟨74648, by rfl⟩) R149297
theorem R224459 : Reach 224459 := rs (se 1 (by rfl) ⟨168344, by rfl⟩) R336689
theorem R99543 : Reach 99543 := rs (se 1 (by rfl) ⟨74657, by rfl⟩) R149315
theorem R335069 : Reach 335069 := rs (se 3 (by rfl) ⟨62825, by rfl⟩) R125651
theorem R99563 : Reach 99563 := rs (se 1 (by rfl) ⟨74672, by rfl⟩) R149345
theorem R99575 : Reach 99575 := rs (se 1 (by rfl) ⟨74681, by rfl⟩) R149363
theorem R111883 : Reach 111883 := rs (se 1 (by rfl) ⟨83912, by rfl⟩) R167825
theorem R99595 : Reach 99595 := rs (se 1 (by rfl) ⟨74696, by rfl⟩) R149393
theorem R99607 : Reach 99607 := rs (se 1 (by rfl) ⟨74705, by rfl⟩) R149411
theorem R99627 : Reach 99627 := rs (se 1 (by rfl) ⟨74720, by rfl⟩) R149441
theorem R402733 : Reach 402733 := rs (se 3 (by rfl) ⟨75512, by rfl⟩) R151025
theorem R204083 : Reach 204083 := rs (se 1 (by rfl) ⟨153062, by rfl⟩) R306125
theorem R99639 : Reach 99639 := rs (se 1 (by rfl) ⟨74729, by rfl⟩) R149459
theorem R251201 : Reach 251201 := rs (se 2 (by rfl) ⟨94200, by rfl⟩) R188401
theorem R148811 : Reach 148811 := rs (se 1 (by rfl) ⟨111608, by rfl⟩) R223217
theorem R806219 : Reach 806219 := rs (se 1 (by rfl) ⟨604664, by rfl⟩) R1209329
theorem R605515 : Reach 605515 := rs (se 1 (by rfl) ⟨454136, by rfl⟩) R908273
theorem R99659 : Reach 99659 := rs (se 1 (by rfl) ⟨74744, by rfl⟩) R149489
theorem R148823 : Reach 148823 := rs (se 1 (by rfl) ⟨111617, by rfl⟩) R223235
theorem R99671 : Reach 99671 := rs (se 1 (by rfl) ⟨74753, by rfl⟩) R149507
theorem R99691 : Reach 99691 := rs (se 1 (by rfl) ⟨74768, by rfl⟩) R149537
theorem R3231089 : Reach 3231089 := rs (se 2 (by rfl) ⟨1211658, by rfl⟩) R2423317
theorem R111991 : Reach 111991 := rs (se 1 (by rfl) ⟨83993, by rfl⟩) R167987
theorem R99703 : Reach 99703 := rs (se 1 (by rfl) ⟨74777, by rfl⟩) R149555
theorem R503171 : Reach 503171 := rs (se 1 (by rfl) ⟨377378, by rfl⟩) R754757
theorem R179585 : Reach 179585 := rs (se 2 (by rfl) ⟨67344, by rfl⟩) R134689
theorem R99723 : Reach 99723 := rs (se 1 (by rfl) ⟨74792, by rfl⟩) R149585
theorem R4078997 : Reach 4078997 := rs (se 6 (by rfl) ⟨95601, by rfl⟩) R191203
theorem R148889 : Reach 148889 := rs (se 2 (by rfl) ⟨55833, by rfl⟩) R111667
theorem R99735 : Reach 99735 := rs (se 1 (by rfl) ⟨74801, by rfl⟩) R149603
theorem R99755 : Reach 99755 := rs (se 1 (by rfl) ⟨74816, by rfl⟩) R149633
theorem R99767 : Reach 99767 := rs (se 1 (by rfl) ⟨74825, by rfl⟩) R149651
theorem R239041 : Reach 239041 := rs (se 2 (by rfl) ⟨89640, by rfl⟩) R179281
theorem R605657 : Reach 605657 := rs (se 2 (by rfl) ⟨227121, by rfl⟩) R454243
theorem R763397 : Reach 763397 := rs (se 4 (by rfl) ⟨71568, by rfl⟩) R143137
theorem R149003 : Reach 149003 := rs (se 1 (by rfl) ⟨111752, by rfl⟩) R223505
theorem R2870801 : Reach 2870801 := rs (se 2 (by rfl) ⟨1076550, by rfl⟩) R2153101
theorem R167447 : Reach 167447 := rs (se 1 (by rfl) ⟨125585, by rfl⟩) R251171
theorem R149015 : Reach 149015 := rs (se 1 (by rfl) ⟨111761, by rfl⟩) R223523
theorem R112171 : Reach 112171 := rs (se 1 (by rfl) ⟨84128, by rfl⟩) R168257
theorem R149081 : Reach 149081 := rs (se 2 (by rfl) ⟨55905, by rfl⟩) R111811
theorem R167575 : Reach 167575 := rs (se 1 (by rfl) ⟨125681, by rfl⟩) R251363
theorem R425645 : Reach 425645 := rs (se 3 (by rfl) ⟨79808, by rfl⟩) R159617
theorem R851633 : Reach 851633 := rs (se 2 (by rfl) ⟨319362, by rfl⟩) R638725
theorem R282305 : Reach 282305 := rs (se 2 (by rfl) ⟨105864, by rfl⟩) R211729
theorem R149195 : Reach 149195 := rs (se 1 (by rfl) ⟨111896, by rfl⟩) R223793
theorem R149207 : Reach 149207 := rs (se 1 (by rfl) ⟨111905, by rfl⟩) R223811
theorem R282329 : Reach 282329 := rs (se 2 (by rfl) ⟨105873, by rfl⟩) R211747
theorem R149273 : Reach 149273 := rs (se 2 (by rfl) ⟨55977, by rfl⟩) R111955
theorem R423731 : Reach 423731 := rs (se 1 (by rfl) ⟨317798, by rfl⟩) R635597
theorem R223091 : Reach 223091 := rs (se 1 (by rfl) ⟨167318, by rfl⟩) R334637
theorem R149387 : Reach 149387 := rs (se 1 (by rfl) ⟨112040, by rfl⟩) R224081
theorem R223127 : Reach 223127 := rs (se 1 (by rfl) ⟨167345, by rfl⟩) R334691
theorem R149399 : Reach 149399 := rs (se 1 (by rfl) ⟨112049, by rfl⟩) R224099
theorem R358361 : Reach 358361 := rs (se 2 (by rfl) ⟨134385, by rfl⟩) R268771
theorem R149465 : Reach 149465 := rs (se 2 (by rfl) ⟨56049, by rfl⟩) R112099
theorem R503819 : Reach 503819 := rs (se 1 (by rfl) ⟨377864, by rfl⟩) R755729
theorem R149519 : Reach 149519 := rs (se 1 (by rfl) ⟨112139, by rfl⟩) R224279
theorem R149561 : Reach 149561 := rs (se 2 (by rfl) ⟨56085, by rfl⟩) R112171
theorem R335933 : Reach 335933 := rs (se 3 (by rfl) ⟨62987, by rfl⟩) R125975
theorem R149639 : Reach 149639 := rs (se 1 (by rfl) ⟨112229, by rfl⟩) R224459
theorem R223379 : Reach 223379 := rs (se 1 (by rfl) ⟨167534, by rfl⟩) R335069
theorem R503981 : Reach 503981 := rs (se 3 (by rfl) ⟨94496, by rfl⟩) R188993
theorem R223433 : Reach 223433 := rs (se 2 (by rfl) ⟨83787, by rfl⟩) R167575
theorem R606437 : Reach 606437 := rs (se 4 (by rfl) ⟨56853, by rfl⟩) R113707
theorem R119723 : Reach 119723 := rs (se 1 (by rfl) ⟨89792, by rfl⟩) R179585
theorem R188705 : Reach 188705 := rs (se 2 (by rfl) ⟨70764, by rfl⟩) R141529
theorem R252193 : Reach 252193 := rs (se 2 (by rfl) ⟨94572, by rfl⟩) R189145
theorem R168311 : Reach 168311 := rs (se 1 (by rfl) ⟨126233, by rfl⟩) R252467
theorem R536977 : Reach 536977 := rs (se 2 (by rfl) ⟨201366, by rfl⟩) R402733
theorem R807353 : Reach 807353 := rs (se 2 (by rfl) ⟨302757, by rfl⟩) R605515
theorem R567755 : Reach 567755 := rs (se 1 (by rfl) ⟨425816, by rfl⟩) R851633
theorem R537131 : Reach 537131 := rs (se 1 (by rfl) ⟨402848, by rfl⟩) R805697
theorem R3236395 : Reach 3236395 := rs (se 1 (by rfl) ⟨2427296, by rfl⟩) R4854593
theorem R189047 : Reach 189047 := rs (se 1 (by rfl) ⟨141785, by rfl⟩) R283571
theorem R254611 : Reach 254611 := rs (se 1 (by rfl) ⟨190958, by rfl⟩) R381917
theorem R4207285 : Reach 4207285 := rs (se 5 (by rfl) ⟨197216, by rfl⟩) R394433
theorem R238265 : Reach 238265 := rs (se 2 (by rfl) ⟨89349, by rfl⟩) R178699
theorem R6195973 : Reach 6195973 := rs (se 4 (by rfl) ⟨580872, by rfl⟩) R1161745
theorem R99207 : Reach 99207 := rs (se 1 (by rfl) ⟨74405, by rfl⟩) R148811
theorem R537479 : Reach 537479 := rs (se 1 (by rfl) ⟨403109, by rfl⟩) R806219
theorem R224135 : Reach 224135 := rs (se 1 (by rfl) ⟨168101, by rfl⟩) R336203
theorem R99215 : Reach 99215 := rs (se 1 (by rfl) ⟨74411, by rfl⟩) R148823
theorem R334745 : Reach 334745 := rs (se 2 (by rfl) ⟨125529, by rfl⟩) R251059
theorem R99259 : Reach 99259 := rs (se 1 (by rfl) ⟨74444, by rfl⟩) R148889
theorem R508931 : Reach 508931 := rs (se 1 (by rfl) ⟨381698, by rfl⟩) R763397
theorem R99335 : Reach 99335 := rs (se 1 (by rfl) ⟨74501, by rfl⟩) R149003
theorem R1274885 : Reach 1274885 := rs (se 4 (by rfl) ⟨119520, by rfl⟩) R239041
theorem R1913867 : Reach 1913867 := rs (se 1 (by rfl) ⟨1435400, by rfl⟩) R2870801
theorem R111631 : Reach 111631 := rs (se 1 (by rfl) ⟨83723, by rfl⟩) R167447
theorem R99343 : Reach 99343 := rs (se 1 (by rfl) ⟨74507, by rfl⟩) R149015
theorem R99387 : Reach 99387 := rs (se 1 (by rfl) ⟨74540, by rfl⟩) R149081
theorem R224315 : Reach 224315 := rs (se 1 (by rfl) ⟨168236, by rfl⟩) R336473
theorem R283763 : Reach 283763 := rs (se 1 (by rfl) ⟨212822, by rfl⟩) R425645
theorem R99463 : Reach 99463 := rs (se 1 (by rfl) ⟨74597, by rfl⟩) R149195
theorem R99471 : Reach 99471 := rs (se 1 (by rfl) ⟨74603, by rfl⟩) R149207
theorem R752813 : Reach 752813 := rs (se 3 (by rfl) ⟨141152, by rfl⟩) R282305
theorem R99515 : Reach 99515 := rs (se 1 (by rfl) ⟨74636, by rfl⟩) R149273
theorem R224441 : Reach 224441 := rs (se 2 (by rfl) ⟨84165, by rfl⟩) R168331
theorem R1615085 : Reach 1615085 := rs (se 3 (by rfl) ⟨302828, by rfl⟩) R605657
theorem R148727 : Reach 148727 := rs (se 1 (by rfl) ⟨111545, by rfl⟩) R223091
theorem R99591 : Reach 99591 := rs (se 1 (by rfl) ⟨74693, by rfl⟩) R149387
theorem R148751 : Reach 148751 := rs (se 1 (by rfl) ⟨111563, by rfl⟩) R223127
theorem R99599 : Reach 99599 := rs (se 1 (by rfl) ⟨74699, by rfl⟩) R149399
theorem R148793 : Reach 148793 := rs (se 2 (by rfl) ⟨55797, by rfl⟩) R111595
theorem R238907 : Reach 238907 := rs (se 1 (by rfl) ⟨179180, by rfl⟩) R358361
theorem R99643 : Reach 99643 := rs (se 1 (by rfl) ⟨74732, by rfl⟩) R149465
theorem R148871 : Reach 148871 := rs (se 1 (by rfl) ⟨111653, by rfl⟩) R223307
theorem R99719 : Reach 99719 := rs (se 1 (by rfl) ⟨74789, by rfl⟩) R149579
theorem R99727 : Reach 99727 := rs (se 1 (by rfl) ⟨74795, by rfl⟩) R149591
theorem R148907 : Reach 148907 := rs (se 1 (by rfl) ⟨111680, by rfl⟩) R223361
theorem R239033 : Reach 239033 := rs (se 2 (by rfl) ⟨89637, by rfl⟩) R179275
theorem R99771 : Reach 99771 := rs (se 1 (by rfl) ⟨74828, by rfl⟩) R149657
theorem R161225 : Reach 161225 := rs (se 2 (by rfl) ⟨60459, by rfl⟩) R120919
theorem R148937 : Reach 148937 := rs (se 2 (by rfl) ⟨55851, by rfl⟩) R111703
theorem R1129949 : Reach 1129949 := rs (se 3 (by rfl) ⟨211865, by rfl⟩) R423731
theorem R112135 : Reach 112135 := rs (se 1 (by rfl) ⟨84101, by rfl⟩) R168203
theorem R167467 : Reach 167467 := rs (se 1 (by rfl) ⟨125600, by rfl⟩) R251201
theorem R755243 : Reach 755243 := rs (se 1 (by rfl) ⟨566432, by rfl⟩) R1132865
theorem R149051 : Reach 149051 := rs (se 1 (by rfl) ⟨111788, by rfl⟩) R223577
theorem R2154059 : Reach 2154059 := rs (se 1 (by rfl) ⟨1615544, by rfl⟩) R3231089
theorem R335447 : Reach 335447 := rs (se 1 (by rfl) ⟨251585, by rfl⟩) R503171
theorem R2719331 : Reach 2719331 := rs (se 1 (by rfl) ⟨2039498, by rfl⟩) R4078997
theorem R149111 : Reach 149111 := rs (se 1 (by rfl) ⟨111833, by rfl⟩) R223667
theorem R149135 : Reach 149135 := rs (se 1 (by rfl) ⟨111851, by rfl⟩) R223703
theorem R251545 : Reach 251545 := rs (se 2 (by rfl) ⟨94329, by rfl⟩) R188659
theorem R167609 : Reach 167609 := rs (se 2 (by rfl) ⟨62853, by rfl⟩) R125707
theorem R149177 : Reach 149177 := rs (se 2 (by rfl) ⟨55941, by rfl⟩) R111883
theorem R149255 : Reach 149255 := rs (se 1 (by rfl) ⟨111941, by rfl⟩) R223883
theorem R149291 : Reach 149291 := rs (se 1 (by rfl) ⟨111968, by rfl⟩) R223937
theorem R188219 : Reach 188219 := rs (se 1 (by rfl) ⟨141164, by rfl⟩) R282329
theorem R251707 : Reach 251707 := rs (se 1 (by rfl) ⟨188780, by rfl⟩) R377561
theorem R149321 : Reach 149321 := rs (se 2 (by rfl) ⟨55995, by rfl⟩) R111991
theorem R2176885 : Reach 2176885 := rs (se 5 (by rfl) ⟨102041, by rfl⟩) R204083
theorem R149435 : Reach 149435 := rs (se 1 (by rfl) ⟨112076, by rfl⟩) R224153
theorem R251849 : Reach 251849 := rs (se 2 (by rfl) ⟨94443, by rfl⟩) R188887
theorem R149495 : Reach 149495 := rs (se 1 (by rfl) ⟨112121, by rfl⟩) R224243
theorem R849923 : Reach 849923 := rs (se 1 (by rfl) ⟨637442, by rfl⟩) R1274885
theorem R335879 : Reach 335879 := rs (se 1 (by rfl) ⟨251909, by rfl⟩) R503819
theorem R1275911 : Reach 1275911 := rs (se 1 (by rfl) ⟨956933, by rfl⟩) R1913867
theorem R149513 : Reach 149513 := rs (se 2 (by rfl) ⟨56067, by rfl⟩) R112135
theorem R149543 : Reach 149543 := rs (se 1 (by rfl) ⟨112157, by rfl⟩) R224315
theorem R223289 : Reach 223289 := rs (se 2 (by rfl) ⟨83733, by rfl⟩) R167467
theorem R4315193 : Reach 4315193 := rs (se 2 (by rfl) ⟨1618197, by rfl⟩) R3236395
theorem R501875 : Reach 501875 := rs (se 1 (by rfl) ⟨376406, by rfl⟩) R752813
theorem R335987 : Reach 335987 := rs (se 1 (by rfl) ⟨251990, by rfl⟩) R503981
theorem R149627 : Reach 149627 := rs (se 1 (by rfl) ⟨112220, by rfl⟩) R224441
theorem R637085 : Reach 637085 := rs (se 3 (by rfl) ⟨119453, by rfl⟩) R238907
theorem R336257 : Reach 336257 := rs (se 2 (by rfl) ⟨126096, by rfl⟩) R252193
theorem R1436039 : Reach 1436039 := rs (se 1 (by rfl) ⟨1077029, by rfl⟩) R2154059
theorem R223631 : Reach 223631 := rs (se 1 (by rfl) ⟨167723, by rfl⟩) R335447
theorem R1812887 : Reach 1812887 := rs (se 1 (by rfl) ⟨1359665, by rfl⟩) R2719331
theorem R125479 : Reach 125479 := rs (se 1 (by rfl) ⟨94109, by rfl⟩) R188219
theorem R223955 : Reach 223955 := rs (se 1 (by rfl) ⟨167966, by rfl⟩) R335933
theorem R1432349 : Reach 1432349 := rs (se 3 (by rfl) ⟨268565, by rfl⟩) R537131
theorem R404291 : Reach 404291 := rs (se 1 (by rfl) ⟨303218, by rfl⟩) R606437
theorem R99151 : Reach 99151 := rs (se 1 (by rfl) ⟨74363, by rfl⟩) R148727
theorem R99167 : Reach 99167 := rs (se 1 (by rfl) ⟨74375, by rfl⟩) R148751
theorem R125803 : Reach 125803 := rs (se 1 (by rfl) ⟨94352, by rfl⟩) R188705
theorem R99195 : Reach 99195 := rs (se 1 (by rfl) ⟨74396, by rfl⟩) R148793
theorem R99247 : Reach 99247 := rs (se 1 (by rfl) ⟨74435, by rfl⟩) R148871
theorem R22438853 : Reach 22438853 := rs (se 4 (by rfl) ⟨2103642, by rfl⟩) R4207285
theorem R99271 : Reach 99271 := rs (se 1 (by rfl) ⟨74453, by rfl⟩) R148907
theorem R99291 : Reach 99291 := rs (se 1 (by rfl) ⟨74468, by rfl⟩) R148937
theorem R107483 : Reach 107483 := rs (se 1 (by rfl) ⟨80612, by rfl⟩) R161225
theorem R756701 : Reach 756701 := rs (se 3 (by rfl) ⟨141881, by rfl⟩) R283763
theorem R99367 : Reach 99367 := rs (se 1 (by rfl) ⟨74525, by rfl⟩) R149051
theorem R99407 : Reach 99407 := rs (se 1 (by rfl) ⟨74555, by rfl⟩) R149111
theorem R126031 : Reach 126031 := rs (se 1 (by rfl) ⟨94523, by rfl⟩) R189047
theorem R99423 : Reach 99423 := rs (se 1 (by rfl) ⟨74567, by rfl⟩) R149135
theorem R158843 : Reach 158843 := rs (se 1 (by rfl) ⟨119132, by rfl⟩) R238265
theorem R111739 : Reach 111739 := rs (se 1 (by rfl) ⟨83804, by rfl⟩) R167609
theorem R99451 : Reach 99451 := rs (se 1 (by rfl) ⟨74588, by rfl⟩) R149177
theorem R99503 : Reach 99503 := rs (se 1 (by rfl) ⟨74627, by rfl⟩) R149255
theorem R715969 : Reach 715969 := rs (se 2 (by rfl) ⟨268488, by rfl⟩) R536977
theorem R99527 : Reach 99527 := rs (se 1 (by rfl) ⟨74645, by rfl⟩) R149291
theorem R99547 : Reach 99547 := rs (se 1 (by rfl) ⟨74660, by rfl⟩) R149321
theorem R99623 : Reach 99623 := rs (se 1 (by rfl) ⟨74717, by rfl⟩) R149435
theorem R99663 : Reach 99663 := rs (se 1 (by rfl) ⟨74747, by rfl⟩) R149495
theorem R339287 : Reach 339287 := rs (se 1 (by rfl) ⟨254465, by rfl⟩) R508931
theorem R99679 : Reach 99679 := rs (se 1 (by rfl) ⟨74759, by rfl⟩) R149519
theorem R148841 : Reach 148841 := rs (se 2 (by rfl) ⟨55815, by rfl⟩) R111631
theorem R99707 : Reach 99707 := rs (se 1 (by rfl) ⟨74780, by rfl⟩) R149561
theorem R99759 : Reach 99759 := rs (se 1 (by rfl) ⟨74819, by rfl⟩) R149639
theorem R148919 : Reach 148919 := rs (se 1 (by rfl) ⟨111689, by rfl⟩) R223379
theorem R148955 : Reach 148955 := rs (se 1 (by rfl) ⟨111716, by rfl⟩) R223433
theorem R1076723 : Reach 1076723 := rs (se 1 (by rfl) ⟨807542, by rfl⟩) R1615085
theorem R339481 : Reach 339481 := rs (se 2 (by rfl) ⟨127305, by rfl⟩) R254611
theorem R335393 : Reach 335393 := rs (se 2 (by rfl) ⟨125772, by rfl⟩) R251545
theorem R112207 : Reach 112207 := rs (se 1 (by rfl) ⟨84155, by rfl⟩) R168311
theorem R159355 : Reach 159355 := rs (se 1 (by rfl) ⟨119516, by rfl⟩) R239033
theorem R538235 : Reach 538235 := rs (se 1 (by rfl) ⟨403676, by rfl⟩) R807353
theorem R378503 : Reach 378503 := rs (se 1 (by rfl) ⟨283877, by rfl⟩) R567755
theorem R753299 : Reach 753299 := rs (se 1 (by rfl) ⟨564974, by rfl⟩) R1129949
theorem R8261297 : Reach 8261297 := rs (se 2 (by rfl) ⟨3097986, by rfl⟩) R6195973
theorem R503495 : Reach 503495 := rs (se 1 (by rfl) ⟨377621, by rfl⟩) R755243
theorem R335609 : Reach 335609 := rs (se 2 (by rfl) ⟨125853, by rfl⟩) R251707
theorem R319261 : Reach 319261 := rs (se 3 (by rfl) ⟨59861, by rfl⟩) R119723
theorem R358319 : Reach 358319 := rs (se 1 (by rfl) ⟨268739, by rfl⟩) R537479
theorem R149423 : Reach 149423 := rs (se 1 (by rfl) ⟨112067, by rfl⟩) R224135
theorem R223163 : Reach 223163 := rs (se 1 (by rfl) ⟨167372, by rfl⟩) R334745
theorem R11610053 : Reach 11610053 := rs (se 4 (by rfl) ⟨1088442, by rfl⟩) R2176885
theorem R167899 : Reach 167899 := rs (se 1 (by rfl) ⟨125924, by rfl⟩) R251849
theorem R452641 : Reach 452641 := rs (se 2 (by rfl) ⟨169740, by rfl⟩) R339481
theorem R168041 : Reach 168041 := rs (se 2 (by rfl) ⟨63015, by rfl⟩) R126031
theorem R149609 : Reach 149609 := rs (se 2 (by rfl) ⟨56103, by rfl⟩) R112207
theorem R1208591 : Reach 1208591 := rs (se 1 (by rfl) ⟨906443, by rfl⟩) R1812887
theorem R223595 : Reach 223595 := rs (se 1 (by rfl) ⟨167696, by rfl⟩) R335393
theorem R358823 : Reach 358823 := rs (se 1 (by rfl) ⟨269117, by rfl⟩) R538235
theorem R252335 : Reach 252335 := rs (se 1 (by rfl) ⟨189251, by rfl⟩) R378503
theorem R502199 : Reach 502199 := rs (se 1 (by rfl) ⟨376649, by rfl⟩) R753299
theorem R5507531 : Reach 5507531 := rs (se 1 (by rfl) ⟨4130648, by rfl⟩) R8261297
theorem R223739 : Reach 223739 := rs (se 1 (by rfl) ⟨167804, by rfl⟩) R335609
theorem R954899 : Reach 954899 := rs (se 1 (by rfl) ⟨716174, by rfl⟩) R1432349
theorem R223865 : Reach 223865 := rs (se 2 (by rfl) ⟨83949, by rfl⟩) R167899
theorem R7740035 : Reach 7740035 := rs (se 1 (by rfl) ⟨5805026, by rfl⟩) R11610053
theorem R14959235 : Reach 14959235 := rs (se 1 (by rfl) ⟨11219426, by rfl⟩) R22438853
theorem R504467 : Reach 504467 := rs (se 1 (by rfl) ⟨378350, by rfl⟩) R756701
theorem R2876795 : Reach 2876795 := rs (se 1 (by rfl) ⟨2157596, by rfl⟩) R4315193
theorem R223919 : Reach 223919 := rs (se 1 (by rfl) ⟨167939, by rfl⟩) R335879
theorem R850607 : Reach 850607 := rs (se 1 (by rfl) ⟨637955, by rfl⟩) R1275911
theorem R334583 : Reach 334583 := rs (se 1 (by rfl) ⟨250937, by rfl⟩) R501875
theorem R223991 : Reach 223991 := rs (se 1 (by rfl) ⟨167993, by rfl⟩) R335987
theorem R424723 : Reach 424723 := rs (se 1 (by rfl) ⟨318542, by rfl⟩) R637085
theorem R1078109 : Reach 1078109 := rs (se 3 (by rfl) ⟨202145, by rfl⟩) R404291
theorem R99227 : Reach 99227 := rs (se 1 (by rfl) ⟨74420, by rfl⟩) R148841
theorem R957359 : Reach 957359 := rs (se 1 (by rfl) ⟨718019, by rfl⟩) R1436039
theorem R224171 : Reach 224171 := rs (se 1 (by rfl) ⟨168128, by rfl⟩) R336257
theorem R99279 : Reach 99279 := rs (se 1 (by rfl) ⟨74459, by rfl⟩) R148919
theorem R99303 : Reach 99303 := rs (se 1 (by rfl) ⟨74477, by rfl⟩) R148955
theorem R717815 : Reach 717815 := rs (se 1 (by rfl) ⟨538361, by rfl⟩) R1076723
theorem R3818501 : Reach 3818501 := rs (se 4 (by rfl) ⟨357984, by rfl⟩) R715969
theorem R238879 : Reach 238879 := rs (se 1 (by rfl) ⟨179159, by rfl⟩) R358319
theorem R99615 : Reach 99615 := rs (se 1 (by rfl) ⟨74711, by rfl⟩) R149423
theorem R148775 : Reach 148775 := rs (se 1 (by rfl) ⟨111581, by rfl⟩) R223163
theorem R566615 : Reach 566615 := rs (se 1 (by rfl) ⟨424961, by rfl⟩) R849923
theorem R99675 : Reach 99675 := rs (se 1 (by rfl) ⟨74756, by rfl⟩) R149513
theorem R99695 : Reach 99695 := rs (se 1 (by rfl) ⟨74771, by rfl⟩) R149543
theorem R148859 : Reach 148859 := rs (se 1 (by rfl) ⟨111644, by rfl⟩) R223289
theorem R167305 : Reach 167305 := rs (se 2 (by rfl) ⟨62739, by rfl⟩) R125479
theorem R105895 : Reach 105895 := rs (se 1 (by rfl) ⟨79421, by rfl⟩) R158843
theorem R99751 : Reach 99751 := rs (se 1 (by rfl) ⟨74813, by rfl⟩) R149627
theorem R148985 : Reach 148985 := rs (se 2 (by rfl) ⟨55869, by rfl⟩) R111739
theorem R212473 : Reach 212473 := rs (se 2 (by rfl) ⟨79677, by rfl⟩) R159355
theorem R904765 : Reach 904765 := rs (se 3 (by rfl) ⟨169643, by rfl⟩) R339287
theorem R149087 : Reach 149087 := rs (se 1 (by rfl) ⟨111815, by rfl⟩) R223631
theorem R425681 : Reach 425681 := rs (se 2 (by rfl) ⟨159630, by rfl⟩) R319261
theorem R335663 : Reach 335663 := rs (se 1 (by rfl) ⟨251747, by rfl⟩) R503495
theorem R149303 : Reach 149303 := rs (se 1 (by rfl) ⟨111977, by rfl⟩) R223955
theorem R167737 : Reach 167737 := rs (se 2 (by rfl) ⟨62901, by rfl⟩) R125803
theorem R286621 : Reach 286621 := rs (se 3 (by rfl) ⟨53741, by rfl⟩) R107483
theorem R2545667 : Reach 2545667 := rs (se 1 (by rfl) ⟨1909250, by rfl⟩) R3818501
theorem R1206353 : Reach 1206353 := rs (se 2 (by rfl) ⟨452382, by rfl⟩) R904765
theorem R168223 : Reach 168223 := rs (se 1 (by rfl) ⟨126167, by rfl⟩) R252335
theorem R223649 : Reach 223649 := rs (se 2 (by rfl) ⟨83868, by rfl⟩) R167737
theorem R336311 : Reach 336311 := rs (se 1 (by rfl) ⟨252233, by rfl⟩) R504467
theorem R223775 : Reach 223775 := rs (se 1 (by rfl) ⟨167831, by rfl⟩) R335663
theorem R283297 : Reach 283297 := rs (se 2 (by rfl) ⟨106236, by rfl⟩) R212473
theorem R1528645 : Reach 1528645 := rs (se 4 (by rfl) ⟨143310, by rfl⟩) R286621
theorem R805727 : Reach 805727 := rs (se 1 (by rfl) ⟨604295, by rfl⟩) R1208591
theorem R99183 : Reach 99183 := rs (se 1 (by rfl) ⟨74387, by rfl⟩) R148775
theorem R377743 : Reach 377743 := rs (se 1 (by rfl) ⟨283307, by rfl⟩) R566615
theorem R99239 : Reach 99239 := rs (se 1 (by rfl) ⟨74429, by rfl⟩) R148859
theorem R1917863 : Reach 1917863 := rs (se 1 (by rfl) ⟨1438397, by rfl⟩) R2876795
theorem R334799 : Reach 334799 := rs (se 1 (by rfl) ⟨251099, by rfl⟩) R502199
theorem R99323 : Reach 99323 := rs (se 1 (by rfl) ⟨74492, by rfl⟩) R148985
theorem R566297 : Reach 566297 := rs (se 2 (by rfl) ⟨212361, by rfl⟩) R424723
theorem R318505 : Reach 318505 := rs (se 2 (by rfl) ⟨119439, by rfl⟩) R238879
theorem R99391 : Reach 99391 := rs (se 1 (by rfl) ⟨74543, by rfl⟩) R149087
theorem R5160023 : Reach 5160023 := rs (se 1 (by rfl) ⟨3870017, by rfl⟩) R7740035
theorem R9972823 : Reach 9972823 := rs (se 1 (by rfl) ⟨7479617, by rfl⟩) R14959235
theorem R283787 : Reach 283787 := rs (se 1 (by rfl) ⟨212840, by rfl⟩) R425681
theorem R99535 : Reach 99535 := rs (se 1 (by rfl) ⟨74651, by rfl⟩) R149303
theorem R638239 : Reach 638239 := rs (se 1 (by rfl) ⟨478679, by rfl⟩) R957359
theorem R478543 : Reach 478543 := rs (se 1 (by rfl) ⟨358907, by rfl⟩) R717815
theorem R603521 : Reach 603521 := rs (se 2 (by rfl) ⟨226320, by rfl⟩) R452641
theorem R112027 : Reach 112027 := rs (se 1 (by rfl) ⟨84020, by rfl⟩) R168041
theorem R99739 : Reach 99739 := rs (se 1 (by rfl) ⟨74804, by rfl⟩) R149609
theorem R149063 : Reach 149063 := rs (se 1 (by rfl) ⟨111797, by rfl⟩) R223595
theorem R239215 : Reach 239215 := rs (se 1 (by rfl) ⟨179411, by rfl⟩) R358823
theorem R3671687 : Reach 3671687 := rs (se 1 (by rfl) ⟨2753765, by rfl⟩) R5507531
theorem R149159 : Reach 149159 := rs (se 1 (by rfl) ⟨111869, by rfl⟩) R223739
theorem R636599 : Reach 636599 := rs (se 1 (by rfl) ⟨477449, by rfl⟩) R954899
theorem R149243 : Reach 149243 := rs (se 1 (by rfl) ⟨111932, by rfl⟩) R223865
theorem R149279 : Reach 149279 := rs (se 1 (by rfl) ⟨111959, by rfl⟩) R223919
theorem R567071 : Reach 567071 := rs (se 1 (by rfl) ⟨425303, by rfl⟩) R850607
theorem R223055 : Reach 223055 := rs (se 1 (by rfl) ⟨167291, by rfl⟩) R334583
theorem R149327 : Reach 149327 := rs (se 1 (by rfl) ⟨111995, by rfl⟩) R223991
theorem R223073 : Reach 223073 := rs (se 2 (by rfl) ⟨83652, by rfl⟩) R167305
theorem R141193 : Reach 141193 := rs (se 2 (by rfl) ⟨52947, by rfl⟩) R105895
theorem R718739 : Reach 718739 := rs (se 1 (by rfl) ⟨539054, by rfl⟩) R1078109
theorem R149447 : Reach 149447 := rs (se 1 (by rfl) ⟨112085, by rfl⟩) R224171
theorem R2148605 : Reach 2148605 := rs (se 3 (by rfl) ⟨402863, by rfl⟩) R805727
theorem R2038193 : Reach 2038193 := rs (se 2 (by rfl) ⟨764322, by rfl⟩) R1528645
theorem R424399 : Reach 424399 := rs (se 1 (by rfl) ⟨318299, by rfl⟩) R636599
theorem R1278575 : Reach 1278575 := rs (se 1 (by rfl) ⟨958931, by rfl⟩) R1917863
theorem R377531 : Reach 377531 := rs (se 1 (by rfl) ⟨283148, by rfl⟩) R566297
theorem R424673 : Reach 424673 := rs (se 2 (by rfl) ⟨159252, by rfl⟩) R318505
theorem R189191 : Reach 189191 := rs (se 1 (by rfl) ⟨141893, by rfl⟩) R283787
theorem R377729 : Reach 377729 := rs (se 2 (by rfl) ⟨141648, by rfl⟩) R283297
theorem R402347 : Reach 402347 := rs (se 1 (by rfl) ⟨301760, by rfl⟩) R603521
theorem R224207 : Reach 224207 := rs (se 1 (by rfl) ⟨168155, by rfl⟩) R336311
theorem R850985 : Reach 850985 := rs (se 2 (by rfl) ⟨319119, by rfl⟩) R638239
theorem R224297 : Reach 224297 := rs (se 2 (by rfl) ⟨84111, by rfl⟩) R168223
theorem R99375 : Reach 99375 := rs (se 1 (by rfl) ⟨74531, by rfl⟩) R149063
theorem R99439 : Reach 99439 := rs (se 1 (by rfl) ⟨74579, by rfl⟩) R149159
theorem R638057 : Reach 638057 := rs (se 2 (by rfl) ⟨239271, by rfl⟩) R478543
theorem R99495 : Reach 99495 := rs (se 1 (by rfl) ⟨74621, by rfl⟩) R149243
theorem R99519 : Reach 99519 := rs (se 1 (by rfl) ⟨74639, by rfl⟩) R149279
theorem R378047 : Reach 378047 := rs (se 1 (by rfl) ⟨283535, by rfl⟩) R567071
theorem R148703 : Reach 148703 := rs (se 1 (by rfl) ⟨111527, by rfl⟩) R223055
theorem R99551 : Reach 99551 := rs (se 1 (by rfl) ⟨74663, by rfl⟩) R149327
theorem R148715 : Reach 148715 := rs (se 1 (by rfl) ⟨111536, by rfl⟩) R223073
theorem R99631 : Reach 99631 := rs (se 1 (by rfl) ⟨74723, by rfl⟩) R149447
theorem R1697111 : Reach 1697111 := rs (se 1 (by rfl) ⟨1272833, by rfl⟩) R2545667
theorem R3440015 : Reach 3440015 := rs (se 1 (by rfl) ⟨2580011, by rfl⟩) R5160023
theorem R13297097 : Reach 13297097 := rs (se 2 (by rfl) ⟨4986411, by rfl⟩) R9972823
theorem R318953 : Reach 318953 := rs (se 2 (by rfl) ⟨119607, by rfl⟩) R239215
theorem R3216941 : Reach 3216941 := rs (se 3 (by rfl) ⟨603176, by rfl⟩) R1206353
theorem R149099 : Reach 149099 := rs (se 1 (by rfl) ⟨111824, by rfl⟩) R223649
theorem R9791165 : Reach 9791165 := rs (se 3 (by rfl) ⟨1835843, by rfl⟩) R3671687
theorem R149183 : Reach 149183 := rs (se 1 (by rfl) ⟨111887, by rfl⟩) R223775
theorem R188257 : Reach 188257 := rs (se 2 (by rfl) ⟨70596, by rfl⟩) R141193
theorem R503657 : Reach 503657 := rs (se 2 (by rfl) ⟨188871, by rfl⟩) R377743
theorem R149369 : Reach 149369 := rs (se 2 (by rfl) ⟨56013, by rfl⟩) R112027
theorem R479159 : Reach 479159 := rs (se 1 (by rfl) ⟨359369, by rfl⟩) R718739
theorem R223199 : Reach 223199 := rs (se 1 (by rfl) ⟨167399, by rfl⟩) R334799
theorem R567323 : Reach 567323 := rs (se 1 (by rfl) ⟨425492, by rfl⟩) R850985
theorem R149531 : Reach 149531 := rs (se 1 (by rfl) ⟨112148, by rfl⟩) R224297
theorem R252031 : Reach 252031 := rs (se 1 (by rfl) ⟨189023, by rfl⟩) R378047
theorem R2144627 : Reach 2144627 := rs (se 1 (by rfl) ⟨1608470, by rfl⟩) R3216941
theorem R852383 : Reach 852383 := rs (se 1 (by rfl) ⟨639287, by rfl⟩) R1278575
theorem R283115 : Reach 283115 := rs (se 1 (by rfl) ⟨212336, by rfl⟩) R424673
theorem R565865 : Reach 565865 := rs (se 2 (by rfl) ⟨212199, by rfl⟩) R424399
theorem R99135 : Reach 99135 := rs (se 1 (by rfl) ⟨74351, by rfl⟩) R148703
theorem R99143 : Reach 99143 := rs (se 1 (by rfl) ⟨74357, by rfl⟩) R148715
theorem R1432403 : Reach 1432403 := rs (se 1 (by rfl) ⟨1074302, by rfl⟩) R2148605
theorem R1131407 : Reach 1131407 := rs (se 1 (by rfl) ⟨848555, by rfl⟩) R1697111
theorem R1358795 : Reach 1358795 := rs (se 1 (by rfl) ⟨1019096, by rfl⟩) R2038193
theorem R8864731 : Reach 8864731 := rs (se 1 (by rfl) ⟨6648548, by rfl⟩) R13297097
theorem R99399 : Reach 99399 := rs (se 1 (by rfl) ⟨74549, by rfl⟩) R149099
theorem R99455 : Reach 99455 := rs (se 1 (by rfl) ⟨74591, by rfl⟩) R149183
theorem R251009 : Reach 251009 := rs (se 2 (by rfl) ⟨94128, by rfl⟩) R188257
theorem R126127 : Reach 126127 := rs (se 1 (by rfl) ⟨94595, by rfl⟩) R189191
theorem R99579 : Reach 99579 := rs (se 1 (by rfl) ⟨74684, by rfl⟩) R149369
theorem R148799 : Reach 148799 := rs (se 1 (by rfl) ⟨111599, by rfl⟩) R223199
theorem R2293343 : Reach 2293343 := rs (se 1 (by rfl) ⟨1720007, by rfl⟩) R3440015
theorem R1701485 : Reach 1701485 := rs (se 3 (by rfl) ⟨319028, by rfl⟩) R638057
theorem R212635 : Reach 212635 := rs (se 1 (by rfl) ⟨159476, by rfl⟩) R318953
theorem R251687 : Reach 251687 := rs (se 1 (by rfl) ⟨188765, by rfl⟩) R377531
theorem R26109773 : Reach 26109773 := rs (se 3 (by rfl) ⟨4895582, by rfl⟩) R9791165
theorem R335771 : Reach 335771 := rs (se 1 (by rfl) ⟨251828, by rfl⟩) R503657
theorem R251819 : Reach 251819 := rs (se 1 (by rfl) ⟨188864, by rfl⟩) R377729
theorem R268231 : Reach 268231 := rs (se 1 (by rfl) ⟨201173, by rfl⟩) R402347
theorem R319439 : Reach 319439 := rs (se 1 (by rfl) ⟨239579, by rfl⟩) R479159
theorem R149471 : Reach 149471 := rs (se 1 (by rfl) ⟨112103, by rfl⟩) R224207
theorem R336041 : Reach 336041 := rs (se 2 (by rfl) ⟨126015, by rfl⟩) R252031
theorem R168169 : Reach 168169 := rs (se 2 (by rfl) ⟨63063, by rfl⟩) R126127
theorem R1429751 : Reach 1429751 := rs (se 1 (by rfl) ⟨1072313, by rfl⟩) R2144627
theorem R188743 : Reach 188743 := rs (se 1 (by rfl) ⟨141557, by rfl⟩) R283115
theorem R377243 : Reach 377243 := rs (se 1 (by rfl) ⟨282932, by rfl⟩) R565865
theorem R17406515 : Reach 17406515 := rs (se 1 (by rfl) ⟨13054886, by rfl⟩) R26109773
theorem R954935 : Reach 954935 := rs (se 1 (by rfl) ⟨716201, by rfl⟩) R1432403
theorem R754271 : Reach 754271 := rs (se 1 (by rfl) ⟨565703, by rfl⟩) R1131407
theorem R223847 : Reach 223847 := rs (se 1 (by rfl) ⟨167885, by rfl⟩) R335771
theorem R11819641 : Reach 11819641 := rs (se 2 (by rfl) ⟨4432365, by rfl⟩) R8864731
theorem R905863 : Reach 905863 := rs (se 1 (by rfl) ⟨679397, by rfl⟩) R1358795
theorem R283513 : Reach 283513 := rs (se 2 (by rfl) ⟨106317, by rfl⟩) R212635
theorem R99199 : Reach 99199 := rs (se 1 (by rfl) ⟨74399, by rfl⟩) R148799
theorem R568255 : Reach 568255 := rs (se 1 (by rfl) ⟨426191, by rfl⟩) R852383
theorem R1528895 : Reach 1528895 := rs (se 1 (by rfl) ⟨1146671, by rfl⟩) R2293343
theorem R357641 : Reach 357641 := rs (se 2 (by rfl) ⟨134115, by rfl⟩) R268231
theorem R99647 : Reach 99647 := rs (se 1 (by rfl) ⟨74735, by rfl⟩) R149471
theorem R378215 : Reach 378215 := rs (se 1 (by rfl) ⟨283661, by rfl⟩) R567323
theorem R99687 : Reach 99687 := rs (se 1 (by rfl) ⟨74765, by rfl⟩) R149531
theorem R167339 : Reach 167339 := rs (se 1 (by rfl) ⟨125504, by rfl⟩) R251009
theorem R1134323 : Reach 1134323 := rs (se 1 (by rfl) ⟨850742, by rfl⟩) R1701485
theorem R167791 : Reach 167791 := rs (se 1 (by rfl) ⟨125843, by rfl⟩) R251687
theorem R167879 : Reach 167879 := rs (se 1 (by rfl) ⟨125909, by rfl⟩) R251819
theorem R212959 : Reach 212959 := rs (se 1 (by rfl) ⟨159719, by rfl⟩) R319439
theorem R15759521 : Reach 15759521 := rs (se 2 (by rfl) ⟨5909820, by rfl⟩) R11819641
theorem R252143 : Reach 252143 := rs (se 1 (by rfl) ⟨189107, by rfl⟩) R378215
theorem R11604343 : Reach 11604343 := rs (se 1 (by rfl) ⟨8703257, by rfl⟩) R17406515
theorem R223721 : Reach 223721 := rs (se 2 (by rfl) ⟨83895, by rfl⟩) R167791
theorem R756215 : Reach 756215 := rs (se 1 (by rfl) ⟨567161, by rfl⟩) R1134323
theorem R224027 : Reach 224027 := rs (se 1 (by rfl) ⟨168020, by rfl⟩) R336041
theorem R953167 : Reach 953167 := rs (se 1 (by rfl) ⟨714875, by rfl⟩) R1429751
theorem R238427 : Reach 238427 := rs (se 1 (by rfl) ⟨178820, by rfl⟩) R357641
theorem R111559 : Reach 111559 := rs (se 1 (by rfl) ⟨83669, by rfl⟩) R167339
theorem R224225 : Reach 224225 := rs (se 2 (by rfl) ⟨84084, by rfl⟩) R168169
theorem R502847 : Reach 502847 := rs (se 1 (by rfl) ⟨377135, by rfl⟩) R754271
theorem R378017 : Reach 378017 := rs (se 2 (by rfl) ⟨141756, by rfl⟩) R283513
theorem R1135781 : Reach 1135781 := rs (se 4 (by rfl) ⟨106479, by rfl⟩) R212959
theorem R111919 : Reach 111919 := rs (se 1 (by rfl) ⟨83939, by rfl⟩) R167879
theorem R1019263 : Reach 1019263 := rs (se 1 (by rfl) ⟨764447, by rfl⟩) R1528895
theorem R1207817 : Reach 1207817 := rs (se 2 (by rfl) ⟨452931, by rfl⟩) R905863
theorem R251495 : Reach 251495 := rs (se 1 (by rfl) ⟨188621, by rfl⟩) R377243
theorem R636623 : Reach 636623 := rs (se 1 (by rfl) ⟨477467, by rfl⟩) R954935
theorem R149231 : Reach 149231 := rs (se 1 (by rfl) ⟨111923, by rfl⟩) R223847
theorem R251657 : Reach 251657 := rs (se 2 (by rfl) ⟨94371, by rfl⟩) R188743
theorem R757673 : Reach 757673 := rs (se 2 (by rfl) ⟨284127, by rfl⟩) R568255
theorem R252011 : Reach 252011 := rs (se 1 (by rfl) ⟨189008, by rfl⟩) R378017
theorem R168095 : Reach 168095 := rs (se 1 (by rfl) ⟨126071, by rfl⟩) R252143
theorem R504143 : Reach 504143 := rs (se 1 (by rfl) ⟨378107, by rfl⟩) R756215
theorem R805211 : Reach 805211 := rs (se 1 (by rfl) ⟨603908, by rfl⟩) R1207817
theorem R424415 : Reach 424415 := rs (se 1 (by rfl) ⟨318311, by rfl⟩) R636623
theorem R1270889 : Reach 1270889 := rs (se 2 (by rfl) ⟨476583, by rfl⟩) R953167
theorem R10506347 : Reach 10506347 := rs (se 1 (by rfl) ⟨7879760, by rfl⟩) R15759521
theorem R99487 : Reach 99487 := rs (se 1 (by rfl) ⟨74615, by rfl⟩) R149231
theorem R1359017 : Reach 1359017 := rs (se 2 (by rfl) ⟨509631, by rfl⟩) R1019263
theorem R158951 : Reach 158951 := rs (se 1 (by rfl) ⟨119213, by rfl⟩) R238427
theorem R148745 : Reach 148745 := rs (se 2 (by rfl) ⟨55779, by rfl⟩) R111559
theorem R335231 : Reach 335231 := rs (se 1 (by rfl) ⟨251423, by rfl⟩) R502847
theorem R757187 : Reach 757187 := rs (se 1 (by rfl) ⟨567890, by rfl⟩) R1135781
theorem R149147 : Reach 149147 := rs (se 1 (by rfl) ⟨111860, by rfl⟩) R223721
theorem R149225 : Reach 149225 := rs (se 2 (by rfl) ⟨55959, by rfl⟩) R111919
theorem R167663 : Reach 167663 := rs (se 1 (by rfl) ⟨125747, by rfl⟩) R251495
theorem R505115 : Reach 505115 := rs (se 1 (by rfl) ⟨378836, by rfl⟩) R757673
theorem R15472457 : Reach 15472457 := rs (se 2 (by rfl) ⟨5802171, by rfl⟩) R11604343
theorem R167771 : Reach 167771 := rs (se 1 (by rfl) ⟨125828, by rfl⟩) R251657
theorem R149351 : Reach 149351 := rs (se 1 (by rfl) ⟨112013, by rfl⟩) R224027
theorem R149483 : Reach 149483 := rs (se 1 (by rfl) ⟨112112, by rfl⟩) R224225
theorem R168007 : Reach 168007 := rs (se 1 (by rfl) ⟨126005, by rfl⟩) R252011
theorem R7004231 : Reach 7004231 := rs (se 1 (by rfl) ⟨5253173, by rfl⟩) R10506347
theorem R336095 : Reach 336095 := rs (se 1 (by rfl) ⟨252071, by rfl⟩) R504143
theorem R536807 : Reach 536807 := rs (se 1 (by rfl) ⟨402605, by rfl⟩) R805211
theorem R223487 : Reach 223487 := rs (se 1 (by rfl) ⟨167615, by rfl⟩) R335231
theorem R282943 : Reach 282943 := rs (se 1 (by rfl) ⟨212207, by rfl⟩) R424415
theorem R906011 : Reach 906011 := rs (se 1 (by rfl) ⟨679508, by rfl⟩) R1359017
theorem R99163 : Reach 99163 := rs (se 1 (by rfl) ⟨74372, by rfl⟩) R148745
theorem R336743 : Reach 336743 := rs (se 1 (by rfl) ⟨252557, by rfl⟩) R505115
theorem R504791 : Reach 504791 := rs (se 1 (by rfl) ⟨378593, by rfl⟩) R757187
theorem R99431 : Reach 99431 := rs (se 1 (by rfl) ⟨74573, by rfl⟩) R149147
theorem R99483 : Reach 99483 := rs (se 1 (by rfl) ⟨74612, by rfl⟩) R149225
theorem R111775 : Reach 111775 := rs (se 1 (by rfl) ⟨83831, by rfl⟩) R167663
theorem R10314971 : Reach 10314971 := rs (se 1 (by rfl) ⟨7736228, by rfl⟩) R15472457
theorem R111847 : Reach 111847 := rs (se 1 (by rfl) ⟨83885, by rfl⟩) R167771
theorem R99567 : Reach 99567 := rs (se 1 (by rfl) ⟨74675, by rfl⟩) R149351
theorem R99655 : Reach 99655 := rs (se 1 (by rfl) ⟨74741, by rfl⟩) R149483
theorem R847259 : Reach 847259 := rs (se 1 (by rfl) ⟨635444, by rfl⟩) R1270889
theorem R112063 : Reach 112063 := rs (se 1 (by rfl) ⟨84047, by rfl⟩) R168095
theorem R105967 : Reach 105967 := rs (se 1 (by rfl) ⟨79475, by rfl⟩) R158951
theorem R4669487 : Reach 4669487 := rs (se 1 (by rfl) ⟨3502115, by rfl⟩) R7004231
theorem R377257 : Reach 377257 := rs (se 2 (by rfl) ⟨141471, by rfl⟩) R282943
theorem R336527 : Reach 336527 := rs (se 1 (by rfl) ⟨252395, by rfl⟩) R504791
theorem R224009 : Reach 224009 := rs (se 2 (by rfl) ⟨84003, by rfl⟩) R168007
theorem R224063 : Reach 224063 := rs (se 1 (by rfl) ⟨168047, by rfl⟩) R336095
theorem R224495 : Reach 224495 := rs (se 1 (by rfl) ⟨168371, by rfl⟩) R336743
theorem R6876647 : Reach 6876647 := rs (se 1 (by rfl) ⟨5157485, by rfl⟩) R10314971
theorem R357871 : Reach 357871 := rs (se 1 (by rfl) ⟨268403, by rfl⟩) R536807
theorem R148991 : Reach 148991 := rs (se 1 (by rfl) ⟨111743, by rfl⟩) R223487
theorem R149033 : Reach 149033 := rs (se 2 (by rfl) ⟨55887, by rfl⟩) R111775
theorem R564839 : Reach 564839 := rs (se 1 (by rfl) ⟨423629, by rfl⟩) R847259
theorem R149129 : Reach 149129 := rs (se 2 (by rfl) ⟨55923, by rfl⟩) R111847
theorem R604007 : Reach 604007 := rs (se 1 (by rfl) ⟨453005, by rfl⟩) R906011
theorem R565157 : Reach 565157 := rs (se 4 (by rfl) ⟨52983, by rfl⟩) R105967
theorem R149417 : Reach 149417 := rs (se 2 (by rfl) ⟨56031, by rfl⟩) R112063
theorem R3112991 : Reach 3112991 := rs (se 1 (by rfl) ⟨2334743, by rfl⟩) R4669487
theorem R149663 : Reach 149663 := rs (se 1 (by rfl) ⟨112247, by rfl⟩) R224495
theorem R4584431 : Reach 4584431 := rs (se 1 (by rfl) ⟨3438323, by rfl⟩) R6876647
theorem R99327 : Reach 99327 := rs (se 1 (by rfl) ⟨74495, by rfl⟩) R148991
theorem R99355 : Reach 99355 := rs (se 1 (by rfl) ⟨74516, by rfl⟩) R149033
theorem R99419 : Reach 99419 := rs (se 1 (by rfl) ⟨74564, by rfl⟩) R149129
theorem R224351 : Reach 224351 := rs (se 1 (by rfl) ⟨168263, by rfl⟩) R336527
theorem R503009 : Reach 503009 := rs (se 2 (by rfl) ⟨188628, by rfl⟩) R377257
theorem R402671 : Reach 402671 := rs (se 1 (by rfl) ⟨302003, by rfl⟩) R604007
theorem R99611 : Reach 99611 := rs (se 1 (by rfl) ⟨74708, by rfl⟩) R149417
theorem R376559 : Reach 376559 := rs (se 1 (by rfl) ⟨282419, by rfl⟩) R564839
theorem R149339 : Reach 149339 := rs (se 1 (by rfl) ⟨112004, by rfl⟩) R224009
theorem R149375 : Reach 149375 := rs (se 1 (by rfl) ⟨112031, by rfl⟩) R224063
theorem R376771 : Reach 376771 := rs (se 1 (by rfl) ⟨282578, by rfl⟩) R565157
theorem R477161 : Reach 477161 := rs (se 2 (by rfl) ⟨178935, by rfl⟩) R357871
theorem R149567 : Reach 149567 := rs (se 1 (by rfl) ⟨112175, by rfl⟩) R224351
theorem R268447 : Reach 268447 := rs (se 1 (by rfl) ⟨201335, by rfl⟩) R402671
theorem R502361 : Reach 502361 := rs (se 2 (by rfl) ⟨188385, by rfl⟩) R376771
theorem R318107 : Reach 318107 := rs (se 1 (by rfl) ⟨238580, by rfl⟩) R477161
theorem R3056287 : Reach 3056287 := rs (se 1 (by rfl) ⟨2292215, by rfl⟩) R4584431
theorem R2075327 : Reach 2075327 := rs (se 1 (by rfl) ⟨1556495, by rfl⟩) R3112991
theorem R251039 : Reach 251039 := rs (se 1 (by rfl) ⟨188279, by rfl⟩) R376559
theorem R99559 : Reach 99559 := rs (se 1 (by rfl) ⟨74669, by rfl⟩) R149339
theorem R99583 : Reach 99583 := rs (se 1 (by rfl) ⟨74687, by rfl⟩) R149375
theorem R99775 : Reach 99775 := rs (se 1 (by rfl) ⟨74831, by rfl⟩) R149663
theorem R335339 : Reach 335339 := rs (se 1 (by rfl) ⟨251504, by rfl⟩) R503009
theorem R223559 : Reach 223559 := rs (se 1 (by rfl) ⟨167669, by rfl⟩) R335339
theorem R334907 : Reach 334907 := rs (se 1 (by rfl) ⟨251180, by rfl⟩) R502361
theorem R212071 : Reach 212071 := rs (se 1 (by rfl) ⟨159053, by rfl⟩) R318107
theorem R1383551 : Reach 1383551 := rs (se 1 (by rfl) ⟨1037663, by rfl⟩) R2075327
theorem R99711 : Reach 99711 := rs (se 1 (by rfl) ⟨74783, by rfl⟩) R149567
theorem R167359 : Reach 167359 := rs (se 1 (by rfl) ⟨125519, by rfl⟩) R251039
theorem R4075049 : Reach 4075049 := rs (se 2 (by rfl) ⟨1528143, by rfl⟩) R3056287
theorem R357929 : Reach 357929 := rs (se 2 (by rfl) ⟨134223, by rfl⟩) R268447
theorem R223271 : Reach 223271 := rs (se 1 (by rfl) ⟨167453, by rfl⟩) R334907
theorem R282761 : Reach 282761 := rs (se 2 (by rfl) ⟨106035, by rfl⟩) R212071
theorem R922367 : Reach 922367 := rs (se 1 (by rfl) ⟨691775, by rfl⟩) R1383551
theorem R2716699 : Reach 2716699 := rs (se 1 (by rfl) ⟨2037524, by rfl⟩) R4075049
theorem R238619 : Reach 238619 := rs (se 1 (by rfl) ⟨178964, by rfl⟩) R357929
theorem R149039 : Reach 149039 := rs (se 1 (by rfl) ⟨111779, by rfl⟩) R223559
theorem R223145 : Reach 223145 := rs (se 2 (by rfl) ⟨83679, by rfl⟩) R167359
theorem R188507 : Reach 188507 := rs (se 1 (by rfl) ⟨141380, by rfl⟩) R282761
theorem R99359 : Reach 99359 := rs (se 1 (by rfl) ⟨74519, by rfl⟩) R149039
theorem R2459645 : Reach 2459645 := rs (se 3 (by rfl) ⟨461183, by rfl⟩) R922367
theorem R148763 : Reach 148763 := rs (se 1 (by rfl) ⟨111572, by rfl⟩) R223145
theorem R159079 : Reach 159079 := rs (se 1 (by rfl) ⟨119309, by rfl⟩) R238619
theorem R148847 : Reach 148847 := rs (se 1 (by rfl) ⟨111635, by rfl⟩) R223271
theorem R3622265 : Reach 3622265 := rs (se 2 (by rfl) ⟨1358349, by rfl⟩) R2716699
theorem R2414843 : Reach 2414843 := rs (se 1 (by rfl) ⟨1811132, by rfl⟩) R3622265
theorem R1639763 : Reach 1639763 := rs (se 1 (by rfl) ⟨1229822, by rfl⟩) R2459645
theorem R99175 : Reach 99175 := rs (se 1 (by rfl) ⟨74381, by rfl⟩) R148763
theorem R502685 : Reach 502685 := rs (se 3 (by rfl) ⟨94253, by rfl⟩) R188507
theorem R99231 : Reach 99231 := rs (se 1 (by rfl) ⟨74423, by rfl⟩) R148847
theorem R212105 : Reach 212105 := rs (se 2 (by rfl) ⟨79539, by rfl⟩) R159079
theorem R1609895 : Reach 1609895 := rs (se 1 (by rfl) ⟨1207421, by rfl⟩) R2414843
theorem R565613 : Reach 565613 := rs (se 3 (by rfl) ⟨106052, by rfl⟩) R212105
theorem R335123 : Reach 335123 := rs (se 1 (by rfl) ⟨251342, by rfl⟩) R502685
theorem R1093175 : Reach 1093175 := rs (se 1 (by rfl) ⟨819881, by rfl⟩) R1639763
theorem R1073263 : Reach 1073263 := rs (se 1 (by rfl) ⟨804947, by rfl⟩) R1609895
theorem R223415 : Reach 223415 := rs (se 1 (by rfl) ⟨167561, by rfl⟩) R335123
theorem R377075 : Reach 377075 := rs (se 1 (by rfl) ⟨282806, by rfl⟩) R565613
theorem R728783 : Reach 728783 := rs (se 1 (by rfl) ⟨546587, by rfl⟩) R1093175
theorem R485855 : Reach 485855 := rs (se 1 (by rfl) ⟨364391, by rfl⟩) R728783
theorem R148943 : Reach 148943 := rs (se 1 (by rfl) ⟨111707, by rfl⟩) R223415
theorem R1431017 : Reach 1431017 := rs (se 2 (by rfl) ⟨536631, by rfl⟩) R1073263
theorem R251383 : Reach 251383 := rs (se 1 (by rfl) ⟨188537, by rfl⟩) R377075
theorem R323903 : Reach 323903 := rs (se 1 (by rfl) ⟨242927, by rfl⟩) R485855
theorem R99295 : Reach 99295 := rs (se 1 (by rfl) ⟨74471, by rfl⟩) R148943
theorem R335177 : Reach 335177 := rs (se 2 (by rfl) ⟨125691, by rfl⟩) R251383
theorem R954011 : Reach 954011 := rs (se 1 (by rfl) ⟨715508, by rfl⟩) R1431017
theorem R223451 : Reach 223451 := rs (se 1 (by rfl) ⟨167588, by rfl⟩) R335177
theorem R215935 : Reach 215935 := rs (se 1 (by rfl) ⟨161951, by rfl⟩) R323903
theorem R636007 : Reach 636007 := rs (se 1 (by rfl) ⟨477005, by rfl⟩) R954011
theorem R848009 : Reach 848009 := rs (se 2 (by rfl) ⟨318003, by rfl⟩) R636007
theorem R1151653 : Reach 1151653 := rs (se 4 (by rfl) ⟨107967, by rfl⟩) R215935
theorem R148967 : Reach 148967 := rs (se 1 (by rfl) ⟨111725, by rfl⟩) R223451
theorem R565339 : Reach 565339 := rs (se 1 (by rfl) ⟨424004, by rfl⟩) R848009
theorem R99311 : Reach 99311 := rs (se 1 (by rfl) ⟨74483, by rfl⟩) R148967
theorem R1535537 : Reach 1535537 := rs (se 2 (by rfl) ⟨575826, by rfl⟩) R1151653
theorem R753785 : Reach 753785 := rs (se 2 (by rfl) ⟨282669, by rfl⟩) R565339
theorem R1023691 : Reach 1023691 := rs (se 1 (by rfl) ⟨767768, by rfl⟩) R1535537
theorem R502523 : Reach 502523 := rs (se 1 (by rfl) ⟨376892, by rfl⟩) R753785
theorem R1364921 : Reach 1364921 := rs (se 2 (by rfl) ⟨511845, by rfl⟩) R1023691
theorem R909947 : Reach 909947 := rs (se 1 (by rfl) ⟨682460, by rfl⟩) R1364921
theorem R335015 : Reach 335015 := rs (se 1 (by rfl) ⟨251261, by rfl⟩) R502523
theorem R223343 : Reach 223343 := rs (se 1 (by rfl) ⟨167507, by rfl⟩) R335015
theorem R606631 : Reach 606631 := rs (se 1 (by rfl) ⟨454973, by rfl⟩) R909947
theorem R148895 : Reach 148895 := rs (se 1 (by rfl) ⟨111671, by rfl⟩) R223343
theorem R808841 : Reach 808841 := rs (se 2 (by rfl) ⟨303315, by rfl⟩) R606631
theorem R539227 : Reach 539227 := rs (se 1 (by rfl) ⟨404420, by rfl⟩) R808841
theorem R99263 : Reach 99263 := rs (se 1 (by rfl) ⟨74447, by rfl⟩) R148895
theorem R718969 : Reach 718969 := rs (se 2 (by rfl) ⟨269613, by rfl⟩) R539227
theorem R958625 : Reach 958625 := rs (se 2 (by rfl) ⟨359484, by rfl⟩) R718969
theorem R639083 : Reach 639083 := rs (se 1 (by rfl) ⟨479312, by rfl⟩) R958625
theorem R426055 : Reach 426055 := rs (se 1 (by rfl) ⟨319541, by rfl⟩) R639083
theorem R568073 : Reach 568073 := rs (se 2 (by rfl) ⟨213027, by rfl⟩) R426055
theorem R378715 : Reach 378715 := rs (se 1 (by rfl) ⟨284036, by rfl⟩) R568073
theorem R504953 : Reach 504953 := rs (se 2 (by rfl) ⟨189357, by rfl⟩) R378715
theorem R336635 : Reach 336635 := rs (se 1 (by rfl) ⟨252476, by rfl⟩) R504953
theorem R224423 : Reach 224423 := rs (se 1 (by rfl) ⟨168317, by rfl⟩) R336635
theorem R149615 : Reach 149615 := rs (se 1 (by rfl) ⟨112211, by rfl⟩) R224423
theorem R99743 : Reach 99743 := rs (se 1 (by rfl) ⟨74807, by rfl⟩) R149615

theorem C0 (j : ℕ) (h1 : 49566 ≤ j) (h2 : j ≤ 49889) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R99133
  · exact R99135
  · exact R99137
  · exact R99139
  · exact R99141
  · exact R99143
  · exact R99145
  · exact R99147
  · exact R99149
  · exact R99151
  · exact R99153
  · exact R99155
  · exact R99157
  · exact R99159
  · exact R99161
  · exact R99163
  · exact R99165
  · exact R99167
  · exact R99169
  · exact R99171
  · exact R99173
  · exact R99175
  · exact R99177
  · exact R99179
  · exact R99181
  · exact R99183
  · exact R99185
  · exact R99187
  · exact R99189
  · exact R99191
  · exact R99193
  · exact R99195
  · exact R99197
  · exact R99199
  · exact R99201
  · exact R99203
  · exact R99205
  · exact R99207
  · exact R99209
  · exact R99211
  · exact R99213
  · exact R99215
  · exact R99217
  · exact R99219
  · exact R99221
  · exact R99223
  · exact R99225
  · exact R99227
  · exact R99229
  · exact R99231
  · exact R99233
  · exact R99235
  · exact R99237
  · exact R99239
  · exact R99241
  · exact R99243
  · exact R99245
  · exact R99247
  · exact R99249
  · exact R99251
  · exact R99253
  · exact R99255
  · exact R99257
  · exact R99259
  · exact R99261
  · exact R99263
  · exact R99265
  · exact R99267
  · exact R99269
  · exact R99271
  · exact R99273
  · exact R99275
  · exact R99277
  · exact R99279
  · exact R99281
  · exact R99283
  · exact R99285
  · exact R99287
  · exact R99289
  · exact R99291
  · exact R99293
  · exact R99295
  · exact R99297
  · exact R99299
  · exact R99301
  · exact R99303
  · exact R99305
  · exact R99307
  · exact R99309
  · exact R99311
  · exact R99313
  · exact R99315
  · exact R99317
  · exact R99319
  · exact R99321
  · exact R99323
  · exact R99325
  · exact R99327
  · exact R99329
  · exact R99331
  · exact R99333
  · exact R99335
  · exact R99337
  · exact R99339
  · exact R99341
  · exact R99343
  · exact R99345
  · exact R99347
  · exact R99349
  · exact R99351
  · exact R99353
  · exact R99355
  · exact R99357
  · exact R99359
  · exact R99361
  · exact R99363
  · exact R99365
  · exact R99367
  · exact R99369
  · exact R99371
  · exact R99373
  · exact R99375
  · exact R99377
  · exact R99379
  · exact R99381
  · exact R99383
  · exact R99385
  · exact R99387
  · exact R99389
  · exact R99391
  · exact R99393
  · exact R99395
  · exact R99397
  · exact R99399
  · exact R99401
  · exact R99403
  · exact R99405
  · exact R99407
  · exact R99409
  · exact R99411
  · exact R99413
  · exact R99415
  · exact R99417
  · exact R99419
  · exact R99421
  · exact R99423
  · exact R99425
  · exact R99427
  · exact R99429
  · exact R99431
  · exact R99433
  · exact R99435
  · exact R99437
  · exact R99439
  · exact R99441
  · exact R99443
  · exact R99445
  · exact R99447
  · exact R99449
  · exact R99451
  · exact R99453
  · exact R99455
  · exact R99457
  · exact R99459
  · exact R99461
  · exact R99463
  · exact R99465
  · exact R99467
  · exact R99469
  · exact R99471
  · exact R99473
  · exact R99475
  · exact R99477
  · exact R99479
  · exact R99481
  · exact R99483
  · exact R99485
  · exact R99487
  · exact R99489
  · exact R99491
  · exact R99493
  · exact R99495
  · exact R99497
  · exact R99499
  · exact R99501
  · exact R99503
  · exact R99505
  · exact R99507
  · exact R99509
  · exact R99511
  · exact R99513
  · exact R99515
  · exact R99517
  · exact R99519
  · exact R99521
  · exact R99523
  · exact R99525
  · exact R99527
  · exact R99529
  · exact R99531
  · exact R99533
  · exact R99535
  · exact R99537
  · exact R99539
  · exact R99541
  · exact R99543
  · exact R99545
  · exact R99547
  · exact R99549
  · exact R99551
  · exact R99553
  · exact R99555
  · exact R99557
  · exact R99559
  · exact R99561
  · exact R99563
  · exact R99565
  · exact R99567
  · exact R99569
  · exact R99571
  · exact R99573
  · exact R99575
  · exact R99577
  · exact R99579
  · exact R99581
  · exact R99583
  · exact R99585
  · exact R99587
  · exact R99589
  · exact R99591
  · exact R99593
  · exact R99595
  · exact R99597
  · exact R99599
  · exact R99601
  · exact R99603
  · exact R99605
  · exact R99607
  · exact R99609
  · exact R99611
  · exact R99613
  · exact R99615
  · exact R99617
  · exact R99619
  · exact R99621
  · exact R99623
  · exact R99625
  · exact R99627
  · exact R99629
  · exact R99631
  · exact R99633
  · exact R99635
  · exact R99637
  · exact R99639
  · exact R99641
  · exact R99643
  · exact R99645
  · exact R99647
  · exact R99649
  · exact R99651
  · exact R99653
  · exact R99655
  · exact R99657
  · exact R99659
  · exact R99661
  · exact R99663
  · exact R99665
  · exact R99667
  · exact R99669
  · exact R99671
  · exact R99673
  · exact R99675
  · exact R99677
  · exact R99679
  · exact R99681
  · exact R99683
  · exact R99685
  · exact R99687
  · exact R99689
  · exact R99691
  · exact R99693
  · exact R99695
  · exact R99697
  · exact R99699
  · exact R99701
  · exact R99703
  · exact R99705
  · exact R99707
  · exact R99709
  · exact R99711
  · exact R99713
  · exact R99715
  · exact R99717
  · exact R99719
  · exact R99721
  · exact R99723
  · exact R99725
  · exact R99727
  · exact R99729
  · exact R99731
  · exact R99733
  · exact R99735
  · exact R99737
  · exact R99739
  · exact R99741
  · exact R99743
  · exact R99745
  · exact R99747
  · exact R99749
  · exact R99751
  · exact R99753
  · exact R99755
  · exact R99757
  · exact R99759
  · exact R99761
  · exact R99763
  · exact R99765
  · exact R99767
  · exact R99769
  · exact R99771
  · exact R99773
  · exact R99775
  · exact R99777
  · exact R99779

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 99780) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 99132 with hlo | hlo
  · exact syracuse_reaches_one_below_99132 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  exact C0 j (by omega) (by omega)
