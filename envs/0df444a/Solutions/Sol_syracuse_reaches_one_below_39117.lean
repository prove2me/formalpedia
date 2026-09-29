-- Prove2me | solution 1 for syracuse_reaches_one_below_39117
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T05:34:23.815629+00:00
-- url     : https://prove2.me/submissions/f1017fe2-8529-42c0-bfaf-41952f328d53

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_35116

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 35115) : Reach n :=
  syracuse_reaches_one_below_35116 n h1 h2 h3
theorem R65549 : Reach 65549 := rs (se 3 (by rfl) ⟨12290, by rfl⟩) (B 24581 (by norm_num) ⟨12290, by rfl⟩ (by norm_num))
theorem R65605 : Reach 65605 := rs (se 4 (by rfl) ⟨6150, by rfl⟩) (B 12301 (by norm_num) ⟨6150, by rfl⟩ (by norm_num))
theorem R98405 : Reach 98405 := rs (se 4 (by rfl) ⟨9225, by rfl⟩) (B 18451 (by norm_num) ⟨9225, by rfl⟩ (by norm_num))
theorem R163957 : Reach 163957 := rs (se 5 (by rfl) ⟨7685, by rfl⟩) (B 15371 (by norm_num) ⟨7685, by rfl⟩ (by norm_num))
theorem R65677 : Reach 65677 := rs (se 3 (by rfl) ⟨12314, by rfl⟩) (B 24629 (by norm_num) ⟨12314, by rfl⟩ (by norm_num))
theorem R65765 : Reach 65765 := rs (se 4 (by rfl) ⟨6165, by rfl⟩) (B 12331 (by norm_num) ⟨6165, by rfl⟩ (by norm_num))
theorem R98597 : Reach 98597 := rs (se 4 (by rfl) ⟨9243, by rfl⟩) (B 18487 (by norm_num) ⟨9243, by rfl⟩ (by norm_num))
theorem R327989 : Reach 327989 := rs (se 5 (by rfl) ⟨15374, by rfl⟩) (B 30749 (by norm_num) ⟨15374, by rfl⟩ (by norm_num))
theorem R131381 : Reach 131381 := rs (se 5 (by rfl) ⟨6158, by rfl⟩) (B 12317 (by norm_num) ⟨6158, by rfl⟩ (by norm_num))
theorem R65893 : Reach 65893 := rs (se 4 (by rfl) ⟨6177, by rfl⟩) (B 12355 (by norm_num) ⟨6177, by rfl⟩ (by norm_num))
theorem R65981 : Reach 65981 := rs (se 3 (by rfl) ⟨12371, by rfl⟩) (B 24743 (by norm_num) ⟨12371, by rfl⟩ (by norm_num))
theorem R164501 : Reach 164501 := rs (se 6 (by rfl) ⟨3855, by rfl⟩) (B 7711 (by norm_num) ⟨3855, by rfl⟩ (by norm_num))
theorem R131813 : Reach 131813 := rs (se 4 (by rfl) ⟨12357, by rfl⟩) (B 24715 (by norm_num) ⟨12357, by rfl⟩ (by norm_num))
theorem R164693 : Reach 164693 := rs (se 9 (by rfl) ⟨482, by rfl⟩) (B 965 (by norm_num) ⟨482, by rfl⟩ (by norm_num))
theorem R984149 : Reach 984149 := rs (se 8 (by rfl) ⟨5766, by rfl⟩) (B 11533 (by norm_num) ⟨5766, by rfl⟩ (by norm_num))
theorem R66757 : Reach 66757 := rs (se 4 (by rfl) ⟨6258, by rfl⟩) (B 12517 (by norm_num) ⟨6258, by rfl⟩ (by norm_num))
theorem R165125 : Reach 165125 := rs (se 4 (by rfl) ⟨15480, by rfl⟩) (B 30961 (by norm_num) ⟨15480, by rfl⟩ (by norm_num))
theorem R66901 : Reach 66901 := rs (se 12 (by rfl) ⟨24, by rfl⟩) (B 49 (by norm_num) ⟨24, by rfl⟩ (by norm_num))
theorem R99733 : Reach 99733 := rs (se 6 (by rfl) ⟨2337, by rfl⟩) (B 4675 (by norm_num) ⟨2337, by rfl⟩ (by norm_num))
theorem R67061 : Reach 67061 := rs (se 5 (by rfl) ⟨3143, by rfl⟩) (B 6287 (by norm_num) ⟨3143, by rfl⟩ (by norm_num))
theorem R67205 : Reach 67205 := rs (se 4 (by rfl) ⟨6300, by rfl⟩) (B 12601 (by norm_num) ⟨6300, by rfl⟩ (by norm_num))
theorem R67405 : Reach 67405 := rs (se 3 (by rfl) ⟨12638, by rfl⟩) (B 25277 (by norm_num) ⟨12638, by rfl⟩ (by norm_num))
theorem R67493 : Reach 67493 := rs (se 4 (by rfl) ⟨6327, by rfl⟩) (B 12655 (by norm_num) ⟨6327, by rfl⟩ (by norm_num))
theorem R67645 : Reach 67645 := rs (se 3 (by rfl) ⟨12683, by rfl⟩) (B 25367 (by norm_num) ⟨12683, by rfl⟩ (by norm_num))
theorem R165989 : Reach 165989 := rs (se 4 (by rfl) ⟨15561, by rfl⟩) (B 31123 (by norm_num) ⟨15561, by rfl⟩ (by norm_num))
theorem R362677 : Reach 362677 := rs (se 5 (by rfl) ⟨17000, by rfl⟩) (B 34001 (by norm_num) ⟨17000, by rfl⟩ (by norm_num))
theorem R35117 : Reach 35117 := rs (se 3 (by rfl) ⟨6584, by rfl⟩) (B 13169 (by norm_num) ⟨6584, by rfl⟩ (by norm_num))
theorem R35121 : Reach 35121 := rs (se 2 (by rfl) ⟨13170, by rfl⟩) (B 26341 (by norm_num) ⟨13170, by rfl⟩ (by norm_num))
theorem R35125 : Reach 35125 := rs (se 5 (by rfl) ⟨1646, by rfl⟩) (B 3293 (by norm_num) ⟨1646, by rfl⟩ (by norm_num))
theorem R35129 : Reach 35129 := rs (se 2 (by rfl) ⟨13173, by rfl⟩) (B 26347 (by norm_num) ⟨13173, by rfl⟩ (by norm_num))
theorem R35133 : Reach 35133 := rs (se 3 (by rfl) ⟨6587, by rfl⟩) (B 13175 (by norm_num) ⟨6587, by rfl⟩ (by norm_num))
theorem R35137 : Reach 35137 := rs (se 2 (by rfl) ⟨13176, by rfl⟩) (B 26353 (by norm_num) ⟨13176, by rfl⟩ (by norm_num))
theorem R35141 : Reach 35141 := rs (se 4 (by rfl) ⟨3294, by rfl⟩) (B 6589 (by norm_num) ⟨3294, by rfl⟩ (by norm_num))
theorem R35145 : Reach 35145 := rs (se 2 (by rfl) ⟨13179, by rfl⟩) (B 26359 (by norm_num) ⟨13179, by rfl⟩ (by norm_num))
theorem R35149 : Reach 35149 := rs (se 3 (by rfl) ⟨6590, by rfl⟩) (B 13181 (by norm_num) ⟨6590, by rfl⟩ (by norm_num))
theorem R35153 : Reach 35153 := rs (se 2 (by rfl) ⟨13182, by rfl⟩) (B 26365 (by norm_num) ⟨13182, by rfl⟩ (by norm_num))
theorem R35157 : Reach 35157 := rs (se 10 (by rfl) ⟨51, by rfl⟩) (B 103 (by norm_num) ⟨51, by rfl⟩ (by norm_num))
theorem R100693 : Reach 100693 := rs (se 10 (by rfl) ⟨147, by rfl⟩) (B 295 (by norm_num) ⟨147, by rfl⟩ (by norm_num))
theorem R35161 : Reach 35161 := rs (se 2 (by rfl) ⟨13185, by rfl⟩) (B 26371 (by norm_num) ⟨13185, by rfl⟩ (by norm_num))
theorem R35165 : Reach 35165 := rs (se 3 (by rfl) ⟨6593, by rfl⟩) (B 13187 (by norm_num) ⟨6593, by rfl⟩ (by norm_num))
theorem R35169 : Reach 35169 := rs (se 2 (by rfl) ⟨13188, by rfl⟩) (B 26377 (by norm_num) ⟨13188, by rfl⟩ (by norm_num))
theorem R35173 : Reach 35173 := rs (se 4 (by rfl) ⟨3297, by rfl⟩) (B 6595 (by norm_num) ⟨3297, by rfl⟩ (by norm_num))
theorem R35177 : Reach 35177 := rs (se 2 (by rfl) ⟨13191, by rfl⟩) (B 26383 (by norm_num) ⟨13191, by rfl⟩ (by norm_num))
theorem R35181 : Reach 35181 := rs (se 3 (by rfl) ⟨6596, by rfl⟩) (B 13193 (by norm_num) ⟨6596, by rfl⟩ (by norm_num))
theorem R67949 : Reach 67949 := rs (se 3 (by rfl) ⟨12740, by rfl⟩) (B 25481 (by norm_num) ⟨12740, by rfl⟩ (by norm_num))
theorem R35185 : Reach 35185 := rs (se 2 (by rfl) ⟨13194, by rfl⟩) (B 26389 (by norm_num) ⟨13194, by rfl⟩ (by norm_num))
theorem R35189 : Reach 35189 := rs (se 5 (by rfl) ⟨1649, by rfl⟩) (B 3299 (by norm_num) ⟨1649, by rfl⟩ (by norm_num))
theorem R330101 : Reach 330101 := rs (se 5 (by rfl) ⟨15473, by rfl⟩) (B 30947 (by norm_num) ⟨15473, by rfl⟩ (by norm_num))
theorem R35193 : Reach 35193 := rs (se 2 (by rfl) ⟨13197, by rfl⟩) (B 26395 (by norm_num) ⟨13197, by rfl⟩ (by norm_num))
theorem R35197 : Reach 35197 := rs (se 3 (by rfl) ⟨6599, by rfl⟩) (B 13199 (by norm_num) ⟨6599, by rfl⟩ (by norm_num))
theorem R35201 : Reach 35201 := rs (se 2 (by rfl) ⟨13200, by rfl⟩) (B 26401 (by norm_num) ⟨13200, by rfl⟩ (by norm_num))
theorem R35205 : Reach 35205 := rs (se 4 (by rfl) ⟨3300, by rfl⟩) (B 6601 (by norm_num) ⟨3300, by rfl⟩ (by norm_num))
theorem R35209 : Reach 35209 := rs (se 2 (by rfl) ⟨13203, by rfl⟩) (B 26407 (by norm_num) ⟨13203, by rfl⟩ (by norm_num))
theorem R35213 : Reach 35213 := rs (se 3 (by rfl) ⟨6602, by rfl⟩) (B 13205 (by norm_num) ⟨6602, by rfl⟩ (by norm_num))
theorem R35217 : Reach 35217 := rs (se 2 (by rfl) ⟨13206, by rfl⟩) (B 26413 (by norm_num) ⟨13206, by rfl⟩ (by norm_num))
theorem R35221 : Reach 35221 := rs (se 6 (by rfl) ⟨825, by rfl⟩) (B 1651 (by norm_num) ⟨825, by rfl⟩ (by norm_num))
theorem R35225 : Reach 35225 := rs (se 2 (by rfl) ⟨13209, by rfl⟩) (B 26419 (by norm_num) ⟨13209, by rfl⟩ (by norm_num))
theorem R35229 : Reach 35229 := rs (se 3 (by rfl) ⟨6605, by rfl⟩) (B 13211 (by norm_num) ⟨6605, by rfl⟩ (by norm_num))
theorem R35233 : Reach 35233 := rs (se 2 (by rfl) ⟨13212, by rfl⟩) (B 26425 (by norm_num) ⟨13212, by rfl⟩ (by norm_num))
theorem R35237 : Reach 35237 := rs (se 4 (by rfl) ⟨3303, by rfl⟩) (B 6607 (by norm_num) ⟨3303, by rfl⟩ (by norm_num))
theorem R35241 : Reach 35241 := rs (se 2 (by rfl) ⟨13215, by rfl⟩) (B 26431 (by norm_num) ⟨13215, by rfl⟩ (by norm_num))
theorem R35245 : Reach 35245 := rs (se 3 (by rfl) ⟨6608, by rfl⟩) (B 13217 (by norm_num) ⟨6608, by rfl⟩ (by norm_num))
theorem R35249 : Reach 35249 := rs (se 2 (by rfl) ⟨13218, by rfl⟩) (B 26437 (by norm_num) ⟨13218, by rfl⟩ (by norm_num))
theorem R35253 : Reach 35253 := rs (se 5 (by rfl) ⟨1652, by rfl⟩) (B 3305 (by norm_num) ⟨1652, by rfl⟩ (by norm_num))
theorem R35257 : Reach 35257 := rs (se 2 (by rfl) ⟨13221, by rfl⟩) (B 26443 (by norm_num) ⟨13221, by rfl⟩ (by norm_num))
theorem R35261 : Reach 35261 := rs (se 3 (by rfl) ⟨6611, by rfl⟩) (B 13223 (by norm_num) ⟨6611, by rfl⟩ (by norm_num))
theorem R35265 : Reach 35265 := rs (se 2 (by rfl) ⟨13224, by rfl⟩) (B 26449 (by norm_num) ⟨13224, by rfl⟩ (by norm_num))
theorem R35269 : Reach 35269 := rs (se 4 (by rfl) ⟨3306, by rfl⟩) (B 6613 (by norm_num) ⟨3306, by rfl⟩ (by norm_num))
theorem R35273 : Reach 35273 := rs (se 2 (by rfl) ⟨13227, by rfl⟩) (B 26455 (by norm_num) ⟨13227, by rfl⟩ (by norm_num))
theorem R35277 : Reach 35277 := rs (se 3 (by rfl) ⟨6614, by rfl⟩) (B 13229 (by norm_num) ⟨6614, by rfl⟩ (by norm_num))
theorem R68045 : Reach 68045 := rs (se 3 (by rfl) ⟨12758, by rfl⟩) (B 25517 (by norm_num) ⟨12758, by rfl⟩ (by norm_num))
theorem R35281 : Reach 35281 := rs (se 2 (by rfl) ⟨13230, by rfl⟩) (B 26461 (by norm_num) ⟨13230, by rfl⟩ (by norm_num))
theorem R133589 : Reach 133589 := rs (se 7 (by rfl) ⟨1565, by rfl⟩) (B 3131 (by norm_num) ⟨1565, by rfl⟩ (by norm_num))
theorem R35285 : Reach 35285 := rs (se 7 (by rfl) ⟨413, by rfl⟩) (B 827 (by norm_num) ⟨413, by rfl⟩ (by norm_num))
theorem R35289 : Reach 35289 := rs (se 2 (by rfl) ⟨13233, by rfl⟩) (B 26467 (by norm_num) ⟨13233, by rfl⟩ (by norm_num))
theorem R35293 : Reach 35293 := rs (se 3 (by rfl) ⟨6617, by rfl⟩) (B 13235 (by norm_num) ⟨6617, by rfl⟩ (by norm_num))
theorem R35297 : Reach 35297 := rs (se 2 (by rfl) ⟨13236, by rfl⟩) (B 26473 (by norm_num) ⟨13236, by rfl⟩ (by norm_num))
theorem R35301 : Reach 35301 := rs (se 4 (by rfl) ⟨3309, by rfl⟩) (B 6619 (by norm_num) ⟨3309, by rfl⟩ (by norm_num))
theorem R35305 : Reach 35305 := rs (se 2 (by rfl) ⟨13239, by rfl⟩) (B 26479 (by norm_num) ⟨13239, by rfl⟩ (by norm_num))
theorem R35309 : Reach 35309 := rs (se 3 (by rfl) ⟨6620, by rfl⟩) (B 13241 (by norm_num) ⟨6620, by rfl⟩ (by norm_num))
theorem R35313 : Reach 35313 := rs (se 2 (by rfl) ⟨13242, by rfl⟩) (B 26485 (by norm_num) ⟨13242, by rfl⟩ (by norm_num))
theorem R35317 : Reach 35317 := rs (se 5 (by rfl) ⟨1655, by rfl⟩) (B 3311 (by norm_num) ⟨1655, by rfl⟩ (by norm_num))
theorem R35321 : Reach 35321 := rs (se 2 (by rfl) ⟨13245, by rfl⟩) (B 26491 (by norm_num) ⟨13245, by rfl⟩ (by norm_num))
theorem R35325 : Reach 35325 := rs (se 3 (by rfl) ⟨6623, by rfl⟩) (B 13247 (by norm_num) ⟨6623, by rfl⟩ (by norm_num))
theorem R35329 : Reach 35329 := rs (se 2 (by rfl) ⟨13248, by rfl⟩) (B 26497 (by norm_num) ⟨13248, by rfl⟩ (by norm_num))
theorem R35333 : Reach 35333 := rs (se 4 (by rfl) ⟨3312, by rfl⟩) (B 6625 (by norm_num) ⟨3312, by rfl⟩ (by norm_num))
theorem R35337 : Reach 35337 := rs (se 2 (by rfl) ⟨13251, by rfl⟩) (B 26503 (by norm_num) ⟨13251, by rfl⟩ (by norm_num))
theorem R35341 : Reach 35341 := rs (se 3 (by rfl) ⟨6626, by rfl⟩) (B 13253 (by norm_num) ⟨6626, by rfl⟩ (by norm_num))
theorem R35345 : Reach 35345 := rs (se 2 (by rfl) ⟨13254, by rfl⟩) (B 26509 (by norm_num) ⟨13254, by rfl⟩ (by norm_num))
theorem R35349 : Reach 35349 := rs (se 6 (by rfl) ⟨828, by rfl⟩) (B 1657 (by norm_num) ⟨828, by rfl⟩ (by norm_num))
theorem R35353 : Reach 35353 := rs (se 2 (by rfl) ⟨13257, by rfl⟩) (B 26515 (by norm_num) ⟨13257, by rfl⟩ (by norm_num))
theorem R35357 : Reach 35357 := rs (se 3 (by rfl) ⟨6629, by rfl⟩) (B 13259 (by norm_num) ⟨6629, by rfl⟩ (by norm_num))
theorem R35361 : Reach 35361 := rs (se 2 (by rfl) ⟨13260, by rfl⟩) (B 26521 (by norm_num) ⟨13260, by rfl⟩ (by norm_num))
theorem R35365 : Reach 35365 := rs (se 4 (by rfl) ⟨3315, by rfl⟩) (B 6631 (by norm_num) ⟨3315, by rfl⟩ (by norm_num))
theorem R35369 : Reach 35369 := rs (se 2 (by rfl) ⟨13263, by rfl⟩) (B 26527 (by norm_num) ⟨13263, by rfl⟩ (by norm_num))
theorem R35373 : Reach 35373 := rs (se 3 (by rfl) ⟨6632, by rfl⟩) (B 13265 (by norm_num) ⟨6632, by rfl⟩ (by norm_num))
theorem R35377 : Reach 35377 := rs (se 2 (by rfl) ⟨13266, by rfl⟩) (B 26533 (by norm_num) ⟨13266, by rfl⟩ (by norm_num))
theorem R35381 : Reach 35381 := rs (se 5 (by rfl) ⟨1658, by rfl⟩) (B 3317 (by norm_num) ⟨1658, by rfl⟩ (by norm_num))
theorem R35385 : Reach 35385 := rs (se 2 (by rfl) ⟨13269, by rfl⟩) (B 26539 (by norm_num) ⟨13269, by rfl⟩ (by norm_num))
theorem R35389 : Reach 35389 := rs (se 3 (by rfl) ⟨6635, by rfl⟩) (B 13271 (by norm_num) ⟨6635, by rfl⟩ (by norm_num))
theorem R35393 : Reach 35393 := rs (se 2 (by rfl) ⟨13272, by rfl⟩) (B 26545 (by norm_num) ⟨13272, by rfl⟩ (by norm_num))
theorem R35397 : Reach 35397 := rs (se 4 (by rfl) ⟨3318, by rfl⟩) (B 6637 (by norm_num) ⟨3318, by rfl⟩ (by norm_num))
theorem R35401 : Reach 35401 := rs (se 2 (by rfl) ⟨13275, by rfl⟩) (B 26551 (by norm_num) ⟨13275, by rfl⟩ (by norm_num))
theorem R35405 : Reach 35405 := rs (se 3 (by rfl) ⟨6638, by rfl⟩) (B 13277 (by norm_num) ⟨6638, by rfl⟩ (by norm_num))
theorem R35409 : Reach 35409 := rs (se 2 (by rfl) ⟨13278, by rfl⟩) (B 26557 (by norm_num) ⟨13278, by rfl⟩ (by norm_num))
theorem R35413 : Reach 35413 := rs (se 8 (by rfl) ⟨207, by rfl⟩) (B 415 (by norm_num) ⟨207, by rfl⟩ (by norm_num))
theorem R35417 : Reach 35417 := rs (se 2 (by rfl) ⟨13281, by rfl⟩) (B 26563 (by norm_num) ⟨13281, by rfl⟩ (by norm_num))
theorem R35421 : Reach 35421 := rs (se 3 (by rfl) ⟨6641, by rfl⟩) (B 13283 (by norm_num) ⟨6641, by rfl⟩ (by norm_num))
theorem R35425 : Reach 35425 := rs (se 2 (by rfl) ⟨13284, by rfl⟩) (B 26569 (by norm_num) ⟨13284, by rfl⟩ (by norm_num))
theorem R35429 : Reach 35429 := rs (se 4 (by rfl) ⟨3321, by rfl⟩) (B 6643 (by norm_num) ⟨3321, by rfl⟩ (by norm_num))
theorem R35433 : Reach 35433 := rs (se 2 (by rfl) ⟨13287, by rfl⟩) (B 26575 (by norm_num) ⟨13287, by rfl⟩ (by norm_num))
theorem R35437 : Reach 35437 := rs (se 3 (by rfl) ⟨6644, by rfl⟩) (B 13289 (by norm_num) ⟨6644, by rfl⟩ (by norm_num))
theorem R35441 : Reach 35441 := rs (se 2 (by rfl) ⟨13290, by rfl⟩) (B 26581 (by norm_num) ⟨13290, by rfl⟩ (by norm_num))
theorem R35445 : Reach 35445 := rs (se 5 (by rfl) ⟨1661, by rfl⟩) (B 3323 (by norm_num) ⟨1661, by rfl⟩ (by norm_num))
theorem R35449 : Reach 35449 := rs (se 2 (by rfl) ⟨13293, by rfl⟩) (B 26587 (by norm_num) ⟨13293, by rfl⟩ (by norm_num))
theorem R35453 : Reach 35453 := rs (se 3 (by rfl) ⟨6647, by rfl⟩) (B 13295 (by norm_num) ⟨6647, by rfl⟩ (by norm_num))
theorem R35457 : Reach 35457 := rs (se 2 (by rfl) ⟨13296, by rfl⟩) (B 26593 (by norm_num) ⟨13296, by rfl⟩ (by norm_num))
theorem R35461 : Reach 35461 := rs (se 4 (by rfl) ⟨3324, by rfl⟩) (B 6649 (by norm_num) ⟨3324, by rfl⟩ (by norm_num))
theorem R35465 : Reach 35465 := rs (se 2 (by rfl) ⟨13299, by rfl⟩) (B 26599 (by norm_num) ⟨13299, by rfl⟩ (by norm_num))
theorem R35469 : Reach 35469 := rs (se 3 (by rfl) ⟨6650, by rfl⟩) (B 13301 (by norm_num) ⟨6650, by rfl⟩ (by norm_num))
theorem R35473 : Reach 35473 := rs (se 2 (by rfl) ⟨13302, by rfl⟩) (B 26605 (by norm_num) ⟨13302, by rfl⟩ (by norm_num))
theorem R35477 : Reach 35477 := rs (se 6 (by rfl) ⟨831, by rfl⟩) (B 1663 (by norm_num) ⟨831, by rfl⟩ (by norm_num))
theorem R35481 : Reach 35481 := rs (se 2 (by rfl) ⟨13305, by rfl⟩) (B 26611 (by norm_num) ⟨13305, by rfl⟩ (by norm_num))
theorem R35485 : Reach 35485 := rs (se 3 (by rfl) ⟨6653, by rfl⟩) (B 13307 (by norm_num) ⟨6653, by rfl⟩ (by norm_num))
theorem R35489 : Reach 35489 := rs (se 2 (by rfl) ⟨13308, by rfl⟩) (B 26617 (by norm_num) ⟨13308, by rfl⟩ (by norm_num))
theorem R35493 : Reach 35493 := rs (se 4 (by rfl) ⟨3327, by rfl⟩) (B 6655 (by norm_num) ⟨3327, by rfl⟩ (by norm_num))
theorem R35497 : Reach 35497 := rs (se 2 (by rfl) ⟨13311, by rfl⟩) (B 26623 (by norm_num) ⟨13311, by rfl⟩ (by norm_num))
theorem R35501 : Reach 35501 := rs (se 3 (by rfl) ⟨6656, by rfl⟩) (B 13313 (by norm_num) ⟨6656, by rfl⟩ (by norm_num))
theorem R35505 : Reach 35505 := rs (se 2 (by rfl) ⟨13314, by rfl⟩) (B 26629 (by norm_num) ⟨13314, by rfl⟩ (by norm_num))
theorem R35509 : Reach 35509 := rs (se 5 (by rfl) ⟨1664, by rfl⟩) (B 3329 (by norm_num) ⟨1664, by rfl⟩ (by norm_num))
theorem R35513 : Reach 35513 := rs (se 2 (by rfl) ⟨13317, by rfl⟩) (B 26635 (by norm_num) ⟨13317, by rfl⟩ (by norm_num))
theorem R35517 : Reach 35517 := rs (se 3 (by rfl) ⟨6659, by rfl⟩) (B 13319 (by norm_num) ⟨6659, by rfl⟩ (by norm_num))
theorem R35521 : Reach 35521 := rs (se 2 (by rfl) ⟨13320, by rfl⟩) (B 26641 (by norm_num) ⟨13320, by rfl⟩ (by norm_num))
theorem R35525 : Reach 35525 := rs (se 4 (by rfl) ⟨3330, by rfl⟩) (B 6661 (by norm_num) ⟨3330, by rfl⟩ (by norm_num))
theorem R35529 : Reach 35529 := rs (se 2 (by rfl) ⟨13323, by rfl⟩) (B 26647 (by norm_num) ⟨13323, by rfl⟩ (by norm_num))
theorem R35533 : Reach 35533 := rs (se 3 (by rfl) ⟨6662, by rfl⟩) (B 13325 (by norm_num) ⟨6662, by rfl⟩ (by norm_num))
theorem R35537 : Reach 35537 := rs (se 2 (by rfl) ⟨13326, by rfl⟩) (B 26653 (by norm_num) ⟨13326, by rfl⟩ (by norm_num))
theorem R35541 : Reach 35541 := rs (se 7 (by rfl) ⟨416, by rfl⟩) (B 833 (by norm_num) ⟨416, by rfl⟩ (by norm_num))
theorem R35545 : Reach 35545 := rs (se 2 (by rfl) ⟨13329, by rfl⟩) (B 26659 (by norm_num) ⟨13329, by rfl⟩ (by norm_num))
theorem R35549 : Reach 35549 := rs (se 3 (by rfl) ⟨6665, by rfl⟩) (B 13331 (by norm_num) ⟨6665, by rfl⟩ (by norm_num))
theorem R35553 : Reach 35553 := rs (se 2 (by rfl) ⟨13332, by rfl⟩) (B 26665 (by norm_num) ⟨13332, by rfl⟩ (by norm_num))
theorem R35557 : Reach 35557 := rs (se 4 (by rfl) ⟨3333, by rfl⟩) (B 6667 (by norm_num) ⟨3333, by rfl⟩ (by norm_num))
theorem R35561 : Reach 35561 := rs (se 2 (by rfl) ⟨13335, by rfl⟩) (B 26671 (by norm_num) ⟨13335, by rfl⟩ (by norm_num))
theorem R35565 : Reach 35565 := rs (se 3 (by rfl) ⟨6668, by rfl⟩) (B 13337 (by norm_num) ⟨6668, by rfl⟩ (by norm_num))
theorem R35569 : Reach 35569 := rs (se 2 (by rfl) ⟨13338, by rfl⟩) (B 26677 (by norm_num) ⟨13338, by rfl⟩ (by norm_num))
theorem R35573 : Reach 35573 := rs (se 5 (by rfl) ⟨1667, by rfl⟩) (B 3335 (by norm_num) ⟨1667, by rfl⟩ (by norm_num))
theorem R35577 : Reach 35577 := rs (se 2 (by rfl) ⟨13341, by rfl⟩) (B 26683 (by norm_num) ⟨13341, by rfl⟩ (by norm_num))
theorem R35581 : Reach 35581 := rs (se 3 (by rfl) ⟨6671, by rfl⟩) (B 13343 (by norm_num) ⟨6671, by rfl⟩ (by norm_num))
theorem R35585 : Reach 35585 := rs (se 2 (by rfl) ⟨13344, by rfl⟩) (B 26689 (by norm_num) ⟨13344, by rfl⟩ (by norm_num))
theorem R35589 : Reach 35589 := rs (se 4 (by rfl) ⟨3336, by rfl⟩) (B 6673 (by norm_num) ⟨3336, by rfl⟩ (by norm_num))
theorem R35593 : Reach 35593 := rs (se 2 (by rfl) ⟨13347, by rfl⟩) (B 26695 (by norm_num) ⟨13347, by rfl⟩ (by norm_num))
theorem R35597 : Reach 35597 := rs (se 3 (by rfl) ⟨6674, by rfl⟩) (B 13349 (by norm_num) ⟨6674, by rfl⟩ (by norm_num))
theorem R35601 : Reach 35601 := rs (se 2 (by rfl) ⟨13350, by rfl⟩) (B 26701 (by norm_num) ⟨13350, by rfl⟩ (by norm_num))
theorem R35605 : Reach 35605 := rs (se 6 (by rfl) ⟨834, by rfl⟩) (B 1669 (by norm_num) ⟨834, by rfl⟩ (by norm_num))
theorem R35609 : Reach 35609 := rs (se 2 (by rfl) ⟨13353, by rfl⟩) (B 26707 (by norm_num) ⟨13353, by rfl⟩ (by norm_num))
theorem R35613 : Reach 35613 := rs (se 3 (by rfl) ⟨6677, by rfl⟩) (B 13355 (by norm_num) ⟨6677, by rfl⟩ (by norm_num))
theorem R35617 : Reach 35617 := rs (se 2 (by rfl) ⟨13356, by rfl⟩) (B 26713 (by norm_num) ⟨13356, by rfl⟩ (by norm_num))
theorem R35621 : Reach 35621 := rs (se 4 (by rfl) ⟨3339, by rfl⟩) (B 6679 (by norm_num) ⟨3339, by rfl⟩ (by norm_num))
theorem R35625 : Reach 35625 := rs (se 2 (by rfl) ⟨13359, by rfl⟩) (B 26719 (by norm_num) ⟨13359, by rfl⟩ (by norm_num))
theorem R35629 : Reach 35629 := rs (se 3 (by rfl) ⟨6680, by rfl⟩) (B 13361 (by norm_num) ⟨6680, by rfl⟩ (by norm_num))
theorem R35633 : Reach 35633 := rs (se 2 (by rfl) ⟨13362, by rfl⟩) (B 26725 (by norm_num) ⟨13362, by rfl⟩ (by norm_num))
theorem R35637 : Reach 35637 := rs (se 5 (by rfl) ⟨1670, by rfl⟩) (B 3341 (by norm_num) ⟨1670, by rfl⟩ (by norm_num))
theorem R35641 : Reach 35641 := rs (se 2 (by rfl) ⟨13365, by rfl⟩) (B 26731 (by norm_num) ⟨13365, by rfl⟩ (by norm_num))
theorem R35645 : Reach 35645 := rs (se 3 (by rfl) ⟨6683, by rfl⟩) (B 13367 (by norm_num) ⟨6683, by rfl⟩ (by norm_num))
theorem R35649 : Reach 35649 := rs (se 2 (by rfl) ⟨13368, by rfl⟩) (B 26737 (by norm_num) ⟨13368, by rfl⟩ (by norm_num))
theorem R35653 : Reach 35653 := rs (se 4 (by rfl) ⟨3342, by rfl⟩) (B 6685 (by norm_num) ⟨3342, by rfl⟩ (by norm_num))
theorem R35657 : Reach 35657 := rs (se 2 (by rfl) ⟨13371, by rfl⟩) (B 26743 (by norm_num) ⟨13371, by rfl⟩ (by norm_num))
theorem R35661 : Reach 35661 := rs (se 3 (by rfl) ⟨6686, by rfl⟩) (B 13373 (by norm_num) ⟨6686, by rfl⟩ (by norm_num))
theorem R35665 : Reach 35665 := rs (se 2 (by rfl) ⟨13374, by rfl⟩) (B 26749 (by norm_num) ⟨13374, by rfl⟩ (by norm_num))
theorem R35669 : Reach 35669 := rs (se 9 (by rfl) ⟨104, by rfl⟩) (B 209 (by norm_num) ⟨104, by rfl⟩ (by norm_num))
theorem R35673 : Reach 35673 := rs (se 2 (by rfl) ⟨13377, by rfl⟩) (B 26755 (by norm_num) ⟨13377, by rfl⟩ (by norm_num))
theorem R35677 : Reach 35677 := rs (se 3 (by rfl) ⟨6689, by rfl⟩) (B 13379 (by norm_num) ⟨6689, by rfl⟩ (by norm_num))
theorem R35681 : Reach 35681 := rs (se 2 (by rfl) ⟨13380, by rfl⟩) (B 26761 (by norm_num) ⟨13380, by rfl⟩ (by norm_num))
theorem R35685 : Reach 35685 := rs (se 4 (by rfl) ⟨3345, by rfl⟩) (B 6691 (by norm_num) ⟨3345, by rfl⟩ (by norm_num))
theorem R35689 : Reach 35689 := rs (se 2 (by rfl) ⟨13383, by rfl⟩) (B 26767 (by norm_num) ⟨13383, by rfl⟩ (by norm_num))
theorem R35693 : Reach 35693 := rs (se 3 (by rfl) ⟨6692, by rfl⟩) (B 13385 (by norm_num) ⟨6692, by rfl⟩ (by norm_num))
theorem R35697 : Reach 35697 := rs (se 2 (by rfl) ⟨13386, by rfl⟩) (B 26773 (by norm_num) ⟨13386, by rfl⟩ (by norm_num))
theorem R35701 : Reach 35701 := rs (se 5 (by rfl) ⟨1673, by rfl⟩) (B 3347 (by norm_num) ⟨1673, by rfl⟩ (by norm_num))
theorem R35705 : Reach 35705 := rs (se 2 (by rfl) ⟨13389, by rfl⟩) (B 26779 (by norm_num) ⟨13389, by rfl⟩ (by norm_num))
theorem R35709 : Reach 35709 := rs (se 3 (by rfl) ⟨6695, by rfl⟩) (B 13391 (by norm_num) ⟨6695, by rfl⟩ (by norm_num))
theorem R35713 : Reach 35713 := rs (se 2 (by rfl) ⟨13392, by rfl⟩) (B 26785 (by norm_num) ⟨13392, by rfl⟩ (by norm_num))
theorem R35717 : Reach 35717 := rs (se 4 (by rfl) ⟨3348, by rfl⟩) (B 6697 (by norm_num) ⟨3348, by rfl⟩ (by norm_num))
theorem R35721 : Reach 35721 := rs (se 2 (by rfl) ⟨13395, by rfl⟩) (B 26791 (by norm_num) ⟨13395, by rfl⟩ (by norm_num))
theorem R35725 : Reach 35725 := rs (se 3 (by rfl) ⟨6698, by rfl⟩) (B 13397 (by norm_num) ⟨6698, by rfl⟩ (by norm_num))
theorem R35729 : Reach 35729 := rs (se 2 (by rfl) ⟨13398, by rfl⟩) (B 26797 (by norm_num) ⟨13398, by rfl⟩ (by norm_num))
theorem R35733 : Reach 35733 := rs (se 6 (by rfl) ⟨837, by rfl⟩) (B 1675 (by norm_num) ⟨837, by rfl⟩ (by norm_num))
theorem R35737 : Reach 35737 := rs (se 2 (by rfl) ⟨13401, by rfl⟩) (B 26803 (by norm_num) ⟨13401, by rfl⟩ (by norm_num))
theorem R35741 : Reach 35741 := rs (se 3 (by rfl) ⟨6701, by rfl⟩) (B 13403 (by norm_num) ⟨6701, by rfl⟩ (by norm_num))
theorem R35745 : Reach 35745 := rs (se 2 (by rfl) ⟨13404, by rfl⟩) (B 26809 (by norm_num) ⟨13404, by rfl⟩ (by norm_num))
theorem R35749 : Reach 35749 := rs (se 4 (by rfl) ⟨3351, by rfl⟩) (B 6703 (by norm_num) ⟨3351, by rfl⟩ (by norm_num))
theorem R35753 : Reach 35753 := rs (se 2 (by rfl) ⟨13407, by rfl⟩) (B 26815 (by norm_num) ⟨13407, by rfl⟩ (by norm_num))
theorem R35757 : Reach 35757 := rs (se 3 (by rfl) ⟨6704, by rfl⟩) (B 13409 (by norm_num) ⟨6704, by rfl⟩ (by norm_num))
theorem R35761 : Reach 35761 := rs (se 2 (by rfl) ⟨13410, by rfl⟩) (B 26821 (by norm_num) ⟨13410, by rfl⟩ (by norm_num))
theorem R35765 : Reach 35765 := rs (se 5 (by rfl) ⟨1676, by rfl⟩) (B 3353 (by norm_num) ⟨1676, by rfl⟩ (by norm_num))
theorem R35769 : Reach 35769 := rs (se 2 (by rfl) ⟨13413, by rfl⟩) (B 26827 (by norm_num) ⟨13413, by rfl⟩ (by norm_num))
theorem R35773 : Reach 35773 := rs (se 3 (by rfl) ⟨6707, by rfl⟩) (B 13415 (by norm_num) ⟨6707, by rfl⟩ (by norm_num))
theorem R35777 : Reach 35777 := rs (se 2 (by rfl) ⟨13416, by rfl⟩) (B 26833 (by norm_num) ⟨13416, by rfl⟩ (by norm_num))
theorem R35781 : Reach 35781 := rs (se 4 (by rfl) ⟨3354, by rfl⟩) (B 6709 (by norm_num) ⟨3354, by rfl⟩ (by norm_num))
theorem R35785 : Reach 35785 := rs (se 2 (by rfl) ⟨13419, by rfl⟩) (B 26839 (by norm_num) ⟨13419, by rfl⟩ (by norm_num))
theorem R35789 : Reach 35789 := rs (se 3 (by rfl) ⟨6710, by rfl⟩) (B 13421 (by norm_num) ⟨6710, by rfl⟩ (by norm_num))
theorem R35793 : Reach 35793 := rs (se 2 (by rfl) ⟨13422, by rfl⟩) (B 26845 (by norm_num) ⟨13422, by rfl⟩ (by norm_num))
theorem R35797 : Reach 35797 := rs (se 7 (by rfl) ⟨419, by rfl⟩) (B 839 (by norm_num) ⟨419, by rfl⟩ (by norm_num))
theorem R35801 : Reach 35801 := rs (se 2 (by rfl) ⟨13425, by rfl⟩) (B 26851 (by norm_num) ⟨13425, by rfl⟩ (by norm_num))
theorem R35805 : Reach 35805 := rs (se 3 (by rfl) ⟨6713, by rfl⟩) (B 13427 (by norm_num) ⟨6713, by rfl⟩ (by norm_num))
theorem R35809 : Reach 35809 := rs (se 2 (by rfl) ⟨13428, by rfl⟩) (B 26857 (by norm_num) ⟨13428, by rfl⟩ (by norm_num))
theorem R35813 : Reach 35813 := rs (se 4 (by rfl) ⟨3357, by rfl⟩) (B 6715 (by norm_num) ⟨3357, by rfl⟩ (by norm_num))
theorem R35817 : Reach 35817 := rs (se 2 (by rfl) ⟨13431, by rfl⟩) (B 26863 (by norm_num) ⟨13431, by rfl⟩ (by norm_num))
theorem R35821 : Reach 35821 := rs (se 3 (by rfl) ⟨6716, by rfl⟩) (B 13433 (by norm_num) ⟨6716, by rfl⟩ (by norm_num))
theorem R35825 : Reach 35825 := rs (se 2 (by rfl) ⟨13434, by rfl⟩) (B 26869 (by norm_num) ⟨13434, by rfl⟩ (by norm_num))
theorem R35829 : Reach 35829 := rs (se 5 (by rfl) ⟨1679, by rfl⟩) (B 3359 (by norm_num) ⟨1679, by rfl⟩ (by norm_num))
theorem R35833 : Reach 35833 := rs (se 2 (by rfl) ⟨13437, by rfl⟩) (B 26875 (by norm_num) ⟨13437, by rfl⟩ (by norm_num))
theorem R35837 : Reach 35837 := rs (se 3 (by rfl) ⟨6719, by rfl⟩) (B 13439 (by norm_num) ⟨6719, by rfl⟩ (by norm_num))
theorem R35841 : Reach 35841 := rs (se 2 (by rfl) ⟨13440, by rfl⟩) (B 26881 (by norm_num) ⟨13440, by rfl⟩ (by norm_num))
theorem R35845 : Reach 35845 := rs (se 4 (by rfl) ⟨3360, by rfl⟩) (B 6721 (by norm_num) ⟨3360, by rfl⟩ (by norm_num))
theorem R35849 : Reach 35849 := rs (se 2 (by rfl) ⟨13443, by rfl⟩) (B 26887 (by norm_num) ⟨13443, by rfl⟩ (by norm_num))
theorem R35853 : Reach 35853 := rs (se 3 (by rfl) ⟨6722, by rfl⟩) (B 13445 (by norm_num) ⟨6722, by rfl⟩ (by norm_num))
theorem R35857 : Reach 35857 := rs (se 2 (by rfl) ⟨13446, by rfl⟩) (B 26893 (by norm_num) ⟨13446, by rfl⟩ (by norm_num))
theorem R35861 : Reach 35861 := rs (se 6 (by rfl) ⟨840, by rfl⟩) (B 1681 (by norm_num) ⟨840, by rfl⟩ (by norm_num))
theorem R35865 : Reach 35865 := rs (se 2 (by rfl) ⟨13449, by rfl⟩) (B 26899 (by norm_num) ⟨13449, by rfl⟩ (by norm_num))
theorem R35869 : Reach 35869 := rs (se 3 (by rfl) ⟨6725, by rfl⟩) (B 13451 (by norm_num) ⟨6725, by rfl⟩ (by norm_num))
theorem R35873 : Reach 35873 := rs (se 2 (by rfl) ⟨13452, by rfl⟩) (B 26905 (by norm_num) ⟨13452, by rfl⟩ (by norm_num))
theorem R35877 : Reach 35877 := rs (se 4 (by rfl) ⟨3363, by rfl⟩) (B 6727 (by norm_num) ⟨3363, by rfl⟩ (by norm_num))
theorem R35881 : Reach 35881 := rs (se 2 (by rfl) ⟨13455, by rfl⟩) (B 26911 (by norm_num) ⟨13455, by rfl⟩ (by norm_num))
theorem R35885 : Reach 35885 := rs (se 3 (by rfl) ⟨6728, by rfl⟩) (B 13457 (by norm_num) ⟨6728, by rfl⟩ (by norm_num))
theorem R35889 : Reach 35889 := rs (se 2 (by rfl) ⟨13458, by rfl⟩) (B 26917 (by norm_num) ⟨13458, by rfl⟩ (by norm_num))
theorem R35893 : Reach 35893 := rs (se 5 (by rfl) ⟨1682, by rfl⟩) (B 3365 (by norm_num) ⟨1682, by rfl⟩ (by norm_num))
theorem R35897 : Reach 35897 := rs (se 2 (by rfl) ⟨13461, by rfl⟩) (B 26923 (by norm_num) ⟨13461, by rfl⟩ (by norm_num))
theorem R35901 : Reach 35901 := rs (se 3 (by rfl) ⟨6731, by rfl⟩) (B 13463 (by norm_num) ⟨6731, by rfl⟩ (by norm_num))
theorem R35905 : Reach 35905 := rs (se 2 (by rfl) ⟨13464, by rfl⟩) (B 26929 (by norm_num) ⟨13464, by rfl⟩ (by norm_num))
theorem R68677 : Reach 68677 := rs (se 4 (by rfl) ⟨6438, by rfl⟩) (B 12877 (by norm_num) ⟨6438, by rfl⟩ (by norm_num))
theorem R35909 : Reach 35909 := rs (se 4 (by rfl) ⟨3366, by rfl⟩) (B 6733 (by norm_num) ⟨3366, by rfl⟩ (by norm_num))
theorem R35913 : Reach 35913 := rs (se 2 (by rfl) ⟨13467, by rfl⟩) (B 26935 (by norm_num) ⟨13467, by rfl⟩ (by norm_num))
theorem R35917 : Reach 35917 := rs (se 3 (by rfl) ⟨6734, by rfl⟩) (B 13469 (by norm_num) ⟨6734, by rfl⟩ (by norm_num))
theorem R35921 : Reach 35921 := rs (se 2 (by rfl) ⟨13470, by rfl⟩) (B 26941 (by norm_num) ⟨13470, by rfl⟩ (by norm_num))
theorem R35925 : Reach 35925 := rs (se 8 (by rfl) ⟨210, by rfl⟩) (B 421 (by norm_num) ⟨210, by rfl⟩ (by norm_num))
theorem R35929 : Reach 35929 := rs (se 2 (by rfl) ⟨13473, by rfl⟩) (B 26947 (by norm_num) ⟨13473, by rfl⟩ (by norm_num))
theorem R35933 : Reach 35933 := rs (se 3 (by rfl) ⟨6737, by rfl⟩) (B 13475 (by norm_num) ⟨6737, by rfl⟩ (by norm_num))
theorem R68701 : Reach 68701 := rs (se 3 (by rfl) ⟨12881, by rfl⟩) (B 25763 (by norm_num) ⟨12881, by rfl⟩ (by norm_num))
theorem R35937 : Reach 35937 := rs (se 2 (by rfl) ⟨13476, by rfl⟩) (B 26953 (by norm_num) ⟨13476, by rfl⟩ (by norm_num))
theorem R35941 : Reach 35941 := rs (se 4 (by rfl) ⟨3369, by rfl⟩) (B 6739 (by norm_num) ⟨3369, by rfl⟩ (by norm_num))
theorem R35945 : Reach 35945 := rs (se 2 (by rfl) ⟨13479, by rfl⟩) (B 26959 (by norm_num) ⟨13479, by rfl⟩ (by norm_num))
theorem R35949 : Reach 35949 := rs (se 3 (by rfl) ⟨6740, by rfl⟩) (B 13481 (by norm_num) ⟨6740, by rfl⟩ (by norm_num))
theorem R35953 : Reach 35953 := rs (se 2 (by rfl) ⟨13482, by rfl⟩) (B 26965 (by norm_num) ⟨13482, by rfl⟩ (by norm_num))
theorem R35957 : Reach 35957 := rs (se 5 (by rfl) ⟨1685, by rfl⟩) (B 3371 (by norm_num) ⟨1685, by rfl⟩ (by norm_num))
theorem R35961 : Reach 35961 := rs (se 2 (by rfl) ⟨13485, by rfl⟩) (B 26971 (by norm_num) ⟨13485, by rfl⟩ (by norm_num))
theorem R35965 : Reach 35965 := rs (se 3 (by rfl) ⟨6743, by rfl⟩) (B 13487 (by norm_num) ⟨6743, by rfl⟩ (by norm_num))
theorem R35969 : Reach 35969 := rs (se 2 (by rfl) ⟨13488, by rfl⟩) (B 26977 (by norm_num) ⟨13488, by rfl⟩ (by norm_num))
theorem R35973 : Reach 35973 := rs (se 4 (by rfl) ⟨3372, by rfl⟩) (B 6745 (by norm_num) ⟨3372, by rfl⟩ (by norm_num))
theorem R35977 : Reach 35977 := rs (se 2 (by rfl) ⟨13491, by rfl⟩) (B 26983 (by norm_num) ⟨13491, by rfl⟩ (by norm_num))
theorem R35981 : Reach 35981 := rs (se 3 (by rfl) ⟨6746, by rfl⟩) (B 13493 (by norm_num) ⟨6746, by rfl⟩ (by norm_num))
theorem R35985 : Reach 35985 := rs (se 2 (by rfl) ⟨13494, by rfl⟩) (B 26989 (by norm_num) ⟨13494, by rfl⟩ (by norm_num))
theorem R35989 : Reach 35989 := rs (se 6 (by rfl) ⟨843, by rfl⟩) (B 1687 (by norm_num) ⟨843, by rfl⟩ (by norm_num))
theorem R35993 : Reach 35993 := rs (se 2 (by rfl) ⟨13497, by rfl⟩) (B 26995 (by norm_num) ⟨13497, by rfl⟩ (by norm_num))
theorem R35997 : Reach 35997 := rs (se 3 (by rfl) ⟨6749, by rfl⟩) (B 13499 (by norm_num) ⟨6749, by rfl⟩ (by norm_num))
theorem R36001 : Reach 36001 := rs (se 2 (by rfl) ⟨13500, by rfl⟩) (B 27001 (by norm_num) ⟨13500, by rfl⟩ (by norm_num))
theorem R36005 : Reach 36005 := rs (se 4 (by rfl) ⟨3375, by rfl⟩) (B 6751 (by norm_num) ⟨3375, by rfl⟩ (by norm_num))
theorem R36009 : Reach 36009 := rs (se 2 (by rfl) ⟨13503, by rfl⟩) (B 27007 (by norm_num) ⟨13503, by rfl⟩ (by norm_num))
theorem R36013 : Reach 36013 := rs (se 3 (by rfl) ⟨6752, by rfl⟩) (B 13505 (by norm_num) ⟨6752, by rfl⟩ (by norm_num))
theorem R36017 : Reach 36017 := rs (se 2 (by rfl) ⟨13506, by rfl⟩) (B 27013 (by norm_num) ⟨13506, by rfl⟩ (by norm_num))
theorem R36021 : Reach 36021 := rs (se 5 (by rfl) ⟨1688, by rfl⟩) (B 3377 (by norm_num) ⟨1688, by rfl⟩ (by norm_num))
theorem R36025 : Reach 36025 := rs (se 2 (by rfl) ⟨13509, by rfl⟩) (B 27019 (by norm_num) ⟨13509, by rfl⟩ (by norm_num))
theorem R36029 : Reach 36029 := rs (se 3 (by rfl) ⟨6755, by rfl⟩) (B 13511 (by norm_num) ⟨6755, by rfl⟩ (by norm_num))
theorem R36033 : Reach 36033 := rs (se 2 (by rfl) ⟨13512, by rfl⟩) (B 27025 (by norm_num) ⟨13512, by rfl⟩ (by norm_num))
theorem R36037 : Reach 36037 := rs (se 4 (by rfl) ⟨3378, by rfl⟩) (B 6757 (by norm_num) ⟨3378, by rfl⟩ (by norm_num))
theorem R36041 : Reach 36041 := rs (se 2 (by rfl) ⟨13515, by rfl⟩) (B 27031 (by norm_num) ⟨13515, by rfl⟩ (by norm_num))
theorem R36045 : Reach 36045 := rs (se 3 (by rfl) ⟨6758, by rfl⟩) (B 13517 (by norm_num) ⟨6758, by rfl⟩ (by norm_num))
theorem R36049 : Reach 36049 := rs (se 2 (by rfl) ⟨13518, by rfl⟩) (B 27037 (by norm_num) ⟨13518, by rfl⟩ (by norm_num))
theorem R36053 : Reach 36053 := rs (se 7 (by rfl) ⟨422, by rfl⟩) (B 845 (by norm_num) ⟨422, by rfl⟩ (by norm_num))
theorem R36057 : Reach 36057 := rs (se 2 (by rfl) ⟨13521, by rfl⟩) (B 27043 (by norm_num) ⟨13521, by rfl⟩ (by norm_num))
theorem R36061 : Reach 36061 := rs (se 3 (by rfl) ⟨6761, by rfl⟩) (B 13523 (by norm_num) ⟨6761, by rfl⟩ (by norm_num))
theorem R36065 : Reach 36065 := rs (se 2 (by rfl) ⟨13524, by rfl⟩) (B 27049 (by norm_num) ⟨13524, by rfl⟩ (by norm_num))
theorem R36069 : Reach 36069 := rs (se 4 (by rfl) ⟨3381, by rfl⟩) (B 6763 (by norm_num) ⟨3381, by rfl⟩ (by norm_num))
theorem R36073 : Reach 36073 := rs (se 2 (by rfl) ⟨13527, by rfl⟩) (B 27055 (by norm_num) ⟨13527, by rfl⟩ (by norm_num))
theorem R36077 : Reach 36077 := rs (se 3 (by rfl) ⟨6764, by rfl⟩) (B 13529 (by norm_num) ⟨6764, by rfl⟩ (by norm_num))
theorem R68845 : Reach 68845 := rs (se 3 (by rfl) ⟨12908, by rfl⟩) (B 25817 (by norm_num) ⟨12908, by rfl⟩ (by norm_num))
theorem R36081 : Reach 36081 := rs (se 2 (by rfl) ⟨13530, by rfl⟩) (B 27061 (by norm_num) ⟨13530, by rfl⟩ (by norm_num))
theorem R36085 : Reach 36085 := rs (se 5 (by rfl) ⟨1691, by rfl⟩) (B 3383 (by norm_num) ⟨1691, by rfl⟩ (by norm_num))
theorem R36089 : Reach 36089 := rs (se 2 (by rfl) ⟨13533, by rfl⟩) (B 27067 (by norm_num) ⟨13533, by rfl⟩ (by norm_num))
theorem R36093 : Reach 36093 := rs (se 3 (by rfl) ⟨6767, by rfl⟩) (B 13535 (by norm_num) ⟨6767, by rfl⟩ (by norm_num))
theorem R36097 : Reach 36097 := rs (se 2 (by rfl) ⟨13536, by rfl⟩) (B 27073 (by norm_num) ⟨13536, by rfl⟩ (by norm_num))
theorem R36101 : Reach 36101 := rs (se 4 (by rfl) ⟨3384, by rfl⟩) (B 6769 (by norm_num) ⟨3384, by rfl⟩ (by norm_num))
theorem R36105 : Reach 36105 := rs (se 2 (by rfl) ⟨13539, by rfl⟩) (B 27079 (by norm_num) ⟨13539, by rfl⟩ (by norm_num))
theorem R36109 : Reach 36109 := rs (se 3 (by rfl) ⟨6770, by rfl⟩) (B 13541 (by norm_num) ⟨6770, by rfl⟩ (by norm_num))
theorem R36113 : Reach 36113 := rs (se 2 (by rfl) ⟨13542, by rfl⟩) (B 27085 (by norm_num) ⟨13542, by rfl⟩ (by norm_num))
theorem R36117 : Reach 36117 := rs (se 6 (by rfl) ⟨846, by rfl⟩) (B 1693 (by norm_num) ⟨846, by rfl⟩ (by norm_num))
theorem R36121 : Reach 36121 := rs (se 2 (by rfl) ⟨13545, by rfl⟩) (B 27091 (by norm_num) ⟨13545, by rfl⟩ (by norm_num))
theorem R36125 : Reach 36125 := rs (se 3 (by rfl) ⟨6773, by rfl⟩) (B 13547 (by norm_num) ⟨6773, by rfl⟩ (by norm_num))
theorem R36129 : Reach 36129 := rs (se 2 (by rfl) ⟨13548, by rfl⟩) (B 27097 (by norm_num) ⟨13548, by rfl⟩ (by norm_num))
theorem R36133 : Reach 36133 := rs (se 4 (by rfl) ⟨3387, by rfl⟩) (B 6775 (by norm_num) ⟨3387, by rfl⟩ (by norm_num))
theorem R36137 : Reach 36137 := rs (se 2 (by rfl) ⟨13551, by rfl⟩) (B 27103 (by norm_num) ⟨13551, by rfl⟩ (by norm_num))
theorem R36141 : Reach 36141 := rs (se 3 (by rfl) ⟨6776, by rfl⟩) (B 13553 (by norm_num) ⟨6776, by rfl⟩ (by norm_num))
theorem R36145 : Reach 36145 := rs (se 2 (by rfl) ⟨13554, by rfl⟩) (B 27109 (by norm_num) ⟨13554, by rfl⟩ (by norm_num))
theorem R36149 : Reach 36149 := rs (se 5 (by rfl) ⟨1694, by rfl⟩) (B 3389 (by norm_num) ⟨1694, by rfl⟩ (by norm_num))
theorem R36153 : Reach 36153 := rs (se 2 (by rfl) ⟨13557, by rfl⟩) (B 27115 (by norm_num) ⟨13557, by rfl⟩ (by norm_num))
theorem R36157 : Reach 36157 := rs (se 3 (by rfl) ⟨6779, by rfl⟩) (B 13559 (by norm_num) ⟨6779, by rfl⟩ (by norm_num))
theorem R36161 : Reach 36161 := rs (se 2 (by rfl) ⟨13560, by rfl⟩) (B 27121 (by norm_num) ⟨13560, by rfl⟩ (by norm_num))
theorem R36165 : Reach 36165 := rs (se 4 (by rfl) ⟨3390, by rfl⟩) (B 6781 (by norm_num) ⟨3390, by rfl⟩ (by norm_num))
theorem R36169 : Reach 36169 := rs (se 2 (by rfl) ⟨13563, by rfl⟩) (B 27127 (by norm_num) ⟨13563, by rfl⟩ (by norm_num))
theorem R36173 : Reach 36173 := rs (se 3 (by rfl) ⟨6782, by rfl⟩) (B 13565 (by norm_num) ⟨6782, by rfl⟩ (by norm_num))
theorem R36177 : Reach 36177 := rs (se 2 (by rfl) ⟨13566, by rfl⟩) (B 27133 (by norm_num) ⟨13566, by rfl⟩ (by norm_num))
theorem R36181 : Reach 36181 := rs (se 11 (by rfl) ⟨26, by rfl⟩) (B 53 (by norm_num) ⟨26, by rfl⟩ (by norm_num))
theorem R36185 : Reach 36185 := rs (se 2 (by rfl) ⟨13569, by rfl⟩) (B 27139 (by norm_num) ⟨13569, by rfl⟩ (by norm_num))
theorem R36189 : Reach 36189 := rs (se 3 (by rfl) ⟨6785, by rfl⟩) (B 13571 (by norm_num) ⟨6785, by rfl⟩ (by norm_num))
theorem R36193 : Reach 36193 := rs (se 2 (by rfl) ⟨13572, by rfl⟩) (B 27145 (by norm_num) ⟨13572, by rfl⟩ (by norm_num))
theorem R36197 : Reach 36197 := rs (se 4 (by rfl) ⟨3393, by rfl⟩) (B 6787 (by norm_num) ⟨3393, by rfl⟩ (by norm_num))
theorem R36201 : Reach 36201 := rs (se 2 (by rfl) ⟨13575, by rfl⟩) (B 27151 (by norm_num) ⟨13575, by rfl⟩ (by norm_num))
theorem R36205 : Reach 36205 := rs (se 3 (by rfl) ⟨6788, by rfl⟩) (B 13577 (by norm_num) ⟨6788, by rfl⟩ (by norm_num))
theorem R36209 : Reach 36209 := rs (se 2 (by rfl) ⟨13578, by rfl⟩) (B 27157 (by norm_num) ⟨13578, by rfl⟩ (by norm_num))
theorem R36213 : Reach 36213 := rs (se 5 (by rfl) ⟨1697, by rfl⟩) (B 3395 (by norm_num) ⟨1697, by rfl⟩ (by norm_num))
theorem R36217 : Reach 36217 := rs (se 2 (by rfl) ⟨13581, by rfl⟩) (B 27163 (by norm_num) ⟨13581, by rfl⟩ (by norm_num))
theorem R36221 : Reach 36221 := rs (se 3 (by rfl) ⟨6791, by rfl⟩) (B 13583 (by norm_num) ⟨6791, by rfl⟩ (by norm_num))
theorem R36225 : Reach 36225 := rs (se 2 (by rfl) ⟨13584, by rfl⟩) (B 27169 (by norm_num) ⟨13584, by rfl⟩ (by norm_num))
theorem R36229 : Reach 36229 := rs (se 4 (by rfl) ⟨3396, by rfl⟩) (B 6793 (by norm_num) ⟨3396, by rfl⟩ (by norm_num))
theorem R36233 : Reach 36233 := rs (se 2 (by rfl) ⟨13587, by rfl⟩) (B 27175 (by norm_num) ⟨13587, by rfl⟩ (by norm_num))
theorem R36237 : Reach 36237 := rs (se 3 (by rfl) ⟨6794, by rfl⟩) (B 13589 (by norm_num) ⟨6794, by rfl⟩ (by norm_num))
theorem R69005 : Reach 69005 := rs (se 3 (by rfl) ⟨12938, by rfl⟩) (B 25877 (by norm_num) ⟨12938, by rfl⟩ (by norm_num))
theorem R36241 : Reach 36241 := rs (se 2 (by rfl) ⟨13590, by rfl⟩) (B 27181 (by norm_num) ⟨13590, by rfl⟩ (by norm_num))
theorem R36245 : Reach 36245 := rs (se 6 (by rfl) ⟨849, by rfl⟩) (B 1699 (by norm_num) ⟨849, by rfl⟩ (by norm_num))
theorem R36249 : Reach 36249 := rs (se 2 (by rfl) ⟨13593, by rfl⟩) (B 27187 (by norm_num) ⟨13593, by rfl⟩ (by norm_num))
theorem R36253 : Reach 36253 := rs (se 3 (by rfl) ⟨6797, by rfl⟩) (B 13595 (by norm_num) ⟨6797, by rfl⟩ (by norm_num))
theorem R36257 : Reach 36257 := rs (se 2 (by rfl) ⟨13596, by rfl⟩) (B 27193 (by norm_num) ⟨13596, by rfl⟩ (by norm_num))
theorem R36261 : Reach 36261 := rs (se 4 (by rfl) ⟨3399, by rfl⟩) (B 6799 (by norm_num) ⟨3399, by rfl⟩ (by norm_num))
theorem R36265 : Reach 36265 := rs (se 2 (by rfl) ⟨13599, by rfl⟩) (B 27199 (by norm_num) ⟨13599, by rfl⟩ (by norm_num))
theorem R36269 : Reach 36269 := rs (se 3 (by rfl) ⟨6800, by rfl⟩) (B 13601 (by norm_num) ⟨6800, by rfl⟩ (by norm_num))
theorem R36273 : Reach 36273 := rs (se 2 (by rfl) ⟨13602, by rfl⟩) (B 27205 (by norm_num) ⟨13602, by rfl⟩ (by norm_num))
theorem R36277 : Reach 36277 := rs (se 5 (by rfl) ⟨1700, by rfl⟩) (B 3401 (by norm_num) ⟨1700, by rfl⟩ (by norm_num))
theorem R36281 : Reach 36281 := rs (se 2 (by rfl) ⟨13605, by rfl⟩) (B 27211 (by norm_num) ⟨13605, by rfl⟩ (by norm_num))
theorem R36285 : Reach 36285 := rs (se 3 (by rfl) ⟨6803, by rfl⟩) (B 13607 (by norm_num) ⟨6803, by rfl⟩ (by norm_num))
theorem R36289 : Reach 36289 := rs (se 2 (by rfl) ⟨13608, by rfl⟩) (B 27217 (by norm_num) ⟨13608, by rfl⟩ (by norm_num))
theorem R36293 : Reach 36293 := rs (se 4 (by rfl) ⟨3402, by rfl⟩) (B 6805 (by norm_num) ⟨3402, by rfl⟩ (by norm_num))
theorem R36297 : Reach 36297 := rs (se 2 (by rfl) ⟨13611, by rfl⟩) (B 27223 (by norm_num) ⟨13611, by rfl⟩ (by norm_num))
theorem R36301 : Reach 36301 := rs (se 3 (by rfl) ⟨6806, by rfl⟩) (B 13613 (by norm_num) ⟨6806, by rfl⟩ (by norm_num))
theorem R36305 : Reach 36305 := rs (se 2 (by rfl) ⟨13614, by rfl⟩) (B 27229 (by norm_num) ⟨13614, by rfl⟩ (by norm_num))
theorem R36309 : Reach 36309 := rs (se 7 (by rfl) ⟨425, by rfl⟩) (B 851 (by norm_num) ⟨425, by rfl⟩ (by norm_num))
theorem R36313 : Reach 36313 := rs (se 2 (by rfl) ⟨13617, by rfl⟩) (B 27235 (by norm_num) ⟨13617, by rfl⟩ (by norm_num))
theorem R36317 : Reach 36317 := rs (se 3 (by rfl) ⟨6809, by rfl⟩) (B 13619 (by norm_num) ⟨6809, by rfl⟩ (by norm_num))
theorem R36321 : Reach 36321 := rs (se 2 (by rfl) ⟨13620, by rfl⟩) (B 27241 (by norm_num) ⟨13620, by rfl⟩ (by norm_num))
theorem R36325 : Reach 36325 := rs (se 4 (by rfl) ⟨3405, by rfl⟩) (B 6811 (by norm_num) ⟨3405, by rfl⟩ (by norm_num))
theorem R36329 : Reach 36329 := rs (se 2 (by rfl) ⟨13623, by rfl⟩) (B 27247 (by norm_num) ⟨13623, by rfl⟩ (by norm_num))
theorem R36333 : Reach 36333 := rs (se 3 (by rfl) ⟨6812, by rfl⟩) (B 13625 (by norm_num) ⟨6812, by rfl⟩ (by norm_num))
theorem R36337 : Reach 36337 := rs (se 2 (by rfl) ⟨13626, by rfl⟩) (B 27253 (by norm_num) ⟨13626, by rfl⟩ (by norm_num))
theorem R36341 : Reach 36341 := rs (se 5 (by rfl) ⟨1703, by rfl⟩) (B 3407 (by norm_num) ⟨1703, by rfl⟩ (by norm_num))
theorem R36345 : Reach 36345 := rs (se 2 (by rfl) ⟨13629, by rfl⟩) (B 27259 (by norm_num) ⟨13629, by rfl⟩ (by norm_num))
theorem R36349 : Reach 36349 := rs (se 3 (by rfl) ⟨6815, by rfl⟩) (B 13631 (by norm_num) ⟨6815, by rfl⟩ (by norm_num))
theorem R36353 : Reach 36353 := rs (se 2 (by rfl) ⟨13632, by rfl⟩) (B 27265 (by norm_num) ⟨13632, by rfl⟩ (by norm_num))
theorem R36357 : Reach 36357 := rs (se 4 (by rfl) ⟨3408, by rfl⟩) (B 6817 (by norm_num) ⟨3408, by rfl⟩ (by norm_num))
theorem R36361 : Reach 36361 := rs (se 2 (by rfl) ⟨13635, by rfl⟩) (B 27271 (by norm_num) ⟨13635, by rfl⟩ (by norm_num))
theorem R36365 : Reach 36365 := rs (se 3 (by rfl) ⟨6818, by rfl⟩) (B 13637 (by norm_num) ⟨6818, by rfl⟩ (by norm_num))
theorem R36369 : Reach 36369 := rs (se 2 (by rfl) ⟨13638, by rfl⟩) (B 27277 (by norm_num) ⟨13638, by rfl⟩ (by norm_num))
theorem R36373 : Reach 36373 := rs (se 6 (by rfl) ⟨852, by rfl⟩) (B 1705 (by norm_num) ⟨852, by rfl⟩ (by norm_num))
theorem R36377 : Reach 36377 := rs (se 2 (by rfl) ⟨13641, by rfl⟩) (B 27283 (by norm_num) ⟨13641, by rfl⟩ (by norm_num))
theorem R36381 : Reach 36381 := rs (se 3 (by rfl) ⟨6821, by rfl⟩) (B 13643 (by norm_num) ⟨6821, by rfl⟩ (by norm_num))
theorem R69149 : Reach 69149 := rs (se 3 (by rfl) ⟨12965, by rfl⟩) (B 25931 (by norm_num) ⟨12965, by rfl⟩ (by norm_num))
theorem R36385 : Reach 36385 := rs (se 2 (by rfl) ⟨13644, by rfl⟩) (B 27289 (by norm_num) ⟨13644, by rfl⟩ (by norm_num))
theorem R36389 : Reach 36389 := rs (se 4 (by rfl) ⟨3411, by rfl⟩) (B 6823 (by norm_num) ⟨3411, by rfl⟩ (by norm_num))
theorem R36393 : Reach 36393 := rs (se 2 (by rfl) ⟨13647, by rfl⟩) (B 27295 (by norm_num) ⟨13647, by rfl⟩ (by norm_num))
theorem R36397 : Reach 36397 := rs (se 3 (by rfl) ⟨6824, by rfl⟩) (B 13649 (by norm_num) ⟨6824, by rfl⟩ (by norm_num))
theorem R36401 : Reach 36401 := rs (se 2 (by rfl) ⟨13650, by rfl⟩) (B 27301 (by norm_num) ⟨13650, by rfl⟩ (by norm_num))
theorem R36405 : Reach 36405 := rs (se 5 (by rfl) ⟨1706, by rfl⟩) (B 3413 (by norm_num) ⟨1706, by rfl⟩ (by norm_num))
theorem R36409 : Reach 36409 := rs (se 2 (by rfl) ⟨13653, by rfl⟩) (B 27307 (by norm_num) ⟨13653, by rfl⟩ (by norm_num))
theorem R36413 : Reach 36413 := rs (se 3 (by rfl) ⟨6827, by rfl⟩) (B 13655 (by norm_num) ⟨6827, by rfl⟩ (by norm_num))
theorem R36417 : Reach 36417 := rs (se 2 (by rfl) ⟨13656, by rfl⟩) (B 27313 (by norm_num) ⟨13656, by rfl⟩ (by norm_num))
theorem R36421 : Reach 36421 := rs (se 4 (by rfl) ⟨3414, by rfl⟩) (B 6829 (by norm_num) ⟨3414, by rfl⟩ (by norm_num))
theorem R36425 : Reach 36425 := rs (se 2 (by rfl) ⟨13659, by rfl⟩) (B 27319 (by norm_num) ⟨13659, by rfl⟩ (by norm_num))
theorem R36429 : Reach 36429 := rs (se 3 (by rfl) ⟨6830, by rfl⟩) (B 13661 (by norm_num) ⟨6830, by rfl⟩ (by norm_num))
theorem R36433 : Reach 36433 := rs (se 2 (by rfl) ⟨13662, by rfl⟩) (B 27325 (by norm_num) ⟨13662, by rfl⟩ (by norm_num))
theorem R36437 : Reach 36437 := rs (se 8 (by rfl) ⟨213, by rfl⟩) (B 427 (by norm_num) ⟨213, by rfl⟩ (by norm_num))
theorem R36441 : Reach 36441 := rs (se 2 (by rfl) ⟨13665, by rfl⟩) (B 27331 (by norm_num) ⟨13665, by rfl⟩ (by norm_num))
theorem R36445 : Reach 36445 := rs (se 3 (by rfl) ⟨6833, by rfl⟩) (B 13667 (by norm_num) ⟨6833, by rfl⟩ (by norm_num))
theorem R36449 : Reach 36449 := rs (se 2 (by rfl) ⟨13668, by rfl⟩) (B 27337 (by norm_num) ⟨13668, by rfl⟩ (by norm_num))
theorem R36453 : Reach 36453 := rs (se 4 (by rfl) ⟨3417, by rfl⟩) (B 6835 (by norm_num) ⟨3417, by rfl⟩ (by norm_num))
theorem R36457 : Reach 36457 := rs (se 2 (by rfl) ⟨13671, by rfl⟩) (B 27343 (by norm_num) ⟨13671, by rfl⟩ (by norm_num))
theorem R36461 : Reach 36461 := rs (se 3 (by rfl) ⟨6836, by rfl⟩) (B 13673 (by norm_num) ⟨6836, by rfl⟩ (by norm_num))
theorem R36465 : Reach 36465 := rs (se 2 (by rfl) ⟨13674, by rfl⟩) (B 27349 (by norm_num) ⟨13674, by rfl⟩ (by norm_num))
theorem R36469 : Reach 36469 := rs (se 5 (by rfl) ⟨1709, by rfl⟩) (B 3419 (by norm_num) ⟨1709, by rfl⟩ (by norm_num))
theorem R36473 : Reach 36473 := rs (se 2 (by rfl) ⟨13677, by rfl⟩) (B 27355 (by norm_num) ⟨13677, by rfl⟩ (by norm_num))
theorem R36477 : Reach 36477 := rs (se 3 (by rfl) ⟨6839, by rfl⟩) (B 13679 (by norm_num) ⟨6839, by rfl⟩ (by norm_num))
theorem R36481 : Reach 36481 := rs (se 2 (by rfl) ⟨13680, by rfl⟩) (B 27361 (by norm_num) ⟨13680, by rfl⟩ (by norm_num))
theorem R36485 : Reach 36485 := rs (se 4 (by rfl) ⟨3420, by rfl⟩) (B 6841 (by norm_num) ⟨3420, by rfl⟩ (by norm_num))
theorem R36489 : Reach 36489 := rs (se 2 (by rfl) ⟨13683, by rfl⟩) (B 27367 (by norm_num) ⟨13683, by rfl⟩ (by norm_num))
theorem R36493 : Reach 36493 := rs (se 3 (by rfl) ⟨6842, by rfl⟩) (B 13685 (by norm_num) ⟨6842, by rfl⟩ (by norm_num))
theorem R36497 : Reach 36497 := rs (se 2 (by rfl) ⟨13686, by rfl⟩) (B 27373 (by norm_num) ⟨13686, by rfl⟩ (by norm_num))
theorem R36501 : Reach 36501 := rs (se 6 (by rfl) ⟨855, by rfl⟩) (B 1711 (by norm_num) ⟨855, by rfl⟩ (by norm_num))
theorem R36505 : Reach 36505 := rs (se 2 (by rfl) ⟨13689, by rfl⟩) (B 27379 (by norm_num) ⟨13689, by rfl⟩ (by norm_num))
theorem R36509 : Reach 36509 := rs (se 3 (by rfl) ⟨6845, by rfl⟩) (B 13691 (by norm_num) ⟨6845, by rfl⟩ (by norm_num))
theorem R36513 : Reach 36513 := rs (se 2 (by rfl) ⟨13692, by rfl⟩) (B 27385 (by norm_num) ⟨13692, by rfl⟩ (by norm_num))
theorem R36517 : Reach 36517 := rs (se 4 (by rfl) ⟨3423, by rfl⟩) (B 6847 (by norm_num) ⟨3423, by rfl⟩ (by norm_num))
theorem R36521 : Reach 36521 := rs (se 2 (by rfl) ⟨13695, by rfl⟩) (B 27391 (by norm_num) ⟨13695, by rfl⟩ (by norm_num))
theorem R36525 : Reach 36525 := rs (se 3 (by rfl) ⟨6848, by rfl⟩) (B 13697 (by norm_num) ⟨6848, by rfl⟩ (by norm_num))
theorem R36529 : Reach 36529 := rs (se 2 (by rfl) ⟨13698, by rfl⟩) (B 27397 (by norm_num) ⟨13698, by rfl⟩ (by norm_num))
theorem R36533 : Reach 36533 := rs (se 5 (by rfl) ⟨1712, by rfl⟩) (B 3425 (by norm_num) ⟨1712, by rfl⟩ (by norm_num))
theorem R36537 : Reach 36537 := rs (se 2 (by rfl) ⟨13701, by rfl⟩) (B 27403 (by norm_num) ⟨13701, by rfl⟩ (by norm_num))
theorem R36541 : Reach 36541 := rs (se 3 (by rfl) ⟨6851, by rfl⟩) (B 13703 (by norm_num) ⟨6851, by rfl⟩ (by norm_num))
theorem R36545 : Reach 36545 := rs (se 2 (by rfl) ⟨13704, by rfl⟩) (B 27409 (by norm_num) ⟨13704, by rfl⟩ (by norm_num))
theorem R36549 : Reach 36549 := rs (se 4 (by rfl) ⟨3426, by rfl⟩) (B 6853 (by norm_num) ⟨3426, by rfl⟩ (by norm_num))
theorem R36553 : Reach 36553 := rs (se 2 (by rfl) ⟨13707, by rfl⟩) (B 27415 (by norm_num) ⟨13707, by rfl⟩ (by norm_num))
theorem R36557 : Reach 36557 := rs (se 3 (by rfl) ⟨6854, by rfl⟩) (B 13709 (by norm_num) ⟨6854, by rfl⟩ (by norm_num))
theorem R36561 : Reach 36561 := rs (se 2 (by rfl) ⟨13710, by rfl⟩) (B 27421 (by norm_num) ⟨13710, by rfl⟩ (by norm_num))
theorem R36565 : Reach 36565 := rs (se 7 (by rfl) ⟨428, by rfl⟩) (B 857 (by norm_num) ⟨428, by rfl⟩ (by norm_num))
theorem R36569 : Reach 36569 := rs (se 2 (by rfl) ⟨13713, by rfl⟩) (B 27427 (by norm_num) ⟨13713, by rfl⟩ (by norm_num))
theorem R36573 : Reach 36573 := rs (se 3 (by rfl) ⟨6857, by rfl⟩) (B 13715 (by norm_num) ⟨6857, by rfl⟩ (by norm_num))
theorem R36577 : Reach 36577 := rs (se 2 (by rfl) ⟨13716, by rfl⟩) (B 27433 (by norm_num) ⟨13716, by rfl⟩ (by norm_num))
theorem R36581 : Reach 36581 := rs (se 4 (by rfl) ⟨3429, by rfl⟩) (B 6859 (by norm_num) ⟨3429, by rfl⟩ (by norm_num))
theorem R36585 : Reach 36585 := rs (se 2 (by rfl) ⟨13719, by rfl⟩) (B 27439 (by norm_num) ⟨13719, by rfl⟩ (by norm_num))
theorem R36589 : Reach 36589 := rs (se 3 (by rfl) ⟨6860, by rfl⟩) (B 13721 (by norm_num) ⟨6860, by rfl⟩ (by norm_num))
theorem R36593 : Reach 36593 := rs (se 2 (by rfl) ⟨13722, by rfl⟩) (B 27445 (by norm_num) ⟨13722, by rfl⟩ (by norm_num))
theorem R36597 : Reach 36597 := rs (se 5 (by rfl) ⟨1715, by rfl⟩) (B 3431 (by norm_num) ⟨1715, by rfl⟩ (by norm_num))
theorem R36601 : Reach 36601 := rs (se 2 (by rfl) ⟨13725, by rfl⟩) (B 27451 (by norm_num) ⟨13725, by rfl⟩ (by norm_num))
theorem R36605 : Reach 36605 := rs (se 3 (by rfl) ⟨6863, by rfl⟩) (B 13727 (by norm_num) ⟨6863, by rfl⟩ (by norm_num))
theorem R36609 : Reach 36609 := rs (se 2 (by rfl) ⟨13728, by rfl⟩) (B 27457 (by norm_num) ⟨13728, by rfl⟩ (by norm_num))
theorem R36613 : Reach 36613 := rs (se 4 (by rfl) ⟨3432, by rfl⟩) (B 6865 (by norm_num) ⟨3432, by rfl⟩ (by norm_num))
theorem R36617 : Reach 36617 := rs (se 2 (by rfl) ⟨13731, by rfl⟩) (B 27463 (by norm_num) ⟨13731, by rfl⟩ (by norm_num))
theorem R36621 : Reach 36621 := rs (se 3 (by rfl) ⟨6866, by rfl⟩) (B 13733 (by norm_num) ⟨6866, by rfl⟩ (by norm_num))
theorem R36625 : Reach 36625 := rs (se 2 (by rfl) ⟨13734, by rfl⟩) (B 27469 (by norm_num) ⟨13734, by rfl⟩ (by norm_num))
theorem R36629 : Reach 36629 := rs (se 6 (by rfl) ⟨858, by rfl⟩) (B 1717 (by norm_num) ⟨858, by rfl⟩ (by norm_num))
theorem R36633 : Reach 36633 := rs (se 2 (by rfl) ⟨13737, by rfl⟩) (B 27475 (by norm_num) ⟨13737, by rfl⟩ (by norm_num))
theorem R36637 : Reach 36637 := rs (se 3 (by rfl) ⟨6869, by rfl⟩) (B 13739 (by norm_num) ⟨6869, by rfl⟩ (by norm_num))
theorem R36641 : Reach 36641 := rs (se 2 (by rfl) ⟨13740, by rfl⟩) (B 27481 (by norm_num) ⟨13740, by rfl⟩ (by norm_num))
theorem R36645 : Reach 36645 := rs (se 4 (by rfl) ⟨3435, by rfl⟩) (B 6871 (by norm_num) ⟨3435, by rfl⟩ (by norm_num))
theorem R36649 : Reach 36649 := rs (se 2 (by rfl) ⟨13743, by rfl⟩) (B 27487 (by norm_num) ⟨13743, by rfl⟩ (by norm_num))
theorem R36653 : Reach 36653 := rs (se 3 (by rfl) ⟨6872, by rfl⟩) (B 13745 (by norm_num) ⟨6872, by rfl⟩ (by norm_num))
theorem R36657 : Reach 36657 := rs (se 2 (by rfl) ⟨13746, by rfl⟩) (B 27493 (by norm_num) ⟨13746, by rfl⟩ (by norm_num))
theorem R102197 : Reach 102197 := rs (se 5 (by rfl) ⟨4790, by rfl⟩) (B 9581 (by norm_num) ⟨4790, by rfl⟩ (by norm_num))
theorem R36661 : Reach 36661 := rs (se 5 (by rfl) ⟨1718, by rfl⟩) (B 3437 (by norm_num) ⟨1718, by rfl⟩ (by norm_num))
theorem R36665 : Reach 36665 := rs (se 2 (by rfl) ⟨13749, by rfl⟩) (B 27499 (by norm_num) ⟨13749, by rfl⟩ (by norm_num))
theorem R69437 : Reach 69437 := rs (se 3 (by rfl) ⟨13019, by rfl⟩) (B 26039 (by norm_num) ⟨13019, by rfl⟩ (by norm_num))
theorem R36669 : Reach 36669 := rs (se 3 (by rfl) ⟨6875, by rfl⟩) (B 13751 (by norm_num) ⟨6875, by rfl⟩ (by norm_num))
theorem R36673 : Reach 36673 := rs (se 2 (by rfl) ⟨13752, by rfl⟩) (B 27505 (by norm_num) ⟨13752, by rfl⟩ (by norm_num))
theorem R36677 : Reach 36677 := rs (se 4 (by rfl) ⟨3438, by rfl⟩) (B 6877 (by norm_num) ⟨3438, by rfl⟩ (by norm_num))
theorem R36681 : Reach 36681 := rs (se 2 (by rfl) ⟨13755, by rfl⟩) (B 27511 (by norm_num) ⟨13755, by rfl⟩ (by norm_num))
theorem R36685 : Reach 36685 := rs (se 3 (by rfl) ⟨6878, by rfl⟩) (B 13757 (by norm_num) ⟨6878, by rfl⟩ (by norm_num))
theorem R36689 : Reach 36689 := rs (se 2 (by rfl) ⟨13758, by rfl⟩) (B 27517 (by norm_num) ⟨13758, by rfl⟩ (by norm_num))
theorem R36693 : Reach 36693 := rs (se 9 (by rfl) ⟨107, by rfl⟩) (B 215 (by norm_num) ⟨107, by rfl⟩ (by norm_num))
theorem R36697 : Reach 36697 := rs (se 2 (by rfl) ⟨13761, by rfl⟩) (B 27523 (by norm_num) ⟨13761, by rfl⟩ (by norm_num))
theorem R36701 : Reach 36701 := rs (se 3 (by rfl) ⟨6881, by rfl⟩) (B 13763 (by norm_num) ⟨6881, by rfl⟩ (by norm_num))
theorem R36705 : Reach 36705 := rs (se 2 (by rfl) ⟨13764, by rfl⟩) (B 27529 (by norm_num) ⟨13764, by rfl⟩ (by norm_num))
theorem R36709 : Reach 36709 := rs (se 4 (by rfl) ⟨3441, by rfl⟩) (B 6883 (by norm_num) ⟨3441, by rfl⟩ (by norm_num))
theorem R36713 : Reach 36713 := rs (se 2 (by rfl) ⟨13767, by rfl⟩) (B 27535 (by norm_num) ⟨13767, by rfl⟩ (by norm_num))
theorem R36717 : Reach 36717 := rs (se 3 (by rfl) ⟨6884, by rfl⟩) (B 13769 (by norm_num) ⟨6884, by rfl⟩ (by norm_num))
theorem R36721 : Reach 36721 := rs (se 2 (by rfl) ⟨13770, by rfl⟩) (B 27541 (by norm_num) ⟨13770, by rfl⟩ (by norm_num))
theorem R36725 : Reach 36725 := rs (se 5 (by rfl) ⟨1721, by rfl⟩) (B 3443 (by norm_num) ⟨1721, by rfl⟩ (by norm_num))
theorem R36729 : Reach 36729 := rs (se 2 (by rfl) ⟨13773, by rfl⟩) (B 27547 (by norm_num) ⟨13773, by rfl⟩ (by norm_num))
theorem R36733 : Reach 36733 := rs (se 3 (by rfl) ⟨6887, by rfl⟩) (B 13775 (by norm_num) ⟨6887, by rfl⟩ (by norm_num))
theorem R36737 : Reach 36737 := rs (se 2 (by rfl) ⟨13776, by rfl⟩) (B 27553 (by norm_num) ⟨13776, by rfl⟩ (by norm_num))
theorem R36741 : Reach 36741 := rs (se 4 (by rfl) ⟨3444, by rfl⟩) (B 6889 (by norm_num) ⟨3444, by rfl⟩ (by norm_num))
theorem R36745 : Reach 36745 := rs (se 2 (by rfl) ⟨13779, by rfl⟩) (B 27559 (by norm_num) ⟨13779, by rfl⟩ (by norm_num))
theorem R36749 : Reach 36749 := rs (se 3 (by rfl) ⟨6890, by rfl⟩) (B 13781 (by norm_num) ⟨6890, by rfl⟩ (by norm_num))
theorem R36753 : Reach 36753 := rs (se 2 (by rfl) ⟨13782, by rfl⟩) (B 27565 (by norm_num) ⟨13782, by rfl⟩ (by norm_num))
theorem R36757 : Reach 36757 := rs (se 6 (by rfl) ⟨861, by rfl⟩) (B 1723 (by norm_num) ⟨861, by rfl⟩ (by norm_num))
theorem R36761 : Reach 36761 := rs (se 2 (by rfl) ⟨13785, by rfl⟩) (B 27571 (by norm_num) ⟨13785, by rfl⟩ (by norm_num))
theorem R36765 : Reach 36765 := rs (se 3 (by rfl) ⟨6893, by rfl⟩) (B 13787 (by norm_num) ⟨6893, by rfl⟩ (by norm_num))
theorem R36769 : Reach 36769 := rs (se 2 (by rfl) ⟨13788, by rfl⟩) (B 27577 (by norm_num) ⟨13788, by rfl⟩ (by norm_num))
theorem R36773 : Reach 36773 := rs (se 4 (by rfl) ⟨3447, by rfl⟩) (B 6895 (by norm_num) ⟨3447, by rfl⟩ (by norm_num))
theorem R36777 : Reach 36777 := rs (se 2 (by rfl) ⟨13791, by rfl⟩) (B 27583 (by norm_num) ⟨13791, by rfl⟩ (by norm_num))
theorem R36781 : Reach 36781 := rs (se 3 (by rfl) ⟨6896, by rfl⟩) (B 13793 (by norm_num) ⟨6896, by rfl⟩ (by norm_num))
theorem R36785 : Reach 36785 := rs (se 2 (by rfl) ⟨13794, by rfl⟩) (B 27589 (by norm_num) ⟨13794, by rfl⟩ (by norm_num))
theorem R36789 : Reach 36789 := rs (se 5 (by rfl) ⟨1724, by rfl⟩) (B 3449 (by norm_num) ⟨1724, by rfl⟩ (by norm_num))
theorem R36793 : Reach 36793 := rs (se 2 (by rfl) ⟨13797, by rfl⟩) (B 27595 (by norm_num) ⟨13797, by rfl⟩ (by norm_num))
theorem R36797 : Reach 36797 := rs (se 3 (by rfl) ⟨6899, by rfl⟩) (B 13799 (by norm_num) ⟨6899, by rfl⟩ (by norm_num))
theorem R36801 : Reach 36801 := rs (se 2 (by rfl) ⟨13800, by rfl⟩) (B 27601 (by norm_num) ⟨13800, by rfl⟩ (by norm_num))
theorem R36805 : Reach 36805 := rs (se 4 (by rfl) ⟨3450, by rfl⟩) (B 6901 (by norm_num) ⟨3450, by rfl⟩ (by norm_num))
theorem R36809 : Reach 36809 := rs (se 2 (by rfl) ⟨13803, by rfl⟩) (B 27607 (by norm_num) ⟨13803, by rfl⟩ (by norm_num))
theorem R36813 : Reach 36813 := rs (se 3 (by rfl) ⟨6902, by rfl⟩) (B 13805 (by norm_num) ⟨6902, by rfl⟩ (by norm_num))
theorem R36817 : Reach 36817 := rs (se 2 (by rfl) ⟨13806, by rfl⟩) (B 27613 (by norm_num) ⟨13806, by rfl⟩ (by norm_num))
theorem R69589 : Reach 69589 := rs (se 7 (by rfl) ⟨815, by rfl⟩) (B 1631 (by norm_num) ⟨815, by rfl⟩ (by norm_num))
theorem R36821 : Reach 36821 := rs (se 7 (by rfl) ⟨431, by rfl⟩) (B 863 (by norm_num) ⟨431, by rfl⟩ (by norm_num))
theorem R36825 : Reach 36825 := rs (se 2 (by rfl) ⟨13809, by rfl⟩) (B 27619 (by norm_num) ⟨13809, by rfl⟩ (by norm_num))
theorem R36829 : Reach 36829 := rs (se 3 (by rfl) ⟨6905, by rfl⟩) (B 13811 (by norm_num) ⟨6905, by rfl⟩ (by norm_num))
theorem R36833 : Reach 36833 := rs (se 2 (by rfl) ⟨13812, by rfl⟩) (B 27625 (by norm_num) ⟨13812, by rfl⟩ (by norm_num))
theorem R36837 : Reach 36837 := rs (se 4 (by rfl) ⟨3453, by rfl⟩) (B 6907 (by norm_num) ⟨3453, by rfl⟩ (by norm_num))
theorem R36841 : Reach 36841 := rs (se 2 (by rfl) ⟨13815, by rfl⟩) (B 27631 (by norm_num) ⟨13815, by rfl⟩ (by norm_num))
theorem R36845 : Reach 36845 := rs (se 3 (by rfl) ⟨6908, by rfl⟩) (B 13817 (by norm_num) ⟨6908, by rfl⟩ (by norm_num))
theorem R36849 : Reach 36849 := rs (se 2 (by rfl) ⟨13818, by rfl⟩) (B 27637 (by norm_num) ⟨13818, by rfl⟩ (by norm_num))
theorem R36853 : Reach 36853 := rs (se 5 (by rfl) ⟨1727, by rfl⟩) (B 3455 (by norm_num) ⟨1727, by rfl⟩ (by norm_num))
theorem R36857 : Reach 36857 := rs (se 2 (by rfl) ⟨13821, by rfl⟩) (B 27643 (by norm_num) ⟨13821, by rfl⟩ (by norm_num))
theorem R36861 : Reach 36861 := rs (se 3 (by rfl) ⟨6911, by rfl⟩) (B 13823 (by norm_num) ⟨6911, by rfl⟩ (by norm_num))
theorem R36865 : Reach 36865 := rs (se 2 (by rfl) ⟨13824, by rfl⟩) (B 27649 (by norm_num) ⟨13824, by rfl⟩ (by norm_num))
theorem R36869 : Reach 36869 := rs (se 4 (by rfl) ⟨3456, by rfl⟩) (B 6913 (by norm_num) ⟨3456, by rfl⟩ (by norm_num))
theorem R36873 : Reach 36873 := rs (se 2 (by rfl) ⟨13827, by rfl⟩) (B 27655 (by norm_num) ⟨13827, by rfl⟩ (by norm_num))
theorem R36877 : Reach 36877 := rs (se 3 (by rfl) ⟨6914, by rfl⟩) (B 13829 (by norm_num) ⟨6914, by rfl⟩ (by norm_num))
theorem R36881 : Reach 36881 := rs (se 2 (by rfl) ⟨13830, by rfl⟩) (B 27661 (by norm_num) ⟨13830, by rfl⟩ (by norm_num))
theorem R36885 : Reach 36885 := rs (se 6 (by rfl) ⟨864, by rfl⟩) (B 1729 (by norm_num) ⟨864, by rfl⟩ (by norm_num))
theorem R36889 : Reach 36889 := rs (se 2 (by rfl) ⟨13833, by rfl⟩) (B 27667 (by norm_num) ⟨13833, by rfl⟩ (by norm_num))
theorem R36893 : Reach 36893 := rs (se 3 (by rfl) ⟨6917, by rfl⟩) (B 13835 (by norm_num) ⟨6917, by rfl⟩ (by norm_num))
theorem R36897 : Reach 36897 := rs (se 2 (by rfl) ⟨13836, by rfl⟩) (B 27673 (by norm_num) ⟨13836, by rfl⟩ (by norm_num))
theorem R36901 : Reach 36901 := rs (se 4 (by rfl) ⟨3459, by rfl⟩) (B 6919 (by norm_num) ⟨3459, by rfl⟩ (by norm_num))
theorem R36905 : Reach 36905 := rs (se 2 (by rfl) ⟨13839, by rfl⟩) (B 27679 (by norm_num) ⟨13839, by rfl⟩ (by norm_num))
theorem R36909 : Reach 36909 := rs (se 3 (by rfl) ⟨6920, by rfl⟩) (B 13841 (by norm_num) ⟨6920, by rfl⟩ (by norm_num))
theorem R36913 : Reach 36913 := rs (se 2 (by rfl) ⟨13842, by rfl⟩) (B 27685 (by norm_num) ⟨13842, by rfl⟩ (by norm_num))
theorem R36917 : Reach 36917 := rs (se 5 (by rfl) ⟨1730, by rfl⟩) (B 3461 (by norm_num) ⟨1730, by rfl⟩ (by norm_num))
theorem R36921 : Reach 36921 := rs (se 2 (by rfl) ⟨13845, by rfl⟩) (B 27691 (by norm_num) ⟨13845, by rfl⟩ (by norm_num))
theorem R36925 : Reach 36925 := rs (se 3 (by rfl) ⟨6923, by rfl⟩) (B 13847 (by norm_num) ⟨6923, by rfl⟩ (by norm_num))
theorem R36929 : Reach 36929 := rs (se 2 (by rfl) ⟨13848, by rfl⟩) (B 27697 (by norm_num) ⟨13848, by rfl⟩ (by norm_num))
theorem R36933 : Reach 36933 := rs (se 4 (by rfl) ⟨3462, by rfl⟩) (B 6925 (by norm_num) ⟨3462, by rfl⟩ (by norm_num))
theorem R36937 : Reach 36937 := rs (se 2 (by rfl) ⟨13851, by rfl⟩) (B 27703 (by norm_num) ⟨13851, by rfl⟩ (by norm_num))
theorem R36941 : Reach 36941 := rs (se 3 (by rfl) ⟨6926, by rfl⟩) (B 13853 (by norm_num) ⟨6926, by rfl⟩ (by norm_num))
theorem R36945 : Reach 36945 := rs (se 2 (by rfl) ⟨13854, by rfl⟩) (B 27709 (by norm_num) ⟨13854, by rfl⟩ (by norm_num))
theorem R36949 : Reach 36949 := rs (se 8 (by rfl) ⟨216, by rfl⟩) (B 433 (by norm_num) ⟨216, by rfl⟩ (by norm_num))
theorem R36953 : Reach 36953 := rs (se 2 (by rfl) ⟨13857, by rfl⟩) (B 27715 (by norm_num) ⟨13857, by rfl⟩ (by norm_num))
theorem R36957 : Reach 36957 := rs (se 3 (by rfl) ⟨6929, by rfl⟩) (B 13859 (by norm_num) ⟨6929, by rfl⟩ (by norm_num))
theorem R36961 : Reach 36961 := rs (se 2 (by rfl) ⟨13860, by rfl⟩) (B 27721 (by norm_num) ⟨13860, by rfl⟩ (by norm_num))
theorem R36965 : Reach 36965 := rs (se 4 (by rfl) ⟨3465, by rfl⟩) (B 6931 (by norm_num) ⟨3465, by rfl⟩ (by norm_num))
theorem R36969 : Reach 36969 := rs (se 2 (by rfl) ⟨13863, by rfl⟩) (B 27727 (by norm_num) ⟨13863, by rfl⟩ (by norm_num))
theorem R36973 : Reach 36973 := rs (se 3 (by rfl) ⟨6932, by rfl⟩) (B 13865 (by norm_num) ⟨6932, by rfl⟩ (by norm_num))
theorem R36977 : Reach 36977 := rs (se 2 (by rfl) ⟨13866, by rfl⟩) (B 27733 (by norm_num) ⟨13866, by rfl⟩ (by norm_num))
theorem R36981 : Reach 36981 := rs (se 5 (by rfl) ⟨1733, by rfl⟩) (B 3467 (by norm_num) ⟨1733, by rfl⟩ (by norm_num))
theorem R36985 : Reach 36985 := rs (se 2 (by rfl) ⟨13869, by rfl⟩) (B 27739 (by norm_num) ⟨13869, by rfl⟩ (by norm_num))
theorem R36989 : Reach 36989 := rs (se 3 (by rfl) ⟨6935, by rfl⟩) (B 13871 (by norm_num) ⟨6935, by rfl⟩ (by norm_num))
theorem R36993 : Reach 36993 := rs (se 2 (by rfl) ⟨13872, by rfl⟩) (B 27745 (by norm_num) ⟨13872, by rfl⟩ (by norm_num))
theorem R36997 : Reach 36997 := rs (se 4 (by rfl) ⟨3468, by rfl⟩) (B 6937 (by norm_num) ⟨3468, by rfl⟩ (by norm_num))
theorem R37001 : Reach 37001 := rs (se 2 (by rfl) ⟨13875, by rfl⟩) (B 27751 (by norm_num) ⟨13875, by rfl⟩ (by norm_num))
theorem R37005 : Reach 37005 := rs (se 3 (by rfl) ⟨6938, by rfl⟩) (B 13877 (by norm_num) ⟨6938, by rfl⟩ (by norm_num))
theorem R37009 : Reach 37009 := rs (se 2 (by rfl) ⟨13878, by rfl⟩) (B 27757 (by norm_num) ⟨13878, by rfl⟩ (by norm_num))
theorem R37013 : Reach 37013 := rs (se 6 (by rfl) ⟨867, by rfl⟩) (B 1735 (by norm_num) ⟨867, by rfl⟩ (by norm_num))
theorem R37017 : Reach 37017 := rs (se 2 (by rfl) ⟨13881, by rfl⟩) (B 27763 (by norm_num) ⟨13881, by rfl⟩ (by norm_num))
theorem R37021 : Reach 37021 := rs (se 3 (by rfl) ⟨6941, by rfl⟩) (B 13883 (by norm_num) ⟨6941, by rfl⟩ (by norm_num))
theorem R37025 : Reach 37025 := rs (se 2 (by rfl) ⟨13884, by rfl⟩) (B 27769 (by norm_num) ⟨13884, by rfl⟩ (by norm_num))
theorem R37029 : Reach 37029 := rs (se 4 (by rfl) ⟨3471, by rfl⟩) (B 6943 (by norm_num) ⟨3471, by rfl⟩ (by norm_num))
theorem R37033 : Reach 37033 := rs (se 2 (by rfl) ⟨13887, by rfl⟩) (B 27775 (by norm_num) ⟨13887, by rfl⟩ (by norm_num))
theorem R37037 : Reach 37037 := rs (se 3 (by rfl) ⟨6944, by rfl⟩) (B 13889 (by norm_num) ⟨6944, by rfl⟩ (by norm_num))
theorem R37041 : Reach 37041 := rs (se 2 (by rfl) ⟨13890, by rfl⟩) (B 27781 (by norm_num) ⟨13890, by rfl⟩ (by norm_num))
theorem R37045 : Reach 37045 := rs (se 5 (by rfl) ⟨1736, by rfl⟩) (B 3473 (by norm_num) ⟨1736, by rfl⟩ (by norm_num))
theorem R37049 : Reach 37049 := rs (se 2 (by rfl) ⟨13893, by rfl⟩) (B 27787 (by norm_num) ⟨13893, by rfl⟩ (by norm_num))
theorem R37053 : Reach 37053 := rs (se 3 (by rfl) ⟨6947, by rfl⟩) (B 13895 (by norm_num) ⟨6947, by rfl⟩ (by norm_num))
theorem R37057 : Reach 37057 := rs (se 2 (by rfl) ⟨13896, by rfl⟩) (B 27793 (by norm_num) ⟨13896, by rfl⟩ (by norm_num))
theorem R37061 : Reach 37061 := rs (se 4 (by rfl) ⟨3474, by rfl⟩) (B 6949 (by norm_num) ⟨3474, by rfl⟩ (by norm_num))
theorem R37065 : Reach 37065 := rs (se 2 (by rfl) ⟨13899, by rfl⟩) (B 27799 (by norm_num) ⟨13899, by rfl⟩ (by norm_num))
theorem R37069 : Reach 37069 := rs (se 3 (by rfl) ⟨6950, by rfl⟩) (B 13901 (by norm_num) ⟨6950, by rfl⟩ (by norm_num))
theorem R37073 : Reach 37073 := rs (se 2 (by rfl) ⟨13902, by rfl⟩) (B 27805 (by norm_num) ⟨13902, by rfl⟩ (by norm_num))
theorem R37077 : Reach 37077 := rs (se 7 (by rfl) ⟨434, by rfl⟩) (B 869 (by norm_num) ⟨434, by rfl⟩ (by norm_num))
theorem R37081 : Reach 37081 := rs (se 2 (by rfl) ⟨13905, by rfl⟩) (B 27811 (by norm_num) ⟨13905, by rfl⟩ (by norm_num))
theorem R37085 : Reach 37085 := rs (se 3 (by rfl) ⟨6953, by rfl⟩) (B 13907 (by norm_num) ⟨6953, by rfl⟩ (by norm_num))
theorem R37089 : Reach 37089 := rs (se 2 (by rfl) ⟨13908, by rfl⟩) (B 27817 (by norm_num) ⟨13908, by rfl⟩ (by norm_num))
theorem R37093 : Reach 37093 := rs (se 4 (by rfl) ⟨3477, by rfl⟩) (B 6955 (by norm_num) ⟨3477, by rfl⟩ (by norm_num))
theorem R37097 : Reach 37097 := rs (se 2 (by rfl) ⟨13911, by rfl⟩) (B 27823 (by norm_num) ⟨13911, by rfl⟩ (by norm_num))
theorem R37101 : Reach 37101 := rs (se 3 (by rfl) ⟨6956, by rfl⟩) (B 13913 (by norm_num) ⟨6956, by rfl⟩ (by norm_num))
theorem R37105 : Reach 37105 := rs (se 2 (by rfl) ⟨13914, by rfl⟩) (B 27829 (by norm_num) ⟨13914, by rfl⟩ (by norm_num))
theorem R37109 : Reach 37109 := rs (se 5 (by rfl) ⟨1739, by rfl⟩) (B 3479 (by norm_num) ⟨1739, by rfl⟩ (by norm_num))
theorem R37113 : Reach 37113 := rs (se 2 (by rfl) ⟨13917, by rfl⟩) (B 27835 (by norm_num) ⟨13917, by rfl⟩ (by norm_num))
theorem R37117 : Reach 37117 := rs (se 3 (by rfl) ⟨6959, by rfl⟩) (B 13919 (by norm_num) ⟨6959, by rfl⟩ (by norm_num))
theorem R37121 : Reach 37121 := rs (se 2 (by rfl) ⟨13920, by rfl⟩) (B 27841 (by norm_num) ⟨13920, by rfl⟩ (by norm_num))
theorem R69893 : Reach 69893 := rs (se 4 (by rfl) ⟨6552, by rfl⟩) (B 13105 (by norm_num) ⟨6552, by rfl⟩ (by norm_num))
theorem R37125 : Reach 37125 := rs (se 4 (by rfl) ⟨3480, by rfl⟩) (B 6961 (by norm_num) ⟨3480, by rfl⟩ (by norm_num))
theorem R37129 : Reach 37129 := rs (se 2 (by rfl) ⟨13923, by rfl⟩) (B 27847 (by norm_num) ⟨13923, by rfl⟩ (by norm_num))
theorem R37133 : Reach 37133 := rs (se 3 (by rfl) ⟨6962, by rfl⟩) (B 13925 (by norm_num) ⟨6962, by rfl⟩ (by norm_num))
theorem R37137 : Reach 37137 := rs (se 2 (by rfl) ⟨13926, by rfl⟩) (B 27853 (by norm_num) ⟨13926, by rfl⟩ (by norm_num))
theorem R37141 : Reach 37141 := rs (se 6 (by rfl) ⟨870, by rfl⟩) (B 1741 (by norm_num) ⟨870, by rfl⟩ (by norm_num))
theorem R299285 : Reach 299285 := rs (se 6 (by rfl) ⟨7014, by rfl⟩) (B 14029 (by norm_num) ⟨7014, by rfl⟩ (by norm_num))
theorem R37145 : Reach 37145 := rs (se 2 (by rfl) ⟨13929, by rfl⟩) (B 27859 (by norm_num) ⟨13929, by rfl⟩ (by norm_num))
theorem R37149 : Reach 37149 := rs (se 3 (by rfl) ⟨6965, by rfl⟩) (B 13931 (by norm_num) ⟨6965, by rfl⟩ (by norm_num))
theorem R37153 : Reach 37153 := rs (se 2 (by rfl) ⟨13932, by rfl⟩) (B 27865 (by norm_num) ⟨13932, by rfl⟩ (by norm_num))
theorem R69925 : Reach 69925 := rs (se 4 (by rfl) ⟨6555, by rfl⟩) (B 13111 (by norm_num) ⟨6555, by rfl⟩ (by norm_num))
theorem R37157 : Reach 37157 := rs (se 4 (by rfl) ⟨3483, by rfl⟩) (B 6967 (by norm_num) ⟨3483, by rfl⟩ (by norm_num))
theorem R37161 : Reach 37161 := rs (se 2 (by rfl) ⟨13935, by rfl⟩) (B 27871 (by norm_num) ⟨13935, by rfl⟩ (by norm_num))
theorem R37165 : Reach 37165 := rs (se 3 (by rfl) ⟨6968, by rfl⟩) (B 13937 (by norm_num) ⟨6968, by rfl⟩ (by norm_num))
theorem R37169 : Reach 37169 := rs (se 2 (by rfl) ⟨13938, by rfl⟩) (B 27877 (by norm_num) ⟨13938, by rfl⟩ (by norm_num))
theorem R37173 : Reach 37173 := rs (se 5 (by rfl) ⟨1742, by rfl⟩) (B 3485 (by norm_num) ⟨1742, by rfl⟩ (by norm_num))
theorem R37177 : Reach 37177 := rs (se 2 (by rfl) ⟨13941, by rfl⟩) (B 27883 (by norm_num) ⟨13941, by rfl⟩ (by norm_num))
theorem R37181 : Reach 37181 := rs (se 3 (by rfl) ⟨6971, by rfl⟩) (B 13943 (by norm_num) ⟨6971, by rfl⟩ (by norm_num))
theorem R37185 : Reach 37185 := rs (se 2 (by rfl) ⟨13944, by rfl⟩) (B 27889 (by norm_num) ⟨13944, by rfl⟩ (by norm_num))
theorem R37189 : Reach 37189 := rs (se 4 (by rfl) ⟨3486, by rfl⟩) (B 6973 (by norm_num) ⟨3486, by rfl⟩ (by norm_num))
theorem R37193 : Reach 37193 := rs (se 2 (by rfl) ⟨13947, by rfl⟩) (B 27895 (by norm_num) ⟨13947, by rfl⟩ (by norm_num))
theorem R37197 : Reach 37197 := rs (se 3 (by rfl) ⟨6974, by rfl⟩) (B 13949 (by norm_num) ⟨6974, by rfl⟩ (by norm_num))
theorem R37201 : Reach 37201 := rs (se 2 (by rfl) ⟨13950, by rfl⟩) (B 27901 (by norm_num) ⟨13950, by rfl⟩ (by norm_num))
theorem R37205 : Reach 37205 := rs (se 10 (by rfl) ⟨54, by rfl⟩) (B 109 (by norm_num) ⟨54, by rfl⟩ (by norm_num))
theorem R37209 : Reach 37209 := rs (se 2 (by rfl) ⟨13953, by rfl⟩) (B 27907 (by norm_num) ⟨13953, by rfl⟩ (by norm_num))
theorem R37213 : Reach 37213 := rs (se 3 (by rfl) ⟨6977, by rfl⟩) (B 13955 (by norm_num) ⟨6977, by rfl⟩ (by norm_num))
theorem R37217 : Reach 37217 := rs (se 2 (by rfl) ⟨13956, by rfl⟩) (B 27913 (by norm_num) ⟨13956, by rfl⟩ (by norm_num))
theorem R37221 : Reach 37221 := rs (se 4 (by rfl) ⟨3489, by rfl⟩) (B 6979 (by norm_num) ⟨3489, by rfl⟩ (by norm_num))
theorem R37225 : Reach 37225 := rs (se 2 (by rfl) ⟨13959, by rfl⟩) (B 27919 (by norm_num) ⟨13959, by rfl⟩ (by norm_num))
theorem R37229 : Reach 37229 := rs (se 3 (by rfl) ⟨6980, by rfl⟩) (B 13961 (by norm_num) ⟨6980, by rfl⟩ (by norm_num))
theorem R37233 : Reach 37233 := rs (se 2 (by rfl) ⟨13962, by rfl⟩) (B 27925 (by norm_num) ⟨13962, by rfl⟩ (by norm_num))
theorem R37237 : Reach 37237 := rs (se 5 (by rfl) ⟨1745, by rfl⟩) (B 3491 (by norm_num) ⟨1745, by rfl⟩ (by norm_num))
theorem R37241 : Reach 37241 := rs (se 2 (by rfl) ⟨13965, by rfl⟩) (B 27931 (by norm_num) ⟨13965, by rfl⟩ (by norm_num))
theorem R37245 : Reach 37245 := rs (se 3 (by rfl) ⟨6983, by rfl⟩) (B 13967 (by norm_num) ⟨6983, by rfl⟩ (by norm_num))
theorem R37249 : Reach 37249 := rs (se 2 (by rfl) ⟨13968, by rfl⟩) (B 27937 (by norm_num) ⟨13968, by rfl⟩ (by norm_num))
theorem R37253 : Reach 37253 := rs (se 4 (by rfl) ⟨3492, by rfl⟩) (B 6985 (by norm_num) ⟨3492, by rfl⟩ (by norm_num))
theorem R37257 : Reach 37257 := rs (se 2 (by rfl) ⟨13971, by rfl⟩) (B 27943 (by norm_num) ⟨13971, by rfl⟩ (by norm_num))
theorem R37261 : Reach 37261 := rs (se 3 (by rfl) ⟨6986, by rfl⟩) (B 13973 (by norm_num) ⟨6986, by rfl⟩ (by norm_num))
theorem R37265 : Reach 37265 := rs (se 2 (by rfl) ⟨13974, by rfl⟩) (B 27949 (by norm_num) ⟨13974, by rfl⟩ (by norm_num))
theorem R37269 : Reach 37269 := rs (se 6 (by rfl) ⟨873, by rfl⟩) (B 1747 (by norm_num) ⟨873, by rfl⟩ (by norm_num))
theorem R37273 : Reach 37273 := rs (se 2 (by rfl) ⟨13977, by rfl⟩) (B 27955 (by norm_num) ⟨13977, by rfl⟩ (by norm_num))
theorem R37277 : Reach 37277 := rs (se 3 (by rfl) ⟨6989, by rfl⟩) (B 13979 (by norm_num) ⟨6989, by rfl⟩ (by norm_num))
theorem R37281 : Reach 37281 := rs (se 2 (by rfl) ⟨13980, by rfl⟩) (B 27961 (by norm_num) ⟨13980, by rfl⟩ (by norm_num))
theorem R37285 : Reach 37285 := rs (se 4 (by rfl) ⟨3495, by rfl⟩) (B 6991 (by norm_num) ⟨3495, by rfl⟩ (by norm_num))
theorem R37289 : Reach 37289 := rs (se 2 (by rfl) ⟨13983, by rfl⟩) (B 27967 (by norm_num) ⟨13983, by rfl⟩ (by norm_num))
theorem R37293 : Reach 37293 := rs (se 3 (by rfl) ⟨6992, by rfl⟩) (B 13985 (by norm_num) ⟨6992, by rfl⟩ (by norm_num))
theorem R37297 : Reach 37297 := rs (se 2 (by rfl) ⟨13986, by rfl⟩) (B 27973 (by norm_num) ⟨13986, by rfl⟩ (by norm_num))
theorem R37301 : Reach 37301 := rs (se 5 (by rfl) ⟨1748, by rfl⟩) (B 3497 (by norm_num) ⟨1748, by rfl⟩ (by norm_num))
theorem R37305 : Reach 37305 := rs (se 2 (by rfl) ⟨13989, by rfl⟩) (B 27979 (by norm_num) ⟨13989, by rfl⟩ (by norm_num))
theorem R37309 : Reach 37309 := rs (se 3 (by rfl) ⟨6995, by rfl⟩) (B 13991 (by norm_num) ⟨6995, by rfl⟩ (by norm_num))
theorem R37313 : Reach 37313 := rs (se 2 (by rfl) ⟨13992, by rfl⟩) (B 27985 (by norm_num) ⟨13992, by rfl⟩ (by norm_num))
theorem R37317 : Reach 37317 := rs (se 4 (by rfl) ⟨3498, by rfl⟩) (B 6997 (by norm_num) ⟨3498, by rfl⟩ (by norm_num))
theorem R37321 : Reach 37321 := rs (se 2 (by rfl) ⟨13995, by rfl⟩) (B 27991 (by norm_num) ⟨13995, by rfl⟩ (by norm_num))
theorem R37325 : Reach 37325 := rs (se 3 (by rfl) ⟨6998, by rfl⟩) (B 13997 (by norm_num) ⟨6998, by rfl⟩ (by norm_num))
theorem R37329 : Reach 37329 := rs (se 2 (by rfl) ⟨13998, by rfl⟩) (B 27997 (by norm_num) ⟨13998, by rfl⟩ (by norm_num))
theorem R233941 : Reach 233941 := rs (se 7 (by rfl) ⟨2741, by rfl⟩) (B 5483 (by norm_num) ⟨2741, by rfl⟩ (by norm_num))
theorem R37333 : Reach 37333 := rs (se 7 (by rfl) ⟨437, by rfl⟩) (B 875 (by norm_num) ⟨437, by rfl⟩ (by norm_num))
theorem R37337 : Reach 37337 := rs (se 2 (by rfl) ⟨14001, by rfl⟩) (B 28003 (by norm_num) ⟨14001, by rfl⟩ (by norm_num))
theorem R37341 : Reach 37341 := rs (se 3 (by rfl) ⟨7001, by rfl⟩) (B 14003 (by norm_num) ⟨7001, by rfl⟩ (by norm_num))
theorem R37345 : Reach 37345 := rs (se 2 (by rfl) ⟨14004, by rfl⟩) (B 28009 (by norm_num) ⟨14004, by rfl⟩ (by norm_num))
theorem R37349 : Reach 37349 := rs (se 4 (by rfl) ⟨3501, by rfl⟩) (B 7003 (by norm_num) ⟨3501, by rfl⟩ (by norm_num))
theorem R37353 : Reach 37353 := rs (se 2 (by rfl) ⟨14007, by rfl⟩) (B 28015 (by norm_num) ⟨14007, by rfl⟩ (by norm_num))
theorem R37357 : Reach 37357 := rs (se 3 (by rfl) ⟨7004, by rfl⟩) (B 14009 (by norm_num) ⟨7004, by rfl⟩ (by norm_num))
theorem R37361 : Reach 37361 := rs (se 2 (by rfl) ⟨14010, by rfl⟩) (B 28021 (by norm_num) ⟨14010, by rfl⟩ (by norm_num))
theorem R37365 : Reach 37365 := rs (se 5 (by rfl) ⟨1751, by rfl⟩) (B 3503 (by norm_num) ⟨1751, by rfl⟩ (by norm_num))
theorem R37369 : Reach 37369 := rs (se 2 (by rfl) ⟨14013, by rfl⟩) (B 28027 (by norm_num) ⟨14013, by rfl⟩ (by norm_num))
theorem R37373 : Reach 37373 := rs (se 3 (by rfl) ⟨7007, by rfl⟩) (B 14015 (by norm_num) ⟨7007, by rfl⟩ (by norm_num))
theorem R37377 : Reach 37377 := rs (se 2 (by rfl) ⟨14016, by rfl⟩) (B 28033 (by norm_num) ⟨14016, by rfl⟩ (by norm_num))
theorem R37381 : Reach 37381 := rs (se 4 (by rfl) ⟨3504, by rfl⟩) (B 7009 (by norm_num) ⟨3504, by rfl⟩ (by norm_num))
theorem R37385 : Reach 37385 := rs (se 2 (by rfl) ⟨14019, by rfl⟩) (B 28039 (by norm_num) ⟨14019, by rfl⟩ (by norm_num))
theorem R37389 : Reach 37389 := rs (se 3 (by rfl) ⟨7010, by rfl⟩) (B 14021 (by norm_num) ⟨7010, by rfl⟩ (by norm_num))
theorem R37393 : Reach 37393 := rs (se 2 (by rfl) ⟨14022, by rfl⟩) (B 28045 (by norm_num) ⟨14022, by rfl⟩ (by norm_num))
theorem R135701 : Reach 135701 := rs (se 6 (by rfl) ⟨3180, by rfl⟩) (B 6361 (by norm_num) ⟨3180, by rfl⟩ (by norm_num))
theorem R37397 : Reach 37397 := rs (se 6 (by rfl) ⟨876, by rfl⟩) (B 1753 (by norm_num) ⟨876, by rfl⟩ (by norm_num))
theorem R37401 : Reach 37401 := rs (se 2 (by rfl) ⟨14025, by rfl⟩) (B 28051 (by norm_num) ⟨14025, by rfl⟩ (by norm_num))
theorem R37405 : Reach 37405 := rs (se 3 (by rfl) ⟨7013, by rfl⟩) (B 14027 (by norm_num) ⟨7013, by rfl⟩ (by norm_num))
theorem R37409 : Reach 37409 := rs (se 2 (by rfl) ⟨14028, by rfl⟩) (B 28057 (by norm_num) ⟨14028, by rfl⟩ (by norm_num))
theorem R37413 : Reach 37413 := rs (se 4 (by rfl) ⟨3507, by rfl⟩) (B 7015 (by norm_num) ⟨3507, by rfl⟩ (by norm_num))
theorem R37417 : Reach 37417 := rs (se 2 (by rfl) ⟨14031, by rfl⟩) (B 28063 (by norm_num) ⟨14031, by rfl⟩ (by norm_num))
theorem R37421 : Reach 37421 := rs (se 3 (by rfl) ⟨7016, by rfl⟩) (B 14033 (by norm_num) ⟨7016, by rfl⟩ (by norm_num))
theorem R37425 : Reach 37425 := rs (se 2 (by rfl) ⟨14034, by rfl⟩) (B 28069 (by norm_num) ⟨14034, by rfl⟩ (by norm_num))
theorem R37429 : Reach 37429 := rs (se 5 (by rfl) ⟨1754, by rfl⟩) (B 3509 (by norm_num) ⟨1754, by rfl⟩ (by norm_num))
theorem R37433 : Reach 37433 := rs (se 2 (by rfl) ⟨14037, by rfl⟩) (B 28075 (by norm_num) ⟨14037, by rfl⟩ (by norm_num))
theorem R37437 : Reach 37437 := rs (se 3 (by rfl) ⟨7019, by rfl⟩) (B 14039 (by norm_num) ⟨7019, by rfl⟩ (by norm_num))
theorem R37441 : Reach 37441 := rs (se 2 (by rfl) ⟨14040, by rfl⟩) (B 28081 (by norm_num) ⟨14040, by rfl⟩ (by norm_num))
theorem R37445 : Reach 37445 := rs (se 4 (by rfl) ⟨3510, by rfl⟩) (B 7021 (by norm_num) ⟨3510, by rfl⟩ (by norm_num))
theorem R37449 : Reach 37449 := rs (se 2 (by rfl) ⟨14043, by rfl⟩) (B 28087 (by norm_num) ⟨14043, by rfl⟩ (by norm_num))
theorem R37453 : Reach 37453 := rs (se 3 (by rfl) ⟨7022, by rfl⟩) (B 14045 (by norm_num) ⟨7022, by rfl⟩ (by norm_num))
theorem R37457 : Reach 37457 := rs (se 2 (by rfl) ⟨14046, by rfl⟩) (B 28093 (by norm_num) ⟨14046, by rfl⟩ (by norm_num))
theorem R37461 : Reach 37461 := rs (se 8 (by rfl) ⟨219, by rfl⟩) (B 439 (by norm_num) ⟨219, by rfl⟩ (by norm_num))
theorem R37465 : Reach 37465 := rs (se 2 (by rfl) ⟨14049, by rfl⟩) (B 28099 (by norm_num) ⟨14049, by rfl⟩ (by norm_num))
theorem R37469 : Reach 37469 := rs (se 3 (by rfl) ⟨7025, by rfl⟩) (B 14051 (by norm_num) ⟨7025, by rfl⟩ (by norm_num))
theorem R70237 : Reach 70237 := rs (se 3 (by rfl) ⟨13169, by rfl⟩) (B 26339 (by norm_num) ⟨13169, by rfl⟩ (by norm_num))
theorem R37473 : Reach 37473 := rs (se 2 (by rfl) ⟨14052, by rfl⟩) (B 28105 (by norm_num) ⟨14052, by rfl⟩ (by norm_num))
theorem R37477 : Reach 37477 := rs (se 4 (by rfl) ⟨3513, by rfl⟩) (B 7027 (by norm_num) ⟨3513, by rfl⟩ (by norm_num))
theorem R37481 : Reach 37481 := rs (se 2 (by rfl) ⟨14055, by rfl⟩) (B 28111 (by norm_num) ⟨14055, by rfl⟩ (by norm_num))
theorem R37485 : Reach 37485 := rs (se 3 (by rfl) ⟨7028, by rfl⟩) (B 14057 (by norm_num) ⟨7028, by rfl⟩ (by norm_num))
theorem R37489 : Reach 37489 := rs (se 2 (by rfl) ⟨14058, by rfl⟩) (B 28117 (by norm_num) ⟨14058, by rfl⟩ (by norm_num))
theorem R37493 : Reach 37493 := rs (se 5 (by rfl) ⟨1757, by rfl⟩) (B 3515 (by norm_num) ⟨1757, by rfl⟩ (by norm_num))
theorem R37497 : Reach 37497 := rs (se 2 (by rfl) ⟨14061, by rfl⟩) (B 28123 (by norm_num) ⟨14061, by rfl⟩ (by norm_num))
theorem R37501 : Reach 37501 := rs (se 3 (by rfl) ⟨7031, by rfl⟩) (B 14063 (by norm_num) ⟨7031, by rfl⟩ (by norm_num))
theorem R37505 : Reach 37505 := rs (se 2 (by rfl) ⟨14064, by rfl⟩) (B 28129 (by norm_num) ⟨14064, by rfl⟩ (by norm_num))
theorem R37509 : Reach 37509 := rs (se 4 (by rfl) ⟨3516, by rfl⟩) (B 7033 (by norm_num) ⟨3516, by rfl⟩ (by norm_num))
theorem R37513 : Reach 37513 := rs (se 2 (by rfl) ⟨14067, by rfl⟩) (B 28135 (by norm_num) ⟨14067, by rfl⟩ (by norm_num))
theorem R37517 : Reach 37517 := rs (se 3 (by rfl) ⟨7034, by rfl⟩) (B 14069 (by norm_num) ⟨7034, by rfl⟩ (by norm_num))
theorem R37521 : Reach 37521 := rs (se 2 (by rfl) ⟨14070, by rfl⟩) (B 28141 (by norm_num) ⟨14070, by rfl⟩ (by norm_num))
theorem R201365 : Reach 201365 := rs (se 6 (by rfl) ⟨4719, by rfl⟩) (B 9439 (by norm_num) ⟨4719, by rfl⟩ (by norm_num))
theorem R37525 : Reach 37525 := rs (se 6 (by rfl) ⟨879, by rfl⟩) (B 1759 (by norm_num) ⟨879, by rfl⟩ (by norm_num))
theorem R37529 : Reach 37529 := rs (se 2 (by rfl) ⟨14073, by rfl⟩) (B 28147 (by norm_num) ⟨14073, by rfl⟩ (by norm_num))
theorem R37533 : Reach 37533 := rs (se 3 (by rfl) ⟨7037, by rfl⟩) (B 14075 (by norm_num) ⟨7037, by rfl⟩ (by norm_num))
theorem R37537 : Reach 37537 := rs (se 2 (by rfl) ⟨14076, by rfl⟩) (B 28153 (by norm_num) ⟨14076, by rfl⟩ (by norm_num))
theorem R37541 : Reach 37541 := rs (se 4 (by rfl) ⟨3519, by rfl⟩) (B 7039 (by norm_num) ⟨3519, by rfl⟩ (by norm_num))
theorem R135845 : Reach 135845 := rs (se 4 (by rfl) ⟨12735, by rfl⟩) (B 25471 (by norm_num) ⟨12735, by rfl⟩ (by norm_num))
theorem R70309 : Reach 70309 := rs (se 4 (by rfl) ⟨6591, by rfl⟩) (B 13183 (by norm_num) ⟨6591, by rfl⟩ (by norm_num))
theorem R37545 : Reach 37545 := rs (se 2 (by rfl) ⟨14079, by rfl⟩) (B 28159 (by norm_num) ⟨14079, by rfl⟩ (by norm_num))
theorem R37549 : Reach 37549 := rs (se 3 (by rfl) ⟨7040, by rfl⟩) (B 14081 (by norm_num) ⟨7040, by rfl⟩ (by norm_num))
theorem R37553 : Reach 37553 := rs (se 2 (by rfl) ⟨14082, by rfl⟩) (B 28165 (by norm_num) ⟨14082, by rfl⟩ (by norm_num))
theorem R37557 : Reach 37557 := rs (se 5 (by rfl) ⟨1760, by rfl⟩) (B 3521 (by norm_num) ⟨1760, by rfl⟩ (by norm_num))
theorem R37561 : Reach 37561 := rs (se 2 (by rfl) ⟨14085, by rfl⟩) (B 28171 (by norm_num) ⟨14085, by rfl⟩ (by norm_num))
theorem R37565 : Reach 37565 := rs (se 3 (by rfl) ⟨7043, by rfl⟩) (B 14087 (by norm_num) ⟨7043, by rfl⟩ (by norm_num))
theorem R37569 : Reach 37569 := rs (se 2 (by rfl) ⟨14088, by rfl⟩) (B 28177 (by norm_num) ⟨14088, by rfl⟩ (by norm_num))
theorem R37573 : Reach 37573 := rs (se 4 (by rfl) ⟨3522, by rfl⟩) (B 7045 (by norm_num) ⟨3522, by rfl⟩ (by norm_num))
theorem R37577 : Reach 37577 := rs (se 2 (by rfl) ⟨14091, by rfl⟩) (B 28183 (by norm_num) ⟨14091, by rfl⟩ (by norm_num))
theorem R37581 : Reach 37581 := rs (se 3 (by rfl) ⟨7046, by rfl⟩) (B 14093 (by norm_num) ⟨7046, by rfl⟩ (by norm_num))
theorem R37585 : Reach 37585 := rs (se 2 (by rfl) ⟨14094, by rfl⟩) (B 28189 (by norm_num) ⟨14094, by rfl⟩ (by norm_num))
theorem R37589 : Reach 37589 := rs (se 7 (by rfl) ⟨440, by rfl⟩) (B 881 (by norm_num) ⟨440, by rfl⟩ (by norm_num))
theorem R37593 : Reach 37593 := rs (se 2 (by rfl) ⟨14097, by rfl⟩) (B 28195 (by norm_num) ⟨14097, by rfl⟩ (by norm_num))
theorem R37597 : Reach 37597 := rs (se 3 (by rfl) ⟨7049, by rfl⟩) (B 14099 (by norm_num) ⟨7049, by rfl⟩ (by norm_num))
theorem R37601 : Reach 37601 := rs (se 2 (by rfl) ⟨14100, by rfl⟩) (B 28201 (by norm_num) ⟨14100, by rfl⟩ (by norm_num))
theorem R37605 : Reach 37605 := rs (se 4 (by rfl) ⟨3525, by rfl⟩) (B 7051 (by norm_num) ⟨3525, by rfl⟩ (by norm_num))
theorem R37609 : Reach 37609 := rs (se 2 (by rfl) ⟨14103, by rfl⟩) (B 28207 (by norm_num) ⟨14103, by rfl⟩ (by norm_num))
theorem R37613 : Reach 37613 := rs (se 3 (by rfl) ⟨7052, by rfl⟩) (B 14105 (by norm_num) ⟨7052, by rfl⟩ (by norm_num))
theorem R37617 : Reach 37617 := rs (se 2 (by rfl) ⟨14106, by rfl⟩) (B 28213 (by norm_num) ⟨14106, by rfl⟩ (by norm_num))
theorem R37621 : Reach 37621 := rs (se 5 (by rfl) ⟨1763, by rfl⟩) (B 3527 (by norm_num) ⟨1763, by rfl⟩ (by norm_num))
theorem R37625 : Reach 37625 := rs (se 2 (by rfl) ⟨14109, by rfl⟩) (B 28219 (by norm_num) ⟨14109, by rfl⟩ (by norm_num))
theorem R37629 : Reach 37629 := rs (se 3 (by rfl) ⟨7055, by rfl⟩) (B 14111 (by norm_num) ⟨7055, by rfl⟩ (by norm_num))
theorem R37633 : Reach 37633 := rs (se 2 (by rfl) ⟨14112, by rfl⟩) (B 28225 (by norm_num) ⟨14112, by rfl⟩ (by norm_num))
theorem R37637 : Reach 37637 := rs (se 4 (by rfl) ⟨3528, by rfl⟩) (B 7057 (by norm_num) ⟨3528, by rfl⟩ (by norm_num))
theorem R37641 : Reach 37641 := rs (se 2 (by rfl) ⟨14115, by rfl⟩) (B 28231 (by norm_num) ⟨14115, by rfl⟩ (by norm_num))
theorem R37645 : Reach 37645 := rs (se 3 (by rfl) ⟨7058, by rfl⟩) (B 14117 (by norm_num) ⟨7058, by rfl⟩ (by norm_num))
theorem R37649 : Reach 37649 := rs (se 2 (by rfl) ⟨14118, by rfl⟩) (B 28237 (by norm_num) ⟨14118, by rfl⟩ (by norm_num))
theorem R37653 : Reach 37653 := rs (se 6 (by rfl) ⟨882, by rfl⟩) (B 1765 (by norm_num) ⟨882, by rfl⟩ (by norm_num))
theorem R37657 : Reach 37657 := rs (se 2 (by rfl) ⟨14121, by rfl⟩) (B 28243 (by norm_num) ⟨14121, by rfl⟩ (by norm_num))
theorem R37661 : Reach 37661 := rs (se 3 (by rfl) ⟨7061, by rfl⟩) (B 14123 (by norm_num) ⟨7061, by rfl⟩ (by norm_num))
theorem R37665 : Reach 37665 := rs (se 2 (by rfl) ⟨14124, by rfl⟩) (B 28249 (by norm_num) ⟨14124, by rfl⟩ (by norm_num))
theorem R37669 : Reach 37669 := rs (se 4 (by rfl) ⟨3531, by rfl⟩) (B 7063 (by norm_num) ⟨3531, by rfl⟩ (by norm_num))
theorem R37673 : Reach 37673 := rs (se 2 (by rfl) ⟨14127, by rfl⟩) (B 28255 (by norm_num) ⟨14127, by rfl⟩ (by norm_num))
theorem R37677 : Reach 37677 := rs (se 3 (by rfl) ⟨7064, by rfl⟩) (B 14129 (by norm_num) ⟨7064, by rfl⟩ (by norm_num))
theorem R37681 : Reach 37681 := rs (se 2 (by rfl) ⟨14130, by rfl⟩) (B 28261 (by norm_num) ⟨14130, by rfl⟩ (by norm_num))
theorem R135989 : Reach 135989 := rs (se 5 (by rfl) ⟨6374, by rfl⟩) (B 12749 (by norm_num) ⟨6374, by rfl⟩ (by norm_num))
theorem R37685 : Reach 37685 := rs (se 5 (by rfl) ⟨1766, by rfl⟩) (B 3533 (by norm_num) ⟨1766, by rfl⟩ (by norm_num))
theorem R37689 : Reach 37689 := rs (se 2 (by rfl) ⟨14133, by rfl⟩) (B 28267 (by norm_num) ⟨14133, by rfl⟩ (by norm_num))
theorem R37693 : Reach 37693 := rs (se 3 (by rfl) ⟨7067, by rfl⟩) (B 14135 (by norm_num) ⟨7067, by rfl⟩ (by norm_num))
theorem R37697 : Reach 37697 := rs (se 2 (by rfl) ⟨14136, by rfl⟩) (B 28273 (by norm_num) ⟨14136, by rfl⟩ (by norm_num))
theorem R37701 : Reach 37701 := rs (se 4 (by rfl) ⟨3534, by rfl⟩) (B 7069 (by norm_num) ⟨3534, by rfl⟩ (by norm_num))
theorem R37705 : Reach 37705 := rs (se 2 (by rfl) ⟨14139, by rfl⟩) (B 28279 (by norm_num) ⟨14139, by rfl⟩ (by norm_num))
theorem R37709 : Reach 37709 := rs (se 3 (by rfl) ⟨7070, by rfl⟩) (B 14141 (by norm_num) ⟨7070, by rfl⟩ (by norm_num))
theorem R37713 : Reach 37713 := rs (se 2 (by rfl) ⟨14142, by rfl⟩) (B 28285 (by norm_num) ⟨14142, by rfl⟩ (by norm_num))
theorem R37717 : Reach 37717 := rs (se 9 (by rfl) ⟨110, by rfl⟩) (B 221 (by norm_num) ⟨110, by rfl⟩ (by norm_num))
theorem R37721 : Reach 37721 := rs (se 2 (by rfl) ⟨14145, by rfl⟩) (B 28291 (by norm_num) ⟨14145, by rfl⟩ (by norm_num))
theorem R37725 : Reach 37725 := rs (se 3 (by rfl) ⟨7073, by rfl⟩) (B 14147 (by norm_num) ⟨7073, by rfl⟩ (by norm_num))
theorem R37729 : Reach 37729 := rs (se 2 (by rfl) ⟨14148, by rfl⟩) (B 28297 (by norm_num) ⟨14148, by rfl⟩ (by norm_num))
theorem R37733 : Reach 37733 := rs (se 4 (by rfl) ⟨3537, by rfl⟩) (B 7075 (by norm_num) ⟨3537, by rfl⟩ (by norm_num))
theorem R37737 : Reach 37737 := rs (se 2 (by rfl) ⟨14151, by rfl⟩) (B 28303 (by norm_num) ⟨14151, by rfl⟩ (by norm_num))
theorem R37741 : Reach 37741 := rs (se 3 (by rfl) ⟨7076, by rfl⟩) (B 14153 (by norm_num) ⟨7076, by rfl⟩ (by norm_num))
theorem R37745 : Reach 37745 := rs (se 2 (by rfl) ⟨14154, by rfl⟩) (B 28309 (by norm_num) ⟨14154, by rfl⟩ (by norm_num))
theorem R37749 : Reach 37749 := rs (se 5 (by rfl) ⟨1769, by rfl⟩) (B 3539 (by norm_num) ⟨1769, by rfl⟩ (by norm_num))
theorem R37753 : Reach 37753 := rs (se 2 (by rfl) ⟨14157, by rfl⟩) (B 28315 (by norm_num) ⟨14157, by rfl⟩ (by norm_num))
theorem R37757 : Reach 37757 := rs (se 3 (by rfl) ⟨7079, by rfl⟩) (B 14159 (by norm_num) ⟨7079, by rfl⟩ (by norm_num))
theorem R37761 : Reach 37761 := rs (se 2 (by rfl) ⟨14160, by rfl⟩) (B 28321 (by norm_num) ⟨14160, by rfl⟩ (by norm_num))
theorem R37765 : Reach 37765 := rs (se 4 (by rfl) ⟨3540, by rfl⟩) (B 7081 (by norm_num) ⟨3540, by rfl⟩ (by norm_num))
theorem R37769 : Reach 37769 := rs (se 2 (by rfl) ⟨14163, by rfl⟩) (B 28327 (by norm_num) ⟨14163, by rfl⟩ (by norm_num))
theorem R37773 : Reach 37773 := rs (se 3 (by rfl) ⟨7082, by rfl⟩) (B 14165 (by norm_num) ⟨7082, by rfl⟩ (by norm_num))
theorem R37777 : Reach 37777 := rs (se 2 (by rfl) ⟨14166, by rfl⟩) (B 28333 (by norm_num) ⟨14166, by rfl⟩ (by norm_num))
theorem R37781 : Reach 37781 := rs (se 6 (by rfl) ⟨885, by rfl⟩) (B 1771 (by norm_num) ⟨885, by rfl⟩ (by norm_num))
theorem R37785 : Reach 37785 := rs (se 2 (by rfl) ⟨14169, by rfl⟩) (B 28339 (by norm_num) ⟨14169, by rfl⟩ (by norm_num))
theorem R37789 : Reach 37789 := rs (se 3 (by rfl) ⟨7085, by rfl⟩) (B 14171 (by norm_num) ⟨7085, by rfl⟩ (by norm_num))
theorem R37793 : Reach 37793 := rs (se 2 (by rfl) ⟨14172, by rfl⟩) (B 28345 (by norm_num) ⟨14172, by rfl⟩ (by norm_num))
theorem R37797 : Reach 37797 := rs (se 4 (by rfl) ⟨3543, by rfl⟩) (B 7087 (by norm_num) ⟨3543, by rfl⟩ (by norm_num))
theorem R37801 : Reach 37801 := rs (se 2 (by rfl) ⟨14175, by rfl⟩) (B 28351 (by norm_num) ⟨14175, by rfl⟩ (by norm_num))
theorem R37805 : Reach 37805 := rs (se 3 (by rfl) ⟨7088, by rfl⟩) (B 14177 (by norm_num) ⟨7088, by rfl⟩ (by norm_num))
theorem R37809 : Reach 37809 := rs (se 2 (by rfl) ⟨14178, by rfl⟩) (B 28357 (by norm_num) ⟨14178, by rfl⟩ (by norm_num))
theorem R37813 : Reach 37813 := rs (se 5 (by rfl) ⟨1772, by rfl⟩) (B 3545 (by norm_num) ⟨1772, by rfl⟩ (by norm_num))
theorem R37817 : Reach 37817 := rs (se 2 (by rfl) ⟨14181, by rfl⟩) (B 28363 (by norm_num) ⟨14181, by rfl⟩ (by norm_num))
theorem R37821 : Reach 37821 := rs (se 3 (by rfl) ⟨7091, by rfl⟩) (B 14183 (by norm_num) ⟨7091, by rfl⟩ (by norm_num))
theorem R37825 : Reach 37825 := rs (se 2 (by rfl) ⟨14184, by rfl⟩) (B 28369 (by norm_num) ⟨14184, by rfl⟩ (by norm_num))
theorem R37829 : Reach 37829 := rs (se 4 (by rfl) ⟨3546, by rfl⟩) (B 7093 (by norm_num) ⟨3546, by rfl⟩ (by norm_num))
theorem R37833 : Reach 37833 := rs (se 2 (by rfl) ⟨14187, by rfl⟩) (B 28375 (by norm_num) ⟨14187, by rfl⟩ (by norm_num))
theorem R37837 : Reach 37837 := rs (se 3 (by rfl) ⟨7094, by rfl⟩) (B 14189 (by norm_num) ⟨7094, by rfl⟩ (by norm_num))
theorem R37841 : Reach 37841 := rs (se 2 (by rfl) ⟨14190, by rfl⟩) (B 28381 (by norm_num) ⟨14190, by rfl⟩ (by norm_num))
theorem R37845 : Reach 37845 := rs (se 7 (by rfl) ⟨443, by rfl⟩) (B 887 (by norm_num) ⟨443, by rfl⟩ (by norm_num))
theorem R37849 : Reach 37849 := rs (se 2 (by rfl) ⟨14193, by rfl⟩) (B 28387 (by norm_num) ⟨14193, by rfl⟩ (by norm_num))
theorem R37853 : Reach 37853 := rs (se 3 (by rfl) ⟨7097, by rfl⟩) (B 14195 (by norm_num) ⟨7097, by rfl⟩ (by norm_num))
theorem R37857 : Reach 37857 := rs (se 2 (by rfl) ⟨14196, by rfl⟩) (B 28393 (by norm_num) ⟨14196, by rfl⟩ (by norm_num))
theorem R37861 : Reach 37861 := rs (se 4 (by rfl) ⟨3549, by rfl⟩) (B 7099 (by norm_num) ⟨3549, by rfl⟩ (by norm_num))
theorem R37865 : Reach 37865 := rs (se 2 (by rfl) ⟨14199, by rfl⟩) (B 28399 (by norm_num) ⟨14199, by rfl⟩ (by norm_num))
theorem R37869 : Reach 37869 := rs (se 3 (by rfl) ⟨7100, by rfl⟩) (B 14201 (by norm_num) ⟨7100, by rfl⟩ (by norm_num))
theorem R37873 : Reach 37873 := rs (se 2 (by rfl) ⟨14202, by rfl⟩) (B 28405 (by norm_num) ⟨14202, by rfl⟩ (by norm_num))
theorem R37877 : Reach 37877 := rs (se 5 (by rfl) ⟨1775, by rfl⟩) (B 3551 (by norm_num) ⟨1775, by rfl⟩ (by norm_num))
theorem R70645 : Reach 70645 := rs (se 5 (by rfl) ⟨3311, by rfl⟩) (B 6623 (by norm_num) ⟨3311, by rfl⟩ (by norm_num))
theorem R37881 : Reach 37881 := rs (se 2 (by rfl) ⟨14205, by rfl⟩) (B 28411 (by norm_num) ⟨14205, by rfl⟩ (by norm_num))
theorem R37885 : Reach 37885 := rs (se 3 (by rfl) ⟨7103, by rfl⟩) (B 14207 (by norm_num) ⟨7103, by rfl⟩ (by norm_num))
theorem R37889 : Reach 37889 := rs (se 2 (by rfl) ⟨14208, by rfl⟩) (B 28417 (by norm_num) ⟨14208, by rfl⟩ (by norm_num))
theorem R37893 : Reach 37893 := rs (se 4 (by rfl) ⟨3552, by rfl⟩) (B 7105 (by norm_num) ⟨3552, by rfl⟩ (by norm_num))
theorem R37897 : Reach 37897 := rs (se 2 (by rfl) ⟨14211, by rfl⟩) (B 28423 (by norm_num) ⟨14211, by rfl⟩ (by norm_num))
theorem R37901 : Reach 37901 := rs (se 3 (by rfl) ⟨7106, by rfl⟩) (B 14213 (by norm_num) ⟨7106, by rfl⟩ (by norm_num))
theorem R37905 : Reach 37905 := rs (se 2 (by rfl) ⟨14214, by rfl⟩) (B 28429 (by norm_num) ⟨14214, by rfl⟩ (by norm_num))
theorem R37909 : Reach 37909 := rs (se 6 (by rfl) ⟨888, by rfl⟩) (B 1777 (by norm_num) ⟨888, by rfl⟩ (by norm_num))
theorem R37913 : Reach 37913 := rs (se 2 (by rfl) ⟨14217, by rfl⟩) (B 28435 (by norm_num) ⟨14217, by rfl⟩ (by norm_num))
theorem R37917 : Reach 37917 := rs (se 3 (by rfl) ⟨7109, by rfl⟩) (B 14219 (by norm_num) ⟨7109, by rfl⟩ (by norm_num))
theorem R37921 : Reach 37921 := rs (se 2 (by rfl) ⟨14220, by rfl⟩) (B 28441 (by norm_num) ⟨14220, by rfl⟩ (by norm_num))
theorem R37925 : Reach 37925 := rs (se 4 (by rfl) ⟨3555, by rfl⟩) (B 7111 (by norm_num) ⟨3555, by rfl⟩ (by norm_num))
theorem R37929 : Reach 37929 := rs (se 2 (by rfl) ⟨14223, by rfl⟩) (B 28447 (by norm_num) ⟨14223, by rfl⟩ (by norm_num))
theorem R37933 : Reach 37933 := rs (se 3 (by rfl) ⟨7112, by rfl⟩) (B 14225 (by norm_num) ⟨7112, by rfl⟩ (by norm_num))
theorem R37937 : Reach 37937 := rs (se 2 (by rfl) ⟨14226, by rfl⟩) (B 28453 (by norm_num) ⟨14226, by rfl⟩ (by norm_num))
theorem R37941 : Reach 37941 := rs (se 5 (by rfl) ⟨1778, by rfl⟩) (B 3557 (by norm_num) ⟨1778, by rfl⟩ (by norm_num))
theorem R37945 : Reach 37945 := rs (se 2 (by rfl) ⟨14229, by rfl⟩) (B 28459 (by norm_num) ⟨14229, by rfl⟩ (by norm_num))
theorem R37949 : Reach 37949 := rs (se 3 (by rfl) ⟨7115, by rfl⟩) (B 14231 (by norm_num) ⟨7115, by rfl⟩ (by norm_num))
theorem R37953 : Reach 37953 := rs (se 2 (by rfl) ⟨14232, by rfl⟩) (B 28465 (by norm_num) ⟨14232, by rfl⟩ (by norm_num))
theorem R37957 : Reach 37957 := rs (se 4 (by rfl) ⟨3558, by rfl⟩) (B 7117 (by norm_num) ⟨3558, by rfl⟩ (by norm_num))
theorem R37961 : Reach 37961 := rs (se 2 (by rfl) ⟨14235, by rfl⟩) (B 28471 (by norm_num) ⟨14235, by rfl⟩ (by norm_num))
theorem R37965 : Reach 37965 := rs (se 3 (by rfl) ⟨7118, by rfl⟩) (B 14237 (by norm_num) ⟨7118, by rfl⟩ (by norm_num))
theorem R37969 : Reach 37969 := rs (se 2 (by rfl) ⟨14238, by rfl⟩) (B 28477 (by norm_num) ⟨14238, by rfl⟩ (by norm_num))
theorem R37973 : Reach 37973 := rs (se 8 (by rfl) ⟨222, by rfl⟩) (B 445 (by norm_num) ⟨222, by rfl⟩ (by norm_num))
theorem R37977 : Reach 37977 := rs (se 2 (by rfl) ⟨14241, by rfl⟩) (B 28483 (by norm_num) ⟨14241, by rfl⟩ (by norm_num))
theorem R37981 : Reach 37981 := rs (se 3 (by rfl) ⟨7121, by rfl⟩) (B 14243 (by norm_num) ⟨7121, by rfl⟩ (by norm_num))
theorem R37985 : Reach 37985 := rs (se 2 (by rfl) ⟨14244, by rfl⟩) (B 28489 (by norm_num) ⟨14244, by rfl⟩ (by norm_num))
theorem R37989 : Reach 37989 := rs (se 4 (by rfl) ⟨3561, by rfl⟩) (B 7123 (by norm_num) ⟨3561, by rfl⟩ (by norm_num))
theorem R37993 : Reach 37993 := rs (se 2 (by rfl) ⟨14247, by rfl⟩) (B 28495 (by norm_num) ⟨14247, by rfl⟩ (by norm_num))
theorem R37997 : Reach 37997 := rs (se 3 (by rfl) ⟨7124, by rfl⟩) (B 14249 (by norm_num) ⟨7124, by rfl⟩ (by norm_num))
theorem R38001 : Reach 38001 := rs (se 2 (by rfl) ⟨14250, by rfl⟩) (B 28501 (by norm_num) ⟨14250, by rfl⟩ (by norm_num))
theorem R38005 : Reach 38005 := rs (se 5 (by rfl) ⟨1781, by rfl⟩) (B 3563 (by norm_num) ⟨1781, by rfl⟩ (by norm_num))
theorem R38009 : Reach 38009 := rs (se 2 (by rfl) ⟨14253, by rfl⟩) (B 28507 (by norm_num) ⟨14253, by rfl⟩ (by norm_num))
theorem R38013 : Reach 38013 := rs (se 3 (by rfl) ⟨7127, by rfl⟩) (B 14255 (by norm_num) ⟨7127, by rfl⟩ (by norm_num))
theorem R38017 : Reach 38017 := rs (se 2 (by rfl) ⟨14256, by rfl⟩) (B 28513 (by norm_num) ⟨14256, by rfl⟩ (by norm_num))
theorem R70789 : Reach 70789 := rs (se 4 (by rfl) ⟨6636, by rfl⟩) (B 13273 (by norm_num) ⟨6636, by rfl⟩ (by norm_num))
theorem R38021 : Reach 38021 := rs (se 4 (by rfl) ⟨3564, by rfl⟩) (B 7129 (by norm_num) ⟨3564, by rfl⟩ (by norm_num))
theorem R38025 : Reach 38025 := rs (se 2 (by rfl) ⟨14259, by rfl⟩) (B 28519 (by norm_num) ⟨14259, by rfl⟩ (by norm_num))
theorem R38029 : Reach 38029 := rs (se 3 (by rfl) ⟨7130, by rfl⟩) (B 14261 (by norm_num) ⟨7130, by rfl⟩ (by norm_num))
theorem R38033 : Reach 38033 := rs (se 2 (by rfl) ⟨14262, by rfl⟩) (B 28525 (by norm_num) ⟨14262, by rfl⟩ (by norm_num))
theorem R38037 : Reach 38037 := rs (se 6 (by rfl) ⟨891, by rfl⟩) (B 1783 (by norm_num) ⟨891, by rfl⟩ (by norm_num))
theorem R38041 : Reach 38041 := rs (se 2 (by rfl) ⟨14265, by rfl⟩) (B 28531 (by norm_num) ⟨14265, by rfl⟩ (by norm_num))
theorem R38045 : Reach 38045 := rs (se 3 (by rfl) ⟨7133, by rfl⟩) (B 14267 (by norm_num) ⟨7133, by rfl⟩ (by norm_num))
theorem R38049 : Reach 38049 := rs (se 2 (by rfl) ⟨14268, by rfl⟩) (B 28537 (by norm_num) ⟨14268, by rfl⟩ (by norm_num))
theorem R38053 : Reach 38053 := rs (se 4 (by rfl) ⟨3567, by rfl⟩) (B 7135 (by norm_num) ⟨3567, by rfl⟩ (by norm_num))
theorem R38057 : Reach 38057 := rs (se 2 (by rfl) ⟨14271, by rfl⟩) (B 28543 (by norm_num) ⟨14271, by rfl⟩ (by norm_num))
theorem R38061 : Reach 38061 := rs (se 3 (by rfl) ⟨7136, by rfl⟩) (B 14273 (by norm_num) ⟨7136, by rfl⟩ (by norm_num))
theorem R38065 : Reach 38065 := rs (se 2 (by rfl) ⟨14274, by rfl⟩) (B 28549 (by norm_num) ⟨14274, by rfl⟩ (by norm_num))
theorem R38069 : Reach 38069 := rs (se 5 (by rfl) ⟨1784, by rfl⟩) (B 3569 (by norm_num) ⟨1784, by rfl⟩ (by norm_num))
theorem R38073 : Reach 38073 := rs (se 2 (by rfl) ⟨14277, by rfl⟩) (B 28555 (by norm_num) ⟨14277, by rfl⟩ (by norm_num))
theorem R38077 : Reach 38077 := rs (se 3 (by rfl) ⟨7139, by rfl⟩) (B 14279 (by norm_num) ⟨7139, by rfl⟩ (by norm_num))
theorem R38081 : Reach 38081 := rs (se 2 (by rfl) ⟨14280, by rfl⟩) (B 28561 (by norm_num) ⟨14280, by rfl⟩ (by norm_num))
theorem R38085 : Reach 38085 := rs (se 4 (by rfl) ⟨3570, by rfl⟩) (B 7141 (by norm_num) ⟨3570, by rfl⟩ (by norm_num))
theorem R38089 : Reach 38089 := rs (se 2 (by rfl) ⟨14283, by rfl⟩) (B 28567 (by norm_num) ⟨14283, by rfl⟩ (by norm_num))
theorem R38093 : Reach 38093 := rs (se 3 (by rfl) ⟨7142, by rfl⟩) (B 14285 (by norm_num) ⟨7142, by rfl⟩ (by norm_num))
theorem R38097 : Reach 38097 := rs (se 2 (by rfl) ⟨14286, by rfl⟩) (B 28573 (by norm_num) ⟨14286, by rfl⟩ (by norm_num))
theorem R38101 : Reach 38101 := rs (se 7 (by rfl) ⟨446, by rfl⟩) (B 893 (by norm_num) ⟨446, by rfl⟩ (by norm_num))
theorem R38105 : Reach 38105 := rs (se 2 (by rfl) ⟨14289, by rfl⟩) (B 28579 (by norm_num) ⟨14289, by rfl⟩ (by norm_num))
theorem R38109 : Reach 38109 := rs (se 3 (by rfl) ⟨7145, by rfl⟩) (B 14291 (by norm_num) ⟨7145, by rfl⟩ (by norm_num))
theorem R38113 : Reach 38113 := rs (se 2 (by rfl) ⟨14292, by rfl⟩) (B 28585 (by norm_num) ⟨14292, by rfl⟩ (by norm_num))
theorem R38117 : Reach 38117 := rs (se 4 (by rfl) ⟨3573, by rfl⟩) (B 7147 (by norm_num) ⟨3573, by rfl⟩ (by norm_num))
theorem R38121 : Reach 38121 := rs (se 2 (by rfl) ⟨14295, by rfl⟩) (B 28591 (by norm_num) ⟨14295, by rfl⟩ (by norm_num))
theorem R38125 : Reach 38125 := rs (se 3 (by rfl) ⟨7148, by rfl⟩) (B 14297 (by norm_num) ⟨7148, by rfl⟩ (by norm_num))
theorem R38129 : Reach 38129 := rs (se 2 (by rfl) ⟨14298, by rfl⟩) (B 28597 (by norm_num) ⟨14298, by rfl⟩ (by norm_num))
theorem R38133 : Reach 38133 := rs (se 5 (by rfl) ⟨1787, by rfl⟩) (B 3575 (by norm_num) ⟨1787, by rfl⟩ (by norm_num))
theorem R38137 : Reach 38137 := rs (se 2 (by rfl) ⟨14301, by rfl⟩) (B 28603 (by norm_num) ⟨14301, by rfl⟩ (by norm_num))
theorem R38141 : Reach 38141 := rs (se 3 (by rfl) ⟨7151, by rfl⟩) (B 14303 (by norm_num) ⟨7151, by rfl⟩ (by norm_num))
theorem R38145 : Reach 38145 := rs (se 2 (by rfl) ⟨14304, by rfl⟩) (B 28609 (by norm_num) ⟨14304, by rfl⟩ (by norm_num))
theorem R38149 : Reach 38149 := rs (se 4 (by rfl) ⟨3576, by rfl⟩) (B 7153 (by norm_num) ⟨3576, by rfl⟩ (by norm_num))
theorem R38153 : Reach 38153 := rs (se 2 (by rfl) ⟨14307, by rfl⟩) (B 28615 (by norm_num) ⟨14307, by rfl⟩ (by norm_num))
theorem R38157 : Reach 38157 := rs (se 3 (by rfl) ⟨7154, by rfl⟩) (B 14309 (by norm_num) ⟨7154, by rfl⟩ (by norm_num))
theorem R38161 : Reach 38161 := rs (se 2 (by rfl) ⟨14310, by rfl⟩) (B 28621 (by norm_num) ⟨14310, by rfl⟩ (by norm_num))
theorem R38165 : Reach 38165 := rs (se 6 (by rfl) ⟨894, by rfl⟩) (B 1789 (by norm_num) ⟨894, by rfl⟩ (by norm_num))
theorem R38169 : Reach 38169 := rs (se 2 (by rfl) ⟨14313, by rfl⟩) (B 28627 (by norm_num) ⟨14313, by rfl⟩ (by norm_num))
theorem R38173 : Reach 38173 := rs (se 3 (by rfl) ⟨7157, by rfl⟩) (B 14315 (by norm_num) ⟨7157, by rfl⟩ (by norm_num))
theorem R38177 : Reach 38177 := rs (se 2 (by rfl) ⟨14316, by rfl⟩) (B 28633 (by norm_num) ⟨14316, by rfl⟩ (by norm_num))
theorem R70949 : Reach 70949 := rs (se 4 (by rfl) ⟨6651, by rfl⟩) (B 13303 (by norm_num) ⟨6651, by rfl⟩ (by norm_num))
theorem R38181 : Reach 38181 := rs (se 4 (by rfl) ⟨3579, by rfl⟩) (B 7159 (by norm_num) ⟨3579, by rfl⟩ (by norm_num))
theorem R38185 : Reach 38185 := rs (se 2 (by rfl) ⟨14319, by rfl⟩) (B 28639 (by norm_num) ⟨14319, by rfl⟩ (by norm_num))
theorem R38189 : Reach 38189 := rs (se 3 (by rfl) ⟨7160, by rfl⟩) (B 14321 (by norm_num) ⟨7160, by rfl⟩ (by norm_num))
theorem R38193 : Reach 38193 := rs (se 2 (by rfl) ⟨14322, by rfl⟩) (B 28645 (by norm_num) ⟨14322, by rfl⟩ (by norm_num))
theorem R38197 : Reach 38197 := rs (se 5 (by rfl) ⟨1790, by rfl⟩) (B 3581 (by norm_num) ⟨1790, by rfl⟩ (by norm_num))
theorem R38201 : Reach 38201 := rs (se 2 (by rfl) ⟨14325, by rfl⟩) (B 28651 (by norm_num) ⟨14325, by rfl⟩ (by norm_num))
theorem R38205 : Reach 38205 := rs (se 3 (by rfl) ⟨7163, by rfl⟩) (B 14327 (by norm_num) ⟨7163, by rfl⟩ (by norm_num))
theorem R38209 : Reach 38209 := rs (se 2 (by rfl) ⟨14328, by rfl⟩) (B 28657 (by norm_num) ⟨14328, by rfl⟩ (by norm_num))
theorem R38213 : Reach 38213 := rs (se 4 (by rfl) ⟨3582, by rfl⟩) (B 7165 (by norm_num) ⟨3582, by rfl⟩ (by norm_num))
theorem R38217 : Reach 38217 := rs (se 2 (by rfl) ⟨14331, by rfl⟩) (B 28663 (by norm_num) ⟨14331, by rfl⟩ (by norm_num))
theorem R38221 : Reach 38221 := rs (se 3 (by rfl) ⟨7166, by rfl⟩) (B 14333 (by norm_num) ⟨7166, by rfl⟩ (by norm_num))
theorem R38225 : Reach 38225 := rs (se 2 (by rfl) ⟨14334, by rfl⟩) (B 28669 (by norm_num) ⟨14334, by rfl⟩ (by norm_num))
theorem R38229 : Reach 38229 := rs (se 14 (by rfl) ⟨3, by rfl⟩) (B 7 (by norm_num) ⟨3, by rfl⟩ (by norm_num))
theorem R38233 : Reach 38233 := rs (se 2 (by rfl) ⟨14337, by rfl⟩) (B 28675 (by norm_num) ⟨14337, by rfl⟩ (by norm_num))
theorem R38237 : Reach 38237 := rs (se 3 (by rfl) ⟨7169, by rfl⟩) (B 14339 (by norm_num) ⟨7169, by rfl⟩ (by norm_num))
theorem R38241 : Reach 38241 := rs (se 2 (by rfl) ⟨14340, by rfl⟩) (B 28681 (by norm_num) ⟨14340, by rfl⟩ (by norm_num))
theorem R103781 : Reach 103781 := rs (se 4 (by rfl) ⟨9729, by rfl⟩) (B 19459 (by norm_num) ⟨9729, by rfl⟩ (by norm_num))
theorem R38245 : Reach 38245 := rs (se 4 (by rfl) ⟨3585, by rfl⟩) (B 7171 (by norm_num) ⟨3585, by rfl⟩ (by norm_num))
theorem R38249 : Reach 38249 := rs (se 2 (by rfl) ⟨14343, by rfl⟩) (B 28687 (by norm_num) ⟨14343, by rfl⟩ (by norm_num))
theorem R38253 : Reach 38253 := rs (se 3 (by rfl) ⟨7172, by rfl⟩) (B 14345 (by norm_num) ⟨7172, by rfl⟩ (by norm_num))
theorem R38257 : Reach 38257 := rs (se 2 (by rfl) ⟨14346, by rfl⟩) (B 28693 (by norm_num) ⟨14346, by rfl⟩ (by norm_num))
theorem R38261 : Reach 38261 := rs (se 5 (by rfl) ⟨1793, by rfl⟩) (B 3587 (by norm_num) ⟨1793, by rfl⟩ (by norm_num))
theorem R38265 : Reach 38265 := rs (se 2 (by rfl) ⟨14349, by rfl⟩) (B 28699 (by norm_num) ⟨14349, by rfl⟩ (by norm_num))
theorem R38269 : Reach 38269 := rs (se 3 (by rfl) ⟨7175, by rfl⟩) (B 14351 (by norm_num) ⟨7175, by rfl⟩ (by norm_num))
theorem R38273 : Reach 38273 := rs (se 2 (by rfl) ⟨14352, by rfl⟩) (B 28705 (by norm_num) ⟨14352, by rfl⟩ (by norm_num))
theorem R38277 : Reach 38277 := rs (se 4 (by rfl) ⟨3588, by rfl⟩) (B 7177 (by norm_num) ⟨3588, by rfl⟩ (by norm_num))
theorem R38281 : Reach 38281 := rs (se 2 (by rfl) ⟨14355, by rfl⟩) (B 28711 (by norm_num) ⟨14355, by rfl⟩ (by norm_num))
theorem R38285 : Reach 38285 := rs (se 3 (by rfl) ⟨7178, by rfl⟩) (B 14357 (by norm_num) ⟨7178, by rfl⟩ (by norm_num))
theorem R38289 : Reach 38289 := rs (se 2 (by rfl) ⟨14358, by rfl⟩) (B 28717 (by norm_num) ⟨14358, by rfl⟩ (by norm_num))
theorem R38293 : Reach 38293 := rs (se 6 (by rfl) ⟨897, by rfl⟩) (B 1795 (by norm_num) ⟨897, by rfl⟩ (by norm_num))
theorem R38297 : Reach 38297 := rs (se 2 (by rfl) ⟨14361, by rfl⟩) (B 28723 (by norm_num) ⟨14361, by rfl⟩ (by norm_num))
theorem R38301 : Reach 38301 := rs (se 3 (by rfl) ⟨7181, by rfl⟩) (B 14363 (by norm_num) ⟨7181, by rfl⟩ (by norm_num))
theorem R38305 : Reach 38305 := rs (se 2 (by rfl) ⟨14364, by rfl⟩) (B 28729 (by norm_num) ⟨14364, by rfl⟩ (by norm_num))
theorem R38309 : Reach 38309 := rs (se 4 (by rfl) ⟨3591, by rfl⟩) (B 7183 (by norm_num) ⟨3591, by rfl⟩ (by norm_num))
theorem R38313 : Reach 38313 := rs (se 2 (by rfl) ⟨14367, by rfl⟩) (B 28735 (by norm_num) ⟨14367, by rfl⟩ (by norm_num))
theorem R38317 : Reach 38317 := rs (se 3 (by rfl) ⟨7184, by rfl⟩) (B 14369 (by norm_num) ⟨7184, by rfl⟩ (by norm_num))
theorem R38321 : Reach 38321 := rs (se 2 (by rfl) ⟨14370, by rfl⟩) (B 28741 (by norm_num) ⟨14370, by rfl⟩ (by norm_num))
theorem R71093 : Reach 71093 := rs (se 5 (by rfl) ⟨3332, by rfl⟩) (B 6665 (by norm_num) ⟨3332, by rfl⟩ (by norm_num))
theorem R38325 : Reach 38325 := rs (se 5 (by rfl) ⟨1796, by rfl⟩) (B 3593 (by norm_num) ⟨1796, by rfl⟩ (by norm_num))
theorem R38329 : Reach 38329 := rs (se 2 (by rfl) ⟨14373, by rfl⟩) (B 28747 (by norm_num) ⟨14373, by rfl⟩ (by norm_num))
theorem R38333 : Reach 38333 := rs (se 3 (by rfl) ⟨7187, by rfl⟩) (B 14375 (by norm_num) ⟨7187, by rfl⟩ (by norm_num))
theorem R38337 : Reach 38337 := rs (se 2 (by rfl) ⟨14376, by rfl⟩) (B 28753 (by norm_num) ⟨14376, by rfl⟩ (by norm_num))
theorem R38341 : Reach 38341 := rs (se 4 (by rfl) ⟨3594, by rfl⟩) (B 7189 (by norm_num) ⟨3594, by rfl⟩ (by norm_num))
theorem R38345 : Reach 38345 := rs (se 2 (by rfl) ⟨14379, by rfl⟩) (B 28759 (by norm_num) ⟨14379, by rfl⟩ (by norm_num))
theorem R38349 : Reach 38349 := rs (se 3 (by rfl) ⟨7190, by rfl⟩) (B 14381 (by norm_num) ⟨7190, by rfl⟩ (by norm_num))
theorem R38353 : Reach 38353 := rs (se 2 (by rfl) ⟨14382, by rfl⟩) (B 28765 (by norm_num) ⟨14382, by rfl⟩ (by norm_num))
theorem R38357 : Reach 38357 := rs (se 7 (by rfl) ⟨449, by rfl⟩) (B 899 (by norm_num) ⟨449, by rfl⟩ (by norm_num))
theorem R38361 : Reach 38361 := rs (se 2 (by rfl) ⟨14385, by rfl⟩) (B 28771 (by norm_num) ⟨14385, by rfl⟩ (by norm_num))
theorem R38365 : Reach 38365 := rs (se 3 (by rfl) ⟨7193, by rfl⟩) (B 14387 (by norm_num) ⟨7193, by rfl⟩ (by norm_num))
theorem R38369 : Reach 38369 := rs (se 2 (by rfl) ⟨14388, by rfl⟩) (B 28777 (by norm_num) ⟨14388, by rfl⟩ (by norm_num))
theorem R38373 : Reach 38373 := rs (se 4 (by rfl) ⟨3597, by rfl⟩) (B 7195 (by norm_num) ⟨3597, by rfl⟩ (by norm_num))
theorem R38377 : Reach 38377 := rs (se 2 (by rfl) ⟨14391, by rfl⟩) (B 28783 (by norm_num) ⟨14391, by rfl⟩ (by norm_num))
theorem R38381 : Reach 38381 := rs (se 3 (by rfl) ⟨7196, by rfl⟩) (B 14393 (by norm_num) ⟨7196, by rfl⟩ (by norm_num))
theorem R38385 : Reach 38385 := rs (se 2 (by rfl) ⟨14394, by rfl⟩) (B 28789 (by norm_num) ⟨14394, by rfl⟩ (by norm_num))
theorem R38389 : Reach 38389 := rs (se 5 (by rfl) ⟨1799, by rfl⟩) (B 3599 (by norm_num) ⟨1799, by rfl⟩ (by norm_num))
theorem R38393 : Reach 38393 := rs (se 2 (by rfl) ⟨14397, by rfl⟩) (B 28795 (by norm_num) ⟨14397, by rfl⟩ (by norm_num))
theorem R38397 : Reach 38397 := rs (se 3 (by rfl) ⟨7199, by rfl⟩) (B 14399 (by norm_num) ⟨7199, by rfl⟩ (by norm_num))
theorem R38401 : Reach 38401 := rs (se 2 (by rfl) ⟨14400, by rfl⟩) (B 28801 (by norm_num) ⟨14400, by rfl⟩ (by norm_num))
theorem R38405 : Reach 38405 := rs (se 4 (by rfl) ⟨3600, by rfl⟩) (B 7201 (by norm_num) ⟨3600, by rfl⟩ (by norm_num))
theorem R38409 : Reach 38409 := rs (se 2 (by rfl) ⟨14403, by rfl⟩) (B 28807 (by norm_num) ⟨14403, by rfl⟩ (by norm_num))
theorem R38413 : Reach 38413 := rs (se 3 (by rfl) ⟨7202, by rfl⟩) (B 14405 (by norm_num) ⟨7202, by rfl⟩ (by norm_num))
theorem R38417 : Reach 38417 := rs (se 2 (by rfl) ⟨14406, by rfl⟩) (B 28813 (by norm_num) ⟨14406, by rfl⟩ (by norm_num))
theorem R38421 : Reach 38421 := rs (se 6 (by rfl) ⟨900, by rfl⟩) (B 1801 (by norm_num) ⟨900, by rfl⟩ (by norm_num))
theorem R38425 : Reach 38425 := rs (se 2 (by rfl) ⟨14409, by rfl⟩) (B 28819 (by norm_num) ⟨14409, by rfl⟩ (by norm_num))
theorem R38429 : Reach 38429 := rs (se 3 (by rfl) ⟨7205, by rfl⟩) (B 14411 (by norm_num) ⟨7205, by rfl⟩ (by norm_num))
theorem R38433 : Reach 38433 := rs (se 2 (by rfl) ⟨14412, by rfl⟩) (B 28825 (by norm_num) ⟨14412, by rfl⟩ (by norm_num))
theorem R38437 : Reach 38437 := rs (se 4 (by rfl) ⟨3603, by rfl⟩) (B 7207 (by norm_num) ⟨3603, by rfl⟩ (by norm_num))
theorem R38441 : Reach 38441 := rs (se 2 (by rfl) ⟨14415, by rfl⟩) (B 28831 (by norm_num) ⟨14415, by rfl⟩ (by norm_num))
theorem R38445 : Reach 38445 := rs (se 3 (by rfl) ⟨7208, by rfl⟩) (B 14417 (by norm_num) ⟨7208, by rfl⟩ (by norm_num))
theorem R38449 : Reach 38449 := rs (se 2 (by rfl) ⟨14418, by rfl⟩) (B 28837 (by norm_num) ⟨14418, by rfl⟩ (by norm_num))
theorem R38453 : Reach 38453 := rs (se 5 (by rfl) ⟨1802, by rfl⟩) (B 3605 (by norm_num) ⟨1802, by rfl⟩ (by norm_num))
theorem R38457 : Reach 38457 := rs (se 2 (by rfl) ⟨14421, by rfl⟩) (B 28843 (by norm_num) ⟨14421, by rfl⟩ (by norm_num))
theorem R38461 : Reach 38461 := rs (se 3 (by rfl) ⟨7211, by rfl⟩) (B 14423 (by norm_num) ⟨7211, by rfl⟩ (by norm_num))
theorem R38465 : Reach 38465 := rs (se 2 (by rfl) ⟨14424, by rfl⟩) (B 28849 (by norm_num) ⟨14424, by rfl⟩ (by norm_num))
theorem R38469 : Reach 38469 := rs (se 4 (by rfl) ⟨3606, by rfl⟩) (B 7213 (by norm_num) ⟨3606, by rfl⟩ (by norm_num))
theorem R38473 : Reach 38473 := rs (se 2 (by rfl) ⟨14427, by rfl⟩) (B 28855 (by norm_num) ⟨14427, by rfl⟩ (by norm_num))
theorem R38477 : Reach 38477 := rs (se 3 (by rfl) ⟨7214, by rfl⟩) (B 14429 (by norm_num) ⟨7214, by rfl⟩ (by norm_num))
theorem R38481 : Reach 38481 := rs (se 2 (by rfl) ⟨14430, by rfl⟩) (B 28861 (by norm_num) ⟨14430, by rfl⟩ (by norm_num))
theorem R38485 : Reach 38485 := rs (se 8 (by rfl) ⟨225, by rfl⟩) (B 451 (by norm_num) ⟨225, by rfl⟩ (by norm_num))
theorem R38489 : Reach 38489 := rs (se 2 (by rfl) ⟨14433, by rfl⟩) (B 28867 (by norm_num) ⟨14433, by rfl⟩ (by norm_num))
theorem R38493 : Reach 38493 := rs (se 3 (by rfl) ⟨7217, by rfl⟩) (B 14435 (by norm_num) ⟨7217, by rfl⟩ (by norm_num))
theorem R38497 : Reach 38497 := rs (se 2 (by rfl) ⟨14436, by rfl⟩) (B 28873 (by norm_num) ⟨14436, by rfl⟩ (by norm_num))
theorem R38501 : Reach 38501 := rs (se 4 (by rfl) ⟨3609, by rfl⟩) (B 7219 (by norm_num) ⟨3609, by rfl⟩ (by norm_num))
theorem R38505 : Reach 38505 := rs (se 2 (by rfl) ⟨14439, by rfl⟩) (B 28879 (by norm_num) ⟨14439, by rfl⟩ (by norm_num))
theorem R38509 : Reach 38509 := rs (se 3 (by rfl) ⟨7220, by rfl⟩) (B 14441 (by norm_num) ⟨7220, by rfl⟩ (by norm_num))
theorem R38513 : Reach 38513 := rs (se 2 (by rfl) ⟨14442, by rfl⟩) (B 28885 (by norm_num) ⟨14442, by rfl⟩ (by norm_num))
theorem R38517 : Reach 38517 := rs (se 5 (by rfl) ⟨1805, by rfl⟩) (B 3611 (by norm_num) ⟨1805, by rfl⟩ (by norm_num))
theorem R38521 : Reach 38521 := rs (se 2 (by rfl) ⟨14445, by rfl⟩) (B 28891 (by norm_num) ⟨14445, by rfl⟩ (by norm_num))
theorem R38525 : Reach 38525 := rs (se 3 (by rfl) ⟨7223, by rfl⟩) (B 14447 (by norm_num) ⟨7223, by rfl⟩ (by norm_num))
theorem R38529 : Reach 38529 := rs (se 2 (by rfl) ⟨14448, by rfl⟩) (B 28897 (by norm_num) ⟨14448, by rfl⟩ (by norm_num))
theorem R38533 : Reach 38533 := rs (se 4 (by rfl) ⟨3612, by rfl⟩) (B 7225 (by norm_num) ⟨3612, by rfl⟩ (by norm_num))
theorem R38537 : Reach 38537 := rs (se 2 (by rfl) ⟨14451, by rfl⟩) (B 28903 (by norm_num) ⟨14451, by rfl⟩ (by norm_num))
theorem R38541 : Reach 38541 := rs (se 3 (by rfl) ⟨7226, by rfl⟩) (B 14453 (by norm_num) ⟨7226, by rfl⟩ (by norm_num))
theorem R38545 : Reach 38545 := rs (se 2 (by rfl) ⟨14454, by rfl⟩) (B 28909 (by norm_num) ⟨14454, by rfl⟩ (by norm_num))
theorem R38549 : Reach 38549 := rs (se 6 (by rfl) ⟨903, by rfl⟩) (B 1807 (by norm_num) ⟨903, by rfl⟩ (by norm_num))
theorem R38553 : Reach 38553 := rs (se 2 (by rfl) ⟨14457, by rfl⟩) (B 28915 (by norm_num) ⟨14457, by rfl⟩ (by norm_num))
theorem R38557 : Reach 38557 := rs (se 3 (by rfl) ⟨7229, by rfl⟩) (B 14459 (by norm_num) ⟨7229, by rfl⟩ (by norm_num))
theorem R38561 : Reach 38561 := rs (se 2 (by rfl) ⟨14460, by rfl⟩) (B 28921 (by norm_num) ⟨14460, by rfl⟩ (by norm_num))
theorem R38565 : Reach 38565 := rs (se 4 (by rfl) ⟨3615, by rfl⟩) (B 7231 (by norm_num) ⟨3615, by rfl⟩ (by norm_num))
theorem R38569 : Reach 38569 := rs (se 2 (by rfl) ⟨14463, by rfl⟩) (B 28927 (by norm_num) ⟨14463, by rfl⟩ (by norm_num))
theorem R38573 : Reach 38573 := rs (se 3 (by rfl) ⟨7232, by rfl⟩) (B 14465 (by norm_num) ⟨7232, by rfl⟩ (by norm_num))
theorem R38577 : Reach 38577 := rs (se 2 (by rfl) ⟨14466, by rfl⟩) (B 28933 (by norm_num) ⟨14466, by rfl⟩ (by norm_num))
theorem R136885 : Reach 136885 := rs (se 5 (by rfl) ⟨6416, by rfl⟩) (B 12833 (by norm_num) ⟨6416, by rfl⟩ (by norm_num))
theorem R38581 : Reach 38581 := rs (se 5 (by rfl) ⟨1808, by rfl⟩) (B 3617 (by norm_num) ⟨1808, by rfl⟩ (by norm_num))
theorem R38585 : Reach 38585 := rs (se 2 (by rfl) ⟨14469, by rfl⟩) (B 28939 (by norm_num) ⟨14469, by rfl⟩ (by norm_num))
theorem R38589 : Reach 38589 := rs (se 3 (by rfl) ⟨7235, by rfl⟩) (B 14471 (by norm_num) ⟨7235, by rfl⟩ (by norm_num))
theorem R38593 : Reach 38593 := rs (se 2 (by rfl) ⟨14472, by rfl⟩) (B 28945 (by norm_num) ⟨14472, by rfl⟩ (by norm_num))
theorem R38597 : Reach 38597 := rs (se 4 (by rfl) ⟨3618, by rfl⟩) (B 7237 (by norm_num) ⟨3618, by rfl⟩ (by norm_num))
theorem R38601 : Reach 38601 := rs (se 2 (by rfl) ⟨14475, by rfl⟩) (B 28951 (by norm_num) ⟨14475, by rfl⟩ (by norm_num))
theorem R38605 : Reach 38605 := rs (se 3 (by rfl) ⟨7238, by rfl⟩) (B 14477 (by norm_num) ⟨7238, by rfl⟩ (by norm_num))
theorem R38609 : Reach 38609 := rs (se 2 (by rfl) ⟨14478, by rfl⟩) (B 28957 (by norm_num) ⟨14478, by rfl⟩ (by norm_num))
theorem R71381 : Reach 71381 := rs (se 7 (by rfl) ⟨836, by rfl⟩) (B 1673 (by norm_num) ⟨836, by rfl⟩ (by norm_num))
theorem R38613 : Reach 38613 := rs (se 7 (by rfl) ⟨452, by rfl⟩) (B 905 (by norm_num) ⟨452, by rfl⟩ (by norm_num))
theorem R38617 : Reach 38617 := rs (se 2 (by rfl) ⟨14481, by rfl⟩) (B 28963 (by norm_num) ⟨14481, by rfl⟩ (by norm_num))
theorem R38621 : Reach 38621 := rs (se 3 (by rfl) ⟨7241, by rfl⟩) (B 14483 (by norm_num) ⟨7241, by rfl⟩ (by norm_num))
theorem R38625 : Reach 38625 := rs (se 2 (by rfl) ⟨14484, by rfl⟩) (B 28969 (by norm_num) ⟨14484, by rfl⟩ (by norm_num))
theorem R38629 : Reach 38629 := rs (se 4 (by rfl) ⟨3621, by rfl⟩) (B 7243 (by norm_num) ⟨3621, by rfl⟩ (by norm_num))
theorem R38633 : Reach 38633 := rs (se 2 (by rfl) ⟨14487, by rfl⟩) (B 28975 (by norm_num) ⟨14487, by rfl⟩ (by norm_num))
theorem R38637 : Reach 38637 := rs (se 3 (by rfl) ⟨7244, by rfl⟩) (B 14489 (by norm_num) ⟨7244, by rfl⟩ (by norm_num))
theorem R38641 : Reach 38641 := rs (se 2 (by rfl) ⟨14490, by rfl⟩) (B 28981 (by norm_num) ⟨14490, by rfl⟩ (by norm_num))
theorem R38645 : Reach 38645 := rs (se 5 (by rfl) ⟨1811, by rfl⟩) (B 3623 (by norm_num) ⟨1811, by rfl⟩ (by norm_num))
theorem R38649 : Reach 38649 := rs (se 2 (by rfl) ⟨14493, by rfl⟩) (B 28987 (by norm_num) ⟨14493, by rfl⟩ (by norm_num))
theorem R38653 : Reach 38653 := rs (se 3 (by rfl) ⟨7247, by rfl⟩) (B 14495 (by norm_num) ⟨7247, by rfl⟩ (by norm_num))
theorem R38657 : Reach 38657 := rs (se 2 (by rfl) ⟨14496, by rfl⟩) (B 28993 (by norm_num) ⟨14496, by rfl⟩ (by norm_num))
theorem R38661 : Reach 38661 := rs (se 4 (by rfl) ⟨3624, by rfl⟩) (B 7249 (by norm_num) ⟨3624, by rfl⟩ (by norm_num))
theorem R38665 : Reach 38665 := rs (se 2 (by rfl) ⟨14499, by rfl⟩) (B 28999 (by norm_num) ⟨14499, by rfl⟩ (by norm_num))
theorem R38669 : Reach 38669 := rs (se 3 (by rfl) ⟨7250, by rfl⟩) (B 14501 (by norm_num) ⟨7250, by rfl⟩ (by norm_num))
theorem R38673 : Reach 38673 := rs (se 2 (by rfl) ⟨14502, by rfl⟩) (B 29005 (by norm_num) ⟨14502, by rfl⟩ (by norm_num))
theorem R38677 : Reach 38677 := rs (se 6 (by rfl) ⟨906, by rfl⟩) (B 1813 (by norm_num) ⟨906, by rfl⟩ (by norm_num))
theorem R38681 : Reach 38681 := rs (se 2 (by rfl) ⟨14505, by rfl⟩) (B 29011 (by norm_num) ⟨14505, by rfl⟩ (by norm_num))
theorem R38685 : Reach 38685 := rs (se 3 (by rfl) ⟨7253, by rfl⟩) (B 14507 (by norm_num) ⟨7253, by rfl⟩ (by norm_num))
theorem R38689 : Reach 38689 := rs (se 2 (by rfl) ⟨14508, by rfl⟩) (B 29017 (by norm_num) ⟨14508, by rfl⟩ (by norm_num))
theorem R38693 : Reach 38693 := rs (se 4 (by rfl) ⟨3627, by rfl⟩) (B 7255 (by norm_num) ⟨3627, by rfl⟩ (by norm_num))
theorem R38697 : Reach 38697 := rs (se 2 (by rfl) ⟨14511, by rfl⟩) (B 29023 (by norm_num) ⟨14511, by rfl⟩ (by norm_num))
theorem R38701 : Reach 38701 := rs (se 3 (by rfl) ⟨7256, by rfl⟩) (B 14513 (by norm_num) ⟨7256, by rfl⟩ (by norm_num))
theorem R38705 : Reach 38705 := rs (se 2 (by rfl) ⟨14514, by rfl⟩) (B 29029 (by norm_num) ⟨14514, by rfl⟩ (by norm_num))
theorem R38709 : Reach 38709 := rs (se 5 (by rfl) ⟨1814, by rfl⟩) (B 3629 (by norm_num) ⟨1814, by rfl⟩ (by norm_num))
theorem R38713 : Reach 38713 := rs (se 2 (by rfl) ⟨14517, by rfl⟩) (B 29035 (by norm_num) ⟨14517, by rfl⟩ (by norm_num))
theorem R38717 : Reach 38717 := rs (se 3 (by rfl) ⟨7259, by rfl⟩) (B 14519 (by norm_num) ⟨7259, by rfl⟩ (by norm_num))
theorem R38721 : Reach 38721 := rs (se 2 (by rfl) ⟨14520, by rfl⟩) (B 29041 (by norm_num) ⟨14520, by rfl⟩ (by norm_num))
theorem R38725 : Reach 38725 := rs (se 4 (by rfl) ⟨3630, by rfl⟩) (B 7261 (by norm_num) ⟨3630, by rfl⟩ (by norm_num))
theorem R38729 : Reach 38729 := rs (se 2 (by rfl) ⟨14523, by rfl⟩) (B 29047 (by norm_num) ⟨14523, by rfl⟩ (by norm_num))
theorem R38733 : Reach 38733 := rs (se 3 (by rfl) ⟨7262, by rfl⟩) (B 14525 (by norm_num) ⟨7262, by rfl⟩ (by norm_num))
theorem R38737 : Reach 38737 := rs (se 2 (by rfl) ⟨14526, by rfl⟩) (B 29053 (by norm_num) ⟨14526, by rfl⟩ (by norm_num))
theorem R38741 : Reach 38741 := rs (se 9 (by rfl) ⟨113, by rfl⟩) (B 227 (by norm_num) ⟨113, by rfl⟩ (by norm_num))
theorem R38745 : Reach 38745 := rs (se 2 (by rfl) ⟨14529, by rfl⟩) (B 29059 (by norm_num) ⟨14529, by rfl⟩ (by norm_num))
theorem R38749 : Reach 38749 := rs (se 3 (by rfl) ⟨7265, by rfl⟩) (B 14531 (by norm_num) ⟨7265, by rfl⟩ (by norm_num))
theorem R38753 : Reach 38753 := rs (se 2 (by rfl) ⟨14532, by rfl⟩) (B 29065 (by norm_num) ⟨14532, by rfl⟩ (by norm_num))
theorem R38757 : Reach 38757 := rs (se 4 (by rfl) ⟨3633, by rfl⟩) (B 7267 (by norm_num) ⟨3633, by rfl⟩ (by norm_num))
theorem R38761 : Reach 38761 := rs (se 2 (by rfl) ⟨14535, by rfl⟩) (B 29071 (by norm_num) ⟨14535, by rfl⟩ (by norm_num))
theorem R71533 : Reach 71533 := rs (se 3 (by rfl) ⟨13412, by rfl⟩) (B 26825 (by norm_num) ⟨13412, by rfl⟩ (by norm_num))
theorem R38765 : Reach 38765 := rs (se 3 (by rfl) ⟨7268, by rfl⟩) (B 14537 (by norm_num) ⟨7268, by rfl⟩ (by norm_num))
theorem R38769 : Reach 38769 := rs (se 2 (by rfl) ⟨14538, by rfl⟩) (B 29077 (by norm_num) ⟨14538, by rfl⟩ (by norm_num))
theorem R38773 : Reach 38773 := rs (se 5 (by rfl) ⟨1817, by rfl⟩) (B 3635 (by norm_num) ⟨1817, by rfl⟩ (by norm_num))
theorem R38777 : Reach 38777 := rs (se 2 (by rfl) ⟨14541, by rfl⟩) (B 29083 (by norm_num) ⟨14541, by rfl⟩ (by norm_num))
theorem R38781 : Reach 38781 := rs (se 3 (by rfl) ⟨7271, by rfl⟩) (B 14543 (by norm_num) ⟨7271, by rfl⟩ (by norm_num))
theorem R38785 : Reach 38785 := rs (se 2 (by rfl) ⟨14544, by rfl⟩) (B 29089 (by norm_num) ⟨14544, by rfl⟩ (by norm_num))
theorem R38789 : Reach 38789 := rs (se 4 (by rfl) ⟨3636, by rfl⟩) (B 7273 (by norm_num) ⟨3636, by rfl⟩ (by norm_num))
theorem R38793 : Reach 38793 := rs (se 2 (by rfl) ⟨14547, by rfl⟩) (B 29095 (by norm_num) ⟨14547, by rfl⟩ (by norm_num))
theorem R38797 : Reach 38797 := rs (se 3 (by rfl) ⟨7274, by rfl⟩) (B 14549 (by norm_num) ⟨7274, by rfl⟩ (by norm_num))
theorem R38801 : Reach 38801 := rs (se 2 (by rfl) ⟨14550, by rfl⟩) (B 29101 (by norm_num) ⟨14550, by rfl⟩ (by norm_num))
theorem R38805 : Reach 38805 := rs (se 6 (by rfl) ⟨909, by rfl⟩) (B 1819 (by norm_num) ⟨909, by rfl⟩ (by norm_num))
theorem R38809 : Reach 38809 := rs (se 2 (by rfl) ⟨14553, by rfl⟩) (B 29107 (by norm_num) ⟨14553, by rfl⟩ (by norm_num))
theorem R38813 : Reach 38813 := rs (se 3 (by rfl) ⟨7277, by rfl⟩) (B 14555 (by norm_num) ⟨7277, by rfl⟩ (by norm_num))
theorem R38817 : Reach 38817 := rs (se 2 (by rfl) ⟨14556, by rfl⟩) (B 29113 (by norm_num) ⟨14556, by rfl⟩ (by norm_num))
theorem R38821 : Reach 38821 := rs (se 4 (by rfl) ⟨3639, by rfl⟩) (B 7279 (by norm_num) ⟨3639, by rfl⟩ (by norm_num))
theorem R38825 : Reach 38825 := rs (se 2 (by rfl) ⟨14559, by rfl⟩) (B 29119 (by norm_num) ⟨14559, by rfl⟩ (by norm_num))
theorem R38829 : Reach 38829 := rs (se 3 (by rfl) ⟨7280, by rfl⟩) (B 14561 (by norm_num) ⟨7280, by rfl⟩ (by norm_num))
theorem R38833 : Reach 38833 := rs (se 2 (by rfl) ⟨14562, by rfl⟩) (B 29125 (by norm_num) ⟨14562, by rfl⟩ (by norm_num))
theorem R38837 : Reach 38837 := rs (se 5 (by rfl) ⟨1820, by rfl⟩) (B 3641 (by norm_num) ⟨1820, by rfl⟩ (by norm_num))
theorem R38841 : Reach 38841 := rs (se 2 (by rfl) ⟨14565, by rfl⟩) (B 29131 (by norm_num) ⟨14565, by rfl⟩ (by norm_num))
theorem R38845 : Reach 38845 := rs (se 3 (by rfl) ⟨7283, by rfl⟩) (B 14567 (by norm_num) ⟨7283, by rfl⟩ (by norm_num))
theorem R38849 : Reach 38849 := rs (se 2 (by rfl) ⟨14568, by rfl⟩) (B 29137 (by norm_num) ⟨14568, by rfl⟩ (by norm_num))
theorem R38853 : Reach 38853 := rs (se 4 (by rfl) ⟨3642, by rfl⟩) (B 7285 (by norm_num) ⟨3642, by rfl⟩ (by norm_num))
theorem R38857 : Reach 38857 := rs (se 2 (by rfl) ⟨14571, by rfl⟩) (B 29143 (by norm_num) ⟨14571, by rfl⟩ (by norm_num))
theorem R38861 : Reach 38861 := rs (se 3 (by rfl) ⟨7286, by rfl⟩) (B 14573 (by norm_num) ⟨7286, by rfl⟩ (by norm_num))
theorem R38865 : Reach 38865 := rs (se 2 (by rfl) ⟨14574, by rfl⟩) (B 29149 (by norm_num) ⟨14574, by rfl⟩ (by norm_num))
theorem R137173 : Reach 137173 := rs (se 7 (by rfl) ⟨1607, by rfl⟩) (B 3215 (by norm_num) ⟨1607, by rfl⟩ (by norm_num))
theorem R38869 : Reach 38869 := rs (se 7 (by rfl) ⟨455, by rfl⟩) (B 911 (by norm_num) ⟨455, by rfl⟩ (by norm_num))
theorem R38873 : Reach 38873 := rs (se 2 (by rfl) ⟨14577, by rfl⟩) (B 29155 (by norm_num) ⟨14577, by rfl⟩ (by norm_num))
theorem R38877 : Reach 38877 := rs (se 3 (by rfl) ⟨7289, by rfl⟩) (B 14579 (by norm_num) ⟨7289, by rfl⟩ (by norm_num))
theorem R38881 : Reach 38881 := rs (se 2 (by rfl) ⟨14580, by rfl⟩) (B 29161 (by norm_num) ⟨14580, by rfl⟩ (by norm_num))
theorem R38885 : Reach 38885 := rs (se 4 (by rfl) ⟨3645, by rfl⟩) (B 7291 (by norm_num) ⟨3645, by rfl⟩ (by norm_num))
theorem R38889 : Reach 38889 := rs (se 2 (by rfl) ⟨14583, by rfl⟩) (B 29167 (by norm_num) ⟨14583, by rfl⟩ (by norm_num))
theorem R38893 : Reach 38893 := rs (se 3 (by rfl) ⟨7292, by rfl⟩) (B 14585 (by norm_num) ⟨7292, by rfl⟩ (by norm_num))
theorem R38897 : Reach 38897 := rs (se 2 (by rfl) ⟨14586, by rfl⟩) (B 29173 (by norm_num) ⟨14586, by rfl⟩ (by norm_num))
theorem R38901 : Reach 38901 := rs (se 5 (by rfl) ⟨1823, by rfl⟩) (B 3647 (by norm_num) ⟨1823, by rfl⟩ (by norm_num))
theorem R38905 : Reach 38905 := rs (se 2 (by rfl) ⟨14589, by rfl⟩) (B 29179 (by norm_num) ⟨14589, by rfl⟩ (by norm_num))
theorem R38909 : Reach 38909 := rs (se 3 (by rfl) ⟨7295, by rfl⟩) (B 14591 (by norm_num) ⟨7295, by rfl⟩ (by norm_num))
theorem R38913 : Reach 38913 := rs (se 2 (by rfl) ⟨14592, by rfl⟩) (B 29185 (by norm_num) ⟨14592, by rfl⟩ (by norm_num))
theorem R104453 : Reach 104453 := rs (se 4 (by rfl) ⟨9792, by rfl⟩) (B 19585 (by norm_num) ⟨9792, by rfl⟩ (by norm_num))
theorem R38917 : Reach 38917 := rs (se 4 (by rfl) ⟨3648, by rfl⟩) (B 7297 (by norm_num) ⟨3648, by rfl⟩ (by norm_num))
theorem R38921 : Reach 38921 := rs (se 2 (by rfl) ⟨14595, by rfl⟩) (B 29191 (by norm_num) ⟨14595, by rfl⟩ (by norm_num))
theorem R38925 : Reach 38925 := rs (se 3 (by rfl) ⟨7298, by rfl⟩) (B 14597 (by norm_num) ⟨7298, by rfl⟩ (by norm_num))
theorem R38929 : Reach 38929 := rs (se 2 (by rfl) ⟨14598, by rfl⟩) (B 29197 (by norm_num) ⟨14598, by rfl⟩ (by norm_num))
theorem R38933 : Reach 38933 := rs (se 6 (by rfl) ⟨912, by rfl⟩) (B 1825 (by norm_num) ⟨912, by rfl⟩ (by norm_num))
theorem R38937 : Reach 38937 := rs (se 2 (by rfl) ⟨14601, by rfl⟩) (B 29203 (by norm_num) ⟨14601, by rfl⟩ (by norm_num))
theorem R38941 : Reach 38941 := rs (se 3 (by rfl) ⟨7301, by rfl⟩) (B 14603 (by norm_num) ⟨7301, by rfl⟩ (by norm_num))
theorem R38945 : Reach 38945 := rs (se 2 (by rfl) ⟨14604, by rfl⟩) (B 29209 (by norm_num) ⟨14604, by rfl⟩ (by norm_num))
theorem R38949 : Reach 38949 := rs (se 4 (by rfl) ⟨3651, by rfl⟩) (B 7303 (by norm_num) ⟨3651, by rfl⟩ (by norm_num))
theorem R38953 : Reach 38953 := rs (se 2 (by rfl) ⟨14607, by rfl⟩) (B 29215 (by norm_num) ⟨14607, by rfl⟩ (by norm_num))
theorem R38957 : Reach 38957 := rs (se 3 (by rfl) ⟨7304, by rfl⟩) (B 14609 (by norm_num) ⟨7304, by rfl⟩ (by norm_num))
theorem R38961 : Reach 38961 := rs (se 2 (by rfl) ⟨14610, by rfl⟩) (B 29221 (by norm_num) ⟨14610, by rfl⟩ (by norm_num))
theorem R38965 : Reach 38965 := rs (se 5 (by rfl) ⟨1826, by rfl⟩) (B 3653 (by norm_num) ⟨1826, by rfl⟩ (by norm_num))
theorem R38969 : Reach 38969 := rs (se 2 (by rfl) ⟨14613, by rfl⟩) (B 29227 (by norm_num) ⟨14613, by rfl⟩ (by norm_num))
theorem R38973 : Reach 38973 := rs (se 3 (by rfl) ⟨7307, by rfl⟩) (B 14615 (by norm_num) ⟨7307, by rfl⟩ (by norm_num))
theorem R38977 : Reach 38977 := rs (se 2 (by rfl) ⟨14616, by rfl⟩) (B 29233 (by norm_num) ⟨14616, by rfl⟩ (by norm_num))
theorem R38981 : Reach 38981 := rs (se 4 (by rfl) ⟨3654, by rfl⟩) (B 7309 (by norm_num) ⟨3654, by rfl⟩ (by norm_num))
theorem R38985 : Reach 38985 := rs (se 2 (by rfl) ⟨14619, by rfl⟩) (B 29239 (by norm_num) ⟨14619, by rfl⟩ (by norm_num))
theorem R38989 : Reach 38989 := rs (se 3 (by rfl) ⟨7310, by rfl⟩) (B 14621 (by norm_num) ⟨7310, by rfl⟩ (by norm_num))
theorem R38993 : Reach 38993 := rs (se 2 (by rfl) ⟨14622, by rfl⟩) (B 29245 (by norm_num) ⟨14622, by rfl⟩ (by norm_num))
theorem R38997 : Reach 38997 := rs (se 8 (by rfl) ⟨228, by rfl⟩) (B 457 (by norm_num) ⟨228, by rfl⟩ (by norm_num))
theorem R39001 : Reach 39001 := rs (se 2 (by rfl) ⟨14625, by rfl⟩) (B 29251 (by norm_num) ⟨14625, by rfl⟩ (by norm_num))
theorem R39005 : Reach 39005 := rs (se 3 (by rfl) ⟨7313, by rfl⟩) (B 14627 (by norm_num) ⟨7313, by rfl⟩ (by norm_num))
theorem R39009 : Reach 39009 := rs (se 2 (by rfl) ⟨14628, by rfl⟩) (B 29257 (by norm_num) ⟨14628, by rfl⟩ (by norm_num))
theorem R39013 : Reach 39013 := rs (se 4 (by rfl) ⟨3657, by rfl⟩) (B 7315 (by norm_num) ⟨3657, by rfl⟩ (by norm_num))
theorem R39017 : Reach 39017 := rs (se 2 (by rfl) ⟨14631, by rfl⟩) (B 29263 (by norm_num) ⟨14631, by rfl⟩ (by norm_num))
theorem R39021 : Reach 39021 := rs (se 3 (by rfl) ⟨7316, by rfl⟩) (B 14633 (by norm_num) ⟨7316, by rfl⟩ (by norm_num))
theorem R39025 : Reach 39025 := rs (se 2 (by rfl) ⟨14634, by rfl⟩) (B 29269 (by norm_num) ⟨14634, by rfl⟩ (by norm_num))
theorem R39029 : Reach 39029 := rs (se 5 (by rfl) ⟨1829, by rfl⟩) (B 3659 (by norm_num) ⟨1829, by rfl⟩ (by norm_num))
theorem R39033 : Reach 39033 := rs (se 2 (by rfl) ⟨14637, by rfl⟩) (B 29275 (by norm_num) ⟨14637, by rfl⟩ (by norm_num))
theorem R39037 : Reach 39037 := rs (se 3 (by rfl) ⟨7319, by rfl⟩) (B 14639 (by norm_num) ⟨7319, by rfl⟩ (by norm_num))
theorem R39041 : Reach 39041 := rs (se 2 (by rfl) ⟨14640, by rfl⟩) (B 29281 (by norm_num) ⟨14640, by rfl⟩ (by norm_num))
theorem R39045 : Reach 39045 := rs (se 4 (by rfl) ⟨3660, by rfl⟩) (B 7321 (by norm_num) ⟨3660, by rfl⟩ (by norm_num))
theorem R39049 : Reach 39049 := rs (se 2 (by rfl) ⟨14643, by rfl⟩) (B 29287 (by norm_num) ⟨14643, by rfl⟩ (by norm_num))
theorem R39053 : Reach 39053 := rs (se 3 (by rfl) ⟨7322, by rfl⟩) (B 14645 (by norm_num) ⟨7322, by rfl⟩ (by norm_num))
theorem R39057 : Reach 39057 := rs (se 2 (by rfl) ⟨14646, by rfl⟩) (B 29293 (by norm_num) ⟨14646, by rfl⟩ (by norm_num))
theorem R39061 : Reach 39061 := rs (se 6 (by rfl) ⟨915, by rfl⟩) (B 1831 (by norm_num) ⟨915, by rfl⟩ (by norm_num))
theorem R39065 : Reach 39065 := rs (se 2 (by rfl) ⟨14649, by rfl⟩) (B 29299 (by norm_num) ⟨14649, by rfl⟩ (by norm_num))
theorem R71837 : Reach 71837 := rs (se 3 (by rfl) ⟨13469, by rfl⟩) (B 26939 (by norm_num) ⟨13469, by rfl⟩ (by norm_num))
theorem R39069 : Reach 39069 := rs (se 3 (by rfl) ⟨7325, by rfl⟩) (B 14651 (by norm_num) ⟨7325, by rfl⟩ (by norm_num))
theorem R39073 : Reach 39073 := rs (se 2 (by rfl) ⟨14652, by rfl⟩) (B 29305 (by norm_num) ⟨14652, by rfl⟩ (by norm_num))
theorem R39077 : Reach 39077 := rs (se 4 (by rfl) ⟨3663, by rfl⟩) (B 7327 (by norm_num) ⟨3663, by rfl⟩ (by norm_num))
theorem R39081 : Reach 39081 := rs (se 2 (by rfl) ⟨14655, by rfl⟩) (B 29311 (by norm_num) ⟨14655, by rfl⟩ (by norm_num))
theorem R39085 : Reach 39085 := rs (se 3 (by rfl) ⟨7328, by rfl⟩) (B 14657 (by norm_num) ⟨7328, by rfl⟩ (by norm_num))
theorem R39089 : Reach 39089 := rs (se 2 (by rfl) ⟨14658, by rfl⟩) (B 29317 (by norm_num) ⟨14658, by rfl⟩ (by norm_num))
theorem R39093 : Reach 39093 := rs (se 5 (by rfl) ⟨1832, by rfl⟩) (B 3665 (by norm_num) ⟨1832, by rfl⟩ (by norm_num))
theorem R39097 : Reach 39097 := rs (se 2 (by rfl) ⟨14661, by rfl⟩) (B 29323 (by norm_num) ⟨14661, by rfl⟩ (by norm_num))
theorem R39101 : Reach 39101 := rs (se 3 (by rfl) ⟨7331, by rfl⟩) (B 14663 (by norm_num) ⟨7331, by rfl⟩ (by norm_num))
theorem R39105 : Reach 39105 := rs (se 2 (by rfl) ⟨14664, by rfl⟩) (B 29329 (by norm_num) ⟨14664, by rfl⟩ (by norm_num))
theorem R39109 : Reach 39109 := rs (se 4 (by rfl) ⟨3666, by rfl⟩) (B 7333 (by norm_num) ⟨3666, by rfl⟩ (by norm_num))
theorem R39113 : Reach 39113 := rs (se 2 (by rfl) ⟨14667, by rfl⟩) (B 29335 (by norm_num) ⟨14667, by rfl⟩ (by norm_num))
theorem R39161 : Reach 39161 := rs (se 2 (by rfl) ⟨14685, by rfl⟩) (B 29371 (by norm_num) ⟨14685, by rfl⟩ (by norm_num))
theorem R137477 : Reach 137477 := rs (se 4 (by rfl) ⟨12888, by rfl⟩) (B 25777 (by norm_num) ⟨12888, by rfl⟩ (by norm_num))
theorem R366869 : Reach 366869 := rs (se 6 (by rfl) ⟨8598, by rfl⟩) (B 17197 (by norm_num) ⟨8598, by rfl⟩ (by norm_num))
theorem R104885 : Reach 104885 := rs (se 5 (by rfl) ⟨4916, by rfl⟩) (B 9833 (by norm_num) ⟨4916, by rfl⟩ (by norm_num))
theorem R39349 : Reach 39349 := rs (se 5 (by rfl) ⟨1844, by rfl⟩) (B 3689 (by norm_num) ⟨1844, by rfl⟩ (by norm_num))
theorem R268757 : Reach 268757 := rs (se 7 (by rfl) ⟨3149, by rfl⟩) (B 6299 (by norm_num) ⟨3149, by rfl⟩ (by norm_num))
theorem R39533 : Reach 39533 := rs (se 3 (by rfl) ⟨7412, by rfl⟩) (B 14825 (by norm_num) ⟨7412, by rfl⟩ (by norm_num))
theorem R39541 : Reach 39541 := rs (se 5 (by rfl) ⟨1853, by rfl⟩) (B 3707 (by norm_num) ⟨1853, by rfl⟩ (by norm_num))
theorem R203381 : Reach 203381 := rs (se 5 (by rfl) ⟨9533, by rfl⟩) (B 19067 (by norm_num) ⟨9533, by rfl⟩ (by norm_num))
theorem R39577 : Reach 39577 := rs (se 2 (by rfl) ⟨14841, by rfl⟩) (B 29683 (by norm_num) ⟨14841, by rfl⟩ (by norm_num))
theorem R39613 : Reach 39613 := rs (se 3 (by rfl) ⟨7427, by rfl⟩) (B 14855 (by norm_num) ⟨7427, by rfl⟩ (by norm_num))
theorem R39649 : Reach 39649 := rs (se 2 (by rfl) ⟨14868, by rfl⟩) (B 29737 (by norm_num) ⟨14868, by rfl⟩ (by norm_num))
theorem R39685 : Reach 39685 := rs (se 4 (by rfl) ⟨3720, by rfl⟩) (B 7441 (by norm_num) ⟨3720, by rfl⟩ (by norm_num))
theorem R39721 : Reach 39721 := rs (se 2 (by rfl) ⟨14895, by rfl⟩) (B 29791 (by norm_num) ⟨14895, by rfl⟩ (by norm_num))
theorem R203573 : Reach 203573 := rs (se 5 (by rfl) ⟨9542, by rfl⟩) (B 19085 (by norm_num) ⟨9542, by rfl⟩ (by norm_num))
theorem R39757 : Reach 39757 := rs (se 3 (by rfl) ⟨7454, by rfl⟩) (B 14909 (by norm_num) ⟨7454, by rfl⟩ (by norm_num))
theorem R105301 : Reach 105301 := rs (se 9 (by rfl) ⟨308, by rfl⟩) (B 617 (by norm_num) ⟨308, by rfl⟩ (by norm_num))
theorem R39793 : Reach 39793 := rs (se 2 (by rfl) ⟨14922, by rfl⟩) (B 29845 (by norm_num) ⟨14922, by rfl⟩ (by norm_num))
theorem R72589 : Reach 72589 := rs (se 3 (by rfl) ⟨13610, by rfl⟩) (B 27221 (by norm_num) ⟨13610, by rfl⟩ (by norm_num))
theorem R39829 : Reach 39829 := rs (se 6 (by rfl) ⟨933, by rfl⟩) (B 1867 (by norm_num) ⟨933, by rfl⟩ (by norm_num))
theorem R39865 : Reach 39865 := rs (se 2 (by rfl) ⟨14949, by rfl⟩) (B 29899 (by norm_num) ⟨14949, by rfl⟩ (by norm_num))
theorem R39901 : Reach 39901 := rs (se 3 (by rfl) ⟨7481, by rfl⟩) (B 14963 (by norm_num) ⟨7481, by rfl⟩ (by norm_num))
theorem R170981 : Reach 170981 := rs (se 4 (by rfl) ⟨16029, by rfl⟩) (B 32059 (by norm_num) ⟨16029, by rfl⟩ (by norm_num))
theorem R39937 : Reach 39937 := rs (se 2 (by rfl) ⟨14976, by rfl⟩) (B 29953 (by norm_num) ⟨14976, by rfl⟩ (by norm_num))
theorem R72733 : Reach 72733 := rs (se 3 (by rfl) ⟨13637, by rfl⟩) (B 27275 (by norm_num) ⟨13637, by rfl⟩ (by norm_num))
theorem R39973 : Reach 39973 := rs (se 4 (by rfl) ⟨3747, by rfl⟩) (B 7495 (by norm_num) ⟨3747, by rfl⟩ (by norm_num))
theorem R40009 : Reach 40009 := rs (se 2 (by rfl) ⟨15003, by rfl⟩) (B 30007 (by norm_num) ⟨15003, by rfl⟩ (by norm_num))
theorem R40045 : Reach 40045 := rs (se 3 (by rfl) ⟨7508, by rfl⟩) (B 15017 (by norm_num) ⟨7508, by rfl⟩ (by norm_num))
theorem R40081 : Reach 40081 := rs (se 2 (by rfl) ⟨15030, by rfl⟩) (B 30061 (by norm_num) ⟨15030, by rfl⟩ (by norm_num))
theorem R105637 : Reach 105637 := rs (se 4 (by rfl) ⟨9903, by rfl⟩) (B 19807 (by norm_num) ⟨9903, by rfl⟩ (by norm_num))
theorem R40117 : Reach 40117 := rs (se 5 (by rfl) ⟨1880, by rfl⟩) (B 3761 (by norm_num) ⟨1880, by rfl⟩ (by norm_num))
theorem R72893 : Reach 72893 := rs (se 3 (by rfl) ⟨13667, by rfl⟩) (B 27335 (by norm_num) ⟨13667, by rfl⟩ (by norm_num))
theorem R40153 : Reach 40153 := rs (se 2 (by rfl) ⟨15057, by rfl⟩) (B 30115 (by norm_num) ⟨15057, by rfl⟩ (by norm_num))
theorem R236789 : Reach 236789 := rs (se 5 (by rfl) ⟨11099, by rfl⟩) (B 22199 (by norm_num) ⟨11099, by rfl⟩ (by norm_num))
theorem R40189 : Reach 40189 := rs (se 3 (by rfl) ⟨7535, by rfl⟩) (B 15071 (by norm_num) ⟨7535, by rfl⟩ (by norm_num))
theorem R72965 : Reach 72965 := rs (se 4 (by rfl) ⟨6840, by rfl⟩) (B 13681 (by norm_num) ⟨6840, by rfl⟩ (by norm_num))
theorem R40225 : Reach 40225 := rs (se 2 (by rfl) ⟨15084, by rfl⟩) (B 30169 (by norm_num) ⟨15084, by rfl⟩ (by norm_num))
theorem R40261 : Reach 40261 := rs (se 4 (by rfl) ⟨3774, by rfl⟩) (B 7549 (by norm_num) ⟨3774, by rfl⟩ (by norm_num))
theorem R73037 : Reach 73037 := rs (se 3 (by rfl) ⟨13694, by rfl⟩) (B 27389 (by norm_num) ⟨13694, by rfl⟩ (by norm_num))
theorem R40285 : Reach 40285 := rs (se 3 (by rfl) ⟨7553, by rfl⟩) (B 15107 (by norm_num) ⟨7553, by rfl⟩ (by norm_num))
theorem R40297 : Reach 40297 := rs (se 2 (by rfl) ⟨15111, by rfl⟩) (B 30223 (by norm_num) ⟨15111, by rfl⟩ (by norm_num))
theorem R40333 : Reach 40333 := rs (se 3 (by rfl) ⟨7562, by rfl⟩) (B 15125 (by norm_num) ⟨7562, by rfl⟩ (by norm_num))
theorem R40357 : Reach 40357 := rs (se 4 (by rfl) ⟨3783, by rfl⟩) (B 7567 (by norm_num) ⟨3783, by rfl⟩ (by norm_num))
theorem R40369 : Reach 40369 := rs (se 2 (by rfl) ⟨15138, by rfl⟩) (B 30277 (by norm_num) ⟨15138, by rfl⟩ (by norm_num))
theorem R40405 : Reach 40405 := rs (se 7 (by rfl) ⟨473, by rfl⟩) (B 947 (by norm_num) ⟨473, by rfl⟩ (by norm_num))
theorem R40441 : Reach 40441 := rs (se 2 (by rfl) ⟨15165, by rfl⟩) (B 30331 (by norm_num) ⟨15165, by rfl⟩ (by norm_num))
theorem R138773 : Reach 138773 := rs (se 6 (by rfl) ⟨3252, by rfl⟩) (B 6505 (by norm_num) ⟨3252, by rfl⟩ (by norm_num))
theorem R40477 : Reach 40477 := rs (se 3 (by rfl) ⟨7589, by rfl⟩) (B 15179 (by norm_num) ⟨7589, by rfl⟩ (by norm_num))
theorem R40513 : Reach 40513 := rs (se 2 (by rfl) ⟨15192, by rfl⟩) (B 30385 (by norm_num) ⟨15192, by rfl⟩ (by norm_num))
theorem R40537 : Reach 40537 := rs (se 2 (by rfl) ⟨15201, by rfl⟩) (B 30403 (by norm_num) ⟨15201, by rfl⟩ (by norm_num))
theorem R40549 : Reach 40549 := rs (se 4 (by rfl) ⟨3801, by rfl⟩) (B 7603 (by norm_num) ⟨3801, by rfl⟩ (by norm_num))
theorem R73325 : Reach 73325 := rs (se 3 (by rfl) ⟨13748, by rfl⟩) (B 27497 (by norm_num) ⟨13748, by rfl⟩ (by norm_num))
theorem R40585 : Reach 40585 := rs (se 2 (by rfl) ⟨15219, by rfl⟩) (B 30439 (by norm_num) ⟨15219, by rfl⟩ (by norm_num))
theorem R40621 : Reach 40621 := rs (se 3 (by rfl) ⟨7616, by rfl⟩) (B 15233 (by norm_num) ⟨7616, by rfl⟩ (by norm_num))
theorem R40657 : Reach 40657 := rs (se 2 (by rfl) ⟨15246, by rfl⟩) (B 30493 (by norm_num) ⟨15246, by rfl⟩ (by norm_num))
theorem R40693 : Reach 40693 := rs (se 5 (by rfl) ⟨1907, by rfl⟩) (B 3815 (by norm_num) ⟨1907, by rfl⟩ (by norm_num))
theorem R73477 : Reach 73477 := rs (se 4 (by rfl) ⟨6888, by rfl⟩) (B 13777 (by norm_num) ⟨6888, by rfl⟩ (by norm_num))
theorem R40729 : Reach 40729 := rs (se 2 (by rfl) ⟨15273, by rfl⟩) (B 30547 (by norm_num) ⟨15273, by rfl⟩ (by norm_num))
theorem R40765 : Reach 40765 := rs (se 3 (by rfl) ⟨7643, by rfl⟩) (B 15287 (by norm_num) ⟨7643, by rfl⟩ (by norm_num))
theorem R40801 : Reach 40801 := rs (se 2 (by rfl) ⟨15300, by rfl⟩) (B 30601 (by norm_num) ⟨15300, by rfl⟩ (by norm_num))
theorem R40837 : Reach 40837 := rs (se 4 (by rfl) ⟨3828, by rfl⟩) (B 7657 (by norm_num) ⟨3828, by rfl⟩ (by norm_num))
theorem R434069 : Reach 434069 := rs (se 6 (by rfl) ⟨10173, by rfl⟩) (B 20347 (by norm_num) ⟨10173, by rfl⟩ (by norm_num))
theorem R40873 : Reach 40873 := rs (se 2 (by rfl) ⟨15327, by rfl⟩) (B 30655 (by norm_num) ⟨15327, by rfl⟩ (by norm_num))
theorem R40909 : Reach 40909 := rs (se 3 (by rfl) ⟨7670, by rfl⟩) (B 15341 (by norm_num) ⟨7670, by rfl⟩ (by norm_num))
theorem R171989 : Reach 171989 := rs (se 7 (by rfl) ⟨2015, by rfl⟩) (B 4031 (by norm_num) ⟨2015, by rfl⟩ (by norm_num))
theorem R40945 : Reach 40945 := rs (se 2 (by rfl) ⟨15354, by rfl⟩) (B 30709 (by norm_num) ⟨15354, by rfl⟩ (by norm_num))
theorem R40981 : Reach 40981 := rs (se 6 (by rfl) ⟨960, by rfl⟩) (B 1921 (by norm_num) ⟨960, by rfl⟩ (by norm_num))
theorem R73781 : Reach 73781 := rs (se 5 (by rfl) ⟨3458, by rfl⟩) (B 6917 (by norm_num) ⟨3458, by rfl⟩ (by norm_num))
theorem R41017 : Reach 41017 := rs (se 2 (by rfl) ⟨15381, by rfl⟩) (B 30763 (by norm_num) ⟨15381, by rfl⟩ (by norm_num))
theorem R41053 : Reach 41053 := rs (se 3 (by rfl) ⟨7697, by rfl⟩) (B 15395 (by norm_num) ⟨7697, by rfl⟩ (by norm_num))
theorem R41089 : Reach 41089 := rs (se 2 (by rfl) ⟨15408, by rfl⟩) (B 30817 (by norm_num) ⟨15408, by rfl⟩ (by norm_num))
theorem R41105 : Reach 41105 := rs (se 2 (by rfl) ⟨15414, by rfl⟩) (B 30829 (by norm_num) ⟨15414, by rfl⟩ (by norm_num))
theorem R41125 : Reach 41125 := rs (se 4 (by rfl) ⟨3855, by rfl⟩) (B 7711 (by norm_num) ⟨3855, by rfl⟩ (by norm_num))
theorem R139445 : Reach 139445 := rs (se 5 (by rfl) ⟨6536, by rfl⟩) (B 13073 (by norm_num) ⟨6536, by rfl⟩ (by norm_num))
theorem R41161 : Reach 41161 := rs (se 2 (by rfl) ⟨15435, by rfl⟩) (B 30871 (by norm_num) ⟨15435, by rfl⟩ (by norm_num))
theorem R41197 : Reach 41197 := rs (se 3 (by rfl) ⟨7724, by rfl⟩) (B 15449 (by norm_num) ⟨7724, by rfl⟩ (by norm_num))
theorem R41233 : Reach 41233 := rs (se 2 (by rfl) ⟨15462, by rfl⟩) (B 30925 (by norm_num) ⟨15462, by rfl⟩ (by norm_num))
theorem R41257 : Reach 41257 := rs (se 2 (by rfl) ⟨15471, by rfl⟩) (B 30943 (by norm_num) ⟨15471, by rfl⟩ (by norm_num))
theorem R41269 : Reach 41269 := rs (se 5 (by rfl) ⟨1934, by rfl⟩) (B 3869 (by norm_num) ⟨1934, by rfl⟩ (by norm_num))
theorem R139589 : Reach 139589 := rs (se 4 (by rfl) ⟨13086, by rfl⟩) (B 26173 (by norm_num) ⟨13086, by rfl⟩ (by norm_num))
theorem R41305 : Reach 41305 := rs (se 2 (by rfl) ⟨15489, by rfl⟩) (B 30979 (by norm_num) ⟨15489, by rfl⟩ (by norm_num))
theorem R41341 : Reach 41341 := rs (se 3 (by rfl) ⟨7751, by rfl⟩) (B 15503 (by norm_num) ⟨7751, by rfl⟩ (by norm_num))
theorem R41357 : Reach 41357 := rs (se 3 (by rfl) ⟨7754, by rfl⟩) (B 15509 (by norm_num) ⟨7754, by rfl⟩ (by norm_num))
theorem R41377 : Reach 41377 := rs (se 2 (by rfl) ⟨15516, by rfl⟩) (B 31033 (by norm_num) ⟨15516, by rfl⟩ (by norm_num))
theorem R41401 : Reach 41401 := rs (se 2 (by rfl) ⟨15525, by rfl⟩) (B 31051 (by norm_num) ⟨15525, by rfl⟩ (by norm_num))
theorem R41413 : Reach 41413 := rs (se 4 (by rfl) ⟨3882, by rfl⟩) (B 7765 (by norm_num) ⟨3882, by rfl⟩ (by norm_num))
theorem R41449 : Reach 41449 := rs (se 2 (by rfl) ⟨15543, by rfl⟩) (B 31087 (by norm_num) ⟨15543, by rfl⟩ (by norm_num))
theorem R139781 : Reach 139781 := rs (se 4 (by rfl) ⟨13104, by rfl⟩) (B 26209 (by norm_num) ⟨13104, by rfl⟩ (by norm_num))
theorem R41485 : Reach 41485 := rs (se 3 (by rfl) ⟨7778, by rfl⟩) (B 15557 (by norm_num) ⟨7778, by rfl⟩ (by norm_num))
theorem R41521 : Reach 41521 := rs (se 2 (by rfl) ⟨15570, by rfl⟩) (B 31141 (by norm_num) ⟨15570, by rfl⟩ (by norm_num))
theorem R41557 : Reach 41557 := rs (se 8 (by rfl) ⟨243, by rfl⟩) (B 487 (by norm_num) ⟨243, by rfl⟩ (by norm_num))
theorem R139877 : Reach 139877 := rs (se 4 (by rfl) ⟨13113, by rfl⟩) (B 26227 (by norm_num) ⟨13113, by rfl⟩ (by norm_num))
theorem R41593 : Reach 41593 := rs (se 2 (by rfl) ⟨15597, by rfl⟩) (B 31195 (by norm_num) ⟨15597, by rfl⟩ (by norm_num))
theorem R139909 : Reach 139909 := rs (se 4 (by rfl) ⟨13116, by rfl⟩) (B 26233 (by norm_num) ⟨13116, by rfl⟩ (by norm_num))
theorem R41629 : Reach 41629 := rs (se 3 (by rfl) ⟨7805, by rfl⟩) (B 15611 (by norm_num) ⟨7805, by rfl⟩ (by norm_num))
theorem R107189 : Reach 107189 := rs (se 5 (by rfl) ⟨5024, by rfl⟩) (B 10049 (by norm_num) ⟨5024, by rfl⟩ (by norm_num))
theorem R41665 : Reach 41665 := rs (se 2 (by rfl) ⟨15624, by rfl⟩) (B 31249 (by norm_num) ⟨15624, by rfl⟩ (by norm_num))
theorem R107237 : Reach 107237 := rs (se 4 (by rfl) ⟨10053, by rfl⟩) (B 20107 (by norm_num) ⟨10053, by rfl⟩ (by norm_num))
theorem R41701 : Reach 41701 := rs (se 4 (by rfl) ⟨3909, by rfl⟩) (B 7819 (by norm_num) ⟨3909, by rfl⟩ (by norm_num))
theorem R41737 : Reach 41737 := rs (se 2 (by rfl) ⟨15651, by rfl⟩) (B 31303 (by norm_num) ⟨15651, by rfl⟩ (by norm_num))
theorem R41773 : Reach 41773 := rs (se 3 (by rfl) ⟨7832, by rfl⟩) (B 15665 (by norm_num) ⟨7832, by rfl⟩ (by norm_num))
theorem R41809 : Reach 41809 := rs (se 2 (by rfl) ⟨15678, by rfl⟩) (B 31357 (by norm_num) ⟨15678, by rfl⟩ (by norm_num))
theorem R41845 : Reach 41845 := rs (se 5 (by rfl) ⟨1961, by rfl⟩) (B 3923 (by norm_num) ⟨1961, by rfl⟩ (by norm_num))
theorem R41881 : Reach 41881 := rs (se 2 (by rfl) ⟨15705, by rfl⟩) (B 31411 (by norm_num) ⟨15705, by rfl⟩ (by norm_num))
theorem R41917 : Reach 41917 := rs (se 3 (by rfl) ⟨7859, by rfl⟩) (B 15719 (by norm_num) ⟨7859, by rfl⟩ (by norm_num))
theorem R41953 : Reach 41953 := rs (se 2 (by rfl) ⟨15732, by rfl⟩) (B 31465 (by norm_num) ⟨15732, by rfl⟩ (by norm_num))
theorem R41989 : Reach 41989 := rs (se 4 (by rfl) ⟨3936, by rfl⟩) (B 7873 (by norm_num) ⟨3936, by rfl⟩ (by norm_num))
theorem R42025 : Reach 42025 := rs (se 2 (by rfl) ⟨15759, by rfl⟩) (B 31519 (by norm_num) ⟨15759, by rfl⟩ (by norm_num))
theorem R42061 : Reach 42061 := rs (se 3 (by rfl) ⟨7886, by rfl⟩) (B 15773 (by norm_num) ⟨7886, by rfl⟩ (by norm_num))
theorem R42097 : Reach 42097 := rs (se 2 (by rfl) ⟨15786, by rfl⟩) (B 31573 (by norm_num) ⟨15786, by rfl⟩ (by norm_num))
theorem R42133 : Reach 42133 := rs (se 6 (by rfl) ⟨987, by rfl⟩) (B 1975 (by norm_num) ⟨987, by rfl⟩ (by norm_num))
theorem R42169 : Reach 42169 := rs (se 2 (by rfl) ⟨15813, by rfl⟩) (B 31627 (by norm_num) ⟨15813, by rfl⟩ (by norm_num))
theorem R42205 : Reach 42205 := rs (se 3 (by rfl) ⟨7913, by rfl⟩) (B 15827 (by norm_num) ⟨7913, by rfl⟩ (by norm_num))
theorem R42221 : Reach 42221 := rs (se 3 (by rfl) ⟨7916, by rfl⟩) (B 15833 (by norm_num) ⟨7916, by rfl⟩ (by norm_num))
theorem R42241 : Reach 42241 := rs (se 2 (by rfl) ⟨15840, by rfl⟩) (B 31681 (by norm_num) ⟨15840, by rfl⟩ (by norm_num))
theorem R42277 : Reach 42277 := rs (se 4 (by rfl) ⟨3963, by rfl⟩) (B 7927 (by norm_num) ⟨3963, by rfl⟩ (by norm_num))
theorem R42313 : Reach 42313 := rs (se 2 (by rfl) ⟨15867, by rfl⟩) (B 31735 (by norm_num) ⟨15867, by rfl⟩ (by norm_num))
theorem R599381 : Reach 599381 := rs (se 12 (by rfl) ⟨219, by rfl⟩) (B 439 (by norm_num) ⟨219, by rfl⟩ (by norm_num))
theorem R42349 : Reach 42349 := rs (se 3 (by rfl) ⟨7940, by rfl⟩) (B 15881 (by norm_num) ⟨7940, by rfl⟩ (by norm_num))
theorem R42385 : Reach 42385 := rs (se 2 (by rfl) ⟨15894, by rfl⟩) (B 31789 (by norm_num) ⟨15894, by rfl⟩ (by norm_num))
theorem R42421 : Reach 42421 := rs (se 5 (by rfl) ⟨1988, by rfl⟩) (B 3977 (by norm_num) ⟨1988, by rfl⟩ (by norm_num))
theorem R42457 : Reach 42457 := rs (se 2 (by rfl) ⟨15921, by rfl⟩) (B 31843 (by norm_num) ⟨15921, by rfl⟩ (by norm_num))
theorem R42493 : Reach 42493 := rs (se 3 (by rfl) ⟨7967, by rfl⟩) (B 15935 (by norm_num) ⟨7967, by rfl⟩ (by norm_num))
theorem R42529 : Reach 42529 := rs (se 2 (by rfl) ⟨15948, by rfl⟩) (B 31897 (by norm_num) ⟨15948, by rfl⟩ (by norm_num))
theorem R42553 : Reach 42553 := rs (se 2 (by rfl) ⟨15957, by rfl⟩) (B 31915 (by norm_num) ⟨15957, by rfl⟩ (by norm_num))
theorem R42565 : Reach 42565 := rs (se 4 (by rfl) ⟨3990, by rfl⟩) (B 7981 (by norm_num) ⟨3990, by rfl⟩ (by norm_num))
theorem R42601 : Reach 42601 := rs (se 2 (by rfl) ⟨15975, by rfl⟩) (B 31951 (by norm_num) ⟨15975, by rfl⟩ (by norm_num))
theorem R42637 : Reach 42637 := rs (se 3 (by rfl) ⟨7994, by rfl⟩) (B 15989 (by norm_num) ⟨7994, by rfl⟩ (by norm_num))
theorem R42673 : Reach 42673 := rs (se 2 (by rfl) ⟨16002, by rfl⟩) (B 32005 (by norm_num) ⟨16002, by rfl⟩ (by norm_num))
theorem R173765 : Reach 173765 := rs (se 4 (by rfl) ⟨16290, by rfl⟩) (B 32581 (by norm_num) ⟨16290, by rfl⟩ (by norm_num))
theorem R42709 : Reach 42709 := rs (se 7 (by rfl) ⟨500, by rfl⟩) (B 1001 (by norm_num) ⟨500, by rfl⟩ (by norm_num))
theorem R42745 : Reach 42745 := rs (se 2 (by rfl) ⟨16029, by rfl⟩) (B 32059 (by norm_num) ⟨16029, by rfl⟩ (by norm_num))
theorem R42749 : Reach 42749 := rs (se 3 (by rfl) ⟨8015, by rfl⟩) (B 16031 (by norm_num) ⟨8015, by rfl⟩ (by norm_num))
theorem R141061 : Reach 141061 := rs (se 4 (by rfl) ⟨13224, by rfl⟩) (B 26449 (by norm_num) ⟨13224, by rfl⟩ (by norm_num))
theorem R42781 : Reach 42781 := rs (se 3 (by rfl) ⟨8021, by rfl⟩) (B 16043 (by norm_num) ⟨8021, by rfl⟩ (by norm_num))
theorem R108341 : Reach 108341 := rs (se 5 (by rfl) ⟨5078, by rfl⟩) (B 10157 (by norm_num) ⟨5078, by rfl⟩ (by norm_num))
theorem R42805 : Reach 42805 := rs (se 5 (by rfl) ⟨2006, by rfl⟩) (B 4013 (by norm_num) ⟨2006, by rfl⟩ (by norm_num))
theorem R42817 : Reach 42817 := rs (se 2 (by rfl) ⟨16056, by rfl⟩) (B 32113 (by norm_num) ⟨16056, by rfl⟩ (by norm_num))
theorem R42853 : Reach 42853 := rs (se 4 (by rfl) ⟨4017, by rfl⟩) (B 8035 (by norm_num) ⟨4017, by rfl⟩ (by norm_num))
theorem R42889 : Reach 42889 := rs (se 2 (by rfl) ⟨16083, by rfl⟩) (B 32167 (by norm_num) ⟨16083, by rfl⟩ (by norm_num))
theorem R141221 : Reach 141221 := rs (se 4 (by rfl) ⟨13239, by rfl⟩) (B 26479 (by norm_num) ⟨13239, by rfl⟩ (by norm_num))
theorem R42925 : Reach 42925 := rs (se 3 (by rfl) ⟨8048, by rfl⟩) (B 16097 (by norm_num) ⟨8048, by rfl⟩ (by norm_num))
theorem R108485 : Reach 108485 := rs (se 4 (by rfl) ⟨10170, by rfl⟩) (B 20341 (by norm_num) ⟨10170, by rfl⟩ (by norm_num))
theorem R42961 : Reach 42961 := rs (se 2 (by rfl) ⟨16110, by rfl⟩) (B 32221 (by norm_num) ⟨16110, by rfl⟩ (by norm_num))
theorem R42997 : Reach 42997 := rs (se 5 (by rfl) ⟨2015, by rfl⟩) (B 4031 (by norm_num) ⟨2015, by rfl⟩ (by norm_num))
theorem R43033 : Reach 43033 := rs (se 2 (by rfl) ⟨16137, by rfl⟩) (B 32275 (by norm_num) ⟨16137, by rfl⟩ (by norm_num))
theorem R141365 : Reach 141365 := rs (se 5 (by rfl) ⟨6626, by rfl⟩) (B 13253 (by norm_num) ⟨6626, by rfl⟩ (by norm_num))
theorem R43069 : Reach 43069 := rs (se 3 (by rfl) ⟨8075, by rfl⟩) (B 16151 (by norm_num) ⟨8075, by rfl⟩ (by norm_num))
theorem R43105 : Reach 43105 := rs (se 2 (by rfl) ⟨16164, by rfl⟩) (B 32329 (by norm_num) ⟨16164, by rfl⟩ (by norm_num))
theorem R43133 : Reach 43133 := rs (se 3 (by rfl) ⟨8087, by rfl⟩) (B 16175 (by norm_num) ⟨8087, by rfl⟩ (by norm_num))
theorem R43141 : Reach 43141 := rs (se 4 (by rfl) ⟨4044, by rfl⟩) (B 8089 (by norm_num) ⟨4044, by rfl⟩ (by norm_num))
theorem R43177 : Reach 43177 := rs (se 2 (by rfl) ⟨16191, by rfl⟩) (B 32383 (by norm_num) ⟨16191, by rfl⟩ (by norm_num))
theorem R43213 : Reach 43213 := rs (se 3 (by rfl) ⟨8102, by rfl⟩) (B 16205 (by norm_num) ⟨8102, by rfl⟩ (by norm_num))
theorem R43249 : Reach 43249 := rs (se 2 (by rfl) ⟨16218, by rfl⟩) (B 32437 (by norm_num) ⟨16218, by rfl⟩ (by norm_num))
theorem R43285 : Reach 43285 := rs (se 6 (by rfl) ⟨1014, by rfl⟩) (B 2029 (by norm_num) ⟨1014, by rfl⟩ (by norm_num))
theorem R43321 : Reach 43321 := rs (se 2 (by rfl) ⟨16245, by rfl⟩) (B 32491 (by norm_num) ⟨16245, by rfl⟩ (by norm_num))
theorem R43357 : Reach 43357 := rs (se 3 (by rfl) ⟨8129, by rfl⟩) (B 16259 (by norm_num) ⟨8129, by rfl⟩ (by norm_num))
theorem R43393 : Reach 43393 := rs (se 2 (by rfl) ⟨16272, by rfl⟩) (B 32545 (by norm_num) ⟨16272, by rfl⟩ (by norm_num))
theorem R43429 : Reach 43429 := rs (se 4 (by rfl) ⟨4071, by rfl⟩) (B 8143 (by norm_num) ⟨4071, by rfl⟩ (by norm_num))
theorem R43465 : Reach 43465 := rs (se 2 (by rfl) ⟨16299, by rfl⟩) (B 32599 (by norm_num) ⟨16299, by rfl⟩ (by norm_num))
theorem R43501 : Reach 43501 := rs (se 3 (by rfl) ⟨8156, by rfl⟩) (B 16313 (by norm_num) ⟨8156, by rfl⟩ (by norm_num))
theorem R43537 : Reach 43537 := rs (se 2 (by rfl) ⟨16326, by rfl⟩) (B 32653 (by norm_num) ⟨16326, by rfl⟩ (by norm_num))
theorem R43573 : Reach 43573 := rs (se 5 (by rfl) ⟨2042, by rfl⟩) (B 4085 (by norm_num) ⟨2042, by rfl⟩ (by norm_num))
theorem R76349 : Reach 76349 := rs (se 3 (by rfl) ⟨14315, by rfl⟩) (B 28631 (by norm_num) ⟨14315, by rfl⟩ (by norm_num))
theorem R43609 : Reach 43609 := rs (se 2 (by rfl) ⟨16353, by rfl⟩) (B 32707 (by norm_num) ⟨16353, by rfl⟩ (by norm_num))
theorem R43645 : Reach 43645 := rs (se 3 (by rfl) ⟨8183, by rfl⟩) (B 16367 (by norm_num) ⟨8183, by rfl⟩ (by norm_num))
theorem R404117 : Reach 404117 := rs (se 6 (by rfl) ⟨9471, by rfl⟩) (B 18943 (by norm_num) ⟨9471, by rfl⟩ (by norm_num))
theorem R43681 : Reach 43681 := rs (se 2 (by rfl) ⟨16380, by rfl⟩) (B 32761 (by norm_num) ⟨16380, by rfl⟩ (by norm_num))
theorem R76477 : Reach 76477 := rs (se 3 (by rfl) ⟨14339, by rfl⟩) (B 28679 (by norm_num) ⟨14339, by rfl⟩ (by norm_num))
theorem R43717 : Reach 43717 := rs (se 4 (by rfl) ⟨4098, by rfl⟩) (B 8197 (by norm_num) ⟨4098, by rfl⟩ (by norm_num))
theorem R43753 : Reach 43753 := rs (se 2 (by rfl) ⟨16407, by rfl⟩) (B 32815 (by norm_num) ⟨16407, by rfl⟩ (by norm_num))
theorem R43789 : Reach 43789 := rs (se 3 (by rfl) ⟨8210, by rfl⟩) (B 16421 (by norm_num) ⟨8210, by rfl⟩ (by norm_num))
theorem R43825 : Reach 43825 := rs (se 2 (by rfl) ⟨16434, by rfl⟩) (B 32869 (by norm_num) ⟨16434, by rfl⟩ (by norm_num))
theorem R43861 : Reach 43861 := rs (se 9 (by rfl) ⟨128, by rfl⟩) (B 257 (by norm_num) ⟨128, by rfl⟩ (by norm_num))
theorem R43897 : Reach 43897 := rs (se 2 (by rfl) ⟨16461, by rfl⟩) (B 32923 (by norm_num) ⟨16461, by rfl⟩ (by norm_num))
theorem R43933 : Reach 43933 := rs (se 3 (by rfl) ⟨8237, by rfl⟩) (B 16475 (by norm_num) ⟨8237, by rfl⟩ (by norm_num))
theorem R43969 : Reach 43969 := rs (se 2 (by rfl) ⟨16488, by rfl⟩) (B 32977 (by norm_num) ⟨16488, by rfl⟩ (by norm_num))
theorem R44005 : Reach 44005 := rs (se 4 (by rfl) ⟨4125, by rfl⟩) (B 8251 (by norm_num) ⟨4125, by rfl⟩ (by norm_num))
theorem R109669 : Reach 109669 := rs (se 4 (by rfl) ⟨10281, by rfl⟩) (B 20563 (by norm_num) ⟨10281, by rfl⟩ (by norm_num))
theorem R109829 : Reach 109829 := rs (se 4 (by rfl) ⟨10296, by rfl⟩) (B 20593 (by norm_num) ⟨10296, by rfl⟩ (by norm_num))
theorem R44321 : Reach 44321 := rs (se 2 (by rfl) ⟨16620, by rfl⟩) (B 33241 (by norm_num) ⟨16620, by rfl⟩ (by norm_num))
theorem R44345 : Reach 44345 := rs (se 2 (by rfl) ⟨16629, by rfl⟩) (B 33259 (by norm_num) ⟨16629, by rfl⟩ (by norm_num))
theorem R44489 : Reach 44489 := rs (se 2 (by rfl) ⟨16683, by rfl⟩) (B 33367 (by norm_num) ⟨16683, by rfl⟩ (by norm_num))
theorem R142805 : Reach 142805 := rs (se 7 (by rfl) ⟨1673, by rfl⟩) (B 3347 (by norm_num) ⟨1673, by rfl⟩ (by norm_num))
theorem R110069 : Reach 110069 := rs (se 5 (by rfl) ⟨5159, by rfl⟩) (B 10319 (by norm_num) ⟨5159, by rfl⟩ (by norm_num))
theorem R44545 : Reach 44545 := rs (se 2 (by rfl) ⟨16704, by rfl⟩) (B 33409 (by norm_num) ⟨16704, by rfl⟩ (by norm_num))
theorem R77365 : Reach 77365 := rs (se 5 (by rfl) ⟨3626, by rfl⟩) (B 7253 (by norm_num) ⟨3626, by rfl⟩ (by norm_num))
theorem R44641 : Reach 44641 := rs (se 2 (by rfl) ⟨16740, by rfl⟩) (B 33481 (by norm_num) ⟨16740, by rfl⟩ (by norm_num))
theorem R44653 : Reach 44653 := rs (se 3 (by rfl) ⟨8372, by rfl⟩) (B 16745 (by norm_num) ⟨8372, by rfl⟩ (by norm_num))
theorem R77429 : Reach 77429 := rs (se 5 (by rfl) ⟨3629, by rfl⟩) (B 7259 (by norm_num) ⟨3629, by rfl⟩ (by norm_num))
theorem R77453 : Reach 77453 := rs (se 3 (by rfl) ⟨14522, by rfl⟩) (B 29045 (by norm_num) ⟨14522, by rfl⟩ (by norm_num))
theorem R44693 : Reach 44693 := rs (se 6 (by rfl) ⟨1047, by rfl⟩) (B 2095 (by norm_num) ⟨1047, by rfl⟩ (by norm_num))
theorem R110261 : Reach 110261 := rs (se 5 (by rfl) ⟨5168, by rfl⟩) (B 10337 (by norm_num) ⟨5168, by rfl⟩ (by norm_num))
theorem R44813 : Reach 44813 := rs (se 3 (by rfl) ⟨8402, by rfl⟩) (B 16805 (by norm_num) ⟨8402, by rfl⟩ (by norm_num))
theorem R306965 : Reach 306965 := rs (se 6 (by rfl) ⟨7194, by rfl⟩) (B 14389 (by norm_num) ⟨7194, by rfl⟩ (by norm_num))
theorem R44825 : Reach 44825 := rs (se 2 (by rfl) ⟨16809, by rfl⟩) (B 33619 (by norm_num) ⟨16809, by rfl⟩ (by norm_num))
theorem R44869 : Reach 44869 := rs (se 4 (by rfl) ⟨4206, by rfl⟩) (B 8413 (by norm_num) ⟨4206, by rfl⟩ (by norm_num))
theorem R44941 : Reach 44941 := rs (se 3 (by rfl) ⟨8426, by rfl⟩) (B 16853 (by norm_num) ⟨8426, by rfl⟩ (by norm_num))
theorem R44965 : Reach 44965 := rs (se 4 (by rfl) ⟨4215, by rfl⟩) (B 8431 (by norm_num) ⟨4215, by rfl⟩ (by norm_num))
theorem R45037 : Reach 45037 := rs (se 3 (by rfl) ⟨8444, by rfl⟩) (B 16889 (by norm_num) ⟨8444, by rfl⟩ (by norm_num))
theorem R77861 : Reach 77861 := rs (se 4 (by rfl) ⟨7299, by rfl⟩) (B 14599 (by norm_num) ⟨7299, by rfl⟩ (by norm_num))
theorem R45137 : Reach 45137 := rs (se 2 (by rfl) ⟨16926, by rfl⟩) (B 33853 (by norm_num) ⟨16926, by rfl⟩ (by norm_num))
theorem R143477 : Reach 143477 := rs (se 5 (by rfl) ⟨6725, by rfl⟩) (B 13451 (by norm_num) ⟨6725, by rfl⟩ (by norm_num))
theorem R45181 : Reach 45181 := rs (se 3 (by rfl) ⟨8471, by rfl⟩) (B 16943 (by norm_num) ⟨8471, by rfl⟩ (by norm_num))
theorem R45193 : Reach 45193 := rs (se 2 (by rfl) ⟨16947, by rfl⟩) (B 33895 (by norm_num) ⟨16947, by rfl⟩ (by norm_num))
theorem R45289 : Reach 45289 := rs (se 2 (by rfl) ⟨16983, by rfl⟩) (B 33967 (by norm_num) ⟨16983, by rfl⟩ (by norm_num))
theorem R45293 : Reach 45293 := rs (se 3 (by rfl) ⟨8492, by rfl⟩) (B 16985 (by norm_num) ⟨8492, by rfl⟩ (by norm_num))
theorem R78173 : Reach 78173 := rs (se 3 (by rfl) ⟨14657, by rfl⟩) (B 29315 (by norm_num) ⟨14657, by rfl⟩ (by norm_num))
theorem R143765 : Reach 143765 := rs (se 6 (by rfl) ⟨3369, by rfl⟩) (B 6739 (by norm_num) ⟨3369, by rfl⟩ (by norm_num))
theorem R45461 : Reach 45461 := rs (se 6 (by rfl) ⟨1065, by rfl⟩) (B 2131 (by norm_num) ⟨1065, by rfl⟩ (by norm_num))
theorem R307637 : Reach 307637 := rs (se 5 (by rfl) ⟨14420, by rfl⟩) (B 28841 (by norm_num) ⟨14420, by rfl⟩ (by norm_num))
theorem R45517 : Reach 45517 := rs (se 3 (by rfl) ⟨8534, by rfl⟩) (B 17069 (by norm_num) ⟨8534, by rfl⟩ (by norm_num))
theorem R209429 : Reach 209429 := rs (se 6 (by rfl) ⟨4908, by rfl⟩) (B 9817 (by norm_num) ⟨4908, by rfl⟩ (by norm_num))
theorem R45613 : Reach 45613 := rs (se 3 (by rfl) ⟨8552, by rfl⟩) (B 17105 (by norm_num) ⟨8552, by rfl⟩ (by norm_num))
theorem R78413 : Reach 78413 := rs (se 3 (by rfl) ⟨14702, by rfl⟩) (B 29405 (by norm_num) ⟨14702, by rfl⟩ (by norm_num))
theorem R111253 : Reach 111253 := rs (se 6 (by rfl) ⟨2607, by rfl⟩) (B 5215 (by norm_num) ⟨2607, by rfl⟩ (by norm_num))
theorem R45785 : Reach 45785 := rs (se 2 (by rfl) ⟨17169, by rfl⟩) (B 34339 (by norm_num) ⟨17169, by rfl⟩ (by norm_num))
theorem R45841 : Reach 45841 := rs (se 2 (by rfl) ⟨17190, by rfl⟩) (B 34381 (by norm_num) ⟨17190, by rfl⟩ (by norm_num))
theorem R45937 : Reach 45937 := rs (se 2 (by rfl) ⟨17226, by rfl⟩) (B 34453 (by norm_num) ⟨17226, by rfl⟩ (by norm_num))
theorem R78725 : Reach 78725 := rs (se 4 (by rfl) ⟨7380, by rfl⟩) (B 14761 (by norm_num) ⟨7380, by rfl⟩ (by norm_num))
theorem R78869 : Reach 78869 := rs (se 6 (by rfl) ⟨1848, by rfl⟩) (B 3697 (by norm_num) ⟨1848, by rfl⟩ (by norm_num))
theorem R46109 : Reach 46109 := rs (se 3 (by rfl) ⟨8645, by rfl⟩) (B 17291 (by norm_num) ⟨8645, by rfl⟩ (by norm_num))
theorem R504917 : Reach 504917 := rs (se 8 (by rfl) ⟨2958, by rfl⟩) (B 5917 (by norm_num) ⟨2958, by rfl⟩ (by norm_num))
theorem R46165 : Reach 46165 := rs (se 8 (by rfl) ⟨270, by rfl⟩) (B 541 (by norm_num) ⟨270, by rfl⟩ (by norm_num))
theorem R46261 : Reach 46261 := rs (se 5 (by rfl) ⟨2168, by rfl⟩) (B 4337 (by norm_num) ⟨2168, by rfl⟩ (by norm_num))
theorem R79037 : Reach 79037 := rs (se 3 (by rfl) ⟨14819, by rfl⟩) (B 29639 (by norm_num) ⟨14819, by rfl⟩ (by norm_num))
theorem R79109 : Reach 79109 := rs (se 4 (by rfl) ⟨7416, by rfl⟩) (B 14833 (by norm_num) ⟨7416, by rfl⟩ (by norm_num))
theorem R46345 : Reach 46345 := rs (se 2 (by rfl) ⟨17379, by rfl⟩) (B 34759 (by norm_num) ⟨17379, by rfl⟩ (by norm_num))
theorem R79181 : Reach 79181 := rs (se 3 (by rfl) ⟨14846, by rfl⟩) (B 29693 (by norm_num) ⟨14846, by rfl⟩ (by norm_num))
theorem R46433 : Reach 46433 := rs (se 2 (by rfl) ⟨17412, by rfl⟩) (B 34825 (by norm_num) ⟨17412, by rfl⟩ (by norm_num))
theorem R79253 : Reach 79253 := rs (se 6 (by rfl) ⟨1857, by rfl⟩) (B 3715 (by norm_num) ⟨1857, by rfl⟩ (by norm_num))
theorem R46489 : Reach 46489 := rs (se 2 (by rfl) ⟨17433, by rfl⟩) (B 34867 (by norm_num) ⟨17433, by rfl⟩ (by norm_num))
theorem R79325 : Reach 79325 := rs (se 3 (by rfl) ⟨14873, by rfl⟩) (B 29747 (by norm_num) ⟨14873, by rfl⟩ (by norm_num))
theorem R46585 : Reach 46585 := rs (se 2 (by rfl) ⟨17469, by rfl⟩) (B 34939 (by norm_num) ⟨17469, by rfl⟩ (by norm_num))
theorem R79397 : Reach 79397 := rs (se 4 (by rfl) ⟨7443, by rfl⟩) (B 14887 (by norm_num) ⟨7443, by rfl⟩ (by norm_num))
theorem R144949 : Reach 144949 := rs (se 5 (by rfl) ⟨6794, by rfl⟩) (B 13589 (by norm_num) ⟨6794, by rfl⟩ (by norm_num))
theorem R79469 : Reach 79469 := rs (se 3 (by rfl) ⟨14900, by rfl⟩) (B 29801 (by norm_num) ⟨14900, by rfl⟩ (by norm_num))
theorem R46757 : Reach 46757 := rs (se 4 (by rfl) ⟨4383, by rfl⟩) (B 8767 (by norm_num) ⟨4383, by rfl⟩ (by norm_num))
theorem R79541 : Reach 79541 := rs (se 5 (by rfl) ⟨3728, by rfl⟩) (B 7457 (by norm_num) ⟨3728, by rfl⟩ (by norm_num))
theorem R210613 : Reach 210613 := rs (se 5 (by rfl) ⟨9872, by rfl⟩) (B 19745 (by norm_num) ⟨9872, by rfl⟩ (by norm_num))
theorem R46813 : Reach 46813 := rs (se 3 (by rfl) ⟨8777, by rfl⟩) (B 17555 (by norm_num) ⟨8777, by rfl⟩ (by norm_num))
theorem R46837 : Reach 46837 := rs (se 5 (by rfl) ⟨2195, by rfl⟩) (B 4391 (by norm_num) ⟨2195, by rfl⟩ (by norm_num))
theorem R79613 : Reach 79613 := rs (se 3 (by rfl) ⟨14927, by rfl⟩) (B 29855 (by norm_num) ⟨14927, by rfl⟩ (by norm_num))
theorem R46901 : Reach 46901 := rs (se 5 (by rfl) ⟨2198, by rfl⟩) (B 4397 (by norm_num) ⟨2198, by rfl⟩ (by norm_num))
theorem R46909 : Reach 46909 := rs (se 3 (by rfl) ⟨8795, by rfl⟩) (B 17591 (by norm_num) ⟨8795, by rfl⟩ (by norm_num))
theorem R79685 : Reach 79685 := rs (se 4 (by rfl) ⟨7470, by rfl⟩) (B 14941 (by norm_num) ⟨7470, by rfl⟩ (by norm_num))
theorem R145253 : Reach 145253 := rs (se 4 (by rfl) ⟨13617, by rfl⟩) (B 27235 (by norm_num) ⟨13617, by rfl⟩ (by norm_num))
theorem R178037 : Reach 178037 := rs (se 5 (by rfl) ⟨8345, by rfl⟩) (B 16691 (by norm_num) ⟨8345, by rfl⟩ (by norm_num))
theorem R79757 : Reach 79757 := rs (se 3 (by rfl) ⟨14954, by rfl⟩) (B 29909 (by norm_num) ⟨14954, by rfl⟩ (by norm_num))
theorem R79829 : Reach 79829 := rs (se 7 (by rfl) ⟨935, by rfl⟩) (B 1871 (by norm_num) ⟨935, by rfl⟩ (by norm_num))
theorem R79901 : Reach 79901 := rs (se 3 (by rfl) ⟨14981, by rfl⟩) (B 29963 (by norm_num) ⟨14981, by rfl⟩ (by norm_num))
theorem R276533 : Reach 276533 := rs (se 5 (by rfl) ⟨12962, by rfl⟩) (B 25925 (by norm_num) ⟨12962, by rfl⟩ (by norm_num))
theorem R79973 : Reach 79973 := rs (se 4 (by rfl) ⟨7497, by rfl⟩) (B 14995 (by norm_num) ⟨7497, by rfl⟩ (by norm_num))
theorem R80045 : Reach 80045 := rs (se 3 (by rfl) ⟨15008, by rfl⟩) (B 30017 (by norm_num) ⟨15008, by rfl⟩ (by norm_num))
theorem R80117 : Reach 80117 := rs (se 5 (by rfl) ⟨3755, by rfl⟩) (B 7511 (by norm_num) ⟨3755, by rfl⟩ (by norm_num))
theorem R47405 : Reach 47405 := rs (se 3 (by rfl) ⟨8888, by rfl⟩) (B 17777 (by norm_num) ⟨8888, by rfl⟩ (by norm_num))
theorem R80189 : Reach 80189 := rs (se 3 (by rfl) ⟨15035, by rfl⟩) (B 30071 (by norm_num) ⟨15035, by rfl⟩ (by norm_num))
theorem R47461 : Reach 47461 := rs (se 4 (by rfl) ⟨4449, by rfl⟩) (B 8899 (by norm_num) ⟨4449, by rfl⟩ (by norm_num))
theorem R80261 : Reach 80261 := rs (se 4 (by rfl) ⟨7524, by rfl⟩) (B 15049 (by norm_num) ⟨7524, by rfl⟩ (by norm_num))
theorem R47509 : Reach 47509 := rs (se 6 (by rfl) ⟨1113, by rfl⟩) (B 2227 (by norm_num) ⟨1113, by rfl⟩ (by norm_num))
theorem R47557 : Reach 47557 := rs (se 4 (by rfl) ⟨4458, by rfl⟩) (B 8917 (by norm_num) ⟨4458, by rfl⟩ (by norm_num))
theorem R80333 : Reach 80333 := rs (se 3 (by rfl) ⟨15062, by rfl⟩) (B 30125 (by norm_num) ⟨15062, by rfl⟩ (by norm_num))
theorem R80365 : Reach 80365 := rs (se 3 (by rfl) ⟨15068, by rfl⟩) (B 30137 (by norm_num) ⟨15068, by rfl⟩ (by norm_num))
theorem R80405 : Reach 80405 := rs (se 6 (by rfl) ⟨1884, by rfl⟩) (B 3769 (by norm_num) ⟨1884, by rfl⟩ (by norm_num))
theorem R80477 : Reach 80477 := rs (se 3 (by rfl) ⟨15089, by rfl⟩) (B 30179 (by norm_num) ⟨15089, by rfl⟩ (by norm_num))
theorem R80509 : Reach 80509 := rs (se 3 (by rfl) ⟨15095, by rfl⟩) (B 30191 (by norm_num) ⟨15095, by rfl⟩ (by norm_num))
theorem R277141 : Reach 277141 := rs (se 6 (by rfl) ⟨6495, by rfl⟩) (B 12991 (by norm_num) ⟨6495, by rfl⟩ (by norm_num))
theorem R80549 : Reach 80549 := rs (se 4 (by rfl) ⟨7551, by rfl⟩) (B 15103 (by norm_num) ⟨7551, by rfl⟩ (by norm_num))
theorem R80621 : Reach 80621 := rs (se 3 (by rfl) ⟨15116, by rfl⟩) (B 30233 (by norm_num) ⟨15116, by rfl⟩ (by norm_num))
theorem R80693 : Reach 80693 := rs (se 5 (by rfl) ⟨3782, by rfl⟩) (B 7565 (by norm_num) ⟨3782, by rfl⟩ (by norm_num))
theorem R80765 : Reach 80765 := rs (se 3 (by rfl) ⟨15143, by rfl⟩) (B 30287 (by norm_num) ⟨15143, by rfl⟩ (by norm_num))
theorem R48053 : Reach 48053 := rs (se 5 (by rfl) ⟨2252, by rfl⟩) (B 4505 (by norm_num) ⟨2252, by rfl⟩ (by norm_num))
theorem R48061 : Reach 48061 := rs (se 3 (by rfl) ⟨9011, by rfl⟩) (B 18023 (by norm_num) ⟨9011, by rfl⟩ (by norm_num))
theorem R80837 : Reach 80837 := rs (se 4 (by rfl) ⟨7578, by rfl⟩) (B 15157 (by norm_num) ⟨7578, by rfl⟩ (by norm_num))
theorem R48109 : Reach 48109 := rs (se 3 (by rfl) ⟨9020, by rfl⟩) (B 18041 (by norm_num) ⟨9020, by rfl⟩ (by norm_num))
theorem R80885 : Reach 80885 := rs (se 5 (by rfl) ⟨3791, by rfl⟩) (B 7583 (by norm_num) ⟨3791, by rfl⟩ (by norm_num))
theorem R80909 : Reach 80909 := rs (se 3 (by rfl) ⟨15170, by rfl⟩) (B 30341 (by norm_num) ⟨15170, by rfl⟩ (by norm_num))
theorem R113717 : Reach 113717 := rs (se 5 (by rfl) ⟨5330, by rfl⟩) (B 10661 (by norm_num) ⟨5330, by rfl⟩ (by norm_num))
theorem R48205 : Reach 48205 := rs (se 3 (by rfl) ⟨9038, by rfl⟩) (B 18077 (by norm_num) ⟨9038, by rfl⟩ (by norm_num))
theorem R80981 : Reach 80981 := rs (se 8 (by rfl) ⟨474, by rfl⟩) (B 949 (by norm_num) ⟨474, by rfl⟩ (by norm_num))
theorem R179333 : Reach 179333 := rs (se 4 (by rfl) ⟨16812, by rfl⟩) (B 33625 (by norm_num) ⟨16812, by rfl⟩ (by norm_num))
theorem R81053 : Reach 81053 := rs (se 3 (by rfl) ⟨15197, by rfl⟩) (B 30395 (by norm_num) ⟨15197, by rfl⟩ (by norm_num))
theorem R113845 : Reach 113845 := rs (se 5 (by rfl) ⟨5336, by rfl⟩) (B 10673 (by norm_num) ⟨5336, by rfl⟩ (by norm_num))
theorem R81125 : Reach 81125 := rs (se 4 (by rfl) ⟨7605, by rfl⟩) (B 15211 (by norm_num) ⟨7605, by rfl⟩ (by norm_num))
theorem R81197 : Reach 81197 := rs (se 3 (by rfl) ⟨15224, by rfl⟩) (B 30449 (by norm_num) ⟨15224, by rfl⟩ (by norm_num))
theorem R81253 : Reach 81253 := rs (se 4 (by rfl) ⟨7617, by rfl⟩) (B 15235 (by norm_num) ⟨7617, by rfl⟩ (by norm_num))
theorem R81269 : Reach 81269 := rs (se 5 (by rfl) ⟨3809, by rfl⟩) (B 7619 (by norm_num) ⟨3809, by rfl⟩ (by norm_num))
theorem R114101 : Reach 114101 := rs (se 5 (by rfl) ⟨5348, by rfl⟩) (B 10697 (by norm_num) ⟨5348, by rfl⟩ (by norm_num))
theorem R81341 : Reach 81341 := rs (se 3 (by rfl) ⟨15251, by rfl⟩) (B 30503 (by norm_num) ⟨15251, by rfl⟩ (by norm_num))
theorem R81413 : Reach 81413 := rs (se 4 (by rfl) ⟨7632, by rfl⟩) (B 15265 (by norm_num) ⟨7632, by rfl⟩ (by norm_num))
theorem R48701 : Reach 48701 := rs (se 3 (by rfl) ⟨9131, by rfl⟩) (B 18263 (by norm_num) ⟨9131, by rfl⟩ (by norm_num))
theorem R81485 : Reach 81485 := rs (se 3 (by rfl) ⟨15278, by rfl⟩) (B 30557 (by norm_num) ⟨15278, by rfl⟩ (by norm_num))
theorem R48757 : Reach 48757 := rs (se 5 (by rfl) ⟨2285, by rfl⟩) (B 4571 (by norm_num) ⟨2285, by rfl⟩ (by norm_num))
theorem R81557 : Reach 81557 := rs (se 6 (by rfl) ⟨1911, by rfl⟩) (B 3823 (by norm_num) ⟨1911, by rfl⟩ (by norm_num))
theorem R114389 : Reach 114389 := rs (se 7 (by rfl) ⟨1340, by rfl⟩) (B 2681 (by norm_num) ⟨1340, by rfl⟩ (by norm_num))
theorem R704213 : Reach 704213 := rs (se 7 (by rfl) ⟨8252, by rfl⟩) (B 16505 (by norm_num) ⟨8252, by rfl⟩ (by norm_num))
theorem R48853 : Reach 48853 := rs (se 7 (by rfl) ⟨572, by rfl⟩) (B 1145 (by norm_num) ⟨572, by rfl⟩ (by norm_num))
theorem R81629 : Reach 81629 := rs (se 3 (by rfl) ⟨15305, by rfl⟩) (B 30611 (by norm_num) ⟨15305, by rfl⟩ (by norm_num))
theorem R114437 : Reach 114437 := rs (se 4 (by rfl) ⟨10728, by rfl⟩) (B 21457 (by norm_num) ⟨10728, by rfl⟩ (by norm_num))
theorem R540437 : Reach 540437 := rs (se 6 (by rfl) ⟨12666, by rfl⟩) (B 25333 (by norm_num) ⟨12666, by rfl⟩ (by norm_num))
theorem R81701 : Reach 81701 := rs (se 4 (by rfl) ⟨7659, by rfl⟩) (B 15319 (by norm_num) ⟨7659, by rfl⟩ (by norm_num))
theorem R180053 : Reach 180053 := rs (se 9 (by rfl) ⟨527, by rfl⟩) (B 1055 (by norm_num) ⟨527, by rfl⟩ (by norm_num))
theorem R81773 : Reach 81773 := rs (se 3 (by rfl) ⟨15332, by rfl⟩) (B 30665 (by norm_num) ⟨15332, by rfl⟩ (by norm_num))
theorem R147365 : Reach 147365 := rs (se 4 (by rfl) ⟨13815, by rfl⟩) (B 27631 (by norm_num) ⟨13815, by rfl⟩ (by norm_num))
theorem R49069 : Reach 49069 := rs (se 3 (by rfl) ⟨9200, by rfl⟩) (B 18401 (by norm_num) ⟨9200, by rfl⟩ (by norm_num))
theorem R81845 : Reach 81845 := rs (se 5 (by rfl) ⟨3836, by rfl⟩) (B 7673 (by norm_num) ⟨3836, by rfl⟩ (by norm_num))
theorem R81917 : Reach 81917 := rs (se 3 (by rfl) ⟨15359, by rfl⟩) (B 30719 (by norm_num) ⟨15359, by rfl⟩ (by norm_num))
theorem R81989 : Reach 81989 := rs (se 4 (by rfl) ⟨7686, by rfl⟩) (B 15373 (by norm_num) ⟨7686, by rfl⟩ (by norm_num))
theorem R82061 : Reach 82061 := rs (se 3 (by rfl) ⟨15386, by rfl⟩) (B 30773 (by norm_num) ⟨15386, by rfl⟩ (by norm_num))
theorem R49333 : Reach 49333 := rs (se 5 (by rfl) ⟨2312, by rfl⟩) (B 4625 (by norm_num) ⟨2312, by rfl⟩ (by norm_num))
theorem R147653 : Reach 147653 := rs (se 4 (by rfl) ⟨13842, by rfl⟩) (B 27685 (by norm_num) ⟨13842, by rfl⟩ (by norm_num))
theorem R49349 : Reach 49349 := rs (se 4 (by rfl) ⟨4626, by rfl⟩) (B 9253 (by norm_num) ⟨4626, by rfl⟩ (by norm_num))
theorem R82133 : Reach 82133 := rs (se 7 (by rfl) ⟨962, by rfl⟩) (B 1925 (by norm_num) ⟨962, by rfl⟩ (by norm_num))
theorem R49405 : Reach 49405 := rs (se 3 (by rfl) ⟨9263, by rfl⟩) (B 18527 (by norm_num) ⟨9263, by rfl⟩ (by norm_num))
theorem R82205 : Reach 82205 := rs (se 3 (by rfl) ⟨15413, by rfl⟩) (B 30827 (by norm_num) ⟨15413, by rfl⟩ (by norm_num))
theorem R49501 : Reach 49501 := rs (se 3 (by rfl) ⟨9281, by rfl⟩) (B 18563 (by norm_num) ⟨9281, by rfl⟩ (by norm_num))
theorem R82277 : Reach 82277 := rs (se 4 (by rfl) ⟨7713, by rfl⟩) (B 15427 (by norm_num) ⟨7713, by rfl⟩ (by norm_num))
theorem R82301 : Reach 82301 := rs (se 3 (by rfl) ⟨15431, by rfl⟩) (B 30863 (by norm_num) ⟨15431, by rfl⟩ (by norm_num))
theorem R180629 : Reach 180629 := rs (se 6 (by rfl) ⟨4233, by rfl⟩) (B 8467 (by norm_num) ⟨4233, by rfl⟩ (by norm_num))
theorem R82325 : Reach 82325 := rs (se 6 (by rfl) ⟨1929, by rfl⟩) (B 3859 (by norm_num) ⟨1929, by rfl⟩ (by norm_num))
theorem R82349 : Reach 82349 := rs (se 3 (by rfl) ⟨15440, by rfl⟩) (B 30881 (by norm_num) ⟨15440, by rfl⟩ (by norm_num))
theorem R213461 : Reach 213461 := rs (se 7 (by rfl) ⟨2501, by rfl⟩) (B 5003 (by norm_num) ⟨2501, by rfl⟩ (by norm_num))
theorem R82421 : Reach 82421 := rs (se 5 (by rfl) ⟨3863, by rfl⟩) (B 7727 (by norm_num) ⟨3863, by rfl⟩ (by norm_num))
theorem R82493 : Reach 82493 := rs (se 3 (by rfl) ⟨15467, by rfl⟩) (B 30935 (by norm_num) ⟨15467, by rfl⟩ (by norm_num))
theorem R82565 : Reach 82565 := rs (se 4 (by rfl) ⟨7740, by rfl⟩) (B 15481 (by norm_num) ⟨7740, by rfl⟩ (by norm_num))
theorem R82637 : Reach 82637 := rs (se 3 (by rfl) ⟨15494, by rfl⟩) (B 30989 (by norm_num) ⟨15494, by rfl⟩ (by norm_num))
theorem R82709 : Reach 82709 := rs (se 6 (by rfl) ⟨1938, by rfl⟩) (B 3877 (by norm_num) ⟨1938, by rfl⟩ (by norm_num))
theorem R82757 : Reach 82757 := rs (se 4 (by rfl) ⟨7758, by rfl⟩) (B 15517 (by norm_num) ⟨7758, by rfl⟩ (by norm_num))
theorem R50005 : Reach 50005 := rs (se 9 (by rfl) ⟨146, by rfl⟩) (B 293 (by norm_num) ⟨146, by rfl⟩ (by norm_num))
theorem R82781 : Reach 82781 := rs (se 3 (by rfl) ⟨15521, by rfl⟩) (B 31043 (by norm_num) ⟨15521, by rfl⟩ (by norm_num))
theorem R82853 : Reach 82853 := rs (se 4 (by rfl) ⟨7767, by rfl⟩) (B 15535 (by norm_num) ⟨7767, by rfl⟩ (by norm_num))
theorem R82901 : Reach 82901 := rs (se 7 (by rfl) ⟨971, by rfl⟩) (B 1943 (by norm_num) ⟨971, by rfl⟩ (by norm_num))
theorem R82925 : Reach 82925 := rs (se 3 (by rfl) ⟨15548, by rfl⟩) (B 31097 (by norm_num) ⟨15548, by rfl⟩ (by norm_num))
theorem R82997 : Reach 82997 := rs (se 5 (by rfl) ⟨3890, by rfl⟩) (B 7781 (by norm_num) ⟨3890, by rfl⟩ (by norm_num))
theorem R83069 : Reach 83069 := rs (se 3 (by rfl) ⟨15575, by rfl⟩) (B 31151 (by norm_num) ⟨15575, by rfl⟩ (by norm_num))
theorem R83141 : Reach 83141 := rs (se 4 (by rfl) ⟨7794, by rfl⟩) (B 15589 (by norm_num) ⟨7794, by rfl⟩ (by norm_num))
theorem R83213 : Reach 83213 := rs (se 3 (by rfl) ⟨15602, by rfl⟩) (B 31205 (by norm_num) ⟨15602, by rfl⟩ (by norm_num))
theorem R83261 : Reach 83261 := rs (se 3 (by rfl) ⟨15611, by rfl⟩) (B 31223 (by norm_num) ⟨15611, by rfl⟩ (by norm_num))
theorem R83285 : Reach 83285 := rs (se 12 (by rfl) ⟨30, by rfl⟩) (B 61 (by norm_num) ⟨30, by rfl⟩ (by norm_num))
theorem R83357 : Reach 83357 := rs (se 3 (by rfl) ⟨15629, by rfl⟩) (B 31259 (by norm_num) ⟨15629, by rfl⟩ (by norm_num))
theorem R83429 : Reach 83429 := rs (se 4 (by rfl) ⟨7821, by rfl⟩) (B 15643 (by norm_num) ⟨7821, by rfl⟩ (by norm_num))
theorem R83501 : Reach 83501 := rs (se 3 (by rfl) ⟨15656, by rfl⟩) (B 31313 (by norm_num) ⟨15656, by rfl⟩ (by norm_num))
theorem R50797 : Reach 50797 := rs (se 3 (by rfl) ⟨9524, by rfl⟩) (B 19049 (by norm_num) ⟨9524, by rfl⟩ (by norm_num))
theorem R83573 : Reach 83573 := rs (se 5 (by rfl) ⟨3917, by rfl⟩) (B 7835 (by norm_num) ⟨3917, by rfl⟩ (by norm_num))
theorem R181925 : Reach 181925 := rs (se 4 (by rfl) ⟨17055, by rfl⟩) (B 34111 (by norm_num) ⟨17055, by rfl⟩ (by norm_num))
theorem R83645 : Reach 83645 := rs (se 3 (by rfl) ⟨15683, by rfl⟩) (B 31367 (by norm_num) ⟨15683, by rfl⟩ (by norm_num))
theorem R83717 : Reach 83717 := rs (se 4 (by rfl) ⟨7848, by rfl⟩) (B 15697 (by norm_num) ⟨7848, by rfl⟩ (by norm_num))
theorem R116549 : Reach 116549 := rs (se 4 (by rfl) ⟨10926, by rfl⟩) (B 21853 (by norm_num) ⟨10926, by rfl⟩ (by norm_num))
theorem R83789 : Reach 83789 := rs (se 3 (by rfl) ⟨15710, by rfl⟩) (B 31421 (by norm_num) ⟨15710, by rfl⟩ (by norm_num))
theorem R345941 : Reach 345941 := rs (se 9 (by rfl) ⟨1013, by rfl⟩) (B 2027 (by norm_num) ⟨1013, by rfl⟩ (by norm_num))
theorem R83861 : Reach 83861 := rs (se 6 (by rfl) ⟨1965, by rfl⟩) (B 3931 (by norm_num) ⟨1965, by rfl⟩ (by norm_num))
theorem R51133 : Reach 51133 := rs (se 3 (by rfl) ⟨9587, by rfl⟩) (B 19175 (by norm_num) ⟨9587, by rfl⟩ (by norm_num))
theorem R83933 : Reach 83933 := rs (se 3 (by rfl) ⟨15737, by rfl⟩) (B 31475 (by norm_num) ⟨15737, by rfl⟩ (by norm_num))
theorem R84005 : Reach 84005 := rs (se 4 (by rfl) ⟨7875, by rfl⟩) (B 15751 (by norm_num) ⟨7875, by rfl⟩ (by norm_num))
theorem R84077 : Reach 84077 := rs (se 3 (by rfl) ⟨15764, by rfl⟩) (B 31529 (by norm_num) ⟨15764, by rfl⟩ (by norm_num))
theorem R51349 : Reach 51349 := rs (se 6 (by rfl) ⟨1203, by rfl⟩) (B 2407 (by norm_num) ⟨1203, by rfl⟩ (by norm_num))
theorem R84149 : Reach 84149 := rs (se 5 (by rfl) ⟨3944, by rfl⟩) (B 7889 (by norm_num) ⟨3944, by rfl⟩ (by norm_num))
theorem R84221 : Reach 84221 := rs (se 3 (by rfl) ⟨15791, by rfl⟩) (B 31583 (by norm_num) ⟨15791, by rfl⟩ (by norm_num))
theorem R84293 : Reach 84293 := rs (se 4 (by rfl) ⟨7902, by rfl⟩) (B 15805 (by norm_num) ⟨7902, by rfl⟩ (by norm_num))
theorem R84365 : Reach 84365 := rs (se 3 (by rfl) ⟨15818, by rfl⟩) (B 31637 (by norm_num) ⟨15818, by rfl⟩ (by norm_num))
theorem R84437 : Reach 84437 := rs (se 7 (by rfl) ⟨989, by rfl⟩) (B 1979 (by norm_num) ⟨989, by rfl⟩ (by norm_num))
theorem R51725 : Reach 51725 := rs (se 3 (by rfl) ⟨9698, by rfl⟩) (B 19397 (by norm_num) ⟨9698, by rfl⟩ (by norm_num))
theorem R84509 : Reach 84509 := rs (se 3 (by rfl) ⟨15845, by rfl⟩) (B 31691 (by norm_num) ⟨15845, by rfl⟩ (by norm_num))
theorem R182837 : Reach 182837 := rs (se 5 (by rfl) ⟨8570, by rfl⟩) (B 17141 (by norm_num) ⟨8570, by rfl⟩ (by norm_num))
theorem R84581 : Reach 84581 := rs (se 4 (by rfl) ⟨7929, by rfl⟩) (B 15859 (by norm_num) ⟨7929, by rfl⟩ (by norm_num))
theorem R84653 : Reach 84653 := rs (se 3 (by rfl) ⟨15872, by rfl⟩) (B 31745 (by norm_num) ⟨15872, by rfl⟩ (by norm_num))
theorem R84725 : Reach 84725 := rs (se 5 (by rfl) ⟨3971, by rfl⟩) (B 7943 (by norm_num) ⟨3971, by rfl⟩ (by norm_num))
theorem R84797 : Reach 84797 := rs (se 3 (by rfl) ⟨15899, by rfl⟩) (B 31799 (by norm_num) ⟨15899, by rfl⟩ (by norm_num))
theorem R84845 : Reach 84845 := rs (se 3 (by rfl) ⟨15908, by rfl⟩) (B 31817 (by norm_num) ⟨15908, by rfl⟩ (by norm_num))
theorem R52093 : Reach 52093 := rs (se 3 (by rfl) ⟨9767, by rfl⟩) (B 19535 (by norm_num) ⟨9767, by rfl⟩ (by norm_num))
theorem R84869 : Reach 84869 := rs (se 4 (by rfl) ⟨7956, by rfl⟩) (B 15913 (by norm_num) ⟨7956, by rfl⟩ (by norm_num))
theorem R183221 : Reach 183221 := rs (se 5 (by rfl) ⟨8588, by rfl⟩) (B 17177 (by norm_num) ⟨8588, by rfl⟩ (by norm_num))
theorem R84941 : Reach 84941 := rs (se 3 (by rfl) ⟨15926, by rfl⟩) (B 31853 (by norm_num) ⟨15926, by rfl⟩ (by norm_num))
theorem R52213 : Reach 52213 := rs (se 5 (by rfl) ⟨2447, by rfl⟩) (B 4895 (by norm_num) ⟨2447, by rfl⟩ (by norm_num))
theorem R85013 : Reach 85013 := rs (se 6 (by rfl) ⟨1992, by rfl⟩) (B 3985 (by norm_num) ⟨1992, by rfl⟩ (by norm_num))
theorem R85085 : Reach 85085 := rs (se 3 (by rfl) ⟨15953, by rfl⟩) (B 31907 (by norm_num) ⟨15953, by rfl⟩ (by norm_num))
theorem R117893 : Reach 117893 := rs (se 4 (by rfl) ⟨11052, by rfl⟩) (B 22105 (by norm_num) ⟨11052, by rfl⟩ (by norm_num))
theorem R85157 : Reach 85157 := rs (se 4 (by rfl) ⟨7983, by rfl⟩) (B 15967 (by norm_num) ⟨7983, by rfl⟩ (by norm_num))
theorem R85229 : Reach 85229 := rs (se 3 (by rfl) ⟨15980, by rfl⟩) (B 31961 (by norm_num) ⟨15980, by rfl⟩ (by norm_num))
theorem R85301 : Reach 85301 := rs (se 5 (by rfl) ⟨3998, by rfl⟩) (B 7997 (by norm_num) ⟨3998, by rfl⟩ (by norm_num))
theorem R85373 : Reach 85373 := rs (se 3 (by rfl) ⟨16007, by rfl⟩) (B 32015 (by norm_num) ⟨16007, by rfl⟩ (by norm_num))
theorem R85445 : Reach 85445 := rs (se 4 (by rfl) ⟨8010, by rfl⟩) (B 16021 (by norm_num) ⟨8010, by rfl⟩ (by norm_num))
theorem R52685 : Reach 52685 := rs (se 3 (by rfl) ⟨9878, by rfl⟩) (B 19757 (by norm_num) ⟨9878, by rfl⟩ (by norm_num))
theorem R314837 : Reach 314837 := rs (se 7 (by rfl) ⟨3689, by rfl⟩) (B 7379 (by norm_num) ⟨3689, by rfl⟩ (by norm_num))
theorem R52709 : Reach 52709 := rs (se 4 (by rfl) ⟨4941, by rfl⟩) (B 9883 (by norm_num) ⟨4941, by rfl⟩ (by norm_num))
theorem R52733 : Reach 52733 := rs (se 3 (by rfl) ⟨9887, by rfl⟩) (B 19775 (by norm_num) ⟨9887, by rfl⟩ (by norm_num))
theorem R85517 : Reach 85517 := rs (se 3 (by rfl) ⟨16034, by rfl⟩) (B 32069 (by norm_num) ⟨16034, by rfl⟩ (by norm_num))
theorem R52757 : Reach 52757 := rs (se 6 (by rfl) ⟨1236, by rfl⟩) (B 2473 (by norm_num) ⟨1236, by rfl⟩ (by norm_num))
theorem R52781 : Reach 52781 := rs (se 3 (by rfl) ⟨9896, by rfl⟩) (B 19793 (by norm_num) ⟨9896, by rfl⟩ (by norm_num))
theorem R52805 : Reach 52805 := rs (se 4 (by rfl) ⟨4950, by rfl⟩) (B 9901 (by norm_num) ⟨4950, by rfl⟩ (by norm_num))
theorem R151109 : Reach 151109 := rs (se 4 (by rfl) ⟨14166, by rfl⟩) (B 28333 (by norm_num) ⟨14166, by rfl⟩ (by norm_num))
theorem R52813 : Reach 52813 := rs (se 3 (by rfl) ⟨9902, by rfl⟩) (B 19805 (by norm_num) ⟨9902, by rfl⟩ (by norm_num))
theorem R85589 : Reach 85589 := rs (se 8 (by rfl) ⟨501, by rfl⟩) (B 1003 (by norm_num) ⟨501, by rfl⟩ (by norm_num))
theorem R52829 : Reach 52829 := rs (se 3 (by rfl) ⟨9905, by rfl⟩) (B 19811 (by norm_num) ⟨9905, by rfl⟩ (by norm_num))
theorem R52853 : Reach 52853 := rs (se 5 (by rfl) ⟨2477, by rfl⟩) (B 4955 (by norm_num) ⟨2477, by rfl⟩ (by norm_num))
theorem R52877 : Reach 52877 := rs (se 3 (by rfl) ⟨9914, by rfl⟩) (B 19829 (by norm_num) ⟨9914, by rfl⟩ (by norm_num))
theorem R85661 : Reach 85661 := rs (se 3 (by rfl) ⟨16061, by rfl⟩) (B 32123 (by norm_num) ⟨16061, by rfl⟩ (by norm_num))
theorem R52901 : Reach 52901 := rs (se 4 (by rfl) ⟨4959, by rfl⟩) (B 9919 (by norm_num) ⟨4959, by rfl⟩ (by norm_num))
theorem R52925 : Reach 52925 := rs (se 3 (by rfl) ⟨9923, by rfl⟩) (B 19847 (by norm_num) ⟨9923, by rfl⟩ (by norm_num))
theorem R52949 : Reach 52949 := rs (se 7 (by rfl) ⟨620, by rfl⟩) (B 1241 (by norm_num) ⟨620, by rfl⟩ (by norm_num))
theorem R85733 : Reach 85733 := rs (se 4 (by rfl) ⟨8037, by rfl⟩) (B 16075 (by norm_num) ⟨8037, by rfl⟩ (by norm_num))
theorem R52973 : Reach 52973 := rs (se 3 (by rfl) ⟨9932, by rfl⟩) (B 19865 (by norm_num) ⟨9932, by rfl⟩ (by norm_num))
theorem R52997 : Reach 52997 := rs (se 4 (by rfl) ⟨4968, by rfl⟩) (B 9937 (by norm_num) ⟨4968, by rfl⟩ (by norm_num))
theorem R53021 : Reach 53021 := rs (se 3 (by rfl) ⟨9941, by rfl⟩) (B 19883 (by norm_num) ⟨9941, by rfl⟩ (by norm_num))
theorem R85805 : Reach 85805 := rs (se 3 (by rfl) ⟨16088, by rfl⟩) (B 32177 (by norm_num) ⟨16088, by rfl⟩ (by norm_num))
theorem R53045 : Reach 53045 := rs (se 5 (by rfl) ⟨2486, by rfl⟩) (B 4973 (by norm_num) ⟨2486, by rfl⟩ (by norm_num))
theorem R53069 : Reach 53069 := rs (se 3 (by rfl) ⟨9950, by rfl⟩) (B 19901 (by norm_num) ⟨9950, by rfl⟩ (by norm_num))
theorem R2117461 : Reach 2117461 := rs (se 9 (by rfl) ⟨6203, by rfl⟩) (B 12407 (by norm_num) ⟨6203, by rfl⟩ (by norm_num))
theorem R53093 : Reach 53093 := rs (se 4 (by rfl) ⟨4977, by rfl⟩) (B 9955 (by norm_num) ⟨4977, by rfl⟩ (by norm_num))
theorem R85877 : Reach 85877 := rs (se 5 (by rfl) ⟨4025, by rfl⟩) (B 8051 (by norm_num) ⟨4025, by rfl⟩ (by norm_num))
theorem R53117 : Reach 53117 := rs (se 3 (by rfl) ⟨9959, by rfl⟩) (B 19919 (by norm_num) ⟨9959, by rfl⟩ (by norm_num))
theorem R53141 : Reach 53141 := rs (se 6 (by rfl) ⟨1245, by rfl⟩) (B 2491 (by norm_num) ⟨1245, by rfl⟩ (by norm_num))
theorem R53149 : Reach 53149 := rs (se 3 (by rfl) ⟨9965, by rfl⟩) (B 19931 (by norm_num) ⟨9965, by rfl⟩ (by norm_num))
theorem R53165 : Reach 53165 := rs (se 3 (by rfl) ⟨9968, by rfl⟩) (B 19937 (by norm_num) ⟨9968, by rfl⟩ (by norm_num))
theorem R85949 : Reach 85949 := rs (se 3 (by rfl) ⟨16115, by rfl⟩) (B 32231 (by norm_num) ⟨16115, by rfl⟩ (by norm_num))
theorem R53189 : Reach 53189 := rs (se 4 (by rfl) ⟨4986, by rfl⟩) (B 9973 (by norm_num) ⟨4986, by rfl⟩ (by norm_num))
theorem R53213 : Reach 53213 := rs (se 3 (by rfl) ⟨9977, by rfl⟩) (B 19955 (by norm_num) ⟨9977, by rfl⟩ (by norm_num))
theorem R53237 : Reach 53237 := rs (se 5 (by rfl) ⟨2495, by rfl⟩) (B 4991 (by norm_num) ⟨2495, by rfl⟩ (by norm_num))
theorem R86021 : Reach 86021 := rs (se 4 (by rfl) ⟨8064, by rfl⟩) (B 16129 (by norm_num) ⟨8064, by rfl⟩ (by norm_num))
theorem R53261 : Reach 53261 := rs (se 3 (by rfl) ⟨9986, by rfl⟩) (B 19973 (by norm_num) ⟨9986, by rfl⟩ (by norm_num))
theorem R53285 : Reach 53285 := rs (se 4 (by rfl) ⟨4995, by rfl⟩) (B 9991 (by norm_num) ⟨4995, by rfl⟩ (by norm_num))
theorem R53309 : Reach 53309 := rs (se 3 (by rfl) ⟨9995, by rfl⟩) (B 19991 (by norm_num) ⟨9995, by rfl⟩ (by norm_num))
theorem R118853 : Reach 118853 := rs (se 4 (by rfl) ⟨11142, by rfl⟩) (B 22285 (by norm_num) ⟨11142, by rfl⟩ (by norm_num))
theorem R86093 : Reach 86093 := rs (se 3 (by rfl) ⟨16142, by rfl⟩) (B 32285 (by norm_num) ⟨16142, by rfl⟩ (by norm_num))
theorem R1527893 : Reach 1527893 := rs (se 8 (by rfl) ⟨8952, by rfl⟩) (B 17905 (by norm_num) ⟨8952, by rfl⟩ (by norm_num))
theorem R53333 : Reach 53333 := rs (se 8 (by rfl) ⟨312, by rfl⟩) (B 625 (by norm_num) ⟨312, by rfl⟩ (by norm_num))
theorem R53357 : Reach 53357 := rs (se 3 (by rfl) ⟨10004, by rfl⟩) (B 20009 (by norm_num) ⟨10004, by rfl⟩ (by norm_num))
theorem R53381 : Reach 53381 := rs (se 4 (by rfl) ⟨5004, by rfl⟩) (B 10009 (by norm_num) ⟨5004, by rfl⟩ (by norm_num))
theorem R86165 : Reach 86165 := rs (se 6 (by rfl) ⟨2019, by rfl⟩) (B 4039 (by norm_num) ⟨2019, by rfl⟩ (by norm_num))
theorem R53405 : Reach 53405 := rs (se 3 (by rfl) ⟨10013, by rfl⟩) (B 20027 (by norm_num) ⟨10013, by rfl⟩ (by norm_num))
theorem R53429 : Reach 53429 := rs (se 5 (by rfl) ⟨2504, by rfl⟩) (B 5009 (by norm_num) ⟨2504, by rfl⟩ (by norm_num))
theorem R250037 : Reach 250037 := rs (se 5 (by rfl) ⟨11720, by rfl⟩) (B 23441 (by norm_num) ⟨11720, by rfl⟩ (by norm_num))
theorem R184517 : Reach 184517 := rs (se 4 (by rfl) ⟨17298, by rfl⟩) (B 34597 (by norm_num) ⟨17298, by rfl⟩ (by norm_num))
theorem R53453 : Reach 53453 := rs (se 3 (by rfl) ⟨10022, by rfl⟩) (B 20045 (by norm_num) ⟨10022, by rfl⟩ (by norm_num))
theorem R86237 : Reach 86237 := rs (se 3 (by rfl) ⟨16169, by rfl⟩) (B 32339 (by norm_num) ⟨16169, by rfl⟩ (by norm_num))
theorem R53477 : Reach 53477 := rs (se 4 (by rfl) ⟨5013, by rfl⟩) (B 10027 (by norm_num) ⟨5013, by rfl⟩ (by norm_num))
theorem R53501 : Reach 53501 := rs (se 3 (by rfl) ⟨10031, by rfl⟩) (B 20063 (by norm_num) ⟨10031, by rfl⟩ (by norm_num))
theorem R53525 : Reach 53525 := rs (se 6 (by rfl) ⟨1254, by rfl⟩) (B 2509 (by norm_num) ⟨1254, by rfl⟩ (by norm_num))
theorem R86309 : Reach 86309 := rs (se 4 (by rfl) ⟨8091, by rfl⟩) (B 16183 (by norm_num) ⟨8091, by rfl⟩ (by norm_num))
theorem R53549 : Reach 53549 := rs (se 3 (by rfl) ⟨10040, by rfl⟩) (B 20081 (by norm_num) ⟨10040, by rfl⟩ (by norm_num))
theorem R53573 : Reach 53573 := rs (se 4 (by rfl) ⟨5022, by rfl⟩) (B 10045 (by norm_num) ⟨5022, by rfl⟩ (by norm_num))
theorem R86341 : Reach 86341 := rs (se 4 (by rfl) ⟨8094, by rfl⟩) (B 16189 (by norm_num) ⟨8094, by rfl⟩ (by norm_num))
theorem R53597 : Reach 53597 := rs (se 3 (by rfl) ⟨10049, by rfl⟩) (B 20099 (by norm_num) ⟨10049, by rfl⟩ (by norm_num))
theorem R86381 : Reach 86381 := rs (se 3 (by rfl) ⟨16196, by rfl⟩) (B 32393 (by norm_num) ⟨16196, by rfl⟩ (by norm_num))
theorem R53621 : Reach 53621 := rs (se 5 (by rfl) ⟨2513, by rfl⟩) (B 5027 (by norm_num) ⟨2513, by rfl⟩ (by norm_num))
theorem R250229 : Reach 250229 := rs (se 5 (by rfl) ⟨11729, by rfl⟩) (B 23459 (by norm_num) ⟨11729, by rfl⟩ (by norm_num))
theorem R53645 : Reach 53645 := rs (se 3 (by rfl) ⟨10058, by rfl⟩) (B 20117 (by norm_num) ⟨10058, by rfl⟩ (by norm_num))
theorem R53669 : Reach 53669 := rs (se 4 (by rfl) ⟨5031, by rfl⟩) (B 10063 (by norm_num) ⟨5031, by rfl⟩ (by norm_num))
theorem R86453 : Reach 86453 := rs (se 5 (by rfl) ⟨4052, by rfl⟩) (B 8105 (by norm_num) ⟨4052, by rfl⟩ (by norm_num))
theorem R53693 : Reach 53693 := rs (se 3 (by rfl) ⟨10067, by rfl⟩) (B 20135 (by norm_num) ⟨10067, by rfl⟩ (by norm_num))
theorem R53717 : Reach 53717 := rs (se 7 (by rfl) ⟨629, by rfl⟩) (B 1259 (by norm_num) ⟨629, by rfl⟩ (by norm_num))
theorem R53741 : Reach 53741 := rs (se 3 (by rfl) ⟨10076, by rfl⟩) (B 20153 (by norm_num) ⟨10076, by rfl⟩ (by norm_num))
theorem R119285 : Reach 119285 := rs (se 5 (by rfl) ⟨5591, by rfl⟩) (B 11183 (by norm_num) ⟨5591, by rfl⟩ (by norm_num))
theorem R86525 : Reach 86525 := rs (se 3 (by rfl) ⟨16223, by rfl⟩) (B 32447 (by norm_num) ⟨16223, by rfl⟩ (by norm_num))
theorem R53765 : Reach 53765 := rs (se 4 (by rfl) ⟨5040, by rfl⟩) (B 10081 (by norm_num) ⟨5040, by rfl⟩ (by norm_num))
theorem R53789 : Reach 53789 := rs (se 3 (by rfl) ⟨10085, by rfl⟩) (B 20171 (by norm_num) ⟨10085, by rfl⟩ (by norm_num))
theorem R53813 : Reach 53813 := rs (se 5 (by rfl) ⟨2522, by rfl⟩) (B 5045 (by norm_num) ⟨2522, by rfl⟩ (by norm_num))
theorem R53821 : Reach 53821 := rs (se 3 (by rfl) ⟨10091, by rfl⟩) (B 20183 (by norm_num) ⟨10091, by rfl⟩ (by norm_num))
theorem R86597 : Reach 86597 := rs (se 4 (by rfl) ⟨8118, by rfl⟩) (B 16237 (by norm_num) ⟨8118, by rfl⟩ (by norm_num))
theorem R53837 : Reach 53837 := rs (se 3 (by rfl) ⟨10094, by rfl⟩) (B 20189 (by norm_num) ⟨10094, by rfl⟩ (by norm_num))
theorem R53861 : Reach 53861 := rs (se 4 (by rfl) ⟨5049, by rfl⟩) (B 10099 (by norm_num) ⟨5049, by rfl⟩ (by norm_num))
theorem R316021 : Reach 316021 := rs (se 5 (by rfl) ⟨14813, by rfl⟩) (B 29627 (by norm_num) ⟨14813, by rfl⟩ (by norm_num))
theorem R53885 : Reach 53885 := rs (se 3 (by rfl) ⟨10103, by rfl⟩) (B 20207 (by norm_num) ⟨10103, by rfl⟩ (by norm_num))
theorem R86669 : Reach 86669 := rs (se 3 (by rfl) ⟨16250, by rfl⟩) (B 32501 (by norm_num) ⟨16250, by rfl⟩ (by norm_num))
theorem R53909 : Reach 53909 := rs (se 6 (by rfl) ⟨1263, by rfl⟩) (B 2527 (by norm_num) ⟨1263, by rfl⟩ (by norm_num))
theorem R53933 : Reach 53933 := rs (se 3 (by rfl) ⟨10112, by rfl⟩) (B 20225 (by norm_num) ⟨10112, by rfl⟩ (by norm_num))
theorem R53941 : Reach 53941 := rs (se 5 (by rfl) ⟨2528, by rfl⟩) (B 5057 (by norm_num) ⟨2528, by rfl⟩ (by norm_num))
theorem R53957 : Reach 53957 := rs (se 4 (by rfl) ⟨5058, by rfl⟩) (B 10117 (by norm_num) ⟨5058, by rfl⟩ (by norm_num))
theorem R86741 : Reach 86741 := rs (se 7 (by rfl) ⟨1016, by rfl⟩) (B 2033 (by norm_num) ⟨1016, by rfl⟩ (by norm_num))
theorem R53981 : Reach 53981 := rs (se 3 (by rfl) ⟨10121, by rfl⟩) (B 20243 (by norm_num) ⟨10121, by rfl⟩ (by norm_num))
theorem R54005 : Reach 54005 := rs (se 5 (by rfl) ⟨2531, by rfl⟩) (B 5063 (by norm_num) ⟨2531, by rfl⟩ (by norm_num))
theorem R54029 : Reach 54029 := rs (se 3 (by rfl) ⟨10130, by rfl⟩) (B 20261 (by norm_num) ⟨10130, by rfl⟩ (by norm_num))
theorem R54037 : Reach 54037 := rs (se 6 (by rfl) ⟨1266, by rfl⟩) (B 2533 (by norm_num) ⟨1266, by rfl⟩ (by norm_num))
theorem R86813 : Reach 86813 := rs (se 3 (by rfl) ⟨16277, by rfl⟩) (B 32555 (by norm_num) ⟨16277, by rfl⟩ (by norm_num))
theorem R54053 : Reach 54053 := rs (se 4 (by rfl) ⟨5067, by rfl⟩) (B 10135 (by norm_num) ⟨5067, by rfl⟩ (by norm_num))
theorem R54077 : Reach 54077 := rs (se 3 (by rfl) ⟨10139, by rfl⟩) (B 20279 (by norm_num) ⟨10139, by rfl⟩ (by norm_num))
theorem R86845 : Reach 86845 := rs (se 3 (by rfl) ⟨16283, by rfl⟩) (B 32567 (by norm_num) ⟨16283, by rfl⟩ (by norm_num))
theorem R54101 : Reach 54101 := rs (se 9 (by rfl) ⟨158, by rfl⟩) (B 317 (by norm_num) ⟨158, by rfl⟩ (by norm_num))
theorem R86885 : Reach 86885 := rs (se 4 (by rfl) ⟨8145, by rfl⟩) (B 16291 (by norm_num) ⟨8145, by rfl⟩ (by norm_num))
theorem R54125 : Reach 54125 := rs (se 3 (by rfl) ⟨10148, by rfl⟩) (B 20297 (by norm_num) ⟨10148, by rfl⟩ (by norm_num))
theorem R54149 : Reach 54149 := rs (se 4 (by rfl) ⟨5076, by rfl⟩) (B 10153 (by norm_num) ⟨5076, by rfl⟩ (by norm_num))
theorem R54173 : Reach 54173 := rs (se 3 (by rfl) ⟨10157, by rfl⟩) (B 20315 (by norm_num) ⟨10157, by rfl⟩ (by norm_num))
theorem R119717 : Reach 119717 := rs (se 4 (by rfl) ⟨11223, by rfl⟩) (B 22447 (by norm_num) ⟨11223, by rfl⟩ (by norm_num))
theorem R86957 : Reach 86957 := rs (se 3 (by rfl) ⟨16304, by rfl⟩) (B 32609 (by norm_num) ⟨16304, by rfl⟩ (by norm_num))
theorem R54197 : Reach 54197 := rs (se 5 (by rfl) ⟨2540, by rfl⟩) (B 5081 (by norm_num) ⟨2540, by rfl⟩ (by norm_num))
theorem R54221 : Reach 54221 := rs (se 3 (by rfl) ⟨10166, by rfl⟩) (B 20333 (by norm_num) ⟨10166, by rfl⟩ (by norm_num))
theorem R807893 : Reach 807893 := rs (se 7 (by rfl) ⟨9467, by rfl⟩) (B 18935 (by norm_num) ⟨9467, by rfl⟩ (by norm_num))
theorem R54245 : Reach 54245 := rs (se 4 (by rfl) ⟨5085, by rfl⟩) (B 10171 (by norm_num) ⟨5085, by rfl⟩ (by norm_num))
theorem R87029 : Reach 87029 := rs (se 5 (by rfl) ⟨4079, by rfl⟩) (B 8159 (by norm_num) ⟨4079, by rfl⟩ (by norm_num))
theorem R54269 : Reach 54269 := rs (se 3 (by rfl) ⟨10175, by rfl⟩) (B 20351 (by norm_num) ⟨10175, by rfl⟩ (by norm_num))
theorem R54293 : Reach 54293 := rs (se 6 (by rfl) ⟨1272, by rfl⟩) (B 2545 (by norm_num) ⟨1272, by rfl⟩ (by norm_num))
theorem R54317 : Reach 54317 := rs (se 3 (by rfl) ⟨10184, by rfl⟩) (B 20369 (by norm_num) ⟨10184, by rfl⟩ (by norm_num))
theorem R87101 : Reach 87101 := rs (se 3 (by rfl) ⟨16331, by rfl⟩) (B 32663 (by norm_num) ⟨16331, by rfl⟩ (by norm_num))
theorem R54341 : Reach 54341 := rs (se 4 (by rfl) ⟨5094, by rfl⟩) (B 10189 (by norm_num) ⟨5094, by rfl⟩ (by norm_num))
theorem R119893 : Reach 119893 := rs (se 8 (by rfl) ⟨702, by rfl⟩) (B 1405 (by norm_num) ⟨702, by rfl⟩ (by norm_num))
theorem R54365 : Reach 54365 := rs (se 3 (by rfl) ⟨10193, by rfl⟩) (B 20387 (by norm_num) ⟨10193, by rfl⟩ (by norm_num))
theorem R54389 : Reach 54389 := rs (se 5 (by rfl) ⟨2549, by rfl⟩) (B 5099 (by norm_num) ⟨2549, by rfl⟩ (by norm_num))
theorem R87173 : Reach 87173 := rs (se 4 (by rfl) ⟨8172, by rfl⟩) (B 16345 (by norm_num) ⟨8172, by rfl⟩ (by norm_num))
theorem R54413 : Reach 54413 := rs (se 3 (by rfl) ⟨10202, by rfl⟩) (B 20405 (by norm_num) ⟨10202, by rfl⟩ (by norm_num))
theorem R54437 : Reach 54437 := rs (se 4 (by rfl) ⟨5103, by rfl⟩) (B 10207 (by norm_num) ⟨5103, by rfl⟩ (by norm_num))
theorem R54461 : Reach 54461 := rs (se 3 (by rfl) ⟨10211, by rfl⟩) (B 20423 (by norm_num) ⟨10211, by rfl⟩ (by norm_num))
theorem R87245 : Reach 87245 := rs (se 3 (by rfl) ⟨16358, by rfl⟩) (B 32717 (by norm_num) ⟨16358, by rfl⟩ (by norm_num))
theorem R54485 : Reach 54485 := rs (se 7 (by rfl) ⟨638, by rfl⟩) (B 1277 (by norm_num) ⟨638, by rfl⟩ (by norm_num))
theorem R54509 : Reach 54509 := rs (se 3 (by rfl) ⟨10220, by rfl⟩) (B 20441 (by norm_num) ⟨10220, by rfl⟩ (by norm_num))
theorem R54533 : Reach 54533 := rs (se 4 (by rfl) ⟨5112, by rfl⟩) (B 10225 (by norm_num) ⟨5112, by rfl⟩ (by norm_num))
theorem R87317 : Reach 87317 := rs (se 6 (by rfl) ⟨2046, by rfl⟩) (B 4093 (by norm_num) ⟨2046, by rfl⟩ (by norm_num))
theorem R54557 : Reach 54557 := rs (se 3 (by rfl) ⟨10229, by rfl⟩) (B 20459 (by norm_num) ⟨10229, by rfl⟩ (by norm_num))
theorem R54581 : Reach 54581 := rs (se 5 (by rfl) ⟨2558, by rfl⟩) (B 5117 (by norm_num) ⟨2558, by rfl⟩ (by norm_num))
theorem R54605 : Reach 54605 := rs (se 3 (by rfl) ⟨10238, by rfl⟩) (B 20477 (by norm_num) ⟨10238, by rfl⟩ (by norm_num))
theorem R120149 : Reach 120149 := rs (se 15 (by rfl) ⟨5, by rfl⟩) (B 11 (by norm_num) ⟨5, by rfl⟩ (by norm_num))
theorem R87389 : Reach 87389 := rs (se 3 (by rfl) ⟨16385, by rfl⟩) (B 32771 (by norm_num) ⟨16385, by rfl⟩ (by norm_num))
theorem R54629 : Reach 54629 := rs (se 4 (by rfl) ⟨5121, by rfl⟩) (B 10243 (by norm_num) ⟨5121, by rfl⟩ (by norm_num))
theorem R87421 : Reach 87421 := rs (se 3 (by rfl) ⟨16391, by rfl⟩) (B 32783 (by norm_num) ⟨16391, by rfl⟩ (by norm_num))
theorem R54653 : Reach 54653 := rs (se 3 (by rfl) ⟨10247, by rfl⟩) (B 20495 (by norm_num) ⟨10247, by rfl⟩ (by norm_num))
theorem R54677 : Reach 54677 := rs (se 6 (by rfl) ⟨1281, by rfl⟩) (B 2563 (by norm_num) ⟨1281, by rfl⟩ (by norm_num))
theorem R87461 : Reach 87461 := rs (se 4 (by rfl) ⟨8199, by rfl⟩) (B 16399 (by norm_num) ⟨8199, by rfl⟩ (by norm_num))
theorem R54701 : Reach 54701 := rs (se 3 (by rfl) ⟨10256, by rfl⟩) (B 20513 (by norm_num) ⟨10256, by rfl⟩ (by norm_num))
theorem R54725 : Reach 54725 := rs (se 4 (by rfl) ⟨5130, by rfl⟩) (B 10261 (by norm_num) ⟨5130, by rfl⟩ (by norm_num))
theorem R185813 : Reach 185813 := rs (se 7 (by rfl) ⟨2177, by rfl⟩) (B 4355 (by norm_num) ⟨2177, by rfl⟩ (by norm_num))
theorem R54749 : Reach 54749 := rs (se 3 (by rfl) ⟨10265, by rfl⟩) (B 20531 (by norm_num) ⟨10265, by rfl⟩ (by norm_num))
theorem R87533 : Reach 87533 := rs (se 3 (by rfl) ⟨16412, by rfl⟩) (B 32825 (by norm_num) ⟨16412, by rfl⟩ (by norm_num))
theorem R54773 : Reach 54773 := rs (se 5 (by rfl) ⟨2567, by rfl⟩) (B 5135 (by norm_num) ⟨2567, by rfl⟩ (by norm_num))
theorem R54797 : Reach 54797 := rs (se 3 (by rfl) ⟨10274, by rfl⟩) (B 20549 (by norm_num) ⟨10274, by rfl⟩ (by norm_num))
theorem R54821 : Reach 54821 := rs (se 4 (by rfl) ⟨5139, by rfl⟩) (B 10279 (by norm_num) ⟨5139, by rfl⟩ (by norm_num))
theorem R87605 : Reach 87605 := rs (se 5 (by rfl) ⟨4106, by rfl⟩) (B 8213 (by norm_num) ⟨4106, by rfl⟩ (by norm_num))
theorem R54845 : Reach 54845 := rs (se 3 (by rfl) ⟨10283, by rfl⟩) (B 20567 (by norm_num) ⟨10283, by rfl⟩ (by norm_num))
theorem R54869 : Reach 54869 := rs (se 8 (by rfl) ⟨321, by rfl⟩) (B 643 (by norm_num) ⟨321, by rfl⟩ (by norm_num))
theorem R54893 : Reach 54893 := rs (se 3 (by rfl) ⟨10292, by rfl⟩) (B 20585 (by norm_num) ⟨10292, by rfl⟩ (by norm_num))
theorem R87677 : Reach 87677 := rs (se 3 (by rfl) ⟨16439, by rfl⟩) (B 32879 (by norm_num) ⟨16439, by rfl⟩ (by norm_num))
theorem R54917 : Reach 54917 := rs (se 4 (by rfl) ⟨5148, by rfl⟩) (B 10297 (by norm_num) ⟨5148, by rfl⟩ (by norm_num))
theorem R284309 : Reach 284309 := rs (se 6 (by rfl) ⟨6663, by rfl⟩) (B 13327 (by norm_num) ⟨6663, by rfl⟩ (by norm_num))
theorem R54941 : Reach 54941 := rs (se 3 (by rfl) ⟨10301, by rfl⟩) (B 20603 (by norm_num) ⟨10301, by rfl⟩ (by norm_num))
theorem R54965 : Reach 54965 := rs (se 5 (by rfl) ⟨2576, by rfl⟩) (B 5153 (by norm_num) ⟨2576, by rfl⟩ (by norm_num))
theorem R87749 : Reach 87749 := rs (se 4 (by rfl) ⟨8226, by rfl⟩) (B 16453 (by norm_num) ⟨8226, by rfl⟩ (by norm_num))
theorem R54989 : Reach 54989 := rs (se 3 (by rfl) ⟨10310, by rfl⟩) (B 20621 (by norm_num) ⟨10310, by rfl⟩ (by norm_num))
theorem R55013 : Reach 55013 := rs (se 4 (by rfl) ⟨5157, by rfl⟩) (B 10315 (by norm_num) ⟨5157, by rfl⟩ (by norm_num))
theorem R87805 : Reach 87805 := rs (se 3 (by rfl) ⟨16463, by rfl⟩) (B 32927 (by norm_num) ⟨16463, by rfl⟩ (by norm_num))
theorem R55037 : Reach 55037 := rs (se 3 (by rfl) ⟨10319, by rfl⟩) (B 20639 (by norm_num) ⟨10319, by rfl⟩ (by norm_num))
theorem R120581 : Reach 120581 := rs (se 4 (by rfl) ⟨11304, by rfl⟩) (B 22609 (by norm_num) ⟨11304, by rfl⟩ (by norm_num))
theorem R87821 : Reach 87821 := rs (se 3 (by rfl) ⟨16466, by rfl⟩) (B 32933 (by norm_num) ⟨16466, by rfl⟩ (by norm_num))
theorem R55061 : Reach 55061 := rs (se 6 (by rfl) ⟨1290, by rfl⟩) (B 2581 (by norm_num) ⟨1290, by rfl⟩ (by norm_num))
theorem R55085 : Reach 55085 := rs (se 3 (by rfl) ⟨10328, by rfl⟩) (B 20657 (by norm_num) ⟨10328, by rfl⟩ (by norm_num))
theorem R55109 : Reach 55109 := rs (se 4 (by rfl) ⟨5166, by rfl⟩) (B 10333 (by norm_num) ⟨5166, by rfl⟩ (by norm_num))
theorem R87893 : Reach 87893 := rs (se 9 (by rfl) ⟨257, by rfl⟩) (B 515 (by norm_num) ⟨257, by rfl⟩ (by norm_num))
theorem R55133 : Reach 55133 := rs (se 3 (by rfl) ⟨10337, by rfl⟩) (B 20675 (by norm_num) ⟨10337, by rfl⟩ (by norm_num))
theorem R55157 : Reach 55157 := rs (se 5 (by rfl) ⟨2585, by rfl⟩) (B 5171 (by norm_num) ⟨2585, by rfl⟩ (by norm_num))
theorem R55181 : Reach 55181 := rs (se 3 (by rfl) ⟨10346, by rfl⟩) (B 20693 (by norm_num) ⟨10346, by rfl⟩ (by norm_num))
theorem R87965 : Reach 87965 := rs (se 3 (by rfl) ⟨16493, by rfl⟩) (B 32987 (by norm_num) ⟨16493, by rfl⟩ (by norm_num))
theorem R55205 : Reach 55205 := rs (se 4 (by rfl) ⟨5175, by rfl⟩) (B 10351 (by norm_num) ⟨5175, by rfl⟩ (by norm_num))
theorem R55229 : Reach 55229 := rs (se 3 (by rfl) ⟨10355, by rfl⟩) (B 20711 (by norm_num) ⟨10355, by rfl⟩ (by norm_num))
theorem R55253 : Reach 55253 := rs (se 7 (by rfl) ⟨647, by rfl⟩) (B 1295 (by norm_num) ⟨647, by rfl⟩ (by norm_num))
theorem R88037 : Reach 88037 := rs (se 4 (by rfl) ⟨8253, by rfl⟩) (B 16507 (by norm_num) ⟨8253, by rfl⟩ (by norm_num))
theorem R55277 : Reach 55277 := rs (se 3 (by rfl) ⟨10364, by rfl⟩) (B 20729 (by norm_num) ⟨10364, by rfl⟩ (by norm_num))
theorem R55301 : Reach 55301 := rs (se 4 (by rfl) ⟨5184, by rfl⟩) (B 10369 (by norm_num) ⟨5184, by rfl⟩ (by norm_num))
theorem R55325 : Reach 55325 := rs (se 3 (by rfl) ⟨10373, by rfl⟩) (B 20747 (by norm_num) ⟨10373, by rfl⟩ (by norm_num))
theorem R55349 : Reach 55349 := rs (se 5 (by rfl) ⟨2594, by rfl⟩) (B 5189 (by norm_num) ⟨2594, by rfl⟩ (by norm_num))
theorem R55373 : Reach 55373 := rs (se 3 (by rfl) ⟨10382, by rfl⟩) (B 20765 (by norm_num) ⟨10382, by rfl⟩ (by norm_num))
theorem R55397 : Reach 55397 := rs (se 4 (by rfl) ⟨5193, by rfl⟩) (B 10387 (by norm_num) ⟨5193, by rfl⟩ (by norm_num))
theorem R55421 : Reach 55421 := rs (se 3 (by rfl) ⟨10391, by rfl⟩) (B 20783 (by norm_num) ⟨10391, by rfl⟩ (by norm_num))
theorem R55445 : Reach 55445 := rs (se 6 (by rfl) ⟨1299, by rfl⟩) (B 2599 (by norm_num) ⟨1299, by rfl⟩ (by norm_num))
theorem R88229 : Reach 88229 := rs (se 4 (by rfl) ⟨8271, by rfl⟩) (B 16543 (by norm_num) ⟨8271, by rfl⟩ (by norm_num))
theorem R55469 : Reach 55469 := rs (se 3 (by rfl) ⟨10400, by rfl⟩) (B 20801 (by norm_num) ⟨10400, by rfl⟩ (by norm_num))
theorem R121013 : Reach 121013 := rs (se 5 (by rfl) ⟨5672, by rfl⟩) (B 11345 (by norm_num) ⟨5672, by rfl⟩ (by norm_num))
theorem R55493 : Reach 55493 := rs (se 4 (by rfl) ⟨5202, by rfl⟩) (B 10405 (by norm_num) ⟨5202, by rfl⟩ (by norm_num))
theorem R55517 : Reach 55517 := rs (se 3 (by rfl) ⟨10409, by rfl⟩) (B 20819 (by norm_num) ⟨10409, by rfl⟩ (by norm_num))
theorem R55541 : Reach 55541 := rs (se 5 (by rfl) ⟨2603, by rfl⟩) (B 5207 (by norm_num) ⟨2603, by rfl⟩ (by norm_num))
theorem R55565 : Reach 55565 := rs (se 3 (by rfl) ⟨10418, by rfl⟩) (B 20837 (by norm_num) ⟨10418, by rfl⟩ (by norm_num))
theorem R55589 : Reach 55589 := rs (se 4 (by rfl) ⟨5211, by rfl⟩) (B 10423 (by norm_num) ⟨5211, by rfl⟩ (by norm_num))
theorem R55613 : Reach 55613 := rs (se 3 (by rfl) ⟨10427, by rfl⟩) (B 20855 (by norm_num) ⟨10427, by rfl⟩ (by norm_num))
theorem R55637 : Reach 55637 := rs (se 10 (by rfl) ⟨81, by rfl⟩) (B 163 (by norm_num) ⟨81, by rfl⟩ (by norm_num))
theorem R55661 : Reach 55661 := rs (se 3 (by rfl) ⟨10436, by rfl⟩) (B 20873 (by norm_num) ⟨10436, by rfl⟩ (by norm_num))
theorem R55685 : Reach 55685 := rs (se 4 (by rfl) ⟨5220, by rfl⟩) (B 10441 (by norm_num) ⟨5220, by rfl⟩ (by norm_num))
theorem R55709 : Reach 55709 := rs (se 3 (by rfl) ⟨10445, by rfl⟩) (B 20891 (by norm_num) ⟨10445, by rfl⟩ (by norm_num))
theorem R55733 : Reach 55733 := rs (se 5 (by rfl) ⟨2612, by rfl⟩) (B 5225 (by norm_num) ⟨2612, by rfl⟩ (by norm_num))
theorem R55757 : Reach 55757 := rs (se 3 (by rfl) ⟨10454, by rfl⟩) (B 20909 (by norm_num) ⟨10454, by rfl⟩ (by norm_num))
theorem R55781 : Reach 55781 := rs (se 4 (by rfl) ⟨5229, by rfl⟩) (B 10459 (by norm_num) ⟨5229, by rfl⟩ (by norm_num))
theorem R55805 : Reach 55805 := rs (se 3 (by rfl) ⟨10463, by rfl⟩) (B 20927 (by norm_num) ⟨10463, by rfl⟩ (by norm_num))
theorem R55829 : Reach 55829 := rs (se 6 (by rfl) ⟨1308, by rfl⟩) (B 2617 (by norm_num) ⟨1308, by rfl⟩ (by norm_num))
theorem R55853 : Reach 55853 := rs (se 3 (by rfl) ⟨10472, by rfl⟩) (B 20945 (by norm_num) ⟨10472, by rfl⟩ (by norm_num))
theorem R318005 : Reach 318005 := rs (se 5 (by rfl) ⟨14906, by rfl⟩) (B 29813 (by norm_num) ⟨14906, by rfl⟩ (by norm_num))
theorem R55877 : Reach 55877 := rs (se 4 (by rfl) ⟨5238, by rfl⟩) (B 10477 (by norm_num) ⟨5238, by rfl⟩ (by norm_num))
theorem R55901 : Reach 55901 := rs (se 3 (by rfl) ⟨10481, by rfl⟩) (B 20963 (by norm_num) ⟨10481, by rfl⟩ (by norm_num))
theorem R121445 : Reach 121445 := rs (se 4 (by rfl) ⟨11385, by rfl⟩) (B 22771 (by norm_num) ⟨11385, by rfl⟩ (by norm_num))
theorem R55925 : Reach 55925 := rs (se 5 (by rfl) ⟨2621, by rfl⟩) (B 5243 (by norm_num) ⟨2621, by rfl⟩ (by norm_num))
theorem R55949 : Reach 55949 := rs (se 3 (by rfl) ⟨10490, by rfl⟩) (B 20981 (by norm_num) ⟨10490, by rfl⟩ (by norm_num))
theorem R55973 : Reach 55973 := rs (se 4 (by rfl) ⟨5247, by rfl⟩) (B 10495 (by norm_num) ⟨5247, by rfl⟩ (by norm_num))
theorem R55997 : Reach 55997 := rs (se 3 (by rfl) ⟨10499, by rfl⟩) (B 20999 (by norm_num) ⟨10499, by rfl⟩ (by norm_num))
theorem R56021 : Reach 56021 := rs (se 7 (by rfl) ⟨656, by rfl⟩) (B 1313 (by norm_num) ⟨656, by rfl⟩ (by norm_num))
theorem R187109 : Reach 187109 := rs (se 4 (by rfl) ⟨17541, by rfl⟩) (B 35083 (by norm_num) ⟨17541, by rfl⟩ (by norm_num))
theorem R88813 : Reach 88813 := rs (se 3 (by rfl) ⟨16652, by rfl⟩) (B 33305 (by norm_num) ⟨16652, by rfl⟩ (by norm_num))
theorem R56045 : Reach 56045 := rs (se 3 (by rfl) ⟨10508, by rfl⟩) (B 21017 (by norm_num) ⟨10508, by rfl⟩ (by norm_num))
theorem R56069 : Reach 56069 := rs (se 4 (by rfl) ⟨5256, by rfl⟩) (B 10513 (by norm_num) ⟨5256, by rfl⟩ (by norm_num))
theorem R56093 : Reach 56093 := rs (se 3 (by rfl) ⟨10517, by rfl⟩) (B 21035 (by norm_num) ⟨10517, by rfl⟩ (by norm_num))
theorem R56117 : Reach 56117 := rs (se 5 (by rfl) ⟨2630, by rfl⟩) (B 5261 (by norm_num) ⟨2630, by rfl⟩ (by norm_num))
theorem R56141 : Reach 56141 := rs (se 3 (by rfl) ⟨10526, by rfl⟩) (B 21053 (by norm_num) ⟨10526, by rfl⟩ (by norm_num))
theorem R56165 : Reach 56165 := rs (se 4 (by rfl) ⟨5265, by rfl⟩) (B 10531 (by norm_num) ⟨5265, by rfl⟩ (by norm_num))
theorem R56189 : Reach 56189 := rs (se 3 (by rfl) ⟨10535, by rfl⟩) (B 21071 (by norm_num) ⟨10535, by rfl⟩ (by norm_num))
theorem R56213 : Reach 56213 := rs (se 6 (by rfl) ⟨1317, by rfl⟩) (B 2635 (by norm_num) ⟨1317, by rfl⟩ (by norm_num))
theorem R56237 : Reach 56237 := rs (se 3 (by rfl) ⟨10544, by rfl⟩) (B 21089 (by norm_num) ⟨10544, by rfl⟩ (by norm_num))
theorem R56261 : Reach 56261 := rs (se 4 (by rfl) ⟨5274, by rfl⟩) (B 10549 (by norm_num) ⟨5274, by rfl⟩ (by norm_num))
theorem R220117 : Reach 220117 := rs (se 7 (by rfl) ⟨2579, by rfl⟩) (B 5159 (by norm_num) ⟨2579, by rfl⟩ (by norm_num))
theorem R56285 : Reach 56285 := rs (se 3 (by rfl) ⟨10553, by rfl⟩) (B 21107 (by norm_num) ⟨10553, by rfl⟩ (by norm_num))
theorem R56309 : Reach 56309 := rs (se 5 (by rfl) ⟨2639, by rfl⟩) (B 5279 (by norm_num) ⟨2639, by rfl⟩ (by norm_num))
theorem R56333 : Reach 56333 := rs (se 3 (by rfl) ⟨10562, by rfl⟩) (B 21125 (by norm_num) ⟨10562, by rfl⟩ (by norm_num))
theorem R121877 : Reach 121877 := rs (se 6 (by rfl) ⟨2856, by rfl⟩) (B 5713 (by norm_num) ⟨2856, by rfl⟩ (by norm_num))
theorem R56357 : Reach 56357 := rs (se 4 (by rfl) ⟨5283, by rfl⟩) (B 10567 (by norm_num) ⟨5283, by rfl⟩ (by norm_num))
theorem R56381 : Reach 56381 := rs (se 3 (by rfl) ⟨10571, by rfl⟩) (B 21143 (by norm_num) ⟨10571, by rfl⟩ (by norm_num))
theorem R121925 : Reach 121925 := rs (se 4 (by rfl) ⟨11430, by rfl⟩) (B 22861 (by norm_num) ⟨11430, by rfl⟩ (by norm_num))
theorem R56405 : Reach 56405 := rs (se 8 (by rfl) ⟨330, by rfl⟩) (B 661 (by norm_num) ⟨330, by rfl⟩ (by norm_num))
theorem R89189 : Reach 89189 := rs (se 4 (by rfl) ⟨8361, by rfl⟩) (B 16723 (by norm_num) ⟨8361, by rfl⟩ (by norm_num))
theorem R56429 : Reach 56429 := rs (se 3 (by rfl) ⟨10580, by rfl⟩) (B 21161 (by norm_num) ⟨10580, by rfl⟩ (by norm_num))
theorem R89221 : Reach 89221 := rs (se 4 (by rfl) ⟨8364, by rfl⟩) (B 16729 (by norm_num) ⟨8364, by rfl⟩ (by norm_num))
theorem R56453 : Reach 56453 := rs (se 4 (by rfl) ⟨5292, by rfl⟩) (B 10585 (by norm_num) ⟨5292, by rfl⟩ (by norm_num))
theorem R56477 : Reach 56477 := rs (se 3 (by rfl) ⟨10589, by rfl⟩) (B 21179 (by norm_num) ⟨10589, by rfl⟩ (by norm_num))
theorem R56501 : Reach 56501 := rs (se 5 (by rfl) ⟨2648, by rfl⟩) (B 5297 (by norm_num) ⟨2648, by rfl⟩ (by norm_num))
theorem R56525 : Reach 56525 := rs (se 3 (by rfl) ⟨10598, by rfl⟩) (B 21197 (by norm_num) ⟨10598, by rfl⟩ (by norm_num))
theorem R56549 : Reach 56549 := rs (se 4 (by rfl) ⟨5301, by rfl⟩) (B 10603 (by norm_num) ⟨5301, by rfl⟩ (by norm_num))
theorem R89333 : Reach 89333 := rs (se 5 (by rfl) ⟨4187, by rfl⟩) (B 8375 (by norm_num) ⟨4187, by rfl⟩ (by norm_num))
theorem R56573 : Reach 56573 := rs (se 3 (by rfl) ⟨10607, by rfl⟩) (B 21215 (by norm_num) ⟨10607, by rfl⟩ (by norm_num))
theorem R56597 : Reach 56597 := rs (se 6 (by rfl) ⟨1326, by rfl⟩) (B 2653 (by norm_num) ⟨1326, by rfl⟩ (by norm_num))
theorem R56621 : Reach 56621 := rs (se 3 (by rfl) ⟨10616, by rfl⟩) (B 21233 (by norm_num) ⟨10616, by rfl⟩ (by norm_num))
theorem R89413 : Reach 89413 := rs (se 4 (by rfl) ⟨8382, by rfl⟩) (B 16765 (by norm_num) ⟨8382, by rfl⟩ (by norm_num))
theorem R56645 : Reach 56645 := rs (se 4 (by rfl) ⟨5310, by rfl⟩) (B 10621 (by norm_num) ⟨5310, by rfl⟩ (by norm_num))
theorem R56669 : Reach 56669 := rs (se 3 (by rfl) ⟨10625, by rfl⟩) (B 21251 (by norm_num) ⟨10625, by rfl⟩ (by norm_num))
theorem R56693 : Reach 56693 := rs (se 5 (by rfl) ⟨2657, by rfl⟩) (B 5315 (by norm_num) ⟨2657, by rfl⟩ (by norm_num))
theorem R56717 : Reach 56717 := rs (se 3 (by rfl) ⟨10634, by rfl⟩) (B 21269 (by norm_num) ⟨10634, by rfl⟩ (by norm_num))
theorem R56741 : Reach 56741 := rs (se 4 (by rfl) ⟨5319, by rfl⟩) (B 10639 (by norm_num) ⟨5319, by rfl⟩ (by norm_num))
theorem R89525 : Reach 89525 := rs (se 5 (by rfl) ⟨4196, by rfl⟩) (B 8393 (by norm_num) ⟨4196, by rfl⟩ (by norm_num))
theorem R56765 : Reach 56765 := rs (se 3 (by rfl) ⟨10643, by rfl⟩) (B 21287 (by norm_num) ⟨10643, by rfl⟩ (by norm_num))
theorem R122309 : Reach 122309 := rs (se 4 (by rfl) ⟨11466, by rfl⟩) (B 22933 (by norm_num) ⟨11466, by rfl⟩ (by norm_num))
theorem R56789 : Reach 56789 := rs (se 7 (by rfl) ⟨665, by rfl⟩) (B 1331 (by norm_num) ⟨665, by rfl⟩ (by norm_num))
theorem R56813 : Reach 56813 := rs (se 3 (by rfl) ⟨10652, by rfl⟩) (B 21305 (by norm_num) ⟨10652, by rfl⟩ (by norm_num))
theorem R155141 : Reach 155141 := rs (se 4 (by rfl) ⟨14544, by rfl⟩) (B 29089 (by norm_num) ⟨14544, by rfl⟩ (by norm_num))
theorem R56837 : Reach 56837 := rs (se 4 (by rfl) ⟨5328, by rfl⟩) (B 10657 (by norm_num) ⟨5328, by rfl⟩ (by norm_num))
theorem R56845 : Reach 56845 := rs (se 3 (by rfl) ⟨10658, by rfl⟩) (B 21317 (by norm_num) ⟨10658, by rfl⟩ (by norm_num))
theorem R56861 : Reach 56861 := rs (se 3 (by rfl) ⟨10661, by rfl⟩) (B 21323 (by norm_num) ⟨10661, by rfl⟩ (by norm_num))
theorem R56885 : Reach 56885 := rs (se 5 (by rfl) ⟨2666, by rfl⟩) (B 5333 (by norm_num) ⟨2666, by rfl⟩ (by norm_num))
theorem R56909 : Reach 56909 := rs (se 3 (by rfl) ⟨10670, by rfl⟩) (B 21341 (by norm_num) ⟨10670, by rfl⟩ (by norm_num))
theorem R56933 : Reach 56933 := rs (se 4 (by rfl) ⟨5337, by rfl⟩) (B 10675 (by norm_num) ⟨5337, by rfl⟩ (by norm_num))
theorem R56957 : Reach 56957 := rs (se 3 (by rfl) ⟨10679, by rfl⟩) (B 21359 (by norm_num) ⟨10679, by rfl⟩ (by norm_num))
theorem R56981 : Reach 56981 := rs (se 6 (by rfl) ⟨1335, by rfl⟩) (B 2671 (by norm_num) ⟨1335, by rfl⟩ (by norm_num))
theorem R57005 : Reach 57005 := rs (se 3 (by rfl) ⟨10688, by rfl⟩) (B 21377 (by norm_num) ⟨10688, by rfl⟩ (by norm_num))
theorem R57029 : Reach 57029 := rs (se 4 (by rfl) ⟨5346, by rfl⟩) (B 10693 (by norm_num) ⟨5346, by rfl⟩ (by norm_num))
theorem R57053 : Reach 57053 := rs (se 3 (by rfl) ⟨10697, by rfl⟩) (B 21395 (by norm_num) ⟨10697, by rfl⟩ (by norm_num))
theorem R57077 : Reach 57077 := rs (se 5 (by rfl) ⟨2675, by rfl⟩) (B 5351 (by norm_num) ⟨2675, by rfl⟩ (by norm_num))
theorem R89869 : Reach 89869 := rs (se 3 (by rfl) ⟨16850, by rfl⟩) (B 33701 (by norm_num) ⟨16850, by rfl⟩ (by norm_num))
theorem R57101 : Reach 57101 := rs (se 3 (by rfl) ⟨10706, by rfl⟩) (B 21413 (by norm_num) ⟨10706, by rfl⟩ (by norm_num))
theorem R57125 : Reach 57125 := rs (se 4 (by rfl) ⟨5355, by rfl⟩) (B 10711 (by norm_num) ⟨5355, by rfl⟩ (by norm_num))
theorem R57149 : Reach 57149 := rs (se 3 (by rfl) ⟨10715, by rfl⟩) (B 21431 (by norm_num) ⟨10715, by rfl⟩ (by norm_num))
theorem R57173 : Reach 57173 := rs (se 9 (by rfl) ⟨167, by rfl⟩) (B 335 (by norm_num) ⟨167, by rfl⟩ (by norm_num))
theorem R57197 : Reach 57197 := rs (se 3 (by rfl) ⟨10724, by rfl⟩) (B 21449 (by norm_num) ⟨10724, by rfl⟩ (by norm_num))
theorem R122741 : Reach 122741 := rs (se 5 (by rfl) ⟨5753, by rfl⟩) (B 11507 (by norm_num) ⟨5753, by rfl⟩ (by norm_num))
theorem R89981 : Reach 89981 := rs (se 3 (by rfl) ⟨16871, by rfl⟩) (B 33743 (by norm_num) ⟨16871, by rfl⟩ (by norm_num))
theorem R57221 : Reach 57221 := rs (se 4 (by rfl) ⟨5364, by rfl⟩) (B 10729 (by norm_num) ⟨5364, by rfl⟩ (by norm_num))
theorem R57245 : Reach 57245 := rs (se 3 (by rfl) ⟨10733, by rfl⟩) (B 21467 (by norm_num) ⟨10733, by rfl⟩ (by norm_num))
theorem R57269 : Reach 57269 := rs (se 5 (by rfl) ⟨2684, by rfl⟩) (B 5369 (by norm_num) ⟨2684, by rfl⟩ (by norm_num))
theorem R57293 : Reach 57293 := rs (se 3 (by rfl) ⟨10742, by rfl⟩) (B 21485 (by norm_num) ⟨10742, by rfl⟩ (by norm_num))
theorem R57317 : Reach 57317 := rs (se 4 (by rfl) ⟨5373, by rfl⟩) (B 10747 (by norm_num) ⟨5373, by rfl⟩ (by norm_num))
theorem R188405 : Reach 188405 := rs (se 5 (by rfl) ⟨8831, by rfl⟩) (B 17663 (by norm_num) ⟨8831, by rfl⟩ (by norm_num))
theorem R57341 : Reach 57341 := rs (se 3 (by rfl) ⟨10751, by rfl⟩) (B 21503 (by norm_num) ⟨10751, by rfl⟩ (by norm_num))
theorem R57365 : Reach 57365 := rs (se 6 (by rfl) ⟨1344, by rfl⟩) (B 2689 (by norm_num) ⟨1344, by rfl⟩ (by norm_num))
theorem R122917 : Reach 122917 := rs (se 4 (by rfl) ⟨11523, by rfl⟩) (B 23047 (by norm_num) ⟨11523, by rfl⟩ (by norm_num))
theorem R57389 : Reach 57389 := rs (se 3 (by rfl) ⟨10760, by rfl⟩) (B 21521 (by norm_num) ⟨10760, by rfl⟩ (by norm_num))
theorem R90173 : Reach 90173 := rs (se 3 (by rfl) ⟨16907, by rfl⟩) (B 33815 (by norm_num) ⟨16907, by rfl⟩ (by norm_num))
theorem R57413 : Reach 57413 := rs (se 4 (by rfl) ⟨5382, by rfl⟩) (B 10765 (by norm_num) ⟨5382, by rfl⟩ (by norm_num))
theorem R680021 : Reach 680021 := rs (se 8 (by rfl) ⟨3984, by rfl⟩) (B 7969 (by norm_num) ⟨3984, by rfl⟩ (by norm_num))
theorem R57437 : Reach 57437 := rs (se 3 (by rfl) ⟨10769, by rfl⟩) (B 21539 (by norm_num) ⟨10769, by rfl⟩ (by norm_num))
theorem R57461 : Reach 57461 := rs (se 5 (by rfl) ⟨2693, by rfl⟩) (B 5387 (by norm_num) ⟨2693, by rfl⟩ (by norm_num))
theorem R57485 : Reach 57485 := rs (se 3 (by rfl) ⟨10778, by rfl⟩) (B 21557 (by norm_num) ⟨10778, by rfl⟩ (by norm_num))
theorem R57509 : Reach 57509 := rs (se 4 (by rfl) ⟨5391, by rfl⟩) (B 10783 (by norm_num) ⟨5391, by rfl⟩ (by norm_num))
theorem R57533 : Reach 57533 := rs (se 3 (by rfl) ⟨10787, by rfl⟩) (B 21575 (by norm_num) ⟨10787, by rfl⟩ (by norm_num))
theorem R57557 : Reach 57557 := rs (se 7 (by rfl) ⟨674, by rfl⟩) (B 1349 (by norm_num) ⟨674, by rfl⟩ (by norm_num))
theorem R57581 : Reach 57581 := rs (se 3 (by rfl) ⟨10796, by rfl⟩) (B 21593 (by norm_num) ⟨10796, by rfl⟩ (by norm_num))
theorem R57605 : Reach 57605 := rs (se 4 (by rfl) ⟨5400, by rfl⟩) (B 10801 (by norm_num) ⟨5400, by rfl⟩ (by norm_num))
theorem R57629 : Reach 57629 := rs (se 3 (by rfl) ⟨10805, by rfl⟩) (B 21611 (by norm_num) ⟨10805, by rfl⟩ (by norm_num))
theorem R123173 : Reach 123173 := rs (se 4 (by rfl) ⟨11547, by rfl⟩) (B 23095 (by norm_num) ⟨11547, by rfl⟩ (by norm_num))
theorem R57653 : Reach 57653 := rs (se 5 (by rfl) ⟨2702, by rfl⟩) (B 5405 (by norm_num) ⟨2702, by rfl⟩ (by norm_num))
theorem R57677 : Reach 57677 := rs (se 3 (by rfl) ⟨10814, by rfl⟩) (B 21629 (by norm_num) ⟨10814, by rfl⟩ (by norm_num))
theorem R221525 : Reach 221525 := rs (se 10 (by rfl) ⟨324, by rfl⟩) (B 649 (by norm_num) ⟨324, by rfl⟩ (by norm_num))
theorem R57701 : Reach 57701 := rs (se 4 (by rfl) ⟨5409, by rfl⟩) (B 10819 (by norm_num) ⟨5409, by rfl⟩ (by norm_num))
theorem R57725 : Reach 57725 := rs (se 3 (by rfl) ⟨10823, by rfl⟩) (B 21647 (by norm_num) ⟨10823, by rfl⟩ (by norm_num))
theorem R90517 : Reach 90517 := rs (se 6 (by rfl) ⟨2121, by rfl⟩) (B 4243 (by norm_num) ⟨2121, by rfl⟩ (by norm_num))
theorem R57749 : Reach 57749 := rs (se 6 (by rfl) ⟨1353, by rfl⟩) (B 2707 (by norm_num) ⟨1353, by rfl⟩ (by norm_num))
theorem R57773 : Reach 57773 := rs (se 3 (by rfl) ⟨10832, by rfl⟩) (B 21665 (by norm_num) ⟨10832, by rfl⟩ (by norm_num))
theorem R57781 : Reach 57781 := rs (se 5 (by rfl) ⟨2708, by rfl⟩) (B 5417 (by norm_num) ⟨2708, by rfl⟩ (by norm_num))
theorem R57797 : Reach 57797 := rs (se 4 (by rfl) ⟨5418, by rfl⟩) (B 10837 (by norm_num) ⟨5418, by rfl⟩ (by norm_num))
theorem R57821 : Reach 57821 := rs (se 3 (by rfl) ⟨10841, by rfl⟩) (B 21683 (by norm_num) ⟨10841, by rfl⟩ (by norm_num))
theorem R57845 : Reach 57845 := rs (se 5 (by rfl) ⟨2711, by rfl⟩) (B 5423 (by norm_num) ⟨2711, by rfl⟩ (by norm_num))
theorem R90629 : Reach 90629 := rs (se 4 (by rfl) ⟨8496, by rfl⟩) (B 16993 (by norm_num) ⟨8496, by rfl⟩ (by norm_num))
theorem R57869 : Reach 57869 := rs (se 3 (by rfl) ⟨10850, by rfl⟩) (B 21701 (by norm_num) ⟨10850, by rfl⟩ (by norm_num))
theorem R221717 : Reach 221717 := rs (se 6 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R57893 : Reach 57893 := rs (se 4 (by rfl) ⟨5427, by rfl⟩) (B 10855 (by norm_num) ⟨5427, by rfl⟩ (by norm_num))
theorem R57917 : Reach 57917 := rs (se 3 (by rfl) ⟨10859, by rfl⟩) (B 21719 (by norm_num) ⟨10859, by rfl⟩ (by norm_num))
theorem R57925 : Reach 57925 := rs (se 4 (by rfl) ⟨5430, by rfl⟩) (B 10861 (by norm_num) ⟨5430, by rfl⟩ (by norm_num))
theorem R57941 : Reach 57941 := rs (se 8 (by rfl) ⟨339, by rfl⟩) (B 679 (by norm_num) ⟨339, by rfl⟩ (by norm_num))
theorem R57965 : Reach 57965 := rs (se 3 (by rfl) ⟨10868, by rfl⟩) (B 21737 (by norm_num) ⟨10868, by rfl⟩ (by norm_num))
theorem R57989 : Reach 57989 := rs (se 4 (by rfl) ⟨5436, by rfl⟩) (B 10873 (by norm_num) ⟨5436, by rfl⟩ (by norm_num))
theorem R58013 : Reach 58013 := rs (se 3 (by rfl) ⟨10877, by rfl⟩) (B 21755 (by norm_num) ⟨10877, by rfl⟩ (by norm_num))
theorem R58037 : Reach 58037 := rs (se 5 (by rfl) ⟨2720, by rfl⟩) (B 5441 (by norm_num) ⟨2720, by rfl⟩ (by norm_num))
theorem R90821 : Reach 90821 := rs (se 4 (by rfl) ⟨8514, by rfl⟩) (B 17029 (by norm_num) ⟨8514, by rfl⟩ (by norm_num))
theorem R58061 : Reach 58061 := rs (se 3 (by rfl) ⟨10886, by rfl⟩) (B 21773 (by norm_num) ⟨10886, by rfl⟩ (by norm_num))
theorem R123605 : Reach 123605 := rs (se 7 (by rfl) ⟨1448, by rfl⟩) (B 2897 (by norm_num) ⟨1448, by rfl⟩ (by norm_num))
theorem R58085 : Reach 58085 := rs (se 4 (by rfl) ⟨5445, by rfl⟩) (B 10891 (by norm_num) ⟨5445, by rfl⟩ (by norm_num))
theorem R58109 : Reach 58109 := rs (se 3 (by rfl) ⟨10895, by rfl⟩) (B 21791 (by norm_num) ⟨10895, by rfl⟩ (by norm_num))
theorem R58133 : Reach 58133 := rs (se 6 (by rfl) ⟨1362, by rfl⟩) (B 2725 (by norm_num) ⟨1362, by rfl⟩ (by norm_num))
theorem R58157 : Reach 58157 := rs (se 3 (by rfl) ⟨10904, by rfl⟩) (B 21809 (by norm_num) ⟨10904, by rfl⟩ (by norm_num))
theorem R58181 : Reach 58181 := rs (se 4 (by rfl) ⟨5454, by rfl⟩) (B 10909 (by norm_num) ⟨5454, by rfl⟩ (by norm_num))
theorem R58205 : Reach 58205 := rs (se 3 (by rfl) ⟨10913, by rfl⟩) (B 21827 (by norm_num) ⟨10913, by rfl⟩ (by norm_num))
theorem R58229 : Reach 58229 := rs (se 5 (by rfl) ⟨2729, by rfl⟩) (B 5459 (by norm_num) ⟨2729, by rfl⟩ (by norm_num))
theorem R58253 : Reach 58253 := rs (se 3 (by rfl) ⟨10922, by rfl⟩) (B 21845 (by norm_num) ⟨10922, by rfl⟩ (by norm_num))
theorem R58277 : Reach 58277 := rs (se 4 (by rfl) ⟨5463, by rfl⟩) (B 10927 (by norm_num) ⟨5463, by rfl⟩ (by norm_num))
theorem R58301 : Reach 58301 := rs (se 3 (by rfl) ⟨10931, by rfl⟩) (B 21863 (by norm_num) ⟨10931, by rfl⟩ (by norm_num))
theorem R58325 : Reach 58325 := rs (se 7 (by rfl) ⟨683, by rfl⟩) (B 1367 (by norm_num) ⟨683, by rfl⟩ (by norm_num))
theorem R58349 : Reach 58349 := rs (se 3 (by rfl) ⟨10940, by rfl⟩) (B 21881 (by norm_num) ⟨10940, by rfl⟩ (by norm_num))
theorem R58373 : Reach 58373 := rs (se 4 (by rfl) ⟨5472, by rfl⟩) (B 10945 (by norm_num) ⟨5472, by rfl⟩ (by norm_num))
theorem R91165 : Reach 91165 := rs (se 3 (by rfl) ⟨17093, by rfl⟩) (B 34187 (by norm_num) ⟨17093, by rfl⟩ (by norm_num))
theorem R58397 : Reach 58397 := rs (se 3 (by rfl) ⟨10949, by rfl⟩) (B 21899 (by norm_num) ⟨10949, by rfl⟩ (by norm_num))
theorem R58421 : Reach 58421 := rs (se 5 (by rfl) ⟨2738, by rfl⟩) (B 5477 (by norm_num) ⟨2738, by rfl⟩ (by norm_num))
theorem R58445 : Reach 58445 := rs (se 3 (by rfl) ⟨10958, by rfl⟩) (B 21917 (by norm_num) ⟨10958, by rfl⟩ (by norm_num))
theorem R58469 : Reach 58469 := rs (se 4 (by rfl) ⟨5481, by rfl⟩) (B 10963 (by norm_num) ⟨5481, by rfl⟩ (by norm_num))
theorem R58493 : Reach 58493 := rs (se 3 (by rfl) ⟨10967, by rfl⟩) (B 21935 (by norm_num) ⟨10967, by rfl⟩ (by norm_num))
theorem R124037 : Reach 124037 := rs (se 4 (by rfl) ⟨11628, by rfl⟩) (B 23257 (by norm_num) ⟨11628, by rfl⟩ (by norm_num))
theorem R91277 : Reach 91277 := rs (se 3 (by rfl) ⟨17114, by rfl⟩) (B 34229 (by norm_num) ⟨17114, by rfl⟩ (by norm_num))
theorem R58517 : Reach 58517 := rs (se 6 (by rfl) ⟨1371, by rfl⟩) (B 2743 (by norm_num) ⟨1371, by rfl⟩ (by norm_num))
theorem R58541 : Reach 58541 := rs (se 3 (by rfl) ⟨10976, by rfl⟩) (B 21953 (by norm_num) ⟨10976, by rfl⟩ (by norm_num))
theorem R58565 : Reach 58565 := rs (se 4 (by rfl) ⟨5490, by rfl⟩) (B 10981 (by norm_num) ⟨5490, by rfl⟩ (by norm_num))
theorem R58589 : Reach 58589 := rs (se 3 (by rfl) ⟨10985, by rfl⟩) (B 21971 (by norm_num) ⟨10985, by rfl⟩ (by norm_num))
theorem R156917 : Reach 156917 := rs (se 5 (by rfl) ⟨7355, by rfl⟩) (B 14711 (by norm_num) ⟨7355, by rfl⟩ (by norm_num))
theorem R58613 : Reach 58613 := rs (se 5 (by rfl) ⟨2747, by rfl⟩) (B 5495 (by norm_num) ⟨2747, by rfl⟩ (by norm_num))
theorem R58637 : Reach 58637 := rs (se 3 (by rfl) ⟨10994, by rfl⟩) (B 21989 (by norm_num) ⟨10994, by rfl⟩ (by norm_num))
theorem R58661 : Reach 58661 := rs (se 4 (by rfl) ⟨5499, by rfl⟩) (B 10999 (by norm_num) ⟨5499, by rfl⟩ (by norm_num))
theorem R91469 : Reach 91469 := rs (se 3 (by rfl) ⟨17150, by rfl⟩) (B 34301 (by norm_num) ⟨17150, by rfl⟩ (by norm_num))
theorem R157157 : Reach 157157 := rs (se 4 (by rfl) ⟨14733, by rfl⟩) (B 29467 (by norm_num) ⟨14733, by rfl⟩ (by norm_num))
theorem R222709 : Reach 222709 := rs (se 5 (by rfl) ⟨10439, by rfl⟩) (B 20879 (by norm_num) ⟨10439, by rfl⟩ (by norm_num))
theorem R58909 : Reach 58909 := rs (se 3 (by rfl) ⟨11045, by rfl⟩) (B 22091 (by norm_num) ⟨11045, by rfl⟩ (by norm_num))
theorem R124469 : Reach 124469 := rs (se 5 (by rfl) ⟨5834, by rfl⟩) (B 11669 (by norm_num) ⟨5834, by rfl⟩ (by norm_num))
theorem R91813 : Reach 91813 := rs (se 4 (by rfl) ⟨8607, by rfl⟩) (B 17215 (by norm_num) ⟨8607, by rfl⟩ (by norm_num))
theorem R517909 : Reach 517909 := rs (se 6 (by rfl) ⟨12138, by rfl⟩) (B 24277 (by norm_num) ⟨12138, by rfl⟩ (by norm_num))
theorem R91925 : Reach 91925 := rs (se 6 (by rfl) ⟨2154, by rfl⟩) (B 4309 (by norm_num) ⟨2154, by rfl⟩ (by norm_num))
theorem R59165 : Reach 59165 := rs (se 3 (by rfl) ⟨11093, by rfl⟩) (B 22187 (by norm_num) ⟨11093, by rfl⟩ (by norm_num))
theorem R91957 : Reach 91957 := rs (se 5 (by rfl) ⟨4310, by rfl⟩) (B 8621 (by norm_num) ⟨4310, by rfl⟩ (by norm_num))
theorem R59285 : Reach 59285 := rs (se 6 (by rfl) ⟨1389, by rfl⟩) (B 2779 (by norm_num) ⟨1389, by rfl⟩ (by norm_num))
theorem R92117 : Reach 92117 := rs (se 7 (by rfl) ⟨1079, by rfl⟩) (B 2159 (by norm_num) ⟨1079, by rfl⟩ (by norm_num))
theorem R59357 : Reach 59357 := rs (se 3 (by rfl) ⟨11129, by rfl⟩) (B 22259 (by norm_num) ⟨11129, by rfl⟩ (by norm_num))
theorem R124901 : Reach 124901 := rs (se 4 (by rfl) ⟨11709, by rfl⟩) (B 23419 (by norm_num) ⟨11709, by rfl⟩ (by norm_num))
theorem R59413 : Reach 59413 := rs (se 6 (by rfl) ⟨1392, by rfl⟩) (B 2785 (by norm_num) ⟨1392, by rfl⟩ (by norm_num))
theorem R59501 : Reach 59501 := rs (se 3 (by rfl) ⟨11156, by rfl⟩) (B 22313 (by norm_num) ⟨11156, by rfl⟩ (by norm_num))
theorem R125077 : Reach 125077 := rs (se 6 (by rfl) ⟨2931, by rfl⟩) (B 5863 (by norm_num) ⟨2931, by rfl⟩ (by norm_num))
theorem R92333 : Reach 92333 := rs (se 3 (by rfl) ⟨17312, by rfl⟩) (B 34625 (by norm_num) ⟨17312, by rfl⟩ (by norm_num))
theorem R157909 : Reach 157909 := rs (se 7 (by rfl) ⟨1850, by rfl⟩) (B 3701 (by norm_num) ⟨1850, by rfl⟩ (by norm_num))
theorem R59629 : Reach 59629 := rs (se 3 (by rfl) ⟨11180, by rfl⟩) (B 22361 (by norm_num) ⟨11180, by rfl⟩ (by norm_num))
theorem R92461 : Reach 92461 := rs (se 3 (by rfl) ⟨17336, by rfl⟩) (B 34673 (by norm_num) ⟨17336, by rfl⟩ (by norm_num))
theorem R59717 : Reach 59717 := rs (se 4 (by rfl) ⟨5598, by rfl⟩) (B 11197 (by norm_num) ⟨5598, by rfl⟩ (by norm_num))
theorem R125333 : Reach 125333 := rs (se 6 (by rfl) ⟨2937, by rfl⟩) (B 5875 (by norm_num) ⟨2937, by rfl⟩ (by norm_num))
theorem R92573 : Reach 92573 := rs (se 3 (by rfl) ⟨17357, by rfl⟩) (B 34715 (by norm_num) ⟨17357, by rfl⟩ (by norm_num))
theorem R59845 : Reach 59845 := rs (se 4 (by rfl) ⟨5610, by rfl⟩) (B 11221 (by norm_num) ⟨5610, by rfl⟩ (by norm_num))
theorem R190997 : Reach 190997 := rs (se 6 (by rfl) ⟨4476, by rfl⟩) (B 8953 (by norm_num) ⟨4476, by rfl⟩ (by norm_num))
theorem R59933 : Reach 59933 := rs (se 3 (by rfl) ⟨11237, by rfl⟩) (B 22475 (by norm_num) ⟨11237, by rfl⟩ (by norm_num))
theorem R92765 : Reach 92765 := rs (se 3 (by rfl) ⟨17393, by rfl⟩) (B 34787 (by norm_num) ⟨17393, by rfl⟩ (by norm_num))
theorem R60061 : Reach 60061 := rs (se 3 (by rfl) ⟨11261, by rfl⟩) (B 22523 (by norm_num) ⟨11261, by rfl⟩ (by norm_num))
theorem R60149 : Reach 60149 := rs (se 5 (by rfl) ⟨2819, by rfl⟩) (B 5639 (by norm_num) ⟨2819, by rfl⟩ (by norm_num))
theorem R125765 : Reach 125765 := rs (se 4 (by rfl) ⟨11790, by rfl⟩) (B 23581 (by norm_num) ⟨11790, by rfl⟩ (by norm_num))
theorem R60277 : Reach 60277 := rs (se 5 (by rfl) ⟨2825, by rfl⟩) (B 5651 (by norm_num) ⟨2825, by rfl⟩ (by norm_num))
theorem R93053 : Reach 93053 := rs (se 3 (by rfl) ⟨17447, by rfl⟩) (B 34895 (by norm_num) ⟨17447, by rfl⟩ (by norm_num))
theorem R93109 : Reach 93109 := rs (se 5 (by rfl) ⟨4364, by rfl⟩) (B 8729 (by norm_num) ⟨4364, by rfl⟩ (by norm_num))
theorem R60365 : Reach 60365 := rs (se 3 (by rfl) ⟨11318, by rfl⟩) (B 22637 (by norm_num) ⟨11318, by rfl⟩ (by norm_num))
theorem R93221 : Reach 93221 := rs (se 4 (by rfl) ⟨8739, by rfl⟩) (B 17479 (by norm_num) ⟨8739, by rfl⟩ (by norm_num))
theorem R60493 : Reach 60493 := rs (se 3 (by rfl) ⟨11342, by rfl⟩) (B 22685 (by norm_num) ⟨11342, by rfl⟩ (by norm_num))
theorem R93341 : Reach 93341 := rs (se 3 (by rfl) ⟨17501, by rfl⟩) (B 35003 (by norm_num) ⟨17501, by rfl⟩ (by norm_num))
theorem R60581 : Reach 60581 := rs (se 4 (by rfl) ⟨5679, by rfl⟩) (B 11359 (by norm_num) ⟨5679, by rfl⟩ (by norm_num))
theorem R93413 : Reach 93413 := rs (se 4 (by rfl) ⟨8757, by rfl⟩) (B 17515 (by norm_num) ⟨8757, by rfl⟩ (by norm_num))
theorem R126197 : Reach 126197 := rs (se 5 (by rfl) ⟨5915, by rfl⟩) (B 11831 (by norm_num) ⟨5915, by rfl⟩ (by norm_num))
theorem R60709 : Reach 60709 := rs (se 4 (by rfl) ⟨5691, by rfl⟩) (B 11383 (by norm_num) ⟨5691, by rfl⟩ (by norm_num))
theorem R93485 : Reach 93485 := rs (se 3 (by rfl) ⟨17528, by rfl⟩) (B 35057 (by norm_num) ⟨17528, by rfl⟩ (by norm_num))
theorem R60797 : Reach 60797 := rs (se 3 (by rfl) ⟨11399, by rfl⟩) (B 22799 (by norm_num) ⟨11399, by rfl⟩ (by norm_num))
theorem R60869 : Reach 60869 := rs (se 4 (by rfl) ⟨5706, by rfl⟩) (B 11413 (by norm_num) ⟨5706, by rfl⟩ (by norm_num))
theorem R60925 : Reach 60925 := rs (se 3 (by rfl) ⟨11423, by rfl⟩) (B 22847 (by norm_num) ⟨11423, by rfl⟩ (by norm_num))
theorem R60997 : Reach 60997 := rs (se 4 (by rfl) ⟨5718, by rfl⟩) (B 11437 (by norm_num) ⟨5718, by rfl⟩ (by norm_num))
theorem R61013 : Reach 61013 := rs (se 8 (by rfl) ⟨357, by rfl⟩) (B 715 (by norm_num) ⟨357, by rfl⟩ (by norm_num))
theorem R126629 : Reach 126629 := rs (se 4 (by rfl) ⟨11871, by rfl⟩) (B 23743 (by norm_num) ⟨11871, by rfl⟩ (by norm_num))
theorem R61141 : Reach 61141 := rs (se 7 (by rfl) ⟨716, by rfl⟩) (B 1433 (by norm_num) ⟨716, by rfl⟩ (by norm_num))
theorem R61229 : Reach 61229 := rs (se 3 (by rfl) ⟨11480, by rfl⟩) (B 22961 (by norm_num) ⟨11480, by rfl⟩ (by norm_num))
theorem R61357 : Reach 61357 := rs (se 3 (by rfl) ⟨11504, by rfl⟩) (B 23009 (by norm_num) ⟨11504, by rfl⟩ (by norm_num))
theorem R61445 : Reach 61445 := rs (se 4 (by rfl) ⟨5760, by rfl⟩) (B 11521 (by norm_num) ⟨5760, by rfl⟩ (by norm_num))
theorem R127061 : Reach 127061 := rs (se 8 (by rfl) ⟨744, by rfl⟩) (B 1489 (by norm_num) ⟨744, by rfl⟩ (by norm_num))
theorem R61573 : Reach 61573 := rs (se 4 (by rfl) ⟨5772, by rfl⟩) (B 11545 (by norm_num) ⟨5772, by rfl⟩ (by norm_num))
theorem R94405 : Reach 94405 := rs (se 4 (by rfl) ⟨8850, by rfl⟩) (B 17701 (by norm_num) ⟨8850, by rfl⟩ (by norm_num))
theorem R61661 : Reach 61661 := rs (se 3 (by rfl) ⟨11561, by rfl⟩) (B 23123 (by norm_num) ⟨11561, by rfl⟩ (by norm_num))
theorem R61717 : Reach 61717 := rs (se 6 (by rfl) ⟨1446, by rfl⟩) (B 2893 (by norm_num) ⟨1446, by rfl⟩ (by norm_num))
theorem R94517 : Reach 94517 := rs (se 5 (by rfl) ⟨4430, by rfl⟩) (B 8861 (by norm_num) ⟨4430, by rfl⟩ (by norm_num))
theorem R61789 : Reach 61789 := rs (se 3 (by rfl) ⟨11585, by rfl⟩) (B 23171 (by norm_num) ⟨11585, by rfl⟩ (by norm_num))
theorem R61877 : Reach 61877 := rs (se 5 (by rfl) ⟨2900, by rfl⟩) (B 5801 (by norm_num) ⟨2900, by rfl⟩ (by norm_num))
theorem R94709 : Reach 94709 := rs (se 5 (by rfl) ⟨4439, by rfl⟩) (B 8879 (by norm_num) ⟨4439, by rfl⟩ (by norm_num))
theorem R127493 : Reach 127493 := rs (se 4 (by rfl) ⟨11952, by rfl⟩) (B 23905 (by norm_num) ⟨11952, by rfl⟩ (by norm_num))
theorem R160309 : Reach 160309 := rs (se 5 (by rfl) ⟨7514, by rfl⟩) (B 15029 (by norm_num) ⟨7514, by rfl⟩ (by norm_num))
theorem R62005 : Reach 62005 := rs (se 5 (by rfl) ⟨2906, by rfl⟩) (B 5813 (by norm_num) ⟨2906, by rfl⟩ (by norm_num))
theorem R62093 : Reach 62093 := rs (se 3 (by rfl) ⟨11642, by rfl⟩) (B 23285 (by norm_num) ⟨11642, by rfl⟩ (by norm_num))
theorem R62221 : Reach 62221 := rs (se 3 (by rfl) ⟨11666, by rfl⟩) (B 23333 (by norm_num) ⟨11666, by rfl⟩ (by norm_num))
theorem R62309 : Reach 62309 := rs (se 4 (by rfl) ⟨5841, by rfl⟩) (B 11683 (by norm_num) ⟨5841, by rfl⟩ (by norm_num))
theorem R62381 : Reach 62381 := rs (se 3 (by rfl) ⟨11696, by rfl⟩) (B 23393 (by norm_num) ⟨11696, by rfl⟩ (by norm_num))
theorem R127925 : Reach 127925 := rs (se 5 (by rfl) ⟨5996, by rfl⟩) (B 11993 (by norm_num) ⟨5996, by rfl⟩ (by norm_num))
theorem R62437 : Reach 62437 := rs (se 4 (by rfl) ⟨5853, by rfl⟩) (B 11707 (by norm_num) ⟨5853, by rfl⟩ (by norm_num))
theorem R193589 : Reach 193589 := rs (se 5 (by rfl) ⟨9074, by rfl⟩) (B 18149 (by norm_num) ⟨9074, by rfl⟩ (by norm_num))
theorem R62525 : Reach 62525 := rs (se 3 (by rfl) ⟨11723, by rfl⟩) (B 23447 (by norm_num) ⟨11723, by rfl⟩ (by norm_num))
theorem R62653 : Reach 62653 := rs (se 3 (by rfl) ⟨11747, by rfl⟩) (B 23495 (by norm_num) ⟨11747, by rfl⟩ (by norm_num))
theorem R292085 : Reach 292085 := rs (se 5 (by rfl) ⟨13691, by rfl⟩) (B 27383 (by norm_num) ⟨13691, by rfl⟩ (by norm_num))
theorem R62741 : Reach 62741 := rs (se 6 (by rfl) ⟨1470, by rfl⟩) (B 2941 (by norm_num) ⟨1470, by rfl⟩ (by norm_num))
theorem R128357 : Reach 128357 := rs (se 4 (by rfl) ⟨12033, by rfl⟩) (B 24067 (by norm_num) ⟨12033, by rfl⟩ (by norm_num))
theorem R193909 : Reach 193909 := rs (se 5 (by rfl) ⟨9089, by rfl⟩) (B 18179 (by norm_num) ⟨9089, by rfl⟩ (by norm_num))
theorem R62869 : Reach 62869 := rs (se 6 (by rfl) ⟨1473, by rfl⟩) (B 2947 (by norm_num) ⟨1473, by rfl⟩ (by norm_num))
theorem R95701 : Reach 95701 := rs (se 7 (by rfl) ⟨1121, by rfl⟩) (B 2243 (by norm_num) ⟨1121, by rfl⟩ (by norm_num))
theorem R62957 : Reach 62957 := rs (se 3 (by rfl) ⟨11804, by rfl⟩) (B 23609 (by norm_num) ⟨11804, by rfl⟩ (by norm_num))
theorem R95813 : Reach 95813 := rs (se 4 (by rfl) ⟨8982, by rfl⟩) (B 17965 (by norm_num) ⟨8982, by rfl⟩ (by norm_num))
theorem R63085 : Reach 63085 := rs (se 3 (by rfl) ⟨11828, by rfl⟩) (B 23657 (by norm_num) ⟨11828, by rfl⟩ (by norm_num))
theorem R63173 : Reach 63173 := rs (se 4 (by rfl) ⟨5922, by rfl⟩) (B 11845 (by norm_num) ⟨5922, by rfl⟩ (by norm_num))
theorem R96005 : Reach 96005 := rs (se 4 (by rfl) ⟨9000, by rfl⟩) (B 18001 (by norm_num) ⟨9000, by rfl⟩ (by norm_num))
theorem R128789 : Reach 128789 := rs (se 6 (by rfl) ⟨3018, by rfl⟩) (B 6037 (by norm_num) ⟨3018, by rfl⟩ (by norm_num))
theorem R63301 : Reach 63301 := rs (se 4 (by rfl) ⟨5934, by rfl⟩) (B 11869 (by norm_num) ⟨5934, by rfl⟩ (by norm_num))
theorem R63317 : Reach 63317 := rs (se 9 (by rfl) ⟨185, by rfl⟩) (B 371 (by norm_num) ⟨185, by rfl⟩ (by norm_num))
theorem R63389 : Reach 63389 := rs (se 3 (by rfl) ⟨11885, by rfl⟩) (B 23771 (by norm_num) ⟨11885, by rfl⟩ (by norm_num))
theorem R63517 : Reach 63517 := rs (se 3 (by rfl) ⟨11909, by rfl⟩) (B 23819 (by norm_num) ⟨11909, by rfl⟩ (by norm_num))
theorem R63605 : Reach 63605 := rs (se 5 (by rfl) ⟨2981, by rfl⟩) (B 5963 (by norm_num) ⟨2981, by rfl⟩ (by norm_num))
theorem R129221 : Reach 129221 := rs (se 4 (by rfl) ⟨12114, by rfl⟩) (B 24229 (by norm_num) ⟨12114, by rfl⟩ (by norm_num))
theorem R63733 : Reach 63733 := rs (se 5 (by rfl) ⟨2987, by rfl⟩) (B 5975 (by norm_num) ⟨2987, by rfl⟩ (by norm_num))
theorem R63821 : Reach 63821 := rs (se 3 (by rfl) ⟨11966, by rfl⟩) (B 23933 (by norm_num) ⟨11966, by rfl⟩ (by norm_num))
theorem R424277 : Reach 424277 := rs (se 10 (by rfl) ⟨621, by rfl⟩) (B 1243 (by norm_num) ⟨621, by rfl⟩ (by norm_num))
theorem R63893 : Reach 63893 := rs (se 6 (by rfl) ⟨1497, by rfl⟩) (B 2995 (by norm_num) ⟨1497, by rfl⟩ (by norm_num))
theorem R63949 : Reach 63949 := rs (se 3 (by rfl) ⟨11990, by rfl⟩) (B 23981 (by norm_num) ⟨11990, by rfl⟩ (by norm_num))
theorem R64037 : Reach 64037 := rs (se 4 (by rfl) ⟨6003, by rfl⟩) (B 12007 (by norm_num) ⟨6003, by rfl⟩ (by norm_num))
theorem R227893 : Reach 227893 := rs (se 5 (by rfl) ⟨10682, by rfl⟩) (B 21365 (by norm_num) ⟨10682, by rfl⟩ (by norm_num))
theorem R129653 : Reach 129653 := rs (se 5 (by rfl) ⟨6077, by rfl⟩) (B 12155 (by norm_num) ⟨6077, by rfl⟩ (by norm_num))
theorem R64165 : Reach 64165 := rs (se 4 (by rfl) ⟨6015, by rfl⟩) (B 12031 (by norm_num) ⟨6015, by rfl⟩ (by norm_num))
theorem R96965 : Reach 96965 := rs (se 4 (by rfl) ⟨9090, by rfl⟩) (B 18181 (by norm_num) ⟨9090, by rfl⟩ (by norm_num))
theorem R96997 : Reach 96997 := rs (se 4 (by rfl) ⟨9093, by rfl⟩) (B 18187 (by norm_num) ⟨9093, by rfl⟩ (by norm_num))
theorem R64253 : Reach 64253 := rs (se 3 (by rfl) ⟨12047, by rfl⟩) (B 24095 (by norm_num) ⟨12047, by rfl⟩ (by norm_num))
theorem R97109 : Reach 97109 := rs (se 9 (by rfl) ⟨284, by rfl⟩) (B 569 (by norm_num) ⟨284, by rfl⟩ (by norm_num))
theorem R64381 : Reach 64381 := rs (se 3 (by rfl) ⟨12071, by rfl⟩) (B 24143 (by norm_num) ⟨12071, by rfl⟩ (by norm_num))
theorem R64469 : Reach 64469 := rs (se 7 (by rfl) ⟨755, by rfl⟩) (B 1511 (by norm_num) ⟨755, by rfl⟩ (by norm_num))
theorem R97301 : Reach 97301 := rs (se 6 (by rfl) ⟨2280, by rfl⟩) (B 4561 (by norm_num) ⟨2280, by rfl⟩ (by norm_num))
theorem R130085 : Reach 130085 := rs (se 4 (by rfl) ⟨12195, by rfl⟩) (B 24391 (by norm_num) ⟨12195, by rfl⟩ (by norm_num))
theorem R64597 : Reach 64597 := rs (se 8 (by rfl) ⟨378, by rfl⟩) (B 757 (by norm_num) ⟨378, by rfl⟩ (by norm_num))
theorem R162917 : Reach 162917 := rs (se 4 (by rfl) ⟨15273, by rfl⟩) (B 30547 (by norm_num) ⟨15273, by rfl⟩ (by norm_num))
theorem R64685 : Reach 64685 := rs (se 3 (by rfl) ⟨12128, by rfl⟩) (B 24257 (by norm_num) ⟨12128, by rfl⟩ (by norm_num))
theorem R64813 : Reach 64813 := rs (se 3 (by rfl) ⟨12152, by rfl⟩) (B 24305 (by norm_num) ⟨12152, by rfl⟩ (by norm_num))
theorem R163205 : Reach 163205 := rs (se 4 (by rfl) ⟨15300, by rfl⟩) (B 30601 (by norm_num) ⟨15300, by rfl⟩ (by norm_num))
theorem R64901 : Reach 64901 := rs (se 4 (by rfl) ⟨6084, by rfl⟩) (B 12169 (by norm_num) ⟨6084, by rfl⟩ (by norm_num))
theorem R130517 : Reach 130517 := rs (se 7 (by rfl) ⟨1529, by rfl⟩) (B 3059 (by norm_num) ⟨1529, by rfl⟩ (by norm_num))
theorem R65029 : Reach 65029 := rs (se 4 (by rfl) ⟨6096, by rfl⟩) (B 12193 (by norm_num) ⟨6096, by rfl⟩ (by norm_num))
theorem R196181 : Reach 196181 := rs (se 8 (by rfl) ⟨1149, by rfl⟩) (B 2299 (by norm_num) ⟨1149, by rfl⟩ (by norm_num))
theorem R65117 : Reach 65117 := rs (se 3 (by rfl) ⟨12209, by rfl⟩) (B 24419 (by norm_num) ⟨12209, by rfl⟩ (by norm_num))
theorem R65245 : Reach 65245 := rs (se 3 (by rfl) ⟨12233, by rfl⟩) (B 24467 (by norm_num) ⟨12233, by rfl⟩ (by norm_num))
theorem R65333 : Reach 65333 := rs (se 5 (by rfl) ⟨3062, by rfl⟩) (B 6125 (by norm_num) ⟨3062, by rfl⟩ (by norm_num))
theorem R130949 : Reach 130949 := rs (se 4 (by rfl) ⟨12276, by rfl⟩) (B 24553 (by norm_num) ⟨12276, by rfl⟩ (by norm_num))
theorem R65461 : Reach 65461 := rs (se 5 (by rfl) ⟨3068, by rfl⟩) (B 6137 (by norm_num) ⟨3068, by rfl⟩ (by norm_num))
theorem R98293 : Reach 98293 := rs (se 5 (by rfl) ⟨4607, by rfl⟩) (B 9215 (by norm_num) ⟨4607, by rfl⟩ (by norm_num))
theorem R163889 : Reach 163889 := rs (se 2 (by rfl) ⟨61458, by rfl⟩) R122917
theorem R65603 : Reach 65603 := rs (se 1 (by rfl) ⟨49202, by rfl⟩) R98405
theorem R98435 : Reach 98435 := rs (se 1 (by rfl) ⟨73826, by rfl⟩) R147653
theorem R65731 : Reach 65731 := rs (se 1 (by rfl) ⟨49298, by rfl⟩) R98597
theorem R65777 : Reach 65777 := rs (se 2 (by rfl) ⟨24666, by rfl⟩) R49333
theorem R65873 : Reach 65873 := rs (se 2 (by rfl) ⟨24702, by rfl⟩) R49405
theorem R66001 : Reach 66001 := rs (se 2 (by rfl) ⟨24750, by rfl⟩) R49501
theorem R131597 : Reach 131597 := rs (se 3 (by rfl) ⟨24674, by rfl⟩) R49349
theorem R656099 : Reach 656099 := rs (se 1 (by rfl) ⟨492074, by rfl⟩) R984149
theorem R66673 : Reach 66673 := rs (se 2 (by rfl) ⟨25002, by rfl⟩) R50005
theorem R230627 : Reach 230627 := rs (se 1 (by rfl) ⟨172970, by rfl⟩) R345941
theorem R99949 : Reach 99949 := rs (se 3 (by rfl) ⟨18740, by rfl⟩) R37481
theorem R132977 : Reach 132977 := rs (se 2 (by rfl) ⟨49866, by rfl⟩) R99733
theorem R296945 : Reach 296945 := rs (se 2 (by rfl) ⟨111354, by rfl⟩) R222709
theorem R67729 : Reach 67729 := rs (se 2 (by rfl) ⟨25398, by rfl⟩) R50797
theorem R35123 : Reach 35123 := rs (se 1 (by rfl) ⟨26342, by rfl⟩) R52685
theorem R35139 : Reach 35139 := rs (se 1 (by rfl) ⟨26354, by rfl⟩) R52709
theorem R35155 : Reach 35155 := rs (se 1 (by rfl) ⟨26366, by rfl⟩) R52733
theorem R35171 : Reach 35171 := rs (se 1 (by rfl) ⟨26378, by rfl⟩) R52757
theorem R690545 : Reach 690545 := rs (se 2 (by rfl) ⟨258954, by rfl⟩) R517909
theorem R35187 : Reach 35187 := rs (se 1 (by rfl) ⟨26390, by rfl⟩) R52781
theorem R35203 : Reach 35203 := rs (se 1 (by rfl) ⟨26402, by rfl⟩) R52805
theorem R100739 : Reach 100739 := rs (se 1 (by rfl) ⟨75554, by rfl⟩) R151109
theorem R35219 : Reach 35219 := rs (se 1 (by rfl) ⟨26414, by rfl⟩) R52829
theorem R35235 : Reach 35235 := rs (se 1 (by rfl) ⟨26426, by rfl⟩) R52853
theorem R35251 : Reach 35251 := rs (se 1 (by rfl) ⟨26438, by rfl⟩) R52877
theorem R35267 : Reach 35267 := rs (se 1 (by rfl) ⟨26450, by rfl⟩) R52901
theorem R166349 : Reach 166349 := rs (se 3 (by rfl) ⟨31190, by rfl⟩) R62381
theorem R35283 : Reach 35283 := rs (se 1 (by rfl) ⟨26462, by rfl⟩) R52925
theorem R35299 : Reach 35299 := rs (se 1 (by rfl) ⟨26474, by rfl⟩) R52949
theorem R35315 : Reach 35315 := rs (se 1 (by rfl) ⟨26486, by rfl⟩) R52973
theorem R35331 : Reach 35331 := rs (se 1 (by rfl) ⟨26498, by rfl⟩) R52997
theorem R35347 : Reach 35347 := rs (se 1 (by rfl) ⟨26510, by rfl⟩) R53021
theorem R35363 : Reach 35363 := rs (se 1 (by rfl) ⟨26522, by rfl⟩) R53045
theorem R68131 : Reach 68131 := rs (se 1 (by rfl) ⟨51098, by rfl⟩) R102197
theorem R35379 : Reach 35379 := rs (se 1 (by rfl) ⟨26534, by rfl⟩) R53069
theorem R35395 : Reach 35395 := rs (se 1 (by rfl) ⟨26546, by rfl⟩) R53093
theorem R68177 : Reach 68177 := rs (se 2 (by rfl) ⟨25566, by rfl⟩) R51133
theorem R35411 : Reach 35411 := rs (se 1 (by rfl) ⟨26558, by rfl⟩) R53117
theorem R35427 : Reach 35427 := rs (se 1 (by rfl) ⟨26570, by rfl⟩) R53141
theorem R35443 : Reach 35443 := rs (se 1 (by rfl) ⟨26582, by rfl⟩) R53165
theorem R35459 : Reach 35459 := rs (se 1 (by rfl) ⟨26594, by rfl⟩) R53189
theorem R35475 : Reach 35475 := rs (se 1 (by rfl) ⟨26606, by rfl⟩) R53213
theorem R35491 : Reach 35491 := rs (se 1 (by rfl) ⟨26618, by rfl⟩) R53237
theorem R35507 : Reach 35507 := rs (se 1 (by rfl) ⟨26630, by rfl⟩) R53261
theorem R35523 : Reach 35523 := rs (se 1 (by rfl) ⟨26642, by rfl⟩) R53285
theorem R35539 : Reach 35539 := rs (se 1 (by rfl) ⟨26654, by rfl⟩) R53309
theorem R1018595 : Reach 1018595 := rs (se 1 (by rfl) ⟨763946, by rfl⟩) R1527893
theorem R35555 : Reach 35555 := rs (se 1 (by rfl) ⟨26666, by rfl⟩) R53333
theorem R35571 : Reach 35571 := rs (se 1 (by rfl) ⟨26678, by rfl⟩) R53357
theorem R35587 : Reach 35587 := rs (se 1 (by rfl) ⟨26690, by rfl⟩) R53381
theorem R35603 : Reach 35603 := rs (se 1 (by rfl) ⟨26702, by rfl⟩) R53405
theorem R35619 : Reach 35619 := rs (se 1 (by rfl) ⟨26714, by rfl⟩) R53429
theorem R166691 : Reach 166691 := rs (se 1 (by rfl) ⟨125018, by rfl⟩) R250037
theorem R35635 : Reach 35635 := rs (se 1 (by rfl) ⟨26726, by rfl⟩) R53453
theorem R35651 : Reach 35651 := rs (se 1 (by rfl) ⟨26738, by rfl⟩) R53477
theorem R35667 : Reach 35667 := rs (se 1 (by rfl) ⟨26750, by rfl⟩) R53501
theorem R35683 : Reach 35683 := rs (se 1 (by rfl) ⟨26762, by rfl⟩) R53525
theorem R199523 : Reach 199523 := rs (se 1 (by rfl) ⟨149642, by rfl⟩) R299285
theorem R68465 : Reach 68465 := rs (se 2 (by rfl) ⟨25674, by rfl⟩) R51349
theorem R35699 : Reach 35699 := rs (se 1 (by rfl) ⟨26774, by rfl⟩) R53549
theorem R166769 : Reach 166769 := rs (se 2 (by rfl) ⟨62538, by rfl⟩) R125077
theorem R35715 : Reach 35715 := rs (se 1 (by rfl) ⟨26786, by rfl⟩) R53573
theorem R35731 : Reach 35731 := rs (se 1 (by rfl) ⟨26798, by rfl⟩) R53597
theorem R35747 : Reach 35747 := rs (se 1 (by rfl) ⟨26810, by rfl⟩) R53621
theorem R35763 : Reach 35763 := rs (se 1 (by rfl) ⟨26822, by rfl⟩) R53645
theorem R35779 : Reach 35779 := rs (se 1 (by rfl) ⟨26834, by rfl⟩) R53669
theorem R854981 : Reach 854981 := rs (se 4 (by rfl) ⟨80154, by rfl⟩) R160309
theorem R35795 : Reach 35795 := rs (se 1 (by rfl) ⟨26846, by rfl⟩) R53693
theorem R35811 : Reach 35811 := rs (se 1 (by rfl) ⟨26858, by rfl⟩) R53717
theorem R35827 : Reach 35827 := rs (se 1 (by rfl) ⟨26870, by rfl⟩) R53741
theorem R35843 : Reach 35843 := rs (se 1 (by rfl) ⟨26882, by rfl⟩) R53765
theorem R199685 : Reach 199685 := rs (se 4 (by rfl) ⟨18720, by rfl⟩) R37441
theorem R35859 : Reach 35859 := rs (se 1 (by rfl) ⟨26894, by rfl⟩) R53789
theorem R35875 : Reach 35875 := rs (se 1 (by rfl) ⟨26906, by rfl⟩) R53813
theorem R35891 : Reach 35891 := rs (se 1 (by rfl) ⟨26918, by rfl⟩) R53837
theorem R35907 : Reach 35907 := rs (se 1 (by rfl) ⟨26930, by rfl⟩) R53861
theorem R35923 : Reach 35923 := rs (se 1 (by rfl) ⟨26942, by rfl⟩) R53885
theorem R134243 : Reach 134243 := rs (se 1 (by rfl) ⟨100682, by rfl⟩) R201365
theorem R35939 : Reach 35939 := rs (se 1 (by rfl) ⟨26954, by rfl⟩) R53909
theorem R134257 : Reach 134257 := rs (se 2 (by rfl) ⟨50346, by rfl⟩) R100693
theorem R35955 : Reach 35955 := rs (se 1 (by rfl) ⟨26966, by rfl⟩) R53933
theorem R35971 : Reach 35971 := rs (se 1 (by rfl) ⟨26978, by rfl⟩) R53957
theorem R35987 : Reach 35987 := rs (se 1 (by rfl) ⟨26990, by rfl⟩) R53981
theorem R36003 : Reach 36003 := rs (se 1 (by rfl) ⟨27002, by rfl⟩) R54005
theorem R101549 : Reach 101549 := rs (se 3 (by rfl) ⟨19040, by rfl⟩) R38081
theorem R36019 : Reach 36019 := rs (se 1 (by rfl) ⟨27014, by rfl⟩) R54029
theorem R36035 : Reach 36035 := rs (se 1 (by rfl) ⟨27026, by rfl⟩) R54053
theorem R36051 : Reach 36051 := rs (se 1 (by rfl) ⟨27038, by rfl⟩) R54077
theorem R36067 : Reach 36067 := rs (se 1 (by rfl) ⟨27050, by rfl⟩) R54101
theorem R36083 : Reach 36083 := rs (se 1 (by rfl) ⟨27062, by rfl⟩) R54125
theorem R36099 : Reach 36099 := rs (se 1 (by rfl) ⟨27074, by rfl⟩) R54149
theorem R36115 : Reach 36115 := rs (se 1 (by rfl) ⟨27086, by rfl⟩) R54173
theorem R36131 : Reach 36131 := rs (se 1 (by rfl) ⟨27098, by rfl⟩) R54197
theorem R36147 : Reach 36147 := rs (se 1 (by rfl) ⟨27110, by rfl⟩) R54221
theorem R36163 : Reach 36163 := rs (se 1 (by rfl) ⟨27122, by rfl⟩) R54245
theorem R36179 : Reach 36179 := rs (se 1 (by rfl) ⟨27134, by rfl⟩) R54269
theorem R36195 : Reach 36195 := rs (se 1 (by rfl) ⟨27146, by rfl⟩) R54293
theorem R36211 : Reach 36211 := rs (se 1 (by rfl) ⟨27158, by rfl⟩) R54317
theorem R36227 : Reach 36227 := rs (se 1 (by rfl) ⟨27170, by rfl⟩) R54341
theorem R36243 : Reach 36243 := rs (se 1 (by rfl) ⟨27182, by rfl⟩) R54365
theorem R36259 : Reach 36259 := rs (se 1 (by rfl) ⟨27194, by rfl⟩) R54389
theorem R36275 : Reach 36275 := rs (se 1 (by rfl) ⟨27206, by rfl⟩) R54413
theorem R36291 : Reach 36291 := rs (se 1 (by rfl) ⟨27218, by rfl⟩) R54437
theorem R36307 : Reach 36307 := rs (se 1 (by rfl) ⟨27230, by rfl⟩) R54461
theorem R36323 : Reach 36323 := rs (se 1 (by rfl) ⟨27242, by rfl⟩) R54485
theorem R36339 : Reach 36339 := rs (se 1 (by rfl) ⟨27254, by rfl⟩) R54509
theorem R36355 : Reach 36355 := rs (se 1 (by rfl) ⟨27266, by rfl⟩) R54533
theorem R36371 : Reach 36371 := rs (se 1 (by rfl) ⟨27278, by rfl⟩) R54557
theorem R36387 : Reach 36387 := rs (se 1 (by rfl) ⟨27290, by rfl⟩) R54581
theorem R36403 : Reach 36403 := rs (se 1 (by rfl) ⟨27302, by rfl⟩) R54605
theorem R36419 : Reach 36419 := rs (se 1 (by rfl) ⟨27314, by rfl⟩) R54629
theorem R69187 : Reach 69187 := rs (se 1 (by rfl) ⟨51890, by rfl⟩) R103781
theorem R101969 : Reach 101969 := rs (se 2 (by rfl) ⟨38238, by rfl⟩) R76477
theorem R36435 : Reach 36435 := rs (se 1 (by rfl) ⟨27326, by rfl⟩) R54653
theorem R36451 : Reach 36451 := rs (se 1 (by rfl) ⟨27338, by rfl⟩) R54677
theorem R36467 : Reach 36467 := rs (se 1 (by rfl) ⟨27350, by rfl⟩) R54701
theorem R36483 : Reach 36483 := rs (se 1 (by rfl) ⟨27362, by rfl⟩) R54725
theorem R36499 : Reach 36499 := rs (se 1 (by rfl) ⟨27374, by rfl⟩) R54749
theorem R36515 : Reach 36515 := rs (se 1 (by rfl) ⟨27386, by rfl⟩) R54773
theorem R36531 : Reach 36531 := rs (se 1 (by rfl) ⟨27398, by rfl⟩) R54797
theorem R36547 : Reach 36547 := rs (se 1 (by rfl) ⟨27410, by rfl⟩) R54821
theorem R36563 : Reach 36563 := rs (se 1 (by rfl) ⟨27422, by rfl⟩) R54845
theorem R36579 : Reach 36579 := rs (se 1 (by rfl) ⟨27434, by rfl⟩) R54869
theorem R36595 : Reach 36595 := rs (se 1 (by rfl) ⟨27446, by rfl⟩) R54893
theorem R36611 : Reach 36611 := rs (se 1 (by rfl) ⟨27458, by rfl⟩) R54917
theorem R36627 : Reach 36627 := rs (se 1 (by rfl) ⟨27470, by rfl⟩) R54941
theorem R36643 : Reach 36643 := rs (se 1 (by rfl) ⟨27482, by rfl⟩) R54965
theorem R36659 : Reach 36659 := rs (se 1 (by rfl) ⟨27494, by rfl⟩) R54989
theorem R36675 : Reach 36675 := rs (se 1 (by rfl) ⟨27506, by rfl⟩) R55013
theorem R69457 : Reach 69457 := rs (se 2 (by rfl) ⟨26046, by rfl⟩) R52093
theorem R36691 : Reach 36691 := rs (se 1 (by rfl) ⟨27518, by rfl⟩) R55037
theorem R36707 : Reach 36707 := rs (se 1 (by rfl) ⟨27530, by rfl⟩) R55061
theorem R36723 : Reach 36723 := rs (se 1 (by rfl) ⟨27542, by rfl⟩) R55085
theorem R36739 : Reach 36739 := rs (se 1 (by rfl) ⟨27554, by rfl⟩) R55109
theorem R36755 : Reach 36755 := rs (se 1 (by rfl) ⟨27566, by rfl⟩) R55133
theorem R36771 : Reach 36771 := rs (se 1 (by rfl) ⟨27578, by rfl⟩) R55157
theorem R36787 : Reach 36787 := rs (se 1 (by rfl) ⟨27590, by rfl⟩) R55181
theorem R36803 : Reach 36803 := rs (se 1 (by rfl) ⟨27602, by rfl⟩) R55205
theorem R36819 : Reach 36819 := rs (se 1 (by rfl) ⟨27614, by rfl⟩) R55229
theorem R36835 : Reach 36835 := rs (se 1 (by rfl) ⟨27626, by rfl⟩) R55253
theorem R69617 : Reach 69617 := rs (se 2 (by rfl) ⟨26106, by rfl⟩) R52213
theorem R36851 : Reach 36851 := rs (se 1 (by rfl) ⟨27638, by rfl⟩) R55277
theorem R69635 : Reach 69635 := rs (se 1 (by rfl) ⟨52226, by rfl⟩) R104453
theorem R36867 : Reach 36867 := rs (se 1 (by rfl) ⟨27650, by rfl⟩) R55301
theorem R36883 : Reach 36883 := rs (se 1 (by rfl) ⟨27662, by rfl⟩) R55325
theorem R36899 : Reach 36899 := rs (se 1 (by rfl) ⟨27674, by rfl⟩) R55349
theorem R36915 : Reach 36915 := rs (se 1 (by rfl) ⟨27686, by rfl⟩) R55373
theorem R36931 : Reach 36931 := rs (se 1 (by rfl) ⟨27698, by rfl⟩) R55397
theorem R36947 : Reach 36947 := rs (se 1 (by rfl) ⟨27710, by rfl⟩) R55421
theorem R36963 : Reach 36963 := rs (se 1 (by rfl) ⟨27722, by rfl⟩) R55445
theorem R36979 : Reach 36979 := rs (se 1 (by rfl) ⟨27734, by rfl⟩) R55469
theorem R36995 : Reach 36995 := rs (se 1 (by rfl) ⟨27746, by rfl⟩) R55493
theorem R37011 : Reach 37011 := rs (se 1 (by rfl) ⟨27758, by rfl⟩) R55517
theorem R37027 : Reach 37027 := rs (se 1 (by rfl) ⟨27770, by rfl⟩) R55541
theorem R37043 : Reach 37043 := rs (se 1 (by rfl) ⟨27782, by rfl⟩) R55565
theorem R37059 : Reach 37059 := rs (se 1 (by rfl) ⟨27794, by rfl⟩) R55589
theorem R37075 : Reach 37075 := rs (se 1 (by rfl) ⟨27806, by rfl⟩) R55613
theorem R37091 : Reach 37091 := rs (se 1 (by rfl) ⟨27818, by rfl⟩) R55637
theorem R37107 : Reach 37107 := rs (se 1 (by rfl) ⟨27830, by rfl⟩) R55661
theorem R37123 : Reach 37123 := rs (se 1 (by rfl) ⟨27842, by rfl⟩) R55685
theorem R37139 : Reach 37139 := rs (se 1 (by rfl) ⟨27854, by rfl⟩) R55709
theorem R69923 : Reach 69923 := rs (se 1 (by rfl) ⟨52442, by rfl⟩) R104885
theorem R37155 : Reach 37155 := rs (se 1 (by rfl) ⟨27866, by rfl⟩) R55733
theorem R37171 : Reach 37171 := rs (se 1 (by rfl) ⟨27878, by rfl⟩) R55757
theorem R37187 : Reach 37187 := rs (se 1 (by rfl) ⟨27890, by rfl⟩) R55781
theorem R37203 : Reach 37203 := rs (se 1 (by rfl) ⟨27902, by rfl⟩) R55805
theorem R37219 : Reach 37219 := rs (se 1 (by rfl) ⟨27914, by rfl⟩) R55829
theorem R37235 : Reach 37235 := rs (se 1 (by rfl) ⟨27926, by rfl⟩) R55853
theorem R37251 : Reach 37251 := rs (se 1 (by rfl) ⟨27938, by rfl⟩) R55877
theorem R102797 : Reach 102797 := rs (se 3 (by rfl) ⟨19274, by rfl⟩) R38549
theorem R37267 : Reach 37267 := rs (se 1 (by rfl) ⟨27950, by rfl⟩) R55901
theorem R135587 : Reach 135587 := rs (se 1 (by rfl) ⟨101690, by rfl⟩) R203381
theorem R37283 : Reach 37283 := rs (se 1 (by rfl) ⟨27962, by rfl⟩) R55925
theorem R37299 : Reach 37299 := rs (se 1 (by rfl) ⟨27974, by rfl⟩) R55949
theorem R37315 : Reach 37315 := rs (se 1 (by rfl) ⟨27986, by rfl⟩) R55973
theorem R37331 : Reach 37331 := rs (se 1 (by rfl) ⟨27998, by rfl⟩) R55997
theorem R37347 : Reach 37347 := rs (se 1 (by rfl) ⟨28010, by rfl⟩) R56021
theorem R37363 : Reach 37363 := rs (se 1 (by rfl) ⟨28022, by rfl⟩) R56045
theorem R37379 : Reach 37379 := rs (se 1 (by rfl) ⟨28034, by rfl⟩) R56069
theorem R37395 : Reach 37395 := rs (se 1 (by rfl) ⟨28046, by rfl⟩) R56093
theorem R135715 : Reach 135715 := rs (se 1 (by rfl) ⟨101786, by rfl⟩) R203573
theorem R37411 : Reach 37411 := rs (se 1 (by rfl) ⟨28058, by rfl⟩) R56117
theorem R37427 : Reach 37427 := rs (se 1 (by rfl) ⟨28070, by rfl⟩) R56141
theorem R37443 : Reach 37443 := rs (se 1 (by rfl) ⟨28082, by rfl⟩) R56165
theorem R37459 : Reach 37459 := rs (se 1 (by rfl) ⟨28094, by rfl⟩) R56189
theorem R37475 : Reach 37475 := rs (se 1 (by rfl) ⟨28106, by rfl⟩) R56213
theorem R37491 : Reach 37491 := rs (se 1 (by rfl) ⟨28118, by rfl⟩) R56237
theorem R37507 : Reach 37507 := rs (se 1 (by rfl) ⟨28130, by rfl⟩) R56261
theorem R37523 : Reach 37523 := rs (se 1 (by rfl) ⟨28142, by rfl⟩) R56285
theorem R37539 : Reach 37539 := rs (se 1 (by rfl) ⟨28154, by rfl⟩) R56309
theorem R103085 : Reach 103085 := rs (se 3 (by rfl) ⟨19328, by rfl⟩) R38657
theorem R37555 : Reach 37555 := rs (se 1 (by rfl) ⟨28166, by rfl⟩) R56333
theorem R37571 : Reach 37571 := rs (se 1 (by rfl) ⟨28178, by rfl⟩) R56357
theorem R37587 : Reach 37587 := rs (se 1 (by rfl) ⟨28190, by rfl⟩) R56381
theorem R37603 : Reach 37603 := rs (se 1 (by rfl) ⟨28202, by rfl⟩) R56405
theorem R37619 : Reach 37619 := rs (se 1 (by rfl) ⟨28214, by rfl⟩) R56429
theorem R37635 : Reach 37635 := rs (se 1 (by rfl) ⟨28226, by rfl⟩) R56453
theorem R70417 : Reach 70417 := rs (se 2 (by rfl) ⟨26406, by rfl⟩) R52813
theorem R37651 : Reach 37651 := rs (se 1 (by rfl) ⟨28238, by rfl⟩) R56477
theorem R37667 : Reach 37667 := rs (se 1 (by rfl) ⟨28250, by rfl⟩) R56501
theorem R37683 : Reach 37683 := rs (se 1 (by rfl) ⟨28262, by rfl⟩) R56525
theorem R37699 : Reach 37699 := rs (se 1 (by rfl) ⟨28274, by rfl⟩) R56549
theorem R201541 : Reach 201541 := rs (se 4 (by rfl) ⟨18894, by rfl⟩) R37789
theorem R37715 : Reach 37715 := rs (se 1 (by rfl) ⟨28286, by rfl⟩) R56573
theorem R37731 : Reach 37731 := rs (se 1 (by rfl) ⟨28298, by rfl⟩) R56597
theorem R37747 : Reach 37747 := rs (se 1 (by rfl) ⟨28310, by rfl⟩) R56621
theorem R37763 : Reach 37763 := rs (se 1 (by rfl) ⟨28322, by rfl⟩) R56645
theorem R37779 : Reach 37779 := rs (se 1 (by rfl) ⟨28334, by rfl⟩) R56669
theorem R37795 : Reach 37795 := rs (se 1 (by rfl) ⟨28346, by rfl⟩) R56693
theorem R37811 : Reach 37811 := rs (se 1 (by rfl) ⟨28358, by rfl⟩) R56717
theorem R37827 : Reach 37827 := rs (se 1 (by rfl) ⟨28370, by rfl⟩) R56741
theorem R37843 : Reach 37843 := rs (se 1 (by rfl) ⟨28382, by rfl⟩) R56765
theorem R37859 : Reach 37859 := rs (se 1 (by rfl) ⟨28394, by rfl⟩) R56789
theorem R37875 : Reach 37875 := rs (se 1 (by rfl) ⟨28406, by rfl⟩) R56813
theorem R103427 : Reach 103427 := rs (se 1 (by rfl) ⟨77570, by rfl⟩) R155141
theorem R37891 : Reach 37891 := rs (se 1 (by rfl) ⟨28418, by rfl⟩) R56837
theorem R37907 : Reach 37907 := rs (se 1 (by rfl) ⟨28430, by rfl⟩) R56861
theorem R37923 : Reach 37923 := rs (se 1 (by rfl) ⟨28442, by rfl⟩) R56885
theorem R37939 : Reach 37939 := rs (se 1 (by rfl) ⟨28454, by rfl⟩) R56909
theorem R37955 : Reach 37955 := rs (se 1 (by rfl) ⟨28466, by rfl⟩) R56933
theorem R201797 : Reach 201797 := rs (se 4 (by rfl) ⟨18918, by rfl⟩) R37837
theorem R169037 : Reach 169037 := rs (se 3 (by rfl) ⟨31694, by rfl⟩) R63389
theorem R37971 : Reach 37971 := rs (se 1 (by rfl) ⟨28478, by rfl⟩) R56957
theorem R37987 : Reach 37987 := rs (se 1 (by rfl) ⟨28490, by rfl⟩) R56981
theorem R2823281 : Reach 2823281 := rs (se 2 (by rfl) ⟨1058730, by rfl⟩) R2117461
theorem R38003 : Reach 38003 := rs (se 1 (by rfl) ⟨28502, by rfl⟩) R57005
theorem R38019 : Reach 38019 := rs (se 1 (by rfl) ⟨28514, by rfl⟩) R57029
theorem R38035 : Reach 38035 := rs (se 1 (by rfl) ⟨28526, by rfl⟩) R57053
theorem R38051 : Reach 38051 := rs (se 1 (by rfl) ⟨28538, by rfl⟩) R57077
theorem R38067 : Reach 38067 := rs (se 1 (by rfl) ⟨28550, by rfl⟩) R57101
theorem R38083 : Reach 38083 := rs (se 1 (by rfl) ⟨28562, by rfl⟩) R57125
theorem R70865 : Reach 70865 := rs (se 2 (by rfl) ⟨26574, by rfl⟩) R53149
theorem R38099 : Reach 38099 := rs (se 1 (by rfl) ⟨28574, by rfl⟩) R57149
theorem R38115 : Reach 38115 := rs (se 1 (by rfl) ⟨28586, by rfl⟩) R57173
theorem R38131 : Reach 38131 := rs (se 1 (by rfl) ⟨28598, by rfl⟩) R57197
theorem R38147 : Reach 38147 := rs (se 1 (by rfl) ⟨28610, by rfl⟩) R57221
theorem R38163 : Reach 38163 := rs (se 1 (by rfl) ⟨28622, by rfl⟩) R57245
theorem R38179 : Reach 38179 := rs (se 1 (by rfl) ⟨28634, by rfl⟩) R57269
theorem R38195 : Reach 38195 := rs (se 1 (by rfl) ⟨28646, by rfl⟩) R57293
theorem R38211 : Reach 38211 := rs (se 1 (by rfl) ⟨28658, by rfl⟩) R57317
theorem R38227 : Reach 38227 := rs (se 1 (by rfl) ⟨28670, by rfl⟩) R57341
theorem R38243 : Reach 38243 := rs (se 1 (by rfl) ⟨28682, by rfl⟩) R57365
theorem R38259 : Reach 38259 := rs (se 1 (by rfl) ⟨28694, by rfl⟩) R57389
theorem R38275 : Reach 38275 := rs (se 1 (by rfl) ⟨28706, by rfl⟩) R57413
theorem R38291 : Reach 38291 := rs (se 1 (by rfl) ⟨28718, by rfl⟩) R57437
theorem R38307 : Reach 38307 := rs (se 1 (by rfl) ⟨28730, by rfl⟩) R57461
theorem R38323 : Reach 38323 := rs (se 1 (by rfl) ⟨28742, by rfl⟩) R57485
theorem R38339 : Reach 38339 := rs (se 1 (by rfl) ⟨28754, by rfl⟩) R57509
theorem R38355 : Reach 38355 := rs (se 1 (by rfl) ⟨28766, by rfl⟩) R57533
theorem R38371 : Reach 38371 := rs (se 1 (by rfl) ⟨28778, by rfl⟩) R57557
theorem R38387 : Reach 38387 := rs (se 1 (by rfl) ⟨28790, by rfl⟩) R57581
theorem R38403 : Reach 38403 := rs (se 1 (by rfl) ⟨28802, by rfl⟩) R57605
theorem R38419 : Reach 38419 := rs (se 1 (by rfl) ⟨28814, by rfl⟩) R57629
theorem R38435 : Reach 38435 := rs (se 1 (by rfl) ⟨28826, by rfl⟩) R57653
theorem R38451 : Reach 38451 := rs (se 1 (by rfl) ⟨28838, by rfl⟩) R57677
theorem R38467 : Reach 38467 := rs (se 1 (by rfl) ⟨28850, by rfl⟩) R57701
theorem R38483 : Reach 38483 := rs (se 1 (by rfl) ⟨28862, by rfl⟩) R57725
theorem R38499 : Reach 38499 := rs (se 1 (by rfl) ⟨28874, by rfl⟩) R57749
theorem R38515 : Reach 38515 := rs (se 1 (by rfl) ⟨28886, by rfl⟩) R57773
theorem R38531 : Reach 38531 := rs (se 1 (by rfl) ⟨28898, by rfl⟩) R57797
theorem R38547 : Reach 38547 := rs (se 1 (by rfl) ⟨28910, by rfl⟩) R57821
theorem R38563 : Reach 38563 := rs (se 1 (by rfl) ⟨28922, by rfl⟩) R57845
theorem R38579 : Reach 38579 := rs (se 1 (by rfl) ⟨28934, by rfl⟩) R57869
theorem R38595 : Reach 38595 := rs (se 1 (by rfl) ⟨28946, by rfl⟩) R57893
theorem R366277 : Reach 366277 := rs (se 4 (by rfl) ⟨34338, by rfl⟩) R68677
theorem R38611 : Reach 38611 := rs (se 1 (by rfl) ⟨28958, by rfl⟩) R57917
theorem R38627 : Reach 38627 := rs (se 1 (by rfl) ⟨28970, by rfl⟩) R57941
theorem R38643 : Reach 38643 := rs (se 1 (by rfl) ⟨28982, by rfl⟩) R57965
theorem R38659 : Reach 38659 := rs (se 1 (by rfl) ⟨28994, by rfl⟩) R57989
theorem R38675 : Reach 38675 := rs (se 1 (by rfl) ⟨29006, by rfl⟩) R58013
theorem R71459 : Reach 71459 := rs (se 1 (by rfl) ⟨53594, by rfl⟩) R107189
theorem R38691 : Reach 38691 := rs (se 1 (by rfl) ⟨29018, by rfl⟩) R58037
theorem R104237 : Reach 104237 := rs (se 3 (by rfl) ⟨19544, by rfl⟩) R39089
theorem R38707 : Reach 38707 := rs (se 1 (by rfl) ⟨29030, by rfl⟩) R58061
theorem R71491 : Reach 71491 := rs (se 1 (by rfl) ⟨53618, by rfl⟩) R107237
theorem R38723 : Reach 38723 := rs (se 1 (by rfl) ⟨29042, by rfl⟩) R58085
theorem R38739 : Reach 38739 := rs (se 1 (by rfl) ⟨29054, by rfl⟩) R58109
theorem R38755 : Reach 38755 := rs (se 1 (by rfl) ⟨29066, by rfl⟩) R58133
theorem R38771 : Reach 38771 := rs (se 1 (by rfl) ⟨29078, by rfl⟩) R58157
theorem R38787 : Reach 38787 := rs (se 1 (by rfl) ⟨29090, by rfl⟩) R58181
theorem R38803 : Reach 38803 := rs (se 1 (by rfl) ⟨29102, by rfl⟩) R58205
theorem R38819 : Reach 38819 := rs (se 1 (by rfl) ⟨29114, by rfl⟩) R58229
theorem R38835 : Reach 38835 := rs (se 1 (by rfl) ⟨29126, by rfl⟩) R58253
theorem R38851 : Reach 38851 := rs (se 1 (by rfl) ⟨29138, by rfl⟩) R58277
theorem R38867 : Reach 38867 := rs (se 1 (by rfl) ⟨29150, by rfl⟩) R58301
theorem R38883 : Reach 38883 := rs (se 1 (by rfl) ⟨29162, by rfl⟩) R58325
theorem R104429 : Reach 104429 := rs (se 3 (by rfl) ⟨19580, by rfl⟩) R39161
theorem R38899 : Reach 38899 := rs (se 1 (by rfl) ⟨29174, by rfl⟩) R58349
theorem R38915 : Reach 38915 := rs (se 1 (by rfl) ⟨29186, by rfl⟩) R58373
theorem R38931 : Reach 38931 := rs (se 1 (by rfl) ⟨29198, by rfl⟩) R58397
theorem R38947 : Reach 38947 := rs (se 1 (by rfl) ⟨29210, by rfl⟩) R58421
theorem R38963 : Reach 38963 := rs (se 1 (by rfl) ⟨29222, by rfl⟩) R58445
theorem R38979 : Reach 38979 := rs (se 1 (by rfl) ⟨29234, by rfl⟩) R58469
theorem R71761 : Reach 71761 := rs (se 2 (by rfl) ⟨26910, by rfl⟩) R53821
theorem R38995 : Reach 38995 := rs (se 1 (by rfl) ⟨29246, by rfl⟩) R58493
theorem R39011 : Reach 39011 := rs (se 1 (by rfl) ⟨29258, by rfl⟩) R58517
theorem R39027 : Reach 39027 := rs (se 1 (by rfl) ⟨29270, by rfl⟩) R58541
theorem R39043 : Reach 39043 := rs (se 1 (by rfl) ⟨29282, by rfl⟩) R58565
theorem R39059 : Reach 39059 := rs (se 1 (by rfl) ⟨29294, by rfl⟩) R58589
theorem R39075 : Reach 39075 := rs (se 1 (by rfl) ⟨29306, by rfl⟩) R58613
theorem R39091 : Reach 39091 := rs (se 1 (by rfl) ⟨29318, by rfl⟩) R58637
theorem R39107 : Reach 39107 := rs (se 1 (by rfl) ⟨29330, by rfl⟩) R58661
theorem R399587 : Reach 399587 := rs (se 1 (by rfl) ⟨299690, by rfl⟩) R599381
theorem R71921 : Reach 71921 := rs (se 2 (by rfl) ⟨26970, by rfl⟩) R53941
theorem R104771 : Reach 104771 := rs (se 1 (by rfl) ⟨78578, by rfl⟩) R157157
theorem R170381 : Reach 170381 := rs (se 3 (by rfl) ⟨31946, by rfl⟩) R63893
theorem R39443 : Reach 39443 := rs (se 1 (by rfl) ⟨29582, by rfl⟩) R59165
theorem R72227 : Reach 72227 := rs (se 1 (by rfl) ⟨54170, by rfl⟩) R108341
theorem R39523 : Reach 39523 := rs (se 1 (by rfl) ⟨29642, by rfl⟩) R59285
theorem R72323 : Reach 72323 := rs (se 1 (by rfl) ⟨54242, by rfl⟩) R108485
theorem R39571 : Reach 39571 := rs (se 1 (by rfl) ⟨29678, by rfl⟩) R59357
theorem R137933 : Reach 137933 := rs (se 3 (by rfl) ⟨25862, by rfl⟩) R51725
theorem R39667 : Reach 39667 := rs (se 1 (by rfl) ⟨29750, by rfl⟩) R59501
theorem R203597 : Reach 203597 := rs (se 3 (by rfl) ⟨38174, by rfl⟩) R76349
theorem R39811 : Reach 39811 := rs (se 1 (by rfl) ⟨29858, by rfl⟩) R59717
theorem R105421 : Reach 105421 := rs (se 3 (by rfl) ⟨19766, by rfl⟩) R39533
theorem R39955 : Reach 39955 := rs (se 1 (by rfl) ⟨29966, by rfl⟩) R59933
theorem R269411 : Reach 269411 := rs (se 1 (by rfl) ⟨202058, by rfl⟩) R404117
theorem R40099 : Reach 40099 := rs (se 1 (by rfl) ⟨30074, by rfl⟩) R60149
theorem R40243 : Reach 40243 := rs (se 1 (by rfl) ⟨30182, by rfl⟩) R60365
theorem R40387 : Reach 40387 := rs (se 1 (by rfl) ⟨30290, by rfl⟩) R60581
theorem R73219 : Reach 73219 := rs (se 1 (by rfl) ⟨54914, by rfl⟩) R109829
theorem R400949 : Reach 400949 := rs (se 5 (by rfl) ⟨18794, by rfl⟩) R37589
theorem R40531 : Reach 40531 := rs (se 1 (by rfl) ⟨30398, by rfl⟩) R60797
theorem R73379 : Reach 73379 := rs (se 1 (by rfl) ⟨55034, by rfl⟩) R110069
theorem R40675 : Reach 40675 := rs (se 1 (by rfl) ⟨30506, by rfl⟩) R61013
theorem R204643 : Reach 204643 := rs (se 1 (by rfl) ⟨153482, by rfl⟩) R306965
theorem R40819 : Reach 40819 := rs (se 1 (by rfl) ⟨30614, by rfl⟩) R61229
theorem R40963 : Reach 40963 := rs (se 1 (by rfl) ⟨30722, by rfl⟩) R61445
theorem R303173 : Reach 303173 := rs (se 4 (by rfl) ⟨28422, by rfl⟩) R56845
theorem R41107 : Reach 41107 := rs (se 1 (by rfl) ⟨30830, by rfl⟩) R61661
theorem R41251 : Reach 41251 := rs (se 1 (by rfl) ⟨30938, by rfl⟩) R61877
theorem R205091 : Reach 205091 := rs (se 1 (by rfl) ⟨153818, by rfl⟩) R307637
theorem R139619 : Reach 139619 := rs (se 1 (by rfl) ⟨104714, by rfl⟩) R209429
theorem R41395 : Reach 41395 := rs (se 1 (by rfl) ⟨31046, by rfl⟩) R62093
theorem R41539 : Reach 41539 := rs (se 1 (by rfl) ⟨31154, by rfl⟩) R62309
theorem R107153 : Reach 107153 := rs (se 2 (by rfl) ⟨40182, by rfl⟩) R80365
theorem R41683 : Reach 41683 := rs (se 1 (by rfl) ⟨31262, by rfl⟩) R62525
theorem R336611 : Reach 336611 := rs (se 1 (by rfl) ⟨252458, by rfl⟩) R504917
theorem R303857 : Reach 303857 := rs (se 2 (by rfl) ⟨113946, by rfl⟩) R227893
theorem R107345 : Reach 107345 := rs (se 2 (by rfl) ⟨40254, by rfl⟩) R80509
theorem R41827 : Reach 41827 := rs (se 1 (by rfl) ⟨31370, by rfl⟩) R62741
theorem R369521 : Reach 369521 := rs (se 2 (by rfl) ⟨138570, by rfl⟩) R277141
theorem R41971 : Reach 41971 := rs (se 1 (by rfl) ⟨31478, by rfl⟩) R62957
theorem R140401 : Reach 140401 := rs (se 2 (by rfl) ⟨52650, by rfl⟩) R105301
theorem R42115 : Reach 42115 := rs (se 1 (by rfl) ⟨31586, by rfl⟩) R63173
theorem R42211 : Reach 42211 := rs (se 1 (by rfl) ⟨31658, by rfl⟩) R63317
theorem R42259 : Reach 42259 := rs (se 1 (by rfl) ⟨31694, by rfl⟩) R63389
theorem R42403 : Reach 42403 := rs (se 1 (by rfl) ⟨31802, by rfl⟩) R63605
theorem R140849 : Reach 140849 := rs (se 2 (by rfl) ⟨52818, by rfl⟩) R105637
theorem R42547 : Reach 42547 := rs (se 1 (by rfl) ⟨31910, by rfl⟩) R63821
theorem R173645 : Reach 173645 := rs (se 3 (by rfl) ⟨32558, by rfl⟩) R65117
theorem R42691 : Reach 42691 := rs (se 1 (by rfl) ⟨32018, by rfl⟩) R64037
theorem R108337 : Reach 108337 := rs (se 2 (by rfl) ⟨40626, by rfl⟩) R81253
theorem R42835 : Reach 42835 := rs (se 1 (by rfl) ⟨32126, by rfl⟩) R64253
theorem R42979 : Reach 42979 := rs (se 1 (by rfl) ⟨32234, by rfl⟩) R64469
theorem R75811 : Reach 75811 := rs (se 1 (by rfl) ⟨56858, by rfl⟩) R113717
theorem R108611 : Reach 108611 := rs (se 1 (by rfl) ⟨81458, by rfl⟩) R162917
theorem R43123 : Reach 43123 := rs (se 1 (by rfl) ⟨32342, by rfl⟩) R64685
theorem R108803 : Reach 108803 := rs (se 1 (by rfl) ⟨81602, by rfl⟩) R163205
theorem R43267 : Reach 43267 := rs (se 1 (by rfl) ⟨32450, by rfl⟩) R64901
theorem R76067 : Reach 76067 := rs (se 1 (by rfl) ⟨57050, by rfl⟩) R114101
theorem R43411 : Reach 43411 := rs (se 1 (by rfl) ⟨32558, by rfl⟩) R65117
theorem R76259 : Reach 76259 := rs (se 1 (by rfl) ⟨57194, by rfl⟩) R114389
theorem R469475 : Reach 469475 := rs (se 1 (by rfl) ⟨352106, by rfl⟩) R704213
theorem R76291 : Reach 76291 := rs (se 1 (by rfl) ⟨57218, by rfl⟩) R114437
theorem R43555 : Reach 43555 := rs (se 1 (by rfl) ⟨32666, by rfl⟩) R65333
theorem R404021 : Reach 404021 := rs (se 5 (by rfl) ⟨18938, by rfl⟩) R37877
theorem R43699 : Reach 43699 := rs (se 1 (by rfl) ⟨32774, by rfl⟩) R65549
theorem R207629 : Reach 207629 := rs (se 3 (by rfl) ⟨38930, by rfl⟩) R77861
theorem R43843 : Reach 43843 := rs (se 1 (by rfl) ⟨32882, by rfl⟩) R65765
theorem R43987 : Reach 43987 := rs (se 1 (by rfl) ⟨32990, by rfl⟩) R65981
theorem R142307 : Reach 142307 := rs (se 1 (by rfl) ⟨106730, by rfl⟩) R213461
theorem R109613 : Reach 109613 := rs (se 3 (by rfl) ⟨20552, by rfl⟩) R41105
theorem R109667 : Reach 109667 := rs (se 1 (by rfl) ⟨82250, by rfl⟩) R164501
theorem R109795 : Reach 109795 := rs (se 1 (by rfl) ⟨82346, by rfl⟩) R164693
theorem R77041 : Reach 77041 := rs (se 2 (by rfl) ⟨28890, by rfl⟩) R57781
theorem R240965 : Reach 240965 := rs (se 4 (by rfl) ⟨22590, by rfl⟩) R45181
theorem R110083 : Reach 110083 := rs (se 1 (by rfl) ⟨82562, by rfl⟩) R165125
theorem R667277 : Reach 667277 := rs (se 3 (by rfl) ⟨125114, by rfl⟩) R250229
theorem R44707 : Reach 44707 := rs (se 1 (by rfl) ⟨33530, by rfl⟩) R67061
theorem R110285 : Reach 110285 := rs (se 3 (by rfl) ⟨20678, by rfl⟩) R41357
theorem R44803 : Reach 44803 := rs (se 1 (by rfl) ⟨33602, by rfl⟩) R67205
theorem R77699 : Reach 77699 := rs (se 1 (by rfl) ⟨58274, by rfl⟩) R116549
theorem R143309 : Reach 143309 := rs (se 3 (by rfl) ⟨26870, by rfl⟩) R53741
theorem R110659 : Reach 110659 := rs (se 1 (by rfl) ⟨82994, by rfl⟩) R165989
theorem R45299 : Reach 45299 := rs (se 1 (by rfl) ⟨33974, by rfl⟩) R67949
theorem R78545 : Reach 78545 := rs (se 2 (by rfl) ⟨29454, by rfl⟩) R58909
theorem R46003 : Reach 46003 := rs (se 1 (by rfl) ⟨34502, by rfl⟩) R69005
theorem R209861 : Reach 209861 := rs (se 4 (by rfl) ⟨19674, by rfl⟩) R39349
theorem R209891 : Reach 209891 := rs (se 1 (by rfl) ⟨157418, by rfl⟩) R314837
theorem R46099 : Reach 46099 := rs (se 1 (by rfl) ⟨34574, by rfl⟩) R69149
theorem R79217 : Reach 79217 := rs (se 2 (by rfl) ⟨29706, by rfl⟩) R59413
theorem R79235 : Reach 79235 := rs (se 1 (by rfl) ⟨59426, by rfl⟩) R118853
theorem R46595 : Reach 46595 := rs (se 1 (by rfl) ⟨34946, by rfl⟩) R69893
theorem R210545 : Reach 210545 := rs (se 2 (by rfl) ⟨78954, by rfl⟩) R157909
theorem R79505 : Reach 79505 := rs (se 2 (by rfl) ⟨29814, by rfl⟩) R59629
theorem R79523 : Reach 79523 := rs (se 1 (by rfl) ⟨59642, by rfl⟩) R119285
theorem R308933 : Reach 308933 := rs (se 4 (by rfl) ⟨28962, by rfl⟩) R57925
theorem R79793 : Reach 79793 := rs (se 2 (by rfl) ⟨29922, by rfl⟩) R59845
theorem R79811 : Reach 79811 := rs (se 1 (by rfl) ⟨59858, by rfl⟩) R119717
theorem R112589 : Reach 112589 := rs (se 3 (by rfl) ⟨21110, by rfl⟩) R42221
theorem R538595 : Reach 538595 := rs (se 1 (by rfl) ⟨403946, by rfl⟩) R807893
theorem R145421 : Reach 145421 := rs (se 3 (by rfl) ⟨27266, by rfl⟩) R54533
theorem R47137 : Reach 47137 := rs (se 2 (by rfl) ⟨17676, by rfl⟩) R35353
theorem R47233 : Reach 47233 := rs (se 2 (by rfl) ⟨17712, by rfl⟩) R35425
theorem R47299 : Reach 47299 := rs (se 1 (by rfl) ⟨35474, by rfl⟩) R70949
theorem R80081 : Reach 80081 := rs (se 2 (by rfl) ⟨30030, by rfl⟩) R60061
theorem R80099 : Reach 80099 := rs (se 1 (by rfl) ⟨60074, by rfl⟩) R120149
theorem R47395 : Reach 47395 := rs (se 1 (by rfl) ⟨35546, by rfl⟩) R71093
theorem R80369 : Reach 80369 := rs (se 2 (by rfl) ⟨30138, by rfl⟩) R60277
theorem R80387 : Reach 80387 := rs (se 1 (by rfl) ⟨60290, by rfl⟩) R120581
theorem R47729 : Reach 47729 := rs (se 2 (by rfl) ⟨17898, by rfl⟩) R35797
theorem R80657 : Reach 80657 := rs (se 2 (by rfl) ⟨30246, by rfl⟩) R60493
theorem R47891 : Reach 47891 := rs (se 1 (by rfl) ⟨35918, by rfl⟩) R71837
theorem R80675 : Reach 80675 := rs (se 1 (by rfl) ⟨60506, by rfl⟩) R121013
theorem R146225 : Reach 146225 := rs (se 2 (by rfl) ⟨54834, by rfl⟩) R109669
theorem R244579 : Reach 244579 := rs (se 1 (by rfl) ⟨183434, by rfl⟩) R366869
theorem R179171 : Reach 179171 := rs (se 1 (by rfl) ⟨134378, by rfl⟩) R268757
theorem R212003 : Reach 212003 := rs (se 1 (by rfl) ⟨159002, by rfl⟩) R318005
theorem R80945 : Reach 80945 := rs (se 2 (by rfl) ⟨30354, by rfl⟩) R60709
theorem R80963 : Reach 80963 := rs (se 1 (by rfl) ⟨60722, by rfl⟩) R121445
theorem R48433 : Reach 48433 := rs (se 2 (by rfl) ⟨18162, by rfl⟩) R36325
theorem R113987 : Reach 113987 := rs (se 1 (by rfl) ⟨85490, by rfl⟩) R170981
theorem R81233 : Reach 81233 := rs (se 2 (by rfl) ⟨30462, by rfl⟩) R60925
theorem R81251 : Reach 81251 := rs (se 1 (by rfl) ⟨60938, by rfl⟩) R121877
theorem R48529 : Reach 48529 := rs (se 2 (by rfl) ⟨18198, by rfl⟩) R36397
theorem R81329 : Reach 81329 := rs (se 2 (by rfl) ⟨30498, by rfl⟩) R60997
theorem R146893 : Reach 146893 := rs (se 3 (by rfl) ⟨27542, by rfl⟩) R55085
theorem R48595 : Reach 48595 := rs (se 1 (by rfl) ⟨36446, by rfl⟩) R72893
theorem R48643 : Reach 48643 := rs (se 1 (by rfl) ⟨36482, by rfl⟩) R72965
theorem R48691 : Reach 48691 := rs (se 1 (by rfl) ⟨36518, by rfl⟩) R73037
theorem R81521 : Reach 81521 := rs (se 2 (by rfl) ⟨30570, by rfl⟩) R61141
theorem R81539 : Reach 81539 := rs (se 1 (by rfl) ⟨61154, by rfl⟩) R122309
theorem R179981 : Reach 179981 := rs (se 3 (by rfl) ⟨33746, by rfl⟩) R67493
theorem R376589 : Reach 376589 := rs (se 3 (by rfl) ⟨70610, by rfl⟩) R141221
theorem R49025 : Reach 49025 := rs (se 2 (by rfl) ⟨18384, by rfl⟩) R36769
theorem R81809 : Reach 81809 := rs (se 2 (by rfl) ⟨30678, by rfl⟩) R61357
theorem R81827 : Reach 81827 := rs (se 1 (by rfl) ⟨61370, by rfl⟩) R122741
theorem R114659 : Reach 114659 := rs (se 1 (by rfl) ⟨85994, by rfl⟩) R171989
theorem R49187 : Reach 49187 := rs (se 1 (by rfl) ⟨36890, by rfl⟩) R73781
theorem R82097 : Reach 82097 := rs (se 2 (by rfl) ⟨30786, by rfl⟩) R61573
theorem R82115 : Reach 82115 := rs (se 1 (by rfl) ⟨61586, by rfl⟩) R123173
theorem R147683 : Reach 147683 := rs (se 1 (by rfl) ⟨110762, by rfl⟩) R221525
theorem R115021 : Reach 115021 := rs (se 3 (by rfl) ⟨21566, by rfl⟩) R43133
theorem R147811 : Reach 147811 := rs (se 1 (by rfl) ⟨110858, by rfl⟩) R221717
theorem R82289 : Reach 82289 := rs (se 2 (by rfl) ⟨30858, by rfl⟩) R61717
theorem R115121 : Reach 115121 := rs (se 2 (by rfl) ⟨43170, by rfl⟩) R86341
theorem R82385 : Reach 82385 := rs (se 2 (by rfl) ⟨30894, by rfl⟩) R61789
theorem R82403 : Reach 82403 := rs (se 1 (by rfl) ⟨61802, by rfl⟩) R123605
theorem R311921 : Reach 311921 := rs (se 2 (by rfl) ⟨116970, by rfl⟩) R233941
theorem R82673 : Reach 82673 := rs (se 2 (by rfl) ⟨31002, by rfl⟩) R62005
theorem R82691 : Reach 82691 := rs (se 1 (by rfl) ⟨62018, by rfl⟩) R124037
theorem R836405 : Reach 836405 := rs (se 5 (by rfl) ⟨39206, by rfl⟩) R78413
theorem R148337 : Reach 148337 := rs (se 2 (by rfl) ⟨55626, by rfl⟩) R111253
theorem R82961 : Reach 82961 := rs (se 2 (by rfl) ⟨31110, by rfl⟩) R62221
theorem R82979 : Reach 82979 := rs (se 1 (by rfl) ⟨62234, by rfl⟩) R124469
theorem R115793 : Reach 115793 := rs (se 2 (by rfl) ⟨43422, by rfl⟩) R86845
theorem R115843 : Reach 115843 := rs (se 1 (by rfl) ⟨86882, by rfl⟩) R173765
theorem R181453 : Reach 181453 := rs (se 3 (by rfl) ⟨34022, by rfl⟩) R68045
theorem R83249 : Reach 83249 := rs (se 2 (by rfl) ⟨31218, by rfl⟩) R62437
theorem R83267 : Reach 83267 := rs (se 1 (by rfl) ⟨62450, by rfl⟩) R124901
theorem R476725 : Reach 476725 := rs (se 5 (by rfl) ⟨22346, by rfl⟩) R44693
theorem R247373 : Reach 247373 := rs (se 3 (by rfl) ⟨46382, by rfl⟩) R92765
theorem R83537 : Reach 83537 := rs (se 2 (by rfl) ⟨31326, by rfl⟩) R62653
theorem R83555 : Reach 83555 := rs (se 1 (by rfl) ⟨62666, by rfl⟩) R125333
theorem R476869 : Reach 476869 := rs (se 4 (by rfl) ⟨44706, by rfl⟩) R89413
theorem R51025 : Reach 51025 := rs (se 2 (by rfl) ⟨19134, by rfl⟩) R38269
theorem R116561 : Reach 116561 := rs (se 2 (by rfl) ⟨43710, by rfl⟩) R87421
theorem R83825 : Reach 83825 := rs (se 2 (by rfl) ⟨31434, by rfl⟩) R62869
theorem R83843 : Reach 83843 := rs (se 1 (by rfl) ⟨62882, by rfl⟩) R125765
theorem R51121 : Reach 51121 := rs (se 2 (by rfl) ⟨19170, by rfl⟩) R38341
theorem R84113 : Reach 84113 := rs (se 2 (by rfl) ⟨31542, by rfl⟩) R63085
theorem R84131 : Reach 84131 := rs (se 1 (by rfl) ⟨63098, by rfl⟩) R126197
theorem R215237 : Reach 215237 := rs (se 4 (by rfl) ⟨20178, by rfl⟩) R40357
theorem R182513 : Reach 182513 := rs (se 2 (by rfl) ⟨68442, by rfl⟩) R136885
theorem R280817 : Reach 280817 := rs (se 2 (by rfl) ⟨105306, by rfl⟩) R210613
theorem R51521 : Reach 51521 := rs (se 2 (by rfl) ⟨19320, by rfl⟩) R38641
theorem R248141 : Reach 248141 := rs (se 3 (by rfl) ⟨46526, by rfl⟩) R93053
theorem R117073 : Reach 117073 := rs (se 2 (by rfl) ⟨43902, by rfl⟩) R87805
theorem R51553 : Reach 51553 := rs (se 2 (by rfl) ⟨19332, by rfl⟩) R38665
theorem R51617 : Reach 51617 := rs (se 2 (by rfl) ⟨19356, by rfl⟩) R38713
theorem R51619 : Reach 51619 := rs (se 1 (by rfl) ⟨38714, by rfl⟩) R77429
theorem R84401 : Reach 84401 := rs (se 2 (by rfl) ⟨31650, by rfl⟩) R63301
theorem R51635 : Reach 51635 := rs (se 1 (by rfl) ⟨38726, by rfl⟩) R77453
theorem R84419 : Reach 84419 := rs (se 1 (by rfl) ⟨63314, by rfl⟩) R126629
theorem R182897 : Reach 182897 := rs (se 2 (by rfl) ⟨68586, by rfl⟩) R137173
theorem R215693 : Reach 215693 := rs (se 3 (by rfl) ⟨40442, by rfl⟩) R80885
theorem R84689 : Reach 84689 := rs (se 2 (by rfl) ⟨31758, by rfl⟩) R63517
theorem R84707 : Reach 84707 := rs (se 1 (by rfl) ⟨63530, by rfl⟩) R127061
theorem R52115 : Reach 52115 := rs (se 1 (by rfl) ⟨39086, by rfl⟩) R78173
theorem R478133 : Reach 478133 := rs (se 5 (by rfl) ⟨22412, by rfl⟩) R44825
theorem R412613 : Reach 412613 := rs (se 4 (by rfl) ⟨38682, by rfl⟩) R77365
theorem R84977 : Reach 84977 := rs (se 2 (by rfl) ⟨31866, by rfl⟩) R63733
theorem R84995 : Reach 84995 := rs (se 1 (by rfl) ⟨63746, by rfl⟩) R127493
theorem R314381 : Reach 314381 := rs (se 3 (by rfl) ⟨58946, by rfl⟩) R117893
theorem R52483 : Reach 52483 := rs (se 1 (by rfl) ⟨39362, by rfl⟩) R78725
theorem R85265 : Reach 85265 := rs (se 2 (by rfl) ⟨31974, by rfl⟩) R63949
theorem R85283 : Reach 85283 := rs (se 1 (by rfl) ⟨63962, by rfl⟩) R127925
theorem R52579 : Reach 52579 := rs (se 1 (by rfl) ⟨39434, by rfl⟩) R78869
theorem R118189 : Reach 118189 := rs (se 3 (by rfl) ⟨22160, by rfl⟩) R44321
theorem R249293 : Reach 249293 := rs (se 3 (by rfl) ⟨46742, by rfl⟩) R93485
theorem R52691 : Reach 52691 := rs (se 1 (by rfl) ⟨39518, by rfl⟩) R79037
theorem R118253 : Reach 118253 := rs (se 3 (by rfl) ⟨22172, by rfl⟩) R44345
theorem R52721 : Reach 52721 := rs (se 2 (by rfl) ⟨19770, by rfl⟩) R39541
theorem R52739 : Reach 52739 := rs (se 1 (by rfl) ⟨39554, by rfl⟩) R79109
theorem R52769 : Reach 52769 := rs (se 2 (by rfl) ⟨19788, by rfl⟩) R39577
theorem R85553 : Reach 85553 := rs (se 2 (by rfl) ⟨32082, by rfl⟩) R64165
theorem R52787 : Reach 52787 := rs (se 1 (by rfl) ⟨39590, by rfl⟩) R79181
theorem R85571 : Reach 85571 := rs (se 1 (by rfl) ⟨64178, by rfl⟩) R128357
theorem R52817 : Reach 52817 := rs (se 2 (by rfl) ⟨19806, by rfl⟩) R39613
theorem R52835 : Reach 52835 := rs (se 1 (by rfl) ⟨39626, by rfl⟩) R79253
theorem R52865 : Reach 52865 := rs (se 2 (by rfl) ⟨19824, by rfl⟩) R39649
theorem R118417 : Reach 118417 := rs (se 2 (by rfl) ⟨44406, by rfl⟩) R88813
theorem R52883 : Reach 52883 := rs (se 1 (by rfl) ⟨39662, by rfl⟩) R79325
theorem R52913 : Reach 52913 := rs (se 2 (by rfl) ⟨19842, by rfl⟩) R39685
theorem R52931 : Reach 52931 := rs (se 1 (by rfl) ⟨39698, by rfl⟩) R79397
theorem R52961 : Reach 52961 := rs (se 2 (by rfl) ⟨19860, by rfl⟩) R39721
theorem R52979 : Reach 52979 := rs (se 1 (by rfl) ⟨39734, by rfl⟩) R79469
theorem R53009 : Reach 53009 := rs (se 2 (by rfl) ⟨19878, by rfl⟩) R39757
theorem R53027 : Reach 53027 := rs (se 1 (by rfl) ⟨39770, by rfl⟩) R79541
theorem R53057 : Reach 53057 := rs (se 2 (by rfl) ⟨19896, by rfl⟩) R39793
theorem R85841 : Reach 85841 := rs (se 2 (by rfl) ⟨32190, by rfl⟩) R64381
theorem R53075 : Reach 53075 := rs (se 1 (by rfl) ⟨39806, by rfl⟩) R79613
theorem R85859 : Reach 85859 := rs (se 1 (by rfl) ⟨64394, by rfl⟩) R128789
theorem R118637 : Reach 118637 := rs (se 3 (by rfl) ⟨22244, by rfl⟩) R44489
theorem R53105 : Reach 53105 := rs (se 2 (by rfl) ⟨19914, by rfl⟩) R39829
theorem R53123 : Reach 53123 := rs (se 1 (by rfl) ⟨39842, by rfl⟩) R79685
theorem R53153 : Reach 53153 := rs (se 2 (by rfl) ⟨19932, by rfl⟩) R39865
theorem R118691 : Reach 118691 := rs (se 1 (by rfl) ⟨89018, by rfl⟩) R178037
theorem R53171 : Reach 53171 := rs (se 1 (by rfl) ⟨39878, by rfl⟩) R79757
theorem R249797 : Reach 249797 := rs (se 4 (by rfl) ⟨23418, by rfl⟩) R46837
theorem R53201 : Reach 53201 := rs (se 2 (by rfl) ⟨19950, by rfl⟩) R39901
theorem R53219 : Reach 53219 := rs (se 1 (by rfl) ⟨39914, by rfl⟩) R79829
theorem R53249 : Reach 53249 := rs (se 2 (by rfl) ⟨19968, by rfl⟩) R39937
theorem R53267 : Reach 53267 := rs (se 1 (by rfl) ⟨39950, by rfl⟩) R79901
theorem R184355 : Reach 184355 := rs (se 1 (by rfl) ⟨138266, by rfl⟩) R276533
theorem R53297 : Reach 53297 := rs (se 2 (by rfl) ⟨19986, by rfl⟩) R39973
theorem R53315 : Reach 53315 := rs (se 1 (by rfl) ⟨39986, by rfl⟩) R79973
theorem R53345 : Reach 53345 := rs (se 2 (by rfl) ⟨20004, by rfl⟩) R40009
theorem R86129 : Reach 86129 := rs (se 2 (by rfl) ⟨32298, by rfl⟩) R64597
theorem R53363 : Reach 53363 := rs (se 1 (by rfl) ⟨40022, by rfl⟩) R80045
theorem R86147 : Reach 86147 := rs (se 1 (by rfl) ⟨64610, by rfl⟩) R129221
theorem R53393 : Reach 53393 := rs (se 2 (by rfl) ⟨20022, by rfl⟩) R40045
theorem R53411 : Reach 53411 := rs (se 1 (by rfl) ⟨40058, by rfl⟩) R80117
theorem R118961 : Reach 118961 := rs (se 2 (by rfl) ⟨44610, by rfl⟩) R89221
theorem R53441 : Reach 53441 := rs (se 2 (by rfl) ⟨20040, by rfl⟩) R40081
theorem R53459 : Reach 53459 := rs (se 1 (by rfl) ⟨40094, by rfl⟩) R80189
theorem R282851 : Reach 282851 := rs (se 1 (by rfl) ⟨212138, by rfl⟩) R424277
theorem R151793 : Reach 151793 := rs (se 2 (by rfl) ⟨56922, by rfl⟩) R113845
theorem R53489 : Reach 53489 := rs (se 2 (by rfl) ⟨20058, by rfl⟩) R40117
theorem R53507 : Reach 53507 := rs (se 1 (by rfl) ⟨40130, by rfl⟩) R80261
theorem R53537 : Reach 53537 := rs (se 2 (by rfl) ⟨20076, by rfl⟩) R40153
theorem R53555 : Reach 53555 := rs (se 1 (by rfl) ⟨40166, by rfl⟩) R80333
theorem R53585 : Reach 53585 := rs (se 2 (by rfl) ⟨20094, by rfl⟩) R40189
theorem R53603 : Reach 53603 := rs (se 1 (by rfl) ⟨40202, by rfl⟩) R80405
theorem R53633 : Reach 53633 := rs (se 2 (by rfl) ⟨20112, by rfl⟩) R40225
theorem R86417 : Reach 86417 := rs (se 2 (by rfl) ⟨32406, by rfl⟩) R64813
theorem R53651 : Reach 53651 := rs (se 1 (by rfl) ⟨40238, by rfl⟩) R80477
theorem R86435 : Reach 86435 := rs (se 1 (by rfl) ⟨64826, by rfl⟩) R129653
theorem R53681 : Reach 53681 := rs (se 2 (by rfl) ⟨20130, by rfl⟩) R40261
theorem R53699 : Reach 53699 := rs (se 1 (by rfl) ⟨40274, by rfl⟩) R80549
theorem R53713 : Reach 53713 := rs (se 2 (by rfl) ⟨20142, by rfl⟩) R40285
theorem R53729 : Reach 53729 := rs (se 2 (by rfl) ⟨20148, by rfl⟩) R40297
theorem R53747 : Reach 53747 := rs (se 1 (by rfl) ⟨40310, by rfl⟩) R80621
theorem R53777 : Reach 53777 := rs (se 2 (by rfl) ⟨20166, by rfl⟩) R40333
theorem R53795 : Reach 53795 := rs (se 1 (by rfl) ⟨40346, by rfl⟩) R80693
theorem R53825 : Reach 53825 := rs (se 2 (by rfl) ⟨20184, by rfl⟩) R40369
theorem R53843 : Reach 53843 := rs (se 1 (by rfl) ⟨40382, by rfl⟩) R80765
theorem R53873 : Reach 53873 := rs (se 2 (by rfl) ⟨20202, by rfl⟩) R40405
theorem R53891 : Reach 53891 := rs (se 1 (by rfl) ⟨40418, by rfl⟩) R80837
theorem R53921 : Reach 53921 := rs (se 2 (by rfl) ⟨20220, by rfl⟩) R40441
theorem R86705 : Reach 86705 := rs (se 2 (by rfl) ⟨32514, by rfl⟩) R65029
theorem R53939 : Reach 53939 := rs (se 1 (by rfl) ⟨40454, by rfl⟩) R80909
theorem R86723 : Reach 86723 := rs (se 1 (by rfl) ⟨65042, by rfl⟩) R130085
theorem R119501 : Reach 119501 := rs (se 3 (by rfl) ⟨22406, by rfl⟩) R44813
theorem R53969 : Reach 53969 := rs (se 2 (by rfl) ⟨20238, by rfl⟩) R40477
theorem R53987 : Reach 53987 := rs (se 1 (by rfl) ⟨40490, by rfl⟩) R80981
theorem R54017 : Reach 54017 := rs (se 2 (by rfl) ⟨20256, by rfl⟩) R40513
theorem R119555 : Reach 119555 := rs (se 1 (by rfl) ⟨89666, by rfl⟩) R179333
theorem R54035 : Reach 54035 := rs (se 1 (by rfl) ⟨40526, by rfl⟩) R81053
theorem R54049 : Reach 54049 := rs (se 2 (by rfl) ⟨20268, by rfl⟩) R40537
theorem R54065 : Reach 54065 := rs (se 2 (by rfl) ⟨20274, by rfl⟩) R40549
theorem R54083 : Reach 54083 := rs (se 1 (by rfl) ⟨40562, by rfl⟩) R81125
theorem R185165 : Reach 185165 := rs (se 3 (by rfl) ⟨34718, by rfl⟩) R69437
theorem R54113 : Reach 54113 := rs (se 2 (by rfl) ⟨20292, by rfl⟩) R40585
theorem R54131 : Reach 54131 := rs (se 1 (by rfl) ⟨40598, by rfl⟩) R81197
theorem R54161 : Reach 54161 := rs (se 2 (by rfl) ⟨20310, by rfl⟩) R40621
theorem R54179 : Reach 54179 := rs (se 1 (by rfl) ⟨40634, by rfl⟩) R81269
theorem R54209 : Reach 54209 := rs (se 2 (by rfl) ⟨20328, by rfl⟩) R40657
theorem R86993 : Reach 86993 := rs (se 2 (by rfl) ⟨32622, by rfl⟩) R65245
theorem R54227 : Reach 54227 := rs (se 1 (by rfl) ⟨40670, by rfl⟩) R81341
theorem R87011 : Reach 87011 := rs (se 1 (by rfl) ⟨65258, by rfl⟩) R130517
theorem R54257 : Reach 54257 := rs (se 2 (by rfl) ⟨20346, by rfl⟩) R40693
theorem R54275 : Reach 54275 := rs (se 1 (by rfl) ⟨40706, by rfl⟩) R81413
theorem R119825 : Reach 119825 := rs (se 2 (by rfl) ⟨44934, by rfl⟩) R89869
theorem R54305 : Reach 54305 := rs (se 2 (by rfl) ⟨20364, by rfl⟩) R40729
theorem R54323 : Reach 54323 := rs (se 1 (by rfl) ⟨40742, by rfl⟩) R81485
theorem R54353 : Reach 54353 := rs (se 2 (by rfl) ⟨20382, by rfl⟩) R40765
theorem R54371 : Reach 54371 := rs (se 1 (by rfl) ⟨40778, by rfl⟩) R81557
theorem R54401 : Reach 54401 := rs (se 2 (by rfl) ⟨20400, by rfl⟩) R40801
theorem R54419 : Reach 54419 := rs (se 1 (by rfl) ⟨40814, by rfl⟩) R81629
theorem R54449 : Reach 54449 := rs (se 2 (by rfl) ⟨20418, by rfl⟩) R40837
theorem R54467 : Reach 54467 := rs (se 1 (by rfl) ⟨40850, by rfl⟩) R81701
theorem R54497 : Reach 54497 := rs (se 2 (by rfl) ⟨20436, by rfl⟩) R40873
theorem R120035 : Reach 120035 := rs (se 1 (by rfl) ⟨90026, by rfl⟩) R180053
theorem R87281 : Reach 87281 := rs (se 2 (by rfl) ⟨32730, by rfl⟩) R65461
theorem R54515 : Reach 54515 := rs (se 1 (by rfl) ⟨40886, by rfl⟩) R81773
theorem R87299 : Reach 87299 := rs (se 1 (by rfl) ⟨65474, by rfl⟩) R130949
theorem R54545 : Reach 54545 := rs (se 2 (by rfl) ⟨20454, by rfl⟩) R40909
theorem R54563 : Reach 54563 := rs (se 1 (by rfl) ⟨40922, by rfl⟩) R81845
theorem R54593 : Reach 54593 := rs (se 2 (by rfl) ⟨20472, by rfl⟩) R40945
theorem R54611 : Reach 54611 := rs (se 1 (by rfl) ⟨40958, by rfl⟩) R81917
theorem R54641 : Reach 54641 := rs (se 2 (by rfl) ⟨20490, by rfl⟩) R40981
theorem R54659 : Reach 54659 := rs (se 1 (by rfl) ⟨40994, by rfl⟩) R81989
theorem R54689 : Reach 54689 := rs (se 2 (by rfl) ⟨20508, by rfl⟩) R41017
theorem R87473 : Reach 87473 := rs (se 2 (by rfl) ⟨32802, by rfl⟩) R65605
theorem R54707 : Reach 54707 := rs (se 1 (by rfl) ⟨41030, by rfl⟩) R82061
theorem R54737 : Reach 54737 := rs (se 2 (by rfl) ⟨20526, by rfl⟩) R41053
theorem R54755 : Reach 54755 := rs (se 1 (by rfl) ⟨41066, by rfl⟩) R82133
theorem R218609 : Reach 218609 := rs (se 2 (by rfl) ⟨81978, by rfl⟩) R163957
theorem R54785 : Reach 54785 := rs (se 2 (by rfl) ⟨20544, by rfl⟩) R41089
theorem R87569 : Reach 87569 := rs (se 2 (by rfl) ⟨32838, by rfl⟩) R65677
theorem R54803 : Reach 54803 := rs (se 1 (by rfl) ⟨41102, by rfl⟩) R82205
theorem R218659 : Reach 218659 := rs (se 1 (by rfl) ⟨163994, by rfl⟩) R327989
theorem R87587 : Reach 87587 := rs (se 1 (by rfl) ⟨65690, by rfl⟩) R131381
theorem R120365 : Reach 120365 := rs (se 3 (by rfl) ⟨22568, by rfl⟩) R45137
theorem R54833 : Reach 54833 := rs (se 2 (by rfl) ⟨20562, by rfl⟩) R41125
theorem R54851 : Reach 54851 := rs (se 1 (by rfl) ⟨41138, by rfl⟩) R82277
theorem R54881 : Reach 54881 := rs (se 2 (by rfl) ⟨20580, by rfl⟩) R41161
theorem R120419 : Reach 120419 := rs (se 1 (by rfl) ⟨90314, by rfl⟩) R180629
theorem R54883 : Reach 54883 := rs (se 1 (by rfl) ⟨41162, by rfl⟩) R82325
theorem R54899 : Reach 54899 := rs (se 1 (by rfl) ⟨41174, by rfl⟩) R82349
theorem R54929 : Reach 54929 := rs (se 2 (by rfl) ⟨20598, by rfl⟩) R41197
theorem R54947 : Reach 54947 := rs (se 1 (by rfl) ⟨41210, by rfl⟩) R82421
theorem R54977 : Reach 54977 := rs (se 2 (by rfl) ⟨20616, by rfl⟩) R41233
theorem R54995 : Reach 54995 := rs (se 1 (by rfl) ⟨41246, by rfl⟩) R82493
theorem R55009 : Reach 55009 := rs (se 2 (by rfl) ⟨20628, by rfl⟩) R41257
theorem R55025 : Reach 55025 := rs (se 2 (by rfl) ⟨20634, by rfl⟩) R41269
theorem R55043 : Reach 55043 := rs (se 1 (by rfl) ⟨41282, by rfl⟩) R82565
theorem R55073 : Reach 55073 := rs (se 2 (by rfl) ⟨20652, by rfl⟩) R41305
theorem R87857 : Reach 87857 := rs (se 2 (by rfl) ⟨32946, by rfl⟩) R65893
theorem R55091 : Reach 55091 := rs (se 1 (by rfl) ⟨41318, by rfl⟩) R82637
theorem R87875 : Reach 87875 := rs (se 1 (by rfl) ⟨65906, by rfl⟩) R131813
theorem R55121 : Reach 55121 := rs (se 2 (by rfl) ⟨20670, by rfl⟩) R41341
theorem R55139 : Reach 55139 := rs (se 1 (by rfl) ⟨41354, by rfl⟩) R82709
theorem R120689 : Reach 120689 := rs (se 2 (by rfl) ⟨45258, by rfl⟩) R90517
theorem R55169 : Reach 55169 := rs (se 2 (by rfl) ⟨20688, by rfl⟩) R41377
theorem R55171 : Reach 55171 := rs (se 1 (by rfl) ⟨41378, by rfl⟩) R82757
theorem R153485 : Reach 153485 := rs (se 3 (by rfl) ⟨28778, by rfl⟩) R57557
theorem R55187 : Reach 55187 := rs (se 1 (by rfl) ⟨41390, by rfl⟩) R82781
theorem R55217 : Reach 55217 := rs (se 2 (by rfl) ⟨20706, by rfl⟩) R41413
theorem R55235 : Reach 55235 := rs (se 1 (by rfl) ⟨41426, by rfl⟩) R82853
theorem R120781 : Reach 120781 := rs (se 3 (by rfl) ⟨22646, by rfl⟩) R45293
theorem R55265 : Reach 55265 := rs (se 2 (by rfl) ⟨20724, by rfl⟩) R41449
theorem R55283 : Reach 55283 := rs (se 1 (by rfl) ⟨41462, by rfl⟩) R82925
theorem R55313 : Reach 55313 := rs (se 2 (by rfl) ⟨20742, by rfl⟩) R41485
theorem R55331 : Reach 55331 := rs (se 1 (by rfl) ⟨41498, by rfl⟩) R82997
theorem R55361 : Reach 55361 := rs (se 2 (by rfl) ⟨20760, by rfl⟩) R41521
theorem R55379 : Reach 55379 := rs (se 1 (by rfl) ⟨41534, by rfl⟩) R83069
theorem R55409 : Reach 55409 := rs (se 2 (by rfl) ⟨20778, by rfl⟩) R41557
theorem R55427 : Reach 55427 := rs (se 1 (by rfl) ⟨41570, by rfl⟩) R83141
theorem R55457 : Reach 55457 := rs (se 2 (by rfl) ⟨20796, by rfl⟩) R41593
theorem R186545 : Reach 186545 := rs (se 2 (by rfl) ⟨69954, by rfl⟩) R139909
theorem R55475 : Reach 55475 := rs (se 1 (by rfl) ⟨41606, by rfl⟩) R83213
theorem R55505 : Reach 55505 := rs (se 2 (by rfl) ⟨20814, by rfl⟩) R41629
theorem R55507 : Reach 55507 := rs (se 1 (by rfl) ⟨41630, by rfl⟩) R83261
theorem R55523 : Reach 55523 := rs (se 1 (by rfl) ⟨41642, by rfl⟩) R83285
theorem R55553 : Reach 55553 := rs (se 2 (by rfl) ⟨20832, by rfl⟩) R41665
theorem R55571 : Reach 55571 := rs (se 1 (by rfl) ⟨41678, by rfl⟩) R83357
theorem R55601 : Reach 55601 := rs (se 2 (by rfl) ⟨20850, by rfl⟩) R41701
theorem R55619 : Reach 55619 := rs (se 1 (by rfl) ⟨41714, by rfl⟩) R83429
theorem R55649 : Reach 55649 := rs (se 2 (by rfl) ⟨20868, by rfl⟩) R41737
theorem R55667 : Reach 55667 := rs (se 1 (by rfl) ⟨41750, by rfl⟩) R83501
theorem R121229 : Reach 121229 := rs (se 3 (by rfl) ⟨22730, by rfl⟩) R45461
theorem R55697 : Reach 55697 := rs (se 2 (by rfl) ⟨20886, by rfl⟩) R41773
theorem R55715 : Reach 55715 := rs (se 1 (by rfl) ⟨41786, by rfl⟩) R83573
theorem R55745 : Reach 55745 := rs (se 2 (by rfl) ⟨20904, by rfl⟩) R41809
theorem R121283 : Reach 121283 := rs (se 1 (by rfl) ⟨90962, by rfl⟩) R181925
theorem R55763 : Reach 55763 := rs (se 1 (by rfl) ⟨41822, by rfl⟩) R83645
theorem R55793 : Reach 55793 := rs (se 2 (by rfl) ⟨20922, by rfl⟩) R41845
theorem R55811 : Reach 55811 := rs (se 1 (by rfl) ⟨41858, by rfl⟩) R83717
theorem R55841 : Reach 55841 := rs (se 2 (by rfl) ⟨20940, by rfl⟩) R41881
theorem R55859 : Reach 55859 := rs (se 1 (by rfl) ⟨41894, by rfl⟩) R83789
theorem R55889 : Reach 55889 := rs (se 2 (by rfl) ⟨20958, by rfl⟩) R41917
theorem R55907 : Reach 55907 := rs (se 1 (by rfl) ⟨41930, by rfl⟩) R83861
theorem R55937 : Reach 55937 := rs (se 2 (by rfl) ⟨20976, by rfl⟩) R41953
theorem R55955 : Reach 55955 := rs (se 1 (by rfl) ⟨41966, by rfl⟩) R83933
theorem R55985 : Reach 55985 := rs (se 2 (by rfl) ⟨20994, by rfl⟩) R41989
theorem R56003 : Reach 56003 := rs (se 1 (by rfl) ⟨42002, by rfl⟩) R84005
theorem R121553 : Reach 121553 := rs (se 2 (by rfl) ⟨45582, by rfl⟩) R91165
theorem R56033 : Reach 56033 := rs (se 2 (by rfl) ⟨21012, by rfl⟩) R42025
theorem R56051 : Reach 56051 := rs (se 1 (by rfl) ⟨42038, by rfl⟩) R84077
theorem R56081 : Reach 56081 := rs (se 2 (by rfl) ⟨21030, by rfl⟩) R42061
theorem R56099 : Reach 56099 := rs (se 1 (by rfl) ⟨42074, by rfl⟩) R84149
theorem R56129 : Reach 56129 := rs (se 2 (by rfl) ⟨21048, by rfl⟩) R42097
theorem R56147 : Reach 56147 := rs (se 1 (by rfl) ⟨42110, by rfl⟩) R84221
theorem R56177 : Reach 56177 := rs (se 2 (by rfl) ⟨21066, by rfl⟩) R42133
theorem R56195 : Reach 56195 := rs (se 1 (by rfl) ⟨42146, by rfl⟩) R84293
theorem R56225 : Reach 56225 := rs (se 2 (by rfl) ⟨21084, by rfl⟩) R42169
theorem R220067 : Reach 220067 := rs (se 1 (by rfl) ⟨165050, by rfl⟩) R330101
theorem R89009 : Reach 89009 := rs (se 2 (by rfl) ⟨33378, by rfl⟩) R66757
theorem R56243 : Reach 56243 := rs (se 1 (by rfl) ⟨42182, by rfl⟩) R84365
theorem R56273 : Reach 56273 := rs (se 2 (by rfl) ⟨21102, by rfl⟩) R42205
theorem R89059 : Reach 89059 := rs (se 1 (by rfl) ⟨66794, by rfl⟩) R133589
theorem R56291 : Reach 56291 := rs (se 1 (by rfl) ⟨42218, by rfl⟩) R84437
theorem R56321 : Reach 56321 := rs (se 2 (by rfl) ⟨21120, by rfl⟩) R42241
theorem R56339 : Reach 56339 := rs (se 1 (by rfl) ⟨42254, by rfl⟩) R84509
theorem R56369 : Reach 56369 := rs (se 2 (by rfl) ⟨21138, by rfl⟩) R42277
theorem R56387 : Reach 56387 := rs (se 1 (by rfl) ⟨42290, by rfl⟩) R84581
theorem R56417 : Reach 56417 := rs (se 2 (by rfl) ⟨21156, by rfl⟩) R42313
theorem R89201 : Reach 89201 := rs (se 2 (by rfl) ⟨33450, by rfl⟩) R66901
theorem R56435 : Reach 56435 := rs (se 1 (by rfl) ⟨42326, by rfl⟩) R84653
theorem R56465 : Reach 56465 := rs (se 2 (by rfl) ⟨21174, by rfl⟩) R42349
theorem R56483 : Reach 56483 := rs (se 1 (by rfl) ⟨42362, by rfl⟩) R84725
theorem R56513 : Reach 56513 := rs (se 2 (by rfl) ⟨21192, by rfl⟩) R42385
theorem R56531 : Reach 56531 := rs (se 1 (by rfl) ⟨42398, by rfl⟩) R84797
theorem R122093 : Reach 122093 := rs (se 3 (by rfl) ⟨22892, by rfl⟩) R45785
theorem R56561 : Reach 56561 := rs (se 2 (by rfl) ⟨21210, by rfl⟩) R42421
theorem R56579 : Reach 56579 := rs (se 1 (by rfl) ⟨42434, by rfl⟩) R84869
theorem R56609 : Reach 56609 := rs (se 2 (by rfl) ⟨21228, by rfl⟩) R42457
theorem R122147 : Reach 122147 := rs (se 1 (by rfl) ⟨91610, by rfl⟩) R183221
theorem R56627 : Reach 56627 := rs (se 1 (by rfl) ⟨42470, by rfl⟩) R84941
theorem R56657 : Reach 56657 := rs (se 2 (by rfl) ⟨21246, by rfl⟩) R42493
theorem R56675 : Reach 56675 := rs (se 1 (by rfl) ⟨42506, by rfl⟩) R85013
theorem R56705 : Reach 56705 := rs (se 2 (by rfl) ⟨21264, by rfl⟩) R42529
theorem R56723 : Reach 56723 := rs (se 1 (by rfl) ⟨42542, by rfl⟩) R85085
theorem R56737 : Reach 56737 := rs (se 2 (by rfl) ⟨21276, by rfl⟩) R42553
theorem R56753 : Reach 56753 := rs (se 2 (by rfl) ⟨21282, by rfl⟩) R42565
theorem R56771 : Reach 56771 := rs (se 1 (by rfl) ⟨42578, by rfl⟩) R85157
theorem R253381 : Reach 253381 := rs (se 4 (by rfl) ⟨23754, by rfl⟩) R47509
theorem R56801 : Reach 56801 := rs (se 2 (by rfl) ⟨21300, by rfl⟩) R42601
theorem R56819 : Reach 56819 := rs (se 1 (by rfl) ⟨42614, by rfl⟩) R85229
theorem R56849 : Reach 56849 := rs (se 2 (by rfl) ⟨21318, by rfl⟩) R42637
theorem R56867 : Reach 56867 := rs (se 1 (by rfl) ⟨42650, by rfl⟩) R85301
theorem R122417 : Reach 122417 := rs (se 2 (by rfl) ⟨45906, by rfl⟩) R91813
theorem R56897 : Reach 56897 := rs (se 2 (by rfl) ⟨21336, by rfl⟩) R42673
theorem R56915 : Reach 56915 := rs (se 1 (by rfl) ⟨42686, by rfl⟩) R85373
theorem R56945 : Reach 56945 := rs (se 2 (by rfl) ⟨21354, by rfl⟩) R42709
theorem R56963 : Reach 56963 := rs (se 1 (by rfl) ⟨42722, by rfl⟩) R85445
theorem R220805 : Reach 220805 := rs (se 4 (by rfl) ⟨20700, by rfl⟩) R41401
theorem R56993 : Reach 56993 := rs (se 2 (by rfl) ⟨21372, by rfl⟩) R42745
theorem R188081 : Reach 188081 := rs (se 2 (by rfl) ⟨70530, by rfl⟩) R141061
theorem R57011 : Reach 57011 := rs (se 1 (by rfl) ⟨42758, by rfl⟩) R85517
theorem R57041 : Reach 57041 := rs (se 2 (by rfl) ⟨21390, by rfl⟩) R42781
theorem R57059 : Reach 57059 := rs (se 1 (by rfl) ⟨42794, by rfl⟩) R85589
theorem R57073 : Reach 57073 := rs (se 2 (by rfl) ⟨21402, by rfl⟩) R42805
theorem R122609 : Reach 122609 := rs (se 2 (by rfl) ⟨45978, by rfl⟩) R91957
theorem R57089 : Reach 57089 := rs (se 2 (by rfl) ⟨21408, by rfl⟩) R42817
theorem R89873 : Reach 89873 := rs (se 2 (by rfl) ⟨33702, by rfl⟩) R67405
theorem R57107 : Reach 57107 := rs (se 1 (by rfl) ⟨42830, by rfl⟩) R85661
theorem R57137 : Reach 57137 := rs (se 2 (by rfl) ⟨21426, by rfl⟩) R42853
theorem R57155 : Reach 57155 := rs (se 1 (by rfl) ⟨42866, by rfl⟩) R85733
theorem R57185 : Reach 57185 := rs (se 2 (by rfl) ⟨21444, by rfl⟩) R42889
theorem R57203 : Reach 57203 := rs (se 1 (by rfl) ⟨42902, by rfl⟩) R85805
theorem R221069 : Reach 221069 := rs (se 3 (by rfl) ⟨41450, by rfl⟩) R82901
theorem R57233 : Reach 57233 := rs (se 2 (by rfl) ⟨21462, by rfl⟩) R42925
theorem R57251 : Reach 57251 := rs (se 1 (by rfl) ⟨42938, by rfl⟩) R85877
theorem R57281 : Reach 57281 := rs (se 2 (by rfl) ⟨21480, by rfl⟩) R42961
theorem R57299 : Reach 57299 := rs (se 1 (by rfl) ⟨42974, by rfl⟩) R85949
theorem R57329 : Reach 57329 := rs (se 2 (by rfl) ⟨21498, by rfl⟩) R42997
theorem R57347 : Reach 57347 := rs (se 1 (by rfl) ⟨43010, by rfl⟩) R86021
theorem R57377 : Reach 57377 := rs (se 2 (by rfl) ⟨21516, by rfl⟩) R43033
theorem R57395 : Reach 57395 := rs (se 1 (by rfl) ⟨43046, by rfl⟩) R86093
theorem R122957 : Reach 122957 := rs (se 3 (by rfl) ⟨23054, by rfl⟩) R46109
theorem R90193 : Reach 90193 := rs (se 2 (by rfl) ⟨33822, by rfl⟩) R67645
theorem R57425 : Reach 57425 := rs (se 2 (by rfl) ⟨21534, by rfl⟩) R43069
theorem R57443 : Reach 57443 := rs (se 1 (by rfl) ⟨43082, by rfl⟩) R86165
theorem R57473 : Reach 57473 := rs (se 2 (by rfl) ⟨21552, by rfl⟩) R43105
theorem R123011 : Reach 123011 := rs (se 1 (by rfl) ⟨92258, by rfl⟩) R184517
theorem R57491 : Reach 57491 := rs (se 1 (by rfl) ⟨43118, by rfl⟩) R86237
theorem R57521 : Reach 57521 := rs (se 2 (by rfl) ⟨21570, by rfl⟩) R43141
theorem R57539 : Reach 57539 := rs (se 1 (by rfl) ⟨43154, by rfl⟩) R86309
theorem R57569 : Reach 57569 := rs (se 2 (by rfl) ⟨21588, by rfl⟩) R43177
theorem R483569 : Reach 483569 := rs (se 2 (by rfl) ⟨181338, by rfl⟩) R362677
theorem R57587 : Reach 57587 := rs (se 1 (by rfl) ⟨43190, by rfl⟩) R86381
theorem R57617 : Reach 57617 := rs (se 2 (by rfl) ⟨21606, by rfl⟩) R43213
theorem R57635 : Reach 57635 := rs (se 1 (by rfl) ⟨43226, by rfl⟩) R86453
theorem R57665 : Reach 57665 := rs (se 2 (by rfl) ⟨21624, by rfl⟩) R43249
theorem R57683 : Reach 57683 := rs (se 1 (by rfl) ⟨43262, by rfl⟩) R86525
theorem R90467 : Reach 90467 := rs (se 1 (by rfl) ⟨67850, by rfl⟩) R135701
theorem R57713 : Reach 57713 := rs (se 2 (by rfl) ⟨21642, by rfl⟩) R43285
theorem R57731 : Reach 57731 := rs (se 1 (by rfl) ⟨43298, by rfl⟩) R86597
theorem R123281 : Reach 123281 := rs (se 2 (by rfl) ⟨46230, by rfl⟩) R92461
theorem R57761 : Reach 57761 := rs (se 2 (by rfl) ⟨21660, by rfl⟩) R43321
theorem R57779 : Reach 57779 := rs (se 1 (by rfl) ⟨43334, by rfl⟩) R86669
theorem R90563 : Reach 90563 := rs (se 1 (by rfl) ⟨67922, by rfl⟩) R135845
theorem R57809 : Reach 57809 := rs (se 2 (by rfl) ⟨21678, by rfl⟩) R43357
theorem R57827 : Reach 57827 := rs (se 1 (by rfl) ⟨43370, by rfl⟩) R86741
theorem R57857 : Reach 57857 := rs (se 2 (by rfl) ⟨21696, by rfl⟩) R43393
theorem R57875 : Reach 57875 := rs (se 1 (by rfl) ⟨43406, by rfl⟩) R86813
theorem R90659 : Reach 90659 := rs (se 1 (by rfl) ⟨67994, by rfl⟩) R135989
theorem R57905 : Reach 57905 := rs (se 2 (by rfl) ⟨21714, by rfl⟩) R43429
theorem R57923 : Reach 57923 := rs (se 1 (by rfl) ⟨43442, by rfl⟩) R86885
theorem R57953 : Reach 57953 := rs (se 2 (by rfl) ⟨21732, by rfl⟩) R43465
theorem R57971 : Reach 57971 := rs (se 1 (by rfl) ⟨43478, by rfl⟩) R86957
theorem R418445 : Reach 418445 := rs (se 3 (by rfl) ⟨78458, by rfl⟩) R156917
theorem R58001 : Reach 58001 := rs (se 2 (by rfl) ⟨21750, by rfl⟩) R43501
theorem R58019 : Reach 58019 := rs (se 1 (by rfl) ⟨43514, by rfl⟩) R87029
theorem R58049 : Reach 58049 := rs (se 2 (by rfl) ⟨21768, by rfl⟩) R43537
theorem R58067 : Reach 58067 := rs (se 1 (by rfl) ⟨43550, by rfl⟩) R87101
theorem R58097 : Reach 58097 := rs (se 2 (by rfl) ⟨21786, by rfl⟩) R43573
theorem R58115 : Reach 58115 := rs (se 1 (by rfl) ⟨43586, by rfl⟩) R87173
theorem R58145 : Reach 58145 := rs (se 2 (by rfl) ⟨21804, by rfl⟩) R43609
theorem R58163 : Reach 58163 := rs (se 1 (by rfl) ⟨43622, by rfl⟩) R87245
theorem R58193 : Reach 58193 := rs (se 2 (by rfl) ⟨21822, by rfl⟩) R43645
theorem R58211 : Reach 58211 := rs (se 1 (by rfl) ⟨43658, by rfl⟩) R87317
theorem R58241 : Reach 58241 := rs (se 2 (by rfl) ⟨21840, by rfl⟩) R43681
theorem R58259 : Reach 58259 := rs (se 1 (by rfl) ⟨43694, by rfl⟩) R87389
theorem R123821 : Reach 123821 := rs (se 3 (by rfl) ⟨23216, by rfl⟩) R46433
theorem R58289 : Reach 58289 := rs (se 2 (by rfl) ⟨21858, by rfl⟩) R43717
theorem R58307 : Reach 58307 := rs (se 1 (by rfl) ⟨43730, by rfl⟩) R87461
theorem R58337 : Reach 58337 := rs (se 2 (by rfl) ⟨21876, by rfl⟩) R43753
theorem R123875 : Reach 123875 := rs (se 1 (by rfl) ⟨92906, by rfl⟩) R185813
theorem R58355 : Reach 58355 := rs (se 1 (by rfl) ⟨43766, by rfl⟩) R87533
theorem R58385 : Reach 58385 := rs (se 2 (by rfl) ⟨21894, by rfl⟩) R43789
theorem R58403 : Reach 58403 := rs (se 1 (by rfl) ⟨43802, by rfl⟩) R87605
theorem R58433 : Reach 58433 := rs (se 2 (by rfl) ⟨21912, by rfl⟩) R43825
theorem R58451 : Reach 58451 := rs (se 1 (by rfl) ⟨43838, by rfl⟩) R87677
theorem R189539 : Reach 189539 := rs (se 1 (by rfl) ⟨142154, by rfl⟩) R284309
theorem R58481 : Reach 58481 := rs (se 2 (by rfl) ⟨21930, by rfl⟩) R43861
theorem R58499 : Reach 58499 := rs (se 1 (by rfl) ⟨43874, by rfl⟩) R87749
theorem R58529 : Reach 58529 := rs (se 2 (by rfl) ⟨21948, by rfl⟩) R43897
theorem R58547 : Reach 58547 := rs (se 1 (by rfl) ⟨43910, by rfl⟩) R87821
theorem R58577 : Reach 58577 := rs (se 2 (by rfl) ⟨21966, by rfl⟩) R43933
theorem R58595 : Reach 58595 := rs (se 1 (by rfl) ⟨43946, by rfl⟩) R87893
theorem R124145 : Reach 124145 := rs (se 2 (by rfl) ⟨46554, by rfl⟩) R93109
theorem R58625 : Reach 58625 := rs (se 2 (by rfl) ⟨21984, by rfl⟩) R43969
theorem R189701 : Reach 189701 := rs (se 4 (by rfl) ⟨17784, by rfl⟩) R35569
theorem R58643 : Reach 58643 := rs (se 1 (by rfl) ⟨43982, by rfl⟩) R87965
theorem R58673 : Reach 58673 := rs (se 2 (by rfl) ⟨22002, by rfl⟩) R44005
theorem R877877 : Reach 877877 := rs (se 5 (by rfl) ⟨41150, by rfl⟩) R82301
theorem R58691 : Reach 58691 := rs (se 1 (by rfl) ⟨44018, by rfl⟩) R88037
theorem R58819 : Reach 58819 := rs (se 1 (by rfl) ⟨44114, by rfl⟩) R88229
theorem R288197 : Reach 288197 := rs (se 4 (by rfl) ⟨27018, by rfl⟩) R54037
theorem R91601 : Reach 91601 := rs (se 2 (by rfl) ⟨34350, by rfl⟩) R68701
theorem R91651 : Reach 91651 := rs (se 1 (by rfl) ⟨68738, by rfl⟩) R137477
theorem R91793 : Reach 91793 := rs (se 2 (by rfl) ⟨34422, by rfl⟩) R68845
theorem R124685 : Reach 124685 := rs (se 3 (by rfl) ⟨23378, by rfl⟩) R46757
theorem R124739 : Reach 124739 := rs (se 1 (by rfl) ⟨93554, by rfl⟩) R187109
theorem R190349 : Reach 190349 := rs (se 3 (by rfl) ⟨35690, by rfl⟩) R71381
theorem R59393 : Reach 59393 := rs (se 2 (by rfl) ⟨22272, by rfl⟩) R44545
theorem R59459 : Reach 59459 := rs (se 1 (by rfl) ⟨44594, by rfl⟩) R89189
theorem R59521 : Reach 59521 := rs (se 2 (by rfl) ⟨22320, by rfl⟩) R44641
theorem R125069 : Reach 125069 := rs (se 3 (by rfl) ⟨23450, by rfl⟩) R46901
theorem R59537 : Reach 59537 := rs (se 2 (by rfl) ⟨22326, by rfl⟩) R44653
theorem R59555 : Reach 59555 := rs (se 1 (by rfl) ⟨44666, by rfl⟩) R89333
theorem R157859 : Reach 157859 := rs (se 1 (by rfl) ⟨118394, by rfl⟩) R236789
theorem R387341 : Reach 387341 := rs (se 3 (by rfl) ⟨72626, by rfl⟩) R145253
theorem R59683 : Reach 59683 := rs (se 1 (by rfl) ⟨44762, by rfl⟩) R89525
theorem R92515 : Reach 92515 := rs (se 1 (by rfl) ⟨69386, by rfl⟩) R138773
theorem R59825 : Reach 59825 := rs (se 2 (by rfl) ⟨22434, by rfl⟩) R44869
theorem R387509 : Reach 387509 := rs (se 5 (by rfl) ⟨18164, by rfl⟩) R36329
theorem R59921 : Reach 59921 := rs (se 2 (by rfl) ⟨22470, by rfl⟩) R44941
theorem R59953 : Reach 59953 := rs (se 2 (by rfl) ⟨22482, by rfl⟩) R44965
theorem R59987 : Reach 59987 := rs (se 1 (by rfl) ⟨44990, by rfl⟩) R89981
theorem R289379 : Reach 289379 := rs (se 1 (by rfl) ⟨217034, by rfl⟩) R434069
theorem R92785 : Reach 92785 := rs (se 2 (by rfl) ⟨34794, by rfl⟩) R69589
theorem R60049 : Reach 60049 := rs (se 2 (by rfl) ⟨22518, by rfl⟩) R45037
theorem R125603 : Reach 125603 := rs (se 1 (by rfl) ⟨94202, by rfl⟩) R188405
theorem R60115 : Reach 60115 := rs (se 1 (by rfl) ⟨45086, by rfl⟩) R90173
theorem R453347 : Reach 453347 := rs (se 1 (by rfl) ⟨340010, by rfl⟩) R680021
theorem R92963 : Reach 92963 := rs (se 1 (by rfl) ⟨69722, by rfl⟩) R139445
theorem R60257 : Reach 60257 := rs (se 2 (by rfl) ⟨22596, by rfl⟩) R45193
theorem R93059 : Reach 93059 := rs (se 1 (by rfl) ⟨69794, by rfl⟩) R139589
theorem R125873 : Reach 125873 := rs (se 2 (by rfl) ⟨47202, by rfl⟩) R94405
theorem R60385 : Reach 60385 := rs (se 2 (by rfl) ⟨22644, by rfl⟩) R45289
theorem R60419 : Reach 60419 := rs (se 1 (by rfl) ⟨45314, by rfl⟩) R90629
theorem R93187 : Reach 93187 := rs (se 1 (by rfl) ⟨69890, by rfl⟩) R139781
theorem R93233 : Reach 93233 := rs (se 2 (by rfl) ⟨34962, by rfl⟩) R69925
theorem R93251 : Reach 93251 := rs (se 1 (by rfl) ⟨69938, by rfl⟩) R139877
theorem R60547 : Reach 60547 := rs (se 1 (by rfl) ⟨45410, by rfl⟩) R90821
theorem R60689 : Reach 60689 := rs (se 2 (by rfl) ⟨22758, by rfl⟩) R45517
theorem R60817 : Reach 60817 := rs (se 2 (by rfl) ⟨22806, by rfl⟩) R45613
theorem R60851 : Reach 60851 := rs (se 1 (by rfl) ⟨45638, by rfl⟩) R91277
theorem R126413 : Reach 126413 := rs (se 3 (by rfl) ⟨23702, by rfl⟩) R47405
theorem R93649 : Reach 93649 := rs (se 2 (by rfl) ⟨35118, by rfl⟩) R70237
theorem R421361 : Reach 421361 := rs (se 2 (by rfl) ⟨158010, by rfl⟩) R316021
theorem R93745 : Reach 93745 := rs (se 2 (by rfl) ⟨35154, by rfl⟩) R70309
theorem R60979 : Reach 60979 := rs (se 1 (by rfl) ⟨45734, by rfl⟩) R91469
theorem R93869 : Reach 93869 := rs (se 3 (by rfl) ⟨17600, by rfl⟩) R35201
theorem R61121 : Reach 61121 := rs (se 2 (by rfl) ⟨22920, by rfl⟩) R45841
theorem R61249 : Reach 61249 := rs (se 2 (by rfl) ⟨22968, by rfl⟩) R45937
theorem R61283 : Reach 61283 := rs (se 1 (by rfl) ⟨45962, by rfl⟩) R91925
theorem R94061 : Reach 94061 := rs (se 3 (by rfl) ⟨17636, by rfl⟩) R35273
theorem R61411 : Reach 61411 := rs (se 1 (by rfl) ⟨46058, by rfl⟩) R92117
theorem R94193 : Reach 94193 := rs (se 2 (by rfl) ⟨35322, by rfl⟩) R70645
theorem R94243 : Reach 94243 := rs (se 1 (by rfl) ⟨70682, by rfl⟩) R141365
theorem R61553 : Reach 61553 := rs (se 2 (by rfl) ⟨23082, by rfl⟩) R46165
theorem R159857 : Reach 159857 := rs (se 2 (by rfl) ⟨59946, by rfl⟩) R119893
theorem R61555 : Reach 61555 := rs (se 1 (by rfl) ⟨46166, by rfl⟩) R92333
theorem R487565 : Reach 487565 := rs (se 3 (by rfl) ⟨91418, by rfl⟩) R182837
theorem R94385 : Reach 94385 := rs (se 2 (by rfl) ⟨35394, by rfl⟩) R70789
theorem R61681 : Reach 61681 := rs (se 2 (by rfl) ⟨23130, by rfl⟩) R46261
theorem R61715 : Reach 61715 := rs (se 1 (by rfl) ⟨46286, by rfl⟩) R92573
theorem R61793 : Reach 61793 := rs (se 2 (by rfl) ⟨23172, by rfl⟩) R46345
theorem R127331 : Reach 127331 := rs (se 1 (by rfl) ⟨95498, by rfl⟩) R190997
theorem R61843 : Reach 61843 := rs (se 1 (by rfl) ⟨46382, by rfl⟩) R92765
theorem R258545 : Reach 258545 := rs (se 2 (by rfl) ⟨96954, by rfl⟩) R193909
theorem R61985 : Reach 61985 := rs (se 2 (by rfl) ⟨23244, by rfl⟩) R46489
theorem R94765 : Reach 94765 := rs (se 3 (by rfl) ⟨17768, by rfl⟩) R35537
theorem R127601 : Reach 127601 := rs (se 2 (by rfl) ⟨47850, by rfl⟩) R95701
theorem R62113 : Reach 62113 := rs (se 2 (by rfl) ⟨23292, by rfl⟩) R46585
theorem R62147 : Reach 62147 := rs (se 1 (by rfl) ⟨46610, by rfl⟩) R93221
theorem R193265 : Reach 193265 := rs (se 2 (by rfl) ⟨72474, by rfl⟩) R144949
theorem R62227 : Reach 62227 := rs (se 1 (by rfl) ⟨46670, by rfl⟩) R93341
theorem R62275 : Reach 62275 := rs (se 1 (by rfl) ⟨46706, by rfl⟩) R93413
theorem R95053 : Reach 95053 := rs (se 3 (by rfl) ⟨17822, by rfl⟩) R35645
theorem R226253 : Reach 226253 := rs (se 3 (by rfl) ⟨42422, by rfl⟩) R84845
theorem R62417 : Reach 62417 := rs (se 2 (by rfl) ⟨23406, by rfl⟩) R46813
theorem R95203 : Reach 95203 := rs (se 1 (by rfl) ⟨71402, by rfl⟩) R142805
theorem R62545 : Reach 62545 := rs (se 2 (by rfl) ⟨23454, by rfl⟩) R46909
theorem R128141 : Reach 128141 := rs (se 3 (by rfl) ⟨24026, by rfl⟩) R48053
theorem R95377 : Reach 95377 := rs (se 2 (by rfl) ⟨35766, by rfl⟩) R71533
theorem R455989 : Reach 455989 := rs (se 5 (by rfl) ⟨21374, by rfl⟩) R42749
theorem R259469 : Reach 259469 := rs (se 3 (by rfl) ⟨48650, by rfl⟩) R97301
theorem R95651 : Reach 95651 := rs (se 1 (by rfl) ⟨71738, by rfl⟩) R143477
theorem R325133 : Reach 325133 := rs (se 3 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R63011 : Reach 63011 := rs (se 1 (by rfl) ⟨47258, by rfl⟩) R94517
theorem R95843 : Reach 95843 := rs (se 1 (by rfl) ⟨71882, by rfl⟩) R143765
theorem R63139 : Reach 63139 := rs (se 1 (by rfl) ⟨47354, by rfl⟩) R94709
theorem R95917 : Reach 95917 := rs (se 3 (by rfl) ⟨17984, by rfl⟩) R35969
theorem R96013 : Reach 96013 := rs (se 3 (by rfl) ⟨18002, by rfl⟩) R36005
theorem R63281 : Reach 63281 := rs (se 2 (by rfl) ⟨23730, by rfl⟩) R47461
theorem R63409 : Reach 63409 := rs (se 2 (by rfl) ⟨23778, by rfl⟩) R47557
theorem R129059 : Reach 129059 := rs (se 1 (by rfl) ⟨96794, by rfl⟩) R193589
theorem R194723 : Reach 194723 := rs (se 1 (by rfl) ⟨146042, by rfl⟩) R292085
theorem R96461 : Reach 96461 := rs (se 3 (by rfl) ⟨18086, by rfl⟩) R36173
theorem R129329 : Reach 129329 := rs (se 2 (by rfl) ⟨48498, by rfl⟩) R96997
theorem R194885 : Reach 194885 := rs (se 4 (by rfl) ⟨18270, by rfl⟩) R36541
theorem R63875 : Reach 63875 := rs (se 1 (by rfl) ⟨47906, by rfl⟩) R95813
theorem R96653 : Reach 96653 := rs (se 3 (by rfl) ⟨18122, by rfl⟩) R36245
theorem R64003 : Reach 64003 := rs (se 1 (by rfl) ⟨48002, by rfl⟩) R96005
theorem R162317 : Reach 162317 := rs (se 3 (by rfl) ⟨30434, by rfl⟩) R60869
theorem R96785 : Reach 96785 := rs (se 2 (by rfl) ⟨36294, by rfl⟩) R72589
theorem R96835 : Reach 96835 := rs (se 1 (by rfl) ⟨72626, by rfl⟩) R145253
theorem R64081 : Reach 64081 := rs (se 2 (by rfl) ⟨24030, by rfl⟩) R48061
theorem R293489 : Reach 293489 := rs (se 2 (by rfl) ⟨110058, by rfl⟩) R220117
theorem R64145 : Reach 64145 := rs (se 2 (by rfl) ⟨24054, by rfl⟩) R48109
theorem R96977 : Reach 96977 := rs (se 2 (by rfl) ⟨36366, by rfl⟩) R72733
theorem R64273 : Reach 64273 := rs (se 2 (by rfl) ⟨24102, by rfl⟩) R48205
theorem R129869 : Reach 129869 := rs (se 3 (by rfl) ⟨24350, by rfl⟩) R48701
theorem R195533 : Reach 195533 := rs (se 3 (by rfl) ⟨36662, by rfl⟩) R73325
theorem R64643 : Reach 64643 := rs (se 1 (by rfl) ⟨48482, by rfl⟩) R96965
theorem R294029 : Reach 294029 := rs (se 3 (by rfl) ⟨55130, by rfl⟩) R110261
theorem R64739 : Reach 64739 := rs (se 1 (by rfl) ⟨48554, by rfl⟩) R97109
theorem R64867 : Reach 64867 := rs (se 1 (by rfl) ⟨48650, by rfl⟩) R97301
theorem R97645 : Reach 97645 := rs (se 3 (by rfl) ⟨18308, by rfl⟩) R36617
theorem R1441165 : Reach 1441165 := rs (se 3 (by rfl) ⟨270218, by rfl⟩) R540437
theorem R65009 : Reach 65009 := rs (se 2 (by rfl) ⟨24378, by rfl⟩) R48757
theorem R261701 : Reach 261701 := rs (se 4 (by rfl) ⟨24534, by rfl⟩) R49069
theorem R65137 : Reach 65137 := rs (se 2 (by rfl) ⟨24426, by rfl⟩) R48853
theorem R97969 : Reach 97969 := rs (se 2 (by rfl) ⟨36738, by rfl⟩) R73477
theorem R130787 : Reach 130787 := rs (se 1 (by rfl) ⟨98090, by rfl⟩) R196181
theorem R98243 : Reach 98243 := rs (se 1 (by rfl) ⟨73682, by rfl⟩) R147365
theorem R131057 : Reach 131057 := rs (se 2 (by rfl) ⟨49146, by rfl⟩) R98293
theorem R65623 : Reach 65623 := rs (se 1 (by rfl) ⟨49217, by rfl⟩) R98435
theorem R131165 : Reach 131165 := rs (se 3 (by rfl) ⟨24593, by rfl⟩) R49187
theorem R98455 : Reach 98455 := rs (se 1 (by rfl) ⟨73841, by rfl⟩) R147683
theorem R197081 : Reach 197081 := rs (se 2 (by rfl) ⟨73905, by rfl⟩) R147811
theorem R557603 : Reach 557603 := rs (se 1 (by rfl) ⟨418202, by rfl⟩) R836405
theorem R98891 : Reach 98891 := rs (se 1 (by rfl) ⟨74168, by rfl⟩) R148337
theorem R197477 : Reach 197477 := rs (se 4 (by rfl) ⟨18513, by rfl⟩) R37027
theorem R164915 : Reach 164915 := rs (se 1 (by rfl) ⟨123686, by rfl⟩) R247373
theorem R197963 : Reach 197963 := rs (se 1 (by rfl) ⟨148472, by rfl⟩) R296945
theorem R460363 : Reach 460363 := rs (se 1 (by rfl) ⟨345272, by rfl⟩) R690545
theorem R67159 : Reach 67159 := rs (se 1 (by rfl) ⟨50369, by rfl⟩) R100739
theorem R133015 : Reach 133015 := rs (se 1 (by rfl) ⟨99761, by rfl⟩) R199523
theorem R133123 : Reach 133123 := rs (se 1 (by rfl) ⟨99842, by rfl⟩) R199685
theorem R67699 : Reach 67699 := rs (se 1 (by rfl) ⟨50774, by rfl⟩) R101549
theorem R133265 : Reach 133265 := rs (se 2 (by rfl) ⟨49974, by rfl⟩) R99949
theorem R166195 : Reach 166195 := rs (se 1 (by rfl) ⟨124646, by rfl⟩) R249293
theorem R35127 : Reach 35127 := rs (se 1 (by rfl) ⟨26345, by rfl⟩) R52691
theorem R35147 : Reach 35147 := rs (se 1 (by rfl) ⟨26360, by rfl⟩) R52721
theorem R35159 : Reach 35159 := rs (se 1 (by rfl) ⟨26369, by rfl⟩) R52739
theorem R35179 : Reach 35179 := rs (se 1 (by rfl) ⟨26384, by rfl⟩) R52769
theorem R35191 : Reach 35191 := rs (se 1 (by rfl) ⟨26393, by rfl⟩) R52787
theorem R67979 : Reach 67979 := rs (se 1 (by rfl) ⟨50984, by rfl⟩) R101969
theorem R35211 : Reach 35211 := rs (se 1 (by rfl) ⟨26408, by rfl⟩) R52817
theorem R35223 : Reach 35223 := rs (se 1 (by rfl) ⟨26417, by rfl⟩) R52835
theorem R35243 : Reach 35243 := rs (se 1 (by rfl) ⟨26432, by rfl⟩) R52865
theorem R35255 : Reach 35255 := rs (se 1 (by rfl) ⟨26441, by rfl⟩) R52883
theorem R68033 : Reach 68033 := rs (se 2 (by rfl) ⟨25512, by rfl⟩) R51025
theorem R35275 : Reach 35275 := rs (se 1 (by rfl) ⟨26456, by rfl⟩) R52913
theorem R35287 : Reach 35287 := rs (se 1 (by rfl) ⟨26465, by rfl⟩) R52931
theorem R35307 : Reach 35307 := rs (se 1 (by rfl) ⟨26480, by rfl⟩) R52961
theorem R35319 : Reach 35319 := rs (se 1 (by rfl) ⟨26489, by rfl⟩) R52979
theorem R35339 : Reach 35339 := rs (se 1 (by rfl) ⟨26504, by rfl⟩) R53009
theorem R35351 : Reach 35351 := rs (se 1 (by rfl) ⟨26513, by rfl⟩) R53027
theorem R35371 : Reach 35371 := rs (se 1 (by rfl) ⟨26528, by rfl⟩) R53057
theorem R35383 : Reach 35383 := rs (se 1 (by rfl) ⟨26537, by rfl⟩) R53075
theorem R35403 : Reach 35403 := rs (se 1 (by rfl) ⟨26552, by rfl⟩) R53105
theorem R35415 : Reach 35415 := rs (se 1 (by rfl) ⟨26561, by rfl⟩) R53123
theorem R35435 : Reach 35435 := rs (se 1 (by rfl) ⟨26576, by rfl⟩) R53153
theorem R35447 : Reach 35447 := rs (se 1 (by rfl) ⟨26585, by rfl⟩) R53171
theorem R166531 : Reach 166531 := rs (se 1 (by rfl) ⟨124898, by rfl⟩) R249797
theorem R35467 : Reach 35467 := rs (se 1 (by rfl) ⟨26600, by rfl⟩) R53201
theorem R35479 : Reach 35479 := rs (se 1 (by rfl) ⟨26609, by rfl⟩) R53219
theorem R35499 : Reach 35499 := rs (se 1 (by rfl) ⟨26624, by rfl⟩) R53249
theorem R35511 : Reach 35511 := rs (se 1 (by rfl) ⟨26633, by rfl⟩) R53267
theorem R35531 : Reach 35531 := rs (se 1 (by rfl) ⟨26648, by rfl⟩) R53297
theorem R35543 : Reach 35543 := rs (se 1 (by rfl) ⟨26657, by rfl⟩) R53315
theorem R101081 : Reach 101081 := rs (se 2 (by rfl) ⟨37905, by rfl⟩) R75811
theorem R35563 : Reach 35563 := rs (se 1 (by rfl) ⟨26672, by rfl⟩) R53345
theorem R35575 : Reach 35575 := rs (se 1 (by rfl) ⟨26681, by rfl⟩) R53363
theorem R35595 : Reach 35595 := rs (se 1 (by rfl) ⟨26696, by rfl⟩) R53393
theorem R35607 : Reach 35607 := rs (se 1 (by rfl) ⟨26705, by rfl⟩) R53411
theorem R35627 : Reach 35627 := rs (se 1 (by rfl) ⟨26720, by rfl⟩) R53441
theorem R35639 : Reach 35639 := rs (se 1 (by rfl) ⟨26729, by rfl⟩) R53459
theorem R101195 : Reach 101195 := rs (se 1 (by rfl) ⟨75896, by rfl⟩) R151793
theorem R35659 : Reach 35659 := rs (se 1 (by rfl) ⟨26744, by rfl⟩) R53489
theorem R35671 : Reach 35671 := rs (se 1 (by rfl) ⟨26753, by rfl⟩) R53507
theorem R35691 : Reach 35691 := rs (se 1 (by rfl) ⟨26768, by rfl⟩) R53537
theorem R35703 : Reach 35703 := rs (se 1 (by rfl) ⟨26777, by rfl⟩) R53555
theorem R35723 : Reach 35723 := rs (se 1 (by rfl) ⟨26792, by rfl⟩) R53585
theorem R35735 : Reach 35735 := rs (se 1 (by rfl) ⟨26801, by rfl⟩) R53603
theorem R35755 : Reach 35755 := rs (se 1 (by rfl) ⟨26816, by rfl⟩) R53633
theorem R68531 : Reach 68531 := rs (se 1 (by rfl) ⟨51398, by rfl⟩) R102797
theorem R35767 : Reach 35767 := rs (se 1 (by rfl) ⟨26825, by rfl⟩) R53651
theorem R35787 : Reach 35787 := rs (se 1 (by rfl) ⟨26840, by rfl⟩) R53681
theorem R35799 : Reach 35799 := rs (se 1 (by rfl) ⟨26849, by rfl⟩) R53699
theorem R35819 : Reach 35819 := rs (se 1 (by rfl) ⟨26864, by rfl⟩) R53729
theorem R35831 : Reach 35831 := rs (se 1 (by rfl) ⟨26873, by rfl⟩) R53747
theorem R35851 : Reach 35851 := rs (se 1 (by rfl) ⟨26888, by rfl⟩) R53777
theorem R35863 : Reach 35863 := rs (se 1 (by rfl) ⟨26897, by rfl⟩) R53795
theorem R35883 : Reach 35883 := rs (se 1 (by rfl) ⟨26912, by rfl⟩) R53825
theorem R35895 : Reach 35895 := rs (se 1 (by rfl) ⟨26921, by rfl⟩) R53843
theorem R35915 : Reach 35915 := rs (se 1 (by rfl) ⟨26936, by rfl⟩) R53873
theorem R35927 : Reach 35927 := rs (se 1 (by rfl) ⟨26945, by rfl⟩) R53891
theorem R35947 : Reach 35947 := rs (se 1 (by rfl) ⟨26960, by rfl⟩) R53921
theorem R68723 : Reach 68723 := rs (se 1 (by rfl) ⟨51542, by rfl⟩) R103085
theorem R35959 : Reach 35959 := rs (se 1 (by rfl) ⟨26969, by rfl⟩) R53939
theorem R68737 : Reach 68737 := rs (se 2 (by rfl) ⟨25776, by rfl⟩) R51553
theorem R35979 : Reach 35979 := rs (se 1 (by rfl) ⟨26984, by rfl⟩) R53969
theorem R35991 : Reach 35991 := rs (se 1 (by rfl) ⟨26993, by rfl⟩) R53987
theorem R36011 : Reach 36011 := rs (se 1 (by rfl) ⟨27008, by rfl⟩) R54017
theorem R36023 : Reach 36023 := rs (se 1 (by rfl) ⟨27017, by rfl⟩) R54035
theorem R36043 : Reach 36043 := rs (se 1 (by rfl) ⟨27032, by rfl⟩) R54065
theorem R36055 : Reach 36055 := rs (se 1 (by rfl) ⟨27041, by rfl⟩) R54083
theorem R68825 : Reach 68825 := rs (se 2 (by rfl) ⟨25809, by rfl⟩) R51619
theorem R36075 : Reach 36075 := rs (se 1 (by rfl) ⟨27056, by rfl⟩) R54113
theorem R36087 : Reach 36087 := rs (se 1 (by rfl) ⟨27065, by rfl⟩) R54131
theorem R36107 : Reach 36107 := rs (se 1 (by rfl) ⟨27080, by rfl⟩) R54161
theorem R36119 : Reach 36119 := rs (se 1 (by rfl) ⟨27089, by rfl⟩) R54179
theorem R36139 : Reach 36139 := rs (se 1 (by rfl) ⟨27104, by rfl⟩) R54209
theorem R36151 : Reach 36151 := rs (se 1 (by rfl) ⟨27113, by rfl⟩) R54227
theorem R36171 : Reach 36171 := rs (se 1 (by rfl) ⟨27128, by rfl⟩) R54257
theorem R36183 : Reach 36183 := rs (se 1 (by rfl) ⟨27137, by rfl⟩) R54275
theorem R68951 : Reach 68951 := rs (se 1 (by rfl) ⟨51713, by rfl⟩) R103427
theorem R36203 : Reach 36203 := rs (se 1 (by rfl) ⟨27152, by rfl⟩) R54305
theorem R36215 : Reach 36215 := rs (se 1 (by rfl) ⟨27161, by rfl⟩) R54323
theorem R134531 : Reach 134531 := rs (se 1 (by rfl) ⟨100898, by rfl⟩) R201797
theorem R36235 : Reach 36235 := rs (se 1 (by rfl) ⟨27176, by rfl⟩) R54353
theorem R36247 : Reach 36247 := rs (se 1 (by rfl) ⟨27185, by rfl⟩) R54371
theorem R36267 : Reach 36267 := rs (se 1 (by rfl) ⟨27200, by rfl⟩) R54401
theorem R36279 : Reach 36279 := rs (se 1 (by rfl) ⟨27209, by rfl⟩) R54419
theorem R36299 : Reach 36299 := rs (se 1 (by rfl) ⟨27224, by rfl⟩) R54449
theorem R36311 : Reach 36311 := rs (se 1 (by rfl) ⟨27233, by rfl⟩) R54467
theorem R36331 : Reach 36331 := rs (se 1 (by rfl) ⟨27248, by rfl⟩) R54497
theorem R36343 : Reach 36343 := rs (se 1 (by rfl) ⟨27257, by rfl⟩) R54515
theorem R36363 : Reach 36363 := rs (se 1 (by rfl) ⟨27272, by rfl⟩) R54545
theorem R36375 : Reach 36375 := rs (se 1 (by rfl) ⟨27281, by rfl⟩) R54563
theorem R36395 : Reach 36395 := rs (se 1 (by rfl) ⟨27296, by rfl⟩) R54593
theorem R36407 : Reach 36407 := rs (se 1 (by rfl) ⟨27305, by rfl⟩) R54611
theorem R36427 : Reach 36427 := rs (se 1 (by rfl) ⟨27320, by rfl⟩) R54641
theorem R36439 : Reach 36439 := rs (se 1 (by rfl) ⟨27329, by rfl⟩) R54659
theorem R36459 : Reach 36459 := rs (se 1 (by rfl) ⟨27344, by rfl⟩) R54689
theorem R36471 : Reach 36471 := rs (se 1 (by rfl) ⟨27353, by rfl⟩) R54707
theorem R36491 : Reach 36491 := rs (se 1 (by rfl) ⟨27368, by rfl⟩) R54737
theorem R36503 : Reach 36503 := rs (se 1 (by rfl) ⟨27377, by rfl⟩) R54755
theorem R36523 : Reach 36523 := rs (se 1 (by rfl) ⟨27392, by rfl⟩) R54785
theorem R36535 : Reach 36535 := rs (se 1 (by rfl) ⟨27401, by rfl⟩) R54803
theorem R36555 : Reach 36555 := rs (se 1 (by rfl) ⟨27416, by rfl⟩) R54833
theorem R36567 : Reach 36567 := rs (se 1 (by rfl) ⟨27425, by rfl⟩) R54851
theorem R36587 : Reach 36587 := rs (se 1 (by rfl) ⟨27440, by rfl⟩) R54881
theorem R36599 : Reach 36599 := rs (se 1 (by rfl) ⟨27449, by rfl⟩) R54899
theorem R36619 : Reach 36619 := rs (se 1 (by rfl) ⟨27464, by rfl⟩) R54929
theorem R36631 : Reach 36631 := rs (se 1 (by rfl) ⟨27473, by rfl⟩) R54947
theorem R36651 : Reach 36651 := rs (se 1 (by rfl) ⟨27488, by rfl⟩) R54977
theorem R36663 : Reach 36663 := rs (se 1 (by rfl) ⟨27497, by rfl⟩) R54995
theorem R36683 : Reach 36683 := rs (se 1 (by rfl) ⟨27512, by rfl⟩) R55025
theorem R36695 : Reach 36695 := rs (se 1 (by rfl) ⟨27521, by rfl⟩) R55043
theorem R36715 : Reach 36715 := rs (se 1 (by rfl) ⟨27536, by rfl⟩) R55073
theorem R69491 : Reach 69491 := rs (se 1 (by rfl) ⟨52118, by rfl⟩) R104237
theorem R36727 : Reach 36727 := rs (se 1 (by rfl) ⟨27545, by rfl⟩) R55091
theorem R36747 : Reach 36747 := rs (se 1 (by rfl) ⟨27560, by rfl⟩) R55121
theorem R36759 : Reach 36759 := rs (se 1 (by rfl) ⟨27569, by rfl⟩) R55139
theorem R36779 : Reach 36779 := rs (se 1 (by rfl) ⟨27584, by rfl⟩) R55169
theorem R102323 : Reach 102323 := rs (se 1 (by rfl) ⟨76742, by rfl⟩) R153485
theorem R36791 : Reach 36791 := rs (se 1 (by rfl) ⟨27593, by rfl⟩) R55187
theorem R36811 : Reach 36811 := rs (se 1 (by rfl) ⟨27608, by rfl⟩) R55217
theorem R36823 : Reach 36823 := rs (se 1 (by rfl) ⟨27617, by rfl⟩) R55235
theorem R36843 : Reach 36843 := rs (se 1 (by rfl) ⟨27632, by rfl⟩) R55265
theorem R36855 : Reach 36855 := rs (se 1 (by rfl) ⟨27641, by rfl⟩) R55283
theorem R36875 : Reach 36875 := rs (se 1 (by rfl) ⟨27656, by rfl⟩) R55313
theorem R36887 : Reach 36887 := rs (se 1 (by rfl) ⟨27665, by rfl⟩) R55331
theorem R36907 : Reach 36907 := rs (se 1 (by rfl) ⟨27680, by rfl⟩) R55361
theorem R36919 : Reach 36919 := rs (se 1 (by rfl) ⟨27689, by rfl⟩) R55379
theorem R36939 : Reach 36939 := rs (se 1 (by rfl) ⟨27704, by rfl⟩) R55409
theorem R36951 : Reach 36951 := rs (se 1 (by rfl) ⟨27713, by rfl⟩) R55427
theorem R331877 : Reach 331877 := rs (se 4 (by rfl) ⟨31113, by rfl⟩) R62227
theorem R36971 : Reach 36971 := rs (se 1 (by rfl) ⟨27728, by rfl⟩) R55457
theorem R36983 : Reach 36983 := rs (se 1 (by rfl) ⟨27737, by rfl⟩) R55475
theorem R37003 : Reach 37003 := rs (se 1 (by rfl) ⟨27752, by rfl⟩) R55505
theorem R37015 : Reach 37015 := rs (se 1 (by rfl) ⟨27761, by rfl⟩) R55523
theorem R37035 : Reach 37035 := rs (se 1 (by rfl) ⟨27776, by rfl⟩) R55553
theorem R37047 : Reach 37047 := rs (se 1 (by rfl) ⟨27785, by rfl⟩) R55571
theorem R37067 : Reach 37067 := rs (se 1 (by rfl) ⟨27800, by rfl⟩) R55601
theorem R37079 : Reach 37079 := rs (se 1 (by rfl) ⟨27809, by rfl⟩) R55619
theorem R37099 : Reach 37099 := rs (se 1 (by rfl) ⟨27824, by rfl⟩) R55649
theorem R37111 : Reach 37111 := rs (se 1 (by rfl) ⟨27833, by rfl⟩) R55667
theorem R37131 : Reach 37131 := rs (se 1 (by rfl) ⟨27848, by rfl⟩) R55697
theorem R37143 : Reach 37143 := rs (se 1 (by rfl) ⟨27857, by rfl⟩) R55715
theorem R37163 : Reach 37163 := rs (se 1 (by rfl) ⟨27872, by rfl⟩) R55745
theorem R37175 : Reach 37175 := rs (se 1 (by rfl) ⟨27881, by rfl⟩) R55763
theorem R102721 : Reach 102721 := rs (se 2 (by rfl) ⟨38520, by rfl⟩) R77041
theorem R37195 : Reach 37195 := rs (se 1 (by rfl) ⟨27896, by rfl⟩) R55793
theorem R37207 : Reach 37207 := rs (se 1 (by rfl) ⟨27905, by rfl⟩) R55811
theorem R69977 : Reach 69977 := rs (se 2 (by rfl) ⟨26241, by rfl⟩) R52483
theorem R37227 : Reach 37227 := rs (se 1 (by rfl) ⟨27920, by rfl⟩) R55841
theorem R37239 : Reach 37239 := rs (se 1 (by rfl) ⟨27929, by rfl⟩) R55859
theorem R37259 : Reach 37259 := rs (se 1 (by rfl) ⟨27944, by rfl⟩) R55889
theorem R37271 : Reach 37271 := rs (se 1 (by rfl) ⟨27953, by rfl⟩) R55907
theorem R37291 : Reach 37291 := rs (se 1 (by rfl) ⟨27968, by rfl⟩) R55937
theorem R37303 : Reach 37303 := rs (se 1 (by rfl) ⟨27977, by rfl⟩) R55955
theorem R37323 : Reach 37323 := rs (se 1 (by rfl) ⟨27992, by rfl⟩) R55985
theorem R37335 : Reach 37335 := rs (se 1 (by rfl) ⟨28001, by rfl⟩) R56003
theorem R37355 : Reach 37355 := rs (se 1 (by rfl) ⟨28016, by rfl⟩) R56033
theorem R37367 : Reach 37367 := rs (se 1 (by rfl) ⟨28025, by rfl⟩) R56051
theorem R37387 : Reach 37387 := rs (se 1 (by rfl) ⟨28040, by rfl⟩) R56081
theorem R37399 : Reach 37399 := rs (se 1 (by rfl) ⟨28049, by rfl⟩) R56099
theorem R37419 : Reach 37419 := rs (se 1 (by rfl) ⟨28064, by rfl⟩) R56129
theorem R135731 : Reach 135731 := rs (se 1 (by rfl) ⟨101798, by rfl⟩) R203597
theorem R37431 : Reach 37431 := rs (se 1 (by rfl) ⟨28073, by rfl⟩) R56147
theorem R37451 : Reach 37451 := rs (se 1 (by rfl) ⟨28088, by rfl⟩) R56177
theorem R37463 : Reach 37463 := rs (se 1 (by rfl) ⟨28097, by rfl⟩) R56195
theorem R37483 : Reach 37483 := rs (se 1 (by rfl) ⟨28112, by rfl⟩) R56225
theorem R37495 : Reach 37495 := rs (se 1 (by rfl) ⟨28121, by rfl⟩) R56243
theorem R37515 : Reach 37515 := rs (se 1 (by rfl) ⟨28136, by rfl⟩) R56273
theorem R37527 : Reach 37527 := rs (se 1 (by rfl) ⟨28145, by rfl⟩) R56291
theorem R37547 : Reach 37547 := rs (se 1 (by rfl) ⟨28160, by rfl⟩) R56321
theorem R37559 : Reach 37559 := rs (se 1 (by rfl) ⟨28169, by rfl⟩) R56339
theorem R37579 : Reach 37579 := rs (se 1 (by rfl) ⟨28184, by rfl⟩) R56369
theorem R37591 : Reach 37591 := rs (se 1 (by rfl) ⟨28193, by rfl⟩) R56387
theorem R37611 : Reach 37611 := rs (se 1 (by rfl) ⟨28208, by rfl⟩) R56417
theorem R37623 : Reach 37623 := rs (se 1 (by rfl) ⟨28217, by rfl⟩) R56435
theorem R37643 : Reach 37643 := rs (se 1 (by rfl) ⟨28232, by rfl⟩) R56465
theorem R37655 : Reach 37655 := rs (se 1 (by rfl) ⟨28241, by rfl⟩) R56483
theorem R37675 : Reach 37675 := rs (se 1 (by rfl) ⟨28256, by rfl⟩) R56513
theorem R37687 : Reach 37687 := rs (se 1 (by rfl) ⟨28265, by rfl⟩) R56531
theorem R37707 : Reach 37707 := rs (se 1 (by rfl) ⟨28280, by rfl⟩) R56561
theorem R37719 : Reach 37719 := rs (se 1 (by rfl) ⟨28289, by rfl⟩) R56579
theorem R37739 : Reach 37739 := rs (se 1 (by rfl) ⟨28304, by rfl⟩) R56609
theorem R37751 : Reach 37751 := rs (se 1 (by rfl) ⟨28313, by rfl⟩) R56627
theorem R37771 : Reach 37771 := rs (se 1 (by rfl) ⟨28328, by rfl⟩) R56657
theorem R37783 : Reach 37783 := rs (se 1 (by rfl) ⟨28337, by rfl⟩) R56675
theorem R37803 : Reach 37803 := rs (se 1 (by rfl) ⟨28352, by rfl⟩) R56705
theorem R37815 : Reach 37815 := rs (se 1 (by rfl) ⟨28361, by rfl⟩) R56723
theorem R37835 : Reach 37835 := rs (se 1 (by rfl) ⟨28376, by rfl⟩) R56753
theorem R37847 : Reach 37847 := rs (se 1 (by rfl) ⟨28385, by rfl⟩) R56771
theorem R37867 : Reach 37867 := rs (se 1 (by rfl) ⟨28400, by rfl⟩) R56801
theorem R37879 : Reach 37879 := rs (se 1 (by rfl) ⟨28409, by rfl⟩) R56819
theorem R37899 : Reach 37899 := rs (se 1 (by rfl) ⟨28424, by rfl⟩) R56849
theorem R37911 : Reach 37911 := rs (se 1 (by rfl) ⟨28433, by rfl⟩) R56867
theorem R267299 : Reach 267299 := rs (se 1 (by rfl) ⟨200474, by rfl⟩) R400949
theorem R37931 : Reach 37931 := rs (se 1 (by rfl) ⟨28448, by rfl⟩) R56897
theorem R37943 : Reach 37943 := rs (se 1 (by rfl) ⟨28457, by rfl⟩) R56915
theorem R37963 : Reach 37963 := rs (se 1 (by rfl) ⟨28472, by rfl⟩) R56945
theorem R37975 : Reach 37975 := rs (se 1 (by rfl) ⟨28481, by rfl⟩) R56963
theorem R37995 : Reach 37995 := rs (se 1 (by rfl) ⟨28496, by rfl⟩) R56993
theorem R38007 : Reach 38007 := rs (se 1 (by rfl) ⟨28505, by rfl⟩) R57011
theorem R38027 : Reach 38027 := rs (se 1 (by rfl) ⟨28520, by rfl⟩) R57041
theorem R38039 : Reach 38039 := rs (se 1 (by rfl) ⟨28529, by rfl⟩) R57059
theorem R38059 : Reach 38059 := rs (se 1 (by rfl) ⟨28544, by rfl⟩) R57089
theorem R38071 : Reach 38071 := rs (se 1 (by rfl) ⟨28553, by rfl⟩) R57107
theorem R38091 : Reach 38091 := rs (se 1 (by rfl) ⟨28568, by rfl⟩) R57137
theorem R38103 : Reach 38103 := rs (se 1 (by rfl) ⟨28577, by rfl⟩) R57155
theorem R38123 : Reach 38123 := rs (se 1 (by rfl) ⟨28592, by rfl⟩) R57185
theorem R38135 : Reach 38135 := rs (se 1 (by rfl) ⟨28601, by rfl⟩) R57203
theorem R38155 : Reach 38155 := rs (se 1 (by rfl) ⟨28616, by rfl⟩) R57233
theorem R38167 : Reach 38167 := rs (se 1 (by rfl) ⟨28625, by rfl⟩) R57251
theorem R38187 : Reach 38187 := rs (se 1 (by rfl) ⟨28640, by rfl⟩) R57281
theorem R38199 : Reach 38199 := rs (se 1 (by rfl) ⟨28649, by rfl⟩) R57299
theorem R38219 : Reach 38219 := rs (se 1 (by rfl) ⟨28664, by rfl⟩) R57329
theorem R38231 : Reach 38231 := rs (se 1 (by rfl) ⟨28673, by rfl⟩) R57347
theorem R38251 : Reach 38251 := rs (se 1 (by rfl) ⟨28688, by rfl⟩) R57377
theorem R38263 : Reach 38263 := rs (se 1 (by rfl) ⟨28697, by rfl⟩) R57395
theorem R202115 : Reach 202115 := rs (se 1 (by rfl) ⟨151586, by rfl⟩) R303173
theorem R38283 : Reach 38283 := rs (se 1 (by rfl) ⟨28712, by rfl⟩) R57425
theorem R38295 : Reach 38295 := rs (se 1 (by rfl) ⟨28721, by rfl⟩) R57443
theorem R38315 : Reach 38315 := rs (se 1 (by rfl) ⟨28736, by rfl⟩) R57473
theorem R38327 : Reach 38327 := rs (se 1 (by rfl) ⟨28745, by rfl⟩) R57491
theorem R38347 : Reach 38347 := rs (se 1 (by rfl) ⟨28760, by rfl⟩) R57521
theorem R38359 : Reach 38359 := rs (se 1 (by rfl) ⟨28769, by rfl⟩) R57539
theorem R38379 : Reach 38379 := rs (se 1 (by rfl) ⟨28784, by rfl⟩) R57569
theorem R38391 : Reach 38391 := rs (se 1 (by rfl) ⟨28793, by rfl⟩) R57587
theorem R38411 : Reach 38411 := rs (se 1 (by rfl) ⟨28808, by rfl⟩) R57617
theorem R136727 : Reach 136727 := rs (se 1 (by rfl) ⟨102545, by rfl⟩) R205091
theorem R38423 : Reach 38423 := rs (se 1 (by rfl) ⟨28817, by rfl⟩) R57635
theorem R38443 : Reach 38443 := rs (se 1 (by rfl) ⟨28832, by rfl⟩) R57665
theorem R38455 : Reach 38455 := rs (se 1 (by rfl) ⟨28841, by rfl⟩) R57683
theorem R38475 : Reach 38475 := rs (se 1 (by rfl) ⟨28856, by rfl⟩) R57713
theorem R38487 : Reach 38487 := rs (se 1 (by rfl) ⟨28865, by rfl⟩) R57731
theorem R38507 : Reach 38507 := rs (se 1 (by rfl) ⟨28880, by rfl⟩) R57761
theorem R38519 : Reach 38519 := rs (se 1 (by rfl) ⟨28889, by rfl⟩) R57779
theorem R38539 : Reach 38539 := rs (se 1 (by rfl) ⟨28904, by rfl⟩) R57809
theorem R38551 : Reach 38551 := rs (se 1 (by rfl) ⟨28913, by rfl⟩) R57827
theorem R38571 : Reach 38571 := rs (se 1 (by rfl) ⟨28928, by rfl⟩) R57857
theorem R38583 : Reach 38583 := rs (se 1 (by rfl) ⟨28937, by rfl⟩) R57875
theorem R38603 : Reach 38603 := rs (se 1 (by rfl) ⟨28952, by rfl⟩) R57905
theorem R333517 : Reach 333517 := rs (se 3 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R38615 : Reach 38615 := rs (se 1 (by rfl) ⟨28961, by rfl⟩) R57923
theorem R38635 : Reach 38635 := rs (se 1 (by rfl) ⟨28976, by rfl⟩) R57953
theorem R38647 : Reach 38647 := rs (se 1 (by rfl) ⟨28985, by rfl⟩) R57971
theorem R71435 : Reach 71435 := rs (se 1 (by rfl) ⟨53576, by rfl⟩) R107153
theorem R38667 : Reach 38667 := rs (se 1 (by rfl) ⟨29000, by rfl⟩) R58001
theorem R38679 : Reach 38679 := rs (se 1 (by rfl) ⟨29009, by rfl⟩) R58019
theorem R38699 : Reach 38699 := rs (se 1 (by rfl) ⟨29024, by rfl⟩) R58049
theorem R38711 : Reach 38711 := rs (se 1 (by rfl) ⟨29033, by rfl⟩) R58067
theorem R202571 : Reach 202571 := rs (se 1 (by rfl) ⟨151928, by rfl⟩) R303857
theorem R38731 : Reach 38731 := rs (se 1 (by rfl) ⟨29048, by rfl⟩) R58097
theorem R38743 : Reach 38743 := rs (se 1 (by rfl) ⟨29057, by rfl⟩) R58115
theorem R38763 : Reach 38763 := rs (se 1 (by rfl) ⟨29072, by rfl⟩) R58145
theorem R38775 : Reach 38775 := rs (se 1 (by rfl) ⟨29081, by rfl⟩) R58163
theorem R38795 : Reach 38795 := rs (se 1 (by rfl) ⟨29096, by rfl⟩) R58193
theorem R38807 : Reach 38807 := rs (se 1 (by rfl) ⟨29105, by rfl⟩) R58211
theorem R38827 : Reach 38827 := rs (se 1 (by rfl) ⟨29120, by rfl⟩) R58241
theorem R38839 : Reach 38839 := rs (se 1 (by rfl) ⟨29129, by rfl⟩) R58259
theorem R71617 : Reach 71617 := rs (se 2 (by rfl) ⟨26856, by rfl⟩) R53713
theorem R38859 : Reach 38859 := rs (se 1 (by rfl) ⟨29144, by rfl⟩) R58289
theorem R38871 : Reach 38871 := rs (se 1 (by rfl) ⟨29153, by rfl⟩) R58307
theorem R38891 : Reach 38891 := rs (se 1 (by rfl) ⟨29168, by rfl⟩) R58337
theorem R38903 : Reach 38903 := rs (se 1 (by rfl) ⟨29177, by rfl⟩) R58355
theorem R38923 : Reach 38923 := rs (se 1 (by rfl) ⟨29192, by rfl⟩) R58385
theorem R38935 : Reach 38935 := rs (se 1 (by rfl) ⟨29201, by rfl⟩) R58403
theorem R38955 : Reach 38955 := rs (se 1 (by rfl) ⟨29216, by rfl⟩) R58433
theorem R38967 : Reach 38967 := rs (se 1 (by rfl) ⟨29225, by rfl⟩) R58451
theorem R38987 : Reach 38987 := rs (se 1 (by rfl) ⟨29240, by rfl⟩) R58481
theorem R38999 : Reach 38999 := rs (se 1 (by rfl) ⟨29249, by rfl⟩) R58499
theorem R39019 : Reach 39019 := rs (se 1 (by rfl) ⟨29264, by rfl⟩) R58529
theorem R39031 : Reach 39031 := rs (se 1 (by rfl) ⟨29273, by rfl⟩) R58547
theorem R39051 : Reach 39051 := rs (se 1 (by rfl) ⟨29288, by rfl⟩) R58577
theorem R39063 : Reach 39063 := rs (se 1 (by rfl) ⟨29297, by rfl⟩) R58595
theorem R39083 : Reach 39083 := rs (se 1 (by rfl) ⟨29312, by rfl⟩) R58625
theorem R137389 : Reach 137389 := rs (se 3 (by rfl) ⟨25760, by rfl⟩) R51521
theorem R39095 : Reach 39095 := rs (se 1 (by rfl) ⟨29321, by rfl⟩) R58643
theorem R39115 : Reach 39115 := rs (se 1 (by rfl) ⟨29336, by rfl⟩) R58673
theorem R661709 : Reach 661709 := rs (se 3 (by rfl) ⟨124070, by rfl⟩) R248141
theorem R39127 : Reach 39127 := rs (se 1 (by rfl) ⟨29345, by rfl⟩) R58691
theorem R72065 : Reach 72065 := rs (se 2 (by rfl) ⟨27024, by rfl⟩) R54049
theorem R137645 : Reach 137645 := rs (se 3 (by rfl) ⟨25808, by rfl⟩) R51617
theorem R268721 : Reach 268721 := rs (se 2 (by rfl) ⟨100770, by rfl⟩) R201541
theorem R137693 : Reach 137693 := rs (se 3 (by rfl) ⟨25817, by rfl⟩) R51635
theorem R203357 : Reach 203357 := rs (se 3 (by rfl) ⟨38129, by rfl⟩) R76259
theorem R39595 : Reach 39595 := rs (se 1 (by rfl) ⟨29696, by rfl⟩) R59393
theorem R72407 : Reach 72407 := rs (se 1 (by rfl) ⟨54305, by rfl⟩) R108611
theorem R105181 : Reach 105181 := rs (se 3 (by rfl) ⟨19721, by rfl⟩) R39443
theorem R39691 : Reach 39691 := rs (se 1 (by rfl) ⟨29768, by rfl⟩) R59537
theorem R39703 : Reach 39703 := rs (se 1 (by rfl) ⟨29777, by rfl⟩) R59555
theorem R105239 : Reach 105239 := rs (se 1 (by rfl) ⟨78929, by rfl⟩) R157859
theorem R39883 : Reach 39883 := rs (se 1 (by rfl) ⟨29912, by rfl⟩) R59825
theorem R39947 : Reach 39947 := rs (se 1 (by rfl) ⟨29960, by rfl⟩) R59921
theorem R269347 : Reach 269347 := rs (se 1 (by rfl) ⟨202010, by rfl⟩) R404021
theorem R39991 : Reach 39991 := rs (se 1 (by rfl) ⟨29993, by rfl⟩) R59987
theorem R302231 : Reach 302231 := rs (se 1 (by rfl) ⟨226673, by rfl⟩) R453347
theorem R138419 : Reach 138419 := rs (se 1 (by rfl) ⟨103814, by rfl⟩) R207629
theorem R40171 : Reach 40171 := rs (se 1 (by rfl) ⟨30128, by rfl⟩) R60257
theorem R40279 : Reach 40279 := rs (se 1 (by rfl) ⟨30209, by rfl⟩) R60419
theorem R73075 : Reach 73075 := rs (se 1 (by rfl) ⟨54806, by rfl⟩) R109613
theorem R73111 : Reach 73111 := rs (se 1 (by rfl) ⟨54833, by rfl⟩) R109667
theorem R40459 : Reach 40459 := rs (se 1 (by rfl) ⟨30344, by rfl⟩) R60689
theorem R40567 : Reach 40567 := rs (se 1 (by rfl) ⟨30425, by rfl⟩) R60851
theorem R73345 : Reach 73345 := rs (se 2 (by rfl) ⟨27504, by rfl⟩) R55009
theorem R40747 : Reach 40747 := rs (se 1 (by rfl) ⟨30560, by rfl⟩) R61121
theorem R73523 : Reach 73523 := rs (se 1 (by rfl) ⟨55142, by rfl⟩) R110285
theorem R73561 : Reach 73561 := rs (se 2 (by rfl) ⟨27585, by rfl⟩) R55171
theorem R40855 : Reach 40855 := rs (se 1 (by rfl) ⟨30641, by rfl⟩) R61283
theorem R41035 : Reach 41035 := rs (se 1 (by rfl) ⟨30776, by rfl⟩) R61553
theorem R106571 : Reach 106571 := rs (se 1 (by rfl) ⟨79928, by rfl⟩) R159857
theorem R41143 : Reach 41143 := rs (se 1 (by rfl) ⟨30857, by rfl⟩) R61715
theorem R41195 : Reach 41195 := rs (se 1 (by rfl) ⟨30896, by rfl⟩) R61793
theorem R74009 : Reach 74009 := rs (se 2 (by rfl) ⟨27753, by rfl⟩) R55507
theorem R172363 : Reach 172363 := rs (se 1 (by rfl) ⟨129272, by rfl⟩) R258545
theorem R172381 : Reach 172381 := rs (se 3 (by rfl) ⟨32321, by rfl⟩) R64643
theorem R41323 : Reach 41323 := rs (se 1 (by rfl) ⟨30992, by rfl⟩) R61985
theorem R41431 : Reach 41431 := rs (se 1 (by rfl) ⟨31073, by rfl⟩) R62147
theorem R139907 : Reach 139907 := rs (se 1 (by rfl) ⟨104930, by rfl⟩) R209861
theorem R41611 : Reach 41611 := rs (se 1 (by rfl) ⟨31208, by rfl⟩) R62417
theorem R139927 : Reach 139927 := rs (se 1 (by rfl) ⟨104945, by rfl⟩) R209891
theorem R172979 : Reach 172979 := rs (se 1 (by rfl) ⟨129734, by rfl⟩) R259469
theorem R42007 : Reach 42007 := rs (se 1 (by rfl) ⟨31505, by rfl⟩) R63011
theorem R140363 : Reach 140363 := rs (se 1 (by rfl) ⟨105272, by rfl⟩) R210545
theorem R205955 : Reach 205955 := rs (se 1 (by rfl) ⟨154466, by rfl⟩) R308933
theorem R42187 : Reach 42187 := rs (se 1 (by rfl) ⟨31640, by rfl⟩) R63281
theorem R140561 : Reach 140561 := rs (se 2 (by rfl) ⟨52710, by rfl⟩) R105421
theorem R75059 : Reach 75059 := rs (se 1 (by rfl) ⟨56294, by rfl⟩) R112589
theorem R42583 : Reach 42583 := rs (se 1 (by rfl) ⟨31937, by rfl⟩) R63875
theorem R108211 : Reach 108211 := rs (se 1 (by rfl) ⟨81158, by rfl⟩) R162317
theorem R42763 : Reach 42763 := rs (se 1 (by rfl) ⟨32072, by rfl⟩) R64145
theorem R75649 : Reach 75649 := rs (se 2 (by rfl) ⟨28368, by rfl⟩) R56737
theorem R337841 : Reach 337841 := rs (se 2 (by rfl) ⟨126690, by rfl⟩) R253381
theorem R141335 : Reach 141335 := rs (se 1 (by rfl) ⟨106001, by rfl⟩) R212003
theorem R43159 : Reach 43159 := rs (se 1 (by rfl) ⟨32369, by rfl⟩) R64739
theorem R75991 : Reach 75991 := rs (se 1 (by rfl) ⟨56993, by rfl⟩) R113987
theorem R141533 : Reach 141533 := rs (se 3 (by rfl) ⟨26537, by rfl⟩) R53075
theorem R272645 : Reach 272645 := rs (se 4 (by rfl) ⟨25560, by rfl⟩) R51121
theorem R76097 : Reach 76097 := rs (se 2 (by rfl) ⟨28536, by rfl⟩) R57073
theorem R43339 : Reach 43339 := rs (se 1 (by rfl) ⟨32504, by rfl⟩) R65009
theorem R207197 : Reach 207197 := rs (se 3 (by rfl) ⟨38849, by rfl⟩) R77699
theorem R174467 : Reach 174467 := rs (se 1 (by rfl) ⟨130850, by rfl⟩) R261701
theorem R272857 : Reach 272857 := rs (se 2 (by rfl) ⟨102321, by rfl⟩) R204643
theorem R76439 : Reach 76439 := rs (se 1 (by rfl) ⟨57329, by rfl⟩) R114659
theorem R109259 : Reach 109259 := rs (se 1 (by rfl) ⟨81944, by rfl⟩) R163889
theorem R43735 : Reach 43735 := rs (se 1 (by rfl) ⟨32801, by rfl⟩) R65603
theorem R43915 : Reach 43915 := rs (se 1 (by rfl) ⟨32936, by rfl⟩) R65873
theorem R76747 : Reach 76747 := rs (se 1 (by rfl) ⟨57560, by rfl⟩) R115121
theorem R207947 : Reach 207947 := rs (se 1 (by rfl) ⟨155960, by rfl⟩) R311921
theorem R437399 : Reach 437399 := rs (se 1 (by rfl) ⟨328049, by rfl⟩) R656099
theorem R175405 : Reach 175405 := rs (se 3 (by rfl) ⟨32888, by rfl⟩) R65777
theorem R634229 : Reach 634229 := rs (se 5 (by rfl) ⟨29729, by rfl⟩) R59459
theorem R77195 : Reach 77195 := rs (se 1 (by rfl) ⟨57896, by rfl⟩) R115793
theorem R241501 : Reach 241501 := rs (se 3 (by rfl) ⟨45281, by rfl⟩) R90563
theorem R77707 : Reach 77707 := rs (se 1 (by rfl) ⟨58280, by rfl⟩) R116561
theorem R143491 : Reach 143491 := rs (se 1 (by rfl) ⟨107618, by rfl⟩) R215237
theorem R241937 : Reach 241937 := rs (se 2 (by rfl) ⟨90726, by rfl⟩) R181453
theorem R110899 : Reach 110899 := rs (se 1 (by rfl) ⟨83174, by rfl⟩) R166349
theorem R45451 : Reach 45451 := rs (se 1 (by rfl) ⟨34088, by rfl⟩) R68177
theorem R143795 : Reach 143795 := rs (se 1 (by rfl) ⟨107846, by rfl⟩) R215693
theorem R111127 : Reach 111127 := rs (se 1 (by rfl) ⟨83345, by rfl⟩) R166691
theorem R111179 : Reach 111179 := rs (se 1 (by rfl) ⟨83384, by rfl⟩) R166769
theorem R78425 : Reach 78425 := rs (se 2 (by rfl) ⟨29409, by rfl⟩) R58819
theorem R569987 : Reach 569987 := rs (se 1 (by rfl) ⟨427490, by rfl⟩) R854981
theorem R275075 : Reach 275075 := rs (se 1 (by rfl) ⟨206306, by rfl⟩) R412613
theorem R209587 : Reach 209587 := rs (se 1 (by rfl) ⟨157190, by rfl⟩) R314381
theorem R635633 : Reach 635633 := rs (se 2 (by rfl) ⟨238362, by rfl⟩) R476725
theorem R635825 : Reach 635825 := rs (se 2 (by rfl) ⟨238434, by rfl⟩) R476869
theorem R78835 : Reach 78835 := rs (se 1 (by rfl) ⟨59126, by rfl⟩) R118253
theorem R144449 : Reach 144449 := rs (se 2 (by rfl) ⟨54168, by rfl⟩) R108337
theorem R79091 : Reach 79091 := rs (se 1 (by rfl) ⟨59318, by rfl⟩) R118637
theorem R79127 : Reach 79127 := rs (se 1 (by rfl) ⟨59345, by rfl⟩) R118691
theorem R46423 : Reach 46423 := rs (se 1 (by rfl) ⟨34817, by rfl⟩) R69635
theorem R406885 : Reach 406885 := rs (se 4 (by rfl) ⟨38145, by rfl⟩) R76291
theorem R79307 : Reach 79307 := rs (se 1 (by rfl) ⟨59480, by rfl⟩) R118961
theorem R79361 : Reach 79361 := rs (se 2 (by rfl) ⟨29760, by rfl⟩) R59521
theorem R79577 : Reach 79577 := rs (se 2 (by rfl) ⟨29841, by rfl⟩) R59683
theorem R341765 : Reach 341765 := rs (se 4 (by rfl) ⟨32040, by rfl⟩) R64081
theorem R79667 : Reach 79667 := rs (se 1 (by rfl) ⟨59750, by rfl⟩) R119501
theorem R79703 : Reach 79703 := rs (se 1 (by rfl) ⟨59777, by rfl⟩) R119555
theorem R79883 : Reach 79883 := rs (se 1 (by rfl) ⟨59912, by rfl⟩) R119825
theorem R112691 : Reach 112691 := rs (se 1 (by rfl) ⟨84518, by rfl⟩) R169037
theorem R79937 : Reach 79937 := rs (se 2 (by rfl) ⟨29976, by rfl⟩) R59953
theorem R1882187 : Reach 1882187 := rs (se 1 (by rfl) ⟨1411640, by rfl⟩) R2823281
theorem R211045 : Reach 211045 := rs (se 4 (by rfl) ⟨19785, by rfl⟩) R39571
theorem R47243 : Reach 47243 := rs (se 1 (by rfl) ⟨35432, by rfl⟩) R70865
theorem R80023 : Reach 80023 := rs (se 1 (by rfl) ⟨60017, by rfl⟩) R120035
theorem R80065 : Reach 80065 := rs (se 2 (by rfl) ⟨30024, by rfl⟩) R60049
theorem R80153 : Reach 80153 := rs (se 2 (by rfl) ⟨30057, by rfl⟩) R60115
theorem R145709 : Reach 145709 := rs (se 3 (by rfl) ⟨27320, by rfl⟩) R54641
theorem R145739 : Reach 145739 := rs (se 1 (by rfl) ⟨109304, by rfl⟩) R218609
theorem R80243 : Reach 80243 := rs (se 1 (by rfl) ⟨60182, by rfl⟩) R120365
theorem R80279 : Reach 80279 := rs (se 1 (by rfl) ⟨60209, by rfl⟩) R120419
theorem R47639 : Reach 47639 := rs (se 1 (by rfl) ⟨35729, by rfl⟩) R71459
theorem R80459 : Reach 80459 := rs (se 1 (by rfl) ⟨60344, by rfl⟩) R120689
theorem R80513 : Reach 80513 := rs (se 2 (by rfl) ⟨30192, by rfl⟩) R60385
theorem R179009 : Reach 179009 := rs (se 2 (by rfl) ⟨67128, by rfl⟩) R134257
theorem R47947 : Reach 47947 := rs (se 1 (by rfl) ⟨35960, by rfl⟩) R71921
theorem R80729 : Reach 80729 := rs (se 2 (by rfl) ⟨30273, by rfl⟩) R60547
theorem R80819 : Reach 80819 := rs (se 1 (by rfl) ⟨60614, by rfl⟩) R121229
theorem R80855 : Reach 80855 := rs (se 1 (by rfl) ⟨60641, by rfl⟩) R121283
theorem R146393 : Reach 146393 := rs (se 2 (by rfl) ⟨54897, by rfl⟩) R109795
theorem R48151 : Reach 48151 := rs (se 1 (by rfl) ⟨36113, by rfl⟩) R72227
theorem R48215 : Reach 48215 := rs (se 1 (by rfl) ⟨36161, by rfl⟩) R72323
theorem R81035 : Reach 81035 := rs (se 1 (by rfl) ⟨60776, by rfl⟩) R121553
theorem R81089 : Reach 81089 := rs (se 2 (by rfl) ⟨30408, by rfl⟩) R60817
theorem R146711 : Reach 146711 := rs (se 1 (by rfl) ⟨110033, by rfl⟩) R220067
theorem R146777 : Reach 146777 := rs (se 2 (by rfl) ⟨55041, by rfl⟩) R110083
theorem R81305 : Reach 81305 := rs (se 2 (by rfl) ⟨30489, by rfl⟩) R60979
theorem R81395 : Reach 81395 := rs (se 1 (by rfl) ⟨61046, by rfl⟩) R122093
theorem R81431 : Reach 81431 := rs (se 1 (by rfl) ⟨61073, by rfl⟩) R122147
theorem R81611 : Reach 81611 := rs (se 1 (by rfl) ⟨61208, by rfl⟩) R122417
theorem R81665 : Reach 81665 := rs (se 2 (by rfl) ⟨30624, by rfl⟩) R61249
theorem R147203 : Reach 147203 := rs (se 1 (by rfl) ⟨110402, by rfl⟩) R220805
theorem R48919 : Reach 48919 := rs (se 1 (by rfl) ⟨36689, by rfl⟩) R73379
theorem R81739 : Reach 81739 := rs (se 1 (by rfl) ⟨61304, by rfl⟩) R122609
theorem R147379 : Reach 147379 := rs (se 1 (by rfl) ⟨110534, by rfl⟩) R221069
theorem R278477 : Reach 278477 := rs (se 3 (by rfl) ⟨52214, by rfl⟩) R104429
theorem R81881 : Reach 81881 := rs (se 2 (by rfl) ⟨30705, by rfl⟩) R61411
theorem R49177 : Reach 49177 := rs (se 2 (by rfl) ⟨18441, by rfl⟩) R36883
theorem R81971 : Reach 81971 := rs (se 1 (by rfl) ⟨61478, by rfl⟩) R122957
theorem R82007 : Reach 82007 := rs (se 1 (by rfl) ⟨61505, by rfl⟩) R123011
theorem R147545 : Reach 147545 := rs (se 2 (by rfl) ⟨55329, by rfl⟩) R110659
theorem R82073 : Reach 82073 := rs (se 2 (by rfl) ⟨30777, by rfl⟩) R61555
theorem R82187 : Reach 82187 := rs (se 1 (by rfl) ⟨61640, by rfl⟩) R123281
theorem R82241 : Reach 82241 := rs (se 2 (by rfl) ⟨30840, by rfl⟩) R61681
theorem R278963 : Reach 278963 := rs (se 1 (by rfl) ⟨209222, by rfl⟩) R418445
theorem R82457 : Reach 82457 := rs (se 2 (by rfl) ⟨30921, by rfl⟩) R61843
theorem R246347 : Reach 246347 := rs (se 1 (by rfl) ⟨184760, by rfl⟩) R369521
theorem R1065565 : Reach 1065565 := rs (se 3 (by rfl) ⟨199793, by rfl⟩) R399587
theorem R82547 : Reach 82547 := rs (se 1 (by rfl) ⟨61910, by rfl⟩) R123821
theorem R82583 : Reach 82583 := rs (se 1 (by rfl) ⟨61937, by rfl⟩) R123875
theorem R180953 : Reach 180953 := rs (se 2 (by rfl) ⟨67857, by rfl⟩) R135715
theorem R82763 : Reach 82763 := rs (se 1 (by rfl) ⟨62072, by rfl⟩) R124145
theorem R279389 : Reach 279389 := rs (se 3 (by rfl) ⟨52385, by rfl⟩) R104771
theorem R82817 : Reach 82817 := rs (se 2 (by rfl) ⟨31056, by rfl⟩) R62113
theorem R115763 : Reach 115763 := rs (se 1 (by rfl) ⟨86822, by rfl⟩) R173645
theorem R83033 : Reach 83033 := rs (se 2 (by rfl) ⟨31137, by rfl⟩) R62275
theorem R1033357 : Reach 1033357 := rs (se 3 (by rfl) ⟨193754, by rfl⟩) R387509
theorem R83123 : Reach 83123 := rs (se 1 (by rfl) ⟨62342, by rfl⟩) R124685
theorem R83159 : Reach 83159 := rs (se 1 (by rfl) ⟨62369, by rfl⟩) R124739
theorem R83393 : Reach 83393 := rs (se 2 (by rfl) ⟨31272, by rfl⟩) R62545
theorem R50711 : Reach 50711 := rs (se 1 (by rfl) ⟨38033, by rfl⟩) R76067
theorem R771677 : Reach 771677 := rs (se 3 (by rfl) ⟨144689, by rfl⟩) R289379
theorem R312983 : Reach 312983 := rs (se 1 (by rfl) ⟨234737, by rfl⟩) R469475
theorem R50905 : Reach 50905 := rs (se 2 (by rfl) ⟨19089, by rfl⟩) R38179
theorem R607985 : Reach 607985 := rs (se 2 (by rfl) ⟨227994, by rfl⟩) R455989
theorem R83735 : Reach 83735 := rs (se 1 (by rfl) ⟨62801, by rfl⟩) R125603
theorem R280421 : Reach 280421 := rs (se 4 (by rfl) ⟨26289, by rfl⟩) R52579
theorem R83915 : Reach 83915 := rs (se 1 (by rfl) ⟨62936, by rfl⟩) R125873
theorem R247901 : Reach 247901 := rs (se 3 (by rfl) ⟨46481, by rfl⟩) R92963
theorem R84185 : Reach 84185 := rs (se 2 (by rfl) ⟨31569, by rfl⟩) R63139
theorem R182573 : Reach 182573 := rs (se 3 (by rfl) ⟨34232, by rfl⟩) R68465
theorem R84275 : Reach 84275 := rs (se 1 (by rfl) ⟨63206, by rfl⟩) R126413
theorem R280907 : Reach 280907 := rs (se 1 (by rfl) ⟨210680, by rfl⟩) R421361
theorem R444851 : Reach 444851 := rs (se 1 (by rfl) ⟨333638, by rfl⟩) R667277
theorem R84545 : Reach 84545 := rs (se 2 (by rfl) ⟨31704, by rfl⟩) R63409
theorem R84887 : Reach 84887 := rs (se 1 (by rfl) ⟨63665, by rfl⟩) R127331
theorem R150493 : Reach 150493 := rs (se 3 (by rfl) ⟨28217, by rfl⟩) R56435
theorem R85067 : Reach 85067 := rs (se 1 (by rfl) ⟨63800, by rfl⟩) R127601
theorem R52363 : Reach 52363 := rs (se 1 (by rfl) ⟨39272, by rfl⟩) R78545
theorem R150835 : Reach 150835 := rs (se 1 (by rfl) ⟨113126, by rfl⟩) R226253
theorem R85337 : Reach 85337 := rs (se 2 (by rfl) ⟨32001, by rfl⟩) R64003
theorem R85427 : Reach 85427 := rs (se 1 (by rfl) ⟨64070, by rfl⟩) R128141
theorem R52697 : Reach 52697 := rs (se 2 (by rfl) ⟨19761, by rfl⟩) R39523
theorem R52811 : Reach 52811 := rs (se 1 (by rfl) ⟨39608, by rfl⟩) R79217
theorem R52823 : Reach 52823 := rs (se 1 (by rfl) ⟨39617, by rfl⟩) R79235
theorem R52889 : Reach 52889 := rs (se 2 (by rfl) ⟨19833, by rfl⟩) R39667
theorem R216755 : Reach 216755 := rs (se 1 (by rfl) ⟨162566, by rfl⟩) R325133
theorem R85697 : Reach 85697 := rs (se 2 (by rfl) ⟨32136, by rfl⟩) R64273
theorem R53003 : Reach 53003 := rs (se 1 (by rfl) ⟨39752, by rfl⟩) R79505
theorem R53015 : Reach 53015 := rs (se 1 (by rfl) ⟨39761, by rfl⟩) R79523
theorem R216877 : Reach 216877 := rs (se 3 (by rfl) ⟨40664, by rfl⟩) R81329
theorem R53081 : Reach 53081 := rs (se 2 (by rfl) ⟨19905, by rfl⟩) R39811
theorem R53195 : Reach 53195 := rs (se 1 (by rfl) ⟨39896, by rfl⟩) R79793
theorem R53207 : Reach 53207 := rs (se 1 (by rfl) ⟨39905, by rfl⟩) R79811
theorem R118745 : Reach 118745 := rs (se 2 (by rfl) ⟨44529, by rfl⟩) R89059
theorem R86039 : Reach 86039 := rs (se 1 (by rfl) ⟨64529, by rfl⟩) R129059
theorem R53273 : Reach 53273 := rs (se 2 (by rfl) ⟨19977, by rfl⟩) R39955
theorem R53387 : Reach 53387 := rs (se 1 (by rfl) ⟨40040, by rfl⟩) R80081
theorem R53399 : Reach 53399 := rs (se 1 (by rfl) ⟨40049, by rfl⟩) R80099
theorem R86219 : Reach 86219 := rs (se 1 (by rfl) ⟨64664, by rfl⟩) R129329
theorem R53465 : Reach 53465 := rs (se 2 (by rfl) ⟨20049, by rfl⟩) R40099
theorem R53579 : Reach 53579 := rs (se 1 (by rfl) ⟨40184, by rfl⟩) R80369
theorem R53591 : Reach 53591 := rs (se 1 (by rfl) ⟨40193, by rfl⟩) R80387
theorem R53657 : Reach 53657 := rs (se 2 (by rfl) ⟨20121, by rfl⟩) R40243
theorem R86489 : Reach 86489 := rs (se 2 (by rfl) ⟨32433, by rfl⟩) R64867
theorem R53771 : Reach 53771 := rs (se 1 (by rfl) ⟨40328, by rfl⟩) R80657
theorem R1921553 : Reach 1921553 := rs (se 2 (by rfl) ⟨720582, by rfl⟩) R1441165
theorem R53783 : Reach 53783 := rs (se 1 (by rfl) ⟨40337, by rfl⟩) R80675
theorem R86579 : Reach 86579 := rs (se 1 (by rfl) ⟨64934, by rfl⟩) R129869
theorem R53849 : Reach 53849 := rs (se 2 (by rfl) ⟨20193, by rfl⟩) R40387
theorem R119447 : Reach 119447 := rs (se 1 (by rfl) ⟨89585, by rfl⟩) R179171
theorem R53963 : Reach 53963 := rs (se 1 (by rfl) ⟨40472, by rfl⟩) R80945
theorem R53975 : Reach 53975 := rs (se 1 (by rfl) ⟨40481, by rfl⟩) R80963
theorem R54041 : Reach 54041 := rs (se 2 (by rfl) ⟨20265, by rfl⟩) R40531
theorem R86849 : Reach 86849 := rs (se 2 (by rfl) ⟨32568, by rfl⟩) R65137
theorem R54155 : Reach 54155 := rs (se 1 (by rfl) ⟨40616, by rfl⟩) R81233
theorem R54167 : Reach 54167 := rs (se 1 (by rfl) ⟨40625, by rfl⟩) R81251
theorem R54233 : Reach 54233 := rs (se 2 (by rfl) ⟨20337, by rfl⟩) R40675
theorem R54347 : Reach 54347 := rs (se 1 (by rfl) ⟨40760, by rfl⟩) R81521
theorem R54359 : Reach 54359 := rs (se 1 (by rfl) ⟨40769, by rfl⟩) R81539
theorem R87191 : Reach 87191 := rs (se 1 (by rfl) ⟨65393, by rfl⟩) R130787
theorem R54425 : Reach 54425 := rs (se 2 (by rfl) ⟨20409, by rfl⟩) R40819
theorem R119987 : Reach 119987 := rs (se 1 (by rfl) ⟨89990, by rfl⟩) R179981
theorem R251059 : Reach 251059 := rs (se 1 (by rfl) ⟨188294, by rfl⟩) R376589
theorem R54539 : Reach 54539 := rs (se 1 (by rfl) ⟨40904, by rfl⟩) R81809
theorem R54551 : Reach 54551 := rs (se 1 (by rfl) ⟨40913, by rfl⟩) R81827
theorem R185645 : Reach 185645 := rs (se 3 (by rfl) ⟨34808, by rfl⟩) R69617
theorem R87371 : Reach 87371 := rs (se 1 (by rfl) ⟨65528, by rfl⟩) R131057
theorem R54617 : Reach 54617 := rs (se 2 (by rfl) ⟨20481, by rfl⟩) R40963
theorem R1037717 : Reach 1037717 := rs (se 6 (by rfl) ⟨24321, by rfl⟩) R48643
theorem R120257 : Reach 120257 := rs (se 2 (by rfl) ⟨45096, by rfl⟩) R90193
theorem R54731 : Reach 54731 := rs (se 1 (by rfl) ⟨41048, by rfl⟩) R82097
theorem R54743 : Reach 54743 := rs (se 1 (by rfl) ⟨41057, by rfl⟩) R82115
theorem R54809 : Reach 54809 := rs (se 2 (by rfl) ⟨20553, by rfl⟩) R41107
theorem R54859 : Reach 54859 := rs (se 1 (by rfl) ⟨41144, by rfl⟩) R82289
theorem R87641 : Reach 87641 := rs (se 2 (by rfl) ⟨32865, by rfl⟩) R65731
theorem R54923 : Reach 54923 := rs (se 1 (by rfl) ⟨41192, by rfl⟩) R82385
theorem R54935 : Reach 54935 := rs (se 1 (by rfl) ⟨41201, by rfl⟩) R82403
theorem R87731 : Reach 87731 := rs (se 1 (by rfl) ⟨65798, by rfl⟩) R131597
theorem R55001 : Reach 55001 := rs (se 2 (by rfl) ⟨20625, by rfl⟩) R41251
theorem R153361 : Reach 153361 := rs (se 2 (by rfl) ⟨57510, by rfl⟩) R115021
theorem R55115 : Reach 55115 := rs (se 1 (by rfl) ⟨41336, by rfl⟩) R82673
theorem R55127 : Reach 55127 := rs (se 1 (by rfl) ⟨41345, by rfl⟩) R82691
theorem R55193 : Reach 55193 := rs (se 2 (by rfl) ⟨20697, by rfl⟩) R41395
theorem R88001 : Reach 88001 := rs (se 2 (by rfl) ⟨33000, by rfl⟩) R66001
theorem R120797 : Reach 120797 := rs (se 3 (by rfl) ⟨22649, by rfl⟩) R45299
theorem R55307 : Reach 55307 := rs (se 1 (by rfl) ⟨41480, by rfl⟩) R82961
theorem R55319 : Reach 55319 := rs (se 1 (by rfl) ⟨41489, by rfl⟩) R82979
theorem R55385 : Reach 55385 := rs (se 2 (by rfl) ⟨20769, by rfl⟩) R41539
theorem R186461 : Reach 186461 := rs (se 3 (by rfl) ⟨34961, by rfl⟩) R69923
theorem R153751 : Reach 153751 := rs (se 1 (by rfl) ⟨115313, by rfl⟩) R230627
theorem R55499 : Reach 55499 := rs (se 1 (by rfl) ⟨41624, by rfl⟩) R83249
theorem R55511 : Reach 55511 := rs (se 1 (by rfl) ⟨41633, by rfl⟩) R83267
theorem R55577 : Reach 55577 := rs (se 2 (by rfl) ⟨20841, by rfl⟩) R41683
theorem R55691 : Reach 55691 := rs (se 1 (by rfl) ⟨41768, by rfl⟩) R83537
theorem R55703 : Reach 55703 := rs (se 1 (by rfl) ⟨41777, by rfl⟩) R83555
theorem R55769 : Reach 55769 := rs (se 2 (by rfl) ⟨20913, by rfl⟩) R41827
theorem R88651 : Reach 88651 := rs (se 1 (by rfl) ⟨66488, by rfl⟩) R132977
theorem R55883 : Reach 55883 := rs (se 1 (by rfl) ⟨41912, by rfl⟩) R83825
theorem R55895 : Reach 55895 := rs (se 1 (by rfl) ⟨41921, by rfl⟩) R83843
theorem R55961 : Reach 55961 := rs (se 2 (by rfl) ⟨20985, by rfl⟩) R41971
theorem R56075 : Reach 56075 := rs (se 1 (by rfl) ⟨42056, by rfl⟩) R84113
theorem R56087 : Reach 56087 := rs (se 1 (by rfl) ⟨42065, by rfl⟩) R84131
theorem R88897 : Reach 88897 := rs (se 2 (by rfl) ⟨33336, by rfl⟩) R66673
theorem R187201 : Reach 187201 := rs (se 2 (by rfl) ⟨70200, by rfl⟩) R140401
theorem R121675 : Reach 121675 := rs (se 1 (by rfl) ⟨91256, by rfl⟩) R182513
theorem R187211 : Reach 187211 := rs (se 1 (by rfl) ⟨140408, by rfl⟩) R280817
theorem R154457 : Reach 154457 := rs (se 2 (by rfl) ⟨57921, by rfl⟩) R115843
theorem R56153 : Reach 56153 := rs (se 2 (by rfl) ⟨21057, by rfl⟩) R42115
theorem R56267 : Reach 56267 := rs (se 1 (by rfl) ⟨42200, by rfl⟩) R84401
theorem R56279 : Reach 56279 := rs (se 1 (by rfl) ⟨42209, by rfl⟩) R84419
theorem R56345 : Reach 56345 := rs (se 2 (by rfl) ⟨21129, by rfl⟩) R42259
theorem R121931 : Reach 121931 := rs (se 1 (by rfl) ⟨91448, by rfl⟩) R182897
theorem R56459 : Reach 56459 := rs (se 1 (by rfl) ⟨42344, by rfl⟩) R84689
theorem R679063 : Reach 679063 := rs (se 1 (by rfl) ⟨509297, by rfl⟩) R1018595
theorem R56471 : Reach 56471 := rs (se 1 (by rfl) ⟨42353, by rfl⟩) R84707
theorem R56537 : Reach 56537 := rs (se 2 (by rfl) ⟨21201, by rfl⟩) R42403
theorem R318755 : Reach 318755 := rs (se 1 (by rfl) ⟨239066, by rfl⟩) R478133
theorem R56651 : Reach 56651 := rs (se 1 (by rfl) ⟨42488, by rfl⟩) R84977
theorem R56663 : Reach 56663 := rs (se 1 (by rfl) ⟨42497, by rfl⟩) R84995
theorem R122201 : Reach 122201 := rs (se 2 (by rfl) ⟨45825, by rfl⟩) R91651
theorem R89495 : Reach 89495 := rs (se 1 (by rfl) ⟨67121, by rfl⟩) R134243
theorem R56729 : Reach 56729 := rs (se 2 (by rfl) ⟨21273, by rfl⟩) R42547
theorem R56843 : Reach 56843 := rs (se 1 (by rfl) ⟨42632, by rfl⟩) R85265
theorem R56855 : Reach 56855 := rs (se 1 (by rfl) ⟨42641, by rfl⟩) R85283
theorem R286253 : Reach 286253 := rs (se 3 (by rfl) ⟨53672, by rfl⟩) R107345
theorem R56921 : Reach 56921 := rs (se 2 (by rfl) ⟨21345, by rfl⟩) R42691
theorem R57035 : Reach 57035 := rs (se 1 (by rfl) ⟨42776, by rfl⟩) R85553
theorem R57047 : Reach 57047 := rs (se 1 (by rfl) ⟨42785, by rfl⟩) R85571
theorem R57113 : Reach 57113 := rs (se 2 (by rfl) ⟨21417, by rfl⟩) R42835
theorem R57227 : Reach 57227 := rs (se 1 (by rfl) ⟨42920, by rfl⟩) R85841
theorem R57239 : Reach 57239 := rs (se 1 (by rfl) ⟨42929, by rfl⟩) R85859
theorem R57305 : Reach 57305 := rs (se 2 (by rfl) ⟨21489, by rfl⟩) R42979
theorem R122903 : Reach 122903 := rs (se 1 (by rfl) ⟨92177, by rfl⟩) R184355
theorem R57419 : Reach 57419 := rs (se 1 (by rfl) ⟨43064, by rfl⟩) R86129
theorem R57431 : Reach 57431 := rs (se 1 (by rfl) ⟨43073, by rfl⟩) R86147
theorem R188567 : Reach 188567 := rs (se 1 (by rfl) ⟨141425, by rfl⟩) R282851
theorem R57497 : Reach 57497 := rs (se 2 (by rfl) ⟨21561, by rfl⟩) R43123
theorem R90305 : Reach 90305 := rs (se 2 (by rfl) ⟨33864, by rfl⟩) R67729
theorem R57611 : Reach 57611 := rs (se 1 (by rfl) ⟨43208, by rfl⟩) R86417
theorem R90391 : Reach 90391 := rs (se 1 (by rfl) ⟨67793, by rfl⟩) R135587
theorem R57623 : Reach 57623 := rs (se 1 (by rfl) ⟨43217, by rfl⟩) R86435
theorem R57689 : Reach 57689 := rs (se 2 (by rfl) ⟨21633, by rfl⟩) R43267
theorem R156097 : Reach 156097 := rs (se 2 (by rfl) ⟨58536, by rfl⟩) R117073
theorem R57803 : Reach 57803 := rs (se 1 (by rfl) ⟨43352, by rfl⟩) R86705
theorem R57815 : Reach 57815 := rs (se 1 (by rfl) ⟨43361, by rfl⟩) R86723
theorem R123353 : Reach 123353 := rs (se 2 (by rfl) ⟨46257, by rfl⟩) R92515
theorem R57881 : Reach 57881 := rs (se 2 (by rfl) ⟨21705, by rfl⟩) R43411
theorem R123443 : Reach 123443 := rs (se 1 (by rfl) ⟨92582, by rfl⟩) R185165
theorem R57995 : Reach 57995 := rs (se 1 (by rfl) ⟨43496, by rfl⟩) R86993
theorem R58007 : Reach 58007 := rs (se 1 (by rfl) ⟨43505, by rfl⟩) R87011
theorem R90841 : Reach 90841 := rs (se 2 (by rfl) ⟨34065, by rfl⟩) R68131
theorem R58073 : Reach 58073 := rs (se 2 (by rfl) ⟨21777, by rfl⟩) R43555
theorem R123713 : Reach 123713 := rs (se 2 (by rfl) ⟨46392, by rfl⟩) R92785
theorem R58187 : Reach 58187 := rs (se 1 (by rfl) ⟨43640, by rfl⟩) R87281
theorem R58199 : Reach 58199 := rs (se 1 (by rfl) ⟨43649, by rfl⟩) R87299
theorem R58265 : Reach 58265 := rs (se 2 (by rfl) ⟨21849, by rfl⟩) R43699
theorem R58315 : Reach 58315 := rs (se 1 (by rfl) ⟨43736, by rfl⟩) R87473
theorem R58379 : Reach 58379 := rs (se 1 (by rfl) ⟨43784, by rfl⟩) R87569
theorem R58391 : Reach 58391 := rs (se 1 (by rfl) ⟨43793, by rfl⟩) R87587
theorem R58457 : Reach 58457 := rs (se 2 (by rfl) ⟨21921, by rfl⟩) R43843
theorem R58571 : Reach 58571 := rs (se 1 (by rfl) ⟨43928, by rfl⟩) R87857
theorem R58583 : Reach 58583 := rs (se 1 (by rfl) ⟨43937, by rfl⟩) R87875
theorem R58649 : Reach 58649 := rs (se 2 (by rfl) ⟨21993, by rfl⟩) R43987
theorem R124249 : Reach 124249 := rs (se 2 (by rfl) ⟨46593, by rfl⟩) R93187
theorem R124253 : Reach 124253 := rs (se 3 (by rfl) ⟨23297, by rfl⟩) R46595
theorem R124363 : Reach 124363 := rs (se 1 (by rfl) ⟨93272, by rfl⟩) R186545
theorem R91955 : Reach 91955 := rs (se 1 (by rfl) ⟨68966, by rfl⟩) R137933
theorem R157585 : Reach 157585 := rs (se 2 (by rfl) ⟨59094, by rfl⟩) R118189
theorem R124865 : Reach 124865 := rs (se 2 (by rfl) ⟨46824, by rfl⟩) R93649
theorem R59339 : Reach 59339 := rs (se 1 (by rfl) ⟨44504, by rfl⟩) R89009
theorem R124993 : Reach 124993 := rs (se 2 (by rfl) ⟨46872, by rfl⟩) R93745
theorem R59467 : Reach 59467 := rs (se 1 (by rfl) ⟨44600, by rfl⟩) R89201
theorem R92249 : Reach 92249 := rs (se 2 (by rfl) ⟨34593, by rfl⟩) R69187
theorem R583861 : Reach 583861 := rs (se 5 (by rfl) ⟨27368, by rfl⟩) R54737
theorem R157889 : Reach 157889 := rs (se 2 (by rfl) ⟨59208, by rfl⟩) R118417
theorem R59609 : Reach 59609 := rs (se 2 (by rfl) ⟨22353, by rfl⟩) R44707
theorem R59737 : Reach 59737 := rs (se 2 (by rfl) ⟨22401, by rfl⟩) R44803
theorem R92609 : Reach 92609 := rs (se 2 (by rfl) ⟨34728, by rfl⟩) R69457
theorem R125387 : Reach 125387 := rs (se 1 (by rfl) ⟨94040, by rfl⟩) R188081
theorem R59915 : Reach 59915 := rs (se 1 (by rfl) ⟨44936, by rfl⟩) R89873
theorem R125657 : Reach 125657 := rs (se 2 (by rfl) ⟨47121, by rfl⟩) R94243
theorem R322379 : Reach 322379 := rs (se 1 (by rfl) ⟨241784, by rfl⟩) R483569
theorem R60311 : Reach 60311 := rs (se 1 (by rfl) ⟨45233, by rfl⟩) R90467
theorem R93079 : Reach 93079 := rs (se 1 (by rfl) ⟨69809, by rfl⟩) R139619
theorem R60439 : Reach 60439 := rs (se 1 (by rfl) ⟨45329, by rfl⟩) R90659
theorem R224407 : Reach 224407 := rs (se 1 (by rfl) ⟨168305, by rfl⟩) R336611
theorem R290141 : Reach 290141 := rs (se 3 (by rfl) ⟨54401, by rfl⟩) R108803
theorem R126353 : Reach 126353 := rs (se 2 (by rfl) ⟨47382, by rfl⟩) R94765
theorem R126359 : Reach 126359 := rs (se 1 (by rfl) ⟨94769, by rfl⟩) R189539
theorem R126467 : Reach 126467 := rs (se 1 (by rfl) ⟨94850, by rfl⟩) R189701
theorem R585251 : Reach 585251 := rs (se 1 (by rfl) ⟨438938, by rfl⟩) R877877
theorem R192131 : Reach 192131 := rs (se 1 (by rfl) ⟨144098, by rfl⟩) R288197
theorem R61067 : Reach 61067 := rs (se 1 (by rfl) ⟨45800, by rfl⟩) R91601
theorem R93889 : Reach 93889 := rs (se 2 (by rfl) ⟨35208, by rfl⟩) R70417
theorem R93899 : Reach 93899 := rs (se 1 (by rfl) ⟨70424, by rfl⟩) R140849
theorem R454349 : Reach 454349 := rs (se 3 (by rfl) ⟨85190, by rfl⟩) R170381
theorem R61195 : Reach 61195 := rs (se 1 (by rfl) ⟨45896, by rfl⟩) R91793
theorem R126737 : Reach 126737 := rs (se 2 (by rfl) ⟨47526, by rfl⟩) R95053
theorem R225125 : Reach 225125 := rs (se 4 (by rfl) ⟨21105, by rfl⟩) R42211
theorem R61337 : Reach 61337 := rs (se 2 (by rfl) ⟨23001, by rfl⟩) R46003
theorem R126899 : Reach 126899 := rs (se 1 (by rfl) ⟨95174, by rfl⟩) R190349
theorem R126937 : Reach 126937 := rs (se 2 (by rfl) ⟨47601, by rfl⟩) R95203
theorem R61465 : Reach 61465 := rs (se 2 (by rfl) ⟨23049, by rfl⟩) R46099
theorem R258227 : Reach 258227 := rs (se 1 (by rfl) ⟨193670, by rfl⟩) R387341
theorem R127169 : Reach 127169 := rs (se 2 (by rfl) ⟨47688, by rfl⟩) R95377
theorem R127277 : Reach 127277 := rs (se 3 (by rfl) ⟨23864, by rfl⟩) R47729
theorem R62039 : Reach 62039 := rs (se 1 (by rfl) ⟨46529, by rfl⟩) R93059
theorem R94871 : Reach 94871 := rs (se 1 (by rfl) ⟨71153, by rfl⟩) R142307
theorem R62155 : Reach 62155 := rs (se 1 (by rfl) ⟨46616, by rfl⟩) R93233
theorem R62167 : Reach 62167 := rs (se 1 (by rfl) ⟨46625, by rfl⟩) R93251
theorem R291545 : Reach 291545 := rs (se 2 (by rfl) ⟨109329, by rfl⟩) R218659
theorem R127709 : Reach 127709 := rs (se 3 (by rfl) ⟨23945, by rfl⟩) R47891
theorem R160643 : Reach 160643 := rs (se 1 (by rfl) ⟨120482, by rfl⟩) R240965
theorem R127889 : Reach 127889 := rs (se 2 (by rfl) ⟨47958, by rfl⟩) R95917
theorem R488369 : Reach 488369 := rs (se 2 (by rfl) ⟨183138, by rfl⟩) R366277
theorem R128017 : Reach 128017 := rs (se 2 (by rfl) ⟨48006, by rfl⟩) R96013
theorem R95321 : Reach 95321 := rs (se 2 (by rfl) ⟨35745, by rfl⟩) R71491
theorem R62579 : Reach 62579 := rs (se 1 (by rfl) ⟨46934, by rfl⟩) R93869
theorem R62707 : Reach 62707 := rs (se 1 (by rfl) ⟨47030, by rfl⟩) R94061
theorem R161041 : Reach 161041 := rs (se 2 (by rfl) ⟨60390, by rfl⟩) R120781
theorem R95539 : Reach 95539 := rs (se 1 (by rfl) ⟨71654, by rfl⟩) R143309
theorem R62795 : Reach 62795 := rs (se 1 (by rfl) ⟨47096, by rfl⟩) R94193
theorem R62849 : Reach 62849 := rs (se 2 (by rfl) ⟨23568, by rfl⟩) R47137
theorem R325043 : Reach 325043 := rs (se 1 (by rfl) ⟨243782, by rfl⟩) R487565
theorem R95681 : Reach 95681 := rs (se 2 (by rfl) ⟨35880, by rfl⟩) R71761
theorem R62923 : Reach 62923 := rs (se 1 (by rfl) ⟨47192, by rfl⟩) R94385
theorem R62977 : Reach 62977 := rs (se 2 (by rfl) ⟨23616, by rfl⟩) R47233
theorem R63065 : Reach 63065 := rs (se 2 (by rfl) ⟨23649, by rfl⟩) R47299
theorem R718429 : Reach 718429 := rs (se 3 (by rfl) ⟨134705, by rfl⟩) R269411
theorem R63193 : Reach 63193 := rs (se 2 (by rfl) ⟨23697, by rfl⟩) R47395
theorem R128843 : Reach 128843 := rs (se 1 (by rfl) ⟨96632, by rfl⟩) R193265
theorem R292709 : Reach 292709 := rs (se 4 (by rfl) ⟨27441, by rfl⟩) R54883
theorem R129113 : Reach 129113 := rs (se 2 (by rfl) ⟨48417, by rfl⟩) R96835
theorem R96349 : Reach 96349 := rs (se 3 (by rfl) ⟨18065, by rfl⟩) R36131
theorem R63767 : Reach 63767 := rs (se 1 (by rfl) ⟨47825, by rfl⟩) R95651
theorem R63895 : Reach 63895 := rs (se 1 (by rfl) ⟨47921, by rfl⟩) R95843
theorem R326105 : Reach 326105 := rs (se 2 (by rfl) ⟨122289, by rfl⟩) R244579
theorem R359063 : Reach 359063 := rs (se 1 (by rfl) ⟨269297, by rfl⟩) R538595
theorem R96947 : Reach 96947 := rs (se 1 (by rfl) ⟨72710, by rfl⟩) R145421
theorem R129815 : Reach 129815 := rs (se 1 (by rfl) ⟨97361, by rfl⟩) R194723
theorem R64307 : Reach 64307 := rs (se 1 (by rfl) ⟨48230, by rfl⟩) R96461
theorem R555893 : Reach 555893 := rs (se 5 (by rfl) ⟨26057, by rfl⟩) R52115
theorem R129923 : Reach 129923 := rs (se 1 (by rfl) ⟨97442, by rfl⟩) R194885
theorem R64435 : Reach 64435 := rs (se 1 (by rfl) ⟨48326, by rfl⟩) R96653
theorem R64523 : Reach 64523 := rs (se 1 (by rfl) ⟨48392, by rfl⟩) R96785
theorem R64577 : Reach 64577 := rs (se 2 (by rfl) ⟨24216, by rfl⟩) R48433
theorem R195659 : Reach 195659 := rs (se 1 (by rfl) ⟨146744, by rfl⟩) R293489
theorem R64651 : Reach 64651 := rs (se 1 (by rfl) ⟨48488, by rfl⟩) R96977
theorem R130193 : Reach 130193 := rs (se 2 (by rfl) ⟨48822, by rfl⟩) R97645
theorem R64705 : Reach 64705 := rs (se 2 (by rfl) ⟨24264, by rfl⟩) R48529
theorem R97483 : Reach 97483 := rs (se 1 (by rfl) ⟨73112, by rfl⟩) R146225
theorem R195857 : Reach 195857 := rs (se 2 (by rfl) ⟨73446, by rfl⟩) R146893
theorem R64793 : Reach 64793 := rs (se 2 (by rfl) ⟨24297, by rfl⟩) R48595
theorem R130355 : Reach 130355 := rs (se 1 (by rfl) ⟨97766, by rfl⟩) R195533
theorem R97625 : Reach 97625 := rs (se 2 (by rfl) ⟨36609, by rfl⟩) R73219
theorem R64921 : Reach 64921 := rs (se 2 (by rfl) ⟨24345, by rfl⟩) R48691
theorem R196019 : Reach 196019 := rs (se 1 (by rfl) ⟨147014, by rfl⟩) R294029
theorem R97757 : Reach 97757 := rs (se 3 (by rfl) ⟨18329, by rfl⟩) R36659
theorem R130625 : Reach 130625 := rs (se 2 (by rfl) ⟨48984, by rfl⟩) R97969
theorem R130733 : Reach 130733 := rs (se 3 (by rfl) ⟨24512, by rfl⟩) R49025
theorem R65495 : Reach 65495 := rs (se 1 (by rfl) ⟨49121, by rfl⟩) R98243
theorem R65569 : Reach 65569 := rs (se 2 (by rfl) ⟨24588, by rfl⟩) R49177
theorem R98363 : Reach 98363 := rs (se 1 (by rfl) ⟨73772, by rfl⟩) R147545
theorem R131273 : Reach 131273 := rs (se 2 (by rfl) ⟨49227, by rfl⟩) R98455
theorem R131387 : Reach 131387 := rs (se 1 (by rfl) ⟨98540, by rfl⟩) R197081
theorem R65927 : Reach 65927 := rs (se 1 (by rfl) ⟨49445, by rfl⟩) R98891
theorem R164231 : Reach 164231 := rs (se 1 (by rfl) ⟨123173, by rfl⟩) R246347
theorem R229817 : Reach 229817 := rs (se 2 (by rfl) ⟨86181, by rfl⟩) R172363
theorem R229841 : Reach 229841 := rs (se 2 (by rfl) ⟨86190, by rfl⟩) R172381
theorem R131651 : Reach 131651 := rs (se 1 (by rfl) ⟨98738, by rfl⟩) R197477
theorem R361061 : Reach 361061 := rs (se 4 (by rfl) ⟨33849, by rfl⟩) R67699
theorem R131975 : Reach 131975 := rs (se 1 (by rfl) ⟨98981, by rfl⟩) R197963
theorem R1377809 : Reach 1377809 := rs (se 2 (by rfl) ⟨516678, by rfl⟩) R1033357
theorem R886373 : Reach 886373 := rs (se 4 (by rfl) ⟨83097, by rfl⟩) R166195
theorem R296567 : Reach 296567 := rs (se 1 (by rfl) ⟨222425, by rfl⟩) R444851
theorem R165665 : Reach 165665 := rs (se 2 (by rfl) ⟨62124, by rfl⟩) R124249
theorem R67387 : Reach 67387 := rs (se 1 (by rfl) ⟨50540, by rfl⟩) R101081
theorem R67463 : Reach 67463 := rs (se 1 (by rfl) ⟨50597, by rfl⟩) R101195
theorem R165817 : Reach 165817 := rs (se 2 (by rfl) ⟨62181, by rfl⟩) R124363
theorem R67873 : Reach 67873 := rs (se 2 (by rfl) ⟨25452, by rfl⟩) R50905
theorem R35131 : Reach 35131 := rs (se 1 (by rfl) ⟨26348, by rfl⟩) R52697
theorem R35207 : Reach 35207 := rs (se 1 (by rfl) ⟨26405, by rfl⟩) R52811
theorem R35215 : Reach 35215 := rs (se 1 (by rfl) ⟨26411, by rfl⟩) R52823
theorem R35259 : Reach 35259 := rs (se 1 (by rfl) ⟨26444, by rfl⟩) R52889
theorem R100865 : Reach 100865 := rs (se 2 (by rfl) ⟨37824, by rfl⟩) R75649
theorem R35335 : Reach 35335 := rs (se 1 (by rfl) ⟨26501, by rfl⟩) R53003
theorem R35343 : Reach 35343 := rs (se 1 (by rfl) ⟨26507, by rfl⟩) R53015
theorem R35387 : Reach 35387 := rs (se 1 (by rfl) ⟨26540, by rfl⟩) R53081
theorem R68215 : Reach 68215 := rs (se 1 (by rfl) ⟨51161, by rfl⟩) R102323
theorem R35463 : Reach 35463 := rs (se 1 (by rfl) ⟨26597, by rfl⟩) R53195
theorem R35471 : Reach 35471 := rs (se 1 (by rfl) ⟨26603, by rfl⟩) R53207
theorem R35515 : Reach 35515 := rs (se 1 (by rfl) ⟨26636, by rfl⟩) R53273
theorem R166657 : Reach 166657 := rs (se 2 (by rfl) ⟨62496, by rfl⟩) R124993
theorem R35591 : Reach 35591 := rs (se 1 (by rfl) ⟨26693, by rfl⟩) R53387
theorem R35599 : Reach 35599 := rs (se 1 (by rfl) ⟨26699, by rfl⟩) R53399
theorem R35643 : Reach 35643 := rs (se 1 (by rfl) ⟨26732, by rfl⟩) R53465
theorem R35719 : Reach 35719 := rs (se 1 (by rfl) ⟨26789, by rfl⟩) R53579
theorem R35727 : Reach 35727 := rs (se 1 (by rfl) ⟨26795, by rfl⟩) R53591
theorem R35771 : Reach 35771 := rs (se 1 (by rfl) ⟨26828, by rfl⟩) R53657
theorem R101321 : Reach 101321 := rs (se 2 (by rfl) ⟨37995, by rfl⟩) R75991
theorem R35847 : Reach 35847 := rs (se 1 (by rfl) ⟨26885, by rfl⟩) R53771
theorem R1281035 : Reach 1281035 := rs (se 1 (by rfl) ⟨960776, by rfl⟩) R1921553
theorem R35855 : Reach 35855 := rs (se 1 (by rfl) ⟨26891, by rfl⟩) R53783
theorem R35899 : Reach 35899 := rs (se 1 (by rfl) ⟨26924, by rfl⟩) R53849
theorem R35975 : Reach 35975 := rs (se 1 (by rfl) ⟨26981, by rfl⟩) R53963
theorem R35983 : Reach 35983 := rs (se 1 (by rfl) ⟨26987, by rfl⟩) R53975
theorem R36027 : Reach 36027 := rs (se 1 (by rfl) ⟨27020, by rfl⟩) R54041
theorem R36103 : Reach 36103 := rs (se 1 (by rfl) ⟨27077, by rfl⟩) R54155
theorem R36111 : Reach 36111 := rs (se 1 (by rfl) ⟨27083, by rfl⟩) R54167
theorem R363809 : Reach 363809 := rs (se 2 (by rfl) ⟨136428, by rfl⟩) R272857
theorem R36155 : Reach 36155 := rs (se 1 (by rfl) ⟨27116, by rfl⟩) R54233
theorem R36231 : Reach 36231 := rs (se 1 (by rfl) ⟨27173, by rfl⟩) R54347
theorem R36239 : Reach 36239 := rs (se 1 (by rfl) ⟨27179, by rfl⟩) R54359
theorem R36283 : Reach 36283 := rs (se 1 (by rfl) ⟨27212, by rfl⟩) R54425
theorem R36359 : Reach 36359 := rs (se 1 (by rfl) ⟨27269, by rfl⟩) R54539
theorem R36367 : Reach 36367 := rs (se 1 (by rfl) ⟨27275, by rfl⟩) R54551
theorem R36411 : Reach 36411 := rs (se 1 (by rfl) ⟨27308, by rfl⟩) R54617
theorem R134743 : Reach 134743 := rs (se 1 (by rfl) ⟨101057, by rfl⟩) R202115
theorem R691811 : Reach 691811 := rs (se 1 (by rfl) ⟨518858, by rfl⟩) R1037717
theorem R36487 : Reach 36487 := rs (se 1 (by rfl) ⟨27365, by rfl⟩) R54731
theorem R36495 : Reach 36495 := rs (se 1 (by rfl) ⟨27371, by rfl⟩) R54743
theorem R36539 : Reach 36539 := rs (se 1 (by rfl) ⟨27404, by rfl⟩) R54809
theorem R36615 : Reach 36615 := rs (se 1 (by rfl) ⟨27461, by rfl⟩) R54923
theorem R36623 : Reach 36623 := rs (se 1 (by rfl) ⟨27467, by rfl⟩) R54935
theorem R36667 : Reach 36667 := rs (se 1 (by rfl) ⟨27500, by rfl⟩) R55001
theorem R135047 : Reach 135047 := rs (se 1 (by rfl) ⟨101285, by rfl⟩) R202571
theorem R36743 : Reach 36743 := rs (se 1 (by rfl) ⟨27557, by rfl⟩) R55115
theorem R36751 : Reach 36751 := rs (se 1 (by rfl) ⟨27563, by rfl⟩) R55127
theorem R102329 : Reach 102329 := rs (se 2 (by rfl) ⟨38373, by rfl⟩) R76747
theorem R36795 : Reach 36795 := rs (se 1 (by rfl) ⟨27596, by rfl⟩) R55193
theorem R200657 : Reach 200657 := rs (se 2 (by rfl) ⟨75246, by rfl⟩) R150493
theorem R36871 : Reach 36871 := rs (se 1 (by rfl) ⟨27653, by rfl⟩) R55307
theorem R36879 : Reach 36879 := rs (se 1 (by rfl) ⟨27659, by rfl⟩) R55319
theorem R36923 : Reach 36923 := rs (se 1 (by rfl) ⟨27692, by rfl⟩) R55385
theorem R135229 : Reach 135229 := rs (se 3 (by rfl) ⟨25355, by rfl⟩) R50711
theorem R36999 : Reach 36999 := rs (se 1 (by rfl) ⟨27749, by rfl⟩) R55499
theorem R37007 : Reach 37007 := rs (se 1 (by rfl) ⟨27755, by rfl⟩) R55511
theorem R69817 : Reach 69817 := rs (se 2 (by rfl) ⟨26181, by rfl⟩) R52363
theorem R37051 : Reach 37051 := rs (se 1 (by rfl) ⟨27788, by rfl⟩) R55577
theorem R299209 : Reach 299209 := rs (se 2 (by rfl) ⟨112203, by rfl⟩) R224407
theorem R37127 : Reach 37127 := rs (se 1 (by rfl) ⟨27845, by rfl⟩) R55691
theorem R37135 : Reach 37135 := rs (se 1 (by rfl) ⟨27851, by rfl⟩) R55703
theorem R37179 : Reach 37179 := rs (se 1 (by rfl) ⟨27884, by rfl⟩) R55769
theorem R37255 : Reach 37255 := rs (se 1 (by rfl) ⟨27941, by rfl⟩) R55883
theorem R37263 : Reach 37263 := rs (se 1 (by rfl) ⟨27947, by rfl⟩) R55895
theorem R233873 : Reach 233873 := rs (se 2 (by rfl) ⟨87702, by rfl⟩) R175405
theorem R201113 : Reach 201113 := rs (se 2 (by rfl) ⟨75417, by rfl⟩) R150835
theorem R37307 : Reach 37307 := rs (se 1 (by rfl) ⟨27980, by rfl⟩) R55961
theorem R37383 : Reach 37383 := rs (se 1 (by rfl) ⟨28037, by rfl⟩) R56075
theorem R70159 : Reach 70159 := rs (se 1 (by rfl) ⟨52619, by rfl⟩) R105239
theorem R37391 : Reach 37391 := rs (se 1 (by rfl) ⟨28043, by rfl⟩) R56087
theorem R102971 : Reach 102971 := rs (se 1 (by rfl) ⟨77228, by rfl⟩) R154457
theorem R37435 : Reach 37435 := rs (se 1 (by rfl) ⟨28076, by rfl⟩) R56153
theorem R37511 : Reach 37511 := rs (se 1 (by rfl) ⟨28133, by rfl⟩) R56267
theorem R37519 : Reach 37519 := rs (se 1 (by rfl) ⟨28139, by rfl⟩) R56279
theorem R37563 : Reach 37563 := rs (se 1 (by rfl) ⟨28172, by rfl⟩) R56345
theorem R37639 : Reach 37639 := rs (se 1 (by rfl) ⟨28229, by rfl⟩) R56459
theorem R37647 : Reach 37647 := rs (se 1 (by rfl) ⟨28235, by rfl⟩) R56471
theorem R37691 : Reach 37691 := rs (se 1 (by rfl) ⟨28268, by rfl⟩) R56537
theorem R37767 : Reach 37767 := rs (se 1 (by rfl) ⟨28325, by rfl⟩) R56651
theorem R37775 : Reach 37775 := rs (se 1 (by rfl) ⟨28331, by rfl⟩) R56663
theorem R37819 : Reach 37819 := rs (se 1 (by rfl) ⟨28364, by rfl⟩) R56729
theorem R37895 : Reach 37895 := rs (se 1 (by rfl) ⟨28421, by rfl⟩) R56843
theorem R37903 : Reach 37903 := rs (se 1 (by rfl) ⟨28427, by rfl⟩) R56855
theorem R37947 : Reach 37947 := rs (se 1 (by rfl) ⟨28460, by rfl⟩) R56921
theorem R38023 : Reach 38023 := rs (se 1 (by rfl) ⟨28517, by rfl⟩) R57035
theorem R38031 : Reach 38031 := rs (se 1 (by rfl) ⟨28523, by rfl⟩) R57047
theorem R103609 : Reach 103609 := rs (se 2 (by rfl) ⟨38853, by rfl⟩) R77707
theorem R38075 : Reach 38075 := rs (se 1 (by rfl) ⟨28556, by rfl⟩) R57113
theorem R38151 : Reach 38151 := rs (se 1 (by rfl) ⟨28613, by rfl⟩) R57227
theorem R38159 : Reach 38159 := rs (se 1 (by rfl) ⟨28619, by rfl⟩) R57239
theorem R169249 : Reach 169249 := rs (se 2 (by rfl) ⟨63468, by rfl⟩) R126937
theorem R38203 : Reach 38203 := rs (se 1 (by rfl) ⟨28652, by rfl⟩) R57305
theorem R71047 : Reach 71047 := rs (se 1 (by rfl) ⟨53285, by rfl⟩) R106571
theorem R38279 : Reach 38279 := rs (se 1 (by rfl) ⟨28709, by rfl⟩) R57419
theorem R38287 : Reach 38287 := rs (se 1 (by rfl) ⟨28715, by rfl⟩) R57431
theorem R38331 : Reach 38331 := rs (se 1 (by rfl) ⟨28748, by rfl⟩) R57497
theorem R300509 : Reach 300509 := rs (se 3 (by rfl) ⟨56345, by rfl⟩) R112691
theorem R38407 : Reach 38407 := rs (se 1 (by rfl) ⟨28805, by rfl⟩) R57611
theorem R38415 : Reach 38415 := rs (se 1 (by rfl) ⟨28811, by rfl⟩) R57623
theorem R38459 : Reach 38459 := rs (se 1 (by rfl) ⟨28844, by rfl⟩) R57689
theorem R103997 : Reach 103997 := rs (se 3 (by rfl) ⟨19499, by rfl⟩) R38999
theorem R661069 : Reach 661069 := rs (se 3 (by rfl) ⟨123950, by rfl⟩) R247901
theorem R38535 : Reach 38535 := rs (se 1 (by rfl) ⟨28901, by rfl⟩) R57803
theorem R38543 : Reach 38543 := rs (se 1 (by rfl) ⟨28907, by rfl⟩) R57815
theorem R38587 : Reach 38587 := rs (se 1 (by rfl) ⟨28940, by rfl⟩) R57881
theorem R136961 : Reach 136961 := rs (se 2 (by rfl) ⟨51360, by rfl⟩) R102721
theorem R38663 : Reach 38663 := rs (se 1 (by rfl) ⟨28997, by rfl⟩) R57995
theorem R38671 : Reach 38671 := rs (se 1 (by rfl) ⟨29003, by rfl⟩) R58007
theorem R38715 : Reach 38715 := rs (se 1 (by rfl) ⟨29036, by rfl⟩) R58073
theorem R38791 : Reach 38791 := rs (se 1 (by rfl) ⟨29093, by rfl⟩) R58187
theorem R38799 : Reach 38799 := rs (se 1 (by rfl) ⟨29099, by rfl⟩) R58199
theorem R38843 : Reach 38843 := rs (se 1 (by rfl) ⟨29132, by rfl⟩) R58265
theorem R38919 : Reach 38919 := rs (se 1 (by rfl) ⟨29189, by rfl⟩) R58379
theorem R38927 : Reach 38927 := rs (se 1 (by rfl) ⟨29195, by rfl⟩) R58391
theorem R38971 : Reach 38971 := rs (se 1 (by rfl) ⟨29228, by rfl⟩) R58457
theorem R137303 : Reach 137303 := rs (se 1 (by rfl) ⟨102977, by rfl⟩) R205955
theorem R39047 : Reach 39047 := rs (se 1 (by rfl) ⟨29285, by rfl⟩) R58571
theorem R39055 : Reach 39055 := rs (se 1 (by rfl) ⟨29291, by rfl⟩) R58583
theorem R202925 : Reach 202925 := rs (se 3 (by rfl) ⟨38048, by rfl⟩) R76097
theorem R39099 : Reach 39099 := rs (se 1 (by rfl) ⟨29324, by rfl⟩) R58649
theorem R39559 : Reach 39559 := rs (se 1 (by rfl) ⟨29669, by rfl⟩) R59339
theorem R105113 : Reach 105113 := rs (se 2 (by rfl) ⟨39417, by rfl⟩) R78835
theorem R170689 : Reach 170689 := rs (se 2 (by rfl) ⟨64008, by rfl⟩) R128017
theorem R105259 : Reach 105259 := rs (se 1 (by rfl) ⟨78944, by rfl⟩) R157889
theorem R39739 : Reach 39739 := rs (se 1 (by rfl) ⟨29804, by rfl⟩) R59609
theorem R138131 : Reach 138131 := rs (se 1 (by rfl) ⟨103598, by rfl⟩) R207197
theorem R334745 : Reach 334745 := rs (se 2 (by rfl) ⟨125529, by rfl⟩) R251059
theorem R39943 : Reach 39943 := rs (se 1 (by rfl) ⟨29957, by rfl⟩) R59915
theorem R72839 : Reach 72839 := rs (se 1 (by rfl) ⟨54629, by rfl⟩) R109259
theorem R40207 : Reach 40207 := rs (se 1 (by rfl) ⟨30155, by rfl⟩) R60311
theorem R138631 : Reach 138631 := rs (se 1 (by rfl) ⟨103973, by rfl⟩) R207947
theorem R73145 : Reach 73145 := rs (se 2 (by rfl) ⟨27429, by rfl⟩) R54859
theorem R957905 : Reach 957905 := rs (se 2 (by rfl) ⟨359214, by rfl⟩) R718429
theorem R499229 : Reach 499229 := rs (se 3 (by rfl) ⟨93605, by rfl⟩) R187211
theorem R204481 : Reach 204481 := rs (se 2 (by rfl) ⟨76680, by rfl⟩) R153361
theorem R40711 : Reach 40711 := rs (se 1 (by rfl) ⟨30533, by rfl⟩) R61067
theorem R302899 : Reach 302899 := rs (se 1 (by rfl) ⟨227174, by rfl⟩) R454349
theorem R40891 : Reach 40891 := rs (se 1 (by rfl) ⟨30668, by rfl⟩) R61337
theorem R106525 : Reach 106525 := rs (se 3 (by rfl) ⟨19973, by rfl⟩) R39947
theorem R172151 : Reach 172151 := rs (se 1 (by rfl) ⟨129113, by rfl⟩) R258227
theorem R106697 : Reach 106697 := rs (se 2 (by rfl) ⟨40011, by rfl⟩) R80023
theorem R205001 : Reach 205001 := rs (se 2 (by rfl) ⟨76875, by rfl⟩) R153751
theorem R106753 : Reach 106753 := rs (se 2 (by rfl) ⟨40032, by rfl⟩) R80065
theorem R74119 : Reach 74119 := rs (se 1 (by rfl) ⟨55589, by rfl⟩) R111179
theorem R41359 : Reach 41359 := rs (se 1 (by rfl) ⟨31019, by rfl⟩) R62039
theorem R107095 : Reach 107095 := rs (se 1 (by rfl) ⟨80321, by rfl⟩) R160643
theorem R41719 : Reach 41719 := rs (se 1 (by rfl) ⟨31289, by rfl⟩) R62579
theorem R41863 : Reach 41863 := rs (se 1 (by rfl) ⟨31397, by rfl⟩) R62795
theorem R41899 : Reach 41899 := rs (se 1 (by rfl) ⟨31424, by rfl⟩) R62849
theorem R500741 : Reach 500741 := rs (se 4 (by rfl) ⟨46944, by rfl⟩) R93889
theorem R42043 : Reach 42043 := rs (se 1 (by rfl) ⟨31532, by rfl⟩) R63065
theorem R1254791 : Reach 1254791 := rs (se 1 (by rfl) ⟨941093, by rfl⟩) R1882187
theorem R42511 : Reach 42511 := rs (se 1 (by rfl) ⟨31883, by rfl⟩) R63767
theorem R435941 : Reach 435941 := rs (se 4 (by rfl) ⟨40869, by rfl⟩) R81739
theorem R239375 : Reach 239375 := rs (se 1 (by rfl) ⟨179531, by rfl⟩) R359063
theorem R42871 : Reach 42871 := rs (se 1 (by rfl) ⟨32153, by rfl⟩) R64307
theorem R370595 : Reach 370595 := rs (se 1 (by rfl) ⟨277946, by rfl⟩) R555893
theorem R43015 : Reach 43015 := rs (se 1 (by rfl) ⟨32261, by rfl⟩) R64523
theorem R43051 : Reach 43051 := rs (se 1 (by rfl) ⟨32288, by rfl⟩) R64577
theorem R43195 : Reach 43195 := rs (se 1 (by rfl) ⟨32396, by rfl⟩) R64793
theorem R43663 : Reach 43663 := rs (se 1 (by rfl) ⟨32747, by rfl⟩) R65495
theorem R371735 : Reach 371735 := rs (se 1 (by rfl) ⟨278801, by rfl⟩) R557603
theorem R208129 : Reach 208129 := rs (se 2 (by rfl) ⟨78048, by rfl⟩) R156097
theorem R109853 : Reach 109853 := rs (se 3 (by rfl) ⟨20597, by rfl⟩) R41195
theorem R109943 : Reach 109943 := rs (se 1 (by rfl) ⟨82457, by rfl⟩) R164915
theorem R1420753 : Reach 1420753 := rs (se 2 (by rfl) ⟨532782, by rfl⟩) R1065565
theorem R208655 : Reach 208655 := rs (se 1 (by rfl) ⟨156491, by rfl⟩) R312983
theorem R405323 : Reach 405323 := rs (se 1 (by rfl) ⟨303992, by rfl⟩) R607985
theorem R77753 : Reach 77753 := rs (se 2 (by rfl) ⟨29157, by rfl⟩) R58315
theorem R45355 : Reach 45355 := rs (se 1 (by rfl) ⟨34016, by rfl⟩) R68033
theorem R45815 : Reach 45815 := rs (se 1 (by rfl) ⟨34361, by rfl⟩) R68723
theorem R45883 : Reach 45883 := rs (se 1 (by rfl) ⟨34412, by rfl⟩) R68825
theorem R144281 : Reach 144281 := rs (se 2 (by rfl) ⟨54105, by rfl⟩) R108211
theorem R144503 : Reach 144503 := rs (se 1 (by rfl) ⟨108377, by rfl⟩) R216755
theorem R210113 : Reach 210113 := rs (se 2 (by rfl) ⟨78792, by rfl⟩) R157585
theorem R177353 : Reach 177353 := rs (se 2 (by rfl) ⟨66507, by rfl⟩) R133015
theorem R46327 : Reach 46327 := rs (se 1 (by rfl) ⟨34745, by rfl⟩) R69491
theorem R79163 : Reach 79163 := rs (se 1 (by rfl) ⟨59372, by rfl⟩) R118745
theorem R177497 : Reach 177497 := rs (se 2 (by rfl) ⟨66561, by rfl⟩) R133123
theorem R79289 : Reach 79289 := rs (se 2 (by rfl) ⟨29733, by rfl⟩) R59467
theorem R308701 : Reach 308701 := rs (se 3 (by rfl) ⟨57881, by rfl⟩) R115763
theorem R46651 : Reach 46651 := rs (se 1 (by rfl) ⟨34988, by rfl⟩) R69977
theorem R79631 : Reach 79631 := rs (se 1 (by rfl) ⟨59723, by rfl⟩) R119447
theorem R79649 : Reach 79649 := rs (se 2 (by rfl) ⟨29868, by rfl⟩) R59737
theorem R178199 : Reach 178199 := rs (se 1 (by rfl) ⟨133649, by rfl⟩) R267299
theorem R79991 : Reach 79991 := rs (se 1 (by rfl) ⟨59993, by rfl⟩) R119987
theorem R80171 : Reach 80171 := rs (se 1 (by rfl) ⟨60128, by rfl⟩) R120257
theorem R47623 : Reach 47623 := rs (se 1 (by rfl) ⟨35717, by rfl⟩) R71435
theorem R80531 : Reach 80531 := rs (se 1 (by rfl) ⟨60398, by rfl⟩) R120797
theorem R80585 : Reach 80585 := rs (se 2 (by rfl) ⟨30219, by rfl⟩) R60439
theorem R441139 : Reach 441139 := rs (se 1 (by rfl) ⟨330854, by rfl⟩) R661709
theorem R48043 : Reach 48043 := rs (se 1 (by rfl) ⟨36032, by rfl⟩) R72065
theorem R179147 : Reach 179147 := rs (se 1 (by rfl) ⟨134360, by rfl⟩) R268721
theorem R48271 : Reach 48271 := rs (se 1 (by rfl) ⟨36203, by rfl⟩) R72407
theorem R2243861 : Reach 2243861 := rs (se 6 (by rfl) ⟨52590, by rfl⟩) R105181
theorem R81287 : Reach 81287 := rs (se 1 (by rfl) ⟨60965, by rfl⟩) R121931
theorem R212503 : Reach 212503 := rs (se 1 (by rfl) ⟨159377, by rfl⟩) R318755
theorem R81467 : Reach 81467 := rs (se 1 (by rfl) ⟨61100, by rfl⟩) R122201
theorem R147005 : Reach 147005 := rs (se 3 (by rfl) ⟨27563, by rfl⟩) R55127
theorem R81593 : Reach 81593 := rs (se 2 (by rfl) ⟨30597, by rfl⟩) R61195
theorem R49015 : Reach 49015 := rs (se 1 (by rfl) ⟨36761, by rfl⟩) R73523
theorem R49081 : Reach 49081 := rs (se 2 (by rfl) ⟨18405, by rfl⟩) R36811
theorem R81935 : Reach 81935 := rs (se 1 (by rfl) ⟨61451, by rfl⟩) R122903
theorem R81953 : Reach 81953 := rs (se 2 (by rfl) ⟨30732, by rfl⟩) R61465
theorem R49339 : Reach 49339 := rs (se 1 (by rfl) ⟨37004, by rfl⟩) R74009
theorem R82235 : Reach 82235 := rs (se 1 (by rfl) ⟨61676, by rfl⟩) R123353
theorem R82295 : Reach 82295 := rs (se 1 (by rfl) ⟨61721, by rfl⟩) R123443
theorem R147865 : Reach 147865 := rs (se 2 (by rfl) ⟨55449, by rfl⟩) R110899
theorem R82475 : Reach 82475 := rs (se 1 (by rfl) ⟨61856, by rfl⟩) R123713
theorem R115319 : Reach 115319 := rs (se 1 (by rfl) ⟨86489, by rfl⟩) R172979
theorem R148169 : Reach 148169 := rs (se 2 (by rfl) ⟨55563, by rfl⟩) R111127
theorem R50039 : Reach 50039 := rs (se 1 (by rfl) ⟨37529, by rfl⟩) R75059
theorem R82835 : Reach 82835 := rs (se 1 (by rfl) ⟨62126, by rfl⟩) R124253
theorem R279449 : Reach 279449 := rs (se 2 (by rfl) ⟨104793, by rfl⟩) R209587
theorem R82873 : Reach 82873 := rs (se 2 (by rfl) ⟨31077, by rfl⟩) R62155
theorem R50105 : Reach 50105 := rs (se 2 (by rfl) ⟨18789, by rfl⟩) R37579
theorem R82889 : Reach 82889 := rs (se 2 (by rfl) ⟨31083, by rfl⟩) R62167
theorem R181277 : Reach 181277 := rs (se 3 (by rfl) ⟨33989, by rfl⟩) R67979
theorem R50233 : Reach 50233 := rs (se 2 (by rfl) ⟨18837, by rfl⟩) R37675
theorem R83243 : Reach 83243 := rs (se 1 (by rfl) ⟨62432, by rfl⟩) R124865
theorem R181763 : Reach 181763 := rs (se 1 (by rfl) ⟨136322, by rfl⟩) R272645
theorem R542285 : Reach 542285 := rs (se 3 (by rfl) ⟨101678, by rfl⟩) R203357
theorem R116311 : Reach 116311 := rs (se 1 (by rfl) ⟨87233, by rfl⟩) R174467
theorem R83591 : Reach 83591 := rs (se 1 (by rfl) ⟨62693, by rfl⟩) R125387
theorem R83609 : Reach 83609 := rs (se 2 (by rfl) ⟨31353, by rfl⟩) R62707
theorem R214721 : Reach 214721 := rs (se 2 (by rfl) ⟨80520, by rfl⟩) R161041
theorem R50959 : Reach 50959 := rs (se 1 (by rfl) ⟨38219, by rfl⟩) R76439
theorem R542513 : Reach 542513 := rs (se 2 (by rfl) ⟨203442, by rfl⟩) R406885
theorem R83771 : Reach 83771 := rs (se 1 (by rfl) ⟨62828, by rfl⟩) R125657
theorem R214919 : Reach 214919 := rs (se 1 (by rfl) ⟨161189, by rfl⟩) R322379
theorem R83897 : Reach 83897 := rs (se 2 (by rfl) ⟨31461, by rfl⟩) R62923
theorem R83969 : Reach 83969 := rs (se 2 (by rfl) ⟨31488, by rfl⟩) R62977
theorem R51463 : Reach 51463 := rs (se 1 (by rfl) ⟨38597, by rfl⟩) R77195
theorem R84235 : Reach 84235 := rs (se 1 (by rfl) ⟨63176, by rfl⟩) R126353
theorem R84239 : Reach 84239 := rs (se 1 (by rfl) ⟨63179, by rfl⟩) R126359
theorem R444689 : Reach 444689 := rs (se 2 (by rfl) ⟨166758, by rfl⟩) R333517
theorem R84257 : Reach 84257 := rs (se 2 (by rfl) ⟨31596, by rfl⟩) R63193
theorem R84311 : Reach 84311 := rs (se 1 (by rfl) ⟨63233, by rfl⟩) R126467
theorem R182749 : Reach 182749 := rs (se 3 (by rfl) ⟨34265, by rfl⟩) R68531
theorem R84491 : Reach 84491 := rs (se 1 (by rfl) ⟨63368, by rfl⟩) R126737
theorem R150083 : Reach 150083 := rs (se 1 (by rfl) ⟨112562, by rfl⟩) R225125
theorem R84599 : Reach 84599 := rs (se 1 (by rfl) ⟨63449, by rfl⟩) R126899
theorem R84779 : Reach 84779 := rs (se 1 (by rfl) ⟨63584, by rfl⟩) R127169
theorem R281393 : Reach 281393 := rs (se 2 (by rfl) ⟨105522, by rfl⟩) R211045
theorem R84851 : Reach 84851 := rs (se 1 (by rfl) ⟨63638, by rfl⟩) R127277
theorem R183185 : Reach 183185 := rs (se 2 (by rfl) ⟨68694, by rfl⟩) R137389
theorem R52169 : Reach 52169 := rs (se 2 (by rfl) ⟨19563, by rfl⟩) R39127
theorem R52283 : Reach 52283 := rs (se 1 (by rfl) ⟨39212, by rfl⟩) R78425
theorem R805949 : Reach 805949 := rs (se 3 (by rfl) ⟨151115, by rfl⟩) R302231
theorem R379991 : Reach 379991 := rs (se 1 (by rfl) ⟨284993, by rfl⟩) R569987
theorem R183383 : Reach 183383 := rs (se 1 (by rfl) ⟨137537, by rfl⟩) R275075
theorem R85139 : Reach 85139 := rs (se 1 (by rfl) ⟨63854, by rfl⟩) R127709
theorem R85193 : Reach 85193 := rs (se 2 (by rfl) ⟨31947, by rfl⟩) R63895
theorem R85259 : Reach 85259 := rs (se 1 (by rfl) ⟨63944, by rfl⟩) R127889
theorem R118201 : Reach 118201 := rs (se 2 (by rfl) ⟨44325, by rfl⟩) R88651
theorem R52727 : Reach 52727 := rs (se 1 (by rfl) ⟨39545, by rfl⟩) R79091
theorem R52751 : Reach 52751 := rs (se 1 (by rfl) ⟨39563, by rfl⟩) R79127
theorem R52793 : Reach 52793 := rs (se 2 (by rfl) ⟨19797, by rfl⟩) R39595
theorem R183869 : Reach 183869 := rs (se 3 (by rfl) ⟨34475, by rfl⟩) R68951
theorem R216695 : Reach 216695 := rs (se 1 (by rfl) ⟨162521, by rfl⟩) R325043
theorem R52871 : Reach 52871 := rs (se 1 (by rfl) ⟨39653, by rfl⟩) R79307
theorem R52907 : Reach 52907 := rs (se 1 (by rfl) ⟨39680, by rfl⟩) R79361
theorem R52921 : Reach 52921 := rs (se 2 (by rfl) ⟨19845, by rfl⟩) R39691
theorem R52937 : Reach 52937 := rs (se 2 (by rfl) ⟨19851, by rfl⟩) R39703
theorem R118529 : Reach 118529 := rs (se 2 (by rfl) ⟨44448, by rfl⟩) R88897
theorem R249601 : Reach 249601 := rs (se 2 (by rfl) ⟨93600, by rfl⟩) R187201
theorem R53051 : Reach 53051 := rs (se 1 (by rfl) ⟨39788, by rfl⟩) R79577
theorem R53111 : Reach 53111 := rs (se 1 (by rfl) ⟨39833, by rfl⟩) R79667
theorem R85895 : Reach 85895 := rs (se 1 (by rfl) ⟨64421, by rfl⟩) R128843
theorem R53135 : Reach 53135 := rs (se 1 (by rfl) ⟨39851, by rfl⟩) R79703
theorem R85913 : Reach 85913 := rs (se 2 (by rfl) ⟨32217, by rfl⟩) R64435
theorem R53177 : Reach 53177 := rs (se 2 (by rfl) ⟨19941, by rfl⟩) R39883
theorem R53255 : Reach 53255 := rs (se 1 (by rfl) ⟨39941, by rfl⟩) R79883
theorem R53291 : Reach 53291 := rs (se 1 (by rfl) ⟨39968, by rfl⟩) R79937
theorem R86075 : Reach 86075 := rs (se 1 (by rfl) ⟨64556, by rfl⟩) R129113
theorem R53321 : Reach 53321 := rs (se 2 (by rfl) ⟨19995, by rfl⟩) R39991
theorem R86201 : Reach 86201 := rs (se 2 (by rfl) ⟨32325, by rfl⟩) R64651
theorem R53435 : Reach 53435 := rs (se 1 (by rfl) ⟨40076, by rfl⟩) R80153
theorem R905417 : Reach 905417 := rs (se 2 (by rfl) ⟨339531, by rfl⟩) R679063
theorem R53495 : Reach 53495 := rs (se 1 (by rfl) ⟨40121, by rfl⟩) R80243
theorem R86273 : Reach 86273 := rs (se 2 (by rfl) ⟨32352, by rfl⟩) R64705
theorem R53519 : Reach 53519 := rs (se 1 (by rfl) ⟨40139, by rfl⟩) R80279
theorem R53561 : Reach 53561 := rs (se 2 (by rfl) ⟨20085, by rfl⟩) R40171
theorem R217403 : Reach 217403 := rs (se 1 (by rfl) ⟨163052, by rfl⟩) R326105
theorem R53639 : Reach 53639 := rs (se 1 (by rfl) ⟨40229, by rfl⟩) R80459
theorem R53675 : Reach 53675 := rs (se 1 (by rfl) ⟨40256, by rfl⟩) R80513
theorem R53705 : Reach 53705 := rs (se 2 (by rfl) ⟨20139, by rfl⟩) R40279
theorem R86543 : Reach 86543 := rs (se 1 (by rfl) ⟨64907, by rfl⟩) R129815
theorem R250397 : Reach 250397 := rs (se 3 (by rfl) ⟨46949, by rfl⟩) R93899
theorem R86561 : Reach 86561 := rs (se 2 (by rfl) ⟨32460, by rfl⟩) R64921
theorem R119339 : Reach 119339 := rs (se 1 (by rfl) ⟨89504, by rfl⟩) R179009
theorem R53819 : Reach 53819 := rs (se 1 (by rfl) ⟨40364, by rfl⟩) R80729
theorem R86615 : Reach 86615 := rs (se 1 (by rfl) ⟨64961, by rfl⟩) R129923
theorem R53879 : Reach 53879 := rs (se 1 (by rfl) ⟨40409, by rfl⟩) R80819
theorem R53903 : Reach 53903 := rs (se 1 (by rfl) ⟨40427, by rfl⟩) R80855
theorem R53945 : Reach 53945 := rs (se 2 (by rfl) ⟨20229, by rfl⟩) R40459
theorem R54023 : Reach 54023 := rs (se 1 (by rfl) ⟨40517, by rfl⟩) R81035
theorem R86795 : Reach 86795 := rs (se 1 (by rfl) ⟨65096, by rfl⟩) R130193
theorem R54059 : Reach 54059 := rs (se 1 (by rfl) ⟨40544, by rfl⟩) R81089
theorem R54089 : Reach 54089 := rs (se 2 (by rfl) ⟨20283, by rfl⟩) R40567
theorem R86903 : Reach 86903 := rs (se 1 (by rfl) ⟨65177, by rfl⟩) R130355
theorem R54203 : Reach 54203 := rs (se 1 (by rfl) ⟨40652, by rfl⟩) R81305
theorem R54263 : Reach 54263 := rs (se 1 (by rfl) ⟨40697, by rfl⟩) R81395
theorem R54287 : Reach 54287 := rs (se 1 (by rfl) ⟨40715, by rfl⟩) R81431
theorem R87083 : Reach 87083 := rs (se 1 (by rfl) ⟨65312, by rfl⟩) R130625
theorem R54329 : Reach 54329 := rs (se 2 (by rfl) ⟨20373, by rfl⟩) R40747
theorem R87155 : Reach 87155 := rs (se 1 (by rfl) ⟨65366, by rfl⟩) R130733
theorem R54407 : Reach 54407 := rs (se 1 (by rfl) ⟨40805, by rfl⟩) R81611
theorem R54443 : Reach 54443 := rs (se 1 (by rfl) ⟨40832, by rfl⟩) R81665
theorem R54473 : Reach 54473 := rs (se 2 (by rfl) ⟨20427, by rfl⟩) R40855
theorem R185651 : Reach 185651 := rs (se 1 (by rfl) ⟨139238, by rfl⟩) R278477
theorem R54587 : Reach 54587 := rs (se 1 (by rfl) ⟨40940, by rfl⟩) R81881
theorem R54647 : Reach 54647 := rs (se 1 (by rfl) ⟨40985, by rfl⟩) R81971
theorem R54671 : Reach 54671 := rs (se 1 (by rfl) ⟨41003, by rfl⟩) R82007
theorem R87443 : Reach 87443 := rs (se 1 (by rfl) ⟨65582, by rfl⟩) R131165
theorem R54713 : Reach 54713 := rs (se 2 (by rfl) ⟨20517, by rfl⟩) R41035
theorem R87497 : Reach 87497 := rs (se 2 (by rfl) ⟨32811, by rfl⟩) R65623
theorem R54791 : Reach 54791 := rs (se 1 (by rfl) ⟨41093, by rfl⟩) R82187
theorem R54827 : Reach 54827 := rs (se 1 (by rfl) ⟨41120, by rfl⟩) R82241
theorem R54857 : Reach 54857 := rs (se 2 (by rfl) ⟨20571, by rfl⟩) R41143
theorem R185975 : Reach 185975 := rs (se 1 (by rfl) ⟨139481, by rfl⟩) R278963
theorem R54971 : Reach 54971 := rs (se 1 (by rfl) ⟨41228, by rfl⟩) R82457
theorem R120521 : Reach 120521 := rs (se 2 (by rfl) ⟨45195, by rfl⟩) R90391
theorem R218861 : Reach 218861 := rs (se 3 (by rfl) ⟨41036, by rfl⟩) R82073
theorem R55031 : Reach 55031 := rs (se 1 (by rfl) ⟨41273, by rfl⟩) R82547
theorem R55055 : Reach 55055 := rs (se 1 (by rfl) ⟨41291, by rfl⟩) R82583
theorem R55097 : Reach 55097 := rs (se 2 (by rfl) ⟨20661, by rfl⟩) R41323
theorem R120635 : Reach 120635 := rs (se 1 (by rfl) ⟨90476, by rfl⟩) R180953
theorem R55175 : Reach 55175 := rs (se 1 (by rfl) ⟨41381, by rfl⟩) R82763
theorem R55211 : Reach 55211 := rs (se 1 (by rfl) ⟨41408, by rfl⟩) R82817
theorem R55241 : Reach 55241 := rs (se 2 (by rfl) ⟨20715, by rfl⟩) R41431
theorem R55355 : Reach 55355 := rs (se 1 (by rfl) ⟨41516, by rfl⟩) R83033
theorem R55415 : Reach 55415 := rs (se 1 (by rfl) ⟨41561, by rfl⟩) R83123
theorem R55439 : Reach 55439 := rs (se 1 (by rfl) ⟨41579, by rfl⟩) R83159
theorem R55481 : Reach 55481 := rs (se 2 (by rfl) ⟨20805, by rfl⟩) R41611
theorem R186569 : Reach 186569 := rs (se 2 (by rfl) ⟨69963, by rfl⟩) R139927
theorem R121121 : Reach 121121 := rs (se 2 (by rfl) ⟨45420, by rfl⟩) R90841
theorem R55595 : Reach 55595 := rs (se 1 (by rfl) ⟨41696, by rfl⟩) R83393
theorem R514451 : Reach 514451 := rs (se 1 (by rfl) ⟨385838, by rfl⟩) R771677
theorem R55823 : Reach 55823 := rs (se 1 (by rfl) ⟨41867, by rfl⟩) R83735
theorem R186947 : Reach 186947 := rs (se 1 (by rfl) ⟨140210, by rfl⟩) R280421
theorem R55943 : Reach 55943 := rs (se 1 (by rfl) ⟨41957, by rfl⟩) R83915
theorem R56009 : Reach 56009 := rs (se 2 (by rfl) ⟨21003, by rfl⟩) R42007
theorem R56123 : Reach 56123 := rs (se 1 (by rfl) ⟨42092, by rfl⟩) R84185
theorem R121715 : Reach 121715 := rs (se 1 (by rfl) ⟨91286, by rfl⟩) R182573
theorem R56183 : Reach 56183 := rs (se 1 (by rfl) ⟨42137, by rfl⟩) R84275
theorem R187271 : Reach 187271 := rs (se 1 (by rfl) ⟨140453, by rfl⟩) R280907
theorem R56249 : Reach 56249 := rs (se 2 (by rfl) ⟨21093, by rfl⟩) R42187
theorem R56363 : Reach 56363 := rs (se 1 (by rfl) ⟨42272, by rfl⟩) R84545
theorem R56591 : Reach 56591 := rs (se 1 (by rfl) ⟨42443, by rfl⟩) R84887
theorem R56711 : Reach 56711 := rs (se 1 (by rfl) ⟨42533, by rfl⟩) R85067
theorem R613817 : Reach 613817 := rs (se 2 (by rfl) ⟨230181, by rfl⟩) R460363
theorem R89545 : Reach 89545 := rs (se 2 (by rfl) ⟨33579, by rfl⟩) R67159
theorem R56777 : Reach 56777 := rs (se 2 (by rfl) ⟨21291, by rfl⟩) R42583
theorem R56891 : Reach 56891 := rs (se 1 (by rfl) ⟨42668, by rfl⟩) R85337
theorem R745037 : Reach 745037 := rs (se 3 (by rfl) ⟨139694, by rfl⟩) R279389
theorem R89687 : Reach 89687 := rs (se 1 (by rfl) ⟨67265, by rfl⟩) R134531
theorem R56951 : Reach 56951 := rs (se 1 (by rfl) ⟨42713, by rfl⟩) R85427
theorem R57017 : Reach 57017 := rs (se 2 (by rfl) ⟨21381, by rfl⟩) R42763
theorem R57131 : Reach 57131 := rs (se 1 (by rfl) ⟨42848, by rfl⟩) R85697
theorem R57359 : Reach 57359 := rs (se 1 (by rfl) ⟨43019, by rfl⟩) R86039
theorem R221251 : Reach 221251 := rs (se 1 (by rfl) ⟨165938, by rfl⟩) R331877
theorem R57479 : Reach 57479 := rs (se 1 (by rfl) ⟨43109, by rfl⟩) R86219
theorem R57545 : Reach 57545 := rs (se 2 (by rfl) ⟨21579, by rfl⟩) R43159
theorem R778481 : Reach 778481 := rs (se 2 (by rfl) ⟨291930, by rfl⟩) R583861
theorem R57659 : Reach 57659 := rs (se 1 (by rfl) ⟨43244, by rfl⟩) R86489
theorem R90487 : Reach 90487 := rs (se 1 (by rfl) ⟨67865, by rfl⟩) R135731
theorem R57719 : Reach 57719 := rs (se 1 (by rfl) ⟨43289, by rfl⟩) R86579
theorem R57785 : Reach 57785 := rs (se 2 (by rfl) ⟨21669, by rfl⟩) R43339
theorem R57899 : Reach 57899 := rs (se 1 (by rfl) ⟨43424, by rfl⟩) R86849
theorem R58127 : Reach 58127 := rs (se 1 (by rfl) ⟨43595, by rfl⟩) R87191
theorem R222041 : Reach 222041 := rs (se 2 (by rfl) ⟨83265, by rfl⟩) R166531
theorem R123763 : Reach 123763 := rs (se 1 (by rfl) ⟨92822, by rfl⟩) R185645
theorem R58247 : Reach 58247 := rs (se 1 (by rfl) ⟨43685, by rfl⟩) R87371
theorem R58313 : Reach 58313 := rs (se 2 (by rfl) ⟨21867, by rfl⟩) R43735
theorem R91151 : Reach 91151 := rs (se 1 (by rfl) ⟨68363, by rfl⟩) R136727
theorem R58427 : Reach 58427 := rs (se 1 (by rfl) ⟨43820, by rfl⟩) R87641
theorem R58487 : Reach 58487 := rs (se 1 (by rfl) ⟨43865, by rfl⟩) R87731
theorem R58553 : Reach 58553 := rs (se 2 (by rfl) ⟨21957, by rfl⟩) R43915
theorem R124105 : Reach 124105 := rs (se 2 (by rfl) ⟨46539, by rfl⟩) R93079
theorem R58667 : Reach 58667 := rs (se 1 (by rfl) ⟨44000, by rfl⟩) R88001
theorem R124307 : Reach 124307 := rs (se 1 (by rfl) ⟨93230, by rfl⟩) R186461
theorem R91649 : Reach 91649 := rs (se 2 (by rfl) ⟨34368, by rfl⟩) R68737
theorem R91763 : Reach 91763 := rs (se 1 (by rfl) ⟨68822, by rfl⟩) R137645
theorem R91795 : Reach 91795 := rs (se 1 (by rfl) ⟨68846, by rfl⟩) R137693
theorem R92279 : Reach 92279 := rs (se 1 (by rfl) ⟨69209, by rfl⟩) R138419
theorem R59663 : Reach 59663 := rs (se 1 (by rfl) ⟨44747, by rfl⟩) R89495
theorem R190835 : Reach 190835 := rs (se 1 (by rfl) ⟨143126, by rfl⟩) R286253
theorem R289169 : Reach 289169 := rs (se 2 (by rfl) ⟨108438, by rfl⟩) R216877
theorem R322001 : Reach 322001 := rs (se 2 (by rfl) ⟨120750, by rfl⟩) R241501
theorem R125711 : Reach 125711 := rs (se 1 (by rfl) ⟨94283, by rfl⟩) R188567
theorem R60203 : Reach 60203 := rs (se 1 (by rfl) ⟨45152, by rfl⟩) R90305
theorem R191321 : Reach 191321 := rs (se 2 (by rfl) ⟨71745, by rfl⟩) R143491
theorem R125981 : Reach 125981 := rs (se 3 (by rfl) ⟨23621, by rfl⟩) R47243
theorem R355373 : Reach 355373 := rs (se 3 (by rfl) ⟨66632, by rfl⟩) R133265
theorem R93271 : Reach 93271 := rs (se 1 (by rfl) ⟨69953, by rfl⟩) R139907
theorem R60601 : Reach 60601 := rs (se 2 (by rfl) ⟨22725, by rfl⟩) R45451
theorem R93575 : Reach 93575 := rs (se 1 (by rfl) ⟨70181, by rfl⟩) R140363
theorem R93707 : Reach 93707 := rs (se 1 (by rfl) ⟨70280, by rfl⟩) R140561
theorem R93757 : Reach 93757 := rs (se 3 (by rfl) ⟨17579, by rfl⟩) R35159
theorem R192293 : Reach 192293 := rs (se 4 (by rfl) ⟨18027, by rfl⟩) R36055
theorem R61303 : Reach 61303 := rs (se 1 (by rfl) ⟨45977, by rfl⟩) R91955
theorem R225227 : Reach 225227 := rs (se 1 (by rfl) ⟨168920, by rfl⟩) R337841
theorem R94223 : Reach 94223 := rs (se 1 (by rfl) ⟨70667, by rfl⟩) R141335
theorem R61499 : Reach 61499 := rs (se 1 (by rfl) ⟨46124, by rfl⟩) R92249
theorem R127037 : Reach 127037 := rs (se 3 (by rfl) ⟨23819, by rfl⟩) R47639
theorem R94355 : Reach 94355 := rs (se 1 (by rfl) ⟨70766, by rfl⟩) R141533
theorem R61739 : Reach 61739 := rs (se 1 (by rfl) ⟨46304, by rfl⟩) R92609
theorem R127385 : Reach 127385 := rs (se 2 (by rfl) ⟨47769, by rfl⟩) R95539
theorem R61897 : Reach 61897 := rs (se 2 (by rfl) ⟨23211, by rfl⟩) R46423
theorem R291599 : Reach 291599 := rs (se 1 (by rfl) ⟨218699, by rfl⟩) R437399
theorem R193427 : Reach 193427 := rs (se 1 (by rfl) ⟨145070, by rfl⟩) R290141
theorem R422819 : Reach 422819 := rs (se 1 (by rfl) ⟨317114, by rfl⟩) R634229
theorem R390167 : Reach 390167 := rs (se 1 (by rfl) ⟨292625, by rfl⟩) R585251
theorem R128087 : Reach 128087 := rs (se 1 (by rfl) ⟨96065, by rfl⟩) R192131
theorem R62599 : Reach 62599 := rs (se 1 (by rfl) ⟨46949, by rfl⟩) R93899
theorem R95489 : Reach 95489 := rs (se 2 (by rfl) ⟨35808, by rfl⟩) R71617
theorem R128465 : Reach 128465 := rs (se 2 (by rfl) ⟨48174, by rfl⟩) R96349
theorem R161291 : Reach 161291 := rs (se 1 (by rfl) ⟨120968, by rfl⟩) R241937
theorem R128573 : Reach 128573 := rs (se 3 (by rfl) ⟨24107, by rfl⟩) R48215
theorem R95863 : Reach 95863 := rs (se 1 (by rfl) ⟨71897, by rfl⟩) R143795
theorem R63247 : Reach 63247 := rs (se 1 (by rfl) ⟨47435, by rfl⟩) R94871
theorem R194363 : Reach 194363 := rs (se 1 (by rfl) ⟨145772, by rfl⟩) R291545
theorem R423755 : Reach 423755 := rs (se 1 (by rfl) ⟨317816, by rfl⟩) R635633
theorem R325579 : Reach 325579 := rs (se 1 (by rfl) ⟨244184, by rfl⟩) R488369
theorem R423883 : Reach 423883 := rs (se 1 (by rfl) ⟨317912, by rfl⟩) R635825
theorem R96299 : Reach 96299 := rs (se 1 (by rfl) ⟨72224, by rfl⟩) R144449
theorem R63547 : Reach 63547 := rs (se 1 (by rfl) ⟨47660, by rfl⟩) R95321
theorem R391405 : Reach 391405 := rs (se 3 (by rfl) ⟨73388, by rfl⟩) R146777
theorem R63787 : Reach 63787 := rs (se 1 (by rfl) ⟨47840, by rfl⟩) R95681
theorem R63929 : Reach 63929 := rs (se 2 (by rfl) ⟨23973, by rfl⟩) R47947
theorem R162233 : Reach 162233 := rs (se 2 (by rfl) ⟨60837, by rfl⟩) R121675
theorem R227843 : Reach 227843 := rs (se 1 (by rfl) ⟨170882, by rfl⟩) R341765
theorem R195139 : Reach 195139 := rs (se 1 (by rfl) ⟨146354, by rfl⟩) R292709
theorem R64201 : Reach 64201 := rs (se 2 (by rfl) ⟨24075, by rfl⟩) R48151
theorem R359129 : Reach 359129 := rs (se 2 (by rfl) ⟨134673, by rfl⟩) R269347
theorem R97139 : Reach 97139 := rs (se 1 (by rfl) ⟨72854, by rfl⟩) R145709
theorem R97159 : Reach 97159 := rs (se 1 (by rfl) ⟨72869, by rfl⟩) R145739
theorem R129977 : Reach 129977 := rs (se 2 (by rfl) ⟨48741, by rfl⟩) R97483
theorem R64631 : Reach 64631 := rs (se 1 (by rfl) ⟨48473, by rfl⟩) R96947
theorem R97433 : Reach 97433 := rs (se 2 (by rfl) ⟨36537, by rfl⟩) R73075
theorem R97481 : Reach 97481 := rs (se 2 (by rfl) ⟨36555, by rfl⟩) R73111
theorem R97595 : Reach 97595 := rs (se 1 (by rfl) ⟨73196, by rfl⟩) R146393
theorem R130439 : Reach 130439 := rs (se 1 (by rfl) ⟨97829, by rfl⟩) R195659
theorem R97793 : Reach 97793 := rs (se 2 (by rfl) ⟨36672, by rfl⟩) R73345
theorem R130571 : Reach 130571 := rs (se 1 (by rfl) ⟨97928, by rfl⟩) R195857
theorem R97807 : Reach 97807 := rs (se 1 (by rfl) ⟨73355, by rfl⟩) R146711
theorem R65083 : Reach 65083 := rs (se 1 (by rfl) ⟨48812, by rfl⟩) R97625
theorem R130679 : Reach 130679 := rs (se 1 (by rfl) ⟨98009, by rfl⟩) R196019
theorem R65171 : Reach 65171 := rs (se 1 (by rfl) ⟨48878, by rfl⟩) R97757
theorem R65225 : Reach 65225 := rs (se 2 (by rfl) ⟨24459, by rfl⟩) R48919
theorem R98081 : Reach 98081 := rs (se 2 (by rfl) ⟨36780, by rfl⟩) R73561
theorem R98135 : Reach 98135 := rs (se 1 (by rfl) ⟨73601, by rfl⟩) R147203
theorem R196505 : Reach 196505 := rs (se 2 (by rfl) ⟨73689, by rfl⟩) R147379
theorem R65575 : Reach 65575 := rs (se 1 (by rfl) ⟨49181, by rfl⟩) R98363
theorem R295001 : Reach 295001 := rs (se 2 (by rfl) ⟨110625, by rfl⟩) R221251
theorem R65785 : Reach 65785 := rs (se 2 (by rfl) ⟨24669, by rfl⟩) R49339
theorem R98779 : Reach 98779 := rs (se 1 (by rfl) ⟨74084, by rfl⟩) R148169
theorem R98825 : Reach 98825 := rs (se 2 (by rfl) ⟨37059, by rfl⟩) R74119
theorem R197153 : Reach 197153 := rs (se 2 (by rfl) ⟨73932, by rfl⟩) R147865
theorem R918539 : Reach 918539 := rs (se 1 (by rfl) ⟨688904, by rfl⟩) R1377809
theorem R361523 : Reach 361523 := rs (se 1 (by rfl) ⟨271142, by rfl⟩) R542285
theorem R590915 : Reach 590915 := rs (se 1 (by rfl) ⟨443186, by rfl⟩) R886373
theorem R197711 : Reach 197711 := rs (se 1 (by rfl) ⟨148283, by rfl⟩) R296567
theorem R165017 : Reach 165017 := rs (se 2 (by rfl) ⟨61881, by rfl⟩) R123763
theorem R361675 : Reach 361675 := rs (se 1 (by rfl) ⟨271256, by rfl⟩) R542513
theorem R66977 : Reach 66977 := rs (se 2 (by rfl) ⟨25116, by rfl⟩) R50233
theorem R296459 : Reach 296459 := rs (se 1 (by rfl) ⟨222344, by rfl⟩) R444689
theorem R165473 : Reach 165473 := rs (se 2 (by rfl) ⟨62052, by rfl⟩) R124105
theorem R67243 : Reach 67243 := rs (se 1 (by rfl) ⟨50432, by rfl⟩) R100865
theorem R100055 : Reach 100055 := rs (se 1 (by rfl) ⟨75041, by rfl⟩) R150083
theorem R67547 : Reach 67547 := rs (se 1 (by rfl) ⟨50660, by rfl⟩) R101321
theorem R854023 : Reach 854023 := rs (se 1 (by rfl) ⟨640517, by rfl⟩) R1281035
theorem R592109 : Reach 592109 := rs (se 3 (by rfl) ⟨111020, by rfl⟩) R222041
theorem R35151 : Reach 35151 := rs (se 1 (by rfl) ⟨26363, by rfl⟩) R52727
theorem R35167 : Reach 35167 := rs (se 1 (by rfl) ⟨26375, by rfl⟩) R52751
theorem R35195 : Reach 35195 := rs (se 1 (by rfl) ⟨26396, by rfl⟩) R52793
theorem R461207 : Reach 461207 := rs (se 1 (by rfl) ⟨345905, by rfl⟩) R691811
theorem R35247 : Reach 35247 := rs (se 1 (by rfl) ⟨26435, by rfl⟩) R52871
theorem R35271 : Reach 35271 := rs (se 1 (by rfl) ⟨26453, by rfl⟩) R52907
theorem R35291 : Reach 35291 := rs (se 1 (by rfl) ⟨26468, by rfl⟩) R52937
theorem R133613 : Reach 133613 := rs (se 3 (by rfl) ⟨25052, by rfl⟩) R50105
theorem R35367 : Reach 35367 := rs (se 1 (by rfl) ⟨26525, by rfl⟩) R53051
theorem R35407 : Reach 35407 := rs (se 1 (by rfl) ⟨26555, by rfl⟩) R53111
theorem R35423 : Reach 35423 := rs (se 1 (by rfl) ⟨26567, by rfl⟩) R53135
theorem R35451 : Reach 35451 := rs (se 1 (by rfl) ⟨26588, by rfl⟩) R53177
theorem R68219 : Reach 68219 := rs (se 1 (by rfl) ⟨51164, by rfl⟩) R102329
theorem R133771 : Reach 133771 := rs (se 1 (by rfl) ⟨100328, by rfl⟩) R200657
theorem R35503 : Reach 35503 := rs (se 1 (by rfl) ⟨26627, by rfl⟩) R53255
theorem R35527 : Reach 35527 := rs (se 1 (by rfl) ⟨26645, by rfl⟩) R53291
theorem R35547 : Reach 35547 := rs (se 1 (by rfl) ⟨26660, by rfl⟩) R53321
theorem R35623 : Reach 35623 := rs (se 1 (by rfl) ⟨26717, by rfl⟩) R53435
theorem R35663 : Reach 35663 := rs (se 1 (by rfl) ⟨26747, by rfl⟩) R53495
theorem R35679 : Reach 35679 := rs (se 1 (by rfl) ⟨26759, by rfl⟩) R53519
theorem R35707 : Reach 35707 := rs (se 1 (by rfl) ⟨26780, by rfl⟩) R53561
theorem R35759 : Reach 35759 := rs (se 1 (by rfl) ⟨26819, by rfl⟩) R53639
theorem R134075 : Reach 134075 := rs (se 1 (by rfl) ⟨100556, by rfl⟩) R201113
theorem R35783 : Reach 35783 := rs (se 1 (by rfl) ⟨26837, by rfl⟩) R53675
theorem R35803 : Reach 35803 := rs (se 1 (by rfl) ⟨26852, by rfl⟩) R53705
theorem R68617 : Reach 68617 := rs (se 2 (by rfl) ⟨25731, by rfl⟩) R51463
theorem R166931 : Reach 166931 := rs (se 1 (by rfl) ⟨125198, by rfl⟩) R250397
theorem R35879 : Reach 35879 := rs (se 1 (by rfl) ⟨26909, by rfl⟩) R53819
theorem R35919 : Reach 35919 := rs (se 1 (by rfl) ⟨26939, by rfl⟩) R53879
theorem R35935 : Reach 35935 := rs (se 1 (by rfl) ⟨26951, by rfl⟩) R53903
theorem R35963 : Reach 35963 := rs (se 1 (by rfl) ⟨26972, by rfl⟩) R53945
theorem R36015 : Reach 36015 := rs (se 1 (by rfl) ⟨27011, by rfl⟩) R54023
theorem R36039 : Reach 36039 := rs (se 1 (by rfl) ⟨27029, by rfl⟩) R54059
theorem R36059 : Reach 36059 := rs (se 1 (by rfl) ⟨27044, by rfl⟩) R54089
theorem R36135 : Reach 36135 := rs (se 1 (by rfl) ⟨27101, by rfl⟩) R54203
theorem R36175 : Reach 36175 := rs (se 1 (by rfl) ⟨27131, by rfl⟩) R54263
theorem R36191 : Reach 36191 := rs (se 1 (by rfl) ⟨27143, by rfl⟩) R54287
theorem R36219 : Reach 36219 := rs (se 1 (by rfl) ⟨27164, by rfl⟩) R54329
theorem R36271 : Reach 36271 := rs (se 1 (by rfl) ⟨27203, by rfl⟩) R54407
theorem R36295 : Reach 36295 := rs (se 1 (by rfl) ⟨27221, by rfl⟩) R54443
theorem R36315 : Reach 36315 := rs (se 1 (by rfl) ⟨27236, by rfl⟩) R54473
theorem R36391 : Reach 36391 := rs (se 1 (by rfl) ⟨27293, by rfl⟩) R54587
theorem R36431 : Reach 36431 := rs (se 1 (by rfl) ⟨27323, by rfl⟩) R54647
theorem R36447 : Reach 36447 := rs (se 1 (by rfl) ⟨27335, by rfl⟩) R54671
theorem R36475 : Reach 36475 := rs (se 1 (by rfl) ⟨27356, by rfl⟩) R54713
theorem R200339 : Reach 200339 := rs (se 1 (by rfl) ⟨150254, by rfl⟩) R300509
theorem R36527 : Reach 36527 := rs (se 1 (by rfl) ⟨27395, by rfl⟩) R54791
theorem R36551 : Reach 36551 := rs (se 1 (by rfl) ⟨27413, by rfl⟩) R54827
theorem R69331 : Reach 69331 := rs (se 1 (by rfl) ⟨51998, by rfl⟩) R103997
theorem R36571 : Reach 36571 := rs (se 1 (by rfl) ⟨27428, by rfl⟩) R54857
theorem R36647 : Reach 36647 := rs (se 1 (by rfl) ⟨27485, by rfl⟩) R54971
theorem R36687 : Reach 36687 := rs (se 1 (by rfl) ⟨27515, by rfl⟩) R55031
theorem R36703 : Reach 36703 := rs (se 1 (by rfl) ⟨27527, by rfl⟩) R55055
theorem R36731 : Reach 36731 := rs (se 1 (by rfl) ⟨27548, by rfl⟩) R55097
theorem R36783 : Reach 36783 := rs (se 1 (by rfl) ⟨27587, by rfl⟩) R55175
theorem R36807 : Reach 36807 := rs (se 1 (by rfl) ⟨27605, by rfl⟩) R55211
theorem R36827 : Reach 36827 := rs (se 1 (by rfl) ⟨27620, by rfl⟩) R55241
theorem R430109 : Reach 430109 := rs (se 3 (by rfl) ⟨80645, by rfl⟩) R161291
theorem R36903 : Reach 36903 := rs (se 1 (by rfl) ⟨27677, by rfl⟩) R55355
theorem R36943 : Reach 36943 := rs (se 1 (by rfl) ⟨27707, by rfl⟩) R55415
theorem R36959 : Reach 36959 := rs (se 1 (by rfl) ⟨27719, by rfl⟩) R55439
theorem R135283 : Reach 135283 := rs (se 1 (by rfl) ⟨101462, by rfl⟩) R202925
theorem R36987 : Reach 36987 := rs (se 1 (by rfl) ⟨27740, by rfl⟩) R55481
theorem R37063 : Reach 37063 := rs (se 1 (by rfl) ⟨27797, by rfl⟩) R55595
theorem R37215 : Reach 37215 := rs (se 1 (by rfl) ⟨27911, by rfl⟩) R55823
theorem R37295 : Reach 37295 := rs (se 1 (by rfl) ⟨27971, by rfl⟩) R55943
theorem R70075 : Reach 70075 := rs (se 1 (by rfl) ⟨52556, by rfl⟩) R105113
theorem R37339 : Reach 37339 := rs (se 1 (by rfl) ⟨28004, by rfl⟩) R56009
theorem R37415 : Reach 37415 := rs (se 1 (by rfl) ⟨28061, by rfl⟩) R56123
theorem R37455 : Reach 37455 := rs (se 1 (by rfl) ⟨28091, by rfl⟩) R56183
theorem R37499 : Reach 37499 := rs (se 1 (by rfl) ⟨28124, by rfl⟩) R56249
theorem R37575 : Reach 37575 := rs (se 1 (by rfl) ⟨28181, by rfl⟩) R56363
theorem R37727 : Reach 37727 := rs (se 1 (by rfl) ⟨28295, by rfl⟩) R56591
theorem R70561 : Reach 70561 := rs (se 2 (by rfl) ⟨26460, by rfl⟩) R52921
theorem R37807 : Reach 37807 := rs (se 1 (by rfl) ⟨28355, by rfl⟩) R56711
theorem R37851 : Reach 37851 := rs (se 1 (by rfl) ⟨28388, by rfl⟩) R56777
theorem R332801 : Reach 332801 := rs (se 2 (by rfl) ⟨124800, by rfl⟩) R249601
theorem R332819 : Reach 332819 := rs (se 1 (by rfl) ⟨249614, by rfl⟩) R499229
theorem R37927 : Reach 37927 := rs (se 1 (by rfl) ⟨28445, by rfl⟩) R56891
theorem R496691 : Reach 496691 := rs (se 1 (by rfl) ⟨372518, by rfl⟩) R745037
theorem R37967 : Reach 37967 := rs (se 1 (by rfl) ⟨28475, by rfl⟩) R56951
theorem R38011 : Reach 38011 := rs (se 1 (by rfl) ⟨28508, by rfl⟩) R57017
theorem R38087 : Reach 38087 := rs (se 1 (by rfl) ⟨28565, by rfl⟩) R57131
theorem R38239 : Reach 38239 := rs (se 1 (by rfl) ⟨28679, by rfl⟩) R57359
theorem R38319 : Reach 38319 := rs (se 1 (by rfl) ⟨28739, by rfl⟩) R57479
theorem R71131 : Reach 71131 := rs (se 1 (by rfl) ⟨53348, by rfl⟩) R106697
theorem R136667 : Reach 136667 := rs (se 1 (by rfl) ⟨102500, by rfl⟩) R205001
theorem R38363 : Reach 38363 := rs (se 1 (by rfl) ⟨28772, by rfl⟩) R57545
theorem R38439 : Reach 38439 := rs (se 1 (by rfl) ⟨28829, by rfl⟩) R57659
theorem R38479 : Reach 38479 := rs (se 1 (by rfl) ⟨28859, by rfl⟩) R57719
theorem R398945 : Reach 398945 := rs (se 2 (by rfl) ⟨149604, by rfl⟩) R299209
theorem R38523 : Reach 38523 := rs (se 1 (by rfl) ⟨28892, by rfl⟩) R57785
theorem R38599 : Reach 38599 := rs (se 1 (by rfl) ⟨28949, by rfl⟩) R57899
theorem R38751 : Reach 38751 := rs (se 1 (by rfl) ⟨29063, by rfl⟩) R58127
theorem R38831 : Reach 38831 := rs (se 1 (by rfl) ⟨29123, by rfl⟩) R58247
theorem R38875 : Reach 38875 := rs (se 1 (by rfl) ⟨29156, by rfl⟩) R58313
theorem R333827 : Reach 333827 := rs (se 1 (by rfl) ⟨250370, by rfl⟩) R500741
theorem R38951 : Reach 38951 := rs (se 1 (by rfl) ⟨29213, by rfl⟩) R58427
theorem R38991 : Reach 38991 := rs (se 1 (by rfl) ⟨29243, by rfl⟩) R58487
theorem R39035 : Reach 39035 := rs (se 1 (by rfl) ⟨29276, by rfl⟩) R58553
theorem R39111 : Reach 39111 := rs (se 1 (by rfl) ⟨29333, by rfl⟩) R58667
theorem R39775 : Reach 39775 := rs (se 1 (by rfl) ⟨29831, by rfl⟩) R59663
theorem R138145 : Reach 138145 := rs (se 2 (by rfl) ⟨51804, by rfl⟩) R103609
theorem R40135 : Reach 40135 := rs (se 1 (by rfl) ⟨30101, by rfl⟩) R60203
theorem R236915 : Reach 236915 := rs (se 1 (by rfl) ⟨177686, by rfl⟩) R355373
theorem R73235 : Reach 73235 := rs (se 1 (by rfl) ⟨54926, by rfl⟩) R109853
theorem R73295 : Reach 73295 := rs (se 1 (by rfl) ⟨54971, by rfl⟩) R109943
theorem R139103 : Reach 139103 := rs (se 1 (by rfl) ⟨104327, by rfl⟩) R208655
theorem R139117 : Reach 139117 := rs (se 3 (by rfl) ⟨26084, by rfl⟩) R52169
theorem R270215 : Reach 270215 := rs (se 1 (by rfl) ⟨202661, by rfl⟩) R405323
theorem R434105 : Reach 434105 := rs (se 2 (by rfl) ⟨162789, by rfl⟩) R325579
theorem R565177 : Reach 565177 := rs (se 2 (by rfl) ⟨211941, by rfl⟩) R423883
theorem R40999 : Reach 40999 := rs (se 1 (by rfl) ⟨30749, by rfl⟩) R61499
theorem R139421 : Reach 139421 := rs (se 3 (by rfl) ⟨26141, by rfl⟩) R52283
theorem R41159 : Reach 41159 := rs (se 1 (by rfl) ⟨30869, by rfl⟩) R61739
theorem R140075 : Reach 140075 := rs (se 1 (by rfl) ⟨105056, by rfl⟩) R210113
theorem R140345 : Reach 140345 := rs (se 2 (by rfl) ⟨52629, by rfl⟩) R105259
theorem R533749 : Reach 533749 := rs (se 5 (by rfl) ⟨25019, by rfl⟩) R50039
theorem R271781 : Reach 271781 := rs (se 4 (by rfl) ⟨25479, by rfl⟩) R50959
theorem R42619 : Reach 42619 := rs (se 1 (by rfl) ⟨31964, by rfl⟩) R63929
theorem R108155 : Reach 108155 := rs (se 1 (by rfl) ⟨81116, by rfl⟩) R162233
theorem R239419 : Reach 239419 := rs (se 1 (by rfl) ⟨179564, by rfl⟩) R359129
theorem R43087 : Reach 43087 := rs (se 1 (by rfl) ⟨32315, by rfl⟩) R64631
theorem R272641 : Reach 272641 := rs (se 2 (by rfl) ⟨102240, by rfl⟩) R204481
theorem R403865 : Reach 403865 := rs (se 2 (by rfl) ⟨151449, by rfl⟩) R302899
theorem R43447 : Reach 43447 := rs (se 1 (by rfl) ⟨32585, by rfl⟩) R65171
theorem R43483 : Reach 43483 := rs (se 1 (by rfl) ⟨32612, by rfl⟩) R65225
theorem R600605 : Reach 600605 := rs (se 3 (by rfl) ⟨112613, by rfl⟩) R225227
theorem R535085 : Reach 535085 := rs (se 3 (by rfl) ⟨100328, by rfl⟩) R200657
theorem R142033 : Reach 142033 := rs (se 2 (by rfl) ⟨53262, by rfl⟩) R106525
theorem R43951 : Reach 43951 := rs (se 1 (by rfl) ⟨32963, by rfl⟩) R65927
theorem R109487 : Reach 109487 := rs (se 1 (by rfl) ⟨82115, by rfl⟩) R164231
theorem R338917 : Reach 338917 := rs (se 4 (by rfl) ⟨31773, by rfl⟩) R63547
theorem R142337 : Reach 142337 := rs (se 2 (by rfl) ⟨53376, by rfl⟩) R106753
theorem R240707 : Reach 240707 := rs (se 1 (by rfl) ⟨180530, by rfl⟩) R361061
theorem R76879 : Reach 76879 := rs (se 1 (by rfl) ⟨57659, by rfl⟩) R115319
theorem R142793 : Reach 142793 := rs (se 2 (by rfl) ⟨53547, by rfl⟩) R107095
theorem R143147 : Reach 143147 := rs (se 1 (by rfl) ⟨107360, by rfl⟩) R214721
theorem R110497 : Reach 110497 := rs (se 2 (by rfl) ⟨41436, by rfl⟩) R82873
theorem R44975 : Reach 44975 := rs (se 1 (by rfl) ⟨33731, by rfl⟩) R67463
theorem R143279 : Reach 143279 := rs (se 1 (by rfl) ⟨107459, by rfl⟩) R214919
theorem R274589 : Reach 274589 := rs (se 3 (by rfl) ⟨51485, by rfl⟩) R102971
theorem R537299 : Reach 537299 := rs (se 1 (by rfl) ⟨402974, by rfl⟩) R805949
theorem R144463 : Reach 144463 := rs (se 1 (by rfl) ⟨108347, by rfl⟩) R216695
theorem R79019 : Reach 79019 := rs (se 1 (by rfl) ⟨59264, by rfl⟩) R118529
theorem R603611 : Reach 603611 := rs (se 1 (by rfl) ⟨452708, by rfl⟩) R905417
theorem R144935 : Reach 144935 := rs (se 1 (by rfl) ⟨108701, by rfl⟩) R217403
theorem R112313 : Reach 112313 := rs (se 2 (by rfl) ⟨42117, by rfl⟩) R84235
theorem R79559 : Reach 79559 := rs (se 1 (by rfl) ⟨59669, by rfl⟩) R119339
theorem R243665 : Reach 243665 := rs (se 2 (by rfl) ⟨91374, by rfl⟩) R182749
theorem R80347 : Reach 80347 := rs (se 1 (by rfl) ⟨60260, by rfl⟩) R120521
theorem R145907 : Reach 145907 := rs (se 1 (by rfl) ⟨109430, by rfl⟩) R218861
theorem R80423 : Reach 80423 := rs (se 1 (by rfl) ⟨60317, by rfl⟩) R120635
theorem R244397 : Reach 244397 := rs (se 3 (by rfl) ⟨45824, by rfl⟩) R91649
theorem R80747 : Reach 80747 := rs (se 1 (by rfl) ⟨60560, by rfl⟩) R121121
theorem R80801 : Reach 80801 := rs (se 2 (by rfl) ⟨30300, by rfl⟩) R60601
theorem R342967 : Reach 342967 := rs (se 1 (by rfl) ⟨257225, by rfl⟩) R514451
theorem R277505 : Reach 277505 := rs (se 2 (by rfl) ⟨104064, by rfl⟩) R208129
theorem R81143 : Reach 81143 := rs (se 1 (by rfl) ⟨60857, by rfl⟩) R121715
theorem R48377 : Reach 48377 := rs (se 2 (by rfl) ⟨18141, by rfl⟩) R36283
theorem R441773 : Reach 441773 := rs (se 3 (by rfl) ⟨82832, by rfl⟩) R165665
theorem R179657 : Reach 179657 := rs (se 2 (by rfl) ⟨67371, by rfl⟩) R134743
theorem R409211 : Reach 409211 := rs (se 1 (by rfl) ⟨306908, by rfl⟩) R613817
theorem R638603 : Reach 638603 := rs (se 1 (by rfl) ⟨478952, by rfl⟩) R957905
theorem R147133 : Reach 147133 := rs (se 3 (by rfl) ⟨27587, by rfl⟩) R55175
theorem R81737 : Reach 81737 := rs (se 2 (by rfl) ⟨30651, by rfl⟩) R61303
theorem R213029 : Reach 213029 := rs (se 4 (by rfl) ⟨19971, by rfl⟩) R39943
theorem R114767 : Reach 114767 := rs (se 1 (by rfl) ⟨86075, by rfl⟩) R172151
theorem R180305 : Reach 180305 := rs (se 2 (by rfl) ⟨67614, by rfl⟩) R135229
theorem R82529 : Reach 82529 := rs (se 2 (by rfl) ⟨30948, by rfl⟩) R61897
theorem R836527 : Reach 836527 := rs (se 1 (by rfl) ⟨627395, by rfl⟩) R1254791
theorem R82871 : Reach 82871 := rs (se 1 (by rfl) ⟨62153, by rfl⟩) R124307
theorem R247063 : Reach 247063 := rs (se 1 (by rfl) ⟨185297, by rfl⟩) R370595
theorem R83465 : Reach 83465 := rs (se 2 (by rfl) ⟨31299, by rfl⟩) R62599
theorem R214667 : Reach 214667 := rs (se 1 (by rfl) ⟨161000, by rfl⟩) R322001
theorem R83807 : Reach 83807 := rs (se 1 (by rfl) ⟨62855, by rfl⟩) R125711
theorem R411601 : Reach 411601 := rs (se 2 (by rfl) ⟨154350, by rfl⟩) R308701
theorem R247823 : Reach 247823 := rs (se 1 (by rfl) ⟨185867, by rfl⟩) R371735
theorem R83987 : Reach 83987 := rs (se 1 (by rfl) ⟨62990, by rfl⟩) R125981
theorem R84329 : Reach 84329 := rs (se 2 (by rfl) ⟨31623, by rfl⟩) R63247
theorem R51835 : Reach 51835 := rs (se 1 (by rfl) ⟨38876, by rfl⟩) R77753
theorem R84691 : Reach 84691 := rs (se 1 (by rfl) ⟨63518, by rfl⟩) R127037
theorem R84923 : Reach 84923 := rs (se 1 (by rfl) ⟨63692, by rfl⟩) R127385
theorem R85049 : Reach 85049 := rs (se 2 (by rfl) ⟨31893, by rfl⟩) R63787
theorem R281879 : Reach 281879 := rs (se 1 (by rfl) ⟨211409, by rfl⟩) R422819
theorem R85391 : Reach 85391 := rs (se 1 (by rfl) ⟨64043, by rfl⟩) R128087
theorem R970157 : Reach 970157 := rs (se 3 (by rfl) ⟨181904, by rfl⟩) R363809
theorem R118235 : Reach 118235 := rs (se 1 (by rfl) ⟨88676, by rfl⟩) R177353
theorem R52745 : Reach 52745 := rs (se 2 (by rfl) ⟨19779, by rfl⟩) R39559
theorem R52775 : Reach 52775 := rs (se 1 (by rfl) ⟨39581, by rfl⟩) R79163
theorem R118331 : Reach 118331 := rs (se 1 (by rfl) ⟨88748, by rfl⟩) R177497
theorem R85601 : Reach 85601 := rs (se 2 (by rfl) ⟨32100, by rfl⟩) R64201
theorem R52859 : Reach 52859 := rs (se 1 (by rfl) ⟨39644, by rfl⟩) R79289
theorem R85643 : Reach 85643 := rs (se 1 (by rfl) ⟨64232, by rfl⟩) R128465
theorem R85715 : Reach 85715 := rs (se 1 (by rfl) ⟨64286, by rfl⟩) R128573
theorem R52985 : Reach 52985 := rs (se 2 (by rfl) ⟨19869, by rfl⟩) R39739
theorem R53087 : Reach 53087 := rs (se 1 (by rfl) ⟨39815, by rfl⟩) R79631
theorem R53099 : Reach 53099 := rs (se 1 (by rfl) ⟨39824, by rfl⟩) R79649
theorem R282503 : Reach 282503 := rs (se 1 (by rfl) ⟨211877, by rfl⟩) R423755
theorem R118799 : Reach 118799 := rs (se 1 (by rfl) ⟨89099, by rfl⟩) R178199
theorem R53327 : Reach 53327 := rs (se 1 (by rfl) ⟨39995, by rfl⟩) R79991
theorem R53447 : Reach 53447 := rs (se 1 (by rfl) ⟨40085, by rfl⟩) R80171
theorem R151895 : Reach 151895 := rs (se 1 (by rfl) ⟨113921, by rfl⟩) R227843
theorem R53609 : Reach 53609 := rs (se 2 (by rfl) ⟨20103, by rfl⟩) R40207
theorem R53687 : Reach 53687 := rs (se 1 (by rfl) ⟨40265, by rfl⟩) R80531
theorem R53723 : Reach 53723 := rs (se 1 (by rfl) ⟨40292, by rfl⟩) R80585
theorem R184841 : Reach 184841 := rs (se 2 (by rfl) ⟨69315, by rfl⟩) R138631
theorem R119393 : Reach 119393 := rs (se 2 (by rfl) ⟨44772, by rfl⟩) R89545
theorem R86651 : Reach 86651 := rs (se 1 (by rfl) ⟨64988, by rfl⟩) R129977
theorem R119431 : Reach 119431 := rs (se 1 (by rfl) ⟨89573, by rfl⟩) R179147
theorem R283337 : Reach 283337 := rs (se 2 (by rfl) ⟨106251, by rfl⟩) R212503
theorem R86777 : Reach 86777 := rs (se 2 (by rfl) ⟨32541, by rfl⟩) R65083
theorem R1495907 : Reach 1495907 := rs (se 1 (by rfl) ⟨1121930, by rfl⟩) R2243861
theorem R54191 : Reach 54191 := rs (se 1 (by rfl) ⟨40643, by rfl⟩) R81287
theorem R86959 : Reach 86959 := rs (se 1 (by rfl) ⟨65219, by rfl⟩) R130439
theorem R87047 : Reach 87047 := rs (se 1 (by rfl) ⟨65285, by rfl⟩) R130571
theorem R54281 : Reach 54281 := rs (se 2 (by rfl) ⟨20355, by rfl⟩) R40711
theorem R54311 : Reach 54311 := rs (se 1 (by rfl) ⟨40733, by rfl⟩) R81467
theorem R87119 : Reach 87119 := rs (se 1 (by rfl) ⟨65339, by rfl⟩) R130679
theorem R54395 : Reach 54395 := rs (se 1 (by rfl) ⟨40796, by rfl⟩) R81593
theorem R54521 : Reach 54521 := rs (se 2 (by rfl) ⟨20445, by rfl⟩) R40891
theorem R54623 : Reach 54623 := rs (se 1 (by rfl) ⟨40967, by rfl⟩) R81935
theorem R54635 : Reach 54635 := rs (se 1 (by rfl) ⟨40976, by rfl⟩) R81953
theorem R87425 : Reach 87425 := rs (se 2 (by rfl) ⟨32784, by rfl⟩) R65569
theorem R87515 : Reach 87515 := rs (se 1 (by rfl) ⟨65636, by rfl⟩) R131273
theorem R54863 : Reach 54863 := rs (se 1 (by rfl) ⟨41147, by rfl⟩) R82295
theorem R153211 : Reach 153211 := rs (se 1 (by rfl) ⟨114908, by rfl⟩) R229817
theorem R153227 : Reach 153227 := rs (se 1 (by rfl) ⟨114920, by rfl⟩) R229841
theorem R54983 : Reach 54983 := rs (se 1 (by rfl) ⟨41237, by rfl⟩) R82475
theorem R87767 : Reach 87767 := rs (se 1 (by rfl) ⟨65825, by rfl⟩) R131651
theorem R55145 : Reach 55145 := rs (se 2 (by rfl) ⟨20679, by rfl⟩) R41359
theorem R87983 : Reach 87983 := rs (se 1 (by rfl) ⟨65987, by rfl⟩) R131975
theorem R55223 : Reach 55223 := rs (se 1 (by rfl) ⟨41417, by rfl⟩) R82835
theorem R186299 : Reach 186299 := rs (se 1 (by rfl) ⟨139724, by rfl⟩) R279449
theorem R55259 : Reach 55259 := rs (se 1 (by rfl) ⟨41444, by rfl⟩) R82889
theorem R120851 : Reach 120851 := rs (se 1 (by rfl) ⟨90638, by rfl⟩) R181277
theorem R350365 : Reach 350365 := rs (se 3 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R219293 : Reach 219293 := rs (se 3 (by rfl) ⟨41117, by rfl⟩) R82235
theorem R55495 : Reach 55495 := rs (se 1 (by rfl) ⟨41621, by rfl⟩) R83243
theorem R55625 : Reach 55625 := rs (se 2 (by rfl) ⟨20859, by rfl⟩) R41719
theorem R121175 : Reach 121175 := rs (se 1 (by rfl) ⟨90881, by rfl⟩) R181763
theorem R55727 : Reach 55727 := rs (se 1 (by rfl) ⟨41795, by rfl⟩) R83591
theorem R55739 : Reach 55739 := rs (se 1 (by rfl) ⟨41804, by rfl⟩) R83609
theorem R55817 : Reach 55817 := rs (se 2 (by rfl) ⟨20931, by rfl⟩) R41863
theorem R55847 : Reach 55847 := rs (se 1 (by rfl) ⟨41885, by rfl⟩) R83771
theorem R55865 : Reach 55865 := rs (se 2 (by rfl) ⟨20949, by rfl⟩) R41899
theorem R55931 : Reach 55931 := rs (se 1 (by rfl) ⟨41948, by rfl⟩) R83897
theorem R55979 : Reach 55979 := rs (se 1 (by rfl) ⟨41984, by rfl⟩) R83969
theorem R56057 : Reach 56057 := rs (se 2 (by rfl) ⟨21021, by rfl⟩) R42043
theorem R56159 : Reach 56159 := rs (se 1 (by rfl) ⟨42119, by rfl⟩) R84239
theorem R56171 : Reach 56171 := rs (se 1 (by rfl) ⟨42128, by rfl⟩) R84257
theorem R56207 : Reach 56207 := rs (se 1 (by rfl) ⟨42155, by rfl⟩) R84311
theorem R56327 : Reach 56327 := rs (se 1 (by rfl) ⟨42245, by rfl⟩) R84491
theorem R56399 : Reach 56399 := rs (se 1 (by rfl) ⟨42299, by rfl⟩) R84599
theorem R56519 : Reach 56519 := rs (se 1 (by rfl) ⟨42389, by rfl⟩) R84779
theorem R187595 : Reach 187595 := rs (se 1 (by rfl) ⟨140696, by rfl⟩) R281393
theorem R56567 : Reach 56567 := rs (se 1 (by rfl) ⟨42425, by rfl⟩) R84851
theorem R122123 : Reach 122123 := rs (se 1 (by rfl) ⟨91592, by rfl⟩) R183185
theorem R482597 : Reach 482597 := rs (se 4 (by rfl) ⟨45243, by rfl⟩) R90487
theorem R56681 : Reach 56681 := rs (se 2 (by rfl) ⟨21255, by rfl⟩) R42511
theorem R253327 : Reach 253327 := rs (se 1 (by rfl) ⟨189995, by rfl⟩) R379991
theorem R122255 : Reach 122255 := rs (se 1 (by rfl) ⟨91691, by rfl⟩) R183383
theorem R56759 : Reach 56759 := rs (se 1 (by rfl) ⟨42569, by rfl⟩) R85139
theorem R155081 : Reach 155081 := rs (se 2 (by rfl) ⟨58155, by rfl⟩) R116311
theorem R56795 : Reach 56795 := rs (se 1 (by rfl) ⟨42596, by rfl⟩) R85193
theorem R122393 : Reach 122393 := rs (se 2 (by rfl) ⟨45897, by rfl⟩) R91795
theorem R122579 : Reach 122579 := rs (se 1 (by rfl) ⟨91934, by rfl⟩) R183869
theorem R89849 : Reach 89849 := rs (se 2 (by rfl) ⟨33693, by rfl⟩) R67387
theorem R57161 : Reach 57161 := rs (se 2 (by rfl) ⟨21435, by rfl⟩) R42871
theorem R221089 : Reach 221089 := rs (se 2 (by rfl) ⟨82908, by rfl⟩) R165817
theorem R90031 : Reach 90031 := rs (se 1 (by rfl) ⟨67523, by rfl⟩) R135047
theorem R57263 : Reach 57263 := rs (se 1 (by rfl) ⟨42947, by rfl⟩) R85895
theorem R57275 : Reach 57275 := rs (se 1 (by rfl) ⟨42956, by rfl⟩) R85913
theorem R57353 : Reach 57353 := rs (se 2 (by rfl) ⟨21507, by rfl⟩) R43015
theorem R57383 : Reach 57383 := rs (se 1 (by rfl) ⟨43037, by rfl⟩) R86075
theorem R57401 : Reach 57401 := rs (se 2 (by rfl) ⟨21525, by rfl⟩) R43051
theorem R57467 : Reach 57467 := rs (se 1 (by rfl) ⟨43100, by rfl⟩) R86201
theorem R57515 : Reach 57515 := rs (se 1 (by rfl) ⟨43136, by rfl⟩) R86273
theorem R57593 : Reach 57593 := rs (se 2 (by rfl) ⟨21597, by rfl⟩) R43195
theorem R155915 : Reach 155915 := rs (se 1 (by rfl) ⟨116936, by rfl⟩) R233873
theorem R57695 : Reach 57695 := rs (se 1 (by rfl) ⟨43271, by rfl⟩) R86543
theorem R57707 : Reach 57707 := rs (se 1 (by rfl) ⟨43280, by rfl⟩) R86561
theorem R90497 : Reach 90497 := rs (se 2 (by rfl) ⟨33936, by rfl⟩) R67873
theorem R57743 : Reach 57743 := rs (se 1 (by rfl) ⟨43307, by rfl⟩) R86615
theorem R57863 : Reach 57863 := rs (se 1 (by rfl) ⟨43397, by rfl⟩) R86795
theorem R57935 : Reach 57935 := rs (se 1 (by rfl) ⟨43451, by rfl⟩) R86903
theorem R58055 : Reach 58055 := rs (se 1 (by rfl) ⟨43541, by rfl⟩) R87083
theorem R58103 : Reach 58103 := rs (se 1 (by rfl) ⟨43577, by rfl⟩) R87155
theorem R90953 : Reach 90953 := rs (se 2 (by rfl) ⟨34107, by rfl⟩) R68215
theorem R58217 : Reach 58217 := rs (se 2 (by rfl) ⟨21831, by rfl⟩) R43663
theorem R123767 : Reach 123767 := rs (se 1 (by rfl) ⟨92825, by rfl⟩) R185651
theorem R58295 : Reach 58295 := rs (se 1 (by rfl) ⟨43721, by rfl⟩) R87443
theorem R58331 : Reach 58331 := rs (se 1 (by rfl) ⟨43748, by rfl⟩) R87497
theorem R222209 : Reach 222209 := rs (se 2 (by rfl) ⟨83328, by rfl⟩) R166657
theorem R123983 : Reach 123983 := rs (se 1 (by rfl) ⟨92987, by rfl⟩) R185975
theorem R91307 : Reach 91307 := rs (se 1 (by rfl) ⟨68480, by rfl⟩) R136961
theorem R91535 : Reach 91535 := rs (se 1 (by rfl) ⟨68651, by rfl⟩) R137303
theorem R124361 : Reach 124361 := rs (se 2 (by rfl) ⟨46635, by rfl⟩) R93271
theorem R124379 : Reach 124379 := rs (se 1 (by rfl) ⟨93284, by rfl⟩) R186569
theorem R124631 : Reach 124631 := rs (se 1 (by rfl) ⟨93473, by rfl⟩) R186947
theorem R157601 : Reach 157601 := rs (se 2 (by rfl) ⟨59100, by rfl⟩) R118201
theorem R124847 : Reach 124847 := rs (se 1 (by rfl) ⟨93635, by rfl⟩) R187271
theorem R92087 : Reach 92087 := rs (se 1 (by rfl) ⟨69065, by rfl⟩) R138131
theorem R223163 : Reach 223163 := rs (se 1 (by rfl) ⟨167372, by rfl⟩) R334745
theorem R1894337 : Reach 1894337 := rs (se 2 (by rfl) ⟨710376, by rfl⟩) R1420753
theorem R125009 : Reach 125009 := rs (se 2 (by rfl) ⟨46878, by rfl⟩) R93757
theorem R59791 : Reach 59791 := rs (se 1 (by rfl) ⟨44843, by rfl⟩) R89687
theorem R518987 : Reach 518987 := rs (se 1 (by rfl) ⟨389240, by rfl⟩) R778481
theorem R93089 : Reach 93089 := rs (se 2 (by rfl) ⟨34908, by rfl⟩) R69817
theorem R60473 : Reach 60473 := rs (se 2 (by rfl) ⟨22677, by rfl⟩) R45355
theorem R60767 : Reach 60767 := rs (se 1 (by rfl) ⟨45575, by rfl⟩) R91151
theorem R93545 : Reach 93545 := rs (se 2 (by rfl) ⟨35079, by rfl⟩) R70159
theorem R61175 : Reach 61175 := rs (se 1 (by rfl) ⟨45881, by rfl⟩) R91763
theorem R61177 : Reach 61177 := rs (se 2 (by rfl) ⟨22941, by rfl⟩) R45883
theorem R290627 : Reach 290627 := rs (se 1 (by rfl) ⟨217970, by rfl⟩) R435941
theorem R159583 : Reach 159583 := rs (se 1 (by rfl) ⟨119687, by rfl⟩) R239375
theorem R61519 : Reach 61519 := rs (se 1 (by rfl) ⟨46139, by rfl⟩) R92279
theorem R127223 : Reach 127223 := rs (se 1 (by rfl) ⟨95417, by rfl⟩) R190835
theorem R192779 : Reach 192779 := rs (se 1 (by rfl) ⟨144584, by rfl⟩) R289169
theorem R61769 : Reach 61769 := rs (se 2 (by rfl) ⟨23163, by rfl⟩) R46327
theorem R225665 : Reach 225665 := rs (se 2 (by rfl) ⟨84624, by rfl⟩) R169249
theorem R94729 : Reach 94729 := rs (se 2 (by rfl) ⟨35523, by rfl⟩) R71047
theorem R127547 : Reach 127547 := rs (se 1 (by rfl) ⟨95660, by rfl⟩) R191321
theorem R62201 : Reach 62201 := rs (se 2 (by rfl) ⟨23325, by rfl⟩) R46651
theorem R881425 : Reach 881425 := rs (se 2 (by rfl) ⟨330534, by rfl⟩) R661069
theorem R160541 : Reach 160541 := rs (se 3 (by rfl) ⟨30101, by rfl⟩) R60203
theorem R127817 : Reach 127817 := rs (se 2 (by rfl) ⟨47931, by rfl⟩) R95863
theorem R62383 : Reach 62383 := rs (se 1 (by rfl) ⟨46787, by rfl⟩) R93575
theorem R62471 : Reach 62471 := rs (se 1 (by rfl) ⟨46853, by rfl⟩) R93707
theorem R128195 : Reach 128195 := rs (se 1 (by rfl) ⟨96146, by rfl⟩) R192293
theorem R488693 : Reach 488693 := rs (se 5 (by rfl) ⟨22907, by rfl⟩) R45815
theorem R62815 : Reach 62815 := rs (se 1 (by rfl) ⟨47111, by rfl⟩) R94223
theorem R62903 : Reach 62903 := rs (se 1 (by rfl) ⟨47177, by rfl⟩) R94355
theorem R521873 : Reach 521873 := rs (se 2 (by rfl) ⟨195702, by rfl⟩) R391405
theorem R194237 : Reach 194237 := rs (se 3 (by rfl) ⟨36419, by rfl⟩) R72839
theorem R194399 : Reach 194399 := rs (se 1 (by rfl) ⟨145799, by rfl⟩) R291599
theorem R259949 : Reach 259949 := rs (se 3 (by rfl) ⟨48740, by rfl⟩) R97481
theorem R128951 : Reach 128951 := rs (se 1 (by rfl) ⟨96713, by rfl⟩) R193427
theorem R96187 : Reach 96187 := rs (se 1 (by rfl) ⟨72140, by rfl⟩) R144281
theorem R63497 : Reach 63497 := rs (se 2 (by rfl) ⟨23811, by rfl⟩) R47623
theorem R260111 : Reach 260111 := rs (se 1 (by rfl) ⟨195083, by rfl⟩) R390167
theorem R227357 : Reach 227357 := rs (se 3 (by rfl) ⟨42629, by rfl⟩) R85259
theorem R96335 : Reach 96335 := rs (se 1 (by rfl) ⟨72251, by rfl⟩) R144503
theorem R260185 : Reach 260185 := rs (se 2 (by rfl) ⟨97569, by rfl⟩) R195139
theorem R63659 : Reach 63659 := rs (se 1 (by rfl) ⟨47744, by rfl⟩) R95489
theorem R227585 : Reach 227585 := rs (se 2 (by rfl) ⟨85344, by rfl⟩) R170689
theorem R588185 : Reach 588185 := rs (se 2 (by rfl) ⟨220569, by rfl⟩) R441139
theorem R195053 : Reach 195053 := rs (se 3 (by rfl) ⟨36572, by rfl⟩) R73145
theorem R129545 : Reach 129545 := rs (se 2 (by rfl) ⟨48579, by rfl⟩) R97159
theorem R129575 : Reach 129575 := rs (se 1 (by rfl) ⟨97181, by rfl⟩) R194363
theorem R64057 : Reach 64057 := rs (se 2 (by rfl) ⟨24021, by rfl⟩) R48043
theorem R64199 : Reach 64199 := rs (se 1 (by rfl) ⟨48149, by rfl⟩) R96299
theorem R64361 : Reach 64361 := rs (se 2 (by rfl) ⟨24135, by rfl⟩) R48271
theorem R64759 : Reach 64759 := rs (se 1 (by rfl) ⟨48569, by rfl⟩) R97139
theorem R130409 : Reach 130409 := rs (se 2 (by rfl) ⟨48903, by rfl⟩) R97807
theorem R64955 : Reach 64955 := rs (se 1 (by rfl) ⟨48716, by rfl⟩) R97433
theorem R65063 : Reach 65063 := rs (se 1 (by rfl) ⟨48797, by rfl⟩) R97595
theorem R65195 : Reach 65195 := rs (se 1 (by rfl) ⟨48896, by rfl⟩) R97793
theorem R98003 : Reach 98003 := rs (se 1 (by rfl) ⟨73502, by rfl⟩) R147005
theorem R65353 : Reach 65353 := rs (se 2 (by rfl) ⟨24507, by rfl⟩) R49015
theorem R65387 : Reach 65387 := rs (se 1 (by rfl) ⟨49040, by rfl⟩) R98081
theorem R65423 : Reach 65423 := rs (se 1 (by rfl) ⟨49067, by rfl⟩) R98135
theorem R65441 : Reach 65441 := rs (se 2 (by rfl) ⟨24540, by rfl⟩) R49081
theorem R131003 : Reach 131003 := rs (se 1 (by rfl) ⟨98252, by rfl⟩) R196505
theorem R196667 : Reach 196667 := rs (se 1 (by rfl) ⟨147500, by rfl⟩) R295001
theorem R131435 : Reach 131435 := rs (se 1 (by rfl) ⟨98576, by rfl⟩) R197153
theorem R131705 : Reach 131705 := rs (se 2 (by rfl) ⟨49389, by rfl⟩) R98779
theorem R393943 : Reach 393943 := rs (se 1 (by rfl) ⟨295457, by rfl⟩) R590915
theorem R131807 : Reach 131807 := rs (se 1 (by rfl) ⟨98855, by rfl⟩) R197711
theorem R197639 : Reach 197639 := rs (se 1 (by rfl) ⟨148229, by rfl⟩) R296459
theorem R295973 : Reach 295973 := rs (se 4 (by rfl) ⟨27747, by rfl⟩) R55495
theorem R1115369 : Reach 1115369 := rs (se 2 (by rfl) ⟨418263, by rfl⟩) R836527
theorem R165215 : Reach 165215 := rs (se 1 (by rfl) ⟨123911, by rfl⟩) R247823
theorem R263533 : Reach 263533 := rs (se 3 (by rfl) ⟨49412, by rfl⟩) R98825
theorem R394739 : Reach 394739 := rs (se 1 (by rfl) ⟨296054, by rfl⟩) R592109
theorem R329417 : Reach 329417 := rs (se 2 (by rfl) ⟨123531, by rfl⟩) R247063
theorem R35163 : Reach 35163 := rs (se 1 (by rfl) ⟨26372, by rfl⟩) R52745
theorem R35183 : Reach 35183 := rs (se 1 (by rfl) ⟨26387, by rfl⟩) R52775
theorem R35239 : Reach 35239 := rs (se 1 (by rfl) ⟨26429, by rfl⟩) R52859
theorem R133559 : Reach 133559 := rs (se 1 (by rfl) ⟨100169, by rfl⟩) R200339
theorem R35323 : Reach 35323 := rs (se 1 (by rfl) ⟨26492, by rfl⟩) R52985
theorem R35391 : Reach 35391 := rs (se 1 (by rfl) ⟨26543, by rfl⟩) R53087
theorem R35399 : Reach 35399 := rs (se 1 (by rfl) ⟨26549, by rfl⟩) R53099
theorem R35551 : Reach 35551 := rs (se 1 (by rfl) ⟨26663, by rfl⟩) R53327
theorem R35631 : Reach 35631 := rs (se 1 (by rfl) ⟨26723, by rfl⟩) R53447
theorem R101263 : Reach 101263 := rs (se 1 (by rfl) ⟨75947, by rfl⟩) R151895
theorem R35739 : Reach 35739 := rs (se 1 (by rfl) ⟨26804, by rfl⟩) R53609
theorem R35791 : Reach 35791 := rs (se 1 (by rfl) ⟨26843, by rfl⟩) R53687
theorem R35815 : Reach 35815 := rs (se 1 (by rfl) ⟨26861, by rfl⟩) R53723
theorem R363521 : Reach 363521 := rs (se 2 (by rfl) ⟨136320, by rfl⟩) R272641
theorem R36127 : Reach 36127 := rs (se 1 (by rfl) ⟨27095, by rfl⟩) R54191
theorem R36187 : Reach 36187 := rs (se 1 (by rfl) ⟨27140, by rfl⟩) R54281
theorem R36207 : Reach 36207 := rs (se 1 (by rfl) ⟨27155, by rfl⟩) R54311
theorem R331127 : Reach 331127 := rs (se 1 (by rfl) ⟨248345, by rfl⟩) R496691
theorem R36263 : Reach 36263 := rs (se 1 (by rfl) ⟨27197, by rfl⟩) R54395
theorem R69113 : Reach 69113 := rs (se 2 (by rfl) ⟨25917, by rfl⟩) R51835
theorem R36347 : Reach 36347 := rs (se 1 (by rfl) ⟨27260, by rfl⟩) R54521
theorem R36415 : Reach 36415 := rs (se 1 (by rfl) ⟨27311, by rfl⟩) R54623
theorem R36423 : Reach 36423 := rs (se 1 (by rfl) ⟨27317, by rfl⟩) R54635
theorem R36575 : Reach 36575 := rs (se 1 (by rfl) ⟨27431, by rfl⟩) R54863
theorem R265963 : Reach 265963 := rs (se 1 (by rfl) ⟨199472, by rfl⟩) R398945
theorem R102151 : Reach 102151 := rs (se 1 (by rfl) ⟨76613, by rfl⟩) R153227
theorem R36655 : Reach 36655 := rs (se 1 (by rfl) ⟨27491, by rfl⟩) R54983
theorem R36763 : Reach 36763 := rs (se 1 (by rfl) ⟨27572, by rfl⟩) R55145
theorem R364445 : Reach 364445 := rs (se 3 (by rfl) ⟨68333, by rfl⟩) R136667
theorem R36815 : Reach 36815 := rs (se 1 (by rfl) ⟨27611, by rfl⟩) R55223
theorem R36839 : Reach 36839 := rs (se 1 (by rfl) ⟨27629, by rfl⟩) R55259
theorem R102505 : Reach 102505 := rs (se 2 (by rfl) ⟨38439, by rfl⟩) R76879
theorem R37083 : Reach 37083 := rs (se 1 (by rfl) ⟨27812, by rfl⟩) R55625
theorem R37151 : Reach 37151 := rs (se 1 (by rfl) ⟨27863, by rfl⟩) R55727
theorem R37159 : Reach 37159 := rs (se 1 (by rfl) ⟨27869, by rfl⟩) R55739
theorem R37211 : Reach 37211 := rs (se 1 (by rfl) ⟨27908, by rfl⟩) R55817
theorem R37231 : Reach 37231 := rs (se 1 (by rfl) ⟨27923, by rfl⟩) R55847
theorem R37243 : Reach 37243 := rs (se 1 (by rfl) ⟨27932, by rfl⟩) R55865
theorem R37287 : Reach 37287 := rs (se 1 (by rfl) ⟨27965, by rfl⟩) R55931
theorem R37319 : Reach 37319 := rs (se 1 (by rfl) ⟨27989, by rfl⟩) R55979
theorem R299501 : Reach 299501 := rs (se 3 (by rfl) ⟨56156, by rfl⟩) R112313
theorem R37371 : Reach 37371 := rs (se 1 (by rfl) ⟨28028, by rfl⟩) R56057
theorem R266813 : Reach 266813 := rs (se 3 (by rfl) ⟨50027, by rfl⟩) R100055
theorem R37439 : Reach 37439 := rs (se 1 (by rfl) ⟨28079, by rfl⟩) R56159
theorem R37447 : Reach 37447 := rs (se 1 (by rfl) ⟨28085, by rfl⟩) R56171
theorem R37471 : Reach 37471 := rs (se 1 (by rfl) ⟨28103, by rfl⟩) R56207
theorem R37551 : Reach 37551 := rs (se 1 (by rfl) ⟨28163, by rfl⟩) R56327
theorem R37599 : Reach 37599 := rs (se 1 (by rfl) ⟨28199, by rfl⟩) R56399
theorem R37679 : Reach 37679 := rs (se 1 (by rfl) ⟨28259, by rfl⟩) R56519
theorem R37711 : Reach 37711 := rs (se 1 (by rfl) ⟨28283, by rfl⟩) R56567
theorem R37787 : Reach 37787 := rs (se 1 (by rfl) ⟨28340, by rfl⟩) R56681
theorem R463781 : Reach 463781 := rs (se 4 (by rfl) ⟨43479, by rfl⟩) R86959
theorem R693197 : Reach 693197 := rs (se 3 (by rfl) ⟨129974, by rfl⟩) R259949
theorem R37839 : Reach 37839 := rs (se 1 (by rfl) ⟨28379, by rfl⟩) R56759
theorem R37863 : Reach 37863 := rs (se 1 (by rfl) ⟨28397, by rfl⟩) R56795
theorem R38107 : Reach 38107 := rs (se 1 (by rfl) ⟨28580, by rfl⟩) R57161
theorem R38175 : Reach 38175 := rs (se 1 (by rfl) ⟨28631, by rfl⟩) R57263
theorem R38183 : Reach 38183 := rs (se 1 (by rfl) ⟨28637, by rfl⟩) R57275
theorem R38235 : Reach 38235 := rs (se 1 (by rfl) ⟨28676, by rfl⟩) R57353
theorem R38255 : Reach 38255 := rs (se 1 (by rfl) ⟨28691, by rfl⟩) R57383
theorem R38267 : Reach 38267 := rs (se 1 (by rfl) ⟨28700, by rfl⟩) R57401
theorem R693629 : Reach 693629 := rs (se 3 (by rfl) ⟨130055, by rfl⟩) R260111
theorem R38311 : Reach 38311 := rs (se 1 (by rfl) ⟨28733, by rfl⟩) R57467
theorem R38343 : Reach 38343 := rs (se 1 (by rfl) ⟨28757, by rfl⟩) R57515
theorem R38395 : Reach 38395 := rs (se 1 (by rfl) ⟨28796, by rfl⟩) R57593
theorem R103943 : Reach 103943 := rs (se 1 (by rfl) ⟨77957, by rfl⟩) R155915
theorem R38463 : Reach 38463 := rs (se 1 (by rfl) ⟨28847, by rfl⟩) R57695
theorem R38471 : Reach 38471 := rs (se 1 (by rfl) ⟨28853, by rfl⟩) R57707
theorem R38495 : Reach 38495 := rs (se 1 (by rfl) ⟨28871, by rfl⟩) R57743
theorem R38575 : Reach 38575 := rs (se 1 (by rfl) ⟨28931, by rfl⟩) R57863
theorem R38623 : Reach 38623 := rs (se 1 (by rfl) ⟨28967, by rfl⟩) R57935
theorem R38703 : Reach 38703 := rs (se 1 (by rfl) ⟨29027, by rfl⟩) R58055
theorem R38735 : Reach 38735 := rs (se 1 (by rfl) ⟨29051, by rfl⟩) R58103
theorem R38811 : Reach 38811 := rs (se 1 (by rfl) ⟨29108, by rfl⟩) R58217
theorem R38863 : Reach 38863 := rs (se 1 (by rfl) ⟨29147, by rfl⟩) R58295
theorem R38887 : Reach 38887 := rs (se 1 (by rfl) ⟨29165, by rfl⟩) R58331
theorem R72103 : Reach 72103 := rs (se 1 (by rfl) ⟨54077, by rfl⟩) R108155
theorem R105067 : Reach 105067 := rs (se 1 (by rfl) ⟨78800, by rfl⟩) R157601
theorem R269243 : Reach 269243 := rs (se 1 (by rfl) ⟨201932, by rfl⟩) R403865
theorem R400403 : Reach 400403 := rs (se 1 (by rfl) ⟨300302, by rfl⟩) R600605
theorem R72991 : Reach 72991 := rs (se 1 (by rfl) ⟨54743, by rfl⟩) R109487
theorem R40315 : Reach 40315 := rs (se 1 (by rfl) ⟨30236, by rfl⟩) R60473
theorem R204281 : Reach 204281 := rs (se 2 (by rfl) ⟨76605, by rfl⟩) R153211
theorem R40511 : Reach 40511 := rs (se 1 (by rfl) ⟨30383, by rfl⟩) R60767
theorem R40783 : Reach 40783 := rs (se 1 (by rfl) ⟨30587, by rfl⟩) R61175
theorem R467153 : Reach 467153 := rs (se 2 (by rfl) ⟨175182, by rfl⟩) R350365
theorem R41179 : Reach 41179 := rs (se 1 (by rfl) ⟨30884, by rfl⟩) R61769
theorem R41467 : Reach 41467 := rs (se 1 (by rfl) ⟨31100, by rfl⟩) R62201
theorem R107027 : Reach 107027 := rs (se 1 (by rfl) ⟨80270, by rfl⟩) R160541
theorem R107129 : Reach 107129 := rs (se 2 (by rfl) ⟨40173, by rfl⟩) R80347
theorem R41647 : Reach 41647 := rs (se 1 (by rfl) ⟨31235, by rfl⟩) R62471
theorem R41935 : Reach 41935 := rs (se 1 (by rfl) ⟨31451, by rfl⟩) R62903
theorem R402407 : Reach 402407 := rs (se 1 (by rfl) ⟨301805, by rfl⟩) R603611
theorem R42331 : Reach 42331 := rs (se 1 (by rfl) ⟨31748, by rfl⟩) R63497
theorem R42439 : Reach 42439 := rs (se 1 (by rfl) ⟨31829, by rfl⟩) R63659
theorem R42799 : Reach 42799 := rs (se 1 (by rfl) ⟨32099, by rfl⟩) R64199
theorem R337769 : Reach 337769 := rs (se 2 (by rfl) ⟨126663, by rfl⟩) R253327
theorem R42907 : Reach 42907 := rs (se 1 (by rfl) ⟨32180, by rfl⟩) R64361
theorem R43303 : Reach 43303 := rs (se 1 (by rfl) ⟨32477, by rfl⟩) R64955
theorem R43375 : Reach 43375 := rs (se 1 (by rfl) ⟨32531, by rfl⟩) R65063
theorem R272807 : Reach 272807 := rs (se 1 (by rfl) ⟨204605, by rfl⟩) R409211
theorem R43463 : Reach 43463 := rs (se 1 (by rfl) ⟨32597, by rfl⟩) R65195
theorem R43591 : Reach 43591 := rs (se 1 (by rfl) ⟨32693, by rfl⟩) R65387
theorem R43615 : Reach 43615 := rs (se 1 (by rfl) ⟨32711, by rfl⟩) R65423
theorem R43627 : Reach 43627 := rs (se 1 (by rfl) ⟨32720, by rfl⟩) R65441
theorem R142019 : Reach 142019 := rs (se 1 (by rfl) ⟨106514, by rfl⟩) R213029
theorem R76511 : Reach 76511 := rs (se 1 (by rfl) ⟨57383, by rfl⟩) R114767
theorem R109757 : Reach 109757 := rs (se 3 (by rfl) ⟨20579, by rfl⟩) R41159
theorem R241015 : Reach 241015 := rs (se 1 (by rfl) ⟨180761, by rfl⟩) R361523
theorem R110011 : Reach 110011 := rs (se 1 (by rfl) ⟨82508, by rfl⟩) R165017
theorem R44651 : Reach 44651 := rs (se 1 (by rfl) ⟨33488, by rfl⟩) R66977
theorem R110315 : Reach 110315 := rs (se 1 (by rfl) ⟨82736, by rfl⟩) R165473
theorem R143111 : Reach 143111 := rs (se 1 (by rfl) ⟨107333, by rfl⟩) R214667
theorem R45031 : Reach 45031 := rs (se 1 (by rfl) ⟨33773, by rfl⟩) R67547
theorem R307471 : Reach 307471 := rs (se 1 (by rfl) ⟨230603, by rfl⟩) R461207
theorem R45479 : Reach 45479 := rs (se 1 (by rfl) ⟨34109, by rfl⟩) R68219
theorem R111287 : Reach 111287 := rs (se 1 (by rfl) ⟨83465, by rfl⟩) R166931
theorem R78823 : Reach 78823 := rs (se 1 (by rfl) ⟨59117, by rfl⟩) R118235
theorem R78887 : Reach 78887 := rs (se 1 (by rfl) ⟨59165, by rfl⟩) R118331
theorem R79199 : Reach 79199 := rs (se 1 (by rfl) ⟨59399, by rfl⟩) R118799
theorem R79595 : Reach 79595 := rs (se 1 (by rfl) ⟨59696, by rfl⟩) R119393
theorem R79721 : Reach 79721 := rs (se 2 (by rfl) ⟨29895, by rfl⟩) R59791
theorem R997271 : Reach 997271 := rs (se 1 (by rfl) ⟨747953, by rfl⟩) R1495907
theorem R178361 : Reach 178361 := rs (se 2 (by rfl) ⟨66885, by rfl⟩) R133771
theorem R112921 : Reach 112921 := rs (se 2 (by rfl) ⟨42345, by rfl⟩) R84691
theorem R80567 : Reach 80567 := rs (se 1 (by rfl) ⟨60425, by rfl⟩) R120851
theorem R146195 : Reach 146195 := rs (se 1 (by rfl) ⟨109646, by rfl⟩) R219293
theorem R80783 : Reach 80783 := rs (se 1 (by rfl) ⟨60587, by rfl⟩) R121175
theorem R81415 : Reach 81415 := rs (se 1 (by rfl) ⟨61061, by rfl⟩) R122123
theorem R81503 : Reach 81503 := rs (se 1 (by rfl) ⟨61127, by rfl⟩) R122255
theorem R81569 : Reach 81569 := rs (se 2 (by rfl) ⟨30588, by rfl⟩) R61177
theorem R81595 : Reach 81595 := rs (se 1 (by rfl) ⟨61196, by rfl⟩) R122393
theorem R48863 : Reach 48863 := rs (se 1 (by rfl) ⟨36647, by rfl⟩) R73295
theorem R212777 : Reach 212777 := rs (se 2 (by rfl) ⟨79791, by rfl⟩) R159583
theorem R81719 : Reach 81719 := rs (se 1 (by rfl) ⟨61289, by rfl⟩) R122579
theorem R147329 : Reach 147329 := rs (se 2 (by rfl) ⟨55248, by rfl⟩) R110497
theorem R180143 : Reach 180143 := rs (se 1 (by rfl) ⟨135107, by rfl⟩) R270215
theorem R82025 : Reach 82025 := rs (se 2 (by rfl) ⟨30759, by rfl⟩) R61519
theorem R180377 : Reach 180377 := rs (se 2 (by rfl) ⟨67641, by rfl⟩) R135283
theorem R82511 : Reach 82511 := rs (se 1 (by rfl) ⟨61883, by rfl⟩) R123767
theorem R148139 : Reach 148139 := rs (se 1 (by rfl) ⟨111104, by rfl⟩) R222209
theorem R82655 : Reach 82655 := rs (se 1 (by rfl) ⟨61991, by rfl⟩) R123983
theorem R181187 : Reach 181187 := rs (se 1 (by rfl) ⟨135890, by rfl⟩) R271781
theorem R82907 : Reach 82907 := rs (se 1 (by rfl) ⟨62180, by rfl⟩) R124361
theorem R82919 : Reach 82919 := rs (se 1 (by rfl) ⟨62189, by rfl⟩) R124379
theorem R83087 : Reach 83087 := rs (se 1 (by rfl) ⟨62315, by rfl⟩) R124631
theorem R83177 : Reach 83177 := rs (se 2 (by rfl) ⟨31191, by rfl⟩) R62383
theorem R83231 : Reach 83231 := rs (se 1 (by rfl) ⟨62423, by rfl⟩) R124847
theorem R148775 : Reach 148775 := rs (se 1 (by rfl) ⟨111581, by rfl⟩) R223163
theorem R1262891 : Reach 1262891 := rs (se 1 (by rfl) ⟨947168, by rfl⟩) R1894337
theorem R83339 : Reach 83339 := rs (se 1 (by rfl) ⟨62504, by rfl⟩) R125009
theorem R83753 : Reach 83753 := rs (se 2 (by rfl) ⟨31407, by rfl⟩) R62815
theorem R345991 : Reach 345991 := rs (se 1 (by rfl) ⟨259493, by rfl⟩) R518987
theorem R183059 : Reach 183059 := rs (se 1 (by rfl) ⟨137294, by rfl⟩) R274589
theorem R346913 : Reach 346913 := rs (se 2 (by rfl) ⟨130092, by rfl⟩) R260185
theorem R84815 : Reach 84815 := rs (se 1 (by rfl) ⟨63611, by rfl⟩) R127223
theorem R150443 : Reach 150443 := rs (se 1 (by rfl) ⟨112832, by rfl⟩) R225665
theorem R85031 : Reach 85031 := rs (se 1 (by rfl) ⟨63773, by rfl⟩) R127547
theorem R85211 : Reach 85211 := rs (se 1 (by rfl) ⟨63908, by rfl⟩) R127817
theorem R85409 : Reach 85409 := rs (se 2 (by rfl) ⟨32028, by rfl⟩) R64057
theorem R52679 : Reach 52679 := rs (se 1 (by rfl) ⟨39509, by rfl⟩) R79019
theorem R85463 : Reach 85463 := rs (se 1 (by rfl) ⟨64097, by rfl⟩) R128195
theorem R347915 : Reach 347915 := rs (se 1 (by rfl) ⟨260936, by rfl⟩) R521873
theorem R53033 : Reach 53033 := rs (se 2 (by rfl) ⟨19887, by rfl⟩) R39775
theorem R53039 : Reach 53039 := rs (se 1 (by rfl) ⟨39779, by rfl⟩) R79559
theorem R413549 : Reach 413549 := rs (se 3 (by rfl) ⟨77540, by rfl⟩) R155081
theorem R184193 : Reach 184193 := rs (se 2 (by rfl) ⟨69072, by rfl⟩) R138145
theorem R85967 : Reach 85967 := rs (se 1 (by rfl) ⟨64475, by rfl⟩) R128951
theorem R151571 : Reach 151571 := rs (se 1 (by rfl) ⟨113678, by rfl⟩) R227357
theorem R151723 : Reach 151723 := rs (se 1 (by rfl) ⟨113792, by rfl⟩) R227585
theorem R53513 : Reach 53513 := rs (se 2 (by rfl) ⟨20067, by rfl⟩) R40135
theorem R86345 : Reach 86345 := rs (se 2 (by rfl) ⟨32379, by rfl⟩) R64759
theorem R86363 : Reach 86363 := rs (se 1 (by rfl) ⟨64772, by rfl⟩) R129545
theorem R53615 : Reach 53615 := rs (se 1 (by rfl) ⟨40211, by rfl⟩) R80423
theorem R86383 : Reach 86383 := rs (se 1 (by rfl) ⟨64787, by rfl⟩) R129575
theorem R53831 : Reach 53831 := rs (se 1 (by rfl) ⟨40373, by rfl⟩) R80747
theorem R53867 : Reach 53867 := rs (se 1 (by rfl) ⟨40400, by rfl⟩) R80801
theorem R185003 : Reach 185003 := rs (se 1 (by rfl) ⟨138752, by rfl⟩) R277505
theorem R54095 : Reach 54095 := rs (se 1 (by rfl) ⟨40571, by rfl⟩) R81143
theorem R86939 : Reach 86939 := rs (se 1 (by rfl) ⟨65204, by rfl⟩) R130409
theorem R119771 : Reach 119771 := rs (se 1 (by rfl) ⟨89828, by rfl⟩) R179657
theorem R87137 : Reach 87137 := rs (se 2 (by rfl) ⟨32676, by rfl⟩) R65353
theorem R119933 : Reach 119933 := rs (se 3 (by rfl) ⟨22487, by rfl⟩) R44975
theorem R185489 : Reach 185489 := rs (se 2 (by rfl) ⟨69558, by rfl⟩) R139117
theorem R54491 : Reach 54491 := rs (se 1 (by rfl) ⟨40868, by rfl⟩) R81737
theorem R120041 : Reach 120041 := rs (se 2 (by rfl) ⟨45015, by rfl⟩) R90031
theorem R87335 : Reach 87335 := rs (se 1 (by rfl) ⟨65501, by rfl⟩) R131003
theorem R54665 : Reach 54665 := rs (se 2 (by rfl) ⟨20499, by rfl⟩) R40999
theorem R120203 : Reach 120203 := rs (se 1 (by rfl) ⟨90152, by rfl⟩) R180305
theorem R349733 : Reach 349733 := rs (se 4 (by rfl) ⟨32787, by rfl⟩) R65575
theorem R87713 : Reach 87713 := rs (se 2 (by rfl) ⟨32892, by rfl⟩) R65785
theorem R55019 : Reach 55019 := rs (se 1 (by rfl) ⟨41264, by rfl⟩) R82529
theorem R55247 : Reach 55247 := rs (se 1 (by rfl) ⟨41435, by rfl⟩) R82871
theorem R612359 : Reach 612359 := rs (se 1 (by rfl) ⟨459269, by rfl⟩) R918539
theorem R55643 : Reach 55643 := rs (se 1 (by rfl) ⟨41732, by rfl⟩) R83465
theorem R55871 : Reach 55871 := rs (se 1 (by rfl) ⟨41903, by rfl⟩) R83807
theorem R55991 : Reach 55991 := rs (se 1 (by rfl) ⟨41993, by rfl⟩) R83987
theorem R154493 : Reach 154493 := rs (se 3 (by rfl) ⟨28967, by rfl⟩) R57935
theorem R56219 : Reach 56219 := rs (se 1 (by rfl) ⟨42164, by rfl⟩) R84329
theorem R482233 : Reach 482233 := rs (se 2 (by rfl) ⟨180837, by rfl⟩) R361675
theorem R711665 : Reach 711665 := rs (se 2 (by rfl) ⟨266874, by rfl⟩) R533749
theorem R89075 : Reach 89075 := rs (se 1 (by rfl) ⟨66806, by rfl⟩) R133613
theorem R89383 : Reach 89383 := rs (se 1 (by rfl) ⟨67037, by rfl⟩) R134075
theorem R56615 : Reach 56615 := rs (se 1 (by rfl) ⟨42461, by rfl⟩) R84923
theorem R56699 : Reach 56699 := rs (se 1 (by rfl) ⟨42524, by rfl⟩) R85049
theorem R56825 : Reach 56825 := rs (se 2 (by rfl) ⟨21309, by rfl⟩) R42619
theorem R187919 : Reach 187919 := rs (se 1 (by rfl) ⟨140939, by rfl⟩) R281879
theorem R89657 : Reach 89657 := rs (se 2 (by rfl) ⟨33621, by rfl⟩) R67243
theorem R56927 : Reach 56927 := rs (se 1 (by rfl) ⟨42695, by rfl⟩) R85391
theorem R57067 : Reach 57067 := rs (se 1 (by rfl) ⟨42800, by rfl⟩) R85601
theorem R57095 : Reach 57095 := rs (se 1 (by rfl) ⟨42821, by rfl⟩) R85643
theorem R57143 : Reach 57143 := rs (se 1 (by rfl) ⟨42857, by rfl⟩) R85715
theorem R188335 : Reach 188335 := rs (se 1 (by rfl) ⟨141251, by rfl⟩) R282503
theorem R548801 : Reach 548801 := rs (se 2 (by rfl) ⟨205800, by rfl⟩) R411601
theorem R1138697 : Reach 1138697 := rs (se 2 (by rfl) ⟨427011, by rfl⟩) R854023
theorem R286739 : Reach 286739 := rs (se 1 (by rfl) ⟨215054, by rfl⟩) R430109
theorem R57449 : Reach 57449 := rs (se 2 (by rfl) ⟨21543, by rfl⟩) R43087
theorem R123227 : Reach 123227 := rs (se 1 (by rfl) ⟨92420, by rfl⟩) R184841
theorem R57767 : Reach 57767 := rs (se 1 (by rfl) ⟨43325, by rfl⟩) R86651
theorem R188891 : Reach 188891 := rs (se 1 (by rfl) ⟨141668, by rfl⟩) R283337
theorem R57851 : Reach 57851 := rs (se 1 (by rfl) ⟨43388, by rfl⟩) R86777
theorem R57929 : Reach 57929 := rs (se 2 (by rfl) ⟨21723, by rfl⟩) R43447
theorem R57977 : Reach 57977 := rs (se 2 (by rfl) ⟨21741, by rfl⟩) R43483
theorem R221867 : Reach 221867 := rs (se 1 (by rfl) ⟨166400, by rfl⟩) R332801
theorem R58031 : Reach 58031 := rs (se 1 (by rfl) ⟨43523, by rfl⟩) R87047
theorem R221879 : Reach 221879 := rs (se 1 (by rfl) ⟨166409, by rfl⟩) R332819
theorem R58079 : Reach 58079 := rs (se 1 (by rfl) ⟨43559, by rfl⟩) R87119
theorem R58283 : Reach 58283 := rs (se 1 (by rfl) ⟨43712, by rfl⟩) R87425
theorem R189377 : Reach 189377 := rs (se 2 (by rfl) ⟨71016, by rfl⟩) R142033
theorem R58343 : Reach 58343 := rs (se 1 (by rfl) ⟨43757, by rfl⟩) R87515
theorem R58511 : Reach 58511 := rs (se 1 (by rfl) ⟨43883, by rfl⟩) R87767
theorem R58601 : Reach 58601 := rs (se 2 (by rfl) ⟨21975, by rfl⟩) R43951
theorem R58655 : Reach 58655 := rs (se 1 (by rfl) ⟨43991, by rfl⟩) R87983
theorem R124199 : Reach 124199 := rs (se 1 (by rfl) ⟨93149, by rfl⟩) R186299
theorem R451889 : Reach 451889 := rs (se 2 (by rfl) ⟨169458, by rfl⟩) R338917
theorem R222551 : Reach 222551 := rs (se 1 (by rfl) ⟨166913, by rfl⟩) R333827
theorem R91489 : Reach 91489 := rs (se 2 (by rfl) ⟨34308, by rfl⟩) R68617
theorem R976373 : Reach 976373 := rs (se 5 (by rfl) ⟨45767, by rfl⟩) R91535
theorem R125063 : Reach 125063 := rs (se 1 (by rfl) ⟨93797, by rfl⟩) R187595
theorem R321731 : Reach 321731 := rs (se 1 (by rfl) ⟨241298, by rfl⟩) R482597
theorem R157943 : Reach 157943 := rs (se 1 (by rfl) ⟨118457, by rfl⟩) R236915
theorem R92441 : Reach 92441 := rs (se 2 (by rfl) ⟨34665, by rfl⟩) R69331
theorem R59899 : Reach 59899 := rs (se 1 (by rfl) ⟨44924, by rfl⟩) R89849
theorem R92735 : Reach 92735 := rs (se 1 (by rfl) ⟨69551, by rfl⟩) R139103
theorem R289403 : Reach 289403 := rs (se 1 (by rfl) ⟨217052, by rfl⟩) R434105
theorem R92947 : Reach 92947 := rs (se 1 (by rfl) ⟨69710, by rfl⟩) R139421
theorem R60331 : Reach 60331 := rs (se 1 (by rfl) ⟨45248, by rfl⟩) R90497
theorem R93383 : Reach 93383 := rs (se 1 (by rfl) ⟨70037, by rfl⟩) R140075
theorem R60635 : Reach 60635 := rs (se 1 (by rfl) ⟨45476, by rfl⟩) R90953
theorem R93433 : Reach 93433 := rs (se 2 (by rfl) ⟨35037, by rfl⟩) R70075
theorem R126305 : Reach 126305 := rs (se 2 (by rfl) ⟨47364, by rfl⟩) R94729
theorem R93563 : Reach 93563 := rs (se 1 (by rfl) ⟨70172, by rfl⟩) R140345
theorem R60871 : Reach 60871 := rs (se 1 (by rfl) ⟨45653, by rfl⟩) R91307
theorem R159241 : Reach 159241 := rs (se 2 (by rfl) ⟨59715, by rfl⟩) R119431
theorem R1175233 : Reach 1175233 := rs (se 2 (by rfl) ⟨440712, by rfl⟩) R881425
theorem R94081 : Reach 94081 := rs (se 2 (by rfl) ⟨35280, by rfl⟩) R70561
theorem R520141 : Reach 520141 := rs (se 3 (by rfl) ⟨97526, by rfl⟩) R195053
theorem R61391 : Reach 61391 := rs (se 1 (by rfl) ⟨46043, by rfl⟩) R92087
theorem R192617 : Reach 192617 := rs (se 2 (by rfl) ⟨72231, by rfl⟩) R144463
theorem R356723 : Reach 356723 := rs (se 1 (by rfl) ⟨267542, by rfl⟩) R535085
theorem R651725 : Reach 651725 := rs (se 3 (by rfl) ⟨122198, by rfl⟩) R244397
theorem R62059 : Reach 62059 := rs (se 1 (by rfl) ⟨46544, by rfl⟩) R93089
theorem R94841 : Reach 94841 := rs (se 2 (by rfl) ⟨35565, by rfl⟩) R71131
theorem R94891 : Reach 94891 := rs (se 1 (by rfl) ⟨71168, by rfl⟩) R142337
theorem R160471 : Reach 160471 := rs (se 1 (by rfl) ⟨120353, by rfl⟩) R240707
theorem R62363 : Reach 62363 := rs (se 1 (by rfl) ⟨46772, by rfl⟩) R93545
theorem R95195 : Reach 95195 := rs (se 1 (by rfl) ⟨71396, by rfl⟩) R142793
theorem R95357 : Reach 95357 := rs (se 3 (by rfl) ⟨17879, by rfl⟩) R35759
theorem R95431 : Reach 95431 := rs (se 1 (by rfl) ⟨71573, by rfl⟩) R143147
theorem R193751 : Reach 193751 := rs (se 1 (by rfl) ⟨145313, by rfl⟩) R290627
theorem R128249 : Reach 128249 := rs (se 2 (by rfl) ⟨48093, by rfl⟩) R96187
theorem R95519 : Reach 95519 := rs (se 1 (by rfl) ⟨71639, by rfl⟩) R143279
theorem R128519 : Reach 128519 := rs (se 1 (by rfl) ⟨96389, by rfl⟩) R192779
theorem R358199 : Reach 358199 := rs (se 1 (by rfl) ⟨268649, by rfl⟩) R537299
theorem R129005 : Reach 129005 := rs (se 3 (by rfl) ⟨24188, by rfl⟩) R48377
theorem R325795 : Reach 325795 := rs (se 1 (by rfl) ⟨244346, by rfl⟩) R488693
theorem R96623 : Reach 96623 := rs (se 1 (by rfl) ⟨72467, by rfl⟩) R144935
theorem R2587085 : Reach 2587085 := rs (se 3 (by rfl) ⟨485078, by rfl⟩) R970157
theorem R129491 : Reach 129491 := rs (se 1 (by rfl) ⟨97118, by rfl⟩) R194237
theorem R129599 : Reach 129599 := rs (se 1 (by rfl) ⟨97199, by rfl⟩) R194399
theorem R457289 : Reach 457289 := rs (se 2 (by rfl) ⟨171483, by rfl⟩) R342967
theorem R162443 : Reach 162443 := rs (se 1 (by rfl) ⟨121832, by rfl⟩) R243665
theorem R195293 : Reach 195293 := rs (se 3 (by rfl) ⟨36617, by rfl⟩) R73235
theorem R64223 : Reach 64223 := rs (se 1 (by rfl) ⟨48167, by rfl⟩) R96335
theorem R392123 : Reach 392123 := rs (se 1 (by rfl) ⟨294092, by rfl⟩) R588185
theorem R1276901 : Reach 1276901 := rs (se 4 (by rfl) ⟨119709, by rfl⟩) R239419
theorem R97271 : Reach 97271 := rs (se 1 (by rfl) ⟨72953, by rfl⟩) R145907
theorem R196177 : Reach 196177 := rs (se 2 (by rfl) ⟨73566, by rfl⟩) R147133
theorem R294515 : Reach 294515 := rs (se 1 (by rfl) ⟨220886, by rfl⟩) R441773
theorem R97949 : Reach 97949 := rs (se 3 (by rfl) ⟨18365, by rfl⟩) R36731
theorem R425735 : Reach 425735 := rs (se 1 (by rfl) ⟨319301, by rfl⟩) R638603
theorem R65335 : Reach 65335 := rs (se 1 (by rfl) ⟨49001, by rfl⟩) R98003
theorem R294785 : Reach 294785 := rs (se 2 (by rfl) ⟨110544, by rfl⟩) R221089
theorem R753569 : Reach 753569 := rs (se 2 (by rfl) ⟨282588, by rfl⟩) R565177
theorem R131111 : Reach 131111 := rs (se 1 (by rfl) ⟨98333, by rfl⟩) R196667
theorem R98759 : Reach 98759 := rs (se 1 (by rfl) ⟨74069, by rfl⟩) R148139
theorem R131759 : Reach 131759 := rs (se 1 (by rfl) ⟨98819, by rfl⟩) R197639
theorem R197315 : Reach 197315 := rs (se 1 (by rfl) ⟨147986, by rfl⟩) R295973
theorem R525257 : Reach 525257 := rs (se 2 (by rfl) ⟨196971, by rfl⟩) R393943
theorem R263159 : Reach 263159 := rs (se 1 (by rfl) ⟨197369, by rfl⟩) R394739
theorem R231275 : Reach 231275 := rs (se 1 (by rfl) ⟨173456, by rfl⟩) R346913
theorem R100295 : Reach 100295 := rs (se 1 (by rfl) ⟨75221, by rfl⟩) R150443
theorem R35119 : Reach 35119 := rs (se 1 (by rfl) ⟨26339, by rfl⟩) R52679
theorem R231943 : Reach 231943 := rs (se 1 (by rfl) ⟨173957, by rfl⟩) R347915
theorem R461321 : Reach 461321 := rs (se 2 (by rfl) ⟨172995, by rfl⟩) R345991
theorem R35355 : Reach 35355 := rs (se 1 (by rfl) ⟨26516, by rfl⟩) R53033
theorem R35359 : Reach 35359 := rs (se 1 (by rfl) ⟨26519, by rfl⟩) R53039
theorem R101047 : Reach 101047 := rs (se 1 (by rfl) ⟨75785, by rfl⟩) R151571
theorem R35675 : Reach 35675 := rs (se 1 (by rfl) ⟨26756, by rfl⟩) R53513
theorem R35743 : Reach 35743 := rs (se 1 (by rfl) ⟨26807, by rfl⟩) R53615
theorem R199667 : Reach 199667 := rs (se 1 (by rfl) ⟨149750, by rfl⟩) R299501
theorem R35887 : Reach 35887 := rs (se 1 (by rfl) ⟨26915, by rfl⟩) R53831
theorem R35911 : Reach 35911 := rs (se 1 (by rfl) ⟨26933, by rfl⟩) R53867
theorem R36063 : Reach 36063 := rs (se 1 (by rfl) ⟨27047, by rfl⟩) R54095
theorem R462131 : Reach 462131 := rs (se 1 (by rfl) ⟨346598, by rfl⟩) R693197
theorem R396733 : Reach 396733 := rs (se 3 (by rfl) ⟨74387, by rfl⟩) R148775
theorem R36327 : Reach 36327 := rs (se 1 (by rfl) ⟨27245, by rfl⟩) R54491
theorem R462419 : Reach 462419 := rs (se 1 (by rfl) ⟨346814, by rfl⟩) R693629
theorem R36443 : Reach 36443 := rs (se 1 (by rfl) ⟨27332, by rfl⟩) R54665
theorem R233155 : Reach 233155 := rs (se 1 (by rfl) ⟨174866, by rfl⟩) R349733
theorem R36679 : Reach 36679 := rs (se 1 (by rfl) ⟨27509, by rfl⟩) R55019
theorem R135017 : Reach 135017 := rs (se 2 (by rfl) ⟨50631, by rfl⟩) R101263
theorem R36831 : Reach 36831 := rs (se 1 (by rfl) ⟨27623, by rfl⟩) R55247
theorem R37095 : Reach 37095 := rs (se 1 (by rfl) ⟨27821, by rfl⟩) R55643
theorem R102653 : Reach 102653 := rs (se 3 (by rfl) ⟨19247, by rfl⟩) R38495
theorem R37247 : Reach 37247 := rs (se 1 (by rfl) ⟨27935, by rfl⟩) R55871
theorem R37327 : Reach 37327 := rs (se 1 (by rfl) ⟨27995, by rfl⟩) R55991
theorem R102995 : Reach 102995 := rs (se 1 (by rfl) ⟨77246, by rfl⟩) R154493
theorem R37479 : Reach 37479 := rs (se 1 (by rfl) ⟨28109, by rfl⟩) R56219
theorem R266935 : Reach 266935 := rs (se 1 (by rfl) ⟨200201, by rfl⟩) R400403
theorem R37743 : Reach 37743 := rs (se 1 (by rfl) ⟨28307, by rfl⟩) R56615
theorem R1217429 : Reach 1217429 := rs (se 6 (by rfl) ⟨28533, by rfl⟩) R57067
theorem R37799 : Reach 37799 := rs (se 1 (by rfl) ⟨28349, by rfl⟩) R56699
theorem R136187 : Reach 136187 := rs (se 1 (by rfl) ⟨102140, by rfl⟩) R204281
theorem R37883 : Reach 37883 := rs (se 1 (by rfl) ⟨28412, by rfl⟩) R56825
theorem R136201 : Reach 136201 := rs (se 2 (by rfl) ⟨51075, by rfl⟩) R102151
theorem R37951 : Reach 37951 := rs (se 1 (by rfl) ⟨28463, by rfl⟩) R56927
theorem R38063 : Reach 38063 := rs (se 1 (by rfl) ⟨28547, by rfl⟩) R57095
theorem R38095 : Reach 38095 := rs (se 1 (by rfl) ⟨28571, by rfl⟩) R57143
theorem R693521 : Reach 693521 := rs (se 2 (by rfl) ⟨260070, by rfl⟩) R520141
theorem R365867 : Reach 365867 := rs (se 1 (by rfl) ⟨274400, by rfl⟩) R548801
theorem R759131 : Reach 759131 := rs (se 1 (by rfl) ⟨569348, by rfl⟩) R1138697
theorem R38299 : Reach 38299 := rs (se 1 (by rfl) ⟨28724, by rfl⟩) R57449
theorem R136673 : Reach 136673 := rs (se 2 (by rfl) ⟨51252, by rfl⟩) R102505
theorem R202297 : Reach 202297 := rs (se 2 (by rfl) ⟨75861, by rfl⟩) R151723
theorem R38511 : Reach 38511 := rs (se 1 (by rfl) ⟨28883, by rfl⟩) R57767
theorem R38567 : Reach 38567 := rs (se 1 (by rfl) ⟨28925, by rfl⟩) R57851
theorem R71351 : Reach 71351 := rs (se 1 (by rfl) ⟨53513, by rfl⟩) R107027
theorem R38619 : Reach 38619 := rs (se 1 (by rfl) ⟨28964, by rfl⟩) R57929
theorem R38651 : Reach 38651 := rs (se 1 (by rfl) ⟨28988, by rfl⟩) R57977
theorem R38687 : Reach 38687 := rs (se 1 (by rfl) ⟨29015, by rfl⟩) R58031
theorem R38719 : Reach 38719 := rs (se 1 (by rfl) ⟨29039, by rfl⟩) R58079
theorem R38855 : Reach 38855 := rs (se 1 (by rfl) ⟨29141, by rfl⟩) R58283
theorem R268271 : Reach 268271 := rs (se 1 (by rfl) ⟨201203, by rfl⟩) R402407
theorem R38895 : Reach 38895 := rs (se 1 (by rfl) ⟨29171, by rfl⟩) R58343
theorem R39007 : Reach 39007 := rs (se 1 (by rfl) ⟨29255, by rfl⟩) R58511
theorem R39067 : Reach 39067 := rs (se 1 (by rfl) ⟨29300, by rfl⟩) R58601
theorem R39103 : Reach 39103 := rs (se 1 (by rfl) ⟨29327, by rfl⟩) R58655
theorem R301259 : Reach 301259 := rs (se 1 (by rfl) ⟨225944, by rfl⟩) R451889
theorem R105097 : Reach 105097 := rs (se 2 (by rfl) ⟨39411, by rfl⟩) R78823
theorem R105295 : Reach 105295 := rs (se 1 (by rfl) ⟨78971, by rfl⟩) R157943
theorem R433181 : Reach 433181 := rs (se 3 (by rfl) ⟨81221, by rfl⟩) R162443
theorem R204029 : Reach 204029 := rs (se 3 (by rfl) ⟨38255, by rfl⟩) R76511
theorem R73171 : Reach 73171 := rs (se 1 (by rfl) ⟨54878, by rfl⟩) R109757
theorem R40423 : Reach 40423 := rs (se 1 (by rfl) ⟨30317, by rfl⟩) R60635
theorem R73543 : Reach 73543 := rs (se 1 (by rfl) ⟨55157, by rfl⟩) R110315
theorem R40927 : Reach 40927 := rs (se 1 (by rfl) ⟨30695, by rfl⟩) R61391
theorem R434393 : Reach 434393 := rs (se 2 (by rfl) ⟨162897, by rfl⟩) R325795
theorem R237815 : Reach 237815 := rs (se 1 (by rfl) ⟨178361, by rfl⟩) R356723
theorem R434483 : Reach 434483 := rs (se 1 (by rfl) ⟨325862, by rfl⟩) R651725
theorem R74191 : Reach 74191 := rs (se 1 (by rfl) ⟨55643, by rfl⟩) R111287
theorem R41575 : Reach 41575 := rs (se 1 (by rfl) ⟨31181, by rfl⟩) R62363
theorem R140089 : Reach 140089 := rs (se 2 (by rfl) ⟨52533, by rfl⟩) R105067
theorem R238799 : Reach 238799 := rs (se 1 (by rfl) ⟨179099, by rfl⟩) R358199
theorem R664847 : Reach 664847 := rs (se 1 (by rfl) ⟨498635, by rfl⟩) R997271
theorem R108029 : Reach 108029 := rs (se 3 (by rfl) ⟨20255, by rfl⟩) R40511
theorem R304859 : Reach 304859 := rs (se 1 (by rfl) ⟨228644, by rfl⟩) R457289
theorem R42815 : Reach 42815 := rs (se 1 (by rfl) ⟨32111, by rfl⟩) R64223
theorem R108553 : Reach 108553 := rs (se 2 (by rfl) ⟨40707, by rfl⟩) R81415
theorem R108793 : Reach 108793 := rs (se 2 (by rfl) ⟨40797, by rfl⟩) R81595
theorem R141851 : Reach 141851 := rs (se 1 (by rfl) ⟨106388, by rfl⟩) R212777
theorem R502379 : Reach 502379 := rs (se 1 (by rfl) ⟨376784, by rfl⟩) R753569
theorem R110143 : Reach 110143 := rs (se 1 (by rfl) ⟨82607, by rfl⟩) R165215
theorem R602245 : Reach 602245 := rs (se 4 (by rfl) ⟨56460, by rfl⟩) R112921
theorem R242347 : Reach 242347 := rs (se 1 (by rfl) ⟨181760, by rfl⟩) R363521
theorem R275699 : Reach 275699 := rs (se 1 (by rfl) ⟨206774, by rfl⟩) R413549
theorem R242963 : Reach 242963 := rs (se 1 (by rfl) ⟨182222, by rfl⟩) R364445
theorem R177875 : Reach 177875 := rs (se 1 (by rfl) ⟨133406, by rfl⟩) R266813
theorem R309187 : Reach 309187 := rs (se 1 (by rfl) ⟨231890, by rfl⟩) R463781
theorem R79847 : Reach 79847 := rs (se 1 (by rfl) ⟨59885, by rfl⟩) R119771
theorem R79865 : Reach 79865 := rs (se 2 (by rfl) ⟨29949, by rfl⟩) R59899
theorem R79955 : Reach 79955 := rs (se 1 (by rfl) ⟨59966, by rfl⟩) R119933
theorem R80027 : Reach 80027 := rs (se 1 (by rfl) ⟨60020, by rfl⟩) R120041
theorem R80135 : Reach 80135 := rs (se 1 (by rfl) ⟨60101, by rfl⟩) R120203
theorem R80441 : Reach 80441 := rs (se 2 (by rfl) ⟨30165, by rfl⟩) R60331
theorem R408239 : Reach 408239 := rs (se 1 (by rfl) ⟨306179, by rfl⟩) R612359
theorem R277181 : Reach 277181 := rs (se 3 (by rfl) ⟨51971, by rfl⟩) R103943
theorem R146681 : Reach 146681 := rs (se 2 (by rfl) ⟨55005, by rfl⟩) R110011
theorem R81161 : Reach 81161 := rs (se 2 (by rfl) ⟨30435, by rfl⟩) R60871
theorem R179495 : Reach 179495 := rs (se 1 (by rfl) ⟨134621, by rfl⟩) R269243
theorem R474443 : Reach 474443 := rs (se 1 (by rfl) ⟨355832, by rfl⟩) R711665
theorem R212321 : Reach 212321 := rs (se 2 (by rfl) ⟨79620, by rfl⟩) R159241
theorem R311435 : Reach 311435 := rs (se 1 (by rfl) ⟨233576, by rfl⟩) R467153
theorem R82151 : Reach 82151 := rs (se 1 (by rfl) ⟨61613, by rfl⟩) R123227
theorem R409961 : Reach 409961 := rs (se 2 (by rfl) ⟨153735, by rfl⟩) R307471
theorem R147911 : Reach 147911 := rs (se 1 (by rfl) ⟨110933, by rfl⟩) R221867
theorem R147919 : Reach 147919 := rs (se 1 (by rfl) ⟨110939, by rfl⟩) R221879
theorem R115177 : Reach 115177 := rs (se 2 (by rfl) ⟨43191, by rfl⟩) R86383
theorem R82745 : Reach 82745 := rs (se 2 (by rfl) ⟨31029, by rfl⟩) R62059
theorem R82799 : Reach 82799 := rs (se 1 (by rfl) ⟨62099, by rfl⟩) R124199
theorem R148367 : Reach 148367 := rs (se 1 (by rfl) ⟨111275, by rfl⟩) R222551
theorem R213961 : Reach 213961 := rs (se 2 (by rfl) ⟨80235, by rfl⟩) R160471
theorem R115901 : Reach 115901 := rs (se 3 (by rfl) ⟨21731, by rfl⟩) R43463
theorem R83375 : Reach 83375 := rs (se 1 (by rfl) ⟨62531, by rfl⟩) R125063
theorem R214487 : Reach 214487 := rs (se 1 (by rfl) ⟨160865, by rfl⟩) R321731
theorem R181871 : Reach 181871 := rs (se 1 (by rfl) ⟨136403, by rfl⟩) R272807
theorem R84203 : Reach 84203 := rs (se 1 (by rfl) ⟨63152, by rfl⟩) R126305
theorem R52591 : Reach 52591 := rs (se 1 (by rfl) ⟨39443, by rfl⟩) R78887
theorem R85499 : Reach 85499 := rs (se 1 (by rfl) ⟨64124, by rfl⟩) R128249
theorem R52799 : Reach 52799 := rs (se 1 (by rfl) ⟨39599, by rfl⟩) R79199
theorem R85679 : Reach 85679 := rs (se 1 (by rfl) ⟨64259, by rfl⟩) R128519
theorem R53063 : Reach 53063 := rs (se 1 (by rfl) ⟨39797, by rfl⟩) R79595
theorem R53147 : Reach 53147 := rs (se 1 (by rfl) ⟨39860, by rfl⟩) R79721
theorem R642977 : Reach 642977 := rs (se 2 (by rfl) ⟨241116, by rfl⟩) R482233
theorem R184301 : Reach 184301 := rs (se 3 (by rfl) ⟨34556, by rfl⟩) R69113
theorem R86003 : Reach 86003 := rs (se 1 (by rfl) ⟨64502, by rfl⟩) R129005
theorem R118907 : Reach 118907 := rs (se 1 (by rfl) ⟨89180, by rfl⟩) R178361
theorem R119069 : Reach 119069 := rs (se 3 (by rfl) ⟨22325, by rfl⟩) R44651
theorem R1724723 : Reach 1724723 := rs (se 1 (by rfl) ⟨1293542, by rfl⟩) R2587085
theorem R86327 : Reach 86327 := rs (se 1 (by rfl) ⟨64745, by rfl⟩) R129491
theorem R86399 : Reach 86399 := rs (se 1 (by rfl) ⟨64799, by rfl⟩) R129599
theorem R119177 : Reach 119177 := rs (se 2 (by rfl) ⟨44691, by rfl⟩) R89383
theorem R53711 : Reach 53711 := rs (se 1 (by rfl) ⟨40283, by rfl⟩) R80567
theorem R53753 : Reach 53753 := rs (se 2 (by rfl) ⟨20157, by rfl⟩) R40315
theorem R53855 : Reach 53855 := rs (se 1 (by rfl) ⟨40391, by rfl⟩) R80783
theorem R54335 : Reach 54335 := rs (se 1 (by rfl) ⟨40751, by rfl⟩) R81503
theorem R87113 : Reach 87113 := rs (se 2 (by rfl) ⟨32667, by rfl⟩) R65335
theorem R54377 : Reach 54377 := rs (se 2 (by rfl) ⟨20391, by rfl⟩) R40783
theorem R54379 : Reach 54379 := rs (se 1 (by rfl) ⟨40784, by rfl⟩) R81569
theorem R283823 : Reach 283823 := rs (se 1 (by rfl) ⟨212867, by rfl⟩) R425735
theorem R54479 : Reach 54479 := rs (se 1 (by rfl) ⟨40859, by rfl⟩) R81719
theorem R251113 : Reach 251113 := rs (se 2 (by rfl) ⟨94167, by rfl⟩) R188335
theorem R120095 : Reach 120095 := rs (se 1 (by rfl) ⟨90071, by rfl⟩) R180143
theorem R54683 : Reach 54683 := rs (se 1 (by rfl) ⟨41012, by rfl⟩) R82025
theorem R120251 : Reach 120251 := rs (se 1 (by rfl) ⟨90188, by rfl⟩) R180377
theorem R87623 : Reach 87623 := rs (se 1 (by rfl) ⟨65717, by rfl⟩) R131435
theorem R54905 : Reach 54905 := rs (se 2 (by rfl) ⟨20589, by rfl⟩) R41179
theorem R55007 : Reach 55007 := rs (se 1 (by rfl) ⟨41255, by rfl⟩) R82511
theorem R87803 : Reach 87803 := rs (se 1 (by rfl) ⟨65852, by rfl⟩) R131705
theorem R55103 : Reach 55103 := rs (se 1 (by rfl) ⟨41327, by rfl⟩) R82655
theorem R120791 : Reach 120791 := rs (se 1 (by rfl) ⟨90593, by rfl⟩) R181187
theorem R55271 : Reach 55271 := rs (se 1 (by rfl) ⟨41453, by rfl⟩) R82907
theorem R55279 : Reach 55279 := rs (se 1 (by rfl) ⟨41459, by rfl⟩) R82919
theorem R55289 : Reach 55289 := rs (se 2 (by rfl) ⟨20733, by rfl⟩) R41467
theorem R55391 : Reach 55391 := rs (se 1 (by rfl) ⟨41543, by rfl⟩) R83087
theorem R55451 : Reach 55451 := rs (se 1 (by rfl) ⟨41588, by rfl⟩) R83177
theorem R743579 : Reach 743579 := rs (se 1 (by rfl) ⟨557684, by rfl⟩) R1115369
theorem R55487 : Reach 55487 := rs (se 1 (by rfl) ⟨41615, by rfl⟩) R83231
theorem R841927 : Reach 841927 := rs (se 1 (by rfl) ⟨631445, by rfl⟩) R1262891
theorem R55529 : Reach 55529 := rs (se 2 (by rfl) ⟨20823, by rfl⟩) R41647
theorem R55559 : Reach 55559 := rs (se 1 (by rfl) ⟨41669, by rfl⟩) R83339
theorem R121277 : Reach 121277 := rs (se 3 (by rfl) ⟨22739, by rfl⟩) R45479
theorem R219611 : Reach 219611 := rs (se 1 (by rfl) ⟨164708, by rfl⟩) R329417
theorem R55835 : Reach 55835 := rs (se 1 (by rfl) ⟨41876, by rfl⟩) R83753
theorem R55913 : Reach 55913 := rs (se 2 (by rfl) ⟨20967, by rfl⟩) R41935
theorem R89039 : Reach 89039 := rs (se 1 (by rfl) ⟨66779, by rfl⟩) R133559
theorem R285677 : Reach 285677 := rs (se 3 (by rfl) ⟨53564, by rfl⟩) R107129
theorem R56441 : Reach 56441 := rs (se 2 (by rfl) ⟨21165, by rfl⟩) R42331
theorem R121985 : Reach 121985 := rs (se 2 (by rfl) ⟨45744, by rfl⟩) R91489
theorem R351377 : Reach 351377 := rs (se 2 (by rfl) ⟨131766, by rfl⟩) R263533
theorem R122039 : Reach 122039 := rs (se 1 (by rfl) ⟨91529, by rfl⟩) R183059
theorem R56543 : Reach 56543 := rs (se 1 (by rfl) ⟨42407, by rfl⟩) R84815
theorem R351485 : Reach 351485 := rs (se 3 (by rfl) ⟨65903, by rfl⟩) R131807
theorem R56585 : Reach 56585 := rs (se 2 (by rfl) ⟨21219, by rfl⟩) R42439
theorem R56687 : Reach 56687 := rs (se 1 (by rfl) ⟨42515, by rfl⟩) R85031
theorem R56807 : Reach 56807 := rs (se 1 (by rfl) ⟨42605, by rfl⟩) R85211
theorem R220751 : Reach 220751 := rs (se 1 (by rfl) ⟨165563, by rfl⟩) R331127
theorem R56939 : Reach 56939 := rs (se 1 (by rfl) ⟨42704, by rfl⟩) R85409
theorem R56975 : Reach 56975 := rs (se 1 (by rfl) ⟨42731, by rfl⟩) R85463
theorem R57065 : Reach 57065 := rs (se 2 (by rfl) ⟨21399, by rfl⟩) R42799
theorem R57209 : Reach 57209 := rs (se 2 (by rfl) ⟨21453, by rfl⟩) R42907
theorem R122795 : Reach 122795 := rs (se 1 (by rfl) ⟨92096, by rfl⟩) R184193
theorem R57311 : Reach 57311 := rs (se 1 (by rfl) ⟨42983, by rfl⟩) R85967
theorem R57563 : Reach 57563 := rs (se 1 (by rfl) ⟨43172, by rfl⟩) R86345
theorem R57575 : Reach 57575 := rs (se 1 (by rfl) ⟨43181, by rfl⟩) R86363
theorem R57737 : Reach 57737 := rs (se 2 (by rfl) ⟨21651, by rfl⟩) R43303
theorem R123335 : Reach 123335 := rs (se 1 (by rfl) ⟨92501, by rfl⟩) R185003
theorem R57833 : Reach 57833 := rs (se 2 (by rfl) ⟨21687, by rfl⟩) R43375
theorem R57959 : Reach 57959 := rs (se 1 (by rfl) ⟨43469, by rfl⟩) R86939
theorem R156269 : Reach 156269 := rs (se 3 (by rfl) ⟨29300, by rfl⟩) R58601
theorem R58091 : Reach 58091 := rs (se 1 (by rfl) ⟨43568, by rfl⟩) R87137
theorem R58121 : Reach 58121 := rs (se 2 (by rfl) ⟨21795, by rfl⟩) R43591
theorem R123659 : Reach 123659 := rs (se 1 (by rfl) ⟨92744, by rfl⟩) R185489
theorem R58153 : Reach 58153 := rs (se 2 (by rfl) ⟨21807, by rfl⟩) R43615
theorem R58169 : Reach 58169 := rs (se 2 (by rfl) ⟨21813, by rfl⟩) R43627
theorem R58223 : Reach 58223 := rs (se 1 (by rfl) ⟨43667, by rfl⟩) R87335
theorem R123929 : Reach 123929 := rs (se 2 (by rfl) ⟨46473, by rfl⟩) R92947
theorem R58475 : Reach 58475 := rs (se 1 (by rfl) ⟨43856, by rfl⟩) R87713
theorem R124577 : Reach 124577 := rs (se 2 (by rfl) ⟨46716, by rfl⟩) R93433
theorem R321353 : Reach 321353 := rs (se 2 (by rfl) ⟨120507, by rfl⟩) R241015
theorem R59383 : Reach 59383 := rs (se 1 (by rfl) ⟨44537, by rfl⟩) R89075
theorem R1566977 : Reach 1566977 := rs (se 2 (by rfl) ⟨587616, by rfl⟩) R1175233
theorem R354617 : Reach 354617 := rs (se 2 (by rfl) ⟨132981, by rfl⟩) R265963
theorem R125279 : Reach 125279 := rs (se 1 (by rfl) ⟨93959, by rfl⟩) R187919
theorem R59771 : Reach 59771 := rs (se 1 (by rfl) ⟨44828, by rfl⟩) R89657
theorem R125441 : Reach 125441 := rs (se 2 (by rfl) ⟨47040, by rfl⟩) R94081
theorem R60041 : Reach 60041 := rs (se 2 (by rfl) ⟨22515, by rfl⟩) R45031
theorem R191159 : Reach 191159 := rs (se 1 (by rfl) ⟨143369, by rfl⟩) R286739
theorem R125927 : Reach 125927 := rs (se 1 (by rfl) ⟨94445, by rfl⟩) R188891
theorem R126251 : Reach 126251 := rs (se 1 (by rfl) ⟨94688, by rfl⟩) R189377
theorem R126521 : Reach 126521 := rs (se 2 (by rfl) ⟨47445, by rfl⟩) R94891
theorem R650915 : Reach 650915 := rs (se 1 (by rfl) ⟨488186, by rfl⟩) R976373
theorem R225179 : Reach 225179 := rs (se 1 (by rfl) ⟨168884, by rfl⟩) R337769
theorem R61627 : Reach 61627 := rs (se 1 (by rfl) ⟨46220, by rfl⟩) R92441
theorem R127241 : Reach 127241 := rs (se 2 (by rfl) ⟨47715, by rfl⟩) R95431
theorem R61823 : Reach 61823 := rs (se 1 (by rfl) ⟨46367, by rfl⟩) R92735
theorem R192935 : Reach 192935 := rs (se 1 (by rfl) ⟨144701, by rfl⟩) R289403
theorem R94679 : Reach 94679 := rs (se 1 (by rfl) ⟨71009, by rfl⟩) R142019
theorem R62255 : Reach 62255 := rs (se 1 (by rfl) ⟨46691, by rfl⟩) R93383
theorem R62375 : Reach 62375 := rs (se 1 (by rfl) ⟨46781, by rfl⟩) R93563
theorem R95407 : Reach 95407 := rs (se 1 (by rfl) ⟨71555, by rfl⟩) R143111
theorem R128411 : Reach 128411 := rs (se 1 (by rfl) ⟨96308, by rfl⟩) R192617
theorem R63227 : Reach 63227 := rs (se 1 (by rfl) ⟨47420, by rfl⟩) R94841
theorem R96137 : Reach 96137 := rs (se 2 (by rfl) ⟨36051, by rfl⟩) R72103
theorem R63463 : Reach 63463 := rs (se 1 (by rfl) ⟨47597, by rfl⟩) R95195
theorem R63571 : Reach 63571 := rs (se 1 (by rfl) ⟨47678, by rfl⟩) R95357
theorem R129167 : Reach 129167 := rs (se 1 (by rfl) ⟨96875, by rfl⟩) R193751
theorem R63679 : Reach 63679 := rs (se 1 (by rfl) ⟨47759, by rfl⟩) R95519
theorem R64415 : Reach 64415 := rs (se 1 (by rfl) ⟨48311, by rfl⟩) R96623
theorem R97321 : Reach 97321 := rs (se 2 (by rfl) ⟨36495, by rfl⟩) R72991
theorem R130195 : Reach 130195 := rs (se 1 (by rfl) ⟨97646, by rfl⟩) R195293
theorem R97463 : Reach 97463 := rs (se 1 (by rfl) ⟨73097, by rfl⟩) R146195
theorem R130301 : Reach 130301 := rs (se 3 (by rfl) ⟨24431, by rfl⟩) R48863
theorem R261415 : Reach 261415 := rs (se 1 (by rfl) ⟨196061, by rfl⟩) R392123
theorem R851267 : Reach 851267 := rs (se 1 (by rfl) ⟨638450, by rfl⟩) R1276901
theorem R64847 : Reach 64847 := rs (se 1 (by rfl) ⟨48635, by rfl⟩) R97271
theorem R261569 : Reach 261569 := rs (se 2 (by rfl) ⟨98088, by rfl⟩) R196177
theorem R196343 : Reach 196343 := rs (se 1 (by rfl) ⟨147257, by rfl⟩) R294515
theorem R65299 : Reach 65299 := rs (se 1 (by rfl) ⟨48974, by rfl⟩) R97949
theorem R98219 : Reach 98219 := rs (se 1 (by rfl) ⟨73664, by rfl⟩) R147329
theorem R196523 : Reach 196523 := rs (se 1 (by rfl) ⟨147392, by rfl⟩) R294785
theorem R65839 : Reach 65839 := rs (se 1 (by rfl) ⟨49379, by rfl⟩) R98759
theorem R131543 : Reach 131543 := rs (se 1 (by rfl) ⟨98657, by rfl⟩) R197315
theorem R98911 : Reach 98911 := rs (se 1 (by rfl) ⟨74183, by rfl⟩) R148367
theorem R197225 : Reach 197225 := rs (se 2 (by rfl) ⟨73959, by rfl⟩) R147919
theorem R98921 : Reach 98921 := rs (se 2 (by rfl) ⟨37095, by rfl⟩) R74191
theorem R3211973 : Reach 3211973 := rs (se 4 (by rfl) ⟨301122, by rfl⟩) R602245
theorem R66863 : Reach 66863 := rs (se 1 (by rfl) ⟨50147, by rfl⟩) R100295
theorem R133111 : Reach 133111 := rs (se 1 (by rfl) ⟨99833, by rfl⟩) R199667
theorem R35199 : Reach 35199 := rs (se 1 (by rfl) ⟨26399, by rfl⟩) R52799
theorem R166333 : Reach 166333 := rs (se 3 (by rfl) ⟨31187, by rfl⟩) R62375
theorem R35375 : Reach 35375 := rs (se 1 (by rfl) ⟨26531, by rfl⟩) R53063
theorem R35431 : Reach 35431 := rs (se 1 (by rfl) ⟨26573, by rfl⟩) R53147
theorem R428651 : Reach 428651 := rs (se 1 (by rfl) ⟨321488, by rfl⟩) R642977
theorem R16714421 : Reach 16714421 := rs (se 5 (by rfl) ⟨783488, by rfl⟩) R1566977
theorem R68435 : Reach 68435 := rs (se 1 (by rfl) ⟨51326, by rfl⟩) R102653
theorem R232301 : Reach 232301 := rs (se 3 (by rfl) ⟨43556, by rfl⟩) R87113
theorem R1149815 : Reach 1149815 := rs (se 1 (by rfl) ⟨862361, by rfl⟩) R1724723
theorem R35807 : Reach 35807 := rs (se 1 (by rfl) ⟨26855, by rfl⟩) R53711
theorem R35835 : Reach 35835 := rs (se 1 (by rfl) ⟨26876, by rfl⟩) R53753
theorem R68663 : Reach 68663 := rs (se 1 (by rfl) ⟨51497, by rfl⟩) R102995
theorem R35903 : Reach 35903 := rs (se 1 (by rfl) ⟨26927, by rfl⟩) R53855
theorem R36223 : Reach 36223 := rs (se 1 (by rfl) ⟨27167, by rfl⟩) R54335
theorem R36251 : Reach 36251 := rs (se 1 (by rfl) ⟨27188, by rfl⟩) R54377
theorem R36319 : Reach 36319 := rs (se 1 (by rfl) ⟨27239, by rfl⟩) R54479
theorem R462347 : Reach 462347 := rs (se 1 (by rfl) ⟨346760, by rfl⟩) R693521
theorem R134729 : Reach 134729 := rs (se 2 (by rfl) ⟨50523, by rfl⟩) R101047
theorem R36455 : Reach 36455 := rs (se 1 (by rfl) ⟨27341, by rfl⟩) R54683
theorem R36603 : Reach 36603 := rs (se 1 (by rfl) ⟨27452, by rfl⟩) R54905
theorem R36671 : Reach 36671 := rs (se 1 (by rfl) ⟨27503, by rfl⟩) R55007
theorem R36735 : Reach 36735 := rs (se 1 (by rfl) ⟨27551, by rfl⟩) R55103
theorem R36847 : Reach 36847 := rs (se 1 (by rfl) ⟨27635, by rfl⟩) R55271
theorem R36859 : Reach 36859 := rs (se 1 (by rfl) ⟨27644, by rfl⟩) R55289
theorem R36927 : Reach 36927 := rs (se 1 (by rfl) ⟨27695, by rfl⟩) R55391
theorem R36967 : Reach 36967 := rs (se 1 (by rfl) ⟨27725, by rfl⟩) R55451
theorem R495719 : Reach 495719 := rs (se 1 (by rfl) ⟨371789, by rfl⟩) R743579
theorem R36991 : Reach 36991 := rs (se 1 (by rfl) ⟨27743, by rfl⟩) R55487
theorem R200839 : Reach 200839 := rs (se 1 (by rfl) ⟨150629, by rfl⟩) R301259
theorem R37019 : Reach 37019 := rs (se 1 (by rfl) ⟨27764, by rfl⟩) R55529
theorem R37039 : Reach 37039 := rs (se 1 (by rfl) ⟨27779, by rfl⟩) R55559
theorem R37223 : Reach 37223 := rs (se 1 (by rfl) ⟨27917, by rfl⟩) R55835
theorem R37275 : Reach 37275 := rs (se 1 (by rfl) ⟨27956, by rfl⟩) R55913
theorem R70121 : Reach 70121 := rs (se 2 (by rfl) ⟨26295, by rfl⟩) R52591
theorem R528977 : Reach 528977 := rs (se 2 (by rfl) ⟨198366, by rfl⟩) R396733
theorem R1577717 : Reach 1577717 := rs (se 5 (by rfl) ⟨73955, by rfl⟩) R147911
theorem R37627 : Reach 37627 := rs (se 1 (by rfl) ⟨28220, by rfl⟩) R56441
theorem R234251 : Reach 234251 := rs (se 1 (by rfl) ⟨175688, by rfl⟩) R351377
theorem R37695 : Reach 37695 := rs (se 1 (by rfl) ⟨28271, by rfl⟩) R56543
theorem R136019 : Reach 136019 := rs (se 1 (by rfl) ⟨102014, by rfl⟩) R204029
theorem R234323 : Reach 234323 := rs (se 1 (by rfl) ⟨175742, by rfl⟩) R351485
theorem R37723 : Reach 37723 := rs (se 1 (by rfl) ⟨28292, by rfl⟩) R56585
theorem R37791 : Reach 37791 := rs (se 1 (by rfl) ⟨28343, by rfl⟩) R56687
theorem R37871 : Reach 37871 := rs (se 1 (by rfl) ⟨28403, by rfl⟩) R56807
theorem R37959 : Reach 37959 := rs (se 1 (by rfl) ⟨28469, by rfl⟩) R56939
theorem R37983 : Reach 37983 := rs (se 1 (by rfl) ⟨28487, by rfl⟩) R56975
theorem R38043 : Reach 38043 := rs (se 1 (by rfl) ⟨28532, by rfl⟩) R57065
theorem R38139 : Reach 38139 := rs (se 1 (by rfl) ⟨28604, by rfl⟩) R57209
theorem R38207 : Reach 38207 := rs (se 1 (by rfl) ⟨28655, by rfl⟩) R57311
theorem R38375 : Reach 38375 := rs (se 1 (by rfl) ⟨28781, by rfl⟩) R57563
theorem R38383 : Reach 38383 := rs (se 1 (by rfl) ⟨28787, by rfl⟩) R57575
theorem R38491 : Reach 38491 := rs (se 1 (by rfl) ⟨28868, by rfl⟩) R57737
theorem R38555 : Reach 38555 := rs (se 1 (by rfl) ⟨28916, by rfl⟩) R57833
theorem R38639 : Reach 38639 := rs (se 1 (by rfl) ⟨28979, by rfl⟩) R57959
theorem R104179 : Reach 104179 := rs (se 1 (by rfl) ⟨78134, by rfl⟩) R156269
theorem R38727 : Reach 38727 := rs (se 1 (by rfl) ⟨29045, by rfl⟩) R58091
theorem R38747 : Reach 38747 := rs (se 1 (by rfl) ⟨29060, by rfl⟩) R58121
theorem R38779 : Reach 38779 := rs (se 1 (by rfl) ⟨29084, by rfl⟩) R58169
theorem R38815 : Reach 38815 := rs (se 1 (by rfl) ⟨29111, by rfl⟩) R58223
theorem R38983 : Reach 38983 := rs (se 1 (by rfl) ⟨29237, by rfl⟩) R58475
theorem R72019 : Reach 72019 := rs (se 1 (by rfl) ⟨54014, by rfl⟩) R108029
theorem R203239 : Reach 203239 := rs (se 1 (by rfl) ⟨152429, by rfl⟩) R304859
theorem R72505 : Reach 72505 := rs (se 2 (by rfl) ⟨27189, by rfl⟩) R54379
theorem R236411 : Reach 236411 := rs (se 1 (by rfl) ⟨177308, by rfl⟩) R354617
theorem R39847 : Reach 39847 := rs (se 1 (by rfl) ⟨29885, by rfl⟩) R59771
theorem R334817 : Reach 334817 := rs (se 2 (by rfl) ⟨125556, by rfl⟩) R251113
theorem R334919 : Reach 334919 := rs (se 1 (by rfl) ⟨251189, by rfl⟩) R502379
theorem R40027 : Reach 40027 := rs (se 1 (by rfl) ⟨30020, by rfl⟩) R60041
theorem R269729 : Reach 269729 := rs (se 2 (by rfl) ⟨101148, by rfl⟩) R202297
theorem R433943 : Reach 433943 := rs (se 1 (by rfl) ⟨325457, by rfl⟩) R650915
theorem R73705 : Reach 73705 := rs (se 2 (by rfl) ⟨27639, by rfl⟩) R55279
theorem R41215 : Reach 41215 := rs (se 1 (by rfl) ⟨30911, by rfl⟩) R61823
theorem R1122569 : Reach 1122569 := rs (se 2 (by rfl) ⟨420963, by rfl⟩) R841927
theorem R41503 : Reach 41503 := rs (se 1 (by rfl) ⟨31127, by rfl⟩) R62255
theorem R2270045 : Reach 2270045 := rs (se 3 (by rfl) ⟨425633, by rfl⟩) R851267
theorem R140129 : Reach 140129 := rs (se 2 (by rfl) ⟨52548, by rfl⟩) R105097
theorem R140393 : Reach 140393 := rs (se 2 (by rfl) ⟨52647, by rfl⟩) R105295
theorem R42151 : Reach 42151 := rs (se 1 (by rfl) ⟨31613, by rfl⟩) R63227
theorem R697517 : Reach 697517 := rs (se 3 (by rfl) ⟨130784, by rfl⟩) R261569
theorem R173593 : Reach 173593 := rs (se 2 (by rfl) ⟨65097, by rfl⟩) R130195
theorem R272159 : Reach 272159 := rs (se 1 (by rfl) ⟨204119, by rfl⟩) R408239
theorem R42943 : Reach 42943 := rs (se 1 (by rfl) ⟨32207, by rfl⟩) R64415
theorem R43231 : Reach 43231 := rs (se 1 (by rfl) ⟨32423, by rfl⟩) R64847
theorem R141547 : Reach 141547 := rs (se 1 (by rfl) ⟨106160, by rfl⟩) R212321
theorem R1648997 : Reach 1648997 := rs (se 4 (by rfl) ⟨154593, by rfl⟩) R309187
theorem R207623 : Reach 207623 := rs (se 1 (by rfl) ⟨155717, by rfl⟩) R311435
theorem R273307 : Reach 273307 := rs (se 1 (by rfl) ⟨204980, by rfl⟩) R409961
theorem R175439 : Reach 175439 := rs (se 1 (by rfl) ⟨131579, by rfl⟩) R263159
theorem R77267 : Reach 77267 := rs (se 1 (by rfl) ⟨57950, by rfl⟩) R115901
theorem R142991 : Reach 142991 := rs (se 1 (by rfl) ⟨107243, by rfl⟩) R214487
theorem R77537 : Reach 77537 := rs (se 2 (by rfl) ⟨29076, by rfl⟩) R58153
theorem R307547 : Reach 307547 := rs (se 1 (by rfl) ⟨230660, by rfl⟩) R461321
theorem R308087 : Reach 308087 := rs (se 1 (by rfl) ⟨231065, by rfl⟩) R462131
theorem R308279 : Reach 308279 := rs (se 1 (by rfl) ⟨231209, by rfl⟩) R462419
theorem R79177 : Reach 79177 := rs (se 2 (by rfl) ⟨29691, by rfl⟩) R59383
theorem R144737 : Reach 144737 := rs (se 2 (by rfl) ⟨54276, by rfl⟩) R108553
theorem R79271 : Reach 79271 := rs (se 1 (by rfl) ⟨59453, by rfl⟩) R118907
theorem R79379 : Reach 79379 := rs (se 1 (by rfl) ⟨59534, by rfl⟩) R119069
theorem R79451 : Reach 79451 := rs (se 1 (by rfl) ⟨59588, by rfl⟩) R119177
theorem R636797 : Reach 636797 := rs (se 3 (by rfl) ⟨119399, by rfl⟩) R238799
theorem R309257 : Reach 309257 := rs (se 2 (by rfl) ⟨115971, by rfl⟩) R231943
theorem R80063 : Reach 80063 := rs (se 1 (by rfl) ⟨60047, by rfl⟩) R120095
theorem R243911 : Reach 243911 := rs (se 1 (by rfl) ⟨182933, by rfl⟩) R365867
theorem R506087 : Reach 506087 := rs (se 1 (by rfl) ⟨379565, by rfl⟩) R759131
theorem R47567 : Reach 47567 := rs (se 1 (by rfl) ⟨35675, by rfl⟩) R71351
theorem R80527 : Reach 80527 := rs (se 1 (by rfl) ⟨60395, by rfl⟩) R120791
theorem R178847 : Reach 178847 := rs (se 1 (by rfl) ⟨134135, by rfl⟩) R268271
theorem R47881 : Reach 47881 := rs (se 2 (by rfl) ⟨17955, by rfl⟩) R35911
theorem R80851 : Reach 80851 := rs (se 1 (by rfl) ⟨60638, by rfl⟩) R121277
theorem R146407 : Reach 146407 := rs (se 1 (by rfl) ⟨109805, by rfl⟩) R219611
theorem R146857 : Reach 146857 := rs (se 2 (by rfl) ⟨55071, by rfl⟩) R110143
theorem R81323 : Reach 81323 := rs (se 1 (by rfl) ⟨60992, by rfl⟩) R121985
theorem R81359 : Reach 81359 := rs (se 1 (by rfl) ⟨61019, by rfl⟩) R122039
theorem R114173 : Reach 114173 := rs (se 3 (by rfl) ⟨21407, by rfl⟩) R42815
theorem R310873 : Reach 310873 := rs (se 2 (by rfl) ⟨116577, by rfl⟩) R233155
theorem R147167 : Reach 147167 := rs (se 1 (by rfl) ⟨110375, by rfl⟩) R220751
theorem R81863 : Reach 81863 := rs (se 1 (by rfl) ⟨61397, by rfl⟩) R122795
theorem R82169 : Reach 82169 := rs (se 2 (by rfl) ⟨30813, by rfl⟩) R61627
theorem R82223 : Reach 82223 := rs (se 1 (by rfl) ⟨61667, by rfl⟩) R123335
theorem R82439 : Reach 82439 := rs (se 1 (by rfl) ⟨61829, by rfl⟩) R123659
theorem R82619 : Reach 82619 := rs (se 1 (by rfl) ⟨61964, by rfl⟩) R123929
theorem R443231 : Reach 443231 := rs (se 1 (by rfl) ⟨332423, by rfl⟩) R664847
theorem R508837 : Reach 508837 := rs (se 4 (by rfl) ⟨47703, by rfl⟩) R95407
theorem R83051 : Reach 83051 := rs (se 1 (by rfl) ⟨62288, by rfl⟩) R124577
theorem R214235 : Reach 214235 := rs (se 1 (by rfl) ⟨160676, by rfl⟩) R321353
theorem R181601 : Reach 181601 := rs (se 2 (by rfl) ⟨68100, by rfl⟩) R136201
theorem R378269 : Reach 378269 := rs (se 3 (by rfl) ⟨70925, by rfl⟩) R141851
theorem R83519 : Reach 83519 := rs (se 1 (by rfl) ⟨62639, by rfl⟩) R125279
theorem R83627 : Reach 83627 := rs (se 1 (by rfl) ⟨62720, by rfl⟩) R125441
theorem R83951 : Reach 83951 := rs (se 1 (by rfl) ⟨62963, by rfl⟩) R125927
theorem R84167 : Reach 84167 := rs (se 1 (by rfl) ⟨63125, by rfl⟩) R126251
theorem R84347 : Reach 84347 := rs (se 1 (by rfl) ⟨63260, by rfl⟩) R126521
theorem R150119 : Reach 150119 := rs (se 1 (by rfl) ⟨112589, by rfl⟩) R225179
theorem R84617 : Reach 84617 := rs (se 2 (by rfl) ⟨31731, by rfl⟩) R63463
theorem R84761 : Reach 84761 := rs (se 2 (by rfl) ⟨31785, by rfl⟩) R63571
theorem R84827 : Reach 84827 := rs (se 1 (by rfl) ⟨63620, by rfl⟩) R127241
theorem R84905 : Reach 84905 := rs (se 2 (by rfl) ⟨31839, by rfl⟩) R63679
theorem R183799 : Reach 183799 := rs (se 1 (by rfl) ⟨137849, by rfl⟩) R275699
theorem R85607 : Reach 85607 := rs (se 1 (by rfl) ⟨64205, by rfl⟩) R128411
theorem R118583 : Reach 118583 := rs (se 1 (by rfl) ⟨88937, by rfl⟩) R177875
theorem R53231 : Reach 53231 := rs (se 1 (by rfl) ⟨39923, by rfl⟩) R79847
theorem R53243 : Reach 53243 := rs (se 1 (by rfl) ⟨39932, by rfl⟩) R79865
theorem R53303 : Reach 53303 := rs (se 1 (by rfl) ⟨39977, by rfl⟩) R79955
theorem R86111 : Reach 86111 := rs (se 1 (by rfl) ⟨64583, by rfl⟩) R129167
theorem R53351 : Reach 53351 := rs (se 1 (by rfl) ⟨40013, by rfl⟩) R80027
theorem R53423 : Reach 53423 := rs (se 1 (by rfl) ⟨40067, by rfl⟩) R80135
theorem R53627 : Reach 53627 := rs (se 1 (by rfl) ⟨40220, by rfl⟩) R80441
theorem R348553 : Reach 348553 := rs (se 2 (by rfl) ⟨130707, by rfl⟩) R261415
theorem R184787 : Reach 184787 := rs (se 1 (by rfl) ⟨138590, by rfl⟩) R277181
theorem R53897 : Reach 53897 := rs (se 2 (by rfl) ⟨20211, by rfl⟩) R40423
theorem R86867 : Reach 86867 := rs (se 1 (by rfl) ⟨65150, by rfl⟩) R130301
theorem R54107 : Reach 54107 := rs (se 1 (by rfl) ⟨40580, by rfl⟩) R81161
theorem R119663 : Reach 119663 := rs (se 1 (by rfl) ⟨89747, by rfl⟩) R179495
theorem R316295 : Reach 316295 := rs (se 1 (by rfl) ⟨237221, by rfl⟩) R474443
theorem R87065 : Reach 87065 := rs (se 2 (by rfl) ⟨32649, by rfl⟩) R65299
theorem R54569 : Reach 54569 := rs (se 2 (by rfl) ⟨20463, by rfl⟩) R40927
theorem R87407 : Reach 87407 := rs (se 1 (by rfl) ⟨65555, by rfl⟩) R131111
theorem R54767 : Reach 54767 := rs (se 1 (by rfl) ⟨41075, by rfl⟩) R82151
theorem R87839 : Reach 87839 := rs (se 1 (by rfl) ⟨65879, by rfl⟩) R131759
theorem R55163 : Reach 55163 := rs (se 1 (by rfl) ⟨41372, by rfl⟩) R82745
theorem R55199 : Reach 55199 := rs (se 1 (by rfl) ⟨41399, by rfl⟩) R82799
theorem R350171 : Reach 350171 := rs (se 1 (by rfl) ⟨262628, by rfl⟩) R525257
theorem R153569 : Reach 153569 := rs (se 2 (by rfl) ⟨57588, by rfl⟩) R115177
theorem R55433 : Reach 55433 := rs (se 2 (by rfl) ⟨20787, by rfl⟩) R41575
theorem R55583 : Reach 55583 := rs (se 1 (by rfl) ⟨41687, by rfl⟩) R83375
theorem R121247 : Reach 121247 := rs (se 1 (by rfl) ⟨90935, by rfl⟩) R181871
theorem R186785 : Reach 186785 := rs (se 2 (by rfl) ⟨70044, by rfl⟩) R140089
theorem R285281 : Reach 285281 := rs (se 2 (by rfl) ⟨106980, by rfl⟩) R213961
theorem R580229 : Reach 580229 := rs (se 4 (by rfl) ⟨54396, by rfl⟩) R108793
theorem R56135 : Reach 56135 := rs (se 1 (by rfl) ⟨42101, by rfl⟩) R84203
theorem R56999 : Reach 56999 := rs (se 1 (by rfl) ⟨42749, by rfl⟩) R85499
theorem R57119 : Reach 57119 := rs (se 1 (by rfl) ⟨42839, by rfl⟩) R85679
theorem R90011 : Reach 90011 := rs (se 1 (by rfl) ⟨67508, by rfl⟩) R135017
theorem R122867 : Reach 122867 := rs (se 1 (by rfl) ⟨92150, by rfl⟩) R184301
theorem R57335 : Reach 57335 := rs (se 1 (by rfl) ⟨43001, by rfl⟩) R86003
theorem R57551 : Reach 57551 := rs (se 1 (by rfl) ⟨43163, by rfl⟩) R86327
theorem R57599 : Reach 57599 := rs (se 1 (by rfl) ⟨43199, by rfl⟩) R86399
theorem R811619 : Reach 811619 := rs (se 1 (by rfl) ⟨608714, by rfl⟩) R1217429
theorem R90791 : Reach 90791 := rs (se 1 (by rfl) ⟨68093, by rfl⟩) R136187
theorem R189215 : Reach 189215 := rs (se 1 (by rfl) ⟨141911, by rfl⟩) R283823
theorem R91115 : Reach 91115 := rs (se 1 (by rfl) ⟨68336, by rfl⟩) R136673
theorem R58415 : Reach 58415 := rs (se 1 (by rfl) ⟨43811, by rfl⟩) R87623
theorem R320669 : Reach 320669 := rs (se 3 (by rfl) ⟨60125, by rfl⟩) R120251
theorem R58535 : Reach 58535 := rs (se 1 (by rfl) ⟨43901, by rfl⟩) R87803
theorem R59359 : Reach 59359 := rs (se 1 (by rfl) ⟨44519, by rfl⟩) R89039
theorem R190451 : Reach 190451 := rs (se 1 (by rfl) ⟨142838, by rfl⟩) R285677
theorem R288787 : Reach 288787 := rs (se 1 (by rfl) ⟨216590, by rfl⟩) R433181
theorem R616733 : Reach 616733 := rs (se 3 (by rfl) ⟨115637, by rfl⟩) R231275
theorem R289595 : Reach 289595 := rs (se 1 (by rfl) ⟨217196, by rfl⟩) R434393
theorem R158543 : Reach 158543 := rs (se 1 (by rfl) ⟨118907, by rfl⟩) R237815
theorem R289655 : Reach 289655 := rs (se 1 (by rfl) ⟨217241, by rfl⟩) R434483
theorem R323129 : Reach 323129 := rs (se 2 (by rfl) ⟨121173, by rfl⟩) R242347
theorem R355913 : Reach 355913 := rs (se 2 (by rfl) ⟨133467, by rfl⟩) R266935
theorem R94567 : Reach 94567 := rs (se 1 (by rfl) ⟨70925, by rfl⟩) R141851
theorem R127439 : Reach 127439 := rs (se 1 (by rfl) ⟨95579, by rfl⟩) R191159
theorem R128623 : Reach 128623 := rs (se 1 (by rfl) ⟨96467, by rfl⟩) R192935
theorem R63119 : Reach 63119 := rs (se 1 (by rfl) ⟨47339, by rfl⟩) R94679
theorem R161975 : Reach 161975 := rs (se 1 (by rfl) ⟨121481, by rfl⟩) R242963
theorem R64091 : Reach 64091 := rs (se 1 (by rfl) ⟨48068, by rfl⟩) R96137
theorem R129761 : Reach 129761 := rs (se 2 (by rfl) ⟨48660, by rfl⟩) R97321
theorem R97561 : Reach 97561 := rs (se 2 (by rfl) ⟨36585, by rfl⟩) R73171
theorem R64975 : Reach 64975 := rs (se 1 (by rfl) ⟨48731, by rfl⟩) R97463
theorem R97787 : Reach 97787 := rs (se 1 (by rfl) ⟨73340, by rfl⟩) R146681
theorem R98057 : Reach 98057 := rs (se 2 (by rfl) ⟨36771, by rfl⟩) R73543
theorem R261917 : Reach 261917 := rs (se 3 (by rfl) ⟨49109, by rfl⟩) R98219
theorem R130895 : Reach 130895 := rs (se 1 (by rfl) ⟨98171, by rfl⟩) R196343
theorem R131015 : Reach 131015 := rs (se 1 (by rfl) ⟨98261, by rfl⟩) R196523
theorem R131483 : Reach 131483 := rs (se 1 (by rfl) ⟨98612, by rfl⟩) R197225
theorem R65947 : Reach 65947 := rs (se 1 (by rfl) ⟨49460, by rfl⟩) R98921
theorem R295487 : Reach 295487 := rs (se 1 (by rfl) ⟨221615, by rfl⟩) R443231
theorem R131881 : Reach 131881 := rs (se 2 (by rfl) ⟨49455, by rfl⟩) R98911
theorem R1410605 : Reach 1410605 := rs (se 3 (by rfl) ⟨264488, by rfl⟩) R528977
theorem R100079 : Reach 100079 := rs (se 1 (by rfl) ⟨75059, by rfl⟩) R150119
theorem R11142947 : Reach 11142947 := rs (se 1 (by rfl) ⟨8357210, by rfl⟩) R16714421
theorem R231457 : Reach 231457 := rs (se 2 (by rfl) ⟨86796, by rfl⟩) R173593
theorem R1083941 : Reach 1083941 := rs (se 4 (by rfl) ⟨101619, by rfl⟩) R203239
theorem R35487 : Reach 35487 := rs (se 1 (by rfl) ⟨26615, by rfl⟩) R53231
theorem R35495 : Reach 35495 := rs (se 1 (by rfl) ⟨26621, by rfl⟩) R53243
theorem R35535 : Reach 35535 := rs (se 1 (by rfl) ⟨26651, by rfl⟩) R53303
theorem R35567 : Reach 35567 := rs (se 1 (by rfl) ⟨26675, by rfl⟩) R53351
theorem R330479 : Reach 330479 := rs (se 1 (by rfl) ⟨247859, by rfl⟩) R495719
theorem R35615 : Reach 35615 := rs (se 1 (by rfl) ⟨26711, by rfl⟩) R53423
theorem R35751 : Reach 35751 := rs (se 1 (by rfl) ⟨26813, by rfl⟩) R53627
theorem R35931 : Reach 35931 := rs (se 1 (by rfl) ⟨26948, by rfl⟩) R53897
theorem R1051811 : Reach 1051811 := rs (se 1 (by rfl) ⟨788858, by rfl⟩) R1577717
theorem R36071 : Reach 36071 := rs (se 1 (by rfl) ⟨27053, by rfl⟩) R54107
theorem R36379 : Reach 36379 := rs (se 1 (by rfl) ⟨27284, by rfl⟩) R54569
theorem R36511 : Reach 36511 := rs (se 1 (by rfl) ⟨27383, by rfl⟩) R54767
theorem R364409 : Reach 364409 := rs (se 2 (by rfl) ⟨136653, by rfl⟩) R273307
theorem R36775 : Reach 36775 := rs (se 1 (by rfl) ⟨27581, by rfl⟩) R55163
theorem R36799 : Reach 36799 := rs (se 1 (by rfl) ⟨27599, by rfl⟩) R55199
theorem R233447 : Reach 233447 := rs (se 1 (by rfl) ⟨175085, by rfl⟩) R350171
theorem R102379 : Reach 102379 := rs (se 1 (by rfl) ⟨76784, by rfl⟩) R153569
theorem R36955 : Reach 36955 := rs (se 1 (by rfl) ⟨27716, by rfl⟩) R55433
theorem R37055 : Reach 37055 := rs (se 1 (by rfl) ⟨27791, by rfl⟩) R55583
theorem R37423 : Reach 37423 := rs (se 1 (by rfl) ⟨28067, by rfl⟩) R56135
theorem R37999 : Reach 37999 := rs (se 1 (by rfl) ⟨28499, by rfl⟩) R56999
theorem R38079 : Reach 38079 := rs (se 1 (by rfl) ⟨28559, by rfl⟩) R57119
theorem R38223 : Reach 38223 := rs (se 1 (by rfl) ⟨28667, by rfl⟩) R57335
theorem R38367 : Reach 38367 := rs (se 1 (by rfl) ⟨28775, by rfl⟩) R57551
theorem R38399 : Reach 38399 := rs (se 1 (by rfl) ⟨28799, by rfl⟩) R57599
theorem R267785 : Reach 267785 := rs (se 2 (by rfl) ⟨100419, by rfl⟩) R200839
theorem R464737 : Reach 464737 := rs (se 2 (by rfl) ⟨174276, by rfl⟩) R348553
theorem R1513363 : Reach 1513363 := rs (se 1 (by rfl) ⟨1135022, by rfl⟩) R2270045
theorem R38943 : Reach 38943 := rs (se 1 (by rfl) ⟨29207, by rfl⟩) R58415
theorem R39023 : Reach 39023 := rs (se 1 (by rfl) ⟨29267, by rfl⟩) R58535
theorem R465011 : Reach 465011 := rs (se 1 (by rfl) ⟨348758, by rfl⟩) R697517
theorem R105569 : Reach 105569 := rs (se 2 (by rfl) ⟨39588, by rfl⟩) R79177
theorem R105695 : Reach 105695 := rs (se 1 (by rfl) ⟨79271, by rfl⟩) R158543
theorem R171497 : Reach 171497 := rs (se 2 (by rfl) ⟨64311, by rfl⟩) R128623
theorem R138905 : Reach 138905 := rs (se 2 (by rfl) ⟨52089, by rfl⟩) R104179
theorem R237275 : Reach 237275 := rs (se 1 (by rfl) ⟨177956, by rfl⟩) R355913
theorem R205031 : Reach 205031 := rs (se 1 (by rfl) ⟨153773, by rfl⟩) R307547
theorem R205391 : Reach 205391 := rs (se 1 (by rfl) ⟨154043, by rfl⟩) R308087
theorem R205519 : Reach 205519 := rs (se 1 (by rfl) ⟨154139, by rfl⟩) R308279
theorem R107369 : Reach 107369 := rs (se 2 (by rfl) ⟨40263, by rfl⟩) R80527
theorem R42079 : Reach 42079 := rs (se 1 (by rfl) ⟨31559, by rfl⟩) R63119
theorem R107801 : Reach 107801 := rs (se 2 (by rfl) ⟨40425, by rfl⟩) R80851
theorem R206171 : Reach 206171 := rs (se 1 (by rfl) ⟨154628, by rfl⟩) R309257
theorem R107983 : Reach 107983 := rs (se 1 (by rfl) ⟨80987, by rfl⟩) R161975
theorem R337391 : Reach 337391 := rs (se 1 (by rfl) ⟨253043, by rfl⟩) R506087
theorem R42727 : Reach 42727 := rs (se 1 (by rfl) ⟨32045, by rfl⟩) R64091
theorem R76115 : Reach 76115 := rs (se 1 (by rfl) ⟨57086, by rfl⟩) R114173
theorem R174611 : Reach 174611 := rs (se 1 (by rfl) ⟨130958, by rfl⟩) R261917
theorem R2141315 : Reach 2141315 := rs (se 1 (by rfl) ⟨1605986, by rfl⟩) R3211973
theorem R142823 : Reach 142823 := rs (se 1 (by rfl) ⟨107117, by rfl⟩) R214235
theorem R143005 : Reach 143005 := rs (se 3 (by rfl) ⟨26813, by rfl⟩) R53627
theorem R45623 : Reach 45623 := rs (se 1 (by rfl) ⟨34217, by rfl⟩) R68435
theorem R45775 : Reach 45775 := rs (se 1 (by rfl) ⟨34331, by rfl⟩) R68663
theorem R308231 : Reach 308231 := rs (se 1 (by rfl) ⟨231173, by rfl⟩) R462347
theorem R79055 : Reach 79055 := rs (se 1 (by rfl) ⟨59291, by rfl⟩) R118583
theorem R79145 : Reach 79145 := rs (se 2 (by rfl) ⟨29679, by rfl⟩) R59359
theorem R177481 : Reach 177481 := rs (se 2 (by rfl) ⟨66555, by rfl⟩) R133111
theorem R46747 : Reach 46747 := rs (se 1 (by rfl) ⟨35060, by rfl⟩) R70121
theorem R79775 : Reach 79775 := rs (se 1 (by rfl) ⟨59831, by rfl⟩) R119663
theorem R210863 : Reach 210863 := rs (se 1 (by rfl) ⟨158147, by rfl⟩) R316295
theorem R178301 : Reach 178301 := rs (se 3 (by rfl) ⟨33431, by rfl⟩) R66863
theorem R80831 : Reach 80831 := rs (se 1 (by rfl) ⟨60623, by rfl⟩) R121247
theorem R245065 : Reach 245065 := rs (se 2 (by rfl) ⟨91899, by rfl⟩) R183799
theorem R179819 : Reach 179819 := rs (se 1 (by rfl) ⟨134864, by rfl⟩) R269729
theorem R147197 : Reach 147197 := rs (se 3 (by rfl) ⟨27599, by rfl⟩) R55199
theorem R81911 : Reach 81911 := rs (se 1 (by rfl) ⟨61433, by rfl⟩) R122867
theorem R541079 : Reach 541079 := rs (se 1 (by rfl) ⟨405809, by rfl⟩) R811619
theorem R213779 : Reach 213779 := rs (se 1 (by rfl) ⟨160334, by rfl⟩) R320669
theorem R181439 : Reach 181439 := rs (se 1 (by rfl) ⟨136079, by rfl⟩) R272159
theorem R411155 : Reach 411155 := rs (se 1 (by rfl) ⟨308366, by rfl⟩) R616733
theorem R1099331 : Reach 1099331 := rs (se 1 (by rfl) ⟨824498, by rfl⟩) R1648997
theorem R772253 : Reach 772253 := rs (se 3 (by rfl) ⟨144797, by rfl⟩) R289595
theorem R116959 : Reach 116959 := rs (se 1 (by rfl) ⟨87719, by rfl⟩) R175439
theorem R51511 : Reach 51511 := rs (se 1 (by rfl) ⟨38633, by rfl⟩) R77267
theorem R3066173 : Reach 3066173 := rs (se 3 (by rfl) ⟨574907, by rfl⟩) R1149815
theorem R215419 : Reach 215419 := rs (se 1 (by rfl) ⟨161564, by rfl⟩) R323129
theorem R51691 : Reach 51691 := rs (se 1 (by rfl) ⟨38768, by rfl⟩) R77537
theorem R84959 : Reach 84959 := rs (se 1 (by rfl) ⟨63719, by rfl⟩) R127439
theorem R52847 : Reach 52847 := rs (se 1 (by rfl) ⟨39635, by rfl⟩) R79271
theorem R52919 : Reach 52919 := rs (se 1 (by rfl) ⟨39689, by rfl⟩) R79379
theorem R52967 : Reach 52967 := rs (se 1 (by rfl) ⟨39725, by rfl⟩) R79451
theorem R53129 : Reach 53129 := rs (se 2 (by rfl) ⟨19923, by rfl⟩) R39847
theorem R53369 : Reach 53369 := rs (se 2 (by rfl) ⟨20013, by rfl⟩) R40027
theorem R53375 : Reach 53375 := rs (se 1 (by rfl) ⟨40031, by rfl⟩) R80063
theorem R119231 : Reach 119231 := rs (se 1 (by rfl) ⟨89423, by rfl⟩) R178847
theorem R86507 : Reach 86507 := rs (se 1 (by rfl) ⟨64880, by rfl⟩) R129761
theorem R86633 : Reach 86633 := rs (se 2 (by rfl) ⟨32487, by rfl⟩) R64975
theorem R414497 : Reach 414497 := rs (se 2 (by rfl) ⟨155436, by rfl⟩) R310873
theorem R54215 : Reach 54215 := rs (se 1 (by rfl) ⟨40661, by rfl⟩) R81323
theorem R54239 : Reach 54239 := rs (se 1 (by rfl) ⟨40679, by rfl⟩) R81359
theorem R349373 : Reach 349373 := rs (se 3 (by rfl) ⟨65507, by rfl⟩) R131015
theorem R87263 : Reach 87263 := rs (se 1 (by rfl) ⟨65447, by rfl⟩) R130895
theorem R54575 : Reach 54575 := rs (se 1 (by rfl) ⟨40931, by rfl⟩) R81863
theorem R54779 : Reach 54779 := rs (se 1 (by rfl) ⟨41084, by rfl⟩) R82169
theorem R54815 : Reach 54815 := rs (se 1 (by rfl) ⟨41111, by rfl⟩) R82223
theorem R87695 : Reach 87695 := rs (se 1 (by rfl) ⟨65771, by rfl⟩) R131543
theorem R54953 : Reach 54953 := rs (se 2 (by rfl) ⟨20607, by rfl⟩) R41215
theorem R54959 : Reach 54959 := rs (se 1 (by rfl) ⟨41219, by rfl⟩) R82439
theorem R87785 : Reach 87785 := rs (se 2 (by rfl) ⟨32919, by rfl⟩) R65839
theorem R55079 : Reach 55079 := rs (se 1 (by rfl) ⟨41309, by rfl⟩) R82619
theorem R55337 : Reach 55337 := rs (se 2 (by rfl) ⟨20751, by rfl⟩) R41503
theorem R55367 : Reach 55367 := rs (se 1 (by rfl) ⟨41525, by rfl⟩) R83051
theorem R121067 : Reach 121067 := rs (se 1 (by rfl) ⟨90800, by rfl⟩) R181601
theorem R252179 : Reach 252179 := rs (se 1 (by rfl) ⟨189134, by rfl⟩) R378269
theorem R55679 : Reach 55679 := rs (se 1 (by rfl) ⟨41759, by rfl⟩) R83519
theorem R55751 : Reach 55751 := rs (se 1 (by rfl) ⟨41813, by rfl⟩) R83627
theorem R678449 : Reach 678449 := rs (se 2 (by rfl) ⟨254418, by rfl⟩) R508837
theorem R55967 : Reach 55967 := rs (se 1 (by rfl) ⟨41975, by rfl⟩) R83951
theorem R56111 : Reach 56111 := rs (se 1 (by rfl) ⟨42083, by rfl⟩) R84167
theorem R56201 : Reach 56201 := rs (se 2 (by rfl) ⟨21075, by rfl⟩) R42151
theorem R56231 : Reach 56231 := rs (se 1 (by rfl) ⟨42173, by rfl⟩) R84347
theorem R285767 : Reach 285767 := rs (se 1 (by rfl) ⟨214325, by rfl⟩) R428651
theorem R56411 : Reach 56411 := rs (se 1 (by rfl) ⟨42308, by rfl⟩) R84617
theorem R56507 : Reach 56507 := rs (se 1 (by rfl) ⟨42380, by rfl⟩) R84761
theorem R56551 : Reach 56551 := rs (se 1 (by rfl) ⟨42413, by rfl⟩) R84827
theorem R154867 : Reach 154867 := rs (se 1 (by rfl) ⟨116150, by rfl⟩) R232301
theorem R56603 : Reach 56603 := rs (se 1 (by rfl) ⟨42452, by rfl⟩) R84905
theorem R89819 : Reach 89819 := rs (se 1 (by rfl) ⟨67364, by rfl⟩) R134729
theorem R57071 : Reach 57071 := rs (se 1 (by rfl) ⟨42803, by rfl⟩) R85607
theorem R57257 : Reach 57257 := rs (se 2 (by rfl) ⟨21471, by rfl⟩) R42943
theorem R385049 : Reach 385049 := rs (se 2 (by rfl) ⟨144393, by rfl⟩) R288787
theorem R57407 : Reach 57407 := rs (se 1 (by rfl) ⟨43055, by rfl⟩) R86111
theorem R57641 : Reach 57641 := rs (se 2 (by rfl) ⟨21615, by rfl⟩) R43231
theorem R123191 : Reach 123191 := rs (se 1 (by rfl) ⟨92393, by rfl⟩) R184787
theorem R188729 : Reach 188729 := rs (se 2 (by rfl) ⟨70773, by rfl⟩) R141547
theorem R156167 : Reach 156167 := rs (se 1 (by rfl) ⟨117125, by rfl⟩) R234251
theorem R90679 : Reach 90679 := rs (se 1 (by rfl) ⟨68009, by rfl⟩) R136019
theorem R156215 : Reach 156215 := rs (se 1 (by rfl) ⟨117161, by rfl⟩) R234323
theorem R57911 : Reach 57911 := rs (se 1 (by rfl) ⟨43433, by rfl⟩) R86867
theorem R221777 : Reach 221777 := rs (se 2 (by rfl) ⟨83166, by rfl⟩) R166333
theorem R58043 : Reach 58043 := rs (se 1 (by rfl) ⟨43532, by rfl⟩) R87065
theorem R58271 : Reach 58271 := rs (se 1 (by rfl) ⟨43703, by rfl⟩) R87407
theorem R58559 : Reach 58559 := rs (se 1 (by rfl) ⟨43919, by rfl⟩) R87839
theorem R124523 : Reach 124523 := rs (se 1 (by rfl) ⟨93392, by rfl⟩) R186785
theorem R190187 : Reach 190187 := rs (se 1 (by rfl) ⟨142640, by rfl⟩) R285281
theorem R386819 : Reach 386819 := rs (se 1 (by rfl) ⟨290114, by rfl⟩) R580229
theorem R157607 : Reach 157607 := rs (se 1 (by rfl) ⟨118205, by rfl⟩) R236411
theorem R223211 : Reach 223211 := rs (se 1 (by rfl) ⟨167408, by rfl⟩) R334817
theorem R223279 : Reach 223279 := rs (se 1 (by rfl) ⟨167459, by rfl⟩) R334919
theorem R289295 : Reach 289295 := rs (se 1 (by rfl) ⟨216971, by rfl⟩) R433943
theorem R60007 : Reach 60007 := rs (se 1 (by rfl) ⟨45005, by rfl⟩) R90011
theorem R748379 : Reach 748379 := rs (se 1 (by rfl) ⟨561284, by rfl⟩) R1122569
theorem R60527 : Reach 60527 := rs (se 1 (by rfl) ⟨45395, by rfl⟩) R90791
theorem R126089 : Reach 126089 := rs (se 2 (by rfl) ⟨47283, by rfl⟩) R94567
theorem R650429 : Reach 650429 := rs (se 3 (by rfl) ⟨121955, by rfl⟩) R243911
theorem R126143 : Reach 126143 := rs (se 1 (by rfl) ⟨94607, by rfl⟩) R189215
theorem R93419 : Reach 93419 := rs (se 1 (by rfl) ⟨70064, by rfl⟩) R140129
theorem R60743 : Reach 60743 := rs (se 1 (by rfl) ⟨45557, by rfl⟩) R91115
theorem R93595 : Reach 93595 := rs (se 1 (by rfl) ⟨70196, by rfl⟩) R140393
theorem R126845 : Reach 126845 := rs (se 3 (by rfl) ⟨23783, by rfl⟩) R47567
theorem R126967 : Reach 126967 := rs (se 1 (by rfl) ⟨95225, by rfl⟩) R190451
theorem R193103 : Reach 193103 := rs (se 1 (by rfl) ⟨144827, by rfl⟩) R289655
theorem R553661 : Reach 553661 := rs (se 3 (by rfl) ⟨103811, by rfl⟩) R207623
theorem R95327 : Reach 95327 := rs (se 1 (by rfl) ⟨71495, by rfl⟩) R142991
theorem R96025 : Reach 96025 := rs (se 2 (by rfl) ⟨36009, by rfl⟩) R72019
theorem R96491 : Reach 96491 := rs (se 1 (by rfl) ⟨72368, by rfl⟩) R144737
theorem R63841 : Reach 63841 := rs (se 2 (by rfl) ⟨23940, by rfl⟩) R47881
theorem R96673 : Reach 96673 := rs (se 2 (by rfl) ⟨36252, by rfl⟩) R72505
theorem R424531 : Reach 424531 := rs (se 1 (by rfl) ⟨318398, by rfl⟩) R636797
theorem R195209 : Reach 195209 := rs (se 2 (by rfl) ⟨73203, by rfl⟩) R146407
theorem R130081 : Reach 130081 := rs (se 2 (by rfl) ⟨48780, by rfl⟩) R97561
theorem R195809 : Reach 195809 := rs (se 2 (by rfl) ⟨73428, by rfl⟩) R146857
theorem R65191 : Reach 65191 := rs (se 1 (by rfl) ⟨48893, by rfl⟩) R97787
theorem R98111 : Reach 98111 := rs (se 1 (by rfl) ⟨73583, by rfl⟩) R147167
theorem R65371 : Reach 65371 := rs (se 1 (by rfl) ⟨49028, by rfl⟩) R98057
theorem R98273 : Reach 98273 := rs (se 2 (by rfl) ⟨36852, by rfl⟩) R73705
theorem R360719 : Reach 360719 := rs (se 1 (by rfl) ⟨270539, by rfl⟩) R541079
theorem R196991 : Reach 196991 := rs (se 1 (by rfl) ⟨147743, by rfl⟩) R295487
theorem R66719 : Reach 66719 := rs (se 1 (by rfl) ⟨50039, by rfl⟩) R100079
theorem R722627 : Reach 722627 := rs (se 1 (by rfl) ⟨541970, by rfl⟩) R1083941
theorem R35231 : Reach 35231 := rs (se 1 (by rfl) ⟨26423, by rfl⟩) R52847
theorem R35279 : Reach 35279 := rs (se 1 (by rfl) ⟨26459, by rfl⟩) R52919
theorem R35311 : Reach 35311 := rs (se 1 (by rfl) ⟨26483, by rfl⟩) R52967
theorem R35419 : Reach 35419 := rs (se 1 (by rfl) ⟨26564, by rfl⟩) R53129
theorem R35579 : Reach 35579 := rs (se 1 (by rfl) ⟨26684, by rfl⟩) R53369
theorem R35583 : Reach 35583 := rs (se 1 (by rfl) ⟨26687, by rfl⟩) R53375
theorem R68681 : Reach 68681 := rs (se 2 (by rfl) ⟨25755, by rfl⟩) R51511
theorem R36143 : Reach 36143 := rs (se 1 (by rfl) ⟨27107, by rfl⟩) R54215
theorem R68921 : Reach 68921 := rs (se 2 (by rfl) ⟨25845, by rfl⟩) R51691
theorem R36159 : Reach 36159 := rs (se 1 (by rfl) ⟨27119, by rfl⟩) R54239
theorem R36383 : Reach 36383 := rs (se 1 (by rfl) ⟨27287, by rfl⟩) R54575
theorem R36519 : Reach 36519 := rs (se 1 (by rfl) ⟨27389, by rfl⟩) R54779
theorem R36543 : Reach 36543 := rs (se 1 (by rfl) ⟨27407, by rfl⟩) R54815
theorem R36635 : Reach 36635 := rs (se 1 (by rfl) ⟨27476, by rfl⟩) R54953
theorem R36639 : Reach 36639 := rs (se 1 (by rfl) ⟨27479, by rfl⟩) R54959
theorem R36719 : Reach 36719 := rs (se 1 (by rfl) ⟨27539, by rfl⟩) R55079
theorem R36891 : Reach 36891 := rs (se 1 (by rfl) ⟨27668, by rfl⟩) R55337
theorem R36911 : Reach 36911 := rs (se 1 (by rfl) ⟨27683, by rfl⟩) R55367
theorem R168119 : Reach 168119 := rs (se 1 (by rfl) ⟨126089, by rfl⟩) R252179
theorem R37119 : Reach 37119 := rs (se 1 (by rfl) ⟨27839, by rfl⟩) R55679
theorem R37167 : Reach 37167 := rs (se 1 (by rfl) ⟨27875, by rfl⟩) R55751
theorem R37311 : Reach 37311 := rs (se 1 (by rfl) ⟨27983, by rfl⟩) R55967
theorem R37407 : Reach 37407 := rs (se 1 (by rfl) ⟨28055, by rfl⟩) R56111
theorem R37467 : Reach 37467 := rs (se 1 (by rfl) ⟨28100, by rfl⟩) R56201
theorem R37487 : Reach 37487 := rs (se 1 (by rfl) ⟨28115, by rfl⟩) R56231
theorem R37607 : Reach 37607 := rs (se 1 (by rfl) ⟨28205, by rfl⟩) R56411
theorem R70379 : Reach 70379 := rs (se 1 (by rfl) ⟨52784, by rfl⟩) R105569
theorem R37671 : Reach 37671 := rs (se 1 (by rfl) ⟨28253, by rfl⟩) R56507
theorem R70463 : Reach 70463 := rs (se 1 (by rfl) ⟨52847, by rfl⟩) R105695
theorem R37735 : Reach 37735 := rs (se 1 (by rfl) ⟨28301, by rfl⟩) R56603
theorem R562301 : Reach 562301 := rs (se 3 (by rfl) ⟨105431, by rfl⟩) R210863
theorem R38047 : Reach 38047 := rs (se 1 (by rfl) ⟨28535, by rfl⟩) R57071
theorem R38171 : Reach 38171 := rs (se 1 (by rfl) ⟨28628, by rfl⟩) R57257
theorem R136505 : Reach 136505 := rs (se 2 (by rfl) ⟨51189, by rfl⟩) R102379
theorem R169289 : Reach 169289 := rs (se 2 (by rfl) ⟨63483, by rfl⟩) R126967
theorem R38271 : Reach 38271 := rs (se 1 (by rfl) ⟨28703, by rfl⟩) R57407
theorem R136687 : Reach 136687 := rs (se 1 (by rfl) ⟨102515, by rfl⟩) R205031
theorem R38427 : Reach 38427 := rs (se 1 (by rfl) ⟨28820, by rfl⟩) R57641
theorem R104111 : Reach 104111 := rs (se 1 (by rfl) ⟨78083, by rfl⟩) R156167
theorem R38607 : Reach 38607 := rs (se 1 (by rfl) ⟨28955, by rfl⟩) R57911
theorem R136927 : Reach 136927 := rs (se 1 (by rfl) ⟨102695, by rfl⟩) R205391
theorem R38695 : Reach 38695 := rs (se 1 (by rfl) ⟨29021, by rfl⟩) R58043
theorem R71579 : Reach 71579 := rs (se 1 (by rfl) ⟨53684, by rfl⟩) R107369
theorem R38847 : Reach 38847 := rs (se 1 (by rfl) ⟨29135, by rfl⟩) R58271
theorem R39039 : Reach 39039 := rs (se 1 (by rfl) ⟨29279, by rfl⟩) R58559
theorem R71867 : Reach 71867 := rs (se 1 (by rfl) ⟨53900, by rfl⟩) R107801
theorem R137447 : Reach 137447 := rs (se 1 (by rfl) ⟨103085, by rfl⟩) R206171
theorem R105071 : Reach 105071 := rs (se 1 (by rfl) ⟨78803, by rfl⟩) R157607
theorem R236641 : Reach 236641 := rs (se 2 (by rfl) ⟨88740, by rfl⟩) R177481
theorem R498919 : Reach 498919 := rs (se 1 (by rfl) ⟨374189, by rfl⟩) R748379
theorem R40351 : Reach 40351 := rs (se 1 (by rfl) ⟨30263, by rfl⟩) R60527
theorem R433619 : Reach 433619 := rs (se 1 (by rfl) ⟨325214, by rfl⟩) R650429
theorem R40495 : Reach 40495 := rs (se 1 (by rfl) ⟨30371, by rfl⟩) R60743
theorem R369107 : Reach 369107 := rs (se 1 (by rfl) ⟨276830, by rfl⟩) R553661
theorem R205487 : Reach 205487 := rs (se 1 (by rfl) ⟨154115, by rfl⟩) R308231
theorem R566041 : Reach 566041 := rs (se 2 (by rfl) ⟨212265, by rfl⟩) R424531
theorem R140575 : Reach 140575 := rs (se 1 (by rfl) ⟨105431, by rfl⟩) R210863
theorem R173441 : Reach 173441 := rs (se 2 (by rfl) ⟨65040, by rfl⟩) R130081
theorem R75401 : Reach 75401 := rs (se 2 (by rfl) ⟨28275, by rfl⟩) R56551
theorem R206489 : Reach 206489 := rs (se 2 (by rfl) ⟨77433, by rfl⟩) R154867
theorem R1190821 : Reach 1190821 := rs (se 4 (by rfl) ⟨111639, by rfl⟩) R223279
theorem R142519 : Reach 142519 := rs (se 1 (by rfl) ⟨106889, by rfl⟩) R213779
theorem R274025 : Reach 274025 := rs (se 2 (by rfl) ⟨102759, by rfl⟩) R205519
theorem R274103 : Reach 274103 := rs (se 1 (by rfl) ⟨205577, by rfl⟩) R411155
theorem R732887 : Reach 732887 := rs (se 1 (by rfl) ⟨549665, by rfl⟩) R1099331
theorem R175841 : Reach 175841 := rs (se 2 (by rfl) ⟨65940, by rfl⟩) R131881
theorem R2044115 : Reach 2044115 := rs (se 1 (by rfl) ⟨1533086, by rfl⟩) R3066173
theorem R143977 : Reach 143977 := rs (se 2 (by rfl) ⟨53991, by rfl⟩) R107983
theorem R701207 : Reach 701207 := rs (se 1 (by rfl) ⟨525905, by rfl⟩) R1051811
theorem R242939 : Reach 242939 := rs (se 1 (by rfl) ⟨182204, by rfl⟩) R364409
theorem R308609 : Reach 308609 := rs (se 2 (by rfl) ⟨115728, by rfl⟩) R231457
theorem R79487 : Reach 79487 := rs (se 1 (by rfl) ⟨59615, by rfl⟩) R119231
theorem R931661 : Reach 931661 := rs (se 3 (by rfl) ⟨174686, by rfl⟩) R349373
theorem R80009 : Reach 80009 := rs (se 2 (by rfl) ⟨30003, by rfl⟩) R60007
theorem R178523 : Reach 178523 := rs (se 1 (by rfl) ⟨133892, by rfl⟩) R267785
theorem R310007 : Reach 310007 := rs (se 1 (by rfl) ⟨232505, by rfl⟩) R465011
theorem R80711 : Reach 80711 := rs (se 1 (by rfl) ⟨60533, by rfl⟩) R121067
theorem R82127 : Reach 82127 := rs (se 1 (by rfl) ⟨61595, by rfl⟩) R123191
theorem R475469 : Reach 475469 := rs (se 3 (by rfl) ⟨89150, by rfl⟩) R178301
theorem R147851 : Reach 147851 := rs (se 1 (by rfl) ⟨110888, by rfl⟩) R221777
theorem R83015 : Reach 83015 := rs (se 1 (by rfl) ⟨62261, by rfl⟩) R124523
theorem R148807 : Reach 148807 := rs (se 1 (by rfl) ⟨111605, by rfl⟩) R223211
theorem R50743 : Reach 50743 := rs (se 1 (by rfl) ⟨38057, by rfl⟩) R76115
theorem R116407 : Reach 116407 := rs (se 1 (by rfl) ⟨87305, by rfl⟩) R174611
theorem R1427543 : Reach 1427543 := rs (se 1 (by rfl) ⟨1070657, by rfl⟩) R2141315
theorem R84059 : Reach 84059 := rs (se 1 (by rfl) ⟨63044, by rfl⟩) R126089
theorem R84095 : Reach 84095 := rs (se 1 (by rfl) ⟨63071, by rfl⟩) R126143
theorem R2017817 : Reach 2017817 := rs (se 2 (by rfl) ⟨756681, by rfl⟩) R1513363
theorem R84563 : Reach 84563 := rs (se 1 (by rfl) ⟨63422, by rfl⟩) R126845
theorem R85121 : Reach 85121 := rs (se 2 (by rfl) ⟨31920, by rfl⟩) R63841
theorem R52703 : Reach 52703 := rs (se 1 (by rfl) ⟨39527, by rfl⟩) R79055
theorem R52763 : Reach 52763 := rs (se 1 (by rfl) ⟨39572, by rfl⟩) R79145
theorem R53183 : Reach 53183 := rs (se 1 (by rfl) ⟨39887, by rfl⟩) R79775
theorem R53887 : Reach 53887 := rs (se 1 (by rfl) ⟨40415, by rfl⟩) R80831
theorem R86921 : Reach 86921 := rs (se 2 (by rfl) ⟨32595, by rfl⟩) R65191
theorem R119879 : Reach 119879 := rs (se 1 (by rfl) ⟨89909, by rfl⟩) R179819
theorem R87161 : Reach 87161 := rs (se 2 (by rfl) ⟨32685, by rfl⟩) R65371
theorem R54607 : Reach 54607 := rs (se 1 (by rfl) ⟨40955, by rfl⟩) R81911
theorem R87655 : Reach 87655 := rs (se 1 (by rfl) ⟨65741, by rfl⟩) R131483
theorem R87929 : Reach 87929 := rs (se 2 (by rfl) ⟨32973, by rfl⟩) R65947
theorem R120905 : Reach 120905 := rs (se 2 (by rfl) ⟨45339, by rfl⟩) R90679
theorem R120959 : Reach 120959 := rs (se 1 (by rfl) ⟨90719, by rfl⟩) R181439
theorem R940403 : Reach 940403 := rs (se 1 (by rfl) ⟨705302, by rfl⟩) R1410605
theorem R7428631 : Reach 7428631 := rs (se 1 (by rfl) ⟨5571473, by rfl⟩) R11142947
theorem R514835 : Reach 514835 := rs (se 1 (by rfl) ⟨386126, by rfl⟩) R772253
theorem R56105 : Reach 56105 := rs (se 2 (by rfl) ⟨21039, by rfl⟩) R42079
theorem R121661 : Reach 121661 := rs (se 3 (by rfl) ⟨22811, by rfl⟩) R45623
theorem R416573 : Reach 416573 := rs (se 3 (by rfl) ⟨78107, by rfl⟩) R156215
theorem R220319 : Reach 220319 := rs (se 1 (by rfl) ⟨165239, by rfl⟩) R330479
theorem R56639 : Reach 56639 := rs (se 1 (by rfl) ⟨42479, by rfl⟩) R84959
theorem R1105325 : Reach 1105325 := rs (se 3 (by rfl) ⟨207248, by rfl⟩) R414497
theorem R56969 : Reach 56969 := rs (se 2 (by rfl) ⟨21363, by rfl⟩) R42727
theorem R2088629 : Reach 2088629 := rs (se 5 (by rfl) ⟨97904, by rfl⟩) R195809
theorem R155945 : Reach 155945 := rs (se 2 (by rfl) ⟨58479, by rfl⟩) R116959
theorem R57671 : Reach 57671 := rs (se 1 (by rfl) ⟨43253, by rfl⟩) R86507
theorem R57755 : Reach 57755 := rs (se 1 (by rfl) ⟨43316, by rfl⟩) R86633
theorem R287225 : Reach 287225 := rs (se 2 (by rfl) ⟨107709, by rfl⟩) R215419
theorem R58175 : Reach 58175 := rs (se 1 (by rfl) ⟨43631, by rfl⟩) R87263
theorem R58463 : Reach 58463 := rs (se 1 (by rfl) ⟨43847, by rfl⟩) R87695
theorem R58523 : Reach 58523 := rs (se 1 (by rfl) ⟨43892, by rfl⟩) R87785
theorem R452299 : Reach 452299 := rs (se 1 (by rfl) ⟨339224, by rfl⟩) R678449
theorem R124793 : Reach 124793 := rs (se 2 (by rfl) ⟨46797, by rfl⟩) R93595
theorem R190511 : Reach 190511 := rs (se 1 (by rfl) ⟨142883, by rfl⟩) R285767
theorem R190673 : Reach 190673 := rs (se 2 (by rfl) ⟨71502, by rfl⟩) R143005
theorem R92603 : Reach 92603 := rs (se 1 (by rfl) ⟨69452, by rfl⟩) R138905
theorem R59879 : Reach 59879 := rs (se 1 (by rfl) ⟨44909, by rfl⟩) R89819
theorem R158183 : Reach 158183 := rs (se 1 (by rfl) ⟨118637, by rfl⟩) R237275
theorem R256699 : Reach 256699 := rs (se 1 (by rfl) ⟨192524, by rfl⟩) R385049
theorem R125819 : Reach 125819 := rs (se 1 (by rfl) ⟨94364, by rfl⟩) R188729
theorem R61033 : Reach 61033 := rs (se 2 (by rfl) ⟨22887, by rfl⟩) R45775
theorem R224927 : Reach 224927 := rs (se 1 (by rfl) ⟨168695, by rfl⟩) R337391
theorem R126791 : Reach 126791 := rs (se 1 (by rfl) ⟨95093, by rfl⟩) R190187
theorem R257879 : Reach 257879 := rs (se 1 (by rfl) ⟨193409, by rfl⟩) R386819
theorem R192863 : Reach 192863 := rs (se 1 (by rfl) ⟨144647, by rfl⟩) R289295
theorem R62279 : Reach 62279 := rs (se 1 (by rfl) ⟨46709, by rfl⟩) R93419
theorem R62329 : Reach 62329 := rs (se 2 (by rfl) ⟨23373, by rfl⟩) R46747
theorem R95215 : Reach 95215 := rs (se 1 (by rfl) ⟨71411, by rfl⟩) R142823
theorem R128033 : Reach 128033 := rs (se 2 (by rfl) ⟨48012, by rfl⟩) R96025
theorem R619649 : Reach 619649 := rs (se 2 (by rfl) ⟨232368, by rfl⟩) R464737
theorem R128735 : Reach 128735 := rs (se 1 (by rfl) ⟨96551, by rfl⟩) R193103
theorem R128897 : Reach 128897 := rs (se 2 (by rfl) ⟨48336, by rfl⟩) R96673
theorem R63551 : Reach 63551 := rs (se 1 (by rfl) ⟨47663, by rfl⟩) R95327
theorem R457325 : Reach 457325 := rs (se 3 (by rfl) ⟨85748, by rfl⟩) R171497
theorem R64327 : Reach 64327 := rs (se 1 (by rfl) ⟨48245, by rfl⟩) R96491
theorem R130139 : Reach 130139 := rs (se 1 (by rfl) ⟨97604, by rfl⟩) R195209
theorem R326753 : Reach 326753 := rs (se 2 (by rfl) ⟨122532, by rfl⟩) R245065
theorem R98131 : Reach 98131 := rs (se 1 (by rfl) ⟨73598, by rfl⟩) R147197
theorem R65407 : Reach 65407 := rs (se 1 (by rfl) ⟨49055, by rfl⟩) R98111
theorem R622525 : Reach 622525 := rs (se 3 (by rfl) ⟨116723, by rfl⟩) R233447
theorem R65515 : Reach 65515 := rs (se 1 (by rfl) ⟨49136, by rfl⟩) R98273
theorem R131327 : Reach 131327 := rs (se 1 (by rfl) ⟨98495, by rfl⟩) R196991
theorem R98567 : Reach 98567 := rs (se 1 (by rfl) ⟨73925, by rfl⟩) R147851
theorem R754721 : Reach 754721 := rs (se 2 (by rfl) ⟨283020, by rfl⟩) R566041
theorem R951695 : Reach 951695 := rs (se 1 (by rfl) ⟨713771, by rfl⟩) R1427543
theorem R1345211 : Reach 1345211 := rs (se 1 (by rfl) ⟨1008908, by rfl⟩) R2017817
theorem R198409 : Reach 198409 := rs (se 2 (by rfl) ⟨74403, by rfl⟩) R148807
theorem R67657 : Reach 67657 := rs (se 2 (by rfl) ⟨25371, by rfl⟩) R50743
theorem R35135 : Reach 35135 := rs (se 1 (by rfl) ⟨26351, by rfl⟩) R52703
theorem R35175 : Reach 35175 := rs (se 1 (by rfl) ⟨26381, by rfl⟩) R52763
theorem R35455 : Reach 35455 := rs (se 1 (by rfl) ⟨26591, by rfl⟩) R53183
theorem R69407 : Reach 69407 := rs (se 1 (by rfl) ⟨52055, by rfl⟩) R104111
theorem R626935 : Reach 626935 := rs (se 1 (by rfl) ⟨470201, by rfl⟩) R940403
theorem R37403 : Reach 37403 := rs (se 1 (by rfl) ⟨28052, by rfl⟩) R56105
theorem R37759 : Reach 37759 := rs (se 1 (by rfl) ⟨28319, by rfl⟩) R56639
theorem R37979 : Reach 37979 := rs (se 1 (by rfl) ⟨28484, by rfl⟩) R56969
theorem R103963 : Reach 103963 := rs (se 1 (by rfl) ⟨77972, by rfl⟩) R155945
theorem R38447 : Reach 38447 := rs (se 1 (by rfl) ⟨28835, by rfl⟩) R57671
theorem R38503 : Reach 38503 := rs (se 1 (by rfl) ⟨28877, by rfl⟩) R57755
theorem R136991 : Reach 136991 := rs (se 1 (by rfl) ⟨102743, by rfl⟩) R205487
theorem R38783 : Reach 38783 := rs (se 1 (by rfl) ⟨29087, by rfl⟩) R58175
theorem R38975 : Reach 38975 := rs (se 1 (by rfl) ⟨29231, by rfl⟩) R58463
theorem R39015 : Reach 39015 := rs (se 1 (by rfl) ⟨29261, by rfl⟩) R58523
theorem R71849 : Reach 71849 := rs (se 2 (by rfl) ⟨26943, by rfl⟩) R53887
theorem R137659 : Reach 137659 := rs (se 1 (by rfl) ⟨103244, by rfl⟩) R206489
theorem R39919 : Reach 39919 := rs (se 1 (by rfl) ⟨29939, by rfl⟩) R59879
theorem R105455 : Reach 105455 := rs (se 1 (by rfl) ⟨79091, by rfl⟩) R158183
theorem R72809 : Reach 72809 := rs (se 2 (by rfl) ⟨27303, by rfl⟩) R54607
theorem R171919 : Reach 171919 := rs (se 1 (by rfl) ⟨128939, by rfl⟩) R257879
theorem R467471 : Reach 467471 := rs (se 1 (by rfl) ⟨350603, by rfl⟩) R701207
theorem R41519 : Reach 41519 := rs (se 1 (by rfl) ⟨31139, by rfl⟩) R62279
theorem R9904841 : Reach 9904841 := rs (se 2 (by rfl) ⟨3714315, by rfl⟩) R7428631
theorem R205739 : Reach 205739 := rs (se 1 (by rfl) ⟨154304, by rfl⟩) R308609
theorem R42367 : Reach 42367 := rs (se 1 (by rfl) ⟨31775, by rfl⟩) R63551
theorem R665225 : Reach 665225 := rs (se 2 (by rfl) ⟨249459, by rfl⟩) R498919
theorem R304883 : Reach 304883 := rs (se 1 (by rfl) ⟨228662, by rfl⟩) R457325
theorem R206671 : Reach 206671 := rs (se 1 (by rfl) ⟨155003, by rfl⟩) R310007
theorem R141821 : Reach 141821 := rs (se 3 (by rfl) ⟨26591, by rfl⟩) R53183
theorem R830033 : Reach 830033 := rs (se 2 (by rfl) ⟨311262, by rfl⟩) R622525
theorem R240479 : Reach 240479 := rs (se 1 (by rfl) ⟨180359, by rfl⟩) R360719
theorem R44479 : Reach 44479 := rs (se 1 (by rfl) ⟨33359, by rfl⟩) R66719
theorem R929717 : Reach 929717 := rs (se 5 (by rfl) ⟨43580, by rfl⟩) R87161
theorem R45787 : Reach 45787 := rs (se 1 (by rfl) ⟨34340, by rfl⟩) R68681
theorem R45947 : Reach 45947 := rs (se 1 (by rfl) ⟨34460, by rfl⟩) R68921
theorem R603065 : Reach 603065 := rs (se 2 (by rfl) ⟨226149, by rfl⟩) R452299
theorem R112079 : Reach 112079 := rs (se 1 (by rfl) ⟨84059, by rfl⟩) R168119
theorem R46919 : Reach 46919 := rs (se 1 (by rfl) ⟨35189, by rfl⟩) R70379
theorem R46975 : Reach 46975 := rs (se 1 (by rfl) ⟨35231, by rfl⟩) R70463
theorem R47081 : Reach 47081 := rs (se 2 (by rfl) ⟨17655, by rfl⟩) R35311
theorem R79919 : Reach 79919 := rs (se 1 (by rfl) ⟨59939, by rfl⟩) R119879
theorem R374867 : Reach 374867 := rs (se 1 (by rfl) ⟨281150, by rfl⟩) R562301
theorem R112859 : Reach 112859 := rs (se 1 (by rfl) ⟨84644, by rfl⟩) R169289
theorem R342265 : Reach 342265 := rs (se 2 (by rfl) ⟨128349, by rfl⟩) R256699
theorem R1587761 : Reach 1587761 := rs (se 2 (by rfl) ⟨595410, by rfl⟩) R1190821
theorem R47719 : Reach 47719 := rs (se 1 (by rfl) ⟨35789, by rfl⟩) R71579
theorem R80603 : Reach 80603 := rs (se 1 (by rfl) ⟨60452, by rfl⟩) R120905
theorem R80639 : Reach 80639 := rs (se 1 (by rfl) ⟨60479, by rfl⟩) R120959
theorem R343223 : Reach 343223 := rs (se 1 (by rfl) ⟨257417, by rfl⟩) R514835
theorem R81107 : Reach 81107 := rs (se 1 (by rfl) ⟨60830, by rfl⟩) R121661
theorem R277715 : Reach 277715 := rs (se 1 (by rfl) ⟨208286, by rfl⟩) R416573
theorem R146879 : Reach 146879 := rs (se 1 (by rfl) ⟨110159, by rfl⟩) R220319
theorem R81377 : Reach 81377 := rs (se 2 (by rfl) ⟨30516, by rfl⟩) R61033
theorem R736883 : Reach 736883 := rs (se 1 (by rfl) ⟨552662, by rfl⟩) R1105325
theorem R1392419 : Reach 1392419 := rs (se 1 (by rfl) ⟨1044314, by rfl⟩) R2088629
theorem R246071 : Reach 246071 := rs (se 1 (by rfl) ⟨184553, by rfl⟩) R369107
theorem R115627 : Reach 115627 := rs (se 1 (by rfl) ⟨86720, by rfl⟩) R173441
theorem R50267 : Reach 50267 := rs (se 1 (by rfl) ⟨37700, by rfl⟩) R75401
theorem R83105 : Reach 83105 := rs (se 2 (by rfl) ⟨31164, by rfl⟩) R62329
theorem R83195 : Reach 83195 := rs (se 1 (by rfl) ⟨62396, by rfl⟩) R124793
theorem R280189 : Reach 280189 := rs (se 3 (by rfl) ⟨52535, by rfl⟩) R105071
theorem R83879 : Reach 83879 := rs (se 1 (by rfl) ⟨62909, by rfl⟩) R125819
theorem R182249 : Reach 182249 := rs (se 2 (by rfl) ⟨68343, by rfl⟩) R136687
theorem R116873 : Reach 116873 := rs (se 2 (by rfl) ⟨43827, by rfl⟩) R87655
theorem R182569 : Reach 182569 := rs (se 2 (by rfl) ⟨68463, by rfl⟩) R136927
theorem R182683 : Reach 182683 := rs (se 1 (by rfl) ⟨137012, by rfl⟩) R274025
theorem R149951 : Reach 149951 := rs (se 1 (by rfl) ⟨112463, by rfl⟩) R224927
theorem R182735 : Reach 182735 := rs (se 1 (by rfl) ⟨137051, by rfl⟩) R274103
theorem R117227 : Reach 117227 := rs (se 1 (by rfl) ⟨87920, by rfl⟩) R175841
theorem R84527 : Reach 84527 := rs (se 1 (by rfl) ⟨63395, by rfl⟩) R126791
theorem R1362743 : Reach 1362743 := rs (se 1 (by rfl) ⟨1022057, by rfl⟩) R2044115
theorem R85355 : Reach 85355 := rs (se 1 (by rfl) ⟨64016, by rfl⟩) R128033
theorem R413099 : Reach 413099 := rs (se 1 (by rfl) ⟨309824, by rfl⟩) R619649
theorem R52991 : Reach 52991 := rs (se 1 (by rfl) ⟨39743, by rfl⟩) R79487
theorem R85769 : Reach 85769 := rs (se 2 (by rfl) ⟨32163, by rfl⟩) R64327
theorem R85823 : Reach 85823 := rs (se 1 (by rfl) ⟨64367, by rfl⟩) R128735
theorem R85931 : Reach 85931 := rs (se 1 (by rfl) ⟨64448, by rfl⟩) R128897
theorem R53339 : Reach 53339 := rs (se 1 (by rfl) ⟨40004, by rfl⟩) R80009
theorem R315521 : Reach 315521 := rs (se 2 (by rfl) ⟨118320, by rfl⟩) R236641
theorem R119015 : Reach 119015 := rs (se 1 (by rfl) ⟨89261, by rfl⟩) R178523
theorem R53801 : Reach 53801 := rs (se 2 (by rfl) ⟨20175, by rfl⟩) R40351
theorem R53807 : Reach 53807 := rs (se 1 (by rfl) ⟨40355, by rfl⟩) R80711
theorem R86759 : Reach 86759 := rs (se 1 (by rfl) ⟨65069, by rfl⟩) R130139
theorem R53993 : Reach 53993 := rs (se 2 (by rfl) ⟨20247, by rfl⟩) R40495
theorem R217835 : Reach 217835 := rs (se 1 (by rfl) ⟨163376, by rfl⟩) R326753
theorem R87209 : Reach 87209 := rs (se 2 (by rfl) ⟨32703, by rfl⟩) R65407
theorem R87353 : Reach 87353 := rs (se 2 (by rfl) ⟨32757, by rfl⟩) R65515
theorem R54751 : Reach 54751 := rs (se 1 (by rfl) ⟨41063, by rfl⟩) R82127
theorem R316979 : Reach 316979 := rs (se 1 (by rfl) ⟨237734, by rfl⟩) R475469
theorem R55343 : Reach 55343 := rs (se 1 (by rfl) ⟨41507, by rfl⟩) R83015
theorem R481751 : Reach 481751 := rs (se 1 (by rfl) ⟨361313, by rfl⟩) R722627
theorem R56039 : Reach 56039 := rs (se 1 (by rfl) ⟨42029, by rfl⟩) R84059
theorem R56063 : Reach 56063 := rs (se 1 (by rfl) ⟨42047, by rfl⟩) R84095
theorem R187433 : Reach 187433 := rs (se 2 (by rfl) ⟨70287, by rfl⟩) R140575
theorem R56375 : Reach 56375 := rs (se 1 (by rfl) ⟨42281, by rfl⟩) R84563
theorem R56747 : Reach 56747 := rs (se 1 (by rfl) ⟨42560, by rfl⟩) R85121
theorem R155209 : Reach 155209 := rs (se 2 (by rfl) ⟨58203, by rfl⟩) R116407
theorem R57947 : Reach 57947 := rs (se 1 (by rfl) ⟨43460, by rfl⟩) R86921
theorem R91003 : Reach 91003 := rs (se 1 (by rfl) ⟨68252, by rfl⟩) R136505
theorem R58619 : Reach 58619 := rs (se 1 (by rfl) ⟨43964, by rfl⟩) R87929
theorem R91631 : Reach 91631 := rs (se 1 (by rfl) ⟨68723, by rfl⟩) R137447
theorem R190025 : Reach 190025 := rs (se 2 (by rfl) ⟨71259, by rfl⟩) R142519
theorem R289079 : Reach 289079 := rs (se 1 (by rfl) ⟨216809, by rfl⟩) R433619
theorem R191483 : Reach 191483 := rs (se 1 (by rfl) ⟨143612, by rfl⟩) R287225
theorem R191645 : Reach 191645 := rs (se 3 (by rfl) ⟨35933, by rfl⟩) R71867
theorem R191969 : Reach 191969 := rs (se 2 (by rfl) ⟨71988, by rfl⟩) R143977
theorem R126953 : Reach 126953 := rs (se 2 (by rfl) ⟨47607, by rfl⟩) R95215
theorem R127007 : Reach 127007 := rs (se 1 (by rfl) ⟨95255, by rfl⟩) R190511
theorem R127115 : Reach 127115 := rs (se 1 (by rfl) ⟨95336, by rfl⟩) R190673
theorem R61735 : Reach 61735 := rs (se 1 (by rfl) ⟨46301, by rfl⟩) R92603
theorem R488591 : Reach 488591 := rs (se 1 (by rfl) ⟨366443, by rfl⟩) R732887
theorem R128575 : Reach 128575 := rs (se 1 (by rfl) ⟨96431, by rfl⟩) R192863
theorem R161959 : Reach 161959 := rs (se 1 (by rfl) ⟨121469, by rfl⟩) R242939
theorem R621107 : Reach 621107 := rs (se 1 (by rfl) ⟨465830, by rfl⟩) R931661
theorem R130841 : Reach 130841 := rs (se 2 (by rfl) ⟨49065, by rfl⟩) R98131
theorem R65711 : Reach 65711 := rs (se 1 (by rfl) ⟨49283, by rfl⟩) R98567
theorem R164047 : Reach 164047 := rs (se 1 (by rfl) ⟨123035, by rfl⟩) R246071
theorem R99967 : Reach 99967 := rs (se 1 (by rfl) ⟨74975, by rfl⟩) R149951
theorem R264545 : Reach 264545 := rs (se 2 (by rfl) ⟨99204, by rfl⟩) R198409
theorem R35327 : Reach 35327 := rs (se 1 (by rfl) ⟨26495, by rfl⟩) R52991
theorem R35559 : Reach 35559 := rs (se 1 (by rfl) ⟨26669, by rfl⟩) R53339
theorem R134045 : Reach 134045 := rs (se 3 (by rfl) ⟨25133, by rfl⟩) R50267
theorem R35867 : Reach 35867 := rs (se 1 (by rfl) ⟨26900, by rfl⟩) R53801
theorem R35871 : Reach 35871 := rs (se 1 (by rfl) ⟨26903, by rfl⟩) R53807
theorem R35995 : Reach 35995 := rs (se 1 (by rfl) ⟨26996, by rfl⟩) R53993
theorem R36895 : Reach 36895 := rs (se 1 (by rfl) ⟨27671, by rfl⟩) R55343
theorem R37359 : Reach 37359 := rs (se 1 (by rfl) ⟨28019, by rfl⟩) R56039
theorem R37375 : Reach 37375 := rs (se 1 (by rfl) ⟨28031, by rfl⟩) R56063
theorem R70303 : Reach 70303 := rs (se 1 (by rfl) ⟨52727, by rfl⟩) R105455
theorem R37583 : Reach 37583 := rs (se 1 (by rfl) ⟨28187, by rfl⟩) R56375
theorem R37831 : Reach 37831 := rs (se 1 (by rfl) ⟨28373, by rfl⟩) R56747
theorem R38631 : Reach 38631 := rs (se 1 (by rfl) ⟨28973, by rfl⟩) R57947
theorem R137159 : Reach 137159 := rs (se 1 (by rfl) ⟨102869, by rfl⟩) R205739
theorem R39079 : Reach 39079 := rs (se 1 (by rfl) ⟨29309, by rfl⟩) R58619
theorem R203255 : Reach 203255 := rs (se 1 (by rfl) ⟨152441, by rfl⟩) R304883
theorem R73001 : Reach 73001 := rs (se 2 (by rfl) ⟨27375, by rfl⟩) R54751
theorem R138617 : Reach 138617 := rs (se 2 (by rfl) ⟨51981, by rfl⟩) R103963
theorem R171433 : Reach 171433 := rs (se 2 (by rfl) ⟨64287, by rfl⟩) R128575
theorem R402043 : Reach 402043 := rs (se 1 (by rfl) ⟨301532, by rfl⟩) R603065
theorem R74719 : Reach 74719 := rs (se 1 (by rfl) ⟨56039, by rfl⟩) R112079
theorem R75239 : Reach 75239 := rs (se 1 (by rfl) ⟨56429, by rfl⟩) R112859
theorem R1058507 : Reach 1058507 := rs (se 1 (by rfl) ⟨793880, by rfl⟩) R1587761
theorem R206945 : Reach 206945 := rs (se 2 (by rfl) ⟨77604, by rfl⟩) R155209
theorem R928279 : Reach 928279 := rs (se 1 (by rfl) ⟨696209, by rfl⟩) R1392419
theorem R503147 : Reach 503147 := rs (se 1 (by rfl) ⟨377360, by rfl⟩) R754721
theorem R634463 : Reach 634463 := rs (se 1 (by rfl) ⟨475847, by rfl⟩) R951695
theorem R896807 : Reach 896807 := rs (se 1 (by rfl) ⟨672605, by rfl⟩) R1345211
theorem R77915 : Reach 77915 := rs (se 1 (by rfl) ⟨58436, by rfl⟩) R116873
theorem R110717 : Reach 110717 := rs (se 3 (by rfl) ⟨20759, by rfl⟩) R41519
theorem R373585 : Reach 373585 := rs (se 2 (by rfl) ⟨140094, by rfl⟩) R280189
theorem R275399 : Reach 275399 := rs (se 1 (by rfl) ⟨206549, by rfl⟩) R413099
theorem R275561 : Reach 275561 := rs (se 2 (by rfl) ⟨103335, by rfl⟩) R206671
theorem R46271 : Reach 46271 := rs (se 1 (by rfl) ⟨34703, by rfl⟩) R69407
theorem R210347 : Reach 210347 := rs (se 1 (by rfl) ⟨157760, by rfl⟩) R315521
theorem R79343 : Reach 79343 := rs (se 1 (by rfl) ⟨59507, by rfl⟩) R119015
theorem R243425 : Reach 243425 := rs (se 2 (by rfl) ⟨91284, by rfl⟩) R182569
theorem R145223 : Reach 145223 := rs (se 1 (by rfl) ⟨108917, by rfl⟩) R217835
theorem R243577 : Reach 243577 := rs (se 2 (by rfl) ⟨91341, by rfl⟩) R182683
theorem R211319 : Reach 211319 := rs (se 1 (by rfl) ⟨158489, by rfl⟩) R316979
theorem R47899 : Reach 47899 := rs (se 1 (by rfl) ⟨35924, by rfl⟩) R71849
theorem R48539 : Reach 48539 := rs (se 1 (by rfl) ⟨36404, by rfl⟩) R72809
theorem R835913 : Reach 835913 := rs (se 2 (by rfl) ⟨313467, by rfl⟩) R626935
theorem R311647 : Reach 311647 := rs (se 1 (by rfl) ⟨233735, by rfl⟩) R467471
theorem R82313 : Reach 82313 := rs (se 2 (by rfl) ⟨30867, by rfl⟩) R61735
theorem R6603227 : Reach 6603227 := rs (se 1 (by rfl) ⟨4952420, by rfl⟩) R9904841
theorem R443483 : Reach 443483 := rs (se 1 (by rfl) ⟨332612, by rfl⟩) R665225
theorem R312605 : Reach 312605 := rs (se 3 (by rfl) ⟨58613, by rfl⟩) R117227
theorem R84635 : Reach 84635 := rs (se 1 (by rfl) ⟨63476, by rfl⟩) R126953
theorem R84671 : Reach 84671 := rs (se 1 (by rfl) ⟨63503, by rfl⟩) R127007
theorem R84743 : Reach 84743 := rs (se 1 (by rfl) ⟨63557, by rfl⟩) R127115
theorem R215945 : Reach 215945 := rs (se 2 (by rfl) ⟨80979, by rfl⟩) R161959
theorem R740573 : Reach 740573 := rs (se 3 (by rfl) ⟨138857, by rfl⟩) R277715
theorem R183545 : Reach 183545 := rs (se 2 (by rfl) ⟨68829, by rfl⟩) R137659
theorem R53225 : Reach 53225 := rs (se 2 (by rfl) ⟨19959, by rfl⟩) R39919
theorem R53279 : Reach 53279 := rs (se 1 (by rfl) ⟨39959, by rfl⟩) R79919
theorem R249911 : Reach 249911 := rs (se 1 (by rfl) ⟨187433, by rfl⟩) R374867
theorem R414071 : Reach 414071 := rs (se 1 (by rfl) ⟨310553, by rfl⟩) R621107
theorem R53735 : Reach 53735 := rs (se 1 (by rfl) ⟨40301, by rfl⟩) R80603
theorem R53759 : Reach 53759 := rs (se 1 (by rfl) ⟨40319, by rfl⟩) R80639
theorem R54071 : Reach 54071 := rs (se 1 (by rfl) ⟨40553, by rfl⟩) R81107
theorem R54251 : Reach 54251 := rs (se 1 (by rfl) ⟨40688, by rfl⟩) R81377
theorem R87227 : Reach 87227 := rs (se 1 (by rfl) ⟨65420, by rfl⟩) R130841
theorem R87551 : Reach 87551 := rs (se 1 (by rfl) ⟨65663, by rfl⟩) R131327
theorem R55403 : Reach 55403 := rs (se 1 (by rfl) ⟨41552, by rfl⟩) R83105
theorem R55463 : Reach 55463 := rs (se 1 (by rfl) ⟨41597, by rfl⟩) R83195
theorem R121337 : Reach 121337 := rs (se 2 (by rfl) ⟨45501, by rfl⟩) R91003
theorem R154169 : Reach 154169 := rs (se 2 (by rfl) ⟨57813, by rfl⟩) R115627
theorem R55919 : Reach 55919 := rs (se 1 (by rfl) ⟨41939, by rfl⟩) R83879
theorem R121499 : Reach 121499 := rs (se 1 (by rfl) ⟨91124, by rfl⟩) R182249
theorem R121823 : Reach 121823 := rs (se 1 (by rfl) ⟨91367, by rfl⟩) R182735
theorem R56351 : Reach 56351 := rs (se 1 (by rfl) ⟨42263, by rfl⟩) R84527
theorem R56489 : Reach 56489 := rs (se 2 (by rfl) ⟨21183, by rfl⟩) R42367
theorem R908495 : Reach 908495 := rs (se 1 (by rfl) ⟨681371, by rfl⟩) R1362743
theorem R56903 : Reach 56903 := rs (se 1 (by rfl) ⟨42677, by rfl⟩) R85355
theorem R122525 : Reach 122525 := rs (se 3 (by rfl) ⟨22973, by rfl⟩) R45947
theorem R57179 : Reach 57179 := rs (se 1 (by rfl) ⟨42884, by rfl⟩) R85769
theorem R57215 : Reach 57215 := rs (se 1 (by rfl) ⟨42911, by rfl⟩) R85823
theorem R57287 : Reach 57287 := rs (se 1 (by rfl) ⟨42965, by rfl⟩) R85931
theorem R90209 : Reach 90209 := rs (se 2 (by rfl) ⟨33828, by rfl⟩) R67657
theorem R57839 : Reach 57839 := rs (se 1 (by rfl) ⟨43379, by rfl⟩) R86759
theorem R58139 : Reach 58139 := rs (se 1 (by rfl) ⟨43604, by rfl⟩) R87209
theorem R58235 : Reach 58235 := rs (se 1 (by rfl) ⟨43676, by rfl⟩) R87353
theorem R91327 : Reach 91327 := rs (se 1 (by rfl) ⟨68495, by rfl⟩) R136991
theorem R321167 : Reach 321167 := rs (se 1 (by rfl) ⟨240875, by rfl⟩) R481751
theorem R59305 : Reach 59305 := rs (se 2 (by rfl) ⟨22239, by rfl⟩) R44479
theorem R124955 : Reach 124955 := rs (se 1 (by rfl) ⟨93716, by rfl⟩) R187433
theorem R125117 : Reach 125117 := rs (se 3 (by rfl) ⟨23459, by rfl⟩) R46919
theorem R125549 : Reach 125549 := rs (se 3 (by rfl) ⟨23540, by rfl⟩) R47081
theorem R61049 : Reach 61049 := rs (se 2 (by rfl) ⟨22893, by rfl⟩) R45787
theorem R61087 : Reach 61087 := rs (se 1 (by rfl) ⟨45815, by rfl⟩) R91631
theorem R126683 : Reach 126683 := rs (se 1 (by rfl) ⟨95012, by rfl⟩) R190025
theorem R192719 : Reach 192719 := rs (se 1 (by rfl) ⟨144539, by rfl⟩) R289079
theorem R94547 : Reach 94547 := rs (se 1 (by rfl) ⟨70910, by rfl⟩) R141821
theorem R553355 : Reach 553355 := rs (se 1 (by rfl) ⟨415016, by rfl⟩) R830033
theorem R160319 : Reach 160319 := rs (se 1 (by rfl) ⟨120239, by rfl⟩) R240479
theorem R127655 : Reach 127655 := rs (se 1 (by rfl) ⟨95741, by rfl⟩) R191483
theorem R127763 : Reach 127763 := rs (se 1 (by rfl) ⟨95822, by rfl⟩) R191645
theorem R127979 : Reach 127979 := rs (se 1 (by rfl) ⟨95984, by rfl⟩) R191969
theorem R62633 : Reach 62633 := rs (se 2 (by rfl) ⟨23487, by rfl⟩) R46975
theorem R619811 : Reach 619811 := rs (se 1 (by rfl) ⟨464858, by rfl⟩) R929717
theorem R456353 : Reach 456353 := rs (se 2 (by rfl) ⟨171132, by rfl⟩) R342265
theorem R325727 : Reach 325727 := rs (se 1 (by rfl) ⟨244295, by rfl⟩) R488591
theorem R63625 : Reach 63625 := rs (se 2 (by rfl) ⟨23859, by rfl⟩) R47719
theorem R228815 : Reach 228815 := rs (se 1 (by rfl) ⟨171611, by rfl⟩) R343223
theorem R97919 : Reach 97919 := rs (se 1 (by rfl) ⟨73439, by rfl⟩) R146879
theorem R491255 : Reach 491255 := rs (se 1 (by rfl) ⟨368441, by rfl⟩) R736883
theorem R229225 : Reach 229225 := rs (se 2 (by rfl) ⟨85959, by rfl⟩) R171919
theorem R557275 : Reach 557275 := rs (se 1 (by rfl) ⟨417956, by rfl⟩) R835913
theorem R295655 : Reach 295655 := rs (se 1 (by rfl) ⟨221741, by rfl⟩) R443483
theorem R99625 : Reach 99625 := rs (se 2 (by rfl) ⟨37359, by rfl⟩) R74719
theorem R493715 : Reach 493715 := rs (se 1 (by rfl) ⟨370286, by rfl⟩) R740573
theorem R133289 : Reach 133289 := rs (se 2 (by rfl) ⟨49983, by rfl⟩) R99967
theorem R35483 : Reach 35483 := rs (se 1 (by rfl) ⟨26612, by rfl⟩) R53225
theorem R35519 : Reach 35519 := rs (se 1 (by rfl) ⟨26639, by rfl⟩) R53279
theorem R166607 : Reach 166607 := rs (se 1 (by rfl) ⟨124955, by rfl⟩) R249911
theorem R4950821 : Reach 4950821 := rs (se 4 (by rfl) ⟨464139, by rfl⟩) R928279
theorem R35823 : Reach 35823 := rs (se 1 (by rfl) ⟨26867, by rfl⟩) R53735
theorem R35839 : Reach 35839 := rs (se 1 (by rfl) ⟨26879, by rfl⟩) R53759
theorem R36047 : Reach 36047 := rs (se 1 (by rfl) ⟨27035, by rfl⟩) R54071
theorem R36167 : Reach 36167 := rs (se 1 (by rfl) ⟨27125, by rfl⟩) R54251
theorem R36935 : Reach 36935 := rs (se 1 (by rfl) ⟨27701, by rfl⟩) R55403
theorem R36975 : Reach 36975 := rs (se 1 (by rfl) ⟨27731, by rfl⟩) R55463
theorem R135503 : Reach 135503 := rs (se 1 (by rfl) ⟨101627, by rfl⟩) R203255
theorem R102779 : Reach 102779 := rs (se 1 (by rfl) ⟨77084, by rfl⟩) R154169
theorem R37279 : Reach 37279 := rs (se 1 (by rfl) ⟨27959, by rfl⟩) R55919
theorem R37567 : Reach 37567 := rs (se 1 (by rfl) ⟨28175, by rfl⟩) R56351
theorem R37659 : Reach 37659 := rs (se 1 (by rfl) ⟨28244, by rfl⟩) R56489
theorem R37935 : Reach 37935 := rs (se 1 (by rfl) ⟨28451, by rfl⟩) R56903
theorem R38119 : Reach 38119 := rs (se 1 (by rfl) ⟨28589, by rfl⟩) R57179
theorem R38143 : Reach 38143 := rs (se 1 (by rfl) ⟨28607, by rfl⟩) R57215
theorem R38191 : Reach 38191 := rs (se 1 (by rfl) ⟨28643, by rfl⟩) R57287
theorem R38559 : Reach 38559 := rs (se 1 (by rfl) ⟨28919, by rfl⟩) R57839
theorem R38759 : Reach 38759 := rs (se 1 (by rfl) ⟨29069, by rfl⟩) R58139
theorem R38823 : Reach 38823 := rs (se 1 (by rfl) ⟨29117, by rfl⟩) R58235
theorem R498113 : Reach 498113 := rs (se 2 (by rfl) ⟨186792, by rfl⟩) R373585
theorem R137963 : Reach 137963 := rs (se 1 (by rfl) ⟨103472, by rfl⟩) R206945
theorem R335431 : Reach 335431 := rs (se 1 (by rfl) ⟨251573, by rfl⟩) R503147
theorem R40699 : Reach 40699 := rs (se 1 (by rfl) ⟨30524, by rfl⟩) R61049
theorem R597871 : Reach 597871 := rs (se 1 (by rfl) ⟨448403, by rfl⟩) R896807
theorem R73811 : Reach 73811 := rs (se 1 (by rfl) ⟨55358, by rfl⟩) R110717
theorem R368903 : Reach 368903 := rs (se 1 (by rfl) ⟨276677, by rfl⟩) R553355
theorem R106879 : Reach 106879 := rs (se 1 (by rfl) ⟨80159, by rfl⟩) R160319
theorem R41755 : Reach 41755 := rs (se 1 (by rfl) ⟨31316, by rfl⟩) R62633
theorem R140231 : Reach 140231 := rs (se 1 (by rfl) ⟨105173, by rfl⟩) R210347
theorem R304235 : Reach 304235 := rs (se 1 (by rfl) ⟨228176, by rfl⟩) R456353
theorem R140879 : Reach 140879 := rs (se 1 (by rfl) ⟨105659, by rfl⟩) R211319
theorem R305633 : Reach 305633 := rs (se 2 (by rfl) ⟨114612, by rfl⟩) R229225
theorem R43807 : Reach 43807 := rs (se 1 (by rfl) ⟨32855, by rfl⟩) R65711
theorem R4402151 : Reach 4402151 := rs (se 1 (by rfl) ⟨3301613, by rfl⟩) R6603227
theorem R536057 : Reach 536057 := rs (se 2 (by rfl) ⟨201021, by rfl⟩) R402043
theorem R208403 : Reach 208403 := rs (se 1 (by rfl) ⟨156302, by rfl⟩) R312605
theorem R176363 : Reach 176363 := rs (se 1 (by rfl) ⟨132272, by rfl⟩) R264545
theorem R143963 : Reach 143963 := rs (se 1 (by rfl) ⟨107972, by rfl⟩) R215945
theorem R79073 : Reach 79073 := rs (se 2 (by rfl) ⟨29652, by rfl⟩) R59305
theorem R276047 : Reach 276047 := rs (se 1 (by rfl) ⟨207035, by rfl⟩) R414071
theorem R80891 : Reach 80891 := rs (se 1 (by rfl) ⟨60668, by rfl⟩) R121337
theorem R80999 : Reach 80999 := rs (se 1 (by rfl) ⟨60749, by rfl⟩) R121499
theorem R81215 : Reach 81215 := rs (se 1 (by rfl) ⟨60911, by rfl⟩) R121823
theorem R605663 : Reach 605663 := rs (se 1 (by rfl) ⟨454247, by rfl⟩) R908495
theorem R48667 : Reach 48667 := rs (se 1 (by rfl) ⟨36500, by rfl⟩) R73001
theorem R81449 : Reach 81449 := rs (se 2 (by rfl) ⟨30543, by rfl⟩) R61087
theorem R81683 : Reach 81683 := rs (se 1 (by rfl) ⟨61262, by rfl⟩) R122525
theorem R50159 : Reach 50159 := rs (se 1 (by rfl) ⟨37619, by rfl⟩) R75239
theorem R214111 : Reach 214111 := rs (se 1 (by rfl) ⟨160583, by rfl⟩) R321167
theorem R705671 : Reach 705671 := rs (se 1 (by rfl) ⟨529253, by rfl⟩) R1058507
theorem R83303 : Reach 83303 := rs (se 1 (by rfl) ⟨62477, by rfl⟩) R124955
theorem R83411 : Reach 83411 := rs (se 1 (by rfl) ⟨62558, by rfl⟩) R125117
theorem R83699 : Reach 83699 := rs (se 1 (by rfl) ⟨62774, by rfl⟩) R125549
theorem R84455 : Reach 84455 := rs (se 1 (by rfl) ⟨63341, by rfl⟩) R126683
theorem R51943 : Reach 51943 := rs (se 1 (by rfl) ⟨38957, by rfl⟩) R77915
theorem R84833 : Reach 84833 := rs (se 2 (by rfl) ⟨31812, by rfl⟩) R63625
theorem R85103 : Reach 85103 := rs (se 1 (by rfl) ⟨63827, by rfl⟩) R127655
theorem R85175 : Reach 85175 := rs (se 1 (by rfl) ⟨63881, by rfl⟩) R127763
theorem R183599 : Reach 183599 := rs (se 1 (by rfl) ⟨137699, by rfl⟩) R275399
theorem R85319 : Reach 85319 := rs (se 1 (by rfl) ⟨63989, by rfl⟩) R127979
theorem R183707 : Reach 183707 := rs (se 1 (by rfl) ⟨137780, by rfl⟩) R275561
theorem R413207 : Reach 413207 := rs (se 1 (by rfl) ⟨309905, by rfl⟩) R619811
theorem R52895 : Reach 52895 := rs (se 1 (by rfl) ⟨39671, by rfl⟩) R79343
theorem R217151 : Reach 217151 := rs (se 1 (by rfl) ⟨162863, by rfl⟩) R325727
theorem R152543 : Reach 152543 := rs (se 1 (by rfl) ⟨114407, by rfl⟩) R228815
theorem R54875 : Reach 54875 := rs (se 1 (by rfl) ⟨41156, by rfl⟩) R82313
theorem R218729 : Reach 218729 := rs (se 2 (by rfl) ⟨82023, by rfl⟩) R164047
theorem R415529 : Reach 415529 := rs (se 2 (by rfl) ⟨155823, by rfl⟩) R311647
theorem R121769 : Reach 121769 := rs (se 2 (by rfl) ⟨45663, by rfl⟩) R91327
theorem R56423 : Reach 56423 := rs (se 1 (by rfl) ⟨42317, by rfl⟩) R84635
theorem R56447 : Reach 56447 := rs (se 1 (by rfl) ⟨42335, by rfl⟩) R84671
theorem R56495 : Reach 56495 := rs (se 1 (by rfl) ⟨42371, by rfl⟩) R84743
theorem R89363 : Reach 89363 := rs (se 1 (by rfl) ⟨67022, by rfl⟩) R134045
theorem R122363 : Reach 122363 := rs (se 1 (by rfl) ⟨91772, by rfl⟩) R183545
theorem R123389 : Reach 123389 := rs (se 3 (by rfl) ⟨23135, by rfl⟩) R46271
theorem R58151 : Reach 58151 := rs (se 1 (by rfl) ⟨43613, by rfl⟩) R87227
theorem R58367 : Reach 58367 := rs (se 1 (by rfl) ⟨43775, by rfl⟩) R87551
theorem R91439 : Reach 91439 := rs (se 1 (by rfl) ⟨68579, by rfl⟩) R137159
theorem R92411 : Reach 92411 := rs (se 1 (by rfl) ⟨69308, by rfl⟩) R138617
theorem R60139 : Reach 60139 := rs (se 1 (by rfl) ⟨45104, by rfl⟩) R90209
theorem R93737 : Reach 93737 := rs (se 2 (by rfl) ⟨35151, by rfl⟩) R70303
theorem R422975 : Reach 422975 := rs (se 1 (by rfl) ⟨317231, by rfl⟩) R634463
theorem R324769 : Reach 324769 := rs (se 2 (by rfl) ⟨121788, by rfl⟩) R243577
theorem R128479 : Reach 128479 := rs (se 1 (by rfl) ⟨96359, by rfl⟩) R192719
theorem R63031 : Reach 63031 := rs (se 1 (by rfl) ⟨47273, by rfl⟩) R94547
theorem R63865 : Reach 63865 := rs (se 2 (by rfl) ⟨23949, by rfl⟩) R47899
theorem R129437 : Reach 129437 := rs (se 3 (by rfl) ⟨24269, by rfl⟩) R48539
theorem R162283 : Reach 162283 := rs (se 1 (by rfl) ⟨121712, by rfl⟩) R243425
theorem R96815 : Reach 96815 := rs (se 1 (by rfl) ⟨72611, by rfl⟩) R145223
theorem R228577 : Reach 228577 := rs (se 2 (by rfl) ⟨85716, by rfl⟩) R171433
theorem R65279 : Reach 65279 := rs (se 1 (by rfl) ⟨48959, by rfl⟩) R97919
theorem R327503 : Reach 327503 := rs (se 1 (by rfl) ⟨245627, by rfl⟩) R491255
theorem R196829 : Reach 196829 := rs (se 3 (by rfl) ⟨36905, by rfl⟩) R73811
theorem R329143 : Reach 329143 := rs (se 1 (by rfl) ⟨246857, by rfl⟩) R493715
theorem R132833 : Reach 132833 := rs (se 2 (by rfl) ⟨49812, by rfl⟩) R99625
theorem R788413 : Reach 788413 := rs (se 3 (by rfl) ⟨147827, by rfl⟩) R295655
theorem R35263 : Reach 35263 := rs (se 1 (by rfl) ⟨26447, by rfl⟩) R52895
theorem R133757 : Reach 133757 := rs (se 3 (by rfl) ⟨25079, by rfl⟩) R50159
theorem R68519 : Reach 68519 := rs (se 1 (by rfl) ⟨51389, by rfl⟩) R102779
theorem R69257 : Reach 69257 := rs (se 2 (by rfl) ⟨25971, by rfl⟩) R51943
theorem R36583 : Reach 36583 := rs (se 1 (by rfl) ⟨27437, by rfl⟩) R54875
theorem R332075 : Reach 332075 := rs (se 1 (by rfl) ⟨249056, by rfl⟩) R498113
theorem R37615 : Reach 37615 := rs (se 1 (by rfl) ⟨28211, by rfl⟩) R56423
theorem R37631 : Reach 37631 := rs (se 1 (by rfl) ⟨28223, by rfl⟩) R56447
theorem R37663 : Reach 37663 := rs (se 1 (by rfl) ⟨28247, by rfl⟩) R56495
theorem R38767 : Reach 38767 := rs (se 1 (by rfl) ⟨29075, by rfl⟩) R58151
theorem R38911 : Reach 38911 := rs (se 1 (by rfl) ⟨29183, by rfl⟩) R58367
theorem R202823 : Reach 202823 := rs (se 1 (by rfl) ⟨152117, by rfl⟩) R304235
theorem R433025 : Reach 433025 := rs (se 2 (by rfl) ⟨162384, by rfl⟩) R324769
theorem R203755 : Reach 203755 := rs (se 1 (by rfl) ⟨152816, by rfl⟩) R305633
theorem R171305 : Reach 171305 := rs (se 2 (by rfl) ⟨64239, by rfl⟩) R128479
theorem R138935 : Reach 138935 := rs (se 1 (by rfl) ⟨104201, by rfl⟩) R208403
theorem R238301 : Reach 238301 := rs (se 3 (by rfl) ⟨44681, by rfl⟩) R89363
theorem R304769 : Reach 304769 := rs (se 2 (by rfl) ⟨114288, by rfl⟩) R228577
theorem R3188645 : Reach 3188645 := rs (se 4 (by rfl) ⟨298935, by rfl⟩) R597871
theorem R403775 : Reach 403775 := rs (se 1 (by rfl) ⟨302831, by rfl⟩) R605663
theorem R43519 : Reach 43519 := rs (se 1 (by rfl) ⟨32639, by rfl⟩) R65279
theorem R142505 : Reach 142505 := rs (se 2 (by rfl) ⟨53439, by rfl⟩) R106879
theorem R470447 : Reach 470447 := rs (se 1 (by rfl) ⟨352835, by rfl⟩) R705671
theorem R111071 : Reach 111071 := rs (se 1 (by rfl) ⟨83303, by rfl⟩) R166607
theorem R275471 : Reach 275471 := rs (se 1 (by rfl) ⟨206603, by rfl⟩) R413207
theorem R406781 : Reach 406781 := rs (se 3 (by rfl) ⟨76271, by rfl⟩) R152543
theorem R144767 : Reach 144767 := rs (se 1 (by rfl) ⟨108575, by rfl⟩) R217151
theorem R80185 : Reach 80185 := rs (se 2 (by rfl) ⟨30069, by rfl⟩) R60139
theorem R145819 : Reach 145819 := rs (se 1 (by rfl) ⟨109364, by rfl⟩) R218729
theorem R277019 : Reach 277019 := rs (se 1 (by rfl) ⟨207764, by rfl⟩) R415529
theorem R47785 : Reach 47785 := rs (se 2 (by rfl) ⟨17919, by rfl⟩) R35839
theorem R81179 : Reach 81179 := rs (se 1 (by rfl) ⟨60884, by rfl⟩) R121769
theorem R81575 : Reach 81575 := rs (se 1 (by rfl) ⟨61181, by rfl⟩) R122363
theorem R245935 : Reach 245935 := rs (se 1 (by rfl) ⟨184451, by rfl⟩) R368903
theorem R82259 : Reach 82259 := rs (se 1 (by rfl) ⟨61694, by rfl⟩) R123389
theorem R50825 : Reach 50825 := rs (se 2 (by rfl) ⟨19059, by rfl⟩) R38119
theorem R2934767 : Reach 2934767 := rs (se 1 (by rfl) ⟨2201075, by rfl⟩) R4402151
theorem R84041 : Reach 84041 := rs (se 2 (by rfl) ⟨31515, by rfl⟩) R63031
theorem R117575 : Reach 117575 := rs (se 1 (by rfl) ⟨88181, by rfl⟩) R176363
theorem R85153 : Reach 85153 := rs (se 2 (by rfl) ⟨31932, by rfl⟩) R63865
theorem R216377 : Reach 216377 := rs (se 2 (by rfl) ⟨81141, by rfl⟩) R162283
theorem R281983 : Reach 281983 := rs (se 1 (by rfl) ⟨211487, by rfl⟩) R422975
theorem R52715 : Reach 52715 := rs (se 1 (by rfl) ⟨39536, by rfl⟩) R79073
theorem R184031 : Reach 184031 := rs (se 1 (by rfl) ⟨138023, by rfl⟩) R276047
theorem R86291 : Reach 86291 := rs (se 1 (by rfl) ⟨64718, by rfl⟩) R129437
theorem R53927 : Reach 53927 := rs (se 1 (by rfl) ⟨40445, by rfl⟩) R80891
theorem R53999 : Reach 53999 := rs (se 1 (by rfl) ⟨40499, by rfl⟩) R80999
theorem R447241 : Reach 447241 := rs (se 2 (by rfl) ⟨167715, by rfl⟩) R335431
theorem R54143 : Reach 54143 := rs (se 1 (by rfl) ⟨40607, by rfl⟩) R81215
theorem R54265 : Reach 54265 := rs (se 2 (by rfl) ⟨20349, by rfl⟩) R40699
theorem R54299 : Reach 54299 := rs (se 1 (by rfl) ⟨40724, by rfl⟩) R81449
theorem R54455 : Reach 54455 := rs (se 1 (by rfl) ⟨40841, by rfl⟩) R81683
theorem R218335 : Reach 218335 := rs (se 1 (by rfl) ⟨163751, by rfl⟩) R327503
theorem R743033 : Reach 743033 := rs (se 2 (by rfl) ⟨278637, by rfl⟩) R557275
theorem R55535 : Reach 55535 := rs (se 1 (by rfl) ⟨41651, by rfl⟩) R83303
theorem R55607 : Reach 55607 := rs (se 1 (by rfl) ⟨41705, by rfl⟩) R83411
theorem R55673 : Reach 55673 := rs (se 2 (by rfl) ⟨20877, by rfl⟩) R41755
theorem R55799 : Reach 55799 := rs (se 1 (by rfl) ⟨41849, by rfl⟩) R83699
theorem R88859 : Reach 88859 := rs (se 1 (by rfl) ⟨66644, by rfl⟩) R133289
theorem R285481 : Reach 285481 := rs (se 2 (by rfl) ⟨107055, by rfl⟩) R214111
theorem R56303 : Reach 56303 := rs (se 1 (by rfl) ⟨42227, by rfl⟩) R84455
theorem R56555 : Reach 56555 := rs (se 1 (by rfl) ⟨42416, by rfl⟩) R84833
theorem R56735 : Reach 56735 := rs (se 1 (by rfl) ⟨42551, by rfl⟩) R85103
theorem R56783 : Reach 56783 := rs (se 1 (by rfl) ⟨42587, by rfl⟩) R85175
theorem R122399 : Reach 122399 := rs (se 1 (by rfl) ⟨91799, by rfl⟩) R183599
theorem R56879 : Reach 56879 := rs (se 1 (by rfl) ⟨42659, by rfl⟩) R85319
theorem R122471 : Reach 122471 := rs (se 1 (by rfl) ⟨91853, by rfl⟩) R183707
theorem R90335 : Reach 90335 := rs (se 1 (by rfl) ⟨67751, by rfl⟩) R135503
theorem R58409 : Reach 58409 := rs (se 2 (by rfl) ⟨21903, by rfl⟩) R43807
theorem R91975 : Reach 91975 := rs (se 1 (by rfl) ⟨68981, by rfl⟩) R137963
theorem R59575 : Reach 59575 := rs (se 1 (by rfl) ⟨44681, by rfl⟩) R89363
theorem R93487 : Reach 93487 := rs (se 1 (by rfl) ⟨70115, by rfl⟩) R140231
theorem R60959 : Reach 60959 := rs (se 1 (by rfl) ⟨45719, by rfl⟩) R91439
theorem R93919 : Reach 93919 := rs (se 1 (by rfl) ⟨70439, by rfl⟩) R140879
theorem R61607 : Reach 61607 := rs (se 1 (by rfl) ⟨46205, by rfl⟩) R92411
theorem R13202189 : Reach 13202189 := rs (se 3 (by rfl) ⟨2475410, by rfl⟩) R4950821
theorem R357371 : Reach 357371 := rs (se 1 (by rfl) ⟨268028, by rfl⟩) R536057
theorem R62491 : Reach 62491 := rs (se 1 (by rfl) ⟨46868, by rfl⟩) R93737
theorem R95975 : Reach 95975 := rs (se 1 (by rfl) ⟨71981, by rfl⟩) R143963
theorem R64543 : Reach 64543 := rs (se 1 (by rfl) ⟨48407, by rfl⟩) R96815
theorem R64889 : Reach 64889 := rs (se 2 (by rfl) ⟨24333, by rfl⟩) R48667
theorem R131219 : Reach 131219 := rs (se 1 (by rfl) ⟨98414, by rfl⟩) R196829
theorem R1311653 : Reach 1311653 := rs (se 4 (by rfl) ⟨122967, by rfl⟩) R245935
theorem R35143 : Reach 35143 := rs (se 1 (by rfl) ⟨26357, by rfl⟩) R52715
theorem R1051217 : Reach 1051217 := rs (se 2 (by rfl) ⟨394206, by rfl⟩) R788413
theorem R35951 : Reach 35951 := rs (se 1 (by rfl) ⟨26963, by rfl⟩) R53927
theorem R35999 : Reach 35999 := rs (se 1 (by rfl) ⟨26999, by rfl⟩) R53999
theorem R36095 : Reach 36095 := rs (se 1 (by rfl) ⟨27071, by rfl⟩) R54143
theorem R36199 : Reach 36199 := rs (se 1 (by rfl) ⟨27149, by rfl⟩) R54299
theorem R36303 : Reach 36303 := rs (se 1 (by rfl) ⟨27227, by rfl⟩) R54455
theorem R495355 : Reach 495355 := rs (se 1 (by rfl) ⟨371516, by rfl⟩) R743033
theorem R135215 : Reach 135215 := rs (se 1 (by rfl) ⟨101411, by rfl⟩) R202823
theorem R37023 : Reach 37023 := rs (se 1 (by rfl) ⟨27767, by rfl⟩) R55535
theorem R37071 : Reach 37071 := rs (se 1 (by rfl) ⟨27803, by rfl⟩) R55607
theorem R37115 : Reach 37115 := rs (se 1 (by rfl) ⟨27836, by rfl⟩) R55673
theorem R37199 : Reach 37199 := rs (se 1 (by rfl) ⟨27899, by rfl⟩) R55799
theorem R135533 : Reach 135533 := rs (se 3 (by rfl) ⟨25412, by rfl⟩) R50825
theorem R37535 : Reach 37535 := rs (se 1 (by rfl) ⟨28151, by rfl⟩) R56303
theorem R37703 : Reach 37703 := rs (se 1 (by rfl) ⟨28277, by rfl⟩) R56555
theorem R37823 : Reach 37823 := rs (se 1 (by rfl) ⟨28367, by rfl⟩) R56735
theorem R37855 : Reach 37855 := rs (se 1 (by rfl) ⟨28391, by rfl⟩) R56783
theorem R37919 : Reach 37919 := rs (se 1 (by rfl) ⟨28439, by rfl⟩) R56879
theorem R38939 : Reach 38939 := rs (se 1 (by rfl) ⟨29204, by rfl⟩) R58409
theorem R596321 : Reach 596321 := rs (se 2 (by rfl) ⟨223620, by rfl⟩) R447241
theorem R72353 : Reach 72353 := rs (se 2 (by rfl) ⟨27132, by rfl⟩) R54265
theorem R269183 : Reach 269183 := rs (se 1 (by rfl) ⟨201887, by rfl⟩) R403775
theorem R40639 : Reach 40639 := rs (se 1 (by rfl) ⟨30479, by rfl⟩) R60959
theorem R41071 : Reach 41071 := rs (se 1 (by rfl) ⟨30803, by rfl⟩) R61607
theorem R74047 : Reach 74047 := rs (se 1 (by rfl) ⟨55535, by rfl⟩) R111071
theorem R106913 : Reach 106913 := rs (se 2 (by rfl) ⟨40092, by rfl⟩) R80185
theorem R238247 : Reach 238247 := rs (se 1 (by rfl) ⟨178685, by rfl⟩) R357371
theorem R271187 : Reach 271187 := rs (se 1 (by rfl) ⟨203390, by rfl⟩) R406781
theorem R271673 : Reach 271673 := rs (se 2 (by rfl) ⟨101877, by rfl⟩) R203755
theorem R43259 : Reach 43259 := rs (se 1 (by rfl) ⟨32444, by rfl⟩) R64889
theorem R78383 : Reach 78383 := rs (se 1 (by rfl) ⟨58787, by rfl⟩) R117575
theorem R438857 : Reach 438857 := rs (se 2 (by rfl) ⟨164571, by rfl⟩) R329143
theorem R45679 : Reach 45679 := rs (se 1 (by rfl) ⟨34259, by rfl⟩) R68519
theorem R144251 : Reach 144251 := rs (se 1 (by rfl) ⟨108188, by rfl⟩) R216377
theorem R46171 : Reach 46171 := rs (se 1 (by rfl) ⟨34628, by rfl⟩) R69257
theorem R79433 : Reach 79433 := rs (se 2 (by rfl) ⟨29787, by rfl⟩) R59575
theorem R113537 : Reach 113537 := rs (se 2 (by rfl) ⟨42576, by rfl⟩) R85153
theorem R375977 : Reach 375977 := rs (se 2 (by rfl) ⟨140991, by rfl⟩) R281983
theorem R114203 : Reach 114203 := rs (se 1 (by rfl) ⟨85652, by rfl⟩) R171305
theorem R81599 : Reach 81599 := rs (se 1 (by rfl) ⟨61199, by rfl⟩) R122399
theorem R81647 : Reach 81647 := rs (se 1 (by rfl) ⟨61235, by rfl⟩) R122471
theorem R50153 : Reach 50153 := rs (se 2 (by rfl) ⟨18807, by rfl⟩) R37615
theorem R83321 : Reach 83321 := rs (se 2 (by rfl) ⟨31245, by rfl⟩) R62491
theorem R313631 : Reach 313631 := rs (se 1 (by rfl) ⟨235223, by rfl⟩) R470447
theorem R8801459 : Reach 8801459 := rs (se 1 (by rfl) ⟨6601094, by rfl⟩) R13202189
theorem R183647 : Reach 183647 := rs (se 1 (by rfl) ⟨137735, by rfl⟩) R275471
theorem R380641 : Reach 380641 := rs (se 2 (by rfl) ⟨142740, by rfl⟩) R285481
theorem R86057 : Reach 86057 := rs (se 2 (by rfl) ⟨32271, by rfl⟩) R64543
theorem R184679 : Reach 184679 := rs (se 1 (by rfl) ⟨138509, by rfl⟩) R277019
theorem R54119 : Reach 54119 := rs (se 1 (by rfl) ⟨40589, by rfl⟩) R81179
theorem R54383 : Reach 54383 := rs (se 1 (by rfl) ⟨40787, by rfl⟩) R81575
theorem R54839 : Reach 54839 := rs (se 1 (by rfl) ⟨41129, by rfl⟩) R82259
theorem R88555 : Reach 88555 := rs (se 1 (by rfl) ⟨66416, by rfl⟩) R132833
theorem R1956511 : Reach 1956511 := rs (se 1 (by rfl) ⟨1467383, by rfl⟩) R2934767
theorem R56027 : Reach 56027 := rs (se 1 (by rfl) ⟨42020, by rfl⟩) R84041
theorem R89171 : Reach 89171 := rs (se 1 (by rfl) ⟨66878, by rfl⟩) R133757
theorem R777701 : Reach 777701 := rs (se 4 (by rfl) ⟨72909, by rfl⟩) R145819
theorem R122633 : Reach 122633 := rs (se 2 (by rfl) ⟨45987, by rfl⟩) R91975
theorem R122687 : Reach 122687 := rs (se 1 (by rfl) ⟨92015, by rfl⟩) R184031
theorem R57527 : Reach 57527 := rs (se 1 (by rfl) ⟨43145, by rfl⟩) R86291
theorem R221383 : Reach 221383 := rs (se 1 (by rfl) ⟨166037, by rfl⟩) R332075
theorem R58025 : Reach 58025 := rs (se 2 (by rfl) ⟨21759, by rfl⟩) R43519
theorem R812717 : Reach 812717 := rs (se 3 (by rfl) ⟨152384, by rfl⟩) R304769
theorem R124649 : Reach 124649 := rs (se 2 (by rfl) ⟨46743, by rfl⟩) R93487
theorem R59239 : Reach 59239 := rs (se 1 (by rfl) ⟨44429, by rfl⟩) R88859
theorem R288683 : Reach 288683 := rs (se 1 (by rfl) ⟨216512, by rfl⟩) R433025
theorem R125225 : Reach 125225 := rs (se 2 (by rfl) ⟨46959, by rfl⟩) R93919
theorem R92623 : Reach 92623 := rs (se 1 (by rfl) ⟨69467, by rfl⟩) R138935
theorem R60223 : Reach 60223 := rs (se 1 (by rfl) ⟨45167, by rfl⟩) R90335
theorem R158867 : Reach 158867 := rs (se 1 (by rfl) ⟨119150, by rfl⟩) R238301
theorem R2125763 : Reach 2125763 := rs (se 1 (by rfl) ⟨1594322, by rfl⟩) R3188645
theorem R291113 : Reach 291113 := rs (se 2 (by rfl) ⟨109167, by rfl⟩) R218335
theorem R95003 : Reach 95003 := rs (se 1 (by rfl) ⟨71252, by rfl⟩) R142505
theorem R63713 : Reach 63713 := rs (se 2 (by rfl) ⟨23892, by rfl⟩) R47785
theorem R96511 : Reach 96511 := rs (se 1 (by rfl) ⟨72383, by rfl⟩) R144767
theorem R63983 : Reach 63983 := rs (se 1 (by rfl) ⟨47987, by rfl⟩) R95975
theorem R162557 : Reach 162557 := rs (se 3 (by rfl) ⟨30479, by rfl⟩) R60959
theorem R295177 : Reach 295177 := rs (se 2 (by rfl) ⟨110691, by rfl⟩) R221383
theorem R98729 : Reach 98729 := rs (se 2 (by rfl) ⟨37023, by rfl⟩) R74047
theorem R5867639 : Reach 5867639 := rs (se 1 (by rfl) ⟨4400729, by rfl⟩) R8801459
theorem R133741 : Reach 133741 := rs (se 3 (by rfl) ⟨25076, by rfl⟩) R50153
theorem R36079 : Reach 36079 := rs (se 1 (by rfl) ⟨27059, by rfl⟩) R54119
theorem R36255 : Reach 36255 := rs (se 1 (by rfl) ⟨27191, by rfl⟩) R54383
theorem R36559 : Reach 36559 := rs (se 1 (by rfl) ⟨27419, by rfl⟩) R54839
theorem R397547 : Reach 397547 := rs (se 1 (by rfl) ⟨298160, by rfl⟩) R596321
theorem R37351 : Reach 37351 := rs (se 1 (by rfl) ⟨28013, by rfl⟩) R56027
theorem R660473 : Reach 660473 := rs (se 2 (by rfl) ⟨247677, by rfl⟩) R495355
theorem R103837 : Reach 103837 := rs (se 3 (by rfl) ⟨19469, by rfl⟩) R38939
theorem R38351 : Reach 38351 := rs (se 1 (by rfl) ⟨28763, by rfl⟩) R57527
theorem R71275 : Reach 71275 := rs (se 1 (by rfl) ⟨53456, by rfl⟩) R106913
theorem R38683 : Reach 38683 := rs (se 1 (by rfl) ⟨29012, by rfl⟩) R58025
theorem R105911 : Reach 105911 := rs (se 1 (by rfl) ⟨79433, by rfl⟩) R158867
theorem R1417175 : Reach 1417175 := rs (se 1 (by rfl) ⟨1062881, by rfl⟩) R2125763
theorem R2073869 : Reach 2073869 := rs (se 3 (by rfl) ⟨388850, by rfl⟩) R777701
theorem R42475 : Reach 42475 := rs (se 1 (by rfl) ⟨31856, by rfl⟩) R63713
theorem R42655 : Reach 42655 := rs (se 1 (by rfl) ⟨31991, by rfl⟩) R63983
theorem R108371 : Reach 108371 := rs (se 1 (by rfl) ⟨81278, by rfl⟩) R162557
theorem R75691 : Reach 75691 := rs (se 1 (by rfl) ⟨56768, by rfl⟩) R113537
theorem R76135 : Reach 76135 := rs (se 1 (by rfl) ⟨57101, by rfl⟩) R114203
theorem R209087 : Reach 209087 := rs (se 1 (by rfl) ⟨156815, by rfl⟩) R313631
theorem R700811 : Reach 700811 := rs (se 1 (by rfl) ⟨525608, by rfl⟩) R1051217
theorem R78985 : Reach 78985 := rs (se 2 (by rfl) ⟨29619, by rfl⟩) R59239
theorem R80297 : Reach 80297 := rs (se 2 (by rfl) ⟨30111, by rfl⟩) R60223
theorem R179455 : Reach 179455 := rs (se 1 (by rfl) ⟨134591, by rfl⟩) R269183
theorem R507521 : Reach 507521 := rs (se 2 (by rfl) ⟨190320, by rfl⟩) R380641
theorem R81755 : Reach 81755 := rs (se 1 (by rfl) ⟨61316, by rfl⟩) R122633
theorem R81791 : Reach 81791 := rs (se 1 (by rfl) ⟨61343, by rfl⟩) R122687
theorem R180791 : Reach 180791 := rs (se 1 (by rfl) ⟨135593, by rfl⟩) R271187
theorem R115357 : Reach 115357 := rs (se 3 (by rfl) ⟨21629, by rfl⟩) R43259
theorem R181115 : Reach 181115 := rs (se 1 (by rfl) ⟨135836, by rfl⟩) R271673
theorem R541811 : Reach 541811 := rs (se 1 (by rfl) ⟨406358, by rfl⟩) R812717
theorem R83099 : Reach 83099 := rs (se 1 (by rfl) ⟨62324, by rfl⟩) R124649
theorem R83483 : Reach 83483 := rs (se 1 (by rfl) ⟨62612, by rfl⟩) R125225
theorem R870389 : Reach 870389 := rs (se 5 (by rfl) ⟨40799, by rfl⟩) R81599
theorem R52255 : Reach 52255 := rs (se 1 (by rfl) ⟨39191, by rfl⟩) R78383
theorem R118073 : Reach 118073 := rs (se 2 (by rfl) ⟨44277, by rfl⟩) R88555
theorem R2608681 : Reach 2608681 := rs (se 2 (by rfl) ⟨978255, by rfl⟩) R1956511
theorem R52955 : Reach 52955 := rs (se 1 (by rfl) ⟨39716, by rfl⟩) R79433
theorem R250651 : Reach 250651 := rs (se 1 (by rfl) ⟨187988, by rfl⟩) R375977
theorem R54185 : Reach 54185 := rs (se 2 (by rfl) ⟨20319, by rfl⟩) R40639
theorem R54431 : Reach 54431 := rs (se 1 (by rfl) ⟨40823, by rfl⟩) R81647
theorem R87479 : Reach 87479 := rs (se 1 (by rfl) ⟨65609, by rfl⟩) R131219
theorem R54761 : Reach 54761 := rs (se 2 (by rfl) ⟨20535, by rfl⟩) R41071
theorem R874435 : Reach 874435 := rs (se 1 (by rfl) ⟨655826, by rfl⟩) R1311653
theorem R55547 : Reach 55547 := rs (se 1 (by rfl) ⟨41660, by rfl⟩) R83321
theorem R122431 : Reach 122431 := rs (se 1 (by rfl) ⟨91823, by rfl⟩) R183647
theorem R57371 : Reach 57371 := rs (se 1 (by rfl) ⟨43028, by rfl⟩) R86057
theorem R90143 : Reach 90143 := rs (se 1 (by rfl) ⟨67607, by rfl⟩) R135215
theorem R123119 : Reach 123119 := rs (se 1 (by rfl) ⟨92339, by rfl⟩) R184679
theorem R90355 : Reach 90355 := rs (se 1 (by rfl) ⟨67766, by rfl⟩) R135533
theorem R123497 : Reach 123497 := rs (se 2 (by rfl) ⟨46311, by rfl⟩) R92623
theorem R59447 : Reach 59447 := rs (se 1 (by rfl) ⟨44585, by rfl⟩) R89171
theorem R158831 : Reach 158831 := rs (se 1 (by rfl) ⟨119123, by rfl⟩) R238247
theorem R60905 : Reach 60905 := rs (se 2 (by rfl) ⟨22839, by rfl⟩) R45679
theorem R192455 : Reach 192455 := rs (se 1 (by rfl) ⟨144341, by rfl⟩) R288683
theorem R61561 : Reach 61561 := rs (se 2 (by rfl) ⟨23085, by rfl⟩) R46171
theorem R192941 : Reach 192941 := rs (se 3 (by rfl) ⟨36176, by rfl⟩) R72353
theorem R194075 : Reach 194075 := rs (se 1 (by rfl) ⟨145556, by rfl⟩) R291113
theorem R128681 : Reach 128681 := rs (se 2 (by rfl) ⟨48255, by rfl⟩) R96511
theorem R292571 : Reach 292571 := rs (se 1 (by rfl) ⟨219428, by rfl⟩) R438857
theorem R63335 : Reach 63335 := rs (se 1 (by rfl) ⟨47501, by rfl⟩) R95003
theorem R96167 : Reach 96167 := rs (se 1 (by rfl) ⟨72125, by rfl⟩) R144251
theorem R65819 : Reach 65819 := rs (se 1 (by rfl) ⟨49364, by rfl⟩) R98729
theorem R393569 : Reach 393569 := rs (se 2 (by rfl) ⟨147588, by rfl⟩) R295177
theorem R361207 : Reach 361207 := rs (se 1 (by rfl) ⟨270905, by rfl⟩) R541811
theorem R35303 : Reach 35303 := rs (se 1 (by rfl) ⟨26477, by rfl⟩) R52955
theorem R100921 : Reach 100921 := rs (se 2 (by rfl) ⟨37845, by rfl⟩) R75691
theorem R265031 : Reach 265031 := rs (se 1 (by rfl) ⟨198773, by rfl⟩) R397547
theorem R101513 : Reach 101513 := rs (se 2 (by rfl) ⟨38067, by rfl⟩) R76135
theorem R36123 : Reach 36123 := rs (se 1 (by rfl) ⟨27092, by rfl⟩) R54185
theorem R36287 : Reach 36287 := rs (se 1 (by rfl) ⟨27215, by rfl⟩) R54431
theorem R36507 : Reach 36507 := rs (se 1 (by rfl) ⟨27380, by rfl⟩) R54761
theorem R69673 : Reach 69673 := rs (se 2 (by rfl) ⟨26127, by rfl⟩) R52255
theorem R37031 : Reach 37031 := rs (se 1 (by rfl) ⟨27773, by rfl⟩) R55547
theorem R3478241 : Reach 3478241 := rs (se 2 (by rfl) ⟨1304340, by rfl⟩) R2608681
theorem R70607 : Reach 70607 := rs (se 1 (by rfl) ⟨52955, by rfl⟩) R105911
theorem R38247 : Reach 38247 := rs (se 1 (by rfl) ⟨28685, by rfl⟩) R57371
theorem R1382579 : Reach 1382579 := rs (se 1 (by rfl) ⟨1036934, by rfl⟩) R2073869
theorem R334201 : Reach 334201 := rs (se 2 (by rfl) ⟨125325, by rfl⟩) R250651
theorem R72247 : Reach 72247 := rs (se 1 (by rfl) ⟨54185, by rfl⟩) R108371
theorem R39631 : Reach 39631 := rs (se 1 (by rfl) ⟨29723, by rfl⟩) R59447
theorem R105313 : Reach 105313 := rs (se 2 (by rfl) ⟨39492, by rfl⟩) R78985
theorem R138449 : Reach 138449 := rs (se 2 (by rfl) ⟨51918, by rfl⟩) R103837
theorem R105887 : Reach 105887 := rs (se 1 (by rfl) ⟨79415, by rfl⟩) R158831
theorem R40603 : Reach 40603 := rs (se 1 (by rfl) ⟨30452, by rfl⟩) R60905
theorem R139391 : Reach 139391 := rs (se 1 (by rfl) ⟨104543, by rfl⟩) R209087
theorem R467207 : Reach 467207 := rs (se 1 (by rfl) ⟨350405, by rfl⟩) R700811
theorem R42223 : Reach 42223 := rs (se 1 (by rfl) ⟨31667, by rfl⟩) R63335
theorem R239273 : Reach 239273 := rs (se 2 (by rfl) ⟨89727, by rfl⟩) R179455
theorem R338347 : Reach 338347 := rs (se 1 (by rfl) ⟨253760, by rfl⟩) R507521
theorem R3911759 : Reach 3911759 := rs (se 1 (by rfl) ⟨2933819, by rfl⟩) R5867639
theorem R78715 : Reach 78715 := rs (se 1 (by rfl) ⟨59036, by rfl⟩) R118073
theorem R440315 : Reach 440315 := rs (se 1 (by rfl) ⟨330236, by rfl⟩) R660473
theorem R178321 : Reach 178321 := rs (se 2 (by rfl) ⟨66870, by rfl⟩) R133741
theorem R82079 : Reach 82079 := rs (se 1 (by rfl) ⟨61559, by rfl⟩) R123119
theorem R82081 : Reach 82081 := rs (se 2 (by rfl) ⟨30780, by rfl⟩) R61561
theorem R82331 : Reach 82331 := rs (se 1 (by rfl) ⟨61748, by rfl⟩) R123497
theorem R1165913 : Reach 1165913 := rs (se 2 (by rfl) ⟨437217, by rfl⟩) R874435
theorem R85787 : Reach 85787 := rs (se 1 (by rfl) ⟨64340, by rfl⟩) R128681
theorem R53531 : Reach 53531 := rs (se 1 (by rfl) ⟨40148, by rfl⟩) R80297
theorem R54503 : Reach 54503 := rs (se 1 (by rfl) ⟨40877, by rfl⟩) R81755
theorem R54527 : Reach 54527 := rs (se 1 (by rfl) ⟨40895, by rfl⟩) R81791
theorem R120473 : Reach 120473 := rs (se 2 (by rfl) ⟨45177, by rfl⟩) R90355
theorem R120527 : Reach 120527 := rs (se 1 (by rfl) ⟨90395, by rfl⟩) R180791
theorem R120743 : Reach 120743 := rs (se 1 (by rfl) ⟨90557, by rfl⟩) R181115
theorem R55399 : Reach 55399 := rs (se 1 (by rfl) ⟨41549, by rfl⟩) R83099
theorem R153809 : Reach 153809 := rs (se 2 (by rfl) ⟨57678, by rfl⟩) R115357
theorem R55655 : Reach 55655 := rs (se 1 (by rfl) ⟨41741, by rfl⟩) R83483
theorem R580259 : Reach 580259 := rs (se 1 (by rfl) ⟨435194, by rfl⟩) R870389
theorem R56633 : Reach 56633 := rs (se 2 (by rfl) ⟨21237, by rfl⟩) R42475
theorem R56873 : Reach 56873 := rs (se 2 (by rfl) ⟨21327, by rfl⟩) R42655
theorem R58319 : Reach 58319 := rs (se 1 (by rfl) ⟨43739, by rfl⟩) R87479
theorem R944783 : Reach 944783 := rs (se 1 (by rfl) ⟨708587, by rfl⟩) R1417175
theorem R60095 : Reach 60095 := rs (se 1 (by rfl) ⟨45071, by rfl⟩) R90143
theorem R95033 : Reach 95033 := rs (se 2 (by rfl) ⟨35637, by rfl⟩) R71275
theorem R128303 : Reach 128303 := rs (se 1 (by rfl) ⟨96227, by rfl⟩) R192455
theorem R128627 : Reach 128627 := rs (se 1 (by rfl) ⟨96470, by rfl⟩) R192941
theorem R129383 : Reach 129383 := rs (se 1 (by rfl) ⟨97037, by rfl⟩) R194075
theorem R195047 : Reach 195047 := rs (se 1 (by rfl) ⟨146285, by rfl⟩) R292571
theorem R64111 : Reach 64111 := rs (se 1 (by rfl) ⟨48083, by rfl⟩) R96167
theorem R163241 : Reach 163241 := rs (se 2 (by rfl) ⟨61215, by rfl⟩) R122431
theorem R262379 : Reach 262379 := rs (se 1 (by rfl) ⟨196784, by rfl⟩) R393569
theorem R9275309 : Reach 9275309 := rs (se 3 (by rfl) ⟨1739120, by rfl⟩) R3478241
theorem R1804517 : Reach 1804517 := rs (se 4 (by rfl) ⟨169173, by rfl⟩) R338347
theorem R35687 : Reach 35687 := rs (se 1 (by rfl) ⟨26765, by rfl⟩) R53531
theorem R134561 : Reach 134561 := rs (se 2 (by rfl) ⟨50460, by rfl⟩) R100921
theorem R36335 : Reach 36335 := rs (se 1 (by rfl) ⟨27251, by rfl⟩) R54503
theorem R36351 : Reach 36351 := rs (se 1 (by rfl) ⟨27263, by rfl⟩) R54527
theorem R921719 : Reach 921719 := rs (se 1 (by rfl) ⟨691289, by rfl⟩) R1382579
theorem R102539 : Reach 102539 := rs (se 1 (by rfl) ⟨76904, by rfl⟩) R153809
theorem R37103 : Reach 37103 := rs (se 1 (by rfl) ⟨27827, by rfl⟩) R55655
theorem R37755 : Reach 37755 := rs (se 1 (by rfl) ⟨28316, by rfl⟩) R56633
theorem R37915 : Reach 37915 := rs (se 1 (by rfl) ⟨28436, by rfl⟩) R56873
theorem R38879 : Reach 38879 := rs (se 1 (by rfl) ⟨29159, by rfl⟩) R58319
theorem R629855 : Reach 629855 := rs (se 1 (by rfl) ⟨472391, by rfl⟩) R944783
theorem R40063 : Reach 40063 := rs (se 1 (by rfl) ⟨30047, by rfl⟩) R60095
theorem R73865 : Reach 73865 := rs (se 2 (by rfl) ⟨27699, by rfl⟩) R55399
theorem R237761 : Reach 237761 := rs (se 2 (by rfl) ⟨89160, by rfl⟩) R178321
theorem R270701 : Reach 270701 := rs (se 3 (by rfl) ⟨50756, by rfl⟩) R101513
theorem R140417 : Reach 140417 := rs (se 2 (by rfl) ⟨52656, by rfl⟩) R105313
theorem R108827 : Reach 108827 := rs (se 1 (by rfl) ⟨81620, by rfl⟩) R163241
theorem R43879 : Reach 43879 := rs (se 1 (by rfl) ⟨32909, by rfl⟩) R65819
theorem R109441 : Reach 109441 := rs (se 2 (by rfl) ⟨41040, by rfl⟩) R82081
theorem R175517 : Reach 175517 := rs (se 3 (by rfl) ⟨32909, by rfl⟩) R65819
theorem R176687 : Reach 176687 := rs (se 1 (by rfl) ⟨132515, by rfl⟩) R265031
theorem R47071 : Reach 47071 := rs (se 1 (by rfl) ⟨35303, by rfl⟩) R70607
theorem R80315 : Reach 80315 := rs (se 1 (by rfl) ⟨60236, by rfl⟩) R120473
theorem R80351 : Reach 80351 := rs (se 1 (by rfl) ⟨60263, by rfl⟩) R120527
theorem R80495 : Reach 80495 := rs (se 1 (by rfl) ⟨60371, by rfl⟩) R120743
theorem R311471 : Reach 311471 := rs (se 1 (by rfl) ⟨233603, by rfl⟩) R467207
theorem R2607839 : Reach 2607839 := rs (se 1 (by rfl) ⟨1955879, by rfl⟩) R3911759
theorem R445601 : Reach 445601 := rs (se 2 (by rfl) ⟨167100, by rfl⟩) R334201
theorem R85481 : Reach 85481 := rs (se 2 (by rfl) ⟨32055, by rfl⟩) R64111
theorem R85535 : Reach 85535 := rs (se 1 (by rfl) ⟨64151, by rfl⟩) R128303
theorem R52841 : Reach 52841 := rs (se 2 (by rfl) ⟨19815, by rfl⟩) R39631
theorem R85751 : Reach 85751 := rs (se 1 (by rfl) ⟨64313, by rfl⟩) R128627
theorem R282365 : Reach 282365 := rs (se 3 (by rfl) ⟨52943, by rfl⟩) R105887
theorem R86255 : Reach 86255 := rs (se 1 (by rfl) ⟨64691, by rfl⟩) R129383
theorem R54137 : Reach 54137 := rs (se 2 (by rfl) ⟨20301, by rfl⟩) R40603
theorem R54719 : Reach 54719 := rs (se 1 (by rfl) ⟨41039, by rfl⟩) R82079
theorem R54887 : Reach 54887 := rs (se 1 (by rfl) ⟨41165, by rfl⟩) R82331
theorem R481609 : Reach 481609 := rs (se 2 (by rfl) ⟨180603, by rfl⟩) R361207
theorem R56297 : Reach 56297 := rs (se 2 (by rfl) ⟨21111, by rfl⟩) R42223
theorem R777275 : Reach 777275 := rs (se 1 (by rfl) ⟨582956, by rfl⟩) R1165913
theorem R57191 : Reach 57191 := rs (se 1 (by rfl) ⟨42893, by rfl⟩) R85787
theorem R386839 : Reach 386839 := rs (se 1 (by rfl) ⟨290129, by rfl⟩) R580259
theorem R419813 : Reach 419813 := rs (se 4 (by rfl) ⟨39357, by rfl⟩) R78715
theorem R92299 : Reach 92299 := rs (se 1 (by rfl) ⟨69224, by rfl⟩) R138449
theorem R92897 : Reach 92897 := rs (se 2 (by rfl) ⟨34836, by rfl⟩) R69673
theorem R92927 : Reach 92927 := rs (se 1 (by rfl) ⟨69695, by rfl⟩) R139391
theorem R159515 : Reach 159515 := rs (se 1 (by rfl) ⟨119636, by rfl⟩) R239273
theorem R63355 : Reach 63355 := rs (se 1 (by rfl) ⟨47516, by rfl⟩) R95033
theorem R96329 : Reach 96329 := rs (se 2 (by rfl) ⟨36123, by rfl⟩) R72247
theorem R293543 : Reach 293543 := rs (se 1 (by rfl) ⟨220157, by rfl⟩) R440315
theorem R130031 : Reach 130031 := rs (se 1 (by rfl) ⟨97523, by rfl⟩) R195047
theorem R98941 : Reach 98941 := rs (se 3 (by rfl) ⟨18551, by rfl⟩) R37103
theorem R1738559 : Reach 1738559 := rs (se 1 (by rfl) ⟨1303919, by rfl⟩) R2607839
theorem R297067 : Reach 297067 := rs (se 1 (by rfl) ⟨222800, by rfl⟩) R445601
theorem R35227 : Reach 35227 := rs (se 1 (by rfl) ⟨26420, by rfl⟩) R52841
theorem R68359 : Reach 68359 := rs (se 1 (by rfl) ⟨51269, by rfl⟩) R102539
theorem R36091 : Reach 36091 := rs (se 1 (by rfl) ⟨27068, by rfl⟩) R54137
theorem R36479 : Reach 36479 := rs (se 1 (by rfl) ⟨27359, by rfl⟩) R54719
theorem R36591 : Reach 36591 := rs (se 1 (by rfl) ⟨27443, by rfl⟩) R54887
theorem R37531 : Reach 37531 := rs (se 1 (by rfl) ⟨28148, by rfl⟩) R56297
theorem R38127 : Reach 38127 := rs (se 1 (by rfl) ⟨28595, by rfl⟩) R57191
theorem R72551 : Reach 72551 := rs (se 1 (by rfl) ⟨54413, by rfl⟩) R108827
theorem R106343 : Reach 106343 := rs (se 1 (by rfl) ⟨79757, by rfl⟩) R159515
theorem R207647 : Reach 207647 := rs (se 1 (by rfl) ⟨155735, by rfl⟩) R311471
theorem R174919 : Reach 174919 := rs (se 1 (by rfl) ⟨131189, by rfl⟩) R262379
theorem R2568581 : Reach 2568581 := rs (se 4 (by rfl) ⟨240804, by rfl⟩) R481609
theorem R145921 : Reach 145921 := rs (se 2 (by rfl) ⟨54720, by rfl⟩) R109441
theorem R49243 : Reach 49243 := rs (se 1 (by rfl) ⟨36932, by rfl⟩) R73865
theorem R180467 : Reach 180467 := rs (se 1 (by rfl) ⟨135350, by rfl⟩) R270701
theorem R279875 : Reach 279875 := rs (se 1 (by rfl) ⟨209906, by rfl⟩) R419813
theorem R117011 : Reach 117011 := rs (se 1 (by rfl) ⟨87758, by rfl⟩) R175517
theorem R84473 : Reach 84473 := rs (se 2 (by rfl) ⟨31677, by rfl⟩) R63355
theorem R117791 : Reach 117791 := rs (se 1 (by rfl) ⟨88343, by rfl⟩) R176687
theorem R53417 : Reach 53417 := rs (se 2 (by rfl) ⟨20031, by rfl⟩) R40063
theorem R53543 : Reach 53543 := rs (se 1 (by rfl) ⟨40157, by rfl⟩) R80315
theorem R53567 : Reach 53567 := rs (se 1 (by rfl) ⟨40175, by rfl⟩) R80351
theorem R53663 : Reach 53663 := rs (se 1 (by rfl) ⟨40247, by rfl⟩) R80495
theorem R86687 : Reach 86687 := rs (se 1 (by rfl) ⟨65015, by rfl⟩) R130031
theorem R6183539 : Reach 6183539 := rs (se 1 (by rfl) ⟨4637654, by rfl⟩) R9275309
theorem R1203011 : Reach 1203011 := rs (se 1 (by rfl) ⟨902258, by rfl⟩) R1804517
theorem R89707 : Reach 89707 := rs (se 1 (by rfl) ⟨67280, by rfl⟩) R134561
theorem R56987 : Reach 56987 := rs (se 1 (by rfl) ⟨42740, by rfl⟩) R85481
theorem R57023 : Reach 57023 := rs (se 1 (by rfl) ⟨42767, by rfl⟩) R85535
theorem R57167 : Reach 57167 := rs (se 1 (by rfl) ⟨42875, by rfl⟩) R85751
theorem R188243 : Reach 188243 := rs (se 1 (by rfl) ⟨141182, by rfl⟩) R282365
theorem R614479 : Reach 614479 := rs (se 1 (by rfl) ⟨460859, by rfl⟩) R921719
theorem R57503 : Reach 57503 := rs (se 1 (by rfl) ⟨43127, by rfl⟩) R86255
theorem R123065 : Reach 123065 := rs (se 2 (by rfl) ⟨46149, by rfl⟩) R92299
theorem R58505 : Reach 58505 := rs (se 2 (by rfl) ⟨21939, by rfl⟩) R43879
theorem R518183 : Reach 518183 := rs (se 1 (by rfl) ⟨388637, by rfl⟩) R777275
theorem R419903 : Reach 419903 := rs (se 1 (by rfl) ⟨314927, by rfl⟩) R629855
theorem R158507 : Reach 158507 := rs (se 1 (by rfl) ⟨118880, by rfl⟩) R237761
theorem R93611 : Reach 93611 := rs (se 1 (by rfl) ⟨70208, by rfl⟩) R140417
theorem R61931 : Reach 61931 := rs (se 1 (by rfl) ⟨46448, by rfl⟩) R92897
theorem R61951 : Reach 61951 := rs (se 1 (by rfl) ⟨46463, by rfl⟩) R92927
theorem R95165 : Reach 95165 := rs (se 3 (by rfl) ⟨17843, by rfl⟩) R35687
theorem R62761 : Reach 62761 := rs (se 2 (by rfl) ⟨23535, by rfl⟩) R47071
theorem R64219 : Reach 64219 := rs (se 1 (by rfl) ⟨48164, by rfl⟩) R96329
theorem R2063141 : Reach 2063141 := rs (se 4 (by rfl) ⟨193419, by rfl⟩) R386839
theorem R195695 : Reach 195695 := rs (se 1 (by rfl) ⟨146771, by rfl⟩) R293543
theorem R819305 : Reach 819305 := rs (se 2 (by rfl) ⟨307239, by rfl⟩) R614479
theorem R65657 : Reach 65657 := rs (se 2 (by rfl) ⟨24621, by rfl⟩) R49243
theorem R131921 : Reach 131921 := rs (se 2 (by rfl) ⟨49470, by rfl⟩) R98941
theorem R35611 : Reach 35611 := rs (se 1 (by rfl) ⟨26708, by rfl⟩) R53417
theorem R396089 : Reach 396089 := rs (se 2 (by rfl) ⟨148533, by rfl⟩) R297067
theorem R35695 : Reach 35695 := rs (se 1 (by rfl) ⟨26771, by rfl⟩) R53543
theorem R35711 : Reach 35711 := rs (se 1 (by rfl) ⟨26783, by rfl⟩) R53567
theorem R35775 : Reach 35775 := rs (se 1 (by rfl) ⟨26831, by rfl⟩) R53663
theorem R233225 : Reach 233225 := rs (se 2 (by rfl) ⟨87459, by rfl⟩) R174919
theorem R37991 : Reach 37991 := rs (se 1 (by rfl) ⟨28493, by rfl⟩) R56987
theorem R38015 : Reach 38015 := rs (se 1 (by rfl) ⟨28511, by rfl⟩) R57023
theorem R38111 : Reach 38111 := rs (se 1 (by rfl) ⟨28583, by rfl⟩) R57167
theorem R70895 : Reach 70895 := rs (se 1 (by rfl) ⟨53171, by rfl⟩) R106343
theorem R38335 : Reach 38335 := rs (se 1 (by rfl) ⟨28751, by rfl⟩) R57503
theorem R39003 : Reach 39003 := rs (se 1 (by rfl) ⟨29252, by rfl⟩) R58505
theorem R138431 : Reach 138431 := rs (se 1 (by rfl) ⟨103823, by rfl⟩) R207647
theorem R105671 : Reach 105671 := rs (se 1 (by rfl) ⟨79253, by rfl⟩) R158507
theorem R1712387 : Reach 1712387 := rs (se 1 (by rfl) ⟨1284290, by rfl⟩) R2568581
theorem R41287 : Reach 41287 := rs (se 1 (by rfl) ⟨30965, by rfl⟩) R61931
theorem R1159039 : Reach 1159039 := rs (se 1 (by rfl) ⟨869279, by rfl⟩) R1738559
theorem R78007 : Reach 78007 := rs (se 1 (by rfl) ⟨58505, by rfl⟩) R117011
theorem R78527 : Reach 78527 := rs (se 1 (by rfl) ⟨58895, by rfl⟩) R117791
theorem R802007 : Reach 802007 := rs (se 1 (by rfl) ⟨601505, by rfl⟩) R1203011
theorem R48367 : Reach 48367 := rs (se 1 (by rfl) ⟨36275, by rfl⟩) R72551
theorem R82043 : Reach 82043 := rs (se 1 (by rfl) ⟨61532, by rfl⟩) R123065
theorem R82601 : Reach 82601 := rs (se 2 (by rfl) ⟨30975, by rfl⟩) R61951
theorem R345455 : Reach 345455 := rs (se 1 (by rfl) ⟨259091, by rfl⟩) R518183
theorem R279935 : Reach 279935 := rs (se 1 (by rfl) ⟨209951, by rfl⟩) R419903
theorem R83681 : Reach 83681 := rs (se 2 (by rfl) ⟨31380, by rfl⟩) R62761
theorem R85625 : Reach 85625 := rs (se 2 (by rfl) ⟨32109, by rfl⟩) R64219
theorem R119609 : Reach 119609 := rs (se 2 (by rfl) ⟨44853, by rfl⟩) R89707
theorem R120311 : Reach 120311 := rs (se 1 (by rfl) ⟨90233, by rfl⟩) R180467
theorem R186583 : Reach 186583 := rs (se 1 (by rfl) ⟨139937, by rfl⟩) R279875
theorem R56315 : Reach 56315 := rs (se 1 (by rfl) ⟨42236, by rfl⟩) R84473
theorem R57791 : Reach 57791 := rs (se 1 (by rfl) ⟨43343, by rfl⟩) R86687
theorem R91145 : Reach 91145 := rs (se 2 (by rfl) ⟨34179, by rfl⟩) R68359
theorem R4122359 : Reach 4122359 := rs (se 1 (by rfl) ⟨3091769, by rfl⟩) R6183539
theorem R125495 : Reach 125495 := rs (se 1 (by rfl) ⟨94121, by rfl⟩) R188243
theorem R62407 : Reach 62407 := rs (se 1 (by rfl) ⟨46805, by rfl⟩) R93611
theorem R63443 : Reach 63443 := rs (se 1 (by rfl) ⟨47582, by rfl⟩) R95165
theorem R194561 : Reach 194561 := rs (se 2 (by rfl) ⟨72960, by rfl⟩) R145921
theorem R1375427 : Reach 1375427 := rs (se 1 (by rfl) ⟨1031570, by rfl⟩) R2063141
theorem R130463 : Reach 130463 := rs (se 1 (by rfl) ⟨97847, by rfl⟩) R195695
theorem R230303 : Reach 230303 := rs (se 1 (by rfl) ⟨172727, by rfl⟩) R345455
theorem R264059 : Reach 264059 := rs (se 1 (by rfl) ⟨198044, by rfl⟩) R396089
theorem R37543 : Reach 37543 := rs (se 1 (by rfl) ⟨28157, by rfl⟩) R56315
theorem R104009 : Reach 104009 := rs (se 2 (by rfl) ⟨39003, by rfl⟩) R78007
theorem R38527 : Reach 38527 := rs (se 1 (by rfl) ⟨28895, by rfl⟩) R57791
theorem R42295 : Reach 42295 := rs (se 1 (by rfl) ⟨31721, by rfl⟩) R63443
theorem R534671 : Reach 534671 := rs (se 1 (by rfl) ⟨401003, by rfl⟩) R802007
theorem R43771 : Reach 43771 := rs (se 1 (by rfl) ⟨32828, by rfl⟩) R65657
theorem R4566365 : Reach 4566365 := rs (se 3 (by rfl) ⟨856193, by rfl⟩) R1712387
theorem R209405 : Reach 209405 := rs (se 3 (by rfl) ⟨39263, by rfl⟩) R78527
theorem R79739 : Reach 79739 := rs (se 1 (by rfl) ⟨59804, by rfl⟩) R119609
theorem R80207 : Reach 80207 := rs (se 1 (by rfl) ⟨60155, by rfl⟩) R120311
theorem R83209 : Reach 83209 := rs (se 2 (by rfl) ⟨31203, by rfl⟩) R62407
theorem R83663 : Reach 83663 := rs (se 1 (by rfl) ⟨62747, by rfl⟩) R125495
theorem R248777 : Reach 248777 := rs (se 2 (by rfl) ⟨93291, by rfl⟩) R186583
theorem R281789 : Reach 281789 := rs (se 3 (by rfl) ⟨52835, by rfl⟩) R105671
theorem R6181541 : Reach 6181541 := rs (se 4 (by rfl) ⟨579519, by rfl⟩) R1159039
theorem R86975 : Reach 86975 := rs (se 1 (by rfl) ⟨65231, by rfl⟩) R130463
theorem R546203 : Reach 546203 := rs (se 1 (by rfl) ⟨409652, by rfl⟩) R819305
theorem R54695 : Reach 54695 := rs (se 1 (by rfl) ⟨41021, by rfl⟩) R82043
theorem R55049 : Reach 55049 := rs (se 2 (by rfl) ⟨20643, by rfl⟩) R41287
theorem R55067 : Reach 55067 := rs (se 1 (by rfl) ⟨41300, by rfl⟩) R82601
theorem R87947 : Reach 87947 := rs (se 1 (by rfl) ⟨65960, by rfl⟩) R131921
theorem R186623 : Reach 186623 := rs (se 1 (by rfl) ⟨139967, by rfl⟩) R279935
theorem R55787 : Reach 55787 := rs (se 1 (by rfl) ⟨41840, by rfl⟩) R83681
theorem R57083 : Reach 57083 := rs (se 1 (by rfl) ⟨42812, by rfl⟩) R85625
theorem R155483 : Reach 155483 := rs (se 1 (by rfl) ⟨116612, by rfl⟩) R233225
theorem R189053 : Reach 189053 := rs (se 3 (by rfl) ⟨35447, by rfl⟩) R70895
theorem R92287 : Reach 92287 := rs (se 1 (by rfl) ⟨69215, by rfl⟩) R138431
theorem R60763 : Reach 60763 := rs (se 1 (by rfl) ⟨45572, by rfl⟩) R91145
theorem R2748239 : Reach 2748239 := rs (se 1 (by rfl) ⟨2061179, by rfl⟩) R4122359
theorem R3667805 : Reach 3667805 := rs (se 3 (by rfl) ⟨687713, by rfl⟩) R1375427
theorem R129707 : Reach 129707 := rs (se 1 (by rfl) ⟨97280, by rfl⟩) R194561
theorem R64489 : Reach 64489 := rs (se 2 (by rfl) ⟨24183, by rfl⟩) R48367
theorem R165851 : Reach 165851 := rs (se 1 (by rfl) ⟨124388, by rfl⟩) R248777
theorem R36463 : Reach 36463 := rs (se 1 (by rfl) ⟨27347, by rfl⟩) R54695
theorem R36699 : Reach 36699 := rs (se 1 (by rfl) ⟨27524, by rfl⟩) R55049
theorem R36711 : Reach 36711 := rs (se 1 (by rfl) ⟨27533, by rfl⟩) R55067
theorem R37191 : Reach 37191 := rs (se 1 (by rfl) ⟨27893, by rfl⟩) R55787
theorem R38055 : Reach 38055 := rs (se 1 (by rfl) ⟨28541, by rfl⟩) R57083
theorem R103655 : Reach 103655 := rs (se 1 (by rfl) ⟨77741, by rfl⟩) R155483
theorem R139603 : Reach 139603 := rs (se 1 (by rfl) ⟨104702, by rfl⟩) R209405
theorem R176039 : Reach 176039 := rs (se 1 (by rfl) ⟨132029, by rfl⟩) R264059
theorem R110945 : Reach 110945 := rs (se 2 (by rfl) ⟨41604, by rfl⟩) R83209
theorem R1456541 : Reach 1456541 := rs (se 3 (by rfl) ⟨273101, by rfl⟩) R546203
theorem R277357 : Reach 277357 := rs (se 3 (by rfl) ⟨52004, by rfl⟩) R104009
theorem R81017 : Reach 81017 := rs (se 2 (by rfl) ⟨30381, by rfl⟩) R60763
theorem R2445203 : Reach 2445203 := rs (se 1 (by rfl) ⟨1833902, by rfl⟩) R3667805
theorem R53159 : Reach 53159 := rs (se 1 (by rfl) ⟨39869, by rfl⟩) R79739
theorem R85985 : Reach 85985 := rs (se 2 (by rfl) ⟨32244, by rfl⟩) R64489
theorem R53471 : Reach 53471 := rs (se 1 (by rfl) ⟨40103, by rfl⟩) R80207
theorem R86471 : Reach 86471 := rs (se 1 (by rfl) ⟨64853, by rfl⟩) R129707
theorem R153535 : Reach 153535 := rs (se 1 (by rfl) ⟨115151, by rfl⟩) R230303
theorem R55775 : Reach 55775 := rs (se 1 (by rfl) ⟨41831, by rfl⟩) R83663
theorem R56393 : Reach 56393 := rs (se 2 (by rfl) ⟨21147, by rfl⟩) R42295
theorem R187859 : Reach 187859 := rs (se 1 (by rfl) ⟨140894, by rfl⟩) R281789
theorem R123049 : Reach 123049 := rs (se 2 (by rfl) ⟨46143, by rfl⟩) R92287
theorem R4121027 : Reach 4121027 := rs (se 1 (by rfl) ⟨3090770, by rfl⟩) R6181541
theorem R57983 : Reach 57983 := rs (se 1 (by rfl) ⟨43487, by rfl⟩) R86975
theorem R58361 : Reach 58361 := rs (se 2 (by rfl) ⟨21885, by rfl⟩) R43771
theorem R58631 : Reach 58631 := rs (se 1 (by rfl) ⟨43973, by rfl⟩) R87947
theorem R124415 : Reach 124415 := rs (se 1 (by rfl) ⟨93311, by rfl⟩) R186623
theorem R126035 : Reach 126035 := rs (se 1 (by rfl) ⟨94526, by rfl⟩) R189053
theorem R356447 : Reach 356447 := rs (se 1 (by rfl) ⟨267335, by rfl⟩) R534671
theorem R3044243 : Reach 3044243 := rs (se 1 (by rfl) ⟨2283182, by rfl⟩) R4566365
theorem R1832159 : Reach 1832159 := rs (se 1 (by rfl) ⟨1374119, by rfl⟩) R2748239
theorem R950525 : Reach 950525 := rs (se 3 (by rfl) ⟨178223, by rfl⟩) R356447
theorem R656261 : Reach 656261 := rs (se 4 (by rfl) ⟨61524, by rfl⟩) R123049
theorem R35439 : Reach 35439 := rs (se 1 (by rfl) ⟨26579, by rfl⟩) R53159
theorem R35647 : Reach 35647 := rs (se 1 (by rfl) ⟨26735, by rfl⟩) R53471
theorem R69103 : Reach 69103 := rs (se 1 (by rfl) ⟨51827, by rfl⟩) R103655
theorem R37183 : Reach 37183 := rs (se 1 (by rfl) ⟨27887, by rfl⟩) R55775
theorem R37595 : Reach 37595 := rs (se 1 (by rfl) ⟨28196, by rfl⟩) R56393
theorem R38655 : Reach 38655 := rs (se 1 (by rfl) ⟨28991, by rfl⟩) R57983
theorem R38907 : Reach 38907 := rs (se 1 (by rfl) ⟨29180, by rfl⟩) R58361
theorem R39087 : Reach 39087 := rs (se 1 (by rfl) ⟨29315, by rfl⟩) R58631
theorem R204713 : Reach 204713 := rs (se 2 (by rfl) ⟨76767, by rfl⟩) R153535
theorem R73963 : Reach 73963 := rs (se 1 (by rfl) ⟨55472, by rfl⟩) R110945
theorem R1221439 : Reach 1221439 := rs (se 1 (by rfl) ⟨916079, by rfl⟩) R1832159
theorem R369809 : Reach 369809 := rs (se 2 (by rfl) ⟨138678, by rfl⟩) R277357
theorem R110567 : Reach 110567 := rs (se 1 (by rfl) ⟨82925, by rfl⟩) R165851
theorem R82943 : Reach 82943 := rs (se 1 (by rfl) ⟨62207, by rfl⟩) R124415
theorem R84023 : Reach 84023 := rs (se 1 (by rfl) ⟨63017, by rfl⟩) R126035
theorem R117359 : Reach 117359 := rs (se 1 (by rfl) ⟨88019, by rfl⟩) R176039
theorem R971027 : Reach 971027 := rs (se 1 (by rfl) ⟨728270, by rfl⟩) R1456541
theorem R54011 : Reach 54011 := rs (se 1 (by rfl) ⟨40508, by rfl⟩) R81017
theorem R186137 : Reach 186137 := rs (se 2 (by rfl) ⟨69801, by rfl⟩) R139603
theorem R1630135 : Reach 1630135 := rs (se 1 (by rfl) ⟨1222601, by rfl⟩) R2445203
theorem R57323 : Reach 57323 := rs (se 1 (by rfl) ⟨42992, by rfl⟩) R85985
theorem R57647 : Reach 57647 := rs (se 1 (by rfl) ⟨43235, by rfl⟩) R86471
theorem R125239 : Reach 125239 := rs (se 1 (by rfl) ⟨93929, by rfl⟩) R187859
theorem R2747351 : Reach 2747351 := rs (se 1 (by rfl) ⟨2060513, by rfl⟩) R4121027
theorem R2029495 : Reach 2029495 := rs (se 1 (by rfl) ⟨1522121, by rfl⟩) R3044243
theorem R98617 : Reach 98617 := rs (se 2 (by rfl) ⟨36981, by rfl⟩) R73963
theorem R100253 : Reach 100253 := rs (se 3 (by rfl) ⟨18797, by rfl⟩) R37595
theorem R166985 : Reach 166985 := rs (se 2 (by rfl) ⟨62619, by rfl⟩) R125239
theorem R36007 : Reach 36007 := rs (se 1 (by rfl) ⟨27005, by rfl⟩) R54011
theorem R136475 : Reach 136475 := rs (se 1 (by rfl) ⟨102356, by rfl⟩) R204713
theorem R38215 : Reach 38215 := rs (se 1 (by rfl) ⟨28661, by rfl⟩) R57323
theorem R38431 : Reach 38431 := rs (se 1 (by rfl) ⟨28823, by rfl⟩) R57647
theorem R73711 : Reach 73711 := rs (se 1 (by rfl) ⟨55283, by rfl⟩) R110567
theorem R2173513 : Reach 2173513 := rs (se 2 (by rfl) ⟨815067, by rfl⟩) R1630135
theorem R633683 : Reach 633683 := rs (se 1 (by rfl) ⟨475262, by rfl⟩) R950525
theorem R437507 : Reach 437507 := rs (se 1 (by rfl) ⟨328130, by rfl⟩) R656261
theorem R78239 : Reach 78239 := rs (se 1 (by rfl) ⟨58679, by rfl⟩) R117359
theorem R246539 : Reach 246539 := rs (se 1 (by rfl) ⟨184904, by rfl⟩) R369809
theorem R2705993 : Reach 2705993 := rs (se 2 (by rfl) ⟨1014747, by rfl⟩) R2029495
theorem R55295 : Reach 55295 := rs (se 1 (by rfl) ⟨41471, by rfl⟩) R82943
theorem R1628585 : Reach 1628585 := rs (se 2 (by rfl) ⟨610719, by rfl⟩) R1221439
theorem R56015 : Reach 56015 := rs (se 1 (by rfl) ⟨42011, by rfl⟩) R84023
theorem R647351 : Reach 647351 := rs (se 1 (by rfl) ⟨485513, by rfl⟩) R971027
theorem R124091 : Reach 124091 := rs (se 1 (by rfl) ⟨93068, by rfl⟩) R186137
theorem R92137 : Reach 92137 := rs (se 2 (by rfl) ⟨34551, by rfl⟩) R69103
theorem R1831567 : Reach 1831567 := rs (se 1 (by rfl) ⟨1373675, by rfl⟩) R2747351
theorem R131489 : Reach 131489 := rs (se 2 (by rfl) ⟨49308, by rfl⟩) R98617
theorem R164359 : Reach 164359 := rs (se 1 (by rfl) ⟨123269, by rfl⟩) R246539
theorem R66835 : Reach 66835 := rs (se 1 (by rfl) ⟨50126, by rfl⟩) R100253
theorem R1803995 : Reach 1803995 := rs (se 1 (by rfl) ⟨1352996, by rfl⟩) R2705993
theorem R36863 : Reach 36863 := rs (se 1 (by rfl) ⟨27647, by rfl⟩) R55295
theorem R1085723 : Reach 1085723 := rs (se 1 (by rfl) ⟨814292, by rfl⟩) R1628585
theorem R37343 : Reach 37343 := rs (se 1 (by rfl) ⟨28007, by rfl⟩) R56015
theorem R431567 : Reach 431567 := rs (se 1 (by rfl) ⟨323675, by rfl⟩) R647351
theorem R111323 : Reach 111323 := rs (se 1 (by rfl) ⟨83492, by rfl⟩) R166985
theorem R2898017 : Reach 2898017 := rs (se 2 (by rfl) ⟨1086756, by rfl⟩) R2173513
theorem R82727 : Reach 82727 := rs (se 1 (by rfl) ⟨62045, by rfl⟩) R124091
theorem R2442089 : Reach 2442089 := rs (se 2 (by rfl) ⟨915783, by rfl⟩) R1831567
theorem R1689821 : Reach 1689821 := rs (se 3 (by rfl) ⟨316841, by rfl⟩) R633683
theorem R52159 : Reach 52159 := rs (se 1 (by rfl) ⟨39119, by rfl⟩) R78239
theorem R122849 : Reach 122849 := rs (se 2 (by rfl) ⟨46068, by rfl⟩) R92137
theorem R90983 : Reach 90983 := rs (se 1 (by rfl) ⟨68237, by rfl⟩) R136475
theorem R291671 : Reach 291671 := rs (se 1 (by rfl) ⟨218753, by rfl⟩) R437507
theorem R98281 : Reach 98281 := rs (se 2 (by rfl) ⟨36855, by rfl⟩) R73711
theorem R723815 : Reach 723815 := rs (se 1 (by rfl) ⟨542861, by rfl⟩) R1085723
theorem R69545 : Reach 69545 := rs (se 2 (by rfl) ⟨26079, by rfl⟩) R52159
theorem R74215 : Reach 74215 := rs (se 1 (by rfl) ⟨55661, by rfl⟩) R111323
theorem R1126547 : Reach 1126547 := rs (se 1 (by rfl) ⟨844910, by rfl⟩) R1689821
theorem R81899 : Reach 81899 := rs (se 1 (by rfl) ⟨61424, by rfl⟩) R122849
theorem R87659 : Reach 87659 := rs (se 1 (by rfl) ⟨65744, by rfl⟩) R131489
theorem R55151 : Reach 55151 := rs (se 1 (by rfl) ⟨41363, by rfl⟩) R82727
theorem R1628059 : Reach 1628059 := rs (se 1 (by rfl) ⟨1221044, by rfl⟩) R2442089
theorem R219145 : Reach 219145 := rs (se 2 (by rfl) ⟨82179, by rfl⟩) R164359
theorem R1202663 : Reach 1202663 := rs (se 1 (by rfl) ⟨901997, by rfl⟩) R1803995
theorem R89113 : Reach 89113 := rs (se 2 (by rfl) ⟨33417, by rfl⟩) R66835
theorem R287711 : Reach 287711 := rs (se 1 (by rfl) ⟨215783, by rfl⟩) R431567
theorem R60655 : Reach 60655 := rs (se 1 (by rfl) ⟨45491, by rfl⟩) R90983
theorem R194447 : Reach 194447 := rs (se 1 (by rfl) ⟨145835, by rfl⟩) R291671
theorem R1932011 : Reach 1932011 := rs (se 1 (by rfl) ⟨1449008, by rfl⟩) R2898017
theorem R131041 : Reach 131041 := rs (se 2 (by rfl) ⟨49140, by rfl⟩) R98281
theorem R395813 : Reach 395813 := rs (se 4 (by rfl) ⟨37107, by rfl⟩) R74215
theorem R36767 : Reach 36767 := rs (se 1 (by rfl) ⟨27575, by rfl⟩) R55151
theorem R2170745 : Reach 2170745 := rs (se 2 (by rfl) ⟨814029, by rfl⟩) R1628059
theorem R1288007 : Reach 1288007 := rs (se 1 (by rfl) ⟨966005, by rfl⟩) R1932011
theorem R174721 : Reach 174721 := rs (se 2 (by rfl) ⟨65520, by rfl⟩) R131041
theorem R46363 : Reach 46363 := rs (se 1 (by rfl) ⟨34772, by rfl⟩) R69545
theorem R80873 : Reach 80873 := rs (se 2 (by rfl) ⟨30327, by rfl⟩) R60655
theorem R801775 : Reach 801775 := rs (se 1 (by rfl) ⟨601331, by rfl⟩) R1202663
theorem R118817 : Reach 118817 := rs (se 2 (by rfl) ⟨44556, by rfl⟩) R89113
theorem R54599 : Reach 54599 := rs (se 1 (by rfl) ⟨40949, by rfl⟩) R81899
theorem R482543 : Reach 482543 := rs (se 1 (by rfl) ⟨361907, by rfl⟩) R723815
theorem R58439 : Reach 58439 := rs (se 1 (by rfl) ⟨43829, by rfl⟩) R87659
theorem R518525 : Reach 518525 := rs (se 3 (by rfl) ⟨97223, by rfl⟩) R194447
theorem R191807 : Reach 191807 := rs (se 1 (by rfl) ⟨143855, by rfl⟩) R287711
theorem R292193 : Reach 292193 := rs (se 2 (by rfl) ⟨109572, by rfl⟩) R219145
theorem R751031 : Reach 751031 := rs (se 1 (by rfl) ⟨563273, by rfl⟩) R1126547
theorem R232961 : Reach 232961 := rs (se 2 (by rfl) ⟨87360, by rfl⟩) R174721
theorem R36399 : Reach 36399 := rs (se 1 (by rfl) ⟨27299, by rfl⟩) R54599
theorem R1447163 : Reach 1447163 := rs (se 1 (by rfl) ⟨1085372, by rfl⟩) R2170745
theorem R38959 : Reach 38959 := rs (se 1 (by rfl) ⟨29219, by rfl⟩) R58439
theorem R858671 : Reach 858671 := rs (se 1 (by rfl) ⟨644003, by rfl⟩) R1288007
theorem R1055501 : Reach 1055501 := rs (se 3 (by rfl) ⟨197906, by rfl⟩) R395813
theorem R500687 : Reach 500687 := rs (se 1 (by rfl) ⟨375515, by rfl⟩) R751031
theorem R79211 : Reach 79211 := rs (se 1 (by rfl) ⟨59408, by rfl⟩) R118817
theorem R345683 : Reach 345683 := rs (se 1 (by rfl) ⟨259262, by rfl⟩) R518525
theorem R1069033 : Reach 1069033 := rs (se 2 (by rfl) ⟨400887, by rfl⟩) R801775
theorem R53915 : Reach 53915 := rs (se 1 (by rfl) ⟨40436, by rfl⟩) R80873
theorem R321695 : Reach 321695 := rs (se 1 (by rfl) ⟨241271, by rfl⟩) R482543
theorem R61817 : Reach 61817 := rs (se 2 (by rfl) ⟨23181, by rfl⟩) R46363
theorem R127871 : Reach 127871 := rs (se 1 (by rfl) ⟨95903, by rfl⟩) R191807
theorem R194795 : Reach 194795 := rs (se 1 (by rfl) ⟨146096, by rfl⟩) R292193
theorem R164845 : Reach 164845 := rs (se 3 (by rfl) ⟨30908, by rfl⟩) R61817
theorem R230455 : Reach 230455 := rs (se 1 (by rfl) ⟨172841, by rfl⟩) R345683
theorem R35943 : Reach 35943 := rs (se 1 (by rfl) ⟨26957, by rfl⟩) R53915
theorem R333791 : Reach 333791 := rs (se 1 (by rfl) ⟨250343, by rfl⟩) R500687
theorem R964775 : Reach 964775 := rs (se 1 (by rfl) ⟨723581, by rfl⟩) R1447163
theorem R572447 : Reach 572447 := rs (se 1 (by rfl) ⟨429335, by rfl⟩) R858671
theorem R703667 : Reach 703667 := rs (se 1 (by rfl) ⟨527750, by rfl⟩) R1055501
theorem R1425377 : Reach 1425377 := rs (se 2 (by rfl) ⟨534516, by rfl⟩) R1069033
theorem R214463 : Reach 214463 := rs (se 1 (by rfl) ⟨160847, by rfl⟩) R321695
theorem R85247 : Reach 85247 := rs (se 1 (by rfl) ⟨63935, by rfl⟩) R127871
theorem R52807 : Reach 52807 := rs (se 1 (by rfl) ⟨39605, by rfl⟩) R79211
theorem R621229 : Reach 621229 := rs (se 3 (by rfl) ⟨116480, by rfl⟩) R232961
theorem R129863 : Reach 129863 := rs (se 1 (by rfl) ⟨97397, by rfl⟩) R194795
theorem R70409 : Reach 70409 := rs (se 2 (by rfl) ⟨26403, by rfl⟩) R52807
theorem R828305 : Reach 828305 := rs (se 2 (by rfl) ⟨310614, by rfl⟩) R621229
theorem R469111 : Reach 469111 := rs (se 1 (by rfl) ⟨351833, by rfl⟩) R703667
theorem R142975 : Reach 142975 := rs (se 1 (by rfl) ⟨107231, by rfl⟩) R214463
theorem R307273 : Reach 307273 := rs (se 2 (by rfl) ⟨115227, by rfl⟩) R230455
theorem R643183 : Reach 643183 := rs (se 1 (by rfl) ⟨482387, by rfl⟩) R964775
theorem R86575 : Reach 86575 := rs (se 1 (by rfl) ⟨64931, by rfl⟩) R129863
theorem R381631 : Reach 381631 := rs (se 1 (by rfl) ⟨286223, by rfl⟩) R572447
theorem R219793 : Reach 219793 := rs (se 2 (by rfl) ⟨82422, by rfl⟩) R164845
theorem R56831 : Reach 56831 := rs (se 1 (by rfl) ⟨42623, by rfl⟩) R85247
theorem R222527 : Reach 222527 := rs (se 1 (by rfl) ⟨166895, by rfl⟩) R333791
theorem R3801005 : Reach 3801005 := rs (se 3 (by rfl) ⟨712688, by rfl⟩) R1425377
theorem R625481 : Reach 625481 := rs (se 2 (by rfl) ⟨234555, by rfl⟩) R469111
theorem R37887 : Reach 37887 := rs (se 1 (by rfl) ⟨28415, by rfl⟩) R56831
theorem R762533 : Reach 762533 := rs (se 4 (by rfl) ⟨71487, by rfl⟩) R142975
theorem R2534003 : Reach 2534003 := rs (se 1 (by rfl) ⟨1900502, by rfl⟩) R3801005
theorem R409697 : Reach 409697 := rs (se 2 (by rfl) ⟨153636, by rfl⟩) R307273
theorem R115433 : Reach 115433 := rs (se 2 (by rfl) ⟨43287, by rfl⟩) R86575
theorem R148351 : Reach 148351 := rs (se 1 (by rfl) ⟨111263, by rfl⟩) R222527
theorem R508841 : Reach 508841 := rs (se 2 (by rfl) ⟨190815, by rfl⟩) R381631
theorem R187757 : Reach 187757 := rs (se 3 (by rfl) ⟨35204, by rfl⟩) R70409
theorem R13721237 : Reach 13721237 := rs (se 6 (by rfl) ⟨321591, by rfl⟩) R643183
theorem R552203 : Reach 552203 := rs (se 1 (by rfl) ⟨414152, by rfl⟩) R828305
theorem R293057 : Reach 293057 := rs (se 2 (by rfl) ⟨109896, by rfl⟩) R219793
theorem R197801 : Reach 197801 := rs (se 2 (by rfl) ⟨74175, by rfl⟩) R148351
theorem R9147491 : Reach 9147491 := rs (se 1 (by rfl) ⟨6860618, by rfl⟩) R13721237
theorem R368135 : Reach 368135 := rs (se 1 (by rfl) ⟨276101, by rfl⟩) R552203
theorem R273131 : Reach 273131 := rs (se 1 (by rfl) ⟨204848, by rfl⟩) R409697
theorem R76955 : Reach 76955 := rs (se 1 (by rfl) ⟨57716, by rfl⟩) R115433
theorem R339227 : Reach 339227 := rs (se 1 (by rfl) ⟨254420, by rfl⟩) R508841
theorem R508355 : Reach 508355 := rs (se 1 (by rfl) ⟨381266, by rfl⟩) R762533
theorem R1689335 : Reach 1689335 := rs (se 1 (by rfl) ⟨1267001, by rfl⟩) R2534003
theorem R416987 : Reach 416987 := rs (se 1 (by rfl) ⟨312740, by rfl⟩) R625481
theorem R125171 : Reach 125171 := rs (se 1 (by rfl) ⟨93878, by rfl⟩) R187757
theorem R195371 : Reach 195371 := rs (se 1 (by rfl) ⟨146528, by rfl⟩) R293057
theorem R131867 : Reach 131867 := rs (se 1 (by rfl) ⟨98900, by rfl⟩) R197801
theorem R6098327 : Reach 6098327 := rs (se 1 (by rfl) ⟨4573745, by rfl⟩) R9147491
theorem R205213 : Reach 205213 := rs (se 3 (by rfl) ⟨38477, by rfl⟩) R76955
theorem R338903 : Reach 338903 := rs (se 1 (by rfl) ⟨254177, by rfl⟩) R508355
theorem R1126223 : Reach 1126223 := rs (se 1 (by rfl) ⟨844667, by rfl⟩) R1689335
theorem R277991 : Reach 277991 := rs (se 1 (by rfl) ⟨208493, by rfl⟩) R416987
theorem R245423 : Reach 245423 := rs (se 1 (by rfl) ⟨184067, by rfl⟩) R368135
theorem R83447 : Reach 83447 := rs (se 1 (by rfl) ⟨62585, by rfl⟩) R125171
theorem R182087 : Reach 182087 := rs (se 1 (by rfl) ⟨136565, by rfl⟩) R273131
theorem R226151 : Reach 226151 := rs (se 1 (by rfl) ⟨169613, by rfl⟩) R339227
theorem R130247 : Reach 130247 := rs (se 1 (by rfl) ⟨97685, by rfl⟩) R195371
theorem R4065551 : Reach 4065551 := rs (se 1 (by rfl) ⟨3049163, by rfl⟩) R6098327
theorem R273617 : Reach 273617 := rs (se 2 (by rfl) ⟨102606, by rfl⟩) R205213
theorem R150767 : Reach 150767 := rs (se 1 (by rfl) ⟨113075, by rfl⟩) R226151
theorem R86831 : Reach 86831 := rs (se 1 (by rfl) ⟨65123, by rfl⟩) R130247
theorem R185327 : Reach 185327 := rs (se 1 (by rfl) ⟨138995, by rfl⟩) R277991
theorem R87911 : Reach 87911 := rs (se 1 (by rfl) ⟨65933, by rfl⟩) R131867
theorem R55631 : Reach 55631 := rs (se 1 (by rfl) ⟨41723, by rfl⟩) R83447
theorem R121391 : Reach 121391 := rs (se 1 (by rfl) ⟨91043, by rfl⟩) R182087
theorem R225935 : Reach 225935 := rs (se 1 (by rfl) ⟨169451, by rfl⟩) R338903
theorem R750815 : Reach 750815 := rs (se 1 (by rfl) ⟨563111, by rfl⟩) R1126223
theorem R163615 : Reach 163615 := rs (se 1 (by rfl) ⟨122711, by rfl⟩) R245423
theorem R100511 : Reach 100511 := rs (se 1 (by rfl) ⟨75383, by rfl⟩) R150767
theorem R37087 : Reach 37087 := rs (se 1 (by rfl) ⟨27815, by rfl⟩) R55631
theorem R500543 : Reach 500543 := rs (se 1 (by rfl) ⟨375407, by rfl⟩) R750815
theorem R80927 : Reach 80927 := rs (se 1 (by rfl) ⟨60695, by rfl⟩) R121391
theorem R182411 : Reach 182411 := rs (se 1 (by rfl) ⟨136808, by rfl⟩) R273617
theorem R150623 : Reach 150623 := rs (se 1 (by rfl) ⟨112967, by rfl⟩) R225935
theorem R218153 : Reach 218153 := rs (se 2 (by rfl) ⟨81807, by rfl⟩) R163615
theorem R2710367 : Reach 2710367 := rs (se 1 (by rfl) ⟨2032775, by rfl⟩) R4065551
theorem R57887 : Reach 57887 := rs (se 1 (by rfl) ⟨43415, by rfl⟩) R86831
theorem R123551 : Reach 123551 := rs (se 1 (by rfl) ⟨92663, by rfl⟩) R185327
theorem R58607 : Reach 58607 := rs (se 1 (by rfl) ⟨43955, by rfl⟩) R87911
theorem R67007 : Reach 67007 := rs (se 1 (by rfl) ⟨50255, by rfl⟩) R100511
theorem R100415 : Reach 100415 := rs (se 1 (by rfl) ⟨75311, by rfl⟩) R150623
theorem R1806911 : Reach 1806911 := rs (se 1 (by rfl) ⟨1355183, by rfl⟩) R2710367
theorem R38591 : Reach 38591 := rs (se 1 (by rfl) ⟨28943, by rfl⟩) R57887
theorem R333695 : Reach 333695 := rs (se 1 (by rfl) ⟨250271, by rfl⟩) R500543
theorem R39071 : Reach 39071 := rs (se 1 (by rfl) ⟨29303, by rfl⟩) R58607
theorem R145435 : Reach 145435 := rs (se 1 (by rfl) ⟨109076, by rfl⟩) R218153
theorem R82367 : Reach 82367 := rs (se 1 (by rfl) ⟨61775, by rfl⟩) R123551
theorem R53951 : Reach 53951 := rs (se 1 (by rfl) ⟨40463, by rfl⟩) R80927
theorem R121607 : Reach 121607 := rs (se 1 (by rfl) ⟨91205, by rfl⟩) R182411
theorem R66943 : Reach 66943 := rs (se 1 (by rfl) ⟨50207, by rfl⟩) R100415
theorem R35967 : Reach 35967 := rs (se 1 (by rfl) ⟨26975, by rfl⟩) R53951
theorem R178685 : Reach 178685 := rs (se 3 (by rfl) ⟨33503, by rfl⟩) R67007
theorem R81071 : Reach 81071 := rs (se 1 (by rfl) ⟨60803, by rfl⟩) R121607
theorem R54911 : Reach 54911 := rs (se 1 (by rfl) ⟨41183, by rfl⟩) R82367
theorem R1204607 : Reach 1204607 := rs (se 1 (by rfl) ⟨903455, by rfl⟩) R1806911
theorem R222463 : Reach 222463 := rs (se 1 (by rfl) ⟨166847, by rfl⟩) R333695
theorem R193913 : Reach 193913 := rs (se 2 (by rfl) ⟨72717, by rfl⟩) R145435
theorem R296617 : Reach 296617 := rs (se 2 (by rfl) ⟨111231, by rfl⟩) R222463
theorem R36607 : Reach 36607 := rs (se 1 (by rfl) ⟨27455, by rfl⟩) R54911
theorem R803071 : Reach 803071 := rs (se 1 (by rfl) ⟨602303, by rfl⟩) R1204607
theorem R119123 : Reach 119123 := rs (se 1 (by rfl) ⟨89342, by rfl⟩) R178685
theorem R54047 : Reach 54047 := rs (se 1 (by rfl) ⟨40535, by rfl⟩) R81071
theorem R89257 : Reach 89257 := rs (se 2 (by rfl) ⟨33471, by rfl⟩) R66943
theorem R129275 : Reach 129275 := rs (se 1 (by rfl) ⟨96956, by rfl⟩) R193913
theorem R395489 : Reach 395489 := rs (se 2 (by rfl) ⟨148308, by rfl⟩) R296617
theorem R36031 : Reach 36031 := rs (se 1 (by rfl) ⟨27023, by rfl⟩) R54047
theorem R79415 : Reach 79415 := rs (se 1 (by rfl) ⟨59561, by rfl⟩) R119123
theorem R86183 : Reach 86183 := rs (se 1 (by rfl) ⟨64637, by rfl⟩) R129275
theorem R119009 : Reach 119009 := rs (se 2 (by rfl) ⟨44628, by rfl⟩) R89257
theorem R1070761 : Reach 1070761 := rs (se 2 (by rfl) ⟨401535, by rfl⟩) R803071
theorem R1054637 : Reach 1054637 := rs (se 3 (by rfl) ⟨197744, by rfl⟩) R395489
theorem R1427681 : Reach 1427681 := rs (se 2 (by rfl) ⟨535380, by rfl⟩) R1070761
theorem R52943 : Reach 52943 := rs (se 1 (by rfl) ⟨39707, by rfl⟩) R79415
theorem R317357 : Reach 317357 := rs (se 3 (by rfl) ⟨59504, by rfl⟩) R119009
theorem R57455 : Reach 57455 := rs (se 1 (by rfl) ⟨43091, by rfl⟩) R86183
theorem R951787 : Reach 951787 := rs (se 1 (by rfl) ⟨713840, by rfl⟩) R1427681
theorem R35295 : Reach 35295 := rs (se 1 (by rfl) ⟨26471, by rfl⟩) R52943
theorem R38303 : Reach 38303 := rs (se 1 (by rfl) ⟨28727, by rfl⟩) R57455
theorem R211571 : Reach 211571 := rs (se 1 (by rfl) ⟨158678, by rfl⟩) R317357
theorem R703091 : Reach 703091 := rs (se 1 (by rfl) ⟨527318, by rfl⟩) R1054637
theorem R1874909 : Reach 1874909 := rs (se 3 (by rfl) ⟨351545, by rfl⟩) R703091
theorem R141047 : Reach 141047 := rs (se 1 (by rfl) ⟨105785, by rfl⟩) R211571
theorem R1269049 : Reach 1269049 := rs (se 2 (by rfl) ⟨475893, by rfl⟩) R951787
theorem R1249939 : Reach 1249939 := rs (se 1 (by rfl) ⟨937454, by rfl⟩) R1874909
theorem R1692065 : Reach 1692065 := rs (se 2 (by rfl) ⟨634524, by rfl⟩) R1269049
theorem R94031 : Reach 94031 := rs (se 1 (by rfl) ⟨70523, by rfl⟩) R141047
theorem R1128043 : Reach 1128043 := rs (se 1 (by rfl) ⟨846032, by rfl⟩) R1692065
theorem R1666585 : Reach 1666585 := rs (se 2 (by rfl) ⟨624969, by rfl⟩) R1249939
theorem R62687 : Reach 62687 := rs (se 1 (by rfl) ⟨47015, by rfl⟩) R94031
theorem R41791 : Reach 41791 := rs (se 1 (by rfl) ⟨31343, by rfl⟩) R62687
theorem R2222113 : Reach 2222113 := rs (se 2 (by rfl) ⟨833292, by rfl⟩) R1666585
theorem R1504057 : Reach 1504057 := rs (se 2 (by rfl) ⟨564021, by rfl⟩) R1128043
theorem R2005409 : Reach 2005409 := rs (se 2 (by rfl) ⟨752028, by rfl⟩) R1504057
theorem R2962817 : Reach 2962817 := rs (se 2 (by rfl) ⟨1111056, by rfl⟩) R2222113
theorem R55721 : Reach 55721 := rs (se 2 (by rfl) ⟨20895, by rfl⟩) R41791
theorem R37147 : Reach 37147 := rs (se 1 (by rfl) ⟨27860, by rfl⟩) R55721
theorem R5347757 : Reach 5347757 := rs (se 3 (by rfl) ⟨1002704, by rfl⟩) R2005409
theorem R1975211 : Reach 1975211 := rs (se 1 (by rfl) ⟨1481408, by rfl⟩) R2962817
theorem R1316807 : Reach 1316807 := rs (se 1 (by rfl) ⟨987605, by rfl⟩) R1975211
theorem R3565171 : Reach 3565171 := rs (se 1 (by rfl) ⟨2673878, by rfl⟩) R5347757
theorem R4753561 : Reach 4753561 := rs (se 2 (by rfl) ⟨1782585, by rfl⟩) R3565171
theorem R877871 : Reach 877871 := rs (se 1 (by rfl) ⟨658403, by rfl⟩) R1316807
theorem R6338081 : Reach 6338081 := rs (se 2 (by rfl) ⟨2376780, by rfl⟩) R4753561
theorem R585247 : Reach 585247 := rs (se 1 (by rfl) ⟨438935, by rfl⟩) R877871
theorem R780329 : Reach 780329 := rs (se 2 (by rfl) ⟨292623, by rfl⟩) R585247
theorem R4225387 : Reach 4225387 := rs (se 1 (by rfl) ⟨3169040, by rfl⟩) R6338081
theorem R520219 : Reach 520219 := rs (se 1 (by rfl) ⟨390164, by rfl⟩) R780329
theorem R5633849 : Reach 5633849 := rs (se 2 (by rfl) ⟨2112693, by rfl⟩) R4225387
theorem R693625 : Reach 693625 := rs (se 2 (by rfl) ⟨260109, by rfl⟩) R520219
theorem R3755899 : Reach 3755899 := rs (se 1 (by rfl) ⟨2816924, by rfl⟩) R5633849
theorem R924833 : Reach 924833 := rs (se 2 (by rfl) ⟨346812, by rfl⟩) R693625
theorem R5007865 : Reach 5007865 := rs (se 2 (by rfl) ⟨1877949, by rfl⟩) R3755899
theorem R6677153 : Reach 6677153 := rs (se 2 (by rfl) ⟨2503932, by rfl⟩) R5007865
theorem R616555 : Reach 616555 := rs (se 1 (by rfl) ⟨462416, by rfl⟩) R924833
theorem R822073 : Reach 822073 := rs (se 2 (by rfl) ⟨308277, by rfl⟩) R616555
theorem R4451435 : Reach 4451435 := rs (se 1 (by rfl) ⟨3338576, by rfl⟩) R6677153
theorem R1096097 : Reach 1096097 := rs (se 2 (by rfl) ⟨411036, by rfl⟩) R822073
theorem R2967623 : Reach 2967623 := rs (se 1 (by rfl) ⟨2225717, by rfl⟩) R4451435
theorem R1978415 : Reach 1978415 := rs (se 1 (by rfl) ⟨1483811, by rfl⟩) R2967623
theorem R11691701 : Reach 11691701 := rs (se 5 (by rfl) ⟨548048, by rfl⟩) R1096097
theorem R1318943 : Reach 1318943 := rs (se 1 (by rfl) ⟨989207, by rfl⟩) R1978415
theorem R7794467 : Reach 7794467 := rs (se 1 (by rfl) ⟨5845850, by rfl⟩) R11691701
theorem R5196311 : Reach 5196311 := rs (se 1 (by rfl) ⟨3897233, by rfl⟩) R7794467
theorem R879295 : Reach 879295 := rs (se 1 (by rfl) ⟨659471, by rfl⟩) R1318943
theorem R3464207 : Reach 3464207 := rs (se 1 (by rfl) ⟨2598155, by rfl⟩) R5196311
theorem R1172393 : Reach 1172393 := rs (se 2 (by rfl) ⟨439647, by rfl⟩) R879295
theorem R2309471 : Reach 2309471 := rs (se 1 (by rfl) ⟨1732103, by rfl⟩) R3464207
theorem R781595 : Reach 781595 := rs (se 1 (by rfl) ⟨586196, by rfl⟩) R1172393
theorem R521063 : Reach 521063 := rs (se 1 (by rfl) ⟨390797, by rfl⟩) R781595
theorem R1539647 : Reach 1539647 := rs (se 1 (by rfl) ⟨1154735, by rfl⟩) R2309471
theorem R1026431 : Reach 1026431 := rs (se 1 (by rfl) ⟨769823, by rfl⟩) R1539647
theorem R347375 : Reach 347375 := rs (se 1 (by rfl) ⟨260531, by rfl⟩) R521063
theorem R231583 : Reach 231583 := rs (se 1 (by rfl) ⟨173687, by rfl⟩) R347375
theorem R684287 : Reach 684287 := rs (se 1 (by rfl) ⟨513215, by rfl⟩) R1026431
theorem R308777 : Reach 308777 := rs (se 2 (by rfl) ⟨115791, by rfl⟩) R231583
theorem R456191 : Reach 456191 := rs (se 1 (by rfl) ⟨342143, by rfl⟩) R684287
theorem R823405 : Reach 823405 := rs (se 3 (by rfl) ⟨154388, by rfl⟩) R308777
theorem R304127 : Reach 304127 := rs (se 1 (by rfl) ⟨228095, by rfl⟩) R456191
theorem R202751 : Reach 202751 := rs (se 1 (by rfl) ⟨152063, by rfl⟩) R304127
theorem R1097873 : Reach 1097873 := rs (se 2 (by rfl) ⟨411702, by rfl⟩) R823405
theorem R135167 : Reach 135167 := rs (se 1 (by rfl) ⟨101375, by rfl⟩) R202751
theorem R731915 : Reach 731915 := rs (se 1 (by rfl) ⟨548936, by rfl⟩) R1097873
theorem R487943 : Reach 487943 := rs (se 1 (by rfl) ⟨365957, by rfl⟩) R731915
theorem R360445 : Reach 360445 := rs (se 3 (by rfl) ⟨67583, by rfl⟩) R135167
theorem R480593 : Reach 480593 := rs (se 2 (by rfl) ⟨180222, by rfl⟩) R360445
theorem R325295 : Reach 325295 := rs (se 1 (by rfl) ⟨243971, by rfl⟩) R487943
theorem R216863 : Reach 216863 := rs (se 1 (by rfl) ⟨162647, by rfl⟩) R325295
theorem R320395 : Reach 320395 := rs (se 1 (by rfl) ⟨240296, by rfl⟩) R480593
theorem R427193 : Reach 427193 := rs (se 2 (by rfl) ⟨160197, by rfl⟩) R320395
theorem R144575 : Reach 144575 := rs (se 1 (by rfl) ⟨108431, by rfl⟩) R216863
theorem R284795 : Reach 284795 := rs (se 1 (by rfl) ⟨213596, by rfl⟩) R427193
theorem R96383 : Reach 96383 := rs (se 1 (by rfl) ⟨72287, by rfl⟩) R144575
theorem R189863 : Reach 189863 := rs (se 1 (by rfl) ⟨142397, by rfl⟩) R284795
theorem R64255 : Reach 64255 := rs (se 1 (by rfl) ⟨48191, by rfl⟩) R96383
theorem R85673 : Reach 85673 := rs (se 2 (by rfl) ⟨32127, by rfl⟩) R64255
theorem R126575 : Reach 126575 := rs (se 1 (by rfl) ⟨94931, by rfl⟩) R189863
theorem R84383 : Reach 84383 := rs (se 1 (by rfl) ⟨63287, by rfl⟩) R126575
theorem R57115 : Reach 57115 := rs (se 1 (by rfl) ⟨42836, by rfl⟩) R85673
theorem R76153 : Reach 76153 := rs (se 2 (by rfl) ⟨28557, by rfl⟩) R57115
theorem R56255 : Reach 56255 := rs (se 1 (by rfl) ⟨42191, by rfl⟩) R84383
theorem R101537 : Reach 101537 := rs (se 2 (by rfl) ⟨38076, by rfl⟩) R76153
theorem R37503 : Reach 37503 := rs (se 1 (by rfl) ⟨28127, by rfl⟩) R56255
theorem R67691 : Reach 67691 := rs (se 1 (by rfl) ⟨50768, by rfl⟩) R101537
theorem R45127 : Reach 45127 := rs (se 1 (by rfl) ⟨33845, by rfl⟩) R67691
theorem R60169 : Reach 60169 := rs (se 2 (by rfl) ⟨22563, by rfl⟩) R45127
theorem R80225 : Reach 80225 := rs (se 2 (by rfl) ⟨30084, by rfl⟩) R60169
theorem R53483 : Reach 53483 := rs (se 1 (by rfl) ⟨40112, by rfl⟩) R80225
theorem R35655 : Reach 35655 := rs (se 1 (by rfl) ⟨26741, by rfl⟩) R53483

theorem C0 (j : ℕ) (h1 : 17558 ≤ j) (h2 : j ≤ 18257) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R35117
  · exact R35119
  · exact R35121
  · exact R35123
  · exact R35125
  · exact R35127
  · exact R35129
  · exact R35131
  · exact R35133
  · exact R35135
  · exact R35137
  · exact R35139
  · exact R35141
  · exact R35143
  · exact R35145
  · exact R35147
  · exact R35149
  · exact R35151
  · exact R35153
  · exact R35155
  · exact R35157
  · exact R35159
  · exact R35161
  · exact R35163
  · exact R35165
  · exact R35167
  · exact R35169
  · exact R35171
  · exact R35173
  · exact R35175
  · exact R35177
  · exact R35179
  · exact R35181
  · exact R35183
  · exact R35185
  · exact R35187
  · exact R35189
  · exact R35191
  · exact R35193
  · exact R35195
  · exact R35197
  · exact R35199
  · exact R35201
  · exact R35203
  · exact R35205
  · exact R35207
  · exact R35209
  · exact R35211
  · exact R35213
  · exact R35215
  · exact R35217
  · exact R35219
  · exact R35221
  · exact R35223
  · exact R35225
  · exact R35227
  · exact R35229
  · exact R35231
  · exact R35233
  · exact R35235
  · exact R35237
  · exact R35239
  · exact R35241
  · exact R35243
  · exact R35245
  · exact R35247
  · exact R35249
  · exact R35251
  · exact R35253
  · exact R35255
  · exact R35257
  · exact R35259
  · exact R35261
  · exact R35263
  · exact R35265
  · exact R35267
  · exact R35269
  · exact R35271
  · exact R35273
  · exact R35275
  · exact R35277
  · exact R35279
  · exact R35281
  · exact R35283
  · exact R35285
  · exact R35287
  · exact R35289
  · exact R35291
  · exact R35293
  · exact R35295
  · exact R35297
  · exact R35299
  · exact R35301
  · exact R35303
  · exact R35305
  · exact R35307
  · exact R35309
  · exact R35311
  · exact R35313
  · exact R35315
  · exact R35317
  · exact R35319
  · exact R35321
  · exact R35323
  · exact R35325
  · exact R35327
  · exact R35329
  · exact R35331
  · exact R35333
  · exact R35335
  · exact R35337
  · exact R35339
  · exact R35341
  · exact R35343
  · exact R35345
  · exact R35347
  · exact R35349
  · exact R35351
  · exact R35353
  · exact R35355
  · exact R35357
  · exact R35359
  · exact R35361
  · exact R35363
  · exact R35365
  · exact R35367
  · exact R35369
  · exact R35371
  · exact R35373
  · exact R35375
  · exact R35377
  · exact R35379
  · exact R35381
  · exact R35383
  · exact R35385
  · exact R35387
  · exact R35389
  · exact R35391
  · exact R35393
  · exact R35395
  · exact R35397
  · exact R35399
  · exact R35401
  · exact R35403
  · exact R35405
  · exact R35407
  · exact R35409
  · exact R35411
  · exact R35413
  · exact R35415
  · exact R35417
  · exact R35419
  · exact R35421
  · exact R35423
  · exact R35425
  · exact R35427
  · exact R35429
  · exact R35431
  · exact R35433
  · exact R35435
  · exact R35437
  · exact R35439
  · exact R35441
  · exact R35443
  · exact R35445
  · exact R35447
  · exact R35449
  · exact R35451
  · exact R35453
  · exact R35455
  · exact R35457
  · exact R35459
  · exact R35461
  · exact R35463
  · exact R35465
  · exact R35467
  · exact R35469
  · exact R35471
  · exact R35473
  · exact R35475
  · exact R35477
  · exact R35479
  · exact R35481
  · exact R35483
  · exact R35485
  · exact R35487
  · exact R35489
  · exact R35491
  · exact R35493
  · exact R35495
  · exact R35497
  · exact R35499
  · exact R35501
  · exact R35503
  · exact R35505
  · exact R35507
  · exact R35509
  · exact R35511
  · exact R35513
  · exact R35515
  · exact R35517
  · exact R35519
  · exact R35521
  · exact R35523
  · exact R35525
  · exact R35527
  · exact R35529
  · exact R35531
  · exact R35533
  · exact R35535
  · exact R35537
  · exact R35539
  · exact R35541
  · exact R35543
  · exact R35545
  · exact R35547
  · exact R35549
  · exact R35551
  · exact R35553
  · exact R35555
  · exact R35557
  · exact R35559
  · exact R35561
  · exact R35563
  · exact R35565
  · exact R35567
  · exact R35569
  · exact R35571
  · exact R35573
  · exact R35575
  · exact R35577
  · exact R35579
  · exact R35581
  · exact R35583
  · exact R35585
  · exact R35587
  · exact R35589
  · exact R35591
  · exact R35593
  · exact R35595
  · exact R35597
  · exact R35599
  · exact R35601
  · exact R35603
  · exact R35605
  · exact R35607
  · exact R35609
  · exact R35611
  · exact R35613
  · exact R35615
  · exact R35617
  · exact R35619
  · exact R35621
  · exact R35623
  · exact R35625
  · exact R35627
  · exact R35629
  · exact R35631
  · exact R35633
  · exact R35635
  · exact R35637
  · exact R35639
  · exact R35641
  · exact R35643
  · exact R35645
  · exact R35647
  · exact R35649
  · exact R35651
  · exact R35653
  · exact R35655
  · exact R35657
  · exact R35659
  · exact R35661
  · exact R35663
  · exact R35665
  · exact R35667
  · exact R35669
  · exact R35671
  · exact R35673
  · exact R35675
  · exact R35677
  · exact R35679
  · exact R35681
  · exact R35683
  · exact R35685
  · exact R35687
  · exact R35689
  · exact R35691
  · exact R35693
  · exact R35695
  · exact R35697
  · exact R35699
  · exact R35701
  · exact R35703
  · exact R35705
  · exact R35707
  · exact R35709
  · exact R35711
  · exact R35713
  · exact R35715
  · exact R35717
  · exact R35719
  · exact R35721
  · exact R35723
  · exact R35725
  · exact R35727
  · exact R35729
  · exact R35731
  · exact R35733
  · exact R35735
  · exact R35737
  · exact R35739
  · exact R35741
  · exact R35743
  · exact R35745
  · exact R35747
  · exact R35749
  · exact R35751
  · exact R35753
  · exact R35755
  · exact R35757
  · exact R35759
  · exact R35761
  · exact R35763
  · exact R35765
  · exact R35767
  · exact R35769
  · exact R35771
  · exact R35773
  · exact R35775
  · exact R35777
  · exact R35779
  · exact R35781
  · exact R35783
  · exact R35785
  · exact R35787
  · exact R35789
  · exact R35791
  · exact R35793
  · exact R35795
  · exact R35797
  · exact R35799
  · exact R35801
  · exact R35803
  · exact R35805
  · exact R35807
  · exact R35809
  · exact R35811
  · exact R35813
  · exact R35815
  · exact R35817
  · exact R35819
  · exact R35821
  · exact R35823
  · exact R35825
  · exact R35827
  · exact R35829
  · exact R35831
  · exact R35833
  · exact R35835
  · exact R35837
  · exact R35839
  · exact R35841
  · exact R35843
  · exact R35845
  · exact R35847
  · exact R35849
  · exact R35851
  · exact R35853
  · exact R35855
  · exact R35857
  · exact R35859
  · exact R35861
  · exact R35863
  · exact R35865
  · exact R35867
  · exact R35869
  · exact R35871
  · exact R35873
  · exact R35875
  · exact R35877
  · exact R35879
  · exact R35881
  · exact R35883
  · exact R35885
  · exact R35887
  · exact R35889
  · exact R35891
  · exact R35893
  · exact R35895
  · exact R35897
  · exact R35899
  · exact R35901
  · exact R35903
  · exact R35905
  · exact R35907
  · exact R35909
  · exact R35911
  · exact R35913
  · exact R35915
  · exact R35917
  · exact R35919
  · exact R35921
  · exact R35923
  · exact R35925
  · exact R35927
  · exact R35929
  · exact R35931
  · exact R35933
  · exact R35935
  · exact R35937
  · exact R35939
  · exact R35941
  · exact R35943
  · exact R35945
  · exact R35947
  · exact R35949
  · exact R35951
  · exact R35953
  · exact R35955
  · exact R35957
  · exact R35959
  · exact R35961
  · exact R35963
  · exact R35965
  · exact R35967
  · exact R35969
  · exact R35971
  · exact R35973
  · exact R35975
  · exact R35977
  · exact R35979
  · exact R35981
  · exact R35983
  · exact R35985
  · exact R35987
  · exact R35989
  · exact R35991
  · exact R35993
  · exact R35995
  · exact R35997
  · exact R35999
  · exact R36001
  · exact R36003
  · exact R36005
  · exact R36007
  · exact R36009
  · exact R36011
  · exact R36013
  · exact R36015
  · exact R36017
  · exact R36019
  · exact R36021
  · exact R36023
  · exact R36025
  · exact R36027
  · exact R36029
  · exact R36031
  · exact R36033
  · exact R36035
  · exact R36037
  · exact R36039
  · exact R36041
  · exact R36043
  · exact R36045
  · exact R36047
  · exact R36049
  · exact R36051
  · exact R36053
  · exact R36055
  · exact R36057
  · exact R36059
  · exact R36061
  · exact R36063
  · exact R36065
  · exact R36067
  · exact R36069
  · exact R36071
  · exact R36073
  · exact R36075
  · exact R36077
  · exact R36079
  · exact R36081
  · exact R36083
  · exact R36085
  · exact R36087
  · exact R36089
  · exact R36091
  · exact R36093
  · exact R36095
  · exact R36097
  · exact R36099
  · exact R36101
  · exact R36103
  · exact R36105
  · exact R36107
  · exact R36109
  · exact R36111
  · exact R36113
  · exact R36115
  · exact R36117
  · exact R36119
  · exact R36121
  · exact R36123
  · exact R36125
  · exact R36127
  · exact R36129
  · exact R36131
  · exact R36133
  · exact R36135
  · exact R36137
  · exact R36139
  · exact R36141
  · exact R36143
  · exact R36145
  · exact R36147
  · exact R36149
  · exact R36151
  · exact R36153
  · exact R36155
  · exact R36157
  · exact R36159
  · exact R36161
  · exact R36163
  · exact R36165
  · exact R36167
  · exact R36169
  · exact R36171
  · exact R36173
  · exact R36175
  · exact R36177
  · exact R36179
  · exact R36181
  · exact R36183
  · exact R36185
  · exact R36187
  · exact R36189
  · exact R36191
  · exact R36193
  · exact R36195
  · exact R36197
  · exact R36199
  · exact R36201
  · exact R36203
  · exact R36205
  · exact R36207
  · exact R36209
  · exact R36211
  · exact R36213
  · exact R36215
  · exact R36217
  · exact R36219
  · exact R36221
  · exact R36223
  · exact R36225
  · exact R36227
  · exact R36229
  · exact R36231
  · exact R36233
  · exact R36235
  · exact R36237
  · exact R36239
  · exact R36241
  · exact R36243
  · exact R36245
  · exact R36247
  · exact R36249
  · exact R36251
  · exact R36253
  · exact R36255
  · exact R36257
  · exact R36259
  · exact R36261
  · exact R36263
  · exact R36265
  · exact R36267
  · exact R36269
  · exact R36271
  · exact R36273
  · exact R36275
  · exact R36277
  · exact R36279
  · exact R36281
  · exact R36283
  · exact R36285
  · exact R36287
  · exact R36289
  · exact R36291
  · exact R36293
  · exact R36295
  · exact R36297
  · exact R36299
  · exact R36301
  · exact R36303
  · exact R36305
  · exact R36307
  · exact R36309
  · exact R36311
  · exact R36313
  · exact R36315
  · exact R36317
  · exact R36319
  · exact R36321
  · exact R36323
  · exact R36325
  · exact R36327
  · exact R36329
  · exact R36331
  · exact R36333
  · exact R36335
  · exact R36337
  · exact R36339
  · exact R36341
  · exact R36343
  · exact R36345
  · exact R36347
  · exact R36349
  · exact R36351
  · exact R36353
  · exact R36355
  · exact R36357
  · exact R36359
  · exact R36361
  · exact R36363
  · exact R36365
  · exact R36367
  · exact R36369
  · exact R36371
  · exact R36373
  · exact R36375
  · exact R36377
  · exact R36379
  · exact R36381
  · exact R36383
  · exact R36385
  · exact R36387
  · exact R36389
  · exact R36391
  · exact R36393
  · exact R36395
  · exact R36397
  · exact R36399
  · exact R36401
  · exact R36403
  · exact R36405
  · exact R36407
  · exact R36409
  · exact R36411
  · exact R36413
  · exact R36415
  · exact R36417
  · exact R36419
  · exact R36421
  · exact R36423
  · exact R36425
  · exact R36427
  · exact R36429
  · exact R36431
  · exact R36433
  · exact R36435
  · exact R36437
  · exact R36439
  · exact R36441
  · exact R36443
  · exact R36445
  · exact R36447
  · exact R36449
  · exact R36451
  · exact R36453
  · exact R36455
  · exact R36457
  · exact R36459
  · exact R36461
  · exact R36463
  · exact R36465
  · exact R36467
  · exact R36469
  · exact R36471
  · exact R36473
  · exact R36475
  · exact R36477
  · exact R36479
  · exact R36481
  · exact R36483
  · exact R36485
  · exact R36487
  · exact R36489
  · exact R36491
  · exact R36493
  · exact R36495
  · exact R36497
  · exact R36499
  · exact R36501
  · exact R36503
  · exact R36505
  · exact R36507
  · exact R36509
  · exact R36511
  · exact R36513
  · exact R36515

theorem C1 (j : ℕ) (h1 : 18258 ≤ j) (h2 : j ≤ 18957) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R36517
  · exact R36519
  · exact R36521
  · exact R36523
  · exact R36525
  · exact R36527
  · exact R36529
  · exact R36531
  · exact R36533
  · exact R36535
  · exact R36537
  · exact R36539
  · exact R36541
  · exact R36543
  · exact R36545
  · exact R36547
  · exact R36549
  · exact R36551
  · exact R36553
  · exact R36555
  · exact R36557
  · exact R36559
  · exact R36561
  · exact R36563
  · exact R36565
  · exact R36567
  · exact R36569
  · exact R36571
  · exact R36573
  · exact R36575
  · exact R36577
  · exact R36579
  · exact R36581
  · exact R36583
  · exact R36585
  · exact R36587
  · exact R36589
  · exact R36591
  · exact R36593
  · exact R36595
  · exact R36597
  · exact R36599
  · exact R36601
  · exact R36603
  · exact R36605
  · exact R36607
  · exact R36609
  · exact R36611
  · exact R36613
  · exact R36615
  · exact R36617
  · exact R36619
  · exact R36621
  · exact R36623
  · exact R36625
  · exact R36627
  · exact R36629
  · exact R36631
  · exact R36633
  · exact R36635
  · exact R36637
  · exact R36639
  · exact R36641
  · exact R36643
  · exact R36645
  · exact R36647
  · exact R36649
  · exact R36651
  · exact R36653
  · exact R36655
  · exact R36657
  · exact R36659
  · exact R36661
  · exact R36663
  · exact R36665
  · exact R36667
  · exact R36669
  · exact R36671
  · exact R36673
  · exact R36675
  · exact R36677
  · exact R36679
  · exact R36681
  · exact R36683
  · exact R36685
  · exact R36687
  · exact R36689
  · exact R36691
  · exact R36693
  · exact R36695
  · exact R36697
  · exact R36699
  · exact R36701
  · exact R36703
  · exact R36705
  · exact R36707
  · exact R36709
  · exact R36711
  · exact R36713
  · exact R36715
  · exact R36717
  · exact R36719
  · exact R36721
  · exact R36723
  · exact R36725
  · exact R36727
  · exact R36729
  · exact R36731
  · exact R36733
  · exact R36735
  · exact R36737
  · exact R36739
  · exact R36741
  · exact R36743
  · exact R36745
  · exact R36747
  · exact R36749
  · exact R36751
  · exact R36753
  · exact R36755
  · exact R36757
  · exact R36759
  · exact R36761
  · exact R36763
  · exact R36765
  · exact R36767
  · exact R36769
  · exact R36771
  · exact R36773
  · exact R36775
  · exact R36777
  · exact R36779
  · exact R36781
  · exact R36783
  · exact R36785
  · exact R36787
  · exact R36789
  · exact R36791
  · exact R36793
  · exact R36795
  · exact R36797
  · exact R36799
  · exact R36801
  · exact R36803
  · exact R36805
  · exact R36807
  · exact R36809
  · exact R36811
  · exact R36813
  · exact R36815
  · exact R36817
  · exact R36819
  · exact R36821
  · exact R36823
  · exact R36825
  · exact R36827
  · exact R36829
  · exact R36831
  · exact R36833
  · exact R36835
  · exact R36837
  · exact R36839
  · exact R36841
  · exact R36843
  · exact R36845
  · exact R36847
  · exact R36849
  · exact R36851
  · exact R36853
  · exact R36855
  · exact R36857
  · exact R36859
  · exact R36861
  · exact R36863
  · exact R36865
  · exact R36867
  · exact R36869
  · exact R36871
  · exact R36873
  · exact R36875
  · exact R36877
  · exact R36879
  · exact R36881
  · exact R36883
  · exact R36885
  · exact R36887
  · exact R36889
  · exact R36891
  · exact R36893
  · exact R36895
  · exact R36897
  · exact R36899
  · exact R36901
  · exact R36903
  · exact R36905
  · exact R36907
  · exact R36909
  · exact R36911
  · exact R36913
  · exact R36915
  · exact R36917
  · exact R36919
  · exact R36921
  · exact R36923
  · exact R36925
  · exact R36927
  · exact R36929
  · exact R36931
  · exact R36933
  · exact R36935
  · exact R36937
  · exact R36939
  · exact R36941
  · exact R36943
  · exact R36945
  · exact R36947
  · exact R36949
  · exact R36951
  · exact R36953
  · exact R36955
  · exact R36957
  · exact R36959
  · exact R36961
  · exact R36963
  · exact R36965
  · exact R36967
  · exact R36969
  · exact R36971
  · exact R36973
  · exact R36975
  · exact R36977
  · exact R36979
  · exact R36981
  · exact R36983
  · exact R36985
  · exact R36987
  · exact R36989
  · exact R36991
  · exact R36993
  · exact R36995
  · exact R36997
  · exact R36999
  · exact R37001
  · exact R37003
  · exact R37005
  · exact R37007
  · exact R37009
  · exact R37011
  · exact R37013
  · exact R37015
  · exact R37017
  · exact R37019
  · exact R37021
  · exact R37023
  · exact R37025
  · exact R37027
  · exact R37029
  · exact R37031
  · exact R37033
  · exact R37035
  · exact R37037
  · exact R37039
  · exact R37041
  · exact R37043
  · exact R37045
  · exact R37047
  · exact R37049
  · exact R37051
  · exact R37053
  · exact R37055
  · exact R37057
  · exact R37059
  · exact R37061
  · exact R37063
  · exact R37065
  · exact R37067
  · exact R37069
  · exact R37071
  · exact R37073
  · exact R37075
  · exact R37077
  · exact R37079
  · exact R37081
  · exact R37083
  · exact R37085
  · exact R37087
  · exact R37089
  · exact R37091
  · exact R37093
  · exact R37095
  · exact R37097
  · exact R37099
  · exact R37101
  · exact R37103
  · exact R37105
  · exact R37107
  · exact R37109
  · exact R37111
  · exact R37113
  · exact R37115
  · exact R37117
  · exact R37119
  · exact R37121
  · exact R37123
  · exact R37125
  · exact R37127
  · exact R37129
  · exact R37131
  · exact R37133
  · exact R37135
  · exact R37137
  · exact R37139
  · exact R37141
  · exact R37143
  · exact R37145
  · exact R37147
  · exact R37149
  · exact R37151
  · exact R37153
  · exact R37155
  · exact R37157
  · exact R37159
  · exact R37161
  · exact R37163
  · exact R37165
  · exact R37167
  · exact R37169
  · exact R37171
  · exact R37173
  · exact R37175
  · exact R37177
  · exact R37179
  · exact R37181
  · exact R37183
  · exact R37185
  · exact R37187
  · exact R37189
  · exact R37191
  · exact R37193
  · exact R37195
  · exact R37197
  · exact R37199
  · exact R37201
  · exact R37203
  · exact R37205
  · exact R37207
  · exact R37209
  · exact R37211
  · exact R37213
  · exact R37215
  · exact R37217
  · exact R37219
  · exact R37221
  · exact R37223
  · exact R37225
  · exact R37227
  · exact R37229
  · exact R37231
  · exact R37233
  · exact R37235
  · exact R37237
  · exact R37239
  · exact R37241
  · exact R37243
  · exact R37245
  · exact R37247
  · exact R37249
  · exact R37251
  · exact R37253
  · exact R37255
  · exact R37257
  · exact R37259
  · exact R37261
  · exact R37263
  · exact R37265
  · exact R37267
  · exact R37269
  · exact R37271
  · exact R37273
  · exact R37275
  · exact R37277
  · exact R37279
  · exact R37281
  · exact R37283
  · exact R37285
  · exact R37287
  · exact R37289
  · exact R37291
  · exact R37293
  · exact R37295
  · exact R37297
  · exact R37299
  · exact R37301
  · exact R37303
  · exact R37305
  · exact R37307
  · exact R37309
  · exact R37311
  · exact R37313
  · exact R37315
  · exact R37317
  · exact R37319
  · exact R37321
  · exact R37323
  · exact R37325
  · exact R37327
  · exact R37329
  · exact R37331
  · exact R37333
  · exact R37335
  · exact R37337
  · exact R37339
  · exact R37341
  · exact R37343
  · exact R37345
  · exact R37347
  · exact R37349
  · exact R37351
  · exact R37353
  · exact R37355
  · exact R37357
  · exact R37359
  · exact R37361
  · exact R37363
  · exact R37365
  · exact R37367
  · exact R37369
  · exact R37371
  · exact R37373
  · exact R37375
  · exact R37377
  · exact R37379
  · exact R37381
  · exact R37383
  · exact R37385
  · exact R37387
  · exact R37389
  · exact R37391
  · exact R37393
  · exact R37395
  · exact R37397
  · exact R37399
  · exact R37401
  · exact R37403
  · exact R37405
  · exact R37407
  · exact R37409
  · exact R37411
  · exact R37413
  · exact R37415
  · exact R37417
  · exact R37419
  · exact R37421
  · exact R37423
  · exact R37425
  · exact R37427
  · exact R37429
  · exact R37431
  · exact R37433
  · exact R37435
  · exact R37437
  · exact R37439
  · exact R37441
  · exact R37443
  · exact R37445
  · exact R37447
  · exact R37449
  · exact R37451
  · exact R37453
  · exact R37455
  · exact R37457
  · exact R37459
  · exact R37461
  · exact R37463
  · exact R37465
  · exact R37467
  · exact R37469
  · exact R37471
  · exact R37473
  · exact R37475
  · exact R37477
  · exact R37479
  · exact R37481
  · exact R37483
  · exact R37485
  · exact R37487
  · exact R37489
  · exact R37491
  · exact R37493
  · exact R37495
  · exact R37497
  · exact R37499
  · exact R37501
  · exact R37503
  · exact R37505
  · exact R37507
  · exact R37509
  · exact R37511
  · exact R37513
  · exact R37515
  · exact R37517
  · exact R37519
  · exact R37521
  · exact R37523
  · exact R37525
  · exact R37527
  · exact R37529
  · exact R37531
  · exact R37533
  · exact R37535
  · exact R37537
  · exact R37539
  · exact R37541
  · exact R37543
  · exact R37545
  · exact R37547
  · exact R37549
  · exact R37551
  · exact R37553
  · exact R37555
  · exact R37557
  · exact R37559
  · exact R37561
  · exact R37563
  · exact R37565
  · exact R37567
  · exact R37569
  · exact R37571
  · exact R37573
  · exact R37575
  · exact R37577
  · exact R37579
  · exact R37581
  · exact R37583
  · exact R37585
  · exact R37587
  · exact R37589
  · exact R37591
  · exact R37593
  · exact R37595
  · exact R37597
  · exact R37599
  · exact R37601
  · exact R37603
  · exact R37605
  · exact R37607
  · exact R37609
  · exact R37611
  · exact R37613
  · exact R37615
  · exact R37617
  · exact R37619
  · exact R37621
  · exact R37623
  · exact R37625
  · exact R37627
  · exact R37629
  · exact R37631
  · exact R37633
  · exact R37635
  · exact R37637
  · exact R37639
  · exact R37641
  · exact R37643
  · exact R37645
  · exact R37647
  · exact R37649
  · exact R37651
  · exact R37653
  · exact R37655
  · exact R37657
  · exact R37659
  · exact R37661
  · exact R37663
  · exact R37665
  · exact R37667
  · exact R37669
  · exact R37671
  · exact R37673
  · exact R37675
  · exact R37677
  · exact R37679
  · exact R37681
  · exact R37683
  · exact R37685
  · exact R37687
  · exact R37689
  · exact R37691
  · exact R37693
  · exact R37695
  · exact R37697
  · exact R37699
  · exact R37701
  · exact R37703
  · exact R37705
  · exact R37707
  · exact R37709
  · exact R37711
  · exact R37713
  · exact R37715
  · exact R37717
  · exact R37719
  · exact R37721
  · exact R37723
  · exact R37725
  · exact R37727
  · exact R37729
  · exact R37731
  · exact R37733
  · exact R37735
  · exact R37737
  · exact R37739
  · exact R37741
  · exact R37743
  · exact R37745
  · exact R37747
  · exact R37749
  · exact R37751
  · exact R37753
  · exact R37755
  · exact R37757
  · exact R37759
  · exact R37761
  · exact R37763
  · exact R37765
  · exact R37767
  · exact R37769
  · exact R37771
  · exact R37773
  · exact R37775
  · exact R37777
  · exact R37779
  · exact R37781
  · exact R37783
  · exact R37785
  · exact R37787
  · exact R37789
  · exact R37791
  · exact R37793
  · exact R37795
  · exact R37797
  · exact R37799
  · exact R37801
  · exact R37803
  · exact R37805
  · exact R37807
  · exact R37809
  · exact R37811
  · exact R37813
  · exact R37815
  · exact R37817
  · exact R37819
  · exact R37821
  · exact R37823
  · exact R37825
  · exact R37827
  · exact R37829
  · exact R37831
  · exact R37833
  · exact R37835
  · exact R37837
  · exact R37839
  · exact R37841
  · exact R37843
  · exact R37845
  · exact R37847
  · exact R37849
  · exact R37851
  · exact R37853
  · exact R37855
  · exact R37857
  · exact R37859
  · exact R37861
  · exact R37863
  · exact R37865
  · exact R37867
  · exact R37869
  · exact R37871
  · exact R37873
  · exact R37875
  · exact R37877
  · exact R37879
  · exact R37881
  · exact R37883
  · exact R37885
  · exact R37887
  · exact R37889
  · exact R37891
  · exact R37893
  · exact R37895
  · exact R37897
  · exact R37899
  · exact R37901
  · exact R37903
  · exact R37905
  · exact R37907
  · exact R37909
  · exact R37911
  · exact R37913
  · exact R37915

theorem C2 (j : ℕ) (h1 : 18958 ≤ j) (h2 : j ≤ 19557) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R37917
  · exact R37919
  · exact R37921
  · exact R37923
  · exact R37925
  · exact R37927
  · exact R37929
  · exact R37931
  · exact R37933
  · exact R37935
  · exact R37937
  · exact R37939
  · exact R37941
  · exact R37943
  · exact R37945
  · exact R37947
  · exact R37949
  · exact R37951
  · exact R37953
  · exact R37955
  · exact R37957
  · exact R37959
  · exact R37961
  · exact R37963
  · exact R37965
  · exact R37967
  · exact R37969
  · exact R37971
  · exact R37973
  · exact R37975
  · exact R37977
  · exact R37979
  · exact R37981
  · exact R37983
  · exact R37985
  · exact R37987
  · exact R37989
  · exact R37991
  · exact R37993
  · exact R37995
  · exact R37997
  · exact R37999
  · exact R38001
  · exact R38003
  · exact R38005
  · exact R38007
  · exact R38009
  · exact R38011
  · exact R38013
  · exact R38015
  · exact R38017
  · exact R38019
  · exact R38021
  · exact R38023
  · exact R38025
  · exact R38027
  · exact R38029
  · exact R38031
  · exact R38033
  · exact R38035
  · exact R38037
  · exact R38039
  · exact R38041
  · exact R38043
  · exact R38045
  · exact R38047
  · exact R38049
  · exact R38051
  · exact R38053
  · exact R38055
  · exact R38057
  · exact R38059
  · exact R38061
  · exact R38063
  · exact R38065
  · exact R38067
  · exact R38069
  · exact R38071
  · exact R38073
  · exact R38075
  · exact R38077
  · exact R38079
  · exact R38081
  · exact R38083
  · exact R38085
  · exact R38087
  · exact R38089
  · exact R38091
  · exact R38093
  · exact R38095
  · exact R38097
  · exact R38099
  · exact R38101
  · exact R38103
  · exact R38105
  · exact R38107
  · exact R38109
  · exact R38111
  · exact R38113
  · exact R38115
  · exact R38117
  · exact R38119
  · exact R38121
  · exact R38123
  · exact R38125
  · exact R38127
  · exact R38129
  · exact R38131
  · exact R38133
  · exact R38135
  · exact R38137
  · exact R38139
  · exact R38141
  · exact R38143
  · exact R38145
  · exact R38147
  · exact R38149
  · exact R38151
  · exact R38153
  · exact R38155
  · exact R38157
  · exact R38159
  · exact R38161
  · exact R38163
  · exact R38165
  · exact R38167
  · exact R38169
  · exact R38171
  · exact R38173
  · exact R38175
  · exact R38177
  · exact R38179
  · exact R38181
  · exact R38183
  · exact R38185
  · exact R38187
  · exact R38189
  · exact R38191
  · exact R38193
  · exact R38195
  · exact R38197
  · exact R38199
  · exact R38201
  · exact R38203
  · exact R38205
  · exact R38207
  · exact R38209
  · exact R38211
  · exact R38213
  · exact R38215
  · exact R38217
  · exact R38219
  · exact R38221
  · exact R38223
  · exact R38225
  · exact R38227
  · exact R38229
  · exact R38231
  · exact R38233
  · exact R38235
  · exact R38237
  · exact R38239
  · exact R38241
  · exact R38243
  · exact R38245
  · exact R38247
  · exact R38249
  · exact R38251
  · exact R38253
  · exact R38255
  · exact R38257
  · exact R38259
  · exact R38261
  · exact R38263
  · exact R38265
  · exact R38267
  · exact R38269
  · exact R38271
  · exact R38273
  · exact R38275
  · exact R38277
  · exact R38279
  · exact R38281
  · exact R38283
  · exact R38285
  · exact R38287
  · exact R38289
  · exact R38291
  · exact R38293
  · exact R38295
  · exact R38297
  · exact R38299
  · exact R38301
  · exact R38303
  · exact R38305
  · exact R38307
  · exact R38309
  · exact R38311
  · exact R38313
  · exact R38315
  · exact R38317
  · exact R38319
  · exact R38321
  · exact R38323
  · exact R38325
  · exact R38327
  · exact R38329
  · exact R38331
  · exact R38333
  · exact R38335
  · exact R38337
  · exact R38339
  · exact R38341
  · exact R38343
  · exact R38345
  · exact R38347
  · exact R38349
  · exact R38351
  · exact R38353
  · exact R38355
  · exact R38357
  · exact R38359
  · exact R38361
  · exact R38363
  · exact R38365
  · exact R38367
  · exact R38369
  · exact R38371
  · exact R38373
  · exact R38375
  · exact R38377
  · exact R38379
  · exact R38381
  · exact R38383
  · exact R38385
  · exact R38387
  · exact R38389
  · exact R38391
  · exact R38393
  · exact R38395
  · exact R38397
  · exact R38399
  · exact R38401
  · exact R38403
  · exact R38405
  · exact R38407
  · exact R38409
  · exact R38411
  · exact R38413
  · exact R38415
  · exact R38417
  · exact R38419
  · exact R38421
  · exact R38423
  · exact R38425
  · exact R38427
  · exact R38429
  · exact R38431
  · exact R38433
  · exact R38435
  · exact R38437
  · exact R38439
  · exact R38441
  · exact R38443
  · exact R38445
  · exact R38447
  · exact R38449
  · exact R38451
  · exact R38453
  · exact R38455
  · exact R38457
  · exact R38459
  · exact R38461
  · exact R38463
  · exact R38465
  · exact R38467
  · exact R38469
  · exact R38471
  · exact R38473
  · exact R38475
  · exact R38477
  · exact R38479
  · exact R38481
  · exact R38483
  · exact R38485
  · exact R38487
  · exact R38489
  · exact R38491
  · exact R38493
  · exact R38495
  · exact R38497
  · exact R38499
  · exact R38501
  · exact R38503
  · exact R38505
  · exact R38507
  · exact R38509
  · exact R38511
  · exact R38513
  · exact R38515
  · exact R38517
  · exact R38519
  · exact R38521
  · exact R38523
  · exact R38525
  · exact R38527
  · exact R38529
  · exact R38531
  · exact R38533
  · exact R38535
  · exact R38537
  · exact R38539
  · exact R38541
  · exact R38543
  · exact R38545
  · exact R38547
  · exact R38549
  · exact R38551
  · exact R38553
  · exact R38555
  · exact R38557
  · exact R38559
  · exact R38561
  · exact R38563
  · exact R38565
  · exact R38567
  · exact R38569
  · exact R38571
  · exact R38573
  · exact R38575
  · exact R38577
  · exact R38579
  · exact R38581
  · exact R38583
  · exact R38585
  · exact R38587
  · exact R38589
  · exact R38591
  · exact R38593
  · exact R38595
  · exact R38597
  · exact R38599
  · exact R38601
  · exact R38603
  · exact R38605
  · exact R38607
  · exact R38609
  · exact R38611
  · exact R38613
  · exact R38615
  · exact R38617
  · exact R38619
  · exact R38621
  · exact R38623
  · exact R38625
  · exact R38627
  · exact R38629
  · exact R38631
  · exact R38633
  · exact R38635
  · exact R38637
  · exact R38639
  · exact R38641
  · exact R38643
  · exact R38645
  · exact R38647
  · exact R38649
  · exact R38651
  · exact R38653
  · exact R38655
  · exact R38657
  · exact R38659
  · exact R38661
  · exact R38663
  · exact R38665
  · exact R38667
  · exact R38669
  · exact R38671
  · exact R38673
  · exact R38675
  · exact R38677
  · exact R38679
  · exact R38681
  · exact R38683
  · exact R38685
  · exact R38687
  · exact R38689
  · exact R38691
  · exact R38693
  · exact R38695
  · exact R38697
  · exact R38699
  · exact R38701
  · exact R38703
  · exact R38705
  · exact R38707
  · exact R38709
  · exact R38711
  · exact R38713
  · exact R38715
  · exact R38717
  · exact R38719
  · exact R38721
  · exact R38723
  · exact R38725
  · exact R38727
  · exact R38729
  · exact R38731
  · exact R38733
  · exact R38735
  · exact R38737
  · exact R38739
  · exact R38741
  · exact R38743
  · exact R38745
  · exact R38747
  · exact R38749
  · exact R38751
  · exact R38753
  · exact R38755
  · exact R38757
  · exact R38759
  · exact R38761
  · exact R38763
  · exact R38765
  · exact R38767
  · exact R38769
  · exact R38771
  · exact R38773
  · exact R38775
  · exact R38777
  · exact R38779
  · exact R38781
  · exact R38783
  · exact R38785
  · exact R38787
  · exact R38789
  · exact R38791
  · exact R38793
  · exact R38795
  · exact R38797
  · exact R38799
  · exact R38801
  · exact R38803
  · exact R38805
  · exact R38807
  · exact R38809
  · exact R38811
  · exact R38813
  · exact R38815
  · exact R38817
  · exact R38819
  · exact R38821
  · exact R38823
  · exact R38825
  · exact R38827
  · exact R38829
  · exact R38831
  · exact R38833
  · exact R38835
  · exact R38837
  · exact R38839
  · exact R38841
  · exact R38843
  · exact R38845
  · exact R38847
  · exact R38849
  · exact R38851
  · exact R38853
  · exact R38855
  · exact R38857
  · exact R38859
  · exact R38861
  · exact R38863
  · exact R38865
  · exact R38867
  · exact R38869
  · exact R38871
  · exact R38873
  · exact R38875
  · exact R38877
  · exact R38879
  · exact R38881
  · exact R38883
  · exact R38885
  · exact R38887
  · exact R38889
  · exact R38891
  · exact R38893
  · exact R38895
  · exact R38897
  · exact R38899
  · exact R38901
  · exact R38903
  · exact R38905
  · exact R38907
  · exact R38909
  · exact R38911
  · exact R38913
  · exact R38915
  · exact R38917
  · exact R38919
  · exact R38921
  · exact R38923
  · exact R38925
  · exact R38927
  · exact R38929
  · exact R38931
  · exact R38933
  · exact R38935
  · exact R38937
  · exact R38939
  · exact R38941
  · exact R38943
  · exact R38945
  · exact R38947
  · exact R38949
  · exact R38951
  · exact R38953
  · exact R38955
  · exact R38957
  · exact R38959
  · exact R38961
  · exact R38963
  · exact R38965
  · exact R38967
  · exact R38969
  · exact R38971
  · exact R38973
  · exact R38975
  · exact R38977
  · exact R38979
  · exact R38981
  · exact R38983
  · exact R38985
  · exact R38987
  · exact R38989
  · exact R38991
  · exact R38993
  · exact R38995
  · exact R38997
  · exact R38999
  · exact R39001
  · exact R39003
  · exact R39005
  · exact R39007
  · exact R39009
  · exact R39011
  · exact R39013
  · exact R39015
  · exact R39017
  · exact R39019
  · exact R39021
  · exact R39023
  · exact R39025
  · exact R39027
  · exact R39029
  · exact R39031
  · exact R39033
  · exact R39035
  · exact R39037
  · exact R39039
  · exact R39041
  · exact R39043
  · exact R39045
  · exact R39047
  · exact R39049
  · exact R39051
  · exact R39053
  · exact R39055
  · exact R39057
  · exact R39059
  · exact R39061
  · exact R39063
  · exact R39065
  · exact R39067
  · exact R39069
  · exact R39071
  · exact R39073
  · exact R39075
  · exact R39077
  · exact R39079
  · exact R39081
  · exact R39083
  · exact R39085
  · exact R39087
  · exact R39089
  · exact R39091
  · exact R39093
  · exact R39095
  · exact R39097
  · exact R39099
  · exact R39101
  · exact R39103
  · exact R39105
  · exact R39107
  · exact R39109
  · exact R39111
  · exact R39113
  · exact R39115

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 39116) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 35116 with hlo | hlo
  · exact syracuse_reaches_one_below_35116 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 18258 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 18958 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
