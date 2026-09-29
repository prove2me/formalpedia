-- Prove2me | solution 1 for syracuse_reaches_one_below_71125
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T06:18:07.404918+00:00
-- url     : https://prove2.me/submissions/4849f358-59eb-4fdf-b682-09fc8e1ddaf6

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_67124

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 67123) : Reach n :=
  syracuse_reaches_one_below_67124 n h1 h2 h3
theorem R163885 : Reach 163885 := rs (se 3 (by rfl) ⟨30728, by rfl⟩) (B 61457 (by norm_num) ⟨30728, by rfl⟩ (by norm_num))
theorem R229445 : Reach 229445 := rs (se 4 (by rfl) ⟨21510, by rfl⟩) (B 43021 (by norm_num) ⟨21510, by rfl⟩ (by norm_num))
theorem R98381 : Reach 98381 := rs (se 3 (by rfl) ⟨18446, by rfl⟩) (B 36893 (by norm_num) ⟨18446, by rfl⟩ (by norm_num))
theorem R131213 : Reach 131213 := rs (se 3 (by rfl) ⟨24602, by rfl⟩) (B 49205 (by norm_num) ⟨24602, by rfl⟩ (by norm_num))
theorem R327845 : Reach 327845 := rs (se 4 (by rfl) ⟨30735, by rfl⟩) (B 61471 (by norm_num) ⟨30735, by rfl⟩ (by norm_num))
theorem R295109 : Reach 295109 := rs (se 4 (by rfl) ⟨27666, by rfl⟩) (B 55333 (by norm_num) ⟨27666, by rfl⟩ (by norm_num))
theorem R131357 : Reach 131357 := rs (se 3 (by rfl) ⟨24629, by rfl⟩) (B 49259 (by norm_num) ⟨24629, by rfl⟩ (by norm_num))
theorem R197093 : Reach 197093 := rs (se 4 (by rfl) ⟨18477, by rfl⟩) (B 36955 (by norm_num) ⟨18477, by rfl⟩ (by norm_num))
theorem R229877 : Reach 229877 := rs (se 5 (by rfl) ⟨10775, by rfl⟩) (B 21551 (by norm_num) ⟨10775, by rfl⟩ (by norm_num))
theorem R164405 : Reach 164405 := rs (se 5 (by rfl) ⟨7706, by rfl⟩) (B 15413 (by norm_num) ⟨7706, by rfl⟩ (by norm_num))
theorem R131645 : Reach 131645 := rs (se 3 (by rfl) ⟨24683, by rfl⟩) (B 49367 (by norm_num) ⟨24683, by rfl⟩ (by norm_num))
theorem R164501 : Reach 164501 := rs (se 6 (by rfl) ⟨3855, by rfl⟩) (B 7711 (by norm_num) ⟨3855, by rfl⟩ (by norm_num))
theorem R131797 : Reach 131797 := rs (se 7 (by rfl) ⟨1544, by rfl⟩) (B 3089 (by norm_num) ⟨1544, by rfl⟩ (by norm_num))
theorem R230309 : Reach 230309 := rs (se 4 (by rfl) ⟨21591, by rfl⟩) (B 43183 (by norm_num) ⟨21591, by rfl⟩ (by norm_num))
theorem R132101 : Reach 132101 := rs (se 4 (by rfl) ⟨12384, by rfl⟩) (B 24769 (by norm_num) ⟨12384, by rfl⟩ (by norm_num))
theorem R525365 : Reach 525365 := rs (se 5 (by rfl) ⟨24626, by rfl⟩) (B 49253 (by norm_num) ⟨24626, by rfl⟩ (by norm_num))
theorem R99389 : Reach 99389 := rs (se 3 (by rfl) ⟨18635, by rfl⟩) (B 37271 (by norm_num) ⟨18635, by rfl⟩ (by norm_num))
theorem R197765 : Reach 197765 := rs (se 4 (by rfl) ⟨18540, by rfl⟩) (B 37081 (by norm_num) ⟨18540, by rfl⟩ (by norm_num))
theorem R459989 : Reach 459989 := rs (se 7 (by rfl) ⟨5390, by rfl⟩) (B 10781 (by norm_num) ⟨5390, by rfl⟩ (by norm_num))
theorem R656693 : Reach 656693 := rs (se 5 (by rfl) ⟨30782, by rfl⟩) (B 61565 (by norm_num) ⟨30782, by rfl⟩ (by norm_num))
theorem R230741 : Reach 230741 := rs (se 12 (by rfl) ⟨84, by rfl⟩) (B 169 (by norm_num) ⟨84, by rfl⟩ (by norm_num))
theorem R99805 : Reach 99805 := rs (se 3 (by rfl) ⟨18713, by rfl⟩) (B 37427 (by norm_num) ⟨18713, by rfl⟩ (by norm_num))
theorem R67125 : Reach 67125 := rs (se 5 (by rfl) ⟨3146, by rfl⟩) (B 6293 (by norm_num) ⟨3146, by rfl⟩ (by norm_num))
theorem R198197 : Reach 198197 := rs (se 5 (by rfl) ⟨9290, by rfl⟩) (B 18581 (by norm_num) ⟨9290, by rfl⟩ (by norm_num))
theorem R67129 : Reach 67129 := rs (se 2 (by rfl) ⟨25173, by rfl⟩) (B 50347 (by norm_num) ⟨25173, by rfl⟩ (by norm_num))
theorem R67133 : Reach 67133 := rs (se 3 (by rfl) ⟨12587, by rfl⟩) (B 25175 (by norm_num) ⟨12587, by rfl⟩ (by norm_num))
theorem R67137 : Reach 67137 := rs (se 2 (by rfl) ⟨25176, by rfl⟩) (B 50353 (by norm_num) ⟨25176, by rfl⟩ (by norm_num))
theorem R67141 : Reach 67141 := rs (se 4 (by rfl) ⟨6294, by rfl⟩) (B 12589 (by norm_num) ⟨6294, by rfl⟩ (by norm_num))
theorem R67145 : Reach 67145 := rs (se 2 (by rfl) ⟨25179, by rfl⟩) (B 50359 (by norm_num) ⟨25179, by rfl⟩ (by norm_num))
theorem R67149 : Reach 67149 := rs (se 3 (by rfl) ⟨12590, by rfl⟩) (B 25181 (by norm_num) ⟨12590, by rfl⟩ (by norm_num))
theorem R67153 : Reach 67153 := rs (se 2 (by rfl) ⟨25182, by rfl⟩) (B 50365 (by norm_num) ⟨25182, by rfl⟩ (by norm_num))
theorem R67157 : Reach 67157 := rs (se 8 (by rfl) ⟨393, by rfl⟩) (B 787 (by norm_num) ⟨393, by rfl⟩ (by norm_num))
theorem R67161 : Reach 67161 := rs (se 2 (by rfl) ⟨25185, by rfl⟩) (B 50371 (by norm_num) ⟨25185, by rfl⟩ (by norm_num))
theorem R67165 : Reach 67165 := rs (se 3 (by rfl) ⟨12593, by rfl⟩) (B 25187 (by norm_num) ⟨12593, by rfl⟩ (by norm_num))
theorem R67169 : Reach 67169 := rs (se 2 (by rfl) ⟨25188, by rfl⟩) (B 50377 (by norm_num) ⟨25188, by rfl⟩ (by norm_num))
theorem R67173 : Reach 67173 := rs (se 4 (by rfl) ⟨6297, by rfl⟩) (B 12595 (by norm_num) ⟨6297, by rfl⟩ (by norm_num))
theorem R67177 : Reach 67177 := rs (se 2 (by rfl) ⟨25191, by rfl⟩) (B 50383 (by norm_num) ⟨25191, by rfl⟩ (by norm_num))
theorem R67181 : Reach 67181 := rs (se 3 (by rfl) ⟨12596, by rfl⟩) (B 25193 (by norm_num) ⟨12596, by rfl⟩ (by norm_num))
theorem R67185 : Reach 67185 := rs (se 2 (by rfl) ⟨25194, by rfl⟩) (B 50389 (by norm_num) ⟨25194, by rfl⟩ (by norm_num))
theorem R67189 : Reach 67189 := rs (se 5 (by rfl) ⟨3149, by rfl⟩) (B 6299 (by norm_num) ⟨3149, by rfl⟩ (by norm_num))
theorem R67193 : Reach 67193 := rs (se 2 (by rfl) ⟨25197, by rfl⟩) (B 50395 (by norm_num) ⟨25197, by rfl⟩ (by norm_num))
theorem R67197 : Reach 67197 := rs (se 3 (by rfl) ⟨12599, by rfl⟩) (B 25199 (by norm_num) ⟨12599, by rfl⟩ (by norm_num))
theorem R67201 : Reach 67201 := rs (se 2 (by rfl) ⟨25200, by rfl⟩) (B 50401 (by norm_num) ⟨25200, by rfl⟩ (by norm_num))
theorem R67205 : Reach 67205 := rs (se 4 (by rfl) ⟨6300, by rfl⟩) (B 12601 (by norm_num) ⟨6300, by rfl⟩ (by norm_num))
theorem R67209 : Reach 67209 := rs (se 2 (by rfl) ⟨25203, by rfl⟩) (B 50407 (by norm_num) ⟨25203, by rfl⟩ (by norm_num))
theorem R67213 : Reach 67213 := rs (se 3 (by rfl) ⟨12602, by rfl⟩) (B 25205 (by norm_num) ⟨12602, by rfl⟩ (by norm_num))
theorem R67217 : Reach 67217 := rs (se 2 (by rfl) ⟨25206, by rfl⟩) (B 50413 (by norm_num) ⟨25206, by rfl⟩ (by norm_num))
theorem R67221 : Reach 67221 := rs (se 6 (by rfl) ⟨1575, by rfl⟩) (B 3151 (by norm_num) ⟨1575, by rfl⟩ (by norm_num))
theorem R67225 : Reach 67225 := rs (se 2 (by rfl) ⟨25209, by rfl⟩) (B 50419 (by norm_num) ⟨25209, by rfl⟩ (by norm_num))
theorem R67229 : Reach 67229 := rs (se 3 (by rfl) ⟨12605, by rfl⟩) (B 25211 (by norm_num) ⟨12605, by rfl⟩ (by norm_num))
theorem R67233 : Reach 67233 := rs (se 2 (by rfl) ⟨25212, by rfl⟩) (B 50425 (by norm_num) ⟨25212, by rfl⟩ (by norm_num))
theorem R67237 : Reach 67237 := rs (se 4 (by rfl) ⟨6303, by rfl⟩) (B 12607 (by norm_num) ⟨6303, by rfl⟩ (by norm_num))
theorem R67241 : Reach 67241 := rs (se 2 (by rfl) ⟨25215, by rfl⟩) (B 50431 (by norm_num) ⟨25215, by rfl⟩ (by norm_num))
theorem R67245 : Reach 67245 := rs (se 3 (by rfl) ⟨12608, by rfl⟩) (B 25217 (by norm_num) ⟨12608, by rfl⟩ (by norm_num))
theorem R67249 : Reach 67249 := rs (se 2 (by rfl) ⟨25218, by rfl⟩) (B 50437 (by norm_num) ⟨25218, by rfl⟩ (by norm_num))
theorem R67253 : Reach 67253 := rs (se 5 (by rfl) ⟨3152, by rfl⟩) (B 6305 (by norm_num) ⟨3152, by rfl⟩ (by norm_num))
theorem R67257 : Reach 67257 := rs (se 2 (by rfl) ⟨25221, by rfl⟩) (B 50443 (by norm_num) ⟨25221, by rfl⟩ (by norm_num))
theorem R67261 : Reach 67261 := rs (se 3 (by rfl) ⟨12611, by rfl⟩) (B 25223 (by norm_num) ⟨12611, by rfl⟩ (by norm_num))
theorem R67265 : Reach 67265 := rs (se 2 (by rfl) ⟨25224, by rfl⟩) (B 50449 (by norm_num) ⟨25224, by rfl⟩ (by norm_num))
theorem R67269 : Reach 67269 := rs (se 4 (by rfl) ⟨6306, by rfl⟩) (B 12613 (by norm_num) ⟨6306, by rfl⟩ (by norm_num))
theorem R67273 : Reach 67273 := rs (se 2 (by rfl) ⟨25227, by rfl⟩) (B 50455 (by norm_num) ⟨25227, by rfl⟩ (by norm_num))
theorem R67277 : Reach 67277 := rs (se 3 (by rfl) ⟨12614, by rfl⟩) (B 25229 (by norm_num) ⟨12614, by rfl⟩ (by norm_num))
theorem R67281 : Reach 67281 := rs (se 2 (by rfl) ⟨25230, by rfl⟩) (B 50461 (by norm_num) ⟨25230, by rfl⟩ (by norm_num))
theorem R67285 : Reach 67285 := rs (se 7 (by rfl) ⟨788, by rfl⟩) (B 1577 (by norm_num) ⟨788, by rfl⟩ (by norm_num))
theorem R67289 : Reach 67289 := rs (se 2 (by rfl) ⟨25233, by rfl⟩) (B 50467 (by norm_num) ⟨25233, by rfl⟩ (by norm_num))
theorem R67293 : Reach 67293 := rs (se 3 (by rfl) ⟨12617, by rfl⟩) (B 25235 (by norm_num) ⟨12617, by rfl⟩ (by norm_num))
theorem R67297 : Reach 67297 := rs (se 2 (by rfl) ⟨25236, by rfl⟩) (B 50473 (by norm_num) ⟨25236, by rfl⟩ (by norm_num))
theorem R67301 : Reach 67301 := rs (se 4 (by rfl) ⟨6309, by rfl⟩) (B 12619 (by norm_num) ⟨6309, by rfl⟩ (by norm_num))
theorem R67305 : Reach 67305 := rs (se 2 (by rfl) ⟨25239, by rfl⟩) (B 50479 (by norm_num) ⟨25239, by rfl⟩ (by norm_num))
theorem R67309 : Reach 67309 := rs (se 3 (by rfl) ⟨12620, by rfl⟩) (B 25241 (by norm_num) ⟨12620, by rfl⟩ (by norm_num))
theorem R67313 : Reach 67313 := rs (se 2 (by rfl) ⟨25242, by rfl⟩) (B 50485 (by norm_num) ⟨25242, by rfl⟩ (by norm_num))
theorem R67317 : Reach 67317 := rs (se 5 (by rfl) ⟨3155, by rfl⟩) (B 6311 (by norm_num) ⟨3155, by rfl⟩ (by norm_num))
theorem R132853 : Reach 132853 := rs (se 5 (by rfl) ⟨6227, by rfl⟩) (B 12455 (by norm_num) ⟨6227, by rfl⟩ (by norm_num))
theorem R67321 : Reach 67321 := rs (se 2 (by rfl) ⟨25245, by rfl⟩) (B 50491 (by norm_num) ⟨25245, by rfl⟩ (by norm_num))
theorem R67325 : Reach 67325 := rs (se 3 (by rfl) ⟨12623, by rfl⟩) (B 25247 (by norm_num) ⟨12623, by rfl⟩ (by norm_num))
theorem R67329 : Reach 67329 := rs (se 2 (by rfl) ⟨25248, by rfl⟩) (B 50497 (by norm_num) ⟨25248, by rfl⟩ (by norm_num))
theorem R67333 : Reach 67333 := rs (se 4 (by rfl) ⟨6312, by rfl⟩) (B 12625 (by norm_num) ⟨6312, by rfl⟩ (by norm_num))
theorem R231173 : Reach 231173 := rs (se 4 (by rfl) ⟨21672, by rfl⟩) (B 43345 (by norm_num) ⟨21672, by rfl⟩ (by norm_num))
theorem R67337 : Reach 67337 := rs (se 2 (by rfl) ⟨25251, by rfl⟩) (B 50503 (by norm_num) ⟨25251, by rfl⟩ (by norm_num))
theorem R67341 : Reach 67341 := rs (se 3 (by rfl) ⟨12626, by rfl⟩) (B 25253 (by norm_num) ⟨12626, by rfl⟩ (by norm_num))
theorem R67345 : Reach 67345 := rs (se 2 (by rfl) ⟨25254, by rfl⟩) (B 50509 (by norm_num) ⟨25254, by rfl⟩ (by norm_num))
theorem R67349 : Reach 67349 := rs (se 6 (by rfl) ⟨1578, by rfl⟩) (B 3157 (by norm_num) ⟨1578, by rfl⟩ (by norm_num))
theorem R67353 : Reach 67353 := rs (se 2 (by rfl) ⟨25257, by rfl⟩) (B 50515 (by norm_num) ⟨25257, by rfl⟩ (by norm_num))
theorem R67357 : Reach 67357 := rs (se 3 (by rfl) ⟨12629, by rfl⟩) (B 25259 (by norm_num) ⟨12629, by rfl⟩ (by norm_num))
theorem R67361 : Reach 67361 := rs (se 2 (by rfl) ⟨25260, by rfl⟩) (B 50521 (by norm_num) ⟨25260, by rfl⟩ (by norm_num))
theorem R67365 : Reach 67365 := rs (se 4 (by rfl) ⟨6315, by rfl⟩) (B 12631 (by norm_num) ⟨6315, by rfl⟩ (by norm_num))
theorem R67369 : Reach 67369 := rs (se 2 (by rfl) ⟨25263, by rfl⟩) (B 50527 (by norm_num) ⟨25263, by rfl⟩ (by norm_num))
theorem R67373 : Reach 67373 := rs (se 3 (by rfl) ⟨12632, by rfl⟩) (B 25265 (by norm_num) ⟨12632, by rfl⟩ (by norm_num))
theorem R67377 : Reach 67377 := rs (se 2 (by rfl) ⟨25266, by rfl⟩) (B 50533 (by norm_num) ⟨25266, by rfl⟩ (by norm_num))
theorem R67381 : Reach 67381 := rs (se 5 (by rfl) ⟨3158, by rfl⟩) (B 6317 (by norm_num) ⟨3158, by rfl⟩ (by norm_num))
theorem R67385 : Reach 67385 := rs (se 2 (by rfl) ⟨25269, by rfl⟩) (B 50539 (by norm_num) ⟨25269, by rfl⟩ (by norm_num))
theorem R67389 : Reach 67389 := rs (se 3 (by rfl) ⟨12635, by rfl⟩) (B 25271 (by norm_num) ⟨12635, by rfl⟩ (by norm_num))
theorem R67393 : Reach 67393 := rs (se 2 (by rfl) ⟨25272, by rfl⟩) (B 50545 (by norm_num) ⟨25272, by rfl⟩ (by norm_num))
theorem R67397 : Reach 67397 := rs (se 4 (by rfl) ⟨6318, by rfl⟩) (B 12637 (by norm_num) ⟨6318, by rfl⟩ (by norm_num))
theorem R264005 : Reach 264005 := rs (se 4 (by rfl) ⟨24750, by rfl⟩) (B 49501 (by norm_num) ⟨24750, by rfl⟩ (by norm_num))
theorem R67401 : Reach 67401 := rs (se 2 (by rfl) ⟨25275, by rfl⟩) (B 50551 (by norm_num) ⟨25275, by rfl⟩ (by norm_num))
theorem R67405 : Reach 67405 := rs (se 3 (by rfl) ⟨12638, by rfl⟩) (B 25277 (by norm_num) ⟨12638, by rfl⟩ (by norm_num))
theorem R67409 : Reach 67409 := rs (se 2 (by rfl) ⟨25278, by rfl⟩) (B 50557 (by norm_num) ⟨25278, by rfl⟩ (by norm_num))
theorem R67413 : Reach 67413 := rs (se 9 (by rfl) ⟨197, by rfl⟩) (B 395 (by norm_num) ⟨197, by rfl⟩ (by norm_num))
theorem R67417 : Reach 67417 := rs (se 2 (by rfl) ⟨25281, by rfl⟩) (B 50563 (by norm_num) ⟨25281, by rfl⟩ (by norm_num))
theorem R67421 : Reach 67421 := rs (se 3 (by rfl) ⟨12641, by rfl⟩) (B 25283 (by norm_num) ⟨12641, by rfl⟩ (by norm_num))
theorem R67425 : Reach 67425 := rs (se 2 (by rfl) ⟨25284, by rfl⟩) (B 50569 (by norm_num) ⟨25284, by rfl⟩ (by norm_num))
theorem R67429 : Reach 67429 := rs (se 4 (by rfl) ⟨6321, by rfl⟩) (B 12643 (by norm_num) ⟨6321, by rfl⟩ (by norm_num))
theorem R67433 : Reach 67433 := rs (se 2 (by rfl) ⟨25287, by rfl⟩) (B 50575 (by norm_num) ⟨25287, by rfl⟩ (by norm_num))
theorem R67437 : Reach 67437 := rs (se 3 (by rfl) ⟨12644, by rfl⟩) (B 25289 (by norm_num) ⟨12644, by rfl⟩ (by norm_num))
theorem R67441 : Reach 67441 := rs (se 2 (by rfl) ⟨25290, by rfl⟩) (B 50581 (by norm_num) ⟨25290, by rfl⟩ (by norm_num))
theorem R67445 : Reach 67445 := rs (se 5 (by rfl) ⟨3161, by rfl⟩) (B 6323 (by norm_num) ⟨3161, by rfl⟩ (by norm_num))
theorem R67449 : Reach 67449 := rs (se 2 (by rfl) ⟨25293, by rfl⟩) (B 50587 (by norm_num) ⟨25293, by rfl⟩ (by norm_num))
theorem R67453 : Reach 67453 := rs (se 3 (by rfl) ⟨12647, by rfl⟩) (B 25295 (by norm_num) ⟨12647, by rfl⟩ (by norm_num))
theorem R67457 : Reach 67457 := rs (se 2 (by rfl) ⟨25296, by rfl⟩) (B 50593 (by norm_num) ⟨25296, by rfl⟩ (by norm_num))
theorem R67461 : Reach 67461 := rs (se 4 (by rfl) ⟨6324, by rfl⟩) (B 12649 (by norm_num) ⟨6324, by rfl⟩ (by norm_num))
theorem R132997 : Reach 132997 := rs (se 4 (by rfl) ⟨12468, by rfl⟩) (B 24937 (by norm_num) ⟨12468, by rfl⟩ (by norm_num))
theorem R67465 : Reach 67465 := rs (se 2 (by rfl) ⟨25299, by rfl⟩) (B 50599 (by norm_num) ⟨25299, by rfl⟩ (by norm_num))
theorem R67469 : Reach 67469 := rs (se 3 (by rfl) ⟨12650, by rfl⟩) (B 25301 (by norm_num) ⟨12650, by rfl⟩ (by norm_num))
theorem R67473 : Reach 67473 := rs (se 2 (by rfl) ⟨25302, by rfl⟩) (B 50605 (by norm_num) ⟨25302, by rfl⟩ (by norm_num))
theorem R67477 : Reach 67477 := rs (se 6 (by rfl) ⟨1581, by rfl⟩) (B 3163 (by norm_num) ⟨1581, by rfl⟩ (by norm_num))
theorem R67481 : Reach 67481 := rs (se 2 (by rfl) ⟨25305, by rfl⟩) (B 50611 (by norm_num) ⟨25305, by rfl⟩ (by norm_num))
theorem R67485 : Reach 67485 := rs (se 3 (by rfl) ⟨12653, by rfl⟩) (B 25307 (by norm_num) ⟨12653, by rfl⟩ (by norm_num))
theorem R67489 : Reach 67489 := rs (se 2 (by rfl) ⟨25308, by rfl⟩) (B 50617 (by norm_num) ⟨25308, by rfl⟩ (by norm_num))
theorem R67493 : Reach 67493 := rs (se 4 (by rfl) ⟨6327, by rfl⟩) (B 12655 (by norm_num) ⟨6327, by rfl⟩ (by norm_num))
theorem R67497 : Reach 67497 := rs (se 2 (by rfl) ⟨25311, by rfl⟩) (B 50623 (by norm_num) ⟨25311, by rfl⟩ (by norm_num))
theorem R67501 : Reach 67501 := rs (se 3 (by rfl) ⟨12656, by rfl⟩) (B 25313 (by norm_num) ⟨12656, by rfl⟩ (by norm_num))
theorem R67505 : Reach 67505 := rs (se 2 (by rfl) ⟨25314, by rfl⟩) (B 50629 (by norm_num) ⟨25314, by rfl⟩ (by norm_num))
theorem R67509 : Reach 67509 := rs (se 5 (by rfl) ⟨3164, by rfl⟩) (B 6329 (by norm_num) ⟨3164, by rfl⟩ (by norm_num))
theorem R296885 : Reach 296885 := rs (se 5 (by rfl) ⟨13916, by rfl⟩) (B 27833 (by norm_num) ⟨13916, by rfl⟩ (by norm_num))
theorem R67513 : Reach 67513 := rs (se 2 (by rfl) ⟨25317, by rfl⟩) (B 50635 (by norm_num) ⟨25317, by rfl⟩ (by norm_num))
theorem R67517 : Reach 67517 := rs (se 3 (by rfl) ⟨12659, by rfl⟩) (B 25319 (by norm_num) ⟨12659, by rfl⟩ (by norm_num))
theorem R67521 : Reach 67521 := rs (se 2 (by rfl) ⟨25320, by rfl⟩) (B 50641 (by norm_num) ⟨25320, by rfl⟩ (by norm_num))
theorem R67525 : Reach 67525 := rs (se 4 (by rfl) ⟨6330, by rfl⟩) (B 12661 (by norm_num) ⟨6330, by rfl⟩ (by norm_num))
theorem R67529 : Reach 67529 := rs (se 2 (by rfl) ⟨25323, by rfl⟩) (B 50647 (by norm_num) ⟨25323, by rfl⟩ (by norm_num))
theorem R67533 : Reach 67533 := rs (se 3 (by rfl) ⟨12662, by rfl⟩) (B 25325 (by norm_num) ⟨12662, by rfl⟩ (by norm_num))
theorem R67537 : Reach 67537 := rs (se 2 (by rfl) ⟨25326, by rfl⟩) (B 50653 (by norm_num) ⟨25326, by rfl⟩ (by norm_num))
theorem R67541 : Reach 67541 := rs (se 7 (by rfl) ⟨791, by rfl⟩) (B 1583 (by norm_num) ⟨791, by rfl⟩ (by norm_num))
theorem R165845 : Reach 165845 := rs (se 7 (by rfl) ⟨1943, by rfl⟩) (B 3887 (by norm_num) ⟨1943, by rfl⟩ (by norm_num))
theorem R67545 : Reach 67545 := rs (se 2 (by rfl) ⟨25329, by rfl⟩) (B 50659 (by norm_num) ⟨25329, by rfl⟩ (by norm_num))
theorem R67549 : Reach 67549 := rs (se 3 (by rfl) ⟨12665, by rfl⟩) (B 25331 (by norm_num) ⟨12665, by rfl⟩ (by norm_num))
theorem R67553 : Reach 67553 := rs (se 2 (by rfl) ⟨25332, by rfl⟩) (B 50665 (by norm_num) ⟨25332, by rfl⟩ (by norm_num))
theorem R67557 : Reach 67557 := rs (se 4 (by rfl) ⟨6333, by rfl⟩) (B 12667 (by norm_num) ⟨6333, by rfl⟩ (by norm_num))
theorem R67561 : Reach 67561 := rs (se 2 (by rfl) ⟨25335, by rfl⟩) (B 50671 (by norm_num) ⟨25335, by rfl⟩ (by norm_num))
theorem R67565 : Reach 67565 := rs (se 3 (by rfl) ⟨12668, by rfl⟩) (B 25337 (by norm_num) ⟨12668, by rfl⟩ (by norm_num))
theorem R67569 : Reach 67569 := rs (se 2 (by rfl) ⟨25338, by rfl⟩) (B 50677 (by norm_num) ⟨25338, by rfl⟩ (by norm_num))
theorem R67573 : Reach 67573 := rs (se 5 (by rfl) ⟨3167, by rfl⟩) (B 6335 (by norm_num) ⟨3167, by rfl⟩ (by norm_num))
theorem R67577 : Reach 67577 := rs (se 2 (by rfl) ⟨25341, by rfl⟩) (B 50683 (by norm_num) ⟨25341, by rfl⟩ (by norm_num))
theorem R67581 : Reach 67581 := rs (se 3 (by rfl) ⟨12671, by rfl⟩) (B 25343 (by norm_num) ⟨12671, by rfl⟩ (by norm_num))
theorem R67585 : Reach 67585 := rs (se 2 (by rfl) ⟨25344, by rfl⟩) (B 50689 (by norm_num) ⟨25344, by rfl⟩ (by norm_num))
theorem R67589 : Reach 67589 := rs (se 4 (by rfl) ⟨6336, by rfl⟩) (B 12673 (by norm_num) ⟨6336, by rfl⟩ (by norm_num))
theorem R67593 : Reach 67593 := rs (se 2 (by rfl) ⟨25347, by rfl⟩) (B 50695 (by norm_num) ⟨25347, by rfl⟩ (by norm_num))
theorem R67597 : Reach 67597 := rs (se 3 (by rfl) ⟨12674, by rfl⟩) (B 25349 (by norm_num) ⟨12674, by rfl⟩ (by norm_num))
theorem R67601 : Reach 67601 := rs (se 2 (by rfl) ⟨25350, by rfl⟩) (B 50701 (by norm_num) ⟨25350, by rfl⟩ (by norm_num))
theorem R67605 : Reach 67605 := rs (se 6 (by rfl) ⟨1584, by rfl⟩) (B 3169 (by norm_num) ⟨1584, by rfl⟩ (by norm_num))
theorem R67609 : Reach 67609 := rs (se 2 (by rfl) ⟨25353, by rfl⟩) (B 50707 (by norm_num) ⟨25353, by rfl⟩ (by norm_num))
theorem R67613 : Reach 67613 := rs (se 3 (by rfl) ⟨12677, by rfl⟩) (B 25355 (by norm_num) ⟨12677, by rfl⟩ (by norm_num))
theorem R67617 : Reach 67617 := rs (se 2 (by rfl) ⟨25356, by rfl⟩) (B 50713 (by norm_num) ⟨25356, by rfl⟩ (by norm_num))
theorem R67621 : Reach 67621 := rs (se 4 (by rfl) ⟨6339, by rfl⟩) (B 12679 (by norm_num) ⟨6339, by rfl⟩ (by norm_num))
theorem R133157 : Reach 133157 := rs (se 4 (by rfl) ⟨12483, by rfl⟩) (B 24967 (by norm_num) ⟨12483, by rfl⟩ (by norm_num))
theorem R67625 : Reach 67625 := rs (se 2 (by rfl) ⟨25359, by rfl⟩) (B 50719 (by norm_num) ⟨25359, by rfl⟩ (by norm_num))
theorem R67629 : Reach 67629 := rs (se 3 (by rfl) ⟨12680, by rfl⟩) (B 25361 (by norm_num) ⟨12680, by rfl⟩ (by norm_num))
theorem R100397 : Reach 100397 := rs (se 3 (by rfl) ⟨18824, by rfl⟩) (B 37649 (by norm_num) ⟨18824, by rfl⟩ (by norm_num))
theorem R67633 : Reach 67633 := rs (se 2 (by rfl) ⟨25362, by rfl⟩) (B 50725 (by norm_num) ⟨25362, by rfl⟩ (by norm_num))
theorem R67637 : Reach 67637 := rs (se 5 (by rfl) ⟨3170, by rfl⟩) (B 6341 (by norm_num) ⟨3170, by rfl⟩ (by norm_num))
theorem R67641 : Reach 67641 := rs (se 2 (by rfl) ⟨25365, by rfl⟩) (B 50731 (by norm_num) ⟨25365, by rfl⟩ (by norm_num))
theorem R67645 : Reach 67645 := rs (se 3 (by rfl) ⟨12683, by rfl⟩) (B 25367 (by norm_num) ⟨12683, by rfl⟩ (by norm_num))
theorem R67649 : Reach 67649 := rs (se 2 (by rfl) ⟨25368, by rfl⟩) (B 50737 (by norm_num) ⟨25368, by rfl⟩ (by norm_num))
theorem R67653 : Reach 67653 := rs (se 4 (by rfl) ⟨6342, by rfl⟩) (B 12685 (by norm_num) ⟨6342, by rfl⟩ (by norm_num))
theorem R67657 : Reach 67657 := rs (se 2 (by rfl) ⟨25371, by rfl⟩) (B 50743 (by norm_num) ⟨25371, by rfl⟩ (by norm_num))
theorem R67661 : Reach 67661 := rs (se 3 (by rfl) ⟨12686, by rfl⟩) (B 25373 (by norm_num) ⟨12686, by rfl⟩ (by norm_num))
theorem R67665 : Reach 67665 := rs (se 2 (by rfl) ⟨25374, by rfl⟩) (B 50749 (by norm_num) ⟨25374, by rfl⟩ (by norm_num))
theorem R67669 : Reach 67669 := rs (se 8 (by rfl) ⟨396, by rfl⟩) (B 793 (by norm_num) ⟨396, by rfl⟩ (by norm_num))
theorem R67673 : Reach 67673 := rs (se 2 (by rfl) ⟨25377, by rfl⟩) (B 50755 (by norm_num) ⟨25377, by rfl⟩ (by norm_num))
theorem R67677 : Reach 67677 := rs (se 3 (by rfl) ⟨12689, by rfl⟩) (B 25379 (by norm_num) ⟨12689, by rfl⟩ (by norm_num))
theorem R67681 : Reach 67681 := rs (se 2 (by rfl) ⟨25380, by rfl⟩) (B 50761 (by norm_num) ⟨25380, by rfl⟩ (by norm_num))
theorem R67685 : Reach 67685 := rs (se 4 (by rfl) ⟨6345, by rfl⟩) (B 12691 (by norm_num) ⟨6345, by rfl⟩ (by norm_num))
theorem R264293 : Reach 264293 := rs (se 4 (by rfl) ⟨24777, by rfl⟩) (B 49555 (by norm_num) ⟨24777, by rfl⟩ (by norm_num))
theorem R67689 : Reach 67689 := rs (se 2 (by rfl) ⟨25383, by rfl⟩) (B 50767 (by norm_num) ⟨25383, by rfl⟩ (by norm_num))
theorem R67693 : Reach 67693 := rs (se 3 (by rfl) ⟨12692, by rfl⟩) (B 25385 (by norm_num) ⟨12692, by rfl⟩ (by norm_num))
theorem R67697 : Reach 67697 := rs (se 2 (by rfl) ⟨25386, by rfl⟩) (B 50773 (by norm_num) ⟨25386, by rfl⟩ (by norm_num))
theorem R67701 : Reach 67701 := rs (se 5 (by rfl) ⟨3173, by rfl⟩) (B 6347 (by norm_num) ⟨3173, by rfl⟩ (by norm_num))
theorem R329845 : Reach 329845 := rs (se 5 (by rfl) ⟨15461, by rfl⟩) (B 30923 (by norm_num) ⟨15461, by rfl⟩ (by norm_num))
theorem R67705 : Reach 67705 := rs (se 2 (by rfl) ⟨25389, by rfl⟩) (B 50779 (by norm_num) ⟨25389, by rfl⟩ (by norm_num))
theorem R67709 : Reach 67709 := rs (se 3 (by rfl) ⟨12695, by rfl⟩) (B 25391 (by norm_num) ⟨12695, by rfl⟩ (by norm_num))
theorem R100477 : Reach 100477 := rs (se 3 (by rfl) ⟨18839, by rfl⟩) (B 37679 (by norm_num) ⟨18839, by rfl⟩ (by norm_num))
theorem R67713 : Reach 67713 := rs (se 2 (by rfl) ⟨25392, by rfl⟩) (B 50785 (by norm_num) ⟨25392, by rfl⟩ (by norm_num))
theorem R67717 : Reach 67717 := rs (se 4 (by rfl) ⟨6348, by rfl⟩) (B 12697 (by norm_num) ⟨6348, by rfl⟩ (by norm_num))
theorem R67721 : Reach 67721 := rs (se 2 (by rfl) ⟨25395, by rfl⟩) (B 50791 (by norm_num) ⟨25395, by rfl⟩ (by norm_num))
theorem R67725 : Reach 67725 := rs (se 3 (by rfl) ⟨12698, by rfl⟩) (B 25397 (by norm_num) ⟨12698, by rfl⟩ (by norm_num))
theorem R67729 : Reach 67729 := rs (se 2 (by rfl) ⟨25398, by rfl⟩) (B 50797 (by norm_num) ⟨25398, by rfl⟩ (by norm_num))
theorem R67733 : Reach 67733 := rs (se 6 (by rfl) ⟨1587, by rfl⟩) (B 3175 (by norm_num) ⟨1587, by rfl⟩ (by norm_num))
theorem R67737 : Reach 67737 := rs (se 2 (by rfl) ⟨25401, by rfl⟩) (B 50803 (by norm_num) ⟨25401, by rfl⟩ (by norm_num))
theorem R67741 : Reach 67741 := rs (se 3 (by rfl) ⟨12701, by rfl⟩) (B 25403 (by norm_num) ⟨12701, by rfl⟩ (by norm_num))
theorem R67745 : Reach 67745 := rs (se 2 (by rfl) ⟨25404, by rfl⟩) (B 50809 (by norm_num) ⟨25404, by rfl⟩ (by norm_num))
theorem R67749 : Reach 67749 := rs (se 4 (by rfl) ⟨6351, by rfl⟩) (B 12703 (by norm_num) ⟨6351, by rfl⟩ (by norm_num))
theorem R67753 : Reach 67753 := rs (se 2 (by rfl) ⟨25407, by rfl⟩) (B 50815 (by norm_num) ⟨25407, by rfl⟩ (by norm_num))
theorem R67757 : Reach 67757 := rs (se 3 (by rfl) ⟨12704, by rfl⟩) (B 25409 (by norm_num) ⟨12704, by rfl⟩ (by norm_num))
theorem R67761 : Reach 67761 := rs (se 2 (by rfl) ⟨25410, by rfl⟩) (B 50821 (by norm_num) ⟨25410, by rfl⟩ (by norm_num))
theorem R67765 : Reach 67765 := rs (se 5 (by rfl) ⟨3176, by rfl⟩) (B 6353 (by norm_num) ⟨3176, by rfl⟩ (by norm_num))
theorem R231605 : Reach 231605 := rs (se 5 (by rfl) ⟨10856, by rfl⟩) (B 21713 (by norm_num) ⟨10856, by rfl⟩ (by norm_num))
theorem R133301 : Reach 133301 := rs (se 5 (by rfl) ⟨6248, by rfl⟩) (B 12497 (by norm_num) ⟨6248, by rfl⟩ (by norm_num))
theorem R67769 : Reach 67769 := rs (se 2 (by rfl) ⟨25413, by rfl⟩) (B 50827 (by norm_num) ⟨25413, by rfl⟩ (by norm_num))
theorem R67773 : Reach 67773 := rs (se 3 (by rfl) ⟨12707, by rfl⟩) (B 25415 (by norm_num) ⟨12707, by rfl⟩ (by norm_num))
theorem R67777 : Reach 67777 := rs (se 2 (by rfl) ⟨25416, by rfl⟩) (B 50833 (by norm_num) ⟨25416, by rfl⟩ (by norm_num))
theorem R67781 : Reach 67781 := rs (se 4 (by rfl) ⟨6354, by rfl⟩) (B 12709 (by norm_num) ⟨6354, by rfl⟩ (by norm_num))
theorem R67785 : Reach 67785 := rs (se 2 (by rfl) ⟨25419, by rfl⟩) (B 50839 (by norm_num) ⟨25419, by rfl⟩ (by norm_num))
theorem R67789 : Reach 67789 := rs (se 3 (by rfl) ⟨12710, by rfl⟩) (B 25421 (by norm_num) ⟨12710, by rfl⟩ (by norm_num))
theorem R67793 : Reach 67793 := rs (se 2 (by rfl) ⟨25422, by rfl⟩) (B 50845 (by norm_num) ⟨25422, by rfl⟩ (by norm_num))
theorem R67797 : Reach 67797 := rs (se 7 (by rfl) ⟨794, by rfl⟩) (B 1589 (by norm_num) ⟨794, by rfl⟩ (by norm_num))
theorem R67801 : Reach 67801 := rs (se 2 (by rfl) ⟨25425, by rfl⟩) (B 50851 (by norm_num) ⟨25425, by rfl⟩ (by norm_num))
theorem R67805 : Reach 67805 := rs (se 3 (by rfl) ⟨12713, by rfl⟩) (B 25427 (by norm_num) ⟨12713, by rfl⟩ (by norm_num))
theorem R67809 : Reach 67809 := rs (se 2 (by rfl) ⟨25428, by rfl⟩) (B 50857 (by norm_num) ⟨25428, by rfl⟩ (by norm_num))
theorem R67813 : Reach 67813 := rs (se 4 (by rfl) ⟨6357, by rfl⟩) (B 12715 (by norm_num) ⟨6357, by rfl⟩ (by norm_num))
theorem R67817 : Reach 67817 := rs (se 2 (by rfl) ⟨25431, by rfl⟩) (B 50863 (by norm_num) ⟨25431, by rfl⟩ (by norm_num))
theorem R67821 : Reach 67821 := rs (se 3 (by rfl) ⟨12716, by rfl⟩) (B 25433 (by norm_num) ⟨12716, by rfl⟩ (by norm_num))
theorem R67825 : Reach 67825 := rs (se 2 (by rfl) ⟨25434, by rfl⟩) (B 50869 (by norm_num) ⟨25434, by rfl⟩ (by norm_num))
theorem R67829 : Reach 67829 := rs (se 5 (by rfl) ⟨3179, by rfl⟩) (B 6359 (by norm_num) ⟨3179, by rfl⟩ (by norm_num))
theorem R100597 : Reach 100597 := rs (se 5 (by rfl) ⟨4715, by rfl⟩) (B 9431 (by norm_num) ⟨4715, by rfl⟩ (by norm_num))
theorem R67833 : Reach 67833 := rs (se 2 (by rfl) ⟨25437, by rfl⟩) (B 50875 (by norm_num) ⟨25437, by rfl⟩ (by norm_num))
theorem R67837 : Reach 67837 := rs (se 3 (by rfl) ⟨12719, by rfl⟩) (B 25439 (by norm_num) ⟨12719, by rfl⟩ (by norm_num))
theorem R67841 : Reach 67841 := rs (se 2 (by rfl) ⟨25440, by rfl⟩) (B 50881 (by norm_num) ⟨25440, by rfl⟩ (by norm_num))
theorem R67845 : Reach 67845 := rs (se 4 (by rfl) ⟨6360, by rfl⟩) (B 12721 (by norm_num) ⟨6360, by rfl⟩ (by norm_num))
theorem R67849 : Reach 67849 := rs (se 2 (by rfl) ⟨25443, by rfl⟩) (B 50887 (by norm_num) ⟨25443, by rfl⟩ (by norm_num))
theorem R67853 : Reach 67853 := rs (se 3 (by rfl) ⟨12722, by rfl⟩) (B 25445 (by norm_num) ⟨12722, by rfl⟩ (by norm_num))
theorem R67857 : Reach 67857 := rs (se 2 (by rfl) ⟨25446, by rfl⟩) (B 50893 (by norm_num) ⟨25446, by rfl⟩ (by norm_num))
theorem R67861 : Reach 67861 := rs (se 6 (by rfl) ⟨1590, by rfl⟩) (B 3181 (by norm_num) ⟨1590, by rfl⟩ (by norm_num))
theorem R67865 : Reach 67865 := rs (se 2 (by rfl) ⟨25449, by rfl⟩) (B 50899 (by norm_num) ⟨25449, by rfl⟩ (by norm_num))
theorem R67869 : Reach 67869 := rs (se 3 (by rfl) ⟨12725, by rfl⟩) (B 25451 (by norm_num) ⟨12725, by rfl⟩ (by norm_num))
theorem R67873 : Reach 67873 := rs (se 2 (by rfl) ⟨25452, by rfl⟩) (B 50905 (by norm_num) ⟨25452, by rfl⟩ (by norm_num))
theorem R198949 : Reach 198949 := rs (se 4 (by rfl) ⟨18651, by rfl⟩) (B 37303 (by norm_num) ⟨18651, by rfl⟩ (by norm_num))
theorem R67877 : Reach 67877 := rs (se 4 (by rfl) ⟨6363, by rfl⟩) (B 12727 (by norm_num) ⟨6363, by rfl⟩ (by norm_num))
theorem R264485 : Reach 264485 := rs (se 4 (by rfl) ⟨24795, by rfl⟩) (B 49591 (by norm_num) ⟨24795, by rfl⟩ (by norm_num))
theorem R67881 : Reach 67881 := rs (se 2 (by rfl) ⟨25455, by rfl⟩) (B 50911 (by norm_num) ⟨25455, by rfl⟩ (by norm_num))
theorem R67885 : Reach 67885 := rs (se 3 (by rfl) ⟨12728, by rfl⟩) (B 25457 (by norm_num) ⟨12728, by rfl⟩ (by norm_num))
theorem R67889 : Reach 67889 := rs (se 2 (by rfl) ⟨25458, by rfl⟩) (B 50917 (by norm_num) ⟨25458, by rfl⟩ (by norm_num))
theorem R67893 : Reach 67893 := rs (se 5 (by rfl) ⟨3182, by rfl⟩) (B 6365 (by norm_num) ⟨3182, by rfl⟩ (by norm_num))
theorem R67897 : Reach 67897 := rs (se 2 (by rfl) ⟨25461, by rfl⟩) (B 50923 (by norm_num) ⟨25461, by rfl⟩ (by norm_num))
theorem R67901 : Reach 67901 := rs (se 3 (by rfl) ⟨12731, by rfl⟩) (B 25463 (by norm_num) ⟨12731, by rfl⟩ (by norm_num))
theorem R67905 : Reach 67905 := rs (se 2 (by rfl) ⟨25464, by rfl⟩) (B 50929 (by norm_num) ⟨25464, by rfl⟩ (by norm_num))
theorem R67909 : Reach 67909 := rs (se 4 (by rfl) ⟨6366, by rfl⟩) (B 12733 (by norm_num) ⟨6366, by rfl⟩ (by norm_num))
theorem R67913 : Reach 67913 := rs (se 2 (by rfl) ⟨25467, by rfl⟩) (B 50935 (by norm_num) ⟨25467, by rfl⟩ (by norm_num))
theorem R67917 : Reach 67917 := rs (se 3 (by rfl) ⟨12734, by rfl⟩) (B 25469 (by norm_num) ⟨12734, by rfl⟩ (by norm_num))
theorem R67921 : Reach 67921 := rs (se 2 (by rfl) ⟨25470, by rfl⟩) (B 50941 (by norm_num) ⟨25470, by rfl⟩ (by norm_num))
theorem R67925 : Reach 67925 := rs (se 10 (by rfl) ⟨99, by rfl⟩) (B 199 (by norm_num) ⟨99, by rfl⟩ (by norm_num))
theorem R100693 : Reach 100693 := rs (se 10 (by rfl) ⟨147, by rfl⟩) (B 295 (by norm_num) ⟨147, by rfl⟩ (by norm_num))
theorem R67929 : Reach 67929 := rs (se 2 (by rfl) ⟨25473, by rfl⟩) (B 50947 (by norm_num) ⟨25473, by rfl⟩ (by norm_num))
theorem R67933 : Reach 67933 := rs (se 3 (by rfl) ⟨12737, by rfl⟩) (B 25475 (by norm_num) ⟨12737, by rfl⟩ (by norm_num))
theorem R67937 : Reach 67937 := rs (se 2 (by rfl) ⟨25476, by rfl⟩) (B 50953 (by norm_num) ⟨25476, by rfl⟩ (by norm_num))
theorem R100709 : Reach 100709 := rs (se 4 (by rfl) ⟨9441, by rfl⟩) (B 18883 (by norm_num) ⟨9441, by rfl⟩ (by norm_num))
theorem R67941 : Reach 67941 := rs (se 4 (by rfl) ⟨6369, by rfl⟩) (B 12739 (by norm_num) ⟨6369, by rfl⟩ (by norm_num))
theorem R67945 : Reach 67945 := rs (se 2 (by rfl) ⟨25479, by rfl⟩) (B 50959 (by norm_num) ⟨25479, by rfl⟩ (by norm_num))
theorem R67949 : Reach 67949 := rs (se 3 (by rfl) ⟨12740, by rfl⟩) (B 25481 (by norm_num) ⟨12740, by rfl⟩ (by norm_num))
theorem R67953 : Reach 67953 := rs (se 2 (by rfl) ⟨25482, by rfl⟩) (B 50965 (by norm_num) ⟨25482, by rfl⟩ (by norm_num))
theorem R67957 : Reach 67957 := rs (se 5 (by rfl) ⟨3185, by rfl⟩) (B 6371 (by norm_num) ⟨3185, by rfl⟩ (by norm_num))
theorem R67961 : Reach 67961 := rs (se 2 (by rfl) ⟨25485, by rfl⟩) (B 50971 (by norm_num) ⟨25485, by rfl⟩ (by norm_num))
theorem R100733 : Reach 100733 := rs (se 3 (by rfl) ⟨18887, by rfl⟩) (B 37775 (by norm_num) ⟨18887, by rfl⟩ (by norm_num))
theorem R67965 : Reach 67965 := rs (se 3 (by rfl) ⟨12743, by rfl⟩) (B 25487 (by norm_num) ⟨12743, by rfl⟩ (by norm_num))
theorem R67969 : Reach 67969 := rs (se 2 (by rfl) ⟨25488, by rfl⟩) (B 50977 (by norm_num) ⟨25488, by rfl⟩ (by norm_num))
theorem R67973 : Reach 67973 := rs (se 4 (by rfl) ⟨6372, by rfl⟩) (B 12745 (by norm_num) ⟨6372, by rfl⟩ (by norm_num))
theorem R67977 : Reach 67977 := rs (se 2 (by rfl) ⟨25491, by rfl⟩) (B 50983 (by norm_num) ⟨25491, by rfl⟩ (by norm_num))
theorem R67981 : Reach 67981 := rs (se 3 (by rfl) ⟨12746, by rfl⟩) (B 25493 (by norm_num) ⟨12746, by rfl⟩ (by norm_num))
theorem R67985 : Reach 67985 := rs (se 2 (by rfl) ⟨25494, by rfl⟩) (B 50989 (by norm_num) ⟨25494, by rfl⟩ (by norm_num))
theorem R100757 : Reach 100757 := rs (se 6 (by rfl) ⟨2361, by rfl⟩) (B 4723 (by norm_num) ⟨2361, by rfl⟩ (by norm_num))
theorem R67989 : Reach 67989 := rs (se 6 (by rfl) ⟨1593, by rfl⟩) (B 3187 (by norm_num) ⟨1593, by rfl⟩ (by norm_num))
theorem R67993 : Reach 67993 := rs (se 2 (by rfl) ⟨25497, by rfl⟩) (B 50995 (by norm_num) ⟨25497, by rfl⟩ (by norm_num))
theorem R67997 : Reach 67997 := rs (se 3 (by rfl) ⟨12749, by rfl⟩) (B 25499 (by norm_num) ⟨12749, by rfl⟩ (by norm_num))
theorem R68001 : Reach 68001 := rs (se 2 (by rfl) ⟨25500, by rfl⟩) (B 51001 (by norm_num) ⟨25500, by rfl⟩ (by norm_num))
theorem R68005 : Reach 68005 := rs (se 4 (by rfl) ⟨6375, by rfl⟩) (B 12751 (by norm_num) ⟨6375, by rfl⟩ (by norm_num))
theorem R68009 : Reach 68009 := rs (se 2 (by rfl) ⟨25503, by rfl⟩) (B 51007 (by norm_num) ⟨25503, by rfl⟩ (by norm_num))
theorem R100781 : Reach 100781 := rs (se 3 (by rfl) ⟨18896, by rfl⟩) (B 37793 (by norm_num) ⟨18896, by rfl⟩ (by norm_num))
theorem R68013 : Reach 68013 := rs (se 3 (by rfl) ⟨12752, by rfl⟩) (B 25505 (by norm_num) ⟨12752, by rfl⟩ (by norm_num))
theorem R68017 : Reach 68017 := rs (se 2 (by rfl) ⟨25506, by rfl⟩) (B 51013 (by norm_num) ⟨25506, by rfl⟩ (by norm_num))
theorem R68021 : Reach 68021 := rs (se 5 (by rfl) ⟨3188, by rfl⟩) (B 6377 (by norm_num) ⟨3188, by rfl⟩ (by norm_num))
theorem R68025 : Reach 68025 := rs (se 2 (by rfl) ⟨25509, by rfl⟩) (B 51019 (by norm_num) ⟨25509, by rfl⟩ (by norm_num))
theorem R68029 : Reach 68029 := rs (se 3 (by rfl) ⟨12755, by rfl⟩) (B 25511 (by norm_num) ⟨12755, by rfl⟩ (by norm_num))
theorem R68033 : Reach 68033 := rs (se 2 (by rfl) ⟨25512, by rfl⟩) (B 51025 (by norm_num) ⟨25512, by rfl⟩ (by norm_num))
theorem R100805 : Reach 100805 := rs (se 4 (by rfl) ⟨9450, by rfl⟩) (B 18901 (by norm_num) ⟨9450, by rfl⟩ (by norm_num))
theorem R68037 : Reach 68037 := rs (se 4 (by rfl) ⟨6378, by rfl⟩) (B 12757 (by norm_num) ⟨6378, by rfl⟩ (by norm_num))
theorem R68041 : Reach 68041 := rs (se 2 (by rfl) ⟨25515, by rfl⟩) (B 51031 (by norm_num) ⟨25515, by rfl⟩ (by norm_num))
theorem R68045 : Reach 68045 := rs (se 3 (by rfl) ⟨12758, by rfl⟩) (B 25517 (by norm_num) ⟨12758, by rfl⟩ (by norm_num))
theorem R68049 : Reach 68049 := rs (se 2 (by rfl) ⟨25518, by rfl⟩) (B 51037 (by norm_num) ⟨25518, by rfl⟩ (by norm_num))
theorem R68053 : Reach 68053 := rs (se 7 (by rfl) ⟨797, by rfl⟩) (B 1595 (by norm_num) ⟨797, by rfl⟩ (by norm_num))
theorem R133589 : Reach 133589 := rs (se 7 (by rfl) ⟨1565, by rfl⟩) (B 3131 (by norm_num) ⟨1565, by rfl⟩ (by norm_num))
theorem R68057 : Reach 68057 := rs (se 2 (by rfl) ⟨25521, by rfl⟩) (B 51043 (by norm_num) ⟨25521, by rfl⟩ (by norm_num))
theorem R100829 : Reach 100829 := rs (se 3 (by rfl) ⟨18905, by rfl⟩) (B 37811 (by norm_num) ⟨18905, by rfl⟩ (by norm_num))
theorem R68061 : Reach 68061 := rs (se 3 (by rfl) ⟨12761, by rfl⟩) (B 25523 (by norm_num) ⟨12761, by rfl⟩ (by norm_num))
theorem R68065 : Reach 68065 := rs (se 2 (by rfl) ⟨25524, by rfl⟩) (B 51049 (by norm_num) ⟨25524, by rfl⟩ (by norm_num))
theorem R68069 : Reach 68069 := rs (se 4 (by rfl) ⟨6381, by rfl⟩) (B 12763 (by norm_num) ⟨6381, by rfl⟩ (by norm_num))
theorem R68073 : Reach 68073 := rs (se 2 (by rfl) ⟨25527, by rfl⟩) (B 51055 (by norm_num) ⟨25527, by rfl⟩ (by norm_num))
theorem R68077 : Reach 68077 := rs (se 3 (by rfl) ⟨12764, by rfl⟩) (B 25529 (by norm_num) ⟨12764, by rfl⟩ (by norm_num))
theorem R68081 : Reach 68081 := rs (se 2 (by rfl) ⟨25530, by rfl⟩) (B 51061 (by norm_num) ⟨25530, by rfl⟩ (by norm_num))
theorem R100853 : Reach 100853 := rs (se 5 (by rfl) ⟨4727, by rfl⟩) (B 9455 (by norm_num) ⟨4727, by rfl⟩ (by norm_num))
theorem R68085 : Reach 68085 := rs (se 5 (by rfl) ⟨3191, by rfl⟩) (B 6383 (by norm_num) ⟨3191, by rfl⟩ (by norm_num))
theorem R68089 : Reach 68089 := rs (se 2 (by rfl) ⟨25533, by rfl⟩) (B 51067 (by norm_num) ⟨25533, by rfl⟩ (by norm_num))
theorem R68093 : Reach 68093 := rs (se 3 (by rfl) ⟨12767, by rfl⟩) (B 25535 (by norm_num) ⟨12767, by rfl⟩ (by norm_num))
theorem R68097 : Reach 68097 := rs (se 2 (by rfl) ⟨25536, by rfl⟩) (B 51073 (by norm_num) ⟨25536, by rfl⟩ (by norm_num))
theorem R68101 : Reach 68101 := rs (se 4 (by rfl) ⟨6384, by rfl⟩) (B 12769 (by norm_num) ⟨6384, by rfl⟩ (by norm_num))
theorem R68105 : Reach 68105 := rs (se 2 (by rfl) ⟨25539, by rfl⟩) (B 51079 (by norm_num) ⟨25539, by rfl⟩ (by norm_num))
theorem R100877 : Reach 100877 := rs (se 3 (by rfl) ⟨18914, by rfl⟩) (B 37829 (by norm_num) ⟨18914, by rfl⟩ (by norm_num))
theorem R68109 : Reach 68109 := rs (se 3 (by rfl) ⟨12770, by rfl⟩) (B 25541 (by norm_num) ⟨12770, by rfl⟩ (by norm_num))
theorem R68113 : Reach 68113 := rs (se 2 (by rfl) ⟨25542, by rfl⟩) (B 51085 (by norm_num) ⟨25542, by rfl⟩ (by norm_num))
theorem R68117 : Reach 68117 := rs (se 6 (by rfl) ⟨1596, by rfl⟩) (B 3193 (by norm_num) ⟨1596, by rfl⟩ (by norm_num))
theorem R68121 : Reach 68121 := rs (se 2 (by rfl) ⟨25545, by rfl⟩) (B 51091 (by norm_num) ⟨25545, by rfl⟩ (by norm_num))
theorem R68125 : Reach 68125 := rs (se 3 (by rfl) ⟨12773, by rfl⟩) (B 25547 (by norm_num) ⟨12773, by rfl⟩ (by norm_num))
theorem R68129 : Reach 68129 := rs (se 2 (by rfl) ⟨25548, by rfl⟩) (B 51097 (by norm_num) ⟨25548, by rfl⟩ (by norm_num))
theorem R100901 : Reach 100901 := rs (se 4 (by rfl) ⟨9459, by rfl⟩) (B 18919 (by norm_num) ⟨9459, by rfl⟩ (by norm_num))
theorem R68133 : Reach 68133 := rs (se 4 (by rfl) ⟨6387, by rfl⟩) (B 12775 (by norm_num) ⟨6387, by rfl⟩ (by norm_num))
theorem R68137 : Reach 68137 := rs (se 2 (by rfl) ⟨25551, by rfl⟩) (B 51103 (by norm_num) ⟨25551, by rfl⟩ (by norm_num))
theorem R68141 : Reach 68141 := rs (se 3 (by rfl) ⟨12776, by rfl⟩) (B 25553 (by norm_num) ⟨12776, by rfl⟩ (by norm_num))
theorem R68145 : Reach 68145 := rs (se 2 (by rfl) ⟨25554, by rfl⟩) (B 51109 (by norm_num) ⟨25554, by rfl⟩ (by norm_num))
theorem R68149 : Reach 68149 := rs (se 5 (by rfl) ⟨3194, by rfl⟩) (B 6389 (by norm_num) ⟨3194, by rfl⟩ (by norm_num))
theorem R68153 : Reach 68153 := rs (se 2 (by rfl) ⟨25557, by rfl⟩) (B 51115 (by norm_num) ⟨25557, by rfl⟩ (by norm_num))
theorem R100925 : Reach 100925 := rs (se 3 (by rfl) ⟨18923, by rfl⟩) (B 37847 (by norm_num) ⟨18923, by rfl⟩ (by norm_num))
theorem R68157 : Reach 68157 := rs (se 3 (by rfl) ⟨12779, by rfl⟩) (B 25559 (by norm_num) ⟨12779, by rfl⟩ (by norm_num))
theorem R68161 : Reach 68161 := rs (se 2 (by rfl) ⟨25560, by rfl⟩) (B 51121 (by norm_num) ⟨25560, by rfl⟩ (by norm_num))
theorem R68165 : Reach 68165 := rs (se 4 (by rfl) ⟨6390, by rfl⟩) (B 12781 (by norm_num) ⟨6390, by rfl⟩ (by norm_num))
theorem R68169 : Reach 68169 := rs (se 2 (by rfl) ⟨25563, by rfl⟩) (B 51127 (by norm_num) ⟨25563, by rfl⟩ (by norm_num))
theorem R68173 : Reach 68173 := rs (se 3 (by rfl) ⟨12782, by rfl⟩) (B 25565 (by norm_num) ⟨12782, by rfl⟩ (by norm_num))
theorem R68177 : Reach 68177 := rs (se 2 (by rfl) ⟨25566, by rfl⟩) (B 51133 (by norm_num) ⟨25566, by rfl⟩ (by norm_num))
theorem R100949 : Reach 100949 := rs (se 8 (by rfl) ⟨591, by rfl⟩) (B 1183 (by norm_num) ⟨591, by rfl⟩ (by norm_num))
theorem R68181 : Reach 68181 := rs (se 8 (by rfl) ⟨399, by rfl⟩) (B 799 (by norm_num) ⟨399, by rfl⟩ (by norm_num))
theorem R68185 : Reach 68185 := rs (se 2 (by rfl) ⟨25569, by rfl⟩) (B 51139 (by norm_num) ⟨25569, by rfl⟩ (by norm_num))
theorem R68189 : Reach 68189 := rs (se 3 (by rfl) ⟨12785, by rfl⟩) (B 25571 (by norm_num) ⟨12785, by rfl⟩ (by norm_num))
theorem R68193 : Reach 68193 := rs (se 2 (by rfl) ⟨25572, by rfl⟩) (B 51145 (by norm_num) ⟨25572, by rfl⟩ (by norm_num))
theorem R68197 : Reach 68197 := rs (se 4 (by rfl) ⟨6393, by rfl⟩) (B 12787 (by norm_num) ⟨6393, by rfl⟩ (by norm_num))
theorem R232037 : Reach 232037 := rs (se 4 (by rfl) ⟨21753, by rfl⟩) (B 43507 (by norm_num) ⟨21753, by rfl⟩ (by norm_num))
theorem R68201 : Reach 68201 := rs (se 2 (by rfl) ⟨25575, by rfl⟩) (B 51151 (by norm_num) ⟨25575, by rfl⟩ (by norm_num))
theorem R100973 : Reach 100973 := rs (se 3 (by rfl) ⟨18932, by rfl⟩) (B 37865 (by norm_num) ⟨18932, by rfl⟩ (by norm_num))
theorem R68205 : Reach 68205 := rs (se 3 (by rfl) ⟨12788, by rfl⟩) (B 25577 (by norm_num) ⟨12788, by rfl⟩ (by norm_num))
theorem R133741 : Reach 133741 := rs (se 3 (by rfl) ⟨25076, by rfl⟩) (B 50153 (by norm_num) ⟨25076, by rfl⟩ (by norm_num))
theorem R68209 : Reach 68209 := rs (se 2 (by rfl) ⟨25578, by rfl⟩) (B 51157 (by norm_num) ⟨25578, by rfl⟩ (by norm_num))
theorem R68213 : Reach 68213 := rs (se 5 (by rfl) ⟨3197, by rfl⟩) (B 6395 (by norm_num) ⟨3197, by rfl⟩ (by norm_num))
theorem R68217 : Reach 68217 := rs (se 2 (by rfl) ⟨25581, by rfl⟩) (B 51163 (by norm_num) ⟨25581, by rfl⟩ (by norm_num))
theorem R68221 : Reach 68221 := rs (se 3 (by rfl) ⟨12791, by rfl⟩) (B 25583 (by norm_num) ⟨12791, by rfl⟩ (by norm_num))
theorem R68225 : Reach 68225 := rs (se 2 (by rfl) ⟨25584, by rfl⟩) (B 51169 (by norm_num) ⟨25584, by rfl⟩ (by norm_num))
theorem R100997 : Reach 100997 := rs (se 4 (by rfl) ⟨9468, by rfl⟩) (B 18937 (by norm_num) ⟨9468, by rfl⟩ (by norm_num))
theorem R68229 : Reach 68229 := rs (se 4 (by rfl) ⟨6396, by rfl⟩) (B 12793 (by norm_num) ⟨6396, by rfl⟩ (by norm_num))
theorem R68233 : Reach 68233 := rs (se 2 (by rfl) ⟨25587, by rfl⟩) (B 51175 (by norm_num) ⟨25587, by rfl⟩ (by norm_num))
theorem R68237 : Reach 68237 := rs (se 3 (by rfl) ⟨12794, by rfl⟩) (B 25589 (by norm_num) ⟨12794, by rfl⟩ (by norm_num))
theorem R68241 : Reach 68241 := rs (se 2 (by rfl) ⟨25590, by rfl⟩) (B 51181 (by norm_num) ⟨25590, by rfl⟩ (by norm_num))
theorem R68245 : Reach 68245 := rs (se 6 (by rfl) ⟨1599, by rfl⟩) (B 3199 (by norm_num) ⟨1599, by rfl⟩ (by norm_num))
theorem R68249 : Reach 68249 := rs (se 2 (by rfl) ⟨25593, by rfl⟩) (B 51187 (by norm_num) ⟨25593, by rfl⟩ (by norm_num))
theorem R101021 : Reach 101021 := rs (se 3 (by rfl) ⟨18941, by rfl⟩) (B 37883 (by norm_num) ⟨18941, by rfl⟩ (by norm_num))
theorem R68253 : Reach 68253 := rs (se 3 (by rfl) ⟨12797, by rfl⟩) (B 25595 (by norm_num) ⟨12797, by rfl⟩ (by norm_num))
theorem R68257 : Reach 68257 := rs (se 2 (by rfl) ⟨25596, by rfl⟩) (B 51193 (by norm_num) ⟨25596, by rfl⟩ (by norm_num))
theorem R68261 : Reach 68261 := rs (se 4 (by rfl) ⟨6399, by rfl⟩) (B 12799 (by norm_num) ⟨6399, by rfl⟩ (by norm_num))
theorem R68265 : Reach 68265 := rs (se 2 (by rfl) ⟨25599, by rfl⟩) (B 51199 (by norm_num) ⟨25599, by rfl⟩ (by norm_num))
theorem R68269 : Reach 68269 := rs (se 3 (by rfl) ⟨12800, by rfl⟩) (B 25601 (by norm_num) ⟨12800, by rfl⟩ (by norm_num))
theorem R68273 : Reach 68273 := rs (se 2 (by rfl) ⟨25602, by rfl⟩) (B 51205 (by norm_num) ⟨25602, by rfl⟩ (by norm_num))
theorem R101045 : Reach 101045 := rs (se 5 (by rfl) ⟨4736, by rfl⟩) (B 9473 (by norm_num) ⟨4736, by rfl⟩ (by norm_num))
theorem R68277 : Reach 68277 := rs (se 5 (by rfl) ⟨3200, by rfl⟩) (B 6401 (by norm_num) ⟨3200, by rfl⟩ (by norm_num))
theorem R68281 : Reach 68281 := rs (se 2 (by rfl) ⟨25605, by rfl⟩) (B 51211 (by norm_num) ⟨25605, by rfl⟩ (by norm_num))
theorem R68285 : Reach 68285 := rs (se 3 (by rfl) ⟨12803, by rfl⟩) (B 25607 (by norm_num) ⟨12803, by rfl⟩ (by norm_num))
theorem R68289 : Reach 68289 := rs (se 2 (by rfl) ⟨25608, by rfl⟩) (B 51217 (by norm_num) ⟨25608, by rfl⟩ (by norm_num))
theorem R68293 : Reach 68293 := rs (se 4 (by rfl) ⟨6402, by rfl⟩) (B 12805 (by norm_num) ⟨6402, by rfl⟩ (by norm_num))
theorem R133829 : Reach 133829 := rs (se 4 (by rfl) ⟨12546, by rfl⟩) (B 25093 (by norm_num) ⟨12546, by rfl⟩ (by norm_num))
theorem R68297 : Reach 68297 := rs (se 2 (by rfl) ⟨25611, by rfl⟩) (B 51223 (by norm_num) ⟨25611, by rfl⟩ (by norm_num))
theorem R101069 : Reach 101069 := rs (se 3 (by rfl) ⟨18950, by rfl⟩) (B 37901 (by norm_num) ⟨18950, by rfl⟩ (by norm_num))
theorem R68301 : Reach 68301 := rs (se 3 (by rfl) ⟨12806, by rfl⟩) (B 25613 (by norm_num) ⟨12806, by rfl⟩ (by norm_num))
theorem R68305 : Reach 68305 := rs (se 2 (by rfl) ⟨25614, by rfl⟩) (B 51229 (by norm_num) ⟨25614, by rfl⟩ (by norm_num))
theorem R68309 : Reach 68309 := rs (se 7 (by rfl) ⟨800, by rfl⟩) (B 1601 (by norm_num) ⟨800, by rfl⟩ (by norm_num))
theorem R68313 : Reach 68313 := rs (se 2 (by rfl) ⟨25617, by rfl⟩) (B 51235 (by norm_num) ⟨25617, by rfl⟩ (by norm_num))
theorem R68317 : Reach 68317 := rs (se 3 (by rfl) ⟨12809, by rfl⟩) (B 25619 (by norm_num) ⟨12809, by rfl⟩ (by norm_num))
theorem R68321 : Reach 68321 := rs (se 2 (by rfl) ⟨25620, by rfl⟩) (B 51241 (by norm_num) ⟨25620, by rfl⟩ (by norm_num))
theorem R101093 : Reach 101093 := rs (se 4 (by rfl) ⟨9477, by rfl⟩) (B 18955 (by norm_num) ⟨9477, by rfl⟩ (by norm_num))
theorem R68325 : Reach 68325 := rs (se 4 (by rfl) ⟨6405, by rfl⟩) (B 12811 (by norm_num) ⟨6405, by rfl⟩ (by norm_num))
theorem R68329 : Reach 68329 := rs (se 2 (by rfl) ⟨25623, by rfl⟩) (B 51247 (by norm_num) ⟨25623, by rfl⟩ (by norm_num))
theorem R68333 : Reach 68333 := rs (se 3 (by rfl) ⟨12812, by rfl⟩) (B 25625 (by norm_num) ⟨12812, by rfl⟩ (by norm_num))
theorem R68337 : Reach 68337 := rs (se 2 (by rfl) ⟨25626, by rfl⟩) (B 51253 (by norm_num) ⟨25626, by rfl⟩ (by norm_num))
theorem R68341 : Reach 68341 := rs (se 5 (by rfl) ⟨3203, by rfl⟩) (B 6407 (by norm_num) ⟨3203, by rfl⟩ (by norm_num))
theorem R68345 : Reach 68345 := rs (se 2 (by rfl) ⟨25629, by rfl⟩) (B 51259 (by norm_num) ⟨25629, by rfl⟩ (by norm_num))
theorem R101117 : Reach 101117 := rs (se 3 (by rfl) ⟨18959, by rfl⟩) (B 37919 (by norm_num) ⟨18959, by rfl⟩ (by norm_num))
theorem R68349 : Reach 68349 := rs (se 3 (by rfl) ⟨12815, by rfl⟩) (B 25631 (by norm_num) ⟨12815, by rfl⟩ (by norm_num))
theorem R68353 : Reach 68353 := rs (se 2 (by rfl) ⟨25632, by rfl⟩) (B 51265 (by norm_num) ⟨25632, by rfl⟩ (by norm_num))
theorem R68357 : Reach 68357 := rs (se 4 (by rfl) ⟨6408, by rfl⟩) (B 12817 (by norm_num) ⟨6408, by rfl⟩ (by norm_num))
theorem R68361 : Reach 68361 := rs (se 2 (by rfl) ⟨25635, by rfl⟩) (B 51271 (by norm_num) ⟨25635, by rfl⟩ (by norm_num))
theorem R68365 : Reach 68365 := rs (se 3 (by rfl) ⟨12818, by rfl⟩) (B 25637 (by norm_num) ⟨12818, by rfl⟩ (by norm_num))
theorem R68369 : Reach 68369 := rs (se 2 (by rfl) ⟨25638, by rfl⟩) (B 51277 (by norm_num) ⟨25638, by rfl⟩ (by norm_num))
theorem R101141 : Reach 101141 := rs (se 6 (by rfl) ⟨2370, by rfl⟩) (B 4741 (by norm_num) ⟨2370, by rfl⟩ (by norm_num))
theorem R68373 : Reach 68373 := rs (se 6 (by rfl) ⟨1602, by rfl⟩) (B 3205 (by norm_num) ⟨1602, by rfl⟩ (by norm_num))
theorem R68377 : Reach 68377 := rs (se 2 (by rfl) ⟨25641, by rfl⟩) (B 51283 (by norm_num) ⟨25641, by rfl⟩ (by norm_num))
theorem R68381 : Reach 68381 := rs (se 3 (by rfl) ⟨12821, by rfl⟩) (B 25643 (by norm_num) ⟨12821, by rfl⟩ (by norm_num))
theorem R68385 : Reach 68385 := rs (se 2 (by rfl) ⟨25644, by rfl⟩) (B 51289 (by norm_num) ⟨25644, by rfl⟩ (by norm_num))
theorem R68389 : Reach 68389 := rs (se 4 (by rfl) ⟨6411, by rfl⟩) (B 12823 (by norm_num) ⟨6411, by rfl⟩ (by norm_num))
theorem R68393 : Reach 68393 := rs (se 2 (by rfl) ⟨25647, by rfl⟩) (B 51295 (by norm_num) ⟨25647, by rfl⟩ (by norm_num))
theorem R101165 : Reach 101165 := rs (se 3 (by rfl) ⟨18968, by rfl⟩) (B 37937 (by norm_num) ⟨18968, by rfl⟩ (by norm_num))
theorem R68397 : Reach 68397 := rs (se 3 (by rfl) ⟨12824, by rfl⟩) (B 25649 (by norm_num) ⟨12824, by rfl⟩ (by norm_num))
theorem R68401 : Reach 68401 := rs (se 2 (by rfl) ⟨25650, by rfl⟩) (B 51301 (by norm_num) ⟨25650, by rfl⟩ (by norm_num))
theorem R68405 : Reach 68405 := rs (se 5 (by rfl) ⟨3206, by rfl⟩) (B 6413 (by norm_num) ⟨3206, by rfl⟩ (by norm_num))
theorem R68409 : Reach 68409 := rs (se 2 (by rfl) ⟨25653, by rfl⟩) (B 51307 (by norm_num) ⟨25653, by rfl⟩ (by norm_num))
theorem R68413 : Reach 68413 := rs (se 3 (by rfl) ⟨12827, by rfl⟩) (B 25655 (by norm_num) ⟨12827, by rfl⟩ (by norm_num))
theorem R68417 : Reach 68417 := rs (se 2 (by rfl) ⟨25656, by rfl⟩) (B 51313 (by norm_num) ⟨25656, by rfl⟩ (by norm_num))
theorem R101189 : Reach 101189 := rs (se 4 (by rfl) ⟨9486, by rfl⟩) (B 18973 (by norm_num) ⟨9486, by rfl⟩ (by norm_num))
theorem R68421 : Reach 68421 := rs (se 4 (by rfl) ⟨6414, by rfl⟩) (B 12829 (by norm_num) ⟨6414, by rfl⟩ (by norm_num))
theorem R68425 : Reach 68425 := rs (se 2 (by rfl) ⟨25659, by rfl⟩) (B 51319 (by norm_num) ⟨25659, by rfl⟩ (by norm_num))
theorem R68429 : Reach 68429 := rs (se 3 (by rfl) ⟨12830, by rfl⟩) (B 25661 (by norm_num) ⟨12830, by rfl⟩ (by norm_num))
theorem R68433 : Reach 68433 := rs (se 2 (by rfl) ⟨25662, by rfl⟩) (B 51325 (by norm_num) ⟨25662, by rfl⟩ (by norm_num))
theorem R68437 : Reach 68437 := rs (se 9 (by rfl) ⟨200, by rfl⟩) (B 401 (by norm_num) ⟨200, by rfl⟩ (by norm_num))
theorem R68441 : Reach 68441 := rs (se 2 (by rfl) ⟨25665, by rfl⟩) (B 51331 (by norm_num) ⟨25665, by rfl⟩ (by norm_num))
theorem R101213 : Reach 101213 := rs (se 3 (by rfl) ⟨18977, by rfl⟩) (B 37955 (by norm_num) ⟨18977, by rfl⟩ (by norm_num))
theorem R68445 : Reach 68445 := rs (se 3 (by rfl) ⟨12833, by rfl⟩) (B 25667 (by norm_num) ⟨12833, by rfl⟩ (by norm_num))
theorem R68449 : Reach 68449 := rs (se 2 (by rfl) ⟨25668, by rfl⟩) (B 51337 (by norm_num) ⟨25668, by rfl⟩ (by norm_num))
theorem R68453 : Reach 68453 := rs (se 4 (by rfl) ⟨6417, by rfl⟩) (B 12835 (by norm_num) ⟨6417, by rfl⟩ (by norm_num))
theorem R68457 : Reach 68457 := rs (se 2 (by rfl) ⟨25671, by rfl⟩) (B 51343 (by norm_num) ⟨25671, by rfl⟩ (by norm_num))
theorem R68461 : Reach 68461 := rs (se 3 (by rfl) ⟨12836, by rfl⟩) (B 25673 (by norm_num) ⟨12836, by rfl⟩ (by norm_num))
theorem R68465 : Reach 68465 := rs (se 2 (by rfl) ⟨25674, by rfl⟩) (B 51349 (by norm_num) ⟨25674, by rfl⟩ (by norm_num))
theorem R101237 : Reach 101237 := rs (se 5 (by rfl) ⟨4745, by rfl⟩) (B 9491 (by norm_num) ⟨4745, by rfl⟩ (by norm_num))
theorem R68469 : Reach 68469 := rs (se 5 (by rfl) ⟨3209, by rfl⟩) (B 6419 (by norm_num) ⟨3209, by rfl⟩ (by norm_num))
theorem R68473 : Reach 68473 := rs (se 2 (by rfl) ⟨25677, by rfl⟩) (B 51355 (by norm_num) ⟨25677, by rfl⟩ (by norm_num))
theorem R68477 : Reach 68477 := rs (se 3 (by rfl) ⟨12839, by rfl⟩) (B 25679 (by norm_num) ⟨12839, by rfl⟩ (by norm_num))
theorem R68481 : Reach 68481 := rs (se 2 (by rfl) ⟨25680, by rfl⟩) (B 51361 (by norm_num) ⟨25680, by rfl⟩ (by norm_num))
theorem R68485 : Reach 68485 := rs (se 4 (by rfl) ⟨6420, by rfl⟩) (B 12841 (by norm_num) ⟨6420, by rfl⟩ (by norm_num))
theorem R68489 : Reach 68489 := rs (se 2 (by rfl) ⟨25683, by rfl⟩) (B 51367 (by norm_num) ⟨25683, by rfl⟩ (by norm_num))
theorem R101261 : Reach 101261 := rs (se 3 (by rfl) ⟨18986, by rfl⟩) (B 37973 (by norm_num) ⟨18986, by rfl⟩ (by norm_num))
theorem R68493 : Reach 68493 := rs (se 3 (by rfl) ⟨12842, by rfl⟩) (B 25685 (by norm_num) ⟨12842, by rfl⟩ (by norm_num))
theorem R68497 : Reach 68497 := rs (se 2 (by rfl) ⟨25686, by rfl⟩) (B 51373 (by norm_num) ⟨25686, by rfl⟩ (by norm_num))
theorem R68501 : Reach 68501 := rs (se 6 (by rfl) ⟨1605, by rfl⟩) (B 3211 (by norm_num) ⟨1605, by rfl⟩ (by norm_num))
theorem R297877 : Reach 297877 := rs (se 6 (by rfl) ⟨6981, by rfl⟩) (B 13963 (by norm_num) ⟨6981, by rfl⟩ (by norm_num))
theorem R68505 : Reach 68505 := rs (se 2 (by rfl) ⟨25689, by rfl⟩) (B 51379 (by norm_num) ⟨25689, by rfl⟩ (by norm_num))
theorem R68509 : Reach 68509 := rs (se 3 (by rfl) ⟨12845, by rfl⟩) (B 25691 (by norm_num) ⟨12845, by rfl⟩ (by norm_num))
theorem R134045 : Reach 134045 := rs (se 3 (by rfl) ⟨25133, by rfl⟩) (B 50267 (by norm_num) ⟨25133, by rfl⟩ (by norm_num))
theorem R68513 : Reach 68513 := rs (se 2 (by rfl) ⟨25692, by rfl⟩) (B 51385 (by norm_num) ⟨25692, by rfl⟩ (by norm_num))
theorem R101285 : Reach 101285 := rs (se 4 (by rfl) ⟨9495, by rfl⟩) (B 18991 (by norm_num) ⟨9495, by rfl⟩ (by norm_num))
theorem R68517 : Reach 68517 := rs (se 4 (by rfl) ⟨6423, by rfl⟩) (B 12847 (by norm_num) ⟨6423, by rfl⟩ (by norm_num))
theorem R68521 : Reach 68521 := rs (se 2 (by rfl) ⟨25695, by rfl⟩) (B 51391 (by norm_num) ⟨25695, by rfl⟩ (by norm_num))
theorem R68525 : Reach 68525 := rs (se 3 (by rfl) ⟨12848, by rfl⟩) (B 25697 (by norm_num) ⟨12848, by rfl⟩ (by norm_num))
theorem R68529 : Reach 68529 := rs (se 2 (by rfl) ⟨25698, by rfl⟩) (B 51397 (by norm_num) ⟨25698, by rfl⟩ (by norm_num))
theorem R68533 : Reach 68533 := rs (se 5 (by rfl) ⟨3212, by rfl⟩) (B 6425 (by norm_num) ⟨3212, by rfl⟩ (by norm_num))
theorem R68537 : Reach 68537 := rs (se 2 (by rfl) ⟨25701, by rfl⟩) (B 51403 (by norm_num) ⟨25701, by rfl⟩ (by norm_num))
theorem R101309 : Reach 101309 := rs (se 3 (by rfl) ⟨18995, by rfl⟩) (B 37991 (by norm_num) ⟨18995, by rfl⟩ (by norm_num))
theorem R68541 : Reach 68541 := rs (se 3 (by rfl) ⟨12851, by rfl⟩) (B 25703 (by norm_num) ⟨12851, by rfl⟩ (by norm_num))
theorem R68545 : Reach 68545 := rs (se 2 (by rfl) ⟨25704, by rfl⟩) (B 51409 (by norm_num) ⟨25704, by rfl⟩ (by norm_num))
theorem R68549 : Reach 68549 := rs (se 4 (by rfl) ⟨6426, by rfl⟩) (B 12853 (by norm_num) ⟨6426, by rfl⟩ (by norm_num))
theorem R68553 : Reach 68553 := rs (se 2 (by rfl) ⟨25707, by rfl⟩) (B 51415 (by norm_num) ⟨25707, by rfl⟩ (by norm_num))
theorem R68557 : Reach 68557 := rs (se 3 (by rfl) ⟨12854, by rfl⟩) (B 25709 (by norm_num) ⟨12854, by rfl⟩ (by norm_num))
theorem R68561 : Reach 68561 := rs (se 2 (by rfl) ⟨25710, by rfl⟩) (B 51421 (by norm_num) ⟨25710, by rfl⟩ (by norm_num))
theorem R101333 : Reach 101333 := rs (se 7 (by rfl) ⟨1187, by rfl⟩) (B 2375 (by norm_num) ⟨1187, by rfl⟩ (by norm_num))
theorem R68565 : Reach 68565 := rs (se 7 (by rfl) ⟨803, by rfl⟩) (B 1607 (by norm_num) ⟨803, by rfl⟩ (by norm_num))
theorem R68569 : Reach 68569 := rs (se 2 (by rfl) ⟨25713, by rfl⟩) (B 51427 (by norm_num) ⟨25713, by rfl⟩ (by norm_num))
theorem R68573 : Reach 68573 := rs (se 3 (by rfl) ⟨12857, by rfl⟩) (B 25715 (by norm_num) ⟨12857, by rfl⟩ (by norm_num))
theorem R68577 : Reach 68577 := rs (se 2 (by rfl) ⟨25716, by rfl⟩) (B 51433 (by norm_num) ⟨25716, by rfl⟩ (by norm_num))
theorem R68581 : Reach 68581 := rs (se 4 (by rfl) ⟨6429, by rfl⟩) (B 12859 (by norm_num) ⟨6429, by rfl⟩ (by norm_num))
theorem R68585 : Reach 68585 := rs (se 2 (by rfl) ⟨25719, by rfl⟩) (B 51439 (by norm_num) ⟨25719, by rfl⟩ (by norm_num))
theorem R101357 : Reach 101357 := rs (se 3 (by rfl) ⟨19004, by rfl⟩) (B 38009 (by norm_num) ⟨19004, by rfl⟩ (by norm_num))
theorem R68589 : Reach 68589 := rs (se 3 (by rfl) ⟨12860, by rfl⟩) (B 25721 (by norm_num) ⟨12860, by rfl⟩ (by norm_num))
theorem R68593 : Reach 68593 := rs (se 2 (by rfl) ⟨25722, by rfl⟩) (B 51445 (by norm_num) ⟨25722, by rfl⟩ (by norm_num))
theorem R68597 : Reach 68597 := rs (se 5 (by rfl) ⟨3215, by rfl⟩) (B 6431 (by norm_num) ⟨3215, by rfl⟩ (by norm_num))
theorem R68601 : Reach 68601 := rs (se 2 (by rfl) ⟨25725, by rfl⟩) (B 51451 (by norm_num) ⟨25725, by rfl⟩ (by norm_num))
theorem R68605 : Reach 68605 := rs (se 3 (by rfl) ⟨12863, by rfl⟩) (B 25727 (by norm_num) ⟨12863, by rfl⟩ (by norm_num))
theorem R68609 : Reach 68609 := rs (se 2 (by rfl) ⟨25728, by rfl⟩) (B 51457 (by norm_num) ⟨25728, by rfl⟩ (by norm_num))
theorem R101381 : Reach 101381 := rs (se 4 (by rfl) ⟨9504, by rfl⟩) (B 19009 (by norm_num) ⟨9504, by rfl⟩ (by norm_num))
theorem R68613 : Reach 68613 := rs (se 4 (by rfl) ⟨6432, by rfl⟩) (B 12865 (by norm_num) ⟨6432, by rfl⟩ (by norm_num))
theorem R68617 : Reach 68617 := rs (se 2 (by rfl) ⟨25731, by rfl⟩) (B 51463 (by norm_num) ⟨25731, by rfl⟩ (by norm_num))
theorem R68621 : Reach 68621 := rs (se 3 (by rfl) ⟨12866, by rfl⟩) (B 25733 (by norm_num) ⟨12866, by rfl⟩ (by norm_num))
theorem R68625 : Reach 68625 := rs (se 2 (by rfl) ⟨25734, by rfl⟩) (B 51469 (by norm_num) ⟨25734, by rfl⟩ (by norm_num))
theorem R68629 : Reach 68629 := rs (se 6 (by rfl) ⟨1608, by rfl⟩) (B 3217 (by norm_num) ⟨1608, by rfl⟩ (by norm_num))
theorem R232469 : Reach 232469 := rs (se 6 (by rfl) ⟨5448, by rfl⟩) (B 10897 (by norm_num) ⟨5448, by rfl⟩ (by norm_num))
theorem R68633 : Reach 68633 := rs (se 2 (by rfl) ⟨25737, by rfl⟩) (B 51475 (by norm_num) ⟨25737, by rfl⟩ (by norm_num))
theorem R101405 : Reach 101405 := rs (se 3 (by rfl) ⟨19013, by rfl⟩) (B 38027 (by norm_num) ⟨19013, by rfl⟩ (by norm_num))
theorem R68637 : Reach 68637 := rs (se 3 (by rfl) ⟨12869, by rfl⟩) (B 25739 (by norm_num) ⟨12869, by rfl⟩ (by norm_num))
theorem R68641 : Reach 68641 := rs (se 2 (by rfl) ⟨25740, by rfl⟩) (B 51481 (by norm_num) ⟨25740, by rfl⟩ (by norm_num))
theorem R68645 : Reach 68645 := rs (se 4 (by rfl) ⟨6435, by rfl⟩) (B 12871 (by norm_num) ⟨6435, by rfl⟩ (by norm_num))
theorem R68649 : Reach 68649 := rs (se 2 (by rfl) ⟨25743, by rfl⟩) (B 51487 (by norm_num) ⟨25743, by rfl⟩ (by norm_num))
theorem R68653 : Reach 68653 := rs (se 3 (by rfl) ⟨12872, by rfl⟩) (B 25745 (by norm_num) ⟨12872, by rfl⟩ (by norm_num))
theorem R68657 : Reach 68657 := rs (se 2 (by rfl) ⟨25746, by rfl⟩) (B 51493 (by norm_num) ⟨25746, by rfl⟩ (by norm_num))
theorem R101429 : Reach 101429 := rs (se 5 (by rfl) ⟨4754, by rfl⟩) (B 9509 (by norm_num) ⟨4754, by rfl⟩ (by norm_num))
theorem R68661 : Reach 68661 := rs (se 5 (by rfl) ⟨3218, by rfl⟩) (B 6437 (by norm_num) ⟨3218, by rfl⟩ (by norm_num))
theorem R68665 : Reach 68665 := rs (se 2 (by rfl) ⟨25749, by rfl⟩) (B 51499 (by norm_num) ⟨25749, by rfl⟩ (by norm_num))
theorem R68669 : Reach 68669 := rs (se 3 (by rfl) ⟨12875, by rfl⟩) (B 25751 (by norm_num) ⟨12875, by rfl⟩ (by norm_num))
theorem R68673 : Reach 68673 := rs (se 2 (by rfl) ⟨25752, by rfl⟩) (B 51505 (by norm_num) ⟨25752, by rfl⟩ (by norm_num))
theorem R68677 : Reach 68677 := rs (se 4 (by rfl) ⟨6438, by rfl⟩) (B 12877 (by norm_num) ⟨6438, by rfl⟩ (by norm_num))
theorem R68681 : Reach 68681 := rs (se 2 (by rfl) ⟨25755, by rfl⟩) (B 51511 (by norm_num) ⟨25755, by rfl⟩ (by norm_num))
theorem R101453 : Reach 101453 := rs (se 3 (by rfl) ⟨19022, by rfl⟩) (B 38045 (by norm_num) ⟨19022, by rfl⟩ (by norm_num))
theorem R68685 : Reach 68685 := rs (se 3 (by rfl) ⟨12878, by rfl⟩) (B 25757 (by norm_num) ⟨12878, by rfl⟩ (by norm_num))
theorem R68689 : Reach 68689 := rs (se 2 (by rfl) ⟨25758, by rfl⟩) (B 51517 (by norm_num) ⟨25758, by rfl⟩ (by norm_num))
theorem R68693 : Reach 68693 := rs (se 8 (by rfl) ⟨402, by rfl⟩) (B 805 (by norm_num) ⟨402, by rfl⟩ (by norm_num))
theorem R68697 : Reach 68697 := rs (se 2 (by rfl) ⟨25761, by rfl⟩) (B 51523 (by norm_num) ⟨25761, by rfl⟩ (by norm_num))
theorem R68701 : Reach 68701 := rs (se 3 (by rfl) ⟨12881, by rfl⟩) (B 25763 (by norm_num) ⟨12881, by rfl⟩ (by norm_num))
theorem R68705 : Reach 68705 := rs (se 2 (by rfl) ⟨25764, by rfl⟩) (B 51529 (by norm_num) ⟨25764, by rfl⟩ (by norm_num))
theorem R101477 : Reach 101477 := rs (se 4 (by rfl) ⟨9513, by rfl⟩) (B 19027 (by norm_num) ⟨9513, by rfl⟩ (by norm_num))
theorem R68709 : Reach 68709 := rs (se 4 (by rfl) ⟨6441, by rfl⟩) (B 12883 (by norm_num) ⟨6441, by rfl⟩ (by norm_num))
theorem R68713 : Reach 68713 := rs (se 2 (by rfl) ⟨25767, by rfl⟩) (B 51535 (by norm_num) ⟨25767, by rfl⟩ (by norm_num))
theorem R68717 : Reach 68717 := rs (se 3 (by rfl) ⟨12884, by rfl⟩) (B 25769 (by norm_num) ⟨12884, by rfl⟩ (by norm_num))
theorem R68721 : Reach 68721 := rs (se 2 (by rfl) ⟨25770, by rfl⟩) (B 51541 (by norm_num) ⟨25770, by rfl⟩ (by norm_num))
theorem R68725 : Reach 68725 := rs (se 5 (by rfl) ⟨3221, by rfl⟩) (B 6443 (by norm_num) ⟨3221, by rfl⟩ (by norm_num))
theorem R68729 : Reach 68729 := rs (se 2 (by rfl) ⟨25773, by rfl⟩) (B 51547 (by norm_num) ⟨25773, by rfl⟩ (by norm_num))
theorem R101501 : Reach 101501 := rs (se 3 (by rfl) ⟨19031, by rfl⟩) (B 38063 (by norm_num) ⟨19031, by rfl⟩ (by norm_num))
theorem R68733 : Reach 68733 := rs (se 3 (by rfl) ⟨12887, by rfl⟩) (B 25775 (by norm_num) ⟨12887, by rfl⟩ (by norm_num))
theorem R68737 : Reach 68737 := rs (se 2 (by rfl) ⟨25776, by rfl⟩) (B 51553 (by norm_num) ⟨25776, by rfl⟩ (by norm_num))
theorem R68741 : Reach 68741 := rs (se 4 (by rfl) ⟨6444, by rfl⟩) (B 12889 (by norm_num) ⟨6444, by rfl⟩ (by norm_num))
theorem R68745 : Reach 68745 := rs (se 2 (by rfl) ⟨25779, by rfl⟩) (B 51559 (by norm_num) ⟨25779, by rfl⟩ (by norm_num))
theorem R68749 : Reach 68749 := rs (se 3 (by rfl) ⟨12890, by rfl⟩) (B 25781 (by norm_num) ⟨12890, by rfl⟩ (by norm_num))
theorem R68753 : Reach 68753 := rs (se 2 (by rfl) ⟨25782, by rfl⟩) (B 51565 (by norm_num) ⟨25782, by rfl⟩ (by norm_num))
theorem R101525 : Reach 101525 := rs (se 6 (by rfl) ⟨2379, by rfl⟩) (B 4759 (by norm_num) ⟨2379, by rfl⟩ (by norm_num))
theorem R494741 : Reach 494741 := rs (se 6 (by rfl) ⟨11595, by rfl⟩) (B 23191 (by norm_num) ⟨11595, by rfl⟩ (by norm_num))
theorem R68757 : Reach 68757 := rs (se 6 (by rfl) ⟨1611, by rfl⟩) (B 3223 (by norm_num) ⟨1611, by rfl⟩ (by norm_num))
theorem R68761 : Reach 68761 := rs (se 2 (by rfl) ⟨25785, by rfl⟩) (B 51571 (by norm_num) ⟨25785, by rfl⟩ (by norm_num))
theorem R68765 : Reach 68765 := rs (se 3 (by rfl) ⟨12893, by rfl⟩) (B 25787 (by norm_num) ⟨12893, by rfl⟩ (by norm_num))
theorem R68769 : Reach 68769 := rs (se 2 (by rfl) ⟨25788, by rfl⟩) (B 51577 (by norm_num) ⟨25788, by rfl⟩ (by norm_num))
theorem R68773 : Reach 68773 := rs (se 4 (by rfl) ⟨6447, by rfl⟩) (B 12895 (by norm_num) ⟨6447, by rfl⟩ (by norm_num))
theorem R68777 : Reach 68777 := rs (se 2 (by rfl) ⟨25791, by rfl⟩) (B 51583 (by norm_num) ⟨25791, by rfl⟩ (by norm_num))
theorem R101549 : Reach 101549 := rs (se 3 (by rfl) ⟨19040, by rfl⟩) (B 38081 (by norm_num) ⟨19040, by rfl⟩ (by norm_num))
theorem R68781 : Reach 68781 := rs (se 3 (by rfl) ⟨12896, by rfl⟩) (B 25793 (by norm_num) ⟨12896, by rfl⟩ (by norm_num))
theorem R68785 : Reach 68785 := rs (se 2 (by rfl) ⟨25794, by rfl⟩) (B 51589 (by norm_num) ⟨25794, by rfl⟩ (by norm_num))
theorem R68789 : Reach 68789 := rs (se 5 (by rfl) ⟨3224, by rfl⟩) (B 6449 (by norm_num) ⟨3224, by rfl⟩ (by norm_num))
theorem R68793 : Reach 68793 := rs (se 2 (by rfl) ⟨25797, by rfl⟩) (B 51595 (by norm_num) ⟨25797, by rfl⟩ (by norm_num))
theorem R68797 : Reach 68797 := rs (se 3 (by rfl) ⟨12899, by rfl⟩) (B 25799 (by norm_num) ⟨12899, by rfl⟩ (by norm_num))
theorem R68801 : Reach 68801 := rs (se 2 (by rfl) ⟨25800, by rfl⟩) (B 51601 (by norm_num) ⟨25800, by rfl⟩ (by norm_num))
theorem R101573 : Reach 101573 := rs (se 4 (by rfl) ⟨9522, by rfl⟩) (B 19045 (by norm_num) ⟨9522, by rfl⟩ (by norm_num))
theorem R68805 : Reach 68805 := rs (se 4 (by rfl) ⟨6450, by rfl⟩) (B 12901 (by norm_num) ⟨6450, by rfl⟩ (by norm_num))
theorem R68809 : Reach 68809 := rs (se 2 (by rfl) ⟨25803, by rfl⟩) (B 51607 (by norm_num) ⟨25803, by rfl⟩ (by norm_num))
theorem R68813 : Reach 68813 := rs (se 3 (by rfl) ⟨12902, by rfl⟩) (B 25805 (by norm_num) ⟨12902, by rfl⟩ (by norm_num))
theorem R68817 : Reach 68817 := rs (se 2 (by rfl) ⟨25806, by rfl⟩) (B 51613 (by norm_num) ⟨25806, by rfl⟩ (by norm_num))
theorem R68821 : Reach 68821 := rs (se 7 (by rfl) ⟨806, by rfl⟩) (B 1613 (by norm_num) ⟨806, by rfl⟩ (by norm_num))
theorem R68825 : Reach 68825 := rs (se 2 (by rfl) ⟨25809, by rfl⟩) (B 51619 (by norm_num) ⟨25809, by rfl⟩ (by norm_num))
theorem R101597 : Reach 101597 := rs (se 3 (by rfl) ⟨19049, by rfl⟩) (B 38099 (by norm_num) ⟨19049, by rfl⟩ (by norm_num))
theorem R68829 : Reach 68829 := rs (se 3 (by rfl) ⟨12905, by rfl⟩) (B 25811 (by norm_num) ⟨12905, by rfl⟩ (by norm_num))
theorem R68833 : Reach 68833 := rs (se 2 (by rfl) ⟨25812, by rfl⟩) (B 51625 (by norm_num) ⟨25812, by rfl⟩ (by norm_num))
theorem R68837 : Reach 68837 := rs (se 4 (by rfl) ⟨6453, by rfl⟩) (B 12907 (by norm_num) ⟨6453, by rfl⟩ (by norm_num))
theorem R68841 : Reach 68841 := rs (se 2 (by rfl) ⟨25815, by rfl⟩) (B 51631 (by norm_num) ⟨25815, by rfl⟩ (by norm_num))
theorem R68845 : Reach 68845 := rs (se 3 (by rfl) ⟨12908, by rfl⟩) (B 25817 (by norm_num) ⟨12908, by rfl⟩ (by norm_num))
theorem R68849 : Reach 68849 := rs (se 2 (by rfl) ⟨25818, by rfl⟩) (B 51637 (by norm_num) ⟨25818, by rfl⟩ (by norm_num))
theorem R101621 : Reach 101621 := rs (se 5 (by rfl) ⟨4763, by rfl⟩) (B 9527 (by norm_num) ⟨4763, by rfl⟩ (by norm_num))
theorem R68853 : Reach 68853 := rs (se 5 (by rfl) ⟨3227, by rfl⟩) (B 6455 (by norm_num) ⟨3227, by rfl⟩ (by norm_num))
theorem R68857 : Reach 68857 := rs (se 2 (by rfl) ⟨25821, by rfl⟩) (B 51643 (by norm_num) ⟨25821, by rfl⟩ (by norm_num))
theorem R68861 : Reach 68861 := rs (se 3 (by rfl) ⟨12911, by rfl⟩) (B 25823 (by norm_num) ⟨12911, by rfl⟩ (by norm_num))
theorem R68865 : Reach 68865 := rs (se 2 (by rfl) ⟨25824, by rfl⟩) (B 51649 (by norm_num) ⟨25824, by rfl⟩ (by norm_num))
theorem R68869 : Reach 68869 := rs (se 4 (by rfl) ⟨6456, by rfl⟩) (B 12913 (by norm_num) ⟨6456, by rfl⟩ (by norm_num))
theorem R265477 : Reach 265477 := rs (se 4 (by rfl) ⟨24888, by rfl⟩) (B 49777 (by norm_num) ⟨24888, by rfl⟩ (by norm_num))
theorem R68873 : Reach 68873 := rs (se 2 (by rfl) ⟨25827, by rfl⟩) (B 51655 (by norm_num) ⟨25827, by rfl⟩ (by norm_num))
theorem R101645 : Reach 101645 := rs (se 3 (by rfl) ⟨19058, by rfl⟩) (B 38117 (by norm_num) ⟨19058, by rfl⟩ (by norm_num))
theorem R68877 : Reach 68877 := rs (se 3 (by rfl) ⟨12914, by rfl⟩) (B 25829 (by norm_num) ⟨12914, by rfl⟩ (by norm_num))
theorem R68881 : Reach 68881 := rs (se 2 (by rfl) ⟨25830, by rfl⟩) (B 51661 (by norm_num) ⟨25830, by rfl⟩ (by norm_num))
theorem R68885 : Reach 68885 := rs (se 6 (by rfl) ⟨1614, by rfl⟩) (B 3229 (by norm_num) ⟨1614, by rfl⟩ (by norm_num))
theorem R68889 : Reach 68889 := rs (se 2 (by rfl) ⟨25833, by rfl⟩) (B 51667 (by norm_num) ⟨25833, by rfl⟩ (by norm_num))
theorem R68893 : Reach 68893 := rs (se 3 (by rfl) ⟨12917, by rfl⟩) (B 25835 (by norm_num) ⟨12917, by rfl⟩ (by norm_num))
theorem R68897 : Reach 68897 := rs (se 2 (by rfl) ⟨25836, by rfl⟩) (B 51673 (by norm_num) ⟨25836, by rfl⟩ (by norm_num))
theorem R101669 : Reach 101669 := rs (se 4 (by rfl) ⟨9531, by rfl⟩) (B 19063 (by norm_num) ⟨9531, by rfl⟩ (by norm_num))
theorem R68901 : Reach 68901 := rs (se 4 (by rfl) ⟨6459, by rfl⟩) (B 12919 (by norm_num) ⟨6459, by rfl⟩ (by norm_num))
theorem R68905 : Reach 68905 := rs (se 2 (by rfl) ⟨25839, by rfl⟩) (B 51679 (by norm_num) ⟨25839, by rfl⟩ (by norm_num))
theorem R68909 : Reach 68909 := rs (se 3 (by rfl) ⟨12920, by rfl⟩) (B 25841 (by norm_num) ⟨12920, by rfl⟩ (by norm_num))
theorem R68913 : Reach 68913 := rs (se 2 (by rfl) ⟨25842, by rfl⟩) (B 51685 (by norm_num) ⟨25842, by rfl⟩ (by norm_num))
theorem R68917 : Reach 68917 := rs (se 5 (by rfl) ⟨3230, by rfl⟩) (B 6461 (by norm_num) ⟨3230, by rfl⟩ (by norm_num))
theorem R68921 : Reach 68921 := rs (se 2 (by rfl) ⟨25845, by rfl⟩) (B 51691 (by norm_num) ⟨25845, by rfl⟩ (by norm_num))
theorem R101693 : Reach 101693 := rs (se 3 (by rfl) ⟨19067, by rfl⟩) (B 38135 (by norm_num) ⟨19067, by rfl⟩ (by norm_num))
theorem R68925 : Reach 68925 := rs (se 3 (by rfl) ⟨12923, by rfl⟩) (B 25847 (by norm_num) ⟨12923, by rfl⟩ (by norm_num))
theorem R68929 : Reach 68929 := rs (se 2 (by rfl) ⟨25848, by rfl⟩) (B 51697 (by norm_num) ⟨25848, by rfl⟩ (by norm_num))
theorem R68933 : Reach 68933 := rs (se 4 (by rfl) ⟨6462, by rfl⟩) (B 12925 (by norm_num) ⟨6462, by rfl⟩ (by norm_num))
theorem R68937 : Reach 68937 := rs (se 2 (by rfl) ⟨25851, by rfl⟩) (B 51703 (by norm_num) ⟨25851, by rfl⟩ (by norm_num))
theorem R68941 : Reach 68941 := rs (se 3 (by rfl) ⟨12926, by rfl⟩) (B 25853 (by norm_num) ⟨12926, by rfl⟩ (by norm_num))
theorem R68945 : Reach 68945 := rs (se 2 (by rfl) ⟨25854, by rfl⟩) (B 51709 (by norm_num) ⟨25854, by rfl⟩ (by norm_num))
theorem R101717 : Reach 101717 := rs (se 11 (by rfl) ⟨74, by rfl⟩) (B 149 (by norm_num) ⟨74, by rfl⟩ (by norm_num))
theorem R68949 : Reach 68949 := rs (se 11 (by rfl) ⟨50, by rfl⟩) (B 101 (by norm_num) ⟨50, by rfl⟩ (by norm_num))
theorem R68953 : Reach 68953 := rs (se 2 (by rfl) ⟨25857, by rfl⟩) (B 51715 (by norm_num) ⟨25857, by rfl⟩ (by norm_num))
theorem R68957 : Reach 68957 := rs (se 3 (by rfl) ⟨12929, by rfl⟩) (B 25859 (by norm_num) ⟨12929, by rfl⟩ (by norm_num))
theorem R68961 : Reach 68961 := rs (se 2 (by rfl) ⟨25860, by rfl⟩) (B 51721 (by norm_num) ⟨25860, by rfl⟩ (by norm_num))
theorem R68965 : Reach 68965 := rs (se 4 (by rfl) ⟨6465, by rfl⟩) (B 12931 (by norm_num) ⟨6465, by rfl⟩ (by norm_num))
theorem R68969 : Reach 68969 := rs (se 2 (by rfl) ⟨25863, by rfl⟩) (B 51727 (by norm_num) ⟨25863, by rfl⟩ (by norm_num))
theorem R101741 : Reach 101741 := rs (se 3 (by rfl) ⟨19076, by rfl⟩) (B 38153 (by norm_num) ⟨19076, by rfl⟩ (by norm_num))
theorem R68973 : Reach 68973 := rs (se 3 (by rfl) ⟨12932, by rfl⟩) (B 25865 (by norm_num) ⟨12932, by rfl⟩ (by norm_num))
theorem R68977 : Reach 68977 := rs (se 2 (by rfl) ⟨25866, by rfl⟩) (B 51733 (by norm_num) ⟨25866, by rfl⟩ (by norm_num))
theorem R68981 : Reach 68981 := rs (se 5 (by rfl) ⟨3233, by rfl⟩) (B 6467 (by norm_num) ⟨3233, by rfl⟩ (by norm_num))
theorem R68985 : Reach 68985 := rs (se 2 (by rfl) ⟨25869, by rfl⟩) (B 51739 (by norm_num) ⟨25869, by rfl⟩ (by norm_num))
theorem R68989 : Reach 68989 := rs (se 3 (by rfl) ⟨12935, by rfl⟩) (B 25871 (by norm_num) ⟨12935, by rfl⟩ (by norm_num))
theorem R68993 : Reach 68993 := rs (se 2 (by rfl) ⟨25872, by rfl⟩) (B 51745 (by norm_num) ⟨25872, by rfl⟩ (by norm_num))
theorem R101765 : Reach 101765 := rs (se 4 (by rfl) ⟨9540, by rfl⟩) (B 19081 (by norm_num) ⟨9540, by rfl⟩ (by norm_num))
theorem R68997 : Reach 68997 := rs (se 4 (by rfl) ⟨6468, by rfl⟩) (B 12937 (by norm_num) ⟨6468, by rfl⟩ (by norm_num))
theorem R69001 : Reach 69001 := rs (se 2 (by rfl) ⟨25875, by rfl⟩) (B 51751 (by norm_num) ⟨25875, by rfl⟩ (by norm_num))
theorem R69005 : Reach 69005 := rs (se 3 (by rfl) ⟨12938, by rfl⟩) (B 25877 (by norm_num) ⟨12938, by rfl⟩ (by norm_num))
theorem R69009 : Reach 69009 := rs (se 2 (by rfl) ⟨25878, by rfl⟩) (B 51757 (by norm_num) ⟨25878, by rfl⟩ (by norm_num))
theorem R69013 : Reach 69013 := rs (se 6 (by rfl) ⟨1617, by rfl⟩) (B 3235 (by norm_num) ⟨1617, by rfl⟩ (by norm_num))
theorem R69017 : Reach 69017 := rs (se 2 (by rfl) ⟨25881, by rfl⟩) (B 51763 (by norm_num) ⟨25881, by rfl⟩ (by norm_num))
theorem R101789 : Reach 101789 := rs (se 3 (by rfl) ⟨19085, by rfl⟩) (B 38171 (by norm_num) ⟨19085, by rfl⟩ (by norm_num))
theorem R69021 : Reach 69021 := rs (se 3 (by rfl) ⟨12941, by rfl⟩) (B 25883 (by norm_num) ⟨12941, by rfl⟩ (by norm_num))
theorem R69025 : Reach 69025 := rs (se 2 (by rfl) ⟨25884, by rfl⟩) (B 51769 (by norm_num) ⟨25884, by rfl⟩ (by norm_num))
theorem R69029 : Reach 69029 := rs (se 4 (by rfl) ⟨6471, by rfl⟩) (B 12943 (by norm_num) ⟨6471, by rfl⟩ (by norm_num))
theorem R69033 : Reach 69033 := rs (se 2 (by rfl) ⟨25887, by rfl⟩) (B 51775 (by norm_num) ⟨25887, by rfl⟩ (by norm_num))
theorem R69037 : Reach 69037 := rs (se 3 (by rfl) ⟨12944, by rfl⟩) (B 25889 (by norm_num) ⟨12944, by rfl⟩ (by norm_num))
theorem R69041 : Reach 69041 := rs (se 2 (by rfl) ⟨25890, by rfl⟩) (B 51781 (by norm_num) ⟨25890, by rfl⟩ (by norm_num))
theorem R101813 : Reach 101813 := rs (se 5 (by rfl) ⟨4772, by rfl⟩) (B 9545 (by norm_num) ⟨4772, by rfl⟩ (by norm_num))
theorem R69045 : Reach 69045 := rs (se 5 (by rfl) ⟨3236, by rfl⟩) (B 6473 (by norm_num) ⟨3236, by rfl⟩ (by norm_num))
theorem R69049 : Reach 69049 := rs (se 2 (by rfl) ⟨25893, by rfl⟩) (B 51787 (by norm_num) ⟨25893, by rfl⟩ (by norm_num))
theorem R69053 : Reach 69053 := rs (se 3 (by rfl) ⟨12947, by rfl⟩) (B 25895 (by norm_num) ⟨12947, by rfl⟩ (by norm_num))
theorem R69057 : Reach 69057 := rs (se 2 (by rfl) ⟨25896, by rfl⟩) (B 51793 (by norm_num) ⟨25896, by rfl⟩ (by norm_num))
theorem R232901 : Reach 232901 := rs (se 4 (by rfl) ⟨21834, by rfl⟩) (B 43669 (by norm_num) ⟨21834, by rfl⟩ (by norm_num))
theorem R69061 : Reach 69061 := rs (se 4 (by rfl) ⟨6474, by rfl⟩) (B 12949 (by norm_num) ⟨6474, by rfl⟩ (by norm_num))
theorem R69065 : Reach 69065 := rs (se 2 (by rfl) ⟨25899, by rfl⟩) (B 51799 (by norm_num) ⟨25899, by rfl⟩ (by norm_num))
theorem R101837 : Reach 101837 := rs (se 3 (by rfl) ⟨19094, by rfl⟩) (B 38189 (by norm_num) ⟨19094, by rfl⟩ (by norm_num))
theorem R69069 : Reach 69069 := rs (se 3 (by rfl) ⟨12950, by rfl⟩) (B 25901 (by norm_num) ⟨12950, by rfl⟩ (by norm_num))
theorem R69073 : Reach 69073 := rs (se 2 (by rfl) ⟨25902, by rfl⟩) (B 51805 (by norm_num) ⟨25902, by rfl⟩ (by norm_num))
theorem R69077 : Reach 69077 := rs (se 7 (by rfl) ⟨809, by rfl⟩) (B 1619 (by norm_num) ⟨809, by rfl⟩ (by norm_num))
theorem R69081 : Reach 69081 := rs (se 2 (by rfl) ⟨25905, by rfl⟩) (B 51811 (by norm_num) ⟨25905, by rfl⟩ (by norm_num))
theorem R69085 : Reach 69085 := rs (se 3 (by rfl) ⟨12953, by rfl⟩) (B 25907 (by norm_num) ⟨12953, by rfl⟩ (by norm_num))
theorem R69089 : Reach 69089 := rs (se 2 (by rfl) ⟨25908, by rfl⟩) (B 51817 (by norm_num) ⟨25908, by rfl⟩ (by norm_num))
theorem R101861 : Reach 101861 := rs (se 4 (by rfl) ⟨9549, by rfl⟩) (B 19099 (by norm_num) ⟨9549, by rfl⟩ (by norm_num))
theorem R69093 : Reach 69093 := rs (se 4 (by rfl) ⟨6477, by rfl⟩) (B 12955 (by norm_num) ⟨6477, by rfl⟩ (by norm_num))
theorem R69097 : Reach 69097 := rs (se 2 (by rfl) ⟨25911, by rfl⟩) (B 51823 (by norm_num) ⟨25911, by rfl⟩ (by norm_num))
theorem R69101 : Reach 69101 := rs (se 3 (by rfl) ⟨12956, by rfl⟩) (B 25913 (by norm_num) ⟨12956, by rfl⟩ (by norm_num))
theorem R69105 : Reach 69105 := rs (se 2 (by rfl) ⟨25914, by rfl⟩) (B 51829 (by norm_num) ⟨25914, by rfl⟩ (by norm_num))
theorem R69109 : Reach 69109 := rs (se 5 (by rfl) ⟨3239, by rfl⟩) (B 6479 (by norm_num) ⟨3239, by rfl⟩ (by norm_num))
theorem R69113 : Reach 69113 := rs (se 2 (by rfl) ⟨25917, by rfl⟩) (B 51835 (by norm_num) ⟨25917, by rfl⟩ (by norm_num))
theorem R101885 : Reach 101885 := rs (se 3 (by rfl) ⟨19103, by rfl⟩) (B 38207 (by norm_num) ⟨19103, by rfl⟩ (by norm_num))
theorem R69117 : Reach 69117 := rs (se 3 (by rfl) ⟨12959, by rfl⟩) (B 25919 (by norm_num) ⟨12959, by rfl⟩ (by norm_num))
theorem R69121 : Reach 69121 := rs (se 2 (by rfl) ⟨25920, by rfl⟩) (B 51841 (by norm_num) ⟨25920, by rfl⟩ (by norm_num))
theorem R69125 : Reach 69125 := rs (se 4 (by rfl) ⟨6480, by rfl⟩) (B 12961 (by norm_num) ⟨6480, by rfl⟩ (by norm_num))
theorem R69129 : Reach 69129 := rs (se 2 (by rfl) ⟨25923, by rfl⟩) (B 51847 (by norm_num) ⟨25923, by rfl⟩ (by norm_num))
theorem R69133 : Reach 69133 := rs (se 3 (by rfl) ⟨12962, by rfl⟩) (B 25925 (by norm_num) ⟨12962, by rfl⟩ (by norm_num))
theorem R69137 : Reach 69137 := rs (se 2 (by rfl) ⟨25926, by rfl⟩) (B 51853 (by norm_num) ⟨25926, by rfl⟩ (by norm_num))
theorem R101909 : Reach 101909 := rs (se 6 (by rfl) ⟨2388, by rfl⟩) (B 4777 (by norm_num) ⟨2388, by rfl⟩ (by norm_num))
theorem R69141 : Reach 69141 := rs (se 6 (by rfl) ⟨1620, by rfl⟩) (B 3241 (by norm_num) ⟨1620, by rfl⟩ (by norm_num))
theorem R69145 : Reach 69145 := rs (se 2 (by rfl) ⟨25929, by rfl⟩) (B 51859 (by norm_num) ⟨25929, by rfl⟩ (by norm_num))
theorem R69149 : Reach 69149 := rs (se 3 (by rfl) ⟨12965, by rfl⟩) (B 25931 (by norm_num) ⟨12965, by rfl⟩ (by norm_num))
theorem R69153 : Reach 69153 := rs (se 2 (by rfl) ⟨25932, by rfl⟩) (B 51865 (by norm_num) ⟨25932, by rfl⟩ (by norm_num))
theorem R69157 : Reach 69157 := rs (se 4 (by rfl) ⟨6483, by rfl⟩) (B 12967 (by norm_num) ⟨6483, by rfl⟩ (by norm_num))
theorem R69161 : Reach 69161 := rs (se 2 (by rfl) ⟨25935, by rfl⟩) (B 51871 (by norm_num) ⟨25935, by rfl⟩ (by norm_num))
theorem R101933 : Reach 101933 := rs (se 3 (by rfl) ⟨19112, by rfl⟩) (B 38225 (by norm_num) ⟨19112, by rfl⟩ (by norm_num))
theorem R69165 : Reach 69165 := rs (se 3 (by rfl) ⟨12968, by rfl⟩) (B 25937 (by norm_num) ⟨12968, by rfl⟩ (by norm_num))
theorem R69169 : Reach 69169 := rs (se 2 (by rfl) ⟨25938, by rfl⟩) (B 51877 (by norm_num) ⟨25938, by rfl⟩ (by norm_num))
theorem R69173 : Reach 69173 := rs (se 5 (by rfl) ⟨3242, by rfl⟩) (B 6485 (by norm_num) ⟨3242, by rfl⟩ (by norm_num))
theorem R265781 : Reach 265781 := rs (se 5 (by rfl) ⟨12458, by rfl⟩) (B 24917 (by norm_num) ⟨12458, by rfl⟩ (by norm_num))
theorem R69177 : Reach 69177 := rs (se 2 (by rfl) ⟨25941, by rfl⟩) (B 51883 (by norm_num) ⟨25941, by rfl⟩ (by norm_num))
theorem R69181 : Reach 69181 := rs (se 3 (by rfl) ⟨12971, by rfl⟩) (B 25943 (by norm_num) ⟨12971, by rfl⟩ (by norm_num))
theorem R69185 : Reach 69185 := rs (se 2 (by rfl) ⟨25944, by rfl⟩) (B 51889 (by norm_num) ⟨25944, by rfl⟩ (by norm_num))
theorem R101957 : Reach 101957 := rs (se 4 (by rfl) ⟨9558, by rfl⟩) (B 19117 (by norm_num) ⟨9558, by rfl⟩ (by norm_num))
theorem R69189 : Reach 69189 := rs (se 4 (by rfl) ⟨6486, by rfl⟩) (B 12973 (by norm_num) ⟨6486, by rfl⟩ (by norm_num))
theorem R69193 : Reach 69193 := rs (se 2 (by rfl) ⟨25947, by rfl⟩) (B 51895 (by norm_num) ⟨25947, by rfl⟩ (by norm_num))
theorem R69197 : Reach 69197 := rs (se 3 (by rfl) ⟨12974, by rfl⟩) (B 25949 (by norm_num) ⟨12974, by rfl⟩ (by norm_num))
theorem R69201 : Reach 69201 := rs (se 2 (by rfl) ⟨25950, by rfl⟩) (B 51901 (by norm_num) ⟨25950, by rfl⟩ (by norm_num))
theorem R69205 : Reach 69205 := rs (se 8 (by rfl) ⟨405, by rfl⟩) (B 811 (by norm_num) ⟨405, by rfl⟩ (by norm_num))
theorem R69209 : Reach 69209 := rs (se 2 (by rfl) ⟨25953, by rfl⟩) (B 51907 (by norm_num) ⟨25953, by rfl⟩ (by norm_num))
theorem R101981 : Reach 101981 := rs (se 3 (by rfl) ⟨19121, by rfl⟩) (B 38243 (by norm_num) ⟨19121, by rfl⟩ (by norm_num))
theorem R69213 : Reach 69213 := rs (se 3 (by rfl) ⟨12977, by rfl⟩) (B 25955 (by norm_num) ⟨12977, by rfl⟩ (by norm_num))
theorem R69217 : Reach 69217 := rs (se 2 (by rfl) ⟨25956, by rfl⟩) (B 51913 (by norm_num) ⟨25956, by rfl⟩ (by norm_num))
theorem R69221 : Reach 69221 := rs (se 4 (by rfl) ⟨6489, by rfl⟩) (B 12979 (by norm_num) ⟨6489, by rfl⟩ (by norm_num))
theorem R69225 : Reach 69225 := rs (se 2 (by rfl) ⟨25959, by rfl⟩) (B 51919 (by norm_num) ⟨25959, by rfl⟩ (by norm_num))
theorem R69229 : Reach 69229 := rs (se 3 (by rfl) ⟨12980, by rfl⟩) (B 25961 (by norm_num) ⟨12980, by rfl⟩ (by norm_num))
theorem R69233 : Reach 69233 := rs (se 2 (by rfl) ⟨25962, by rfl⟩) (B 51925 (by norm_num) ⟨25962, by rfl⟩ (by norm_num))
theorem R102005 : Reach 102005 := rs (se 5 (by rfl) ⟨4781, by rfl⟩) (B 9563 (by norm_num) ⟨4781, by rfl⟩ (by norm_num))
theorem R69237 : Reach 69237 := rs (se 5 (by rfl) ⟨3245, by rfl⟩) (B 6491 (by norm_num) ⟨3245, by rfl⟩ (by norm_num))
theorem R69241 : Reach 69241 := rs (se 2 (by rfl) ⟨25965, by rfl⟩) (B 51931 (by norm_num) ⟨25965, by rfl⟩ (by norm_num))
theorem R69245 : Reach 69245 := rs (se 3 (by rfl) ⟨12983, by rfl⟩) (B 25967 (by norm_num) ⟨12983, by rfl⟩ (by norm_num))
theorem R69249 : Reach 69249 := rs (se 2 (by rfl) ⟨25968, by rfl⟩) (B 51937 (by norm_num) ⟨25968, by rfl⟩ (by norm_num))
theorem R69253 : Reach 69253 := rs (se 4 (by rfl) ⟨6492, by rfl⟩) (B 12985 (by norm_num) ⟨6492, by rfl⟩ (by norm_num))
theorem R69257 : Reach 69257 := rs (se 2 (by rfl) ⟨25971, by rfl⟩) (B 51943 (by norm_num) ⟨25971, by rfl⟩ (by norm_num))
theorem R102029 : Reach 102029 := rs (se 3 (by rfl) ⟨19130, by rfl⟩) (B 38261 (by norm_num) ⟨19130, by rfl⟩ (by norm_num))
theorem R69261 : Reach 69261 := rs (se 3 (by rfl) ⟨12986, by rfl⟩) (B 25973 (by norm_num) ⟨12986, by rfl⟩ (by norm_num))
theorem R134797 : Reach 134797 := rs (se 3 (by rfl) ⟨25274, by rfl⟩) (B 50549 (by norm_num) ⟨25274, by rfl⟩ (by norm_num))
theorem R69265 : Reach 69265 := rs (se 2 (by rfl) ⟨25974, by rfl⟩) (B 51949 (by norm_num) ⟨25974, by rfl⟩ (by norm_num))
theorem R69269 : Reach 69269 := rs (se 6 (by rfl) ⟨1623, by rfl⟩) (B 3247 (by norm_num) ⟨1623, by rfl⟩ (by norm_num))
theorem R69273 : Reach 69273 := rs (se 2 (by rfl) ⟨25977, by rfl⟩) (B 51955 (by norm_num) ⟨25977, by rfl⟩ (by norm_num))
theorem R69277 : Reach 69277 := rs (se 3 (by rfl) ⟨12989, by rfl⟩) (B 25979 (by norm_num) ⟨12989, by rfl⟩ (by norm_num))
theorem R69281 : Reach 69281 := rs (se 2 (by rfl) ⟨25980, by rfl⟩) (B 51961 (by norm_num) ⟨25980, by rfl⟩ (by norm_num))
theorem R102053 : Reach 102053 := rs (se 4 (by rfl) ⟨9567, by rfl⟩) (B 19135 (by norm_num) ⟨9567, by rfl⟩ (by norm_num))
theorem R69285 : Reach 69285 := rs (se 4 (by rfl) ⟨6495, by rfl⟩) (B 12991 (by norm_num) ⟨6495, by rfl⟩ (by norm_num))
theorem R69289 : Reach 69289 := rs (se 2 (by rfl) ⟨25983, by rfl⟩) (B 51967 (by norm_num) ⟨25983, by rfl⟩ (by norm_num))
theorem R69293 : Reach 69293 := rs (se 3 (by rfl) ⟨12992, by rfl⟩) (B 25985 (by norm_num) ⟨12992, by rfl⟩ (by norm_num))
theorem R69297 : Reach 69297 := rs (se 2 (by rfl) ⟨25986, by rfl⟩) (B 51973 (by norm_num) ⟨25986, by rfl⟩ (by norm_num))
theorem R69301 : Reach 69301 := rs (se 5 (by rfl) ⟨3248, by rfl⟩) (B 6497 (by norm_num) ⟨3248, by rfl⟩ (by norm_num))
theorem R69305 : Reach 69305 := rs (se 2 (by rfl) ⟨25989, by rfl⟩) (B 51979 (by norm_num) ⟨25989, by rfl⟩ (by norm_num))
theorem R102077 : Reach 102077 := rs (se 3 (by rfl) ⟨19139, by rfl⟩) (B 38279 (by norm_num) ⟨19139, by rfl⟩ (by norm_num))
theorem R69309 : Reach 69309 := rs (se 3 (by rfl) ⟨12995, by rfl⟩) (B 25991 (by norm_num) ⟨12995, by rfl⟩ (by norm_num))
theorem R69313 : Reach 69313 := rs (se 2 (by rfl) ⟨25992, by rfl⟩) (B 51985 (by norm_num) ⟨25992, by rfl⟩ (by norm_num))
theorem R69317 : Reach 69317 := rs (se 4 (by rfl) ⟨6498, by rfl⟩) (B 12997 (by norm_num) ⟨6498, by rfl⟩ (by norm_num))
theorem R69321 : Reach 69321 := rs (se 2 (by rfl) ⟨25995, by rfl⟩) (B 51991 (by norm_num) ⟨25995, by rfl⟩ (by norm_num))
theorem R69325 : Reach 69325 := rs (se 3 (by rfl) ⟨12998, by rfl⟩) (B 25997 (by norm_num) ⟨12998, by rfl⟩ (by norm_num))
theorem R69329 : Reach 69329 := rs (se 2 (by rfl) ⟨25998, by rfl⟩) (B 51997 (by norm_num) ⟨25998, by rfl⟩ (by norm_num))
theorem R102101 : Reach 102101 := rs (se 7 (by rfl) ⟨1196, by rfl⟩) (B 2393 (by norm_num) ⟨1196, by rfl⟩ (by norm_num))
theorem R69333 : Reach 69333 := rs (se 7 (by rfl) ⟨812, by rfl⟩) (B 1625 (by norm_num) ⟨812, by rfl⟩ (by norm_num))
theorem R69337 : Reach 69337 := rs (se 2 (by rfl) ⟨26001, by rfl⟩) (B 52003 (by norm_num) ⟨26001, by rfl⟩ (by norm_num))
theorem R69341 : Reach 69341 := rs (se 3 (by rfl) ⟨13001, by rfl⟩) (B 26003 (by norm_num) ⟨13001, by rfl⟩ (by norm_num))
theorem R69345 : Reach 69345 := rs (se 2 (by rfl) ⟨26004, by rfl⟩) (B 52009 (by norm_num) ⟨26004, by rfl⟩ (by norm_num))
theorem R69349 : Reach 69349 := rs (se 4 (by rfl) ⟨6501, by rfl⟩) (B 13003 (by norm_num) ⟨6501, by rfl⟩ (by norm_num))
theorem R69353 : Reach 69353 := rs (se 2 (by rfl) ⟨26007, by rfl⟩) (B 52015 (by norm_num) ⟨26007, by rfl⟩ (by norm_num))
theorem R102125 : Reach 102125 := rs (se 3 (by rfl) ⟨19148, by rfl⟩) (B 38297 (by norm_num) ⟨19148, by rfl⟩ (by norm_num))
theorem R69357 : Reach 69357 := rs (se 3 (by rfl) ⟨13004, by rfl⟩) (B 26009 (by norm_num) ⟨13004, by rfl⟩ (by norm_num))
theorem R69361 : Reach 69361 := rs (se 2 (by rfl) ⟨26010, by rfl⟩) (B 52021 (by norm_num) ⟨26010, by rfl⟩ (by norm_num))
theorem R69365 : Reach 69365 := rs (se 5 (by rfl) ⟨3251, by rfl⟩) (B 6503 (by norm_num) ⟨3251, by rfl⟩ (by norm_num))
theorem R69369 : Reach 69369 := rs (se 2 (by rfl) ⟨26013, by rfl⟩) (B 52027 (by norm_num) ⟨26013, by rfl⟩ (by norm_num))
theorem R69373 : Reach 69373 := rs (se 3 (by rfl) ⟨13007, by rfl⟩) (B 26015 (by norm_num) ⟨13007, by rfl⟩ (by norm_num))
theorem R69377 : Reach 69377 := rs (se 2 (by rfl) ⟨26016, by rfl⟩) (B 52033 (by norm_num) ⟨26016, by rfl⟩ (by norm_num))
theorem R102149 : Reach 102149 := rs (se 4 (by rfl) ⟨9576, by rfl⟩) (B 19153 (by norm_num) ⟨9576, by rfl⟩ (by norm_num))
theorem R69381 : Reach 69381 := rs (se 4 (by rfl) ⟨6504, by rfl⟩) (B 13009 (by norm_num) ⟨6504, by rfl⟩ (by norm_num))
theorem R69385 : Reach 69385 := rs (se 2 (by rfl) ⟨26019, by rfl⟩) (B 52039 (by norm_num) ⟨26019, by rfl⟩ (by norm_num))
theorem R69389 : Reach 69389 := rs (se 3 (by rfl) ⟨13010, by rfl⟩) (B 26021 (by norm_num) ⟨13010, by rfl⟩ (by norm_num))
theorem R69393 : Reach 69393 := rs (se 2 (by rfl) ⟨26022, by rfl⟩) (B 52045 (by norm_num) ⟨26022, by rfl⟩ (by norm_num))
theorem R69397 : Reach 69397 := rs (se 6 (by rfl) ⟨1626, by rfl⟩) (B 3253 (by norm_num) ⟨1626, by rfl⟩ (by norm_num))
theorem R69401 : Reach 69401 := rs (se 2 (by rfl) ⟨26025, by rfl⟩) (B 52051 (by norm_num) ⟨26025, by rfl⟩ (by norm_num))
theorem R102173 : Reach 102173 := rs (se 3 (by rfl) ⟨19157, by rfl⟩) (B 38315 (by norm_num) ⟨19157, by rfl⟩ (by norm_num))
theorem R69405 : Reach 69405 := rs (se 3 (by rfl) ⟨13013, by rfl⟩) (B 26027 (by norm_num) ⟨13013, by rfl⟩ (by norm_num))
theorem R134941 : Reach 134941 := rs (se 3 (by rfl) ⟨25301, by rfl⟩) (B 50603 (by norm_num) ⟨25301, by rfl⟩ (by norm_num))
theorem R69409 : Reach 69409 := rs (se 2 (by rfl) ⟨26028, by rfl⟩) (B 52057 (by norm_num) ⟨26028, by rfl⟩ (by norm_num))
theorem R69413 : Reach 69413 := rs (se 4 (by rfl) ⟨6507, by rfl⟩) (B 13015 (by norm_num) ⟨6507, by rfl⟩ (by norm_num))
theorem R69417 : Reach 69417 := rs (se 2 (by rfl) ⟨26031, by rfl⟩) (B 52063 (by norm_num) ⟨26031, by rfl⟩ (by norm_num))
theorem R69421 : Reach 69421 := rs (se 3 (by rfl) ⟨13016, by rfl⟩) (B 26033 (by norm_num) ⟨13016, by rfl⟩ (by norm_num))
theorem R69425 : Reach 69425 := rs (se 2 (by rfl) ⟨26034, by rfl⟩) (B 52069 (by norm_num) ⟨26034, by rfl⟩ (by norm_num))
theorem R102197 : Reach 102197 := rs (se 5 (by rfl) ⟨4790, by rfl⟩) (B 9581 (by norm_num) ⟨4790, by rfl⟩ (by norm_num))
theorem R69429 : Reach 69429 := rs (se 5 (by rfl) ⟨3254, by rfl⟩) (B 6509 (by norm_num) ⟨3254, by rfl⟩ (by norm_num))
theorem R69433 : Reach 69433 := rs (se 2 (by rfl) ⟨26037, by rfl⟩) (B 52075 (by norm_num) ⟨26037, by rfl⟩ (by norm_num))
theorem R69437 : Reach 69437 := rs (se 3 (by rfl) ⟨13019, by rfl⟩) (B 26039 (by norm_num) ⟨13019, by rfl⟩ (by norm_num))
theorem R69441 : Reach 69441 := rs (se 2 (by rfl) ⟨26040, by rfl⟩) (B 52081 (by norm_num) ⟨26040, by rfl⟩ (by norm_num))
theorem R69445 : Reach 69445 := rs (se 4 (by rfl) ⟨6510, by rfl⟩) (B 13021 (by norm_num) ⟨6510, by rfl⟩ (by norm_num))
theorem R69449 : Reach 69449 := rs (se 2 (by rfl) ⟨26043, by rfl⟩) (B 52087 (by norm_num) ⟨26043, by rfl⟩ (by norm_num))
theorem R102221 : Reach 102221 := rs (se 3 (by rfl) ⟨19166, by rfl⟩) (B 38333 (by norm_num) ⟨19166, by rfl⟩ (by norm_num))
theorem R69453 : Reach 69453 := rs (se 3 (by rfl) ⟨13022, by rfl⟩) (B 26045 (by norm_num) ⟨13022, by rfl⟩ (by norm_num))
theorem R69457 : Reach 69457 := rs (se 2 (by rfl) ⟨26046, by rfl⟩) (B 52093 (by norm_num) ⟨26046, by rfl⟩ (by norm_num))
theorem R560981 : Reach 560981 := rs (se 9 (by rfl) ⟨1643, by rfl⟩) (B 3287 (by norm_num) ⟨1643, by rfl⟩ (by norm_num))
theorem R69461 : Reach 69461 := rs (se 9 (by rfl) ⟨203, by rfl⟩) (B 407 (by norm_num) ⟨203, by rfl⟩ (by norm_num))
theorem R69465 : Reach 69465 := rs (se 2 (by rfl) ⟨26049, by rfl⟩) (B 52099 (by norm_num) ⟨26049, by rfl⟩ (by norm_num))
theorem R69469 : Reach 69469 := rs (se 3 (by rfl) ⟨13025, by rfl⟩) (B 26051 (by norm_num) ⟨13025, by rfl⟩ (by norm_num))
theorem R69473 : Reach 69473 := rs (se 2 (by rfl) ⟨26052, by rfl⟩) (B 52105 (by norm_num) ⟨26052, by rfl⟩ (by norm_num))
theorem R102245 : Reach 102245 := rs (se 4 (by rfl) ⟨9585, by rfl⟩) (B 19171 (by norm_num) ⟨9585, by rfl⟩ (by norm_num))
theorem R69477 : Reach 69477 := rs (se 4 (by rfl) ⟨6513, by rfl⟩) (B 13027 (by norm_num) ⟨6513, by rfl⟩ (by norm_num))
theorem R69481 : Reach 69481 := rs (se 2 (by rfl) ⟨26055, by rfl⟩) (B 52111 (by norm_num) ⟨26055, by rfl⟩ (by norm_num))
theorem R69485 : Reach 69485 := rs (se 3 (by rfl) ⟨13028, by rfl⟩) (B 26057 (by norm_num) ⟨13028, by rfl⟩ (by norm_num))
theorem R69489 : Reach 69489 := rs (se 2 (by rfl) ⟨26058, by rfl⟩) (B 52117 (by norm_num) ⟨26058, by rfl⟩ (by norm_num))
theorem R233333 : Reach 233333 := rs (se 5 (by rfl) ⟨10937, by rfl⟩) (B 21875 (by norm_num) ⟨10937, by rfl⟩ (by norm_num))
theorem R69493 : Reach 69493 := rs (se 5 (by rfl) ⟨3257, by rfl⟩) (B 6515 (by norm_num) ⟨3257, by rfl⟩ (by norm_num))
theorem R69497 : Reach 69497 := rs (se 2 (by rfl) ⟨26061, by rfl⟩) (B 52123 (by norm_num) ⟨26061, by rfl⟩ (by norm_num))
theorem R102269 : Reach 102269 := rs (se 3 (by rfl) ⟨19175, by rfl⟩) (B 38351 (by norm_num) ⟨19175, by rfl⟩ (by norm_num))
theorem R69501 : Reach 69501 := rs (se 3 (by rfl) ⟨13031, by rfl⟩) (B 26063 (by norm_num) ⟨13031, by rfl⟩ (by norm_num))
theorem R69505 : Reach 69505 := rs (se 2 (by rfl) ⟨26064, by rfl⟩) (B 52129 (by norm_num) ⟨26064, by rfl⟩ (by norm_num))
theorem R69509 : Reach 69509 := rs (se 4 (by rfl) ⟨6516, by rfl⟩) (B 13033 (by norm_num) ⟨6516, by rfl⟩ (by norm_num))
theorem R69513 : Reach 69513 := rs (se 2 (by rfl) ⟨26067, by rfl⟩) (B 52135 (by norm_num) ⟨26067, by rfl⟩ (by norm_num))
theorem R69517 : Reach 69517 := rs (se 3 (by rfl) ⟨13034, by rfl⟩) (B 26069 (by norm_num) ⟨13034, by rfl⟩ (by norm_num))
theorem R69521 : Reach 69521 := rs (se 2 (by rfl) ⟨26070, by rfl⟩) (B 52141 (by norm_num) ⟨26070, by rfl⟩ (by norm_num))
theorem R102293 : Reach 102293 := rs (se 6 (by rfl) ⟨2397, by rfl⟩) (B 4795 (by norm_num) ⟨2397, by rfl⟩ (by norm_num))
theorem R69525 : Reach 69525 := rs (se 6 (by rfl) ⟨1629, by rfl⟩) (B 3259 (by norm_num) ⟨1629, by rfl⟩ (by norm_num))
theorem R69529 : Reach 69529 := rs (se 2 (by rfl) ⟨26073, by rfl⟩) (B 52147 (by norm_num) ⟨26073, by rfl⟩ (by norm_num))
theorem R69533 : Reach 69533 := rs (se 3 (by rfl) ⟨13037, by rfl⟩) (B 26075 (by norm_num) ⟨13037, by rfl⟩ (by norm_num))
theorem R69537 : Reach 69537 := rs (se 2 (by rfl) ⟨26076, by rfl⟩) (B 52153 (by norm_num) ⟨26076, by rfl⟩ (by norm_num))
theorem R167845 : Reach 167845 := rs (se 4 (by rfl) ⟨15735, by rfl⟩) (B 31471 (by norm_num) ⟨15735, by rfl⟩ (by norm_num))
theorem R69541 : Reach 69541 := rs (se 4 (by rfl) ⟨6519, by rfl⟩) (B 13039 (by norm_num) ⟨6519, by rfl⟩ (by norm_num))
theorem R69545 : Reach 69545 := rs (se 2 (by rfl) ⟨26079, by rfl⟩) (B 52159 (by norm_num) ⟨26079, by rfl⟩ (by norm_num))
theorem R102317 : Reach 102317 := rs (se 3 (by rfl) ⟨19184, by rfl⟩) (B 38369 (by norm_num) ⟨19184, by rfl⟩ (by norm_num))
theorem R69549 : Reach 69549 := rs (se 3 (by rfl) ⟨13040, by rfl⟩) (B 26081 (by norm_num) ⟨13040, by rfl⟩ (by norm_num))
theorem R69553 : Reach 69553 := rs (se 2 (by rfl) ⟨26082, by rfl⟩) (B 52165 (by norm_num) ⟨26082, by rfl⟩ (by norm_num))
theorem R69557 : Reach 69557 := rs (se 5 (by rfl) ⟨3260, by rfl⟩) (B 6521 (by norm_num) ⟨3260, by rfl⟩ (by norm_num))
theorem R69561 : Reach 69561 := rs (se 2 (by rfl) ⟨26085, by rfl⟩) (B 52171 (by norm_num) ⟨26085, by rfl⟩ (by norm_num))
theorem R69565 : Reach 69565 := rs (se 3 (by rfl) ⟨13043, by rfl⟩) (B 26087 (by norm_num) ⟨13043, by rfl⟩ (by norm_num))
theorem R69569 : Reach 69569 := rs (se 2 (by rfl) ⟨26088, by rfl⟩) (B 52177 (by norm_num) ⟨26088, by rfl⟩ (by norm_num))
theorem R102341 : Reach 102341 := rs (se 4 (by rfl) ⟨9594, by rfl⟩) (B 19189 (by norm_num) ⟨9594, by rfl⟩ (by norm_num))
theorem R69573 : Reach 69573 := rs (se 4 (by rfl) ⟨6522, by rfl⟩) (B 13045 (by norm_num) ⟨6522, by rfl⟩ (by norm_num))
theorem R69577 : Reach 69577 := rs (se 2 (by rfl) ⟨26091, by rfl⟩) (B 52183 (by norm_num) ⟨26091, by rfl⟩ (by norm_num))
theorem R69581 : Reach 69581 := rs (se 3 (by rfl) ⟨13046, by rfl⟩) (B 26093 (by norm_num) ⟨13046, by rfl⟩ (by norm_num))
theorem R69585 : Reach 69585 := rs (se 2 (by rfl) ⟨26094, by rfl⟩) (B 52189 (by norm_num) ⟨26094, by rfl⟩ (by norm_num))
theorem R69589 : Reach 69589 := rs (se 7 (by rfl) ⟨815, by rfl⟩) (B 1631 (by norm_num) ⟨815, by rfl⟩ (by norm_num))
theorem R69593 : Reach 69593 := rs (se 2 (by rfl) ⟨26097, by rfl⟩) (B 52195 (by norm_num) ⟨26097, by rfl⟩ (by norm_num))
theorem R102365 : Reach 102365 := rs (se 3 (by rfl) ⟨19193, by rfl⟩) (B 38387 (by norm_num) ⟨19193, by rfl⟩ (by norm_num))
theorem R69597 : Reach 69597 := rs (se 3 (by rfl) ⟨13049, by rfl⟩) (B 26099 (by norm_num) ⟨13049, by rfl⟩ (by norm_num))
theorem R69601 : Reach 69601 := rs (se 2 (by rfl) ⟨26100, by rfl⟩) (B 52201 (by norm_num) ⟨26100, by rfl⟩ (by norm_num))
theorem R69605 : Reach 69605 := rs (se 4 (by rfl) ⟨6525, by rfl⟩) (B 13051 (by norm_num) ⟨6525, by rfl⟩ (by norm_num))
theorem R69609 : Reach 69609 := rs (se 2 (by rfl) ⟨26103, by rfl⟩) (B 52207 (by norm_num) ⟨26103, by rfl⟩ (by norm_num))
theorem R69613 : Reach 69613 := rs (se 3 (by rfl) ⟨13052, by rfl⟩) (B 26105 (by norm_num) ⟨13052, by rfl⟩ (by norm_num))
theorem R69617 : Reach 69617 := rs (se 2 (by rfl) ⟨26106, by rfl⟩) (B 52213 (by norm_num) ⟨26106, by rfl⟩ (by norm_num))
theorem R102389 : Reach 102389 := rs (se 5 (by rfl) ⟨4799, by rfl⟩) (B 9599 (by norm_num) ⟨4799, by rfl⟩ (by norm_num))
theorem R69621 : Reach 69621 := rs (se 5 (by rfl) ⟨3263, by rfl⟩) (B 6527 (by norm_num) ⟨3263, by rfl⟩ (by norm_num))
theorem R69625 : Reach 69625 := rs (se 2 (by rfl) ⟨26109, by rfl⟩) (B 52219 (by norm_num) ⟨26109, by rfl⟩ (by norm_num))
theorem R69629 : Reach 69629 := rs (se 3 (by rfl) ⟨13055, by rfl⟩) (B 26111 (by norm_num) ⟨13055, by rfl⟩ (by norm_num))
theorem R69633 : Reach 69633 := rs (se 2 (by rfl) ⟨26112, by rfl⟩) (B 52225 (by norm_num) ⟨26112, by rfl⟩ (by norm_num))
theorem R69637 : Reach 69637 := rs (se 4 (by rfl) ⟨6528, by rfl⟩) (B 13057 (by norm_num) ⟨6528, by rfl⟩ (by norm_num))
theorem R69641 : Reach 69641 := rs (se 2 (by rfl) ⟨26115, by rfl⟩) (B 52231 (by norm_num) ⟨26115, by rfl⟩ (by norm_num))
theorem R102413 : Reach 102413 := rs (se 3 (by rfl) ⟨19202, by rfl⟩) (B 38405 (by norm_num) ⟨19202, by rfl⟩ (by norm_num))
theorem R69645 : Reach 69645 := rs (se 3 (by rfl) ⟨13058, by rfl⟩) (B 26117 (by norm_num) ⟨13058, by rfl⟩ (by norm_num))
theorem R69649 : Reach 69649 := rs (se 2 (by rfl) ⟨26118, by rfl⟩) (B 52237 (by norm_num) ⟨26118, by rfl⟩ (by norm_num))
theorem R69653 : Reach 69653 := rs (se 6 (by rfl) ⟨1632, by rfl⟩) (B 3265 (by norm_num) ⟨1632, by rfl⟩ (by norm_num))
theorem R69657 : Reach 69657 := rs (se 2 (by rfl) ⟨26121, by rfl⟩) (B 52243 (by norm_num) ⟨26121, by rfl⟩ (by norm_num))
theorem R69661 : Reach 69661 := rs (se 3 (by rfl) ⟨13061, by rfl⟩) (B 26123 (by norm_num) ⟨13061, by rfl⟩ (by norm_num))
theorem R69665 : Reach 69665 := rs (se 2 (by rfl) ⟨26124, by rfl⟩) (B 52249 (by norm_num) ⟨26124, by rfl⟩ (by norm_num))
theorem R102437 : Reach 102437 := rs (se 4 (by rfl) ⟨9603, by rfl⟩) (B 19207 (by norm_num) ⟨9603, by rfl⟩ (by norm_num))
theorem R69669 : Reach 69669 := rs (se 4 (by rfl) ⟨6531, by rfl⟩) (B 13063 (by norm_num) ⟨6531, by rfl⟩ (by norm_num))
theorem R69673 : Reach 69673 := rs (se 2 (by rfl) ⟨26127, by rfl⟩) (B 52255 (by norm_num) ⟨26127, by rfl⟩ (by norm_num))
theorem R69677 : Reach 69677 := rs (se 3 (by rfl) ⟨13064, by rfl⟩) (B 26129 (by norm_num) ⟨13064, by rfl⟩ (by norm_num))
theorem R167989 : Reach 167989 := rs (se 5 (by rfl) ⟨7874, by rfl⟩) (B 15749 (by norm_num) ⟨7874, by rfl⟩ (by norm_num))
theorem R69681 : Reach 69681 := rs (se 2 (by rfl) ⟨26130, by rfl⟩) (B 52261 (by norm_num) ⟨26130, by rfl⟩ (by norm_num))
theorem R69689 : Reach 69689 := rs (se 2 (by rfl) ⟨26133, by rfl⟩) (B 52267 (by norm_num) ⟨26133, by rfl⟩ (by norm_num))
theorem R69685 : Reach 69685 := rs (se 5 (by rfl) ⟨3266, by rfl⟩) (B 6533 (by norm_num) ⟨3266, by rfl⟩ (by norm_num))
theorem R102461 : Reach 102461 := rs (se 3 (by rfl) ⟨19211, by rfl⟩) (B 38423 (by norm_num) ⟨19211, by rfl⟩ (by norm_num))
theorem R69693 : Reach 69693 := rs (se 3 (by rfl) ⟨13067, by rfl⟩) (B 26135 (by norm_num) ⟨13067, by rfl⟩ (by norm_num))
theorem R69697 : Reach 69697 := rs (se 2 (by rfl) ⟨26136, by rfl⟩) (B 52273 (by norm_num) ⟨26136, by rfl⟩ (by norm_num))
theorem R69701 : Reach 69701 := rs (se 4 (by rfl) ⟨6534, by rfl⟩) (B 13069 (by norm_num) ⟨6534, by rfl⟩ (by norm_num))
theorem R69705 : Reach 69705 := rs (se 2 (by rfl) ⟨26139, by rfl⟩) (B 52279 (by norm_num) ⟨26139, by rfl⟩ (by norm_num))
theorem R69709 : Reach 69709 := rs (se 3 (by rfl) ⟨13070, by rfl⟩) (B 26141 (by norm_num) ⟨13070, by rfl⟩ (by norm_num))
theorem R69713 : Reach 69713 := rs (se 2 (by rfl) ⟨26142, by rfl⟩) (B 52285 (by norm_num) ⟨26142, by rfl⟩ (by norm_num))
theorem R102485 : Reach 102485 := rs (se 8 (by rfl) ⟨600, by rfl⟩) (B 1201 (by norm_num) ⟨600, by rfl⟩ (by norm_num))
theorem R69717 : Reach 69717 := rs (se 8 (by rfl) ⟨408, by rfl⟩) (B 817 (by norm_num) ⟨408, by rfl⟩ (by norm_num))
theorem R69721 : Reach 69721 := rs (se 2 (by rfl) ⟨26145, by rfl⟩) (B 52291 (by norm_num) ⟨26145, by rfl⟩ (by norm_num))
theorem R69725 : Reach 69725 := rs (se 3 (by rfl) ⟨13073, by rfl⟩) (B 26147 (by norm_num) ⟨13073, by rfl⟩ (by norm_num))
theorem R69729 : Reach 69729 := rs (se 2 (by rfl) ⟨26148, by rfl⟩) (B 52297 (by norm_num) ⟨26148, by rfl⟩ (by norm_num))
theorem R69733 : Reach 69733 := rs (se 4 (by rfl) ⟨6537, by rfl⟩) (B 13075 (by norm_num) ⟨6537, by rfl⟩ (by norm_num))
theorem R69737 : Reach 69737 := rs (se 2 (by rfl) ⟨26151, by rfl⟩) (B 52303 (by norm_num) ⟨26151, by rfl⟩ (by norm_num))
theorem R102509 : Reach 102509 := rs (se 3 (by rfl) ⟨19220, by rfl⟩) (B 38441 (by norm_num) ⟨19220, by rfl⟩ (by norm_num))
theorem R69741 : Reach 69741 := rs (se 3 (by rfl) ⟨13076, by rfl⟩) (B 26153 (by norm_num) ⟨13076, by rfl⟩ (by norm_num))
theorem R69745 : Reach 69745 := rs (se 2 (by rfl) ⟨26154, by rfl⟩) (B 52309 (by norm_num) ⟨26154, by rfl⟩ (by norm_num))
theorem R69749 : Reach 69749 := rs (se 5 (by rfl) ⟨3269, by rfl⟩) (B 6539 (by norm_num) ⟨3269, by rfl⟩ (by norm_num))
theorem R69753 : Reach 69753 := rs (se 2 (by rfl) ⟨26157, by rfl⟩) (B 52315 (by norm_num) ⟨26157, by rfl⟩ (by norm_num))
theorem R69757 : Reach 69757 := rs (se 3 (by rfl) ⟨13079, by rfl⟩) (B 26159 (by norm_num) ⟨13079, by rfl⟩ (by norm_num))
theorem R69761 : Reach 69761 := rs (se 2 (by rfl) ⟨26160, by rfl⟩) (B 52321 (by norm_num) ⟨26160, by rfl⟩ (by norm_num))
theorem R102533 : Reach 102533 := rs (se 4 (by rfl) ⟨9612, by rfl⟩) (B 19225 (by norm_num) ⟨9612, by rfl⟩ (by norm_num))
theorem R69765 : Reach 69765 := rs (se 4 (by rfl) ⟨6540, by rfl⟩) (B 13081 (by norm_num) ⟨6540, by rfl⟩ (by norm_num))
theorem R69769 : Reach 69769 := rs (se 2 (by rfl) ⟨26163, by rfl⟩) (B 52327 (by norm_num) ⟨26163, by rfl⟩ (by norm_num))
theorem R69773 : Reach 69773 := rs (se 3 (by rfl) ⟨13082, by rfl⟩) (B 26165 (by norm_num) ⟨13082, by rfl⟩ (by norm_num))
theorem R69777 : Reach 69777 := rs (se 2 (by rfl) ⟨26166, by rfl⟩) (B 52333 (by norm_num) ⟨26166, by rfl⟩ (by norm_num))
theorem R69781 : Reach 69781 := rs (se 6 (by rfl) ⟨1635, by rfl⟩) (B 3271 (by norm_num) ⟨1635, by rfl⟩ (by norm_num))
theorem R69785 : Reach 69785 := rs (se 2 (by rfl) ⟨26169, by rfl⟩) (B 52339 (by norm_num) ⟨26169, by rfl⟩ (by norm_num))
theorem R102557 : Reach 102557 := rs (se 3 (by rfl) ⟨19229, by rfl⟩) (B 38459 (by norm_num) ⟨19229, by rfl⟩ (by norm_num))
theorem R69789 : Reach 69789 := rs (se 3 (by rfl) ⟨13085, by rfl⟩) (B 26171 (by norm_num) ⟨13085, by rfl⟩ (by norm_num))
theorem R69793 : Reach 69793 := rs (se 2 (by rfl) ⟨26172, by rfl⟩) (B 52345 (by norm_num) ⟨26172, by rfl⟩ (by norm_num))
theorem R102565 : Reach 102565 := rs (se 4 (by rfl) ⟨9615, by rfl⟩) (B 19231 (by norm_num) ⟨9615, by rfl⟩ (by norm_num))
theorem R69797 : Reach 69797 := rs (se 4 (by rfl) ⟨6543, by rfl⟩) (B 13087 (by norm_num) ⟨6543, by rfl⟩ (by norm_num))
theorem R69801 : Reach 69801 := rs (se 2 (by rfl) ⟨26175, by rfl⟩) (B 52351 (by norm_num) ⟨26175, by rfl⟩ (by norm_num))
theorem R69805 : Reach 69805 := rs (se 3 (by rfl) ⟨13088, by rfl⟩) (B 26177 (by norm_num) ⟨13088, by rfl⟩ (by norm_num))
theorem R69809 : Reach 69809 := rs (se 2 (by rfl) ⟨26178, by rfl⟩) (B 52357 (by norm_num) ⟨26178, by rfl⟩ (by norm_num))
theorem R102581 : Reach 102581 := rs (se 5 (by rfl) ⟨4808, by rfl⟩) (B 9617 (by norm_num) ⟨4808, by rfl⟩ (by norm_num))
theorem R69813 : Reach 69813 := rs (se 5 (by rfl) ⟨3272, by rfl⟩) (B 6545 (by norm_num) ⟨3272, by rfl⟩ (by norm_num))
theorem R69817 : Reach 69817 := rs (se 2 (by rfl) ⟨26181, by rfl⟩) (B 52363 (by norm_num) ⟨26181, by rfl⟩ (by norm_num))
theorem R69821 : Reach 69821 := rs (se 3 (by rfl) ⟨13091, by rfl⟩) (B 26183 (by norm_num) ⟨13091, by rfl⟩ (by norm_num))
theorem R69825 : Reach 69825 := rs (se 2 (by rfl) ⟨26184, by rfl⟩) (B 52369 (by norm_num) ⟨26184, by rfl⟩ (by norm_num))
theorem R69829 : Reach 69829 := rs (se 4 (by rfl) ⟨6546, by rfl⟩) (B 13093 (by norm_num) ⟨6546, by rfl⟩ (by norm_num))
theorem R69833 : Reach 69833 := rs (se 2 (by rfl) ⟨26187, by rfl⟩) (B 52375 (by norm_num) ⟨26187, by rfl⟩ (by norm_num))
theorem R102605 : Reach 102605 := rs (se 3 (by rfl) ⟨19238, by rfl⟩) (B 38477 (by norm_num) ⟨19238, by rfl⟩ (by norm_num))
theorem R69837 : Reach 69837 := rs (se 3 (by rfl) ⟨13094, by rfl⟩) (B 26189 (by norm_num) ⟨13094, by rfl⟩ (by norm_num))
theorem R69841 : Reach 69841 := rs (se 2 (by rfl) ⟨26190, by rfl⟩) (B 52381 (by norm_num) ⟨26190, by rfl⟩ (by norm_num))
theorem R69845 : Reach 69845 := rs (se 7 (by rfl) ⟨818, by rfl⟩) (B 1637 (by norm_num) ⟨818, by rfl⟩ (by norm_num))
theorem R69849 : Reach 69849 := rs (se 2 (by rfl) ⟨26193, by rfl⟩) (B 52387 (by norm_num) ⟨26193, by rfl⟩ (by norm_num))
theorem R69853 : Reach 69853 := rs (se 3 (by rfl) ⟨13097, by rfl⟩) (B 26195 (by norm_num) ⟨13097, by rfl⟩ (by norm_num))
theorem R69857 : Reach 69857 := rs (se 2 (by rfl) ⟨26196, by rfl⟩) (B 52393 (by norm_num) ⟨26196, by rfl⟩ (by norm_num))
theorem R102629 : Reach 102629 := rs (se 4 (by rfl) ⟨9621, by rfl⟩) (B 19243 (by norm_num) ⟨9621, by rfl⟩ (by norm_num))
theorem R69861 : Reach 69861 := rs (se 4 (by rfl) ⟨6549, by rfl⟩) (B 13099 (by norm_num) ⟨6549, by rfl⟩ (by norm_num))
theorem R69865 : Reach 69865 := rs (se 2 (by rfl) ⟨26199, by rfl⟩) (B 52399 (by norm_num) ⟨26199, by rfl⟩ (by norm_num))
theorem R69869 : Reach 69869 := rs (se 3 (by rfl) ⟨13100, by rfl⟩) (B 26201 (by norm_num) ⟨13100, by rfl⟩ (by norm_num))
theorem R69873 : Reach 69873 := rs (se 2 (by rfl) ⟨26202, by rfl⟩) (B 52405 (by norm_num) ⟨26202, by rfl⟩ (by norm_num))
theorem R69877 : Reach 69877 := rs (se 5 (by rfl) ⟨3275, by rfl⟩) (B 6551 (by norm_num) ⟨3275, by rfl⟩ (by norm_num))
theorem R69881 : Reach 69881 := rs (se 2 (by rfl) ⟨26205, by rfl⟩) (B 52411 (by norm_num) ⟨26205, by rfl⟩ (by norm_num))
theorem R102653 : Reach 102653 := rs (se 3 (by rfl) ⟨19247, by rfl⟩) (B 38495 (by norm_num) ⟨19247, by rfl⟩ (by norm_num))
theorem R69885 : Reach 69885 := rs (se 3 (by rfl) ⟨13103, by rfl⟩) (B 26207 (by norm_num) ⟨13103, by rfl⟩ (by norm_num))
theorem R69889 : Reach 69889 := rs (se 2 (by rfl) ⟨26208, by rfl⟩) (B 52417 (by norm_num) ⟨26208, by rfl⟩ (by norm_num))
theorem R69893 : Reach 69893 := rs (se 4 (by rfl) ⟨6552, by rfl⟩) (B 13105 (by norm_num) ⟨6552, by rfl⟩ (by norm_num))
theorem R69897 : Reach 69897 := rs (se 2 (by rfl) ⟨26211, by rfl⟩) (B 52423 (by norm_num) ⟨26211, by rfl⟩ (by norm_num))
theorem R69901 : Reach 69901 := rs (se 3 (by rfl) ⟨13106, by rfl⟩) (B 26213 (by norm_num) ⟨13106, by rfl⟩ (by norm_num))
theorem R69905 : Reach 69905 := rs (se 2 (by rfl) ⟨26214, by rfl⟩) (B 52429 (by norm_num) ⟨26214, by rfl⟩ (by norm_num))
theorem R102677 : Reach 102677 := rs (se 6 (by rfl) ⟨2406, by rfl⟩) (B 4813 (by norm_num) ⟨2406, by rfl⟩ (by norm_num))
theorem R69909 : Reach 69909 := rs (se 6 (by rfl) ⟨1638, by rfl⟩) (B 3277 (by norm_num) ⟨1638, by rfl⟩ (by norm_num))
theorem R69913 : Reach 69913 := rs (se 2 (by rfl) ⟨26217, by rfl⟩) (B 52435 (by norm_num) ⟨26217, by rfl⟩ (by norm_num))
theorem R69917 : Reach 69917 := rs (se 3 (by rfl) ⟨13109, by rfl⟩) (B 26219 (by norm_num) ⟨13109, by rfl⟩ (by norm_num))
theorem R69921 : Reach 69921 := rs (se 2 (by rfl) ⟨26220, by rfl⟩) (B 52441 (by norm_num) ⟨26220, by rfl⟩ (by norm_num))
theorem R233765 : Reach 233765 := rs (se 4 (by rfl) ⟨21915, by rfl⟩) (B 43831 (by norm_num) ⟨21915, by rfl⟩ (by norm_num))
theorem R69925 : Reach 69925 := rs (se 4 (by rfl) ⟨6555, by rfl⟩) (B 13111 (by norm_num) ⟨6555, by rfl⟩ (by norm_num))
theorem R69929 : Reach 69929 := rs (se 2 (by rfl) ⟨26223, by rfl⟩) (B 52447 (by norm_num) ⟨26223, by rfl⟩ (by norm_num))
theorem R102701 : Reach 102701 := rs (se 3 (by rfl) ⟨19256, by rfl⟩) (B 38513 (by norm_num) ⟨19256, by rfl⟩ (by norm_num))
theorem R69933 : Reach 69933 := rs (se 3 (by rfl) ⟨13112, by rfl⟩) (B 26225 (by norm_num) ⟨13112, by rfl⟩ (by norm_num))
theorem R69937 : Reach 69937 := rs (se 2 (by rfl) ⟨26226, by rfl⟩) (B 52453 (by norm_num) ⟨26226, by rfl⟩ (by norm_num))
theorem R69941 : Reach 69941 := rs (se 5 (by rfl) ⟨3278, by rfl⟩) (B 6557 (by norm_num) ⟨3278, by rfl⟩ (by norm_num))
theorem R69945 : Reach 69945 := rs (se 2 (by rfl) ⟨26229, by rfl⟩) (B 52459 (by norm_num) ⟨26229, by rfl⟩ (by norm_num))
theorem R69949 : Reach 69949 := rs (se 3 (by rfl) ⟨13115, by rfl⟩) (B 26231 (by norm_num) ⟨13115, by rfl⟩ (by norm_num))
theorem R69953 : Reach 69953 := rs (se 2 (by rfl) ⟨26232, by rfl⟩) (B 52465 (by norm_num) ⟨26232, by rfl⟩ (by norm_num))
theorem R102725 : Reach 102725 := rs (se 4 (by rfl) ⟨9630, by rfl⟩) (B 19261 (by norm_num) ⟨9630, by rfl⟩ (by norm_num))
theorem R69957 : Reach 69957 := rs (se 4 (by rfl) ⟨6558, by rfl⟩) (B 13117 (by norm_num) ⟨6558, by rfl⟩ (by norm_num))
theorem R69961 : Reach 69961 := rs (se 2 (by rfl) ⟨26235, by rfl⟩) (B 52471 (by norm_num) ⟨26235, by rfl⟩ (by norm_num))
theorem R69965 : Reach 69965 := rs (se 3 (by rfl) ⟨13118, by rfl⟩) (B 26237 (by norm_num) ⟨13118, by rfl⟩ (by norm_num))
theorem R69969 : Reach 69969 := rs (se 2 (by rfl) ⟨26238, by rfl⟩) (B 52477 (by norm_num) ⟨26238, by rfl⟩ (by norm_num))
theorem R1118549 : Reach 1118549 := rs (se 10 (by rfl) ⟨1638, by rfl⟩) (B 3277 (by norm_num) ⟨1638, by rfl⟩ (by norm_num))
theorem R69973 : Reach 69973 := rs (se 10 (by rfl) ⟨102, by rfl⟩) (B 205 (by norm_num) ⟨102, by rfl⟩ (by norm_num))
theorem R69977 : Reach 69977 := rs (se 2 (by rfl) ⟨26241, by rfl⟩) (B 52483 (by norm_num) ⟨26241, by rfl⟩ (by norm_num))
theorem R102749 : Reach 102749 := rs (se 3 (by rfl) ⟨19265, by rfl⟩) (B 38531 (by norm_num) ⟨19265, by rfl⟩ (by norm_num))
theorem R69981 : Reach 69981 := rs (se 3 (by rfl) ⟨13121, by rfl⟩) (B 26243 (by norm_num) ⟨13121, by rfl⟩ (by norm_num))
theorem R69985 : Reach 69985 := rs (se 2 (by rfl) ⟨26244, by rfl⟩) (B 52489 (by norm_num) ⟨26244, by rfl⟩ (by norm_num))
theorem R69989 : Reach 69989 := rs (se 4 (by rfl) ⟨6561, by rfl⟩) (B 13123 (by norm_num) ⟨6561, by rfl⟩ (by norm_num))
theorem R69993 : Reach 69993 := rs (se 2 (by rfl) ⟨26247, by rfl⟩) (B 52495 (by norm_num) ⟨26247, by rfl⟩ (by norm_num))
theorem R69997 : Reach 69997 := rs (se 3 (by rfl) ⟨13124, by rfl⟩) (B 26249 (by norm_num) ⟨13124, by rfl⟩ (by norm_num))
theorem R70001 : Reach 70001 := rs (se 2 (by rfl) ⟨26250, by rfl⟩) (B 52501 (by norm_num) ⟨26250, by rfl⟩ (by norm_num))
theorem R102773 : Reach 102773 := rs (se 5 (by rfl) ⟨4817, by rfl⟩) (B 9635 (by norm_num) ⟨4817, by rfl⟩ (by norm_num))
theorem R70005 : Reach 70005 := rs (se 5 (by rfl) ⟨3281, by rfl⟩) (B 6563 (by norm_num) ⟨3281, by rfl⟩ (by norm_num))
theorem R70009 : Reach 70009 := rs (se 2 (by rfl) ⟨26253, by rfl⟩) (B 52507 (by norm_num) ⟨26253, by rfl⟩ (by norm_num))
theorem R70013 : Reach 70013 := rs (se 3 (by rfl) ⟨13127, by rfl⟩) (B 26255 (by norm_num) ⟨13127, by rfl⟩ (by norm_num))
theorem R70017 : Reach 70017 := rs (se 2 (by rfl) ⟨26256, by rfl⟩) (B 52513 (by norm_num) ⟨26256, by rfl⟩ (by norm_num))
theorem R70021 : Reach 70021 := rs (se 4 (by rfl) ⟨6564, by rfl⟩) (B 13129 (by norm_num) ⟨6564, by rfl⟩ (by norm_num))
theorem R70025 : Reach 70025 := rs (se 2 (by rfl) ⟨26259, by rfl⟩) (B 52519 (by norm_num) ⟨26259, by rfl⟩ (by norm_num))
theorem R102797 : Reach 102797 := rs (se 3 (by rfl) ⟨19274, by rfl⟩) (B 38549 (by norm_num) ⟨19274, by rfl⟩ (by norm_num))
theorem R70029 : Reach 70029 := rs (se 3 (by rfl) ⟨13130, by rfl⟩) (B 26261 (by norm_num) ⟨13130, by rfl⟩ (by norm_num))
theorem R70033 : Reach 70033 := rs (se 2 (by rfl) ⟨26262, by rfl⟩) (B 52525 (by norm_num) ⟨26262, by rfl⟩ (by norm_num))
theorem R70037 : Reach 70037 := rs (se 6 (by rfl) ⟨1641, by rfl⟩) (B 3283 (by norm_num) ⟨1641, by rfl⟩ (by norm_num))
theorem R70041 : Reach 70041 := rs (se 2 (by rfl) ⟨26265, by rfl⟩) (B 52531 (by norm_num) ⟨26265, by rfl⟩ (by norm_num))
theorem R70045 : Reach 70045 := rs (se 3 (by rfl) ⟨13133, by rfl⟩) (B 26267 (by norm_num) ⟨13133, by rfl⟩ (by norm_num))
theorem R70049 : Reach 70049 := rs (se 2 (by rfl) ⟨26268, by rfl⟩) (B 52537 (by norm_num) ⟨26268, by rfl⟩ (by norm_num))
theorem R102821 : Reach 102821 := rs (se 4 (by rfl) ⟨9639, by rfl⟩) (B 19279 (by norm_num) ⟨9639, by rfl⟩ (by norm_num))
theorem R70053 : Reach 70053 := rs (se 4 (by rfl) ⟨6567, by rfl⟩) (B 13135 (by norm_num) ⟨6567, by rfl⟩ (by norm_num))
theorem R70057 : Reach 70057 := rs (se 2 (by rfl) ⟨26271, by rfl⟩) (B 52543 (by norm_num) ⟨26271, by rfl⟩ (by norm_num))
theorem R70061 : Reach 70061 := rs (se 3 (by rfl) ⟨13136, by rfl⟩) (B 26273 (by norm_num) ⟨13136, by rfl⟩ (by norm_num))
theorem R70065 : Reach 70065 := rs (se 2 (by rfl) ⟨26274, by rfl⟩) (B 52549 (by norm_num) ⟨26274, by rfl⟩ (by norm_num))
theorem R70069 : Reach 70069 := rs (se 5 (by rfl) ⟨3284, by rfl⟩) (B 6569 (by norm_num) ⟨3284, by rfl⟩ (by norm_num))
theorem R70073 : Reach 70073 := rs (se 2 (by rfl) ⟨26277, by rfl⟩) (B 52555 (by norm_num) ⟨26277, by rfl⟩ (by norm_num))
theorem R102845 : Reach 102845 := rs (se 3 (by rfl) ⟨19283, by rfl⟩) (B 38567 (by norm_num) ⟨19283, by rfl⟩ (by norm_num))
theorem R70077 : Reach 70077 := rs (se 3 (by rfl) ⟨13139, by rfl⟩) (B 26279 (by norm_num) ⟨13139, by rfl⟩ (by norm_num))
theorem R70081 : Reach 70081 := rs (se 2 (by rfl) ⟨26280, by rfl⟩) (B 52561 (by norm_num) ⟨26280, by rfl⟩ (by norm_num))
theorem R70085 : Reach 70085 := rs (se 4 (by rfl) ⟨6570, by rfl⟩) (B 13141 (by norm_num) ⟨6570, by rfl⟩ (by norm_num))
theorem R70089 : Reach 70089 := rs (se 2 (by rfl) ⟨26283, by rfl⟩) (B 52567 (by norm_num) ⟨26283, by rfl⟩ (by norm_num))
theorem R70093 : Reach 70093 := rs (se 3 (by rfl) ⟨13142, by rfl⟩) (B 26285 (by norm_num) ⟨13142, by rfl⟩ (by norm_num))
theorem R70097 : Reach 70097 := rs (se 2 (by rfl) ⟨26286, by rfl⟩) (B 52573 (by norm_num) ⟨26286, by rfl⟩ (by norm_num))
theorem R102869 : Reach 102869 := rs (se 7 (by rfl) ⟨1205, by rfl⟩) (B 2411 (by norm_num) ⟨1205, by rfl⟩ (by norm_num))
theorem R70101 : Reach 70101 := rs (se 7 (by rfl) ⟨821, by rfl⟩) (B 1643 (by norm_num) ⟨821, by rfl⟩ (by norm_num))
theorem R70105 : Reach 70105 := rs (se 2 (by rfl) ⟨26289, by rfl⟩) (B 52579 (by norm_num) ⟨26289, by rfl⟩ (by norm_num))
theorem R70109 : Reach 70109 := rs (se 3 (by rfl) ⟨13145, by rfl⟩) (B 26291 (by norm_num) ⟨13145, by rfl⟩ (by norm_num))
theorem R70113 : Reach 70113 := rs (se 2 (by rfl) ⟨26292, by rfl⟩) (B 52585 (by norm_num) ⟨26292, by rfl⟩ (by norm_num))
theorem R70117 : Reach 70117 := rs (se 4 (by rfl) ⟨6573, by rfl⟩) (B 13147 (by norm_num) ⟨6573, by rfl⟩ (by norm_num))
theorem R70121 : Reach 70121 := rs (se 2 (by rfl) ⟨26295, by rfl⟩) (B 52591 (by norm_num) ⟨26295, by rfl⟩ (by norm_num))
theorem R102893 : Reach 102893 := rs (se 3 (by rfl) ⟨19292, by rfl⟩) (B 38585 (by norm_num) ⟨19292, by rfl⟩ (by norm_num))
theorem R70125 : Reach 70125 := rs (se 3 (by rfl) ⟨13148, by rfl⟩) (B 26297 (by norm_num) ⟨13148, by rfl⟩ (by norm_num))
theorem R70129 : Reach 70129 := rs (se 2 (by rfl) ⟨26298, by rfl⟩) (B 52597 (by norm_num) ⟨26298, by rfl⟩ (by norm_num))
theorem R70133 : Reach 70133 := rs (se 5 (by rfl) ⟨3287, by rfl⟩) (B 6575 (by norm_num) ⟨3287, by rfl⟩ (by norm_num))
theorem R70137 : Reach 70137 := rs (se 2 (by rfl) ⟨26301, by rfl⟩) (B 52603 (by norm_num) ⟨26301, by rfl⟩ (by norm_num))
theorem R70141 : Reach 70141 := rs (se 3 (by rfl) ⟨13151, by rfl⟩) (B 26303 (by norm_num) ⟨13151, by rfl⟩ (by norm_num))
theorem R70145 : Reach 70145 := rs (se 2 (by rfl) ⟨26304, by rfl⟩) (B 52609 (by norm_num) ⟨26304, by rfl⟩ (by norm_num))
theorem R102917 : Reach 102917 := rs (se 4 (by rfl) ⟨9648, by rfl⟩) (B 19297 (by norm_num) ⟨9648, by rfl⟩ (by norm_num))
theorem R70149 : Reach 70149 := rs (se 4 (by rfl) ⟨6576, by rfl⟩) (B 13153 (by norm_num) ⟨6576, by rfl⟩ (by norm_num))
theorem R70153 : Reach 70153 := rs (se 2 (by rfl) ⟨26307, by rfl⟩) (B 52615 (by norm_num) ⟨26307, by rfl⟩ (by norm_num))
theorem R70157 : Reach 70157 := rs (se 3 (by rfl) ⟨13154, by rfl⟩) (B 26309 (by norm_num) ⟨13154, by rfl⟩ (by norm_num))
theorem R70161 : Reach 70161 := rs (se 2 (by rfl) ⟨26310, by rfl⟩) (B 52621 (by norm_num) ⟨26310, by rfl⟩ (by norm_num))
theorem R70165 : Reach 70165 := rs (se 6 (by rfl) ⟨1644, by rfl⟩) (B 3289 (by norm_num) ⟨1644, by rfl⟩ (by norm_num))
theorem R70169 : Reach 70169 := rs (se 2 (by rfl) ⟨26313, by rfl⟩) (B 52627 (by norm_num) ⟨26313, by rfl⟩ (by norm_num))
theorem R102941 : Reach 102941 := rs (se 3 (by rfl) ⟨19301, by rfl⟩) (B 38603 (by norm_num) ⟨19301, by rfl⟩ (by norm_num))
theorem R70173 : Reach 70173 := rs (se 3 (by rfl) ⟨13157, by rfl⟩) (B 26315 (by norm_num) ⟨13157, by rfl⟩ (by norm_num))
theorem R70177 : Reach 70177 := rs (se 2 (by rfl) ⟨26316, by rfl⟩) (B 52633 (by norm_num) ⟨26316, by rfl⟩ (by norm_num))
theorem R70181 : Reach 70181 := rs (se 4 (by rfl) ⟨6579, by rfl⟩) (B 13159 (by norm_num) ⟨6579, by rfl⟩ (by norm_num))
theorem R70185 : Reach 70185 := rs (se 2 (by rfl) ⟨26319, by rfl⟩) (B 52639 (by norm_num) ⟨26319, by rfl⟩ (by norm_num))
theorem R70189 : Reach 70189 := rs (se 3 (by rfl) ⟨13160, by rfl⟩) (B 26321 (by norm_num) ⟨13160, by rfl⟩ (by norm_num))
theorem R70193 : Reach 70193 := rs (se 2 (by rfl) ⟨26322, by rfl⟩) (B 52645 (by norm_num) ⟨26322, by rfl⟩ (by norm_num))
theorem R102965 : Reach 102965 := rs (se 5 (by rfl) ⟨4826, by rfl⟩) (B 9653 (by norm_num) ⟨4826, by rfl⟩ (by norm_num))
theorem R70197 : Reach 70197 := rs (se 5 (by rfl) ⟨3290, by rfl⟩) (B 6581 (by norm_num) ⟨3290, by rfl⟩ (by norm_num))
theorem R70201 : Reach 70201 := rs (se 2 (by rfl) ⟨26325, by rfl⟩) (B 52651 (by norm_num) ⟨26325, by rfl⟩ (by norm_num))
theorem R70205 : Reach 70205 := rs (se 3 (by rfl) ⟨13163, by rfl⟩) (B 26327 (by norm_num) ⟨13163, by rfl⟩ (by norm_num))
theorem R70209 : Reach 70209 := rs (se 2 (by rfl) ⟨26328, by rfl⟩) (B 52657 (by norm_num) ⟨26328, by rfl⟩ (by norm_num))
theorem R70213 : Reach 70213 := rs (se 4 (by rfl) ⟨6582, by rfl⟩) (B 13165 (by norm_num) ⟨6582, by rfl⟩ (by norm_num))
theorem R70217 : Reach 70217 := rs (se 2 (by rfl) ⟨26331, by rfl⟩) (B 52663 (by norm_num) ⟨26331, by rfl⟩ (by norm_num))
theorem R102989 : Reach 102989 := rs (se 3 (by rfl) ⟨19310, by rfl⟩) (B 38621 (by norm_num) ⟨19310, by rfl⟩ (by norm_num))
theorem R70221 : Reach 70221 := rs (se 3 (by rfl) ⟨13166, by rfl⟩) (B 26333 (by norm_num) ⟨13166, by rfl⟩ (by norm_num))
theorem R70225 : Reach 70225 := rs (se 2 (by rfl) ⟨26334, by rfl⟩) (B 52669 (by norm_num) ⟨26334, by rfl⟩ (by norm_num))
theorem R70229 : Reach 70229 := rs (se 8 (by rfl) ⟨411, by rfl⟩) (B 823 (by norm_num) ⟨411, by rfl⟩ (by norm_num))
theorem R70233 : Reach 70233 := rs (se 2 (by rfl) ⟨26337, by rfl⟩) (B 52675 (by norm_num) ⟨26337, by rfl⟩ (by norm_num))
theorem R70237 : Reach 70237 := rs (se 3 (by rfl) ⟨13169, by rfl⟩) (B 26339 (by norm_num) ⟨13169, by rfl⟩ (by norm_num))
theorem R70241 : Reach 70241 := rs (se 2 (by rfl) ⟨26340, by rfl⟩) (B 52681 (by norm_num) ⟨26340, by rfl⟩ (by norm_num))
theorem R103013 : Reach 103013 := rs (se 4 (by rfl) ⟨9657, by rfl⟩) (B 19315 (by norm_num) ⟨9657, by rfl⟩ (by norm_num))
theorem R70245 : Reach 70245 := rs (se 4 (by rfl) ⟨6585, by rfl⟩) (B 13171 (by norm_num) ⟨6585, by rfl⟩ (by norm_num))
theorem R70249 : Reach 70249 := rs (se 2 (by rfl) ⟨26343, by rfl⟩) (B 52687 (by norm_num) ⟨26343, by rfl⟩ (by norm_num))
theorem R70253 : Reach 70253 := rs (se 3 (by rfl) ⟨13172, by rfl⟩) (B 26345 (by norm_num) ⟨13172, by rfl⟩ (by norm_num))
theorem R70257 : Reach 70257 := rs (se 2 (by rfl) ⟨26346, by rfl⟩) (B 52693 (by norm_num) ⟨26346, by rfl⟩ (by norm_num))
theorem R70261 : Reach 70261 := rs (se 5 (by rfl) ⟨3293, by rfl⟩) (B 6587 (by norm_num) ⟨3293, by rfl⟩ (by norm_num))
theorem R70265 : Reach 70265 := rs (se 2 (by rfl) ⟨26349, by rfl⟩) (B 52699 (by norm_num) ⟨26349, by rfl⟩ (by norm_num))
theorem R103037 : Reach 103037 := rs (se 3 (by rfl) ⟨19319, by rfl⟩) (B 38639 (by norm_num) ⟨19319, by rfl⟩ (by norm_num))
theorem R70269 : Reach 70269 := rs (se 3 (by rfl) ⟨13175, by rfl⟩) (B 26351 (by norm_num) ⟨13175, by rfl⟩ (by norm_num))
theorem R70273 : Reach 70273 := rs (se 2 (by rfl) ⟨26352, by rfl⟩) (B 52705 (by norm_num) ⟨26352, by rfl⟩ (by norm_num))
theorem R70277 : Reach 70277 := rs (se 4 (by rfl) ⟨6588, by rfl⟩) (B 13177 (by norm_num) ⟨6588, by rfl⟩ (by norm_num))
theorem R70281 : Reach 70281 := rs (se 2 (by rfl) ⟨26355, by rfl⟩) (B 52711 (by norm_num) ⟨26355, by rfl⟩ (by norm_num))
theorem R70285 : Reach 70285 := rs (se 3 (by rfl) ⟨13178, by rfl⟩) (B 26357 (by norm_num) ⟨13178, by rfl⟩ (by norm_num))
theorem R70289 : Reach 70289 := rs (se 2 (by rfl) ⟨26358, by rfl⟩) (B 52717 (by norm_num) ⟨26358, by rfl⟩ (by norm_num))
theorem R103061 : Reach 103061 := rs (se 6 (by rfl) ⟨2415, by rfl⟩) (B 4831 (by norm_num) ⟨2415, by rfl⟩ (by norm_num))
theorem R70293 : Reach 70293 := rs (se 6 (by rfl) ⟨1647, by rfl⟩) (B 3295 (by norm_num) ⟨1647, by rfl⟩ (by norm_num))
theorem R70297 : Reach 70297 := rs (se 2 (by rfl) ⟨26361, by rfl⟩) (B 52723 (by norm_num) ⟨26361, by rfl⟩ (by norm_num))
theorem R168605 : Reach 168605 := rs (se 3 (by rfl) ⟨31613, by rfl⟩) (B 63227 (by norm_num) ⟨31613, by rfl⟩ (by norm_num))
theorem R70301 : Reach 70301 := rs (se 3 (by rfl) ⟨13181, by rfl⟩) (B 26363 (by norm_num) ⟨13181, by rfl⟩ (by norm_num))
theorem R70305 : Reach 70305 := rs (se 2 (by rfl) ⟨26364, by rfl⟩) (B 52729 (by norm_num) ⟨26364, by rfl⟩ (by norm_num))
theorem R70309 : Reach 70309 := rs (se 4 (by rfl) ⟨6591, by rfl⟩) (B 13183 (by norm_num) ⟨6591, by rfl⟩ (by norm_num))
theorem R135845 : Reach 135845 := rs (se 4 (by rfl) ⟨12735, by rfl⟩) (B 25471 (by norm_num) ⟨12735, by rfl⟩ (by norm_num))
theorem R70313 : Reach 70313 := rs (se 2 (by rfl) ⟨26367, by rfl⟩) (B 52735 (by norm_num) ⟨26367, by rfl⟩ (by norm_num))
theorem R103085 : Reach 103085 := rs (se 3 (by rfl) ⟨19328, by rfl⟩) (B 38657 (by norm_num) ⟨19328, by rfl⟩ (by norm_num))
theorem R70317 : Reach 70317 := rs (se 3 (by rfl) ⟨13184, by rfl⟩) (B 26369 (by norm_num) ⟨13184, by rfl⟩ (by norm_num))
theorem R70321 : Reach 70321 := rs (se 2 (by rfl) ⟨26370, by rfl⟩) (B 52741 (by norm_num) ⟨26370, by rfl⟩ (by norm_num))
theorem R70325 : Reach 70325 := rs (se 5 (by rfl) ⟨3296, by rfl⟩) (B 6593 (by norm_num) ⟨3296, by rfl⟩ (by norm_num))
theorem R70329 : Reach 70329 := rs (se 2 (by rfl) ⟨26373, by rfl⟩) (B 52747 (by norm_num) ⟨26373, by rfl⟩ (by norm_num))
theorem R70333 : Reach 70333 := rs (se 3 (by rfl) ⟨13187, by rfl⟩) (B 26375 (by norm_num) ⟨13187, by rfl⟩ (by norm_num))
theorem R70337 : Reach 70337 := rs (se 2 (by rfl) ⟨26376, by rfl⟩) (B 52753 (by norm_num) ⟨26376, by rfl⟩ (by norm_num))
theorem R103109 : Reach 103109 := rs (se 4 (by rfl) ⟨9666, by rfl⟩) (B 19333 (by norm_num) ⟨9666, by rfl⟩ (by norm_num))
theorem R70341 : Reach 70341 := rs (se 4 (by rfl) ⟨6594, by rfl⟩) (B 13189 (by norm_num) ⟨6594, by rfl⟩ (by norm_num))
theorem R70345 : Reach 70345 := rs (se 2 (by rfl) ⟨26379, by rfl⟩) (B 52759 (by norm_num) ⟨26379, by rfl⟩ (by norm_num))
theorem R70349 : Reach 70349 := rs (se 3 (by rfl) ⟨13190, by rfl⟩) (B 26381 (by norm_num) ⟨13190, by rfl⟩ (by norm_num))
theorem R70353 : Reach 70353 := rs (se 2 (by rfl) ⟨26382, by rfl⟩) (B 52765 (by norm_num) ⟨26382, by rfl⟩ (by norm_num))
theorem R824021 : Reach 824021 := rs (se 7 (by rfl) ⟨9656, by rfl⟩) (B 19313 (by norm_num) ⟨9656, by rfl⟩ (by norm_num))
theorem R234197 : Reach 234197 := rs (se 7 (by rfl) ⟨2744, by rfl⟩) (B 5489 (by norm_num) ⟨2744, by rfl⟩ (by norm_num))
theorem R70357 : Reach 70357 := rs (se 7 (by rfl) ⟨824, by rfl⟩) (B 1649 (by norm_num) ⟨824, by rfl⟩ (by norm_num))
theorem R70361 : Reach 70361 := rs (se 2 (by rfl) ⟨26385, by rfl⟩) (B 52771 (by norm_num) ⟨26385, by rfl⟩ (by norm_num))
theorem R103133 : Reach 103133 := rs (se 3 (by rfl) ⟨19337, by rfl⟩) (B 38675 (by norm_num) ⟨19337, by rfl⟩ (by norm_num))
theorem R70365 : Reach 70365 := rs (se 3 (by rfl) ⟨13193, by rfl⟩) (B 26387 (by norm_num) ⟨13193, by rfl⟩ (by norm_num))
theorem R70369 : Reach 70369 := rs (se 2 (by rfl) ⟨26388, by rfl⟩) (B 52777 (by norm_num) ⟨26388, by rfl⟩ (by norm_num))
theorem R70373 : Reach 70373 := rs (se 4 (by rfl) ⟨6597, by rfl⟩) (B 13195 (by norm_num) ⟨6597, by rfl⟩ (by norm_num))
theorem R70377 : Reach 70377 := rs (se 2 (by rfl) ⟨26391, by rfl⟩) (B 52783 (by norm_num) ⟨26391, by rfl⟩ (by norm_num))
theorem R70381 : Reach 70381 := rs (se 3 (by rfl) ⟨13196, by rfl⟩) (B 26393 (by norm_num) ⟨13196, by rfl⟩ (by norm_num))
theorem R70385 : Reach 70385 := rs (se 2 (by rfl) ⟨26394, by rfl⟩) (B 52789 (by norm_num) ⟨26394, by rfl⟩ (by norm_num))
theorem R103157 : Reach 103157 := rs (se 5 (by rfl) ⟨4835, by rfl⟩) (B 9671 (by norm_num) ⟨4835, by rfl⟩ (by norm_num))
theorem R70389 : Reach 70389 := rs (se 5 (by rfl) ⟨3299, by rfl⟩) (B 6599 (by norm_num) ⟨3299, by rfl⟩ (by norm_num))
theorem R70393 : Reach 70393 := rs (se 2 (by rfl) ⟨26397, by rfl⟩) (B 52795 (by norm_num) ⟨26397, by rfl⟩ (by norm_num))
theorem R70397 : Reach 70397 := rs (se 3 (by rfl) ⟨13199, by rfl⟩) (B 26399 (by norm_num) ⟨13199, by rfl⟩ (by norm_num))
theorem R70401 : Reach 70401 := rs (se 2 (by rfl) ⟨26400, by rfl⟩) (B 52801 (by norm_num) ⟨26400, by rfl⟩ (by norm_num))
theorem R70405 : Reach 70405 := rs (se 4 (by rfl) ⟨6600, by rfl⟩) (B 13201 (by norm_num) ⟨6600, by rfl⟩ (by norm_num))
theorem R70409 : Reach 70409 := rs (se 2 (by rfl) ⟨26403, by rfl⟩) (B 52807 (by norm_num) ⟨26403, by rfl⟩ (by norm_num))
theorem R103181 : Reach 103181 := rs (se 3 (by rfl) ⟨19346, by rfl⟩) (B 38693 (by norm_num) ⟨19346, by rfl⟩ (by norm_num))
theorem R70413 : Reach 70413 := rs (se 3 (by rfl) ⟨13202, by rfl⟩) (B 26405 (by norm_num) ⟨13202, by rfl⟩ (by norm_num))
theorem R70417 : Reach 70417 := rs (se 2 (by rfl) ⟨26406, by rfl⟩) (B 52813 (by norm_num) ⟨26406, by rfl⟩ (by norm_num))
theorem R70421 : Reach 70421 := rs (se 6 (by rfl) ⟨1650, by rfl⟩) (B 3301 (by norm_num) ⟨1650, by rfl⟩ (by norm_num))
theorem R1151765 : Reach 1151765 := rs (se 6 (by rfl) ⟨26994, by rfl⟩) (B 53989 (by norm_num) ⟨26994, by rfl⟩ (by norm_num))
theorem R70425 : Reach 70425 := rs (se 2 (by rfl) ⟨26409, by rfl⟩) (B 52819 (by norm_num) ⟨26409, by rfl⟩ (by norm_num))
theorem R70429 : Reach 70429 := rs (se 3 (by rfl) ⟨13205, by rfl⟩) (B 26411 (by norm_num) ⟨13205, by rfl⟩ (by norm_num))
theorem R70433 : Reach 70433 := rs (se 2 (by rfl) ⟨26412, by rfl⟩) (B 52825 (by norm_num) ⟨26412, by rfl⟩ (by norm_num))
theorem R103205 : Reach 103205 := rs (se 4 (by rfl) ⟨9675, by rfl⟩) (B 19351 (by norm_num) ⟨9675, by rfl⟩ (by norm_num))
theorem R70437 : Reach 70437 := rs (se 4 (by rfl) ⟨6603, by rfl⟩) (B 13207 (by norm_num) ⟨6603, by rfl⟩ (by norm_num))
theorem R70441 : Reach 70441 := rs (se 2 (by rfl) ⟨26415, by rfl⟩) (B 52831 (by norm_num) ⟨26415, by rfl⟩ (by norm_num))
theorem R70445 : Reach 70445 := rs (se 3 (by rfl) ⟨13208, by rfl⟩) (B 26417 (by norm_num) ⟨13208, by rfl⟩ (by norm_num))
theorem R70449 : Reach 70449 := rs (se 2 (by rfl) ⟨26418, by rfl⟩) (B 52837 (by norm_num) ⟨26418, by rfl⟩ (by norm_num))
theorem R70453 : Reach 70453 := rs (se 5 (by rfl) ⟨3302, by rfl⟩) (B 6605 (by norm_num) ⟨3302, by rfl⟩ (by norm_num))
theorem R70457 : Reach 70457 := rs (se 2 (by rfl) ⟨26421, by rfl⟩) (B 52843 (by norm_num) ⟨26421, by rfl⟩ (by norm_num))
theorem R103229 : Reach 103229 := rs (se 3 (by rfl) ⟨19355, by rfl⟩) (B 38711 (by norm_num) ⟨19355, by rfl⟩ (by norm_num))
theorem R70461 : Reach 70461 := rs (se 3 (by rfl) ⟨13211, by rfl⟩) (B 26423 (by norm_num) ⟨13211, by rfl⟩ (by norm_num))
theorem R70465 : Reach 70465 := rs (se 2 (by rfl) ⟨26424, by rfl⟩) (B 52849 (by norm_num) ⟨26424, by rfl⟩ (by norm_num))
theorem R70469 : Reach 70469 := rs (se 4 (by rfl) ⟨6606, by rfl⟩) (B 13213 (by norm_num) ⟨6606, by rfl⟩ (by norm_num))
theorem R70473 : Reach 70473 := rs (se 2 (by rfl) ⟨26427, by rfl⟩) (B 52855 (by norm_num) ⟨26427, by rfl⟩ (by norm_num))
theorem R70477 : Reach 70477 := rs (se 3 (by rfl) ⟨13214, by rfl⟩) (B 26429 (by norm_num) ⟨13214, by rfl⟩ (by norm_num))
theorem R70481 : Reach 70481 := rs (se 2 (by rfl) ⟨26430, by rfl⟩) (B 52861 (by norm_num) ⟨26430, by rfl⟩ (by norm_num))
theorem R103253 : Reach 103253 := rs (se 9 (by rfl) ⟨302, by rfl⟩) (B 605 (by norm_num) ⟨302, by rfl⟩ (by norm_num))
theorem R70485 : Reach 70485 := rs (se 9 (by rfl) ⟨206, by rfl⟩) (B 413 (by norm_num) ⟨206, by rfl⟩ (by norm_num))
theorem R70489 : Reach 70489 := rs (se 2 (by rfl) ⟨26433, by rfl⟩) (B 52867 (by norm_num) ⟨26433, by rfl⟩ (by norm_num))
theorem R70493 : Reach 70493 := rs (se 3 (by rfl) ⟨13217, by rfl⟩) (B 26435 (by norm_num) ⟨13217, by rfl⟩ (by norm_num))
theorem R70497 : Reach 70497 := rs (se 2 (by rfl) ⟨26436, by rfl⟩) (B 52873 (by norm_num) ⟨26436, by rfl⟩ (by norm_num))
theorem R70501 : Reach 70501 := rs (se 4 (by rfl) ⟨6609, by rfl⟩) (B 13219 (by norm_num) ⟨6609, by rfl⟩ (by norm_num))
theorem R70505 : Reach 70505 := rs (se 2 (by rfl) ⟨26439, by rfl⟩) (B 52879 (by norm_num) ⟨26439, by rfl⟩ (by norm_num))
theorem R103277 : Reach 103277 := rs (se 3 (by rfl) ⟨19364, by rfl⟩) (B 38729 (by norm_num) ⟨19364, by rfl⟩ (by norm_num))
theorem R70509 : Reach 70509 := rs (se 3 (by rfl) ⟨13220, by rfl⟩) (B 26441 (by norm_num) ⟨13220, by rfl⟩ (by norm_num))
theorem R70513 : Reach 70513 := rs (se 2 (by rfl) ⟨26442, by rfl⟩) (B 52885 (by norm_num) ⟨26442, by rfl⟩ (by norm_num))
theorem R70517 : Reach 70517 := rs (se 5 (by rfl) ⟨3305, by rfl⟩) (B 6611 (by norm_num) ⟨3305, by rfl⟩ (by norm_num))
theorem R70521 : Reach 70521 := rs (se 2 (by rfl) ⟨26445, by rfl⟩) (B 52891 (by norm_num) ⟨26445, by rfl⟩ (by norm_num))
theorem R70525 : Reach 70525 := rs (se 3 (by rfl) ⟨13223, by rfl⟩) (B 26447 (by norm_num) ⟨13223, by rfl⟩ (by norm_num))
theorem R70529 : Reach 70529 := rs (se 2 (by rfl) ⟨26448, by rfl⟩) (B 52897 (by norm_num) ⟨26448, by rfl⟩ (by norm_num))
theorem R103301 : Reach 103301 := rs (se 4 (by rfl) ⟨9684, by rfl⟩) (B 19369 (by norm_num) ⟨9684, by rfl⟩ (by norm_num))
theorem R70533 : Reach 70533 := rs (se 4 (by rfl) ⟨6612, by rfl⟩) (B 13225 (by norm_num) ⟨6612, by rfl⟩ (by norm_num))
theorem R70537 : Reach 70537 := rs (se 2 (by rfl) ⟨26451, by rfl⟩) (B 52903 (by norm_num) ⟨26451, by rfl⟩ (by norm_num))
theorem R70541 : Reach 70541 := rs (se 3 (by rfl) ⟨13226, by rfl⟩) (B 26453 (by norm_num) ⟨13226, by rfl⟩ (by norm_num))
theorem R70545 : Reach 70545 := rs (se 2 (by rfl) ⟨26454, by rfl⟩) (B 52909 (by norm_num) ⟨26454, by rfl⟩ (by norm_num))
theorem R70549 : Reach 70549 := rs (se 6 (by rfl) ⟨1653, by rfl⟩) (B 3307 (by norm_num) ⟨1653, by rfl⟩ (by norm_num))
theorem R70553 : Reach 70553 := rs (se 2 (by rfl) ⟨26457, by rfl⟩) (B 52915 (by norm_num) ⟨26457, by rfl⟩ (by norm_num))
theorem R103325 : Reach 103325 := rs (se 3 (by rfl) ⟨19373, by rfl⟩) (B 38747 (by norm_num) ⟨19373, by rfl⟩ (by norm_num))
theorem R70557 : Reach 70557 := rs (se 3 (by rfl) ⟨13229, by rfl⟩) (B 26459 (by norm_num) ⟨13229, by rfl⟩ (by norm_num))
theorem R70561 : Reach 70561 := rs (se 2 (by rfl) ⟨26460, by rfl⟩) (B 52921 (by norm_num) ⟨26460, by rfl⟩ (by norm_num))
theorem R70565 : Reach 70565 := rs (se 4 (by rfl) ⟨6615, by rfl⟩) (B 13231 (by norm_num) ⟨6615, by rfl⟩ (by norm_num))
theorem R70569 : Reach 70569 := rs (se 2 (by rfl) ⟨26463, by rfl⟩) (B 52927 (by norm_num) ⟨26463, by rfl⟩ (by norm_num))
theorem R70573 : Reach 70573 := rs (se 3 (by rfl) ⟨13232, by rfl⟩) (B 26465 (by norm_num) ⟨13232, by rfl⟩ (by norm_num))
theorem R70577 : Reach 70577 := rs (se 2 (by rfl) ⟨26466, by rfl⟩) (B 52933 (by norm_num) ⟨26466, by rfl⟩ (by norm_num))
theorem R103349 : Reach 103349 := rs (se 5 (by rfl) ⟨4844, by rfl⟩) (B 9689 (by norm_num) ⟨4844, by rfl⟩ (by norm_num))
theorem R70581 : Reach 70581 := rs (se 5 (by rfl) ⟨3308, by rfl⟩) (B 6617 (by norm_num) ⟨3308, by rfl⟩ (by norm_num))
theorem R70585 : Reach 70585 := rs (se 2 (by rfl) ⟨26469, by rfl⟩) (B 52939 (by norm_num) ⟨26469, by rfl⟩ (by norm_num))
theorem R70589 : Reach 70589 := rs (se 3 (by rfl) ⟨13235, by rfl⟩) (B 26471 (by norm_num) ⟨13235, by rfl⟩ (by norm_num))
theorem R70593 : Reach 70593 := rs (se 2 (by rfl) ⟨26472, by rfl⟩) (B 52945 (by norm_num) ⟨26472, by rfl⟩ (by norm_num))
theorem R70597 : Reach 70597 := rs (se 4 (by rfl) ⟨6618, by rfl⟩) (B 13237 (by norm_num) ⟨6618, by rfl⟩ (by norm_num))
theorem R70601 : Reach 70601 := rs (se 2 (by rfl) ⟨26475, by rfl⟩) (B 52951 (by norm_num) ⟨26475, by rfl⟩ (by norm_num))
theorem R103373 : Reach 103373 := rs (se 3 (by rfl) ⟨19382, by rfl⟩) (B 38765 (by norm_num) ⟨19382, by rfl⟩ (by norm_num))
theorem R70605 : Reach 70605 := rs (se 3 (by rfl) ⟨13238, by rfl⟩) (B 26477 (by norm_num) ⟨13238, by rfl⟩ (by norm_num))
theorem R70609 : Reach 70609 := rs (se 2 (by rfl) ⟨26478, by rfl⟩) (B 52957 (by norm_num) ⟨26478, by rfl⟩ (by norm_num))
theorem R70613 : Reach 70613 := rs (se 7 (by rfl) ⟨827, by rfl⟩) (B 1655 (by norm_num) ⟨827, by rfl⟩ (by norm_num))
theorem R70617 : Reach 70617 := rs (se 2 (by rfl) ⟨26481, by rfl⟩) (B 52963 (by norm_num) ⟨26481, by rfl⟩ (by norm_num))
theorem R70621 : Reach 70621 := rs (se 3 (by rfl) ⟨13241, by rfl⟩) (B 26483 (by norm_num) ⟨13241, by rfl⟩ (by norm_num))
theorem R70625 : Reach 70625 := rs (se 2 (by rfl) ⟨26484, by rfl⟩) (B 52969 (by norm_num) ⟨26484, by rfl⟩ (by norm_num))
theorem R103397 : Reach 103397 := rs (se 4 (by rfl) ⟨9693, by rfl⟩) (B 19387 (by norm_num) ⟨9693, by rfl⟩ (by norm_num))
theorem R70629 : Reach 70629 := rs (se 4 (by rfl) ⟨6621, by rfl⟩) (B 13243 (by norm_num) ⟨6621, by rfl⟩ (by norm_num))
theorem R70633 : Reach 70633 := rs (se 2 (by rfl) ⟨26487, by rfl⟩) (B 52975 (by norm_num) ⟨26487, by rfl⟩ (by norm_num))
theorem R168941 : Reach 168941 := rs (se 3 (by rfl) ⟨31676, by rfl⟩) (B 63353 (by norm_num) ⟨31676, by rfl⟩ (by norm_num))
theorem R70637 : Reach 70637 := rs (se 3 (by rfl) ⟨13244, by rfl⟩) (B 26489 (by norm_num) ⟨13244, by rfl⟩ (by norm_num))
theorem R70641 : Reach 70641 := rs (se 2 (by rfl) ⟨26490, by rfl⟩) (B 52981 (by norm_num) ⟨26490, by rfl⟩ (by norm_num))
theorem R70645 : Reach 70645 := rs (se 5 (by rfl) ⟨3311, by rfl⟩) (B 6623 (by norm_num) ⟨3311, by rfl⟩ (by norm_num))
theorem R70649 : Reach 70649 := rs (se 2 (by rfl) ⟨26493, by rfl⟩) (B 52987 (by norm_num) ⟨26493, by rfl⟩ (by norm_num))
theorem R103421 : Reach 103421 := rs (se 3 (by rfl) ⟨19391, by rfl⟩) (B 38783 (by norm_num) ⟨19391, by rfl⟩ (by norm_num))
theorem R70653 : Reach 70653 := rs (se 3 (by rfl) ⟨13247, by rfl⟩) (B 26495 (by norm_num) ⟨13247, by rfl⟩ (by norm_num))
theorem R70657 : Reach 70657 := rs (se 2 (by rfl) ⟨26496, by rfl⟩) (B 52993 (by norm_num) ⟨26496, by rfl⟩ (by norm_num))
theorem R70661 : Reach 70661 := rs (se 4 (by rfl) ⟨6624, by rfl⟩) (B 13249 (by norm_num) ⟨6624, by rfl⟩ (by norm_num))
theorem R70665 : Reach 70665 := rs (se 2 (by rfl) ⟨26499, by rfl⟩) (B 52999 (by norm_num) ⟨26499, by rfl⟩ (by norm_num))
theorem R70669 : Reach 70669 := rs (se 3 (by rfl) ⟨13250, by rfl⟩) (B 26501 (by norm_num) ⟨13250, by rfl⟩ (by norm_num))
theorem R70673 : Reach 70673 := rs (se 2 (by rfl) ⟨26502, by rfl⟩) (B 53005 (by norm_num) ⟨26502, by rfl⟩ (by norm_num))
theorem R103445 : Reach 103445 := rs (se 6 (by rfl) ⟨2424, by rfl⟩) (B 4849 (by norm_num) ⟨2424, by rfl⟩ (by norm_num))
theorem R70677 : Reach 70677 := rs (se 6 (by rfl) ⟨1656, by rfl⟩) (B 3313 (by norm_num) ⟨1656, by rfl⟩ (by norm_num))
theorem R70681 : Reach 70681 := rs (se 2 (by rfl) ⟨26505, by rfl⟩) (B 53011 (by norm_num) ⟨26505, by rfl⟩ (by norm_num))
theorem R70685 : Reach 70685 := rs (se 3 (by rfl) ⟨13253, by rfl⟩) (B 26507 (by norm_num) ⟨13253, by rfl⟩ (by norm_num))
theorem R70689 : Reach 70689 := rs (se 2 (by rfl) ⟨26508, by rfl⟩) (B 53017 (by norm_num) ⟨26508, by rfl⟩ (by norm_num))
theorem R70693 : Reach 70693 := rs (se 4 (by rfl) ⟨6627, by rfl⟩) (B 13255 (by norm_num) ⟨6627, by rfl⟩ (by norm_num))
theorem R70697 : Reach 70697 := rs (se 2 (by rfl) ⟨26511, by rfl⟩) (B 53023 (by norm_num) ⟨26511, by rfl⟩ (by norm_num))
theorem R103469 : Reach 103469 := rs (se 3 (by rfl) ⟨19400, by rfl⟩) (B 38801 (by norm_num) ⟨19400, by rfl⟩ (by norm_num))
theorem R70701 : Reach 70701 := rs (se 3 (by rfl) ⟨13256, by rfl⟩) (B 26513 (by norm_num) ⟨13256, by rfl⟩ (by norm_num))
theorem R70705 : Reach 70705 := rs (se 2 (by rfl) ⟨26514, by rfl⟩) (B 53029 (by norm_num) ⟨26514, by rfl⟩ (by norm_num))
theorem R70709 : Reach 70709 := rs (se 5 (by rfl) ⟨3314, by rfl⟩) (B 6629 (by norm_num) ⟨3314, by rfl⟩ (by norm_num))
theorem R70713 : Reach 70713 := rs (se 2 (by rfl) ⟨26517, by rfl⟩) (B 53035 (by norm_num) ⟨26517, by rfl⟩ (by norm_num))
theorem R70717 : Reach 70717 := rs (se 3 (by rfl) ⟨13259, by rfl⟩) (B 26519 (by norm_num) ⟨13259, by rfl⟩ (by norm_num))
theorem R70721 : Reach 70721 := rs (se 2 (by rfl) ⟨26520, by rfl⟩) (B 53041 (by norm_num) ⟨26520, by rfl⟩ (by norm_num))
theorem R103493 : Reach 103493 := rs (se 4 (by rfl) ⟨9702, by rfl⟩) (B 19405 (by norm_num) ⟨9702, by rfl⟩ (by norm_num))
theorem R70725 : Reach 70725 := rs (se 4 (by rfl) ⟨6630, by rfl⟩) (B 13261 (by norm_num) ⟨6630, by rfl⟩ (by norm_num))
theorem R201797 : Reach 201797 := rs (se 4 (by rfl) ⟨18918, by rfl⟩) (B 37837 (by norm_num) ⟨18918, by rfl⟩ (by norm_num))
theorem R70729 : Reach 70729 := rs (se 2 (by rfl) ⟨26523, by rfl⟩) (B 53047 (by norm_num) ⟨26523, by rfl⟩ (by norm_num))
theorem R169037 : Reach 169037 := rs (se 3 (by rfl) ⟨31694, by rfl⟩) (B 63389 (by norm_num) ⟨31694, by rfl⟩ (by norm_num))
theorem R70733 : Reach 70733 := rs (se 3 (by rfl) ⟨13262, by rfl⟩) (B 26525 (by norm_num) ⟨13262, by rfl⟩ (by norm_num))
theorem R70737 : Reach 70737 := rs (se 2 (by rfl) ⟨26526, by rfl⟩) (B 53053 (by norm_num) ⟨26526, by rfl⟩ (by norm_num))
theorem R70741 : Reach 70741 := rs (se 8 (by rfl) ⟨414, by rfl⟩) (B 829 (by norm_num) ⟨414, by rfl⟩ (by norm_num))
theorem R70745 : Reach 70745 := rs (se 2 (by rfl) ⟨26529, by rfl⟩) (B 53059 (by norm_num) ⟨26529, by rfl⟩ (by norm_num))
theorem R103517 : Reach 103517 := rs (se 3 (by rfl) ⟨19409, by rfl⟩) (B 38819 (by norm_num) ⟨19409, by rfl⟩ (by norm_num))
theorem R70749 : Reach 70749 := rs (se 3 (by rfl) ⟨13265, by rfl⟩) (B 26531 (by norm_num) ⟨13265, by rfl⟩ (by norm_num))
theorem R70753 : Reach 70753 := rs (se 2 (by rfl) ⟨26532, by rfl⟩) (B 53065 (by norm_num) ⟨26532, by rfl⟩ (by norm_num))
theorem R70757 : Reach 70757 := rs (se 4 (by rfl) ⟨6633, by rfl⟩) (B 13267 (by norm_num) ⟨6633, by rfl⟩ (by norm_num))
theorem R70761 : Reach 70761 := rs (se 2 (by rfl) ⟨26535, by rfl⟩) (B 53071 (by norm_num) ⟨26535, by rfl⟩ (by norm_num))
theorem R70765 : Reach 70765 := rs (se 3 (by rfl) ⟨13268, by rfl⟩) (B 26537 (by norm_num) ⟨13268, by rfl⟩ (by norm_num))
theorem R70769 : Reach 70769 := rs (se 2 (by rfl) ⟨26538, by rfl⟩) (B 53077 (by norm_num) ⟨26538, by rfl⟩ (by norm_num))
theorem R103541 : Reach 103541 := rs (se 5 (by rfl) ⟨4853, by rfl⟩) (B 9707 (by norm_num) ⟨4853, by rfl⟩ (by norm_num))
theorem R70773 : Reach 70773 := rs (se 5 (by rfl) ⟨3317, by rfl⟩) (B 6635 (by norm_num) ⟨3317, by rfl⟩ (by norm_num))
theorem R70777 : Reach 70777 := rs (se 2 (by rfl) ⟨26541, by rfl⟩) (B 53083 (by norm_num) ⟨26541, by rfl⟩ (by norm_num))
theorem R70781 : Reach 70781 := rs (se 3 (by rfl) ⟨13271, by rfl⟩) (B 26543 (by norm_num) ⟨13271, by rfl⟩ (by norm_num))
theorem R70785 : Reach 70785 := rs (se 2 (by rfl) ⟨26544, by rfl⟩) (B 53089 (by norm_num) ⟨26544, by rfl⟩ (by norm_num))
theorem R234629 : Reach 234629 := rs (se 4 (by rfl) ⟨21996, by rfl⟩) (B 43993 (by norm_num) ⟨21996, by rfl⟩ (by norm_num))
theorem R70789 : Reach 70789 := rs (se 4 (by rfl) ⟨6636, by rfl⟩) (B 13273 (by norm_num) ⟨6636, by rfl⟩ (by norm_num))
theorem R70793 : Reach 70793 := rs (se 2 (by rfl) ⟨26547, by rfl⟩) (B 53095 (by norm_num) ⟨26547, by rfl⟩ (by norm_num))
theorem R103565 : Reach 103565 := rs (se 3 (by rfl) ⟨19418, by rfl⟩) (B 38837 (by norm_num) ⟨19418, by rfl⟩ (by norm_num))
theorem R70797 : Reach 70797 := rs (se 3 (by rfl) ⟨13274, by rfl⟩) (B 26549 (by norm_num) ⟨13274, by rfl⟩ (by norm_num))
theorem R70801 : Reach 70801 := rs (se 2 (by rfl) ⟨26550, by rfl⟩) (B 53101 (by norm_num) ⟨26550, by rfl⟩ (by norm_num))
theorem R70805 : Reach 70805 := rs (se 6 (by rfl) ⟨1659, by rfl⟩) (B 3319 (by norm_num) ⟨1659, by rfl⟩ (by norm_num))
theorem R70809 : Reach 70809 := rs (se 2 (by rfl) ⟨26553, by rfl⟩) (B 53107 (by norm_num) ⟨26553, by rfl⟩ (by norm_num))
theorem R70813 : Reach 70813 := rs (se 3 (by rfl) ⟨13277, by rfl⟩) (B 26555 (by norm_num) ⟨13277, by rfl⟩ (by norm_num))
theorem R70817 : Reach 70817 := rs (se 2 (by rfl) ⟨26556, by rfl⟩) (B 53113 (by norm_num) ⟨26556, by rfl⟩ (by norm_num))
theorem R103589 : Reach 103589 := rs (se 4 (by rfl) ⟨9711, by rfl⟩) (B 19423 (by norm_num) ⟨9711, by rfl⟩ (by norm_num))
theorem R70821 : Reach 70821 := rs (se 4 (by rfl) ⟨6639, by rfl⟩) (B 13279 (by norm_num) ⟨6639, by rfl⟩ (by norm_num))
theorem R70825 : Reach 70825 := rs (se 2 (by rfl) ⟨26559, by rfl⟩) (B 53119 (by norm_num) ⟨26559, by rfl⟩ (by norm_num))
theorem R70829 : Reach 70829 := rs (se 3 (by rfl) ⟨13280, by rfl⟩) (B 26561 (by norm_num) ⟨13280, by rfl⟩ (by norm_num))
theorem R70833 : Reach 70833 := rs (se 2 (by rfl) ⟨26562, by rfl⟩) (B 53125 (by norm_num) ⟨26562, by rfl⟩ (by norm_num))
theorem R70837 : Reach 70837 := rs (se 5 (by rfl) ⟨3320, by rfl⟩) (B 6641 (by norm_num) ⟨3320, by rfl⟩ (by norm_num))
theorem R70841 : Reach 70841 := rs (se 2 (by rfl) ⟨26565, by rfl⟩) (B 53131 (by norm_num) ⟨26565, by rfl⟩ (by norm_num))
theorem R103613 : Reach 103613 := rs (se 3 (by rfl) ⟨19427, by rfl⟩) (B 38855 (by norm_num) ⟨19427, by rfl⟩ (by norm_num))
theorem R70845 : Reach 70845 := rs (se 3 (by rfl) ⟨13283, by rfl⟩) (B 26567 (by norm_num) ⟨13283, by rfl⟩ (by norm_num))
theorem R70849 : Reach 70849 := rs (se 2 (by rfl) ⟨26568, by rfl⟩) (B 53137 (by norm_num) ⟨26568, by rfl⟩ (by norm_num))
theorem R70853 : Reach 70853 := rs (se 4 (by rfl) ⟨6642, by rfl⟩) (B 13285 (by norm_num) ⟨6642, by rfl⟩ (by norm_num))
theorem R70857 : Reach 70857 := rs (se 2 (by rfl) ⟨26571, by rfl⟩) (B 53143 (by norm_num) ⟨26571, by rfl⟩ (by norm_num))
theorem R70861 : Reach 70861 := rs (se 3 (by rfl) ⟨13286, by rfl⟩) (B 26573 (by norm_num) ⟨13286, by rfl⟩ (by norm_num))
theorem R70865 : Reach 70865 := rs (se 2 (by rfl) ⟨26574, by rfl⟩) (B 53149 (by norm_num) ⟨26574, by rfl⟩ (by norm_num))
theorem R103637 : Reach 103637 := rs (se 7 (by rfl) ⟨1214, by rfl⟩) (B 2429 (by norm_num) ⟨1214, by rfl⟩ (by norm_num))
theorem R70869 : Reach 70869 := rs (se 7 (by rfl) ⟨830, by rfl⟩) (B 1661 (by norm_num) ⟨830, by rfl⟩ (by norm_num))
theorem R70873 : Reach 70873 := rs (se 2 (by rfl) ⟨26577, by rfl⟩) (B 53155 (by norm_num) ⟨26577, by rfl⟩ (by norm_num))
theorem R70877 : Reach 70877 := rs (se 3 (by rfl) ⟨13289, by rfl⟩) (B 26579 (by norm_num) ⟨13289, by rfl⟩ (by norm_num))
theorem R70881 : Reach 70881 := rs (se 2 (by rfl) ⟨26580, by rfl⟩) (B 53161 (by norm_num) ⟨26580, by rfl⟩ (by norm_num))
theorem R70885 : Reach 70885 := rs (se 4 (by rfl) ⟨6645, by rfl⟩) (B 13291 (by norm_num) ⟨6645, by rfl⟩ (by norm_num))
theorem R70889 : Reach 70889 := rs (se 2 (by rfl) ⟨26583, by rfl⟩) (B 53167 (by norm_num) ⟨26583, by rfl⟩ (by norm_num))
theorem R103661 : Reach 103661 := rs (se 3 (by rfl) ⟨19436, by rfl⟩) (B 38873 (by norm_num) ⟨19436, by rfl⟩ (by norm_num))
theorem R70893 : Reach 70893 := rs (se 3 (by rfl) ⟨13292, by rfl⟩) (B 26585 (by norm_num) ⟨13292, by rfl⟩ (by norm_num))
theorem R70897 : Reach 70897 := rs (se 2 (by rfl) ⟨26586, by rfl⟩) (B 53173 (by norm_num) ⟨26586, by rfl⟩ (by norm_num))
theorem R70901 : Reach 70901 := rs (se 5 (by rfl) ⟨3323, by rfl⟩) (B 6647 (by norm_num) ⟨3323, by rfl⟩ (by norm_num))
theorem R70905 : Reach 70905 := rs (se 2 (by rfl) ⟨26589, by rfl⟩) (B 53179 (by norm_num) ⟨26589, by rfl⟩ (by norm_num))
theorem R70909 : Reach 70909 := rs (se 3 (by rfl) ⟨13295, by rfl⟩) (B 26591 (by norm_num) ⟨13295, by rfl⟩ (by norm_num))
theorem R70913 : Reach 70913 := rs (se 2 (by rfl) ⟨26592, by rfl⟩) (B 53185 (by norm_num) ⟨26592, by rfl⟩ (by norm_num))
theorem R103685 : Reach 103685 := rs (se 4 (by rfl) ⟨9720, by rfl⟩) (B 19441 (by norm_num) ⟨9720, by rfl⟩ (by norm_num))
theorem R70917 : Reach 70917 := rs (se 4 (by rfl) ⟨6648, by rfl⟩) (B 13297 (by norm_num) ⟨6648, by rfl⟩ (by norm_num))
theorem R70921 : Reach 70921 := rs (se 2 (by rfl) ⟨26595, by rfl⟩) (B 53191 (by norm_num) ⟨26595, by rfl⟩ (by norm_num))
theorem R169229 : Reach 169229 := rs (se 3 (by rfl) ⟨31730, by rfl⟩) (B 63461 (by norm_num) ⟨31730, by rfl⟩ (by norm_num))
theorem R70925 : Reach 70925 := rs (se 3 (by rfl) ⟨13298, by rfl⟩) (B 26597 (by norm_num) ⟨13298, by rfl⟩ (by norm_num))
theorem R70929 : Reach 70929 := rs (se 2 (by rfl) ⟨26598, by rfl⟩) (B 53197 (by norm_num) ⟨26598, by rfl⟩ (by norm_num))
theorem R70933 : Reach 70933 := rs (se 6 (by rfl) ⟨1662, by rfl⟩) (B 3325 (by norm_num) ⟨1662, by rfl⟩ (by norm_num))
theorem R70937 : Reach 70937 := rs (se 2 (by rfl) ⟨26601, by rfl⟩) (B 53203 (by norm_num) ⟨26601, by rfl⟩ (by norm_num))
theorem R103709 : Reach 103709 := rs (se 3 (by rfl) ⟨19445, by rfl⟩) (B 38891 (by norm_num) ⟨19445, by rfl⟩ (by norm_num))
theorem R70941 : Reach 70941 := rs (se 3 (by rfl) ⟨13301, by rfl⟩) (B 26603 (by norm_num) ⟨13301, by rfl⟩ (by norm_num))
theorem R70945 : Reach 70945 := rs (se 2 (by rfl) ⟨26604, by rfl⟩) (B 53209 (by norm_num) ⟨26604, by rfl⟩ (by norm_num))
theorem R70949 : Reach 70949 := rs (se 4 (by rfl) ⟨6651, by rfl⟩) (B 13303 (by norm_num) ⟨6651, by rfl⟩ (by norm_num))
theorem R70953 : Reach 70953 := rs (se 2 (by rfl) ⟨26607, by rfl⟩) (B 53215 (by norm_num) ⟨26607, by rfl⟩ (by norm_num))
theorem R70957 : Reach 70957 := rs (se 3 (by rfl) ⟨13304, by rfl⟩) (B 26609 (by norm_num) ⟨13304, by rfl⟩ (by norm_num))
theorem R70961 : Reach 70961 := rs (se 2 (by rfl) ⟨26610, by rfl⟩) (B 53221 (by norm_num) ⟨26610, by rfl⟩ (by norm_num))
theorem R103733 : Reach 103733 := rs (se 5 (by rfl) ⟨4862, by rfl⟩) (B 9725 (by norm_num) ⟨4862, by rfl⟩ (by norm_num))
theorem R70965 : Reach 70965 := rs (se 5 (by rfl) ⟨3326, by rfl⟩) (B 6653 (by norm_num) ⟨3326, by rfl⟩ (by norm_num))
theorem R70969 : Reach 70969 := rs (se 2 (by rfl) ⟨26613, by rfl⟩) (B 53227 (by norm_num) ⟨26613, by rfl⟩ (by norm_num))
theorem R70973 : Reach 70973 := rs (se 3 (by rfl) ⟨13307, by rfl⟩) (B 26615 (by norm_num) ⟨13307, by rfl⟩ (by norm_num))
theorem R70977 : Reach 70977 := rs (se 2 (by rfl) ⟨26616, by rfl⟩) (B 53233 (by norm_num) ⟨26616, by rfl⟩ (by norm_num))
theorem R70981 : Reach 70981 := rs (se 4 (by rfl) ⟨6654, by rfl⟩) (B 13309 (by norm_num) ⟨6654, by rfl⟩ (by norm_num))
theorem R70985 : Reach 70985 := rs (se 2 (by rfl) ⟨26619, by rfl⟩) (B 53239 (by norm_num) ⟨26619, by rfl⟩ (by norm_num))
theorem R103757 : Reach 103757 := rs (se 3 (by rfl) ⟨19454, by rfl⟩) (B 38909 (by norm_num) ⟨19454, by rfl⟩ (by norm_num))
theorem R70989 : Reach 70989 := rs (se 3 (by rfl) ⟨13310, by rfl⟩) (B 26621 (by norm_num) ⟨13310, by rfl⟩ (by norm_num))
theorem R70993 : Reach 70993 := rs (se 2 (by rfl) ⟨26622, by rfl⟩) (B 53245 (by norm_num) ⟨26622, by rfl⟩ (by norm_num))
theorem R70997 : Reach 70997 := rs (se 14 (by rfl) ⟨6, by rfl⟩) (B 13 (by norm_num) ⟨6, by rfl⟩ (by norm_num))
theorem R71001 : Reach 71001 := rs (se 2 (by rfl) ⟨26625, by rfl⟩) (B 53251 (by norm_num) ⟨26625, by rfl⟩ (by norm_num))
theorem R71005 : Reach 71005 := rs (se 3 (by rfl) ⟨13313, by rfl⟩) (B 26627 (by norm_num) ⟨13313, by rfl⟩ (by norm_num))
theorem R71009 : Reach 71009 := rs (se 2 (by rfl) ⟨26628, by rfl⟩) (B 53257 (by norm_num) ⟨26628, by rfl⟩ (by norm_num))
theorem R103781 : Reach 103781 := rs (se 4 (by rfl) ⟨9729, by rfl⟩) (B 19459 (by norm_num) ⟨9729, by rfl⟩ (by norm_num))
theorem R71013 : Reach 71013 := rs (se 4 (by rfl) ⟨6657, by rfl⟩) (B 13315 (by norm_num) ⟨6657, by rfl⟩ (by norm_num))
theorem R71017 : Reach 71017 := rs (se 2 (by rfl) ⟨26631, by rfl⟩) (B 53263 (by norm_num) ⟨26631, by rfl⟩ (by norm_num))
theorem R71021 : Reach 71021 := rs (se 3 (by rfl) ⟨13316, by rfl⟩) (B 26633 (by norm_num) ⟨13316, by rfl⟩ (by norm_num))
theorem R71025 : Reach 71025 := rs (se 2 (by rfl) ⟨26634, by rfl⟩) (B 53269 (by norm_num) ⟨26634, by rfl⟩ (by norm_num))
theorem R71029 : Reach 71029 := rs (se 5 (by rfl) ⟨3329, by rfl⟩) (B 6659 (by norm_num) ⟨3329, by rfl⟩ (by norm_num))
theorem R71033 : Reach 71033 := rs (se 2 (by rfl) ⟨26637, by rfl⟩) (B 53275 (by norm_num) ⟨26637, by rfl⟩ (by norm_num))
theorem R103805 : Reach 103805 := rs (se 3 (by rfl) ⟨19463, by rfl⟩) (B 38927 (by norm_num) ⟨19463, by rfl⟩ (by norm_num))
theorem R71037 : Reach 71037 := rs (se 3 (by rfl) ⟨13319, by rfl⟩) (B 26639 (by norm_num) ⟨13319, by rfl⟩ (by norm_num))
theorem R71041 : Reach 71041 := rs (se 2 (by rfl) ⟨26640, by rfl⟩) (B 53281 (by norm_num) ⟨26640, by rfl⟩ (by norm_num))
theorem R71045 : Reach 71045 := rs (se 4 (by rfl) ⟨6660, by rfl⟩) (B 13321 (by norm_num) ⟨6660, by rfl⟩ (by norm_num))
theorem R71049 : Reach 71049 := rs (se 2 (by rfl) ⟨26643, by rfl⟩) (B 53287 (by norm_num) ⟨26643, by rfl⟩ (by norm_num))
theorem R71053 : Reach 71053 := rs (se 3 (by rfl) ⟨13322, by rfl⟩) (B 26645 (by norm_num) ⟨13322, by rfl⟩ (by norm_num))
theorem R71057 : Reach 71057 := rs (se 2 (by rfl) ⟨26646, by rfl⟩) (B 53293 (by norm_num) ⟨26646, by rfl⟩ (by norm_num))
theorem R103829 : Reach 103829 := rs (se 6 (by rfl) ⟨2433, by rfl⟩) (B 4867 (by norm_num) ⟨2433, by rfl⟩ (by norm_num))
theorem R71061 : Reach 71061 := rs (se 6 (by rfl) ⟨1665, by rfl⟩) (B 3331 (by norm_num) ⟨1665, by rfl⟩ (by norm_num))
theorem R71065 : Reach 71065 := rs (se 2 (by rfl) ⟨26649, by rfl⟩) (B 53299 (by norm_num) ⟨26649, by rfl⟩ (by norm_num))
theorem R71069 : Reach 71069 := rs (se 3 (by rfl) ⟨13325, by rfl⟩) (B 26651 (by norm_num) ⟨13325, by rfl⟩ (by norm_num))
theorem R71073 : Reach 71073 := rs (se 2 (by rfl) ⟨26652, by rfl⟩) (B 53305 (by norm_num) ⟨26652, by rfl⟩ (by norm_num))
theorem R71077 : Reach 71077 := rs (se 4 (by rfl) ⟨6663, by rfl⟩) (B 13327 (by norm_num) ⟨6663, by rfl⟩ (by norm_num))
theorem R71081 : Reach 71081 := rs (se 2 (by rfl) ⟨26655, by rfl⟩) (B 53311 (by norm_num) ⟨26655, by rfl⟩ (by norm_num))
theorem R103853 : Reach 103853 := rs (se 3 (by rfl) ⟨19472, by rfl⟩) (B 38945 (by norm_num) ⟨19472, by rfl⟩ (by norm_num))
theorem R71085 : Reach 71085 := rs (se 3 (by rfl) ⟨13328, by rfl⟩) (B 26657 (by norm_num) ⟨13328, by rfl⟩ (by norm_num))
theorem R71089 : Reach 71089 := rs (se 2 (by rfl) ⟨26658, by rfl⟩) (B 53317 (by norm_num) ⟨26658, by rfl⟩ (by norm_num))
theorem R71093 : Reach 71093 := rs (se 5 (by rfl) ⟨3332, by rfl⟩) (B 6665 (by norm_num) ⟨3332, by rfl⟩ (by norm_num))
theorem R71097 : Reach 71097 := rs (se 2 (by rfl) ⟨26661, by rfl⟩) (B 53323 (by norm_num) ⟨26661, by rfl⟩ (by norm_num))
theorem R71101 : Reach 71101 := rs (se 3 (by rfl) ⟨13331, by rfl⟩) (B 26663 (by norm_num) ⟨13331, by rfl⟩ (by norm_num))
theorem R71105 : Reach 71105 := rs (se 2 (by rfl) ⟨26664, by rfl⟩) (B 53329 (by norm_num) ⟨26664, by rfl⟩ (by norm_num))
theorem R103877 : Reach 103877 := rs (se 4 (by rfl) ⟨9738, by rfl⟩) (B 19477 (by norm_num) ⟨9738, by rfl⟩ (by norm_num))
theorem R71109 : Reach 71109 := rs (se 4 (by rfl) ⟨6666, by rfl⟩) (B 13333 (by norm_num) ⟨6666, by rfl⟩ (by norm_num))
theorem R71113 : Reach 71113 := rs (se 2 (by rfl) ⟨26667, by rfl⟩) (B 53335 (by norm_num) ⟨26667, by rfl⟩ (by norm_num))
theorem R71117 : Reach 71117 := rs (se 3 (by rfl) ⟨13334, by rfl⟩) (B 26669 (by norm_num) ⟨13334, by rfl⟩ (by norm_num))
theorem R71121 : Reach 71121 := rs (se 2 (by rfl) ⟨26670, by rfl⟩) (B 53341 (by norm_num) ⟨26670, by rfl⟩ (by norm_num))
theorem R103901 : Reach 103901 := rs (se 3 (by rfl) ⟨19481, by rfl⟩) (B 38963 (by norm_num) ⟨19481, by rfl⟩ (by norm_num))
theorem R103925 : Reach 103925 := rs (se 5 (by rfl) ⟨4871, by rfl⟩) (B 9743 (by norm_num) ⟨4871, by rfl⟩ (by norm_num))
theorem R103949 : Reach 103949 := rs (se 3 (by rfl) ⟨19490, by rfl⟩) (B 38981 (by norm_num) ⟨19490, by rfl⟩ (by norm_num))
theorem R103973 : Reach 103973 := rs (se 4 (by rfl) ⟨9747, by rfl⟩) (B 19495 (by norm_num) ⟨9747, by rfl⟩ (by norm_num))
theorem R235061 : Reach 235061 := rs (se 5 (by rfl) ⟨11018, by rfl⟩) (B 22037 (by norm_num) ⟨11018, by rfl⟩ (by norm_num))
theorem R103997 : Reach 103997 := rs (se 3 (by rfl) ⟨19499, by rfl⟩) (B 38999 (by norm_num) ⟨19499, by rfl⟩ (by norm_num))
theorem R104021 : Reach 104021 := rs (se 8 (by rfl) ⟨609, by rfl⟩) (B 1219 (by norm_num) ⟨609, by rfl⟩ (by norm_num))
theorem R104045 : Reach 104045 := rs (se 3 (by rfl) ⟨19508, by rfl⟩) (B 39017 (by norm_num) ⟨19508, by rfl⟩ (by norm_num))
theorem R267893 : Reach 267893 := rs (se 5 (by rfl) ⟨12557, by rfl⟩) (B 25115 (by norm_num) ⟨12557, by rfl⟩ (by norm_num))
theorem R136829 : Reach 136829 := rs (se 3 (by rfl) ⟨25655, by rfl⟩) (B 51311 (by norm_num) ⟨25655, by rfl⟩ (by norm_num))
theorem R104069 : Reach 104069 := rs (se 4 (by rfl) ⟨9756, by rfl⟩) (B 19513 (by norm_num) ⟨9756, by rfl⟩ (by norm_num))
theorem R104093 : Reach 104093 := rs (se 3 (by rfl) ⟨19517, by rfl⟩) (B 39035 (by norm_num) ⟨19517, by rfl⟩ (by norm_num))
theorem R202405 : Reach 202405 := rs (se 4 (by rfl) ⟨18975, by rfl⟩) (B 37951 (by norm_num) ⟨18975, by rfl⟩ (by norm_num))
theorem R104117 : Reach 104117 := rs (se 5 (by rfl) ⟨4880, by rfl⟩) (B 9761 (by norm_num) ⟨4880, by rfl⟩ (by norm_num))
theorem R169661 : Reach 169661 := rs (se 3 (by rfl) ⟨31811, by rfl⟩) (B 63623 (by norm_num) ⟨31811, by rfl⟩ (by norm_num))
theorem R104141 : Reach 104141 := rs (se 3 (by rfl) ⟨19526, by rfl⟩) (B 39053 (by norm_num) ⟨19526, by rfl⟩ (by norm_num))
theorem R104165 : Reach 104165 := rs (se 4 (by rfl) ⟨9765, by rfl⟩) (B 19531 (by norm_num) ⟨9765, by rfl⟩ (by norm_num))
theorem R104189 : Reach 104189 := rs (se 3 (by rfl) ⟨19535, by rfl⟩) (B 39071 (by norm_num) ⟨19535, by rfl⟩ (by norm_num))
theorem R104213 : Reach 104213 := rs (se 6 (by rfl) ⟨2442, by rfl⟩) (B 4885 (by norm_num) ⟨2442, by rfl⟩ (by norm_num))
theorem R104237 : Reach 104237 := rs (se 3 (by rfl) ⟨19544, by rfl⟩) (B 39089 (by norm_num) ⟨19544, by rfl⟩ (by norm_num))
theorem R104261 : Reach 104261 := rs (se 4 (by rfl) ⟨9774, by rfl⟩) (B 19549 (by norm_num) ⟨9774, by rfl⟩ (by norm_num))
theorem R104285 : Reach 104285 := rs (se 3 (by rfl) ⟨19553, by rfl⟩) (B 39107 (by norm_num) ⟨19553, by rfl⟩ (by norm_num))
theorem R104309 : Reach 104309 := rs (se 5 (by rfl) ⟨4889, by rfl⟩) (B 9779 (by norm_num) ⟨4889, by rfl⟩ (by norm_num))
theorem R104333 : Reach 104333 := rs (se 3 (by rfl) ⟨19562, by rfl⟩) (B 39125 (by norm_num) ⟨19562, by rfl⟩ (by norm_num))
theorem R268181 : Reach 268181 := rs (se 6 (by rfl) ⟨6285, by rfl⟩) (B 12571 (by norm_num) ⟨6285, by rfl⟩ (by norm_num))
theorem R104357 : Reach 104357 := rs (se 4 (by rfl) ⟨9783, by rfl⟩) (B 19567 (by norm_num) ⟨9783, by rfl⟩ (by norm_num))
theorem R104381 : Reach 104381 := rs (se 3 (by rfl) ⟨19571, by rfl⟩) (B 39143 (by norm_num) ⟨19571, by rfl⟩ (by norm_num))
theorem R104405 : Reach 104405 := rs (se 7 (by rfl) ⟨1223, by rfl⟩) (B 2447 (by norm_num) ⟨1223, by rfl⟩ (by norm_num))
theorem R235493 : Reach 235493 := rs (se 4 (by rfl) ⟨22077, by rfl⟩) (B 44155 (by norm_num) ⟨22077, by rfl⟩ (by norm_num))
theorem R71653 : Reach 71653 := rs (se 4 (by rfl) ⟨6717, by rfl⟩) (B 13435 (by norm_num) ⟨6717, by rfl⟩ (by norm_num))
theorem R104429 : Reach 104429 := rs (se 3 (by rfl) ⟨19580, by rfl⟩) (B 39161 (by norm_num) ⟨19580, by rfl⟩ (by norm_num))
theorem R595957 : Reach 595957 := rs (se 5 (by rfl) ⟨27935, by rfl⟩) (B 55871 (by norm_num) ⟨27935, by rfl⟩ (by norm_num))
theorem R104453 : Reach 104453 := rs (se 4 (by rfl) ⟨9792, by rfl⟩) (B 19585 (by norm_num) ⟨9792, by rfl⟩ (by norm_num))
theorem R104477 : Reach 104477 := rs (se 3 (by rfl) ⟨19589, by rfl⟩) (B 39179 (by norm_num) ⟨19589, by rfl⟩ (by norm_num))
theorem R104501 : Reach 104501 := rs (se 5 (by rfl) ⟨4898, by rfl⟩) (B 9797 (by norm_num) ⟨4898, by rfl⟩ (by norm_num))
theorem R104525 : Reach 104525 := rs (se 3 (by rfl) ⟨19598, by rfl⟩) (B 39197 (by norm_num) ⟨19598, by rfl⟩ (by norm_num))
theorem R104549 : Reach 104549 := rs (se 4 (by rfl) ⟨9801, by rfl⟩) (B 19603 (by norm_num) ⟨9801, by rfl⟩ (by norm_num))
theorem R104573 : Reach 104573 := rs (se 3 (by rfl) ⟨19607, by rfl⟩) (B 39215 (by norm_num) ⟨19607, by rfl⟩ (by norm_num))
theorem R104597 : Reach 104597 := rs (se 6 (by rfl) ⟨2451, by rfl⟩) (B 4903 (by norm_num) ⟨2451, by rfl⟩ (by norm_num))
theorem R104621 : Reach 104621 := rs (se 3 (by rfl) ⟨19616, by rfl⟩) (B 39233 (by norm_num) ⟨19616, by rfl⟩ (by norm_num))
theorem R104645 : Reach 104645 := rs (se 4 (by rfl) ⟨9810, by rfl⟩) (B 19621 (by norm_num) ⟨9810, by rfl⟩ (by norm_num))
theorem R104669 : Reach 104669 := rs (se 3 (by rfl) ⟨19625, by rfl⟩) (B 39251 (by norm_num) ⟨19625, by rfl⟩ (by norm_num))
theorem R170221 : Reach 170221 := rs (se 3 (by rfl) ⟨31916, by rfl⟩) (B 63833 (by norm_num) ⟨31916, by rfl⟩ (by norm_num))
theorem R104693 : Reach 104693 := rs (se 5 (by rfl) ⟨4907, by rfl⟩) (B 9815 (by norm_num) ⟨4907, by rfl⟩ (by norm_num))
theorem R104701 : Reach 104701 := rs (se 3 (by rfl) ⟨19631, by rfl⟩) (B 39263 (by norm_num) ⟨19631, by rfl⟩ (by norm_num))
theorem R104717 : Reach 104717 := rs (se 3 (by rfl) ⟨19634, by rfl⟩) (B 39269 (by norm_num) ⟨19634, by rfl⟩ (by norm_num))
theorem R104741 : Reach 104741 := rs (se 4 (by rfl) ⟨9819, by rfl⟩) (B 19639 (by norm_num) ⟨9819, by rfl⟩ (by norm_num))
theorem R104765 : Reach 104765 := rs (se 3 (by rfl) ⟨19643, by rfl⟩) (B 39287 (by norm_num) ⟨19643, by rfl⟩ (by norm_num))
theorem R104789 : Reach 104789 := rs (se 10 (by rfl) ⟨153, by rfl⟩) (B 307 (by norm_num) ⟨153, by rfl⟩ (by norm_num))
theorem R170333 : Reach 170333 := rs (se 3 (by rfl) ⟨31937, by rfl⟩) (B 63875 (by norm_num) ⟨31937, by rfl⟩ (by norm_num))
theorem R104813 : Reach 104813 := rs (se 3 (by rfl) ⟨19652, by rfl⟩) (B 39305 (by norm_num) ⟨19652, by rfl⟩ (by norm_num))
theorem R104837 : Reach 104837 := rs (se 4 (by rfl) ⟨9828, by rfl⟩) (B 19657 (by norm_num) ⟨9828, by rfl⟩ (by norm_num))
theorem R170381 : Reach 170381 := rs (se 3 (by rfl) ⟨31946, by rfl⟩) (B 63893 (by norm_num) ⟨31946, by rfl⟩ (by norm_num))
theorem R235925 : Reach 235925 := rs (se 6 (by rfl) ⟨5529, by rfl⟩) (B 11059 (by norm_num) ⟨5529, by rfl⟩ (by norm_num))
theorem R104861 : Reach 104861 := rs (se 3 (by rfl) ⟨19661, by rfl⟩) (B 39323 (by norm_num) ⟨19661, by rfl⟩ (by norm_num))
theorem R104885 : Reach 104885 := rs (se 5 (by rfl) ⟨4916, by rfl⟩) (B 9833 (by norm_num) ⟨4916, by rfl⟩ (by norm_num))
theorem R72137 : Reach 72137 := rs (se 2 (by rfl) ⟨27051, by rfl⟩) (B 54103 (by norm_num) ⟨27051, by rfl⟩ (by norm_num))
theorem R104909 : Reach 104909 := rs (se 3 (by rfl) ⟨19670, by rfl⟩) (B 39341 (by norm_num) ⟨19670, by rfl⟩ (by norm_num))
theorem R104933 : Reach 104933 := rs (se 4 (by rfl) ⟨9837, by rfl⟩) (B 19675 (by norm_num) ⟨9837, by rfl⟩ (by norm_num))
theorem R104957 : Reach 104957 := rs (se 3 (by rfl) ⟨19679, by rfl⟩) (B 39359 (by norm_num) ⟨19679, by rfl⟩ (by norm_num))
theorem R104981 : Reach 104981 := rs (se 6 (by rfl) ⟨2460, by rfl⟩) (B 4921 (by norm_num) ⟨2460, by rfl⟩ (by norm_num))
theorem R170525 : Reach 170525 := rs (se 3 (by rfl) ⟨31973, by rfl⟩) (B 63947 (by norm_num) ⟨31973, by rfl⟩ (by norm_num))
theorem R105005 : Reach 105005 := rs (se 3 (by rfl) ⟨19688, by rfl⟩) (B 39377 (by norm_num) ⟨19688, by rfl⟩ (by norm_num))
theorem R105029 : Reach 105029 := rs (se 4 (by rfl) ⟨9846, by rfl⟩) (B 19693 (by norm_num) ⟨9846, by rfl⟩ (by norm_num))
theorem R105053 : Reach 105053 := rs (se 3 (by rfl) ⟨19697, by rfl⟩) (B 39395 (by norm_num) ⟨19697, by rfl⟩ (by norm_num))
theorem R105077 : Reach 105077 := rs (se 5 (by rfl) ⟨4925, by rfl⟩) (B 9851 (by norm_num) ⟨4925, by rfl⟩ (by norm_num))
theorem R105101 : Reach 105101 := rs (se 3 (by rfl) ⟨19706, by rfl⟩) (B 39413 (by norm_num) ⟨19706, by rfl⟩ (by norm_num))
theorem R105125 : Reach 105125 := rs (se 4 (by rfl) ⟨9855, by rfl⟩) (B 19711 (by norm_num) ⟨9855, by rfl⟩ (by norm_num))
theorem R105149 : Reach 105149 := rs (se 3 (by rfl) ⟨19715, by rfl⟩) (B 39431 (by norm_num) ⟨19715, by rfl⟩ (by norm_num))
theorem R105173 : Reach 105173 := rs (se 7 (by rfl) ⟨1232, by rfl⟩) (B 2465 (by norm_num) ⟨1232, by rfl⟩ (by norm_num))
theorem R400085 : Reach 400085 := rs (se 7 (by rfl) ⟨4688, by rfl⟩) (B 9377 (by norm_num) ⟨4688, by rfl⟩ (by norm_num))
theorem R105197 : Reach 105197 := rs (se 3 (by rfl) ⟨19724, by rfl⟩) (B 39449 (by norm_num) ⟨19724, by rfl⟩ (by norm_num))
theorem R105221 : Reach 105221 := rs (se 4 (by rfl) ⟨9864, by rfl⟩) (B 19729 (by norm_num) ⟨9864, by rfl⟩ (by norm_num))
theorem R105245 : Reach 105245 := rs (se 3 (by rfl) ⟨19733, by rfl⟩) (B 39467 (by norm_num) ⟨19733, by rfl⟩ (by norm_num))
theorem R105269 : Reach 105269 := rs (se 5 (by rfl) ⟨4934, by rfl⟩) (B 9869 (by norm_num) ⟨4934, by rfl⟩ (by norm_num))
theorem R236357 : Reach 236357 := rs (se 4 (by rfl) ⟨22158, by rfl⟩) (B 44317 (by norm_num) ⟨22158, by rfl⟩ (by norm_num))
theorem R105293 : Reach 105293 := rs (se 3 (by rfl) ⟨19742, by rfl⟩) (B 39485 (by norm_num) ⟨19742, by rfl⟩ (by norm_num))
theorem R170837 : Reach 170837 := rs (se 9 (by rfl) ⟨500, by rfl⟩) (B 1001 (by norm_num) ⟨500, by rfl⟩ (by norm_num))
theorem R105317 : Reach 105317 := rs (se 4 (by rfl) ⟨9873, by rfl⟩) (B 19747 (by norm_num) ⟨9873, by rfl⟩ (by norm_num))
theorem R170869 : Reach 170869 := rs (se 5 (by rfl) ⟨8009, by rfl⟩) (B 16019 (by norm_num) ⟨8009, by rfl⟩ (by norm_num))
theorem R105341 : Reach 105341 := rs (se 3 (by rfl) ⟨19751, by rfl⟩) (B 39503 (by norm_num) ⟨19751, by rfl⟩ (by norm_num))
theorem R72581 : Reach 72581 := rs (se 4 (by rfl) ⟨6804, by rfl⟩) (B 13609 (by norm_num) ⟨6804, by rfl⟩ (by norm_num))
theorem R105365 : Reach 105365 := rs (se 6 (by rfl) ⟨2469, by rfl⟩) (B 4939 (by norm_num) ⟨2469, by rfl⟩ (by norm_num))
theorem R105389 : Reach 105389 := rs (se 3 (by rfl) ⟨19760, by rfl⟩) (B 39521 (by norm_num) ⟨19760, by rfl⟩ (by norm_num))
theorem R105413 : Reach 105413 := rs (se 4 (by rfl) ⟨9882, by rfl⟩) (B 19765 (by norm_num) ⟨9882, by rfl⟩ (by norm_num))
theorem R105437 : Reach 105437 := rs (se 3 (by rfl) ⟨19769, by rfl⟩) (B 39539 (by norm_num) ⟨19769, by rfl⟩ (by norm_num))
theorem R170981 : Reach 170981 := rs (se 4 (by rfl) ⟨16029, by rfl⟩) (B 32059 (by norm_num) ⟨16029, by rfl⟩ (by norm_num))
theorem R105461 : Reach 105461 := rs (se 5 (by rfl) ⟨4943, by rfl⟩) (B 9887 (by norm_num) ⟨4943, by rfl⟩ (by norm_num))
theorem R105485 : Reach 105485 := rs (se 3 (by rfl) ⟨19778, by rfl⟩) (B 39557 (by norm_num) ⟨19778, by rfl⟩ (by norm_num))
theorem R105509 : Reach 105509 := rs (se 4 (by rfl) ⟨9891, by rfl⟩) (B 19783 (by norm_num) ⟨9891, by rfl⟩ (by norm_num))
theorem R269365 : Reach 269365 := rs (se 5 (by rfl) ⟨12626, by rfl⟩) (B 25253 (by norm_num) ⟨12626, by rfl⟩ (by norm_num))
theorem R105533 : Reach 105533 := rs (se 3 (by rfl) ⟨19787, by rfl⟩) (B 39575 (by norm_num) ⟨19787, by rfl⟩ (by norm_num))
theorem R236629 : Reach 236629 := rs (se 8 (by rfl) ⟨1386, by rfl⟩) (B 2773 (by norm_num) ⟨1386, by rfl⟩ (by norm_num))
theorem R105557 : Reach 105557 := rs (se 8 (by rfl) ⟨618, by rfl⟩) (B 1237 (by norm_num) ⟨618, by rfl⟩ (by norm_num))
theorem R105581 : Reach 105581 := rs (se 3 (by rfl) ⟨19796, by rfl⟩) (B 39593 (by norm_num) ⟨19796, by rfl⟩ (by norm_num))
theorem R72829 : Reach 72829 := rs (se 3 (by rfl) ⟨13655, by rfl⟩) (B 27311 (by norm_num) ⟨13655, by rfl⟩ (by norm_num))
theorem R105605 : Reach 105605 := rs (se 4 (by rfl) ⟨9900, by rfl⟩) (B 19801 (by norm_num) ⟨9900, by rfl⟩ (by norm_num))
theorem R105629 : Reach 105629 := rs (se 3 (by rfl) ⟨19805, by rfl⟩) (B 39611 (by norm_num) ⟨19805, by rfl⟩ (by norm_num))
theorem R171173 : Reach 171173 := rs (se 4 (by rfl) ⟨16047, by rfl⟩) (B 32095 (by norm_num) ⟨16047, by rfl⟩ (by norm_num))
theorem R105653 : Reach 105653 := rs (se 5 (by rfl) ⟨4952, by rfl⟩) (B 9905 (by norm_num) ⟨4952, by rfl⟩ (by norm_num))
theorem R105677 : Reach 105677 := rs (se 3 (by rfl) ⟨19814, by rfl⟩) (B 39629 (by norm_num) ⟨19814, by rfl⟩ (by norm_num))
theorem R105701 : Reach 105701 := rs (se 4 (by rfl) ⟨9909, by rfl⟩) (B 19819 (by norm_num) ⟨9909, by rfl⟩ (by norm_num))
theorem R236789 : Reach 236789 := rs (se 5 (by rfl) ⟨11099, by rfl⟩) (B 22199 (by norm_num) ⟨11099, by rfl⟩ (by norm_num))
theorem R105725 : Reach 105725 := rs (se 3 (by rfl) ⟨19823, by rfl⟩) (B 39647 (by norm_num) ⟨19823, by rfl⟩ (by norm_num))
theorem R105749 : Reach 105749 := rs (se 6 (by rfl) ⟨2478, by rfl⟩) (B 4957 (by norm_num) ⟨2478, by rfl⟩ (by norm_num))
theorem R105773 : Reach 105773 := rs (se 3 (by rfl) ⟨19832, by rfl⟩) (B 39665 (by norm_num) ⟨19832, by rfl⟩ (by norm_num))
theorem R105797 : Reach 105797 := rs (se 4 (by rfl) ⟨9918, by rfl⟩) (B 19837 (by norm_num) ⟨9918, by rfl⟩ (by norm_num))
theorem R105821 : Reach 105821 := rs (se 3 (by rfl) ⟨19841, by rfl⟩) (B 39683 (by norm_num) ⟨19841, by rfl⟩ (by norm_num))
theorem R269669 : Reach 269669 := rs (se 4 (by rfl) ⟨25281, by rfl⟩) (B 50563 (by norm_num) ⟨25281, by rfl⟩ (by norm_num))
theorem R105845 : Reach 105845 := rs (se 5 (by rfl) ⟨4961, by rfl⟩) (B 9923 (by norm_num) ⟨4961, by rfl⟩ (by norm_num))
theorem R105869 : Reach 105869 := rs (se 3 (by rfl) ⟨19850, by rfl⟩) (B 39701 (by norm_num) ⟨19850, by rfl⟩ (by norm_num))
theorem R105893 : Reach 105893 := rs (se 4 (by rfl) ⟨9927, by rfl⟩) (B 19855 (by norm_num) ⟨9927, by rfl⟩ (by norm_num))
theorem R105917 : Reach 105917 := rs (se 3 (by rfl) ⟨19859, by rfl⟩) (B 39719 (by norm_num) ⟨19859, by rfl⟩ (by norm_num))
theorem R105941 : Reach 105941 := rs (se 7 (by rfl) ⟨1241, by rfl⟩) (B 2483 (by norm_num) ⟨1241, by rfl⟩ (by norm_num))
theorem R105965 : Reach 105965 := rs (se 3 (by rfl) ⟨19868, by rfl⟩) (B 39737 (by norm_num) ⟨19868, by rfl⟩ (by norm_num))
theorem R171517 : Reach 171517 := rs (se 3 (by rfl) ⟨32159, by rfl⟩) (B 64319 (by norm_num) ⟨32159, by rfl⟩ (by norm_num))
theorem R105989 : Reach 105989 := rs (se 4 (by rfl) ⟨9936, by rfl⟩) (B 19873 (by norm_num) ⟨9936, by rfl⟩ (by norm_num))
theorem R138781 : Reach 138781 := rs (se 3 (by rfl) ⟨26021, by rfl⟩) (B 52043 (by norm_num) ⟨26021, by rfl⟩ (by norm_num))
theorem R106013 : Reach 106013 := rs (se 3 (by rfl) ⟨19877, by rfl⟩) (B 39755 (by norm_num) ⟨19877, by rfl⟩ (by norm_num))
theorem R73261 : Reach 73261 := rs (se 3 (by rfl) ⟨13736, by rfl⟩) (B 27473 (by norm_num) ⟨13736, by rfl⟩ (by norm_num))
theorem R106037 : Reach 106037 := rs (se 5 (by rfl) ⟨4970, by rfl⟩) (B 9941 (by norm_num) ⟨4970, by rfl⟩ (by norm_num))
theorem R106061 : Reach 106061 := rs (se 3 (by rfl) ⟨19886, by rfl⟩) (B 39773 (by norm_num) ⟨19886, by rfl⟩ (by norm_num))
theorem R106085 : Reach 106085 := rs (se 4 (by rfl) ⟨9945, by rfl⟩) (B 19891 (by norm_num) ⟨9945, by rfl⟩ (by norm_num))
theorem R171629 : Reach 171629 := rs (se 3 (by rfl) ⟨32180, by rfl⟩) (B 64361 (by norm_num) ⟨32180, by rfl⟩ (by norm_num))
theorem R73333 : Reach 73333 := rs (se 5 (by rfl) ⟨3437, by rfl⟩) (B 6875 (by norm_num) ⟨3437, by rfl⟩ (by norm_num))
theorem R106109 : Reach 106109 := rs (se 3 (by rfl) ⟨19895, by rfl⟩) (B 39791 (by norm_num) ⟨19895, by rfl⟩ (by norm_num))
theorem R106133 : Reach 106133 := rs (se 6 (by rfl) ⟨2487, by rfl⟩) (B 4975 (by norm_num) ⟨2487, by rfl⟩ (by norm_num))
theorem R237221 : Reach 237221 := rs (se 4 (by rfl) ⟨22239, by rfl⟩) (B 44479 (by norm_num) ⟨22239, by rfl⟩ (by norm_num))
theorem R106157 : Reach 106157 := rs (se 3 (by rfl) ⟨19904, by rfl⟩) (B 39809 (by norm_num) ⟨19904, by rfl⟩ (by norm_num))
theorem R106181 : Reach 106181 := rs (se 4 (by rfl) ⟨9954, by rfl⟩) (B 19909 (by norm_num) ⟨9954, by rfl⟩ (by norm_num))
theorem R106205 : Reach 106205 := rs (se 3 (by rfl) ⟨19913, by rfl⟩) (B 39827 (by norm_num) ⟨19913, by rfl⟩ (by norm_num))
theorem R106229 : Reach 106229 := rs (se 5 (by rfl) ⟨4979, by rfl⟩) (B 9959 (by norm_num) ⟨4979, by rfl⟩ (by norm_num))
theorem R106253 : Reach 106253 := rs (se 3 (by rfl) ⟨19922, by rfl⟩) (B 39845 (by norm_num) ⟨19922, by rfl⟩ (by norm_num))
theorem R106277 : Reach 106277 := rs (se 4 (by rfl) ⟨9963, by rfl⟩) (B 19927 (by norm_num) ⟨9963, by rfl⟩ (by norm_num))
theorem R302885 : Reach 302885 := rs (se 4 (by rfl) ⟨28395, by rfl⟩) (B 56791 (by norm_num) ⟨28395, by rfl⟩ (by norm_num))
theorem R171821 : Reach 171821 := rs (se 3 (by rfl) ⟨32216, by rfl⟩) (B 64433 (by norm_num) ⟨32216, by rfl⟩ (by norm_num))
theorem R106301 : Reach 106301 := rs (se 3 (by rfl) ⟨19931, by rfl⟩) (B 39863 (by norm_num) ⟨19931, by rfl⟩ (by norm_num))
theorem R106325 : Reach 106325 := rs (se 9 (by rfl) ⟨311, by rfl⟩) (B 623 (by norm_num) ⟨311, by rfl⟩ (by norm_num))
theorem R106349 : Reach 106349 := rs (se 3 (by rfl) ⟨19940, by rfl⟩) (B 39881 (by norm_num) ⟨19940, by rfl⟩ (by norm_num))
theorem R106373 : Reach 106373 := rs (se 4 (by rfl) ⟨9972, by rfl⟩) (B 19945 (by norm_num) ⟨9972, by rfl⟩ (by norm_num))
theorem R335765 : Reach 335765 := rs (se 6 (by rfl) ⟨7869, by rfl⟩) (B 15739 (by norm_num) ⟨7869, by rfl⟩ (by norm_num))
theorem R106397 : Reach 106397 := rs (se 3 (by rfl) ⟨19949, by rfl⟩) (B 39899 (by norm_num) ⟨19949, by rfl⟩ (by norm_num))
theorem R597941 : Reach 597941 := rs (se 5 (by rfl) ⟨28028, by rfl⟩) (B 56057 (by norm_num) ⟨28028, by rfl⟩ (by norm_num))
theorem R106421 : Reach 106421 := rs (se 5 (by rfl) ⟨4988, by rfl⟩) (B 9977 (by norm_num) ⟨4988, by rfl⟩ (by norm_num))
theorem R106445 : Reach 106445 := rs (se 3 (by rfl) ⟨19958, by rfl⟩) (B 39917 (by norm_num) ⟨19958, by rfl⟩ (by norm_num))
theorem R106469 : Reach 106469 := rs (se 4 (by rfl) ⟨9981, by rfl⟩) (B 19963 (by norm_num) ⟨9981, by rfl⟩ (by norm_num))
theorem R73705 : Reach 73705 := rs (se 2 (by rfl) ⟨27639, by rfl⟩) (B 55279 (by norm_num) ⟨27639, by rfl⟩ (by norm_num))
theorem R106493 : Reach 106493 := rs (se 3 (by rfl) ⟨19967, by rfl⟩) (B 39935 (by norm_num) ⟨19967, by rfl⟩ (by norm_num))
theorem R106517 : Reach 106517 := rs (se 6 (by rfl) ⟨2496, by rfl⟩) (B 4993 (by norm_num) ⟨2496, by rfl⟩ (by norm_num))
theorem R106541 : Reach 106541 := rs (se 3 (by rfl) ⟨19976, by rfl⟩) (B 39953 (by norm_num) ⟨19976, by rfl⟩ (by norm_num))
theorem R303173 : Reach 303173 := rs (se 4 (by rfl) ⟨28422, by rfl⟩) (B 56845 (by norm_num) ⟨28422, by rfl⟩ (by norm_num))
theorem R106565 : Reach 106565 := rs (se 4 (by rfl) ⟨9990, by rfl⟩) (B 19981 (by norm_num) ⟨9990, by rfl⟩ (by norm_num))
theorem R237653 : Reach 237653 := rs (se 8 (by rfl) ⟨1392, by rfl⟩) (B 2785 (by norm_num) ⟨1392, by rfl⟩ (by norm_num))
theorem R106589 : Reach 106589 := rs (se 3 (by rfl) ⟨19985, by rfl⟩) (B 39971 (by norm_num) ⟨19985, by rfl⟩ (by norm_num))
theorem R106613 : Reach 106613 := rs (se 5 (by rfl) ⟨4997, by rfl⟩) (B 9995 (by norm_num) ⟨4997, by rfl⟩ (by norm_num))
theorem R172165 : Reach 172165 := rs (se 4 (by rfl) ⟨16140, by rfl⟩) (B 32281 (by norm_num) ⟨16140, by rfl⟩ (by norm_num))
theorem R106637 : Reach 106637 := rs (se 3 (by rfl) ⟨19994, by rfl⟩) (B 39989 (by norm_num) ⟨19994, by rfl⟩ (by norm_num))
theorem R106661 : Reach 106661 := rs (se 4 (by rfl) ⟨9999, by rfl⟩) (B 19999 (by norm_num) ⟨9999, by rfl⟩ (by norm_num))
theorem R106685 : Reach 106685 := rs (se 3 (by rfl) ⟨20003, by rfl⟩) (B 40007 (by norm_num) ⟨20003, by rfl⟩ (by norm_num))
theorem R172277 : Reach 172277 := rs (se 5 (by rfl) ⟨8075, by rfl⟩) (B 16151 (by norm_num) ⟨8075, by rfl⟩ (by norm_num))
theorem R368981 : Reach 368981 := rs (se 10 (by rfl) ⟨540, by rfl⟩) (B 1081 (by norm_num) ⟨540, by rfl⟩ (by norm_num))
theorem R74081 : Reach 74081 := rs (se 2 (by rfl) ⟨27780, by rfl⟩) (B 55561 (by norm_num) ⟨27780, by rfl⟩ (by norm_num))
theorem R74153 : Reach 74153 := rs (se 2 (by rfl) ⟨27807, by rfl⟩) (B 55615 (by norm_num) ⟨27807, by rfl⟩ (by norm_num))
theorem R172469 : Reach 172469 := rs (se 5 (by rfl) ⟨8084, by rfl⟩) (B 16169 (by norm_num) ⟨8084, by rfl⟩ (by norm_num))
theorem R434645 : Reach 434645 := rs (se 7 (by rfl) ⟨5093, by rfl⟩) (B 10187 (by norm_num) ⟨5093, by rfl⟩ (by norm_num))
theorem R238085 : Reach 238085 := rs (se 4 (by rfl) ⟨22320, by rfl⟩) (B 44641 (by norm_num) ⟨22320, by rfl⟩ (by norm_num))
theorem R369173 : Reach 369173 := rs (se 6 (by rfl) ⟨8652, by rfl⟩) (B 17305 (by norm_num) ⟨8652, by rfl⟩ (by norm_num))
theorem R74341 : Reach 74341 := rs (se 4 (by rfl) ⟨6969, by rfl⟩) (B 13939 (by norm_num) ⟨6969, by rfl⟩ (by norm_num))
theorem R533141 : Reach 533141 := rs (se 6 (by rfl) ⟨12495, by rfl⟩) (B 24991 (by norm_num) ⟨12495, by rfl⟩ (by norm_num))
theorem R139997 : Reach 139997 := rs (se 3 (by rfl) ⟨26249, by rfl⟩) (B 52499 (by norm_num) ⟨26249, by rfl⟩ (by norm_num))
theorem R172813 : Reach 172813 := rs (se 3 (by rfl) ⟨32402, by rfl⟩) (B 64805 (by norm_num) ⟨32402, by rfl⟩ (by norm_num))
theorem R74525 : Reach 74525 := rs (se 3 (by rfl) ⟨13973, by rfl⟩) (B 27947 (by norm_num) ⟨13973, by rfl⟩ (by norm_num))
theorem R172925 : Reach 172925 := rs (se 3 (by rfl) ⟨32423, by rfl⟩) (B 64847 (by norm_num) ⟨32423, by rfl⟩ (by norm_num))
theorem R238517 : Reach 238517 := rs (se 5 (by rfl) ⟨11180, by rfl⟩) (B 22361 (by norm_num) ⟨11180, by rfl⟩ (by norm_num))
theorem R205861 : Reach 205861 := rs (se 4 (by rfl) ⟨19299, by rfl⟩) (B 38599 (by norm_num) ⟨19299, by rfl⟩ (by norm_num))
theorem R173117 : Reach 173117 := rs (se 3 (by rfl) ⟨32459, by rfl⟩) (B 64919 (by norm_num) ⟨32459, by rfl⟩ (by norm_num))
theorem R140549 : Reach 140549 := rs (se 4 (by rfl) ⟨13176, by rfl⟩) (B 26353 (by norm_num) ⟨13176, by rfl⟩ (by norm_num))
theorem R992533 : Reach 992533 := rs (se 6 (by rfl) ⟨23262, by rfl⟩) (B 46525 (by norm_num) ⟨23262, by rfl⟩ (by norm_num))
theorem R107821 : Reach 107821 := rs (se 3 (by rfl) ⟨20216, by rfl⟩) (B 40433 (by norm_num) ⟨20216, by rfl⟩ (by norm_num))
theorem R238949 : Reach 238949 := rs (se 4 (by rfl) ⟨22401, by rfl⟩) (B 44803 (by norm_num) ⟨22401, by rfl⟩ (by norm_num))
theorem R173461 : Reach 173461 := rs (se 6 (by rfl) ⟨4065, by rfl⟩) (B 8131 (by norm_num) ⟨4065, by rfl⟩ (by norm_num))
theorem R173573 : Reach 173573 := rs (se 4 (by rfl) ⟨16272, by rfl⟩) (B 32545 (by norm_num) ⟨16272, by rfl⟩ (by norm_num))
theorem R75277 : Reach 75277 := rs (se 3 (by rfl) ⟨14114, by rfl⟩) (B 28229 (by norm_num) ⟨14114, by rfl⟩ (by norm_num))
theorem R173645 : Reach 173645 := rs (se 3 (by rfl) ⟨32558, by rfl⟩) (B 65117 (by norm_num) ⟨32558, by rfl⟩ (by norm_num))
theorem R75349 : Reach 75349 := rs (se 8 (by rfl) ⟨441, by rfl⟩) (B 883 (by norm_num) ⟨441, by rfl⟩ (by norm_num))
theorem R173765 : Reach 173765 := rs (se 4 (by rfl) ⟨16290, by rfl⟩) (B 32581 (by norm_num) ⟨16290, by rfl⟩ (by norm_num))
theorem R108253 : Reach 108253 := rs (se 3 (by rfl) ⟨20297, by rfl⟩) (B 40595 (by norm_num) ⟨20297, by rfl⟩ (by norm_num))
theorem R75529 : Reach 75529 := rs (se 2 (by rfl) ⟨28323, by rfl⟩) (B 56647 (by norm_num) ⟨28323, by rfl⟩ (by norm_num))
theorem R75541 : Reach 75541 := rs (se 6 (by rfl) ⟨1770, by rfl⟩) (B 3541 (by norm_num) ⟨1770, by rfl⟩ (by norm_num))
theorem R239381 : Reach 239381 := rs (se 6 (by rfl) ⟨5610, by rfl⟩) (B 11221 (by norm_num) ⟨5610, by rfl⟩ (by norm_num))
theorem R75577 : Reach 75577 := rs (se 2 (by rfl) ⟨28341, by rfl⟩) (B 56683 (by norm_num) ⟨28341, by rfl⟩ (by norm_num))
theorem R108373 : Reach 108373 := rs (se 9 (by rfl) ⟨317, by rfl⟩) (B 635 (by norm_num) ⟨317, by rfl⟩ (by norm_num))
theorem R75613 : Reach 75613 := rs (se 3 (by rfl) ⟨14177, by rfl⟩) (B 28355 (by norm_num) ⟨14177, by rfl⟩ (by norm_num))
theorem R75649 : Reach 75649 := rs (se 2 (by rfl) ⟨28368, by rfl⟩) (B 56737 (by norm_num) ⟨28368, by rfl⟩ (by norm_num))
theorem R108445 : Reach 108445 := rs (se 3 (by rfl) ⟨20333, by rfl⟩) (B 40667 (by norm_num) ⟨20333, by rfl⟩ (by norm_num))
theorem R75685 : Reach 75685 := rs (se 4 (by rfl) ⟨7095, by rfl⟩) (B 14191 (by norm_num) ⟨7095, by rfl⟩ (by norm_num))
theorem R75721 : Reach 75721 := rs (se 2 (by rfl) ⟨28395, by rfl⟩) (B 56791 (by norm_num) ⟨28395, by rfl⟩ (by norm_num))
theorem R567253 : Reach 567253 := rs (se 7 (by rfl) ⟨6647, by rfl⟩) (B 13295 (by norm_num) ⟨6647, by rfl⟩ (by norm_num))
theorem R75757 : Reach 75757 := rs (se 3 (by rfl) ⟨14204, by rfl⟩) (B 28409 (by norm_num) ⟨14204, by rfl⟩ (by norm_num))
theorem R75793 : Reach 75793 := rs (se 2 (by rfl) ⟨28422, by rfl⟩) (B 56845 (by norm_num) ⟨28422, by rfl⟩ (by norm_num))
theorem R174109 : Reach 174109 := rs (se 3 (by rfl) ⟨32645, by rfl⟩) (B 65291 (by norm_num) ⟨32645, by rfl⟩ (by norm_num))
theorem R75829 : Reach 75829 := rs (se 5 (by rfl) ⟨3554, by rfl⟩) (B 7109 (by norm_num) ⟨3554, by rfl⟩ (by norm_num))
theorem R108629 : Reach 108629 := rs (se 8 (by rfl) ⟨636, by rfl⟩) (B 1273 (by norm_num) ⟨636, by rfl⟩ (by norm_num))
theorem R75865 : Reach 75865 := rs (se 2 (by rfl) ⟨28449, by rfl⟩) (B 56899 (by norm_num) ⟨28449, by rfl⟩ (by norm_num))
theorem R75901 : Reach 75901 := rs (se 3 (by rfl) ⟨14231, by rfl⟩) (B 28463 (by norm_num) ⟨14231, by rfl⟩ (by norm_num))
theorem R174221 : Reach 174221 := rs (se 3 (by rfl) ⟨32666, by rfl⟩) (B 65333 (by norm_num) ⟨32666, by rfl⟩ (by norm_num))
theorem R75937 : Reach 75937 := rs (se 2 (by rfl) ⟨28476, by rfl⟩) (B 56953 (by norm_num) ⟨28476, by rfl⟩ (by norm_num))
theorem R207029 : Reach 207029 := rs (se 5 (by rfl) ⟨9704, by rfl⟩) (B 19409 (by norm_num) ⟨9704, by rfl⟩ (by norm_num))
theorem R75973 : Reach 75973 := rs (se 4 (by rfl) ⟨7122, by rfl⟩) (B 14245 (by norm_num) ⟨7122, by rfl⟩ (by norm_num))
theorem R239813 : Reach 239813 := rs (se 4 (by rfl) ⟨22482, by rfl⟩) (B 44965 (by norm_num) ⟨22482, by rfl⟩ (by norm_num))
theorem R76009 : Reach 76009 := rs (se 2 (by rfl) ⟨28503, by rfl⟩) (B 57007 (by norm_num) ⟨28503, by rfl⟩ (by norm_num))
theorem R76045 : Reach 76045 := rs (se 3 (by rfl) ⟨14258, by rfl⟩) (B 28517 (by norm_num) ⟨14258, by rfl⟩ (by norm_num))
theorem R698645 : Reach 698645 := rs (se 6 (by rfl) ⟨16374, by rfl⟩) (B 32749 (by norm_num) ⟨16374, by rfl⟩ (by norm_num))
theorem R76081 : Reach 76081 := rs (se 2 (by rfl) ⟨28530, by rfl⟩) (B 57061 (by norm_num) ⟨28530, by rfl⟩ (by norm_num))
theorem R174413 : Reach 174413 := rs (se 3 (by rfl) ⟨32702, by rfl⟩) (B 65405 (by norm_num) ⟨32702, by rfl⟩ (by norm_num))
theorem R76117 : Reach 76117 := rs (se 10 (by rfl) ⟨111, by rfl⟩) (B 223 (by norm_num) ⟨111, by rfl⟩ (by norm_num))
theorem R141677 : Reach 141677 := rs (se 3 (by rfl) ⟨26564, by rfl⟩) (B 53129 (by norm_num) ⟨26564, by rfl⟩ (by norm_num))
theorem R76153 : Reach 76153 := rs (se 2 (by rfl) ⟨28557, by rfl⟩) (B 57115 (by norm_num) ⟨28557, by rfl⟩ (by norm_num))
theorem R76189 : Reach 76189 := rs (se 3 (by rfl) ⟨14285, by rfl⟩) (B 28571 (by norm_num) ⟨14285, by rfl⟩ (by norm_num))
theorem R108973 : Reach 108973 := rs (se 3 (by rfl) ⟨20432, by rfl⟩) (B 40865 (by norm_num) ⟨20432, by rfl⟩ (by norm_num))
theorem R76225 : Reach 76225 := rs (se 2 (by rfl) ⟨28584, by rfl⟩) (B 57169 (by norm_num) ⟨28584, by rfl⟩ (by norm_num))
theorem R76261 : Reach 76261 := rs (se 4 (by rfl) ⟨7149, by rfl⟩) (B 14299 (by norm_num) ⟨7149, by rfl⟩ (by norm_num))
theorem R76297 : Reach 76297 := rs (se 2 (by rfl) ⟨28611, by rfl⟩) (B 57223 (by norm_num) ⟨28611, by rfl⟩ (by norm_num))
theorem R76333 : Reach 76333 := rs (se 3 (by rfl) ⟨14312, by rfl⟩) (B 28625 (by norm_num) ⟨14312, by rfl⟩ (by norm_num))
theorem R76369 : Reach 76369 := rs (se 2 (by rfl) ⟨28638, by rfl⟩) (B 57277 (by norm_num) ⟨28638, by rfl⟩ (by norm_num))
theorem R76405 : Reach 76405 := rs (se 5 (by rfl) ⟨3581, by rfl⟩) (B 7163 (by norm_num) ⟨3581, by rfl⟩ (by norm_num))
theorem R76441 : Reach 76441 := rs (se 2 (by rfl) ⟨28665, by rfl⟩) (B 57331 (by norm_num) ⟨28665, by rfl⟩ (by norm_num))
theorem R174757 : Reach 174757 := rs (se 4 (by rfl) ⟨16383, by rfl⟩) (B 32767 (by norm_num) ⟨16383, by rfl⟩ (by norm_num))
theorem R76477 : Reach 76477 := rs (se 3 (by rfl) ⟨14339, by rfl⟩) (B 28679 (by norm_num) ⟨14339, by rfl⟩ (by norm_num))
theorem R731861 : Reach 731861 := rs (se 7 (by rfl) ⟨8576, by rfl⟩) (B 17153 (by norm_num) ⟨8576, by rfl⟩ (by norm_num))
theorem R76513 : Reach 76513 := rs (se 2 (by rfl) ⟨28692, by rfl⟩) (B 57385 (by norm_num) ⟨28692, by rfl⟩ (by norm_num))
theorem R76549 : Reach 76549 := rs (se 4 (by rfl) ⟨7176, by rfl⟩) (B 14353 (by norm_num) ⟨7176, by rfl⟩ (by norm_num))
theorem R174869 : Reach 174869 := rs (se 6 (by rfl) ⟨4098, by rfl⟩) (B 8197 (by norm_num) ⟨4098, by rfl⟩ (by norm_num))
theorem R109333 : Reach 109333 := rs (se 6 (by rfl) ⟨2562, by rfl⟩) (B 5125 (by norm_num) ⟨2562, by rfl⟩ (by norm_num))
theorem R76585 : Reach 76585 := rs (se 2 (by rfl) ⟨28719, by rfl⟩) (B 57439 (by norm_num) ⟨28719, by rfl⟩ (by norm_num))
theorem R76621 : Reach 76621 := rs (se 3 (by rfl) ⟨14366, by rfl⟩) (B 28733 (by norm_num) ⟨14366, by rfl⟩ (by norm_num))
theorem R797525 : Reach 797525 := rs (se 9 (by rfl) ⟨2336, by rfl⟩) (B 4673 (by norm_num) ⟨2336, by rfl⟩ (by norm_num))
theorem R76657 : Reach 76657 := rs (se 2 (by rfl) ⟨28746, by rfl⟩) (B 57493 (by norm_num) ⟨28746, by rfl⟩ (by norm_num))
theorem R76693 : Reach 76693 := rs (se 6 (by rfl) ⟨1797, by rfl⟩) (B 3595 (by norm_num) ⟨1797, by rfl⟩ (by norm_num))
theorem R76729 : Reach 76729 := rs (se 2 (by rfl) ⟨28773, by rfl⟩) (B 57547 (by norm_num) ⟨28773, by rfl⟩ (by norm_num))
theorem R273365 : Reach 273365 := rs (se 7 (by rfl) ⟨3203, by rfl⟩) (B 6407 (by norm_num) ⟨3203, by rfl⟩ (by norm_num))
theorem R175061 : Reach 175061 := rs (se 7 (by rfl) ⟨2051, by rfl⟩) (B 4103 (by norm_num) ⟨2051, by rfl⟩ (by norm_num))
theorem R76765 : Reach 76765 := rs (se 3 (by rfl) ⟨14393, by rfl⟩) (B 28787 (by norm_num) ⟨14393, by rfl⟩ (by norm_num))
theorem R338917 : Reach 338917 := rs (se 4 (by rfl) ⟨31773, by rfl⟩) (B 63547 (by norm_num) ⟨31773, by rfl⟩ (by norm_num))
theorem R76801 : Reach 76801 := rs (se 2 (by rfl) ⟨28800, by rfl⟩) (B 57601 (by norm_num) ⟨28800, by rfl⟩ (by norm_num))
theorem R76837 : Reach 76837 := rs (se 4 (by rfl) ⟨7203, by rfl⟩) (B 14407 (by norm_num) ⟨7203, by rfl⟩ (by norm_num))
theorem R76873 : Reach 76873 := rs (se 2 (by rfl) ⟨28827, by rfl⟩) (B 57655 (by norm_num) ⟨28827, by rfl⟩ (by norm_num))
theorem R76909 : Reach 76909 := rs (se 3 (by rfl) ⟨14420, by rfl⟩) (B 28841 (by norm_num) ⟨14420, by rfl⟩ (by norm_num))
theorem R76945 : Reach 76945 := rs (se 2 (by rfl) ⟨28854, by rfl⟩) (B 57709 (by norm_num) ⟨28854, by rfl⟩ (by norm_num))
theorem R76961 : Reach 76961 := rs (se 2 (by rfl) ⟨28860, by rfl⟩) (B 57721 (by norm_num) ⟨28860, by rfl⟩ (by norm_num))
theorem R76981 : Reach 76981 := rs (se 5 (by rfl) ⟨3608, by rfl⟩) (B 7217 (by norm_num) ⟨3608, by rfl⟩ (by norm_num))
theorem R109757 : Reach 109757 := rs (se 3 (by rfl) ⟨20579, by rfl⟩) (B 41159 (by norm_num) ⟨20579, by rfl⟩ (by norm_num))
theorem R77017 : Reach 77017 := rs (se 2 (by rfl) ⟨28881, by rfl⟩) (B 57763 (by norm_num) ⟨28881, by rfl⟩ (by norm_num))
theorem R77053 : Reach 77053 := rs (se 3 (by rfl) ⟨14447, by rfl⟩) (B 28895 (by norm_num) ⟨14447, by rfl⟩ (by norm_num))
theorem R77089 : Reach 77089 := rs (se 2 (by rfl) ⟨28908, by rfl⟩) (B 57817 (by norm_num) ⟨28908, by rfl⟩ (by norm_num))
theorem R175405 : Reach 175405 := rs (se 3 (by rfl) ⟨32888, by rfl⟩) (B 65777 (by norm_num) ⟨32888, by rfl⟩ (by norm_num))
theorem R77125 : Reach 77125 := rs (se 4 (by rfl) ⟨7230, by rfl⟩) (B 14461 (by norm_num) ⟨7230, by rfl⟩ (by norm_num))
theorem R77161 : Reach 77161 := rs (se 2 (by rfl) ⟨28935, by rfl⟩) (B 57871 (by norm_num) ⟨28935, by rfl⟩ (by norm_num))
theorem R77197 : Reach 77197 := rs (se 3 (by rfl) ⟨14474, by rfl⟩) (B 28949 (by norm_num) ⟨14474, by rfl⟩ (by norm_num))
theorem R175517 : Reach 175517 := rs (se 3 (by rfl) ⟨32909, by rfl⟩) (B 65819 (by norm_num) ⟨32909, by rfl⟩ (by norm_num))
theorem R77233 : Reach 77233 := rs (se 2 (by rfl) ⟨28962, by rfl⟩) (B 57925 (by norm_num) ⟨28962, by rfl⟩ (by norm_num))
theorem R77269 : Reach 77269 := rs (se 7 (by rfl) ⟨905, by rfl⟩) (B 1811 (by norm_num) ⟨905, by rfl⟩ (by norm_num))
theorem R110045 : Reach 110045 := rs (se 3 (by rfl) ⟨20633, by rfl⟩) (B 41267 (by norm_num) ⟨20633, by rfl⟩ (by norm_num))
theorem R77305 : Reach 77305 := rs (se 2 (by rfl) ⟨28989, by rfl⟩) (B 57979 (by norm_num) ⟨28989, by rfl⟩ (by norm_num))
theorem R77341 : Reach 77341 := rs (se 3 (by rfl) ⟨14501, by rfl⟩) (B 29003 (by norm_num) ⟨14501, by rfl⟩ (by norm_num))
theorem R77377 : Reach 77377 := rs (se 2 (by rfl) ⟨29016, by rfl⟩) (B 58033 (by norm_num) ⟨29016, by rfl⟩ (by norm_num))
theorem R437845 : Reach 437845 := rs (se 8 (by rfl) ⟨2565, by rfl⟩) (B 5131 (by norm_num) ⟨2565, by rfl⟩ (by norm_num))
theorem R142933 : Reach 142933 := rs (se 8 (by rfl) ⟨837, by rfl⟩) (B 1675 (by norm_num) ⟨837, by rfl⟩ (by norm_num))
theorem R175709 : Reach 175709 := rs (se 3 (by rfl) ⟨32945, by rfl⟩) (B 65891 (by norm_num) ⟨32945, by rfl⟩ (by norm_num))
theorem R77413 : Reach 77413 := rs (se 4 (by rfl) ⟨7257, by rfl⟩) (B 14515 (by norm_num) ⟨7257, by rfl⟩ (by norm_num))
theorem R77449 : Reach 77449 := rs (se 2 (by rfl) ⟨29043, by rfl⟩) (B 58087 (by norm_num) ⟨29043, by rfl⟩ (by norm_num))
theorem R77485 : Reach 77485 := rs (se 3 (by rfl) ⟨14528, by rfl⟩) (B 29057 (by norm_num) ⟨14528, by rfl⟩ (by norm_num))
theorem R110269 : Reach 110269 := rs (se 3 (by rfl) ⟨20675, by rfl⟩) (B 41351 (by norm_num) ⟨20675, by rfl⟩ (by norm_num))
theorem R77521 : Reach 77521 := rs (se 2 (by rfl) ⟨29070, by rfl⟩) (B 58141 (by norm_num) ⟨29070, by rfl⟩ (by norm_num))
theorem R77545 : Reach 77545 := rs (se 2 (by rfl) ⟨29079, by rfl⟩) (B 58159 (by norm_num) ⟨29079, by rfl⟩ (by norm_num))
theorem R77557 : Reach 77557 := rs (se 5 (by rfl) ⟨3635, by rfl⟩) (B 7271 (by norm_num) ⟨3635, by rfl⟩ (by norm_num))
theorem R306965 : Reach 306965 := rs (se 6 (by rfl) ⟨7194, by rfl⟩) (B 14389 (by norm_num) ⟨7194, by rfl⟩ (by norm_num))
theorem R77593 : Reach 77593 := rs (se 2 (by rfl) ⟨29097, by rfl⟩) (B 58195 (by norm_num) ⟨29097, by rfl⟩ (by norm_num))
theorem R77629 : Reach 77629 := rs (se 3 (by rfl) ⟨14555, by rfl⟩) (B 29111 (by norm_num) ⟨14555, by rfl⟩ (by norm_num))
theorem R77665 : Reach 77665 := rs (se 2 (by rfl) ⟨29124, by rfl⟩) (B 58249 (by norm_num) ⟨29124, by rfl⟩ (by norm_num))
theorem R77701 : Reach 77701 := rs (se 4 (by rfl) ⟨7284, by rfl⟩) (B 14569 (by norm_num) ⟨7284, by rfl⟩ (by norm_num))
theorem R77737 : Reach 77737 := rs (se 2 (by rfl) ⟨29151, by rfl⟩) (B 58303 (by norm_num) ⟨29151, by rfl⟩ (by norm_num))
theorem R176053 : Reach 176053 := rs (se 5 (by rfl) ⟨8252, by rfl⟩) (B 16505 (by norm_num) ⟨8252, by rfl⟩ (by norm_num))
theorem R77773 : Reach 77773 := rs (se 3 (by rfl) ⟨14582, by rfl⟩) (B 29165 (by norm_num) ⟨14582, by rfl⟩ (by norm_num))
theorem R77809 : Reach 77809 := rs (se 2 (by rfl) ⟨29178, by rfl⟩) (B 58357 (by norm_num) ⟨29178, by rfl⟩ (by norm_num))
theorem R77845 : Reach 77845 := rs (se 6 (by rfl) ⟨1824, by rfl⟩) (B 3649 (by norm_num) ⟨1824, by rfl⟩ (by norm_num))
theorem R176165 : Reach 176165 := rs (se 4 (by rfl) ⟨16515, by rfl⟩) (B 33031 (by norm_num) ⟨16515, by rfl⟩ (by norm_num))
theorem R77881 : Reach 77881 := rs (se 2 (by rfl) ⟨29205, by rfl⟩) (B 58411 (by norm_num) ⟨29205, by rfl⟩ (by norm_num))
theorem R340037 : Reach 340037 := rs (se 4 (by rfl) ⟨31878, by rfl⟩) (B 63757 (by norm_num) ⟨31878, by rfl⟩ (by norm_num))
theorem R77917 : Reach 77917 := rs (se 3 (by rfl) ⟨14609, by rfl⟩) (B 29219 (by norm_num) ⟨14609, by rfl⟩ (by norm_num))
theorem R77953 : Reach 77953 := rs (se 2 (by rfl) ⟨29232, by rfl⟩) (B 58465 (by norm_num) ⟨29232, by rfl⟩ (by norm_num))
theorem R77989 : Reach 77989 := rs (se 4 (by rfl) ⟨7311, by rfl⟩) (B 14623 (by norm_num) ⟨7311, by rfl⟩ (by norm_num))
theorem R78025 : Reach 78025 := rs (se 2 (by rfl) ⟨29259, by rfl⟩) (B 58519 (by norm_num) ⟨29259, by rfl⟩ (by norm_num))
theorem R176357 : Reach 176357 := rs (se 4 (by rfl) ⟨16533, by rfl⟩) (B 33067 (by norm_num) ⟨16533, by rfl⟩ (by norm_num))
theorem R78061 : Reach 78061 := rs (se 3 (by rfl) ⟨14636, by rfl⟩) (B 29273 (by norm_num) ⟨14636, by rfl⟩ (by norm_num))
theorem R78097 : Reach 78097 := rs (se 2 (by rfl) ⟨29286, by rfl⟩) (B 58573 (by norm_num) ⟨29286, by rfl⟩ (by norm_num))
theorem R78133 : Reach 78133 := rs (se 5 (by rfl) ⟨3662, by rfl⟩) (B 7325 (by norm_num) ⟨3662, by rfl⟩ (by norm_num))
theorem R78169 : Reach 78169 := rs (se 2 (by rfl) ⟨29313, by rfl⟩) (B 58627 (by norm_num) ⟨29313, by rfl⟩ (by norm_num))
theorem R78205 : Reach 78205 := rs (se 3 (by rfl) ⟨14663, by rfl⟩) (B 29327 (by norm_num) ⟨14663, by rfl⟩ (by norm_num))
theorem R78241 : Reach 78241 := rs (se 2 (by rfl) ⟨29340, by rfl⟩) (B 58681 (by norm_num) ⟨29340, by rfl⟩ (by norm_num))
theorem R78277 : Reach 78277 := rs (se 4 (by rfl) ⟨7338, by rfl⟩) (B 14677 (by norm_num) ⟨7338, by rfl⟩ (by norm_num))
theorem R78313 : Reach 78313 := rs (se 2 (by rfl) ⟨29367, by rfl⟩) (B 58735 (by norm_num) ⟨29367, by rfl⟩ (by norm_num))
theorem R78349 : Reach 78349 := rs (se 3 (by rfl) ⟨14690, by rfl⟩) (B 29381 (by norm_num) ⟨14690, by rfl⟩ (by norm_num))
theorem R78385 : Reach 78385 := rs (se 2 (by rfl) ⟨29394, by rfl⟩) (B 58789 (by norm_num) ⟨29394, by rfl⟩ (by norm_num))
theorem R176701 : Reach 176701 := rs (se 3 (by rfl) ⟨33131, by rfl⟩) (B 66263 (by norm_num) ⟨33131, by rfl⟩ (by norm_num))
theorem R78421 : Reach 78421 := rs (se 8 (by rfl) ⟨459, by rfl⟩) (B 919 (by norm_num) ⟨459, by rfl⟩ (by norm_num))
theorem R78457 : Reach 78457 := rs (se 2 (by rfl) ⟨29421, by rfl⟩) (B 58843 (by norm_num) ⟨29421, by rfl⟩ (by norm_num))
theorem R242309 : Reach 242309 := rs (se 4 (by rfl) ⟨22716, by rfl⟩) (B 45433 (by norm_num) ⟨22716, by rfl⟩ (by norm_num))
theorem R78493 : Reach 78493 := rs (se 3 (by rfl) ⟨14717, by rfl⟩) (B 29435 (by norm_num) ⟨14717, by rfl⟩ (by norm_num))
theorem R176813 : Reach 176813 := rs (se 3 (by rfl) ⟨33152, by rfl⟩) (B 66305 (by norm_num) ⟨33152, by rfl⟩ (by norm_num))
theorem R78529 : Reach 78529 := rs (se 2 (by rfl) ⟨29448, by rfl⟩) (B 58897 (by norm_num) ⟨29448, by rfl⟩ (by norm_num))
theorem R78565 : Reach 78565 := rs (se 4 (by rfl) ⟨7365, by rfl⟩) (B 14731 (by norm_num) ⟨7365, by rfl⟩ (by norm_num))
theorem R78601 : Reach 78601 := rs (se 2 (by rfl) ⟨29475, by rfl⟩) (B 58951 (by norm_num) ⟨29475, by rfl⟩ (by norm_num))
theorem R111397 : Reach 111397 := rs (se 4 (by rfl) ⟨10443, by rfl⟩) (B 20887 (by norm_num) ⟨10443, by rfl⟩ (by norm_num))
theorem R78637 : Reach 78637 := rs (se 3 (by rfl) ⟨14744, by rfl⟩) (B 29489 (by norm_num) ⟨14744, by rfl⟩ (by norm_num))
theorem R78673 : Reach 78673 := rs (se 2 (by rfl) ⟨29502, by rfl⟩) (B 59005 (by norm_num) ⟨29502, by rfl⟩ (by norm_num))
theorem R177005 : Reach 177005 := rs (se 3 (by rfl) ⟨33188, by rfl⟩) (B 66377 (by norm_num) ⟨33188, by rfl⟩ (by norm_num))
theorem R78709 : Reach 78709 := rs (se 5 (by rfl) ⟨3689, by rfl⟩) (B 7379 (by norm_num) ⟨3689, by rfl⟩ (by norm_num))
theorem R78745 : Reach 78745 := rs (se 2 (by rfl) ⟨29529, by rfl⟩) (B 59059 (by norm_num) ⟨29529, by rfl⟩ (by norm_num))
theorem R78781 : Reach 78781 := rs (se 3 (by rfl) ⟨14771, by rfl⟩) (B 29543 (by norm_num) ⟨14771, by rfl⟩ (by norm_num))
theorem R78817 : Reach 78817 := rs (se 2 (by rfl) ⟨29556, by rfl⟩) (B 59113 (by norm_num) ⟨29556, by rfl⟩ (by norm_num))
theorem R78853 : Reach 78853 := rs (se 4 (by rfl) ⟨7392, by rfl⟩) (B 14785 (by norm_num) ⟨7392, by rfl⟩ (by norm_num))
theorem R78889 : Reach 78889 := rs (se 2 (by rfl) ⟨29583, by rfl⟩) (B 59167 (by norm_num) ⟨29583, by rfl⟩ (by norm_num))
theorem R144445 : Reach 144445 := rs (se 3 (by rfl) ⟨27083, by rfl⟩) (B 54167 (by norm_num) ⟨27083, by rfl⟩ (by norm_num))
theorem R78925 : Reach 78925 := rs (se 3 (by rfl) ⟨14798, by rfl⟩) (B 29597 (by norm_num) ⟨14798, by rfl⟩ (by norm_num))
theorem R504917 : Reach 504917 := rs (se 8 (by rfl) ⟨2958, by rfl⟩) (B 5917 (by norm_num) ⟨2958, by rfl⟩ (by norm_num))
theorem R78961 : Reach 78961 := rs (se 2 (by rfl) ⟨29610, by rfl⟩) (B 59221 (by norm_num) ⟨29610, by rfl⟩ (by norm_num))
theorem R78997 : Reach 78997 := rs (se 6 (by rfl) ⟨1851, by rfl⟩) (B 3703 (by norm_num) ⟨1851, by rfl⟩ (by norm_num))
theorem R79033 : Reach 79033 := rs (se 2 (by rfl) ⟨29637, by rfl⟩) (B 59275 (by norm_num) ⟨29637, by rfl⟩ (by norm_num))
theorem R177349 : Reach 177349 := rs (se 4 (by rfl) ⟨16626, by rfl⟩) (B 33253 (by norm_num) ⟨16626, by rfl⟩ (by norm_num))
theorem R79069 : Reach 79069 := rs (se 3 (by rfl) ⟨14825, by rfl⟩) (B 29651 (by norm_num) ⟨14825, by rfl⟩ (by norm_num))
theorem R111845 : Reach 111845 := rs (se 4 (by rfl) ⟨10485, by rfl⟩) (B 20971 (by norm_num) ⟨10485, by rfl⟩ (by norm_num))
theorem R79105 : Reach 79105 := rs (se 2 (by rfl) ⟨29664, by rfl⟩) (B 59329 (by norm_num) ⟨29664, by rfl⟩ (by norm_num))
theorem R79141 : Reach 79141 := rs (se 4 (by rfl) ⟨7419, by rfl⟩) (B 14839 (by norm_num) ⟨7419, by rfl⟩ (by norm_num))
theorem R177461 : Reach 177461 := rs (se 5 (by rfl) ⟨8318, by rfl⟩) (B 16637 (by norm_num) ⟨8318, by rfl⟩ (by norm_num))
theorem R79177 : Reach 79177 := rs (se 2 (by rfl) ⟨29691, by rfl⟩) (B 59383 (by norm_num) ⟨29691, by rfl⟩ (by norm_num))
theorem R341333 : Reach 341333 := rs (se 13 (by rfl) ⟨62, by rfl⟩) (B 125 (by norm_num) ⟨62, by rfl⟩ (by norm_num))
theorem R79213 : Reach 79213 := rs (se 3 (by rfl) ⟨14852, by rfl⟩) (B 29705 (by norm_num) ⟨14852, by rfl⟩ (by norm_num))
theorem R79249 : Reach 79249 := rs (se 2 (by rfl) ⟨29718, by rfl⟩) (B 59437 (by norm_num) ⟨29718, by rfl⟩ (by norm_num))
theorem R144821 : Reach 144821 := rs (se 5 (by rfl) ⟨6788, by rfl⟩) (B 13577 (by norm_num) ⟨6788, by rfl⟩ (by norm_num))
theorem R79285 : Reach 79285 := rs (se 5 (by rfl) ⟨3716, by rfl⟩) (B 7433 (by norm_num) ⟨3716, by rfl⟩ (by norm_num))
theorem R79321 : Reach 79321 := rs (se 2 (by rfl) ⟨29745, by rfl⟩) (B 59491 (by norm_num) ⟨29745, by rfl⟩ (by norm_num))
theorem R177653 : Reach 177653 := rs (se 5 (by rfl) ⟨8327, by rfl⟩) (B 16655 (by norm_num) ⟨8327, by rfl⟩ (by norm_num))
theorem R79357 : Reach 79357 := rs (se 3 (by rfl) ⟨14879, by rfl⟩) (B 29759 (by norm_num) ⟨14879, by rfl⟩ (by norm_num))
theorem R177677 : Reach 177677 := rs (se 3 (by rfl) ⟨33314, by rfl⟩) (B 66629 (by norm_num) ⟨33314, by rfl⟩ (by norm_num))
theorem R79393 : Reach 79393 := rs (se 2 (by rfl) ⟨29772, by rfl⟩) (B 59545 (by norm_num) ⟨29772, by rfl⟩ (by norm_num))
theorem R79429 : Reach 79429 := rs (se 4 (by rfl) ⟨7446, by rfl⟩) (B 14893 (by norm_num) ⟨7446, by rfl⟩ (by norm_num))
theorem R79465 : Reach 79465 := rs (se 2 (by rfl) ⟨29799, by rfl⟩) (B 59599 (by norm_num) ⟨29799, by rfl⟩ (by norm_num))
theorem R79501 : Reach 79501 := rs (se 3 (by rfl) ⟨14906, by rfl⟩) (B 29813 (by norm_num) ⟨14906, by rfl⟩ (by norm_num))
theorem R79537 : Reach 79537 := rs (se 2 (by rfl) ⟨29826, by rfl⟩) (B 59653 (by norm_num) ⟨29826, by rfl⟩ (by norm_num))
theorem R308933 : Reach 308933 := rs (se 4 (by rfl) ⟨28962, by rfl⟩) (B 57925 (by norm_num) ⟨28962, by rfl⟩ (by norm_num))
theorem R79573 : Reach 79573 := rs (se 7 (by rfl) ⟨932, by rfl⟩) (B 1865 (by norm_num) ⟨932, by rfl⟩ (by norm_num))
theorem R79609 : Reach 79609 := rs (se 2 (by rfl) ⟨29853, by rfl⟩) (B 59707 (by norm_num) ⟨29853, by rfl⟩ (by norm_num))
theorem R341765 : Reach 341765 := rs (se 4 (by rfl) ⟨32040, by rfl⟩) (B 64081 (by norm_num) ⟨32040, by rfl⟩ (by norm_num))
theorem R79645 : Reach 79645 := rs (se 3 (by rfl) ⟨14933, by rfl⟩) (B 29867 (by norm_num) ⟨14933, by rfl⟩ (by norm_num))
theorem R177965 : Reach 177965 := rs (se 3 (by rfl) ⟨33368, by rfl⟩) (B 66737 (by norm_num) ⟨33368, by rfl⟩ (by norm_num))
theorem R79681 : Reach 79681 := rs (se 2 (by rfl) ⟨29880, by rfl⟩) (B 59761 (by norm_num) ⟨29880, by rfl⟩ (by norm_num))
theorem R177997 : Reach 177997 := rs (se 3 (by rfl) ⟨33374, by rfl⟩) (B 66749 (by norm_num) ⟨33374, by rfl⟩ (by norm_num))
theorem R79717 : Reach 79717 := rs (se 4 (by rfl) ⟨7473, by rfl⟩) (B 14947 (by norm_num) ⟨7473, by rfl⟩ (by norm_num))
theorem R79753 : Reach 79753 := rs (se 2 (by rfl) ⟨29907, by rfl⟩) (B 59815 (by norm_num) ⟨29907, by rfl⟩ (by norm_num))
theorem R79789 : Reach 79789 := rs (se 3 (by rfl) ⟨14960, by rfl⟩) (B 29921 (by norm_num) ⟨14960, by rfl⟩ (by norm_num))
theorem R178109 : Reach 178109 := rs (se 3 (by rfl) ⟨33395, by rfl⟩) (B 66791 (by norm_num) ⟨33395, by rfl⟩ (by norm_num))
theorem R79825 : Reach 79825 := rs (se 2 (by rfl) ⟨29934, by rfl⟩) (B 59869 (by norm_num) ⟨29934, by rfl⟩ (by norm_num))
theorem R79861 : Reach 79861 := rs (se 5 (by rfl) ⟨3743, by rfl⟩) (B 7487 (by norm_num) ⟨3743, by rfl⟩ (by norm_num))
theorem R79897 : Reach 79897 := rs (se 2 (by rfl) ⟨29961, by rfl⟩) (B 59923 (by norm_num) ⟨29961, by rfl⟩ (by norm_num))
theorem R276517 : Reach 276517 := rs (se 4 (by rfl) ⟨25923, by rfl⟩) (B 51847 (by norm_num) ⟨25923, by rfl⟩ (by norm_num))
theorem R79933 : Reach 79933 := rs (se 3 (by rfl) ⟨14987, by rfl⟩) (B 29975 (by norm_num) ⟨14987, by rfl⟩ (by norm_num))
theorem R79969 : Reach 79969 := rs (se 2 (by rfl) ⟨29988, by rfl⟩) (B 59977 (by norm_num) ⟨29988, by rfl⟩ (by norm_num))
theorem R178301 : Reach 178301 := rs (se 3 (by rfl) ⟨33431, by rfl⟩) (B 66863 (by norm_num) ⟨33431, by rfl⟩ (by norm_num))
theorem R80005 : Reach 80005 := rs (se 4 (by rfl) ⟨7500, by rfl⟩) (B 15001 (by norm_num) ⟨7500, by rfl⟩ (by norm_num))
theorem R669941 : Reach 669941 := rs (se 5 (by rfl) ⟨31403, by rfl⟩) (B 62807 (by norm_num) ⟨31403, by rfl⟩ (by norm_num))
theorem R211285 : Reach 211285 := rs (se 10 (by rfl) ⟨309, by rfl⟩) (B 619 (by norm_num) ⟨309, by rfl⟩ (by norm_num))
theorem R178645 : Reach 178645 := rs (se 7 (by rfl) ⟨2093, by rfl⟩) (B 4187 (by norm_num) ⟨2093, by rfl⟩ (by norm_num))
theorem R178757 : Reach 178757 := rs (se 4 (by rfl) ⟨16758, by rfl⟩) (B 33517 (by norm_num) ⟨16758, by rfl⟩ (by norm_num))
theorem R342629 : Reach 342629 := rs (se 4 (by rfl) ⟨32121, by rfl⟩) (B 64243 (by norm_num) ⟨32121, by rfl⟩ (by norm_num))
theorem R113285 : Reach 113285 := rs (se 4 (by rfl) ⟨10620, by rfl⟩) (B 21241 (by norm_num) ⟨10620, by rfl⟩ (by norm_num))
theorem R113333 : Reach 113333 := rs (se 5 (by rfl) ⟨5312, by rfl⟩) (B 10625 (by norm_num) ⟨5312, by rfl⟩ (by norm_num))
theorem R113357 : Reach 113357 := rs (se 3 (by rfl) ⟨21254, by rfl⟩) (B 42509 (by norm_num) ⟨21254, by rfl⟩ (by norm_num))
theorem R113413 : Reach 113413 := rs (se 4 (by rfl) ⟨10632, by rfl⟩) (B 21265 (by norm_num) ⟨10632, by rfl⟩ (by norm_num))
theorem R178949 : Reach 178949 := rs (se 4 (by rfl) ⟨16776, by rfl⟩) (B 33553 (by norm_num) ⟨16776, by rfl⟩ (by norm_num))
theorem R80689 : Reach 80689 := rs (se 2 (by rfl) ⟨30258, by rfl⟩) (B 60517 (by norm_num) ⟨30258, by rfl⟩ (by norm_num))
theorem R113485 : Reach 113485 := rs (se 3 (by rfl) ⟨21278, by rfl⟩) (B 42557 (by norm_num) ⟨21278, by rfl⟩ (by norm_num))
theorem R113501 : Reach 113501 := rs (se 3 (by rfl) ⟨21281, by rfl⟩) (B 42563 (by norm_num) ⟨21281, by rfl⟩ (by norm_num))
theorem R113629 : Reach 113629 := rs (se 3 (by rfl) ⟨21305, by rfl⟩) (B 42611 (by norm_num) ⟨21305, by rfl⟩ (by norm_num))
theorem R146461 : Reach 146461 := rs (se 3 (by rfl) ⟨27461, by rfl⟩) (B 54923 (by norm_num) ⟨27461, by rfl⟩ (by norm_num))
theorem R113717 : Reach 113717 := rs (se 5 (by rfl) ⟨5330, by rfl⟩) (B 10661 (by norm_num) ⟨5330, by rfl⟩ (by norm_num))
theorem R113845 : Reach 113845 := rs (se 5 (by rfl) ⟨5336, by rfl⟩) (B 10673 (by norm_num) ⟨5336, by rfl⟩ (by norm_num))
theorem R113933 : Reach 113933 := rs (se 3 (by rfl) ⟨21362, by rfl⟩) (B 42725 (by norm_num) ⟨21362, by rfl⟩ (by norm_num))
theorem R310613 : Reach 310613 := rs (se 11 (by rfl) ⟨227, by rfl⟩) (B 455 (by norm_num) ⟨227, by rfl⟩ (by norm_num))
theorem R114061 : Reach 114061 := rs (se 3 (by rfl) ⟨21386, by rfl⟩) (B 42773 (by norm_num) ⟨21386, by rfl⟩ (by norm_num))
theorem R114149 : Reach 114149 := rs (se 4 (by rfl) ⟨10701, by rfl⟩) (B 21403 (by norm_num) ⟨10701, by rfl⟩ (by norm_num))
theorem R114277 : Reach 114277 := rs (se 4 (by rfl) ⟨10713, by rfl⟩) (B 21427 (by norm_num) ⟨10713, by rfl⟩ (by norm_num))
theorem R179813 : Reach 179813 := rs (se 4 (by rfl) ⟨16857, by rfl⟩) (B 33715 (by norm_num) ⟨16857, by rfl⟩ (by norm_num))
theorem R245413 : Reach 245413 := rs (se 4 (by rfl) ⟨23007, by rfl⟩) (B 46015 (by norm_num) ⟨23007, by rfl⟩ (by norm_num))
theorem R81577 : Reach 81577 := rs (se 2 (by rfl) ⟨30591, by rfl⟩) (B 61183 (by norm_num) ⟨30591, by rfl⟩ (by norm_num))
theorem R114365 : Reach 114365 := rs (se 3 (by rfl) ⟨21443, by rfl⟩) (B 42887 (by norm_num) ⟨21443, by rfl⟩ (by norm_num))
theorem R179941 : Reach 179941 := rs (se 4 (by rfl) ⟨16869, by rfl⟩) (B 33739 (by norm_num) ⟨16869, by rfl⟩ (by norm_num))
theorem R114493 : Reach 114493 := rs (se 3 (by rfl) ⟨21467, by rfl⟩) (B 42935 (by norm_num) ⟨21467, by rfl⟩ (by norm_num))
theorem R343925 : Reach 343925 := rs (se 5 (by rfl) ⟨16121, by rfl⟩) (B 32243 (by norm_num) ⟨16121, by rfl⟩ (by norm_num))
theorem R114581 : Reach 114581 := rs (se 6 (by rfl) ⟨2685, by rfl⟩) (B 5371 (by norm_num) ⟨2685, by rfl⟩ (by norm_num))
theorem R147349 : Reach 147349 := rs (se 6 (by rfl) ⟨3453, by rfl⟩) (B 6907 (by norm_num) ⟨3453, by rfl⟩ (by norm_num))
theorem R114709 : Reach 114709 := rs (se 6 (by rfl) ⟨2688, by rfl⟩) (B 5377 (by norm_num) ⟨2688, by rfl⟩ (by norm_num))
theorem R81941 : Reach 81941 := rs (se 6 (by rfl) ⟨1920, by rfl⟩) (B 3841 (by norm_num) ⟨1920, by rfl⟩ (by norm_num))
theorem R114797 : Reach 114797 := rs (se 3 (by rfl) ⟨21524, by rfl⟩) (B 43049 (by norm_num) ⟨21524, by rfl⟩ (by norm_num))
theorem R377045 : Reach 377045 := rs (se 7 (by rfl) ⟨4418, by rfl⟩) (B 8837 (by norm_num) ⟨4418, by rfl⟩ (by norm_num))
theorem R114925 : Reach 114925 := rs (se 3 (by rfl) ⟨21548, by rfl⟩) (B 43097 (by norm_num) ⟨21548, by rfl⟩ (by norm_num))
theorem R540917 : Reach 540917 := rs (se 5 (by rfl) ⟨25355, by rfl⟩) (B 50711 (by norm_num) ⟨25355, by rfl⟩ (by norm_num))
theorem R115013 : Reach 115013 := rs (se 4 (by rfl) ⟨10782, by rfl⟩) (B 21565 (by norm_num) ⟨10782, by rfl⟩ (by norm_num))
theorem R147845 : Reach 147845 := rs (se 4 (by rfl) ⟨13860, by rfl⟩) (B 27721 (by norm_num) ⟨13860, by rfl⟩ (by norm_num))
theorem R115141 : Reach 115141 := rs (se 4 (by rfl) ⟨10794, by rfl⟩) (B 21589 (by norm_num) ⟨10794, by rfl⟩ (by norm_num))
theorem R115229 : Reach 115229 := rs (se 3 (by rfl) ⟨21605, by rfl⟩) (B 43211 (by norm_num) ⟨21605, by rfl⟩ (by norm_num))
theorem R115357 : Reach 115357 := rs (se 3 (by rfl) ⟨21629, by rfl⟩) (B 43259 (by norm_num) ⟨21629, by rfl⟩ (by norm_num))
theorem R705205 : Reach 705205 := rs (se 5 (by rfl) ⟨33056, by rfl⟩) (B 66113 (by norm_num) ⟨33056, by rfl⟩ (by norm_num))
theorem R82625 : Reach 82625 := rs (se 2 (by rfl) ⟨30984, by rfl⟩) (B 61969 (by norm_num) ⟨30984, by rfl⟩ (by norm_num))
theorem R115445 : Reach 115445 := rs (se 5 (by rfl) ⟨5411, by rfl⟩) (B 10823 (by norm_num) ⟨5411, by rfl⟩ (by norm_num))
theorem R115573 : Reach 115573 := rs (se 5 (by rfl) ⟨5417, by rfl⟩) (B 10835 (by norm_num) ⟨5417, by rfl⟩ (by norm_num))
theorem R279413 : Reach 279413 := rs (se 5 (by rfl) ⟨13097, by rfl⟩) (B 26195 (by norm_num) ⟨13097, by rfl⟩ (by norm_num))
theorem R115661 : Reach 115661 := rs (se 3 (by rfl) ⟨21686, by rfl⟩) (B 43373 (by norm_num) ⟨21686, by rfl⟩ (by norm_num))
theorem R82981 : Reach 82981 := rs (se 4 (by rfl) ⟨7779, by rfl⟩) (B 15559 (by norm_num) ⟨7779, by rfl⟩ (by norm_num))
theorem R115789 : Reach 115789 := rs (se 3 (by rfl) ⟨21710, by rfl⟩) (B 43421 (by norm_num) ⟨21710, by rfl⟩ (by norm_num))
theorem R345221 : Reach 345221 := rs (se 4 (by rfl) ⟨32364, by rfl⟩) (B 64729 (by norm_num) ⟨32364, by rfl⟩ (by norm_num))
theorem R115877 : Reach 115877 := rs (se 4 (by rfl) ⟨10863, by rfl⟩) (B 21727 (by norm_num) ⟨10863, by rfl⟩ (by norm_num))
theorem R83173 : Reach 83173 := rs (se 4 (by rfl) ⟨7797, by rfl⟩) (B 15595 (by norm_num) ⟨7797, by rfl⟩ (by norm_num))
theorem R148709 : Reach 148709 := rs (se 4 (by rfl) ⟨13941, by rfl⟩) (B 27883 (by norm_num) ⟨13941, by rfl⟩ (by norm_num))
theorem R116005 : Reach 116005 := rs (se 4 (by rfl) ⟨10875, by rfl⟩) (B 21751 (by norm_num) ⟨10875, by rfl⟩ (by norm_num))
theorem R83317 : Reach 83317 := rs (se 5 (by rfl) ⟨3905, by rfl⟩) (B 7811 (by norm_num) ⟨3905, by rfl⟩ (by norm_num))
theorem R148853 : Reach 148853 := rs (se 5 (by rfl) ⟨6977, by rfl⟩) (B 13955 (by norm_num) ⟨6977, by rfl⟩ (by norm_num))
theorem R116093 : Reach 116093 := rs (se 3 (by rfl) ⟨21767, by rfl⟩) (B 43535 (by norm_num) ⟨21767, by rfl⟩ (by norm_num))
theorem R443893 : Reach 443893 := rs (se 5 (by rfl) ⟨20807, by rfl⟩) (B 41615 (by norm_num) ⟨20807, by rfl⟩ (by norm_num))
theorem R116221 : Reach 116221 := rs (se 3 (by rfl) ⟨21791, by rfl⟩) (B 43583 (by norm_num) ⟨21791, by rfl⟩ (by norm_num))
theorem R83521 : Reach 83521 := rs (se 2 (by rfl) ⟨31320, by rfl⟩) (B 62641 (by norm_num) ⟨31320, by rfl⟩ (by norm_num))
theorem R116309 : Reach 116309 := rs (se 8 (by rfl) ⟨681, by rfl⟩) (B 1363 (by norm_num) ⟨681, by rfl⟩ (by norm_num))
theorem R116437 : Reach 116437 := rs (se 7 (by rfl) ⟨1364, by rfl⟩) (B 2729 (by norm_num) ⟨1364, by rfl⟩ (by norm_num))
theorem R116525 : Reach 116525 := rs (se 3 (by rfl) ⟨21848, by rfl⟩) (B 43697 (by norm_num) ⟨21848, by rfl⟩ (by norm_num))
theorem R509813 : Reach 509813 := rs (se 5 (by rfl) ⟨23897, by rfl⟩) (B 47795 (by norm_num) ⟨23897, by rfl⟩ (by norm_num))
theorem R116653 : Reach 116653 := rs (se 3 (by rfl) ⟨21872, by rfl⟩) (B 43745 (by norm_num) ⟨21872, by rfl⟩ (by norm_num))
theorem R247781 : Reach 247781 := rs (se 4 (by rfl) ⟨23229, by rfl⟩) (B 46459 (by norm_num) ⟨23229, by rfl⟩ (by norm_num))
theorem R116741 : Reach 116741 := rs (se 4 (by rfl) ⟨10944, by rfl⟩) (B 21889 (by norm_num) ⟨10944, by rfl⟩ (by norm_num))
theorem R149597 : Reach 149597 := rs (se 3 (by rfl) ⟨28049, by rfl⟩) (B 56099 (by norm_num) ⟨28049, by rfl⟩ (by norm_num))
theorem R116869 : Reach 116869 := rs (se 4 (by rfl) ⟨10956, by rfl⟩) (B 21913 (by norm_num) ⟨10956, by rfl⟩ (by norm_num))
theorem R248021 : Reach 248021 := rs (se 7 (by rfl) ⟨2906, by rfl⟩) (B 5813 (by norm_num) ⟨2906, by rfl⟩ (by norm_num))
theorem R116957 : Reach 116957 := rs (se 3 (by rfl) ⟨21929, by rfl⟩) (B 43859 (by norm_num) ⟨21929, by rfl⟩ (by norm_num))
theorem R117085 : Reach 117085 := rs (se 3 (by rfl) ⟨21953, by rfl⟩) (B 43907 (by norm_num) ⟨21953, by rfl⟩ (by norm_num))
theorem R346517 : Reach 346517 := rs (se 6 (by rfl) ⟨8121, by rfl⟩) (B 16243 (by norm_num) ⟨8121, by rfl⟩ (by norm_num))
theorem R117173 : Reach 117173 := rs (se 5 (by rfl) ⟨5492, by rfl⟩) (B 10985 (by norm_num) ⟨5492, by rfl⟩ (by norm_num))
theorem R248293 : Reach 248293 := rs (se 4 (by rfl) ⟨23277, by rfl⟩) (B 46555 (by norm_num) ⟨23277, by rfl⟩ (by norm_num))
theorem R117301 : Reach 117301 := rs (se 5 (by rfl) ⟨5498, by rfl⟩) (B 10997 (by norm_num) ⟨5498, by rfl⟩ (by norm_num))
theorem R248453 : Reach 248453 := rs (se 4 (by rfl) ⟨23292, by rfl⟩) (B 46585 (by norm_num) ⟨23292, by rfl⟩ (by norm_num))
theorem R117389 : Reach 117389 := rs (se 3 (by rfl) ⟨22010, by rfl⟩) (B 44021 (by norm_num) ⟨22010, by rfl⟩ (by norm_num))
theorem R117517 : Reach 117517 := rs (se 3 (by rfl) ⟨22034, by rfl⟩) (B 44069 (by norm_num) ⟨22034, by rfl⟩ (by norm_num))
theorem R150349 : Reach 150349 := rs (se 3 (by rfl) ⟨28190, by rfl⟩) (B 56381 (by norm_num) ⟨28190, by rfl⟩ (by norm_num))
theorem R117605 : Reach 117605 := rs (se 4 (by rfl) ⟨11025, by rfl⟩) (B 22051 (by norm_num) ⟨11025, by rfl⟩ (by norm_num))
theorem R84845 : Reach 84845 := rs (se 3 (by rfl) ⟨15908, by rfl⟩) (B 31817 (by norm_num) ⟨15908, by rfl⟩ (by norm_num))
theorem R150493 : Reach 150493 := rs (se 3 (by rfl) ⟨28217, by rfl⟩) (B 56435 (by norm_num) ⟨28217, by rfl⟩ (by norm_num))
theorem R117733 : Reach 117733 := rs (se 4 (by rfl) ⟨11037, by rfl⟩) (B 22075 (by norm_num) ⟨11037, by rfl⟩ (by norm_num))
theorem R216053 : Reach 216053 := rs (se 5 (by rfl) ⟨10127, by rfl⟩) (B 20255 (by norm_num) ⟨10127, by rfl⟩ (by norm_num))
theorem R84989 : Reach 84989 := rs (se 3 (by rfl) ⟨15935, by rfl⟩) (B 31871 (by norm_num) ⟨15935, by rfl⟩ (by norm_num))
theorem R85045 : Reach 85045 := rs (se 5 (by rfl) ⟨3986, by rfl⟩) (B 7973 (by norm_num) ⟨3986, by rfl⟩ (by norm_num))
theorem R117821 : Reach 117821 := rs (se 3 (by rfl) ⟨22091, by rfl⟩) (B 44183 (by norm_num) ⟨22091, by rfl⟩ (by norm_num))
theorem R85141 : Reach 85141 := rs (se 6 (by rfl) ⟨1995, by rfl⟩) (B 3991 (by norm_num) ⟨1995, by rfl⟩ (by norm_num))
theorem R85153 : Reach 85153 := rs (se 2 (by rfl) ⟨31932, by rfl⟩) (B 63865 (by norm_num) ⟨31932, by rfl⟩ (by norm_num))
theorem R117949 : Reach 117949 := rs (se 3 (by rfl) ⟨22115, by rfl⟩) (B 44231 (by norm_num) ⟨22115, by rfl⟩ (by norm_num))
theorem R85249 : Reach 85249 := rs (se 2 (by rfl) ⟨31968, by rfl⟩) (B 63937 (by norm_num) ⟨31968, by rfl⟩ (by norm_num))
theorem R118037 : Reach 118037 := rs (se 6 (by rfl) ⟨2766, by rfl⟩) (B 5533 (by norm_num) ⟨2766, by rfl⟩ (by norm_num))
theorem R576821 : Reach 576821 := rs (se 5 (by rfl) ⟨27038, by rfl⟩) (B 54077 (by norm_num) ⟨27038, by rfl⟩ (by norm_num))
theorem R85313 : Reach 85313 := rs (se 2 (by rfl) ⟨31992, by rfl⟩) (B 63985 (by norm_num) ⟨31992, by rfl⟩ (by norm_num))
theorem R150869 : Reach 150869 := rs (se 11 (by rfl) ⟨110, by rfl⟩) (B 221 (by norm_num) ⟨110, by rfl⟩ (by norm_num))
theorem R544085 : Reach 544085 := rs (se 11 (by rfl) ⟨398, by rfl⟩) (B 797 (by norm_num) ⟨398, by rfl⟩ (by norm_num))
theorem R85369 : Reach 85369 := rs (se 2 (by rfl) ⟨32013, by rfl⟩) (B 64027 (by norm_num) ⟨32013, by rfl⟩ (by norm_num))
theorem R118165 : Reach 118165 := rs (se 6 (by rfl) ⟨2769, by rfl⟩) (B 5539 (by norm_num) ⟨2769, by rfl⟩ (by norm_num))
theorem R85465 : Reach 85465 := rs (se 2 (by rfl) ⟨32049, by rfl⟩) (B 64099 (by norm_num) ⟨32049, by rfl⟩ (by norm_num))
theorem R118253 : Reach 118253 := rs (se 3 (by rfl) ⟨22172, by rfl⟩) (B 44345 (by norm_num) ⟨22172, by rfl⟩ (by norm_num))
theorem R151037 : Reach 151037 := rs (se 3 (by rfl) ⟨28319, by rfl⟩) (B 56639 (by norm_num) ⟨28319, by rfl⟩ (by norm_num))
theorem R151093 : Reach 151093 := rs (se 5 (by rfl) ⟨7082, by rfl⟩) (B 14165 (by norm_num) ⟨7082, by rfl⟩ (by norm_num))
theorem R151109 : Reach 151109 := rs (se 4 (by rfl) ⟨14166, by rfl⟩) (B 28333 (by norm_num) ⟨14166, by rfl⟩ (by norm_num))
theorem R118381 : Reach 118381 := rs (se 3 (by rfl) ⟨22196, by rfl⟩) (B 44393 (by norm_num) ⟨22196, by rfl⟩ (by norm_num))
theorem R85637 : Reach 85637 := rs (se 4 (by rfl) ⟨8028, by rfl⟩) (B 16057 (by norm_num) ⟨8028, by rfl⟩ (by norm_num))
theorem R183941 : Reach 183941 := rs (se 4 (by rfl) ⟨17244, by rfl⟩) (B 34489 (by norm_num) ⟨17244, by rfl⟩ (by norm_num))
theorem R151181 : Reach 151181 := rs (se 3 (by rfl) ⟨28346, by rfl⟩) (B 56693 (by norm_num) ⟨28346, by rfl⟩ (by norm_num))
theorem R347813 : Reach 347813 := rs (se 4 (by rfl) ⟨32607, by rfl⟩) (B 65215 (by norm_num) ⟨32607, by rfl⟩ (by norm_num))
theorem R85693 : Reach 85693 := rs (se 3 (by rfl) ⟨16067, by rfl⟩) (B 32135 (by norm_num) ⟨16067, by rfl⟩ (by norm_num))
theorem R118469 : Reach 118469 := rs (se 4 (by rfl) ⟨11106, by rfl⟩) (B 22213 (by norm_num) ⟨11106, by rfl⟩ (by norm_num))
theorem R151237 : Reach 151237 := rs (se 4 (by rfl) ⟨14178, by rfl⟩) (B 28357 (by norm_num) ⟨14178, by rfl⟩ (by norm_num))
theorem R151253 : Reach 151253 := rs (se 7 (by rfl) ⟨1772, by rfl⟩) (B 3545 (by norm_num) ⟨1772, by rfl⟩ (by norm_num))
theorem R85765 : Reach 85765 := rs (se 4 (by rfl) ⟨8040, by rfl⟩) (B 16081 (by norm_num) ⟨8040, by rfl⟩ (by norm_num))
theorem R151325 : Reach 151325 := rs (se 3 (by rfl) ⟨28373, by rfl⟩) (B 56747 (by norm_num) ⟨28373, by rfl⟩ (by norm_num))
theorem R85789 : Reach 85789 := rs (se 3 (by rfl) ⟨16085, by rfl⟩) (B 32171 (by norm_num) ⟨16085, by rfl⟩ (by norm_num))
theorem R118597 : Reach 118597 := rs (se 4 (by rfl) ⟨11118, by rfl⟩) (B 22237 (by norm_num) ⟨11118, by rfl⟩ (by norm_num))
theorem R151397 : Reach 151397 := rs (se 4 (by rfl) ⟨14193, by rfl⟩) (B 28387 (by norm_num) ⟨14193, by rfl⟩ (by norm_num))
theorem R118685 : Reach 118685 := rs (se 3 (by rfl) ⟨22253, by rfl⟩) (B 44507 (by norm_num) ⟨22253, by rfl⟩ (by norm_num))
theorem R282533 : Reach 282533 := rs (se 4 (by rfl) ⟨26487, by rfl⟩) (B 52975 (by norm_num) ⟨26487, by rfl⟩ (by norm_num))
theorem R151469 : Reach 151469 := rs (se 3 (by rfl) ⟨28400, by rfl⟩) (B 56801 (by norm_num) ⟨28400, by rfl⟩ (by norm_num))
theorem R85961 : Reach 85961 := rs (se 2 (by rfl) ⟨32235, by rfl⟩) (B 64471 (by norm_num) ⟨32235, by rfl⟩ (by norm_num))
theorem R151541 : Reach 151541 := rs (se 5 (by rfl) ⟨7103, by rfl⟩) (B 14207 (by norm_num) ⟨7103, by rfl⟩ (by norm_num))
theorem R86017 : Reach 86017 := rs (se 2 (by rfl) ⟨32256, by rfl⟩) (B 64513 (by norm_num) ⟨32256, by rfl⟩ (by norm_num))
theorem R118813 : Reach 118813 := rs (se 3 (by rfl) ⟨22277, by rfl⟩) (B 44555 (by norm_num) ⟨22277, by rfl⟩ (by norm_num))
theorem R151613 : Reach 151613 := rs (se 3 (by rfl) ⟨28427, by rfl⟩) (B 56855 (by norm_num) ⟨28427, by rfl⟩ (by norm_num))
theorem R1527893 : Reach 1527893 := rs (se 8 (by rfl) ⟨8952, by rfl⟩) (B 17905 (by norm_num) ⟨8952, by rfl⟩ (by norm_num))
theorem R86113 : Reach 86113 := rs (se 2 (by rfl) ⟨32292, by rfl⟩) (B 64585 (by norm_num) ⟨32292, by rfl⟩ (by norm_num))
theorem R118901 : Reach 118901 := rs (se 5 (by rfl) ⟨5573, by rfl⟩) (B 11147 (by norm_num) ⟨5573, by rfl⟩ (by norm_num))
theorem R151685 : Reach 151685 := rs (se 4 (by rfl) ⟨14220, by rfl⟩) (B 28441 (by norm_num) ⟨14220, by rfl⟩ (by norm_num))
theorem R675989 : Reach 675989 := rs (se 6 (by rfl) ⟨15843, by rfl⟩) (B 31687 (by norm_num) ⟨15843, by rfl⟩ (by norm_num))
theorem R151757 : Reach 151757 := rs (se 3 (by rfl) ⟨28454, by rfl⟩) (B 56909 (by norm_num) ⟨28454, by rfl⟩ (by norm_num))
theorem R217333 : Reach 217333 := rs (se 5 (by rfl) ⟨10187, by rfl⟩) (B 20375 (by norm_num) ⟨10187, by rfl⟩ (by norm_num))
theorem R119029 : Reach 119029 := rs (se 5 (by rfl) ⟨5579, by rfl⟩) (B 11159 (by norm_num) ⟨5579, by rfl⟩ (by norm_num))
theorem R86285 : Reach 86285 := rs (se 3 (by rfl) ⟨16178, by rfl⟩) (B 32357 (by norm_num) ⟨16178, by rfl⟩ (by norm_num))
theorem R151829 : Reach 151829 := rs (se 6 (by rfl) ⟨3558, by rfl⟩) (B 7117 (by norm_num) ⟨3558, by rfl⟩ (by norm_num))
theorem R446741 : Reach 446741 := rs (se 6 (by rfl) ⟨10470, by rfl⟩) (B 20941 (by norm_num) ⟨10470, by rfl⟩ (by norm_num))
theorem R86341 : Reach 86341 := rs (se 4 (by rfl) ⟨8094, by rfl⟩) (B 16189 (by norm_num) ⟨8094, by rfl⟩ (by norm_num))
theorem R119117 : Reach 119117 := rs (se 3 (by rfl) ⟨22334, by rfl⟩) (B 44669 (by norm_num) ⟨22334, by rfl⟩ (by norm_num))
theorem R151901 : Reach 151901 := rs (se 3 (by rfl) ⟨28481, by rfl⟩) (B 56963 (by norm_num) ⟨28481, by rfl⟩ (by norm_num))
theorem R151973 : Reach 151973 := rs (se 4 (by rfl) ⟨14247, by rfl⟩) (B 28495 (by norm_num) ⟨14247, by rfl⟩ (by norm_num))
theorem R86437 : Reach 86437 := rs (se 4 (by rfl) ⟨8103, by rfl⟩) (B 16207 (by norm_num) ⟨8103, by rfl⟩ (by norm_num))
theorem R119245 : Reach 119245 := rs (se 3 (by rfl) ⟨22358, by rfl⟩) (B 44717 (by norm_num) ⟨22358, by rfl⟩ (by norm_num))
theorem R86509 : Reach 86509 := rs (se 3 (by rfl) ⟨16220, by rfl⟩) (B 32441 (by norm_num) ⟨16220, by rfl⟩ (by norm_num))
theorem R152045 : Reach 152045 := rs (se 3 (by rfl) ⟨28508, by rfl⟩) (B 57017 (by norm_num) ⟨28508, by rfl⟩ (by norm_num))
theorem R119333 : Reach 119333 := rs (se 4 (by rfl) ⟨11187, by rfl⟩) (B 22375 (by norm_num) ⟨11187, by rfl⟩ (by norm_num))
theorem R152117 : Reach 152117 := rs (se 5 (by rfl) ⟨7130, by rfl⟩) (B 14261 (by norm_num) ⟨7130, by rfl⟩ (by norm_num))
theorem R86609 : Reach 86609 := rs (se 2 (by rfl) ⟨32478, by rfl⟩) (B 64957 (by norm_num) ⟨32478, by rfl⟩ (by norm_num))
theorem R184933 : Reach 184933 := rs (se 4 (by rfl) ⟨17337, by rfl⟩) (B 34675 (by norm_num) ⟨17337, by rfl⟩ (by norm_num))
theorem R152189 : Reach 152189 := rs (se 3 (by rfl) ⟨28535, by rfl⟩) (B 57071 (by norm_num) ⟨28535, by rfl⟩ (by norm_num))
theorem R86665 : Reach 86665 := rs (se 2 (by rfl) ⟨32499, by rfl⟩) (B 64999 (by norm_num) ⟨32499, by rfl⟩ (by norm_num))
theorem R119461 : Reach 119461 := rs (se 4 (by rfl) ⟨11199, by rfl⟩) (B 22399 (by norm_num) ⟨11199, by rfl⟩ (by norm_num))
theorem R152261 : Reach 152261 := rs (se 4 (by rfl) ⟨14274, by rfl⟩) (B 28549 (by norm_num) ⟨14274, by rfl⟩ (by norm_num))
theorem R86761 : Reach 86761 := rs (se 2 (by rfl) ⟨32535, by rfl⟩) (B 65071 (by norm_num) ⟨32535, by rfl⟩ (by norm_num))
theorem R119549 : Reach 119549 := rs (se 3 (by rfl) ⟨22415, by rfl⟩) (B 44831 (by norm_num) ⟨22415, by rfl⟩ (by norm_num))
theorem R152333 : Reach 152333 := rs (se 3 (by rfl) ⟨28562, by rfl⟩) (B 57125 (by norm_num) ⟨28562, by rfl⟩ (by norm_num))
theorem R152405 : Reach 152405 := rs (se 9 (by rfl) ⟨446, by rfl⟩) (B 893 (by norm_num) ⟨446, by rfl⟩ (by norm_num))
theorem R119677 : Reach 119677 := rs (se 3 (by rfl) ⟨22439, by rfl⟩) (B 44879 (by norm_num) ⟨22439, by rfl⟩ (by norm_num))
theorem R86933 : Reach 86933 := rs (se 6 (by rfl) ⟨2037, by rfl⟩) (B 4075 (by norm_num) ⟨2037, by rfl⟩ (by norm_num))
theorem R152477 : Reach 152477 := rs (se 3 (by rfl) ⟨28589, by rfl⟩) (B 57179 (by norm_num) ⟨28589, by rfl⟩ (by norm_num))
theorem R349109 : Reach 349109 := rs (se 5 (by rfl) ⟨16364, by rfl⟩) (B 32729 (by norm_num) ⟨16364, by rfl⟩ (by norm_num))
theorem R86989 : Reach 86989 := rs (se 3 (by rfl) ⟨16310, by rfl⟩) (B 32621 (by norm_num) ⟨16310, by rfl⟩ (by norm_num))
theorem R119765 : Reach 119765 := rs (se 7 (by rfl) ⟨1403, by rfl⟩) (B 2807 (by norm_num) ⟨1403, by rfl⟩ (by norm_num))
theorem R152549 : Reach 152549 := rs (se 4 (by rfl) ⟨14301, by rfl⟩) (B 28603 (by norm_num) ⟨14301, by rfl⟩ (by norm_num))
theorem R152621 : Reach 152621 := rs (se 3 (by rfl) ⟨28616, by rfl⟩) (B 57233 (by norm_num) ⟨28616, by rfl⟩ (by norm_num))
theorem R87085 : Reach 87085 := rs (se 3 (by rfl) ⟨16328, by rfl⟩) (B 32657 (by norm_num) ⟨16328, by rfl⟩ (by norm_num))
theorem R119893 : Reach 119893 := rs (se 8 (by rfl) ⟨702, by rfl⟩) (B 1405 (by norm_num) ⟨702, by rfl⟩ (by norm_num))
theorem R152693 : Reach 152693 := rs (se 5 (by rfl) ⟨7157, by rfl⟩) (B 14315 (by norm_num) ⟨7157, by rfl⟩ (by norm_num))
theorem R119981 : Reach 119981 := rs (se 3 (by rfl) ⟨22496, by rfl⟩) (B 44993 (by norm_num) ⟨22496, by rfl⟩ (by norm_num))
theorem R152765 : Reach 152765 := rs (se 3 (by rfl) ⟨28643, by rfl⟩) (B 57287 (by norm_num) ⟨28643, by rfl⟩ (by norm_num))
theorem R87257 : Reach 87257 := rs (se 2 (by rfl) ⟨32721, by rfl⟩) (B 65443 (by norm_num) ⟨32721, by rfl⟩ (by norm_num))
theorem R152837 : Reach 152837 := rs (se 4 (by rfl) ⟨14328, by rfl⟩) (B 28657 (by norm_num) ⟨14328, by rfl⟩ (by norm_num))
theorem R87313 : Reach 87313 := rs (se 2 (by rfl) ⟨32742, by rfl⟩) (B 65485 (by norm_num) ⟨32742, by rfl⟩ (by norm_num))
theorem R152909 : Reach 152909 := rs (se 3 (by rfl) ⟨28670, by rfl⟩) (B 57341 (by norm_num) ⟨28670, by rfl⟩ (by norm_num))
theorem R251221 : Reach 251221 := rs (se 15 (by rfl) ⟨11, by rfl⟩) (B 23 (by norm_num) ⟨11, by rfl⟩ (by norm_num))
theorem R87409 : Reach 87409 := rs (se 2 (by rfl) ⟨32778, by rfl⟩) (B 65557 (by norm_num) ⟨32778, by rfl⟩ (by norm_num))
theorem R152981 : Reach 152981 := rs (se 6 (by rfl) ⟨3585, by rfl⟩) (B 7171 (by norm_num) ⟨3585, by rfl⟩ (by norm_num))
theorem R185797 : Reach 185797 := rs (se 4 (by rfl) ⟨17418, by rfl⟩) (B 34837 (by norm_num) ⟨17418, by rfl⟩ (by norm_num))
theorem R153053 : Reach 153053 := rs (se 3 (by rfl) ⟨28697, by rfl⟩) (B 57395 (by norm_num) ⟨28697, by rfl⟩ (by norm_num))
theorem R87581 : Reach 87581 := rs (se 3 (by rfl) ⟨16421, by rfl⟩) (B 32843 (by norm_num) ⟨16421, by rfl⟩ (by norm_num))
theorem R153125 : Reach 153125 := rs (se 4 (by rfl) ⟨14355, by rfl⟩) (B 28711 (by norm_num) ⟨14355, by rfl⟩ (by norm_num))
theorem R218693 : Reach 218693 := rs (se 4 (by rfl) ⟨20502, by rfl⟩) (B 41005 (by norm_num) ⟨20502, by rfl⟩ (by norm_num))
theorem R87637 : Reach 87637 := rs (se 8 (by rfl) ⟨513, by rfl⟩) (B 1027 (by norm_num) ⟨513, by rfl⟩ (by norm_num))
theorem R153197 : Reach 153197 := rs (se 3 (by rfl) ⟨28724, by rfl⟩) (B 57449 (by norm_num) ⟨28724, by rfl⟩ (by norm_num))
theorem R87685 : Reach 87685 := rs (se 4 (by rfl) ⟨8220, by rfl⟩) (B 16441 (by norm_num) ⟨8220, by rfl⟩ (by norm_num))
theorem R87725 : Reach 87725 := rs (se 3 (by rfl) ⟨16448, by rfl⟩) (B 32897 (by norm_num) ⟨16448, by rfl⟩ (by norm_num))
theorem R153269 : Reach 153269 := rs (se 5 (by rfl) ⟨7184, by rfl⟩) (B 14369 (by norm_num) ⟨7184, by rfl⟩ (by norm_num))
theorem R87733 : Reach 87733 := rs (se 5 (by rfl) ⟨4112, by rfl⟩) (B 8225 (by norm_num) ⟨4112, by rfl⟩ (by norm_num))
theorem R218821 : Reach 218821 := rs (se 4 (by rfl) ⟨20514, by rfl⟩) (B 41029 (by norm_num) ⟨20514, by rfl⟩ (by norm_num))
theorem R153341 : Reach 153341 := rs (se 3 (by rfl) ⟨28751, by rfl⟩) (B 57503 (by norm_num) ⟨28751, by rfl⟩ (by norm_num))
theorem R153413 : Reach 153413 := rs (se 4 (by rfl) ⟨14382, by rfl⟩) (B 28765 (by norm_num) ⟨14382, by rfl⟩ (by norm_num))
theorem R87905 : Reach 87905 := rs (se 2 (by rfl) ⟨32964, by rfl⟩) (B 65929 (by norm_num) ⟨32964, by rfl⟩ (by norm_num))
theorem R153485 : Reach 153485 := rs (se 3 (by rfl) ⟨28778, by rfl⟩) (B 57557 (by norm_num) ⟨28778, by rfl⟩ (by norm_num))
theorem R87961 : Reach 87961 := rs (se 2 (by rfl) ⟨32985, by rfl⟩) (B 65971 (by norm_num) ⟨32985, by rfl⟩ (by norm_num))
theorem R219077 : Reach 219077 := rs (se 4 (by rfl) ⟨20538, by rfl⟩) (B 41077 (by norm_num) ⟨20538, by rfl⟩ (by norm_num))
theorem R153557 : Reach 153557 := rs (se 7 (by rfl) ⟨1799, by rfl⟩) (B 3599 (by norm_num) ⟨1799, by rfl⟩ (by norm_num))
theorem R88057 : Reach 88057 := rs (se 2 (by rfl) ⟨33021, by rfl⟩) (B 66043 (by norm_num) ⟨33021, by rfl⟩ (by norm_num))
theorem R153629 : Reach 153629 := rs (se 3 (by rfl) ⟨28805, by rfl⟩) (B 57611 (by norm_num) ⟨28805, by rfl⟩ (by norm_num))
theorem R153701 : Reach 153701 := rs (se 4 (by rfl) ⟨14409, by rfl⟩) (B 28819 (by norm_num) ⟨14409, by rfl⟩ (by norm_num))
theorem R88229 : Reach 88229 := rs (se 4 (by rfl) ⟨8271, by rfl⟩) (B 16543 (by norm_num) ⟨8271, by rfl⟩ (by norm_num))
theorem R153773 : Reach 153773 := rs (se 3 (by rfl) ⟨28832, by rfl⟩) (B 57665 (by norm_num) ⟨28832, by rfl⟩ (by norm_num))
theorem R350405 : Reach 350405 := rs (se 4 (by rfl) ⟨32850, by rfl⟩) (B 65701 (by norm_num) ⟨32850, by rfl⟩ (by norm_num))
theorem R579797 : Reach 579797 := rs (se 7 (by rfl) ⟨6794, by rfl⟩) (B 13589 (by norm_num) ⟨6794, by rfl⟩ (by norm_num))
theorem R88285 : Reach 88285 := rs (se 3 (by rfl) ⟨16553, by rfl⟩) (B 33107 (by norm_num) ⟨16553, by rfl⟩ (by norm_num))
theorem R153845 : Reach 153845 := rs (se 5 (by rfl) ⟨7211, by rfl⟩) (B 14423 (by norm_num) ⟨7211, by rfl⟩ (by norm_num))
theorem R153917 : Reach 153917 := rs (se 3 (by rfl) ⟨28859, by rfl⟩) (B 57719 (by norm_num) ⟨28859, by rfl⟩ (by norm_num))
theorem R88381 : Reach 88381 := rs (se 3 (by rfl) ⟨16571, by rfl⟩) (B 33143 (by norm_num) ⟨16571, by rfl⟩ (by norm_num))
theorem R153989 : Reach 153989 := rs (se 4 (by rfl) ⟨14436, by rfl⟩) (B 28873 (by norm_num) ⟨14436, by rfl⟩ (by norm_num))
theorem R121285 : Reach 121285 := rs (se 4 (by rfl) ⟨11370, by rfl⟩) (B 22741 (by norm_num) ⟨11370, by rfl⟩ (by norm_num))
theorem R154061 : Reach 154061 := rs (se 3 (by rfl) ⟨28886, by rfl⟩) (B 57773 (by norm_num) ⟨28886, by rfl⟩ (by norm_num))
theorem R88553 : Reach 88553 := rs (se 2 (by rfl) ⟨33207, by rfl⟩) (B 66415 (by norm_num) ⟨33207, by rfl⟩ (by norm_num))
theorem R154133 : Reach 154133 := rs (se 6 (by rfl) ⟨3612, by rfl⟩) (B 7225 (by norm_num) ⟨3612, by rfl⟩ (by norm_num))
theorem R88609 : Reach 88609 := rs (se 2 (by rfl) ⟨33228, by rfl⟩) (B 66457 (by norm_num) ⟨33228, by rfl⟩ (by norm_num))
theorem R154205 : Reach 154205 := rs (se 3 (by rfl) ⟨28913, by rfl⟩) (B 57827 (by norm_num) ⟨28913, by rfl⟩ (by norm_num))
theorem R88705 : Reach 88705 := rs (se 2 (by rfl) ⟨33264, by rfl⟩) (B 66529 (by norm_num) ⟨33264, by rfl⟩ (by norm_num))
theorem R154277 : Reach 154277 := rs (se 4 (by rfl) ⟨14463, by rfl⟩) (B 28927 (by norm_num) ⟨14463, by rfl⟩ (by norm_num))
theorem R154349 : Reach 154349 := rs (se 3 (by rfl) ⟨28940, by rfl⟩) (B 57881 (by norm_num) ⟨28940, by rfl⟩ (by norm_num))
theorem R88877 : Reach 88877 := rs (se 3 (by rfl) ⟨16664, by rfl⟩) (B 33329 (by norm_num) ⟨16664, by rfl⟩ (by norm_num))
theorem R154421 : Reach 154421 := rs (se 5 (by rfl) ⟨7238, by rfl⟩) (B 14477 (by norm_num) ⟨7238, by rfl⟩ (by norm_num))
theorem R88921 : Reach 88921 := rs (se 2 (by rfl) ⟨33345, by rfl⟩) (B 66691 (by norm_num) ⟨33345, by rfl⟩ (by norm_num))
theorem R88933 : Reach 88933 := rs (se 4 (by rfl) ⟨8337, by rfl⟩) (B 16675 (by norm_num) ⟨8337, by rfl⟩ (by norm_num))
theorem R154493 : Reach 154493 := rs (se 3 (by rfl) ⟨28967, by rfl⟩) (B 57935 (by norm_num) ⟨28967, by rfl⟩ (by norm_num))
theorem R154565 : Reach 154565 := rs (se 4 (by rfl) ⟨14490, by rfl⟩) (B 28981 (by norm_num) ⟨14490, by rfl⟩ (by norm_num))
theorem R89029 : Reach 89029 := rs (se 4 (by rfl) ⟨8346, by rfl⟩) (B 16693 (by norm_num) ⟨8346, by rfl⟩ (by norm_num))
theorem R154637 : Reach 154637 := rs (se 3 (by rfl) ⟨28994, by rfl⟩) (B 57989 (by norm_num) ⟨28994, by rfl⟩ (by norm_num))
theorem R154709 : Reach 154709 := rs (se 8 (by rfl) ⟨906, by rfl⟩) (B 1813 (by norm_num) ⟨906, by rfl⟩ (by norm_num))
theorem R89201 : Reach 89201 := rs (se 2 (by rfl) ⟨33450, by rfl⟩) (B 66901 (by norm_num) ⟨33450, by rfl⟩ (by norm_num))
theorem R154781 : Reach 154781 := rs (se 3 (by rfl) ⟨29021, by rfl⟩) (B 58043 (by norm_num) ⟨29021, by rfl⟩ (by norm_num))
theorem R89257 : Reach 89257 := rs (se 2 (by rfl) ⟨33471, by rfl⟩) (B 66943 (by norm_num) ⟨33471, by rfl⟩ (by norm_num))
theorem R154853 : Reach 154853 := rs (se 4 (by rfl) ⟨14517, by rfl⟩) (B 29035 (by norm_num) ⟨14517, by rfl⟩ (by norm_num))
theorem R89353 : Reach 89353 := rs (se 2 (by rfl) ⟨33507, by rfl⟩) (B 67015 (by norm_num) ⟨33507, by rfl⟩ (by norm_num))
theorem R154925 : Reach 154925 := rs (se 3 (by rfl) ⟨29048, by rfl⟩) (B 58097 (by norm_num) ⟨29048, by rfl⟩ (by norm_num))
theorem R122165 : Reach 122165 := rs (se 5 (by rfl) ⟨5726, by rfl⟩) (B 11453 (by norm_num) ⟨5726, by rfl⟩ (by norm_num))
theorem R154997 : Reach 154997 := rs (se 5 (by rfl) ⟨7265, by rfl⟩) (B 14531 (by norm_num) ⟨7265, by rfl⟩ (by norm_num))
theorem R89525 : Reach 89525 := rs (se 5 (by rfl) ⟨4196, by rfl⟩) (B 8393 (by norm_num) ⟨4196, by rfl⟩ (by norm_num))
theorem R155069 : Reach 155069 := rs (se 3 (by rfl) ⟨29075, by rfl⟩) (B 58151 (by norm_num) ⟨29075, by rfl⟩ (by norm_num))
theorem R253381 : Reach 253381 := rs (se 4 (by rfl) ⟨23754, by rfl⟩) (B 47509 (by norm_num) ⟨23754, by rfl⟩ (by norm_num))
theorem R351701 : Reach 351701 := rs (se 7 (by rfl) ⟨4121, by rfl⟩) (B 8243 (by norm_num) ⟨4121, by rfl⟩ (by norm_num))
theorem R89581 : Reach 89581 := rs (se 3 (by rfl) ⟨16796, by rfl⟩) (B 33593 (by norm_num) ⟨16796, by rfl⟩ (by norm_num))
theorem R155141 : Reach 155141 := rs (se 4 (by rfl) ⟨14544, by rfl⟩) (B 29089 (by norm_num) ⟨14544, by rfl⟩ (by norm_num))
theorem R155213 : Reach 155213 := rs (se 3 (by rfl) ⟨29102, by rfl⟩) (B 58205 (by norm_num) ⟨29102, by rfl⟩ (by norm_num))
theorem R89677 : Reach 89677 := rs (se 3 (by rfl) ⟨16814, by rfl⟩) (B 33629 (by norm_num) ⟨16814, by rfl⟩ (by norm_num))
theorem R155285 : Reach 155285 := rs (se 6 (by rfl) ⟨3639, by rfl⟩) (B 7279 (by norm_num) ⟨3639, by rfl⟩ (by norm_num))
theorem R155357 : Reach 155357 := rs (se 3 (by rfl) ⟨29129, by rfl⟩) (B 58259 (by norm_num) ⟨29129, by rfl⟩ (by norm_num))
theorem R351989 : Reach 351989 := rs (se 5 (by rfl) ⟨16499, by rfl⟩) (B 32999 (by norm_num) ⟨16499, by rfl⟩ (by norm_num))
theorem R155429 : Reach 155429 := rs (se 4 (by rfl) ⟨14571, by rfl⟩) (B 29143 (by norm_num) ⟨14571, by rfl⟩ (by norm_num))
theorem R384821 : Reach 384821 := rs (se 5 (by rfl) ⟨18038, by rfl⟩) (B 36077 (by norm_num) ⟨18038, by rfl⟩ (by norm_num))
theorem R155501 : Reach 155501 := rs (se 3 (by rfl) ⟨29156, by rfl⟩) (B 58313 (by norm_num) ⟨29156, by rfl⟩ (by norm_num))
theorem R253829 : Reach 253829 := rs (se 4 (by rfl) ⟨23796, by rfl⟩) (B 47593 (by norm_num) ⟨23796, by rfl⟩ (by norm_num))
theorem R155573 : Reach 155573 := rs (se 5 (by rfl) ⟨7292, by rfl⟩) (B 14585 (by norm_num) ⟨7292, by rfl⟩ (by norm_num))
theorem R155645 : Reach 155645 := rs (se 3 (by rfl) ⟨29183, by rfl⟩) (B 58367 (by norm_num) ⟨29183, by rfl⟩ (by norm_num))
theorem R155717 : Reach 155717 := rs (se 4 (by rfl) ⟨14598, by rfl⟩) (B 29197 (by norm_num) ⟨14598, by rfl⟩ (by norm_num))
theorem R155789 : Reach 155789 := rs (se 3 (by rfl) ⟨29210, by rfl⟩) (B 58421 (by norm_num) ⟨29210, by rfl⟩ (by norm_num))
theorem R155861 : Reach 155861 := rs (se 7 (by rfl) ⟨1826, by rfl⟩) (B 3653 (by norm_num) ⟨1826, by rfl⟩ (by norm_num))
theorem R155933 : Reach 155933 := rs (se 3 (by rfl) ⟨29237, by rfl⟩) (B 58475 (by norm_num) ⟨29237, by rfl⟩ (by norm_num))
theorem R123173 : Reach 123173 := rs (se 4 (by rfl) ⟨11547, by rfl⟩) (B 23095 (by norm_num) ⟨11547, by rfl⟩ (by norm_num))
theorem R221525 : Reach 221525 := rs (se 10 (by rfl) ⟨324, by rfl⟩) (B 649 (by norm_num) ⟨324, by rfl⟩ (by norm_num))
theorem R156005 : Reach 156005 := rs (se 4 (by rfl) ⟨14625, by rfl⟩) (B 29251 (by norm_num) ⟨14625, by rfl⟩ (by norm_num))
theorem R156077 : Reach 156077 := rs (se 3 (by rfl) ⟨29264, by rfl⟩) (B 58529 (by norm_num) ⟨29264, by rfl⟩ (by norm_num))
theorem R156149 : Reach 156149 := rs (se 5 (by rfl) ⟨7319, by rfl⟩) (B 14639 (by norm_num) ⟨7319, by rfl⟩ (by norm_num))
theorem R221717 : Reach 221717 := rs (se 6 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R156221 : Reach 156221 := rs (se 3 (by rfl) ⟨29291, by rfl⟩) (B 58583 (by norm_num) ⟨29291, by rfl⟩ (by norm_num))
theorem R287317 : Reach 287317 := rs (se 8 (by rfl) ⟨1683, by rfl⟩) (B 3367 (by norm_num) ⟨1683, by rfl⟩ (by norm_num))
theorem R156293 : Reach 156293 := rs (se 4 (by rfl) ⟨14652, by rfl⟩) (B 29305 (by norm_num) ⟨14652, by rfl⟩ (by norm_num))
theorem R156365 : Reach 156365 := rs (se 3 (by rfl) ⟨29318, by rfl⟩) (B 58637 (by norm_num) ⟨29318, by rfl⟩ (by norm_num))
theorem R352997 : Reach 352997 := rs (se 4 (by rfl) ⟨33093, by rfl⟩) (B 66187 (by norm_num) ⟨33093, by rfl⟩ (by norm_num))
theorem R156437 : Reach 156437 := rs (se 6 (by rfl) ⟨3666, by rfl⟩) (B 7333 (by norm_num) ⟨3666, by rfl⟩ (by norm_num))
theorem R156509 : Reach 156509 := rs (se 3 (by rfl) ⟨29345, by rfl⟩) (B 58691 (by norm_num) ⟨29345, by rfl⟩ (by norm_num))
theorem R156581 : Reach 156581 := rs (se 4 (by rfl) ⟨14679, by rfl⟩) (B 29359 (by norm_num) ⟨14679, by rfl⟩ (by norm_num))
theorem R386005 : Reach 386005 := rs (se 7 (by rfl) ⟨4523, by rfl⟩) (B 9047 (by norm_num) ⟨4523, by rfl⟩ (by norm_num))
theorem R156653 : Reach 156653 := rs (se 3 (by rfl) ⟨29372, by rfl⟩) (B 58745 (by norm_num) ⟨29372, by rfl⟩ (by norm_num))
theorem R156725 : Reach 156725 := rs (se 5 (by rfl) ⟨7346, by rfl⟩) (B 14693 (by norm_num) ⟨7346, by rfl⟩ (by norm_num))
theorem R287813 : Reach 287813 := rs (se 4 (by rfl) ⟨26982, by rfl⟩) (B 53965 (by norm_num) ⟨26982, by rfl⟩ (by norm_num))
theorem R156797 : Reach 156797 := rs (se 3 (by rfl) ⟨29399, by rfl⟩) (B 58799 (by norm_num) ⟨29399, by rfl⟩ (by norm_num))
theorem R156869 : Reach 156869 := rs (se 4 (by rfl) ⟨14706, by rfl⟩) (B 29413 (by norm_num) ⟨14706, by rfl⟩ (by norm_num))
theorem R156941 : Reach 156941 := rs (se 3 (by rfl) ⟨29426, by rfl⟩) (B 58853 (by norm_num) ⟨29426, by rfl⟩ (by norm_num))
theorem R157013 : Reach 157013 := rs (se 12 (by rfl) ⟨57, by rfl⟩) (B 115 (by norm_num) ⟨57, by rfl⟩ (by norm_num))
theorem R157085 : Reach 157085 := rs (se 3 (by rfl) ⟨29453, by rfl⟩) (B 58907 (by norm_num) ⟨29453, by rfl⟩ (by norm_num))
theorem R517589 : Reach 517589 := rs (se 7 (by rfl) ⟨6065, by rfl⟩) (B 12131 (by norm_num) ⟨6065, by rfl⟩ (by norm_num))
theorem R157157 : Reach 157157 := rs (se 4 (by rfl) ⟨14733, by rfl⟩) (B 29467 (by norm_num) ⟨14733, by rfl⟩ (by norm_num))
theorem R157229 : Reach 157229 := rs (se 3 (by rfl) ⟨29480, by rfl⟩) (B 58961 (by norm_num) ⟨29480, by rfl⟩ (by norm_num))
theorem R157301 : Reach 157301 := rs (se 5 (by rfl) ⟨7373, by rfl⟩) (B 14747 (by norm_num) ⟨7373, by rfl⟩ (by norm_num))
theorem R222869 : Reach 222869 := rs (se 6 (by rfl) ⟨5223, by rfl⟩) (B 10447 (by norm_num) ⟨5223, by rfl⟩ (by norm_num))
theorem R157373 : Reach 157373 := rs (se 3 (by rfl) ⟨29507, by rfl⟩) (B 59015 (by norm_num) ⟨29507, by rfl⟩ (by norm_num))
theorem R157445 : Reach 157445 := rs (se 4 (by rfl) ⟨14760, by rfl⟩) (B 29521 (by norm_num) ⟨14760, by rfl⟩ (by norm_num))
theorem R157517 : Reach 157517 := rs (se 3 (by rfl) ⟨29534, by rfl⟩) (B 59069 (by norm_num) ⟨29534, by rfl⟩ (by norm_num))
theorem R6022997 : Reach 6022997 := rs (se 9 (by rfl) ⟨17645, by rfl⟩) (B 35291 (by norm_num) ⟨17645, by rfl⟩ (by norm_num))
theorem R157589 : Reach 157589 := rs (se 6 (by rfl) ⟨3693, by rfl⟩) (B 7387 (by norm_num) ⟨3693, by rfl⟩ (by norm_num))
theorem R124861 : Reach 124861 := rs (se 3 (by rfl) ⟨23411, by rfl⟩) (B 46823 (by norm_num) ⟨23411, by rfl⟩ (by norm_num))
theorem R157661 : Reach 157661 := rs (se 3 (by rfl) ⟨29561, by rfl⟩) (B 59123 (by norm_num) ⟨29561, by rfl⟩ (by norm_num))
theorem R354293 : Reach 354293 := rs (se 5 (by rfl) ⟨16607, by rfl⟩) (B 33215 (by norm_num) ⟨16607, by rfl⟩ (by norm_num))
theorem R157717 : Reach 157717 := rs (se 6 (by rfl) ⟨3696, by rfl⟩) (B 7393 (by norm_num) ⟨3696, by rfl⟩ (by norm_num))
theorem R288805 : Reach 288805 := rs (se 4 (by rfl) ⟨27075, by rfl⟩) (B 54151 (by norm_num) ⟨27075, by rfl⟩ (by norm_num))
theorem R157733 : Reach 157733 := rs (se 4 (by rfl) ⟨14787, by rfl⟩) (B 29575 (by norm_num) ⟨14787, by rfl⟩ (by norm_num))
theorem R288821 : Reach 288821 := rs (se 5 (by rfl) ⟨13538, by rfl⟩) (B 27077 (by norm_num) ⟨13538, by rfl⟩ (by norm_num))
theorem R157805 : Reach 157805 := rs (se 3 (by rfl) ⟨29588, by rfl⟩) (B 59177 (by norm_num) ⟨29588, by rfl⟩ (by norm_num))
theorem R125069 : Reach 125069 := rs (se 3 (by rfl) ⟨23450, by rfl⟩) (B 46901 (by norm_num) ⟨23450, by rfl⟩ (by norm_num))
theorem R125077 : Reach 125077 := rs (se 6 (by rfl) ⟨2931, by rfl⟩) (B 5863 (by norm_num) ⟨2931, by rfl⟩ (by norm_num))
theorem R157877 : Reach 157877 := rs (se 5 (by rfl) ⟨7400, by rfl⟩) (B 14801 (by norm_num) ⟨7400, by rfl⟩ (by norm_num))
theorem R256229 : Reach 256229 := rs (se 4 (by rfl) ⟨24021, by rfl⟩) (B 48043 (by norm_num) ⟨24021, by rfl⟩ (by norm_num))
theorem R157949 : Reach 157949 := rs (se 3 (by rfl) ⟨29615, by rfl⟩) (B 59231 (by norm_num) ⟨29615, by rfl⟩ (by norm_num))
theorem R125221 : Reach 125221 := rs (se 4 (by rfl) ⟨11739, by rfl⟩) (B 23479 (by norm_num) ⟨11739, by rfl⟩ (by norm_num))
theorem R158021 : Reach 158021 := rs (se 4 (by rfl) ⟨14814, by rfl⟩) (B 29629 (by norm_num) ⟨14814, by rfl⟩ (by norm_num))
theorem R158093 : Reach 158093 := rs (se 3 (by rfl) ⟨29642, by rfl⟩) (B 59285 (by norm_num) ⟨29642, by rfl⟩ (by norm_num))
theorem R158165 : Reach 158165 := rs (se 7 (by rfl) ⟨1853, by rfl⟩) (B 3707 (by norm_num) ⟨1853, by rfl⟩ (by norm_num))
theorem R256517 : Reach 256517 := rs (se 4 (by rfl) ⟨24048, by rfl⟩) (B 48097 (by norm_num) ⟨24048, by rfl⟩ (by norm_num))
theorem R158237 : Reach 158237 := rs (se 3 (by rfl) ⟨29669, by rfl⟩) (B 59339 (by norm_num) ⟨29669, by rfl⟩ (by norm_num))
theorem R158309 : Reach 158309 := rs (se 4 (by rfl) ⟨14841, by rfl⟩) (B 29683 (by norm_num) ⟨14841, by rfl⟩ (by norm_num))
theorem R158381 : Reach 158381 := rs (se 3 (by rfl) ⟨29696, by rfl⟩) (B 59393 (by norm_num) ⟨29696, by rfl⟩ (by norm_num))
theorem R158453 : Reach 158453 := rs (se 5 (by rfl) ⟨7427, by rfl⟩) (B 14855 (by norm_num) ⟨7427, by rfl⟩ (by norm_num))
theorem R191269 : Reach 191269 := rs (se 4 (by rfl) ⟨17931, by rfl⟩) (B 35863 (by norm_num) ⟨17931, by rfl⟩ (by norm_num))
theorem R158525 : Reach 158525 := rs (se 3 (by rfl) ⟨29723, by rfl⟩) (B 59447 (by norm_num) ⟨29723, by rfl⟩ (by norm_num))
theorem R191317 : Reach 191317 := rs (se 9 (by rfl) ⟨560, by rfl⟩) (B 1121 (by norm_num) ⟨560, by rfl⟩ (by norm_num))
theorem R191333 : Reach 191333 := rs (se 4 (by rfl) ⟨17937, by rfl⟩) (B 35875 (by norm_num) ⟨17937, by rfl⟩ (by norm_num))
theorem R158597 : Reach 158597 := rs (se 4 (by rfl) ⟨14868, by rfl⟩) (B 29737 (by norm_num) ⟨14868, by rfl⟩ (by norm_num))
theorem R387989 : Reach 387989 := rs (se 6 (by rfl) ⟨9093, by rfl⟩) (B 18187 (by norm_num) ⟨9093, by rfl⟩ (by norm_num))
theorem R158669 : Reach 158669 := rs (se 3 (by rfl) ⟨29750, by rfl⟩) (B 59501 (by norm_num) ⟨29750, by rfl⟩ (by norm_num))
theorem R191477 : Reach 191477 := rs (se 5 (by rfl) ⟨8975, by rfl⟩) (B 17951 (by norm_num) ⟨8975, by rfl⟩ (by norm_num))
theorem R125941 : Reach 125941 := rs (se 5 (by rfl) ⟨5903, by rfl⟩) (B 11807 (by norm_num) ⟨5903, by rfl⟩ (by norm_num))
theorem R158741 : Reach 158741 := rs (se 6 (by rfl) ⟨3720, by rfl⟩) (B 7441 (by norm_num) ⟨3720, by rfl⟩ (by norm_num))
theorem R126029 : Reach 126029 := rs (se 3 (by rfl) ⟨23630, by rfl⟩) (B 47261 (by norm_num) ⟨23630, by rfl⟩ (by norm_num))
theorem R158813 : Reach 158813 := rs (se 3 (by rfl) ⟨29777, by rfl⟩) (B 59555 (by norm_num) ⟨29777, by rfl⟩ (by norm_num))
theorem R158885 : Reach 158885 := rs (se 4 (by rfl) ⟨14895, by rfl⟩) (B 29791 (by norm_num) ⟨14895, by rfl⟩ (by norm_num))
theorem R257189 : Reach 257189 := rs (se 4 (by rfl) ⟨24111, by rfl⟩) (B 48223 (by norm_num) ⟨24111, by rfl⟩ (by norm_num))
theorem R191717 : Reach 191717 := rs (se 4 (by rfl) ⟨17973, by rfl⟩) (B 35947 (by norm_num) ⟨17973, by rfl⟩ (by norm_num))
theorem R158957 : Reach 158957 := rs (se 3 (by rfl) ⟨29804, by rfl⟩) (B 59609 (by norm_num) ⟨29804, by rfl⟩ (by norm_num))
theorem R355589 : Reach 355589 := rs (se 4 (by rfl) ⟨33336, by rfl⟩) (B 66673 (by norm_num) ⟨33336, by rfl⟩ (by norm_num))
theorem R159029 : Reach 159029 := rs (se 5 (by rfl) ⟨7454, by rfl⟩) (B 14909 (by norm_num) ⟨7454, by rfl⟩ (by norm_num))
theorem R159101 : Reach 159101 := rs (se 3 (by rfl) ⟨29831, by rfl⟩) (B 59663 (by norm_num) ⟨29831, by rfl⟩ (by norm_num))
theorem R191909 : Reach 191909 := rs (se 4 (by rfl) ⟨17991, by rfl⟩) (B 35983 (by norm_num) ⟨17991, by rfl⟩ (by norm_num))
theorem R159173 : Reach 159173 := rs (se 4 (by rfl) ⟨14922, by rfl⟩) (B 29845 (by norm_num) ⟨14922, by rfl⟩ (by norm_num))
theorem R126461 : Reach 126461 := rs (se 3 (by rfl) ⟨23711, by rfl⟩) (B 47423 (by norm_num) ⟨23711, by rfl⟩ (by norm_num))
theorem R159245 : Reach 159245 := rs (se 3 (by rfl) ⟨29858, by rfl⟩) (B 59717 (by norm_num) ⟨29858, by rfl⟩ (by norm_num))
theorem R159317 : Reach 159317 := rs (se 8 (by rfl) ⟨933, by rfl⟩) (B 1867 (by norm_num) ⟨933, by rfl⟩ (by norm_num))
theorem R224869 : Reach 224869 := rs (se 4 (by rfl) ⟨21081, by rfl⟩) (B 42163 (by norm_num) ⟨21081, by rfl⟩ (by norm_num))
theorem R126605 : Reach 126605 := rs (se 3 (by rfl) ⟨23738, by rfl⟩) (B 47477 (by norm_num) ⟨23738, by rfl⟩ (by norm_num))
theorem R192149 : Reach 192149 := rs (se 6 (by rfl) ⟨4503, by rfl⟩) (B 9007 (by norm_num) ⟨4503, by rfl⟩ (by norm_num))
theorem R159389 : Reach 159389 := rs (se 3 (by rfl) ⟨29885, by rfl⟩) (B 59771 (by norm_num) ⟨29885, by rfl⟩ (by norm_num))
theorem R257701 : Reach 257701 := rs (se 4 (by rfl) ⟨24159, by rfl⟩) (B 48319 (by norm_num) ⟨24159, by rfl⟩ (by norm_num))
theorem R159461 : Reach 159461 := rs (se 4 (by rfl) ⟨14949, by rfl⟩) (B 29899 (by norm_num) ⟨14949, by rfl⟩ (by norm_num))
theorem R159533 : Reach 159533 := rs (se 3 (by rfl) ⟨29912, by rfl⟩) (B 59825 (by norm_num) ⟨29912, by rfl⟩ (by norm_num))
theorem R126821 : Reach 126821 := rs (se 4 (by rfl) ⟨11889, by rfl⟩) (B 23779 (by norm_num) ⟨11889, by rfl⟩ (by norm_num))
theorem R159605 : Reach 159605 := rs (se 5 (by rfl) ⟨7481, by rfl⟩) (B 14963 (by norm_num) ⟨7481, by rfl⟩ (by norm_num))
theorem R159677 : Reach 159677 := rs (se 3 (by rfl) ⟨29939, by rfl⟩) (B 59879 (by norm_num) ⟨29939, by rfl⟩ (by norm_num))
theorem R258005 : Reach 258005 := rs (se 7 (by rfl) ⟨3023, by rfl⟩) (B 6047 (by norm_num) ⟨3023, by rfl⟩ (by norm_num))
theorem R159749 : Reach 159749 := rs (se 4 (by rfl) ⟨14976, by rfl⟩) (B 29953 (by norm_num) ⟨14976, by rfl⟩ (by norm_num))
theorem R159821 : Reach 159821 := rs (se 3 (by rfl) ⟨29966, by rfl⟩) (B 59933 (by norm_num) ⟨29966, by rfl⟩ (by norm_num))
theorem R159893 : Reach 159893 := rs (se 6 (by rfl) ⟨3747, by rfl⟩) (B 7495 (by norm_num) ⟨3747, by rfl⟩ (by norm_num))
theorem R159965 : Reach 159965 := rs (se 3 (by rfl) ⟨29993, by rfl⟩) (B 59987 (by norm_num) ⟨29993, by rfl⟩ (by norm_num))
theorem R291077 : Reach 291077 := rs (se 4 (by rfl) ⟨27288, by rfl⟩) (B 54577 (by norm_num) ⟨27288, by rfl⟩ (by norm_num))
theorem R192901 : Reach 192901 := rs (se 4 (by rfl) ⟨18084, by rfl⟩) (B 36169 (by norm_num) ⟨18084, by rfl⟩ (by norm_num))
theorem R160157 : Reach 160157 := rs (se 3 (by rfl) ⟨30029, by rfl⟩) (B 60059 (by norm_num) ⟨30029, by rfl⟩ (by norm_num))
theorem R127469 : Reach 127469 := rs (se 3 (by rfl) ⟨23900, by rfl⟩) (B 47801 (by norm_num) ⟨23900, by rfl⟩ (by norm_num))
theorem R356885 : Reach 356885 := rs (se 6 (by rfl) ⟨8364, by rfl⟩) (B 16729 (by norm_num) ⟨8364, by rfl⟩ (by norm_num))
theorem R127613 : Reach 127613 := rs (se 3 (by rfl) ⟨23927, by rfl⟩) (B 47855 (by norm_num) ⟨23927, by rfl⟩ (by norm_num))
theorem R127757 : Reach 127757 := rs (se 3 (by rfl) ⟨23954, by rfl⟩) (B 47909 (by norm_num) ⟨23954, by rfl⟩ (by norm_num))
theorem R127837 : Reach 127837 := rs (se 3 (by rfl) ⟨23969, by rfl⟩) (B 47939 (by norm_num) ⟨23969, by rfl⟩ (by norm_num))
theorem R127909 : Reach 127909 := rs (se 4 (by rfl) ⟨11991, by rfl⟩) (B 23983 (by norm_num) ⟨11991, by rfl⟩ (by norm_num))
theorem R390197 : Reach 390197 := rs (se 5 (by rfl) ⟨18290, by rfl⟩) (B 36581 (by norm_num) ⟨18290, by rfl⟩ (by norm_num))
theorem R128213 : Reach 128213 := rs (se 7 (by rfl) ⟨1502, by rfl⟩) (B 3005 (by norm_num) ⟨1502, by rfl⟩ (by norm_num))
theorem R95461 : Reach 95461 := rs (se 4 (by rfl) ⟨8949, by rfl⟩) (B 17899 (by norm_num) ⟨8949, by rfl⟩ (by norm_num))
theorem R128413 : Reach 128413 := rs (se 3 (by rfl) ⟨24077, by rfl⟩) (B 48155 (by norm_num) ⟨24077, by rfl⟩ (by norm_num))
theorem R194005 : Reach 194005 := rs (se 7 (by rfl) ⟨2273, by rfl⟩) (B 4547 (by norm_num) ⟨2273, by rfl⟩ (by norm_num))
theorem R226853 : Reach 226853 := rs (se 4 (by rfl) ⟨21267, by rfl⟩) (B 42535 (by norm_num) ⟨21267, by rfl⟩ (by norm_num))
theorem R161357 : Reach 161357 := rs (se 3 (by rfl) ⟨30254, by rfl⟩) (B 60509 (by norm_num) ⟨30254, by rfl⟩ (by norm_num))
theorem R95845 : Reach 95845 := rs (se 4 (by rfl) ⟨8985, by rfl⟩) (B 17971 (by norm_num) ⟨8985, by rfl⟩ (by norm_num))
theorem R95909 : Reach 95909 := rs (se 4 (by rfl) ⟨8991, by rfl⟩) (B 17983 (by norm_num) ⟨8991, by rfl⟩ (by norm_num))
theorem R96013 : Reach 96013 := rs (se 3 (by rfl) ⟨18002, by rfl⟩) (B 36005 (by norm_num) ⟨18002, by rfl⟩ (by norm_num))
theorem R128965 : Reach 128965 := rs (se 4 (by rfl) ⟨12090, by rfl⟩) (B 24181 (by norm_num) ⟨12090, by rfl⟩ (by norm_num))
theorem R227285 : Reach 227285 := rs (se 7 (by rfl) ⟨2663, by rfl⟩) (B 5327 (by norm_num) ⟨2663, by rfl⟩ (by norm_num))
theorem R260117 : Reach 260117 := rs (se 6 (by rfl) ⟨6096, by rfl⟩) (B 12193 (by norm_num) ⟨6096, by rfl⟩ (by norm_num))
theorem R129109 : Reach 129109 := rs (se 8 (by rfl) ⟨756, by rfl⟩) (B 1513 (by norm_num) ⟨756, by rfl⟩ (by norm_num))
theorem R129269 : Reach 129269 := rs (se 5 (by rfl) ⟨6059, by rfl⟩) (B 12119 (by norm_num) ⟨6059, by rfl⟩ (by norm_num))
theorem R260405 : Reach 260405 := rs (se 5 (by rfl) ⟨12206, by rfl⟩) (B 24413 (by norm_num) ⟨12206, by rfl⟩ (by norm_num))
theorem R227717 : Reach 227717 := rs (se 4 (by rfl) ⟨21348, by rfl⟩) (B 42697 (by norm_num) ⟨21348, by rfl⟩ (by norm_num))
theorem R129413 : Reach 129413 := rs (se 4 (by rfl) ⟨12132, by rfl⟩) (B 24265 (by norm_num) ⟨12132, by rfl⟩ (by norm_num))
theorem R96661 : Reach 96661 := rs (se 6 (by rfl) ⟨2265, by rfl⟩) (B 4531 (by norm_num) ⟨2265, by rfl⟩ (by norm_num))
theorem R653845 : Reach 653845 := rs (se 6 (by rfl) ⟨15324, by rfl⟩) (B 30649 (by norm_num) ⟨15324, by rfl⟩ (by norm_num))
theorem R129701 : Reach 129701 := rs (se 4 (by rfl) ⟨12159, by rfl⟩) (B 24319 (by norm_num) ⟨12159, by rfl⟩ (by norm_num))
theorem R228149 : Reach 228149 := rs (se 5 (by rfl) ⟨10694, by rfl⟩) (B 21389 (by norm_num) ⟨10694, by rfl⟩ (by norm_num))
theorem R129853 : Reach 129853 := rs (se 3 (by rfl) ⟨24347, by rfl⟩) (B 48695 (by norm_num) ⟨24347, by rfl⟩ (by norm_num))
theorem R326501 : Reach 326501 := rs (se 4 (by rfl) ⟨30609, by rfl⟩) (B 61219 (by norm_num) ⟨30609, by rfl⟩ (by norm_num))
theorem R1014677 : Reach 1014677 := rs (se 6 (by rfl) ⟨23781, by rfl⟩) (B 47563 (by norm_num) ⟨23781, by rfl⟩ (by norm_num))
theorem R195509 : Reach 195509 := rs (se 5 (by rfl) ⟨9164, by rfl⟩) (B 18329 (by norm_num) ⟨9164, by rfl⟩ (by norm_num))
theorem R359477 : Reach 359477 := rs (se 5 (by rfl) ⟨16850, by rfl⟩) (B 33701 (by norm_num) ⟨16850, by rfl⟩ (by norm_num))
theorem R130157 : Reach 130157 := rs (se 3 (by rfl) ⟨24404, by rfl⟩) (B 48809 (by norm_num) ⟨24404, by rfl⟩ (by norm_num))
theorem R97453 : Reach 97453 := rs (se 3 (by rfl) ⟨18272, by rfl⟩) (B 36545 (by norm_num) ⟨18272, by rfl⟩ (by norm_num))
theorem R228581 : Reach 228581 := rs (se 4 (by rfl) ⟨21429, by rfl⟩) (B 42859 (by norm_num) ⟨21429, by rfl⟩ (by norm_num))
theorem R261589 : Reach 261589 := rs (se 7 (by rfl) ⟨3065, by rfl⟩) (B 6131 (by norm_num) ⟨3065, by rfl⟩ (by norm_num))
theorem R97789 : Reach 97789 := rs (se 3 (by rfl) ⟨18335, by rfl⟩) (B 36671 (by norm_num) ⟨18335, by rfl⟩ (by norm_num))
theorem R261701 : Reach 261701 := rs (se 4 (by rfl) ⟨24534, by rfl⟩) (B 49069 (by norm_num) ⟨24534, by rfl⟩ (by norm_num))
theorem R229013 : Reach 229013 := rs (se 6 (by rfl) ⟨5367, by rfl⟩) (B 10735 (by norm_num) ⟨5367, by rfl⟩ (by norm_num))
theorem R98005 : Reach 98005 := rs (se 7 (by rfl) ⟨1148, by rfl⟩) (B 2297 (by norm_num) ⟨1148, by rfl⟩ (by norm_num))
theorem R261893 : Reach 261893 := rs (se 4 (by rfl) ⟨24552, by rfl⟩) (B 49105 (by norm_num) ⟨24552, by rfl⟩ (by norm_num))
theorem R1408853 : Reach 1408853 := rs (se 9 (by rfl) ⟨4127, by rfl⟩) (B 8255 (by norm_num) ⟨4127, by rfl⟩ (by norm_num))
theorem R130909 : Reach 130909 := rs (se 3 (by rfl) ⟨24545, by rfl⟩) (B 49091 (by norm_num) ⟨24545, by rfl⟩ (by norm_num))
theorem R131053 : Reach 131053 := rs (se 3 (by rfl) ⟨24572, by rfl⟩) (B 49145 (by norm_num) ⟨24572, by rfl⟩ (by norm_num))
theorem R196739 : Reach 196739 := rs (se 1 (by rfl) ⟨147554, by rfl⟩) R295109
theorem R360611 : Reach 360611 := rs (se 1 (by rfl) ⟨270458, by rfl⟩) R540917
theorem R229553 : Reach 229553 := rs (se 2 (by rfl) ⟨86082, by rfl⟩) R172165
theorem R1474757 : Reach 1474757 := rs (se 4 (by rfl) ⟨138258, by rfl⟩) R276517
theorem R262349 : Reach 262349 := rs (se 3 (by rfl) ⟨49190, by rfl⟩) R98381
theorem R131395 : Reach 131395 := rs (se 1 (by rfl) ⟨98546, by rfl⟩) R197093
theorem R230093 : Reach 230093 := rs (se 3 (by rfl) ⟨43142, by rfl⟩) R86285
theorem R230147 : Reach 230147 := rs (se 1 (by rfl) ⟨172610, by rfl⟩) R345221
theorem R131843 : Reach 131843 := rs (se 1 (by rfl) ⟨98882, by rfl⟩) R197765
theorem R99139 : Reach 99139 := rs (se 1 (by rfl) ⟨74354, by rfl⟩) R148709
theorem R99235 : Reach 99235 := rs (se 1 (by rfl) ⟨74426, by rfl⟩) R148853
theorem R197549 : Reach 197549 := rs (se 3 (by rfl) ⟨37040, by rfl⟩) R74081
theorem R394253 : Reach 394253 := rs (se 3 (by rfl) ⟨73922, by rfl⟩) R147845
theorem R230417 : Reach 230417 := rs (se 2 (by rfl) ⟨86406, by rfl⟩) R172813
theorem R132131 : Reach 132131 := rs (se 1 (by rfl) ⟨99098, by rfl⟩) R198197
theorem R197741 : Reach 197741 := rs (se 3 (by rfl) ⟨37076, by rfl⟩) R74153
theorem R165187 : Reach 165187 := rs (se 1 (by rfl) ⟨123890, by rfl⟩) R247781
theorem R99731 : Reach 99731 := rs (se 1 (by rfl) ⟨74798, by rfl⟩) R149597
theorem R165347 : Reach 165347 := rs (se 1 (by rfl) ⟨124010, by rfl⟩) R248021
theorem R230957 : Reach 230957 := rs (se 3 (by rfl) ⟨43304, by rfl⟩) R86609
theorem R67139 : Reach 67139 := rs (se 1 (by rfl) ⟨50354, by rfl⟩) R100709
theorem R67155 : Reach 67155 := rs (se 1 (by rfl) ⟨50366, by rfl⟩) R100733
theorem R67171 : Reach 67171 := rs (se 1 (by rfl) ⟨50378, by rfl⟩) R100757
theorem R231011 : Reach 231011 := rs (se 1 (by rfl) ⟨173258, by rfl⟩) R346517
theorem R67187 : Reach 67187 := rs (se 1 (by rfl) ⟨50390, by rfl⟩) R100781
theorem R67203 : Reach 67203 := rs (se 1 (by rfl) ⟨50402, by rfl⟩) R100805
theorem R67219 : Reach 67219 := rs (se 1 (by rfl) ⟨50414, by rfl⟩) R100829
theorem R67235 : Reach 67235 := rs (se 1 (by rfl) ⟨50426, by rfl⟩) R100853
theorem R67251 : Reach 67251 := rs (se 1 (by rfl) ⟨50438, by rfl⟩) R100877
theorem R67267 : Reach 67267 := rs (se 1 (by rfl) ⟨50450, by rfl⟩) R100901
theorem R67283 : Reach 67283 := rs (se 1 (by rfl) ⟨50462, by rfl⟩) R100925
theorem R67299 : Reach 67299 := rs (se 1 (by rfl) ⟨50474, by rfl⟩) R100949
theorem R67315 : Reach 67315 := rs (se 1 (by rfl) ⟨50486, by rfl⟩) R100973
theorem R67331 : Reach 67331 := rs (se 1 (by rfl) ⟨50498, by rfl⟩) R100997
theorem R165635 : Reach 165635 := rs (se 1 (by rfl) ⟨124226, by rfl⟩) R248453
theorem R67347 : Reach 67347 := rs (se 1 (by rfl) ⟨50510, by rfl⟩) R101021
theorem R67363 : Reach 67363 := rs (se 1 (by rfl) ⟨50522, by rfl⟩) R101045
theorem R67379 : Reach 67379 := rs (se 1 (by rfl) ⟨50534, by rfl⟩) R101069
theorem R67395 : Reach 67395 := rs (se 1 (by rfl) ⟨50546, by rfl⟩) R101093
theorem R67411 : Reach 67411 := rs (se 1 (by rfl) ⟨50558, by rfl⟩) R101117
theorem R67427 : Reach 67427 := rs (se 1 (by rfl) ⟨50570, by rfl⟩) R101141
theorem R231281 : Reach 231281 := rs (se 2 (by rfl) ⟨86730, by rfl⟩) R173461
theorem R67443 : Reach 67443 := rs (se 1 (by rfl) ⟨50582, by rfl⟩) R101165
theorem R67459 : Reach 67459 := rs (se 1 (by rfl) ⟨50594, by rfl⟩) R101189
theorem R67475 : Reach 67475 := rs (se 1 (by rfl) ⟨50606, by rfl⟩) R101213
theorem R67491 : Reach 67491 := rs (se 1 (by rfl) ⟨50618, by rfl⟩) R101237
theorem R67507 : Reach 67507 := rs (se 1 (by rfl) ⟨50630, by rfl⟩) R101261
theorem R67523 : Reach 67523 := rs (se 1 (by rfl) ⟨50642, by rfl⟩) R101285
theorem R133073 : Reach 133073 := rs (se 2 (by rfl) ⟨49902, by rfl⟩) R99805
theorem R67539 : Reach 67539 := rs (se 1 (by rfl) ⟨50654, by rfl⟩) R101309
theorem R67555 : Reach 67555 := rs (se 1 (by rfl) ⟨50666, by rfl⟩) R101333
theorem R591857 : Reach 591857 := rs (se 2 (by rfl) ⟨221946, by rfl⟩) R443893
theorem R67571 : Reach 67571 := rs (se 1 (by rfl) ⟨50678, by rfl⟩) R101357
theorem R67587 : Reach 67587 := rs (se 1 (by rfl) ⟨50690, by rfl⟩) R101381
theorem R100369 : Reach 100369 := rs (se 2 (by rfl) ⟨37638, by rfl⟩) R75277
theorem R67603 : Reach 67603 := rs (se 1 (by rfl) ⟨50702, by rfl⟩) R101405
theorem R67619 : Reach 67619 := rs (se 1 (by rfl) ⟨50714, by rfl⟩) R101429
theorem R67635 : Reach 67635 := rs (se 1 (by rfl) ⟨50726, by rfl⟩) R101453
theorem R67651 : Reach 67651 := rs (se 1 (by rfl) ⟨50738, by rfl⟩) R101477
theorem R198733 : Reach 198733 := rs (se 3 (by rfl) ⟨37262, by rfl⟩) R74525
theorem R67667 : Reach 67667 := rs (se 1 (by rfl) ⟨50750, by rfl⟩) R101501
theorem R67683 : Reach 67683 := rs (se 1 (by rfl) ⟨50762, by rfl⟩) R101525
theorem R329827 : Reach 329827 := rs (se 1 (by rfl) ⟨247370, by rfl⟩) R494741
theorem R67699 : Reach 67699 := rs (se 1 (by rfl) ⟨50774, by rfl⟩) R101549
theorem R67715 : Reach 67715 := rs (se 1 (by rfl) ⟨50786, by rfl⟩) R101573
theorem R67731 : Reach 67731 := rs (se 1 (by rfl) ⟨50798, by rfl⟩) R101597
theorem R67747 : Reach 67747 := rs (se 1 (by rfl) ⟨50810, by rfl⟩) R101621
theorem R67763 : Reach 67763 := rs (se 1 (by rfl) ⟨50822, by rfl⟩) R101645
theorem R67779 : Reach 67779 := rs (se 1 (by rfl) ⟨50834, by rfl⟩) R101669
theorem R67795 : Reach 67795 := rs (se 1 (by rfl) ⟨50846, by rfl⟩) R101693
theorem R67811 : Reach 67811 := rs (se 1 (by rfl) ⟨50858, by rfl⟩) R101717
theorem R362723 : Reach 362723 := rs (se 1 (by rfl) ⟨272042, by rfl⟩) R544085
theorem R67827 : Reach 67827 := rs (se 1 (by rfl) ⟨50870, by rfl⟩) R101741
theorem R67843 : Reach 67843 := rs (se 1 (by rfl) ⟨50882, by rfl⟩) R101765
theorem R67859 : Reach 67859 := rs (se 1 (by rfl) ⟨50894, by rfl⟩) R101789
theorem R67875 : Reach 67875 := rs (se 1 (by rfl) ⟨50906, by rfl⟩) R101813
theorem R67891 : Reach 67891 := rs (se 1 (by rfl) ⟨50918, by rfl⟩) R101837
theorem R67907 : Reach 67907 := rs (se 1 (by rfl) ⟨50930, by rfl⟩) R101861
theorem R100691 : Reach 100691 := rs (se 1 (by rfl) ⟨75518, by rfl⟩) R151037
theorem R67923 : Reach 67923 := rs (se 1 (by rfl) ⟨50942, by rfl⟩) R101885
theorem R67939 : Reach 67939 := rs (se 1 (by rfl) ⟨50954, by rfl⟩) R101909
theorem R100705 : Reach 100705 := rs (se 2 (by rfl) ⟨37764, by rfl⟩) R75529
theorem R100721 : Reach 100721 := rs (se 2 (by rfl) ⟨37770, by rfl⟩) R75541
theorem R67955 : Reach 67955 := rs (se 1 (by rfl) ⟨50966, by rfl⟩) R101933
theorem R100739 : Reach 100739 := rs (se 1 (by rfl) ⟨75554, by rfl⟩) R151109
theorem R67971 : Reach 67971 := rs (se 1 (by rfl) ⟨50978, by rfl⟩) R101957
theorem R231821 : Reach 231821 := rs (se 3 (by rfl) ⟨43466, by rfl⟩) R86933
theorem R67987 : Reach 67987 := rs (se 1 (by rfl) ⟨50990, by rfl⟩) R101981
theorem R100769 : Reach 100769 := rs (se 2 (by rfl) ⟨37788, by rfl⟩) R75577
theorem R68003 : Reach 68003 := rs (se 1 (by rfl) ⟨51002, by rfl⟩) R102005
theorem R100787 : Reach 100787 := rs (se 1 (by rfl) ⟨75590, by rfl⟩) R151181
theorem R68019 : Reach 68019 := rs (se 1 (by rfl) ⟨51014, by rfl⟩) R102029
theorem R68035 : Reach 68035 := rs (se 1 (by rfl) ⟨51026, by rfl⟩) R102053
theorem R231875 : Reach 231875 := rs (se 1 (by rfl) ⟨173906, by rfl⟩) R347813
theorem R100817 : Reach 100817 := rs (se 2 (by rfl) ⟨37806, by rfl⟩) R75613
theorem R68051 : Reach 68051 := rs (se 1 (by rfl) ⟨51038, by rfl⟩) R102077
theorem R100835 : Reach 100835 := rs (se 1 (by rfl) ⟨75626, by rfl⟩) R151253
theorem R68067 : Reach 68067 := rs (se 1 (by rfl) ⟨51050, by rfl⟩) R102101
theorem R68083 : Reach 68083 := rs (se 1 (by rfl) ⟨51062, by rfl⟩) R102125
theorem R100865 : Reach 100865 := rs (se 2 (by rfl) ⟨37824, by rfl⟩) R75649
theorem R68099 : Reach 68099 := rs (se 1 (by rfl) ⟨51074, by rfl⟩) R102149
theorem R100883 : Reach 100883 := rs (se 1 (by rfl) ⟨75662, by rfl⟩) R151325
theorem R68115 : Reach 68115 := rs (se 1 (by rfl) ⟨51086, by rfl⟩) R102173
theorem R68131 : Reach 68131 := rs (se 1 (by rfl) ⟨51098, by rfl⟩) R102197
theorem R100913 : Reach 100913 := rs (se 2 (by rfl) ⟨37842, by rfl⟩) R75685
theorem R68147 : Reach 68147 := rs (se 1 (by rfl) ⟨51110, by rfl⟩) R102221
theorem R100931 : Reach 100931 := rs (se 1 (by rfl) ⟨75698, by rfl⟩) R151397
theorem R68163 : Reach 68163 := rs (se 1 (by rfl) ⟨51122, by rfl⟩) R102245
theorem R68179 : Reach 68179 := rs (se 1 (by rfl) ⟨51134, by rfl⟩) R102269
theorem R166481 : Reach 166481 := rs (se 2 (by rfl) ⟨62430, by rfl⟩) R124861
theorem R100961 : Reach 100961 := rs (se 2 (by rfl) ⟨37860, by rfl⟩) R75721
theorem R68195 : Reach 68195 := rs (se 1 (by rfl) ⟨51146, by rfl⟩) R102293
theorem R756337 : Reach 756337 := rs (se 2 (by rfl) ⟨283626, by rfl⟩) R567253
theorem R100979 : Reach 100979 := rs (se 1 (by rfl) ⟨75734, by rfl⟩) R151469
theorem R68211 : Reach 68211 := rs (se 1 (by rfl) ⟨51158, by rfl⟩) R102317
theorem R68227 : Reach 68227 := rs (se 1 (by rfl) ⟨51170, by rfl⟩) R102341
theorem R101009 : Reach 101009 := rs (se 2 (by rfl) ⟨37878, by rfl⟩) R75757
theorem R68243 : Reach 68243 := rs (se 1 (by rfl) ⟨51182, by rfl⟩) R102365
theorem R101027 : Reach 101027 := rs (se 1 (by rfl) ⟨75770, by rfl⟩) R151541
theorem R68259 : Reach 68259 := rs (se 1 (by rfl) ⟨51194, by rfl⟩) R102389
theorem R68275 : Reach 68275 := rs (se 1 (by rfl) ⟨51206, by rfl⟩) R102413
theorem R101057 : Reach 101057 := rs (se 2 (by rfl) ⟨37896, by rfl⟩) R75793
theorem R68291 : Reach 68291 := rs (se 1 (by rfl) ⟨51218, by rfl⟩) R102437
theorem R232145 : Reach 232145 := rs (se 2 (by rfl) ⟨87054, by rfl⟩) R174109
theorem R101075 : Reach 101075 := rs (se 1 (by rfl) ⟨75806, by rfl⟩) R151613
theorem R68307 : Reach 68307 := rs (se 1 (by rfl) ⟨51230, by rfl⟩) R102461
theorem R68323 : Reach 68323 := rs (se 1 (by rfl) ⟨51242, by rfl⟩) R102485
theorem R1018595 : Reach 1018595 := rs (se 1 (by rfl) ⟨763946, by rfl⟩) R1527893
theorem R101105 : Reach 101105 := rs (se 2 (by rfl) ⟨37914, by rfl⟩) R75829
theorem R68339 : Reach 68339 := rs (se 1 (by rfl) ⟨51254, by rfl⟩) R102509
theorem R101123 : Reach 101123 := rs (se 1 (by rfl) ⟨75842, by rfl⟩) R151685
theorem R68355 : Reach 68355 := rs (se 1 (by rfl) ⟨51266, by rfl⟩) R102533
theorem R68371 : Reach 68371 := rs (se 1 (by rfl) ⟨51278, by rfl⟩) R102557
theorem R101153 : Reach 101153 := rs (se 2 (by rfl) ⟨37932, by rfl⟩) R75865
theorem R68387 : Reach 68387 := rs (se 1 (by rfl) ⟨51290, by rfl⟩) R102581
theorem R101171 : Reach 101171 := rs (se 1 (by rfl) ⟨75878, by rfl⟩) R151757
theorem R68403 : Reach 68403 := rs (se 1 (by rfl) ⟨51302, by rfl⟩) R102605
theorem R68419 : Reach 68419 := rs (se 1 (by rfl) ⟨51314, by rfl⟩) R102629
theorem R265037 : Reach 265037 := rs (se 3 (by rfl) ⟨49694, by rfl⟩) R99389
theorem R101201 : Reach 101201 := rs (se 2 (by rfl) ⟨37950, by rfl⟩) R75901
theorem R68435 : Reach 68435 := rs (se 1 (by rfl) ⟨51326, by rfl⟩) R102653
theorem R133969 : Reach 133969 := rs (se 2 (by rfl) ⟨50238, by rfl⟩) R100477
theorem R101219 : Reach 101219 := rs (se 1 (by rfl) ⟨75914, by rfl⟩) R151829
theorem R68451 : Reach 68451 := rs (se 1 (by rfl) ⟨51338, by rfl⟩) R102677
theorem R297827 : Reach 297827 := rs (se 1 (by rfl) ⟨223370, by rfl⟩) R446741
theorem R166769 : Reach 166769 := rs (se 2 (by rfl) ⟨62538, by rfl⟩) R125077
theorem R68467 : Reach 68467 := rs (se 1 (by rfl) ⟨51350, by rfl⟩) R102701
theorem R101249 : Reach 101249 := rs (se 2 (by rfl) ⟨37968, by rfl⟩) R75937
theorem R68483 : Reach 68483 := rs (se 1 (by rfl) ⟨51362, by rfl⟩) R102725
theorem R101267 : Reach 101267 := rs (se 1 (by rfl) ⟨75950, by rfl⟩) R151901
theorem R68499 : Reach 68499 := rs (se 1 (by rfl) ⟨51374, by rfl⟩) R102749
theorem R68515 : Reach 68515 := rs (se 1 (by rfl) ⟨51386, by rfl⟩) R102773
theorem R101297 : Reach 101297 := rs (se 2 (by rfl) ⟨37986, by rfl⟩) R75973
theorem R68531 : Reach 68531 := rs (se 1 (by rfl) ⟨51398, by rfl⟩) R102797
theorem R101315 : Reach 101315 := rs (se 1 (by rfl) ⟨75986, by rfl⟩) R151973
theorem R68547 : Reach 68547 := rs (se 1 (by rfl) ⟨51410, by rfl⟩) R102821
theorem R68563 : Reach 68563 := rs (se 1 (by rfl) ⟨51422, by rfl⟩) R102845
theorem R101345 : Reach 101345 := rs (se 2 (by rfl) ⟨38004, by rfl⟩) R76009
theorem R68579 : Reach 68579 := rs (se 1 (by rfl) ⟨51434, by rfl⟩) R102869
theorem R134129 : Reach 134129 := rs (se 2 (by rfl) ⟨50298, by rfl⟩) R100597
theorem R101363 : Reach 101363 := rs (se 1 (by rfl) ⟨76022, by rfl⟩) R152045
theorem R68595 : Reach 68595 := rs (se 1 (by rfl) ⟨51446, by rfl⟩) R102893
theorem R68611 : Reach 68611 := rs (se 1 (by rfl) ⟨51458, by rfl⟩) R102917
theorem R101393 : Reach 101393 := rs (se 2 (by rfl) ⟨38022, by rfl⟩) R76045
theorem R68627 : Reach 68627 := rs (se 1 (by rfl) ⟨51470, by rfl⟩) R102941
theorem R101411 : Reach 101411 := rs (se 1 (by rfl) ⟨76058, by rfl⟩) R152117
theorem R68643 : Reach 68643 := rs (se 1 (by rfl) ⟨51482, by rfl⟩) R102965
theorem R166961 : Reach 166961 := rs (se 2 (by rfl) ⟨62610, by rfl⟩) R125221
theorem R68659 : Reach 68659 := rs (se 1 (by rfl) ⟨51494, by rfl⟩) R102989
theorem R265265 : Reach 265265 := rs (se 2 (by rfl) ⟨99474, by rfl⟩) R198949
theorem R101441 : Reach 101441 := rs (se 2 (by rfl) ⟨38040, by rfl⟩) R76081
theorem R68675 : Reach 68675 := rs (se 1 (by rfl) ⟨51506, by rfl⟩) R103013
theorem R101459 : Reach 101459 := rs (se 1 (by rfl) ⟨76094, by rfl⟩) R152189
theorem R68691 : Reach 68691 := rs (se 1 (by rfl) ⟨51518, by rfl⟩) R103037
theorem R68707 : Reach 68707 := rs (se 1 (by rfl) ⟨51530, by rfl⟩) R103061
theorem R101489 : Reach 101489 := rs (se 2 (by rfl) ⟨38058, by rfl⟩) R76117
theorem R68723 : Reach 68723 := rs (se 1 (by rfl) ⟨51542, by rfl⟩) R103085
theorem R101507 : Reach 101507 := rs (se 1 (by rfl) ⟨76130, by rfl⟩) R152261
theorem R68739 : Reach 68739 := rs (se 1 (by rfl) ⟨51554, by rfl⟩) R103109
theorem R68755 : Reach 68755 := rs (se 1 (by rfl) ⟨51566, by rfl⟩) R103133
theorem R101537 : Reach 101537 := rs (se 2 (by rfl) ⟨38076, by rfl⟩) R76153
theorem R68771 : Reach 68771 := rs (se 1 (by rfl) ⟨51578, by rfl⟩) R103157
theorem R101555 : Reach 101555 := rs (se 1 (by rfl) ⟨76166, by rfl⟩) R152333
theorem R68787 : Reach 68787 := rs (se 1 (by rfl) ⟨51590, by rfl⟩) R103181
theorem R68803 : Reach 68803 := rs (se 1 (by rfl) ⟨51602, by rfl⟩) R103205
theorem R396485 : Reach 396485 := rs (se 4 (by rfl) ⟨37170, by rfl⟩) R74341
theorem R101585 : Reach 101585 := rs (se 2 (by rfl) ⟨38094, by rfl⟩) R76189
theorem R68819 : Reach 68819 := rs (se 1 (by rfl) ⟨51614, by rfl⟩) R103229
theorem R101603 : Reach 101603 := rs (se 1 (by rfl) ⟨76202, by rfl⟩) R152405
theorem R68835 : Reach 68835 := rs (se 1 (by rfl) ⟨51626, by rfl⟩) R103253
theorem R232685 : Reach 232685 := rs (se 3 (by rfl) ⟨43628, by rfl⟩) R87257
theorem R68851 : Reach 68851 := rs (se 1 (by rfl) ⟨51638, by rfl⟩) R103277
theorem R101633 : Reach 101633 := rs (se 2 (by rfl) ⟨38112, by rfl⟩) R76225
theorem R68867 : Reach 68867 := rs (se 1 (by rfl) ⟨51650, by rfl⟩) R103301
theorem R101651 : Reach 101651 := rs (se 1 (by rfl) ⟨76238, by rfl⟩) R152477
theorem R68883 : Reach 68883 := rs (se 1 (by rfl) ⟨51662, by rfl⟩) R103325
theorem R68899 : Reach 68899 := rs (se 1 (by rfl) ⟨51674, by rfl⟩) R103349
theorem R232739 : Reach 232739 := rs (se 1 (by rfl) ⟨174554, by rfl⟩) R349109
theorem R101681 : Reach 101681 := rs (se 2 (by rfl) ⟨38130, by rfl⟩) R76261
theorem R331057 : Reach 331057 := rs (se 2 (by rfl) ⟨124146, by rfl⟩) R248293
theorem R68915 : Reach 68915 := rs (se 1 (by rfl) ⟨51686, by rfl⟩) R103373
theorem R101699 : Reach 101699 := rs (se 1 (by rfl) ⟨76274, by rfl⟩) R152549
theorem R68931 : Reach 68931 := rs (se 1 (by rfl) ⟨51698, by rfl⟩) R103397
theorem R68947 : Reach 68947 := rs (se 1 (by rfl) ⟨51710, by rfl⟩) R103421
theorem R101729 : Reach 101729 := rs (se 2 (by rfl) ⟨38148, by rfl⟩) R76297
theorem R68963 : Reach 68963 := rs (se 1 (by rfl) ⟨51722, by rfl⟩) R103445
theorem R101747 : Reach 101747 := rs (se 1 (by rfl) ⟨76310, by rfl⟩) R152621
theorem R68979 : Reach 68979 := rs (se 1 (by rfl) ⟨51734, by rfl⟩) R103469
theorem R68995 : Reach 68995 := rs (se 1 (by rfl) ⟨51746, by rfl⟩) R103493
theorem R134531 : Reach 134531 := rs (se 1 (by rfl) ⟨100898, by rfl⟩) R201797
theorem R101777 : Reach 101777 := rs (se 2 (by rfl) ⟨38166, by rfl⟩) R76333
theorem R69011 : Reach 69011 := rs (se 1 (by rfl) ⟨51758, by rfl⟩) R103517
theorem R101795 : Reach 101795 := rs (se 1 (by rfl) ⟨76346, by rfl⟩) R152693
theorem R69027 : Reach 69027 := rs (se 1 (by rfl) ⟨51770, by rfl⟩) R103541
theorem R69043 : Reach 69043 := rs (se 1 (by rfl) ⟨51782, by rfl⟩) R103565
theorem R101825 : Reach 101825 := rs (se 2 (by rfl) ⟨38184, by rfl⟩) R76369
theorem R69059 : Reach 69059 := rs (se 1 (by rfl) ⟨51794, by rfl⟩) R103589
theorem R101843 : Reach 101843 := rs (se 1 (by rfl) ⟨76382, by rfl⟩) R152765
theorem R69075 : Reach 69075 := rs (se 1 (by rfl) ⟨51806, by rfl⟩) R103613
theorem R69091 : Reach 69091 := rs (se 1 (by rfl) ⟨51818, by rfl⟩) R103637
theorem R101873 : Reach 101873 := rs (se 2 (by rfl) ⟨38202, by rfl⟩) R76405
theorem R69107 : Reach 69107 := rs (se 1 (by rfl) ⟨51830, by rfl⟩) R103661
theorem R101891 : Reach 101891 := rs (se 1 (by rfl) ⟨76418, by rfl⟩) R152837
theorem R69123 : Reach 69123 := rs (se 1 (by rfl) ⟨51842, by rfl⟩) R103685
theorem R69139 : Reach 69139 := rs (se 1 (by rfl) ⟨51854, by rfl⟩) R103709
theorem R101921 : Reach 101921 := rs (se 2 (by rfl) ⟨38220, by rfl⟩) R76441
theorem R69155 : Reach 69155 := rs (se 1 (by rfl) ⟨51866, by rfl⟩) R103733
theorem R233009 : Reach 233009 := rs (se 2 (by rfl) ⟨87378, by rfl⟩) R174757
theorem R101939 : Reach 101939 := rs (se 1 (by rfl) ⟨76454, by rfl⟩) R152909
theorem R69171 : Reach 69171 := rs (se 1 (by rfl) ⟨51878, by rfl⟩) R103757
theorem R69187 : Reach 69187 := rs (se 1 (by rfl) ⟨51890, by rfl⟩) R103781
theorem R101969 : Reach 101969 := rs (se 2 (by rfl) ⟨38238, by rfl⟩) R76477
theorem R69203 : Reach 69203 := rs (se 1 (by rfl) ⟨51902, by rfl⟩) R103805
theorem R101987 : Reach 101987 := rs (se 1 (by rfl) ⟨76490, by rfl⟩) R152981
theorem R69219 : Reach 69219 := rs (se 1 (by rfl) ⟨51914, by rfl⟩) R103829
theorem R69235 : Reach 69235 := rs (se 1 (by rfl) ⟨51926, by rfl⟩) R103853
theorem R102017 : Reach 102017 := rs (se 2 (by rfl) ⟨38256, by rfl⟩) R76513
theorem R69251 : Reach 69251 := rs (se 1 (by rfl) ⟨51938, by rfl⟩) R103877
theorem R102035 : Reach 102035 := rs (se 1 (by rfl) ⟨76526, by rfl⟩) R153053
theorem R69267 : Reach 69267 := rs (se 1 (by rfl) ⟨51950, by rfl⟩) R103901
theorem R69283 : Reach 69283 := rs (se 1 (by rfl) ⟨51962, by rfl⟩) R103925
theorem R102065 : Reach 102065 := rs (se 2 (by rfl) ⟨38274, by rfl⟩) R76549
theorem R69299 : Reach 69299 := rs (se 1 (by rfl) ⟨51974, by rfl⟩) R103949
theorem R102083 : Reach 102083 := rs (se 1 (by rfl) ⟨76562, by rfl⟩) R153125
theorem R69315 : Reach 69315 := rs (se 1 (by rfl) ⟨51986, by rfl⟩) R103973
theorem R69331 : Reach 69331 := rs (se 1 (by rfl) ⟨51998, by rfl⟩) R103997
theorem R102113 : Reach 102113 := rs (se 2 (by rfl) ⟨38292, by rfl⟩) R76585
theorem R69347 : Reach 69347 := rs (se 1 (by rfl) ⟨52010, by rfl⟩) R104021
theorem R102131 : Reach 102131 := rs (se 1 (by rfl) ⟨76598, by rfl⟩) R153197
theorem R69363 : Reach 69363 := rs (se 1 (by rfl) ⟨52022, by rfl⟩) R104045
theorem R69379 : Reach 69379 := rs (se 1 (by rfl) ⟨52034, by rfl⟩) R104069
theorem R102161 : Reach 102161 := rs (se 2 (by rfl) ⟨38310, by rfl⟩) R76621
theorem R69395 : Reach 69395 := rs (se 1 (by rfl) ⟨52046, by rfl⟩) R104093
theorem R200465 : Reach 200465 := rs (se 2 (by rfl) ⟨75174, by rfl⟩) R150349
theorem R102179 : Reach 102179 := rs (se 1 (by rfl) ⟨76634, by rfl⟩) R153269
theorem R69411 : Reach 69411 := rs (se 1 (by rfl) ⟨52058, by rfl⟩) R104117
theorem R69427 : Reach 69427 := rs (se 1 (by rfl) ⟨52070, by rfl⟩) R104141
theorem R102209 : Reach 102209 := rs (se 2 (by rfl) ⟨38328, by rfl⟩) R76657
theorem R69443 : Reach 69443 := rs (se 1 (by rfl) ⟨52082, by rfl⟩) R104165
theorem R102227 : Reach 102227 := rs (se 1 (by rfl) ⟨76670, by rfl⟩) R153341
theorem R69459 : Reach 69459 := rs (se 1 (by rfl) ⟨52094, by rfl⟩) R104189
theorem R69475 : Reach 69475 := rs (se 1 (by rfl) ⟨52106, by rfl⟩) R104213
theorem R102257 : Reach 102257 := rs (se 2 (by rfl) ⟨38346, by rfl⟩) R76693
theorem R69491 : Reach 69491 := rs (se 1 (by rfl) ⟨52118, by rfl⟩) R104237
theorem R397169 : Reach 397169 := rs (se 2 (by rfl) ⟨148938, by rfl⟩) R297877
theorem R102275 : Reach 102275 := rs (se 1 (by rfl) ⟨76706, by rfl⟩) R153413
theorem R69507 : Reach 69507 := rs (se 1 (by rfl) ⟨52130, by rfl⟩) R104261
theorem R69523 : Reach 69523 := rs (se 1 (by rfl) ⟨52142, by rfl⟩) R104285
theorem R102305 : Reach 102305 := rs (se 2 (by rfl) ⟨38364, by rfl⟩) R76729
theorem R69539 : Reach 69539 := rs (se 1 (by rfl) ⟨52154, by rfl⟩) R104309
theorem R102323 : Reach 102323 := rs (se 1 (by rfl) ⟨76742, by rfl⟩) R153485
theorem R69555 : Reach 69555 := rs (se 1 (by rfl) ⟨52166, by rfl⟩) R104333
theorem R69571 : Reach 69571 := rs (se 1 (by rfl) ⟨52178, by rfl⟩) R104357
theorem R102353 : Reach 102353 := rs (se 2 (by rfl) ⟨38382, by rfl⟩) R76765
theorem R69587 : Reach 69587 := rs (se 1 (by rfl) ⟨52190, by rfl⟩) R104381
theorem R200657 : Reach 200657 := rs (se 2 (by rfl) ⟨75246, by rfl⟩) R150493
theorem R102371 : Reach 102371 := rs (se 1 (by rfl) ⟨76778, by rfl⟩) R153557
theorem R69603 : Reach 69603 := rs (se 1 (by rfl) ⟨52202, by rfl⟩) R104405
theorem R167921 : Reach 167921 := rs (se 2 (by rfl) ⟨62970, by rfl⟩) R125941
theorem R69619 : Reach 69619 := rs (se 1 (by rfl) ⟨52214, by rfl⟩) R104429
theorem R102401 : Reach 102401 := rs (se 2 (by rfl) ⟨38400, by rfl⟩) R76801
theorem R69635 : Reach 69635 := rs (se 1 (by rfl) ⟨52226, by rfl⟩) R104453
theorem R102419 : Reach 102419 := rs (se 1 (by rfl) ⟨76814, by rfl⟩) R153629
theorem R69651 : Reach 69651 := rs (se 1 (by rfl) ⟨52238, by rfl⟩) R104477
theorem R69667 : Reach 69667 := rs (se 1 (by rfl) ⟨52250, by rfl⟩) R104501
theorem R102449 : Reach 102449 := rs (se 2 (by rfl) ⟨38418, by rfl⟩) R76837
theorem R69683 : Reach 69683 := rs (se 1 (by rfl) ⟨52262, by rfl⟩) R104525
theorem R102467 : Reach 102467 := rs (se 1 (by rfl) ⟨76850, by rfl⟩) R153701
theorem R69699 : Reach 69699 := rs (se 1 (by rfl) ⟨52274, by rfl⟩) R104549
theorem R233549 : Reach 233549 := rs (se 3 (by rfl) ⟨43790, by rfl⟩) R87581
theorem R69715 : Reach 69715 := rs (se 1 (by rfl) ⟨52286, by rfl⟩) R104573
theorem R102497 : Reach 102497 := rs (se 2 (by rfl) ⟨38436, by rfl⟩) R76873
theorem R69731 : Reach 69731 := rs (se 1 (by rfl) ⟨52298, by rfl⟩) R104597
theorem R102515 : Reach 102515 := rs (se 1 (by rfl) ⟨76886, by rfl⟩) R153773
theorem R69747 : Reach 69747 := rs (se 1 (by rfl) ⟨52310, by rfl⟩) R104621
theorem R233603 : Reach 233603 := rs (se 1 (by rfl) ⟨175202, by rfl⟩) R350405
theorem R69763 : Reach 69763 := rs (se 1 (by rfl) ⟨52322, by rfl⟩) R104645
theorem R102545 : Reach 102545 := rs (se 2 (by rfl) ⟨38454, by rfl⟩) R76909
theorem R69779 : Reach 69779 := rs (se 1 (by rfl) ⟨52334, by rfl⟩) R104669
theorem R102563 : Reach 102563 := rs (se 1 (by rfl) ⟨76922, by rfl⟩) R153845
theorem R69795 : Reach 69795 := rs (se 1 (by rfl) ⟨52346, by rfl⟩) R104693
theorem R69811 : Reach 69811 := rs (se 1 (by rfl) ⟨52358, by rfl⟩) R104717
theorem R102593 : Reach 102593 := rs (se 2 (by rfl) ⟨38472, by rfl⟩) R76945
theorem R69827 : Reach 69827 := rs (se 1 (by rfl) ⟨52370, by rfl⟩) R104741
theorem R430285 : Reach 430285 := rs (se 3 (by rfl) ⟨80678, by rfl⟩) R161357
theorem R102611 : Reach 102611 := rs (se 1 (by rfl) ⟨76958, by rfl⟩) R153917
theorem R69843 : Reach 69843 := rs (se 1 (by rfl) ⟨52382, by rfl⟩) R104765
theorem R69859 : Reach 69859 := rs (se 1 (by rfl) ⟨52394, by rfl⟩) R104789
theorem R102641 : Reach 102641 := rs (se 2 (by rfl) ⟨38490, by rfl⟩) R76981
theorem R69875 : Reach 69875 := rs (se 1 (by rfl) ⟨52406, by rfl⟩) R104813
theorem R102659 : Reach 102659 := rs (se 1 (by rfl) ⟨76994, by rfl⟩) R153989
theorem R69891 : Reach 69891 := rs (se 1 (by rfl) ⟨52418, by rfl⟩) R104837
theorem R69907 : Reach 69907 := rs (se 1 (by rfl) ⟨52430, by rfl⟩) R104861
theorem R102689 : Reach 102689 := rs (se 2 (by rfl) ⟨38508, by rfl⟩) R77017
theorem R69923 : Reach 69923 := rs (se 1 (by rfl) ⟨52442, by rfl⟩) R104885
theorem R102707 : Reach 102707 := rs (se 1 (by rfl) ⟨77030, by rfl⟩) R154061
theorem R69939 : Reach 69939 := rs (se 1 (by rfl) ⟨52454, by rfl⟩) R104909
theorem R758069 : Reach 758069 := rs (se 5 (by rfl) ⟨35534, by rfl⟩) R71069
theorem R69955 : Reach 69955 := rs (se 1 (by rfl) ⟨52466, by rfl⟩) R104933
theorem R364877 : Reach 364877 := rs (se 3 (by rfl) ⟨68414, by rfl⟩) R136829
theorem R102737 : Reach 102737 := rs (se 2 (by rfl) ⟨38526, by rfl⟩) R77053
theorem R69971 : Reach 69971 := rs (se 1 (by rfl) ⟨52478, by rfl⟩) R104957
theorem R102755 : Reach 102755 := rs (se 1 (by rfl) ⟨77066, by rfl⟩) R154133
theorem R69987 : Reach 69987 := rs (se 1 (by rfl) ⟨52490, by rfl⟩) R104981
theorem R70003 : Reach 70003 := rs (se 1 (by rfl) ⟨52502, by rfl⟩) R105005
theorem R102785 : Reach 102785 := rs (se 2 (by rfl) ⟨38544, by rfl⟩) R77089
theorem R70019 : Reach 70019 := rs (se 1 (by rfl) ⟨52514, by rfl⟩) R105029
theorem R594317 : Reach 594317 := rs (se 3 (by rfl) ⟨111434, by rfl⟩) R222869
theorem R233873 : Reach 233873 := rs (se 2 (by rfl) ⟨87702, by rfl⟩) R175405
theorem R102803 : Reach 102803 := rs (se 1 (by rfl) ⟨77102, by rfl⟩) R154205
theorem R70035 : Reach 70035 := rs (se 1 (by rfl) ⟨52526, by rfl⟩) R105053
theorem R70051 : Reach 70051 := rs (se 1 (by rfl) ⟨52538, by rfl⟩) R105077
theorem R102833 : Reach 102833 := rs (se 2 (by rfl) ⟨38562, by rfl⟩) R77125
theorem R70067 : Reach 70067 := rs (se 1 (by rfl) ⟨52550, by rfl⟩) R105101
theorem R102851 : Reach 102851 := rs (se 1 (by rfl) ⟨77138, by rfl⟩) R154277
theorem R70083 : Reach 70083 := rs (se 1 (by rfl) ⟨52562, by rfl⟩) R105125
theorem R233933 : Reach 233933 := rs (se 3 (by rfl) ⟨43862, by rfl⟩) R87725
theorem R70099 : Reach 70099 := rs (se 1 (by rfl) ⟨52574, by rfl⟩) R105149
theorem R102881 : Reach 102881 := rs (se 2 (by rfl) ⟨38580, by rfl⟩) R77161
theorem R70115 : Reach 70115 := rs (se 1 (by rfl) ⟨52586, by rfl⟩) R105173
theorem R266723 : Reach 266723 := rs (se 1 (by rfl) ⟨200042, by rfl⟩) R400085
theorem R102899 : Reach 102899 := rs (se 1 (by rfl) ⟨77174, by rfl⟩) R154349
theorem R70131 : Reach 70131 := rs (se 1 (by rfl) ⟨52598, by rfl⟩) R105197
theorem R70147 : Reach 70147 := rs (se 1 (by rfl) ⟨52610, by rfl⟩) R105221
theorem R102929 : Reach 102929 := rs (se 2 (by rfl) ⟨38598, by rfl⟩) R77197
theorem R70163 : Reach 70163 := rs (se 1 (by rfl) ⟨52622, by rfl⟩) R105245
theorem R102947 : Reach 102947 := rs (se 1 (by rfl) ⟨77210, by rfl⟩) R154421
theorem R70179 : Reach 70179 := rs (se 1 (by rfl) ⟨52634, by rfl⟩) R105269
theorem R70195 : Reach 70195 := rs (se 1 (by rfl) ⟨52646, by rfl⟩) R105293
theorem R102977 : Reach 102977 := rs (se 2 (by rfl) ⟨38616, by rfl⟩) R77233
theorem R70211 : Reach 70211 := rs (se 1 (by rfl) ⟨52658, by rfl⟩) R105317
theorem R102995 : Reach 102995 := rs (se 1 (by rfl) ⟨77246, by rfl⟩) R154493
theorem R70227 : Reach 70227 := rs (se 1 (by rfl) ⟨52670, by rfl⟩) R105341
theorem R70243 : Reach 70243 := rs (se 1 (by rfl) ⟨52682, by rfl⟩) R105365
theorem R103025 : Reach 103025 := rs (se 2 (by rfl) ⟨38634, by rfl⟩) R77269
theorem R70259 : Reach 70259 := rs (se 1 (by rfl) ⟨52694, by rfl⟩) R105389
theorem R103043 : Reach 103043 := rs (se 1 (by rfl) ⟨77282, by rfl⟩) R154565
theorem R70275 : Reach 70275 := rs (se 1 (by rfl) ⟨52706, by rfl⟩) R105413
theorem R70291 : Reach 70291 := rs (se 1 (by rfl) ⟨52718, by rfl⟩) R105437
theorem R103073 : Reach 103073 := rs (se 2 (by rfl) ⟨38652, by rfl⟩) R77305
theorem R70307 : Reach 70307 := rs (se 1 (by rfl) ⟨52730, by rfl⟩) R105461
theorem R103091 : Reach 103091 := rs (se 1 (by rfl) ⟨77318, by rfl⟩) R154637
theorem R70323 : Reach 70323 := rs (se 1 (by rfl) ⟨52742, by rfl⟩) R105485
theorem R70339 : Reach 70339 := rs (se 1 (by rfl) ⟨52754, by rfl⟩) R105509
theorem R103121 : Reach 103121 := rs (se 2 (by rfl) ⟨38670, by rfl⟩) R77341
theorem R70355 : Reach 70355 := rs (se 1 (by rfl) ⟨52766, by rfl⟩) R105533
theorem R103139 : Reach 103139 := rs (se 1 (by rfl) ⟨77354, by rfl⟩) R154709
theorem R70371 : Reach 70371 := rs (se 1 (by rfl) ⟨52778, by rfl⟩) R105557
theorem R201457 : Reach 201457 := rs (se 2 (by rfl) ⟨75546, by rfl⟩) R151093
theorem R70387 : Reach 70387 := rs (se 1 (by rfl) ⟨52790, by rfl⟩) R105581
theorem R103169 : Reach 103169 := rs (se 2 (by rfl) ⟨38688, by rfl⟩) R77377
theorem R70403 : Reach 70403 := rs (se 1 (by rfl) ⟨52802, by rfl⟩) R105605
theorem R103187 : Reach 103187 := rs (se 1 (by rfl) ⟨77390, by rfl⟩) R154781
theorem R70419 : Reach 70419 := rs (se 1 (by rfl) ⟨52814, by rfl⟩) R105629
theorem R2036501 : Reach 2036501 := rs (se 6 (by rfl) ⟨47730, by rfl⟩) R95461
theorem R70435 : Reach 70435 := rs (se 1 (by rfl) ⟨52826, by rfl⟩) R105653
theorem R103217 : Reach 103217 := rs (se 2 (by rfl) ⟨38706, by rfl⟩) R77413
theorem R299825 : Reach 299825 := rs (se 2 (by rfl) ⟨112434, by rfl⟩) R224869
theorem R70451 : Reach 70451 := rs (se 1 (by rfl) ⟨52838, by rfl⟩) R105677
theorem R103235 : Reach 103235 := rs (se 1 (by rfl) ⟨77426, by rfl⟩) R154853
theorem R70467 : Reach 70467 := rs (se 1 (by rfl) ⟨52850, by rfl⟩) R105701
theorem R70483 : Reach 70483 := rs (se 1 (by rfl) ⟨52862, by rfl⟩) R105725
theorem R103265 : Reach 103265 := rs (se 2 (by rfl) ⟨38724, by rfl⟩) R77449
theorem R70499 : Reach 70499 := rs (se 1 (by rfl) ⟨52874, by rfl⟩) R105749
theorem R103283 : Reach 103283 := rs (se 1 (by rfl) ⟨77462, by rfl⟩) R154925
theorem R70515 : Reach 70515 := rs (se 1 (by rfl) ⟨52886, by rfl⟩) R105773
theorem R70531 : Reach 70531 := rs (se 1 (by rfl) ⟨52898, by rfl⟩) R105797
theorem R103313 : Reach 103313 := rs (se 2 (by rfl) ⟨38742, by rfl⟩) R77485
theorem R70547 : Reach 70547 := rs (se 1 (by rfl) ⟨52910, by rfl⟩) R105821
theorem R103331 : Reach 103331 := rs (se 1 (by rfl) ⟨77498, by rfl⟩) R154997
theorem R70563 : Reach 70563 := rs (se 1 (by rfl) ⟨52922, by rfl⟩) R105845
theorem R234413 : Reach 234413 := rs (se 3 (by rfl) ⟨43952, by rfl⟩) R87905
theorem R201649 : Reach 201649 := rs (se 2 (by rfl) ⟨75618, by rfl⟩) R151237
theorem R70579 : Reach 70579 := rs (se 1 (by rfl) ⟨52934, by rfl⟩) R105869
theorem R103361 : Reach 103361 := rs (se 2 (by rfl) ⟨38760, by rfl⟩) R77521
theorem R70595 : Reach 70595 := rs (se 1 (by rfl) ⟨52946, by rfl⟩) R105893
theorem R103379 : Reach 103379 := rs (se 1 (by rfl) ⟨77534, by rfl⟩) R155069
theorem R70611 : Reach 70611 := rs (se 1 (by rfl) ⟨52958, by rfl⟩) R105917
theorem R103393 : Reach 103393 := rs (se 2 (by rfl) ⟨38772, by rfl⟩) R77545
theorem R234467 : Reach 234467 := rs (se 1 (by rfl) ⟨175850, by rfl⟩) R351701
theorem R70627 : Reach 70627 := rs (se 1 (by rfl) ⟨52970, by rfl⟩) R105941
theorem R103409 : Reach 103409 := rs (se 2 (by rfl) ⟨38778, by rfl⟩) R77557
theorem R70643 : Reach 70643 := rs (se 1 (by rfl) ⟨52982, by rfl⟩) R105965
theorem R103427 : Reach 103427 := rs (se 1 (by rfl) ⟨77570, by rfl⟩) R155141
theorem R70659 : Reach 70659 := rs (se 1 (by rfl) ⟨52994, by rfl⟩) R105989
theorem R70675 : Reach 70675 := rs (se 1 (by rfl) ⟨53006, by rfl⟩) R106013
theorem R103457 : Reach 103457 := rs (se 2 (by rfl) ⟨38796, by rfl⟩) R77593
theorem R70691 : Reach 70691 := rs (se 1 (by rfl) ⟨53018, by rfl⟩) R106037
theorem R103475 : Reach 103475 := rs (se 1 (by rfl) ⟨77606, by rfl⟩) R155213
theorem R70707 : Reach 70707 := rs (se 1 (by rfl) ⟨53030, by rfl⟩) R106061
theorem R70723 : Reach 70723 := rs (se 1 (by rfl) ⟨53042, by rfl⟩) R106085
theorem R103505 : Reach 103505 := rs (se 2 (by rfl) ⟨38814, by rfl⟩) R77629
theorem R70739 : Reach 70739 := rs (se 1 (by rfl) ⟨53054, by rfl⟩) R106109
theorem R103523 : Reach 103523 := rs (se 1 (by rfl) ⟨77642, by rfl⟩) R155285
theorem R70755 : Reach 70755 := rs (se 1 (by rfl) ⟨53066, by rfl⟩) R106133
theorem R70771 : Reach 70771 := rs (se 1 (by rfl) ⟨53078, by rfl⟩) R106157
theorem R103553 : Reach 103553 := rs (se 2 (by rfl) ⟨38832, by rfl⟩) R77665
theorem R70787 : Reach 70787 := rs (se 1 (by rfl) ⟨53090, by rfl⟩) R106181
theorem R791693 : Reach 791693 := rs (se 3 (by rfl) ⟨148442, by rfl⟩) R296885
theorem R103571 : Reach 103571 := rs (se 1 (by rfl) ⟨77678, by rfl⟩) R155357
theorem R70803 : Reach 70803 := rs (se 1 (by rfl) ⟨53102, by rfl⟩) R106205
theorem R234659 : Reach 234659 := rs (se 1 (by rfl) ⟨175994, by rfl⟩) R351989
theorem R70819 : Reach 70819 := rs (se 1 (by rfl) ⟨53114, by rfl⟩) R106229
theorem R103601 : Reach 103601 := rs (se 2 (by rfl) ⟨38850, by rfl⟩) R77701
theorem R70835 : Reach 70835 := rs (se 1 (by rfl) ⟨53126, by rfl⟩) R106253
theorem R103619 : Reach 103619 := rs (se 1 (by rfl) ⟨77714, by rfl⟩) R155429
theorem R70851 : Reach 70851 := rs (se 1 (by rfl) ⟨53138, by rfl⟩) R106277
theorem R201923 : Reach 201923 := rs (se 1 (by rfl) ⟨151442, by rfl⟩) R302885
theorem R70867 : Reach 70867 := rs (se 1 (by rfl) ⟨53150, by rfl⟩) R106301
theorem R103649 : Reach 103649 := rs (se 2 (by rfl) ⟨38868, by rfl⟩) R77737
theorem R70883 : Reach 70883 := rs (se 1 (by rfl) ⟨53162, by rfl⟩) R106325
theorem R234737 : Reach 234737 := rs (se 2 (by rfl) ⟨88026, by rfl⟩) R176053
theorem R103667 : Reach 103667 := rs (se 1 (by rfl) ⟨77750, by rfl⟩) R155501
theorem R70899 : Reach 70899 := rs (se 1 (by rfl) ⟨53174, by rfl⟩) R106349
theorem R169219 : Reach 169219 := rs (se 1 (by rfl) ⟨126914, by rfl⟩) R253829
theorem R70915 : Reach 70915 := rs (se 1 (by rfl) ⟨53186, by rfl⟩) R106373
theorem R103697 : Reach 103697 := rs (se 2 (by rfl) ⟨38886, by rfl⟩) R77773
theorem R70931 : Reach 70931 := rs (se 1 (by rfl) ⟨53198, by rfl⟩) R106397
theorem R103715 : Reach 103715 := rs (se 1 (by rfl) ⟨77786, by rfl⟩) R155573
theorem R398627 : Reach 398627 := rs (se 1 (by rfl) ⟨298970, by rfl⟩) R597941
theorem R70947 : Reach 70947 := rs (se 1 (by rfl) ⟨53210, by rfl⟩) R106421
theorem R70963 : Reach 70963 := rs (se 1 (by rfl) ⟨53222, by rfl⟩) R106445
theorem R103745 : Reach 103745 := rs (se 2 (by rfl) ⟨38904, by rfl⟩) R77809
theorem R70979 : Reach 70979 := rs (se 1 (by rfl) ⟨53234, by rfl⟩) R106469
theorem R103763 : Reach 103763 := rs (se 1 (by rfl) ⟨77822, by rfl⟩) R155645
theorem R70995 : Reach 70995 := rs (se 1 (by rfl) ⟨53246, by rfl⟩) R106493
theorem R71011 : Reach 71011 := rs (se 1 (by rfl) ⟨53258, by rfl⟩) R106517
theorem R103793 : Reach 103793 := rs (se 2 (by rfl) ⟨38922, by rfl⟩) R77845
theorem R71027 : Reach 71027 := rs (se 1 (by rfl) ⟨53270, by rfl⟩) R106541
theorem R103811 : Reach 103811 := rs (se 1 (by rfl) ⟨77858, by rfl⟩) R155717
theorem R202115 : Reach 202115 := rs (se 1 (by rfl) ⟨151586, by rfl⟩) R303173
theorem R71043 : Reach 71043 := rs (se 1 (by rfl) ⟨53282, by rfl⟩) R106565
theorem R71059 : Reach 71059 := rs (se 1 (by rfl) ⟨53294, by rfl⟩) R106589
theorem R103841 : Reach 103841 := rs (se 2 (by rfl) ⟨38940, by rfl⟩) R77881
theorem R71075 : Reach 71075 := rs (se 1 (by rfl) ⟨53306, by rfl⟩) R106613
theorem R103859 : Reach 103859 := rs (se 1 (by rfl) ⟨77894, by rfl⟩) R155789
theorem R71091 : Reach 71091 := rs (se 1 (by rfl) ⟨53318, by rfl⟩) R106637
theorem R71107 : Reach 71107 := rs (se 1 (by rfl) ⟨53330, by rfl⟩) R106661
theorem R267725 : Reach 267725 := rs (se 3 (by rfl) ⟨50198, by rfl⟩) R100397
theorem R103889 : Reach 103889 := rs (se 2 (by rfl) ⟨38958, by rfl⟩) R77917
theorem R71123 : Reach 71123 := rs (se 1 (by rfl) ⟨53342, by rfl⟩) R106685
theorem R103907 : Reach 103907 := rs (se 1 (by rfl) ⟨77930, by rfl⟩) R155861
theorem R103937 : Reach 103937 := rs (se 2 (by rfl) ⟨38976, by rfl⟩) R77953
theorem R103955 : Reach 103955 := rs (se 1 (by rfl) ⟨77966, by rfl⟩) R155933
theorem R103985 : Reach 103985 := rs (se 2 (by rfl) ⟨38994, by rfl⟩) R77989
theorem R104003 : Reach 104003 := rs (se 1 (by rfl) ⟨78002, by rfl⟩) R156005
theorem R104033 : Reach 104033 := rs (se 2 (by rfl) ⟨39012, by rfl⟩) R78025
theorem R104051 : Reach 104051 := rs (se 1 (by rfl) ⟨78038, by rfl⟩) R156077
theorem R104081 : Reach 104081 := rs (se 2 (by rfl) ⟨39030, by rfl⟩) R78061
theorem R104099 : Reach 104099 := rs (se 1 (by rfl) ⟨78074, by rfl⟩) R156149
theorem R104129 : Reach 104129 := rs (se 2 (by rfl) ⟨39048, by rfl⟩) R78097
theorem R366277 : Reach 366277 := rs (se 4 (by rfl) ⟨34338, by rfl⟩) R68677
theorem R104147 : Reach 104147 := rs (se 1 (by rfl) ⟨78110, by rfl⟩) R156221
theorem R104177 : Reach 104177 := rs (se 2 (by rfl) ⟨39066, by rfl⟩) R78133
theorem R104195 : Reach 104195 := rs (se 1 (by rfl) ⟨78146, by rfl⟩) R156293
theorem R235277 : Reach 235277 := rs (se 3 (by rfl) ⟨44114, by rfl⟩) R88229
theorem R104225 : Reach 104225 := rs (se 2 (by rfl) ⟨39084, by rfl⟩) R78169
theorem R104243 : Reach 104243 := rs (se 1 (by rfl) ⟨78182, by rfl⟩) R156365
theorem R235331 : Reach 235331 := rs (se 1 (by rfl) ⟨176498, by rfl⟩) R352997
theorem R104273 : Reach 104273 := rs (se 2 (by rfl) ⟨39102, by rfl⟩) R78205
theorem R104291 : Reach 104291 := rs (se 1 (by rfl) ⟨78218, by rfl⟩) R156437
theorem R104321 : Reach 104321 := rs (se 2 (by rfl) ⟨39120, by rfl⟩) R78241
theorem R104339 : Reach 104339 := rs (se 1 (by rfl) ⟨78254, by rfl⟩) R156509
theorem R104369 : Reach 104369 := rs (se 2 (by rfl) ⟨39138, by rfl⟩) R78277
theorem R104387 : Reach 104387 := rs (se 1 (by rfl) ⟨78290, by rfl⟩) R156581
theorem R104417 : Reach 104417 := rs (se 2 (by rfl) ⟨39156, by rfl⟩) R78313
theorem R104435 : Reach 104435 := rs (se 1 (by rfl) ⟨78326, by rfl⟩) R156653
theorem R104465 : Reach 104465 := rs (se 2 (by rfl) ⟨39174, by rfl⟩) R78349
theorem R104483 : Reach 104483 := rs (se 1 (by rfl) ⟨78362, by rfl⟩) R156725
theorem R104513 : Reach 104513 := rs (se 2 (by rfl) ⟨39192, by rfl⟩) R78385
theorem R235601 : Reach 235601 := rs (se 2 (by rfl) ⟨88350, by rfl⟩) R176701
theorem R104531 : Reach 104531 := rs (se 1 (by rfl) ⟨78398, by rfl⟩) R156797
theorem R104561 : Reach 104561 := rs (se 2 (by rfl) ⟨39210, by rfl⟩) R78421
theorem R104579 : Reach 104579 := rs (se 1 (by rfl) ⟨78434, by rfl⟩) R156869
theorem R104609 : Reach 104609 := rs (se 2 (by rfl) ⟨39228, by rfl⟩) R78457
theorem R104627 : Reach 104627 := rs (se 1 (by rfl) ⟨78470, by rfl⟩) R156941
theorem R104657 : Reach 104657 := rs (se 2 (by rfl) ⟨39246, by rfl⟩) R78493
theorem R104675 : Reach 104675 := rs (se 1 (by rfl) ⟨78506, by rfl⟩) R157013
theorem R104705 : Reach 104705 := rs (se 2 (by rfl) ⟨39264, by rfl⟩) R78529
theorem R104723 : Reach 104723 := rs (se 1 (by rfl) ⟨78542, by rfl⟩) R157085
theorem R104753 : Reach 104753 := rs (se 2 (by rfl) ⟨39282, by rfl⟩) R78565
theorem R104771 : Reach 104771 := rs (se 1 (by rfl) ⟨78578, by rfl⟩) R157157
theorem R104801 : Reach 104801 := rs (se 2 (by rfl) ⟨39300, by rfl⟩) R78601
theorem R104819 : Reach 104819 := rs (se 1 (by rfl) ⟨78614, by rfl⟩) R157229
theorem R104849 : Reach 104849 := rs (se 2 (by rfl) ⟨39318, by rfl⟩) R78637
theorem R104867 : Reach 104867 := rs (se 1 (by rfl) ⟨78650, by rfl⟩) R157301
theorem R104897 : Reach 104897 := rs (se 2 (by rfl) ⟨39336, by rfl⟩) R78673
theorem R104915 : Reach 104915 := rs (se 1 (by rfl) ⟨78686, by rfl⟩) R157373
theorem R104945 : Reach 104945 := rs (se 2 (by rfl) ⟨39354, by rfl⟩) R78709
theorem R104963 : Reach 104963 := rs (se 1 (by rfl) ⟨78722, by rfl⟩) R157445
theorem R104993 : Reach 104993 := rs (se 2 (by rfl) ⟨39372, by rfl⟩) R78745
theorem R170545 : Reach 170545 := rs (se 2 (by rfl) ⟨63954, by rfl⟩) R127909
theorem R105011 : Reach 105011 := rs (se 1 (by rfl) ⟨78758, by rfl⟩) R157517
theorem R105041 : Reach 105041 := rs (se 2 (by rfl) ⟨39390, by rfl⟩) R78781
theorem R105059 : Reach 105059 := rs (se 1 (by rfl) ⟨78794, by rfl⟩) R157589
theorem R236141 : Reach 236141 := rs (se 3 (by rfl) ⟨44276, by rfl⟩) R88553
theorem R105089 : Reach 105089 := rs (se 2 (by rfl) ⟨39408, by rfl⟩) R78817
theorem R105107 : Reach 105107 := rs (se 1 (by rfl) ⟨78830, by rfl⟩) R157661
theorem R236195 : Reach 236195 := rs (se 1 (by rfl) ⟨177146, by rfl⟩) R354293
theorem R105137 : Reach 105137 := rs (se 2 (by rfl) ⟨39426, by rfl⟩) R78853
theorem R105155 : Reach 105155 := rs (se 1 (by rfl) ⟨78866, by rfl⟩) R157733
theorem R105185 : Reach 105185 := rs (se 2 (by rfl) ⟨39444, by rfl⟩) R78889
theorem R72419 : Reach 72419 := rs (se 1 (by rfl) ⟨54314, by rfl⟩) R108629
theorem R105203 : Reach 105203 := rs (se 1 (by rfl) ⟨78902, by rfl⟩) R157805
theorem R105233 : Reach 105233 := rs (se 2 (by rfl) ⟨39462, by rfl⟩) R78925
theorem R138019 : Reach 138019 := rs (se 1 (by rfl) ⟨103514, by rfl⟩) R207029
theorem R105251 : Reach 105251 := rs (se 1 (by rfl) ⟨78938, by rfl⟩) R157877
theorem R105281 : Reach 105281 := rs (se 2 (by rfl) ⟨39480, by rfl⟩) R78961
theorem R170819 : Reach 170819 := rs (se 1 (by rfl) ⟨128114, by rfl⟩) R256229
theorem R105299 : Reach 105299 := rs (se 1 (by rfl) ⟨78974, by rfl⟩) R157949
theorem R465763 : Reach 465763 := rs (se 1 (by rfl) ⟨349322, by rfl⟩) R698645
theorem R105329 : Reach 105329 := rs (se 2 (by rfl) ⟨39498, by rfl⟩) R78997
theorem R105347 : Reach 105347 := rs (se 1 (by rfl) ⟨79010, by rfl⟩) R158021
theorem R105377 : Reach 105377 := rs (se 2 (by rfl) ⟨39516, by rfl⟩) R79033
theorem R236465 : Reach 236465 := rs (se 2 (by rfl) ⟨88674, by rfl⟩) R177349
theorem R105395 : Reach 105395 := rs (se 1 (by rfl) ⟨79046, by rfl⟩) R158093
theorem R105425 : Reach 105425 := rs (se 2 (by rfl) ⟨39534, by rfl⟩) R79069
theorem R105443 : Reach 105443 := rs (se 1 (by rfl) ⟨79082, by rfl⟩) R158165
theorem R105473 : Reach 105473 := rs (se 2 (by rfl) ⟨39552, by rfl⟩) R79105
theorem R171011 : Reach 171011 := rs (se 1 (by rfl) ⟨128258, by rfl⟩) R256517
theorem R105491 : Reach 105491 := rs (se 1 (by rfl) ⟨79118, by rfl⟩) R158237
theorem R105521 : Reach 105521 := rs (se 2 (by rfl) ⟨39570, by rfl⟩) R79141
theorem R105539 : Reach 105539 := rs (se 1 (by rfl) ⟨79154, by rfl⟩) R158309
theorem R105569 : Reach 105569 := rs (se 2 (by rfl) ⟨39588, by rfl⟩) R79177
theorem R334961 : Reach 334961 := rs (se 2 (by rfl) ⟨125610, by rfl⟩) R251221
theorem R105587 : Reach 105587 := rs (se 1 (by rfl) ⟨79190, by rfl⟩) R158381
theorem R302221 : Reach 302221 := rs (se 3 (by rfl) ⟨56666, by rfl⟩) R113333
theorem R105617 : Reach 105617 := rs (se 2 (by rfl) ⟨39606, by rfl⟩) R79213
theorem R105635 : Reach 105635 := rs (se 1 (by rfl) ⟨79226, by rfl⟩) R158453
theorem R105665 : Reach 105665 := rs (se 2 (by rfl) ⟨39624, by rfl⟩) R79249
theorem R302285 : Reach 302285 := rs (se 3 (by rfl) ⟨56678, by rfl⟩) R113357
theorem R171217 : Reach 171217 := rs (se 2 (by rfl) ⟨64206, by rfl⟩) R128413
theorem R105683 : Reach 105683 := rs (se 1 (by rfl) ⟨79262, by rfl⟩) R158525
theorem R531683 : Reach 531683 := rs (se 1 (by rfl) ⟨398762, by rfl⟩) R797525
theorem R105713 : Reach 105713 := rs (se 2 (by rfl) ⟨39642, by rfl⟩) R79285
theorem R105731 : Reach 105731 := rs (se 1 (by rfl) ⟨79298, by rfl⟩) R158597
theorem R105761 : Reach 105761 := rs (se 2 (by rfl) ⟨39660, by rfl⟩) R79321
theorem R105779 : Reach 105779 := rs (se 1 (by rfl) ⟨79334, by rfl⟩) R158669
theorem R105809 : Reach 105809 := rs (se 2 (by rfl) ⟨39678, by rfl⟩) R79357
theorem R105827 : Reach 105827 := rs (se 1 (by rfl) ⟨79370, by rfl⟩) R158741
theorem R105857 : Reach 105857 := rs (se 2 (by rfl) ⟨39696, by rfl⟩) R79393
theorem R105875 : Reach 105875 := rs (se 1 (by rfl) ⟨79406, by rfl⟩) R158813
theorem R105905 : Reach 105905 := rs (se 2 (by rfl) ⟨39714, by rfl⟩) R79429
theorem R105923 : Reach 105923 := rs (se 1 (by rfl) ⟨79442, by rfl⟩) R158885
theorem R237005 : Reach 237005 := rs (se 3 (by rfl) ⟨44438, by rfl⟩) R88877
theorem R73171 : Reach 73171 := rs (se 1 (by rfl) ⟨54878, by rfl⟩) R109757
theorem R105953 : Reach 105953 := rs (se 2 (by rfl) ⟨39732, by rfl⟩) R79465
theorem R105971 : Reach 105971 := rs (se 1 (by rfl) ⟨79478, by rfl⟩) R158957
theorem R237059 : Reach 237059 := rs (se 1 (by rfl) ⟨177794, by rfl⟩) R355589
theorem R269837 : Reach 269837 := rs (se 3 (by rfl) ⟨50594, by rfl⟩) R101189
theorem R106001 : Reach 106001 := rs (se 2 (by rfl) ⟨39750, by rfl⟩) R79501
theorem R106019 : Reach 106019 := rs (se 1 (by rfl) ⟨79514, by rfl⟩) R159029
theorem R269873 : Reach 269873 := rs (se 2 (by rfl) ⟨101202, by rfl⟩) R202405
theorem R106049 : Reach 106049 := rs (se 2 (by rfl) ⟨39768, by rfl⟩) R79537
theorem R106067 : Reach 106067 := rs (se 1 (by rfl) ⟨79550, by rfl⟩) R159101
theorem R106097 : Reach 106097 := rs (se 2 (by rfl) ⟨39786, by rfl⟩) R79573
theorem R106115 : Reach 106115 := rs (se 1 (by rfl) ⟨79586, by rfl⟩) R159173
theorem R106145 : Reach 106145 := rs (se 2 (by rfl) ⟨39804, by rfl⟩) R79609
theorem R106163 : Reach 106163 := rs (se 1 (by rfl) ⟨79622, by rfl⟩) R159245
theorem R990917 : Reach 990917 := rs (se 4 (by rfl) ⟨92898, by rfl⟩) R185797
theorem R106193 : Reach 106193 := rs (se 2 (by rfl) ⟨39822, by rfl⟩) R79645
theorem R106211 : Reach 106211 := rs (se 1 (by rfl) ⟨79658, by rfl⟩) R159317
theorem R106241 : Reach 106241 := rs (se 2 (by rfl) ⟨39840, by rfl⟩) R79681
theorem R237329 : Reach 237329 := rs (se 2 (by rfl) ⟨88998, by rfl⟩) R177997
theorem R106259 : Reach 106259 := rs (se 1 (by rfl) ⟨79694, by rfl⟩) R159389
theorem R106289 : Reach 106289 := rs (se 2 (by rfl) ⟨39858, by rfl⟩) R79717
theorem R106307 : Reach 106307 := rs (se 1 (by rfl) ⟨79730, by rfl⟩) R159461
theorem R106337 : Reach 106337 := rs (se 2 (by rfl) ⟨39876, by rfl⟩) R79753
theorem R204643 : Reach 204643 := rs (se 1 (by rfl) ⟨153482, by rfl⟩) R306965
theorem R106355 : Reach 106355 := rs (se 1 (by rfl) ⟨79766, by rfl⟩) R159533
theorem R106385 : Reach 106385 := rs (se 2 (by rfl) ⟨39894, by rfl⟩) R79789
theorem R106403 : Reach 106403 := rs (se 1 (by rfl) ⟨79802, by rfl⟩) R159605
theorem R171953 : Reach 171953 := rs (se 2 (by rfl) ⟨64482, by rfl⟩) R128965
theorem R106433 : Reach 106433 := rs (se 2 (by rfl) ⟨39912, by rfl⟩) R79825
theorem R106451 : Reach 106451 := rs (se 1 (by rfl) ⟨79838, by rfl⟩) R159677
theorem R172003 : Reach 172003 := rs (se 1 (by rfl) ⟨129002, by rfl⟩) R258005
theorem R794609 : Reach 794609 := rs (se 2 (by rfl) ⟨297978, by rfl⟩) R595957
theorem R106481 : Reach 106481 := rs (se 2 (by rfl) ⟨39930, by rfl⟩) R79861
theorem R106499 : Reach 106499 := rs (se 1 (by rfl) ⟨79874, by rfl⟩) R159749
theorem R106529 : Reach 106529 := rs (se 2 (by rfl) ⟨39948, by rfl⟩) R79897
theorem R106547 : Reach 106547 := rs (se 1 (by rfl) ⟨79910, by rfl⟩) R159821
theorem R106577 : Reach 106577 := rs (se 2 (by rfl) ⟨39966, by rfl⟩) R79933
theorem R106595 : Reach 106595 := rs (se 1 (by rfl) ⟨79946, by rfl⟩) R159893
theorem R172145 : Reach 172145 := rs (se 2 (by rfl) ⟨64554, by rfl⟩) R129109
theorem R106625 : Reach 106625 := rs (se 2 (by rfl) ⟨39984, by rfl⟩) R79969
theorem R106643 : Reach 106643 := rs (se 1 (by rfl) ⟨79982, by rfl⟩) R159965
theorem R106673 : Reach 106673 := rs (se 2 (by rfl) ⟨40002, by rfl⟩) R80005
theorem R106771 : Reach 106771 := rs (se 1 (by rfl) ⟨80078, by rfl⟩) R160157
theorem R237869 : Reach 237869 := rs (se 3 (by rfl) ⟨44600, by rfl⟩) R89201
theorem R139601 : Reach 139601 := rs (se 2 (by rfl) ⟨52350, by rfl⟩) R104701
theorem R237923 : Reach 237923 := rs (se 1 (by rfl) ⟨178442, by rfl⟩) R356885
theorem R205229 : Reach 205229 := rs (se 3 (by rfl) ⟨38480, by rfl⟩) R76961
theorem R401861 : Reach 401861 := rs (se 4 (by rfl) ⟨37674, by rfl⟩) R75349
theorem R238193 : Reach 238193 := rs (se 2 (by rfl) ⟨89322, by rfl⟩) R178645
theorem R467653 : Reach 467653 := rs (se 4 (by rfl) ⟨43842, by rfl⟩) R87685
theorem R336611 : Reach 336611 := rs (se 1 (by rfl) ⟨252458, by rfl⟩) R504917
theorem R74563 : Reach 74563 := rs (se 1 (by rfl) ⟨55922, by rfl⟩) R111845
theorem R435077 : Reach 435077 := rs (se 4 (by rfl) ⟨40788, by rfl⟩) R81577
theorem R828301 : Reach 828301 := rs (se 3 (by rfl) ⟨155306, by rfl⟩) R310613
theorem R402317 : Reach 402317 := rs (se 3 (by rfl) ⟨75434, by rfl⟩) R150869
theorem R107585 : Reach 107585 := rs (se 2 (by rfl) ⟨40344, by rfl⟩) R80689
theorem R173137 : Reach 173137 := rs (se 2 (by rfl) ⟨64926, by rfl⟩) R129853
theorem R205955 : Reach 205955 := rs (se 1 (by rfl) ⟨154466, by rfl⟩) R308933
theorem R238733 : Reach 238733 := rs (se 3 (by rfl) ⟨44762, by rfl⟩) R89525
theorem R173411 : Reach 173411 := rs (se 1 (by rfl) ⟨130058, by rfl⟩) R260117
theorem R173603 : Reach 173603 := rs (se 1 (by rfl) ⟨130202, by rfl⟩) R260405
theorem R75523 : Reach 75523 := rs (se 1 (by rfl) ⟨56642, by rfl⟩) R113285
theorem R75667 : Reach 75667 := rs (se 1 (by rfl) ⟨56750, by rfl⟩) R113501
theorem R337841 : Reach 337841 := rs (se 2 (by rfl) ⟨126690, by rfl⟩) R253381
theorem R75811 : Reach 75811 := rs (se 1 (by rfl) ⟨56858, by rfl⟩) R113717
theorem R239651 : Reach 239651 := rs (se 1 (by rfl) ⟨179738, by rfl⟩) R359477
theorem R75955 : Reach 75955 := rs (se 1 (by rfl) ⟨56966, by rfl⟩) R113933
theorem R239921 : Reach 239921 := rs (se 2 (by rfl) ⟨89970, by rfl⟩) R179941
theorem R76099 : Reach 76099 := rs (se 1 (by rfl) ⟨57074, by rfl⟩) R114149
theorem R174467 : Reach 174467 := rs (se 1 (by rfl) ⟨130850, by rfl⟩) R261701
theorem R895373 : Reach 895373 := rs (se 3 (by rfl) ⟨167882, by rfl⟩) R335765
theorem R174545 : Reach 174545 := rs (se 2 (by rfl) ⟨65454, by rfl⟩) R130909
theorem R76243 : Reach 76243 := rs (se 1 (by rfl) ⟨57182, by rfl⟩) R114365
theorem R174595 : Reach 174595 := rs (se 1 (by rfl) ⟨130946, by rfl⟩) R261893
theorem R76387 : Reach 76387 := rs (se 1 (by rfl) ⟨57290, by rfl⟩) R114581
theorem R174737 : Reach 174737 := rs (se 2 (by rfl) ⟨65526, by rfl⟩) R131053
theorem R76531 : Reach 76531 := rs (se 1 (by rfl) ⟨57398, by rfl⟩) R114797
theorem R76675 : Reach 76675 := rs (se 1 (by rfl) ⟨57506, by rfl⟩) R115013
theorem R76819 : Reach 76819 := rs (se 1 (by rfl) ⟨57614, by rfl⟩) R115229
theorem R109603 : Reach 109603 := rs (se 1 (by rfl) ⟨82202, by rfl⟩) R164405
theorem R109667 : Reach 109667 := rs (se 1 (by rfl) ⟨82250, by rfl⟩) R164501
theorem R76963 : Reach 76963 := rs (se 1 (by rfl) ⟨57722, by rfl⟩) R115445
theorem R77107 : Reach 77107 := rs (se 1 (by rfl) ⟨57830, by rfl⟩) R115661
theorem R77251 : Reach 77251 := rs (se 1 (by rfl) ⟨57938, by rfl⟩) R115877
theorem R306659 : Reach 306659 := rs (se 1 (by rfl) ⟨229994, by rfl⟩) R459989
theorem R437795 : Reach 437795 := rs (se 1 (by rfl) ⟨328346, by rfl⟩) R656693
theorem R77395 : Reach 77395 := rs (se 1 (by rfl) ⟨58046, by rfl⟩) R116093
theorem R175729 : Reach 175729 := rs (se 2 (by rfl) ⟨65898, by rfl⟩) R131797
theorem R77539 : Reach 77539 := rs (se 1 (by rfl) ⟨58154, by rfl⟩) R116309
theorem R77683 : Reach 77683 := rs (se 1 (by rfl) ⟨58262, by rfl⟩) R116525
theorem R176003 : Reach 176003 := rs (se 1 (by rfl) ⟨132002, by rfl⟩) R264005
theorem R339875 : Reach 339875 := rs (se 1 (by rfl) ⟨254906, by rfl⟩) R509813
theorem R1159109 : Reach 1159109 := rs (se 4 (by rfl) ⟨108666, by rfl⟩) R217333
theorem R77827 : Reach 77827 := rs (se 1 (by rfl) ⟨58370, by rfl⟩) R116741
theorem R274481 : Reach 274481 := rs (se 2 (by rfl) ⟨102930, by rfl⟩) R205861
theorem R110641 : Reach 110641 := rs (se 2 (by rfl) ⟨41490, by rfl⟩) R82981
theorem R176195 : Reach 176195 := rs (se 1 (by rfl) ⟨132146, by rfl⟩) R264293
theorem R77971 : Reach 77971 := rs (se 1 (by rfl) ⟨58478, by rfl⟩) R116957
theorem R78115 : Reach 78115 := rs (se 1 (by rfl) ⟨58586, by rfl⟩) R117173
theorem R110897 : Reach 110897 := rs (se 2 (by rfl) ⟨41586, by rfl⟩) R83173
theorem R340301 : Reach 340301 := rs (se 3 (by rfl) ⟨63806, by rfl⟩) R127613
theorem R1323377 : Reach 1323377 := rs (se 2 (by rfl) ⟨496266, by rfl⟩) R992533
theorem R78259 : Reach 78259 := rs (se 1 (by rfl) ⟨58694, by rfl⟩) R117389
theorem R537029 : Reach 537029 := rs (se 4 (by rfl) ⟨50346, by rfl⟩) R100693
theorem R111089 : Reach 111089 := rs (se 2 (by rfl) ⟨41658, by rfl⟩) R83317
theorem R78403 : Reach 78403 := rs (se 1 (by rfl) ⟨58802, by rfl⟩) R117605
theorem R144035 : Reach 144035 := rs (se 1 (by rfl) ⟨108026, by rfl⟩) R216053
theorem R340685 : Reach 340685 := rs (se 3 (by rfl) ⟨63878, by rfl⟩) R127757
theorem R78547 : Reach 78547 := rs (se 1 (by rfl) ⟨58910, by rfl⟩) R117821
theorem R111361 : Reach 111361 := rs (se 2 (by rfl) ⟨41760, by rfl⟩) R83521
theorem R78691 : Reach 78691 := rs (se 1 (by rfl) ⟨59018, by rfl⟩) R118037
theorem R144337 : Reach 144337 := rs (se 2 (by rfl) ⟨54126, by rfl⟩) R108253
theorem R177137 : Reach 177137 := rs (se 2 (by rfl) ⟨66426, by rfl⟩) R132853
theorem R78835 : Reach 78835 := rs (se 1 (by rfl) ⟨59126, by rfl⟩) R118253
theorem R177187 : Reach 177187 := rs (se 1 (by rfl) ⟨132890, by rfl⟩) R265781
theorem R144497 : Reach 144497 := rs (se 2 (by rfl) ⟨54186, by rfl⟩) R108373
theorem R78979 : Reach 78979 := rs (se 1 (by rfl) ⟨59234, by rfl⟩) R118469
theorem R177329 : Reach 177329 := rs (se 2 (by rfl) ⟨66498, by rfl⟩) R132997
theorem R144593 : Reach 144593 := rs (se 2 (by rfl) ⟨54222, by rfl⟩) R108445
theorem R373987 : Reach 373987 := rs (se 1 (by rfl) ⟨280490, by rfl⟩) R560981
theorem R79123 : Reach 79123 := rs (se 1 (by rfl) ⟨59342, by rfl⟩) R118685
theorem R210289 : Reach 210289 := rs (se 2 (by rfl) ⟨78858, by rfl⟩) R157717
theorem R79267 : Reach 79267 := rs (se 1 (by rfl) ⟨59450, by rfl⟩) R118901
theorem R439793 : Reach 439793 := rs (se 2 (by rfl) ⟨164922, by rfl⟩) R329845
theorem R767501 : Reach 767501 := rs (se 3 (by rfl) ⟨143906, by rfl⟩) R287813
theorem R79411 : Reach 79411 := rs (se 1 (by rfl) ⟨59558, by rfl⟩) R119117
theorem R79555 : Reach 79555 := rs (se 1 (by rfl) ⟨59666, by rfl⟩) R119333
theorem R112403 : Reach 112403 := rs (se 1 (by rfl) ⟨84302, by rfl⟩) R168605
theorem R79699 : Reach 79699 := rs (se 1 (by rfl) ⟨59774, by rfl⟩) R119549
theorem R767843 : Reach 767843 := rs (se 1 (by rfl) ⟨575882, by rfl⟩) R1151765
theorem R145297 : Reach 145297 := rs (se 2 (by rfl) ⟨54486, by rfl⟩) R108973
theorem R79843 : Reach 79843 := rs (se 1 (by rfl) ⟨59882, by rfl⟩) R119765
theorem R112627 : Reach 112627 := rs (se 1 (by rfl) ⟨84470, by rfl⟩) R168941
theorem R374797 : Reach 374797 := rs (se 3 (by rfl) ⟨70274, by rfl⟩) R140549
theorem R112691 : Reach 112691 := rs (se 1 (by rfl) ⟨84518, by rfl⟩) R169037
theorem R79987 : Reach 79987 := rs (se 1 (by rfl) ⟨59990, by rfl⟩) R119981
theorem R178321 : Reach 178321 := rs (se 2 (by rfl) ⟨66870, by rfl⟩) R133741
theorem R112819 : Reach 112819 := rs (se 1 (by rfl) ⟨84614, by rfl⟩) R169229
theorem R145795 : Reach 145795 := rs (se 1 (by rfl) ⟨109346, by rfl⟩) R218693
theorem R178595 : Reach 178595 := rs (se 1 (by rfl) ⟨133946, by rfl⟩) R267893
theorem R178787 : Reach 178787 := rs (se 1 (by rfl) ⟨134090, by rfl⟩) R268181
theorem R146051 : Reach 146051 := rs (se 1 (by rfl) ⟨109538, by rfl⟩) R219077
theorem R735925 : Reach 735925 := rs (se 5 (by rfl) ⟨34496, by rfl⟩) R68993
theorem R113393 : Reach 113393 := rs (se 2 (by rfl) ⟨42522, by rfl⟩) R85045
theorem R113521 : Reach 113521 := rs (se 2 (by rfl) ⟨42570, by rfl⟩) R85141
theorem R113537 : Reach 113537 := rs (se 2 (by rfl) ⟨42576, by rfl⟩) R85153
theorem R113555 : Reach 113555 := rs (se 1 (by rfl) ⟨85166, by rfl⟩) R170333
theorem R113665 : Reach 113665 := rs (se 2 (by rfl) ⟨42624, by rfl⟩) R85249
theorem R113683 : Reach 113683 := rs (se 1 (by rfl) ⟨85262, by rfl⟩) R170525
theorem R474245 : Reach 474245 := rs (se 4 (by rfl) ⟨44460, by rfl⟩) R88921
theorem R113825 : Reach 113825 := rs (se 2 (by rfl) ⟨42684, by rfl⟩) R85369
theorem R179405 : Reach 179405 := rs (se 3 (by rfl) ⟨33638, by rfl⟩) R67277
theorem R113891 : Reach 113891 := rs (se 1 (by rfl) ⟨85418, by rfl⟩) R170837
theorem R113953 : Reach 113953 := rs (se 2 (by rfl) ⟨42732, by rfl⟩) R85465
theorem R113987 : Reach 113987 := rs (se 1 (by rfl) ⟨85490, by rfl⟩) R170981
theorem R179597 : Reach 179597 := rs (se 3 (by rfl) ⟨33674, by rfl⟩) R67349
theorem R114115 : Reach 114115 := rs (se 1 (by rfl) ⟨85586, by rfl⟩) R171173
theorem R179729 : Reach 179729 := rs (se 2 (by rfl) ⟨67398, by rfl⟩) R134797
theorem R81443 : Reach 81443 := rs (se 1 (by rfl) ⟨61082, by rfl⟩) R122165
theorem R343601 : Reach 343601 := rs (se 2 (by rfl) ⟨128850, by rfl⟩) R257701
theorem R179779 : Reach 179779 := rs (se 1 (by rfl) ⟨134834, by rfl⟩) R269669
theorem R114257 : Reach 114257 := rs (se 2 (by rfl) ⟨42846, by rfl⟩) R85693
theorem R147025 : Reach 147025 := rs (se 2 (by rfl) ⟨55134, by rfl⟩) R110269
theorem R114353 : Reach 114353 := rs (se 2 (by rfl) ⟨42882, by rfl⟩) R85765
theorem R114385 : Reach 114385 := rs (se 2 (by rfl) ⟨42894, by rfl⟩) R85789
theorem R179921 : Reach 179921 := rs (se 2 (by rfl) ⟨67470, by rfl⟩) R134941
theorem R114419 : Reach 114419 := rs (se 1 (by rfl) ⟨85814, by rfl⟩) R171629
theorem R114547 : Reach 114547 := rs (se 1 (by rfl) ⟨85910, by rfl⟩) R171821
theorem R442253 : Reach 442253 := rs (se 3 (by rfl) ⟨82922, by rfl⟩) R165845
theorem R114689 : Reach 114689 := rs (se 2 (by rfl) ⟨43008, by rfl⟩) R86017
theorem R114817 : Reach 114817 := rs (se 2 (by rfl) ⟨43056, by rfl⟩) R86113
theorem R114851 : Reach 114851 := rs (se 1 (by rfl) ⟨86138, by rfl⟩) R172277
theorem R82115 : Reach 82115 := rs (se 1 (by rfl) ⟨61586, by rfl⟩) R123173
theorem R245987 : Reach 245987 := rs (se 1 (by rfl) ⟨184490, by rfl⟩) R368981
theorem R147683 : Reach 147683 := rs (se 1 (by rfl) ⟨110762, by rfl⟩) R221525
theorem R114979 : Reach 114979 := rs (se 1 (by rfl) ⟨86234, by rfl⟩) R172469
theorem R147811 : Reach 147811 := rs (se 1 (by rfl) ⟨110858, by rfl⟩) R221717
theorem R246115 : Reach 246115 := rs (se 1 (by rfl) ⟨184586, by rfl⟩) R369173
theorem R115121 : Reach 115121 := rs (se 2 (by rfl) ⟨43170, by rfl⟩) R86341
theorem R115249 : Reach 115249 := rs (se 2 (by rfl) ⟨43218, by rfl⟩) R86437
theorem R115283 : Reach 115283 := rs (se 1 (by rfl) ⟨86462, by rfl⟩) R172925
theorem R115345 : Reach 115345 := rs (se 2 (by rfl) ⟨43254, by rfl⟩) R86509
theorem R115411 : Reach 115411 := rs (se 1 (by rfl) ⟨86558, by rfl⟩) R173117
theorem R705293 : Reach 705293 := rs (se 3 (by rfl) ⟨132242, by rfl⟩) R264485
theorem R246577 : Reach 246577 := rs (se 2 (by rfl) ⟨92466, by rfl⟩) R184933
theorem R115553 : Reach 115553 := rs (se 2 (by rfl) ⟨43332, by rfl⟩) R86665
theorem R115681 : Reach 115681 := rs (se 2 (by rfl) ⟨43380, by rfl⟩) R86761
theorem R345059 : Reach 345059 := rs (se 1 (by rfl) ⟨258794, by rfl⟩) R517589
theorem R115715 : Reach 115715 := rs (se 1 (by rfl) ⟨86786, by rfl⟩) R173573
theorem R148529 : Reach 148529 := rs (se 2 (by rfl) ⟨55698, by rfl⟩) R111397
theorem R115763 : Reach 115763 := rs (se 1 (by rfl) ⟨86822, by rfl⟩) R173645
theorem R115843 : Reach 115843 := rs (se 1 (by rfl) ⟨86882, by rfl⟩) R173765
theorem R4015331 : Reach 4015331 := rs (se 1 (by rfl) ⟨3011498, by rfl⟩) R6022997
theorem R115985 : Reach 115985 := rs (se 2 (by rfl) ⟨43494, by rfl⟩) R86989
theorem R181645 : Reach 181645 := rs (se 3 (by rfl) ⟨34058, by rfl⟩) R68117
theorem R116113 : Reach 116113 := rs (se 2 (by rfl) ⟨43542, by rfl⟩) R87085
theorem R116147 : Reach 116147 := rs (se 1 (by rfl) ⟨87110, by rfl⟩) R174221
theorem R116275 : Reach 116275 := rs (se 1 (by rfl) ⟨87206, by rfl⟩) R174413
theorem R575045 : Reach 575045 := rs (se 4 (by rfl) ⟨53910, by rfl⟩) R107821
theorem R116417 : Reach 116417 := rs (se 2 (by rfl) ⟨43656, by rfl⟩) R87313
theorem R345869 : Reach 345869 := rs (se 3 (by rfl) ⟨64850, by rfl⟩) R129701
theorem R116545 : Reach 116545 := rs (se 2 (by rfl) ⟨43704, by rfl⟩) R87409
theorem R116579 : Reach 116579 := rs (se 1 (by rfl) ⟨87434, by rfl⟩) R174869
theorem R182189 : Reach 182189 := rs (se 3 (by rfl) ⟨34160, by rfl⟩) R68321
theorem R182243 : Reach 182243 := rs (se 1 (by rfl) ⟨136682, by rfl⟩) R273365
theorem R116707 : Reach 116707 := rs (se 1 (by rfl) ⟨87530, by rfl⟩) R175061
theorem R84019 : Reach 84019 := rs (se 1 (by rfl) ⟨63014, by rfl⟩) R126029
theorem R116849 : Reach 116849 := rs (se 2 (by rfl) ⟨43818, by rfl⟩) R87637
theorem R116977 : Reach 116977 := rs (se 2 (by rfl) ⟨43866, by rfl⟩) R87733
theorem R510221 : Reach 510221 := rs (se 3 (by rfl) ⟨95666, by rfl⟩) R191333
theorem R117011 : Reach 117011 := rs (se 1 (by rfl) ⟨87758, by rfl⟩) R175517
theorem R84307 : Reach 84307 := rs (se 1 (by rfl) ⟨63230, by rfl⟩) R126461
theorem R117139 : Reach 117139 := rs (se 1 (by rfl) ⟨87854, by rfl⟩) R175709
theorem R84403 : Reach 84403 := rs (se 1 (by rfl) ⟨63302, by rfl⟩) R126605
theorem R117281 : Reach 117281 := rs (se 2 (by rfl) ⟨43980, by rfl⟩) R87961
theorem R84547 : Reach 84547 := rs (se 1 (by rfl) ⟨63410, by rfl⟩) R126821
theorem R117409 : Reach 117409 := rs (se 2 (by rfl) ⟨44028, by rfl⟩) R88057
theorem R117443 : Reach 117443 := rs (se 1 (by rfl) ⟨88082, by rfl⟩) R176165
theorem R117571 : Reach 117571 := rs (se 1 (by rfl) ⟨88178, by rfl⟩) R176357
theorem R117713 : Reach 117713 := rs (se 2 (by rfl) ⟨44142, by rfl⟩) R88285
theorem R84979 : Reach 84979 := rs (se 1 (by rfl) ⟨63734, by rfl⟩) R127469
theorem R117841 : Reach 117841 := rs (se 2 (by rfl) ⟨44190, by rfl⟩) R88381
theorem R281713 : Reach 281713 := rs (se 2 (by rfl) ⟨105642, by rfl⟩) R211285
theorem R117875 : Reach 117875 := rs (se 1 (by rfl) ⟨88406, by rfl⟩) R176813
theorem R118003 : Reach 118003 := rs (se 1 (by rfl) ⟨88502, by rfl⟩) R177005
theorem R871793 : Reach 871793 := rs (se 2 (by rfl) ⟨326922, by rfl⟩) R653845
theorem R118145 : Reach 118145 := rs (se 2 (by rfl) ⟨44304, by rfl⟩) R88609
theorem R85475 : Reach 85475 := rs (se 1 (by rfl) ⟨64106, by rfl⟩) R128213
theorem R118273 : Reach 118273 := rs (se 2 (by rfl) ⟨44352, by rfl⟩) R88705
theorem R118307 : Reach 118307 := rs (se 1 (by rfl) ⟨88730, by rfl⟩) R177461
theorem R118435 : Reach 118435 := rs (se 1 (by rfl) ⟨88826, by rfl⟩) R177653
theorem R151217 : Reach 151217 := rs (se 2 (by rfl) ⟨56706, by rfl⟩) R113413
theorem R118451 : Reach 118451 := rs (se 1 (by rfl) ⟨88838, by rfl⟩) R177677
theorem R151235 : Reach 151235 := rs (se 1 (by rfl) ⟨113426, by rfl⟩) R226853
theorem R511757 : Reach 511757 := rs (se 3 (by rfl) ⟨95954, by rfl⟩) R191909
theorem R151313 : Reach 151313 := rs (se 2 (by rfl) ⟨56742, by rfl⟩) R113485
theorem R118577 : Reach 118577 := rs (se 2 (by rfl) ⟨44466, by rfl⟩) R88933
theorem R118643 : Reach 118643 := rs (se 1 (by rfl) ⟨88982, by rfl⟩) R177965
theorem R118705 : Reach 118705 := rs (se 2 (by rfl) ⟨44514, by rfl⟩) R89029
theorem R151505 : Reach 151505 := rs (se 2 (by rfl) ⟨56814, by rfl⟩) R113629
theorem R118739 : Reach 118739 := rs (se 1 (by rfl) ⟨89054, by rfl⟩) R178109
theorem R151523 : Reach 151523 := rs (se 1 (by rfl) ⟨113642, by rfl⟩) R227285
theorem R774197 : Reach 774197 := rs (se 5 (by rfl) ⟨36290, by rfl⟩) R72581
theorem R118867 : Reach 118867 := rs (se 1 (by rfl) ⟨89150, by rfl⟩) R178301
theorem R315505 : Reach 315505 := rs (se 2 (by rfl) ⟨118314, by rfl⟩) R236629
theorem R86179 : Reach 86179 := rs (se 1 (by rfl) ⟨64634, by rfl⟩) R129269
theorem R446627 : Reach 446627 := rs (se 1 (by rfl) ⟨334970, by rfl⟩) R669941
theorem R119009 : Reach 119009 := rs (se 2 (by rfl) ⟨44628, by rfl⟩) R89257
theorem R151793 : Reach 151793 := rs (se 2 (by rfl) ⟨56922, by rfl⟩) R113845
theorem R151811 : Reach 151811 := rs (se 1 (by rfl) ⟨113858, by rfl⟩) R227717
theorem R86275 : Reach 86275 := rs (se 1 (by rfl) ⟨64706, by rfl⟩) R129413
theorem R119137 : Reach 119137 := rs (se 2 (by rfl) ⟨44676, by rfl⟩) R89353
theorem R119171 : Reach 119171 := rs (se 1 (by rfl) ⟨89378, by rfl⟩) R178757
theorem R119299 : Reach 119299 := rs (se 1 (by rfl) ⟨89474, by rfl⟩) R178949
theorem R152081 : Reach 152081 := rs (se 2 (by rfl) ⟨57030, by rfl⟩) R114061
theorem R152099 : Reach 152099 := rs (se 1 (by rfl) ⟨114074, by rfl⟩) R228149
theorem R217667 : Reach 217667 := rs (se 1 (by rfl) ⟨163250, by rfl⟩) R326501
theorem R676451 : Reach 676451 := rs (se 1 (by rfl) ⟨507338, by rfl⟩) R1014677
theorem R348785 : Reach 348785 := rs (se 2 (by rfl) ⟨130794, by rfl⟩) R261589
theorem R119441 : Reach 119441 := rs (se 2 (by rfl) ⟨44790, by rfl⟩) R89581
theorem R185041 : Reach 185041 := rs (se 2 (by rfl) ⟨69390, by rfl⟩) R138781
theorem R86771 : Reach 86771 := rs (se 1 (by rfl) ⟨65078, by rfl⟩) R130157
theorem R119569 : Reach 119569 := rs (se 2 (by rfl) ⟨44838, by rfl⟩) R89677
theorem R152369 : Reach 152369 := rs (se 2 (by rfl) ⟨57138, by rfl⟩) R114277
theorem R152387 : Reach 152387 := rs (se 1 (by rfl) ⟨114290, by rfl⟩) R228581
theorem R119875 : Reach 119875 := rs (se 1 (by rfl) ⟨89906, by rfl⟩) R179813
theorem R152657 : Reach 152657 := rs (se 2 (by rfl) ⟨57246, by rfl⟩) R114493
theorem R152675 : Reach 152675 := rs (se 1 (by rfl) ⟨114506, by rfl⟩) R229013
theorem R939235 : Reach 939235 := rs (se 1 (by rfl) ⟨704426, by rfl⟩) R1408853
theorem R152945 : Reach 152945 := rs (se 2 (by rfl) ⟨57354, by rfl⟩) R114709
theorem R152963 : Reach 152963 := rs (se 1 (by rfl) ⟨114722, by rfl⟩) R229445
theorem R218513 : Reach 218513 := rs (se 2 (by rfl) ⟨81942, by rfl⟩) R163885
theorem R87475 : Reach 87475 := rs (se 1 (by rfl) ⟨65606, by rfl⟩) R131213
theorem R251363 : Reach 251363 := rs (se 1 (by rfl) ⟨188522, by rfl⟩) R377045
theorem R87571 : Reach 87571 := rs (se 1 (by rfl) ⟨65678, by rfl⟩) R131357
theorem R874037 : Reach 874037 := rs (se 5 (by rfl) ⟨40970, by rfl⟩) R81941
theorem R153233 : Reach 153233 := rs (se 2 (by rfl) ⟨57462, by rfl⟩) R114925
theorem R153251 : Reach 153251 := rs (se 1 (by rfl) ⟨114938, by rfl⟩) R229877
theorem R874253 : Reach 874253 := rs (se 3 (by rfl) ⟨163922, by rfl⟩) R327845
theorem R186275 : Reach 186275 := rs (se 1 (by rfl) ⟨139706, by rfl⟩) R279413
theorem R153521 : Reach 153521 := rs (se 2 (by rfl) ⟨57570, by rfl⟩) R115141
theorem R153539 : Reach 153539 := rs (se 1 (by rfl) ⟨115154, by rfl⟩) R230309
theorem R186317 : Reach 186317 := rs (se 3 (by rfl) ⟨34934, by rfl⟩) R69869
theorem R88067 : Reach 88067 := rs (se 1 (by rfl) ⟨66050, by rfl⟩) R132101
theorem R350243 : Reach 350243 := rs (se 1 (by rfl) ⟨262682, by rfl⟩) R525365
theorem R383089 : Reach 383089 := rs (se 2 (by rfl) ⟨143658, by rfl⟩) R287317
theorem R547013 : Reach 547013 := rs (se 4 (by rfl) ⟨51282, by rfl⟩) R102565
theorem R153809 : Reach 153809 := rs (se 2 (by rfl) ⟨57678, by rfl⟩) R115357
theorem R153827 : Reach 153827 := rs (se 1 (by rfl) ⟨115370, by rfl⟩) R230741
theorem R154097 : Reach 154097 := rs (se 2 (by rfl) ⟨57786, by rfl⟩) R115573
theorem R154115 : Reach 154115 := rs (se 1 (by rfl) ⟨115586, by rfl⟩) R231173
theorem R514673 : Reach 514673 := rs (se 2 (by rfl) ⟨193002, by rfl⟩) R386005
theorem R88771 : Reach 88771 := rs (se 1 (by rfl) ⟨66578, by rfl⟩) R133157
theorem R154385 : Reach 154385 := rs (se 2 (by rfl) ⟨57894, by rfl⟩) R115789
theorem R154403 : Reach 154403 := rs (se 1 (by rfl) ⟨115802, by rfl⟩) R231605
theorem R88867 : Reach 88867 := rs (se 1 (by rfl) ⟨66650, by rfl⟩) R133301
theorem R1334069 : Reach 1334069 := rs (se 5 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R351053 : Reach 351053 := rs (se 3 (by rfl) ⟨65822, by rfl⟩) R131645
theorem R646157 : Reach 646157 := rs (se 3 (by rfl) ⟨121154, by rfl⟩) R242309
theorem R154673 : Reach 154673 := rs (se 2 (by rfl) ⟨58002, by rfl⟩) R116005
theorem R154691 : Reach 154691 := rs (se 1 (by rfl) ⟨116018, by rfl⟩) R232037
theorem R89219 : Reach 89219 := rs (se 1 (by rfl) ⟨66914, by rfl⟩) R133829
theorem R220333 : Reach 220333 := rs (se 3 (by rfl) ⟨41312, by rfl⟩) R82625
theorem R89363 : Reach 89363 := rs (se 1 (by rfl) ⟨67022, by rfl⟩) R134045
theorem R154961 : Reach 154961 := rs (se 2 (by rfl) ⟨58110, by rfl⟩) R116221
theorem R154979 : Reach 154979 := rs (se 1 (by rfl) ⟨116234, by rfl⟩) R232469
theorem R384547 : Reach 384547 := rs (se 1 (by rfl) ⟨288410, by rfl⟩) R576821
theorem R155249 : Reach 155249 := rs (se 2 (by rfl) ⟨58218, by rfl⟩) R116437
theorem R155267 : Reach 155267 := rs (se 1 (by rfl) ⟨116450, by rfl⟩) R232901
theorem R122627 : Reach 122627 := rs (se 1 (by rfl) ⟨91970, by rfl⟩) R183941
theorem R89905 : Reach 89905 := rs (se 2 (by rfl) ⟨33714, by rfl⟩) R67429
theorem R155537 : Reach 155537 := rs (se 2 (by rfl) ⟨58326, by rfl⟩) R116653
theorem R90001 : Reach 90001 := rs (se 2 (by rfl) ⟨33750, by rfl⟩) R67501
theorem R155555 : Reach 155555 := rs (se 1 (by rfl) ⟨116666, by rfl⟩) R233333
theorem R385073 : Reach 385073 := rs (se 2 (by rfl) ⟨144402, by rfl⟩) R288805
theorem R450659 : Reach 450659 := rs (se 1 (by rfl) ⟨337994, by rfl⟩) R675989
theorem R155825 : Reach 155825 := rs (se 2 (by rfl) ⟨58434, by rfl⟩) R116869
theorem R155843 : Reach 155843 := rs (se 1 (by rfl) ⟨116882, by rfl⟩) R233765
theorem R745699 : Reach 745699 := rs (se 1 (by rfl) ⟨559274, by rfl⟩) R1118549
theorem R90563 : Reach 90563 := rs (se 1 (by rfl) ⟨67922, by rfl⟩) R135845
theorem R156113 : Reach 156113 := rs (se 2 (by rfl) ⟨58542, by rfl⟩) R117085
theorem R549347 : Reach 549347 := rs (se 1 (by rfl) ⟨412010, by rfl⟩) R824021
theorem R156131 : Reach 156131 := rs (se 1 (by rfl) ⟨117098, by rfl⟩) R234197
theorem R156401 : Reach 156401 := rs (se 2 (by rfl) ⟨58650, by rfl⟩) R117301
theorem R156419 : Reach 156419 := rs (se 1 (by rfl) ⟨117314, by rfl⟩) R234629
theorem R3761093 : Reach 3761093 := rs (se 4 (by rfl) ⟨352602, by rfl⟩) R705205
theorem R156689 : Reach 156689 := rs (se 2 (by rfl) ⟨58758, by rfl⟩) R117517
theorem R156707 : Reach 156707 := rs (se 1 (by rfl) ⟨117530, by rfl⟩) R235061
theorem R255025 : Reach 255025 := rs (se 2 (by rfl) ⟨95634, by rfl⟩) R191269
theorem R255089 : Reach 255089 := rs (se 2 (by rfl) ⟨95658, by rfl⟩) R191317
theorem R156977 : Reach 156977 := rs (se 2 (by rfl) ⟨58866, by rfl⟩) R117733
theorem R451889 : Reach 451889 := rs (se 2 (by rfl) ⟨169458, by rfl⟩) R338917
theorem R156995 : Reach 156995 := rs (se 1 (by rfl) ⟨117746, by rfl⟩) R235493
theorem R583109 : Reach 583109 := rs (se 4 (by rfl) ⟨54666, by rfl⟩) R109333
theorem R386531 : Reach 386531 := rs (se 1 (by rfl) ⟨289898, by rfl⟩) R579797
theorem R157265 : Reach 157265 := rs (se 2 (by rfl) ⟨58974, by rfl⟩) R117949
theorem R157283 : Reach 157283 := rs (se 1 (by rfl) ⟨117962, by rfl⟩) R235925
theorem R353969 : Reach 353969 := rs (se 2 (by rfl) ⟨132738, by rfl⟩) R265477
theorem R255757 : Reach 255757 := rs (se 3 (by rfl) ⟨47954, by rfl⟩) R95909
theorem R681797 : Reach 681797 := rs (se 4 (by rfl) ⟨63918, by rfl⟩) R127837
theorem R452429 : Reach 452429 := rs (se 3 (by rfl) ⟨84830, by rfl⟩) R169661
theorem R157553 : Reach 157553 := rs (se 2 (by rfl) ⟨59082, by rfl⟩) R118165
theorem R157571 : Reach 157571 := rs (se 1 (by rfl) ⟨118178, by rfl⟩) R236357
theorem R583793 : Reach 583793 := rs (se 2 (by rfl) ⟨218922, by rfl⟩) R437845
theorem R190577 : Reach 190577 := rs (se 2 (by rfl) ⟨71466, by rfl⟩) R142933
theorem R157841 : Reach 157841 := rs (se 2 (by rfl) ⟨59190, by rfl⟩) R118381
theorem R157859 : Reach 157859 := rs (se 1 (by rfl) ⟨118394, by rfl⟩) R236789
theorem R158129 : Reach 158129 := rs (se 2 (by rfl) ⟨59298, by rfl⟩) R118597
theorem R158147 : Reach 158147 := rs (se 1 (by rfl) ⟨118610, by rfl⟩) R237221
theorem R256547 : Reach 256547 := rs (se 1 (by rfl) ⟨192410, by rfl⟩) R384821
theorem R223793 : Reach 223793 := rs (se 2 (by rfl) ⟨83922, by rfl⟩) R167845
theorem R158417 : Reach 158417 := rs (se 2 (by rfl) ⟨59406, by rfl⟩) R118813
theorem R158435 : Reach 158435 := rs (se 1 (by rfl) ⟨118826, by rfl⟩) R237653
theorem R223985 : Reach 223985 := rs (se 2 (by rfl) ⟨83994, by rfl⟩) R167989
theorem R289763 : Reach 289763 := rs (se 1 (by rfl) ⟨217322, by rfl⟩) R434645
theorem R158705 : Reach 158705 := rs (se 2 (by rfl) ⟨59514, by rfl⟩) R119029
theorem R158723 : Reach 158723 := rs (se 1 (by rfl) ⟨119042, by rfl⟩) R238085
theorem R355427 : Reach 355427 := rs (se 1 (by rfl) ⟨266570, by rfl⟩) R533141
theorem R93331 : Reach 93331 := rs (se 1 (by rfl) ⟨69998, by rfl⟩) R139997
theorem R257201 : Reach 257201 := rs (se 2 (by rfl) ⟨96450, by rfl⟩) R192901
theorem R158993 : Reach 158993 := rs (se 2 (by rfl) ⟨59622, by rfl⟩) R119245
theorem R159011 : Reach 159011 := rs (se 1 (by rfl) ⟨119258, by rfl⟩) R238517
theorem R388421 : Reach 388421 := rs (se 4 (by rfl) ⟨36414, by rfl⟩) R72829
theorem R159281 : Reach 159281 := rs (se 2 (by rfl) ⟨59730, by rfl⟩) R119461
theorem R159299 : Reach 159299 := rs (se 1 (by rfl) ⟨119474, by rfl⟩) R238949
theorem R93889 : Reach 93889 := rs (se 2 (by rfl) ⟨35208, by rfl⟩) R70417
theorem R454349 : Reach 454349 := rs (se 3 (by rfl) ⟨85190, by rfl⟩) R170381
theorem R159569 : Reach 159569 := rs (se 2 (by rfl) ⟨59838, by rfl⟩) R119677
theorem R159587 : Reach 159587 := rs (se 1 (by rfl) ⟨119690, by rfl⟩) R239381
theorem R192365 : Reach 192365 := rs (se 3 (by rfl) ⟨36068, by rfl⟩) R72137
theorem R356237 : Reach 356237 := rs (se 3 (by rfl) ⟨66794, by rfl⟩) R133589
theorem R192547 : Reach 192547 := rs (se 1 (by rfl) ⟨144410, by rfl⟩) R288821
theorem R192593 : Reach 192593 := rs (se 2 (by rfl) ⟨72222, by rfl⟩) R144445
theorem R159857 : Reach 159857 := rs (se 2 (by rfl) ⟨59946, by rfl⟩) R119893
theorem R159875 : Reach 159875 := rs (se 1 (by rfl) ⟨119906, by rfl⟩) R239813
theorem R94451 : Reach 94451 := rs (se 1 (by rfl) ⟨70838, by rfl⟩) R141677
theorem R487907 : Reach 487907 := rs (se 1 (by rfl) ⟨365930, by rfl⟩) R731861
theorem R258659 : Reach 258659 := rs (se 1 (by rfl) ⟨193994, by rfl⟩) R387989
theorem R258673 : Reach 258673 := rs (se 2 (by rfl) ⟨97002, by rfl⟩) R194005
theorem R127651 : Reach 127651 := rs (se 1 (by rfl) ⟨95738, by rfl⟩) R191477
theorem R127793 : Reach 127793 := rs (se 2 (by rfl) ⟨47922, by rfl⟩) R95845
theorem R127811 : Reach 127811 := rs (se 1 (by rfl) ⟨95858, by rfl⟩) R191717
theorem R291761 : Reach 291761 := rs (se 2 (by rfl) ⟨109410, by rfl⟩) R218821
theorem R226253 : Reach 226253 := rs (se 3 (by rfl) ⟨42422, by rfl⟩) R84845
theorem R128017 : Reach 128017 := rs (se 2 (by rfl) ⟨48006, by rfl⟩) R96013
theorem R128099 : Reach 128099 := rs (se 1 (by rfl) ⟨96074, by rfl⟩) R192149
theorem R95537 : Reach 95537 := rs (se 2 (by rfl) ⟨35826, by rfl⟩) R71653
theorem R226637 : Reach 226637 := rs (se 3 (by rfl) ⟨42494, by rfl⟩) R84989
theorem R226691 : Reach 226691 := rs (se 1 (by rfl) ⟨170018, by rfl⟩) R340037
theorem R194051 : Reach 194051 := rs (se 1 (by rfl) ⟨145538, by rfl⟩) R291077
theorem R226961 : Reach 226961 := rs (se 2 (by rfl) ⟨85110, by rfl⟩) R170221
theorem R685837 : Reach 685837 := rs (se 3 (by rfl) ⟨128594, by rfl⟩) R257189
theorem R128881 : Reach 128881 := rs (se 2 (by rfl) ⟨48330, by rfl⟩) R96661
theorem R161713 : Reach 161713 := rs (se 2 (by rfl) ⟨60642, by rfl⟩) R121285
theorem R260131 : Reach 260131 := rs (se 1 (by rfl) ⟨195098, by rfl⟩) R390197
theorem R227501 : Reach 227501 := rs (se 3 (by rfl) ⟨42656, by rfl⟩) R85313
theorem R1308869 : Reach 1308869 := rs (se 4 (by rfl) ⟨122706, by rfl⟩) R245413
theorem R227555 : Reach 227555 := rs (se 1 (by rfl) ⟨170666, by rfl⟩) R341333
theorem R96547 : Reach 96547 := rs (se 1 (by rfl) ⟨72410, by rfl⟩) R144821
theorem R227825 : Reach 227825 := rs (se 2 (by rfl) ⟨85434, by rfl⟩) R170869
theorem R227843 : Reach 227843 := rs (se 1 (by rfl) ⟨170882, by rfl⟩) R341765
theorem R293453 : Reach 293453 := rs (se 3 (by rfl) ⟨55022, by rfl⟩) R110045
theorem R195281 : Reach 195281 := rs (se 2 (by rfl) ⟨73230, by rfl⟩) R146461
theorem R359153 : Reach 359153 := rs (se 2 (by rfl) ⟨134682, by rfl⟩) R269365
theorem R129937 : Reach 129937 := rs (se 2 (by rfl) ⟨48726, by rfl⟩) R97453
theorem R228365 : Reach 228365 := rs (se 3 (by rfl) ⟨42818, by rfl⟩) R85637
theorem R3013685 : Reach 3013685 := rs (se 5 (by rfl) ⟨141266, by rfl⟩) R282533
theorem R228419 : Reach 228419 := rs (se 1 (by rfl) ⟨171314, by rfl⟩) R342629
theorem R130339 : Reach 130339 := rs (se 1 (by rfl) ⟨97754, by rfl⟩) R195509
theorem R228689 : Reach 228689 := rs (se 2 (by rfl) ⟨85758, by rfl⟩) R171517
theorem R130385 : Reach 130385 := rs (se 2 (by rfl) ⟨48894, by rfl⟩) R97789
theorem R97681 : Reach 97681 := rs (se 2 (by rfl) ⟨36630, by rfl⟩) R73261
theorem R785861 : Reach 785861 := rs (se 4 (by rfl) ⟨73674, by rfl⟩) R147349
theorem R97777 : Reach 97777 := rs (se 2 (by rfl) ⟨36666, by rfl⟩) R73333
theorem R130673 : Reach 130673 := rs (se 2 (by rfl) ⟨49002, by rfl⟩) R98005
theorem R229229 : Reach 229229 := rs (se 3 (by rfl) ⟨42980, by rfl⟩) R85961
theorem R229283 : Reach 229283 := rs (se 1 (by rfl) ⟨171962, by rfl⟩) R343925
theorem R98273 : Reach 98273 := rs (se 2 (by rfl) ⟨36852, by rfl⟩) R73705
theorem R131159 : Reach 131159 := rs (se 1 (by rfl) ⟨98369, by rfl⟩) R196739
theorem R983171 : Reach 983171 := rs (se 1 (by rfl) ⟨737378, by rfl⟩) R1474757
theorem R163991 : Reach 163991 := rs (se 1 (by rfl) ⟨122993, by rfl⟩) R245987
theorem R197081 : Reach 197081 := rs (se 2 (by rfl) ⟨73905, by rfl⟩) R147811
theorem R328153 : Reach 328153 := rs (se 2 (by rfl) ⟨123057, by rfl⟩) R246115
theorem R393821 : Reach 393821 := rs (se 3 (by rfl) ⟨73841, by rfl⟩) R147683
theorem R131699 : Reach 131699 := rs (se 1 (by rfl) ⟨98774, by rfl⟩) R197549
theorem R230039 : Reach 230039 := rs (se 1 (by rfl) ⟨172529, by rfl⟩) R345059
theorem R262835 : Reach 262835 := rs (se 1 (by rfl) ⟨197126, by rfl⟩) R394253
theorem R99019 : Reach 99019 := rs (se 1 (by rfl) ⟨74264, by rfl⟩) R148529
theorem R623537 : Reach 623537 := rs (se 2 (by rfl) ⟨233826, by rfl⟩) R467653
theorem R328769 : Reach 328769 := rs (se 2 (by rfl) ⟨123288, by rfl⟩) R246577
theorem R132185 : Reach 132185 := rs (se 2 (by rfl) ⟨49569, by rfl⟩) R99139
theorem R230579 : Reach 230579 := rs (se 1 (by rfl) ⟨172934, by rfl⟩) R345869
theorem R296237 : Reach 296237 := rs (se 3 (by rfl) ⟨55544, by rfl⟩) R111089
theorem R394571 : Reach 394571 := rs (se 1 (by rfl) ⟨295928, by rfl⟩) R591857
theorem R230849 : Reach 230849 := rs (se 2 (by rfl) ⟨86568, by rfl⟩) R173137
theorem R67127 : Reach 67127 := rs (se 1 (by rfl) ⟨50345, by rfl⟩) R100691
theorem R67147 : Reach 67147 := rs (se 1 (by rfl) ⟨50360, by rfl⟩) R100721
theorem R67159 : Reach 67159 := rs (se 1 (by rfl) ⟨50369, by rfl⟩) R100739
theorem R67179 : Reach 67179 := rs (se 1 (by rfl) ⟨50384, by rfl⟩) R100769
theorem R67191 : Reach 67191 := rs (se 1 (by rfl) ⟨50393, by rfl⟩) R100787
theorem R67211 : Reach 67211 := rs (se 1 (by rfl) ⟨50408, by rfl⟩) R100817
theorem R67223 : Reach 67223 := rs (se 1 (by rfl) ⟨50417, by rfl⟩) R100835
theorem R67243 : Reach 67243 := rs (se 1 (by rfl) ⟨50432, by rfl⟩) R100865
theorem R67255 : Reach 67255 := rs (se 1 (by rfl) ⟨50441, by rfl⟩) R100883
theorem R67275 : Reach 67275 := rs (se 1 (by rfl) ⟨50456, by rfl⟩) R100913
theorem R67287 : Reach 67287 := rs (se 1 (by rfl) ⟨50465, by rfl⟩) R100931
theorem R67307 : Reach 67307 := rs (se 1 (by rfl) ⟨50480, by rfl⟩) R100961
theorem R67319 : Reach 67319 := rs (se 1 (by rfl) ⟨50489, by rfl⟩) R100979
theorem R67339 : Reach 67339 := rs (se 1 (by rfl) ⟨50504, by rfl⟩) R101009
theorem R67351 : Reach 67351 := rs (se 1 (by rfl) ⟨50513, by rfl⟩) R101027
theorem R67371 : Reach 67371 := rs (se 1 (by rfl) ⟨50528, by rfl⟩) R101057
theorem R67383 : Reach 67383 := rs (se 1 (by rfl) ⟨50537, by rfl⟩) R101075
theorem R67403 : Reach 67403 := rs (se 1 (by rfl) ⟨50552, by rfl⟩) R101105
theorem R67415 : Reach 67415 := rs (se 1 (by rfl) ⟨50561, by rfl⟩) R101123
theorem R67435 : Reach 67435 := rs (se 1 (by rfl) ⟨50576, by rfl⟩) R101153
theorem R67447 : Reach 67447 := rs (se 1 (by rfl) ⟨50585, by rfl⟩) R101171
theorem R67467 : Reach 67467 := rs (se 1 (by rfl) ⟨50600, by rfl⟩) R101201
theorem R67479 : Reach 67479 := rs (se 1 (by rfl) ⟨50609, by rfl⟩) R101219
theorem R198551 : Reach 198551 := rs (se 1 (by rfl) ⟨148913, by rfl⟩) R297827
theorem R67499 : Reach 67499 := rs (se 1 (by rfl) ⟨50624, by rfl⟩) R101249
theorem R67511 : Reach 67511 := rs (se 1 (by rfl) ⟨50633, by rfl⟩) R101267
theorem R67531 : Reach 67531 := rs (se 1 (by rfl) ⟨50648, by rfl⟩) R101297
theorem R67543 : Reach 67543 := rs (se 1 (by rfl) ⟨50657, by rfl⟩) R101315
theorem R231389 : Reach 231389 := rs (se 3 (by rfl) ⟨43385, by rfl⟩) R86771
theorem R67563 : Reach 67563 := rs (se 1 (by rfl) ⟨50672, by rfl⟩) R101345
theorem R67575 : Reach 67575 := rs (se 1 (by rfl) ⟨50681, by rfl⟩) R101363
theorem R67595 : Reach 67595 := rs (se 1 (by rfl) ⟨50696, by rfl⟩) R101393
theorem R67607 : Reach 67607 := rs (se 1 (by rfl) ⟨50705, by rfl⟩) R101411
theorem R67627 : Reach 67627 := rs (se 1 (by rfl) ⟨50720, by rfl⟩) R101441
theorem R67639 : Reach 67639 := rs (se 1 (by rfl) ⟨50729, by rfl⟩) R101459
theorem R67659 : Reach 67659 := rs (se 1 (by rfl) ⟨50744, by rfl⟩) R101489
theorem R67671 : Reach 67671 := rs (se 1 (by rfl) ⟨50753, by rfl⟩) R101507
theorem R67691 : Reach 67691 := rs (se 1 (by rfl) ⟨50768, by rfl⟩) R101537
theorem R67703 : Reach 67703 := rs (se 1 (by rfl) ⟨50777, by rfl⟩) R101555
theorem R264323 : Reach 264323 := rs (se 1 (by rfl) ⟨198242, by rfl⟩) R396485
theorem R67723 : Reach 67723 := rs (se 1 (by rfl) ⟨50792, by rfl⟩) R101585
theorem R67735 : Reach 67735 := rs (se 1 (by rfl) ⟨50801, by rfl⟩) R101603
theorem R67755 : Reach 67755 := rs (se 1 (by rfl) ⟨50816, by rfl⟩) R101633
theorem R67767 : Reach 67767 := rs (se 1 (by rfl) ⟨50825, by rfl⟩) R101651
theorem R67787 : Reach 67787 := rs (se 1 (by rfl) ⟨50840, by rfl⟩) R101681
theorem R67799 : Reach 67799 := rs (se 1 (by rfl) ⟨50849, by rfl⟩) R101699
theorem R67819 : Reach 67819 := rs (se 1 (by rfl) ⟨50864, by rfl⟩) R101729
theorem R67831 : Reach 67831 := rs (se 1 (by rfl) ⟨50873, by rfl⟩) R101747
theorem R67851 : Reach 67851 := rs (se 1 (by rfl) ⟨50888, by rfl⟩) R101777
theorem R67863 : Reach 67863 := rs (se 1 (by rfl) ⟨50897, by rfl⟩) R101795
theorem R67883 : Reach 67883 := rs (se 1 (by rfl) ⟨50912, by rfl⟩) R101825
theorem R67895 : Reach 67895 := rs (se 1 (by rfl) ⟨50921, by rfl⟩) R101843
theorem R67915 : Reach 67915 := rs (se 1 (by rfl) ⟨50936, by rfl⟩) R101873
theorem R67927 : Reach 67927 := rs (se 1 (by rfl) ⟨50945, by rfl⟩) R101891
theorem R100697 : Reach 100697 := rs (se 2 (by rfl) ⟨37761, by rfl⟩) R75523
theorem R67947 : Reach 67947 := rs (se 1 (by rfl) ⟨50960, by rfl⟩) R101921
theorem R3869045 : Reach 3869045 := rs (se 5 (by rfl) ⟨181361, by rfl⟩) R362723
theorem R67959 : Reach 67959 := rs (se 1 (by rfl) ⟨50969, by rfl⟩) R101939
theorem R67979 : Reach 67979 := rs (se 1 (by rfl) ⟨50984, by rfl⟩) R101969
theorem R67991 : Reach 67991 := rs (se 1 (by rfl) ⟨50993, by rfl⟩) R101987
theorem R68011 : Reach 68011 := rs (se 1 (by rfl) ⟨51008, by rfl⟩) R102017
theorem R68023 : Reach 68023 := rs (se 1 (by rfl) ⟨51017, by rfl⟩) R102035
theorem R100811 : Reach 100811 := rs (se 1 (by rfl) ⟨75608, by rfl⟩) R151217
theorem R68043 : Reach 68043 := rs (se 1 (by rfl) ⟨51032, by rfl⟩) R102065
theorem R100823 : Reach 100823 := rs (se 1 (by rfl) ⟨75617, by rfl⟩) R151235
theorem R68055 : Reach 68055 := rs (se 1 (by rfl) ⟨51041, by rfl⟩) R102083
theorem R68075 : Reach 68075 := rs (se 1 (by rfl) ⟨51056, by rfl⟩) R102113
theorem R68087 : Reach 68087 := rs (se 1 (by rfl) ⟨51065, by rfl⟩) R102131
theorem R68107 : Reach 68107 := rs (se 1 (by rfl) ⟨51080, by rfl⟩) R102161
theorem R133643 : Reach 133643 := rs (se 1 (by rfl) ⟨100232, by rfl⟩) R200465
theorem R68119 : Reach 68119 := rs (se 1 (by rfl) ⟨51089, by rfl⟩) R102179
theorem R100889 : Reach 100889 := rs (se 2 (by rfl) ⟨37833, by rfl⟩) R75667
theorem R68139 : Reach 68139 := rs (se 1 (by rfl) ⟨51104, by rfl⟩) R102209
theorem R68151 : Reach 68151 := rs (se 1 (by rfl) ⟨51113, by rfl⟩) R102227
theorem R68171 : Reach 68171 := rs (se 1 (by rfl) ⟨51128, by rfl⟩) R102257
theorem R264779 : Reach 264779 := rs (se 1 (by rfl) ⟨198584, by rfl⟩) R397169
theorem R68183 : Reach 68183 := rs (se 1 (by rfl) ⟨51137, by rfl⟩) R102275
theorem R68203 : Reach 68203 := rs (se 1 (by rfl) ⟨51152, by rfl⟩) R102305
theorem R68215 : Reach 68215 := rs (se 1 (by rfl) ⟨51161, by rfl⟩) R102323
theorem R101003 : Reach 101003 := rs (se 1 (by rfl) ⟨75752, by rfl⟩) R151505
theorem R68235 : Reach 68235 := rs (se 1 (by rfl) ⟨51176, by rfl⟩) R102353
theorem R101015 : Reach 101015 := rs (se 1 (by rfl) ⟨75761, by rfl⟩) R151523
theorem R68247 : Reach 68247 := rs (se 1 (by rfl) ⟨51185, by rfl⟩) R102371
theorem R68267 : Reach 68267 := rs (se 1 (by rfl) ⟨51200, by rfl⟩) R102401
theorem R68279 : Reach 68279 := rs (se 1 (by rfl) ⟨51209, by rfl⟩) R102419
theorem R133825 : Reach 133825 := rs (se 2 (by rfl) ⟨50184, by rfl⟩) R100369
theorem R68299 : Reach 68299 := rs (se 1 (by rfl) ⟨51224, by rfl⟩) R102449
theorem R68311 : Reach 68311 := rs (se 1 (by rfl) ⟨51233, by rfl⟩) R102467
theorem R101081 : Reach 101081 := rs (se 2 (by rfl) ⟨37905, by rfl⟩) R75811
theorem R68331 : Reach 68331 := rs (se 1 (by rfl) ⟨51248, by rfl⟩) R102497
theorem R68343 : Reach 68343 := rs (se 1 (by rfl) ⟨51257, by rfl⟩) R102515
theorem R68363 : Reach 68363 := rs (se 1 (by rfl) ⟨51272, by rfl⟩) R102545
theorem R264977 : Reach 264977 := rs (se 2 (by rfl) ⟨99366, by rfl⟩) R198733
theorem R68375 : Reach 68375 := rs (se 1 (by rfl) ⟨51281, by rfl⟩) R102563
theorem R297751 : Reach 297751 := rs (se 1 (by rfl) ⟨223313, by rfl⟩) R446627
theorem R68395 : Reach 68395 := rs (se 1 (by rfl) ⟨51296, by rfl⟩) R102593
theorem R68407 : Reach 68407 := rs (se 1 (by rfl) ⟨51305, by rfl⟩) R102611
theorem R101195 : Reach 101195 := rs (se 1 (by rfl) ⟨75896, by rfl⟩) R151793
theorem R68427 : Reach 68427 := rs (se 1 (by rfl) ⟨51320, by rfl⟩) R102641
theorem R101207 : Reach 101207 := rs (se 1 (by rfl) ⟨75905, by rfl⟩) R151811
theorem R68439 : Reach 68439 := rs (se 1 (by rfl) ⟨51329, by rfl⟩) R102659
theorem R68459 : Reach 68459 := rs (se 1 (by rfl) ⟨51344, by rfl⟩) R102689
theorem R68471 : Reach 68471 := rs (se 1 (by rfl) ⟨51353, by rfl⟩) R102707
theorem R68491 : Reach 68491 := rs (se 1 (by rfl) ⟨51368, by rfl⟩) R102737
theorem R68503 : Reach 68503 := rs (se 1 (by rfl) ⟨51377, by rfl⟩) R102755
theorem R101273 : Reach 101273 := rs (se 2 (by rfl) ⟨37977, by rfl⟩) R75955
theorem R68523 : Reach 68523 := rs (se 1 (by rfl) ⟨51392, by rfl⟩) R102785
theorem R396211 : Reach 396211 := rs (se 1 (by rfl) ⟨297158, by rfl⟩) R594317
theorem R68535 : Reach 68535 := rs (se 1 (by rfl) ⟨51401, by rfl⟩) R102803
theorem R68555 : Reach 68555 := rs (se 1 (by rfl) ⟨51416, by rfl⟩) R102833
theorem R527309 : Reach 527309 := rs (se 3 (by rfl) ⟨98870, by rfl⟩) R197741
theorem R68567 : Reach 68567 := rs (se 1 (by rfl) ⟨51425, by rfl⟩) R102851
theorem R68587 : Reach 68587 := rs (se 1 (by rfl) ⟨51440, by rfl⟩) R102881
theorem R68599 : Reach 68599 := rs (se 1 (by rfl) ⟨51449, by rfl⟩) R102899
theorem R101387 : Reach 101387 := rs (se 1 (by rfl) ⟨76040, by rfl⟩) R152081
theorem R68619 : Reach 68619 := rs (se 1 (by rfl) ⟨51464, by rfl⟩) R102929
theorem R101399 : Reach 101399 := rs (se 1 (by rfl) ⟨76049, by rfl⟩) R152099
theorem R68631 : Reach 68631 := rs (se 1 (by rfl) ⟨51473, by rfl⟩) R102947
theorem R68651 : Reach 68651 := rs (se 1 (by rfl) ⟨51488, by rfl⟩) R102977
theorem R68663 : Reach 68663 := rs (se 1 (by rfl) ⟨51497, by rfl⟩) R102995
theorem R68683 : Reach 68683 := rs (se 1 (by rfl) ⟨51512, by rfl⟩) R103025
theorem R232523 : Reach 232523 := rs (se 1 (by rfl) ⟨174392, by rfl⟩) R348785
theorem R68695 : Reach 68695 := rs (se 1 (by rfl) ⟨51521, by rfl⟩) R103043
theorem R101465 : Reach 101465 := rs (se 2 (by rfl) ⟨38049, by rfl⟩) R76099
theorem R68715 : Reach 68715 := rs (se 1 (by rfl) ⟨51536, by rfl⟩) R103073
theorem R68727 : Reach 68727 := rs (se 1 (by rfl) ⟨51545, by rfl⟩) R103091
theorem R134273 : Reach 134273 := rs (se 2 (by rfl) ⟨50352, by rfl⟩) R100705
theorem R68747 : Reach 68747 := rs (se 1 (by rfl) ⟨51560, by rfl⟩) R103121
theorem R68759 : Reach 68759 := rs (se 1 (by rfl) ⟨51569, by rfl⟩) R103139
theorem R68779 : Reach 68779 := rs (se 1 (by rfl) ⟨51584, by rfl⟩) R103169
theorem R68791 : Reach 68791 := rs (se 1 (by rfl) ⟨51593, by rfl⟩) R103187
theorem R101579 : Reach 101579 := rs (se 1 (by rfl) ⟨76184, by rfl⟩) R152369
theorem R68811 : Reach 68811 := rs (se 1 (by rfl) ⟨51608, by rfl⟩) R103217
theorem R199883 : Reach 199883 := rs (se 1 (by rfl) ⟨149912, by rfl⟩) R299825
theorem R101591 : Reach 101591 := rs (se 1 (by rfl) ⟨76193, by rfl⟩) R152387
theorem R68823 : Reach 68823 := rs (se 1 (by rfl) ⟨51617, by rfl⟩) R103235
theorem R68843 : Reach 68843 := rs (se 1 (by rfl) ⟨51632, by rfl⟩) R103265
theorem R68855 : Reach 68855 := rs (se 1 (by rfl) ⟨51641, by rfl⟩) R103283
theorem R68875 : Reach 68875 := rs (se 1 (by rfl) ⟨51656, by rfl⟩) R103313
theorem R68887 : Reach 68887 := rs (se 1 (by rfl) ⟨51665, by rfl⟩) R103331
theorem R101657 : Reach 101657 := rs (se 2 (by rfl) ⟨38121, by rfl⟩) R76243
theorem R68907 : Reach 68907 := rs (se 1 (by rfl) ⟨51680, by rfl⟩) R103361
theorem R68919 : Reach 68919 := rs (se 1 (by rfl) ⟨51689, by rfl⟩) R103379
theorem R68939 : Reach 68939 := rs (se 1 (by rfl) ⟨51704, by rfl⟩) R103409
theorem R68951 : Reach 68951 := rs (se 1 (by rfl) ⟨51713, by rfl⟩) R103427
theorem R232793 : Reach 232793 := rs (se 2 (by rfl) ⟨87297, by rfl⟩) R174595
theorem R68971 : Reach 68971 := rs (se 1 (by rfl) ⟨51728, by rfl⟩) R103457
theorem R68983 : Reach 68983 := rs (se 1 (by rfl) ⟨51737, by rfl⟩) R103475
theorem R101771 : Reach 101771 := rs (se 1 (by rfl) ⟨76328, by rfl⟩) R152657
theorem R69003 : Reach 69003 := rs (se 1 (by rfl) ⟨51752, by rfl⟩) R103505
theorem R101783 : Reach 101783 := rs (se 1 (by rfl) ⟨76337, by rfl⟩) R152675
theorem R69015 : Reach 69015 := rs (se 1 (by rfl) ⟨51761, by rfl⟩) R103523
theorem R69035 : Reach 69035 := rs (se 1 (by rfl) ⟨51776, by rfl⟩) R103553
theorem R527795 : Reach 527795 := rs (se 1 (by rfl) ⟨395846, by rfl⟩) R791693
theorem R69047 : Reach 69047 := rs (se 1 (by rfl) ⟨51785, by rfl⟩) R103571
theorem R69067 : Reach 69067 := rs (se 1 (by rfl) ⟨51800, by rfl⟩) R103601
theorem R69079 : Reach 69079 := rs (se 1 (by rfl) ⟨51809, by rfl⟩) R103619
theorem R101849 : Reach 101849 := rs (se 2 (by rfl) ⟨38193, by rfl⟩) R76387
theorem R134615 : Reach 134615 := rs (se 1 (by rfl) ⟨100961, by rfl⟩) R201923
theorem R69099 : Reach 69099 := rs (se 1 (by rfl) ⟨51824, by rfl⟩) R103649
theorem R69111 : Reach 69111 := rs (se 1 (by rfl) ⟨51833, by rfl⟩) R103667
theorem R69131 : Reach 69131 := rs (se 1 (by rfl) ⟨51848, by rfl⟩) R103697
theorem R265751 : Reach 265751 := rs (se 1 (by rfl) ⟨199313, by rfl⟩) R398627
theorem R69143 : Reach 69143 := rs (se 1 (by rfl) ⟨51857, by rfl⟩) R103715
theorem R69163 : Reach 69163 := rs (se 1 (by rfl) ⟨51872, by rfl⟩) R103745
theorem R69175 : Reach 69175 := rs (se 1 (by rfl) ⟨51881, by rfl⟩) R103763
theorem R101963 : Reach 101963 := rs (se 1 (by rfl) ⟨76472, by rfl⟩) R152945
theorem R69195 : Reach 69195 := rs (se 1 (by rfl) ⟨51896, by rfl⟩) R103793
theorem R101975 : Reach 101975 := rs (se 1 (by rfl) ⟨76481, by rfl⟩) R152963
theorem R69207 : Reach 69207 := rs (se 1 (by rfl) ⟨51905, by rfl⟩) R103811
theorem R69227 : Reach 69227 := rs (se 1 (by rfl) ⟨51920, by rfl⟩) R103841
theorem R69239 : Reach 69239 := rs (se 1 (by rfl) ⟨51929, by rfl⟩) R103859
theorem R69259 : Reach 69259 := rs (se 1 (by rfl) ⟨51944, by rfl⟩) R103889
theorem R69271 : Reach 69271 := rs (se 1 (by rfl) ⟨51953, by rfl⟩) R103907
theorem R102041 : Reach 102041 := rs (se 2 (by rfl) ⟨38265, by rfl⟩) R76531
theorem R69291 : Reach 69291 := rs (se 1 (by rfl) ⟨51968, by rfl⟩) R103937
theorem R69303 : Reach 69303 := rs (se 1 (by rfl) ⟨51977, by rfl⟩) R103955
theorem R69323 : Reach 69323 := rs (se 1 (by rfl) ⟨51992, by rfl⟩) R103985
theorem R69335 : Reach 69335 := rs (se 1 (by rfl) ⟨52001, by rfl⟩) R104003
theorem R265949 : Reach 265949 := rs (se 3 (by rfl) ⟨49865, by rfl⟩) R99731
theorem R69355 : Reach 69355 := rs (se 1 (by rfl) ⟨52016, by rfl⟩) R104033
theorem R69367 : Reach 69367 := rs (se 1 (by rfl) ⟨52025, by rfl⟩) R104051
theorem R102155 : Reach 102155 := rs (se 1 (by rfl) ⟨76616, by rfl⟩) R153233
theorem R69387 : Reach 69387 := rs (se 1 (by rfl) ⟨52040, by rfl⟩) R104081
theorem R102167 : Reach 102167 := rs (se 1 (by rfl) ⟨76625, by rfl⟩) R153251
theorem R69399 : Reach 69399 := rs (se 1 (by rfl) ⟨52049, by rfl⟩) R104099
theorem R69419 : Reach 69419 := rs (se 1 (by rfl) ⟨52064, by rfl⟩) R104129
theorem R69431 : Reach 69431 := rs (se 1 (by rfl) ⟨52073, by rfl⟩) R104147
theorem R69451 : Reach 69451 := rs (se 1 (by rfl) ⟨52088, by rfl⟩) R104177
theorem R69463 : Reach 69463 := rs (se 1 (by rfl) ⟨52097, by rfl⟩) R104195
theorem R102233 : Reach 102233 := rs (se 2 (by rfl) ⟨38337, by rfl⟩) R76675
theorem R69483 : Reach 69483 := rs (se 1 (by rfl) ⟨52112, by rfl⟩) R104225
theorem R69495 : Reach 69495 := rs (se 1 (by rfl) ⟨52121, by rfl⟩) R104243
theorem R69515 : Reach 69515 := rs (se 1 (by rfl) ⟨52136, by rfl⟩) R104273
theorem R69527 : Reach 69527 := rs (se 1 (by rfl) ⟨52145, by rfl⟩) R104291
theorem R69547 : Reach 69547 := rs (se 1 (by rfl) ⟨52160, by rfl⟩) R104321
theorem R69559 : Reach 69559 := rs (se 1 (by rfl) ⟨52169, by rfl⟩) R104339
theorem R102347 : Reach 102347 := rs (se 1 (by rfl) ⟨76760, by rfl⟩) R153521
theorem R69579 : Reach 69579 := rs (se 1 (by rfl) ⟨52184, by rfl⟩) R104369
theorem R102359 : Reach 102359 := rs (se 1 (by rfl) ⟨76769, by rfl⟩) R153539
theorem R69591 : Reach 69591 := rs (se 1 (by rfl) ⟨52193, by rfl⟩) R104387
theorem R69611 : Reach 69611 := rs (se 1 (by rfl) ⟨52208, by rfl⟩) R104417
theorem R69623 : Reach 69623 := rs (se 1 (by rfl) ⟨52217, by rfl⟩) R104435
theorem R69643 : Reach 69643 := rs (se 1 (by rfl) ⟨52232, by rfl⟩) R104465
theorem R233495 : Reach 233495 := rs (se 1 (by rfl) ⟨175121, by rfl⟩) R350243
theorem R69655 : Reach 69655 := rs (se 1 (by rfl) ⟨52241, by rfl⟩) R104483
theorem R102425 : Reach 102425 := rs (se 2 (by rfl) ⟨38409, by rfl⟩) R76819
theorem R69675 : Reach 69675 := rs (se 1 (by rfl) ⟨52256, by rfl⟩) R104513
theorem R69687 : Reach 69687 := rs (se 1 (by rfl) ⟨52265, by rfl⟩) R104531
theorem R69707 : Reach 69707 := rs (se 1 (by rfl) ⟨52280, by rfl⟩) R104561
theorem R69719 : Reach 69719 := rs (se 1 (by rfl) ⟨52289, by rfl⟩) R104579
theorem R69739 : Reach 69739 := rs (se 1 (by rfl) ⟨52304, by rfl⟩) R104609
theorem R69751 : Reach 69751 := rs (se 1 (by rfl) ⟨52313, by rfl⟩) R104627
theorem R364675 : Reach 364675 := rs (se 1 (by rfl) ⟨273506, by rfl⟩) R547013
theorem R102539 : Reach 102539 := rs (se 1 (by rfl) ⟨76904, by rfl⟩) R153809
theorem R69771 : Reach 69771 := rs (se 1 (by rfl) ⟨52328, by rfl⟩) R104657
theorem R2330765 : Reach 2330765 := rs (se 3 (by rfl) ⟨437018, by rfl⟩) R874037
theorem R102551 : Reach 102551 := rs (se 1 (by rfl) ⟨76913, by rfl⟩) R153827
theorem R69783 : Reach 69783 := rs (se 1 (by rfl) ⟨52337, by rfl⟩) R104675
theorem R69803 : Reach 69803 := rs (se 1 (by rfl) ⟨52352, by rfl⟩) R104705
theorem R69815 : Reach 69815 := rs (se 1 (by rfl) ⟨52361, by rfl⟩) R104723
theorem R69835 : Reach 69835 := rs (se 1 (by rfl) ⟨52376, by rfl⟩) R104753
theorem R69847 : Reach 69847 := rs (se 1 (by rfl) ⟨52385, by rfl⟩) R104771
theorem R102617 : Reach 102617 := rs (se 2 (by rfl) ⟨38481, by rfl⟩) R76963
theorem R69867 : Reach 69867 := rs (se 1 (by rfl) ⟨52400, by rfl⟩) R104801
theorem R69879 : Reach 69879 := rs (se 1 (by rfl) ⟨52409, by rfl⟩) R104819
theorem R69899 : Reach 69899 := rs (se 1 (by rfl) ⟨52424, by rfl⟩) R104849
theorem R69911 : Reach 69911 := rs (se 1 (by rfl) ⟨52433, by rfl⟩) R104867
theorem R69931 : Reach 69931 := rs (se 1 (by rfl) ⟨52448, by rfl⟩) R104897
theorem R69943 : Reach 69943 := rs (se 1 (by rfl) ⟨52457, by rfl⟩) R104915
theorem R102731 : Reach 102731 := rs (se 1 (by rfl) ⟨77048, by rfl⟩) R154097
theorem R69963 : Reach 69963 := rs (se 1 (by rfl) ⟨52472, by rfl⟩) R104945
theorem R102743 : Reach 102743 := rs (se 1 (by rfl) ⟨77057, by rfl⟩) R154115
theorem R69975 : Reach 69975 := rs (se 1 (by rfl) ⟨52481, by rfl⟩) R104963
theorem R397669 : Reach 397669 := rs (se 4 (by rfl) ⟨37281, by rfl⟩) R74563
theorem R69995 : Reach 69995 := rs (se 1 (by rfl) ⟨52496, by rfl⟩) R104993
theorem R70007 : Reach 70007 := rs (se 1 (by rfl) ⟨52505, by rfl⟩) R105011
theorem R70027 : Reach 70027 := rs (se 1 (by rfl) ⟨52520, by rfl⟩) R105041
theorem R70039 : Reach 70039 := rs (se 1 (by rfl) ⟨52529, by rfl⟩) R105059
theorem R102809 : Reach 102809 := rs (se 2 (by rfl) ⟨38553, by rfl⟩) R77107
theorem R70059 : Reach 70059 := rs (se 1 (by rfl) ⟨52544, by rfl⟩) R105089
theorem R70071 : Reach 70071 := rs (se 1 (by rfl) ⟨52553, by rfl⟩) R105107
theorem R70091 : Reach 70091 := rs (se 1 (by rfl) ⟨52568, by rfl⟩) R105137
theorem R70103 : Reach 70103 := rs (se 1 (by rfl) ⟨52577, by rfl⟩) R105155
theorem R70123 : Reach 70123 := rs (se 1 (by rfl) ⟨52592, by rfl⟩) R105185
theorem R70135 : Reach 70135 := rs (se 1 (by rfl) ⟨52601, by rfl⟩) R105203
theorem R102923 : Reach 102923 := rs (se 1 (by rfl) ⟨77192, by rfl⟩) R154385
theorem R70155 : Reach 70155 := rs (se 1 (by rfl) ⟨52616, by rfl⟩) R105233
theorem R102935 : Reach 102935 := rs (se 1 (by rfl) ⟨77201, by rfl⟩) R154403
theorem R70167 : Reach 70167 := rs (se 1 (by rfl) ⟨52625, by rfl⟩) R105251
theorem R889379 : Reach 889379 := rs (se 1 (by rfl) ⟨667034, by rfl⟩) R1334069
theorem R70187 : Reach 70187 := rs (se 1 (by rfl) ⟨52640, by rfl⟩) R105281
theorem R234035 : Reach 234035 := rs (se 1 (by rfl) ⟨175526, by rfl⟩) R351053
theorem R70199 : Reach 70199 := rs (se 1 (by rfl) ⟨52649, by rfl⟩) R105299
theorem R70219 : Reach 70219 := rs (se 1 (by rfl) ⟨52664, by rfl⟩) R105329
theorem R70231 : Reach 70231 := rs (se 1 (by rfl) ⟨52673, by rfl⟩) R105347
theorem R103001 : Reach 103001 := rs (se 2 (by rfl) ⟨38625, by rfl⟩) R77251
theorem R70251 : Reach 70251 := rs (se 1 (by rfl) ⟨52688, by rfl⟩) R105377
theorem R70263 : Reach 70263 := rs (se 1 (by rfl) ⟨52697, by rfl⟩) R105395
theorem R70283 : Reach 70283 := rs (se 1 (by rfl) ⟨52712, by rfl⟩) R105425
theorem R70295 : Reach 70295 := rs (se 1 (by rfl) ⟨52721, by rfl⟩) R105443
theorem R70315 : Reach 70315 := rs (se 1 (by rfl) ⟨52736, by rfl⟩) R105473
theorem R430771 : Reach 430771 := rs (se 1 (by rfl) ⟨323078, by rfl⟩) R646157
theorem R70327 : Reach 70327 := rs (se 1 (by rfl) ⟨52745, by rfl⟩) R105491
theorem R103115 : Reach 103115 := rs (se 1 (by rfl) ⟨77336, by rfl⟩) R154673
theorem R70347 : Reach 70347 := rs (se 1 (by rfl) ⟨52760, by rfl⟩) R105521
theorem R103127 : Reach 103127 := rs (se 1 (by rfl) ⟨77345, by rfl⟩) R154691
theorem R70359 : Reach 70359 := rs (se 1 (by rfl) ⟨52769, by rfl⟩) R105539
theorem R70379 : Reach 70379 := rs (se 1 (by rfl) ⟨52784, by rfl⟩) R105569
theorem R70391 : Reach 70391 := rs (se 1 (by rfl) ⟨52793, by rfl⟩) R105587
theorem R70411 : Reach 70411 := rs (se 1 (by rfl) ⟨52808, by rfl⟩) R105617
theorem R70423 : Reach 70423 := rs (se 1 (by rfl) ⟨52817, by rfl⟩) R105635
theorem R103193 : Reach 103193 := rs (se 2 (by rfl) ⟨38697, by rfl⟩) R77395
theorem R70443 : Reach 70443 := rs (se 1 (by rfl) ⟨52832, by rfl⟩) R105665
theorem R2495285 : Reach 2495285 := rs (se 5 (by rfl) ⟨116966, by rfl⟩) R233933
theorem R70455 : Reach 70455 := rs (se 1 (by rfl) ⟨52841, by rfl⟩) R105683
theorem R201523 : Reach 201523 := rs (se 1 (by rfl) ⟨151142, by rfl⟩) R302285
theorem R234305 : Reach 234305 := rs (se 2 (by rfl) ⟨87864, by rfl⟩) R175729
theorem R70475 : Reach 70475 := rs (se 1 (by rfl) ⟨52856, by rfl⟩) R105713
theorem R70487 : Reach 70487 := rs (se 1 (by rfl) ⟨52865, by rfl⟩) R105731
theorem R529253 : Reach 529253 := rs (se 4 (by rfl) ⟨49617, by rfl⟩) R99235
theorem R70507 : Reach 70507 := rs (se 1 (by rfl) ⟨52880, by rfl⟩) R105761
theorem R70519 : Reach 70519 := rs (se 1 (by rfl) ⟨52889, by rfl⟩) R105779
theorem R103307 : Reach 103307 := rs (se 1 (by rfl) ⟨77480, by rfl⟩) R154961
theorem R70539 : Reach 70539 := rs (se 1 (by rfl) ⟨52904, by rfl⟩) R105809
theorem R103319 : Reach 103319 := rs (se 1 (by rfl) ⟨77489, by rfl⟩) R154979
theorem R70551 : Reach 70551 := rs (se 1 (by rfl) ⟨52913, by rfl⟩) R105827
theorem R70571 : Reach 70571 := rs (se 1 (by rfl) ⟨52928, by rfl⟩) R105857
theorem R70583 : Reach 70583 := rs (se 1 (by rfl) ⟨52937, by rfl⟩) R105875
theorem R70603 : Reach 70603 := rs (se 1 (by rfl) ⟨52952, by rfl⟩) R105905
theorem R70615 : Reach 70615 := rs (se 1 (by rfl) ⟨52961, by rfl⟩) R105923
theorem R103385 : Reach 103385 := rs (se 2 (by rfl) ⟨38769, by rfl⟩) R77539
theorem R70635 : Reach 70635 := rs (se 1 (by rfl) ⟨52976, by rfl⟩) R105953
theorem R70647 : Reach 70647 := rs (se 1 (by rfl) ⟨52985, by rfl⟩) R105971
theorem R70667 : Reach 70667 := rs (se 1 (by rfl) ⟨53000, by rfl⟩) R106001
theorem R70679 : Reach 70679 := rs (se 1 (by rfl) ⟨53009, by rfl⟩) R106019
theorem R70699 : Reach 70699 := rs (se 1 (by rfl) ⟨53024, by rfl⟩) R106049
theorem R70711 : Reach 70711 := rs (se 1 (by rfl) ⟨53033, by rfl⟩) R106067
theorem R103499 : Reach 103499 := rs (se 1 (by rfl) ⟨77624, by rfl⟩) R155249
theorem R70731 : Reach 70731 := rs (se 1 (by rfl) ⟨53048, by rfl⟩) R106097
theorem R103511 : Reach 103511 := rs (se 1 (by rfl) ⟨77633, by rfl⟩) R155267
theorem R70743 : Reach 70743 := rs (se 1 (by rfl) ⟨53057, by rfl⟩) R106115
theorem R70763 : Reach 70763 := rs (se 1 (by rfl) ⟨53072, by rfl⟩) R106145
theorem R70775 : Reach 70775 := rs (se 1 (by rfl) ⟨53081, by rfl⟩) R106163
theorem R660611 : Reach 660611 := rs (se 1 (by rfl) ⟨495458, by rfl⟩) R990917
theorem R70795 : Reach 70795 := rs (se 1 (by rfl) ⟨53096, by rfl⟩) R106193
theorem R70807 : Reach 70807 := rs (se 1 (by rfl) ⟨53105, by rfl⟩) R106211
theorem R103577 : Reach 103577 := rs (se 2 (by rfl) ⟨38841, by rfl⟩) R77683
theorem R70827 : Reach 70827 := rs (se 1 (by rfl) ⟨53120, by rfl⟩) R106241
theorem R70839 : Reach 70839 := rs (se 1 (by rfl) ⟨53129, by rfl⟩) R106259
theorem R70859 : Reach 70859 := rs (se 1 (by rfl) ⟨53144, by rfl⟩) R106289
theorem R70871 : Reach 70871 := rs (se 1 (by rfl) ⟨53153, by rfl⟩) R106307
theorem R70891 : Reach 70891 := rs (se 1 (by rfl) ⟨53168, by rfl⟩) R106337
theorem R70903 : Reach 70903 := rs (se 1 (by rfl) ⟨53177, by rfl⟩) R106355
theorem R103691 : Reach 103691 := rs (se 1 (by rfl) ⟨77768, by rfl⟩) R155537
theorem R70923 : Reach 70923 := rs (se 1 (by rfl) ⟨53192, by rfl⟩) R106385
theorem R103703 : Reach 103703 := rs (se 1 (by rfl) ⟨77777, by rfl⟩) R155555
theorem R70935 : Reach 70935 := rs (se 1 (by rfl) ⟨53201, by rfl⟩) R106403
theorem R70955 : Reach 70955 := rs (se 1 (by rfl) ⟨53216, by rfl⟩) R106433
theorem R70967 : Reach 70967 := rs (se 1 (by rfl) ⟨53225, by rfl⟩) R106451
theorem R529739 : Reach 529739 := rs (se 1 (by rfl) ⟨397304, by rfl⟩) R794609
theorem R70987 : Reach 70987 := rs (se 1 (by rfl) ⟨53240, by rfl⟩) R106481
theorem R70999 : Reach 70999 := rs (se 1 (by rfl) ⟨53249, by rfl⟩) R106499
theorem R103769 : Reach 103769 := rs (se 2 (by rfl) ⟨38913, by rfl⟩) R77827
theorem R234845 : Reach 234845 := rs (se 3 (by rfl) ⟨44033, by rfl⟩) R88067
theorem R71019 : Reach 71019 := rs (se 1 (by rfl) ⟨53264, by rfl⟩) R106529
theorem R71031 : Reach 71031 := rs (se 1 (by rfl) ⟨53273, by rfl⟩) R106547
theorem R71051 : Reach 71051 := rs (se 1 (by rfl) ⟨53288, by rfl⟩) R106577
theorem R300439 : Reach 300439 := rs (se 1 (by rfl) ⟨225329, by rfl⟩) R450659
theorem R71063 : Reach 71063 := rs (se 1 (by rfl) ⟨53297, by rfl⟩) R106595
theorem R71083 : Reach 71083 := rs (se 1 (by rfl) ⟨53312, by rfl⟩) R106625
theorem R71095 : Reach 71095 := rs (se 1 (by rfl) ⟨53321, by rfl⟩) R106643
theorem R103883 : Reach 103883 := rs (se 1 (by rfl) ⟨77912, by rfl⟩) R155825
theorem R71115 : Reach 71115 := rs (se 1 (by rfl) ⟨53336, by rfl⟩) R106673
theorem R103895 : Reach 103895 := rs (se 1 (by rfl) ⟨77921, by rfl⟩) R155843
theorem R300509 : Reach 300509 := rs (se 3 (by rfl) ⟨56345, by rfl⟩) R112691
theorem R103961 : Reach 103961 := rs (se 2 (by rfl) ⟨38985, by rfl⟩) R77971
theorem R136819 : Reach 136819 := rs (se 1 (by rfl) ⟨102614, by rfl⟩) R205229
theorem R267907 : Reach 267907 := rs (se 1 (by rfl) ⟨200930, by rfl⟩) R401861
theorem R104075 : Reach 104075 := rs (se 1 (by rfl) ⟨78056, by rfl⟩) R156113
theorem R104087 : Reach 104087 := rs (se 1 (by rfl) ⟨78065, by rfl⟩) R156131
theorem R104153 : Reach 104153 := rs (se 2 (by rfl) ⟨39057, by rfl⟩) R78115
theorem R104267 : Reach 104267 := rs (se 1 (by rfl) ⟨78200, by rfl⟩) R156401
theorem R104279 : Reach 104279 := rs (se 1 (by rfl) ⟨78209, by rfl⟩) R156419
theorem R104345 : Reach 104345 := rs (se 2 (by rfl) ⟨39129, by rfl⟩) R78259
theorem R268211 : Reach 268211 := rs (se 1 (by rfl) ⟨201158, by rfl⟩) R402317
theorem R104459 : Reach 104459 := rs (se 1 (by rfl) ⟨78344, by rfl⟩) R156689
theorem R104471 : Reach 104471 := rs (se 1 (by rfl) ⟨78353, by rfl⟩) R156707
theorem R71723 : Reach 71723 := rs (se 1 (by rfl) ⟨53792, by rfl⟩) R107585
theorem R170059 : Reach 170059 := rs (se 1 (by rfl) ⟨127544, by rfl⟩) R255089
theorem R137303 : Reach 137303 := rs (se 1 (by rfl) ⟨102977, by rfl⟩) R205955
theorem R104537 : Reach 104537 := rs (se 2 (by rfl) ⟨39201, by rfl⟩) R78403
theorem R497765 : Reach 497765 := rs (se 4 (by rfl) ⟨46665, by rfl⟩) R93331
theorem R104651 : Reach 104651 := rs (se 1 (by rfl) ⟨78488, by rfl⟩) R156977
theorem R301259 : Reach 301259 := rs (se 1 (by rfl) ⟨225944, by rfl⟩) R451889
theorem R104663 : Reach 104663 := rs (se 1 (by rfl) ⟨78497, by rfl⟩) R156995
theorem R170201 : Reach 170201 := rs (se 2 (by rfl) ⟨63825, by rfl⟩) R127651
theorem R104729 : Reach 104729 := rs (se 2 (by rfl) ⟨39273, by rfl⟩) R78547
theorem R268609 : Reach 268609 := rs (se 2 (by rfl) ⟨100728, by rfl⟩) R201457
theorem R104843 : Reach 104843 := rs (se 1 (by rfl) ⟨78632, by rfl⟩) R157265
theorem R104855 : Reach 104855 := rs (se 1 (by rfl) ⟨78641, by rfl⟩) R157283
theorem R235979 : Reach 235979 := rs (se 1 (by rfl) ⟨176984, by rfl⟩) R353969
theorem R104921 : Reach 104921 := rs (se 2 (by rfl) ⟨39345, by rfl⟩) R78691
theorem R301619 : Reach 301619 := rs (se 1 (by rfl) ⟨226214, by rfl⟩) R452429
theorem R268865 : Reach 268865 := rs (se 2 (by rfl) ⟨100824, by rfl⟩) R201649
theorem R105035 : Reach 105035 := rs (se 1 (by rfl) ⟨78776, by rfl⟩) R157553
theorem R105047 : Reach 105047 := rs (se 1 (by rfl) ⟨78785, by rfl⟩) R157571
theorem R137857 : Reach 137857 := rs (se 2 (by rfl) ⟨51696, by rfl⟩) R103393
theorem R105113 : Reach 105113 := rs (se 2 (by rfl) ⟨39417, by rfl⟩) R78835
theorem R170689 : Reach 170689 := rs (se 2 (by rfl) ⟨64008, by rfl⟩) R128017
theorem R236249 : Reach 236249 := rs (se 2 (by rfl) ⟨88593, by rfl⟩) R177187
theorem R105227 : Reach 105227 := rs (se 1 (by rfl) ⟨78920, by rfl⟩) R157841
theorem R105239 : Reach 105239 := rs (se 1 (by rfl) ⟨78929, by rfl⟩) R157859
theorem R105305 : Reach 105305 := rs (se 2 (by rfl) ⟨39489, by rfl⟩) R78979
theorem R596915 : Reach 596915 := rs (se 1 (by rfl) ⟨447686, by rfl⟩) R895373
theorem R105419 : Reach 105419 := rs (se 1 (by rfl) ⟨79064, by rfl⟩) R158129
theorem R105431 : Reach 105431 := rs (se 1 (by rfl) ⟨79073, by rfl⟩) R158147
theorem R498649 : Reach 498649 := rs (se 2 (by rfl) ⟨186993, by rfl⟩) R373987
theorem R1252313 : Reach 1252313 := rs (se 2 (by rfl) ⟨469617, by rfl⟩) R939235
theorem R171031 : Reach 171031 := rs (se 1 (by rfl) ⟨128273, by rfl⟩) R256547
theorem R105497 : Reach 105497 := rs (se 2 (by rfl) ⟨39561, by rfl⟩) R79123
theorem R105611 : Reach 105611 := rs (se 1 (by rfl) ⟨79208, by rfl⟩) R158417
theorem R105623 : Reach 105623 := rs (se 1 (by rfl) ⟨79217, by rfl⟩) R158435
theorem R105689 : Reach 105689 := rs (se 2 (by rfl) ⟨39633, by rfl⟩) R79267
theorem R597293 : Reach 597293 := rs (se 3 (by rfl) ⟨111992, by rfl⟩) R223985
theorem R105803 : Reach 105803 := rs (se 1 (by rfl) ⟨79352, by rfl⟩) R158705
theorem R105815 : Reach 105815 := rs (se 1 (by rfl) ⟨79361, by rfl⟩) R158723
theorem R73111 : Reach 73111 := rs (se 1 (by rfl) ⟨54833, by rfl⟩) R109667
theorem R236951 : Reach 236951 := rs (se 1 (by rfl) ⟨177713, by rfl⟩) R355427
theorem R105881 : Reach 105881 := rs (se 2 (by rfl) ⟨39705, by rfl⟩) R79411
theorem R171467 : Reach 171467 := rs (se 1 (by rfl) ⟨128600, by rfl⟩) R257201
theorem R105995 : Reach 105995 := rs (se 1 (by rfl) ⟨79496, by rfl⟩) R158993
theorem R106007 : Reach 106007 := rs (se 1 (by rfl) ⟨79505, by rfl⟩) R159011
theorem R106073 : Reach 106073 := rs (se 2 (by rfl) ⟨39777, by rfl⟩) R79555
theorem R204439 : Reach 204439 := rs (se 1 (by rfl) ⟨153329, by rfl⟩) R306659
theorem R106187 : Reach 106187 := rs (se 1 (by rfl) ⟨79640, by rfl⟩) R159281
theorem R106199 : Reach 106199 := rs (se 1 (by rfl) ⟨79649, by rfl⟩) R159299
theorem R106265 : Reach 106265 := rs (se 2 (by rfl) ⟨39849, by rfl⟩) R79699
theorem R171841 : Reach 171841 := rs (se 2 (by rfl) ⟨64440, by rfl⟩) R128881
theorem R106379 : Reach 106379 := rs (se 1 (by rfl) ⟨79784, by rfl⟩) R159569
theorem R106391 : Reach 106391 := rs (se 1 (by rfl) ⟨79793, by rfl⟩) R159587
theorem R237491 : Reach 237491 := rs (se 1 (by rfl) ⟨178118, by rfl⟩) R356237
theorem R106457 : Reach 106457 := rs (se 2 (by rfl) ⟨39921, by rfl⟩) R79843
theorem R499729 : Reach 499729 := rs (se 2 (by rfl) ⟨187398, by rfl⟩) R374797
theorem R106571 : Reach 106571 := rs (se 1 (by rfl) ⟨79928, by rfl⟩) R159857
theorem R106583 : Reach 106583 := rs (se 1 (by rfl) ⟨79937, by rfl⟩) R159875
theorem R106649 : Reach 106649 := rs (se 2 (by rfl) ⟨39993, by rfl⟩) R79987
theorem R237761 : Reach 237761 := rs (se 2 (by rfl) ⟨89160, by rfl⟩) R178321
theorem R73931 : Reach 73931 := rs (se 1 (by rfl) ⟨55448, by rfl⟩) R110897
theorem R74059 : Reach 74059 := rs (se 1 (by rfl) ⟨55544, by rfl⟩) R111089
theorem R237917 : Reach 237917 := rs (se 3 (by rfl) ⟨44609, by rfl⟩) R89219
theorem R172439 : Reach 172439 := rs (se 1 (by rfl) ⟨129329, by rfl⟩) R258659
theorem R303709 : Reach 303709 := rs (se 3 (by rfl) ⟨56945, by rfl⟩) R113891
theorem R238301 : Reach 238301 := rs (se 3 (by rfl) ⟨44681, by rfl⟩) R89363
theorem R500741 : Reach 500741 := rs (se 4 (by rfl) ⟨46944, by rfl⟩) R93889
theorem R74935 : Reach 74935 := rs (se 1 (by rfl) ⟨56201, by rfl⟩) R112403
theorem R173249 : Reach 173249 := rs (se 2 (by rfl) ⟨64968, by rfl⟩) R129937
theorem R402961 : Reach 402961 := rs (se 2 (by rfl) ⟨151110, by rfl⟩) R302221
theorem R173785 : Reach 173785 := rs (se 2 (by rfl) ⟨65169, by rfl⟩) R130339
theorem R75595 : Reach 75595 := rs (se 1 (by rfl) ⟨56696, by rfl⟩) R113393
theorem R239435 : Reach 239435 := rs (se 1 (by rfl) ⟨179576, by rfl⟩) R359153
theorem R75691 : Reach 75691 := rs (se 1 (by rfl) ⟨56768, by rfl⟩) R113537
theorem R75703 : Reach 75703 := rs (se 1 (by rfl) ⟨56777, by rfl⟩) R113555
theorem R2009123 : Reach 2009123 := rs (se 1 (by rfl) ⟨1506842, by rfl⟩) R3013685
theorem R403501 : Reach 403501 := rs (se 3 (by rfl) ⟨75656, by rfl⟩) R151313
theorem R239705 : Reach 239705 := rs (se 2 (by rfl) ⟨89889, by rfl⟩) R179779
theorem R75883 : Reach 75883 := rs (se 1 (by rfl) ⟨56912, by rfl⟩) R113825
theorem R75991 : Reach 75991 := rs (se 1 (by rfl) ⟨56993, by rfl⟩) R113987
theorem R76171 : Reach 76171 := rs (se 1 (by rfl) ⟨57128, by rfl⟩) R114257
theorem R76235 : Reach 76235 := rs (se 1 (by rfl) ⟨57176, by rfl⟩) R114353
theorem R272857 : Reach 272857 := rs (se 2 (by rfl) ⟨102321, by rfl⟩) R204643
theorem R76279 : Reach 76279 := rs (se 1 (by rfl) ⟨57209, by rfl⟩) R114419
theorem R535085 : Reach 535085 := rs (se 3 (by rfl) ⟨100328, by rfl⟩) R200657
theorem R76459 : Reach 76459 := rs (se 1 (by rfl) ⟨57344, by rfl⟩) R114689
theorem R76567 : Reach 76567 := rs (se 1 (by rfl) ⟨57425, by rfl⟩) R114851
theorem R240407 : Reach 240407 := rs (se 1 (by rfl) ⟨180305, by rfl⟩) R360611
theorem R174899 : Reach 174899 := rs (se 1 (by rfl) ⟨131174, by rfl⟩) R262349
theorem R76747 : Reach 76747 := rs (se 1 (by rfl) ⟨57560, by rfl⟩) R115121
theorem R994265 : Reach 994265 := rs (se 2 (by rfl) ⟨372849, by rfl⟩) R745699
theorem R142361 : Reach 142361 := rs (se 2 (by rfl) ⟨53385, by rfl⟩) R106771
theorem R76855 : Reach 76855 := rs (se 1 (by rfl) ⟨57641, by rfl⟩) R115283
theorem R175193 : Reach 175193 := rs (se 2 (by rfl) ⟨65697, by rfl⟩) R131395
theorem R470195 : Reach 470195 := rs (se 1 (by rfl) ⟨352646, by rfl⟩) R705293
theorem R77035 : Reach 77035 := rs (se 1 (by rfl) ⟨57776, by rfl⟩) R115553
theorem R1682693 : Reach 1682693 := rs (se 4 (by rfl) ⟨157752, by rfl⟩) R315505
theorem R77143 : Reach 77143 := rs (se 1 (by rfl) ⟨57857, by rfl⟩) R115715
theorem R77323 : Reach 77323 := rs (se 1 (by rfl) ⟨57992, by rfl⟩) R115985
theorem R372269 : Reach 372269 := rs (se 3 (by rfl) ⟨69800, by rfl⟩) R139601
theorem R274013 : Reach 274013 := rs (se 3 (by rfl) ⟨51377, by rfl⟩) R102755
theorem R77431 : Reach 77431 := rs (se 1 (by rfl) ⟨58073, by rfl⟩) R116147
theorem R110231 : Reach 110231 := rs (se 1 (by rfl) ⟨82673, by rfl⟩) R165347
theorem R77611 : Reach 77611 := rs (se 1 (by rfl) ⟨58208, by rfl⟩) R116417
theorem R110423 : Reach 110423 := rs (se 1 (by rfl) ⟨82817, by rfl⟩) R165635
theorem R241501 : Reach 241501 := rs (se 3 (by rfl) ⟨45281, by rfl⟩) R90563
theorem R77719 : Reach 77719 := rs (se 1 (by rfl) ⟨58289, by rfl⟩) R116579
theorem R340033 : Reach 340033 := rs (se 2 (by rfl) ⟨127512, by rfl⟩) R255025
theorem R77899 : Reach 77899 := rs (se 1 (by rfl) ⟨58424, by rfl⟩) R116849
theorem R340147 : Reach 340147 := rs (se 1 (by rfl) ⟨255110, by rfl⟩) R510221
theorem R78007 : Reach 78007 := rs (se 1 (by rfl) ⟨58505, by rfl⟩) R117011
theorem R78187 : Reach 78187 := rs (se 1 (by rfl) ⟨58640, by rfl⟩) R117281
theorem R110987 : Reach 110987 := rs (se 1 (by rfl) ⟨83240, by rfl⟩) R166481
theorem R78295 : Reach 78295 := rs (se 1 (by rfl) ⟨58721, by rfl⟩) R117443
theorem R111179 : Reach 111179 := rs (se 1 (by rfl) ⟨83384, by rfl⟩) R166769
theorem R78475 : Reach 78475 := rs (se 1 (by rfl) ⟨58856, by rfl⟩) R117713
theorem R111307 : Reach 111307 := rs (se 1 (by rfl) ⟨83480, by rfl⟩) R166961
theorem R176843 : Reach 176843 := rs (se 1 (by rfl) ⟨132632, by rfl⟩) R265265
theorem R78583 : Reach 78583 := rs (se 1 (by rfl) ⟨58937, by rfl⟩) R117875
theorem R78763 : Reach 78763 := rs (se 1 (by rfl) ⟨59072, by rfl⟩) R118145
theorem R341009 : Reach 341009 := rs (se 2 (by rfl) ⟨127878, by rfl⟩) R255757
theorem R78871 : Reach 78871 := rs (se 1 (by rfl) ⟨59153, by rfl⟩) R118307
theorem R78967 : Reach 78967 := rs (se 1 (by rfl) ⟨59225, by rfl⟩) R118451
theorem R341171 : Reach 341171 := rs (se 1 (by rfl) ⟨255878, by rfl⟩) R511757
theorem R79051 : Reach 79051 := rs (se 1 (by rfl) ⟨59288, by rfl⟩) R118577
theorem R79159 : Reach 79159 := rs (se 1 (by rfl) ⟨59369, by rfl⟩) R118739
theorem R111947 : Reach 111947 := rs (se 1 (by rfl) ⟨83960, by rfl⟩) R167921
theorem R308573 : Reach 308573 := rs (se 3 (by rfl) ⟨57857, by rfl⟩) R115715
theorem R112025 : Reach 112025 := rs (se 2 (by rfl) ⟨42009, by rfl⟩) R84019
theorem R439769 : Reach 439769 := rs (se 2 (by rfl) ⟨164913, by rfl⟩) R329827
theorem R308701 : Reach 308701 := rs (se 3 (by rfl) ⟨57881, by rfl⟩) R115763
theorem R79339 : Reach 79339 := rs (se 1 (by rfl) ⟨59504, by rfl⟩) R119009
theorem R505379 : Reach 505379 := rs (se 1 (by rfl) ⟨379034, by rfl⟩) R758069
theorem R243251 : Reach 243251 := rs (se 1 (by rfl) ⟨182438, by rfl⟩) R364877
theorem R79447 : Reach 79447 := rs (se 1 (by rfl) ⟨59585, by rfl⟩) R119171
theorem R341597 : Reach 341597 := rs (se 3 (by rfl) ⟨64049, by rfl⟩) R128099
theorem R177815 : Reach 177815 := rs (se 1 (by rfl) ⟨133361, by rfl⟩) R266723
theorem R79627 : Reach 79627 := rs (se 1 (by rfl) ⟨59720, by rfl⟩) R119441
theorem R112409 : Reach 112409 := rs (se 2 (by rfl) ⟨42153, by rfl⟩) R84307
theorem R1357667 : Reach 1357667 := rs (se 1 (by rfl) ⟨1018250, by rfl⟩) R2036501
theorem R112537 : Reach 112537 := rs (se 2 (by rfl) ⟨42201, by rfl⟩) R84403
theorem R145675 : Reach 145675 := rs (se 1 (by rfl) ⟨109256, by rfl⟩) R218513
theorem R178483 : Reach 178483 := rs (se 1 (by rfl) ⟨133862, by rfl⟩) R267725
theorem R538973 : Reach 538973 := rs (se 3 (by rfl) ⟨101057, by rfl⟩) R202115
theorem R178625 : Reach 178625 := rs (se 2 (by rfl) ⟨66984, by rfl⟩) R133969
theorem R670301 : Reach 670301 := rs (se 3 (by rfl) ⟨125681, by rfl⟩) R251363
theorem R113305 : Reach 113305 := rs (se 2 (by rfl) ⟨42489, by rfl⟩) R84979
theorem R146137 : Reach 146137 := rs (se 2 (by rfl) ⟨54801, by rfl⟩) R109603
theorem R375617 : Reach 375617 := rs (se 2 (by rfl) ⟨140856, by rfl⟩) R281713
theorem R441409 : Reach 441409 := rs (se 2 (by rfl) ⟨165528, by rfl⟩) R331057
theorem R343115 : Reach 343115 := rs (se 1 (by rfl) ⟨257336, by rfl⟩) R514673
theorem R179293 : Reach 179293 := rs (se 3 (by rfl) ⟨33617, by rfl⟩) R67235
theorem R113879 : Reach 113879 := rs (se 1 (by rfl) ⟨85409, by rfl⟩) R170819
theorem R114007 : Reach 114007 := rs (se 1 (by rfl) ⟨85505, by rfl⟩) R171011
theorem R179891 : Reach 179891 := rs (se 1 (by rfl) ⟨134918, by rfl⟩) R269837
theorem R179915 : Reach 179915 := rs (se 1 (by rfl) ⟨134936, by rfl⟩) R269873
theorem R81751 : Reach 81751 := rs (se 1 (by rfl) ⟨61313, by rfl⟩) R122627
theorem R114635 : Reach 114635 := rs (se 1 (by rfl) ⟨85976, by rfl⟩) R171953
theorem R147521 : Reach 147521 := rs (se 2 (by rfl) ⟨55320, by rfl⟩) R110641
theorem R114763 : Reach 114763 := rs (se 1 (by rfl) ⟨86072, by rfl⟩) R172145
theorem R114905 : Reach 114905 := rs (se 2 (by rfl) ⟨43089, by rfl⟩) R86179
theorem R573713 : Reach 573713 := rs (se 2 (by rfl) ⟨215142, by rfl⟩) R430285
theorem R115033 : Reach 115033 := rs (se 2 (by rfl) ⟨43137, by rfl⟩) R86275
theorem R278957 : Reach 278957 := rs (se 3 (by rfl) ⟨52304, by rfl⟩) R104609
theorem R2507395 : Reach 2507395 := rs (se 1 (by rfl) ⟨1880546, by rfl⟩) R3761093
theorem R344897 : Reach 344897 := rs (se 2 (by rfl) ⟨129336, by rfl⟩) R258673
theorem R115607 : Reach 115607 := rs (se 1 (by rfl) ⟨86705, by rfl⟩) R173411
theorem R246721 : Reach 246721 := rs (se 2 (by rfl) ⟨92520, by rfl⟩) R185041
theorem R148481 : Reach 148481 := rs (se 2 (by rfl) ⟨55680, by rfl⟩) R111361
theorem R115735 : Reach 115735 := rs (se 1 (by rfl) ⟨86801, by rfl⟩) R173603
theorem R902501 : Reach 902501 := rs (se 4 (by rfl) ⟨84609, by rfl⟩) R169219
theorem R116311 : Reach 116311 := rs (se 1 (by rfl) ⟨87233, by rfl⟩) R174467
theorem R116363 : Reach 116363 := rs (se 1 (by rfl) ⟨87272, by rfl⟩) R174545
theorem R149195 : Reach 149195 := rs (se 1 (by rfl) ⟨111896, by rfl⟩) R223793
theorem R116491 : Reach 116491 := rs (se 1 (by rfl) ⟨87368, by rfl⟩) R174737
theorem R280385 : Reach 280385 := rs (se 2 (by rfl) ⟨105144, by rfl⟩) R210289
theorem R116633 : Reach 116633 := rs (se 2 (by rfl) ⟨43737, by rfl⟩) R87475
theorem R116761 : Reach 116761 := rs (se 2 (by rfl) ⟨43785, by rfl⟩) R87571
theorem R968773 : Reach 968773 := rs (se 4 (by rfl) ⟨90822, by rfl⟩) R181645
theorem R706765 : Reach 706765 := rs (se 3 (by rfl) ⟨132518, by rfl⟩) R265037
theorem R215617 : Reach 215617 := rs (se 2 (by rfl) ⟨80856, by rfl⟩) R161713
theorem R117335 : Reach 117335 := rs (se 1 (by rfl) ⟨88001, by rfl⟩) R176003
theorem R772739 : Reach 772739 := rs (se 1 (by rfl) ⟨579554, by rfl⟩) R1159109
theorem R150169 : Reach 150169 := rs (se 2 (by rfl) ⟨56313, by rfl⟩) R112627
theorem R182987 : Reach 182987 := rs (se 1 (by rfl) ⟨137240, by rfl⟩) R274481
theorem R117463 : Reach 117463 := rs (se 1 (by rfl) ⟨88097, by rfl⟩) R176195
theorem R346841 : Reach 346841 := rs (se 2 (by rfl) ⟨130065, by rfl⟩) R260131
theorem R510785 : Reach 510785 := rs (se 2 (by rfl) ⟨191544, by rfl⟩) R383089
theorem R150425 : Reach 150425 := rs (se 2 (by rfl) ⟨56409, by rfl⟩) R112819
theorem R85195 : Reach 85195 := rs (se 1 (by rfl) ⟨63896, by rfl⟩) R127793
theorem R85207 : Reach 85207 := rs (se 1 (by rfl) ⟨63905, by rfl⟩) R127811
theorem R150835 : Reach 150835 := rs (se 1 (by rfl) ⟨113126, by rfl⟩) R226253
theorem R118091 : Reach 118091 := rs (se 1 (by rfl) ⟨88568, by rfl⟩) R177137
theorem R118219 : Reach 118219 := rs (se 1 (by rfl) ⟨88664, by rfl⟩) R177329
theorem R151091 : Reach 151091 := rs (se 1 (by rfl) ⟨113318, by rfl⟩) R226637
theorem R151127 : Reach 151127 := rs (se 1 (by rfl) ⟨113345, by rfl⟩) R226691
theorem R118361 : Reach 118361 := rs (se 2 (by rfl) ⟨44385, by rfl⟩) R88771
theorem R511667 : Reach 511667 := rs (se 1 (by rfl) ⟨383750, by rfl⟩) R767501
theorem R184025 : Reach 184025 := rs (se 2 (by rfl) ⟨69009, by rfl⟩) R138019
theorem R118489 : Reach 118489 := rs (se 2 (by rfl) ⟨44433, by rfl⟩) R88867
theorem R151307 : Reach 151307 := rs (se 1 (by rfl) ⟨113480, by rfl⟩) R226961
theorem R151361 : Reach 151361 := rs (se 2 (by rfl) ⟨56760, by rfl⟩) R113521
theorem R511895 : Reach 511895 := rs (se 1 (by rfl) ⟨383921, by rfl⟩) R767843
theorem R151553 : Reach 151553 := rs (se 2 (by rfl) ⟨56832, by rfl⟩) R113665
theorem R151577 : Reach 151577 := rs (se 2 (by rfl) ⟨56841, by rfl⟩) R113683
theorem R217181 : Reach 217181 := rs (se 3 (by rfl) ⟨40721, by rfl⟩) R81443
theorem R151667 : Reach 151667 := rs (se 1 (by rfl) ⟨113750, by rfl⟩) R227501
theorem R872579 : Reach 872579 := rs (se 1 (by rfl) ⟨654434, by rfl⟩) R1308869
theorem R151703 : Reach 151703 := rs (se 1 (by rfl) ⟨113777, by rfl⟩) R227555
theorem R119063 : Reach 119063 := rs (se 1 (by rfl) ⟨89297, by rfl⟩) R178595
theorem R348461 : Reach 348461 := rs (se 3 (by rfl) ⟨65336, by rfl⟩) R130673
theorem R151883 : Reach 151883 := rs (se 1 (by rfl) ⟨113912, by rfl⟩) R227825
theorem R151895 : Reach 151895 := rs (se 1 (by rfl) ⟨113921, by rfl⟩) R227843
theorem R151937 : Reach 151937 := rs (se 2 (by rfl) ⟨56976, by rfl⟩) R113953
theorem R119191 : Reach 119191 := rs (se 1 (by rfl) ⟨89393, by rfl⟩) R178787
theorem R152153 : Reach 152153 := rs (se 2 (by rfl) ⟨57057, by rfl⟩) R114115
theorem R152243 : Reach 152243 := rs (se 1 (by rfl) ⟨114182, by rfl⟩) R228365
theorem R152279 : Reach 152279 := rs (se 1 (by rfl) ⟨114209, by rfl⟩) R228419
theorem R512729 : Reach 512729 := rs (se 2 (by rfl) ⟨192273, by rfl⟩) R384547
theorem R316163 : Reach 316163 := rs (se 1 (by rfl) ⟨237122, by rfl⟩) R474245
theorem R774917 : Reach 774917 := rs (se 4 (by rfl) ⟨72648, by rfl⟩) R145297
theorem R119603 : Reach 119603 := rs (se 1 (by rfl) ⟨89702, by rfl⟩) R179405
theorem R152459 : Reach 152459 := rs (se 1 (by rfl) ⟨114344, by rfl⟩) R228689
theorem R86923 : Reach 86923 := rs (se 1 (by rfl) ⟨65192, by rfl⟩) R130385
theorem R119731 : Reach 119731 := rs (se 1 (by rfl) ⟨89798, by rfl⟩) R179597
theorem R152513 : Reach 152513 := rs (se 2 (by rfl) ⟨57192, by rfl⟩) R114385
theorem R316381 : Reach 316381 := rs (se 3 (by rfl) ⟨59321, by rfl⟩) R118643
theorem R119819 : Reach 119819 := rs (se 1 (by rfl) ⟨89864, by rfl⟩) R179729
theorem R119873 : Reach 119873 := rs (se 2 (by rfl) ⟨44952, by rfl⟩) R89905
theorem R119947 : Reach 119947 := rs (se 1 (by rfl) ⟨89960, by rfl⟩) R179921
theorem R152729 : Reach 152729 := rs (se 2 (by rfl) ⟨57273, by rfl⟩) R114547
theorem R120001 : Reach 120001 := rs (se 2 (by rfl) ⟨45000, by rfl⟩) R90001
theorem R152819 : Reach 152819 := rs (se 1 (by rfl) ⟨114614, by rfl⟩) R229229
theorem R152855 : Reach 152855 := rs (se 1 (by rfl) ⟨114641, by rfl⟩) R229283
theorem R284077 : Reach 284077 := rs (se 3 (by rfl) ⟨53264, by rfl⟩) R106529
theorem R153035 : Reach 153035 := rs (se 1 (by rfl) ⟨114776, by rfl⟩) R229553
theorem R153089 : Reach 153089 := rs (se 2 (by rfl) ⟨57408, by rfl⟩) R114817
theorem R153305 : Reach 153305 := rs (se 2 (by rfl) ⟨57489, by rfl⟩) R114979
theorem R153395 : Reach 153395 := rs (se 1 (by rfl) ⟨115046, by rfl⟩) R230093
theorem R153431 : Reach 153431 := rs (se 1 (by rfl) ⟨115073, by rfl⟩) R230147
theorem R87895 : Reach 87895 := rs (se 1 (by rfl) ⟨65921, by rfl⟩) R131843
theorem R153611 : Reach 153611 := rs (se 1 (by rfl) ⟨115208, by rfl⟩) R230417
theorem R153665 : Reach 153665 := rs (se 2 (by rfl) ⟨57624, by rfl⟩) R115249
theorem R2676887 : Reach 2676887 := rs (se 1 (by rfl) ⟨2007665, by rfl⟩) R4015331
theorem R153793 : Reach 153793 := rs (se 2 (by rfl) ⟨57672, by rfl⟩) R115345
theorem R907469 : Reach 907469 := rs (se 3 (by rfl) ⟨170150, by rfl⟩) R340301
theorem R153881 : Reach 153881 := rs (se 2 (by rfl) ⟨57705, by rfl⟩) R115411
theorem R153971 : Reach 153971 := rs (se 1 (by rfl) ⟨115478, by rfl⟩) R230957
theorem R383363 : Reach 383363 := rs (se 1 (by rfl) ⟨287522, by rfl⟩) R575045
theorem R154007 : Reach 154007 := rs (se 1 (by rfl) ⟨115505, by rfl⟩) R231011
theorem R1104401 : Reach 1104401 := rs (se 2 (by rfl) ⟨414150, by rfl⟩) R828301
theorem R154187 : Reach 154187 := rs (se 1 (by rfl) ⟨115640, by rfl⟩) R231281
theorem R1464925 : Reach 1464925 := rs (se 3 (by rfl) ⟨274673, by rfl⟩) R549347
theorem R121459 : Reach 121459 := rs (se 1 (by rfl) ⟨91094, by rfl⟩) R182189
theorem R154241 : Reach 154241 := rs (se 2 (by rfl) ⟨57840, by rfl⟩) R115681
theorem R88715 : Reach 88715 := rs (se 1 (by rfl) ⟨66536, by rfl⟩) R133073
theorem R121495 : Reach 121495 := rs (se 1 (by rfl) ⟨91121, by rfl⟩) R182243
theorem R154457 : Reach 154457 := rs (se 2 (by rfl) ⟨57921, by rfl⟩) R115843
theorem R580445 : Reach 580445 := rs (se 3 (by rfl) ⟨108833, by rfl⟩) R217667
theorem R154547 : Reach 154547 := rs (se 1 (by rfl) ⟨115910, by rfl⟩) R231821
theorem R154583 : Reach 154583 := rs (se 1 (by rfl) ⟨115937, by rfl⟩) R231875
theorem R220249 : Reach 220249 := rs (se 2 (by rfl) ⟨82593, by rfl⟩) R165187
theorem R154763 : Reach 154763 := rs (se 1 (by rfl) ⟨116072, by rfl⟩) R232145
theorem R154817 : Reach 154817 := rs (se 2 (by rfl) ⟨58056, by rfl⟩) R116113
theorem R89419 : Reach 89419 := rs (se 1 (by rfl) ⟨67064, by rfl⟩) R134129
theorem R875893 : Reach 875893 := rs (se 5 (by rfl) ⟨41057, by rfl⟩) R82115
theorem R155033 : Reach 155033 := rs (se 2 (by rfl) ⟨58137, by rfl⟩) R116275
theorem R155123 : Reach 155123 := rs (se 1 (by rfl) ⟨116342, by rfl⟩) R232685
theorem R155159 : Reach 155159 := rs (se 1 (by rfl) ⟨116369, by rfl⟩) R232739
theorem R581195 : Reach 581195 := rs (se 1 (by rfl) ⟨435896, by rfl⟩) R871793
theorem R89687 : Reach 89687 := rs (se 1 (by rfl) ⟨67265, by rfl⟩) R134531
theorem R155339 : Reach 155339 := rs (se 1 (by rfl) ⟨116504, by rfl⟩) R233009
theorem R155393 : Reach 155393 := rs (se 2 (by rfl) ⟨58272, by rfl⟩) R116545
theorem R1007477 : Reach 1007477 := rs (se 5 (by rfl) ⟨47225, by rfl⟩) R94451
theorem R155609 : Reach 155609 := rs (se 2 (by rfl) ⟨58353, by rfl⟩) R116707
theorem R516131 : Reach 516131 := rs (se 1 (by rfl) ⟨387098, by rfl⟩) R774197
theorem R155699 : Reach 155699 := rs (se 1 (by rfl) ⟨116774, by rfl⟩) R233549
theorem R155735 : Reach 155735 := rs (se 1 (by rfl) ⟨116801, by rfl⟩) R233603
theorem R352349 : Reach 352349 := rs (se 3 (by rfl) ⟨66065, by rfl⟩) R132131
theorem R155915 : Reach 155915 := rs (se 1 (by rfl) ⟨116936, by rfl⟩) R233873
theorem R155969 : Reach 155969 := rs (se 2 (by rfl) ⟨58488, by rfl⟩) R116977
theorem R450917 : Reach 450917 := rs (se 4 (by rfl) ⟨42273, by rfl⟩) R84547
theorem R450967 : Reach 450967 := rs (se 1 (by rfl) ⟨338225, by rfl⟩) R676451
theorem R156185 : Reach 156185 := rs (se 2 (by rfl) ⟨58569, by rfl⟩) R117139
theorem R156275 : Reach 156275 := rs (se 1 (by rfl) ⟨117206, by rfl⟩) R234413
theorem R156311 : Reach 156311 := rs (se 1 (by rfl) ⟨117233, by rfl⟩) R234467
theorem R156439 : Reach 156439 := rs (se 1 (by rfl) ⟨117329, by rfl⟩) R234659
theorem R254765 : Reach 254765 := rs (se 3 (by rfl) ⟨47768, by rfl⟩) R95537
theorem R1008449 : Reach 1008449 := rs (se 2 (by rfl) ⟨378168, by rfl⟩) R756337
theorem R156491 : Reach 156491 := rs (se 1 (by rfl) ⟨117368, by rfl⟩) R234737
theorem R156545 : Reach 156545 := rs (se 2 (by rfl) ⟨58704, by rfl⟩) R117409
theorem R156761 : Reach 156761 := rs (se 2 (by rfl) ⟨58785, by rfl⟩) R117571
theorem R582835 : Reach 582835 := rs (se 1 (by rfl) ⟨437126, by rfl⟩) R874253
theorem R156851 : Reach 156851 := rs (se 1 (by rfl) ⟨117638, by rfl⟩) R235277
theorem R156887 : Reach 156887 := rs (se 1 (by rfl) ⟨117665, by rfl⟩) R235331
theorem R124183 : Reach 124183 := rs (se 1 (by rfl) ⟨93137, by rfl⟩) R186275
theorem R124211 : Reach 124211 := rs (se 1 (by rfl) ⟨93158, by rfl⟩) R186317
theorem R157067 : Reach 157067 := rs (se 1 (by rfl) ⟨117800, by rfl⟩) R235601
theorem R157121 : Reach 157121 := rs (se 2 (by rfl) ⟨58920, by rfl⟩) R117841
theorem R157337 : Reach 157337 := rs (se 2 (by rfl) ⟨59001, by rfl⟩) R118003
theorem R157427 : Reach 157427 := rs (se 1 (by rfl) ⟨118070, by rfl⟩) R236141
theorem R157463 : Reach 157463 := rs (se 1 (by rfl) ⟨118097, by rfl⟩) R236195
theorem R157643 : Reach 157643 := rs (se 1 (by rfl) ⟨118232, by rfl⟩) R236465
theorem R157697 : Reach 157697 := rs (se 2 (by rfl) ⟨59136, by rfl⟩) R118273
theorem R223307 : Reach 223307 := rs (se 1 (by rfl) ⟨167480, by rfl⟩) R334961
theorem R354455 : Reach 354455 := rs (se 1 (by rfl) ⟨265841, by rfl⟩) R531683
theorem R157913 : Reach 157913 := rs (se 2 (by rfl) ⟨59217, by rfl⟩) R118435
theorem R158003 : Reach 158003 := rs (se 1 (by rfl) ⟨118502, by rfl⟩) R237005
theorem R158039 : Reach 158039 := rs (se 1 (by rfl) ⟨118529, by rfl⟩) R237059
theorem R158219 : Reach 158219 := rs (se 1 (by rfl) ⟨118664, by rfl⟩) R237329
theorem R158273 : Reach 158273 := rs (se 2 (by rfl) ⟨59352, by rfl⟩) R118705
theorem R256715 : Reach 256715 := rs (se 1 (by rfl) ⟨192536, by rfl⟩) R385073
theorem R256729 : Reach 256729 := rs (se 2 (by rfl) ⟨96273, by rfl⟩) R192547
theorem R158489 : Reach 158489 := rs (se 2 (by rfl) ⟨59433, by rfl⟩) R118867
theorem R158579 : Reach 158579 := rs (se 1 (by rfl) ⟨118934, by rfl⟩) R237869
theorem R158615 : Reach 158615 := rs (se 1 (by rfl) ⟨118961, by rfl⟩) R237923
theorem R158795 : Reach 158795 := rs (se 1 (by rfl) ⟨119096, by rfl⟩) R238193
theorem R158849 : Reach 158849 := rs (se 2 (by rfl) ⟨59568, by rfl⟩) R119137
theorem R224407 : Reach 224407 := rs (se 1 (by rfl) ⟨168305, by rfl⟩) R336611
theorem R290051 : Reach 290051 := rs (se 1 (by rfl) ⟨217538, by rfl⟩) R435077
theorem R159065 : Reach 159065 := rs (se 2 (by rfl) ⟨59649, by rfl⟩) R119299
theorem R159155 : Reach 159155 := rs (se 1 (by rfl) ⟨119366, by rfl⟩) R238733
theorem R388739 : Reach 388739 := rs (se 1 (by rfl) ⟨291554, by rfl⟩) R583109
theorem R257687 : Reach 257687 := rs (se 1 (by rfl) ⟨193265, by rfl⟩) R386531
theorem R159425 : Reach 159425 := rs (se 2 (by rfl) ⟨59784, by rfl⟩) R119569
theorem R913157 : Reach 913157 := rs (se 4 (by rfl) ⟨85608, by rfl⟩) R171217
theorem R454531 : Reach 454531 := rs (se 1 (by rfl) ⟨340898, by rfl⟩) R681797
theorem R192449 : Reach 192449 := rs (se 2 (by rfl) ⟨72168, by rfl⟩) R144337
theorem R225227 : Reach 225227 := rs (se 1 (by rfl) ⟨168920, by rfl⟩) R337841
theorem R159767 : Reach 159767 := rs (se 1 (by rfl) ⟨119825, by rfl⟩) R239651
theorem R389195 : Reach 389195 := rs (se 1 (by rfl) ⟨291896, by rfl⟩) R583793
theorem R127051 : Reach 127051 := rs (se 1 (by rfl) ⟨95288, by rfl⟩) R190577
theorem R159833 : Reach 159833 := rs (se 2 (by rfl) ⟨59937, by rfl⟩) R119875
theorem R159947 : Reach 159947 := rs (se 1 (by rfl) ⟨119960, by rfl⟩) R239921
theorem R193117 : Reach 193117 := rs (se 3 (by rfl) ⟨36209, by rfl⟩) R72419
theorem R2716253 : Reach 2716253 := rs (se 3 (by rfl) ⟨509297, by rfl⟩) R1018595
theorem R193175 : Reach 193175 := rs (se 1 (by rfl) ⟨144881, by rfl⟩) R289763
theorem R258947 : Reach 258947 := rs (se 1 (by rfl) ⟨194210, by rfl⟩) R388421
theorem R488369 : Reach 488369 := rs (se 2 (by rfl) ⟨183138, by rfl⟩) R366277
theorem R914449 : Reach 914449 := rs (se 2 (by rfl) ⟨342918, by rfl⟩) R685837
theorem R291863 : Reach 291863 := rs (se 1 (by rfl) ⟨218897, by rfl⟩) R437795
theorem R128243 : Reach 128243 := rs (se 1 (by rfl) ⟨96182, by rfl⟩) R192365
theorem R521477 : Reach 521477 := rs (se 4 (by rfl) ⟨48888, by rfl⟩) R97777
theorem R226583 : Reach 226583 := rs (se 1 (by rfl) ⟨169937, by rfl⟩) R339875
theorem R128395 : Reach 128395 := rs (se 1 (by rfl) ⟨96296, by rfl⟩) R192593
theorem R882251 : Reach 882251 := rs (se 1 (by rfl) ⟨661688, by rfl⟩) R1323377
theorem R358019 : Reach 358019 := rs (se 1 (by rfl) ⟨268514, by rfl⟩) R537029
theorem R325271 : Reach 325271 := rs (se 1 (by rfl) ⟨243953, by rfl⟩) R487907
theorem R128729 : Reach 128729 := rs (se 2 (by rfl) ⟨48273, by rfl⟩) R96547
theorem R96023 : Reach 96023 := rs (se 1 (by rfl) ⟨72017, by rfl⟩) R144035
theorem R227123 : Reach 227123 := rs (se 1 (by rfl) ⟨170342, by rfl⟩) R340685
theorem R194393 : Reach 194393 := rs (se 2 (by rfl) ⟨72897, by rfl⟩) R145795
theorem R194507 : Reach 194507 := rs (se 1 (by rfl) ⟨145880, by rfl⟩) R291761
theorem R227393 : Reach 227393 := rs (se 2 (by rfl) ⟨85272, by rfl⟩) R170545
theorem R96331 : Reach 96331 := rs (se 1 (by rfl) ⟨72248, by rfl⟩) R144497
theorem R96395 : Reach 96395 := rs (se 1 (by rfl) ⟨72296, by rfl⟩) R144593
theorem R981233 : Reach 981233 := rs (se 2 (by rfl) ⟨367962, by rfl⟩) R735925
theorem R293195 : Reach 293195 := rs (se 1 (by rfl) ⟨219896, by rfl⟩) R439793
theorem R129367 : Reach 129367 := rs (se 1 (by rfl) ⟨97025, by rfl⟩) R194051
theorem R621017 : Reach 621017 := rs (se 2 (by rfl) ⟨232881, by rfl⟩) R465763
theorem R227933 : Reach 227933 := rs (se 3 (by rfl) ⟨42737, by rfl⟩) R85475
theorem R293777 : Reach 293777 := rs (se 2 (by rfl) ⟨110166, by rfl⟩) R220333
theorem R195635 : Reach 195635 := rs (se 1 (by rfl) ⟨146726, by rfl⟩) R293453
theorem R97367 : Reach 97367 := rs (se 1 (by rfl) ⟨73025, by rfl⟩) R146051
theorem R130187 : Reach 130187 := rs (se 1 (by rfl) ⟨97640, by rfl⟩) R195281
theorem R130241 : Reach 130241 := rs (se 2 (by rfl) ⟨48840, by rfl⟩) R97681
theorem R1211597 : Reach 1211597 := rs (se 3 (by rfl) ⟨227174, by rfl⟩) R454349
theorem R97561 : Reach 97561 := rs (se 2 (by rfl) ⟨36585, by rfl⟩) R73171
theorem R196033 : Reach 196033 := rs (se 2 (by rfl) ⟨73512, by rfl⟩) R147025
theorem R523907 : Reach 523907 := rs (se 1 (by rfl) ⟨392930, by rfl⟩) R785861
theorem R229067 : Reach 229067 := rs (se 1 (by rfl) ⟨171800, by rfl⟩) R343601
theorem R262061 : Reach 262061 := rs (se 3 (by rfl) ⟨49136, by rfl⟩) R98273
theorem R294835 : Reach 294835 := rs (se 1 (by rfl) ⟨221126, by rfl⟩) R442253
theorem R229337 : Reach 229337 := rs (se 2 (by rfl) ⟨86001, by rfl⟩) R172003
theorem R98347 : Reach 98347 := rs (se 1 (by rfl) ⟨73760, by rfl⟩) R147521
theorem R655447 : Reach 655447 := rs (se 1 (by rfl) ⟨491585, by rfl⟩) R983171
theorem R426221 : Reach 426221 := rs (se 3 (by rfl) ⟨79916, by rfl⟩) R159833
theorem R131387 : Reach 131387 := rs (se 1 (by rfl) ⟨98540, by rfl⟩) R197081
theorem R2326877 : Reach 2326877 := rs (se 3 (by rfl) ⟨436289, by rfl⟩) R872579
theorem R262547 : Reach 262547 := rs (se 1 (by rfl) ⟨196910, by rfl⟩) R393821
theorem R197149 : Reach 197149 := rs (se 3 (by rfl) ⟨36965, by rfl⟩) R73931
theorem R229931 : Reach 229931 := rs (se 1 (by rfl) ⟨172448, by rfl⟩) R344897
theorem R98987 : Reach 98987 := rs (se 1 (by rfl) ⟨74240, by rfl⟩) R148481
theorem R3343193 : Reach 3343193 := rs (se 2 (by rfl) ⟨1253697, by rfl⟩) R2507395
theorem R197491 : Reach 197491 := rs (se 1 (by rfl) ⟨148118, by rfl⟩) R296237
theorem R263047 : Reach 263047 := rs (se 1 (by rfl) ⟨197285, by rfl⟩) R394571
theorem R132025 : Reach 132025 := rs (se 2 (by rfl) ⟨49509, by rfl⟩) R99019
theorem R99463 : Reach 99463 := rs (se 1 (by rfl) ⟨74597, by rfl⟩) R149195
theorem R328961 : Reach 328961 := rs (se 2 (by rfl) ⟨123360, by rfl⟩) R246721
theorem R132367 : Reach 132367 := rs (se 1 (by rfl) ⟨99275, by rfl⟩) R198551
theorem R67131 : Reach 67131 := rs (se 1 (by rfl) ⟨50348, by rfl⟩) R100697
theorem R67207 : Reach 67207 := rs (se 1 (by rfl) ⟨50405, by rfl⟩) R100811
theorem R67215 : Reach 67215 := rs (se 1 (by rfl) ⟨50411, by rfl⟩) R100823
theorem R67259 : Reach 67259 := rs (se 1 (by rfl) ⟨50444, by rfl⟩) R100889
theorem R165577 : Reach 165577 := rs (se 2 (by rfl) ⟨62091, by rfl⟩) R124183
theorem R67335 : Reach 67335 := rs (se 1 (by rfl) ⟨50501, by rfl⟩) R101003
theorem R67343 : Reach 67343 := rs (se 1 (by rfl) ⟨50507, by rfl⟩) R101015
theorem R67387 : Reach 67387 := rs (se 1 (by rfl) ⟨50540, by rfl⟩) R101081
theorem R231227 : Reach 231227 := rs (se 1 (by rfl) ⟨173420, by rfl⟩) R346841
theorem R67463 : Reach 67463 := rs (se 1 (by rfl) ⟨50597, by rfl⟩) R101195
theorem R67471 : Reach 67471 := rs (se 1 (by rfl) ⟨50603, by rfl⟩) R101207
theorem R67515 : Reach 67515 := rs (se 1 (by rfl) ⟨50636, by rfl⟩) R101273
theorem R100283 : Reach 100283 := rs (se 1 (by rfl) ⟨75212, by rfl⟩) R150425
theorem R67591 : Reach 67591 := rs (se 1 (by rfl) ⟨50693, by rfl⟩) R101387
theorem R67599 : Reach 67599 := rs (se 1 (by rfl) ⟨50699, by rfl⟩) R101399
theorem R67643 : Reach 67643 := rs (se 1 (by rfl) ⟨50732, by rfl⟩) R101465
theorem R67719 : Reach 67719 := rs (se 1 (by rfl) ⟨50789, by rfl⟩) R101579
theorem R133255 : Reach 133255 := rs (se 1 (by rfl) ⟨99941, by rfl⟩) R199883
theorem R67727 : Reach 67727 := rs (se 1 (by rfl) ⟨50795, by rfl⟩) R101591
theorem R67771 : Reach 67771 := rs (se 1 (by rfl) ⟨50828, by rfl⟩) R101657
theorem R67847 : Reach 67847 := rs (se 1 (by rfl) ⟨50885, by rfl⟩) R101771
theorem R67855 : Reach 67855 := rs (se 1 (by rfl) ⟨50891, by rfl⟩) R101783
theorem R231713 : Reach 231713 := rs (se 2 (by rfl) ⟨86892, by rfl⟩) R173785
theorem R67899 : Reach 67899 := rs (se 1 (by rfl) ⟨50924, by rfl⟩) R101849
theorem R100727 : Reach 100727 := rs (se 1 (by rfl) ⟨75545, by rfl⟩) R151091
theorem R67975 : Reach 67975 := rs (se 1 (by rfl) ⟨50981, by rfl⟩) R101963
theorem R100751 : Reach 100751 := rs (se 1 (by rfl) ⟨75563, by rfl⟩) R151127
theorem R67983 : Reach 67983 := rs (se 1 (by rfl) ⟨50987, by rfl⟩) R101975
theorem R100793 : Reach 100793 := rs (se 2 (by rfl) ⟨37797, by rfl⟩) R75595
theorem R68027 : Reach 68027 := rs (se 1 (by rfl) ⟨51020, by rfl⟩) R102041
theorem R100871 : Reach 100871 := rs (se 1 (by rfl) ⟨75653, by rfl⟩) R151307
theorem R68103 : Reach 68103 := rs (se 1 (by rfl) ⟨51077, by rfl⟩) R102155
theorem R68111 : Reach 68111 := rs (se 1 (by rfl) ⟨51083, by rfl⟩) R102167
theorem R100907 : Reach 100907 := rs (se 1 (by rfl) ⟨75680, by rfl⟩) R151361
theorem R68155 : Reach 68155 := rs (se 1 (by rfl) ⟨51116, by rfl⟩) R102233
theorem R100921 : Reach 100921 := rs (se 2 (by rfl) ⟨37845, by rfl⟩) R75691
theorem R100937 : Reach 100937 := rs (se 2 (by rfl) ⟨37851, by rfl⟩) R75703
theorem R68231 : Reach 68231 := rs (se 1 (by rfl) ⟨51173, by rfl⟩) R102347
theorem R68239 : Reach 68239 := rs (se 1 (by rfl) ⟨51179, by rfl⟩) R102359
theorem R101035 : Reach 101035 := rs (se 1 (by rfl) ⟨75776, by rfl⟩) R151553
theorem R101051 : Reach 101051 := rs (se 1 (by rfl) ⟨75788, by rfl⟩) R151577
theorem R68283 : Reach 68283 := rs (se 1 (by rfl) ⟨51212, by rfl⟩) R102425
theorem R101111 : Reach 101111 := rs (se 1 (by rfl) ⟨75833, by rfl⟩) R151667
theorem R68359 : Reach 68359 := rs (se 1 (by rfl) ⟨51269, by rfl⟩) R102539
theorem R101135 : Reach 101135 := rs (se 1 (by rfl) ⟨75851, by rfl⟩) R151703
theorem R68367 : Reach 68367 := rs (se 1 (by rfl) ⟨51275, by rfl⟩) R102551
theorem R101177 : Reach 101177 := rs (se 2 (by rfl) ⟨37941, by rfl⟩) R75883
theorem R68411 : Reach 68411 := rs (se 1 (by rfl) ⟨51308, by rfl⟩) R102617
theorem R232307 : Reach 232307 := rs (se 1 (by rfl) ⟨174230, by rfl⟩) R348461
theorem R101255 : Reach 101255 := rs (se 1 (by rfl) ⟨75941, by rfl⟩) R151883
theorem R68487 : Reach 68487 := rs (se 1 (by rfl) ⟨51365, by rfl⟩) R102731
theorem R68495 : Reach 68495 := rs (se 1 (by rfl) ⟨51371, by rfl⟩) R102743
theorem R101263 : Reach 101263 := rs (se 1 (by rfl) ⟨75947, by rfl⟩) R151895
theorem R101291 : Reach 101291 := rs (se 1 (by rfl) ⟨75968, by rfl⟩) R151937
theorem R68539 : Reach 68539 := rs (se 1 (by rfl) ⟨51404, by rfl⟩) R102809
theorem R101321 : Reach 101321 := rs (se 2 (by rfl) ⟨37995, by rfl⟩) R75991
theorem R68615 : Reach 68615 := rs (se 1 (by rfl) ⟨51461, by rfl⟩) R102923
theorem R68623 : Reach 68623 := rs (se 1 (by rfl) ⟨51467, by rfl⟩) R102935
theorem R592919 : Reach 592919 := rs (se 1 (by rfl) ⟨444689, by rfl⟩) R889379
theorem R101435 : Reach 101435 := rs (se 1 (by rfl) ⟨76076, by rfl⟩) R152153
theorem R68667 : Reach 68667 := rs (se 1 (by rfl) ⟨51500, by rfl⟩) R103001
theorem R101495 : Reach 101495 := rs (se 1 (by rfl) ⟨76121, by rfl⟩) R152243
theorem R68743 : Reach 68743 := rs (se 1 (by rfl) ⟨51557, by rfl⟩) R103115
theorem R101519 : Reach 101519 := rs (se 1 (by rfl) ⟨76139, by rfl⟩) R152279
theorem R68751 : Reach 68751 := rs (se 1 (by rfl) ⟨51563, by rfl⟩) R103127
theorem R101561 : Reach 101561 := rs (se 2 (by rfl) ⟨38085, by rfl⟩) R76171
theorem R68795 : Reach 68795 := rs (se 1 (by rfl) ⟨51596, by rfl⟩) R103193
theorem R101639 : Reach 101639 := rs (se 1 (by rfl) ⟨76229, by rfl⟩) R152459
theorem R68871 : Reach 68871 := rs (se 1 (by rfl) ⟨51653, by rfl⟩) R103307
theorem R68879 : Reach 68879 := rs (se 1 (by rfl) ⟨51659, by rfl⟩) R103319
theorem R363809 : Reach 363809 := rs (se 2 (by rfl) ⟨136428, by rfl⟩) R272857
theorem R101675 : Reach 101675 := rs (se 1 (by rfl) ⟨76256, by rfl⟩) R152513
theorem R68923 : Reach 68923 := rs (se 1 (by rfl) ⟨51692, by rfl⟩) R103385
theorem R101705 : Reach 101705 := rs (se 2 (by rfl) ⟨38139, by rfl⟩) R76279
theorem R68999 : Reach 68999 := rs (se 1 (by rfl) ⟨51749, by rfl⟩) R103499
theorem R69007 : Reach 69007 := rs (se 1 (by rfl) ⟨51755, by rfl⟩) R103511
theorem R101819 : Reach 101819 := rs (se 1 (by rfl) ⟨76364, by rfl⟩) R152729
theorem R69051 : Reach 69051 := rs (se 1 (by rfl) ⟨51788, by rfl⟩) R103577
theorem R331229 : Reach 331229 := rs (se 3 (by rfl) ⟨62105, by rfl⟩) R124211
theorem R101879 : Reach 101879 := rs (se 1 (by rfl) ⟨76409, by rfl⟩) R152819
theorem R69127 : Reach 69127 := rs (se 1 (by rfl) ⟨51845, by rfl⟩) R103691
theorem R101903 : Reach 101903 := rs (se 1 (by rfl) ⟨76427, by rfl⟩) R152855
theorem R69135 : Reach 69135 := rs (se 1 (by rfl) ⟨51851, by rfl⟩) R103703
theorem R200225 : Reach 200225 := rs (se 2 (by rfl) ⟨75084, by rfl⟩) R150169
theorem R101945 : Reach 101945 := rs (se 2 (by rfl) ⟨38229, by rfl⟩) R76459
theorem R69179 : Reach 69179 := rs (se 1 (by rfl) ⟨51884, by rfl⟩) R103769
theorem R102023 : Reach 102023 := rs (se 1 (by rfl) ⟨76517, by rfl⟩) R153035
theorem R69255 : Reach 69255 := rs (se 1 (by rfl) ⟨51941, by rfl⟩) R103883
theorem R69263 : Reach 69263 := rs (se 1 (by rfl) ⟨51947, by rfl⟩) R103895
theorem R200339 : Reach 200339 := rs (se 1 (by rfl) ⟨150254, by rfl⟩) R300509
theorem R102059 : Reach 102059 := rs (se 1 (by rfl) ⟨76544, by rfl⟩) R153089
theorem R69307 : Reach 69307 := rs (se 1 (by rfl) ⟨51980, by rfl⟩) R103961
theorem R102089 : Reach 102089 := rs (se 2 (by rfl) ⟨38283, by rfl⟩) R76567
theorem R397001 : Reach 397001 := rs (se 2 (by rfl) ⟨148875, by rfl⟩) R297751
theorem R69383 : Reach 69383 := rs (se 1 (by rfl) ⟨52037, by rfl⟩) R104075
theorem R69391 : Reach 69391 := rs (se 1 (by rfl) ⟨52043, by rfl⟩) R104087
theorem R102203 : Reach 102203 := rs (se 1 (by rfl) ⟨76652, by rfl⟩) R153305
theorem R69435 : Reach 69435 := rs (se 1 (by rfl) ⟨52076, by rfl⟩) R104153
theorem R102263 : Reach 102263 := rs (se 1 (by rfl) ⟨76697, by rfl⟩) R153395
theorem R69511 : Reach 69511 := rs (se 1 (by rfl) ⟨52133, by rfl⟩) R104267
theorem R102287 : Reach 102287 := rs (se 1 (by rfl) ⟨76715, by rfl⟩) R153431
theorem R69519 : Reach 69519 := rs (se 1 (by rfl) ⟨52139, by rfl⟩) R104279
theorem R528281 : Reach 528281 := rs (se 2 (by rfl) ⟨198105, by rfl⟩) R396211
theorem R102329 : Reach 102329 := rs (se 2 (by rfl) ⟨38373, by rfl⟩) R76747
theorem R69563 : Reach 69563 := rs (se 1 (by rfl) ⟨52172, by rfl⟩) R104345
theorem R102407 : Reach 102407 := rs (se 1 (by rfl) ⟨76805, by rfl⟩) R153611
theorem R69639 : Reach 69639 := rs (se 1 (by rfl) ⟨52229, by rfl⟩) R104459
theorem R69647 : Reach 69647 := rs (se 1 (by rfl) ⟨52235, by rfl⟩) R104471
theorem R102443 : Reach 102443 := rs (se 1 (by rfl) ⟨76832, by rfl⟩) R153665
theorem R69691 : Reach 69691 := rs (se 1 (by rfl) ⟨52268, by rfl⟩) R104537
theorem R102473 : Reach 102473 := rs (se 2 (by rfl) ⟨38427, by rfl⟩) R76855
theorem R69767 : Reach 69767 := rs (se 1 (by rfl) ⟨52325, by rfl⟩) R104651
theorem R69775 : Reach 69775 := rs (se 1 (by rfl) ⟨52331, by rfl⟩) R104663
theorem R102587 : Reach 102587 := rs (se 1 (by rfl) ⟨76940, by rfl⟩) R153881
theorem R69819 : Reach 69819 := rs (se 1 (by rfl) ⟨52364, by rfl⟩) R104729
theorem R299209 : Reach 299209 := rs (se 2 (by rfl) ⟨112203, by rfl⟩) R224407
theorem R102647 : Reach 102647 := rs (se 1 (by rfl) ⟨76985, by rfl⟩) R153971
theorem R69895 : Reach 69895 := rs (se 1 (by rfl) ⟨52421, by rfl⟩) R104843
theorem R102671 : Reach 102671 := rs (se 1 (by rfl) ⟨77003, by rfl⟩) R154007
theorem R69903 : Reach 69903 := rs (se 1 (by rfl) ⟨52427, by rfl⟩) R104855
theorem R102713 : Reach 102713 := rs (se 2 (by rfl) ⟨38517, by rfl⟩) R77035
theorem R69947 : Reach 69947 := rs (se 1 (by rfl) ⟨52460, by rfl⟩) R104921
theorem R201079 : Reach 201079 := rs (se 1 (by rfl) ⟨150809, by rfl⟩) R301619
theorem R102791 : Reach 102791 := rs (se 1 (by rfl) ⟨77093, by rfl⟩) R154187
theorem R70023 : Reach 70023 := rs (se 1 (by rfl) ⟨52517, by rfl⟩) R105035
theorem R70031 : Reach 70031 := rs (se 1 (by rfl) ⟨52523, by rfl⟩) R105047
theorem R201113 : Reach 201113 := rs (se 2 (by rfl) ⟨75417, by rfl⟩) R150835
theorem R102827 : Reach 102827 := rs (se 1 (by rfl) ⟨77120, by rfl⟩) R154241
theorem R70075 : Reach 70075 := rs (se 1 (by rfl) ⟨52556, by rfl⟩) R105113
theorem R102857 : Reach 102857 := rs (se 2 (by rfl) ⟨38571, by rfl⟩) R77143
theorem R70151 : Reach 70151 := rs (se 1 (by rfl) ⟨52613, by rfl⟩) R105227
theorem R70159 : Reach 70159 := rs (se 1 (by rfl) ⟨52619, by rfl⟩) R105239
theorem R102971 : Reach 102971 := rs (se 1 (by rfl) ⟨77228, by rfl⟩) R154457
theorem R70203 : Reach 70203 := rs (se 1 (by rfl) ⟨52652, by rfl⟩) R105305
theorem R103031 : Reach 103031 := rs (se 1 (by rfl) ⟨77273, by rfl⟩) R154547
theorem R397943 : Reach 397943 := rs (se 1 (by rfl) ⟨298457, by rfl⟩) R596915
theorem R70279 : Reach 70279 := rs (se 1 (by rfl) ⟨52709, by rfl⟩) R105419
theorem R103055 : Reach 103055 := rs (se 1 (by rfl) ⟨77291, by rfl⟩) R154583
theorem R70287 : Reach 70287 := rs (se 1 (by rfl) ⟨52715, by rfl⟩) R105431
theorem R103097 : Reach 103097 := rs (se 2 (by rfl) ⟨38661, by rfl⟩) R77323
theorem R70331 : Reach 70331 := rs (se 1 (by rfl) ⟨52748, by rfl⟩) R105497
theorem R103175 : Reach 103175 := rs (se 1 (by rfl) ⟨77381, by rfl⟩) R154763
theorem R70407 : Reach 70407 := rs (se 1 (by rfl) ⟨52805, by rfl⟩) R105611
theorem R70415 : Reach 70415 := rs (se 1 (by rfl) ⟨52811, by rfl⟩) R105623
theorem R103211 : Reach 103211 := rs (se 1 (by rfl) ⟨77408, by rfl⟩) R154817
theorem R70459 : Reach 70459 := rs (se 1 (by rfl) ⟨52844, by rfl⟩) R105689
theorem R103241 : Reach 103241 := rs (se 2 (by rfl) ⟨38715, by rfl⟩) R77431
theorem R398195 : Reach 398195 := rs (se 1 (by rfl) ⟨298646, by rfl⟩) R597293
theorem R70535 : Reach 70535 := rs (se 1 (by rfl) ⟨52901, by rfl⟩) R105803
theorem R70543 : Reach 70543 := rs (se 1 (by rfl) ⟨52907, by rfl⟩) R105815
theorem R103355 : Reach 103355 := rs (se 1 (by rfl) ⟨77516, by rfl⟩) R155033
theorem R70587 : Reach 70587 := rs (se 1 (by rfl) ⟨52940, by rfl⟩) R105881
theorem R103415 : Reach 103415 := rs (se 1 (by rfl) ⟨77561, by rfl⟩) R155123
theorem R70663 : Reach 70663 := rs (se 1 (by rfl) ⟨52997, by rfl⟩) R105995
theorem R103439 : Reach 103439 := rs (se 1 (by rfl) ⟨77579, by rfl⟩) R155159
theorem R70671 : Reach 70671 := rs (se 1 (by rfl) ⟨53003, by rfl⟩) R106007
theorem R103481 : Reach 103481 := rs (se 2 (by rfl) ⟨38805, by rfl⟩) R77611
theorem R70715 : Reach 70715 := rs (se 1 (by rfl) ⟨53036, by rfl⟩) R106073
theorem R103559 : Reach 103559 := rs (se 1 (by rfl) ⟨77669, by rfl⟩) R155339
theorem R70791 : Reach 70791 := rs (se 1 (by rfl) ⟨53093, by rfl⟩) R106187
theorem R70799 : Reach 70799 := rs (se 1 (by rfl) ⟨53099, by rfl⟩) R106199
theorem R103595 : Reach 103595 := rs (se 1 (by rfl) ⟨77696, by rfl⟩) R155393
theorem R70843 : Reach 70843 := rs (se 1 (by rfl) ⟨53132, by rfl⟩) R106265
theorem R103625 : Reach 103625 := rs (se 2 (by rfl) ⟨38859, by rfl⟩) R77719
theorem R70919 : Reach 70919 := rs (se 1 (by rfl) ⟨53189, by rfl⟩) R106379
theorem R70927 : Reach 70927 := rs (se 1 (by rfl) ⟨53195, by rfl⟩) R106391
theorem R103739 : Reach 103739 := rs (se 1 (by rfl) ⟨77804, by rfl⟩) R155609
theorem R70971 : Reach 70971 := rs (se 1 (by rfl) ⟨53228, by rfl⟩) R106457
theorem R103799 : Reach 103799 := rs (se 1 (by rfl) ⟨77849, by rfl⟩) R155699
theorem R71047 : Reach 71047 := rs (se 1 (by rfl) ⟨53285, by rfl⟩) R106571
theorem R103823 : Reach 103823 := rs (se 1 (by rfl) ⟨77867, by rfl⟩) R155735
theorem R71055 : Reach 71055 := rs (se 1 (by rfl) ⟨53291, by rfl⟩) R106583
theorem R234899 : Reach 234899 := rs (se 1 (by rfl) ⟨176174, by rfl⟩) R352349
theorem R103865 : Reach 103865 := rs (se 2 (by rfl) ⟨38949, by rfl⟩) R77899
theorem R71099 : Reach 71099 := rs (se 1 (by rfl) ⟨53324, by rfl⟩) R106649
theorem R103943 : Reach 103943 := rs (se 1 (by rfl) ⟨77957, by rfl⟩) R155915
theorem R103979 : Reach 103979 := rs (se 1 (by rfl) ⟨77984, by rfl⟩) R155969
theorem R300611 : Reach 300611 := rs (se 1 (by rfl) ⟨225458, by rfl⟩) R450917
theorem R104009 : Reach 104009 := rs (se 2 (by rfl) ⟨39003, by rfl⟩) R78007
theorem R104123 : Reach 104123 := rs (se 1 (by rfl) ⟨78092, by rfl⟩) R156185
theorem R104183 : Reach 104183 := rs (se 1 (by rfl) ⟨78137, by rfl⟩) R156275
theorem R104207 : Reach 104207 := rs (se 1 (by rfl) ⟨78155, by rfl⟩) R156311
theorem R530225 : Reach 530225 := rs (se 2 (by rfl) ⟨198834, by rfl⟩) R397669
theorem R104249 : Reach 104249 := rs (se 2 (by rfl) ⟨39093, by rfl⟩) R78187
theorem R104327 : Reach 104327 := rs (se 1 (by rfl) ⟨78245, by rfl⟩) R156491
theorem R104363 : Reach 104363 := rs (se 1 (by rfl) ⟨78272, by rfl⟩) R156545
theorem R104393 : Reach 104393 := rs (se 2 (by rfl) ⟨39147, by rfl⟩) R78295
theorem R333827 : Reach 333827 := rs (se 1 (by rfl) ⟨250370, by rfl⟩) R500741
theorem R104507 : Reach 104507 := rs (se 1 (by rfl) ⟨78380, by rfl⟩) R156761
theorem R104567 : Reach 104567 := rs (se 1 (by rfl) ⟨78425, by rfl⟩) R156851
theorem R104591 : Reach 104591 := rs (se 1 (by rfl) ⟨78443, by rfl⟩) R156887
theorem R104633 : Reach 104633 := rs (se 2 (by rfl) ⟨39237, by rfl⟩) R78475
theorem R104711 : Reach 104711 := rs (se 1 (by rfl) ⟨78533, by rfl⟩) R157067
theorem R399653 : Reach 399653 := rs (se 4 (by rfl) ⟨37467, by rfl⟩) R74935
theorem R104747 : Reach 104747 := rs (se 1 (by rfl) ⟨78560, by rfl⟩) R157121
theorem R104777 : Reach 104777 := rs (se 2 (by rfl) ⟨39291, by rfl⟩) R78583
theorem R268697 : Reach 268697 := rs (se 2 (by rfl) ⟨100761, by rfl⟩) R201523
theorem R104891 : Reach 104891 := rs (se 1 (by rfl) ⟨78668, by rfl⟩) R157337
theorem R104951 : Reach 104951 := rs (se 1 (by rfl) ⟨78713, by rfl⟩) R157427
theorem R104975 : Reach 104975 := rs (se 1 (by rfl) ⟨78731, by rfl⟩) R157463
theorem R203293 : Reach 203293 := rs (se 3 (by rfl) ⟨38117, by rfl⟩) R76235
theorem R105017 : Reach 105017 := rs (se 2 (by rfl) ⟨39381, by rfl⟩) R78763
theorem R105095 : Reach 105095 := rs (se 1 (by rfl) ⟨78821, by rfl⟩) R157643
theorem R105131 : Reach 105131 := rs (se 1 (by rfl) ⟨78848, by rfl⟩) R157697
theorem R1219265 : Reach 1219265 := rs (se 2 (by rfl) ⟨457224, by rfl⟩) R914449
theorem R105161 : Reach 105161 := rs (se 2 (by rfl) ⟨39435, by rfl⟩) R78871
theorem R236303 : Reach 236303 := rs (se 1 (by rfl) ⟨177227, by rfl⟩) R354455
theorem R105275 : Reach 105275 := rs (se 1 (by rfl) ⟨78956, by rfl⟩) R157913
theorem R105335 : Reach 105335 := rs (se 1 (by rfl) ⟨79001, by rfl⟩) R158003
theorem R105359 : Reach 105359 := rs (se 1 (by rfl) ⟨79019, by rfl⟩) R158039
theorem R1579925 : Reach 1579925 := rs (se 6 (by rfl) ⟨37029, by rfl⟩) R74059
theorem R105401 : Reach 105401 := rs (se 2 (by rfl) ⟨39525, by rfl⟩) R79051
theorem R105479 : Reach 105479 := rs (se 1 (by rfl) ⟨79109, by rfl⟩) R158219
theorem R236573 : Reach 236573 := rs (se 3 (by rfl) ⟨44357, by rfl⟩) R88715
theorem R105515 : Reach 105515 := rs (se 1 (by rfl) ⟨79136, by rfl⟩) R158273
theorem R105545 : Reach 105545 := rs (se 2 (by rfl) ⟨39579, by rfl⟩) R79159
theorem R171143 : Reach 171143 := rs (se 1 (by rfl) ⟨128357, by rfl⟩) R256715
theorem R171193 : Reach 171193 := rs (se 2 (by rfl) ⟨64197, by rfl⟩) R128395
theorem R105659 : Reach 105659 := rs (se 1 (by rfl) ⟨79244, by rfl⟩) R158489
theorem R400585 : Reach 400585 := rs (se 2 (by rfl) ⟨150219, by rfl⟩) R300439
theorem R105719 : Reach 105719 := rs (se 1 (by rfl) ⟨79289, by rfl⟩) R158579
theorem R105743 : Reach 105743 := rs (se 1 (by rfl) ⟨79307, by rfl⟩) R158615
theorem R105785 : Reach 105785 := rs (se 2 (by rfl) ⟨39669, by rfl⟩) R79339
theorem R662843 : Reach 662843 := rs (se 1 (by rfl) ⟨497132, by rfl⟩) R994265
theorem R105863 : Reach 105863 := rs (se 1 (by rfl) ⟨79397, by rfl⟩) R158795
theorem R105899 : Reach 105899 := rs (se 1 (by rfl) ⟨79424, by rfl⟩) R158849
theorem R105929 : Reach 105929 := rs (se 2 (by rfl) ⟨39723, by rfl⟩) R79447
theorem R1121795 : Reach 1121795 := rs (se 1 (by rfl) ⟨841346, by rfl⟩) R1682693
theorem R106043 : Reach 106043 := rs (se 1 (by rfl) ⟨79532, by rfl⟩) R159065
theorem R106103 : Reach 106103 := rs (se 1 (by rfl) ⟨79577, by rfl⟩) R159155
theorem R106169 : Reach 106169 := rs (se 2 (by rfl) ⟨39813, by rfl⟩) R79627
theorem R171791 : Reach 171791 := rs (se 1 (by rfl) ⟨128843, by rfl⟩) R257687
theorem R73487 : Reach 73487 := rs (se 1 (by rfl) ⟨55115, by rfl⟩) R110231
theorem R106283 : Reach 106283 := rs (se 1 (by rfl) ⟨79712, by rfl⟩) R159425
theorem R106511 : Reach 106511 := rs (se 1 (by rfl) ⟨79883, by rfl⟩) R159767
theorem R106631 : Reach 106631 := rs (se 1 (by rfl) ⟨79973, by rfl⟩) R159947
theorem R205057 : Reach 205057 := rs (se 2 (by rfl) ⟨76896, by rfl⟩) R153793
theorem R73991 : Reach 73991 := rs (se 1 (by rfl) ⟨55493, by rfl⟩) R110987
theorem R74119 : Reach 74119 := rs (se 1 (by rfl) ⟨55589, by rfl⟩) R111179
theorem R1810835 : Reach 1810835 := rs (se 1 (by rfl) ⟨1358126, by rfl⟩) R2716253
theorem R237977 : Reach 237977 := rs (se 2 (by rfl) ⟨89241, by rfl⟩) R178483
theorem R172489 : Reach 172489 := rs (se 2 (by rfl) ⟨64683, by rfl⟩) R129367
theorem R172631 : Reach 172631 := rs (se 1 (by rfl) ⟨129473, by rfl⟩) R258947
theorem R205715 : Reach 205715 := rs (se 1 (by rfl) ⟨154286, by rfl⟩) R308573
theorem R74683 : Reach 74683 := rs (se 1 (by rfl) ⟨56012, by rfl⟩) R112025
theorem R336919 : Reach 336919 := rs (se 1 (by rfl) ⟨252689, by rfl⟩) R505379
theorem R238679 : Reach 238679 := rs (se 1 (by rfl) ⟨179009, by rfl⟩) R358019
theorem R74939 : Reach 74939 := rs (se 1 (by rfl) ⟨56204, by rfl⟩) R112409
theorem R664865 : Reach 664865 := rs (se 2 (by rfl) ⟨249324, by rfl⟩) R498649
theorem R239057 : Reach 239057 := rs (se 2 (by rfl) ⟨89646, by rfl⟩) R179293
theorem R239165 : Reach 239165 := rs (se 3 (by rfl) ⟨44843, by rfl⟩) R89687
theorem R75919 : Reach 75919 := rs (se 1 (by rfl) ⟨56939, by rfl⟩) R113879
theorem R272585 : Reach 272585 := rs (se 2 (by rfl) ⟨102219, by rfl⟩) R204439
theorem R109001 : Reach 109001 := rs (se 2 (by rfl) ⟨40875, by rfl⟩) R81751
theorem R600605 : Reach 600605 := rs (se 3 (by rfl) ⟨112613, by rfl⟩) R225227
theorem R174707 : Reach 174707 := rs (se 1 (by rfl) ⟨131030, by rfl⟩) R262061
theorem R76423 : Reach 76423 := rs (se 1 (by rfl) ⟨57317, by rfl⟩) R114635
theorem R666305 : Reach 666305 := rs (se 2 (by rfl) ⟨249864, by rfl⟩) R499729
theorem R76603 : Reach 76603 := rs (se 1 (by rfl) ⟨57452, by rfl⟩) R114905
theorem R437309 : Reach 437309 := rs (se 3 (by rfl) ⟨81995, by rfl⟩) R163991
theorem R175223 : Reach 175223 := rs (se 1 (by rfl) ⟨131417, by rfl⟩) R262835
theorem R601289 : Reach 601289 := rs (se 2 (by rfl) ⟨225483, by rfl⟩) R450967
theorem R77071 : Reach 77071 := rs (se 1 (by rfl) ⟨57803, by rfl⟩) R115607
theorem R437537 : Reach 437537 := rs (se 2 (by rfl) ⟨164076, by rfl⟩) R328153
theorem R404945 : Reach 404945 := rs (se 2 (by rfl) ⟨151854, by rfl⟩) R303709
theorem R601667 : Reach 601667 := rs (se 1 (by rfl) ⟨451250, by rfl⟩) R902501
theorem R208585 : Reach 208585 := rs (se 2 (by rfl) ⟨78219, by rfl⟩) R156439
theorem R77575 : Reach 77575 := rs (se 1 (by rfl) ⟨58181, by rfl⟩) R116363
theorem R77755 : Reach 77755 := rs (se 1 (by rfl) ⟨58316, by rfl⟩) R116633
theorem R176215 : Reach 176215 := rs (se 1 (by rfl) ⟨132161, by rfl⟩) R264323
theorem R176519 : Reach 176519 := rs (se 1 (by rfl) ⟨132389, by rfl⟩) R264779
theorem R78223 : Reach 78223 := rs (se 1 (by rfl) ⟨58667, by rfl⟩) R117335
theorem R176651 : Reach 176651 := rs (se 1 (by rfl) ⟨132488, by rfl⟩) R264977
theorem R340523 : Reach 340523 := rs (se 1 (by rfl) ⟨255392, by rfl⟩) R510785
theorem R537281 : Reach 537281 := rs (se 2 (by rfl) ⟨201480, by rfl⟩) R402961
theorem R78727 : Reach 78727 := rs (se 1 (by rfl) ⟨59045, by rfl⟩) R118091
theorem R177167 : Reach 177167 := rs (se 1 (by rfl) ⟨132875, by rfl⟩) R265751
theorem R78907 : Reach 78907 := rs (se 1 (by rfl) ⟨59180, by rfl⟩) R118361
theorem R341111 : Reach 341111 := rs (se 1 (by rfl) ⟨255833, by rfl⟩) R511667
theorem R177299 : Reach 177299 := rs (se 1 (by rfl) ⟨132974, by rfl⟩) R265949
theorem R341263 : Reach 341263 := rs (se 1 (by rfl) ⟨255947, by rfl⟩) R511895
theorem R538001 : Reach 538001 := rs (se 2 (by rfl) ⟨201750, by rfl⟩) R403501
theorem R144787 : Reach 144787 := rs (se 1 (by rfl) ⟨108590, by rfl⟩) R217181
theorem R1291697 : Reach 1291697 := rs (se 2 (by rfl) ⟨484386, by rfl⟩) R968773
theorem R1553843 : Reach 1553843 := rs (se 1 (by rfl) ⟨1165382, by rfl⟩) R2330765
theorem R79375 : Reach 79375 := rs (se 1 (by rfl) ⟨59531, by rfl⟩) R119063
theorem R341819 : Reach 341819 := rs (se 1 (by rfl) ⟨256364, by rfl⟩) R512729
theorem R210775 : Reach 210775 := rs (se 1 (by rfl) ⟨158081, by rfl⟩) R316163
theorem R79735 : Reach 79735 := rs (se 1 (by rfl) ⟨59801, by rfl⟩) R119603
theorem R341981 : Reach 341981 := rs (se 3 (by rfl) ⟨64121, by rfl⟩) R128243
theorem R79879 : Reach 79879 := rs (se 1 (by rfl) ⟨59909, by rfl⟩) R119819
theorem R79915 : Reach 79915 := rs (se 1 (by rfl) ⟨59936, by rfl⟩) R119873
theorem R440407 : Reach 440407 := rs (se 1 (by rfl) ⟨330305, by rfl⟩) R660611
theorem R1194101 : Reach 1194101 := rs (se 5 (by rfl) ⟨55973, by rfl⟩) R111947
theorem R178433 : Reach 178433 := rs (se 2 (by rfl) ⟨66912, by rfl⟩) R133825
theorem R342305 : Reach 342305 := rs (se 2 (by rfl) ⟨128364, by rfl⟩) R256729
theorem R178807 : Reach 178807 := rs (se 1 (by rfl) ⟨134105, by rfl⟩) R268211
theorem R1784591 : Reach 1784591 := rs (se 1 (by rfl) ⟨1338443, by rfl⟩) R2676887
theorem R604979 : Reach 604979 := rs (se 1 (by rfl) ⟨453734, by rfl⟩) R907469
theorem R113467 : Reach 113467 := rs (se 1 (by rfl) ⟨85100, by rfl⟩) R170201
theorem R113593 : Reach 113593 := rs (se 2 (by rfl) ⟨42597, by rfl⟩) R85195
theorem R113609 : Reach 113609 := rs (se 2 (by rfl) ⟨42603, by rfl⟩) R85207
theorem R179243 : Reach 179243 := rs (se 1 (by rfl) ⟨134432, by rfl⟩) R268865
theorem R343277 : Reach 343277 := rs (se 3 (by rfl) ⟨64364, by rfl⟩) R128729
theorem R834875 : Reach 834875 := rs (se 1 (by rfl) ⟨626156, by rfl⟩) R1252313
theorem R114311 : Reach 114311 := rs (se 1 (by rfl) ⟨85733, by rfl⟩) R171467
theorem R376613 : Reach 376613 := rs (se 4 (by rfl) ⟨35307, by rfl⟩) R70615
theorem R606041 : Reach 606041 := rs (se 2 (by rfl) ⟨227265, by rfl⟩) R454531
theorem R671651 : Reach 671651 := rs (se 1 (by rfl) ⟨503738, by rfl⟩) R1007477
theorem R344087 : Reach 344087 := rs (se 1 (by rfl) ⟨258065, by rfl⟩) R516131
theorem R1327373 : Reach 1327373 := rs (se 3 (by rfl) ⟨248882, by rfl⟩) R497765
theorem R114959 : Reach 114959 := rs (se 1 (by rfl) ⟨86219, by rfl⟩) R172439
theorem R803357 : Reach 803357 := rs (se 3 (by rfl) ⟨150629, by rfl⟩) R301259
theorem R672299 : Reach 672299 := rs (se 1 (by rfl) ⟨504224, by rfl⟩) R1008449
theorem R115499 : Reach 115499 := rs (se 1 (by rfl) ⟨86624, by rfl⟩) R173249
theorem R574361 : Reach 574361 := rs (se 2 (by rfl) ⟨215385, by rfl⟩) R430771
theorem R148409 : Reach 148409 := rs (se 2 (by rfl) ⟨55653, by rfl⟩) R111307
theorem R115897 : Reach 115897 := rs (se 2 (by rfl) ⟨43461, by rfl⟩) R86923
theorem R148871 : Reach 148871 := rs (se 1 (by rfl) ⟨111653, by rfl⟩) R223307
theorem R116599 : Reach 116599 := rs (se 1 (by rfl) ⟨87449, by rfl⟩) R174899
theorem R378769 : Reach 378769 := rs (se 2 (by rfl) ⟨142038, by rfl⟩) R284077
theorem R411601 : Reach 411601 := rs (se 2 (by rfl) ⟨154350, by rfl⟩) R308701
theorem R116795 : Reach 116795 := rs (se 1 (by rfl) ⟨87596, by rfl⟩) R175193
theorem R313463 : Reach 313463 := rs (se 1 (by rfl) ⟨235097, by rfl⟩) R470195
theorem R182425 : Reach 182425 := rs (se 2 (by rfl) ⟨68409, by rfl⟩) R136819
theorem R1001645 : Reach 1001645 := rs (se 3 (by rfl) ⟨187808, by rfl⟩) R375617
theorem R248179 : Reach 248179 := rs (se 1 (by rfl) ⟨186134, by rfl⟩) R372269
theorem R182675 : Reach 182675 := rs (se 1 (by rfl) ⟨137006, by rfl⟩) R274013
theorem R117193 : Reach 117193 := rs (se 2 (by rfl) ⟨43947, by rfl⟩) R87895
theorem R608771 : Reach 608771 := rs (se 1 (by rfl) ⟨456578, by rfl⟩) R913157
theorem R150049 : Reach 150049 := rs (se 2 (by rfl) ⟨56268, by rfl⟩) R112537
theorem R347165 : Reach 347165 := rs (se 3 (by rfl) ⟨65093, by rfl⟩) R130187
theorem R117895 : Reach 117895 := rs (se 1 (by rfl) ⟨88421, by rfl⟩) R176843
theorem R1953233 : Reach 1953233 := rs (se 2 (by rfl) ⟨732462, by rfl⟩) R1464925
theorem R183809 : Reach 183809 := rs (se 2 (by rfl) ⟨68928, by rfl⟩) R137857
theorem R347651 : Reach 347651 := rs (se 1 (by rfl) ⟨260738, by rfl⟩) R521477
theorem R151055 : Reach 151055 := rs (se 1 (by rfl) ⟨113291, by rfl⟩) R226583
theorem R151073 : Reach 151073 := rs (se 2 (by rfl) ⟨56652, by rfl⟩) R113305
theorem R216847 : Reach 216847 := rs (se 1 (by rfl) ⟨162635, by rfl⟩) R325271
theorem R118543 : Reach 118543 := rs (se 1 (by rfl) ⟨88907, by rfl⟩) R177815
theorem R85819 : Reach 85819 := rs (se 1 (by rfl) ⟨64364, by rfl⟩) R128729
theorem R151415 : Reach 151415 := rs (se 1 (by rfl) ⟨113561, by rfl⟩) R227123
theorem R905111 : Reach 905111 := rs (se 1 (by rfl) ⟨678833, by rfl⟩) R1357667
theorem R151595 : Reach 151595 := rs (se 1 (by rfl) ⟨113696, by rfl⟩) R227393
theorem R119083 : Reach 119083 := rs (se 1 (by rfl) ⟨89312, by rfl⟩) R178625
theorem R414011 : Reach 414011 := rs (se 1 (by rfl) ⟨310508, by rfl⟩) R621017
theorem R151955 : Reach 151955 := rs (se 1 (by rfl) ⟨113966, by rfl⟩) R227933
theorem R446867 : Reach 446867 := rs (se 1 (by rfl) ⟨335150, by rfl⟩) R670301
theorem R119225 : Reach 119225 := rs (se 2 (by rfl) ⟨44709, by rfl⟩) R89419
theorem R152009 : Reach 152009 := rs (se 2 (by rfl) ⟨57003, by rfl⟩) R114007
theorem R1167857 : Reach 1167857 := rs (se 2 (by rfl) ⟨437946, by rfl⟩) R875893
theorem R479773 : Reach 479773 := rs (se 3 (by rfl) ⟨89957, by rfl⟩) R179915
theorem R86827 : Reach 86827 := rs (se 1 (by rfl) ⟨65120, by rfl⟩) R130241
theorem R807731 : Reach 807731 := rs (se 1 (by rfl) ⟨605798, by rfl⟩) R1211597
theorem R349271 : Reach 349271 := rs (se 1 (by rfl) ⟨261953, by rfl⟩) R523907
theorem R119927 : Reach 119927 := rs (se 1 (by rfl) ⟨89945, by rfl⟩) R179891
theorem R152711 : Reach 152711 := rs (se 1 (by rfl) ⟨114533, by rfl⟩) R229067
theorem R152891 : Reach 152891 := rs (se 1 (by rfl) ⟨114668, by rfl⟩) R229337
theorem R153017 : Reach 153017 := rs (se 2 (by rfl) ⟨57381, by rfl⟩) R114763
theorem R382475 : Reach 382475 := rs (se 1 (by rfl) ⟨286856, by rfl⟩) R573713
theorem R349757 : Reach 349757 := rs (se 3 (by rfl) ⟨65579, by rfl⟩) R131159
theorem R185971 : Reach 185971 := rs (se 1 (by rfl) ⟨139478, by rfl⟩) R278957
theorem R677605 : Reach 677605 := rs (se 4 (by rfl) ⟨63525, by rfl⟩) R127051
theorem R87799 : Reach 87799 := rs (se 1 (by rfl) ⟨65849, by rfl⟩) R131699
theorem R153359 : Reach 153359 := rs (se 1 (by rfl) ⟨115019, by rfl⟩) R230039
theorem R153377 : Reach 153377 := rs (se 2 (by rfl) ⟨57516, by rfl⟩) R115033
theorem R415691 : Reach 415691 := rs (se 1 (by rfl) ⟨311768, by rfl⟩) R623537
theorem R219179 : Reach 219179 := rs (se 1 (by rfl) ⟨164384, by rfl⟩) R328769
theorem R88123 : Reach 88123 := rs (se 1 (by rfl) ⟨66092, by rfl⟩) R132185
theorem R153719 : Reach 153719 := rs (se 1 (by rfl) ⟨115289, by rfl⟩) R230579
theorem R1038581 : Reach 1038581 := rs (se 5 (by rfl) ⟨48683, by rfl⟩) R97367
theorem R153899 : Reach 153899 := rs (se 1 (by rfl) ⟨115424, by rfl⟩) R230849
theorem R186923 : Reach 186923 := rs (se 1 (by rfl) ⟨140192, by rfl⟩) R280385
theorem R154259 : Reach 154259 := rs (se 1 (by rfl) ⟨115694, by rfl⟩) R231389
theorem R154313 : Reach 154313 := rs (se 2 (by rfl) ⟨57867, by rfl⟩) R115735
theorem R777113 : Reach 777113 := rs (se 2 (by rfl) ⟨291417, by rfl⟩) R582835
theorem R2579363 : Reach 2579363 := rs (se 1 (by rfl) ⟨1934522, by rfl⟩) R3869045
theorem R89095 : Reach 89095 := rs (se 1 (by rfl) ⟨66821, by rfl⟩) R133643
theorem R515159 : Reach 515159 := rs (se 1 (by rfl) ⟨386369, by rfl⟩) R772739
theorem R121991 : Reach 121991 := rs (se 1 (by rfl) ⟨91493, by rfl⟩) R182987
theorem R351539 : Reach 351539 := rs (se 1 (by rfl) ⟨263654, by rfl⟩) R527309
theorem R155015 : Reach 155015 := rs (se 1 (by rfl) ⟨116261, by rfl⟩) R232523
theorem R89515 : Reach 89515 := rs (se 1 (by rfl) ⟨67136, by rfl⟩) R134273
theorem R155081 : Reach 155081 := rs (se 2 (by rfl) ⟨58155, by rfl⟩) R116311
theorem R679373 : Reach 679373 := rs (se 3 (by rfl) ⟨127382, by rfl⟩) R254765
theorem R155195 : Reach 155195 := rs (se 1 (by rfl) ⟨116396, by rfl⟩) R232793
theorem R351863 : Reach 351863 := rs (se 1 (by rfl) ⟨263897, by rfl⟩) R527795
theorem R89743 : Reach 89743 := rs (se 1 (by rfl) ⟨67307, by rfl⟩) R134615
theorem R155321 : Reach 155321 := rs (se 2 (by rfl) ⟨58245, by rfl⟩) R116491
theorem R122683 : Reach 122683 := rs (se 1 (by rfl) ⟨92012, by rfl⟩) R184025
theorem R155663 : Reach 155663 := rs (se 1 (by rfl) ⟨116747, by rfl⟩) R233495
theorem R155681 : Reach 155681 := rs (se 2 (by rfl) ⟨58380, by rfl⟩) R116761
theorem R942353 : Reach 942353 := rs (se 2 (by rfl) ⟨353382, by rfl⟩) R706765
theorem R156023 : Reach 156023 := rs (se 1 (by rfl) ⟨117017, by rfl⟩) R234035
theorem R516611 : Reach 516611 := rs (se 1 (by rfl) ⟨387458, by rfl⟩) R774917
theorem R1663523 : Reach 1663523 := rs (se 1 (by rfl) ⟨1247642, by rfl⟩) R2495285
theorem R156203 : Reach 156203 := rs (se 1 (by rfl) ⟨117152, by rfl⟩) R234305
theorem R352835 : Reach 352835 := rs (se 1 (by rfl) ⟨264626, by rfl⟩) R529253
theorem R287489 : Reach 287489 := rs (se 2 (by rfl) ⟨107808, by rfl⟩) R215617
theorem R353159 : Reach 353159 := rs (se 1 (by rfl) ⟨264869, by rfl⟩) R529739
theorem R156563 : Reach 156563 := rs (se 1 (by rfl) ⟨117422, by rfl⟩) R234845
theorem R156617 : Reach 156617 := rs (se 2 (by rfl) ⟨58731, by rfl⟩) R117463
theorem R91535 : Reach 91535 := rs (se 1 (by rfl) ⟨68651, by rfl⟩) R137303
theorem R255575 : Reach 255575 := rs (se 1 (by rfl) ⟨191681, by rfl⟩) R383363
theorem R157319 : Reach 157319 := rs (se 1 (by rfl) ⟨117989, by rfl⟩) R235979
theorem R157499 : Reach 157499 := rs (se 1 (by rfl) ⟨118124, by rfl⟩) R236249
theorem R386963 : Reach 386963 := rs (se 1 (by rfl) ⟨290222, by rfl⟩) R580445
theorem R157625 : Reach 157625 := rs (se 2 (by rfl) ⟨59109, by rfl⟩) R118219
theorem R256061 : Reach 256061 := rs (se 3 (by rfl) ⟨48011, by rfl⟩) R96023
theorem R157967 : Reach 157967 := rs (se 1 (by rfl) ⟨118475, by rfl⟩) R236951
theorem R157985 : Reach 157985 := rs (se 2 (by rfl) ⟨59244, by rfl⟩) R118489
theorem R387463 : Reach 387463 := rs (se 1 (by rfl) ⟨290597, by rfl⟩) R581195
theorem R322001 : Reach 322001 := rs (se 2 (by rfl) ⟨120750, by rfl⟩) R241501
theorem R158327 : Reach 158327 := rs (se 1 (by rfl) ⟨118745, by rfl⟩) R237491
theorem R453377 : Reach 453377 := rs (se 2 (by rfl) ⟨170016, by rfl⟩) R340033
theorem R191261 : Reach 191261 := rs (se 3 (by rfl) ⟨35861, by rfl⟩) R71723
theorem R158507 : Reach 158507 := rs (se 1 (by rfl) ⟨118880, by rfl⟩) R237761
theorem R486233 : Reach 486233 := rs (se 2 (by rfl) ⟨182337, by rfl⟩) R364675
theorem R158611 : Reach 158611 := rs (se 1 (by rfl) ⟨118958, by rfl⟩) R237917
theorem R453529 : Reach 453529 := rs (se 2 (by rfl) ⟨170073, by rfl⟩) R340147
theorem R257053 : Reach 257053 := rs (se 3 (by rfl) ⟨48197, by rfl⟩) R96395
theorem R158867 : Reach 158867 := rs (se 1 (by rfl) ⟨119150, by rfl⟩) R238301
theorem R158921 : Reach 158921 := rs (se 2 (by rfl) ⟨59595, by rfl⟩) R119191
theorem R421157 : Reach 421157 := rs (se 4 (by rfl) ⟨39483, by rfl⟩) R78967
theorem R257489 : Reach 257489 := rs (se 2 (by rfl) ⟨96558, by rfl⟩) R193117
theorem R159623 : Reach 159623 := rs (se 1 (by rfl) ⟨119717, by rfl⟩) R239435
theorem R159641 : Reach 159641 := rs (se 2 (by rfl) ⟨59865, by rfl⟩) R119731
theorem R421841 : Reach 421841 := rs (se 2 (by rfl) ⟨158190, by rfl⟩) R316381
theorem R1339415 : Reach 1339415 := rs (se 1 (by rfl) ⟨1004561, by rfl⟩) R2009123
theorem R2945069 : Reach 2945069 := rs (se 3 (by rfl) ⟨552200, by rfl⟩) R1104401
theorem R159803 : Reach 159803 := rs (se 1 (by rfl) ⟨119852, by rfl⟩) R239705
theorem R159929 : Reach 159929 := rs (se 2 (by rfl) ⟨59973, by rfl⟩) R119947
theorem R160001 : Reach 160001 := rs (se 2 (by rfl) ⟨60000, by rfl⟩) R120001
theorem R356723 : Reach 356723 := rs (se 1 (by rfl) ⟨267542, by rfl⟩) R535085
theorem R160271 : Reach 160271 := rs (se 1 (by rfl) ⟨120203, by rfl⟩) R240407
theorem R94907 : Reach 94907 := rs (se 1 (by rfl) ⟨71180, by rfl⟩) R142361
theorem R193367 : Reach 193367 := rs (se 1 (by rfl) ⟨145025, by rfl⟩) R290051
theorem R357209 : Reach 357209 := rs (se 2 (by rfl) ⟨133953, by rfl⟩) R267907
theorem R259159 : Reach 259159 := rs (se 1 (by rfl) ⟨194369, by rfl⟩) R388739
theorem R128299 : Reach 128299 := rs (se 1 (by rfl) ⟨96224, by rfl⟩) R192449
theorem R259463 : Reach 259463 := rs (se 1 (by rfl) ⟨194597, by rfl⟩) R389195
theorem R226745 : Reach 226745 := rs (se 2 (by rfl) ⟨85029, by rfl⟩) R170059
theorem R128441 : Reach 128441 := rs (se 2 (by rfl) ⟨48165, by rfl⟩) R96331
theorem R259645 : Reach 259645 := rs (se 3 (by rfl) ⟨48683, by rfl⟩) R97367
theorem R194233 : Reach 194233 := rs (se 2 (by rfl) ⟨72837, by rfl⟩) R145675
theorem R358145 : Reach 358145 := rs (se 2 (by rfl) ⟨134304, by rfl⟩) R268609
theorem R128783 : Reach 128783 := rs (se 1 (by rfl) ⟨96587, by rfl⟩) R193175
theorem R358181 : Reach 358181 := rs (se 4 (by rfl) ⟨33579, by rfl⟩) R67159
theorem R325579 : Reach 325579 := rs (se 1 (by rfl) ⟨244184, by rfl⟩) R488369
theorem R227339 : Reach 227339 := rs (se 1 (by rfl) ⟨170504, by rfl⟩) R341009
theorem R194575 : Reach 194575 := rs (se 1 (by rfl) ⟨145931, by rfl⟩) R291863
theorem R227447 : Reach 227447 := rs (se 1 (by rfl) ⟨170585, by rfl⟩) R341171
theorem R161945 : Reach 161945 := rs (se 2 (by rfl) ⟨60729, by rfl⟩) R121459
theorem R161993 : Reach 161993 := rs (se 2 (by rfl) ⟨60747, by rfl⟩) R121495
theorem R227585 : Reach 227585 := rs (se 2 (by rfl) ⟨85344, by rfl⟩) R170689
theorem R194849 : Reach 194849 := rs (se 2 (by rfl) ⟨73068, by rfl⟩) R146137
theorem R293179 : Reach 293179 := rs (se 1 (by rfl) ⟨219884, by rfl⟩) R439769
theorem R162167 : Reach 162167 := rs (se 1 (by rfl) ⟨121625, by rfl⟩) R243251
theorem R588167 : Reach 588167 := rs (se 1 (by rfl) ⟨441125, by rfl⟩) R882251
theorem R227731 : Reach 227731 := rs (se 1 (by rfl) ⟨170798, by rfl⟩) R341597
theorem R129595 : Reach 129595 := rs (se 1 (by rfl) ⟨97196, by rfl⟩) R194393
theorem R129671 : Reach 129671 := rs (se 1 (by rfl) ⟨97253, by rfl⟩) R194507
theorem R228041 : Reach 228041 := rs (se 2 (by rfl) ⟨85515, by rfl⟩) R171031
theorem R588545 : Reach 588545 := rs (se 2 (by rfl) ⟨220704, by rfl⟩) R441409
theorem R293665 : Reach 293665 := rs (se 2 (by rfl) ⟨110124, by rfl⟩) R220249
theorem R654155 : Reach 654155 := rs (se 1 (by rfl) ⟨490616, by rfl⟩) R981233
theorem R195463 : Reach 195463 := rs (se 1 (by rfl) ⟨146597, by rfl⟩) R293195
theorem R359315 : Reach 359315 := rs (se 1 (by rfl) ⟨269486, by rfl⟩) R538973
theorem R130081 : Reach 130081 := rs (se 2 (by rfl) ⟨48780, by rfl⟩) R97561
theorem R97481 : Reach 97481 := rs (se 2 (by rfl) ⟨36555, by rfl⟩) R73111
theorem R261377 : Reach 261377 := rs (se 2 (by rfl) ⟨98016, by rfl⟩) R196033
theorem R195851 : Reach 195851 := rs (se 1 (by rfl) ⟨146888, by rfl⟩) R293777
theorem R130423 : Reach 130423 := rs (se 1 (by rfl) ⟨97817, by rfl⟩) R195635
theorem R228743 : Reach 228743 := rs (se 1 (by rfl) ⟨171557, by rfl⟩) R343115
theorem R294461 : Reach 294461 := rs (se 3 (by rfl) ⟨55211, by rfl⟩) R110423
theorem R229121 : Reach 229121 := rs (se 2 (by rfl) ⟨85920, by rfl⟩) R171841
theorem R393113 : Reach 393113 := rs (se 2 (by rfl) ⟨147417, by rfl⟩) R294835
theorem R229391 : Reach 229391 := rs (se 1 (by rfl) ⟨172043, by rfl⟩) R344087
theorem R131129 : Reach 131129 := rs (se 2 (by rfl) ⟨49173, by rfl⟩) R98347
theorem R884915 : Reach 884915 := rs (se 1 (by rfl) ⟨663686, by rfl⟩) R1327373
theorem R98825 : Reach 98825 := rs (se 2 (by rfl) ⟨37059, by rfl⟩) R74119
theorem R2228795 : Reach 2228795 := rs (se 1 (by rfl) ⟨1671596, by rfl⟩) R3343193
theorem R229985 : Reach 229985 := rs (se 2 (by rfl) ⟨86244, by rfl⟩) R172489
theorem R98939 : Reach 98939 := rs (se 1 (by rfl) ⟨74204, by rfl⟩) R148409
theorem R197309 : Reach 197309 := rs (se 3 (by rfl) ⟨36995, by rfl⟩) R73991
theorem R262865 : Reach 262865 := rs (se 2 (by rfl) ⟨98574, by rfl⟩) R197149
theorem R99247 : Reach 99247 := rs (se 1 (by rfl) ⟨74435, by rfl⟩) R148871
theorem R263321 : Reach 263321 := rs (se 2 (by rfl) ⟨98745, by rfl⟩) R197491
theorem R99577 : Reach 99577 := rs (se 2 (by rfl) ⟨37341, by rfl⟩) R74683
theorem R132617 : Reach 132617 := rs (se 2 (by rfl) ⟨49731, by rfl⟩) R99463
theorem R67151 : Reach 67151 := rs (se 1 (by rfl) ⟨50363, by rfl⟩) R100727
theorem R67167 : Reach 67167 := rs (se 1 (by rfl) ⟨50375, by rfl⟩) R100751
theorem R67195 : Reach 67195 := rs (se 1 (by rfl) ⟨50396, by rfl⟩) R100793
theorem R67247 : Reach 67247 := rs (se 1 (by rfl) ⟨50435, by rfl⟩) R100871
theorem R67271 : Reach 67271 := rs (se 1 (by rfl) ⟨50453, by rfl⟩) R100907
theorem R67291 : Reach 67291 := rs (se 1 (by rfl) ⟨50468, by rfl⟩) R100937
theorem R67367 : Reach 67367 := rs (se 1 (by rfl) ⟨50525, by rfl⟩) R101051
theorem R67407 : Reach 67407 := rs (se 1 (by rfl) ⟨50555, by rfl⟩) R101111
theorem R67423 : Reach 67423 := rs (se 1 (by rfl) ⟨50567, by rfl⟩) R101135
theorem R67451 : Reach 67451 := rs (se 1 (by rfl) ⟨50588, by rfl⟩) R101177
theorem R67503 : Reach 67503 := rs (se 1 (by rfl) ⟨50627, by rfl⟩) R101255
theorem R67527 : Reach 67527 := rs (se 1 (by rfl) ⟨50645, by rfl⟩) R101291
theorem R67547 : Reach 67547 := rs (se 1 (by rfl) ⟨50660, by rfl⟩) R101321
theorem R395279 : Reach 395279 := rs (se 1 (by rfl) ⟨296459, by rfl⟩) R592919
theorem R231443 : Reach 231443 := rs (se 1 (by rfl) ⟨173582, by rfl⟩) R347165
theorem R67623 : Reach 67623 := rs (se 1 (by rfl) ⟨50717, by rfl⟩) R101435
theorem R67663 : Reach 67663 := rs (se 1 (by rfl) ⟨50747, by rfl⟩) R101495
theorem R67679 : Reach 67679 := rs (se 1 (by rfl) ⟨50759, by rfl⟩) R101519
theorem R67707 : Reach 67707 := rs (se 1 (by rfl) ⟨50780, by rfl⟩) R101561
theorem R67759 : Reach 67759 := rs (se 1 (by rfl) ⟨50819, by rfl⟩) R101639
theorem R67783 : Reach 67783 := rs (se 1 (by rfl) ⟨50837, by rfl⟩) R101675
theorem R67803 : Reach 67803 := rs (se 1 (by rfl) ⟨50852, by rfl⟩) R101705
theorem R67879 : Reach 67879 := rs (se 1 (by rfl) ⟨50909, by rfl⟩) R101819
theorem R67919 : Reach 67919 := rs (se 1 (by rfl) ⟨50939, by rfl⟩) R101879
theorem R231767 : Reach 231767 := rs (se 1 (by rfl) ⟨173825, by rfl⟩) R347651
theorem R100703 : Reach 100703 := rs (se 1 (by rfl) ⟨75527, by rfl⟩) R151055
theorem R67935 : Reach 67935 := rs (se 1 (by rfl) ⟨50951, by rfl⟩) R101903
theorem R100715 : Reach 100715 := rs (se 1 (by rfl) ⟨75536, by rfl⟩) R151073
theorem R133483 : Reach 133483 := rs (se 1 (by rfl) ⟨100112, by rfl⟩) R200225
theorem R67963 : Reach 67963 := rs (se 1 (by rfl) ⟨50972, by rfl⟩) R101945
theorem R68015 : Reach 68015 := rs (se 1 (by rfl) ⟨51011, by rfl⟩) R102023
theorem R133559 : Reach 133559 := rs (se 1 (by rfl) ⟨100169, by rfl⟩) R200339
theorem R68039 : Reach 68039 := rs (se 1 (by rfl) ⟨51029, by rfl⟩) R102059
theorem R68059 : Reach 68059 := rs (se 1 (by rfl) ⟨51044, by rfl⟩) R102089
theorem R68135 : Reach 68135 := rs (se 1 (by rfl) ⟨51101, by rfl⟩) R102203
theorem R100943 : Reach 100943 := rs (se 1 (by rfl) ⟨75707, by rfl⟩) R151415
theorem R68175 : Reach 68175 := rs (se 1 (by rfl) ⟨51131, by rfl⟩) R102263
theorem R68191 : Reach 68191 := rs (se 1 (by rfl) ⟨51143, by rfl⟩) R102287
theorem R68219 : Reach 68219 := rs (se 1 (by rfl) ⟨51164, by rfl⟩) R102329
theorem R68271 : Reach 68271 := rs (se 1 (by rfl) ⟨51203, by rfl⟩) R102407
theorem R101063 : Reach 101063 := rs (se 1 (by rfl) ⟨75797, by rfl⟩) R151595
theorem R68295 : Reach 68295 := rs (se 1 (by rfl) ⟨51221, by rfl⟩) R102443
theorem R68315 : Reach 68315 := rs (se 1 (by rfl) ⟨51236, by rfl⟩) R102473
theorem R68391 : Reach 68391 := rs (se 1 (by rfl) ⟨51293, by rfl⟩) R102587
theorem R1084229 : Reach 1084229 := rs (se 4 (by rfl) ⟨101646, by rfl⟩) R203293
theorem R2558789 : Reach 2558789 := rs (se 4 (by rfl) ⟨239886, by rfl⟩) R479773
theorem R68431 : Reach 68431 := rs (se 1 (by rfl) ⟨51323, by rfl⟩) R102647
theorem R68447 : Reach 68447 := rs (se 1 (by rfl) ⟨51335, by rfl⟩) R102671
theorem R101225 : Reach 101225 := rs (se 2 (by rfl) ⟨37959, by rfl⟩) R75919
theorem R68475 : Reach 68475 := rs (se 1 (by rfl) ⟨51356, by rfl⟩) R102713
theorem R68527 : Reach 68527 := rs (se 1 (by rfl) ⟨51395, by rfl⟩) R102791
theorem R101303 : Reach 101303 := rs (se 1 (by rfl) ⟨75977, by rfl⟩) R151955
theorem R297911 : Reach 297911 := rs (se 1 (by rfl) ⟨223433, by rfl⟩) R446867
theorem R134075 : Reach 134075 := rs (se 1 (by rfl) ⟨100556, by rfl⟩) R201113
theorem R68551 : Reach 68551 := rs (se 1 (by rfl) ⟨51413, by rfl⟩) R102827
theorem R101339 : Reach 101339 := rs (se 1 (by rfl) ⟨76004, by rfl⟩) R152009
theorem R68571 : Reach 68571 := rs (se 1 (by rfl) ⟨51428, by rfl⟩) R102857
theorem R68647 : Reach 68647 := rs (se 1 (by rfl) ⟨51485, by rfl⟩) R102971
theorem R68687 : Reach 68687 := rs (se 1 (by rfl) ⟨51515, by rfl⟩) R103031
theorem R265295 : Reach 265295 := rs (se 1 (by rfl) ⟨198971, by rfl⟩) R397943
theorem R68703 : Reach 68703 := rs (se 1 (by rfl) ⟨51527, by rfl⟩) R103055
theorem R68731 : Reach 68731 := rs (se 1 (by rfl) ⟨51548, by rfl⟩) R103097
theorem R330905 : Reach 330905 := rs (se 2 (by rfl) ⟨124089, by rfl⟩) R248179
theorem R199837 : Reach 199837 := rs (se 3 (by rfl) ⟨37469, by rfl⟩) R74939
theorem R68783 : Reach 68783 := rs (se 1 (by rfl) ⟨51587, by rfl⟩) R103175
theorem R68807 : Reach 68807 := rs (se 1 (by rfl) ⟨51605, by rfl⟩) R103211
theorem R68827 : Reach 68827 := rs (se 1 (by rfl) ⟨51620, by rfl⟩) R103241
theorem R265463 : Reach 265463 := rs (se 1 (by rfl) ⟨199097, by rfl⟩) R398195
theorem R68903 : Reach 68903 := rs (se 1 (by rfl) ⟨51677, by rfl⟩) R103355
theorem R68943 : Reach 68943 := rs (se 1 (by rfl) ⟨51707, by rfl⟩) R103415
theorem R68959 : Reach 68959 := rs (se 1 (by rfl) ⟨51719, by rfl⟩) R103439
theorem R68987 : Reach 68987 := rs (se 1 (by rfl) ⟨51740, by rfl⟩) R103481
theorem R200065 : Reach 200065 := rs (se 2 (by rfl) ⟨75024, by rfl⟩) R150049
theorem R232847 : Reach 232847 := rs (se 1 (by rfl) ⟨174635, by rfl⟩) R349271
theorem R134561 : Reach 134561 := rs (se 2 (by rfl) ⟨50460, by rfl⟩) R100921
theorem R101807 : Reach 101807 := rs (se 1 (by rfl) ⟨76355, by rfl⟩) R152711
theorem R69039 : Reach 69039 := rs (se 1 (by rfl) ⟨51779, by rfl⟩) R103559
theorem R69063 : Reach 69063 := rs (se 1 (by rfl) ⟨51797, by rfl⟩) R103595
theorem R69083 : Reach 69083 := rs (se 1 (by rfl) ⟨51812, by rfl⟩) R103625
theorem R101897 : Reach 101897 := rs (se 2 (by rfl) ⟨38211, by rfl⟩) R76423
theorem R101927 : Reach 101927 := rs (se 1 (by rfl) ⟨76445, by rfl⟩) R152891
theorem R69159 : Reach 69159 := rs (se 1 (by rfl) ⟨51869, by rfl⟩) R103739
theorem R134713 : Reach 134713 := rs (se 2 (by rfl) ⟨50517, by rfl⟩) R101035
theorem R69199 : Reach 69199 := rs (se 1 (by rfl) ⟨51899, by rfl⟩) R103799
theorem R69215 : Reach 69215 := rs (se 1 (by rfl) ⟨51911, by rfl⟩) R103823
theorem R102011 : Reach 102011 := rs (se 1 (by rfl) ⟨76508, by rfl⟩) R153017
theorem R69243 : Reach 69243 := rs (se 1 (by rfl) ⟨51932, by rfl⟩) R103865
theorem R69295 : Reach 69295 := rs (se 1 (by rfl) ⟨51971, by rfl⟩) R103943
theorem R69319 : Reach 69319 := rs (se 1 (by rfl) ⟨51989, by rfl⟩) R103979
theorem R233171 : Reach 233171 := rs (se 1 (by rfl) ⟨174878, by rfl⟩) R349757
theorem R200407 : Reach 200407 := rs (se 1 (by rfl) ⟨150305, by rfl⟩) R300611
theorem R69339 : Reach 69339 := rs (se 1 (by rfl) ⟨52004, by rfl⟩) R104009
theorem R102137 : Reach 102137 := rs (se 2 (by rfl) ⟨38301, by rfl⟩) R76603
theorem R69415 : Reach 69415 := rs (se 1 (by rfl) ⟨52061, by rfl⟩) R104123
theorem R69455 : Reach 69455 := rs (se 1 (by rfl) ⟨52091, by rfl⟩) R104183
theorem R102239 : Reach 102239 := rs (se 1 (by rfl) ⟨76679, by rfl⟩) R153359
theorem R69471 : Reach 69471 := rs (se 1 (by rfl) ⟨52103, by rfl⟩) R104207
theorem R135017 : Reach 135017 := rs (se 2 (by rfl) ⟨50631, by rfl⟩) R101263
theorem R102251 : Reach 102251 := rs (se 1 (by rfl) ⟨76688, by rfl⟩) R153377
theorem R69499 : Reach 69499 := rs (se 1 (by rfl) ⟨52124, by rfl⟩) R104249
theorem R69551 : Reach 69551 := rs (se 1 (by rfl) ⟨52163, by rfl⟩) R104327
theorem R69575 : Reach 69575 := rs (se 1 (by rfl) ⟨52181, by rfl⟩) R104363
theorem R69595 : Reach 69595 := rs (se 1 (by rfl) ⟨52196, by rfl⟩) R104393
theorem R69671 : Reach 69671 := rs (se 1 (by rfl) ⟨52253, by rfl⟩) R104507
theorem R102479 : Reach 102479 := rs (se 1 (by rfl) ⟨76859, by rfl⟩) R153719
theorem R69711 : Reach 69711 := rs (se 1 (by rfl) ⟨52283, by rfl⟩) R104567
theorem R69727 : Reach 69727 := rs (se 1 (by rfl) ⟨52295, by rfl⟩) R104591
theorem R69755 : Reach 69755 := rs (se 1 (by rfl) ⟨52316, by rfl⟩) R104633
theorem R692387 : Reach 692387 := rs (se 1 (by rfl) ⟨519290, by rfl⟩) R1038581
theorem R69807 : Reach 69807 := rs (se 1 (by rfl) ⟨52355, by rfl⟩) R104711
theorem R266435 : Reach 266435 := rs (se 1 (by rfl) ⟨199826, by rfl⟩) R399653
theorem R102599 : Reach 102599 := rs (se 1 (by rfl) ⟨76949, by rfl⟩) R153899
theorem R69831 : Reach 69831 := rs (se 1 (by rfl) ⟨52373, by rfl⟩) R104747
theorem R69851 : Reach 69851 := rs (se 1 (by rfl) ⟨52388, by rfl⟩) R104777
theorem R69927 : Reach 69927 := rs (se 1 (by rfl) ⟨52445, by rfl⟩) R104891
theorem R69967 : Reach 69967 := rs (se 1 (by rfl) ⟨52475, by rfl⟩) R104951
theorem R69983 : Reach 69983 := rs (se 1 (by rfl) ⟨52487, by rfl⟩) R104975
theorem R102761 : Reach 102761 := rs (se 2 (by rfl) ⟨38535, by rfl⟩) R77071
theorem R70011 : Reach 70011 := rs (se 1 (by rfl) ⟨52508, by rfl⟩) R105017
theorem R70063 : Reach 70063 := rs (se 1 (by rfl) ⟨52547, by rfl⟩) R105095
theorem R102839 : Reach 102839 := rs (se 1 (by rfl) ⟨77129, by rfl⟩) R154259
theorem R70087 : Reach 70087 := rs (se 1 (by rfl) ⟨52565, by rfl⟩) R105131
theorem R102875 : Reach 102875 := rs (se 1 (by rfl) ⟨77156, by rfl⟩) R154313
theorem R70107 : Reach 70107 := rs (se 1 (by rfl) ⟨52580, by rfl⟩) R105161
theorem R70183 : Reach 70183 := rs (se 1 (by rfl) ⟨52637, by rfl⟩) R105275
theorem R70223 : Reach 70223 := rs (se 1 (by rfl) ⟨52667, by rfl⟩) R105335
theorem R70239 : Reach 70239 := rs (se 1 (by rfl) ⟨52679, by rfl⟩) R105359
theorem R1053283 : Reach 1053283 := rs (se 1 (by rfl) ⟨789962, by rfl⟩) R1579925
theorem R70267 : Reach 70267 := rs (se 1 (by rfl) ⟨52700, by rfl⟩) R105401
theorem R70319 : Reach 70319 := rs (se 1 (by rfl) ⟨52739, by rfl⟩) R105479
theorem R70343 : Reach 70343 := rs (se 1 (by rfl) ⟨52757, by rfl⟩) R105515
theorem R70363 : Reach 70363 := rs (se 1 (by rfl) ⟨52772, by rfl⟩) R105545
theorem R70439 : Reach 70439 := rs (se 1 (by rfl) ⟨52829, by rfl⟩) R105659
theorem R70479 : Reach 70479 := rs (se 1 (by rfl) ⟨52859, by rfl⟩) R105719
theorem R70495 : Reach 70495 := rs (se 1 (by rfl) ⟨52871, by rfl⟩) R105743
theorem R234359 : Reach 234359 := rs (se 1 (by rfl) ⟨175769, by rfl⟩) R351539
theorem R70523 : Reach 70523 := rs (se 1 (by rfl) ⟨52892, by rfl⟩) R105785
theorem R103343 : Reach 103343 := rs (se 1 (by rfl) ⟨77507, by rfl⟩) R155015
theorem R70575 : Reach 70575 := rs (se 1 (by rfl) ⟨52931, by rfl⟩) R105863
theorem R70599 : Reach 70599 := rs (se 1 (by rfl) ⟨52949, by rfl⟩) R105899
theorem R70619 : Reach 70619 := rs (se 1 (by rfl) ⟨52964, by rfl⟩) R105929
theorem R103433 : Reach 103433 := rs (se 2 (by rfl) ⟨38787, by rfl⟩) R77575
theorem R103463 : Reach 103463 := rs (se 1 (by rfl) ⟨77597, by rfl⟩) R155195
theorem R70695 : Reach 70695 := rs (se 1 (by rfl) ⟨53021, by rfl⟩) R106043
theorem R234575 : Reach 234575 := rs (se 1 (by rfl) ⟨175931, by rfl⟩) R351863
theorem R70735 : Reach 70735 := rs (se 1 (by rfl) ⟨53051, by rfl⟩) R106103
theorem R103547 : Reach 103547 := rs (se 1 (by rfl) ⟨77660, by rfl⟩) R155321
theorem R70779 : Reach 70779 := rs (se 1 (by rfl) ⟨53084, by rfl⟩) R106169
theorem R267421 : Reach 267421 := rs (se 3 (by rfl) ⟨50141, by rfl⟩) R100283
theorem R70855 : Reach 70855 := rs (se 1 (by rfl) ⟨53141, by rfl⟩) R106283
theorem R103673 : Reach 103673 := rs (se 2 (by rfl) ⟨38877, by rfl⟩) R77755
theorem R103775 : Reach 103775 := rs (se 1 (by rfl) ⟨77831, by rfl⟩) R155663
theorem R71007 : Reach 71007 := rs (se 1 (by rfl) ⟨53255, by rfl⟩) R106511
theorem R103787 : Reach 103787 := rs (se 1 (by rfl) ⟨77840, by rfl⟩) R155681
theorem R71087 : Reach 71087 := rs (se 1 (by rfl) ⟨53315, by rfl⟩) R106631
theorem R234953 : Reach 234953 := rs (se 2 (by rfl) ⟨88107, by rfl⟩) R176215
theorem R628235 : Reach 628235 := rs (se 1 (by rfl) ⟨471176, by rfl⟩) R942353
theorem R104015 : Reach 104015 := rs (se 1 (by rfl) ⟨78011, by rfl⟩) R156023
theorem R398945 : Reach 398945 := rs (se 2 (by rfl) ⟨149604, by rfl⟩) R299209
theorem R104135 : Reach 104135 := rs (se 1 (by rfl) ⟨78101, by rfl⟩) R156203
theorem R235223 : Reach 235223 := rs (se 1 (by rfl) ⟨176417, by rfl⟩) R352835
theorem R268105 : Reach 268105 := rs (se 2 (by rfl) ⟨100539, by rfl⟩) R201079
theorem R104297 : Reach 104297 := rs (se 2 (by rfl) ⟨39111, by rfl⟩) R78223
theorem R235439 : Reach 235439 := rs (se 1 (by rfl) ⟨176579, by rfl⟩) R353159
theorem R137143 : Reach 137143 := rs (se 1 (by rfl) ⟨102857, by rfl⟩) R205715
theorem R104375 : Reach 104375 := rs (se 1 (by rfl) ⟨78281, by rfl⟩) R156563
theorem R104411 : Reach 104411 := rs (se 1 (by rfl) ⟨78308, by rfl⟩) R156617
theorem R170383 : Reach 170383 := rs (se 1 (by rfl) ⟨127787, by rfl⟩) R255575
theorem R104879 : Reach 104879 := rs (se 1 (by rfl) ⟨78659, by rfl⟩) R157319
theorem R104969 : Reach 104969 := rs (se 2 (by rfl) ⟨39363, by rfl⟩) R78727
theorem R104999 : Reach 104999 := rs (se 1 (by rfl) ⟨78749, by rfl⟩) R157499
theorem R105083 : Reach 105083 := rs (se 1 (by rfl) ⟨78812, by rfl⟩) R157625
theorem R170707 : Reach 170707 := rs (se 1 (by rfl) ⟨128030, by rfl⟩) R256061
theorem R105209 : Reach 105209 := rs (se 2 (by rfl) ⟨39453, by rfl⟩) R78907
theorem R105311 : Reach 105311 := rs (se 1 (by rfl) ⟨78983, by rfl⟩) R157967
theorem R105323 : Reach 105323 := rs (se 1 (by rfl) ⟨78992, by rfl⟩) R157985
theorem R72667 : Reach 72667 := rs (se 1 (by rfl) ⟨54500, by rfl⟩) R109001
theorem R400403 : Reach 400403 := rs (se 1 (by rfl) ⟨300302, by rfl⟩) R600605
theorem R171065 : Reach 171065 := rs (se 2 (by rfl) ⟨64149, by rfl⟩) R128299
theorem R105551 : Reach 105551 := rs (se 1 (by rfl) ⟨79163, by rfl⟩) R158327
theorem R1055861 : Reach 1055861 := rs (se 5 (by rfl) ⟨49493, by rfl⟩) R98987
theorem R302251 : Reach 302251 := rs (se 1 (by rfl) ⟨226688, by rfl⟩) R453377
theorem R105671 : Reach 105671 := rs (se 1 (by rfl) ⟨79253, by rfl⟩) R158507
theorem R105833 : Reach 105833 := rs (se 2 (by rfl) ⟨39687, by rfl⟩) R79375
theorem R105911 : Reach 105911 := rs (se 1 (by rfl) ⟨79433, by rfl⟩) R158867
theorem R400859 : Reach 400859 := rs (se 1 (by rfl) ⟨300644, by rfl⟩) R601289
theorem R105947 : Reach 105947 := rs (se 1 (by rfl) ⟨79460, by rfl⟩) R158921
theorem R171659 : Reach 171659 := rs (se 1 (by rfl) ⟨128744, by rfl⟩) R257489
theorem R269963 : Reach 269963 := rs (se 1 (by rfl) ⟨202472, by rfl⟩) R404945
theorem R401111 : Reach 401111 := rs (se 1 (by rfl) ⟨300833, by rfl⟩) R601667
theorem R106313 : Reach 106313 := rs (se 2 (by rfl) ⟨39867, by rfl⟩) R79735
theorem R106415 : Reach 106415 := rs (se 1 (by rfl) ⟨79811, by rfl⟩) R159623
theorem R434105 : Reach 434105 := rs (se 2 (by rfl) ⟨162789, by rfl⟩) R325579
theorem R106427 : Reach 106427 := rs (se 1 (by rfl) ⟨79820, by rfl⟩) R159641
theorem R106505 : Reach 106505 := rs (se 2 (by rfl) ⟨39939, by rfl⟩) R79879
theorem R892943 : Reach 892943 := rs (se 1 (by rfl) ⟨669707, by rfl⟩) R1339415
theorem R106535 : Reach 106535 := rs (se 1 (by rfl) ⟨79901, by rfl⟩) R159803
theorem R106553 : Reach 106553 := rs (se 2 (by rfl) ⟨39957, by rfl⟩) R79915
theorem R106619 : Reach 106619 := rs (se 1 (by rfl) ⟨79964, by rfl⟩) R159929
theorem R106667 : Reach 106667 := rs (se 1 (by rfl) ⟨80000, by rfl⟩) R160001
theorem R237815 : Reach 237815 := rs (se 1 (by rfl) ⟨178361, by rfl⟩) R356723
theorem R106847 : Reach 106847 := rs (se 1 (by rfl) ⟨80135, by rfl⟩) R160271
theorem R303641 : Reach 303641 := rs (se 2 (by rfl) ⟨113865, by rfl⟩) R227731
theorem R238139 : Reach 238139 := rs (se 1 (by rfl) ⟨178604, by rfl⟩) R357209
theorem R172793 : Reach 172793 := rs (se 2 (by rfl) ⟨64797, by rfl⟩) R129595
theorem R1123085 : Reach 1123085 := rs (se 3 (by rfl) ⟨210578, by rfl⟩) R421157
theorem R238409 : Reach 238409 := rs (se 2 (by rfl) ⟨89403, by rfl⟩) R178807
theorem R172975 : Reach 172975 := rs (se 1 (by rfl) ⟨129731, by rfl⟩) R259463
theorem R861131 : Reach 861131 := rs (se 1 (by rfl) ⟨645848, by rfl⟩) R1291697
theorem R238763 : Reach 238763 := rs (se 1 (by rfl) ⟨179072, by rfl⟩) R358145
theorem R238787 : Reach 238787 := rs (se 1 (by rfl) ⟨179090, by rfl⟩) R358181
theorem R173441 : Reach 173441 := rs (se 2 (by rfl) ⟨65040, by rfl⟩) R130081
theorem R796067 : Reach 796067 := rs (se 1 (by rfl) ⟨597050, by rfl⟩) R1194101
theorem R107963 : Reach 107963 := rs (se 1 (by rfl) ⟨80972, by rfl⟩) R161945
theorem R107995 : Reach 107995 := rs (se 1 (by rfl) ⟨80996, by rfl⟩) R161993
theorem R534113 : Reach 534113 := rs (se 2 (by rfl) ⟨200292, by rfl⟩) R400585
theorem R173897 : Reach 173897 := rs (se 2 (by rfl) ⟨65211, by rfl⟩) R130423
theorem R1189727 : Reach 1189727 := rs (se 1 (by rfl) ⟨892295, by rfl⟩) R1784591
theorem R1058669 : Reach 1058669 := rs (se 3 (by rfl) ⟨198500, by rfl⟩) R397001
theorem R403319 : Reach 403319 := rs (se 1 (by rfl) ⟨302489, by rfl⟩) R604979
theorem R436103 : Reach 436103 := rs (se 1 (by rfl) ⟨327077, by rfl⟩) R654155
theorem R239543 : Reach 239543 := rs (se 1 (by rfl) ⟨179657, by rfl⟩) R359315
theorem R75739 : Reach 75739 := rs (se 1 (by rfl) ⟨56804, by rfl⟩) R113609
theorem R174251 : Reach 174251 := rs (se 1 (by rfl) ⟨130688, by rfl⟩) R261377
theorem R76207 : Reach 76207 := rs (se 1 (by rfl) ⟨57155, by rfl⟩) R114311
theorem R404027 : Reach 404027 := rs (se 1 (by rfl) ⟨303020, by rfl⟩) R606041
theorem R76639 : Reach 76639 := rs (se 1 (by rfl) ⟨57479, by rfl⟩) R114959
theorem R1551251 : Reach 1551251 := rs (se 1 (by rfl) ⟨1163438, by rfl⟩) R2326877
theorem R175031 : Reach 175031 := rs (se 1 (by rfl) ⟨131273, by rfl⟩) R262547
theorem R535571 : Reach 535571 := rs (se 1 (by rfl) ⟨401678, by rfl⟩) R803357
theorem R76999 : Reach 76999 := rs (se 1 (by rfl) ⟨57749, by rfl⟩) R115499
theorem R176033 : Reach 176033 := rs (se 2 (by rfl) ⟨66012, by rfl⟩) R132025
theorem R1093637 : Reach 1093637 := rs (se 4 (by rfl) ⟨102528, by rfl⟩) R205057
theorem R77863 : Reach 77863 := rs (se 1 (by rfl) ⟨58397, by rfl⟩) R116795
theorem R208975 : Reach 208975 := rs (se 1 (by rfl) ⟨156731, by rfl⟩) R313463
theorem R667763 : Reach 667763 := rs (se 1 (by rfl) ⟨500822, by rfl⟩) R1001645
theorem R405847 : Reach 405847 := rs (se 1 (by rfl) ⟨304385, by rfl⟩) R608771
theorem R176489 : Reach 176489 := rs (se 2 (by rfl) ⟨66183, by rfl⟩) R132367
theorem R505025 : Reach 505025 := rs (se 2 (by rfl) ⟨189384, by rfl⟩) R378769
theorem R603407 : Reach 603407 := rs (se 1 (by rfl) ⟨452555, by rfl⟩) R905111
theorem R177673 : Reach 177673 := rs (se 2 (by rfl) ⟨66627, by rfl⟩) R133255
theorem R243233 : Reach 243233 := rs (se 2 (by rfl) ⟨91212, by rfl⟩) R182425
theorem R276007 : Reach 276007 := rs (se 1 (by rfl) ⟨207005, by rfl⟩) R414011
theorem R79483 : Reach 79483 := rs (se 1 (by rfl) ⟨59612, by rfl⟩) R119225
theorem R538487 : Reach 538487 := rs (se 1 (by rfl) ⟨403865, by rfl⟩) R807731
theorem R79951 : Reach 79951 := rs (se 1 (by rfl) ⟨59963, by rfl⟩) R119927
theorem R4143581 : Reach 4143581 := rs (se 3 (by rfl) ⟨776921, by rfl⟩) R1553843
theorem R211481 : Reach 211481 := rs (se 2 (by rfl) ⟨79305, by rfl⟩) R158611
theorem R604705 : Reach 604705 := rs (se 2 (by rfl) ⟨226764, by rfl⟩) R453529
theorem R277127 : Reach 277127 := rs (se 1 (by rfl) ⟨207845, by rfl⟩) R415691
theorem R146119 : Reach 146119 := rs (se 1 (by rfl) ⟨109589, by rfl⟩) R219179
theorem R342737 : Reach 342737 := rs (se 2 (by rfl) ⟨128526, by rfl⟩) R257053
theorem R179131 : Reach 179131 := rs (se 1 (by rfl) ⟨134348, by rfl⟩) R268697
theorem R1719575 : Reach 1719575 := rs (se 1 (by rfl) ⟨1289681, by rfl⟩) R2579363
theorem R343439 : Reach 343439 := rs (se 1 (by rfl) ⟨257579, by rfl⟩) R515159
theorem R114095 : Reach 114095 := rs (se 1 (by rfl) ⟨85571, by rfl⟩) R171143
theorem R441895 : Reach 441895 := rs (se 1 (by rfl) ⟨331421, by rfl⟩) R662843
theorem R114425 : Reach 114425 := rs (se 2 (by rfl) ⟨42909, by rfl⟩) R85819
theorem R114527 : Reach 114527 := rs (se 1 (by rfl) ⟨85895, by rfl⟩) R171791
theorem R344407 : Reach 344407 := rs (se 1 (by rfl) ⟨258305, by rfl⟩) R516611
theorem R115087 : Reach 115087 := rs (se 1 (by rfl) ⟨86315, by rfl⟩) R172631
theorem R443243 : Reach 443243 := rs (se 1 (by rfl) ⟨332432, by rfl⟩) R664865
theorem R115769 : Reach 115769 := rs (se 2 (by rfl) ⟨43413, by rfl⟩) R86827
theorem R345545 : Reach 345545 := rs (se 2 (by rfl) ⟨129579, by rfl⟩) R259159
theorem R181723 : Reach 181723 := rs (se 1 (by rfl) ⟨136292, by rfl⟩) R272585
theorem R214667 : Reach 214667 := rs (se 1 (by rfl) ⟨161000, by rfl⟩) R322001
theorem R280253 : Reach 280253 := rs (se 3 (by rfl) ⟨52547, by rfl⟩) R105095
theorem R116471 : Reach 116471 := rs (se 1 (by rfl) ⟨87353, by rfl⟩) R174707
theorem R444203 : Reach 444203 := rs (se 1 (by rfl) ⟨333152, by rfl⟩) R666305
theorem R116815 : Reach 116815 := rs (se 1 (by rfl) ⟨87611, by rfl⟩) R175223
theorem R346193 : Reach 346193 := rs (se 2 (by rfl) ⟨129822, by rfl⟩) R259645
theorem R247961 : Reach 247961 := rs (se 2 (by rfl) ⟨92985, by rfl⟩) R185971
theorem R903473 : Reach 903473 := rs (se 2 (by rfl) ⟨338802, by rfl⟩) R677605
theorem R117065 : Reach 117065 := rs (se 2 (by rfl) ⟨43899, by rfl⟩) R87799
theorem R281033 : Reach 281033 := rs (se 2 (by rfl) ⟨105387, by rfl⟩) R210775
theorem R281227 : Reach 281227 := rs (se 1 (by rfl) ⟨210920, by rfl⟩) R421841
theorem R117497 : Reach 117497 := rs (se 2 (by rfl) ⟨44061, by rfl⟩) R88123
theorem R117679 : Reach 117679 := rs (se 1 (by rfl) ⟨88259, by rfl⟩) R176519
theorem R117767 : Reach 117767 := rs (se 1 (by rfl) ⟨88325, by rfl⟩) R176651
theorem R118111 : Reach 118111 := rs (se 1 (by rfl) ⟨88583, by rfl⟩) R177167
theorem R970157 : Reach 970157 := rs (se 3 (by rfl) ⟨181904, by rfl⟩) R363809
theorem R118199 : Reach 118199 := rs (se 1 (by rfl) ⟨88649, by rfl⟩) R177299
theorem R151163 : Reach 151163 := rs (se 1 (by rfl) ⟨113372, by rfl⟩) R226745
theorem R85627 : Reach 85627 := rs (se 1 (by rfl) ⟨64220, by rfl⟩) R128441
theorem R151289 : Reach 151289 := rs (se 2 (by rfl) ⟨56733, by rfl⟩) R113467
theorem R85855 : Reach 85855 := rs (se 1 (by rfl) ⟨64391, by rfl⟩) R128783
theorem R413549 : Reach 413549 := rs (se 3 (by rfl) ⟨77540, by rfl⟩) R155081
theorem R151559 : Reach 151559 := rs (se 1 (by rfl) ⟨113669, by rfl⟩) R227339
theorem R118793 : Reach 118793 := rs (se 2 (by rfl) ⟨44547, by rfl⟩) R89095
theorem R151631 : Reach 151631 := rs (se 1 (by rfl) ⟨113723, by rfl⟩) R227447
theorem R118955 : Reach 118955 := rs (se 1 (by rfl) ⟨89216, by rfl⟩) R178433
theorem R151723 : Reach 151723 := rs (se 1 (by rfl) ⟨113792, by rfl⟩) R227585
theorem R86447 : Reach 86447 := rs (se 1 (by rfl) ⟨64835, by rfl⟩) R129671
theorem R152027 : Reach 152027 := rs (se 1 (by rfl) ⟨114020, by rfl⟩) R228041
theorem R119353 : Reach 119353 := rs (se 2 (by rfl) ⟨44757, by rfl⟩) R89515
theorem R119495 : Reach 119495 := rs (se 1 (by rfl) ⟨89621, by rfl⟩) R179243
theorem R119657 : Reach 119657 := rs (se 2 (by rfl) ⟨44871, by rfl⟩) R89743
theorem R152495 : Reach 152495 := rs (se 1 (by rfl) ⟨114371, by rfl⟩) R228743
theorem R152747 : Reach 152747 := rs (se 1 (by rfl) ⟨114560, by rfl⟩) R229121
theorem R251075 : Reach 251075 := rs (se 1 (by rfl) ⟨188306, by rfl⟩) R376613
theorem R447767 : Reach 447767 := rs (se 1 (by rfl) ⟨335825, by rfl⟩) R671651
theorem R873929 : Reach 873929 := rs (se 2 (by rfl) ⟨327723, by rfl⟩) R655447
theorem R284147 : Reach 284147 := rs (se 1 (by rfl) ⟨213110, by rfl⟩) R426221
theorem R153287 : Reach 153287 := rs (se 1 (by rfl) ⟨114965, by rfl⟩) R229931
theorem R448199 : Reach 448199 := rs (se 1 (by rfl) ⟨336149, by rfl⟩) R672299
theorem R382907 : Reach 382907 := rs (se 1 (by rfl) ⟨287180, by rfl⟩) R574361
theorem R350365 : Reach 350365 := rs (se 3 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R350729 : Reach 350729 := rs (se 2 (by rfl) ⟨131523, by rfl⟩) R263047
theorem R154151 : Reach 154151 := rs (se 1 (by rfl) ⟨115613, by rfl⟩) R231227
theorem R449225 : Reach 449225 := rs (se 2 (by rfl) ⟨168459, by rfl⟩) R336919
theorem R154475 : Reach 154475 := rs (se 1 (by rfl) ⟨115856, by rfl⟩) R231713
theorem R154529 : Reach 154529 := rs (se 2 (by rfl) ⟨57948, by rfl⟩) R115897
theorem R253085 : Reach 253085 := rs (se 3 (by rfl) ⟨47453, by rfl⟩) R94907
theorem R154871 : Reach 154871 := rs (se 1 (by rfl) ⟨116153, by rfl⟩) R232307
theorem R515645 : Reach 515645 := rs (se 3 (by rfl) ⟨96683, by rfl⟩) R193367
theorem R220769 : Reach 220769 := rs (se 2 (by rfl) ⟨82788, by rfl⟩) R165577
theorem R1302155 : Reach 1302155 := rs (se 1 (by rfl) ⟨976616, by rfl⟩) R1953233
theorem R220819 : Reach 220819 := rs (se 1 (by rfl) ⟨165614, by rfl⟩) R331229
theorem R122539 : Reach 122539 := rs (se 1 (by rfl) ⟨91904, by rfl⟩) R183809
theorem R89849 : Reach 89849 := rs (se 2 (by rfl) ⟨33693, by rfl⟩) R67387
theorem R155465 : Reach 155465 := rs (se 2 (by rfl) ⟨58299, by rfl⟩) R116599
theorem R352187 : Reach 352187 := rs (se 1 (by rfl) ⟨264140, by rfl⟩) R528281
theorem R548801 : Reach 548801 := rs (se 2 (by rfl) ⟨205800, by rfl⟩) R411601
theorem R778571 : Reach 778571 := rs (se 1 (by rfl) ⟨583928, by rfl⟩) R1167857
theorem R516617 : Reach 516617 := rs (se 2 (by rfl) ⟨193731, by rfl⟩) R387463
theorem R156257 : Reach 156257 := rs (se 2 (by rfl) ⟨58596, by rfl⟩) R117193
theorem R877229 : Reach 877229 := rs (se 3 (by rfl) ⟨164480, by rfl⟩) R328961
theorem R156599 : Reach 156599 := rs (se 1 (by rfl) ⟨117449, by rfl⟩) R234899
theorem R254983 : Reach 254983 := rs (se 1 (by rfl) ⟨191237, by rfl⟩) R382475
theorem R353483 : Reach 353483 := rs (se 1 (by rfl) ⟨265112, by rfl⟩) R530225
theorem R1729781 : Reach 1729781 := rs (se 5 (by rfl) ⟨81083, by rfl⟩) R162167
theorem R222551 : Reach 222551 := rs (se 1 (by rfl) ⟨166913, by rfl⟩) R333827
theorem R976373 : Reach 976373 := rs (se 5 (by rfl) ⟨45767, by rfl⟩) R91535
theorem R157193 : Reach 157193 := rs (se 2 (by rfl) ⟨58947, by rfl⟩) R117895
theorem R124615 : Reach 124615 := rs (se 1 (by rfl) ⟨93461, by rfl⟩) R186923
theorem R812843 : Reach 812843 := rs (se 1 (by rfl) ⟨609632, by rfl⟩) R1219265
theorem R157535 : Reach 157535 := rs (se 1 (by rfl) ⟨118151, by rfl⟩) R236303
theorem R518075 : Reach 518075 := rs (se 1 (by rfl) ⟨388556, by rfl⟩) R777113
theorem R157715 : Reach 157715 := rs (se 1 (by rfl) ⟨118286, by rfl⟩) R236573
theorem R452915 : Reach 452915 := rs (se 1 (by rfl) ⟨339686, by rfl⟩) R679373
theorem R747863 : Reach 747863 := rs (se 1 (by rfl) ⟨560897, by rfl⟩) R1121795
theorem R289129 : Reach 289129 := rs (se 2 (by rfl) ⟨108423, by rfl⟩) R216847
theorem R158057 : Reach 158057 := rs (se 2 (by rfl) ⟨59271, by rfl⟩) R118543
theorem R1207223 : Reach 1207223 := rs (se 1 (by rfl) ⟨905417, by rfl⟩) R1810835
theorem R158651 : Reach 158651 := rs (se 1 (by rfl) ⟨118988, by rfl⟩) R237977
theorem R1109015 : Reach 1109015 := rs (se 1 (by rfl) ⟨831761, by rfl⟩) R1663523
theorem R158777 : Reach 158777 := rs (se 2 (by rfl) ⟨59541, by rfl⟩) R119083
theorem R191659 : Reach 191659 := rs (se 1 (by rfl) ⟨143744, by rfl⟩) R287489
theorem R159119 : Reach 159119 := rs (se 1 (by rfl) ⟨119339, by rfl⟩) R238679
theorem R159371 : Reach 159371 := rs (se 1 (by rfl) ⟨119528, by rfl⟩) R239057
theorem R159443 : Reach 159443 := rs (se 1 (by rfl) ⟨119582, by rfl⟩) R239165
theorem R487133 : Reach 487133 := rs (se 3 (by rfl) ⟨91337, by rfl⟩) R182675
theorem R257975 : Reach 257975 := rs (se 1 (by rfl) ⟨193481, by rfl⟩) R386963
theorem R455017 : Reach 455017 := rs (se 2 (by rfl) ⟨170631, by rfl⟩) R341263
theorem R127507 : Reach 127507 := rs (se 1 (by rfl) ⟨95630, by rfl⟩) R191261
theorem R193049 : Reach 193049 := rs (se 2 (by rfl) ⟨72393, by rfl⟩) R144787
theorem R324155 : Reach 324155 := rs (se 1 (by rfl) ⟨243116, by rfl⟩) R486233
theorem R291539 : Reach 291539 := rs (se 1 (by rfl) ⟨218654, by rfl⟩) R437309
theorem R291691 : Reach 291691 := rs (se 1 (by rfl) ⟨218768, by rfl⟩) R437537
theorem R258977 : Reach 258977 := rs (se 2 (by rfl) ⟨97116, by rfl⟩) R194233
theorem R259433 : Reach 259433 := rs (se 2 (by rfl) ⟨97287, by rfl⟩) R194575
theorem R1963379 : Reach 1963379 := rs (se 1 (by rfl) ⟨1472534, by rfl⟩) R2945069
theorem R587209 : Reach 587209 := rs (se 2 (by rfl) ⟨220203, by rfl⟩) R440407
theorem R325309 : Reach 325309 := rs (se 3 (by rfl) ⟨60995, by rfl⟩) R121991
theorem R227015 : Reach 227015 := rs (se 1 (by rfl) ⟨170261, by rfl⟩) R340523
theorem R390905 : Reach 390905 := rs (se 2 (by rfl) ⟨146589, by rfl⟩) R293179
theorem R358187 : Reach 358187 := rs (se 1 (by rfl) ⟨268640, by rfl⟩) R537281
theorem R259949 : Reach 259949 := rs (se 3 (by rfl) ⟨48740, by rfl⟩) R97481
theorem R227407 : Reach 227407 := rs (se 1 (by rfl) ⟨170555, by rfl⟩) R341111
theorem R358667 : Reach 358667 := rs (se 1 (by rfl) ⟨269000, by rfl⟩) R538001
theorem R391553 : Reach 391553 := rs (se 2 (by rfl) ⟨146832, by rfl⟩) R293665
theorem R1112453 : Reach 1112453 := rs (se 4 (by rfl) ⟨104292, by rfl⟩) R208585
theorem R260617 : Reach 260617 := rs (se 2 (by rfl) ⟨97731, by rfl⟩) R195463
theorem R2423317 : Reach 2423317 := rs (se 6 (by rfl) ⟨56796, by rfl⟩) R113593
theorem R227879 : Reach 227879 := rs (se 1 (by rfl) ⟨170909, by rfl⟩) R341819
theorem R227987 : Reach 227987 := rs (se 1 (by rfl) ⟨170990, by rfl⟩) R341981
theorem R228203 : Reach 228203 := rs (se 1 (by rfl) ⟨171152, by rfl⟩) R342305
theorem R129899 : Reach 129899 := rs (se 1 (by rfl) ⟨97424, by rfl⟩) R194849
theorem R228257 : Reach 228257 := rs (se 2 (by rfl) ⟨85596, by rfl⟩) R171193
theorem R392111 : Reach 392111 := rs (se 1 (by rfl) ⟨294083, by rfl⟩) R588167
theorem R392363 : Reach 392363 := rs (se 1 (by rfl) ⟨294272, by rfl⟩) R588545
theorem R195965 : Reach 195965 := rs (se 3 (by rfl) ⟨36743, by rfl⟩) R73487
theorem R228851 : Reach 228851 := rs (se 1 (by rfl) ⟨171638, by rfl⟩) R343277
theorem R130567 : Reach 130567 := rs (se 1 (by rfl) ⟨97925, by rfl⟩) R195851
theorem R556583 : Reach 556583 := rs (se 1 (by rfl) ⟨417437, by rfl⟩) R834875
theorem R196307 : Reach 196307 := rs (se 1 (by rfl) ⟨147230, by rfl⟩) R294461
theorem R163577 : Reach 163577 := rs (se 2 (by rfl) ⟨61341, by rfl⟩) R122683
theorem R262075 : Reach 262075 := rs (se 1 (by rfl) ⟨196556, by rfl⟩) R393113
theorem R589943 : Reach 589943 := rs (se 1 (by rfl) ⟨442457, by rfl⟩) R884915
theorem R459209 : Reach 459209 := rs (se 2 (by rfl) ⟨172203, by rfl⟩) R344407
theorem R131539 : Reach 131539 := rs (se 1 (by rfl) ⟨98654, by rfl⟩) R197309
theorem R295495 : Reach 295495 := rs (se 1 (by rfl) ⟨221621, by rfl⟩) R443243
theorem R230363 : Reach 230363 := rs (se 1 (by rfl) ⟨172772, by rfl⟩) R345545
theorem R230525 : Reach 230525 := rs (se 3 (by rfl) ⟨43223, by rfl⟩) R86447
theorem R296135 : Reach 296135 := rs (se 1 (by rfl) ⟨222101, by rfl⟩) R444203
theorem R230633 : Reach 230633 := rs (se 2 (by rfl) ⟨86487, by rfl⟩) R172975
theorem R132329 : Reach 132329 := rs (se 2 (by rfl) ⟨49623, by rfl⟩) R99247
theorem R263519 : Reach 263519 := rs (se 1 (by rfl) ⟨197639, by rfl⟩) R395279
theorem R263533 : Reach 263533 := rs (se 3 (by rfl) ⟨49412, by rfl⟩) R98825
theorem R230795 : Reach 230795 := rs (se 1 (by rfl) ⟨173096, by rfl⟩) R346193
theorem R165307 : Reach 165307 := rs (se 1 (by rfl) ⟨123980, by rfl⟩) R247961
theorem R67135 : Reach 67135 := rs (se 1 (by rfl) ⟨50351, by rfl⟩) R100703
theorem R67143 : Reach 67143 := rs (se 1 (by rfl) ⟨50357, by rfl⟩) R100715
theorem R263837 : Reach 263837 := rs (se 3 (by rfl) ⟨49469, by rfl⟩) R98939
theorem R132769 : Reach 132769 := rs (se 2 (by rfl) ⟨49788, by rfl⟩) R99577
theorem R67295 : Reach 67295 := rs (se 1 (by rfl) ⟨50471, by rfl⟩) R100943
theorem R67375 : Reach 67375 := rs (se 1 (by rfl) ⟨50531, by rfl⟩) R101063
theorem R722819 : Reach 722819 := rs (se 1 (by rfl) ⟨542114, by rfl⟩) R1084229
theorem R1705859 : Reach 1705859 := rs (se 1 (by rfl) ⟨1279394, by rfl⟩) R2558789
theorem R67483 : Reach 67483 := rs (se 1 (by rfl) ⟨50612, by rfl⟩) R101225
theorem R67535 : Reach 67535 := rs (se 1 (by rfl) ⟨50651, by rfl⟩) R101303
theorem R198607 : Reach 198607 := rs (se 1 (by rfl) ⟨148955, by rfl⟩) R297911
theorem R67559 : Reach 67559 := rs (se 1 (by rfl) ⟨50669, by rfl⟩) R101339
theorem R166153 : Reach 166153 := rs (se 2 (by rfl) ⟨62307, by rfl⟩) R124615
theorem R67871 : Reach 67871 := rs (se 1 (by rfl) ⟨50903, by rfl⟩) R101807
theorem R67931 : Reach 67931 := rs (se 1 (by rfl) ⟨50948, by rfl⟩) R101897
theorem R67951 : Reach 67951 := rs (se 1 (by rfl) ⟨50963, by rfl⟩) R101927
theorem R100775 : Reach 100775 := rs (se 1 (by rfl) ⟨75581, by rfl⟩) R151163
theorem R68007 : Reach 68007 := rs (se 1 (by rfl) ⟨51005, by rfl⟩) R102011
theorem R100859 : Reach 100859 := rs (se 1 (by rfl) ⟨75644, by rfl⟩) R151289
theorem R68091 : Reach 68091 := rs (se 1 (by rfl) ⟨51068, by rfl⟩) R102137
theorem R68159 : Reach 68159 := rs (se 1 (by rfl) ⟨51119, by rfl⟩) R102239
theorem R68167 : Reach 68167 := rs (se 1 (by rfl) ⟨51125, by rfl⟩) R102251
theorem R100985 : Reach 100985 := rs (se 2 (by rfl) ⟨37869, by rfl⟩) R75739
theorem R101039 : Reach 101039 := rs (se 1 (by rfl) ⟨75779, by rfl⟩) R151559
theorem R101087 : Reach 101087 := rs (se 1 (by rfl) ⟨75815, by rfl⟩) R151631
theorem R68319 : Reach 68319 := rs (se 1 (by rfl) ⟨51239, by rfl⟩) R102479
theorem R461591 : Reach 461591 := rs (se 1 (by rfl) ⟨346193, by rfl⟩) R692387
theorem R68399 : Reach 68399 := rs (se 1 (by rfl) ⟨51299, by rfl⟩) R102599
theorem R68507 : Reach 68507 := rs (se 1 (by rfl) ⟨51380, by rfl⟩) R102761
theorem R68559 : Reach 68559 := rs (se 1 (by rfl) ⟨51419, by rfl⟩) R102839
theorem R101351 : Reach 101351 := rs (se 1 (by rfl) ⟨76013, by rfl⟩) R152027
theorem R68583 : Reach 68583 := rs (se 1 (by rfl) ⟨51437, by rfl⟩) R102875
theorem R101609 : Reach 101609 := rs (se 2 (by rfl) ⟨38103, by rfl⟩) R76207
theorem R101663 : Reach 101663 := rs (se 1 (by rfl) ⟨76247, by rfl⟩) R152495
theorem R68895 : Reach 68895 := rs (se 1 (by rfl) ⟨51671, by rfl⟩) R103343
theorem R68955 : Reach 68955 := rs (se 1 (by rfl) ⟨51716, by rfl⟩) R103433
theorem R68975 : Reach 68975 := rs (se 1 (by rfl) ⟨51731, by rfl⟩) R103463
theorem R1609085 : Reach 1609085 := rs (se 3 (by rfl) ⟨301703, by rfl⟩) R603407
theorem R69031 : Reach 69031 := rs (se 1 (by rfl) ⟨51773, by rfl⟩) R103547
theorem R101831 : Reach 101831 := rs (se 1 (by rfl) ⟨76373, by rfl⟩) R152747
theorem R167383 : Reach 167383 := rs (se 1 (by rfl) ⟨125537, by rfl⟩) R251075
theorem R69115 : Reach 69115 := rs (se 1 (by rfl) ⟨51836, by rfl⟩) R103673
theorem R298511 : Reach 298511 := rs (se 1 (by rfl) ⟨223883, by rfl⟩) R447767
theorem R69183 : Reach 69183 := rs (se 1 (by rfl) ⟨51887, by rfl⟩) R103775
theorem R69191 : Reach 69191 := rs (se 1 (by rfl) ⟨51893, by rfl⟩) R103787
theorem R69343 : Reach 69343 := rs (se 1 (by rfl) ⟨52007, by rfl⟩) R104015
theorem R265963 : Reach 265963 := rs (se 1 (by rfl) ⟨199472, by rfl⟩) R398945
theorem R102185 : Reach 102185 := rs (se 2 (by rfl) ⟨38319, by rfl⟩) R76639
theorem R102191 : Reach 102191 := rs (se 1 (by rfl) ⟨76643, by rfl⟩) R153287
theorem R69423 : Reach 69423 := rs (se 1 (by rfl) ⟨52067, by rfl⟩) R104135
theorem R298799 : Reach 298799 := rs (se 1 (by rfl) ⟨224099, by rfl⟩) R448199
theorem R2330477 : Reach 2330477 := rs (se 3 (by rfl) ⟨436964, by rfl⟩) R873929
theorem R69531 : Reach 69531 := rs (se 1 (by rfl) ⟨52148, by rfl⟩) R104297
theorem R69583 : Reach 69583 := rs (se 1 (by rfl) ⟨52187, by rfl⟩) R104375
theorem R69607 : Reach 69607 := rs (se 1 (by rfl) ⟨52205, by rfl⟩) R104411
theorem R266449 : Reach 266449 := rs (se 2 (by rfl) ⟨99918, by rfl⟩) R199837
theorem R102665 : Reach 102665 := rs (se 2 (by rfl) ⟨38499, by rfl⟩) R76999
theorem R69919 : Reach 69919 := rs (se 1 (by rfl) ⟨52439, by rfl⟩) R104879
theorem R233819 : Reach 233819 := rs (se 1 (by rfl) ⟨175364, by rfl⟩) R350729
theorem R69979 : Reach 69979 := rs (se 1 (by rfl) ⟨52484, by rfl⟩) R104969
theorem R102767 : Reach 102767 := rs (se 1 (by rfl) ⟨77075, by rfl⟩) R154151
theorem R69999 : Reach 69999 := rs (se 1 (by rfl) ⟨52499, by rfl⟩) R104999
theorem R70055 : Reach 70055 := rs (se 1 (by rfl) ⟨52541, by rfl⟩) R105083
theorem R299483 : Reach 299483 := rs (se 1 (by rfl) ⟨224612, by rfl⟩) R449225
theorem R70139 : Reach 70139 := rs (se 1 (by rfl) ⟨52604, by rfl⟩) R105209
theorem R266753 : Reach 266753 := rs (se 2 (by rfl) ⟨100032, by rfl⟩) R200065
theorem R70207 : Reach 70207 := rs (se 1 (by rfl) ⟨52655, by rfl⟩) R105311
theorem R102983 : Reach 102983 := rs (se 1 (by rfl) ⟨77237, by rfl⟩) R154475
theorem R70215 : Reach 70215 := rs (se 1 (by rfl) ⟨52661, by rfl⟩) R105323
theorem R103019 : Reach 103019 := rs (se 1 (by rfl) ⟨77264, by rfl⟩) R154529
theorem R266935 : Reach 266935 := rs (se 1 (by rfl) ⟨200201, by rfl⟩) R400403
theorem R70367 : Reach 70367 := rs (se 1 (by rfl) ⟨52775, by rfl⟩) R105551
theorem R955165 : Reach 955165 := rs (se 3 (by rfl) ⟨179093, by rfl⟩) R358187
theorem R70447 : Reach 70447 := rs (se 1 (by rfl) ⟨52835, by rfl⟩) R105671
theorem R103247 : Reach 103247 := rs (se 1 (by rfl) ⟨77435, by rfl⟩) R154871
theorem R70555 : Reach 70555 := rs (se 1 (by rfl) ⟨52916, by rfl⟩) R105833
theorem R267209 : Reach 267209 := rs (se 2 (by rfl) ⟨100203, by rfl⟩) R200407
theorem R70607 : Reach 70607 := rs (se 1 (by rfl) ⟨52955, by rfl⟩) R105911
theorem R267239 : Reach 267239 := rs (se 1 (by rfl) ⟨200429, by rfl⟩) R400859
theorem R70631 : Reach 70631 := rs (se 1 (by rfl) ⟨52973, by rfl⟩) R105947
theorem R267407 : Reach 267407 := rs (se 1 (by rfl) ⟨200555, by rfl⟩) R401111
theorem R103643 : Reach 103643 := rs (se 1 (by rfl) ⟨77732, by rfl⟩) R155465
theorem R70875 : Reach 70875 := rs (se 1 (by rfl) ⟨53156, by rfl⟩) R106313
theorem R70943 : Reach 70943 := rs (se 1 (by rfl) ⟨53207, by rfl⟩) R106415
theorem R234791 : Reach 234791 := rs (se 1 (by rfl) ⟨176093, by rfl⟩) R352187
theorem R70951 : Reach 70951 := rs (se 1 (by rfl) ⟨53213, by rfl⟩) R106427
theorem R365867 : Reach 365867 := rs (se 1 (by rfl) ⟨274400, by rfl⟩) R548801
theorem R71003 : Reach 71003 := rs (se 1 (by rfl) ⟨53252, by rfl⟩) R106505
theorem R595295 : Reach 595295 := rs (se 1 (by rfl) ⟨446471, by rfl⟩) R892943
theorem R71023 : Reach 71023 := rs (se 1 (by rfl) ⟨53267, by rfl⟩) R106535
theorem R71035 : Reach 71035 := rs (se 1 (by rfl) ⟨53276, by rfl⟩) R106553
theorem R103817 : Reach 103817 := rs (se 2 (by rfl) ⟨38931, by rfl⟩) R77863
theorem R71079 : Reach 71079 := rs (se 1 (by rfl) ⟨53309, by rfl⟩) R106619
theorem R71111 : Reach 71111 := rs (se 1 (by rfl) ⟨53333, by rfl⟩) R106667
theorem R71231 : Reach 71231 := rs (se 1 (by rfl) ⟨53423, by rfl⟩) R106847
theorem R202427 : Reach 202427 := rs (se 1 (by rfl) ⟨151820, by rfl⟩) R303641
theorem R104171 : Reach 104171 := rs (se 1 (by rfl) ⟨78128, by rfl⟩) R156257
theorem R5936885 : Reach 5936885 := rs (se 5 (by rfl) ⟨278291, by rfl⟩) R556583
theorem R104399 : Reach 104399 := rs (se 1 (by rfl) ⟨78299, by rfl⟩) R156599
theorem R170009 : Reach 170009 := rs (se 2 (by rfl) ⟨63753, by rfl⟩) R127507
theorem R235655 : Reach 235655 := rs (se 1 (by rfl) ⟨176741, by rfl⟩) R353483
theorem R1153187 : Reach 1153187 := rs (se 1 (by rfl) ⟨864890, by rfl⟩) R1729781
theorem R530711 : Reach 530711 := rs (se 1 (by rfl) ⟨398033, by rfl⟩) R796067
theorem R71975 : Reach 71975 := rs (se 1 (by rfl) ⟨53981, by rfl⟩) R107963
theorem R104795 : Reach 104795 := rs (se 1 (by rfl) ⟨78596, by rfl⟩) R157193
theorem R793151 : Reach 793151 := rs (se 1 (by rfl) ⟨594863, by rfl⟩) R1189727
theorem R105023 : Reach 105023 := rs (se 1 (by rfl) ⟨78767, by rfl⟩) R157535
theorem R268879 : Reach 268879 := rs (se 1 (by rfl) ⟨201659, by rfl⟩) R403319
theorem R105143 : Reach 105143 := rs (se 1 (by rfl) ⟨78857, by rfl⟩) R157715
theorem R301943 : Reach 301943 := rs (se 1 (by rfl) ⟨226457, by rfl⟩) R452915
theorem R498575 : Reach 498575 := rs (se 1 (by rfl) ⟨373931, by rfl⟩) R747863
theorem R105371 : Reach 105371 := rs (se 1 (by rfl) ⟨79028, by rfl⟩) R158057
theorem R269351 : Reach 269351 := rs (se 1 (by rfl) ⟨202013, by rfl⟩) R404027
theorem R105767 : Reach 105767 := rs (se 1 (by rfl) ⟨79325, by rfl⟩) R158651
theorem R236897 : Reach 236897 := rs (se 2 (by rfl) ⟨88836, by rfl⟩) R177673
theorem R105851 : Reach 105851 := rs (se 1 (by rfl) ⟨79388, by rfl⟩) R158777
theorem R368009 : Reach 368009 := rs (se 2 (by rfl) ⟨138003, by rfl⟩) R276007
theorem R105977 : Reach 105977 := rs (se 2 (by rfl) ⟨39741, by rfl⟩) R79483
theorem R433745 : Reach 433745 := rs (se 2 (by rfl) ⟨162654, by rfl⟩) R325309
theorem R106079 : Reach 106079 := rs (se 1 (by rfl) ⟨79559, by rfl⟩) R159119
theorem R106247 : Reach 106247 := rs (se 1 (by rfl) ⟨79685, by rfl⟩) R159371
theorem R106295 : Reach 106295 := rs (se 1 (by rfl) ⟨79721, by rfl⟩) R159443
theorem R171983 : Reach 171983 := rs (se 1 (by rfl) ⟨128987, by rfl⟩) R257975
theorem R729091 : Reach 729091 := rs (se 1 (by rfl) ⟨546818, by rfl⟩) R1093637
theorem R303209 : Reach 303209 := rs (se 2 (by rfl) ⟨113703, by rfl⟩) R227407
theorem R106601 : Reach 106601 := rs (se 2 (by rfl) ⟨39975, by rfl⟩) R79951
theorem R467153 : Reach 467153 := rs (se 2 (by rfl) ⟨175182, by rfl⟩) R350365
theorem R172651 : Reach 172651 := rs (se 1 (by rfl) ⟨129488, by rfl⟩) R258977
theorem R336683 : Reach 336683 := rs (se 1 (by rfl) ⟨252512, by rfl⟩) R505025
theorem R172955 : Reach 172955 := rs (se 1 (by rfl) ⟨129716, by rfl⟩) R259433
theorem R173299 : Reach 173299 := rs (se 1 (by rfl) ⟨129974, by rfl⟩) R259949
theorem R238841 : Reach 238841 := rs (se 2 (by rfl) ⟨89565, by rfl⟩) R179131
theorem R239111 : Reach 239111 := rs (se 1 (by rfl) ⟨179333, by rfl⟩) R358667
theorem R403001 : Reach 403001 := rs (se 2 (by rfl) ⟨151125, by rfl⟩) R302251
theorem R2762387 : Reach 2762387 := rs (se 1 (by rfl) ⟨2071790, by rfl⟩) R4143581
theorem R140987 : Reach 140987 := rs (se 1 (by rfl) ⟨105740, by rfl⟩) R211481
theorem R436205 : Reach 436205 := rs (se 3 (by rfl) ⟨81788, by rfl⟩) R163577
theorem R239597 : Reach 239597 := rs (se 3 (by rfl) ⟨44924, by rfl⟩) R89849
theorem R174089 : Reach 174089 := rs (se 2 (by rfl) ⟨65283, by rfl⟩) R130567
theorem R76063 : Reach 76063 := rs (se 1 (by rfl) ⟨57047, by rfl⟩) R114095
theorem R731429 : Reach 731429 := rs (se 4 (by rfl) ⟨68571, by rfl⟩) R137143
theorem R76283 : Reach 76283 := rs (se 1 (by rfl) ⟨57212, by rfl⟩) R114425
theorem R76351 : Reach 76351 := rs (se 1 (by rfl) ⟨57263, by rfl⟩) R114527
theorem R1485863 : Reach 1485863 := rs (se 1 (by rfl) ⟨1114397, by rfl⟩) R2228795
theorem R175243 : Reach 175243 := rs (se 1 (by rfl) ⟨131432, by rfl⟩) R262865
theorem R77179 : Reach 77179 := rs (se 1 (by rfl) ⟨57884, by rfl⟩) R115769
theorem R175547 : Reach 175547 := rs (se 1 (by rfl) ⟨131660, by rfl⟩) R263321
theorem R143111 : Reach 143111 := rs (se 1 (by rfl) ⟨107333, by rfl⟩) R214667
theorem R77647 : Reach 77647 := rs (se 1 (by rfl) ⟨58235, by rfl⟩) R116471
theorem R339977 : Reach 339977 := rs (se 2 (by rfl) ⟨127491, by rfl⟩) R254983
theorem R602315 : Reach 602315 := rs (se 1 (by rfl) ⟨451736, by rfl⟩) R903473
theorem R78043 : Reach 78043 := rs (se 1 (by rfl) ⟨58532, by rfl⟩) R117065
theorem R78331 : Reach 78331 := rs (se 1 (by rfl) ⟨58748, by rfl⟩) R117497
theorem R242297 : Reach 242297 := rs (se 2 (by rfl) ⟨90861, by rfl⟩) R181723
theorem R143993 : Reach 143993 := rs (se 2 (by rfl) ⟨53997, by rfl⟩) R107995
theorem R78511 : Reach 78511 := rs (se 1 (by rfl) ⟨58883, by rfl⟩) R117767
theorem R2994893 : Reach 2994893 := rs (se 3 (by rfl) ⟨561542, by rfl⟩) R1123085
theorem R176863 : Reach 176863 := rs (se 1 (by rfl) ⟨132647, by rfl⟩) R265295
theorem R176975 : Reach 176975 := rs (se 1 (by rfl) ⟨132731, by rfl⟩) R265463
theorem R78799 : Reach 78799 := rs (se 1 (by rfl) ⟨59099, by rfl⟩) R118199
theorem R275699 : Reach 275699 := rs (se 1 (by rfl) ⟨206774, by rfl⟩) R413549
theorem R79195 : Reach 79195 := rs (se 1 (by rfl) ⟨59396, by rfl⟩) R118793
theorem R79303 : Reach 79303 := rs (se 1 (by rfl) ⟨59477, by rfl⟩) R118955
theorem R177623 : Reach 177623 := rs (se 1 (by rfl) ⟨133217, by rfl⟩) R266435
theorem R79663 : Reach 79663 := rs (se 1 (by rfl) ⟨59747, by rfl⟩) R119495
theorem R177977 : Reach 177977 := rs (se 2 (by rfl) ⟨66741, by rfl⟩) R133483
theorem R79771 : Reach 79771 := rs (se 1 (by rfl) ⟨59828, by rfl⟩) R119657
theorem R374969 : Reach 374969 := rs (se 2 (by rfl) ⟨140613, by rfl⟩) R281227
theorem R114043 : Reach 114043 := rs (se 1 (by rfl) ⟨85532, by rfl⟩) R171065
theorem R179617 : Reach 179617 := rs (se 2 (by rfl) ⟨67356, by rfl⟩) R134713
theorem R703907 : Reach 703907 := rs (se 1 (by rfl) ⟨527930, by rfl⟩) R1055861
theorem R114169 : Reach 114169 := rs (se 2 (by rfl) ⟨42813, by rfl⟩) R85627
theorem R343763 : Reach 343763 := rs (se 1 (by rfl) ⟨257822, by rfl⟩) R515645
theorem R147179 : Reach 147179 := rs (se 1 (by rfl) ⟨110384, by rfl⟩) R220769
theorem R868103 : Reach 868103 := rs (se 1 (by rfl) ⟨651077, by rfl⟩) R1302155
theorem R114439 : Reach 114439 := rs (se 1 (by rfl) ⟨85829, by rfl⟩) R171659
theorem R179975 : Reach 179975 := rs (se 1 (by rfl) ⟨134981, by rfl⟩) R269963
theorem R114473 : Reach 114473 := rs (se 2 (by rfl) ⟨42927, by rfl⟩) R85855
theorem R278633 : Reach 278633 := rs (se 2 (by rfl) ⟨104487, by rfl⟩) R208975
theorem R344411 : Reach 344411 := rs (se 1 (by rfl) ⟨258308, by rfl⟩) R516617
theorem R541129 : Reach 541129 := rs (se 2 (by rfl) ⟨202923, by rfl⟩) R405847
theorem R606689 : Reach 606689 := rs (se 2 (by rfl) ⟨227508, by rfl⟩) R455017
theorem R115195 : Reach 115195 := rs (se 1 (by rfl) ⟨86396, by rfl⟩) R172793
theorem R574087 : Reach 574087 := rs (se 1 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R148367 : Reach 148367 := rs (se 1 (by rfl) ⟨111275, by rfl⟩) R222551
theorem R115627 : Reach 115627 := rs (se 1 (by rfl) ⟨86720, by rfl⟩) R173441
theorem R541895 : Reach 541895 := rs (se 1 (by rfl) ⟨406421, by rfl⟩) R812843
theorem R115931 : Reach 115931 := rs (se 1 (by rfl) ⟨86948, by rfl⟩) R173897
theorem R705779 : Reach 705779 := rs (se 1 (by rfl) ⟨529334, by rfl⟩) R1058669
theorem R345383 : Reach 345383 := rs (se 1 (by rfl) ⟨259037, by rfl⟩) R518075
theorem R116167 : Reach 116167 := rs (se 1 (by rfl) ⟨87125, by rfl⟩) R174251
theorem R1034167 : Reach 1034167 := rs (se 1 (by rfl) ⟨775625, by rfl⟩) R1551251
theorem R116687 : Reach 116687 := rs (se 1 (by rfl) ⟨87515, by rfl⟩) R175031
theorem R804815 : Reach 804815 := rs (se 1 (by rfl) ⟨603611, by rfl⟩) R1207223
theorem R739343 : Reach 739343 := rs (se 1 (by rfl) ⟨554507, by rfl⟩) R1109015
theorem R117355 : Reach 117355 := rs (se 1 (by rfl) ⟨88016, by rfl⟩) R176033
theorem R445175 : Reach 445175 := rs (se 1 (by rfl) ⟨333881, by rfl⟩) R667763
theorem R117659 : Reach 117659 := rs (se 1 (by rfl) ⟨88244, by rfl⟩) R176489
theorem R216103 : Reach 216103 := rs (se 1 (by rfl) ⟨162077, by rfl⟩) R324155
theorem R674893 : Reach 674893 := rs (se 3 (by rfl) ⟨126542, by rfl⟩) R253085
theorem R347489 : Reach 347489 := rs (se 2 (by rfl) ⟨130308, by rfl⟩) R260617
theorem R3231089 : Reach 3231089 := rs (se 2 (by rfl) ⟨1211658, by rfl⟩) R2423317
theorem R806273 : Reach 806273 := rs (se 2 (by rfl) ⟨302352, by rfl⟩) R604705
theorem R151343 : Reach 151343 := rs (se 1 (by rfl) ⟨113507, by rfl⟩) R227015
theorem R741635 : Reach 741635 := rs (se 1 (by rfl) ⟨556226, by rfl⟩) R1112453
theorem R151919 : Reach 151919 := rs (se 1 (by rfl) ⟨113939, by rfl⟩) R227879
theorem R184751 : Reach 184751 := rs (se 1 (by rfl) ⟨138563, by rfl⟩) R277127
theorem R151991 : Reach 151991 := rs (se 1 (by rfl) ⟨113993, by rfl⟩) R227987
theorem R152135 : Reach 152135 := rs (se 1 (by rfl) ⟨114101, by rfl⟩) R228203
theorem R86599 : Reach 86599 := rs (se 1 (by rfl) ⟨64949, by rfl⟩) R129899
theorem R152171 : Reach 152171 := rs (se 1 (by rfl) ⟨114128, by rfl⟩) R228257
theorem R152567 : Reach 152567 := rs (se 1 (by rfl) ⟨114425, by rfl⟩) R228851
theorem R349433 : Reach 349433 := rs (se 2 (by rfl) ⟨131037, by rfl⟩) R262075
theorem R152927 : Reach 152927 := rs (se 1 (by rfl) ⟨114695, by rfl⟩) R229391
theorem R87419 : Reach 87419 := rs (se 1 (by rfl) ⟨65564, by rfl⟩) R131129
theorem R153323 : Reach 153323 := rs (se 1 (by rfl) ⟨114992, by rfl⟩) R229985
theorem R153449 : Reach 153449 := rs (se 2 (by rfl) ⟨57543, by rfl⟩) R115087
theorem R809189 : Reach 809189 := rs (se 4 (by rfl) ⟨75861, by rfl⟩) R151723
theorem R186835 : Reach 186835 := rs (se 1 (by rfl) ⟨140126, by rfl⟩) R280253
theorem R154295 : Reach 154295 := rs (se 1 (by rfl) ⟨115721, by rfl⟩) R231443
theorem R154511 : Reach 154511 := rs (se 1 (by rfl) ⟨115883, by rfl⟩) R231767
theorem R89039 : Reach 89039 := rs (se 1 (by rfl) ⟨66779, by rfl⟩) R133559
theorem R187355 : Reach 187355 := rs (se 1 (by rfl) ⟨140516, by rfl⟩) R281033
theorem R220603 : Reach 220603 := rs (se 1 (by rfl) ⟨165452, by rfl⟩) R330905
theorem R155231 : Reach 155231 := rs (se 1 (by rfl) ⟨116423, by rfl⟩) R232847
theorem R155447 : Reach 155447 := rs (se 1 (by rfl) ⟨116585, by rfl⟩) R233171
theorem R90011 : Reach 90011 := rs (se 1 (by rfl) ⟨67508, by rfl⟩) R135017
theorem R155753 : Reach 155753 := rs (se 2 (by rfl) ⟨58407, by rfl⟩) R116815
theorem R385505 : Reach 385505 := rs (se 2 (by rfl) ⟨144564, by rfl⟩) R289129
theorem R156239 : Reach 156239 := rs (se 1 (by rfl) ⟨117179, by rfl⟩) R234359
theorem R156383 : Reach 156383 := rs (se 1 (by rfl) ⟨117287, by rfl⟩) R234575
theorem R156635 : Reach 156635 := rs (se 1 (by rfl) ⟨117476, by rfl⟩) R234953
theorem R189431 : Reach 189431 := rs (se 1 (by rfl) ⟨142073, by rfl⟩) R284147
theorem R418823 : Reach 418823 := rs (se 1 (by rfl) ⟨314117, by rfl⟩) R628235
theorem R156815 : Reach 156815 := rs (se 1 (by rfl) ⟨117611, by rfl⟩) R235223
theorem R156905 : Reach 156905 := rs (se 2 (by rfl) ⟨58839, by rfl⟩) R117679
theorem R156959 : Reach 156959 := rs (se 1 (by rfl) ⟨117719, by rfl⟩) R235439
theorem R255271 : Reach 255271 := rs (se 1 (by rfl) ⟨191453, by rfl⟩) R382907
theorem R353645 : Reach 353645 := rs (se 3 (by rfl) ⟨66308, by rfl⟩) R132617
theorem R255545 : Reach 255545 := rs (se 2 (by rfl) ⟨95829, by rfl⟩) R191659
theorem R157481 : Reach 157481 := rs (se 2 (by rfl) ⟨59055, by rfl⟩) R118111
theorem R289403 : Reach 289403 := rs (se 1 (by rfl) ⟨217052, by rfl⟩) R434105
theorem R158543 : Reach 158543 := rs (se 1 (by rfl) ⟨118907, by rfl⟩) R237815
theorem R519047 : Reach 519047 := rs (se 1 (by rfl) ⟨389285, by rfl⟩) R778571
theorem R158759 : Reach 158759 := rs (se 1 (by rfl) ⟨119069, by rfl⟩) R238139
theorem R584819 : Reach 584819 := rs (se 1 (by rfl) ⟨438614, by rfl⟩) R877229
theorem R158939 : Reach 158939 := rs (se 1 (by rfl) ⟨119204, by rfl⟩) R238409
theorem R159137 : Reach 159137 := rs (se 2 (by rfl) ⟨59676, by rfl⟩) R119353
theorem R159175 : Reach 159175 := rs (se 1 (by rfl) ⟨119381, by rfl⟩) R238763
theorem R159191 : Reach 159191 := rs (se 1 (by rfl) ⟨119393, by rfl⟩) R238787
theorem R1404377 : Reach 1404377 := rs (se 2 (by rfl) ⟨526641, by rfl⟩) R1053283
theorem R650915 : Reach 650915 := rs (se 1 (by rfl) ⟨488186, by rfl⟩) R976373
theorem R356075 : Reach 356075 := rs (se 1 (by rfl) ⟨267056, by rfl⟩) R534113
theorem R388921 : Reach 388921 := rs (se 2 (by rfl) ⟨145845, by rfl⟩) R291691
theorem R290735 : Reach 290735 := rs (se 1 (by rfl) ⟨218051, by rfl⟩) R436103
theorem R159695 : Reach 159695 := rs (se 1 (by rfl) ⟨119771, by rfl⟩) R239543
theorem R356561 : Reach 356561 := rs (se 2 (by rfl) ⟨133710, by rfl⟩) R267421
theorem R782945 : Reach 782945 := rs (se 2 (by rfl) ⟨293604, by rfl⟩) R587209
theorem R357047 : Reach 357047 := rs (se 1 (by rfl) ⟨267785, by rfl⟩) R535571
theorem R357473 : Reach 357473 := rs (se 2 (by rfl) ⟨134052, by rfl⟩) R268105
theorem R324755 : Reach 324755 := rs (se 1 (by rfl) ⟨243566, by rfl⟩) R487133
theorem R357533 : Reach 357533 := rs (se 3 (by rfl) ⟨67037, by rfl⟩) R134075
theorem R128699 : Reach 128699 := rs (se 1 (by rfl) ⟨96524, by rfl⟩) R193049
theorem R194359 : Reach 194359 := rs (se 1 (by rfl) ⟨145769, by rfl⟩) R291539
theorem R227177 : Reach 227177 := rs (se 2 (by rfl) ⟨85191, by rfl⟩) R170383
theorem R1308919 : Reach 1308919 := rs (se 1 (by rfl) ⟨981689, by rfl⟩) R1963379
theorem R194825 : Reach 194825 := rs (se 2 (by rfl) ⟨73059, by rfl⟩) R146119
theorem R227609 : Reach 227609 := rs (se 2 (by rfl) ⟨85353, by rfl⟩) R170707
theorem R162155 : Reach 162155 := rs (se 1 (by rfl) ⟨121616, by rfl⟩) R243233
theorem R358829 : Reach 358829 := rs (se 3 (by rfl) ⟨67280, by rfl⟩) R134561
theorem R2587085 : Reach 2587085 := rs (se 3 (by rfl) ⟨485078, by rfl⟩) R970157
theorem R260603 : Reach 260603 := rs (se 1 (by rfl) ⟨195452, by rfl⟩) R390905
theorem R358991 : Reach 358991 := rs (se 1 (by rfl) ⟨269243, by rfl⟩) R538487
theorem R96889 : Reach 96889 := rs (se 2 (by rfl) ⟨36333, by rfl⟩) R72667
theorem R261035 : Reach 261035 := rs (se 1 (by rfl) ⟨195776, by rfl⟩) R391553
theorem R228491 : Reach 228491 := rs (se 1 (by rfl) ⟨171368, by rfl⟩) R342737
theorem R261407 : Reach 261407 := rs (se 1 (by rfl) ⟨196055, by rfl⟩) R392111
theorem R589193 : Reach 589193 := rs (se 2 (by rfl) ⟨220947, by rfl⟩) R441895
theorem R261575 : Reach 261575 := rs (se 1 (by rfl) ⟨196181, by rfl⟩) R392363
theorem R1146383 : Reach 1146383 := rs (se 1 (by rfl) ⟨859787, by rfl⟩) R1719575
theorem R294425 : Reach 294425 := rs (se 2 (by rfl) ⟨110409, by rfl⟩) R220819
theorem R163385 : Reach 163385 := rs (se 2 (by rfl) ⟨61269, by rfl⟩) R122539
theorem R130643 : Reach 130643 := rs (se 1 (by rfl) ⟨97982, by rfl⟩) R195965
theorem R228959 : Reach 228959 := rs (se 1 (by rfl) ⟨171719, by rfl⟩) R343439
theorem R130871 : Reach 130871 := rs (se 1 (by rfl) ⟨98153, by rfl⟩) R196307
theorem R393295 : Reach 393295 := rs (se 1 (by rfl) ⟨294971, by rfl⟩) R589943
theorem R229607 : Reach 229607 := rs (se 1 (by rfl) ⟨172205, by rfl⟩) R344411
theorem R98911 : Reach 98911 := rs (se 1 (by rfl) ⟨74183, by rfl⟩) R148367
theorem R721505 : Reach 721505 := rs (se 2 (by rfl) ⟨270564, by rfl⟩) R541129
theorem R197423 : Reach 197423 := rs (se 1 (by rfl) ⟨148067, by rfl⟩) R296135
theorem R230201 : Reach 230201 := rs (se 2 (by rfl) ⟨86325, by rfl⟩) R172651
theorem R230255 : Reach 230255 := rs (se 1 (by rfl) ⟨172691, by rfl⟩) R345383
theorem R492895 : Reach 492895 := rs (se 1 (by rfl) ⟨369671, by rfl⟩) R739343
theorem R67183 : Reach 67183 := rs (se 1 (by rfl) ⟨50387, by rfl⟩) R100775
theorem R231065 : Reach 231065 := rs (se 2 (by rfl) ⟨86649, by rfl⟩) R173299
theorem R67239 : Reach 67239 := rs (se 1 (by rfl) ⟨50429, by rfl⟩) R100859
theorem R67323 : Reach 67323 := rs (se 1 (by rfl) ⟨50492, by rfl⟩) R100985
theorem R67359 : Reach 67359 := rs (se 1 (by rfl) ⟨50519, by rfl⟩) R101039
theorem R67391 : Reach 67391 := rs (se 1 (by rfl) ⟨50543, by rfl⟩) R101087
theorem R296783 : Reach 296783 := rs (se 1 (by rfl) ⟨222587, by rfl⟩) R445175
theorem R67567 : Reach 67567 := rs (se 1 (by rfl) ⟨50675, by rfl⟩) R101351
theorem R67739 : Reach 67739 := rs (se 1 (by rfl) ⟨50804, by rfl⟩) R101609
theorem R67775 : Reach 67775 := rs (se 1 (by rfl) ⟨50831, by rfl⟩) R101663
theorem R231659 : Reach 231659 := rs (se 1 (by rfl) ⟨173744, by rfl⟩) R347489
theorem R67887 : Reach 67887 := rs (se 1 (by rfl) ⟨50915, by rfl⟩) R101831
theorem R199007 : Reach 199007 := rs (se 1 (by rfl) ⟨149255, by rfl⟩) R298511
theorem R68123 : Reach 68123 := rs (se 1 (by rfl) ⟨51092, by rfl⟩) R102185
theorem R100895 : Reach 100895 := rs (se 1 (by rfl) ⟨75671, by rfl⟩) R151343
theorem R68127 : Reach 68127 := rs (se 1 (by rfl) ⟨51095, by rfl⟩) R102191
theorem R199199 : Reach 199199 := rs (se 1 (by rfl) ⟨149399, by rfl⟩) R298799
theorem R1378889 : Reach 1378889 := rs (se 2 (by rfl) ⟨517083, by rfl⟩) R1034167
theorem R264809 : Reach 264809 := rs (se 2 (by rfl) ⟨99303, by rfl⟩) R198607
theorem R494423 : Reach 494423 := rs (se 1 (by rfl) ⟨370817, by rfl⟩) R741635
theorem R68443 : Reach 68443 := rs (se 1 (by rfl) ⟨51332, by rfl⟩) R102665
theorem R101279 : Reach 101279 := rs (se 1 (by rfl) ⟨75959, by rfl⟩) R151919
theorem R68511 : Reach 68511 := rs (se 1 (by rfl) ⟨51383, by rfl⟩) R102767
theorem R101327 : Reach 101327 := rs (se 1 (by rfl) ⟨75995, by rfl⟩) R151991
theorem R199655 : Reach 199655 := rs (se 1 (by rfl) ⟨149741, by rfl⟩) R299483
theorem R1575973 : Reach 1575973 := rs (se 4 (by rfl) ⟨147747, by rfl⟩) R295495
theorem R101417 : Reach 101417 := rs (se 2 (by rfl) ⟨38031, by rfl⟩) R76063
theorem R101423 : Reach 101423 := rs (se 1 (by rfl) ⟨76067, by rfl⟩) R152135
theorem R68655 : Reach 68655 := rs (se 1 (by rfl) ⟨51491, by rfl⟩) R102983
theorem R101447 : Reach 101447 := rs (se 1 (by rfl) ⟨76085, by rfl⟩) R152171
theorem R68679 : Reach 68679 := rs (se 1 (by rfl) ⟨51509, by rfl⟩) R103019
theorem R1445053 : Reach 1445053 := rs (se 3 (by rfl) ⟨270947, by rfl⟩) R541895
theorem R68831 : Reach 68831 := rs (se 1 (by rfl) ⟨51623, by rfl⟩) R103247
theorem R101711 : Reach 101711 := rs (se 1 (by rfl) ⟨76283, by rfl⟩) R152567
theorem R101801 : Reach 101801 := rs (se 2 (by rfl) ⟨38175, by rfl⟩) R76351
theorem R69095 : Reach 69095 := rs (se 1 (by rfl) ⟨51821, by rfl⟩) R103643
theorem R232955 : Reach 232955 := rs (se 1 (by rfl) ⟨174716, by rfl⟩) R349433
theorem R101951 : Reach 101951 := rs (se 1 (by rfl) ⟨76463, by rfl⟩) R152927
theorem R396863 : Reach 396863 := rs (se 1 (by rfl) ⟨297647, by rfl⟩) R595295
theorem R69211 : Reach 69211 := rs (se 1 (by rfl) ⟨51908, by rfl⟩) R103817
theorem R233117 : Reach 233117 := rs (se 3 (by rfl) ⟨43709, by rfl⟩) R87419
theorem R134951 : Reach 134951 := rs (se 1 (by rfl) ⟨101213, by rfl⟩) R202427
theorem R102215 : Reach 102215 := rs (se 1 (by rfl) ⟨76661, by rfl⟩) R153323
theorem R69447 : Reach 69447 := rs (se 1 (by rfl) ⟨52085, by rfl⟩) R104171
theorem R102299 : Reach 102299 := rs (se 1 (by rfl) ⟨76724, by rfl⟩) R153449
theorem R69599 : Reach 69599 := rs (se 1 (by rfl) ⟨52199, by rfl⟩) R104399
theorem R233657 : Reach 233657 := rs (se 2 (by rfl) ⟨87621, by rfl⟩) R175243
theorem R69863 : Reach 69863 := rs (se 1 (by rfl) ⟨52397, by rfl⟩) R104795
theorem R528767 : Reach 528767 := rs (se 1 (by rfl) ⟨396575, by rfl⟩) R793151
theorem R70015 : Reach 70015 := rs (se 1 (by rfl) ⟨52511, by rfl⟩) R105023
theorem R102863 : Reach 102863 := rs (se 1 (by rfl) ⟨77147, by rfl⟩) R154295
theorem R70095 : Reach 70095 := rs (se 1 (by rfl) ⟨52571, by rfl⟩) R105143
theorem R102905 : Reach 102905 := rs (se 2 (by rfl) ⟨38589, by rfl⟩) R77179
theorem R201295 : Reach 201295 := rs (se 1 (by rfl) ⟨150971, by rfl⟩) R301943
theorem R103007 : Reach 103007 := rs (se 1 (by rfl) ⟨77255, by rfl⟩) R154511
theorem R332383 : Reach 332383 := rs (se 1 (by rfl) ⟨249287, by rfl⟩) R498575
theorem R70247 : Reach 70247 := rs (se 1 (by rfl) ⟨52685, by rfl⟩) R105371
theorem R70511 : Reach 70511 := rs (se 1 (by rfl) ⟨52883, by rfl⟩) R105767
theorem R70567 : Reach 70567 := rs (se 1 (by rfl) ⟨52925, by rfl⟩) R105851
theorem R70651 : Reach 70651 := rs (se 1 (by rfl) ⟨52988, by rfl⟩) R105977
theorem R103487 : Reach 103487 := rs (se 1 (by rfl) ⟨77615, by rfl⟩) R155231
theorem R70719 : Reach 70719 := rs (se 1 (by rfl) ⟨53039, by rfl⟩) R106079
theorem R103529 : Reach 103529 := rs (se 2 (by rfl) ⟨38823, by rfl⟩) R77647
theorem R70831 : Reach 70831 := rs (se 1 (by rfl) ⟨53123, by rfl⟩) R106247
theorem R103631 : Reach 103631 := rs (se 1 (by rfl) ⟨77723, by rfl⟩) R155447
theorem R70863 : Reach 70863 := rs (se 1 (by rfl) ⟨53147, by rfl⟩) R106295
theorem R103835 : Reach 103835 := rs (se 1 (by rfl) ⟨77876, by rfl⟩) R155753
theorem R202139 : Reach 202139 := rs (se 1 (by rfl) ⟨151604, by rfl⟩) R303209
theorem R71067 : Reach 71067 := rs (se 1 (by rfl) ⟨53300, by rfl⟩) R106601
theorem R104057 : Reach 104057 := rs (se 2 (by rfl) ⟨39021, by rfl⟩) R78043
theorem R104159 : Reach 104159 := rs (se 1 (by rfl) ⟨78119, by rfl⟩) R156239
theorem R104255 : Reach 104255 := rs (se 1 (by rfl) ⟨78191, by rfl⟩) R156383
theorem R104423 : Reach 104423 := rs (se 1 (by rfl) ⟨78317, by rfl⟩) R156635
theorem R104441 : Reach 104441 := rs (se 2 (by rfl) ⟨39165, by rfl⟩) R78331
theorem R104543 : Reach 104543 := rs (se 1 (by rfl) ⟨78407, by rfl⟩) R156815
theorem R104603 : Reach 104603 := rs (se 1 (by rfl) ⟨78452, by rfl⟩) R156905
theorem R104639 : Reach 104639 := rs (se 1 (by rfl) ⟨78479, by rfl⟩) R156959
theorem R104681 : Reach 104681 := rs (se 2 (by rfl) ⟨39255, by rfl⟩) R78511
theorem R235763 : Reach 235763 := rs (se 1 (by rfl) ⟨176822, by rfl⟩) R353645
theorem R235817 : Reach 235817 := rs (se 2 (by rfl) ⟨88431, by rfl⟩) R176863
theorem R170363 : Reach 170363 := rs (se 1 (by rfl) ⟨127772, by rfl⟩) R255545
theorem R268667 : Reach 268667 := rs (se 1 (by rfl) ⟨201500, by rfl⟩) R403001
theorem R1841591 : Reach 1841591 := rs (se 1 (by rfl) ⟨1381193, by rfl⟩) R2762387
theorem R104987 : Reach 104987 := rs (se 1 (by rfl) ⟨78740, by rfl⟩) R157481
theorem R105065 : Reach 105065 := rs (se 2 (by rfl) ⟨39399, by rfl⟩) R78799
theorem R105593 : Reach 105593 := rs (se 2 (by rfl) ⟨39597, by rfl⟩) R79195
theorem R105695 : Reach 105695 := rs (se 1 (by rfl) ⟨79271, by rfl⟩) R158543
theorem R105737 : Reach 105737 := rs (se 2 (by rfl) ⟨39651, by rfl⟩) R79303
theorem R990575 : Reach 990575 := rs (se 1 (by rfl) ⟨742931, by rfl⟩) R1485863
theorem R105839 : Reach 105839 := rs (se 1 (by rfl) ⟨79379, by rfl⟩) R158759
theorem R105959 : Reach 105959 := rs (se 1 (by rfl) ⟨79469, by rfl⟩) R158939
theorem R106091 : Reach 106091 := rs (se 1 (by rfl) ⟨79568, by rfl⟩) R159137
theorem R106127 : Reach 106127 := rs (se 1 (by rfl) ⟨79595, by rfl⟩) R159191
theorem R106217 : Reach 106217 := rs (se 2 (by rfl) ⟨39831, by rfl⟩) R79663
theorem R433943 : Reach 433943 := rs (se 1 (by rfl) ⟨325457, by rfl⟩) R650915
theorem R237383 : Reach 237383 := rs (se 1 (by rfl) ⟨178037, by rfl⟩) R356075
theorem R106361 : Reach 106361 := rs (se 2 (by rfl) ⟨39885, by rfl⟩) R79771
theorem R237437 : Reach 237437 := rs (se 3 (by rfl) ⟨44519, by rfl⟩) R89039
theorem R106463 : Reach 106463 := rs (se 1 (by rfl) ⟨79847, by rfl⟩) R159695
theorem R401543 : Reach 401543 := rs (se 1 (by rfl) ⟨301157, by rfl⟩) R602315
theorem R237707 : Reach 237707 := rs (se 1 (by rfl) ⟨178280, by rfl⟩) R356561
theorem R1745225 : Reach 1745225 := rs (se 2 (by rfl) ⟨654459, by rfl⟩) R1308919
theorem R238031 : Reach 238031 := rs (se 1 (by rfl) ⟨178523, by rfl⟩) R357047
theorem R238315 : Reach 238315 := rs (se 1 (by rfl) ⟨178736, by rfl⟩) R357473
theorem R238355 : Reach 238355 := rs (se 1 (by rfl) ⟨178766, by rfl⟩) R357533
theorem R108103 : Reach 108103 := rs (se 1 (by rfl) ⟨81077, by rfl⟩) R162155
theorem R239219 : Reach 239219 := rs (se 1 (by rfl) ⟨179414, by rfl⟩) R358829
theorem R173735 : Reach 173735 := rs (se 1 (by rfl) ⟨130301, by rfl⟩) R260603
theorem R239327 : Reach 239327 := rs (se 1 (by rfl) ⟨179495, by rfl⟩) R358991
theorem R239489 : Reach 239489 := rs (se 2 (by rfl) ⟨89808, by rfl⟩) R179617
theorem R174023 : Reach 174023 := rs (se 1 (by rfl) ⟨130517, by rfl⟩) R261035
theorem R174271 : Reach 174271 := rs (se 1 (by rfl) ⟨130703, by rfl⟩) R261407
theorem R469271 : Reach 469271 := rs (se 1 (by rfl) ⟨351953, by rfl⟩) R703907
theorem R174383 : Reach 174383 := rs (se 1 (by rfl) ⟨130787, by rfl⟩) R261575
theorem R764255 : Reach 764255 := rs (se 1 (by rfl) ⟨573191, by rfl⟩) R1146383
theorem R108923 : Reach 108923 := rs (se 1 (by rfl) ⟨81692, by rfl⟩) R163385
theorem R240029 : Reach 240029 := rs (se 3 (by rfl) ⟨45005, by rfl⟩) R90011
theorem R76315 : Reach 76315 := rs (se 1 (by rfl) ⟨57236, by rfl⟩) R114473
theorem R306139 : Reach 306139 := rs (se 1 (by rfl) ⟨229604, by rfl⟩) R459209
theorem R404459 : Reach 404459 := rs (se 1 (by rfl) ⟨303344, by rfl⟩) R606689
theorem R175385 : Reach 175385 := rs (se 2 (by rfl) ⟨65769, by rfl⟩) R131539
theorem R77287 : Reach 77287 := rs (se 1 (by rfl) ⟨57965, by rfl⟩) R115931
theorem R470519 : Reach 470519 := rs (se 1 (by rfl) ⟨352889, by rfl⟩) R705779
theorem R765449 : Reach 765449 := rs (se 2 (by rfl) ⟨287043, by rfl⟩) R574087
theorem R175679 : Reach 175679 := rs (se 1 (by rfl) ⟨131759, by rfl⟩) R263519
theorem R175891 : Reach 175891 := rs (se 1 (by rfl) ⟨131918, by rfl⟩) R263837
theorem R77791 : Reach 77791 := rs (se 1 (by rfl) ⟨58343, by rfl⟩) R116687
theorem R536543 : Reach 536543 := rs (se 1 (by rfl) ⟨402407, by rfl⟩) R804815
theorem R340361 : Reach 340361 := rs (se 2 (by rfl) ⟨127635, by rfl⟩) R255271
theorem R307727 : Reach 307727 := rs (se 1 (by rfl) ⟨230795, by rfl⟩) R461591
theorem R78439 : Reach 78439 := rs (se 1 (by rfl) ⟨58829, by rfl⟩) R117659
theorem R897821 : Reach 897821 := rs (se 3 (by rfl) ⟨168341, by rfl⟩) R336683
theorem R177025 : Reach 177025 := rs (se 2 (by rfl) ⟨66384, by rfl⟩) R132769
theorem R537515 : Reach 537515 := rs (se 1 (by rfl) ⟨403136, by rfl⟩) R806273
theorem R1553651 : Reach 1553651 := rs (se 1 (by rfl) ⟨1165238, by rfl⟩) R2330477
theorem R177835 : Reach 177835 := rs (se 1 (by rfl) ⟨133376, by rfl⟩) R266753
theorem R178139 : Reach 178139 := rs (se 1 (by rfl) ⟨133604, by rfl⟩) R267209
theorem R178159 : Reach 178159 := rs (se 1 (by rfl) ⟨133619, by rfl⟩) R267239
theorem R178271 : Reach 178271 := rs (se 1 (by rfl) ⟨133703, by rfl⟩) R267407
theorem R243911 : Reach 243911 := rs (se 1 (by rfl) ⟨182933, by rfl⟩) R365867
theorem R113339 : Reach 113339 := rs (se 1 (by rfl) ⟨85004, by rfl⟩) R170009
theorem R899857 : Reach 899857 := rs (se 2 (by rfl) ⟨337446, by rfl⟩) R674893
theorem R768791 : Reach 768791 := rs (se 1 (by rfl) ⟨576593, by rfl⟩) R1153187
theorem R539459 : Reach 539459 := rs (se 1 (by rfl) ⟨404594, by rfl⟩) R809189
theorem R375965 : Reach 375965 := rs (se 3 (by rfl) ⟨70493, by rfl⟩) R140987
theorem R179567 : Reach 179567 := rs (se 1 (by rfl) ⟨134675, by rfl⟩) R269351
theorem R245339 : Reach 245339 := rs (se 1 (by rfl) ⟨184004, by rfl⟩) R368009
theorem R114655 : Reach 114655 := rs (se 1 (by rfl) ⟨85991, by rfl⟩) R171983
theorem R311435 : Reach 311435 := rs (se 1 (by rfl) ⟨233576, by rfl⟩) R467153
theorem R115303 : Reach 115303 := rs (se 1 (by rfl) ⟨86477, by rfl⟩) R172955
theorem R279215 : Reach 279215 := rs (se 1 (by rfl) ⟨209411, by rfl⟩) R418823
theorem R115465 : Reach 115465 := rs (se 2 (by rfl) ⟨43299, by rfl⟩) R86599
theorem R116059 : Reach 116059 := rs (se 1 (by rfl) ⟨87044, by rfl⟩) R174089
theorem R346031 : Reach 346031 := rs (se 1 (by rfl) ⟨259523, by rfl⟩) R519047
theorem R117031 : Reach 117031 := rs (se 1 (by rfl) ⟨87773, by rfl⟩) R175547
theorem R936251 : Reach 936251 := rs (se 1 (by rfl) ⟨702188, by rfl⟩) R1404377
theorem R117983 : Reach 117983 := rs (se 1 (by rfl) ⟨88487, by rfl⟩) R176975
theorem R249113 : Reach 249113 := rs (se 2 (by rfl) ⟨93417, by rfl⟩) R186835
theorem R216503 : Reach 216503 := rs (se 1 (by rfl) ⟨162377, by rfl⟩) R324755
theorem R183799 : Reach 183799 := rs (se 1 (by rfl) ⟨137849, by rfl⟩) R275699
theorem R118415 : Reach 118415 := rs (se 1 (by rfl) ⟨88811, by rfl⟩) R177623
theorem R85799 : Reach 85799 := rs (se 1 (by rfl) ⟨64349, by rfl⟩) R128699
theorem R118651 : Reach 118651 := rs (se 1 (by rfl) ⟨88988, by rfl⟩) R177977
theorem R151451 : Reach 151451 := rs (se 1 (by rfl) ⟨113588, by rfl⟩) R227177
theorem R249979 : Reach 249979 := rs (se 1 (by rfl) ⟨187484, by rfl⟩) R374969
theorem R151739 : Reach 151739 := rs (se 1 (by rfl) ⟨113804, by rfl⟩) R227609
theorem R1724723 : Reach 1724723 := rs (se 1 (by rfl) ⟨1293542, by rfl⟩) R2587085
theorem R152057 : Reach 152057 := rs (se 2 (by rfl) ⟨57021, by rfl⟩) R114043
theorem R152225 : Reach 152225 := rs (se 2 (by rfl) ⟨57084, by rfl⟩) R114169
theorem R479933 : Reach 479933 := rs (se 3 (by rfl) ⟨89987, by rfl⟩) R179975
theorem R152327 : Reach 152327 := rs (se 1 (by rfl) ⟨114245, by rfl⟩) R228491
theorem R152585 : Reach 152585 := rs (se 2 (by rfl) ⟨57219, by rfl⟩) R114439
theorem R87095 : Reach 87095 := rs (se 1 (by rfl) ⟨65321, by rfl⟩) R130643
theorem R152639 : Reach 152639 := rs (se 1 (by rfl) ⟨114479, by rfl⟩) R228959
theorem R578735 : Reach 578735 := rs (se 1 (by rfl) ⟨434051, by rfl⟩) R868103
theorem R87247 : Reach 87247 := rs (se 1 (by rfl) ⟨65435, by rfl⟩) R130871
theorem R972121 : Reach 972121 := rs (se 2 (by rfl) ⟨364545, by rfl⟩) R729091
theorem R185755 : Reach 185755 := rs (se 1 (by rfl) ⟨139316, by rfl⟩) R278633
theorem R153575 : Reach 153575 := rs (se 1 (by rfl) ⟨115181, by rfl⟩) R230363
theorem R153593 : Reach 153593 := rs (se 2 (by rfl) ⟨57597, by rfl⟩) R115195
theorem R153683 : Reach 153683 := rs (se 1 (by rfl) ⟨115262, by rfl⟩) R230525
theorem R153755 : Reach 153755 := rs (se 1 (by rfl) ⟨115316, by rfl⟩) R230633
theorem R88219 : Reach 88219 := rs (se 1 (by rfl) ⟨66164, by rfl⟩) R132329
theorem R153863 : Reach 153863 := rs (se 1 (by rfl) ⟨115397, by rfl⟩) R230795
theorem R154169 : Reach 154169 := rs (se 2 (by rfl) ⟨57813, by rfl⟩) R115627
theorem R481879 : Reach 481879 := rs (se 1 (by rfl) ⟨361409, by rfl⟩) R722819
theorem R1137239 : Reach 1137239 := rs (se 1 (by rfl) ⟨852929, by rfl⟩) R1705859
theorem R351377 : Reach 351377 := rs (se 2 (by rfl) ⟨131766, by rfl⟩) R263533
theorem R220409 : Reach 220409 := rs (se 2 (by rfl) ⟨82653, by rfl⟩) R165307
theorem R154889 : Reach 154889 := rs (se 2 (by rfl) ⟨58083, by rfl⟩) R116167
theorem R2154059 : Reach 2154059 := rs (se 1 (by rfl) ⟨1615544, by rfl⟩) R3231089
theorem R1072723 : Reach 1072723 := rs (se 1 (by rfl) ⟨804542, by rfl⟩) R1609085
theorem R155879 : Reach 155879 := rs (se 1 (by rfl) ⟨116909, by rfl⟩) R233819
theorem R123167 : Reach 123167 := rs (se 1 (by rfl) ⟨92375, by rfl⟩) R184751
theorem R221537 : Reach 221537 := rs (se 2 (by rfl) ⟨83076, by rfl⟩) R166153
theorem R156473 : Reach 156473 := rs (se 2 (by rfl) ⟨58677, by rfl⟩) R117355
theorem R156527 : Reach 156527 := rs (se 1 (by rfl) ⟨117395, by rfl⟩) R234791
theorem R3957923 : Reach 3957923 := rs (se 1 (by rfl) ⟨2968442, by rfl⟩) R5936885
theorem R288137 : Reach 288137 := rs (se 2 (by rfl) ⟨108051, by rfl⟩) R216103
theorem R157103 : Reach 157103 := rs (se 1 (by rfl) ⟨117827, by rfl⟩) R235655
theorem R189949 : Reach 189949 := rs (se 3 (by rfl) ⟨35615, by rfl⟩) R71231
theorem R353807 : Reach 353807 := rs (se 1 (by rfl) ⟨265355, by rfl⟩) R530711
theorem R223177 : Reach 223177 := rs (se 2 (by rfl) ⟨83691, by rfl⟩) R167383
theorem R124903 : Reach 124903 := rs (se 1 (by rfl) ⟨93677, by rfl⟩) R187355
theorem R157931 : Reach 157931 := rs (se 1 (by rfl) ⟨118448, by rfl⟩) R236897
theorem R354617 : Reach 354617 := rs (se 2 (by rfl) ⟨132981, by rfl⟩) R265963
theorem R289163 : Reach 289163 := rs (se 1 (by rfl) ⟨216872, by rfl⟩) R433745
theorem R518561 : Reach 518561 := rs (se 2 (by rfl) ⟨194460, by rfl⟩) R388921
theorem R813685 : Reach 813685 := rs (se 5 (by rfl) ⟨38141, by rfl⟩) R76283
theorem R355265 : Reach 355265 := rs (se 2 (by rfl) ⟨133224, by rfl⟩) R266449
theorem R257003 : Reach 257003 := rs (se 1 (by rfl) ⟨192752, by rfl⟩) R385505
theorem R126287 : Reach 126287 := rs (se 1 (by rfl) ⟨94715, by rfl⟩) R189431
theorem R519533 : Reach 519533 := rs (se 3 (by rfl) ⟨97412, by rfl⟩) R194825
theorem R191933 : Reach 191933 := rs (se 3 (by rfl) ⟨35987, by rfl⟩) R71975
theorem R159227 : Reach 159227 := rs (se 1 (by rfl) ⟨119420, by rfl⟩) R238841
theorem R355913 : Reach 355913 := rs (se 2 (by rfl) ⟨133467, by rfl⟩) R266935
theorem R159407 : Reach 159407 := rs (se 1 (by rfl) ⟨119555, by rfl⟩) R239111
theorem R1273553 : Reach 1273553 := rs (se 2 (by rfl) ⟨477582, by rfl⟩) R955165
theorem R290803 : Reach 290803 := rs (se 1 (by rfl) ⟨218102, by rfl⟩) R436205
theorem R159731 : Reach 159731 := rs (se 1 (by rfl) ⟨119798, by rfl⟩) R239597
theorem R487619 : Reach 487619 := rs (se 1 (by rfl) ⟨365714, by rfl⟩) R731429
theorem R192935 : Reach 192935 := rs (se 1 (by rfl) ⟨144701, by rfl⟩) R289403
theorem R389879 : Reach 389879 := rs (se 1 (by rfl) ⟨292409, by rfl⟩) R584819
theorem R848933 : Reach 848933 := rs (se 4 (by rfl) ⟨79587, by rfl⟩) R159175
theorem R259145 : Reach 259145 := rs (se 2 (by rfl) ⟨97179, by rfl⟩) R194359
theorem R95407 : Reach 95407 := rs (se 1 (by rfl) ⟨71555, by rfl⟩) R143111
theorem R193823 : Reach 193823 := rs (se 1 (by rfl) ⟨145367, by rfl⟩) R290735
theorem R226651 : Reach 226651 := rs (se 1 (by rfl) ⟨169988, by rfl⟩) R339977
theorem R521963 : Reach 521963 := rs (se 1 (by rfl) ⟨391472, by rfl⟩) R782945
theorem R161531 : Reach 161531 := rs (se 1 (by rfl) ⟨121148, by rfl⟩) R242297
theorem R95995 : Reach 95995 := rs (se 1 (by rfl) ⟨71996, by rfl⟩) R143993
theorem R1996595 : Reach 1996595 := rs (se 1 (by rfl) ⟨1497446, by rfl⟩) R2994893
theorem R358505 : Reach 358505 := rs (se 2 (by rfl) ⟨134439, by rfl⟩) R268879
theorem R129185 : Reach 129185 := rs (se 2 (by rfl) ⟨48444, by rfl⟩) R96889
theorem R294137 : Reach 294137 := rs (se 2 (by rfl) ⟨110301, by rfl⟩) R220603
theorem R392795 : Reach 392795 := rs (se 1 (by rfl) ⟨294596, by rfl⟩) R589193
theorem R196283 : Reach 196283 := rs (se 1 (by rfl) ⟨147212, by rfl⟩) R294425
theorem R229175 : Reach 229175 := rs (se 1 (by rfl) ⟨171881, by rfl⟩) R343763
theorem R98119 : Reach 98119 := rs (se 1 (by rfl) ⟨73589, by rfl⟩) R147179
theorem R524393 : Reach 524393 := rs (se 2 (by rfl) ⟨196647, by rfl⟩) R393295
theorem R131615 : Reach 131615 := rs (se 1 (by rfl) ⟨98711, by rfl⟩) R197423
theorem R328445 : Reach 328445 := rs (se 3 (by rfl) ⟨61583, by rfl⟩) R123167
theorem R131881 : Reach 131881 := rs (se 2 (by rfl) ⟨49455, by rfl⟩) R98911
theorem R197855 : Reach 197855 := rs (se 1 (by rfl) ⟨148391, by rfl⟩) R296783
theorem R230687 : Reach 230687 := rs (se 1 (by rfl) ⟨173015, by rfl⟩) R346031
theorem R624167 : Reach 624167 := rs (se 1 (by rfl) ⟨468125, by rfl⟩) R936251
theorem R132671 : Reach 132671 := rs (se 1 (by rfl) ⟨99503, by rfl⟩) R199007
theorem R67263 : Reach 67263 := rs (se 1 (by rfl) ⟨50447, by rfl⟩) R100895
theorem R919259 : Reach 919259 := rs (se 1 (by rfl) ⟨689444, by rfl⟩) R1378889
theorem R657193 : Reach 657193 := rs (se 2 (by rfl) ⟨246447, by rfl⟩) R492895
theorem R329615 : Reach 329615 := rs (se 1 (by rfl) ⟨247211, by rfl⟩) R494423
theorem R67519 : Reach 67519 := rs (se 1 (by rfl) ⟨50639, by rfl⟩) R101279
theorem R67551 : Reach 67551 := rs (se 1 (by rfl) ⟨50663, by rfl⟩) R101327
theorem R133103 : Reach 133103 := rs (se 1 (by rfl) ⟨99827, by rfl⟩) R199655
theorem R67611 : Reach 67611 := rs (se 1 (by rfl) ⟨50708, by rfl⟩) R101417
theorem R67615 : Reach 67615 := rs (se 1 (by rfl) ⟨50711, by rfl⟩) R101423
theorem R67631 : Reach 67631 := rs (se 1 (by rfl) ⟨50723, by rfl⟩) R101447
theorem R67807 : Reach 67807 := rs (se 1 (by rfl) ⟨50855, by rfl⟩) R101711
theorem R67867 : Reach 67867 := rs (se 1 (by rfl) ⟨50900, by rfl⟩) R101801
theorem R67967 : Reach 67967 := rs (se 1 (by rfl) ⟨50975, by rfl⟩) R101951
theorem R264575 : Reach 264575 := rs (se 1 (by rfl) ⟨198431, by rfl⟩) R396863
theorem R68143 : Reach 68143 := rs (se 1 (by rfl) ⟨51107, by rfl⟩) R102215
theorem R297569 : Reach 297569 := rs (se 2 (by rfl) ⟨111588, by rfl⟩) R223177
theorem R100967 : Reach 100967 := rs (se 1 (by rfl) ⟨75725, by rfl⟩) R151451
theorem R68199 : Reach 68199 := rs (se 1 (by rfl) ⟨51149, by rfl⟩) R102299
theorem R166537 : Reach 166537 := rs (se 2 (by rfl) ⟨62451, by rfl⟩) R124903
theorem R101159 : Reach 101159 := rs (se 1 (by rfl) ⟨75869, by rfl⟩) R151739
theorem R232253 : Reach 232253 := rs (se 3 (by rfl) ⟨43547, by rfl⟩) R87095
theorem R1149815 : Reach 1149815 := rs (se 1 (by rfl) ⟨862361, by rfl⟩) R1724723
theorem R232361 : Reach 232361 := rs (se 2 (by rfl) ⟨87135, by rfl⟩) R174271
theorem R68575 : Reach 68575 := rs (se 1 (by rfl) ⟨51431, by rfl⟩) R102863
theorem R68603 : Reach 68603 := rs (se 1 (by rfl) ⟨51452, by rfl⟩) R102905
theorem R68671 : Reach 68671 := rs (se 1 (by rfl) ⟨51503, by rfl⟩) R103007
theorem R101483 : Reach 101483 := rs (se 1 (by rfl) ⟨76112, by rfl⟩) R152225
theorem R101723 : Reach 101723 := rs (se 1 (by rfl) ⟨76292, by rfl⟩) R152585
theorem R101753 : Reach 101753 := rs (se 2 (by rfl) ⟨38157, by rfl⟩) R76315
theorem R101759 : Reach 101759 := rs (se 1 (by rfl) ⟨76319, by rfl⟩) R152639
theorem R68991 : Reach 68991 := rs (se 1 (by rfl) ⟨51743, by rfl⟩) R103487
theorem R69019 : Reach 69019 := rs (se 1 (by rfl) ⟨51764, by rfl⟩) R103529
theorem R69087 : Reach 69087 := rs (se 1 (by rfl) ⟨51815, by rfl⟩) R103631
theorem R1084913 : Reach 1084913 := rs (se 2 (by rfl) ⟨406842, by rfl⟩) R813685
theorem R69223 : Reach 69223 := rs (se 1 (by rfl) ⟨51917, by rfl⟩) R103835
theorem R134759 : Reach 134759 := rs (se 1 (by rfl) ⟨101069, by rfl⟩) R202139
theorem R69371 : Reach 69371 := rs (se 1 (by rfl) ⟨52028, by rfl⟩) R104057
theorem R69439 : Reach 69439 := rs (se 1 (by rfl) ⟨52079, by rfl⟩) R104159
theorem R69503 : Reach 69503 := rs (se 1 (by rfl) ⟨52127, by rfl⟩) R104255
theorem R102383 : Reach 102383 := rs (se 1 (by rfl) ⟨76787, by rfl⟩) R153575
theorem R69615 : Reach 69615 := rs (se 1 (by rfl) ⟨52211, by rfl⟩) R104423
theorem R102395 : Reach 102395 := rs (se 1 (by rfl) ⟨76796, by rfl⟩) R153593
theorem R69627 : Reach 69627 := rs (se 1 (by rfl) ⟨52220, by rfl⟩) R104441
theorem R2101297 : Reach 2101297 := rs (se 2 (by rfl) ⟨787986, by rfl⟩) R1575973
theorem R102455 : Reach 102455 := rs (se 1 (by rfl) ⟨76841, by rfl⟩) R153683
theorem R69695 : Reach 69695 := rs (se 1 (by rfl) ⟨52271, by rfl⟩) R104543
theorem R102503 : Reach 102503 := rs (se 1 (by rfl) ⟨76877, by rfl⟩) R153755
theorem R69735 : Reach 69735 := rs (se 1 (by rfl) ⟨52301, by rfl⟩) R104603
theorem R69759 : Reach 69759 := rs (se 1 (by rfl) ⟨52319, by rfl⟩) R104639
theorem R69787 : Reach 69787 := rs (se 1 (by rfl) ⟨52340, by rfl⟩) R104681
theorem R102575 : Reach 102575 := rs (se 1 (by rfl) ⟨76931, by rfl⟩) R153863
theorem R69991 : Reach 69991 := rs (se 1 (by rfl) ⟨52493, by rfl⟩) R104987
theorem R102779 : Reach 102779 := rs (se 1 (by rfl) ⟨77084, by rfl⟩) R154169
theorem R758159 : Reach 758159 := rs (se 1 (by rfl) ⟨568619, by rfl⟩) R1137239
theorem R70043 : Reach 70043 := rs (se 1 (by rfl) ⟨52532, by rfl⟩) R105065
theorem R103049 : Reach 103049 := rs (se 2 (by rfl) ⟨38643, by rfl⟩) R77287
theorem R70395 : Reach 70395 := rs (se 1 (by rfl) ⟨52796, by rfl⟩) R105593
theorem R234251 : Reach 234251 := rs (se 1 (by rfl) ⟨175688, by rfl⟩) R351377
theorem R70463 : Reach 70463 := rs (se 1 (by rfl) ⟨52847, by rfl⟩) R105695
theorem R103259 : Reach 103259 := rs (se 1 (by rfl) ⟨77444, by rfl⟩) R154889
theorem R70491 : Reach 70491 := rs (se 1 (by rfl) ⟨52868, by rfl⟩) R105737
theorem R660383 : Reach 660383 := rs (se 1 (by rfl) ⟨495287, by rfl⟩) R990575
theorem R70559 : Reach 70559 := rs (se 1 (by rfl) ⟨52919, by rfl⟩) R105839
theorem R70639 : Reach 70639 := rs (se 1 (by rfl) ⟨52979, by rfl⟩) R105959
theorem R234521 : Reach 234521 := rs (se 2 (by rfl) ⟨87945, by rfl⟩) R175891
theorem R70727 : Reach 70727 := rs (se 1 (by rfl) ⟨53045, by rfl⟩) R106091
theorem R70751 : Reach 70751 := rs (se 1 (by rfl) ⟨53063, by rfl⟩) R106127
theorem R70811 : Reach 70811 := rs (se 1 (by rfl) ⟨53108, by rfl⟩) R106217
theorem R70907 : Reach 70907 := rs (se 1 (by rfl) ⟨53180, by rfl⟩) R106361
theorem R103721 : Reach 103721 := rs (se 2 (by rfl) ⟨38895, by rfl⟩) R77791
theorem R70975 : Reach 70975 := rs (se 1 (by rfl) ⟨53231, by rfl⟩) R106463
theorem R267695 : Reach 267695 := rs (se 1 (by rfl) ⟨200771, by rfl⟩) R401543
theorem R103919 : Reach 103919 := rs (se 1 (by rfl) ⟨77939, by rfl⟩) R155879
theorem R333305 : Reach 333305 := rs (se 2 (by rfl) ⟨124989, by rfl⟩) R249979
theorem R104315 : Reach 104315 := rs (se 1 (by rfl) ⟨78236, by rfl⟩) R156473
theorem R104351 : Reach 104351 := rs (se 1 (by rfl) ⟨78263, by rfl⟩) R156527
theorem R1251389 : Reach 1251389 := rs (se 3 (by rfl) ⟨234635, by rfl⟩) R469271
theorem R268393 : Reach 268393 := rs (se 2 (by rfl) ⟨100647, by rfl⟩) R201295
theorem R104585 : Reach 104585 := rs (se 2 (by rfl) ⟨39219, by rfl⟩) R78439
theorem R104735 : Reach 104735 := rs (se 1 (by rfl) ⟨78551, by rfl⟩) R157103
theorem R235871 : Reach 235871 := rs (se 1 (by rfl) ⟨176903, by rfl⟩) R353807
theorem R236033 : Reach 236033 := rs (se 2 (by rfl) ⟨88512, by rfl⟩) R177025
theorem R531197 : Reach 531197 := rs (se 3 (by rfl) ⟨99599, by rfl⟩) R199199
theorem R105287 : Reach 105287 := rs (se 1 (by rfl) ⟨78965, by rfl⟩) R157931
theorem R236411 : Reach 236411 := rs (se 1 (by rfl) ⟨177308, by rfl⟩) R354617
theorem R302201 : Reach 302201 := rs (se 2 (by rfl) ⟨113325, by rfl⟩) R226651
theorem R236843 : Reach 236843 := rs (se 1 (by rfl) ⟨177632, by rfl⟩) R355265
theorem R171335 : Reach 171335 := rs (se 1 (by rfl) ⟨128501, by rfl⟩) R257003
theorem R269639 : Reach 269639 := rs (se 1 (by rfl) ⟨202229, by rfl⟩) R404459
theorem R237113 : Reach 237113 := rs (se 2 (by rfl) ⟨88917, by rfl⟩) R177835
theorem R106151 : Reach 106151 := rs (se 1 (by rfl) ⟨79613, by rfl⟩) R159227
theorem R237275 : Reach 237275 := rs (se 1 (by rfl) ⟨177956, by rfl⟩) R355913
theorem R106271 : Reach 106271 := rs (se 1 (by rfl) ⟨79703, by rfl⟩) R159407
theorem R237545 : Reach 237545 := rs (se 2 (by rfl) ⟨89079, by rfl⟩) R178159
theorem R106487 : Reach 106487 := rs (se 1 (by rfl) ⟨79865, by rfl⟩) R159731
theorem R205151 : Reach 205151 := rs (se 1 (by rfl) ⟨153863, by rfl⟩) R307727
theorem R598547 : Reach 598547 := rs (se 1 (by rfl) ⟨448910, by rfl⟩) R897821
theorem R565955 : Reach 565955 := rs (se 1 (by rfl) ⟨424466, by rfl⟩) R848933
theorem R172763 : Reach 172763 := rs (se 1 (by rfl) ⟨129572, by rfl⟩) R259145
theorem R664301 : Reach 664301 := rs (se 3 (by rfl) ⟨124556, by rfl⟩) R249113
theorem R107687 : Reach 107687 := rs (se 1 (by rfl) ⟨80765, by rfl⟩) R161531
theorem R239003 : Reach 239003 := rs (se 1 (by rfl) ⟨179252, by rfl⟩) R358505
theorem R75559 : Reach 75559 := rs (se 1 (by rfl) ⟨56669, by rfl⟩) R113339
theorem R207623 : Reach 207623 := rs (se 1 (by rfl) ⟨155717, by rfl⟩) R311435
theorem R405485 : Reach 405485 := rs (se 3 (by rfl) ⟨76028, by rfl⟩) R152057
theorem R176539 : Reach 176539 := rs (se 1 (by rfl) ⟨132404, by rfl⟩) R264809
theorem R406205 : Reach 406205 := rs (se 3 (by rfl) ⟨76163, by rfl⟩) R152327
theorem R144137 : Reach 144137 := rs (se 2 (by rfl) ⟨54051, by rfl⟩) R108103
theorem R78655 : Reach 78655 := rs (se 1 (by rfl) ⟨58991, by rfl⟩) R117983
theorem R144335 : Reach 144335 := rs (se 1 (by rfl) ⟨108251, by rfl⟩) R216503
theorem R78943 : Reach 78943 := rs (se 1 (by rfl) ⟨59207, by rfl⟩) R118415
theorem R768365 : Reach 768365 := rs (se 3 (by rfl) ⟨144068, by rfl⟩) R288137
theorem R408185 : Reach 408185 := rs (se 2 (by rfl) ⟨153069, by rfl⟩) R306139
theorem R113575 : Reach 113575 := rs (se 1 (by rfl) ⟨85181, by rfl⟩) R170363
theorem R179111 : Reach 179111 := rs (se 1 (by rfl) ⟨134333, by rfl⟩) R268667
theorem R1227727 : Reach 1227727 := rs (se 1 (by rfl) ⟨920795, by rfl⟩) R1841591
theorem R245065 : Reach 245065 := rs (se 2 (by rfl) ⟨91899, by rfl⟩) R183799
theorem R146939 : Reach 146939 := rs (se 1 (by rfl) ⟨110204, by rfl⟩) R220409
theorem R1163483 : Reach 1163483 := rs (se 1 (by rfl) ⟨872612, by rfl⟩) R1745225
theorem R147691 : Reach 147691 := rs (se 1 (by rfl) ⟨110768, by rfl⟩) R221537
theorem R2638615 : Reach 2638615 := rs (se 1 (by rfl) ⟨1978961, by rfl⟩) R3957923
theorem R443177 : Reach 443177 := rs (se 2 (by rfl) ⟨166191, by rfl⟩) R332383
theorem R508837 : Reach 508837 := rs (se 4 (by rfl) ⟨47703, by rfl⟩) R95407
theorem R115823 : Reach 115823 := rs (se 1 (by rfl) ⟨86867, by rfl⟩) R173735
theorem R116015 : Reach 116015 := rs (se 1 (by rfl) ⟨87011, by rfl⟩) R174023
theorem R116255 : Reach 116255 := rs (se 1 (by rfl) ⟨87191, by rfl⟩) R174383
theorem R509503 : Reach 509503 := rs (se 1 (by rfl) ⟨382127, by rfl⟩) R764255
theorem R116329 : Reach 116329 := rs (se 2 (by rfl) ⟨43623, by rfl⟩) R87247
theorem R345707 : Reach 345707 := rs (se 1 (by rfl) ⟨259280, by rfl⟩) R518561
theorem R1296161 : Reach 1296161 := rs (se 2 (by rfl) ⟨486060, by rfl⟩) R972121
theorem R247673 : Reach 247673 := rs (se 2 (by rfl) ⟨92877, by rfl⟩) R185755
theorem R2050109 : Reach 2050109 := rs (se 3 (by rfl) ⟨384395, by rfl⟩) R768791
theorem R116923 : Reach 116923 := rs (se 1 (by rfl) ⟨87692, by rfl⟩) R175385
theorem R84191 : Reach 84191 := rs (se 1 (by rfl) ⟨63143, by rfl⟩) R126287
theorem R346355 : Reach 346355 := rs (se 1 (by rfl) ⟨259766, by rfl⟩) R519533
theorem R313679 : Reach 313679 := rs (se 1 (by rfl) ⟨235259, by rfl⟩) R470519
theorem R510299 : Reach 510299 := rs (se 1 (by rfl) ⟨382724, by rfl⟩) R765449
theorem R117119 : Reach 117119 := rs (se 1 (by rfl) ⟨87839, by rfl⟩) R175679
theorem R117625 : Reach 117625 := rs (se 2 (by rfl) ⟨44109, by rfl⟩) R88219
theorem R642505 : Reach 642505 := rs (se 2 (by rfl) ⟨240939, by rfl⟩) R481879
theorem R1035767 : Reach 1035767 := rs (se 1 (by rfl) ⟨776825, by rfl⟩) R1553651
theorem R1199809 : Reach 1199809 := rs (se 2 (by rfl) ⟨449928, by rfl⟩) R899857
theorem R347975 : Reach 347975 := rs (se 1 (by rfl) ⟨260981, by rfl⟩) R521963
theorem R1331063 : Reach 1331063 := rs (se 1 (by rfl) ⟨998297, by rfl⟩) R1996595
theorem R118759 : Reach 118759 := rs (se 1 (by rfl) ⟨89069, by rfl⟩) R178139
theorem R118847 : Reach 118847 := rs (se 1 (by rfl) ⟨89135, by rfl⟩) R178271
theorem R86123 : Reach 86123 := rs (se 1 (by rfl) ⟨64592, by rfl⟩) R129185
theorem R250643 : Reach 250643 := rs (se 1 (by rfl) ⟨187982, by rfl⟩) R375965
theorem R1430297 : Reach 1430297 := rs (se 2 (by rfl) ⟨536361, by rfl⟩) R1072723
theorem R119711 : Reach 119711 := rs (se 1 (by rfl) ⟨89783, by rfl⟩) R179567
theorem R152783 : Reach 152783 := rs (se 1 (by rfl) ⟨114587, by rfl⟩) R229175
theorem R152873 : Reach 152873 := rs (se 2 (by rfl) ⟨57327, by rfl⟩) R114655
theorem R153071 : Reach 153071 := rs (se 1 (by rfl) ⟨114803, by rfl⟩) R229607
theorem R186143 : Reach 186143 := rs (se 1 (by rfl) ⟨139607, by rfl⟩) R279215
theorem R153467 : Reach 153467 := rs (se 1 (by rfl) ⟨115100, by rfl⟩) R230201
theorem R153503 : Reach 153503 := rs (se 1 (by rfl) ⟨115127, by rfl⟩) R230255
theorem R153737 : Reach 153737 := rs (se 2 (by rfl) ⟨57651, by rfl⟩) R115303
theorem R317753 : Reach 317753 := rs (se 2 (by rfl) ⟨119157, by rfl⟩) R238315
theorem R153953 : Reach 153953 := rs (se 2 (by rfl) ⟨57732, by rfl⟩) R115465
theorem R154043 : Reach 154043 := rs (se 1 (by rfl) ⟨115532, by rfl⟩) R231065
theorem R154439 : Reach 154439 := rs (se 1 (by rfl) ⟨115829, by rfl⟩) R231659
theorem R1924013 : Reach 1924013 := rs (se 3 (by rfl) ⟨360752, by rfl⟩) R721505
theorem R154745 : Reach 154745 := rs (se 2 (by rfl) ⟨58029, by rfl⟩) R116059
theorem R253265 : Reach 253265 := rs (se 2 (by rfl) ⟨94974, by rfl⟩) R189949
theorem R155303 : Reach 155303 := rs (se 1 (by rfl) ⟨116477, by rfl⟩) R232955
theorem R155411 : Reach 155411 := rs (se 1 (by rfl) ⟨116558, by rfl⟩) R233117
theorem R155771 : Reach 155771 := rs (se 1 (by rfl) ⟨116828, by rfl⟩) R233657
theorem R352511 : Reach 352511 := rs (se 1 (by rfl) ⟨264383, by rfl⟩) R528767
theorem R156041 : Reach 156041 := rs (se 2 (by rfl) ⟨58515, by rfl⟩) R117031
theorem R319955 : Reach 319955 := rs (se 1 (by rfl) ⟨239966, by rfl⟩) R479933
theorem R385823 : Reach 385823 := rs (se 1 (by rfl) ⟨289367, by rfl⟩) R578735
theorem R157175 : Reach 157175 := rs (se 1 (by rfl) ⟨117881, by rfl⟩) R235763
theorem R157211 : Reach 157211 := rs (se 1 (by rfl) ⟨117908, by rfl⟩) R235817
theorem R1926737 : Reach 1926737 := rs (se 2 (by rfl) ⟨722526, by rfl⟩) R1445053
theorem R1436039 : Reach 1436039 := rs (se 1 (by rfl) ⟨1077029, by rfl⟩) R2154059
theorem R158201 : Reach 158201 := rs (se 2 (by rfl) ⟨59325, by rfl⟩) R118651
theorem R289295 : Reach 289295 := rs (se 1 (by rfl) ⟨216971, by rfl⟩) R433943
theorem R158255 : Reach 158255 := rs (se 1 (by rfl) ⟨118691, by rfl⟩) R237383
theorem R158291 : Reach 158291 := rs (se 1 (by rfl) ⟨118718, by rfl⟩) R237437
theorem R387737 : Reach 387737 := rs (se 2 (by rfl) ⟨145401, by rfl⟩) R290803
theorem R158471 : Reach 158471 := rs (se 1 (by rfl) ⟨118853, by rfl⟩) R237707
theorem R158687 : Reach 158687 := rs (se 1 (by rfl) ⟨119015, by rfl⟩) R238031
theorem R158903 : Reach 158903 := rs (se 1 (by rfl) ⟨119177, by rfl⟩) R238355
theorem R650429 : Reach 650429 := rs (se 3 (by rfl) ⟨121955, by rfl⟩) R243911
theorem R290461 : Reach 290461 := rs (se 3 (by rfl) ⟨54461, by rfl⟩) R108923
theorem R159479 : Reach 159479 := rs (se 1 (by rfl) ⟨119609, by rfl⟩) R239219
theorem R159551 : Reach 159551 := rs (se 1 (by rfl) ⟨119663, by rfl⟩) R239327
theorem R159659 : Reach 159659 := rs (se 1 (by rfl) ⟨119744, by rfl⟩) R239489
theorem R192775 : Reach 192775 := rs (se 1 (by rfl) ⟨144581, by rfl⟩) R289163
theorem R160019 : Reach 160019 := rs (se 1 (by rfl) ⟨120014, by rfl⟩) R240029
theorem R127955 : Reach 127955 := rs (se 1 (by rfl) ⟨95966, by rfl⟩) R191933
theorem R127993 : Reach 127993 := rs (se 2 (by rfl) ⟨47997, by rfl⟩) R95995
theorem R849035 : Reach 849035 := rs (se 1 (by rfl) ⟨636776, by rfl⟩) R1273553
theorem R357695 : Reach 357695 := rs (se 1 (by rfl) ⟨268271, by rfl⟩) R536543
theorem R325079 : Reach 325079 := rs (se 1 (by rfl) ⟨243809, by rfl⟩) R487619
theorem R226907 : Reach 226907 := rs (se 1 (by rfl) ⟨170180, by rfl⟩) R340361
theorem R128623 : Reach 128623 := rs (se 1 (by rfl) ⟨96467, by rfl⟩) R192935
theorem R259919 : Reach 259919 := rs (se 1 (by rfl) ⟨194939, by rfl⟩) R389879
theorem R358343 : Reach 358343 := rs (se 1 (by rfl) ⟨268757, by rfl⟩) R537515
theorem R129215 : Reach 129215 := rs (se 1 (by rfl) ⟨96911, by rfl⟩) R193823
theorem R523421 : Reach 523421 := rs (se 3 (by rfl) ⟨98141, by rfl⟩) R196283
theorem R359639 : Reach 359639 := rs (se 1 (by rfl) ⟨269729, by rfl⟩) R539459
theorem R228797 : Reach 228797 := rs (se 3 (by rfl) ⟨42899, by rfl⟩) R85799
theorem R359869 : Reach 359869 := rs (se 3 (by rfl) ⟨67475, by rfl⟩) R134951
theorem R196091 : Reach 196091 := rs (se 1 (by rfl) ⟨147068, by rfl⟩) R294137
theorem R163559 : Reach 163559 := rs (se 1 (by rfl) ⟨122669, by rfl⟩) R245339
theorem R261863 : Reach 261863 := rs (se 1 (by rfl) ⟨196397, by rfl⟩) R392795
theorem R130825 : Reach 130825 := rs (se 2 (by rfl) ⟨49059, by rfl⟩) R98119
theorem R229661 : Reach 229661 := rs (se 3 (by rfl) ⟨43061, by rfl⟩) R86123
theorem R196921 : Reach 196921 := rs (se 2 (by rfl) ⟨73845, by rfl⟩) R147691
theorem R295451 : Reach 295451 := rs (se 1 (by rfl) ⟨221588, by rfl⟩) R443177
theorem R131903 : Reach 131903 := rs (se 1 (by rfl) ⟨98927, by rfl⟩) R197855
theorem R230471 : Reach 230471 := rs (se 1 (by rfl) ⟨172853, by rfl⟩) R345707
theorem R853213 : Reach 853213 := rs (se 3 (by rfl) ⟨159977, by rfl⟩) R319955
theorem R165115 : Reach 165115 := rs (se 1 (by rfl) ⟨123836, by rfl⟩) R247673
theorem R230903 : Reach 230903 := rs (se 1 (by rfl) ⟨173177, by rfl⟩) R346355
theorem R198379 : Reach 198379 := rs (se 1 (by rfl) ⟨148784, by rfl⟩) R297569
theorem R67311 : Reach 67311 := rs (se 1 (by rfl) ⟨50483, by rfl⟩) R100967
theorem R67439 : Reach 67439 := rs (se 1 (by rfl) ⟨50579, by rfl⟩) R101159
theorem R1771469 : Reach 1771469 := rs (se 3 (by rfl) ⟨332150, by rfl⟩) R664301
theorem R67655 : Reach 67655 := rs (se 1 (by rfl) ⟨50741, by rfl⟩) R101483
theorem R67815 : Reach 67815 := rs (se 1 (by rfl) ⟨50861, by rfl⟩) R101723
theorem R67835 : Reach 67835 := rs (se 1 (by rfl) ⟨50876, by rfl⟩) R101753
theorem R67839 : Reach 67839 := rs (se 1 (by rfl) ⟨50879, by rfl⟩) R101759
theorem R723275 : Reach 723275 := rs (se 1 (by rfl) ⟨542456, by rfl⟩) R1084913
theorem R100745 : Reach 100745 := rs (se 2 (by rfl) ⟨37779, by rfl⟩) R75559
theorem R231983 : Reach 231983 := rs (se 1 (by rfl) ⟨173987, by rfl⟩) R347975
theorem R887375 : Reach 887375 := rs (se 1 (by rfl) ⟨665531, by rfl⟩) R1331063
theorem R68255 : Reach 68255 := rs (se 1 (by rfl) ⟨51191, by rfl⟩) R102383
theorem R68263 : Reach 68263 := rs (se 1 (by rfl) ⟨51197, by rfl⟩) R102395
theorem R68303 : Reach 68303 := rs (se 1 (by rfl) ⟨51227, by rfl⟩) R102455
theorem R68335 : Reach 68335 := rs (se 1 (by rfl) ⟨51251, by rfl⟩) R102503
theorem R68383 : Reach 68383 := rs (se 1 (by rfl) ⟨51287, by rfl⟩) R102575
theorem R68519 : Reach 68519 := rs (se 1 (by rfl) ⟨51389, by rfl⟩) R102779
theorem R68699 : Reach 68699 := rs (se 1 (by rfl) ⟨51524, by rfl⟩) R103049
theorem R167095 : Reach 167095 := rs (se 1 (by rfl) ⟨125321, by rfl⟩) R250643
theorem R953531 : Reach 953531 := rs (se 1 (by rfl) ⟨715148, by rfl⟩) R1430297
theorem R68839 : Reach 68839 := rs (se 1 (by rfl) ⟨51629, by rfl⟩) R103259
theorem R101855 : Reach 101855 := rs (se 1 (by rfl) ⟨76391, by rfl⟩) R152783
theorem R101915 : Reach 101915 := rs (se 1 (by rfl) ⟨76436, by rfl⟩) R152873
theorem R69147 : Reach 69147 := rs (se 1 (by rfl) ⟨51860, by rfl⟩) R103721
theorem R102047 : Reach 102047 := rs (se 1 (by rfl) ⟨76535, by rfl⟩) R153071
theorem R69279 : Reach 69279 := rs (se 1 (by rfl) ⟨51959, by rfl⟩) R103919
theorem R102311 : Reach 102311 := rs (se 1 (by rfl) ⟨76733, by rfl⟩) R153467
theorem R69543 : Reach 69543 := rs (se 1 (by rfl) ⟨52157, by rfl⟩) R104315
theorem R102335 : Reach 102335 := rs (se 1 (by rfl) ⟨76751, by rfl⟩) R153503
theorem R69567 : Reach 69567 := rs (se 1 (by rfl) ⟨52175, by rfl⟩) R104351
theorem R102491 : Reach 102491 := rs (se 1 (by rfl) ⟨76868, by rfl⟩) R153737
theorem R69723 : Reach 69723 := rs (se 1 (by rfl) ⟨52292, by rfl⟩) R104585
theorem R69823 : Reach 69823 := rs (se 1 (by rfl) ⟨52367, by rfl⟩) R104735
theorem R102635 : Reach 102635 := rs (se 1 (by rfl) ⟨76976, by rfl⟩) R153953
theorem R102695 : Reach 102695 := rs (se 1 (by rfl) ⟨77021, by rfl⟩) R154043
theorem R102959 : Reach 102959 := rs (se 1 (by rfl) ⟨77219, by rfl⟩) R154439
theorem R70191 : Reach 70191 := rs (se 1 (by rfl) ⟨52643, by rfl⟩) R105287
theorem R856673 : Reach 856673 := rs (se 2 (by rfl) ⟨321252, by rfl⟩) R642505
theorem R103163 : Reach 103163 := rs (se 1 (by rfl) ⟨77372, by rfl⟩) R154745
theorem R496381 : Reach 496381 := rs (se 3 (by rfl) ⟨93071, by rfl⟩) R186143
theorem R201467 : Reach 201467 := rs (se 1 (by rfl) ⟨151100, by rfl⟩) R302201
theorem R103535 : Reach 103535 := rs (se 1 (by rfl) ⟨77651, by rfl⟩) R155303
theorem R70767 : Reach 70767 := rs (se 1 (by rfl) ⟨53075, by rfl⟩) R106151
theorem R103607 : Reach 103607 := rs (se 1 (by rfl) ⟨77705, by rfl⟩) R155411
theorem R70847 : Reach 70847 := rs (se 1 (by rfl) ⟨53135, by rfl⟩) R106271
theorem R70991 : Reach 70991 := rs (se 1 (by rfl) ⟨53243, by rfl⟩) R106487
theorem R103847 : Reach 103847 := rs (se 1 (by rfl) ⟨77885, by rfl⟩) R155771
theorem R235007 : Reach 235007 := rs (se 1 (by rfl) ⟨176255, by rfl⟩) R352511
theorem R104027 : Reach 104027 := rs (se 1 (by rfl) ⟨78020, by rfl⟩) R156041
theorem R235385 : Reach 235385 := rs (se 2 (by rfl) ⟨88269, by rfl⟩) R176539
theorem R104783 : Reach 104783 := rs (se 1 (by rfl) ⟨78587, by rfl⟩) R157175
theorem R104807 : Reach 104807 := rs (se 1 (by rfl) ⟨78605, by rfl⟩) R157211
theorem R1284491 : Reach 1284491 := rs (se 1 (by rfl) ⟨963368, by rfl⟩) R1926737
theorem R104873 : Reach 104873 := rs (se 2 (by rfl) ⟨39327, by rfl⟩) R78655
theorem R170657 : Reach 170657 := rs (se 2 (by rfl) ⟨63996, by rfl⟩) R127993
theorem R105257 : Reach 105257 := rs (se 2 (by rfl) ⟨39471, by rfl⟩) R78943
theorem R957359 : Reach 957359 := rs (se 1 (by rfl) ⟨718019, by rfl⟩) R1436039
theorem R105467 : Reach 105467 := rs (se 1 (by rfl) ⟨79100, by rfl⟩) R158201
theorem R105503 : Reach 105503 := rs (se 1 (by rfl) ⟨79127, by rfl⟩) R158255
theorem R105527 : Reach 105527 := rs (se 1 (by rfl) ⟨79145, by rfl⟩) R158291
theorem R105647 : Reach 105647 := rs (se 1 (by rfl) ⟨79235, by rfl⟩) R158471
theorem R105791 : Reach 105791 := rs (se 1 (by rfl) ⟨79343, by rfl⟩) R158687
theorem R105935 : Reach 105935 := rs (se 1 (by rfl) ⟨79451, by rfl⟩) R158903
theorem R433619 : Reach 433619 := rs (se 1 (by rfl) ⟨325214, by rfl⟩) R650429
theorem R171497 : Reach 171497 := rs (se 2 (by rfl) ⟨64311, by rfl⟩) R128623
theorem R106319 : Reach 106319 := rs (se 1 (by rfl) ⟨79739, by rfl⟩) R159479
theorem R106367 : Reach 106367 := rs (se 1 (by rfl) ⟨79775, by rfl⟩) R159551
theorem R106439 : Reach 106439 := rs (se 1 (by rfl) ⟨79829, by rfl⟩) R159659
theorem R270323 : Reach 270323 := rs (se 1 (by rfl) ⟨202742, by rfl⟩) R405485
theorem R106679 : Reach 106679 := rs (se 1 (by rfl) ⟨80009, by rfl⟩) R160019
theorem R270803 : Reach 270803 := rs (se 1 (by rfl) ⟨203102, by rfl⟩) R406205
theorem R566023 : Reach 566023 := rs (se 1 (by rfl) ⟨424517, by rfl⟩) R849035
theorem R238463 : Reach 238463 := rs (se 1 (by rfl) ⟨178847, by rfl⟩) R357695
theorem R173279 : Reach 173279 := rs (se 1 (by rfl) ⟨129959, by rfl⟩) R259919
theorem R238895 : Reach 238895 := rs (se 1 (by rfl) ⟨179171, by rfl⟩) R358343
theorem R2762045 : Reach 2762045 := rs (se 3 (by rfl) ⟨517883, by rfl⟩) R1035767
theorem R272123 : Reach 272123 := rs (se 1 (by rfl) ⟨204092, by rfl⟩) R408185
theorem R239759 : Reach 239759 := rs (se 1 (by rfl) ⟨179819, by rfl⟩) R359639
theorem R174433 : Reach 174433 := rs (se 2 (by rfl) ⟨65412, by rfl⟩) R130825
theorem R109039 : Reach 109039 := rs (se 1 (by rfl) ⟨81779, by rfl⟩) R163559
theorem R174575 : Reach 174575 := rs (se 1 (by rfl) ⟨130931, by rfl⟩) R261863
theorem R77215 : Reach 77215 := rs (se 1 (by rfl) ⟨57911, by rfl⟩) R115823
theorem R77503 : Reach 77503 := rs (se 1 (by rfl) ⟨58127, by rfl⟩) R116255
theorem R3518153 : Reach 3518153 := rs (se 2 (by rfl) ⟨1319307, by rfl⟩) R2638615
theorem R175841 : Reach 175841 := rs (se 2 (by rfl) ⟨65940, by rfl⟩) R131881
theorem R864107 : Reach 864107 := rs (se 1 (by rfl) ⟨648080, by rfl⟩) R1296161
theorem R340199 : Reach 340199 := rs (se 1 (by rfl) ⟨255149, by rfl⟩) R510299
theorem R78079 : Reach 78079 := rs (se 1 (by rfl) ⟨58559, by rfl⟩) R117119
theorem R176383 : Reach 176383 := rs (se 1 (by rfl) ⟨132287, by rfl⟩) R264575
theorem R275357 : Reach 275357 := rs (se 3 (by rfl) ⟨51629, by rfl⟩) R103259
theorem R898037 : Reach 898037 := rs (se 5 (by rfl) ⟨42095, by rfl⟩) R84191
theorem R79231 : Reach 79231 := rs (se 1 (by rfl) ⟨59423, by rfl⟩) R118847
theorem R505439 : Reach 505439 := rs (se 1 (by rfl) ⟨379079, by rfl⟩) R758159
theorem R440255 : Reach 440255 := rs (se 1 (by rfl) ⟨330191, by rfl⟩) R660383
theorem R79807 : Reach 79807 := rs (se 1 (by rfl) ⟨59855, by rfl⟩) R119711
theorem R178463 : Reach 178463 := rs (se 1 (by rfl) ⟨133847, by rfl⟩) R267695
theorem R211835 : Reach 211835 := rs (se 1 (by rfl) ⟨158876, by rfl⟩) R317753
theorem R114223 : Reach 114223 := rs (se 1 (by rfl) ⟨85667, by rfl⟩) R171335
theorem R179759 : Reach 179759 := rs (se 1 (by rfl) ⟨134819, by rfl⟩) R269639
theorem R2801729 : Reach 2801729 := rs (se 2 (by rfl) ⟨1050648, by rfl⟩) R2101297
theorem R377303 : Reach 377303 := rs (se 1 (by rfl) ⟨282977, by rfl⟩) R565955
theorem R115175 : Reach 115175 := rs (se 1 (by rfl) ⟨86381, by rfl⟩) R172763
theorem R344573 : Reach 344573 := rs (se 3 (by rfl) ⟨64607, by rfl⟩) R129215
theorem R836477 : Reach 836477 := rs (se 3 (by rfl) ⟨156839, by rfl⟩) R313679
theorem R3066173 : Reach 3066173 := rs (se 3 (by rfl) ⟨574907, by rfl⟩) R1149815
theorem R5130701 : Reach 5130701 := rs (se 3 (by rfl) ⟨962006, by rfl⟩) R1924013
theorem R85303 : Reach 85303 := rs (se 1 (by rfl) ⟨63977, by rfl⟩) R127955
theorem R675373 : Reach 675373 := rs (se 3 (by rfl) ⟨126632, by rfl⟩) R253265
theorem R216719 : Reach 216719 := rs (se 1 (by rfl) ⟨162539, by rfl⟩) R325079
theorem R151271 : Reach 151271 := rs (se 1 (by rfl) ⟨113453, by rfl⟩) R226907
theorem R151433 : Reach 151433 := rs (se 2 (by rfl) ⟨56787, by rfl⟩) R113575
theorem R512243 : Reach 512243 := rs (se 1 (by rfl) ⟨384182, by rfl⟩) R768365
theorem R479825 : Reach 479825 := rs (se 2 (by rfl) ⟨179934, by rfl⟩) R359869
theorem R119407 : Reach 119407 := rs (se 1 (by rfl) ⟨89555, by rfl⟩) R179111
theorem R348947 : Reach 348947 := rs (se 1 (by rfl) ⟨261710, by rfl⟩) R523421
theorem R152531 : Reach 152531 := rs (se 1 (by rfl) ⟨114398, by rfl⟩) R228797
theorem R349595 : Reach 349595 := rs (se 1 (by rfl) ⟨262196, by rfl⟩) R524393
theorem R775655 : Reach 775655 := rs (se 1 (by rfl) ⟨581741, by rfl⟩) R1163483
theorem R87743 : Reach 87743 := rs (se 1 (by rfl) ⟨65807, by rfl⟩) R131615
theorem R218963 : Reach 218963 := rs (se 1 (by rfl) ⟨164222, by rfl⟩) R328445
theorem R153791 : Reach 153791 := rs (se 1 (by rfl) ⟨115343, by rfl⟩) R230687
theorem R547069 : Reach 547069 := rs (se 3 (by rfl) ⟨102575, by rfl⟩) R205151
theorem R416111 : Reach 416111 := rs (se 1 (by rfl) ⟨312083, by rfl⟩) R624167
theorem R88447 : Reach 88447 := rs (se 1 (by rfl) ⟨66335, by rfl⟩) R132671
theorem R612839 : Reach 612839 := rs (se 1 (by rfl) ⟨459629, by rfl⟩) R919259
theorem R678449 : Reach 678449 := rs (se 2 (by rfl) ⟨254418, by rfl⟩) R508837
theorem R219743 : Reach 219743 := rs (se 1 (by rfl) ⟨164807, by rfl⟩) R329615
theorem R1366739 : Reach 1366739 := rs (se 1 (by rfl) ⟨1025054, by rfl⟩) R2050109
theorem R1596125 : Reach 1596125 := rs (se 3 (by rfl) ⟨299273, by rfl⟩) R598547
theorem R154835 : Reach 154835 := rs (se 1 (by rfl) ⟨116126, by rfl⟩) R232253
theorem R154907 : Reach 154907 := rs (se 1 (by rfl) ⟨116180, by rfl⟩) R232361
theorem R384365 : Reach 384365 := rs (se 3 (by rfl) ⟨72068, by rfl⟩) R144137
theorem R679337 : Reach 679337 := rs (se 2 (by rfl) ⟨254751, by rfl⟩) R509503
theorem R155105 : Reach 155105 := rs (se 2 (by rfl) ⟨58164, by rfl⟩) R116329
theorem R876257 : Reach 876257 := rs (se 2 (by rfl) ⟨328596, by rfl⟩) R657193
theorem R89839 : Reach 89839 := rs (se 1 (by rfl) ⟨67379, by rfl⟩) R134759
theorem R155897 : Reach 155897 := rs (se 2 (by rfl) ⟨58461, by rfl⟩) R116923
theorem R287165 : Reach 287165 := rs (se 3 (by rfl) ⟨53843, by rfl⟩) R107687
theorem R1237493 : Reach 1237493 := rs (se 5 (by rfl) ⟨58007, by rfl⟩) R116015
theorem R156167 : Reach 156167 := rs (se 1 (by rfl) ⟨117125, by rfl⟩) R234251
theorem R156347 : Reach 156347 := rs (se 1 (by rfl) ⟨117260, by rfl⟩) R234521
theorem R222049 : Reach 222049 := rs (se 2 (by rfl) ⟨83268, by rfl⟩) R166537
theorem R222203 : Reach 222203 := rs (se 1 (by rfl) ⟨166652, by rfl⟩) R333305
theorem R156833 : Reach 156833 := rs (se 2 (by rfl) ⟨58812, by rfl⟩) R117625
theorem R157247 : Reach 157247 := rs (se 1 (by rfl) ⟨117935, by rfl⟩) R235871
theorem R157355 : Reach 157355 := rs (se 1 (by rfl) ⟨118016, by rfl⟩) R236033
theorem R354131 : Reach 354131 := rs (se 1 (by rfl) ⟨265598, by rfl⟩) R531197
theorem R157607 : Reach 157607 := rs (se 1 (by rfl) ⟨118205, by rfl⟩) R236411
theorem R157895 : Reach 157895 := rs (se 1 (by rfl) ⟨118421, by rfl⟩) R236843
theorem R387281 : Reach 387281 := rs (se 2 (by rfl) ⟨145230, by rfl⟩) R290461
theorem R1599745 : Reach 1599745 := rs (se 2 (by rfl) ⟨599904, by rfl⟩) R1199809
theorem R158075 : Reach 158075 := rs (se 1 (by rfl) ⟨118556, by rfl⟩) R237113
theorem R6547877 : Reach 6547877 := rs (se 4 (by rfl) ⟨613863, by rfl⟩) R1227727
theorem R158183 : Reach 158183 := rs (se 1 (by rfl) ⟨118637, by rfl⟩) R237275
theorem R354941 : Reach 354941 := rs (se 3 (by rfl) ⟨66551, by rfl⟩) R133103
theorem R158345 : Reach 158345 := rs (se 2 (by rfl) ⟨59379, by rfl⟩) R118759
theorem R158363 : Reach 158363 := rs (se 1 (by rfl) ⟨118772, by rfl⟩) R237545
theorem R3337037 : Reach 3337037 := rs (se 3 (by rfl) ⟨625694, by rfl⟩) R1251389
theorem R257033 : Reach 257033 := rs (se 2 (by rfl) ⟨96387, by rfl⟩) R192775
theorem R257215 : Reach 257215 := rs (se 1 (by rfl) ⟨192911, by rfl⟩) R385823
theorem R159335 : Reach 159335 := rs (se 1 (by rfl) ⟨119501, by rfl⟩) R239003
theorem R192863 : Reach 192863 := rs (se 1 (by rfl) ⟨144647, by rfl⟩) R289295
theorem R258491 : Reach 258491 := rs (se 1 (by rfl) ⟨193868, by rfl⟩) R387737
theorem R553661 : Reach 553661 := rs (se 3 (by rfl) ⟨103811, by rfl⟩) R207623
theorem R357857 : Reach 357857 := rs (se 2 (by rfl) ⟨134196, by rfl⟩) R268393
theorem R96223 : Reach 96223 := rs (se 1 (by rfl) ⟨72167, by rfl⟩) R144335
theorem R391837 : Reach 391837 := rs (se 3 (by rfl) ⟨73469, by rfl⟩) R146939
theorem R326753 : Reach 326753 := rs (se 2 (by rfl) ⟨122532, by rfl⟩) R245065
theorem R130727 : Reach 130727 := rs (se 1 (by rfl) ⟨98045, by rfl⟩) R196091
theorem R1867819 : Reach 1867819 := rs (se 1 (by rfl) ⟨1400864, by rfl⟩) R2801729
theorem R229715 : Reach 229715 := rs (se 1 (by rfl) ⟨172286, by rfl⟩) R344573
theorem R196967 : Reach 196967 := rs (se 1 (by rfl) ⟨147725, by rfl⟩) R295451
theorem R262561 : Reach 262561 := rs (se 2 (by rfl) ⟨98460, by rfl⟩) R196921
theorem R557651 : Reach 557651 := rs (se 1 (by rfl) ⟨418238, by rfl⟩) R836477
theorem R754697 : Reach 754697 := rs (se 2 (by rfl) ⟨283011, by rfl⟩) R566023
theorem R296065 : Reach 296065 := rs (se 2 (by rfl) ⟨111024, by rfl⟩) R222049
theorem R1180979 : Reach 1180979 := rs (se 1 (by rfl) ⟨885734, by rfl⟩) R1771469
theorem R67163 : Reach 67163 := rs (se 1 (by rfl) ⟨50372, by rfl⟩) R100745
theorem R591583 : Reach 591583 := rs (se 1 (by rfl) ⟨443687, by rfl⟩) R887375
theorem R264505 : Reach 264505 := rs (se 2 (by rfl) ⟨99189, by rfl⟩) R198379
theorem R67903 : Reach 67903 := rs (se 1 (by rfl) ⟨50927, by rfl⟩) R101855
theorem R67943 : Reach 67943 := rs (se 1 (by rfl) ⟨50957, by rfl⟩) R101915
theorem R68031 : Reach 68031 := rs (se 1 (by rfl) ⟨51023, by rfl⟩) R102047
theorem R100847 : Reach 100847 := rs (se 1 (by rfl) ⟨75635, by rfl⟩) R151271
theorem R100955 : Reach 100955 := rs (se 1 (by rfl) ⟨75716, by rfl⟩) R151433
theorem R68207 : Reach 68207 := rs (se 1 (by rfl) ⟨51155, by rfl⟩) R102311
theorem R68223 : Reach 68223 := rs (se 1 (by rfl) ⟨51167, by rfl⟩) R102335
theorem R592541 : Reach 592541 := rs (se 3 (by rfl) ⟨111101, by rfl⟩) R222203
theorem R68327 : Reach 68327 := rs (se 1 (by rfl) ⟨51245, by rfl⟩) R102491
theorem R68423 : Reach 68423 := rs (se 1 (by rfl) ⟨51317, by rfl⟩) R102635
theorem R68463 : Reach 68463 := rs (se 1 (by rfl) ⟨51347, by rfl⟩) R102695
theorem R2132993 : Reach 2132993 := rs (se 2 (by rfl) ⟨799872, by rfl⟩) R1599745
theorem R68639 : Reach 68639 := rs (se 1 (by rfl) ⟨51479, by rfl⟩) R102959
theorem R232577 : Reach 232577 := rs (se 2 (by rfl) ⟨87216, by rfl⟩) R174433
theorem R68775 : Reach 68775 := rs (se 1 (by rfl) ⟨51581, by rfl⟩) R103163
theorem R134311 : Reach 134311 := rs (se 1 (by rfl) ⟨100733, by rfl⟩) R201467
theorem R232631 : Reach 232631 := rs (se 1 (by rfl) ⟨174473, by rfl⟩) R348947
theorem R101687 : Reach 101687 := rs (se 1 (by rfl) ⟨76265, by rfl⟩) R152531
theorem R69023 : Reach 69023 := rs (se 1 (by rfl) ⟨51767, by rfl⟩) R103535
theorem R69071 : Reach 69071 := rs (se 1 (by rfl) ⟨51803, by rfl⟩) R103607
theorem R233063 : Reach 233063 := rs (se 1 (by rfl) ⟨174797, by rfl⟩) R349595
theorem R69231 : Reach 69231 := rs (se 1 (by rfl) ⟨51923, by rfl⟩) R103847
theorem R69351 : Reach 69351 := rs (se 1 (by rfl) ⟨52013, by rfl⟩) R104027
theorem R102527 : Reach 102527 := rs (se 1 (by rfl) ⟨76895, by rfl⟩) R153791
theorem R69855 : Reach 69855 := rs (se 1 (by rfl) ⟨52391, by rfl⟩) R104783
theorem R69871 : Reach 69871 := rs (se 1 (by rfl) ⟨52403, by rfl⟩) R104807
theorem R856327 : Reach 856327 := rs (se 1 (by rfl) ⟨642245, by rfl⟩) R1284491
theorem R69915 : Reach 69915 := rs (se 1 (by rfl) ⟨52436, by rfl⟩) R104873
theorem R233981 : Reach 233981 := rs (se 3 (by rfl) ⟨43871, by rfl⟩) R87743
theorem R70171 : Reach 70171 := rs (se 1 (by rfl) ⟨52628, by rfl⟩) R105257
theorem R102953 : Reach 102953 := rs (se 2 (by rfl) ⟨38607, by rfl⟩) R77215
theorem R70311 : Reach 70311 := rs (se 1 (by rfl) ⟨52733, by rfl⟩) R105467
theorem R70335 : Reach 70335 := rs (se 1 (by rfl) ⟨52751, by rfl⟩) R105503
theorem R70351 : Reach 70351 := rs (se 1 (by rfl) ⟨52763, by rfl⟩) R105527
theorem R70431 : Reach 70431 := rs (se 1 (by rfl) ⟨52823, by rfl⟩) R105647
theorem R103223 : Reach 103223 := rs (se 1 (by rfl) ⟨77417, by rfl⟩) R154835
theorem R103271 : Reach 103271 := rs (se 1 (by rfl) ⟨77453, by rfl⟩) R154907
theorem R70527 : Reach 70527 := rs (se 1 (by rfl) ⟨52895, by rfl⟩) R105791
theorem R103337 : Reach 103337 := rs (se 2 (by rfl) ⟨38751, by rfl⟩) R77503
theorem R70623 : Reach 70623 := rs (se 1 (by rfl) ⟨52967, by rfl⟩) R105935
theorem R103403 : Reach 103403 := rs (se 1 (by rfl) ⟨77552, by rfl⟩) R155105
theorem R70879 : Reach 70879 := rs (se 1 (by rfl) ⟨53159, by rfl⟩) R106319
theorem R70911 : Reach 70911 := rs (se 1 (by rfl) ⟨53183, by rfl⟩) R106367
theorem R70959 : Reach 70959 := rs (se 1 (by rfl) ⟨53219, by rfl⟩) R106439
theorem R71119 : Reach 71119 := rs (se 1 (by rfl) ⟨53339, by rfl⟩) R106679
theorem R103931 : Reach 103931 := rs (se 1 (by rfl) ⟨77948, by rfl⟩) R155897
theorem R824995 : Reach 824995 := rs (se 1 (by rfl) ⟨618746, by rfl⟩) R1237493
theorem R104105 : Reach 104105 := rs (se 2 (by rfl) ⟨39039, by rfl⟩) R78079
theorem R104111 : Reach 104111 := rs (se 1 (by rfl) ⟨78083, by rfl⟩) R156167
theorem R104231 : Reach 104231 := rs (se 1 (by rfl) ⟨78173, by rfl⟩) R156347
theorem R104555 : Reach 104555 := rs (se 1 (by rfl) ⟨78416, by rfl⟩) R156833
theorem R1841363 : Reach 1841363 := rs (se 1 (by rfl) ⟨1381022, by rfl⟩) R2762045
theorem R661841 : Reach 661841 := rs (se 2 (by rfl) ⟨248190, by rfl⟩) R496381
theorem R104831 : Reach 104831 := rs (se 1 (by rfl) ⟨78623, by rfl⟩) R157247
theorem R104903 : Reach 104903 := rs (se 1 (by rfl) ⟨78677, by rfl⟩) R157355
theorem R236087 : Reach 236087 := rs (se 1 (by rfl) ⟨177065, by rfl⟩) R354131
theorem R105071 : Reach 105071 := rs (se 1 (by rfl) ⟨78803, by rfl⟩) R157607
theorem R105263 : Reach 105263 := rs (se 1 (by rfl) ⟨78947, by rfl⟩) R157895
theorem R105383 : Reach 105383 := rs (se 1 (by rfl) ⟨79037, by rfl⟩) R158075
theorem R4365251 : Reach 4365251 := rs (se 1 (by rfl) ⟨3273938, by rfl⟩) R6547877
theorem R105455 : Reach 105455 := rs (se 1 (by rfl) ⟨79091, by rfl⟩) R158183
theorem R236627 : Reach 236627 := rs (se 1 (by rfl) ⟨177470, by rfl⟩) R354941
theorem R105563 : Reach 105563 := rs (se 1 (by rfl) ⟨79172, by rfl⟩) R158345
theorem R105575 : Reach 105575 := rs (se 1 (by rfl) ⟨79181, by rfl⟩) R158363
theorem R105641 : Reach 105641 := rs (se 2 (by rfl) ⟨39615, by rfl⟩) R79231
theorem R171355 : Reach 171355 := rs (se 1 (by rfl) ⟨128516, by rfl⟩) R257033
theorem R106223 : Reach 106223 := rs (se 1 (by rfl) ⟨79667, by rfl⟩) R159335
theorem R106409 : Reach 106409 := rs (se 2 (by rfl) ⟨39903, by rfl⟩) R79807
theorem R172327 : Reach 172327 := rs (se 1 (by rfl) ⟨129245, by rfl⟩) R258491
theorem R729425 : Reach 729425 := rs (se 2 (by rfl) ⟨273534, by rfl⟩) R547069
theorem R369107 : Reach 369107 := rs (se 1 (by rfl) ⟨276830, by rfl⟩) R553661
theorem R598691 : Reach 598691 := rs (se 1 (by rfl) ⟨449018, by rfl⟩) R898037
theorem R238571 : Reach 238571 := rs (se 1 (by rfl) ⟨178928, by rfl⟩) R357857
theorem R336959 : Reach 336959 := rs (se 1 (by rfl) ⟨252719, by rfl⟩) R505439
theorem R141223 : Reach 141223 := rs (se 1 (by rfl) ⟨105917, by rfl⟩) R211835
theorem R76783 : Reach 76783 := rs (se 1 (by rfl) ⟨57587, by rfl⟩) R115175
theorem R2044115 : Reach 2044115 := rs (se 1 (by rfl) ⟨1533086, by rfl⟩) R3066173
theorem R3420467 : Reach 3420467 := rs (se 1 (by rfl) ⟨2565350, by rfl⟩) R5130701
theorem R635687 : Reach 635687 := rs (se 1 (by rfl) ⟨476765, by rfl⟩) R953531
theorem R734285 : Reach 734285 := rs (se 3 (by rfl) ⟨137678, by rfl⟩) R275357
theorem R144479 : Reach 144479 := rs (se 1 (by rfl) ⟨108359, by rfl⟩) R216719
theorem R341495 : Reach 341495 := rs (se 1 (by rfl) ⟨256121, by rfl⟩) R512243
theorem R571115 : Reach 571115 := rs (se 1 (by rfl) ⟨428336, by rfl⟩) R856673
theorem R145385 : Reach 145385 := rs (se 2 (by rfl) ⟨54519, by rfl⟩) R109039
theorem R145975 : Reach 145975 := rs (se 1 (by rfl) ⟨109481, by rfl⟩) R218963
theorem R342953 : Reach 342953 := rs (se 2 (by rfl) ⟨128607, by rfl⟩) R257215
theorem R408559 : Reach 408559 := rs (se 1 (by rfl) ⟨306419, by rfl⟩) R612839
theorem R146495 : Reach 146495 := rs (se 1 (by rfl) ⟨109871, by rfl⟩) R219743
theorem R113737 : Reach 113737 := rs (se 2 (by rfl) ⟨42651, by rfl⟩) R85303
theorem R113771 : Reach 113771 := rs (se 1 (by rfl) ⟨85328, by rfl⟩) R170657
theorem R1064083 : Reach 1064083 := rs (se 1 (by rfl) ⟨798062, by rfl⟩) R1596125
theorem R638239 : Reach 638239 := rs (se 1 (by rfl) ⟨478679, by rfl⟩) R957359
theorem R900497 : Reach 900497 := rs (se 2 (by rfl) ⟨337686, by rfl⟩) R675373
theorem R114331 : Reach 114331 := rs (se 1 (by rfl) ⟨85748, by rfl⟩) R171497
theorem R180215 : Reach 180215 := rs (se 1 (by rfl) ⟨135161, by rfl⟩) R270323
theorem R180535 : Reach 180535 := rs (se 1 (by rfl) ⟨135401, by rfl⟩) R270803
theorem R115519 : Reach 115519 := rs (se 1 (by rfl) ⟨86639, by rfl⟩) R173279
theorem R181415 : Reach 181415 := rs (se 1 (by rfl) ⟨136061, by rfl⟩) R272123
theorem R116383 : Reach 116383 := rs (se 1 (by rfl) ⟨87287, by rfl⟩) R174575
theorem R2345435 : Reach 2345435 := rs (se 1 (by rfl) ⟨1759076, by rfl⟩) R3518153
theorem R117227 : Reach 117227 := rs (se 1 (by rfl) ⟨87920, by rfl⟩) R175841
theorem R576071 : Reach 576071 := rs (se 1 (by rfl) ⟨432053, by rfl⟩) R864107
theorem R117929 : Reach 117929 := rs (se 2 (by rfl) ⟨44223, by rfl⟩) R88447
theorem R118975 : Reach 118975 := rs (se 1 (by rfl) ⟨89231, by rfl⟩) R178463
theorem R152297 : Reach 152297 := rs (se 2 (by rfl) ⟨57111, by rfl⟩) R114223
theorem R217835 : Reach 217835 := rs (se 1 (by rfl) ⟨163376, by rfl⟩) R326753
theorem R119785 : Reach 119785 := rs (se 2 (by rfl) ⟨44919, by rfl⟩) R89839
theorem R119839 : Reach 119839 := rs (se 1 (by rfl) ⟨89879, by rfl⟩) R179759
theorem R87151 : Reach 87151 := rs (se 1 (by rfl) ⟨65363, by rfl⟩) R130727
theorem R153107 : Reach 153107 := rs (se 1 (by rfl) ⟨114830, by rfl⟩) R229661
theorem R87935 : Reach 87935 := rs (se 1 (by rfl) ⟨65951, by rfl⟩) R131903
theorem R153647 : Reach 153647 := rs (se 1 (by rfl) ⟨115235, by rfl⟩) R230471
theorem R153935 : Reach 153935 := rs (se 1 (by rfl) ⟨115451, by rfl⟩) R230903
theorem R1006141 : Reach 1006141 := rs (se 3 (by rfl) ⟨188651, by rfl⟩) R377303
theorem R940709 : Reach 940709 := rs (se 4 (by rfl) ⟨88191, by rfl⟩) R176383
theorem R482183 : Reach 482183 := rs (se 1 (by rfl) ⟨361637, by rfl⟩) R723275
theorem R1137617 : Reach 1137617 := rs (se 2 (by rfl) ⟨426606, by rfl⟩) R853213
theorem R220153 : Reach 220153 := rs (se 2 (by rfl) ⟨82557, by rfl⟩) R165115
theorem R154655 : Reach 154655 := rs (se 1 (by rfl) ⟨115991, by rfl⟩) R231983
theorem R319883 : Reach 319883 := rs (se 1 (by rfl) ⟨239912, by rfl⟩) R479825
theorem R517103 : Reach 517103 := rs (se 1 (by rfl) ⟨387827, by rfl⟩) R775655
theorem R156671 : Reach 156671 := rs (se 1 (by rfl) ⟨117503, by rfl⟩) R235007
theorem R156923 : Reach 156923 := rs (se 1 (by rfl) ⟨117692, by rfl⟩) R235385
theorem R222793 : Reach 222793 := rs (se 2 (by rfl) ⟨83547, by rfl⟩) R167095
theorem R452299 : Reach 452299 := rs (se 1 (by rfl) ⟨339224, by rfl⟩) R678449
theorem R911159 : Reach 911159 := rs (se 1 (by rfl) ⟨683369, by rfl⟩) R1366739
theorem R256243 : Reach 256243 := rs (se 1 (by rfl) ⟨192182, by rfl⟩) R384365
theorem R452891 : Reach 452891 := rs (se 1 (by rfl) ⟨339668, by rfl⟩) R679337
theorem R289079 : Reach 289079 := rs (se 1 (by rfl) ⟨216809, by rfl⟩) R433619
theorem R584171 : Reach 584171 := rs (se 1 (by rfl) ⟨438128, by rfl⟩) R876257
theorem R191443 : Reach 191443 := rs (se 1 (by rfl) ⟨143582, by rfl⟩) R287165
theorem R158975 : Reach 158975 := rs (se 1 (by rfl) ⟨119231, by rfl⟩) R238463
theorem R159209 : Reach 159209 := rs (se 2 (by rfl) ⟨59703, by rfl⟩) R119407
theorem R159263 : Reach 159263 := rs (se 1 (by rfl) ⟨119447, by rfl⟩) R238895
theorem R1109629 : Reach 1109629 := rs (se 3 (by rfl) ⟨208055, by rfl⟩) R416111
theorem R159839 : Reach 159839 := rs (se 1 (by rfl) ⟨119879, by rfl⟩) R239759
theorem R258187 : Reach 258187 := rs (se 1 (by rfl) ⟨193640, by rfl⟩) R387281
theorem R2224691 : Reach 2224691 := rs (se 1 (by rfl) ⟨1668518, by rfl⟩) R3337037
theorem R128297 : Reach 128297 := rs (se 2 (by rfl) ⟨48111, by rfl⟩) R96223
theorem R226799 : Reach 226799 := rs (se 1 (by rfl) ⟨170099, by rfl⟩) R340199
theorem R128575 : Reach 128575 := rs (se 1 (by rfl) ⟨96431, by rfl⟩) R192863
theorem R522449 : Reach 522449 := rs (se 2 (by rfl) ⟨195918, by rfl⟩) R391837
theorem R293503 : Reach 293503 := rs (se 1 (by rfl) ⟨220127, by rfl⟩) R440255
theorem R2490425 : Reach 2490425 := rs (se 2 (by rfl) ⟨933909, by rfl⟩) R1867819
theorem R131311 : Reach 131311 := rs (se 1 (by rfl) ⟨98483, by rfl⟩) R196967
theorem R229769 : Reach 229769 := rs (se 2 (by rfl) ⟨86163, by rfl⟩) R172327
theorem R787319 : Reach 787319 := rs (se 1 (by rfl) ⟨590489, by rfl⟩) R1180979
theorem R853021 : Reach 853021 := rs (se 3 (by rfl) ⟨159941, by rfl⟩) R319883
theorem R394753 : Reach 394753 := rs (se 2 (by rfl) ⟨148032, by rfl⟩) R296065
theorem R67231 : Reach 67231 := rs (se 1 (by rfl) ⟨50423, by rfl⟩) R100847
theorem R67303 : Reach 67303 := rs (se 1 (by rfl) ⟨50477, by rfl⟩) R100955
theorem R395027 : Reach 395027 := rs (se 1 (by rfl) ⟨296270, by rfl⟩) R592541
theorem R67791 : Reach 67791 := rs (se 1 (by rfl) ⟨50843, by rfl⟩) R101687
theorem R788777 : Reach 788777 := rs (se 2 (by rfl) ⟨295791, by rfl⟩) R591583
theorem R68351 : Reach 68351 := rs (se 1 (by rfl) ⟨51263, by rfl⟩) R102527
theorem R68635 : Reach 68635 := rs (se 1 (by rfl) ⟨51476, by rfl⟩) R102953
theorem R101531 : Reach 101531 := rs (se 1 (by rfl) ⟨76148, by rfl⟩) R152297
theorem R68815 : Reach 68815 := rs (se 1 (by rfl) ⟨51611, by rfl⟩) R103223
theorem R68847 : Reach 68847 := rs (se 1 (by rfl) ⟨51635, by rfl⟩) R103271
theorem R68891 : Reach 68891 := rs (se 1 (by rfl) ⟨51668, by rfl⟩) R103337
theorem R68935 : Reach 68935 := rs (se 1 (by rfl) ⟨51701, by rfl⟩) R103403
theorem R69287 : Reach 69287 := rs (se 1 (by rfl) ⟨51965, by rfl⟩) R103931
theorem R102071 : Reach 102071 := rs (se 1 (by rfl) ⟨76553, by rfl⟩) R153107
theorem R69403 : Reach 69403 := rs (se 1 (by rfl) ⟨52052, by rfl⟩) R104105
theorem R69407 : Reach 69407 := rs (se 1 (by rfl) ⟨52055, by rfl⟩) R104111
theorem R69487 : Reach 69487 := rs (se 1 (by rfl) ⟨52115, by rfl⟩) R104231
theorem R102377 : Reach 102377 := rs (se 2 (by rfl) ⟨38391, by rfl⟩) R76783
theorem R102431 : Reach 102431 := rs (se 1 (by rfl) ⟨76823, by rfl⟩) R153647
theorem R69703 : Reach 69703 := rs (se 1 (by rfl) ⟨52277, by rfl⟩) R104555
theorem R102623 : Reach 102623 := rs (se 1 (by rfl) ⟨76967, by rfl⟩) R153935
theorem R69887 : Reach 69887 := rs (se 1 (by rfl) ⟨52415, by rfl⟩) R104831
theorem R69935 : Reach 69935 := rs (se 1 (by rfl) ⟨52451, by rfl⟩) R104903
theorem R70047 : Reach 70047 := rs (se 1 (by rfl) ⟨52535, by rfl⟩) R105071
theorem R627139 : Reach 627139 := rs (se 1 (by rfl) ⟨470354, by rfl⟩) R940709
theorem R70175 : Reach 70175 := rs (se 1 (by rfl) ⟨52631, by rfl⟩) R105263
theorem R70255 : Reach 70255 := rs (se 1 (by rfl) ⟨52691, by rfl⟩) R105383
theorem R758411 : Reach 758411 := rs (se 1 (by rfl) ⟨568808, by rfl⟩) R1137617
theorem R70303 : Reach 70303 := rs (se 1 (by rfl) ⟨52727, by rfl⟩) R105455
theorem R103103 : Reach 103103 := rs (se 1 (by rfl) ⟨77327, by rfl⟩) R154655
theorem R70375 : Reach 70375 := rs (se 1 (by rfl) ⟨52781, by rfl⟩) R105563
theorem R70383 : Reach 70383 := rs (se 1 (by rfl) ⟨52787, by rfl⟩) R105575
theorem R70427 : Reach 70427 := rs (se 1 (by rfl) ⟨52820, by rfl⟩) R105641
theorem R1479505 : Reach 1479505 := rs (se 2 (by rfl) ⟨554814, by rfl⟩) R1109629
theorem R70815 : Reach 70815 := rs (se 1 (by rfl) ⟨53111, by rfl⟩) R106223
theorem R70939 : Reach 70939 := rs (se 1 (by rfl) ⟨53204, by rfl⟩) R106409
theorem R399127 : Reach 399127 := rs (se 1 (by rfl) ⟨299345, by rfl⟩) R598691
theorem R104447 : Reach 104447 := rs (se 1 (by rfl) ⟨78335, by rfl⟩) R156671
theorem R104615 : Reach 104615 := rs (se 1 (by rfl) ⟨78461, by rfl⟩) R156923
theorem R301927 : Reach 301927 := rs (se 1 (by rfl) ⟨226445, by rfl⟩) R452891
theorem R171433 : Reach 171433 := rs (se 2 (by rfl) ⟨64287, by rfl⟩) R128575
theorem R105983 : Reach 105983 := rs (se 1 (by rfl) ⟨79487, by rfl⟩) R158975
theorem R106139 : Reach 106139 := rs (se 1 (by rfl) ⟨79604, by rfl⟩) R159209
theorem R106175 : Reach 106175 := rs (se 1 (by rfl) ⟨79631, by rfl⟩) R159263
theorem R106559 : Reach 106559 := rs (se 1 (by rfl) ⟨79919, by rfl⟩) R159839
theorem R1483127 : Reach 1483127 := rs (se 1 (by rfl) ⟨1112345, by rfl⟩) R2224691
theorem R1188229 : Reach 1188229 := rs (se 4 (by rfl) ⟨111396, by rfl⟩) R222793
theorem R1418777 : Reach 1418777 := rs (se 2 (by rfl) ⟨532041, by rfl⟩) R1064083
theorem R75847 : Reach 75847 := rs (se 1 (by rfl) ⟨56885, by rfl⟩) R113771
theorem R600331 : Reach 600331 := rs (se 1 (by rfl) ⟨450248, by rfl⟩) R900497
theorem R240713 : Reach 240713 := rs (se 2 (by rfl) ⟨90267, by rfl⟩) R180535
theorem R503131 : Reach 503131 := rs (se 1 (by rfl) ⟨377348, by rfl⟩) R754697
theorem R1945133 : Reach 1945133 := rs (se 3 (by rfl) ⟨364712, by rfl⟩) R729425
theorem R1487069 : Reach 1487069 := rs (se 3 (by rfl) ⟨278825, by rfl⟩) R557651
theorem R78151 : Reach 78151 := rs (se 1 (by rfl) ⟨58613, by rfl⟩) R117227
theorem R1421995 : Reach 1421995 := rs (se 1 (by rfl) ⟨1066496, by rfl⟩) R2132993
theorem R78619 : Reach 78619 := rs (se 1 (by rfl) ⟨58964, by rfl⟩) R117929
theorem R603065 : Reach 603065 := rs (se 2 (by rfl) ⟨226149, by rfl⟩) R452299
theorem R341657 : Reach 341657 := rs (se 2 (by rfl) ⟨128121, by rfl⟩) R256243
theorem R145223 : Reach 145223 := rs (se 1 (by rfl) ⟨108917, by rfl⟩) R217835
theorem R1227575 : Reach 1227575 := rs (se 1 (by rfl) ⟨920681, by rfl⟩) R1841363
theorem R179081 : Reach 179081 := rs (se 2 (by rfl) ⟨67155, by rfl⟩) R134311
theorem R441227 : Reach 441227 := rs (se 1 (by rfl) ⟨330920, by rfl⟩) R661841
theorem R344249 : Reach 344249 := rs (se 2 (by rfl) ⟨129093, by rfl⟩) R258187
theorem R246071 : Reach 246071 := rs (se 1 (by rfl) ⟨184553, by rfl⟩) R369107
theorem R344735 : Reach 344735 := rs (se 1 (by rfl) ⟨258551, by rfl⟩) R517103
theorem R607439 : Reach 607439 := rs (se 1 (by rfl) ⟨455579, by rfl⟩) R911159
theorem R116201 : Reach 116201 := rs (se 2 (by rfl) ⟨43575, by rfl⟩) R87151
theorem R280189 : Reach 280189 := rs (se 3 (by rfl) ⟨52535, by rfl⟩) R105071
theorem R1099993 : Reach 1099993 := rs (se 2 (by rfl) ⟨412497, by rfl⟩) R824995
theorem R1362743 : Reach 1362743 := rs (se 1 (by rfl) ⟨1022057, by rfl⟩) R2044115
theorem R2280311 : Reach 2280311 := rs (se 1 (by rfl) ⟨1710233, by rfl⟩) R3420467
theorem R85531 : Reach 85531 := rs (se 1 (by rfl) ⟨64148, by rfl⟩) R128297
theorem R151199 : Reach 151199 := rs (se 1 (by rfl) ⟨113399, by rfl⟩) R226799
theorem R380743 : Reach 380743 := rs (se 1 (by rfl) ⟨285557, by rfl⟩) R571115
theorem R544745 : Reach 544745 := rs (se 2 (by rfl) ⟨204279, by rfl⟩) R408559
theorem R937973 : Reach 937973 := rs (se 5 (by rfl) ⟨43967, by rfl⟩) R87935
theorem R151649 : Reach 151649 := rs (se 2 (by rfl) ⟨56868, by rfl⟩) R113737
theorem R348299 : Reach 348299 := rs (se 1 (by rfl) ⟨261224, by rfl⟩) R522449
theorem R152441 : Reach 152441 := rs (se 2 (by rfl) ⟨57165, by rfl⟩) R114331
theorem R120143 : Reach 120143 := rs (se 1 (by rfl) ⟨90107, by rfl⟩) R180215
theorem R153143 : Reach 153143 := rs (se 1 (by rfl) ⟨114857, by rfl⟩) R229715
theorem R350081 : Reach 350081 := rs (se 2 (by rfl) ⟨131280, by rfl⟩) R262561
theorem R120943 : Reach 120943 := rs (se 1 (by rfl) ⟨90707, by rfl⟩) R181415
theorem R154025 : Reach 154025 := rs (se 2 (by rfl) ⟨57759, by rfl⟩) R115519
theorem R1563623 : Reach 1563623 := rs (se 1 (by rfl) ⟨1172717, by rfl⟩) R2345435
theorem R384047 : Reach 384047 := rs (se 1 (by rfl) ⟨288035, by rfl⟩) R576071
theorem R155051 : Reach 155051 := rs (se 1 (by rfl) ⟨116288, by rfl⟩) R232577
theorem R155087 : Reach 155087 := rs (se 1 (by rfl) ⟨116315, by rfl⟩) R232631
theorem R155177 : Reach 155177 := rs (se 2 (by rfl) ⟨58191, by rfl⟩) R116383
theorem R155375 : Reach 155375 := rs (se 1 (by rfl) ⟨116531, by rfl⟩) R233063
theorem R188297 : Reach 188297 := rs (se 2 (by rfl) ⟨70611, by rfl⟩) R141223
theorem R155987 : Reach 155987 := rs (se 1 (by rfl) ⟨116990, by rfl⟩) R233981
theorem R352673 : Reach 352673 := rs (se 2 (by rfl) ⟨132252, by rfl⟩) R264505
theorem R255257 : Reach 255257 := rs (se 2 (by rfl) ⟨95721, by rfl⟩) R191443
theorem R157391 : Reach 157391 := rs (se 1 (by rfl) ⟨118043, by rfl⟩) R236087
theorem R321455 : Reach 321455 := rs (se 1 (by rfl) ⟨241091, by rfl⟩) R482183
theorem R2910167 : Reach 2910167 := rs (se 1 (by rfl) ⟨2182625, by rfl⟩) R4365251
theorem R157751 : Reach 157751 := rs (se 1 (by rfl) ⟨118313, by rfl⟩) R236627
theorem R158633 : Reach 158633 := rs (se 2 (by rfl) ⟨59487, by rfl⟩) R118975
theorem R1141769 : Reach 1141769 := rs (se 2 (by rfl) ⟨428163, by rfl⟩) R856327
theorem R159047 : Reach 159047 := rs (se 1 (by rfl) ⟨119285, by rfl⟩) R238571
theorem R224639 : Reach 224639 := rs (se 1 (by rfl) ⟨168479, by rfl⟩) R336959
theorem R159713 : Reach 159713 := rs (se 2 (by rfl) ⟨59892, by rfl⟩) R119785
theorem R159785 : Reach 159785 := rs (se 2 (by rfl) ⟨59919, by rfl⟩) R119839
theorem R192719 : Reach 192719 := rs (se 1 (by rfl) ⟨144539, by rfl⟩) R289079
theorem R389447 : Reach 389447 := rs (se 1 (by rfl) ⟨292085, by rfl⟩) R584171
theorem R390653 : Reach 390653 := rs (se 3 (by rfl) ⟨73247, by rfl⟩) R146495
theorem R423791 : Reach 423791 := rs (se 1 (by rfl) ⟨317843, by rfl⟩) R635687
theorem R489523 : Reach 489523 := rs (se 1 (by rfl) ⟨367142, by rfl⟩) R734285
theorem R96319 : Reach 96319 := rs (se 1 (by rfl) ⟨72239, by rfl⟩) R144479
theorem R194633 : Reach 194633 := rs (se 2 (by rfl) ⟨72987, by rfl⟩) R145975
theorem R1341521 : Reach 1341521 := rs (se 2 (by rfl) ⟨503070, by rfl⟩) R1006141
theorem R391337 : Reach 391337 := rs (se 2 (by rfl) ⟨146751, by rfl⟩) R293503
theorem R227663 : Reach 227663 := rs (se 1 (by rfl) ⟨170747, by rfl⟩) R341495
theorem R96923 : Reach 96923 := rs (se 1 (by rfl) ⟨72692, by rfl⟩) R145385
theorem R293537 : Reach 293537 := rs (se 2 (by rfl) ⟨110076, by rfl⟩) R220153
theorem R850985 : Reach 850985 := rs (se 2 (by rfl) ⟨319119, by rfl⟩) R638239
theorem R228473 : Reach 228473 := rs (se 2 (by rfl) ⟨85677, by rfl⟩) R171355
theorem R228635 : Reach 228635 := rs (se 1 (by rfl) ⟨171476, by rfl⟩) R342953
theorem R229499 : Reach 229499 := rs (se 1 (by rfl) ⟨172124, by rfl⟩) R344249
theorem R164047 : Reach 164047 := rs (se 1 (by rfl) ⟨123035, by rfl⟩) R246071
theorem R229823 : Reach 229823 := rs (se 1 (by rfl) ⟨172367, by rfl⟩) R344735
theorem R524879 : Reach 524879 := rs (se 1 (by rfl) ⟨393659, by rfl⟩) R787319
theorem R263351 : Reach 263351 := rs (se 1 (by rfl) ⟨197513, by rfl⟩) R395027
theorem R525851 : Reach 525851 := rs (se 1 (by rfl) ⟨394388, by rfl⟩) R788777
theorem R526337 : Reach 526337 := rs (se 2 (by rfl) ⟨197376, by rfl⟩) R394753
theorem R67687 : Reach 67687 := rs (se 1 (by rfl) ⟨50765, by rfl⟩) R101531
theorem R100799 : Reach 100799 := rs (se 1 (by rfl) ⟨75599, by rfl⟩) R151199
theorem R68047 : Reach 68047 := rs (se 1 (by rfl) ⟨51035, by rfl⟩) R102071
theorem R363163 : Reach 363163 := rs (se 1 (by rfl) ⟨272372, by rfl⟩) R544745
theorem R68251 : Reach 68251 := rs (se 1 (by rfl) ⟨51188, by rfl⟩) R102377
theorem R625315 : Reach 625315 := rs (se 1 (by rfl) ⟨468986, by rfl⟩) R937973
theorem R68287 : Reach 68287 := rs (se 1 (by rfl) ⟨51215, by rfl⟩) R102431
theorem R101099 : Reach 101099 := rs (se 1 (by rfl) ⟨75824, by rfl⟩) R151649
theorem R232199 : Reach 232199 := rs (se 1 (by rfl) ⟨174149, by rfl⟩) R348299
theorem R101129 : Reach 101129 := rs (se 2 (by rfl) ⟨37923, by rfl⟩) R75847
theorem R68415 : Reach 68415 := rs (se 1 (by rfl) ⟨51311, by rfl⟩) R102623
theorem R68735 : Reach 68735 := rs (se 1 (by rfl) ⟨51551, by rfl⟩) R103103
theorem R101627 : Reach 101627 := rs (se 1 (by rfl) ⟨76220, by rfl⟩) R152441
theorem R102095 : Reach 102095 := rs (se 1 (by rfl) ⟨76571, by rfl⟩) R153143
theorem R233387 : Reach 233387 := rs (se 1 (by rfl) ⟨175040, by rfl⟩) R350081
theorem R69631 : Reach 69631 := rs (se 1 (by rfl) ⟨52223, by rfl⟩) R104447
theorem R69743 : Reach 69743 := rs (se 1 (by rfl) ⟨52307, by rfl⟩) R104615
theorem R102683 : Reach 102683 := rs (se 1 (by rfl) ⟨77012, by rfl⟩) R154025
theorem R103367 : Reach 103367 := rs (se 1 (by rfl) ⟨77525, by rfl⟩) R155051
theorem R103391 : Reach 103391 := rs (se 1 (by rfl) ⟨77543, by rfl⟩) R155087
theorem R70655 : Reach 70655 := rs (se 1 (by rfl) ⟨52991, by rfl⟩) R105983
theorem R103451 : Reach 103451 := rs (se 1 (by rfl) ⟨77588, by rfl⟩) R155177
theorem R70759 : Reach 70759 := rs (se 1 (by rfl) ⟨53069, by rfl⟩) R106139
theorem R857213 : Reach 857213 := rs (se 3 (by rfl) ⟨160727, by rfl⟩) R321455
theorem R70783 : Reach 70783 := rs (se 1 (by rfl) ⟨53087, by rfl⟩) R106175
theorem R103583 : Reach 103583 := rs (se 1 (by rfl) ⟨77687, by rfl⟩) R155375
theorem R71039 : Reach 71039 := rs (se 1 (by rfl) ⟨53279, by rfl⟩) R106559
theorem R103991 : Reach 103991 := rs (se 1 (by rfl) ⟨77993, by rfl⟩) R155987
theorem R988751 : Reach 988751 := rs (se 1 (by rfl) ⟨741563, by rfl⟩) R1483127
theorem R235115 : Reach 235115 := rs (se 1 (by rfl) ⟨176336, by rfl⟩) R352673
theorem R104201 : Reach 104201 := rs (se 2 (by rfl) ⟨39075, by rfl⟩) R78151
theorem R170171 : Reach 170171 := rs (se 1 (by rfl) ⟨127628, by rfl⟩) R255257
theorem R104825 : Reach 104825 := rs (se 2 (by rfl) ⟨39309, by rfl⟩) R78619
theorem R1972673 : Reach 1972673 := rs (se 2 (by rfl) ⟨739752, by rfl⟩) R1479505
theorem R104927 : Reach 104927 := rs (se 1 (by rfl) ⟨78695, by rfl⟩) R157391
theorem R1940111 : Reach 1940111 := rs (se 1 (by rfl) ⟨1455083, by rfl⟩) R2910167
theorem R105167 : Reach 105167 := rs (se 1 (by rfl) ⟨78875, by rfl⟩) R157751
theorem R105755 : Reach 105755 := rs (se 1 (by rfl) ⟨79316, by rfl⟩) R158633
theorem R761179 : Reach 761179 := rs (se 1 (by rfl) ⟨570884, by rfl⟩) R1141769
theorem R106031 : Reach 106031 := rs (se 1 (by rfl) ⟨79523, by rfl⟩) R159047
theorem R532169 : Reach 532169 := rs (se 2 (by rfl) ⟨199563, by rfl⟩) R399127
theorem R106475 : Reach 106475 := rs (se 1 (by rfl) ⟨79856, by rfl⟩) R159713
theorem R106523 : Reach 106523 := rs (se 1 (by rfl) ⟨79892, by rfl⟩) R159785
theorem R991379 : Reach 991379 := rs (se 1 (by rfl) ⟨743534, by rfl⟩) R1487069
theorem R402043 : Reach 402043 := rs (se 1 (by rfl) ⟨301532, by rfl⟩) R603065
theorem R402569 : Reach 402569 := rs (se 2 (by rfl) ⟨150963, by rfl⟩) R301927
theorem R894347 : Reach 894347 := rs (se 1 (by rfl) ⟨670760, by rfl⟩) R1341521
theorem R567323 : Reach 567323 := rs (se 1 (by rfl) ⟨425492, by rfl⟩) R850985
theorem R175081 : Reach 175081 := rs (se 2 (by rfl) ⟨65655, by rfl⟩) R131311
theorem R371749 : Reach 371749 := rs (se 4 (by rfl) ⟨34851, by rfl⟩) R69703
theorem R1584305 : Reach 1584305 := rs (se 2 (by rfl) ⟨594114, by rfl⟩) R1188229
theorem R404959 : Reach 404959 := rs (se 1 (by rfl) ⟨303719, by rfl⟩) R607439
theorem R77467 : Reach 77467 := rs (se 1 (by rfl) ⟨58100, by rfl⟩) R116201
theorem R1520207 : Reach 1520207 := rs (se 1 (by rfl) ⟨1140155, by rfl⟩) R2280311
theorem R373585 : Reach 373585 := rs (se 2 (by rfl) ⟨140094, by rfl⟩) R280189
theorem R800441 : Reach 800441 := rs (se 2 (by rfl) ⟨300165, by rfl⟩) R600331
theorem R505607 : Reach 505607 := rs (se 1 (by rfl) ⟨379205, by rfl⟩) R758411
theorem R670841 : Reach 670841 := rs (se 2 (by rfl) ⟨251565, by rfl⟩) R503131
theorem R114041 : Reach 114041 := rs (se 2 (by rfl) ⟨42765, by rfl⟩) R85531
theorem R836185 : Reach 836185 := rs (se 2 (by rfl) ⟨313569, by rfl⟩) R627139
theorem R149759 : Reach 149759 := rs (se 1 (by rfl) ⟨112319, by rfl⟩) R224639
theorem R1296755 : Reach 1296755 := rs (se 1 (by rfl) ⟨972566, by rfl⟩) R1945133
theorem R282527 : Reach 282527 := rs (se 1 (by rfl) ⟨211895, by rfl⟩) R423791
theorem R151775 : Reach 151775 := rs (se 1 (by rfl) ⟨113831, by rfl⟩) R227663
theorem R119387 : Reach 119387 := rs (se 1 (by rfl) ⟨89540, by rfl⟩) R179081
theorem R152315 : Reach 152315 := rs (se 1 (by rfl) ⟨114236, by rfl⟩) R228473
theorem R152423 : Reach 152423 := rs (se 1 (by rfl) ⟨114317, by rfl⟩) R228635
theorem R1660283 : Reach 1660283 := rs (se 1 (by rfl) ⟨1245212, by rfl⟩) R2490425
theorem R153179 : Reach 153179 := rs (se 1 (by rfl) ⟨114884, by rfl⟩) R229769
theorem R513701 : Reach 513701 := rs (se 4 (by rfl) ⟨48159, by rfl⟩) R96319
theorem R645029 : Reach 645029 := rs (se 4 (by rfl) ⟨60471, by rfl⟩) R120943
theorem R1137361 : Reach 1137361 := rs (se 2 (by rfl) ⟨426510, by rfl⟩) R853021
theorem R908495 : Reach 908495 := rs (se 1 (by rfl) ⟨681371, by rfl⟩) R1362743
theorem R1466657 : Reach 1466657 := rs (se 2 (by rfl) ⟨549996, by rfl⟩) R1099993
theorem R320381 : Reach 320381 := rs (se 3 (by rfl) ⟨60071, by rfl⟩) R120143
theorem R1042415 : Reach 1042415 := rs (se 1 (by rfl) ⟨781811, by rfl⟩) R1563623
theorem R256031 : Reach 256031 := rs (se 1 (by rfl) ⟨192023, by rfl⟩) R384047
theorem R125531 : Reach 125531 := rs (se 1 (by rfl) ⟨94148, by rfl⟩) R188297
theorem R1895993 : Reach 1895993 := rs (se 2 (by rfl) ⟨710997, by rfl⟩) R1421995
theorem R945851 : Reach 945851 := rs (se 1 (by rfl) ⟨709388, by rfl⟩) R1418777
theorem R258461 : Reach 258461 := rs (se 3 (by rfl) ⟨48461, by rfl⟩) R96923
theorem R160475 : Reach 160475 := rs (se 1 (by rfl) ⟨120356, by rfl⟩) R240713
theorem R1176605 : Reach 1176605 := rs (se 3 (by rfl) ⟨220613, by rfl⟩) R441227
theorem R652697 : Reach 652697 := rs (se 2 (by rfl) ⟨244761, by rfl⟩) R489523
theorem R128479 : Reach 128479 := rs (se 1 (by rfl) ⟨96359, by rfl⟩) R192719
theorem R259631 : Reach 259631 := rs (se 1 (by rfl) ⟨194723, by rfl⟩) R389447
theorem R260435 : Reach 260435 := rs (se 1 (by rfl) ⟨195326, by rfl⟩) R390653
theorem R227771 : Reach 227771 := rs (se 1 (by rfl) ⟨170828, by rfl⟩) R341657
theorem R96815 : Reach 96815 := rs (se 1 (by rfl) ⟨72611, by rfl⟩) R145223
theorem R129755 : Reach 129755 := rs (se 1 (by rfl) ⟨97316, by rfl⟩) R194633
theorem R260891 : Reach 260891 := rs (se 1 (by rfl) ⟨195668, by rfl⟩) R391337
theorem R2030629 : Reach 2030629 := rs (se 4 (by rfl) ⟨190371, by rfl⟩) R380743
theorem R195691 : Reach 195691 := rs (se 1 (by rfl) ⟨146768, by rfl⟩) R293537
theorem R818383 : Reach 818383 := rs (se 1 (by rfl) ⟨613787, by rfl⟩) R1227575
theorem R228577 : Reach 228577 := rs (se 2 (by rfl) ⟨85716, by rfl⟩) R171433
theorem R1114913 : Reach 1114913 := rs (se 2 (by rfl) ⟨418092, by rfl⟩) R836185
theorem R99839 : Reach 99839 := rs (se 1 (by rfl) ⟨74879, by rfl⟩) R149759
theorem R67199 : Reach 67199 := rs (se 1 (by rfl) ⟨50399, by rfl⟩) R100799
theorem R67399 : Reach 67399 := rs (se 1 (by rfl) ⟨50549, by rfl⟩) R101099
theorem R67419 : Reach 67419 := rs (se 1 (by rfl) ⟨50564, by rfl⟩) R101129
theorem R427933 : Reach 427933 := rs (se 3 (by rfl) ⟨80237, by rfl⟩) R160475
theorem R67751 : Reach 67751 := rs (se 1 (by rfl) ⟨50813, by rfl⟩) R101627
theorem R68063 : Reach 68063 := rs (se 1 (by rfl) ⟨51047, by rfl⟩) R102095
theorem R101183 : Reach 101183 := rs (se 1 (by rfl) ⟨75887, by rfl⟩) R151775
theorem R68455 : Reach 68455 := rs (se 1 (by rfl) ⟨51341, by rfl⟩) R102683
theorem R101543 : Reach 101543 := rs (se 1 (by rfl) ⟨76157, by rfl⟩) R152315
theorem R101615 : Reach 101615 := rs (se 1 (by rfl) ⟨76211, by rfl⟩) R152423
theorem R68911 : Reach 68911 := rs (se 1 (by rfl) ⟨51683, by rfl⟩) R103367
theorem R68927 : Reach 68927 := rs (se 1 (by rfl) ⟨51695, by rfl⟩) R103391
theorem R68967 : Reach 68967 := rs (se 1 (by rfl) ⟨51725, by rfl⟩) R103451
theorem R69055 : Reach 69055 := rs (se 1 (by rfl) ⟨51791, by rfl⟩) R103583
theorem R69327 : Reach 69327 := rs (se 1 (by rfl) ⟨51995, by rfl⟩) R103991
theorem R659167 : Reach 659167 := rs (se 1 (by rfl) ⟨494375, by rfl⟩) R988751
theorem R102119 : Reach 102119 := rs (se 1 (by rfl) ⟨76589, by rfl⟩) R153179
theorem R69467 : Reach 69467 := rs (se 1 (by rfl) ⟨52100, by rfl⟩) R104201
theorem R430019 : Reach 430019 := rs (se 1 (by rfl) ⟨322514, by rfl⟩) R645029
theorem R233441 : Reach 233441 := rs (se 2 (by rfl) ⟨87540, by rfl⟩) R175081
theorem R495665 : Reach 495665 := rs (se 2 (by rfl) ⟨185874, by rfl⟩) R371749
theorem R69883 : Reach 69883 := rs (se 1 (by rfl) ⟨52412, by rfl⟩) R104825
theorem R1315115 : Reach 1315115 := rs (se 1 (by rfl) ⟨986336, by rfl⟩) R1972673
theorem R69951 : Reach 69951 := rs (se 1 (by rfl) ⟨52463, by rfl⟩) R104927
theorem R70111 : Reach 70111 := rs (se 1 (by rfl) ⟨52583, by rfl⟩) R105167
theorem R1348285 : Reach 1348285 := rs (se 3 (by rfl) ⟨252803, by rfl⟩) R505607
theorem R70503 : Reach 70503 := rs (se 1 (by rfl) ⟨52877, by rfl⟩) R105755
theorem R103289 : Reach 103289 := rs (se 2 (by rfl) ⟨38733, by rfl⟩) R77467
theorem R70687 : Reach 70687 := rs (se 1 (by rfl) ⟨53015, by rfl⟩) R106031
theorem R70983 : Reach 70983 := rs (se 1 (by rfl) ⟨53237, by rfl⟩) R106475
theorem R71015 : Reach 71015 := rs (se 1 (by rfl) ⟨53261, by rfl⟩) R106523
theorem R660919 : Reach 660919 := rs (se 1 (by rfl) ⟨495689, by rfl⟩) R991379
theorem R268379 : Reach 268379 := rs (se 1 (by rfl) ⟨201284, by rfl⟩) R402569
theorem R596231 : Reach 596231 := rs (se 1 (by rfl) ⟨447173, by rfl⟩) R894347
theorem R498113 : Reach 498113 := rs (se 2 (by rfl) ⟨186792, by rfl⟩) R373585
theorem R694943 : Reach 694943 := rs (se 1 (by rfl) ⟨521207, by rfl⟩) R1042415
theorem R170687 : Reach 170687 := rs (se 1 (by rfl) ⟨128015, by rfl⟩) R256031
theorem R171305 : Reach 171305 := rs (se 2 (by rfl) ⟨64239, by rfl⟩) R128479
theorem R1056203 : Reach 1056203 := rs (se 1 (by rfl) ⟨792152, by rfl⟩) R1584305
theorem R172307 : Reach 172307 := rs (se 1 (by rfl) ⟨129230, by rfl⟩) R258461
theorem R435131 : Reach 435131 := rs (se 1 (by rfl) ⟨326348, by rfl⟩) R652697
theorem R1516481 : Reach 1516481 := rs (se 2 (by rfl) ⟨568680, by rfl⟩) R1137361
theorem R173087 : Reach 173087 := rs (se 1 (by rfl) ⟨129815, by rfl⟩) R259631
theorem R533627 : Reach 533627 := rs (se 1 (by rfl) ⟨400220, by rfl⟩) R800441
theorem R173623 : Reach 173623 := rs (se 1 (by rfl) ⟨130217, by rfl⟩) R260435
theorem R1091177 : Reach 1091177 := rs (se 2 (by rfl) ⟨409191, by rfl⟩) R818383
theorem R304769 : Reach 304769 := rs (se 2 (by rfl) ⟨114288, by rfl⟩) R228577
theorem R173927 : Reach 173927 := rs (se 1 (by rfl) ⟨130445, by rfl⟩) R260891
theorem R76027 : Reach 76027 := rs (se 1 (by rfl) ⟨57020, by rfl⟩) R114041
theorem R175567 : Reach 175567 := rs (se 1 (by rfl) ⟨131675, by rfl⟩) R263351
theorem R536057 : Reach 536057 := rs (se 2 (by rfl) ⟨201021, by rfl⟩) R402043
theorem R864503 : Reach 864503 := rs (se 1 (by rfl) ⟨648377, by rfl⟩) R1296755
theorem R79591 : Reach 79591 := rs (se 1 (by rfl) ⟨59693, by rfl⟩) R119387
theorem R571475 : Reach 571475 := rs (se 1 (by rfl) ⟨428606, by rfl⟩) R857213
theorem R833753 : Reach 833753 := rs (se 2 (by rfl) ⟨312657, by rfl⟩) R625315
theorem R342467 : Reach 342467 := rs (se 1 (by rfl) ⟨256850, by rfl⟩) R513701
theorem R113447 : Reach 113447 := rs (se 1 (by rfl) ⟨85085, by rfl⟩) R170171
theorem R1293407 : Reach 1293407 := rs (se 1 (by rfl) ⟨970055, by rfl⟩) R1940111
theorem R539945 : Reach 539945 := rs (se 2 (by rfl) ⟨202479, by rfl⟩) R404959
theorem R605663 : Reach 605663 := rs (se 1 (by rfl) ⟨454247, by rfl⟩) R908495
theorem R213587 : Reach 213587 := rs (se 1 (by rfl) ⟨160190, by rfl⟩) R320381
theorem R378215 : Reach 378215 := rs (se 1 (by rfl) ⟨283661, by rfl⟩) R567323
theorem R83687 : Reach 83687 := rs (se 1 (by rfl) ⟨62765, by rfl⟩) R125531
theorem R1263995 : Reach 1263995 := rs (se 1 (by rfl) ⟨947996, by rfl⟩) R1895993
theorem R2707505 : Reach 2707505 := rs (se 2 (by rfl) ⟨1015314, by rfl⟩) R2030629
theorem R151847 : Reach 151847 := rs (se 1 (by rfl) ⟨113885, by rfl⟩) R227771
theorem R86503 : Reach 86503 := rs (se 1 (by rfl) ⟨64877, by rfl⟩) R129755
theorem R447227 : Reach 447227 := rs (se 1 (by rfl) ⟨335420, by rfl⟩) R670841
theorem R152999 : Reach 152999 := rs (se 1 (by rfl) ⟨114749, by rfl⟩) R229499
theorem R218729 : Reach 218729 := rs (se 2 (by rfl) ⟨82023, by rfl⟩) R164047
theorem R153215 : Reach 153215 := rs (se 1 (by rfl) ⟨114911, by rfl⟩) R229823
theorem R349919 : Reach 349919 := rs (se 1 (by rfl) ⟨262439, by rfl⟩) R524879
theorem R350567 : Reach 350567 := rs (se 1 (by rfl) ⟨262925, by rfl⟩) R525851
theorem R350891 : Reach 350891 := rs (se 1 (by rfl) ⟨263168, by rfl⟩) R526337
theorem R154799 : Reach 154799 := rs (se 1 (by rfl) ⟨116099, by rfl⟩) R232199
theorem R188351 : Reach 188351 := rs (se 1 (by rfl) ⟨141263, by rfl⟩) R282527
theorem R155591 : Reach 155591 := rs (se 1 (by rfl) ⟨116693, by rfl⟩) R233387
theorem R484217 : Reach 484217 := rs (se 2 (by rfl) ⟨181581, by rfl⟩) R363163
theorem R1106855 : Reach 1106855 := rs (se 1 (by rfl) ⟨830141, by rfl⟩) R1660283
theorem R156743 : Reach 156743 := rs (se 1 (by rfl) ⟨117557, by rfl⟩) R235115
theorem R354779 : Reach 354779 := rs (se 1 (by rfl) ⟨266084, by rfl⟩) R532169
theorem R977771 : Reach 977771 := rs (se 1 (by rfl) ⟨733328, by rfl⟩) R1466657
theorem R258173 : Reach 258173 := rs (se 3 (by rfl) ⟨48407, by rfl⟩) R96815
theorem R1013471 : Reach 1013471 := rs (se 1 (by rfl) ⟨760103, by rfl⟩) R1520207
theorem R784403 : Reach 784403 := rs (se 1 (by rfl) ⟨588302, by rfl⟩) R1176605
theorem R260921 : Reach 260921 := rs (se 2 (by rfl) ⟨97845, by rfl⟩) R195691
theorem R1014905 : Reach 1014905 := rs (se 2 (by rfl) ⟨380589, by rfl⟩) R761179
theorem R2522269 : Reach 2522269 := rs (se 3 (by rfl) ⟨472925, by rfl⟩) R945851
theorem R67455 : Reach 67455 := rs (se 1 (by rfl) ⟨50591, by rfl⟩) R101183
theorem R231497 : Reach 231497 := rs (se 2 (by rfl) ⟨86811, by rfl⟩) R173623
theorem R67695 : Reach 67695 := rs (se 1 (by rfl) ⟨50771, by rfl⟩) R101543
theorem R67743 : Reach 67743 := rs (se 1 (by rfl) ⟨50807, by rfl⟩) R101615
theorem R68079 : Reach 68079 := rs (se 1 (by rfl) ⟨51059, by rfl⟩) R102119
theorem R1805003 : Reach 1805003 := rs (se 1 (by rfl) ⟨1353752, by rfl⟩) R2707505
theorem R101231 : Reach 101231 := rs (se 1 (by rfl) ⟨75923, by rfl⟩) R151847
theorem R101369 : Reach 101369 := rs (se 2 (by rfl) ⟨38013, by rfl⟩) R76027
theorem R298151 : Reach 298151 := rs (se 1 (by rfl) ⟨223613, by rfl⟩) R447227
theorem R68859 : Reach 68859 := rs (se 1 (by rfl) ⟨51644, by rfl⟩) R103289
theorem R101999 : Reach 101999 := rs (se 1 (by rfl) ⟨76499, by rfl⟩) R152999
theorem R102143 : Reach 102143 := rs (se 1 (by rfl) ⟨76607, by rfl⟩) R153215
theorem R233279 : Reach 233279 := rs (se 1 (by rfl) ⟨174959, by rfl⟩) R349919
theorem R266237 : Reach 266237 := rs (se 3 (by rfl) ⟨49919, by rfl⟩) R99839
theorem R397487 : Reach 397487 := rs (se 1 (by rfl) ⟨298115, by rfl⟩) R596231
theorem R233711 : Reach 233711 := rs (se 1 (by rfl) ⟨175283, by rfl⟩) R350567
theorem R332075 : Reach 332075 := rs (se 1 (by rfl) ⟨249056, by rfl⟩) R498113
theorem R463295 : Reach 463295 := rs (se 1 (by rfl) ⟨347471, by rfl⟩) R694943
theorem R233927 : Reach 233927 := rs (se 1 (by rfl) ⟨175445, by rfl⟩) R350891
theorem R234089 : Reach 234089 := rs (se 2 (by rfl) ⟨87783, by rfl⟩) R175567
theorem R103199 : Reach 103199 := rs (se 1 (by rfl) ⟨77399, by rfl⟩) R154799
theorem R103727 : Reach 103727 := rs (se 1 (by rfl) ⟨77795, by rfl⟩) R155591
theorem R104495 : Reach 104495 := rs (se 1 (by rfl) ⟨78371, by rfl⟩) R156743
theorem R727451 : Reach 727451 := rs (se 1 (by rfl) ⟨545588, by rfl⟩) R1091177
theorem R236519 : Reach 236519 := rs (se 1 (by rfl) ⟨177389, by rfl⟩) R354779
theorem R302525 : Reach 302525 := rs (se 3 (by rfl) ⟨56723, by rfl⟩) R113447
theorem R106121 : Reach 106121 := rs (se 2 (by rfl) ⟨39795, by rfl⟩) R79591
theorem R172115 : Reach 172115 := rs (se 1 (by rfl) ⟨129086, by rfl⟩) R258173
theorem R3515557 : Reach 3515557 := rs (se 4 (by rfl) ⟨329583, by rfl⟩) R659167
theorem R75631 : Reach 75631 := rs (se 1 (by rfl) ⟨56723, by rfl⟩) R113447
theorem R173947 : Reach 173947 := rs (se 1 (by rfl) ⟨130460, by rfl⟩) R260921
theorem R862271 : Reach 862271 := rs (se 1 (by rfl) ⟨646703, by rfl⟩) R1293407
theorem R403775 : Reach 403775 := rs (se 1 (by rfl) ⟨302831, by rfl⟩) R605663
theorem R142391 : Reach 142391 := rs (se 1 (by rfl) ⟨106793, by rfl⟩) R213587
theorem R570577 : Reach 570577 := rs (se 2 (by rfl) ⟨213966, by rfl⟩) R427933
theorem R145819 : Reach 145819 := rs (se 1 (by rfl) ⟨109364, by rfl⟩) R218729
theorem R178919 : Reach 178919 := rs (se 1 (by rfl) ⟨134189, by rfl⟩) R268379
theorem R113791 : Reach 113791 := rs (se 1 (by rfl) ⟨85343, by rfl⟩) R170687
theorem R114203 : Reach 114203 := rs (se 1 (by rfl) ⟨85652, by rfl⟩) R171305
theorem R704135 : Reach 704135 := rs (se 1 (by rfl) ⟨528101, by rfl⟩) R1056203
theorem R114871 : Reach 114871 := rs (se 1 (by rfl) ⟨86153, by rfl⟩) R172307
theorem R737903 : Reach 737903 := rs (se 1 (by rfl) ⟨553427, by rfl⟩) R1106855
theorem R115337 : Reach 115337 := rs (se 2 (by rfl) ⟨43251, by rfl⟩) R86503
theorem R115391 : Reach 115391 := rs (se 1 (by rfl) ⟨86543, by rfl⟩) R173087
theorem R13452101 : Reach 13452101 := rs (se 4 (by rfl) ⟨1261134, by rfl⟩) R2522269
theorem R115951 : Reach 115951 := rs (se 1 (by rfl) ⟨86963, by rfl⟩) R173927
theorem R576335 : Reach 576335 := rs (se 1 (by rfl) ⟨432251, by rfl⟩) R864503
theorem R675647 : Reach 675647 := rs (se 1 (by rfl) ⟨506735, by rfl⟩) R1013471
theorem R380983 : Reach 380983 := rs (se 1 (by rfl) ⟨285737, by rfl⟩) R571475
theorem R676603 : Reach 676603 := rs (se 1 (by rfl) ⟨507452, by rfl⟩) R1014905
theorem R743275 : Reach 743275 := rs (se 1 (by rfl) ⟨557456, by rfl⟩) R1114913
theorem R252143 : Reach 252143 := rs (se 1 (by rfl) ⟨189107, by rfl⟩) R378215
theorem R842663 : Reach 842663 := rs (se 1 (by rfl) ⟨631997, by rfl⟩) R1263995
theorem R330443 : Reach 330443 := rs (se 1 (by rfl) ⟨247832, by rfl⟩) R495665
theorem R286679 : Reach 286679 := rs (se 1 (by rfl) ⟨215009, by rfl⟩) R430019
theorem R155627 : Reach 155627 := rs (se 1 (by rfl) ⟨116720, by rfl⟩) R233441
theorem R876743 : Reach 876743 := rs (se 1 (by rfl) ⟨657557, by rfl⟩) R1315115
theorem R812717 : Reach 812717 := rs (se 3 (by rfl) ⟨152384, by rfl⟩) R304769
theorem R223165 : Reach 223165 := rs (se 3 (by rfl) ⟨41843, by rfl⟩) R83687
theorem R125567 : Reach 125567 := rs (se 1 (by rfl) ⟨94175, by rfl⟩) R188351
theorem R322811 : Reach 322811 := rs (se 1 (by rfl) ⟨242108, by rfl⟩) R484217
theorem R290087 : Reach 290087 := rs (se 1 (by rfl) ⟨217565, by rfl⟩) R435131
theorem R1010987 : Reach 1010987 := rs (se 1 (by rfl) ⟨758240, by rfl⟩) R1516481
theorem R355751 : Reach 355751 := rs (se 1 (by rfl) ⟨266813, by rfl⟩) R533627
theorem R1797713 : Reach 1797713 := rs (se 2 (by rfl) ⟨674142, by rfl⟩) R1348285
theorem R716789 : Reach 716789 := rs (se 5 (by rfl) ⟨33599, by rfl⟩) R67199
theorem R651847 : Reach 651847 := rs (se 1 (by rfl) ⟨488885, by rfl⟩) R977771
theorem R881225 : Reach 881225 := rs (se 2 (by rfl) ⟨330459, by rfl⟩) R660919
theorem R357371 : Reach 357371 := rs (se 1 (by rfl) ⟨268028, by rfl⟩) R536057
theorem R522935 : Reach 522935 := rs (se 1 (by rfl) ⟨392201, by rfl⟩) R784403
theorem R555835 : Reach 555835 := rs (se 1 (by rfl) ⟨416876, by rfl⟩) R833753
theorem R228311 : Reach 228311 := rs (se 1 (by rfl) ⟨171233, by rfl⟩) R342467
theorem R359963 : Reach 359963 := rs (se 1 (by rfl) ⟨269972, by rfl⟩) R539945
theorem R491935 : Reach 491935 := rs (se 1 (by rfl) ⟨368951, by rfl⟩) R737903
theorem R4687409 : Reach 4687409 := rs (se 2 (by rfl) ⟨1757778, by rfl⟩) R3515557
theorem R67487 : Reach 67487 := rs (se 1 (by rfl) ⟨50615, by rfl⟩) R101231
theorem R67579 : Reach 67579 := rs (se 1 (by rfl) ⟨50684, by rfl⟩) R101369
theorem R198767 : Reach 198767 := rs (se 1 (by rfl) ⟨149075, by rfl⟩) R298151
theorem R67999 : Reach 67999 := rs (se 1 (by rfl) ⟨50999, by rfl⟩) R101999
theorem R100841 : Reach 100841 := rs (se 2 (by rfl) ⟨37815, by rfl⟩) R75631
theorem R231929 : Reach 231929 := rs (se 2 (by rfl) ⟨86973, by rfl⟩) R173947
theorem R68095 : Reach 68095 := rs (se 1 (by rfl) ⟨51071, by rfl⟩) R102143
theorem R297553 : Reach 297553 := rs (se 2 (by rfl) ⟨111582, by rfl⟩) R223165
theorem R264991 : Reach 264991 := rs (se 1 (by rfl) ⟨198743, by rfl⟩) R397487
theorem R68799 : Reach 68799 := rs (se 1 (by rfl) ⟨51599, by rfl⟩) R103199
theorem R69151 : Reach 69151 := rs (se 1 (by rfl) ⟨51863, by rfl⟩) R103727
theorem R69663 : Reach 69663 := rs (se 1 (by rfl) ⟨52247, by rfl⟩) R104495
theorem R168095 : Reach 168095 := rs (se 1 (by rfl) ⟨126071, by rfl⟩) R252143
theorem R561775 : Reach 561775 := rs (se 1 (by rfl) ⟨421331, by rfl⟩) R842663
theorem R201683 : Reach 201683 := rs (se 1 (by rfl) ⟨151262, by rfl⟩) R302525
theorem R70747 : Reach 70747 := rs (se 1 (by rfl) ⟨53060, by rfl⟩) R106121
theorem R103751 : Reach 103751 := rs (se 1 (by rfl) ⟨77813, by rfl⟩) R155627
theorem R269183 : Reach 269183 := rs (se 1 (by rfl) ⟨201887, by rfl⟩) R403775
theorem R760769 : Reach 760769 := rs (se 2 (by rfl) ⟨285288, by rfl⟩) R570577
theorem R237167 : Reach 237167 := rs (se 1 (by rfl) ⟨177875, by rfl⟩) R355751
theorem R991033 : Reach 991033 := rs (se 2 (by rfl) ⟨371637, by rfl⟩) R743275
theorem R238247 : Reach 238247 := rs (se 1 (by rfl) ⟨178685, by rfl⟩) R357371
theorem R76135 : Reach 76135 := rs (se 1 (by rfl) ⟨57101, by rfl⟩) R114203
theorem R239975 : Reach 239975 := rs (se 1 (by rfl) ⟨179981, by rfl⟩) R359963
theorem R469423 : Reach 469423 := rs (se 1 (by rfl) ⟨352067, by rfl⟩) R704135
theorem R1911437 : Reach 1911437 := rs (se 3 (by rfl) ⟨358394, by rfl⟩) R716789
theorem R76891 : Reach 76891 := rs (se 1 (by rfl) ⟨57668, by rfl⟩) R115337
theorem R76927 : Reach 76927 := rs (se 1 (by rfl) ⟨57695, by rfl⟩) R115391
theorem R177491 : Reach 177491 := rs (se 1 (by rfl) ⟨133118, by rfl⟩) R266237
theorem R308863 : Reach 308863 := rs (se 1 (by rfl) ⟨231647, by rfl⟩) R463295
theorem R114743 : Reach 114743 := rs (se 1 (by rfl) ⟨86057, by rfl⟩) R172115
theorem R507977 : Reach 507977 := rs (se 2 (by rfl) ⟨190491, by rfl⟩) R380983
theorem R869129 : Reach 869129 := rs (se 2 (by rfl) ⟨325923, by rfl⟩) R651847
theorem R902137 : Reach 902137 := rs (se 2 (by rfl) ⟨338301, by rfl⟩) R676603
theorem R541811 : Reach 541811 := rs (se 1 (by rfl) ⟨406358, by rfl⟩) R812717
theorem R574847 : Reach 574847 := rs (se 1 (by rfl) ⟨431135, by rfl⟩) R862271
theorem R83711 : Reach 83711 := rs (se 1 (by rfl) ⟨62783, by rfl⟩) R125567
theorem R215207 : Reach 215207 := rs (se 1 (by rfl) ⟨161405, by rfl⟩) R322811
theorem R673991 : Reach 673991 := rs (se 1 (by rfl) ⟨505493, by rfl⟩) R1010987
theorem R1198475 : Reach 1198475 := rs (se 1 (by rfl) ⟨898856, by rfl⟩) R1797713
theorem R741113 : Reach 741113 := rs (se 2 (by rfl) ⟨277917, by rfl⟩) R555835
theorem R151721 : Reach 151721 := rs (se 2 (by rfl) ⟨56895, by rfl⟩) R113791
theorem R348623 : Reach 348623 := rs (se 1 (by rfl) ⟨261467, by rfl⟩) R522935
theorem R119279 : Reach 119279 := rs (se 1 (by rfl) ⟨89459, by rfl⟩) R178919
theorem R152207 : Reach 152207 := rs (se 1 (by rfl) ⟨114155, by rfl⟩) R228311
theorem R153161 : Reach 153161 := rs (se 2 (by rfl) ⟨57435, by rfl⟩) R114871
theorem R8968067 : Reach 8968067 := rs (se 1 (by rfl) ⟨6726050, by rfl⟩) R13452101
theorem R154331 : Reach 154331 := rs (se 1 (by rfl) ⟨115748, by rfl⟩) R231497
theorem R154601 : Reach 154601 := rs (se 2 (by rfl) ⟨57975, by rfl⟩) R115951
theorem R220295 : Reach 220295 := rs (se 1 (by rfl) ⟨165221, by rfl⟩) R330443
theorem R1203335 : Reach 1203335 := rs (se 1 (by rfl) ⟨902501, by rfl⟩) R1805003
theorem R777701 : Reach 777701 := rs (se 4 (by rfl) ⟨72909, by rfl⟩) R145819
theorem R155519 : Reach 155519 := rs (se 1 (by rfl) ⟨116639, by rfl⟩) R233279
theorem R450431 : Reach 450431 := rs (se 1 (by rfl) ⟨337823, by rfl⟩) R675647
theorem R155807 : Reach 155807 := rs (se 1 (by rfl) ⟨116855, by rfl⟩) R233711
theorem R221383 : Reach 221383 := rs (se 1 (by rfl) ⟨166037, by rfl⟩) R332075
theorem R155951 : Reach 155951 := rs (se 1 (by rfl) ⟨116963, by rfl⟩) R233927
theorem R156059 : Reach 156059 := rs (se 1 (by rfl) ⟨117044, by rfl⟩) R234089
theorem R484967 : Reach 484967 := rs (se 1 (by rfl) ⟨363725, by rfl⟩) R727451
theorem R157679 : Reach 157679 := rs (se 1 (by rfl) ⟨118259, by rfl⟩) R236519
theorem R191119 : Reach 191119 := rs (se 1 (by rfl) ⟨143339, by rfl⟩) R286679
theorem R584495 : Reach 584495 := rs (se 1 (by rfl) ⟨438371, by rfl⟩) R876743
theorem R94927 : Reach 94927 := rs (se 1 (by rfl) ⟨71195, by rfl⟩) R142391
theorem R193391 : Reach 193391 := rs (se 1 (by rfl) ⟨145043, by rfl⟩) R290087
theorem R1536893 : Reach 1536893 := rs (se 3 (by rfl) ⟨288167, by rfl⟩) R576335
theorem R587483 : Reach 587483 := rs (se 1 (by rfl) ⟨440612, by rfl⟩) R881225
theorem R295177 : Reach 295177 := rs (se 2 (by rfl) ⟨110691, by rfl⟩) R221383
theorem R655913 : Reach 655913 := rs (se 2 (by rfl) ⟨245967, by rfl⟩) R491935
theorem R361207 : Reach 361207 := rs (se 1 (by rfl) ⟨270905, by rfl⟩) R541811
theorem R132511 : Reach 132511 := rs (se 1 (by rfl) ⟨99383, by rfl⟩) R198767
theorem R67227 : Reach 67227 := rs (se 1 (by rfl) ⟨50420, by rfl⟩) R100841
theorem R494075 : Reach 494075 := rs (se 1 (by rfl) ⟨370556, by rfl⟩) R741113
theorem R101147 : Reach 101147 := rs (se 1 (by rfl) ⟨75860, by rfl⟩) R151721
theorem R232415 : Reach 232415 := rs (se 1 (by rfl) ⟨174311, by rfl⟩) R348623
theorem R101471 : Reach 101471 := rs (se 1 (by rfl) ⟨76103, by rfl⟩) R152207
theorem R101513 : Reach 101513 := rs (se 2 (by rfl) ⟨38067, by rfl⟩) R76135
theorem R625897 : Reach 625897 := rs (se 2 (by rfl) ⟨234711, by rfl⟩) R469423
theorem R134455 : Reach 134455 := rs (se 1 (by rfl) ⟨100841, by rfl⟩) R201683
theorem R396737 : Reach 396737 := rs (se 2 (by rfl) ⟨148776, by rfl⟩) R297553
theorem R69167 : Reach 69167 := rs (se 1 (by rfl) ⟨51875, by rfl⟩) R103751
theorem R102107 : Reach 102107 := rs (se 1 (by rfl) ⟨76580, by rfl⟩) R153161
theorem R102521 : Reach 102521 := rs (se 2 (by rfl) ⟨38445, by rfl⟩) R76891
theorem R102569 : Reach 102569 := rs (se 2 (by rfl) ⟨38463, by rfl⟩) R76927
theorem R102887 : Reach 102887 := rs (se 1 (by rfl) ⟨77165, by rfl⟩) R154331
theorem R103067 : Reach 103067 := rs (se 1 (by rfl) ⟨77300, by rfl⟩) R154601
theorem R103679 : Reach 103679 := rs (se 1 (by rfl) ⟨77759, by rfl⟩) R155519
theorem R300287 : Reach 300287 := rs (se 1 (by rfl) ⟨225215, by rfl⟩) R450431
theorem R103871 : Reach 103871 := rs (se 1 (by rfl) ⟨77903, by rfl⟩) R155807
theorem R103967 : Reach 103967 := rs (se 1 (by rfl) ⟨77975, by rfl⟩) R155951
theorem R104039 : Reach 104039 := rs (se 1 (by rfl) ⟨78029, by rfl⟩) R156059
theorem R21142037 : Reach 21142037 := rs (se 6 (by rfl) ⟨495516, by rfl⟩) R991033
theorem R105119 : Reach 105119 := rs (se 1 (by rfl) ⟨78839, by rfl⟩) R157679
theorem R1024595 : Reach 1024595 := rs (se 1 (by rfl) ⟨768446, by rfl⟩) R1536893
theorem R76495 : Reach 76495 := rs (se 1 (by rfl) ⟨57371, by rfl⟩) R114743
theorem R338651 : Reach 338651 := rs (se 1 (by rfl) ⟨253988, by rfl⟩) R507977
theorem R3124939 : Reach 3124939 := rs (se 1 (by rfl) ⟨2343704, by rfl⟩) R4687409
theorem R143471 : Reach 143471 := rs (se 1 (by rfl) ⟨107603, by rfl⟩) R215207
theorem R798983 : Reach 798983 := rs (se 1 (by rfl) ⟨599237, by rfl⟩) R1198475
theorem R79519 : Reach 79519 := rs (se 1 (by rfl) ⟨59639, by rfl⟩) R119279
theorem R5978711 : Reach 5978711 := rs (se 1 (by rfl) ⟨4484033, by rfl⟩) R8968067
theorem R179455 : Reach 179455 := rs (se 1 (by rfl) ⟨134591, by rfl⟩) R269183
theorem R507179 : Reach 507179 := rs (se 1 (by rfl) ⟨380384, by rfl⟩) R760769
theorem R146863 : Reach 146863 := rs (se 1 (by rfl) ⟨110147, by rfl⟩) R220295
theorem R802223 : Reach 802223 := rs (se 1 (by rfl) ⟨601667, by rfl⟩) R1203335
theorem R411817 : Reach 411817 := rs (se 2 (by rfl) ⟨154431, by rfl⟩) R308863
theorem R118327 : Reach 118327 := rs (se 1 (by rfl) ⟨88745, by rfl⟩) R177491
theorem R448253 : Reach 448253 := rs (se 3 (by rfl) ⟨84047, by rfl⟩) R168095
theorem R579419 : Reach 579419 := rs (se 1 (by rfl) ⟨434564, by rfl⟩) R869129
theorem R383231 : Reach 383231 := rs (se 1 (by rfl) ⟨287423, by rfl⟩) R574847
theorem R1202849 : Reach 1202849 := rs (se 2 (by rfl) ⟨451068, by rfl⟩) R902137
theorem R449327 : Reach 449327 := rs (se 1 (by rfl) ⟨336995, by rfl⟩) R673991
theorem R154619 : Reach 154619 := rs (se 1 (by rfl) ⟨115964, by rfl⟩) R231929
theorem R254825 : Reach 254825 := rs (se 2 (by rfl) ⟨95559, by rfl⟩) R191119
theorem R353321 : Reach 353321 := rs (se 2 (by rfl) ⟨132495, by rfl⟩) R264991
theorem R223229 : Reach 223229 := rs (se 3 (by rfl) ⟨41855, by rfl⟩) R83711
theorem R518467 : Reach 518467 := rs (se 1 (by rfl) ⟨388850, by rfl⟩) R777701
theorem R158111 : Reach 158111 := rs (se 1 (by rfl) ⟨118583, by rfl⟩) R237167
theorem R158831 : Reach 158831 := rs (se 1 (by rfl) ⟨119123, by rfl⟩) R238247
theorem R749033 : Reach 749033 := rs (se 2 (by rfl) ⟨280887, by rfl⟩) R561775
theorem R126569 : Reach 126569 := rs (se 2 (by rfl) ⟨47463, by rfl⟩) R94927
theorem R323311 : Reach 323311 := rs (se 1 (by rfl) ⟨242483, by rfl⟩) R484967
theorem R159983 : Reach 159983 := rs (se 1 (by rfl) ⟨119987, by rfl⟩) R239975
theorem R1274291 : Reach 1274291 := rs (se 1 (by rfl) ⟨955718, by rfl⟩) R1911437
theorem R389663 : Reach 389663 := rs (se 1 (by rfl) ⟨292247, by rfl⟩) R584495
theorem R128927 : Reach 128927 := rs (se 1 (by rfl) ⟨96695, by rfl⟩) R193391
theorem R391655 : Reach 391655 := rs (se 1 (by rfl) ⟨293741, by rfl⟩) R587483
theorem R393569 : Reach 393569 := rs (se 2 (by rfl) ⟨147588, by rfl⟩) R295177
theorem R329383 : Reach 329383 := rs (se 1 (by rfl) ⟨247037, by rfl⟩) R494075
theorem R67431 : Reach 67431 := rs (se 1 (by rfl) ⟨50573, by rfl⟩) R101147
theorem R67647 : Reach 67647 := rs (se 1 (by rfl) ⟨50735, by rfl⟩) R101471
theorem R67675 : Reach 67675 := rs (se 1 (by rfl) ⟨50756, by rfl⟩) R101513
theorem R264491 : Reach 264491 := rs (se 1 (by rfl) ⟨198368, by rfl⟩) R396737
theorem R68071 : Reach 68071 := rs (se 1 (by rfl) ⟨51053, by rfl⟩) R102107
theorem R68347 : Reach 68347 := rs (se 1 (by rfl) ⟨51260, by rfl⟩) R102521
theorem R68379 : Reach 68379 := rs (se 1 (by rfl) ⟨51284, by rfl⟩) R102569
theorem R68591 : Reach 68591 := rs (se 1 (by rfl) ⟨51443, by rfl⟩) R102887
theorem R691289 : Reach 691289 := rs (se 2 (by rfl) ⟨259233, by rfl⟩) R518467
theorem R68711 : Reach 68711 := rs (se 1 (by rfl) ⟨51533, by rfl⟩) R103067
theorem R69119 : Reach 69119 := rs (se 1 (by rfl) ⟨51839, by rfl⟩) R103679
theorem R200191 : Reach 200191 := rs (se 1 (by rfl) ⟨150143, by rfl⟩) R300287
theorem R101993 : Reach 101993 := rs (se 2 (by rfl) ⟨38247, by rfl⟩) R76495
theorem R69247 : Reach 69247 := rs (se 1 (by rfl) ⟨51935, by rfl⟩) R103871
theorem R69311 : Reach 69311 := rs (se 1 (by rfl) ⟨51983, by rfl⟩) R103967
theorem R69359 : Reach 69359 := rs (se 1 (by rfl) ⟨52019, by rfl⟩) R104039
theorem R298835 : Reach 298835 := rs (se 1 (by rfl) ⟨224126, by rfl⟩) R448253
theorem R14094691 : Reach 14094691 := rs (se 1 (by rfl) ⟨10571018, by rfl⟩) R21142037
theorem R70079 : Reach 70079 := rs (se 1 (by rfl) ⟨52559, by rfl⟩) R105119
theorem R299551 : Reach 299551 := rs (se 1 (by rfl) ⟨224663, by rfl⟩) R449327
theorem R103079 : Reach 103079 := rs (se 1 (by rfl) ⟨77309, by rfl⟩) R154619
theorem R4166585 : Reach 4166585 := rs (se 2 (by rfl) ⟨1562469, by rfl⟩) R3124939
theorem R431081 : Reach 431081 := rs (se 2 (by rfl) ⟨161655, by rfl⟩) R323311
theorem R169883 : Reach 169883 := rs (se 1 (by rfl) ⟨127412, by rfl⟩) R254825
theorem R235547 : Reach 235547 := rs (se 1 (by rfl) ⟨176660, by rfl⟩) R353321
theorem R105407 : Reach 105407 := rs (se 1 (by rfl) ⟨79055, by rfl⟩) R158111
theorem R105887 : Reach 105887 := rs (se 1 (by rfl) ⟨79415, by rfl⟩) R158831
theorem R106025 : Reach 106025 := rs (se 2 (by rfl) ⟨39759, by rfl⟩) R79519
theorem R499355 : Reach 499355 := rs (se 1 (by rfl) ⟨374516, by rfl⟩) R749033
theorem R106655 : Reach 106655 := rs (se 1 (by rfl) ⟨79991, by rfl⟩) R159983
theorem R532655 : Reach 532655 := rs (se 1 (by rfl) ⟨399491, by rfl⟩) R798983
theorem R1352477 : Reach 1352477 := rs (se 3 (by rfl) ⟨253589, by rfl⟩) R507179
theorem R337517 : Reach 337517 := rs (se 3 (by rfl) ⟨63284, by rfl⟩) R126569
theorem R239273 : Reach 239273 := rs (se 2 (by rfl) ⟨89727, by rfl⟩) R179455
theorem R534815 : Reach 534815 := rs (se 1 (by rfl) ⟨401111, by rfl⟩) R802223
theorem R437275 : Reach 437275 := rs (se 1 (by rfl) ⟨327956, by rfl⟩) R655913
theorem R176681 : Reach 176681 := rs (se 2 (by rfl) ⟨66255, by rfl⟩) R132511
theorem R834529 : Reach 834529 := rs (se 2 (by rfl) ⟨312948, by rfl⟩) R625897
theorem R179273 : Reach 179273 := rs (se 2 (by rfl) ⟨67227, by rfl⟩) R134455
theorem R801899 : Reach 801899 := rs (se 1 (by rfl) ⟨601424, by rfl⟩) R1202849
theorem R148819 : Reach 148819 := rs (se 1 (by rfl) ⟨111614, by rfl⟩) R223229
theorem R15943229 : Reach 15943229 := rs (se 3 (by rfl) ⟨2989355, by rfl⟩) R5978711
theorem R85951 : Reach 85951 := rs (se 1 (by rfl) ⟨64463, by rfl⟩) R128927
theorem R382589 : Reach 382589 := rs (se 3 (by rfl) ⟨71735, by rfl⟩) R143471
theorem R481609 : Reach 481609 := rs (se 2 (by rfl) ⟨180603, by rfl⟩) R361207
theorem R154943 : Reach 154943 := rs (se 1 (by rfl) ⟨116207, by rfl⟩) R232415
theorem R549089 : Reach 549089 := rs (se 2 (by rfl) ⟨205908, by rfl⟩) R411817
theorem R386279 : Reach 386279 := rs (se 1 (by rfl) ⟨289709, by rfl⟩) R579419
theorem R255487 : Reach 255487 := rs (se 1 (by rfl) ⟨191615, by rfl⟩) R383231
theorem R157769 : Reach 157769 := rs (se 2 (by rfl) ⟨59163, by rfl⟩) R118327
theorem R683063 : Reach 683063 := rs (se 1 (by rfl) ⟨512297, by rfl⟩) R1024595
theorem R225767 : Reach 225767 := rs (se 1 (by rfl) ⟨169325, by rfl⟩) R338651
theorem R849527 : Reach 849527 := rs (se 1 (by rfl) ⟨637145, by rfl⟩) R1274291
theorem R259775 : Reach 259775 := rs (se 1 (by rfl) ⟨194831, by rfl⟩) R389663
theorem R261103 : Reach 261103 := rs (se 1 (by rfl) ⟨195827, by rfl⟩) R391655
theorem R195817 : Reach 195817 := rs (se 2 (by rfl) ⟨73431, by rfl⟩) R146863
theorem R262379 : Reach 262379 := rs (se 1 (by rfl) ⟨196784, by rfl⟩) R393569
theorem R198425 : Reach 198425 := rs (se 2 (by rfl) ⟨74409, by rfl⟩) R148819
theorem R75171685 : Reach 75171685 := rs (se 4 (by rfl) ⟨7047345, by rfl⟩) R14094691
theorem R460859 : Reach 460859 := rs (se 1 (by rfl) ⟨345644, by rfl⟩) R691289
theorem R3606605 : Reach 3606605 := rs (se 3 (by rfl) ⟨676238, by rfl⟩) R1352477
theorem R67995 : Reach 67995 := rs (se 1 (by rfl) ⟨50996, by rfl⟩) R101993
theorem R199223 : Reach 199223 := rs (se 1 (by rfl) ⟨149417, by rfl⟩) R298835
theorem R68719 : Reach 68719 := rs (se 1 (by rfl) ⟨51539, by rfl⟩) R103079
theorem R70271 : Reach 70271 := rs (se 1 (by rfl) ⟨52703, by rfl⟩) R105407
theorem R266921 : Reach 266921 := rs (se 2 (by rfl) ⟨100095, by rfl⟩) R200191
theorem R103295 : Reach 103295 := rs (se 1 (by rfl) ⟨77471, by rfl⟩) R154943
theorem R70591 : Reach 70591 := rs (se 1 (by rfl) ⟨52943, by rfl⟩) R105887
theorem R70683 : Reach 70683 := rs (se 1 (by rfl) ⟨53012, by rfl⟩) R106025
theorem R332903 : Reach 332903 := rs (se 1 (by rfl) ⟨249677, by rfl⟩) R499355
theorem R71103 : Reach 71103 := rs (se 1 (by rfl) ⟨53327, by rfl⟩) R106655
theorem R366059 : Reach 366059 := rs (se 1 (by rfl) ⟨274544, by rfl⟩) R549089
theorem R399401 : Reach 399401 := rs (se 2 (by rfl) ⟨149775, by rfl⟩) R299551
theorem R105179 : Reach 105179 := rs (se 1 (by rfl) ⟨78884, by rfl⟩) R157769
theorem R566351 : Reach 566351 := rs (se 1 (by rfl) ⟨424763, by rfl⟩) R849527
theorem R173183 : Reach 173183 := rs (se 1 (by rfl) ⟨129887, by rfl⟩) R259775
theorem R534599 : Reach 534599 := rs (se 1 (by rfl) ⟨400949, by rfl⟩) R801899
theorem R10628819 : Reach 10628819 := rs (se 1 (by rfl) ⟨7971614, by rfl⟩) R15943229
theorem R176327 : Reach 176327 := rs (se 1 (by rfl) ⟨132245, by rfl⟩) R264491
theorem R2568581 : Reach 2568581 := rs (se 4 (by rfl) ⟨240804, by rfl⟩) R481609
theorem R340649 : Reach 340649 := rs (se 2 (by rfl) ⟨127743, by rfl⟩) R255487
theorem R439177 : Reach 439177 := rs (se 2 (by rfl) ⟨164691, by rfl⟩) R329383
theorem R113255 : Reach 113255 := rs (se 1 (by rfl) ⟨84941, by rfl⟩) R169883
theorem R114601 : Reach 114601 := rs (se 2 (by rfl) ⟨42975, by rfl⟩) R85951
theorem R150511 : Reach 150511 := rs (se 1 (by rfl) ⟨112883, by rfl⟩) R225767
theorem R117787 : Reach 117787 := rs (se 1 (by rfl) ⟨88340, by rfl⟩) R176681
theorem R348137 : Reach 348137 := rs (se 2 (by rfl) ⟨130551, by rfl⟩) R261103
theorem R119515 : Reach 119515 := rs (se 1 (by rfl) ⟨89636, by rfl⟩) R179273
theorem R2777723 : Reach 2777723 := rs (se 1 (by rfl) ⟨2083292, by rfl⟩) R4166585
theorem R287387 : Reach 287387 := rs (se 1 (by rfl) ⟨215540, by rfl⟩) R431081
theorem R255059 : Reach 255059 := rs (se 1 (by rfl) ⟨191294, by rfl⟩) R382589
theorem R157031 : Reach 157031 := rs (se 1 (by rfl) ⟨117773, by rfl⟩) R235547
theorem R583033 : Reach 583033 := rs (se 2 (by rfl) ⟨218637, by rfl⟩) R437275
theorem R355103 : Reach 355103 := rs (se 1 (by rfl) ⟨266327, by rfl⟩) R532655
theorem R257519 : Reach 257519 := rs (se 1 (by rfl) ⟨193139, by rfl⟩) R386279
theorem R225011 : Reach 225011 := rs (se 1 (by rfl) ⟨168758, by rfl⟩) R337517
theorem R159515 : Reach 159515 := rs (se 1 (by rfl) ⟨119636, by rfl⟩) R239273
theorem R356543 : Reach 356543 := rs (se 1 (by rfl) ⟨267407, by rfl⟩) R534815
theorem R455375 : Reach 455375 := rs (se 1 (by rfl) ⟨341531, by rfl⟩) R683063
theorem R1112705 : Reach 1112705 := rs (se 2 (by rfl) ⟨417264, by rfl⟩) R834529
theorem R261089 : Reach 261089 := rs (se 2 (by rfl) ⟨97908, by rfl⟩) R195817
theorem R4915829 : Reach 4915829 := rs (se 5 (by rfl) ⟨230429, by rfl⟩) R460859
theorem R132283 : Reach 132283 := rs (se 1 (by rfl) ⟨99212, by rfl⟩) R198425
theorem R132815 : Reach 132815 := rs (se 1 (by rfl) ⟨99611, by rfl⟩) R199223
theorem R3803125 : Reach 3803125 := rs (se 5 (by rfl) ⟨178271, by rfl⟩) R356543
theorem R232091 : Reach 232091 := rs (se 1 (by rfl) ⟨174068, by rfl⟩) R348137
theorem R68863 : Reach 68863 := rs (se 1 (by rfl) ⟨51647, by rfl⟩) R103295
theorem R200681 : Reach 200681 := rs (se 2 (by rfl) ⟨75255, by rfl⟩) R150511
theorem R266267 : Reach 266267 := rs (se 1 (by rfl) ⟨199700, by rfl⟩) R399401
theorem R70119 : Reach 70119 := rs (se 1 (by rfl) ⟨52589, by rfl⟩) R105179
theorem R170039 : Reach 170039 := rs (se 1 (by rfl) ⟨127529, by rfl⟩) R255059
theorem R104687 : Reach 104687 := rs (se 1 (by rfl) ⟨78515, by rfl⟩) R157031
theorem R236735 : Reach 236735 := rs (se 1 (by rfl) ⟨177551, by rfl⟩) R355103
theorem R171679 : Reach 171679 := rs (se 1 (by rfl) ⟨128759, by rfl⟩) R257519
theorem R7085879 : Reach 7085879 := rs (se 1 (by rfl) ⟨5314409, by rfl⟩) R10628819
theorem R106343 : Reach 106343 := rs (se 1 (by rfl) ⟨79757, by rfl⟩) R159515
theorem R1712387 : Reach 1712387 := rs (se 1 (by rfl) ⟨1284290, by rfl⟩) R2568581
theorem R303583 : Reach 303583 := rs (se 1 (by rfl) ⟨227687, by rfl⟩) R455375
theorem R75503 : Reach 75503 := rs (se 1 (by rfl) ⟨56627, by rfl⟩) R113255
theorem R174059 : Reach 174059 := rs (se 1 (by rfl) ⟨130544, by rfl⟩) R261089
theorem R174919 : Reach 174919 := rs (se 1 (by rfl) ⟨131189, by rfl⟩) R262379
theorem R1847285 : Reach 1847285 := rs (se 5 (by rfl) ⟨86591, by rfl⟩) R173183
theorem R2404403 : Reach 2404403 := rs (se 1 (by rfl) ⟨1803302, by rfl⟩) R3606605
theorem R177947 : Reach 177947 := rs (se 1 (by rfl) ⟨133460, by rfl⟩) R266921
theorem R244039 : Reach 244039 := rs (se 1 (by rfl) ⟨183029, by rfl⟩) R366059
theorem R1851815 : Reach 1851815 := rs (se 1 (by rfl) ⟨1388861, by rfl⟩) R2777723
theorem R377567 : Reach 377567 := rs (se 1 (by rfl) ⟨283175, by rfl⟩) R566351
theorem R150007 : Reach 150007 := rs (se 1 (by rfl) ⟨112505, by rfl⟩) R225011
theorem R117551 : Reach 117551 := rs (se 1 (by rfl) ⟨88163, by rfl⟩) R176327
theorem R741803 : Reach 741803 := rs (se 1 (by rfl) ⟨556352, by rfl⟩) R1112705
theorem R152801 : Reach 152801 := rs (se 2 (by rfl) ⟨57300, by rfl⟩) R114601
theorem R777377 : Reach 777377 := rs (se 2 (by rfl) ⟨291516, by rfl⟩) R583033
theorem R100228913 : Reach 100228913 := rs (se 2 (by rfl) ⟨37585842, by rfl⟩) R75171685
theorem R221935 : Reach 221935 := rs (se 1 (by rfl) ⟨166451, by rfl⟩) R332903
theorem R157049 : Reach 157049 := rs (se 2 (by rfl) ⟨58893, by rfl⟩) R117787
theorem R191591 : Reach 191591 := rs (se 1 (by rfl) ⟨143693, by rfl⟩) R287387
theorem R159353 : Reach 159353 := rs (se 2 (by rfl) ⟨59757, by rfl⟩) R119515
theorem R585569 : Reach 585569 := rs (se 2 (by rfl) ⟨219588, by rfl⟩) R439177
theorem R356399 : Reach 356399 := rs (se 1 (by rfl) ⟨267299, by rfl⟩) R534599
theorem R227099 : Reach 227099 := rs (se 1 (by rfl) ⟨170324, by rfl⟩) R340649
theorem R3277219 : Reach 3277219 := rs (se 1 (by rfl) ⟨2457914, by rfl⟩) R4915829
theorem R295913 : Reach 295913 := rs (se 2 (by rfl) ⟨110967, by rfl⟩) R221935
theorem R200009 : Reach 200009 := rs (se 2 (by rfl) ⟨75003, by rfl⟩) R150007
theorem R101867 : Reach 101867 := rs (se 1 (by rfl) ⟨76400, by rfl⟩) R152801
theorem R233225 : Reach 233225 := rs (se 2 (by rfl) ⟨87459, by rfl⟩) R174919
theorem R69791 : Reach 69791 := rs (se 1 (by rfl) ⟨52343, by rfl⟩) R104687
theorem R201341 : Reach 201341 := rs (se 3 (by rfl) ⟨37751, by rfl⟩) R75503
theorem R66819275 : Reach 66819275 := rs (se 1 (by rfl) ⟨50114456, by rfl⟩) R100228913
theorem R4723919 : Reach 4723919 := rs (se 1 (by rfl) ⟨3542939, by rfl⟩) R7085879
theorem R70895 : Reach 70895 := rs (se 1 (by rfl) ⟨53171, by rfl⟩) R106343
theorem R104699 : Reach 104699 := rs (se 1 (by rfl) ⟨78524, by rfl⟩) R157049
theorem R106235 : Reach 106235 := rs (se 1 (by rfl) ⟨79676, by rfl⟩) R159353
theorem R237599 : Reach 237599 := rs (se 1 (by rfl) ⟨178199, by rfl⟩) R356399
theorem R404777 : Reach 404777 := rs (se 2 (by rfl) ⟨151791, by rfl⟩) R303583
theorem R4566365 : Reach 4566365 := rs (se 3 (by rfl) ⟨856193, by rfl⟩) R1712387
theorem R1978141 : Reach 1978141 := rs (se 3 (by rfl) ⟨370901, by rfl⟩) R741803
theorem R176377 : Reach 176377 := rs (se 2 (by rfl) ⟨66141, by rfl⟩) R132283
theorem R78367 : Reach 78367 := rs (se 1 (by rfl) ⟨58775, by rfl⟩) R117551
theorem R177511 : Reach 177511 := rs (se 1 (by rfl) ⟨133133, by rfl⟩) R266267
theorem R113359 : Reach 113359 := rs (se 1 (by rfl) ⟨85019, by rfl⟩) R170039
theorem R116039 : Reach 116039 := rs (se 1 (by rfl) ⟨87029, by rfl⟩) R174059
theorem R133787 : Reach 133787 := rs (se 1 (by rfl) ⟨100340, by rfl⟩) R200681
theorem R1231523 : Reach 1231523 := rs (se 1 (by rfl) ⟨923642, by rfl⟩) R1847285
theorem R118631 : Reach 118631 := rs (se 1 (by rfl) ⟨88973, by rfl⟩) R177947
theorem R151399 : Reach 151399 := rs (se 1 (by rfl) ⟨113549, by rfl⟩) R227099
theorem R1234543 : Reach 1234543 := rs (se 1 (by rfl) ⟨925907, by rfl⟩) R1851815
theorem R251711 : Reach 251711 := rs (se 1 (by rfl) ⟨188783, by rfl⟩) R377567
theorem R88543 : Reach 88543 := rs (se 1 (by rfl) ⟨66407, by rfl⟩) R132815
theorem R154727 : Reach 154727 := rs (se 1 (by rfl) ⟨116045, by rfl⟩) R232091
theorem R5070833 : Reach 5070833 := rs (se 2 (by rfl) ⟨1901562, by rfl⟩) R3803125
theorem R518251 : Reach 518251 := rs (se 1 (by rfl) ⟨388688, by rfl⟩) R777377
theorem R157823 : Reach 157823 := rs (se 1 (by rfl) ⟨118367, by rfl⟩) R236735
theorem R127727 : Reach 127727 := rs (se 1 (by rfl) ⟨95795, by rfl⟩) R191591
theorem R390379 : Reach 390379 := rs (se 1 (by rfl) ⟨292784, by rfl⟩) R585569
theorem R1602935 : Reach 1602935 := rs (se 1 (by rfl) ⟨1202201, by rfl⟩) R2404403
theorem R325385 : Reach 325385 := rs (se 2 (by rfl) ⟨122019, by rfl⟩) R244039
theorem R228905 : Reach 228905 := rs (se 2 (by rfl) ⟨85839, by rfl⟩) R171679
theorem R197275 : Reach 197275 := rs (se 1 (by rfl) ⟨147956, by rfl⟩) R295913
theorem R821015 : Reach 821015 := rs (se 1 (by rfl) ⟨615761, by rfl⟩) R1231523
theorem R133339 : Reach 133339 := rs (se 1 (by rfl) ⟨100004, by rfl⟩) R200009
theorem R67911 : Reach 67911 := rs (se 1 (by rfl) ⟨50933, by rfl⟩) R101867
theorem R691001 : Reach 691001 := rs (se 2 (by rfl) ⟨259125, by rfl⟩) R518251
theorem R134227 : Reach 134227 := rs (se 1 (by rfl) ⟨100670, by rfl⟩) R201341
theorem R3149279 : Reach 3149279 := rs (se 1 (by rfl) ⟨2361959, by rfl⟩) R4723919
theorem R167807 : Reach 167807 := rs (se 1 (by rfl) ⟨125855, by rfl⟩) R251711
theorem R69799 : Reach 69799 := rs (se 1 (by rfl) ⟨52349, by rfl⟩) R104699
theorem R103151 : Reach 103151 := rs (se 1 (by rfl) ⟨77363, by rfl⟩) R154727
theorem R201865 : Reach 201865 := rs (se 2 (by rfl) ⟨75699, by rfl⟩) R151399
theorem R70823 : Reach 70823 := rs (se 1 (by rfl) ⟨53117, by rfl⟩) R106235
theorem R3380555 : Reach 3380555 := rs (se 1 (by rfl) ⟨2535416, by rfl⟩) R5070833
theorem R235169 : Reach 235169 := rs (se 2 (by rfl) ⟨88188, by rfl⟩) R176377
theorem R104489 : Reach 104489 := rs (se 2 (by rfl) ⟨39183, by rfl⟩) R78367
theorem R105215 : Reach 105215 := rs (se 1 (by rfl) ⟨78911, by rfl⟩) R157823
theorem R236681 : Reach 236681 := rs (se 2 (by rfl) ⟨88755, by rfl⟩) R177511
theorem R1646057 : Reach 1646057 := rs (se 2 (by rfl) ⟨617271, by rfl⟩) R1234543
theorem R269851 : Reach 269851 := rs (se 1 (by rfl) ⟨202388, by rfl⟩) R404777
theorem R4369625 : Reach 4369625 := rs (se 2 (by rfl) ⟨1638609, by rfl⟩) R3277219
theorem R77359 : Reach 77359 := rs (se 1 (by rfl) ⟨58019, by rfl⟩) R116039
theorem R79087 : Reach 79087 := rs (se 1 (by rfl) ⟨59315, by rfl⟩) R118631
theorem R44546183 : Reach 44546183 := rs (se 1 (by rfl) ⟨33409637, by rfl⟩) R66819275
theorem R2637521 : Reach 2637521 := rs (se 2 (by rfl) ⟨989070, by rfl⟩) R1978141
theorem R85151 : Reach 85151 := rs (se 1 (by rfl) ⟨63863, by rfl⟩) R127727
theorem R118057 : Reach 118057 := rs (se 2 (by rfl) ⟨44271, by rfl⟩) R88543
theorem R1068623 : Reach 1068623 := rs (se 1 (by rfl) ⟨801467, by rfl⟩) R1602935
theorem R151145 : Reach 151145 := rs (se 2 (by rfl) ⟨56679, by rfl⟩) R113359
theorem R216923 : Reach 216923 := rs (se 1 (by rfl) ⟨162692, by rfl⟩) R325385
theorem R152603 : Reach 152603 := rs (se 1 (by rfl) ⟨114452, by rfl⟩) R228905
theorem R89191 : Reach 89191 := rs (se 1 (by rfl) ⟨66893, by rfl⟩) R133787
theorem R155483 : Reach 155483 := rs (se 1 (by rfl) ⟨116612, by rfl⟩) R233225
theorem R158399 : Reach 158399 := rs (se 1 (by rfl) ⟨118799, by rfl⟩) R237599
theorem R520505 : Reach 520505 := rs (se 2 (by rfl) ⟨195189, by rfl⟩) R390379
theorem R3044243 : Reach 3044243 := rs (se 1 (by rfl) ⟨2283182, by rfl⟩) R4566365
theorem R263033 : Reach 263033 := rs (se 2 (by rfl) ⟨98637, by rfl⟩) R197275
theorem R460667 : Reach 460667 := rs (se 1 (by rfl) ⟨345500, by rfl⟩) R691001
theorem R2099519 : Reach 2099519 := rs (se 1 (by rfl) ⟨1574639, by rfl⟩) R3149279
theorem R100763 : Reach 100763 := rs (se 1 (by rfl) ⟨75572, by rfl⟩) R151145
theorem R68767 : Reach 68767 := rs (se 1 (by rfl) ⟨51575, by rfl⟩) R103151
theorem R101735 : Reach 101735 := rs (se 1 (by rfl) ⟨76301, by rfl⟩) R152603
theorem R69659 : Reach 69659 := rs (se 1 (by rfl) ⟨52244, by rfl⟩) R104489
theorem R70143 : Reach 70143 := rs (se 1 (by rfl) ⟨52607, by rfl⟩) R105215
theorem R103145 : Reach 103145 := rs (se 2 (by rfl) ⟨38679, by rfl⟩) R77359
theorem R103655 : Reach 103655 := rs (se 1 (by rfl) ⟨77741, by rfl⟩) R155483
theorem R269153 : Reach 269153 := rs (se 2 (by rfl) ⟨100932, by rfl⟩) R201865
theorem R105449 : Reach 105449 := rs (se 2 (by rfl) ⟨39543, by rfl⟩) R79087
theorem R105599 : Reach 105599 := rs (se 1 (by rfl) ⟨79199, by rfl⟩) R158399
theorem R29697455 : Reach 29697455 := rs (se 1 (by rfl) ⟨22273091, by rfl⟩) R44546183
theorem R111871 : Reach 111871 := rs (se 1 (by rfl) ⟨83903, by rfl⟩) R167807
theorem R177785 : Reach 177785 := rs (se 2 (by rfl) ⟨66669, by rfl⟩) R133339
theorem R178969 : Reach 178969 := rs (se 2 (by rfl) ⟨67113, by rfl⟩) R134227
theorem R1097371 : Reach 1097371 := rs (se 1 (by rfl) ⟨823028, by rfl⟩) R1646057
theorem R347003 : Reach 347003 := rs (se 1 (by rfl) ⟨260252, by rfl⟩) R520505
theorem R118921 : Reach 118921 := rs (se 2 (by rfl) ⟨44595, by rfl⟩) R89191
theorem R578461 : Reach 578461 := rs (se 3 (by rfl) ⟨108461, by rfl⟩) R216923
theorem R1758347 : Reach 1758347 := rs (se 1 (by rfl) ⟨1318760, by rfl⟩) R2637521
theorem R547343 : Reach 547343 := rs (se 1 (by rfl) ⟨410507, by rfl⟩) R821015
theorem R712415 : Reach 712415 := rs (se 1 (by rfl) ⟨534311, by rfl⟩) R1068623
theorem R2253703 : Reach 2253703 := rs (se 1 (by rfl) ⟨1690277, by rfl⟩) R3380555
theorem R156779 : Reach 156779 := rs (se 1 (by rfl) ⟨117584, by rfl⟩) R235169
theorem R157409 : Reach 157409 := rs (se 2 (by rfl) ⟨59028, by rfl⟩) R118057
theorem R157787 : Reach 157787 := rs (se 1 (by rfl) ⟨118340, by rfl⟩) R236681
theorem R2913083 : Reach 2913083 := rs (se 1 (by rfl) ⟨2184812, by rfl⟩) R4369625
theorem R227069 : Reach 227069 := rs (se 3 (by rfl) ⟨42575, by rfl⟩) R85151
theorem R2029495 : Reach 2029495 := rs (se 1 (by rfl) ⟨1522121, by rfl⟩) R3044243
theorem R359801 : Reach 359801 := rs (se 2 (by rfl) ⟨134925, by rfl⟩) R269851
theorem R67175 : Reach 67175 := rs (se 1 (by rfl) ⟨50381, by rfl⟩) R100763
theorem R231335 : Reach 231335 := rs (se 1 (by rfl) ⟨173501, by rfl⟩) R347003
theorem R67823 : Reach 67823 := rs (se 1 (by rfl) ⟨50867, by rfl⟩) R101735
theorem R68763 : Reach 68763 := rs (se 1 (by rfl) ⟨51572, by rfl⟩) R103145
theorem R69103 : Reach 69103 := rs (se 1 (by rfl) ⟨51827, by rfl⟩) R103655
theorem R364895 : Reach 364895 := rs (se 1 (by rfl) ⟨273671, by rfl⟩) R547343
theorem R70299 : Reach 70299 := rs (se 1 (by rfl) ⟨52724, by rfl⟩) R105449
theorem R70399 : Reach 70399 := rs (se 1 (by rfl) ⟨52799, by rfl⟩) R105599
theorem R104519 : Reach 104519 := rs (se 1 (by rfl) ⟨78389, by rfl⟩) R156779
theorem R104939 : Reach 104939 := rs (se 1 (by rfl) ⟨78704, by rfl⟩) R157409
theorem R105191 : Reach 105191 := rs (se 1 (by rfl) ⟨78893, by rfl⟩) R157787
theorem R1942055 : Reach 1942055 := rs (se 1 (by rfl) ⟨1456541, by rfl⟩) R2913083
theorem R238625 : Reach 238625 := rs (se 2 (by rfl) ⟨89484, by rfl⟩) R178969
theorem R239867 : Reach 239867 := rs (se 1 (by rfl) ⟨179900, by rfl⟩) R359801
theorem R175355 : Reach 175355 := rs (se 1 (by rfl) ⟨131516, by rfl⟩) R263033
theorem R307111 : Reach 307111 := rs (se 1 (by rfl) ⟨230333, by rfl⟩) R460667
theorem R179435 : Reach 179435 := rs (se 1 (by rfl) ⟨134576, by rfl⟩) R269153
theorem R771281 : Reach 771281 := rs (se 2 (by rfl) ⟨289230, by rfl⟩) R578461
theorem R149161 : Reach 149161 := rs (se 2 (by rfl) ⟨55935, by rfl⟩) R111871
theorem R2705993 : Reach 2705993 := rs (se 2 (by rfl) ⟨1014747, by rfl⟩) R2029495
theorem R5852645 : Reach 5852645 := rs (se 4 (by rfl) ⟨548685, by rfl⟩) R1097371
theorem R118523 : Reach 118523 := rs (se 1 (by rfl) ⟨88892, by rfl⟩) R177785
theorem R151379 : Reach 151379 := rs (se 1 (by rfl) ⟨113534, by rfl⟩) R227069
theorem R3004937 : Reach 3004937 := rs (se 2 (by rfl) ⟨1126851, by rfl⟩) R2253703
theorem R1399679 : Reach 1399679 := rs (se 1 (by rfl) ⟨1049759, by rfl⟩) R2099519
theorem R1172231 : Reach 1172231 := rs (se 1 (by rfl) ⟨879173, by rfl⟩) R1758347
theorem R79193213 : Reach 79193213 := rs (se 3 (by rfl) ⟨14848727, by rfl⟩) R29697455
theorem R158561 : Reach 158561 := rs (se 2 (by rfl) ⟨59460, by rfl⟩) R118921
theorem R1899773 : Reach 1899773 := rs (se 3 (by rfl) ⟨356207, by rfl⟩) R712415
theorem R1803995 : Reach 1803995 := rs (se 1 (by rfl) ⟨1352996, by rfl⟩) R2705993
theorem R198881 : Reach 198881 := rs (se 2 (by rfl) ⟨74580, by rfl⟩) R149161
theorem R3901763 : Reach 3901763 := rs (se 1 (by rfl) ⟨2926322, by rfl⟩) R5852645
theorem R100919 : Reach 100919 := rs (se 1 (by rfl) ⟨75689, by rfl⟩) R151379
theorem R69679 : Reach 69679 := rs (se 1 (by rfl) ⟨52259, by rfl⟩) R104519
theorem R69959 : Reach 69959 := rs (se 1 (by rfl) ⟨52469, by rfl⟩) R104939
theorem R2003291 : Reach 2003291 := rs (se 1 (by rfl) ⟨1502468, by rfl⟩) R3004937
theorem R70127 : Reach 70127 := rs (se 1 (by rfl) ⟨52595, by rfl⟩) R105191
theorem R52795475 : Reach 52795475 := rs (se 1 (by rfl) ⟨39596606, by rfl⟩) R79193213
theorem R105707 : Reach 105707 := rs (se 1 (by rfl) ⟨79280, by rfl⟩) R158561
theorem R79015 : Reach 79015 := rs (se 1 (by rfl) ⟨59261, by rfl⟩) R118523
theorem R243263 : Reach 243263 := rs (se 1 (by rfl) ⟨182447, by rfl⟩) R364895
theorem R933119 : Reach 933119 := rs (se 1 (by rfl) ⟨699839, by rfl⟩) R1399679
theorem R409481 : Reach 409481 := rs (se 2 (by rfl) ⟨153555, by rfl⟩) R307111
theorem R1294703 : Reach 1294703 := rs (se 1 (by rfl) ⟨971027, by rfl⟩) R1942055
theorem R116903 : Reach 116903 := rs (se 1 (by rfl) ⟨87677, by rfl⟩) R175355
theorem R119623 : Reach 119623 := rs (se 1 (by rfl) ⟨89717, by rfl⟩) R179435
theorem R1266515 : Reach 1266515 := rs (se 1 (by rfl) ⟨949886, by rfl⟩) R1899773
theorem R514187 : Reach 514187 := rs (se 1 (by rfl) ⟨385640, by rfl⟩) R771281
theorem R154223 : Reach 154223 := rs (se 1 (by rfl) ⟨115667, by rfl⟩) R231335
theorem R781487 : Reach 781487 := rs (se 1 (by rfl) ⟨586115, by rfl⟩) R1172231
theorem R159083 : Reach 159083 := rs (se 1 (by rfl) ⟨119312, by rfl⟩) R238625
theorem R159911 : Reach 159911 := rs (se 1 (by rfl) ⟨119933, by rfl⟩) R239867
theorem R132587 : Reach 132587 := rs (se 1 (by rfl) ⟨99440, by rfl⟩) R198881
theorem R67279 : Reach 67279 := rs (se 1 (by rfl) ⟨50459, by rfl⟩) R100919
theorem R35196983 : Reach 35196983 := rs (se 1 (by rfl) ⟨26397737, by rfl⟩) R52795475
theorem R102815 : Reach 102815 := rs (se 1 (by rfl) ⟨77111, by rfl⟩) R154223
theorem R70471 : Reach 70471 := rs (se 1 (by rfl) ⟨52853, by rfl⟩) R105707
theorem R105353 : Reach 105353 := rs (se 2 (by rfl) ⟨39507, by rfl⟩) R79015
theorem R106055 : Reach 106055 := rs (se 1 (by rfl) ⟨79541, by rfl⟩) R159083
theorem R106607 : Reach 106607 := rs (se 1 (by rfl) ⟨79955, by rfl⟩) R159911
theorem R272987 : Reach 272987 := rs (se 1 (by rfl) ⟨204740, by rfl⟩) R409481
theorem R863135 : Reach 863135 := rs (se 1 (by rfl) ⟨647351, by rfl⟩) R1294703
theorem R77935 : Reach 77935 := rs (se 1 (by rfl) ⟨58451, by rfl⟩) R116903
theorem R2601175 : Reach 2601175 := rs (se 1 (by rfl) ⟨1950881, by rfl⟩) R3901763
theorem R342791 : Reach 342791 := rs (se 1 (by rfl) ⟨257093, by rfl⟩) R514187
theorem R1202663 : Reach 1202663 := rs (se 1 (by rfl) ⟨901997, by rfl⟩) R1803995
theorem R1335527 : Reach 1335527 := rs (se 1 (by rfl) ⟨1001645, by rfl⟩) R2003291
theorem R844343 : Reach 844343 := rs (se 1 (by rfl) ⟨633257, by rfl⟩) R1266515
theorem R159497 : Reach 159497 := rs (se 2 (by rfl) ⟨59811, by rfl⟩) R119623
theorem R520991 : Reach 520991 := rs (se 1 (by rfl) ⟨390743, by rfl⟩) R781487
theorem R162175 : Reach 162175 := rs (se 1 (by rfl) ⟨121631, by rfl⟩) R243263
theorem R622079 : Reach 622079 := rs (se 1 (by rfl) ⟨466559, by rfl⟩) R933119
theorem R23464655 : Reach 23464655 := rs (se 1 (by rfl) ⟨17598491, by rfl⟩) R35196983
theorem R68543 : Reach 68543 := rs (se 1 (by rfl) ⟨51407, by rfl⟩) R102815
theorem R70235 : Reach 70235 := rs (se 1 (by rfl) ⟨52676, by rfl⟩) R105353
theorem R70703 : Reach 70703 := rs (se 1 (by rfl) ⟨53027, by rfl⟩) R106055
theorem R71071 : Reach 71071 := rs (se 1 (by rfl) ⟨53303, by rfl⟩) R106607
theorem R103913 : Reach 103913 := rs (se 2 (by rfl) ⟨38967, by rfl⟩) R77935
theorem R890351 : Reach 890351 := rs (se 1 (by rfl) ⟨667763, by rfl⟩) R1335527
theorem R562895 : Reach 562895 := rs (se 1 (by rfl) ⟨422171, by rfl⟩) R844343
theorem R106331 : Reach 106331 := rs (se 1 (by rfl) ⟨79748, by rfl⟩) R159497
theorem R801775 : Reach 801775 := rs (se 1 (by rfl) ⟨601331, by rfl⟩) R1202663
theorem R181991 : Reach 181991 := rs (se 1 (by rfl) ⟨136493, by rfl⟩) R272987
theorem R575423 : Reach 575423 := rs (se 1 (by rfl) ⟨431567, by rfl⟩) R863135
theorem R216233 : Reach 216233 := rs (se 2 (by rfl) ⟨81087, by rfl⟩) R162175
theorem R347327 : Reach 347327 := rs (se 1 (by rfl) ⟨260495, by rfl⟩) R520991
theorem R414719 : Reach 414719 := rs (se 1 (by rfl) ⟨311039, by rfl⟩) R622079
theorem R88391 : Reach 88391 := rs (se 1 (by rfl) ⟨66293, by rfl⟩) R132587
theorem R3468233 : Reach 3468233 := rs (se 2 (by rfl) ⟨1300587, by rfl⟩) R2601175
theorem R228527 : Reach 228527 := rs (se 1 (by rfl) ⟨171395, by rfl⟩) R342791
theorem R231551 : Reach 231551 := rs (se 1 (by rfl) ⟨173663, by rfl⟩) R347327
theorem R69275 : Reach 69275 := rs (se 1 (by rfl) ⟨51956, by rfl⟩) R103913
theorem R593567 : Reach 593567 := rs (se 1 (by rfl) ⟨445175, by rfl⟩) R890351
theorem R70887 : Reach 70887 := rs (se 1 (by rfl) ⟨53165, by rfl⟩) R106331
theorem R235709 : Reach 235709 := rs (se 3 (by rfl) ⟨44195, by rfl⟩) R88391
theorem R15643103 : Reach 15643103 := rs (se 1 (by rfl) ⟨11732327, by rfl⟩) R23464655
theorem R144155 : Reach 144155 := rs (se 1 (by rfl) ⟨108116, by rfl⟩) R216233
theorem R276479 : Reach 276479 := rs (se 1 (by rfl) ⟨207359, by rfl⟩) R414719
theorem R375263 : Reach 375263 := rs (se 1 (by rfl) ⟨281447, by rfl⟩) R562895
theorem R2312155 : Reach 2312155 := rs (se 1 (by rfl) ⟨1734116, by rfl⟩) R3468233
theorem R1069033 : Reach 1069033 := rs (se 2 (by rfl) ⟨400887, by rfl⟩) R801775
theorem R152351 : Reach 152351 := rs (se 1 (by rfl) ⟨114263, by rfl⟩) R228527
theorem R383615 : Reach 383615 := rs (se 1 (by rfl) ⟨287711, by rfl⟩) R575423
theorem R485309 : Reach 485309 := rs (se 3 (by rfl) ⟨90995, by rfl⟩) R181991
theorem R41714941 : Reach 41714941 := rs (se 3 (by rfl) ⟨7821551, by rfl⟩) R15643103
theorem R395711 : Reach 395711 := rs (se 1 (by rfl) ⟨296783, by rfl⟩) R593567
theorem R3082873 : Reach 3082873 := rs (se 2 (by rfl) ⟨1156077, by rfl⟩) R2312155
theorem R101567 : Reach 101567 := rs (se 1 (by rfl) ⟨76175, by rfl⟩) R152351
theorem R1294157 : Reach 1294157 := rs (se 3 (by rfl) ⟨242654, by rfl⟩) R485309
theorem R1425377 : Reach 1425377 := rs (se 2 (by rfl) ⟨534516, by rfl⟩) R1069033
theorem R184319 : Reach 184319 := rs (se 1 (by rfl) ⟨138239, by rfl⟩) R276479
theorem R250175 : Reach 250175 := rs (se 1 (by rfl) ⟨187631, by rfl⟩) R375263
theorem R154367 : Reach 154367 := rs (se 1 (by rfl) ⟨115775, by rfl⟩) R231551
theorem R157139 : Reach 157139 := rs (se 1 (by rfl) ⟨117854, by rfl⟩) R235709
theorem R255743 : Reach 255743 := rs (se 1 (by rfl) ⟨191807, by rfl⟩) R383615
theorem R96103 : Reach 96103 := rs (se 1 (by rfl) ⟨72077, by rfl⟩) R144155
theorem R263807 : Reach 263807 := rs (se 1 (by rfl) ⟨197855, by rfl⟩) R395711
theorem R67711 : Reach 67711 := rs (se 1 (by rfl) ⟨50783, by rfl⟩) R101567
theorem R102911 : Reach 102911 := rs (se 1 (by rfl) ⟨77183, by rfl⟩) R154367
theorem R104759 : Reach 104759 := rs (se 1 (by rfl) ⟨78569, by rfl⟩) R157139
theorem R170495 : Reach 170495 := rs (se 1 (by rfl) ⟨127871, by rfl⟩) R255743
theorem R862771 : Reach 862771 := rs (se 1 (by rfl) ⟨647078, by rfl⟩) R1294157
theorem R667133 : Reach 667133 := rs (se 3 (by rfl) ⟨125087, by rfl⟩) R250175
theorem R55619921 : Reach 55619921 := rs (se 2 (by rfl) ⟨20857470, by rfl⟩) R41714941
theorem R4110497 : Reach 4110497 := rs (se 2 (by rfl) ⟨1541436, by rfl⟩) R3082873
theorem R122879 : Reach 122879 := rs (se 1 (by rfl) ⟨92159, by rfl⟩) R184319
theorem R128137 : Reach 128137 := rs (se 2 (by rfl) ⟨48051, by rfl⟩) R96103
theorem R3801005 : Reach 3801005 := rs (se 3 (by rfl) ⟨712688, by rfl⟩) R1425377
theorem R68607 : Reach 68607 := rs (se 1 (by rfl) ⟨51455, by rfl⟩) R102911
theorem R1150361 : Reach 1150361 := rs (se 2 (by rfl) ⟨431385, by rfl⟩) R862771
theorem R69839 : Reach 69839 := rs (se 1 (by rfl) ⟨52379, by rfl⟩) R104759
theorem R170849 : Reach 170849 := rs (se 2 (by rfl) ⟨64068, by rfl⟩) R128137
theorem R2534003 : Reach 2534003 := rs (se 1 (by rfl) ⟨1900502, by rfl⟩) R3801005
theorem R175871 : Reach 175871 := rs (se 1 (by rfl) ⟨131903, by rfl⟩) R263807
theorem R113663 : Reach 113663 := rs (se 1 (by rfl) ⟨85247, by rfl⟩) R170495
theorem R81919 : Reach 81919 := rs (se 1 (by rfl) ⟨61439, by rfl⟩) R122879
theorem R444755 : Reach 444755 := rs (se 1 (by rfl) ⟨333566, by rfl⟩) R667133
theorem R37079947 : Reach 37079947 := rs (se 1 (by rfl) ⟨27809960, by rfl⟩) R55619921
theorem R2740331 : Reach 2740331 := rs (se 1 (by rfl) ⟨2055248, by rfl⟩) R4110497
theorem R296503 : Reach 296503 := rs (se 1 (by rfl) ⟨222377, by rfl⟩) R444755
theorem R197759717 : Reach 197759717 := rs (se 4 (by rfl) ⟨18539973, by rfl⟩) R37079947
theorem R75775 : Reach 75775 := rs (se 1 (by rfl) ⟨56831, by rfl⟩) R113663
theorem R109225 : Reach 109225 := rs (se 2 (by rfl) ⟨40959, by rfl⟩) R81919
theorem R766907 : Reach 766907 := rs (se 1 (by rfl) ⟨575180, by rfl⟩) R1150361
theorem R113899 : Reach 113899 := rs (se 1 (by rfl) ⟨85424, by rfl⟩) R170849
theorem R1689335 : Reach 1689335 := rs (se 1 (by rfl) ⟨1267001, by rfl⟩) R2534003
theorem R117247 : Reach 117247 := rs (se 1 (by rfl) ⟨87935, by rfl⟩) R175871
theorem R1826887 : Reach 1826887 := rs (se 1 (by rfl) ⟨1370165, by rfl⟩) R2740331
theorem R6325397 : Reach 6325397 := rs (se 6 (by rfl) ⟨148251, by rfl⟩) R296503
theorem R101033 : Reach 101033 := rs (se 2 (by rfl) ⟨37887, by rfl⟩) R75775
theorem R2435849 : Reach 2435849 := rs (se 2 (by rfl) ⟨913443, by rfl⟩) R1826887
theorem R1126223 : Reach 1126223 := rs (se 1 (by rfl) ⟨844667, by rfl⟩) R1689335
theorem R131839811 : Reach 131839811 := rs (se 1 (by rfl) ⟨98879858, by rfl⟩) R197759717
theorem R145633 : Reach 145633 := rs (se 2 (by rfl) ⟨54612, by rfl⟩) R109225
theorem R511271 : Reach 511271 := rs (se 1 (by rfl) ⟨383453, by rfl⟩) R766907
theorem R151865 : Reach 151865 := rs (se 2 (by rfl) ⟨56949, by rfl⟩) R113899
theorem R156329 : Reach 156329 := rs (se 2 (by rfl) ⟨58623, by rfl⟩) R117247
theorem R67355 : Reach 67355 := rs (se 1 (by rfl) ⟨50516, by rfl⟩) R101033
theorem R101243 : Reach 101243 := rs (se 1 (by rfl) ⟨75932, by rfl⟩) R151865
theorem R104219 : Reach 104219 := rs (se 1 (by rfl) ⟨78164, by rfl⟩) R156329
theorem R87893207 : Reach 87893207 := rs (se 1 (by rfl) ⟨65919905, by rfl⟩) R131839811
theorem R340847 : Reach 340847 := rs (se 1 (by rfl) ⟨255635, by rfl⟩) R511271
theorem R1623899 : Reach 1623899 := rs (se 1 (by rfl) ⟨1217924, by rfl⟩) R2435849
theorem R4216931 : Reach 4216931 := rs (se 1 (by rfl) ⟨3162698, by rfl⟩) R6325397
theorem R750815 : Reach 750815 := rs (se 1 (by rfl) ⟨563111, by rfl⟩) R1126223
theorem R194177 : Reach 194177 := rs (se 2 (by rfl) ⟨72816, by rfl⟩) R145633
theorem R67495 : Reach 67495 := rs (se 1 (by rfl) ⟨50621, by rfl⟩) R101243
theorem R69479 : Reach 69479 := rs (se 1 (by rfl) ⟨52109, by rfl⟩) R104219
theorem R4330397 : Reach 4330397 := rs (se 3 (by rfl) ⟨811949, by rfl⟩) R1623899
theorem R58595471 : Reach 58595471 := rs (se 1 (by rfl) ⟨43946603, by rfl⟩) R87893207
theorem R500543 : Reach 500543 := rs (se 1 (by rfl) ⟨375407, by rfl⟩) R750815
theorem R2811287 : Reach 2811287 := rs (se 1 (by rfl) ⟨2108465, by rfl⟩) R4216931
theorem R227231 : Reach 227231 := rs (se 1 (by rfl) ⟨170423, by rfl⟩) R340847
theorem R129451 : Reach 129451 := rs (se 1 (by rfl) ⟨97088, by rfl⟩) R194177
theorem R2886931 : Reach 2886931 := rs (se 1 (by rfl) ⟨2165198, by rfl⟩) R4330397
theorem R39063647 : Reach 39063647 := rs (se 1 (by rfl) ⟨29297735, by rfl⟩) R58595471
theorem R333695 : Reach 333695 := rs (se 1 (by rfl) ⟨250271, by rfl⟩) R500543
theorem R1874191 : Reach 1874191 := rs (se 1 (by rfl) ⟨1405643, by rfl⟩) R2811287
theorem R172601 : Reach 172601 := rs (se 2 (by rfl) ⟨64725, by rfl⟩) R129451
theorem R151487 : Reach 151487 := rs (se 1 (by rfl) ⟨113615, by rfl⟩) R227231
theorem R100991 : Reach 100991 := rs (se 1 (by rfl) ⟨75743, by rfl⟩) R151487
theorem R2498921 : Reach 2498921 := rs (se 2 (by rfl) ⟨937095, by rfl⟩) R1874191
theorem R3849241 : Reach 3849241 := rs (se 2 (by rfl) ⟨1443465, by rfl⟩) R2886931
theorem R115067 : Reach 115067 := rs (se 1 (by rfl) ⟨86300, by rfl⟩) R172601
theorem R26042431 : Reach 26042431 := rs (se 1 (by rfl) ⟨19531823, by rfl⟩) R39063647
theorem R222463 : Reach 222463 := rs (se 1 (by rfl) ⟨166847, by rfl⟩) R333695
theorem R296617 : Reach 296617 := rs (se 2 (by rfl) ⟨111231, by rfl⟩) R222463
theorem R67327 : Reach 67327 := rs (se 1 (by rfl) ⟨50495, by rfl⟩) R100991
theorem R76711 : Reach 76711 := rs (se 1 (by rfl) ⟨57533, by rfl⟩) R115067
theorem R5132321 : Reach 5132321 := rs (se 2 (by rfl) ⟨1924620, by rfl⟩) R3849241
theorem R34723241 : Reach 34723241 := rs (se 2 (by rfl) ⟨13021215, by rfl⟩) R26042431
theorem R1665947 : Reach 1665947 := rs (se 1 (by rfl) ⟨1249460, by rfl⟩) R2498921
theorem R395489 : Reach 395489 := rs (se 2 (by rfl) ⟨148308, by rfl⟩) R296617
theorem R102281 : Reach 102281 := rs (se 2 (by rfl) ⟨38355, by rfl⟩) R76711
theorem R3421547 : Reach 3421547 := rs (se 1 (by rfl) ⟨2566160, by rfl⟩) R5132321
theorem R23148827 : Reach 23148827 := rs (se 1 (by rfl) ⟨17361620, by rfl⟩) R34723241
theorem R1110631 : Reach 1110631 := rs (se 1 (by rfl) ⟨832973, by rfl⟩) R1665947
theorem R68187 : Reach 68187 := rs (se 1 (by rfl) ⟨51140, by rfl⟩) R102281
theorem R1054637 : Reach 1054637 := rs (se 3 (by rfl) ⟨197744, by rfl⟩) R395489
theorem R1480841 : Reach 1480841 := rs (se 2 (by rfl) ⟨555315, by rfl⟩) R1110631
theorem R2281031 : Reach 2281031 := rs (se 1 (by rfl) ⟨1710773, by rfl⟩) R3421547
theorem R15432551 : Reach 15432551 := rs (se 1 (by rfl) ⟨11574413, by rfl⟩) R23148827
theorem R987227 : Reach 987227 := rs (se 1 (by rfl) ⟨740420, by rfl⟩) R1480841
theorem R1520687 : Reach 1520687 := rs (se 1 (by rfl) ⟨1140515, by rfl⟩) R2281031
theorem R703091 : Reach 703091 := rs (se 1 (by rfl) ⟨527318, by rfl⟩) R1054637
theorem R10288367 : Reach 10288367 := rs (se 1 (by rfl) ⟨7716275, by rfl⟩) R15432551
theorem R658151 : Reach 658151 := rs (se 1 (by rfl) ⟨493613, by rfl⟩) R987227
theorem R1874909 : Reach 1874909 := rs (se 3 (by rfl) ⟨351545, by rfl⟩) R703091
theorem R6858911 : Reach 6858911 := rs (se 1 (by rfl) ⟨5144183, by rfl⟩) R10288367
theorem R1013791 : Reach 1013791 := rs (se 1 (by rfl) ⟨760343, by rfl⟩) R1520687
theorem R1249939 : Reach 1249939 := rs (se 1 (by rfl) ⟨937454, by rfl⟩) R1874909
theorem R1351721 : Reach 1351721 := rs (se 2 (by rfl) ⟨506895, by rfl⟩) R1013791
theorem R438767 : Reach 438767 := rs (se 1 (by rfl) ⟨329075, by rfl⟩) R658151
theorem R4572607 : Reach 4572607 := rs (se 1 (by rfl) ⟨3429455, by rfl⟩) R6858911
theorem R6096809 : Reach 6096809 := rs (se 2 (by rfl) ⟨2286303, by rfl⟩) R4572607
theorem R901147 : Reach 901147 := rs (se 1 (by rfl) ⟨675860, by rfl⟩) R1351721
theorem R1666585 : Reach 1666585 := rs (se 2 (by rfl) ⟨624969, by rfl⟩) R1249939
theorem R292511 : Reach 292511 := rs (se 1 (by rfl) ⟨219383, by rfl⟩) R438767
theorem R16258157 : Reach 16258157 := rs (se 3 (by rfl) ⟨3048404, by rfl⟩) R6096809
theorem R1201529 : Reach 1201529 := rs (se 2 (by rfl) ⟨450573, by rfl⟩) R901147
theorem R780029 : Reach 780029 := rs (se 3 (by rfl) ⟨146255, by rfl⟩) R292511
theorem R2222113 : Reach 2222113 := rs (se 2 (by rfl) ⟨833292, by rfl⟩) R1666585
theorem R2962817 : Reach 2962817 := rs (se 2 (by rfl) ⟨1111056, by rfl⟩) R2222113
theorem R801019 : Reach 801019 := rs (se 1 (by rfl) ⟨600764, by rfl⟩) R1201529
theorem R10838771 : Reach 10838771 := rs (se 1 (by rfl) ⟨8129078, by rfl⟩) R16258157
theorem R520019 : Reach 520019 := rs (se 1 (by rfl) ⟨390014, by rfl⟩) R780029
theorem R1975211 : Reach 1975211 := rs (se 1 (by rfl) ⟨1481408, by rfl⟩) R2962817
theorem R4272101 : Reach 4272101 := rs (se 4 (by rfl) ⟨400509, by rfl⟩) R801019
theorem R7225847 : Reach 7225847 := rs (se 1 (by rfl) ⟨5419385, by rfl⟩) R10838771
theorem R346679 : Reach 346679 := rs (se 1 (by rfl) ⟨260009, by rfl⟩) R520019
theorem R4817231 : Reach 4817231 := rs (se 1 (by rfl) ⟨3612923, by rfl⟩) R7225847
theorem R231119 : Reach 231119 := rs (se 1 (by rfl) ⟨173339, by rfl⟩) R346679
theorem R1316807 : Reach 1316807 := rs (se 1 (by rfl) ⟨987605, by rfl⟩) R1975211
theorem R2848067 : Reach 2848067 := rs (se 1 (by rfl) ⟨2136050, by rfl⟩) R4272101
theorem R3211487 : Reach 3211487 := rs (se 1 (by rfl) ⟨2408615, by rfl⟩) R4817231
theorem R154079 : Reach 154079 := rs (se 1 (by rfl) ⟨115559, by rfl⟩) R231119
theorem R877871 : Reach 877871 := rs (se 1 (by rfl) ⟨658403, by rfl⟩) R1316807
theorem R1898711 : Reach 1898711 := rs (se 1 (by rfl) ⟨1424033, by rfl⟩) R2848067
theorem R102719 : Reach 102719 := rs (se 1 (by rfl) ⟨77039, by rfl⟩) R154079
theorem R2140991 : Reach 2140991 := rs (se 1 (by rfl) ⟨1605743, by rfl⟩) R3211487
theorem R1265807 : Reach 1265807 := rs (se 1 (by rfl) ⟨949355, by rfl⟩) R1898711
theorem R585247 : Reach 585247 := rs (se 1 (by rfl) ⟨438935, by rfl⟩) R877871
theorem R68479 : Reach 68479 := rs (se 1 (by rfl) ⟨51359, by rfl⟩) R102719
theorem R1427327 : Reach 1427327 := rs (se 1 (by rfl) ⟨1070495, by rfl⟩) R2140991
theorem R843871 : Reach 843871 := rs (se 1 (by rfl) ⟨632903, by rfl⟩) R1265807
theorem R780329 : Reach 780329 := rs (se 2 (by rfl) ⟨292623, by rfl⟩) R585247
theorem R951551 : Reach 951551 := rs (se 1 (by rfl) ⟨713663, by rfl⟩) R1427327
theorem R1125161 : Reach 1125161 := rs (se 2 (by rfl) ⟨421935, by rfl⟩) R843871
theorem R520219 : Reach 520219 := rs (se 1 (by rfl) ⟨390164, by rfl⟩) R780329
theorem R693625 : Reach 693625 := rs (se 2 (by rfl) ⟨260109, by rfl⟩) R520219
theorem R634367 : Reach 634367 := rs (se 1 (by rfl) ⟨475775, by rfl⟩) R951551
theorem R750107 : Reach 750107 := rs (se 1 (by rfl) ⟨562580, by rfl⟩) R1125161
theorem R2000285 : Reach 2000285 := rs (se 3 (by rfl) ⟨375053, by rfl⟩) R750107
theorem R924833 : Reach 924833 := rs (se 2 (by rfl) ⟨346812, by rfl⟩) R693625
theorem R422911 : Reach 422911 := rs (se 1 (by rfl) ⟨317183, by rfl⟩) R634367
theorem R563881 : Reach 563881 := rs (se 2 (by rfl) ⟨211455, by rfl⟩) R422911
theorem R1333523 : Reach 1333523 := rs (se 1 (by rfl) ⟨1000142, by rfl⟩) R2000285
theorem R616555 : Reach 616555 := rs (se 1 (by rfl) ⟨462416, by rfl⟩) R924833
theorem R822073 : Reach 822073 := rs (se 2 (by rfl) ⟨308277, by rfl⟩) R616555
theorem R889015 : Reach 889015 := rs (se 1 (by rfl) ⟨666761, by rfl⟩) R1333523
theorem R751841 : Reach 751841 := rs (se 2 (by rfl) ⟨281940, by rfl⟩) R563881
theorem R1185353 : Reach 1185353 := rs (se 2 (by rfl) ⟨444507, by rfl⟩) R889015
theorem R501227 : Reach 501227 := rs (se 1 (by rfl) ⟨375920, by rfl⟩) R751841
theorem R1096097 : Reach 1096097 := rs (se 2 (by rfl) ⟨411036, by rfl⟩) R822073
theorem R790235 : Reach 790235 := rs (se 1 (by rfl) ⟨592676, by rfl⟩) R1185353
theorem R334151 : Reach 334151 := rs (se 1 (by rfl) ⟨250613, by rfl⟩) R501227
theorem R2922925 : Reach 2922925 := rs (se 3 (by rfl) ⟨548048, by rfl⟩) R1096097
theorem R526823 : Reach 526823 := rs (se 1 (by rfl) ⟨395117, by rfl⟩) R790235
theorem R222767 : Reach 222767 := rs (se 1 (by rfl) ⟨167075, by rfl⟩) R334151
theorem R3897233 : Reach 3897233 := rs (se 2 (by rfl) ⟨1461462, by rfl⟩) R2922925
theorem R2598155 : Reach 2598155 := rs (se 1 (by rfl) ⟨1948616, by rfl⟩) R3897233
theorem R148511 : Reach 148511 := rs (se 1 (by rfl) ⟨111383, by rfl⟩) R222767
theorem R351215 : Reach 351215 := rs (se 1 (by rfl) ⟨263411, by rfl⟩) R526823
theorem R396029 : Reach 396029 := rs (se 3 (by rfl) ⟨74255, by rfl⟩) R148511
theorem R234143 : Reach 234143 := rs (se 1 (by rfl) ⟨175607, by rfl⟩) R351215
theorem R1732103 : Reach 1732103 := rs (se 1 (by rfl) ⟨1299077, by rfl⟩) R2598155
theorem R264019 : Reach 264019 := rs (se 1 (by rfl) ⟨198014, by rfl⟩) R396029
theorem R1154735 : Reach 1154735 := rs (se 1 (by rfl) ⟨866051, by rfl⟩) R1732103
theorem R156095 : Reach 156095 := rs (se 1 (by rfl) ⟨117071, by rfl⟩) R234143
theorem R104063 : Reach 104063 := rs (se 1 (by rfl) ⟨78047, by rfl⟩) R156095
theorem R769823 : Reach 769823 := rs (se 1 (by rfl) ⟨577367, by rfl⟩) R1154735
theorem R352025 : Reach 352025 := rs (se 2 (by rfl) ⟨132009, by rfl⟩) R264019
theorem R69375 : Reach 69375 := rs (se 1 (by rfl) ⟨52031, by rfl⟩) R104063
theorem R234683 : Reach 234683 := rs (se 1 (by rfl) ⟨176012, by rfl⟩) R352025
theorem R513215 : Reach 513215 := rs (se 1 (by rfl) ⟨384911, by rfl⟩) R769823
theorem R342143 : Reach 342143 := rs (se 1 (by rfl) ⟨256607, by rfl⟩) R513215
theorem R156455 : Reach 156455 := rs (se 1 (by rfl) ⟨117341, by rfl⟩) R234683
theorem R104303 : Reach 104303 := rs (se 1 (by rfl) ⟨78227, by rfl⟩) R156455
theorem R228095 : Reach 228095 := rs (se 1 (by rfl) ⟨171071, by rfl⟩) R342143
theorem R69535 : Reach 69535 := rs (se 1 (by rfl) ⟨52151, by rfl⟩) R104303
theorem R152063 : Reach 152063 := rs (se 1 (by rfl) ⟨114047, by rfl⟩) R228095
theorem R101375 : Reach 101375 := rs (se 1 (by rfl) ⟨76031, by rfl⟩) R152063
theorem R67583 : Reach 67583 := rs (se 1 (by rfl) ⟨50687, by rfl⟩) R101375

theorem C0 (j : ℕ) (h1 : 33562 ≤ j) (h2 : j ≤ 34261) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R67125
  · exact R67127
  · exact R67129
  · exact R67131
  · exact R67133
  · exact R67135
  · exact R67137
  · exact R67139
  · exact R67141
  · exact R67143
  · exact R67145
  · exact R67147
  · exact R67149
  · exact R67151
  · exact R67153
  · exact R67155
  · exact R67157
  · exact R67159
  · exact R67161
  · exact R67163
  · exact R67165
  · exact R67167
  · exact R67169
  · exact R67171
  · exact R67173
  · exact R67175
  · exact R67177
  · exact R67179
  · exact R67181
  · exact R67183
  · exact R67185
  · exact R67187
  · exact R67189
  · exact R67191
  · exact R67193
  · exact R67195
  · exact R67197
  · exact R67199
  · exact R67201
  · exact R67203
  · exact R67205
  · exact R67207
  · exact R67209
  · exact R67211
  · exact R67213
  · exact R67215
  · exact R67217
  · exact R67219
  · exact R67221
  · exact R67223
  · exact R67225
  · exact R67227
  · exact R67229
  · exact R67231
  · exact R67233
  · exact R67235
  · exact R67237
  · exact R67239
  · exact R67241
  · exact R67243
  · exact R67245
  · exact R67247
  · exact R67249
  · exact R67251
  · exact R67253
  · exact R67255
  · exact R67257
  · exact R67259
  · exact R67261
  · exact R67263
  · exact R67265
  · exact R67267
  · exact R67269
  · exact R67271
  · exact R67273
  · exact R67275
  · exact R67277
  · exact R67279
  · exact R67281
  · exact R67283
  · exact R67285
  · exact R67287
  · exact R67289
  · exact R67291
  · exact R67293
  · exact R67295
  · exact R67297
  · exact R67299
  · exact R67301
  · exact R67303
  · exact R67305
  · exact R67307
  · exact R67309
  · exact R67311
  · exact R67313
  · exact R67315
  · exact R67317
  · exact R67319
  · exact R67321
  · exact R67323
  · exact R67325
  · exact R67327
  · exact R67329
  · exact R67331
  · exact R67333
  · exact R67335
  · exact R67337
  · exact R67339
  · exact R67341
  · exact R67343
  · exact R67345
  · exact R67347
  · exact R67349
  · exact R67351
  · exact R67353
  · exact R67355
  · exact R67357
  · exact R67359
  · exact R67361
  · exact R67363
  · exact R67365
  · exact R67367
  · exact R67369
  · exact R67371
  · exact R67373
  · exact R67375
  · exact R67377
  · exact R67379
  · exact R67381
  · exact R67383
  · exact R67385
  · exact R67387
  · exact R67389
  · exact R67391
  · exact R67393
  · exact R67395
  · exact R67397
  · exact R67399
  · exact R67401
  · exact R67403
  · exact R67405
  · exact R67407
  · exact R67409
  · exact R67411
  · exact R67413
  · exact R67415
  · exact R67417
  · exact R67419
  · exact R67421
  · exact R67423
  · exact R67425
  · exact R67427
  · exact R67429
  · exact R67431
  · exact R67433
  · exact R67435
  · exact R67437
  · exact R67439
  · exact R67441
  · exact R67443
  · exact R67445
  · exact R67447
  · exact R67449
  · exact R67451
  · exact R67453
  · exact R67455
  · exact R67457
  · exact R67459
  · exact R67461
  · exact R67463
  · exact R67465
  · exact R67467
  · exact R67469
  · exact R67471
  · exact R67473
  · exact R67475
  · exact R67477
  · exact R67479
  · exact R67481
  · exact R67483
  · exact R67485
  · exact R67487
  · exact R67489
  · exact R67491
  · exact R67493
  · exact R67495
  · exact R67497
  · exact R67499
  · exact R67501
  · exact R67503
  · exact R67505
  · exact R67507
  · exact R67509
  · exact R67511
  · exact R67513
  · exact R67515
  · exact R67517
  · exact R67519
  · exact R67521
  · exact R67523
  · exact R67525
  · exact R67527
  · exact R67529
  · exact R67531
  · exact R67533
  · exact R67535
  · exact R67537
  · exact R67539
  · exact R67541
  · exact R67543
  · exact R67545
  · exact R67547
  · exact R67549
  · exact R67551
  · exact R67553
  · exact R67555
  · exact R67557
  · exact R67559
  · exact R67561
  · exact R67563
  · exact R67565
  · exact R67567
  · exact R67569
  · exact R67571
  · exact R67573
  · exact R67575
  · exact R67577
  · exact R67579
  · exact R67581
  · exact R67583
  · exact R67585
  · exact R67587
  · exact R67589
  · exact R67591
  · exact R67593
  · exact R67595
  · exact R67597
  · exact R67599
  · exact R67601
  · exact R67603
  · exact R67605
  · exact R67607
  · exact R67609
  · exact R67611
  · exact R67613
  · exact R67615
  · exact R67617
  · exact R67619
  · exact R67621
  · exact R67623
  · exact R67625
  · exact R67627
  · exact R67629
  · exact R67631
  · exact R67633
  · exact R67635
  · exact R67637
  · exact R67639
  · exact R67641
  · exact R67643
  · exact R67645
  · exact R67647
  · exact R67649
  · exact R67651
  · exact R67653
  · exact R67655
  · exact R67657
  · exact R67659
  · exact R67661
  · exact R67663
  · exact R67665
  · exact R67667
  · exact R67669
  · exact R67671
  · exact R67673
  · exact R67675
  · exact R67677
  · exact R67679
  · exact R67681
  · exact R67683
  · exact R67685
  · exact R67687
  · exact R67689
  · exact R67691
  · exact R67693
  · exact R67695
  · exact R67697
  · exact R67699
  · exact R67701
  · exact R67703
  · exact R67705
  · exact R67707
  · exact R67709
  · exact R67711
  · exact R67713
  · exact R67715
  · exact R67717
  · exact R67719
  · exact R67721
  · exact R67723
  · exact R67725
  · exact R67727
  · exact R67729
  · exact R67731
  · exact R67733
  · exact R67735
  · exact R67737
  · exact R67739
  · exact R67741
  · exact R67743
  · exact R67745
  · exact R67747
  · exact R67749
  · exact R67751
  · exact R67753
  · exact R67755
  · exact R67757
  · exact R67759
  · exact R67761
  · exact R67763
  · exact R67765
  · exact R67767
  · exact R67769
  · exact R67771
  · exact R67773
  · exact R67775
  · exact R67777
  · exact R67779
  · exact R67781
  · exact R67783
  · exact R67785
  · exact R67787
  · exact R67789
  · exact R67791
  · exact R67793
  · exact R67795
  · exact R67797
  · exact R67799
  · exact R67801
  · exact R67803
  · exact R67805
  · exact R67807
  · exact R67809
  · exact R67811
  · exact R67813
  · exact R67815
  · exact R67817
  · exact R67819
  · exact R67821
  · exact R67823
  · exact R67825
  · exact R67827
  · exact R67829
  · exact R67831
  · exact R67833
  · exact R67835
  · exact R67837
  · exact R67839
  · exact R67841
  · exact R67843
  · exact R67845
  · exact R67847
  · exact R67849
  · exact R67851
  · exact R67853
  · exact R67855
  · exact R67857
  · exact R67859
  · exact R67861
  · exact R67863
  · exact R67865
  · exact R67867
  · exact R67869
  · exact R67871
  · exact R67873
  · exact R67875
  · exact R67877
  · exact R67879
  · exact R67881
  · exact R67883
  · exact R67885
  · exact R67887
  · exact R67889
  · exact R67891
  · exact R67893
  · exact R67895
  · exact R67897
  · exact R67899
  · exact R67901
  · exact R67903
  · exact R67905
  · exact R67907
  · exact R67909
  · exact R67911
  · exact R67913
  · exact R67915
  · exact R67917
  · exact R67919
  · exact R67921
  · exact R67923
  · exact R67925
  · exact R67927
  · exact R67929
  · exact R67931
  · exact R67933
  · exact R67935
  · exact R67937
  · exact R67939
  · exact R67941
  · exact R67943
  · exact R67945
  · exact R67947
  · exact R67949
  · exact R67951
  · exact R67953
  · exact R67955
  · exact R67957
  · exact R67959
  · exact R67961
  · exact R67963
  · exact R67965
  · exact R67967
  · exact R67969
  · exact R67971
  · exact R67973
  · exact R67975
  · exact R67977
  · exact R67979
  · exact R67981
  · exact R67983
  · exact R67985
  · exact R67987
  · exact R67989
  · exact R67991
  · exact R67993
  · exact R67995
  · exact R67997
  · exact R67999
  · exact R68001
  · exact R68003
  · exact R68005
  · exact R68007
  · exact R68009
  · exact R68011
  · exact R68013
  · exact R68015
  · exact R68017
  · exact R68019
  · exact R68021
  · exact R68023
  · exact R68025
  · exact R68027
  · exact R68029
  · exact R68031
  · exact R68033
  · exact R68035
  · exact R68037
  · exact R68039
  · exact R68041
  · exact R68043
  · exact R68045
  · exact R68047
  · exact R68049
  · exact R68051
  · exact R68053
  · exact R68055
  · exact R68057
  · exact R68059
  · exact R68061
  · exact R68063
  · exact R68065
  · exact R68067
  · exact R68069
  · exact R68071
  · exact R68073
  · exact R68075
  · exact R68077
  · exact R68079
  · exact R68081
  · exact R68083
  · exact R68085
  · exact R68087
  · exact R68089
  · exact R68091
  · exact R68093
  · exact R68095
  · exact R68097
  · exact R68099
  · exact R68101
  · exact R68103
  · exact R68105
  · exact R68107
  · exact R68109
  · exact R68111
  · exact R68113
  · exact R68115
  · exact R68117
  · exact R68119
  · exact R68121
  · exact R68123
  · exact R68125
  · exact R68127
  · exact R68129
  · exact R68131
  · exact R68133
  · exact R68135
  · exact R68137
  · exact R68139
  · exact R68141
  · exact R68143
  · exact R68145
  · exact R68147
  · exact R68149
  · exact R68151
  · exact R68153
  · exact R68155
  · exact R68157
  · exact R68159
  · exact R68161
  · exact R68163
  · exact R68165
  · exact R68167
  · exact R68169
  · exact R68171
  · exact R68173
  · exact R68175
  · exact R68177
  · exact R68179
  · exact R68181
  · exact R68183
  · exact R68185
  · exact R68187
  · exact R68189
  · exact R68191
  · exact R68193
  · exact R68195
  · exact R68197
  · exact R68199
  · exact R68201
  · exact R68203
  · exact R68205
  · exact R68207
  · exact R68209
  · exact R68211
  · exact R68213
  · exact R68215
  · exact R68217
  · exact R68219
  · exact R68221
  · exact R68223
  · exact R68225
  · exact R68227
  · exact R68229
  · exact R68231
  · exact R68233
  · exact R68235
  · exact R68237
  · exact R68239
  · exact R68241
  · exact R68243
  · exact R68245
  · exact R68247
  · exact R68249
  · exact R68251
  · exact R68253
  · exact R68255
  · exact R68257
  · exact R68259
  · exact R68261
  · exact R68263
  · exact R68265
  · exact R68267
  · exact R68269
  · exact R68271
  · exact R68273
  · exact R68275
  · exact R68277
  · exact R68279
  · exact R68281
  · exact R68283
  · exact R68285
  · exact R68287
  · exact R68289
  · exact R68291
  · exact R68293
  · exact R68295
  · exact R68297
  · exact R68299
  · exact R68301
  · exact R68303
  · exact R68305
  · exact R68307
  · exact R68309
  · exact R68311
  · exact R68313
  · exact R68315
  · exact R68317
  · exact R68319
  · exact R68321
  · exact R68323
  · exact R68325
  · exact R68327
  · exact R68329
  · exact R68331
  · exact R68333
  · exact R68335
  · exact R68337
  · exact R68339
  · exact R68341
  · exact R68343
  · exact R68345
  · exact R68347
  · exact R68349
  · exact R68351
  · exact R68353
  · exact R68355
  · exact R68357
  · exact R68359
  · exact R68361
  · exact R68363
  · exact R68365
  · exact R68367
  · exact R68369
  · exact R68371
  · exact R68373
  · exact R68375
  · exact R68377
  · exact R68379
  · exact R68381
  · exact R68383
  · exact R68385
  · exact R68387
  · exact R68389
  · exact R68391
  · exact R68393
  · exact R68395
  · exact R68397
  · exact R68399
  · exact R68401
  · exact R68403
  · exact R68405
  · exact R68407
  · exact R68409
  · exact R68411
  · exact R68413
  · exact R68415
  · exact R68417
  · exact R68419
  · exact R68421
  · exact R68423
  · exact R68425
  · exact R68427
  · exact R68429
  · exact R68431
  · exact R68433
  · exact R68435
  · exact R68437
  · exact R68439
  · exact R68441
  · exact R68443
  · exact R68445
  · exact R68447
  · exact R68449
  · exact R68451
  · exact R68453
  · exact R68455
  · exact R68457
  · exact R68459
  · exact R68461
  · exact R68463
  · exact R68465
  · exact R68467
  · exact R68469
  · exact R68471
  · exact R68473
  · exact R68475
  · exact R68477
  · exact R68479
  · exact R68481
  · exact R68483
  · exact R68485
  · exact R68487
  · exact R68489
  · exact R68491
  · exact R68493
  · exact R68495
  · exact R68497
  · exact R68499
  · exact R68501
  · exact R68503
  · exact R68505
  · exact R68507
  · exact R68509
  · exact R68511
  · exact R68513
  · exact R68515
  · exact R68517
  · exact R68519
  · exact R68521
  · exact R68523

theorem C1 (j : ℕ) (h1 : 34262 ≤ j) (h2 : j ≤ 34961) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R68525
  · exact R68527
  · exact R68529
  · exact R68531
  · exact R68533
  · exact R68535
  · exact R68537
  · exact R68539
  · exact R68541
  · exact R68543
  · exact R68545
  · exact R68547
  · exact R68549
  · exact R68551
  · exact R68553
  · exact R68555
  · exact R68557
  · exact R68559
  · exact R68561
  · exact R68563
  · exact R68565
  · exact R68567
  · exact R68569
  · exact R68571
  · exact R68573
  · exact R68575
  · exact R68577
  · exact R68579
  · exact R68581
  · exact R68583
  · exact R68585
  · exact R68587
  · exact R68589
  · exact R68591
  · exact R68593
  · exact R68595
  · exact R68597
  · exact R68599
  · exact R68601
  · exact R68603
  · exact R68605
  · exact R68607
  · exact R68609
  · exact R68611
  · exact R68613
  · exact R68615
  · exact R68617
  · exact R68619
  · exact R68621
  · exact R68623
  · exact R68625
  · exact R68627
  · exact R68629
  · exact R68631
  · exact R68633
  · exact R68635
  · exact R68637
  · exact R68639
  · exact R68641
  · exact R68643
  · exact R68645
  · exact R68647
  · exact R68649
  · exact R68651
  · exact R68653
  · exact R68655
  · exact R68657
  · exact R68659
  · exact R68661
  · exact R68663
  · exact R68665
  · exact R68667
  · exact R68669
  · exact R68671
  · exact R68673
  · exact R68675
  · exact R68677
  · exact R68679
  · exact R68681
  · exact R68683
  · exact R68685
  · exact R68687
  · exact R68689
  · exact R68691
  · exact R68693
  · exact R68695
  · exact R68697
  · exact R68699
  · exact R68701
  · exact R68703
  · exact R68705
  · exact R68707
  · exact R68709
  · exact R68711
  · exact R68713
  · exact R68715
  · exact R68717
  · exact R68719
  · exact R68721
  · exact R68723
  · exact R68725
  · exact R68727
  · exact R68729
  · exact R68731
  · exact R68733
  · exact R68735
  · exact R68737
  · exact R68739
  · exact R68741
  · exact R68743
  · exact R68745
  · exact R68747
  · exact R68749
  · exact R68751
  · exact R68753
  · exact R68755
  · exact R68757
  · exact R68759
  · exact R68761
  · exact R68763
  · exact R68765
  · exact R68767
  · exact R68769
  · exact R68771
  · exact R68773
  · exact R68775
  · exact R68777
  · exact R68779
  · exact R68781
  · exact R68783
  · exact R68785
  · exact R68787
  · exact R68789
  · exact R68791
  · exact R68793
  · exact R68795
  · exact R68797
  · exact R68799
  · exact R68801
  · exact R68803
  · exact R68805
  · exact R68807
  · exact R68809
  · exact R68811
  · exact R68813
  · exact R68815
  · exact R68817
  · exact R68819
  · exact R68821
  · exact R68823
  · exact R68825
  · exact R68827
  · exact R68829
  · exact R68831
  · exact R68833
  · exact R68835
  · exact R68837
  · exact R68839
  · exact R68841
  · exact R68843
  · exact R68845
  · exact R68847
  · exact R68849
  · exact R68851
  · exact R68853
  · exact R68855
  · exact R68857
  · exact R68859
  · exact R68861
  · exact R68863
  · exact R68865
  · exact R68867
  · exact R68869
  · exact R68871
  · exact R68873
  · exact R68875
  · exact R68877
  · exact R68879
  · exact R68881
  · exact R68883
  · exact R68885
  · exact R68887
  · exact R68889
  · exact R68891
  · exact R68893
  · exact R68895
  · exact R68897
  · exact R68899
  · exact R68901
  · exact R68903
  · exact R68905
  · exact R68907
  · exact R68909
  · exact R68911
  · exact R68913
  · exact R68915
  · exact R68917
  · exact R68919
  · exact R68921
  · exact R68923
  · exact R68925
  · exact R68927
  · exact R68929
  · exact R68931
  · exact R68933
  · exact R68935
  · exact R68937
  · exact R68939
  · exact R68941
  · exact R68943
  · exact R68945
  · exact R68947
  · exact R68949
  · exact R68951
  · exact R68953
  · exact R68955
  · exact R68957
  · exact R68959
  · exact R68961
  · exact R68963
  · exact R68965
  · exact R68967
  · exact R68969
  · exact R68971
  · exact R68973
  · exact R68975
  · exact R68977
  · exact R68979
  · exact R68981
  · exact R68983
  · exact R68985
  · exact R68987
  · exact R68989
  · exact R68991
  · exact R68993
  · exact R68995
  · exact R68997
  · exact R68999
  · exact R69001
  · exact R69003
  · exact R69005
  · exact R69007
  · exact R69009
  · exact R69011
  · exact R69013
  · exact R69015
  · exact R69017
  · exact R69019
  · exact R69021
  · exact R69023
  · exact R69025
  · exact R69027
  · exact R69029
  · exact R69031
  · exact R69033
  · exact R69035
  · exact R69037
  · exact R69039
  · exact R69041
  · exact R69043
  · exact R69045
  · exact R69047
  · exact R69049
  · exact R69051
  · exact R69053
  · exact R69055
  · exact R69057
  · exact R69059
  · exact R69061
  · exact R69063
  · exact R69065
  · exact R69067
  · exact R69069
  · exact R69071
  · exact R69073
  · exact R69075
  · exact R69077
  · exact R69079
  · exact R69081
  · exact R69083
  · exact R69085
  · exact R69087
  · exact R69089
  · exact R69091
  · exact R69093
  · exact R69095
  · exact R69097
  · exact R69099
  · exact R69101
  · exact R69103
  · exact R69105
  · exact R69107
  · exact R69109
  · exact R69111
  · exact R69113
  · exact R69115
  · exact R69117
  · exact R69119
  · exact R69121
  · exact R69123
  · exact R69125
  · exact R69127
  · exact R69129
  · exact R69131
  · exact R69133
  · exact R69135
  · exact R69137
  · exact R69139
  · exact R69141
  · exact R69143
  · exact R69145
  · exact R69147
  · exact R69149
  · exact R69151
  · exact R69153
  · exact R69155
  · exact R69157
  · exact R69159
  · exact R69161
  · exact R69163
  · exact R69165
  · exact R69167
  · exact R69169
  · exact R69171
  · exact R69173
  · exact R69175
  · exact R69177
  · exact R69179
  · exact R69181
  · exact R69183
  · exact R69185
  · exact R69187
  · exact R69189
  · exact R69191
  · exact R69193
  · exact R69195
  · exact R69197
  · exact R69199
  · exact R69201
  · exact R69203
  · exact R69205
  · exact R69207
  · exact R69209
  · exact R69211
  · exact R69213
  · exact R69215
  · exact R69217
  · exact R69219
  · exact R69221
  · exact R69223
  · exact R69225
  · exact R69227
  · exact R69229
  · exact R69231
  · exact R69233
  · exact R69235
  · exact R69237
  · exact R69239
  · exact R69241
  · exact R69243
  · exact R69245
  · exact R69247
  · exact R69249
  · exact R69251
  · exact R69253
  · exact R69255
  · exact R69257
  · exact R69259
  · exact R69261
  · exact R69263
  · exact R69265
  · exact R69267
  · exact R69269
  · exact R69271
  · exact R69273
  · exact R69275
  · exact R69277
  · exact R69279
  · exact R69281
  · exact R69283
  · exact R69285
  · exact R69287
  · exact R69289
  · exact R69291
  · exact R69293
  · exact R69295
  · exact R69297
  · exact R69299
  · exact R69301
  · exact R69303
  · exact R69305
  · exact R69307
  · exact R69309
  · exact R69311
  · exact R69313
  · exact R69315
  · exact R69317
  · exact R69319
  · exact R69321
  · exact R69323
  · exact R69325
  · exact R69327
  · exact R69329
  · exact R69331
  · exact R69333
  · exact R69335
  · exact R69337
  · exact R69339
  · exact R69341
  · exact R69343
  · exact R69345
  · exact R69347
  · exact R69349
  · exact R69351
  · exact R69353
  · exact R69355
  · exact R69357
  · exact R69359
  · exact R69361
  · exact R69363
  · exact R69365
  · exact R69367
  · exact R69369
  · exact R69371
  · exact R69373
  · exact R69375
  · exact R69377
  · exact R69379
  · exact R69381
  · exact R69383
  · exact R69385
  · exact R69387
  · exact R69389
  · exact R69391
  · exact R69393
  · exact R69395
  · exact R69397
  · exact R69399
  · exact R69401
  · exact R69403
  · exact R69405
  · exact R69407
  · exact R69409
  · exact R69411
  · exact R69413
  · exact R69415
  · exact R69417
  · exact R69419
  · exact R69421
  · exact R69423
  · exact R69425
  · exact R69427
  · exact R69429
  · exact R69431
  · exact R69433
  · exact R69435
  · exact R69437
  · exact R69439
  · exact R69441
  · exact R69443
  · exact R69445
  · exact R69447
  · exact R69449
  · exact R69451
  · exact R69453
  · exact R69455
  · exact R69457
  · exact R69459
  · exact R69461
  · exact R69463
  · exact R69465
  · exact R69467
  · exact R69469
  · exact R69471
  · exact R69473
  · exact R69475
  · exact R69477
  · exact R69479
  · exact R69481
  · exact R69483
  · exact R69485
  · exact R69487
  · exact R69489
  · exact R69491
  · exact R69493
  · exact R69495
  · exact R69497
  · exact R69499
  · exact R69501
  · exact R69503
  · exact R69505
  · exact R69507
  · exact R69509
  · exact R69511
  · exact R69513
  · exact R69515
  · exact R69517
  · exact R69519
  · exact R69521
  · exact R69523
  · exact R69525
  · exact R69527
  · exact R69529
  · exact R69531
  · exact R69533
  · exact R69535
  · exact R69537
  · exact R69539
  · exact R69541
  · exact R69543
  · exact R69545
  · exact R69547
  · exact R69549
  · exact R69551
  · exact R69553
  · exact R69555
  · exact R69557
  · exact R69559
  · exact R69561
  · exact R69563
  · exact R69565
  · exact R69567
  · exact R69569
  · exact R69571
  · exact R69573
  · exact R69575
  · exact R69577
  · exact R69579
  · exact R69581
  · exact R69583
  · exact R69585
  · exact R69587
  · exact R69589
  · exact R69591
  · exact R69593
  · exact R69595
  · exact R69597
  · exact R69599
  · exact R69601
  · exact R69603
  · exact R69605
  · exact R69607
  · exact R69609
  · exact R69611
  · exact R69613
  · exact R69615
  · exact R69617
  · exact R69619
  · exact R69621
  · exact R69623
  · exact R69625
  · exact R69627
  · exact R69629
  · exact R69631
  · exact R69633
  · exact R69635
  · exact R69637
  · exact R69639
  · exact R69641
  · exact R69643
  · exact R69645
  · exact R69647
  · exact R69649
  · exact R69651
  · exact R69653
  · exact R69655
  · exact R69657
  · exact R69659
  · exact R69661
  · exact R69663
  · exact R69665
  · exact R69667
  · exact R69669
  · exact R69671
  · exact R69673
  · exact R69675
  · exact R69677
  · exact R69679
  · exact R69681
  · exact R69683
  · exact R69685
  · exact R69687
  · exact R69689
  · exact R69691
  · exact R69693
  · exact R69695
  · exact R69697
  · exact R69699
  · exact R69701
  · exact R69703
  · exact R69705
  · exact R69707
  · exact R69709
  · exact R69711
  · exact R69713
  · exact R69715
  · exact R69717
  · exact R69719
  · exact R69721
  · exact R69723
  · exact R69725
  · exact R69727
  · exact R69729
  · exact R69731
  · exact R69733
  · exact R69735
  · exact R69737
  · exact R69739
  · exact R69741
  · exact R69743
  · exact R69745
  · exact R69747
  · exact R69749
  · exact R69751
  · exact R69753
  · exact R69755
  · exact R69757
  · exact R69759
  · exact R69761
  · exact R69763
  · exact R69765
  · exact R69767
  · exact R69769
  · exact R69771
  · exact R69773
  · exact R69775
  · exact R69777
  · exact R69779
  · exact R69781
  · exact R69783
  · exact R69785
  · exact R69787
  · exact R69789
  · exact R69791
  · exact R69793
  · exact R69795
  · exact R69797
  · exact R69799
  · exact R69801
  · exact R69803
  · exact R69805
  · exact R69807
  · exact R69809
  · exact R69811
  · exact R69813
  · exact R69815
  · exact R69817
  · exact R69819
  · exact R69821
  · exact R69823
  · exact R69825
  · exact R69827
  · exact R69829
  · exact R69831
  · exact R69833
  · exact R69835
  · exact R69837
  · exact R69839
  · exact R69841
  · exact R69843
  · exact R69845
  · exact R69847
  · exact R69849
  · exact R69851
  · exact R69853
  · exact R69855
  · exact R69857
  · exact R69859
  · exact R69861
  · exact R69863
  · exact R69865
  · exact R69867
  · exact R69869
  · exact R69871
  · exact R69873
  · exact R69875
  · exact R69877
  · exact R69879
  · exact R69881
  · exact R69883
  · exact R69885
  · exact R69887
  · exact R69889
  · exact R69891
  · exact R69893
  · exact R69895
  · exact R69897
  · exact R69899
  · exact R69901
  · exact R69903
  · exact R69905
  · exact R69907
  · exact R69909
  · exact R69911
  · exact R69913
  · exact R69915
  · exact R69917
  · exact R69919
  · exact R69921
  · exact R69923

theorem C2 (j : ℕ) (h1 : 34962 ≤ j) (h2 : j ≤ 35561) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R69925
  · exact R69927
  · exact R69929
  · exact R69931
  · exact R69933
  · exact R69935
  · exact R69937
  · exact R69939
  · exact R69941
  · exact R69943
  · exact R69945
  · exact R69947
  · exact R69949
  · exact R69951
  · exact R69953
  · exact R69955
  · exact R69957
  · exact R69959
  · exact R69961
  · exact R69963
  · exact R69965
  · exact R69967
  · exact R69969
  · exact R69971
  · exact R69973
  · exact R69975
  · exact R69977
  · exact R69979
  · exact R69981
  · exact R69983
  · exact R69985
  · exact R69987
  · exact R69989
  · exact R69991
  · exact R69993
  · exact R69995
  · exact R69997
  · exact R69999
  · exact R70001
  · exact R70003
  · exact R70005
  · exact R70007
  · exact R70009
  · exact R70011
  · exact R70013
  · exact R70015
  · exact R70017
  · exact R70019
  · exact R70021
  · exact R70023
  · exact R70025
  · exact R70027
  · exact R70029
  · exact R70031
  · exact R70033
  · exact R70035
  · exact R70037
  · exact R70039
  · exact R70041
  · exact R70043
  · exact R70045
  · exact R70047
  · exact R70049
  · exact R70051
  · exact R70053
  · exact R70055
  · exact R70057
  · exact R70059
  · exact R70061
  · exact R70063
  · exact R70065
  · exact R70067
  · exact R70069
  · exact R70071
  · exact R70073
  · exact R70075
  · exact R70077
  · exact R70079
  · exact R70081
  · exact R70083
  · exact R70085
  · exact R70087
  · exact R70089
  · exact R70091
  · exact R70093
  · exact R70095
  · exact R70097
  · exact R70099
  · exact R70101
  · exact R70103
  · exact R70105
  · exact R70107
  · exact R70109
  · exact R70111
  · exact R70113
  · exact R70115
  · exact R70117
  · exact R70119
  · exact R70121
  · exact R70123
  · exact R70125
  · exact R70127
  · exact R70129
  · exact R70131
  · exact R70133
  · exact R70135
  · exact R70137
  · exact R70139
  · exact R70141
  · exact R70143
  · exact R70145
  · exact R70147
  · exact R70149
  · exact R70151
  · exact R70153
  · exact R70155
  · exact R70157
  · exact R70159
  · exact R70161
  · exact R70163
  · exact R70165
  · exact R70167
  · exact R70169
  · exact R70171
  · exact R70173
  · exact R70175
  · exact R70177
  · exact R70179
  · exact R70181
  · exact R70183
  · exact R70185
  · exact R70187
  · exact R70189
  · exact R70191
  · exact R70193
  · exact R70195
  · exact R70197
  · exact R70199
  · exact R70201
  · exact R70203
  · exact R70205
  · exact R70207
  · exact R70209
  · exact R70211
  · exact R70213
  · exact R70215
  · exact R70217
  · exact R70219
  · exact R70221
  · exact R70223
  · exact R70225
  · exact R70227
  · exact R70229
  · exact R70231
  · exact R70233
  · exact R70235
  · exact R70237
  · exact R70239
  · exact R70241
  · exact R70243
  · exact R70245
  · exact R70247
  · exact R70249
  · exact R70251
  · exact R70253
  · exact R70255
  · exact R70257
  · exact R70259
  · exact R70261
  · exact R70263
  · exact R70265
  · exact R70267
  · exact R70269
  · exact R70271
  · exact R70273
  · exact R70275
  · exact R70277
  · exact R70279
  · exact R70281
  · exact R70283
  · exact R70285
  · exact R70287
  · exact R70289
  · exact R70291
  · exact R70293
  · exact R70295
  · exact R70297
  · exact R70299
  · exact R70301
  · exact R70303
  · exact R70305
  · exact R70307
  · exact R70309
  · exact R70311
  · exact R70313
  · exact R70315
  · exact R70317
  · exact R70319
  · exact R70321
  · exact R70323
  · exact R70325
  · exact R70327
  · exact R70329
  · exact R70331
  · exact R70333
  · exact R70335
  · exact R70337
  · exact R70339
  · exact R70341
  · exact R70343
  · exact R70345
  · exact R70347
  · exact R70349
  · exact R70351
  · exact R70353
  · exact R70355
  · exact R70357
  · exact R70359
  · exact R70361
  · exact R70363
  · exact R70365
  · exact R70367
  · exact R70369
  · exact R70371
  · exact R70373
  · exact R70375
  · exact R70377
  · exact R70379
  · exact R70381
  · exact R70383
  · exact R70385
  · exact R70387
  · exact R70389
  · exact R70391
  · exact R70393
  · exact R70395
  · exact R70397
  · exact R70399
  · exact R70401
  · exact R70403
  · exact R70405
  · exact R70407
  · exact R70409
  · exact R70411
  · exact R70413
  · exact R70415
  · exact R70417
  · exact R70419
  · exact R70421
  · exact R70423
  · exact R70425
  · exact R70427
  · exact R70429
  · exact R70431
  · exact R70433
  · exact R70435
  · exact R70437
  · exact R70439
  · exact R70441
  · exact R70443
  · exact R70445
  · exact R70447
  · exact R70449
  · exact R70451
  · exact R70453
  · exact R70455
  · exact R70457
  · exact R70459
  · exact R70461
  · exact R70463
  · exact R70465
  · exact R70467
  · exact R70469
  · exact R70471
  · exact R70473
  · exact R70475
  · exact R70477
  · exact R70479
  · exact R70481
  · exact R70483
  · exact R70485
  · exact R70487
  · exact R70489
  · exact R70491
  · exact R70493
  · exact R70495
  · exact R70497
  · exact R70499
  · exact R70501
  · exact R70503
  · exact R70505
  · exact R70507
  · exact R70509
  · exact R70511
  · exact R70513
  · exact R70515
  · exact R70517
  · exact R70519
  · exact R70521
  · exact R70523
  · exact R70525
  · exact R70527
  · exact R70529
  · exact R70531
  · exact R70533
  · exact R70535
  · exact R70537
  · exact R70539
  · exact R70541
  · exact R70543
  · exact R70545
  · exact R70547
  · exact R70549
  · exact R70551
  · exact R70553
  · exact R70555
  · exact R70557
  · exact R70559
  · exact R70561
  · exact R70563
  · exact R70565
  · exact R70567
  · exact R70569
  · exact R70571
  · exact R70573
  · exact R70575
  · exact R70577
  · exact R70579
  · exact R70581
  · exact R70583
  · exact R70585
  · exact R70587
  · exact R70589
  · exact R70591
  · exact R70593
  · exact R70595
  · exact R70597
  · exact R70599
  · exact R70601
  · exact R70603
  · exact R70605
  · exact R70607
  · exact R70609
  · exact R70611
  · exact R70613
  · exact R70615
  · exact R70617
  · exact R70619
  · exact R70621
  · exact R70623
  · exact R70625
  · exact R70627
  · exact R70629
  · exact R70631
  · exact R70633
  · exact R70635
  · exact R70637
  · exact R70639
  · exact R70641
  · exact R70643
  · exact R70645
  · exact R70647
  · exact R70649
  · exact R70651
  · exact R70653
  · exact R70655
  · exact R70657
  · exact R70659
  · exact R70661
  · exact R70663
  · exact R70665
  · exact R70667
  · exact R70669
  · exact R70671
  · exact R70673
  · exact R70675
  · exact R70677
  · exact R70679
  · exact R70681
  · exact R70683
  · exact R70685
  · exact R70687
  · exact R70689
  · exact R70691
  · exact R70693
  · exact R70695
  · exact R70697
  · exact R70699
  · exact R70701
  · exact R70703
  · exact R70705
  · exact R70707
  · exact R70709
  · exact R70711
  · exact R70713
  · exact R70715
  · exact R70717
  · exact R70719
  · exact R70721
  · exact R70723
  · exact R70725
  · exact R70727
  · exact R70729
  · exact R70731
  · exact R70733
  · exact R70735
  · exact R70737
  · exact R70739
  · exact R70741
  · exact R70743
  · exact R70745
  · exact R70747
  · exact R70749
  · exact R70751
  · exact R70753
  · exact R70755
  · exact R70757
  · exact R70759
  · exact R70761
  · exact R70763
  · exact R70765
  · exact R70767
  · exact R70769
  · exact R70771
  · exact R70773
  · exact R70775
  · exact R70777
  · exact R70779
  · exact R70781
  · exact R70783
  · exact R70785
  · exact R70787
  · exact R70789
  · exact R70791
  · exact R70793
  · exact R70795
  · exact R70797
  · exact R70799
  · exact R70801
  · exact R70803
  · exact R70805
  · exact R70807
  · exact R70809
  · exact R70811
  · exact R70813
  · exact R70815
  · exact R70817
  · exact R70819
  · exact R70821
  · exact R70823
  · exact R70825
  · exact R70827
  · exact R70829
  · exact R70831
  · exact R70833
  · exact R70835
  · exact R70837
  · exact R70839
  · exact R70841
  · exact R70843
  · exact R70845
  · exact R70847
  · exact R70849
  · exact R70851
  · exact R70853
  · exact R70855
  · exact R70857
  · exact R70859
  · exact R70861
  · exact R70863
  · exact R70865
  · exact R70867
  · exact R70869
  · exact R70871
  · exact R70873
  · exact R70875
  · exact R70877
  · exact R70879
  · exact R70881
  · exact R70883
  · exact R70885
  · exact R70887
  · exact R70889
  · exact R70891
  · exact R70893
  · exact R70895
  · exact R70897
  · exact R70899
  · exact R70901
  · exact R70903
  · exact R70905
  · exact R70907
  · exact R70909
  · exact R70911
  · exact R70913
  · exact R70915
  · exact R70917
  · exact R70919
  · exact R70921
  · exact R70923
  · exact R70925
  · exact R70927
  · exact R70929
  · exact R70931
  · exact R70933
  · exact R70935
  · exact R70937
  · exact R70939
  · exact R70941
  · exact R70943
  · exact R70945
  · exact R70947
  · exact R70949
  · exact R70951
  · exact R70953
  · exact R70955
  · exact R70957
  · exact R70959
  · exact R70961
  · exact R70963
  · exact R70965
  · exact R70967
  · exact R70969
  · exact R70971
  · exact R70973
  · exact R70975
  · exact R70977
  · exact R70979
  · exact R70981
  · exact R70983
  · exact R70985
  · exact R70987
  · exact R70989
  · exact R70991
  · exact R70993
  · exact R70995
  · exact R70997
  · exact R70999
  · exact R71001
  · exact R71003
  · exact R71005
  · exact R71007
  · exact R71009
  · exact R71011
  · exact R71013
  · exact R71015
  · exact R71017
  · exact R71019
  · exact R71021
  · exact R71023
  · exact R71025
  · exact R71027
  · exact R71029
  · exact R71031
  · exact R71033
  · exact R71035
  · exact R71037
  · exact R71039
  · exact R71041
  · exact R71043
  · exact R71045
  · exact R71047
  · exact R71049
  · exact R71051
  · exact R71053
  · exact R71055
  · exact R71057
  · exact R71059
  · exact R71061
  · exact R71063
  · exact R71065
  · exact R71067
  · exact R71069
  · exact R71071
  · exact R71073
  · exact R71075
  · exact R71077
  · exact R71079
  · exact R71081
  · exact R71083
  · exact R71085
  · exact R71087
  · exact R71089
  · exact R71091
  · exact R71093
  · exact R71095
  · exact R71097
  · exact R71099
  · exact R71101
  · exact R71103
  · exact R71105
  · exact R71107
  · exact R71109
  · exact R71111
  · exact R71113
  · exact R71115
  · exact R71117
  · exact R71119
  · exact R71121
  · exact R71123

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 71124) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 67124 with hlo | hlo
  · exact syracuse_reaches_one_below_67124 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 34262 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 34962 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
