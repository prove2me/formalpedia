-- Prove2me | solution 1 for syracuse_descends_range_1194414_1196414
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:41.692962+00:00
-- url     : https://prove2.me/submissions/669b4b29-c41b-4e07-a08e-8052fb142fff

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


theorem B1794053 : Blo 1194414 1794053 := bbase (se 4 (by rfl) ⟨168192, by rfl⟩ : syracuseStep 1794053 = 336385) (by norm_num)
theorem B4538389 : Blo 1194414 4538389 := bbase (se 6 (by rfl) ⟨106368, by rfl⟩ : syracuseStep 4538389 = 212737) (by norm_num)
theorem B1794077 : Blo 1194414 1794077 := bbase (se 3 (by rfl) ⟨336389, by rfl⟩ : syracuseStep 1794077 = 672779) (by norm_num)
theorem B1794101 : Blo 1194414 1794101 := bbase (se 5 (by rfl) ⟨84098, by rfl⟩ : syracuseStep 1794101 = 168197) (by norm_num)
theorem B1794125 : Blo 1194414 1794125 := bbase (se 3 (by rfl) ⟨336398, by rfl⟩ : syracuseStep 1794125 = 672797) (by norm_num)
theorem B1794149 : Blo 1194414 1794149 := bbase (se 4 (by rfl) ⟨168201, by rfl⟩ : syracuseStep 1794149 = 336403) (by norm_num)
theorem B4309109 : Blo 1194414 4309109 := bbase (se 5 (by rfl) ⟨201989, by rfl⟩ : syracuseStep 4309109 = 403979) (by norm_num)
theorem B2269309 : Blo 1194414 2269309 := bbase (se 3 (by rfl) ⟨425495, by rfl⟩ : syracuseStep 2269309 = 850991) (by norm_num)
theorem B1794173 : Blo 1194414 1794173 := bbase (se 3 (by rfl) ⟨336407, by rfl⟩ : syracuseStep 1794173 = 672815) (by norm_num)
theorem B1245325 : Blo 1194414 1245325 := bbase (se 3 (by rfl) ⟨233498, by rfl⟩ : syracuseStep 1245325 = 466997) (by norm_num)
theorem B1794197 : Blo 1194414 1794197 := bbase (se 6 (by rfl) ⟨42051, by rfl⟩ : syracuseStep 1794197 = 84103) (by norm_num)
theorem B1818781 : Blo 1194414 1818781 := bbase (se 3 (by rfl) ⟨341021, by rfl⟩ : syracuseStep 1818781 = 682043) (by norm_num)
theorem B1794221 : Blo 1194414 1794221 := bbase (se 3 (by rfl) ⟨336416, by rfl⟩ : syracuseStep 1794221 = 672833) (by norm_num)
theorem B1794245 : Blo 1194414 1794245 := bbase (se 4 (by rfl) ⟨168210, by rfl⟩ : syracuseStep 1794245 = 336421) (by norm_num)
theorem B6054101 : Blo 1194414 6054101 := bbase (se 7 (by rfl) ⟨70946, by rfl⟩ : syracuseStep 6054101 = 141893) (by norm_num)
theorem B1794269 : Blo 1194414 1794269 := bbase (se 3 (by rfl) ⟨336425, by rfl⟩ : syracuseStep 1794269 = 672851) (by norm_num)
theorem B1794293 : Blo 1194414 1794293 := bbase (se 5 (by rfl) ⟨84107, by rfl⟩ : syracuseStep 1794293 = 168215) (by norm_num)
theorem B1343749 : Blo 1194414 1343749 := bbase (se 4 (by rfl) ⟨125976, by rfl⟩ : syracuseStep 1343749 = 251953) (by norm_num)
theorem B2269453 : Blo 1194414 2269453 := bbase (se 3 (by rfl) ⟨425522, by rfl⟩ : syracuseStep 2269453 = 851045) (by norm_num)
theorem B1794317 : Blo 1194414 1794317 := bbase (se 3 (by rfl) ⟨336434, by rfl⟩ : syracuseStep 1794317 = 672869) (by norm_num)
theorem B1794341 : Blo 1194414 1794341 := bbase (se 4 (by rfl) ⟨168219, by rfl⟩ : syracuseStep 1794341 = 336439) (by norm_num)
theorem B1343785 : Blo 1194414 1343785 := bbase (se 2 (by rfl) ⟨503919, by rfl⟩ : syracuseStep 1343785 = 1007839) (by norm_num)
theorem B1794365 : Blo 1194414 1794365 := bbase (se 3 (by rfl) ⟨336443, by rfl⟩ : syracuseStep 1794365 = 672887) (by norm_num)
theorem B4538693 : Blo 1194414 4538693 := bbase (se 4 (by rfl) ⟨425502, by rfl⟩ : syracuseStep 4538693 = 851005) (by norm_num)
theorem B1343821 : Blo 1194414 1343821 := bbase (se 3 (by rfl) ⟨251966, by rfl⟩ : syracuseStep 1343821 = 503933) (by norm_num)
theorem B1794389 : Blo 1194414 1794389 := bbase (se 10 (by rfl) ⟨2628, by rfl⟩ : syracuseStep 1794389 = 5257) (by norm_num)
theorem B2015597 : Blo 1194414 2015597 := bbase (se 3 (by rfl) ⟨377924, by rfl⟩ : syracuseStep 2015597 = 755849) (by norm_num)
theorem B1794413 : Blo 1194414 1794413 := bbase (se 3 (by rfl) ⟨336452, by rfl⟩ : syracuseStep 1794413 = 672905) (by norm_num)
theorem B1343857 : Blo 1194414 1343857 := bbase (se 2 (by rfl) ⟨503946, by rfl⟩ : syracuseStep 1343857 = 1007893) (by norm_num)
theorem B1794437 : Blo 1194414 1794437 := bbase (se 4 (by rfl) ⟨168228, by rfl⟩ : syracuseStep 1794437 = 336457) (by norm_num)
theorem B1343893 : Blo 1194414 1343893 := bbase (se 6 (by rfl) ⟨31497, by rfl⟩ : syracuseStep 1343893 = 62995) (by norm_num)
theorem B1794461 : Blo 1194414 1794461 := bbase (se 3 (by rfl) ⟨336461, by rfl⟩ : syracuseStep 1794461 = 672923) (by norm_num)
theorem B2269613 : Blo 1194414 2269613 := bbase (se 3 (by rfl) ⟨425552, by rfl⟩ : syracuseStep 2269613 = 851105) (by norm_num)
theorem B1794485 : Blo 1194414 1794485 := bbase (se 5 (by rfl) ⟨84116, by rfl⟩ : syracuseStep 1794485 = 168233) (by norm_num)
theorem B1343929 : Blo 1194414 1343929 := bbase (se 2 (by rfl) ⟨503973, by rfl⟩ : syracuseStep 1343929 = 1007947) (by norm_num)
theorem B2425277 : Blo 1194414 2425277 := bbase (se 3 (by rfl) ⟨454739, by rfl⟩ : syracuseStep 2425277 = 909479) (by norm_num)
theorem B1794509 : Blo 1194414 1794509 := bbase (se 3 (by rfl) ⟨336470, by rfl⟩ : syracuseStep 1794509 = 672941) (by norm_num)
theorem B2687453 : Blo 1194414 2687453 := bbase (se 3 (by rfl) ⟨503897, by rfl⟩ : syracuseStep 2687453 = 1007795) (by norm_num)
theorem B1343965 : Blo 1194414 1343965 := bbase (se 3 (by rfl) ⟨251993, by rfl⟩ : syracuseStep 1343965 = 503987) (by norm_num)
theorem B1794533 : Blo 1194414 1794533 := bbase (se 4 (by rfl) ⟨168237, by rfl⟩ : syracuseStep 1794533 = 336475) (by norm_num)
theorem B2015725 : Blo 1194414 2015725 := bbase (se 3 (by rfl) ⟨377948, by rfl⟩ : syracuseStep 2015725 = 755897) (by norm_num)
theorem B1794557 : Blo 1194414 1794557 := bbase (se 3 (by rfl) ⟨336479, by rfl⟩ : syracuseStep 1794557 = 672959) (by norm_num)
theorem B1344001 : Blo 1194414 1344001 := bbase (se 2 (by rfl) ⟨504000, by rfl⟩ : syracuseStep 1344001 = 1008001) (by norm_num)
theorem B3023365 : Blo 1194414 3023365 := bbase (se 4 (by rfl) ⟨283440, by rfl⟩ : syracuseStep 3023365 = 566881) (by norm_num)
theorem B2425349 : Blo 1194414 2425349 := bbase (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) (by norm_num)
theorem B3637781 : Blo 1194414 3637781 := bbase (se 6 (by rfl) ⟨85260, by rfl⟩ : syracuseStep 3637781 = 170521) (by norm_num)
theorem B1794581 : Blo 1194414 1794581 := bbase (se 6 (by rfl) ⟨42060, by rfl⟩ : syracuseStep 1794581 = 84121) (by norm_num)
theorem B2687525 : Blo 1194414 2687525 := bbase (se 4 (by rfl) ⟨251955, by rfl⟩ : syracuseStep 2687525 = 503911) (by norm_num)
theorem B1344037 : Blo 1194414 1344037 := bbase (se 4 (by rfl) ⟨126003, by rfl⟩ : syracuseStep 1344037 = 252007) (by norm_num)
theorem B1794605 : Blo 1194414 1794605 := bbase (se 3 (by rfl) ⟨336488, by rfl⟩ : syracuseStep 1794605 = 672977) (by norm_num)
theorem B2269757 : Blo 1194414 2269757 := bbase (se 3 (by rfl) ⟨425579, by rfl⟩ : syracuseStep 2269757 = 851159) (by norm_num)
theorem B2015813 : Blo 1194414 2015813 := bbase (se 4 (by rfl) ⟨188982, by rfl⟩ : syracuseStep 2015813 = 377965) (by norm_num)
theorem B1344073 : Blo 1194414 1344073 := bbase (se 2 (by rfl) ⟨504027, by rfl⟩ : syracuseStep 1344073 = 1008055) (by norm_num)
theorem B2687597 : Blo 1194414 2687597 := bbase (se 3 (by rfl) ⟨503924, by rfl⟩ : syracuseStep 2687597 = 1007849) (by norm_num)
theorem B1344109 : Blo 1194414 1344109 := bbase (se 3 (by rfl) ⟨252020, by rfl⟩ : syracuseStep 1344109 = 504041) (by norm_num)
theorem B3023477 : Blo 1194414 3023477 := bbase (se 5 (by rfl) ⟨141725, by rfl⟩ : syracuseStep 3023477 = 283451) (by norm_num)
theorem B1344145 : Blo 1194414 1344145 := bbase (se 2 (by rfl) ⟨504054, by rfl⟩ : syracuseStep 1344145 = 1008109) (by norm_num)
theorem B20439701 : Blo 1194414 20439701 := bbase (se 6 (by rfl) ⟨479055, by rfl⟩ : syracuseStep 20439701 = 958111) (by norm_num)
theorem B2687669 : Blo 1194414 2687669 := bbase (se 5 (by rfl) ⟨125984, by rfl⟩ : syracuseStep 2687669 = 251969) (by norm_num)
theorem B1344181 : Blo 1194414 1344181 := bbase (se 5 (by rfl) ⟨63008, by rfl⟩ : syracuseStep 1344181 = 126017) (by norm_num)
theorem B2015941 : Blo 1194414 2015941 := bbase (se 4 (by rfl) ⟨188994, by rfl⟩ : syracuseStep 2015941 = 377989) (by norm_num)
theorem B1344217 : Blo 1194414 1344217 := bbase (se 2 (by rfl) ⟨504081, by rfl⟩ : syracuseStep 1344217 = 1008163) (by norm_num)
theorem B7660277 : Blo 1194414 7660277 := bbase (se 5 (by rfl) ⟨359075, by rfl⟩ : syracuseStep 7660277 = 718151) (by norm_num)
theorem B2687741 : Blo 1194414 2687741 := bbase (se 3 (by rfl) ⟨503951, by rfl⟩ : syracuseStep 2687741 = 1007903) (by norm_num)
theorem B1344253 : Blo 1194414 1344253 := bbase (se 3 (by rfl) ⟨252047, by rfl⟩ : syracuseStep 1344253 = 504095) (by norm_num)
theorem B2155261 : Blo 1194414 2155261 := bbase (se 3 (by rfl) ⟨404111, by rfl⟩ : syracuseStep 2155261 = 808223) (by norm_num)
theorem B2016029 : Blo 1194414 2016029 := bbase (se 3 (by rfl) ⟨378005, by rfl⟩ : syracuseStep 2016029 = 756011) (by norm_num)
theorem B1344289 : Blo 1194414 1344289 := bbase (se 2 (by rfl) ⟨504108, by rfl⟩ : syracuseStep 1344289 = 1008217) (by norm_num)
theorem B3023669 : Blo 1194414 3023669 := bbase (se 5 (by rfl) ⟨141734, by rfl⟩ : syracuseStep 3023669 = 283469) (by norm_num)
theorem B2687813 : Blo 1194414 2687813 := bbase (se 4 (by rfl) ⟨251982, by rfl⟩ : syracuseStep 2687813 = 503965) (by norm_num)
theorem B1344325 : Blo 1194414 1344325 := bbase (se 4 (by rfl) ⟨126030, by rfl⟩ : syracuseStep 1344325 = 252061) (by norm_num)
theorem B2270045 : Blo 1194414 2270045 := bbase (se 3 (by rfl) ⟨425633, by rfl⟩ : syracuseStep 2270045 = 851267) (by norm_num)
theorem B1344361 : Blo 1194414 1344361 := bbase (se 2 (by rfl) ⟨504135, by rfl⟩ : syracuseStep 1344361 = 1008271) (by norm_num)
theorem B2687885 : Blo 1194414 2687885 := bbase (se 3 (by rfl) ⟨503978, by rfl⟩ : syracuseStep 2687885 = 1007957) (by norm_num)
theorem B1344397 : Blo 1194414 1344397 := bbase (se 3 (by rfl) ⟨252074, by rfl⟩ : syracuseStep 1344397 = 504149) (by norm_num)
theorem B2155405 : Blo 1194414 2155405 := bbase (se 3 (by rfl) ⟨404138, by rfl⟩ : syracuseStep 2155405 = 808277) (by norm_num)
theorem B2016157 : Blo 1194414 2016157 := bbase (se 3 (by rfl) ⟨378029, by rfl⟩ : syracuseStep 2016157 = 756059) (by norm_num)
theorem B1344433 : Blo 1194414 1344433 := bbase (se 2 (by rfl) ⟨504162, by rfl⟩ : syracuseStep 1344433 = 1008325) (by norm_num)
theorem B2687957 : Blo 1194414 2687957 := bbase (se 7 (by rfl) ⟨31499, by rfl⟩ : syracuseStep 2687957 = 62999) (by norm_num)
theorem B1344469 : Blo 1194414 1344469 := bbase (se 7 (by rfl) ⟨15755, by rfl⟩ : syracuseStep 1344469 = 31511) (by norm_num)
theorem B2155477 : Blo 1194414 2155477 := bbase (se 7 (by rfl) ⟨25259, by rfl⟩ : syracuseStep 2155477 = 50519) (by norm_num)
theorem B4031477 : Blo 1194414 4031477 := bbase (se 5 (by rfl) ⟨188975, by rfl⟩ : syracuseStep 4031477 = 377951) (by norm_num)
theorem B2016245 : Blo 1194414 2016245 := bbase (se 5 (by rfl) ⟨94511, by rfl⟩ : syracuseStep 2016245 = 189023) (by norm_num)
theorem B2270197 : Blo 1194414 2270197 := bbase (se 5 (by rfl) ⟨106415, by rfl⟩ : syracuseStep 2270197 = 212831) (by norm_num)
theorem B1344505 : Blo 1194414 1344505 := bbase (se 2 (by rfl) ⟨504189, by rfl⟩ : syracuseStep 1344505 = 1008379) (by norm_num)
theorem B2950141 : Blo 1194414 2950141 := bbase (se 3 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 2950141 = 1106303) (by norm_num)
theorem B2688029 : Blo 1194414 2688029 := bbase (se 3 (by rfl) ⟨504005, by rfl⟩ : syracuseStep 2688029 = 1008011) (by norm_num)
theorem B1344541 : Blo 1194414 1344541 := bbase (se 3 (by rfl) ⟨252101, by rfl⟩ : syracuseStep 1344541 = 504203) (by norm_num)
theorem B11486261 : Blo 1194414 11486261 := bbase (se 5 (by rfl) ⟨538418, by rfl⟩ : syracuseStep 11486261 = 1076837) (by norm_num)
theorem B1344577 : Blo 1194414 1344577 := bbase (se 2 (by rfl) ⟨504216, by rfl⟩ : syracuseStep 1344577 = 1008433) (by norm_num)
theorem B2688101 : Blo 1194414 2688101 := bbase (se 4 (by rfl) ⟨252009, by rfl⟩ : syracuseStep 2688101 = 504019) (by norm_num)
theorem B1344613 : Blo 1194414 1344613 := bbase (se 4 (by rfl) ⟨126057, by rfl⟩ : syracuseStep 1344613 = 252115) (by norm_num)
theorem B4310117 : Blo 1194414 4310117 := bbase (se 4 (by rfl) ⟨404073, by rfl⟩ : syracuseStep 4310117 = 808147) (by norm_num)
theorem B2016373 : Blo 1194414 2016373 := bbase (se 5 (by rfl) ⟨94517, by rfl⟩ : syracuseStep 2016373 = 189035) (by norm_num)
theorem B1344649 : Blo 1194414 1344649 := bbase (se 2 (by rfl) ⟨504243, by rfl⟩ : syracuseStep 1344649 = 1008487) (by norm_num)
theorem B3024013 : Blo 1194414 3024013 := bbase (se 3 (by rfl) ⟨567002, by rfl⟩ : syracuseStep 3024013 = 1134005) (by norm_num)
theorem B22103189 : Blo 1194414 22103189 := bbase (se 6 (by rfl) ⟨518043, by rfl⟩ : syracuseStep 22103189 = 1036087) (by norm_num)
theorem B2688173 : Blo 1194414 2688173 := bbase (se 3 (by rfl) ⟨504032, by rfl⟩ : syracuseStep 2688173 = 1008065) (by norm_num)
theorem B1344685 : Blo 1194414 1344685 := bbase (se 3 (by rfl) ⟨252128, by rfl⟩ : syracuseStep 1344685 = 504257) (by norm_num)
theorem B1533109 : Blo 1194414 1533109 := bbase (se 5 (by rfl) ⟨71864, by rfl⟩ : syracuseStep 1533109 = 143729) (by norm_num)
theorem B2016461 : Blo 1194414 2016461 := bbase (se 3 (by rfl) ⟨378086, by rfl⟩ : syracuseStep 2016461 = 756173) (by norm_num)
theorem B1344721 : Blo 1194414 1344721 := bbase (se 2 (by rfl) ⟨504270, by rfl⟩ : syracuseStep 1344721 = 1008541) (by norm_num)
theorem B5104853 : Blo 1194414 5104853 := bbase (se 7 (by rfl) ⟨59822, by rfl⟩ : syracuseStep 5104853 = 119645) (by norm_num)
theorem B2688245 : Blo 1194414 2688245 := bbase (se 5 (by rfl) ⟨126011, by rfl⟩ : syracuseStep 2688245 = 252023) (by norm_num)
theorem B1344757 : Blo 1194414 1344757 := bbase (se 5 (by rfl) ⟨63035, by rfl⟩ : syracuseStep 1344757 = 126071) (by norm_num)
theorem B3024125 : Blo 1194414 3024125 := bbase (se 3 (by rfl) ⟨567023, by rfl⟩ : syracuseStep 3024125 = 1134047) (by norm_num)
theorem B1344793 : Blo 1194414 1344793 := bbase (se 2 (by rfl) ⟨504297, by rfl⟩ : syracuseStep 1344793 = 1008595) (by norm_num)
theorem B2270501 : Blo 1194414 2270501 := bbase (se 4 (by rfl) ⟨212859, by rfl⟩ : syracuseStep 2270501 = 425719) (by norm_num)
theorem B3065149 : Blo 1194414 3065149 := bbase (se 3 (by rfl) ⟨574715, by rfl⟩ : syracuseStep 3065149 = 1149431) (by norm_num)
theorem B2688317 : Blo 1194414 2688317 := bbase (se 3 (by rfl) ⟨504059, by rfl⟩ : syracuseStep 2688317 = 1008119) (by norm_num)
theorem B1344829 : Blo 1194414 1344829 := bbase (se 3 (by rfl) ⟨252155, by rfl⟩ : syracuseStep 1344829 = 504311) (by norm_num)
theorem B2016589 : Blo 1194414 2016589 := bbase (se 3 (by rfl) ⟨378110, by rfl⟩ : syracuseStep 2016589 = 756221) (by norm_num)
theorem B1344865 : Blo 1194414 1344865 := bbase (se 2 (by rfl) ⟨504324, by rfl⟩ : syracuseStep 1344865 = 1008649) (by norm_num)
theorem B2688389 : Blo 1194414 2688389 := bbase (se 4 (by rfl) ⟨252036, by rfl⟩ : syracuseStep 2688389 = 504073) (by norm_num)
theorem B4089221 : Blo 1194414 4089221 := bbase (se 4 (by rfl) ⟨383364, by rfl⟩ : syracuseStep 4089221 = 766729) (by norm_num)
theorem B1344901 : Blo 1194414 1344901 := bbase (se 4 (by rfl) ⟨126084, by rfl⟩ : syracuseStep 1344901 = 252169) (by norm_num)
theorem B4031909 : Blo 1194414 4031909 := bbase (se 4 (by rfl) ⟨377991, by rfl⟩ : syracuseStep 4031909 = 755983) (by norm_num)
theorem B2016677 : Blo 1194414 2016677 := bbase (se 4 (by rfl) ⟨189063, by rfl⟩ : syracuseStep 2016677 = 378127) (by norm_num)
theorem B1344937 : Blo 1194414 1344937 := bbase (se 2 (by rfl) ⟨504351, by rfl⟩ : syracuseStep 1344937 = 1008703) (by norm_num)
theorem B3024317 : Blo 1194414 3024317 := bbase (se 3 (by rfl) ⟨567059, by rfl⟩ : syracuseStep 3024317 = 1134119) (by norm_num)
theorem B2688461 : Blo 1194414 2688461 := bbase (se 3 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 2688461 = 1008173) (by norm_num)
theorem B1344973 : Blo 1194414 1344973 := bbase (se 3 (by rfl) ⟨252182, by rfl⟩ : syracuseStep 1344973 = 504365) (by norm_num)
theorem B6055397 : Blo 1194414 6055397 := bbase (se 4 (by rfl) ⟨567693, by rfl⟩ : syracuseStep 6055397 = 1135387) (by norm_num)
theorem B1345009 : Blo 1194414 1345009 := bbase (se 2 (by rfl) ⟨504378, by rfl⟩ : syracuseStep 1345009 = 1008757) (by norm_num)
theorem B3065357 : Blo 1194414 3065357 := bbase (se 3 (by rfl) ⟨574754, by rfl⟩ : syracuseStep 3065357 = 1149509) (by norm_num)
theorem B2688533 : Blo 1194414 2688533 := bbase (se 6 (by rfl) ⟨63012, by rfl⟩ : syracuseStep 2688533 = 126025) (by norm_num)
theorem B1345045 : Blo 1194414 1345045 := bbase (se 6 (by rfl) ⟨31524, by rfl⟩ : syracuseStep 1345045 = 63049) (by norm_num)
theorem B2016805 : Blo 1194414 2016805 := bbase (se 4 (by rfl) ⟨189075, by rfl⟩ : syracuseStep 2016805 = 378151) (by norm_num)
theorem B3229237 : Blo 1194414 3229237 := bbase (se 5 (by rfl) ⟨151370, by rfl⟩ : syracuseStep 3229237 = 302741) (by norm_num)
theorem B1345081 : Blo 1194414 1345081 := bbase (se 2 (by rfl) ⟨504405, by rfl⟩ : syracuseStep 1345081 = 1008811) (by norm_num)
theorem B2909773 : Blo 1194414 2909773 := bbase (se 3 (by rfl) ⟨545582, by rfl⟩ : syracuseStep 2909773 = 1091165) (by norm_num)
theorem B2688605 : Blo 1194414 2688605 := bbase (se 3 (by rfl) ⟨504113, by rfl⟩ : syracuseStep 2688605 = 1008227) (by norm_num)
theorem B1345117 : Blo 1194414 1345117 := bbase (se 3 (by rfl) ⟨252209, by rfl⟩ : syracuseStep 1345117 = 504419) (by norm_num)
theorem B3229301 : Blo 1194414 3229301 := bbase (se 5 (by rfl) ⟨151373, by rfl⟩ : syracuseStep 3229301 = 302747) (by norm_num)
theorem B2016893 : Blo 1194414 2016893 := bbase (se 3 (by rfl) ⟨378167, by rfl⟩ : syracuseStep 2016893 = 756335) (by norm_num)
theorem B1345153 : Blo 1194414 1345153 := bbase (se 2 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 1345153 = 1008865) (by norm_num)
theorem B2688677 : Blo 1194414 2688677 := bbase (se 4 (by rfl) ⟨252063, by rfl⟩ : syracuseStep 2688677 = 504127) (by norm_num)
theorem B1345189 : Blo 1194414 1345189 := bbase (se 4 (by rfl) ⟨126111, by rfl⟩ : syracuseStep 1345189 = 252223) (by norm_num)
theorem B1345225 : Blo 1194414 1345225 := bbase (se 2 (by rfl) ⟨504459, by rfl⟩ : syracuseStep 1345225 = 1008919) (by norm_num)
theorem B2688749 : Blo 1194414 2688749 := bbase (se 3 (by rfl) ⟨504140, by rfl⟩ : syracuseStep 2688749 = 1008281) (by norm_num)
theorem B1345261 : Blo 1194414 1345261 := bbase (se 3 (by rfl) ⟨252236, by rfl⟩ : syracuseStep 1345261 = 504473) (by norm_num)
theorem B2017021 : Blo 1194414 2017021 := bbase (se 3 (by rfl) ⟨378191, by rfl⟩ : syracuseStep 2017021 = 756383) (by norm_num)
theorem B1345297 : Blo 1194414 1345297 := bbase (se 2 (by rfl) ⟨504486, by rfl⟩ : syracuseStep 1345297 = 1008973) (by norm_num)
theorem B3024661 : Blo 1194414 3024661 := bbase (se 6 (by rfl) ⟨70890, by rfl⟩ : syracuseStep 3024661 = 141781) (by norm_num)
theorem B1615645 : Blo 1194414 1615645 := bbase (se 3 (by rfl) ⟨302933, by rfl⟩ : syracuseStep 1615645 = 605867) (by norm_num)
theorem B2688821 : Blo 1194414 2688821 := bbase (se 5 (by rfl) ⟨126038, by rfl⟩ : syracuseStep 2688821 = 252077) (by norm_num)
theorem B1345333 : Blo 1194414 1345333 := bbase (se 5 (by rfl) ⟨63062, by rfl⟩ : syracuseStep 1345333 = 126125) (by norm_num)
theorem B4032341 : Blo 1194414 4032341 := bbase (se 9 (by rfl) ⟨11813, by rfl⟩ : syracuseStep 4032341 = 23627) (by norm_num)
theorem B2017109 : Blo 1194414 2017109 := bbase (se 9 (by rfl) ⟨5909, by rfl⟩ : syracuseStep 2017109 = 11819) (by norm_num)
theorem B1345369 : Blo 1194414 1345369 := bbase (se 2 (by rfl) ⟨504513, by rfl⟩ : syracuseStep 1345369 = 1009027) (by norm_num)
theorem B2688893 : Blo 1194414 2688893 := bbase (se 3 (by rfl) ⟨504167, by rfl⟩ : syracuseStep 2688893 = 1008335) (by norm_num)
theorem B1345405 : Blo 1194414 1345405 := bbase (se 3 (by rfl) ⟨252263, by rfl⟩ : syracuseStep 1345405 = 504527) (by norm_num)
theorem B3401605 : Blo 1194414 3401605 := bbase (se 4 (by rfl) ⟨318900, by rfl⟩ : syracuseStep 3401605 = 637801) (by norm_num)
theorem B6047621 : Blo 1194414 6047621 := bbase (se 4 (by rfl) ⟨566964, by rfl⟩ : syracuseStep 6047621 = 1133929) (by norm_num)
theorem B3024773 : Blo 1194414 3024773 := bbase (se 4 (by rfl) ⟨283572, by rfl⟩ : syracuseStep 3024773 = 567145) (by norm_num)
theorem B1345441 : Blo 1194414 1345441 := bbase (se 2 (by rfl) ⟨504540, by rfl⟩ : syracuseStep 1345441 = 1009081) (by norm_num)
theorem B1574845 : Blo 1194414 1574845 := bbase (se 3 (by rfl) ⟨295283, by rfl⟩ : syracuseStep 1574845 = 590567) (by norm_num)
theorem B2688965 : Blo 1194414 2688965 := bbase (se 4 (by rfl) ⟨252090, by rfl⟩ : syracuseStep 2688965 = 504181) (by norm_num)
theorem B1345477 : Blo 1194414 1345477 := bbase (se 4 (by rfl) ⟨126138, by rfl⟩ : syracuseStep 1345477 = 252277) (by norm_num)
theorem B2017237 : Blo 1194414 2017237 := bbase (se 7 (by rfl) ⟨23639, by rfl⟩ : syracuseStep 2017237 = 47279) (by norm_num)
theorem B1345513 : Blo 1194414 1345513 := bbase (se 2 (by rfl) ⟨504567, by rfl⟩ : syracuseStep 1345513 = 1009135) (by norm_num)
theorem B2689037 : Blo 1194414 2689037 := bbase (se 3 (by rfl) ⟨504194, by rfl⟩ : syracuseStep 2689037 = 1008389) (by norm_num)
theorem B1345549 : Blo 1194414 1345549 := bbase (se 3 (by rfl) ⟨252290, by rfl⟩ : syracuseStep 1345549 = 504581) (by norm_num)
theorem B13273109 : Blo 1194414 13273109 := bbase (se 6 (by rfl) ⟨311088, by rfl⟩ : syracuseStep 13273109 = 622177) (by norm_num)
theorem B2271253 : Blo 1194414 2271253 := bbase (se 6 (by rfl) ⟨53232, by rfl⟩ : syracuseStep 2271253 = 106465) (by norm_num)
theorem B2017325 : Blo 1194414 2017325 := bbase (se 3 (by rfl) ⟨378248, by rfl⟩ : syracuseStep 2017325 = 756497) (by norm_num)
theorem B1345585 : Blo 1194414 1345585 := bbase (se 2 (by rfl) ⟨504594, by rfl⟩ : syracuseStep 1345585 = 1009189) (by norm_num)
theorem B3024965 : Blo 1194414 3024965 := bbase (se 4 (by rfl) ⟨283590, by rfl⟩ : syracuseStep 3024965 = 567181) (by norm_num)
theorem B2689109 : Blo 1194414 2689109 := bbase (se 8 (by rfl) ⟨15756, by rfl⟩ : syracuseStep 2689109 = 31513) (by norm_num)
theorem B1345621 : Blo 1194414 1345621 := bbase (se 8 (by rfl) ⟨7884, by rfl⟩ : syracuseStep 1345621 = 15769) (by norm_num)
theorem B1345657 : Blo 1194414 1345657 := bbase (se 2 (by rfl) ⟨504621, by rfl⟩ : syracuseStep 1345657 = 1009243) (by norm_num)
theorem B2689181 : Blo 1194414 2689181 := bbase (se 3 (by rfl) ⟨504221, by rfl⟩ : syracuseStep 2689181 = 1008443) (by norm_num)
theorem B1345693 : Blo 1194414 1345693 := bbase (se 3 (by rfl) ⟨252317, by rfl⟩ : syracuseStep 1345693 = 504635) (by norm_num)
theorem B1435817 : Blo 1194414 1435817 := bbase (se 2 (by rfl) ⟨538431, by rfl⟩ : syracuseStep 1435817 = 1076863) (by norm_num)
theorem B2017453 : Blo 1194414 2017453 := bbase (se 3 (by rfl) ⟨378272, by rfl⟩ : syracuseStep 2017453 = 756545) (by norm_num)
theorem B9078965 : Blo 1194414 9078965 := bbase (se 5 (by rfl) ⟨425576, by rfl⟩ : syracuseStep 9078965 = 851153) (by norm_num)
theorem B1345729 : Blo 1194414 1345729 := bbase (se 2 (by rfl) ⟨504648, by rfl⟩ : syracuseStep 1345729 = 1009297) (by norm_num)
theorem B5105861 : Blo 1194414 5105861 := bbase (se 4 (by rfl) ⟨478674, by rfl⟩ : syracuseStep 5105861 = 957349) (by norm_num)
theorem B2689253 : Blo 1194414 2689253 := bbase (se 4 (by rfl) ⟨252117, by rfl⟩ : syracuseStep 2689253 = 504235) (by norm_num)
theorem B1345765 : Blo 1194414 1345765 := bbase (se 4 (by rfl) ⟨126165, by rfl⟩ : syracuseStep 1345765 = 252331) (by norm_num)
theorem B4032773 : Blo 1194414 4032773 := bbase (se 4 (by rfl) ⟨378072, by rfl⟩ : syracuseStep 4032773 = 756145) (by norm_num)
theorem B2017541 : Blo 1194414 2017541 := bbase (se 4 (by rfl) ⟨189144, by rfl⟩ : syracuseStep 2017541 = 378289) (by norm_num)
theorem B1345801 : Blo 1194414 1345801 := bbase (se 2 (by rfl) ⟨504675, by rfl⟩ : syracuseStep 1345801 = 1009351) (by norm_num)
theorem B2689325 : Blo 1194414 2689325 := bbase (se 3 (by rfl) ⟨504248, by rfl⟩ : syracuseStep 2689325 = 1008497) (by norm_num)
theorem B1345837 : Blo 1194414 1345837 := bbase (se 3 (by rfl) ⟨252344, by rfl⟩ : syracuseStep 1345837 = 504689) (by norm_num)
theorem B1345873 : Blo 1194414 1345873 := bbase (se 2 (by rfl) ⟨504702, by rfl⟩ : syracuseStep 1345873 = 1009405) (by norm_num)
theorem B2689397 : Blo 1194414 2689397 := bbase (se 5 (by rfl) ⟨126065, by rfl⟩ : syracuseStep 2689397 = 252131) (by norm_num)
theorem B1345909 : Blo 1194414 1345909 := bbase (se 5 (by rfl) ⟨63089, by rfl⟩ : syracuseStep 1345909 = 126179) (by norm_num)
theorem B2017669 : Blo 1194414 2017669 := bbase (se 4 (by rfl) ⟨189156, by rfl⟩ : syracuseStep 2017669 = 378313) (by norm_num)
theorem B4540805 : Blo 1194414 4540805 := bbase (se 4 (by rfl) ⟨425700, by rfl⟩ : syracuseStep 4540805 = 851401) (by norm_num)
theorem B1345945 : Blo 1194414 1345945 := bbase (se 2 (by rfl) ⟨504729, by rfl⟩ : syracuseStep 1345945 = 1009459) (by norm_num)
theorem B3025309 : Blo 1194414 3025309 := bbase (se 3 (by rfl) ⟨567245, by rfl⟩ : syracuseStep 3025309 = 1134491) (by norm_num)
theorem B2689469 : Blo 1194414 2689469 := bbase (se 3 (by rfl) ⟨504275, by rfl⟩ : syracuseStep 2689469 = 1008551) (by norm_num)
theorem B1436125 : Blo 1194414 1436125 := bbase (se 3 (by rfl) ⟨269273, by rfl⟩ : syracuseStep 1436125 = 538547) (by norm_num)
theorem B2017757 : Blo 1194414 2017757 := bbase (se 3 (by rfl) ⟨378329, by rfl⟩ : syracuseStep 2017757 = 756659) (by norm_num)
theorem B2689541 : Blo 1194414 2689541 := bbase (se 4 (by rfl) ⟨252144, by rfl⟩ : syracuseStep 2689541 = 504289) (by norm_num)
theorem B3025421 : Blo 1194414 3025421 := bbase (se 3 (by rfl) ⟨567266, by rfl⟩ : syracuseStep 3025421 = 1134533) (by norm_num)
theorem B1436225 : Blo 1194414 1436225 := bbase (se 2 (by rfl) ⟨538584, by rfl⟩ : syracuseStep 1436225 = 1077169) (by norm_num)
theorem B3828293 : Blo 1194414 3828293 := bbase (se 4 (by rfl) ⟨358902, by rfl⟩ : syracuseStep 3828293 = 717805) (by norm_num)
theorem B2689613 : Blo 1194414 2689613 := bbase (se 3 (by rfl) ⟨504302, by rfl⟩ : syracuseStep 2689613 = 1008605) (by norm_num)
theorem B9071189 : Blo 1194414 9071189 := bbase (se 8 (by rfl) ⟨53151, by rfl⟩ : syracuseStep 9071189 = 106303) (by norm_num)
theorem B2017885 : Blo 1194414 2017885 := bbase (se 3 (by rfl) ⟨378353, by rfl⟩ : syracuseStep 2017885 = 756707) (by norm_num)
theorem B2689685 : Blo 1194414 2689685 := bbase (se 6 (by rfl) ⟨63039, by rfl⟩ : syracuseStep 2689685 = 126079) (by norm_num)
theorem B4541093 : Blo 1194414 4541093 := bbase (se 4 (by rfl) ⟨425727, by rfl⟩ : syracuseStep 4541093 = 851455) (by norm_num)
theorem B4033205 : Blo 1194414 4033205 := bbase (se 5 (by rfl) ⟨189056, by rfl⟩ : syracuseStep 4033205 = 378113) (by norm_num)
theorem B2017973 : Blo 1194414 2017973 := bbase (se 5 (by rfl) ⟨94592, by rfl⟩ : syracuseStep 2017973 = 189185) (by norm_num)
theorem B3025613 : Blo 1194414 3025613 := bbase (se 3 (by rfl) ⟨567302, by rfl⟩ : syracuseStep 3025613 = 1134605) (by norm_num)
theorem B2689757 : Blo 1194414 2689757 := bbase (se 3 (by rfl) ⟨504329, by rfl⟩ : syracuseStep 2689757 = 1008659) (by norm_num)
theorem B6056693 : Blo 1194414 6056693 := bbase (se 5 (by rfl) ⟨283907, by rfl⟩ : syracuseStep 6056693 = 567815) (by norm_num)
theorem B2689829 : Blo 1194414 2689829 := bbase (se 4 (by rfl) ⟨252171, by rfl⟩ : syracuseStep 2689829 = 504343) (by norm_num)
theorem B2018101 : Blo 1194414 2018101 := bbase (se 5 (by rfl) ⟨94598, by rfl⟩ : syracuseStep 2018101 = 189197) (by norm_num)
theorem B2689901 : Blo 1194414 2689901 := bbase (se 3 (by rfl) ⟨504356, by rfl⟩ : syracuseStep 2689901 = 1008713) (by norm_num)
theorem B2018189 : Blo 1194414 2018189 := bbase (se 3 (by rfl) ⟨378410, by rfl⟩ : syracuseStep 2018189 = 756821) (by norm_num)
theorem B14740373 : Blo 1194414 14740373 := bbase (se 6 (by rfl) ⟨345477, by rfl⟩ : syracuseStep 14740373 = 690955) (by norm_num)
theorem B2689973 : Blo 1194414 2689973 := bbase (se 5 (by rfl) ⟨126092, by rfl⟩ : syracuseStep 2689973 = 252185) (by norm_num)
theorem B1436629 : Blo 1194414 1436629 := bbase (se 7 (by rfl) ⟨16835, by rfl⟩ : syracuseStep 1436629 = 33671) (by norm_num)
theorem B2690045 : Blo 1194414 2690045 := bbase (se 3 (by rfl) ⟨504383, by rfl⟩ : syracuseStep 2690045 = 1008767) (by norm_num)
theorem B2018317 : Blo 1194414 2018317 := bbase (se 3 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 2018317 = 756869) (by norm_num)
theorem B3025957 : Blo 1194414 3025957 := bbase (se 4 (by rfl) ⟨283683, by rfl⟩ : syracuseStep 3025957 = 567367) (by norm_num)
theorem B2690117 : Blo 1194414 2690117 := bbase (se 4 (by rfl) ⟨252198, by rfl⟩ : syracuseStep 2690117 = 504397) (by norm_num)
theorem B4033637 : Blo 1194414 4033637 := bbase (se 4 (by rfl) ⟨378153, by rfl⟩ : syracuseStep 4033637 = 756307) (by norm_num)
theorem B2018405 : Blo 1194414 2018405 := bbase (se 4 (by rfl) ⟨189225, by rfl⟩ : syracuseStep 2018405 = 378451) (by norm_num)
theorem B2690189 : Blo 1194414 2690189 := bbase (se 3 (by rfl) ⟨504410, by rfl⟩ : syracuseStep 2690189 = 1008821) (by norm_num)
theorem B6048917 : Blo 1194414 6048917 := bbase (se 6 (by rfl) ⟨141771, by rfl⟩ : syracuseStep 6048917 = 283543) (by norm_num)
theorem B3026069 : Blo 1194414 3026069 := bbase (se 6 (by rfl) ⟨70923, by rfl⟩ : syracuseStep 3026069 = 141847) (by norm_num)
theorem B2690261 : Blo 1194414 2690261 := bbase (se 7 (by rfl) ⟨31526, by rfl⟩ : syracuseStep 2690261 = 63053) (by norm_num)
theorem B2018533 : Blo 1194414 2018533 := bbase (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) (by norm_num)
theorem B2690333 : Blo 1194414 2690333 := bbase (se 3 (by rfl) ⟨504437, by rfl⟩ : syracuseStep 2690333 = 1008875) (by norm_num)
theorem B2624797 : Blo 1194414 2624797 := bbase (se 3 (by rfl) ⟨492149, by rfl⟩ : syracuseStep 2624797 = 984299) (by norm_num)
theorem B2551085 : Blo 1194414 2551085 := bbase (se 3 (by rfl) ⟨478328, by rfl⟩ : syracuseStep 2551085 = 956657) (by norm_num)
theorem B2018621 : Blo 1194414 2018621 := bbase (se 3 (by rfl) ⟨378491, by rfl⟩ : syracuseStep 2018621 = 756983) (by norm_num)
theorem B3026261 : Blo 1194414 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B1437013 : Blo 1194414 1437013 := bbase (se 11 (by rfl) ⟨1052, by rfl⟩ : syracuseStep 1437013 = 2105) (by norm_num)
theorem B3403109 : Blo 1194414 3403109 := bbase (se 4 (by rfl) ⟨319041, by rfl⟩ : syracuseStep 3403109 = 638083) (by norm_num)
theorem B2690405 : Blo 1194414 2690405 := bbase (se 4 (by rfl) ⟨252225, by rfl⟩ : syracuseStep 2690405 = 504451) (by norm_num)
theorem B2690477 : Blo 1194414 2690477 := bbase (se 3 (by rfl) ⟨504464, by rfl⟩ : syracuseStep 2690477 = 1008929) (by norm_num)
theorem B2018749 : Blo 1194414 2018749 := bbase (se 3 (by rfl) ⟨378515, by rfl⟩ : syracuseStep 2018749 = 757031) (by norm_num)
theorem B3452357 : Blo 1194414 3452357 := bbase (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) (by norm_num)
theorem B2690549 : Blo 1194414 2690549 := bbase (se 5 (by rfl) ⟨126119, by rfl⟩ : syracuseStep 2690549 = 252239) (by norm_num)
theorem B2870797 : Blo 1194414 2870797 := bbase (se 3 (by rfl) ⟨538274, by rfl⟩ : syracuseStep 2870797 = 1076549) (by norm_num)
theorem B4034069 : Blo 1194414 4034069 := bbase (se 6 (by rfl) ⟨94548, by rfl⟩ : syracuseStep 4034069 = 189097) (by norm_num)
theorem B2018837 : Blo 1194414 2018837 := bbase (se 6 (by rfl) ⟨47316, by rfl⟩ : syracuseStep 2018837 = 94633) (by norm_num)
theorem B2551333 : Blo 1194414 2551333 := bbase (se 4 (by rfl) ⟨239187, by rfl⟩ : syracuseStep 2551333 = 478375) (by norm_num)
theorem B1363493 : Blo 1194414 1363493 := bbase (se 4 (by rfl) ⟨127827, by rfl⟩ : syracuseStep 1363493 = 255655) (by norm_num)
theorem B2690621 : Blo 1194414 2690621 := bbase (se 3 (by rfl) ⟨504491, by rfl⟩ : syracuseStep 2690621 = 1008983) (by norm_num)
theorem B2870893 : Blo 1194414 2870893 := bbase (se 3 (by rfl) ⟨538292, by rfl⟩ : syracuseStep 2870893 = 1076585) (by norm_num)
theorem B2690693 : Blo 1194414 2690693 := bbase (se 4 (by rfl) ⟨252252, by rfl⟩ : syracuseStep 2690693 = 504505) (by norm_num)
theorem B3026605 : Blo 1194414 3026605 := bbase (se 3 (by rfl) ⟨567488, by rfl⟩ : syracuseStep 3026605 = 1134977) (by norm_num)
theorem B2690765 : Blo 1194414 2690765 := bbase (se 3 (by rfl) ⟨504518, by rfl⟩ : syracuseStep 2690765 = 1009037) (by norm_num)
theorem B6803189 : Blo 1194414 6803189 := bbase (se 5 (by rfl) ⟨318899, by rfl⟩ : syracuseStep 6803189 = 637799) (by norm_num)
theorem B2690837 : Blo 1194414 2690837 := bbase (se 6 (by rfl) ⟨63066, by rfl⟩ : syracuseStep 2690837 = 126133) (by norm_num)
theorem B3026717 : Blo 1194414 3026717 := bbase (se 3 (by rfl) ⟨567509, by rfl⟩ : syracuseStep 3026717 = 1135019) (by norm_num)
theorem B4845365 : Blo 1194414 4845365 := bbase (se 5 (by rfl) ⟨227126, by rfl⟩ : syracuseStep 4845365 = 454253) (by norm_num)
theorem B4542277 : Blo 1194414 4542277 := bbase (se 4 (by rfl) ⟨425838, by rfl⟩ : syracuseStep 4542277 = 851677) (by norm_num)
theorem B5820245 : Blo 1194414 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B11497301 : Blo 1194414 11497301 := bbase (se 9 (by rfl) ⟨33683, by rfl⟩ : syracuseStep 11497301 = 67367) (by norm_num)
theorem B2690909 : Blo 1194414 2690909 := bbase (se 3 (by rfl) ⟨504545, by rfl⟩ : syracuseStep 2690909 = 1009091) (by norm_num)
theorem B2690981 : Blo 1194414 2690981 := bbase (se 4 (by rfl) ⟨252279, by rfl⟩ : syracuseStep 2690981 = 504559) (by norm_num)
theorem B5107637 : Blo 1194414 5107637 := bbase (se 5 (by rfl) ⟨239420, by rfl⟩ : syracuseStep 5107637 = 478841) (by norm_num)
theorem B4034501 : Blo 1194414 4034501 := bbase (se 4 (by rfl) ⟨378234, by rfl⟩ : syracuseStep 4034501 = 756469) (by norm_num)
theorem B3026909 : Blo 1194414 3026909 := bbase (se 3 (by rfl) ⟨567545, by rfl⟩ : syracuseStep 3026909 = 1135091) (by norm_num)
theorem B2691053 : Blo 1194414 2691053 := bbase (se 3 (by rfl) ⟨504572, by rfl⟩ : syracuseStep 2691053 = 1009145) (by norm_num)
theorem B5451781 : Blo 1194414 5451781 := bbase (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) (by norm_num)
theorem B2551837 : Blo 1194414 2551837 := bbase (se 3 (by rfl) ⟨478469, by rfl⟩ : syracuseStep 2551837 = 956939) (by norm_num)
theorem B2691125 : Blo 1194414 2691125 := bbase (se 5 (by rfl) ⟨126146, by rfl⟩ : syracuseStep 2691125 = 252293) (by norm_num)
theorem B1364077 : Blo 1194414 1364077 := bbase (se 3 (by rfl) ⟨255764, by rfl⟩ : syracuseStep 1364077 = 511529) (by norm_num)
theorem B2871413 : Blo 1194414 2871413 := bbase (se 5 (by rfl) ⟨134597, by rfl⟩ : syracuseStep 2871413 = 269195) (by norm_num)
theorem B4542581 : Blo 1194414 4542581 := bbase (se 5 (by rfl) ⟨212933, by rfl⟩ : syracuseStep 4542581 = 425867) (by norm_num)
theorem B2101373 : Blo 1194414 2101373 := bbase (se 3 (by rfl) ⟨394007, by rfl⟩ : syracuseStep 2101373 = 788015) (by norm_num)
theorem B2691197 : Blo 1194414 2691197 := bbase (se 3 (by rfl) ⟨504599, by rfl⟩ : syracuseStep 2691197 = 1009199) (by norm_num)
theorem B2044037 : Blo 1194414 2044037 := bbase (se 4 (by rfl) ⟨191628, by rfl⟩ : syracuseStep 2044037 = 383257) (by norm_num)
theorem B2691269 : Blo 1194414 2691269 := bbase (se 4 (by rfl) ⟨252306, by rfl⟩ : syracuseStep 2691269 = 504613) (by norm_num)
theorem B22974677 : Blo 1194414 22974677 := bbase (se 7 (by rfl) ⟨269234, by rfl⟩ : syracuseStep 22974677 = 538469) (by norm_num)
theorem B2691341 : Blo 1194414 2691341 := bbase (se 3 (by rfl) ⟨504626, by rfl⟩ : syracuseStep 2691341 = 1009253) (by norm_num)
theorem B1511713 : Blo 1194414 1511713 := bbase (se 2 (by rfl) ⟨566892, by rfl⟩ : syracuseStep 1511713 = 1133785) (by norm_num)
theorem B1364269 : Blo 1194414 1364269 := bbase (se 3 (by rfl) ⟨255800, by rfl⟩ : syracuseStep 1364269 = 511601) (by norm_num)
theorem B3027253 : Blo 1194414 3027253 := bbase (se 5 (by rfl) ⟨141902, by rfl⟩ : syracuseStep 3027253 = 283805) (by norm_num)
theorem B2691413 : Blo 1194414 2691413 := bbase (se 10 (by rfl) ⟨3942, by rfl⟩ : syracuseStep 2691413 = 7885) (by norm_num)
theorem B34959701 : Blo 1194414 34959701 := bbase (se 10 (by rfl) ⟨51210, by rfl⟩ : syracuseStep 34959701 = 102421) (by norm_num)
theorem B4034933 : Blo 1194414 4034933 := bbase (se 5 (by rfl) ⟨189137, by rfl⟩ : syracuseStep 4034933 = 378275) (by norm_num)
theorem B2691485 : Blo 1194414 2691485 := bbase (se 3 (by rfl) ⟨504653, by rfl⟩ : syracuseStep 2691485 = 1009307) (by norm_num)
theorem B6050213 : Blo 1194414 6050213 := bbase (se 4 (by rfl) ⟨567207, by rfl⟩ : syracuseStep 6050213 = 1134415) (by norm_num)
theorem B3027365 : Blo 1194414 3027365 := bbase (se 4 (by rfl) ⟨283815, by rfl⟩ : syracuseStep 3027365 = 567631) (by norm_num)
theorem B1511885 : Blo 1194414 1511885 := bbase (se 3 (by rfl) ⟨283478, by rfl⟩ : syracuseStep 1511885 = 566957) (by norm_num)
theorem B2691557 : Blo 1194414 2691557 := bbase (se 4 (by rfl) ⟨252333, by rfl⟩ : syracuseStep 2691557 = 504667) (by norm_num)
theorem B1511941 : Blo 1194414 1511941 := bbase (se 4 (by rfl) ⟨141744, by rfl⟩ : syracuseStep 1511941 = 283489) (by norm_num)
theorem B2691629 : Blo 1194414 2691629 := bbase (se 3 (by rfl) ⟨504680, by rfl⟩ : syracuseStep 2691629 = 1009361) (by norm_num)
theorem B1913429 : Blo 1194414 1913429 := bbase (se 8 (by rfl) ⟨11211, by rfl⟩ : syracuseStep 1913429 = 22423) (by norm_num)
theorem B1512037 : Blo 1194414 1512037 := bbase (se 4 (by rfl) ⟨141753, by rfl⟩ : syracuseStep 1512037 = 283507) (by norm_num)
theorem B3027557 : Blo 1194414 3027557 := bbase (se 4 (by rfl) ⟨283833, by rfl⟩ : syracuseStep 3027557 = 567667) (by norm_num)
theorem B2691701 : Blo 1194414 2691701 := bbase (se 5 (by rfl) ⟨126173, by rfl⟩ : syracuseStep 2691701 = 252347) (by norm_num)
theorem B3592837 : Blo 1194414 3592837 := bbase (se 4 (by rfl) ⟨336828, by rfl⟩ : syracuseStep 3592837 = 673657) (by norm_num)
theorem B2871941 : Blo 1194414 2871941 := bbase (se 4 (by rfl) ⟨269244, by rfl⟩ : syracuseStep 2871941 = 538489) (by norm_num)
theorem B8622773 : Blo 1194414 8622773 := bbase (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) (by norm_num)
theorem B2691773 : Blo 1194414 2691773 := bbase (se 3 (by rfl) ⟨504707, by rfl⟩ : syracuseStep 2691773 = 1009415) (by norm_num)
theorem B3830485 : Blo 1194414 3830485 := bbase (se 7 (by rfl) ⟨44888, by rfl⟩ : syracuseStep 3830485 = 89777) (by norm_num)
theorem B2691845 : Blo 1194414 2691845 := bbase (se 4 (by rfl) ⟨252360, by rfl⟩ : syracuseStep 2691845 = 504721) (by norm_num)
theorem B1512209 : Blo 1194414 1512209 := bbase (se 2 (by rfl) ⟨567078, by rfl⟩ : syracuseStep 1512209 = 1134157) (by norm_num)
theorem B4035365 : Blo 1194414 4035365 := bbase (se 4 (by rfl) ⟨378315, by rfl⟩ : syracuseStep 4035365 = 756631) (by norm_num)
theorem B1512265 : Blo 1194414 1512265 := bbase (se 2 (by rfl) ⟨567099, by rfl⟩ : syracuseStep 1512265 = 1134199) (by norm_num)
theorem B2691917 : Blo 1194414 2691917 := bbase (se 3 (by rfl) ⟨504734, by rfl⟩ : syracuseStep 2691917 = 1009469) (by norm_num)
theorem B7656277 : Blo 1194414 7656277 := bbase (se 9 (by rfl) ⟨22430, by rfl⟩ : syracuseStep 7656277 = 44861) (by norm_num)
theorem B2872181 : Blo 1194414 2872181 := bbase (se 5 (by rfl) ⟨134633, by rfl⟩ : syracuseStep 2872181 = 269267) (by norm_num)
theorem B5747573 : Blo 1194414 5747573 := bbase (se 5 (by rfl) ⟨269417, by rfl⟩ : syracuseStep 5747573 = 538835) (by norm_num)
theorem B2552725 : Blo 1194414 2552725 := bbase (se 6 (by rfl) ⟨59829, by rfl⟩ : syracuseStep 2552725 = 119659) (by norm_num)
theorem B3404693 : Blo 1194414 3404693 := bbase (se 6 (by rfl) ⟨79797, by rfl⟩ : syracuseStep 3404693 = 159595) (by norm_num)
theorem B1553317 : Blo 1194414 1553317 := bbase (se 4 (by rfl) ⟨145623, by rfl⟩ : syracuseStep 1553317 = 291247) (by norm_num)
theorem B1512361 : Blo 1194414 1512361 := bbase (se 2 (by rfl) ⟨567135, by rfl⟩ : syracuseStep 1512361 = 1134271) (by norm_num)
theorem B3027901 : Blo 1194414 3027901 := bbase (se 3 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 3027901 = 1135463) (by norm_num)
theorem B5747669 : Blo 1194414 5747669 := bbase (se 7 (by rfl) ⟨67355, by rfl⟩ : syracuseStep 5747669 = 134711) (by norm_num)
theorem B2298917 : Blo 1194414 2298917 := bbase (se 4 (by rfl) ⟨215523, by rfl⟩ : syracuseStep 2298917 = 431047) (by norm_num)
theorem B3028013 : Blo 1194414 3028013 := bbase (se 3 (by rfl) ⟨567752, by rfl⟩ : syracuseStep 3028013 = 1135505) (by norm_num)
theorem B1512533 : Blo 1194414 1512533 := bbase (se 8 (by rfl) ⟨8862, by rfl⟩ : syracuseStep 1512533 = 17725) (by norm_num)
theorem B24540245 : Blo 1194414 24540245 := bbase (se 8 (by rfl) ⟨143790, by rfl⟩ : syracuseStep 24540245 = 287581) (by norm_num)
theorem B4846709 : Blo 1194414 4846709 := bbase (se 5 (by rfl) ⟨227189, by rfl⟩ : syracuseStep 4846709 = 454379) (by norm_num)
theorem B1512589 : Blo 1194414 1512589 := bbase (se 3 (by rfl) ⟨283610, by rfl⟩ : syracuseStep 1512589 = 567221) (by norm_num)
theorem B4035797 : Blo 1194414 4035797 := bbase (se 7 (by rfl) ⟨47294, by rfl⟩ : syracuseStep 4035797 = 94589) (by norm_num)
theorem B1512685 : Blo 1194414 1512685 := bbase (se 3 (by rfl) ⟨283628, by rfl⟩ : syracuseStep 1512685 = 567257) (by norm_num)
theorem B3028205 : Blo 1194414 3028205 := bbase (se 3 (by rfl) ⟨567788, by rfl⟩ : syracuseStep 3028205 = 1135577) (by norm_num)
theorem B8295797 : Blo 1194414 8295797 := bbase (se 5 (by rfl) ⟨388865, by rfl⟩ : syracuseStep 8295797 = 777731) (by norm_num)
theorem B1701253 : Blo 1194414 1701253 := bbase (se 4 (by rfl) ⟨159492, by rfl⟩ : syracuseStep 1701253 = 318985) (by norm_num)
theorem B2553221 : Blo 1194414 2553221 := bbase (se 4 (by rfl) ⟨239364, by rfl⟩ : syracuseStep 2553221 = 478729) (by norm_num)
theorem B1512857 : Blo 1194414 1512857 := bbase (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) (by norm_num)
theorem B1512913 : Blo 1194414 1512913 := bbase (se 2 (by rfl) ⟨567342, by rfl⟩ : syracuseStep 1512913 = 1134685) (by norm_num)
theorem B2659837 : Blo 1194414 2659837 := bbase (se 3 (by rfl) ⟨498719, by rfl⟩ : syracuseStep 2659837 = 997439) (by norm_num)
theorem B3831317 : Blo 1194414 3831317 := bbase (se 6 (by rfl) ⟨89796, by rfl⟩ : syracuseStep 3831317 = 179593) (by norm_num)
theorem B1513009 : Blo 1194414 1513009 := bbase (se 2 (by rfl) ⟨567378, by rfl⟩ : syracuseStep 1513009 = 1134757) (by norm_num)
theorem B5174837 : Blo 1194414 5174837 := bbase (se 5 (by rfl) ⟨242570, by rfl⟩ : syracuseStep 5174837 = 485141) (by norm_num)
theorem B3405365 : Blo 1194414 3405365 := bbase (se 5 (by rfl) ⟨159626, by rfl⟩ : syracuseStep 3405365 = 319253) (by norm_num)
theorem B1275517 : Blo 1194414 1275517 := bbase (se 3 (by rfl) ⟨239159, by rfl⟩ : syracuseStep 1275517 = 478319) (by norm_num)
theorem B4036229 : Blo 1194414 4036229 := bbase (se 4 (by rfl) ⟨378396, by rfl⟩ : syracuseStep 4036229 = 756793) (by norm_num)
theorem B1791629 : Blo 1194414 1791629 := bbase (se 3 (by rfl) ⟨335930, by rfl⟩ : syracuseStep 1791629 = 671861) (by norm_num)
theorem B1791653 : Blo 1194414 1791653 := bbase (se 4 (by rfl) ⟨167967, by rfl⟩ : syracuseStep 1791653 = 335935) (by norm_num)
theorem B6051509 : Blo 1194414 6051509 := bbase (se 5 (by rfl) ⟨283664, by rfl⟩ : syracuseStep 6051509 = 567329) (by norm_num)
theorem B1791677 : Blo 1194414 1791677 := bbase (se 3 (by rfl) ⟨335939, by rfl⟩ : syracuseStep 1791677 = 671879) (by norm_num)
theorem B1791701 : Blo 1194414 1791701 := bbase (se 7 (by rfl) ⟨20996, by rfl⟩ : syracuseStep 1791701 = 41993) (by norm_num)
theorem B1701589 : Blo 1194414 1701589 := bbase (se 7 (by rfl) ⟨19940, by rfl⟩ : syracuseStep 1701589 = 39881) (by norm_num)
theorem B1513181 : Blo 1194414 1513181 := bbase (se 3 (by rfl) ⟨283721, by rfl⟩ : syracuseStep 1513181 = 567443) (by norm_num)
theorem B1791725 : Blo 1194414 1791725 := bbase (se 3 (by rfl) ⟨335948, by rfl⟩ : syracuseStep 1791725 = 671897) (by norm_num)
theorem B1791749 : Blo 1194414 1791749 := bbase (se 4 (by rfl) ⟨167976, by rfl⟩ : syracuseStep 1791749 = 335953) (by norm_num)
theorem B1513237 : Blo 1194414 1513237 := bbase (se 6 (by rfl) ⟨35466, by rfl⟩ : syracuseStep 1513237 = 70933) (by norm_num)
theorem B1791773 : Blo 1194414 1791773 := bbase (se 3 (by rfl) ⟨335957, by rfl⟩ : syracuseStep 1791773 = 671915) (by norm_num)
theorem B1816349 : Blo 1194414 1816349 := bbase (se 3 (by rfl) ⟨340565, by rfl⟩ : syracuseStep 1816349 = 681131) (by norm_num)
theorem B1791797 : Blo 1194414 1791797 := bbase (se 5 (by rfl) ⟨83990, by rfl⟩ : syracuseStep 1791797 = 167981) (by norm_num)
theorem B1791821 : Blo 1194414 1791821 := bbase (se 3 (by rfl) ⟨335966, by rfl⟩ : syracuseStep 1791821 = 671933) (by norm_num)
theorem B1791845 : Blo 1194414 1791845 := bbase (se 4 (by rfl) ⟨167985, by rfl⟩ : syracuseStep 1791845 = 335971) (by norm_num)
theorem B1513333 : Blo 1194414 1513333 := bbase (se 5 (by rfl) ⟨70937, by rfl⟩ : syracuseStep 1513333 = 141875) (by norm_num)
theorem B1791869 : Blo 1194414 1791869 := bbase (se 3 (by rfl) ⟨335975, by rfl⟩ : syracuseStep 1791869 = 671951) (by norm_num)
theorem B1791893 : Blo 1194414 1791893 := bbase (se 6 (by rfl) ⟨41997, by rfl⟩ : syracuseStep 1791893 = 83995) (by norm_num)
theorem B6805397 : Blo 1194414 6805397 := bbase (se 6 (by rfl) ⟨159501, by rfl⟩ : syracuseStep 6805397 = 319003) (by norm_num)
theorem B1791917 : Blo 1194414 1791917 := bbase (se 3 (by rfl) ⟨335984, by rfl⟩ : syracuseStep 1791917 = 671969) (by norm_num)
theorem B1701805 : Blo 1194414 1701805 := bbase (se 3 (by rfl) ⟨319088, by rfl⟩ : syracuseStep 1701805 = 638177) (by norm_num)
theorem B1791941 : Blo 1194414 1791941 := bbase (se 4 (by rfl) ⟨167994, by rfl⟩ : syracuseStep 1791941 = 335989) (by norm_num)
theorem B1791965 : Blo 1194414 1791965 := bbase (se 3 (by rfl) ⟨335993, by rfl⟩ : syracuseStep 1791965 = 671987) (by norm_num)
theorem B3405797 : Blo 1194414 3405797 := bbase (se 4 (by rfl) ⟨319293, by rfl⟩ : syracuseStep 3405797 = 638587) (by norm_num)
theorem B1791989 : Blo 1194414 1791989 := bbase (se 5 (by rfl) ⟨83999, by rfl⟩ : syracuseStep 1791989 = 167999) (by norm_num)
theorem B2299909 : Blo 1194414 2299909 := bbase (se 4 (by rfl) ⟨215616, by rfl⟩ : syracuseStep 2299909 = 431233) (by norm_num)
theorem B1792013 : Blo 1194414 1792013 := bbase (se 3 (by rfl) ⟨336002, by rfl⟩ : syracuseStep 1792013 = 672005) (by norm_num)
theorem B1513505 : Blo 1194414 1513505 := bbase (se 2 (by rfl) ⟨567564, by rfl⟩ : syracuseStep 1513505 = 1135129) (by norm_num)
theorem B1792037 : Blo 1194414 1792037 := bbase (se 4 (by rfl) ⟨168003, by rfl⟩ : syracuseStep 1792037 = 336007) (by norm_num)
theorem B4036661 : Blo 1194414 4036661 := bbase (se 5 (by rfl) ⟨189218, by rfl⟩ : syracuseStep 4036661 = 378437) (by norm_num)
theorem B1275961 : Blo 1194414 1275961 := bbase (se 2 (by rfl) ⟨478485, by rfl⟩ : syracuseStep 1275961 = 956971) (by norm_num)
theorem B1792061 : Blo 1194414 1792061 := bbase (se 3 (by rfl) ⟨336011, by rfl⟩ : syracuseStep 1792061 = 672023) (by norm_num)
theorem B2799677 : Blo 1194414 2799677 := bbase (se 3 (by rfl) ⟨524939, by rfl⟩ : syracuseStep 2799677 = 1049879) (by norm_num)
theorem B1914941 : Blo 1194414 1914941 := bbase (se 3 (by rfl) ⟨359051, by rfl⟩ : syracuseStep 1914941 = 718103) (by norm_num)
theorem B1792085 : Blo 1194414 1792085 := bbase (se 8 (by rfl) ⟨10500, by rfl⟩ : syracuseStep 1792085 = 21001) (by norm_num)
theorem B17234005 : Blo 1194414 17234005 := bbase (se 8 (by rfl) ⟨100980, by rfl⟩ : syracuseStep 17234005 = 201961) (by norm_num)
theorem B25860181 : Blo 1194414 25860181 := bbase (se 8 (by rfl) ⟨151524, by rfl⟩ : syracuseStep 25860181 = 303049) (by norm_num)
theorem B1513561 : Blo 1194414 1513561 := bbase (se 2 (by rfl) ⟨567585, by rfl⟩ : syracuseStep 1513561 = 1135171) (by norm_num)
theorem B1792109 : Blo 1194414 1792109 := bbase (se 3 (by rfl) ⟨336020, by rfl⟩ : syracuseStep 1792109 = 672041) (by norm_num)
theorem B1276021 : Blo 1194414 1276021 := bbase (se 5 (by rfl) ⟨59813, by rfl⟩ : syracuseStep 1276021 = 119627) (by norm_num)
theorem B1792133 : Blo 1194414 1792133 := bbase (se 4 (by rfl) ⟨168012, by rfl⟩ : syracuseStep 1792133 = 336025) (by norm_num)
theorem B1792157 : Blo 1194414 1792157 := bbase (se 3 (by rfl) ⟨336029, by rfl⟩ : syracuseStep 1792157 = 672059) (by norm_num)
theorem B1792181 : Blo 1194414 1792181 := bbase (se 5 (by rfl) ⟨84008, by rfl⟩ : syracuseStep 1792181 = 168017) (by norm_num)
theorem B1513657 : Blo 1194414 1513657 := bbase (se 2 (by rfl) ⟨567621, by rfl⟩ : syracuseStep 1513657 = 1135243) (by norm_num)
theorem B1792205 : Blo 1194414 1792205 := bbase (se 3 (by rfl) ⟨336038, by rfl⟩ : syracuseStep 1792205 = 672077) (by norm_num)
theorem B1792229 : Blo 1194414 1792229 := bbase (se 4 (by rfl) ⟨168021, by rfl⟩ : syracuseStep 1792229 = 336043) (by norm_num)
theorem B1792253 : Blo 1194414 1792253 := bbase (se 3 (by rfl) ⟨336047, by rfl⟩ : syracuseStep 1792253 = 672095) (by norm_num)
theorem B2554109 : Blo 1194414 2554109 := bbase (se 3 (by rfl) ⟨478895, by rfl⟩ : syracuseStep 2554109 = 957791) (by norm_num)
theorem B1792277 : Blo 1194414 1792277 := bbase (se 6 (by rfl) ⟨42006, by rfl⟩ : syracuseStep 1792277 = 84013) (by norm_num)
theorem B24254741 : Blo 1194414 24254741 := bbase (se 6 (by rfl) ⟨568470, by rfl⟩ : syracuseStep 24254741 = 1136941) (by norm_num)
theorem B1702181 : Blo 1194414 1702181 := bbase (se 4 (by rfl) ⟨159579, by rfl⟩ : syracuseStep 1702181 = 319159) (by norm_num)
theorem B1792301 : Blo 1194414 1792301 := bbase (se 3 (by rfl) ⟨336056, by rfl⟩ : syracuseStep 1792301 = 672113) (by norm_num)
theorem B1792325 : Blo 1194414 1792325 := bbase (se 4 (by rfl) ⟨168030, by rfl⟩ : syracuseStep 1792325 = 336061) (by norm_num)
theorem B1792349 : Blo 1194414 1792349 := bbase (se 3 (by rfl) ⟨336065, by rfl⟩ : syracuseStep 1792349 = 672131) (by norm_num)
theorem B1513829 : Blo 1194414 1513829 := bbase (se 4 (by rfl) ⟨141921, by rfl⟩ : syracuseStep 1513829 = 283843) (by norm_num)
theorem B1792373 : Blo 1194414 1792373 := bbase (se 5 (by rfl) ⟨84017, by rfl⟩ : syracuseStep 1792373 = 168035) (by norm_num)
theorem B2554229 : Blo 1194414 2554229 := bbase (se 5 (by rfl) ⟨119729, by rfl⟩ : syracuseStep 2554229 = 239459) (by norm_num)
theorem B1792397 : Blo 1194414 1792397 := bbase (se 3 (by rfl) ⟨336074, by rfl⟩ : syracuseStep 1792397 = 672149) (by norm_num)
theorem B1210777 : Blo 1194414 1210777 := bbase (se 2 (by rfl) ⟨454041, by rfl⟩ : syracuseStep 1210777 = 908083) (by norm_num)
theorem B1513885 : Blo 1194414 1513885 := bbase (se 3 (by rfl) ⟨283853, by rfl⟩ : syracuseStep 1513885 = 567707) (by norm_num)
theorem B1792421 : Blo 1194414 1792421 := bbase (se 4 (by rfl) ⟨168039, by rfl⟩ : syracuseStep 1792421 = 336079) (by norm_num)
theorem B1276337 : Blo 1194414 1276337 := bbase (se 2 (by rfl) ⟨478626, by rfl⟩ : syracuseStep 1276337 = 957253) (by norm_num)
theorem B1792445 : Blo 1194414 1792445 := bbase (se 3 (by rfl) ⟨336083, by rfl⟩ : syracuseStep 1792445 = 672167) (by norm_num)
theorem B1792469 : Blo 1194414 1792469 := bbase (se 7 (by rfl) ⟨21005, by rfl⟩ : syracuseStep 1792469 = 42011) (by norm_num)
theorem B4037093 : Blo 1194414 4037093 := bbase (se 4 (by rfl) ⟨378477, by rfl⟩ : syracuseStep 4037093 = 756955) (by norm_num)
theorem B1792493 : Blo 1194414 1792493 := bbase (se 3 (by rfl) ⟨336092, by rfl⟩ : syracuseStep 1792493 = 672185) (by norm_num)
theorem B1792517 : Blo 1194414 1792517 := bbase (se 4 (by rfl) ⟨168048, by rfl⟩ : syracuseStep 1792517 = 336097) (by norm_num)
theorem B1915397 : Blo 1194414 1915397 := bbase (se 4 (by rfl) ⟨179568, by rfl⟩ : syracuseStep 1915397 = 359137) (by norm_num)
theorem B2267669 : Blo 1194414 2267669 := bbase (se 6 (by rfl) ⟨53148, by rfl⟩ : syracuseStep 2267669 = 106297) (by norm_num)
theorem B1792541 : Blo 1194414 1792541 := bbase (se 3 (by rfl) ⟨336101, by rfl⟩ : syracuseStep 1792541 = 672203) (by norm_num)
theorem B2873893 : Blo 1194414 2873893 := bbase (se 4 (by rfl) ⟨269427, by rfl⟩ : syracuseStep 2873893 = 538855) (by norm_num)
theorem B1792565 : Blo 1194414 1792565 := bbase (se 5 (by rfl) ⟨84026, by rfl⟩ : syracuseStep 1792565 = 168053) (by norm_num)
theorem B1792589 : Blo 1194414 1792589 := bbase (se 3 (by rfl) ⟨336110, by rfl⟩ : syracuseStep 1792589 = 672221) (by norm_num)
theorem B4536917 : Blo 1194414 4536917 := bbase (se 8 (by rfl) ⟨26583, by rfl⟩ : syracuseStep 4536917 = 53167) (by norm_num)
theorem B1792613 : Blo 1194414 1792613 := bbase (se 4 (by rfl) ⟨168057, by rfl⟩ : syracuseStep 1792613 = 336115) (by norm_num)
theorem B1792637 : Blo 1194414 1792637 := bbase (se 3 (by rfl) ⟨336119, by rfl⟩ : syracuseStep 1792637 = 672239) (by norm_num)
theorem B1792661 : Blo 1194414 1792661 := bbase (se 6 (by rfl) ⟨42015, by rfl⟩ : syracuseStep 1792661 = 84031) (by norm_num)
theorem B2267813 : Blo 1194414 2267813 := bbase (se 4 (by rfl) ⟨212607, by rfl⟩ : syracuseStep 2267813 = 425215) (by norm_num)
theorem B1514153 : Blo 1194414 1514153 := bbase (se 2 (by rfl) ⟨567807, by rfl⟩ : syracuseStep 1514153 = 1135615) (by norm_num)
theorem B1792685 : Blo 1194414 1792685 := bbase (se 3 (by rfl) ⟨336128, by rfl⟩ : syracuseStep 1792685 = 672257) (by norm_num)
theorem B1513981 : Blo 1194414 1513981 := bbase (se 3 (by rfl) ⟨283871, by rfl⟩ : syracuseStep 1513981 = 567743) (by norm_num)
theorem B1792709 : Blo 1194414 1792709 := bbase (se 4 (by rfl) ⟨168066, by rfl⟩ : syracuseStep 1792709 = 336133) (by norm_num)
theorem B10205909 : Blo 1194414 10205909 := bbase (se 7 (by rfl) ⟨119600, by rfl⟩ : syracuseStep 10205909 = 239201) (by norm_num)
theorem B3406549 : Blo 1194414 3406549 := bbase (se 7 (by rfl) ⟨39920, by rfl⟩ : syracuseStep 3406549 = 79841) (by norm_num)
theorem B1792733 : Blo 1194414 1792733 := bbase (se 3 (by rfl) ⟨336137, by rfl⟩ : syracuseStep 1792733 = 672275) (by norm_num)
theorem B1514209 : Blo 1194414 1514209 := bbase (se 2 (by rfl) ⟨567828, by rfl⟩ : syracuseStep 1514209 = 1135657) (by norm_num)
theorem B5741285 : Blo 1194414 5741285 := bbase (se 4 (by rfl) ⟨538245, by rfl⟩ : syracuseStep 5741285 = 1076491) (by norm_num)
theorem B1792757 : Blo 1194414 1792757 := bbase (se 5 (by rfl) ⟨84035, by rfl⟩ : syracuseStep 1792757 = 168071) (by norm_num)
theorem B1792781 : Blo 1194414 1792781 := bbase (se 3 (by rfl) ⟨336146, by rfl⟩ : syracuseStep 1792781 = 672293) (by norm_num)
theorem B1792805 : Blo 1194414 1792805 := bbase (se 4 (by rfl) ⟨168075, by rfl⟩ : syracuseStep 1792805 = 336151) (by norm_num)
theorem B1940285 : Blo 1194414 1940285 := bbase (se 3 (by rfl) ⟨363803, by rfl⟩ : syracuseStep 1940285 = 727607) (by norm_num)
theorem B1792829 : Blo 1194414 1792829 := bbase (se 3 (by rfl) ⟨336155, by rfl⟩ : syracuseStep 1792829 = 672311) (by norm_num)
theorem B1792853 : Blo 1194414 1792853 := bbase (se 9 (by rfl) ⟨5252, by rfl⟩ : syracuseStep 1792853 = 10505) (by norm_num)
theorem B1792877 : Blo 1194414 1792877 := bbase (se 3 (by rfl) ⟨336164, by rfl⟩ : syracuseStep 1792877 = 672329) (by norm_num)
theorem B1276781 : Blo 1194414 1276781 := bbase (se 3 (by rfl) ⟨239396, by rfl⟩ : syracuseStep 1276781 = 478793) (by norm_num)
theorem B6896501 : Blo 1194414 6896501 := bbase (se 5 (by rfl) ⟨323273, by rfl⟩ : syracuseStep 6896501 = 646547) (by norm_num)
theorem B4537205 : Blo 1194414 4537205 := bbase (se 5 (by rfl) ⟨212681, by rfl⟩ : syracuseStep 4537205 = 425363) (by norm_num)
theorem B1792901 : Blo 1194414 1792901 := bbase (se 4 (by rfl) ⟨168084, by rfl⟩ : syracuseStep 1792901 = 336169) (by norm_num)
theorem B4037525 : Blo 1194414 4037525 := bbase (se 6 (by rfl) ⟨94629, by rfl⟩ : syracuseStep 4037525 = 189259) (by norm_num)
theorem B1792925 : Blo 1194414 1792925 := bbase (se 3 (by rfl) ⟨336173, by rfl⟩ : syracuseStep 1792925 = 672347) (by norm_num)
theorem B1276841 : Blo 1194414 1276841 := bbase (se 2 (by rfl) ⟨478815, by rfl⟩ : syracuseStep 1276841 = 957631) (by norm_num)
theorem B1792949 : Blo 1194414 1792949 := bbase (se 5 (by rfl) ⟨84044, by rfl⟩ : syracuseStep 1792949 = 168089) (by norm_num)
theorem B2268101 : Blo 1194414 2268101 := bbase (se 4 (by rfl) ⟨212634, by rfl⟩ : syracuseStep 2268101 = 425269) (by norm_num)
theorem B6052805 : Blo 1194414 6052805 := bbase (se 4 (by rfl) ⟨567450, by rfl⟩ : syracuseStep 6052805 = 1134901) (by norm_num)
theorem B1792973 : Blo 1194414 1792973 := bbase (se 3 (by rfl) ⟨336182, by rfl⟩ : syracuseStep 1792973 = 672365) (by norm_num)
theorem B1792997 : Blo 1194414 1792997 := bbase (se 4 (by rfl) ⟨168093, by rfl⟩ : syracuseStep 1792997 = 336187) (by norm_num)
theorem B2554861 : Blo 1194414 2554861 := bbase (se 3 (by rfl) ⟨479036, by rfl⟩ : syracuseStep 2554861 = 958073) (by norm_num)
theorem B1793021 : Blo 1194414 1793021 := bbase (se 3 (by rfl) ⟨336191, by rfl⟩ : syracuseStep 1793021 = 672383) (by norm_num)
theorem B1793045 : Blo 1194414 1793045 := bbase (se 6 (by rfl) ⟨42024, by rfl⟩ : syracuseStep 1793045 = 84049) (by norm_num)
theorem B1276969 : Blo 1194414 1276969 := bbase (se 2 (by rfl) ⟨478863, by rfl⟩ : syracuseStep 1276969 = 957727) (by norm_num)
theorem B1793069 : Blo 1194414 1793069 := bbase (se 3 (by rfl) ⟨336200, by rfl⟩ : syracuseStep 1793069 = 672401) (by norm_num)
theorem B1793093 : Blo 1194414 1793093 := bbase (se 4 (by rfl) ⟨168102, by rfl⟩ : syracuseStep 1793093 = 336205) (by norm_num)
theorem B2268253 : Blo 1194414 2268253 := bbase (se 3 (by rfl) ⟨425297, by rfl⟩ : syracuseStep 2268253 = 850595) (by norm_num)
theorem B1793117 : Blo 1194414 1793117 := bbase (se 3 (by rfl) ⟨336209, by rfl⟩ : syracuseStep 1793117 = 672419) (by norm_num)
theorem B1793141 : Blo 1194414 1793141 := bbase (se 5 (by rfl) ⟨84053, by rfl⟩ : syracuseStep 1793141 = 168107) (by norm_num)
theorem B1793165 : Blo 1194414 1793165 := bbase (se 3 (by rfl) ⟨336218, by rfl⟩ : syracuseStep 1793165 = 672437) (by norm_num)
theorem B1793189 : Blo 1194414 1793189 := bbase (se 4 (by rfl) ⟨168111, by rfl⟩ : syracuseStep 1793189 = 336223) (by norm_num)
theorem B1793213 : Blo 1194414 1793213 := bbase (se 3 (by rfl) ⟨336227, by rfl⟩ : syracuseStep 1793213 = 672455) (by norm_num)
theorem B2301133 : Blo 1194414 2301133 := bbase (se 3 (by rfl) ⟨431462, by rfl⟩ : syracuseStep 2301133 = 862925) (by norm_num)
theorem B1793237 : Blo 1194414 1793237 := bbase (se 7 (by rfl) ⟨21014, by rfl⟩ : syracuseStep 1793237 = 42029) (by norm_num)
theorem B1940701 : Blo 1194414 1940701 := bbase (se 3 (by rfl) ⟨363881, by rfl⟩ : syracuseStep 1940701 = 727763) (by norm_num)
theorem B1793261 : Blo 1194414 1793261 := bbase (se 3 (by rfl) ⟨336236, by rfl⟩ : syracuseStep 1793261 = 672473) (by norm_num)
theorem B1793285 : Blo 1194414 1793285 := bbase (se 4 (by rfl) ⟨168120, by rfl⟩ : syracuseStep 1793285 = 336241) (by norm_num)
theorem B1793309 : Blo 1194414 1793309 := bbase (se 3 (by rfl) ⟨336245, by rfl⟩ : syracuseStep 1793309 = 672491) (by norm_num)
theorem B5242165 : Blo 1194414 5242165 := bbase (se 5 (by rfl) ⟨245726, by rfl⟩ : syracuseStep 5242165 = 491453) (by norm_num)
theorem B1793333 : Blo 1194414 1793333 := bbase (se 5 (by rfl) ⟨84062, by rfl⟩ : syracuseStep 1793333 = 168125) (by norm_num)
theorem B1793357 : Blo 1194414 1793357 := bbase (se 3 (by rfl) ⟨336254, by rfl⟩ : syracuseStep 1793357 = 672509) (by norm_num)
theorem B1793381 : Blo 1194414 1793381 := bbase (se 4 (by rfl) ⟨168129, by rfl⟩ : syracuseStep 1793381 = 336259) (by norm_num)
theorem B1793405 : Blo 1194414 1793405 := bbase (se 3 (by rfl) ⟨336263, by rfl⟩ : syracuseStep 1793405 = 672527) (by norm_num)
theorem B1228169 : Blo 1194414 1228169 := bbase (se 2 (by rfl) ⟨460563, by rfl⟩ : syracuseStep 1228169 = 921127) (by norm_num)
theorem B2268557 : Blo 1194414 2268557 := bbase (se 3 (by rfl) ⟨425354, by rfl⟩ : syracuseStep 2268557 = 850709) (by norm_num)
theorem B1793429 : Blo 1194414 1793429 := bbase (se 6 (by rfl) ⟨42033, by rfl⟩ : syracuseStep 1793429 = 84067) (by norm_num)
theorem B10911125 : Blo 1194414 10911125 := bbase (se 6 (by rfl) ⟨255729, by rfl⟩ : syracuseStep 10911125 = 511459) (by norm_num)
theorem B1793453 : Blo 1194414 1793453 := bbase (se 3 (by rfl) ⟨336272, by rfl⟩ : syracuseStep 1793453 = 672545) (by norm_num)
theorem B1793477 : Blo 1194414 1793477 := bbase (se 4 (by rfl) ⟨168138, by rfl⟩ : syracuseStep 1793477 = 336277) (by norm_num)
theorem B1793501 : Blo 1194414 1793501 := bbase (se 3 (by rfl) ⟨336281, by rfl⟩ : syracuseStep 1793501 = 672563) (by norm_num)
theorem B1277413 : Blo 1194414 1277413 := bbase (se 4 (by rfl) ⟨119757, by rfl⟩ : syracuseStep 1277413 = 239515) (by norm_num)
theorem B1916389 : Blo 1194414 1916389 := bbase (se 4 (by rfl) ⟨179661, by rfl⟩ : syracuseStep 1916389 = 359323) (by norm_num)
theorem B1793525 : Blo 1194414 1793525 := bbase (se 5 (by rfl) ⟨84071, by rfl⟩ : syracuseStep 1793525 = 168143) (by norm_num)
theorem B4849141 : Blo 1194414 4849141 := bbase (se 5 (by rfl) ⟨227303, by rfl⟩ : syracuseStep 4849141 = 454607) (by norm_num)
theorem B1793549 : Blo 1194414 1793549 := bbase (se 3 (by rfl) ⟨336290, by rfl⟩ : syracuseStep 1793549 = 672581) (by norm_num)
theorem B20708885 : Blo 1194414 20708885 := bbase (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) (by norm_num)
theorem B1793573 : Blo 1194414 1793573 := bbase (se 4 (by rfl) ⟨168147, by rfl⟩ : syracuseStep 1793573 = 336295) (by norm_num)
theorem B1793597 : Blo 1194414 1793597 := bbase (se 3 (by rfl) ⟨336299, by rfl⟩ : syracuseStep 1793597 = 672599) (by norm_num)
theorem B1793621 : Blo 1194414 1793621 := bbase (se 8 (by rfl) ⟨10509, by rfl⟩ : syracuseStep 1793621 = 21019) (by norm_num)
theorem B1277533 : Blo 1194414 1277533 := bbase (se 3 (by rfl) ⟨239537, by rfl⟩ : syracuseStep 1277533 = 479075) (by norm_num)
theorem B1793645 : Blo 1194414 1793645 := bbase (se 3 (by rfl) ⟨336308, by rfl⟩ : syracuseStep 1793645 = 672617) (by norm_num)
theorem B1793669 : Blo 1194414 1793669 := bbase (se 4 (by rfl) ⟨168156, by rfl⟩ : syracuseStep 1793669 = 336313) (by norm_num)
theorem B1793693 : Blo 1194414 1793693 := bbase (se 3 (by rfl) ⟨336317, by rfl⟩ : syracuseStep 1793693 = 672635) (by norm_num)
theorem B1793717 : Blo 1194414 1793717 := bbase (se 5 (by rfl) ⟨84080, by rfl⟩ : syracuseStep 1793717 = 168161) (by norm_num)
theorem B1793741 : Blo 1194414 1793741 := bbase (se 3 (by rfl) ⟨336326, by rfl⟩ : syracuseStep 1793741 = 672653) (by norm_num)
theorem B1793765 : Blo 1194414 1793765 := bbase (se 4 (by rfl) ⟨168165, by rfl⟩ : syracuseStep 1793765 = 336331) (by norm_num)
theorem B9699061 : Blo 1194414 9699061 := bbase (se 5 (by rfl) ⟨454643, by rfl⟩ : syracuseStep 9699061 = 909287) (by norm_num)
theorem B1793789 : Blo 1194414 1793789 := bbase (se 3 (by rfl) ⟨336335, by rfl⟩ : syracuseStep 1793789 = 672671) (by norm_num)
theorem B6463253 : Blo 1194414 6463253 := bbase (se 6 (by rfl) ⟨151482, by rfl⟩ : syracuseStep 6463253 = 302965) (by norm_num)
theorem B1793813 : Blo 1194414 1793813 := bbase (se 6 (by rfl) ⟨42042, by rfl⟩ : syracuseStep 1793813 = 84085) (by norm_num)
theorem B1212185 : Blo 1194414 1212185 := bbase (se 2 (by rfl) ⟨454569, by rfl⟩ : syracuseStep 1212185 = 909139) (by norm_num)
theorem B1793837 : Blo 1194414 1793837 := bbase (se 3 (by rfl) ⟨336344, by rfl⟩ : syracuseStep 1793837 = 672689) (by norm_num)
theorem B7757621 : Blo 1194414 7757621 := bbase (se 5 (by rfl) ⟨363638, by rfl⟩ : syracuseStep 7757621 = 727277) (by norm_num)
theorem B1228613 : Blo 1194414 1228613 := bbase (se 4 (by rfl) ⟨115182, by rfl⟩ : syracuseStep 1228613 = 230365) (by norm_num)
theorem B1793861 : Blo 1194414 1793861 := bbase (se 4 (by rfl) ⟨168174, by rfl⟩ : syracuseStep 1793861 = 336349) (by norm_num)
theorem B1793885 : Blo 1194414 1793885 := bbase (se 3 (by rfl) ⟨336353, by rfl⟩ : syracuseStep 1793885 = 672707) (by norm_num)
theorem B1793909 : Blo 1194414 1793909 := bbase (se 5 (by rfl) ⟨84089, by rfl⟩ : syracuseStep 1793909 = 168179) (by norm_num)
theorem B1793933 : Blo 1194414 1793933 := bbase (se 3 (by rfl) ⟨336362, by rfl⟩ : syracuseStep 1793933 = 672725) (by norm_num)
theorem B1793957 : Blo 1194414 1793957 := bbase (se 4 (by rfl) ⟨168183, by rfl⟩ : syracuseStep 1793957 = 336367) (by norm_num)
theorem B3448757 : Blo 1194414 3448757 := bbase (se 5 (by rfl) ⟨161660, by rfl⟩ : syracuseStep 3448757 = 323321) (by norm_num)
theorem B1793981 : Blo 1194414 1793981 := bbase (se 3 (by rfl) ⟨336371, by rfl⟩ : syracuseStep 1793981 = 672743) (by norm_num)
theorem B1794005 : Blo 1194414 1794005 := bbase (se 7 (by rfl) ⟨21023, by rfl⟩ : syracuseStep 1794005 = 42047) (by norm_num)
theorem B1794029 : Blo 1194414 1794029 := bbase (se 3 (by rfl) ⟨336380, by rfl⟩ : syracuseStep 1794029 = 672761) (by norm_num)
theorem B1196035 : Blo 1194414 1196035 := bstep (se 1 (by rfl) ⟨897026, by rfl⟩ : syracuseStep 1196035 = 1794053) B1794053
theorem B1794065 : Blo 1194414 1794065 := bstep (se 2 (by rfl) ⟨672774, by rfl⟩ : syracuseStep 1794065 = 1345549) B1345549
theorem B1196051 : Blo 1194414 1196051 := bstep (se 1 (by rfl) ⟨897038, by rfl⟩ : syracuseStep 1196051 = 1794077) B1794077
theorem B1794083 : Blo 1194414 1794083 := bstep (se 1 (by rfl) ⟨1345562, by rfl⟩ : syracuseStep 1794083 = 2691125) B2691125
theorem B1196067 : Blo 1194414 1196067 := bstep (se 1 (by rfl) ⟨897050, by rfl⟩ : syracuseStep 1196067 = 1794101) B1794101
theorem B1196083 : Blo 1194414 1196083 := bstep (se 1 (by rfl) ⟨897062, by rfl⟩ : syracuseStep 1196083 = 1794125) B1794125
theorem B1794113 : Blo 1194414 1794113 := bstep (se 2 (by rfl) ⟨672792, by rfl⟩ : syracuseStep 1794113 = 1345585) B1345585
theorem B1196099 : Blo 1194414 1196099 := bstep (se 1 (by rfl) ⟨897074, by rfl⟩ : syracuseStep 1196099 = 1794149) B1794149
theorem B1400915 : Blo 1194414 1400915 := bstep (se 1 (by rfl) ⟨1050686, by rfl⟩ : syracuseStep 1400915 = 2101373) B2101373
theorem B1794131 : Blo 1194414 1794131 := bstep (se 1 (by rfl) ⟨1345598, by rfl⟩ : syracuseStep 1794131 = 2691197) B2691197
theorem B1196115 : Blo 1194414 1196115 := bstep (se 1 (by rfl) ⟨897086, by rfl⟩ : syracuseStep 1196115 = 1794173) B1794173
theorem B1196131 : Blo 1194414 1196131 := bstep (se 1 (by rfl) ⟨897098, by rfl⟩ : syracuseStep 1196131 = 1794197) B1794197
theorem B22978673 : Blo 1194414 22978673 := bstep (se 2 (by rfl) ⟨8617002, by rfl⟩ : syracuseStep 22978673 = 17234005) B17234005
theorem B34480241 : Blo 1194414 34480241 := bstep (se 2 (by rfl) ⟨12930090, by rfl⟩ : syracuseStep 34480241 = 25860181) B25860181
theorem B1794161 : Blo 1194414 1794161 := bstep (se 2 (by rfl) ⟨672810, by rfl⟩ : syracuseStep 1794161 = 1345621) B1345621
theorem B1196147 : Blo 1194414 1196147 := bstep (se 1 (by rfl) ⟨897110, by rfl⟩ : syracuseStep 1196147 = 1794221) B1794221
theorem B1794179 : Blo 1194414 1794179 := bstep (se 1 (by rfl) ⟨1345634, by rfl⟩ : syracuseStep 1794179 = 2691269) B2691269
theorem B1196163 : Blo 1194414 1196163 := bstep (se 1 (by rfl) ⟨897122, by rfl⟩ : syracuseStep 1196163 = 1794245) B1794245
theorem B1818769 : Blo 1194414 1818769 := bstep (se 2 (by rfl) ⟨682038, by rfl⟩ : syracuseStep 1818769 = 1364077) B1364077
theorem B1196179 : Blo 1194414 1196179 := bstep (se 1 (by rfl) ⟨897134, by rfl⟩ : syracuseStep 1196179 = 1794269) B1794269
theorem B1794209 : Blo 1194414 1794209 := bstep (se 2 (by rfl) ⟨672828, by rfl⟩ : syracuseStep 1794209 = 1345657) B1345657
theorem B1196195 : Blo 1194414 1196195 := bstep (se 1 (by rfl) ⟨897146, by rfl⟩ : syracuseStep 1196195 = 1794293) B1794293
theorem B1794227 : Blo 1194414 1794227 := bstep (se 1 (by rfl) ⟨1345670, by rfl⟩ : syracuseStep 1794227 = 2691341) B2691341
theorem B1196211 : Blo 1194414 1196211 := bstep (se 1 (by rfl) ⟨897158, by rfl⟩ : syracuseStep 1196211 = 1794317) B1794317
theorem B1196227 : Blo 1194414 1196227 := bstep (se 1 (by rfl) ⟨897170, by rfl⟩ : syracuseStep 1196227 = 1794341) B1794341
theorem B1794257 : Blo 1194414 1794257 := bstep (se 2 (by rfl) ⟨672846, by rfl⟩ : syracuseStep 1794257 = 1345693) B1345693
theorem B1196243 : Blo 1194414 1196243 := bstep (se 1 (by rfl) ⟨897182, by rfl⟩ : syracuseStep 1196243 = 1794365) B1794365
theorem B1794275 : Blo 1194414 1794275 := bstep (se 1 (by rfl) ⟨1345706, by rfl⟩ : syracuseStep 1794275 = 2691413) B2691413
theorem B23306467 : Blo 1194414 23306467 := bstep (se 1 (by rfl) ⟨17479850, by rfl⟩ : syracuseStep 23306467 = 34959701) B34959701
theorem B1196259 : Blo 1194414 1196259 := bstep (se 1 (by rfl) ⟨897194, by rfl⟩ : syracuseStep 1196259 = 1794389) B1794389
theorem B1343731 : Blo 1194414 1343731 := bstep (se 1 (by rfl) ⟨1007798, by rfl⟩ : syracuseStep 1343731 = 2015597) B2015597
theorem B1196275 : Blo 1194414 1196275 := bstep (se 1 (by rfl) ⟨897206, by rfl⟩ : syracuseStep 1196275 = 1794413) B1794413
theorem B1794305 : Blo 1194414 1794305 := bstep (se 2 (by rfl) ⟨672864, by rfl⟩ : syracuseStep 1794305 = 1345729) B1345729
theorem B1196291 : Blo 1194414 1196291 := bstep (se 1 (by rfl) ⟨897218, by rfl⟩ : syracuseStep 1196291 = 1794437) B1794437
theorem B1794323 : Blo 1194414 1794323 := bstep (se 1 (by rfl) ⟨1345742, by rfl⟩ : syracuseStep 1794323 = 2691485) B2691485
theorem B1196307 : Blo 1194414 1196307 := bstep (se 1 (by rfl) ⟨897230, by rfl⟩ : syracuseStep 1196307 = 1794461) B1794461
theorem B1196323 : Blo 1194414 1196323 := bstep (se 1 (by rfl) ⟨897242, by rfl⟩ : syracuseStep 1196323 = 1794485) B1794485
theorem B1794353 : Blo 1194414 1794353 := bstep (se 2 (by rfl) ⟨672882, by rfl⟩ : syracuseStep 1794353 = 1345765) B1345765
theorem B1196339 : Blo 1194414 1196339 := bstep (se 1 (by rfl) ⟨897254, by rfl⟩ : syracuseStep 1196339 = 1794509) B1794509
theorem B1794371 : Blo 1194414 1794371 := bstep (se 1 (by rfl) ⟨1345778, by rfl⟩ : syracuseStep 1794371 = 2691557) B2691557
theorem B1196355 : Blo 1194414 1196355 := bstep (se 1 (by rfl) ⟨897266, by rfl⟩ : syracuseStep 1196355 = 1794533) B1794533
theorem B1196371 : Blo 1194414 1196371 := bstep (se 1 (by rfl) ⟨897278, by rfl⟩ : syracuseStep 1196371 = 1794557) B1794557
theorem B1794401 : Blo 1194414 1794401 := bstep (se 2 (by rfl) ⟨672900, by rfl⟩ : syracuseStep 1794401 = 1345801) B1345801
theorem B2425187 : Blo 1194414 2425187 := bstep (se 1 (by rfl) ⟨1818890, by rfl⟩ : syracuseStep 2425187 = 3637781) B3637781
theorem B1196387 : Blo 1194414 1196387 := bstep (se 1 (by rfl) ⟨897290, by rfl⟩ : syracuseStep 1196387 = 1794581) B1794581
theorem B1794419 : Blo 1194414 1794419 := bstep (se 1 (by rfl) ⟨1345814, by rfl⟩ : syracuseStep 1794419 = 2691629) B2691629
theorem B1196403 : Blo 1194414 1196403 := bstep (se 1 (by rfl) ⟨897302, by rfl⟩ : syracuseStep 1196403 = 1794605) B1794605
theorem B2015617 : Blo 1194414 2015617 := bstep (se 2 (by rfl) ⟨755856, by rfl⟩ : syracuseStep 2015617 = 1511713) B1511713
theorem B1343875 : Blo 1194414 1343875 := bstep (se 1 (by rfl) ⟨1007906, by rfl⟩ : syracuseStep 1343875 = 2015813) B2015813
theorem B1794449 : Blo 1194414 1794449 := bstep (se 2 (by rfl) ⟨672918, by rfl⟩ : syracuseStep 1794449 = 1345837) B1345837
theorem B1819025 : Blo 1194414 1819025 := bstep (se 2 (by rfl) ⟨682134, by rfl⟩ : syracuseStep 1819025 = 1364269) B1364269
theorem B2015651 : Blo 1194414 2015651 := bstep (se 1 (by rfl) ⟨1511738, by rfl⟩ : syracuseStep 2015651 = 3023477) B3023477
theorem B1794467 : Blo 1194414 1794467 := bstep (se 1 (by rfl) ⟨1345850, by rfl⟩ : syracuseStep 1794467 = 2691701) B2691701
theorem B1794497 : Blo 1194414 1794497 := bstep (se 2 (by rfl) ⟨672936, by rfl⟩ : syracuseStep 1794497 = 1345873) B1345873
theorem B1794515 : Blo 1194414 1794515 := bstep (se 1 (by rfl) ⟨1345886, by rfl⟩ : syracuseStep 1794515 = 2691773) B2691773
theorem B1794545 : Blo 1194414 1794545 := bstep (se 2 (by rfl) ⟨672954, by rfl⟩ : syracuseStep 1794545 = 1345909) B1345909
theorem B1794563 : Blo 1194414 1794563 := bstep (se 1 (by rfl) ⟨1345922, by rfl⟩ : syracuseStep 1794563 = 2691845) B2691845
theorem B1344019 : Blo 1194414 1344019 := bstep (se 1 (by rfl) ⟨1008014, by rfl⟩ : syracuseStep 1344019 = 2016029) B2016029
theorem B1794593 : Blo 1194414 1794593 := bstep (se 2 (by rfl) ⟨672972, by rfl⟩ : syracuseStep 1794593 = 1345945) B1345945
theorem B2015779 : Blo 1194414 2015779 := bstep (se 1 (by rfl) ⟨1511834, by rfl⟩ : syracuseStep 2015779 = 3023669) B3023669
theorem B1794611 : Blo 1194414 1794611 := bstep (se 1 (by rfl) ⟨1345958, by rfl⟩ : syracuseStep 1794611 = 2691917) B2691917
theorem B15311429 : Blo 1194414 15311429 := bstep (se 4 (by rfl) ⟨1435446, by rfl⟩ : syracuseStep 15311429 = 2870893) B2870893
theorem B2269795 : Blo 1194414 2269795 := bstep (se 1 (by rfl) ⟨1702346, by rfl⟩ : syracuseStep 2269795 = 3404693) B3404693
theorem B2687633 : Blo 1194414 2687633 := bstep (se 2 (by rfl) ⟨1007862, by rfl⟩ : syracuseStep 2687633 = 2015725) B2015725
theorem B2687651 : Blo 1194414 2687651 := bstep (se 1 (by rfl) ⟨2015738, by rfl⟩ : syracuseStep 2687651 = 4031477) B4031477
theorem B1344163 : Blo 1194414 1344163 := bstep (se 1 (by rfl) ⟨1008122, by rfl⟩ : syracuseStep 1344163 = 2016245) B2016245
theorem B4031153 : Blo 1194414 4031153 := bstep (se 2 (by rfl) ⟨1511682, by rfl⟩ : syracuseStep 4031153 = 3023365) B3023365
theorem B2015921 : Blo 1194414 2015921 := bstep (se 2 (by rfl) ⟨755970, by rfl⟩ : syracuseStep 2015921 = 1511941) B1511941
theorem B1532611 : Blo 1194414 1532611 := bstep (se 1 (by rfl) ⟨1149458, by rfl⟩ : syracuseStep 1532611 = 2298917) B2298917
theorem B16360163 : Blo 1194414 16360163 := bstep (se 1 (by rfl) ⟨12270122, by rfl⟩ : syracuseStep 16360163 = 24540245) B24540245
theorem B4539149 : Blo 1194414 4539149 := bstep (se 3 (by rfl) ⟨851090, by rfl⟩ : syracuseStep 4539149 = 1702181) B1702181
theorem B2016049 : Blo 1194414 2016049 := bstep (se 2 (by rfl) ⟨756018, by rfl⟩ : syracuseStep 2016049 = 1512037) B1512037
theorem B1344307 : Blo 1194414 1344307 := bstep (se 1 (by rfl) ⟨1008230, by rfl⟩ : syracuseStep 1344307 = 2016461) B2016461
theorem B9700165 : Blo 1194414 9700165 := bstep (se 4 (by rfl) ⟨909390, by rfl⟩ : syracuseStep 9700165 = 1818781) B1818781
theorem B2016083 : Blo 1194414 2016083 := bstep (se 1 (by rfl) ⟨1512062, by rfl⟩ : syracuseStep 2016083 = 3024125) B3024125
theorem B5530531 : Blo 1194414 5530531 := bstep (se 1 (by rfl) ⟨4147898, by rfl⟩ : syracuseStep 5530531 = 8295797) B8295797
theorem B2687921 : Blo 1194414 2687921 := bstep (se 2 (by rfl) ⟨1007970, by rfl⟩ : syracuseStep 2687921 = 2015941) B2015941
theorem B2687939 : Blo 1194414 2687939 := bstep (se 1 (by rfl) ⟨2015954, by rfl⟩ : syracuseStep 2687939 = 4031909) B4031909
theorem B1344451 : Blo 1194414 1344451 := bstep (se 1 (by rfl) ⟨1008338, by rfl⟩ : syracuseStep 1344451 = 2016677) B2016677
theorem B2016211 : Blo 1194414 2016211 := bstep (se 1 (by rfl) ⟨1512158, by rfl⟩ : syracuseStep 2016211 = 3024317) B3024317
theorem B3449891 : Blo 1194414 3449891 := bstep (se 1 (by rfl) ⟨2587418, by rfl⟩ : syracuseStep 3449891 = 5174837) B5174837
theorem B2270243 : Blo 1194414 2270243 := bstep (se 1 (by rfl) ⟨1702682, by rfl⟩ : syracuseStep 2270243 = 3405365) B3405365
theorem B1344595 : Blo 1194414 1344595 := bstep (se 1 (by rfl) ⟨1008446, by rfl⟩ : syracuseStep 1344595 = 2016893) B2016893
theorem B2016353 : Blo 1194414 2016353 := bstep (se 2 (by rfl) ⟨756132, by rfl⟩ : syracuseStep 2016353 = 1512265) B1512265
theorem B10208369 : Blo 1194414 10208369 := bstep (se 2 (by rfl) ⟨3828138, by rfl⟩ : syracuseStep 10208369 = 7656277) B7656277
theorem B4031693 : Blo 1194414 4031693 := bstep (se 3 (by rfl) ⟨755942, by rfl⟩ : syracuseStep 4031693 = 1511885) B1511885
theorem B2688209 : Blo 1194414 2688209 := bstep (se 2 (by rfl) ⟨1008078, by rfl⟩ : syracuseStep 2688209 = 2016157) B2016157
theorem B2016481 : Blo 1194414 2016481 := bstep (se 2 (by rfl) ⟨756180, by rfl⟩ : syracuseStep 2016481 = 1512361) B1512361
theorem B2688227 : Blo 1194414 2688227 := bstep (se 1 (by rfl) ⟨2016170, by rfl⟩ : syracuseStep 2688227 = 4032341) B4032341
theorem B1344739 : Blo 1194414 1344739 := bstep (se 1 (by rfl) ⟨1008554, by rfl⟩ : syracuseStep 1344739 = 2017109) B2017109
theorem B4031747 : Blo 1194414 4031747 := bstep (se 1 (by rfl) ⟨3023810, by rfl⟩ : syracuseStep 4031747 = 6047621) B6047621
theorem B2016515 : Blo 1194414 2016515 := bstep (se 1 (by rfl) ⟨1512386, by rfl⟩ : syracuseStep 2016515 = 3024773) B3024773
theorem B33596693 : Blo 1194414 33596693 := bstep (se 6 (by rfl) ⟨787422, by rfl⟩ : syracuseStep 33596693 = 1574845) B1574845
theorem B2270531 : Blo 1194414 2270531 := bstep (se 1 (by rfl) ⟨1702898, by rfl⟩ : syracuseStep 2270531 = 3405797) B3405797
theorem B3933521 : Blo 1194414 3933521 := bstep (se 2 (by rfl) ⟨1475070, by rfl⟩ : syracuseStep 3933521 = 2950141) B2950141
theorem B8848739 : Blo 1194414 8848739 := bstep (se 1 (by rfl) ⟨6636554, by rfl⟩ : syracuseStep 8848739 = 13273109) B13273109
theorem B1344883 : Blo 1194414 1344883 := bstep (se 1 (by rfl) ⟨1008662, by rfl⟩ : syracuseStep 1344883 = 2017325) B2017325
theorem B2016643 : Blo 1194414 2016643 := bstep (se 1 (by rfl) ⟨1512482, by rfl⟩ : syracuseStep 2016643 = 3024965) B3024965
theorem B3024337 : Blo 1194414 3024337 := bstep (se 2 (by rfl) ⟨1134126, by rfl⟩ : syracuseStep 3024337 = 2268253) B2268253
theorem B2688497 : Blo 1194414 2688497 := bstep (se 2 (by rfl) ⟨1008186, by rfl⟩ : syracuseStep 2688497 = 2016373) B2016373
theorem B2688515 : Blo 1194414 2688515 := bstep (se 1 (by rfl) ⟨2016386, by rfl⟩ : syracuseStep 2688515 = 4032773) B4032773
theorem B1345027 : Blo 1194414 1345027 := bstep (se 1 (by rfl) ⟨1008770, by rfl⟩ : syracuseStep 1345027 = 2017541) B2017541
theorem B4032017 : Blo 1194414 4032017 := bstep (se 2 (by rfl) ⟨1512006, by rfl⟩ : syracuseStep 4032017 = 3024013) B3024013
theorem B2016785 : Blo 1194414 2016785 := bstep (se 2 (by rfl) ⟨756294, by rfl⟩ : syracuseStep 2016785 = 1512589) B1512589
theorem B2016913 : Blo 1194414 2016913 := bstep (se 2 (by rfl) ⟨756342, by rfl⟩ : syracuseStep 2016913 = 1512685) B1512685
theorem B1345171 : Blo 1194414 1345171 := bstep (se 1 (by rfl) ⟨1008878, by rfl⟩ : syracuseStep 1345171 = 2017757) B2017757
theorem B2016947 : Blo 1194414 2016947 := bstep (se 1 (by rfl) ⟨1512710, by rfl⟩ : syracuseStep 2016947 = 3025421) B3025421
theorem B6047459 : Blo 1194414 6047459 := bstep (se 1 (by rfl) ⟨4535594, by rfl⟩ : syracuseStep 6047459 = 9071189) B9071189
theorem B3024611 : Blo 1194414 3024611 := bstep (se 1 (by rfl) ⟨2268458, by rfl⟩ : syracuseStep 3024611 = 4536917) B4536917
theorem B2688785 : Blo 1194414 2688785 := bstep (se 2 (by rfl) ⟨1008294, by rfl⟩ : syracuseStep 2688785 = 2016589) B2016589
theorem B2688803 : Blo 1194414 2688803 := bstep (se 1 (by rfl) ⟨2016602, by rfl⟩ : syracuseStep 2688803 = 4033205) B4033205
theorem B1345315 : Blo 1194414 1345315 := bstep (se 1 (by rfl) ⟨1008986, by rfl⟩ : syracuseStep 1345315 = 2017973) B2017973
theorem B2017075 : Blo 1194414 2017075 := bstep (se 1 (by rfl) ⟨1512806, by rfl⟩ : syracuseStep 2017075 = 3025613) B3025613
theorem B4597667 : Blo 1194414 4597667 := bstep (se 1 (by rfl) ⟨3448250, by rfl⟩ : syracuseStep 4597667 = 6896501) B6896501
theorem B3024803 : Blo 1194414 3024803 := bstep (se 1 (by rfl) ⟨2268602, by rfl⟩ : syracuseStep 3024803 = 4537205) B4537205
theorem B1345459 : Blo 1194414 1345459 := bstep (se 1 (by rfl) ⟨1009094, by rfl⟩ : syracuseStep 1345459 = 2018189) B2018189
theorem B2017217 : Blo 1194414 2017217 := bstep (se 2 (by rfl) ⟨756456, by rfl⟩ : syracuseStep 2017217 = 1512913) B1512913
theorem B6465521 : Blo 1194414 6465521 := bstep (se 2 (by rfl) ⟨2424570, by rfl⟩ : syracuseStep 6465521 = 4849141) B4849141
theorem B3827729 : Blo 1194414 3827729 := bstep (se 2 (by rfl) ⟨1435398, by rfl⟩ : syracuseStep 3827729 = 2870797) B2870797
theorem B4032557 : Blo 1194414 4032557 := bstep (se 3 (by rfl) ⟨756104, by rfl⟩ : syracuseStep 4032557 = 1512209) B1512209
theorem B3401777 : Blo 1194414 3401777 := bstep (se 2 (by rfl) ⟨1275666, by rfl⟩ : syracuseStep 3401777 = 2551333) B2551333
theorem B2689073 : Blo 1194414 2689073 := bstep (se 2 (by rfl) ⟨1008402, by rfl⟩ : syracuseStep 2689073 = 2016805) B2016805
theorem B2017345 : Blo 1194414 2017345 := bstep (se 2 (by rfl) ⟨756504, by rfl⟩ : syracuseStep 2017345 = 1513009) B1513009
theorem B2689091 : Blo 1194414 2689091 := bstep (se 1 (by rfl) ⟨2016818, by rfl⟩ : syracuseStep 2689091 = 4033637) B4033637
theorem B1345603 : Blo 1194414 1345603 := bstep (se 1 (by rfl) ⟨1009202, by rfl⟩ : syracuseStep 1345603 = 2018405) B2018405
theorem B4843597 : Blo 1194414 4843597 := bstep (se 3 (by rfl) ⟨908174, by rfl⟩ : syracuseStep 4843597 = 1816349) B1816349
theorem B4032611 : Blo 1194414 4032611 := bstep (se 1 (by rfl) ⟨3024458, by rfl⟩ : syracuseStep 4032611 = 6048917) B6048917
theorem B2017379 : Blo 1194414 2017379 := bstep (se 1 (by rfl) ⟨1513034, by rfl⟩ : syracuseStep 2017379 = 3026069) B3026069
theorem B6457477 : Blo 1194414 6457477 := bstep (se 4 (by rfl) ⟨605388, by rfl⟩ : syracuseStep 6457477 = 1210777) B1210777
theorem B8284357 : Blo 1194414 8284357 := bstep (se 4 (by rfl) ⟨776658, by rfl⟩ : syracuseStep 8284357 = 1553317) B1553317
theorem B1345747 : Blo 1194414 1345747 := bstep (se 1 (by rfl) ⟨1009310, by rfl⟩ : syracuseStep 1345747 = 2018621) B2018621
theorem B2017507 : Blo 1194414 2017507 := bstep (se 1 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 2017507 = 3026261) B3026261
theorem B2689361 : Blo 1194414 2689361 := bstep (se 2 (by rfl) ⟨1008510, by rfl⟩ : syracuseStep 2689361 = 2017021) B2017021
theorem B2689379 : Blo 1194414 2689379 := bstep (se 1 (by rfl) ⟨2017034, by rfl⟩ : syracuseStep 2689379 = 4034069) B4034069
theorem B13805923 : Blo 1194414 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B1345891 : Blo 1194414 1345891 := bstep (se 1 (by rfl) ⟨1009418, by rfl⟩ : syracuseStep 1345891 = 2018837) B2018837
theorem B4032881 : Blo 1194414 4032881 := bstep (se 2 (by rfl) ⟨1512330, by rfl⟩ : syracuseStep 4032881 = 3024661) B3024661
theorem B2017649 : Blo 1194414 2017649 := bstep (se 2 (by rfl) ⟨756618, by rfl⟩ : syracuseStep 2017649 = 1513237) B1513237
theorem B6056369 : Blo 1194414 6056369 := bstep (se 2 (by rfl) ⟨2271138, by rfl⟩ : syracuseStep 6056369 = 4542277) B4542277
theorem B2017777 : Blo 1194414 2017777 := bstep (se 2 (by rfl) ⟨756666, by rfl⟩ : syracuseStep 2017777 = 1513333) B1513333
theorem B6048269 : Blo 1194414 6048269 := bstep (se 3 (by rfl) ⟨1134050, by rfl⟩ : syracuseStep 6048269 = 2268101) B2268101
theorem B2017811 : Blo 1194414 2017811 := bstep (se 1 (by rfl) ⟨1513358, by rfl⟩ : syracuseStep 2017811 = 3026717) B3026717
theorem B5171747 : Blo 1194414 5171747 := bstep (se 1 (by rfl) ⟨3878810, by rfl⟩ : syracuseStep 5171747 = 7757621) B7757621
theorem B3230243 : Blo 1194414 3230243 := bstep (se 1 (by rfl) ⟨2422682, by rfl⟩ : syracuseStep 3230243 = 4845365) B4845365
theorem B2689649 : Blo 1194414 2689649 := bstep (se 2 (by rfl) ⟨1008618, by rfl⟩ : syracuseStep 2689649 = 2017237) B2017237
theorem B2689667 : Blo 1194414 2689667 := bstep (se 1 (by rfl) ⟨2017250, by rfl⟩ : syracuseStep 2689667 = 4034501) B4034501
theorem B2017939 : Blo 1194414 2017939 := bstep (se 1 (by rfl) ⟨1513454, by rfl⟩ : syracuseStep 2017939 = 3026909) B3026909
theorem B3066545 : Blo 1194414 3066545 := bstep (se 2 (by rfl) ⟨1149954, by rfl⟩ : syracuseStep 3066545 = 2299909) B2299909
theorem B7269041 : Blo 1194414 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B3402449 : Blo 1194414 3402449 := bstep (se 2 (by rfl) ⟨1275918, by rfl⟩ : syracuseStep 3402449 = 2551837) B2551837
theorem B1362691 : Blo 1194414 1362691 := bstep (se 1 (by rfl) ⟨1022018, by rfl⟩ : syracuseStep 1362691 = 2044037) B2044037
theorem B2018081 : Blo 1194414 2018081 := bstep (se 2 (by rfl) ⟨756780, by rfl⟩ : syracuseStep 2018081 = 1513561) B1513561
theorem B5106509 : Blo 1194414 5106509 := bstep (se 3 (by rfl) ⟨957470, by rfl⟩ : syracuseStep 5106509 = 1914941) B1914941
theorem B3025745 : Blo 1194414 3025745 := bstep (se 2 (by rfl) ⟨1134654, by rfl⟩ : syracuseStep 3025745 = 2269309) B2269309
theorem B3025795 : Blo 1194414 3025795 := bstep (se 1 (by rfl) ⟨2269346, by rfl⟩ : syracuseStep 3025795 = 4538693) B4538693
theorem B4033421 : Blo 1194414 4033421 := bstep (se 3 (by rfl) ⟨756266, by rfl⟩ : syracuseStep 4033421 = 1512533) B1512533
theorem B2689937 : Blo 1194414 2689937 := bstep (se 2 (by rfl) ⟨1008726, by rfl⟩ : syracuseStep 2689937 = 2017453) B2017453
theorem B2689955 : Blo 1194414 2689955 := bstep (se 1 (by rfl) ⟨2017466, by rfl⟩ : syracuseStep 2689955 = 4034933) B4034933
theorem B2018209 : Blo 1194414 2018209 := bstep (se 2 (by rfl) ⟨756828, by rfl⟩ : syracuseStep 2018209 = 1513657) B1513657
theorem B4033475 : Blo 1194414 4033475 := bstep (se 1 (by rfl) ⟨3025106, by rfl⟩ : syracuseStep 4033475 = 6050213) B6050213
theorem B2018243 : Blo 1194414 2018243 := bstep (se 1 (by rfl) ⟨1513682, by rfl⟩ : syracuseStep 2018243 = 3027365) B3027365
theorem B1616851 : Blo 1194414 1616851 := bstep (se 1 (by rfl) ⟨1212638, by rfl⟩ : syracuseStep 1616851 = 2425277) B2425277
theorem B3025937 : Blo 1194414 3025937 := bstep (se 2 (by rfl) ⟨1134726, by rfl⟩ : syracuseStep 3025937 = 2269453) B2269453
theorem B2018371 : Blo 1194414 2018371 := bstep (se 1 (by rfl) ⟨1513778, by rfl⟩ : syracuseStep 2018371 = 3027557) B3027557
theorem B13626467 : Blo 1194414 13626467 := bstep (se 1 (by rfl) ⟨10219850, by rfl⟩ : syracuseStep 13626467 = 20439701) B20439701
theorem B3828845 : Blo 1194414 3828845 := bstep (se 3 (by rfl) ⟨717908, by rfl⟩ : syracuseStep 3828845 = 1435817) B1435817
theorem B5106851 : Blo 1194414 5106851 := bstep (se 1 (by rfl) ⟨3830138, by rfl⟩ : syracuseStep 5106851 = 7660277) B7660277
theorem B2690225 : Blo 1194414 2690225 := bstep (se 2 (by rfl) ⟨1008834, by rfl⟩ : syracuseStep 2690225 = 2017669) B2017669
theorem B2690243 : Blo 1194414 2690243 := bstep (se 1 (by rfl) ⟨2017682, by rfl⟩ : syracuseStep 2690243 = 4035365) B4035365
theorem B4033745 : Blo 1194414 4033745 := bstep (se 2 (by rfl) ⟨1512654, by rfl⟩ : syracuseStep 4033745 = 3025309) B3025309
theorem B2018513 : Blo 1194414 2018513 := bstep (se 2 (by rfl) ⟨756942, by rfl⟩ : syracuseStep 2018513 = 1513885) B1513885
theorem B2018641 : Blo 1194414 2018641 := bstep (se 2 (by rfl) ⟨756990, by rfl⟩ : syracuseStep 2018641 = 1513981) B1513981
theorem B2018675 : Blo 1194414 2018675 := bstep (se 1 (by rfl) ⟨1514006, by rfl⟩ : syracuseStep 2018675 = 3028013) B3028013
theorem B3231139 : Blo 1194414 3231139 := bstep (se 1 (by rfl) ⟨2423354, by rfl⟩ : syracuseStep 3231139 = 4846709) B4846709
theorem B2690513 : Blo 1194414 2690513 := bstep (se 2 (by rfl) ⟨1008942, by rfl⟩ : syracuseStep 2690513 = 2017885) B2017885
theorem B3403235 : Blo 1194414 3403235 := bstep (se 1 (by rfl) ⟨2552426, by rfl⟩ : syracuseStep 3403235 = 5104853) B5104853
theorem B2690531 : Blo 1194414 2690531 := bstep (se 1 (by rfl) ⟨2017898, by rfl⟩ : syracuseStep 2690531 = 4035797) B4035797
theorem B2018803 : Blo 1194414 2018803 := bstep (se 1 (by rfl) ⟨1514102, by rfl⟩ : syracuseStep 2018803 = 3028205) B3028205
theorem B5107313 : Blo 1194414 5107313 := bstep (se 2 (by rfl) ⟨1915242, by rfl⟩ : syracuseStep 5107313 = 3830485) B3830485
theorem B4542065 : Blo 1194414 4542065 := bstep (se 2 (by rfl) ⟨1703274, by rfl⟩ : syracuseStep 4542065 = 3406549) B3406549
theorem B2018945 : Blo 1194414 2018945 := bstep (se 2 (by rfl) ⟨757104, by rfl⟩ : syracuseStep 2018945 = 1514209) B1514209
theorem B2043571 : Blo 1194414 2043571 := bstep (se 1 (by rfl) ⟨1532678, by rfl⟩ : syracuseStep 2043571 = 3065357) B3065357
theorem B4034285 : Blo 1194414 4034285 := bstep (se 3 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 4034285 = 1512857) B1512857
theorem B2690801 : Blo 1194414 2690801 := bstep (se 2 (by rfl) ⟨1009050, by rfl⟩ : syracuseStep 2690801 = 2018101) B2018101
theorem B2690819 : Blo 1194414 2690819 := bstep (se 1 (by rfl) ⟨2018114, by rfl⟩ : syracuseStep 2690819 = 4036229) B4036229
theorem B4034339 : Blo 1194414 4034339 := bstep (se 1 (by rfl) ⟨3025754, by rfl⟩ : syracuseStep 4034339 = 6051509) B6051509
theorem B3403565 : Blo 1194414 3403565 := bstep (se 3 (by rfl) ⟨638168, by rfl⟩ : syracuseStep 3403565 = 1276337) B1276337
theorem B3403633 : Blo 1194414 3403633 := bstep (se 2 (by rfl) ⟨1276362, by rfl⟩ : syracuseStep 3403633 = 2552725) B2552725
theorem B3026929 : Blo 1194414 3026929 := bstep (se 2 (by rfl) ⟨1135098, by rfl⟩ : syracuseStep 3026929 = 2270197) B2270197
theorem B6467597 : Blo 1194414 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B2691089 : Blo 1194414 2691089 := bstep (se 2 (by rfl) ⟨1009158, by rfl⟩ : syracuseStep 2691089 = 2018317) B2018317
theorem B2691107 : Blo 1194414 2691107 := bstep (se 1 (by rfl) ⟨2018330, by rfl⟩ : syracuseStep 2691107 = 4036661) B4036661
theorem B4034609 : Blo 1194414 4034609 := bstep (se 2 (by rfl) ⟨1512978, by rfl⟩ : syracuseStep 4034609 = 3025957) B3025957
theorem B3403907 : Blo 1194414 3403907 := bstep (se 1 (by rfl) ⟨2552930, by rfl⟩ : syracuseStep 3403907 = 5105861) B5105861
theorem B3829933 : Blo 1194414 3829933 := bstep (se 3 (by rfl) ⟨718112, by rfl⟩ : syracuseStep 3829933 = 1436225) B1436225
theorem B2044145 : Blo 1194414 2044145 := bstep (se 2 (by rfl) ⟨766554, by rfl⟩ : syracuseStep 2044145 = 1533109) B1533109
theorem B3027203 : Blo 1194414 3027203 := bstep (se 1 (by rfl) ⟨2270402, by rfl⟩ : syracuseStep 3027203 = 4540805) B4540805
theorem B3068177 : Blo 1194414 3068177 := bstep (se 2 (by rfl) ⟨1150566, by rfl⟩ : syracuseStep 3068177 = 2301133) B2301133
theorem B2691377 : Blo 1194414 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B2691395 : Blo 1194414 2691395 := bstep (se 1 (by rfl) ⟨2018546, by rfl⟩ : syracuseStep 2691395 = 4037093) B4037093
theorem B1511779 : Blo 1194414 1511779 := bstep (se 1 (by rfl) ⟨1133834, by rfl⟩ : syracuseStep 1511779 = 2267669) B2267669
theorem B2552195 : Blo 1194414 2552195 := bstep (se 1 (by rfl) ⟨1914146, by rfl⟩ : syracuseStep 2552195 = 3828293) B3828293
theorem B1511875 : Blo 1194414 1511875 := bstep (se 1 (by rfl) ⟨1133906, by rfl⟩ : syracuseStep 1511875 = 2267813) B2267813
theorem B3027395 : Blo 1194414 3027395 := bstep (se 1 (by rfl) ⟨2270546, by rfl⟩ : syracuseStep 3027395 = 4541093) B4541093
theorem B6803939 : Blo 1194414 6803939 := bstep (se 1 (by rfl) ⟨5102954, by rfl⟩ : syracuseStep 6803939 = 10205909) B10205909
theorem B4035149 : Blo 1194414 4035149 := bstep (se 3 (by rfl) ⟨756590, by rfl⟩ : syracuseStep 4035149 = 1513181) B1513181
theorem B2691665 : Blo 1194414 2691665 := bstep (se 2 (by rfl) ⟨1009374, by rfl⟩ : syracuseStep 2691665 = 2018749) B2018749
theorem B9826915 : Blo 1194414 9826915 := bstep (se 1 (by rfl) ⟨7370186, by rfl⟩ : syracuseStep 9826915 = 14740373) B14740373
theorem B2691683 : Blo 1194414 2691683 := bstep (se 1 (by rfl) ⟨2018762, by rfl⟩ : syracuseStep 2691683 = 4037525) B4037525
theorem B4035203 : Blo 1194414 4035203 := bstep (se 1 (by rfl) ⟨3026402, by rfl⟩ : syracuseStep 4035203 = 6052805) B6052805
theorem B3232493 : Blo 1194414 3232493 := bstep (se 3 (by rfl) ⟨606092, by rfl⟩ : syracuseStep 3232493 = 1212185) B1212185
theorem B4305649 : Blo 1194414 4305649 := bstep (se 2 (by rfl) ⟨1614618, by rfl⟩ : syracuseStep 4305649 = 3229237) B3229237
theorem B3879697 : Blo 1194414 3879697 := bstep (se 2 (by rfl) ⟨1454886, by rfl⟩ : syracuseStep 3879697 = 2909773) B2909773
theorem B5174093 : Blo 1194414 5174093 := bstep (se 3 (by rfl) ⟨970142, by rfl⟩ : syracuseStep 5174093 = 1940285) B1940285
theorem B1700689 : Blo 1194414 1700689 := bstep (se 2 (by rfl) ⟨637758, by rfl⟩ : syracuseStep 1700689 = 1275517) B1275517
theorem B1700723 : Blo 1194414 1700723 := bstep (se 1 (by rfl) ⟨1275542, by rfl⟩ : syracuseStep 1700723 = 2551085) B2551085
theorem B4035473 : Blo 1194414 4035473 := bstep (se 2 (by rfl) ⟨1513302, by rfl⟩ : syracuseStep 4035473 = 3026605) B3026605
theorem B1512371 : Blo 1194414 1512371 := bstep (se 1 (by rfl) ⟨1134278, by rfl⟩ : syracuseStep 1512371 = 2268557) B2268557
theorem B3404749 : Blo 1194414 3404749 := bstep (se 3 (by rfl) ⟨638390, by rfl⟩ : syracuseStep 3404749 = 1276781) B1276781
theorem B12932081 : Blo 1194414 12932081 := bstep (se 2 (by rfl) ⟨4849530, by rfl⟩ : syracuseStep 12932081 = 9699061) B9699061
theorem B3404909 : Blo 1194414 3404909 := bstep (se 3 (by rfl) ⟨638420, by rfl⟩ : syracuseStep 3404909 = 1276841) B1276841
theorem B9196685 : Blo 1194414 9196685 := bstep (se 3 (by rfl) ⟨1724378, by rfl⟩ : syracuseStep 9196685 = 3448757) B3448757
theorem B4535459 : Blo 1194414 4535459 := bstep (se 1 (by rfl) ⟨3401594, by rfl⟩ : syracuseStep 4535459 = 6803189) B6803189
theorem B4535473 : Blo 1194414 4535473 := bstep (se 2 (by rfl) ⟨1700802, by rfl⟩ : syracuseStep 4535473 = 3401605) B3401605
theorem B6812869 : Blo 1194414 6812869 := bstep (se 4 (by rfl) ⟨638706, by rfl⟩ : syracuseStep 6812869 = 1277413) B1277413
theorem B10220741 : Blo 1194414 10220741 := bstep (se 4 (by rfl) ⟨958194, by rfl⟩ : syracuseStep 10220741 = 1916389) B1916389
theorem B3880163 : Blo 1194414 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B7664867 : Blo 1194414 7664867 := bstep (se 1 (by rfl) ⟨5748650, by rfl⟩ : syracuseStep 7664867 = 11497301) B11497301
theorem B3405091 : Blo 1194414 3405091 := bstep (se 1 (by rfl) ⟨2553818, by rfl⟩ : syracuseStep 3405091 = 5107637) B5107637
theorem B6051185 : Blo 1194414 6051185 := bstep (se 2 (by rfl) ⟨2269194, by rfl⟩ : syracuseStep 6051185 = 4538389) B4538389
theorem B3028337 : Blo 1194414 3028337 := bstep (se 2 (by rfl) ⟨1135626, by rfl⟩ : syracuseStep 3028337 = 2271253) B2271253
theorem B1701281 : Blo 1194414 1701281 := bstep (se 2 (by rfl) ⟨637980, by rfl⟩ : syracuseStep 1701281 = 1275961) B1275961
theorem B1914275 : Blo 1194414 1914275 := bstep (se 1 (by rfl) ⟨1435706, by rfl⟩ : syracuseStep 1914275 = 2871413) B2871413
theorem B2872739 : Blo 1194414 2872739 := bstep (se 1 (by rfl) ⟨2154554, by rfl⟩ : syracuseStep 2872739 = 4309109) B4309109
theorem B3028387 : Blo 1194414 3028387 := bstep (se 1 (by rfl) ⟨2271290, by rfl⟩ : syracuseStep 3028387 = 4542581) B4542581
theorem B4036013 : Blo 1194414 4036013 := bstep (se 3 (by rfl) ⟨756752, by rfl⟩ : syracuseStep 4036013 = 1513505) B1513505
theorem B15316451 : Blo 1194414 15316451 := bstep (se 1 (by rfl) ⟨11487338, by rfl⟩ : syracuseStep 15316451 = 22974677) B22974677
theorem B4036067 : Blo 1194414 4036067 := bstep (se 1 (by rfl) ⟨3027050, by rfl⟩ : syracuseStep 4036067 = 6054101) B6054101
theorem B1701361 : Blo 1194414 1701361 := bstep (se 2 (by rfl) ⟨638010, by rfl⟩ : syracuseStep 1701361 = 1276021) B1276021
theorem B1660433 : Blo 1194414 1660433 := bstep (se 2 (by rfl) ⟨622662, by rfl⟩ : syracuseStep 1660433 = 1245325) B1245325
theorem B1513075 : Blo 1194414 1513075 := bstep (se 1 (by rfl) ⟨1134806, by rfl⟩ : syracuseStep 1513075 = 2269613) B2269613
theorem B1791635 : Blo 1194414 1791635 := bstep (se 1 (by rfl) ⟨1343726, by rfl⟩ : syracuseStep 1791635 = 2687453) B2687453
theorem B1791665 : Blo 1194414 1791665 := bstep (se 2 (by rfl) ⟨671874, by rfl⟩ : syracuseStep 1791665 = 1343749) B1343749
theorem B1791683 : Blo 1194414 1791683 := bstep (se 1 (by rfl) ⟨1343762, by rfl⟩ : syracuseStep 1791683 = 2687525) B2687525
theorem B1513171 : Blo 1194414 1513171 := bstep (se 1 (by rfl) ⟨1134878, by rfl⟩ : syracuseStep 1513171 = 2269757) B2269757
theorem B1791713 : Blo 1194414 1791713 := bstep (se 2 (by rfl) ⟨671892, by rfl⟩ : syracuseStep 1791713 = 1343785) B1343785
theorem B4036337 : Blo 1194414 4036337 := bstep (se 2 (by rfl) ⟨1513626, by rfl⟩ : syracuseStep 4036337 = 3027253) B3027253
theorem B1791731 : Blo 1194414 1791731 := bstep (se 1 (by rfl) ⟨1343798, by rfl⟩ : syracuseStep 1791731 = 2687597) B2687597
theorem B1791761 : Blo 1194414 1791761 := bstep (se 2 (by rfl) ⟨671910, by rfl⟩ : syracuseStep 1791761 = 1343821) B1343821
theorem B1791779 : Blo 1194414 1791779 := bstep (se 1 (by rfl) ⟨1343834, by rfl⟩ : syracuseStep 1791779 = 2687669) B2687669
theorem B5748515 : Blo 1194414 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B1791809 : Blo 1194414 1791809 := bstep (se 2 (by rfl) ⟨671928, by rfl⟩ : syracuseStep 1791809 = 1343857) B1343857
theorem B1791827 : Blo 1194414 1791827 := bstep (se 1 (by rfl) ⟨1343870, by rfl⟩ : syracuseStep 1791827 = 2687741) B2687741
theorem B1791857 : Blo 1194414 1791857 := bstep (se 2 (by rfl) ⟨671946, by rfl⟩ : syracuseStep 1791857 = 1343893) B1343893
theorem B1791875 : Blo 1194414 1791875 := bstep (se 1 (by rfl) ⟨1343906, by rfl⟩ : syracuseStep 1791875 = 2687813) B2687813
theorem B1791905 : Blo 1194414 1791905 := bstep (se 2 (by rfl) ⟨671964, by rfl⟩ : syracuseStep 1791905 = 1343929) B1343929
theorem B1914787 : Blo 1194414 1914787 := bstep (se 1 (by rfl) ⟨1436090, by rfl⟩ : syracuseStep 1914787 = 2872181) B2872181
theorem B3831715 : Blo 1194414 3831715 := bstep (se 1 (by rfl) ⟨2873786, by rfl⟩ : syracuseStep 3831715 = 5747573) B5747573
theorem B1791923 : Blo 1194414 1791923 := bstep (se 1 (by rfl) ⟨1343942, by rfl⟩ : syracuseStep 1791923 = 2687885) B2687885
theorem B1791953 : Blo 1194414 1791953 := bstep (se 2 (by rfl) ⟨671982, by rfl⟩ : syracuseStep 1791953 = 1343965) B1343965
theorem B1914833 : Blo 1194414 1914833 := bstep (se 2 (by rfl) ⟨718062, by rfl⟩ : syracuseStep 1914833 = 1436125) B1436125
theorem B1791971 : Blo 1194414 1791971 := bstep (se 1 (by rfl) ⟨1343978, by rfl⟩ : syracuseStep 1791971 = 2687957) B2687957
theorem B3831779 : Blo 1194414 3831779 := bstep (se 1 (by rfl) ⟨2873834, by rfl⟩ : syracuseStep 3831779 = 5747669) B5747669
theorem B1792001 : Blo 1194414 1792001 := bstep (se 2 (by rfl) ⟨672000, by rfl⟩ : syracuseStep 1792001 = 1344001) B1344001
theorem B1792019 : Blo 1194414 1792019 := bstep (se 1 (by rfl) ⟨1344014, by rfl⟩ : syracuseStep 1792019 = 2688029) B2688029
theorem B7657507 : Blo 1194414 7657507 := bstep (se 1 (by rfl) ⟨5743130, by rfl⟩ : syracuseStep 7657507 = 11486261) B11486261
theorem B1792049 : Blo 1194414 1792049 := bstep (se 2 (by rfl) ⟨672018, by rfl⟩ : syracuseStep 1792049 = 1344037) B1344037
theorem B3831857 : Blo 1194414 3831857 := bstep (se 2 (by rfl) ⟨1436946, by rfl⟩ : syracuseStep 3831857 = 2873893) B2873893
theorem B1792067 : Blo 1194414 1792067 := bstep (se 1 (by rfl) ⟨1344050, by rfl⟩ : syracuseStep 1792067 = 2688101) B2688101
theorem B2873411 : Blo 1194414 2873411 := bstep (se 1 (by rfl) ⟨2155058, by rfl⟩ : syracuseStep 2873411 = 4310117) B4310117
theorem B1792097 : Blo 1194414 1792097 := bstep (se 2 (by rfl) ⟨672036, by rfl⟩ : syracuseStep 1792097 = 1344073) B1344073
theorem B14735459 : Blo 1194414 14735459 := bstep (se 1 (by rfl) ⟨11051594, by rfl⟩ : syracuseStep 14735459 = 22103189) B22103189
theorem B1792115 : Blo 1194414 1792115 := bstep (se 1 (by rfl) ⟨1344086, by rfl⟩ : syracuseStep 1792115 = 2688173) B2688173
theorem B1792145 : Blo 1194414 1792145 := bstep (se 2 (by rfl) ⟨672054, by rfl⟩ : syracuseStep 1792145 = 1344109) B1344109
theorem B1792163 : Blo 1194414 1792163 := bstep (se 1 (by rfl) ⟨1344122, by rfl⟩ : syracuseStep 1792163 = 2688245) B2688245
theorem B4790449 : Blo 1194414 4790449 := bstep (se 2 (by rfl) ⟨1796418, by rfl⟩ : syracuseStep 4790449 = 3592837) B3592837
theorem B1792193 : Blo 1194414 1792193 := bstep (se 2 (by rfl) ⟨672072, by rfl⟩ : syracuseStep 1792193 = 1344145) B1344145
theorem B1513667 : Blo 1194414 1513667 := bstep (se 1 (by rfl) ⟨1135250, by rfl⟩ : syracuseStep 1513667 = 2270501) B2270501
theorem B1792211 : Blo 1194414 1792211 := bstep (se 1 (by rfl) ⟨1344158, by rfl⟩ : syracuseStep 1792211 = 2688317) B2688317
theorem B1792241 : Blo 1194414 1792241 := bstep (se 2 (by rfl) ⟨672090, by rfl⟩ : syracuseStep 1792241 = 1344181) B1344181
theorem B1792259 : Blo 1194414 1792259 := bstep (se 1 (by rfl) ⟨1344194, by rfl⟩ : syracuseStep 1792259 = 2688389) B2688389
theorem B2726147 : Blo 1194414 2726147 := bstep (se 1 (by rfl) ⟨2044610, by rfl⟩ : syracuseStep 2726147 = 4089221) B4089221
theorem B1702147 : Blo 1194414 1702147 := bstep (se 1 (by rfl) ⟨1276610, by rfl⟩ : syracuseStep 1702147 = 2553221) B2553221
theorem B4036877 : Blo 1194414 4036877 := bstep (se 3 (by rfl) ⟨756914, by rfl⟩ : syracuseStep 4036877 = 1513829) B1513829
theorem B1792289 : Blo 1194414 1792289 := bstep (se 2 (by rfl) ⟨672108, by rfl⟩ : syracuseStep 1792289 = 1344217) B1344217
theorem B1792307 : Blo 1194414 1792307 := bstep (se 1 (by rfl) ⟨1344230, by rfl⟩ : syracuseStep 1792307 = 2688461) B2688461
theorem B4036931 : Blo 1194414 4036931 := bstep (se 1 (by rfl) ⟨3027698, by rfl⟩ : syracuseStep 4036931 = 6055397) B6055397
theorem B1792337 : Blo 1194414 1792337 := bstep (se 2 (by rfl) ⟨672126, by rfl⟩ : syracuseStep 1792337 = 1344253) B1344253
theorem B2873681 : Blo 1194414 2873681 := bstep (se 2 (by rfl) ⟨1077630, by rfl⟩ : syracuseStep 2873681 = 2155261) B2155261
theorem B1792355 : Blo 1194414 1792355 := bstep (se 1 (by rfl) ⟨1344266, by rfl⟩ : syracuseStep 1792355 = 2688533) B2688533
theorem B2554211 : Blo 1194414 2554211 := bstep (se 1 (by rfl) ⟨1915658, by rfl⟩ : syracuseStep 2554211 = 3831317) B3831317
theorem B3275117 : Blo 1194414 3275117 := bstep (se 3 (by rfl) ⟨614084, by rfl⟩ : syracuseStep 3275117 = 1228169) B1228169
theorem B1792385 : Blo 1194414 1792385 := bstep (se 2 (by rfl) ⟨672144, by rfl⟩ : syracuseStep 1792385 = 1344289) B1344289
theorem B1792403 : Blo 1194414 1792403 := bstep (se 1 (by rfl) ⟨1344302, by rfl⟩ : syracuseStep 1792403 = 2688605) B2688605
theorem B2152867 : Blo 1194414 2152867 := bstep (se 1 (by rfl) ⟨1614650, by rfl⟩ : syracuseStep 2152867 = 3229301) B3229301
theorem B1792433 : Blo 1194414 1792433 := bstep (se 2 (by rfl) ⟨672162, by rfl⟩ : syracuseStep 1792433 = 1344325) B1344325
theorem B1194419 : Blo 1194414 1194419 := bstep (se 1 (by rfl) ⟨895814, by rfl⟩ : syracuseStep 1194419 = 1791629) B1791629
theorem B1194435 : Blo 1194414 1194435 := bstep (se 1 (by rfl) ⟨895826, by rfl⟩ : syracuseStep 1194435 = 1791653) B1791653
theorem B1792451 : Blo 1194414 1792451 := bstep (se 1 (by rfl) ⟨1344338, by rfl⟩ : syracuseStep 1792451 = 2688677) B2688677
theorem B1194451 : Blo 1194414 1194451 := bstep (se 1 (by rfl) ⟨895838, by rfl⟩ : syracuseStep 1194451 = 1791677) B1791677
theorem B1792481 : Blo 1194414 1792481 := bstep (se 2 (by rfl) ⟨672180, by rfl⟩ : syracuseStep 1792481 = 1344361) B1344361
theorem B1194467 : Blo 1194414 1194467 := bstep (se 1 (by rfl) ⟨895850, by rfl⟩ : syracuseStep 1194467 = 1791701) B1791701
theorem B1194483 : Blo 1194414 1194483 := bstep (se 1 (by rfl) ⟨895862, by rfl⟩ : syracuseStep 1194483 = 1791725) B1791725
theorem B1792499 : Blo 1194414 1792499 := bstep (se 1 (by rfl) ⟨1344374, by rfl⟩ : syracuseStep 1792499 = 2688749) B2688749
theorem B1194499 : Blo 1194414 1194499 := bstep (se 1 (by rfl) ⟨895874, by rfl⟩ : syracuseStep 1194499 = 1791749) B1791749
theorem B1792529 : Blo 1194414 1792529 := bstep (se 2 (by rfl) ⟨672198, by rfl⟩ : syracuseStep 1792529 = 1344397) B1344397
theorem B2873873 : Blo 1194414 2873873 := bstep (se 2 (by rfl) ⟨1077702, by rfl⟩ : syracuseStep 2873873 = 2155405) B2155405
theorem B1194515 : Blo 1194414 1194515 := bstep (se 1 (by rfl) ⟨895886, by rfl⟩ : syracuseStep 1194515 = 1791773) B1791773
theorem B1194531 : Blo 1194414 1194531 := bstep (se 1 (by rfl) ⟨895898, by rfl⟩ : syracuseStep 1194531 = 1791797) B1791797
theorem B1792547 : Blo 1194414 1792547 := bstep (se 1 (by rfl) ⟨1344410, by rfl⟩ : syracuseStep 1792547 = 2688821) B2688821
theorem B1194547 : Blo 1194414 1194547 := bstep (se 1 (by rfl) ⟨895910, by rfl⟩ : syracuseStep 1194547 = 1791821) B1791821
theorem B1792577 : Blo 1194414 1792577 := bstep (se 2 (by rfl) ⟨672216, by rfl⟩ : syracuseStep 1792577 = 1344433) B1344433
theorem B1194563 : Blo 1194414 1194563 := bstep (se 1 (by rfl) ⟨895922, by rfl⟩ : syracuseStep 1194563 = 1791845) B1791845
theorem B4037201 : Blo 1194414 4037201 := bstep (se 2 (by rfl) ⟨1513950, by rfl⟩ : syracuseStep 4037201 = 3027901) B3027901
theorem B1194579 : Blo 1194414 1194579 := bstep (se 1 (by rfl) ⟨895934, by rfl⟩ : syracuseStep 1194579 = 1791869) B1791869
theorem B1792595 : Blo 1194414 1792595 := bstep (se 1 (by rfl) ⟨1344446, by rfl⟩ : syracuseStep 1792595 = 2688893) B2688893
theorem B1194595 : Blo 1194414 1194595 := bstep (se 1 (by rfl) ⟨895946, by rfl⟩ : syracuseStep 1194595 = 1791893) B1791893
theorem B4536931 : Blo 1194414 4536931 := bstep (se 1 (by rfl) ⟨3402698, by rfl⟩ : syracuseStep 4536931 = 6805397) B6805397
theorem B1792625 : Blo 1194414 1792625 := bstep (se 2 (by rfl) ⟨672234, by rfl⟩ : syracuseStep 1792625 = 1344469) B1344469
theorem B1915505 : Blo 1194414 1915505 := bstep (se 2 (by rfl) ⟨718314, by rfl⟩ : syracuseStep 1915505 = 1436629) B1436629
theorem B1194611 : Blo 1194414 1194611 := bstep (se 1 (by rfl) ⟨895958, by rfl⟩ : syracuseStep 1194611 = 1791917) B1791917
theorem B2873969 : Blo 1194414 2873969 := bstep (se 2 (by rfl) ⟨1077738, by rfl⟩ : syracuseStep 2873969 = 2155477) B2155477
theorem B1194627 : Blo 1194414 1194627 := bstep (se 1 (by rfl) ⟨895970, by rfl⟩ : syracuseStep 1194627 = 1791941) B1791941
theorem B1792643 : Blo 1194414 1792643 := bstep (se 1 (by rfl) ⟨1344482, by rfl⟩ : syracuseStep 1792643 = 2688965) B2688965
theorem B3406481 : Blo 1194414 3406481 := bstep (se 2 (by rfl) ⟨1277430, by rfl⟩ : syracuseStep 3406481 = 2554861) B2554861
theorem B1194643 : Blo 1194414 1194643 := bstep (se 1 (by rfl) ⟨895982, by rfl⟩ : syracuseStep 1194643 = 1791965) B1791965
theorem B1792673 : Blo 1194414 1792673 := bstep (se 2 (by rfl) ⟨672252, by rfl⟩ : syracuseStep 1792673 = 1344505) B1344505
theorem B1194659 : Blo 1194414 1194659 := bstep (se 1 (by rfl) ⟨895994, by rfl⟩ : syracuseStep 1194659 = 1791989) B1791989
theorem B1792691 : Blo 1194414 1792691 := bstep (se 1 (by rfl) ⟨1344518, by rfl⟩ : syracuseStep 1792691 = 2689037) B2689037
theorem B1194675 : Blo 1194414 1194675 := bstep (se 1 (by rfl) ⟨896006, by rfl⟩ : syracuseStep 1194675 = 1792013) B1792013
theorem B1194691 : Blo 1194414 1194691 := bstep (se 1 (by rfl) ⟨896018, by rfl⟩ : syracuseStep 1194691 = 1792037) B1792037
theorem B1792721 : Blo 1194414 1792721 := bstep (se 2 (by rfl) ⟨672270, by rfl⟩ : syracuseStep 1792721 = 1344541) B1344541
theorem B1194707 : Blo 1194414 1194707 := bstep (se 1 (by rfl) ⟨896030, by rfl⟩ : syracuseStep 1194707 = 1792061) B1792061
theorem B1866451 : Blo 1194414 1866451 := bstep (se 1 (by rfl) ⟨1399838, by rfl⟩ : syracuseStep 1866451 = 2799677) B2799677
theorem B1702625 : Blo 1194414 1702625 := bstep (se 2 (by rfl) ⟨638484, by rfl⟩ : syracuseStep 1702625 = 1276969) B1276969
theorem B1194723 : Blo 1194414 1194723 := bstep (se 1 (by rfl) ⟨896042, by rfl⟩ : syracuseStep 1194723 = 1792085) B1792085
theorem B1792739 : Blo 1194414 1792739 := bstep (se 1 (by rfl) ⟨1344554, by rfl⟩ : syracuseStep 1792739 = 2689109) B2689109
theorem B1194739 : Blo 1194414 1194739 := bstep (se 1 (by rfl) ⟨896054, by rfl⟩ : syracuseStep 1194739 = 1792109) B1792109
theorem B1792769 : Blo 1194414 1792769 := bstep (se 2 (by rfl) ⟨672288, by rfl⟩ : syracuseStep 1792769 = 1344577) B1344577
theorem B1194755 : Blo 1194414 1194755 := bstep (se 1 (by rfl) ⟨896066, by rfl⟩ : syracuseStep 1194755 = 1792133) B1792133
theorem B3635981 : Blo 1194414 3635981 := bstep (se 3 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 3635981 = 1363493) B1363493
theorem B1194771 : Blo 1194414 1194771 := bstep (se 1 (by rfl) ⟨896078, by rfl⟩ : syracuseStep 1194771 = 1792157) B1792157
theorem B1792787 : Blo 1194414 1792787 := bstep (se 1 (by rfl) ⟨1344590, by rfl⟩ : syracuseStep 1792787 = 2689181) B2689181
theorem B1194787 : Blo 1194414 1194787 := bstep (se 1 (by rfl) ⟨896090, by rfl⟩ : syracuseStep 1194787 = 1792181) B1792181
theorem B6052643 : Blo 1194414 6052643 := bstep (se 1 (by rfl) ⟨4539482, by rfl⟩ : syracuseStep 6052643 = 9078965) B9078965
theorem B1792817 : Blo 1194414 1792817 := bstep (se 2 (by rfl) ⟨672306, by rfl⟩ : syracuseStep 1792817 = 1344613) B1344613
theorem B1194803 : Blo 1194414 1194803 := bstep (se 1 (by rfl) ⟨896102, by rfl⟩ : syracuseStep 1194803 = 1792205) B1792205
theorem B1194819 : Blo 1194414 1194819 := bstep (se 1 (by rfl) ⟨896114, by rfl⟩ : syracuseStep 1194819 = 1792229) B1792229
theorem B1792835 : Blo 1194414 1792835 := bstep (se 1 (by rfl) ⟨1344626, by rfl⟩ : syracuseStep 1792835 = 2689253) B2689253
theorem B8616773 : Blo 1194414 8616773 := bstep (se 4 (by rfl) ⟨807822, by rfl⟩ : syracuseStep 8616773 = 1615645) B1615645
theorem B13998917 : Blo 1194414 13998917 := bstep (se 4 (by rfl) ⟨1312398, by rfl⟩ : syracuseStep 13998917 = 2624797) B2624797
theorem B1194835 : Blo 1194414 1194835 := bstep (se 1 (by rfl) ⟨896126, by rfl⟩ : syracuseStep 1194835 = 1792253) B1792253
theorem B1702739 : Blo 1194414 1702739 := bstep (se 1 (by rfl) ⟨1277054, by rfl⟩ : syracuseStep 1702739 = 2554109) B2554109
theorem B1792865 : Blo 1194414 1792865 := bstep (se 2 (by rfl) ⟨672324, by rfl⟩ : syracuseStep 1792865 = 1344649) B1344649
theorem B1194851 : Blo 1194414 1194851 := bstep (se 1 (by rfl) ⟨896138, by rfl⟩ : syracuseStep 1194851 = 1792277) B1792277
theorem B16169827 : Blo 1194414 16169827 := bstep (se 1 (by rfl) ⟨12127370, by rfl⟩ : syracuseStep 16169827 = 24254741) B24254741
theorem B1194867 : Blo 1194414 1194867 := bstep (se 1 (by rfl) ⟨896150, by rfl⟩ : syracuseStep 1194867 = 1792301) B1792301
theorem B1792883 : Blo 1194414 1792883 := bstep (se 1 (by rfl) ⟨1344662, by rfl⟩ : syracuseStep 1792883 = 2689325) B2689325
theorem B1194883 : Blo 1194414 1194883 := bstep (se 1 (by rfl) ⟨896162, by rfl⟩ : syracuseStep 1194883 = 1792325) B1792325
theorem B5102477 : Blo 1194414 5102477 := bstep (se 3 (by rfl) ⟨956714, by rfl⟩ : syracuseStep 5102477 = 1913429) B1913429
theorem B1792913 : Blo 1194414 1792913 := bstep (se 2 (by rfl) ⟨672342, by rfl⟩ : syracuseStep 1792913 = 1344685) B1344685
theorem B1194899 : Blo 1194414 1194899 := bstep (se 1 (by rfl) ⟨896174, by rfl⟩ : syracuseStep 1194899 = 1792349) B1792349
theorem B1194915 : Blo 1194414 1194915 := bstep (se 1 (by rfl) ⟨896186, by rfl⟩ : syracuseStep 1194915 = 1792373) B1792373
theorem B1792931 : Blo 1194414 1792931 := bstep (se 1 (by rfl) ⟨1344698, by rfl⟩ : syracuseStep 1792931 = 2689397) B2689397
theorem B1702819 : Blo 1194414 1702819 := bstep (se 1 (by rfl) ⟨1277114, by rfl⟩ : syracuseStep 1702819 = 2554229) B2554229
theorem B1194931 : Blo 1194414 1194931 := bstep (se 1 (by rfl) ⟨896198, by rfl⟩ : syracuseStep 1194931 = 1792397) B1792397
theorem B1792961 : Blo 1194414 1792961 := bstep (se 2 (by rfl) ⟨672360, by rfl⟩ : syracuseStep 1792961 = 1344721) B1344721
theorem B1194947 : Blo 1194414 1194947 := bstep (se 1 (by rfl) ⟨896210, by rfl⟩ : syracuseStep 1194947 = 1792421) B1792421
theorem B27958213 : Blo 1194414 27958213 := bstep (se 4 (by rfl) ⟨2621082, by rfl⟩ : syracuseStep 27958213 = 5242165) B5242165
theorem B2587601 : Blo 1194414 2587601 := bstep (se 2 (by rfl) ⟨970350, by rfl⟩ : syracuseStep 2587601 = 1940701) B1940701
theorem B1194963 : Blo 1194414 1194963 := bstep (se 1 (by rfl) ⟨896222, by rfl⟩ : syracuseStep 1194963 = 1792445) B1792445
theorem B1792979 : Blo 1194414 1792979 := bstep (se 1 (by rfl) ⟨1344734, by rfl⟩ : syracuseStep 1792979 = 2689469) B2689469
theorem B1194979 : Blo 1194414 1194979 := bstep (se 1 (by rfl) ⟨896234, by rfl⟩ : syracuseStep 1194979 = 1792469) B1792469
theorem B1793009 : Blo 1194414 1793009 := bstep (se 2 (by rfl) ⟨672378, by rfl⟩ : syracuseStep 1793009 = 1344757) B1344757
theorem B1194995 : Blo 1194414 1194995 := bstep (se 1 (by rfl) ⟨896246, by rfl⟩ : syracuseStep 1194995 = 1792493) B1792493
theorem B1195011 : Blo 1194414 1195011 := bstep (se 1 (by rfl) ⟨896258, by rfl⟩ : syracuseStep 1195011 = 1792517) B1792517
theorem B1793027 : Blo 1194414 1793027 := bstep (se 1 (by rfl) ⟨1344770, by rfl⟩ : syracuseStep 1793027 = 2689541) B2689541
theorem B1276931 : Blo 1194414 1276931 := bstep (se 1 (by rfl) ⟨957698, by rfl⟩ : syracuseStep 1276931 = 1915397) B1915397
theorem B7658509 : Blo 1194414 7658509 := bstep (se 3 (by rfl) ⟨1435970, by rfl⟩ : syracuseStep 7658509 = 2871941) B2871941
theorem B1195027 : Blo 1194414 1195027 := bstep (se 1 (by rfl) ⟨896270, by rfl⟩ : syracuseStep 1195027 = 1792541) B1792541
theorem B1793057 : Blo 1194414 1793057 := bstep (se 2 (by rfl) ⟨672396, by rfl⟩ : syracuseStep 1793057 = 1344793) B1344793
theorem B1195043 : Blo 1194414 1195043 := bstep (se 1 (by rfl) ⟨896282, by rfl⟩ : syracuseStep 1195043 = 1792565) B1792565
theorem B1195059 : Blo 1194414 1195059 := bstep (se 1 (by rfl) ⟨896294, by rfl⟩ : syracuseStep 1195059 = 1792589) B1792589
theorem B1793075 : Blo 1194414 1793075 := bstep (se 1 (by rfl) ⟨1344806, by rfl⟩ : syracuseStep 1793075 = 2689613) B2689613
theorem B1195075 : Blo 1194414 1195075 := bstep (se 1 (by rfl) ⟨896306, by rfl⟩ : syracuseStep 1195075 = 1792613) B1792613
theorem B4086865 : Blo 1194414 4086865 := bstep (se 2 (by rfl) ⟨1532574, by rfl⟩ : syracuseStep 4086865 = 3065149) B3065149
theorem B1793105 : Blo 1194414 1793105 := bstep (se 2 (by rfl) ⟨672414, by rfl⟩ : syracuseStep 1793105 = 1344829) B1344829
theorem B1195091 : Blo 1194414 1195091 := bstep (se 1 (by rfl) ⟨896318, by rfl⟩ : syracuseStep 1195091 = 1792637) B1792637
theorem B1195107 : Blo 1194414 1195107 := bstep (se 1 (by rfl) ⟨896330, by rfl⟩ : syracuseStep 1195107 = 1792661) B1792661
theorem B1793123 : Blo 1194414 1793123 := bstep (se 1 (by rfl) ⟨1344842, by rfl⟩ : syracuseStep 1793123 = 2689685) B2689685
theorem B4037741 : Blo 1194414 4037741 := bstep (se 3 (by rfl) ⟨757076, by rfl⟩ : syracuseStep 4037741 = 1514153) B1514153
theorem B1916017 : Blo 1194414 1916017 := bstep (se 2 (by rfl) ⟨718506, by rfl⟩ : syracuseStep 1916017 = 1437013) B1437013
theorem B1195123 : Blo 1194414 1195123 := bstep (se 1 (by rfl) ⟨896342, by rfl⟩ : syracuseStep 1195123 = 1792685) B1792685
theorem B1793153 : Blo 1194414 1793153 := bstep (se 2 (by rfl) ⟨672432, by rfl⟩ : syracuseStep 1793153 = 1344865) B1344865
theorem B1195139 : Blo 1194414 1195139 := bstep (se 1 (by rfl) ⟨896354, by rfl⟩ : syracuseStep 1195139 = 1792709) B1792709
theorem B1195155 : Blo 1194414 1195155 := bstep (se 1 (by rfl) ⟨896366, by rfl⟩ : syracuseStep 1195155 = 1792733) B1792733
theorem B1793171 : Blo 1194414 1793171 := bstep (se 1 (by rfl) ⟨1344878, by rfl⟩ : syracuseStep 1793171 = 2689757) B2689757
theorem B1195171 : Blo 1194414 1195171 := bstep (se 1 (by rfl) ⟨896378, by rfl⟩ : syracuseStep 1195171 = 1792757) B1792757
theorem B4037795 : Blo 1194414 4037795 := bstep (se 1 (by rfl) ⟨3028346, by rfl⟩ : syracuseStep 4037795 = 6056693) B6056693
theorem B2268337 : Blo 1194414 2268337 := bstep (se 2 (by rfl) ⟨850626, by rfl⟩ : syracuseStep 2268337 = 1701253) B1701253
theorem B1793201 : Blo 1194414 1793201 := bstep (se 2 (by rfl) ⟨672450, by rfl⟩ : syracuseStep 1793201 = 1344901) B1344901
theorem B1195187 : Blo 1194414 1195187 := bstep (se 1 (by rfl) ⟨896390, by rfl⟩ : syracuseStep 1195187 = 1792781) B1792781
theorem B1195203 : Blo 1194414 1195203 := bstep (se 1 (by rfl) ⟨896402, by rfl⟩ : syracuseStep 1195203 = 1792805) B1792805
theorem B1793219 : Blo 1194414 1793219 := bstep (se 1 (by rfl) ⟨1344914, by rfl⟩ : syracuseStep 1793219 = 2689829) B2689829
theorem B1195219 : Blo 1194414 1195219 := bstep (se 1 (by rfl) ⟨896414, by rfl⟩ : syracuseStep 1195219 = 1792829) B1792829
theorem B1793249 : Blo 1194414 1793249 := bstep (se 2 (by rfl) ⟨672468, by rfl⟩ : syracuseStep 1793249 = 1344937) B1344937
theorem B1195235 : Blo 1194414 1195235 := bstep (se 1 (by rfl) ⟨896426, by rfl⟩ : syracuseStep 1195235 = 1792853) B1792853
theorem B1195251 : Blo 1194414 1195251 := bstep (se 1 (by rfl) ⟨896438, by rfl⟩ : syracuseStep 1195251 = 1792877) B1792877
theorem B1793267 : Blo 1194414 1793267 := bstep (se 1 (by rfl) ⟨1344950, by rfl⟩ : syracuseStep 1793267 = 2689901) B2689901
theorem B1195267 : Blo 1194414 1195267 := bstep (se 1 (by rfl) ⟨896450, by rfl⟩ : syracuseStep 1195267 = 1792901) B1792901
theorem B15310093 : Blo 1194414 15310093 := bstep (se 3 (by rfl) ⟨2870642, by rfl⟩ : syracuseStep 15310093 = 5741285) B5741285
theorem B1793297 : Blo 1194414 1793297 := bstep (se 2 (by rfl) ⟨672486, by rfl⟩ : syracuseStep 1793297 = 1344973) B1344973
theorem B1195283 : Blo 1194414 1195283 := bstep (se 1 (by rfl) ⟨896462, by rfl⟩ : syracuseStep 1195283 = 1792925) B1792925
theorem B1195299 : Blo 1194414 1195299 := bstep (se 1 (by rfl) ⟨896474, by rfl⟩ : syracuseStep 1195299 = 1792949) B1792949
theorem B1793315 : Blo 1194414 1793315 := bstep (se 1 (by rfl) ⟨1344986, by rfl⟩ : syracuseStep 1793315 = 2689973) B2689973
theorem B1195315 : Blo 1194414 1195315 := bstep (se 1 (by rfl) ⟨896486, by rfl⟩ : syracuseStep 1195315 = 1792973) B1792973
theorem B1793345 : Blo 1194414 1793345 := bstep (se 2 (by rfl) ⟨672504, by rfl⟩ : syracuseStep 1793345 = 1345009) B1345009
theorem B1195331 : Blo 1194414 1195331 := bstep (se 1 (by rfl) ⟨896498, by rfl⟩ : syracuseStep 1195331 = 1792997) B1792997
theorem B3546449 : Blo 1194414 3546449 := bstep (se 2 (by rfl) ⟨1329918, by rfl⟩ : syracuseStep 3546449 = 2659837) B2659837
theorem B1195347 : Blo 1194414 1195347 := bstep (se 1 (by rfl) ⟨896510, by rfl⟩ : syracuseStep 1195347 = 1793021) B1793021
theorem B1793363 : Blo 1194414 1793363 := bstep (se 1 (by rfl) ⟨1345022, by rfl⟩ : syracuseStep 1793363 = 2690045) B2690045
theorem B1195363 : Blo 1194414 1195363 := bstep (se 1 (by rfl) ⟨896522, by rfl⟩ : syracuseStep 1195363 = 1793045) B1793045
theorem B1793393 : Blo 1194414 1793393 := bstep (se 2 (by rfl) ⟨672522, by rfl⟩ : syracuseStep 1793393 = 1345045) B1345045
theorem B1195379 : Blo 1194414 1195379 := bstep (se 1 (by rfl) ⟨896534, by rfl⟩ : syracuseStep 1195379 = 1793069) B1793069
theorem B1195395 : Blo 1194414 1195395 := bstep (se 1 (by rfl) ⟨896546, by rfl⟩ : syracuseStep 1195395 = 1793093) B1793093
theorem B1793411 : Blo 1194414 1793411 := bstep (se 1 (by rfl) ⟨1345058, by rfl⟩ : syracuseStep 1793411 = 2690117) B2690117
theorem B1195411 : Blo 1194414 1195411 := bstep (se 1 (by rfl) ⟨896558, by rfl⟩ : syracuseStep 1195411 = 1793117) B1793117
theorem B1793441 : Blo 1194414 1793441 := bstep (se 2 (by rfl) ⟨672540, by rfl⟩ : syracuseStep 1793441 = 1345081) B1345081
theorem B1195427 : Blo 1194414 1195427 := bstep (se 1 (by rfl) ⟨896570, by rfl⟩ : syracuseStep 1195427 = 1793141) B1793141
theorem B1195443 : Blo 1194414 1195443 := bstep (se 1 (by rfl) ⟨896582, by rfl⟩ : syracuseStep 1195443 = 1793165) B1793165
theorem B1793459 : Blo 1194414 1793459 := bstep (se 1 (by rfl) ⟨1345094, by rfl⟩ : syracuseStep 1793459 = 2690189) B2690189
theorem B1195459 : Blo 1194414 1195459 := bstep (se 1 (by rfl) ⟨896594, by rfl⟩ : syracuseStep 1195459 = 1793189) B1793189
theorem B1793489 : Blo 1194414 1793489 := bstep (se 2 (by rfl) ⟨672558, by rfl⟩ : syracuseStep 1793489 = 1345117) B1345117
theorem B1703377 : Blo 1194414 1703377 := bstep (se 2 (by rfl) ⟨638766, by rfl⟩ : syracuseStep 1703377 = 1277533) B1277533
theorem B1195475 : Blo 1194414 1195475 := bstep (se 1 (by rfl) ⟨896606, by rfl⟩ : syracuseStep 1195475 = 1793213) B1793213
theorem B1195491 : Blo 1194414 1195491 := bstep (se 1 (by rfl) ⟨896618, by rfl⟩ : syracuseStep 1195491 = 1793237) B1793237
theorem B1793507 : Blo 1194414 1793507 := bstep (se 1 (by rfl) ⟨1345130, by rfl⟩ : syracuseStep 1793507 = 2690261) B2690261
theorem B1195507 : Blo 1194414 1195507 := bstep (se 1 (by rfl) ⟨896630, by rfl⟩ : syracuseStep 1195507 = 1793261) B1793261
theorem B1793537 : Blo 1194414 1793537 := bstep (se 2 (by rfl) ⟨672576, by rfl⟩ : syracuseStep 1793537 = 1345153) B1345153
theorem B1195523 : Blo 1194414 1195523 := bstep (se 1 (by rfl) ⟨896642, by rfl⟩ : syracuseStep 1195523 = 1793285) B1793285
theorem B3276301 : Blo 1194414 3276301 := bstep (se 3 (by rfl) ⟨614306, by rfl⟩ : syracuseStep 3276301 = 1228613) B1228613
theorem B1195539 : Blo 1194414 1195539 := bstep (se 1 (by rfl) ⟨896654, by rfl⟩ : syracuseStep 1195539 = 1793309) B1793309
theorem B1793555 : Blo 1194414 1793555 := bstep (se 1 (by rfl) ⟨1345166, by rfl⟩ : syracuseStep 1793555 = 2690333) B2690333
theorem B1195555 : Blo 1194414 1195555 := bstep (se 1 (by rfl) ⟨896666, by rfl⟩ : syracuseStep 1195555 = 1793333) B1793333
theorem B1793585 : Blo 1194414 1793585 := bstep (se 2 (by rfl) ⟨672594, by rfl⟩ : syracuseStep 1793585 = 1345189) B1345189
theorem B1195571 : Blo 1194414 1195571 := bstep (se 1 (by rfl) ⟨896678, by rfl⟩ : syracuseStep 1195571 = 1793357) B1793357
theorem B2268739 : Blo 1194414 2268739 := bstep (se 1 (by rfl) ⟨1701554, by rfl⟩ : syracuseStep 2268739 = 3403109) B3403109
theorem B1195587 : Blo 1194414 1195587 := bstep (se 1 (by rfl) ⟨896690, by rfl⟩ : syracuseStep 1195587 = 1793381) B1793381
theorem B1793603 : Blo 1194414 1793603 := bstep (se 1 (by rfl) ⟨1345202, by rfl⟩ : syracuseStep 1793603 = 2690405) B2690405
theorem B6053453 : Blo 1194414 6053453 := bstep (se 3 (by rfl) ⟨1135022, by rfl⟩ : syracuseStep 6053453 = 2270045) B2270045
theorem B1195603 : Blo 1194414 1195603 := bstep (se 1 (by rfl) ⟨896702, by rfl⟩ : syracuseStep 1195603 = 1793405) B1793405
theorem B1793633 : Blo 1194414 1793633 := bstep (se 2 (by rfl) ⟨672612, by rfl⟩ : syracuseStep 1793633 = 1345225) B1345225
theorem B1195619 : Blo 1194414 1195619 := bstep (se 1 (by rfl) ⟨896714, by rfl⟩ : syracuseStep 1195619 = 1793429) B1793429
theorem B7274083 : Blo 1194414 7274083 := bstep (se 1 (by rfl) ⟨5455562, by rfl⟩ : syracuseStep 7274083 = 10911125) B10911125
theorem B2268785 : Blo 1194414 2268785 := bstep (se 2 (by rfl) ⟨850794, by rfl⟩ : syracuseStep 2268785 = 1701589) B1701589
theorem B1195635 : Blo 1194414 1195635 := bstep (se 1 (by rfl) ⟨896726, by rfl⟩ : syracuseStep 1195635 = 1793453) B1793453
theorem B1793651 : Blo 1194414 1793651 := bstep (se 1 (by rfl) ⟨1345238, by rfl⟩ : syracuseStep 1793651 = 2690477) B2690477
theorem B1195651 : Blo 1194414 1195651 := bstep (se 1 (by rfl) ⟨896738, by rfl⟩ : syracuseStep 1195651 = 1793477) B1793477
theorem B2301571 : Blo 1194414 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B1793681 : Blo 1194414 1793681 := bstep (se 2 (by rfl) ⟨672630, by rfl⟩ : syracuseStep 1793681 = 1345261) B1345261
theorem B1195667 : Blo 1194414 1195667 := bstep (se 1 (by rfl) ⟨896750, by rfl⟩ : syracuseStep 1195667 = 1793501) B1793501
theorem B1195683 : Blo 1194414 1195683 := bstep (se 1 (by rfl) ⟨896762, by rfl⟩ : syracuseStep 1195683 = 1793525) B1793525
theorem B1793699 : Blo 1194414 1793699 := bstep (se 1 (by rfl) ⟨1345274, by rfl⟩ : syracuseStep 1793699 = 2690549) B2690549
theorem B1195699 : Blo 1194414 1195699 := bstep (se 1 (by rfl) ⟨896774, by rfl⟩ : syracuseStep 1195699 = 1793549) B1793549
theorem B1793729 : Blo 1194414 1793729 := bstep (se 2 (by rfl) ⟨672648, by rfl⟩ : syracuseStep 1793729 = 1345297) B1345297
theorem B1195715 : Blo 1194414 1195715 := bstep (se 1 (by rfl) ⟨896786, by rfl⟩ : syracuseStep 1195715 = 1793573) B1793573
theorem B1195731 : Blo 1194414 1195731 := bstep (se 1 (by rfl) ⟨896798, by rfl⟩ : syracuseStep 1195731 = 1793597) B1793597
theorem B1793747 : Blo 1194414 1793747 := bstep (se 1 (by rfl) ⟨1345310, by rfl⟩ : syracuseStep 1793747 = 2690621) B2690621
theorem B1195747 : Blo 1194414 1195747 := bstep (se 1 (by rfl) ⟨896810, by rfl⟩ : syracuseStep 1195747 = 1793621) B1793621
theorem B1793777 : Blo 1194414 1793777 := bstep (se 2 (by rfl) ⟨672666, by rfl⟩ : syracuseStep 1793777 = 1345333) B1345333
theorem B1195763 : Blo 1194414 1195763 := bstep (se 1 (by rfl) ⟨896822, by rfl⟩ : syracuseStep 1195763 = 1793645) B1793645
theorem B1195779 : Blo 1194414 1195779 := bstep (se 1 (by rfl) ⟨896834, by rfl⟩ : syracuseStep 1195779 = 1793669) B1793669
theorem B1793795 : Blo 1194414 1793795 := bstep (se 1 (by rfl) ⟨1345346, by rfl⟩ : syracuseStep 1793795 = 2690693) B2690693
theorem B1195795 : Blo 1194414 1195795 := bstep (se 1 (by rfl) ⟨896846, by rfl⟩ : syracuseStep 1195795 = 1793693) B1793693
theorem B1793825 : Blo 1194414 1793825 := bstep (se 2 (by rfl) ⟨672684, by rfl⟩ : syracuseStep 1793825 = 1345369) B1345369
theorem B1195811 : Blo 1194414 1195811 := bstep (se 1 (by rfl) ⟨896858, by rfl⟩ : syracuseStep 1195811 = 1793717) B1793717
theorem B1195827 : Blo 1194414 1195827 := bstep (se 1 (by rfl) ⟨896870, by rfl⟩ : syracuseStep 1195827 = 1793741) B1793741
theorem B1793843 : Blo 1194414 1793843 := bstep (se 1 (by rfl) ⟨1345382, by rfl⟩ : syracuseStep 1793843 = 2690765) B2690765
theorem B1195843 : Blo 1194414 1195843 := bstep (se 1 (by rfl) ⟨896882, by rfl⟩ : syracuseStep 1195843 = 1793765) B1793765
theorem B1793873 : Blo 1194414 1793873 := bstep (se 2 (by rfl) ⟨672702, by rfl⟩ : syracuseStep 1793873 = 1345405) B1345405
theorem B1195859 : Blo 1194414 1195859 := bstep (se 1 (by rfl) ⟨896894, by rfl⟩ : syracuseStep 1195859 = 1793789) B1793789
theorem B4308835 : Blo 1194414 4308835 := bstep (se 1 (by rfl) ⟨3231626, by rfl⟩ : syracuseStep 4308835 = 6463253) B6463253
theorem B1195875 : Blo 1194414 1195875 := bstep (se 1 (by rfl) ⟨896906, by rfl⟩ : syracuseStep 1195875 = 1793813) B1793813
theorem B1793891 : Blo 1194414 1793891 := bstep (se 1 (by rfl) ⟨1345418, by rfl⟩ : syracuseStep 1793891 = 2690837) B2690837
theorem B1195891 : Blo 1194414 1195891 := bstep (se 1 (by rfl) ⟨896918, by rfl⟩ : syracuseStep 1195891 = 1793837) B1793837
theorem B1793921 : Blo 1194414 1793921 := bstep (se 2 (by rfl) ⟨672720, by rfl⟩ : syracuseStep 1793921 = 1345441) B1345441
theorem B1195907 : Blo 1194414 1195907 := bstep (se 1 (by rfl) ⟨896930, by rfl⟩ : syracuseStep 1195907 = 1793861) B1793861
theorem B2269073 : Blo 1194414 2269073 := bstep (se 2 (by rfl) ⟨850902, by rfl⟩ : syracuseStep 2269073 = 1701805) B1701805
theorem B1195923 : Blo 1194414 1195923 := bstep (se 1 (by rfl) ⟨896942, by rfl⟩ : syracuseStep 1195923 = 1793885) B1793885
theorem B1793939 : Blo 1194414 1793939 := bstep (se 1 (by rfl) ⟨1345454, by rfl⟩ : syracuseStep 1793939 = 2690909) B2690909
theorem B1195939 : Blo 1194414 1195939 := bstep (se 1 (by rfl) ⟨896954, by rfl⟩ : syracuseStep 1195939 = 1793909) B1793909
theorem B1793969 : Blo 1194414 1793969 := bstep (se 2 (by rfl) ⟨672738, by rfl⟩ : syracuseStep 1793969 = 1345477) B1345477
theorem B1195955 : Blo 1194414 1195955 := bstep (se 1 (by rfl) ⟨896966, by rfl⟩ : syracuseStep 1195955 = 1793933) B1793933
theorem B1195971 : Blo 1194414 1195971 := bstep (se 1 (by rfl) ⟨896978, by rfl⟩ : syracuseStep 1195971 = 1793957) B1793957
theorem B1793987 : Blo 1194414 1793987 := bstep (se 1 (by rfl) ⟨1345490, by rfl⟩ : syracuseStep 1793987 = 2690981) B2690981
theorem B1195987 : Blo 1194414 1195987 := bstep (se 1 (by rfl) ⟨896990, by rfl⟩ : syracuseStep 1195987 = 1793981) B1793981
theorem B1794017 : Blo 1194414 1794017 := bstep (se 2 (by rfl) ⟨672756, by rfl⟩ : syracuseStep 1794017 = 1345513) B1345513
theorem B1196003 : Blo 1194414 1196003 := bstep (se 1 (by rfl) ⟨897002, by rfl⟩ : syracuseStep 1196003 = 1794005) B1794005
theorem B1196019 : Blo 1194414 1196019 := bstep (se 1 (by rfl) ⟨897014, by rfl⟩ : syracuseStep 1196019 = 1794029) B1794029
theorem B1794035 : Blo 1194414 1794035 := bstep (se 1 (by rfl) ⟨1345526, by rfl⟩ : syracuseStep 1794035 = 2691053) B2691053
theorem B1794059 : Blo 1194414 1794059 := bstep (se 1 (by rfl) ⟨1345544, by rfl⟩ : syracuseStep 1794059 = 2691089) B2691089
theorem B1196043 : Blo 1194414 1196043 := bstep (se 1 (by rfl) ⟨897032, by rfl⟩ : syracuseStep 1196043 = 1794065) B1794065
theorem B1794071 : Blo 1194414 1794071 := bstep (se 1 (by rfl) ⟨1345553, by rfl⟩ : syracuseStep 1794071 = 2691107) B2691107
theorem B1196055 : Blo 1194414 1196055 := bstep (se 1 (by rfl) ⟨897041, by rfl⟩ : syracuseStep 1196055 = 1794083) B1794083
theorem B1196075 : Blo 1194414 1196075 := bstep (se 1 (by rfl) ⟨897056, by rfl⟩ : syracuseStep 1196075 = 1794113) B1794113
theorem B1196087 : Blo 1194414 1196087 := bstep (se 1 (by rfl) ⟨897065, by rfl⟩ : syracuseStep 1196087 = 1794131) B1794131
theorem B15319115 : Blo 1194414 15319115 := bstep (se 1 (by rfl) ⟨11489336, by rfl⟩ : syracuseStep 15319115 = 22978673) B22978673
theorem B22986827 : Blo 1194414 22986827 := bstep (se 1 (by rfl) ⟨17240120, by rfl⟩ : syracuseStep 22986827 = 34480241) B34480241
theorem B1196107 : Blo 1194414 1196107 := bstep (se 1 (by rfl) ⟨897080, by rfl⟩ : syracuseStep 1196107 = 1794161) B1794161
theorem B2269271 : Blo 1194414 2269271 := bstep (se 1 (by rfl) ⟨1701953, by rfl⟩ : syracuseStep 2269271 = 3403907) B3403907
theorem B1196119 : Blo 1194414 1196119 := bstep (se 1 (by rfl) ⟨897089, by rfl⟩ : syracuseStep 1196119 = 1794179) B1794179
theorem B1794137 : Blo 1194414 1794137 := bstep (se 2 (by rfl) ⟨672801, by rfl⟩ : syracuseStep 1794137 = 1345603) B1345603
theorem B1196139 : Blo 1194414 1196139 := bstep (se 1 (by rfl) ⟨897104, by rfl⟩ : syracuseStep 1196139 = 1794209) B1794209
theorem B1196151 : Blo 1194414 1196151 := bstep (se 1 (by rfl) ⟨897113, by rfl⟩ : syracuseStep 1196151 = 1794227) B1794227
theorem B1196171 : Blo 1194414 1196171 := bstep (se 1 (by rfl) ⟨897128, by rfl⟩ : syracuseStep 1196171 = 1794257) B1794257
theorem B1196183 : Blo 1194414 1196183 := bstep (se 1 (by rfl) ⟨897137, by rfl⟩ : syracuseStep 1196183 = 1794275) B1794275
theorem B1196203 : Blo 1194414 1196203 := bstep (se 1 (by rfl) ⟨897152, by rfl⟩ : syracuseStep 1196203 = 1794305) B1794305
theorem B8609969 : Blo 1194414 8609969 := bstep (se 2 (by rfl) ⟨3228738, by rfl⟩ : syracuseStep 8609969 = 6457477) B6457477
theorem B1196215 : Blo 1194414 1196215 := bstep (se 1 (by rfl) ⟨897161, by rfl⟩ : syracuseStep 1196215 = 1794323) B1794323
theorem B2425025 : Blo 1194414 2425025 := bstep (se 2 (by rfl) ⟨909384, by rfl⟩ : syracuseStep 2425025 = 1818769) B1818769
theorem B1794251 : Blo 1194414 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B1196235 : Blo 1194414 1196235 := bstep (se 1 (by rfl) ⟨897176, by rfl⟩ : syracuseStep 1196235 = 1794353) B1794353
theorem B1794263 : Blo 1194414 1794263 := bstep (se 1 (by rfl) ⟨1345697, by rfl⟩ : syracuseStep 1794263 = 2691395) B2691395
theorem B1196247 : Blo 1194414 1196247 := bstep (se 1 (by rfl) ⟨897185, by rfl⟩ : syracuseStep 1196247 = 1794371) B1794371
theorem B3735773 : Blo 1194414 3735773 := bstep (se 3 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 3735773 = 1400915) B1400915
theorem B1196267 : Blo 1194414 1196267 := bstep (se 1 (by rfl) ⟨897200, by rfl⟩ : syracuseStep 1196267 = 1794401) B1794401
theorem B1196279 : Blo 1194414 1196279 := bstep (se 1 (by rfl) ⟨897209, by rfl⟩ : syracuseStep 1196279 = 1794419) B1794419
theorem B1196299 : Blo 1194414 1196299 := bstep (se 1 (by rfl) ⟨897224, by rfl⟩ : syracuseStep 1196299 = 1794449) B1794449
theorem B1212683 : Blo 1194414 1212683 := bstep (se 1 (by rfl) ⟨909512, by rfl⟩ : syracuseStep 1212683 = 1819025) B1819025
theorem B1343767 : Blo 1194414 1343767 := bstep (se 1 (by rfl) ⟨1007825, by rfl⟩ : syracuseStep 1343767 = 2015651) B2015651
theorem B1196311 : Blo 1194414 1196311 := bstep (se 1 (by rfl) ⟨897233, by rfl⟩ : syracuseStep 1196311 = 1794467) B1794467
theorem B1794329 : Blo 1194414 1794329 := bstep (se 2 (by rfl) ⟨672873, by rfl⟩ : syracuseStep 1794329 = 1345747) B1345747
theorem B1196331 : Blo 1194414 1196331 := bstep (se 1 (by rfl) ⟨897248, by rfl⟩ : syracuseStep 1196331 = 1794497) B1794497
theorem B1196343 : Blo 1194414 1196343 := bstep (se 1 (by rfl) ⟨897257, by rfl⟩ : syracuseStep 1196343 = 1794515) B1794515
theorem B1196363 : Blo 1194414 1196363 := bstep (se 1 (by rfl) ⟨897272, by rfl⟩ : syracuseStep 1196363 = 1794545) B1794545
theorem B1196375 : Blo 1194414 1196375 := bstep (se 1 (by rfl) ⟨897281, by rfl⟩ : syracuseStep 1196375 = 1794563) B1794563
theorem B2269529 : Blo 1194414 2269529 := bstep (se 2 (by rfl) ⟨851073, by rfl⟩ : syracuseStep 2269529 = 1702147) B1702147
theorem B1196395 : Blo 1194414 1196395 := bstep (se 1 (by rfl) ⟨897296, by rfl⟩ : syracuseStep 1196395 = 1794593) B1794593
theorem B1196407 : Blo 1194414 1196407 := bstep (se 1 (by rfl) ⟨897305, by rfl⟩ : syracuseStep 1196407 = 1794611) B1794611
theorem B10207619 : Blo 1194414 10207619 := bstep (se 1 (by rfl) ⟨7655714, by rfl⟩ : syracuseStep 10207619 = 15311429) B15311429
theorem B1794443 : Blo 1194414 1794443 := bstep (se 1 (by rfl) ⟨1345832, by rfl⟩ : syracuseStep 1794443 = 2691665) B2691665
theorem B1794455 : Blo 1194414 1794455 := bstep (se 1 (by rfl) ⟨1345841, by rfl⟩ : syracuseStep 1794455 = 2691683) B2691683
theorem B2687435 : Blo 1194414 2687435 := bstep (se 1 (by rfl) ⟨2015576, by rfl⟩ : syracuseStep 2687435 = 4031153) B4031153
theorem B1343947 : Blo 1194414 1343947 := bstep (se 1 (by rfl) ⟨1007960, by rfl⟩ : syracuseStep 1343947 = 2015921) B2015921
theorem B2015705 : Blo 1194414 2015705 := bstep (se 2 (by rfl) ⟨755889, by rfl⟩ : syracuseStep 2015705 = 1511779) B1511779
theorem B18407897 : Blo 1194414 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B1794521 : Blo 1194414 1794521 := bstep (se 2 (by rfl) ⟨672945, by rfl⟩ : syracuseStep 1794521 = 1345891) B1345891
theorem B2154995 : Blo 1194414 2154995 := bstep (se 1 (by rfl) ⟨1616246, by rfl⟩ : syracuseStep 2154995 = 3232493) B3232493
theorem B2687489 : Blo 1194414 2687489 := bstep (se 2 (by rfl) ⟨1007808, by rfl⟩ : syracuseStep 2687489 = 2015617) B2015617
theorem B3449395 : Blo 1194414 3449395 := bstep (se 1 (by rfl) ⟨2587046, by rfl⟩ : syracuseStep 3449395 = 5174093) B5174093
theorem B1344055 : Blo 1194414 1344055 := bstep (se 1 (by rfl) ⟨1008041, by rfl⟩ : syracuseStep 1344055 = 2016083) B2016083
theorem B2015833 : Blo 1194414 2015833 := bstep (se 2 (by rfl) ⟨755937, by rfl⟩ : syracuseStep 2015833 = 1511875) B1511875
theorem B2687705 : Blo 1194414 2687705 := bstep (se 2 (by rfl) ⟨1007889, by rfl⟩ : syracuseStep 2687705 = 2015779) B2015779
theorem B1344235 : Blo 1194414 1344235 := bstep (se 1 (by rfl) ⟨1008176, by rfl⟩ : syracuseStep 1344235 = 2016353) B2016353
theorem B2269939 : Blo 1194414 2269939 := bstep (se 1 (by rfl) ⟨1702454, by rfl⟩ : syracuseStep 2269939 = 3404909) B3404909
theorem B3023639 : Blo 1194414 3023639 := bstep (se 1 (by rfl) ⟨2267729, by rfl⟩ : syracuseStep 3023639 = 4535459) B4535459
theorem B2687795 : Blo 1194414 2687795 := bstep (se 1 (by rfl) ⟨2015846, by rfl⟩ : syracuseStep 2687795 = 4031693) B4031693
theorem B2687831 : Blo 1194414 2687831 := bstep (se 1 (by rfl) ⟨2015873, by rfl⟩ : syracuseStep 2687831 = 4031747) B4031747
theorem B1344343 : Blo 1194414 1344343 := bstep (se 1 (by rfl) ⟨1008257, by rfl⟩ : syracuseStep 1344343 = 2016515) B2016515
theorem B6054749 : Blo 1194414 6054749 := bstep (se 3 (by rfl) ⟨1135265, by rfl⟩ : syracuseStep 6054749 = 2270531) B2270531
theorem B22397795 : Blo 1194414 22397795 := bstep (se 1 (by rfl) ⟨16798346, by rfl⟩ : syracuseStep 22397795 = 33596693) B33596693
theorem B2622347 : Blo 1194414 2622347 := bstep (se 1 (by rfl) ⟨1966760, by rfl⟩ : syracuseStep 2622347 = 3933521) B3933521
theorem B5899159 : Blo 1194414 5899159 := bstep (se 1 (by rfl) ⟨4424369, by rfl⟩ : syracuseStep 5899159 = 8848739) B8848739
theorem B2688011 : Blo 1194414 2688011 := bstep (se 1 (by rfl) ⟨2016008, by rfl⟩ : syracuseStep 2688011 = 4032017) B4032017
theorem B1344523 : Blo 1194414 1344523 := bstep (se 1 (by rfl) ⟨1008392, by rfl⟩ : syracuseStep 1344523 = 2016785) B2016785
theorem B2688065 : Blo 1194414 2688065 := bstep (se 2 (by rfl) ⟨1008024, by rfl⟩ : syracuseStep 2688065 = 2016049) B2016049
theorem B1344631 : Blo 1194414 1344631 := bstep (se 1 (by rfl) ⟨1008473, by rfl⟩ : syracuseStep 1344631 = 2016947) B2016947
theorem B4031639 : Blo 1194414 4031639 := bstep (se 1 (by rfl) ⟨3023729, by rfl⟩ : syracuseStep 4031639 = 6047459) B6047459
theorem B2016407 : Blo 1194414 2016407 := bstep (se 1 (by rfl) ⟨1512305, by rfl⟩ : syracuseStep 2016407 = 3024611) B3024611
theorem B2270425 : Blo 1194414 2270425 := bstep (se 2 (by rfl) ⟨851409, by rfl⟩ : syracuseStep 2270425 = 1702819) B1702819
theorem B7374041 : Blo 1194414 7374041 := bstep (se 2 (by rfl) ⟨2765265, by rfl⟩ : syracuseStep 7374041 = 5530531) B5530531
theorem B4539665 : Blo 1194414 4539665 := bstep (se 2 (by rfl) ⟨1702374, by rfl⟩ : syracuseStep 4539665 = 3404749) B3404749
theorem B3065111 : Blo 1194414 3065111 := bstep (se 1 (by rfl) ⟨2298833, by rfl⟩ : syracuseStep 3065111 = 4597667) B4597667
theorem B2016535 : Blo 1194414 2016535 := bstep (se 1 (by rfl) ⟨1512401, by rfl⟩ : syracuseStep 2016535 = 3024803) B3024803
theorem B2688281 : Blo 1194414 2688281 := bstep (se 2 (by rfl) ⟨1008105, by rfl⟩ : syracuseStep 2688281 = 2016211) B2016211
theorem B1344811 : Blo 1194414 1344811 := bstep (se 1 (by rfl) ⟨1008608, by rfl⟩ : syracuseStep 1344811 = 2017217) B2017217
theorem B4310347 : Blo 1194414 4310347 := bstep (se 1 (by rfl) ⟨3232760, by rfl⟩ : syracuseStep 4310347 = 6465521) B6465521
theorem B2688371 : Blo 1194414 2688371 := bstep (se 1 (by rfl) ⟨2016278, by rfl⟩ : syracuseStep 2688371 = 4032557) B4032557
theorem B2688407 : Blo 1194414 2688407 := bstep (se 1 (by rfl) ⟨2016305, by rfl⟩ : syracuseStep 2688407 = 4032611) B4032611
theorem B9823639 : Blo 1194414 9823639 := bstep (se 1 (by rfl) ⟨7367729, by rfl⟩ : syracuseStep 9823639 = 14735459) B14735459
theorem B1344919 : Blo 1194414 1344919 := bstep (se 1 (by rfl) ⟨1008689, by rfl⟩ : syracuseStep 1344919 = 2017379) B2017379
theorem B6047297 : Blo 1194414 6047297 := bstep (se 2 (by rfl) ⟨2267736, by rfl⟩ : syracuseStep 6047297 = 4535473) B4535473
theorem B3024449 : Blo 1194414 3024449 := bstep (se 2 (by rfl) ⟨1134168, by rfl⟩ : syracuseStep 3024449 = 2268337) B2268337
theorem B2688587 : Blo 1194414 2688587 := bstep (se 1 (by rfl) ⟨2016440, by rfl⟩ : syracuseStep 2688587 = 4032881) B4032881
theorem B1345099 : Blo 1194414 1345099 := bstep (se 1 (by rfl) ⟨1008824, by rfl⟩ : syracuseStep 1345099 = 2017649) B2017649
theorem B2688641 : Blo 1194414 2688641 := bstep (se 2 (by rfl) ⟨1008240, by rfl⟩ : syracuseStep 2688641 = 2016481) B2016481
theorem B4032179 : Blo 1194414 4032179 := bstep (se 1 (by rfl) ⟨3024134, by rfl⟩ : syracuseStep 4032179 = 6048269) B6048269
theorem B1345207 : Blo 1194414 1345207 := bstep (se 1 (by rfl) ⟨1008905, by rfl⟩ : syracuseStep 1345207 = 2017811) B2017811
theorem B4540121 : Blo 1194414 4540121 := bstep (se 2 (by rfl) ⟨1702545, by rfl⟩ : syracuseStep 4540121 = 3405091) B3405091
theorem B2270987 : Blo 1194414 2270987 := bstep (se 1 (by rfl) ⟨1703240, by rfl⟩ : syracuseStep 2270987 = 3406481) B3406481
theorem B19384109 : Blo 1194414 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B2688857 : Blo 1194414 2688857 := bstep (se 2 (by rfl) ⟨1008321, by rfl⟩ : syracuseStep 2688857 = 2016643) B2016643
theorem B1345387 : Blo 1194414 1345387 := bstep (se 1 (by rfl) ⟨1009040, by rfl⟩ : syracuseStep 1345387 = 2018081) B2018081
theorem B5744515 : Blo 1194414 5744515 := bstep (se 1 (by rfl) ⟨4308386, by rfl⟩ : syracuseStep 5744515 = 8616773) B8616773
theorem B2017163 : Blo 1194414 2017163 := bstep (se 1 (by rfl) ⟨1512872, by rfl⟩ : syracuseStep 2017163 = 3025745) B3025745
theorem B4540333 : Blo 1194414 4540333 := bstep (se 3 (by rfl) ⟨851312, by rfl⟩ : syracuseStep 4540333 = 1702625) B1702625
theorem B3401651 : Blo 1194414 3401651 := bstep (se 1 (by rfl) ⟨2551238, by rfl⟩ : syracuseStep 3401651 = 5102477) B5102477
theorem B2688947 : Blo 1194414 2688947 := bstep (se 1 (by rfl) ⟨2016710, by rfl⟩ : syracuseStep 2688947 = 4033421) B4033421
theorem B4032449 : Blo 1194414 4032449 := bstep (se 2 (by rfl) ⟨1512168, by rfl⟩ : syracuseStep 4032449 = 3024337) B3024337
theorem B2271169 : Blo 1194414 2271169 := bstep (se 2 (by rfl) ⟨851688, by rfl⟩ : syracuseStep 2271169 = 1703377) B1703377
theorem B2688983 : Blo 1194414 2688983 := bstep (se 1 (by rfl) ⟨2016737, by rfl⟩ : syracuseStep 2688983 = 4033475) B4033475
theorem B1345495 : Blo 1194414 1345495 := bstep (se 1 (by rfl) ⟨1009121, by rfl⟩ : syracuseStep 1345495 = 2018243) B2018243
theorem B2017291 : Blo 1194414 2017291 := bstep (se 1 (by rfl) ⟨1512968, by rfl⟩ : syracuseStep 2017291 = 3025937) B3025937
theorem B4368401 : Blo 1194414 4368401 := bstep (se 2 (by rfl) ⟨1638150, by rfl⟩ : syracuseStep 4368401 = 3276301) B3276301
theorem B3024985 : Blo 1194414 3024985 := bstep (se 2 (by rfl) ⟨1134369, by rfl⟩ : syracuseStep 3024985 = 2268739) B2268739
theorem B2689163 : Blo 1194414 2689163 := bstep (se 1 (by rfl) ⟨2016872, by rfl⟩ : syracuseStep 2689163 = 4033745) B4033745
theorem B1345675 : Blo 1194414 1345675 := bstep (se 1 (by rfl) ⟨1009256, by rfl⟩ : syracuseStep 1345675 = 2018513) B2018513
theorem B2017433 : Blo 1194414 2017433 := bstep (se 2 (by rfl) ⟨756537, by rfl⟩ : syracuseStep 2017433 = 1513075) B1513075
theorem B2689217 : Blo 1194414 2689217 := bstep (se 2 (by rfl) ⟨1008456, by rfl⟩ : syracuseStep 2689217 = 2016913) B2016913
theorem B4540637 : Blo 1194414 4540637 := bstep (se 3 (by rfl) ⟨851369, by rfl⟩ : syracuseStep 4540637 = 1702739) B1702739
theorem B1345783 : Blo 1194414 1345783 := bstep (se 1 (by rfl) ⟨1009337, by rfl⟩ : syracuseStep 1345783 = 2018675) B2018675
theorem B2017561 : Blo 1194414 2017561 := bstep (se 2 (by rfl) ⟨756585, by rfl⟩ : syracuseStep 2017561 = 1513171) B1513171
theorem B2689433 : Blo 1194414 2689433 := bstep (se 2 (by rfl) ⟨1008537, by rfl⟩ : syracuseStep 2689433 = 2017075) B2017075
theorem B1345963 : Blo 1194414 1345963 := bstep (se 1 (by rfl) ⟨1009472, by rfl⟩ : syracuseStep 1345963 = 2018945) B2018945
theorem B5745113 : Blo 1194414 5745113 := bstep (se 2 (by rfl) ⟨2154417, by rfl⟩ : syracuseStep 5745113 = 4308835) B4308835
theorem B4032989 : Blo 1194414 4032989 := bstep (se 3 (by rfl) ⟨756185, by rfl⟩ : syracuseStep 4032989 = 1512371) B1512371
theorem B2689523 : Blo 1194414 2689523 := bstep (se 1 (by rfl) ⟨2017142, by rfl⟩ : syracuseStep 2689523 = 4034285) B4034285
theorem B2689559 : Blo 1194414 2689559 := bstep (se 1 (by rfl) ⟨2017169, by rfl⟩ : syracuseStep 2689559 = 4034339) B4034339
theorem B4311731 : Blo 1194414 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B2689739 : Blo 1194414 2689739 := bstep (se 1 (by rfl) ⟨2017304, by rfl⟩ : syracuseStep 2689739 = 4034609) B4034609
theorem B10210009 : Blo 1194414 10210009 := bstep (se 2 (by rfl) ⟨3828753, by rfl⟩ : syracuseStep 10210009 = 7657507) B7657507
theorem B2689793 : Blo 1194414 2689793 := bstep (se 2 (by rfl) ⟨1008672, by rfl⟩ : syracuseStep 2689793 = 2017345) B2017345
theorem B6458129 : Blo 1194414 6458129 := bstep (se 2 (by rfl) ⟨2421798, by rfl⟩ : syracuseStep 6458129 = 4843597) B4843597
theorem B1362763 : Blo 1194414 1362763 := bstep (se 1 (by rfl) ⟨1022072, by rfl⟩ : syracuseStep 1362763 = 2044145) B2044145
theorem B2018135 : Blo 1194414 2018135 := bstep (se 1 (by rfl) ⟨1513601, by rfl⟩ : syracuseStep 2018135 = 3027203) B3027203
theorem B5106577 : Blo 1194414 5106577 := bstep (se 2 (by rfl) ⟨1914966, by rfl⟩ : syracuseStep 5106577 = 3829933) B3829933
theorem B11045809 : Blo 1194414 11045809 := bstep (se 2 (by rfl) ⟨4142178, by rfl⟩ : syracuseStep 11045809 = 8284357) B8284357
theorem B2018263 : Blo 1194414 2018263 := bstep (se 1 (by rfl) ⟨1513697, by rfl⟩ : syracuseStep 2018263 = 3027395) B3027395
theorem B2690009 : Blo 1194414 2690009 := bstep (se 2 (by rfl) ⟨1008753, by rfl⟩ : syracuseStep 2690009 = 2017507) B2017507
theorem B31075289 : Blo 1194414 31075289 := bstep (se 2 (by rfl) ⟨11653233, by rfl⟩ : syracuseStep 31075289 = 23306467) B23306467
theorem B2690099 : Blo 1194414 2690099 := bstep (se 1 (by rfl) ⟨2017574, by rfl⟩ : syracuseStep 2690099 = 4035149) B4035149
theorem B2690135 : Blo 1194414 2690135 := bstep (se 1 (by rfl) ⟨2017601, by rfl⟩ : syracuseStep 2690135 = 4035203) B4035203
theorem B10906775 : Blo 1194414 10906775 := bstep (se 1 (by rfl) ⟨8180081, by rfl⟩ : syracuseStep 10906775 = 16360163) B16360163
theorem B3026099 : Blo 1194414 3026099 := bstep (se 1 (by rfl) ⟨2269574, by rfl⟩ : syracuseStep 3026099 = 4539149) B4539149
theorem B2870489 : Blo 1194414 2870489 := bstep (se 2 (by rfl) ⟨1076433, by rfl⟩ : syracuseStep 2870489 = 2152867) B2152867
theorem B10218757 : Blo 1194414 10218757 := bstep (se 4 (by rfl) ⟨958008, by rfl⟩ : syracuseStep 10218757 = 1916017) B1916017
theorem B2690315 : Blo 1194414 2690315 := bstep (se 1 (by rfl) ⟨2017736, by rfl⟩ : syracuseStep 2690315 = 4035473) B4035473
theorem B2690369 : Blo 1194414 2690369 := bstep (se 2 (by rfl) ⟨1008888, by rfl⟩ : syracuseStep 2690369 = 2017777) B2017777
theorem B8621387 : Blo 1194414 8621387 := bstep (se 1 (by rfl) ⟨6466040, by rfl⟩ : syracuseStep 8621387 = 12932081) B12932081
theorem B7269725 : Blo 1194414 7269725 := bstep (se 3 (by rfl) ⟨1363073, by rfl⟩ : syracuseStep 7269725 = 2726147) B2726147
theorem B6131123 : Blo 1194414 6131123 := bstep (se 1 (by rfl) ⟨4598342, by rfl⟩ : syracuseStep 6131123 = 9196685) B9196685
theorem B6049241 : Blo 1194414 6049241 := bstep (se 2 (by rfl) ⟨2268465, by rfl⟩ : syracuseStep 6049241 = 4536931) B4536931
theorem B13102553 : Blo 1194414 13102553 := bstep (se 2 (by rfl) ⟨4913457, by rfl⟩ : syracuseStep 13102553 = 9826915) B9826915
theorem B3026393 : Blo 1194414 3026393 := bstep (se 2 (by rfl) ⟨1134897, by rfl⟩ : syracuseStep 3026393 = 2269795) B2269795
theorem B2690585 : Blo 1194414 2690585 := bstep (se 2 (by rfl) ⟨1008969, by rfl⟩ : syracuseStep 2690585 = 2017939) B2017939
theorem B4034123 : Blo 1194414 4034123 := bstep (se 1 (by rfl) ⟨3025592, by rfl⟩ : syracuseStep 4034123 = 6051185) B6051185
theorem B2018891 : Blo 1194414 2018891 := bstep (se 1 (by rfl) ⟨1514168, by rfl⟩ : syracuseStep 2018891 = 3028337) B3028337
theorem B6811229 : Blo 1194414 6811229 := bstep (se 3 (by rfl) ⟨1277105, by rfl⟩ : syracuseStep 6811229 = 2554211) B2554211
theorem B6467165 : Blo 1194414 6467165 := bstep (se 3 (by rfl) ⟨1212593, by rfl⟩ : syracuseStep 6467165 = 2425187) B2425187
theorem B2690675 : Blo 1194414 2690675 := bstep (se 1 (by rfl) ⟨2018006, by rfl⟩ : syracuseStep 2690675 = 4036013) B4036013
theorem B10210967 : Blo 1194414 10210967 := bstep (se 1 (by rfl) ⟨7658225, by rfl⟩ : syracuseStep 10210967 = 15316451) B15316451
theorem B2690711 : Blo 1194414 2690711 := bstep (se 1 (by rfl) ⟨2018033, by rfl⟩ : syracuseStep 2690711 = 4036067) B4036067
theorem B5172929 : Blo 1194414 5172929 := bstep (se 2 (by rfl) ⟨1939848, by rfl⟩ : syracuseStep 5172929 = 3879697) B3879697
theorem B2690891 : Blo 1194414 2690891 := bstep (se 1 (by rfl) ⟨2018168, by rfl⟩ : syracuseStep 2690891 = 4036337) B4036337
theorem B4034393 : Blo 1194414 4034393 := bstep (se 2 (by rfl) ⟨1512897, by rfl⟩ : syracuseStep 4034393 = 3025795) B3025795
theorem B2690945 : Blo 1194414 2690945 := bstep (se 2 (by rfl) ⟨1009104, by rfl⟩ : syracuseStep 2690945 = 2018209) B2018209
theorem B37277617 : Blo 1194414 37277617 := bstep (se 2 (by rfl) ⟨13979106, by rfl⟩ : syracuseStep 37277617 = 27958213) B27958213
theorem B2551819 : Blo 1194414 2551819 := bstep (se 1 (by rfl) ⟨1913864, by rfl⟩ : syracuseStep 2551819 = 3827729) B3827729
theorem B10211345 : Blo 1194414 10211345 := bstep (se 2 (by rfl) ⟨3829254, by rfl⟩ : syracuseStep 10211345 = 7658509) B7658509
theorem B4427821 : Blo 1194414 4427821 := bstep (se 3 (by rfl) ⟨830216, by rfl⟩ : syracuseStep 4427821 = 1660433) B1660433
theorem B2691161 : Blo 1194414 2691161 := bstep (se 2 (by rfl) ⟨1009185, by rfl⟩ : syracuseStep 2691161 = 2018371) B2018371
theorem B13791325 : Blo 1194414 13791325 := bstep (se 3 (by rfl) ⟨2585873, by rfl⟩ : syracuseStep 13791325 = 5171747) B5171747
theorem B2691251 : Blo 1194414 2691251 := bstep (se 1 (by rfl) ⟨2018438, by rfl⟩ : syracuseStep 2691251 = 4036877) B4036877
theorem B2691287 : Blo 1194414 2691287 := bstep (se 1 (by rfl) ⟨2018465, by rfl⟩ : syracuseStep 2691287 = 4036931) B4036931
theorem B2183411 : Blo 1194414 2183411 := bstep (se 1 (by rfl) ⟨1637558, by rfl⟩ : syracuseStep 2183411 = 3275117) B3275117
theorem B2691467 : Blo 1194414 2691467 := bstep (se 1 (by rfl) ⟨2018600, by rfl⟩ : syracuseStep 2691467 = 4037201) B4037201
theorem B2691521 : Blo 1194414 2691521 := bstep (se 2 (by rfl) ⟨1009320, by rfl⟩ : syracuseStep 2691521 = 2018641) B2018641
theorem B2044363 : Blo 1194414 2044363 := bstep (se 1 (by rfl) ⟨1533272, by rfl⟩ : syracuseStep 2044363 = 3066545) B3066545
theorem B4035095 : Blo 1194414 4035095 := bstep (se 1 (by rfl) ⟨3026321, by rfl⟩ : syracuseStep 4035095 = 6052643) B6052643
theorem B3404339 : Blo 1194414 3404339 := bstep (se 1 (by rfl) ⟨2553254, by rfl⟩ : syracuseStep 3404339 = 5106509) B5106509
theorem B1725067 : Blo 1194414 1725067 := bstep (se 1 (by rfl) ⟨1293800, by rfl⟩ : syracuseStep 1725067 = 2587601) B2587601
theorem B2691737 : Blo 1194414 2691737 := bstep (se 2 (by rfl) ⟨1009401, by rfl⟩ : syracuseStep 2691737 = 2018803) B2018803
theorem B2552563 : Blo 1194414 2552563 := bstep (se 1 (by rfl) ⟨1914422, by rfl⟩ : syracuseStep 2552563 = 3828845) B3828845
theorem B2691827 : Blo 1194414 2691827 := bstep (se 1 (by rfl) ⟨2018870, by rfl⟩ : syracuseStep 2691827 = 4037741) B4037741
theorem B3404567 : Blo 1194414 3404567 := bstep (se 1 (by rfl) ⟨2553425, by rfl⟩ : syracuseStep 3404567 = 5106851) B5106851
theorem B2691863 : Blo 1194414 2691863 := bstep (se 1 (by rfl) ⟨2018897, by rfl⟩ : syracuseStep 2691863 = 4037795) B4037795
theorem B3068761 : Blo 1194414 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B2364299 : Blo 1194414 2364299 := bstep (se 1 (by rfl) ⟨1773224, by rfl⟩ : syracuseStep 2364299 = 3546449) B3546449
theorem B2724761 : Blo 1194414 2724761 := bstep (se 2 (by rfl) ⟨1021785, by rfl⟩ : syracuseStep 2724761 = 2043571) B2043571
theorem B4535261 : Blo 1194414 4535261 := bstep (se 3 (by rfl) ⟨850361, by rfl⟩ : syracuseStep 4535261 = 1700723) B1700723
theorem B6050861 : Blo 1194414 6050861 := bstep (se 3 (by rfl) ⟨1134536, by rfl⟩ : syracuseStep 6050861 = 2269073) B2269073
theorem B4035635 : Blo 1194414 4035635 := bstep (se 1 (by rfl) ⟨3026726, by rfl⟩ : syracuseStep 4035635 = 6053453) B6053453
theorem B1512523 : Blo 1194414 1512523 := bstep (se 1 (by rfl) ⟨1134392, by rfl⟩ : syracuseStep 1512523 = 2268785) B2268785
theorem B3404875 : Blo 1194414 3404875 := bstep (se 1 (by rfl) ⟨2553656, by rfl⟩ : syracuseStep 3404875 = 5107313) B5107313
theorem B3028043 : Blo 1194414 3028043 := bstep (se 1 (by rfl) ⟨2271032, by rfl⟩ : syracuseStep 3028043 = 4542065) B4542065
theorem B8623205 : Blo 1194414 8623205 := bstep (se 4 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 8623205 = 1616851) B1616851
theorem B2553049 : Blo 1194414 2553049 := bstep (se 2 (by rfl) ⟨957393, by rfl⟩ : syracuseStep 2553049 = 1914787) B1914787
theorem B5108953 : Blo 1194414 5108953 := bstep (se 2 (by rfl) ⟨1915857, by rfl⟩ : syracuseStep 5108953 = 3831715) B3831715
theorem B4035905 : Blo 1194414 4035905 := bstep (se 2 (by rfl) ⟨1513464, by rfl⟩ : syracuseStep 4035905 = 3026929) B3026929
theorem B3405149 : Blo 1194414 3405149 := bstep (se 3 (by rfl) ⟨638465, by rfl⟩ : syracuseStep 3405149 = 1276931) B1276931
theorem B6387265 : Blo 1194414 6387265 := bstep (se 2 (by rfl) ⟨2395224, by rfl⟩ : syracuseStep 6387265 = 4790449) B4790449
theorem B4535959 : Blo 1194414 4535959 := bstep (se 1 (by rfl) ⟨3401969, by rfl⟩ : syracuseStep 4535959 = 6803939) B6803939
theorem B1791641 : Blo 1194414 1791641 := bstep (se 2 (by rfl) ⟨671865, by rfl⟩ : syracuseStep 1791641 = 1343731) B1343731
theorem B21796613 : Blo 1194414 21796613 := bstep (se 4 (by rfl) ⟨2043432, by rfl⟩ : syracuseStep 21796613 = 4086865) B4086865
theorem B1791755 : Blo 1194414 1791755 := bstep (se 1 (by rfl) ⟨1343816, by rfl⟩ : syracuseStep 1791755 = 2687633) B2687633
theorem B1791767 : Blo 1194414 1791767 := bstep (se 1 (by rfl) ⟨1343825, by rfl⟩ : syracuseStep 1791767 = 2687651) B2687651
theorem B1791833 : Blo 1194414 1791833 := bstep (se 2 (by rfl) ⟨671937, by rfl⟩ : syracuseStep 1791833 = 1343875) B1343875
theorem B4036445 : Blo 1194414 4036445 := bstep (se 3 (by rfl) ⟨756833, by rfl⟩ : syracuseStep 4036445 = 1513667) B1513667
theorem B1791947 : Blo 1194414 1791947 := bstep (se 1 (by rfl) ⟨1343960, by rfl⟩ : syracuseStep 1791947 = 2687921) B2687921
theorem B1791959 : Blo 1194414 1791959 := bstep (se 1 (by rfl) ⟨1343969, by rfl⟩ : syracuseStep 1791959 = 2687939) B2687939
theorem B2299927 : Blo 1194414 2299927 := bstep (se 1 (by rfl) ⟨1724945, by rfl⟩ : syracuseStep 2299927 = 3449891) B3449891
theorem B1513495 : Blo 1194414 1513495 := bstep (se 1 (by rfl) ⟨1135121, by rfl⟩ : syracuseStep 1513495 = 2270243) B2270243
theorem B1792025 : Blo 1194414 1792025 := bstep (se 2 (by rfl) ⟨672009, by rfl⟩ : syracuseStep 1792025 = 1344019) B1344019
theorem B8181805 : Blo 1194414 8181805 := bstep (se 3 (by rfl) ⟨1534088, by rfl⟩ : syracuseStep 8181805 = 3068177) B3068177
theorem B6805579 : Blo 1194414 6805579 := bstep (se 1 (by rfl) ⟨5104184, by rfl⟩ : syracuseStep 6805579 = 10208369) B10208369
theorem B6813827 : Blo 1194414 6813827 := bstep (se 1 (by rfl) ⟨5110370, by rfl⟩ : syracuseStep 6813827 = 10220741) B10220741
theorem B1792139 : Blo 1194414 1792139 := bstep (se 1 (by rfl) ⟨1344104, by rfl⟩ : syracuseStep 1792139 = 2688209) B2688209
theorem B1792151 : Blo 1194414 1792151 := bstep (se 1 (by rfl) ⟨1344113, by rfl⟩ : syracuseStep 1792151 = 2688227) B2688227
theorem B2586775 : Blo 1194414 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B5109911 : Blo 1194414 5109911 := bstep (se 1 (by rfl) ⟨3832433, by rfl⟩ : syracuseStep 5109911 = 7664867) B7664867
theorem B1792217 : Blo 1194414 1792217 := bstep (se 2 (by rfl) ⟨672081, by rfl⟩ : syracuseStep 1792217 = 1344163) B1344163
theorem B1276183 : Blo 1194414 1276183 := bstep (se 1 (by rfl) ⟨957137, by rfl⟩ : syracuseStep 1276183 = 1914275) B1914275
theorem B1915159 : Blo 1194414 1915159 := bstep (se 1 (by rfl) ⟨1436369, by rfl⟩ : syracuseStep 1915159 = 2872739) B2872739
theorem B2488601 : Blo 1194414 2488601 := bstep (se 2 (by rfl) ⟨933225, by rfl⟩ : syracuseStep 2488601 = 1866451) B1866451
theorem B5740865 : Blo 1194414 5740865 := bstep (se 2 (by rfl) ⟨2152824, by rfl⟩ : syracuseStep 5740865 = 4305649) B4305649
theorem B1792331 : Blo 1194414 1792331 := bstep (se 1 (by rfl) ⟨1344248, by rfl⟩ : syracuseStep 1792331 = 2688497) B2688497
theorem B1792343 : Blo 1194414 1792343 := bstep (se 1 (by rfl) ⟨1344257, by rfl⟩ : syracuseStep 1792343 = 2688515) B2688515
theorem B1816921 : Blo 1194414 1816921 := bstep (se 2 (by rfl) ⟨681345, by rfl⟩ : syracuseStep 1816921 = 1362691) B1362691
theorem B6805853 : Blo 1194414 6805853 := bstep (se 3 (by rfl) ⟨1276097, by rfl⟩ : syracuseStep 6805853 = 2552195) B2552195
theorem B8173925 : Blo 1194414 8173925 := bstep (se 4 (by rfl) ⟨766305, by rfl⟩ : syracuseStep 8173925 = 1532611) B1532611
theorem B1792409 : Blo 1194414 1792409 := bstep (se 2 (by rfl) ⟨672153, by rfl⟩ : syracuseStep 1792409 = 1344307) B1344307
theorem B4536749 : Blo 1194414 4536749 := bstep (se 3 (by rfl) ⟨850640, by rfl⟩ : syracuseStep 4536749 = 1701281) B1701281
theorem B12933553 : Blo 1194414 12933553 := bstep (se 2 (by rfl) ⟨4850082, by rfl⟩ : syracuseStep 12933553 = 9700165) B9700165
theorem B1194423 : Blo 1194414 1194423 := bstep (se 1 (by rfl) ⟨895817, by rfl⟩ : syracuseStep 1194423 = 1791635) B1791635
theorem B2267585 : Blo 1194414 2267585 := bstep (se 2 (by rfl) ⟨850344, by rfl⟩ : syracuseStep 2267585 = 1700689) B1700689
theorem B1194443 : Blo 1194414 1194443 := bstep (se 1 (by rfl) ⟨895832, by rfl⟩ : syracuseStep 1194443 = 1791665) B1791665
theorem B1194455 : Blo 1194414 1194455 := bstep (se 1 (by rfl) ⟨895841, by rfl⟩ : syracuseStep 1194455 = 1791683) B1791683
theorem B21559769 : Blo 1194414 21559769 := bstep (se 2 (by rfl) ⟨8084913, by rfl⟩ : syracuseStep 21559769 = 16169827) B16169827
theorem B1194475 : Blo 1194414 1194475 := bstep (se 1 (by rfl) ⟨895856, by rfl⟩ : syracuseStep 1194475 = 1791713) B1791713
theorem B1194487 : Blo 1194414 1194487 := bstep (se 1 (by rfl) ⟨895865, by rfl⟩ : syracuseStep 1194487 = 1791731) B1791731
theorem B1194507 : Blo 1194414 1194507 := bstep (se 1 (by rfl) ⟨895880, by rfl⟩ : syracuseStep 1194507 = 1791761) B1791761
theorem B1792523 : Blo 1194414 1792523 := bstep (se 1 (by rfl) ⟨1344392, by rfl⟩ : syracuseStep 1792523 = 2688785) B2688785
theorem B1194519 : Blo 1194414 1194519 := bstep (se 1 (by rfl) ⟨895889, by rfl⟩ : syracuseStep 1194519 = 1791779) B1791779
theorem B1792535 : Blo 1194414 1792535 := bstep (se 1 (by rfl) ⟨1344401, by rfl⟩ : syracuseStep 1792535 = 2688803) B2688803
theorem B3832343 : Blo 1194414 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B1194539 : Blo 1194414 1194539 := bstep (se 1 (by rfl) ⟨895904, by rfl⟩ : syracuseStep 1194539 = 1791809) B1791809
theorem B1194551 : Blo 1194414 1194551 := bstep (se 1 (by rfl) ⟨895913, by rfl⟩ : syracuseStep 1194551 = 1791827) B1791827
theorem B1194571 : Blo 1194414 1194571 := bstep (se 1 (by rfl) ⟨895928, by rfl⟩ : syracuseStep 1194571 = 1791857) B1791857
theorem B1194583 : Blo 1194414 1194583 := bstep (se 1 (by rfl) ⟨895937, by rfl⟩ : syracuseStep 1194583 = 1791875) B1791875
theorem B1792601 : Blo 1194414 1792601 := bstep (se 2 (by rfl) ⟨672225, by rfl⟩ : syracuseStep 1792601 = 1344451) B1344451
theorem B1194603 : Blo 1194414 1194603 := bstep (se 1 (by rfl) ⟨895952, by rfl⟩ : syracuseStep 1194603 = 1791905) B1791905
theorem B1194615 : Blo 1194414 1194615 := bstep (se 1 (by rfl) ⟨895961, by rfl⟩ : syracuseStep 1194615 = 1791923) B1791923
theorem B1194635 : Blo 1194414 1194635 := bstep (se 1 (by rfl) ⟨895976, by rfl⟩ : syracuseStep 1194635 = 1791953) B1791953
theorem B1276555 : Blo 1194414 1276555 := bstep (se 1 (by rfl) ⟨957416, by rfl⟩ : syracuseStep 1276555 = 1914833) B1914833
theorem B1194647 : Blo 1194414 1194647 := bstep (se 1 (by rfl) ⟨895985, by rfl⟩ : syracuseStep 1194647 = 1791971) B1791971
theorem B2554519 : Blo 1194414 2554519 := bstep (se 1 (by rfl) ⟨1915889, by rfl⟩ : syracuseStep 2554519 = 3831779) B3831779
theorem B1194667 : Blo 1194414 1194667 := bstep (se 1 (by rfl) ⟨896000, by rfl⟩ : syracuseStep 1194667 = 1792001) B1792001
theorem B1194679 : Blo 1194414 1194679 := bstep (se 1 (by rfl) ⟨896009, by rfl⟩ : syracuseStep 1194679 = 1792019) B1792019
theorem B2267851 : Blo 1194414 2267851 := bstep (se 1 (by rfl) ⟨1700888, by rfl⟩ : syracuseStep 2267851 = 3401777) B3401777
theorem B1194699 : Blo 1194414 1194699 := bstep (se 1 (by rfl) ⟨896024, by rfl⟩ : syracuseStep 1194699 = 1792049) B1792049
theorem B1792715 : Blo 1194414 1792715 := bstep (se 1 (by rfl) ⟨1344536, by rfl⟩ : syracuseStep 1792715 = 2689073) B2689073
theorem B2554571 : Blo 1194414 2554571 := bstep (se 1 (by rfl) ⟨1915928, by rfl⟩ : syracuseStep 2554571 = 3831857) B3831857
theorem B1194711 : Blo 1194414 1194711 := bstep (se 1 (by rfl) ⟨896033, by rfl⟩ : syracuseStep 1194711 = 1792067) B1792067
theorem B1792727 : Blo 1194414 1792727 := bstep (se 1 (by rfl) ⟨1344545, by rfl⟩ : syracuseStep 1792727 = 2689091) B2689091
theorem B1915607 : Blo 1194414 1915607 := bstep (se 1 (by rfl) ⟨1436705, by rfl⟩ : syracuseStep 1915607 = 2873411) B2873411
theorem B1194731 : Blo 1194414 1194731 := bstep (se 1 (by rfl) ⟨896048, by rfl⟩ : syracuseStep 1194731 = 1792097) B1792097
theorem B1194743 : Blo 1194414 1194743 := bstep (se 1 (by rfl) ⟨896057, by rfl⟩ : syracuseStep 1194743 = 1792115) B1792115
theorem B1194763 : Blo 1194414 1194763 := bstep (se 1 (by rfl) ⟨896072, by rfl⟩ : syracuseStep 1194763 = 1792145) B1792145
theorem B1194775 : Blo 1194414 1194775 := bstep (se 1 (by rfl) ⟨896081, by rfl⟩ : syracuseStep 1194775 = 1792163) B1792163
theorem B1792793 : Blo 1194414 1792793 := bstep (se 2 (by rfl) ⟨672297, by rfl⟩ : syracuseStep 1792793 = 1344595) B1344595
theorem B1194795 : Blo 1194414 1194795 := bstep (se 1 (by rfl) ⟨896096, by rfl⟩ : syracuseStep 1194795 = 1792193) B1792193
theorem B1194807 : Blo 1194414 1194807 := bstep (se 1 (by rfl) ⟨896105, by rfl⟩ : syracuseStep 1194807 = 1792211) B1792211
theorem B1194827 : Blo 1194414 1194827 := bstep (se 1 (by rfl) ⟨896120, by rfl⟩ : syracuseStep 1194827 = 1792241) B1792241
theorem B1194839 : Blo 1194414 1194839 := bstep (se 1 (by rfl) ⟨896129, by rfl⟩ : syracuseStep 1194839 = 1792259) B1792259
theorem B1194859 : Blo 1194414 1194859 := bstep (se 1 (by rfl) ⟨896144, by rfl⟩ : syracuseStep 1194859 = 1792289) B1792289
theorem B1194871 : Blo 1194414 1194871 := bstep (se 1 (by rfl) ⟨896153, by rfl⟩ : syracuseStep 1194871 = 1792307) B1792307
theorem B1194891 : Blo 1194414 1194891 := bstep (se 1 (by rfl) ⟨896168, by rfl⟩ : syracuseStep 1194891 = 1792337) B1792337
theorem B1792907 : Blo 1194414 1792907 := bstep (se 1 (by rfl) ⟨1344680, by rfl⟩ : syracuseStep 1792907 = 2689361) B2689361
theorem B1915787 : Blo 1194414 1915787 := bstep (se 1 (by rfl) ⟨1436840, by rfl⟩ : syracuseStep 1915787 = 2873681) B2873681
theorem B1194903 : Blo 1194414 1194903 := bstep (se 1 (by rfl) ⟨896177, by rfl⟩ : syracuseStep 1194903 = 1792355) B1792355
theorem B1792919 : Blo 1194414 1792919 := bstep (se 1 (by rfl) ⟨1344689, by rfl⟩ : syracuseStep 1792919 = 2689379) B2689379
theorem B1194923 : Blo 1194414 1194923 := bstep (se 1 (by rfl) ⟨896192, by rfl⟩ : syracuseStep 1194923 = 1792385) B1792385
theorem B9083825 : Blo 1194414 9083825 := bstep (se 2 (by rfl) ⟨3406434, by rfl⟩ : syracuseStep 9083825 = 6812869) B6812869
theorem B1194935 : Blo 1194414 1194935 := bstep (se 1 (by rfl) ⟨896201, by rfl⟩ : syracuseStep 1194935 = 1792403) B1792403
theorem B1194955 : Blo 1194414 1194955 := bstep (se 1 (by rfl) ⟨896216, by rfl⟩ : syracuseStep 1194955 = 1792433) B1792433
theorem B4037579 : Blo 1194414 4037579 := bstep (se 1 (by rfl) ⟨3028184, by rfl⟩ : syracuseStep 4037579 = 6056369) B6056369
theorem B1194967 : Blo 1194414 1194967 := bstep (se 1 (by rfl) ⟨896225, by rfl⟩ : syracuseStep 1194967 = 1792451) B1792451
theorem B1792985 : Blo 1194414 1792985 := bstep (se 2 (by rfl) ⟨672369, by rfl⟩ : syracuseStep 1792985 = 1344739) B1344739
theorem B1194987 : Blo 1194414 1194987 := bstep (se 1 (by rfl) ⟨896240, by rfl⟩ : syracuseStep 1194987 = 1792481) B1792481
theorem B1194999 : Blo 1194414 1194999 := bstep (se 1 (by rfl) ⟨896249, by rfl⟩ : syracuseStep 1194999 = 1792499) B1792499
theorem B1195019 : Blo 1194414 1195019 := bstep (se 1 (by rfl) ⟨896264, by rfl⟩ : syracuseStep 1195019 = 1792529) B1792529
theorem B1915915 : Blo 1194414 1915915 := bstep (se 1 (by rfl) ⟨1436936, by rfl⟩ : syracuseStep 1915915 = 2873873) B2873873
theorem B20413457 : Blo 1194414 20413457 := bstep (se 2 (by rfl) ⟨7655046, by rfl⟩ : syracuseStep 20413457 = 15310093) B15310093
theorem B1195031 : Blo 1194414 1195031 := bstep (se 1 (by rfl) ⟨896273, by rfl⟩ : syracuseStep 1195031 = 1792547) B1792547
theorem B2153495 : Blo 1194414 2153495 := bstep (se 1 (by rfl) ⟨1615121, by rfl⟩ : syracuseStep 2153495 = 3230243) B3230243
theorem B1195051 : Blo 1194414 1195051 := bstep (se 1 (by rfl) ⟨896288, by rfl⟩ : syracuseStep 1195051 = 1792577) B1792577
theorem B1195063 : Blo 1194414 1195063 := bstep (se 1 (by rfl) ⟨896297, by rfl⟩ : syracuseStep 1195063 = 1792595) B1792595
theorem B1195083 : Blo 1194414 1195083 := bstep (se 1 (by rfl) ⟨896312, by rfl⟩ : syracuseStep 1195083 = 1792625) B1792625
theorem B1793099 : Blo 1194414 1793099 := bstep (se 1 (by rfl) ⟨1344824, by rfl⟩ : syracuseStep 1793099 = 2689649) B2689649
theorem B1277003 : Blo 1194414 1277003 := bstep (se 1 (by rfl) ⟨957752, by rfl⟩ : syracuseStep 1277003 = 1915505) B1915505
theorem B1915979 : Blo 1194414 1915979 := bstep (se 1 (by rfl) ⟨1436984, by rfl⟩ : syracuseStep 1915979 = 2873969) B2873969
theorem B1195095 : Blo 1194414 1195095 := bstep (se 1 (by rfl) ⟨896321, by rfl⟩ : syracuseStep 1195095 = 1792643) B1792643
theorem B1793111 : Blo 1194414 1793111 := bstep (se 1 (by rfl) ⟨1344833, by rfl⟩ : syracuseStep 1793111 = 2689667) B2689667
theorem B1195115 : Blo 1194414 1195115 := bstep (se 1 (by rfl) ⟨896336, by rfl⟩ : syracuseStep 1195115 = 1792673) B1792673
theorem B1195127 : Blo 1194414 1195127 := bstep (se 1 (by rfl) ⟨896345, by rfl⟩ : syracuseStep 1195127 = 1792691) B1792691
theorem B2268299 : Blo 1194414 2268299 := bstep (se 1 (by rfl) ⟨1701224, by rfl⟩ : syracuseStep 2268299 = 3402449) B3402449
theorem B1195147 : Blo 1194414 1195147 := bstep (se 1 (by rfl) ⟨896360, by rfl⟩ : syracuseStep 1195147 = 1792721) B1792721
theorem B1195159 : Blo 1194414 1195159 := bstep (se 1 (by rfl) ⟨896369, by rfl⟩ : syracuseStep 1195159 = 1792739) B1792739
theorem B1793177 : Blo 1194414 1793177 := bstep (se 2 (by rfl) ⟨672441, by rfl⟩ : syracuseStep 1793177 = 1344883) B1344883
theorem B1195179 : Blo 1194414 1195179 := bstep (se 1 (by rfl) ⟨896384, by rfl⟩ : syracuseStep 1195179 = 1792769) B1792769
theorem B2423987 : Blo 1194414 2423987 := bstep (se 1 (by rfl) ⟨1817990, by rfl⟩ : syracuseStep 2423987 = 3635981) B3635981
theorem B1195191 : Blo 1194414 1195191 := bstep (se 1 (by rfl) ⟨896393, by rfl⟩ : syracuseStep 1195191 = 1792787) B1792787
theorem B1195211 : Blo 1194414 1195211 := bstep (se 1 (by rfl) ⟨896408, by rfl⟩ : syracuseStep 1195211 = 1792817) B1792817
theorem B1195223 : Blo 1194414 1195223 := bstep (se 1 (by rfl) ⟨896417, by rfl⟩ : syracuseStep 1195223 = 1792835) B1792835
theorem B4308185 : Blo 1194414 4308185 := bstep (se 2 (by rfl) ⟨1615569, by rfl⟩ : syracuseStep 4308185 = 3231139) B3231139
theorem B4037849 : Blo 1194414 4037849 := bstep (se 2 (by rfl) ⟨1514193, by rfl⟩ : syracuseStep 4037849 = 3028387) B3028387
theorem B1195243 : Blo 1194414 1195243 := bstep (se 1 (by rfl) ⟨896432, by rfl⟩ : syracuseStep 1195243 = 1792865) B1792865
theorem B1195255 : Blo 1194414 1195255 := bstep (se 1 (by rfl) ⟨896441, by rfl⟩ : syracuseStep 1195255 = 1792883) B1792883
theorem B1195275 : Blo 1194414 1195275 := bstep (se 1 (by rfl) ⟨896456, by rfl⟩ : syracuseStep 1195275 = 1792913) B1792913
theorem B1793291 : Blo 1194414 1793291 := bstep (se 1 (by rfl) ⟨1344968, by rfl⟩ : syracuseStep 1793291 = 2689937) B2689937
theorem B1195287 : Blo 1194414 1195287 := bstep (se 1 (by rfl) ⟨896465, by rfl⟩ : syracuseStep 1195287 = 1792931) B1792931
theorem B1793303 : Blo 1194414 1793303 := bstep (se 1 (by rfl) ⟨1344977, by rfl⟩ : syracuseStep 1793303 = 2689955) B2689955
theorem B1195307 : Blo 1194414 1195307 := bstep (se 1 (by rfl) ⟨896480, by rfl⟩ : syracuseStep 1195307 = 1792961) B1792961
theorem B1195319 : Blo 1194414 1195319 := bstep (se 1 (by rfl) ⟨896489, by rfl⟩ : syracuseStep 1195319 = 1792979) B1792979
theorem B2268481 : Blo 1194414 2268481 := bstep (se 2 (by rfl) ⟨850680, by rfl⟩ : syracuseStep 2268481 = 1701361) B1701361
theorem B1195339 : Blo 1194414 1195339 := bstep (se 1 (by rfl) ⟨896504, by rfl⟩ : syracuseStep 1195339 = 1793009) B1793009
theorem B1195351 : Blo 1194414 1195351 := bstep (se 1 (by rfl) ⟨896513, by rfl⟩ : syracuseStep 1195351 = 1793027) B1793027
theorem B1793369 : Blo 1194414 1793369 := bstep (se 2 (by rfl) ⟨672513, by rfl⟩ : syracuseStep 1793369 = 1345027) B1345027
theorem B1195371 : Blo 1194414 1195371 := bstep (se 1 (by rfl) ⟨896528, by rfl⟩ : syracuseStep 1195371 = 1793057) B1793057
theorem B1195383 : Blo 1194414 1195383 := bstep (se 1 (by rfl) ⟨896537, by rfl⟩ : syracuseStep 1195383 = 1793075) B1793075
theorem B1195403 : Blo 1194414 1195403 := bstep (se 1 (by rfl) ⟨896552, by rfl⟩ : syracuseStep 1195403 = 1793105) B1793105
theorem B1195415 : Blo 1194414 1195415 := bstep (se 1 (by rfl) ⟨896561, by rfl⟩ : syracuseStep 1195415 = 1793123) B1793123
theorem B9084311 : Blo 1194414 9084311 := bstep (se 1 (by rfl) ⟨6813233, by rfl⟩ : syracuseStep 9084311 = 13626467) B13626467
theorem B1195435 : Blo 1194414 1195435 := bstep (se 1 (by rfl) ⟨896576, by rfl⟩ : syracuseStep 1195435 = 1793153) B1793153
theorem B1195447 : Blo 1194414 1195447 := bstep (se 1 (by rfl) ⟨896585, by rfl⟩ : syracuseStep 1195447 = 1793171) B1793171
theorem B1195467 : Blo 1194414 1195467 := bstep (se 1 (by rfl) ⟨896600, by rfl⟩ : syracuseStep 1195467 = 1793201) B1793201
theorem B1793483 : Blo 1194414 1793483 := bstep (se 1 (by rfl) ⟨1345112, by rfl⟩ : syracuseStep 1793483 = 2690225) B2690225
theorem B1195479 : Blo 1194414 1195479 := bstep (se 1 (by rfl) ⟨896609, by rfl⟩ : syracuseStep 1195479 = 1793219) B1793219
theorem B1793495 : Blo 1194414 1793495 := bstep (se 1 (by rfl) ⟨1345121, by rfl⟩ : syracuseStep 1793495 = 2690243) B2690243
theorem B9698777 : Blo 1194414 9698777 := bstep (se 2 (by rfl) ⟨3637041, by rfl⟩ : syracuseStep 9698777 = 7274083) B7274083
theorem B1195499 : Blo 1194414 1195499 := bstep (se 1 (by rfl) ⟨896624, by rfl⟩ : syracuseStep 1195499 = 1793249) B1793249
theorem B1195511 : Blo 1194414 1195511 := bstep (se 1 (by rfl) ⟨896633, by rfl⟩ : syracuseStep 1195511 = 1793267) B1793267
theorem B1195531 : Blo 1194414 1195531 := bstep (se 1 (by rfl) ⟨896648, by rfl⟩ : syracuseStep 1195531 = 1793297) B1793297
theorem B37330445 : Blo 1194414 37330445 := bstep (se 3 (by rfl) ⟨6999458, by rfl⟩ : syracuseStep 37330445 = 13998917) B13998917
theorem B1195543 : Blo 1194414 1195543 := bstep (se 1 (by rfl) ⟨896657, by rfl⟩ : syracuseStep 1195543 = 1793315) B1793315
theorem B1793561 : Blo 1194414 1793561 := bstep (se 2 (by rfl) ⟨672585, by rfl⟩ : syracuseStep 1793561 = 1345171) B1345171
theorem B1195563 : Blo 1194414 1195563 := bstep (se 1 (by rfl) ⟨896672, by rfl⟩ : syracuseStep 1195563 = 1793345) B1793345
theorem B1195575 : Blo 1194414 1195575 := bstep (se 1 (by rfl) ⟨896681, by rfl⟩ : syracuseStep 1195575 = 1793363) B1793363
theorem B1195595 : Blo 1194414 1195595 := bstep (se 1 (by rfl) ⟨896696, by rfl⟩ : syracuseStep 1195595 = 1793393) B1793393
theorem B1195607 : Blo 1194414 1195607 := bstep (se 1 (by rfl) ⟨896705, by rfl⟩ : syracuseStep 1195607 = 1793411) B1793411
theorem B1195627 : Blo 1194414 1195627 := bstep (se 1 (by rfl) ⟨896720, by rfl⟩ : syracuseStep 1195627 = 1793441) B1793441
theorem B1195639 : Blo 1194414 1195639 := bstep (se 1 (by rfl) ⟨896729, by rfl⟩ : syracuseStep 1195639 = 1793459) B1793459
theorem B1195659 : Blo 1194414 1195659 := bstep (se 1 (by rfl) ⟨896744, by rfl⟩ : syracuseStep 1195659 = 1793489) B1793489
theorem B1793675 : Blo 1194414 1793675 := bstep (se 1 (by rfl) ⟨1345256, by rfl⟩ : syracuseStep 1793675 = 2690513) B2690513
theorem B2268823 : Blo 1194414 2268823 := bstep (se 1 (by rfl) ⟨1701617, by rfl⟩ : syracuseStep 2268823 = 3403235) B3403235
theorem B1195671 : Blo 1194414 1195671 := bstep (se 1 (by rfl) ⟨896753, by rfl⟩ : syracuseStep 1195671 = 1793507) B1793507
theorem B1793687 : Blo 1194414 1793687 := bstep (se 1 (by rfl) ⟨1345265, by rfl⟩ : syracuseStep 1793687 = 2690531) B2690531
theorem B1195691 : Blo 1194414 1195691 := bstep (se 1 (by rfl) ⟨896768, by rfl⟩ : syracuseStep 1195691 = 1793537) B1793537
theorem B1195703 : Blo 1194414 1195703 := bstep (se 1 (by rfl) ⟨896777, by rfl⟩ : syracuseStep 1195703 = 1793555) B1793555
theorem B1195723 : Blo 1194414 1195723 := bstep (se 1 (by rfl) ⟨896792, by rfl⟩ : syracuseStep 1195723 = 1793585) B1793585
theorem B1195735 : Blo 1194414 1195735 := bstep (se 1 (by rfl) ⟨896801, by rfl⟩ : syracuseStep 1195735 = 1793603) B1793603
theorem B1793753 : Blo 1194414 1793753 := bstep (se 2 (by rfl) ⟨672657, by rfl⟩ : syracuseStep 1793753 = 1345315) B1345315
theorem B1195755 : Blo 1194414 1195755 := bstep (se 1 (by rfl) ⟨896816, by rfl⟩ : syracuseStep 1195755 = 1793633) B1793633
theorem B1195767 : Blo 1194414 1195767 := bstep (se 1 (by rfl) ⟨896825, by rfl⟩ : syracuseStep 1195767 = 1793651) B1793651
theorem B1195787 : Blo 1194414 1195787 := bstep (se 1 (by rfl) ⟨896840, by rfl⟩ : syracuseStep 1195787 = 1793681) B1793681
theorem B1195799 : Blo 1194414 1195799 := bstep (se 1 (by rfl) ⟨896849, by rfl⟩ : syracuseStep 1195799 = 1793699) B1793699
theorem B1195819 : Blo 1194414 1195819 := bstep (se 1 (by rfl) ⟨896864, by rfl⟩ : syracuseStep 1195819 = 1793729) B1793729
theorem B1195831 : Blo 1194414 1195831 := bstep (se 1 (by rfl) ⟨896873, by rfl⟩ : syracuseStep 1195831 = 1793747) B1793747
theorem B4538177 : Blo 1194414 4538177 := bstep (se 2 (by rfl) ⟨1701816, by rfl⟩ : syracuseStep 4538177 = 3403633) B3403633
theorem B1195851 : Blo 1194414 1195851 := bstep (se 1 (by rfl) ⟨896888, by rfl⟩ : syracuseStep 1195851 = 1793777) B1793777
theorem B1793867 : Blo 1194414 1793867 := bstep (se 1 (by rfl) ⟨1345400, by rfl⟩ : syracuseStep 1793867 = 2690801) B2690801
theorem B1195863 : Blo 1194414 1195863 := bstep (se 1 (by rfl) ⟨896897, by rfl⟩ : syracuseStep 1195863 = 1793795) B1793795
theorem B1793879 : Blo 1194414 1793879 := bstep (se 1 (by rfl) ⟨1345409, by rfl⟩ : syracuseStep 1793879 = 2690819) B2690819
theorem B1195883 : Blo 1194414 1195883 := bstep (se 1 (by rfl) ⟨896912, by rfl⟩ : syracuseStep 1195883 = 1793825) B1793825
theorem B2269043 : Blo 1194414 2269043 := bstep (se 1 (by rfl) ⟨1701782, by rfl⟩ : syracuseStep 2269043 = 3403565) B3403565
theorem B1195895 : Blo 1194414 1195895 := bstep (se 1 (by rfl) ⟨896921, by rfl⟩ : syracuseStep 1195895 = 1793843) B1793843
theorem B1195915 : Blo 1194414 1195915 := bstep (se 1 (by rfl) ⟨896936, by rfl⟩ : syracuseStep 1195915 = 1793873) B1793873
theorem B1195927 : Blo 1194414 1195927 := bstep (se 1 (by rfl) ⟨896945, by rfl⟩ : syracuseStep 1195927 = 1793891) B1793891
theorem B1793945 : Blo 1194414 1793945 := bstep (se 2 (by rfl) ⟨672729, by rfl⟩ : syracuseStep 1793945 = 1345459) B1345459
theorem B1195947 : Blo 1194414 1195947 := bstep (se 1 (by rfl) ⟨896960, by rfl⟩ : syracuseStep 1195947 = 1793921) B1793921
theorem B1195959 : Blo 1194414 1195959 := bstep (se 1 (by rfl) ⟨896969, by rfl⟩ : syracuseStep 1195959 = 1793939) B1793939
theorem B1195979 : Blo 1194414 1195979 := bstep (se 1 (by rfl) ⟨896984, by rfl⟩ : syracuseStep 1195979 = 1793969) B1793969
theorem B1195991 : Blo 1194414 1195991 := bstep (se 1 (by rfl) ⟨896993, by rfl⟩ : syracuseStep 1195991 = 1793987) B1793987
theorem B1196011 : Blo 1194414 1196011 := bstep (se 1 (by rfl) ⟨897008, by rfl⟩ : syracuseStep 1196011 = 1794017) B1794017
theorem B1196023 : Blo 1194414 1196023 := bstep (se 1 (by rfl) ⟨897017, by rfl⟩ : syracuseStep 1196023 = 1794035) B1794035
theorem B1196039 : Blo 1194414 1196039 := bstep (se 1 (by rfl) ⟨897029, by rfl⟩ : syracuseStep 1196039 = 1794059) B1794059
theorem B6807563 : Blo 1194414 6807563 := bstep (se 1 (by rfl) ⟨5105672, by rfl⟩ : syracuseStep 6807563 = 10211345) B10211345
theorem B1196047 : Blo 1194414 1196047 := bstep (se 1 (by rfl) ⟨897035, by rfl⟩ : syracuseStep 1196047 = 1794071) B1794071
theorem B1794107 : Blo 1194414 1794107 := bstep (se 1 (by rfl) ⟨1345580, by rfl⟩ : syracuseStep 1794107 = 2691161) B2691161
theorem B1196091 : Blo 1194414 1196091 := bstep (se 1 (by rfl) ⟨897068, by rfl⟩ : syracuseStep 1196091 = 1794137) B1794137
theorem B12935285 : Blo 1194414 12935285 := bstep (se 5 (by rfl) ⟨606341, by rfl⟩ : syracuseStep 12935285 = 1212683) B1212683
theorem B1794167 : Blo 1194414 1794167 := bstep (se 1 (by rfl) ⟨1345625, by rfl⟩ : syracuseStep 1794167 = 2691251) B2691251
theorem B1196167 : Blo 1194414 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B1794191 : Blo 1194414 1794191 := bstep (se 1 (by rfl) ⟨1345643, by rfl⟩ : syracuseStep 1794191 = 2691287) B2691287
theorem B1196175 : Blo 1194414 1196175 := bstep (se 1 (by rfl) ⟨897131, by rfl⟩ : syracuseStep 1196175 = 1794263) B1794263
theorem B2490515 : Blo 1194414 2490515 := bstep (se 1 (by rfl) ⟨1867886, by rfl⟩ : syracuseStep 2490515 = 3735773) B3735773
theorem B1794233 : Blo 1194414 1794233 := bstep (se 2 (by rfl) ⟨672837, by rfl⟩ : syracuseStep 1794233 = 1345675) B1345675
theorem B1196219 : Blo 1194414 1196219 := bstep (se 1 (by rfl) ⟨897164, by rfl⟩ : syracuseStep 1196219 = 1794329) B1794329
theorem B3449033 : Blo 1194414 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B1794311 : Blo 1194414 1794311 := bstep (se 1 (by rfl) ⟨1345733, by rfl⟩ : syracuseStep 1794311 = 2691467) B2691467
theorem B1196295 : Blo 1194414 1196295 := bstep (se 1 (by rfl) ⟨897221, by rfl⟩ : syracuseStep 1196295 = 1794443) B1794443
theorem B1196303 : Blo 1194414 1196303 := bstep (se 1 (by rfl) ⟨897227, by rfl⟩ : syracuseStep 1196303 = 1794455) B1794455
theorem B1794347 : Blo 1194414 1794347 := bstep (se 1 (by rfl) ⟨1345760, by rfl⟩ : syracuseStep 1794347 = 2691521) B2691521
theorem B1343803 : Blo 1194414 1343803 := bstep (se 1 (by rfl) ⟨1007852, by rfl⟩ : syracuseStep 1343803 = 2015705) B2015705
theorem B12271931 : Blo 1194414 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B1196347 : Blo 1194414 1196347 := bstep (se 1 (by rfl) ⟨897260, by rfl⟩ : syracuseStep 1196347 = 1794521) B1794521
theorem B1794377 : Blo 1194414 1794377 := bstep (se 2 (by rfl) ⟨672891, by rfl⟩ : syracuseStep 1794377 = 1345783) B1345783
theorem B2269559 : Blo 1194414 2269559 := bstep (se 1 (by rfl) ⟨1702169, by rfl⟩ : syracuseStep 2269559 = 3404339) B3404339
theorem B1794491 : Blo 1194414 1794491 := bstep (se 1 (by rfl) ⟨1345868, by rfl⟩ : syracuseStep 1794491 = 2691737) B2691737
theorem B1794551 : Blo 1194414 1794551 := bstep (se 1 (by rfl) ⟨1345913, by rfl⟩ : syracuseStep 1794551 = 2691827) B2691827
theorem B2015759 : Blo 1194414 2015759 := bstep (se 1 (by rfl) ⟨1511819, by rfl⟩ : syracuseStep 2015759 = 3023639) B3023639
theorem B2269711 : Blo 1194414 2269711 := bstep (se 1 (by rfl) ⟨1702283, by rfl⟩ : syracuseStep 2269711 = 3404567) B3404567
theorem B1794575 : Blo 1194414 1794575 := bstep (se 1 (by rfl) ⟨1345931, by rfl⟩ : syracuseStep 1794575 = 2691863) B2691863
theorem B1794617 : Blo 1194414 1794617 := bstep (se 2 (by rfl) ⟨672981, by rfl⟩ : syracuseStep 1794617 = 1345963) B1345963
theorem B17244737 : Blo 1194414 17244737 := bstep (se 2 (by rfl) ⟨6466776, by rfl⟩ : syracuseStep 17244737 = 12933553) B12933553
theorem B3023507 : Blo 1194414 3023507 := bstep (se 1 (by rfl) ⟨2267630, by rfl⟩ : syracuseStep 3023507 = 4535261) B4535261
theorem B6636269 : Blo 1194414 6636269 := bstep (se 3 (by rfl) ⟨1244300, by rfl⟩ : syracuseStep 6636269 = 2488601) B2488601
theorem B2687759 : Blo 1194414 2687759 := bstep (se 1 (by rfl) ⟨2015819, by rfl⟩ : syracuseStep 2687759 = 4031639) B4031639
theorem B1344271 : Blo 1194414 1344271 := bstep (se 1 (by rfl) ⟨1008203, by rfl⟩ : syracuseStep 1344271 = 2016407) B2016407
theorem B2687777 : Blo 1194414 2687777 := bstep (se 2 (by rfl) ⟨1007916, by rfl⟩ : syracuseStep 2687777 = 2015833) B2015833
theorem B4916027 : Blo 1194414 4916027 := bstep (se 1 (by rfl) ⟨3687020, by rfl⟩ : syracuseStep 4916027 = 7374041) B7374041
theorem B2270099 : Blo 1194414 2270099 := bstep (se 1 (by rfl) ⟨1702574, by rfl⟩ : syracuseStep 2270099 = 3405149) B3405149
theorem B3023801 : Blo 1194414 3023801 := bstep (se 2 (by rfl) ⟨1133925, by rfl⟩ : syracuseStep 3023801 = 2267851) B2267851
theorem B4031531 : Blo 1194414 4031531 := bstep (se 1 (by rfl) ⟨3023648, by rfl⟩ : syracuseStep 4031531 = 6047297) B6047297
theorem B2016299 : Blo 1194414 2016299 := bstep (se 1 (by rfl) ⟨1512224, by rfl⟩ : syracuseStep 2016299 = 3024449) B3024449
theorem B2688119 : Blo 1194414 2688119 := bstep (se 1 (by rfl) ⟨2016089, by rfl⟩ : syracuseStep 2688119 = 4032179) B4032179
theorem B13616261 : Blo 1194414 13616261 := bstep (se 4 (by rfl) ⟨1276524, by rfl⟩ : syracuseStep 13616261 = 2553049) B2553049
theorem B6808769 : Blo 1194414 6808769 := bstep (se 2 (by rfl) ⟨2553288, by rfl⟩ : syracuseStep 6808769 = 5106577) B5106577
theorem B1344775 : Blo 1194414 1344775 := bstep (se 1 (by rfl) ⟨1008581, by rfl⟩ : syracuseStep 1344775 = 2017163) B2017163
theorem B2688299 : Blo 1194414 2688299 := bstep (se 1 (by rfl) ⟨2016224, by rfl⟩ : syracuseStep 2688299 = 4032449) B4032449
theorem B2016697 : Blo 1194414 2016697 := bstep (se 2 (by rfl) ⟨756261, by rfl⟩ : syracuseStep 2016697 = 1512523) B1512523
theorem B4539833 : Blo 1194414 4539833 := bstep (se 2 (by rfl) ⟨1702437, by rfl⟩ : syracuseStep 4539833 = 3404875) B3404875
theorem B1344955 : Blo 1194414 1344955 := bstep (se 1 (by rfl) ⟨1008716, by rfl⟩ : syracuseStep 1344955 = 2017433) B2017433
theorem B3827243 : Blo 1194414 3827243 := bstep (se 1 (by rfl) ⟨2870432, by rfl⟩ : syracuseStep 3827243 = 5740865) B5740865
theorem B5449283 : Blo 1194414 5449283 := bstep (se 1 (by rfl) ⟨4086962, by rfl⟩ : syracuseStep 5449283 = 8173925) B8173925
theorem B3024499 : Blo 1194414 3024499 := bstep (se 1 (by rfl) ⟨2268374, by rfl⟩ : syracuseStep 3024499 = 4536749) B4536749
theorem B2688659 : Blo 1194414 2688659 := bstep (se 1 (by rfl) ⟨2016494, by rfl⟩ : syracuseStep 2688659 = 4032989) B4032989
theorem B13625009 : Blo 1194414 13625009 := bstep (se 2 (by rfl) ⟨5109378, by rfl⟩ : syracuseStep 13625009 = 10218757) B10218757
theorem B2688713 : Blo 1194414 2688713 := bstep (se 2 (by rfl) ⟨1008267, by rfl⟩ : syracuseStep 2688713 = 2016535) B2016535
theorem B7268069 : Blo 1194414 7268069 := bstep (se 4 (by rfl) ⟨681381, by rfl⟩ : syracuseStep 7268069 = 1362763) B1362763
theorem B3024641 : Blo 1194414 3024641 := bstep (se 2 (by rfl) ⟨1134240, by rfl⟩ : syracuseStep 3024641 = 2268481) B2268481
theorem B1345423 : Blo 1194414 1345423 := bstep (se 1 (by rfl) ⟨1009067, by rfl⟩ : syracuseStep 1345423 = 2018135) B2018135
theorem B6055883 : Blo 1194414 6055883 := bstep (se 1 (by rfl) ⟨4541912, by rfl⟩ : syracuseStep 6055883 = 9083825) B9083825
theorem B13608971 : Blo 1194414 13608971 := bstep (se 1 (by rfl) ⟨10206728, by rfl⟩ : syracuseStep 13608971 = 20413457) B20413457
theorem B1435663 : Blo 1194414 1435663 := bstep (se 1 (by rfl) ⟨1076747, by rfl⟩ : syracuseStep 1435663 = 2153495) B2153495
theorem B2017399 : Blo 1194414 2017399 := bstep (se 1 (by rfl) ⟨1513049, by rfl⟩ : syracuseStep 2017399 = 3026099) B3026099
theorem B1615991 : Blo 1194414 1615991 := bstep (se 1 (by rfl) ⟨1211993, by rfl⟩ : syracuseStep 1615991 = 2423987) B2423987
theorem B6047945 : Blo 1194414 6047945 := bstep (se 2 (by rfl) ⟨2267979, by rfl⟩ : syracuseStep 6047945 = 4535959) B4535959
theorem B3025097 : Blo 1194414 3025097 := bstep (se 2 (by rfl) ⟨1134411, by rfl⟩ : syracuseStep 3025097 = 2268823) B2268823
theorem B6056207 : Blo 1194414 6056207 := bstep (se 1 (by rfl) ⟨4542155, by rfl⟩ : syracuseStep 6056207 = 9084311) B9084311
theorem B4032827 : Blo 1194414 4032827 := bstep (se 1 (by rfl) ⟨3024620, by rfl⟩ : syracuseStep 4032827 = 6049241) B6049241
theorem B8735035 : Blo 1194414 8735035 := bstep (se 1 (by rfl) ⟨6551276, by rfl⟩ : syracuseStep 8735035 = 13102553) B13102553
theorem B2017595 : Blo 1194414 2017595 := bstep (se 1 (by rfl) ⟨1513196, by rfl⟩ : syracuseStep 2017595 = 3026393) B3026393
theorem B6465851 : Blo 1194414 6465851 := bstep (se 1 (by rfl) ⟨4849388, by rfl⟩ : syracuseStep 6465851 = 9698777) B9698777
theorem B2689415 : Blo 1194414 2689415 := bstep (se 1 (by rfl) ⟨2017061, by rfl⟩ : syracuseStep 2689415 = 4034123) B4034123
theorem B1345927 : Blo 1194414 1345927 := bstep (se 1 (by rfl) ⟨1009445, by rfl⟩ : syracuseStep 1345927 = 2018891) B2018891
theorem B4540819 : Blo 1194414 4540819 := bstep (se 1 (by rfl) ⟨3405614, by rfl⟩ : syracuseStep 4540819 = 6811229) B6811229
theorem B4311443 : Blo 1194414 4311443 := bstep (se 1 (by rfl) ⟨3233582, by rfl⟩ : syracuseStep 4311443 = 6467165) B6467165
theorem B3025451 : Blo 1194414 3025451 := bstep (se 1 (by rfl) ⟨2269088, by rfl⟩ : syracuseStep 3025451 = 4538177) B4538177
theorem B2689595 : Blo 1194414 2689595 := bstep (se 1 (by rfl) ⟨2017196, by rfl⟩ : syracuseStep 2689595 = 4034393) B4034393
theorem B49703489 : Blo 1194414 49703489 := bstep (se 2 (by rfl) ⟨18638808, by rfl⟩ : syracuseStep 49703489 = 37277617) B37277617
theorem B3402425 : Blo 1194414 3402425 := bstep (se 2 (by rfl) ⟨1275909, by rfl⟩ : syracuseStep 3402425 = 2551819) B2551819
theorem B2689721 : Blo 1194414 2689721 := bstep (se 2 (by rfl) ⟨1008645, by rfl⟩ : syracuseStep 2689721 = 2017291) B2017291
theorem B3066569 : Blo 1194414 3066569 := bstep (se 2 (by rfl) ⟨1149963, by rfl⟩ : syracuseStep 3066569 = 2299927) B2299927
theorem B2017993 : Blo 1194414 2017993 := bstep (se 2 (by rfl) ⟨756747, by rfl⟩ : syracuseStep 2017993 = 1513495) B1513495
theorem B4033313 : Blo 1194414 4033313 := bstep (se 2 (by rfl) ⟨1512492, by rfl⟩ : syracuseStep 4033313 = 3024985) B3024985
theorem B1616683 : Blo 1194414 1616683 := bstep (se 1 (by rfl) ⟨1212512, by rfl⟩ : syracuseStep 1616683 = 2425025) B2425025
theorem B1436663 : Blo 1194414 1436663 := bstep (se 1 (by rfl) ⟨1077497, by rfl⟩ : syracuseStep 1436663 = 2154995) B2154995
theorem B2690063 : Blo 1194414 2690063 := bstep (se 1 (by rfl) ⟨2017547, by rfl⟩ : syracuseStep 2690063 = 4035095) B4035095
theorem B2690081 : Blo 1194414 2690081 := bstep (se 2 (by rfl) ⟨1008780, by rfl⟩ : syracuseStep 2690081 = 2017561) B2017561
theorem B7654637 : Blo 1194414 7654637 := bstep (se 3 (by rfl) ⟨1435244, by rfl⟩ : syracuseStep 7654637 = 2870489) B2870489
theorem B11488493 : Blo 1194414 11488493 := bstep (se 3 (by rfl) ⟨2154092, by rfl⟩ : syracuseStep 11488493 = 4308185) B4308185
theorem B1748231 : Blo 1194414 1748231 := bstep (se 1 (by rfl) ⟨1311173, by rfl⟩ : syracuseStep 1748231 = 2622347) B2622347
theorem B1576199 : Blo 1194414 1576199 := bstep (se 1 (by rfl) ⟨1182149, by rfl⟩ : syracuseStep 1576199 = 2364299) B2364299
theorem B4033907 : Blo 1194414 4033907 := bstep (se 1 (by rfl) ⟨3025430, by rfl⟩ : syracuseStep 4033907 = 6050861) B6050861
theorem B2690423 : Blo 1194414 2690423 := bstep (se 1 (by rfl) ⟨2017817, by rfl⟩ : syracuseStep 2690423 = 4035635) B4035635
theorem B2018695 : Blo 1194414 2018695 := bstep (se 1 (by rfl) ⟨1514021, by rfl⟩ : syracuseStep 2018695 = 3028043) B3028043
theorem B4599193 : Blo 1194414 4599193 := bstep (se 2 (by rfl) ⟨1724697, by rfl⟩ : syracuseStep 4599193 = 3449395) B3449395
theorem B3026443 : Blo 1194414 3026443 := bstep (se 1 (by rfl) ⟨2269832, by rfl⟩ : syracuseStep 3026443 = 4539665) B4539665
theorem B2043407 : Blo 1194414 2043407 := bstep (se 1 (by rfl) ⟨1532555, by rfl⟩ : syracuseStep 2043407 = 3065111) B3065111
theorem B2690603 : Blo 1194414 2690603 := bstep (se 1 (by rfl) ⟨2017952, by rfl⟩ : syracuseStep 2690603 = 4035905) B4035905
theorem B3403417 : Blo 1194414 3403417 := bstep (se 2 (by rfl) ⟨1276281, by rfl⟩ : syracuseStep 3403417 = 2552563) B2552563
theorem B3026585 : Blo 1194414 3026585 := bstep (se 2 (by rfl) ⟨1134969, by rfl⟩ : syracuseStep 3026585 = 2269939) B2269939
theorem B4091681 : Blo 1194414 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B3026747 : Blo 1194414 3026747 := bstep (se 1 (by rfl) ⟨2270060, by rfl⟩ : syracuseStep 3026747 = 4540121) B4540121
theorem B12922739 : Blo 1194414 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B2690963 : Blo 1194414 2690963 := bstep (se 1 (by rfl) ⟨2018222, by rfl⟩ : syracuseStep 2690963 = 4036445) B4036445
theorem B2691017 : Blo 1194414 2691017 := bstep (se 2 (by rfl) ⟨1009131, by rfl⟩ : syracuseStep 2691017 = 2018263) B2018263
theorem B2912267 : Blo 1194414 2912267 := bstep (se 1 (by rfl) ⟨2184200, by rfl⟩ : syracuseStep 2912267 = 4368401) B4368401
theorem B4542551 : Blo 1194414 4542551 := bstep (se 1 (by rfl) ⟨3406913, by rfl⟩ : syracuseStep 4542551 = 6813827) B6813827
theorem B3027091 : Blo 1194414 3027091 := bstep (se 1 (by rfl) ⟨2270318, by rfl⟩ : syracuseStep 3027091 = 4540637) B4540637
theorem B3027233 : Blo 1194414 3027233 := bstep (se 2 (by rfl) ⟨1135212, by rfl⟩ : syracuseStep 3027233 = 2270425) B2270425
theorem B6811937 : Blo 1194414 6811937 := bstep (se 2 (by rfl) ⟨2554476, by rfl⟩ : syracuseStep 6811937 = 5108953) B5108953
theorem B1511723 : Blo 1194414 1511723 := bstep (se 1 (by rfl) ⟨1133792, by rfl⟩ : syracuseStep 1511723 = 2267585) B2267585
theorem B14373179 : Blo 1194414 14373179 := bstep (se 1 (by rfl) ⟨10779884, by rfl⟩ : syracuseStep 14373179 = 21559769) B21559769
theorem B3830075 : Blo 1194414 3830075 := bstep (se 1 (by rfl) ⟨2872556, by rfl⟩ : syracuseStep 3830075 = 5745113) B5745113
theorem B5747129 : Blo 1194414 5747129 := bstep (se 2 (by rfl) ⟨2155173, by rfl⟩ : syracuseStep 5747129 = 4310347) B4310347
theorem B11497949 : Blo 1194414 11497949 := bstep (se 3 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 11497949 = 4311731) B4311731
theorem B4305419 : Blo 1194414 4305419 := bstep (se 1 (by rfl) ⟨3229064, by rfl⟩ : syracuseStep 4305419 = 6458129) B6458129
theorem B5108285 : Blo 1194414 5108285 := bstep (se 3 (by rfl) ⟨957803, by rfl⟩ : syracuseStep 5108285 = 1915607) B1915607
theorem B2691719 : Blo 1194414 2691719 := bstep (se 1 (by rfl) ⟨2018789, by rfl⟩ : syracuseStep 2691719 = 4037579) B4037579
theorem B8516353 : Blo 1194414 8516353 := bstep (se 2 (by rfl) ⟨3193632, by rfl⟩ : syracuseStep 8516353 = 6387265) B6387265
theorem B1512199 : Blo 1194414 1512199 := bstep (se 1 (by rfl) ⟨1134149, by rfl⟩ : syracuseStep 1512199 = 2268299) B2268299
theorem B7271183 : Blo 1194414 7271183 := bstep (se 1 (by rfl) ⟨5453387, by rfl⟩ : syracuseStep 7271183 = 10906775) B10906775
theorem B31462181 : Blo 1194414 31462181 := bstep (se 4 (by rfl) ⟨2949579, by rfl⟩ : syracuseStep 31462181 = 5899159) B5899159
theorem B2691899 : Blo 1194414 2691899 := bstep (se 1 (by rfl) ⟨2018924, by rfl⟩ : syracuseStep 2691899 = 4037849) B4037849
theorem B5747591 : Blo 1194414 5747591 := bstep (se 1 (by rfl) ⟨4310693, by rfl⟩ : syracuseStep 5747591 = 8621387) B8621387
theorem B4846483 : Blo 1194414 4846483 := bstep (se 1 (by rfl) ⟨3634862, by rfl⟩ : syracuseStep 4846483 = 7269725) B7269725
theorem B1512695 : Blo 1194414 1512695 := bstep (se 1 (by rfl) ⟨1134521, by rfl⟩ : syracuseStep 1512695 = 2269043) B2269043
theorem B3028225 : Blo 1194414 3028225 := bstep (se 2 (by rfl) ⟨1135584, by rfl⟩ : syracuseStep 3028225 = 2271169) B2271169
theorem B10212743 : Blo 1194414 10212743 := bstep (se 1 (by rfl) ⟨7659557, by rfl⟩ : syracuseStep 10212743 = 15319115) B15319115
theorem B15324551 : Blo 1194414 15324551 := bstep (se 1 (by rfl) ⟨11493413, by rfl⟩ : syracuseStep 15324551 = 22986827) B22986827
theorem B1512847 : Blo 1194414 1512847 := bstep (se 1 (by rfl) ⟨1134635, by rfl⟩ : syracuseStep 1512847 = 2269271) B2269271
theorem B5903761 : Blo 1194414 5903761 := bstep (se 2 (by rfl) ⟨2213910, by rfl⟩ : syracuseStep 5903761 = 4427821) B4427821
theorem B10909073 : Blo 1194414 10909073 := bstep (se 2 (by rfl) ⟨4090902, by rfl⟩ : syracuseStep 10909073 = 8181805) B8181805
theorem B9074105 : Blo 1194414 9074105 := bstep (se 2 (by rfl) ⟨3402789, by rfl⟩ : syracuseStep 9074105 = 6805579) B6805579
theorem B5739979 : Blo 1194414 5739979 := bstep (se 1 (by rfl) ⟨4304984, by rfl⟩ : syracuseStep 5739979 = 8609969) B8609969
theorem B18388433 : Blo 1194414 18388433 := bstep (se 2 (by rfl) ⟨6895662, by rfl⟩ : syracuseStep 18388433 = 13791325) B13791325
theorem B1455607 : Blo 1194414 1455607 := bstep (se 1 (by rfl) ⟨1091705, by rfl⟩ : syracuseStep 1455607 = 2183411) B2183411
theorem B3405341 : Blo 1194414 3405341 := bstep (se 3 (by rfl) ⟨638501, by rfl⟩ : syracuseStep 3405341 = 1277003) B1277003
theorem B5109277 : Blo 1194414 5109277 := bstep (se 3 (by rfl) ⟨957989, by rfl⟩ : syracuseStep 5109277 = 1915979) B1915979
theorem B1513019 : Blo 1194414 1513019 := bstep (se 1 (by rfl) ⟨1134764, by rfl⟩ : syracuseStep 1513019 = 2269529) B2269529
theorem B6805079 : Blo 1194414 6805079 := bstep (se 1 (by rfl) ⟨5103809, by rfl⟩ : syracuseStep 6805079 = 10207619) B10207619
theorem B1791623 : Blo 1194414 1791623 := bstep (se 1 (by rfl) ⟨1343717, by rfl⟩ : syracuseStep 1791623 = 2687435) B2687435
theorem B1791659 : Blo 1194414 1791659 := bstep (se 1 (by rfl) ⟨1343744, by rfl⟩ : syracuseStep 1791659 = 2687489) B2687489
theorem B1791689 : Blo 1194414 1791689 := bstep (se 2 (by rfl) ⟨671883, by rfl⟩ : syracuseStep 1791689 = 1343767) B1343767
theorem B1701577 : Blo 1194414 1701577 := bstep (se 2 (by rfl) ⟨638091, by rfl⟩ : syracuseStep 1701577 = 1276183) B1276183
theorem B2553545 : Blo 1194414 2553545 := bstep (se 2 (by rfl) ⟨957579, by rfl⟩ : syracuseStep 2553545 = 1915159) B1915159
theorem B2422561 : Blo 1194414 2422561 := bstep (se 2 (by rfl) ⟨908460, by rfl⟩ : syracuseStep 2422561 = 1816921) B1816921
theorem B1791803 : Blo 1194414 1791803 := bstep (se 1 (by rfl) ⟨1343852, by rfl⟩ : syracuseStep 1791803 = 2687705) B2687705
theorem B1791863 : Blo 1194414 1791863 := bstep (se 1 (by rfl) ⟨1343897, by rfl⟩ : syracuseStep 1791863 = 2687795) B2687795
theorem B1791887 : Blo 1194414 1791887 := bstep (se 1 (by rfl) ⟨1343915, by rfl⟩ : syracuseStep 1791887 = 2687831) B2687831
theorem B4036499 : Blo 1194414 4036499 := bstep (se 1 (by rfl) ⟨3027374, by rfl⟩ : syracuseStep 4036499 = 6054749) B6054749
theorem B14931863 : Blo 1194414 14931863 := bstep (se 1 (by rfl) ⟨11198897, by rfl⟩ : syracuseStep 14931863 = 22397795) B22397795
theorem B1791929 : Blo 1194414 1791929 := bstep (se 2 (by rfl) ⟨671973, by rfl⟩ : syracuseStep 1791929 = 1343947) B1343947
theorem B2725817 : Blo 1194414 2725817 := bstep (se 2 (by rfl) ⟨1022181, by rfl⟩ : syracuseStep 2725817 = 2044363) B2044363
theorem B1816507 : Blo 1194414 1816507 := bstep (se 1 (by rfl) ⟨1362380, by rfl⟩ : syracuseStep 1816507 = 2724761) B2724761
theorem B1792007 : Blo 1194414 1792007 := bstep (se 1 (by rfl) ⟨1344005, by rfl⟩ : syracuseStep 1792007 = 2688011) B2688011
theorem B1792043 : Blo 1194414 1792043 := bstep (se 1 (by rfl) ⟨1344032, by rfl⟩ : syracuseStep 1792043 = 2688065) B2688065
theorem B5748803 : Blo 1194414 5748803 := bstep (se 1 (by rfl) ⟨4311602, by rfl⟩ : syracuseStep 5748803 = 8623205) B8623205
theorem B1792073 : Blo 1194414 1792073 := bstep (se 2 (by rfl) ⟨672027, by rfl⟩ : syracuseStep 1792073 = 1344055) B1344055
theorem B2300089 : Blo 1194414 2300089 := bstep (se 2 (by rfl) ⟨862533, by rfl⟩ : syracuseStep 2300089 = 1725067) B1725067
theorem B1702073 : Blo 1194414 1702073 := bstep (se 2 (by rfl) ⟨638277, by rfl⟩ : syracuseStep 1702073 = 1276555) B1276555
theorem B1792187 : Blo 1194414 1792187 := bstep (se 1 (by rfl) ⟨1344140, by rfl⟩ : syracuseStep 1792187 = 2688281) B2688281
theorem B3406025 : Blo 1194414 3406025 := bstep (se 2 (by rfl) ⟨1277259, by rfl⟩ : syracuseStep 3406025 = 2554519) B2554519
theorem B1792247 : Blo 1194414 1792247 := bstep (se 1 (by rfl) ⟨1344185, by rfl⟩ : syracuseStep 1792247 = 2688371) B2688371
theorem B1792271 : Blo 1194414 1792271 := bstep (se 1 (by rfl) ⟨1344203, by rfl⟩ : syracuseStep 1792271 = 2688407) B2688407
theorem B13613345 : Blo 1194414 13613345 := bstep (se 2 (by rfl) ⟨5105004, by rfl⟩ : syracuseStep 13613345 = 10210009) B10210009
theorem B1792313 : Blo 1194414 1792313 := bstep (se 2 (by rfl) ⟨672117, by rfl⟩ : syracuseStep 1792313 = 1344235) B1344235
theorem B1792391 : Blo 1194414 1792391 := bstep (se 1 (by rfl) ⟨1344293, by rfl⟩ : syracuseStep 1792391 = 2688587) B2688587
theorem B1792427 : Blo 1194414 1792427 := bstep (se 1 (by rfl) ⟨1344320, by rfl⟩ : syracuseStep 1792427 = 2688641) B2688641
theorem B1194427 : Blo 1194414 1194427 := bstep (se 1 (by rfl) ⟨895820, by rfl⟩ : syracuseStep 1194427 = 1791641) B1791641
theorem B1792457 : Blo 1194414 1792457 := bstep (se 2 (by rfl) ⟨672171, by rfl⟩ : syracuseStep 1792457 = 1344343) B1344343
theorem B14531075 : Blo 1194414 14531075 := bstep (se 1 (by rfl) ⟨10898306, by rfl⟩ : syracuseStep 14531075 = 21796613) B21796613
theorem B1194503 : Blo 1194414 1194503 := bstep (se 1 (by rfl) ⟨895877, by rfl⟩ : syracuseStep 1194503 = 1791755) B1791755
theorem B1513991 : Blo 1194414 1513991 := bstep (se 1 (by rfl) ⟨1135493, by rfl⟩ : syracuseStep 1513991 = 2270987) B2270987
theorem B1194511 : Blo 1194414 1194511 := bstep (se 1 (by rfl) ⟨895883, by rfl⟩ : syracuseStep 1194511 = 1791767) B1791767
theorem B1194555 : Blo 1194414 1194555 := bstep (se 1 (by rfl) ⟨895916, by rfl⟩ : syracuseStep 1194555 = 1791833) B1791833
theorem B1792571 : Blo 1194414 1792571 := bstep (se 1 (by rfl) ⟨1344428, by rfl⟩ : syracuseStep 1792571 = 2688857) B2688857
theorem B14727745 : Blo 1194414 14727745 := bstep (se 2 (by rfl) ⟨5522904, by rfl⟩ : syracuseStep 14727745 = 11045809) B11045809
theorem B2267767 : Blo 1194414 2267767 := bstep (se 1 (by rfl) ⟨1700825, by rfl⟩ : syracuseStep 2267767 = 3401651) B3401651
theorem B1792631 : Blo 1194414 1792631 := bstep (se 1 (by rfl) ⟨1344473, by rfl⟩ : syracuseStep 1792631 = 2688947) B2688947
theorem B1194631 : Blo 1194414 1194631 := bstep (se 1 (by rfl) ⟨895973, by rfl⟩ : syracuseStep 1194631 = 1791947) B1791947
theorem B1194639 : Blo 1194414 1194639 := bstep (se 1 (by rfl) ⟨895979, by rfl⟩ : syracuseStep 1194639 = 1791959) B1791959
theorem B1792655 : Blo 1194414 1792655 := bstep (se 1 (by rfl) ⟨1344491, by rfl⟩ : syracuseStep 1792655 = 2688983) B2688983
theorem B1792697 : Blo 1194414 1792697 := bstep (se 2 (by rfl) ⟨672261, by rfl⟩ : syracuseStep 1792697 = 1344523) B1344523
theorem B2554553 : Blo 1194414 2554553 := bstep (se 2 (by rfl) ⟨957957, by rfl⟩ : syracuseStep 2554553 = 1915915) B1915915
theorem B1194683 : Blo 1194414 1194683 := bstep (se 1 (by rfl) ⟨896012, by rfl⟩ : syracuseStep 1194683 = 1792025) B1792025
theorem B1194759 : Blo 1194414 1194759 := bstep (se 1 (by rfl) ⟨896069, by rfl⟩ : syracuseStep 1194759 = 1792139) B1792139
theorem B1792775 : Blo 1194414 1792775 := bstep (se 1 (by rfl) ⟨1344581, by rfl⟩ : syracuseStep 1792775 = 2689163) B2689163
theorem B1194767 : Blo 1194414 1194767 := bstep (se 1 (by rfl) ⟨896075, by rfl⟩ : syracuseStep 1194767 = 1792151) B1792151
theorem B3406607 : Blo 1194414 3406607 := bstep (se 1 (by rfl) ⟨2554955, by rfl⟩ : syracuseStep 3406607 = 5109911) B5109911
theorem B1792811 : Blo 1194414 1792811 := bstep (se 1 (by rfl) ⟨1344608, by rfl⟩ : syracuseStep 1792811 = 2689217) B2689217
theorem B1194811 : Blo 1194414 1194811 := bstep (se 1 (by rfl) ⟨896108, by rfl⟩ : syracuseStep 1194811 = 1792217) B1792217
theorem B1792841 : Blo 1194414 1792841 := bstep (se 2 (by rfl) ⟨672315, by rfl⟩ : syracuseStep 1792841 = 1344631) B1344631
theorem B1194887 : Blo 1194414 1194887 := bstep (se 1 (by rfl) ⟨896165, by rfl⟩ : syracuseStep 1194887 = 1792331) B1792331
theorem B1194895 : Blo 1194414 1194895 := bstep (se 1 (by rfl) ⟨896171, by rfl⟩ : syracuseStep 1194895 = 1792343) B1792343
theorem B4537235 : Blo 1194414 4537235 := bstep (se 1 (by rfl) ⟨3402926, by rfl⟩ : syracuseStep 4537235 = 6805853) B6805853
theorem B1194939 : Blo 1194414 1194939 := bstep (se 1 (by rfl) ⟨896204, by rfl⟩ : syracuseStep 1194939 = 1792409) B1792409
theorem B1792955 : Blo 1194414 1792955 := bstep (se 1 (by rfl) ⟨1344716, by rfl⟩ : syracuseStep 1792955 = 2689433) B2689433
theorem B1793015 : Blo 1194414 1793015 := bstep (se 1 (by rfl) ⟨1344761, by rfl⟩ : syracuseStep 1793015 = 2689523) B2689523
theorem B1195015 : Blo 1194414 1195015 := bstep (se 1 (by rfl) ⟨896261, by rfl⟩ : syracuseStep 1195015 = 1792523) B1792523
theorem B1195023 : Blo 1194414 1195023 := bstep (se 1 (by rfl) ⟨896267, by rfl⟩ : syracuseStep 1195023 = 1792535) B1792535
theorem B1793039 : Blo 1194414 1793039 := bstep (se 1 (by rfl) ⟨1344779, by rfl⟩ : syracuseStep 1793039 = 2689559) B2689559
theorem B2554895 : Blo 1194414 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B1793081 : Blo 1194414 1793081 := bstep (se 2 (by rfl) ⟨672405, by rfl⟩ : syracuseStep 1793081 = 1344811) B1344811
theorem B1195067 : Blo 1194414 1195067 := bstep (se 1 (by rfl) ⟨896300, by rfl⟩ : syracuseStep 1195067 = 1792601) B1792601
theorem B1195143 : Blo 1194414 1195143 := bstep (se 1 (by rfl) ⟨896357, by rfl⟩ : syracuseStep 1195143 = 1792715) B1792715
theorem B1793159 : Blo 1194414 1793159 := bstep (se 1 (by rfl) ⟨1344869, by rfl⟩ : syracuseStep 1793159 = 2689739) B2689739
theorem B1703047 : Blo 1194414 1703047 := bstep (se 1 (by rfl) ⟨1277285, by rfl⟩ : syracuseStep 1703047 = 2554571) B2554571
theorem B1195151 : Blo 1194414 1195151 := bstep (se 1 (by rfl) ⟨896363, by rfl⟩ : syracuseStep 1195151 = 1792727) B1792727
theorem B1793195 : Blo 1194414 1793195 := bstep (se 1 (by rfl) ⟨1344896, by rfl⟩ : syracuseStep 1793195 = 2689793) B2689793
theorem B1195195 : Blo 1194414 1195195 := bstep (se 1 (by rfl) ⟨896396, by rfl⟩ : syracuseStep 1195195 = 1792793) B1792793
theorem B13098185 : Blo 1194414 13098185 := bstep (se 2 (by rfl) ⟨4911819, by rfl⟩ : syracuseStep 13098185 = 9823639) B9823639
theorem B1793225 : Blo 1194414 1793225 := bstep (se 2 (by rfl) ⟨672459, by rfl⟩ : syracuseStep 1793225 = 1344919) B1344919
theorem B1195271 : Blo 1194414 1195271 := bstep (se 1 (by rfl) ⟨896453, by rfl⟩ : syracuseStep 1195271 = 1792907) B1792907
theorem B1277191 : Blo 1194414 1277191 := bstep (se 1 (by rfl) ⟨957893, by rfl⟩ : syracuseStep 1277191 = 1915787) B1915787
theorem B1195279 : Blo 1194414 1195279 := bstep (se 1 (by rfl) ⟨896459, by rfl⟩ : syracuseStep 1195279 = 1792919) B1792919
theorem B1195323 : Blo 1194414 1195323 := bstep (se 1 (by rfl) ⟨896492, by rfl⟩ : syracuseStep 1195323 = 1792985) B1792985
theorem B1793339 : Blo 1194414 1793339 := bstep (se 1 (by rfl) ⟨1345004, by rfl⟩ : syracuseStep 1793339 = 2690009) B2690009
theorem B20716859 : Blo 1194414 20716859 := bstep (se 1 (by rfl) ⟨15537644, by rfl⟩ : syracuseStep 20716859 = 31075289) B31075289
theorem B1793399 : Blo 1194414 1793399 := bstep (se 1 (by rfl) ⟨1345049, by rfl⟩ : syracuseStep 1793399 = 2690099) B2690099
theorem B1195399 : Blo 1194414 1195399 := bstep (se 1 (by rfl) ⟨896549, by rfl⟩ : syracuseStep 1195399 = 1793099) B1793099
theorem B1195407 : Blo 1194414 1195407 := bstep (se 1 (by rfl) ⟨896555, by rfl⟩ : syracuseStep 1195407 = 1793111) B1793111
theorem B1793423 : Blo 1194414 1793423 := bstep (se 1 (by rfl) ⟨1345067, by rfl⟩ : syracuseStep 1793423 = 2690135) B2690135
theorem B1793465 : Blo 1194414 1793465 := bstep (se 2 (by rfl) ⟨672549, by rfl⟩ : syracuseStep 1793465 = 1345099) B1345099
theorem B1195451 : Blo 1194414 1195451 := bstep (se 1 (by rfl) ⟨896588, by rfl⟩ : syracuseStep 1195451 = 1793177) B1793177
theorem B1195527 : Blo 1194414 1195527 := bstep (se 1 (by rfl) ⟨896645, by rfl⟩ : syracuseStep 1195527 = 1793291) B1793291
theorem B1793543 : Blo 1194414 1793543 := bstep (se 1 (by rfl) ⟨1345157, by rfl⟩ : syracuseStep 1793543 = 2690315) B2690315
theorem B1195535 : Blo 1194414 1195535 := bstep (se 1 (by rfl) ⟨896651, by rfl⟩ : syracuseStep 1195535 = 1793303) B1793303
theorem B1793579 : Blo 1194414 1793579 := bstep (se 1 (by rfl) ⟨1345184, by rfl⟩ : syracuseStep 1793579 = 2690369) B2690369
theorem B1195579 : Blo 1194414 1195579 := bstep (se 1 (by rfl) ⟨896684, by rfl⟩ : syracuseStep 1195579 = 1793369) B1793369
theorem B1793609 : Blo 1194414 1793609 := bstep (se 2 (by rfl) ⟨672603, by rfl⟩ : syracuseStep 1793609 = 1345207) B1345207
theorem B4087415 : Blo 1194414 4087415 := bstep (se 1 (by rfl) ⟨3065561, by rfl⟩ : syracuseStep 4087415 = 6131123) B6131123
theorem B1195655 : Blo 1194414 1195655 := bstep (se 1 (by rfl) ⟨896741, by rfl⟩ : syracuseStep 1195655 = 1793483) B1793483
theorem B1195663 : Blo 1194414 1195663 := bstep (se 1 (by rfl) ⟨896747, by rfl⟩ : syracuseStep 1195663 = 1793495) B1793495
theorem B24886963 : Blo 1194414 24886963 := bstep (se 1 (by rfl) ⟨18665222, by rfl⟩ : syracuseStep 24886963 = 37330445) B37330445
theorem B1195707 : Blo 1194414 1195707 := bstep (se 1 (by rfl) ⟨896780, by rfl⟩ : syracuseStep 1195707 = 1793561) B1793561
theorem B1793723 : Blo 1194414 1793723 := bstep (se 1 (by rfl) ⟨1345292, by rfl⟩ : syracuseStep 1793723 = 2690585) B2690585
theorem B1793783 : Blo 1194414 1793783 := bstep (se 1 (by rfl) ⟨1345337, by rfl⟩ : syracuseStep 1793783 = 2690675) B2690675
theorem B1195783 : Blo 1194414 1195783 := bstep (se 1 (by rfl) ⟨896837, by rfl⟩ : syracuseStep 1195783 = 1793675) B1793675
theorem B6807311 : Blo 1194414 6807311 := bstep (se 1 (by rfl) ⟨5105483, by rfl⟩ : syracuseStep 6807311 = 10210967) B10210967
theorem B1195791 : Blo 1194414 1195791 := bstep (se 1 (by rfl) ⟨896843, by rfl⟩ : syracuseStep 1195791 = 1793687) B1793687
theorem B1793807 : Blo 1194414 1793807 := bstep (se 1 (by rfl) ⟨1345355, by rfl⟩ : syracuseStep 1793807 = 2690711) B2690711
theorem B3448619 : Blo 1194414 3448619 := bstep (se 1 (by rfl) ⟨2586464, by rfl⟩ : syracuseStep 3448619 = 5172929) B5172929
theorem B1793849 : Blo 1194414 1793849 := bstep (se 2 (by rfl) ⟨672693, by rfl⟩ : syracuseStep 1793849 = 1345387) B1345387
theorem B1195835 : Blo 1194414 1195835 := bstep (se 1 (by rfl) ⟨896876, by rfl⟩ : syracuseStep 1195835 = 1793753) B1793753
theorem B7659353 : Blo 1194414 7659353 := bstep (se 2 (by rfl) ⟨2872257, by rfl⟩ : syracuseStep 7659353 = 5744515) B5744515
theorem B1195911 : Blo 1194414 1195911 := bstep (se 1 (by rfl) ⟨896933, by rfl⟩ : syracuseStep 1195911 = 1793867) B1793867
theorem B1793927 : Blo 1194414 1793927 := bstep (se 1 (by rfl) ⟨1345445, by rfl⟩ : syracuseStep 1793927 = 2690891) B2690891
theorem B1195919 : Blo 1194414 1195919 := bstep (se 1 (by rfl) ⟨896939, by rfl⟩ : syracuseStep 1195919 = 1793879) B1793879
theorem B6053777 : Blo 1194414 6053777 := bstep (se 2 (by rfl) ⟨2270166, by rfl⟩ : syracuseStep 6053777 = 4540333) B4540333
theorem B1793963 : Blo 1194414 1793963 := bstep (se 1 (by rfl) ⟨1345472, by rfl⟩ : syracuseStep 1793963 = 2690945) B2690945
theorem B1195963 : Blo 1194414 1195963 := bstep (se 1 (by rfl) ⟨896972, by rfl⟩ : syracuseStep 1195963 = 1793945) B1793945
theorem B1793993 : Blo 1194414 1793993 := bstep (se 2 (by rfl) ⟨672747, by rfl⟩ : syracuseStep 1793993 = 1345495) B1345495
theorem B4538375 : Blo 1194414 4538375 := bstep (se 1 (by rfl) ⟨3403781, by rfl⟩ : syracuseStep 4538375 = 6807563) B6807563
theorem B1941511 : Blo 1194414 1941511 := bstep (se 1 (by rfl) ⟨1456133, by rfl⟩ : syracuseStep 1941511 = 2912267) B2912267
theorem B1196071 : Blo 1194414 1196071 := bstep (se 1 (by rfl) ⟨897053, by rfl⟩ : syracuseStep 1196071 = 1794107) B1794107
theorem B1196111 : Blo 1194414 1196111 := bstep (se 1 (by rfl) ⟨897083, by rfl⟩ : syracuseStep 1196111 = 1794167) B1794167
theorem B1196127 : Blo 1194414 1196127 := bstep (se 1 (by rfl) ⟨897095, by rfl⟩ : syracuseStep 1196127 = 1794191) B1794191
theorem B1196155 : Blo 1194414 1196155 := bstep (se 1 (by rfl) ⟨897116, by rfl⟩ : syracuseStep 1196155 = 1794233) B1794233
theorem B1196207 : Blo 1194414 1196207 := bstep (se 1 (by rfl) ⟨897155, by rfl⟩ : syracuseStep 1196207 = 1794311) B1794311
theorem B1196231 : Blo 1194414 1196231 := bstep (se 1 (by rfl) ⟨897173, by rfl⟩ : syracuseStep 1196231 = 1794347) B1794347
theorem B1196251 : Blo 1194414 1196251 := bstep (se 1 (by rfl) ⟨897188, by rfl⟩ : syracuseStep 1196251 = 1794377) B1794377
theorem B1196327 : Blo 1194414 1196327 := bstep (se 1 (by rfl) ⟨897245, by rfl⟩ : syracuseStep 1196327 = 1794491) B1794491
theorem B4309309 : Blo 1194414 4309309 := bstep (se 3 (by rfl) ⟨807995, by rfl⟩ : syracuseStep 4309309 = 1615991) B1615991
theorem B1196367 : Blo 1194414 1196367 := bstep (se 1 (by rfl) ⟨897275, by rfl⟩ : syracuseStep 1196367 = 1794551) B1794551
theorem B1343839 : Blo 1194414 1343839 := bstep (se 1 (by rfl) ⟨1007879, by rfl⟩ : syracuseStep 1343839 = 2015759) B2015759
theorem B1196383 : Blo 1194414 1196383 := bstep (se 1 (by rfl) ⟨897287, by rfl⟩ : syracuseStep 1196383 = 1794575) B1794575
theorem B1196411 : Blo 1194414 1196411 := bstep (se 1 (by rfl) ⟨897308, by rfl⟩ : syracuseStep 1196411 = 1794617) B1794617
theorem B1794479 : Blo 1194414 1794479 := bstep (se 1 (by rfl) ⟨1345859, by rfl⟩ : syracuseStep 1794479 = 2691719) B2691719
theorem B2015671 : Blo 1194414 2015671 := bstep (se 1 (by rfl) ⟨1511753, by rfl⟩ : syracuseStep 2015671 = 3023507) B3023507
theorem B4538861 : Blo 1194414 4538861 := bstep (se 3 (by rfl) ⟨851036, by rfl⟩ : syracuseStep 4538861 = 1702073) B1702073
theorem B4424179 : Blo 1194414 4424179 := bstep (se 1 (by rfl) ⟨3318134, by rfl⟩ : syracuseStep 4424179 = 6636269) B6636269
theorem B1794569 : Blo 1194414 1794569 := bstep (se 2 (by rfl) ⟨672963, by rfl⟩ : syracuseStep 1794569 = 1345927) B1345927
theorem B6054425 : Blo 1194414 6054425 := bstep (se 2 (by rfl) ⟨2270409, by rfl⟩ : syracuseStep 6054425 = 4540819) B4540819
theorem B3277351 : Blo 1194414 3277351 := bstep (se 1 (by rfl) ⟨2458013, by rfl⟩ : syracuseStep 3277351 = 4916027) B4916027
theorem B1794599 : Blo 1194414 1794599 := bstep (se 1 (by rfl) ⟨1345949, by rfl⟩ : syracuseStep 1794599 = 2691899) B2691899
theorem B2015867 : Blo 1194414 2015867 := bstep (se 1 (by rfl) ⟨1511900, by rfl⟩ : syracuseStep 2015867 = 3023801) B3023801
theorem B4203197 : Blo 1194414 4203197 := bstep (se 3 (by rfl) ⟨788099, by rfl⟩ : syracuseStep 4203197 = 1576199) B1576199
theorem B2687687 : Blo 1194414 2687687 := bstep (se 1 (by rfl) ⟨2015765, by rfl⟩ : syracuseStep 2687687 = 4031531) B4031531
theorem B1344199 : Blo 1194414 1344199 := bstep (se 1 (by rfl) ⟨1008149, by rfl⟩ : syracuseStep 1344199 = 2016299) B2016299
theorem B19636993 : Blo 1194414 19636993 := bstep (se 2 (by rfl) ⟨7363872, by rfl⟩ : syracuseStep 19636993 = 14727745) B14727745
theorem B9077507 : Blo 1194414 9077507 := bstep (se 1 (by rfl) ⟨6808130, by rfl⟩ : syracuseStep 9077507 = 13616261) B13616261
theorem B4031261 : Blo 1194414 4031261 := bstep (se 3 (by rfl) ⟨755861, by rfl⟩ : syracuseStep 4031261 = 1511723) B1511723
theorem B4539179 : Blo 1194414 4539179 := bstep (se 1 (by rfl) ⟨3404384, by rfl⟩ : syracuseStep 4539179 = 6808769) B6808769
theorem B3023689 : Blo 1194414 3023689 := bstep (se 2 (by rfl) ⟨1133883, by rfl⟩ : syracuseStep 3023689 = 2267767) B2267767
theorem B6808495 : Blo 1194414 6808495 := bstep (se 1 (by rfl) ⟨5106371, by rfl⟩ : syracuseStep 6808495 = 10212743) B10212743
theorem B10216367 : Blo 1194414 10216367 := bstep (se 1 (by rfl) ⟨7662275, by rfl⟩ : syracuseStep 10216367 = 15324551) B15324551
theorem B11355137 : Blo 1194414 11355137 := bstep (se 2 (by rfl) ⟨4258176, by rfl⟩ : syracuseStep 11355137 = 8516353) B8516353
theorem B2016265 : Blo 1194414 2016265 := bstep (se 2 (by rfl) ⟨756099, by rfl⟩ : syracuseStep 2016265 = 1512199) B1512199
theorem B2155577 : Blo 1194414 2155577 := bstep (se 2 (by rfl) ⟨808341, by rfl⟩ : syracuseStep 2155577 = 1616683) B1616683
theorem B2016427 : Blo 1194414 2016427 := bstep (se 1 (by rfl) ⟨1512320, by rfl⟩ : syracuseStep 2016427 = 3024641) B3024641
theorem B9954575 : Blo 1194414 9954575 := bstep (se 1 (by rfl) ⟨7465931, by rfl⟩ : syracuseStep 9954575 = 14931863) B14931863
theorem B4031963 : Blo 1194414 4031963 := bstep (se 1 (by rfl) ⟨3023972, by rfl⟩ : syracuseStep 4031963 = 6047945) B6047945
theorem B2016731 : Blo 1194414 2016731 := bstep (se 1 (by rfl) ⟨1512548, by rfl⟩ : syracuseStep 2016731 = 3025097) B3025097
theorem B2270683 : Blo 1194414 2270683 := bstep (se 1 (by rfl) ⟨1703012, by rfl⟩ : syracuseStep 2270683 = 3406025) B3406025
theorem B2270729 : Blo 1194414 2270729 := bstep (se 2 (by rfl) ⟨851523, by rfl⟩ : syracuseStep 2270729 = 1703047) B1703047
theorem B2688551 : Blo 1194414 2688551 := bstep (se 1 (by rfl) ⟨2016413, by rfl⟩ : syracuseStep 2688551 = 4032827) B4032827
theorem B1345063 : Blo 1194414 1345063 := bstep (se 1 (by rfl) ⟨1008797, by rfl⟩ : syracuseStep 1345063 = 2017595) B2017595
theorem B4310567 : Blo 1194414 4310567 := bstep (se 1 (by rfl) ⟨3232925, by rfl⟩ : syracuseStep 4310567 = 6465851) B6465851
theorem B2016967 : Blo 1194414 2016967 := bstep (se 1 (by rfl) ⟨1512725, by rfl⟩ : syracuseStep 2016967 = 3025451) B3025451
theorem B2271071 : Blo 1194414 2271071 := bstep (se 1 (by rfl) ⟨1703303, by rfl⟩ : syracuseStep 2271071 = 3406607) B3406607
theorem B2017129 : Blo 1194414 2017129 := bstep (se 2 (by rfl) ⟨756423, by rfl⟩ : syracuseStep 2017129 = 1512847) B1512847
theorem B2688875 : Blo 1194414 2688875 := bstep (se 1 (by rfl) ⟨2016656, by rfl⟩ : syracuseStep 2688875 = 4033313) B4033313
theorem B6809453 : Blo 1194414 6809453 := bstep (se 3 (by rfl) ⟨1276772, by rfl⟩ : syracuseStep 6809453 = 2553545) B2553545
theorem B2688929 : Blo 1194414 2688929 := bstep (se 2 (by rfl) ⟨1008348, by rfl⟩ : syracuseStep 2688929 = 2016697) B2016697
theorem B29075381 : Blo 1194414 29075381 := bstep (se 5 (by rfl) ⟨1362908, by rfl⟩ : syracuseStep 29075381 = 2725817) B2725817
theorem B3024823 : Blo 1194414 3024823 := bstep (se 1 (by rfl) ⟨2268617, by rfl⟩ : syracuseStep 3024823 = 4537235) B4537235
theorem B7653305 : Blo 1194414 7653305 := bstep (se 2 (by rfl) ⟨2869989, by rfl⟩ : syracuseStep 7653305 = 5739979) B5739979
theorem B4032665 : Blo 1194414 4032665 := bstep (se 2 (by rfl) ⟨1512249, by rfl⟩ : syracuseStep 4032665 = 3024499) B3024499
theorem B2689271 : Blo 1194414 2689271 := bstep (se 1 (by rfl) ⟨2016953, by rfl⟩ : syracuseStep 2689271 = 4033907) B4033907
theorem B1362271 : Blo 1194414 1362271 := bstep (se 1 (by rfl) ⟨1021703, by rfl⟩ : syracuseStep 1362271 = 2043407) B2043407
theorem B3230081 : Blo 1194414 3230081 := bstep (se 2 (by rfl) ⟨1211280, by rfl⟩ : syracuseStep 3230081 = 2422561) B2422561
theorem B2017723 : Blo 1194414 2017723 := bstep (se 1 (by rfl) ⟨1513292, by rfl⟩ : syracuseStep 2017723 = 3026585) B3026585
theorem B2017831 : Blo 1194414 2017831 := bstep (se 1 (by rfl) ⟨1513373, by rfl⟩ : syracuseStep 2017831 = 3026747) B3026747
theorem B5106235 : Blo 1194414 5106235 := bstep (se 1 (by rfl) ⟨3829676, by rfl⟩ : syracuseStep 5106235 = 7659353) B7659353
theorem B2689865 : Blo 1194414 2689865 := bstep (se 2 (by rfl) ⟨1008699, by rfl⟩ : syracuseStep 2689865 = 2017399) B2017399
theorem B2018155 : Blo 1194414 2018155 := bstep (se 1 (by rfl) ⟨1513616, by rfl⟩ : syracuseStep 2018155 = 3027233) B3027233
theorem B4541291 : Blo 1194414 4541291 := bstep (se 1 (by rfl) ⟨3405968, by rfl⟩ : syracuseStep 4541291 = 6811937) B6811937
theorem B3066785 : Blo 1194414 3066785 := bstep (se 2 (by rfl) ⟨1150044, by rfl⟩ : syracuseStep 3066785 = 2300089) B2300089
theorem B74591189 : Blo 1194414 74591189 := bstep (se 7 (by rfl) ⟨874115, by rfl⟩ : syracuseStep 74591189 = 1748231) B1748231
theorem B2870279 : Blo 1194414 2870279 := bstep (se 1 (by rfl) ⟨2152709, by rfl⟩ : syracuseStep 2870279 = 4305419) B4305419
theorem B11496491 : Blo 1194414 11496491 := bstep (se 1 (by rfl) ⟨8622368, by rfl⟩ : syracuseStep 11496491 = 17244737) B17244737
theorem B20974787 : Blo 1194414 20974787 := bstep (se 1 (by rfl) ⟨15731090, by rfl⟩ : syracuseStep 20974787 = 31462181) B31462181
theorem B4033853 : Blo 1194414 4033853 := bstep (se 3 (by rfl) ⟨756347, by rfl⟩ : syracuseStep 4033853 = 1512695) B1512695
theorem B3026281 : Blo 1194414 3026281 := bstep (se 2 (by rfl) ⟨1134855, by rfl⟩ : syracuseStep 3026281 = 2269711) B2269711
theorem B2690657 : Blo 1194414 2690657 := bstep (se 2 (by rfl) ⟨1008996, by rfl⟩ : syracuseStep 2690657 = 2017993) B2017993
theorem B6049403 : Blo 1194414 6049403 := bstep (se 1 (by rfl) ⟨4537052, by rfl⟩ : syracuseStep 6049403 = 9074105) B9074105
theorem B3026555 : Blo 1194414 3026555 := bstep (se 1 (by rfl) ⟨2269916, by rfl⟩ : syracuseStep 3026555 = 4539833) B4539833
theorem B12258955 : Blo 1194414 12258955 := bstep (se 1 (by rfl) ⟨9194216, by rfl⟩ : syracuseStep 12258955 = 18388433) B18388433
theorem B2551495 : Blo 1194414 2551495 := bstep (se 1 (by rfl) ⟨1913621, by rfl⟩ : syracuseStep 2551495 = 3827243) B3827243
theorem B3632855 : Blo 1194414 3632855 := bstep (se 1 (by rfl) ⟨2724641, by rfl⟩ : syracuseStep 3632855 = 5449283) B5449283
theorem B4845379 : Blo 1194414 4845379 := bstep (se 1 (by rfl) ⟨3634034, by rfl⟩ : syracuseStep 4845379 = 7268069) B7268069
theorem B2690999 : Blo 1194414 2690999 := bstep (se 1 (by rfl) ⟨2018249, by rfl⟩ : syracuseStep 2690999 = 4036499) B4036499
theorem B9072647 : Blo 1194414 9072647 := bstep (se 1 (by rfl) ⟨6804485, by rfl⟩ : syracuseStep 9072647 = 13608971) B13608971
theorem B6811685 : Blo 1194414 6811685 := bstep (se 4 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 6811685 = 1277191) B1277191
theorem B9080909 : Blo 1194414 9080909 := bstep (se 3 (by rfl) ⟨1702670, by rfl⟩ : syracuseStep 9080909 = 3405341) B3405341
theorem B4034717 : Blo 1194414 4034717 := bstep (se 3 (by rfl) ⟨756509, by rfl⟩ : syracuseStep 4034717 = 1513019) B1513019
theorem B9687383 : Blo 1194414 9687383 := bstep (se 1 (by rfl) ⟨7265537, by rfl⟩ : syracuseStep 9687383 = 14531075) B14531075
theorem B2044379 : Blo 1194414 2044379 := bstep (se 1 (by rfl) ⟨1533284, by rfl⟩ : syracuseStep 2044379 = 3066569) B3066569
theorem B9073133 : Blo 1194414 9073133 := bstep (se 3 (by rfl) ⟨1701212, by rfl⟩ : syracuseStep 9073133 = 3402425) B3402425
theorem B2691593 : Blo 1194414 2691593 := bstep (se 2 (by rfl) ⟨1009347, by rfl⟩ : syracuseStep 2691593 = 2018695) B2018695
theorem B6132257 : Blo 1194414 6132257 := bstep (se 2 (by rfl) ⟨2299596, by rfl⟩ : syracuseStep 6132257 = 4599193) B4599193
theorem B4035257 : Blo 1194414 4035257 := bstep (se 2 (by rfl) ⟨1513221, by rfl⟩ : syracuseStep 4035257 = 3026443) B3026443
theorem B6812369 : Blo 1194414 6812369 := bstep (se 2 (by rfl) ⟨2554638, by rfl⟩ : syracuseStep 6812369 = 5109277) B5109277
theorem B33182617 : Blo 1194414 33182617 := bstep (se 2 (by rfl) ⟨12443481, by rfl⟩ : syracuseStep 33182617 = 24886963) B24886963
theorem B2724943 : Blo 1194414 2724943 := bstep (se 1 (by rfl) ⟨2043707, by rfl⟩ : syracuseStep 2724943 = 4087415) B4087415
theorem B2299079 : Blo 1194414 2299079 := bstep (se 1 (by rfl) ⟨1724309, by rfl⟩ : syracuseStep 2299079 = 3448619) B3448619
theorem B8615159 : Blo 1194414 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B2422009 : Blo 1194414 2422009 := bstep (se 2 (by rfl) ⟨908253, by rfl⟩ : syracuseStep 2422009 = 1816507) B1816507
theorem B4035851 : Blo 1194414 4035851 := bstep (se 1 (by rfl) ⟨3026888, by rfl⟩ : syracuseStep 4035851 = 6053777) B6053777
theorem B3831101 : Blo 1194414 3831101 := bstep (se 3 (by rfl) ⟨718331, by rfl⟩ : syracuseStep 3831101 = 1436663) B1436663
theorem B3028367 : Blo 1194414 3028367 := bstep (se 1 (by rfl) ⟨2271275, by rfl⟩ : syracuseStep 3028367 = 4542551) B4542551
theorem B7656869 : Blo 1194414 7656869 := bstep (se 4 (by rfl) ⟨717831, by rfl⟩ : syracuseStep 7656869 = 1435663) B1435663
theorem B8623523 : Blo 1194414 8623523 := bstep (se 1 (by rfl) ⟨6467642, by rfl⟩ : syracuseStep 8623523 = 12935285) B12935285
theorem B1660343 : Blo 1194414 1660343 := bstep (se 1 (by rfl) ⟨1245257, by rfl⟩ : syracuseStep 1660343 = 2490515) B2490515
theorem B2299355 : Blo 1194414 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B4036121 : Blo 1194414 4036121 := bstep (se 2 (by rfl) ⟨1513545, by rfl⟩ : syracuseStep 4036121 = 3027091) B3027091
theorem B9582119 : Blo 1194414 9582119 := bstep (se 1 (by rfl) ⟨7186589, by rfl⟩ : syracuseStep 9582119 = 14373179) B14373179
theorem B2553383 : Blo 1194414 2553383 := bstep (se 1 (by rfl) ⟨1915037, by rfl⟩ : syracuseStep 2553383 = 3830075) B3830075
theorem B8181287 : Blo 1194414 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B3831419 : Blo 1194414 3831419 := bstep (se 1 (by rfl) ⟨2873564, by rfl⟩ : syracuseStep 3831419 = 5747129) B5747129
theorem B7665299 : Blo 1194414 7665299 := bstep (se 1 (by rfl) ⟨5748974, by rfl⟩ : syracuseStep 7665299 = 11497949) B11497949
theorem B1791737 : Blo 1194414 1791737 := bstep (se 2 (by rfl) ⟨671901, by rfl⟩ : syracuseStep 1791737 = 1343803) B1343803
theorem B11646713 : Blo 1194414 11646713 := bstep (se 2 (by rfl) ⟨4367517, by rfl⟩ : syracuseStep 11646713 = 8735035) B8735035
theorem B1791839 : Blo 1194414 1791839 := bstep (se 1 (by rfl) ⟨1343879, by rfl⟩ : syracuseStep 1791839 = 2687759) B2687759
theorem B4847455 : Blo 1194414 4847455 := bstep (se 1 (by rfl) ⟨3635591, by rfl⟩ : syracuseStep 4847455 = 7271183) B7271183
theorem B1791851 : Blo 1194414 1791851 := bstep (se 1 (by rfl) ⟨1343888, by rfl⟩ : syracuseStep 1791851 = 2687777) B2687777
theorem B3831727 : Blo 1194414 3831727 := bstep (se 1 (by rfl) ⟨2873795, by rfl⟩ : syracuseStep 3831727 = 5747591) B5747591
theorem B1513399 : Blo 1194414 1513399 := bstep (se 1 (by rfl) ⟨1135049, by rfl⟩ : syracuseStep 1513399 = 2270099) B2270099
theorem B1792079 : Blo 1194414 1792079 := bstep (se 1 (by rfl) ⟨1344059, by rfl⟩ : syracuseStep 1792079 = 2688119) B2688119
theorem B1792199 : Blo 1194414 1792199 := bstep (se 1 (by rfl) ⟨1344149, by rfl⟩ : syracuseStep 1792199 = 2688299) B2688299
theorem B7272715 : Blo 1194414 7272715 := bstep (se 1 (by rfl) ⟨5454536, by rfl⟩ : syracuseStep 7272715 = 10909073) B10909073
theorem B6052157 : Blo 1194414 6052157 := bstep (se 3 (by rfl) ⟨1134779, by rfl⟩ : syracuseStep 6052157 = 2269559) B2269559
theorem B1792361 : Blo 1194414 1792361 := bstep (se 2 (by rfl) ⟨672135, by rfl⟩ : syracuseStep 1792361 = 1344271) B1344271
theorem B9075077 : Blo 1194414 9075077 := bstep (se 4 (by rfl) ⟨850788, by rfl⟩ : syracuseStep 9075077 = 1701577) B1701577
theorem B4536719 : Blo 1194414 4536719 := bstep (se 1 (by rfl) ⟨3402539, by rfl⟩ : syracuseStep 4536719 = 6805079) B6805079
theorem B1194415 : Blo 1194414 1194415 := bstep (se 1 (by rfl) ⟨895811, by rfl⟩ : syracuseStep 1194415 = 1791623) B1791623
theorem B1792439 : Blo 1194414 1792439 := bstep (se 1 (by rfl) ⟨1344329, by rfl⟩ : syracuseStep 1792439 = 2688659) B2688659
theorem B1194439 : Blo 1194414 1194439 := bstep (se 1 (by rfl) ⟨895829, by rfl⟩ : syracuseStep 1194439 = 1791659) B1791659
theorem B9083339 : Blo 1194414 9083339 := bstep (se 1 (by rfl) ⟨6812504, by rfl⟩ : syracuseStep 9083339 = 13625009) B13625009
theorem B1194459 : Blo 1194414 1194459 := bstep (se 1 (by rfl) ⟨895844, by rfl⟩ : syracuseStep 1194459 = 1791689) B1791689
theorem B1792475 : Blo 1194414 1792475 := bstep (se 1 (by rfl) ⟨1344356, by rfl⟩ : syracuseStep 1792475 = 2688713) B2688713
theorem B6461977 : Blo 1194414 6461977 := bstep (se 2 (by rfl) ⟨2423241, by rfl⟩ : syracuseStep 6461977 = 4846483) B4846483
theorem B1194535 : Blo 1194414 1194535 := bstep (se 1 (by rfl) ⟨895901, by rfl⟩ : syracuseStep 1194535 = 1791803) B1791803
theorem B1194575 : Blo 1194414 1194575 := bstep (se 1 (by rfl) ⟨895931, by rfl⟩ : syracuseStep 1194575 = 1791863) B1791863
theorem B1194591 : Blo 1194414 1194591 := bstep (se 1 (by rfl) ⟨895943, by rfl⟩ : syracuseStep 1194591 = 1791887) B1791887
theorem B1194619 : Blo 1194414 1194619 := bstep (se 1 (by rfl) ⟨895964, by rfl⟩ : syracuseStep 1194619 = 1791929) B1791929
theorem B4037255 : Blo 1194414 4037255 := bstep (se 1 (by rfl) ⟨3027941, by rfl⟩ : syracuseStep 4037255 = 6055883) B6055883
theorem B1194671 : Blo 1194414 1194671 := bstep (se 1 (by rfl) ⟨896003, by rfl⟩ : syracuseStep 1194671 = 1792007) B1792007
theorem B4037309 : Blo 1194414 4037309 := bstep (se 3 (by rfl) ⟨756995, by rfl⟩ : syracuseStep 4037309 = 1513991) B1513991
theorem B1194695 : Blo 1194414 1194695 := bstep (se 1 (by rfl) ⟨896021, by rfl⟩ : syracuseStep 1194695 = 1792043) B1792043
theorem B3832535 : Blo 1194414 3832535 := bstep (se 1 (by rfl) ⟨2874401, by rfl⟩ : syracuseStep 3832535 = 5748803) B5748803
theorem B1194715 : Blo 1194414 1194715 := bstep (se 1 (by rfl) ⟨896036, by rfl⟩ : syracuseStep 1194715 = 1792073) B1792073
theorem B1194791 : Blo 1194414 1194791 := bstep (se 1 (by rfl) ⟨896093, by rfl⟩ : syracuseStep 1194791 = 1792187) B1792187
theorem B13622093 : Blo 1194414 13622093 := bstep (se 3 (by rfl) ⟨2554142, by rfl⟩ : syracuseStep 13622093 = 5108285) B5108285
theorem B1194831 : Blo 1194414 1194831 := bstep (se 1 (by rfl) ⟨896123, by rfl⟩ : syracuseStep 1194831 = 1792247) B1792247
theorem B1194847 : Blo 1194414 1194847 := bstep (se 1 (by rfl) ⟨896135, by rfl⟩ : syracuseStep 1194847 = 1792271) B1792271
theorem B4037471 : Blo 1194414 4037471 := bstep (se 1 (by rfl) ⟨3028103, by rfl⟩ : syracuseStep 4037471 = 6056207) B6056207
theorem B9075563 : Blo 1194414 9075563 := bstep (se 1 (by rfl) ⟨6806672, by rfl⟩ : syracuseStep 9075563 = 13613345) B13613345
theorem B1194875 : Blo 1194414 1194875 := bstep (se 1 (by rfl) ⟨896156, by rfl⟩ : syracuseStep 1194875 = 1792313) B1792313
theorem B1194927 : Blo 1194414 1194927 := bstep (se 1 (by rfl) ⟨896195, by rfl⟩ : syracuseStep 1194927 = 1792391) B1792391
theorem B1792943 : Blo 1194414 1792943 := bstep (se 1 (by rfl) ⟨1344707, by rfl⟩ : syracuseStep 1792943 = 2689415) B2689415
theorem B2874295 : Blo 1194414 2874295 := bstep (se 1 (by rfl) ⟨2155721, by rfl⟩ : syracuseStep 2874295 = 4311443) B4311443
theorem B1194951 : Blo 1194414 1194951 := bstep (se 1 (by rfl) ⟨896213, by rfl⟩ : syracuseStep 1194951 = 1792427) B1792427
theorem B1194971 : Blo 1194414 1194971 := bstep (se 1 (by rfl) ⟨896228, by rfl⟩ : syracuseStep 1194971 = 1792457) B1792457
theorem B4037633 : Blo 1194414 4037633 := bstep (se 2 (by rfl) ⟨1514112, by rfl⟩ : syracuseStep 4037633 = 3028225) B3028225
theorem B1793033 : Blo 1194414 1793033 := bstep (se 2 (by rfl) ⟨672387, by rfl⟩ : syracuseStep 1793033 = 1344775) B1344775
theorem B1195047 : Blo 1194414 1195047 := bstep (se 1 (by rfl) ⟨896285, by rfl⟩ : syracuseStep 1195047 = 1792571) B1792571
theorem B1793063 : Blo 1194414 1793063 := bstep (se 1 (by rfl) ⟨1344797, by rfl⟩ : syracuseStep 1793063 = 2689595) B2689595
theorem B33135659 : Blo 1194414 33135659 := bstep (se 1 (by rfl) ⟨24851744, by rfl⟩ : syracuseStep 33135659 = 49703489) B49703489
theorem B1195087 : Blo 1194414 1195087 := bstep (se 1 (by rfl) ⟨896315, by rfl⟩ : syracuseStep 1195087 = 1792631) B1792631
theorem B1195103 : Blo 1194414 1195103 := bstep (se 1 (by rfl) ⟨896327, by rfl⟩ : syracuseStep 1195103 = 1792655) B1792655
theorem B1195131 : Blo 1194414 1195131 := bstep (se 1 (by rfl) ⟨896348, by rfl⟩ : syracuseStep 1195131 = 1792697) B1792697
theorem B1793147 : Blo 1194414 1793147 := bstep (se 1 (by rfl) ⟨1344860, by rfl⟩ : syracuseStep 1793147 = 2689721) B2689721
theorem B1703035 : Blo 1194414 1703035 := bstep (se 1 (by rfl) ⟨1277276, by rfl⟩ : syracuseStep 1703035 = 2554553) B2554553
theorem B1195183 : Blo 1194414 1195183 := bstep (se 1 (by rfl) ⟨896387, by rfl⟩ : syracuseStep 1195183 = 1792775) B1792775
theorem B7871681 : Blo 1194414 7871681 := bstep (se 2 (by rfl) ⟨2951880, by rfl⟩ : syracuseStep 7871681 = 5903761) B5903761
theorem B1195207 : Blo 1194414 1195207 := bstep (se 1 (by rfl) ⟨896405, by rfl⟩ : syracuseStep 1195207 = 1792811) B1792811
theorem B1195227 : Blo 1194414 1195227 := bstep (se 1 (by rfl) ⟨896420, by rfl⟩ : syracuseStep 1195227 = 1792841) B1792841
theorem B1793273 : Blo 1194414 1793273 := bstep (se 2 (by rfl) ⟨672477, by rfl⟩ : syracuseStep 1793273 = 1344955) B1344955
theorem B1195303 : Blo 1194414 1195303 := bstep (se 1 (by rfl) ⟨896477, by rfl⟩ : syracuseStep 1195303 = 1792955) B1792955
theorem B1940809 : Blo 1194414 1940809 := bstep (se 2 (by rfl) ⟨727803, by rfl⟩ : syracuseStep 1940809 = 1455607) B1455607
theorem B1195343 : Blo 1194414 1195343 := bstep (se 1 (by rfl) ⟨896507, by rfl⟩ : syracuseStep 1195343 = 1793015) B1793015
theorem B1195359 : Blo 1194414 1195359 := bstep (se 1 (by rfl) ⟨896519, by rfl⟩ : syracuseStep 1195359 = 1793039) B1793039
theorem B1793375 : Blo 1194414 1793375 := bstep (se 1 (by rfl) ⟨1345031, by rfl⟩ : syracuseStep 1793375 = 2690063) B2690063
theorem B1703263 : Blo 1194414 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B1793387 : Blo 1194414 1793387 := bstep (se 1 (by rfl) ⟨1345040, by rfl⟩ : syracuseStep 1793387 = 2690081) B2690081
theorem B1195387 : Blo 1194414 1195387 := bstep (se 1 (by rfl) ⟨896540, by rfl⟩ : syracuseStep 1195387 = 1793081) B1793081
theorem B1195439 : Blo 1194414 1195439 := bstep (se 1 (by rfl) ⟨896579, by rfl⟩ : syracuseStep 1195439 = 1793159) B1793159
theorem B1195463 : Blo 1194414 1195463 := bstep (se 1 (by rfl) ⟨896597, by rfl⟩ : syracuseStep 1195463 = 1793195) B1793195
theorem B8732123 : Blo 1194414 8732123 := bstep (se 1 (by rfl) ⟨6549092, by rfl⟩ : syracuseStep 8732123 = 13098185) B13098185
theorem B1195483 : Blo 1194414 1195483 := bstep (se 1 (by rfl) ⟨896612, by rfl⟩ : syracuseStep 1195483 = 1793225) B1793225
theorem B5103091 : Blo 1194414 5103091 := bstep (se 1 (by rfl) ⟨3827318, by rfl⟩ : syracuseStep 5103091 = 7654637) B7654637
theorem B7658995 : Blo 1194414 7658995 := bstep (se 1 (by rfl) ⟨5744246, by rfl⟩ : syracuseStep 7658995 = 11488493) B11488493
theorem B4537889 : Blo 1194414 4537889 := bstep (se 2 (by rfl) ⟨1701708, by rfl⟩ : syracuseStep 4537889 = 3403417) B3403417
theorem B1195559 : Blo 1194414 1195559 := bstep (se 1 (by rfl) ⟨896669, by rfl⟩ : syracuseStep 1195559 = 1793339) B1793339
theorem B13811239 : Blo 1194414 13811239 := bstep (se 1 (by rfl) ⟨10358429, by rfl⟩ : syracuseStep 13811239 = 20716859) B20716859
theorem B1195599 : Blo 1194414 1195599 := bstep (se 1 (by rfl) ⟨896699, by rfl⟩ : syracuseStep 1195599 = 1793399) B1793399
theorem B1793615 : Blo 1194414 1793615 := bstep (se 1 (by rfl) ⟨1345211, by rfl⟩ : syracuseStep 1793615 = 2690423) B2690423
theorem B1195615 : Blo 1194414 1195615 := bstep (se 1 (by rfl) ⟨896711, by rfl⟩ : syracuseStep 1195615 = 1793423) B1793423
theorem B1195643 : Blo 1194414 1195643 := bstep (se 1 (by rfl) ⟨896732, by rfl⟩ : syracuseStep 1195643 = 1793465) B1793465
theorem B1195695 : Blo 1194414 1195695 := bstep (se 1 (by rfl) ⟨896771, by rfl⟩ : syracuseStep 1195695 = 1793543) B1793543
theorem B1195719 : Blo 1194414 1195719 := bstep (se 1 (by rfl) ⟨896789, by rfl⟩ : syracuseStep 1195719 = 1793579) B1793579
theorem B1793735 : Blo 1194414 1793735 := bstep (se 1 (by rfl) ⟨1345301, by rfl⟩ : syracuseStep 1793735 = 2690603) B2690603
theorem B1195739 : Blo 1194414 1195739 := bstep (se 1 (by rfl) ⟨896804, by rfl⟩ : syracuseStep 1195739 = 1793609) B1793609
theorem B1195815 : Blo 1194414 1195815 := bstep (se 1 (by rfl) ⟨896861, by rfl⟩ : syracuseStep 1195815 = 1793723) B1793723
theorem B1195855 : Blo 1194414 1195855 := bstep (se 1 (by rfl) ⟨896891, by rfl⟩ : syracuseStep 1195855 = 1793783) B1793783
theorem B4538207 : Blo 1194414 4538207 := bstep (se 1 (by rfl) ⟨3403655, by rfl⟩ : syracuseStep 4538207 = 6807311) B6807311
theorem B1195871 : Blo 1194414 1195871 := bstep (se 1 (by rfl) ⟨896903, by rfl⟩ : syracuseStep 1195871 = 1793807) B1793807
theorem B1793897 : Blo 1194414 1793897 := bstep (se 2 (by rfl) ⟨672711, by rfl⟩ : syracuseStep 1793897 = 1345423) B1345423
theorem B2727787 : Blo 1194414 2727787 := bstep (se 1 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 2727787 = 4091681) B4091681
theorem B1195899 : Blo 1194414 1195899 := bstep (se 1 (by rfl) ⟨896924, by rfl⟩ : syracuseStep 1195899 = 1793849) B1793849
theorem B1195951 : Blo 1194414 1195951 := bstep (se 1 (by rfl) ⟨896963, by rfl⟩ : syracuseStep 1195951 = 1793927) B1793927
theorem B1793975 : Blo 1194414 1793975 := bstep (se 1 (by rfl) ⟨1345481, by rfl⟩ : syracuseStep 1793975 = 2690963) B2690963
theorem B1195975 : Blo 1194414 1195975 := bstep (se 1 (by rfl) ⟨896981, by rfl⟩ : syracuseStep 1195975 = 1793963) B1793963
theorem B1195995 : Blo 1194414 1195995 := bstep (se 1 (by rfl) ⟨896996, by rfl⟩ : syracuseStep 1195995 = 1793993) B1793993
theorem B1794011 : Blo 1194414 1794011 := bstep (se 1 (by rfl) ⟨1345508, by rfl⟩ : syracuseStep 1794011 = 2691017) B2691017
theorem B2588681 : Blo 1194414 2588681 := bstep (se 2 (by rfl) ⟨970755, by rfl⟩ : syracuseStep 2588681 = 1941511) B1941511
theorem B6053939 : Blo 1194414 6053939 := bstep (se 1 (by rfl) ⟨4540454, by rfl⟩ : syracuseStep 6053939 = 9080909) B9080909
theorem B1196319 : Blo 1194414 1196319 := bstep (se 1 (by rfl) ⟨897239, by rfl⟩ : syracuseStep 1196319 = 1794479) B1794479
theorem B1794395 : Blo 1194414 1794395 := bstep (se 1 (by rfl) ⟨1345796, by rfl⟩ : syracuseStep 1794395 = 2691593) B2691593
theorem B1196379 : Blo 1194414 1196379 := bstep (se 1 (by rfl) ⟨897284, by rfl⟩ : syracuseStep 1196379 = 1794569) B1794569
theorem B4088171 : Blo 1194414 4088171 := bstep (se 1 (by rfl) ⟨3066128, by rfl⟩ : syracuseStep 4088171 = 6132257) B6132257
theorem B1196399 : Blo 1194414 1196399 := bstep (se 1 (by rfl) ⟨897299, by rfl⟩ : syracuseStep 1196399 = 1794599) B1794599
theorem B1343911 : Blo 1194414 1343911 := bstep (se 1 (by rfl) ⟨1007933, by rfl⟩ : syracuseStep 1343911 = 2015867) B2015867
theorem B2802131 : Blo 1194414 2802131 := bstep (se 1 (by rfl) ⟨2101598, by rfl⟩ : syracuseStep 2802131 = 4203197) B4203197
theorem B2687507 : Blo 1194414 2687507 := bstep (se 1 (by rfl) ⟨2015630, by rfl⟩ : syracuseStep 2687507 = 4031261) B4031261
theorem B2687561 : Blo 1194414 2687561 := bstep (se 2 (by rfl) ⟨1007835, by rfl⟩ : syracuseStep 2687561 = 2015671) B2015671
theorem B5898905 : Blo 1194414 5898905 := bstep (se 2 (by rfl) ⟨2212089, by rfl⟩ : syracuseStep 5898905 = 4424179) B4424179
theorem B7570091 : Blo 1194414 7570091 := bstep (se 1 (by rfl) ⟨5677568, by rfl⟩ : syracuseStep 7570091 = 11355137) B11355137
theorem B6808313 : Blo 1194414 6808313 := bstep (se 2 (by rfl) ⟨2553117, by rfl⟩ : syracuseStep 6808313 = 5106235) B5106235
theorem B1532719 : Blo 1194414 1532719 := bstep (se 1 (by rfl) ⟨1149539, by rfl⟩ : syracuseStep 1532719 = 2299079) B2299079
theorem B5743439 : Blo 1194414 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B6636383 : Blo 1194414 6636383 := bstep (se 1 (by rfl) ⟨4977287, by rfl⟩ : syracuseStep 6636383 = 9954575) B9954575
theorem B5104579 : Blo 1194414 5104579 := bstep (se 1 (by rfl) ⟨3828434, by rfl⟩ : syracuseStep 5104579 = 7656869) B7656869
theorem B2687975 : Blo 1194414 2687975 := bstep (se 1 (by rfl) ⟨2015981, by rfl⟩ : syracuseStep 2687975 = 4031963) B4031963
theorem B1532903 : Blo 1194414 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B1344487 : Blo 1194414 1344487 := bstep (se 1 (by rfl) ⟨1008365, by rfl⟩ : syracuseStep 1344487 = 2016731) B2016731
theorem B4031585 : Blo 1194414 4031585 := bstep (se 2 (by rfl) ⟨1511844, by rfl⟩ : syracuseStep 4031585 = 3023689) B3023689
theorem B9077993 : Blo 1194414 9077993 := bstep (se 2 (by rfl) ⟨3404247, by rfl⟩ : syracuseStep 9077993 = 6808495) B6808495
theorem B4539635 : Blo 1194414 4539635 := bstep (se 1 (by rfl) ⟨3404726, by rfl⟩ : syracuseStep 4539635 = 6809453) B6809453
theorem B19383587 : Blo 1194414 19383587 := bstep (se 1 (by rfl) ⟨14537690, by rfl⟩ : syracuseStep 19383587 = 29075381) B29075381
theorem B2688353 : Blo 1194414 2688353 := bstep (se 2 (by rfl) ⟨1008132, by rfl⟩ : syracuseStep 2688353 = 2016265) B2016265
theorem B2688443 : Blo 1194414 2688443 := bstep (se 1 (by rfl) ⟨2016332, by rfl⟩ : syracuseStep 2688443 = 4032665) B4032665
theorem B6809021 : Blo 1194414 6809021 := bstep (se 3 (by rfl) ⟨1276691, by rfl⟩ : syracuseStep 6809021 = 2553383) B2553383
theorem B2688569 : Blo 1194414 2688569 := bstep (se 2 (by rfl) ⟨1008213, by rfl⟩ : syracuseStep 2688569 = 2016427) B2016427
theorem B3024479 : Blo 1194414 3024479 := bstep (se 1 (by rfl) ⟨2268359, by rfl⟩ : syracuseStep 3024479 = 4536719) B4536719
theorem B6055559 : Blo 1194414 6055559 := bstep (se 1 (by rfl) ⟨4541669, by rfl⟩ : syracuseStep 6055559 = 9083339) B9083339
theorem B10217117 : Blo 1194414 10217117 := bstep (se 3 (by rfl) ⟨1915709, by rfl⟩ : syracuseStep 10217117 = 3831419) B3831419
theorem B3229345 : Blo 1194414 3229345 := bstep (se 2 (by rfl) ⟨1211004, by rfl⟩ : syracuseStep 3229345 = 2422009) B2422009
theorem B2271017 : Blo 1194414 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B49727459 : Blo 1194414 49727459 := bstep (se 1 (by rfl) ⟨37295594, by rfl⟩ : syracuseStep 49727459 = 74591189) B74591189
theorem B31057901 : Blo 1194414 31057901 := bstep (se 3 (by rfl) ⟨5823356, by rfl⟩ : syracuseStep 31057901 = 11646713) B11646713
theorem B16345273 : Blo 1194414 16345273 := bstep (se 2 (by rfl) ⟨6129477, by rfl⟩ : syracuseStep 16345273 = 12258955) B12258955
theorem B2689235 : Blo 1194414 2689235 := bstep (se 1 (by rfl) ⟨2016926, by rfl⟩ : syracuseStep 2689235 = 4033853) B4033853
theorem B3401993 : Blo 1194414 3401993 := bstep (se 2 (by rfl) ⟨1275747, by rfl⟩ : syracuseStep 3401993 = 2551495) B2551495
theorem B2689289 : Blo 1194414 2689289 := bstep (se 2 (by rfl) ⟨1008483, by rfl⟩ : syracuseStep 2689289 = 2016967) B2016967
theorem B15329573 : Blo 1194414 15329573 := bstep (se 4 (by rfl) ⟨1437147, by rfl⟩ : syracuseStep 15329573 = 2874295) B2874295
theorem B3025259 : Blo 1194414 3025259 := bstep (se 1 (by rfl) ⟨2268944, by rfl⟩ : syracuseStep 3025259 = 4537889) B4537889
theorem B4032935 : Blo 1194414 4032935 := bstep (se 1 (by rfl) ⟨3024701, by rfl⟩ : syracuseStep 4032935 = 6049403) B6049403
theorem B2017703 : Blo 1194414 2017703 := bstep (se 1 (by rfl) ⟨1513277, by rfl⟩ : syracuseStep 2017703 = 3026555) B3026555
theorem B2689505 : Blo 1194414 2689505 := bstep (se 2 (by rfl) ⟨1008564, by rfl⟩ : syracuseStep 2689505 = 2017129) B2017129
theorem B3025471 : Blo 1194414 3025471 := bstep (se 1 (by rfl) ⟨2269103, by rfl⟩ : syracuseStep 3025471 = 4538207) B4538207
theorem B4033097 : Blo 1194414 4033097 := bstep (se 2 (by rfl) ⟨1512411, by rfl⟩ : syracuseStep 4033097 = 3024823) B3024823
theorem B2017865 : Blo 1194414 2017865 := bstep (se 2 (by rfl) ⟨756699, by rfl⟩ : syracuseStep 2017865 = 1513399) B1513399
theorem B6048431 : Blo 1194414 6048431 := bstep (se 1 (by rfl) ⟨4536323, by rfl⟩ : syracuseStep 6048431 = 9072647) B9072647
theorem B3025583 : Blo 1194414 3025583 := bstep (se 1 (by rfl) ⟨2269187, by rfl⟩ : syracuseStep 3025583 = 4538375) B4538375
theorem B4541123 : Blo 1194414 4541123 := bstep (se 1 (by rfl) ⟨3405842, by rfl⟩ : syracuseStep 4541123 = 6811685) B6811685
theorem B2689811 : Blo 1194414 2689811 := bstep (se 1 (by rfl) ⟨2017358, by rfl⟩ : syracuseStep 2689811 = 4034717) B4034717
theorem B6458255 : Blo 1194414 6458255 := bstep (se 1 (by rfl) ⟨4843691, by rfl⟩ : syracuseStep 6458255 = 9687383) B9687383
theorem B1362919 : Blo 1194414 1362919 := bstep (se 1 (by rfl) ⟨1022189, by rfl⟩ : syracuseStep 1362919 = 2044379) B2044379
theorem B6048755 : Blo 1194414 6048755 := bstep (se 1 (by rfl) ⟨4536566, by rfl⟩ : syracuseStep 6048755 = 9073133) B9073133
theorem B3025907 : Blo 1194414 3025907 := bstep (se 1 (by rfl) ⟨2269430, by rfl⟩ : syracuseStep 3025907 = 4538861) B4538861
theorem B5745745 : Blo 1194414 5745745 := bstep (se 2 (by rfl) ⟨2154654, by rfl⟩ : syracuseStep 5745745 = 4309309) B4309309
theorem B2690171 : Blo 1194414 2690171 := bstep (se 1 (by rfl) ⟨2017628, by rfl⟩ : syracuseStep 2690171 = 4035257) B4035257
theorem B4541579 : Blo 1194414 4541579 := bstep (se 1 (by rfl) ⟨3406184, by rfl⟩ : syracuseStep 4541579 = 6812369) B6812369
theorem B3026119 : Blo 1194414 3026119 := bstep (se 1 (by rfl) ⟨2269589, by rfl⟩ : syracuseStep 3026119 = 4539179) B4539179
theorem B2690297 : Blo 1194414 2690297 := bstep (se 2 (by rfl) ⟨1008861, by rfl⟩ : syracuseStep 2690297 = 2017723) B2017723
theorem B6810911 : Blo 1194414 6810911 := bstep (se 1 (by rfl) ⟨5108183, by rfl⟩ : syracuseStep 6810911 = 10216367) B10216367
theorem B2690441 : Blo 1194414 2690441 := bstep (se 2 (by rfl) ⟨1008915, by rfl⟩ : syracuseStep 2690441 = 2017831) B2017831
theorem B4369801 : Blo 1194414 4369801 := bstep (se 2 (by rfl) ⟨1638675, by rfl⟩ : syracuseStep 4369801 = 3277351) B3277351
theorem B2690567 : Blo 1194414 2690567 := bstep (se 1 (by rfl) ⟨2017925, by rfl⟩ : syracuseStep 2690567 = 4035851) B4035851
theorem B232771157 : Blo 1194414 232771157 := bstep (se 8 (by rfl) ⟨1363893, by rfl⟩ : syracuseStep 232771157 = 2727787) B2727787
theorem B2018911 : Blo 1194414 2018911 := bstep (se 1 (by rfl) ⟨1514183, by rfl⟩ : syracuseStep 2018911 = 3028367) B3028367
theorem B2690747 : Blo 1194414 2690747 := bstep (se 1 (by rfl) ⟨2018060, by rfl⟩ : syracuseStep 2690747 = 4036121) B4036121
theorem B2690873 : Blo 1194414 2690873 := bstep (se 2 (by rfl) ⟨1009077, by rfl⟩ : syracuseStep 2690873 = 2018155) B2018155
theorem B4427581 : Blo 1194414 4427581 := bstep (se 3 (by rfl) ⟨830171, by rfl⟩ : syracuseStep 4427581 = 1660343) B1660343
theorem B104730629 : Blo 1194414 104730629 := bstep (se 4 (by rfl) ⟨9818496, by rfl⟩ : syracuseStep 104730629 = 19636993) B19636993
theorem B3633257 : Blo 1194414 3633257 := bstep (se 2 (by rfl) ⟨1362471, by rfl⟩ : syracuseStep 3633257 = 2724943) B2724943
theorem B4034771 : Blo 1194414 4034771 := bstep (se 1 (by rfl) ⟨3026078, by rfl⟩ : syracuseStep 4034771 = 6052157) B6052157
theorem B6050051 : Blo 1194414 6050051 := bstep (se 1 (by rfl) ⟨4537538, by rfl⟩ : syracuseStep 6050051 = 9075077) B9075077
theorem B2691503 : Blo 1194414 2691503 := bstep (se 1 (by rfl) ⟨2018627, by rfl⟩ : syracuseStep 2691503 = 4037255) B4037255
theorem B2691539 : Blo 1194414 2691539 := bstep (se 1 (by rfl) ⟨2018654, by rfl⟩ : syracuseStep 2691539 = 4037309) B4037309
theorem B4035041 : Blo 1194414 4035041 := bstep (se 2 (by rfl) ⟨1513140, by rfl⟩ : syracuseStep 4035041 = 3026281) B3026281
theorem B9081395 : Blo 1194414 9081395 := bstep (se 1 (by rfl) ⟨6811046, by rfl⟩ : syracuseStep 9081395 = 13622093) B13622093
theorem B9687613 : Blo 1194414 9687613 := bstep (se 3 (by rfl) ⟨1816427, by rfl⟩ : syracuseStep 9687613 = 3632855) B3632855
theorem B2691647 : Blo 1194414 2691647 := bstep (se 1 (by rfl) ⟨2018735, by rfl⟩ : syracuseStep 2691647 = 4037471) B4037471
theorem B10220093 : Blo 1194414 10220093 := bstep (se 3 (by rfl) ⟨1916267, by rfl⟩ : syracuseStep 10220093 = 3832535) B3832535
theorem B6050375 : Blo 1194414 6050375 := bstep (se 1 (by rfl) ⟨4537781, by rfl⟩ : syracuseStep 6050375 = 9075563) B9075563
theorem B3027527 : Blo 1194414 3027527 := bstep (se 1 (by rfl) ⟨2270645, by rfl⟩ : syracuseStep 3027527 = 4541291) B4541291
theorem B2044523 : Blo 1194414 2044523 := bstep (se 1 (by rfl) ⟨1533392, by rfl⟩ : syracuseStep 2044523 = 3066785) B3066785
theorem B3027577 : Blo 1194414 3027577 := bstep (se 2 (by rfl) ⟨1135341, by rfl⟩ : syracuseStep 3027577 = 2270683) B2270683
theorem B6804121 : Blo 1194414 6804121 := bstep (se 2 (by rfl) ⟨2551545, by rfl⟩ : syracuseStep 6804121 = 5103091) B5103091
theorem B10211993 : Blo 1194414 10211993 := bstep (se 2 (by rfl) ⟨3829497, by rfl⟩ : syracuseStep 10211993 = 7658995) B7658995
theorem B2691755 : Blo 1194414 2691755 := bstep (se 1 (by rfl) ⟨2018816, by rfl⟩ : syracuseStep 2691755 = 4037633) B4037633
theorem B1913519 : Blo 1194414 1913519 := bstep (se 1 (by rfl) ⟨1435139, by rfl⟩ : syracuseStep 1913519 = 2870279) B2870279
theorem B22090439 : Blo 1194414 22090439 := bstep (se 1 (by rfl) ⟨16567829, by rfl⟩ : syracuseStep 22090439 = 33135659) B33135659
theorem B7664327 : Blo 1194414 7664327 := bstep (se 1 (by rfl) ⟨5748245, by rfl⟩ : syracuseStep 7664327 = 11496491) B11496491
theorem B5247787 : Blo 1194414 5247787 := bstep (se 1 (by rfl) ⟨3935840, by rfl⟩ : syracuseStep 5247787 = 7871681) B7871681
theorem B5821415 : Blo 1194414 5821415 := bstep (se 1 (by rfl) ⟨4366061, by rfl⟩ : syracuseStep 5821415 = 8732123) B8732123
theorem B6460505 : Blo 1194414 6460505 := bstep (se 2 (by rfl) ⟨2422689, by rfl⟩ : syracuseStep 6460505 = 4845379) B4845379
theorem B5108969 : Blo 1194414 5108969 := bstep (se 2 (by rfl) ⟨1915863, by rfl⟩ : syracuseStep 5108969 = 3831727) B3831727
theorem B9696953 : Blo 1194414 9696953 := bstep (se 2 (by rfl) ⟨3636357, by rfl⟩ : syracuseStep 9696953 = 7272715) B7272715
theorem B4036283 : Blo 1194414 4036283 := bstep (se 1 (by rfl) ⟨3027212, by rfl⟩ : syracuseStep 4036283 = 6054425) B6054425
theorem B1791785 : Blo 1194414 1791785 := bstep (se 2 (by rfl) ⟨671919, by rfl⟩ : syracuseStep 1791785 = 1343839) B1343839
theorem B1816361 : Blo 1194414 1816361 := bstep (se 2 (by rfl) ⟨681135, by rfl⟩ : syracuseStep 1816361 = 1362271) B1362271
theorem B1791791 : Blo 1194414 1791791 := bstep (se 1 (by rfl) ⟨1343843, by rfl⟩ : syracuseStep 1791791 = 2687687) B2687687
theorem B6051671 : Blo 1194414 6051671 := bstep (se 1 (by rfl) ⟨4538753, by rfl⟩ : syracuseStep 6051671 = 9077507) B9077507
theorem B22992821 : Blo 1194414 22992821 := bstep (se 5 (by rfl) ⟨1077788, by rfl⟩ : syracuseStep 22992821 = 2155577) B2155577
theorem B9082853 : Blo 1194414 9082853 := bstep (se 4 (by rfl) ⟨851517, by rfl⟩ : syracuseStep 9082853 = 1703035) B1703035
theorem B8615969 : Blo 1194414 8615969 := bstep (se 2 (by rfl) ⟨3230988, by rfl⟩ : syracuseStep 8615969 = 6461977) B6461977
theorem B2554067 : Blo 1194414 2554067 := bstep (se 1 (by rfl) ⟨1915550, by rfl⟩ : syracuseStep 2554067 = 3831101) B3831101
theorem B1792265 : Blo 1194414 1792265 := bstep (se 2 (by rfl) ⟨672099, by rfl⟩ : syracuseStep 1792265 = 1344199) B1344199
theorem B5749015 : Blo 1194414 5749015 := bstep (se 1 (by rfl) ⟨4311761, by rfl⟩ : syracuseStep 5749015 = 8623523) B8623523
theorem B1513819 : Blo 1194414 1513819 := bstep (se 1 (by rfl) ⟨1135364, by rfl⟩ : syracuseStep 1513819 = 2270729) B2270729
theorem B1792367 : Blo 1194414 1792367 := bstep (se 1 (by rfl) ⟨1344275, by rfl⟩ : syracuseStep 1792367 = 2688551) B2688551
theorem B6388079 : Blo 1194414 6388079 := bstep (se 1 (by rfl) ⟨4791059, by rfl⟩ : syracuseStep 6388079 = 9582119) B9582119
theorem B5454191 : Blo 1194414 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B2873711 : Blo 1194414 2873711 := bstep (se 1 (by rfl) ⟨2155283, by rfl⟩ : syracuseStep 2873711 = 4310567) B4310567
theorem B5110199 : Blo 1194414 5110199 := bstep (se 1 (by rfl) ⟨3832649, by rfl⟩ : syracuseStep 5110199 = 7665299) B7665299
theorem B1194491 : Blo 1194414 1194491 := bstep (se 1 (by rfl) ⟨895868, by rfl⟩ : syracuseStep 1194491 = 1791737) B1791737
theorem B44243489 : Blo 1194414 44243489 := bstep (se 2 (by rfl) ⟨16591308, by rfl⟩ : syracuseStep 44243489 = 33182617) B33182617
theorem B1194559 : Blo 1194414 1194559 := bstep (se 1 (by rfl) ⟨895919, by rfl⟩ : syracuseStep 1194559 = 1791839) B1791839
theorem B1514047 : Blo 1194414 1514047 := bstep (se 1 (by rfl) ⟨1135535, by rfl⟩ : syracuseStep 1514047 = 2271071) B2271071
theorem B1194567 : Blo 1194414 1194567 := bstep (se 1 (by rfl) ⟨895925, by rfl⟩ : syracuseStep 1194567 = 1791851) B1791851
theorem B1792583 : Blo 1194414 1792583 := bstep (se 1 (by rfl) ⟨1344437, by rfl⟩ : syracuseStep 1792583 = 2688875) B2688875
theorem B1792619 : Blo 1194414 1792619 := bstep (se 1 (by rfl) ⟨1344464, by rfl⟩ : syracuseStep 1792619 = 2688929) B2688929
theorem B5102203 : Blo 1194414 5102203 := bstep (se 1 (by rfl) ⟨3826652, by rfl⟩ : syracuseStep 5102203 = 7653305) B7653305
theorem B1194719 : Blo 1194414 1194719 := bstep (se 1 (by rfl) ⟨896039, by rfl⟩ : syracuseStep 1194719 = 1792079) B1792079
theorem B1194799 : Blo 1194414 1194799 := bstep (se 1 (by rfl) ⟨896099, by rfl⟩ : syracuseStep 1194799 = 1792199) B1792199
theorem B1792847 : Blo 1194414 1792847 := bstep (se 1 (by rfl) ⟨1344635, by rfl⟩ : syracuseStep 1792847 = 2689271) B2689271
theorem B1194907 : Blo 1194414 1194907 := bstep (se 1 (by rfl) ⟨896180, by rfl⟩ : syracuseStep 1194907 = 1792361) B1792361
theorem B2153387 : Blo 1194414 2153387 := bstep (se 1 (by rfl) ⟨1615040, by rfl⟩ : syracuseStep 2153387 = 3230081) B3230081
theorem B1194959 : Blo 1194414 1194959 := bstep (se 1 (by rfl) ⟨896219, by rfl⟩ : syracuseStep 1194959 = 1792439) B1792439
theorem B1194983 : Blo 1194414 1194983 := bstep (se 1 (by rfl) ⟨896237, by rfl⟩ : syracuseStep 1194983 = 1792475) B1792475
theorem B2587745 : Blo 1194414 2587745 := bstep (se 2 (by rfl) ⟨970404, by rfl⟩ : syracuseStep 2587745 = 1940809) B1940809
theorem B1793243 : Blo 1194414 1793243 := bstep (se 1 (by rfl) ⟨1344932, by rfl⟩ : syracuseStep 1793243 = 2689865) B2689865
theorem B1195295 : Blo 1194414 1195295 := bstep (se 1 (by rfl) ⟨896471, by rfl⟩ : syracuseStep 1195295 = 1792943) B1792943
theorem B1195355 : Blo 1194414 1195355 := bstep (se 1 (by rfl) ⟨896516, by rfl⟩ : syracuseStep 1195355 = 1793033) B1793033
theorem B1195375 : Blo 1194414 1195375 := bstep (se 1 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 1195375 = 1793063) B1793063
theorem B1793417 : Blo 1194414 1793417 := bstep (se 2 (by rfl) ⟨672531, by rfl⟩ : syracuseStep 1793417 = 1345063) B1345063
theorem B18414985 : Blo 1194414 18414985 := bstep (se 2 (by rfl) ⟨6905619, by rfl⟩ : syracuseStep 18414985 = 13811239) B13811239
theorem B1195431 : Blo 1194414 1195431 := bstep (se 1 (by rfl) ⟨896573, by rfl⟩ : syracuseStep 1195431 = 1793147) B1793147
theorem B13983191 : Blo 1194414 13983191 := bstep (se 1 (by rfl) ⟨10487393, by rfl⟩ : syracuseStep 13983191 = 20974787) B20974787
theorem B1195515 : Blo 1194414 1195515 := bstep (se 1 (by rfl) ⟨896636, by rfl⟩ : syracuseStep 1195515 = 1793273) B1793273
theorem B1195583 : Blo 1194414 1195583 := bstep (se 1 (by rfl) ⟨896687, by rfl⟩ : syracuseStep 1195583 = 1793375) B1793375
theorem B1195591 : Blo 1194414 1195591 := bstep (se 1 (by rfl) ⟨896693, by rfl⟩ : syracuseStep 1195591 = 1793387) B1793387
theorem B1195743 : Blo 1194414 1195743 := bstep (se 1 (by rfl) ⟨896807, by rfl⟩ : syracuseStep 1195743 = 1793615) B1793615
theorem B1793771 : Blo 1194414 1793771 := bstep (se 1 (by rfl) ⟨1345328, by rfl⟩ : syracuseStep 1793771 = 2690657) B2690657
theorem B6463273 : Blo 1194414 6463273 := bstep (se 2 (by rfl) ⟨2423727, by rfl⟩ : syracuseStep 6463273 = 4847455) B4847455
theorem B1195823 : Blo 1194414 1195823 := bstep (se 1 (by rfl) ⟨896867, by rfl⟩ : syracuseStep 1195823 = 1793735) B1793735
theorem B1195931 : Blo 1194414 1195931 := bstep (se 1 (by rfl) ⟨896948, by rfl⟩ : syracuseStep 1195931 = 1793897) B1793897
theorem B1195983 : Blo 1194414 1195983 := bstep (se 1 (by rfl) ⟨896987, by rfl⟩ : syracuseStep 1195983 = 1793975) B1793975
theorem B1793999 : Blo 1194414 1793999 := bstep (se 1 (by rfl) ⟨1345499, by rfl⟩ : syracuseStep 1793999 = 2690999) B2690999
theorem B1196007 : Blo 1194414 1196007 := bstep (se 1 (by rfl) ⟨897005, by rfl⟩ : syracuseStep 1196007 = 1794011) B1794011
theorem B279281677 : Blo 1194414 279281677 := bstep (se 3 (by rfl) ⟨52365314, by rfl⟩ : syracuseStep 279281677 = 104730629) B104730629
theorem B1196263 : Blo 1194414 1196263 := bstep (se 1 (by rfl) ⟨897197, by rfl⟩ : syracuseStep 1196263 = 1794395) B1794395
theorem B1794335 : Blo 1194414 1794335 := bstep (se 1 (by rfl) ⟨1345751, by rfl⟩ : syracuseStep 1794335 = 2691503) B2691503
theorem B1868087 : Blo 1194414 1868087 := bstep (se 1 (by rfl) ⟨1401065, by rfl⟩ : syracuseStep 1868087 = 2802131) B2802131
theorem B1794359 : Blo 1194414 1794359 := bstep (se 1 (by rfl) ⟨1345769, by rfl⟩ : syracuseStep 1794359 = 2691539) B2691539
theorem B6054263 : Blo 1194414 6054263 := bstep (se 1 (by rfl) ⟨4540697, by rfl⟩ : syracuseStep 6054263 = 9081395) B9081395
theorem B1794431 : Blo 1194414 1794431 := bstep (se 1 (by rfl) ⟨1345823, by rfl⟩ : syracuseStep 1794431 = 2691647) B2691647
theorem B3932603 : Blo 1194414 3932603 := bstep (se 1 (by rfl) ⟨2949452, by rfl⟩ : syracuseStep 3932603 = 5898905) B5898905
theorem B6807995 : Blo 1194414 6807995 := bstep (se 1 (by rfl) ⟨5105996, by rfl⟩ : syracuseStep 6807995 = 10211993) B10211993
theorem B1794503 : Blo 1194414 1794503 := bstep (se 1 (by rfl) ⟨1345877, by rfl⟩ : syracuseStep 1794503 = 2691755) B2691755
theorem B4538875 : Blo 1194414 4538875 := bstep (se 1 (by rfl) ⟨3404156, by rfl⟩ : syracuseStep 4538875 = 6808313) B6808313
theorem B4424255 : Blo 1194414 4424255 := bstep (se 1 (by rfl) ⟨3318191, by rfl⟩ : syracuseStep 4424255 = 6636383) B6636383
theorem B2687723 : Blo 1194414 2687723 := bstep (se 1 (by rfl) ⟨2015792, by rfl⟩ : syracuseStep 2687723 = 4031585) B4031585
theorem B4539347 : Blo 1194414 4539347 := bstep (se 1 (by rfl) ⟨3404510, by rfl⟩ : syracuseStep 4539347 = 6809021) B6809021
theorem B6997049 : Blo 1194414 6997049 := bstep (se 2 (by rfl) ⟨2623893, by rfl⟩ : syracuseStep 6997049 = 5247787) B5247787
theorem B2016319 : Blo 1194414 2016319 := bstep (se 1 (by rfl) ⟨1512239, by rfl⟩ : syracuseStep 2016319 = 3024479) B3024479
theorem B15328547 : Blo 1194414 15328547 := bstep (se 1 (by rfl) ⟨11496410, by rfl⟩ : syracuseStep 15328547 = 22992821) B22992821
theorem B6055235 : Blo 1194414 6055235 := bstep (se 1 (by rfl) ⟨4541426, by rfl⟩ : syracuseStep 6055235 = 9082853) B9082853
theorem B5743979 : Blo 1194414 5743979 := bstep (se 1 (by rfl) ⟨4307984, by rfl⟩ : syracuseStep 5743979 = 8615969) B8615969
theorem B7660993 : Blo 1194414 7660993 := bstep (se 2 (by rfl) ⟨2872872, by rfl⟩ : syracuseStep 7660993 = 5745745) B5745745
theorem B2016839 : Blo 1194414 2016839 := bstep (se 1 (by rfl) ⟨1512629, by rfl⟩ : syracuseStep 2016839 = 3025259) B3025259
theorem B2688623 : Blo 1194414 2688623 := bstep (se 1 (by rfl) ⟨2016467, by rfl⟩ : syracuseStep 2688623 = 4032935) B4032935
theorem B1345135 : Blo 1194414 1345135 := bstep (se 1 (by rfl) ⟨1008851, by rfl⟩ : syracuseStep 1345135 = 2017703) B2017703
theorem B2688731 : Blo 1194414 2688731 := bstep (se 1 (by rfl) ⟨2016548, by rfl⟩ : syracuseStep 2688731 = 4033097) B4033097
theorem B1345243 : Blo 1194414 1345243 := bstep (se 1 (by rfl) ⟨1008932, by rfl⟩ : syracuseStep 1345243 = 2017865) B2017865
theorem B20186909 : Blo 1194414 20186909 := bstep (se 3 (by rfl) ⟨3785045, by rfl⟩ : syracuseStep 20186909 = 7570091) B7570091
theorem B4032287 : Blo 1194414 4032287 := bstep (se 1 (by rfl) ⟨3024215, by rfl⟩ : syracuseStep 4032287 = 6048431) B6048431
theorem B2017055 : Blo 1194414 2017055 := bstep (se 1 (by rfl) ⟨1512791, by rfl⟩ : syracuseStep 2017055 = 3025583) B3025583
theorem B5826401 : Blo 1194414 5826401 := bstep (se 2 (by rfl) ⟨2184900, by rfl⟩ : syracuseStep 5826401 = 4369801) B4369801
theorem B24553313 : Blo 1194414 24553313 := bstep (se 2 (by rfl) ⟨9207492, by rfl⟩ : syracuseStep 24553313 = 18414985) B18414985
theorem B1435591 : Blo 1194414 1435591 := bstep (se 1 (by rfl) ⟨1076693, by rfl⟩ : syracuseStep 1435591 = 2153387) B2153387
theorem B4032503 : Blo 1194414 4032503 := bstep (se 1 (by rfl) ⟨3024377, by rfl⟩ : syracuseStep 4032503 = 6048755) B6048755
theorem B2017271 : Blo 1194414 2017271 := bstep (se 1 (by rfl) ⟨1512953, by rfl⟩ : syracuseStep 2017271 = 3025907) B3025907
theorem B6056045 : Blo 1194414 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B4540607 : Blo 1194414 4540607 := bstep (se 1 (by rfl) ⟨3405455, by rfl⟩ : syracuseStep 4540607 = 6810911) B6810911
theorem B2689847 : Blo 1194414 2689847 := bstep (se 1 (by rfl) ⟨2017385, by rfl⟩ : syracuseStep 2689847 = 4034771) B4034771
theorem B4033367 : Blo 1194414 4033367 := bstep (se 1 (by rfl) ⟨3025025, by rfl⟩ : syracuseStep 4033367 = 6050051) B6050051
theorem B21793697 : Blo 1194414 21793697 := bstep (se 2 (by rfl) ⟨8172636, by rfl⟩ : syracuseStep 21793697 = 16345273) B16345273
theorem B6900653 : Blo 1194414 6900653 := bstep (se 3 (by rfl) ⟨1293872, by rfl⟩ : syracuseStep 6900653 = 2587745) B2587745
theorem B2690027 : Blo 1194414 2690027 := bstep (se 1 (by rfl) ⟨2017520, by rfl⟩ : syracuseStep 2690027 = 4035041) B4035041
theorem B4033583 : Blo 1194414 4033583 := bstep (se 1 (by rfl) ⟨3025187, by rfl⟩ : syracuseStep 4033583 = 6050375) B6050375
theorem B2018351 : Blo 1194414 2018351 := bstep (se 1 (by rfl) ⟨1513763, by rfl⟩ : syracuseStep 2018351 = 3027527) B3027527
theorem B1363015 : Blo 1194414 1363015 := bstep (se 1 (by rfl) ⟨1022261, by rfl⟩ : syracuseStep 1363015 = 2044523) B2044523
theorem B2018425 : Blo 1194414 2018425 := bstep (se 2 (by rfl) ⟨756909, by rfl⟩ : syracuseStep 2018425 = 1513819) B1513819
theorem B3828959 : Blo 1194414 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B4033961 : Blo 1194414 4033961 := bstep (se 2 (by rfl) ⟨1512735, by rfl⟩ : syracuseStep 4033961 = 3025471) B3025471
theorem B2018729 : Blo 1194414 2018729 := bstep (se 2 (by rfl) ⟨757023, by rfl⟩ : syracuseStep 2018729 = 1514047) B1514047
theorem B3026423 : Blo 1194414 3026423 := bstep (se 1 (by rfl) ⟨2269817, by rfl⟩ : syracuseStep 3026423 = 4539635) B4539635
theorem B6802937 : Blo 1194414 6802937 := bstep (se 2 (by rfl) ⟨2551101, by rfl⟩ : syracuseStep 6802937 = 5102203) B5102203
theorem B12922391 : Blo 1194414 12922391 := bstep (se 1 (by rfl) ⟨9691793, by rfl⟩ : syracuseStep 12922391 = 19383587) B19383587
theorem B9072161 : Blo 1194414 9072161 := bstep (se 2 (by rfl) ⟨3402060, by rfl⟩ : syracuseStep 9072161 = 6804121) B6804121
theorem B17034877 : Blo 1194414 17034877 := bstep (se 3 (by rfl) ⟨3194039, by rfl⟩ : syracuseStep 17034877 = 6388079) B6388079
theorem B2043625 : Blo 1194414 2043625 := bstep (se 2 (by rfl) ⟨766359, by rfl⟩ : syracuseStep 2043625 = 1532719) B1532719
theorem B6811411 : Blo 1194414 6811411 := bstep (se 1 (by rfl) ⟨5108558, by rfl⟩ : syracuseStep 6811411 = 10217117) B10217117
theorem B2690855 : Blo 1194414 2690855 := bstep (se 1 (by rfl) ⟨2018141, by rfl⟩ : syracuseStep 2690855 = 4036283) B4036283
theorem B4034447 : Blo 1194414 4034447 := bstep (se 1 (by rfl) ⟨3025835, by rfl⟩ : syracuseStep 4034447 = 6051671) B6051671
theorem B20705267 : Blo 1194414 20705267 := bstep (se 1 (by rfl) ⟨15528950, by rfl⟩ : syracuseStep 20705267 = 31057901) B31057901
theorem B10219715 : Blo 1194414 10219715 := bstep (se 1 (by rfl) ⟨7664786, by rfl⟩ : syracuseStep 10219715 = 15329573) B15329573
theorem B4034825 : Blo 1194414 4034825 := bstep (se 2 (by rfl) ⟨1513059, by rfl⟩ : syracuseStep 4034825 = 3026119) B3026119
theorem B29495659 : Blo 1194414 29495659 := bstep (se 1 (by rfl) ⟨22121744, by rfl⟩ : syracuseStep 29495659 = 44243489) B44243489
theorem B3027415 : Blo 1194414 3027415 := bstep (se 1 (by rfl) ⟨2270561, by rfl⟩ : syracuseStep 3027415 = 4541123) B4541123
theorem B25858541 : Blo 1194414 25858541 := bstep (se 3 (by rfl) ⟨4848476, by rfl⟩ : syracuseStep 25858541 = 9696953) B9696953
theorem B4305503 : Blo 1194414 4305503 := bstep (se 1 (by rfl) ⟨3229127, by rfl⟩ : syracuseStep 4305503 = 6458255) B6458255
theorem B3027719 : Blo 1194414 3027719 := bstep (se 1 (by rfl) ⟨2270789, by rfl⟩ : syracuseStep 3027719 = 4541579) B4541579
theorem B2691881 : Blo 1194414 2691881 := bstep (se 2 (by rfl) ⟨1009455, by rfl⟩ : syracuseStep 2691881 = 2018911) B2018911
theorem B4305793 : Blo 1194414 4305793 := bstep (se 2 (by rfl) ⟨1614672, by rfl⟩ : syracuseStep 4305793 = 3229345) B3229345
theorem B5903441 : Blo 1194414 5903441 := bstep (se 2 (by rfl) ⟨2213790, by rfl⟩ : syracuseStep 5903441 = 4427581) B4427581
theorem B1725787 : Blo 1194414 1725787 := bstep (se 1 (by rfl) ⟨1294340, by rfl⟩ : syracuseStep 1725787 = 2588681) B2588681
theorem B4035959 : Blo 1194414 4035959 := bstep (se 1 (by rfl) ⟨3026969, by rfl⟩ : syracuseStep 4035959 = 6053939) B6053939
theorem B2422171 : Blo 1194414 2422171 := bstep (se 1 (by rfl) ⟨1816628, by rfl⟩ : syracuseStep 2422171 = 3633257) B3633257
theorem B2725447 : Blo 1194414 2725447 := bstep (se 1 (by rfl) ⟨2044085, by rfl⟩ : syracuseStep 2725447 = 4088171) B4088171
theorem B1791671 : Blo 1194414 1791671 := bstep (se 1 (by rfl) ⟨1343753, by rfl⟩ : syracuseStep 1791671 = 2687507) B2687507
theorem B7665353 : Blo 1194414 7665353 := bstep (se 2 (by rfl) ⟨2874507, by rfl⟩ : syracuseStep 7665353 = 5749015) B5749015
theorem B6813395 : Blo 1194414 6813395 := bstep (se 1 (by rfl) ⟨5110046, by rfl⟩ : syracuseStep 6813395 = 10220093) B10220093
theorem B1791707 : Blo 1194414 1791707 := bstep (se 1 (by rfl) ⟨1343780, by rfl⟩ : syracuseStep 1791707 = 2687561) B2687561
theorem B1275679 : Blo 1194414 1275679 := bstep (se 1 (by rfl) ⟨956759, by rfl⟩ : syracuseStep 1275679 = 1913519) B1913519
theorem B5109551 : Blo 1194414 5109551 := bstep (se 1 (by rfl) ⟨3832163, by rfl⟩ : syracuseStep 5109551 = 7664327) B7664327
theorem B1791881 : Blo 1194414 1791881 := bstep (se 2 (by rfl) ⟨671955, by rfl⟩ : syracuseStep 1791881 = 1343911) B1343911
theorem B1791983 : Blo 1194414 1791983 := bstep (se 1 (by rfl) ⟨1343987, by rfl⟩ : syracuseStep 1791983 = 2687975) B2687975
theorem B3880943 : Blo 1194414 3880943 := bstep (se 1 (by rfl) ⟨2910707, by rfl⟩ : syracuseStep 3880943 = 5821415) B5821415
theorem B4307003 : Blo 1194414 4307003 := bstep (se 1 (by rfl) ⟨3230252, by rfl⟩ : syracuseStep 4307003 = 6460505) B6460505
theorem B12916817 : Blo 1194414 12916817 := bstep (se 2 (by rfl) ⟨4843806, by rfl⟩ : syracuseStep 12916817 = 9687613) B9687613
theorem B6051995 : Blo 1194414 6051995 := bstep (se 1 (by rfl) ⟨4538996, by rfl⟩ : syracuseStep 6051995 = 9077993) B9077993
theorem B3405979 : Blo 1194414 3405979 := bstep (se 1 (by rfl) ⟨2554484, by rfl⟩ : syracuseStep 3405979 = 5108969) B5108969
theorem B4036769 : Blo 1194414 4036769 := bstep (se 2 (by rfl) ⟨1513788, by rfl⟩ : syracuseStep 4036769 = 3027577) B3027577
theorem B1792235 : Blo 1194414 1792235 := bstep (se 1 (by rfl) ⟨1344176, by rfl⟩ : syracuseStep 1792235 = 2688353) B2688353
theorem B1792295 : Blo 1194414 1792295 := bstep (se 1 (by rfl) ⟨1344221, by rfl⟩ : syracuseStep 1792295 = 2688443) B2688443
theorem B1792379 : Blo 1194414 1792379 := bstep (se 1 (by rfl) ⟨1344284, by rfl⟩ : syracuseStep 1792379 = 2688569) B2688569
theorem B4037039 : Blo 1194414 4037039 := bstep (se 1 (by rfl) ⟨3027779, by rfl⟩ : syracuseStep 4037039 = 6055559) B6055559
theorem B1194523 : Blo 1194414 1194523 := bstep (se 1 (by rfl) ⟨895892, by rfl⟩ : syracuseStep 1194523 = 1791785) B1791785
theorem B1210907 : Blo 1194414 1210907 := bstep (se 1 (by rfl) ⟨908180, by rfl⟩ : syracuseStep 1210907 = 1816361) B1816361
theorem B1194527 : Blo 1194414 1194527 := bstep (se 1 (by rfl) ⟨895895, by rfl⟩ : syracuseStep 1194527 = 1791791) B1791791
theorem B6806105 : Blo 1194414 6806105 := bstep (se 2 (by rfl) ⟨2552289, by rfl⟩ : syracuseStep 6806105 = 5104579) B5104579
theorem B1792649 : Blo 1194414 1792649 := bstep (se 2 (by rfl) ⟨672243, by rfl⟩ : syracuseStep 1792649 = 1344487) B1344487
theorem B1817225 : Blo 1194414 1817225 := bstep (se 2 (by rfl) ⟨681459, by rfl⟩ : syracuseStep 1817225 = 1362919) B1362919
theorem B33151639 : Blo 1194414 33151639 := bstep (se 1 (by rfl) ⟨24863729, by rfl⟩ : syracuseStep 33151639 = 49727459) B49727459
theorem B1792823 : Blo 1194414 1792823 := bstep (se 1 (by rfl) ⟨1344617, by rfl⟩ : syracuseStep 1792823 = 2689235) B2689235
theorem B1702711 : Blo 1194414 1702711 := bstep (se 1 (by rfl) ⟨1277033, by rfl⟩ : syracuseStep 1702711 = 2554067) B2554067
theorem B2267995 : Blo 1194414 2267995 := bstep (se 1 (by rfl) ⟨1700996, by rfl⟩ : syracuseStep 2267995 = 3401993) B3401993
theorem B1194843 : Blo 1194414 1194843 := bstep (se 1 (by rfl) ⟨896132, by rfl⟩ : syracuseStep 1194843 = 1792265) B1792265
theorem B1792859 : Blo 1194414 1792859 := bstep (se 1 (by rfl) ⟨1344644, by rfl⟩ : syracuseStep 1792859 = 2689289) B2689289
theorem B1194911 : Blo 1194414 1194911 := bstep (se 1 (by rfl) ⟨896183, by rfl⟩ : syracuseStep 1194911 = 1792367) B1792367
theorem B3636127 : Blo 1194414 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B1915807 : Blo 1194414 1915807 := bstep (se 1 (by rfl) ⟨1436855, by rfl⟩ : syracuseStep 1915807 = 2873711) B2873711
theorem B3406799 : Blo 1194414 3406799 := bstep (se 1 (by rfl) ⟨2555099, by rfl⟩ : syracuseStep 3406799 = 5110199) B5110199
theorem B1793003 : Blo 1194414 1793003 := bstep (se 1 (by rfl) ⟨1344752, by rfl⟩ : syracuseStep 1793003 = 2689505) B2689505
theorem B1195055 : Blo 1194414 1195055 := bstep (se 1 (by rfl) ⟨896291, by rfl⟩ : syracuseStep 1195055 = 1792583) B1792583
theorem B1195079 : Blo 1194414 1195079 := bstep (se 1 (by rfl) ⟨896309, by rfl⟩ : syracuseStep 1195079 = 1792619) B1792619
theorem B1793207 : Blo 1194414 1793207 := bstep (se 1 (by rfl) ⟨1344905, by rfl⟩ : syracuseStep 1793207 = 2689811) B2689811
theorem B58907837 : Blo 1194414 58907837 := bstep (se 3 (by rfl) ⟨11045219, by rfl⟩ : syracuseStep 58907837 = 22090439) B22090439
theorem B1195231 : Blo 1194414 1195231 := bstep (se 1 (by rfl) ⟨896423, by rfl⟩ : syracuseStep 1195231 = 1792847) B1792847
theorem B1793447 : Blo 1194414 1793447 := bstep (se 1 (by rfl) ⟨1345085, by rfl⟩ : syracuseStep 1793447 = 2690171) B2690171
theorem B1195495 : Blo 1194414 1195495 := bstep (se 1 (by rfl) ⟨896621, by rfl⟩ : syracuseStep 1195495 = 1793243) B1793243
theorem B1793531 : Blo 1194414 1793531 := bstep (se 1 (by rfl) ⟨1345148, by rfl⟩ : syracuseStep 1793531 = 2690297) B2690297
theorem B1195611 : Blo 1194414 1195611 := bstep (se 1 (by rfl) ⟨896708, by rfl⟩ : syracuseStep 1195611 = 1793417) B1793417
theorem B1793627 : Blo 1194414 1793627 := bstep (se 1 (by rfl) ⟨1345220, by rfl⟩ : syracuseStep 1793627 = 2690441) B2690441
theorem B9322127 : Blo 1194414 9322127 := bstep (se 1 (by rfl) ⟨6991595, by rfl⟩ : syracuseStep 9322127 = 13983191) B13983191
theorem B1793711 : Blo 1194414 1793711 := bstep (se 1 (by rfl) ⟨1345283, by rfl⟩ : syracuseStep 1793711 = 2690567) B2690567
theorem B8617697 : Blo 1194414 8617697 := bstep (se 2 (by rfl) ⟨3231636, by rfl⟩ : syracuseStep 8617697 = 6463273) B6463273
theorem B155180771 : Blo 1194414 155180771 := bstep (se 1 (by rfl) ⟨116385578, by rfl⟩ : syracuseStep 155180771 = 232771157) B232771157
theorem B1793831 : Blo 1194414 1793831 := bstep (se 1 (by rfl) ⟨1345373, by rfl⟩ : syracuseStep 1793831 = 2690747) B2690747
theorem B1195847 : Blo 1194414 1195847 := bstep (se 1 (by rfl) ⟨896885, by rfl⟩ : syracuseStep 1195847 = 1793771) B1793771
theorem B1793915 : Blo 1194414 1793915 := bstep (se 1 (by rfl) ⟨1345436, by rfl⟩ : syracuseStep 1793915 = 2690873) B2690873
theorem B4087741 : Blo 1194414 4087741 := bstep (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) B1532903
theorem B1195999 : Blo 1194414 1195999 := bstep (se 1 (by rfl) ⟨896999, by rfl⟩ : syracuseStep 1195999 = 1793999) B1793999
theorem B372375569 : Blo 1194414 372375569 := bstep (se 2 (by rfl) ⟨139640838, by rfl⟩ : syracuseStep 372375569 = 279281677) B279281677
theorem B1196223 : Blo 1194414 1196223 := bstep (se 1 (by rfl) ⟨897167, by rfl⟩ : syracuseStep 1196223 = 1794335) B1794335
theorem B1196239 : Blo 1194414 1196239 := bstep (se 1 (by rfl) ⟨897179, by rfl⟩ : syracuseStep 1196239 = 1794359) B1794359
theorem B1196287 : Blo 1194414 1196287 := bstep (se 1 (by rfl) ⟨897215, by rfl⟩ : syracuseStep 1196287 = 1794431) B1794431
theorem B2621735 : Blo 1194414 2621735 := bstep (se 1 (by rfl) ⟨1966301, by rfl⟩ : syracuseStep 2621735 = 3932603) B3932603
theorem B4538663 : Blo 1194414 4538663 := bstep (se 1 (by rfl) ⟨3403997, by rfl⟩ : syracuseStep 4538663 = 6807995) B6807995
theorem B1196335 : Blo 1194414 1196335 := bstep (se 1 (by rfl) ⟨897251, by rfl⟩ : syracuseStep 1196335 = 1794503) B1794503
theorem B2949503 : Blo 1194414 2949503 := bstep (se 1 (by rfl) ⟨2212127, by rfl⟩ : syracuseStep 2949503 = 4424255) B4424255
theorem B1794587 : Blo 1194414 1794587 := bstep (se 1 (by rfl) ⟨1345940, by rfl⟩ : syracuseStep 1794587 = 2691881) B2691881
theorem B4981565 : Blo 1194414 4981565 := bstep (se 3 (by rfl) ⟨934043, by rfl⟩ : syracuseStep 4981565 = 1868087) B1868087
theorem B1344559 : Blo 1194414 1344559 := bstep (se 1 (by rfl) ⟨1008419, by rfl⟩ : syracuseStep 1344559 = 2016839) B2016839
theorem B2270281 : Blo 1194414 2270281 := bstep (se 2 (by rfl) ⟨851355, by rfl⟩ : syracuseStep 2270281 = 1702711) B1702711
theorem B3023993 : Blo 1194414 3023993 := bstep (se 2 (by rfl) ⟨1133997, by rfl⟩ : syracuseStep 3023993 = 2267995) B2267995
theorem B2688191 : Blo 1194414 2688191 := bstep (se 1 (by rfl) ⟨2016143, by rfl⟩ : syracuseStep 2688191 = 4032287) B4032287
theorem B1344703 : Blo 1194414 1344703 := bstep (se 1 (by rfl) ⟨1008527, by rfl⟩ : syracuseStep 1344703 = 2017055) B2017055
theorem B3884267 : Blo 1194414 3884267 := bstep (se 1 (by rfl) ⟨2913200, by rfl⟩ : syracuseStep 3884267 = 5826401) B5826401
theorem B16368875 : Blo 1194414 16368875 := bstep (se 1 (by rfl) ⟨12276656, by rfl⟩ : syracuseStep 16368875 = 24553313) B24553313
theorem B2688335 : Blo 1194414 2688335 := bstep (se 1 (by rfl) ⟨2016251, by rfl⟩ : syracuseStep 2688335 = 4032503) B4032503
theorem B1344847 : Blo 1194414 1344847 := bstep (se 1 (by rfl) ⟨1008635, by rfl⟩ : syracuseStep 1344847 = 2017271) B2017271
theorem B8611211 : Blo 1194414 8611211 := bstep (se 1 (by rfl) ⟨6458408, by rfl⟩ : syracuseStep 8611211 = 12916817) B12916817
theorem B3229085 : Blo 1194414 3229085 := bstep (se 3 (by rfl) ⟨605453, by rfl⟩ : syracuseStep 3229085 = 1210907) B1210907
theorem B2688425 : Blo 1194414 2688425 := bstep (se 2 (by rfl) ⟨1008159, by rfl⟩ : syracuseStep 2688425 = 2016319) B2016319
theorem B3229561 : Blo 1194414 3229561 := bstep (se 2 (by rfl) ⟨1211085, by rfl⟩ : syracuseStep 3229561 = 2422171) B2422171
theorem B2688911 : Blo 1194414 2688911 := bstep (se 1 (by rfl) ⟨2016683, by rfl⟩ : syracuseStep 2688911 = 4033367) B4033367
theorem B2689055 : Blo 1194414 2689055 := bstep (se 1 (by rfl) ⟨2016791, by rfl⟩ : syracuseStep 2689055 = 4033583) B4033583
theorem B1345567 : Blo 1194414 1345567 := bstep (se 1 (by rfl) ⟨1009175, by rfl⟩ : syracuseStep 1345567 = 2018351) B2018351
theorem B2689307 : Blo 1194414 2689307 := bstep (se 1 (by rfl) ⟨2016980, by rfl⟩ : syracuseStep 2689307 = 4033961) B4033961
theorem B1345819 : Blo 1194414 1345819 := bstep (se 1 (by rfl) ⟨1009364, by rfl⟩ : syracuseStep 1345819 = 2018729) B2018729
theorem B2017615 : Blo 1194414 2017615 := bstep (se 1 (by rfl) ⟨1513211, by rfl⟩ : syracuseStep 2017615 = 3026423) B3026423
theorem B6048107 : Blo 1194414 6048107 := bstep (se 1 (by rfl) ⟨4536080, by rfl⟩ : syracuseStep 6048107 = 9072161) B9072161
theorem B5745131 : Blo 1194414 5745131 := bstep (se 1 (by rfl) ⟨4308848, by rfl⟩ : syracuseStep 5745131 = 8617697) B8617697
theorem B5450321 : Blo 1194414 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B2689631 : Blo 1194414 2689631 := bstep (se 1 (by rfl) ⟨2017223, by rfl⟩ : syracuseStep 2689631 = 4034447) B4034447
theorem B2689883 : Blo 1194414 2689883 := bstep (se 1 (by rfl) ⟨2017412, by rfl⟩ : syracuseStep 2689883 = 4034825) B4034825
theorem B4541305 : Blo 1194414 4541305 := bstep (se 2 (by rfl) ⟨1702989, by rfl⟩ : syracuseStep 4541305 = 3405979) B3405979
theorem B17239027 : Blo 1194414 17239027 := bstep (se 1 (by rfl) ⟨12929270, by rfl⟩ : syracuseStep 17239027 = 25858541) B25858541
theorem B2870335 : Blo 1194414 2870335 := bstep (se 1 (by rfl) ⟨2152751, by rfl⟩ : syracuseStep 2870335 = 4305503) B4305503
theorem B2018479 : Blo 1194414 2018479 := bstep (se 1 (by rfl) ⟨1513859, by rfl⟩ : syracuseStep 2018479 = 3027719) B3027719
theorem B3026231 : Blo 1194414 3026231 := bstep (se 1 (by rfl) ⟨2269673, by rfl⟩ : syracuseStep 3026231 = 4539347) B4539347
theorem B4664699 : Blo 1194414 4664699 := bstep (se 1 (by rfl) ⟨3498524, by rfl⟩ : syracuseStep 4664699 = 6997049) B6997049
theorem B3935627 : Blo 1194414 3935627 := bstep (se 1 (by rfl) ⟨2951720, by rfl⟩ : syracuseStep 3935627 = 5903441) B5903441
theorem B10219031 : Blo 1194414 10219031 := bstep (se 1 (by rfl) ⟨7664273, by rfl⟩ : syracuseStep 10219031 = 15328547) B15328547
theorem B3829319 : Blo 1194414 3829319 := bstep (se 1 (by rfl) ⟨2871989, by rfl⟩ : syracuseStep 3829319 = 5743979) B5743979
theorem B2690639 : Blo 1194414 2690639 := bstep (se 1 (by rfl) ⟨2017979, by rfl⟩ : syracuseStep 2690639 = 4035959) B4035959
theorem B4542263 : Blo 1194414 4542263 := bstep (se 1 (by rfl) ⟨3406697, by rfl⟩ : syracuseStep 4542263 = 6813395) B6813395
theorem B2871335 : Blo 1194414 2871335 := bstep (se 1 (by rfl) ⟨2153501, by rfl⟩ : syracuseStep 2871335 = 4307003) B4307003
theorem B4034663 : Blo 1194414 4034663 := bstep (se 1 (by rfl) ⟨3025997, by rfl⟩ : syracuseStep 4034663 = 6051995) B6051995
theorem B2691179 : Blo 1194414 2691179 := bstep (se 1 (by rfl) ⟨2018384, by rfl⟩ : syracuseStep 2691179 = 4036769) B4036769
theorem B3027071 : Blo 1194414 3027071 := bstep (se 1 (by rfl) ⟨2270303, by rfl⟩ : syracuseStep 3027071 = 4540607) B4540607
theorem B2691233 : Blo 1194414 2691233 := bstep (se 2 (by rfl) ⟨1009212, by rfl⟩ : syracuseStep 2691233 = 2018425) B2018425
theorem B6803621 : Blo 1194414 6803621 := bstep (se 4 (by rfl) ⟨637839, by rfl⟩ : syracuseStep 6803621 = 1275679) B1275679
theorem B2691359 : Blo 1194414 2691359 := bstep (se 1 (by rfl) ⟨2018519, by rfl⟩ : syracuseStep 2691359 = 4037039) B4037039
theorem B14529131 : Blo 1194414 14529131 := bstep (se 1 (by rfl) ⟨10896848, by rfl⟩ : syracuseStep 14529131 = 21793697) B21793697
theorem B4600435 : Blo 1194414 4600435 := bstep (se 1 (by rfl) ⟨3450326, by rfl⟩ : syracuseStep 4600435 = 6900653) B6900653
theorem B3633929 : Blo 1194414 3633929 := bstep (se 2 (by rfl) ⟨1362723, by rfl⟩ : syracuseStep 3633929 = 2725447) B2725447
theorem B2552639 : Blo 1194414 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B22713169 : Blo 1194414 22713169 := bstep (se 2 (by rfl) ⟨8517438, by rfl⟩ : syracuseStep 22713169 = 17034877) B17034877
theorem B2724833 : Blo 1194414 2724833 := bstep (se 2 (by rfl) ⟨1021812, by rfl⟩ : syracuseStep 2724833 = 2043625) B2043625
theorem B4535291 : Blo 1194414 4535291 := bstep (se 1 (by rfl) ⟨3401468, by rfl⟩ : syracuseStep 4535291 = 6802937) B6802937
theorem B8614927 : Blo 1194414 8614927 := bstep (se 1 (by rfl) ⟨6461195, by rfl⟩ : syracuseStep 8614927 = 12922391) B12922391
theorem B9081881 : Blo 1194414 9081881 := bstep (se 2 (by rfl) ⟨3405705, by rfl⟩ : syracuseStep 9081881 = 6811411) B6811411
theorem B6214751 : Blo 1194414 6214751 := bstep (se 1 (by rfl) ⟨4661063, by rfl⟩ : syracuseStep 6214751 = 9322127) B9322127
theorem B103453847 : Blo 1194414 103453847 := bstep (se 1 (by rfl) ⟨77590385, by rfl⟩ : syracuseStep 103453847 = 155180771) B155180771
theorem B1914121 : Blo 1194414 1914121 := bstep (se 2 (by rfl) ⟨717795, by rfl⟩ : syracuseStep 1914121 = 1435591) B1435591
theorem B6813143 : Blo 1194414 6813143 := bstep (se 1 (by rfl) ⟨5109857, by rfl⟩ : syracuseStep 6813143 = 10219715) B10219715
theorem B4036175 : Blo 1194414 4036175 := bstep (se 1 (by rfl) ⟨3027131, by rfl⟩ : syracuseStep 4036175 = 6054263) B6054263
theorem B39327545 : Blo 1194414 39327545 := bstep (se 2 (by rfl) ⟨14747829, by rfl⟩ : syracuseStep 39327545 = 29495659) B29495659
theorem B1791815 : Blo 1194414 1791815 := bstep (se 1 (by rfl) ⟨1343861, by rfl⟩ : syracuseStep 1791815 = 2687723) B2687723
theorem B4036553 : Blo 1194414 4036553 := bstep (se 2 (by rfl) ⟨1513707, by rfl⟩ : syracuseStep 4036553 = 3027415) B3027415
theorem B6051833 : Blo 1194414 6051833 := bstep (se 2 (by rfl) ⟨2269437, by rfl⟩ : syracuseStep 6051833 = 4538875) B4538875
theorem B44202185 : Blo 1194414 44202185 := bstep (se 2 (by rfl) ⟨16575819, by rfl⟩ : syracuseStep 44202185 = 33151639) B33151639
theorem B4036823 : Blo 1194414 4036823 := bstep (se 1 (by rfl) ⟨3027617, by rfl⟩ : syracuseStep 4036823 = 6055235) B6055235
theorem B1792415 : Blo 1194414 1792415 := bstep (se 1 (by rfl) ⟨1344311, by rfl⟩ : syracuseStep 1792415 = 2688623) B2688623
theorem B1194447 : Blo 1194414 1194447 := bstep (se 1 (by rfl) ⟨895835, by rfl⟩ : syracuseStep 1194447 = 1791671) B1791671
theorem B5110235 : Blo 1194414 5110235 := bstep (se 1 (by rfl) ⟨3832676, by rfl⟩ : syracuseStep 5110235 = 7665353) B7665353
theorem B1194471 : Blo 1194414 1194471 := bstep (se 1 (by rfl) ⟨895853, by rfl⟩ : syracuseStep 1194471 = 1791707) B1791707
theorem B1792487 : Blo 1194414 1792487 := bstep (se 1 (by rfl) ⟨1344365, by rfl⟩ : syracuseStep 1792487 = 2688731) B2688731
theorem B5741057 : Blo 1194414 5741057 := bstep (se 2 (by rfl) ⟨2152896, by rfl⟩ : syracuseStep 5741057 = 4305793) B4305793
theorem B13457939 : Blo 1194414 13457939 := bstep (se 1 (by rfl) ⟨10093454, by rfl⟩ : syracuseStep 13457939 = 20186909) B20186909
theorem B3406367 : Blo 1194414 3406367 := bstep (se 1 (by rfl) ⟨2554775, by rfl⟩ : syracuseStep 3406367 = 5109551) B5109551
theorem B4848169 : Blo 1194414 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B2554409 : Blo 1194414 2554409 := bstep (se 2 (by rfl) ⟨957903, by rfl⟩ : syracuseStep 2554409 = 1915807) B1915807
theorem B1194587 : Blo 1194414 1194587 := bstep (se 1 (by rfl) ⟨895940, by rfl⟩ : syracuseStep 1194587 = 1791881) B1791881
theorem B2587295 : Blo 1194414 2587295 := bstep (se 1 (by rfl) ⟨1940471, by rfl⟩ : syracuseStep 2587295 = 3880943) B3880943
theorem B1194655 : Blo 1194414 1194655 := bstep (se 1 (by rfl) ⟨895991, by rfl⟩ : syracuseStep 1194655 = 1791983) B1791983
theorem B4037363 : Blo 1194414 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B1817353 : Blo 1194414 1817353 := bstep (se 2 (by rfl) ⟨681507, by rfl⟩ : syracuseStep 1817353 = 1363015) B1363015
theorem B1194823 : Blo 1194414 1194823 := bstep (se 1 (by rfl) ⟨896117, by rfl⟩ : syracuseStep 1194823 = 1792235) B1792235
theorem B1194863 : Blo 1194414 1194863 := bstep (se 1 (by rfl) ⟨896147, by rfl⟩ : syracuseStep 1194863 = 1792295) B1792295
theorem B1194919 : Blo 1194414 1194919 := bstep (se 1 (by rfl) ⟨896189, by rfl⟩ : syracuseStep 1194919 = 1792379) B1792379
theorem B4537403 : Blo 1194414 4537403 := bstep (se 1 (by rfl) ⟨3403052, by rfl⟩ : syracuseStep 4537403 = 6806105) B6806105
theorem B1195099 : Blo 1194414 1195099 := bstep (se 1 (by rfl) ⟨896324, by rfl⟩ : syracuseStep 1195099 = 1792649) B1792649
theorem B1211483 : Blo 1194414 1211483 := bstep (se 1 (by rfl) ⟨908612, by rfl⟩ : syracuseStep 1211483 = 1817225) B1817225
theorem B2301049 : Blo 1194414 2301049 := bstep (se 2 (by rfl) ⟨862893, by rfl⟩ : syracuseStep 2301049 = 1725787) B1725787
theorem B1195215 : Blo 1194414 1195215 := bstep (se 1 (by rfl) ⟨896411, by rfl⟩ : syracuseStep 1195215 = 1792823) B1792823
theorem B1793231 : Blo 1194414 1793231 := bstep (se 1 (by rfl) ⟨1344923, by rfl⟩ : syracuseStep 1793231 = 2689847) B2689847
theorem B1195239 : Blo 1194414 1195239 := bstep (se 1 (by rfl) ⟨896429, by rfl⟩ : syracuseStep 1195239 = 1792859) B1792859
theorem B10214657 : Blo 1194414 10214657 := bstep (se 2 (by rfl) ⟨3830496, by rfl⟩ : syracuseStep 10214657 = 7660993) B7660993
theorem B1195335 : Blo 1194414 1195335 := bstep (se 1 (by rfl) ⟨896501, by rfl⟩ : syracuseStep 1195335 = 1793003) B1793003
theorem B1793351 : Blo 1194414 1793351 := bstep (se 1 (by rfl) ⟨1345013, by rfl⟩ : syracuseStep 1793351 = 2690027) B2690027
theorem B1195471 : Blo 1194414 1195471 := bstep (se 1 (by rfl) ⟨896603, by rfl⟩ : syracuseStep 1195471 = 1793207) B1793207
theorem B39271891 : Blo 1194414 39271891 := bstep (se 1 (by rfl) ⟨29453918, by rfl⟩ : syracuseStep 39271891 = 58907837) B58907837
theorem B1793513 : Blo 1194414 1793513 := bstep (se 2 (by rfl) ⟨672567, by rfl⟩ : syracuseStep 1793513 = 1345135) B1345135
theorem B1195631 : Blo 1194414 1195631 := bstep (se 1 (by rfl) ⟨896723, by rfl⟩ : syracuseStep 1195631 = 1793447) B1793447
theorem B1793657 : Blo 1194414 1793657 := bstep (se 2 (by rfl) ⟨672621, by rfl⟩ : syracuseStep 1793657 = 1345243) B1345243
theorem B1195687 : Blo 1194414 1195687 := bstep (se 1 (by rfl) ⟨896765, by rfl⟩ : syracuseStep 1195687 = 1793531) B1793531
theorem B1195751 : Blo 1194414 1195751 := bstep (se 1 (by rfl) ⟨896813, by rfl⟩ : syracuseStep 1195751 = 1793627) B1793627
theorem B1195807 : Blo 1194414 1195807 := bstep (se 1 (by rfl) ⟨896855, by rfl⟩ : syracuseStep 1195807 = 1793711) B1793711
theorem B1195887 : Blo 1194414 1195887 := bstep (se 1 (by rfl) ⟨896915, by rfl⟩ : syracuseStep 1195887 = 1793831) B1793831
theorem B1793903 : Blo 1194414 1793903 := bstep (se 1 (by rfl) ⟨1345427, by rfl⟩ : syracuseStep 1793903 = 2690855) B2690855
theorem B9084797 : Blo 1194414 9084797 := bstep (se 3 (by rfl) ⟨1703399, by rfl⟩ : syracuseStep 9084797 = 3406799) B3406799
theorem B1195943 : Blo 1194414 1195943 := bstep (se 1 (by rfl) ⟨896957, by rfl⟩ : syracuseStep 1195943 = 1793915) B1793915
theorem B55214045 : Blo 1194414 55214045 := bstep (se 3 (by rfl) ⟨10352633, by rfl⟩ : syracuseStep 55214045 = 20705267) B20705267
theorem B248250379 : Blo 1194414 248250379 := bstep (se 1 (by rfl) ⟨186187784, by rfl⟩ : syracuseStep 248250379 = 372375569) B372375569
theorem B1794089 : Blo 1194414 1794089 := bstep (se 2 (by rfl) ⟨672783, by rfl⟩ : syracuseStep 1794089 = 1345567) B1345567
theorem B1794119 : Blo 1194414 1794119 := bstep (se 1 (by rfl) ⟨1345589, by rfl⟩ : syracuseStep 1794119 = 2691179) B2691179
theorem B1794155 : Blo 1194414 1794155 := bstep (se 1 (by rfl) ⟨1345616, by rfl⟩ : syracuseStep 1794155 = 2691233) B2691233
theorem B1794239 : Blo 1194414 1794239 := bstep (se 1 (by rfl) ⟨1345679, by rfl⟩ : syracuseStep 1794239 = 2691359) B2691359
theorem B1196391 : Blo 1194414 1196391 := bstep (se 1 (by rfl) ⟨897293, by rfl⟩ : syracuseStep 1196391 = 1794587) B1794587
theorem B1794425 : Blo 1194414 1794425 := bstep (se 2 (by rfl) ⟨672909, by rfl⟩ : syracuseStep 1794425 = 1345819) B1345819
theorem B3023527 : Blo 1194414 3023527 := bstep (se 1 (by rfl) ⟨2267645, by rfl⟩ : syracuseStep 3023527 = 4535291) B4535291
theorem B6054587 : Blo 1194414 6054587 := bstep (se 1 (by rfl) ⟨4540940, by rfl⟩ : syracuseStep 6054587 = 9081881) B9081881
theorem B6464225 : Blo 1194414 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B2015995 : Blo 1194414 2015995 := bstep (se 1 (by rfl) ⟨1511996, by rfl⟩ : syracuseStep 2015995 = 3023993) B3023993
theorem B68969231 : Blo 1194414 68969231 := bstep (se 1 (by rfl) ⟨51726923, by rfl⟩ : syracuseStep 68969231 = 103453847) B103453847
theorem B2589511 : Blo 1194414 2589511 := bstep (se 1 (by rfl) ⟨1942133, by rfl⟩ : syracuseStep 2589511 = 3884267) B3884267
theorem B10912583 : Blo 1194414 10912583 := bstep (se 1 (by rfl) ⟨8184437, by rfl⟩ : syracuseStep 10912583 = 16368875) B16368875
theorem B8610893 : Blo 1194414 8610893 := bstep (se 3 (by rfl) ⟨1614542, by rfl⟩ : syracuseStep 8610893 = 3229085) B3229085
theorem B6055073 : Blo 1194414 6055073 := bstep (se 2 (by rfl) ⟨2270652, by rfl⟩ : syracuseStep 6055073 = 4541305) B4541305
theorem B11486569 : Blo 1194414 11486569 := bstep (se 2 (by rfl) ⟨4307463, by rfl⟩ : syracuseStep 11486569 = 8614927) B8614927
theorem B29468123 : Blo 1194414 29468123 := bstep (se 1 (by rfl) ⟨22101092, by rfl⟩ : syracuseStep 29468123 = 44202185) B44202185
theorem B4032071 : Blo 1194414 4032071 := bstep (se 1 (by rfl) ⟨3024053, by rfl⟩ : syracuseStep 4032071 = 6048107) B6048107
theorem B3827371 : Blo 1194414 3827371 := bstep (se 1 (by rfl) ⟨2870528, by rfl⟩ : syracuseStep 3827371 = 5741057) B5741057
theorem B2270911 : Blo 1194414 2270911 := bstep (se 1 (by rfl) ⟨1703183, by rfl⟩ : syracuseStep 2270911 = 3406367) B3406367
theorem B3024935 : Blo 1194414 3024935 := bstep (se 1 (by rfl) ⟨2268701, by rfl⟩ : syracuseStep 3024935 = 4537403) B4537403
theorem B6809771 : Blo 1194414 6809771 := bstep (se 1 (by rfl) ⟨5107328, by rfl⟩ : syracuseStep 6809771 = 10214657) B10214657
theorem B2017487 : Blo 1194414 2017487 := bstep (se 1 (by rfl) ⟨1513115, by rfl⟩ : syracuseStep 2017487 = 3026231) B3026231
theorem B2623751 : Blo 1194414 2623751 := bstep (se 1 (by rfl) ⟨1967813, by rfl⟩ : syracuseStep 2623751 = 3935627) B3935627
theorem B6056531 : Blo 1194414 6056531 := bstep (se 1 (by rfl) ⟨4542398, by rfl⟩ : syracuseStep 6056531 = 9084797) B9084797
theorem B36809363 : Blo 1194414 36809363 := bstep (se 1 (by rfl) ⟨27607022, by rfl⟩ : syracuseStep 36809363 = 55214045) B55214045
theorem B2689775 : Blo 1194414 2689775 := bstep (se 1 (by rfl) ⟨2017331, by rfl⟩ : syracuseStep 2689775 = 4034663) B4034663
theorem B2018047 : Blo 1194414 2018047 := bstep (se 1 (by rfl) ⟨1513535, by rfl⟩ : syracuseStep 2018047 = 3027071) B3027071
theorem B1747823 : Blo 1194414 1747823 := bstep (se 1 (by rfl) ⟨1310867, by rfl⟩ : syracuseStep 1747823 = 2621735) B2621735
theorem B3025775 : Blo 1194414 3025775 := bstep (se 1 (by rfl) ⟨2269331, by rfl⟩ : syracuseStep 3025775 = 4538663) B4538663
theorem B143551349 : Blo 1194414 143551349 := bstep (se 5 (by rfl) ⟨6728969, by rfl⟩ : syracuseStep 143551349 = 13457939) B13457939
theorem B3230621 : Blo 1194414 3230621 := bstep (se 3 (by rfl) ⟨605741, by rfl⟩ : syracuseStep 3230621 = 1211483) B1211483
theorem B9686087 : Blo 1194414 9686087 := bstep (se 1 (by rfl) ⟨7264565, by rfl⟩ : syracuseStep 9686087 = 14529131) B14529131
theorem B2690153 : Blo 1194414 2690153 := bstep (se 2 (by rfl) ⟨1008807, by rfl⟩ : syracuseStep 2690153 = 2017615) B2017615
theorem B3321043 : Blo 1194414 3321043 := bstep (se 1 (by rfl) ⟨2490782, by rfl⟩ : syracuseStep 3321043 = 4981565) B4981565
theorem B4542095 : Blo 1194414 4542095 := bstep (se 1 (by rfl) ⟨3406571, by rfl⟩ : syracuseStep 4542095 = 6813143) B6813143
theorem B2690783 : Blo 1194414 2690783 := bstep (se 1 (by rfl) ⟨2018087, by rfl⟩ : syracuseStep 2690783 = 4036175) B4036175
theorem B2691035 : Blo 1194414 2691035 := bstep (se 1 (by rfl) ⟨2018276, by rfl⟩ : syracuseStep 2691035 = 4036553) B4036553
theorem B31461365 : Blo 1194414 31461365 := bstep (se 5 (by rfl) ⟨1474751, by rfl⟩ : syracuseStep 31461365 = 2949503) B2949503
theorem B4034555 : Blo 1194414 4034555 := bstep (se 1 (by rfl) ⟨3025916, by rfl⟩ : syracuseStep 4034555 = 6051833) B6051833
theorem B3027041 : Blo 1194414 3027041 := bstep (se 2 (by rfl) ⟨1135140, by rfl⟩ : syracuseStep 3027041 = 2270281) B2270281
theorem B2691215 : Blo 1194414 2691215 := bstep (se 1 (by rfl) ⟨2018411, by rfl⟩ : syracuseStep 2691215 = 4036823) B4036823
theorem B3068065 : Blo 1194414 3068065 := bstep (se 2 (by rfl) ⟨1150524, by rfl⟩ : syracuseStep 3068065 = 2301049) B2301049
theorem B2691305 : Blo 1194414 2691305 := bstep (se 2 (by rfl) ⟨1009239, by rfl⟩ : syracuseStep 2691305 = 2018479) B2018479
theorem B3830087 : Blo 1194414 3830087 := bstep (se 1 (by rfl) ⟨2872565, by rfl⟩ : syracuseStep 3830087 = 5745131) B5745131
theorem B2552161 : Blo 1194414 2552161 := bstep (se 2 (by rfl) ⟨957060, by rfl⟩ : syracuseStep 2552161 = 1914121) B1914121
theorem B3633547 : Blo 1194414 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B1724863 : Blo 1194414 1724863 := bstep (se 1 (by rfl) ⟨1293647, by rfl⟩ : syracuseStep 1724863 = 2587295) B2587295
theorem B2691575 : Blo 1194414 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B3109799 : Blo 1194414 3109799 := bstep (se 1 (by rfl) ⟨2332349, by rfl⟩ : syracuseStep 3109799 = 4664699) B4664699
theorem B6812687 : Blo 1194414 6812687 := bstep (se 1 (by rfl) ⟨5109515, by rfl⟩ : syracuseStep 6812687 = 10219031) B10219031
theorem B2552879 : Blo 1194414 2552879 := bstep (se 1 (by rfl) ⟨1914659, by rfl⟩ : syracuseStep 2552879 = 3829319) B3829319
theorem B4306081 : Blo 1194414 4306081 := bstep (se 2 (by rfl) ⟨1614780, by rfl⟩ : syracuseStep 4306081 = 3229561) B3229561
theorem B3028175 : Blo 1194414 3028175 := bstep (se 1 (by rfl) ⟨2271131, by rfl⟩ : syracuseStep 3028175 = 4542263) B4542263
theorem B7656893 : Blo 1194414 7656893 := bstep (se 3 (by rfl) ⟨1435667, by rfl⟩ : syracuseStep 7656893 = 2871335) B2871335
theorem B4535747 : Blo 1194414 4535747 := bstep (se 1 (by rfl) ⟨3401810, by rfl⟩ : syracuseStep 4535747 = 6803621) B6803621
theorem B15308453 : Blo 1194414 15308453 := bstep (se 4 (by rfl) ⟨1435167, by rfl⟩ : syracuseStep 15308453 = 2870335) B2870335
theorem B2422619 : Blo 1194414 2422619 := bstep (se 1 (by rfl) ⟨1816964, by rfl⟩ : syracuseStep 2422619 = 3633929) B3633929
theorem B1816555 : Blo 1194414 1816555 := bstep (se 1 (by rfl) ⟨1362416, by rfl⟩ : syracuseStep 1816555 = 2724833) B2724833
theorem B4143167 : Blo 1194414 4143167 := bstep (se 1 (by rfl) ⟨3107375, by rfl⟩ : syracuseStep 4143167 = 6214751) B6214751
theorem B1792127 : Blo 1194414 1792127 := bstep (se 1 (by rfl) ⟨1344095, by rfl⟩ : syracuseStep 1792127 = 2688191) B2688191
theorem B6133913 : Blo 1194414 6133913 := bstep (se 2 (by rfl) ⟨2300217, by rfl⟩ : syracuseStep 6133913 = 4600435) B4600435
theorem B1792223 : Blo 1194414 1792223 := bstep (se 1 (by rfl) ⟨1344167, by rfl⟩ : syracuseStep 1792223 = 2688335) B2688335
theorem B5740807 : Blo 1194414 5740807 := bstep (se 1 (by rfl) ⟨4305605, by rfl⟩ : syracuseStep 5740807 = 8611211) B8611211
theorem B1792283 : Blo 1194414 1792283 := bstep (se 1 (by rfl) ⟨1344212, by rfl⟩ : syracuseStep 1792283 = 2688425) B2688425
theorem B2423137 : Blo 1194414 2423137 := bstep (se 2 (by rfl) ⟨908676, by rfl⟩ : syracuseStep 2423137 = 1817353) B1817353
theorem B30284225 : Blo 1194414 30284225 := bstep (se 2 (by rfl) ⟨11356584, by rfl⟩ : syracuseStep 30284225 = 22713169) B22713169
theorem B1194543 : Blo 1194414 1194543 := bstep (se 1 (by rfl) ⟨895907, by rfl⟩ : syracuseStep 1194543 = 1791815) B1791815
theorem B1792607 : Blo 1194414 1792607 := bstep (se 1 (by rfl) ⟨1344455, by rfl⟩ : syracuseStep 1792607 = 2688911) B2688911
theorem B22985369 : Blo 1194414 22985369 := bstep (se 2 (by rfl) ⟨8619513, by rfl⟩ : syracuseStep 22985369 = 17239027) B17239027
theorem B1792703 : Blo 1194414 1792703 := bstep (se 1 (by rfl) ⟨1344527, by rfl⟩ : syracuseStep 1792703 = 2689055) B2689055
theorem B1792745 : Blo 1194414 1792745 := bstep (se 2 (by rfl) ⟨672279, by rfl⟩ : syracuseStep 1792745 = 1344559) B1344559
theorem B1792871 : Blo 1194414 1792871 := bstep (se 1 (by rfl) ⟨1344653, by rfl⟩ : syracuseStep 1792871 = 2689307) B2689307
theorem B1792937 : Blo 1194414 1792937 := bstep (se 2 (by rfl) ⟨672351, by rfl⟩ : syracuseStep 1792937 = 1344703) B1344703
theorem B1194943 : Blo 1194414 1194943 := bstep (se 1 (by rfl) ⟨896207, by rfl⟩ : syracuseStep 1194943 = 1792415) B1792415
theorem B3406823 : Blo 1194414 3406823 := bstep (se 1 (by rfl) ⟨2555117, by rfl⟩ : syracuseStep 3406823 = 5110235) B5110235
theorem B1194991 : Blo 1194414 1194991 := bstep (se 1 (by rfl) ⟨896243, by rfl⟩ : syracuseStep 1194991 = 1792487) B1792487
theorem B1702939 : Blo 1194414 1702939 := bstep (se 1 (by rfl) ⟨1277204, by rfl⟩ : syracuseStep 1702939 = 2554409) B2554409
theorem B1793087 : Blo 1194414 1793087 := bstep (se 1 (by rfl) ⟨1344815, by rfl⟩ : syracuseStep 1793087 = 2689631) B2689631
theorem B1793129 : Blo 1194414 1793129 := bstep (se 2 (by rfl) ⟨672423, by rfl⟩ : syracuseStep 1793129 = 1344847) B1344847
theorem B1793255 : Blo 1194414 1793255 := bstep (se 1 (by rfl) ⟨1344941, by rfl⟩ : syracuseStep 1793255 = 2689883) B2689883
theorem B52362521 : Blo 1194414 52362521 := bstep (se 2 (by rfl) ⟨19635945, by rfl⟩ : syracuseStep 52362521 = 39271891) B39271891
theorem B1195487 : Blo 1194414 1195487 := bstep (se 1 (by rfl) ⟨896615, by rfl⟩ : syracuseStep 1195487 = 1793231) B1793231
theorem B104873453 : Blo 1194414 104873453 := bstep (se 3 (by rfl) ⟨19663772, by rfl⟩ : syracuseStep 104873453 = 39327545) B39327545
theorem B6807037 : Blo 1194414 6807037 := bstep (se 3 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 6807037 = 2552639) B2552639
theorem B1195567 : Blo 1194414 1195567 := bstep (se 1 (by rfl) ⟨896675, by rfl⟩ : syracuseStep 1195567 = 1793351) B1793351
theorem B1195675 : Blo 1194414 1195675 := bstep (se 1 (by rfl) ⟨896756, by rfl⟩ : syracuseStep 1195675 = 1793513) B1793513
theorem B1793759 : Blo 1194414 1793759 := bstep (se 1 (by rfl) ⟨1345319, by rfl⟩ : syracuseStep 1793759 = 2690639) B2690639
theorem B1195771 : Blo 1194414 1195771 := bstep (se 1 (by rfl) ⟨896828, by rfl⟩ : syracuseStep 1195771 = 1793657) B1793657
theorem B1195935 : Blo 1194414 1195935 := bstep (se 1 (by rfl) ⟨896951, by rfl⟩ : syracuseStep 1195935 = 1793903) B1793903
theorem B1196059 : Blo 1194414 1196059 := bstep (se 1 (by rfl) ⟨897044, by rfl⟩ : syracuseStep 1196059 = 1794089) B1794089
theorem B1196079 : Blo 1194414 1196079 := bstep (se 1 (by rfl) ⟨897059, by rfl⟩ : syracuseStep 1196079 = 1794119) B1794119
theorem B1196103 : Blo 1194414 1196103 := bstep (se 1 (by rfl) ⟨897077, by rfl⟩ : syracuseStep 1196103 = 1794155) B1794155
theorem B1794143 : Blo 1194414 1794143 := bstep (se 1 (by rfl) ⟨1345607, by rfl⟩ : syracuseStep 1794143 = 2691215) B2691215
theorem B1196159 : Blo 1194414 1196159 := bstep (se 1 (by rfl) ⟨897119, by rfl⟩ : syracuseStep 1196159 = 1794239) B1794239
theorem B1794203 : Blo 1194414 1794203 := bstep (se 1 (by rfl) ⟨1345652, by rfl⟩ : syracuseStep 1794203 = 2691305) B2691305
theorem B1196283 : Blo 1194414 1196283 := bstep (se 1 (by rfl) ⟨897212, by rfl⟩ : syracuseStep 1196283 = 1794425) B1794425
theorem B1794383 : Blo 1194414 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B7275055 : Blo 1194414 7275055 := bstep (se 1 (by rfl) ⟨5456291, by rfl⟩ : syracuseStep 7275055 = 10912583) B10912583
theorem B4031369 : Blo 1194414 4031369 := bstep (se 2 (by rfl) ⟨1511763, by rfl⟩ : syracuseStep 4031369 = 3023527) B3023527
theorem B5104595 : Blo 1194414 5104595 := bstep (se 1 (by rfl) ⟨3828446, by rfl⟩ : syracuseStep 5104595 = 7656893) B7656893
theorem B3023831 : Blo 1194414 3023831 := bstep (se 1 (by rfl) ⟨2267873, by rfl⟩ : syracuseStep 3023831 = 4535747) B4535747
theorem B19645415 : Blo 1194414 19645415 := bstep (se 1 (by rfl) ⟨14734061, by rfl⟩ : syracuseStep 19645415 = 29468123) B29468123
theorem B2687993 : Blo 1194414 2687993 := bstep (se 2 (by rfl) ⟨1007997, by rfl⟩ : syracuseStep 2687993 = 2015995) B2015995
theorem B2688047 : Blo 1194414 2688047 := bstep (se 1 (by rfl) ⟨2016035, by rfl⟩ : syracuseStep 2688047 = 4032071) B4032071
theorem B17712229 : Blo 1194414 17712229 := bstep (se 4 (by rfl) ⟨1660521, by rfl⟩ : syracuseStep 17712229 = 3321043) B3321043
theorem B1615079 : Blo 1194414 1615079 := bstep (se 1 (by rfl) ⟨1211309, by rfl⟩ : syracuseStep 1615079 = 2422619) B2422619
theorem B2016623 : Blo 1194414 2016623 := bstep (se 1 (by rfl) ⟨1512467, by rfl⟩ : syracuseStep 2016623 = 3024935) B3024935
theorem B2270585 : Blo 1194414 2270585 := bstep (se 2 (by rfl) ⟨851469, by rfl⟩ : syracuseStep 2270585 = 1702939) B1702939
theorem B2762111 : Blo 1194414 2762111 := bstep (se 1 (by rfl) ⟨2071583, by rfl⟩ : syracuseStep 2762111 = 4143167) B4143167
theorem B4089275 : Blo 1194414 4089275 := bstep (se 1 (by rfl) ⟨3066956, by rfl⟩ : syracuseStep 4089275 = 6133913) B6133913
theorem B4539847 : Blo 1194414 4539847 := bstep (se 1 (by rfl) ⟨3404885, by rfl⟩ : syracuseStep 4539847 = 6809771) B6809771
theorem B1344991 : Blo 1194414 1344991 := bstep (se 1 (by rfl) ⟨1008743, by rfl⟩ : syracuseStep 1344991 = 2017487) B2017487
theorem B98158301 : Blo 1194414 98158301 := bstep (se 3 (by rfl) ⟨18404681, by rfl⟩ : syracuseStep 98158301 = 36809363) B36809363
theorem B2017183 : Blo 1194414 2017183 := bstep (se 1 (by rfl) ⟨1512887, by rfl⟩ : syracuseStep 2017183 = 3025775) B3025775
theorem B95700899 : Blo 1194414 95700899 := bstep (se 1 (by rfl) ⟨71775674, by rfl⟩ : syracuseStep 95700899 = 143551349) B143551349
theorem B17237933 : Blo 1194414 17237933 := bstep (se 3 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 17237933 = 6464225) B6464225
theorem B2271215 : Blo 1194414 2271215 := bstep (se 1 (by rfl) ⟨1703411, by rfl⟩ : syracuseStep 2271215 = 3406823) B3406823
theorem B6457391 : Blo 1194414 6457391 := bstep (se 1 (by rfl) ⟨4843043, by rfl⟩ : syracuseStep 6457391 = 9686087) B9686087
theorem B34908347 : Blo 1194414 34908347 := bstep (se 1 (by rfl) ⟨26181260, by rfl⟩ : syracuseStep 34908347 = 52362521) B52362521
theorem B8292797 : Blo 1194414 8292797 := bstep (se 3 (by rfl) ⟨1554899, by rfl⟩ : syracuseStep 8292797 = 3109799) B3109799
theorem B20974243 : Blo 1194414 20974243 := bstep (se 1 (by rfl) ⟨15730682, by rfl⟩ : syracuseStep 20974243 = 31461365) B31461365
theorem B2689703 : Blo 1194414 2689703 := bstep (se 1 (by rfl) ⟨2017277, by rfl⟩ : syracuseStep 2689703 = 4034555) B4034555
theorem B331000505 : Blo 1194414 331000505 := bstep (se 2 (by rfl) ⟨124125189, by rfl⟩ : syracuseStep 331000505 = 248250379) B248250379
theorem B2018027 : Blo 1194414 2018027 := bstep (se 1 (by rfl) ⟨1513520, by rfl⟩ : syracuseStep 2018027 = 3027041) B3027041
theorem B4090753 : Blo 1194414 4090753 := bstep (se 2 (by rfl) ⟨1534032, by rfl⟩ : syracuseStep 4090753 = 3068065) B3068065
theorem B7654409 : Blo 1194414 7654409 := bstep (se 2 (by rfl) ⟨2870403, by rfl⟩ : syracuseStep 7654409 = 5740807) B5740807
theorem B3402881 : Blo 1194414 3402881 := bstep (se 2 (by rfl) ⟨1276080, by rfl⟩ : syracuseStep 3402881 = 2552161) B2552161
theorem B3230849 : Blo 1194414 3230849 := bstep (se 2 (by rfl) ⟨1211568, by rfl⟩ : syracuseStep 3230849 = 2423137) B2423137
theorem B4844729 : Blo 1194414 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B4541791 : Blo 1194414 4541791 := bstep (se 1 (by rfl) ⟨3406343, by rfl⟩ : syracuseStep 4541791 = 6812687) B6812687
theorem B2018783 : Blo 1194414 2018783 := bstep (se 1 (by rfl) ⟨1514087, by rfl⟩ : syracuseStep 2018783 = 3028175) B3028175
theorem B2690729 : Blo 1194414 2690729 := bstep (se 2 (by rfl) ⟨1009023, by rfl⟩ : syracuseStep 2690729 = 2018047) B2018047
theorem B3452681 : Blo 1194414 3452681 := bstep (se 2 (by rfl) ⟨1294755, by rfl⟩ : syracuseStep 3452681 = 2589511) B2589511
theorem B1749167 : Blo 1194414 1749167 := bstep (se 1 (by rfl) ⟨1311875, by rfl⟩ : syracuseStep 1749167 = 2623751) B2623751
theorem B20189483 : Blo 1194414 20189483 := bstep (se 1 (by rfl) ⟨15142112, by rfl⟩ : syracuseStep 20189483 = 30284225) B30284225
theorem B15323579 : Blo 1194414 15323579 := bstep (se 1 (by rfl) ⟨11492684, by rfl⟩ : syracuseStep 15323579 = 22985369) B22985369
theorem B15315425 : Blo 1194414 15315425 := bstep (se 2 (by rfl) ⟨5743284, by rfl⟩ : syracuseStep 15315425 = 11486569) B11486569
theorem B3027881 : Blo 1194414 3027881 := bstep (se 2 (by rfl) ⟨1135455, by rfl⟩ : syracuseStep 3027881 = 2270911) B2270911
theorem B69915635 : Blo 1194414 69915635 := bstep (se 1 (by rfl) ⟨52436726, by rfl⟩ : syracuseStep 69915635 = 104873453) B104873453
theorem B3028063 : Blo 1194414 3028063 := bstep (se 1 (by rfl) ⟨2271047, by rfl⟩ : syracuseStep 3028063 = 4542095) B4542095
theorem B2422073 : Blo 1194414 2422073 := bstep (se 2 (by rfl) ⟨908277, by rfl⟩ : syracuseStep 2422073 = 1816555) B1816555
theorem B2553391 : Blo 1194414 2553391 := bstep (se 1 (by rfl) ⟨1915043, by rfl⟩ : syracuseStep 2553391 = 3830087) B3830087
theorem B4036391 : Blo 1194414 4036391 := bstep (se 1 (by rfl) ⟨3027293, by rfl⟩ : syracuseStep 4036391 = 6054587) B6054587
theorem B45979487 : Blo 1194414 45979487 := bstep (se 1 (by rfl) ⟨34484615, by rfl⟩ : syracuseStep 45979487 = 68969231) B68969231
theorem B2299817 : Blo 1194414 2299817 := bstep (se 2 (by rfl) ⟨862431, by rfl⟩ : syracuseStep 2299817 = 1724863) B1724863
theorem B1701919 : Blo 1194414 1701919 := bstep (se 1 (by rfl) ⟨1276439, by rfl⟩ : syracuseStep 1701919 = 2552879) B2552879
theorem B5740595 : Blo 1194414 5740595 := bstep (se 1 (by rfl) ⟨4305446, by rfl⟩ : syracuseStep 5740595 = 8610893) B8610893
theorem B4036715 : Blo 1194414 4036715 := bstep (se 1 (by rfl) ⟨3027536, by rfl⟩ : syracuseStep 4036715 = 6055073) B6055073
theorem B10205635 : Blo 1194414 10205635 := bstep (se 1 (by rfl) ⟨7654226, by rfl⟩ : syracuseStep 10205635 = 15308453) B15308453
theorem B1194751 : Blo 1194414 1194751 := bstep (se 1 (by rfl) ⟨896063, by rfl⟩ : syracuseStep 1194751 = 1792127) B1792127
theorem B1194815 : Blo 1194414 1194815 := bstep (se 1 (by rfl) ⟨896111, by rfl⟩ : syracuseStep 1194815 = 1792223) B1792223
theorem B1194855 : Blo 1194414 1194855 := bstep (se 1 (by rfl) ⟨896141, by rfl⟩ : syracuseStep 1194855 = 1792283) B1792283
theorem B5741441 : Blo 1194414 5741441 := bstep (se 2 (by rfl) ⟨2153040, by rfl⟩ : syracuseStep 5741441 = 4306081) B4306081
theorem B4037687 : Blo 1194414 4037687 := bstep (se 1 (by rfl) ⟨3028265, by rfl⟩ : syracuseStep 4037687 = 6056531) B6056531
theorem B1195071 : Blo 1194414 1195071 := bstep (se 1 (by rfl) ⟨896303, by rfl⟩ : syracuseStep 1195071 = 1792607) B1792607
theorem B1195135 : Blo 1194414 1195135 := bstep (se 1 (by rfl) ⟨896351, by rfl⟩ : syracuseStep 1195135 = 1792703) B1792703
theorem B1195163 : Blo 1194414 1195163 := bstep (se 1 (by rfl) ⟨896372, by rfl⟩ : syracuseStep 1195163 = 1792745) B1792745
theorem B1793183 : Blo 1194414 1793183 := bstep (se 1 (by rfl) ⟨1344887, by rfl⟩ : syracuseStep 1793183 = 2689775) B2689775
theorem B1195247 : Blo 1194414 1195247 := bstep (se 1 (by rfl) ⟨896435, by rfl⟩ : syracuseStep 1195247 = 1792871) B1792871
theorem B2153747 : Blo 1194414 2153747 := bstep (se 1 (by rfl) ⟨1615310, by rfl⟩ : syracuseStep 2153747 = 3230621) B3230621
theorem B1195291 : Blo 1194414 1195291 := bstep (se 1 (by rfl) ⟨896468, by rfl⟩ : syracuseStep 1195291 = 1792937) B1792937
theorem B9076049 : Blo 1194414 9076049 := bstep (se 2 (by rfl) ⟨3403518, by rfl⟩ : syracuseStep 9076049 = 6807037) B6807037
theorem B1195391 : Blo 1194414 1195391 := bstep (se 1 (by rfl) ⟨896543, by rfl⟩ : syracuseStep 1195391 = 1793087) B1793087
theorem B1195419 : Blo 1194414 1195419 := bstep (se 1 (by rfl) ⟨896564, by rfl⟩ : syracuseStep 1195419 = 1793129) B1793129
theorem B1793435 : Blo 1194414 1793435 := bstep (se 1 (by rfl) ⟨1345076, by rfl⟩ : syracuseStep 1793435 = 2690153) B2690153
theorem B1195503 : Blo 1194414 1195503 := bstep (se 1 (by rfl) ⟨896627, by rfl⟩ : syracuseStep 1195503 = 1793255) B1793255
theorem B5103161 : Blo 1194414 5103161 := bstep (se 2 (by rfl) ⟨1913685, by rfl⟩ : syracuseStep 5103161 = 3827371) B3827371
theorem B4660861 : Blo 1194414 4660861 := bstep (se 3 (by rfl) ⟨873911, by rfl⟩ : syracuseStep 4660861 = 1747823) B1747823
theorem B1195839 : Blo 1194414 1195839 := bstep (se 1 (by rfl) ⟨896879, by rfl⟩ : syracuseStep 1195839 = 1793759) B1793759
theorem B1793855 : Blo 1194414 1793855 := bstep (se 1 (by rfl) ⟨1345391, by rfl⟩ : syracuseStep 1793855 = 2690783) B2690783
theorem B1794023 : Blo 1194414 1794023 := bstep (se 1 (by rfl) ⟨1345517, by rfl⟩ : syracuseStep 1794023 = 2691035) B2691035
theorem B2269225 : Blo 1194414 2269225 := bstep (se 2 (by rfl) ⟨850959, by rfl⟩ : syracuseStep 2269225 = 1701919) B1701919
theorem B1196095 : Blo 1194414 1196095 := bstep (se 1 (by rfl) ⟨897071, by rfl⟩ : syracuseStep 1196095 = 1794143) B1794143
theorem B1196135 : Blo 1194414 1196135 := bstep (se 1 (by rfl) ⟨897101, by rfl⟩ : syracuseStep 1196135 = 1794203) B1794203
theorem B13459655 : Blo 1194414 13459655 := bstep (se 1 (by rfl) ⟨10094741, by rfl⟩ : syracuseStep 13459655 = 20189483) B20189483
theorem B1196255 : Blo 1194414 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B10215719 : Blo 1194414 10215719 := bstep (se 1 (by rfl) ⟨7661789, by rfl⟩ : syracuseStep 10215719 = 15323579) B15323579
theorem B12919277 : Blo 1194414 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B13607513 : Blo 1194414 13607513 := bstep (se 2 (by rfl) ⟨5102817, by rfl⟩ : syracuseStep 13607513 = 10205635) B10205635
theorem B2687579 : Blo 1194414 2687579 := bstep (se 1 (by rfl) ⟨2015684, by rfl⟩ : syracuseStep 2687579 = 4031369) B4031369
theorem B2015887 : Blo 1194414 2015887 := bstep (se 1 (by rfl) ⟨1511915, by rfl⟩ : syracuseStep 2015887 = 3023831) B3023831
theorem B5743325 : Blo 1194414 5743325 := bstep (se 3 (by rfl) ⟨1076873, by rfl⟩ : syracuseStep 5743325 = 2153747) B2153747
theorem B9700073 : Blo 1194414 9700073 := bstep (se 2 (by rfl) ⟨3637527, by rfl⟩ : syracuseStep 9700073 = 7275055) B7275055
theorem B1344415 : Blo 1194414 1344415 := bstep (se 1 (by rfl) ⟨1008311, by rfl⟩ : syracuseStep 1344415 = 2016623) B2016623
theorem B7365629 : Blo 1194414 7365629 := bstep (se 3 (by rfl) ⟨1381055, by rfl⟩ : syracuseStep 7365629 = 2762111) B2762111
theorem B65438867 : Blo 1194414 65438867 := bstep (se 1 (by rfl) ⟨49079150, by rfl⟩ : syracuseStep 65438867 = 98158301) B98158301
theorem B1533211 : Blo 1194414 1533211 := bstep (se 1 (by rfl) ⟨1149908, by rfl⟩ : syracuseStep 1533211 = 2299817) B2299817
theorem B3827063 : Blo 1194414 3827063 := bstep (se 1 (by rfl) ⟨2870297, by rfl⟩ : syracuseStep 3827063 = 5740595) B5740595
theorem B6055721 : Blo 1194414 6055721 := bstep (se 2 (by rfl) ⟨2270895, by rfl⟩ : syracuseStep 6055721 = 4541791) B4541791
theorem B1345351 : Blo 1194414 1345351 := bstep (se 1 (by rfl) ⟨1009013, by rfl⟩ : syracuseStep 1345351 = 2018027) B2018027
theorem B3827627 : Blo 1194414 3827627 := bstep (se 1 (by rfl) ⟨2870720, by rfl⟩ : syracuseStep 3827627 = 5741441) B5741441
theorem B74631125 : Blo 1194414 74631125 := bstep (se 7 (by rfl) ⟨874583, by rfl⟩ : syracuseStep 74631125 = 1749167) B1749167
theorem B1345855 : Blo 1194414 1345855 := bstep (se 1 (by rfl) ⟨1009391, by rfl⟩ : syracuseStep 1345855 = 2018783) B2018783
theorem B3402107 : Blo 1194414 3402107 := bstep (se 1 (by rfl) ⟨2551580, by rfl⟩ : syracuseStep 3402107 = 5103161) B5103161
theorem B2689577 : Blo 1194414 2689577 := bstep (se 2 (by rfl) ⟨1008591, by rfl⟩ : syracuseStep 2689577 = 2017183) B2017183
theorem B10210283 : Blo 1194414 10210283 := bstep (se 1 (by rfl) ⟨7657712, by rfl⟩ : syracuseStep 10210283 = 15315425) B15315425
theorem B93088925 : Blo 1194414 93088925 := bstep (se 3 (by rfl) ⟨17454173, by rfl⟩ : syracuseStep 93088925 = 34908347) B34908347
theorem B2018587 : Blo 1194414 2018587 := bstep (se 1 (by rfl) ⟨1513940, by rfl⟩ : syracuseStep 2018587 = 3027881) B3027881
theorem B3403063 : Blo 1194414 3403063 := bstep (se 1 (by rfl) ⟨2552297, by rfl⟩ : syracuseStep 3403063 = 5104595) B5104595
theorem B6458861 : Blo 1194414 6458861 := bstep (se 3 (by rfl) ⟨1211036, by rfl⟩ : syracuseStep 6458861 = 2422073) B2422073
theorem B2690927 : Blo 1194414 2690927 := bstep (se 1 (by rfl) ⟨2018195, by rfl⟩ : syracuseStep 2690927 = 4036391) B4036391
theorem B4304927 : Blo 1194414 4304927 := bstep (se 1 (by rfl) ⟨3228695, by rfl⟩ : syracuseStep 4304927 = 6457391) B6457391
theorem B2691143 : Blo 1194414 2691143 := bstep (se 1 (by rfl) ⟨2018357, by rfl⟩ : syracuseStep 2691143 = 4036715) B4036715
theorem B2691791 : Blo 1194414 2691791 := bstep (se 1 (by rfl) ⟨2018843, by rfl⟩ : syracuseStep 2691791 = 4037687) B4037687
theorem B3404521 : Blo 1194414 3404521 := bstep (se 2 (by rfl) ⟨1276695, by rfl⟩ : syracuseStep 3404521 = 2553391) B2553391
theorem B6214481 : Blo 1194414 6214481 := bstep (se 2 (by rfl) ⟨2330430, by rfl⟩ : syracuseStep 6214481 = 4660861) B4660861
theorem B6050699 : Blo 1194414 6050699 := bstep (se 1 (by rfl) ⟨4538024, by rfl⟩ : syracuseStep 6050699 = 9076049) B9076049
theorem B255202397 : Blo 1194414 255202397 := bstep (se 3 (by rfl) ⟨47850449, by rfl⟩ : syracuseStep 255202397 = 95700899) B95700899
theorem B4306877 : Blo 1194414 4306877 := bstep (se 3 (by rfl) ⟨807539, by rfl⟩ : syracuseStep 4306877 = 1615079) B1615079
theorem B13096943 : Blo 1194414 13096943 := bstep (se 1 (by rfl) ⟨9822707, by rfl⟩ : syracuseStep 13096943 = 19645415) B19645415
theorem B46610423 : Blo 1194414 46610423 := bstep (se 1 (by rfl) ⟨34957817, by rfl⟩ : syracuseStep 46610423 = 69915635) B69915635
theorem B1791995 : Blo 1194414 1791995 := bstep (se 1 (by rfl) ⟨1343996, by rfl⟩ : syracuseStep 1791995 = 2687993) B2687993
theorem B1792031 : Blo 1194414 1792031 := bstep (se 1 (by rfl) ⟨1344023, by rfl⟩ : syracuseStep 1792031 = 2688047) B2688047
theorem B27965657 : Blo 1194414 27965657 := bstep (se 2 (by rfl) ⟨10487121, by rfl⟩ : syracuseStep 27965657 = 20974243) B20974243
theorem B1513723 : Blo 1194414 1513723 := bstep (se 1 (by rfl) ⟨1135292, by rfl⟩ : syracuseStep 1513723 = 2270585) B2270585
theorem B2726183 : Blo 1194414 2726183 := bstep (se 1 (by rfl) ⟨2044637, by rfl⟩ : syracuseStep 2726183 = 4089275) B4089275
theorem B5454337 : Blo 1194414 5454337 := bstep (se 2 (by rfl) ⟨2045376, by rfl⟩ : syracuseStep 5454337 = 4090753) B4090753
theorem B30652991 : Blo 1194414 30652991 := bstep (se 1 (by rfl) ⟨22989743, by rfl⟩ : syracuseStep 30652991 = 45979487) B45979487
theorem B11491955 : Blo 1194414 11491955 := bstep (se 1 (by rfl) ⟨8618966, by rfl⟩ : syracuseStep 11491955 = 17237933) B17237933
theorem B1514143 : Blo 1194414 1514143 := bstep (se 1 (by rfl) ⟨1135607, by rfl⟩ : syracuseStep 1514143 = 2271215) B2271215
theorem B4037417 : Blo 1194414 4037417 := bstep (se 2 (by rfl) ⟨1514031, by rfl⟩ : syracuseStep 4037417 = 3028063) B3028063
theorem B23616305 : Blo 1194414 23616305 := bstep (se 2 (by rfl) ⟨8856114, by rfl⟩ : syracuseStep 23616305 = 17712229) B17712229
theorem B5528531 : Blo 1194414 5528531 := bstep (se 1 (by rfl) ⟨4146398, by rfl⟩ : syracuseStep 5528531 = 8292797) B8292797
theorem B1793135 : Blo 1194414 1793135 := bstep (se 1 (by rfl) ⟨1344851, by rfl⟩ : syracuseStep 1793135 = 2689703) B2689703
theorem B220667003 : Blo 1194414 220667003 := bstep (se 1 (by rfl) ⟨165500252, by rfl⟩ : syracuseStep 220667003 = 331000505) B331000505
theorem B6053129 : Blo 1194414 6053129 := bstep (se 2 (by rfl) ⟨2269923, by rfl⟩ : syracuseStep 6053129 = 4539847) B4539847
theorem B1793321 : Blo 1194414 1793321 := bstep (se 2 (by rfl) ⟨672495, by rfl⟩ : syracuseStep 1793321 = 1344991) B1344991
theorem B5102939 : Blo 1194414 5102939 := bstep (se 1 (by rfl) ⟨3827204, by rfl⟩ : syracuseStep 5102939 = 7654409) B7654409
theorem B2268587 : Blo 1194414 2268587 := bstep (se 1 (by rfl) ⟨1701440, by rfl⟩ : syracuseStep 2268587 = 3402881) B3402881
theorem B2153899 : Blo 1194414 2153899 := bstep (se 1 (by rfl) ⟨1615424, by rfl⟩ : syracuseStep 2153899 = 3230849) B3230849
theorem B1195455 : Blo 1194414 1195455 := bstep (se 1 (by rfl) ⟨896591, by rfl⟩ : syracuseStep 1195455 = 1793183) B1793183
theorem B1195623 : Blo 1194414 1195623 := bstep (se 1 (by rfl) ⟨896717, by rfl⟩ : syracuseStep 1195623 = 1793435) B1793435
theorem B1793819 : Blo 1194414 1793819 := bstep (se 1 (by rfl) ⟨1345364, by rfl⟩ : syracuseStep 1793819 = 2690729) B2690729
theorem B2301787 : Blo 1194414 2301787 := bstep (se 1 (by rfl) ⟨1726340, by rfl⟩ : syracuseStep 2301787 = 3452681) B3452681
theorem B1195903 : Blo 1194414 1195903 := bstep (se 1 (by rfl) ⟨896927, by rfl⟩ : syracuseStep 1195903 = 1793855) B1793855
theorem B1196015 : Blo 1194414 1196015 := bstep (se 1 (by rfl) ⟨897011, by rfl⟩ : syracuseStep 1196015 = 1794023) B1794023
theorem B1794095 : Blo 1194414 1794095 := bstep (se 1 (by rfl) ⟨1345571, by rfl⟩ : syracuseStep 1794095 = 2691143) B2691143
theorem B1794473 : Blo 1194414 1794473 := bstep (se 2 (by rfl) ⟨672927, by rfl⟩ : syracuseStep 1794473 = 1345855) B1345855
theorem B1794527 : Blo 1194414 1794527 := bstep (se 1 (by rfl) ⟨1345895, by rfl⟩ : syracuseStep 1794527 = 2691791) B2691791
theorem B2687849 : Blo 1194414 2687849 := bstep (se 2 (by rfl) ⟨1007943, by rfl⟩ : syracuseStep 2687849 = 2015887) B2015887
theorem B4539361 : Blo 1194414 4539361 := bstep (se 2 (by rfl) ⟨1702260, by rfl⟩ : syracuseStep 4539361 = 3404521) B3404521
theorem B31073615 : Blo 1194414 31073615 := bstep (se 1 (by rfl) ⟨23305211, by rfl⟩ : syracuseStep 31073615 = 46610423) B46610423
theorem B8177125 : Blo 1194414 8177125 := bstep (se 4 (by rfl) ⟨766605, by rfl⟩ : syracuseStep 8177125 = 1533211) B1533211
theorem B7661303 : Blo 1194414 7661303 := bstep (se 1 (by rfl) ⟨5745977, by rfl⟩ : syracuseStep 7661303 = 11491955) B11491955
theorem B3401959 : Blo 1194414 3401959 := bstep (se 1 (by rfl) ⟨2551469, by rfl⟩ : syracuseStep 3401959 = 5102939) B5102939
theorem B3025633 : Blo 1194414 3025633 := bstep (se 2 (by rfl) ⟨1134612, by rfl⟩ : syracuseStep 3025633 = 2269225) B2269225
theorem B11479805 : Blo 1194414 11479805 := bstep (se 3 (by rfl) ⟨2152463, by rfl⟩ : syracuseStep 11479805 = 4304927) B4304927
theorem B6810479 : Blo 1194414 6810479 := bstep (se 1 (by rfl) ⟨5107859, by rfl⟩ : syracuseStep 6810479 = 10215719) B10215719
theorem B8612851 : Blo 1194414 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B2018297 : Blo 1194414 2018297 := bstep (se 2 (by rfl) ⟨756861, by rfl⟩ : syracuseStep 2018297 = 1513723) B1513723
theorem B9071675 : Blo 1194414 9071675 := bstep (se 1 (by rfl) ⟨6803756, by rfl⟩ : syracuseStep 9071675 = 13607513) B13607513
theorem B3828883 : Blo 1194414 3828883 := bstep (se 1 (by rfl) ⟨2871662, by rfl⟩ : syracuseStep 3828883 = 5743325) B5743325
theorem B6466715 : Blo 1194414 6466715 := bstep (se 1 (by rfl) ⟨4850036, by rfl⟩ : syracuseStep 6466715 = 9700073) B9700073
theorem B35892413 : Blo 1194414 35892413 := bstep (se 3 (by rfl) ⟨6729827, by rfl⟩ : syracuseStep 35892413 = 13459655) B13459655
theorem B4033799 : Blo 1194414 4033799 := bstep (se 1 (by rfl) ⟨3025349, by rfl⟩ : syracuseStep 4033799 = 6050699) B6050699
theorem B4910419 : Blo 1194414 4910419 := bstep (se 1 (by rfl) ⟨3682814, by rfl⟩ : syracuseStep 4910419 = 7365629) B7365629
theorem B170134931 : Blo 1194414 170134931 := bstep (se 1 (by rfl) ⟨127601198, by rfl⟩ : syracuseStep 170134931 = 255202397) B255202397
theorem B43625911 : Blo 1194414 43625911 := bstep (se 1 (by rfl) ⟨32719433, by rfl⟩ : syracuseStep 43625911 = 65438867) B65438867
theorem B7269821 : Blo 1194414 7269821 := bstep (se 3 (by rfl) ⟨1363091, by rfl⟩ : syracuseStep 7269821 = 2726183) B2726183
theorem B2018857 : Blo 1194414 2018857 := bstep (se 2 (by rfl) ⟨757071, by rfl⟩ : syracuseStep 2018857 = 1514143) B1514143
theorem B2551375 : Blo 1194414 2551375 := bstep (se 1 (by rfl) ⟨1913531, by rfl⟩ : syracuseStep 2551375 = 3827063) B3827063
theorem B6049565 : Blo 1194414 6049565 := bstep (se 3 (by rfl) ⟨1134293, by rfl⟩ : syracuseStep 6049565 = 2268587) B2268587
theorem B2551751 : Blo 1194414 2551751 := bstep (se 1 (by rfl) ⟨1913813, by rfl⟩ : syracuseStep 2551751 = 3827627) B3827627
theorem B2871251 : Blo 1194414 2871251 := bstep (se 1 (by rfl) ⟨2153438, by rfl⟩ : syracuseStep 2871251 = 4306877) B4306877
theorem B49754083 : Blo 1194414 49754083 := bstep (se 1 (by rfl) ⟨37315562, by rfl⟩ : syracuseStep 49754083 = 74631125) B74631125
theorem B2691449 : Blo 1194414 2691449 := bstep (se 2 (by rfl) ⟨1009293, by rfl⟩ : syracuseStep 2691449 = 2018587) B2018587
theorem B20435327 : Blo 1194414 20435327 := bstep (se 1 (by rfl) ⟨15326495, by rfl⟩ : syracuseStep 20435327 = 30652991) B30652991
theorem B12276197 : Blo 1194414 12276197 := bstep (se 4 (by rfl) ⟨1150893, by rfl⟩ : syracuseStep 12276197 = 2301787) B2301787
theorem B2691611 : Blo 1194414 2691611 := bstep (se 1 (by rfl) ⟨2018708, by rfl⟩ : syracuseStep 2691611 = 4037417) B4037417
theorem B2871865 : Blo 1194414 2871865 := bstep (se 2 (by rfl) ⟨1076949, by rfl⟩ : syracuseStep 2871865 = 2153899) B2153899
theorem B62059283 : Blo 1194414 62059283 := bstep (se 1 (by rfl) ⟨46544462, by rfl⟩ : syracuseStep 62059283 = 93088925) B93088925
theorem B4035419 : Blo 1194414 4035419 := bstep (se 1 (by rfl) ⟨3026564, by rfl⟩ : syracuseStep 4035419 = 6053129) B6053129
theorem B4305907 : Blo 1194414 4305907 := bstep (se 1 (by rfl) ⟨3229430, by rfl⟩ : syracuseStep 4305907 = 6458861) B6458861
theorem B14742749 : Blo 1194414 14742749 := bstep (se 3 (by rfl) ⟨2764265, by rfl⟩ : syracuseStep 14742749 = 5528531) B5528531
theorem B1791719 : Blo 1194414 1791719 := bstep (se 1 (by rfl) ⟨1343789, by rfl⟩ : syracuseStep 1791719 = 2687579) B2687579
theorem B4142987 : Blo 1194414 4142987 := bstep (se 1 (by rfl) ⟨3107240, by rfl⟩ : syracuseStep 4142987 = 6214481) B6214481
theorem B7272449 : Blo 1194414 7272449 := bstep (se 2 (by rfl) ⟨2727168, by rfl⟩ : syracuseStep 7272449 = 5454337) B5454337
theorem B4037147 : Blo 1194414 4037147 := bstep (se 1 (by rfl) ⟨3027860, by rfl⟩ : syracuseStep 4037147 = 6055721) B6055721
theorem B1792553 : Blo 1194414 1792553 := bstep (se 2 (by rfl) ⟨672207, by rfl⟩ : syracuseStep 1792553 = 1344415) B1344415
theorem B8731295 : Blo 1194414 8731295 := bstep (se 1 (by rfl) ⟨6548471, by rfl⟩ : syracuseStep 8731295 = 13096943) B13096943
theorem B1194663 : Blo 1194414 1194663 := bstep (se 1 (by rfl) ⟨895997, by rfl⟩ : syracuseStep 1194663 = 1791995) B1791995
theorem B1194687 : Blo 1194414 1194687 := bstep (se 1 (by rfl) ⟨896015, by rfl⟩ : syracuseStep 1194687 = 1792031) B1792031
theorem B18643771 : Blo 1194414 18643771 := bstep (se 1 (by rfl) ⟨13982828, by rfl⟩ : syracuseStep 18643771 = 27965657) B27965657
theorem B2268071 : Blo 1194414 2268071 := bstep (se 1 (by rfl) ⟨1701053, by rfl⟩ : syracuseStep 2268071 = 3402107) B3402107
theorem B1793051 : Blo 1194414 1793051 := bstep (se 1 (by rfl) ⟨1344788, by rfl⟩ : syracuseStep 1793051 = 2689577) B2689577
theorem B4537417 : Blo 1194414 4537417 := bstep (se 2 (by rfl) ⟨1701531, by rfl⟩ : syracuseStep 4537417 = 3403063) B3403063
theorem B15744203 : Blo 1194414 15744203 := bstep (se 1 (by rfl) ⟨11808152, by rfl⟩ : syracuseStep 15744203 = 23616305) B23616305
theorem B6806855 : Blo 1194414 6806855 := bstep (se 1 (by rfl) ⟨5105141, by rfl⟩ : syracuseStep 6806855 = 10210283) B10210283
theorem B1195423 : Blo 1194414 1195423 := bstep (se 1 (by rfl) ⟨896567, by rfl⟩ : syracuseStep 1195423 = 1793135) B1793135
theorem B147111335 : Blo 1194414 147111335 := bstep (se 1 (by rfl) ⟨110333501, by rfl⟩ : syracuseStep 147111335 = 220667003) B220667003
theorem B1195547 : Blo 1194414 1195547 := bstep (se 1 (by rfl) ⟨896660, by rfl⟩ : syracuseStep 1195547 = 1793321) B1793321
theorem B1793801 : Blo 1194414 1793801 := bstep (se 2 (by rfl) ⟨672675, by rfl⟩ : syracuseStep 1793801 = 1345351) B1345351
theorem B1195879 : Blo 1194414 1195879 := bstep (se 1 (by rfl) ⟨896909, by rfl⟩ : syracuseStep 1195879 = 1793819) B1793819
theorem B1793951 : Blo 1194414 1793951 := bstep (se 1 (by rfl) ⟨1345463, by rfl⟩ : syracuseStep 1793951 = 2690927) B2690927
theorem B1196063 : Blo 1194414 1196063 := bstep (se 1 (by rfl) ⟨897047, by rfl⟩ : syracuseStep 1196063 = 1794095) B1794095
theorem B1794299 : Blo 1194414 1794299 := bstep (se 1 (by rfl) ⟨1345724, by rfl⟩ : syracuseStep 1794299 = 2691449) B2691449
theorem B13623551 : Blo 1194414 13623551 := bstep (se 1 (by rfl) ⟨10217663, by rfl⟩ : syracuseStep 13623551 = 20435327) B20435327
theorem B1196315 : Blo 1194414 1196315 := bstep (se 1 (by rfl) ⟨897236, by rfl⟩ : syracuseStep 1196315 = 1794473) B1794473
theorem B1196351 : Blo 1194414 1196351 := bstep (se 1 (by rfl) ⟨897263, by rfl⟩ : syracuseStep 1196351 = 1794527) B1794527
theorem B8184131 : Blo 1194414 8184131 := bstep (se 1 (by rfl) ⟨6138098, by rfl⟩ : syracuseStep 8184131 = 12276197) B12276197
theorem B1794407 : Blo 1194414 1794407 := bstep (se 1 (by rfl) ⟨1345805, by rfl⟩ : syracuseStep 1794407 = 2691611) B2691611
theorem B2761991 : Blo 1194414 2761991 := bstep (se 1 (by rfl) ⟨2071493, by rfl⟩ : syracuseStep 2761991 = 4142987) B4142987
theorem B5105177 : Blo 1194414 5105177 := bstep (se 2 (by rfl) ⟨1914441, by rfl⟩ : syracuseStep 5105177 = 3828883) B3828883
theorem B6547225 : Blo 1194414 6547225 := bstep (se 2 (by rfl) ⟨2455209, by rfl⟩ : syracuseStep 6547225 = 4910419) B4910419
theorem B7653203 : Blo 1194414 7653203 := bstep (se 1 (by rfl) ⟨5739902, by rfl⟩ : syracuseStep 7653203 = 11479805) B11479805
theorem B4540319 : Blo 1194414 4540319 := bstep (se 1 (by rfl) ⟨3405239, by rfl⟩ : syracuseStep 4540319 = 6810479) B6810479
theorem B1345531 : Blo 1194414 1345531 := bstep (se 1 (by rfl) ⟨1009148, by rfl⟩ : syracuseStep 1345531 = 2018297) B2018297
theorem B6047783 : Blo 1194414 6047783 := bstep (se 1 (by rfl) ⟨4535837, by rfl⟩ : syracuseStep 6047783 = 9071675) B9071675
theorem B3401833 : Blo 1194414 3401833 := bstep (se 2 (by rfl) ⟨1275687, by rfl⟩ : syracuseStep 3401833 = 2551375) B2551375
theorem B4311143 : Blo 1194414 4311143 := bstep (se 1 (by rfl) ⟨3233357, by rfl⟩ : syracuseStep 4311143 = 6466715) B6466715
theorem B10496135 : Blo 1194414 10496135 := bstep (se 1 (by rfl) ⟨7872101, by rfl⟩ : syracuseStep 10496135 = 15744203) B15744203
theorem B2689199 : Blo 1194414 2689199 := bstep (se 1 (by rfl) ⟨2016899, by rfl⟩ : syracuseStep 2689199 = 4033799) B4033799
theorem B4033043 : Blo 1194414 4033043 := bstep (se 1 (by rfl) ⟨3024782, by rfl⟩ : syracuseStep 4033043 = 6049565) B6049565
theorem B41372855 : Blo 1194414 41372855 := bstep (se 1 (by rfl) ⟨31029641, by rfl⟩ : syracuseStep 41372855 = 62059283) B62059283
theorem B2690279 : Blo 1194414 2690279 := bstep (se 1 (by rfl) ⟨2017709, by rfl⟩ : syracuseStep 2690279 = 4035419) B4035419
theorem B3829153 : Blo 1194414 3829153 := bstep (se 2 (by rfl) ⟨1435932, by rfl⟩ : syracuseStep 3829153 = 2871865) B2871865
theorem B4034177 : Blo 1194414 4034177 := bstep (se 2 (by rfl) ⟨1512816, by rfl⟩ : syracuseStep 4034177 = 3025633) B3025633
theorem B24858361 : Blo 1194414 24858361 := bstep (se 2 (by rfl) ⟨9321885, by rfl⟩ : syracuseStep 24858361 = 18643771) B18643771
theorem B5107535 : Blo 1194414 5107535 := bstep (se 1 (by rfl) ⟨3830651, by rfl⟩ : syracuseStep 5107535 = 7661303) B7661303
theorem B6049889 : Blo 1194414 6049889 := bstep (se 2 (by rfl) ⟨2268708, by rfl⟩ : syracuseStep 6049889 = 4537417) B4537417
theorem B2691431 : Blo 1194414 2691431 := bstep (se 1 (by rfl) ⟨2018573, by rfl⟩ : syracuseStep 2691431 = 4037147) B4037147
theorem B5820863 : Blo 1194414 5820863 := bstep (se 1 (by rfl) ⟨4365647, by rfl⟩ : syracuseStep 5820863 = 8731295) B8731295
theorem B58167881 : Blo 1194414 58167881 := bstep (se 2 (by rfl) ⟨21812955, by rfl⟩ : syracuseStep 58167881 = 43625911) B43625911
theorem B1512047 : Blo 1194414 1512047 := bstep (se 1 (by rfl) ⟨1134035, by rfl⟩ : syracuseStep 1512047 = 2268071) B2268071
theorem B2691809 : Blo 1194414 2691809 := bstep (se 2 (by rfl) ⟨1009428, by rfl⟩ : syracuseStep 2691809 = 2018857) B2018857
theorem B113423287 : Blo 1194414 113423287 := bstep (se 1 (by rfl) ⟨85067465, by rfl⟩ : syracuseStep 113423287 = 170134931) B170134931
theorem B4846547 : Blo 1194414 4846547 := bstep (se 1 (by rfl) ⟨3634910, by rfl⟩ : syracuseStep 4846547 = 7269821) B7269821
theorem B1701167 : Blo 1194414 1701167 := bstep (se 1 (by rfl) ⟨1275875, by rfl⟩ : syracuseStep 1701167 = 2551751) B2551751
theorem B1914167 : Blo 1194414 1914167 := bstep (se 1 (by rfl) ⟨1435625, by rfl⟩ : syracuseStep 1914167 = 2871251) B2871251
theorem B4535945 : Blo 1194414 4535945 := bstep (se 2 (by rfl) ⟨1700979, by rfl⟩ : syracuseStep 4535945 = 3401959) B3401959
theorem B1791899 : Blo 1194414 1791899 := bstep (se 1 (by rfl) ⟨1343924, by rfl⟩ : syracuseStep 1791899 = 2687849) B2687849
theorem B9828499 : Blo 1194414 9828499 := bstep (se 1 (by rfl) ⟨7371374, by rfl⟩ : syracuseStep 9828499 = 14742749) B14742749
theorem B20715743 : Blo 1194414 20715743 := bstep (se 1 (by rfl) ⟨15536807, by rfl⟩ : syracuseStep 20715743 = 31073615) B31073615
theorem B1194479 : Blo 1194414 1194479 := bstep (se 1 (by rfl) ⟨895859, by rfl⟩ : syracuseStep 1194479 = 1791719) B1791719
theorem B6052481 : Blo 1194414 6052481 := bstep (se 2 (by rfl) ⟨2269680, by rfl⟩ : syracuseStep 6052481 = 4539361) B4539361
theorem B5741209 : Blo 1194414 5741209 := bstep (se 2 (by rfl) ⟨2152953, by rfl⟩ : syracuseStep 5741209 = 4305907) B4305907
theorem B11483801 : Blo 1194414 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B4848299 : Blo 1194414 4848299 := bstep (se 1 (by rfl) ⟨3636224, by rfl⟩ : syracuseStep 4848299 = 7272449) B7272449
theorem B1195035 : Blo 1194414 1195035 := bstep (se 1 (by rfl) ⟨896276, by rfl⟩ : syracuseStep 1195035 = 1792553) B1792553
theorem B10902833 : Blo 1194414 10902833 := bstep (se 2 (by rfl) ⟨4088562, by rfl⟩ : syracuseStep 10902833 = 8177125) B8177125
theorem B1195367 : Blo 1194414 1195367 := bstep (se 1 (by rfl) ⟨896525, by rfl⟩ : syracuseStep 1195367 = 1793051) B1793051
theorem B23928275 : Blo 1194414 23928275 := bstep (se 1 (by rfl) ⟨17946206, by rfl⟩ : syracuseStep 23928275 = 35892413) B35892413
theorem B4537903 : Blo 1194414 4537903 := bstep (se 1 (by rfl) ⟨3403427, by rfl⟩ : syracuseStep 4537903 = 6806855) B6806855
theorem B98074223 : Blo 1194414 98074223 := bstep (se 1 (by rfl) ⟨73555667, by rfl⟩ : syracuseStep 98074223 = 147111335) B147111335
theorem B1195867 : Blo 1194414 1195867 := bstep (se 1 (by rfl) ⟨896900, by rfl⟩ : syracuseStep 1195867 = 1793801) B1793801
theorem B1195967 : Blo 1194414 1195967 := bstep (se 1 (by rfl) ⟨896975, by rfl⟩ : syracuseStep 1195967 = 1793951) B1793951
theorem B66338777 : Blo 1194414 66338777 := bstep (se 2 (by rfl) ⟨24877041, by rfl⟩ : syracuseStep 66338777 = 49754083) B49754083
theorem B1196199 : Blo 1194414 1196199 := bstep (se 1 (by rfl) ⟨897149, by rfl⟩ : syracuseStep 1196199 = 1794299) B1794299
theorem B5456087 : Blo 1194414 5456087 := bstep (se 1 (by rfl) ⟨4092065, by rfl⟩ : syracuseStep 5456087 = 8184131) B8184131
theorem B1794287 : Blo 1194414 1794287 := bstep (se 1 (by rfl) ⟨1345715, by rfl⟩ : syracuseStep 1794287 = 2691431) B2691431
theorem B1196271 : Blo 1194414 1196271 := bstep (se 1 (by rfl) ⟨897203, by rfl⟩ : syracuseStep 1196271 = 1794407) B1794407
theorem B1794539 : Blo 1194414 1794539 := bstep (se 1 (by rfl) ⟨1345904, by rfl⟩ : syracuseStep 1794539 = 2691809) B2691809
theorem B3023963 : Blo 1194414 3023963 := bstep (se 1 (by rfl) ⟨2267972, by rfl⟩ : syracuseStep 3023963 = 4535945) B4535945
theorem B4031855 : Blo 1194414 4031855 := bstep (se 1 (by rfl) ⟨3023891, by rfl⟩ : syracuseStep 4031855 = 6047783) B6047783
theorem B6997423 : Blo 1194414 6997423 := bstep (se 1 (by rfl) ⟨5248067, by rfl⟩ : syracuseStep 6997423 = 10496135) B10496135
theorem B4032125 : Blo 1194414 4032125 := bstep (se 3 (by rfl) ⟨756023, by rfl⟩ : syracuseStep 4032125 = 1512047) B1512047
theorem B2688695 : Blo 1194414 2688695 := bstep (se 1 (by rfl) ⟨2016521, by rfl⟩ : syracuseStep 2688695 = 4033043) B4033043
theorem B5105537 : Blo 1194414 5105537 := bstep (se 2 (by rfl) ⟨1914576, by rfl⟩ : syracuseStep 5105537 = 3829153) B3829153
theorem B7268555 : Blo 1194414 7268555 := bstep (se 1 (by rfl) ⟨5451416, by rfl⟩ : syracuseStep 7268555 = 10902833) B10902833
theorem B15952183 : Blo 1194414 15952183 := bstep (se 1 (by rfl) ⟨11964137, by rfl⟩ : syracuseStep 15952183 = 23928275) B23928275
theorem B65382815 : Blo 1194414 65382815 := bstep (se 1 (by rfl) ⟨49037111, by rfl⟩ : syracuseStep 65382815 = 98074223) B98074223
theorem B2689451 : Blo 1194414 2689451 := bstep (se 1 (by rfl) ⟨2017088, by rfl⟩ : syracuseStep 2689451 = 4034177) B4034177
theorem B4033259 : Blo 1194414 4033259 := bstep (se 1 (by rfl) ⟨3024944, by rfl⟩ : syracuseStep 4033259 = 6049889) B6049889
theorem B3231031 : Blo 1194414 3231031 := bstep (se 1 (by rfl) ⟨2423273, by rfl⟩ : syracuseStep 3231031 = 4846547) B4846547
theorem B7654945 : Blo 1194414 7654945 := bstep (se 2 (by rfl) ⟨2870604, by rfl⟩ : syracuseStep 7654945 = 5741209) B5741209
theorem B3403451 : Blo 1194414 3403451 := bstep (se 1 (by rfl) ⟨2552588, by rfl⟩ : syracuseStep 3403451 = 5105177) B5105177
theorem B3026879 : Blo 1194414 3026879 := bstep (se 1 (by rfl) ⟨2270159, by rfl⟩ : syracuseStep 3026879 = 4540319) B4540319
theorem B4034987 : Blo 1194414 4034987 := bstep (se 1 (by rfl) ⟨3026240, by rfl⟩ : syracuseStep 4034987 = 6052481) B6052481
theorem B7655867 : Blo 1194414 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B3232199 : Blo 1194414 3232199 := bstep (se 1 (by rfl) ⟨2424149, by rfl⟩ : syracuseStep 3232199 = 4848299) B4848299
theorem B6050537 : Blo 1194414 6050537 := bstep (se 2 (by rfl) ⟨2268951, by rfl⟩ : syracuseStep 6050537 = 4537903) B4537903
theorem B8729633 : Blo 1194414 8729633 := bstep (se 2 (by rfl) ⟨3273612, by rfl⟩ : syracuseStep 8729633 = 6547225) B6547225
theorem B3405023 : Blo 1194414 3405023 := bstep (se 1 (by rfl) ⟨2553767, by rfl⟩ : syracuseStep 3405023 = 5107535) B5107535
theorem B44225851 : Blo 1194414 44225851 := bstep (se 1 (by rfl) ⟨33169388, by rfl⟩ : syracuseStep 44225851 = 66338777) B66338777
theorem B4535777 : Blo 1194414 4535777 := bstep (se 2 (by rfl) ⟨1700916, by rfl⟩ : syracuseStep 4535777 = 3401833) B3401833
theorem B9082367 : Blo 1194414 9082367 := bstep (se 1 (by rfl) ⟨6811775, by rfl⟩ : syracuseStep 9082367 = 13623551) B13623551
theorem B13104665 : Blo 1194414 13104665 := bstep (se 2 (by rfl) ⟨4914249, by rfl⟩ : syracuseStep 13104665 = 9828499) B9828499
theorem B38778587 : Blo 1194414 38778587 := bstep (se 1 (by rfl) ⟨29083940, by rfl⟩ : syracuseStep 38778587 = 58167881) B58167881
theorem B4536445 : Blo 1194414 4536445 := bstep (se 3 (by rfl) ⟨850583, by rfl⟩ : syracuseStep 4536445 = 1701167) B1701167
theorem B1841327 : Blo 1194414 1841327 := bstep (se 1 (by rfl) ⟨1380995, by rfl⟩ : syracuseStep 1841327 = 2761991) B2761991
theorem B1276111 : Blo 1194414 1276111 := bstep (se 1 (by rfl) ⟨957083, by rfl⟩ : syracuseStep 1276111 = 1914167) B1914167
theorem B15522301 : Blo 1194414 15522301 := bstep (se 3 (by rfl) ⟨2910431, by rfl⟩ : syracuseStep 15522301 = 5820863) B5820863
theorem B5102135 : Blo 1194414 5102135 := bstep (se 1 (by rfl) ⟨3826601, by rfl⟩ : syracuseStep 5102135 = 7653203) B7653203
theorem B151231049 : Blo 1194414 151231049 := bstep (se 2 (by rfl) ⟨56711643, by rfl⟩ : syracuseStep 151231049 = 113423287) B113423287
theorem B1194599 : Blo 1194414 1194599 := bstep (se 1 (by rfl) ⟨895949, by rfl⟩ : syracuseStep 1194599 = 1791899) B1791899
theorem B2874095 : Blo 1194414 2874095 := bstep (se 1 (by rfl) ⟨2155571, by rfl⟩ : syracuseStep 2874095 = 4311143) B4311143
theorem B1792799 : Blo 1194414 1792799 := bstep (se 1 (by rfl) ⟨1344599, by rfl⟩ : syracuseStep 1792799 = 2689199) B2689199
theorem B13810495 : Blo 1194414 13810495 := bstep (se 1 (by rfl) ⟨10357871, by rfl⟩ : syracuseStep 13810495 = 20715743) B20715743
theorem B27581903 : Blo 1194414 27581903 := bstep (se 1 (by rfl) ⟨20686427, by rfl⟩ : syracuseStep 27581903 = 41372855) B41372855
theorem B1793519 : Blo 1194414 1793519 := bstep (se 1 (by rfl) ⟨1345139, by rfl⟩ : syracuseStep 1793519 = 2690279) B2690279
theorem B33144481 : Blo 1194414 33144481 := bstep (se 2 (by rfl) ⟨12429180, by rfl⟩ : syracuseStep 33144481 = 24858361) B24858361
theorem B1794041 : Blo 1194414 1794041 := bstep (se 2 (by rfl) ⟨672765, by rfl⟩ : syracuseStep 1794041 = 1345531) B1345531
theorem B3637391 : Blo 1194414 3637391 := bstep (se 1 (by rfl) ⟨2728043, by rfl⟩ : syracuseStep 3637391 = 5456087) B5456087
theorem B1196191 : Blo 1194414 1196191 := bstep (se 1 (by rfl) ⟨897143, by rfl⟩ : syracuseStep 1196191 = 1794287) B1794287
theorem B5103911 : Blo 1194414 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B2154799 : Blo 1194414 2154799 := bstep (se 1 (by rfl) ⟨1616099, by rfl⟩ : syracuseStep 2154799 = 3232199) B3232199
theorem B1196359 : Blo 1194414 1196359 := bstep (se 1 (by rfl) ⟨897269, by rfl⟩ : syracuseStep 1196359 = 1794539) B1794539
theorem B19382813 : Blo 1194414 19382813 := bstep (se 3 (by rfl) ⟨3634277, by rfl⟩ : syracuseStep 19382813 = 7268555) B7268555
theorem B2015975 : Blo 1194414 2015975 := bstep (se 1 (by rfl) ⟨1511981, by rfl⟩ : syracuseStep 2015975 = 3023963) B3023963
theorem B2270015 : Blo 1194414 2270015 := bstep (se 1 (by rfl) ⟨1702511, by rfl⟩ : syracuseStep 2270015 = 3405023) B3405023
theorem B2687903 : Blo 1194414 2687903 := bstep (se 1 (by rfl) ⟨2015927, by rfl⟩ : syracuseStep 2687903 = 4031855) B4031855
theorem B3023851 : Blo 1194414 3023851 := bstep (se 1 (by rfl) ⟨2267888, by rfl⟩ : syracuseStep 3023851 = 4535777) B4535777
theorem B6054911 : Blo 1194414 6054911 := bstep (se 1 (by rfl) ⟨4541183, by rfl⟩ : syracuseStep 6054911 = 9082367) B9082367
theorem B2688083 : Blo 1194414 2688083 := bstep (se 1 (by rfl) ⟨2016062, by rfl⟩ : syracuseStep 2688083 = 4032125) B4032125
theorem B3401423 : Blo 1194414 3401423 := bstep (se 1 (by rfl) ⟨2551067, by rfl⟩ : syracuseStep 3401423 = 5102135) B5102135
theorem B100820699 : Blo 1194414 100820699 := bstep (se 1 (by rfl) ⟨75615524, by rfl⟩ : syracuseStep 100820699 = 151231049) B151231049
theorem B58967801 : Blo 1194414 58967801 := bstep (se 2 (by rfl) ⟨22112925, by rfl⟩ : syracuseStep 58967801 = 44225851) B44225851
theorem B2688839 : Blo 1194414 2688839 := bstep (se 1 (by rfl) ⟨2016629, by rfl⟩ : syracuseStep 2688839 = 4033259) B4033259
theorem B2017919 : Blo 1194414 2017919 := bstep (se 1 (by rfl) ⟨1513439, by rfl⟩ : syracuseStep 2017919 = 3026879) B3026879
theorem B6048593 : Blo 1194414 6048593 := bstep (se 2 (by rfl) ⟨2268222, by rfl⟩ : syracuseStep 6048593 = 4536445) B4536445
theorem B2689991 : Blo 1194414 2689991 := bstep (se 1 (by rfl) ⟨2017493, by rfl⟩ : syracuseStep 2689991 = 4034987) B4034987
theorem B4033691 : Blo 1194414 4033691 := bstep (se 1 (by rfl) ⟨3025268, by rfl⟩ : syracuseStep 4033691 = 6050537) B6050537
theorem B20696401 : Blo 1194414 20696401 := bstep (se 2 (by rfl) ⟨7761150, by rfl⟩ : syracuseStep 20696401 = 15522301) B15522301
theorem B8736443 : Blo 1194414 8736443 := bstep (se 1 (by rfl) ⟨6552332, by rfl⟩ : syracuseStep 8736443 = 13104665) B13104665
theorem B3403691 : Blo 1194414 3403691 := bstep (se 1 (by rfl) ⟨2552768, by rfl⟩ : syracuseStep 3403691 = 5105537) B5105537
theorem B85078309 : Blo 1194414 85078309 := bstep (se 4 (by rfl) ⟨7976091, by rfl⟩ : syracuseStep 85078309 = 15952183) B15952183
theorem B1196027 : Blo 1194414 1196027 := bstep (se 1 (by rfl) ⟨897020, by rfl⟩ : syracuseStep 1196027 = 1794041) B1794041
theorem B44192641 : Blo 1194414 44192641 := bstep (se 2 (by rfl) ⟨16572240, by rfl⟩ : syracuseStep 44192641 = 33144481) B33144481
theorem B18387935 : Blo 1194414 18387935 := bstep (se 1 (by rfl) ⟨13790951, by rfl⟩ : syracuseStep 18387935 = 27581903) B27581903
theorem B23279021 : Blo 1194414 23279021 := bstep (se 3 (by rfl) ⟨4364816, by rfl⟩ : syracuseStep 23279021 = 8729633) B8729633
theorem B1701481 : Blo 1194414 1701481 := bstep (se 2 (by rfl) ⟨638055, by rfl⟩ : syracuseStep 1701481 = 1276111) B1276111
theorem B18413993 : Blo 1194414 18413993 := bstep (se 2 (by rfl) ⟨6905247, by rfl⟩ : syracuseStep 18413993 = 13810495) B13810495
theorem B1792463 : Blo 1194414 1792463 := bstep (se 1 (by rfl) ⟨1344347, by rfl⟩ : syracuseStep 1792463 = 2688695) B2688695
theorem B25852391 : Blo 1194414 25852391 := bstep (se 1 (by rfl) ⟨19389293, by rfl⟩ : syracuseStep 25852391 = 38778587) B38778587
theorem B1227551 : Blo 1194414 1227551 := bstep (se 1 (by rfl) ⟨920663, by rfl⟩ : syracuseStep 1227551 = 1841327) B1841327
theorem B43588543 : Blo 1194414 43588543 := bstep (se 1 (by rfl) ⟨32691407, by rfl⟩ : syracuseStep 43588543 = 65382815) B65382815
theorem B1792967 : Blo 1194414 1792967 := bstep (se 1 (by rfl) ⟨1344725, by rfl⟩ : syracuseStep 1792967 = 2689451) B2689451
theorem B4308041 : Blo 1194414 4308041 := bstep (se 2 (by rfl) ⟨1615515, by rfl⟩ : syracuseStep 4308041 = 3231031) B3231031
theorem B1916063 : Blo 1194414 1916063 := bstep (se 1 (by rfl) ⟨1437047, by rfl⟩ : syracuseStep 1916063 = 2874095) B2874095
theorem B1195199 : Blo 1194414 1195199 := bstep (se 1 (by rfl) ⟨896399, by rfl⟩ : syracuseStep 1195199 = 1792799) B1792799
theorem B9329897 : Blo 1194414 9329897 := bstep (se 2 (by rfl) ⟨3498711, by rfl⟩ : syracuseStep 9329897 = 6997423) B6997423
theorem B10206593 : Blo 1194414 10206593 := bstep (se 2 (by rfl) ⟨3827472, by rfl⟩ : syracuseStep 10206593 = 7654945) B7654945
theorem B1195679 : Blo 1194414 1195679 := bstep (se 1 (by rfl) ⟨896759, by rfl⟩ : syracuseStep 1195679 = 1793519) B1793519
theorem B2268967 : Blo 1194414 2268967 := bstep (se 1 (by rfl) ⟨1701725, by rfl⟩ : syracuseStep 2268967 = 3403451) B3403451
theorem B1343983 : Blo 1194414 1343983 := bstep (se 1 (by rfl) ⟨1007987, by rfl⟩ : syracuseStep 1343983 = 2015975) B2015975
theorem B49103981 : Blo 1194414 49103981 := bstep (se 3 (by rfl) ⟨9206996, by rfl⟩ : syracuseStep 49103981 = 18413993) B18413993
theorem B4031801 : Blo 1194414 4031801 := bstep (se 2 (by rfl) ⟨1511925, by rfl⟩ : syracuseStep 4031801 = 3023851) B3023851
theorem B38798837 : Blo 1194414 38798837 := bstep (se 5 (by rfl) ⟨1818695, by rfl⟩ : syracuseStep 38798837 = 3637391) B3637391
theorem B1345279 : Blo 1194414 1345279 := bstep (se 1 (by rfl) ⟨1008959, by rfl⟩ : syracuseStep 1345279 = 2017919) B2017919
theorem B4032395 : Blo 1194414 4032395 := bstep (se 1 (by rfl) ⟨3024296, by rfl⟩ : syracuseStep 4032395 = 6048593) B6048593
theorem B2689127 : Blo 1194414 2689127 := bstep (se 1 (by rfl) ⟨2016845, by rfl⟩ : syracuseStep 2689127 = 4033691) B4033691
theorem B6219931 : Blo 1194414 6219931 := bstep (se 1 (by rfl) ⟨4664948, by rfl⟩ : syracuseStep 6219931 = 9329897) B9329897
theorem B3025289 : Blo 1194414 3025289 := bstep (se 2 (by rfl) ⟨1134483, by rfl⟩ : syracuseStep 3025289 = 2268967) B2268967
theorem B13093877 : Blo 1194414 13093877 := bstep (se 5 (by rfl) ⟨613775, by rfl⟩ : syracuseStep 13093877 = 1227551) B1227551
theorem B12921875 : Blo 1194414 12921875 := bstep (se 1 (by rfl) ⟨9691406, by rfl⟩ : syracuseStep 12921875 = 19382813) B19382813
theorem B113437745 : Blo 1194414 113437745 := bstep (se 2 (by rfl) ⟨42539154, by rfl⟩ : syracuseStep 113437745 = 85078309) B85078309
theorem B12258623 : Blo 1194414 12258623 := bstep (se 1 (by rfl) ⟨9193967, by rfl⟩ : syracuseStep 12258623 = 18387935) B18387935
theorem B13610429 : Blo 1194414 13610429 := bstep (se 3 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 13610429 = 5103911) B5103911
theorem B15519347 : Blo 1194414 15519347 := bstep (se 1 (by rfl) ⟨11639510, by rfl⟩ : syracuseStep 15519347 = 23279021) B23279021
theorem B58118057 : Blo 1194414 58118057 := bstep (se 2 (by rfl) ⟨21794271, by rfl⟩ : syracuseStep 58118057 = 43588543) B43588543
theorem B27595201 : Blo 1194414 27595201 := bstep (se 2 (by rfl) ⟨10348200, by rfl⟩ : syracuseStep 27595201 = 20696401) B20696401
theorem B2872027 : Blo 1194414 2872027 := bstep (se 1 (by rfl) ⟨2154020, by rfl⟩ : syracuseStep 2872027 = 4308041) B4308041
theorem B6804395 : Blo 1194414 6804395 := bstep (se 1 (by rfl) ⟨5103296, by rfl⟩ : syracuseStep 6804395 = 10206593) B10206593
theorem B2873065 : Blo 1194414 2873065 := bstep (se 2 (by rfl) ⟨1077399, by rfl⟩ : syracuseStep 2873065 = 2154799) B2154799
theorem B1513343 : Blo 1194414 1513343 := bstep (se 1 (by rfl) ⟨1135007, by rfl⟩ : syracuseStep 1513343 = 2270015) B2270015
theorem B1791935 : Blo 1194414 1791935 := bstep (se 1 (by rfl) ⟨1343951, by rfl⟩ : syracuseStep 1791935 = 2687903) B2687903
theorem B4036607 : Blo 1194414 4036607 := bstep (se 1 (by rfl) ⟨3027455, by rfl⟩ : syracuseStep 4036607 = 6054911) B6054911
theorem B1792055 : Blo 1194414 1792055 := bstep (se 1 (by rfl) ⟨1344041, by rfl⟩ : syracuseStep 1792055 = 2688083) B2688083
theorem B2267615 : Blo 1194414 2267615 := bstep (se 1 (by rfl) ⟨1700711, by rfl⟩ : syracuseStep 2267615 = 3401423) B3401423
theorem B67213799 : Blo 1194414 67213799 := bstep (se 1 (by rfl) ⟨50410349, by rfl⟩ : syracuseStep 67213799 = 100820699) B100820699
theorem B39311867 : Blo 1194414 39311867 := bstep (se 1 (by rfl) ⟨29483900, by rfl⟩ : syracuseStep 39311867 = 58967801) B58967801
theorem B58923521 : Blo 1194414 58923521 := bstep (se 2 (by rfl) ⟨22096320, by rfl⟩ : syracuseStep 58923521 = 44192641) B44192641
theorem B1792559 : Blo 1194414 1792559 := bstep (se 1 (by rfl) ⟨1344419, by rfl⟩ : syracuseStep 1792559 = 2688839) B2688839
theorem B1194975 : Blo 1194414 1194975 := bstep (se 1 (by rfl) ⟨896231, by rfl⟩ : syracuseStep 1194975 = 1792463) B1792463
theorem B17234927 : Blo 1194414 17234927 := bstep (se 1 (by rfl) ⟨12926195, by rfl⟩ : syracuseStep 17234927 = 25852391) B25852391
theorem B1195311 : Blo 1194414 1195311 := bstep (se 1 (by rfl) ⟨896483, by rfl⟩ : syracuseStep 1195311 = 1792967) B1792967
theorem B1793327 : Blo 1194414 1793327 := bstep (se 1 (by rfl) ⟨1344995, by rfl⟩ : syracuseStep 1793327 = 2689991) B2689991
theorem B1277375 : Blo 1194414 1277375 := bstep (se 1 (by rfl) ⟨958031, by rfl⟩ : syracuseStep 1277375 = 1916063) B1916063
theorem B2268641 : Blo 1194414 2268641 := bstep (se 2 (by rfl) ⟨850740, by rfl⟩ : syracuseStep 2268641 = 1701481) B1701481
theorem B5824295 : Blo 1194414 5824295 := bstep (se 1 (by rfl) ⟨4368221, by rfl⟩ : syracuseStep 5824295 = 8736443) B8736443
theorem B2269127 : Blo 1194414 2269127 := bstep (se 1 (by rfl) ⟨1701845, by rfl⟩ : syracuseStep 2269127 = 3403691) B3403691
theorem B32735987 : Blo 1194414 32735987 := bstep (se 1 (by rfl) ⟨24551990, by rfl⟩ : syracuseStep 32735987 = 49103981) B49103981
theorem B2687867 : Blo 1194414 2687867 := bstep (se 1 (by rfl) ⟨2015900, by rfl⟩ : syracuseStep 2687867 = 4031801) B4031801
theorem B6046973 : Blo 1194414 6046973 := bstep (se 3 (by rfl) ⟨1133807, by rfl⟩ : syracuseStep 6046973 = 2267615) B2267615
theorem B2688263 : Blo 1194414 2688263 := bstep (se 1 (by rfl) ⟨2016197, by rfl⟩ : syracuseStep 2688263 = 4032395) B4032395
theorem B2016859 : Blo 1194414 2016859 := bstep (se 1 (by rfl) ⟨1512644, by rfl⟩ : syracuseStep 2016859 = 3025289) B3025289
theorem B26207911 : Blo 1194414 26207911 := bstep (se 1 (by rfl) ⟨19655933, by rfl⟩ : syracuseStep 26207911 = 39311867) B39311867
theorem B39282347 : Blo 1194414 39282347 := bstep (se 1 (by rfl) ⟨29461760, by rfl⟩ : syracuseStep 39282347 = 58923521) B58923521
theorem B8293241 : Blo 1194414 8293241 := bstep (se 2 (by rfl) ⟨3109965, by rfl⟩ : syracuseStep 8293241 = 6219931) B6219931
theorem B36793601 : Blo 1194414 36793601 := bstep (se 2 (by rfl) ⟨13797600, by rfl⟩ : syracuseStep 36793601 = 27595201) B27595201
theorem B3829369 : Blo 1194414 3829369 := bstep (se 2 (by rfl) ⟨1436013, by rfl⟩ : syracuseStep 3829369 = 2872027) B2872027
theorem B25865891 : Blo 1194414 25865891 := bstep (se 1 (by rfl) ⟨19399418, by rfl⟩ : syracuseStep 25865891 = 38798837) B38798837
theorem B2691071 : Blo 1194414 2691071 := bstep (se 1 (by rfl) ⟨2018303, by rfl⟩ : syracuseStep 2691071 = 4036607) B4036607
theorem B11489951 : Blo 1194414 11489951 := bstep (se 1 (by rfl) ⟨8617463, by rfl⟩ : syracuseStep 11489951 = 17234927) B17234927
theorem B8729251 : Blo 1194414 8729251 := bstep (se 1 (by rfl) ⟨6546938, by rfl⟩ : syracuseStep 8729251 = 13093877) B13093877
theorem B8614583 : Blo 1194414 8614583 := bstep (se 1 (by rfl) ⟨6460937, by rfl⟩ : syracuseStep 8614583 = 12921875) B12921875
theorem B75625163 : Blo 1194414 75625163 := bstep (se 1 (by rfl) ⟨56718872, by rfl⟩ : syracuseStep 75625163 = 113437745) B113437745
theorem B8172415 : Blo 1194414 8172415 := bstep (se 1 (by rfl) ⟨6129311, by rfl⟩ : syracuseStep 8172415 = 12258623) B12258623
theorem B9073619 : Blo 1194414 9073619 := bstep (se 1 (by rfl) ⟨6805214, by rfl⟩ : syracuseStep 9073619 = 13610429) B13610429
theorem B3830753 : Blo 1194414 3830753 := bstep (se 2 (by rfl) ⟨1436532, by rfl⟩ : syracuseStep 3830753 = 2873065) B2873065
theorem B1512427 : Blo 1194414 1512427 := bstep (se 1 (by rfl) ⟨1134320, by rfl⟩ : syracuseStep 1512427 = 2268641) B2268641
theorem B4035581 : Blo 1194414 4035581 := bstep (se 3 (by rfl) ⟨756671, by rfl⟩ : syracuseStep 4035581 = 1513343) B1513343
theorem B38745371 : Blo 1194414 38745371 := bstep (se 1 (by rfl) ⟨29059028, by rfl⟩ : syracuseStep 38745371 = 58118057) B58118057
theorem B1512751 : Blo 1194414 1512751 := bstep (se 1 (by rfl) ⟨1134563, by rfl⟩ : syracuseStep 1512751 = 2269127) B2269127
theorem B4536263 : Blo 1194414 4536263 := bstep (se 1 (by rfl) ⟨3402197, by rfl⟩ : syracuseStep 4536263 = 6804395) B6804395
theorem B1791977 : Blo 1194414 1791977 := bstep (se 2 (by rfl) ⟨671991, by rfl⟩ : syracuseStep 1791977 = 1343983) B1343983
theorem B3406333 : Blo 1194414 3406333 := bstep (se 3 (by rfl) ⟨638687, by rfl⟩ : syracuseStep 3406333 = 1277375) B1277375
theorem B1194623 : Blo 1194414 1194623 := bstep (se 1 (by rfl) ⟨895967, by rfl⟩ : syracuseStep 1194623 = 1791935) B1791935
theorem B1194703 : Blo 1194414 1194703 := bstep (se 1 (by rfl) ⟨896027, by rfl⟩ : syracuseStep 1194703 = 1792055) B1792055
theorem B1792751 : Blo 1194414 1792751 := bstep (se 1 (by rfl) ⟨1344563, by rfl⟩ : syracuseStep 1792751 = 2689127) B2689127
theorem B44809199 : Blo 1194414 44809199 := bstep (se 1 (by rfl) ⟨33606899, by rfl⟩ : syracuseStep 44809199 = 67213799) B67213799
theorem B1195039 : Blo 1194414 1195039 := bstep (se 1 (by rfl) ⟨896279, by rfl⟩ : syracuseStep 1195039 = 1792559) B1792559
theorem B1195551 : Blo 1194414 1195551 := bstep (se 1 (by rfl) ⟨896663, by rfl⟩ : syracuseStep 1195551 = 1793327) B1793327
theorem B1793705 : Blo 1194414 1793705 := bstep (se 2 (by rfl) ⟨672639, by rfl⟩ : syracuseStep 1793705 = 1345279) B1345279
theorem B10346231 : Blo 1194414 10346231 := bstep (se 1 (by rfl) ⟨7759673, by rfl⟩ : syracuseStep 10346231 = 15519347) B15519347
theorem B3882863 : Blo 1194414 3882863 := bstep (se 1 (by rfl) ⟨2912147, by rfl⟩ : syracuseStep 3882863 = 5824295) B5824295
theorem B5743055 : Blo 1194414 5743055 := bstep (se 1 (by rfl) ⟨4307291, by rfl⟩ : syracuseStep 5743055 = 8614583) B8614583
theorem B21823991 : Blo 1194414 21823991 := bstep (se 1 (by rfl) ⟨16367993, by rfl⟩ : syracuseStep 21823991 = 32735987) B32735987
theorem B4031315 : Blo 1194414 4031315 := bstep (se 1 (by rfl) ⟨3023486, by rfl⟩ : syracuseStep 4031315 = 6046973) B6046973
theorem B25830247 : Blo 1194414 25830247 := bstep (se 1 (by rfl) ⟨19372685, by rfl⟩ : syracuseStep 25830247 = 38745371) B38745371
theorem B10896553 : Blo 1194414 10896553 := bstep (se 2 (by rfl) ⟨4086207, by rfl⟩ : syracuseStep 10896553 = 8172415) B8172415
theorem B3024175 : Blo 1194414 3024175 := bstep (se 1 (by rfl) ⟨2268131, by rfl⟩ : syracuseStep 3024175 = 4536263) B4536263
theorem B2016569 : Blo 1194414 2016569 := bstep (se 2 (by rfl) ⟨756213, by rfl⟩ : syracuseStep 2016569 = 1512427) B1512427
theorem B2017001 : Blo 1194414 2017001 := bstep (se 2 (by rfl) ⟨756375, by rfl⟩ : syracuseStep 2017001 = 1512751) B1512751
theorem B30639869 : Blo 1194414 30639869 := bstep (se 3 (by rfl) ⟨5744975, by rfl⟩ : syracuseStep 30639869 = 11489951) B11489951
theorem B2689145 : Blo 1194414 2689145 := bstep (se 2 (by rfl) ⟨1008429, by rfl⟩ : syracuseStep 2689145 = 2016859) B2016859
theorem B5105825 : Blo 1194414 5105825 := bstep (se 2 (by rfl) ⟨1914684, by rfl⟩ : syracuseStep 5105825 = 3829369) B3829369
theorem B24529067 : Blo 1194414 24529067 := bstep (se 1 (by rfl) ⟨18396800, by rfl⟩ : syracuseStep 24529067 = 36793601) B36793601
theorem B50416775 : Blo 1194414 50416775 := bstep (se 1 (by rfl) ⟨37812581, by rfl⟩ : syracuseStep 50416775 = 75625163) B75625163
theorem B6049079 : Blo 1194414 6049079 := bstep (se 1 (by rfl) ⟨4536809, by rfl⟩ : syracuseStep 6049079 = 9073619) B9073619
theorem B4541777 : Blo 1194414 4541777 := bstep (se 2 (by rfl) ⟨1703166, by rfl⟩ : syracuseStep 4541777 = 3406333) B3406333
theorem B2690387 : Blo 1194414 2690387 := bstep (se 1 (by rfl) ⟨2017790, by rfl⟩ : syracuseStep 2690387 = 4035581) B4035581
theorem B186224021 : Blo 1194414 186224021 := bstep (se 6 (by rfl) ⟨4364625, by rfl⟩ : syracuseStep 186224021 = 8729251) B8729251
theorem B29872799 : Blo 1194414 29872799 := bstep (se 1 (by rfl) ⟨22404599, by rfl⟩ : syracuseStep 29872799 = 44809199) B44809199
theorem B34943881 : Blo 1194414 34943881 := bstep (se 2 (by rfl) ⟨13103955, by rfl⟩ : syracuseStep 34943881 = 26207911) B26207911
theorem B1791911 : Blo 1194414 1791911 := bstep (se 1 (by rfl) ⟨1343933, by rfl⟩ : syracuseStep 1791911 = 2687867) B2687867
theorem B1792175 : Blo 1194414 1792175 := bstep (se 1 (by rfl) ⟨1344131, by rfl⟩ : syracuseStep 1792175 = 2688263) B2688263
theorem B26188231 : Blo 1194414 26188231 := bstep (se 1 (by rfl) ⟨19641173, by rfl⟩ : syracuseStep 26188231 = 39282347) B39282347
theorem B1194651 : Blo 1194414 1194651 := bstep (se 1 (by rfl) ⟨895988, by rfl⟩ : syracuseStep 1194651 = 1791977) B1791977
theorem B1794047 : Blo 1194414 1794047 := bstep (se 1 (by rfl) ⟨1345535, by rfl⟩ : syracuseStep 1794047 = 2691071) B2691071
theorem B1195167 : Blo 1194414 1195167 := bstep (se 1 (by rfl) ⟨896375, by rfl⟩ : syracuseStep 1195167 = 1792751) B1792751
theorem B5528827 : Blo 1194414 5528827 := bstep (se 1 (by rfl) ⟨4146620, by rfl⟩ : syracuseStep 5528827 = 8293241) B8293241
theorem B10354301 : Blo 1194414 10354301 := bstep (se 3 (by rfl) ⟨1941431, by rfl⟩ : syracuseStep 10354301 = 3882863) B3882863
theorem B17243927 : Blo 1194414 17243927 := bstep (se 1 (by rfl) ⟨12932945, by rfl⟩ : syracuseStep 17243927 = 25865891) B25865891
theorem B1195803 : Blo 1194414 1195803 := bstep (se 1 (by rfl) ⟨896852, by rfl⟩ : syracuseStep 1195803 = 1793705) B1793705
theorem B6897487 : Blo 1194414 6897487 := bstep (se 1 (by rfl) ⟨5173115, by rfl⟩ : syracuseStep 6897487 = 10346231) B10346231
theorem B10215341 : Blo 1194414 10215341 := bstep (se 3 (by rfl) ⟨1915376, by rfl⟩ : syracuseStep 10215341 = 3830753) B3830753
theorem B14549327 : Blo 1194414 14549327 := bstep (se 1 (by rfl) ⟨10911995, by rfl⟩ : syracuseStep 14549327 = 21823991) B21823991
theorem B19915199 : Blo 1194414 19915199 := bstep (se 1 (by rfl) ⟨14936399, by rfl⟩ : syracuseStep 19915199 = 29872799) B29872799
theorem B2687543 : Blo 1194414 2687543 := bstep (se 1 (by rfl) ⟨2015657, by rfl⟩ : syracuseStep 2687543 = 4031315) B4031315
theorem B1344379 : Blo 1194414 1344379 := bstep (se 1 (by rfl) ⟨1008284, by rfl⟩ : syracuseStep 1344379 = 2016569) B2016569
theorem B34440329 : Blo 1194414 34440329 := bstep (se 2 (by rfl) ⟨12915123, by rfl⟩ : syracuseStep 34440329 = 25830247) B25830247
theorem B1344667 : Blo 1194414 1344667 := bstep (se 1 (by rfl) ⟨1008500, by rfl⟩ : syracuseStep 1344667 = 2017001) B2017001
theorem B16352711 : Blo 1194414 16352711 := bstep (se 1 (by rfl) ⟨12264533, by rfl⟩ : syracuseStep 16352711 = 24529067) B24529067
theorem B4032233 : Blo 1194414 4032233 := bstep (se 2 (by rfl) ⟨1512087, by rfl⟩ : syracuseStep 4032233 = 3024175) B3024175
theorem B4032719 : Blo 1194414 4032719 := bstep (se 1 (by rfl) ⟨3024539, by rfl⟩ : syracuseStep 4032719 = 6049079) B6049079
theorem B11495951 : Blo 1194414 11495951 := bstep (se 1 (by rfl) ⟨8621963, by rfl⟩ : syracuseStep 11495951 = 17243927) B17243927
theorem B6810227 : Blo 1194414 6810227 := bstep (se 1 (by rfl) ⟨5107670, by rfl⟩ : syracuseStep 6810227 = 10215341) B10215341
theorem B3828703 : Blo 1194414 3828703 := bstep (se 1 (by rfl) ⟨2871527, by rfl⟩ : syracuseStep 3828703 = 5743055) B5743055
theorem B34917641 : Blo 1194414 34917641 := bstep (se 2 (by rfl) ⟨13094115, by rfl⟩ : syracuseStep 34917641 = 26188231) B26188231
theorem B20426579 : Blo 1194414 20426579 := bstep (se 1 (by rfl) ⟨15319934, by rfl⟩ : syracuseStep 20426579 = 30639869) B30639869
theorem B46591841 : Blo 1194414 46591841 := bstep (se 2 (by rfl) ⟨17471940, by rfl⟩ : syracuseStep 46591841 = 34943881) B34943881
theorem B3403883 : Blo 1194414 3403883 := bstep (se 1 (by rfl) ⟨2552912, by rfl⟩ : syracuseStep 3403883 = 5105825) B5105825
theorem B14528737 : Blo 1194414 14528737 := bstep (se 2 (by rfl) ⟨5448276, by rfl⟩ : syracuseStep 14528737 = 10896553) B10896553
theorem B3027851 : Blo 1194414 3027851 := bstep (se 1 (by rfl) ⟨2270888, by rfl⟩ : syracuseStep 3027851 = 4541777) B4541777
theorem B6902867 : Blo 1194414 6902867 := bstep (se 1 (by rfl) ⟨5177150, by rfl⟩ : syracuseStep 6902867 = 10354301) B10354301
theorem B9196649 : Blo 1194414 9196649 := bstep (se 2 (by rfl) ⟨3448743, by rfl⟩ : syracuseStep 9196649 = 6897487) B6897487
theorem B1194607 : Blo 1194414 1194607 := bstep (se 1 (by rfl) ⟨895955, by rfl⟩ : syracuseStep 1194607 = 1791911) B1791911
theorem B1792763 : Blo 1194414 1792763 := bstep (se 1 (by rfl) ⟨1344572, by rfl⟩ : syracuseStep 1792763 = 2689145) B2689145
theorem B1194783 : Blo 1194414 1194783 := bstep (se 1 (by rfl) ⟨896087, by rfl⟩ : syracuseStep 1194783 = 1792175) B1792175
theorem B7371769 : Blo 1194414 7371769 := bstep (se 2 (by rfl) ⟨2764413, by rfl⟩ : syracuseStep 7371769 = 5528827) B5528827
theorem B33611183 : Blo 1194414 33611183 := bstep (se 1 (by rfl) ⟨25208387, by rfl⟩ : syracuseStep 33611183 = 50416775) B50416775
theorem B1793591 : Blo 1194414 1793591 := bstep (se 1 (by rfl) ⟨1345193, by rfl⟩ : syracuseStep 1793591 = 2690387) B2690387
theorem B124149347 : Blo 1194414 124149347 := bstep (se 1 (by rfl) ⟨93112010, by rfl⟩ : syracuseStep 124149347 = 186224021) B186224021
theorem B1196031 : Blo 1194414 1196031 := bstep (se 1 (by rfl) ⟨897023, by rfl⟩ : syracuseStep 1196031 = 1794047) B1794047
theorem B18407645 : Blo 1194414 18407645 := bstep (se 3 (by rfl) ⟨3451433, by rfl⟩ : syracuseStep 18407645 = 6902867) B6902867
theorem B9699551 : Blo 1194414 9699551 := bstep (se 1 (by rfl) ⟨7274663, by rfl⟩ : syracuseStep 9699551 = 14549327) B14549327
theorem B9077021 : Blo 1194414 9077021 := bstep (se 3 (by rfl) ⟨1701941, by rfl⟩ : syracuseStep 9077021 = 3403883) B3403883
theorem B2688155 : Blo 1194414 2688155 := bstep (se 1 (by rfl) ⟨2016116, by rfl⟩ : syracuseStep 2688155 = 4032233) B4032233
theorem B5104937 : Blo 1194414 5104937 := bstep (se 2 (by rfl) ⟨1914351, by rfl⟩ : syracuseStep 5104937 = 3828703) B3828703
theorem B2688479 : Blo 1194414 2688479 := bstep (se 1 (by rfl) ⟨2016359, by rfl⟩ : syracuseStep 2688479 = 4032719) B4032719
theorem B4540151 : Blo 1194414 4540151 := bstep (se 1 (by rfl) ⟨3405113, by rfl⟩ : syracuseStep 4540151 = 6810227) B6810227
theorem B22407455 : Blo 1194414 22407455 := bstep (se 1 (by rfl) ⟨16805591, by rfl⟩ : syracuseStep 22407455 = 33611183) B33611183
theorem B82766231 : Blo 1194414 82766231 := bstep (se 1 (by rfl) ⟨62074673, by rfl⟩ : syracuseStep 82766231 = 124149347) B124149347
theorem B13617719 : Blo 1194414 13617719 := bstep (se 1 (by rfl) ⟨10213289, by rfl⟩ : syracuseStep 13617719 = 20426579) B20426579
theorem B2018567 : Blo 1194414 2018567 := bstep (se 1 (by rfl) ⟨1513925, by rfl⟩ : syracuseStep 2018567 = 3027851) B3027851
theorem B6131099 : Blo 1194414 6131099 := bstep (se 1 (by rfl) ⟨4598324, by rfl⟩ : syracuseStep 6131099 = 9196649) B9196649
theorem B7663967 : Blo 1194414 7663967 := bstep (se 1 (by rfl) ⟨5747975, by rfl⟩ : syracuseStep 7663967 = 11495951) B11495951
theorem B23278427 : Blo 1194414 23278427 := bstep (se 1 (by rfl) ⟨17458820, by rfl⟩ : syracuseStep 23278427 = 34917641) B34917641
theorem B31061227 : Blo 1194414 31061227 := bstep (se 1 (by rfl) ⟨23295920, by rfl⟩ : syracuseStep 31061227 = 46591841) B46591841
theorem B13276799 : Blo 1194414 13276799 := bstep (se 1 (by rfl) ⟨9957599, by rfl⟩ : syracuseStep 13276799 = 19915199) B19915199
theorem B19371649 : Blo 1194414 19371649 := bstep (se 2 (by rfl) ⟨7264368, by rfl⟩ : syracuseStep 19371649 = 14528737) B14528737
theorem B1791695 : Blo 1194414 1791695 := bstep (se 1 (by rfl) ⟨1343771, by rfl⟩ : syracuseStep 1791695 = 2687543) B2687543
theorem B22960219 : Blo 1194414 22960219 := bstep (se 1 (by rfl) ⟨17220164, by rfl⟩ : syracuseStep 22960219 = 34440329) B34440329
theorem B10901807 : Blo 1194414 10901807 := bstep (se 1 (by rfl) ⟨8176355, by rfl⟩ : syracuseStep 10901807 = 16352711) B16352711
theorem B1792505 : Blo 1194414 1792505 := bstep (se 2 (by rfl) ⟨672189, by rfl⟩ : syracuseStep 1792505 = 1344379) B1344379
theorem B9829025 : Blo 1194414 9829025 := bstep (se 2 (by rfl) ⟨3685884, by rfl⟩ : syracuseStep 9829025 = 7371769) B7371769
theorem B1792889 : Blo 1194414 1792889 := bstep (se 2 (by rfl) ⟨672333, by rfl⟩ : syracuseStep 1792889 = 1344667) B1344667
theorem B1195175 : Blo 1194414 1195175 := bstep (se 1 (by rfl) ⟨896381, by rfl⟩ : syracuseStep 1195175 = 1792763) B1792763
theorem B1195727 : Blo 1194414 1195727 := bstep (se 1 (by rfl) ⟨896795, by rfl⟩ : syracuseStep 1195727 = 1793591) B1793591
theorem B30613625 : Blo 1194414 30613625 := bstep (se 2 (by rfl) ⟨11480109, by rfl⟩ : syracuseStep 30613625 = 22960219) B22960219
theorem B12271763 : Blo 1194414 12271763 := bstep (se 1 (by rfl) ⟨9203822, by rfl⟩ : syracuseStep 12271763 = 18407645) B18407645
theorem B59753213 : Blo 1194414 59753213 := bstep (se 3 (by rfl) ⟨11203727, by rfl⟩ : syracuseStep 59753213 = 22407455) B22407455
theorem B7267871 : Blo 1194414 7267871 := bstep (se 1 (by rfl) ⟨5450903, by rfl⟩ : syracuseStep 7267871 = 10901807) B10901807
theorem B9078479 : Blo 1194414 9078479 := bstep (se 1 (by rfl) ⟨6808859, by rfl⟩ : syracuseStep 9078479 = 13617719) B13617719
theorem B1345711 : Blo 1194414 1345711 := bstep (se 1 (by rfl) ⟨1009283, by rfl⟩ : syracuseStep 1345711 = 2018567) B2018567
theorem B6466367 : Blo 1194414 6466367 := bstep (se 1 (by rfl) ⟨4849775, by rfl⟩ : syracuseStep 6466367 = 9699551) B9699551
theorem B15518951 : Blo 1194414 15518951 := bstep (se 1 (by rfl) ⟨11639213, by rfl⟩ : syracuseStep 15518951 = 23278427) B23278427
theorem B3403291 : Blo 1194414 3403291 := bstep (se 1 (by rfl) ⟨2552468, by rfl⟩ : syracuseStep 3403291 = 5104937) B5104937
theorem B8851199 : Blo 1194414 8851199 := bstep (se 1 (by rfl) ⟨6638399, by rfl⟩ : syracuseStep 8851199 = 13276799) B13276799
theorem B3026767 : Blo 1194414 3026767 := bstep (se 1 (by rfl) ⟨2270075, by rfl⟩ : syracuseStep 3026767 = 4540151) B4540151
theorem B55177487 : Blo 1194414 55177487 := bstep (se 1 (by rfl) ⟨41383115, by rfl⟩ : syracuseStep 55177487 = 82766231) B82766231
theorem B41414969 : Blo 1194414 41414969 := bstep (se 2 (by rfl) ⟨15530613, by rfl⟩ : syracuseStep 41414969 = 31061227) B31061227
theorem B6051347 : Blo 1194414 6051347 := bstep (se 1 (by rfl) ⟨4538510, by rfl⟩ : syracuseStep 6051347 = 9077021) B9077021
theorem B5109311 : Blo 1194414 5109311 := bstep (se 1 (by rfl) ⟨3831983, by rfl⟩ : syracuseStep 5109311 = 7663967) B7663967
theorem B1792103 : Blo 1194414 1792103 := bstep (se 1 (by rfl) ⟨1344077, by rfl⟩ : syracuseStep 1792103 = 2688155) B2688155
theorem B1792319 : Blo 1194414 1792319 := bstep (se 1 (by rfl) ⟨1344239, by rfl⟩ : syracuseStep 1792319 = 2688479) B2688479
theorem B16349597 : Blo 1194414 16349597 := bstep (se 3 (by rfl) ⟨3065549, by rfl⟩ : syracuseStep 16349597 = 6131099) B6131099
theorem B1194463 : Blo 1194414 1194463 := bstep (se 1 (by rfl) ⟨895847, by rfl⟩ : syracuseStep 1194463 = 1791695) B1791695
theorem B1195003 : Blo 1194414 1195003 := bstep (se 1 (by rfl) ⟨896252, by rfl⟩ : syracuseStep 1195003 = 1792505) B1792505
theorem B6552683 : Blo 1194414 6552683 := bstep (se 1 (by rfl) ⟨4914512, by rfl⟩ : syracuseStep 6552683 = 9829025) B9829025
theorem B1195259 : Blo 1194414 1195259 := bstep (se 1 (by rfl) ⟨896444, by rfl⟩ : syracuseStep 1195259 = 1792889) B1792889
theorem B25828865 : Blo 1194414 25828865 := bstep (se 2 (by rfl) ⟨9685824, by rfl⟩ : syracuseStep 25828865 = 19371649) B19371649
theorem B1794281 : Blo 1194414 1794281 := bstep (se 2 (by rfl) ⟨672855, by rfl⟩ : syracuseStep 1794281 = 1345711) B1345711
theorem B4310911 : Blo 1194414 4310911 := bstep (se 1 (by rfl) ⟨3233183, by rfl⟩ : syracuseStep 4310911 = 6466367) B6466367
theorem B4368455 : Blo 1194414 4368455 := bstep (se 1 (by rfl) ⟨3276341, by rfl⟩ : syracuseStep 4368455 = 6552683) B6552683
theorem B20409083 : Blo 1194414 20409083 := bstep (se 1 (by rfl) ⟨15306812, by rfl⟩ : syracuseStep 20409083 = 30613625) B30613625
theorem B36784991 : Blo 1194414 36784991 := bstep (se 1 (by rfl) ⟨27588743, by rfl⟩ : syracuseStep 36784991 = 55177487) B55177487
theorem B27609979 : Blo 1194414 27609979 := bstep (se 1 (by rfl) ⟨20707484, by rfl⟩ : syracuseStep 27609979 = 41414969) B41414969
theorem B4034231 : Blo 1194414 4034231 := bstep (se 1 (by rfl) ⟨3025673, by rfl⟩ : syracuseStep 4034231 = 6051347) B6051347
theorem B10899731 : Blo 1194414 10899731 := bstep (se 1 (by rfl) ⟨8174798, by rfl⟩ : syracuseStep 10899731 = 16349597) B16349597
theorem B4035689 : Blo 1194414 4035689 := bstep (se 2 (by rfl) ⟨1513383, by rfl⟩ : syracuseStep 4035689 = 3026767) B3026767
theorem B8181175 : Blo 1194414 8181175 := bstep (se 1 (by rfl) ⟨6135881, by rfl⟩ : syracuseStep 8181175 = 12271763) B12271763
theorem B39835475 : Blo 1194414 39835475 := bstep (se 1 (by rfl) ⟨29876606, by rfl⟩ : syracuseStep 39835475 = 59753213) B59753213
theorem B3406207 : Blo 1194414 3406207 := bstep (se 1 (by rfl) ⟨2554655, by rfl⟩ : syracuseStep 3406207 = 5109311) B5109311
theorem B6052319 : Blo 1194414 6052319 := bstep (se 1 (by rfl) ⟨4539239, by rfl⟩ : syracuseStep 6052319 = 9078479) B9078479
theorem B1194735 : Blo 1194414 1194735 := bstep (se 1 (by rfl) ⟨896051, by rfl⟩ : syracuseStep 1194735 = 1792103) B1792103
theorem B19380989 : Blo 1194414 19380989 := bstep (se 3 (by rfl) ⟨3633935, by rfl⟩ : syracuseStep 19380989 = 7267871) B7267871
theorem B1194879 : Blo 1194414 1194879 := bstep (se 1 (by rfl) ⟨896159, by rfl⟩ : syracuseStep 1194879 = 1792319) B1792319
theorem B4537721 : Blo 1194414 4537721 := bstep (se 2 (by rfl) ⟨1701645, by rfl⟩ : syracuseStep 4537721 = 3403291) B3403291
theorem B10345967 : Blo 1194414 10345967 := bstep (se 1 (by rfl) ⟨7759475, by rfl⟩ : syracuseStep 10345967 = 15518951) B15518951
theorem B17219243 : Blo 1194414 17219243 := bstep (se 1 (by rfl) ⟨12914432, by rfl⟩ : syracuseStep 17219243 = 25828865) B25828865
theorem B94412789 : Blo 1194414 94412789 := bstep (se 5 (by rfl) ⟨4425599, by rfl⟩ : syracuseStep 94412789 = 8851199) B8851199
theorem B1196187 : Blo 1194414 1196187 := bstep (se 1 (by rfl) ⟨897140, by rfl⟩ : syracuseStep 1196187 = 1794281) B1794281
theorem B29065949 : Blo 1194414 29065949 := bstep (se 3 (by rfl) ⟨5449865, by rfl⟩ : syracuseStep 29065949 = 10899731) B10899731
theorem B3025147 : Blo 1194414 3025147 := bstep (se 1 (by rfl) ⟨2268860, by rfl⟩ : syracuseStep 3025147 = 4537721) B4537721
theorem B11479495 : Blo 1194414 11479495 := bstep (se 1 (by rfl) ⟨8609621, by rfl⟩ : syracuseStep 11479495 = 17219243) B17219243
theorem B2689487 : Blo 1194414 2689487 := bstep (se 1 (by rfl) ⟨2017115, by rfl⟩ : syracuseStep 2689487 = 4034231) B4034231
theorem B62941859 : Blo 1194414 62941859 := bstep (se 1 (by rfl) ⟨47206394, by rfl⟩ : syracuseStep 62941859 = 94412789) B94412789
theorem B4541609 : Blo 1194414 4541609 := bstep (se 2 (by rfl) ⟨1703103, by rfl⟩ : syracuseStep 4541609 = 3406207) B3406207
theorem B2690459 : Blo 1194414 2690459 := bstep (se 1 (by rfl) ⟨2017844, by rfl⟩ : syracuseStep 2690459 = 4035689) B4035689
theorem B2912303 : Blo 1194414 2912303 := bstep (se 1 (by rfl) ⟨2184227, by rfl⟩ : syracuseStep 2912303 = 4368455) B4368455
theorem B4034879 : Blo 1194414 4034879 := bstep (se 1 (by rfl) ⟨3026159, by rfl⟩ : syracuseStep 4034879 = 6052319) B6052319
theorem B24523327 : Blo 1194414 24523327 := bstep (se 1 (by rfl) ⟨18392495, by rfl⟩ : syracuseStep 24523327 = 36784991) B36784991
theorem B10908233 : Blo 1194414 10908233 := bstep (se 2 (by rfl) ⟨4090587, by rfl⟩ : syracuseStep 10908233 = 8181175) B8181175
theorem B5747881 : Blo 1194414 5747881 := bstep (se 2 (by rfl) ⟨2155455, by rfl⟩ : syracuseStep 5747881 = 4310911) B4310911
theorem B36813305 : Blo 1194414 36813305 := bstep (se 2 (by rfl) ⟨13804989, by rfl⟩ : syracuseStep 36813305 = 27609979) B27609979
theorem B26556983 : Blo 1194414 26556983 := bstep (se 1 (by rfl) ⟨19917737, by rfl⟩ : syracuseStep 26556983 = 39835475) B39835475
theorem B13606055 : Blo 1194414 13606055 := bstep (se 1 (by rfl) ⟨10204541, by rfl⟩ : syracuseStep 13606055 = 20409083) B20409083
theorem B51682637 : Blo 1194414 51682637 := bstep (se 3 (by rfl) ⟨9690494, by rfl⟩ : syracuseStep 51682637 = 19380989) B19380989
theorem B6897311 : Blo 1194414 6897311 := bstep (se 1 (by rfl) ⟨5172983, by rfl⟩ : syracuseStep 6897311 = 10345967) B10345967
theorem B1941535 : Blo 1194414 1941535 := bstep (se 1 (by rfl) ⟨1456151, by rfl⟩ : syracuseStep 1941535 = 2912303) B2912303
theorem B17704655 : Blo 1194414 17704655 := bstep (se 1 (by rfl) ⟨13278491, by rfl⟩ : syracuseStep 17704655 = 26556983) B26556983
theorem B41961239 : Blo 1194414 41961239 := bstep (se 1 (by rfl) ⟨31470929, by rfl⟩ : syracuseStep 41961239 = 62941859) B62941859
theorem B9070703 : Blo 1194414 9070703 := bstep (se 1 (by rfl) ⟨6803027, by rfl⟩ : syracuseStep 9070703 = 13606055) B13606055
theorem B4598207 : Blo 1194414 4598207 := bstep (se 1 (by rfl) ⟨3448655, by rfl⟩ : syracuseStep 4598207 = 6897311) B6897311
theorem B2689919 : Blo 1194414 2689919 := bstep (se 1 (by rfl) ⟨2017439, by rfl⟩ : syracuseStep 2689919 = 4034879) B4034879
theorem B4033529 : Blo 1194414 4033529 := bstep (se 2 (by rfl) ⟨1512573, by rfl⟩ : syracuseStep 4033529 = 3025147) B3025147
theorem B19377299 : Blo 1194414 19377299 := bstep (se 1 (by rfl) ⟨14532974, by rfl⟩ : syracuseStep 19377299 = 29065949) B29065949
theorem B15305993 : Blo 1194414 15305993 := bstep (se 2 (by rfl) ⟨5739747, by rfl⟩ : syracuseStep 15305993 = 11479495) B11479495
theorem B32697769 : Blo 1194414 32697769 := bstep (se 2 (by rfl) ⟨12261663, by rfl⟩ : syracuseStep 32697769 = 24523327) B24523327
theorem B7663841 : Blo 1194414 7663841 := bstep (se 2 (by rfl) ⟨2873940, by rfl⟩ : syracuseStep 7663841 = 5747881) B5747881
theorem B3027739 : Blo 1194414 3027739 := bstep (se 1 (by rfl) ⟨2270804, by rfl⟩ : syracuseStep 3027739 = 4541609) B4541609
theorem B7272155 : Blo 1194414 7272155 := bstep (se 1 (by rfl) ⟨5454116, by rfl⟩ : syracuseStep 7272155 = 10908233) B10908233
theorem B1792991 : Blo 1194414 1792991 := bstep (se 1 (by rfl) ⟨1344743, by rfl⟩ : syracuseStep 1792991 = 2689487) B2689487
theorem B24542203 : Blo 1194414 24542203 := bstep (se 1 (by rfl) ⟨18406652, by rfl⟩ : syracuseStep 24542203 = 36813305) B36813305
theorem B34455091 : Blo 1194414 34455091 := bstep (se 1 (by rfl) ⟨25841318, by rfl⟩ : syracuseStep 34455091 = 51682637) B51682637
theorem B1793639 : Blo 1194414 1793639 := bstep (se 1 (by rfl) ⟨1345229, by rfl⟩ : syracuseStep 1793639 = 2690459) B2690459
theorem B10354853 : Blo 1194414 10354853 := bstep (se 4 (by rfl) ⟨970767, by rfl⟩ : syracuseStep 10354853 = 1941535) B1941535
theorem B6047135 : Blo 1194414 6047135 := bstep (se 1 (by rfl) ⟨4535351, by rfl⟩ : syracuseStep 6047135 = 9070703) B9070703
theorem B3065471 : Blo 1194414 3065471 := bstep (se 1 (by rfl) ⟨2299103, by rfl⟩ : syracuseStep 3065471 = 4598207) B4598207
theorem B2689019 : Blo 1194414 2689019 := bstep (se 1 (by rfl) ⟨2016764, by rfl⟩ : syracuseStep 2689019 = 4033529) B4033529
theorem B32722937 : Blo 1194414 32722937 := bstep (se 2 (by rfl) ⟨12271101, by rfl⟩ : syracuseStep 32722937 = 24542203) B24542203
theorem B10203995 : Blo 1194414 10203995 := bstep (se 1 (by rfl) ⟨7652996, by rfl⟩ : syracuseStep 10203995 = 15305993) B15305993
theorem B5109227 : Blo 1194414 5109227 := bstep (se 1 (by rfl) ⟨3831920, by rfl⟩ : syracuseStep 5109227 = 7663841) B7663841
theorem B4036985 : Blo 1194414 4036985 := bstep (se 2 (by rfl) ⟨1513869, by rfl⟩ : syracuseStep 4036985 = 3027739) B3027739
theorem B11803103 : Blo 1194414 11803103 := bstep (se 1 (by rfl) ⟨8852327, by rfl⟩ : syracuseStep 11803103 = 17704655) B17704655
theorem B4848103 : Blo 1194414 4848103 := bstep (se 1 (by rfl) ⟨3636077, by rfl⟩ : syracuseStep 4848103 = 7272155) B7272155
theorem B27974159 : Blo 1194414 27974159 := bstep (se 1 (by rfl) ⟨20980619, by rfl⟩ : syracuseStep 27974159 = 41961239) B41961239
theorem B43597025 : Blo 1194414 43597025 := bstep (se 2 (by rfl) ⟨16348884, by rfl⟩ : syracuseStep 43597025 = 32697769) B32697769
theorem B1793279 : Blo 1194414 1793279 := bstep (se 1 (by rfl) ⟨1344959, by rfl⟩ : syracuseStep 1793279 = 2689919) B2689919
theorem B1195327 : Blo 1194414 1195327 := bstep (se 1 (by rfl) ⟨896495, by rfl⟩ : syracuseStep 1195327 = 1792991) B1792991
theorem B45940121 : Blo 1194414 45940121 := bstep (se 2 (by rfl) ⟨17227545, by rfl⟩ : syracuseStep 45940121 = 34455091) B34455091
theorem B12918199 : Blo 1194414 12918199 := bstep (se 1 (by rfl) ⟨9688649, by rfl⟩ : syracuseStep 12918199 = 19377299) B19377299
theorem B1195759 : Blo 1194414 1195759 := bstep (se 1 (by rfl) ⟨896819, by rfl⟩ : syracuseStep 1195759 = 1793639) B1793639
theorem B6464137 : Blo 1194414 6464137 := bstep (se 2 (by rfl) ⟨2424051, by rfl⟩ : syracuseStep 6464137 = 4848103) B4848103
theorem B4031423 : Blo 1194414 4031423 := bstep (se 1 (by rfl) ⟨3023567, by rfl⟩ : syracuseStep 4031423 = 6047135) B6047135
theorem B6802663 : Blo 1194414 6802663 := bstep (se 1 (by rfl) ⟨5101997, by rfl⟩ : syracuseStep 6802663 = 10203995) B10203995
theorem B2043647 : Blo 1194414 2043647 := bstep (se 1 (by rfl) ⟨1532735, by rfl⟩ : syracuseStep 2043647 = 3065471) B3065471
theorem B2691323 : Blo 1194414 2691323 := bstep (se 1 (by rfl) ⟨2018492, by rfl⟩ : syracuseStep 2691323 = 4036985) B4036985
theorem B7868735 : Blo 1194414 7868735 := bstep (se 1 (by rfl) ⟨5901551, by rfl⟩ : syracuseStep 7868735 = 11803103) B11803103
theorem B18649439 : Blo 1194414 18649439 := bstep (se 1 (by rfl) ⟨13987079, by rfl⟩ : syracuseStep 18649439 = 27974159) B27974159
theorem B17224265 : Blo 1194414 17224265 := bstep (se 2 (by rfl) ⟨6459099, by rfl⟩ : syracuseStep 17224265 = 12918199) B12918199
theorem B30626747 : Blo 1194414 30626747 := bstep (se 1 (by rfl) ⟨22970060, by rfl⟩ : syracuseStep 30626747 = 45940121) B45940121
theorem B6903235 : Blo 1194414 6903235 := bstep (se 1 (by rfl) ⟨5177426, by rfl⟩ : syracuseStep 6903235 = 10354853) B10354853
theorem B3406151 : Blo 1194414 3406151 := bstep (se 1 (by rfl) ⟨2554613, by rfl⟩ : syracuseStep 3406151 = 5109227) B5109227
theorem B1792679 : Blo 1194414 1792679 := bstep (se 1 (by rfl) ⟨1344509, by rfl⟩ : syracuseStep 1792679 = 2689019) B2689019
theorem B29064683 : Blo 1194414 29064683 := bstep (se 1 (by rfl) ⟨21798512, by rfl⟩ : syracuseStep 29064683 = 43597025) B43597025
theorem B1195519 : Blo 1194414 1195519 := bstep (se 1 (by rfl) ⟨896639, by rfl⟩ : syracuseStep 1195519 = 1793279) B1793279
theorem B21815291 : Blo 1194414 21815291 := bstep (se 1 (by rfl) ⟨16361468, by rfl⟩ : syracuseStep 21815291 = 32722937) B32722937
theorem B1794215 : Blo 1194414 1794215 := bstep (se 1 (by rfl) ⟨1345661, by rfl⟩ : syracuseStep 1794215 = 2691323) B2691323
theorem B2687615 : Blo 1194414 2687615 := bstep (se 1 (by rfl) ⟨2015711, by rfl⟩ : syracuseStep 2687615 = 4031423) B4031423
theorem B8618849 : Blo 1194414 8618849 := bstep (se 2 (by rfl) ⟨3232068, by rfl⟩ : syracuseStep 8618849 = 6464137) B6464137
theorem B2270767 : Blo 1194414 2270767 := bstep (se 1 (by rfl) ⟨1703075, by rfl⟩ : syracuseStep 2270767 = 3406151) B3406151
theorem B9070217 : Blo 1194414 9070217 := bstep (se 2 (by rfl) ⟨3401331, by rfl⟩ : syracuseStep 9070217 = 6802663) B6802663
theorem B19376455 : Blo 1194414 19376455 := bstep (se 1 (by rfl) ⟨14532341, by rfl⟩ : syracuseStep 19376455 = 29064683) B29064683
theorem B1362431 : Blo 1194414 1362431 := bstep (se 1 (by rfl) ⟨1021823, by rfl⟩ : syracuseStep 1362431 = 2043647) B2043647
theorem B58174109 : Blo 1194414 58174109 := bstep (se 3 (by rfl) ⟨10907645, by rfl⟩ : syracuseStep 58174109 = 21815291) B21815291
theorem B5245823 : Blo 1194414 5245823 := bstep (se 1 (by rfl) ⟨3934367, by rfl⟩ : syracuseStep 5245823 = 7868735) B7868735
theorem B20417831 : Blo 1194414 20417831 := bstep (se 1 (by rfl) ⟨15313373, by rfl⟩ : syracuseStep 20417831 = 30626747) B30626747
theorem B9204313 : Blo 1194414 9204313 := bstep (se 2 (by rfl) ⟨3451617, by rfl⟩ : syracuseStep 9204313 = 6903235) B6903235
theorem B12432959 : Blo 1194414 12432959 := bstep (se 1 (by rfl) ⟨9324719, by rfl⟩ : syracuseStep 12432959 = 18649439) B18649439
theorem B11482843 : Blo 1194414 11482843 := bstep (se 1 (by rfl) ⟨8612132, by rfl⟩ : syracuseStep 11482843 = 17224265) B17224265
theorem B1195119 : Blo 1194414 1195119 := bstep (se 1 (by rfl) ⟨896339, by rfl⟩ : syracuseStep 1195119 = 1792679) B1792679
theorem B1196143 : Blo 1194414 1196143 := bstep (se 1 (by rfl) ⟨897107, by rfl⟩ : syracuseStep 1196143 = 1794215) B1794215
theorem B12272417 : Blo 1194414 12272417 := bstep (se 2 (by rfl) ⟨4602156, by rfl⟩ : syracuseStep 12272417 = 9204313) B9204313
theorem B6046811 : Blo 1194414 6046811 := bstep (se 1 (by rfl) ⟨4535108, by rfl⟩ : syracuseStep 6046811 = 9070217) B9070217
theorem B38782739 : Blo 1194414 38782739 := bstep (se 1 (by rfl) ⟨29087054, by rfl⟩ : syracuseStep 38782739 = 58174109) B58174109
theorem B5745899 : Blo 1194414 5745899 := bstep (se 1 (by rfl) ⟨4309424, by rfl⟩ : syracuseStep 5745899 = 8618849) B8618849
theorem B3633149 : Blo 1194414 3633149 := bstep (se 3 (by rfl) ⟨681215, by rfl⟩ : syracuseStep 3633149 = 1362431) B1362431
theorem B3027689 : Blo 1194414 3027689 := bstep (se 2 (by rfl) ⟨1135383, by rfl⟩ : syracuseStep 3027689 = 2270767) B2270767
theorem B13611887 : Blo 1194414 13611887 := bstep (se 1 (by rfl) ⟨10208915, by rfl⟩ : syracuseStep 13611887 = 20417831) B20417831
theorem B1791743 : Blo 1194414 1791743 := bstep (se 1 (by rfl) ⟨1343807, by rfl⟩ : syracuseStep 1791743 = 2687615) B2687615
theorem B25835273 : Blo 1194414 25835273 := bstep (se 2 (by rfl) ⟨9688227, by rfl⟩ : syracuseStep 25835273 = 19376455) B19376455
theorem B8288639 : Blo 1194414 8288639 := bstep (se 1 (by rfl) ⟨6216479, by rfl⟩ : syracuseStep 8288639 = 12432959) B12432959
theorem B3497215 : Blo 1194414 3497215 := bstep (se 1 (by rfl) ⟨2622911, by rfl⟩ : syracuseStep 3497215 = 5245823) B5245823
theorem B15310457 : Blo 1194414 15310457 := bstep (se 2 (by rfl) ⟨5741421, by rfl⟩ : syracuseStep 15310457 = 11482843) B11482843
theorem B4031207 : Blo 1194414 4031207 := bstep (se 1 (by rfl) ⟨3023405, by rfl⟩ : syracuseStep 4031207 = 6046811) B6046811
theorem B25855159 : Blo 1194414 25855159 := bstep (se 1 (by rfl) ⟨19391369, by rfl⟩ : syracuseStep 25855159 = 38782739) B38782739
theorem B4662953 : Blo 1194414 4662953 := bstep (se 2 (by rfl) ⟨1748607, by rfl⟩ : syracuseStep 4662953 = 3497215) B3497215
theorem B2018459 : Blo 1194414 2018459 := bstep (se 1 (by rfl) ⟨1513844, by rfl⟩ : syracuseStep 2018459 = 3027689) B3027689
theorem B17223515 : Blo 1194414 17223515 := bstep (se 1 (by rfl) ⟨12917636, by rfl⟩ : syracuseStep 17223515 = 25835273) B25835273
theorem B5525759 : Blo 1194414 5525759 := bstep (se 1 (by rfl) ⟨4144319, by rfl⟩ : syracuseStep 5525759 = 8288639) B8288639
theorem B3830599 : Blo 1194414 3830599 := bstep (se 1 (by rfl) ⟨2872949, by rfl⟩ : syracuseStep 3830599 = 5745899) B5745899
theorem B2422099 : Blo 1194414 2422099 := bstep (se 1 (by rfl) ⟨1816574, by rfl⟩ : syracuseStep 2422099 = 3633149) B3633149
theorem B8181611 : Blo 1194414 8181611 := bstep (se 1 (by rfl) ⟨6136208, by rfl⟩ : syracuseStep 8181611 = 12272417) B12272417
theorem B9074591 : Blo 1194414 9074591 := bstep (se 1 (by rfl) ⟨6805943, by rfl⟩ : syracuseStep 9074591 = 13611887) B13611887
theorem B1194495 : Blo 1194414 1194495 := bstep (se 1 (by rfl) ⟨895871, by rfl⟩ : syracuseStep 1194495 = 1791743) B1791743
theorem B10206971 : Blo 1194414 10206971 := bstep (se 1 (by rfl) ⟨7655228, by rfl⟩ : syracuseStep 10206971 = 15310457) B15310457
theorem B2687471 : Blo 1194414 2687471 := bstep (se 1 (by rfl) ⟨2015603, by rfl⟩ : syracuseStep 2687471 = 4031207) B4031207
theorem B34473545 : Blo 1194414 34473545 := bstep (se 2 (by rfl) ⟨12927579, by rfl⟩ : syracuseStep 34473545 = 25855159) B25855159
theorem B3229465 : Blo 1194414 3229465 := bstep (se 2 (by rfl) ⟨1211049, by rfl⟩ : syracuseStep 3229465 = 2422099) B2422099
theorem B1345639 : Blo 1194414 1345639 := bstep (se 1 (by rfl) ⟨1009229, by rfl⟩ : syracuseStep 1345639 = 2018459) B2018459
theorem B5107465 : Blo 1194414 5107465 := bstep (se 2 (by rfl) ⟨1915299, by rfl⟩ : syracuseStep 5107465 = 3830599) B3830599
theorem B3108635 : Blo 1194414 3108635 := bstep (se 1 (by rfl) ⟨2331476, by rfl⟩ : syracuseStep 3108635 = 4662953) B4662953
theorem B6049727 : Blo 1194414 6049727 := bstep (se 1 (by rfl) ⟨4537295, by rfl⟩ : syracuseStep 6049727 = 9074591) B9074591
theorem B6804647 : Blo 1194414 6804647 := bstep (se 1 (by rfl) ⟨5103485, by rfl⟩ : syracuseStep 6804647 = 10206971) B10206971
theorem B11482343 : Blo 1194414 11482343 := bstep (se 1 (by rfl) ⟨8611757, by rfl⟩ : syracuseStep 11482343 = 17223515) B17223515
theorem B3683839 : Blo 1194414 3683839 := bstep (se 1 (by rfl) ⟨2762879, by rfl⟩ : syracuseStep 3683839 = 5525759) B5525759
theorem B5454407 : Blo 1194414 5454407 := bstep (se 1 (by rfl) ⟨4090805, by rfl⟩ : syracuseStep 5454407 = 8181611) B8181611
theorem B1794185 : Blo 1194414 1794185 := bstep (se 2 (by rfl) ⟨672819, by rfl⟩ : syracuseStep 1794185 = 1345639) B1345639
theorem B6809953 : Blo 1194414 6809953 := bstep (se 2 (by rfl) ⟨2553732, by rfl⟩ : syracuseStep 6809953 = 5107465) B5107465
theorem B4033151 : Blo 1194414 4033151 := bstep (se 1 (by rfl) ⟨3024863, by rfl⟩ : syracuseStep 4033151 = 6049727) B6049727
theorem B7654895 : Blo 1194414 7654895 := bstep (se 1 (by rfl) ⟨5741171, by rfl⟩ : syracuseStep 7654895 = 11482343) B11482343
theorem B22982363 : Blo 1194414 22982363 := bstep (se 1 (by rfl) ⟨17236772, by rfl⟩ : syracuseStep 22982363 = 34473545) B34473545
theorem B4911785 : Blo 1194414 4911785 := bstep (se 2 (by rfl) ⟨1841919, by rfl⟩ : syracuseStep 4911785 = 3683839) B3683839
theorem B4305953 : Blo 1194414 4305953 := bstep (se 2 (by rfl) ⟨1614732, by rfl⟩ : syracuseStep 4305953 = 3229465) B3229465
theorem B1791647 : Blo 1194414 1791647 := bstep (se 1 (by rfl) ⟨1343735, by rfl⟩ : syracuseStep 1791647 = 2687471) B2687471
theorem B4536431 : Blo 1194414 4536431 := bstep (se 1 (by rfl) ⟨3402323, by rfl⟩ : syracuseStep 4536431 = 6804647) B6804647
theorem B3636271 : Blo 1194414 3636271 := bstep (se 1 (by rfl) ⟨2727203, by rfl⟩ : syracuseStep 3636271 = 5454407) B5454407
theorem B2072423 : Blo 1194414 2072423 := bstep (se 1 (by rfl) ⟨1554317, by rfl⟩ : syracuseStep 2072423 = 3108635) B3108635
theorem B1196123 : Blo 1194414 1196123 := bstep (se 1 (by rfl) ⟨897092, by rfl⟩ : syracuseStep 1196123 = 1794185) B1794185
theorem B3024287 : Blo 1194414 3024287 := bstep (se 1 (by rfl) ⟨2268215, by rfl⟩ : syracuseStep 3024287 = 4536431) B4536431
theorem B2688767 : Blo 1194414 2688767 := bstep (se 1 (by rfl) ⟨2016575, by rfl⟩ : syracuseStep 2688767 = 4033151) B4033151
theorem B15321575 : Blo 1194414 15321575 := bstep (se 1 (by rfl) ⟨11491181, by rfl⟩ : syracuseStep 15321575 = 22982363) B22982363
theorem B19393445 : Blo 1194414 19393445 := bstep (se 4 (by rfl) ⟨1818135, by rfl⟩ : syracuseStep 19393445 = 3636271) B3636271
theorem B9079937 : Blo 1194414 9079937 := bstep (se 2 (by rfl) ⟨3404976, by rfl⟩ : syracuseStep 9079937 = 6809953) B6809953
theorem B2870635 : Blo 1194414 2870635 := bstep (se 1 (by rfl) ⟨2152976, by rfl⟩ : syracuseStep 2870635 = 4305953) B4305953
theorem B5526461 : Blo 1194414 5526461 := bstep (se 3 (by rfl) ⟨1036211, by rfl⟩ : syracuseStep 5526461 = 2072423) B2072423
theorem B3274523 : Blo 1194414 3274523 := bstep (se 1 (by rfl) ⟨2455892, by rfl⟩ : syracuseStep 3274523 = 4911785) B4911785
theorem B1194431 : Blo 1194414 1194431 := bstep (se 1 (by rfl) ⟨895823, by rfl⟩ : syracuseStep 1194431 = 1791647) B1791647
theorem B5103263 : Blo 1194414 5103263 := bstep (se 1 (by rfl) ⟨3827447, by rfl⟩ : syracuseStep 5103263 = 7654895) B7654895
theorem B2016191 : Blo 1194414 2016191 := bstep (se 1 (by rfl) ⟨1512143, by rfl⟩ : syracuseStep 2016191 = 3024287) B3024287
theorem B3827513 : Blo 1194414 3827513 := bstep (se 2 (by rfl) ⟨1435317, by rfl⟩ : syracuseStep 3827513 = 2870635) B2870635
theorem B3402175 : Blo 1194414 3402175 := bstep (se 1 (by rfl) ⟨2551631, by rfl⟩ : syracuseStep 3402175 = 5103263) B5103263
theorem B2183015 : Blo 1194414 2183015 := bstep (se 1 (by rfl) ⟨1637261, by rfl⟩ : syracuseStep 2183015 = 3274523) B3274523
theorem B3684307 : Blo 1194414 3684307 := bstep (se 1 (by rfl) ⟨2763230, by rfl⟩ : syracuseStep 3684307 = 5526461) B5526461
theorem B1792511 : Blo 1194414 1792511 := bstep (se 1 (by rfl) ⟨1344383, by rfl⟩ : syracuseStep 1792511 = 2688767) B2688767
theorem B10214383 : Blo 1194414 10214383 := bstep (se 1 (by rfl) ⟨7660787, by rfl⟩ : syracuseStep 10214383 = 15321575) B15321575
theorem B6053291 : Blo 1194414 6053291 := bstep (se 1 (by rfl) ⟨4539968, by rfl⟩ : syracuseStep 6053291 = 9079937) B9079937
theorem B51715853 : Blo 1194414 51715853 := bstep (se 3 (by rfl) ⟨9696722, by rfl⟩ : syracuseStep 51715853 = 19393445) B19393445
theorem B1344127 : Blo 1194414 1344127 := bstep (se 1 (by rfl) ⟨1008095, by rfl⟩ : syracuseStep 1344127 = 2016191) B2016191
theorem B2551675 : Blo 1194414 2551675 := bstep (se 1 (by rfl) ⟨1913756, by rfl⟩ : syracuseStep 2551675 = 3827513) B3827513
theorem B13619177 : Blo 1194414 13619177 := bstep (se 2 (by rfl) ⟨5107191, by rfl⟩ : syracuseStep 13619177 = 10214383) B10214383
theorem B5821373 : Blo 1194414 5821373 := bstep (se 3 (by rfl) ⟨1091507, by rfl⟩ : syracuseStep 5821373 = 2183015) B2183015
theorem B4035527 : Blo 1194414 4035527 := bstep (se 1 (by rfl) ⟨3026645, by rfl⟩ : syracuseStep 4035527 = 6053291) B6053291
theorem B34477235 : Blo 1194414 34477235 := bstep (se 1 (by rfl) ⟨25857926, by rfl⟩ : syracuseStep 34477235 = 51715853) B51715853
theorem B4912409 : Blo 1194414 4912409 := bstep (se 2 (by rfl) ⟨1842153, by rfl⟩ : syracuseStep 4912409 = 3684307) B3684307
theorem B4536233 : Blo 1194414 4536233 := bstep (se 2 (by rfl) ⟨1701087, by rfl⟩ : syracuseStep 4536233 = 3402175) B3402175
theorem B1195007 : Blo 1194414 1195007 := bstep (se 1 (by rfl) ⟨896255, by rfl⟩ : syracuseStep 1195007 = 1792511) B1792511
theorem B3024155 : Blo 1194414 3024155 := bstep (se 1 (by rfl) ⟨2268116, by rfl⟩ : syracuseStep 3024155 = 4536233) B4536233
theorem B3402233 : Blo 1194414 3402233 := bstep (se 2 (by rfl) ⟨1275837, by rfl⟩ : syracuseStep 3402233 = 2551675) B2551675
theorem B9079451 : Blo 1194414 9079451 := bstep (se 1 (by rfl) ⟨6809588, by rfl⟩ : syracuseStep 9079451 = 13619177) B13619177
theorem B2690351 : Blo 1194414 2690351 := bstep (se 1 (by rfl) ⟨2017763, by rfl⟩ : syracuseStep 2690351 = 4035527) B4035527
theorem B3880915 : Blo 1194414 3880915 := bstep (se 1 (by rfl) ⟨2910686, by rfl⟩ : syracuseStep 3880915 = 5821373) B5821373
theorem B22984823 : Blo 1194414 22984823 := bstep (se 1 (by rfl) ⟨17238617, by rfl⟩ : syracuseStep 22984823 = 34477235) B34477235
theorem B1792169 : Blo 1194414 1792169 := bstep (se 2 (by rfl) ⟨672063, by rfl⟩ : syracuseStep 1792169 = 1344127) B1344127
theorem B3274939 : Blo 1194414 3274939 := bstep (se 1 (by rfl) ⟨2456204, by rfl⟩ : syracuseStep 3274939 = 4912409) B4912409
theorem B4366585 : Blo 1194414 4366585 := bstep (se 2 (by rfl) ⟨1637469, by rfl⟩ : syracuseStep 4366585 = 3274939) B3274939
theorem B2016103 : Blo 1194414 2016103 := bstep (se 1 (by rfl) ⟨1512077, by rfl⟩ : syracuseStep 2016103 = 3024155) B3024155
theorem B15323215 : Blo 1194414 15323215 := bstep (se 1 (by rfl) ⟨11492411, by rfl⟩ : syracuseStep 15323215 = 22984823) B22984823
theorem B20698213 : Blo 1194414 20698213 := bstep (se 4 (by rfl) ⟨1940457, by rfl⟩ : syracuseStep 20698213 = 3880915) B3880915
theorem B1194779 : Blo 1194414 1194779 := bstep (se 1 (by rfl) ⟨896084, by rfl⟩ : syracuseStep 1194779 = 1792169) B1792169
theorem B2268155 : Blo 1194414 2268155 := bstep (se 1 (by rfl) ⟨1701116, by rfl⟩ : syracuseStep 2268155 = 3402233) B3402233
theorem B6052967 : Blo 1194414 6052967 := bstep (se 1 (by rfl) ⟨4539725, by rfl⟩ : syracuseStep 6052967 = 9079451) B9079451
theorem B1793567 : Blo 1194414 1793567 := bstep (se 1 (by rfl) ⟨1345175, by rfl⟩ : syracuseStep 1793567 = 2690351) B2690351
theorem B20430953 : Blo 1194414 20430953 := bstep (se 2 (by rfl) ⟨7661607, by rfl⟩ : syracuseStep 20430953 = 15323215) B15323215
theorem B2688137 : Blo 1194414 2688137 := bstep (se 2 (by rfl) ⟨1008051, by rfl⟩ : syracuseStep 2688137 = 2016103) B2016103
theorem B1512103 : Blo 1194414 1512103 := bstep (se 1 (by rfl) ⟨1134077, by rfl⟩ : syracuseStep 1512103 = 2268155) B2268155
theorem B4035311 : Blo 1194414 4035311 := bstep (se 1 (by rfl) ⟨3026483, by rfl⟩ : syracuseStep 4035311 = 6052967) B6052967
theorem B5822113 : Blo 1194414 5822113 := bstep (se 2 (by rfl) ⟨2183292, by rfl⟩ : syracuseStep 5822113 = 4366585) B4366585
theorem B27597617 : Blo 1194414 27597617 := bstep (se 2 (by rfl) ⟨10349106, by rfl⟩ : syracuseStep 27597617 = 20698213) B20698213
theorem B1195711 : Blo 1194414 1195711 := bstep (se 1 (by rfl) ⟨896783, by rfl⟩ : syracuseStep 1195711 = 1793567) B1793567
theorem B2016137 : Blo 1194414 2016137 := bstep (se 2 (by rfl) ⟨756051, by rfl⟩ : syracuseStep 2016137 = 1512103) B1512103
theorem B2690207 : Blo 1194414 2690207 := bstep (se 1 (by rfl) ⟨2017655, by rfl⟩ : syracuseStep 2690207 = 4035311) B4035311
theorem B7762817 : Blo 1194414 7762817 := bstep (se 2 (by rfl) ⟨2911056, by rfl⟩ : syracuseStep 7762817 = 5822113) B5822113
theorem B13620635 : Blo 1194414 13620635 := bstep (se 1 (by rfl) ⟨10215476, by rfl⟩ : syracuseStep 13620635 = 20430953) B20430953
theorem B1792091 : Blo 1194414 1792091 := bstep (se 1 (by rfl) ⟨1344068, by rfl⟩ : syracuseStep 1792091 = 2688137) B2688137
theorem B18398411 : Blo 1194414 18398411 := bstep (se 1 (by rfl) ⟨13798808, by rfl⟩ : syracuseStep 18398411 = 27597617) B27597617
theorem B1344091 : Blo 1194414 1344091 := bstep (se 1 (by rfl) ⟨1008068, by rfl⟩ : syracuseStep 1344091 = 2016137) B2016137
theorem B12265607 : Blo 1194414 12265607 := bstep (se 1 (by rfl) ⟨9199205, by rfl⟩ : syracuseStep 12265607 = 18398411) B18398411
theorem B9080423 : Blo 1194414 9080423 := bstep (se 1 (by rfl) ⟨6810317, by rfl⟩ : syracuseStep 9080423 = 13620635) B13620635
theorem B1194727 : Blo 1194414 1194727 := bstep (se 1 (by rfl) ⟨896045, by rfl⟩ : syracuseStep 1194727 = 1792091) B1792091
theorem B1793471 : Blo 1194414 1793471 := bstep (se 1 (by rfl) ⟨1345103, by rfl⟩ : syracuseStep 1793471 = 2690207) B2690207
theorem B20700845 : Blo 1194414 20700845 := bstep (se 3 (by rfl) ⟨3881408, by rfl⟩ : syracuseStep 20700845 = 7762817) B7762817
theorem B8177071 : Blo 1194414 8177071 := bstep (se 1 (by rfl) ⟨6132803, by rfl⟩ : syracuseStep 8177071 = 12265607) B12265607
theorem B13800563 : Blo 1194414 13800563 := bstep (se 1 (by rfl) ⟨10350422, by rfl⟩ : syracuseStep 13800563 = 20700845) B20700845
theorem B1792121 : Blo 1194414 1792121 := bstep (se 2 (by rfl) ⟨672045, by rfl⟩ : syracuseStep 1792121 = 1344091) B1344091
theorem B1195647 : Blo 1194414 1195647 := bstep (se 1 (by rfl) ⟨896735, by rfl⟩ : syracuseStep 1195647 = 1793471) B1793471
theorem B6053615 : Blo 1194414 6053615 := bstep (se 1 (by rfl) ⟨4540211, by rfl⟩ : syracuseStep 6053615 = 9080423) B9080423
theorem B9200375 : Blo 1194414 9200375 := bstep (se 1 (by rfl) ⟨6900281, by rfl⟩ : syracuseStep 9200375 = 13800563) B13800563
theorem B4035743 : Blo 1194414 4035743 := bstep (se 1 (by rfl) ⟨3026807, by rfl⟩ : syracuseStep 4035743 = 6053615) B6053615
theorem B1194747 : Blo 1194414 1194747 := bstep (se 1 (by rfl) ⟨896060, by rfl⟩ : syracuseStep 1194747 = 1792121) B1792121
theorem B10902761 : Blo 1194414 10902761 := bstep (se 2 (by rfl) ⟨4088535, by rfl⟩ : syracuseStep 10902761 = 8177071) B8177071
theorem B7268507 : Blo 1194414 7268507 := bstep (se 1 (by rfl) ⟨5451380, by rfl⟩ : syracuseStep 7268507 = 10902761) B10902761
theorem B2690495 : Blo 1194414 2690495 := bstep (se 1 (by rfl) ⟨2017871, by rfl⟩ : syracuseStep 2690495 = 4035743) B4035743
theorem B6133583 : Blo 1194414 6133583 := bstep (se 1 (by rfl) ⟨4600187, by rfl⟩ : syracuseStep 6133583 = 9200375) B9200375
theorem B4089055 : Blo 1194414 4089055 := bstep (se 1 (by rfl) ⟨3066791, by rfl⟩ : syracuseStep 4089055 = 6133583) B6133583
theorem B4845671 : Blo 1194414 4845671 := bstep (se 1 (by rfl) ⟨3634253, by rfl⟩ : syracuseStep 4845671 = 7268507) B7268507
theorem B1793663 : Blo 1194414 1793663 := bstep (se 1 (by rfl) ⟨1345247, by rfl⟩ : syracuseStep 1793663 = 2690495) B2690495
theorem B3230447 : Blo 1194414 3230447 := bstep (se 1 (by rfl) ⟨2422835, by rfl⟩ : syracuseStep 3230447 = 4845671) B4845671
theorem B5452073 : Blo 1194414 5452073 := bstep (se 2 (by rfl) ⟨2044527, by rfl⟩ : syracuseStep 5452073 = 4089055) B4089055
theorem B1195775 : Blo 1194414 1195775 := bstep (se 1 (by rfl) ⟨896831, by rfl⟩ : syracuseStep 1195775 = 1793663) B1793663
theorem B8614525 : Blo 1194414 8614525 := bstep (se 3 (by rfl) ⟨1615223, by rfl⟩ : syracuseStep 8614525 = 3230447) B3230447
theorem B3634715 : Blo 1194414 3634715 := bstep (se 1 (by rfl) ⟨2726036, by rfl⟩ : syracuseStep 3634715 = 5452073) B5452073
theorem B11486033 : Blo 1194414 11486033 := bstep (se 2 (by rfl) ⟨4307262, by rfl⟩ : syracuseStep 11486033 = 8614525) B8614525
theorem B2423143 : Blo 1194414 2423143 := bstep (se 1 (by rfl) ⟨1817357, by rfl⟩ : syracuseStep 2423143 = 3634715) B3634715
theorem B3230857 : Blo 1194414 3230857 := bstep (se 2 (by rfl) ⟨1211571, by rfl⟩ : syracuseStep 3230857 = 2423143) B2423143
theorem B7657355 : Blo 1194414 7657355 := bstep (se 1 (by rfl) ⟨5743016, by rfl⟩ : syracuseStep 7657355 = 11486033) B11486033
theorem B5104903 : Blo 1194414 5104903 := bstep (se 1 (by rfl) ⟨3828677, by rfl⟩ : syracuseStep 5104903 = 7657355) B7657355
theorem B17231237 : Blo 1194414 17231237 := bstep (se 4 (by rfl) ⟨1615428, by rfl⟩ : syracuseStep 17231237 = 3230857) B3230857
theorem B11487491 : Blo 1194414 11487491 := bstep (se 1 (by rfl) ⟨8615618, by rfl⟩ : syracuseStep 11487491 = 17231237) B17231237
theorem B6806537 : Blo 1194414 6806537 := bstep (se 2 (by rfl) ⟨2552451, by rfl⟩ : syracuseStep 6806537 = 5104903) B5104903
theorem B7658327 : Blo 1194414 7658327 := bstep (se 1 (by rfl) ⟨5743745, by rfl⟩ : syracuseStep 7658327 = 11487491) B11487491
theorem B4537691 : Blo 1194414 4537691 := bstep (se 1 (by rfl) ⟨3403268, by rfl⟩ : syracuseStep 4537691 = 6806537) B6806537
theorem B3025127 : Blo 1194414 3025127 := bstep (se 1 (by rfl) ⟨2268845, by rfl⟩ : syracuseStep 3025127 = 4537691) B4537691
theorem B20422205 : Blo 1194414 20422205 := bstep (se 3 (by rfl) ⟨3829163, by rfl⟩ : syracuseStep 20422205 = 7658327) B7658327
theorem B2016751 : Blo 1194414 2016751 := bstep (se 1 (by rfl) ⟨1512563, by rfl⟩ : syracuseStep 2016751 = 3025127) B3025127
theorem B13614803 : Blo 1194414 13614803 := bstep (se 1 (by rfl) ⟨10211102, by rfl⟩ : syracuseStep 13614803 = 20422205) B20422205
theorem B2689001 : Blo 1194414 2689001 := bstep (se 2 (by rfl) ⟨1008375, by rfl⟩ : syracuseStep 2689001 = 2016751) B2016751
theorem B9076535 : Blo 1194414 9076535 := bstep (se 1 (by rfl) ⟨6807401, by rfl⟩ : syracuseStep 9076535 = 13614803) B13614803
theorem B6051023 : Blo 1194414 6051023 := bstep (se 1 (by rfl) ⟨4538267, by rfl⟩ : syracuseStep 6051023 = 9076535) B9076535
theorem B1792667 : Blo 1194414 1792667 := bstep (se 1 (by rfl) ⟨1344500, by rfl⟩ : syracuseStep 1792667 = 2689001) B2689001
theorem B4034015 : Blo 1194414 4034015 := bstep (se 1 (by rfl) ⟨3025511, by rfl⟩ : syracuseStep 4034015 = 6051023) B6051023
theorem B1195111 : Blo 1194414 1195111 := bstep (se 1 (by rfl) ⟨896333, by rfl⟩ : syracuseStep 1195111 = 1792667) B1792667
theorem B2689343 : Blo 1194414 2689343 := bstep (se 1 (by rfl) ⟨2017007, by rfl⟩ : syracuseStep 2689343 = 4034015) B4034015
theorem B1792895 : Blo 1194414 1792895 := bstep (se 1 (by rfl) ⟨1344671, by rfl⟩ : syracuseStep 1792895 = 2689343) B2689343
theorem B1195263 : Blo 1194414 1195263 := bstep (se 1 (by rfl) ⟨896447, by rfl⟩ : syracuseStep 1195263 = 1792895) B1792895

theorem C0 (j : ℕ) (h1 : 298603 ≤ j) (h2 : j ≤ 299102) : Blo 1194414 (4 * j + 3) := by
  interval_cases j
  · exact B1194415
  · exact B1194419
  · exact B1194423
  · exact B1194427
  · exact B1194431
  · exact B1194435
  · exact B1194439
  · exact B1194443
  · exact B1194447
  · exact B1194451
  · exact B1194455
  · exact B1194459
  · exact B1194463
  · exact B1194467
  · exact B1194471
  · exact B1194475
  · exact B1194479
  · exact B1194483
  · exact B1194487
  · exact B1194491
  · exact B1194495
  · exact B1194499
  · exact B1194503
  · exact B1194507
  · exact B1194511
  · exact B1194515
  · exact B1194519
  · exact B1194523
  · exact B1194527
  · exact B1194531
  · exact B1194535
  · exact B1194539
  · exact B1194543
  · exact B1194547
  · exact B1194551
  · exact B1194555
  · exact B1194559
  · exact B1194563
  · exact B1194567
  · exact B1194571
  · exact B1194575
  · exact B1194579
  · exact B1194583
  · exact B1194587
  · exact B1194591
  · exact B1194595
  · exact B1194599
  · exact B1194603
  · exact B1194607
  · exact B1194611
  · exact B1194615
  · exact B1194619
  · exact B1194623
  · exact B1194627
  · exact B1194631
  · exact B1194635
  · exact B1194639
  · exact B1194643
  · exact B1194647
  · exact B1194651
  · exact B1194655
  · exact B1194659
  · exact B1194663
  · exact B1194667
  · exact B1194671
  · exact B1194675
  · exact B1194679
  · exact B1194683
  · exact B1194687
  · exact B1194691
  · exact B1194695
  · exact B1194699
  · exact B1194703
  · exact B1194707
  · exact B1194711
  · exact B1194715
  · exact B1194719
  · exact B1194723
  · exact B1194727
  · exact B1194731
  · exact B1194735
  · exact B1194739
  · exact B1194743
  · exact B1194747
  · exact B1194751
  · exact B1194755
  · exact B1194759
  · exact B1194763
  · exact B1194767
  · exact B1194771
  · exact B1194775
  · exact B1194779
  · exact B1194783
  · exact B1194787
  · exact B1194791
  · exact B1194795
  · exact B1194799
  · exact B1194803
  · exact B1194807
  · exact B1194811
  · exact B1194815
  · exact B1194819
  · exact B1194823
  · exact B1194827
  · exact B1194831
  · exact B1194835
  · exact B1194839
  · exact B1194843
  · exact B1194847
  · exact B1194851
  · exact B1194855
  · exact B1194859
  · exact B1194863
  · exact B1194867
  · exact B1194871
  · exact B1194875
  · exact B1194879
  · exact B1194883
  · exact B1194887
  · exact B1194891
  · exact B1194895
  · exact B1194899
  · exact B1194903
  · exact B1194907
  · exact B1194911
  · exact B1194915
  · exact B1194919
  · exact B1194923
  · exact B1194927
  · exact B1194931
  · exact B1194935
  · exact B1194939
  · exact B1194943
  · exact B1194947
  · exact B1194951
  · exact B1194955
  · exact B1194959
  · exact B1194963
  · exact B1194967
  · exact B1194971
  · exact B1194975
  · exact B1194979
  · exact B1194983
  · exact B1194987
  · exact B1194991
  · exact B1194995
  · exact B1194999
  · exact B1195003
  · exact B1195007
  · exact B1195011
  · exact B1195015
  · exact B1195019
  · exact B1195023
  · exact B1195027
  · exact B1195031
  · exact B1195035
  · exact B1195039
  · exact B1195043
  · exact B1195047
  · exact B1195051
  · exact B1195055
  · exact B1195059
  · exact B1195063
  · exact B1195067
  · exact B1195071
  · exact B1195075
  · exact B1195079
  · exact B1195083
  · exact B1195087
  · exact B1195091
  · exact B1195095
  · exact B1195099
  · exact B1195103
  · exact B1195107
  · exact B1195111
  · exact B1195115
  · exact B1195119
  · exact B1195123
  · exact B1195127
  · exact B1195131
  · exact B1195135
  · exact B1195139
  · exact B1195143
  · exact B1195147
  · exact B1195151
  · exact B1195155
  · exact B1195159
  · exact B1195163
  · exact B1195167
  · exact B1195171
  · exact B1195175
  · exact B1195179
  · exact B1195183
  · exact B1195187
  · exact B1195191
  · exact B1195195
  · exact B1195199
  · exact B1195203
  · exact B1195207
  · exact B1195211
  · exact B1195215
  · exact B1195219
  · exact B1195223
  · exact B1195227
  · exact B1195231
  · exact B1195235
  · exact B1195239
  · exact B1195243
  · exact B1195247
  · exact B1195251
  · exact B1195255
  · exact B1195259
  · exact B1195263
  · exact B1195267
  · exact B1195271
  · exact B1195275
  · exact B1195279
  · exact B1195283
  · exact B1195287
  · exact B1195291
  · exact B1195295
  · exact B1195299
  · exact B1195303
  · exact B1195307
  · exact B1195311
  · exact B1195315
  · exact B1195319
  · exact B1195323
  · exact B1195327
  · exact B1195331
  · exact B1195335
  · exact B1195339
  · exact B1195343
  · exact B1195347
  · exact B1195351
  · exact B1195355
  · exact B1195359
  · exact B1195363
  · exact B1195367
  · exact B1195371
  · exact B1195375
  · exact B1195379
  · exact B1195383
  · exact B1195387
  · exact B1195391
  · exact B1195395
  · exact B1195399
  · exact B1195403
  · exact B1195407
  · exact B1195411
  · exact B1195415
  · exact B1195419
  · exact B1195423
  · exact B1195427
  · exact B1195431
  · exact B1195435
  · exact B1195439
  · exact B1195443
  · exact B1195447
  · exact B1195451
  · exact B1195455
  · exact B1195459
  · exact B1195463
  · exact B1195467
  · exact B1195471
  · exact B1195475
  · exact B1195479
  · exact B1195483
  · exact B1195487
  · exact B1195491
  · exact B1195495
  · exact B1195499
  · exact B1195503
  · exact B1195507
  · exact B1195511
  · exact B1195515
  · exact B1195519
  · exact B1195523
  · exact B1195527
  · exact B1195531
  · exact B1195535
  · exact B1195539
  · exact B1195543
  · exact B1195547
  · exact B1195551
  · exact B1195555
  · exact B1195559
  · exact B1195563
  · exact B1195567
  · exact B1195571
  · exact B1195575
  · exact B1195579
  · exact B1195583
  · exact B1195587
  · exact B1195591
  · exact B1195595
  · exact B1195599
  · exact B1195603
  · exact B1195607
  · exact B1195611
  · exact B1195615
  · exact B1195619
  · exact B1195623
  · exact B1195627
  · exact B1195631
  · exact B1195635
  · exact B1195639
  · exact B1195643
  · exact B1195647
  · exact B1195651
  · exact B1195655
  · exact B1195659
  · exact B1195663
  · exact B1195667
  · exact B1195671
  · exact B1195675
  · exact B1195679
  · exact B1195683
  · exact B1195687
  · exact B1195691
  · exact B1195695
  · exact B1195699
  · exact B1195703
  · exact B1195707
  · exact B1195711
  · exact B1195715
  · exact B1195719
  · exact B1195723
  · exact B1195727
  · exact B1195731
  · exact B1195735
  · exact B1195739
  · exact B1195743
  · exact B1195747
  · exact B1195751
  · exact B1195755
  · exact B1195759
  · exact B1195763
  · exact B1195767
  · exact B1195771
  · exact B1195775
  · exact B1195779
  · exact B1195783
  · exact B1195787
  · exact B1195791
  · exact B1195795
  · exact B1195799
  · exact B1195803
  · exact B1195807
  · exact B1195811
  · exact B1195815
  · exact B1195819
  · exact B1195823
  · exact B1195827
  · exact B1195831
  · exact B1195835
  · exact B1195839
  · exact B1195843
  · exact B1195847
  · exact B1195851
  · exact B1195855
  · exact B1195859
  · exact B1195863
  · exact B1195867
  · exact B1195871
  · exact B1195875
  · exact B1195879
  · exact B1195883
  · exact B1195887
  · exact B1195891
  · exact B1195895
  · exact B1195899
  · exact B1195903
  · exact B1195907
  · exact B1195911
  · exact B1195915
  · exact B1195919
  · exact B1195923
  · exact B1195927
  · exact B1195931
  · exact B1195935
  · exact B1195939
  · exact B1195943
  · exact B1195947
  · exact B1195951
  · exact B1195955
  · exact B1195959
  · exact B1195963
  · exact B1195967
  · exact B1195971
  · exact B1195975
  · exact B1195979
  · exact B1195983
  · exact B1195987
  · exact B1195991
  · exact B1195995
  · exact B1195999
  · exact B1196003
  · exact B1196007
  · exact B1196011
  · exact B1196015
  · exact B1196019
  · exact B1196023
  · exact B1196027
  · exact B1196031
  · exact B1196035
  · exact B1196039
  · exact B1196043
  · exact B1196047
  · exact B1196051
  · exact B1196055
  · exact B1196059
  · exact B1196063
  · exact B1196067
  · exact B1196071
  · exact B1196075
  · exact B1196079
  · exact B1196083
  · exact B1196087
  · exact B1196091
  · exact B1196095
  · exact B1196099
  · exact B1196103
  · exact B1196107
  · exact B1196111
  · exact B1196115
  · exact B1196119
  · exact B1196123
  · exact B1196127
  · exact B1196131
  · exact B1196135
  · exact B1196139
  · exact B1196143
  · exact B1196147
  · exact B1196151
  · exact B1196155
  · exact B1196159
  · exact B1196163
  · exact B1196167
  · exact B1196171
  · exact B1196175
  · exact B1196179
  · exact B1196183
  · exact B1196187
  · exact B1196191
  · exact B1196195
  · exact B1196199
  · exact B1196203
  · exact B1196207
  · exact B1196211
  · exact B1196215
  · exact B1196219
  · exact B1196223
  · exact B1196227
  · exact B1196231
  · exact B1196235
  · exact B1196239
  · exact B1196243
  · exact B1196247
  · exact B1196251
  · exact B1196255
  · exact B1196259
  · exact B1196263
  · exact B1196267
  · exact B1196271
  · exact B1196275
  · exact B1196279
  · exact B1196283
  · exact B1196287
  · exact B1196291
  · exact B1196295
  · exact B1196299
  · exact B1196303
  · exact B1196307
  · exact B1196311
  · exact B1196315
  · exact B1196319
  · exact B1196323
  · exact B1196327
  · exact B1196331
  · exact B1196335
  · exact B1196339
  · exact B1196343
  · exact B1196347
  · exact B1196351
  · exact B1196355
  · exact B1196359
  · exact B1196363
  · exact B1196367
  · exact B1196371
  · exact B1196375
  · exact B1196379
  · exact B1196383
  · exact B1196387
  · exact B1196391
  · exact B1196395
  · exact B1196399
  · exact B1196403
  · exact B1196407
  · exact B1196411

theorem solution (m : ℕ) (hlo : 1194414 ≤ m) (hhi : m ≤ 1196414) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 298603 ≤ j := by omega
    have hj2 : j ≤ 299102 := by omega
    have hb : Blo 1194414 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
