-- Prove2me | solution 1 for syracuse_descends_range_1020604_1024604
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:20.009757+00:00
-- url     : https://prove2.me/submissions/38ff9394-471a-4ca2-9f8b-9d523991612a

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


theorem B2621525 : Blo 1020604 2621525 := bbase (se 8 (by rfl) ⟨15360, by rfl⟩ : syracuseStep 2621525 = 30721) (by norm_num)
theorem B2588861 : Blo 1020604 2588861 := bbase (se 3 (by rfl) ⟨485411, by rfl⟩ : syracuseStep 2588861 = 970823) (by norm_num)
theorem B1638605 : Blo 1020604 1638605 := bbase (se 3 (by rfl) ⟨307238, by rfl⟩ : syracuseStep 1638605 = 614477) (by norm_num)
theorem B2457877 : Blo 1020604 2457877 := bbase (se 6 (by rfl) ⟨57606, by rfl⟩ : syracuseStep 2457877 = 115213) (by norm_num)
theorem B2916661 : Blo 1020604 2916661 := bbase (se 5 (by rfl) ⟨136718, by rfl⟩ : syracuseStep 2916661 = 273437) (by norm_num)
theorem B2589205 : Blo 1020604 2589205 := bbase (se 6 (by rfl) ⟨60684, by rfl⟩ : syracuseStep 2589205 = 121369) (by norm_num)
theorem B2589317 : Blo 1020604 2589317 := bbase (se 4 (by rfl) ⟨242748, by rfl⟩ : syracuseStep 2589317 = 485497) (by norm_num)
theorem B5178005 : Blo 1020604 5178005 := bbase (se 6 (by rfl) ⟨121359, by rfl⟩ : syracuseStep 5178005 = 242719) (by norm_num)
theorem B2654893 : Blo 1020604 2654893 := bbase (se 3 (by rfl) ⟨497792, by rfl⟩ : syracuseStep 2654893 = 995585) (by norm_num)
theorem B2589509 : Blo 1020604 2589509 := bbase (se 4 (by rfl) ⟨242766, by rfl⟩ : syracuseStep 2589509 = 485533) (by norm_num)
theorem B1967069 : Blo 1020604 1967069 := bbase (se 3 (by rfl) ⟨368825, by rfl⟩ : syracuseStep 1967069 = 737651) (by norm_num)
theorem B6554645 : Blo 1020604 6554645 := bbase (se 6 (by rfl) ⟨153624, by rfl⟩ : syracuseStep 6554645 = 307249) (by norm_num)
theorem B2589853 : Blo 1020604 2589853 := bbase (se 3 (by rfl) ⟨485597, by rfl⟩ : syracuseStep 2589853 = 971195) (by norm_num)
theorem B1311913 : Blo 1020604 1311913 := bbase (se 2 (by rfl) ⟨491967, by rfl⟩ : syracuseStep 1311913 = 983935) (by norm_num)
theorem B1639597 : Blo 1020604 1639597 := bbase (se 3 (by rfl) ⟨307424, by rfl⟩ : syracuseStep 1639597 = 614849) (by norm_num)
theorem B2589965 : Blo 1020604 2589965 := bbase (se 3 (by rfl) ⟨485618, by rfl⟩ : syracuseStep 2589965 = 971237) (by norm_num)
theorem B1148197 : Blo 1020604 1148197 := bbase (se 4 (by rfl) ⟨107643, by rfl⟩ : syracuseStep 1148197 = 215287) (by norm_num)
theorem B1148233 : Blo 1020604 1148233 := bbase (se 2 (by rfl) ⟨430587, by rfl⟩ : syracuseStep 1148233 = 861175) (by norm_num)
theorem B1148269 : Blo 1020604 1148269 := bbase (se 3 (by rfl) ⟨215300, by rfl⟩ : syracuseStep 1148269 = 430601) (by norm_num)
theorem B1148305 : Blo 1020604 1148305 := bbase (se 2 (by rfl) ⟨430614, by rfl⟩ : syracuseStep 1148305 = 861229) (by norm_num)
theorem B3278245 : Blo 1020604 3278245 := bbase (se 4 (by rfl) ⟨307335, by rfl⟩ : syracuseStep 3278245 = 614671) (by norm_num)
theorem B1148341 : Blo 1020604 1148341 := bbase (se 5 (by rfl) ⟨53828, by rfl⟩ : syracuseStep 1148341 = 107657) (by norm_num)
theorem B2459069 : Blo 1020604 2459069 := bbase (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) (by norm_num)
theorem B2590157 : Blo 1020604 2590157 := bbase (se 3 (by rfl) ⟨485654, by rfl⟩ : syracuseStep 2590157 = 971309) (by norm_num)
theorem B1148377 : Blo 1020604 1148377 := bbase (se 2 (by rfl) ⟨430641, by rfl⟩ : syracuseStep 1148377 = 861283) (by norm_num)
theorem B1148413 : Blo 1020604 1148413 := bbase (se 3 (by rfl) ⟨215327, by rfl⟩ : syracuseStep 1148413 = 430655) (by norm_num)
theorem B1148449 : Blo 1020604 1148449 := bbase (se 2 (by rfl) ⟨430668, by rfl⟩ : syracuseStep 1148449 = 861337) (by norm_num)
theorem B1148485 : Blo 1020604 1148485 := bbase (se 4 (by rfl) ⟨107670, by rfl⟩ : syracuseStep 1148485 = 215341) (by norm_num)
theorem B1148521 : Blo 1020604 1148521 := bbase (se 2 (by rfl) ⟨430695, by rfl⟩ : syracuseStep 1148521 = 861391) (by norm_num)
theorem B1640045 : Blo 1020604 1640045 := bbase (se 3 (by rfl) ⟨307508, by rfl⟩ : syracuseStep 1640045 = 615017) (by norm_num)
theorem B2459261 : Blo 1020604 2459261 := bbase (se 3 (by rfl) ⟨461111, by rfl⟩ : syracuseStep 2459261 = 922223) (by norm_num)
theorem B1148557 : Blo 1020604 1148557 := bbase (se 3 (by rfl) ⟨215354, by rfl⟩ : syracuseStep 1148557 = 430709) (by norm_num)
theorem B1312405 : Blo 1020604 1312405 := bbase (se 6 (by rfl) ⟨30759, by rfl⟩ : syracuseStep 1312405 = 61519) (by norm_num)
theorem B1148593 : Blo 1020604 1148593 := bbase (se 2 (by rfl) ⟨430722, by rfl⟩ : syracuseStep 1148593 = 861445) (by norm_num)
theorem B1312453 : Blo 1020604 1312453 := bbase (se 4 (by rfl) ⟨123042, by rfl⟩ : syracuseStep 1312453 = 246085) (by norm_num)
theorem B1148629 : Blo 1020604 1148629 := bbase (se 7 (by rfl) ⟨13460, by rfl⟩ : syracuseStep 1148629 = 26921) (by norm_num)
theorem B1148665 : Blo 1020604 1148665 := bbase (se 2 (by rfl) ⟨430749, by rfl⟩ : syracuseStep 1148665 = 861499) (by norm_num)
theorem B1148701 : Blo 1020604 1148701 := bbase (se 3 (by rfl) ⟨215381, by rfl⟩ : syracuseStep 1148701 = 430763) (by norm_num)
theorem B2590501 : Blo 1020604 2590501 := bbase (se 4 (by rfl) ⟨242859, by rfl⟩ : syracuseStep 2590501 = 485719) (by norm_num)
theorem B1640245 : Blo 1020604 1640245 := bbase (se 5 (by rfl) ⟨76886, by rfl⟩ : syracuseStep 1640245 = 153773) (by norm_num)
theorem B1148737 : Blo 1020604 1148737 := bbase (se 2 (by rfl) ⟨430776, by rfl⟩ : syracuseStep 1148737 = 861553) (by norm_num)
theorem B1148773 : Blo 1020604 1148773 := bbase (se 4 (by rfl) ⟨107697, by rfl⟩ : syracuseStep 1148773 = 215395) (by norm_num)
theorem B1148809 : Blo 1020604 1148809 := bbase (se 2 (by rfl) ⟨430803, by rfl⟩ : syracuseStep 1148809 = 861607) (by norm_num)
theorem B2590613 : Blo 1020604 2590613 := bbase (se 6 (by rfl) ⟨60717, by rfl⟩ : syracuseStep 2590613 = 121435) (by norm_num)
theorem B5179301 : Blo 1020604 5179301 := bbase (se 4 (by rfl) ⟨485559, by rfl⟩ : syracuseStep 5179301 = 971119) (by norm_num)
theorem B1148845 : Blo 1020604 1148845 := bbase (se 3 (by rfl) ⟨215408, by rfl⟩ : syracuseStep 1148845 = 430817) (by norm_num)
theorem B1312697 : Blo 1020604 1312697 := bbase (se 2 (by rfl) ⟨492261, by rfl⟩ : syracuseStep 1312697 = 984523) (by norm_num)
theorem B1148881 : Blo 1020604 1148881 := bbase (se 2 (by rfl) ⟨430830, by rfl⟩ : syracuseStep 1148881 = 861661) (by norm_num)
theorem B1148917 : Blo 1020604 1148917 := bbase (se 5 (by rfl) ⟨53855, by rfl⟩ : syracuseStep 1148917 = 107711) (by norm_num)
theorem B1148953 : Blo 1020604 1148953 := bbase (se 2 (by rfl) ⟨430857, by rfl⟩ : syracuseStep 1148953 = 861715) (by norm_num)
theorem B1640501 : Blo 1020604 1640501 := bbase (se 5 (by rfl) ⟨76898, by rfl⟩ : syracuseStep 1640501 = 153797) (by norm_num)
theorem B1148989 : Blo 1020604 1148989 := bbase (se 3 (by rfl) ⟨215435, by rfl⟩ : syracuseStep 1148989 = 430871) (by norm_num)
theorem B2590805 : Blo 1020604 2590805 := bbase (se 8 (by rfl) ⟨15180, by rfl⟩ : syracuseStep 2590805 = 30361) (by norm_num)
theorem B1149025 : Blo 1020604 1149025 := bbase (se 2 (by rfl) ⟨430884, by rfl⟩ : syracuseStep 1149025 = 861769) (by norm_num)
theorem B1149061 : Blo 1020604 1149061 := bbase (se 4 (by rfl) ⟨107724, by rfl⟩ : syracuseStep 1149061 = 215449) (by norm_num)
theorem B1149097 : Blo 1020604 1149097 := bbase (se 2 (by rfl) ⟨430911, by rfl⟩ : syracuseStep 1149097 = 861823) (by norm_num)
theorem B1149133 : Blo 1020604 1149133 := bbase (se 3 (by rfl) ⟨215462, by rfl⟩ : syracuseStep 1149133 = 430925) (by norm_num)
theorem B9832661 : Blo 1020604 9832661 := bbase (se 7 (by rfl) ⟨115226, by rfl⟩ : syracuseStep 9832661 = 230453) (by norm_num)
theorem B17500373 : Blo 1020604 17500373 := bbase (se 7 (by rfl) ⟨205082, by rfl⟩ : syracuseStep 17500373 = 410165) (by norm_num)
theorem B1149169 : Blo 1020604 1149169 := bbase (se 2 (by rfl) ⟨430938, by rfl⟩ : syracuseStep 1149169 = 861877) (by norm_num)
theorem B1149205 : Blo 1020604 1149205 := bbase (se 6 (by rfl) ⟨26934, by rfl⟩ : syracuseStep 1149205 = 53869) (by norm_num)
theorem B1149241 : Blo 1020604 1149241 := bbase (se 2 (by rfl) ⟨430965, by rfl⟩ : syracuseStep 1149241 = 861931) (by norm_num)
theorem B1149277 : Blo 1020604 1149277 := bbase (se 3 (by rfl) ⟨215489, by rfl⟩ : syracuseStep 1149277 = 430979) (by norm_num)
theorem B1149313 : Blo 1020604 1149313 := bbase (se 2 (by rfl) ⟨430992, by rfl⟩ : syracuseStep 1149313 = 861985) (by norm_num)
theorem B1149349 : Blo 1020604 1149349 := bbase (se 4 (by rfl) ⟨107751, by rfl⟩ : syracuseStep 1149349 = 215503) (by norm_num)
theorem B2591149 : Blo 1020604 2591149 := bbase (se 3 (by rfl) ⟨485840, by rfl⟩ : syracuseStep 2591149 = 971681) (by norm_num)
theorem B2329013 : Blo 1020604 2329013 := bbase (se 5 (by rfl) ⟨109172, by rfl⟩ : syracuseStep 2329013 = 218345) (by norm_num)
theorem B1149385 : Blo 1020604 1149385 := bbase (se 2 (by rfl) ⟨431019, by rfl⟩ : syracuseStep 1149385 = 862039) (by norm_num)
theorem B1149421 : Blo 1020604 1149421 := bbase (se 3 (by rfl) ⟨215516, by rfl⟩ : syracuseStep 1149421 = 431033) (by norm_num)
theorem B1313273 : Blo 1020604 1313273 := bbase (se 2 (by rfl) ⟨492477, by rfl⟩ : syracuseStep 1313273 = 984955) (by norm_num)
theorem B1149457 : Blo 1020604 1149457 := bbase (se 2 (by rfl) ⟨431046, by rfl⟩ : syracuseStep 1149457 = 862093) (by norm_num)
theorem B2591261 : Blo 1020604 2591261 := bbase (se 3 (by rfl) ⟨485861, by rfl⟩ : syracuseStep 2591261 = 971723) (by norm_num)
theorem B1149493 : Blo 1020604 1149493 := bbase (se 5 (by rfl) ⟨53882, by rfl⟩ : syracuseStep 1149493 = 107765) (by norm_num)
theorem B4917829 : Blo 1020604 4917829 := bbase (se 4 (by rfl) ⟨461046, by rfl⟩ : syracuseStep 4917829 = 922093) (by norm_num)
theorem B1149529 : Blo 1020604 1149529 := bbase (se 2 (by rfl) ⟨431073, by rfl⟩ : syracuseStep 1149529 = 862147) (by norm_num)
theorem B2296421 : Blo 1020604 2296421 := bbase (se 4 (by rfl) ⟨215289, by rfl⟩ : syracuseStep 2296421 = 430579) (by norm_num)
theorem B1149565 : Blo 1020604 1149565 := bbase (se 3 (by rfl) ⟨215543, by rfl⟩ : syracuseStep 1149565 = 431087) (by norm_num)
theorem B1149601 : Blo 1020604 1149601 := bbase (se 2 (by rfl) ⟨431100, by rfl⟩ : syracuseStep 1149601 = 862201) (by norm_num)
theorem B2296493 : Blo 1020604 2296493 := bbase (se 3 (by rfl) ⟨430592, by rfl⟩ : syracuseStep 2296493 = 861185) (by norm_num)
theorem B1149637 : Blo 1020604 1149637 := bbase (se 4 (by rfl) ⟨107778, by rfl⟩ : syracuseStep 1149637 = 215557) (by norm_num)
theorem B2591453 : Blo 1020604 2591453 := bbase (se 3 (by rfl) ⟨485897, by rfl⟩ : syracuseStep 2591453 = 971795) (by norm_num)
theorem B1149673 : Blo 1020604 1149673 := bbase (se 2 (by rfl) ⟨431127, by rfl⟩ : syracuseStep 1149673 = 862255) (by norm_num)
theorem B2296565 : Blo 1020604 2296565 := bbase (se 5 (by rfl) ⟨107651, by rfl⟩ : syracuseStep 2296565 = 215303) (by norm_num)
theorem B1149709 : Blo 1020604 1149709 := bbase (se 3 (by rfl) ⟨215570, by rfl⟩ : syracuseStep 1149709 = 431141) (by norm_num)
theorem B1149745 : Blo 1020604 1149745 := bbase (se 2 (by rfl) ⟨431154, by rfl⟩ : syracuseStep 1149745 = 862309) (by norm_num)
theorem B2296637 : Blo 1020604 2296637 := bbase (se 3 (by rfl) ⟨430619, by rfl⟩ : syracuseStep 2296637 = 861239) (by norm_num)
theorem B1149781 : Blo 1020604 1149781 := bbase (se 9 (by rfl) ⟨3368, by rfl⟩ : syracuseStep 1149781 = 6737) (by norm_num)
theorem B1149817 : Blo 1020604 1149817 := bbase (se 2 (by rfl) ⟨431181, by rfl⟩ : syracuseStep 1149817 = 862363) (by norm_num)
theorem B2296709 : Blo 1020604 2296709 := bbase (se 4 (by rfl) ⟨215316, by rfl⟩ : syracuseStep 2296709 = 430633) (by norm_num)
theorem B11668373 : Blo 1020604 11668373 := bbase (se 6 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 11668373 = 546955) (by norm_num)
theorem B1149853 : Blo 1020604 1149853 := bbase (se 3 (by rfl) ⟨215597, by rfl⟩ : syracuseStep 1149853 = 431195) (by norm_num)
theorem B1149889 : Blo 1020604 1149889 := bbase (se 2 (by rfl) ⟨431208, by rfl⟩ : syracuseStep 1149889 = 862417) (by norm_num)
theorem B2296781 : Blo 1020604 2296781 := bbase (se 3 (by rfl) ⟨430646, by rfl⟩ : syracuseStep 2296781 = 861293) (by norm_num)
theorem B1149925 : Blo 1020604 1149925 := bbase (se 4 (by rfl) ⟨107805, by rfl⟩ : syracuseStep 1149925 = 215611) (by norm_num)
theorem B1149961 : Blo 1020604 1149961 := bbase (se 2 (by rfl) ⟨431235, by rfl⟩ : syracuseStep 1149961 = 862471) (by norm_num)
theorem B2296853 : Blo 1020604 2296853 := bbase (se 6 (by rfl) ⟨53832, by rfl⟩ : syracuseStep 2296853 = 107665) (by norm_num)
theorem B1149997 : Blo 1020604 1149997 := bbase (se 3 (by rfl) ⟨215624, by rfl⟩ : syracuseStep 1149997 = 431249) (by norm_num)
theorem B2591797 : Blo 1020604 2591797 := bbase (se 5 (by rfl) ⟨121490, by rfl⟩ : syracuseStep 2591797 = 242981) (by norm_num)
theorem B1150033 : Blo 1020604 1150033 := bbase (se 2 (by rfl) ⟨431262, by rfl⟩ : syracuseStep 1150033 = 862525) (by norm_num)
theorem B2296925 : Blo 1020604 2296925 := bbase (se 3 (by rfl) ⟨430673, by rfl⟩ : syracuseStep 2296925 = 861347) (by norm_num)
theorem B1150069 : Blo 1020604 1150069 := bbase (se 5 (by rfl) ⟨53909, by rfl⟩ : syracuseStep 1150069 = 107819) (by norm_num)
theorem B1150105 : Blo 1020604 1150105 := bbase (se 2 (by rfl) ⟨431289, by rfl⟩ : syracuseStep 1150105 = 862579) (by norm_num)
theorem B2296997 : Blo 1020604 2296997 := bbase (se 4 (by rfl) ⟨215343, by rfl⟩ : syracuseStep 2296997 = 430687) (by norm_num)
theorem B2591909 : Blo 1020604 2591909 := bbase (se 4 (by rfl) ⟨242991, by rfl⟩ : syracuseStep 2591909 = 485983) (by norm_num)
theorem B5180597 : Blo 1020604 5180597 := bbase (se 5 (by rfl) ⟨242840, by rfl⟩ : syracuseStep 5180597 = 485681) (by norm_num)
theorem B1150141 : Blo 1020604 1150141 := bbase (se 3 (by rfl) ⟨215651, by rfl⟩ : syracuseStep 1150141 = 431303) (by norm_num)
theorem B1150177 : Blo 1020604 1150177 := bbase (se 2 (by rfl) ⟨431316, by rfl⟩ : syracuseStep 1150177 = 862633) (by norm_num)
theorem B2297069 : Blo 1020604 2297069 := bbase (se 3 (by rfl) ⟨430700, by rfl⟩ : syracuseStep 2297069 = 861401) (by norm_num)
theorem B1150213 : Blo 1020604 1150213 := bbase (se 4 (by rfl) ⟨107832, by rfl⟩ : syracuseStep 1150213 = 215665) (by norm_num)
theorem B1150249 : Blo 1020604 1150249 := bbase (se 2 (by rfl) ⟨431343, by rfl⟩ : syracuseStep 1150249 = 862687) (by norm_num)
theorem B2297141 : Blo 1020604 2297141 := bbase (se 5 (by rfl) ⟨107678, by rfl⟩ : syracuseStep 2297141 = 215357) (by norm_num)
theorem B1150285 : Blo 1020604 1150285 := bbase (se 3 (by rfl) ⟨215678, by rfl⟩ : syracuseStep 1150285 = 431357) (by norm_num)
theorem B2592101 : Blo 1020604 2592101 := bbase (se 4 (by rfl) ⟨243009, by rfl⟩ : syracuseStep 2592101 = 486019) (by norm_num)
theorem B1150321 : Blo 1020604 1150321 := bbase (se 2 (by rfl) ⟨431370, by rfl⟩ : syracuseStep 1150321 = 862741) (by norm_num)
theorem B2297213 : Blo 1020604 2297213 := bbase (se 3 (by rfl) ⟨430727, by rfl⟩ : syracuseStep 2297213 = 861455) (by norm_num)
theorem B1150357 : Blo 1020604 1150357 := bbase (se 6 (by rfl) ⟨26961, by rfl⟩ : syracuseStep 1150357 = 53923) (by norm_num)
theorem B4656565 : Blo 1020604 4656565 := bbase (se 5 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 4656565 = 436553) (by norm_num)
theorem B1150393 : Blo 1020604 1150393 := bbase (se 2 (by rfl) ⟨431397, by rfl⟩ : syracuseStep 1150393 = 862795) (by norm_num)
theorem B2297285 : Blo 1020604 2297285 := bbase (se 4 (by rfl) ⟨215370, by rfl⟩ : syracuseStep 2297285 = 430741) (by norm_num)
theorem B7376341 : Blo 1020604 7376341 := bbase (se 7 (by rfl) ⟨86441, by rfl⟩ : syracuseStep 7376341 = 172883) (by norm_num)
theorem B1150429 : Blo 1020604 1150429 := bbase (se 3 (by rfl) ⟨215705, by rfl⟩ : syracuseStep 1150429 = 431411) (by norm_num)
theorem B1150465 : Blo 1020604 1150465 := bbase (se 2 (by rfl) ⟨431424, by rfl⟩ : syracuseStep 1150465 = 862849) (by norm_num)
theorem B2297357 : Blo 1020604 2297357 := bbase (se 3 (by rfl) ⟨430754, by rfl⟩ : syracuseStep 2297357 = 861509) (by norm_num)
theorem B2428453 : Blo 1020604 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B1150501 : Blo 1020604 1150501 := bbase (se 4 (by rfl) ⟨107859, by rfl⟩ : syracuseStep 1150501 = 215719) (by norm_num)
theorem B2494013 : Blo 1020604 2494013 := bbase (se 3 (by rfl) ⟨467627, by rfl⟩ : syracuseStep 2494013 = 935255) (by norm_num)
theorem B1150537 : Blo 1020604 1150537 := bbase (se 2 (by rfl) ⟨431451, by rfl⟩ : syracuseStep 1150537 = 862903) (by norm_num)
theorem B2297429 : Blo 1020604 2297429 := bbase (se 8 (by rfl) ⟨13461, by rfl⟩ : syracuseStep 2297429 = 26923) (by norm_num)
theorem B1150573 : Blo 1020604 1150573 := bbase (se 3 (by rfl) ⟨215732, by rfl⟩ : syracuseStep 1150573 = 431465) (by norm_num)
theorem B2625149 : Blo 1020604 2625149 := bbase (se 3 (by rfl) ⟨492215, by rfl⟩ : syracuseStep 2625149 = 984431) (by norm_num)
theorem B1150609 : Blo 1020604 1150609 := bbase (se 2 (by rfl) ⟨431478, by rfl⟩ : syracuseStep 1150609 = 862957) (by norm_num)
theorem B2297501 : Blo 1020604 2297501 := bbase (se 3 (by rfl) ⟨430781, by rfl⟩ : syracuseStep 2297501 = 861563) (by norm_num)
theorem B1150645 : Blo 1020604 1150645 := bbase (se 5 (by rfl) ⟨53936, by rfl⟩ : syracuseStep 1150645 = 107873) (by norm_num)
theorem B2592445 : Blo 1020604 2592445 := bbase (se 3 (by rfl) ⟨486083, by rfl⟩ : syracuseStep 2592445 = 972167) (by norm_num)
theorem B1150681 : Blo 1020604 1150681 := bbase (se 2 (by rfl) ⟨431505, by rfl⟩ : syracuseStep 1150681 = 863011) (by norm_num)
theorem B2297573 : Blo 1020604 2297573 := bbase (se 4 (by rfl) ⟨215397, by rfl⟩ : syracuseStep 2297573 = 430795) (by norm_num)
theorem B4361957 : Blo 1020604 4361957 := bbase (se 4 (by rfl) ⟨408933, by rfl⟩ : syracuseStep 4361957 = 817867) (by norm_num)
theorem B5672693 : Blo 1020604 5672693 := bbase (se 5 (by rfl) ⟨265907, by rfl⟩ : syracuseStep 5672693 = 531815) (by norm_num)
theorem B1150717 : Blo 1020604 1150717 := bbase (se 3 (by rfl) ⟨215759, by rfl⟩ : syracuseStep 1150717 = 431519) (by norm_num)
theorem B1150753 : Blo 1020604 1150753 := bbase (se 2 (by rfl) ⟨431532, by rfl⟩ : syracuseStep 1150753 = 863065) (by norm_num)
theorem B2297645 : Blo 1020604 2297645 := bbase (se 3 (by rfl) ⟨430808, by rfl⟩ : syracuseStep 2297645 = 861617) (by norm_num)
theorem B2592557 : Blo 1020604 2592557 := bbase (se 3 (by rfl) ⟨486104, by rfl⟩ : syracuseStep 2592557 = 972209) (by norm_num)
theorem B2330437 : Blo 1020604 2330437 := bbase (se 4 (by rfl) ⟨218478, by rfl⟩ : syracuseStep 2330437 = 436957) (by norm_num)
theorem B1150789 : Blo 1020604 1150789 := bbase (se 4 (by rfl) ⟨107886, by rfl⟩ : syracuseStep 1150789 = 215773) (by norm_num)
theorem B1183577 : Blo 1020604 1183577 := bbase (se 2 (by rfl) ⟨443841, by rfl⟩ : syracuseStep 1183577 = 887683) (by norm_num)
theorem B1150825 : Blo 1020604 1150825 := bbase (se 2 (by rfl) ⟨431559, by rfl⟩ : syracuseStep 1150825 = 863119) (by norm_num)
theorem B2461549 : Blo 1020604 2461549 := bbase (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) (by norm_num)
theorem B2297717 : Blo 1020604 2297717 := bbase (se 5 (by rfl) ⟨107705, by rfl⟩ : syracuseStep 2297717 = 215411) (by norm_num)
theorem B1150861 : Blo 1020604 1150861 := bbase (se 3 (by rfl) ⟨215786, by rfl⟩ : syracuseStep 1150861 = 431573) (by norm_num)
theorem B1150897 : Blo 1020604 1150897 := bbase (se 2 (by rfl) ⟨431586, by rfl⟩ : syracuseStep 1150897 = 863173) (by norm_num)
theorem B2297789 : Blo 1020604 2297789 := bbase (se 3 (by rfl) ⟨430835, by rfl⟩ : syracuseStep 2297789 = 861671) (by norm_num)
theorem B1150933 : Blo 1020604 1150933 := bbase (se 7 (by rfl) ⟨13487, by rfl⟩ : syracuseStep 1150933 = 26975) (by norm_num)
theorem B2592749 : Blo 1020604 2592749 := bbase (se 3 (by rfl) ⟨486140, by rfl⟩ : syracuseStep 2592749 = 972281) (by norm_num)
theorem B1150969 : Blo 1020604 1150969 := bbase (se 2 (by rfl) ⟨431613, by rfl⟩ : syracuseStep 1150969 = 863227) (by norm_num)
theorem B4362245 : Blo 1020604 4362245 := bbase (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) (by norm_num)
theorem B2297861 : Blo 1020604 2297861 := bbase (se 4 (by rfl) ⟨215424, by rfl⟩ : syracuseStep 2297861 = 430849) (by norm_num)
theorem B1151005 : Blo 1020604 1151005 := bbase (se 3 (by rfl) ⟨215813, by rfl⟩ : syracuseStep 1151005 = 431627) (by norm_num)
theorem B1151041 : Blo 1020604 1151041 := bbase (se 2 (by rfl) ⟨431640, by rfl⟩ : syracuseStep 1151041 = 863281) (by norm_num)
theorem B2297933 : Blo 1020604 2297933 := bbase (se 3 (by rfl) ⟨430862, by rfl⟩ : syracuseStep 2297933 = 861725) (by norm_num)
theorem B3444821 : Blo 1020604 3444821 := bbase (se 8 (by rfl) ⟨20184, by rfl⟩ : syracuseStep 3444821 = 40369) (by norm_num)
theorem B1151077 : Blo 1020604 1151077 := bbase (se 4 (by rfl) ⟨107913, by rfl⟩ : syracuseStep 1151077 = 215827) (by norm_num)
theorem B1151113 : Blo 1020604 1151113 := bbase (se 2 (by rfl) ⟨431667, by rfl⟩ : syracuseStep 1151113 = 863335) (by norm_num)
theorem B2330765 : Blo 1020604 2330765 := bbase (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) (by norm_num)
theorem B2298005 : Blo 1020604 2298005 := bbase (se 6 (by rfl) ⟨53859, by rfl⟩ : syracuseStep 2298005 = 107719) (by norm_num)
theorem B1151149 : Blo 1020604 1151149 := bbase (se 3 (by rfl) ⟨215840, by rfl⟩ : syracuseStep 1151149 = 431681) (by norm_num)
theorem B4657333 : Blo 1020604 4657333 := bbase (se 5 (by rfl) ⟨218312, by rfl⟩ : syracuseStep 4657333 = 436625) (by norm_num)
theorem B1151185 : Blo 1020604 1151185 := bbase (se 2 (by rfl) ⟨431694, by rfl⟩ : syracuseStep 1151185 = 863389) (by norm_num)
theorem B1937621 : Blo 1020604 1937621 := bbase (se 7 (by rfl) ⟨22706, by rfl⟩ : syracuseStep 1937621 = 45413) (by norm_num)
theorem B2298077 : Blo 1020604 2298077 := bbase (se 3 (by rfl) ⟨430889, by rfl⟩ : syracuseStep 2298077 = 861779) (by norm_num)
theorem B1151221 : Blo 1020604 1151221 := bbase (se 5 (by rfl) ⟨53963, by rfl⟩ : syracuseStep 1151221 = 107927) (by norm_num)
theorem B1151257 : Blo 1020604 1151257 := bbase (se 2 (by rfl) ⟨431721, by rfl⟩ : syracuseStep 1151257 = 863443) (by norm_num)
theorem B2298149 : Blo 1020604 2298149 := bbase (se 4 (by rfl) ⟨215451, by rfl⟩ : syracuseStep 2298149 = 430903) (by norm_num)
theorem B1151293 : Blo 1020604 1151293 := bbase (se 3 (by rfl) ⟨215867, by rfl⟩ : syracuseStep 1151293 = 431735) (by norm_num)
theorem B2593093 : Blo 1020604 2593093 := bbase (se 4 (by rfl) ⟨243102, by rfl⟩ : syracuseStep 2593093 = 486205) (by norm_num)
theorem B1151329 : Blo 1020604 1151329 := bbase (se 2 (by rfl) ⟨431748, by rfl⟩ : syracuseStep 1151329 = 863497) (by norm_num)
theorem B1937773 : Blo 1020604 1937773 := bbase (se 3 (by rfl) ⟨363332, by rfl⟩ : syracuseStep 1937773 = 726665) (by norm_num)
theorem B2298221 : Blo 1020604 2298221 := bbase (se 3 (by rfl) ⟨430916, by rfl⟩ : syracuseStep 2298221 = 861833) (by norm_num)
theorem B1151365 : Blo 1020604 1151365 := bbase (se 4 (by rfl) ⟨107940, by rfl⟩ : syracuseStep 1151365 = 215881) (by norm_num)
theorem B1151401 : Blo 1020604 1151401 := bbase (se 2 (by rfl) ⟨431775, by rfl⟩ : syracuseStep 1151401 = 863551) (by norm_num)
theorem B2298293 : Blo 1020604 2298293 := bbase (se 5 (by rfl) ⟨107732, by rfl⟩ : syracuseStep 2298293 = 215465) (by norm_num)
theorem B2593205 : Blo 1020604 2593205 := bbase (se 5 (by rfl) ⟨121556, by rfl⟩ : syracuseStep 2593205 = 243113) (by norm_num)
theorem B5181893 : Blo 1020604 5181893 := bbase (se 4 (by rfl) ⟨485802, by rfl⟩ : syracuseStep 5181893 = 971605) (by norm_num)
theorem B1151437 : Blo 1020604 1151437 := bbase (se 3 (by rfl) ⟨215894, by rfl⟩ : syracuseStep 1151437 = 431789) (by norm_num)
theorem B1151473 : Blo 1020604 1151473 := bbase (se 2 (by rfl) ⟨431802, by rfl⟩ : syracuseStep 1151473 = 863605) (by norm_num)
theorem B2298365 : Blo 1020604 2298365 := bbase (se 3 (by rfl) ⟨430943, by rfl⟩ : syracuseStep 2298365 = 861887) (by norm_num)
theorem B3445253 : Blo 1020604 3445253 := bbase (se 4 (by rfl) ⟨322992, by rfl⟩ : syracuseStep 3445253 = 645985) (by norm_num)
theorem B1151509 : Blo 1020604 1151509 := bbase (se 6 (by rfl) ⟨26988, by rfl⟩ : syracuseStep 1151509 = 53977) (by norm_num)
theorem B1151545 : Blo 1020604 1151545 := bbase (se 2 (by rfl) ⟨431829, by rfl⟩ : syracuseStep 1151545 = 863659) (by norm_num)
theorem B2298437 : Blo 1020604 2298437 := bbase (se 4 (by rfl) ⟨215478, by rfl⟩ : syracuseStep 2298437 = 430957) (by norm_num)
theorem B1151581 : Blo 1020604 1151581 := bbase (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) (by norm_num)
theorem B2593397 : Blo 1020604 2593397 := bbase (se 5 (by rfl) ⟨121565, by rfl⟩ : syracuseStep 2593397 = 243131) (by norm_num)
theorem B1151617 : Blo 1020604 1151617 := bbase (se 2 (by rfl) ⟨431856, by rfl⟩ : syracuseStep 1151617 = 863713) (by norm_num)
theorem B2298509 : Blo 1020604 2298509 := bbase (se 3 (by rfl) ⟨430970, by rfl⟩ : syracuseStep 2298509 = 861941) (by norm_num)
theorem B1938077 : Blo 1020604 1938077 := bbase (se 3 (by rfl) ⟨363389, by rfl⟩ : syracuseStep 1938077 = 726779) (by norm_num)
theorem B1151653 : Blo 1020604 1151653 := bbase (se 4 (by rfl) ⟨107967, by rfl⟩ : syracuseStep 1151653 = 215935) (by norm_num)
theorem B1151689 : Blo 1020604 1151689 := bbase (se 2 (by rfl) ⟨431883, by rfl⟩ : syracuseStep 1151689 = 863767) (by norm_num)
theorem B2298581 : Blo 1020604 2298581 := bbase (se 7 (by rfl) ⟨26936, by rfl⟩ : syracuseStep 2298581 = 53873) (by norm_num)
theorem B1151725 : Blo 1020604 1151725 := bbase (se 3 (by rfl) ⟨215948, by rfl⟩ : syracuseStep 1151725 = 431897) (by norm_num)
theorem B4362997 : Blo 1020604 4362997 := bbase (se 5 (by rfl) ⟨204515, by rfl⟩ : syracuseStep 4362997 = 409031) (by norm_num)
theorem B1151761 : Blo 1020604 1151761 := bbase (se 2 (by rfl) ⟨431910, by rfl⟩ : syracuseStep 1151761 = 863821) (by norm_num)
theorem B2298653 : Blo 1020604 2298653 := bbase (se 3 (by rfl) ⟨430997, by rfl⟩ : syracuseStep 2298653 = 861995) (by norm_num)
theorem B1151797 : Blo 1020604 1151797 := bbase (se 5 (by rfl) ⟨53990, by rfl⟩ : syracuseStep 1151797 = 107981) (by norm_num)
theorem B1151833 : Blo 1020604 1151833 := bbase (se 2 (by rfl) ⟨431937, by rfl⟩ : syracuseStep 1151833 = 863875) (by norm_num)
theorem B2298725 : Blo 1020604 2298725 := bbase (se 4 (by rfl) ⟨215505, by rfl⟩ : syracuseStep 2298725 = 431011) (by norm_num)
theorem B1151869 : Blo 1020604 1151869 := bbase (se 3 (by rfl) ⟨215975, by rfl⟩ : syracuseStep 1151869 = 431951) (by norm_num)
theorem B1151905 : Blo 1020604 1151905 := bbase (se 2 (by rfl) ⟨431964, by rfl⟩ : syracuseStep 1151905 = 863929) (by norm_num)
theorem B2298797 : Blo 1020604 2298797 := bbase (se 3 (by rfl) ⟨431024, by rfl⟩ : syracuseStep 2298797 = 862049) (by norm_num)
theorem B3445685 : Blo 1020604 3445685 := bbase (se 5 (by rfl) ⟨161516, by rfl⟩ : syracuseStep 3445685 = 323033) (by norm_num)
theorem B1151941 : Blo 1020604 1151941 := bbase (se 4 (by rfl) ⟨107994, by rfl⟩ : syracuseStep 1151941 = 215989) (by norm_num)
theorem B1151977 : Blo 1020604 1151977 := bbase (se 2 (by rfl) ⟨431991, by rfl⟩ : syracuseStep 1151977 = 863983) (by norm_num)
theorem B1577965 : Blo 1020604 1577965 := bbase (se 3 (by rfl) ⟨295868, by rfl⟩ : syracuseStep 1577965 = 591737) (by norm_num)
theorem B2298869 : Blo 1020604 2298869 := bbase (se 5 (by rfl) ⟨107759, by rfl⟩ : syracuseStep 2298869 = 215519) (by norm_num)
theorem B1152013 : Blo 1020604 1152013 := bbase (se 3 (by rfl) ⟨216002, by rfl⟩ : syracuseStep 1152013 = 432005) (by norm_num)
theorem B1381421 : Blo 1020604 1381421 := bbase (se 3 (by rfl) ⟨259016, by rfl⟩ : syracuseStep 1381421 = 518033) (by norm_num)
theorem B1152049 : Blo 1020604 1152049 := bbase (se 2 (by rfl) ⟨432018, by rfl⟩ : syracuseStep 1152049 = 864037) (by norm_num)
theorem B2298941 : Blo 1020604 2298941 := bbase (se 3 (by rfl) ⟨431051, by rfl⟩ : syracuseStep 2298941 = 862103) (by norm_num)
theorem B1152085 : Blo 1020604 1152085 := bbase (se 8 (by rfl) ⟨6750, by rfl⟩ : syracuseStep 1152085 = 13501) (by norm_num)
theorem B2528365 : Blo 1020604 2528365 := bbase (se 3 (by rfl) ⟨474068, by rfl⟩ : syracuseStep 2528365 = 948137) (by norm_num)
theorem B1152121 : Blo 1020604 1152121 := bbase (se 2 (by rfl) ⟨432045, by rfl⟩ : syracuseStep 1152121 = 864091) (by norm_num)
theorem B2299013 : Blo 1020604 2299013 := bbase (se 4 (by rfl) ⟨215532, by rfl⟩ : syracuseStep 2299013 = 431065) (by norm_num)
theorem B1152157 : Blo 1020604 1152157 := bbase (se 3 (by rfl) ⟨216029, by rfl⟩ : syracuseStep 1152157 = 432059) (by norm_num)
theorem B1152193 : Blo 1020604 1152193 := bbase (se 2 (by rfl) ⟨432072, by rfl⟩ : syracuseStep 1152193 = 864145) (by norm_num)
theorem B2299085 : Blo 1020604 2299085 := bbase (se 3 (by rfl) ⟨431078, by rfl⟩ : syracuseStep 2299085 = 862157) (by norm_num)
theorem B1152229 : Blo 1020604 1152229 := bbase (se 4 (by rfl) ⟨108021, by rfl⟩ : syracuseStep 1152229 = 216043) (by norm_num)
theorem B1152265 : Blo 1020604 1152265 := bbase (se 2 (by rfl) ⟨432099, by rfl⟩ : syracuseStep 1152265 = 864199) (by norm_num)
theorem B2299157 : Blo 1020604 2299157 := bbase (se 6 (by rfl) ⟨53886, by rfl⟩ : syracuseStep 2299157 = 107773) (by norm_num)
theorem B1152301 : Blo 1020604 1152301 := bbase (se 3 (by rfl) ⟨216056, by rfl⟩ : syracuseStep 1152301 = 432113) (by norm_num)
theorem B2069813 : Blo 1020604 2069813 := bbase (se 5 (by rfl) ⟨97022, by rfl⟩ : syracuseStep 2069813 = 194045) (by norm_num)
theorem B5051717 : Blo 1020604 5051717 := bbase (se 4 (by rfl) ⟨473598, by rfl⟩ : syracuseStep 5051717 = 947197) (by norm_num)
theorem B1152337 : Blo 1020604 1152337 := bbase (se 2 (by rfl) ⟨432126, by rfl⟩ : syracuseStep 1152337 = 864253) (by norm_num)
theorem B2299229 : Blo 1020604 2299229 := bbase (se 3 (by rfl) ⟨431105, by rfl⟩ : syracuseStep 2299229 = 862211) (by norm_num)
theorem B3446117 : Blo 1020604 3446117 := bbase (se 4 (by rfl) ⟨323073, by rfl⟩ : syracuseStep 3446117 = 646147) (by norm_num)
theorem B1152373 : Blo 1020604 1152373 := bbase (se 5 (by rfl) ⟨54017, by rfl⟩ : syracuseStep 1152373 = 108035) (by norm_num)
theorem B1938829 : Blo 1020604 1938829 := bbase (se 3 (by rfl) ⟨363530, by rfl⟩ : syracuseStep 1938829 = 727061) (by norm_num)
theorem B1152409 : Blo 1020604 1152409 := bbase (se 2 (by rfl) ⟨432153, by rfl⟩ : syracuseStep 1152409 = 864307) (by norm_num)
theorem B2299301 : Blo 1020604 2299301 := bbase (se 4 (by rfl) ⟨215559, by rfl⟩ : syracuseStep 2299301 = 431119) (by norm_num)
theorem B1152445 : Blo 1020604 1152445 := bbase (se 3 (by rfl) ⟨216083, by rfl⟩ : syracuseStep 1152445 = 432167) (by norm_num)
theorem B4363733 : Blo 1020604 4363733 := bbase (se 7 (by rfl) ⟨51137, by rfl⟩ : syracuseStep 4363733 = 102275) (by norm_num)
theorem B1152481 : Blo 1020604 1152481 := bbase (se 2 (by rfl) ⟨432180, by rfl⟩ : syracuseStep 1152481 = 864361) (by norm_num)
theorem B2299373 : Blo 1020604 2299373 := bbase (se 3 (by rfl) ⟨431132, by rfl⟩ : syracuseStep 2299373 = 862265) (by norm_num)
theorem B1381885 : Blo 1020604 1381885 := bbase (se 3 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 1381885 = 518207) (by norm_num)
theorem B1152517 : Blo 1020604 1152517 := bbase (se 4 (by rfl) ⟨108048, by rfl⟩ : syracuseStep 1152517 = 216097) (by norm_num)
theorem B3282437 : Blo 1020604 3282437 := bbase (se 4 (by rfl) ⟨307728, by rfl⟩ : syracuseStep 3282437 = 615457) (by norm_num)
theorem B1938973 : Blo 1020604 1938973 := bbase (se 3 (by rfl) ⟨363557, by rfl⟩ : syracuseStep 1938973 = 727115) (by norm_num)
theorem B1152553 : Blo 1020604 1152553 := bbase (se 2 (by rfl) ⟨432207, by rfl⟩ : syracuseStep 1152553 = 864415) (by norm_num)
theorem B2299445 : Blo 1020604 2299445 := bbase (se 5 (by rfl) ⟨107786, by rfl⟩ : syracuseStep 2299445 = 215573) (by norm_num)
theorem B1152589 : Blo 1020604 1152589 := bbase (se 3 (by rfl) ⟨216110, by rfl⟩ : syracuseStep 1152589 = 432221) (by norm_num)
theorem B1152625 : Blo 1020604 1152625 := bbase (se 2 (by rfl) ⟨432234, by rfl⟩ : syracuseStep 1152625 = 864469) (by norm_num)
theorem B2299517 : Blo 1020604 2299517 := bbase (se 3 (by rfl) ⟨431159, by rfl⟩ : syracuseStep 2299517 = 862319) (by norm_num)
theorem B1152661 : Blo 1020604 1152661 := bbase (se 6 (by rfl) ⟨27015, by rfl⟩ : syracuseStep 1152661 = 54031) (by norm_num)
theorem B1939133 : Blo 1020604 1939133 := bbase (se 3 (by rfl) ⟨363587, by rfl⟩ : syracuseStep 1939133 = 727175) (by norm_num)
theorem B2299589 : Blo 1020604 2299589 := bbase (se 4 (by rfl) ⟨215586, by rfl⟩ : syracuseStep 2299589 = 431173) (by norm_num)
theorem B5183189 : Blo 1020604 5183189 := bbase (se 7 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 5183189 = 121481) (by norm_num)
theorem B2299661 : Blo 1020604 2299661 := bbase (se 3 (by rfl) ⟨431186, by rfl⟩ : syracuseStep 2299661 = 862373) (by norm_num)
theorem B3446549 : Blo 1020604 3446549 := bbase (se 6 (by rfl) ⟨80778, by rfl⟩ : syracuseStep 3446549 = 161557) (by norm_num)
theorem B1939277 : Blo 1020604 1939277 := bbase (se 3 (by rfl) ⟨363614, by rfl⟩ : syracuseStep 1939277 = 727229) (by norm_num)
theorem B2299733 : Blo 1020604 2299733 := bbase (se 9 (by rfl) ⟨6737, by rfl⟩ : syracuseStep 2299733 = 13475) (by norm_num)
theorem B2299805 : Blo 1020604 2299805 := bbase (se 3 (by rfl) ⟨431213, by rfl⟩ : syracuseStep 2299805 = 862427) (by norm_num)
theorem B13277141 : Blo 1020604 13277141 := bbase (se 7 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 13277141 = 311183) (by norm_num)
theorem B2299877 : Blo 1020604 2299877 := bbase (se 4 (by rfl) ⟨215613, by rfl⟩ : syracuseStep 2299877 = 431227) (by norm_num)
theorem B2299949 : Blo 1020604 2299949 := bbase (se 3 (by rfl) ⟨431240, by rfl⟩ : syracuseStep 2299949 = 862481) (by norm_num)
theorem B8296501 : Blo 1020604 8296501 := bbase (se 5 (by rfl) ⟨388898, by rfl⟩ : syracuseStep 8296501 = 777797) (by norm_num)
theorem B2627653 : Blo 1020604 2627653 := bbase (se 4 (by rfl) ⟨246342, by rfl⟩ : syracuseStep 2627653 = 492685) (by norm_num)
theorem B1939565 : Blo 1020604 1939565 := bbase (se 3 (by rfl) ⟨363668, by rfl⟩ : syracuseStep 1939565 = 727337) (by norm_num)
theorem B2300021 : Blo 1020604 2300021 := bbase (se 5 (by rfl) ⟨107813, by rfl⟩ : syracuseStep 2300021 = 215627) (by norm_num)
theorem B2300093 : Blo 1020604 2300093 := bbase (se 3 (by rfl) ⟨431267, by rfl⟩ : syracuseStep 2300093 = 862535) (by norm_num)
theorem B3446981 : Blo 1020604 3446981 := bbase (se 4 (by rfl) ⟨323154, by rfl⟩ : syracuseStep 3446981 = 646309) (by norm_num)
theorem B1939717 : Blo 1020604 1939717 := bbase (se 4 (by rfl) ⟨181848, by rfl⟩ : syracuseStep 1939717 = 363697) (by norm_num)
theorem B2300165 : Blo 1020604 2300165 := bbase (se 4 (by rfl) ⟨215640, by rfl⟩ : syracuseStep 2300165 = 431281) (by norm_num)
theorem B2300237 : Blo 1020604 2300237 := bbase (se 3 (by rfl) ⟨431294, by rfl⟩ : syracuseStep 2300237 = 862589) (by norm_num)
theorem B1382789 : Blo 1020604 1382789 := bbase (se 4 (by rfl) ⟨129636, by rfl⟩ : syracuseStep 1382789 = 259273) (by norm_num)
theorem B2300309 : Blo 1020604 2300309 := bbase (se 6 (by rfl) ⟨53913, by rfl⟩ : syracuseStep 2300309 = 107827) (by norm_num)
theorem B7772597 : Blo 1020604 7772597 := bbase (se 5 (by rfl) ⟨364340, by rfl⟩ : syracuseStep 7772597 = 728681) (by norm_num)
theorem B1382837 : Blo 1020604 1382837 := bbase (se 5 (by rfl) ⟨64820, by rfl⟩ : syracuseStep 1382837 = 129641) (by norm_num)
theorem B2300381 : Blo 1020604 2300381 := bbase (se 3 (by rfl) ⟨431321, by rfl⟩ : syracuseStep 2300381 = 862643) (by norm_num)
theorem B4921829 : Blo 1020604 4921829 := bbase (se 4 (by rfl) ⟨461421, by rfl⟩ : syracuseStep 4921829 = 922843) (by norm_num)
theorem B2300453 : Blo 1020604 2300453 := bbase (se 4 (by rfl) ⟨215667, by rfl⟩ : syracuseStep 2300453 = 431335) (by norm_num)
theorem B1940021 : Blo 1020604 1940021 := bbase (se 5 (by rfl) ⟨90938, by rfl⟩ : syracuseStep 1940021 = 181877) (by norm_num)
theorem B1382989 : Blo 1020604 1382989 := bbase (se 3 (by rfl) ⟨259310, by rfl⟩ : syracuseStep 1382989 = 518621) (by norm_num)
theorem B2300525 : Blo 1020604 2300525 := bbase (se 3 (by rfl) ⟨431348, by rfl⟩ : syracuseStep 2300525 = 862697) (by norm_num)
theorem B3447413 : Blo 1020604 3447413 := bbase (se 5 (by rfl) ⟨161597, by rfl⟩ : syracuseStep 3447413 = 323195) (by norm_num)
theorem B2333357 : Blo 1020604 2333357 := bbase (se 3 (by rfl) ⟨437504, by rfl⟩ : syracuseStep 2333357 = 875009) (by norm_num)
theorem B2300597 : Blo 1020604 2300597 := bbase (se 5 (by rfl) ⟨107840, by rfl⟩ : syracuseStep 2300597 = 215681) (by norm_num)
theorem B2300669 : Blo 1020604 2300669 := bbase (se 3 (by rfl) ⟨431375, by rfl⟩ : syracuseStep 2300669 = 862751) (by norm_num)
theorem B4922117 : Blo 1020604 4922117 := bbase (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) (by norm_num)
theorem B2300741 : Blo 1020604 2300741 := bbase (se 4 (by rfl) ⟨215694, by rfl⟩ : syracuseStep 2300741 = 431389) (by norm_num)
theorem B1383269 : Blo 1020604 1383269 := bbase (se 4 (by rfl) ⟨129681, by rfl⟩ : syracuseStep 1383269 = 259363) (by norm_num)
theorem B2300813 : Blo 1020604 2300813 := bbase (se 3 (by rfl) ⟨431402, by rfl⟩ : syracuseStep 2300813 = 862805) (by norm_num)
theorem B2300885 : Blo 1020604 2300885 := bbase (se 7 (by rfl) ⟨26963, by rfl⟩ : syracuseStep 2300885 = 53927) (by norm_num)
theorem B5184485 : Blo 1020604 5184485 := bbase (se 4 (by rfl) ⟨486045, by rfl⟩ : syracuseStep 5184485 = 972091) (by norm_num)
theorem B2300957 : Blo 1020604 2300957 := bbase (se 3 (by rfl) ⟨431429, by rfl⟩ : syracuseStep 2300957 = 862859) (by norm_num)
theorem B3447845 : Blo 1020604 3447845 := bbase (se 4 (by rfl) ⟨323235, by rfl⟩ : syracuseStep 3447845 = 646471) (by norm_num)
theorem B2071613 : Blo 1020604 2071613 := bbase (se 3 (by rfl) ⟨388427, by rfl⟩ : syracuseStep 2071613 = 776855) (by norm_num)
theorem B2301029 : Blo 1020604 2301029 := bbase (se 4 (by rfl) ⟨215721, by rfl⟩ : syracuseStep 2301029 = 431443) (by norm_num)
theorem B2301101 : Blo 1020604 2301101 := bbase (se 3 (by rfl) ⟨431456, by rfl⟩ : syracuseStep 2301101 = 862913) (by norm_num)
theorem B2301173 : Blo 1020604 2301173 := bbase (se 5 (by rfl) ⟨107867, by rfl⟩ : syracuseStep 2301173 = 215735) (by norm_num)
theorem B1940773 : Blo 1020604 1940773 := bbase (se 4 (by rfl) ⟨181947, by rfl⟩ : syracuseStep 1940773 = 363895) (by norm_num)
theorem B1842485 : Blo 1020604 1842485 := bbase (se 5 (by rfl) ⟨86366, by rfl⟩ : syracuseStep 1842485 = 172733) (by norm_num)
theorem B2301245 : Blo 1020604 2301245 := bbase (se 3 (by rfl) ⟨431483, by rfl⟩ : syracuseStep 2301245 = 862967) (by norm_num)
theorem B2301317 : Blo 1020604 2301317 := bbase (se 4 (by rfl) ⟨215748, by rfl⟩ : syracuseStep 2301317 = 431497) (by norm_num)
theorem B2956709 : Blo 1020604 2956709 := bbase (se 4 (by rfl) ⟨277191, by rfl⟩ : syracuseStep 2956709 = 554383) (by norm_num)
theorem B1940917 : Blo 1020604 1940917 := bbase (se 5 (by rfl) ⟨90980, by rfl⟩ : syracuseStep 1940917 = 181961) (by norm_num)
theorem B2301389 : Blo 1020604 2301389 := bbase (se 3 (by rfl) ⟨431510, by rfl⟩ : syracuseStep 2301389 = 863021) (by norm_num)
theorem B3448277 : Blo 1020604 3448277 := bbase (se 7 (by rfl) ⟨40409, by rfl⟩ : syracuseStep 3448277 = 80819) (by norm_num)
theorem B2301461 : Blo 1020604 2301461 := bbase (se 6 (by rfl) ⟨53940, by rfl⟩ : syracuseStep 2301461 = 107881) (by norm_num)
theorem B1941077 : Blo 1020604 1941077 := bbase (se 8 (by rfl) ⟨11373, by rfl⟩ : syracuseStep 1941077 = 22747) (by norm_num)
theorem B2301533 : Blo 1020604 2301533 := bbase (se 3 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 2301533 = 863075) (by norm_num)
theorem B2301605 : Blo 1020604 2301605 := bbase (se 4 (by rfl) ⟨215775, by rfl⟩ : syracuseStep 2301605 = 431551) (by norm_num)
theorem B9313973 : Blo 1020604 9313973 := bbase (se 5 (by rfl) ⟨436592, by rfl⟩ : syracuseStep 9313973 = 873185) (by norm_num)
theorem B1941221 : Blo 1020604 1941221 := bbase (se 4 (by rfl) ⟨181989, by rfl⟩ : syracuseStep 1941221 = 363979) (by norm_num)
theorem B2301677 : Blo 1020604 2301677 := bbase (se 3 (by rfl) ⟨431564, by rfl⟩ : syracuseStep 2301677 = 863129) (by norm_num)
theorem B2072309 : Blo 1020604 2072309 := bbase (se 5 (by rfl) ⟨97139, by rfl⟩ : syracuseStep 2072309 = 194279) (by norm_num)
theorem B2301749 : Blo 1020604 2301749 := bbase (se 5 (by rfl) ⟨107894, by rfl⟩ : syracuseStep 2301749 = 215789) (by norm_num)
theorem B2301821 : Blo 1020604 2301821 := bbase (se 3 (by rfl) ⟨431591, by rfl⟩ : syracuseStep 2301821 = 863183) (by norm_num)
theorem B3448709 : Blo 1020604 3448709 := bbase (se 4 (by rfl) ⟨323316, by rfl⟩ : syracuseStep 3448709 = 646633) (by norm_num)
theorem B2662301 : Blo 1020604 2662301 := bbase (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) (by norm_num)
theorem B3317701 : Blo 1020604 3317701 := bbase (se 4 (by rfl) ⟨311034, by rfl⟩ : syracuseStep 3317701 = 622069) (by norm_num)
theorem B2301893 : Blo 1020604 2301893 := bbase (se 4 (by rfl) ⟨215802, by rfl⟩ : syracuseStep 2301893 = 431605) (by norm_num)
theorem B1941509 : Blo 1020604 1941509 := bbase (se 4 (by rfl) ⟨182016, by rfl⟩ : syracuseStep 1941509 = 364033) (by norm_num)
theorem B2301965 : Blo 1020604 2301965 := bbase (se 3 (by rfl) ⟨431618, by rfl⟩ : syracuseStep 2301965 = 863237) (by norm_num)
theorem B2302037 : Blo 1020604 2302037 := bbase (se 8 (by rfl) ⟨13488, by rfl⟩ : syracuseStep 2302037 = 26977) (by norm_num)
theorem B2334845 : Blo 1020604 2334845 := bbase (se 3 (by rfl) ⟨437783, by rfl⟩ : syracuseStep 2334845 = 875567) (by norm_num)
theorem B1941661 : Blo 1020604 1941661 := bbase (se 3 (by rfl) ⟨364061, by rfl⟩ : syracuseStep 1941661 = 728123) (by norm_num)
theorem B2302109 : Blo 1020604 2302109 := bbase (se 3 (by rfl) ⟨431645, by rfl⟩ : syracuseStep 2302109 = 863291) (by norm_num)
theorem B2302181 : Blo 1020604 2302181 := bbase (se 4 (by rfl) ⟨215829, by rfl⟩ : syracuseStep 2302181 = 431659) (by norm_num)
theorem B10494197 : Blo 1020604 10494197 := bbase (se 5 (by rfl) ⟨491915, by rfl⟩ : syracuseStep 10494197 = 983831) (by norm_num)
theorem B5185781 : Blo 1020604 5185781 := bbase (se 5 (by rfl) ⟨243083, by rfl⟩ : syracuseStep 5185781 = 486167) (by norm_num)
theorem B2302253 : Blo 1020604 2302253 := bbase (se 3 (by rfl) ⟨431672, by rfl⟩ : syracuseStep 2302253 = 863345) (by norm_num)
theorem B3449141 : Blo 1020604 3449141 := bbase (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) (by norm_num)
theorem B2302325 : Blo 1020604 2302325 := bbase (se 5 (by rfl) ⟨107921, by rfl⟩ : syracuseStep 2302325 = 215843) (by norm_num)
theorem B2302397 : Blo 1020604 2302397 := bbase (se 3 (by rfl) ⟨431699, by rfl⟩ : syracuseStep 2302397 = 863399) (by norm_num)
theorem B1941965 : Blo 1020604 1941965 := bbase (se 3 (by rfl) ⟨364118, by rfl⟩ : syracuseStep 1941965 = 728237) (by norm_num)
theorem B1090045 : Blo 1020604 1090045 := bbase (se 3 (by rfl) ⟨204383, by rfl⟩ : syracuseStep 1090045 = 408767) (by norm_num)
theorem B2302469 : Blo 1020604 2302469 := bbase (se 4 (by rfl) ⟨215856, by rfl⟩ : syracuseStep 2302469 = 431713) (by norm_num)
theorem B2433557 : Blo 1020604 2433557 := bbase (se 6 (by rfl) ⟨57036, by rfl⟩ : syracuseStep 2433557 = 114073) (by norm_num)
theorem B1090117 : Blo 1020604 1090117 := bbase (se 4 (by rfl) ⟨102198, by rfl⟩ : syracuseStep 1090117 = 204397) (by norm_num)
theorem B2761285 : Blo 1020604 2761285 := bbase (se 4 (by rfl) ⟨258870, by rfl⟩ : syracuseStep 2761285 = 517741) (by norm_num)
theorem B2302541 : Blo 1020604 2302541 := bbase (se 3 (by rfl) ⟨431726, by rfl⟩ : syracuseStep 2302541 = 863453) (by norm_num)
theorem B2302613 : Blo 1020604 2302613 := bbase (se 6 (by rfl) ⟨53967, by rfl⟩ : syracuseStep 2302613 = 107935) (by norm_num)
theorem B4367029 : Blo 1020604 4367029 := bbase (se 5 (by rfl) ⟨204704, by rfl⟩ : syracuseStep 4367029 = 409409) (by norm_num)
theorem B2302685 : Blo 1020604 2302685 := bbase (se 3 (by rfl) ⟨431753, by rfl⟩ : syracuseStep 2302685 = 863507) (by norm_num)
theorem B3449573 : Blo 1020604 3449573 := bbase (se 4 (by rfl) ⟨323397, by rfl⟩ : syracuseStep 3449573 = 646795) (by norm_num)
theorem B1843949 : Blo 1020604 1843949 := bbase (se 3 (by rfl) ⟨345740, by rfl⟩ : syracuseStep 1843949 = 691481) (by norm_num)
theorem B1090297 : Blo 1020604 1090297 := bbase (se 2 (by rfl) ⟨408861, by rfl⟩ : syracuseStep 1090297 = 817723) (by norm_num)
theorem B2302757 : Blo 1020604 2302757 := bbase (se 4 (by rfl) ⟨215883, by rfl⟩ : syracuseStep 2302757 = 431767) (by norm_num)
theorem B2073413 : Blo 1020604 2073413 := bbase (se 4 (by rfl) ⟨194382, by rfl⟩ : syracuseStep 2073413 = 388765) (by norm_num)
theorem B2302829 : Blo 1020604 2302829 := bbase (se 3 (by rfl) ⟨431780, by rfl⟩ : syracuseStep 2302829 = 863561) (by norm_num)
theorem B2302901 : Blo 1020604 2302901 := bbase (se 5 (by rfl) ⟨107948, by rfl⟩ : syracuseStep 2302901 = 215897) (by norm_num)
theorem B2302973 : Blo 1020604 2302973 := bbase (se 3 (by rfl) ⟨431807, by rfl⟩ : syracuseStep 2302973 = 863615) (by norm_num)
theorem B2303045 : Blo 1020604 2303045 := bbase (se 4 (by rfl) ⟨215910, by rfl⟩ : syracuseStep 2303045 = 431821) (by norm_num)
theorem B3875957 : Blo 1020604 3875957 := bbase (se 5 (by rfl) ⟨181685, by rfl⟩ : syracuseStep 3875957 = 363371) (by norm_num)
theorem B2303117 : Blo 1020604 2303117 := bbase (se 3 (by rfl) ⟨431834, by rfl⟩ : syracuseStep 2303117 = 863669) (by norm_num)
theorem B3450005 : Blo 1020604 3450005 := bbase (se 6 (by rfl) ⟨80859, by rfl⟩ : syracuseStep 3450005 = 161719) (by norm_num)
theorem B1090741 : Blo 1020604 1090741 := bbase (se 5 (by rfl) ⟨51128, by rfl⟩ : syracuseStep 1090741 = 102257) (by norm_num)
theorem B1942717 : Blo 1020604 1942717 := bbase (se 3 (by rfl) ⟨364259, by rfl⟩ : syracuseStep 1942717 = 728519) (by norm_num)
theorem B2303189 : Blo 1020604 2303189 := bbase (se 7 (by rfl) ⟨26990, by rfl⟩ : syracuseStep 2303189 = 53981) (by norm_num)
theorem B2303261 : Blo 1020604 2303261 := bbase (se 3 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 2303261 = 863723) (by norm_num)
theorem B1090865 : Blo 1020604 1090865 := bbase (se 2 (by rfl) ⟨409074, by rfl⟩ : syracuseStep 1090865 = 818149) (by norm_num)
theorem B1942861 : Blo 1020604 1942861 := bbase (se 3 (by rfl) ⟨364286, by rfl⟩ : syracuseStep 1942861 = 728573) (by norm_num)
theorem B1746269 : Blo 1020604 1746269 := bbase (se 3 (by rfl) ⟨327425, by rfl⟩ : syracuseStep 1746269 = 654851) (by norm_num)
theorem B2303333 : Blo 1020604 2303333 := bbase (se 4 (by rfl) ⟨215937, by rfl⟩ : syracuseStep 2303333 = 431875) (by norm_num)
theorem B3876245 : Blo 1020604 3876245 := bbase (se 6 (by rfl) ⟨90849, by rfl⟩ : syracuseStep 3876245 = 181699) (by norm_num)
theorem B2303405 : Blo 1020604 2303405 := bbase (se 3 (by rfl) ⟨431888, by rfl⟩ : syracuseStep 2303405 = 863777) (by norm_num)
theorem B1943021 : Blo 1020604 1943021 := bbase (se 3 (by rfl) ⟨364316, by rfl⟩ : syracuseStep 1943021 = 728633) (by norm_num)
theorem B2303477 : Blo 1020604 2303477 := bbase (se 5 (by rfl) ⟨107975, by rfl⟩ : syracuseStep 2303477 = 215951) (by norm_num)
theorem B1091117 : Blo 1020604 1091117 := bbase (se 3 (by rfl) ⟨204584, by rfl⟩ : syracuseStep 1091117 = 409169) (by norm_num)
theorem B2303549 : Blo 1020604 2303549 := bbase (se 3 (by rfl) ⟨431915, by rfl⟩ : syracuseStep 2303549 = 863831) (by norm_num)
theorem B3450437 : Blo 1020604 3450437 := bbase (se 4 (by rfl) ⟨323478, by rfl⟩ : syracuseStep 3450437 = 646957) (by norm_num)
theorem B1943165 : Blo 1020604 1943165 := bbase (se 3 (by rfl) ⟨364343, by rfl⟩ : syracuseStep 1943165 = 728687) (by norm_num)
theorem B2303621 : Blo 1020604 2303621 := bbase (se 4 (by rfl) ⟨215964, by rfl⟩ : syracuseStep 2303621 = 431929) (by norm_num)
theorem B2303693 : Blo 1020604 2303693 := bbase (se 3 (by rfl) ⟨431942, by rfl⟩ : syracuseStep 2303693 = 863885) (by norm_num)
theorem B2303765 : Blo 1020604 2303765 := bbase (se 6 (by rfl) ⟨53994, by rfl⟩ : syracuseStep 2303765 = 107989) (by norm_num)
theorem B2303837 : Blo 1020604 2303837 := bbase (se 3 (by rfl) ⟨431969, by rfl⟩ : syracuseStep 2303837 = 863939) (by norm_num)
theorem B1845109 : Blo 1020604 1845109 := bbase (se 5 (by rfl) ⟨86489, by rfl⟩ : syracuseStep 1845109 = 172979) (by norm_num)
theorem B1943453 : Blo 1020604 1943453 := bbase (se 3 (by rfl) ⟨364397, by rfl⟩ : syracuseStep 1943453 = 728795) (by norm_num)
theorem B2303909 : Blo 1020604 2303909 := bbase (se 4 (by rfl) ⟨215991, by rfl⟩ : syracuseStep 2303909 = 431983) (by norm_num)
theorem B1091561 : Blo 1020604 1091561 := bbase (se 2 (by rfl) ⟨409335, by rfl⟩ : syracuseStep 1091561 = 818671) (by norm_num)
theorem B2303981 : Blo 1020604 2303981 := bbase (se 3 (by rfl) ⟨431996, by rfl⟩ : syracuseStep 2303981 = 863993) (by norm_num)
theorem B3450869 : Blo 1020604 3450869 := bbase (se 5 (by rfl) ⟨161759, by rfl⟩ : syracuseStep 3450869 = 323519) (by norm_num)
theorem B1943605 : Blo 1020604 1943605 := bbase (se 5 (by rfl) ⟨91106, by rfl⟩ : syracuseStep 1943605 = 182213) (by norm_num)
theorem B2304053 : Blo 1020604 2304053 := bbase (se 5 (by rfl) ⟨108002, by rfl⟩ : syracuseStep 2304053 = 216005) (by norm_num)
theorem B2304125 : Blo 1020604 2304125 := bbase (se 3 (by rfl) ⟨432023, by rfl⟩ : syracuseStep 2304125 = 864047) (by norm_num)
theorem B1845413 : Blo 1020604 1845413 := bbase (se 4 (by rfl) ⟨173007, by rfl⟩ : syracuseStep 1845413 = 346015) (by norm_num)
theorem B1747117 : Blo 1020604 1747117 := bbase (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) (by norm_num)
theorem B2304197 : Blo 1020604 2304197 := bbase (se 4 (by rfl) ⟨216018, by rfl⟩ : syracuseStep 2304197 = 432037) (by norm_num)
theorem B1091809 : Blo 1020604 1091809 := bbase (se 2 (by rfl) ⟨409428, by rfl⟩ : syracuseStep 1091809 = 818857) (by norm_num)
theorem B2304269 : Blo 1020604 2304269 := bbase (se 3 (by rfl) ⟨432050, by rfl⟩ : syracuseStep 2304269 = 864101) (by norm_num)
theorem B2304341 : Blo 1020604 2304341 := bbase (se 10 (by rfl) ⟨3375, by rfl⟩ : syracuseStep 2304341 = 6751) (by norm_num)
theorem B1943909 : Blo 1020604 1943909 := bbase (se 4 (by rfl) ⟨182241, by rfl⟩ : syracuseStep 1943909 = 364483) (by norm_num)
theorem B2304413 : Blo 1020604 2304413 := bbase (se 3 (by rfl) ⟨432077, by rfl⟩ : syracuseStep 2304413 = 864155) (by norm_num)
theorem B3451301 : Blo 1020604 3451301 := bbase (se 4 (by rfl) ⟨323559, by rfl⟩ : syracuseStep 3451301 = 647119) (by norm_num)
theorem B2304485 : Blo 1020604 2304485 := bbase (se 4 (by rfl) ⟨216045, by rfl⟩ : syracuseStep 2304485 = 432091) (by norm_num)
theorem B2304557 : Blo 1020604 2304557 := bbase (se 3 (by rfl) ⟨432104, by rfl⟩ : syracuseStep 2304557 = 864209) (by norm_num)
theorem B3877429 : Blo 1020604 3877429 := bbase (se 5 (by rfl) ⟨181754, by rfl⟩ : syracuseStep 3877429 = 363509) (by norm_num)
theorem B2304629 : Blo 1020604 2304629 := bbase (se 5 (by rfl) ⟨108029, by rfl⟩ : syracuseStep 2304629 = 216059) (by norm_num)
theorem B1092253 : Blo 1020604 1092253 := bbase (se 3 (by rfl) ⟨204797, by rfl⟩ : syracuseStep 1092253 = 409595) (by norm_num)
theorem B2304701 : Blo 1020604 2304701 := bbase (se 3 (by rfl) ⟨432131, by rfl⟩ : syracuseStep 2304701 = 864263) (by norm_num)
theorem B1092313 : Blo 1020604 1092313 := bbase (se 2 (by rfl) ⟨409617, by rfl⟩ : syracuseStep 1092313 = 819235) (by norm_num)
theorem B5253893 : Blo 1020604 5253893 := bbase (se 4 (by rfl) ⟨492552, by rfl⟩ : syracuseStep 5253893 = 985105) (by norm_num)
theorem B2304773 : Blo 1020604 2304773 := bbase (se 4 (by rfl) ⟨216072, by rfl⟩ : syracuseStep 2304773 = 432145) (by norm_num)
theorem B2304845 : Blo 1020604 2304845 := bbase (se 3 (by rfl) ⟨432158, by rfl⟩ : syracuseStep 2304845 = 864317) (by norm_num)
theorem B3451733 : Blo 1020604 3451733 := bbase (se 9 (by rfl) ⟨10112, by rfl⟩ : syracuseStep 3451733 = 20225) (by norm_num)
theorem B3877733 : Blo 1020604 3877733 := bbase (se 4 (by rfl) ⟨363537, by rfl⟩ : syracuseStep 3877733 = 727075) (by norm_num)
theorem B2304917 : Blo 1020604 2304917 := bbase (se 6 (by rfl) ⟨54021, by rfl⟩ : syracuseStep 2304917 = 108043) (by norm_num)
theorem B2304989 : Blo 1020604 2304989 := bbase (se 3 (by rfl) ⟨432185, by rfl⟩ : syracuseStep 2304989 = 864371) (by norm_num)
theorem B1092629 : Blo 1020604 1092629 := bbase (se 6 (by rfl) ⟨25608, by rfl⟩ : syracuseStep 1092629 = 51217) (by norm_num)
theorem B2305061 : Blo 1020604 2305061 := bbase (se 4 (by rfl) ⟨216099, by rfl⟩ : syracuseStep 2305061 = 432199) (by norm_num)
theorem B1944661 : Blo 1020604 1944661 := bbase (se 8 (by rfl) ⟨11394, by rfl⟩ : syracuseStep 1944661 = 22789) (by norm_num)
theorem B2305133 : Blo 1020604 2305133 := bbase (se 3 (by rfl) ⟨432212, by rfl⟩ : syracuseStep 2305133 = 864425) (by norm_num)
theorem B2305205 : Blo 1020604 2305205 := bbase (se 5 (by rfl) ⟨108056, by rfl⟩ : syracuseStep 2305205 = 216113) (by norm_num)
theorem B1944805 : Blo 1020604 1944805 := bbase (se 4 (by rfl) ⟨182325, by rfl⟩ : syracuseStep 1944805 = 364651) (by norm_num)
theorem B2305277 : Blo 1020604 2305277 := bbase (se 3 (by rfl) ⟨432239, by rfl⟩ : syracuseStep 2305277 = 864479) (by norm_num)
theorem B3452165 : Blo 1020604 3452165 := bbase (se 4 (by rfl) ⟨323640, by rfl⟩ : syracuseStep 3452165 = 647281) (by norm_num)
theorem B4140341 : Blo 1020604 4140341 := bbase (se 5 (by rfl) ⟨194078, by rfl⟩ : syracuseStep 4140341 = 388157) (by norm_num)
theorem B2305349 : Blo 1020604 2305349 := bbase (se 4 (by rfl) ⟨216126, by rfl⟩ : syracuseStep 2305349 = 432253) (by norm_num)
theorem B1453421 : Blo 1020604 1453421 := bbase (se 3 (by rfl) ⟨272516, by rfl⟩ : syracuseStep 1453421 = 545033) (by norm_num)
theorem B1944965 : Blo 1020604 1944965 := bbase (se 4 (by rfl) ⟨182340, by rfl⟩ : syracuseStep 1944965 = 364681) (by norm_num)
theorem B1453501 : Blo 1020604 1453501 := bbase (se 3 (by rfl) ⟨272531, by rfl⟩ : syracuseStep 1453501 = 545063) (by norm_num)
theorem B1093073 : Blo 1020604 1093073 := bbase (se 2 (by rfl) ⟨409902, by rfl⟩ : syracuseStep 1093073 = 819805) (by norm_num)
theorem B1093133 : Blo 1020604 1093133 := bbase (se 3 (by rfl) ⟨204962, by rfl⟩ : syracuseStep 1093133 = 409925) (by norm_num)
theorem B1945109 : Blo 1020604 1945109 := bbase (se 6 (by rfl) ⟨45588, by rfl⟩ : syracuseStep 1945109 = 91177) (by norm_num)
theorem B1453621 : Blo 1020604 1453621 := bbase (se 5 (by rfl) ⟨68138, by rfl⟩ : syracuseStep 1453621 = 136277) (by norm_num)
theorem B4370021 : Blo 1020604 4370021 := bbase (se 4 (by rfl) ⟨409689, by rfl⟩ : syracuseStep 4370021 = 819379) (by norm_num)
theorem B8728181 : Blo 1020604 8728181 := bbase (se 5 (by rfl) ⟨409133, by rfl⟩ : syracuseStep 8728181 = 818267) (by norm_num)
theorem B1093261 : Blo 1020604 1093261 := bbase (se 3 (by rfl) ⟨204986, by rfl⟩ : syracuseStep 1093261 = 409973) (by norm_num)
theorem B1453717 : Blo 1020604 1453717 := bbase (se 6 (by rfl) ⟨34071, by rfl⟩ : syracuseStep 1453717 = 68143) (by norm_num)
theorem B20983445 : Blo 1020604 20983445 := bbase (se 6 (by rfl) ⟨491799, by rfl⟩ : syracuseStep 20983445 = 983599) (by norm_num)
theorem B3452597 : Blo 1020604 3452597 := bbase (se 5 (by rfl) ⟨161840, by rfl⟩ : syracuseStep 3452597 = 323681) (by norm_num)
theorem B1093705 : Blo 1020604 1093705 := bbase (se 2 (by rfl) ⟨410139, by rfl⟩ : syracuseStep 1093705 = 820279) (by norm_num)
theorem B3453029 : Blo 1020604 3453029 := bbase (se 4 (by rfl) ⟨323721, by rfl⟩ : syracuseStep 3453029 = 647443) (by norm_num)
theorem B1454213 : Blo 1020604 1454213 := bbase (se 4 (by rfl) ⟨136332, by rfl⟩ : syracuseStep 1454213 = 272665) (by norm_num)
theorem B4665509 : Blo 1020604 4665509 := bbase (se 4 (by rfl) ⟨437391, by rfl⟩ : syracuseStep 4665509 = 874783) (by norm_num)
theorem B1093825 : Blo 1020604 1093825 := bbase (se 2 (by rfl) ⟨410184, by rfl⟩ : syracuseStep 1093825 = 820369) (by norm_num)
theorem B1094077 : Blo 1020604 1094077 := bbase (se 3 (by rfl) ⟨205139, by rfl⟩ : syracuseStep 1094077 = 410279) (by norm_num)
theorem B1094081 : Blo 1020604 1094081 := bbase (se 2 (by rfl) ⟨410280, by rfl⟩ : syracuseStep 1094081 = 820561) (by norm_num)
theorem B3453461 : Blo 1020604 3453461 := bbase (se 6 (by rfl) ⟨80940, by rfl⟩ : syracuseStep 3453461 = 161881) (by norm_num)
theorem B4141637 : Blo 1020604 4141637 := bbase (se 4 (by rfl) ⟨388278, by rfl⟩ : syracuseStep 4141637 = 776557) (by norm_num)
theorem B9810517 : Blo 1020604 9810517 := bbase (se 8 (by rfl) ⟨57483, by rfl⟩ : syracuseStep 9810517 = 114967) (by norm_num)
theorem B4371029 : Blo 1020604 4371029 := bbase (se 8 (by rfl) ⟨25611, by rfl⟩ : syracuseStep 4371029 = 51223) (by norm_num)
theorem B1454765 : Blo 1020604 1454765 := bbase (se 3 (by rfl) ⟨272768, by rfl⟩ : syracuseStep 1454765 = 545537) (by norm_num)
theorem B1684309 : Blo 1020604 1684309 := bbase (se 9 (by rfl) ⟨4934, by rfl⟩ : syracuseStep 1684309 = 9869) (by norm_num)
theorem B3879845 : Blo 1020604 3879845 := bbase (se 4 (by rfl) ⟨363735, by rfl⟩ : syracuseStep 3879845 = 727471) (by norm_num)
theorem B3453893 : Blo 1020604 3453893 := bbase (se 4 (by rfl) ⟨323802, by rfl⟩ : syracuseStep 3453893 = 647605) (by norm_num)
theorem B1553357 : Blo 1020604 1553357 := bbase (se 3 (by rfl) ⟨291254, by rfl⟩ : syracuseStep 1553357 = 582509) (by norm_num)
theorem B3683285 : Blo 1020604 3683285 := bbase (se 7 (by rfl) ⟨43163, by rfl⟩ : syracuseStep 3683285 = 86327) (by norm_num)
theorem B1553453 : Blo 1020604 1553453 := bbase (se 3 (by rfl) ⟨291272, by rfl⟩ : syracuseStep 1553453 = 582545) (by norm_num)
theorem B3880133 : Blo 1020604 3880133 := bbase (se 4 (by rfl) ⟨363762, by rfl⟩ : syracuseStep 3880133 = 727525) (by norm_num)
theorem B3454325 : Blo 1020604 3454325 := bbase (se 5 (by rfl) ⟨161921, by rfl⟩ : syracuseStep 3454325 = 323843) (by norm_num)
theorem B1455517 : Blo 1020604 1455517 := bbase (se 3 (by rfl) ⟨272909, by rfl⟩ : syracuseStep 1455517 = 545819) (by norm_num)
theorem B1226161 : Blo 1020604 1226161 := bbase (se 2 (by rfl) ⟨459810, by rfl⟩ : syracuseStep 1226161 = 919621) (by norm_num)
theorem B1291717 : Blo 1020604 1291717 := bbase (se 4 (by rfl) ⟨121098, by rfl⟩ : syracuseStep 1291717 = 242197) (by norm_num)
theorem B1553917 : Blo 1020604 1553917 := bbase (se 3 (by rfl) ⟨291359, by rfl⟩ : syracuseStep 1553917 = 582719) (by norm_num)
theorem B1553941 : Blo 1020604 1553941 := bbase (se 6 (by rfl) ⟨36420, by rfl⟩ : syracuseStep 1553941 = 72841) (by norm_num)
theorem B1291889 : Blo 1020604 1291889 := bbase (se 2 (by rfl) ⟨484458, by rfl⟩ : syracuseStep 1291889 = 968917) (by norm_num)
theorem B1291945 : Blo 1020604 1291945 := bbase (se 2 (by rfl) ⟨484479, by rfl⟩ : syracuseStep 1291945 = 968959) (by norm_num)
theorem B1292041 : Blo 1020604 1292041 := bbase (se 2 (by rfl) ⟨484515, by rfl⟩ : syracuseStep 1292041 = 969031) (by norm_num)
theorem B3454757 : Blo 1020604 3454757 := bbase (se 4 (by rfl) ⟨323883, by rfl⟩ : syracuseStep 3454757 = 647767) (by norm_num)
theorem B1292213 : Blo 1020604 1292213 := bbase (se 5 (by rfl) ⟨60572, by rfl⟩ : syracuseStep 1292213 = 121145) (by norm_num)
theorem B1292269 : Blo 1020604 1292269 := bbase (se 3 (by rfl) ⟨242300, by rfl⟩ : syracuseStep 1292269 = 484601) (by norm_num)
theorem B7780373 : Blo 1020604 7780373 := bbase (se 6 (by rfl) ⟨182352, by rfl⟩ : syracuseStep 7780373 = 364705) (by norm_num)
theorem B1292365 : Blo 1020604 1292365 := bbase (se 3 (by rfl) ⟨242318, by rfl⟩ : syracuseStep 1292365 = 484637) (by norm_num)
theorem B1456309 : Blo 1020604 1456309 := bbase (se 5 (by rfl) ⟨68264, by rfl⟩ : syracuseStep 1456309 = 136529) (by norm_num)
theorem B3455189 : Blo 1020604 3455189 := bbase (se 7 (by rfl) ⟨40490, by rfl⟩ : syracuseStep 3455189 = 80981) (by norm_num)
theorem B1292537 : Blo 1020604 1292537 := bbase (se 2 (by rfl) ⟨484701, by rfl⟩ : syracuseStep 1292537 = 969403) (by norm_num)
theorem B1292593 : Blo 1020604 1292593 := bbase (se 2 (by rfl) ⟨484722, by rfl⟩ : syracuseStep 1292593 = 969445) (by norm_num)
theorem B4372805 : Blo 1020604 4372805 := bbase (se 4 (by rfl) ⟨409950, by rfl⟩ : syracuseStep 4372805 = 819901) (by norm_num)
theorem B3881317 : Blo 1020604 3881317 := bbase (se 4 (by rfl) ⟨363873, by rfl⟩ : syracuseStep 3881317 = 727747) (by norm_num)
theorem B1292689 : Blo 1020604 1292689 := bbase (se 2 (by rfl) ⟨484758, by rfl⟩ : syracuseStep 1292689 = 969517) (by norm_num)
theorem B1456645 : Blo 1020604 1456645 := bbase (se 4 (by rfl) ⟨136560, by rfl⟩ : syracuseStep 1456645 = 273121) (by norm_num)
theorem B1292861 : Blo 1020604 1292861 := bbase (se 3 (by rfl) ⟨242411, by rfl⟩ : syracuseStep 1292861 = 484823) (by norm_num)
theorem B1292917 : Blo 1020604 1292917 := bbase (se 5 (by rfl) ⟨60605, by rfl⟩ : syracuseStep 1292917 = 121211) (by norm_num)
theorem B3455621 : Blo 1020604 3455621 := bbase (se 4 (by rfl) ⟨323964, by rfl⟩ : syracuseStep 3455621 = 647929) (by norm_num)
theorem B3881621 : Blo 1020604 3881621 := bbase (se 6 (by rfl) ⟨90975, by rfl⟩ : syracuseStep 3881621 = 181951) (by norm_num)
theorem B1555109 : Blo 1020604 1555109 := bbase (se 4 (by rfl) ⟨145791, by rfl⟩ : syracuseStep 1555109 = 291583) (by norm_num)
theorem B1293013 : Blo 1020604 1293013 := bbase (se 7 (by rfl) ⟨15152, by rfl⟩ : syracuseStep 1293013 = 30305) (by norm_num)
theorem B1456861 : Blo 1020604 1456861 := bbase (se 3 (by rfl) ⟨273161, by rfl⟩ : syracuseStep 1456861 = 546323) (by norm_num)
theorem B1555205 : Blo 1020604 1555205 := bbase (se 4 (by rfl) ⟨145800, by rfl⟩ : syracuseStep 1555205 = 291601) (by norm_num)
theorem B5520149 : Blo 1020604 5520149 := bbase (se 6 (by rfl) ⟨129378, by rfl⟩ : syracuseStep 5520149 = 258757) (by norm_num)
theorem B1293185 : Blo 1020604 1293185 := bbase (se 2 (by rfl) ⟨484944, by rfl⟩ : syracuseStep 1293185 = 969889) (by norm_num)
theorem B1293241 : Blo 1020604 1293241 := bbase (se 2 (by rfl) ⟨484965, by rfl⟩ : syracuseStep 1293241 = 969931) (by norm_num)
theorem B1293337 : Blo 1020604 1293337 := bbase (se 2 (by rfl) ⟨485001, by rfl⟩ : syracuseStep 1293337 = 970003) (by norm_num)
theorem B3456053 : Blo 1020604 3456053 := bbase (se 5 (by rfl) ⟨162002, by rfl⟩ : syracuseStep 3456053 = 324005) (by norm_num)
theorem B1457237 : Blo 1020604 1457237 := bbase (se 8 (by rfl) ⟨8538, by rfl⟩ : syracuseStep 1457237 = 17077) (by norm_num)
theorem B1227881 : Blo 1020604 1227881 := bbase (se 2 (by rfl) ⟨460455, by rfl⟩ : syracuseStep 1227881 = 920911) (by norm_num)
theorem B1293509 : Blo 1020604 1293509 := bbase (se 4 (by rfl) ⟨121266, by rfl⟩ : syracuseStep 1293509 = 242533) (by norm_num)
theorem B1227997 : Blo 1020604 1227997 := bbase (se 3 (by rfl) ⟨230249, by rfl⟩ : syracuseStep 1227997 = 460499) (by norm_num)
theorem B1293565 : Blo 1020604 1293565 := bbase (se 3 (by rfl) ⟨242543, by rfl⟩ : syracuseStep 1293565 = 485087) (by norm_num)
theorem B1228069 : Blo 1020604 1228069 := bbase (se 4 (by rfl) ⟨115131, by rfl⟩ : syracuseStep 1228069 = 230263) (by norm_num)
theorem B1293661 : Blo 1020604 1293661 := bbase (se 3 (by rfl) ⟨242561, by rfl⟩ : syracuseStep 1293661 = 485123) (by norm_num)
theorem B5913973 : Blo 1020604 5913973 := bbase (se 5 (by rfl) ⟨277217, by rfl⟩ : syracuseStep 5913973 = 554435) (by norm_num)
theorem B1228189 : Blo 1020604 1228189 := bbase (se 3 (by rfl) ⟨230285, by rfl⟩ : syracuseStep 1228189 = 460571) (by norm_num)
theorem B3456485 : Blo 1020604 3456485 := bbase (se 4 (by rfl) ⟨324045, by rfl⟩ : syracuseStep 3456485 = 648091) (by norm_num)
theorem B1293833 : Blo 1020604 1293833 := bbase (se 2 (by rfl) ⟨485187, by rfl⟩ : syracuseStep 1293833 = 970375) (by norm_num)
theorem B1293889 : Blo 1020604 1293889 := bbase (se 2 (by rfl) ⟨485208, by rfl⟩ : syracuseStep 1293889 = 970417) (by norm_num)
theorem B6209141 : Blo 1020604 6209141 := bbase (se 5 (by rfl) ⟨291053, by rfl⟩ : syracuseStep 6209141 = 582107) (by norm_num)
theorem B1293985 : Blo 1020604 1293985 := bbase (se 2 (by rfl) ⟨485244, by rfl⟩ : syracuseStep 1293985 = 970489) (by norm_num)
theorem B1228573 : Blo 1020604 1228573 := bbase (se 3 (by rfl) ⟨230357, by rfl⟩ : syracuseStep 1228573 = 460715) (by norm_num)
theorem B1294157 : Blo 1020604 1294157 := bbase (se 3 (by rfl) ⟨242654, by rfl⟩ : syracuseStep 1294157 = 485309) (by norm_num)
theorem B1294213 : Blo 1020604 1294213 := bbase (se 4 (by rfl) ⟨121332, by rfl⟩ : syracuseStep 1294213 = 242665) (by norm_num)
theorem B3456917 : Blo 1020604 3456917 := bbase (se 6 (by rfl) ⟨81021, by rfl⟩ : syracuseStep 3456917 = 162043) (by norm_num)
theorem B1294309 : Blo 1020604 1294309 := bbase (se 4 (by rfl) ⟨121341, by rfl⟩ : syracuseStep 1294309 = 242683) (by norm_num)
theorem B1294481 : Blo 1020604 1294481 := bbase (se 2 (by rfl) ⟨485430, by rfl⟩ : syracuseStep 1294481 = 970861) (by norm_num)
theorem B1294537 : Blo 1020604 1294537 := bbase (se 2 (by rfl) ⟨485451, by rfl⟩ : syracuseStep 1294537 = 970903) (by norm_num)
theorem B1294633 : Blo 1020604 1294633 := bbase (se 2 (by rfl) ⟨485487, by rfl⟩ : syracuseStep 1294633 = 970975) (by norm_num)
theorem B3457349 : Blo 1020604 3457349 := bbase (se 4 (by rfl) ⟨324126, by rfl⟩ : syracuseStep 3457349 = 648253) (by norm_num)
theorem B2769221 : Blo 1020604 2769221 := bbase (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) (by norm_num)
theorem B1229261 : Blo 1020604 1229261 := bbase (se 3 (by rfl) ⟨230486, by rfl⟩ : syracuseStep 1229261 = 460973) (by norm_num)
theorem B1294805 : Blo 1020604 1294805 := bbase (se 7 (by rfl) ⟨15173, by rfl⟩ : syracuseStep 1294805 = 30347) (by norm_num)
theorem B1458661 : Blo 1020604 1458661 := bbase (se 4 (by rfl) ⟨136749, by rfl⟩ : syracuseStep 1458661 = 273499) (by norm_num)
theorem B1294861 : Blo 1020604 1294861 := bbase (se 3 (by rfl) ⟨242786, by rfl⟩ : syracuseStep 1294861 = 485573) (by norm_num)
theorem B1294957 : Blo 1020604 1294957 := bbase (se 3 (by rfl) ⟨242804, by rfl⟩ : syracuseStep 1294957 = 485609) (by norm_num)
theorem B9814709 : Blo 1020604 9814709 := bbase (se 5 (by rfl) ⟨460064, by rfl⟩ : syracuseStep 9814709 = 920129) (by norm_num)
theorem B3883733 : Blo 1020604 3883733 := bbase (se 7 (by rfl) ⟨45512, by rfl⟩ : syracuseStep 3883733 = 91025) (by norm_num)
theorem B3457781 : Blo 1020604 3457781 := bbase (se 5 (by rfl) ⟨162083, by rfl⟩ : syracuseStep 3457781 = 324167) (by norm_num)
theorem B1295129 : Blo 1020604 1295129 := bbase (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) (by norm_num)
theorem B2179885 : Blo 1020604 2179885 := bbase (se 3 (by rfl) ⟨408728, by rfl⟩ : syracuseStep 2179885 = 817457) (by norm_num)
theorem B1295185 : Blo 1020604 1295185 := bbase (se 2 (by rfl) ⟨485694, by rfl⟩ : syracuseStep 1295185 = 971389) (by norm_num)
theorem B1557341 : Blo 1020604 1557341 := bbase (se 3 (by rfl) ⟨292001, by rfl⟩ : syracuseStep 1557341 = 584003) (by norm_num)
theorem B1295281 : Blo 1020604 1295281 := bbase (se 2 (by rfl) ⟨485730, by rfl⟩ : syracuseStep 1295281 = 971461) (by norm_num)
theorem B2180029 : Blo 1020604 2180029 := bbase (se 3 (by rfl) ⟨408755, by rfl⟩ : syracuseStep 2180029 = 817511) (by norm_num)
theorem B3884021 : Blo 1020604 3884021 := bbase (se 5 (by rfl) ⟨182063, by rfl⟩ : syracuseStep 3884021 = 364127) (by norm_num)
theorem B2802709 : Blo 1020604 2802709 := bbase (se 6 (by rfl) ⟨65688, by rfl⟩ : syracuseStep 2802709 = 131377) (by norm_num)
theorem B1229861 : Blo 1020604 1229861 := bbase (se 4 (by rfl) ⟨115299, by rfl⟩ : syracuseStep 1229861 = 230599) (by norm_num)
theorem B2212925 : Blo 1020604 2212925 := bbase (se 3 (by rfl) ⟨414923, by rfl⟩ : syracuseStep 2212925 = 829847) (by norm_num)
theorem B1295453 : Blo 1020604 1295453 := bbase (se 3 (by rfl) ⟨242897, by rfl⟩ : syracuseStep 1295453 = 485795) (by norm_num)
theorem B1295509 : Blo 1020604 1295509 := bbase (se 6 (by rfl) ⟨30363, by rfl⟩ : syracuseStep 1295509 = 60727) (by norm_num)
theorem B1295605 : Blo 1020604 1295605 := bbase (se 5 (by rfl) ⟨60731, by rfl⟩ : syracuseStep 1295605 = 121463) (by norm_num)
theorem B2180405 : Blo 1020604 2180405 := bbase (se 5 (by rfl) ⟨102206, by rfl⟩ : syracuseStep 2180405 = 204413) (by norm_num)
theorem B1164625 : Blo 1020604 1164625 := bbase (se 2 (by rfl) ⟨436734, by rfl⟩ : syracuseStep 1164625 = 873469) (by norm_num)
theorem B1230169 : Blo 1020604 1230169 := bbase (se 2 (by rfl) ⟨461313, by rfl⟩ : syracuseStep 1230169 = 922627) (by norm_num)
theorem B1295777 : Blo 1020604 1295777 := bbase (se 2 (by rfl) ⟨485916, by rfl⟩ : syracuseStep 1295777 = 971833) (by norm_num)
theorem B1230265 : Blo 1020604 1230265 := bbase (se 2 (by rfl) ⟨461349, by rfl⟩ : syracuseStep 1230265 = 922699) (by norm_num)
theorem B13125077 : Blo 1020604 13125077 := bbase (se 7 (by rfl) ⟨153809, by rfl⟩ : syracuseStep 13125077 = 307619) (by norm_num)
theorem B1295833 : Blo 1020604 1295833 := bbase (se 2 (by rfl) ⟨485937, by rfl⟩ : syracuseStep 1295833 = 971875) (by norm_num)
theorem B1230313 : Blo 1020604 1230313 := bbase (se 2 (by rfl) ⟨461367, by rfl⟩ : syracuseStep 1230313 = 922735) (by norm_num)
theorem B1295929 : Blo 1020604 1295929 := bbase (se 2 (by rfl) ⟨485973, by rfl⟩ : syracuseStep 1295929 = 971947) (by norm_num)
theorem B2180773 : Blo 1020604 2180773 := bbase (se 4 (by rfl) ⟨204447, by rfl⟩ : syracuseStep 2180773 = 408895) (by norm_num)
theorem B1296101 : Blo 1020604 1296101 := bbase (se 4 (by rfl) ⟨121509, by rfl⟩ : syracuseStep 1296101 = 243019) (by norm_num)
theorem B8406773 : Blo 1020604 8406773 := bbase (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) (by norm_num)
theorem B1296157 : Blo 1020604 1296157 := bbase (se 3 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 1296157 = 486059) (by norm_num)
theorem B1296253 : Blo 1020604 1296253 := bbase (se 3 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 1296253 = 486095) (by norm_num)
theorem B1722397 : Blo 1020604 1722397 := bbase (se 3 (by rfl) ⟨322949, by rfl⟩ : syracuseStep 1722397 = 645899) (by norm_num)
theorem B1296425 : Blo 1020604 1296425 := bbase (se 2 (by rfl) ⟨486159, by rfl⟩ : syracuseStep 1296425 = 972319) (by norm_num)
theorem B1296481 : Blo 1020604 1296481 := bbase (se 2 (by rfl) ⟨486180, by rfl⟩ : syracuseStep 1296481 = 972361) (by norm_num)
theorem B1722485 : Blo 1020604 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B12601493 : Blo 1020604 12601493 := bbase (se 6 (by rfl) ⟨295347, by rfl⟩ : syracuseStep 12601493 = 590695) (by norm_num)
theorem B3885205 : Blo 1020604 3885205 := bbase (se 6 (by rfl) ⟨91059, by rfl⟩ : syracuseStep 3885205 = 182119) (by norm_num)
theorem B4671637 : Blo 1020604 4671637 := bbase (se 6 (by rfl) ⟨109491, by rfl⟩ : syracuseStep 4671637 = 218983) (by norm_num)
theorem B1296577 : Blo 1020604 1296577 := bbase (se 2 (by rfl) ⟨486216, by rfl⟩ : syracuseStep 1296577 = 972433) (by norm_num)
theorem B3688661 : Blo 1020604 3688661 := bbase (se 7 (by rfl) ⟨43226, by rfl⟩ : syracuseStep 3688661 = 86453) (by norm_num)
theorem B1722613 : Blo 1020604 1722613 := bbase (se 5 (by rfl) ⟨80747, by rfl⟩ : syracuseStep 1722613 = 161495) (by norm_num)
theorem B1034533 : Blo 1020604 1034533 := bbase (se 4 (by rfl) ⟨96987, by rfl⟩ : syracuseStep 1034533 = 193975) (by norm_num)
theorem B1722701 : Blo 1020604 1722701 := bbase (se 3 (by rfl) ⟨323006, by rfl⟩ : syracuseStep 1722701 = 646013) (by norm_num)
theorem B1296749 : Blo 1020604 1296749 := bbase (se 3 (by rfl) ⟨243140, by rfl⟩ : syracuseStep 1296749 = 486281) (by norm_num)
theorem B3885509 : Blo 1020604 3885509 := bbase (se 4 (by rfl) ⟨364266, by rfl⟩ : syracuseStep 3885509 = 728533) (by norm_num)
theorem B1722829 : Blo 1020604 1722829 := bbase (se 3 (by rfl) ⟨323030, by rfl⟩ : syracuseStep 1722829 = 646061) (by norm_num)
theorem B1722917 : Blo 1020604 1722917 := bbase (se 4 (by rfl) ⟨161523, by rfl⟩ : syracuseStep 1722917 = 323047) (by norm_num)
theorem B1723045 : Blo 1020604 1723045 := bbase (se 4 (by rfl) ⟨161535, by rfl⟩ : syracuseStep 1723045 = 323071) (by norm_num)
theorem B1723133 : Blo 1020604 1723133 := bbase (se 3 (by rfl) ⟨323087, by rfl⟩ : syracuseStep 1723133 = 646175) (by norm_num)
theorem B1723261 : Blo 1020604 1723261 := bbase (se 3 (by rfl) ⟨323111, by rfl⟩ : syracuseStep 1723261 = 646223) (by norm_num)
theorem B1723349 : Blo 1020604 1723349 := bbase (se 7 (by rfl) ⟨20195, by rfl⟩ : syracuseStep 1723349 = 40391) (by norm_num)
theorem B1723477 : Blo 1020604 1723477 := bbase (se 8 (by rfl) ⟨10098, by rfl⟩ : syracuseStep 1723477 = 20197) (by norm_num)
theorem B2182277 : Blo 1020604 2182277 := bbase (se 4 (by rfl) ⟨204588, by rfl⟩ : syracuseStep 2182277 = 409177) (by norm_num)
theorem B1035425 : Blo 1020604 1035425 := bbase (se 2 (by rfl) ⟨388284, by rfl⟩ : syracuseStep 1035425 = 776569) (by norm_num)
theorem B1723565 : Blo 1020604 1723565 := bbase (se 3 (by rfl) ⟨323168, by rfl⟩ : syracuseStep 1723565 = 646337) (by norm_num)
theorem B2182421 : Blo 1020604 2182421 := bbase (se 6 (by rfl) ⟨51150, by rfl⟩ : syracuseStep 2182421 = 102301) (by norm_num)
theorem B5524757 : Blo 1020604 5524757 := bbase (se 6 (by rfl) ⟨129486, by rfl⟩ : syracuseStep 5524757 = 258973) (by norm_num)
theorem B1723693 : Blo 1020604 1723693 := bbase (se 3 (by rfl) ⟨323192, by rfl⟩ : syracuseStep 1723693 = 646385) (by norm_num)
theorem B5918005 : Blo 1020604 5918005 := bbase (se 5 (by rfl) ⟨277406, by rfl⟩ : syracuseStep 5918005 = 554813) (by norm_num)
theorem B1723781 : Blo 1020604 1723781 := bbase (se 4 (by rfl) ⟨161604, by rfl⟩ : syracuseStep 1723781 = 323209) (by norm_num)
theorem B8736245 : Blo 1020604 8736245 := bbase (se 5 (by rfl) ⟨409511, by rfl⟩ : syracuseStep 8736245 = 819023) (by norm_num)
theorem B1723909 : Blo 1020604 1723909 := bbase (se 4 (by rfl) ⟨161616, by rfl⟩ : syracuseStep 1723909 = 323233) (by norm_num)
theorem B1723997 : Blo 1020604 1723997 := bbase (se 3 (by rfl) ⟨323249, by rfl⟩ : syracuseStep 1723997 = 646499) (by norm_num)
theorem B2182781 : Blo 1020604 2182781 := bbase (se 3 (by rfl) ⟨409271, by rfl⟩ : syracuseStep 2182781 = 818543) (by norm_num)
theorem B1166989 : Blo 1020604 1166989 := bbase (se 3 (by rfl) ⟨218810, by rfl⟩ : syracuseStep 1166989 = 437621) (by norm_num)
theorem B1724125 : Blo 1020604 1724125 := bbase (se 3 (by rfl) ⟨323273, by rfl⟩ : syracuseStep 1724125 = 646547) (by norm_num)
theorem B1036001 : Blo 1020604 1036001 := bbase (se 2 (by rfl) ⟨388500, by rfl⟩ : syracuseStep 1036001 = 777001) (by norm_num)
theorem B1724213 : Blo 1020604 1724213 := bbase (se 5 (by rfl) ⟨80822, by rfl⟩ : syracuseStep 1724213 = 161645) (by norm_num)
theorem B5820245 : Blo 1020604 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B1724341 : Blo 1020604 1724341 := bbase (se 5 (by rfl) ⟨80828, by rfl⟩ : syracuseStep 1724341 = 161657) (by norm_num)
theorem B1167313 : Blo 1020604 1167313 := bbase (se 2 (by rfl) ⟨437742, by rfl⟩ : syracuseStep 1167313 = 875485) (by norm_num)
theorem B1724429 : Blo 1020604 1724429 := bbase (se 3 (by rfl) ⟨323330, by rfl⟩ : syracuseStep 1724429 = 646661) (by norm_num)
theorem B1036349 : Blo 1020604 1036349 := bbase (se 3 (by rfl) ⟨194315, by rfl⟩ : syracuseStep 1036349 = 388631) (by norm_num)
theorem B1724557 : Blo 1020604 1724557 := bbase (se 3 (by rfl) ⟨323354, by rfl⟩ : syracuseStep 1724557 = 646709) (by norm_num)
theorem B1724645 : Blo 1020604 1724645 := bbase (se 4 (by rfl) ⟨161685, by rfl⟩ : syracuseStep 1724645 = 323371) (by norm_num)
theorem B1036585 : Blo 1020604 1036585 := bbase (se 2 (by rfl) ⟨388719, by rfl⟩ : syracuseStep 1036585 = 777439) (by norm_num)
theorem B1724773 : Blo 1020604 1724773 := bbase (se 4 (by rfl) ⟨161697, by rfl⟩ : syracuseStep 1724773 = 323395) (by norm_num)
theorem B1331605 : Blo 1020604 1331605 := bbase (se 6 (by rfl) ⟨31209, by rfl⟩ : syracuseStep 1331605 = 62419) (by norm_num)
theorem B1724861 : Blo 1020604 1724861 := bbase (se 3 (by rfl) ⟨323411, by rfl⟩ : syracuseStep 1724861 = 646823) (by norm_num)
theorem B2183669 : Blo 1020604 2183669 := bbase (se 5 (by rfl) ⟨102359, by rfl⟩ : syracuseStep 2183669 = 204719) (by norm_num)
theorem B3887621 : Blo 1020604 3887621 := bbase (se 4 (by rfl) ⟨364464, by rfl⟩ : syracuseStep 3887621 = 728929) (by norm_num)
theorem B1724989 : Blo 1020604 1724989 := bbase (se 3 (by rfl) ⟨323435, by rfl⟩ : syracuseStep 1724989 = 646871) (by norm_num)
theorem B1725077 : Blo 1020604 1725077 := bbase (se 6 (by rfl) ⟨40431, by rfl⟩ : syracuseStep 1725077 = 80863) (by norm_num)
theorem B2183917 : Blo 1020604 2183917 := bbase (se 3 (by rfl) ⟨409484, by rfl⟩ : syracuseStep 2183917 = 818969) (by norm_num)
theorem B1168129 : Blo 1020604 1168129 := bbase (se 2 (by rfl) ⟨438048, by rfl⟩ : syracuseStep 1168129 = 876097) (by norm_num)
theorem B1725205 : Blo 1020604 1725205 := bbase (se 6 (by rfl) ⟨40434, by rfl⟩ : syracuseStep 1725205 = 80869) (by norm_num)
theorem B3887909 : Blo 1020604 3887909 := bbase (se 4 (by rfl) ⟨364491, by rfl⟩ : syracuseStep 3887909 = 728983) (by norm_num)
theorem B1725293 : Blo 1020604 1725293 := bbase (se 3 (by rfl) ⟨323492, by rfl⟩ : syracuseStep 1725293 = 646985) (by norm_num)
theorem B1168357 : Blo 1020604 1168357 := bbase (se 4 (by rfl) ⟨109533, by rfl⟩ : syracuseStep 1168357 = 219067) (by norm_num)
theorem B1725421 : Blo 1020604 1725421 := bbase (se 3 (by rfl) ⟨323516, by rfl⟩ : syracuseStep 1725421 = 647033) (by norm_num)
theorem B5821429 : Blo 1020604 5821429 := bbase (se 5 (by rfl) ⟨272879, by rfl⟩ : syracuseStep 5821429 = 545759) (by norm_num)
theorem B1725509 : Blo 1020604 1725509 := bbase (se 4 (by rfl) ⟨161766, by rfl⟩ : syracuseStep 1725509 = 323533) (by norm_num)
theorem B1037485 : Blo 1020604 1037485 := bbase (se 3 (by rfl) ⟨194528, by rfl⟩ : syracuseStep 1037485 = 389057) (by norm_num)
theorem B1660085 : Blo 1020604 1660085 := bbase (se 5 (by rfl) ⟨77816, by rfl⟩ : syracuseStep 1660085 = 155633) (by norm_num)
theorem B1725637 : Blo 1020604 1725637 := bbase (se 4 (by rfl) ⟨161778, by rfl⟩ : syracuseStep 1725637 = 323557) (by norm_num)
theorem B2184421 : Blo 1020604 2184421 := bbase (se 4 (by rfl) ⟨204789, by rfl⟩ : syracuseStep 2184421 = 409579) (by norm_num)
theorem B1725725 : Blo 1020604 1725725 := bbase (se 3 (by rfl) ⟨323573, by rfl⟩ : syracuseStep 1725725 = 647147) (by norm_num)
theorem B1725853 : Blo 1020604 1725853 := bbase (se 3 (by rfl) ⟨323597, by rfl⟩ : syracuseStep 1725853 = 647195) (by norm_num)
theorem B1037777 : Blo 1020604 1037777 := bbase (se 2 (by rfl) ⟨389166, by rfl⟩ : syracuseStep 1037777 = 778333) (by norm_num)
theorem B1725941 : Blo 1020604 1725941 := bbase (se 5 (by rfl) ⟨80903, by rfl⟩ : syracuseStep 1725941 = 161807) (by norm_num)
theorem B1726069 : Blo 1020604 1726069 := bbase (se 5 (by rfl) ⟨80909, by rfl⟩ : syracuseStep 1726069 = 161819) (by norm_num)
theorem B1726157 : Blo 1020604 1726157 := bbase (se 3 (by rfl) ⟨323654, by rfl⟩ : syracuseStep 1726157 = 647309) (by norm_num)
theorem B29513429 : Blo 1020604 29513429 := bbase (se 7 (by rfl) ⟨345860, by rfl⟩ : syracuseStep 29513429 = 691721) (by norm_num)
theorem B7100117 : Blo 1020604 7100117 := bbase (se 7 (by rfl) ⟨83204, by rfl⟩ : syracuseStep 7100117 = 166409) (by norm_num)
theorem B1038101 : Blo 1020604 1038101 := bbase (se 6 (by rfl) ⟨24330, by rfl⟩ : syracuseStep 1038101 = 48661) (by norm_num)
theorem B1726285 : Blo 1020604 1726285 := bbase (se 3 (by rfl) ⟨323678, by rfl⟩ : syracuseStep 1726285 = 647357) (by norm_num)
theorem B1726373 : Blo 1020604 1726373 := bbase (se 4 (by rfl) ⟨161847, by rfl⟩ : syracuseStep 1726373 = 323695) (by norm_num)
theorem B3889093 : Blo 1020604 3889093 := bbase (se 4 (by rfl) ⟨364602, by rfl⟩ : syracuseStep 3889093 = 729205) (by norm_num)
theorem B7985141 : Blo 1020604 7985141 := bbase (se 5 (by rfl) ⟨374303, by rfl⟩ : syracuseStep 7985141 = 748607) (by norm_num)
theorem B1726501 : Blo 1020604 1726501 := bbase (se 4 (by rfl) ⟨161859, by rfl⟩ : syracuseStep 1726501 = 323719) (by norm_num)
theorem B1038425 : Blo 1020604 1038425 := bbase (se 2 (by rfl) ⟨389409, by rfl⟩ : syracuseStep 1038425 = 778819) (by norm_num)
theorem B2185309 : Blo 1020604 2185309 := bbase (se 3 (by rfl) ⟨409745, by rfl⟩ : syracuseStep 2185309 = 819491) (by norm_num)
theorem B1726589 : Blo 1020604 1726589 := bbase (se 3 (by rfl) ⟨323735, by rfl⟩ : syracuseStep 1726589 = 647471) (by norm_num)
theorem B3889397 : Blo 1020604 3889397 := bbase (se 5 (by rfl) ⟨182315, by rfl⟩ : syracuseStep 3889397 = 364631) (by norm_num)
theorem B1726717 : Blo 1020604 1726717 := bbase (se 3 (by rfl) ⟨323759, by rfl⟩ : syracuseStep 1726717 = 647519) (by norm_num)
theorem B1726805 : Blo 1020604 1726805 := bbase (se 10 (by rfl) ⟨2529, by rfl⟩ : syracuseStep 1726805 = 5059) (by norm_num)
theorem B1399205 : Blo 1020604 1399205 := bbase (se 4 (by rfl) ⟨131175, by rfl⟩ : syracuseStep 1399205 = 262351) (by norm_num)
theorem B1661357 : Blo 1020604 1661357 := bbase (se 3 (by rfl) ⟨311504, by rfl⟩ : syracuseStep 1661357 = 623009) (by norm_num)
theorem B6642101 : Blo 1020604 6642101 := bbase (se 5 (by rfl) ⟨311348, by rfl⟩ : syracuseStep 6642101 = 622697) (by norm_num)
theorem B1726933 : Blo 1020604 1726933 := bbase (se 7 (by rfl) ⟨20237, by rfl⟩ : syracuseStep 1726933 = 40475) (by norm_num)
theorem B5167637 : Blo 1020604 5167637 := bbase (se 6 (by rfl) ⟨121116, by rfl⟩ : syracuseStep 5167637 = 242233) (by norm_num)
theorem B1727021 : Blo 1020604 1727021 := bbase (se 3 (by rfl) ⟨323816, by rfl⟩ : syracuseStep 1727021 = 647633) (by norm_num)
theorem B2185805 : Blo 1020604 2185805 := bbase (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) (by norm_num)
theorem B1727149 : Blo 1020604 1727149 := bbase (se 3 (by rfl) ⟨323840, by rfl⟩ : syracuseStep 1727149 = 647681) (by norm_num)
theorem B3496693 : Blo 1020604 3496693 := bbase (se 5 (by rfl) ⟨163907, by rfl⟩ : syracuseStep 3496693 = 327815) (by norm_num)
theorem B1727237 : Blo 1020604 1727237 := bbase (se 4 (by rfl) ⟨161928, by rfl⟩ : syracuseStep 1727237 = 323857) (by norm_num)
theorem B1727365 : Blo 1020604 1727365 := bbase (se 4 (by rfl) ⟨161940, by rfl⟩ : syracuseStep 1727365 = 323881) (by norm_num)
theorem B5823413 : Blo 1020604 5823413 := bbase (se 5 (by rfl) ⟨272972, by rfl⟩ : syracuseStep 5823413 = 545945) (by norm_num)
theorem B1727453 : Blo 1020604 1727453 := bbase (se 3 (by rfl) ⟨323897, by rfl⟩ : syracuseStep 1727453 = 647795) (by norm_num)
theorem B1530917 : Blo 1020604 1530917 := bbase (se 4 (by rfl) ⟨143523, by rfl⟩ : syracuseStep 1530917 = 287047) (by norm_num)
theorem B1530941 : Blo 1020604 1530941 := bbase (se 3 (by rfl) ⟨287051, by rfl⟩ : syracuseStep 1530941 = 574103) (by norm_num)
theorem B1530965 : Blo 1020604 1530965 := bbase (se 8 (by rfl) ⟨8970, by rfl⟩ : syracuseStep 1530965 = 17941) (by norm_num)
theorem B1727581 : Blo 1020604 1727581 := bbase (se 3 (by rfl) ⟨323921, by rfl⟩ : syracuseStep 1727581 = 647843) (by norm_num)
theorem B1530989 : Blo 1020604 1530989 := bbase (se 3 (by rfl) ⟨287060, by rfl⟩ : syracuseStep 1530989 = 574121) (by norm_num)
theorem B1531013 : Blo 1020604 1531013 := bbase (se 4 (by rfl) ⟨143532, by rfl⟩ : syracuseStep 1531013 = 287065) (by norm_num)
theorem B1531037 : Blo 1020604 1531037 := bbase (se 3 (by rfl) ⟨287069, by rfl⟩ : syracuseStep 1531037 = 574139) (by norm_num)
theorem B1531061 : Blo 1020604 1531061 := bbase (se 5 (by rfl) ⟨71768, by rfl⟩ : syracuseStep 1531061 = 143537) (by norm_num)
theorem B9329845 : Blo 1020604 9329845 := bbase (se 5 (by rfl) ⟨437336, by rfl⟩ : syracuseStep 9329845 = 874673) (by norm_num)
theorem B1727669 : Blo 1020604 1727669 := bbase (se 5 (by rfl) ⟨80984, by rfl⟩ : syracuseStep 1727669 = 161969) (by norm_num)
theorem B1531085 : Blo 1020604 1531085 := bbase (se 3 (by rfl) ⟨287078, by rfl⟩ : syracuseStep 1531085 = 574157) (by norm_num)
theorem B1531109 : Blo 1020604 1531109 := bbase (se 4 (by rfl) ⟨143541, by rfl⟩ : syracuseStep 1531109 = 287083) (by norm_num)
theorem B7757045 : Blo 1020604 7757045 := bbase (se 5 (by rfl) ⟨363611, by rfl⟩ : syracuseStep 7757045 = 727223) (by norm_num)
theorem B1531133 : Blo 1020604 1531133 := bbase (se 3 (by rfl) ⟨287087, by rfl⟩ : syracuseStep 1531133 = 574175) (by norm_num)
theorem B1531157 : Blo 1020604 1531157 := bbase (se 6 (by rfl) ⟨35886, by rfl⟩ : syracuseStep 1531157 = 71773) (by norm_num)
theorem B1531181 : Blo 1020604 1531181 := bbase (se 3 (by rfl) ⟨287096, by rfl⟩ : syracuseStep 1531181 = 574193) (by norm_num)
theorem B1727797 : Blo 1020604 1727797 := bbase (se 5 (by rfl) ⟨80990, by rfl⟩ : syracuseStep 1727797 = 161981) (by norm_num)
theorem B1531205 : Blo 1020604 1531205 := bbase (se 4 (by rfl) ⟨143550, by rfl⟩ : syracuseStep 1531205 = 287101) (by norm_num)
theorem B1531229 : Blo 1020604 1531229 := bbase (se 3 (by rfl) ⟨287105, by rfl⟩ : syracuseStep 1531229 = 574211) (by norm_num)
theorem B1531253 : Blo 1020604 1531253 := bbase (se 5 (by rfl) ⟨71777, by rfl⟩ : syracuseStep 1531253 = 143555) (by norm_num)
theorem B1531277 : Blo 1020604 1531277 := bbase (se 3 (by rfl) ⟨287114, by rfl⟩ : syracuseStep 1531277 = 574229) (by norm_num)
theorem B1727885 : Blo 1020604 1727885 := bbase (se 3 (by rfl) ⟨323978, by rfl⟩ : syracuseStep 1727885 = 647957) (by norm_num)
theorem B1531301 : Blo 1020604 1531301 := bbase (se 4 (by rfl) ⟨143559, by rfl⟩ : syracuseStep 1531301 = 287119) (by norm_num)
theorem B1531325 : Blo 1020604 1531325 := bbase (se 3 (by rfl) ⟨287123, by rfl⟩ : syracuseStep 1531325 = 574247) (by norm_num)
theorem B2186693 : Blo 1020604 2186693 := bbase (se 4 (by rfl) ⟨205002, by rfl⟩ : syracuseStep 2186693 = 410005) (by norm_num)
theorem B1531349 : Blo 1020604 1531349 := bbase (se 7 (by rfl) ⟨17945, by rfl⟩ : syracuseStep 1531349 = 35891) (by norm_num)
theorem B1531373 : Blo 1020604 1531373 := bbase (se 3 (by rfl) ⟨287132, by rfl⟩ : syracuseStep 1531373 = 574265) (by norm_num)
theorem B1531397 : Blo 1020604 1531397 := bbase (se 4 (by rfl) ⟨143568, by rfl⟩ : syracuseStep 1531397 = 287137) (by norm_num)
theorem B1728013 : Blo 1020604 1728013 := bbase (se 3 (by rfl) ⟨324002, by rfl⟩ : syracuseStep 1728013 = 648005) (by norm_num)
theorem B1531421 : Blo 1020604 1531421 := bbase (se 3 (by rfl) ⟨287141, by rfl⟩ : syracuseStep 1531421 = 574283) (by norm_num)
theorem B1531445 : Blo 1020604 1531445 := bbase (se 5 (by rfl) ⟨71786, by rfl⟩ : syracuseStep 1531445 = 143573) (by norm_num)
theorem B2186813 : Blo 1020604 2186813 := bbase (se 3 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 2186813 = 820055) (by norm_num)
theorem B1531469 : Blo 1020604 1531469 := bbase (se 3 (by rfl) ⟨287150, by rfl⟩ : syracuseStep 1531469 = 574301) (by norm_num)
theorem B1531493 : Blo 1020604 1531493 := bbase (se 4 (by rfl) ⟨143577, by rfl⟩ : syracuseStep 1531493 = 287155) (by norm_num)
theorem B1728101 : Blo 1020604 1728101 := bbase (se 4 (by rfl) ⟨162009, by rfl⟩ : syracuseStep 1728101 = 324019) (by norm_num)
theorem B1531517 : Blo 1020604 1531517 := bbase (se 3 (by rfl) ⟨287159, by rfl⟩ : syracuseStep 1531517 = 574319) (by norm_num)
theorem B1531541 : Blo 1020604 1531541 := bbase (se 6 (by rfl) ⟨35895, by rfl⟩ : syracuseStep 1531541 = 71791) (by norm_num)
theorem B1531565 : Blo 1020604 1531565 := bbase (se 3 (by rfl) ⟨287168, by rfl⟩ : syracuseStep 1531565 = 574337) (by norm_num)
theorem B1531589 : Blo 1020604 1531589 := bbase (se 4 (by rfl) ⟨143586, by rfl⟩ : syracuseStep 1531589 = 287173) (by norm_num)
theorem B2907845 : Blo 1020604 2907845 := bbase (se 4 (by rfl) ⟨272610, by rfl⟩ : syracuseStep 2907845 = 545221) (by norm_num)
theorem B1531613 : Blo 1020604 1531613 := bbase (se 3 (by rfl) ⟨287177, by rfl⟩ : syracuseStep 1531613 = 574355) (by norm_num)
theorem B1728229 : Blo 1020604 1728229 := bbase (se 4 (by rfl) ⟨162021, by rfl⟩ : syracuseStep 1728229 = 324043) (by norm_num)
theorem B1531637 : Blo 1020604 1531637 := bbase (se 5 (by rfl) ⟨71795, by rfl⟩ : syracuseStep 1531637 = 143591) (by norm_num)
theorem B4906757 : Blo 1020604 4906757 := bbase (se 4 (by rfl) ⟨460008, by rfl⟩ : syracuseStep 4906757 = 920017) (by norm_num)
theorem B1531661 : Blo 1020604 1531661 := bbase (se 3 (by rfl) ⟨287186, by rfl⟩ : syracuseStep 1531661 = 574373) (by norm_num)
theorem B5168933 : Blo 1020604 5168933 := bbase (se 4 (by rfl) ⟨484587, by rfl⟩ : syracuseStep 5168933 = 969175) (by norm_num)
theorem B1531685 : Blo 1020604 1531685 := bbase (se 4 (by rfl) ⟨143595, by rfl⟩ : syracuseStep 1531685 = 287191) (by norm_num)
theorem B1531709 : Blo 1020604 1531709 := bbase (se 3 (by rfl) ⟨287195, by rfl⟩ : syracuseStep 1531709 = 574391) (by norm_num)
theorem B1662781 : Blo 1020604 1662781 := bbase (se 3 (by rfl) ⟨311771, by rfl⟩ : syracuseStep 1662781 = 623543) (by norm_num)
theorem B1728317 : Blo 1020604 1728317 := bbase (se 3 (by rfl) ⟨324059, by rfl⟩ : syracuseStep 1728317 = 648119) (by norm_num)
theorem B1531733 : Blo 1020604 1531733 := bbase (se 9 (by rfl) ⟨4487, by rfl⟩ : syracuseStep 1531733 = 8975) (by norm_num)
theorem B1531757 : Blo 1020604 1531757 := bbase (se 3 (by rfl) ⟨287204, by rfl⟩ : syracuseStep 1531757 = 574409) (by norm_num)
theorem B1531781 : Blo 1020604 1531781 := bbase (se 4 (by rfl) ⟨143604, by rfl⟩ : syracuseStep 1531781 = 287209) (by norm_num)
theorem B1531805 : Blo 1020604 1531805 := bbase (se 3 (by rfl) ⟨287213, by rfl⟩ : syracuseStep 1531805 = 574427) (by norm_num)
theorem B1531829 : Blo 1020604 1531829 := bbase (se 5 (by rfl) ⟨71804, by rfl⟩ : syracuseStep 1531829 = 143609) (by norm_num)
theorem B1728445 : Blo 1020604 1728445 := bbase (se 3 (by rfl) ⟨324083, by rfl⟩ : syracuseStep 1728445 = 648167) (by norm_num)
theorem B1531853 : Blo 1020604 1531853 := bbase (se 3 (by rfl) ⟨287222, by rfl⟩ : syracuseStep 1531853 = 574445) (by norm_num)
theorem B1531877 : Blo 1020604 1531877 := bbase (se 4 (by rfl) ⟨143613, by rfl⟩ : syracuseStep 1531877 = 287227) (by norm_num)
theorem B1531901 : Blo 1020604 1531901 := bbase (se 3 (by rfl) ⟨287231, by rfl⟩ : syracuseStep 1531901 = 574463) (by norm_num)
theorem B1531925 : Blo 1020604 1531925 := bbase (se 6 (by rfl) ⟨35904, by rfl⟩ : syracuseStep 1531925 = 71809) (by norm_num)
theorem B1728533 : Blo 1020604 1728533 := bbase (se 6 (by rfl) ⟨40512, by rfl⟩ : syracuseStep 1728533 = 81025) (by norm_num)
theorem B1531949 : Blo 1020604 1531949 := bbase (se 3 (by rfl) ⟨287240, by rfl⟩ : syracuseStep 1531949 = 574481) (by norm_num)
theorem B1531973 : Blo 1020604 1531973 := bbase (se 4 (by rfl) ⟨143622, by rfl⟩ : syracuseStep 1531973 = 287245) (by norm_num)
theorem B1531997 : Blo 1020604 1531997 := bbase (se 3 (by rfl) ⟨287249, by rfl⟩ : syracuseStep 1531997 = 574499) (by norm_num)
theorem B1532021 : Blo 1020604 1532021 := bbase (se 5 (by rfl) ⟨71813, by rfl⟩ : syracuseStep 1532021 = 143627) (by norm_num)
theorem B1532045 : Blo 1020604 1532045 := bbase (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) (by norm_num)
theorem B1106065 : Blo 1020604 1106065 := bbase (se 2 (by rfl) ⟨414774, by rfl⟩ : syracuseStep 1106065 = 829549) (by norm_num)
theorem B1728661 : Blo 1020604 1728661 := bbase (se 6 (by rfl) ⟨40515, by rfl⟩ : syracuseStep 1728661 = 81031) (by norm_num)
theorem B1532069 : Blo 1020604 1532069 := bbase (se 4 (by rfl) ⟨143631, by rfl⟩ : syracuseStep 1532069 = 287263) (by norm_num)
theorem B2187445 : Blo 1020604 2187445 := bbase (se 5 (by rfl) ⟨102536, by rfl⟩ : syracuseStep 2187445 = 205073) (by norm_num)
theorem B1532093 : Blo 1020604 1532093 := bbase (se 3 (by rfl) ⟨287267, by rfl⟩ : syracuseStep 1532093 = 574535) (by norm_num)
theorem B1532117 : Blo 1020604 1532117 := bbase (se 7 (by rfl) ⟨17954, by rfl⟩ : syracuseStep 1532117 = 35909) (by norm_num)
theorem B1532141 : Blo 1020604 1532141 := bbase (se 3 (by rfl) ⟨287276, by rfl⟩ : syracuseStep 1532141 = 574553) (by norm_num)
theorem B1728749 : Blo 1020604 1728749 := bbase (se 3 (by rfl) ⟨324140, by rfl⟩ : syracuseStep 1728749 = 648281) (by norm_num)
theorem B1532165 : Blo 1020604 1532165 := bbase (se 4 (by rfl) ⟨143640, by rfl⟩ : syracuseStep 1532165 = 287281) (by norm_num)
theorem B1532189 : Blo 1020604 1532189 := bbase (se 3 (by rfl) ⟨287285, by rfl⟩ : syracuseStep 1532189 = 574571) (by norm_num)
theorem B1532213 : Blo 1020604 1532213 := bbase (se 5 (by rfl) ⟨71822, by rfl⟩ : syracuseStep 1532213 = 143645) (by norm_num)
theorem B1663301 : Blo 1020604 1663301 := bbase (se 4 (by rfl) ⟨155934, by rfl⟩ : syracuseStep 1663301 = 311869) (by norm_num)
theorem B1532237 : Blo 1020604 1532237 := bbase (se 3 (by rfl) ⟨287294, by rfl⟩ : syracuseStep 1532237 = 574589) (by norm_num)
theorem B1532261 : Blo 1020604 1532261 := bbase (se 4 (by rfl) ⟨143649, by rfl⟩ : syracuseStep 1532261 = 287299) (by norm_num)
theorem B1728877 : Blo 1020604 1728877 := bbase (se 3 (by rfl) ⟨324164, by rfl⟩ : syracuseStep 1728877 = 648329) (by norm_num)
theorem B1532285 : Blo 1020604 1532285 := bbase (se 3 (by rfl) ⟨287303, by rfl⟩ : syracuseStep 1532285 = 574607) (by norm_num)
theorem B1532309 : Blo 1020604 1532309 := bbase (se 6 (by rfl) ⟨35913, by rfl⟩ : syracuseStep 1532309 = 71827) (by norm_num)
theorem B1532333 : Blo 1020604 1532333 := bbase (se 3 (by rfl) ⟨287312, by rfl⟩ : syracuseStep 1532333 = 574625) (by norm_num)
theorem B1532357 : Blo 1020604 1532357 := bbase (se 4 (by rfl) ⟨143658, by rfl⟩ : syracuseStep 1532357 = 287317) (by norm_num)
theorem B1728965 : Blo 1020604 1728965 := bbase (se 4 (by rfl) ⟨162090, by rfl⟩ : syracuseStep 1728965 = 324181) (by norm_num)
theorem B1532381 : Blo 1020604 1532381 := bbase (se 3 (by rfl) ⟨287321, by rfl⟩ : syracuseStep 1532381 = 574643) (by norm_num)
theorem B1532405 : Blo 1020604 1532405 := bbase (se 5 (by rfl) ⟨71831, by rfl⟩ : syracuseStep 1532405 = 143663) (by norm_num)
theorem B1532429 : Blo 1020604 1532429 := bbase (se 3 (by rfl) ⟨287330, by rfl⟩ : syracuseStep 1532429 = 574661) (by norm_num)
theorem B3105301 : Blo 1020604 3105301 := bbase (se 6 (by rfl) ⟨72780, by rfl⟩ : syracuseStep 3105301 = 145561) (by norm_num)
theorem B1532453 : Blo 1020604 1532453 := bbase (se 4 (by rfl) ⟨143667, by rfl⟩ : syracuseStep 1532453 = 287335) (by norm_num)
theorem B1532477 : Blo 1020604 1532477 := bbase (se 3 (by rfl) ⟨287339, by rfl⟩ : syracuseStep 1532477 = 574679) (by norm_num)
theorem B1532501 : Blo 1020604 1532501 := bbase (se 8 (by rfl) ⟨8979, by rfl⟩ : syracuseStep 1532501 = 17959) (by norm_num)
theorem B1532525 : Blo 1020604 1532525 := bbase (se 3 (by rfl) ⟨287348, by rfl⟩ : syracuseStep 1532525 = 574697) (by norm_num)
theorem B1532549 : Blo 1020604 1532549 := bbase (se 4 (by rfl) ⟨143676, by rfl⟩ : syracuseStep 1532549 = 287353) (by norm_num)
theorem B7365269 : Blo 1020604 7365269 := bbase (se 6 (by rfl) ⟨172623, by rfl⟩ : syracuseStep 7365269 = 345247) (by norm_num)
theorem B1532573 : Blo 1020604 1532573 := bbase (se 3 (by rfl) ⟨287357, by rfl⟩ : syracuseStep 1532573 = 574715) (by norm_num)
theorem B1532597 : Blo 1020604 1532597 := bbase (se 5 (by rfl) ⟨71840, by rfl⟩ : syracuseStep 1532597 = 143681) (by norm_num)
theorem B1532621 : Blo 1020604 1532621 := bbase (se 3 (by rfl) ⟨287366, by rfl⟩ : syracuseStep 1532621 = 574733) (by norm_num)
theorem B1532645 : Blo 1020604 1532645 := bbase (se 4 (by rfl) ⟨143685, by rfl⟩ : syracuseStep 1532645 = 287371) (by norm_num)
theorem B1532669 : Blo 1020604 1532669 := bbase (se 3 (by rfl) ⟨287375, by rfl⟩ : syracuseStep 1532669 = 574751) (by norm_num)
theorem B1532693 : Blo 1020604 1532693 := bbase (se 6 (by rfl) ⟨35922, by rfl⟩ : syracuseStep 1532693 = 71845) (by norm_num)
theorem B3498773 : Blo 1020604 3498773 := bbase (se 6 (by rfl) ⟨82002, by rfl⟩ : syracuseStep 3498773 = 164005) (by norm_num)
theorem B1532717 : Blo 1020604 1532717 := bbase (se 3 (by rfl) ⟨287384, by rfl⟩ : syracuseStep 1532717 = 574769) (by norm_num)
theorem B1532741 : Blo 1020604 1532741 := bbase (se 4 (by rfl) ⟨143694, by rfl⟩ : syracuseStep 1532741 = 287389) (by norm_num)
theorem B1532765 : Blo 1020604 1532765 := bbase (se 3 (by rfl) ⟨287393, by rfl⟩ : syracuseStep 1532765 = 574787) (by norm_num)
theorem B2909029 : Blo 1020604 2909029 := bbase (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) (by norm_num)
theorem B1532789 : Blo 1020604 1532789 := bbase (se 5 (by rfl) ⟨71849, by rfl⟩ : syracuseStep 1532789 = 143699) (by norm_num)
theorem B1532813 : Blo 1020604 1532813 := bbase (se 3 (by rfl) ⟨287402, by rfl⟩ : syracuseStep 1532813 = 574805) (by norm_num)
theorem B1532837 : Blo 1020604 1532837 := bbase (se 4 (by rfl) ⟨143703, by rfl⟩ : syracuseStep 1532837 = 287407) (by norm_num)
theorem B1532861 : Blo 1020604 1532861 := bbase (se 3 (by rfl) ⟨287411, by rfl⟩ : syracuseStep 1532861 = 574823) (by norm_num)
theorem B1532885 : Blo 1020604 1532885 := bbase (se 7 (by rfl) ⟨17963, by rfl⟩ : syracuseStep 1532885 = 35927) (by norm_num)
theorem B1532909 : Blo 1020604 1532909 := bbase (se 3 (by rfl) ⟨287420, by rfl⟩ : syracuseStep 1532909 = 574841) (by norm_num)
theorem B2909189 : Blo 1020604 2909189 := bbase (se 4 (by rfl) ⟨272736, by rfl⟩ : syracuseStep 2909189 = 545473) (by norm_num)
theorem B1532933 : Blo 1020604 1532933 := bbase (se 4 (by rfl) ⟨143712, by rfl⟩ : syracuseStep 1532933 = 287425) (by norm_num)
theorem B1532957 : Blo 1020604 1532957 := bbase (se 3 (by rfl) ⟨287429, by rfl⟩ : syracuseStep 1532957 = 574859) (by norm_num)
theorem B5170229 : Blo 1020604 5170229 := bbase (se 5 (by rfl) ⟨242354, by rfl⟩ : syracuseStep 5170229 = 484709) (by norm_num)
theorem B1532981 : Blo 1020604 1532981 := bbase (se 5 (by rfl) ⟨71858, by rfl⟩ : syracuseStep 1532981 = 143717) (by norm_num)
theorem B1533005 : Blo 1020604 1533005 := bbase (se 3 (by rfl) ⟨287438, by rfl⟩ : syracuseStep 1533005 = 574877) (by norm_num)
theorem B5825621 : Blo 1020604 5825621 := bbase (se 8 (by rfl) ⟨34134, by rfl⟩ : syracuseStep 5825621 = 68269) (by norm_num)
theorem B1533029 : Blo 1020604 1533029 := bbase (se 4 (by rfl) ⟨143721, by rfl⟩ : syracuseStep 1533029 = 287443) (by norm_num)
theorem B1533053 : Blo 1020604 1533053 := bbase (se 3 (by rfl) ⟨287447, by rfl⟩ : syracuseStep 1533053 = 574895) (by norm_num)
theorem B1533077 : Blo 1020604 1533077 := bbase (se 6 (by rfl) ⟨35931, by rfl⟩ : syracuseStep 1533077 = 71863) (by norm_num)
theorem B1533101 : Blo 1020604 1533101 := bbase (se 3 (by rfl) ⟨287456, by rfl⟩ : syracuseStep 1533101 = 574913) (by norm_num)
theorem B1533125 : Blo 1020604 1533125 := bbase (se 4 (by rfl) ⟨143730, by rfl⟩ : syracuseStep 1533125 = 287461) (by norm_num)
theorem B1533149 : Blo 1020604 1533149 := bbase (se 3 (by rfl) ⟨287465, by rfl⟩ : syracuseStep 1533149 = 574931) (by norm_num)
theorem B2909429 : Blo 1020604 2909429 := bbase (se 5 (by rfl) ⟨136379, by rfl⟩ : syracuseStep 2909429 = 272759) (by norm_num)
theorem B1533173 : Blo 1020604 1533173 := bbase (se 5 (by rfl) ⟨71867, by rfl⟩ : syracuseStep 1533173 = 143735) (by norm_num)
theorem B1533197 : Blo 1020604 1533197 := bbase (se 3 (by rfl) ⟨287474, by rfl⟩ : syracuseStep 1533197 = 574949) (by norm_num)
theorem B1533221 : Blo 1020604 1533221 := bbase (se 4 (by rfl) ⟨143739, by rfl⟩ : syracuseStep 1533221 = 287479) (by norm_num)
theorem B1533245 : Blo 1020604 1533245 := bbase (se 3 (by rfl) ⟨287483, by rfl⟩ : syracuseStep 1533245 = 574967) (by norm_num)
theorem B1402181 : Blo 1020604 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B1107277 : Blo 1020604 1107277 := bbase (se 3 (by rfl) ⟨207614, by rfl⟩ : syracuseStep 1107277 = 415229) (by norm_num)
theorem B1533269 : Blo 1020604 1533269 := bbase (se 12 (by rfl) ⟨561, by rfl⟩ : syracuseStep 1533269 = 1123) (by norm_num)
theorem B1533293 : Blo 1020604 1533293 := bbase (se 3 (by rfl) ⟨287492, by rfl⟩ : syracuseStep 1533293 = 574985) (by norm_num)
theorem B1533317 : Blo 1020604 1533317 := bbase (se 4 (by rfl) ⟨143748, by rfl⟩ : syracuseStep 1533317 = 287497) (by norm_num)
theorem B1533341 : Blo 1020604 1533341 := bbase (se 3 (by rfl) ⟨287501, by rfl⟩ : syracuseStep 1533341 = 575003) (by norm_num)
theorem B2909621 : Blo 1020604 2909621 := bbase (se 5 (by rfl) ⟨136388, by rfl⟩ : syracuseStep 2909621 = 272777) (by norm_num)
theorem B1533365 : Blo 1020604 1533365 := bbase (se 5 (by rfl) ⟨71876, by rfl⟩ : syracuseStep 1533365 = 143753) (by norm_num)
theorem B1533389 : Blo 1020604 1533389 := bbase (se 3 (by rfl) ⟨287510, by rfl⟩ : syracuseStep 1533389 = 575021) (by norm_num)
theorem B1533413 : Blo 1020604 1533413 := bbase (se 4 (by rfl) ⟨143757, by rfl⟩ : syracuseStep 1533413 = 287515) (by norm_num)
theorem B1533437 : Blo 1020604 1533437 := bbase (se 3 (by rfl) ⟨287519, by rfl⟩ : syracuseStep 1533437 = 575039) (by norm_num)
theorem B1533461 : Blo 1020604 1533461 := bbase (se 6 (by rfl) ⟨35940, by rfl⟩ : syracuseStep 1533461 = 71881) (by norm_num)
theorem B1533485 : Blo 1020604 1533485 := bbase (se 3 (by rfl) ⟨287528, by rfl⟩ : syracuseStep 1533485 = 575057) (by norm_num)
theorem B1402429 : Blo 1020604 1402429 := bbase (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) (by norm_num)
theorem B1533509 : Blo 1020604 1533509 := bbase (se 4 (by rfl) ⟨143766, by rfl⟩ : syracuseStep 1533509 = 287533) (by norm_num)
theorem B1533533 : Blo 1020604 1533533 := bbase (se 3 (by rfl) ⟨287537, by rfl⟩ : syracuseStep 1533533 = 575075) (by norm_num)
theorem B1533557 : Blo 1020604 1533557 := bbase (se 5 (by rfl) ⟨71885, by rfl⟩ : syracuseStep 1533557 = 143771) (by norm_num)
theorem B1533581 : Blo 1020604 1533581 := bbase (se 3 (by rfl) ⟨287546, by rfl⟩ : syracuseStep 1533581 = 575093) (by norm_num)
theorem B1533605 : Blo 1020604 1533605 := bbase (se 4 (by rfl) ⟨143775, by rfl⟩ : syracuseStep 1533605 = 287551) (by norm_num)
theorem B1533629 : Blo 1020604 1533629 := bbase (se 3 (by rfl) ⟨287555, by rfl⟩ : syracuseStep 1533629 = 575111) (by norm_num)
theorem B3106517 : Blo 1020604 3106517 := bbase (se 7 (by rfl) ⟨36404, by rfl⟩ : syracuseStep 3106517 = 72809) (by norm_num)
theorem B1533653 : Blo 1020604 1533653 := bbase (se 7 (by rfl) ⟨17972, by rfl⟩ : syracuseStep 1533653 = 35945) (by norm_num)
theorem B1533677 : Blo 1020604 1533677 := bbase (se 3 (by rfl) ⟨287564, by rfl⟩ : syracuseStep 1533677 = 575129) (by norm_num)
theorem B1533701 : Blo 1020604 1533701 := bbase (se 4 (by rfl) ⟨143784, by rfl⟩ : syracuseStep 1533701 = 287569) (by norm_num)
theorem B1533725 : Blo 1020604 1533725 := bbase (se 3 (by rfl) ⟨287573, by rfl⟩ : syracuseStep 1533725 = 575147) (by norm_num)
theorem B1533749 : Blo 1020604 1533749 := bbase (se 5 (by rfl) ⟨71894, by rfl⟩ : syracuseStep 1533749 = 143789) (by norm_num)
theorem B1533773 : Blo 1020604 1533773 := bbase (se 3 (by rfl) ⟨287582, by rfl⟩ : syracuseStep 1533773 = 575165) (by norm_num)
theorem B1533797 : Blo 1020604 1533797 := bbase (se 4 (by rfl) ⟨143793, by rfl⟩ : syracuseStep 1533797 = 287587) (by norm_num)
theorem B1533821 : Blo 1020604 1533821 := bbase (se 3 (by rfl) ⟨287591, by rfl⟩ : syracuseStep 1533821 = 575183) (by norm_num)
theorem B1533845 : Blo 1020604 1533845 := bbase (se 6 (by rfl) ⟨35949, by rfl⟩ : syracuseStep 1533845 = 71899) (by norm_num)
theorem B1533869 : Blo 1020604 1533869 := bbase (se 3 (by rfl) ⟨287600, by rfl⟩ : syracuseStep 1533869 = 575201) (by norm_num)
theorem B1533893 : Blo 1020604 1533893 := bbase (se 4 (by rfl) ⟨143802, by rfl⟩ : syracuseStep 1533893 = 287605) (by norm_num)
theorem B1533917 : Blo 1020604 1533917 := bbase (se 3 (by rfl) ⟨287609, by rfl⟩ : syracuseStep 1533917 = 575219) (by norm_num)
theorem B1533941 : Blo 1020604 1533941 := bbase (se 5 (by rfl) ⟨71903, by rfl⟩ : syracuseStep 1533941 = 143807) (by norm_num)
theorem B1533965 : Blo 1020604 1533965 := bbase (se 3 (by rfl) ⟨287618, by rfl⟩ : syracuseStep 1533965 = 575237) (by norm_num)
theorem B1533989 : Blo 1020604 1533989 := bbase (se 4 (by rfl) ⟨143811, by rfl⟩ : syracuseStep 1533989 = 287623) (by norm_num)
theorem B1534013 : Blo 1020604 1534013 := bbase (se 3 (by rfl) ⟨287627, by rfl⟩ : syracuseStep 1534013 = 575255) (by norm_num)
theorem B1534037 : Blo 1020604 1534037 := bbase (se 8 (by rfl) ⟨8988, by rfl⟩ : syracuseStep 1534037 = 17977) (by norm_num)
theorem B1534061 : Blo 1020604 1534061 := bbase (se 3 (by rfl) ⟨287636, by rfl⟩ : syracuseStep 1534061 = 575273) (by norm_num)
theorem B1534085 : Blo 1020604 1534085 := bbase (se 4 (by rfl) ⟨143820, by rfl⟩ : syracuseStep 1534085 = 287641) (by norm_num)
theorem B1534109 : Blo 1020604 1534109 := bbase (se 3 (by rfl) ⟨287645, by rfl⟩ : syracuseStep 1534109 = 575291) (by norm_num)
theorem B1534133 : Blo 1020604 1534133 := bbase (se 5 (by rfl) ⟨71912, by rfl⟩ : syracuseStep 1534133 = 143825) (by norm_num)
theorem B1534157 : Blo 1020604 1534157 := bbase (se 3 (by rfl) ⟨287654, by rfl⟩ : syracuseStep 1534157 = 575309) (by norm_num)
theorem B1534181 : Blo 1020604 1534181 := bbase (se 4 (by rfl) ⟨143829, by rfl⟩ : syracuseStep 1534181 = 287659) (by norm_num)
theorem B1534205 : Blo 1020604 1534205 := bbase (se 3 (by rfl) ⟨287663, by rfl⟩ : syracuseStep 1534205 = 575327) (by norm_num)
theorem B1534229 : Blo 1020604 1534229 := bbase (se 6 (by rfl) ⟨35958, by rfl⟩ : syracuseStep 1534229 = 71917) (by norm_num)
theorem B1534253 : Blo 1020604 1534253 := bbase (se 3 (by rfl) ⟨287672, by rfl⟩ : syracuseStep 1534253 = 575345) (by norm_num)
theorem B5171525 : Blo 1020604 5171525 := bbase (se 4 (by rfl) ⟨484830, by rfl⟩ : syracuseStep 5171525 = 969661) (by norm_num)
theorem B1534277 : Blo 1020604 1534277 := bbase (se 4 (by rfl) ⟨143838, by rfl⟩ : syracuseStep 1534277 = 287677) (by norm_num)
theorem B1534301 : Blo 1020604 1534301 := bbase (se 3 (by rfl) ⟨287681, by rfl⟩ : syracuseStep 1534301 = 575363) (by norm_num)
theorem B1534325 : Blo 1020604 1534325 := bbase (se 5 (by rfl) ⟨71921, by rfl⟩ : syracuseStep 1534325 = 143843) (by norm_num)
theorem B1534349 : Blo 1020604 1534349 := bbase (se 3 (by rfl) ⟨287690, by rfl⟩ : syracuseStep 1534349 = 575381) (by norm_num)
theorem B2910613 : Blo 1020604 2910613 := bbase (se 6 (by rfl) ⟨68217, by rfl⟩ : syracuseStep 2910613 = 136435) (by norm_num)
theorem B1534373 : Blo 1020604 1534373 := bbase (se 4 (by rfl) ⟨143847, by rfl⟩ : syracuseStep 1534373 = 287695) (by norm_num)
theorem B1534397 : Blo 1020604 1534397 := bbase (se 3 (by rfl) ⟨287699, by rfl⟩ : syracuseStep 1534397 = 575399) (by norm_num)
theorem B1534421 : Blo 1020604 1534421 := bbase (se 7 (by rfl) ⟨17981, by rfl⟩ : syracuseStep 1534421 = 35963) (by norm_num)
theorem B1534445 : Blo 1020604 1534445 := bbase (se 3 (by rfl) ⟨287708, by rfl⟩ : syracuseStep 1534445 = 575417) (by norm_num)
theorem B1534469 : Blo 1020604 1534469 := bbase (se 4 (by rfl) ⟨143856, by rfl⟩ : syracuseStep 1534469 = 287713) (by norm_num)
theorem B1534493 : Blo 1020604 1534493 := bbase (se 3 (by rfl) ⟨287717, by rfl⟩ : syracuseStep 1534493 = 575435) (by norm_num)
theorem B1534517 : Blo 1020604 1534517 := bbase (se 5 (by rfl) ⟨71930, by rfl⟩ : syracuseStep 1534517 = 143861) (by norm_num)
theorem B1534541 : Blo 1020604 1534541 := bbase (se 3 (by rfl) ⟨287726, by rfl⟩ : syracuseStep 1534541 = 575453) (by norm_num)
theorem B1534565 : Blo 1020604 1534565 := bbase (se 4 (by rfl) ⟨143865, by rfl⟩ : syracuseStep 1534565 = 287731) (by norm_num)
theorem B1534589 : Blo 1020604 1534589 := bbase (se 3 (by rfl) ⟨287735, by rfl⟩ : syracuseStep 1534589 = 575471) (by norm_num)
theorem B1534613 : Blo 1020604 1534613 := bbase (se 6 (by rfl) ⟨35967, by rfl⟩ : syracuseStep 1534613 = 71935) (by norm_num)
theorem B1534637 : Blo 1020604 1534637 := bbase (se 3 (by rfl) ⟨287744, by rfl⟩ : syracuseStep 1534637 = 575489) (by norm_num)
theorem B1534661 : Blo 1020604 1534661 := bbase (se 4 (by rfl) ⟨143874, by rfl⟩ : syracuseStep 1534661 = 287749) (by norm_num)
theorem B1534685 : Blo 1020604 1534685 := bbase (se 3 (by rfl) ⟨287753, by rfl⟩ : syracuseStep 1534685 = 575507) (by norm_num)
theorem B1534709 : Blo 1020604 1534709 := bbase (se 5 (by rfl) ⟨71939, by rfl⟩ : syracuseStep 1534709 = 143879) (by norm_num)
theorem B1534733 : Blo 1020604 1534733 := bbase (se 3 (by rfl) ⟨287762, by rfl⟩ : syracuseStep 1534733 = 575525) (by norm_num)
theorem B1534757 : Blo 1020604 1534757 := bbase (se 4 (by rfl) ⟨143883, by rfl⟩ : syracuseStep 1534757 = 287767) (by norm_num)
theorem B1534781 : Blo 1020604 1534781 := bbase (se 3 (by rfl) ⟨287771, by rfl⟩ : syracuseStep 1534781 = 575543) (by norm_num)
theorem B1534805 : Blo 1020604 1534805 := bbase (se 9 (by rfl) ⟨4496, by rfl⟩ : syracuseStep 1534805 = 8993) (by norm_num)
theorem B1534829 : Blo 1020604 1534829 := bbase (se 3 (by rfl) ⟨287780, by rfl⟩ : syracuseStep 1534829 = 575561) (by norm_num)
theorem B1534853 : Blo 1020604 1534853 := bbase (se 4 (by rfl) ⟨143892, by rfl⟩ : syracuseStep 1534853 = 287785) (by norm_num)
theorem B1534877 : Blo 1020604 1534877 := bbase (se 3 (by rfl) ⟨287789, by rfl⟩ : syracuseStep 1534877 = 575579) (by norm_num)
theorem B1534901 : Blo 1020604 1534901 := bbase (se 5 (by rfl) ⟨71948, by rfl⟩ : syracuseStep 1534901 = 143897) (by norm_num)
theorem B2583485 : Blo 1020604 2583485 := bbase (se 3 (by rfl) ⟨484403, by rfl⟩ : syracuseStep 2583485 = 968807) (by norm_num)
theorem B1534925 : Blo 1020604 1534925 := bbase (se 3 (by rfl) ⟨287798, by rfl⟩ : syracuseStep 1534925 = 575597) (by norm_num)
theorem B1534949 : Blo 1020604 1534949 := bbase (se 4 (by rfl) ⟨143901, by rfl⟩ : syracuseStep 1534949 = 287803) (by norm_num)
theorem B1534973 : Blo 1020604 1534973 := bbase (se 3 (by rfl) ⟨287807, by rfl⟩ : syracuseStep 1534973 = 575615) (by norm_num)
theorem B1534997 : Blo 1020604 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B5237797 : Blo 1020604 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B1535021 : Blo 1020604 1535021 := bbase (se 3 (by rfl) ⟨287816, by rfl⟩ : syracuseStep 1535021 = 575633) (by norm_num)
theorem B1535045 : Blo 1020604 1535045 := bbase (se 4 (by rfl) ⟨143910, by rfl⟩ : syracuseStep 1535045 = 287821) (by norm_num)
theorem B1535069 : Blo 1020604 1535069 := bbase (se 3 (by rfl) ⟨287825, by rfl⟩ : syracuseStep 1535069 = 575651) (by norm_num)
theorem B6548597 : Blo 1020604 6548597 := bbase (se 5 (by rfl) ⟨306965, by rfl⟩ : syracuseStep 6548597 = 613931) (by norm_num)
theorem B1535093 : Blo 1020604 1535093 := bbase (se 5 (by rfl) ⟨71957, by rfl⟩ : syracuseStep 1535093 = 143915) (by norm_num)
theorem B2583677 : Blo 1020604 2583677 := bbase (se 3 (by rfl) ⟨484439, by rfl⟩ : syracuseStep 2583677 = 968879) (by norm_num)
theorem B1535117 : Blo 1020604 1535117 := bbase (se 3 (by rfl) ⟨287834, by rfl⟩ : syracuseStep 1535117 = 575669) (by norm_num)
theorem B3599509 : Blo 1020604 3599509 := bbase (se 6 (by rfl) ⟨84363, by rfl⟩ : syracuseStep 3599509 = 168727) (by norm_num)
theorem B1535141 : Blo 1020604 1535141 := bbase (se 4 (by rfl) ⟨143919, by rfl⟩ : syracuseStep 1535141 = 287839) (by norm_num)
theorem B1535165 : Blo 1020604 1535165 := bbase (se 3 (by rfl) ⟨287843, by rfl⟩ : syracuseStep 1535165 = 575687) (by norm_num)
theorem B1535189 : Blo 1020604 1535189 := bbase (se 7 (by rfl) ⟨17990, by rfl⟩ : syracuseStep 1535189 = 35981) (by norm_num)
theorem B1535213 : Blo 1020604 1535213 := bbase (se 3 (by rfl) ⟨287852, by rfl⟩ : syracuseStep 1535213 = 575705) (by norm_num)
theorem B1535237 : Blo 1020604 1535237 := bbase (se 4 (by rfl) ⟨143928, by rfl⟩ : syracuseStep 1535237 = 287857) (by norm_num)
theorem B1535261 : Blo 1020604 1535261 := bbase (se 3 (by rfl) ⟨287861, by rfl⟩ : syracuseStep 1535261 = 575723) (by norm_num)
theorem B1535285 : Blo 1020604 1535285 := bbase (se 5 (by rfl) ⟨71966, by rfl⟩ : syracuseStep 1535285 = 143933) (by norm_num)
theorem B1535309 : Blo 1020604 1535309 := bbase (se 3 (by rfl) ⟨287870, by rfl⟩ : syracuseStep 1535309 = 575741) (by norm_num)
theorem B1535333 : Blo 1020604 1535333 := bbase (se 4 (by rfl) ⟨143937, by rfl⟩ : syracuseStep 1535333 = 287875) (by norm_num)
theorem B1535357 : Blo 1020604 1535357 := bbase (se 3 (by rfl) ⟨287879, by rfl⟩ : syracuseStep 1535357 = 575759) (by norm_num)
theorem B1535381 : Blo 1020604 1535381 := bbase (se 6 (by rfl) ⟨35985, by rfl⟩ : syracuseStep 1535381 = 71971) (by norm_num)
theorem B1535405 : Blo 1020604 1535405 := bbase (se 3 (by rfl) ⟨287888, by rfl⟩ : syracuseStep 1535405 = 575777) (by norm_num)
theorem B1535429 : Blo 1020604 1535429 := bbase (se 4 (by rfl) ⟨143946, by rfl⟩ : syracuseStep 1535429 = 287893) (by norm_num)
theorem B2584021 : Blo 1020604 2584021 := bbase (se 7 (by rfl) ⟨30281, by rfl⟩ : syracuseStep 2584021 = 60563) (by norm_num)
theorem B1535453 : Blo 1020604 1535453 := bbase (se 3 (by rfl) ⟨287897, by rfl⟩ : syracuseStep 1535453 = 575795) (by norm_num)
theorem B2911717 : Blo 1020604 2911717 := bbase (se 4 (by rfl) ⟨272973, by rfl⟩ : syracuseStep 2911717 = 545947) (by norm_num)
theorem B1535477 : Blo 1020604 1535477 := bbase (se 5 (by rfl) ⟨71975, by rfl⟩ : syracuseStep 1535477 = 143951) (by norm_num)
theorem B3272197 : Blo 1020604 3272197 := bbase (se 4 (by rfl) ⟨306768, by rfl⟩ : syracuseStep 3272197 = 613537) (by norm_num)
theorem B1535501 : Blo 1020604 1535501 := bbase (se 3 (by rfl) ⟨287906, by rfl⟩ : syracuseStep 1535501 = 575813) (by norm_num)
theorem B1535525 : Blo 1020604 1535525 := bbase (se 4 (by rfl) ⟨143955, by rfl⟩ : syracuseStep 1535525 = 287911) (by norm_num)
theorem B1535549 : Blo 1020604 1535549 := bbase (se 3 (by rfl) ⟨287915, by rfl⟩ : syracuseStep 1535549 = 575831) (by norm_num)
theorem B2584133 : Blo 1020604 2584133 := bbase (se 4 (by rfl) ⟨242262, by rfl⟩ : syracuseStep 2584133 = 484525) (by norm_num)
theorem B5172821 : Blo 1020604 5172821 := bbase (se 8 (by rfl) ⟨30309, by rfl⟩ : syracuseStep 5172821 = 60619) (by norm_num)
theorem B1535573 : Blo 1020604 1535573 := bbase (se 8 (by rfl) ⟨8997, by rfl⟩ : syracuseStep 1535573 = 17995) (by norm_num)
theorem B1535597 : Blo 1020604 1535597 := bbase (se 3 (by rfl) ⟨287924, by rfl⟩ : syracuseStep 1535597 = 575849) (by norm_num)
theorem B1535621 : Blo 1020604 1535621 := bbase (se 4 (by rfl) ⟨143964, by rfl⟩ : syracuseStep 1535621 = 287929) (by norm_num)
theorem B1535645 : Blo 1020604 1535645 := bbase (se 3 (by rfl) ⟨287933, by rfl⟩ : syracuseStep 1535645 = 575867) (by norm_num)
theorem B1535669 : Blo 1020604 1535669 := bbase (se 5 (by rfl) ⟨71984, by rfl⟩ : syracuseStep 1535669 = 143969) (by norm_num)
theorem B4419269 : Blo 1020604 4419269 := bbase (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) (by norm_num)
theorem B1535693 : Blo 1020604 1535693 := bbase (se 3 (by rfl) ⟨287942, by rfl⟩ : syracuseStep 1535693 = 575885) (by norm_num)
theorem B1535717 : Blo 1020604 1535717 := bbase (se 4 (by rfl) ⟨143973, by rfl⟩ : syracuseStep 1535717 = 287947) (by norm_num)
theorem B1535741 : Blo 1020604 1535741 := bbase (se 3 (by rfl) ⟨287951, by rfl⟩ : syracuseStep 1535741 = 575903) (by norm_num)
theorem B2584325 : Blo 1020604 2584325 := bbase (se 4 (by rfl) ⟨242280, by rfl⟩ : syracuseStep 2584325 = 484561) (by norm_num)
theorem B1535765 : Blo 1020604 1535765 := bbase (se 6 (by rfl) ⟨35994, by rfl⟩ : syracuseStep 1535765 = 71989) (by norm_num)
theorem B1535789 : Blo 1020604 1535789 := bbase (se 3 (by rfl) ⟨287960, by rfl⟩ : syracuseStep 1535789 = 575921) (by norm_num)
theorem B1535813 : Blo 1020604 1535813 := bbase (se 4 (by rfl) ⟨143982, by rfl⟩ : syracuseStep 1535813 = 287965) (by norm_num)
theorem B1535837 : Blo 1020604 1535837 := bbase (se 3 (by rfl) ⟨287969, by rfl⟩ : syracuseStep 1535837 = 575939) (by norm_num)
theorem B1535861 : Blo 1020604 1535861 := bbase (se 5 (by rfl) ⟨71993, by rfl⟩ : syracuseStep 1535861 = 143987) (by norm_num)
theorem B1535885 : Blo 1020604 1535885 := bbase (se 3 (by rfl) ⟨287978, by rfl⟩ : syracuseStep 1535885 = 575957) (by norm_num)
theorem B1535909 : Blo 1020604 1535909 := bbase (se 4 (by rfl) ⟨143991, by rfl⟩ : syracuseStep 1535909 = 287983) (by norm_num)
theorem B1535933 : Blo 1020604 1535933 := bbase (se 3 (by rfl) ⟨287987, by rfl⟩ : syracuseStep 1535933 = 575975) (by norm_num)
theorem B1535957 : Blo 1020604 1535957 := bbase (se 7 (by rfl) ⟨17999, by rfl⟩ : syracuseStep 1535957 = 35999) (by norm_num)
theorem B1535981 : Blo 1020604 1535981 := bbase (se 3 (by rfl) ⟨287996, by rfl⟩ : syracuseStep 1535981 = 575993) (by norm_num)
theorem B1536005 : Blo 1020604 1536005 := bbase (se 4 (by rfl) ⟨144000, by rfl⟩ : syracuseStep 1536005 = 288001) (by norm_num)
theorem B1536029 : Blo 1020604 1536029 := bbase (se 3 (by rfl) ⟨288005, by rfl⟩ : syracuseStep 1536029 = 576011) (by norm_num)
theorem B1536053 : Blo 1020604 1536053 := bbase (se 5 (by rfl) ⟨72002, by rfl⟩ : syracuseStep 1536053 = 144005) (by norm_num)
theorem B1536077 : Blo 1020604 1536077 := bbase (se 3 (by rfl) ⟨288014, by rfl⟩ : syracuseStep 1536077 = 576029) (by norm_num)
theorem B2584669 : Blo 1020604 2584669 := bbase (se 3 (by rfl) ⟨484625, by rfl⟩ : syracuseStep 2584669 = 969251) (by norm_num)
theorem B1536101 : Blo 1020604 1536101 := bbase (se 4 (by rfl) ⟨144009, by rfl⟩ : syracuseStep 1536101 = 288019) (by norm_num)
theorem B10514549 : Blo 1020604 10514549 := bbase (se 5 (by rfl) ⟨492869, by rfl⟩ : syracuseStep 10514549 = 985739) (by norm_num)
theorem B1536125 : Blo 1020604 1536125 := bbase (se 3 (by rfl) ⟨288023, by rfl⟩ : syracuseStep 1536125 = 576047) (by norm_num)
theorem B1536149 : Blo 1020604 1536149 := bbase (se 6 (by rfl) ⟨36003, by rfl⟩ : syracuseStep 1536149 = 72007) (by norm_num)
theorem B1536173 : Blo 1020604 1536173 := bbase (se 3 (by rfl) ⟨288032, by rfl⟩ : syracuseStep 1536173 = 576065) (by norm_num)
theorem B1536197 : Blo 1020604 1536197 := bbase (se 4 (by rfl) ⟨144018, by rfl⟩ : syracuseStep 1536197 = 288037) (by norm_num)
theorem B2584781 : Blo 1020604 2584781 := bbase (se 3 (by rfl) ⟨484646, by rfl⟩ : syracuseStep 2584781 = 969293) (by norm_num)
theorem B1536221 : Blo 1020604 1536221 := bbase (se 3 (by rfl) ⟨288041, by rfl⟩ : syracuseStep 1536221 = 576083) (by norm_num)
theorem B1536245 : Blo 1020604 1536245 := bbase (se 5 (by rfl) ⟨72011, by rfl⟩ : syracuseStep 1536245 = 144023) (by norm_num)
theorem B1536269 : Blo 1020604 1536269 := bbase (se 3 (by rfl) ⟨288050, by rfl⟩ : syracuseStep 1536269 = 576101) (by norm_num)
theorem B3502373 : Blo 1020604 3502373 := bbase (se 4 (by rfl) ⟨328347, by rfl⟩ : syracuseStep 3502373 = 656695) (by norm_num)
theorem B1536293 : Blo 1020604 1536293 := bbase (se 4 (by rfl) ⟨144027, by rfl⟩ : syracuseStep 1536293 = 288055) (by norm_num)
theorem B1536317 : Blo 1020604 1536317 := bbase (se 3 (by rfl) ⟨288059, by rfl⟩ : syracuseStep 1536317 = 576119) (by norm_num)
theorem B1536341 : Blo 1020604 1536341 := bbase (se 10 (by rfl) ⟨2250, by rfl⟩ : syracuseStep 1536341 = 4501) (by norm_num)
theorem B1536365 : Blo 1020604 1536365 := bbase (se 3 (by rfl) ⟨288068, by rfl⟩ : syracuseStep 1536365 = 576137) (by norm_num)
theorem B1536389 : Blo 1020604 1536389 := bbase (se 4 (by rfl) ⟨144036, by rfl⟩ : syracuseStep 1536389 = 288073) (by norm_num)
theorem B2584973 : Blo 1020604 2584973 := bbase (se 3 (by rfl) ⟨484682, by rfl⟩ : syracuseStep 2584973 = 969365) (by norm_num)
theorem B2453917 : Blo 1020604 2453917 := bbase (se 3 (by rfl) ⟨460109, by rfl⟩ : syracuseStep 2453917 = 920219) (by norm_num)
theorem B1536413 : Blo 1020604 1536413 := bbase (se 3 (by rfl) ⟨288077, by rfl⟩ : syracuseStep 1536413 = 576155) (by norm_num)
theorem B1536437 : Blo 1020604 1536437 := bbase (se 5 (by rfl) ⟨72020, by rfl⟩ : syracuseStep 1536437 = 144041) (by norm_num)
theorem B1536461 : Blo 1020604 1536461 := bbase (se 3 (by rfl) ⟨288086, by rfl⟩ : syracuseStep 1536461 = 576173) (by norm_num)
theorem B1536485 : Blo 1020604 1536485 := bbase (se 4 (by rfl) ⟨144045, by rfl⟩ : syracuseStep 1536485 = 288091) (by norm_num)
theorem B1536509 : Blo 1020604 1536509 := bbase (se 3 (by rfl) ⟨288095, by rfl⟩ : syracuseStep 1536509 = 576191) (by norm_num)
theorem B1536533 : Blo 1020604 1536533 := bbase (se 6 (by rfl) ⟨36012, by rfl⟩ : syracuseStep 1536533 = 72025) (by norm_num)
theorem B1536557 : Blo 1020604 1536557 := bbase (se 3 (by rfl) ⟨288104, by rfl⟩ : syracuseStep 1536557 = 576209) (by norm_num)
theorem B1536581 : Blo 1020604 1536581 := bbase (se 4 (by rfl) ⟨144054, by rfl⟩ : syracuseStep 1536581 = 288109) (by norm_num)
theorem B1536605 : Blo 1020604 1536605 := bbase (se 3 (by rfl) ⟨288113, by rfl⟩ : syracuseStep 1536605 = 576227) (by norm_num)
theorem B1536629 : Blo 1020604 1536629 := bbase (se 5 (by rfl) ⟨72029, by rfl⟩ : syracuseStep 1536629 = 144059) (by norm_num)
theorem B1536653 : Blo 1020604 1536653 := bbase (se 3 (by rfl) ⟨288122, by rfl⟩ : syracuseStep 1536653 = 576245) (by norm_num)
theorem B1536677 : Blo 1020604 1536677 := bbase (se 4 (by rfl) ⟨144063, by rfl⟩ : syracuseStep 1536677 = 288127) (by norm_num)
theorem B1536701 : Blo 1020604 1536701 := bbase (se 3 (by rfl) ⟨288131, by rfl⟩ : syracuseStep 1536701 = 576263) (by norm_num)
theorem B11072213 : Blo 1020604 11072213 := bbase (se 7 (by rfl) ⟨129752, by rfl⟩ : syracuseStep 11072213 = 259505) (by norm_num)
theorem B1536725 : Blo 1020604 1536725 := bbase (se 7 (by rfl) ⟨18008, by rfl⟩ : syracuseStep 1536725 = 36017) (by norm_num)
theorem B2585317 : Blo 1020604 2585317 := bbase (se 4 (by rfl) ⟨242373, by rfl⟩ : syracuseStep 2585317 = 484747) (by norm_num)
theorem B1536749 : Blo 1020604 1536749 := bbase (se 3 (by rfl) ⟨288140, by rfl⟩ : syracuseStep 1536749 = 576281) (by norm_num)
theorem B2487029 : Blo 1020604 2487029 := bbase (se 5 (by rfl) ⟨116579, by rfl⟩ : syracuseStep 2487029 = 233159) (by norm_num)
theorem B1536773 : Blo 1020604 1536773 := bbase (se 4 (by rfl) ⟨144072, by rfl⟩ : syracuseStep 1536773 = 288145) (by norm_num)
theorem B2454293 : Blo 1020604 2454293 := bbase (se 6 (by rfl) ⟨57522, by rfl⟩ : syracuseStep 2454293 = 115045) (by norm_num)
theorem B2519837 : Blo 1020604 2519837 := bbase (se 3 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 2519837 = 944939) (by norm_num)
theorem B1536797 : Blo 1020604 1536797 := bbase (se 3 (by rfl) ⟨288149, by rfl⟩ : syracuseStep 1536797 = 576299) (by norm_num)
theorem B1536821 : Blo 1020604 1536821 := bbase (se 5 (by rfl) ⟨72038, by rfl⟩ : syracuseStep 1536821 = 144077) (by norm_num)
theorem B1536845 : Blo 1020604 1536845 := bbase (se 3 (by rfl) ⟨288158, by rfl⟩ : syracuseStep 1536845 = 576317) (by norm_num)
theorem B2585429 : Blo 1020604 2585429 := bbase (se 9 (by rfl) ⟨7574, by rfl⟩ : syracuseStep 2585429 = 15149) (by norm_num)
theorem B26178389 : Blo 1020604 26178389 := bbase (se 9 (by rfl) ⟨76694, by rfl⟩ : syracuseStep 26178389 = 153389) (by norm_num)
theorem B13103957 : Blo 1020604 13103957 := bbase (se 9 (by rfl) ⟨38390, by rfl⟩ : syracuseStep 13103957 = 76781) (by norm_num)
theorem B5174117 : Blo 1020604 5174117 := bbase (se 4 (by rfl) ⟨485073, by rfl⟩ : syracuseStep 5174117 = 970147) (by norm_num)
theorem B1536869 : Blo 1020604 1536869 := bbase (se 4 (by rfl) ⟨144081, by rfl⟩ : syracuseStep 1536869 = 288163) (by norm_num)
theorem B1536893 : Blo 1020604 1536893 := bbase (se 3 (by rfl) ⟨288167, by rfl⟩ : syracuseStep 1536893 = 576335) (by norm_num)
theorem B2913221 : Blo 1020604 2913221 := bbase (se 4 (by rfl) ⟨273114, by rfl⟩ : syracuseStep 2913221 = 546229) (by norm_num)
theorem B3109877 : Blo 1020604 3109877 := bbase (se 5 (by rfl) ⟨145775, by rfl⟩ : syracuseStep 3109877 = 291551) (by norm_num)
theorem B2585621 : Blo 1020604 2585621 := bbase (se 6 (by rfl) ⟨60600, by rfl⟩ : syracuseStep 2585621 = 121201) (by norm_num)
theorem B2946133 : Blo 1020604 2946133 := bbase (se 8 (by rfl) ⟨17262, by rfl⟩ : syracuseStep 2946133 = 34525) (by norm_num)
theorem B1635509 : Blo 1020604 1635509 := bbase (se 5 (by rfl) ⟨76664, by rfl⟩ : syracuseStep 1635509 = 153329) (by norm_num)
theorem B2454725 : Blo 1020604 2454725 := bbase (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) (by norm_num)
theorem B1635637 : Blo 1020604 1635637 := bbase (se 5 (by rfl) ⟨76670, by rfl⟩ : syracuseStep 1635637 = 153341) (by norm_num)
theorem B2585965 : Blo 1020604 2585965 := bbase (se 3 (by rfl) ⟨484868, by rfl⟩ : syracuseStep 2585965 = 969737) (by norm_num)
theorem B2586077 : Blo 1020604 2586077 := bbase (se 3 (by rfl) ⟨484889, by rfl⟩ : syracuseStep 2586077 = 969779) (by norm_num)
theorem B3929717 : Blo 1020604 3929717 := bbase (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) (by norm_num)
theorem B2619013 : Blo 1020604 2619013 := bbase (se 4 (by rfl) ⟨245532, by rfl⟩ : syracuseStep 2619013 = 491065) (by norm_num)
theorem B2586269 : Blo 1020604 2586269 := bbase (se 3 (by rfl) ⟨484925, by rfl⟩ : syracuseStep 2586269 = 969851) (by norm_num)
theorem B1865405 : Blo 1020604 1865405 := bbase (se 3 (by rfl) ⟨349763, by rfl⟩ : syracuseStep 1865405 = 699527) (by norm_num)
theorem B2455301 : Blo 1020604 2455301 := bbase (se 4 (by rfl) ⟨230184, by rfl⟩ : syracuseStep 2455301 = 460369) (by norm_num)
theorem B2947013 : Blo 1020604 2947013 := bbase (se 4 (by rfl) ⟨276282, by rfl⟩ : syracuseStep 2947013 = 552565) (by norm_num)
theorem B2586613 : Blo 1020604 2586613 := bbase (se 5 (by rfl) ⟨121247, by rfl⟩ : syracuseStep 2586613 = 242495) (by norm_num)
theorem B1964029 : Blo 1020604 1964029 := bbase (se 3 (by rfl) ⟨368255, by rfl⟩ : syracuseStep 1964029 = 736511) (by norm_num)
theorem B2586725 : Blo 1020604 2586725 := bbase (se 4 (by rfl) ⟨242505, by rfl⟩ : syracuseStep 2586725 = 485011) (by norm_num)
theorem B5175413 : Blo 1020604 5175413 := bbase (se 5 (by rfl) ⟨242597, by rfl⟩ : syracuseStep 5175413 = 485195) (by norm_num)
theorem B2586917 : Blo 1020604 2586917 := bbase (se 4 (by rfl) ⟨242523, by rfl⟩ : syracuseStep 2586917 = 485047) (by norm_num)
theorem B3275093 : Blo 1020604 3275093 := bbase (se 10 (by rfl) ⟨4797, by rfl⟩ : syracuseStep 3275093 = 9595) (by norm_num)
theorem B2914805 : Blo 1020604 2914805 := bbase (se 5 (by rfl) ⟨136631, by rfl⟩ : syracuseStep 2914805 = 273263) (by norm_num)
theorem B2587261 : Blo 1020604 2587261 := bbase (se 3 (by rfl) ⟨485111, by rfl⟩ : syracuseStep 2587261 = 970223) (by norm_num)
theorem B1637021 : Blo 1020604 1637021 := bbase (se 3 (by rfl) ⟨306941, by rfl⟩ : syracuseStep 1637021 = 613883) (by norm_num)
theorem B2587373 : Blo 1020604 2587373 := bbase (se 3 (by rfl) ⟨485132, by rfl⟩ : syracuseStep 2587373 = 970265) (by norm_num)
theorem B4913909 : Blo 1020604 4913909 := bbase (se 5 (by rfl) ⟨230339, by rfl⟩ : syracuseStep 4913909 = 460679) (by norm_num)
theorem B7764821 : Blo 1020604 7764821 := bbase (se 9 (by rfl) ⟨22748, by rfl⟩ : syracuseStep 7764821 = 45497) (by norm_num)
theorem B2587565 : Blo 1020604 2587565 := bbase (se 3 (by rfl) ⟨485168, by rfl⟩ : syracuseStep 2587565 = 970337) (by norm_num)
theorem B2948213 : Blo 1020604 2948213 := bbase (se 5 (by rfl) ⟨138197, by rfl⟩ : syracuseStep 2948213 = 276395) (by norm_num)
theorem B2915477 : Blo 1020604 2915477 := bbase (se 6 (by rfl) ⟨68331, by rfl⟩ : syracuseStep 2915477 = 136663) (by norm_num)
theorem B1309861 : Blo 1020604 1309861 := bbase (se 4 (by rfl) ⟨122799, by rfl⟩ : syracuseStep 1309861 = 245599) (by norm_num)
theorem B2587909 : Blo 1020604 2587909 := bbase (se 4 (by rfl) ⟨242616, by rfl⟩ : syracuseStep 2587909 = 485233) (by norm_num)
theorem B1244441 : Blo 1020604 1244441 := bbase (se 2 (by rfl) ⟨466665, by rfl⟩ : syracuseStep 1244441 = 933331) (by norm_num)
theorem B2588021 : Blo 1020604 2588021 := bbase (se 5 (by rfl) ⟨121313, by rfl⟩ : syracuseStep 2588021 = 242627) (by norm_num)
theorem B5176709 : Blo 1020604 5176709 := bbase (se 4 (by rfl) ⟨485316, by rfl⟩ : syracuseStep 5176709 = 970633) (by norm_num)
theorem B18906581 : Blo 1020604 18906581 := bbase (se 7 (by rfl) ⟨221561, by rfl⟩ : syracuseStep 18906581 = 443123) (by norm_num)
theorem B5897717 : Blo 1020604 5897717 := bbase (se 5 (by rfl) ⟨276455, by rfl⟩ : syracuseStep 5897717 = 552911) (by norm_num)
theorem B2588213 : Blo 1020604 2588213 := bbase (se 5 (by rfl) ⟨121322, by rfl⟩ : syracuseStep 2588213 = 242645) (by norm_num)
theorem B2915909 : Blo 1020604 2915909 := bbase (se 4 (by rfl) ⟨273366, by rfl⟩ : syracuseStep 2915909 = 546733) (by norm_num)
theorem B1637957 : Blo 1020604 1637957 := bbase (se 4 (by rfl) ⟨153558, by rfl⟩ : syracuseStep 1637957 = 307117) (by norm_num)
theorem B3276389 : Blo 1020604 3276389 := bbase (se 4 (by rfl) ⟨307161, by rfl⟩ : syracuseStep 3276389 = 614323) (by norm_num)
theorem B5537621 : Blo 1020604 5537621 := bbase (se 9 (by rfl) ⟨16223, by rfl⟩ : syracuseStep 5537621 = 32447) (by norm_num)
theorem B2588557 : Blo 1020604 2588557 := bbase (se 3 (by rfl) ⟨485354, by rfl⟩ : syracuseStep 2588557 = 970709) (by norm_num)
theorem B2588669 : Blo 1020604 2588669 := bbase (se 3 (by rfl) ⟨485375, by rfl⟩ : syracuseStep 2588669 = 970751) (by norm_num)
theorem B5177357 : Blo 1020604 5177357 := bstep (se 3 (by rfl) ⟨970754, by rfl⟩ : syracuseStep 5177357 = 1941509) B1941509
theorem B2588881 : Blo 1020604 2588881 := bstep (se 2 (by rfl) ⟨970830, by rfl⟩ : syracuseStep 2588881 = 1941661) B1941661
theorem B2916593 : Blo 1020604 2916593 := bstep (se 2 (by rfl) ⟨1093722, by rfl⟩ : syracuseStep 2916593 = 2187445) B2187445
theorem B6226253 : Blo 1020604 6226253 := bstep (se 3 (by rfl) ⟨1167422, by rfl⟩ : syracuseStep 6226253 = 2334845) B2334845
theorem B3277169 : Blo 1020604 3277169 := bstep (se 2 (by rfl) ⟨1228938, by rfl⟩ : syracuseStep 3277169 = 2457877) B2457877
theorem B5833093 : Blo 1020604 5833093 := bstep (se 4 (by rfl) ⟨546852, by rfl⟩ : syracuseStep 5833093 = 1093705) B1093705
theorem B2589155 : Blo 1020604 2589155 := bstep (se 1 (by rfl) ⟨1941866, by rfl⟩ : syracuseStep 2589155 = 3883733) B3883733
theorem B1311379 : Blo 1020604 1311379 := bstep (se 1 (by rfl) ⟨983534, by rfl⟩ : syracuseStep 1311379 = 1967069) B1967069
theorem B2589347 : Blo 1020604 2589347 := bstep (se 1 (by rfl) ⟨1942010, by rfl⟩ : syracuseStep 2589347 = 3884021) B3884021
theorem B5899013 : Blo 1020604 5899013 := bstep (se 4 (by rfl) ⟨553032, by rfl⟩ : syracuseStep 5899013 = 1106065) B1106065
theorem B9339661 : Blo 1020604 9339661 := bstep (se 3 (by rfl) ⟨1751186, by rfl⟩ : syracuseStep 9339661 = 3502373) B3502373
theorem B3539857 : Blo 1020604 3539857 := bstep (se 2 (by rfl) ⟨1327446, by rfl⟩ : syracuseStep 3539857 = 2654893) B2654893
theorem B11076533 : Blo 1020604 11076533 := bstep (se 5 (by rfl) ⟨519212, by rfl⟩ : syracuseStep 11076533 = 1038425) B1038425
theorem B1639379 : Blo 1020604 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B8750051 : Blo 1020604 8750051 := bstep (se 1 (by rfl) ⟨6562538, by rfl⟩ : syracuseStep 8750051 = 13125077) B13125077
theorem B5604515 : Blo 1020604 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B2917549 : Blo 1020604 2917549 := bstep (se 3 (by rfl) ⟨547040, by rfl⟩ : syracuseStep 2917549 = 1094081) B1094081
theorem B3278029 : Blo 1020604 3278029 := bstep (se 3 (by rfl) ⟨614630, by rfl⟩ : syracuseStep 3278029 = 1229261) B1229261
theorem B3736945 : Blo 1020604 3736945 := bstep (se 2 (by rfl) ⟨1401354, by rfl⟩ : syracuseStep 3736945 = 2802709) B2802709
theorem B1148323 : Blo 1020604 1148323 := bstep (se 1 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 1148323 = 1722485) B1722485
theorem B6555107 : Blo 1020604 6555107 := bstep (se 1 (by rfl) ⟨4916330, by rfl⟩ : syracuseStep 6555107 = 9832661) B9832661
theorem B2459107 : Blo 1020604 2459107 := bstep (se 1 (by rfl) ⟨1844330, by rfl⟩ : syracuseStep 2459107 = 3688661) B3688661
theorem B11666915 : Blo 1020604 11666915 := bstep (se 1 (by rfl) ⟨8750186, by rfl⟩ : syracuseStep 11666915 = 17500373) B17500373
theorem B1148467 : Blo 1020604 1148467 := bstep (se 1 (by rfl) ⟨861350, by rfl⟩ : syracuseStep 1148467 = 1722701) B1722701
theorem B2590289 : Blo 1020604 2590289 := bstep (se 2 (by rfl) ⟨971358, by rfl⟩ : syracuseStep 2590289 = 1942717) B1942717
theorem B2590339 : Blo 1020604 2590339 := bstep (se 1 (by rfl) ⟨1942754, by rfl⟩ : syracuseStep 2590339 = 3885509) B3885509
theorem B1148611 : Blo 1020604 1148611 := bstep (se 1 (by rfl) ⟨861458, by rfl⟩ : syracuseStep 1148611 = 1722917) B1722917
theorem B2590481 : Blo 1020604 2590481 := bstep (se 2 (by rfl) ⟨971430, by rfl⟩ : syracuseStep 2590481 = 1942861) B1942861
theorem B1640225 : Blo 1020604 1640225 := bstep (se 2 (by rfl) ⟨615084, by rfl⟩ : syracuseStep 1640225 = 1230169) B1230169
theorem B1148755 : Blo 1020604 1148755 := bstep (se 1 (by rfl) ⟨861566, by rfl⟩ : syracuseStep 1148755 = 1723133) B1723133
theorem B1640353 : Blo 1020604 1640353 := bstep (se 2 (by rfl) ⟨615132, by rfl⟩ : syracuseStep 1640353 = 1230265) B1230265
theorem B1640417 : Blo 1020604 1640417 := bstep (se 2 (by rfl) ⟨615156, by rfl⟩ : syracuseStep 1640417 = 1230313) B1230313
theorem B1148899 : Blo 1020604 1148899 := bstep (se 1 (by rfl) ⟨861674, by rfl⟩ : syracuseStep 1148899 = 1723349) B1723349
theorem B1869905 : Blo 1020604 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B1149043 : Blo 1020604 1149043 := bstep (se 1 (by rfl) ⟨861782, by rfl⟩ : syracuseStep 1149043 = 1723565) B1723565
theorem B1149187 : Blo 1020604 1149187 := bstep (se 1 (by rfl) ⟨861890, by rfl⟩ : syracuseStep 1149187 = 1723781) B1723781
theorem B5835077 : Blo 1020604 5835077 := bstep (se 4 (by rfl) ⟨547038, by rfl⟩ : syracuseStep 5835077 = 1094077) B1094077
theorem B1149331 : Blo 1020604 1149331 := bstep (se 1 (by rfl) ⟨861998, by rfl⟩ : syracuseStep 1149331 = 1723997) B1723997
theorem B2460145 : Blo 1020604 2460145 := bstep (se 2 (by rfl) ⟨922554, by rfl⟩ : syracuseStep 2460145 = 1845109) B1845109
theorem B1149475 : Blo 1020604 1149475 := bstep (se 1 (by rfl) ⟨862106, by rfl⟩ : syracuseStep 1149475 = 1724213) B1724213
theorem B1149619 : Blo 1020604 1149619 := bstep (se 1 (by rfl) ⟨862214, by rfl⟩ : syracuseStep 1149619 = 1724429) B1724429
theorem B2296529 : Blo 1020604 2296529 := bstep (se 2 (by rfl) ⟨861198, by rfl⟩ : syracuseStep 2296529 = 1722397) B1722397
theorem B2296547 : Blo 1020604 2296547 := bstep (se 1 (by rfl) ⟨1722410, by rfl⟩ : syracuseStep 2296547 = 3444821) B3444821
theorem B2591473 : Blo 1020604 2591473 := bstep (se 2 (by rfl) ⟨971802, by rfl⟩ : syracuseStep 2591473 = 1943605) B1943605
theorem B3279629 : Blo 1020604 3279629 := bstep (se 3 (by rfl) ⟨614930, by rfl⟩ : syracuseStep 3279629 = 1229861) B1229861
theorem B1149763 : Blo 1020604 1149763 := bstep (se 1 (by rfl) ⟨862322, by rfl⟩ : syracuseStep 1149763 = 1724645) B1724645
theorem B5180273 : Blo 1020604 5180273 := bstep (se 2 (by rfl) ⟨1942602, by rfl⟩ : syracuseStep 5180273 = 3885205) B3885205
theorem B2329489 : Blo 1020604 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B1149907 : Blo 1020604 1149907 := bstep (se 1 (by rfl) ⟨862430, by rfl⟩ : syracuseStep 1149907 = 1724861) B1724861
theorem B2296817 : Blo 1020604 2296817 := bstep (se 2 (by rfl) ⟨861306, by rfl⟩ : syracuseStep 2296817 = 1722613) B1722613
theorem B2296835 : Blo 1020604 2296835 := bstep (se 1 (by rfl) ⟨1722626, by rfl⟩ : syracuseStep 2296835 = 3445253) B3445253
theorem B2591747 : Blo 1020604 2591747 := bstep (se 1 (by rfl) ⟨1943810, by rfl⟩ : syracuseStep 2591747 = 3887621) B3887621
theorem B1379377 : Blo 1020604 1379377 := bstep (se 2 (by rfl) ⟨517266, by rfl⟩ : syracuseStep 1379377 = 1034533) B1034533
theorem B1150051 : Blo 1020604 1150051 := bstep (se 1 (by rfl) ⟨862538, by rfl⟩ : syracuseStep 1150051 = 1725077) B1725077
theorem B4361357 : Blo 1020604 4361357 := bstep (se 3 (by rfl) ⟨817754, by rfl⟩ : syracuseStep 4361357 = 1635509) B1635509
theorem B2591939 : Blo 1020604 2591939 := bstep (se 1 (by rfl) ⟨1943954, by rfl⟩ : syracuseStep 2591939 = 3887909) B3887909
theorem B1150195 : Blo 1020604 1150195 := bstep (se 1 (by rfl) ⟨862646, by rfl⟩ : syracuseStep 1150195 = 1725293) B1725293
theorem B2297105 : Blo 1020604 2297105 := bstep (se 2 (by rfl) ⟨861414, by rfl⟩ : syracuseStep 2297105 = 1722829) B1722829
theorem B2297123 : Blo 1020604 2297123 := bstep (se 1 (by rfl) ⟨1722842, by rfl⟩ : syracuseStep 2297123 = 3445685) B3445685
theorem B1150339 : Blo 1020604 1150339 := bstep (se 1 (by rfl) ⟨862754, by rfl⟩ : syracuseStep 1150339 = 1725509) B1725509
theorem B6557105 : Blo 1020604 6557105 := bstep (se 2 (by rfl) ⟨2458914, by rfl⟩ : syracuseStep 6557105 = 4917829) B4917829
theorem B1150483 : Blo 1020604 1150483 := bstep (se 1 (by rfl) ⟨862862, by rfl⟩ : syracuseStep 1150483 = 1725725) B1725725
theorem B2297393 : Blo 1020604 2297393 := bstep (se 2 (by rfl) ⟨861522, by rfl⟩ : syracuseStep 2297393 = 1723045) B1723045
theorem B2297411 : Blo 1020604 2297411 := bstep (se 1 (by rfl) ⟨1723058, by rfl⟩ : syracuseStep 2297411 = 3446117) B3446117
theorem B1150627 : Blo 1020604 1150627 := bstep (se 1 (by rfl) ⟨862970, by rfl⟩ : syracuseStep 1150627 = 1725941) B1725941
theorem B1150771 : Blo 1020604 1150771 := bstep (se 1 (by rfl) ⟨863078, by rfl⟩ : syracuseStep 1150771 = 1726157) B1726157
theorem B2297681 : Blo 1020604 2297681 := bstep (se 2 (by rfl) ⟨861630, by rfl⟩ : syracuseStep 2297681 = 1723261) B1723261
theorem B2297699 : Blo 1020604 2297699 := bstep (se 1 (by rfl) ⟨1723274, by rfl⟩ : syracuseStep 2297699 = 3446549) B3446549
theorem B1150915 : Blo 1020604 1150915 := bstep (se 1 (by rfl) ⟨863186, by rfl⟩ : syracuseStep 1150915 = 1726373) B1726373
theorem B8851427 : Blo 1020604 8851427 := bstep (se 1 (by rfl) ⟨6638570, by rfl⟩ : syracuseStep 8851427 = 13277141) B13277141
theorem B6983729 : Blo 1020604 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B1151059 : Blo 1020604 1151059 := bstep (se 1 (by rfl) ⟨863294, by rfl⟩ : syracuseStep 1151059 = 1726589) B1726589
theorem B2297969 : Blo 1020604 2297969 := bstep (se 2 (by rfl) ⟨861738, by rfl⟩ : syracuseStep 2297969 = 1723477) B1723477
theorem B2592881 : Blo 1020604 2592881 := bstep (se 2 (by rfl) ⟨972330, by rfl⟩ : syracuseStep 2592881 = 1944661) B1944661
theorem B2297987 : Blo 1020604 2297987 := bstep (se 1 (by rfl) ⟨1723490, by rfl⟩ : syracuseStep 2297987 = 3446981) B3446981
theorem B2592931 : Blo 1020604 2592931 := bstep (se 1 (by rfl) ⟨1944698, by rfl⟩ : syracuseStep 2592931 = 3889397) B3889397
theorem B1151203 : Blo 1020604 1151203 := bstep (se 1 (by rfl) ⟨863402, by rfl⟩ : syracuseStep 1151203 = 1726805) B1726805
theorem B5181731 : Blo 1020604 5181731 := bstep (se 1 (by rfl) ⟨3886298, by rfl⟩ : syracuseStep 5181731 = 7772597) B7772597
theorem B3445037 : Blo 1020604 3445037 := bstep (se 3 (by rfl) ⟨645944, by rfl⟩ : syracuseStep 3445037 = 1291889) B1291889
theorem B2593073 : Blo 1020604 2593073 := bstep (se 2 (by rfl) ⟨972402, by rfl⟩ : syracuseStep 2593073 = 1944805) B1944805
theorem B3281219 : Blo 1020604 3281219 := bstep (se 1 (by rfl) ⟨2460914, by rfl⟩ : syracuseStep 3281219 = 4921829) B4921829
theorem B6558029 : Blo 1020604 6558029 := bstep (se 3 (by rfl) ⟨1229630, by rfl⟩ : syracuseStep 6558029 = 2459261) B2459261
theorem B3445091 : Blo 1020604 3445091 := bstep (se 1 (by rfl) ⟨2583818, by rfl⟩ : syracuseStep 3445091 = 5167637) B5167637
theorem B1151347 : Blo 1020604 1151347 := bstep (se 1 (by rfl) ⟨863510, by rfl⟩ : syracuseStep 1151347 = 1727021) B1727021
theorem B2298257 : Blo 1020604 2298257 := bstep (se 2 (by rfl) ⟨861846, by rfl⟩ : syracuseStep 2298257 = 1723693) B1723693
theorem B2298275 : Blo 1020604 2298275 := bstep (se 1 (by rfl) ⟨1723706, by rfl⟩ : syracuseStep 2298275 = 3447413) B3447413
theorem B1151491 : Blo 1020604 1151491 := bstep (se 1 (by rfl) ⟨863618, by rfl⟩ : syracuseStep 1151491 = 1727237) B1727237
theorem B3281411 : Blo 1020604 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B1938001 : Blo 1020604 1938001 := bstep (se 2 (by rfl) ⟨726750, by rfl⟩ : syracuseStep 1938001 = 1453501) B1453501
theorem B3445361 : Blo 1020604 3445361 := bstep (se 2 (by rfl) ⟨1292010, by rfl⟩ : syracuseStep 3445361 = 2584021) B2584021
theorem B9835121 : Blo 1020604 9835121 := bstep (se 2 (by rfl) ⟨3688170, by rfl⟩ : syracuseStep 9835121 = 7376341) B7376341
theorem B1151635 : Blo 1020604 1151635 := bstep (se 1 (by rfl) ⟨863726, by rfl⟩ : syracuseStep 1151635 = 1727453) B1727453
theorem B4362929 : Blo 1020604 4362929 := bstep (se 2 (by rfl) ⟨1636098, by rfl⟩ : syracuseStep 4362929 = 3272197) B3272197
theorem B2298545 : Blo 1020604 2298545 := bstep (se 2 (by rfl) ⟨861954, by rfl⟩ : syracuseStep 2298545 = 1723909) B1723909
theorem B1020611 : Blo 1020604 1020611 := bstep (se 1 (by rfl) ⟨765458, by rfl⟩ : syracuseStep 1020611 = 1530917) B1530917
theorem B2298563 : Blo 1020604 2298563 := bstep (se 1 (by rfl) ⟨1723922, by rfl⟩ : syracuseStep 2298563 = 3447845) B3447845
theorem B1020627 : Blo 1020604 1020627 := bstep (se 1 (by rfl) ⟨765470, by rfl⟩ : syracuseStep 1020627 = 1530941) B1530941
theorem B1020643 : Blo 1020604 1020643 := bstep (se 1 (by rfl) ⟨765482, by rfl⟩ : syracuseStep 1020643 = 1530965) B1530965
theorem B1938161 : Blo 1020604 1938161 := bstep (se 2 (by rfl) ⟨726810, by rfl⟩ : syracuseStep 1938161 = 1453621) B1453621
theorem B1020659 : Blo 1020604 1020659 := bstep (se 1 (by rfl) ⟨765494, by rfl⟩ : syracuseStep 1020659 = 1530989) B1530989
theorem B1020675 : Blo 1020604 1020675 := bstep (se 1 (by rfl) ⟨765506, by rfl⟩ : syracuseStep 1020675 = 1531013) B1531013
theorem B1020691 : Blo 1020604 1020691 := bstep (se 1 (by rfl) ⟨765518, by rfl⟩ : syracuseStep 1020691 = 1531037) B1531037
theorem B1020707 : Blo 1020604 1020707 := bstep (se 1 (by rfl) ⟨765530, by rfl⟩ : syracuseStep 1020707 = 1531061) B1531061
theorem B1151779 : Blo 1020604 1151779 := bstep (se 1 (by rfl) ⟨863834, by rfl⟩ : syracuseStep 1151779 = 1727669) B1727669
theorem B1020723 : Blo 1020604 1020723 := bstep (se 1 (by rfl) ⟨765542, by rfl⟩ : syracuseStep 1020723 = 1531085) B1531085
theorem B1020739 : Blo 1020604 1020739 := bstep (se 1 (by rfl) ⟨765554, by rfl⟩ : syracuseStep 1020739 = 1531109) B1531109
theorem B1020755 : Blo 1020604 1020755 := bstep (se 1 (by rfl) ⟨765566, by rfl⟩ : syracuseStep 1020755 = 1531133) B1531133
theorem B1020771 : Blo 1020604 1020771 := bstep (se 1 (by rfl) ⟨765578, by rfl⟩ : syracuseStep 1020771 = 1531157) B1531157
theorem B1020787 : Blo 1020604 1020787 := bstep (se 1 (by rfl) ⟨765590, by rfl⟩ : syracuseStep 1020787 = 1531181) B1531181
theorem B1020803 : Blo 1020604 1020803 := bstep (se 1 (by rfl) ⟨765602, by rfl⟩ : syracuseStep 1020803 = 1531205) B1531205
theorem B1020819 : Blo 1020604 1020819 := bstep (se 1 (by rfl) ⟨765614, by rfl⟩ : syracuseStep 1020819 = 1531229) B1531229
theorem B1020835 : Blo 1020604 1020835 := bstep (se 1 (by rfl) ⟨765626, by rfl⟩ : syracuseStep 1020835 = 1531253) B1531253
theorem B1020851 : Blo 1020604 1020851 := bstep (se 1 (by rfl) ⟨765638, by rfl⟩ : syracuseStep 1020851 = 1531277) B1531277
theorem B1151923 : Blo 1020604 1151923 := bstep (se 1 (by rfl) ⟨863942, by rfl⟩ : syracuseStep 1151923 = 1727885) B1727885
theorem B1020867 : Blo 1020604 1020867 := bstep (se 1 (by rfl) ⟨765650, by rfl⟩ : syracuseStep 1020867 = 1531301) B1531301
theorem B2298833 : Blo 1020604 2298833 := bstep (se 2 (by rfl) ⟨862062, by rfl⟩ : syracuseStep 2298833 = 1724125) B1724125
theorem B1020883 : Blo 1020604 1020883 := bstep (se 1 (by rfl) ⟨765662, by rfl⟩ : syracuseStep 1020883 = 1531325) B1531325
theorem B1020899 : Blo 1020604 1020899 := bstep (se 1 (by rfl) ⟨765674, by rfl⟩ : syracuseStep 1020899 = 1531349) B1531349
theorem B2298851 : Blo 1020604 2298851 := bstep (se 1 (by rfl) ⟨1724138, by rfl⟩ : syracuseStep 2298851 = 3448277) B3448277
theorem B1020915 : Blo 1020604 1020915 := bstep (se 1 (by rfl) ⟨765686, by rfl⟩ : syracuseStep 1020915 = 1531373) B1531373
theorem B1020931 : Blo 1020604 1020931 := bstep (se 1 (by rfl) ⟨765698, by rfl⟩ : syracuseStep 1020931 = 1531397) B1531397
theorem B1020947 : Blo 1020604 1020947 := bstep (se 1 (by rfl) ⟨765710, by rfl⟩ : syracuseStep 1020947 = 1531421) B1531421
theorem B1020963 : Blo 1020604 1020963 := bstep (se 1 (by rfl) ⟨765722, by rfl⟩ : syracuseStep 1020963 = 1531445) B1531445
theorem B1020979 : Blo 1020604 1020979 := bstep (se 1 (by rfl) ⟨765734, by rfl⟩ : syracuseStep 1020979 = 1531469) B1531469
theorem B1020995 : Blo 1020604 1020995 := bstep (se 1 (by rfl) ⟨765746, by rfl⟩ : syracuseStep 1020995 = 1531493) B1531493
theorem B1152067 : Blo 1020604 1152067 := bstep (se 1 (by rfl) ⟨864050, by rfl⟩ : syracuseStep 1152067 = 1728101) B1728101
theorem B5182541 : Blo 1020604 5182541 := bstep (se 3 (by rfl) ⟨971726, by rfl⟩ : syracuseStep 5182541 = 1943453) B1943453
theorem B1021011 : Blo 1020604 1021011 := bstep (se 1 (by rfl) ⟨765758, by rfl⟩ : syracuseStep 1021011 = 1531517) B1531517
theorem B1021027 : Blo 1020604 1021027 := bstep (se 1 (by rfl) ⟨765770, by rfl⟩ : syracuseStep 1021027 = 1531541) B1531541
theorem B1021043 : Blo 1020604 1021043 := bstep (se 1 (by rfl) ⟨765782, by rfl⟩ : syracuseStep 1021043 = 1531565) B1531565
theorem B1021059 : Blo 1020604 1021059 := bstep (se 1 (by rfl) ⟨765794, by rfl⟩ : syracuseStep 1021059 = 1531589) B1531589
theorem B1938563 : Blo 1020604 1938563 := bstep (se 1 (by rfl) ⟨1453922, by rfl⟩ : syracuseStep 1938563 = 2907845) B2907845
theorem B3445901 : Blo 1020604 3445901 := bstep (se 3 (by rfl) ⟨646106, by rfl⟩ : syracuseStep 3445901 = 1292213) B1292213
theorem B3282065 : Blo 1020604 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B1021075 : Blo 1020604 1021075 := bstep (se 1 (by rfl) ⟨765806, by rfl⟩ : syracuseStep 1021075 = 1531613) B1531613
theorem B1021091 : Blo 1020604 1021091 := bstep (se 1 (by rfl) ⟨765818, by rfl⟩ : syracuseStep 1021091 = 1531637) B1531637
theorem B1021107 : Blo 1020604 1021107 := bstep (se 1 (by rfl) ⟨765830, by rfl⟩ : syracuseStep 1021107 = 1531661) B1531661
theorem B3445955 : Blo 1020604 3445955 := bstep (se 1 (by rfl) ⟨2584466, by rfl⟩ : syracuseStep 3445955 = 5168933) B5168933
theorem B1021123 : Blo 1020604 1021123 := bstep (se 1 (by rfl) ⟨765842, by rfl⟩ : syracuseStep 1021123 = 1531685) B1531685
theorem B1021139 : Blo 1020604 1021139 := bstep (se 1 (by rfl) ⟨765854, by rfl⟩ : syracuseStep 1021139 = 1531709) B1531709
theorem B1152211 : Blo 1020604 1152211 := bstep (se 1 (by rfl) ⟨864158, by rfl⟩ : syracuseStep 1152211 = 1728317) B1728317
theorem B1021155 : Blo 1020604 1021155 := bstep (se 1 (by rfl) ⟨765866, by rfl⟩ : syracuseStep 1021155 = 1531733) B1531733
theorem B2299121 : Blo 1020604 2299121 := bstep (se 2 (by rfl) ⟨862170, by rfl⟩ : syracuseStep 2299121 = 1724341) B1724341
theorem B1021171 : Blo 1020604 1021171 := bstep (se 1 (by rfl) ⟨765878, by rfl⟩ : syracuseStep 1021171 = 1531757) B1531757
theorem B1021187 : Blo 1020604 1021187 := bstep (se 1 (by rfl) ⟨765890, by rfl⟩ : syracuseStep 1021187 = 1531781) B1531781
theorem B2299139 : Blo 1020604 2299139 := bstep (se 1 (by rfl) ⟨1724354, by rfl⟩ : syracuseStep 2299139 = 3448709) B3448709
theorem B1021203 : Blo 1020604 1021203 := bstep (se 1 (by rfl) ⟨765902, by rfl⟩ : syracuseStep 1021203 = 1531805) B1531805
theorem B1774867 : Blo 1020604 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B1021219 : Blo 1020604 1021219 := bstep (se 1 (by rfl) ⟨765914, by rfl⟩ : syracuseStep 1021219 = 1531829) B1531829
theorem B1021235 : Blo 1020604 1021235 := bstep (se 1 (by rfl) ⟨765926, by rfl⟩ : syracuseStep 1021235 = 1531853) B1531853
theorem B1021251 : Blo 1020604 1021251 := bstep (se 1 (by rfl) ⟨765938, by rfl⟩ : syracuseStep 1021251 = 1531877) B1531877
theorem B1021267 : Blo 1020604 1021267 := bstep (se 1 (by rfl) ⟨765950, by rfl⟩ : syracuseStep 1021267 = 1531901) B1531901
theorem B1021283 : Blo 1020604 1021283 := bstep (se 1 (by rfl) ⟨765962, by rfl⟩ : syracuseStep 1021283 = 1531925) B1531925
theorem B1152355 : Blo 1020604 1152355 := bstep (se 1 (by rfl) ⟨864266, by rfl⟩ : syracuseStep 1152355 = 1728533) B1728533
theorem B1021299 : Blo 1020604 1021299 := bstep (se 1 (by rfl) ⟨765974, by rfl⟩ : syracuseStep 1021299 = 1531949) B1531949
theorem B1021315 : Blo 1020604 1021315 := bstep (se 1 (by rfl) ⟨765986, by rfl⟩ : syracuseStep 1021315 = 1531973) B1531973
theorem B1021331 : Blo 1020604 1021331 := bstep (se 1 (by rfl) ⟨765998, by rfl⟩ : syracuseStep 1021331 = 1531997) B1531997
theorem B1021347 : Blo 1020604 1021347 := bstep (se 1 (by rfl) ⟨766010, by rfl⟩ : syracuseStep 1021347 = 1532021) B1532021
theorem B1021363 : Blo 1020604 1021363 := bstep (se 1 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 1021363 = 1532045) B1532045
theorem B1021379 : Blo 1020604 1021379 := bstep (se 1 (by rfl) ⟨766034, by rfl⟩ : syracuseStep 1021379 = 1532069) B1532069
theorem B3446225 : Blo 1020604 3446225 := bstep (se 2 (by rfl) ⟨1292334, by rfl⟩ : syracuseStep 3446225 = 2584669) B2584669
theorem B1021395 : Blo 1020604 1021395 := bstep (se 1 (by rfl) ⟨766046, by rfl⟩ : syracuseStep 1021395 = 1532093) B1532093
theorem B1021411 : Blo 1020604 1021411 := bstep (se 1 (by rfl) ⟨766058, by rfl⟩ : syracuseStep 1021411 = 1532117) B1532117
theorem B1021427 : Blo 1020604 1021427 := bstep (se 1 (by rfl) ⟨766070, by rfl⟩ : syracuseStep 1021427 = 1532141) B1532141
theorem B1152499 : Blo 1020604 1152499 := bstep (se 1 (by rfl) ⟨864374, by rfl⟩ : syracuseStep 1152499 = 1728749) B1728749
theorem B1021443 : Blo 1020604 1021443 := bstep (se 1 (by rfl) ⟨766082, by rfl⟩ : syracuseStep 1021443 = 1532165) B1532165
theorem B2299409 : Blo 1020604 2299409 := bstep (se 2 (by rfl) ⟨862278, by rfl⟩ : syracuseStep 2299409 = 1724557) B1724557
theorem B1021459 : Blo 1020604 1021459 := bstep (se 1 (by rfl) ⟨766094, by rfl⟩ : syracuseStep 1021459 = 1532189) B1532189
theorem B1021475 : Blo 1020604 1021475 := bstep (se 1 (by rfl) ⟨766106, by rfl⟩ : syracuseStep 1021475 = 1532213) B1532213
theorem B2299427 : Blo 1020604 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B1021491 : Blo 1020604 1021491 := bstep (se 1 (by rfl) ⟨766118, by rfl⟩ : syracuseStep 1021491 = 1532237) B1532237
theorem B1021507 : Blo 1020604 1021507 := bstep (se 1 (by rfl) ⟨766130, by rfl⟩ : syracuseStep 1021507 = 1532261) B1532261
theorem B1021523 : Blo 1020604 1021523 := bstep (se 1 (by rfl) ⟨766142, by rfl⟩ : syracuseStep 1021523 = 1532285) B1532285
theorem B1021539 : Blo 1020604 1021539 := bstep (se 1 (by rfl) ⟨766154, by rfl⟩ : syracuseStep 1021539 = 1532309) B1532309
theorem B1021555 : Blo 1020604 1021555 := bstep (se 1 (by rfl) ⟨766166, by rfl⟩ : syracuseStep 1021555 = 1532333) B1532333
theorem B1021571 : Blo 1020604 1021571 := bstep (se 1 (by rfl) ⟨766178, by rfl⟩ : syracuseStep 1021571 = 1532357) B1532357
theorem B1152643 : Blo 1020604 1152643 := bstep (se 1 (by rfl) ⟨864482, by rfl⟩ : syracuseStep 1152643 = 1728965) B1728965
theorem B1021587 : Blo 1020604 1021587 := bstep (se 1 (by rfl) ⟨766190, by rfl⟩ : syracuseStep 1021587 = 1532381) B1532381
theorem B1021603 : Blo 1020604 1021603 := bstep (se 1 (by rfl) ⟨766202, by rfl⟩ : syracuseStep 1021603 = 1532405) B1532405
theorem B1021619 : Blo 1020604 1021619 := bstep (se 1 (by rfl) ⟨766214, by rfl⟩ : syracuseStep 1021619 = 1532429) B1532429
theorem B1021635 : Blo 1020604 1021635 := bstep (se 1 (by rfl) ⟨766226, by rfl⟩ : syracuseStep 1021635 = 1532453) B1532453
theorem B1021651 : Blo 1020604 1021651 := bstep (se 1 (by rfl) ⟨766238, by rfl⟩ : syracuseStep 1021651 = 1532477) B1532477
theorem B1382113 : Blo 1020604 1382113 := bstep (se 2 (by rfl) ⟨518292, by rfl⟩ : syracuseStep 1382113 = 1036585) B1036585
theorem B1021667 : Blo 1020604 1021667 := bstep (se 1 (by rfl) ⟨766250, by rfl⟩ : syracuseStep 1021667 = 1532501) B1532501
theorem B1021683 : Blo 1020604 1021683 := bstep (se 1 (by rfl) ⟨766262, by rfl⟩ : syracuseStep 1021683 = 1532525) B1532525
theorem B1021699 : Blo 1020604 1021699 := bstep (se 1 (by rfl) ⟨766274, by rfl⟩ : syracuseStep 1021699 = 1532549) B1532549
theorem B1021715 : Blo 1020604 1021715 := bstep (se 1 (by rfl) ⟨766286, by rfl⟩ : syracuseStep 1021715 = 1532573) B1532573
theorem B1021731 : Blo 1020604 1021731 := bstep (se 1 (by rfl) ⟨766298, by rfl⟩ : syracuseStep 1021731 = 1532597) B1532597
theorem B2299697 : Blo 1020604 2299697 := bstep (se 2 (by rfl) ⟨862386, by rfl⟩ : syracuseStep 2299697 = 1724773) B1724773
theorem B1021747 : Blo 1020604 1021747 := bstep (se 1 (by rfl) ⟨766310, by rfl⟩ : syracuseStep 1021747 = 1532621) B1532621
theorem B1021763 : Blo 1020604 1021763 := bstep (se 1 (by rfl) ⟨766322, by rfl⟩ : syracuseStep 1021763 = 1532645) B1532645
theorem B2299715 : Blo 1020604 2299715 := bstep (se 1 (by rfl) ⟨1724786, by rfl⟩ : syracuseStep 2299715 = 3449573) B3449573
theorem B1021779 : Blo 1020604 1021779 := bstep (se 1 (by rfl) ⟨766334, by rfl⟩ : syracuseStep 1021779 = 1532669) B1532669
theorem B1021795 : Blo 1020604 1021795 := bstep (se 1 (by rfl) ⟨766346, by rfl⟩ : syracuseStep 1021795 = 1532693) B1532693
theorem B1775473 : Blo 1020604 1775473 := bstep (se 2 (by rfl) ⟨665802, by rfl⟩ : syracuseStep 1775473 = 1331605) B1331605
theorem B1021811 : Blo 1020604 1021811 := bstep (se 1 (by rfl) ⟨766358, by rfl⟩ : syracuseStep 1021811 = 1532717) B1532717
theorem B1021827 : Blo 1020604 1021827 := bstep (se 1 (by rfl) ⟨766370, by rfl⟩ : syracuseStep 1021827 = 1532741) B1532741
theorem B1382275 : Blo 1020604 1382275 := bstep (se 1 (by rfl) ⟨1036706, by rfl⟩ : syracuseStep 1382275 = 2073413) B2073413
theorem B1021843 : Blo 1020604 1021843 := bstep (se 1 (by rfl) ⟨766382, by rfl⟩ : syracuseStep 1021843 = 1532765) B1532765
theorem B1021859 : Blo 1020604 1021859 := bstep (se 1 (by rfl) ⟨766394, by rfl⟩ : syracuseStep 1021859 = 1532789) B1532789
theorem B1021875 : Blo 1020604 1021875 := bstep (se 1 (by rfl) ⟨766406, by rfl⟩ : syracuseStep 1021875 = 1532813) B1532813
theorem B1021891 : Blo 1020604 1021891 := bstep (se 1 (by rfl) ⟨766418, by rfl⟩ : syracuseStep 1021891 = 1532837) B1532837
theorem B1021907 : Blo 1020604 1021907 := bstep (se 1 (by rfl) ⟨766430, by rfl⟩ : syracuseStep 1021907 = 1532861) B1532861
theorem B1021923 : Blo 1020604 1021923 := bstep (se 1 (by rfl) ⟨766442, by rfl⟩ : syracuseStep 1021923 = 1532885) B1532885
theorem B3446765 : Blo 1020604 3446765 := bstep (se 3 (by rfl) ⟨646268, by rfl⟩ : syracuseStep 3446765 = 1292537) B1292537
theorem B1021939 : Blo 1020604 1021939 := bstep (se 1 (by rfl) ⟨766454, by rfl⟩ : syracuseStep 1021939 = 1532909) B1532909
theorem B1939459 : Blo 1020604 1939459 := bstep (se 1 (by rfl) ⟨1454594, by rfl⟩ : syracuseStep 1939459 = 2909189) B2909189
theorem B1021955 : Blo 1020604 1021955 := bstep (se 1 (by rfl) ⟨766466, by rfl⟩ : syracuseStep 1021955 = 1532933) B1532933
theorem B1021971 : Blo 1020604 1021971 := bstep (se 1 (by rfl) ⟨766478, by rfl⟩ : syracuseStep 1021971 = 1532957) B1532957
theorem B3446819 : Blo 1020604 3446819 := bstep (se 1 (by rfl) ⟨2585114, by rfl⟩ : syracuseStep 3446819 = 5170229) B5170229
theorem B1021987 : Blo 1020604 1021987 := bstep (se 1 (by rfl) ⟨766490, by rfl⟩ : syracuseStep 1021987 = 1532981) B1532981
theorem B1022003 : Blo 1020604 1022003 := bstep (se 1 (by rfl) ⟨766502, by rfl⟩ : syracuseStep 1022003 = 1533005) B1533005
theorem B1022019 : Blo 1020604 1022019 := bstep (se 1 (by rfl) ⟨766514, by rfl⟩ : syracuseStep 1022019 = 1533029) B1533029
theorem B2299985 : Blo 1020604 2299985 := bstep (se 2 (by rfl) ⟨862494, by rfl⟩ : syracuseStep 2299985 = 1724989) B1724989
theorem B1022035 : Blo 1020604 1022035 := bstep (se 1 (by rfl) ⟨766526, by rfl⟩ : syracuseStep 1022035 = 1533053) B1533053
theorem B1022051 : Blo 1020604 1022051 := bstep (se 1 (by rfl) ⟨766538, by rfl⟩ : syracuseStep 1022051 = 1533077) B1533077
theorem B2300003 : Blo 1020604 2300003 := bstep (se 1 (by rfl) ⟨1725002, by rfl⟩ : syracuseStep 2300003 = 3450005) B3450005
theorem B13080689 : Blo 1020604 13080689 := bstep (se 2 (by rfl) ⟨4905258, by rfl⟩ : syracuseStep 13080689 = 9810517) B9810517
theorem B1022067 : Blo 1020604 1022067 := bstep (se 1 (by rfl) ⟨766550, by rfl⟩ : syracuseStep 1022067 = 1533101) B1533101
theorem B1022083 : Blo 1020604 1022083 := bstep (se 1 (by rfl) ⟨766562, by rfl⟩ : syracuseStep 1022083 = 1533125) B1533125
theorem B1022099 : Blo 1020604 1022099 := bstep (se 1 (by rfl) ⟨766574, by rfl⟩ : syracuseStep 1022099 = 1533149) B1533149
theorem B1939619 : Blo 1020604 1939619 := bstep (se 1 (by rfl) ⟨1454714, by rfl⟩ : syracuseStep 1939619 = 2909429) B2909429
theorem B1022115 : Blo 1020604 1022115 := bstep (se 1 (by rfl) ⟨766586, by rfl⟩ : syracuseStep 1022115 = 1533173) B1533173
theorem B1022131 : Blo 1020604 1022131 := bstep (se 1 (by rfl) ⟨766598, by rfl⟩ : syracuseStep 1022131 = 1533197) B1533197
theorem B1022147 : Blo 1020604 1022147 := bstep (se 1 (by rfl) ⟨766610, by rfl⟩ : syracuseStep 1022147 = 1533221) B1533221
theorem B1022163 : Blo 1020604 1022163 := bstep (se 1 (by rfl) ⟨766622, by rfl⟩ : syracuseStep 1022163 = 1533245) B1533245
theorem B1022179 : Blo 1020604 1022179 := bstep (se 1 (by rfl) ⟨766634, by rfl⟩ : syracuseStep 1022179 = 1533269) B1533269
theorem B1022195 : Blo 1020604 1022195 := bstep (se 1 (by rfl) ⟨766646, by rfl⟩ : syracuseStep 1022195 = 1533293) B1533293
theorem B1022211 : Blo 1020604 1022211 := bstep (se 1 (by rfl) ⟨766658, by rfl⟩ : syracuseStep 1022211 = 1533317) B1533317
theorem B1022227 : Blo 1020604 1022227 := bstep (se 1 (by rfl) ⟨766670, by rfl⟩ : syracuseStep 1022227 = 1533341) B1533341
theorem B1022243 : Blo 1020604 1022243 := bstep (se 1 (by rfl) ⟨766682, by rfl⟩ : syracuseStep 1022243 = 1533365) B1533365
theorem B3447089 : Blo 1020604 3447089 := bstep (se 2 (by rfl) ⟨1292658, by rfl⟩ : syracuseStep 3447089 = 2585317) B2585317
theorem B1022259 : Blo 1020604 1022259 := bstep (se 1 (by rfl) ⟨766694, by rfl⟩ : syracuseStep 1022259 = 1533389) B1533389
theorem B1022275 : Blo 1020604 1022275 := bstep (se 1 (by rfl) ⟨766706, by rfl⟩ : syracuseStep 1022275 = 1533413) B1533413
theorem B1022291 : Blo 1020604 1022291 := bstep (se 1 (by rfl) ⟨766718, by rfl⟩ : syracuseStep 1022291 = 1533437) B1533437
theorem B1022307 : Blo 1020604 1022307 := bstep (se 1 (by rfl) ⟨766730, by rfl⟩ : syracuseStep 1022307 = 1533461) B1533461
theorem B2300273 : Blo 1020604 2300273 := bstep (se 2 (by rfl) ⟨862602, by rfl⟩ : syracuseStep 2300273 = 1725205) B1725205
theorem B1022323 : Blo 1020604 1022323 := bstep (se 1 (by rfl) ⟨766742, by rfl⟩ : syracuseStep 1022323 = 1533485) B1533485
theorem B1022339 : Blo 1020604 1022339 := bstep (se 1 (by rfl) ⟨766754, by rfl⟩ : syracuseStep 1022339 = 1533509) B1533509
theorem B2300291 : Blo 1020604 2300291 := bstep (se 1 (by rfl) ⟨1725218, by rfl⟩ : syracuseStep 2300291 = 3450437) B3450437
theorem B1022355 : Blo 1020604 1022355 := bstep (se 1 (by rfl) ⟨766766, by rfl⟩ : syracuseStep 1022355 = 1533533) B1533533
theorem B1022371 : Blo 1020604 1022371 := bstep (se 1 (by rfl) ⟨766778, by rfl⟩ : syracuseStep 1022371 = 1533557) B1533557
theorem B1022387 : Blo 1020604 1022387 := bstep (se 1 (by rfl) ⟨766790, by rfl⟩ : syracuseStep 1022387 = 1533581) B1533581
theorem B1022403 : Blo 1020604 1022403 := bstep (se 1 (by rfl) ⟨766802, by rfl⟩ : syracuseStep 1022403 = 1533605) B1533605
theorem B4430285 : Blo 1020604 4430285 := bstep (se 3 (by rfl) ⟨830678, by rfl⟩ : syracuseStep 4430285 = 1661357) B1661357
theorem B1022419 : Blo 1020604 1022419 := bstep (se 1 (by rfl) ⟨766814, by rfl⟩ : syracuseStep 1022419 = 1533629) B1533629
theorem B1022435 : Blo 1020604 1022435 := bstep (se 1 (by rfl) ⟨766826, by rfl⟩ : syracuseStep 1022435 = 1533653) B1533653
theorem B1022451 : Blo 1020604 1022451 := bstep (se 1 (by rfl) ⟨766838, by rfl⟩ : syracuseStep 1022451 = 1533677) B1533677
theorem B1022467 : Blo 1020604 1022467 := bstep (se 1 (by rfl) ⟨766850, by rfl⟩ : syracuseStep 1022467 = 1533701) B1533701
theorem B1022483 : Blo 1020604 1022483 := bstep (se 1 (by rfl) ⟨766862, by rfl⟩ : syracuseStep 1022483 = 1533725) B1533725
theorem B1022499 : Blo 1020604 1022499 := bstep (se 1 (by rfl) ⟨766874, by rfl⟩ : syracuseStep 1022499 = 1533749) B1533749
theorem B1022515 : Blo 1020604 1022515 := bstep (se 1 (by rfl) ⟨766886, by rfl⟩ : syracuseStep 1022515 = 1533773) B1533773
theorem B1022531 : Blo 1020604 1022531 := bstep (se 1 (by rfl) ⟨766898, by rfl⟩ : syracuseStep 1022531 = 1533797) B1533797
theorem B1022547 : Blo 1020604 1022547 := bstep (se 1 (by rfl) ⟨766910, by rfl⟩ : syracuseStep 1022547 = 1533821) B1533821
theorem B1022563 : Blo 1020604 1022563 := bstep (se 1 (by rfl) ⟨766922, by rfl⟩ : syracuseStep 1022563 = 1533845) B1533845
theorem B1022579 : Blo 1020604 1022579 := bstep (se 1 (by rfl) ⟨766934, by rfl⟩ : syracuseStep 1022579 = 1533869) B1533869
theorem B1022595 : Blo 1020604 1022595 := bstep (se 1 (by rfl) ⟨766946, by rfl⟩ : syracuseStep 1022595 = 1533893) B1533893
theorem B2300561 : Blo 1020604 2300561 := bstep (se 2 (by rfl) ⟨862710, by rfl⟩ : syracuseStep 2300561 = 1725421) B1725421
theorem B2103953 : Blo 1020604 2103953 := bstep (se 2 (by rfl) ⟨788982, by rfl⟩ : syracuseStep 2103953 = 1577965) B1577965
theorem B1022611 : Blo 1020604 1022611 := bstep (se 1 (by rfl) ⟨766958, by rfl⟩ : syracuseStep 1022611 = 1533917) B1533917
theorem B2300579 : Blo 1020604 2300579 := bstep (se 1 (by rfl) ⟨1725434, by rfl⟩ : syracuseStep 2300579 = 3450869) B3450869
theorem B1022627 : Blo 1020604 1022627 := bstep (se 1 (by rfl) ⟨766970, by rfl⟩ : syracuseStep 1022627 = 1533941) B1533941
theorem B1022643 : Blo 1020604 1022643 := bstep (se 1 (by rfl) ⟨766982, by rfl⟩ : syracuseStep 1022643 = 1533965) B1533965
theorem B1022659 : Blo 1020604 1022659 := bstep (se 1 (by rfl) ⟨766994, by rfl⟩ : syracuseStep 1022659 = 1533989) B1533989
theorem B1022675 : Blo 1020604 1022675 := bstep (se 1 (by rfl) ⟨767006, by rfl⟩ : syracuseStep 1022675 = 1534013) B1534013
theorem B1022691 : Blo 1020604 1022691 := bstep (se 1 (by rfl) ⟨767018, by rfl⟩ : syracuseStep 1022691 = 1534037) B1534037
theorem B1022707 : Blo 1020604 1022707 := bstep (se 1 (by rfl) ⟨767030, by rfl⟩ : syracuseStep 1022707 = 1534061) B1534061
theorem B1022723 : Blo 1020604 1022723 := bstep (se 1 (by rfl) ⟨767042, by rfl⟩ : syracuseStep 1022723 = 1534085) B1534085
theorem B1022739 : Blo 1020604 1022739 := bstep (se 1 (by rfl) ⟨767054, by rfl⟩ : syracuseStep 1022739 = 1534109) B1534109
theorem B1022755 : Blo 1020604 1022755 := bstep (se 1 (by rfl) ⟨767066, by rfl⟩ : syracuseStep 1022755 = 1534133) B1534133
theorem B1022771 : Blo 1020604 1022771 := bstep (se 1 (by rfl) ⟨767078, by rfl⟩ : syracuseStep 1022771 = 1534157) B1534157
theorem B1022787 : Blo 1020604 1022787 := bstep (se 1 (by rfl) ⟨767090, by rfl⟩ : syracuseStep 1022787 = 1534181) B1534181
theorem B3447629 : Blo 1020604 3447629 := bstep (se 3 (by rfl) ⟨646430, by rfl⟩ : syracuseStep 3447629 = 1292861) B1292861
theorem B1022803 : Blo 1020604 1022803 := bstep (se 1 (by rfl) ⟨767102, by rfl⟩ : syracuseStep 1022803 = 1534205) B1534205
theorem B1022819 : Blo 1020604 1022819 := bstep (se 1 (by rfl) ⟨767114, by rfl⟩ : syracuseStep 1022819 = 1534229) B1534229
theorem B1022835 : Blo 1020604 1022835 := bstep (se 1 (by rfl) ⟨767126, by rfl⟩ : syracuseStep 1022835 = 1534253) B1534253
theorem B3447683 : Blo 1020604 3447683 := bstep (se 1 (by rfl) ⟨2585762, by rfl⟩ : syracuseStep 3447683 = 5171525) B5171525
theorem B1022851 : Blo 1020604 1022851 := bstep (se 1 (by rfl) ⟨767138, by rfl⟩ : syracuseStep 1022851 = 1534277) B1534277
theorem B1383313 : Blo 1020604 1383313 := bstep (se 2 (by rfl) ⟨518742, by rfl⟩ : syracuseStep 1383313 = 1037485) B1037485
theorem B1022867 : Blo 1020604 1022867 := bstep (se 1 (by rfl) ⟨767150, by rfl⟩ : syracuseStep 1022867 = 1534301) B1534301
theorem B1022883 : Blo 1020604 1022883 := bstep (se 1 (by rfl) ⟨767162, by rfl⟩ : syracuseStep 1022883 = 1534325) B1534325
theorem B2300849 : Blo 1020604 2300849 := bstep (se 2 (by rfl) ⟨862818, by rfl⟩ : syracuseStep 2300849 = 1725637) B1725637
theorem B1022899 : Blo 1020604 1022899 := bstep (se 1 (by rfl) ⟨767174, by rfl⟩ : syracuseStep 1022899 = 1534349) B1534349
theorem B2300867 : Blo 1020604 2300867 := bstep (se 1 (by rfl) ⟨1725650, by rfl⟩ : syracuseStep 2300867 = 3451301) B3451301
theorem B1022915 : Blo 1020604 1022915 := bstep (se 1 (by rfl) ⟨767186, by rfl⟩ : syracuseStep 1022915 = 1534373) B1534373
theorem B31562693 : Blo 1020604 31562693 := bstep (se 4 (by rfl) ⟨2959002, by rfl⟩ : syracuseStep 31562693 = 5918005) B5918005
theorem B1022931 : Blo 1020604 1022931 := bstep (se 1 (by rfl) ⟨767198, by rfl⟩ : syracuseStep 1022931 = 1534397) B1534397
theorem B1022947 : Blo 1020604 1022947 := bstep (se 1 (by rfl) ⟨767210, by rfl⟩ : syracuseStep 1022947 = 1534421) B1534421
theorem B1022963 : Blo 1020604 1022963 := bstep (se 1 (by rfl) ⟨767222, by rfl⟩ : syracuseStep 1022963 = 1534445) B1534445
theorem B1022979 : Blo 1020604 1022979 := bstep (se 1 (by rfl) ⟨767234, by rfl⟩ : syracuseStep 1022979 = 1534469) B1534469
theorem B1022995 : Blo 1020604 1022995 := bstep (se 1 (by rfl) ⟨767246, by rfl⟩ : syracuseStep 1022995 = 1534493) B1534493
theorem B1023011 : Blo 1020604 1023011 := bstep (se 1 (by rfl) ⟨767258, by rfl⟩ : syracuseStep 1023011 = 1534517) B1534517
theorem B1023027 : Blo 1020604 1023027 := bstep (se 1 (by rfl) ⟨767270, by rfl⟩ : syracuseStep 1023027 = 1534541) B1534541
theorem B1023043 : Blo 1020604 1023043 := bstep (se 1 (by rfl) ⟨767282, by rfl⟩ : syracuseStep 1023043 = 1534565) B1534565
theorem B5905477 : Blo 1020604 5905477 := bstep (se 4 (by rfl) ⟨553638, by rfl⟩ : syracuseStep 5905477 = 1107277) B1107277
theorem B4365389 : Blo 1020604 4365389 := bstep (se 3 (by rfl) ⟨818510, by rfl⟩ : syracuseStep 4365389 = 1637021) B1637021
theorem B1023059 : Blo 1020604 1023059 := bstep (se 1 (by rfl) ⟨767294, by rfl⟩ : syracuseStep 1023059 = 1534589) B1534589
theorem B1023075 : Blo 1020604 1023075 := bstep (se 1 (by rfl) ⟨767306, by rfl⟩ : syracuseStep 1023075 = 1534613) B1534613
theorem B1023091 : Blo 1020604 1023091 := bstep (se 1 (by rfl) ⟨767318, by rfl⟩ : syracuseStep 1023091 = 1534637) B1534637
theorem B1023107 : Blo 1020604 1023107 := bstep (se 1 (by rfl) ⟨767330, by rfl⟩ : syracuseStep 1023107 = 1534661) B1534661
theorem B3447953 : Blo 1020604 3447953 := bstep (se 2 (by rfl) ⟨1292982, by rfl⟩ : syracuseStep 3447953 = 2585965) B2585965
theorem B1023123 : Blo 1020604 1023123 := bstep (se 1 (by rfl) ⟨767342, by rfl⟩ : syracuseStep 1023123 = 1534685) B1534685
theorem B1023139 : Blo 1020604 1023139 := bstep (se 1 (by rfl) ⟨767354, by rfl⟩ : syracuseStep 1023139 = 1534709) B1534709
theorem B1023155 : Blo 1020604 1023155 := bstep (se 1 (by rfl) ⟨767366, by rfl⟩ : syracuseStep 1023155 = 1534733) B1534733
theorem B1023171 : Blo 1020604 1023171 := bstep (se 1 (by rfl) ⟨767378, by rfl⟩ : syracuseStep 1023171 = 1534757) B1534757
theorem B1940689 : Blo 1020604 1940689 := bstep (se 2 (by rfl) ⟨727758, by rfl⟩ : syracuseStep 1940689 = 1455517) B1455517
theorem B2301137 : Blo 1020604 2301137 := bstep (se 2 (by rfl) ⟨862926, by rfl⟩ : syracuseStep 2301137 = 1725853) B1725853
theorem B1023187 : Blo 1020604 1023187 := bstep (se 1 (by rfl) ⟨767390, by rfl⟩ : syracuseStep 1023187 = 1534781) B1534781
theorem B2301155 : Blo 1020604 2301155 := bstep (se 1 (by rfl) ⟨1725866, by rfl⟩ : syracuseStep 2301155 = 3451733) B3451733
theorem B1023203 : Blo 1020604 1023203 := bstep (se 1 (by rfl) ⟨767402, by rfl⟩ : syracuseStep 1023203 = 1534805) B1534805
theorem B1023219 : Blo 1020604 1023219 := bstep (se 1 (by rfl) ⟨767414, by rfl⟩ : syracuseStep 1023219 = 1534829) B1534829
theorem B1023235 : Blo 1020604 1023235 := bstep (se 1 (by rfl) ⟨767426, by rfl⟩ : syracuseStep 1023235 = 1534853) B1534853
theorem B1023251 : Blo 1020604 1023251 := bstep (se 1 (by rfl) ⟨767438, by rfl⟩ : syracuseStep 1023251 = 1534877) B1534877
theorem B1023267 : Blo 1020604 1023267 := bstep (se 1 (by rfl) ⟨767450, by rfl⟩ : syracuseStep 1023267 = 1534901) B1534901
theorem B1023283 : Blo 1020604 1023283 := bstep (se 1 (by rfl) ⟨767462, by rfl⟩ : syracuseStep 1023283 = 1534925) B1534925
theorem B1023299 : Blo 1020604 1023299 := bstep (se 1 (by rfl) ⟨767474, by rfl⟩ : syracuseStep 1023299 = 1534949) B1534949
theorem B2071889 : Blo 1020604 2071889 := bstep (se 2 (by rfl) ⟨776958, by rfl⟩ : syracuseStep 2071889 = 1553917) B1553917
theorem B1023315 : Blo 1020604 1023315 := bstep (se 1 (by rfl) ⟨767486, by rfl⟩ : syracuseStep 1023315 = 1534973) B1534973
theorem B1023331 : Blo 1020604 1023331 := bstep (se 1 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 1023331 = 1534997) B1534997
theorem B2071921 : Blo 1020604 2071921 := bstep (se 2 (by rfl) ⟨776970, by rfl⟩ : syracuseStep 2071921 = 1553941) B1553941
theorem B1023347 : Blo 1020604 1023347 := bstep (se 1 (by rfl) ⟨767510, by rfl⟩ : syracuseStep 1023347 = 1535021) B1535021
theorem B1023363 : Blo 1020604 1023363 := bstep (se 1 (by rfl) ⟨767522, by rfl⟩ : syracuseStep 1023363 = 1535045) B1535045
theorem B1023379 : Blo 1020604 1023379 := bstep (se 1 (by rfl) ⟨767534, by rfl⟩ : syracuseStep 1023379 = 1535069) B1535069
theorem B4365731 : Blo 1020604 4365731 := bstep (se 1 (by rfl) ⟨3274298, by rfl⟩ : syracuseStep 4365731 = 6548597) B6548597
theorem B1023395 : Blo 1020604 1023395 := bstep (se 1 (by rfl) ⟨767546, by rfl⟩ : syracuseStep 1023395 = 1535093) B1535093
theorem B1023411 : Blo 1020604 1023411 := bstep (se 1 (by rfl) ⟨767558, by rfl⟩ : syracuseStep 1023411 = 1535117) B1535117
theorem B1023427 : Blo 1020604 1023427 := bstep (se 1 (by rfl) ⟨767570, by rfl⟩ : syracuseStep 1023427 = 1535141) B1535141
theorem B1023443 : Blo 1020604 1023443 := bstep (se 1 (by rfl) ⟨767582, by rfl⟩ : syracuseStep 1023443 = 1535165) B1535165
theorem B1023459 : Blo 1020604 1023459 := bstep (se 1 (by rfl) ⟨767594, by rfl⟩ : syracuseStep 1023459 = 1535189) B1535189
theorem B2301425 : Blo 1020604 2301425 := bstep (se 2 (by rfl) ⟨863034, by rfl⟩ : syracuseStep 2301425 = 1726069) B1726069
theorem B1023475 : Blo 1020604 1023475 := bstep (se 1 (by rfl) ⟨767606, by rfl⟩ : syracuseStep 1023475 = 1535213) B1535213
theorem B2301443 : Blo 1020604 2301443 := bstep (se 1 (by rfl) ⟨1726082, by rfl⟩ : syracuseStep 2301443 = 3452165) B3452165
theorem B1023491 : Blo 1020604 1023491 := bstep (se 1 (by rfl) ⟨767618, by rfl⟩ : syracuseStep 1023491 = 1535237) B1535237
theorem B1023507 : Blo 1020604 1023507 := bstep (se 1 (by rfl) ⟨767630, by rfl⟩ : syracuseStep 1023507 = 1535261) B1535261
theorem B2760227 : Blo 1020604 2760227 := bstep (se 1 (by rfl) ⟨2070170, by rfl⟩ : syracuseStep 2760227 = 4140341) B4140341
theorem B1023523 : Blo 1020604 1023523 := bstep (se 1 (by rfl) ⟨767642, by rfl⟩ : syracuseStep 1023523 = 1535285) B1535285
theorem B1023539 : Blo 1020604 1023539 := bstep (se 1 (by rfl) ⟨767654, by rfl⟩ : syracuseStep 1023539 = 1535309) B1535309
theorem B1023555 : Blo 1020604 1023555 := bstep (se 1 (by rfl) ⟨767666, by rfl⟩ : syracuseStep 1023555 = 1535333) B1535333
theorem B1023571 : Blo 1020604 1023571 := bstep (se 1 (by rfl) ⟨767678, by rfl⟩ : syracuseStep 1023571 = 1535357) B1535357
theorem B1023587 : Blo 1020604 1023587 := bstep (se 1 (by rfl) ⟨767690, by rfl⟩ : syracuseStep 1023587 = 1535381) B1535381
theorem B1023603 : Blo 1020604 1023603 := bstep (se 1 (by rfl) ⟨767702, by rfl⟩ : syracuseStep 1023603 = 1535405) B1535405
theorem B1023619 : Blo 1020604 1023619 := bstep (se 1 (by rfl) ⟨767714, by rfl⟩ : syracuseStep 1023619 = 1535429) B1535429
theorem B1023635 : Blo 1020604 1023635 := bstep (se 1 (by rfl) ⟨767726, by rfl⟩ : syracuseStep 1023635 = 1535453) B1535453
theorem B1023651 : Blo 1020604 1023651 := bstep (se 1 (by rfl) ⟨767738, by rfl⟩ : syracuseStep 1023651 = 1535477) B1535477
theorem B3448493 : Blo 1020604 3448493 := bstep (se 3 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 3448493 = 1293185) B1293185
theorem B1023667 : Blo 1020604 1023667 := bstep (se 1 (by rfl) ⟨767750, by rfl⟩ : syracuseStep 1023667 = 1535501) B1535501
theorem B1023683 : Blo 1020604 1023683 := bstep (se 1 (by rfl) ⟨767762, by rfl⟩ : syracuseStep 1023683 = 1535525) B1535525
theorem B1023699 : Blo 1020604 1023699 := bstep (se 1 (by rfl) ⟨767774, by rfl⟩ : syracuseStep 1023699 = 1535549) B1535549
theorem B3448547 : Blo 1020604 3448547 := bstep (se 1 (by rfl) ⟨2586410, by rfl⟩ : syracuseStep 3448547 = 5172821) B5172821
theorem B1023715 : Blo 1020604 1023715 := bstep (se 1 (by rfl) ⟨767786, by rfl⟩ : syracuseStep 1023715 = 1535573) B1535573
theorem B1023731 : Blo 1020604 1023731 := bstep (se 1 (by rfl) ⟨767798, by rfl⟩ : syracuseStep 1023731 = 1535597) B1535597
theorem B1023747 : Blo 1020604 1023747 := bstep (se 1 (by rfl) ⟨767810, by rfl⟩ : syracuseStep 1023747 = 1535621) B1535621
theorem B2301713 : Blo 1020604 2301713 := bstep (se 2 (by rfl) ⟨863142, by rfl⟩ : syracuseStep 2301713 = 1726285) B1726285
theorem B1023763 : Blo 1020604 1023763 := bstep (se 1 (by rfl) ⟨767822, by rfl⟩ : syracuseStep 1023763 = 1535645) B1535645
theorem B2301731 : Blo 1020604 2301731 := bstep (se 1 (by rfl) ⟨1726298, by rfl⟩ : syracuseStep 2301731 = 3452597) B3452597
theorem B1023779 : Blo 1020604 1023779 := bstep (se 1 (by rfl) ⟨767834, by rfl⟩ : syracuseStep 1023779 = 1535669) B1535669
theorem B1023795 : Blo 1020604 1023795 := bstep (se 1 (by rfl) ⟨767846, by rfl⟩ : syracuseStep 1023795 = 1535693) B1535693
theorem B1023811 : Blo 1020604 1023811 := bstep (se 1 (by rfl) ⟨767858, by rfl⟩ : syracuseStep 1023811 = 1535717) B1535717
theorem B1023827 : Blo 1020604 1023827 := bstep (se 1 (by rfl) ⟨767870, by rfl⟩ : syracuseStep 1023827 = 1535741) B1535741
theorem B1023843 : Blo 1020604 1023843 := bstep (se 1 (by rfl) ⟨767882, by rfl⟩ : syracuseStep 1023843 = 1535765) B1535765
theorem B1023859 : Blo 1020604 1023859 := bstep (se 1 (by rfl) ⟨767894, by rfl⟩ : syracuseStep 1023859 = 1535789) B1535789
theorem B1023875 : Blo 1020604 1023875 := bstep (se 1 (by rfl) ⟨767906, by rfl⟩ : syracuseStep 1023875 = 1535813) B1535813
theorem B1023891 : Blo 1020604 1023891 := bstep (se 1 (by rfl) ⟨767918, by rfl⟩ : syracuseStep 1023891 = 1535837) B1535837
theorem B1023907 : Blo 1020604 1023907 := bstep (se 1 (by rfl) ⟨767930, by rfl⟩ : syracuseStep 1023907 = 1535861) B1535861
theorem B5185457 : Blo 1020604 5185457 := bstep (se 2 (by rfl) ⟨1944546, by rfl⟩ : syracuseStep 5185457 = 3889093) B3889093
theorem B1023923 : Blo 1020604 1023923 := bstep (se 1 (by rfl) ⟨767942, by rfl⟩ : syracuseStep 1023923 = 1535885) B1535885
theorem B1023939 : Blo 1020604 1023939 := bstep (se 1 (by rfl) ⟨767954, by rfl⟩ : syracuseStep 1023939 = 1535909) B1535909
theorem B1023955 : Blo 1020604 1023955 := bstep (se 1 (by rfl) ⟨767966, by rfl⟩ : syracuseStep 1023955 = 1535933) B1535933
theorem B1023971 : Blo 1020604 1023971 := bstep (se 1 (by rfl) ⟨767978, by rfl⟩ : syracuseStep 1023971 = 1535957) B1535957
theorem B3448817 : Blo 1020604 3448817 := bstep (se 2 (by rfl) ⟨1293306, by rfl⟩ : syracuseStep 3448817 = 2586613) B2586613
theorem B1023987 : Blo 1020604 1023987 := bstep (se 1 (by rfl) ⟨767990, by rfl⟩ : syracuseStep 1023987 = 1535981) B1535981
theorem B1024003 : Blo 1020604 1024003 := bstep (se 1 (by rfl) ⟨768002, by rfl⟩ : syracuseStep 1024003 = 1536005) B1536005
theorem B1024019 : Blo 1020604 1024019 := bstep (se 1 (by rfl) ⟨768014, by rfl⟩ : syracuseStep 1024019 = 1536029) B1536029
theorem B1024035 : Blo 1020604 1024035 := bstep (se 1 (by rfl) ⟨768026, by rfl⟩ : syracuseStep 1024035 = 1536053) B1536053
theorem B2302001 : Blo 1020604 2302001 := bstep (se 2 (by rfl) ⟨863250, by rfl⟩ : syracuseStep 2302001 = 1726501) B1726501
theorem B1024051 : Blo 1020604 1024051 := bstep (se 1 (by rfl) ⟨768038, by rfl⟩ : syracuseStep 1024051 = 1536077) B1536077
theorem B2302019 : Blo 1020604 2302019 := bstep (se 1 (by rfl) ⟨1726514, by rfl⟩ : syracuseStep 2302019 = 3453029) B3453029
theorem B1024067 : Blo 1020604 1024067 := bstep (se 1 (by rfl) ⟨768050, by rfl⟩ : syracuseStep 1024067 = 1536101) B1536101
theorem B1024083 : Blo 1020604 1024083 := bstep (se 1 (by rfl) ⟨768062, by rfl⟩ : syracuseStep 1024083 = 1536125) B1536125
theorem B1024099 : Blo 1020604 1024099 := bstep (se 1 (by rfl) ⟨768074, by rfl⟩ : syracuseStep 1024099 = 1536149) B1536149
theorem B1024115 : Blo 1020604 1024115 := bstep (se 1 (by rfl) ⟨768086, by rfl⟩ : syracuseStep 1024115 = 1536173) B1536173
theorem B1024131 : Blo 1020604 1024131 := bstep (se 1 (by rfl) ⟨768098, by rfl⟩ : syracuseStep 1024131 = 1536197) B1536197
theorem B1024147 : Blo 1020604 1024147 := bstep (se 1 (by rfl) ⟨768110, by rfl⟩ : syracuseStep 1024147 = 1536221) B1536221
theorem B1024163 : Blo 1020604 1024163 := bstep (se 1 (by rfl) ⟨768122, by rfl⟩ : syracuseStep 1024163 = 1536245) B1536245
theorem B1024179 : Blo 1020604 1024179 := bstep (se 1 (by rfl) ⟨768134, by rfl⟩ : syracuseStep 1024179 = 1536269) B1536269
theorem B1024195 : Blo 1020604 1024195 := bstep (se 1 (by rfl) ⟨768146, by rfl⟩ : syracuseStep 1024195 = 1536293) B1536293
theorem B1024211 : Blo 1020604 1024211 := bstep (se 1 (by rfl) ⟨768158, by rfl⟩ : syracuseStep 1024211 = 1536317) B1536317
theorem B1024227 : Blo 1020604 1024227 := bstep (se 1 (by rfl) ⟨768170, by rfl⟩ : syracuseStep 1024227 = 1536341) B1536341
theorem B1941745 : Blo 1020604 1941745 := bstep (se 2 (by rfl) ⟨728154, by rfl⟩ : syracuseStep 1941745 = 1456309) B1456309
theorem B1024243 : Blo 1020604 1024243 := bstep (se 1 (by rfl) ⟨768182, by rfl⟩ : syracuseStep 1024243 = 1536365) B1536365
theorem B1024259 : Blo 1020604 1024259 := bstep (se 1 (by rfl) ⟨768194, by rfl⟩ : syracuseStep 1024259 = 1536389) B1536389
theorem B1024275 : Blo 1020604 1024275 := bstep (se 1 (by rfl) ⟨768206, by rfl⟩ : syracuseStep 1024275 = 1536413) B1536413
theorem B1024291 : Blo 1020604 1024291 := bstep (se 1 (by rfl) ⟨768218, by rfl⟩ : syracuseStep 1024291 = 1536437) B1536437
theorem B1024307 : Blo 1020604 1024307 := bstep (se 1 (by rfl) ⟨768230, by rfl⟩ : syracuseStep 1024307 = 1536461) B1536461
theorem B1024323 : Blo 1020604 1024323 := bstep (se 1 (by rfl) ⟨768242, by rfl⟩ : syracuseStep 1024323 = 1536485) B1536485
theorem B2302289 : Blo 1020604 2302289 := bstep (se 2 (by rfl) ⟨863358, by rfl⟩ : syracuseStep 2302289 = 1726717) B1726717
theorem B1024339 : Blo 1020604 1024339 := bstep (se 1 (by rfl) ⟨768254, by rfl⟩ : syracuseStep 1024339 = 1536509) B1536509
theorem B2302307 : Blo 1020604 2302307 := bstep (se 1 (by rfl) ⟨1726730, by rfl⟩ : syracuseStep 2302307 = 3453461) B3453461
theorem B1024355 : Blo 1020604 1024355 := bstep (se 1 (by rfl) ⟨768266, by rfl⟩ : syracuseStep 1024355 = 1536533) B1536533
theorem B1024371 : Blo 1020604 1024371 := bstep (se 1 (by rfl) ⟨768278, by rfl⟩ : syracuseStep 1024371 = 1536557) B1536557
theorem B2761091 : Blo 1020604 2761091 := bstep (se 1 (by rfl) ⟨2070818, by rfl⟩ : syracuseStep 2761091 = 4141637) B4141637
theorem B1024387 : Blo 1020604 1024387 := bstep (se 1 (by rfl) ⟨768290, by rfl⟩ : syracuseStep 1024387 = 1536581) B1536581
theorem B1024403 : Blo 1020604 1024403 := bstep (se 1 (by rfl) ⟨768302, by rfl⟩ : syracuseStep 1024403 = 1536605) B1536605
theorem B1024419 : Blo 1020604 1024419 := bstep (se 1 (by rfl) ⟨768314, by rfl⟩ : syracuseStep 1024419 = 1536629) B1536629
theorem B2761133 : Blo 1020604 2761133 := bstep (se 3 (by rfl) ⟨517712, by rfl⟩ : syracuseStep 2761133 = 1035425) B1035425
theorem B1024435 : Blo 1020604 1024435 := bstep (se 1 (by rfl) ⟨768326, by rfl⟩ : syracuseStep 1024435 = 1536653) B1536653
theorem B1024451 : Blo 1020604 1024451 := bstep (se 1 (by rfl) ⟨768338, by rfl⟩ : syracuseStep 1024451 = 1536677) B1536677
theorem B1024467 : Blo 1020604 1024467 := bstep (se 1 (by rfl) ⟨768350, by rfl⟩ : syracuseStep 1024467 = 1536701) B1536701
theorem B7381475 : Blo 1020604 7381475 := bstep (se 1 (by rfl) ⟨5536106, by rfl⟩ : syracuseStep 7381475 = 11072213) B11072213
theorem B1024483 : Blo 1020604 1024483 := bstep (se 1 (by rfl) ⟨768362, by rfl⟩ : syracuseStep 1024483 = 1536725) B1536725
theorem B1024499 : Blo 1020604 1024499 := bstep (se 1 (by rfl) ⟨768374, by rfl⟩ : syracuseStep 1024499 = 1536749) B1536749
theorem B1024515 : Blo 1020604 1024515 := bstep (se 1 (by rfl) ⟨768386, by rfl⟩ : syracuseStep 1024515 = 1536773) B1536773
theorem B3449357 : Blo 1020604 3449357 := bstep (se 3 (by rfl) ⟨646754, by rfl⟩ : syracuseStep 3449357 = 1293509) B1293509
theorem B1679891 : Blo 1020604 1679891 := bstep (se 1 (by rfl) ⟨1259918, by rfl⟩ : syracuseStep 1679891 = 2519837) B2519837
theorem B1024531 : Blo 1020604 1024531 := bstep (se 1 (by rfl) ⟨768398, by rfl⟩ : syracuseStep 1024531 = 1536797) B1536797
theorem B1024547 : Blo 1020604 1024547 := bstep (se 1 (by rfl) ⟨768410, by rfl⟩ : syracuseStep 1024547 = 1536821) B1536821
theorem B1024563 : Blo 1020604 1024563 := bstep (se 1 (by rfl) ⟨768422, by rfl⟩ : syracuseStep 1024563 = 1536845) B1536845
theorem B3449411 : Blo 1020604 3449411 := bstep (se 1 (by rfl) ⟨2587058, by rfl⟩ : syracuseStep 3449411 = 5174117) B5174117
theorem B1024579 : Blo 1020604 1024579 := bstep (se 1 (by rfl) ⟨768434, by rfl⟩ : syracuseStep 1024579 = 1536869) B1536869
theorem B1024595 : Blo 1020604 1024595 := bstep (se 1 (by rfl) ⟨768446, by rfl⟩ : syracuseStep 1024595 = 1536893) B1536893
theorem B2302577 : Blo 1020604 2302577 := bstep (se 2 (by rfl) ⟨863466, by rfl⟩ : syracuseStep 2302577 = 1726933) B1726933
theorem B1942147 : Blo 1020604 1942147 := bstep (se 1 (by rfl) ⟨1456610, by rfl⟩ : syracuseStep 1942147 = 2913221) B2913221
theorem B2302595 : Blo 1020604 2302595 := bstep (se 1 (by rfl) ⟨1726946, by rfl⟩ : syracuseStep 2302595 = 3453893) B3453893
theorem B2073251 : Blo 1020604 2073251 := bstep (se 1 (by rfl) ⟨1554938, by rfl⟩ : syracuseStep 2073251 = 3109877) B3109877
theorem B1942193 : Blo 1020604 1942193 := bstep (se 2 (by rfl) ⟨728322, by rfl⟩ : syracuseStep 1942193 = 1456645) B1456645
theorem B3318509 : Blo 1020604 3318509 := bstep (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) B1244441
theorem B1843985 : Blo 1020604 1843985 := bstep (se 2 (by rfl) ⟨691494, by rfl⟩ : syracuseStep 1843985 = 1382989) B1382989
theorem B3449681 : Blo 1020604 3449681 := bstep (se 2 (by rfl) ⟨1293630, by rfl⟩ : syracuseStep 3449681 = 2587261) B2587261
theorem B2302865 : Blo 1020604 2302865 := bstep (se 2 (by rfl) ⟨863574, by rfl⟩ : syracuseStep 2302865 = 1727149) B1727149
theorem B2302883 : Blo 1020604 2302883 := bstep (se 1 (by rfl) ⟨1727162, by rfl⟩ : syracuseStep 2302883 = 3454325) B3454325
theorem B12624821 : Blo 1020604 12624821 := bstep (se 5 (by rfl) ⟨591788, by rfl⟩ : syracuseStep 12624821 = 1183577) B1183577
theorem B3875789 : Blo 1020604 3875789 := bstep (se 3 (by rfl) ⟨726710, by rfl⟩ : syracuseStep 3875789 = 1453421) B1453421
theorem B1942481 : Blo 1020604 1942481 := bstep (se 2 (by rfl) ⟨728430, by rfl⟩ : syracuseStep 1942481 = 1456861) B1456861
theorem B4662257 : Blo 1020604 4662257 := bstep (se 2 (by rfl) ⟨1748346, by rfl⟩ : syracuseStep 4662257 = 3496693) B3496693
theorem B14754869 : Blo 1020604 14754869 := bstep (se 5 (by rfl) ⟨691634, by rfl⟩ : syracuseStep 14754869 = 1383269) B1383269
theorem B2303153 : Blo 1020604 2303153 := bstep (se 2 (by rfl) ⟨863682, by rfl⟩ : syracuseStep 2303153 = 1727365) B1727365
theorem B2303171 : Blo 1020604 2303171 := bstep (se 1 (by rfl) ⟨1727378, by rfl⟩ : syracuseStep 2303171 = 3454757) B3454757
theorem B5186915 : Blo 1020604 5186915 := bstep (se 1 (by rfl) ⟨3890186, by rfl⟩ : syracuseStep 5186915 = 7780373) B7780373
theorem B3450221 : Blo 1020604 3450221 := bstep (se 3 (by rfl) ⟨646916, by rfl⟩ : syracuseStep 3450221 = 1293833) B1293833
theorem B3450275 : Blo 1020604 3450275 := bstep (se 1 (by rfl) ⟨2587706, by rfl⟩ : syracuseStep 3450275 = 5175413) B5175413
theorem B2303441 : Blo 1020604 2303441 := bstep (se 2 (by rfl) ⟨863790, by rfl⟩ : syracuseStep 2303441 = 1727581) B1727581
theorem B2303459 : Blo 1020604 2303459 := bstep (se 1 (by rfl) ⟨1727594, by rfl⟩ : syracuseStep 2303459 = 3455189) B3455189
theorem B1746481 : Blo 1020604 1746481 := bstep (se 2 (by rfl) ⟨654930, by rfl⟩ : syracuseStep 1746481 = 1309861) B1309861
theorem B16557709 : Blo 1020604 16557709 := bstep (se 3 (by rfl) ⟨3104570, by rfl⟩ : syracuseStep 16557709 = 6209141) B6209141
theorem B1943203 : Blo 1020604 1943203 := bstep (se 1 (by rfl) ⟨1457402, by rfl⟩ : syracuseStep 1943203 = 2914805) B2914805
theorem B3450545 : Blo 1020604 3450545 := bstep (se 2 (by rfl) ⟨1293954, by rfl⟩ : syracuseStep 3450545 = 2587909) B2587909
theorem B2303729 : Blo 1020604 2303729 := bstep (se 2 (by rfl) ⟨863898, by rfl⟩ : syracuseStep 2303729 = 1727797) B1727797
theorem B2303747 : Blo 1020604 2303747 := bstep (se 1 (by rfl) ⟨1727810, by rfl⟩ : syracuseStep 2303747 = 3455621) B3455621
theorem B3680099 : Blo 1020604 3680099 := bstep (se 1 (by rfl) ⟨2760074, by rfl⟩ : syracuseStep 3680099 = 5520149) B5520149
theorem B2762669 : Blo 1020604 2762669 := bstep (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) B1036001
theorem B13084685 : Blo 1020604 13084685 := bstep (se 3 (by rfl) ⟨2453378, by rfl⟩ : syracuseStep 13084685 = 4906757) B4906757
theorem B2304017 : Blo 1020604 2304017 := bstep (se 2 (by rfl) ⟨864006, by rfl⟩ : syracuseStep 2304017 = 1728013) B1728013
theorem B2304035 : Blo 1020604 2304035 := bstep (se 1 (by rfl) ⟨1728026, by rfl⟩ : syracuseStep 2304035 = 3456053) B3456053
theorem B1943651 : Blo 1020604 1943651 := bstep (se 1 (by rfl) ⟨1457738, by rfl⟩ : syracuseStep 1943651 = 2915477) B2915477
theorem B3451085 : Blo 1020604 3451085 := bstep (se 3 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 3451085 = 1294157) B1294157
theorem B3451139 : Blo 1020604 3451139 := bstep (se 1 (by rfl) ⟨2588354, by rfl⟩ : syracuseStep 3451139 = 5176709) B5176709
theorem B2304305 : Blo 1020604 2304305 := bstep (se 2 (by rfl) ⟨864114, by rfl⟩ : syracuseStep 2304305 = 1728229) B1728229
theorem B2304323 : Blo 1020604 2304323 := bstep (se 1 (by rfl) ⟨1728242, by rfl⟩ : syracuseStep 2304323 = 3456485) B3456485
theorem B1091971 : Blo 1020604 1091971 := bstep (se 1 (by rfl) ⟨818978, by rfl⟩ : syracuseStep 1091971 = 1637957) B1637957
theorem B1943939 : Blo 1020604 1943939 := bstep (se 1 (by rfl) ⟨1457954, by rfl⟩ : syracuseStep 1943939 = 2915909) B2915909
theorem B3451409 : Blo 1020604 3451409 := bstep (se 2 (by rfl) ⟨1294278, by rfl⟩ : syracuseStep 3451409 = 2588557) B2588557
theorem B2304593 : Blo 1020604 2304593 := bstep (se 2 (by rfl) ⟨864222, by rfl⟩ : syracuseStep 2304593 = 1728445) B1728445
theorem B2304611 : Blo 1020604 2304611 := bstep (se 1 (by rfl) ⟨1728458, by rfl⟩ : syracuseStep 2304611 = 3456917) B3456917
theorem B1092403 : Blo 1020604 1092403 := bstep (se 1 (by rfl) ⟨819302, by rfl⟩ : syracuseStep 1092403 = 1638605) B1638605
theorem B2304881 : Blo 1020604 2304881 := bstep (se 2 (by rfl) ⟨864330, by rfl⟩ : syracuseStep 2304881 = 1728661) B1728661
theorem B2304899 : Blo 1020604 2304899 := bstep (se 1 (by rfl) ⟨1728674, by rfl⟩ : syracuseStep 2304899 = 3457349) B3457349
theorem B1846147 : Blo 1020604 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B6990733 : Blo 1020604 6990733 := bstep (se 3 (by rfl) ⟨1310762, by rfl⟩ : syracuseStep 6990733 = 2621525) B2621525
theorem B3877901 : Blo 1020604 3877901 := bstep (se 3 (by rfl) ⟨727106, by rfl⟩ : syracuseStep 3877901 = 1454213) B1454213
theorem B3451949 : Blo 1020604 3451949 := bstep (se 3 (by rfl) ⟨647240, by rfl⟩ : syracuseStep 3451949 = 1294481) B1294481
theorem B3452003 : Blo 1020604 3452003 := bstep (se 1 (by rfl) ⟨2589002, by rfl⟩ : syracuseStep 3452003 = 5178005) B5178005
theorem B2305169 : Blo 1020604 2305169 := bstep (se 2 (by rfl) ⟨864438, by rfl⟩ : syracuseStep 2305169 = 1728877) B1728877
theorem B2305187 : Blo 1020604 2305187 := bstep (se 1 (by rfl) ⟨1728890, by rfl⟩ : syracuseStep 2305187 = 3457781) B3457781
theorem B1944881 : Blo 1020604 1944881 := bstep (se 2 (by rfl) ⟨729330, by rfl⟩ : syracuseStep 1944881 = 1458661) B1458661
theorem B23604533 : Blo 1020604 23604533 := bstep (se 5 (by rfl) ⟨1106462, by rfl⟩ : syracuseStep 23604533 = 2212925) B2212925
theorem B11054389 : Blo 1020604 11054389 := bstep (se 5 (by rfl) ⟨518174, by rfl⟩ : syracuseStep 11054389 = 1036349) B1036349
theorem B1453393 : Blo 1020604 1453393 := bstep (se 2 (by rfl) ⟨545022, by rfl⟩ : syracuseStep 1453393 = 1090045) B1090045
theorem B4369763 : Blo 1020604 4369763 := bstep (se 1 (by rfl) ⟨3277322, by rfl⟩ : syracuseStep 4369763 = 6554645) B6554645
theorem B4140401 : Blo 1020604 4140401 := bstep (se 2 (by rfl) ⟨1552650, by rfl⟩ : syracuseStep 4140401 = 3105301) B3105301
theorem B3452273 : Blo 1020604 3452273 := bstep (se 2 (by rfl) ⟨1294602, by rfl⟩ : syracuseStep 3452273 = 2589205) B2589205
theorem B3681713 : Blo 1020604 3681713 := bstep (se 2 (by rfl) ⟨1380642, by rfl⟩ : syracuseStep 3681713 = 2761285) B2761285
theorem B24915397 : Blo 1020604 24915397 := bstep (se 4 (by rfl) ⟨2335818, by rfl⟩ : syracuseStep 24915397 = 4671637) B4671637
theorem B4435469 : Blo 1020604 4435469 := bstep (se 3 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 4435469 = 1663301) B1663301
theorem B1453729 : Blo 1020604 1453729 := bstep (se 2 (by rfl) ⟨545148, by rfl⟩ : syracuseStep 1453729 = 1090297) B1090297
theorem B3878705 : Blo 1020604 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B3452813 : Blo 1020604 3452813 := bstep (se 3 (by rfl) ⟨647402, by rfl⟩ : syracuseStep 3452813 = 1294805) B1294805
theorem B3452867 : Blo 1020604 3452867 := bstep (se 1 (by rfl) ⟨2589650, by rfl⟩ : syracuseStep 3452867 = 5179301) B5179301
theorem B1093667 : Blo 1020604 1093667 := bstep (se 1 (by rfl) ⟨820250, by rfl⟩ : syracuseStep 1093667 = 1640501) B1640501
theorem B8400995 : Blo 1020604 8400995 := bstep (se 1 (by rfl) ⟨6300746, by rfl⟩ : syracuseStep 8400995 = 12601493) B12601493
theorem B3453137 : Blo 1020604 3453137 := bstep (se 2 (by rfl) ⟨1294926, by rfl⟩ : syracuseStep 3453137 = 2589853) B2589853
theorem B1749217 : Blo 1020604 1749217 := bstep (se 2 (by rfl) ⟨655956, by rfl⟩ : syracuseStep 1749217 = 1311913) B1311913
theorem B1454321 : Blo 1020604 1454321 := bstep (se 2 (by rfl) ⟨545370, by rfl⟩ : syracuseStep 1454321 = 1090741) B1090741
theorem B19640717 : Blo 1020604 19640717 := bstep (se 3 (by rfl) ⟨3682634, by rfl⟩ : syracuseStep 19640717 = 7365269) B7365269
theorem B3879373 : Blo 1020604 3879373 := bstep (se 3 (by rfl) ⟨727382, by rfl⟩ : syracuseStep 3879373 = 1454765) B1454765
theorem B4370993 : Blo 1020604 4370993 := bstep (se 2 (by rfl) ⟨1639122, by rfl⟩ : syracuseStep 4370993 = 3278245) B3278245
theorem B7778915 : Blo 1020604 7778915 := bstep (se 1 (by rfl) ⟨5834186, by rfl⟩ : syracuseStep 7778915 = 11668373) B11668373
theorem B3453677 : Blo 1020604 3453677 := bstep (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) B1295129
theorem B1454851 : Blo 1020604 1454851 := bstep (se 1 (by rfl) ⟨1091138, by rfl⟩ : syracuseStep 1454851 = 2182277) B2182277
theorem B3453731 : Blo 1020604 3453731 := bstep (se 1 (by rfl) ⟨2590298, by rfl⟩ : syracuseStep 3453731 = 5180597) B5180597
theorem B3683171 : Blo 1020604 3683171 := bstep (se 1 (by rfl) ⟨2762378, by rfl⟩ : syracuseStep 3683171 = 5524757) B5524757
theorem B1749937 : Blo 1020604 1749937 := bstep (se 2 (by rfl) ⟨656226, by rfl⟩ : syracuseStep 1749937 = 1312453) B1312453
theorem B3454001 : Blo 1020604 3454001 := bstep (se 2 (by rfl) ⟨1295250, by rfl⟩ : syracuseStep 3454001 = 2590501) B2590501
theorem B1455187 : Blo 1020604 1455187 := bstep (se 1 (by rfl) ⟨1091390, by rfl⟩ : syracuseStep 1455187 = 2182781) B2182781
theorem B1750099 : Blo 1020604 1750099 := bstep (se 1 (by rfl) ⟨1312574, by rfl⟩ : syracuseStep 1750099 = 2625149) B2625149
theorem B4142285 : Blo 1020604 4142285 := bstep (se 3 (by rfl) ⟨776678, by rfl⟩ : syracuseStep 4142285 = 1553357) B1553357
theorem B3880163 : Blo 1020604 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B1553843 : Blo 1020604 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B3683789 : Blo 1020604 3683789 := bstep (se 3 (by rfl) ⟨690710, by rfl⟩ : syracuseStep 3683789 = 1381421) B1381421
theorem B3454541 : Blo 1020604 3454541 := bstep (se 3 (by rfl) ⟨647726, by rfl⟩ : syracuseStep 3454541 = 1295453) B1295453
theorem B1455745 : Blo 1020604 1455745 := bstep (se 2 (by rfl) ⟨545904, by rfl⟩ : syracuseStep 1455745 = 1091809) B1091809
theorem B3454595 : Blo 1020604 3454595 := bstep (se 1 (by rfl) ⟨2590946, by rfl⟩ : syracuseStep 3454595 = 5181893) B5181893
theorem B1455779 : Blo 1020604 1455779 := bstep (se 1 (by rfl) ⟨1091834, by rfl⟩ : syracuseStep 1455779 = 2183669) B2183669
theorem B5813957 : Blo 1020604 5813957 := bstep (se 4 (by rfl) ⟨545058, by rfl⟩ : syracuseStep 5813957 = 1090117) B1090117
theorem B1292051 : Blo 1020604 1292051 := bstep (se 1 (by rfl) ⟨969038, by rfl⟩ : syracuseStep 1292051 = 1938077) B1938077
theorem B27997973 : Blo 1020604 27997973 := bstep (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) B1312405
theorem B3880817 : Blo 1020604 3880817 := bstep (se 2 (by rfl) ⟨1455306, by rfl⟩ : syracuseStep 3880817 = 2910613) B2910613
theorem B3454865 : Blo 1020604 3454865 := bstep (se 2 (by rfl) ⟨1295574, by rfl⟩ : syracuseStep 3454865 = 2591149) B2591149
theorem B14956597 : Blo 1020604 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B5814413 : Blo 1020604 5814413 := bstep (se 3 (by rfl) ⟨1090202, by rfl⟩ : syracuseStep 5814413 = 2180405) B2180405
theorem B5519501 : Blo 1020604 5519501 := bstep (se 3 (by rfl) ⟨1034906, by rfl⟩ : syracuseStep 5519501 = 2069813) B2069813
theorem B1456337 : Blo 1020604 1456337 := bstep (se 2 (by rfl) ⟨546126, by rfl⟩ : syracuseStep 1456337 = 1092253) B1092253
theorem B1456417 : Blo 1020604 1456417 := bstep (se 2 (by rfl) ⟨546156, by rfl⟩ : syracuseStep 1456417 = 1092313) B1092313
theorem B3455405 : Blo 1020604 3455405 := bstep (se 3 (by rfl) ⟨647888, by rfl⟩ : syracuseStep 3455405 = 1295777) B1295777
theorem B1292755 : Blo 1020604 1292755 := bstep (se 1 (by rfl) ⟨969566, by rfl⟩ : syracuseStep 1292755 = 1939133) B1939133
theorem B19675619 : Blo 1020604 19675619 := bstep (se 1 (by rfl) ⟨14756714, by rfl⟩ : syracuseStep 19675619 = 29513429) B29513429
theorem B4733411 : Blo 1020604 4733411 := bstep (se 1 (by rfl) ⟨3550058, by rfl⟩ : syracuseStep 4733411 = 7100117) B7100117
theorem B3455459 : Blo 1020604 3455459 := bstep (se 1 (by rfl) ⟨2591594, by rfl⟩ : syracuseStep 3455459 = 5183189) B5183189
theorem B2767405 : Blo 1020604 2767405 := bstep (se 3 (by rfl) ⟨518888, by rfl⟩ : syracuseStep 2767405 = 1037777) B1037777
theorem B1292851 : Blo 1020604 1292851 := bstep (se 1 (by rfl) ⟨969638, by rfl⟩ : syracuseStep 1292851 = 1939277) B1939277
theorem B5323427 : Blo 1020604 5323427 := bstep (se 1 (by rfl) ⟨3992570, by rfl⟩ : syracuseStep 5323427 = 7985141) B7985141
theorem B3455729 : Blo 1020604 3455729 := bstep (se 2 (by rfl) ⟨1295898, by rfl⟩ : syracuseStep 3455729 = 2591797) B2591797
theorem B4799345 : Blo 1020604 4799345 := bstep (se 2 (by rfl) ⟨1799754, by rfl⟩ : syracuseStep 4799345 = 3599509) B3599509
theorem B4373453 : Blo 1020604 4373453 := bstep (se 3 (by rfl) ⟨820022, by rfl⟩ : syracuseStep 4373453 = 1640045) B1640045
theorem B1293347 : Blo 1020604 1293347 := bstep (se 1 (by rfl) ⟨970010, by rfl⟩ : syracuseStep 1293347 = 1940021) B1940021
theorem B1457203 : Blo 1020604 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B1555571 : Blo 1020604 1555571 := bstep (se 1 (by rfl) ⟨1166678, by rfl⟩ : syracuseStep 1555571 = 2333357) B2333357
theorem B6208753 : Blo 1020604 6208753 := bstep (se 2 (by rfl) ⟨2328282, by rfl⟩ : syracuseStep 6208753 = 4656565) B4656565
theorem B3456269 : Blo 1020604 3456269 := bstep (se 3 (by rfl) ⟨648050, by rfl⟩ : syracuseStep 3456269 = 1296101) B1296101
theorem B3882275 : Blo 1020604 3882275 := bstep (se 1 (by rfl) ⟨2911706, by rfl⟩ : syracuseStep 3882275 = 5823413) B5823413
theorem B3882289 : Blo 1020604 3882289 := bstep (se 2 (by rfl) ⟨1455858, by rfl⟩ : syracuseStep 3882289 = 2911717) B2911717
theorem B3456323 : Blo 1020604 3456323 := bstep (se 1 (by rfl) ⟨2592242, by rfl⟩ : syracuseStep 3456323 = 5184485) B5184485
theorem B2768269 : Blo 1020604 2768269 := bstep (se 3 (by rfl) ⟨519050, by rfl⟩ : syracuseStep 2768269 = 1038101) B1038101
theorem B1555985 : Blo 1020604 1555985 := bstep (se 2 (by rfl) ⟨583494, by rfl⟩ : syracuseStep 1555985 = 1166989) B1166989
theorem B1457681 : Blo 1020604 1457681 := bstep (se 2 (by rfl) ⟨546630, by rfl⟩ : syracuseStep 1457681 = 1093261) B1093261
theorem B3456593 : Blo 1020604 3456593 := bstep (se 2 (by rfl) ⟨1296222, by rfl⟩ : syracuseStep 3456593 = 2592445) B2592445
theorem B1457795 : Blo 1020604 1457795 := bstep (se 1 (by rfl) ⟨1093346, by rfl⟩ : syracuseStep 1457795 = 2186693) B2186693
theorem B1457875 : Blo 1020604 1457875 := bstep (se 1 (by rfl) ⟨1093406, by rfl⟩ : syracuseStep 1457875 = 2186813) B2186813
theorem B1294051 : Blo 1020604 1294051 := bstep (se 1 (by rfl) ⟨970538, by rfl⟩ : syracuseStep 1294051 = 1941077) B1941077
theorem B6209315 : Blo 1020604 6209315 := bstep (se 1 (by rfl) ⟨4656986, by rfl⟩ : syracuseStep 6209315 = 9313973) B9313973
theorem B1294147 : Blo 1020604 1294147 := bstep (se 1 (by rfl) ⟨970610, by rfl⟩ : syracuseStep 1294147 = 1941221) B1941221
theorem B1556417 : Blo 1020604 1556417 := bstep (se 2 (by rfl) ⟨583656, by rfl⟩ : syracuseStep 1556417 = 1167313) B1167313
theorem B3457133 : Blo 1020604 3457133 := bstep (se 3 (by rfl) ⟨648212, by rfl⟩ : syracuseStep 3457133 = 1296425) B1296425
theorem B6996131 : Blo 1020604 6996131 := bstep (se 1 (by rfl) ⟨5247098, by rfl⟩ : syracuseStep 6996131 = 10494197) B10494197
theorem B3457187 : Blo 1020604 3457187 := bstep (se 1 (by rfl) ⟨2592890, by rfl⟩ : syracuseStep 3457187 = 5185781) B5185781
theorem B6209777 : Blo 1020604 6209777 := bstep (se 2 (by rfl) ⟨2328666, by rfl⟩ : syracuseStep 6209777 = 4657333) B4657333
theorem B1458433 : Blo 1020604 1458433 := bstep (se 2 (by rfl) ⟨546912, by rfl⟩ : syracuseStep 1458433 = 1093825) B1093825
theorem B1294643 : Blo 1020604 1294643 := bstep (se 1 (by rfl) ⟨970982, by rfl⟩ : syracuseStep 1294643 = 1941965) B1941965
theorem B1622371 : Blo 1020604 1622371 := bstep (se 1 (by rfl) ⟨1216778, by rfl⟩ : syracuseStep 1622371 = 2433557) B2433557
theorem B3457457 : Blo 1020604 3457457 := bstep (se 2 (by rfl) ⟨1296546, by rfl⟩ : syracuseStep 3457457 = 2593093) B2593093
theorem B1229299 : Blo 1020604 1229299 := bstep (se 1 (by rfl) ⟨921974, by rfl⟩ : syracuseStep 1229299 = 1843949) B1843949
theorem B3883747 : Blo 1020604 3883747 := bstep (se 1 (by rfl) ⟨2912810, by rfl⟩ : syracuseStep 3883747 = 5825621) B5825621
theorem B8733581 : Blo 1020604 8733581 := bstep (se 3 (by rfl) ⟨1637546, by rfl⟩ : syracuseStep 8733581 = 3275093) B3275093
theorem B1164179 : Blo 1020604 1164179 := bstep (se 1 (by rfl) ⟨873134, by rfl⟩ : syracuseStep 1164179 = 1746269) B1746269
theorem B3457997 : Blo 1020604 3457997 := bstep (se 3 (by rfl) ⟨648374, by rfl⟩ : syracuseStep 3457997 = 1296749) B1296749
theorem B5817329 : Blo 1020604 5817329 := bstep (se 2 (by rfl) ⟨2181498, by rfl⟩ : syracuseStep 5817329 = 4362997) B4362997
theorem B1295347 : Blo 1020604 1295347 := bstep (se 1 (by rfl) ⟨971510, by rfl⟩ : syracuseStep 1295347 = 1943021) B1943021
theorem B1557505 : Blo 1020604 1557505 := bstep (se 2 (by rfl) ⟨584064, by rfl⟩ : syracuseStep 1557505 = 1168129) B1168129
theorem B3687437 : Blo 1020604 3687437 := bstep (se 3 (by rfl) ⟨691394, by rfl⟩ : syracuseStep 3687437 = 1382789) B1382789
theorem B1295443 : Blo 1020604 1295443 := bstep (se 1 (by rfl) ⟨971582, by rfl⟩ : syracuseStep 1295443 = 1943165) B1943165
theorem B2245745 : Blo 1020604 2245745 := bstep (se 2 (by rfl) ⟨842154, by rfl⟩ : syracuseStep 2245745 = 1684309) B1684309
theorem B6210701 : Blo 1020604 6210701 := bstep (se 3 (by rfl) ⟨1164506, by rfl⟩ : syracuseStep 6210701 = 2329013) B2329013
theorem B17712269 : Blo 1020604 17712269 := bstep (se 3 (by rfl) ⟨3321050, by rfl⟩ : syracuseStep 17712269 = 6642101) B6642101
theorem B3687565 : Blo 1020604 3687565 := bstep (se 3 (by rfl) ⟨691418, by rfl⟩ : syracuseStep 3687565 = 1382837) B1382837
theorem B1557809 : Blo 1020604 1557809 := bstep (se 2 (by rfl) ⟨584178, by rfl⟩ : syracuseStep 1557809 = 1168357) B1168357
theorem B1230275 : Blo 1020604 1230275 := bstep (se 1 (by rfl) ⟨922706, by rfl⟩ : syracuseStep 1230275 = 1845413) B1845413
theorem B1295939 : Blo 1020604 1295939 := bstep (se 1 (by rfl) ⟨971954, by rfl⟩ : syracuseStep 1295939 = 1943909) B1943909
theorem B2180849 : Blo 1020604 2180849 := bstep (se 2 (by rfl) ⟨817818, by rfl⟩ : syracuseStep 2180849 = 1635637) B1635637
theorem B6211333 : Blo 1020604 6211333 := bstep (se 4 (by rfl) ⟨582312, by rfl⟩ : syracuseStep 6211333 = 1164625) B1164625
theorem B1722289 : Blo 1020604 1722289 := bstep (se 2 (by rfl) ⟨645858, by rfl⟩ : syracuseStep 1722289 = 1291717) B1291717
theorem B1722323 : Blo 1020604 1722323 := bstep (se 1 (by rfl) ⟨1291742, by rfl⟩ : syracuseStep 1722323 = 2583485) B2583485
theorem B4147213 : Blo 1020604 4147213 := bstep (se 3 (by rfl) ⟨777602, by rfl⟩ : syracuseStep 4147213 = 1555205) B1555205
theorem B1722451 : Blo 1020604 1722451 := bstep (se 1 (by rfl) ⟨1291838, by rfl⟩ : syracuseStep 1722451 = 2583677) B2583677
theorem B3492017 : Blo 1020604 3492017 := bstep (se 2 (by rfl) ⟨1309506, by rfl⟩ : syracuseStep 3492017 = 2619013) B2619013
theorem B1722593 : Blo 1020604 1722593 := bstep (se 2 (by rfl) ⟨645972, by rfl⟩ : syracuseStep 1722593 = 1291945) B1291945
theorem B1296643 : Blo 1020604 1296643 := bstep (se 1 (by rfl) ⟨972482, by rfl⟩ : syracuseStep 1296643 = 1944965) B1944965
theorem B6539525 : Blo 1020604 6539525 := bstep (se 4 (by rfl) ⟨613080, by rfl⟩ : syracuseStep 6539525 = 1226161) B1226161
theorem B1722721 : Blo 1020604 1722721 := bstep (se 2 (by rfl) ⟨646020, by rfl⟩ : syracuseStep 1722721 = 1292041) B1292041
theorem B1296739 : Blo 1020604 1296739 := bstep (se 1 (by rfl) ⟨972554, by rfl⟩ : syracuseStep 1296739 = 1945109) B1945109
theorem B1722755 : Blo 1020604 1722755 := bstep (se 1 (by rfl) ⟨1292066, by rfl⟩ : syracuseStep 1722755 = 2584133) B2584133
theorem B5818787 : Blo 1020604 5818787 := bstep (se 1 (by rfl) ⟨4364090, by rfl⟩ : syracuseStep 5818787 = 8728181) B8728181
theorem B1722883 : Blo 1020604 1722883 := bstep (se 1 (by rfl) ⟨1292162, by rfl⟩ : syracuseStep 1722883 = 2584325) B2584325
theorem B26528309 : Blo 1020604 26528309 := bstep (se 5 (by rfl) ⟨1243514, by rfl⟩ : syracuseStep 26528309 = 2487029) B2487029
theorem B1723025 : Blo 1020604 1723025 := bstep (se 2 (by rfl) ⟨646134, by rfl⟩ : syracuseStep 1723025 = 1292269) B1292269
theorem B11062001 : Blo 1020604 11062001 := bstep (se 2 (by rfl) ⟨4148250, by rfl⟩ : syracuseStep 11062001 = 8296501) B8296501
theorem B1723153 : Blo 1020604 1723153 := bstep (se 2 (by rfl) ⟨646182, by rfl⟩ : syracuseStep 1723153 = 1292365) B1292365
theorem B1723187 : Blo 1020604 1723187 := bstep (se 1 (by rfl) ⟨1292390, by rfl⟩ : syracuseStep 1723187 = 2584781) B2584781
theorem B5524301 : Blo 1020604 5524301 := bstep (se 3 (by rfl) ⟨1035806, by rfl⟩ : syracuseStep 5524301 = 2071613) B2071613
theorem B3885965 : Blo 1020604 3885965 := bstep (se 3 (by rfl) ⟨728618, by rfl⟩ : syracuseStep 3885965 = 1457237) B1457237
theorem B1723315 : Blo 1020604 1723315 := bstep (se 1 (by rfl) ⟨1292486, by rfl⟩ : syracuseStep 1723315 = 2584973) B2584973
theorem B1723457 : Blo 1020604 1723457 := bstep (se 2 (by rfl) ⟨646296, by rfl⟩ : syracuseStep 1723457 = 1292593) B1292593
theorem B1723585 : Blo 1020604 1723585 := bstep (se 2 (by rfl) ⟨646344, by rfl⟩ : syracuseStep 1723585 = 1292689) B1292689
theorem B1723619 : Blo 1020604 1723619 := bstep (se 1 (by rfl) ⟨1292714, by rfl⟩ : syracuseStep 1723619 = 2585429) B2585429
theorem B17452259 : Blo 1020604 17452259 := bstep (se 1 (by rfl) ⟨13089194, by rfl⟩ : syracuseStep 17452259 = 26178389) B26178389
theorem B8735971 : Blo 1020604 8735971 := bstep (se 1 (by rfl) ⟨6551978, by rfl⟩ : syracuseStep 8735971 = 13103957) B13103957
theorem B1723747 : Blo 1020604 1723747 := bstep (se 1 (by rfl) ⟨1292810, by rfl⟩ : syracuseStep 1723747 = 2585621) B2585621
theorem B5819789 : Blo 1020604 5819789 := bstep (se 3 (by rfl) ⟨1091210, by rfl⟩ : syracuseStep 5819789 = 2182421) B2182421
theorem B7753157 : Blo 1020604 7753157 := bstep (se 4 (by rfl) ⟨726858, by rfl⟩ : syracuseStep 7753157 = 1453717) B1453717
theorem B1723889 : Blo 1020604 1723889 := bstep (se 2 (by rfl) ⟨646458, by rfl⟩ : syracuseStep 1723889 = 1292917) B1292917
theorem B1724017 : Blo 1020604 1724017 := bstep (se 2 (by rfl) ⟨646506, by rfl⟩ : syracuseStep 1724017 = 1293013) B1293013
theorem B1724051 : Blo 1020604 1724051 := bstep (se 1 (by rfl) ⟨1293038, by rfl⟩ : syracuseStep 1724051 = 2586077) B2586077
theorem B7884557 : Blo 1020604 7884557 := bstep (se 3 (by rfl) ⟨1478354, by rfl⟩ : syracuseStep 7884557 = 2956709) B2956709
theorem B1724179 : Blo 1020604 1724179 := bstep (se 1 (by rfl) ⟨1293134, by rfl⟩ : syracuseStep 1724179 = 2586269) B2586269
theorem B50417549 : Blo 1020604 50417549 := bstep (se 3 (by rfl) ⟨9453290, by rfl⟩ : syracuseStep 50417549 = 18906581) B18906581
theorem B1724321 : Blo 1020604 1724321 := bstep (se 2 (by rfl) ⟨646620, by rfl⟩ : syracuseStep 1724321 = 1293241) B1293241
theorem B1724449 : Blo 1020604 1724449 := bstep (se 2 (by rfl) ⟨646668, by rfl⟩ : syracuseStep 1724449 = 1293337) B1293337
theorem B1724483 : Blo 1020604 1724483 := bstep (se 1 (by rfl) ⟨1293362, by rfl⟩ : syracuseStep 1724483 = 2586725) B2586725
theorem B1724611 : Blo 1020604 1724611 := bstep (se 1 (by rfl) ⟨1293458, by rfl⟩ : syracuseStep 1724611 = 2586917) B2586917
theorem B12439793 : Blo 1020604 12439793 := bstep (se 2 (by rfl) ⟨4664922, by rfl⟩ : syracuseStep 12439793 = 9329845) B9329845
theorem B1724753 : Blo 1020604 1724753 := bstep (se 2 (by rfl) ⟨646782, by rfl⟩ : syracuseStep 1724753 = 1293565) B1293565
theorem B1036739 : Blo 1020604 1036739 := bstep (se 1 (by rfl) ⟨777554, by rfl⟩ : syracuseStep 1036739 = 1555109) B1555109
theorem B1724881 : Blo 1020604 1724881 := bstep (se 2 (by rfl) ⟨646830, by rfl⟩ : syracuseStep 1724881 = 1293661) B1293661
theorem B7885297 : Blo 1020604 7885297 := bstep (se 2 (by rfl) ⟨2956986, by rfl⟩ : syracuseStep 7885297 = 5913973) B5913973
theorem B1724915 : Blo 1020604 1724915 := bstep (se 1 (by rfl) ⟨1293686, by rfl⟩ : syracuseStep 1724915 = 2587373) B2587373
theorem B1725043 : Blo 1020604 1725043 := bstep (se 1 (by rfl) ⟨1293782, by rfl⟩ : syracuseStep 1725043 = 2587565) B2587565
theorem B15127181 : Blo 1020604 15127181 := bstep (se 3 (by rfl) ⟨2836346, by rfl⟩ : syracuseStep 15127181 = 5672693) B5672693
theorem B5526157 : Blo 1020604 5526157 := bstep (se 3 (by rfl) ⟨1036154, by rfl⟩ : syracuseStep 5526157 = 2072309) B2072309
theorem B1725185 : Blo 1020604 1725185 := bstep (se 2 (by rfl) ⟨646944, by rfl⟩ : syracuseStep 1725185 = 1293889) B1293889
theorem B1725313 : Blo 1020604 1725313 := bstep (se 2 (by rfl) ⟨646992, by rfl⟩ : syracuseStep 1725313 = 1293985) B1293985
theorem B1725347 : Blo 1020604 1725347 := bstep (se 1 (by rfl) ⟨1294010, by rfl⟩ : syracuseStep 1725347 = 2588021) B2588021
theorem B1725475 : Blo 1020604 1725475 := bstep (se 1 (by rfl) ⟨1294106, by rfl⟩ : syracuseStep 1725475 = 2588213) B2588213
theorem B2184259 : Blo 1020604 2184259 := bstep (se 1 (by rfl) ⟨1638194, by rfl⟩ : syracuseStep 2184259 = 3276389) B3276389
theorem B2217041 : Blo 1020604 2217041 := bstep (se 2 (by rfl) ⟨831390, by rfl⟩ : syracuseStep 2217041 = 1662781) B1662781
theorem B1725617 : Blo 1020604 1725617 := bstep (se 2 (by rfl) ⟨647106, by rfl⟩ : syracuseStep 1725617 = 1294213) B1294213
theorem B3691747 : Blo 1020604 3691747 := bstep (se 1 (by rfl) ⟨2768810, by rfl⟩ : syracuseStep 3691747 = 5537621) B5537621
theorem B29480213 : Blo 1020604 29480213 := bstep (se 6 (by rfl) ⟨690942, by rfl⟩ : syracuseStep 29480213 = 1381885) B1381885
theorem B1725745 : Blo 1020604 1725745 := bstep (se 2 (by rfl) ⟨647154, by rfl⟩ : syracuseStep 1725745 = 1294309) B1294309
theorem B1725779 : Blo 1020604 1725779 := bstep (se 1 (by rfl) ⟨1294334, by rfl⟩ : syracuseStep 1725779 = 2588669) B2588669
theorem B1725907 : Blo 1020604 1725907 := bstep (se 1 (by rfl) ⟨1294430, by rfl⟩ : syracuseStep 1725907 = 2588861) B2588861
theorem B1726049 : Blo 1020604 1726049 := bstep (se 2 (by rfl) ⟨647268, by rfl⟩ : syracuseStep 1726049 = 1294537) B1294537
theorem B28038797 : Blo 1020604 28038797 := bstep (se 3 (by rfl) ⟨5257274, by rfl⟩ : syracuseStep 28038797 = 10514549) B10514549
theorem B1726177 : Blo 1020604 1726177 := bstep (se 2 (by rfl) ⟨647316, by rfl⟩ : syracuseStep 1726177 = 1294633) B1294633
theorem B3888881 : Blo 1020604 3888881 := bstep (se 2 (by rfl) ⟨1458330, by rfl⟩ : syracuseStep 3888881 = 2916661) B2916661
theorem B1726211 : Blo 1020604 1726211 := bstep (se 1 (by rfl) ⟨1294658, by rfl⟩ : syracuseStep 1726211 = 2589317) B2589317
theorem B6543139 : Blo 1020604 6543139 := bstep (se 1 (by rfl) ⟨4907354, by rfl⟩ : syracuseStep 6543139 = 9814709) B9814709
theorem B16570165 : Blo 1020604 16570165 := bstep (se 5 (by rfl) ⟨776726, by rfl⟩ : syracuseStep 16570165 = 1553453) B1553453
theorem B1726339 : Blo 1020604 1726339 := bstep (se 1 (by rfl) ⟨1294754, by rfl⟩ : syracuseStep 1726339 = 2589509) B2589509
theorem B5166989 : Blo 1020604 5166989 := bstep (se 3 (by rfl) ⟨968810, by rfl⟩ : syracuseStep 5166989 = 1937621) B1937621
theorem B1038227 : Blo 1020604 1038227 := bstep (se 1 (by rfl) ⟨778670, by rfl⟩ : syracuseStep 1038227 = 1557341) B1557341
theorem B1726481 : Blo 1020604 1726481 := bstep (se 2 (by rfl) ⟨647430, by rfl⟩ : syracuseStep 1726481 = 1294861) B1294861
theorem B1726609 : Blo 1020604 1726609 := bstep (se 2 (by rfl) ⟨647478, by rfl⟩ : syracuseStep 1726609 = 1294957) B1294957
theorem B1726643 : Blo 1020604 1726643 := bstep (se 1 (by rfl) ⟨1294982, by rfl⟩ : syracuseStep 1726643 = 2589965) B2589965
theorem B5822705 : Blo 1020604 5822705 := bstep (se 2 (by rfl) ⟨2183514, by rfl⟩ : syracuseStep 5822705 = 4367029) B4367029
theorem B1726771 : Blo 1020604 1726771 := bstep (se 1 (by rfl) ⟨1295078, by rfl⟩ : syracuseStep 1726771 = 2590157) B2590157
theorem B2906513 : Blo 1020604 2906513 := bstep (se 2 (by rfl) ⟨1089942, by rfl⟩ : syracuseStep 2906513 = 2179885) B2179885
theorem B1726913 : Blo 1020604 1726913 := bstep (se 2 (by rfl) ⟨647592, by rfl⟩ : syracuseStep 1726913 = 1295185) B1295185
theorem B1727041 : Blo 1020604 1727041 := bstep (se 2 (by rfl) ⟨647640, by rfl⟩ : syracuseStep 1727041 = 1295281) B1295281
theorem B2906705 : Blo 1020604 2906705 := bstep (se 2 (by rfl) ⟨1090014, by rfl⟩ : syracuseStep 2906705 = 2180029) B2180029
theorem B1727075 : Blo 1020604 1727075 := bstep (se 1 (by rfl) ⟨1295306, by rfl⟩ : syracuseStep 1727075 = 2590613) B2590613
theorem B1727203 : Blo 1020604 1727203 := bstep (se 1 (by rfl) ⟨1295402, by rfl⟩ : syracuseStep 1727203 = 2590805) B2590805
theorem B1727345 : Blo 1020604 1727345 := bstep (se 2 (by rfl) ⟨647754, by rfl⟩ : syracuseStep 1727345 = 1295509) B1295509
theorem B2186129 : Blo 1020604 2186129 := bstep (se 2 (by rfl) ⟨819798, by rfl⟩ : syracuseStep 2186129 = 1639597) B1639597
theorem B1727473 : Blo 1020604 1727473 := bstep (se 2 (by rfl) ⟨647802, by rfl⟩ : syracuseStep 1727473 = 1295605) B1295605
theorem B1727507 : Blo 1020604 1727507 := bstep (se 1 (by rfl) ⟨1295630, by rfl⟩ : syracuseStep 1727507 = 2591261) B2591261
theorem B1530929 : Blo 1020604 1530929 := bstep (se 2 (by rfl) ⟨574098, by rfl⟩ : syracuseStep 1530929 = 1148197) B1148197
theorem B1530947 : Blo 1020604 1530947 := bstep (se 1 (by rfl) ⟨1148210, by rfl⟩ : syracuseStep 1530947 = 2296421) B2296421
theorem B1530977 : Blo 1020604 1530977 := bstep (se 2 (by rfl) ⟨574116, by rfl⟩ : syracuseStep 1530977 = 1148233) B1148233
theorem B1530995 : Blo 1020604 1530995 := bstep (se 1 (by rfl) ⟨1148246, by rfl⟩ : syracuseStep 1530995 = 2296493) B2296493
theorem B1531025 : Blo 1020604 1531025 := bstep (se 2 (by rfl) ⟨574134, by rfl⟩ : syracuseStep 1531025 = 1148269) B1148269
theorem B1727635 : Blo 1020604 1727635 := bstep (se 1 (by rfl) ⟨1295726, by rfl⟩ : syracuseStep 1727635 = 2591453) B2591453
theorem B1531043 : Blo 1020604 1531043 := bstep (se 1 (by rfl) ⟨1148282, by rfl⟩ : syracuseStep 1531043 = 2296565) B2296565
theorem B1531073 : Blo 1020604 1531073 := bstep (se 2 (by rfl) ⟨574152, by rfl⟩ : syracuseStep 1531073 = 1148305) B1148305
theorem B1531091 : Blo 1020604 1531091 := bstep (se 1 (by rfl) ⟨1148318, by rfl⟩ : syracuseStep 1531091 = 2296637) B2296637
theorem B1531121 : Blo 1020604 1531121 := bstep (se 2 (by rfl) ⟨574170, by rfl⟩ : syracuseStep 1531121 = 1148341) B1148341
theorem B1531139 : Blo 1020604 1531139 := bstep (se 1 (by rfl) ⟨1148354, by rfl⟩ : syracuseStep 1531139 = 2296709) B2296709
theorem B1531169 : Blo 1020604 1531169 := bstep (se 2 (by rfl) ⟨574188, by rfl⟩ : syracuseStep 1531169 = 1148377) B1148377
theorem B1727777 : Blo 1020604 1727777 := bstep (se 2 (by rfl) ⟨647916, by rfl⟩ : syracuseStep 1727777 = 1295833) B1295833
theorem B1531187 : Blo 1020604 1531187 := bstep (se 1 (by rfl) ⟨1148390, by rfl⟩ : syracuseStep 1531187 = 2296781) B2296781
theorem B1531217 : Blo 1020604 1531217 := bstep (se 2 (by rfl) ⟨574206, by rfl⟩ : syracuseStep 1531217 = 1148413) B1148413
theorem B1531235 : Blo 1020604 1531235 := bstep (se 1 (by rfl) ⟨1148426, by rfl⟩ : syracuseStep 1531235 = 2296853) B2296853
theorem B1531265 : Blo 1020604 1531265 := bstep (se 2 (by rfl) ⟨574224, by rfl⟩ : syracuseStep 1531265 = 1148449) B1148449
theorem B9330061 : Blo 1020604 9330061 := bstep (se 3 (by rfl) ⟨1749386, by rfl⟩ : syracuseStep 9330061 = 3498773) B3498773
theorem B1531283 : Blo 1020604 1531283 := bstep (se 1 (by rfl) ⟨1148462, by rfl⟩ : syracuseStep 1531283 = 2296925) B2296925
theorem B1727905 : Blo 1020604 1727905 := bstep (se 2 (by rfl) ⟨647964, by rfl⟩ : syracuseStep 1727905 = 1295929) B1295929
theorem B1531313 : Blo 1020604 1531313 := bstep (se 2 (by rfl) ⟨574242, by rfl⟩ : syracuseStep 1531313 = 1148485) B1148485
theorem B1531331 : Blo 1020604 1531331 := bstep (se 1 (by rfl) ⟨1148498, by rfl⟩ : syracuseStep 1531331 = 2296997) B2296997
theorem B1727939 : Blo 1020604 1727939 := bstep (se 1 (by rfl) ⟨1295954, by rfl⟩ : syracuseStep 1727939 = 2591909) B2591909
theorem B1531361 : Blo 1020604 1531361 := bstep (se 2 (by rfl) ⟨574260, by rfl⟩ : syracuseStep 1531361 = 1148521) B1148521
theorem B1531379 : Blo 1020604 1531379 := bstep (se 1 (by rfl) ⟨1148534, by rfl⟩ : syracuseStep 1531379 = 2297069) B2297069
theorem B1531409 : Blo 1020604 1531409 := bstep (se 2 (by rfl) ⟨574278, by rfl⟩ : syracuseStep 1531409 = 1148557) B1148557
theorem B1531427 : Blo 1020604 1531427 := bstep (se 1 (by rfl) ⟨1148570, by rfl⟩ : syracuseStep 1531427 = 2297141) B2297141
theorem B2907697 : Blo 1020604 2907697 := bstep (se 2 (by rfl) ⟨1090386, by rfl⟩ : syracuseStep 2907697 = 2180773) B2180773
theorem B1531457 : Blo 1020604 1531457 := bstep (se 2 (by rfl) ⟨574296, by rfl⟩ : syracuseStep 1531457 = 1148593) B1148593
theorem B1728067 : Blo 1020604 1728067 := bstep (se 1 (by rfl) ⟨1296050, by rfl⟩ : syracuseStep 1728067 = 2592101) B2592101
theorem B1531475 : Blo 1020604 1531475 := bstep (se 1 (by rfl) ⟨1148606, by rfl⟩ : syracuseStep 1531475 = 2297213) B2297213
theorem B1531505 : Blo 1020604 1531505 := bstep (se 2 (by rfl) ⟨574314, by rfl⟩ : syracuseStep 1531505 = 1148629) B1148629
theorem B1531523 : Blo 1020604 1531523 := bstep (se 1 (by rfl) ⟨1148642, by rfl⟩ : syracuseStep 1531523 = 2297285) B2297285
theorem B1531553 : Blo 1020604 1531553 := bstep (se 2 (by rfl) ⟨574332, by rfl⟩ : syracuseStep 1531553 = 1148665) B1148665
theorem B5824163 : Blo 1020604 5824163 := bstep (se 1 (by rfl) ⟨4368122, by rfl⟩ : syracuseStep 5824163 = 8736245) B8736245
theorem B1531571 : Blo 1020604 1531571 := bstep (se 1 (by rfl) ⟨1148678, by rfl⟩ : syracuseStep 1531571 = 2297357) B2297357
theorem B1531601 : Blo 1020604 1531601 := bstep (se 2 (by rfl) ⟨574350, by rfl⟩ : syracuseStep 1531601 = 1148701) B1148701
theorem B1728209 : Blo 1020604 1728209 := bstep (se 2 (by rfl) ⟨648078, by rfl⟩ : syracuseStep 1728209 = 1296157) B1296157
theorem B1531619 : Blo 1020604 1531619 := bstep (se 1 (by rfl) ⟨1148714, by rfl⟩ : syracuseStep 1531619 = 2297429) B2297429
theorem B2186993 : Blo 1020604 2186993 := bstep (se 2 (by rfl) ⟨820122, by rfl⟩ : syracuseStep 2186993 = 1640245) B1640245
theorem B1531649 : Blo 1020604 1531649 := bstep (se 2 (by rfl) ⟨574368, by rfl⟩ : syracuseStep 1531649 = 1148737) B1148737
theorem B1531667 : Blo 1020604 1531667 := bstep (se 1 (by rfl) ⟨1148750, by rfl⟩ : syracuseStep 1531667 = 2297501) B2297501
theorem B1531697 : Blo 1020604 1531697 := bstep (se 2 (by rfl) ⟨574386, by rfl⟩ : syracuseStep 1531697 = 1148773) B1148773
theorem B1531715 : Blo 1020604 1531715 := bstep (se 1 (by rfl) ⟨1148786, by rfl⟩ : syracuseStep 1531715 = 2297573) B2297573
theorem B2907971 : Blo 1020604 2907971 := bstep (se 1 (by rfl) ⟨2180978, by rfl⟩ : syracuseStep 2907971 = 4361957) B4361957
theorem B1728337 : Blo 1020604 1728337 := bstep (se 2 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 1728337 = 1296253) B1296253
theorem B1531745 : Blo 1020604 1531745 := bstep (se 2 (by rfl) ⟨574404, by rfl⟩ : syracuseStep 1531745 = 1148809) B1148809
theorem B1531763 : Blo 1020604 1531763 := bstep (se 1 (by rfl) ⟨1148822, by rfl⟩ : syracuseStep 1531763 = 2297645) B2297645
theorem B1728371 : Blo 1020604 1728371 := bstep (se 1 (by rfl) ⟨1296278, by rfl⟩ : syracuseStep 1728371 = 2592557) B2592557
theorem B1531793 : Blo 1020604 1531793 := bstep (se 2 (by rfl) ⟨574422, by rfl⟩ : syracuseStep 1531793 = 1148845) B1148845
theorem B1531811 : Blo 1020604 1531811 := bstep (se 1 (by rfl) ⟨1148858, by rfl⟩ : syracuseStep 1531811 = 2297717) B2297717
theorem B1531841 : Blo 1020604 1531841 := bstep (se 2 (by rfl) ⟨574440, by rfl⟩ : syracuseStep 1531841 = 1148881) B1148881
theorem B1531859 : Blo 1020604 1531859 := bstep (se 1 (by rfl) ⟨1148894, by rfl⟩ : syracuseStep 1531859 = 2297789) B2297789
theorem B1531889 : Blo 1020604 1531889 := bstep (se 2 (by rfl) ⟨574458, by rfl⟩ : syracuseStep 1531889 = 1148917) B1148917
theorem B1728499 : Blo 1020604 1728499 := bstep (se 1 (by rfl) ⟨1296374, by rfl⟩ : syracuseStep 1728499 = 2592749) B2592749
theorem B2908163 : Blo 1020604 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B1531907 : Blo 1020604 1531907 := bstep (se 1 (by rfl) ⟨1148930, by rfl⟩ : syracuseStep 1531907 = 2297861) B2297861
theorem B1531937 : Blo 1020604 1531937 := bstep (se 2 (by rfl) ⟨574476, by rfl⟩ : syracuseStep 1531937 = 1148953) B1148953
theorem B1531955 : Blo 1020604 1531955 := bstep (se 1 (by rfl) ⟨1148966, by rfl⟩ : syracuseStep 1531955 = 2297933) B2297933
theorem B1531985 : Blo 1020604 1531985 := bstep (se 2 (by rfl) ⟨574494, by rfl⟩ : syracuseStep 1531985 = 1148989) B1148989
theorem B1532003 : Blo 1020604 1532003 := bstep (se 1 (by rfl) ⟨1149002, by rfl⟩ : syracuseStep 1532003 = 2298005) B2298005
theorem B1532033 : Blo 1020604 1532033 := bstep (se 2 (by rfl) ⟨574512, by rfl⟩ : syracuseStep 1532033 = 1149025) B1149025
theorem B1728641 : Blo 1020604 1728641 := bstep (se 2 (by rfl) ⟨648240, by rfl⟩ : syracuseStep 1728641 = 1296481) B1296481
theorem B1532051 : Blo 1020604 1532051 := bstep (se 1 (by rfl) ⟨1149038, by rfl⟩ : syracuseStep 1532051 = 2298077) B2298077
theorem B1532081 : Blo 1020604 1532081 := bstep (se 2 (by rfl) ⟨574530, by rfl⟩ : syracuseStep 1532081 = 1149061) B1149061
theorem B1532099 : Blo 1020604 1532099 := bstep (se 1 (by rfl) ⟨1149074, by rfl⟩ : syracuseStep 1532099 = 2298149) B2298149
theorem B1532129 : Blo 1020604 1532129 := bstep (se 2 (by rfl) ⟨574548, by rfl⟩ : syracuseStep 1532129 = 1149097) B1149097
theorem B1532147 : Blo 1020604 1532147 := bstep (se 1 (by rfl) ⟨1149110, by rfl⟩ : syracuseStep 1532147 = 2298221) B2298221
theorem B1728769 : Blo 1020604 1728769 := bstep (se 2 (by rfl) ⟨648288, by rfl⟩ : syracuseStep 1728769 = 1296577) B1296577
theorem B1532177 : Blo 1020604 1532177 := bstep (se 2 (by rfl) ⟨574566, by rfl⟩ : syracuseStep 1532177 = 1149133) B1149133
theorem B1532195 : Blo 1020604 1532195 := bstep (se 1 (by rfl) ⟨1149146, by rfl⟩ : syracuseStep 1532195 = 2298293) B2298293
theorem B1728803 : Blo 1020604 1728803 := bstep (se 1 (by rfl) ⟨1296602, by rfl⟩ : syracuseStep 1728803 = 2593205) B2593205
theorem B1532225 : Blo 1020604 1532225 := bstep (se 2 (by rfl) ⟨574584, by rfl⟩ : syracuseStep 1532225 = 1149169) B1149169
theorem B1532243 : Blo 1020604 1532243 := bstep (se 1 (by rfl) ⟨1149182, by rfl⟩ : syracuseStep 1532243 = 2298365) B2298365
theorem B1532273 : Blo 1020604 1532273 := bstep (se 2 (by rfl) ⟨574602, by rfl⟩ : syracuseStep 1532273 = 1149205) B1149205
theorem B1532291 : Blo 1020604 1532291 := bstep (se 1 (by rfl) ⟨1149218, by rfl⟩ : syracuseStep 1532291 = 2298437) B2298437
theorem B1532321 : Blo 1020604 1532321 := bstep (se 2 (by rfl) ⟨574620, by rfl⟩ : syracuseStep 1532321 = 1149241) B1149241
theorem B1728931 : Blo 1020604 1728931 := bstep (se 1 (by rfl) ⟨1296698, by rfl⟩ : syracuseStep 1728931 = 2593397) B2593397
theorem B1532339 : Blo 1020604 1532339 := bstep (se 1 (by rfl) ⟨1149254, by rfl⟩ : syracuseStep 1532339 = 2298509) B2298509
theorem B1532369 : Blo 1020604 1532369 := bstep (se 2 (by rfl) ⟨574638, by rfl⟩ : syracuseStep 1532369 = 1149277) B1149277
theorem B1532387 : Blo 1020604 1532387 := bstep (se 1 (by rfl) ⟨1149290, by rfl⟩ : syracuseStep 1532387 = 2298581) B2298581
theorem B1532417 : Blo 1020604 1532417 := bstep (se 2 (by rfl) ⟨574656, by rfl⟩ : syracuseStep 1532417 = 1149313) B1149313
theorem B6545933 : Blo 1020604 6545933 := bstep (se 3 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 6545933 = 2454725) B2454725
theorem B1532435 : Blo 1020604 1532435 := bstep (se 1 (by rfl) ⟨1149326, by rfl⟩ : syracuseStep 1532435 = 2298653) B2298653
theorem B1532465 : Blo 1020604 1532465 := bstep (se 2 (by rfl) ⟨574674, by rfl⟩ : syracuseStep 1532465 = 1149349) B1149349
theorem B1532483 : Blo 1020604 1532483 := bstep (se 1 (by rfl) ⟨1149362, by rfl⟩ : syracuseStep 1532483 = 2298725) B2298725
theorem B1532513 : Blo 1020604 1532513 := bstep (se 2 (by rfl) ⟨574692, by rfl⟩ : syracuseStep 1532513 = 1149385) B1149385
theorem B1532531 : Blo 1020604 1532531 := bstep (se 1 (by rfl) ⟨1149398, by rfl⟩ : syracuseStep 1532531 = 2298797) B2298797
theorem B1532561 : Blo 1020604 1532561 := bstep (se 2 (by rfl) ⟨574710, by rfl⟩ : syracuseStep 1532561 = 1149421) B1149421
theorem B1532579 : Blo 1020604 1532579 := bstep (se 1 (by rfl) ⟨1149434, by rfl⟩ : syracuseStep 1532579 = 2298869) B2298869
theorem B1532609 : Blo 1020604 1532609 := bstep (se 2 (by rfl) ⟨574728, by rfl⟩ : syracuseStep 1532609 = 1149457) B1149457
theorem B1532627 : Blo 1020604 1532627 := bstep (se 1 (by rfl) ⟨1149470, by rfl⟩ : syracuseStep 1532627 = 2298941) B2298941
theorem B5169905 : Blo 1020604 5169905 := bstep (se 2 (by rfl) ⟨1938714, by rfl⟩ : syracuseStep 5169905 = 3877429) B3877429
theorem B1532657 : Blo 1020604 1532657 := bstep (se 2 (by rfl) ⟨574746, by rfl⟩ : syracuseStep 1532657 = 1149493) B1149493
theorem B1532675 : Blo 1020604 1532675 := bstep (se 1 (by rfl) ⟨1149506, by rfl⟩ : syracuseStep 1532675 = 2299013) B2299013
theorem B1532705 : Blo 1020604 1532705 := bstep (se 2 (by rfl) ⟨574764, by rfl⟩ : syracuseStep 1532705 = 1149529) B1149529
theorem B1106723 : Blo 1020604 1106723 := bstep (se 1 (by rfl) ⟨830042, by rfl⟩ : syracuseStep 1106723 = 1660085) B1660085
theorem B2908973 : Blo 1020604 2908973 := bstep (se 3 (by rfl) ⟨545432, by rfl⟩ : syracuseStep 2908973 = 1090865) B1090865
theorem B1532723 : Blo 1020604 1532723 := bstep (se 1 (by rfl) ⟨1149542, by rfl⟩ : syracuseStep 1532723 = 2299085) B2299085
theorem B1532753 : Blo 1020604 1532753 := bstep (se 2 (by rfl) ⟨574782, by rfl⟩ : syracuseStep 1532753 = 1149565) B1149565
theorem B1532771 : Blo 1020604 1532771 := bstep (se 1 (by rfl) ⟨1149578, by rfl⟩ : syracuseStep 1532771 = 2299157) B2299157
theorem B1532801 : Blo 1020604 1532801 := bstep (se 2 (by rfl) ⟨574800, by rfl⟩ : syracuseStep 1532801 = 1149601) B1149601
theorem B3367811 : Blo 1020604 3367811 := bstep (se 1 (by rfl) ⟨2525858, by rfl⟩ : syracuseStep 3367811 = 5051717) B5051717
theorem B1532819 : Blo 1020604 1532819 := bstep (se 1 (by rfl) ⟨1149614, by rfl⟩ : syracuseStep 1532819 = 2299229) B2299229
theorem B1532849 : Blo 1020604 1532849 := bstep (se 2 (by rfl) ⟨574818, by rfl⟩ : syracuseStep 1532849 = 1149637) B1149637
theorem B1532867 : Blo 1020604 1532867 := bstep (se 1 (by rfl) ⟨1149650, by rfl⟩ : syracuseStep 1532867 = 2299301) B2299301
theorem B1532897 : Blo 1020604 1532897 := bstep (se 2 (by rfl) ⟨574836, by rfl⟩ : syracuseStep 1532897 = 1149673) B1149673
theorem B2909155 : Blo 1020604 2909155 := bstep (se 1 (by rfl) ⟨2181866, by rfl⟩ : syracuseStep 2909155 = 4363733) B4363733
theorem B1532915 : Blo 1020604 1532915 := bstep (se 1 (by rfl) ⟨1149686, by rfl⟩ : syracuseStep 1532915 = 2299373) B2299373
theorem B2188291 : Blo 1020604 2188291 := bstep (se 1 (by rfl) ⟨1641218, by rfl⟩ : syracuseStep 2188291 = 3282437) B3282437
theorem B1532945 : Blo 1020604 1532945 := bstep (se 2 (by rfl) ⟨574854, by rfl⟩ : syracuseStep 1532945 = 1149709) B1149709
theorem B1532963 : Blo 1020604 1532963 := bstep (se 1 (by rfl) ⟨1149722, by rfl⟩ : syracuseStep 1532963 = 2299445) B2299445
theorem B1532993 : Blo 1020604 1532993 := bstep (se 2 (by rfl) ⟨574872, by rfl⟩ : syracuseStep 1532993 = 1149745) B1149745
theorem B1533011 : Blo 1020604 1533011 := bstep (se 1 (by rfl) ⟨1149758, by rfl⟩ : syracuseStep 1533011 = 2299517) B2299517
theorem B1533041 : Blo 1020604 1533041 := bstep (se 2 (by rfl) ⟨574890, by rfl⟩ : syracuseStep 1533041 = 1149781) B1149781
theorem B1533059 : Blo 1020604 1533059 := bstep (se 1 (by rfl) ⟨1149794, by rfl⟩ : syracuseStep 1533059 = 2299589) B2299589
theorem B7758989 : Blo 1020604 7758989 := bstep (se 3 (by rfl) ⟨1454810, by rfl⟩ : syracuseStep 7758989 = 2909621) B2909621
theorem B1533089 : Blo 1020604 1533089 := bstep (se 2 (by rfl) ⟨574908, by rfl⟩ : syracuseStep 1533089 = 1149817) B1149817
theorem B1533107 : Blo 1020604 1533107 := bstep (se 1 (by rfl) ⟨1149830, by rfl⟩ : syracuseStep 1533107 = 2299661) B2299661
theorem B1533137 : Blo 1020604 1533137 := bstep (se 2 (by rfl) ⟨574926, by rfl⟩ : syracuseStep 1533137 = 1149853) B1149853
theorem B1533155 : Blo 1020604 1533155 := bstep (se 1 (by rfl) ⟨1149866, by rfl⟩ : syracuseStep 1533155 = 2299733) B2299733
theorem B1533185 : Blo 1020604 1533185 := bstep (se 2 (by rfl) ⟨574944, by rfl⟩ : syracuseStep 1533185 = 1149889) B1149889
theorem B1533203 : Blo 1020604 1533203 := bstep (se 1 (by rfl) ⟨1149902, by rfl⟩ : syracuseStep 1533203 = 2299805) B2299805
theorem B1533233 : Blo 1020604 1533233 := bstep (se 2 (by rfl) ⟨574962, by rfl⟩ : syracuseStep 1533233 = 1149925) B1149925
theorem B1533251 : Blo 1020604 1533251 := bstep (se 1 (by rfl) ⟨1149938, by rfl⟩ : syracuseStep 1533251 = 2299877) B2299877
theorem B1533281 : Blo 1020604 1533281 := bstep (se 2 (by rfl) ⟨574980, by rfl⟩ : syracuseStep 1533281 = 1149961) B1149961
theorem B1533299 : Blo 1020604 1533299 := bstep (se 1 (by rfl) ⟨1149974, by rfl⟩ : syracuseStep 1533299 = 2299949) B2299949
theorem B1533329 : Blo 1020604 1533329 := bstep (se 2 (by rfl) ⟨574998, by rfl⟩ : syracuseStep 1533329 = 1149997) B1149997
theorem B1533347 : Blo 1020604 1533347 := bstep (se 1 (by rfl) ⟨1150010, by rfl⟩ : syracuseStep 1533347 = 2300021) B2300021
theorem B1533377 : Blo 1020604 1533377 := bstep (se 2 (by rfl) ⟨575016, by rfl⟩ : syracuseStep 1533377 = 1150033) B1150033
theorem B2909645 : Blo 1020604 2909645 := bstep (se 3 (by rfl) ⟨545558, by rfl⟩ : syracuseStep 2909645 = 1091117) B1091117
theorem B1533395 : Blo 1020604 1533395 := bstep (se 1 (by rfl) ⟨1150046, by rfl⟩ : syracuseStep 1533395 = 2300093) B2300093
theorem B1533425 : Blo 1020604 1533425 := bstep (se 2 (by rfl) ⟨575034, by rfl⟩ : syracuseStep 1533425 = 1150069) B1150069
theorem B1533443 : Blo 1020604 1533443 := bstep (se 1 (by rfl) ⟨1150082, by rfl⟩ : syracuseStep 1533443 = 2300165) B2300165
theorem B1533473 : Blo 1020604 1533473 := bstep (se 2 (by rfl) ⟨575052, by rfl⟩ : syracuseStep 1533473 = 1150105) B1150105
theorem B1533491 : Blo 1020604 1533491 := bstep (se 1 (by rfl) ⟨1150118, by rfl⟩ : syracuseStep 1533491 = 2300237) B2300237
theorem B1533521 : Blo 1020604 1533521 := bstep (se 2 (by rfl) ⟨575070, by rfl⟩ : syracuseStep 1533521 = 1150141) B1150141
theorem B1533539 : Blo 1020604 1533539 := bstep (se 1 (by rfl) ⟨1150154, by rfl⟩ : syracuseStep 1533539 = 2300309) B2300309
theorem B1533569 : Blo 1020604 1533569 := bstep (se 2 (by rfl) ⟨575088, by rfl⟩ : syracuseStep 1533569 = 1150177) B1150177
theorem B1533587 : Blo 1020604 1533587 := bstep (se 1 (by rfl) ⟨1150190, by rfl⟩ : syracuseStep 1533587 = 2300381) B2300381
theorem B1533617 : Blo 1020604 1533617 := bstep (se 2 (by rfl) ⟨575106, by rfl⟩ : syracuseStep 1533617 = 1150213) B1150213
theorem B1533635 : Blo 1020604 1533635 := bstep (se 1 (by rfl) ⟨1150226, by rfl⟩ : syracuseStep 1533635 = 2300453) B2300453
theorem B1533665 : Blo 1020604 1533665 := bstep (se 2 (by rfl) ⟨575124, by rfl⟩ : syracuseStep 1533665 = 1150249) B1150249
theorem B1533683 : Blo 1020604 1533683 := bstep (se 1 (by rfl) ⟨1150262, by rfl⟩ : syracuseStep 1533683 = 2300525) B2300525
theorem B1533713 : Blo 1020604 1533713 := bstep (se 2 (by rfl) ⟨575142, by rfl⟩ : syracuseStep 1533713 = 1150285) B1150285
theorem B1533731 : Blo 1020604 1533731 := bstep (se 1 (by rfl) ⟨1150298, by rfl⟩ : syracuseStep 1533731 = 2300597) B2300597
theorem B1533761 : Blo 1020604 1533761 := bstep (se 2 (by rfl) ⟨575160, by rfl⟩ : syracuseStep 1533761 = 1150321) B1150321
theorem B1533779 : Blo 1020604 1533779 := bstep (se 1 (by rfl) ⟨1150334, by rfl⟩ : syracuseStep 1533779 = 2300669) B2300669
theorem B1533809 : Blo 1020604 1533809 := bstep (se 2 (by rfl) ⟨575178, by rfl⟩ : syracuseStep 1533809 = 1150357) B1150357
theorem B1533827 : Blo 1020604 1533827 := bstep (se 1 (by rfl) ⟨1150370, by rfl⟩ : syracuseStep 1533827 = 2300741) B2300741
theorem B8284045 : Blo 1020604 8284045 := bstep (se 3 (by rfl) ⟨1553258, by rfl⟩ : syracuseStep 8284045 = 3106517) B3106517
theorem B1533857 : Blo 1020604 1533857 := bstep (se 2 (by rfl) ⟨575196, by rfl⟩ : syracuseStep 1533857 = 1150393) B1150393
theorem B1533875 : Blo 1020604 1533875 := bstep (se 1 (by rfl) ⟨1150406, by rfl⟩ : syracuseStep 1533875 = 2300813) B2300813
theorem B1533905 : Blo 1020604 1533905 := bstep (se 2 (by rfl) ⟨575214, by rfl⟩ : syracuseStep 1533905 = 1150429) B1150429
theorem B1533923 : Blo 1020604 1533923 := bstep (se 1 (by rfl) ⟨1150442, by rfl⟩ : syracuseStep 1533923 = 2300885) B2300885
theorem B1533953 : Blo 1020604 1533953 := bstep (se 2 (by rfl) ⟨575232, by rfl⟩ : syracuseStep 1533953 = 1150465) B1150465
theorem B1533971 : Blo 1020604 1533971 := bstep (se 1 (by rfl) ⟨1150478, by rfl⟩ : syracuseStep 1533971 = 2300957) B2300957
theorem B3237937 : Blo 1020604 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B1534001 : Blo 1020604 1534001 := bstep (se 2 (by rfl) ⟨575250, by rfl⟩ : syracuseStep 1534001 = 1150501) B1150501
theorem B1534019 : Blo 1020604 1534019 := bstep (se 1 (by rfl) ⟨1150514, by rfl⟩ : syracuseStep 1534019 = 2301029) B2301029
theorem B1534049 : Blo 1020604 1534049 := bstep (se 2 (by rfl) ⟨575268, by rfl⟩ : syracuseStep 1534049 = 1150537) B1150537
theorem B1534067 : Blo 1020604 1534067 := bstep (se 1 (by rfl) ⟨1150550, by rfl⟩ : syracuseStep 1534067 = 2301101) B2301101
theorem B1534097 : Blo 1020604 1534097 := bstep (se 2 (by rfl) ⟨575286, by rfl⟩ : syracuseStep 1534097 = 1150573) B1150573
theorem B5171363 : Blo 1020604 5171363 := bstep (se 1 (by rfl) ⟨3878522, by rfl⟩ : syracuseStep 5171363 = 7757045) B7757045
theorem B1534115 : Blo 1020604 1534115 := bstep (se 1 (by rfl) ⟨1150586, by rfl⟩ : syracuseStep 1534115 = 2301173) B2301173
theorem B1534145 : Blo 1020604 1534145 := bstep (se 2 (by rfl) ⟨575304, by rfl⟩ : syracuseStep 1534145 = 1150609) B1150609
theorem B1534163 : Blo 1020604 1534163 := bstep (se 1 (by rfl) ⟨1150622, by rfl⟩ : syracuseStep 1534163 = 2301245) B2301245
theorem B1534193 : Blo 1020604 1534193 := bstep (se 2 (by rfl) ⟨575322, by rfl⟩ : syracuseStep 1534193 = 1150645) B1150645
theorem B1534211 : Blo 1020604 1534211 := bstep (se 1 (by rfl) ⟨1150658, by rfl⟩ : syracuseStep 1534211 = 2301317) B2301317
theorem B1534241 : Blo 1020604 1534241 := bstep (se 2 (by rfl) ⟨575340, by rfl⟩ : syracuseStep 1534241 = 1150681) B1150681
theorem B1534259 : Blo 1020604 1534259 := bstep (se 1 (by rfl) ⟨1150694, by rfl⟩ : syracuseStep 1534259 = 2301389) B2301389
theorem B1534289 : Blo 1020604 1534289 := bstep (se 2 (by rfl) ⟨575358, by rfl⟩ : syracuseStep 1534289 = 1150717) B1150717
theorem B1534307 : Blo 1020604 1534307 := bstep (se 1 (by rfl) ⟨1150730, by rfl⟩ : syracuseStep 1534307 = 2301461) B2301461
theorem B1534337 : Blo 1020604 1534337 := bstep (se 2 (by rfl) ⟨575376, by rfl⟩ : syracuseStep 1534337 = 1150753) B1150753
theorem B1534355 : Blo 1020604 1534355 := bstep (se 1 (by rfl) ⟨1150766, by rfl⟩ : syracuseStep 1534355 = 2301533) B2301533
theorem B3107249 : Blo 1020604 3107249 := bstep (se 2 (by rfl) ⟨1165218, by rfl⟩ : syracuseStep 3107249 = 2330437) B2330437
theorem B1534385 : Blo 1020604 1534385 := bstep (se 2 (by rfl) ⟨575394, by rfl⟩ : syracuseStep 1534385 = 1150789) B1150789
theorem B1534403 : Blo 1020604 1534403 := bstep (se 1 (by rfl) ⟨1150802, by rfl⟩ : syracuseStep 1534403 = 2301605) B2301605
theorem B1534433 : Blo 1020604 1534433 := bstep (se 2 (by rfl) ⟨575412, by rfl⟩ : syracuseStep 1534433 = 1150825) B1150825
theorem B3500525 : Blo 1020604 3500525 := bstep (se 3 (by rfl) ⟨656348, by rfl⟩ : syracuseStep 3500525 = 1312697) B1312697
theorem B1534451 : Blo 1020604 1534451 := bstep (se 1 (by rfl) ⟨1150838, by rfl⟩ : syracuseStep 1534451 = 2301677) B2301677
theorem B1534481 : Blo 1020604 1534481 := bstep (se 2 (by rfl) ⟨575430, by rfl⟩ : syracuseStep 1534481 = 1150861) B1150861
theorem B1534499 : Blo 1020604 1534499 := bstep (se 1 (by rfl) ⟨1150874, by rfl⟩ : syracuseStep 1534499 = 2301749) B2301749
theorem B1534529 : Blo 1020604 1534529 := bstep (se 2 (by rfl) ⟨575448, by rfl⟩ : syracuseStep 1534529 = 1150897) B1150897
theorem B1534547 : Blo 1020604 1534547 := bstep (se 1 (by rfl) ⟨1150910, by rfl⟩ : syracuseStep 1534547 = 2301821) B2301821
theorem B2910829 : Blo 1020604 2910829 := bstep (se 3 (by rfl) ⟨545780, by rfl⟩ : syracuseStep 2910829 = 1091561) B1091561
theorem B1534577 : Blo 1020604 1534577 := bstep (se 2 (by rfl) ⟨575466, by rfl⟩ : syracuseStep 1534577 = 1150933) B1150933
theorem B1534595 : Blo 1020604 1534595 := bstep (se 1 (by rfl) ⟨1150946, by rfl⟩ : syracuseStep 1534595 = 2301893) B2301893
theorem B1534625 : Blo 1020604 1534625 := bstep (se 2 (by rfl) ⟨575484, by rfl⟩ : syracuseStep 1534625 = 1150969) B1150969
theorem B1534643 : Blo 1020604 1534643 := bstep (se 1 (by rfl) ⟨1150982, by rfl⟩ : syracuseStep 1534643 = 2301965) B2301965
theorem B1534673 : Blo 1020604 1534673 := bstep (se 2 (by rfl) ⟨575502, by rfl⟩ : syracuseStep 1534673 = 1151005) B1151005
theorem B1534691 : Blo 1020604 1534691 := bstep (se 1 (by rfl) ⟨1151018, by rfl⟩ : syracuseStep 1534691 = 2302037) B2302037
theorem B1534721 : Blo 1020604 1534721 := bstep (se 2 (by rfl) ⟨575520, by rfl⟩ : syracuseStep 1534721 = 1151041) B1151041
theorem B1534739 : Blo 1020604 1534739 := bstep (se 1 (by rfl) ⟨1151054, by rfl⟩ : syracuseStep 1534739 = 2302109) B2302109
theorem B1534769 : Blo 1020604 1534769 := bstep (se 2 (by rfl) ⟨575538, by rfl⟩ : syracuseStep 1534769 = 1151077) B1151077
theorem B1534787 : Blo 1020604 1534787 := bstep (se 1 (by rfl) ⟨1151090, by rfl⟩ : syracuseStep 1534787 = 2302181) B2302181
theorem B1534817 : Blo 1020604 1534817 := bstep (se 2 (by rfl) ⟨575556, by rfl⟩ : syracuseStep 1534817 = 1151113) B1151113
theorem B1534835 : Blo 1020604 1534835 := bstep (se 1 (by rfl) ⟨1151126, by rfl⟩ : syracuseStep 1534835 = 2302253) B2302253
theorem B1534865 : Blo 1020604 1534865 := bstep (se 2 (by rfl) ⟨575574, by rfl⟩ : syracuseStep 1534865 = 1151149) B1151149
theorem B1534883 : Blo 1020604 1534883 := bstep (se 1 (by rfl) ⟨1151162, by rfl⟩ : syracuseStep 1534883 = 2302325) B2302325
theorem B1534913 : Blo 1020604 1534913 := bstep (se 2 (by rfl) ⟨575592, by rfl⟩ : syracuseStep 1534913 = 1151185) B1151185
theorem B5172173 : Blo 1020604 5172173 := bstep (se 3 (by rfl) ⟨969782, by rfl⟩ : syracuseStep 5172173 = 1939565) B1939565
theorem B1534931 : Blo 1020604 1534931 := bstep (se 1 (by rfl) ⟨1151198, by rfl⟩ : syracuseStep 1534931 = 2302397) B2302397
theorem B1534961 : Blo 1020604 1534961 := bstep (se 2 (by rfl) ⟨575610, by rfl⟩ : syracuseStep 1534961 = 1151221) B1151221
theorem B1534979 : Blo 1020604 1534979 := bstep (se 1 (by rfl) ⟨1151234, by rfl⟩ : syracuseStep 1534979 = 2302469) B2302469
theorem B1535009 : Blo 1020604 1535009 := bstep (se 2 (by rfl) ⟨575628, by rfl⟩ : syracuseStep 1535009 = 1151257) B1151257
theorem B1535027 : Blo 1020604 1535027 := bstep (se 1 (by rfl) ⟨1151270, by rfl⟩ : syracuseStep 1535027 = 2302541) B2302541
theorem B1535057 : Blo 1020604 1535057 := bstep (se 2 (by rfl) ⟨575646, by rfl⟩ : syracuseStep 1535057 = 1151293) B1151293
theorem B1535075 : Blo 1020604 1535075 := bstep (se 1 (by rfl) ⟨1151306, by rfl⟩ : syracuseStep 1535075 = 2302613) B2302613
theorem B1535105 : Blo 1020604 1535105 := bstep (se 2 (by rfl) ⟨575664, by rfl⟩ : syracuseStep 1535105 = 1151329) B1151329
theorem B2583697 : Blo 1020604 2583697 := bstep (se 2 (by rfl) ⟨968886, by rfl⟩ : syracuseStep 2583697 = 1937773) B1937773
theorem B1535123 : Blo 1020604 1535123 := bstep (se 1 (by rfl) ⟨1151342, by rfl⟩ : syracuseStep 1535123 = 2302685) B2302685
theorem B1535153 : Blo 1020604 1535153 := bstep (se 2 (by rfl) ⟨575682, by rfl⟩ : syracuseStep 1535153 = 1151365) B1151365
theorem B1535171 : Blo 1020604 1535171 := bstep (se 1 (by rfl) ⟨1151378, by rfl⟩ : syracuseStep 1535171 = 2302757) B2302757
theorem B3271889 : Blo 1020604 3271889 := bstep (se 2 (by rfl) ⟨1226958, by rfl⟩ : syracuseStep 3271889 = 2453917) B2453917
theorem B1535201 : Blo 1020604 1535201 := bstep (se 2 (by rfl) ⟨575700, by rfl⟩ : syracuseStep 1535201 = 1151401) B1151401
theorem B1535219 : Blo 1020604 1535219 := bstep (se 1 (by rfl) ⟨1151414, by rfl⟩ : syracuseStep 1535219 = 2302829) B2302829
theorem B1535249 : Blo 1020604 1535249 := bstep (se 2 (by rfl) ⟨575718, by rfl⟩ : syracuseStep 1535249 = 1151437) B1151437
theorem B1535267 : Blo 1020604 1535267 := bstep (se 1 (by rfl) ⟨1151450, by rfl⟩ : syracuseStep 1535267 = 2302901) B2302901
theorem B26602805 : Blo 1020604 26602805 := bstep (se 5 (by rfl) ⟨1247006, by rfl⟩ : syracuseStep 26602805 = 2494013) B2494013
theorem B1535297 : Blo 1020604 1535297 := bstep (se 2 (by rfl) ⟨575736, by rfl⟩ : syracuseStep 1535297 = 1151473) B1151473
theorem B1535315 : Blo 1020604 1535315 := bstep (se 1 (by rfl) ⟨1151486, by rfl⟩ : syracuseStep 1535315 = 2302973) B2302973
theorem B1535345 : Blo 1020604 1535345 := bstep (se 2 (by rfl) ⟨575754, by rfl⟩ : syracuseStep 1535345 = 1151509) B1151509
theorem B1535363 : Blo 1020604 1535363 := bstep (se 1 (by rfl) ⟨1151522, by rfl⟩ : syracuseStep 1535363 = 2303045) B2303045
theorem B1535393 : Blo 1020604 1535393 := bstep (se 2 (by rfl) ⟨575772, by rfl⟩ : syracuseStep 1535393 = 1151545) B1151545
theorem B2583971 : Blo 1020604 2583971 := bstep (se 1 (by rfl) ⟨1937978, by rfl⟩ : syracuseStep 2583971 = 3875957) B3875957
theorem B1535411 : Blo 1020604 1535411 := bstep (se 1 (by rfl) ⟨1151558, by rfl⟩ : syracuseStep 1535411 = 2303117) B2303117
theorem B1535441 : Blo 1020604 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B1535459 : Blo 1020604 1535459 := bstep (se 1 (by rfl) ⟨1151594, by rfl⟩ : syracuseStep 1535459 = 2303189) B2303189
theorem B1535489 : Blo 1020604 1535489 := bstep (se 2 (by rfl) ⟨575808, by rfl⟩ : syracuseStep 1535489 = 1151617) B1151617
theorem B1535507 : Blo 1020604 1535507 := bstep (se 1 (by rfl) ⟨1151630, by rfl⟩ : syracuseStep 1535507 = 2303261) B2303261
theorem B1535537 : Blo 1020604 1535537 := bstep (se 2 (by rfl) ⟨575826, by rfl⟩ : syracuseStep 1535537 = 1151653) B1151653
theorem B1535555 : Blo 1020604 1535555 := bstep (se 1 (by rfl) ⟨1151666, by rfl⟩ : syracuseStep 1535555 = 2303333) B2303333
theorem B1535585 : Blo 1020604 1535585 := bstep (se 2 (by rfl) ⟨575844, by rfl⟩ : syracuseStep 1535585 = 1151689) B1151689
theorem B2584163 : Blo 1020604 2584163 := bstep (se 1 (by rfl) ⟨1938122, by rfl⟩ : syracuseStep 2584163 = 3876245) B3876245
theorem B1535603 : Blo 1020604 1535603 := bstep (se 1 (by rfl) ⟨1151702, by rfl⟩ : syracuseStep 1535603 = 2303405) B2303405
theorem B2911889 : Blo 1020604 2911889 := bstep (se 2 (by rfl) ⟨1091958, by rfl⟩ : syracuseStep 2911889 = 2183917) B2183917
theorem B1535633 : Blo 1020604 1535633 := bstep (se 2 (by rfl) ⟨575862, by rfl⟩ : syracuseStep 1535633 = 1151725) B1151725
theorem B1535651 : Blo 1020604 1535651 := bstep (se 1 (by rfl) ⟨1151738, by rfl⟩ : syracuseStep 1535651 = 2303477) B2303477
theorem B1535681 : Blo 1020604 1535681 := bstep (se 2 (by rfl) ⟨575880, by rfl⟩ : syracuseStep 1535681 = 1151761) B1151761
theorem B1535699 : Blo 1020604 1535699 := bstep (se 1 (by rfl) ⟨1151774, by rfl⟩ : syracuseStep 1535699 = 2303549) B2303549
theorem B1535729 : Blo 1020604 1535729 := bstep (se 2 (by rfl) ⟨575898, by rfl⟩ : syracuseStep 1535729 = 1151797) B1151797
theorem B1535747 : Blo 1020604 1535747 := bstep (se 1 (by rfl) ⟨1151810, by rfl⟩ : syracuseStep 1535747 = 2303621) B2303621
theorem B3731213 : Blo 1020604 3731213 := bstep (se 3 (by rfl) ⟨699602, by rfl⟩ : syracuseStep 3731213 = 1399205) B1399205
theorem B1535777 : Blo 1020604 1535777 := bstep (se 2 (by rfl) ⟨575916, by rfl⟩ : syracuseStep 1535777 = 1151833) B1151833
theorem B1535795 : Blo 1020604 1535795 := bstep (se 1 (by rfl) ⟨1151846, by rfl⟩ : syracuseStep 1535795 = 2303693) B2303693
theorem B1535825 : Blo 1020604 1535825 := bstep (se 2 (by rfl) ⟨575934, by rfl⟩ : syracuseStep 1535825 = 1151869) B1151869
theorem B1535843 : Blo 1020604 1535843 := bstep (se 1 (by rfl) ⟨1151882, by rfl⟩ : syracuseStep 1535843 = 2303765) B2303765
theorem B1535873 : Blo 1020604 1535873 := bstep (se 2 (by rfl) ⟨575952, by rfl⟩ : syracuseStep 1535873 = 1151905) B1151905
theorem B1535891 : Blo 1020604 1535891 := bstep (se 1 (by rfl) ⟨1151918, by rfl⟩ : syracuseStep 1535891 = 2303837) B2303837
theorem B1535921 : Blo 1020604 1535921 := bstep (se 2 (by rfl) ⟨575970, by rfl⟩ : syracuseStep 1535921 = 1151941) B1151941
theorem B1535939 : Blo 1020604 1535939 := bstep (se 1 (by rfl) ⟨1151954, by rfl⟩ : syracuseStep 1535939 = 2303909) B2303909
theorem B1535969 : Blo 1020604 1535969 := bstep (se 2 (by rfl) ⟨575988, by rfl⟩ : syracuseStep 1535969 = 1151977) B1151977
theorem B3502061 : Blo 1020604 3502061 := bstep (se 3 (by rfl) ⟨656636, by rfl⟩ : syracuseStep 3502061 = 1313273) B1313273
theorem B7761905 : Blo 1020604 7761905 := bstep (se 2 (by rfl) ⟨2910714, by rfl⟩ : syracuseStep 7761905 = 5821429) B5821429
theorem B1535987 : Blo 1020604 1535987 := bstep (se 1 (by rfl) ⟨1151990, by rfl⟩ : syracuseStep 1535987 = 2303981) B2303981
theorem B1536017 : Blo 1020604 1536017 := bstep (se 2 (by rfl) ⟨576006, by rfl⟩ : syracuseStep 1536017 = 1152013) B1152013
theorem B1536035 : Blo 1020604 1536035 := bstep (se 1 (by rfl) ⟨1152026, by rfl⟩ : syracuseStep 1536035 = 2304053) B2304053
theorem B1536065 : Blo 1020604 1536065 := bstep (se 2 (by rfl) ⟨576024, by rfl⟩ : syracuseStep 1536065 = 1152049) B1152049
theorem B1536083 : Blo 1020604 1536083 := bstep (se 1 (by rfl) ⟨1152062, by rfl⟩ : syracuseStep 1536083 = 2304125) B2304125
theorem B3928177 : Blo 1020604 3928177 := bstep (se 2 (by rfl) ⟨1473066, by rfl⟩ : syracuseStep 3928177 = 2946133) B2946133
theorem B1536113 : Blo 1020604 1536113 := bstep (se 2 (by rfl) ⟨576042, by rfl⟩ : syracuseStep 1536113 = 1152085) B1152085
theorem B1536131 : Blo 1020604 1536131 := bstep (se 1 (by rfl) ⟨1152098, by rfl⟩ : syracuseStep 1536131 = 2304197) B2304197
theorem B3371153 : Blo 1020604 3371153 := bstep (se 2 (by rfl) ⟨1264182, by rfl⟩ : syracuseStep 3371153 = 2528365) B2528365
theorem B1536161 : Blo 1020604 1536161 := bstep (se 2 (by rfl) ⟨576060, by rfl⟩ : syracuseStep 1536161 = 1152121) B1152121
theorem B1536179 : Blo 1020604 1536179 := bstep (se 1 (by rfl) ⟨1152134, by rfl⟩ : syracuseStep 1536179 = 2304269) B2304269
theorem B1536209 : Blo 1020604 1536209 := bstep (se 2 (by rfl) ⟨576078, by rfl⟩ : syracuseStep 1536209 = 1152157) B1152157
theorem B1536227 : Blo 1020604 1536227 := bstep (se 1 (by rfl) ⟨1152170, by rfl⟩ : syracuseStep 1536227 = 2304341) B2304341
theorem B1536257 : Blo 1020604 1536257 := bstep (se 2 (by rfl) ⟨576096, by rfl⟩ : syracuseStep 1536257 = 1152193) B1152193
theorem B1536275 : Blo 1020604 1536275 := bstep (se 1 (by rfl) ⟨1152206, by rfl⟩ : syracuseStep 1536275 = 2304413) B2304413
theorem B2912561 : Blo 1020604 2912561 := bstep (se 2 (by rfl) ⟨1092210, by rfl⟩ : syracuseStep 2912561 = 2184421) B2184421
theorem B1536305 : Blo 1020604 1536305 := bstep (se 2 (by rfl) ⟨576114, by rfl⟩ : syracuseStep 1536305 = 1152229) B1152229
theorem B1536323 : Blo 1020604 1536323 := bstep (se 1 (by rfl) ⟨1152242, by rfl⟩ : syracuseStep 1536323 = 2304485) B2304485
theorem B1536353 : Blo 1020604 1536353 := bstep (se 2 (by rfl) ⟨576132, by rfl⟩ : syracuseStep 1536353 = 1152265) B1152265
theorem B1536371 : Blo 1020604 1536371 := bstep (se 1 (by rfl) ⟨1152278, by rfl⟩ : syracuseStep 1536371 = 2304557) B2304557
theorem B1536401 : Blo 1020604 1536401 := bstep (se 2 (by rfl) ⟨576150, by rfl⟩ : syracuseStep 1536401 = 1152301) B1152301
theorem B1536419 : Blo 1020604 1536419 := bstep (se 1 (by rfl) ⟨1152314, by rfl⟩ : syracuseStep 1536419 = 2304629) B2304629
theorem B1536449 : Blo 1020604 1536449 := bstep (se 2 (by rfl) ⟨576168, by rfl⟩ : syracuseStep 1536449 = 1152337) B1152337
theorem B1536467 : Blo 1020604 1536467 := bstep (se 1 (by rfl) ⟨1152350, by rfl⟩ : syracuseStep 1536467 = 2304701) B2304701
theorem B1536497 : Blo 1020604 1536497 := bstep (se 2 (by rfl) ⟨576186, by rfl⟩ : syracuseStep 1536497 = 1152373) B1152373
theorem B3502595 : Blo 1020604 3502595 := bstep (se 1 (by rfl) ⟨2626946, by rfl⟩ : syracuseStep 3502595 = 5253893) B5253893
theorem B1536515 : Blo 1020604 1536515 := bstep (se 1 (by rfl) ⟨1152386, by rfl⟩ : syracuseStep 1536515 = 2304773) B2304773
theorem B2585105 : Blo 1020604 2585105 := bstep (se 2 (by rfl) ⟨969414, by rfl⟩ : syracuseStep 2585105 = 1938829) B1938829
theorem B1536545 : Blo 1020604 1536545 := bstep (se 2 (by rfl) ⟨576204, by rfl⟩ : syracuseStep 1536545 = 1152409) B1152409
theorem B1536563 : Blo 1020604 1536563 := bstep (se 1 (by rfl) ⟨1152422, by rfl⟩ : syracuseStep 1536563 = 2304845) B2304845
theorem B2585155 : Blo 1020604 2585155 := bstep (se 1 (by rfl) ⟨1938866, by rfl⟩ : syracuseStep 2585155 = 3877733) B3877733
theorem B1536593 : Blo 1020604 1536593 := bstep (se 2 (by rfl) ⟨576222, by rfl⟩ : syracuseStep 1536593 = 1152445) B1152445
theorem B1536611 : Blo 1020604 1536611 := bstep (se 1 (by rfl) ⟨1152458, by rfl⟩ : syracuseStep 1536611 = 2304917) B2304917
theorem B1536641 : Blo 1020604 1536641 := bstep (se 2 (by rfl) ⟨576240, by rfl⟩ : syracuseStep 1536641 = 1152481) B1152481
theorem B1536659 : Blo 1020604 1536659 := bstep (se 1 (by rfl) ⟨1152494, by rfl⟩ : syracuseStep 1536659 = 2304989) B2304989
theorem B1536689 : Blo 1020604 1536689 := bstep (se 2 (by rfl) ⟨576258, by rfl⟩ : syracuseStep 1536689 = 1152517) B1152517
theorem B1536707 : Blo 1020604 1536707 := bstep (se 1 (by rfl) ⟨1152530, by rfl⟩ : syracuseStep 1536707 = 2305061) B2305061
theorem B2585297 : Blo 1020604 2585297 := bstep (se 2 (by rfl) ⟨969486, by rfl⟩ : syracuseStep 2585297 = 1938973) B1938973
theorem B1536737 : Blo 1020604 1536737 := bstep (se 2 (by rfl) ⟨576276, by rfl⟩ : syracuseStep 1536737 = 1152553) B1152553
theorem B1536755 : Blo 1020604 1536755 := bstep (se 1 (by rfl) ⟨1152566, by rfl⟩ : syracuseStep 1536755 = 2305133) B2305133
theorem B1536785 : Blo 1020604 1536785 := bstep (se 2 (by rfl) ⟨576294, by rfl⟩ : syracuseStep 1536785 = 1152589) B1152589
theorem B1536803 : Blo 1020604 1536803 := bstep (se 1 (by rfl) ⟨1152602, by rfl⟩ : syracuseStep 1536803 = 2305205) B2305205
theorem B1536833 : Blo 1020604 1536833 := bstep (se 2 (by rfl) ⟨576312, by rfl⟩ : syracuseStep 1536833 = 1152625) B1152625
theorem B1536851 : Blo 1020604 1536851 := bstep (se 1 (by rfl) ⟨1152638, by rfl⟩ : syracuseStep 1536851 = 2305277) B2305277
theorem B1536881 : Blo 1020604 1536881 := bstep (se 2 (by rfl) ⟨576330, by rfl⟩ : syracuseStep 1536881 = 1152661) B1152661
theorem B1536899 : Blo 1020604 1536899 := bstep (se 1 (by rfl) ⟨1152674, by rfl⟩ : syracuseStep 1536899 = 2305349) B2305349
theorem B2913347 : Blo 1020604 2913347 := bstep (se 1 (by rfl) ⟨2185010, by rfl⟩ : syracuseStep 2913347 = 4370021) B4370021
theorem B13988963 : Blo 1020604 13988963 := bstep (se 1 (by rfl) ⟨10491722, by rfl⟩ : syracuseStep 13988963 = 20983445) B20983445
theorem B2946179 : Blo 1020604 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B2618705 : Blo 1020604 2618705 := bstep (se 2 (by rfl) ⟨982014, by rfl⟩ : syracuseStep 2618705 = 1964029) B1964029
theorem B2913677 : Blo 1020604 2913677 := bstep (se 3 (by rfl) ⟨546314, by rfl⟩ : syracuseStep 2913677 = 1092629) B1092629
theorem B3503537 : Blo 1020604 3503537 := bstep (se 2 (by rfl) ⟨1313826, by rfl⟩ : syracuseStep 3503537 = 2627653) B2627653
theorem B3110339 : Blo 1020604 3110339 := bstep (se 1 (by rfl) ⟨2332754, by rfl⟩ : syracuseStep 3110339 = 4665509) B4665509
theorem B2913745 : Blo 1020604 2913745 := bstep (se 2 (by rfl) ⟨1092654, by rfl⟩ : syracuseStep 2913745 = 2185309) B2185309
theorem B3274349 : Blo 1020604 3274349 := bstep (se 3 (by rfl) ⟨613940, by rfl⟩ : syracuseStep 3274349 = 1227881) B1227881
theorem B2586289 : Blo 1020604 2586289 := bstep (se 2 (by rfl) ⟨969858, by rfl⟩ : syracuseStep 2586289 = 1939717) B1939717
theorem B2914019 : Blo 1020604 2914019 := bstep (se 1 (by rfl) ⟨2185514, by rfl⟩ : syracuseStep 2914019 = 4371029) B4371029
theorem B5175089 : Blo 1020604 5175089 := bstep (se 2 (by rfl) ⟨1940658, by rfl⟩ : syracuseStep 5175089 = 3881317) B3881317
theorem B1636195 : Blo 1020604 1636195 := bstep (se 1 (by rfl) ⟨1227146, by rfl⟩ : syracuseStep 1636195 = 2454293) B2454293
theorem B2586563 : Blo 1020604 2586563 := bstep (se 1 (by rfl) ⟨1939922, by rfl⟩ : syracuseStep 2586563 = 3879845) B3879845
theorem B2455523 : Blo 1020604 2455523 := bstep (se 1 (by rfl) ⟨1841642, by rfl⟩ : syracuseStep 2455523 = 3683285) B3683285
theorem B2586755 : Blo 1020604 2586755 := bstep (se 1 (by rfl) ⟨1940066, by rfl⟩ : syracuseStep 2586755 = 3880133) B3880133
theorem B4913293 : Blo 1020604 4913293 := bstep (se 3 (by rfl) ⟨921242, by rfl⟩ : syracuseStep 4913293 = 1842485) B1842485
theorem B2619811 : Blo 1020604 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B1243603 : Blo 1020604 1243603 := bstep (se 1 (by rfl) ⟨932702, by rfl⟩ : syracuseStep 1243603 = 1865405) B1865405
theorem B1636867 : Blo 1020604 1636867 := bstep (se 1 (by rfl) ⟨1227650, by rfl⟩ : syracuseStep 1636867 = 2455301) B2455301
theorem B2914861 : Blo 1020604 2914861 := bstep (se 3 (by rfl) ⟨546536, by rfl⟩ : syracuseStep 2914861 = 1093073) B1093073
theorem B1964675 : Blo 1020604 1964675 := bstep (se 1 (by rfl) ⟨1473506, by rfl⟩ : syracuseStep 1964675 = 2947013) B2947013
theorem B2915021 : Blo 1020604 2915021 := bstep (se 3 (by rfl) ⟨546566, by rfl⟩ : syracuseStep 2915021 = 1093133) B1093133
theorem B6552389 : Blo 1020604 6552389 := bstep (se 4 (by rfl) ⟨614286, by rfl⟩ : syracuseStep 6552389 = 1228573) B1228573
theorem B2915203 : Blo 1020604 2915203 := bstep (se 1 (by rfl) ⟨2186402, by rfl⟩ : syracuseStep 2915203 = 4372805) B4372805
theorem B1637329 : Blo 1020604 1637329 := bstep (se 2 (by rfl) ⟨613998, by rfl⟩ : syracuseStep 1637329 = 1227997) B1227997
theorem B1637425 : Blo 1020604 1637425 := bstep (se 2 (by rfl) ⟨614034, by rfl⟩ : syracuseStep 1637425 = 1228069) B1228069
theorem B2587697 : Blo 1020604 2587697 := bstep (se 2 (by rfl) ⟨970386, by rfl⟩ : syracuseStep 2587697 = 1940773) B1940773
theorem B2587747 : Blo 1020604 2587747 := bstep (se 1 (by rfl) ⟨1940810, by rfl⟩ : syracuseStep 2587747 = 3881621) B3881621
theorem B3275939 : Blo 1020604 3275939 := bstep (se 1 (by rfl) ⟨2456954, by rfl⟩ : syracuseStep 3275939 = 4913909) B4913909
theorem B1637585 : Blo 1020604 1637585 := bstep (se 2 (by rfl) ⟨614094, by rfl⟩ : syracuseStep 1637585 = 1228189) B1228189
theorem B5176547 : Blo 1020604 5176547 := bstep (se 1 (by rfl) ⟨3882410, by rfl⟩ : syracuseStep 5176547 = 7764821) B7764821
theorem B2587889 : Blo 1020604 2587889 := bstep (se 2 (by rfl) ⟨970458, by rfl⟩ : syracuseStep 2587889 = 1940917) B1940917
theorem B1965475 : Blo 1020604 1965475 := bstep (se 1 (by rfl) ⟨1474106, by rfl⟩ : syracuseStep 1965475 = 2948213) B2948213
theorem B3931811 : Blo 1020604 3931811 := bstep (se 1 (by rfl) ⟨2948858, by rfl⟩ : syracuseStep 3931811 = 5897717) B5897717
theorem B4423601 : Blo 1020604 4423601 := bstep (se 2 (by rfl) ⟨1658850, by rfl⟩ : syracuseStep 4423601 = 3317701) B3317701
theorem B2916445 : Blo 1020604 2916445 := bstep (se 3 (by rfl) ⟨546833, by rfl⟩ : syracuseStep 2916445 = 1093667) B1093667
theorem B17268997 : Blo 1020604 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B2588993 : Blo 1020604 2588993 := bstep (se 2 (by rfl) ⟨970872, by rfl⟩ : syracuseStep 2588993 = 1941745) B1941745
theorem B2163161 : Blo 1020604 2163161 := bstep (se 2 (by rfl) ⟨811185, by rfl⟩ : syracuseStep 2163161 = 1622371) B1622371
theorem B3932675 : Blo 1020604 3932675 := bstep (se 1 (by rfl) ⟨2949506, by rfl⟩ : syracuseStep 3932675 = 5899013) B5899013
theorem B5833367 : Blo 1020604 5833367 := bstep (se 1 (by rfl) ⟨4375025, by rfl⟩ : syracuseStep 5833367 = 8750051) B8750051
theorem B2458291 : Blo 1020604 2458291 := bstep (se 1 (by rfl) ⟨1843718, by rfl⟩ : syracuseStep 2458291 = 3687437) B3687437
theorem B3736343 : Blo 1020604 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B2589529 : Blo 1020604 2589529 := bstep (se 2 (by rfl) ⟨971073, by rfl⟩ : syracuseStep 2589529 = 1942147) B1942147
theorem B5178329 : Blo 1020604 5178329 := bstep (se 2 (by rfl) ⟨1941873, by rfl⟩ : syracuseStep 5178329 = 3883747) B3883747
theorem B12452881 : Blo 1020604 12452881 := bstep (se 2 (by rfl) ⟨4669830, by rfl⟩ : syracuseStep 12452881 = 9339661) B9339661
theorem B4719809 : Blo 1020604 4719809 := bstep (se 2 (by rfl) ⟨1769928, by rfl⟩ : syracuseStep 4719809 = 3539857) B3539857
theorem B1148215 : Blo 1020604 1148215 := bstep (se 1 (by rfl) ⟨861161, by rfl⟩ : syracuseStep 1148215 = 1722323) B1722323
theorem B2917721 : Blo 1020604 2917721 := bstep (se 2 (by rfl) ⟨1094145, by rfl⟩ : syracuseStep 2917721 = 2188291) B2188291
theorem B8750429 : Blo 1020604 8750429 := bstep (se 3 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 8750429 = 3281411) B3281411
theorem B1246603 : Blo 1020604 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B2328011 : Blo 1020604 2328011 := bstep (se 1 (by rfl) ⟨1746008, by rfl⟩ : syracuseStep 2328011 = 3492017) B3492017
theorem B1148395 : Blo 1020604 1148395 := bstep (se 1 (by rfl) ⟨861296, by rfl⟩ : syracuseStep 1148395 = 1722593) B1722593
theorem B4359683 : Blo 1020604 4359683 := bstep (se 1 (by rfl) ⟨3269762, by rfl⟩ : syracuseStep 4359683 = 6539525) B6539525
theorem B4916753 : Blo 1020604 4916753 := bstep (se 2 (by rfl) ⟨1843782, by rfl⟩ : syracuseStep 4916753 = 3687565) B3687565
theorem B1148503 : Blo 1020604 1148503 := bstep (se 1 (by rfl) ⟨861377, by rfl⟩ : syracuseStep 1148503 = 1722755) B1722755
theorem B1148683 : Blo 1020604 1148683 := bstep (se 1 (by rfl) ⟨861512, by rfl⟩ : syracuseStep 1148683 = 1723025) B1723025
theorem B7374667 : Blo 1020604 7374667 := bstep (se 1 (by rfl) ⟨5531000, by rfl⟩ : syracuseStep 7374667 = 11062001) B11062001
theorem B1148791 : Blo 1020604 1148791 := bstep (se 1 (by rfl) ⟨861593, by rfl⟩ : syracuseStep 1148791 = 1723187) B1723187
theorem B2590643 : Blo 1020604 2590643 := bstep (se 1 (by rfl) ⟨1942982, by rfl⟩ : syracuseStep 2590643 = 3885965) B3885965
theorem B3278809 : Blo 1020604 3278809 := bstep (se 2 (by rfl) ⟨1229553, by rfl⟩ : syracuseStep 3278809 = 2459107) B2459107
theorem B1148971 : Blo 1020604 1148971 := bstep (se 1 (by rfl) ⟨861728, by rfl⟩ : syracuseStep 1148971 = 1723457) B1723457
theorem B4917293 : Blo 1020604 4917293 := bstep (se 3 (by rfl) ⟨921992, by rfl⟩ : syracuseStep 4917293 = 1843985) B1843985
theorem B2328641 : Blo 1020604 2328641 := bstep (se 2 (by rfl) ⟨873240, by rfl⟩ : syracuseStep 2328641 = 1746481) B1746481
theorem B2951261 : Blo 1020604 2951261 := bstep (se 3 (by rfl) ⟨553361, by rfl⟩ : syracuseStep 2951261 = 1106723) B1106723
theorem B1149079 : Blo 1020604 1149079 := bstep (se 1 (by rfl) ⟨861809, by rfl⟩ : syracuseStep 1149079 = 1723619) B1723619
theorem B11634839 : Blo 1020604 11634839 := bstep (se 1 (by rfl) ⟨8726129, by rfl⟩ : syracuseStep 11634839 = 17452259) B17452259
theorem B2590937 : Blo 1020604 2590937 := bstep (se 2 (by rfl) ⟨971601, by rfl⟩ : syracuseStep 2590937 = 1943203) B1943203
theorem B1149259 : Blo 1020604 1149259 := bstep (se 1 (by rfl) ⟨861944, by rfl⟩ : syracuseStep 1149259 = 1723889) B1723889
theorem B1149367 : Blo 1020604 1149367 := bstep (se 1 (by rfl) ⟨862025, by rfl⟩ : syracuseStep 1149367 = 1724051) B1724051
theorem B11045393 : Blo 1020604 11045393 := bstep (se 2 (by rfl) ⟨4142022, by rfl⟩ : syracuseStep 11045393 = 8284045) B8284045
theorem B5179949 : Blo 1020604 5179949 := bstep (se 3 (by rfl) ⟨971240, by rfl⟩ : syracuseStep 5179949 = 1942481) B1942481
theorem B2296385 : Blo 1020604 2296385 := bstep (se 2 (by rfl) ⟨861144, by rfl⟩ : syracuseStep 2296385 = 1722289) B1722289
theorem B6556261 : Blo 1020604 6556261 := bstep (se 4 (by rfl) ⟨614649, by rfl⟩ : syracuseStep 6556261 = 1229299) B1229299
theorem B1149547 : Blo 1020604 1149547 := bstep (se 1 (by rfl) ⟨862160, by rfl⟩ : syracuseStep 1149547 = 1724321) B1724321
theorem B5900951 : Blo 1020604 5900951 := bstep (se 1 (by rfl) ⟨4425713, by rfl⟩ : syracuseStep 5900951 = 8851427) B8851427
theorem B4655819 : Blo 1020604 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B1149655 : Blo 1020604 1149655 := bstep (se 1 (by rfl) ⟨862241, by rfl⟩ : syracuseStep 1149655 = 1724483) B1724483
theorem B2296601 : Blo 1020604 2296601 := bstep (se 2 (by rfl) ⟨861225, by rfl⟩ : syracuseStep 2296601 = 1722451) B1722451
theorem B8293195 : Blo 1020604 8293195 := bstep (se 1 (by rfl) ⟨6219896, by rfl⟩ : syracuseStep 8293195 = 12439793) B12439793
theorem B2296691 : Blo 1020604 2296691 := bstep (se 1 (by rfl) ⟨1722518, by rfl⟩ : syracuseStep 2296691 = 3445037) B3445037
theorem B1149835 : Blo 1020604 1149835 := bstep (se 1 (by rfl) ⟨862376, by rfl⟩ : syracuseStep 1149835 = 1724753) B1724753
theorem B2296727 : Blo 1020604 2296727 := bstep (se 1 (by rfl) ⟨1722545, by rfl⟩ : syracuseStep 2296727 = 3445091) B3445091
theorem B1149943 : Blo 1020604 1149943 := bstep (se 1 (by rfl) ⟨862457, by rfl⟩ : syracuseStep 1149943 = 1724915) B1724915
theorem B2296907 : Blo 1020604 2296907 := bstep (se 1 (by rfl) ⟨1722680, by rfl⟩ : syracuseStep 2296907 = 3445361) B3445361
theorem B6556747 : Blo 1020604 6556747 := bstep (se 1 (by rfl) ⟨4917560, by rfl⟩ : syracuseStep 6556747 = 9835121) B9835121
theorem B2296961 : Blo 1020604 2296961 := bstep (se 2 (by rfl) ⟨861360, by rfl⟩ : syracuseStep 2296961 = 1722721) B1722721
theorem B1150123 : Blo 1020604 1150123 := bstep (se 1 (by rfl) ⟨862592, by rfl⟩ : syracuseStep 1150123 = 1725185) B1725185
theorem B1150231 : Blo 1020604 1150231 := bstep (se 1 (by rfl) ⟨862673, by rfl⟩ : syracuseStep 1150231 = 1725347) B1725347
theorem B3280193 : Blo 1020604 3280193 := bstep (se 2 (by rfl) ⟨1230072, by rfl⟩ : syracuseStep 3280193 = 2460145) B2460145
theorem B2297177 : Blo 1020604 2297177 := bstep (se 2 (by rfl) ⟨861441, by rfl⟩ : syracuseStep 2297177 = 1722883) B1722883
theorem B1478027 : Blo 1020604 1478027 := bstep (se 1 (by rfl) ⟨1108520, by rfl⟩ : syracuseStep 1478027 = 2217041) B2217041
theorem B2297267 : Blo 1020604 2297267 := bstep (se 1 (by rfl) ⟨1722950, by rfl⟩ : syracuseStep 2297267 = 3445901) B3445901
theorem B1150411 : Blo 1020604 1150411 := bstep (se 1 (by rfl) ⟨862808, by rfl⟩ : syracuseStep 1150411 = 1725617) B1725617
theorem B2297303 : Blo 1020604 2297303 := bstep (se 1 (by rfl) ⟨1722977, by rfl⟩ : syracuseStep 2297303 = 3445955) B3445955
theorem B1150519 : Blo 1020604 1150519 := bstep (se 1 (by rfl) ⟨862889, by rfl⟩ : syracuseStep 1150519 = 1725779) B1725779
theorem B2297483 : Blo 1020604 2297483 := bstep (se 1 (by rfl) ⟨1723112, by rfl⟩ : syracuseStep 2297483 = 3446225) B3446225
theorem B2297537 : Blo 1020604 2297537 := bstep (se 2 (by rfl) ⟨861576, by rfl⟩ : syracuseStep 2297537 = 1723153) B1723153
theorem B1150699 : Blo 1020604 1150699 := bstep (se 1 (by rfl) ⟨863024, by rfl⟩ : syracuseStep 1150699 = 1726049) B1726049
theorem B2592587 : Blo 1020604 2592587 := bstep (se 1 (by rfl) ⟨1944440, by rfl⟩ : syracuseStep 2592587 = 3888881) B3888881
theorem B1150807 : Blo 1020604 1150807 := bstep (se 1 (by rfl) ⟨863105, by rfl⟩ : syracuseStep 1150807 = 1726211) B1726211
theorem B2461529 : Blo 1020604 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B3280733 : Blo 1020604 3280733 := bstep (se 3 (by rfl) ⟨615137, by rfl⟩ : syracuseStep 3280733 = 1230275) B1230275
theorem B2297753 : Blo 1020604 2297753 := bstep (se 2 (by rfl) ⟨861657, by rfl⟩ : syracuseStep 2297753 = 1723315) B1723315
theorem B3444659 : Blo 1020604 3444659 := bstep (se 1 (by rfl) ⟨2583494, by rfl⟩ : syracuseStep 3444659 = 5166989) B5166989
theorem B2297843 : Blo 1020604 2297843 := bstep (se 1 (by rfl) ⟨1723382, by rfl⟩ : syracuseStep 2297843 = 3446765) B3446765
theorem B1150987 : Blo 1020604 1150987 := bstep (se 1 (by rfl) ⟨863240, by rfl⟩ : syracuseStep 1150987 = 1726481) B1726481
theorem B2297879 : Blo 1020604 2297879 := bstep (se 1 (by rfl) ⟨1723409, by rfl⟩ : syracuseStep 2297879 = 3446819) B3446819
theorem B1839169 : Blo 1020604 1839169 := bstep (se 2 (by rfl) ⟨689688, by rfl⟩ : syracuseStep 1839169 = 1379377) B1379377
theorem B8720459 : Blo 1020604 8720459 := bstep (se 1 (by rfl) ⟨6540344, by rfl⟩ : syracuseStep 8720459 = 13080689) B13080689
theorem B1151095 : Blo 1020604 1151095 := bstep (se 1 (by rfl) ⟨863321, by rfl⟩ : syracuseStep 1151095 = 1726643) B1726643
theorem B3444929 : Blo 1020604 3444929 := bstep (se 2 (by rfl) ⟨1291848, by rfl⟩ : syracuseStep 3444929 = 2583697) B2583697
theorem B2298059 : Blo 1020604 2298059 := bstep (se 1 (by rfl) ⟨1723544, by rfl⟩ : syracuseStep 2298059 = 3447089) B3447089
theorem B2298113 : Blo 1020604 2298113 := bstep (se 2 (by rfl) ⟨861792, by rfl⟩ : syracuseStep 2298113 = 1723585) B1723585
theorem B1937675 : Blo 1020604 1937675 := bstep (se 1 (by rfl) ⟨1453256, by rfl⟩ : syracuseStep 1937675 = 2906513) B2906513
theorem B1151275 : Blo 1020604 1151275 := bstep (se 1 (by rfl) ⟨863456, by rfl⟩ : syracuseStep 1151275 = 1726913) B1726913
theorem B2953523 : Blo 1020604 2953523 := bstep (se 1 (by rfl) ⟨2215142, by rfl⟩ : syracuseStep 2953523 = 4430285) B4430285
theorem B1151383 : Blo 1020604 1151383 := bstep (se 1 (by rfl) ⟨863537, by rfl⟩ : syracuseStep 1151383 = 1727075) B1727075
theorem B1937857 : Blo 1020604 1937857 := bstep (se 2 (by rfl) ⟨726696, by rfl⟩ : syracuseStep 1937857 = 1453393) B1453393
theorem B2298329 : Blo 1020604 2298329 := bstep (se 2 (by rfl) ⟨861873, by rfl⟩ : syracuseStep 2298329 = 1723747) B1723747
theorem B2298419 : Blo 1020604 2298419 := bstep (se 1 (by rfl) ⟨1723814, by rfl⟩ : syracuseStep 2298419 = 3447629) B3447629
theorem B1151563 : Blo 1020604 1151563 := bstep (se 1 (by rfl) ⟨863672, by rfl⟩ : syracuseStep 1151563 = 1727345) B1727345
theorem B2298455 : Blo 1020604 2298455 := bstep (se 1 (by rfl) ⟨1723841, by rfl⟩ : syracuseStep 2298455 = 3447683) B3447683
theorem B21041795 : Blo 1020604 21041795 := bstep (se 1 (by rfl) ⟨15781346, by rfl⟩ : syracuseStep 21041795 = 31562693) B31562693
theorem B1151671 : Blo 1020604 1151671 := bstep (se 1 (by rfl) ⟨863753, by rfl⟩ : syracuseStep 1151671 = 1727507) B1727507
theorem B1020619 : Blo 1020604 1020619 := bstep (se 1 (by rfl) ⟨765464, by rfl⟩ : syracuseStep 1020619 = 1530929) B1530929
theorem B1020631 : Blo 1020604 1020631 := bstep (se 1 (by rfl) ⟨765473, by rfl⟩ : syracuseStep 1020631 = 1530947) B1530947
theorem B3445469 : Blo 1020604 3445469 := bstep (se 3 (by rfl) ⟨646025, by rfl⟩ : syracuseStep 3445469 = 1292051) B1292051
theorem B1020651 : Blo 1020604 1020651 := bstep (se 1 (by rfl) ⟨765488, by rfl⟩ : syracuseStep 1020651 = 1530977) B1530977
theorem B1020663 : Blo 1020604 1020663 := bstep (se 1 (by rfl) ⟨765497, by rfl⟩ : syracuseStep 1020663 = 1530995) B1530995
theorem B1020683 : Blo 1020604 1020683 := bstep (se 1 (by rfl) ⟨765512, by rfl⟩ : syracuseStep 1020683 = 1531025) B1531025
theorem B2298635 : Blo 1020604 2298635 := bstep (se 1 (by rfl) ⟨1723976, by rfl⟩ : syracuseStep 2298635 = 3447953) B3447953
theorem B1020695 : Blo 1020604 1020695 := bstep (se 1 (by rfl) ⟨765521, by rfl⟩ : syracuseStep 1020695 = 1531043) B1531043
theorem B1020715 : Blo 1020604 1020715 := bstep (se 1 (by rfl) ⟨765536, by rfl⟩ : syracuseStep 1020715 = 1531073) B1531073
theorem B1020727 : Blo 1020604 1020727 := bstep (se 1 (by rfl) ⟨765545, by rfl⟩ : syracuseStep 1020727 = 1531091) B1531091
theorem B2298689 : Blo 1020604 2298689 := bstep (se 2 (by rfl) ⟨862008, by rfl⟩ : syracuseStep 2298689 = 1724017) B1724017
theorem B1020747 : Blo 1020604 1020747 := bstep (se 1 (by rfl) ⟨765560, by rfl⟩ : syracuseStep 1020747 = 1531121) B1531121
theorem B1020759 : Blo 1020604 1020759 := bstep (se 1 (by rfl) ⟨765569, by rfl⟩ : syracuseStep 1020759 = 1531139) B1531139
theorem B1020779 : Blo 1020604 1020779 := bstep (se 1 (by rfl) ⟨765584, by rfl⟩ : syracuseStep 1020779 = 1531169) B1531169
theorem B1151851 : Blo 1020604 1151851 := bstep (se 1 (by rfl) ⟨863888, by rfl⟩ : syracuseStep 1151851 = 1727777) B1727777
theorem B1020791 : Blo 1020604 1020791 := bstep (se 1 (by rfl) ⟨765593, by rfl⟩ : syracuseStep 1020791 = 1531187) B1531187
theorem B1938305 : Blo 1020604 1938305 := bstep (se 2 (by rfl) ⟨726864, by rfl⟩ : syracuseStep 1938305 = 1453729) B1453729
theorem B1020811 : Blo 1020604 1020811 := bstep (se 1 (by rfl) ⟨765608, by rfl⟩ : syracuseStep 1020811 = 1531217) B1531217
theorem B1381259 : Blo 1020604 1381259 := bstep (se 1 (by rfl) ⟨1035944, by rfl⟩ : syracuseStep 1381259 = 2071889) B2071889
theorem B1020823 : Blo 1020604 1020823 := bstep (se 1 (by rfl) ⟨765617, by rfl⟩ : syracuseStep 1020823 = 1531235) B1531235
theorem B1020843 : Blo 1020604 1020843 := bstep (se 1 (by rfl) ⟨765632, by rfl⟩ : syracuseStep 1020843 = 1531265) B1531265
theorem B1020855 : Blo 1020604 1020855 := bstep (se 1 (by rfl) ⟨765641, by rfl⟩ : syracuseStep 1020855 = 1531283) B1531283
theorem B1020875 : Blo 1020604 1020875 := bstep (se 1 (by rfl) ⟨765656, by rfl⟩ : syracuseStep 1020875 = 1531313) B1531313
theorem B1020887 : Blo 1020604 1020887 := bstep (se 1 (by rfl) ⟨765665, by rfl⟩ : syracuseStep 1020887 = 1531331) B1531331
theorem B1151959 : Blo 1020604 1151959 := bstep (se 1 (by rfl) ⟨863969, by rfl⟩ : syracuseStep 1151959 = 1727939) B1727939
theorem B1020907 : Blo 1020604 1020907 := bstep (se 1 (by rfl) ⟨765680, by rfl⟩ : syracuseStep 1020907 = 1531361) B1531361
theorem B1020919 : Blo 1020604 1020919 := bstep (se 1 (by rfl) ⟨765689, by rfl⟩ : syracuseStep 1020919 = 1531379) B1531379
theorem B1020939 : Blo 1020604 1020939 := bstep (se 1 (by rfl) ⟨765704, by rfl⟩ : syracuseStep 1020939 = 1531409) B1531409
theorem B1020951 : Blo 1020604 1020951 := bstep (se 1 (by rfl) ⟨765713, by rfl⟩ : syracuseStep 1020951 = 1531427) B1531427
theorem B1840151 : Blo 1020604 1840151 := bstep (se 1 (by rfl) ⟨1380113, by rfl⟩ : syracuseStep 1840151 = 2760227) B2760227
theorem B2298905 : Blo 1020604 2298905 := bstep (se 2 (by rfl) ⟨862089, by rfl⟩ : syracuseStep 2298905 = 1724179) B1724179
theorem B1020971 : Blo 1020604 1020971 := bstep (se 1 (by rfl) ⟨765728, by rfl⟩ : syracuseStep 1020971 = 1531457) B1531457
theorem B1020983 : Blo 1020604 1020983 := bstep (se 1 (by rfl) ⟨765737, by rfl⟩ : syracuseStep 1020983 = 1531475) B1531475
theorem B1021003 : Blo 1020604 1021003 := bstep (se 1 (by rfl) ⟨765752, by rfl⟩ : syracuseStep 1021003 = 1531505) B1531505
theorem B1021015 : Blo 1020604 1021015 := bstep (se 1 (by rfl) ⟨765761, by rfl⟩ : syracuseStep 1021015 = 1531523) B1531523
theorem B1021035 : Blo 1020604 1021035 := bstep (se 1 (by rfl) ⟨765776, by rfl⟩ : syracuseStep 1021035 = 1531553) B1531553
theorem B2298995 : Blo 1020604 2298995 := bstep (se 1 (by rfl) ⟨1724246, by rfl⟩ : syracuseStep 2298995 = 3448493) B3448493
theorem B1021047 : Blo 1020604 1021047 := bstep (se 1 (by rfl) ⟨765785, by rfl⟩ : syracuseStep 1021047 = 1531571) B1531571
theorem B1021067 : Blo 1020604 1021067 := bstep (se 1 (by rfl) ⟨765800, by rfl⟩ : syracuseStep 1021067 = 1531601) B1531601
theorem B1152139 : Blo 1020604 1152139 := bstep (se 1 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 1152139 = 1728209) B1728209
theorem B1021079 : Blo 1020604 1021079 := bstep (se 1 (by rfl) ⟨765809, by rfl⟩ : syracuseStep 1021079 = 1531619) B1531619
theorem B2299031 : Blo 1020604 2299031 := bstep (se 1 (by rfl) ⟨1724273, by rfl⟩ : syracuseStep 2299031 = 3448547) B3448547
theorem B1021099 : Blo 1020604 1021099 := bstep (se 1 (by rfl) ⟨765824, by rfl⟩ : syracuseStep 1021099 = 1531649) B1531649
theorem B1021111 : Blo 1020604 1021111 := bstep (se 1 (by rfl) ⟨765833, by rfl⟩ : syracuseStep 1021111 = 1531667) B1531667
theorem B1021131 : Blo 1020604 1021131 := bstep (se 1 (by rfl) ⟨765848, by rfl⟩ : syracuseStep 1021131 = 1531697) B1531697
theorem B1021143 : Blo 1020604 1021143 := bstep (se 1 (by rfl) ⟨765857, by rfl⟩ : syracuseStep 1021143 = 1531715) B1531715
theorem B1938647 : Blo 1020604 1938647 := bstep (se 1 (by rfl) ⟨1453985, by rfl⟩ : syracuseStep 1938647 = 2907971) B2907971
theorem B1021163 : Blo 1020604 1021163 := bstep (se 1 (by rfl) ⟨765872, by rfl⟩ : syracuseStep 1021163 = 1531745) B1531745
theorem B1021175 : Blo 1020604 1021175 := bstep (se 1 (by rfl) ⟨765881, by rfl⟩ : syracuseStep 1021175 = 1531763) B1531763
theorem B1152247 : Blo 1020604 1152247 := bstep (se 1 (by rfl) ⟨864185, by rfl⟩ : syracuseStep 1152247 = 1728371) B1728371
theorem B1021195 : Blo 1020604 1021195 := bstep (se 1 (by rfl) ⟨765896, by rfl⟩ : syracuseStep 1021195 = 1531793) B1531793
theorem B1021207 : Blo 1020604 1021207 := bstep (se 1 (by rfl) ⟨765905, by rfl⟩ : syracuseStep 1021207 = 1531811) B1531811
theorem B1021227 : Blo 1020604 1021227 := bstep (se 1 (by rfl) ⟨765920, by rfl⟩ : syracuseStep 1021227 = 1531841) B1531841
theorem B1021239 : Blo 1020604 1021239 := bstep (se 1 (by rfl) ⟨765929, by rfl⟩ : syracuseStep 1021239 = 1531859) B1531859
theorem B1021259 : Blo 1020604 1021259 := bstep (se 1 (by rfl) ⟨765944, by rfl⟩ : syracuseStep 1021259 = 1531889) B1531889
theorem B2299211 : Blo 1020604 2299211 := bstep (se 1 (by rfl) ⟨1724408, by rfl⟩ : syracuseStep 2299211 = 3448817) B3448817
theorem B1021271 : Blo 1020604 1021271 := bstep (se 1 (by rfl) ⟨765953, by rfl⟩ : syracuseStep 1021271 = 1531907) B1531907
theorem B1021291 : Blo 1020604 1021291 := bstep (se 1 (by rfl) ⟨765968, by rfl⟩ : syracuseStep 1021291 = 1531937) B1531937
theorem B1021303 : Blo 1020604 1021303 := bstep (se 1 (by rfl) ⟨765977, by rfl⟩ : syracuseStep 1021303 = 1531955) B1531955
theorem B2299265 : Blo 1020604 2299265 := bstep (se 2 (by rfl) ⟨862224, by rfl⟩ : syracuseStep 2299265 = 1724449) B1724449
theorem B1021323 : Blo 1020604 1021323 := bstep (se 1 (by rfl) ⟨765992, by rfl⟩ : syracuseStep 1021323 = 1531985) B1531985
theorem B1021335 : Blo 1020604 1021335 := bstep (se 1 (by rfl) ⟨766001, by rfl⟩ : syracuseStep 1021335 = 1532003) B1532003
theorem B1021355 : Blo 1020604 1021355 := bstep (se 1 (by rfl) ⟨766016, by rfl⟩ : syracuseStep 1021355 = 1532033) B1532033
theorem B1152427 : Blo 1020604 1152427 := bstep (se 1 (by rfl) ⟨864320, by rfl⟩ : syracuseStep 1152427 = 1728641) B1728641
theorem B1021367 : Blo 1020604 1021367 := bstep (se 1 (by rfl) ⟨766025, by rfl⟩ : syracuseStep 1021367 = 1532051) B1532051
theorem B1021387 : Blo 1020604 1021387 := bstep (se 1 (by rfl) ⟨766040, by rfl⟩ : syracuseStep 1021387 = 1532081) B1532081
theorem B1021399 : Blo 1020604 1021399 := bstep (se 1 (by rfl) ⟨766049, by rfl⟩ : syracuseStep 1021399 = 1532099) B1532099
theorem B1021419 : Blo 1020604 1021419 := bstep (se 1 (by rfl) ⟨766064, by rfl⟩ : syracuseStep 1021419 = 1532129) B1532129
theorem B1021431 : Blo 1020604 1021431 := bstep (se 1 (by rfl) ⟨766073, by rfl⟩ : syracuseStep 1021431 = 1532147) B1532147
theorem B1021451 : Blo 1020604 1021451 := bstep (se 1 (by rfl) ⟨766088, by rfl⟩ : syracuseStep 1021451 = 1532177) B1532177
theorem B1021463 : Blo 1020604 1021463 := bstep (se 1 (by rfl) ⟨766097, by rfl⟩ : syracuseStep 1021463 = 1532195) B1532195
theorem B1152535 : Blo 1020604 1152535 := bstep (se 1 (by rfl) ⟨864401, by rfl⟩ : syracuseStep 1152535 = 1728803) B1728803
theorem B1021483 : Blo 1020604 1021483 := bstep (se 1 (by rfl) ⟨766112, by rfl⟩ : syracuseStep 1021483 = 1532225) B1532225
theorem B1021495 : Blo 1020604 1021495 := bstep (se 1 (by rfl) ⟨766121, by rfl⟩ : syracuseStep 1021495 = 1532243) B1532243
theorem B1021515 : Blo 1020604 1021515 := bstep (se 1 (by rfl) ⟨766136, by rfl⟩ : syracuseStep 1021515 = 1532273) B1532273
theorem B1840727 : Blo 1020604 1840727 := bstep (se 1 (by rfl) ⟨1380545, by rfl⟩ : syracuseStep 1840727 = 2761091) B2761091
theorem B1021527 : Blo 1020604 1021527 := bstep (se 1 (by rfl) ⟨766145, by rfl⟩ : syracuseStep 1021527 = 1532291) B1532291
theorem B2299481 : Blo 1020604 2299481 := bstep (se 2 (by rfl) ⟨862305, by rfl⟩ : syracuseStep 2299481 = 1724611) B1724611
theorem B1021547 : Blo 1020604 1021547 := bstep (se 1 (by rfl) ⟨766160, by rfl⟩ : syracuseStep 1021547 = 1532321) B1532321
theorem B1021559 : Blo 1020604 1021559 := bstep (se 1 (by rfl) ⟨766169, by rfl⟩ : syracuseStep 1021559 = 1532339) B1532339
theorem B2332289 : Blo 1020604 2332289 := bstep (se 2 (by rfl) ⟨874608, by rfl⟩ : syracuseStep 2332289 = 1749217) B1749217
theorem B1021579 : Blo 1020604 1021579 := bstep (se 1 (by rfl) ⟨766184, by rfl⟩ : syracuseStep 1021579 = 1532369) B1532369
theorem B1021591 : Blo 1020604 1021591 := bstep (se 1 (by rfl) ⟨766193, by rfl⟩ : syracuseStep 1021591 = 1532387) B1532387
theorem B4920983 : Blo 1020604 4920983 := bstep (se 1 (by rfl) ⟨3690737, by rfl⟩ : syracuseStep 4920983 = 7381475) B7381475
theorem B1021611 : Blo 1020604 1021611 := bstep (se 1 (by rfl) ⟨766208, by rfl⟩ : syracuseStep 1021611 = 1532417) B1532417
theorem B4363955 : Blo 1020604 4363955 := bstep (se 1 (by rfl) ⟨3272966, by rfl⟩ : syracuseStep 4363955 = 6545933) B6545933
theorem B2299571 : Blo 1020604 2299571 := bstep (se 1 (by rfl) ⟨1724678, by rfl⟩ : syracuseStep 2299571 = 3449357) B3449357
theorem B1021623 : Blo 1020604 1021623 := bstep (se 1 (by rfl) ⟨766217, by rfl⟩ : syracuseStep 1021623 = 1532435) B1532435
theorem B31495877 : Blo 1020604 31495877 := bstep (se 4 (by rfl) ⟨2952738, by rfl⟩ : syracuseStep 31495877 = 5905477) B5905477
theorem B1021643 : Blo 1020604 1021643 := bstep (se 1 (by rfl) ⟨766232, by rfl⟩ : syracuseStep 1021643 = 1532465) B1532465
theorem B1021655 : Blo 1020604 1021655 := bstep (se 1 (by rfl) ⟨766241, by rfl⟩ : syracuseStep 1021655 = 1532483) B1532483
theorem B2299607 : Blo 1020604 2299607 := bstep (se 1 (by rfl) ⟨1724705, by rfl⟩ : syracuseStep 2299607 = 3449411) B3449411
theorem B1021675 : Blo 1020604 1021675 := bstep (se 1 (by rfl) ⟨766256, by rfl⟩ : syracuseStep 1021675 = 1532513) B1532513
theorem B1021687 : Blo 1020604 1021687 := bstep (se 1 (by rfl) ⟨766265, by rfl⟩ : syracuseStep 1021687 = 1532531) B1532531
theorem B1021707 : Blo 1020604 1021707 := bstep (se 1 (by rfl) ⟨766280, by rfl⟩ : syracuseStep 1021707 = 1532561) B1532561
theorem B1021719 : Blo 1020604 1021719 := bstep (se 1 (by rfl) ⟨766289, by rfl⟩ : syracuseStep 1021719 = 1532579) B1532579
theorem B1382167 : Blo 1020604 1382167 := bstep (se 1 (by rfl) ⟨1036625, by rfl⟩ : syracuseStep 1382167 = 2073251) B2073251
theorem B1021739 : Blo 1020604 1021739 := bstep (se 1 (by rfl) ⟨766304, by rfl⟩ : syracuseStep 1021739 = 1532609) B1532609
theorem B1021751 : Blo 1020604 1021751 := bstep (se 1 (by rfl) ⟨766313, by rfl⟩ : syracuseStep 1021751 = 1532627) B1532627
theorem B3446603 : Blo 1020604 3446603 := bstep (se 1 (by rfl) ⟨2584952, by rfl⟩ : syracuseStep 3446603 = 5169905) B5169905
theorem B1021771 : Blo 1020604 1021771 := bstep (se 1 (by rfl) ⟨766328, by rfl⟩ : syracuseStep 1021771 = 1532657) B1532657
theorem B1021783 : Blo 1020604 1021783 := bstep (se 1 (by rfl) ⟨766337, by rfl⟩ : syracuseStep 1021783 = 1532675) B1532675
theorem B1021803 : Blo 1020604 1021803 := bstep (se 1 (by rfl) ⟨766352, by rfl⟩ : syracuseStep 1021803 = 1532705) B1532705
theorem B1939315 : Blo 1020604 1939315 := bstep (se 1 (by rfl) ⟨1454486, by rfl⟩ : syracuseStep 1939315 = 2908973) B2908973
theorem B1021815 : Blo 1020604 1021815 := bstep (se 1 (by rfl) ⟨766361, by rfl⟩ : syracuseStep 1021815 = 1532723) B1532723
theorem B1021835 : Blo 1020604 1021835 := bstep (se 1 (by rfl) ⟨766376, by rfl⟩ : syracuseStep 1021835 = 1532753) B1532753
theorem B2299787 : Blo 1020604 2299787 := bstep (se 1 (by rfl) ⟨1724840, by rfl⟩ : syracuseStep 2299787 = 3449681) B3449681
theorem B1021847 : Blo 1020604 1021847 := bstep (se 1 (by rfl) ⟨766385, by rfl⟩ : syracuseStep 1021847 = 1532771) B1532771
theorem B1021867 : Blo 1020604 1021867 := bstep (se 1 (by rfl) ⟨766400, by rfl⟩ : syracuseStep 1021867 = 1532801) B1532801
theorem B1021879 : Blo 1020604 1021879 := bstep (se 1 (by rfl) ⟨766409, by rfl⟩ : syracuseStep 1021879 = 1532819) B1532819
theorem B2299841 : Blo 1020604 2299841 := bstep (se 2 (by rfl) ⟨862440, by rfl⟩ : syracuseStep 2299841 = 1724881) B1724881
theorem B1021899 : Blo 1020604 1021899 := bstep (se 1 (by rfl) ⟨766424, by rfl⟩ : syracuseStep 1021899 = 1532849) B1532849
theorem B1021911 : Blo 1020604 1021911 := bstep (se 1 (by rfl) ⟨766433, by rfl⟩ : syracuseStep 1021911 = 1532867) B1532867
theorem B1021931 : Blo 1020604 1021931 := bstep (se 1 (by rfl) ⟨766448, by rfl⟩ : syracuseStep 1021931 = 1532897) B1532897
theorem B1021943 : Blo 1020604 1021943 := bstep (se 1 (by rfl) ⟨766457, by rfl⟩ : syracuseStep 1021943 = 1532915) B1532915
theorem B1021963 : Blo 1020604 1021963 := bstep (se 1 (by rfl) ⟨766472, by rfl⟩ : syracuseStep 1021963 = 1532945) B1532945
theorem B1021975 : Blo 1020604 1021975 := bstep (se 1 (by rfl) ⟨766481, by rfl⟩ : syracuseStep 1021975 = 1532963) B1532963
theorem B9836579 : Blo 1020604 9836579 := bstep (se 1 (by rfl) ⟨7377434, by rfl⟩ : syracuseStep 9836579 = 14754869) B14754869
theorem B1021995 : Blo 1020604 1021995 := bstep (se 1 (by rfl) ⟨766496, by rfl⟩ : syracuseStep 1021995 = 1532993) B1532993
theorem B1022007 : Blo 1020604 1022007 := bstep (se 1 (by rfl) ⟨766505, by rfl⟩ : syracuseStep 1022007 = 1533011) B1533011
theorem B1022027 : Blo 1020604 1022027 := bstep (se 1 (by rfl) ⟨766520, by rfl⟩ : syracuseStep 1022027 = 1533041) B1533041
theorem B1022039 : Blo 1020604 1022039 := bstep (se 1 (by rfl) ⟨766529, by rfl⟩ : syracuseStep 1022039 = 1533059) B1533059
theorem B3446873 : Blo 1020604 3446873 := bstep (se 2 (by rfl) ⟨1292577, by rfl⟩ : syracuseStep 3446873 = 2585155) B2585155
theorem B1022059 : Blo 1020604 1022059 := bstep (se 1 (by rfl) ⟨766544, by rfl⟩ : syracuseStep 1022059 = 1533089) B1533089
theorem B1022071 : Blo 1020604 1022071 := bstep (se 1 (by rfl) ⟨766553, by rfl⟩ : syracuseStep 1022071 = 1533107) B1533107
theorem B1022091 : Blo 1020604 1022091 := bstep (se 1 (by rfl) ⟨766568, by rfl⟩ : syracuseStep 1022091 = 1533137) B1533137
theorem B1022103 : Blo 1020604 1022103 := bstep (se 1 (by rfl) ⟨766577, by rfl⟩ : syracuseStep 1022103 = 1533155) B1533155
theorem B2300057 : Blo 1020604 2300057 := bstep (se 2 (by rfl) ⟨862521, by rfl⟩ : syracuseStep 2300057 = 1725043) B1725043
theorem B1022123 : Blo 1020604 1022123 := bstep (se 1 (by rfl) ⟨766592, by rfl⟩ : syracuseStep 1022123 = 1533185) B1533185
theorem B1022135 : Blo 1020604 1022135 := bstep (se 1 (by rfl) ⟨766601, by rfl⟩ : syracuseStep 1022135 = 1533203) B1533203
theorem B1022155 : Blo 1020604 1022155 := bstep (se 1 (by rfl) ⟨766616, by rfl⟩ : syracuseStep 1022155 = 1533233) B1533233
theorem B1022167 : Blo 1020604 1022167 := bstep (se 1 (by rfl) ⟨766625, by rfl⟩ : syracuseStep 1022167 = 1533251) B1533251
theorem B1022187 : Blo 1020604 1022187 := bstep (se 1 (by rfl) ⟨766640, by rfl⟩ : syracuseStep 1022187 = 1533281) B1533281
theorem B2300147 : Blo 1020604 2300147 := bstep (se 1 (by rfl) ⟨1725110, by rfl⟩ : syracuseStep 2300147 = 3450221) B3450221
theorem B1022199 : Blo 1020604 1022199 := bstep (se 1 (by rfl) ⟨766649, by rfl⟩ : syracuseStep 1022199 = 1533299) B1533299
theorem B1022219 : Blo 1020604 1022219 := bstep (se 1 (by rfl) ⟨766664, by rfl⟩ : syracuseStep 1022219 = 1533329) B1533329
theorem B1022231 : Blo 1020604 1022231 := bstep (se 1 (by rfl) ⟨766673, by rfl⟩ : syracuseStep 1022231 = 1533347) B1533347
theorem B2300183 : Blo 1020604 2300183 := bstep (se 1 (by rfl) ⟨1725137, by rfl⟩ : syracuseStep 2300183 = 3450275) B3450275
theorem B1022251 : Blo 1020604 1022251 := bstep (se 1 (by rfl) ⟨766688, by rfl⟩ : syracuseStep 1022251 = 1533377) B1533377
theorem B1939763 : Blo 1020604 1939763 := bstep (se 1 (by rfl) ⟨1454822, by rfl⟩ : syracuseStep 1939763 = 2909645) B2909645
theorem B1022263 : Blo 1020604 1022263 := bstep (se 1 (by rfl) ⟨766697, by rfl⟩ : syracuseStep 1022263 = 1533395) B1533395
theorem B1022283 : Blo 1020604 1022283 := bstep (se 1 (by rfl) ⟨766712, by rfl⟩ : syracuseStep 1022283 = 1533425) B1533425
theorem B1022295 : Blo 1020604 1022295 := bstep (se 1 (by rfl) ⟨766721, by rfl⟩ : syracuseStep 1022295 = 1533443) B1533443
theorem B1939801 : Blo 1020604 1939801 := bstep (se 2 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 1939801 = 1454851) B1454851
theorem B5183837 : Blo 1020604 5183837 := bstep (se 3 (by rfl) ⟨971969, by rfl⟩ : syracuseStep 5183837 = 1943939) B1943939
theorem B1022315 : Blo 1020604 1022315 := bstep (se 1 (by rfl) ⟨766736, by rfl⟩ : syracuseStep 1022315 = 1533473) B1533473
theorem B1022327 : Blo 1020604 1022327 := bstep (se 1 (by rfl) ⟨766745, by rfl⟩ : syracuseStep 1022327 = 1533491) B1533491
theorem B1022347 : Blo 1020604 1022347 := bstep (se 1 (by rfl) ⟨766760, by rfl⟩ : syracuseStep 1022347 = 1533521) B1533521
theorem B1022359 : Blo 1020604 1022359 := bstep (se 1 (by rfl) ⟨766769, by rfl⟩ : syracuseStep 1022359 = 1533539) B1533539
theorem B1022379 : Blo 1020604 1022379 := bstep (se 1 (by rfl) ⟨766784, by rfl⟩ : syracuseStep 1022379 = 1533569) B1533569
theorem B1022391 : Blo 1020604 1022391 := bstep (se 1 (by rfl) ⟨766793, by rfl⟩ : syracuseStep 1022391 = 1533587) B1533587
theorem B2300363 : Blo 1020604 2300363 := bstep (se 1 (by rfl) ⟨1725272, by rfl⟩ : syracuseStep 2300363 = 3450545) B3450545
theorem B1022411 : Blo 1020604 1022411 := bstep (se 1 (by rfl) ⟨766808, by rfl⟩ : syracuseStep 1022411 = 1533617) B1533617
theorem B1022423 : Blo 1020604 1022423 := bstep (se 1 (by rfl) ⟨766817, by rfl⟩ : syracuseStep 1022423 = 1533635) B1533635
theorem B1022443 : Blo 1020604 1022443 := bstep (se 1 (by rfl) ⟨766832, by rfl⟩ : syracuseStep 1022443 = 1533665) B1533665
theorem B1022455 : Blo 1020604 1022455 := bstep (se 1 (by rfl) ⟨766841, by rfl⟩ : syracuseStep 1022455 = 1533683) B1533683
theorem B2300417 : Blo 1020604 2300417 := bstep (se 2 (by rfl) ⟨862656, by rfl⟩ : syracuseStep 2300417 = 1725313) B1725313
theorem B1022475 : Blo 1020604 1022475 := bstep (se 1 (by rfl) ⟨766856, by rfl⟩ : syracuseStep 1022475 = 1533713) B1533713
theorem B1022487 : Blo 1020604 1022487 := bstep (se 1 (by rfl) ⟨766865, by rfl⟩ : syracuseStep 1022487 = 1533731) B1533731
theorem B1022507 : Blo 1020604 1022507 := bstep (se 1 (by rfl) ⟨766880, by rfl⟩ : syracuseStep 1022507 = 1533761) B1533761
theorem B1022519 : Blo 1020604 1022519 := bstep (se 1 (by rfl) ⟨766889, by rfl⟩ : syracuseStep 1022519 = 1533779) B1533779
theorem B2333249 : Blo 1020604 2333249 := bstep (se 2 (by rfl) ⟨874968, by rfl⟩ : syracuseStep 2333249 = 1749937) B1749937
theorem B1022539 : Blo 1020604 1022539 := bstep (se 1 (by rfl) ⟨766904, by rfl⟩ : syracuseStep 1022539 = 1533809) B1533809
theorem B1022551 : Blo 1020604 1022551 := bstep (se 1 (by rfl) ⟨766913, by rfl⟩ : syracuseStep 1022551 = 1533827) B1533827
theorem B12622429 : Blo 1020604 12622429 := bstep (se 3 (by rfl) ⟨2366705, by rfl⟩ : syracuseStep 12622429 = 4733411) B4733411
theorem B1022571 : Blo 1020604 1022571 := bstep (se 1 (by rfl) ⟨766928, by rfl⟩ : syracuseStep 1022571 = 1533857) B1533857
theorem B1841779 : Blo 1020604 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B1022583 : Blo 1020604 1022583 := bstep (se 1 (by rfl) ⟨766937, by rfl⟩ : syracuseStep 1022583 = 1533875) B1533875
theorem B1022603 : Blo 1020604 1022603 := bstep (se 1 (by rfl) ⟨766952, by rfl⟩ : syracuseStep 1022603 = 1533905) B1533905
theorem B1022615 : Blo 1020604 1022615 := bstep (se 1 (by rfl) ⟨766961, by rfl⟩ : syracuseStep 1022615 = 1533923) B1533923
theorem B1022635 : Blo 1020604 1022635 := bstep (se 1 (by rfl) ⟨766976, by rfl⟩ : syracuseStep 1022635 = 1533953) B1533953
theorem B8723123 : Blo 1020604 8723123 := bstep (se 1 (by rfl) ⟨6542342, by rfl⟩ : syracuseStep 8723123 = 13084685) B13084685
theorem B1022647 : Blo 1020604 1022647 := bstep (se 1 (by rfl) ⟨766985, by rfl⟩ : syracuseStep 1022647 = 1533971) B1533971
theorem B1022667 : Blo 1020604 1022667 := bstep (se 1 (by rfl) ⟨767000, by rfl⟩ : syracuseStep 1022667 = 1534001) B1534001
theorem B1022679 : Blo 1020604 1022679 := bstep (se 1 (by rfl) ⟨767009, by rfl⟩ : syracuseStep 1022679 = 1534019) B1534019
theorem B2300633 : Blo 1020604 2300633 := bstep (se 2 (by rfl) ⟨862737, by rfl⟩ : syracuseStep 2300633 = 1725475) B1725475
theorem B1022699 : Blo 1020604 1022699 := bstep (se 1 (by rfl) ⟨767024, by rfl⟩ : syracuseStep 1022699 = 1534049) B1534049
theorem B1022711 : Blo 1020604 1022711 := bstep (se 1 (by rfl) ⟨767033, by rfl⟩ : syracuseStep 1022711 = 1534067) B1534067
theorem B1022731 : Blo 1020604 1022731 := bstep (se 1 (by rfl) ⟨767048, by rfl⟩ : syracuseStep 1022731 = 1534097) B1534097
theorem B3447575 : Blo 1020604 3447575 := bstep (se 1 (by rfl) ⟨2585681, by rfl⟩ : syracuseStep 3447575 = 5171363) B5171363
theorem B1022743 : Blo 1020604 1022743 := bstep (se 1 (by rfl) ⟨767057, by rfl⟩ : syracuseStep 1022743 = 1534115) B1534115
theorem B1940249 : Blo 1020604 1940249 := bstep (se 2 (by rfl) ⟨727593, by rfl⟩ : syracuseStep 1940249 = 1455187) B1455187
theorem B2333465 : Blo 1020604 2333465 := bstep (se 2 (by rfl) ⟨875049, by rfl⟩ : syracuseStep 2333465 = 1750099) B1750099
theorem B1022763 : Blo 1020604 1022763 := bstep (se 1 (by rfl) ⟨767072, by rfl⟩ : syracuseStep 1022763 = 1534145) B1534145
theorem B2300723 : Blo 1020604 2300723 := bstep (se 1 (by rfl) ⟨1725542, by rfl⟩ : syracuseStep 2300723 = 3451085) B3451085
theorem B1022775 : Blo 1020604 1022775 := bstep (se 1 (by rfl) ⟨767081, by rfl⟩ : syracuseStep 1022775 = 1534163) B1534163
theorem B1022795 : Blo 1020604 1022795 := bstep (se 1 (by rfl) ⟨767096, by rfl⟩ : syracuseStep 1022795 = 1534193) B1534193
theorem B2300759 : Blo 1020604 2300759 := bstep (se 1 (by rfl) ⟨1725569, by rfl⟩ : syracuseStep 2300759 = 3451139) B3451139
theorem B1022807 : Blo 1020604 1022807 := bstep (se 1 (by rfl) ⟨767105, by rfl⟩ : syracuseStep 1022807 = 1534211) B1534211
theorem B1022827 : Blo 1020604 1022827 := bstep (se 1 (by rfl) ⟨767120, by rfl⟩ : syracuseStep 1022827 = 1534241) B1534241
theorem B1022839 : Blo 1020604 1022839 := bstep (se 1 (by rfl) ⟨767129, by rfl⟩ : syracuseStep 1022839 = 1534259) B1534259
theorem B1022859 : Blo 1020604 1022859 := bstep (se 1 (by rfl) ⟨767144, by rfl⟩ : syracuseStep 1022859 = 1534289) B1534289
theorem B1022871 : Blo 1020604 1022871 := bstep (se 1 (by rfl) ⟨767153, by rfl⟩ : syracuseStep 1022871 = 1534307) B1534307
theorem B1022891 : Blo 1020604 1022891 := bstep (se 1 (by rfl) ⟨767168, by rfl⟩ : syracuseStep 1022891 = 1534337) B1534337
theorem B1022903 : Blo 1020604 1022903 := bstep (se 1 (by rfl) ⟨767177, by rfl⟩ : syracuseStep 1022903 = 1534355) B1534355
theorem B2071499 : Blo 1020604 2071499 := bstep (se 1 (by rfl) ⟨1553624, by rfl⟩ : syracuseStep 2071499 = 3107249) B3107249
theorem B1022923 : Blo 1020604 1022923 := bstep (se 1 (by rfl) ⟨767192, by rfl⟩ : syracuseStep 1022923 = 1534385) B1534385
theorem B1022935 : Blo 1020604 1022935 := bstep (se 1 (by rfl) ⟨767201, by rfl⟩ : syracuseStep 1022935 = 1534403) B1534403
theorem B4922329 : Blo 1020604 4922329 := bstep (se 2 (by rfl) ⟨1845873, by rfl⟩ : syracuseStep 4922329 = 3691747) B3691747
theorem B1022955 : Blo 1020604 1022955 := bstep (se 1 (by rfl) ⟨767216, by rfl⟩ : syracuseStep 1022955 = 1534433) B1534433
theorem B2333683 : Blo 1020604 2333683 := bstep (se 1 (by rfl) ⟨1750262, by rfl⟩ : syracuseStep 2333683 = 3500525) B3500525
theorem B1022967 : Blo 1020604 1022967 := bstep (se 1 (by rfl) ⟨767225, by rfl⟩ : syracuseStep 1022967 = 1534451) B1534451
theorem B2300939 : Blo 1020604 2300939 := bstep (se 1 (by rfl) ⟨1725704, by rfl⟩ : syracuseStep 2300939 = 3451409) B3451409
theorem B1022987 : Blo 1020604 1022987 := bstep (se 1 (by rfl) ⟨767240, by rfl⟩ : syracuseStep 1022987 = 1534481) B1534481
theorem B1022999 : Blo 1020604 1022999 := bstep (se 1 (by rfl) ⟨767249, by rfl⟩ : syracuseStep 1022999 = 1534499) B1534499
theorem B2366489 : Blo 1020604 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B1023019 : Blo 1020604 1023019 := bstep (se 1 (by rfl) ⟨767264, by rfl⟩ : syracuseStep 1023019 = 1534529) B1534529
theorem B5610541 : Blo 1020604 5610541 := bstep (se 3 (by rfl) ⟨1051976, by rfl⟩ : syracuseStep 5610541 = 2103953) B2103953
theorem B1023031 : Blo 1020604 1023031 := bstep (se 1 (by rfl) ⟨767273, by rfl⟩ : syracuseStep 1023031 = 1534547) B1534547
theorem B2300993 : Blo 1020604 2300993 := bstep (se 2 (by rfl) ⟨862872, by rfl⟩ : syracuseStep 2300993 = 1725745) B1725745
theorem B1023051 : Blo 1020604 1023051 := bstep (se 1 (by rfl) ⟨767288, by rfl⟩ : syracuseStep 1023051 = 1534577) B1534577
theorem B1023063 : Blo 1020604 1023063 := bstep (se 1 (by rfl) ⟨767297, by rfl⟩ : syracuseStep 1023063 = 1534595) B1534595
theorem B1023083 : Blo 1020604 1023083 := bstep (se 1 (by rfl) ⟨767312, by rfl⟩ : syracuseStep 1023083 = 1534625) B1534625
theorem B1023095 : Blo 1020604 1023095 := bstep (se 1 (by rfl) ⟨767321, by rfl⟩ : syracuseStep 1023095 = 1534643) B1534643
theorem B1023115 : Blo 1020604 1023115 := bstep (se 1 (by rfl) ⟨767336, by rfl⟩ : syracuseStep 1023115 = 1534673) B1534673
theorem B1023127 : Blo 1020604 1023127 := bstep (se 1 (by rfl) ⟨767345, by rfl⟩ : syracuseStep 1023127 = 1534691) B1534691
theorem B1023147 : Blo 1020604 1023147 := bstep (se 1 (by rfl) ⟨767360, by rfl⟩ : syracuseStep 1023147 = 1534721) B1534721
theorem B1023159 : Blo 1020604 1023159 := bstep (se 1 (by rfl) ⟨767369, by rfl⟩ : syracuseStep 1023159 = 1534739) B1534739
theorem B1023179 : Blo 1020604 1023179 := bstep (se 1 (by rfl) ⟨767384, by rfl⟩ : syracuseStep 1023179 = 1534769) B1534769
theorem B1023191 : Blo 1020604 1023191 := bstep (se 1 (by rfl) ⟨767393, by rfl⟩ : syracuseStep 1023191 = 1534787) B1534787
theorem B1023211 : Blo 1020604 1023211 := bstep (se 1 (by rfl) ⟨767408, by rfl⟩ : syracuseStep 1023211 = 1534817) B1534817
theorem B1023223 : Blo 1020604 1023223 := bstep (se 1 (by rfl) ⟨767417, by rfl⟩ : syracuseStep 1023223 = 1534835) B1534835
theorem B19930373 : Blo 1020604 19930373 := bstep (se 4 (by rfl) ⟨1868472, by rfl⟩ : syracuseStep 19930373 = 3736945) B3736945
theorem B1023243 : Blo 1020604 1023243 := bstep (se 1 (by rfl) ⟨767432, by rfl⟩ : syracuseStep 1023243 = 1534865) B1534865
theorem B1023255 : Blo 1020604 1023255 := bstep (se 1 (by rfl) ⟨767441, by rfl⟩ : syracuseStep 1023255 = 1534883) B1534883
theorem B2301209 : Blo 1020604 2301209 := bstep (se 2 (by rfl) ⟨862953, by rfl⟩ : syracuseStep 2301209 = 1725907) B1725907
theorem B1023275 : Blo 1020604 1023275 := bstep (se 1 (by rfl) ⟨767456, by rfl⟩ : syracuseStep 1023275 = 1534913) B1534913
theorem B3448115 : Blo 1020604 3448115 := bstep (se 1 (by rfl) ⟨2586086, by rfl⟩ : syracuseStep 3448115 = 5172173) B5172173
theorem B1023287 : Blo 1020604 1023287 := bstep (se 1 (by rfl) ⟨767465, by rfl⟩ : syracuseStep 1023287 = 1534931) B1534931
theorem B1023307 : Blo 1020604 1023307 := bstep (se 1 (by rfl) ⟨767480, by rfl⟩ : syracuseStep 1023307 = 1534961) B1534961
theorem B1023319 : Blo 1020604 1023319 := bstep (se 1 (by rfl) ⟨767489, by rfl⟩ : syracuseStep 1023319 = 1534979) B1534979
theorem B1023339 : Blo 1020604 1023339 := bstep (se 1 (by rfl) ⟨767504, by rfl⟩ : syracuseStep 1023339 = 1535009) B1535009
theorem B2301299 : Blo 1020604 2301299 := bstep (se 1 (by rfl) ⟨1725974, by rfl⟩ : syracuseStep 2301299 = 3451949) B3451949
theorem B1023351 : Blo 1020604 1023351 := bstep (se 1 (by rfl) ⟨767513, by rfl⟩ : syracuseStep 1023351 = 1535027) B1535027
theorem B1023371 : Blo 1020604 1023371 := bstep (se 1 (by rfl) ⟨767528, by rfl⟩ : syracuseStep 1023371 = 1535057) B1535057
theorem B2301335 : Blo 1020604 2301335 := bstep (se 1 (by rfl) ⟨1726001, by rfl⟩ : syracuseStep 2301335 = 3452003) B3452003
theorem B1023383 : Blo 1020604 1023383 := bstep (se 1 (by rfl) ⟨767537, by rfl⟩ : syracuseStep 1023383 = 1535075) B1535075
theorem B1023403 : Blo 1020604 1023403 := bstep (se 1 (by rfl) ⟨767552, by rfl⟩ : syracuseStep 1023403 = 1535105) B1535105
theorem B1023415 : Blo 1020604 1023415 := bstep (se 1 (by rfl) ⟨767561, by rfl⟩ : syracuseStep 1023415 = 1535123) B1535123
theorem B1023435 : Blo 1020604 1023435 := bstep (se 1 (by rfl) ⟨767576, by rfl⟩ : syracuseStep 1023435 = 1535153) B1535153
theorem B1023447 : Blo 1020604 1023447 := bstep (se 1 (by rfl) ⟨767585, by rfl⟩ : syracuseStep 1023447 = 1535171) B1535171
theorem B1023467 : Blo 1020604 1023467 := bstep (se 1 (by rfl) ⟨767600, by rfl⟩ : syracuseStep 1023467 = 1535201) B1535201
theorem B1023479 : Blo 1020604 1023479 := bstep (se 1 (by rfl) ⟨767609, by rfl⟩ : syracuseStep 1023479 = 1535219) B1535219
theorem B1940993 : Blo 1020604 1940993 := bstep (se 2 (by rfl) ⟨727872, by rfl⟩ : syracuseStep 1940993 = 1455745) B1455745
theorem B1023499 : Blo 1020604 1023499 := bstep (se 1 (by rfl) ⟨767624, by rfl⟩ : syracuseStep 1023499 = 1535249) B1535249
theorem B1023511 : Blo 1020604 1023511 := bstep (se 1 (by rfl) ⟨767633, by rfl⟩ : syracuseStep 1023511 = 1535267) B1535267
theorem B15736355 : Blo 1020604 15736355 := bstep (se 1 (by rfl) ⟨11802266, by rfl⟩ : syracuseStep 15736355 = 23604533) B23604533
theorem B17735203 : Blo 1020604 17735203 := bstep (se 1 (by rfl) ⟨13301402, by rfl⟩ : syracuseStep 17735203 = 26602805) B26602805
theorem B1023531 : Blo 1020604 1023531 := bstep (se 1 (by rfl) ⟨767648, by rfl⟩ : syracuseStep 1023531 = 1535297) B1535297
theorem B1023543 : Blo 1020604 1023543 := bstep (se 1 (by rfl) ⟨767657, by rfl⟩ : syracuseStep 1023543 = 1535315) B1535315
theorem B3448385 : Blo 1020604 3448385 := bstep (se 2 (by rfl) ⟨1293144, by rfl⟩ : syracuseStep 3448385 = 2586289) B2586289
theorem B2301515 : Blo 1020604 2301515 := bstep (se 1 (by rfl) ⟨1726136, by rfl⟩ : syracuseStep 2301515 = 3452273) B3452273
theorem B1023563 : Blo 1020604 1023563 := bstep (se 1 (by rfl) ⟨767672, by rfl⟩ : syracuseStep 1023563 = 1535345) B1535345
theorem B1023575 : Blo 1020604 1023575 := bstep (se 1 (by rfl) ⟨767681, by rfl⟩ : syracuseStep 1023575 = 1535363) B1535363
theorem B1023595 : Blo 1020604 1023595 := bstep (se 1 (by rfl) ⟨767696, by rfl⟩ : syracuseStep 1023595 = 1535393) B1535393
theorem B1023607 : Blo 1020604 1023607 := bstep (se 1 (by rfl) ⟨767705, by rfl⟩ : syracuseStep 1023607 = 1535411) B1535411
theorem B2301569 : Blo 1020604 2301569 := bstep (se 2 (by rfl) ⟨863088, by rfl⟩ : syracuseStep 2301569 = 1726177) B1726177
theorem B1023627 : Blo 1020604 1023627 := bstep (se 1 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 1023627 = 1535441) B1535441
theorem B1023639 : Blo 1020604 1023639 := bstep (se 1 (by rfl) ⟨767729, by rfl⟩ : syracuseStep 1023639 = 1535459) B1535459
theorem B1023659 : Blo 1020604 1023659 := bstep (se 1 (by rfl) ⟨767744, by rfl⟩ : syracuseStep 1023659 = 1535489) B1535489
theorem B2956979 : Blo 1020604 2956979 := bstep (se 1 (by rfl) ⟨2217734, by rfl⟩ : syracuseStep 2956979 = 4435469) B4435469
theorem B1023671 : Blo 1020604 1023671 := bstep (se 1 (by rfl) ⟨767753, by rfl⟩ : syracuseStep 1023671 = 1535507) B1535507
theorem B1023691 : Blo 1020604 1023691 := bstep (se 1 (by rfl) ⟨767768, by rfl⟩ : syracuseStep 1023691 = 1535537) B1535537
theorem B1023703 : Blo 1020604 1023703 := bstep (se 1 (by rfl) ⟨767777, by rfl⟩ : syracuseStep 1023703 = 1535555) B1535555
theorem B8724185 : Blo 1020604 8724185 := bstep (se 2 (by rfl) ⟨3271569, by rfl⟩ : syracuseStep 8724185 = 6543139) B6543139
theorem B1023723 : Blo 1020604 1023723 := bstep (se 1 (by rfl) ⟨767792, by rfl⟩ : syracuseStep 1023723 = 1535585) B1535585
theorem B22093553 : Blo 1020604 22093553 := bstep (se 2 (by rfl) ⟨8285082, by rfl⟩ : syracuseStep 22093553 = 16570165) B16570165
theorem B1023735 : Blo 1020604 1023735 := bstep (se 1 (by rfl) ⟨767801, by rfl⟩ : syracuseStep 1023735 = 1535603) B1535603
theorem B1941259 : Blo 1020604 1941259 := bstep (se 1 (by rfl) ⟨1455944, by rfl⟩ : syracuseStep 1941259 = 2911889) B2911889
theorem B1023755 : Blo 1020604 1023755 := bstep (se 1 (by rfl) ⟨767816, by rfl⟩ : syracuseStep 1023755 = 1535633) B1535633
theorem B1023767 : Blo 1020604 1023767 := bstep (se 1 (by rfl) ⟨767825, by rfl⟩ : syracuseStep 1023767 = 1535651) B1535651
theorem B1023787 : Blo 1020604 1023787 := bstep (se 1 (by rfl) ⟨767840, by rfl⟩ : syracuseStep 1023787 = 1535681) B1535681
theorem B1023799 : Blo 1020604 1023799 := bstep (se 1 (by rfl) ⟨767849, by rfl⟩ : syracuseStep 1023799 = 1535699) B1535699
theorem B1023819 : Blo 1020604 1023819 := bstep (se 1 (by rfl) ⟨767864, by rfl⟩ : syracuseStep 1023819 = 1535729) B1535729
theorem B1023831 : Blo 1020604 1023831 := bstep (se 1 (by rfl) ⟨767873, by rfl⟩ : syracuseStep 1023831 = 1535747) B1535747
theorem B2301785 : Blo 1020604 2301785 := bstep (se 2 (by rfl) ⟨863169, by rfl⟩ : syracuseStep 2301785 = 1726339) B1726339
theorem B1023851 : Blo 1020604 1023851 := bstep (se 1 (by rfl) ⟨767888, by rfl⟩ : syracuseStep 1023851 = 1535777) B1535777
theorem B1023863 : Blo 1020604 1023863 := bstep (se 1 (by rfl) ⟨767897, by rfl⟩ : syracuseStep 1023863 = 1535795) B1535795
theorem B1023883 : Blo 1020604 1023883 := bstep (se 1 (by rfl) ⟨767912, by rfl⟩ : syracuseStep 1023883 = 1535825) B1535825
theorem B1023895 : Blo 1020604 1023895 := bstep (se 1 (by rfl) ⟨767921, by rfl⟩ : syracuseStep 1023895 = 1535843) B1535843
theorem B1023915 : Blo 1020604 1023915 := bstep (se 1 (by rfl) ⟨767936, by rfl⟩ : syracuseStep 1023915 = 1535873) B1535873
theorem B2301875 : Blo 1020604 2301875 := bstep (se 1 (by rfl) ⟨1726406, by rfl⟩ : syracuseStep 2301875 = 3452813) B3452813
theorem B1023927 : Blo 1020604 1023927 := bstep (se 1 (by rfl) ⟨767945, by rfl⟩ : syracuseStep 1023927 = 1535891) B1535891
theorem B1023947 : Blo 1020604 1023947 := bstep (se 1 (by rfl) ⟨767960, by rfl⟩ : syracuseStep 1023947 = 1535921) B1535921
theorem B2301911 : Blo 1020604 2301911 := bstep (se 1 (by rfl) ⟨1726433, by rfl⟩ : syracuseStep 2301911 = 3452867) B3452867
theorem B1023959 : Blo 1020604 1023959 := bstep (se 1 (by rfl) ⟨767969, by rfl⟩ : syracuseStep 1023959 = 1535939) B1535939
theorem B1023979 : Blo 1020604 1023979 := bstep (se 1 (by rfl) ⟨767984, by rfl⟩ : syracuseStep 1023979 = 1535969) B1535969
theorem B2334707 : Blo 1020604 2334707 := bstep (se 1 (by rfl) ⟨1751030, by rfl⟩ : syracuseStep 2334707 = 3502061) B3502061
theorem B1023991 : Blo 1020604 1023991 := bstep (se 1 (by rfl) ⟨767993, by rfl⟩ : syracuseStep 1023991 = 1535987) B1535987
theorem B1024011 : Blo 1020604 1024011 := bstep (se 1 (by rfl) ⟨768008, by rfl⟩ : syracuseStep 1024011 = 1536017) B1536017
theorem B1024023 : Blo 1020604 1024023 := bstep (se 1 (by rfl) ⟨768017, by rfl⟩ : syracuseStep 1024023 = 1536035) B1536035
theorem B1024043 : Blo 1020604 1024043 := bstep (se 1 (by rfl) ⟨768032, by rfl⟩ : syracuseStep 1024043 = 1536065) B1536065
theorem B1024055 : Blo 1020604 1024055 := bstep (se 1 (by rfl) ⟨768041, by rfl⟩ : syracuseStep 1024055 = 1536083) B1536083
theorem B1024075 : Blo 1020604 1024075 := bstep (se 1 (by rfl) ⟨768056, by rfl⟩ : syracuseStep 1024075 = 1536113) B1536113
theorem B1024087 : Blo 1020604 1024087 := bstep (se 1 (by rfl) ⟨768065, by rfl⟩ : syracuseStep 1024087 = 1536131) B1536131
theorem B3448925 : Blo 1020604 3448925 := bstep (se 3 (by rfl) ⟨646673, by rfl⟩ : syracuseStep 3448925 = 1293347) B1293347
theorem B1024107 : Blo 1020604 1024107 := bstep (se 1 (by rfl) ⟨768080, by rfl⟩ : syracuseStep 1024107 = 1536161) B1536161
theorem B1024119 : Blo 1020604 1024119 := bstep (se 1 (by rfl) ⟨768089, by rfl⟩ : syracuseStep 1024119 = 1536179) B1536179
theorem B2302091 : Blo 1020604 2302091 := bstep (se 1 (by rfl) ⟨1726568, by rfl⟩ : syracuseStep 2302091 = 3453137) B3453137
theorem B1024139 : Blo 1020604 1024139 := bstep (se 1 (by rfl) ⟨768104, by rfl⟩ : syracuseStep 1024139 = 1536209) B1536209
theorem B1024151 : Blo 1020604 1024151 := bstep (se 1 (by rfl) ⟨768113, by rfl⟩ : syracuseStep 1024151 = 1536227) B1536227
theorem B1024171 : Blo 1020604 1024171 := bstep (se 1 (by rfl) ⟨768128, by rfl⟩ : syracuseStep 1024171 = 1536257) B1536257
theorem B1024183 : Blo 1020604 1024183 := bstep (se 1 (by rfl) ⟨768137, by rfl⟩ : syracuseStep 1024183 = 1536275) B1536275
theorem B2302145 : Blo 1020604 2302145 := bstep (se 2 (by rfl) ⟨863304, by rfl⟩ : syracuseStep 2302145 = 1726609) B1726609
theorem B1941707 : Blo 1020604 1941707 := bstep (se 1 (by rfl) ⟨1456280, by rfl⟩ : syracuseStep 1941707 = 2912561) B2912561
theorem B1024203 : Blo 1020604 1024203 := bstep (se 1 (by rfl) ⟨768152, by rfl⟩ : syracuseStep 1024203 = 1536305) B1536305
theorem B1024215 : Blo 1020604 1024215 := bstep (se 1 (by rfl) ⟨768161, by rfl⟩ : syracuseStep 1024215 = 1536323) B1536323
theorem B1024235 : Blo 1020604 1024235 := bstep (se 1 (by rfl) ⟨768176, by rfl⟩ : syracuseStep 1024235 = 1536353) B1536353
theorem B1024247 : Blo 1020604 1024247 := bstep (se 1 (by rfl) ⟨768185, by rfl⟩ : syracuseStep 1024247 = 1536371) B1536371
theorem B1024267 : Blo 1020604 1024267 := bstep (se 1 (by rfl) ⟨768200, by rfl⟩ : syracuseStep 1024267 = 1536401) B1536401
theorem B1024279 : Blo 1020604 1024279 := bstep (se 1 (by rfl) ⟨768209, by rfl⟩ : syracuseStep 1024279 = 1536419) B1536419
theorem B1024299 : Blo 1020604 1024299 := bstep (se 1 (by rfl) ⟨768224, by rfl⟩ : syracuseStep 1024299 = 1536449) B1536449
theorem B1024311 : Blo 1020604 1024311 := bstep (se 1 (by rfl) ⟨768233, by rfl⟩ : syracuseStep 1024311 = 1536467) B1536467
theorem B1024331 : Blo 1020604 1024331 := bstep (se 1 (by rfl) ⟨768248, by rfl⟩ : syracuseStep 1024331 = 1536497) B1536497
theorem B2335063 : Blo 1020604 2335063 := bstep (se 1 (by rfl) ⟨1751297, by rfl⟩ : syracuseStep 2335063 = 3502595) B3502595
theorem B1024343 : Blo 1020604 1024343 := bstep (se 1 (by rfl) ⟨768257, by rfl⟩ : syracuseStep 1024343 = 1536515) B1536515
theorem B1024363 : Blo 1020604 1024363 := bstep (se 1 (by rfl) ⟨768272, by rfl⟩ : syracuseStep 1024363 = 1536545) B1536545
theorem B1024375 : Blo 1020604 1024375 := bstep (se 1 (by rfl) ⟨768281, by rfl⟩ : syracuseStep 1024375 = 1536563) B1536563
theorem B1941889 : Blo 1020604 1941889 := bstep (se 2 (by rfl) ⟨728208, by rfl⟩ : syracuseStep 1941889 = 1456417) B1456417
theorem B1024395 : Blo 1020604 1024395 := bstep (se 1 (by rfl) ⟨768296, by rfl⟩ : syracuseStep 1024395 = 1536593) B1536593
theorem B5185943 : Blo 1020604 5185943 := bstep (se 1 (by rfl) ⟨3889457, by rfl⟩ : syracuseStep 5185943 = 7778915) B7778915
theorem B1024407 : Blo 1020604 1024407 := bstep (se 1 (by rfl) ⟨768305, by rfl⟩ : syracuseStep 1024407 = 1536611) B1536611
theorem B2302361 : Blo 1020604 2302361 := bstep (se 2 (by rfl) ⟨863385, by rfl⟩ : syracuseStep 2302361 = 1726771) B1726771
theorem B1024427 : Blo 1020604 1024427 := bstep (se 1 (by rfl) ⟨768320, by rfl⟩ : syracuseStep 1024427 = 1536641) B1536641
theorem B1024439 : Blo 1020604 1024439 := bstep (se 1 (by rfl) ⟨768329, by rfl⟩ : syracuseStep 1024439 = 1536659) B1536659
theorem B1024459 : Blo 1020604 1024459 := bstep (se 1 (by rfl) ⟨768344, by rfl⟩ : syracuseStep 1024459 = 1536689) B1536689
theorem B1024471 : Blo 1020604 1024471 := bstep (se 1 (by rfl) ⟨768353, by rfl⟩ : syracuseStep 1024471 = 1536707) B1536707
theorem B1024491 : Blo 1020604 1024491 := bstep (se 1 (by rfl) ⟨768368, by rfl⟩ : syracuseStep 1024491 = 1536737) B1536737
theorem B2302451 : Blo 1020604 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B1024503 : Blo 1020604 1024503 := bstep (se 1 (by rfl) ⟨768377, by rfl⟩ : syracuseStep 1024503 = 1536755) B1536755
theorem B1024523 : Blo 1020604 1024523 := bstep (se 1 (by rfl) ⟨768392, by rfl⟩ : syracuseStep 1024523 = 1536785) B1536785
theorem B2302487 : Blo 1020604 2302487 := bstep (se 1 (by rfl) ⟨1726865, by rfl⟩ : syracuseStep 2302487 = 3453731) B3453731
theorem B1024535 : Blo 1020604 1024535 := bstep (se 1 (by rfl) ⟨768401, by rfl⟩ : syracuseStep 1024535 = 1536803) B1536803
theorem B1024555 : Blo 1020604 1024555 := bstep (se 1 (by rfl) ⟨768416, by rfl⟩ : syracuseStep 1024555 = 1536833) B1536833
theorem B1024567 : Blo 1020604 1024567 := bstep (se 1 (by rfl) ⟨768425, by rfl⟩ : syracuseStep 1024567 = 1536851) B1536851
theorem B1024587 : Blo 1020604 1024587 := bstep (se 1 (by rfl) ⟨768440, by rfl⟩ : syracuseStep 1024587 = 1536881) B1536881
theorem B1024599 : Blo 1020604 1024599 := bstep (se 1 (by rfl) ⟨768449, by rfl⟩ : syracuseStep 1024599 = 1536899) B1536899
theorem B2302667 : Blo 1020604 2302667 := bstep (se 1 (by rfl) ⟨1727000, by rfl⟩ : syracuseStep 2302667 = 3454001) B3454001
theorem B1942231 : Blo 1020604 1942231 := bstep (se 1 (by rfl) ⟨1456673, by rfl⟩ : syracuseStep 1942231 = 2913347) B2913347
theorem B2302721 : Blo 1020604 2302721 := bstep (se 2 (by rfl) ⟨863520, by rfl⟩ : syracuseStep 2302721 = 1727041) B1727041
theorem B2761523 : Blo 1020604 2761523 := bstep (se 1 (by rfl) ⟨2071142, by rfl⟩ : syracuseStep 2761523 = 4142285) B4142285
theorem B1745803 : Blo 1020604 1745803 := bstep (se 1 (by rfl) ⟨1309352, by rfl⟩ : syracuseStep 1745803 = 2618705) B2618705
theorem B1942451 : Blo 1020604 1942451 := bstep (se 1 (by rfl) ⟨1456838, by rfl⟩ : syracuseStep 1942451 = 2913677) B2913677
theorem B2335691 : Blo 1020604 2335691 := bstep (se 1 (by rfl) ⟨1751768, by rfl⟩ : syracuseStep 2335691 = 3503537) B3503537
theorem B2073559 : Blo 1020604 2073559 := bstep (se 1 (by rfl) ⟨1555169, by rfl⟩ : syracuseStep 2073559 = 3110339) B3110339
theorem B2302937 : Blo 1020604 2302937 := bstep (se 2 (by rfl) ⟨863601, by rfl⟩ : syracuseStep 2302937 = 1727203) B1727203
theorem B2303027 : Blo 1020604 2303027 := bstep (se 1 (by rfl) ⟨1727270, by rfl⟩ : syracuseStep 2303027 = 3454541) B3454541
theorem B2303063 : Blo 1020604 2303063 := bstep (se 1 (by rfl) ⟨1727297, by rfl⟩ : syracuseStep 2303063 = 3454595) B3454595
theorem B3875971 : Blo 1020604 3875971 := bstep (se 1 (by rfl) ⟨2906978, by rfl⟩ : syracuseStep 3875971 = 5813957) B5813957
theorem B1942679 : Blo 1020604 1942679 := bstep (se 1 (by rfl) ⟨1457009, by rfl⟩ : syracuseStep 1942679 = 2914019) B2914019
theorem B1844417 : Blo 1020604 1844417 := bstep (se 2 (by rfl) ⟨691656, by rfl⟩ : syracuseStep 1844417 = 1383313) B1383313
theorem B3450059 : Blo 1020604 3450059 := bstep (se 1 (by rfl) ⟨2587544, by rfl⟩ : syracuseStep 3450059 = 5175089) B5175089
theorem B2303243 : Blo 1020604 2303243 := bstep (se 1 (by rfl) ⟨1727432, by rfl⟩ : syracuseStep 2303243 = 3454865) B3454865
theorem B2303297 : Blo 1020604 2303297 := bstep (se 2 (by rfl) ⟨863736, by rfl⟩ : syracuseStep 2303297 = 1727473) B1727473
theorem B1942937 : Blo 1020604 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B3876275 : Blo 1020604 3876275 := bstep (se 1 (by rfl) ⟨2907206, by rfl⟩ : syracuseStep 3876275 = 5814413) B5814413
theorem B3679667 : Blo 1020604 3679667 := bstep (se 1 (by rfl) ⟨2759750, by rfl⟩ : syracuseStep 3679667 = 5519501) B5519501
theorem B3450329 : Blo 1020604 3450329 := bstep (se 2 (by rfl) ⟨1293873, by rfl⟩ : syracuseStep 3450329 = 2587747) B2587747
theorem B2303513 : Blo 1020604 2303513 := bstep (se 2 (by rfl) ⟨863817, by rfl⟩ : syracuseStep 2303513 = 1727635) B1727635
theorem B2303603 : Blo 1020604 2303603 := bstep (se 1 (by rfl) ⟨1727702, by rfl⟩ : syracuseStep 2303603 = 3455405) B3455405
theorem B13117079 : Blo 1020604 13117079 := bstep (se 1 (by rfl) ⟨9837809, by rfl⟩ : syracuseStep 13117079 = 19675619) B19675619
theorem B2303639 : Blo 1020604 2303639 := bstep (se 1 (by rfl) ⟨1727729, by rfl⟩ : syracuseStep 2303639 = 3455459) B3455459
theorem B3548951 : Blo 1020604 3548951 := bstep (se 1 (by rfl) ⟨2661713, by rfl⟩ : syracuseStep 3548951 = 5323427) B5323427
theorem B1943347 : Blo 1020604 1943347 := bstep (se 1 (by rfl) ⟨1457510, by rfl⟩ : syracuseStep 1943347 = 2915021) B2915021
theorem B2762561 : Blo 1020604 2762561 := bstep (se 2 (by rfl) ⟨1035960, by rfl⟩ : syracuseStep 2762561 = 2071921) B2071921
theorem B2303819 : Blo 1020604 2303819 := bstep (se 1 (by rfl) ⟨1727864, by rfl⟩ : syracuseStep 2303819 = 3455729) B3455729
theorem B2303873 : Blo 1020604 2303873 := bstep (se 2 (by rfl) ⟨863952, by rfl⟩ : syracuseStep 2303873 = 1727905) B1727905
theorem B4368259 : Blo 1020604 4368259 := bstep (se 1 (by rfl) ⟨3276194, by rfl⟩ : syracuseStep 4368259 = 6552389) B6552389
theorem B3876929 : Blo 1020604 3876929 := bstep (se 2 (by rfl) ⟨1453848, by rfl⟩ : syracuseStep 3876929 = 2907697) B2907697
theorem B2304089 : Blo 1020604 2304089 := bstep (se 2 (by rfl) ⟨864033, by rfl⟩ : syracuseStep 2304089 = 1728067) B1728067
theorem B1091723 : Blo 1020604 1091723 := bstep (se 1 (by rfl) ⟨818792, by rfl⟩ : syracuseStep 1091723 = 1637585) B1637585
theorem B3451031 : Blo 1020604 3451031 := bstep (se 1 (by rfl) ⟨2588273, by rfl⟩ : syracuseStep 3451031 = 5176547) B5176547
theorem B2304179 : Blo 1020604 2304179 := bstep (se 1 (by rfl) ⟨1728134, by rfl⟩ : syracuseStep 2304179 = 3456269) B3456269
theorem B2304215 : Blo 1020604 2304215 := bstep (se 1 (by rfl) ⟨1728161, by rfl⟩ : syracuseStep 2304215 = 3456323) B3456323
theorem B1943833 : Blo 1020604 1943833 := bstep (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) B1457875
theorem B2304395 : Blo 1020604 2304395 := bstep (se 1 (by rfl) ⟨1728296, by rfl⟩ : syracuseStep 2304395 = 3456593) B3456593
theorem B2304449 : Blo 1020604 2304449 := bstep (se 2 (by rfl) ⟨864168, by rfl⟩ : syracuseStep 2304449 = 1728337) B1728337
theorem B4139543 : Blo 1020604 4139543 := bstep (se 1 (by rfl) ⟨3104657, by rfl⟩ : syracuseStep 4139543 = 6209315) B6209315
theorem B2304665 : Blo 1020604 2304665 := bstep (se 2 (by rfl) ⟨864249, by rfl⟩ : syracuseStep 2304665 = 1728499) B1728499
theorem B3451571 : Blo 1020604 3451571 := bstep (se 1 (by rfl) ⟨2588678, by rfl⟩ : syracuseStep 3451571 = 5177357) B5177357
theorem B2304755 : Blo 1020604 2304755 := bstep (se 1 (by rfl) ⟨1728566, by rfl⟩ : syracuseStep 2304755 = 3457133) B3457133
theorem B4664087 : Blo 1020604 4664087 := bstep (se 1 (by rfl) ⟨3498065, by rfl⟩ : syracuseStep 4664087 = 6996131) B6996131
theorem B2304791 : Blo 1020604 2304791 := bstep (se 1 (by rfl) ⟨1728593, by rfl⟩ : syracuseStep 2304791 = 3457187) B3457187
theorem B4139851 : Blo 1020604 4139851 := bstep (se 1 (by rfl) ⟨3104888, by rfl⟩ : syracuseStep 4139851 = 6209777) B6209777
theorem B1944395 : Blo 1020604 1944395 := bstep (se 1 (by rfl) ⟨1458296, by rfl⟩ : syracuseStep 1944395 = 2916593) B2916593
theorem B3451841 : Blo 1020604 3451841 := bstep (se 2 (by rfl) ⟨1294440, by rfl⟩ : syracuseStep 3451841 = 2588881) B2588881
theorem B2304971 : Blo 1020604 2304971 := bstep (se 1 (by rfl) ⟨1728728, by rfl⟩ : syracuseStep 2304971 = 3457457) B3457457
theorem B1944577 : Blo 1020604 1944577 := bstep (se 2 (by rfl) ⟨729216, by rfl⟩ : syracuseStep 1944577 = 1458433) B1458433
theorem B2305025 : Blo 1020604 2305025 := bstep (se 2 (by rfl) ⟨864384, by rfl⟩ : syracuseStep 2305025 = 1728769) B1728769
theorem B8989741 : Blo 1020604 8989741 := bstep (se 3 (by rfl) ⟨1685576, by rfl⟩ : syracuseStep 8989741 = 3371153) B3371153
theorem B7777457 : Blo 1020604 7777457 := bstep (se 2 (by rfl) ⟨2916546, by rfl⟩ : syracuseStep 7777457 = 5833093) B5833093
theorem B2305241 : Blo 1020604 2305241 := bstep (se 2 (by rfl) ⟨864465, by rfl⟩ : syracuseStep 2305241 = 1728931) B1728931
theorem B7384355 : Blo 1020604 7384355 := bstep (se 1 (by rfl) ⟨5538266, by rfl⟩ : syracuseStep 7384355 = 11076533) B11076533
theorem B3878189 : Blo 1020604 3878189 := bstep (se 3 (by rfl) ⟨727160, by rfl⟩ : syracuseStep 3878189 = 1454321) B1454321
theorem B2305331 : Blo 1020604 2305331 := bstep (se 1 (by rfl) ⟨1728998, by rfl⟩ : syracuseStep 2305331 = 3457997) B3457997
theorem B3878219 : Blo 1020604 3878219 := bstep (se 1 (by rfl) ⟨2908664, by rfl⟩ : syracuseStep 3878219 = 5817329) B5817329
theorem B4140467 : Blo 1020604 4140467 := bstep (se 1 (by rfl) ⟨3105350, by rfl⟩ : syracuseStep 4140467 = 6210701) B6210701
theorem B11808179 : Blo 1020604 11808179 := bstep (se 1 (by rfl) ⟨8856134, by rfl⟩ : syracuseStep 11808179 = 17712269) B17712269
theorem B3452381 : Blo 1020604 3452381 := bstep (se 3 (by rfl) ⟨647321, by rfl⟩ : syracuseStep 3452381 = 1294643) B1294643
theorem B4370071 : Blo 1020604 4370071 := bstep (se 1 (by rfl) ⟨3277553, by rfl⟩ : syracuseStep 4370071 = 6555107) B6555107
theorem B7777943 : Blo 1020604 7777943 := bstep (se 1 (by rfl) ⟨5833457, by rfl⟩ : syracuseStep 7777943 = 11666915) B11666915
theorem B2764637 : Blo 1020604 2764637 := bstep (se 3 (by rfl) ⟨518369, by rfl⟩ : syracuseStep 2764637 = 1036739) B1036739
theorem B1093483 : Blo 1020604 1093483 := bstep (se 1 (by rfl) ⟨820112, by rfl⟩ : syracuseStep 1093483 = 1640225) B1640225
theorem B3878873 : Blo 1020604 3878873 := bstep (se 2 (by rfl) ⟨1454577, by rfl⟩ : syracuseStep 3878873 = 2909155) B2909155
theorem B2076673 : Blo 1020604 2076673 := bstep (se 2 (by rfl) ⟨778752, by rfl⟩ : syracuseStep 2076673 = 1557505) B1557505
theorem B4370705 : Blo 1020604 4370705 := bstep (se 2 (by rfl) ⟨1639014, by rfl⟩ : syracuseStep 4370705 = 3278029) B3278029
theorem B3879191 : Blo 1020604 3879191 := bstep (se 1 (by rfl) ⟨2909393, by rfl⟩ : syracuseStep 3879191 = 5818787) B5818787
theorem B3682867 : Blo 1020604 3682867 := bstep (se 1 (by rfl) ⟨2762150, by rfl⟩ : syracuseStep 3682867 = 5524301) B5524301
theorem B3453515 : Blo 1020604 3453515 := bstep (se 1 (by rfl) ⟨2590136, by rfl⟩ : syracuseStep 3453515 = 5180273) B5180273
theorem B3453785 : Blo 1020604 3453785 := bstep (se 2 (by rfl) ⟨1295169, by rfl⟩ : syracuseStep 3453785 = 2590339) B2590339
theorem B3879859 : Blo 1020604 3879859 := bstep (se 1 (by rfl) ⟨2909894, by rfl⟩ : syracuseStep 3879859 = 5819789) B5819789
theorem B4371403 : Blo 1020604 4371403 := bstep (se 1 (by rfl) ⟨3278552, by rfl⟩ : syracuseStep 4371403 = 6557105) B6557105
theorem B6632549 : Blo 1020604 6632549 := bstep (se 4 (by rfl) ⟨621801, by rfl⟩ : syracuseStep 6632549 = 1243603) B1243603
theorem B5256371 : Blo 1020604 5256371 := bstep (se 1 (by rfl) ⟨3942278, by rfl⟩ : syracuseStep 5256371 = 7884557) B7884557
theorem B4371677 : Blo 1020604 4371677 := bstep (se 3 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 4371677 = 1639379) B1639379
theorem B12432685 : Blo 1020604 12432685 := bstep (se 3 (by rfl) ⟨2331128, by rfl⟩ : syracuseStep 12432685 = 4662257) B4662257
theorem B8729957 : Blo 1020604 8729957 := bstep (se 4 (by rfl) ⟨818433, by rfl⟩ : syracuseStep 8729957 = 1636867) B1636867
theorem B3454487 : Blo 1020604 3454487 := bstep (se 1 (by rfl) ⟨2590865, by rfl⟩ : syracuseStep 3454487 = 5181731) B5181731
theorem B4372019 : Blo 1020604 4372019 := bstep (se 1 (by rfl) ⟨3279014, by rfl⟩ : syracuseStep 4372019 = 6558029) B6558029
theorem B37303901 : Blo 1020604 37303901 := bstep (se 3 (by rfl) ⟨6994481, by rfl⟩ : syracuseStep 37303901 = 13988963) B13988963
theorem B1292107 : Blo 1020604 1292107 := bstep (se 1 (by rfl) ⟨969080, by rfl⟩ : syracuseStep 1292107 = 1938161) B1938161
theorem B3455027 : Blo 1020604 3455027 := bstep (se 1 (by rfl) ⟨2591270, by rfl⟩ : syracuseStep 3455027 = 5182541) B5182541
theorem B1292375 : Blo 1020604 1292375 := bstep (se 1 (by rfl) ⟨969281, by rfl⟩ : syracuseStep 1292375 = 1938563) B1938563
theorem B6994021 : Blo 1020604 6994021 := bstep (se 4 (by rfl) ⟨655689, by rfl⟩ : syracuseStep 6994021 = 1311379) B1311379
theorem B3881105 : Blo 1020604 3881105 := bstep (se 2 (by rfl) ⟨1455414, by rfl⟩ : syracuseStep 3881105 = 2910829) B2910829
theorem B3455297 : Blo 1020604 3455297 := bstep (se 2 (by rfl) ⟨1295736, by rfl⟩ : syracuseStep 3455297 = 2591473) B2591473
theorem B1456537 : Blo 1020604 1456537 := bstep (se 2 (by rfl) ⟨546201, by rfl⟩ : syracuseStep 1456537 = 1092403) B1092403
theorem B18692531 : Blo 1020604 18692531 := bstep (se 1 (by rfl) ⟨14019398, by rfl⟩ : syracuseStep 18692531 = 28038797) B28038797
theorem B9320977 : Blo 1020604 9320977 := bstep (se 2 (by rfl) ⟨3495366, by rfl⟩ : syracuseStep 9320977 = 6990733) B6990733
theorem B1293079 : Blo 1020604 1293079 := bstep (se 1 (by rfl) ⟨969809, by rfl⟩ : syracuseStep 1293079 = 1939619) B1939619
theorem B3881803 : Blo 1020604 3881803 := bstep (se 1 (by rfl) ⟨2911352, by rfl⟩ : syracuseStep 3881803 = 5822705) B5822705
theorem B3455837 : Blo 1020604 3455837 := bstep (se 3 (by rfl) ⟨647969, by rfl⟩ : syracuseStep 3455837 = 1295939) B1295939
theorem B8731597 : Blo 1020604 8731597 := bstep (se 3 (by rfl) ⟨1637174, by rfl⟩ : syracuseStep 8731597 = 3274349) B3274349
theorem B11647961 : Blo 1020604 11647961 := bstep (se 2 (by rfl) ⟨4367985, by rfl⟩ : syracuseStep 11647961 = 8735971) B8735971
theorem B3882077 : Blo 1020604 3882077 := bstep (se 3 (by rfl) ⟨727889, by rfl⟩ : syracuseStep 3882077 = 1455779) B1455779
theorem B5815597 : Blo 1020604 5815597 := bstep (se 3 (by rfl) ⟨1090424, by rfl⟩ : syracuseStep 5815597 = 2180849) B2180849
theorem B3882775 : Blo 1020604 3882775 := bstep (se 1 (by rfl) ⟨2912081, by rfl⟩ : syracuseStep 3882775 = 5824163) B5824163
theorem B1457995 : Blo 1020604 1457995 := bstep (se 1 (by rfl) ⟨1093496, by rfl⟩ : syracuseStep 1457995 = 2186993) B2186993
theorem B4374445 : Blo 1020604 4374445 := bstep (se 3 (by rfl) ⟨820208, by rfl⟩ : syracuseStep 4374445 = 1640417) B1640417
theorem B3456971 : Blo 1020604 3456971 := bstep (se 1 (by rfl) ⟨2592728, by rfl⟩ : syracuseStep 3456971 = 5185457) B5185457
theorem B3457241 : Blo 1020604 3457241 := bstep (se 2 (by rfl) ⟨1296465, by rfl⟩ : syracuseStep 3457241 = 2592931) B2592931
theorem B8732933 : Blo 1020604 8732933 := bstep (se 4 (by rfl) ⟨818712, by rfl⟩ : syracuseStep 8732933 = 1637425) B1637425
theorem B1294795 : Blo 1020604 1294795 := bstep (se 1 (by rfl) ⟨971096, by rfl⟩ : syracuseStep 1294795 = 1942193) B1942193
theorem B2212339 : Blo 1020604 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B3883565 : Blo 1020604 3883565 := bstep (se 3 (by rfl) ⟨728168, by rfl⟩ : syracuseStep 3883565 = 1456337) B1456337
theorem B2245207 : Blo 1020604 2245207 := bstep (se 1 (by rfl) ⟨1683905, by rfl⟩ : syracuseStep 2245207 = 3367811) B3367811
theorem B3457943 : Blo 1020604 3457943 := bstep (se 1 (by rfl) ⟨2593457, by rfl⟩ : syracuseStep 3457943 = 5186915) B5186915
theorem B1295767 : Blo 1020604 1295767 := bstep (se 1 (by rfl) ⟨971825, by rfl⟩ : syracuseStep 1295767 = 1943651) B1943651
theorem B7751213 : Blo 1020604 7751213 := bstep (se 3 (by rfl) ⟨1453352, by rfl⟩ : syracuseStep 7751213 = 2906705) B2906705
theorem B3884993 : Blo 1020604 3884993 := bstep (se 2 (by rfl) ⟨1456872, by rfl⟩ : syracuseStep 3884993 = 2913745) B2913745
theorem B2181259 : Blo 1020604 2181259 := bstep (se 1 (by rfl) ⟨1635944, by rfl⟩ : syracuseStep 2181259 = 3271889) B3271889
theorem B1296587 : Blo 1020604 1296587 := bstep (se 1 (by rfl) ⟨972440, by rfl⟩ : syracuseStep 1296587 = 1944881) B1944881
theorem B1722647 : Blo 1020604 1722647 := bstep (se 1 (by rfl) ⟨1291985, by rfl⟩ : syracuseStep 1722647 = 2583971) B2583971
theorem B12798253 : Blo 1020604 12798253 := bstep (se 3 (by rfl) ⟨2399672, by rfl⟩ : syracuseStep 12798253 = 4799345) B4799345
theorem B1722775 : Blo 1020604 1722775 := bstep (se 1 (by rfl) ⟨1292081, by rfl⟩ : syracuseStep 1722775 = 2584163) B2584163
theorem B2181593 : Blo 1020604 2181593 := bstep (se 2 (by rfl) ⟨818097, by rfl⟩ : syracuseStep 2181593 = 1636195) B1636195
theorem B19942129 : Blo 1020604 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B13093811 : Blo 1020604 13093811 := bstep (se 1 (by rfl) ⟨9820358, by rfl⟩ : syracuseStep 13093811 = 19640717) B19640717
theorem B1723403 : Blo 1020604 1723403 := bstep (se 1 (by rfl) ⟨1292552, by rfl⟩ : syracuseStep 1723403 = 2585105) B2585105
theorem B1723531 : Blo 1020604 1723531 := bstep (se 1 (by rfl) ⟨1292648, by rfl⟩ : syracuseStep 1723531 = 2585297) B2585297
theorem B3493081 : Blo 1020604 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B1723673 : Blo 1020604 1723673 := bstep (se 2 (by rfl) ⟨646377, by rfl⟩ : syracuseStep 1723673 = 1292755) B1292755
theorem B3886481 : Blo 1020604 3886481 := bstep (se 2 (by rfl) ⟨1457430, by rfl⟩ : syracuseStep 3886481 = 2914861) B2914861
theorem B3689873 : Blo 1020604 3689873 := bstep (se 2 (by rfl) ⟨1383702, by rfl⟩ : syracuseStep 3689873 = 2767405) B2767405
theorem B1723801 : Blo 1020604 1723801 := bstep (se 2 (by rfl) ⟨646425, by rfl⟩ : syracuseStep 1723801 = 1292851) B1292851
theorem B1035895 : Blo 1020604 1035895 := bstep (se 1 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 1035895 = 1553843) B1553843
theorem B3886937 : Blo 1020604 3886937 := bstep (se 2 (by rfl) ⟨1457601, by rfl⟩ : syracuseStep 3886937 = 2915203) B2915203
theorem B18665315 : Blo 1020604 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B2183105 : Blo 1020604 2183105 := bstep (se 2 (by rfl) ⟨818664, by rfl⟩ : syracuseStep 2183105 = 1637329) B1637329
theorem B1724375 : Blo 1020604 1724375 := bstep (se 1 (by rfl) ⟨1293281, by rfl⟩ : syracuseStep 1724375 = 2586563) B2586563
theorem B3887149 : Blo 1020604 3887149 := bstep (se 3 (by rfl) ⟨728840, by rfl⟩ : syracuseStep 3887149 = 1457681) B1457681
theorem B1724503 : Blo 1020604 1724503 := bstep (se 1 (by rfl) ⟨1293377, by rfl⟩ : syracuseStep 1724503 = 2586755) B2586755
theorem B8278337 : Blo 1020604 8278337 := bstep (se 2 (by rfl) ⟨3104376, by rfl⟩ : syracuseStep 8278337 = 6208753) B6208753
theorem B3887453 : Blo 1020604 3887453 := bstep (se 3 (by rfl) ⟨728897, by rfl⟩ : syracuseStep 3887453 = 1457795) B1457795
theorem B12440081 : Blo 1020604 12440081 := bstep (se 2 (by rfl) ⟨4665030, by rfl⟩ : syracuseStep 12440081 = 9330061) B9330061
theorem B3691025 : Blo 1020604 3691025 := bstep (se 2 (by rfl) ⟨1384134, by rfl⟩ : syracuseStep 3691025 = 2768269) B2768269
theorem B1725131 : Blo 1020604 1725131 := bstep (se 1 (by rfl) ⟨1293848, by rfl⟩ : syracuseStep 1725131 = 2587697) B2587697
theorem B1037047 : Blo 1020604 1037047 := bstep (se 1 (by rfl) ⟨777785, by rfl⟩ : syracuseStep 1037047 = 1555571) B1555571
theorem B2183959 : Blo 1020604 2183959 := bstep (se 1 (by rfl) ⟨1637969, by rfl⟩ : syracuseStep 2183959 = 3275939) B3275939
theorem B1725259 : Blo 1020604 1725259 := bstep (se 1 (by rfl) ⟨1293944, by rfl⟩ : syracuseStep 1725259 = 2587889) B2587889
theorem B1725401 : Blo 1020604 1725401 := bstep (se 2 (by rfl) ⟨647025, by rfl⟩ : syracuseStep 1725401 = 1294051) B1294051
theorem B1037323 : Blo 1020604 1037323 := bstep (se 1 (by rfl) ⟨777992, by rfl⟩ : syracuseStep 1037323 = 1555985) B1555985
theorem B1725529 : Blo 1020604 1725529 := bstep (se 2 (by rfl) ⟨647073, by rfl⟩ : syracuseStep 1725529 = 1294147) B1294147
theorem B1037611 : Blo 1020604 1037611 := bstep (se 1 (by rfl) ⟨778208, by rfl⟩ : syracuseStep 1037611 = 1556417) B1556417
theorem B7755101 : Blo 1020604 7755101 := bstep (se 3 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 7755101 = 2908163) B2908163
theorem B4150835 : Blo 1020604 4150835 := bstep (se 1 (by rfl) ⟨3113126, by rfl⟩ : syracuseStep 4150835 = 6226253) B6226253
theorem B2184779 : Blo 1020604 2184779 := bstep (se 1 (by rfl) ⟨1638584, by rfl⟩ : syracuseStep 2184779 = 3277169) B3277169
theorem B1726103 : Blo 1020604 1726103 := bstep (se 1 (by rfl) ⟨1294577, by rfl⟩ : syracuseStep 1726103 = 2589155) B2589155
theorem B1726231 : Blo 1020604 1726231 := bstep (se 1 (by rfl) ⟨1294673, by rfl⟩ : syracuseStep 1726231 = 2589347) B2589347
theorem B5822387 : Blo 1020604 5822387 := bstep (se 1 (by rfl) ⟨4366790, by rfl⟩ : syracuseStep 5822387 = 8733581) B8733581
theorem B1497163 : Blo 1020604 1497163 := bstep (se 1 (by rfl) ⟨1122872, by rfl⟩ : syracuseStep 1497163 = 2245745) B2245745
theorem B1038539 : Blo 1020604 1038539 := bstep (se 1 (by rfl) ⟨778904, by rfl⟩ : syracuseStep 1038539 = 1557809) B1557809
theorem B1726859 : Blo 1020604 1726859 := bstep (se 1 (by rfl) ⟨1295144, by rfl⟩ : syracuseStep 1726859 = 2590289) B2590289
theorem B7363021 : Blo 1020604 7363021 := bstep (se 3 (by rfl) ⟨1380566, by rfl⟩ : syracuseStep 7363021 = 2761133) B2761133
theorem B1726987 : Blo 1020604 1726987 := bstep (se 1 (by rfl) ⟨1295240, by rfl⟩ : syracuseStep 1726987 = 2590481) B2590481
theorem B1727129 : Blo 1020604 1727129 := bstep (se 2 (by rfl) ⟨647673, by rfl⟩ : syracuseStep 1727129 = 1295347) B1295347
theorem B4479709 : Blo 1020604 4479709 := bstep (se 3 (by rfl) ⟨839945, by rfl⟩ : syracuseStep 4479709 = 1679891) B1679891
theorem B1727257 : Blo 1020604 1727257 := bstep (se 2 (by rfl) ⟨647721, by rfl⟩ : syracuseStep 1727257 = 1295443) B1295443
theorem B3890051 : Blo 1020604 3890051 := bstep (se 1 (by rfl) ⟨2917538, by rfl⟩ : syracuseStep 3890051 = 5835077) B5835077
theorem B3890065 : Blo 1020604 3890065 := bstep (se 2 (by rfl) ⟨1458774, by rfl⟩ : syracuseStep 3890065 = 2917549) B2917549
theorem B17685539 : Blo 1020604 17685539 := bstep (se 1 (by rfl) ⟨13264154, by rfl⟩ : syracuseStep 17685539 = 26528309) B26528309
theorem B1531019 : Blo 1020604 1531019 := bstep (se 1 (by rfl) ⟨1148264, by rfl⟩ : syracuseStep 1531019 = 2296529) B2296529
theorem B1531031 : Blo 1020604 1531031 := bstep (se 1 (by rfl) ⟨1148273, by rfl⟩ : syracuseStep 1531031 = 2296547) B2296547
theorem B1531097 : Blo 1020604 1531097 := bstep (se 2 (by rfl) ⟨574161, by rfl⟩ : syracuseStep 1531097 = 1148323) B1148323
theorem B1531211 : Blo 1020604 1531211 := bstep (se 1 (by rfl) ⟨1148408, by rfl⟩ : syracuseStep 1531211 = 2296817) B2296817
theorem B1531223 : Blo 1020604 1531223 := bstep (se 1 (by rfl) ⟨1148417, by rfl⟩ : syracuseStep 1531223 = 2296835) B2296835
theorem B1727831 : Blo 1020604 1727831 := bstep (se 1 (by rfl) ⟨1295873, by rfl⟩ : syracuseStep 1727831 = 2591747) B2591747
theorem B5823845 : Blo 1020604 5823845 := bstep (se 4 (by rfl) ⟨545985, by rfl⟩ : syracuseStep 5823845 = 1091971) B1091971
theorem B1531289 : Blo 1020604 1531289 := bstep (se 2 (by rfl) ⟨574233, by rfl⟩ : syracuseStep 1531289 = 1148467) B1148467
theorem B2907571 : Blo 1020604 2907571 := bstep (se 1 (by rfl) ⟨2180678, by rfl⟩ : syracuseStep 2907571 = 4361357) B4361357
theorem B1727959 : Blo 1020604 1727959 := bstep (se 1 (by rfl) ⟨1295969, by rfl⟩ : syracuseStep 1727959 = 2591939) B2591939
theorem B1531403 : Blo 1020604 1531403 := bstep (se 1 (by rfl) ⟨1148552, by rfl⟩ : syracuseStep 1531403 = 2297105) B2297105
theorem B22076945 : Blo 1020604 22076945 := bstep (se 2 (by rfl) ⟨8278854, by rfl⟩ : syracuseStep 22076945 = 16557709) B16557709
theorem B1531415 : Blo 1020604 1531415 := bstep (se 1 (by rfl) ⟨1148561, by rfl⟩ : syracuseStep 1531415 = 2297123) B2297123
theorem B1531481 : Blo 1020604 1531481 := bstep (se 2 (by rfl) ⟨574305, by rfl⟩ : syracuseStep 1531481 = 1148611) B1148611
theorem B5168771 : Blo 1020604 5168771 := bstep (se 1 (by rfl) ⟨3876578, by rfl⟩ : syracuseStep 5168771 = 7753157) B7753157
theorem B8281777 : Blo 1020604 8281777 := bstep (se 2 (by rfl) ⟨3105666, by rfl⟩ : syracuseStep 8281777 = 6211333) B6211333
theorem B1531595 : Blo 1020604 1531595 := bstep (se 1 (by rfl) ⟨1148696, by rfl⟩ : syracuseStep 1531595 = 2297393) B2297393
theorem B1531607 : Blo 1020604 1531607 := bstep (se 1 (by rfl) ⟨1148705, by rfl⟩ : syracuseStep 1531607 = 2297411) B2297411
theorem B3104477 : Blo 1020604 3104477 := bstep (se 3 (by rfl) ⟨582089, by rfl⟩ : syracuseStep 3104477 = 1164179) B1164179
theorem B1531673 : Blo 1020604 1531673 := bstep (se 2 (by rfl) ⟨574377, by rfl⟩ : syracuseStep 1531673 = 1148755) B1148755
theorem B2187137 : Blo 1020604 2187137 := bstep (se 2 (by rfl) ⟨820176, by rfl⟩ : syracuseStep 2187137 = 1640353) B1640353
theorem B1531787 : Blo 1020604 1531787 := bstep (se 1 (by rfl) ⟨1148840, by rfl⟩ : syracuseStep 1531787 = 2297681) B2297681
theorem B1531799 : Blo 1020604 1531799 := bstep (se 1 (by rfl) ⟨1148849, by rfl⟩ : syracuseStep 1531799 = 2297699) B2297699
theorem B33611699 : Blo 1020604 33611699 := bstep (se 1 (by rfl) ⟨25208774, by rfl⟩ : syracuseStep 33611699 = 50417549) B50417549
theorem B1531865 : Blo 1020604 1531865 := bstep (se 2 (by rfl) ⟨574449, by rfl⟩ : syracuseStep 1531865 = 1148899) B1148899
theorem B5529617 : Blo 1020604 5529617 := bstep (se 2 (by rfl) ⟨2073606, by rfl⟩ : syracuseStep 5529617 = 4147213) B4147213
theorem B1531979 : Blo 1020604 1531979 := bstep (se 1 (by rfl) ⟨1148984, by rfl⟩ : syracuseStep 1531979 = 2297969) B2297969
theorem B1728587 : Blo 1020604 1728587 := bstep (se 1 (by rfl) ⟨1296440, by rfl⟩ : syracuseStep 1728587 = 2592881) B2592881
theorem B1531991 : Blo 1020604 1531991 := bstep (se 1 (by rfl) ⟨1148993, by rfl⟩ : syracuseStep 1531991 = 2297987) B2297987
theorem B1532057 : Blo 1020604 1532057 := bstep (se 2 (by rfl) ⟨574521, by rfl⟩ : syracuseStep 1532057 = 1149043) B1149043
theorem B1728715 : Blo 1020604 1728715 := bstep (se 1 (by rfl) ⟨1296536, by rfl⟩ : syracuseStep 1728715 = 2593073) B2593073
theorem B2187479 : Blo 1020604 2187479 := bstep (se 1 (by rfl) ⟨1640609, by rfl⟩ : syracuseStep 2187479 = 3281219) B3281219
theorem B1532171 : Blo 1020604 1532171 := bstep (se 1 (by rfl) ⟨1149128, by rfl⟩ : syracuseStep 1532171 = 2298257) B2298257
theorem B1532183 : Blo 1020604 1532183 := bstep (se 1 (by rfl) ⟨1149137, by rfl⟩ : syracuseStep 1532183 = 2298275) B2298275
theorem B1532249 : Blo 1020604 1532249 := bstep (se 2 (by rfl) ⟨574593, by rfl⟩ : syracuseStep 1532249 = 1149187) B1149187
theorem B1728857 : Blo 1020604 1728857 := bstep (se 2 (by rfl) ⟨648321, by rfl⟩ : syracuseStep 1728857 = 1296643) B1296643
theorem B10084787 : Blo 1020604 10084787 := bstep (se 1 (by rfl) ⟨7563590, by rfl⟩ : syracuseStep 10084787 = 15127181) B15127181
theorem B2908619 : Blo 1020604 2908619 := bstep (se 1 (by rfl) ⟨2181464, by rfl⟩ : syracuseStep 2908619 = 4362929) B4362929
theorem B1532363 : Blo 1020604 1532363 := bstep (se 1 (by rfl) ⟨1149272, by rfl⟩ : syracuseStep 1532363 = 2298545) B2298545
theorem B1532375 : Blo 1020604 1532375 := bstep (se 1 (by rfl) ⟨1149281, by rfl⟩ : syracuseStep 1532375 = 2298563) B2298563
theorem B1728985 : Blo 1020604 1728985 := bstep (se 2 (by rfl) ⟨648369, by rfl⟩ : syracuseStep 1728985 = 1296739) B1296739
theorem B1532441 : Blo 1020604 1532441 := bstep (se 2 (by rfl) ⟨574665, by rfl⟩ : syracuseStep 1532441 = 1149331) B1149331
theorem B1532555 : Blo 1020604 1532555 := bstep (se 1 (by rfl) ⟨1149416, by rfl⟩ : syracuseStep 1532555 = 2298833) B2298833
theorem B1532567 : Blo 1020604 1532567 := bstep (se 1 (by rfl) ⟨1149425, by rfl⟩ : syracuseStep 1532567 = 2298851) B2298851
theorem B1532633 : Blo 1020604 1532633 := bstep (se 2 (by rfl) ⟨574737, by rfl⟩ : syracuseStep 1532633 = 1149475) B1149475
theorem B2188043 : Blo 1020604 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B1532747 : Blo 1020604 1532747 := bstep (se 1 (by rfl) ⟨1149560, by rfl⟩ : syracuseStep 1532747 = 2299121) B2299121
theorem B1532759 : Blo 1020604 1532759 := bstep (se 1 (by rfl) ⟨1149569, by rfl⟩ : syracuseStep 1532759 = 2299139) B2299139
theorem B19653475 : Blo 1020604 19653475 := bstep (se 1 (by rfl) ⟨14740106, by rfl⟩ : syracuseStep 19653475 = 29480213) B29480213
theorem B1532825 : Blo 1020604 1532825 := bstep (se 2 (by rfl) ⟨574809, by rfl⟩ : syracuseStep 1532825 = 1149619) B1149619
theorem B1532939 : Blo 1020604 1532939 := bstep (se 1 (by rfl) ⟨1149704, by rfl⟩ : syracuseStep 1532939 = 2299409) B2299409
theorem B1532951 : Blo 1020604 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B1533017 : Blo 1020604 1533017 := bstep (se 2 (by rfl) ⟨574881, by rfl⟩ : syracuseStep 1533017 = 1149763) B1149763
theorem B44164277 : Blo 1020604 44164277 := bstep (se 5 (by rfl) ⟨2070200, by rfl⟩ : syracuseStep 44164277 = 4140401) B4140401
theorem B3105985 : Blo 1020604 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B1533131 : Blo 1020604 1533131 := bstep (se 1 (by rfl) ⟨1149848, by rfl⟩ : syracuseStep 1533131 = 2299697) B2299697
theorem B1533143 : Blo 1020604 1533143 := bstep (se 1 (by rfl) ⟨1149857, by rfl⟩ : syracuseStep 1533143 = 2299715) B2299715
theorem B1533209 : Blo 1020604 1533209 := bstep (se 2 (by rfl) ⟨574953, by rfl⟩ : syracuseStep 1533209 = 1149907) B1149907
theorem B1533323 : Blo 1020604 1533323 := bstep (se 1 (by rfl) ⟨1149992, by rfl⟩ : syracuseStep 1533323 = 2299985) B2299985
theorem B1533335 : Blo 1020604 1533335 := bstep (se 1 (by rfl) ⟨1150001, by rfl⟩ : syracuseStep 1533335 = 2300003) B2300003
theorem B1533401 : Blo 1020604 1533401 := bstep (se 2 (by rfl) ⟨575025, by rfl⟩ : syracuseStep 1533401 = 1150051) B1150051
theorem B1533515 : Blo 1020604 1533515 := bstep (se 1 (by rfl) ⟨1150136, by rfl⟩ : syracuseStep 1533515 = 2300273) B2300273
theorem B1533527 : Blo 1020604 1533527 := bstep (se 1 (by rfl) ⟨1150145, by rfl⟩ : syracuseStep 1533527 = 2300291) B2300291
theorem B1533593 : Blo 1020604 1533593 := bstep (se 2 (by rfl) ⟨575097, by rfl⟩ : syracuseStep 1533593 = 1150195) B1150195
theorem B14739185 : Blo 1020604 14739185 := bstep (se 2 (by rfl) ⟨5527194, by rfl⟩ : syracuseStep 14739185 = 11054389) B11054389
theorem B1533707 : Blo 1020604 1533707 := bstep (se 1 (by rfl) ⟨1150280, by rfl⟩ : syracuseStep 1533707 = 2300561) B2300561
theorem B1533719 : Blo 1020604 1533719 := bstep (se 1 (by rfl) ⟨1150289, by rfl⟩ : syracuseStep 1533719 = 2300579) B2300579
theorem B1533785 : Blo 1020604 1533785 := bstep (se 2 (by rfl) ⟨575169, by rfl⟩ : syracuseStep 1533785 = 1150339) B1150339
theorem B33220529 : Blo 1020604 33220529 := bstep (se 2 (by rfl) ⟨12457698, by rfl⟩ : syracuseStep 33220529 = 24915397) B24915397
theorem B1533899 : Blo 1020604 1533899 := bstep (se 1 (by rfl) ⟨1150424, by rfl⟩ : syracuseStep 1533899 = 2300849) B2300849
theorem B1533911 : Blo 1020604 1533911 := bstep (se 1 (by rfl) ⟨1150433, by rfl⟩ : syracuseStep 1533911 = 2300867) B2300867
theorem B1533977 : Blo 1020604 1533977 := bstep (se 2 (by rfl) ⟨575241, by rfl⟩ : syracuseStep 1533977 = 1150483) B1150483
theorem B2910259 : Blo 1020604 2910259 := bstep (se 1 (by rfl) ⟨2182694, by rfl⟩ : syracuseStep 2910259 = 4365389) B4365389
theorem B1534091 : Blo 1020604 1534091 := bstep (se 1 (by rfl) ⟨1150568, by rfl⟩ : syracuseStep 1534091 = 2301137) B2301137
theorem B1534103 : Blo 1020604 1534103 := bstep (se 1 (by rfl) ⟨1150577, by rfl⟩ : syracuseStep 1534103 = 2301155) B2301155
theorem B1534169 : Blo 1020604 1534169 := bstep (se 2 (by rfl) ⟨575313, by rfl⟩ : syracuseStep 1534169 = 1150627) B1150627
theorem B2910487 : Blo 1020604 2910487 := bstep (se 1 (by rfl) ⟨2182865, by rfl⟩ : syracuseStep 2910487 = 4365731) B4365731
theorem B1534283 : Blo 1020604 1534283 := bstep (se 1 (by rfl) ⟨1150712, by rfl⟩ : syracuseStep 1534283 = 2301425) B2301425
theorem B1534295 : Blo 1020604 1534295 := bstep (se 1 (by rfl) ⟨1150721, by rfl⟩ : syracuseStep 1534295 = 2301443) B2301443
theorem B1534361 : Blo 1020604 1534361 := bstep (se 2 (by rfl) ⟨575385, by rfl⟩ : syracuseStep 1534361 = 1150771) B1150771
theorem B1534475 : Blo 1020604 1534475 := bstep (se 1 (by rfl) ⟨1150856, by rfl⟩ : syracuseStep 1534475 = 2301713) B2301713
theorem B1534487 : Blo 1020604 1534487 := bstep (se 1 (by rfl) ⟨1150865, by rfl⟩ : syracuseStep 1534487 = 2301731) B2301731
theorem B1534553 : Blo 1020604 1534553 := bstep (se 2 (by rfl) ⟨575457, by rfl⟩ : syracuseStep 1534553 = 1150915) B1150915
theorem B1534667 : Blo 1020604 1534667 := bstep (se 1 (by rfl) ⟨1151000, by rfl⟩ : syracuseStep 1534667 = 2302001) B2302001
theorem B1534679 : Blo 1020604 1534679 := bstep (se 1 (by rfl) ⟨1151009, by rfl⟩ : syracuseStep 1534679 = 2302019) B2302019
theorem B1534745 : Blo 1020604 1534745 := bstep (se 2 (by rfl) ⟨575529, by rfl⟩ : syracuseStep 1534745 = 1151059) B1151059
theorem B5237569 : Blo 1020604 5237569 := bstep (se 2 (by rfl) ⟨1964088, by rfl⟩ : syracuseStep 5237569 = 3928177) B3928177
theorem B1534859 : Blo 1020604 1534859 := bstep (se 1 (by rfl) ⟨1151144, by rfl⟩ : syracuseStep 1534859 = 2302289) B2302289
theorem B1534871 : Blo 1020604 1534871 := bstep (se 1 (by rfl) ⟨1151153, by rfl⟩ : syracuseStep 1534871 = 2302307) B2302307
theorem B1534937 : Blo 1020604 1534937 := bstep (se 2 (by rfl) ⟨575601, by rfl⟩ : syracuseStep 1534937 = 1151203) B1151203
theorem B1535051 : Blo 1020604 1535051 := bstep (se 1 (by rfl) ⟨1151288, by rfl⟩ : syracuseStep 1535051 = 2302577) B2302577
theorem B1535063 : Blo 1020604 1535063 := bstep (se 1 (by rfl) ⟨1151297, by rfl⟩ : syracuseStep 1535063 = 2302595) B2302595
theorem B1535129 : Blo 1020604 1535129 := bstep (se 2 (by rfl) ⟨575673, by rfl⟩ : syracuseStep 1535129 = 1151347) B1151347
theorem B1535243 : Blo 1020604 1535243 := bstep (se 1 (by rfl) ⟨1151432, by rfl⟩ : syracuseStep 1535243 = 2302865) B2302865
theorem B5172497 : Blo 1020604 5172497 := bstep (se 2 (by rfl) ⟨1939686, by rfl⟩ : syracuseStep 5172497 = 3879373) B3879373
theorem B1535255 : Blo 1020604 1535255 := bstep (se 1 (by rfl) ⟨1151441, by rfl⟩ : syracuseStep 1535255 = 2302883) B2302883
theorem B8416547 : Blo 1020604 8416547 := bstep (se 1 (by rfl) ⟨6312410, by rfl⟩ : syracuseStep 8416547 = 12624821) B12624821
theorem B2583859 : Blo 1020604 2583859 := bstep (se 1 (by rfl) ⟨1937894, by rfl⟩ : syracuseStep 2583859 = 3875789) B3875789
theorem B10513729 : Blo 1020604 10513729 := bstep (se 2 (by rfl) ⟨3942648, by rfl⟩ : syracuseStep 10513729 = 7885297) B7885297
theorem B1535321 : Blo 1020604 1535321 := bstep (se 2 (by rfl) ⟨575745, by rfl⟩ : syracuseStep 1535321 = 1151491) B1151491
theorem B5172659 : Blo 1020604 5172659 := bstep (se 1 (by rfl) ⟨3879494, by rfl⟩ : syracuseStep 5172659 = 7758989) B7758989
theorem B2584001 : Blo 1020604 2584001 := bstep (se 2 (by rfl) ⟨969000, by rfl⟩ : syracuseStep 2584001 = 1938001) B1938001
theorem B1535435 : Blo 1020604 1535435 := bstep (se 1 (by rfl) ⟨1151576, by rfl⟩ : syracuseStep 1535435 = 2303153) B2303153
theorem B1535447 : Blo 1020604 1535447 := bstep (se 1 (by rfl) ⟨1151585, by rfl⟩ : syracuseStep 1535447 = 2303171) B2303171
theorem B7368209 : Blo 1020604 7368209 := bstep (se 2 (by rfl) ⟨2763078, by rfl⟩ : syracuseStep 7368209 = 5526157) B5526157
theorem B1535513 : Blo 1020604 1535513 := bstep (se 2 (by rfl) ⟨575817, by rfl⟩ : syracuseStep 1535513 = 1151635) B1151635
theorem B1535627 : Blo 1020604 1535627 := bstep (se 1 (by rfl) ⟨1151720, by rfl⟩ : syracuseStep 1535627 = 2303441) B2303441
theorem B1535639 : Blo 1020604 1535639 := bstep (se 1 (by rfl) ⟨1151729, by rfl⟩ : syracuseStep 1535639 = 2303459) B2303459
theorem B1535705 : Blo 1020604 1535705 := bstep (se 2 (by rfl) ⟨575889, by rfl⟩ : syracuseStep 1535705 = 1151779) B1151779
theorem B1535819 : Blo 1020604 1535819 := bstep (se 1 (by rfl) ⟨1151864, by rfl⟩ : syracuseStep 1535819 = 2303729) B2303729
theorem B1535831 : Blo 1020604 1535831 := bstep (se 1 (by rfl) ⟨1151873, by rfl⟩ : syracuseStep 1535831 = 2303747) B2303747
theorem B2453399 : Blo 1020604 2453399 := bstep (se 1 (by rfl) ⟨1840049, by rfl⟩ : syracuseStep 2453399 = 3680099) B3680099
theorem B1535897 : Blo 1020604 1535897 := bstep (se 2 (by rfl) ⟨575961, by rfl⟩ : syracuseStep 1535897 = 1151923) B1151923
theorem B1536011 : Blo 1020604 1536011 := bstep (se 1 (by rfl) ⟨1152008, by rfl⟩ : syracuseStep 1536011 = 2304017) B2304017
theorem B1536023 : Blo 1020604 1536023 := bstep (se 1 (by rfl) ⟨1152017, by rfl⟩ : syracuseStep 1536023 = 2304035) B2304035
theorem B2912345 : Blo 1020604 2912345 := bstep (se 2 (by rfl) ⟨1092129, by rfl⟩ : syracuseStep 2912345 = 2184259) B2184259
theorem B1536089 : Blo 1020604 1536089 := bstep (se 2 (by rfl) ⟨576033, by rfl⟩ : syracuseStep 1536089 = 1152067) B1152067
theorem B1536203 : Blo 1020604 1536203 := bstep (se 1 (by rfl) ⟨1152152, by rfl⟩ : syracuseStep 1536203 = 2304305) B2304305
theorem B1536215 : Blo 1020604 1536215 := bstep (se 1 (by rfl) ⟨1152161, by rfl⟩ : syracuseStep 1536215 = 2304323) B2304323
theorem B1536281 : Blo 1020604 1536281 := bstep (se 2 (by rfl) ⟨576105, by rfl⟩ : syracuseStep 1536281 = 1152211) B1152211
theorem B1536395 : Blo 1020604 1536395 := bstep (se 1 (by rfl) ⟨1152296, by rfl⟩ : syracuseStep 1536395 = 2304593) B2304593
theorem B1536407 : Blo 1020604 1536407 := bstep (se 1 (by rfl) ⟨1152305, by rfl⟩ : syracuseStep 1536407 = 2304611) B2304611
theorem B1536473 : Blo 1020604 1536473 := bstep (se 2 (by rfl) ⟨576177, by rfl⟩ : syracuseStep 1536473 = 1152355) B1152355
theorem B1536587 : Blo 1020604 1536587 := bstep (se 1 (by rfl) ⟨1152440, by rfl⟩ : syracuseStep 1536587 = 2304881) B2304881
theorem B1536599 : Blo 1020604 1536599 := bstep (se 1 (by rfl) ⟨1152449, by rfl⟩ : syracuseStep 1536599 = 2304899) B2304899
theorem B1536665 : Blo 1020604 1536665 := bstep (se 2 (by rfl) ⟨576249, by rfl⟩ : syracuseStep 1536665 = 1152499) B1152499
theorem B2585267 : Blo 1020604 2585267 := bstep (se 1 (by rfl) ⟨1938950, by rfl⟩ : syracuseStep 2585267 = 3877901) B3877901
theorem B8745677 : Blo 1020604 8745677 := bstep (se 3 (by rfl) ⟨1639814, by rfl⟩ : syracuseStep 8745677 = 3279629) B3279629
theorem B1536779 : Blo 1020604 1536779 := bstep (se 1 (by rfl) ⟨1152584, by rfl⟩ : syracuseStep 1536779 = 2305169) B2305169
theorem B1536791 : Blo 1020604 1536791 := bstep (se 1 (by rfl) ⟨1152593, by rfl⟩ : syracuseStep 1536791 = 2305187) B2305187
theorem B1536857 : Blo 1020604 1536857 := bstep (se 2 (by rfl) ⟨576321, by rfl⟩ : syracuseStep 1536857 = 1152643) B1152643
theorem B2913175 : Blo 1020604 2913175 := bstep (se 1 (by rfl) ⟨2184881, by rfl⟩ : syracuseStep 2913175 = 4369763) B4369763
theorem B2454475 : Blo 1020604 2454475 := bstep (se 1 (by rfl) ⟨1840856, by rfl⟩ : syracuseStep 2454475 = 3681713) B3681713
theorem B5829677 : Blo 1020604 5829677 := bstep (se 3 (by rfl) ⟨1093064, by rfl⟩ : syracuseStep 5829677 = 2186129) B2186129
theorem B2487475 : Blo 1020604 2487475 := bstep (se 1 (by rfl) ⟨1865606, by rfl⟩ : syracuseStep 2487475 = 3731213) B3731213
theorem B2585803 : Blo 1020604 2585803 := bstep (se 1 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 2585803 = 3878705) B3878705
theorem B11662541 : Blo 1020604 11662541 := bstep (se 3 (by rfl) ⟨2186726, by rfl⟩ : syracuseStep 11662541 = 4373453) B4373453
theorem B5174603 : Blo 1020604 5174603 := bstep (se 1 (by rfl) ⟨3880952, by rfl⟩ : syracuseStep 5174603 = 7761905) B7761905
theorem B2585945 : Blo 1020604 2585945 := bstep (se 2 (by rfl) ⟨969729, by rfl⟩ : syracuseStep 2585945 = 1939459) B1939459
theorem B5600663 : Blo 1020604 5600663 := bstep (se 1 (by rfl) ⟨4200497, by rfl⟩ : syracuseStep 5600663 = 8400995) B8400995
theorem B6551057 : Blo 1020604 6551057 := bstep (se 2 (by rfl) ⟨2456646, by rfl⟩ : syracuseStep 6551057 = 4913293) B4913293
theorem B2913995 : Blo 1020604 2913995 := bstep (se 1 (by rfl) ⟨2185496, by rfl⟩ : syracuseStep 2913995 = 4370993) B4370993
theorem B2455447 : Blo 1020604 2455447 := bstep (se 1 (by rfl) ⟨1841585, by rfl⟩ : syracuseStep 2455447 = 3683171) B3683171
theorem B1964119 : Blo 1020604 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B2586775 : Blo 1020604 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B2455859 : Blo 1020604 2455859 := bstep (se 1 (by rfl) ⟨1841894, by rfl⟩ : syracuseStep 2455859 = 3683789) B3683789
theorem B7371269 : Blo 1020604 7371269 := bstep (se 4 (by rfl) ⟨691056, by rfl⟩ : syracuseStep 7371269 = 1382113) B1382113
theorem B2587211 : Blo 1020604 2587211 := bstep (se 1 (by rfl) ⟨1940408, by rfl⟩ : syracuseStep 2587211 = 3880817) B3880817
theorem B1637015 : Blo 1020604 1637015 := bstep (se 1 (by rfl) ⟨1227761, by rfl⟩ : syracuseStep 1637015 = 2455523) B2455523
theorem B11074421 : Blo 1020604 11074421 := bstep (se 5 (by rfl) ⟨519113, by rfl⟩ : syracuseStep 11074421 = 1038227) B1038227
theorem B2587585 : Blo 1020604 2587585 := bstep (se 2 (by rfl) ⟨970344, by rfl⟩ : syracuseStep 2587585 = 1940689) B1940689
theorem B5176385 : Blo 1020604 5176385 := bstep (se 2 (by rfl) ⟨1941144, by rfl⟩ : syracuseStep 5176385 = 3882289) B3882289
theorem B1309783 : Blo 1020604 1309783 := bstep (se 1 (by rfl) ⟨982337, by rfl⟩ : syracuseStep 1309783 = 1964675) B1964675
theorem B2620633 : Blo 1020604 2620633 := bstep (se 2 (by rfl) ⟨982737, by rfl⟩ : syracuseStep 2620633 = 1965475) B1965475
theorem B9469189 : Blo 1020604 9469189 := bstep (se 4 (by rfl) ⟨887736, by rfl⟩ : syracuseStep 9469189 = 1775473) B1775473
theorem B7372133 : Blo 1020604 7372133 := bstep (se 4 (by rfl) ⟨691137, by rfl⟩ : syracuseStep 7372133 = 1382275) B1382275
theorem B2588183 : Blo 1020604 2588183 := bstep (se 1 (by rfl) ⟨1941137, by rfl⟩ : syracuseStep 2588183 = 3882275) B3882275
theorem B2621207 : Blo 1020604 2621207 := bstep (se 1 (by rfl) ⟨1965905, by rfl⟩ : syracuseStep 2621207 = 3931811) B3931811
theorem B2949067 : Blo 1020604 2949067 := bstep (se 1 (by rfl) ⟨2211800, by rfl⟩ : syracuseStep 2949067 = 4423601) B4423601
theorem B1442107 : Blo 1020604 1442107 := bstep (se 1 (by rfl) ⟨1081580, by rfl⟩ : syracuseStep 1442107 = 2163161) B2163161
theorem B2621783 : Blo 1020604 2621783 := bstep (se 1 (by rfl) ⟨1966337, by rfl⟩ : syracuseStep 2621783 = 3932675) B3932675
theorem B2589043 : Blo 1020604 2589043 := bstep (se 1 (by rfl) ⟨1941782, by rfl⟩ : syracuseStep 2589043 = 3883565) B3883565
theorem B3113417 : Blo 1020604 3113417 := bstep (se 2 (by rfl) ⟨1167531, by rfl⟩ : syracuseStep 3113417 = 2335063) B2335063
theorem B2589185 : Blo 1020604 2589185 := bstep (se 2 (by rfl) ⟨970944, by rfl⟩ : syracuseStep 2589185 = 1941889) B1941889
theorem B2490895 : Blo 1020604 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B2949785 : Blo 1020604 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B11633381 : Blo 1020604 11633381 := bstep (se 4 (by rfl) ⟨1090629, by rfl⟩ : syracuseStep 11633381 = 2181259) B2181259
theorem B3146539 : Blo 1020604 3146539 := bstep (se 1 (by rfl) ⟨2359904, by rfl⟩ : syracuseStep 3146539 = 4719809) B4719809
theorem B5833619 : Blo 1020604 5833619 := bstep (se 1 (by rfl) ⟨4375214, by rfl⟩ : syracuseStep 5833619 = 8750429) B8750429
theorem B3277721 : Blo 1020604 3277721 := bstep (se 2 (by rfl) ⟨1229145, by rfl⟩ : syracuseStep 3277721 = 2458291) B2458291
theorem B2589641 : Blo 1020604 2589641 := bstep (se 2 (by rfl) ⟨971115, by rfl⟩ : syracuseStep 2589641 = 1942231) B1942231
theorem B3277835 : Blo 1020604 3277835 := bstep (se 1 (by rfl) ⟨2458376, by rfl⟩ : syracuseStep 3277835 = 4916753) B4916753
theorem B2589995 : Blo 1020604 2589995 := bstep (se 1 (by rfl) ⟨1942496, by rfl⟩ : syracuseStep 2589995 = 3884993) B3884993
theorem B3278195 : Blo 1020604 3278195 := bstep (se 1 (by rfl) ⟨2458646, by rfl⟩ : syracuseStep 3278195 = 4917293) B4917293
theorem B1967507 : Blo 1020604 1967507 := bstep (se 1 (by rfl) ⟨1475630, by rfl⟩ : syracuseStep 1967507 = 2951261) B2951261
theorem B1148431 : Blo 1020604 1148431 := bstep (se 1 (by rfl) ⟨861323, by rfl⟩ : syracuseStep 1148431 = 1722647) B1722647
theorem B68257349 : Blo 1020604 68257349 := bstep (se 4 (by rfl) ⟨6399126, by rfl⟩ : syracuseStep 68257349 = 12798253) B12798253
theorem B1148935 : Blo 1020604 1148935 := bstep (se 1 (by rfl) ⟨861701, by rfl⟩ : syracuseStep 1148935 = 1723403) B1723403
theorem B1149115 : Blo 1020604 1149115 := bstep (se 1 (by rfl) ⟨861836, by rfl⟩ : syracuseStep 1149115 = 1723673) B1723673
theorem B2590987 : Blo 1020604 2590987 := bstep (se 1 (by rfl) ⟨1943240, by rfl⟩ : syracuseStep 2590987 = 3886481) B3886481
theorem B2459915 : Blo 1020604 2459915 := bstep (se 1 (by rfl) ⟨1844936, by rfl⟩ : syracuseStep 2459915 = 3689873) B3689873
theorem B2591129 : Blo 1020604 2591129 := bstep (se 2 (by rfl) ⟨971673, by rfl⟩ : syracuseStep 2591129 = 1943347) B1943347
theorem B9832889 : Blo 1020604 9832889 := bstep (se 2 (by rfl) ⟨3687333, by rfl⟩ : syracuseStep 9832889 = 7374667) B7374667
theorem B2591291 : Blo 1020604 2591291 := bstep (se 1 (by rfl) ⟨1943468, by rfl⟩ : syracuseStep 2591291 = 3886937) B3886937
theorem B2296439 : Blo 1020604 2296439 := bstep (se 1 (by rfl) ⟨1722329, by rfl⟩ : syracuseStep 2296439 = 3444659) B3444659
theorem B1149583 : Blo 1020604 1149583 := bstep (se 1 (by rfl) ⟨862187, by rfl⟩ : syracuseStep 1149583 = 1724375) B1724375
theorem B49711877 : Blo 1020604 49711877 := bstep (se 4 (by rfl) ⟨4660488, by rfl⟩ : syracuseStep 49711877 = 9320977) B9320977
theorem B2296619 : Blo 1020604 2296619 := bstep (se 1 (by rfl) ⟨1722464, by rfl⟩ : syracuseStep 2296619 = 3444929) B3444929
theorem B2591635 : Blo 1020604 2591635 := bstep (se 1 (by rfl) ⟨1943726, by rfl⟩ : syracuseStep 2591635 = 3887453) B3887453
theorem B8293387 : Blo 1020604 8293387 := bstep (se 1 (by rfl) ⟨6220040, by rfl⟩ : syracuseStep 8293387 = 12440081) B12440081
theorem B2460683 : Blo 1020604 2460683 := bstep (se 1 (by rfl) ⟨1845512, by rfl⟩ : syracuseStep 2460683 = 3691025) B3691025
theorem B2591777 : Blo 1020604 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B14027863 : Blo 1020604 14027863 := bstep (se 1 (by rfl) ⟨10520897, by rfl⟩ : syracuseStep 14027863 = 21041795) B21041795
theorem B1150087 : Blo 1020604 1150087 := bstep (se 1 (by rfl) ⟨862565, by rfl⟩ : syracuseStep 1150087 = 1725131) B1725131
theorem B2296979 : Blo 1020604 2296979 := bstep (se 1 (by rfl) ⟨1722734, by rfl⟩ : syracuseStep 2296979 = 3445469) B3445469
theorem B4918445 : Blo 1020604 4918445 := bstep (se 3 (by rfl) ⟨922208, by rfl⟩ : syracuseStep 4918445 = 1844417) B1844417
theorem B2297033 : Blo 1020604 2297033 := bstep (se 2 (by rfl) ⟨861387, by rfl⟩ : syracuseStep 2297033 = 1722775) B1722775
theorem B1150267 : Blo 1020604 1150267 := bstep (se 1 (by rfl) ⟨862700, by rfl⟩ : syracuseStep 1150267 = 1725401) B1725401
theorem B6983425 : Blo 1020604 6983425 := bstep (se 2 (by rfl) ⟨2618784, by rfl⟩ : syracuseStep 6983425 = 5237569) B5237569
theorem B1150735 : Blo 1020604 1150735 := bstep (se 1 (by rfl) ⟨863051, by rfl⟩ : syracuseStep 1150735 = 1726103) B1726103
theorem B3280655 : Blo 1020604 3280655 := bstep (se 1 (by rfl) ⟨2460491, by rfl⟩ : syracuseStep 3280655 = 4920983) B4920983
theorem B2297735 : Blo 1020604 2297735 := bstep (se 1 (by rfl) ⟨1723301, by rfl⟩ : syracuseStep 2297735 = 3446603) B3446603
theorem B2592769 : Blo 1020604 2592769 := bstep (se 2 (by rfl) ⟨972288, by rfl⟩ : syracuseStep 2592769 = 1944577) B1944577
theorem B2297915 : Blo 1020604 2297915 := bstep (se 1 (by rfl) ⟨1723436, by rfl⟩ : syracuseStep 2297915 = 3446873) B3446873
theorem B2298041 : Blo 1020604 2298041 := bstep (se 2 (by rfl) ⟨861765, by rfl⟩ : syracuseStep 2298041 = 1723531) B1723531
theorem B1151239 : Blo 1020604 1151239 := bstep (se 1 (by rfl) ⟨863429, by rfl⟩ : syracuseStep 1151239 = 1726859) B1726859
theorem B4657441 : Blo 1020604 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B3445145 : Blo 1020604 3445145 := bstep (se 2 (by rfl) ⟨1291929, by rfl⟩ : syracuseStep 3445145 = 2583859) B2583859
theorem B1151419 : Blo 1020604 1151419 := bstep (se 1 (by rfl) ⟨863564, by rfl⟩ : syracuseStep 1151419 = 1727129) B1727129
theorem B2298383 : Blo 1020604 2298383 := bstep (se 1 (by rfl) ⟨1723787, by rfl⟩ : syracuseStep 2298383 = 3447575) B3447575
theorem B7770653 : Blo 1020604 7770653 := bstep (se 3 (by rfl) ⟨1456997, by rfl⟩ : syracuseStep 7770653 = 2913995) B2913995
theorem B2298401 : Blo 1020604 2298401 := bstep (se 2 (by rfl) ⟨861900, by rfl⟩ : syracuseStep 2298401 = 1723801) B1723801
theorem B2593367 : Blo 1020604 2593367 := bstep (se 1 (by rfl) ⟨1945025, by rfl⟩ : syracuseStep 2593367 = 3890051) B3890051
theorem B1577659 : Blo 1020604 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B9310949 : Blo 1020604 9310949 := bstep (se 4 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 9310949 = 1745803) B1745803
theorem B1020679 : Blo 1020604 1020679 := bstep (se 1 (by rfl) ⟨765509, by rfl⟩ : syracuseStep 1020679 = 1531019) B1531019
theorem B1020687 : Blo 1020604 1020687 := bstep (se 1 (by rfl) ⟨765515, by rfl⟩ : syracuseStep 1020687 = 1531031) B1531031
theorem B1020731 : Blo 1020604 1020731 := bstep (se 1 (by rfl) ⟨765548, by rfl⟩ : syracuseStep 1020731 = 1531097) B1531097
theorem B1381193 : Blo 1020604 1381193 := bstep (se 2 (by rfl) ⟨517947, by rfl⟩ : syracuseStep 1381193 = 1035895) B1035895
theorem B2298743 : Blo 1020604 2298743 := bstep (se 1 (by rfl) ⟨1724057, by rfl⟩ : syracuseStep 2298743 = 3448115) B3448115
theorem B1020807 : Blo 1020604 1020807 := bstep (se 1 (by rfl) ⟨765605, by rfl⟩ : syracuseStep 1020807 = 1531211) B1531211
theorem B1020815 : Blo 1020604 1020815 := bstep (se 1 (by rfl) ⟨765611, by rfl⟩ : syracuseStep 1020815 = 1531223) B1531223
theorem B1151887 : Blo 1020604 1151887 := bstep (se 1 (by rfl) ⟨863915, by rfl⟩ : syracuseStep 1151887 = 1727831) B1727831
theorem B1020859 : Blo 1020604 1020859 := bstep (se 1 (by rfl) ⟨765644, by rfl⟩ : syracuseStep 1020859 = 1531289) B1531289
theorem B1020935 : Blo 1020604 1020935 := bstep (se 1 (by rfl) ⟨765701, by rfl⟩ : syracuseStep 1020935 = 1531403) B1531403
theorem B14717963 : Blo 1020604 14717963 := bstep (se 1 (by rfl) ⟨11038472, by rfl⟩ : syracuseStep 14717963 = 22076945) B22076945
theorem B1020943 : Blo 1020604 1020943 := bstep (se 1 (by rfl) ⟨765707, by rfl⟩ : syracuseStep 1020943 = 1531415) B1531415
theorem B10490903 : Blo 1020604 10490903 := bstep (se 1 (by rfl) ⟨7868177, by rfl⟩ : syracuseStep 10490903 = 15736355) B15736355
theorem B2298923 : Blo 1020604 2298923 := bstep (se 1 (by rfl) ⟨1724192, by rfl⟩ : syracuseStep 2298923 = 3448385) B3448385
theorem B1020987 : Blo 1020604 1020987 := bstep (se 1 (by rfl) ⟨765740, by rfl⟩ : syracuseStep 1020987 = 1531481) B1531481
theorem B3445847 : Blo 1020604 3445847 := bstep (se 1 (by rfl) ⟨2584385, by rfl⟩ : syracuseStep 3445847 = 5168771) B5168771
theorem B1971319 : Blo 1020604 1971319 := bstep (se 1 (by rfl) ⟨1478489, by rfl⟩ : syracuseStep 1971319 = 2956979) B2956979
theorem B1021063 : Blo 1020604 1021063 := bstep (se 1 (by rfl) ⟨765797, by rfl⟩ : syracuseStep 1021063 = 1531595) B1531595
theorem B1021071 : Blo 1020604 1021071 := bstep (se 1 (by rfl) ⟨765803, by rfl⟩ : syracuseStep 1021071 = 1531607) B1531607
theorem B2069651 : Blo 1020604 2069651 := bstep (se 1 (by rfl) ⟨1552238, by rfl⟩ : syracuseStep 2069651 = 3104477) B3104477
theorem B1021115 : Blo 1020604 1021115 := bstep (se 1 (by rfl) ⟨765836, by rfl⟩ : syracuseStep 1021115 = 1531673) B1531673
theorem B1021191 : Blo 1020604 1021191 := bstep (se 1 (by rfl) ⟨765893, by rfl⟩ : syracuseStep 1021191 = 1531787) B1531787
theorem B1021199 : Blo 1020604 1021199 := bstep (se 1 (by rfl) ⟨765899, by rfl⟩ : syracuseStep 1021199 = 1531799) B1531799
theorem B1021243 : Blo 1020604 1021243 := bstep (se 1 (by rfl) ⟨765932, by rfl⟩ : syracuseStep 1021243 = 1531865) B1531865
theorem B1021319 : Blo 1020604 1021319 := bstep (se 1 (by rfl) ⟨765989, by rfl⟩ : syracuseStep 1021319 = 1531979) B1531979
theorem B1152391 : Blo 1020604 1152391 := bstep (se 1 (by rfl) ⟨864293, by rfl⟩ : syracuseStep 1152391 = 1728587) B1728587
theorem B1021327 : Blo 1020604 1021327 := bstep (se 1 (by rfl) ⟨765995, by rfl⟩ : syracuseStep 1021327 = 1531991) B1531991
theorem B5182865 : Blo 1020604 5182865 := bstep (se 2 (by rfl) ⟨1943574, by rfl⟩ : syracuseStep 5182865 = 3887149) B3887149
theorem B2299283 : Blo 1020604 2299283 := bstep (se 1 (by rfl) ⟨1724462, by rfl⟩ : syracuseStep 2299283 = 3448925) B3448925
theorem B1021371 : Blo 1020604 1021371 := bstep (se 1 (by rfl) ⟨766028, by rfl⟩ : syracuseStep 1021371 = 1532057) B1532057
theorem B2299337 : Blo 1020604 2299337 := bstep (se 2 (by rfl) ⟨862251, by rfl⟩ : syracuseStep 2299337 = 1724503) B1724503
theorem B1021447 : Blo 1020604 1021447 := bstep (se 1 (by rfl) ⟨766085, by rfl⟩ : syracuseStep 1021447 = 1532171) B1532171
theorem B1021455 : Blo 1020604 1021455 := bstep (se 1 (by rfl) ⟨766091, by rfl⟩ : syracuseStep 1021455 = 1532183) B1532183
theorem B1021499 : Blo 1020604 1021499 := bstep (se 1 (by rfl) ⟨766124, by rfl⟩ : syracuseStep 1021499 = 1532249) B1532249
theorem B1152571 : Blo 1020604 1152571 := bstep (se 1 (by rfl) ⟨864428, by rfl⟩ : syracuseStep 1152571 = 1728857) B1728857
theorem B3446333 : Blo 1020604 3446333 := bstep (se 3 (by rfl) ⟨646187, by rfl⟩ : syracuseStep 3446333 = 1292375) B1292375
theorem B6723191 : Blo 1020604 6723191 := bstep (se 1 (by rfl) ⟨5042393, by rfl⟩ : syracuseStep 6723191 = 10084787) B10084787
theorem B1939079 : Blo 1020604 1939079 := bstep (se 1 (by rfl) ⟨1454309, by rfl⟩ : syracuseStep 1939079 = 2908619) B2908619
theorem B1021575 : Blo 1020604 1021575 := bstep (se 1 (by rfl) ⟨766181, by rfl⟩ : syracuseStep 1021575 = 1532363) B1532363
theorem B1021583 : Blo 1020604 1021583 := bstep (se 1 (by rfl) ⟨766187, by rfl⟩ : syracuseStep 1021583 = 1532375) B1532375
theorem B1021627 : Blo 1020604 1021627 := bstep (se 1 (by rfl) ⟨766220, by rfl⟩ : syracuseStep 1021627 = 1532441) B1532441
theorem B1021703 : Blo 1020604 1021703 := bstep (se 1 (by rfl) ⟨766277, by rfl⟩ : syracuseStep 1021703 = 1532555) B1532555
theorem B1021711 : Blo 1020604 1021711 := bstep (se 1 (by rfl) ⟨766283, by rfl⟩ : syracuseStep 1021711 = 1532567) B1532567
theorem B1021755 : Blo 1020604 1021755 := bstep (se 1 (by rfl) ⟨766316, by rfl⟩ : syracuseStep 1021755 = 1532633) B1532633
theorem B1841015 : Blo 1020604 1841015 := bstep (se 1 (by rfl) ⟨1380761, by rfl⟩ : syracuseStep 1841015 = 2761523) B2761523
theorem B1021831 : Blo 1020604 1021831 := bstep (se 1 (by rfl) ⟨766373, by rfl⟩ : syracuseStep 1021831 = 1532747) B1532747
theorem B1021839 : Blo 1020604 1021839 := bstep (se 1 (by rfl) ⟨766379, by rfl⟩ : syracuseStep 1021839 = 1532759) B1532759
theorem B1021883 : Blo 1020604 1021883 := bstep (se 1 (by rfl) ⟨766412, by rfl⟩ : syracuseStep 1021883 = 1532825) B1532825
theorem B1021959 : Blo 1020604 1021959 := bstep (se 1 (by rfl) ⟨766469, by rfl⟩ : syracuseStep 1021959 = 1532939) B1532939
theorem B1021967 : Blo 1020604 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B1022011 : Blo 1020604 1022011 := bstep (se 1 (by rfl) ⟨766508, by rfl⟩ : syracuseStep 1022011 = 1533017) B1533017
theorem B1022087 : Blo 1020604 1022087 := bstep (se 1 (by rfl) ⟨766565, by rfl⟩ : syracuseStep 1022087 = 1533131) B1533131
theorem B2300039 : Blo 1020604 2300039 := bstep (se 1 (by rfl) ⟨1725029, by rfl⟩ : syracuseStep 2300039 = 3450059) B3450059
theorem B1022095 : Blo 1020604 1022095 := bstep (se 1 (by rfl) ⟨766571, by rfl⟩ : syracuseStep 1022095 = 1533143) B1533143
theorem B1022139 : Blo 1020604 1022139 := bstep (se 1 (by rfl) ⟨766604, by rfl⟩ : syracuseStep 1022139 = 1533209) B1533209
theorem B1022215 : Blo 1020604 1022215 := bstep (se 1 (by rfl) ⟨766661, by rfl⟩ : syracuseStep 1022215 = 1533323) B1533323
theorem B1022223 : Blo 1020604 1022223 := bstep (se 1 (by rfl) ⟨766667, by rfl⟩ : syracuseStep 1022223 = 1533335) B1533335
theorem B1022267 : Blo 1020604 1022267 := bstep (se 1 (by rfl) ⟨766700, by rfl⟩ : syracuseStep 1022267 = 1533401) B1533401
theorem B2300219 : Blo 1020604 2300219 := bstep (se 1 (by rfl) ⟨1725164, by rfl⟩ : syracuseStep 2300219 = 3450329) B3450329
theorem B1382729 : Blo 1020604 1382729 := bstep (se 2 (by rfl) ⟨518523, by rfl⟩ : syracuseStep 1382729 = 1037047) B1037047
theorem B1022343 : Blo 1020604 1022343 := bstep (se 1 (by rfl) ⟨766757, by rfl⟩ : syracuseStep 1022343 = 1533515) B1533515
theorem B1022351 : Blo 1020604 1022351 := bstep (se 1 (by rfl) ⟨766763, by rfl⟩ : syracuseStep 1022351 = 1533527) B1533527
theorem B2300345 : Blo 1020604 2300345 := bstep (se 2 (by rfl) ⟨862629, by rfl⟩ : syracuseStep 2300345 = 1725259) B1725259
theorem B1022395 : Blo 1020604 1022395 := bstep (se 1 (by rfl) ⟨766796, by rfl⟩ : syracuseStep 1022395 = 1533593) B1533593
theorem B1022471 : Blo 1020604 1022471 := bstep (se 1 (by rfl) ⟨766853, by rfl⟩ : syracuseStep 1022471 = 1533707) B1533707
theorem B1022479 : Blo 1020604 1022479 := bstep (se 1 (by rfl) ⟨766859, by rfl⟩ : syracuseStep 1022479 = 1533719) B1533719
theorem B2365967 : Blo 1020604 2365967 := bstep (se 1 (by rfl) ⟨1774475, by rfl⟩ : syracuseStep 2365967 = 3548951) B3548951
theorem B1841707 : Blo 1020604 1841707 := bstep (se 1 (by rfl) ⟨1381280, by rfl⟩ : syracuseStep 1841707 = 2762561) B2762561
theorem B1022523 : Blo 1020604 1022523 := bstep (se 1 (by rfl) ⟨766892, by rfl⟩ : syracuseStep 1022523 = 1533785) B1533785
theorem B1022599 : Blo 1020604 1022599 := bstep (se 1 (by rfl) ⟨766949, by rfl⟩ : syracuseStep 1022599 = 1533899) B1533899
theorem B1022607 : Blo 1020604 1022607 := bstep (se 1 (by rfl) ⟨766955, by rfl⟩ : syracuseStep 1022607 = 1533911) B1533911
theorem B1383097 : Blo 1020604 1383097 := bstep (se 2 (by rfl) ⟨518661, by rfl⟩ : syracuseStep 1383097 = 1037323) B1037323
theorem B1022651 : Blo 1020604 1022651 := bstep (se 1 (by rfl) ⟨766988, by rfl⟩ : syracuseStep 1022651 = 1533977) B1533977
theorem B50502341 : Blo 1020604 50502341 := bstep (se 4 (by rfl) ⟨4734594, by rfl⟩ : syracuseStep 50502341 = 9469189) B9469189
theorem B1022727 : Blo 1020604 1022727 := bstep (se 1 (by rfl) ⟨767045, by rfl⟩ : syracuseStep 1022727 = 1534091) B1534091
theorem B2300687 : Blo 1020604 2300687 := bstep (se 1 (by rfl) ⟨1725515, by rfl⟩ : syracuseStep 2300687 = 3451031) B3451031
theorem B1022735 : Blo 1020604 1022735 := bstep (se 1 (by rfl) ⟨767051, by rfl⟩ : syracuseStep 1022735 = 1534103) B1534103
theorem B2300705 : Blo 1020604 2300705 := bstep (se 2 (by rfl) ⟨862764, by rfl⟩ : syracuseStep 2300705 = 1725529) B1725529
theorem B1022779 : Blo 1020604 1022779 := bstep (se 1 (by rfl) ⟨767084, by rfl⟩ : syracuseStep 1022779 = 1534169) B1534169
theorem B1022855 : Blo 1020604 1022855 := bstep (se 1 (by rfl) ⟨767141, by rfl⟩ : syracuseStep 1022855 = 1534283) B1534283
theorem B1022863 : Blo 1020604 1022863 := bstep (se 1 (by rfl) ⟨767147, by rfl⟩ : syracuseStep 1022863 = 1534295) B1534295
theorem B3316633 : Blo 1020604 3316633 := bstep (se 2 (by rfl) ⟨1243737, by rfl⟩ : syracuseStep 3316633 = 2487475) B2487475
theorem B3447737 : Blo 1020604 3447737 := bstep (se 2 (by rfl) ⟨1292901, by rfl⟩ : syracuseStep 3447737 = 2585803) B2585803
theorem B1022907 : Blo 1020604 1022907 := bstep (se 1 (by rfl) ⟨767180, by rfl⟩ : syracuseStep 1022907 = 1534361) B1534361
theorem B1022983 : Blo 1020604 1022983 := bstep (se 1 (by rfl) ⟨767237, by rfl⟩ : syracuseStep 1022983 = 1534475) B1534475
theorem B1022991 : Blo 1020604 1022991 := bstep (se 1 (by rfl) ⟨767243, by rfl⟩ : syracuseStep 1022991 = 1534487) B1534487
theorem B1383481 : Blo 1020604 1383481 := bstep (se 2 (by rfl) ⟨518805, by rfl⟩ : syracuseStep 1383481 = 1037611) B1037611
theorem B1023035 : Blo 1020604 1023035 := bstep (se 1 (by rfl) ⟨767276, by rfl⟩ : syracuseStep 1023035 = 1534553) B1534553
theorem B4365373 : Blo 1020604 4365373 := bstep (se 3 (by rfl) ⟨818507, by rfl⟩ : syracuseStep 4365373 = 1637015) B1637015
theorem B15735869 : Blo 1020604 15735869 := bstep (se 3 (by rfl) ⟨2950475, by rfl⟩ : syracuseStep 15735869 = 5900951) B5900951
theorem B2301047 : Blo 1020604 2301047 := bstep (se 1 (by rfl) ⟨1725785, by rfl⟩ : syracuseStep 2301047 = 3451571) B3451571
theorem B1023111 : Blo 1020604 1023111 := bstep (se 1 (by rfl) ⟨767333, by rfl⟩ : syracuseStep 1023111 = 1534667) B1534667
theorem B1023119 : Blo 1020604 1023119 := bstep (se 1 (by rfl) ⟨767339, by rfl⟩ : syracuseStep 1023119 = 1534679) B1534679
theorem B1023163 : Blo 1020604 1023163 := bstep (se 1 (by rfl) ⟨767372, by rfl⟩ : syracuseStep 1023163 = 1534745) B1534745
theorem B1023239 : Blo 1020604 1023239 := bstep (se 1 (by rfl) ⟨767429, by rfl⟩ : syracuseStep 1023239 = 1534859) B1534859
theorem B1023247 : Blo 1020604 1023247 := bstep (se 1 (by rfl) ⟨767435, by rfl⟩ : syracuseStep 1023247 = 1534871) B1534871
theorem B2301227 : Blo 1020604 2301227 := bstep (se 1 (by rfl) ⟨1725920, by rfl⟩ : syracuseStep 2301227 = 3451841) B3451841
theorem B1023291 : Blo 1020604 1023291 := bstep (se 1 (by rfl) ⟨767468, by rfl⟩ : syracuseStep 1023291 = 1534937) B1534937
theorem B1023367 : Blo 1020604 1023367 := bstep (se 1 (by rfl) ⟨767525, by rfl⟩ : syracuseStep 1023367 = 1535051) B1535051
theorem B1023375 : Blo 1020604 1023375 := bstep (se 1 (by rfl) ⟨767531, by rfl⟩ : syracuseStep 1023375 = 1535063) B1535063
theorem B1023419 : Blo 1020604 1023419 := bstep (se 1 (by rfl) ⟨767564, by rfl⟩ : syracuseStep 1023419 = 1535129) B1535129
theorem B5184971 : Blo 1020604 5184971 := bstep (se 1 (by rfl) ⟨3888728, by rfl⟩ : syracuseStep 5184971 = 7777457) B7777457
theorem B1023495 : Blo 1020604 1023495 := bstep (se 1 (by rfl) ⟨767621, by rfl⟩ : syracuseStep 1023495 = 1535243) B1535243
theorem B3448331 : Blo 1020604 3448331 := bstep (se 1 (by rfl) ⟨2586248, by rfl⟩ : syracuseStep 3448331 = 5172497) B5172497
theorem B1023503 : Blo 1020604 1023503 := bstep (se 1 (by rfl) ⟨767627, by rfl⟩ : syracuseStep 1023503 = 1535255) B1535255
theorem B5611031 : Blo 1020604 5611031 := bstep (se 1 (by rfl) ⟨4208273, by rfl⟩ : syracuseStep 5611031 = 8416547) B8416547
theorem B4922903 : Blo 1020604 4922903 := bstep (se 1 (by rfl) ⟨3692177, by rfl⟩ : syracuseStep 4922903 = 7384355) B7384355
theorem B1023547 : Blo 1020604 1023547 := bstep (se 1 (by rfl) ⟨767660, by rfl⟩ : syracuseStep 1023547 = 1535321) B1535321
theorem B2760311 : Blo 1020604 2760311 := bstep (se 1 (by rfl) ⟨2070233, by rfl⟩ : syracuseStep 2760311 = 4140467) B4140467
theorem B3448439 : Blo 1020604 3448439 := bstep (se 1 (by rfl) ⟨2586329, by rfl⟩ : syracuseStep 3448439 = 5172659) B5172659
theorem B7872119 : Blo 1020604 7872119 := bstep (se 1 (by rfl) ⟨5904089, by rfl⟩ : syracuseStep 7872119 = 11808179) B11808179
theorem B1023623 : Blo 1020604 1023623 := bstep (se 1 (by rfl) ⟨767717, by rfl⟩ : syracuseStep 1023623 = 1535435) B1535435
theorem B1023631 : Blo 1020604 1023631 := bstep (se 1 (by rfl) ⟨767723, by rfl⟩ : syracuseStep 1023631 = 1535447) B1535447
theorem B2301587 : Blo 1020604 2301587 := bstep (se 1 (by rfl) ⟨1726190, by rfl⟩ : syracuseStep 2301587 = 3452381) B3452381
theorem B1023675 : Blo 1020604 1023675 := bstep (se 1 (by rfl) ⟨767756, by rfl⟩ : syracuseStep 1023675 = 1535513) B1535513
theorem B2301641 : Blo 1020604 2301641 := bstep (se 2 (by rfl) ⟨863115, by rfl⟩ : syracuseStep 2301641 = 1726231) B1726231
theorem B1023751 : Blo 1020604 1023751 := bstep (se 1 (by rfl) ⟨767813, by rfl⟩ : syracuseStep 1023751 = 1535627) B1535627
theorem B1023759 : Blo 1020604 1023759 := bstep (se 1 (by rfl) ⟨767819, by rfl⟩ : syracuseStep 1023759 = 1535639) B1535639
theorem B5185295 : Blo 1020604 5185295 := bstep (se 1 (by rfl) ⟨3888971, by rfl⟩ : syracuseStep 5185295 = 7777943) B7777943
theorem B1023803 : Blo 1020604 1023803 := bstep (se 1 (by rfl) ⟨767852, by rfl⟩ : syracuseStep 1023803 = 1535705) B1535705
theorem B1023879 : Blo 1020604 1023879 := bstep (se 1 (by rfl) ⟨767909, by rfl⟩ : syracuseStep 1023879 = 1535819) B1535819
theorem B1023887 : Blo 1020604 1023887 := bstep (se 1 (by rfl) ⟨767915, by rfl⟩ : syracuseStep 1023887 = 1535831) B1535831
theorem B1843091 : Blo 1020604 1843091 := bstep (se 1 (by rfl) ⟨1382318, by rfl⟩ : syracuseStep 1843091 = 2764637) B2764637
theorem B1023931 : Blo 1020604 1023931 := bstep (se 1 (by rfl) ⟨767948, by rfl⟩ : syracuseStep 1023931 = 1535897) B1535897
theorem B1024007 : Blo 1020604 1024007 := bstep (se 1 (by rfl) ⟨768005, by rfl⟩ : syracuseStep 1024007 = 1536011) B1536011
theorem B1024015 : Blo 1020604 1024015 := bstep (se 1 (by rfl) ⟨768011, by rfl⟩ : syracuseStep 1024015 = 1536023) B1536023
theorem B1941563 : Blo 1020604 1941563 := bstep (se 1 (by rfl) ⟨1456172, by rfl⟩ : syracuseStep 1941563 = 2912345) B2912345
theorem B1024059 : Blo 1020604 1024059 := bstep (se 1 (by rfl) ⟨768044, by rfl⟩ : syracuseStep 1024059 = 1536089) B1536089
theorem B1024135 : Blo 1020604 1024135 := bstep (se 1 (by rfl) ⟨768101, by rfl⟩ : syracuseStep 1024135 = 1536203) B1536203
theorem B1024143 : Blo 1020604 1024143 := bstep (se 1 (by rfl) ⟨768107, by rfl⟩ : syracuseStep 1024143 = 1536215) B1536215
theorem B1024187 : Blo 1020604 1024187 := bstep (se 1 (by rfl) ⟨768140, by rfl⟩ : syracuseStep 1024187 = 1536281) B1536281
theorem B3449033 : Blo 1020604 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B1024263 : Blo 1020604 1024263 := bstep (se 1 (by rfl) ⟨768197, by rfl⟩ : syracuseStep 1024263 = 1536395) B1536395
theorem B1024271 : Blo 1020604 1024271 := bstep (se 1 (by rfl) ⟨768203, by rfl⟩ : syracuseStep 1024271 = 1536407) B1536407
theorem B1024315 : Blo 1020604 1024315 := bstep (se 1 (by rfl) ⟨768236, by rfl⟩ : syracuseStep 1024315 = 1536473) B1536473
theorem B2302343 : Blo 1020604 2302343 := bstep (se 1 (by rfl) ⟨1726757, by rfl⟩ : syracuseStep 2302343 = 3453515) B3453515
theorem B1024391 : Blo 1020604 1024391 := bstep (se 1 (by rfl) ⟨768293, by rfl⟩ : syracuseStep 1024391 = 1536587) B1536587
theorem B1024399 : Blo 1020604 1024399 := bstep (se 1 (by rfl) ⟨768299, by rfl⟩ : syracuseStep 1024399 = 1536599) B1536599
theorem B1024443 : Blo 1020604 1024443 := bstep (se 1 (by rfl) ⟨768332, by rfl⟩ : syracuseStep 1024443 = 1536665) B1536665
theorem B1024519 : Blo 1020604 1024519 := bstep (se 1 (by rfl) ⟨768389, by rfl⟩ : syracuseStep 1024519 = 1536779) B1536779
theorem B1024527 : Blo 1020604 1024527 := bstep (se 1 (by rfl) ⟨768395, by rfl⟩ : syracuseStep 1024527 = 1536791) B1536791
theorem B1942049 : Blo 1020604 1942049 := bstep (se 2 (by rfl) ⟨728268, by rfl⟩ : syracuseStep 1942049 = 1456537) B1456537
theorem B2302523 : Blo 1020604 2302523 := bstep (se 1 (by rfl) ⟨1726892, by rfl⟩ : syracuseStep 2302523 = 3453785) B3453785
theorem B1024571 : Blo 1020604 1024571 := bstep (se 1 (by rfl) ⟨768428, by rfl⟩ : syracuseStep 1024571 = 1536857) B1536857
theorem B2302649 : Blo 1020604 2302649 := bstep (se 2 (by rfl) ⟨863493, by rfl⟩ : syracuseStep 2302649 = 1726987) B1726987
theorem B7775027 : Blo 1020604 7775027 := bstep (se 1 (by rfl) ⟨5831270, by rfl⟩ : syracuseStep 7775027 = 11662541) B11662541
theorem B3449735 : Blo 1020604 3449735 := bstep (se 1 (by rfl) ⟨2587301, by rfl⟩ : syracuseStep 3449735 = 5174603) B5174603
theorem B5972945 : Blo 1020604 5972945 := bstep (se 2 (by rfl) ⟨2239854, by rfl⟩ : syracuseStep 5972945 = 4479709) B4479709
theorem B4367371 : Blo 1020604 4367371 := bstep (se 1 (by rfl) ⟨3275528, by rfl⟩ : syracuseStep 4367371 = 6551057) B6551057
theorem B2302991 : Blo 1020604 2302991 := bstep (se 1 (by rfl) ⟨1727243, by rfl⟩ : syracuseStep 2302991 = 3454487) B3454487
theorem B3941405 : Blo 1020604 3941405 := bstep (se 3 (by rfl) ⟨739013, by rfl⟩ : syracuseStep 3941405 = 1478027) B1478027
theorem B2303009 : Blo 1020604 2303009 := bstep (se 2 (by rfl) ⟨863628, by rfl⟩ : syracuseStep 2303009 = 1727257) B1727257
theorem B5186753 : Blo 1020604 5186753 := bstep (se 2 (by rfl) ⟨1945032, by rfl⟩ : syracuseStep 5186753 = 3890065) B3890065
theorem B3450113 : Blo 1020604 3450113 := bstep (se 2 (by rfl) ⟨1293792, by rfl⟩ : syracuseStep 3450113 = 2587585) B2587585
theorem B11642129 : Blo 1020604 11642129 := bstep (se 2 (by rfl) ⟨4365798, by rfl⟩ : syracuseStep 11642129 = 8731597) B8731597
theorem B6563105 : Blo 1020604 6563105 := bstep (se 2 (by rfl) ⟨2461164, by rfl⟩ : syracuseStep 6563105 = 4922329) B4922329
theorem B2303351 : Blo 1020604 2303351 := bstep (se 1 (by rfl) ⟨1727513, by rfl⟩ : syracuseStep 2303351 = 3455027) B3455027
theorem B7480721 : Blo 1020604 7480721 := bstep (se 2 (by rfl) ⟨2805270, by rfl⟩ : syracuseStep 7480721 = 5610541) B5610541
theorem B1746377 : Blo 1020604 1746377 := bstep (se 2 (by rfl) ⟨654891, by rfl⟩ : syracuseStep 1746377 = 1309783) B1309783
theorem B2303531 : Blo 1020604 2303531 := bstep (se 1 (by rfl) ⟨1727648, by rfl⟩ : syracuseStep 2303531 = 3455297) B3455297
theorem B12461687 : Blo 1020604 12461687 := bstep (se 1 (by rfl) ⟨9346265, by rfl⟩ : syracuseStep 12461687 = 18692531) B18692531
theorem B2303891 : Blo 1020604 2303891 := bstep (se 1 (by rfl) ⟨1727918, by rfl⟩ : syracuseStep 2303891 = 3455837) B3455837
theorem B3876761 : Blo 1020604 3876761 := bstep (se 2 (by rfl) ⟨1453785, by rfl⟩ : syracuseStep 3876761 = 2907571) B2907571
theorem B7382947 : Blo 1020604 7382947 := bstep (se 1 (by rfl) ⟨5537210, by rfl⟩ : syracuseStep 7382947 = 11074421) B11074421
theorem B2303945 : Blo 1020604 2303945 := bstep (se 2 (by rfl) ⟨863979, by rfl⟩ : syracuseStep 2303945 = 1727959) B1727959
theorem B3450923 : Blo 1020604 3450923 := bstep (se 1 (by rfl) ⟨2588192, by rfl⟩ : syracuseStep 3450923 = 5176385) B5176385
theorem B6989885 : Blo 1020604 6989885 := bstep (se 3 (by rfl) ⟨1310603, by rfl⟩ : syracuseStep 6989885 = 2621207) B2621207
theorem B6564077 : Blo 1020604 6564077 := bstep (se 3 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 6564077 = 2461529) B2461529
theorem B1943993 : Blo 1020604 1943993 := bstep (se 2 (by rfl) ⟨728997, by rfl⟩ : syracuseStep 1943993 = 1457995) B1457995
theorem B89631197 : Blo 1020604 89631197 := bstep (se 3 (by rfl) ⟨16805849, by rfl⟩ : syracuseStep 89631197 = 33611699) B33611699
theorem B2304647 : Blo 1020604 2304647 := bstep (se 1 (by rfl) ⟨1728485, by rfl⟩ : syracuseStep 2304647 = 3456971) B3456971
theorem B2304827 : Blo 1020604 2304827 := bstep (se 1 (by rfl) ⟨1728620, by rfl⟩ : syracuseStep 2304827 = 3457241) B3457241
theorem B2304953 : Blo 1020604 2304953 := bstep (se 2 (by rfl) ⟨864357, by rfl⟩ : syracuseStep 2304953 = 1728715) B1728715
theorem B9808901 : Blo 1020604 9808901 := bstep (se 4 (by rfl) ⟨919584, by rfl⟩ : syracuseStep 9808901 = 1839169) B1839169
theorem B2305295 : Blo 1020604 2305295 := bstep (se 1 (by rfl) ⟨1728971, by rfl⟩ : syracuseStep 2305295 = 3457943) B3457943
theorem B2305313 : Blo 1020604 2305313 := bstep (se 2 (by rfl) ⟨864492, by rfl⟩ : syracuseStep 2305313 = 1728985) B1728985
theorem B3452219 : Blo 1020604 3452219 := bstep (se 1 (by rfl) ⟨2589164, by rfl⟩ : syracuseStep 3452219 = 5178329) B5178329
theorem B2993609 : Blo 1020604 2993609 := bstep (se 2 (by rfl) ⟨1122603, by rfl⟩ : syracuseStep 2993609 = 2245207) B2245207
theorem B7876061 : Blo 1020604 7876061 := bstep (se 3 (by rfl) ⟨1476761, by rfl⟩ : syracuseStep 7876061 = 2953523) B2953523
theorem B1945147 : Blo 1020604 1945147 := bstep (se 1 (by rfl) ⟨1458860, by rfl⟩ : syracuseStep 1945147 = 2917721) B2917721
theorem B1552007 : Blo 1020604 1552007 := bstep (se 1 (by rfl) ⟨1164005, by rfl⟩ : syracuseStep 1552007 = 2328011) B2328011
theorem B3452705 : Blo 1020604 3452705 := bstep (se 2 (by rfl) ⟨1294764, by rfl⟩ : syracuseStep 3452705 = 2589529) B2589529
theorem B2764745 : Blo 1020604 2764745 := bstep (se 2 (by rfl) ⟨1036779, by rfl⟩ : syracuseStep 2764745 = 2073559) B2073559
theorem B1552427 : Blo 1020604 1552427 := bstep (se 1 (by rfl) ⟨1164320, by rfl⟩ : syracuseStep 1552427 = 2328641) B2328641
theorem B11645045 : Blo 1020604 11645045 := bstep (se 5 (by rfl) ⟨545861, by rfl⟩ : syracuseStep 11645045 = 1091723) B1091723
theorem B4141313 : Blo 1020604 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B3453299 : Blo 1020604 3453299 := bstep (se 1 (by rfl) ⟨2589974, by rfl⟩ : syracuseStep 3453299 = 5179949) B5179949
theorem B8729207 : Blo 1020604 8729207 := bstep (se 1 (by rfl) ⟨6546905, by rfl⟩ : syracuseStep 8729207 = 13093811) B13093811
theorem B3683357 : Blo 1020604 3683357 := bstep (se 3 (by rfl) ⟨690629, by rfl⟩ : syracuseStep 3683357 = 1381259) B1381259
theorem B4371745 : Blo 1020604 4371745 := bstep (se 2 (by rfl) ⟨1639404, by rfl⟩ : syracuseStep 4371745 = 3278809) B3278809
theorem B1455403 : Blo 1020604 1455403 := bstep (se 1 (by rfl) ⟨1091552, by rfl⟩ : syracuseStep 1455403 = 2183105) B2183105
theorem B5813639 : Blo 1020604 5813639 := bstep (se 1 (by rfl) ⟨4360229, by rfl⟩ : syracuseStep 5813639 = 8720459) B8720459
theorem B3880345 : Blo 1020604 3880345 := bstep (se 2 (by rfl) ⟨1455129, by rfl⟩ : syracuseStep 3880345 = 2910259) B2910259
theorem B1291783 : Blo 1020604 1291783 := bstep (se 1 (by rfl) ⟨968837, by rfl⟩ : syracuseStep 1291783 = 1937675) B1937675
theorem B5518891 : Blo 1020604 5518891 := bstep (se 1 (by rfl) ⟨4139168, by rfl⟩ : syracuseStep 5518891 = 8278337) B8278337
theorem B3880649 : Blo 1020604 3880649 := bstep (se 2 (by rfl) ⟨1455243, by rfl⟩ : syracuseStep 3880649 = 2910487) B2910487
theorem B1292203 : Blo 1020604 1292203 := bstep (se 1 (by rfl) ⟨969152, by rfl⟩ : syracuseStep 1292203 = 1938305) B1938305
theorem B1226767 : Blo 1020604 1226767 := bstep (se 1 (by rfl) ⟨920075, by rfl⟩ : syracuseStep 1226767 = 1840151) B1840151
theorem B1292431 : Blo 1020604 1292431 := bstep (se 1 (by rfl) ⟨969323, by rfl⟩ : syracuseStep 1292431 = 1938647) B1938647
theorem B26589505 : Blo 1020604 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B2767223 : Blo 1020604 2767223 := bstep (se 1 (by rfl) ⟨2075417, by rfl⟩ : syracuseStep 2767223 = 4150835) B4150835
theorem B1227151 : Blo 1020604 1227151 := bstep (se 1 (by rfl) ⟨920363, by rfl⟩ : syracuseStep 1227151 = 1840727) B1840727
theorem B1554859 : Blo 1020604 1554859 := bstep (se 1 (by rfl) ⟨1166144, by rfl⟩ : syracuseStep 1554859 = 2332289) B2332289
theorem B5519801 : Blo 1020604 5519801 := bstep (se 2 (by rfl) ⟨2069925, by rfl⟩ : syracuseStep 5519801 = 4139851) B4139851
theorem B11057593 : Blo 1020604 11057593 := bstep (se 2 (by rfl) ⟨4146597, by rfl⟩ : syracuseStep 11057593 = 8293195) B8293195
theorem B3881591 : Blo 1020604 3881591 := bstep (se 1 (by rfl) ⟨2911193, by rfl⟩ : syracuseStep 3881591 = 5822387) B5822387
theorem B1293175 : Blo 1020604 1293175 := bstep (se 1 (by rfl) ⟨969881, by rfl⟩ : syracuseStep 1293175 = 1939763) B1939763
theorem B3455891 : Blo 1020604 3455891 := bstep (se 1 (by rfl) ⟨2591918, by rfl⟩ : syracuseStep 3455891 = 5183837) B5183837
theorem B1555499 : Blo 1020604 1555499 := bstep (se 1 (by rfl) ⟨1166624, by rfl⟩ : syracuseStep 1555499 = 2333249) B2333249
theorem B5815415 : Blo 1020604 5815415 := bstep (se 1 (by rfl) ⟨4361561, by rfl⟩ : syracuseStep 5815415 = 8723123) B8723123
theorem B1293499 : Blo 1020604 1293499 := bstep (se 1 (by rfl) ⟨970124, by rfl⟩ : syracuseStep 1293499 = 1940249) B1940249
theorem B1555643 : Blo 1020604 1555643 := bstep (se 1 (by rfl) ⟨1166732, by rfl⟩ : syracuseStep 1555643 = 2333465) B2333465
theorem B13286915 : Blo 1020604 13286915 := bstep (se 1 (by rfl) ⟨9965186, by rfl⟩ : syracuseStep 13286915 = 19930373) B19930373
theorem B3882563 : Blo 1020604 3882563 := bstep (se 1 (by rfl) ⟨2911922, by rfl⟩ : syracuseStep 3882563 = 5823845) B5823845
theorem B1293995 : Blo 1020604 1293995 := bstep (se 1 (by rfl) ⟨970496, by rfl⟩ : syracuseStep 1293995 = 1940993) B1940993
theorem B5816123 : Blo 1020604 5816123 := bstep (se 1 (by rfl) ⟨4362092, by rfl⟩ : syracuseStep 5816123 = 8724185) B8724185
theorem B14729035 : Blo 1020604 14729035 := bstep (se 1 (by rfl) ⟨11046776, by rfl⟩ : syracuseStep 14729035 = 22093553) B22093553
theorem B1458091 : Blo 1020604 1458091 := bstep (se 1 (by rfl) ⟨1093568, by rfl⟩ : syracuseStep 1458091 = 2187137) B2187137
theorem B1556471 : Blo 1020604 1556471 := bstep (se 1 (by rfl) ⟨1167353, by rfl⟩ : syracuseStep 1556471 = 2334707) B2334707
theorem B2768897 : Blo 1020604 2768897 := bstep (se 2 (by rfl) ⟨1038336, by rfl⟩ : syracuseStep 2768897 = 2076673) B2076673
theorem B3686411 : Blo 1020604 3686411 := bstep (se 1 (by rfl) ⟨2764808, by rfl⟩ : syracuseStep 3686411 = 5529617) B5529617
theorem B26230877 : Blo 1020604 26230877 := bstep (se 3 (by rfl) ⟨4918289, by rfl⟩ : syracuseStep 26230877 = 9836579) B9836579
theorem B1294471 : Blo 1020604 1294471 := bstep (se 1 (by rfl) ⟨970853, by rfl⟩ : syracuseStep 1294471 = 1941707) B1941707
theorem B1458319 : Blo 1020604 1458319 := bstep (se 1 (by rfl) ⟨1093739, by rfl⟩ : syracuseStep 1458319 = 2187479) B2187479
theorem B3457295 : Blo 1020604 3457295 := bstep (se 1 (by rfl) ⟨2592971, by rfl⟩ : syracuseStep 3457295 = 5185943) B5185943
theorem B1458695 : Blo 1020604 1458695 := bstep (se 1 (by rfl) ⟨1094021, by rfl⟩ : syracuseStep 1458695 = 2188043) B2188043
theorem B3457565 : Blo 1020604 3457565 := bstep (se 3 (by rfl) ⟨648293, by rfl⟩ : syracuseStep 3457565 = 1296587) B1296587
theorem B2769437 : Blo 1020604 2769437 := bstep (se 3 (by rfl) ⟨519269, by rfl⟩ : syracuseStep 2769437 = 1038539) B1038539
theorem B1294967 : Blo 1020604 1294967 := bstep (se 1 (by rfl) ⟨971225, by rfl⟩ : syracuseStep 1294967 = 1942451) B1942451
theorem B1557127 : Blo 1020604 1557127 := bstep (se 1 (by rfl) ⟨1167845, by rfl⟩ : syracuseStep 1557127 = 2335691) B2335691
theorem B1295119 : Blo 1020604 1295119 := bstep (se 1 (by rfl) ⟨971339, by rfl⟩ : syracuseStep 1295119 = 1942679) B1942679
theorem B29442851 : Blo 1020604 29442851 := bstep (se 1 (by rfl) ⟨22082138, by rfl⟩ : syracuseStep 29442851 = 44164277) B44164277
theorem B1295291 : Blo 1020604 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B3884233 : Blo 1020604 3884233 := bstep (se 2 (by rfl) ⟨1456587, by rfl⟩ : syracuseStep 3884233 = 2913175) B2913175
theorem B5817581 : Blo 1020604 5817581 := bstep (se 3 (by rfl) ⟨1090796, by rfl⟩ : syracuseStep 5817581 = 2181593) B2181593
theorem B1296263 : Blo 1020604 1296263 := bstep (se 1 (by rfl) ⟨972197, by rfl⟩ : syracuseStep 1296263 = 1944395) B1944395
theorem B1722667 : Blo 1020604 1722667 := bstep (se 1 (by rfl) ⟨1292000, by rfl⟩ : syracuseStep 1722667 = 2584001) B2584001
theorem B1722809 : Blo 1020604 1722809 := bstep (se 2 (by rfl) ⟨646053, by rfl⟩ : syracuseStep 1722809 = 1292107) B1292107
theorem B5523997 : Blo 1020604 5523997 := bstep (se 3 (by rfl) ⟨1035749, by rfl⟩ : syracuseStep 5523997 = 2071499) B2071499
theorem B9325361 : Blo 1020604 9325361 := bstep (se 2 (by rfl) ⟨3497010, by rfl⟩ : syracuseStep 9325361 = 6994021) B6994021
theorem B1723511 : Blo 1020604 1723511 := bstep (se 1 (by rfl) ⟨1292633, by rfl⟩ : syracuseStep 1723511 = 2585267) B2585267
theorem B9817361 : Blo 1020604 9817361 := bstep (se 2 (by rfl) ⟨3681510, by rfl⟩ : syracuseStep 9817361 = 7363021) B7363021
theorem B3886451 : Blo 1020604 3886451 := bstep (se 1 (by rfl) ⟨2914838, by rfl⟩ : syracuseStep 3886451 = 5829677) B5829677
theorem B16829905 : Blo 1020604 16829905 := bstep (se 2 (by rfl) ⟨6311214, by rfl⟩ : syracuseStep 16829905 = 12622429) B12622429
theorem B1723963 : Blo 1020604 1723963 := bstep (se 1 (by rfl) ⟨1292972, by rfl⟩ : syracuseStep 1723963 = 2585945) B2585945
theorem B5819971 : Blo 1020604 5819971 := bstep (se 1 (by rfl) ⟨4364978, by rfl⟩ : syracuseStep 5819971 = 8729957) B8729957
theorem B1724105 : Blo 1020604 1724105 := bstep (se 2 (by rfl) ⟨646539, by rfl⟩ : syracuseStep 1724105 = 1293079) B1293079
theorem B3494177 : Blo 1020604 3494177 := bstep (se 2 (by rfl) ⟨1310316, by rfl⟩ : syracuseStep 3494177 = 2620633) B2620633
theorem B1724807 : Blo 1020604 1724807 := bstep (se 1 (by rfl) ⟨1293605, by rfl⟩ : syracuseStep 1724807 = 2587211) B2587211
theorem B7754129 : Blo 1020604 7754129 := bstep (se 2 (by rfl) ⟨2907798, by rfl⟩ : syracuseStep 7754129 = 5815597) B5815597
theorem B23646937 : Blo 1020604 23646937 := bstep (se 2 (by rfl) ⟨8867601, by rfl⟩ : syracuseStep 23646937 = 17735203) B17735203
theorem B1725455 : Blo 1020604 1725455 := bstep (se 1 (by rfl) ⟨1294091, by rfl⟩ : syracuseStep 1725455 = 2588183) B2588183
theorem B3888593 : Blo 1020604 3888593 := bstep (se 2 (by rfl) ⟨1458222, by rfl⟩ : syracuseStep 3888593 = 2916445) B2916445
theorem B5821955 : Blo 1020604 5821955 := bstep (se 1 (by rfl) ⟨4366466, by rfl⟩ : syracuseStep 5821955 = 8732933) B8732933
theorem B1725995 : Blo 1020604 1725995 := bstep (se 1 (by rfl) ⟨1294496, by rfl⟩ : syracuseStep 1725995 = 2588993) B2588993
theorem B23025329 : Blo 1020604 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B3888911 : Blo 1020604 3888911 := bstep (se 1 (by rfl) ⟨2916683, by rfl⟩ : syracuseStep 3888911 = 5833367) B5833367
theorem B1726393 : Blo 1020604 1726393 := bstep (se 2 (by rfl) ⟨647397, by rfl⟩ : syracuseStep 1726393 = 1294795) B1294795
theorem B2906455 : Blo 1020604 2906455 := bstep (se 1 (by rfl) ⟨2179841, by rfl⟩ : syracuseStep 2906455 = 4359683) B4359683
theorem B5167475 : Blo 1020604 5167475 := bstep (se 1 (by rfl) ⟨3875606, by rfl⟩ : syracuseStep 5167475 = 7751213) B7751213
theorem B26204633 : Blo 1020604 26204633 := bstep (se 2 (by rfl) ⟨9826737, by rfl⟩ : syracuseStep 26204633 = 19653475) B19653475
theorem B1727095 : Blo 1020604 1727095 := bstep (se 1 (by rfl) ⟨1295321, by rfl⟩ : syracuseStep 1727095 = 2590643) B2590643
theorem B16603841 : Blo 1020604 16603841 := bstep (se 2 (by rfl) ⟨6226440, by rfl⟩ : syracuseStep 16603841 = 12452881) B12452881
theorem B7756559 : Blo 1020604 7756559 := bstep (se 1 (by rfl) ⟨5817419, by rfl⟩ : syracuseStep 7756559 = 11634839) B11634839
theorem B1727291 : Blo 1020604 1727291 := bstep (se 1 (by rfl) ⟨1295468, by rfl⟩ : syracuseStep 1727291 = 2590937) B2590937
theorem B5167961 : Blo 1020604 5167961 := bstep (se 2 (by rfl) ⟨1937985, by rfl⟩ : syracuseStep 5167961 = 3875971) B3875971
theorem B7363595 : Blo 1020604 7363595 := bstep (se 1 (by rfl) ⟨5522696, by rfl⟩ : syracuseStep 7363595 = 11045393) B11045393
theorem B1530923 : Blo 1020604 1530923 := bstep (se 1 (by rfl) ⟨1148192, by rfl⟩ : syracuseStep 1530923 = 2296385) B2296385
theorem B1530953 : Blo 1020604 1530953 := bstep (se 2 (by rfl) ⟨574107, by rfl⟩ : syracuseStep 1530953 = 1148215) B1148215
theorem B1662137 : Blo 1020604 1662137 := bstep (se 2 (by rfl) ⟨623301, by rfl⟩ : syracuseStep 1662137 = 1246603) B1246603
theorem B1531067 : Blo 1020604 1531067 := bstep (se 1 (by rfl) ⟨1148300, by rfl⟩ : syracuseStep 1531067 = 2296601) B2296601
theorem B1727689 : Blo 1020604 1727689 := bstep (se 2 (by rfl) ⟨647883, by rfl⟩ : syracuseStep 1727689 = 1295767) B1295767
theorem B1531127 : Blo 1020604 1531127 := bstep (se 1 (by rfl) ⟨1148345, by rfl⟩ : syracuseStep 1531127 = 2296691) B2296691
theorem B1531151 : Blo 1020604 1531151 := bstep (se 1 (by rfl) ⟨1148363, by rfl⟩ : syracuseStep 1531151 = 2296727) B2296727
theorem B1531193 : Blo 1020604 1531193 := bstep (se 2 (by rfl) ⟨574197, by rfl⟩ : syracuseStep 1531193 = 1148395) B1148395
theorem B1531271 : Blo 1020604 1531271 := bstep (se 1 (by rfl) ⟨1148453, by rfl⟩ : syracuseStep 1531271 = 2296907) B2296907
theorem B1531307 : Blo 1020604 1531307 := bstep (se 1 (by rfl) ⟨1148480, by rfl⟩ : syracuseStep 1531307 = 2296961) B2296961
theorem B1531337 : Blo 1020604 1531337 := bstep (se 2 (by rfl) ⟨574251, by rfl⟩ : syracuseStep 1531337 = 1148503) B1148503
theorem B2186795 : Blo 1020604 2186795 := bstep (se 1 (by rfl) ⟨1640096, by rfl⟩ : syracuseStep 2186795 = 3280193) B3280193
theorem B1531451 : Blo 1020604 1531451 := bstep (se 1 (by rfl) ⟨1148588, by rfl⟩ : syracuseStep 1531451 = 2297177) B2297177
theorem B1531511 : Blo 1020604 1531511 := bstep (se 1 (by rfl) ⟨1148633, by rfl⟩ : syracuseStep 1531511 = 2297267) B2297267
theorem B1531535 : Blo 1020604 1531535 := bstep (se 1 (by rfl) ⟨1148651, by rfl⟩ : syracuseStep 1531535 = 2297303) B2297303
theorem B1531577 : Blo 1020604 1531577 := bstep (se 2 (by rfl) ⟨574341, by rfl⟩ : syracuseStep 1531577 = 1148683) B1148683
theorem B1531655 : Blo 1020604 1531655 := bstep (se 1 (by rfl) ⟨1148741, by rfl⟩ : syracuseStep 1531655 = 2297483) B2297483
theorem B1531691 : Blo 1020604 1531691 := bstep (se 1 (by rfl) ⟨1148768, by rfl⟩ : syracuseStep 1531691 = 2297537) B2297537
theorem B1531721 : Blo 1020604 1531721 := bstep (se 2 (by rfl) ⟨574395, by rfl⟩ : syracuseStep 1531721 = 1148791) B1148791
theorem B5824345 : Blo 1020604 5824345 := bstep (se 2 (by rfl) ⟨2184129, by rfl⟩ : syracuseStep 5824345 = 4368259) B4368259
theorem B1728391 : Blo 1020604 1728391 := bstep (se 1 (by rfl) ⟨1296293, by rfl⟩ : syracuseStep 1728391 = 2592587) B2592587
theorem B2187155 : Blo 1020604 2187155 := bstep (se 1 (by rfl) ⟨1640366, by rfl⟩ : syracuseStep 2187155 = 3280733) B3280733
theorem B12443543 : Blo 1020604 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B1531835 : Blo 1020604 1531835 := bstep (se 1 (by rfl) ⟨1148876, by rfl⟩ : syracuseStep 1531835 = 2297753) B2297753
theorem B1531895 : Blo 1020604 1531895 := bstep (se 1 (by rfl) ⟨1148921, by rfl⟩ : syracuseStep 1531895 = 2297843) B2297843
theorem B1531919 : Blo 1020604 1531919 := bstep (se 1 (by rfl) ⟨1148939, by rfl⟩ : syracuseStep 1531919 = 2297879) B2297879
theorem B1531961 : Blo 1020604 1531961 := bstep (se 2 (by rfl) ⟨574485, by rfl⟩ : syracuseStep 1531961 = 1148971) B1148971
theorem B1532039 : Blo 1020604 1532039 := bstep (se 1 (by rfl) ⟨1149029, by rfl⟩ : syracuseStep 1532039 = 2298059) B2298059
theorem B1532075 : Blo 1020604 1532075 := bstep (se 1 (by rfl) ⟨1149056, by rfl⟩ : syracuseStep 1532075 = 2298113) B2298113
theorem B1532105 : Blo 1020604 1532105 := bstep (se 2 (by rfl) ⟨574539, by rfl⟩ : syracuseStep 1532105 = 1149079) B1149079
theorem B1532219 : Blo 1020604 1532219 := bstep (se 1 (by rfl) ⟨1149164, by rfl⟩ : syracuseStep 1532219 = 2298329) B2298329
theorem B1532279 : Blo 1020604 1532279 := bstep (se 1 (by rfl) ⟨1149209, by rfl⟩ : syracuseStep 1532279 = 2298419) B2298419
theorem B1532303 : Blo 1020604 1532303 := bstep (se 1 (by rfl) ⟨1149227, by rfl⟩ : syracuseStep 1532303 = 2298455) B2298455
theorem B1532345 : Blo 1020604 1532345 := bstep (se 2 (by rfl) ⟨574629, by rfl⟩ : syracuseStep 1532345 = 1149259) B1149259
theorem B14016989 : Blo 1020604 14016989 := bstep (se 3 (by rfl) ⟨2628185, by rfl⟩ : syracuseStep 14016989 = 5256371) B5256371
theorem B1532423 : Blo 1020604 1532423 := bstep (se 1 (by rfl) ⟨1149317, by rfl⟩ : syracuseStep 1532423 = 2298635) B2298635
theorem B1532459 : Blo 1020604 1532459 := bstep (se 1 (by rfl) ⟨1149344, by rfl⟩ : syracuseStep 1532459 = 2298689) B2298689
theorem B1532489 : Blo 1020604 1532489 := bstep (se 2 (by rfl) ⟨574683, by rfl⟩ : syracuseStep 1532489 = 1149367) B1149367
theorem B1532603 : Blo 1020604 1532603 := bstep (se 1 (by rfl) ⟨1149452, by rfl⟩ : syracuseStep 1532603 = 2298905) B2298905
theorem B1532663 : Blo 1020604 1532663 := bstep (se 1 (by rfl) ⟨1149497, by rfl⟩ : syracuseStep 1532663 = 2298995) B2298995
theorem B1532687 : Blo 1020604 1532687 := bstep (se 1 (by rfl) ⟨1149515, by rfl⟩ : syracuseStep 1532687 = 2299031) B2299031
theorem B8741681 : Blo 1020604 8741681 := bstep (se 2 (by rfl) ⟨3278130, by rfl⟩ : syracuseStep 8741681 = 6556261) B6556261
theorem B1532729 : Blo 1020604 1532729 := bstep (se 2 (by rfl) ⟨574773, by rfl⟩ : syracuseStep 1532729 = 1149547) B1149547
theorem B1532807 : Blo 1020604 1532807 := bstep (se 1 (by rfl) ⟨1149605, by rfl⟩ : syracuseStep 1532807 = 2299211) B2299211
theorem B5170067 : Blo 1020604 5170067 := bstep (se 1 (by rfl) ⟨3877550, by rfl⟩ : syracuseStep 5170067 = 7755101) B7755101
theorem B1532843 : Blo 1020604 1532843 := bstep (se 1 (by rfl) ⟨1149632, by rfl⟩ : syracuseStep 1532843 = 2299265) B2299265
theorem B1532873 : Blo 1020604 1532873 := bstep (se 2 (by rfl) ⟨574827, by rfl⟩ : syracuseStep 1532873 = 1149655) B1149655
theorem B1532987 : Blo 1020604 1532987 := bstep (se 1 (by rfl) ⟨1149740, by rfl⟩ : syracuseStep 1532987 = 2299481) B2299481
theorem B2909303 : Blo 1020604 2909303 := bstep (se 1 (by rfl) ⟨2181977, by rfl⟩ : syracuseStep 2909303 = 4363955) B4363955
theorem B1533047 : Blo 1020604 1533047 := bstep (se 1 (by rfl) ⟨1149785, by rfl⟩ : syracuseStep 1533047 = 2299571) B2299571
theorem B20997251 : Blo 1020604 20997251 := bstep (se 1 (by rfl) ⟨15747938, by rfl⟩ : syracuseStep 20997251 = 31495877) B31495877
theorem B1533071 : Blo 1020604 1533071 := bstep (se 1 (by rfl) ⟨1149803, by rfl⟩ : syracuseStep 1533071 = 2299607) B2299607
theorem B1533113 : Blo 1020604 1533113 := bstep (se 2 (by rfl) ⟨574917, by rfl⟩ : syracuseStep 1533113 = 1149835) B1149835
theorem B1533191 : Blo 1020604 1533191 := bstep (se 1 (by rfl) ⟨1149893, by rfl⟩ : syracuseStep 1533191 = 2299787) B2299787
theorem B1533227 : Blo 1020604 1533227 := bstep (se 1 (by rfl) ⟨1149920, by rfl⟩ : syracuseStep 1533227 = 2299841) B2299841
theorem B1533257 : Blo 1020604 1533257 := bstep (se 2 (by rfl) ⟨574971, by rfl⟩ : syracuseStep 1533257 = 1149943) B1149943
theorem B11986321 : Blo 1020604 11986321 := bstep (se 2 (by rfl) ⟨4494870, by rfl⟩ : syracuseStep 11986321 = 8989741) B8989741
theorem B8742329 : Blo 1020604 8742329 := bstep (se 2 (by rfl) ⟨3278373, by rfl⟩ : syracuseStep 8742329 = 6556747) B6556747
theorem B1533371 : Blo 1020604 1533371 := bstep (se 1 (by rfl) ⟨1150028, by rfl⟩ : syracuseStep 1533371 = 2300057) B2300057
theorem B1533431 : Blo 1020604 1533431 := bstep (se 1 (by rfl) ⟨1150073, by rfl⟩ : syracuseStep 1533431 = 2300147) B2300147
theorem B1533455 : Blo 1020604 1533455 := bstep (se 1 (by rfl) ⟨1150091, by rfl⟩ : syracuseStep 1533455 = 2300183) B2300183
theorem B5826077 : Blo 1020604 5826077 := bstep (se 3 (by rfl) ⟨1092389, by rfl⟩ : syracuseStep 5826077 = 2184779) B2184779
theorem B1533497 : Blo 1020604 1533497 := bstep (se 2 (by rfl) ⟨575061, by rfl⟩ : syracuseStep 1533497 = 1150123) B1150123
theorem B1533575 : Blo 1020604 1533575 := bstep (se 1 (by rfl) ⟨1150181, by rfl⟩ : syracuseStep 1533575 = 2300363) B2300363
theorem B1533611 : Blo 1020604 1533611 := bstep (se 1 (by rfl) ⟨1150208, by rfl⟩ : syracuseStep 1533611 = 2300417) B2300417
theorem B1533641 : Blo 1020604 1533641 := bstep (se 2 (by rfl) ⟨575115, by rfl⟩ : syracuseStep 1533641 = 1150231) B1150231
theorem B14018305 : Blo 1020604 14018305 := bstep (se 2 (by rfl) ⟨5256864, by rfl⟩ : syracuseStep 14018305 = 10513729) B10513729
theorem B1533755 : Blo 1020604 1533755 := bstep (se 1 (by rfl) ⟨1150316, by rfl⟩ : syracuseStep 1533755 = 2300633) B2300633
theorem B1533815 : Blo 1020604 1533815 := bstep (se 1 (by rfl) ⟨1150361, by rfl⟩ : syracuseStep 1533815 = 2300723) B2300723
theorem B1533839 : Blo 1020604 1533839 := bstep (se 1 (by rfl) ⟨1150379, by rfl⟩ : syracuseStep 1533839 = 2300759) B2300759
theorem B1533881 : Blo 1020604 1533881 := bstep (se 2 (by rfl) ⟨575205, by rfl⟩ : syracuseStep 1533881 = 1150411) B1150411
theorem B1533959 : Blo 1020604 1533959 := bstep (se 1 (by rfl) ⟨1150469, by rfl⟩ : syracuseStep 1533959 = 2300939) B2300939
theorem B11790359 : Blo 1020604 11790359 := bstep (se 1 (by rfl) ⟨8842769, by rfl⟩ : syracuseStep 11790359 = 17685539) B17685539
theorem B1533995 : Blo 1020604 1533995 := bstep (se 1 (by rfl) ⟨1150496, by rfl⟩ : syracuseStep 1533995 = 2300993) B2300993
theorem B1534025 : Blo 1020604 1534025 := bstep (se 2 (by rfl) ⟨575259, by rfl⟩ : syracuseStep 1534025 = 1150519) B1150519
theorem B1534139 : Blo 1020604 1534139 := bstep (se 1 (by rfl) ⟨1150604, by rfl⟩ : syracuseStep 1534139 = 2301209) B2301209
theorem B5826761 : Blo 1020604 5826761 := bstep (se 2 (by rfl) ⟨2185035, by rfl⟩ : syracuseStep 5826761 = 4370071) B4370071
theorem B1534199 : Blo 1020604 1534199 := bstep (se 1 (by rfl) ⟨1150649, by rfl⟩ : syracuseStep 1534199 = 2301299) B2301299
theorem B1534223 : Blo 1020604 1534223 := bstep (se 1 (by rfl) ⟨1150667, by rfl⟩ : syracuseStep 1534223 = 2301335) B2301335
theorem B1534265 : Blo 1020604 1534265 := bstep (se 2 (by rfl) ⟨575349, by rfl⟩ : syracuseStep 1534265 = 1150699) B1150699
theorem B1534343 : Blo 1020604 1534343 := bstep (se 1 (by rfl) ⟨1150757, by rfl⟩ : syracuseStep 1534343 = 2301515) B2301515
theorem B1534379 : Blo 1020604 1534379 := bstep (se 1 (by rfl) ⟨1150784, by rfl⟩ : syracuseStep 1534379 = 2301569) B2301569
theorem B1534409 : Blo 1020604 1534409 := bstep (se 2 (by rfl) ⟨575403, by rfl⟩ : syracuseStep 1534409 = 1150807) B1150807
theorem B1534523 : Blo 1020604 1534523 := bstep (se 1 (by rfl) ⟨1150892, by rfl⟩ : syracuseStep 1534523 = 2301785) B2301785
theorem B1534583 : Blo 1020604 1534583 := bstep (se 1 (by rfl) ⟨1150937, by rfl⟩ : syracuseStep 1534583 = 2301875) B2301875
theorem B1534607 : Blo 1020604 1534607 := bstep (se 1 (by rfl) ⟨1150955, by rfl⟩ : syracuseStep 1534607 = 2301911) B2301911
theorem B1534649 : Blo 1020604 1534649 := bstep (se 2 (by rfl) ⟨575493, by rfl⟩ : syracuseStep 1534649 = 1150987) B1150987
theorem B1534727 : Blo 1020604 1534727 := bstep (se 1 (by rfl) ⟨1151045, by rfl⟩ : syracuseStep 1534727 = 2302091) B2302091
theorem B1534763 : Blo 1020604 1534763 := bstep (se 1 (by rfl) ⟨1151072, by rfl⟩ : syracuseStep 1534763 = 2302145) B2302145
theorem B1534793 : Blo 1020604 1534793 := bstep (se 2 (by rfl) ⟨575547, by rfl⟩ : syracuseStep 1534793 = 1151095) B1151095
theorem B1534907 : Blo 1020604 1534907 := bstep (se 1 (by rfl) ⟨1151180, by rfl⟩ : syracuseStep 1534907 = 2302361) B2302361
theorem B1534967 : Blo 1020604 1534967 := bstep (se 1 (by rfl) ⟨1151225, by rfl⟩ : syracuseStep 1534967 = 2302451) B2302451
theorem B1534991 : Blo 1020604 1534991 := bstep (se 1 (by rfl) ⟨1151243, by rfl⟩ : syracuseStep 1534991 = 2302487) B2302487
theorem B1535033 : Blo 1020604 1535033 := bstep (se 2 (by rfl) ⟨575637, by rfl⟩ : syracuseStep 1535033 = 1151275) B1151275
theorem B1535111 : Blo 1020604 1535111 := bstep (se 1 (by rfl) ⟨1151333, by rfl⟩ : syracuseStep 1535111 = 2302667) B2302667
theorem B1535147 : Blo 1020604 1535147 := bstep (se 1 (by rfl) ⟨1151360, by rfl⟩ : syracuseStep 1535147 = 2302721) B2302721
theorem B1535177 : Blo 1020604 1535177 := bstep (se 2 (by rfl) ⟨575691, by rfl⟩ : syracuseStep 1535177 = 1151383) B1151383
theorem B2583809 : Blo 1020604 2583809 := bstep (se 2 (by rfl) ⟨968928, by rfl⟩ : syracuseStep 2583809 = 1937857) B1937857
theorem B1535291 : Blo 1020604 1535291 := bstep (se 1 (by rfl) ⟨1151468, by rfl⟩ : syracuseStep 1535291 = 2302937) B2302937
theorem B1535351 : Blo 1020604 1535351 := bstep (se 1 (by rfl) ⟨1151513, by rfl⟩ : syracuseStep 1535351 = 2303027) B2303027
theorem B1535375 : Blo 1020604 1535375 := bstep (se 1 (by rfl) ⟨1151531, by rfl⟩ : syracuseStep 1535375 = 2303063) B2303063
theorem B4910489 : Blo 1020604 4910489 := bstep (se 2 (by rfl) ⟨1841433, by rfl⟩ : syracuseStep 4910489 = 3682867) B3682867
theorem B1535417 : Blo 1020604 1535417 := bstep (se 2 (by rfl) ⟨575781, by rfl⟩ : syracuseStep 1535417 = 1151563) B1151563
theorem B6548957 : Blo 1020604 6548957 := bstep (se 3 (by rfl) ⟨1227929, by rfl⟩ : syracuseStep 6548957 = 2455859) B2455859
theorem B1535495 : Blo 1020604 1535495 := bstep (se 1 (by rfl) ⟨1151621, by rfl⟩ : syracuseStep 1535495 = 2303243) B2303243
theorem B1535531 : Blo 1020604 1535531 := bstep (se 1 (by rfl) ⟨1151648, by rfl⟩ : syracuseStep 1535531 = 2303297) B2303297
theorem B1535561 : Blo 1020604 1535561 := bstep (se 2 (by rfl) ⟨575835, by rfl⟩ : syracuseStep 1535561 = 1151671) B1151671
theorem B2584183 : Blo 1020604 2584183 := bstep (se 1 (by rfl) ⟨1938137, by rfl⟩ : syracuseStep 2584183 = 3876275) B3876275
theorem B2453111 : Blo 1020604 2453111 := bstep (se 1 (by rfl) ⟨1839833, by rfl⟩ : syracuseStep 2453111 = 3679667) B3679667
theorem B1535675 : Blo 1020604 1535675 := bstep (se 1 (by rfl) ⟨1151756, by rfl⟩ : syracuseStep 1535675 = 2303513) B2303513
theorem B2911945 : Blo 1020604 2911945 := bstep (se 2 (by rfl) ⟨1091979, by rfl⟩ : syracuseStep 2911945 = 2183959) B2183959
theorem B1535735 : Blo 1020604 1535735 := bstep (se 1 (by rfl) ⟨1151801, by rfl⟩ : syracuseStep 1535735 = 2303603) B2303603
theorem B8744719 : Blo 1020604 8744719 := bstep (se 1 (by rfl) ⟨6558539, by rfl⟩ : syracuseStep 8744719 = 13117079) B13117079
theorem B1535759 : Blo 1020604 1535759 := bstep (se 1 (by rfl) ⟨1151819, by rfl⟩ : syracuseStep 1535759 = 2303639) B2303639
theorem B1535801 : Blo 1020604 1535801 := bstep (se 2 (by rfl) ⟨575925, by rfl⟩ : syracuseStep 1535801 = 1151851) B1151851
theorem B9826123 : Blo 1020604 9826123 := bstep (se 1 (by rfl) ⟨7369592, by rfl⟩ : syracuseStep 9826123 = 14739185) B14739185
theorem B1535879 : Blo 1020604 1535879 := bstep (se 1 (by rfl) ⟨1151909, by rfl⟩ : syracuseStep 1535879 = 2303819) B2303819
theorem B5173145 : Blo 1020604 5173145 := bstep (se 2 (by rfl) ⟨1939929, by rfl⟩ : syracuseStep 5173145 = 3879859) B3879859
theorem B1535915 : Blo 1020604 1535915 := bstep (se 1 (by rfl) ⟨1151936, by rfl⟩ : syracuseStep 1535915 = 2303873) B2303873
theorem B3272633 : Blo 1020604 3272633 := bstep (se 2 (by rfl) ⟨1227237, by rfl⟩ : syracuseStep 3272633 = 2454475) B2454475
theorem B5828537 : Blo 1020604 5828537 := bstep (se 2 (by rfl) ⟨2185701, by rfl⟩ : syracuseStep 5828537 = 4371403) B4371403
theorem B1535945 : Blo 1020604 1535945 := bstep (se 2 (by rfl) ⟨575979, by rfl⟩ : syracuseStep 1535945 = 1151959) B1151959
theorem B22147019 : Blo 1020604 22147019 := bstep (se 1 (by rfl) ⟨16610264, by rfl⟩ : syracuseStep 22147019 = 33220529) B33220529
theorem B2584619 : Blo 1020604 2584619 := bstep (se 1 (by rfl) ⟨1938464, by rfl⟩ : syracuseStep 2584619 = 3876929) B3876929
theorem B1536059 : Blo 1020604 1536059 := bstep (se 1 (by rfl) ⟨1152044, by rfl⟩ : syracuseStep 1536059 = 2304089) B2304089
theorem B11038781 : Blo 1020604 11038781 := bstep (se 3 (by rfl) ⟨2069771, by rfl⟩ : syracuseStep 11038781 = 4139543) B4139543
theorem B1536119 : Blo 1020604 1536119 := bstep (se 1 (by rfl) ⟨1152089, by rfl⟩ : syracuseStep 1536119 = 2304179) B2304179
theorem B1536143 : Blo 1020604 1536143 := bstep (se 1 (by rfl) ⟨1152107, by rfl⟩ : syracuseStep 1536143 = 2304215) B2304215
theorem B1536185 : Blo 1020604 1536185 := bstep (se 2 (by rfl) ⟨576069, by rfl⟩ : syracuseStep 1536185 = 1152139) B1152139
theorem B1536263 : Blo 1020604 1536263 := bstep (se 1 (by rfl) ⟨1152197, by rfl⟩ : syracuseStep 1536263 = 2304395) B2304395
theorem B1536299 : Blo 1020604 1536299 := bstep (se 1 (by rfl) ⟨1152224, by rfl⟩ : syracuseStep 1536299 = 2304449) B2304449
theorem B1536329 : Blo 1020604 1536329 := bstep (se 2 (by rfl) ⟨576123, by rfl⟩ : syracuseStep 1536329 = 1152247) B1152247
theorem B16576913 : Blo 1020604 16576913 := bstep (se 2 (by rfl) ⟨6216342, by rfl⟩ : syracuseStep 16576913 = 12432685) B12432685
theorem B1536443 : Blo 1020604 1536443 := bstep (se 1 (by rfl) ⟨1152332, by rfl⟩ : syracuseStep 1536443 = 2304665) B2304665
theorem B1536503 : Blo 1020604 1536503 := bstep (se 1 (by rfl) ⟨1152377, by rfl⟩ : syracuseStep 1536503 = 2304755) B2304755
theorem B3109391 : Blo 1020604 3109391 := bstep (se 1 (by rfl) ⟨2332043, by rfl⟩ : syracuseStep 3109391 = 4664087) B4664087
theorem B1536527 : Blo 1020604 1536527 := bstep (se 1 (by rfl) ⟨1152395, by rfl⟩ : syracuseStep 1536527 = 2304791) B2304791
theorem B12415517 : Blo 1020604 12415517 := bstep (se 3 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 12415517 = 4655819) B4655819
theorem B1536569 : Blo 1020604 1536569 := bstep (se 2 (by rfl) ⟨576213, by rfl⟩ : syracuseStep 1536569 = 1152427) B1152427
theorem B1536647 : Blo 1020604 1536647 := bstep (se 1 (by rfl) ⟨1152485, by rfl⟩ : syracuseStep 1536647 = 2304971) B2304971
theorem B1536683 : Blo 1020604 1536683 := bstep (se 1 (by rfl) ⟨1152512, by rfl⟩ : syracuseStep 1536683 = 2305025) B2305025
theorem B1536713 : Blo 1020604 1536713 := bstep (se 2 (by rfl) ⟨576267, by rfl⟩ : syracuseStep 1536713 = 1152535) B1152535
theorem B1536827 : Blo 1020604 1536827 := bstep (se 1 (by rfl) ⟨1152620, by rfl⟩ : syracuseStep 1536827 = 2305241) B2305241
theorem B2585459 : Blo 1020604 2585459 := bstep (se 1 (by rfl) ⟨1939094, by rfl⟩ : syracuseStep 2585459 = 3878189) B3878189
theorem B1536887 : Blo 1020604 1536887 := bstep (se 1 (by rfl) ⟨1152665, by rfl⟩ : syracuseStep 1536887 = 2305331) B2305331
theorem B2585479 : Blo 1020604 2585479 := bstep (se 1 (by rfl) ⟨1939109, by rfl⟩ : syracuseStep 2585479 = 3878219) B3878219
theorem B4912139 : Blo 1020604 4912139 := bstep (se 1 (by rfl) ⟨3684104, by rfl⟩ : syracuseStep 4912139 = 7368209) B7368209
theorem B2585753 : Blo 1020604 2585753 := bstep (se 2 (by rfl) ⟨969657, by rfl⟩ : syracuseStep 2585753 = 1939315) B1939315
theorem B3273929 : Blo 1020604 3273929 := bstep (se 2 (by rfl) ⟨1227723, by rfl⟩ : syracuseStep 3273929 = 2455447) B2455447
theorem B1635599 : Blo 1020604 1635599 := bstep (se 1 (by rfl) ⟨1226699, by rfl⟩ : syracuseStep 1635599 = 2453399) B2453399
theorem B2585915 : Blo 1020604 2585915 := bstep (se 1 (by rfl) ⟨1939436, by rfl⟩ : syracuseStep 2585915 = 3878873) B3878873
theorem B1996217 : Blo 1020604 1996217 := bstep (se 2 (by rfl) ⟨748581, by rfl⟩ : syracuseStep 1996217 = 1497163) B1497163
theorem B2618825 : Blo 1020604 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B2913803 : Blo 1020604 2913803 := bstep (se 1 (by rfl) ⟨2185352, by rfl⟩ : syracuseStep 2913803 = 4370705) B4370705
theorem B2586127 : Blo 1020604 2586127 := bstep (se 1 (by rfl) ⟨1939595, by rfl⟩ : syracuseStep 2586127 = 3879191) B3879191
theorem B2586401 : Blo 1020604 2586401 := bstep (se 2 (by rfl) ⟨969900, by rfl⟩ : syracuseStep 2586401 = 1939801) B1939801
theorem B5830451 : Blo 1020604 5830451 := bstep (se 1 (by rfl) ⟨4372838, by rfl⟩ : syracuseStep 5830451 = 8745677) B8745677
theorem B4421699 : Blo 1020604 4421699 := bstep (se 1 (by rfl) ⟨3316274, by rfl⟩ : syracuseStep 4421699 = 6632549) B6632549
theorem B2914451 : Blo 1020604 2914451 := bstep (se 1 (by rfl) ⟨2185838, by rfl⟩ : syracuseStep 2914451 = 4371677) B4371677
theorem B2455705 : Blo 1020604 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B3733775 : Blo 1020604 3733775 := bstep (se 1 (by rfl) ⟨2800331, by rfl⟩ : syracuseStep 3733775 = 5600663) B5600663
theorem B2914679 : Blo 1020604 2914679 := bstep (se 1 (by rfl) ⟨2186009, by rfl⟩ : syracuseStep 2914679 = 4372019) B4372019
theorem B24869267 : Blo 1020604 24869267 := bstep (se 1 (by rfl) ⟨18651950, by rfl⟩ : syracuseStep 24869267 = 37303901) B37303901
theorem B5175737 : Blo 1020604 5175737 := bstep (se 2 (by rfl) ⟨1940901, by rfl⟩ : syracuseStep 5175737 = 3881803) B3881803
theorem B3111577 : Blo 1020604 3111577 := bstep (se 2 (by rfl) ⟨1166841, by rfl⟩ : syracuseStep 3111577 = 2333683) B2333683
theorem B2587403 : Blo 1020604 2587403 := bstep (se 1 (by rfl) ⟨1940552, by rfl⟩ : syracuseStep 2587403 = 3881105) B3881105
theorem B7371557 : Blo 1020604 7371557 := bstep (se 4 (by rfl) ⟨691083, by rfl⟩ : syracuseStep 7371557 = 1382167) B1382167
theorem B4914179 : Blo 1020604 4914179 := bstep (se 1 (by rfl) ⟨3685634, by rfl⟩ : syracuseStep 4914179 = 7371269) B7371269
theorem B5831909 : Blo 1020604 5831909 := bstep (se 4 (by rfl) ⟨546741, by rfl⟩ : syracuseStep 5831909 = 1093483) B1093483
theorem B7765307 : Blo 1020604 7765307 := bstep (se 1 (by rfl) ⟨5823980, by rfl⟩ : syracuseStep 7765307 = 11647961) B11647961
theorem B2588051 : Blo 1020604 2588051 := bstep (se 1 (by rfl) ⟨1941038, by rfl⟩ : syracuseStep 2588051 = 3882077) B3882077
theorem B11042369 : Blo 1020604 11042369 := bstep (se 2 (by rfl) ⟨4140888, by rfl⟩ : syracuseStep 11042369 = 8281777) B8281777
theorem B4914755 : Blo 1020604 4914755 := bstep (se 1 (by rfl) ⟨3686066, by rfl⟩ : syracuseStep 4914755 = 7372133) B7372133
theorem B2588345 : Blo 1020604 2588345 := bstep (se 2 (by rfl) ⟨970629, by rfl⟩ : syracuseStep 2588345 = 1941259) B1941259
theorem B5177033 : Blo 1020604 5177033 := bstep (se 2 (by rfl) ⟨1941387, by rfl⟩ : syracuseStep 5177033 = 3882775) B3882775
theorem B15728357 : Blo 1020604 15728357 := bstep (se 4 (by rfl) ⟨1474533, by rfl⟩ : syracuseStep 15728357 = 2949067) B2949067
theorem B5832593 : Blo 1020604 5832593 := bstep (se 2 (by rfl) ⟨2187222, by rfl⟩ : syracuseStep 5832593 = 4374445) B4374445
theorem B9830429 : Blo 1020604 9830429 := bstep (se 3 (by rfl) ⟨1843205, by rfl⟩ : syracuseStep 9830429 = 3686411) B3686411
theorem B1966523 : Blo 1020604 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B19628567 : Blo 1020604 19628567 := bstep (se 1 (by rfl) ⟨14721425, by rfl⟩ : syracuseStep 19628567 = 29442851) B29442851
theorem B1311671 : Blo 1020604 1311671 := bstep (se 1 (by rfl) ⟨983753, by rfl⟩ : syracuseStep 1311671 = 1967507) B1967507
theorem B44205101 : Blo 1020604 44205101 := bstep (se 3 (by rfl) ⟨8288456, by rfl⟩ : syracuseStep 44205101 = 16576913) B16576913
theorem B4195385 : Blo 1020604 4195385 := bstep (se 2 (by rfl) ⟨1573269, by rfl⟩ : syracuseStep 4195385 = 3146539) B3146539
theorem B1639943 : Blo 1020604 1639943 := bstep (se 1 (by rfl) ⟨1229957, by rfl⟩ : syracuseStep 1639943 = 2459915) B2459915
theorem B5178977 : Blo 1020604 5178977 := bstep (se 2 (by rfl) ⟨1942116, by rfl⟩ : syracuseStep 5178977 = 3884233) B3884233
theorem B1148539 : Blo 1020604 1148539 := bstep (se 1 (by rfl) ⟨861404, by rfl⟩ : syracuseStep 1148539 = 1722809) B1722809
theorem B6555259 : Blo 1020604 6555259 := bstep (se 1 (by rfl) ⟨4916444, by rfl⟩ : syracuseStep 6555259 = 9832889) B9832889
theorem B1640455 : Blo 1020604 1640455 := bstep (se 1 (by rfl) ⟨1230341, by rfl⟩ : syracuseStep 1640455 = 2460683) B2460683
theorem B1149007 : Blo 1020604 1149007 := bstep (se 1 (by rfl) ⟨861755, by rfl⟩ : syracuseStep 1149007 = 1723511) B1723511
theorem B3278963 : Blo 1020604 3278963 := bstep (se 1 (by rfl) ⟨2459222, by rfl⟩ : syracuseStep 3278963 = 4918445) B4918445
theorem B8292581 : Blo 1020604 8292581 := bstep (se 4 (by rfl) ⟨777429, by rfl⟩ : syracuseStep 8292581 = 1554859) B1554859
theorem B2590967 : Blo 1020604 2590967 := bstep (se 1 (by rfl) ⟨1943225, by rfl⟩ : syracuseStep 2590967 = 3886451) B3886451
theorem B1149403 : Blo 1020604 1149403 := bstep (se 1 (by rfl) ⟨862052, by rfl⟩ : syracuseStep 1149403 = 1724105) B1724105
theorem B15927853 : Blo 1020604 15927853 := bstep (se 3 (by rfl) ⟨2986472, by rfl⟩ : syracuseStep 15927853 = 5972945) B5972945
theorem B2329451 : Blo 1020604 2329451 := bstep (se 1 (by rfl) ⟨1747088, by rfl⟩ : syracuseStep 2329451 = 3494177) B3494177
theorem B1149871 : Blo 1020604 1149871 := bstep (se 1 (by rfl) ⟨862403, by rfl⟩ : syracuseStep 1149871 = 1724807) B1724807
theorem B2296763 : Blo 1020604 2296763 := bstep (se 1 (by rfl) ⟨1722572, by rfl⟩ : syracuseStep 2296763 = 3445145) B3445145
theorem B5180435 : Blo 1020604 5180435 := bstep (se 1 (by rfl) ⟨3885326, by rfl⟩ : syracuseStep 5180435 = 7770653) B7770653
theorem B2296889 : Blo 1020604 2296889 := bstep (se 2 (by rfl) ⟨861333, by rfl⟩ : syracuseStep 2296889 = 1722667) B1722667
theorem B1150303 : Blo 1020604 1150303 := bstep (se 1 (by rfl) ⟨862727, by rfl⟩ : syracuseStep 1150303 = 1725455) B1725455
theorem B4361597 : Blo 1020604 4361597 := bstep (se 3 (by rfl) ⟨817799, by rfl⟩ : syracuseStep 4361597 = 1635599) B1635599
theorem B2297231 : Blo 1020604 2297231 := bstep (se 1 (by rfl) ⟨1722923, by rfl⟩ : syracuseStep 2297231 = 3445847) B3445847
theorem B1379767 : Blo 1020604 1379767 := bstep (se 1 (by rfl) ⟨1034825, by rfl⟩ : syracuseStep 1379767 = 2069651) B2069651
theorem B2592395 : Blo 1020604 2592395 := bstep (se 1 (by rfl) ⟨1944296, by rfl⟩ : syracuseStep 2592395 = 3888593) B3888593
theorem B1150663 : Blo 1020604 1150663 := bstep (se 1 (by rfl) ⟨862997, by rfl⟩ : syracuseStep 1150663 = 1725995) B1725995
theorem B2297555 : Blo 1020604 2297555 := bstep (se 1 (by rfl) ⟨1723166, by rfl⟩ : syracuseStep 2297555 = 3446333) B3446333
theorem B2592607 : Blo 1020604 2592607 := bstep (se 1 (by rfl) ⟨1944455, by rfl⟩ : syracuseStep 2592607 = 3888911) B3888911
theorem B6983533 : Blo 1020604 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B3444983 : Blo 1020604 3444983 := bstep (se 1 (by rfl) ⟨2583737, by rfl⟩ : syracuseStep 3444983 = 5167475) B5167475
theorem B17469755 : Blo 1020604 17469755 := bstep (se 1 (by rfl) ⟨13102316, by rfl⟩ : syracuseStep 17469755 = 26204633) B26204633
theorem B1151527 : Blo 1020604 1151527 := bstep (se 1 (by rfl) ⟨863645, by rfl⟩ : syracuseStep 1151527 = 1727291) B1727291
theorem B3445307 : Blo 1020604 3445307 := bstep (se 1 (by rfl) ⟨2583980, by rfl⟩ : syracuseStep 3445307 = 5167961) B5167961
theorem B2298491 : Blo 1020604 2298491 := bstep (se 1 (by rfl) ⟨1723868, by rfl⟩ : syracuseStep 2298491 = 3447737) B3447737
theorem B1020615 : Blo 1020604 1020615 := bstep (se 1 (by rfl) ⟨765461, by rfl⟩ : syracuseStep 1020615 = 1530923) B1530923
theorem B10490579 : Blo 1020604 10490579 := bstep (se 1 (by rfl) ⟨7867934, by rfl⟩ : syracuseStep 10490579 = 15735869) B15735869
theorem B1020635 : Blo 1020604 1020635 := bstep (se 1 (by rfl) ⟨765476, by rfl⟩ : syracuseStep 1020635 = 1530953) B1530953
theorem B2298617 : Blo 1020604 2298617 := bstep (se 2 (by rfl) ⟨861981, by rfl⟩ : syracuseStep 2298617 = 1723963) B1723963
theorem B2593529 : Blo 1020604 2593529 := bstep (se 2 (by rfl) ⟨972573, by rfl⟩ : syracuseStep 2593529 = 1945147) B1945147
theorem B1020711 : Blo 1020604 1020711 := bstep (se 1 (by rfl) ⟨765533, by rfl⟩ : syracuseStep 1020711 = 1531067) B1531067
theorem B3445577 : Blo 1020604 3445577 := bstep (se 2 (by rfl) ⟨1292091, by rfl⟩ : syracuseStep 3445577 = 2584183) B2584183
theorem B1020751 : Blo 1020604 1020751 := bstep (se 1 (by rfl) ⟨765563, by rfl⟩ : syracuseStep 1020751 = 1531127) B1531127
theorem B1020767 : Blo 1020604 1020767 := bstep (se 1 (by rfl) ⟨765575, by rfl⟩ : syracuseStep 1020767 = 1531151) B1531151
theorem B1020795 : Blo 1020604 1020795 := bstep (se 1 (by rfl) ⟨765596, by rfl⟩ : syracuseStep 1020795 = 1531193) B1531193
theorem B1020847 : Blo 1020604 1020847 := bstep (se 1 (by rfl) ⟨765635, by rfl⟩ : syracuseStep 1020847 = 1531271) B1531271
theorem B1020871 : Blo 1020604 1020871 := bstep (se 1 (by rfl) ⟨765653, by rfl⟩ : syracuseStep 1020871 = 1531307) B1531307
theorem B1020891 : Blo 1020604 1020891 := bstep (se 1 (by rfl) ⟨765668, by rfl⟩ : syracuseStep 1020891 = 1531337) B1531337
theorem B9311233 : Blo 1020604 9311233 := bstep (se 2 (by rfl) ⟨3491712, by rfl⟩ : syracuseStep 9311233 = 6983425) B6983425
theorem B2298887 : Blo 1020604 2298887 := bstep (se 1 (by rfl) ⟨1724165, by rfl⟩ : syracuseStep 2298887 = 3448331) B3448331
theorem B3740687 : Blo 1020604 3740687 := bstep (se 1 (by rfl) ⟨2805515, by rfl⟩ : syracuseStep 3740687 = 5611031) B5611031
theorem B1020967 : Blo 1020604 1020967 := bstep (se 1 (by rfl) ⟨765725, by rfl⟩ : syracuseStep 1020967 = 1531451) B1531451
theorem B1021007 : Blo 1020604 1021007 := bstep (se 1 (by rfl) ⟨765755, by rfl⟩ : syracuseStep 1021007 = 1531511) B1531511
theorem B1840207 : Blo 1020604 1840207 := bstep (se 1 (by rfl) ⟨1380155, by rfl⟩ : syracuseStep 1840207 = 2760311) B2760311
theorem B2298959 : Blo 1020604 2298959 := bstep (se 1 (by rfl) ⟨1724219, by rfl⟩ : syracuseStep 2298959 = 3448439) B3448439
theorem B5248079 : Blo 1020604 5248079 := bstep (se 1 (by rfl) ⟨3936059, by rfl⟩ : syracuseStep 5248079 = 7872119) B7872119
theorem B1021023 : Blo 1020604 1021023 := bstep (se 1 (by rfl) ⟨765767, by rfl⟩ : syracuseStep 1021023 = 1531535) B1531535
theorem B1021051 : Blo 1020604 1021051 := bstep (se 1 (by rfl) ⟨765788, by rfl⟩ : syracuseStep 1021051 = 1531577) B1531577
theorem B1021103 : Blo 1020604 1021103 := bstep (se 1 (by rfl) ⟨765827, by rfl⟩ : syracuseStep 1021103 = 1531655) B1531655
theorem B1021127 : Blo 1020604 1021127 := bstep (se 1 (by rfl) ⟨765845, by rfl⟩ : syracuseStep 1021127 = 1531691) B1531691
theorem B1021147 : Blo 1020604 1021147 := bstep (se 1 (by rfl) ⟨765860, by rfl⟩ : syracuseStep 1021147 = 1531721) B1531721
theorem B8295695 : Blo 1020604 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B1021223 : Blo 1020604 1021223 := bstep (se 1 (by rfl) ⟨765917, by rfl⟩ : syracuseStep 1021223 = 1531835) B1531835
theorem B1021263 : Blo 1020604 1021263 := bstep (se 1 (by rfl) ⟨765947, by rfl⟩ : syracuseStep 1021263 = 1531895) B1531895
theorem B1021279 : Blo 1020604 1021279 := bstep (se 1 (by rfl) ⟨765959, by rfl⟩ : syracuseStep 1021279 = 1531919) B1531919
theorem B1021307 : Blo 1020604 1021307 := bstep (se 1 (by rfl) ⟨765980, by rfl⟩ : syracuseStep 1021307 = 1531961) B1531961
theorem B1021359 : Blo 1020604 1021359 := bstep (se 1 (by rfl) ⟨766019, by rfl⟩ : syracuseStep 1021359 = 1532039) B1532039
theorem B1021383 : Blo 1020604 1021383 := bstep (se 1 (by rfl) ⟨766037, by rfl⟩ : syracuseStep 1021383 = 1532075) B1532075
theorem B1021403 : Blo 1020604 1021403 := bstep (se 1 (by rfl) ⟨766052, by rfl⟩ : syracuseStep 1021403 = 1532105) B1532105
theorem B2299355 : Blo 1020604 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B1021479 : Blo 1020604 1021479 := bstep (se 1 (by rfl) ⟨766109, by rfl⟩ : syracuseStep 1021479 = 1532219) B1532219
theorem B1021519 : Blo 1020604 1021519 := bstep (se 1 (by rfl) ⟨766139, by rfl⟩ : syracuseStep 1021519 = 1532279) B1532279
theorem B1021535 : Blo 1020604 1021535 := bstep (se 1 (by rfl) ⟨766151, by rfl⟩ : syracuseStep 1021535 = 1532303) B1532303
theorem B1021563 : Blo 1020604 1021563 := bstep (se 1 (by rfl) ⟨766172, by rfl⟩ : syracuseStep 1021563 = 1532345) B1532345
theorem B9344659 : Blo 1020604 9344659 := bstep (se 1 (by rfl) ⟨7008494, by rfl⟩ : syracuseStep 9344659 = 14016989) B14016989
theorem B1021615 : Blo 1020604 1021615 := bstep (se 1 (by rfl) ⟨766211, by rfl⟩ : syracuseStep 1021615 = 1532423) B1532423
theorem B1021639 : Blo 1020604 1021639 := bstep (se 1 (by rfl) ⟨766229, by rfl⟩ : syracuseStep 1021639 = 1532459) B1532459
theorem B1021659 : Blo 1020604 1021659 := bstep (se 1 (by rfl) ⟨766244, by rfl⟩ : syracuseStep 1021659 = 1532489) B1532489
theorem B1021735 : Blo 1020604 1021735 := bstep (se 1 (by rfl) ⟨766301, by rfl⟩ : syracuseStep 1021735 = 1532603) B1532603
theorem B1021775 : Blo 1020604 1021775 := bstep (se 1 (by rfl) ⟨766331, by rfl⟩ : syracuseStep 1021775 = 1532663) B1532663
theorem B1021791 : Blo 1020604 1021791 := bstep (se 1 (by rfl) ⟨766343, by rfl⟩ : syracuseStep 1021791 = 1532687) B1532687
theorem B5183351 : Blo 1020604 5183351 := bstep (se 1 (by rfl) ⟨3887513, by rfl⟩ : syracuseStep 5183351 = 7775027) B7775027
theorem B1021819 : Blo 1020604 1021819 := bstep (se 1 (by rfl) ⟨766364, by rfl⟩ : syracuseStep 1021819 = 1532729) B1532729
theorem B1021871 : Blo 1020604 1021871 := bstep (se 1 (by rfl) ⟨766403, by rfl⟩ : syracuseStep 1021871 = 1532807) B1532807
theorem B2299823 : Blo 1020604 2299823 := bstep (se 1 (by rfl) ⟨1724867, by rfl⟩ : syracuseStep 2299823 = 3449735) B3449735
theorem B3446711 : Blo 1020604 3446711 := bstep (se 1 (by rfl) ⟨2585033, by rfl⟩ : syracuseStep 3446711 = 5170067) B5170067
theorem B1021895 : Blo 1020604 1021895 := bstep (se 1 (by rfl) ⟨766421, by rfl⟩ : syracuseStep 1021895 = 1532843) B1532843
theorem B1021915 : Blo 1020604 1021915 := bstep (se 1 (by rfl) ⟨766436, by rfl⟩ : syracuseStep 1021915 = 1532873) B1532873
theorem B2627603 : Blo 1020604 2627603 := bstep (se 1 (by rfl) ⟨1970702, by rfl⟩ : syracuseStep 2627603 = 3941405) B3941405
theorem B1021991 : Blo 1020604 1021991 := bstep (se 1 (by rfl) ⟨766493, by rfl⟩ : syracuseStep 1021991 = 1532987) B1532987
theorem B1939535 : Blo 1020604 1939535 := bstep (se 1 (by rfl) ⟨1454651, by rfl⟩ : syracuseStep 1939535 = 2909303) B2909303
theorem B1022031 : Blo 1020604 1022031 := bstep (se 1 (by rfl) ⟨766523, by rfl⟩ : syracuseStep 1022031 = 1533047) B1533047
theorem B13998167 : Blo 1020604 13998167 := bstep (se 1 (by rfl) ⟨10498625, by rfl⟩ : syracuseStep 13998167 = 20997251) B20997251
theorem B1022047 : Blo 1020604 1022047 := bstep (se 1 (by rfl) ⟨766535, by rfl⟩ : syracuseStep 1022047 = 1533071) B1533071
theorem B1022075 : Blo 1020604 1022075 := bstep (se 1 (by rfl) ⟨766556, by rfl⟩ : syracuseStep 1022075 = 1533113) B1533113
theorem B2300075 : Blo 1020604 2300075 := bstep (se 1 (by rfl) ⟨1725056, by rfl⟩ : syracuseStep 2300075 = 3450113) B3450113
theorem B1022127 : Blo 1020604 1022127 := bstep (se 1 (by rfl) ⟨766595, by rfl⟩ : syracuseStep 1022127 = 1533191) B1533191
theorem B1022151 : Blo 1020604 1022151 := bstep (se 1 (by rfl) ⟨766613, by rfl⟩ : syracuseStep 1022151 = 1533227) B1533227
theorem B1022171 : Blo 1020604 1022171 := bstep (se 1 (by rfl) ⟨766628, by rfl⟩ : syracuseStep 1022171 = 1533257) B1533257
theorem B2103545 : Blo 1020604 2103545 := bstep (se 2 (by rfl) ⟨788829, by rfl⟩ : syracuseStep 2103545 = 1577659) B1577659
theorem B31529249 : Blo 1020604 31529249 := bstep (se 2 (by rfl) ⟨11823468, by rfl⟩ : syracuseStep 31529249 = 23646937) B23646937
theorem B1022247 : Blo 1020604 1022247 := bstep (se 1 (by rfl) ⟨766685, by rfl⟩ : syracuseStep 1022247 = 1533371) B1533371
theorem B1022287 : Blo 1020604 1022287 := bstep (se 1 (by rfl) ⟨766715, by rfl⟩ : syracuseStep 1022287 = 1533431) B1533431
theorem B1022303 : Blo 1020604 1022303 := bstep (se 1 (by rfl) ⟨766727, by rfl⟩ : syracuseStep 1022303 = 1533455) B1533455
theorem B1022331 : Blo 1020604 1022331 := bstep (se 1 (by rfl) ⟨766748, by rfl⟩ : syracuseStep 1022331 = 1533497) B1533497
theorem B1022383 : Blo 1020604 1022383 := bstep (se 1 (by rfl) ⟨766787, by rfl⟩ : syracuseStep 1022383 = 1533575) B1533575
theorem B1022407 : Blo 1020604 1022407 := bstep (se 1 (by rfl) ⟨766805, by rfl⟩ : syracuseStep 1022407 = 1533611) B1533611
theorem B1022427 : Blo 1020604 1022427 := bstep (se 1 (by rfl) ⟨766820, by rfl⟩ : syracuseStep 1022427 = 1533641) B1533641
theorem B3447305 : Blo 1020604 3447305 := bstep (se 2 (by rfl) ⟨1292739, by rfl⟩ : syracuseStep 3447305 = 2585479) B2585479
theorem B1022503 : Blo 1020604 1022503 := bstep (se 1 (by rfl) ⟨766877, by rfl⟩ : syracuseStep 1022503 = 1533755) B1533755
theorem B1022543 : Blo 1020604 1022543 := bstep (se 1 (by rfl) ⟨766907, by rfl⟩ : syracuseStep 1022543 = 1533815) B1533815
theorem B1022559 : Blo 1020604 1022559 := bstep (se 1 (by rfl) ⟨766919, by rfl⟩ : syracuseStep 1022559 = 1533839) B1533839
theorem B1022587 : Blo 1020604 1022587 := bstep (se 1 (by rfl) ⟨766940, by rfl⟩ : syracuseStep 1022587 = 1533881) B1533881
theorem B1022639 : Blo 1020604 1022639 := bstep (se 1 (by rfl) ⟨766979, by rfl⟩ : syracuseStep 1022639 = 1533959) B1533959
theorem B2300615 : Blo 1020604 2300615 := bstep (se 1 (by rfl) ⟨1725461, by rfl⟩ : syracuseStep 2300615 = 3450923) B3450923
theorem B1022663 : Blo 1020604 1022663 := bstep (se 1 (by rfl) ⟨766997, by rfl⟩ : syracuseStep 1022663 = 1533995) B1533995
theorem B4659923 : Blo 1020604 4659923 := bstep (se 1 (by rfl) ⟨3494942, by rfl⟩ : syracuseStep 4659923 = 6989885) B6989885
theorem B1022683 : Blo 1020604 1022683 := bstep (se 1 (by rfl) ⟨767012, by rfl⟩ : syracuseStep 1022683 = 1534025) B1534025
theorem B1022759 : Blo 1020604 1022759 := bstep (se 1 (by rfl) ⟨767069, by rfl⟩ : syracuseStep 1022759 = 1534139) B1534139
theorem B2628425 : Blo 1020604 2628425 := bstep (se 2 (by rfl) ⟨985659, by rfl⟩ : syracuseStep 2628425 = 1971319) B1971319
theorem B1022799 : Blo 1020604 1022799 := bstep (se 1 (by rfl) ⟨767099, by rfl⟩ : syracuseStep 1022799 = 1534199) B1534199
theorem B1022815 : Blo 1020604 1022815 := bstep (se 1 (by rfl) ⟨767111, by rfl⟩ : syracuseStep 1022815 = 1534223) B1534223
theorem B1022843 : Blo 1020604 1022843 := bstep (se 1 (by rfl) ⟨767132, by rfl⟩ : syracuseStep 1022843 = 1534265) B1534265
theorem B1022895 : Blo 1020604 1022895 := bstep (se 1 (by rfl) ⟨767171, by rfl⟩ : syracuseStep 1022895 = 1534343) B1534343
theorem B1022919 : Blo 1020604 1022919 := bstep (se 1 (by rfl) ⟨767189, by rfl⟩ : syracuseStep 1022919 = 1534379) B1534379
theorem B1022939 : Blo 1020604 1022939 := bstep (se 1 (by rfl) ⟨767204, by rfl⟩ : syracuseStep 1022939 = 1534409) B1534409
theorem B1023015 : Blo 1020604 1023015 := bstep (se 1 (by rfl) ⟨767261, by rfl⟩ : syracuseStep 1023015 = 1534523) B1534523
theorem B1940537 : Blo 1020604 1940537 := bstep (se 2 (by rfl) ⟨727701, by rfl⟩ : syracuseStep 1940537 = 1455403) B1455403
theorem B1023055 : Blo 1020604 1023055 := bstep (se 1 (by rfl) ⟨767291, by rfl⟩ : syracuseStep 1023055 = 1534583) B1534583
theorem B1023071 : Blo 1020604 1023071 := bstep (se 1 (by rfl) ⟨767303, by rfl⟩ : syracuseStep 1023071 = 1534607) B1534607
theorem B1023099 : Blo 1020604 1023099 := bstep (se 1 (by rfl) ⟨767324, by rfl⟩ : syracuseStep 1023099 = 1534649) B1534649
theorem B1023151 : Blo 1020604 1023151 := bstep (se 1 (by rfl) ⟨767363, by rfl⟩ : syracuseStep 1023151 = 1534727) B1534727
theorem B1023175 : Blo 1020604 1023175 := bstep (se 1 (by rfl) ⟨767381, by rfl⟩ : syracuseStep 1023175 = 1534763) B1534763
theorem B1023195 : Blo 1020604 1023195 := bstep (se 1 (by rfl) ⟨767396, by rfl⟩ : syracuseStep 1023195 = 1534793) B1534793
theorem B1023271 : Blo 1020604 1023271 := bstep (se 1 (by rfl) ⟨767453, by rfl⟩ : syracuseStep 1023271 = 1534907) B1534907
theorem B1023311 : Blo 1020604 1023311 := bstep (se 1 (by rfl) ⟨767483, by rfl⟩ : syracuseStep 1023311 = 1534967) B1534967
theorem B1023327 : Blo 1020604 1023327 := bstep (se 1 (by rfl) ⟨767495, by rfl⟩ : syracuseStep 1023327 = 1534991) B1534991
theorem B3448169 : Blo 1020604 3448169 := bstep (se 2 (by rfl) ⟨1293063, by rfl⟩ : syracuseStep 3448169 = 2586127) B2586127
theorem B1023355 : Blo 1020604 1023355 := bstep (se 1 (by rfl) ⟨767516, by rfl⟩ : syracuseStep 1023355 = 1535033) B1535033
theorem B1023407 : Blo 1020604 1023407 := bstep (se 1 (by rfl) ⟨767555, by rfl⟩ : syracuseStep 1023407 = 1535111) B1535111
theorem B1023431 : Blo 1020604 1023431 := bstep (se 1 (by rfl) ⟨767573, by rfl⟩ : syracuseStep 1023431 = 1535147) B1535147
theorem B1023451 : Blo 1020604 1023451 := bstep (se 1 (by rfl) ⟨767588, by rfl⟩ : syracuseStep 1023451 = 1535177) B1535177
theorem B2301479 : Blo 1020604 2301479 := bstep (se 1 (by rfl) ⟨1726109, by rfl⟩ : syracuseStep 2301479 = 3452219) B3452219
theorem B1023527 : Blo 1020604 1023527 := bstep (se 1 (by rfl) ⟨767645, by rfl⟩ : syracuseStep 1023527 = 1535291) B1535291
theorem B1023567 : Blo 1020604 1023567 := bstep (se 1 (by rfl) ⟨767675, by rfl⟩ : syracuseStep 1023567 = 1535351) B1535351
theorem B1023583 : Blo 1020604 1023583 := bstep (se 1 (by rfl) ⟨767687, by rfl⟩ : syracuseStep 1023583 = 1535375) B1535375
theorem B1023611 : Blo 1020604 1023611 := bstep (se 1 (by rfl) ⟨767708, by rfl⟩ : syracuseStep 1023611 = 1535417) B1535417
theorem B4365971 : Blo 1020604 4365971 := bstep (se 1 (by rfl) ⟨3274478, by rfl⟩ : syracuseStep 4365971 = 6548957) B6548957
theorem B5250707 : Blo 1020604 5250707 := bstep (se 1 (by rfl) ⟨3938030, by rfl⟩ : syracuseStep 5250707 = 7876061) B7876061
theorem B1023663 : Blo 1020604 1023663 := bstep (se 1 (by rfl) ⟨767747, by rfl⟩ : syracuseStep 1023663 = 1535495) B1535495
theorem B1023687 : Blo 1020604 1023687 := bstep (se 1 (by rfl) ⟨767765, by rfl⟩ : syracuseStep 1023687 = 1535531) B1535531
theorem B1023707 : Blo 1020604 1023707 := bstep (se 1 (by rfl) ⟨767780, by rfl⟩ : syracuseStep 1023707 = 1535561) B1535561
theorem B1023783 : Blo 1020604 1023783 := bstep (se 1 (by rfl) ⟨767837, by rfl⟩ : syracuseStep 1023783 = 1535675) B1535675
theorem B1023823 : Blo 1020604 1023823 := bstep (se 1 (by rfl) ⟨767867, by rfl⟩ : syracuseStep 1023823 = 1535735) B1535735
theorem B1023839 : Blo 1020604 1023839 := bstep (se 1 (by rfl) ⟨767879, by rfl⟩ : syracuseStep 1023839 = 1535759) B1535759
theorem B2301803 : Blo 1020604 2301803 := bstep (se 1 (by rfl) ⟨1726352, by rfl⟩ : syracuseStep 2301803 = 3452705) B3452705
theorem B1023867 : Blo 1020604 1023867 := bstep (se 1 (by rfl) ⟨767900, by rfl⟩ : syracuseStep 1023867 = 1535801) B1535801
theorem B2301857 : Blo 1020604 2301857 := bstep (se 2 (by rfl) ⟨863196, by rfl⟩ : syracuseStep 2301857 = 1726393) B1726393
theorem B1023919 : Blo 1020604 1023919 := bstep (se 1 (by rfl) ⟨767939, by rfl⟩ : syracuseStep 1023919 = 1535879) B1535879
theorem B3448763 : Blo 1020604 3448763 := bstep (se 1 (by rfl) ⟨2586572, by rfl⟩ : syracuseStep 3448763 = 5173145) B5173145
theorem B1023943 : Blo 1020604 1023943 := bstep (se 1 (by rfl) ⟨767957, by rfl⟩ : syracuseStep 1023943 = 1535915) B1535915
theorem B1843163 : Blo 1020604 1843163 := bstep (se 1 (by rfl) ⟨1382372, by rfl⟩ : syracuseStep 1843163 = 2764745) B2764745
theorem B1023963 : Blo 1020604 1023963 := bstep (se 1 (by rfl) ⟨767972, by rfl⟩ : syracuseStep 1023963 = 1535945) B1535945
theorem B19636253 : Blo 1020604 19636253 := bstep (se 3 (by rfl) ⟨3681797, by rfl⟩ : syracuseStep 19636253 = 7363595) B7363595
theorem B1024039 : Blo 1020604 1024039 := bstep (se 1 (by rfl) ⟨768029, by rfl⟩ : syracuseStep 1024039 = 1536059) B1536059
theorem B1024079 : Blo 1020604 1024079 := bstep (se 1 (by rfl) ⟨768059, by rfl⟩ : syracuseStep 1024079 = 1536119) B1536119
theorem B1024095 : Blo 1020604 1024095 := bstep (se 1 (by rfl) ⟨768071, by rfl⟩ : syracuseStep 1024095 = 1536143) B1536143
theorem B1024123 : Blo 1020604 1024123 := bstep (se 1 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 1024123 = 1536185) B1536185
theorem B2760875 : Blo 1020604 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B1024175 : Blo 1020604 1024175 := bstep (se 1 (by rfl) ⟨768131, by rfl⟩ : syracuseStep 1024175 = 1536263) B1536263
theorem B1024199 : Blo 1020604 1024199 := bstep (se 1 (by rfl) ⟨768149, by rfl⟩ : syracuseStep 1024199 = 1536299) B1536299
theorem B1024219 : Blo 1020604 1024219 := bstep (se 1 (by rfl) ⟨768164, by rfl⟩ : syracuseStep 1024219 = 1536329) B1536329
theorem B2302199 : Blo 1020604 2302199 := bstep (se 1 (by rfl) ⟨1726649, by rfl⟩ : syracuseStep 2302199 = 3453299) B3453299
theorem B1024295 : Blo 1020604 1024295 := bstep (se 1 (by rfl) ⟨768221, by rfl⟩ : syracuseStep 1024295 = 1536443) B1536443
theorem B1024335 : Blo 1020604 1024335 := bstep (se 1 (by rfl) ⟨768251, by rfl⟩ : syracuseStep 1024335 = 1536503) B1536503
theorem B2072927 : Blo 1020604 2072927 := bstep (se 1 (by rfl) ⟨1554695, by rfl⟩ : syracuseStep 2072927 = 3109391) B3109391
theorem B1024351 : Blo 1020604 1024351 := bstep (se 1 (by rfl) ⟨768263, by rfl⟩ : syracuseStep 1024351 = 1536527) B1536527
theorem B1024379 : Blo 1020604 1024379 := bstep (se 1 (by rfl) ⟨768284, by rfl⟩ : syracuseStep 1024379 = 1536569) B1536569
theorem B1024431 : Blo 1020604 1024431 := bstep (se 1 (by rfl) ⟨768323, by rfl⟩ : syracuseStep 1024431 = 1536647) B1536647
theorem B1024455 : Blo 1020604 1024455 := bstep (se 1 (by rfl) ⟨768341, by rfl⟩ : syracuseStep 1024455 = 1536683) B1536683
theorem B3875273 : Blo 1020604 3875273 := bstep (se 2 (by rfl) ⟨1453227, by rfl⟩ : syracuseStep 3875273 = 2906455) B2906455
theorem B1024475 : Blo 1020604 1024475 := bstep (se 1 (by rfl) ⟨768356, by rfl⟩ : syracuseStep 1024475 = 1536713) B1536713
theorem B1024551 : Blo 1020604 1024551 := bstep (se 1 (by rfl) ⟨768413, by rfl⟩ : syracuseStep 1024551 = 1536827) B1536827
theorem B1024591 : Blo 1020604 1024591 := bstep (se 1 (by rfl) ⟨768443, by rfl⟩ : syracuseStep 1024591 = 1536887) B1536887
theorem B2302793 : Blo 1020604 2302793 := bstep (se 2 (by rfl) ⟨863547, by rfl⟩ : syracuseStep 2302793 = 1727095) B1727095
theorem B1844129 : Blo 1020604 1844129 := bstep (se 2 (by rfl) ⟨691548, by rfl⟩ : syracuseStep 1844129 = 1383097) B1383097
theorem B3875759 : Blo 1020604 3875759 := bstep (se 1 (by rfl) ⟨2906819, by rfl⟩ : syracuseStep 3875759 = 5813639) B5813639
theorem B1942535 : Blo 1020604 1942535 := bstep (se 1 (by rfl) ⟨1456901, by rfl⟩ : syracuseStep 1942535 = 2913803) B2913803
theorem B1844641 : Blo 1020604 1844641 := bstep (se 2 (by rfl) ⟨691740, by rfl⟩ : syracuseStep 1844641 = 1383481) B1383481
theorem B1942967 : Blo 1020604 1942967 := bstep (se 1 (by rfl) ⟨1457225, by rfl⟩ : syracuseStep 1942967 = 2914451) B2914451
theorem B1943119 : Blo 1020604 1943119 := bstep (se 1 (by rfl) ⟨1457339, by rfl⟩ : syracuseStep 1943119 = 2914679) B2914679
theorem B1844815 : Blo 1020604 1844815 := bstep (se 1 (by rfl) ⟨1383611, by rfl⟩ : syracuseStep 1844815 = 2767223) B2767223
theorem B2303585 : Blo 1020604 2303585 := bstep (se 2 (by rfl) ⟨863844, by rfl⟩ : syracuseStep 2303585 = 1727689) B1727689
theorem B3679867 : Blo 1020604 3679867 := bstep (se 1 (by rfl) ⟨2759900, by rfl⟩ : syracuseStep 3679867 = 5519801) B5519801
theorem B3450491 : Blo 1020604 3450491 := bstep (se 1 (by rfl) ⟨2587868, by rfl⟩ : syracuseStep 3450491 = 5175737) B5175737
theorem B4138685 : Blo 1020604 4138685 := bstep (se 3 (by rfl) ⟨776003, by rfl⟩ : syracuseStep 4138685 = 1552007) B1552007
theorem B3450653 : Blo 1020604 3450653 := bstep (se 3 (by rfl) ⟨646997, by rfl⟩ : syracuseStep 3450653 = 1293995) B1293995
theorem B2303927 : Blo 1020604 2303927 := bstep (se 1 (by rfl) ⟨1727945, by rfl⟩ : syracuseStep 2303927 = 3455891) B3455891
theorem B3876943 : Blo 1020604 3876943 := bstep (se 1 (by rfl) ⟨2907707, by rfl⟩ : syracuseStep 3876943 = 5815415) B5815415
theorem B7776485 : Blo 1020604 7776485 := bstep (se 4 (by rfl) ⟨729045, by rfl⟩ : syracuseStep 7776485 = 1458091) B1458091
theorem B8857943 : Blo 1020604 8857943 := bstep (se 1 (by rfl) ⟨6643457, by rfl⟩ : syracuseStep 8857943 = 13286915) B13286915
theorem B19638713 : Blo 1020604 19638713 := bstep (se 2 (by rfl) ⟨7364517, by rfl⟩ : syracuseStep 19638713 = 14729035) B14729035
theorem B3451355 : Blo 1020604 3451355 := bstep (se 1 (by rfl) ⟨2588516, by rfl⟩ : syracuseStep 3451355 = 5177033) B5177033
theorem B2304521 : Blo 1020604 2304521 := bstep (se 2 (by rfl) ⟨864195, by rfl⟩ : syracuseStep 2304521 = 1728391) B1728391
theorem B3877415 : Blo 1020604 3877415 := bstep (se 1 (by rfl) ⟨2908061, by rfl⟩ : syracuseStep 3877415 = 5816123) B5816123
theorem B1845931 : Blo 1020604 1845931 := bstep (se 1 (by rfl) ⟨1384448, by rfl⟩ : syracuseStep 1845931 = 2768897) B2768897
theorem B2304863 : Blo 1020604 2304863 := bstep (se 1 (by rfl) ⟨1728647, by rfl⟩ : syracuseStep 2304863 = 3457295) B3457295
theorem B1944425 : Blo 1020604 1944425 := bstep (se 2 (by rfl) ⟨729159, by rfl⟩ : syracuseStep 1944425 = 1458319) B1458319
theorem B1747855 : Blo 1020604 1747855 := bstep (se 1 (by rfl) ⟨1310891, by rfl⟩ : syracuseStep 1747855 = 2621783) B2621783
theorem B2305043 : Blo 1020604 2305043 := bstep (se 1 (by rfl) ⟨1728782, by rfl⟩ : syracuseStep 2305043 = 3457565) B3457565
theorem B3452057 : Blo 1020604 3452057 := bstep (se 2 (by rfl) ⟨1294521, by rfl⟩ : syracuseStep 3452057 = 2589043) B2589043
theorem B3878387 : Blo 1020604 3878387 := bstep (se 1 (by rfl) ⟨2908790, by rfl⟩ : syracuseStep 3878387 = 5817581) B5817581
theorem B8302445 : Blo 1020604 8302445 := bstep (se 3 (by rfl) ⟨1556708, by rfl⟩ : syracuseStep 8302445 = 3113417) B3113417
theorem B7385165 : Blo 1020604 7385165 := bstep (se 3 (by rfl) ⟨1384718, by rfl⟩ : syracuseStep 7385165 = 2769437) B2769437
theorem B3453245 : Blo 1020604 3453245 := bstep (se 3 (by rfl) ⟨647483, by rfl⟩ : syracuseStep 3453245 = 1294967) B1294967
theorem B33141251 : Blo 1020604 33141251 := bstep (se 1 (by rfl) ⟨24855938, by rfl⟩ : syracuseStep 33141251 = 49711877) B49711877
theorem B18691073 : Blo 1020604 18691073 := bstep (se 2 (by rfl) ⟨7009152, by rfl⟩ : syracuseStep 18691073 = 14018305) B14018305
theorem B3454109 : Blo 1020604 3454109 := bstep (se 3 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 3454109 = 1295291) B1295291
theorem B9843929 : Blo 1020604 9843929 := bstep (se 2 (by rfl) ⟨3691473, by rfl⟩ : syracuseStep 9843929 = 7382947) B7382947
theorem B13284773 : Blo 1020604 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B3454649 : Blo 1020604 3454649 := bstep (se 2 (by rfl) ⟨1295493, by rfl⟩ : syracuseStep 3454649 = 2590987) B2590987
theorem B58930901 : Blo 1020604 58930901 := bstep (se 7 (by rfl) ⟨690596, by rfl⟩ : syracuseStep 58930901 = 1381193) B1381193
theorem B6207299 : Blo 1020604 6207299 := bstep (se 1 (by rfl) ⟨4655474, by rfl⟩ : syracuseStep 6207299 = 9310949) B9310949
theorem B6993935 : Blo 1020604 6993935 := bstep (se 1 (by rfl) ⟨5245451, by rfl⟩ : syracuseStep 6993935 = 10490903) B10490903
theorem B8304677 : Blo 1020604 8304677 := bstep (se 4 (by rfl) ⟨778563, by rfl⟩ : syracuseStep 8304677 = 1557127) B1557127
theorem B16595077 : Blo 1020604 16595077 := bstep (se 4 (by rfl) ⟨1555788, by rfl⟩ : syracuseStep 16595077 = 3111577) B3111577
theorem B3455243 : Blo 1020604 3455243 := bstep (se 1 (by rfl) ⟨2591432, by rfl⟩ : syracuseStep 3455243 = 5182865) B5182865
theorem B3881303 : Blo 1020604 3881303 := bstep (se 1 (by rfl) ⟨2910977, by rfl⟩ : syracuseStep 3881303 = 5821955) B5821955
theorem B15350219 : Blo 1020604 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B3455513 : Blo 1020604 3455513 := bstep (se 2 (by rfl) ⟨1295817, by rfl⟩ : syracuseStep 3455513 = 2591635) B2591635
theorem B1227343 : Blo 1020604 1227343 := bstep (se 1 (by rfl) ⟨920507, by rfl⟩ : syracuseStep 1227343 = 1841015) B1841015
theorem B11057849 : Blo 1020604 11057849 := bstep (se 2 (by rfl) ⟨4146693, by rfl⟩ : syracuseStep 11057849 = 8293387) B8293387
theorem B33668227 : Blo 1020604 33668227 := bstep (se 1 (by rfl) ⟨25251170, by rfl⟩ : syracuseStep 33668227 = 50502341) B50502341
theorem B3882593 : Blo 1020604 3882593 := bstep (se 2 (by rfl) ⟨1455972, by rfl⟩ : syracuseStep 3882593 = 2911945) B2911945
theorem B3456647 : Blo 1020604 3456647 := bstep (se 1 (by rfl) ⟨2592485, by rfl⟩ : syracuseStep 3456647 = 5184971) B5184971
theorem B3456701 : Blo 1020604 3456701 := bstep (se 3 (by rfl) ⟨648131, by rfl⟩ : syracuseStep 3456701 = 1296263) B1296263
theorem B3456863 : Blo 1020604 3456863 := bstep (se 1 (by rfl) ⟨2592647, by rfl⟩ : syracuseStep 3456863 = 5185295) B5185295
theorem B1228727 : Blo 1020604 1228727 := bstep (se 1 (by rfl) ⟨921545, by rfl⟩ : syracuseStep 1228727 = 1843091) B1843091
theorem B1458103 : Blo 1020604 1458103 := bstep (se 1 (by rfl) ⟨1093577, by rfl⟩ : syracuseStep 1458103 = 2187155) B2187155
theorem B3457025 : Blo 1020604 3457025 := bstep (se 2 (by rfl) ⟨1296384, by rfl⟩ : syracuseStep 3457025 = 2592769) B2592769
theorem B1294375 : Blo 1020604 1294375 := bstep (se 1 (by rfl) ⟨970781, by rfl⟩ : syracuseStep 1294375 = 1941563) B1941563
theorem B1294699 : Blo 1020604 1294699 := bstep (se 1 (by rfl) ⟨971024, by rfl⟩ : syracuseStep 1294699 = 1942049) B1942049
theorem B6209921 : Blo 1020604 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B3457835 : Blo 1020604 3457835 := bstep (se 1 (by rfl) ⟨2593376, by rfl⟩ : syracuseStep 3457835 = 5186753) B5186753
theorem B4375403 : Blo 1020604 4375403 := bstep (se 1 (by rfl) ⟨3281552, by rfl⟩ : syracuseStep 4375403 = 6563105) B6563105
theorem B3687277 : Blo 1020604 3687277 := bstep (se 3 (by rfl) ⟨691364, by rfl⟩ : syracuseStep 3687277 = 1382729) B1382729
theorem B1164251 : Blo 1020604 1164251 := bstep (se 1 (by rfl) ⟨873188, by rfl⟩ : syracuseStep 1164251 = 1746377) B1746377
theorem B3884051 : Blo 1020604 3884051 := bstep (se 1 (by rfl) ⟨2913038, by rfl⟩ : syracuseStep 3884051 = 5826077) B5826077
theorem B8307791 : Blo 1020604 8307791 := bstep (se 1 (by rfl) ⟨6230843, by rfl⟩ : syracuseStep 8307791 = 12461687) B12461687
theorem B6309245 : Blo 1020604 6309245 := bstep (se 3 (by rfl) ⟨1182983, by rfl⟩ : syracuseStep 6309245 = 2365967) B2365967
theorem B3884507 : Blo 1020604 3884507 := bstep (se 1 (by rfl) ⟨2913380, by rfl⟩ : syracuseStep 3884507 = 5826761) B5826761
theorem B4376051 : Blo 1020604 4376051 := bstep (se 1 (by rfl) ⟨3282038, by rfl⟩ : syracuseStep 4376051 = 6564077) B6564077
theorem B1295995 : Blo 1020604 1295995 := bstep (se 1 (by rfl) ⟨971996, by rfl⟩ : syracuseStep 1295995 = 1943993) B1943993
theorem B59754131 : Blo 1020604 59754131 := bstep (se 1 (by rfl) ⟨44815598, by rfl⟩ : syracuseStep 59754131 = 89631197) B89631197
theorem B6539267 : Blo 1020604 6539267 := bstep (se 1 (by rfl) ⟨4904450, by rfl⟩ : syracuseStep 6539267 = 9808901) B9808901
theorem B1722377 : Blo 1020604 1722377 := bstep (se 2 (by rfl) ⟨645891, by rfl⟩ : syracuseStep 1722377 = 1291783) B1291783
theorem B7358521 : Blo 1020604 7358521 := bstep (se 2 (by rfl) ⟨2759445, by rfl⟩ : syracuseStep 7358521 = 5518891) B5518891
theorem B1722539 : Blo 1020604 1722539 := bstep (se 1 (by rfl) ⟨1291904, by rfl⟩ : syracuseStep 1722539 = 2583809) B2583809
theorem B1722937 : Blo 1020604 1722937 := bstep (se 2 (by rfl) ⟨646101, by rfl⟩ : syracuseStep 1722937 = 1292203) B1292203
theorem B2181755 : Blo 1020604 2181755 := bstep (se 1 (by rfl) ⟨1636316, by rfl⟩ : syracuseStep 2181755 = 3272633) B3272633
theorem B3885691 : Blo 1020604 3885691 := bstep (se 1 (by rfl) ⟨2914268, by rfl⟩ : syracuseStep 3885691 = 5828537) B5828537
theorem B14764679 : Blo 1020604 14764679 := bstep (se 1 (by rfl) ⟨11073509, by rfl⟩ : syracuseStep 14764679 = 22147019) B22147019
theorem B1034951 : Blo 1020604 1034951 := bstep (se 1 (by rfl) ⟨776213, by rfl⟩ : syracuseStep 1034951 = 1552427) B1552427
theorem B1723079 : Blo 1020604 1723079 := bstep (se 1 (by rfl) ⟨1292309, by rfl⟩ : syracuseStep 1723079 = 2584619) B2584619
theorem B7359187 : Blo 1020604 7359187 := bstep (se 1 (by rfl) ⟨5519390, by rfl⟩ : syracuseStep 7359187 = 11038781) B11038781
theorem B1723241 : Blo 1020604 1723241 := bstep (se 2 (by rfl) ⟨646215, by rfl⟩ : syracuseStep 1723241 = 1292431) B1292431
theorem B8277011 : Blo 1020604 8277011 := bstep (se 1 (by rfl) ⟨6207758, by rfl⟩ : syracuseStep 8277011 = 12415517) B12415517
theorem B5819471 : Blo 1020604 5819471 := bstep (se 1 (by rfl) ⟨4364603, by rfl⟩ : syracuseStep 5819471 = 8729207) B8729207
theorem B4148381 : Blo 1020604 4148381 := bstep (se 3 (by rfl) ⟨777821, by rfl⟩ : syracuseStep 4148381 = 1555643) B1555643
theorem B1723639 : Blo 1020604 1723639 := bstep (se 1 (by rfl) ⟨1292729, by rfl⟩ : syracuseStep 1723639 = 2585459) B2585459
theorem B1723835 : Blo 1020604 1723835 := bstep (se 1 (by rfl) ⟨1292876, by rfl⟩ : syracuseStep 1723835 = 2585753) B2585753
theorem B2182619 : Blo 1020604 2182619 := bstep (se 1 (by rfl) ⟨1636964, by rfl⟩ : syracuseStep 2182619 = 3273929) B3273929
theorem B1723943 : Blo 1020604 1723943 := bstep (se 1 (by rfl) ⟨1292957, by rfl⟩ : syracuseStep 1723943 = 2585915) B2585915
theorem B1330811 : Blo 1020604 1330811 := bstep (se 1 (by rfl) ⟨998108, by rfl⟩ : syracuseStep 1330811 = 1996217) B1996217
theorem B1724233 : Blo 1020604 1724233 := bstep (se 2 (by rfl) ⟨646587, by rfl⟩ : syracuseStep 1724233 = 1293175) B1293175
theorem B1724267 : Blo 1020604 1724267 := bstep (se 1 (by rfl) ⟨1293200, by rfl⟩ : syracuseStep 1724267 = 2586401) B2586401
theorem B7982957 : Blo 1020604 7982957 := bstep (se 3 (by rfl) ⟨1496804, by rfl⟩ : syracuseStep 7982957 = 2993609) B2993609
theorem B3886967 : Blo 1020604 3886967 := bstep (se 1 (by rfl) ⟨2915225, by rfl⟩ : syracuseStep 3886967 = 5830451) B5830451
theorem B13127741 : Blo 1020604 13127741 := bstep (se 3 (by rfl) ⟨2461451, by rfl⟩ : syracuseStep 13127741 = 4922903) B4922903
theorem B5820497 : Blo 1020604 5820497 := bstep (se 2 (by rfl) ⟨2182686, by rfl⟩ : syracuseStep 5820497 = 4365373) B4365373
theorem B1724665 : Blo 1020604 1724665 := bstep (se 2 (by rfl) ⟨646749, by rfl⟩ : syracuseStep 1724665 = 1293499) B1293499
theorem B1724935 : Blo 1020604 1724935 := bstep (se 1 (by rfl) ⟨1293701, by rfl⟩ : syracuseStep 1724935 = 2587403) B2587403
theorem B1036999 : Blo 1020604 1036999 := bstep (se 1 (by rfl) ⟨777749, by rfl⟩ : syracuseStep 1036999 = 1555499) B1555499
theorem B3887939 : Blo 1020604 3887939 := bstep (se 1 (by rfl) ⟨2915954, by rfl⟩ : syracuseStep 3887939 = 5831909) B5831909
theorem B1725367 : Blo 1020604 1725367 := bstep (se 1 (by rfl) ⟨1294025, by rfl⟩ : syracuseStep 1725367 = 2588051) B2588051
theorem B7361579 : Blo 1020604 7361579 := bstep (se 1 (by rfl) ⟨5521184, by rfl⟩ : syracuseStep 7361579 = 11042369) B11042369
theorem B1725563 : Blo 1020604 1725563 := bstep (se 1 (by rfl) ⟨1294172, by rfl⟩ : syracuseStep 1725563 = 2588345) B2588345
theorem B3888395 : Blo 1020604 3888395 := bstep (se 1 (by rfl) ⟨2916296, by rfl⟩ : syracuseStep 3888395 = 5832593) B5832593
theorem B1037647 : Blo 1020604 1037647 := bstep (se 1 (by rfl) ⟨778235, by rfl⟩ : syracuseStep 1037647 = 1556471) B1556471
theorem B17487251 : Blo 1020604 17487251 := bstep (se 1 (by rfl) ⟨13115438, by rfl⟩ : syracuseStep 17487251 = 26230877) B26230877
theorem B1725961 : Blo 1020604 1725961 := bstep (se 2 (by rfl) ⟨647235, by rfl⟩ : syracuseStep 1725961 = 1294471) B1294471
theorem B1726123 : Blo 1020604 1726123 := bstep (se 1 (by rfl) ⟨1294592, by rfl⟩ : syracuseStep 1726123 = 2589185) B2589185
theorem B1922809 : Blo 1020604 1922809 := bstep (se 2 (by rfl) ⟨721053, by rfl⟩ : syracuseStep 1922809 = 1442107) B1442107
theorem B7755587 : Blo 1020604 7755587 := bstep (se 1 (by rfl) ⟨5816690, by rfl⟩ : syracuseStep 7755587 = 11633381) B11633381
theorem B3889079 : Blo 1020604 3889079 := bstep (se 1 (by rfl) ⟨2916809, by rfl⟩ : syracuseStep 3889079 = 5833619) B5833619
theorem B2185147 : Blo 1020604 2185147 := bstep (se 1 (by rfl) ⟨1638860, by rfl⟩ : syracuseStep 2185147 = 3277721) B3277721
theorem B1726427 : Blo 1020604 1726427 := bstep (se 1 (by rfl) ⟨1294820, by rfl⟩ : syracuseStep 1726427 = 2589641) B2589641
theorem B2185223 : Blo 1020604 2185223 := bstep (se 1 (by rfl) ⟨1638917, by rfl⟩ : syracuseStep 2185223 = 3277835) B3277835
theorem B1726663 : Blo 1020604 1726663 := bstep (se 1 (by rfl) ⟨1294997, by rfl⟩ : syracuseStep 1726663 = 2589995) B2589995
theorem B2185463 : Blo 1020604 2185463 := bstep (se 1 (by rfl) ⟨1639097, by rfl⟩ : syracuseStep 2185463 = 3278195) B3278195
theorem B1726825 : Blo 1020604 1726825 := bstep (se 2 (by rfl) ⟨647559, by rfl⟩ : syracuseStep 1726825 = 1295119) B1295119
theorem B45504899 : Blo 1020604 45504899 := bstep (se 1 (by rfl) ⟨34128674, by rfl⟩ : syracuseStep 45504899 = 68257349) B68257349
theorem B5823161 : Blo 1020604 5823161 := bstep (se 2 (by rfl) ⟨2183685, by rfl⟩ : syracuseStep 5823161 = 4367371) B4367371
theorem B3889853 : Blo 1020604 3889853 := bstep (se 3 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 3889853 = 1458695) B1458695
theorem B1727419 : Blo 1020604 1727419 := bstep (se 1 (by rfl) ⟨1295564, by rfl⟩ : syracuseStep 1727419 = 2591129) B2591129
theorem B1727527 : Blo 1020604 1727527 := bstep (se 1 (by rfl) ⟨1295645, by rfl⟩ : syracuseStep 1727527 = 2591291) B2591291
theorem B1530959 : Blo 1020604 1530959 := bstep (se 1 (by rfl) ⟨1148219, by rfl⟩ : syracuseStep 1530959 = 2296439) B2296439
theorem B15981761 : Blo 1020604 15981761 := bstep (se 2 (by rfl) ⟨5993160, by rfl⟩ : syracuseStep 15981761 = 11986321) B11986321
theorem B1531079 : Blo 1020604 1531079 := bstep (se 1 (by rfl) ⟨1148309, by rfl⟩ : syracuseStep 1531079 = 2296619) B2296619
theorem B6216907 : Blo 1020604 6216907 := bstep (se 1 (by rfl) ⟨4662680, by rfl⟩ : syracuseStep 6216907 = 9325361) B9325361
theorem B1531241 : Blo 1020604 1531241 := bstep (se 2 (by rfl) ⟨574215, by rfl⟩ : syracuseStep 1531241 = 1148431) B1148431
theorem B1727851 : Blo 1020604 1727851 := bstep (se 1 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 1727851 = 2591777) B2591777
theorem B1531319 : Blo 1020604 1531319 := bstep (se 1 (by rfl) ⟨1148489, by rfl⟩ : syracuseStep 1531319 = 2296979) B2296979
theorem B1531355 : Blo 1020604 1531355 := bstep (se 1 (by rfl) ⟨1148516, by rfl⟩ : syracuseStep 1531355 = 2297033) B2297033
theorem B6544907 : Blo 1020604 6544907 := bstep (se 1 (by rfl) ⟨4908680, by rfl⟩ : syracuseStep 6544907 = 9817361) B9817361
theorem B2187103 : Blo 1020604 2187103 := bstep (se 1 (by rfl) ⟨1640327, by rfl⟩ : syracuseStep 2187103 = 3280655) B3280655
theorem B1531823 : Blo 1020604 1531823 := bstep (se 1 (by rfl) ⟨1148867, by rfl⟩ : syracuseStep 1531823 = 2297735) B2297735
theorem B1531913 : Blo 1020604 1531913 := bstep (se 2 (by rfl) ⟨574467, by rfl⟩ : syracuseStep 1531913 = 1148935) B1148935
theorem B39247901 : Blo 1020604 39247901 := bstep (se 3 (by rfl) ⟨7358981, by rfl⟩ : syracuseStep 39247901 = 14717963) B14717963
theorem B1531943 : Blo 1020604 1531943 := bstep (se 1 (by rfl) ⟨1148957, by rfl⟩ : syracuseStep 1531943 = 2297915) B2297915
theorem B1532027 : Blo 1020604 1532027 := bstep (se 1 (by rfl) ⟨1149020, by rfl⟩ : syracuseStep 1532027 = 2298041) B2298041
theorem B1532153 : Blo 1020604 1532153 := bstep (se 2 (by rfl) ⟨574557, by rfl⟩ : syracuseStep 1532153 = 1149115) B1149115
theorem B5169419 : Blo 1020604 5169419 := bstep (se 1 (by rfl) ⟨3877064, by rfl⟩ : syracuseStep 5169419 = 7754129) B7754129
theorem B1532255 : Blo 1020604 1532255 := bstep (se 1 (by rfl) ⟨1149191, by rfl⟩ : syracuseStep 1532255 = 2298383) B2298383
theorem B1532267 : Blo 1020604 1532267 := bstep (se 1 (by rfl) ⟨1149200, by rfl⟩ : syracuseStep 1532267 = 2298401) B2298401
theorem B1728911 : Blo 1020604 1728911 := bstep (se 1 (by rfl) ⟨1296683, by rfl⟩ : syracuseStep 1728911 = 2593367) B2593367
theorem B1532495 : Blo 1020604 1532495 := bstep (se 1 (by rfl) ⟨1149371, by rfl⟩ : syracuseStep 1532495 = 2298743) B2298743
theorem B1532615 : Blo 1020604 1532615 := bstep (se 1 (by rfl) ⟨1149461, by rfl⟩ : syracuseStep 1532615 = 2298923) B2298923
theorem B7365329 : Blo 1020604 7365329 := bstep (se 2 (by rfl) ⟨2761998, by rfl⟩ : syracuseStep 7365329 = 5523997) B5523997
theorem B1532777 : Blo 1020604 1532777 := bstep (se 2 (by rfl) ⟨574791, by rfl⟩ : syracuseStep 1532777 = 1149583) B1149583
theorem B1532855 : Blo 1020604 1532855 := bstep (se 1 (by rfl) ⟨1149641, by rfl⟩ : syracuseStep 1532855 = 2299283) B2299283
theorem B1532891 : Blo 1020604 1532891 := bstep (se 1 (by rfl) ⟨1149668, by rfl⟩ : syracuseStep 1532891 = 2299337) B2299337
theorem B19948589 : Blo 1020604 19948589 := bstep (se 3 (by rfl) ⟨3740360, by rfl⟩ : syracuseStep 19948589 = 7480721) B7480721
theorem B4482127 : Blo 1020604 4482127 := bstep (se 1 (by rfl) ⟨3361595, by rfl⟩ : syracuseStep 4482127 = 6723191) B6723191
theorem B1533359 : Blo 1020604 1533359 := bstep (se 1 (by rfl) ⟨1150019, by rfl⟩ : syracuseStep 1533359 = 2300039) B2300039
theorem B18703817 : Blo 1020604 18703817 := bstep (se 2 (by rfl) ⟨7013931, by rfl⟩ : syracuseStep 18703817 = 14027863) B14027863
theorem B1533449 : Blo 1020604 1533449 := bstep (se 2 (by rfl) ⟨575043, by rfl⟩ : syracuseStep 1533449 = 1150087) B1150087
theorem B1533479 : Blo 1020604 1533479 := bstep (se 1 (by rfl) ⟨1150109, by rfl⟩ : syracuseStep 1533479 = 2300219) B2300219
theorem B1533563 : Blo 1020604 1533563 := bstep (se 1 (by rfl) ⟨1150172, by rfl⟩ : syracuseStep 1533563 = 2300345) B2300345
theorem B5170877 : Blo 1020604 5170877 := bstep (se 3 (by rfl) ⟨969539, by rfl⟩ : syracuseStep 5170877 = 1939079) B1939079
theorem B1533689 : Blo 1020604 1533689 := bstep (se 2 (by rfl) ⟨575133, by rfl⟩ : syracuseStep 1533689 = 1150267) B1150267
theorem B11069227 : Blo 1020604 11069227 := bstep (se 1 (by rfl) ⟨8301920, by rfl⟩ : syracuseStep 11069227 = 16603841) B16603841
theorem B5171039 : Blo 1020604 5171039 := bstep (se 1 (by rfl) ⟨3878279, by rfl⟩ : syracuseStep 5171039 = 7756559) B7756559
theorem B1533791 : Blo 1020604 1533791 := bstep (se 1 (by rfl) ⟨1150343, by rfl⟩ : syracuseStep 1533791 = 2300687) B2300687
theorem B1533803 : Blo 1020604 1533803 := bstep (se 1 (by rfl) ⟨1150352, by rfl⟩ : syracuseStep 1533803 = 2300705) B2300705
theorem B22439873 : Blo 1020604 22439873 := bstep (se 2 (by rfl) ⟨8414952, by rfl⟩ : syracuseStep 22439873 = 16829905) B16829905
theorem B1534031 : Blo 1020604 1534031 := bstep (se 1 (by rfl) ⟨1150523, by rfl⟩ : syracuseStep 1534031 = 2301047) B2301047
theorem B7759961 : Blo 1020604 7759961 := bstep (se 2 (by rfl) ⟨2909985, by rfl⟩ : syracuseStep 7759961 = 5819971) B5819971
theorem B1108091 : Blo 1020604 1108091 := bstep (se 1 (by rfl) ⟨831068, by rfl⟩ : syracuseStep 1108091 = 1662137) B1662137
theorem B17688709 : Blo 1020604 17688709 := bstep (se 4 (by rfl) ⟨1658316, by rfl⟩ : syracuseStep 17688709 = 3316633) B3316633
theorem B1534151 : Blo 1020604 1534151 := bstep (se 1 (by rfl) ⟨1150613, by rfl⟩ : syracuseStep 1534151 = 2301227) B2301227
theorem B1534313 : Blo 1020604 1534313 := bstep (se 2 (by rfl) ⟨575367, by rfl⟩ : syracuseStep 1534313 = 1150735) B1150735
theorem B11659625 : Blo 1020604 11659625 := bstep (se 2 (by rfl) ⟨4372359, by rfl⟩ : syracuseStep 11659625 = 8744719) B8744719
theorem B1534391 : Blo 1020604 1534391 := bstep (se 1 (by rfl) ⟨1150793, by rfl⟩ : syracuseStep 1534391 = 2301587) B2301587
theorem B13101497 : Blo 1020604 13101497 := bstep (se 2 (by rfl) ⟨4913061, by rfl⟩ : syracuseStep 13101497 = 9826123) B9826123
theorem B1534427 : Blo 1020604 1534427 := bstep (se 1 (by rfl) ⟨1150820, by rfl⟩ : syracuseStep 1534427 = 2301641) B2301641
theorem B1534895 : Blo 1020604 1534895 := bstep (se 1 (by rfl) ⟨1151171, by rfl⟩ : syracuseStep 1534895 = 2302343) B2302343
theorem B1534985 : Blo 1020604 1534985 := bstep (se 2 (by rfl) ⟨575619, by rfl⟩ : syracuseStep 1534985 = 1151239) B1151239
theorem B1535015 : Blo 1020604 1535015 := bstep (se 1 (by rfl) ⟨1151261, by rfl⟩ : syracuseStep 1535015 = 2302523) B2302523
theorem B1535099 : Blo 1020604 1535099 := bstep (se 1 (by rfl) ⟨1151324, by rfl⟩ : syracuseStep 1535099 = 2302649) B2302649
theorem B5827787 : Blo 1020604 5827787 := bstep (se 1 (by rfl) ⟨4370840, by rfl⟩ : syracuseStep 5827787 = 8741681) B8741681
theorem B1535225 : Blo 1020604 1535225 := bstep (se 2 (by rfl) ⟨575709, by rfl⟩ : syracuseStep 1535225 = 1151419) B1151419
theorem B1535327 : Blo 1020604 1535327 := bstep (se 1 (by rfl) ⟨1151495, by rfl⟩ : syracuseStep 1535327 = 2302991) B2302991
theorem B1535339 : Blo 1020604 1535339 := bstep (se 1 (by rfl) ⟨1151504, by rfl⟩ : syracuseStep 1535339 = 2303009) B2303009
theorem B7761419 : Blo 1020604 7761419 := bstep (se 1 (by rfl) ⟨5821064, by rfl⟩ : syracuseStep 7761419 = 11642129) B11642129
theorem B1535567 : Blo 1020604 1535567 := bstep (se 1 (by rfl) ⟨1151675, by rfl⟩ : syracuseStep 1535567 = 2303351) B2303351
theorem B5828219 : Blo 1020604 5828219 := bstep (se 1 (by rfl) ⟨4371164, by rfl⟩ : syracuseStep 5828219 = 8742329) B8742329
theorem B1535687 : Blo 1020604 1535687 := bstep (se 1 (by rfl) ⟨1151765, by rfl⟩ : syracuseStep 1535687 = 2303531) B2303531
theorem B1535849 : Blo 1020604 1535849 := bstep (se 2 (by rfl) ⟨575943, by rfl⟩ : syracuseStep 1535849 = 1151887) B1151887
theorem B1535927 : Blo 1020604 1535927 := bstep (se 1 (by rfl) ⟨1151945, by rfl⟩ : syracuseStep 1535927 = 2303891) B2303891
theorem B2584507 : Blo 1020604 2584507 := bstep (se 1 (by rfl) ⟨1938380, by rfl⟩ : syracuseStep 2584507 = 3876761) B3876761
theorem B1535963 : Blo 1020604 1535963 := bstep (se 1 (by rfl) ⟨1151972, by rfl⟩ : syracuseStep 1535963 = 2303945) B2303945
theorem B7860239 : Blo 1020604 7860239 := bstep (se 1 (by rfl) ⟨5895179, by rfl⟩ : syracuseStep 7860239 = 11790359) B11790359
theorem B5828993 : Blo 1020604 5828993 := bstep (se 2 (by rfl) ⟨2185872, by rfl⟩ : syracuseStep 5828993 = 4371745) B4371745
theorem B1536431 : Blo 1020604 1536431 := bstep (se 1 (by rfl) ⟨1152323, by rfl⟩ : syracuseStep 1536431 = 2304647) B2304647
theorem B1536521 : Blo 1020604 1536521 := bstep (se 2 (by rfl) ⟨576195, by rfl⟩ : syracuseStep 1536521 = 1152391) B1152391
theorem B5173793 : Blo 1020604 5173793 := bstep (se 2 (by rfl) ⟨1940172, by rfl⟩ : syracuseStep 5173793 = 3880345) B3880345
theorem B1536551 : Blo 1020604 1536551 := bstep (se 1 (by rfl) ⟨1152413, by rfl⟩ : syracuseStep 1536551 = 2304827) B2304827
theorem B1536635 : Blo 1020604 1536635 := bstep (se 1 (by rfl) ⟨1152476, by rfl⟩ : syracuseStep 1536635 = 2304953) B2304953
theorem B1536761 : Blo 1020604 1536761 := bstep (se 2 (by rfl) ⟨576285, by rfl⟩ : syracuseStep 1536761 = 1152571) B1152571
theorem B1536863 : Blo 1020604 1536863 := bstep (se 1 (by rfl) ⟨1152647, by rfl⟩ : syracuseStep 1536863 = 2305295) B2305295
theorem B1536875 : Blo 1020604 1536875 := bstep (se 1 (by rfl) ⟨1152656, by rfl⟩ : syracuseStep 1536875 = 2305313) B2305313
theorem B3273659 : Blo 1020604 3273659 := bstep (se 1 (by rfl) ⟨2455244, by rfl⟩ : syracuseStep 3273659 = 4910489) B4910489
theorem B1635407 : Blo 1020604 1635407 := bstep (se 1 (by rfl) ⟨1226555, by rfl⟩ : syracuseStep 1635407 = 2453111) B2453111
theorem B1635689 : Blo 1020604 1635689 := bstep (se 2 (by rfl) ⟨613383, by rfl⟩ : syracuseStep 1635689 = 1226767) B1226767
theorem B7763363 : Blo 1020604 7763363 := bstep (se 1 (by rfl) ⟨5822522, by rfl⟩ : syracuseStep 7763363 = 11645045) B11645045
theorem B3274273 : Blo 1020604 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B35452673 : Blo 1020604 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B1636201 : Blo 1020604 1636201 := bstep (se 2 (by rfl) ⟨613575, by rfl⟩ : syracuseStep 1636201 = 1227151) B1227151
theorem B14743457 : Blo 1020604 14743457 := bstep (se 2 (by rfl) ⟨5528796, by rfl⟩ : syracuseStep 14743457 = 11057593) B11057593
theorem B3274759 : Blo 1020604 3274759 := bstep (se 1 (by rfl) ⟨2456069, by rfl⟩ : syracuseStep 3274759 = 4912139) B4912139
theorem B2455571 : Blo 1020604 2455571 := bstep (se 1 (by rfl) ⟨1841678, by rfl⟩ : syracuseStep 2455571 = 3683357) B3683357
theorem B2455609 : Blo 1020604 2455609 := bstep (se 2 (by rfl) ⟨920853, by rfl⟩ : syracuseStep 2455609 = 1841707) B1841707
theorem B2587099 : Blo 1020604 2587099 := bstep (se 1 (by rfl) ⟨1940324, by rfl⟩ : syracuseStep 2587099 = 3880649) B3880649
theorem B2947799 : Blo 1020604 2947799 := bstep (se 1 (by rfl) ⟨2210849, by rfl⟩ : syracuseStep 2947799 = 4421699) B4421699
theorem B5831453 : Blo 1020604 5831453 := bstep (se 3 (by rfl) ⟨1093397, by rfl⟩ : syracuseStep 5831453 = 2186795) B2186795
theorem B2489183 : Blo 1020604 2489183 := bstep (se 1 (by rfl) ⟨1866887, by rfl⟩ : syracuseStep 2489183 = 3733775) B3733775
theorem B16579511 : Blo 1020604 16579511 := bstep (se 1 (by rfl) ⟨12434633, by rfl⟩ : syracuseStep 16579511 = 24869267) B24869267
theorem B2587727 : Blo 1020604 2587727 := bstep (se 1 (by rfl) ⟨1940795, by rfl⟩ : syracuseStep 2587727 = 3881591) B3881591
theorem B4914371 : Blo 1020604 4914371 := bstep (se 1 (by rfl) ⟨3685778, by rfl⟩ : syracuseStep 4914371 = 7371557) B7371557
theorem B3276119 : Blo 1020604 3276119 := bstep (se 1 (by rfl) ⟨2457089, by rfl⟩ : syracuseStep 3276119 = 4914179) B4914179
theorem B5176871 : Blo 1020604 5176871 := bstep (se 1 (by rfl) ⟨3882653, by rfl⟩ : syracuseStep 5176871 = 7765307) B7765307
theorem B2588375 : Blo 1020604 2588375 := bstep (se 1 (by rfl) ⟨1941281, by rfl⟩ : syracuseStep 2588375 = 3882563) B3882563
theorem B3276503 : Blo 1020604 3276503 := bstep (se 1 (by rfl) ⟨2457377, by rfl⟩ : syracuseStep 3276503 = 4914755) B4914755
theorem B7765793 : Blo 1020604 7765793 := bstep (se 2 (by rfl) ⟨2912172, by rfl⟩ : syracuseStep 7765793 = 5824345) B5824345
theorem B10485571 : Blo 1020604 10485571 := bstep (se 1 (by rfl) ⟨7864178, by rfl⟩ : syracuseStep 10485571 = 15728357) B15728357
theorem B6553619 : Blo 1020604 6553619 := bstep (se 1 (by rfl) ⟨4915214, by rfl⟩ : syracuseStep 6553619 = 9830429) B9830429
theorem B17465381 : Blo 1020604 17465381 := bstep (se 4 (by rfl) ⟨1637379, by rfl⟩ : syracuseStep 17465381 = 3274759) B3274759
theorem B8749093 : Blo 1020604 8749093 := bstep (se 4 (by rfl) ⟨820227, by rfl⟩ : syracuseStep 8749093 = 1640455) B1640455
theorem B2916935 : Blo 1020604 2916935 := bstep (se 1 (by rfl) ⟨2187701, by rfl⟩ : syracuseStep 2916935 = 4375403) B4375403
theorem B2589367 : Blo 1020604 2589367 := bstep (se 1 (by rfl) ⟨1942025, by rfl⟩ : syracuseStep 2589367 = 3884051) B3884051
theorem B5538527 : Blo 1020604 5538527 := bstep (se 1 (by rfl) ⟨4153895, by rfl⟩ : syracuseStep 5538527 = 8307791) B8307791
theorem B2589671 : Blo 1020604 2589671 := bstep (se 1 (by rfl) ⟨1942253, by rfl⟩ : syracuseStep 2589671 = 3884507) B3884507
theorem B2917367 : Blo 1020604 2917367 := bstep (se 1 (by rfl) ⟨2188025, by rfl⟩ : syracuseStep 2917367 = 4376051) B4376051
theorem B4916369 : Blo 1020604 4916369 := bstep (se 2 (by rfl) ⟨1843638, by rfl⟩ : syracuseStep 4916369 = 3687277) B3687277
theorem B5244061 : Blo 1020604 5244061 := bstep (se 3 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 5244061 = 1966523) B1966523
theorem B4359511 : Blo 1020604 4359511 := bstep (se 1 (by rfl) ⟨3269633, by rfl⟩ : syracuseStep 4359511 = 6539267) B6539267
theorem B1148251 : Blo 1020604 1148251 := bstep (se 1 (by rfl) ⟨861188, by rfl⟩ : syracuseStep 1148251 = 1722377) B1722377
theorem B1148359 : Blo 1020604 1148359 := bstep (se 1 (by rfl) ⟨861269, by rfl⟩ : syracuseStep 1148359 = 1722539) B1722539
theorem B1148719 : Blo 1020604 1148719 := bstep (se 1 (by rfl) ⟨861539, by rfl⟩ : syracuseStep 1148719 = 1723079) B1723079
theorem B2459521 : Blo 1020604 2459521 := bstep (se 2 (by rfl) ⟨922320, by rfl⟩ : syracuseStep 2459521 = 1844641) B1844641
theorem B1148827 : Blo 1020604 1148827 := bstep (se 1 (by rfl) ⟨861620, by rfl⟩ : syracuseStep 1148827 = 1723241) B1723241
theorem B2590825 : Blo 1020604 2590825 := bstep (se 2 (by rfl) ⟨971559, by rfl⟩ : syracuseStep 2590825 = 1943119) B1943119
theorem B2459753 : Blo 1020604 2459753 := bstep (se 2 (by rfl) ⟨922407, by rfl⟩ : syracuseStep 2459753 = 1844815) B1844815
theorem B1149223 : Blo 1020604 1149223 := bstep (se 1 (by rfl) ⟨861917, by rfl⟩ : syracuseStep 1149223 = 1723835) B1723835
theorem B1149295 : Blo 1020604 1149295 := bstep (se 1 (by rfl) ⟨861971, by rfl⟩ : syracuseStep 1149295 = 1723943) B1723943
theorem B1149511 : Blo 1020604 1149511 := bstep (se 1 (by rfl) ⟨862133, by rfl⟩ : syracuseStep 1149511 = 1724267) B1724267
theorem B2591311 : Blo 1020604 2591311 := bstep (se 1 (by rfl) ⟨1943483, by rfl⟩ : syracuseStep 2591311 = 3886967) B3886967
theorem B8751827 : Blo 1020604 8751827 := bstep (se 1 (by rfl) ⟨6563870, by rfl⟩ : syracuseStep 8751827 = 13127741) B13127741
theorem B2296655 : Blo 1020604 2296655 := bstep (se 1 (by rfl) ⟨1722491, by rfl⟩ : syracuseStep 2296655 = 3444983) B3444983
theorem B2296871 : Blo 1020604 2296871 := bstep (se 1 (by rfl) ⟨1722653, by rfl⟩ : syracuseStep 2296871 = 3445307) B3445307
theorem B2591959 : Blo 1020604 2591959 := bstep (se 1 (by rfl) ⟨1943969, by rfl⟩ : syracuseStep 2591959 = 3887939) B3887939
theorem B2297051 : Blo 1020604 2297051 := bstep (se 1 (by rfl) ⟨1722788, by rfl⟩ : syracuseStep 2297051 = 3445577) B3445577
theorem B2493791 : Blo 1020604 2493791 := bstep (se 1 (by rfl) ⟨1870343, by rfl⟩ : syracuseStep 2493791 = 3740687) B3740687
theorem B21237137 : Blo 1020604 21237137 := bstep (se 2 (by rfl) ⟨7963926, by rfl⟩ : syracuseStep 21237137 = 15927853) B15927853
theorem B2297249 : Blo 1020604 2297249 := bstep (se 2 (by rfl) ⟨861468, by rfl⟩ : syracuseStep 2297249 = 1722937) B1722937
theorem B1150375 : Blo 1020604 1150375 := bstep (se 1 (by rfl) ⟨862781, by rfl⟩ : syracuseStep 1150375 = 1725563) B1725563
theorem B5180921 : Blo 1020604 5180921 := bstep (se 2 (by rfl) ⟨1942845, by rfl⟩ : syracuseStep 5180921 = 3885691) B3885691
theorem B2592263 : Blo 1020604 2592263 := bstep (se 1 (by rfl) ⟨1944197, by rfl⟩ : syracuseStep 2592263 = 3888395) B3888395
theorem B2461241 : Blo 1020604 2461241 := bstep (se 2 (by rfl) ⟨922965, by rfl⟩ : syracuseStep 2461241 = 1845931) B1845931
theorem B5181245 : Blo 1020604 5181245 := bstep (se 3 (by rfl) ⟨971483, by rfl⟩ : syracuseStep 5181245 = 1942967) B1942967
theorem B2330473 : Blo 1020604 2330473 := bstep (se 2 (by rfl) ⟨873927, by rfl⟩ : syracuseStep 2330473 = 1747855) B1747855
theorem B2297807 : Blo 1020604 2297807 := bstep (se 1 (by rfl) ⟨1723355, by rfl⟩ : syracuseStep 2297807 = 3446711) B3446711
theorem B2592719 : Blo 1020604 2592719 := bstep (se 1 (by rfl) ⟨1944539, by rfl⟩ : syracuseStep 2592719 = 3889079) B3889079
theorem B1150951 : Blo 1020604 1150951 := bstep (se 1 (by rfl) ⟨863213, by rfl⟩ : syracuseStep 1150951 = 1726427) B1726427
theorem B2298185 : Blo 1020604 2298185 := bstep (se 2 (by rfl) ⟨861819, by rfl⟩ : syracuseStep 2298185 = 1723639) B1723639
theorem B2298203 : Blo 1020604 2298203 := bstep (se 1 (by rfl) ⟨1723652, by rfl⟩ : syracuseStep 2298203 = 3447305) B3447305
theorem B2593235 : Blo 1020604 2593235 := bstep (se 1 (by rfl) ⟨1944926, by rfl⟩ : syracuseStep 2593235 = 3889853) B3889853
theorem B1839689 : Blo 1020604 1839689 := bstep (se 2 (by rfl) ⟨689883, by rfl⟩ : syracuseStep 1839689 = 1379767) B1379767
theorem B1020639 : Blo 1020604 1020639 := bstep (se 1 (by rfl) ⟨765479, by rfl⟩ : syracuseStep 1020639 = 1530959) B1530959
theorem B10654507 : Blo 1020604 10654507 := bstep (se 1 (by rfl) ⟨7990880, by rfl⟩ : syracuseStep 10654507 = 15981761) B15981761
theorem B1020719 : Blo 1020604 1020719 := bstep (se 1 (by rfl) ⟨765539, by rfl⟩ : syracuseStep 1020719 = 1531079) B1531079
theorem B1020827 : Blo 1020604 1020827 := bstep (se 1 (by rfl) ⟨765620, by rfl⟩ : syracuseStep 1020827 = 1531241) B1531241
theorem B2298779 : Blo 1020604 2298779 := bstep (se 1 (by rfl) ⟨1724084, by rfl⟩ : syracuseStep 2298779 = 3448169) B3448169
theorem B1020879 : Blo 1020604 1020879 := bstep (se 1 (by rfl) ⟨765659, by rfl⟩ : syracuseStep 1020879 = 1531319) B1531319
theorem B1020903 : Blo 1020604 1020903 := bstep (se 1 (by rfl) ⟨765677, by rfl⟩ : syracuseStep 1020903 = 1531355) B1531355
theorem B4363271 : Blo 1020604 4363271 := bstep (se 1 (by rfl) ⟨3272453, by rfl⟩ : syracuseStep 4363271 = 6544907) B6544907
theorem B2298977 : Blo 1020604 2298977 := bstep (se 2 (by rfl) ⟨862116, by rfl⟩ : syracuseStep 2298977 = 1724233) B1724233
theorem B9311377 : Blo 1020604 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B59839661 : Blo 1020604 59839661 := bstep (se 3 (by rfl) ⟨11219936, by rfl⟩ : syracuseStep 59839661 = 22439873) B22439873
theorem B3446009 : Blo 1020604 3446009 := bstep (se 2 (by rfl) ⟨1292253, by rfl⟩ : syracuseStep 3446009 = 2584507) B2584507
theorem B1021215 : Blo 1020604 1021215 := bstep (se 1 (by rfl) ⟨765911, by rfl⟩ : syracuseStep 1021215 = 1531823) B1531823
theorem B2299175 : Blo 1020604 2299175 := bstep (se 1 (by rfl) ⟨1724381, by rfl⟩ : syracuseStep 2299175 = 3448763) B3448763
theorem B1021275 : Blo 1020604 1021275 := bstep (se 1 (by rfl) ⟨765956, by rfl⟩ : syracuseStep 1021275 = 1531913) B1531913
theorem B1021295 : Blo 1020604 1021295 := bstep (se 1 (by rfl) ⟨765971, by rfl⟩ : syracuseStep 1021295 = 1531943) B1531943
theorem B1021351 : Blo 1020604 1021351 := bstep (se 1 (by rfl) ⟨766013, by rfl⟩ : syracuseStep 1021351 = 1532027) B1532027
theorem B1840583 : Blo 1020604 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B1021435 : Blo 1020604 1021435 := bstep (se 1 (by rfl) ⟨766076, by rfl⟩ : syracuseStep 1021435 = 1532153) B1532153
theorem B3446279 : Blo 1020604 3446279 := bstep (se 1 (by rfl) ⟨2584709, by rfl⟩ : syracuseStep 3446279 = 5169419) B5169419
theorem B1021503 : Blo 1020604 1021503 := bstep (se 1 (by rfl) ⟨766127, by rfl⟩ : syracuseStep 1021503 = 1532255) B1532255
theorem B1381951 : Blo 1020604 1381951 := bstep (se 1 (by rfl) ⟨1036463, by rfl⟩ : syracuseStep 1381951 = 2072927) B2072927
theorem B1021511 : Blo 1020604 1021511 := bstep (se 1 (by rfl) ⟨766133, by rfl⟩ : syracuseStep 1021511 = 1532267) B1532267
theorem B1152607 : Blo 1020604 1152607 := bstep (se 1 (by rfl) ⟨864455, by rfl⟩ : syracuseStep 1152607 = 1728911) B1728911
theorem B2954909 : Blo 1020604 2954909 := bstep (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) B1108091
theorem B2299553 : Blo 1020604 2299553 := bstep (se 2 (by rfl) ⟨862332, by rfl⟩ : syracuseStep 2299553 = 1724665) B1724665
theorem B1021663 : Blo 1020604 1021663 := bstep (se 1 (by rfl) ⟨766247, by rfl⟩ : syracuseStep 1021663 = 1532495) B1532495
theorem B1021743 : Blo 1020604 1021743 := bstep (se 1 (by rfl) ⟨766307, by rfl⟩ : syracuseStep 1021743 = 1532615) B1532615
theorem B1021851 : Blo 1020604 1021851 := bstep (se 1 (by rfl) ⟨766388, by rfl⟩ : syracuseStep 1021851 = 1532777) B1532777
theorem B1021903 : Blo 1020604 1021903 := bstep (se 1 (by rfl) ⟨766427, by rfl⟩ : syracuseStep 1021903 = 1532855) B1532855
theorem B1021927 : Blo 1020604 1021927 := bstep (se 1 (by rfl) ⟨766445, by rfl⟩ : syracuseStep 1021927 = 1532891) B1532891
theorem B2299913 : Blo 1020604 2299913 := bstep (se 2 (by rfl) ⟨862467, by rfl⟩ : syracuseStep 2299913 = 1724935) B1724935
theorem B1382665 : Blo 1020604 1382665 := bstep (se 2 (by rfl) ⟨518499, by rfl⟩ : syracuseStep 1382665 = 1036999) B1036999
theorem B1022239 : Blo 1020604 1022239 := bstep (se 1 (by rfl) ⟨766679, by rfl⟩ : syracuseStep 1022239 = 1533359) B1533359
theorem B1022299 : Blo 1020604 1022299 := bstep (se 1 (by rfl) ⟨766724, by rfl⟩ : syracuseStep 1022299 = 1533449) B1533449
theorem B1022319 : Blo 1020604 1022319 := bstep (se 1 (by rfl) ⟨766739, by rfl⟩ : syracuseStep 1022319 = 1533479) B1533479
theorem B2300327 : Blo 1020604 2300327 := bstep (se 1 (by rfl) ⟨1725245, by rfl⟩ : syracuseStep 2300327 = 3450491) B3450491
theorem B1022375 : Blo 1020604 1022375 := bstep (se 1 (by rfl) ⟨766781, by rfl⟩ : syracuseStep 1022375 = 1533563) B1533563
theorem B2759123 : Blo 1020604 2759123 := bstep (se 1 (by rfl) ⟨2069342, by rfl⟩ : syracuseStep 2759123 = 4138685) B4138685
theorem B3447251 : Blo 1020604 3447251 := bstep (se 1 (by rfl) ⟨2585438, by rfl⟩ : syracuseStep 3447251 = 5170877) B5170877
theorem B1022459 : Blo 1020604 1022459 := bstep (se 1 (by rfl) ⟨766844, by rfl⟩ : syracuseStep 1022459 = 1533689) B1533689
theorem B2300435 : Blo 1020604 2300435 := bstep (se 1 (by rfl) ⟨1725326, by rfl⟩ : syracuseStep 2300435 = 3450653) B3450653
theorem B3447359 : Blo 1020604 3447359 := bstep (se 1 (by rfl) ⟨2585519, by rfl⟩ : syracuseStep 3447359 = 5171039) B5171039
theorem B1022527 : Blo 1020604 1022527 := bstep (se 1 (by rfl) ⟨766895, by rfl⟩ : syracuseStep 1022527 = 1533791) B1533791
theorem B1022535 : Blo 1020604 1022535 := bstep (se 1 (by rfl) ⟨766901, by rfl⟩ : syracuseStep 1022535 = 1533803) B1533803
theorem B2300489 : Blo 1020604 2300489 := bstep (se 2 (by rfl) ⟨862683, by rfl⟩ : syracuseStep 2300489 = 1725367) B1725367
theorem B14195317 : Blo 1020604 14195317 := bstep (se 5 (by rfl) ⟨665405, by rfl⟩ : syracuseStep 14195317 = 1330811) B1330811
theorem B1022687 : Blo 1020604 1022687 := bstep (se 1 (by rfl) ⟨767015, by rfl⟩ : syracuseStep 1022687 = 1534031) B1534031
theorem B1022767 : Blo 1020604 1022767 := bstep (se 1 (by rfl) ⟨767075, by rfl⟩ : syracuseStep 1022767 = 1534151) B1534151
theorem B5184323 : Blo 1020604 5184323 := bstep (se 1 (by rfl) ⟨3888242, by rfl⟩ : syracuseStep 5184323 = 7776485) B7776485
theorem B5905295 : Blo 1020604 5905295 := bstep (se 1 (by rfl) ⟨4428971, by rfl⟩ : syracuseStep 5905295 = 8857943) B8857943
theorem B1022875 : Blo 1020604 1022875 := bstep (se 1 (by rfl) ⟨767156, by rfl⟩ : syracuseStep 1022875 = 1534313) B1534313
theorem B7773083 : Blo 1020604 7773083 := bstep (se 1 (by rfl) ⟨5829812, by rfl⟩ : syracuseStep 7773083 = 11659625) B11659625
theorem B1022927 : Blo 1020604 1022927 := bstep (se 1 (by rfl) ⟨767195, by rfl⟩ : syracuseStep 1022927 = 1534391) B1534391
theorem B2300903 : Blo 1020604 2300903 := bstep (se 1 (by rfl) ⟨1725677, by rfl⟩ : syracuseStep 2300903 = 3451355) B3451355
theorem B1022951 : Blo 1020604 1022951 := bstep (se 1 (by rfl) ⟨767213, by rfl⟩ : syracuseStep 1022951 = 1534427) B1534427
theorem B1383529 : Blo 1020604 1383529 := bstep (se 2 (by rfl) ⟨518823, by rfl⟩ : syracuseStep 1383529 = 1037647) B1037647
theorem B2759869 : Blo 1020604 2759869 := bstep (se 3 (by rfl) ⟨517475, by rfl⟩ : syracuseStep 2759869 = 1034951) B1034951
theorem B1023263 : Blo 1020604 1023263 := bstep (se 1 (by rfl) ⟨767447, by rfl⟩ : syracuseStep 1023263 = 1534895) B1534895
theorem B1023323 : Blo 1020604 1023323 := bstep (se 1 (by rfl) ⟨767492, by rfl⟩ : syracuseStep 1023323 = 1534985) B1534985
theorem B2301281 : Blo 1020604 2301281 := bstep (se 2 (by rfl) ⟨862980, by rfl⟩ : syracuseStep 2301281 = 1725961) B1725961
theorem B1023343 : Blo 1020604 1023343 := bstep (se 1 (by rfl) ⟨767507, by rfl⟩ : syracuseStep 1023343 = 1535015) B1535015
theorem B4365697 : Blo 1020604 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B1023399 : Blo 1020604 1023399 := bstep (se 1 (by rfl) ⟨767549, by rfl⟩ : syracuseStep 1023399 = 1535099) B1535099
theorem B2301371 : Blo 1020604 2301371 := bstep (se 1 (by rfl) ⟨1726028, by rfl⟩ : syracuseStep 2301371 = 3452057) B3452057
theorem B1023483 : Blo 1020604 1023483 := bstep (se 1 (by rfl) ⟨767612, by rfl⟩ : syracuseStep 1023483 = 1535225) B1535225
theorem B12459545 : Blo 1020604 12459545 := bstep (se 2 (by rfl) ⟨4672329, by rfl⟩ : syracuseStep 12459545 = 9344659) B9344659
theorem B2301497 : Blo 1020604 2301497 := bstep (se 2 (by rfl) ⟨863061, by rfl⟩ : syracuseStep 2301497 = 1726123) B1726123
theorem B1023551 : Blo 1020604 1023551 := bstep (se 1 (by rfl) ⟨767663, by rfl⟩ : syracuseStep 1023551 = 1535327) B1535327
theorem B1023559 : Blo 1020604 1023559 := bstep (se 1 (by rfl) ⟨767669, by rfl⟩ : syracuseStep 1023559 = 1535339) B1535339
theorem B5185133 : Blo 1020604 5185133 := bstep (se 3 (by rfl) ⟨972212, by rfl⟩ : syracuseStep 5185133 = 1944425) B1944425
theorem B2563745 : Blo 1020604 2563745 := bstep (se 2 (by rfl) ⟨961404, by rfl⟩ : syracuseStep 2563745 = 1922809) B1922809
theorem B1023711 : Blo 1020604 1023711 := bstep (se 1 (by rfl) ⟨767783, by rfl⟩ : syracuseStep 1023711 = 1535567) B1535567
theorem B1023791 : Blo 1020604 1023791 := bstep (se 1 (by rfl) ⟨767843, by rfl⟩ : syracuseStep 1023791 = 1535687) B1535687
theorem B1023899 : Blo 1020604 1023899 := bstep (se 1 (by rfl) ⟨767924, by rfl⟩ : syracuseStep 1023899 = 1535849) B1535849
theorem B1023951 : Blo 1020604 1023951 := bstep (se 1 (by rfl) ⟨767963, by rfl⟩ : syracuseStep 1023951 = 1535927) B1535927
theorem B1023975 : Blo 1020604 1023975 := bstep (se 1 (by rfl) ⟨767981, by rfl⟩ : syracuseStep 1023975 = 1535963) B1535963
theorem B4923443 : Blo 1020604 4923443 := bstep (se 1 (by rfl) ⟨3692582, by rfl⟩ : syracuseStep 4923443 = 7385165) B7385165
theorem B22126769 : Blo 1020604 22126769 := bstep (se 2 (by rfl) ⟨8297538, by rfl⟩ : syracuseStep 22126769 = 16595077) B16595077
theorem B2302163 : Blo 1020604 2302163 := bstep (se 1 (by rfl) ⟨1726622, by rfl⟩ : syracuseStep 2302163 = 3453245) B3453245
theorem B2302217 : Blo 1020604 2302217 := bstep (se 2 (by rfl) ⟨863331, by rfl⟩ : syracuseStep 2302217 = 1726663) B1726663
theorem B1024287 : Blo 1020604 1024287 := bstep (se 1 (by rfl) ⟨768215, by rfl⟩ : syracuseStep 1024287 = 1536431) B1536431
theorem B22094167 : Blo 1020604 22094167 := bstep (se 1 (by rfl) ⟨16570625, by rfl⟩ : syracuseStep 22094167 = 33141251) B33141251
theorem B1024347 : Blo 1020604 1024347 := bstep (se 1 (by rfl) ⟨768260, by rfl⟩ : syracuseStep 1024347 = 1536521) B1536521
theorem B3449195 : Blo 1020604 3449195 := bstep (se 1 (by rfl) ⟨2586896, by rfl⟩ : syracuseStep 3449195 = 5173793) B5173793
theorem B1024367 : Blo 1020604 1024367 := bstep (se 1 (by rfl) ⟨768275, by rfl⟩ : syracuseStep 1024367 = 1536551) B1536551
theorem B1024423 : Blo 1020604 1024423 := bstep (se 1 (by rfl) ⟨768317, by rfl⟩ : syracuseStep 1024423 = 1536635) B1536635
theorem B2302433 : Blo 1020604 2302433 := bstep (se 2 (by rfl) ⟨863412, by rfl⟩ : syracuseStep 2302433 = 1726825) B1726825
theorem B1024507 : Blo 1020604 1024507 := bstep (se 1 (by rfl) ⟨768380, by rfl⟩ : syracuseStep 1024507 = 1536761) B1536761
theorem B1024575 : Blo 1020604 1024575 := bstep (se 1 (by rfl) ⟨768431, by rfl⟩ : syracuseStep 1024575 = 1536863) B1536863
theorem B1024583 : Blo 1020604 1024583 := bstep (se 1 (by rfl) ⟨768437, by rfl⟩ : syracuseStep 1024583 = 1536875) B1536875
theorem B3449465 : Blo 1020604 3449465 := bstep (se 2 (by rfl) ⟨1293549, by rfl⟩ : syracuseStep 3449465 = 2587099) B2587099
theorem B12460715 : Blo 1020604 12460715 := bstep (se 1 (by rfl) ⟨9345536, by rfl⟩ : syracuseStep 12460715 = 18691073) B18691073
theorem B1090271 : Blo 1020604 1090271 := bstep (se 1 (by rfl) ⟨817703, by rfl⟩ : syracuseStep 1090271 = 1635407) B1635407
theorem B2302739 : Blo 1020604 2302739 := bstep (se 1 (by rfl) ⟨1727054, by rfl⟩ : syracuseStep 2302739 = 3454109) B3454109
theorem B6562619 : Blo 1020604 6562619 := bstep (se 1 (by rfl) ⟨4921964, by rfl⟩ : syracuseStep 6562619 = 9843929) B9843929
theorem B1090459 : Blo 1020604 1090459 := bstep (se 1 (by rfl) ⟨817844, by rfl⟩ : syracuseStep 1090459 = 1635689) B1635689
theorem B8856515 : Blo 1020604 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B2303099 : Blo 1020604 2303099 := bstep (se 1 (by rfl) ⟨1727324, by rfl⟩ : syracuseStep 2303099 = 3454649) B3454649
theorem B23635115 : Blo 1020604 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B4138199 : Blo 1020604 4138199 := bstep (se 1 (by rfl) ⟨3103649, by rfl⟩ : syracuseStep 4138199 = 6207299) B6207299
theorem B2303225 : Blo 1020604 2303225 := bstep (se 2 (by rfl) ⟨863709, by rfl⟩ : syracuseStep 2303225 = 1727419) B1727419
theorem B4662623 : Blo 1020604 4662623 := bstep (se 1 (by rfl) ⟨3496967, by rfl⟩ : syracuseStep 4662623 = 6993935) B6993935
theorem B2303369 : Blo 1020604 2303369 := bstep (se 2 (by rfl) ⟨863763, by rfl⟩ : syracuseStep 2303369 = 1727527) B1727527
theorem B2303495 : Blo 1020604 2303495 := bstep (se 1 (by rfl) ⟨1727621, by rfl⟩ : syracuseStep 2303495 = 3455243) B3455243
theorem B10233479 : Blo 1020604 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B2303675 : Blo 1020604 2303675 := bstep (se 1 (by rfl) ⟨1727756, by rfl⟩ : syracuseStep 2303675 = 3455513) B3455513
theorem B2303801 : Blo 1020604 2303801 := bstep (se 2 (by rfl) ⟨863925, by rfl⟩ : syracuseStep 2303801 = 1727851) B1727851
theorem B11053007 : Blo 1020604 11053007 := bstep (se 1 (by rfl) ⟨8289755, by rfl⟩ : syracuseStep 11053007 = 16579511) B16579511
theorem B3451247 : Blo 1020604 3451247 := bstep (se 1 (by rfl) ⟨2588435, by rfl⟩ : syracuseStep 3451247 = 5176871) B5176871
theorem B2304431 : Blo 1020604 2304431 := bstep (se 1 (by rfl) ⟨1728323, by rfl⟩ : syracuseStep 2304431 = 3456647) B3456647
theorem B2304467 : Blo 1020604 2304467 := bstep (se 1 (by rfl) ⟨1728350, by rfl⟩ : syracuseStep 2304467 = 3456701) B3456701
theorem B2304575 : Blo 1020604 2304575 := bstep (se 1 (by rfl) ⟨1728431, by rfl⟩ : syracuseStep 2304575 = 3456863) B3456863
theorem B1944137 : Blo 1020604 1944137 := bstep (se 2 (by rfl) ⟨729051, by rfl⟩ : syracuseStep 1944137 = 1458103) B1458103
theorem B2304683 : Blo 1020604 2304683 := bstep (se 1 (by rfl) ⟨1728512, by rfl⟩ : syracuseStep 2304683 = 3457025) B3457025
theorem B4139947 : Blo 1020604 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B13085711 : Blo 1020604 13085711 := bstep (se 1 (by rfl) ⟨9814283, by rfl⟩ : syracuseStep 13085711 = 19628567) B19628567
theorem B2305223 : Blo 1020604 2305223 := bstep (se 1 (by rfl) ⟨1728917, by rfl⟩ : syracuseStep 2305223 = 3457835) B3457835
theorem B29470067 : Blo 1020604 29470067 := bstep (se 1 (by rfl) ⟨22102550, by rfl⟩ : syracuseStep 29470067 = 44205101) B44205101
theorem B2796923 : Blo 1020604 2796923 := bstep (se 1 (by rfl) ⟨2097692, by rfl⟩ : syracuseStep 2796923 = 4195385) B4195385
theorem B4206163 : Blo 1020604 4206163 := bstep (se 1 (by rfl) ⟨3154622, by rfl⟩ : syracuseStep 4206163 = 6309245) B6309245
theorem B1093295 : Blo 1020604 1093295 := bstep (se 1 (by rfl) ⟨819971, by rfl⟩ : syracuseStep 1093295 = 1639943) B1639943
theorem B3452651 : Blo 1020604 3452651 := bstep (se 1 (by rfl) ⟨2589488, by rfl⟩ : syracuseStep 3452651 = 5178977) B5178977
theorem B9843119 : Blo 1020604 9843119 := bstep (se 1 (by rfl) ⟨7382339, by rfl⟩ : syracuseStep 9843119 = 14764679) B14764679
theorem B1552967 : Blo 1020604 1552967 := bstep (se 1 (by rfl) ⟨1164725, by rfl⟩ : syracuseStep 1552967 = 2329451) B2329451
theorem B5518007 : Blo 1020604 5518007 := bstep (se 1 (by rfl) ⟨4138505, by rfl⟩ : syracuseStep 5518007 = 8277011) B8277011
theorem B3453623 : Blo 1020604 3453623 := bstep (se 1 (by rfl) ⟨2590217, by rfl⟩ : syracuseStep 3453623 = 5180435) B5180435
theorem B3879647 : Blo 1020604 3879647 := bstep (se 1 (by rfl) ⟨2909735, by rfl⟩ : syracuseStep 3879647 = 5819471) B5819471
theorem B2765587 : Blo 1020604 2765587 := bstep (se 1 (by rfl) ⟨2074190, by rfl⟩ : syracuseStep 2765587 = 4148381) B4148381
theorem B1455079 : Blo 1020604 1455079 := bstep (se 1 (by rfl) ⟨1091309, by rfl⟩ : syracuseStep 1455079 = 2182619) B2182619
theorem B14758969 : Blo 1020604 14758969 := bstep (se 2 (by rfl) ⟨5534613, by rfl⟩ : syracuseStep 14758969 = 11069227) B11069227
theorem B5321971 : Blo 1020604 5321971 := bstep (se 1 (by rfl) ⟨3991478, by rfl⟩ : syracuseStep 5321971 = 7982957) B7982957
theorem B3880331 : Blo 1020604 3880331 := bstep (se 1 (by rfl) ⟨2910248, by rfl⟩ : syracuseStep 3880331 = 5820497) B5820497
theorem B9811361 : Blo 1020604 9811361 := bstep (se 2 (by rfl) ⟨3679260, by rfl⟩ : syracuseStep 9811361 = 7358521) B7358521
theorem B11646503 : Blo 1020604 11646503 := bstep (se 1 (by rfl) ⟨8734877, by rfl⟩ : syracuseStep 11646503 = 17469755) B17469755
theorem B6993719 : Blo 1020604 6993719 := bstep (se 1 (by rfl) ⟨5245289, by rfl⟩ : syracuseStep 6993719 = 10490579) B10490579
theorem B9812249 : Blo 1020604 9812249 := bstep (se 2 (by rfl) ⟨3679593, by rfl⟩ : syracuseStep 9812249 = 7359187) B7359187
theorem B3455567 : Blo 1020604 3455567 := bstep (se 1 (by rfl) ⟨2591675, by rfl⟩ : syracuseStep 3455567 = 5183351) B5183351
theorem B1751735 : Blo 1020604 1751735 := bstep (se 1 (by rfl) ⟨1313801, by rfl⟩ : syracuseStep 1751735 = 2627603) B2627603
theorem B1293023 : Blo 1020604 1293023 := bstep (se 1 (by rfl) ⟨969767, by rfl⟩ : syracuseStep 1293023 = 1939535) B1939535
theorem B1456975 : Blo 1020604 1456975 := bstep (se 1 (by rfl) ⟨1092731, by rfl⟩ : syracuseStep 1456975 = 2185463) B2185463
theorem B21019499 : Blo 1020604 21019499 := bstep (se 1 (by rfl) ⟨15764624, by rfl⟩ : syracuseStep 21019499 = 31529249) B31529249
theorem B3882107 : Blo 1020604 3882107 := bstep (se 1 (by rfl) ⟨2911580, by rfl⟩ : syracuseStep 3882107 = 5823161) B5823161
theorem B1752283 : Blo 1020604 1752283 := bstep (se 1 (by rfl) ⟨1314212, by rfl⟩ : syracuseStep 1752283 = 2628425) B2628425
theorem B3456809 : Blo 1020604 3456809 := bstep (se 2 (by rfl) ⟨1296303, by rfl⟩ : syracuseStep 3456809 = 2592607) B2592607
theorem B1228775 : Blo 1020604 1228775 := bstep (se 1 (by rfl) ⟨921581, by rfl⟩ : syracuseStep 1228775 = 1843163) B1843163
theorem B26165267 : Blo 1020604 26165267 := bstep (se 1 (by rfl) ⟨19623950, by rfl⟩ : syracuseStep 26165267 = 39247901) B39247901
theorem B13090835 : Blo 1020604 13090835 := bstep (se 1 (by rfl) ⟨9818126, by rfl⟩ : syracuseStep 13090835 = 19636253) B19636253
theorem B23904677 : Blo 1020604 23904677 := bstep (se 4 (by rfl) ⟨2241063, by rfl⟩ : syracuseStep 23904677 = 4482127) B4482127
theorem B1229419 : Blo 1020604 1229419 := bstep (se 1 (by rfl) ⟨922064, by rfl⟩ : syracuseStep 1229419 = 1844129) B1844129
theorem B1295023 : Blo 1020604 1295023 := bstep (se 1 (by rfl) ⟨971267, by rfl⟩ : syracuseStep 1295023 = 1942535) B1942535
theorem B12469211 : Blo 1020604 12469211 := bstep (se 1 (by rfl) ⟨9351908, by rfl⟩ : syracuseStep 12469211 = 18703817) B18703817
theorem B13092475 : Blo 1020604 13092475 := bstep (se 1 (by rfl) ⟨9819356, by rfl⟩ : syracuseStep 13092475 = 19638713) B19638713
theorem B8734331 : Blo 1020604 8734331 := bstep (se 1 (by rfl) ⟨6550748, by rfl⟩ : syracuseStep 8734331 = 13101497) B13101497
theorem B5818013 : Blo 1020604 5818013 := bstep (se 3 (by rfl) ⟨1090877, by rfl⟩ : syracuseStep 5818013 = 2181755) B2181755
theorem B3885191 : Blo 1020604 3885191 := bstep (se 1 (by rfl) ⟨2913893, by rfl⟩ : syracuseStep 3885191 = 5827787) B5827787
theorem B3885479 : Blo 1020604 3885479 := bstep (se 1 (by rfl) ⟨2914109, by rfl⟩ : syracuseStep 3885479 = 5828219) B5828219
theorem B2181601 : Blo 1020604 2181601 := bstep (se 2 (by rfl) ⟨818100, by rfl⟩ : syracuseStep 2181601 = 1636201) B1636201
theorem B3885995 : Blo 1020604 3885995 := bstep (se 1 (by rfl) ⟨2914496, by rfl⟩ : syracuseStep 3885995 = 5828993) B5828993
theorem B2182439 : Blo 1020604 2182439 := bstep (se 1 (by rfl) ⟨1636829, by rfl⟩ : syracuseStep 2182439 = 3273659) B3273659
theorem B3887635 : Blo 1020604 3887635 := bstep (se 1 (by rfl) ⟨2915726, by rfl⟩ : syracuseStep 3887635 = 5831453) B5831453
theorem B1659455 : Blo 1020604 1659455 := bstep (se 1 (by rfl) ⟨1244591, by rfl⟩ : syracuseStep 1659455 = 2489183) B2489183
theorem B1725151 : Blo 1020604 1725151 := bstep (se 1 (by rfl) ⟨1293863, by rfl⟩ : syracuseStep 1725151 = 2587727) B2587727
theorem B2184079 : Blo 1020604 2184079 := bstep (se 1 (by rfl) ⟨1638059, by rfl⟩ : syracuseStep 2184079 = 3276119) B3276119
theorem B13980761 : Blo 1020604 13980761 := bstep (se 2 (by rfl) ⟨5242785, by rfl⟩ : syracuseStep 13980761 = 10485571) B10485571
theorem B1725583 : Blo 1020604 1725583 := bstep (se 1 (by rfl) ⟨1294187, by rfl⟩ : syracuseStep 1725583 = 2588375) B2588375
theorem B2184335 : Blo 1020604 2184335 := bstep (se 1 (by rfl) ⟨1638251, by rfl⟩ : syracuseStep 2184335 = 3276503) B3276503
theorem B1725833 : Blo 1020604 1725833 := bstep (se 2 (by rfl) ⟨647187, by rfl⟩ : syracuseStep 1725833 = 1294375) B1294375
theorem B1726265 : Blo 1020604 1726265 := bstep (se 2 (by rfl) ⟨647349, by rfl⟩ : syracuseStep 1726265 = 1294699) B1294699
theorem B39836087 : Blo 1020604 39836087 := bstep (se 1 (by rfl) ⟨29877065, by rfl⟩ : syracuseStep 39836087 = 59754131) B59754131
theorem B2185975 : Blo 1020604 2185975 := bstep (se 1 (by rfl) ⟨1639481, by rfl⟩ : syracuseStep 2185975 = 3278963) B3278963
theorem B5528387 : Blo 1020604 5528387 := bstep (se 1 (by rfl) ⟨4146290, by rfl⟩ : syracuseStep 5528387 = 8292581) B8292581
theorem B1727311 : Blo 1020604 1727311 := bstep (se 1 (by rfl) ⟨1295483, by rfl⟩ : syracuseStep 1727311 = 2590967) B2590967
theorem B1531175 : Blo 1020604 1531175 := bstep (se 1 (by rfl) ⟨1148381, by rfl⟩ : syracuseStep 1531175 = 2296763) B2296763
theorem B1531259 : Blo 1020604 1531259 := bstep (se 1 (by rfl) ⟨1148444, by rfl⟩ : syracuseStep 1531259 = 2296889) B2296889
theorem B1531385 : Blo 1020604 1531385 := bstep (se 2 (by rfl) ⟨574269, by rfl⟩ : syracuseStep 1531385 = 1148539) B1148539
theorem B4906489 : Blo 1020604 4906489 := bstep (se 2 (by rfl) ⟨1839933, by rfl⟩ : syracuseStep 4906489 = 3679867) B3679867
theorem B8740345 : Blo 1020604 8740345 := bstep (se 2 (by rfl) ⟨3277629, by rfl⟩ : syracuseStep 8740345 = 6555259) B6555259
theorem B1727993 : Blo 1020604 1727993 := bstep (se 2 (by rfl) ⟨647997, by rfl⟩ : syracuseStep 1727993 = 1295995) B1295995
theorem B2907731 : Blo 1020604 2907731 := bstep (se 1 (by rfl) ⟨2180798, by rfl⟩ : syracuseStep 2907731 = 4361597) B4361597
theorem B1531487 : Blo 1020604 1531487 := bstep (se 1 (by rfl) ⟨1148615, by rfl⟩ : syracuseStep 1531487 = 2297231) B2297231
theorem B1728263 : Blo 1020604 1728263 := bstep (se 1 (by rfl) ⟨1296197, by rfl⟩ : syracuseStep 1728263 = 2592395) B2592395
theorem B1531703 : Blo 1020604 1531703 := bstep (se 1 (by rfl) ⟨1148777, by rfl⟩ : syracuseStep 1531703 = 2297555) B2297555
theorem B3497789 : Blo 1020604 3497789 := bstep (se 3 (by rfl) ⟨655835, by rfl⟩ : syracuseStep 3497789 = 1311671) B1311671
theorem B3104669 : Blo 1020604 3104669 := bstep (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) B1164251
theorem B5169257 : Blo 1020604 5169257 := bstep (se 2 (by rfl) ⟨1938471, by rfl⟩ : syracuseStep 5169257 = 3876943) B3876943
theorem B1532009 : Blo 1020604 1532009 := bstep (se 2 (by rfl) ⟨574503, by rfl⟩ : syracuseStep 1532009 = 1149007) B1149007
theorem B23584945 : Blo 1020604 23584945 := bstep (se 2 (by rfl) ⟨8844354, by rfl⟩ : syracuseStep 23584945 = 17688709) B17688709
theorem B1532327 : Blo 1020604 1532327 := bstep (se 1 (by rfl) ⟨1149245, by rfl⟩ : syracuseStep 1532327 = 2298491) B2298491
theorem B1532411 : Blo 1020604 1532411 := bstep (se 1 (by rfl) ⟨1149308, by rfl⟩ : syracuseStep 1532411 = 2298617) B2298617
theorem B1729019 : Blo 1020604 1729019 := bstep (se 1 (by rfl) ⟨1296764, by rfl⟩ : syracuseStep 1729019 = 2593529) B2593529
theorem B1532537 : Blo 1020604 1532537 := bstep (se 2 (by rfl) ⟨574701, by rfl⟩ : syracuseStep 1532537 = 1149403) B1149403
theorem B1532591 : Blo 1020604 1532591 := bstep (se 1 (by rfl) ⟨1149443, by rfl⟩ : syracuseStep 1532591 = 2298887) B2298887
theorem B4907719 : Blo 1020604 4907719 := bstep (se 1 (by rfl) ⟨3680789, by rfl⟩ : syracuseStep 4907719 = 7361579) B7361579
theorem B1532639 : Blo 1020604 1532639 := bstep (se 1 (by rfl) ⟨1149479, by rfl⟩ : syracuseStep 1532639 = 2298959) B2298959
theorem B3498719 : Blo 1020604 3498719 := bstep (se 1 (by rfl) ⟨2624039, by rfl⟩ : syracuseStep 3498719 = 5248079) B5248079
theorem B5530463 : Blo 1020604 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B11658167 : Blo 1020604 11658167 := bstep (se 1 (by rfl) ⟨8743625, by rfl⟩ : syracuseStep 11658167 = 17487251) B17487251
theorem B1532903 : Blo 1020604 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B5170391 : Blo 1020604 5170391 := bstep (se 1 (by rfl) ⟨3877793, by rfl⟩ : syracuseStep 5170391 = 7755587) B7755587
theorem B1533161 : Blo 1020604 1533161 := bstep (se 2 (by rfl) ⟨574935, by rfl⟩ : syracuseStep 1533161 = 1149871) B1149871
theorem B1533215 : Blo 1020604 1533215 := bstep (se 1 (by rfl) ⟨1149911, by rfl⟩ : syracuseStep 1533215 = 2299823) B2299823
theorem B9332111 : Blo 1020604 9332111 := bstep (se 1 (by rfl) ⟨6999083, by rfl⟩ : syracuseStep 9332111 = 13998167) B13998167
theorem B1533383 : Blo 1020604 1533383 := bstep (se 1 (by rfl) ⟨1150037, by rfl⟩ : syracuseStep 1533383 = 2300075) B2300075
theorem B1402363 : Blo 1020604 1402363 := bstep (se 1 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 1402363 = 2103545) B2103545
theorem B30336599 : Blo 1020604 30336599 := bstep (se 1 (by rfl) ⟨22752449, by rfl⟩ : syracuseStep 30336599 = 45504899) B45504899
theorem B1533737 : Blo 1020604 1533737 := bstep (se 2 (by rfl) ⟨575151, by rfl⟩ : syracuseStep 1533737 = 1150303) B1150303
theorem B1533743 : Blo 1020604 1533743 := bstep (se 1 (by rfl) ⟨1150307, by rfl⟩ : syracuseStep 1533743 = 2300615) B2300615
theorem B3106615 : Blo 1020604 3106615 := bstep (se 1 (by rfl) ⟨2329961, by rfl⟩ : syracuseStep 3106615 = 4659923) B4659923
theorem B1534217 : Blo 1020604 1534217 := bstep (se 2 (by rfl) ⟨575331, by rfl⟩ : syracuseStep 1534217 = 1150663) B1150663
theorem B1534319 : Blo 1020604 1534319 := bstep (se 1 (by rfl) ⟨1150739, by rfl⟩ : syracuseStep 1534319 = 2301479) B2301479
theorem B2910647 : Blo 1020604 2910647 := bstep (se 1 (by rfl) ⟨2182985, by rfl⟩ : syracuseStep 2910647 = 4365971) B4365971
theorem B3500471 : Blo 1020604 3500471 := bstep (se 1 (by rfl) ⟨2625353, by rfl⟩ : syracuseStep 3500471 = 5250707) B5250707
theorem B1534535 : Blo 1020604 1534535 := bstep (se 1 (by rfl) ⟨1150901, by rfl⟩ : syracuseStep 1534535 = 2301803) B2301803
theorem B1534571 : Blo 1020604 1534571 := bstep (se 1 (by rfl) ⟨1150928, by rfl⟩ : syracuseStep 1534571 = 2301857) B2301857
theorem B5827261 : Blo 1020604 5827261 := bstep (se 3 (by rfl) ⟨1092611, by rfl⟩ : syracuseStep 5827261 = 2185223) B2185223
theorem B1534799 : Blo 1020604 1534799 := bstep (se 1 (by rfl) ⟨1151099, by rfl⟩ : syracuseStep 1534799 = 2302199) B2302199
theorem B2583515 : Blo 1020604 2583515 := bstep (se 1 (by rfl) ⟨1937636, by rfl⟩ : syracuseStep 2583515 = 3875273) B3875273
theorem B4910219 : Blo 1020604 4910219 := bstep (se 1 (by rfl) ⟨3682664, by rfl⟩ : syracuseStep 4910219 = 7365329) B7365329
theorem B1535195 : Blo 1020604 1535195 := bstep (se 1 (by rfl) ⟨1151396, by rfl⟩ : syracuseStep 1535195 = 2302793) B2302793
theorem B2583839 : Blo 1020604 2583839 := bstep (se 1 (by rfl) ⟨1937879, by rfl⟩ : syracuseStep 2583839 = 3875759) B3875759
theorem B179563877 : Blo 1020604 179563877 := bstep (se 4 (by rfl) ⟨16834113, by rfl⟩ : syracuseStep 179563877 = 33668227) B33668227
theorem B13299059 : Blo 1020604 13299059 := bstep (se 1 (by rfl) ⟨9974294, by rfl⟩ : syracuseStep 13299059 = 19948589) B19948589
theorem B1535369 : Blo 1020604 1535369 := bstep (se 2 (by rfl) ⟨575763, by rfl⟩ : syracuseStep 1535369 = 1151527) B1151527
theorem B1535723 : Blo 1020604 1535723 := bstep (se 1 (by rfl) ⟨1151792, by rfl⟩ : syracuseStep 1535723 = 2303585) B2303585
theorem B1535951 : Blo 1020604 1535951 := bstep (se 1 (by rfl) ⟨1151963, by rfl⟩ : syracuseStep 1535951 = 2303927) B2303927
theorem B12414977 : Blo 1020604 12414977 := bstep (se 2 (by rfl) ⟨4655616, by rfl⟩ : syracuseStep 12414977 = 9311233) B9311233
theorem B5173307 : Blo 1020604 5173307 := bstep (se 1 (by rfl) ⟨3879980, by rfl⟩ : syracuseStep 5173307 = 7759961) B7759961
theorem B2453609 : Blo 1020604 2453609 := bstep (se 2 (by rfl) ⟨920103, by rfl⟩ : syracuseStep 2453609 = 1840207) B1840207
theorem B1536347 : Blo 1020604 1536347 := bstep (se 1 (by rfl) ⟨1152260, by rfl⟩ : syracuseStep 1536347 = 2304521) B2304521
theorem B2584943 : Blo 1020604 2584943 := bstep (se 1 (by rfl) ⟨1938707, by rfl⟩ : syracuseStep 2584943 = 3877415) B3877415
theorem B7860797 : Blo 1020604 7860797 := bstep (se 3 (by rfl) ⟨1473899, by rfl⟩ : syracuseStep 7860797 = 2947799) B2947799
theorem B1536575 : Blo 1020604 1536575 := bstep (se 1 (by rfl) ⟨1152431, by rfl⟩ : syracuseStep 1536575 = 2304863) B2304863
theorem B1536695 : Blo 1020604 1536695 := bstep (se 1 (by rfl) ⟨1152521, by rfl⟩ : syracuseStep 1536695 = 2305043) B2305043
theorem B2585591 : Blo 1020604 2585591 := bstep (se 1 (by rfl) ⟨1939193, by rfl⟩ : syracuseStep 2585591 = 3878387) B3878387
theorem B5174279 : Blo 1020604 5174279 := bstep (se 1 (by rfl) ⟨3880709, by rfl⟩ : syracuseStep 5174279 = 7761419) B7761419
theorem B5534963 : Blo 1020604 5534963 := bstep (se 1 (by rfl) ⟨4151222, by rfl⟩ : syracuseStep 5534963 = 8302445) B8302445
theorem B2913529 : Blo 1020604 2913529 := bstep (se 2 (by rfl) ⟨1092573, by rfl⟩ : syracuseStep 2913529 = 2185147) B2185147
theorem B5240159 : Blo 1020604 5240159 := bstep (se 1 (by rfl) ⟨3930119, by rfl⟩ : syracuseStep 5240159 = 7860239) B7860239
theorem B3274145 : Blo 1020604 3274145 := bstep (se 2 (by rfl) ⟨1227804, by rfl⟩ : syracuseStep 3274145 = 2455609) B2455609
theorem B5174765 : Blo 1020604 5174765 := bstep (se 3 (by rfl) ⟨970268, by rfl⟩ : syracuseStep 5174765 = 1940537) B1940537
theorem B1636457 : Blo 1020604 1636457 := bstep (se 2 (by rfl) ⟨613671, by rfl⟩ : syracuseStep 1636457 = 1227343) B1227343
theorem B5175575 : Blo 1020604 5175575 := bstep (se 1 (by rfl) ⟨3881681, by rfl⟩ : syracuseStep 5175575 = 7763363) B7763363
theorem B39287267 : Blo 1020604 39287267 := bstep (se 1 (by rfl) ⟨29465450, by rfl⟩ : syracuseStep 39287267 = 58930901) B58930901
theorem B9828971 : Blo 1020604 9828971 := bstep (se 1 (by rfl) ⟨7371728, by rfl⟩ : syracuseStep 9828971 = 14743457) B14743457
theorem B1637047 : Blo 1020604 1637047 := bstep (se 1 (by rfl) ⟨1227785, by rfl⟩ : syracuseStep 1637047 = 2455571) B2455571
theorem B5536451 : Blo 1020604 5536451 := bstep (se 1 (by rfl) ⟨4152338, by rfl⟩ : syracuseStep 5536451 = 8304677) B8304677
theorem B2587535 : Blo 1020604 2587535 := bstep (se 1 (by rfl) ⟨1940651, by rfl⟩ : syracuseStep 2587535 = 3881303) B3881303
theorem B8289209 : Blo 1020604 8289209 := bstep (se 2 (by rfl) ⟨3108453, by rfl⟩ : syracuseStep 8289209 = 6216907) B6216907
theorem B7371899 : Blo 1020604 7371899 := bstep (se 1 (by rfl) ⟨5528924, by rfl⟩ : syracuseStep 7371899 = 11057849) B11057849
theorem B3276247 : Blo 1020604 3276247 := bstep (se 1 (by rfl) ⟨2457185, by rfl⟩ : syracuseStep 3276247 = 4914371) B4914371
theorem B2588395 : Blo 1020604 2588395 := bstep (se 1 (by rfl) ⟨1941296, by rfl⟩ : syracuseStep 2588395 = 3882593) B3882593
theorem B2916137 : Blo 1020604 2916137 := bstep (se 2 (by rfl) ⟨1093551, by rfl⟩ : syracuseStep 2916137 = 2187103) B2187103
theorem B3276605 : Blo 1020604 3276605 := bstep (se 3 (by rfl) ⟨614363, by rfl⟩ : syracuseStep 3276605 = 1228727) B1228727
theorem B5177195 : Blo 1020604 5177195 := bstep (se 1 (by rfl) ⟨3882896, by rfl⟩ : syracuseStep 5177195 = 7765793) B7765793
theorem B11665457 : Blo 1020604 11665457 := bstep (se 2 (by rfl) ⟨4374546, by rfl⟩ : syracuseStep 11665457 = 8749093) B8749093
theorem B29458889 : Blo 1020604 29458889 := bstep (se 2 (by rfl) ⟨11047083, by rfl⟩ : syracuseStep 29458889 = 22094167) B22094167
theorem B3277579 : Blo 1020604 3277579 := bstep (se 1 (by rfl) ⟨2458184, by rfl⟩ : syracuseStep 3277579 = 4916369) B4916369
theorem B1639225 : Blo 1020604 1639225 := bstep (se 2 (by rfl) ⟨614709, by rfl⟩ : syracuseStep 1639225 = 1229419) B1229419
theorem B1639835 : Blo 1020604 1639835 := bstep (se 1 (by rfl) ⟨1229876, by rfl⟩ : syracuseStep 1639835 = 2459753) B2459753
theorem B2590127 : Blo 1020604 2590127 := bstep (se 1 (by rfl) ⟨1942595, by rfl⟩ : syracuseStep 2590127 = 3885191) B3885191
theorem B2590319 : Blo 1020604 2590319 := bstep (se 1 (by rfl) ⟨1942739, by rfl⟩ : syracuseStep 2590319 = 3885479) B3885479
theorem B5834551 : Blo 1020604 5834551 := bstep (se 1 (by rfl) ⟨4375913, by rfl⟩ : syracuseStep 5834551 = 8751827) B8751827
theorem B2590663 : Blo 1020604 2590663 := bstep (se 1 (by rfl) ⟨1942997, by rfl⟩ : syracuseStep 2590663 = 3885995) B3885995
theorem B1869817 : Blo 1020604 1869817 := bstep (se 2 (by rfl) ⟨701181, by rfl⟩ : syracuseStep 1869817 = 1402363) B1402363
theorem B14158091 : Blo 1020604 14158091 := bstep (se 1 (by rfl) ⟨10618568, by rfl⟩ : syracuseStep 14158091 = 21237137) B21237137
theorem B1640827 : Blo 1020604 1640827 := bstep (se 1 (by rfl) ⟨1230620, by rfl⟩ : syracuseStep 1640827 = 2461241) B2461241
theorem B3279361 : Blo 1020604 3279361 := bstep (se 2 (by rfl) ⟨1229760, by rfl⟩ : syracuseStep 3279361 = 2459521) B2459521
theorem B2297339 : Blo 1020604 2297339 := bstep (se 1 (by rfl) ⟨1723004, by rfl⟩ : syracuseStep 2297339 = 3446009) B3446009
theorem B7769681 : Blo 1020604 7769681 := bstep (se 2 (by rfl) ⟨2913630, by rfl⟩ : syracuseStep 7769681 = 5827261) B5827261
theorem B1150555 : Blo 1020604 1150555 := bstep (se 1 (by rfl) ⟨862916, by rfl⟩ : syracuseStep 1150555 = 1725833) B1725833
theorem B2297519 : Blo 1020604 2297519 := bstep (se 1 (by rfl) ⟨1723139, by rfl⟩ : syracuseStep 2297519 = 3446279) B3446279
theorem B1969939 : Blo 1020604 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B1150843 : Blo 1020604 1150843 := bstep (se 1 (by rfl) ⟨863132, by rfl⟩ : syracuseStep 1150843 = 1726265) B1726265
theorem B56824037 : Blo 1020604 56824037 := bstep (se 4 (by rfl) ⟨5327253, by rfl⟩ : syracuseStep 56824037 = 10654507) B10654507
theorem B2298167 : Blo 1020604 2298167 := bstep (se 1 (by rfl) ⟨1723625, by rfl⟩ : syracuseStep 2298167 = 3447251) B3447251
theorem B2298239 : Blo 1020604 2298239 := bstep (se 1 (by rfl) ⟨1723679, by rfl⟩ : syracuseStep 2298239 = 3447359) B3447359
theorem B3936863 : Blo 1020604 3936863 := bstep (se 1 (by rfl) ⟨2952647, by rfl⟩ : syracuseStep 3936863 = 5905295) B5905295
theorem B5182055 : Blo 1020604 5182055 := bstep (se 1 (by rfl) ⟨3886541, by rfl⟩ : syracuseStep 5182055 = 7773083) B7773083
theorem B5608217 : Blo 1020604 5608217 := bstep (se 2 (by rfl) ⟨2103081, by rfl⟩ : syracuseStep 5608217 = 4206163) B4206163
theorem B1020783 : Blo 1020604 1020783 := bstep (se 1 (by rfl) ⟨765587, by rfl⟩ : syracuseStep 1020783 = 1531175) B1531175
theorem B1020839 : Blo 1020604 1020839 := bstep (se 1 (by rfl) ⟨765629, by rfl⟩ : syracuseStep 1020839 = 1531259) B1531259
theorem B1020923 : Blo 1020604 1020923 := bstep (se 1 (by rfl) ⟨765692, by rfl⟩ : syracuseStep 1020923 = 1531385) B1531385
theorem B1151995 : Blo 1020604 1151995 := bstep (se 1 (by rfl) ⟨863996, by rfl⟩ : syracuseStep 1151995 = 1727993) B1727993
theorem B1938487 : Blo 1020604 1938487 := bstep (se 1 (by rfl) ⟨1453865, by rfl⟩ : syracuseStep 1938487 = 2907731) B2907731
theorem B1020991 : Blo 1020604 1020991 := bstep (se 1 (by rfl) ⟨765743, by rfl⟩ : syracuseStep 1020991 = 1531487) B1531487
theorem B1152175 : Blo 1020604 1152175 := bstep (se 1 (by rfl) ⟨864131, by rfl⟩ : syracuseStep 1152175 = 1728263) B1728263
theorem B1021135 : Blo 1020604 1021135 := bstep (se 1 (by rfl) ⟨765851, by rfl⟩ : syracuseStep 1021135 = 1531703) B1531703
theorem B3282295 : Blo 1020604 3282295 := bstep (se 1 (by rfl) ⟨2461721, by rfl⟩ : syracuseStep 3282295 = 4923443) B4923443
theorem B3446171 : Blo 1020604 3446171 := bstep (se 1 (by rfl) ⟨2584628, by rfl⟩ : syracuseStep 3446171 = 5169257) B5169257
theorem B1021339 : Blo 1020604 1021339 := bstep (se 1 (by rfl) ⟨766004, by rfl⟩ : syracuseStep 1021339 = 1532009) B1532009
theorem B14751179 : Blo 1020604 14751179 := bstep (se 1 (by rfl) ⟨11063384, by rfl⟩ : syracuseStep 14751179 = 22126769) B22126769
theorem B2299463 : Blo 1020604 2299463 := bstep (se 1 (by rfl) ⟨1724597, by rfl⟩ : syracuseStep 2299463 = 3449195) B3449195
theorem B4363885 : Blo 1020604 4363885 := bstep (se 3 (by rfl) ⟨818228, by rfl⟩ : syracuseStep 4363885 = 1636457) B1636457
theorem B1021551 : Blo 1020604 1021551 := bstep (se 1 (by rfl) ⟨766163, by rfl⟩ : syracuseStep 1021551 = 1532327) B1532327
theorem B1021607 : Blo 1020604 1021607 := bstep (se 1 (by rfl) ⟨766205, by rfl⟩ : syracuseStep 1021607 = 1532411) B1532411
theorem B1152679 : Blo 1020604 1152679 := bstep (se 1 (by rfl) ⟨864509, by rfl⟩ : syracuseStep 1152679 = 1729019) B1729019
theorem B1021691 : Blo 1020604 1021691 := bstep (se 1 (by rfl) ⟨766268, by rfl⟩ : syracuseStep 1021691 = 1532537) B1532537
theorem B2299643 : Blo 1020604 2299643 := bstep (se 1 (by rfl) ⟨1724732, by rfl⟩ : syracuseStep 2299643 = 3449465) B3449465
theorem B1021727 : Blo 1020604 1021727 := bstep (se 1 (by rfl) ⟨766295, by rfl⟩ : syracuseStep 1021727 = 1532591) B1532591
theorem B1021759 : Blo 1020604 1021759 := bstep (se 1 (by rfl) ⟨766319, by rfl⟩ : syracuseStep 1021759 = 1532639) B1532639
theorem B7772111 : Blo 1020604 7772111 := bstep (se 1 (by rfl) ⟨5829083, by rfl⟩ : syracuseStep 7772111 = 11658167) B11658167
theorem B5904343 : Blo 1020604 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B1021935 : Blo 1020604 1021935 := bstep (se 1 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 1021935 = 1532903) B1532903
theorem B5183513 : Blo 1020604 5183513 := bstep (se 2 (by rfl) ⟨1943817, by rfl⟩ : syracuseStep 5183513 = 3887635) B3887635
theorem B2758799 : Blo 1020604 2758799 := bstep (se 1 (by rfl) ⟨2069099, by rfl⟩ : syracuseStep 2758799 = 4138199) B4138199
theorem B3446927 : Blo 1020604 3446927 := bstep (se 1 (by rfl) ⟨2585195, by rfl⟩ : syracuseStep 3446927 = 5170391) B5170391
theorem B1022107 : Blo 1020604 1022107 := bstep (se 1 (by rfl) ⟨766580, by rfl⟩ : syracuseStep 1022107 = 1533161) B1533161
theorem B1022143 : Blo 1020604 1022143 := bstep (se 1 (by rfl) ⟨766607, by rfl⟩ : syracuseStep 1022143 = 1533215) B1533215
theorem B2300201 : Blo 1020604 2300201 := bstep (se 2 (by rfl) ⟨862575, by rfl⟩ : syracuseStep 2300201 = 1725151) B1725151
theorem B1022255 : Blo 1020604 1022255 := bstep (se 1 (by rfl) ⟨766691, by rfl⟩ : syracuseStep 1022255 = 1533383) B1533383
theorem B20224399 : Blo 1020604 20224399 := bstep (se 1 (by rfl) ⟨15168299, by rfl⟩ : syracuseStep 20224399 = 30336599) B30336599
theorem B6822319 : Blo 1020604 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B1022491 : Blo 1020604 1022491 := bstep (se 1 (by rfl) ⟨766868, by rfl⟩ : syracuseStep 1022491 = 1533737) B1533737
theorem B1022495 : Blo 1020604 1022495 := bstep (se 1 (by rfl) ⟨766871, by rfl⟩ : syracuseStep 1022495 = 1533743) B1533743
theorem B1940105 : Blo 1020604 1940105 := bstep (se 2 (by rfl) ⟨727539, by rfl⟩ : syracuseStep 1940105 = 1455079) B1455079
theorem B1022811 : Blo 1020604 1022811 := bstep (se 1 (by rfl) ⟨767108, by rfl⟩ : syracuseStep 1022811 = 1534217) B1534217
theorem B2300777 : Blo 1020604 2300777 := bstep (se 2 (by rfl) ⟨862791, by rfl⟩ : syracuseStep 2300777 = 1725583) B1725583
theorem B2300831 : Blo 1020604 2300831 := bstep (se 1 (by rfl) ⟨1725623, by rfl⟩ : syracuseStep 2300831 = 3451247) B3451247
theorem B1022879 : Blo 1020604 1022879 := bstep (se 1 (by rfl) ⟨767159, by rfl⟩ : syracuseStep 1022879 = 1534319) B1534319
theorem B1940431 : Blo 1020604 1940431 := bstep (se 1 (by rfl) ⟨1455323, by rfl⟩ : syracuseStep 1940431 = 2910647) B2910647
theorem B2333647 : Blo 1020604 2333647 := bstep (se 1 (by rfl) ⟨1750235, by rfl⟩ : syracuseStep 2333647 = 3500471) B3500471
theorem B1023023 : Blo 1020604 1023023 := bstep (se 1 (by rfl) ⟨767267, by rfl⟩ : syracuseStep 1023023 = 1534535) B1534535
theorem B1023047 : Blo 1020604 1023047 := bstep (se 1 (by rfl) ⟨767285, by rfl⟩ : syracuseStep 1023047 = 1534571) B1534571
theorem B1023199 : Blo 1020604 1023199 := bstep (se 1 (by rfl) ⟨767399, by rfl⟩ : syracuseStep 1023199 = 1534799) B1534799
theorem B3448061 : Blo 1020604 3448061 := bstep (se 3 (by rfl) ⟨646511, by rfl⟩ : syracuseStep 3448061 = 1293023) B1293023
theorem B8723807 : Blo 1020604 8723807 := bstep (se 1 (by rfl) ⟨6542855, by rfl⟩ : syracuseStep 8723807 = 13085711) B13085711
theorem B1842601 : Blo 1020604 1842601 := bstep (se 2 (by rfl) ⟨690975, by rfl⟩ : syracuseStep 1842601 = 1381951) B1381951
theorem B1023463 : Blo 1020604 1023463 := bstep (se 1 (by rfl) ⟨767597, by rfl⟩ : syracuseStep 1023463 = 1535195) B1535195
theorem B119709251 : Blo 1020604 119709251 := bstep (se 1 (by rfl) ⟨89781938, by rfl⟩ : syracuseStep 119709251 = 179563877) B179563877
theorem B1023579 : Blo 1020604 1023579 := bstep (se 1 (by rfl) ⟨767684, by rfl⟩ : syracuseStep 1023579 = 1535369) B1535369
theorem B2301767 : Blo 1020604 2301767 := bstep (se 1 (by rfl) ⟨1726325, by rfl⟩ : syracuseStep 2301767 = 3452651) B3452651
theorem B1023815 : Blo 1020604 1023815 := bstep (se 1 (by rfl) ⟨767861, by rfl⟩ : syracuseStep 1023815 = 1535723) B1535723
theorem B1023967 : Blo 1020604 1023967 := bstep (se 1 (by rfl) ⟨767975, by rfl⟩ : syracuseStep 1023967 = 1535951) B1535951
theorem B3448871 : Blo 1020604 3448871 := bstep (se 1 (by rfl) ⟨2586653, by rfl⟩ : syracuseStep 3448871 = 5173307) B5173307
theorem B1024231 : Blo 1020604 1024231 := bstep (se 1 (by rfl) ⟨768173, by rfl⟩ : syracuseStep 1024231 = 1536347) B1536347
theorem B6562079 : Blo 1020604 6562079 := bstep (se 1 (by rfl) ⟨4921559, by rfl⟩ : syracuseStep 6562079 = 9843119) B9843119
theorem B1843553 : Blo 1020604 1843553 := bstep (se 2 (by rfl) ⟨691332, by rfl⟩ : syracuseStep 1843553 = 1382665) B1382665
theorem B1024383 : Blo 1020604 1024383 := bstep (se 1 (by rfl) ⟨768287, by rfl⟩ : syracuseStep 1024383 = 1536575) B1536575
theorem B3678671 : Blo 1020604 3678671 := bstep (se 1 (by rfl) ⟨2759003, by rfl⟩ : syracuseStep 3678671 = 5518007) B5518007
theorem B2302415 : Blo 1020604 2302415 := bstep (se 1 (by rfl) ⟨1726811, by rfl⟩ : syracuseStep 2302415 = 3453623) B3453623
theorem B1024463 : Blo 1020604 1024463 := bstep (se 1 (by rfl) ⟨768347, by rfl⟩ : syracuseStep 1024463 = 1536695) B1536695
theorem B3449519 : Blo 1020604 3449519 := bstep (se 1 (by rfl) ⟨2587139, by rfl⟩ : syracuseStep 3449519 = 5174279) B5174279
theorem B3449843 : Blo 1020604 3449843 := bstep (se 1 (by rfl) ⟨2587382, by rfl⟩ : syracuseStep 3449843 = 5174765) B5174765
theorem B1942633 : Blo 1020604 1942633 := bstep (se 2 (by rfl) ⟨728487, by rfl⟩ : syracuseStep 1942633 = 1456975) B1456975
theorem B2303081 : Blo 1020604 2303081 := bstep (se 2 (by rfl) ⟨863655, by rfl⟩ : syracuseStep 2303081 = 1727311) B1727311
theorem B4662479 : Blo 1020604 4662479 := bstep (se 1 (by rfl) ⟨3496859, by rfl⟩ : syracuseStep 4662479 = 6993719) B6993719
theorem B1844705 : Blo 1020604 1844705 := bstep (se 2 (by rfl) ⟨691764, by rfl⟩ : syracuseStep 1844705 = 1383529) B1383529
theorem B3450383 : Blo 1020604 3450383 := bstep (se 1 (by rfl) ⟨2587787, by rfl⟩ : syracuseStep 3450383 = 5175575) B5175575
theorem B3679825 : Blo 1020604 3679825 := bstep (se 2 (by rfl) ⟨1379934, by rfl⟩ : syracuseStep 3679825 = 2759869) B2759869
theorem B2336377 : Blo 1020604 2336377 := bstep (se 2 (by rfl) ⟨876141, by rfl⟩ : syracuseStep 2336377 = 1752283) B1752283
theorem B26191511 : Blo 1020604 26191511 := bstep (se 1 (by rfl) ⟨19643633, by rfl⟩ : syracuseStep 26191511 = 39287267) B39287267
theorem B2303711 : Blo 1020604 2303711 := bstep (se 1 (by rfl) ⟨1727783, by rfl⟩ : syracuseStep 2303711 = 3455567) B3455567
theorem B4368329 : Blo 1020604 4368329 := bstep (se 2 (by rfl) ⟨1638123, by rfl⟩ : syracuseStep 4368329 = 3276247) B3276247
theorem B3451193 : Blo 1020604 3451193 := bstep (se 2 (by rfl) ⟨1294197, by rfl⟩ : syracuseStep 3451193 = 2588395) B2588395
theorem B1944091 : Blo 1020604 1944091 := bstep (se 1 (by rfl) ⟨1458068, by rfl⟩ : syracuseStep 1944091 = 2916137) B2916137
theorem B2304539 : Blo 1020604 2304539 := bstep (se 1 (by rfl) ⟨1728404, by rfl⟩ : syracuseStep 2304539 = 3456809) B3456809
theorem B3451463 : Blo 1020604 3451463 := bstep (se 1 (by rfl) ⟨2588597, by rfl⟩ : syracuseStep 3451463 = 5177195) B5177195
theorem B17443511 : Blo 1020604 17443511 := bstep (se 1 (by rfl) ⟨13082633, by rfl⟩ : syracuseStep 17443511 = 26165267) B26165267
theorem B8727223 : Blo 1020604 8727223 := bstep (se 1 (by rfl) ⟨6545417, by rfl⟩ : syracuseStep 8727223 = 13090835) B13090835
theorem B4369079 : Blo 1020604 4369079 := bstep (se 1 (by rfl) ⟨3276809, by rfl⟩ : syracuseStep 4369079 = 6553619) B6553619
theorem B11643587 : Blo 1020604 11643587 := bstep (se 1 (by rfl) ⟨8732690, by rfl⟩ : syracuseStep 11643587 = 17465381) B17465381
theorem B1944623 : Blo 1020604 1944623 := bstep (se 1 (by rfl) ⟨1458467, by rfl⟩ : syracuseStep 1944623 = 2916935) B2916935
theorem B1944911 : Blo 1020604 1944911 := bstep (se 1 (by rfl) ⟨1458683, by rfl⟩ : syracuseStep 1944911 = 2917367) B2917367
theorem B3452489 : Blo 1020604 3452489 := bstep (se 2 (by rfl) ⟨1294683, by rfl⟩ : syracuseStep 3452489 = 2589367) B2589367
theorem B63745805 : Blo 1020604 63745805 := bstep (se 3 (by rfl) ⟨11952338, by rfl⟩ : syracuseStep 63745805 = 23904677) B23904677
theorem B3878675 : Blo 1020604 3878675 := bstep (se 1 (by rfl) ⟨2909006, by rfl⟩ : syracuseStep 3878675 = 5818013) B5818013
theorem B1453945 : Blo 1020604 1453945 := bstep (se 2 (by rfl) ⟨545229, by rfl⟩ : syracuseStep 1453945 = 1090459) B1090459
theorem B6992081 : Blo 1020604 6992081 := bstep (se 2 (by rfl) ⟨2622030, by rfl⟩ : syracuseStep 6992081 = 5244061) B5244061
theorem B5812681 : Blo 1020604 5812681 := bstep (se 2 (by rfl) ⟨2179755, by rfl⟩ : syracuseStep 5812681 = 4359511) B4359511
theorem B1454959 : Blo 1020604 1454959 := bstep (se 1 (by rfl) ⟨1091219, by rfl⟩ : syracuseStep 1454959 = 2182439) B2182439
theorem B3453947 : Blo 1020604 3453947 := bstep (se 1 (by rfl) ⟨2590460, by rfl⟩ : syracuseStep 3453947 = 5180921) B5180921
theorem B4142153 : Blo 1020604 4142153 := bstep (se 2 (by rfl) ⟨1553307, by rfl⟩ : syracuseStep 4142153 = 3106615) B3106615
theorem B3454163 : Blo 1020604 3454163 := bstep (se 1 (by rfl) ⟨2590622, by rfl⟩ : syracuseStep 3454163 = 5181245) B5181245
theorem B3454433 : Blo 1020604 3454433 := bstep (se 2 (by rfl) ⟨1295412, by rfl⟩ : syracuseStep 3454433 = 2590825) B2590825
theorem B1226459 : Blo 1020604 1226459 := bstep (se 1 (by rfl) ⟨919844, by rfl⟩ : syracuseStep 1226459 = 1839689) B1839689
theorem B9320507 : Blo 1020604 9320507 := bstep (se 1 (by rfl) ⟨6990380, by rfl⟩ : syracuseStep 9320507 = 13980761) B13980761
theorem B1456223 : Blo 1020604 1456223 := bstep (se 1 (by rfl) ⟨1092167, by rfl⟩ : syracuseStep 1456223 = 2184335) B2184335
theorem B3455081 : Blo 1020604 3455081 := bstep (se 2 (by rfl) ⟨1295655, by rfl⟩ : syracuseStep 3455081 = 2591311) B2591311
theorem B12433661 : Blo 1020604 12433661 := bstep (se 3 (by rfl) ⟨2331311, by rfl⟩ : syracuseStep 12433661 = 4662623) B4662623
theorem B5519929 : Blo 1020604 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B3455945 : Blo 1020604 3455945 := bstep (se 2 (by rfl) ⟨1295979, by rfl⟩ : syracuseStep 3455945 = 2591959) B2591959
theorem B26557391 : Blo 1020604 26557391 := bstep (se 1 (by rfl) ⟨19918043, by rfl⟩ : syracuseStep 26557391 = 39836087) B39836087
theorem B3685591 : Blo 1020604 3685591 := bstep (se 1 (by rfl) ⟨2764193, by rfl⟩ : syracuseStep 3685591 = 5528387) B5528387
theorem B3456215 : Blo 1020604 3456215 := bstep (se 1 (by rfl) ⟨2592161, by rfl⟩ : syracuseStep 3456215 = 5184323) B5184323
theorem B8306363 : Blo 1020604 8306363 := bstep (se 1 (by rfl) ⟨6229772, by rfl⟩ : syracuseStep 8306363 = 12459545) B12459545
theorem B3456755 : Blo 1020604 3456755 := bstep (se 1 (by rfl) ⟨2592566, by rfl⟩ : syracuseStep 3456755 = 5185133) B5185133
theorem B8307143 : Blo 1020604 8307143 := bstep (se 1 (by rfl) ⟨6230357, by rfl⟩ : syracuseStep 8307143 = 12460715) B12460715
theorem B4375079 : Blo 1020604 4375079 := bstep (se 1 (by rfl) ⟨3281309, by rfl⟩ : syracuseStep 4375079 = 6562619) B6562619
theorem B3686975 : Blo 1020604 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B3687449 : Blo 1020604 3687449 := bstep (se 2 (by rfl) ⟨1382793, by rfl⟩ : syracuseStep 3687449 = 2765587) B2765587
theorem B7357661 : Blo 1020604 7357661 := bstep (se 3 (by rfl) ⟨1379561, by rfl⟩ : syracuseStep 7357661 = 2759123) B2759123
theorem B19678625 : Blo 1020604 19678625 := bstep (se 2 (by rfl) ⟨7379484, by rfl⟩ : syracuseStep 19678625 = 14758969) B14758969
theorem B7095961 : Blo 1020604 7095961 := bstep (se 2 (by rfl) ⟨2660985, by rfl⟩ : syracuseStep 7095961 = 5321971) B5321971
theorem B3884705 : Blo 1020604 3884705 := bstep (se 2 (by rfl) ⟨1456764, by rfl⟩ : syracuseStep 3884705 = 2913529) B2913529
theorem B1296091 : Blo 1020604 1296091 := bstep (se 1 (by rfl) ⟨972068, by rfl⟩ : syracuseStep 1296091 = 1944137) B1944137
theorem B14763869 : Blo 1020604 14763869 := bstep (se 3 (by rfl) ⟨2768225, by rfl⟩ : syracuseStep 14763869 = 5536451) B5536451
theorem B1722343 : Blo 1020604 1722343 := bstep (se 1 (by rfl) ⟨1291757, by rfl⟩ : syracuseStep 1722343 = 2583515) B2583515
theorem B1722559 : Blo 1020604 1722559 := bstep (se 1 (by rfl) ⟨1291919, by rfl⟩ : syracuseStep 1722559 = 2583839) B2583839
theorem B19646711 : Blo 1020604 19646711 := bstep (se 1 (by rfl) ⟨14735033, by rfl⟩ : syracuseStep 19646711 = 29470067) B29470067
theorem B8866039 : Blo 1020604 8866039 := bstep (se 1 (by rfl) ⟨6649529, by rfl⟩ : syracuseStep 8866039 = 13299059) B13299059
theorem B8276651 : Blo 1020604 8276651 := bstep (se 1 (by rfl) ⟨6207488, by rfl⟩ : syracuseStep 8276651 = 12414977) B12414977
theorem B1723295 : Blo 1020604 1723295 := bstep (se 1 (by rfl) ⟨1292471, by rfl⟩ : syracuseStep 1723295 = 2584943) B2584943
theorem B1035311 : Blo 1020604 1035311 := bstep (se 1 (by rfl) ⟨776483, by rfl⟩ : syracuseStep 1035311 = 1552967) B1552967
theorem B1723727 : Blo 1020604 1723727 := bstep (se 1 (by rfl) ⟨1292795, by rfl⟩ : syracuseStep 1723727 = 2585591) B2585591
theorem B18927089 : Blo 1020604 18927089 := bstep (se 2 (by rfl) ⟨7097658, by rfl⟩ : syracuseStep 18927089 = 14195317) B14195317
theorem B3689975 : Blo 1020604 3689975 := bstep (se 1 (by rfl) ⟨2767481, by rfl⟩ : syracuseStep 3689975 = 5534963) B5534963
theorem B3493439 : Blo 1020604 3493439 := bstep (se 1 (by rfl) ⟨2620079, by rfl⟩ : syracuseStep 3493439 = 5240159) B5240159
theorem B2182729 : Blo 1020604 2182729 := bstep (se 2 (by rfl) ⟨818523, by rfl⟩ : syracuseStep 2182729 = 1637047) B1637047
theorem B6540907 : Blo 1020604 6540907 := bstep (se 1 (by rfl) ⟨4905680, by rfl⟩ : syracuseStep 6540907 = 9811361) B9811361
theorem B2182763 : Blo 1020604 2182763 := bstep (se 1 (by rfl) ⟨1637072, by rfl⟩ : syracuseStep 2182763 = 3274145) B3274145
theorem B6541499 : Blo 1020604 6541499 := bstep (se 1 (by rfl) ⟨4906124, by rfl⟩ : syracuseStep 6541499 = 9812249) B9812249
theorem B6836653 : Blo 1020604 6836653 := bstep (se 3 (by rfl) ⟨1281872, by rfl⟩ : syracuseStep 6836653 = 2563745) B2563745
theorem B1167823 : Blo 1020604 1167823 := bstep (se 1 (by rfl) ⟨875867, by rfl⟩ : syracuseStep 1167823 = 1751735) B1751735
theorem B5820929 : Blo 1020604 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B14012999 : Blo 1020604 14012999 := bstep (se 1 (by rfl) ⟨10509749, by rfl⟩ : syracuseStep 14012999 = 21019499) B21019499
theorem B1725023 : Blo 1020604 1725023 := bstep (se 1 (by rfl) ⟨1293767, by rfl⟩ : syracuseStep 1725023 = 2587535) B2587535
theorem B5526139 : Blo 1020604 5526139 := bstep (se 1 (by rfl) ⟨4144604, by rfl⟩ : syracuseStep 5526139 = 8289209) B8289209
theorem B6541985 : Blo 1020604 6541985 := bstep (se 2 (by rfl) ⟨2453244, by rfl⟩ : syracuseStep 6541985 = 4906489) B4906489
theorem B11653793 : Blo 1020604 11653793 := bstep (se 2 (by rfl) ⟨4370172, by rfl⟩ : syracuseStep 11653793 = 8740345) B8740345
theorem B9327437 : Blo 1020604 9327437 := bstep (se 3 (by rfl) ⟨1748894, by rfl⟩ : syracuseStep 9327437 = 3497789) B3497789
theorem B8279117 : Blo 1020604 8279117 := bstep (se 3 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 8279117 = 3104669) B3104669
theorem B2184403 : Blo 1020604 2184403 := bstep (se 1 (by rfl) ⟨1638302, by rfl⟩ : syracuseStep 2184403 = 3276605) B3276605
theorem B31446593 : Blo 1020604 31446593 := bstep (se 2 (by rfl) ⟨11792472, by rfl⟩ : syracuseStep 31446593 = 23584945) B23584945
theorem B6542957 : Blo 1020604 6542957 := bstep (se 3 (by rfl) ⟨1226804, by rfl⟩ : syracuseStep 6542957 = 2453609) B2453609
theorem B3692351 : Blo 1020604 3692351 := bstep (se 1 (by rfl) ⟨2769263, by rfl⟩ : syracuseStep 3692351 = 5538527) B5538527
theorem B8312807 : Blo 1020604 8312807 := bstep (se 1 (by rfl) ⟨6234605, by rfl⟩ : syracuseStep 8312807 = 12469211) B12469211
theorem B1726447 : Blo 1020604 1726447 := bstep (se 1 (by rfl) ⟨1294835, by rfl⟩ : syracuseStep 1726447 = 2589671) B2589671
theorem B1726697 : Blo 1020604 1726697 := bstep (se 2 (by rfl) ⟨647511, by rfl⟩ : syracuseStep 1726697 = 1295023) B1295023
theorem B6543625 : Blo 1020604 6543625 := bstep (se 2 (by rfl) ⟨2453859, by rfl⟩ : syracuseStep 6543625 = 4907719) B4907719
theorem B5822887 : Blo 1020604 5822887 := bstep (se 1 (by rfl) ⟨4367165, by rfl⟩ : syracuseStep 5822887 = 8734331) B8734331
theorem B1531001 : Blo 1020604 1531001 := bstep (se 2 (by rfl) ⟨574125, by rfl⟩ : syracuseStep 1531001 = 1148251) B1148251
theorem B1531103 : Blo 1020604 1531103 := bstep (se 1 (by rfl) ⟨1148327, by rfl⟩ : syracuseStep 1531103 = 2296655) B2296655
theorem B2907389 : Blo 1020604 2907389 := bstep (se 3 (by rfl) ⟨545135, by rfl⟩ : syracuseStep 2907389 = 1090271) B1090271
theorem B9329917 : Blo 1020604 9329917 := bstep (se 3 (by rfl) ⟨1749359, by rfl⟩ : syracuseStep 9329917 = 3498719) B3498719
theorem B1531145 : Blo 1020604 1531145 := bstep (se 2 (by rfl) ⟨574179, by rfl⟩ : syracuseStep 1531145 = 1148359) B1148359
theorem B1531247 : Blo 1020604 1531247 := bstep (se 1 (by rfl) ⟨1148435, by rfl⟩ : syracuseStep 1531247 = 2296871) B2296871
theorem B1531367 : Blo 1020604 1531367 := bstep (se 1 (by rfl) ⟨1148525, by rfl⟩ : syracuseStep 1531367 = 2297051) B2297051
theorem B17456633 : Blo 1020604 17456633 := bstep (se 2 (by rfl) ⟨6546237, by rfl⟩ : syracuseStep 17456633 = 13092475) B13092475
theorem B1662527 : Blo 1020604 1662527 := bstep (se 1 (by rfl) ⟨1246895, by rfl⟩ : syracuseStep 1662527 = 2493791) B2493791
theorem B1531499 : Blo 1020604 1531499 := bstep (se 1 (by rfl) ⟨1148624, by rfl⟩ : syracuseStep 1531499 = 2297249) B2297249
theorem B1728175 : Blo 1020604 1728175 := bstep (se 1 (by rfl) ⟨1296131, by rfl⟩ : syracuseStep 1728175 = 2592263) B2592263
theorem B1531625 : Blo 1020604 1531625 := bstep (se 2 (by rfl) ⟨574359, by rfl⟩ : syracuseStep 1531625 = 1148719) B1148719
theorem B1531769 : Blo 1020604 1531769 := bstep (se 2 (by rfl) ⟨574413, by rfl⟩ : syracuseStep 1531769 = 1148827) B1148827
theorem B1531871 : Blo 1020604 1531871 := bstep (se 1 (by rfl) ⟨1148903, by rfl⟩ : syracuseStep 1531871 = 2297807) B2297807
theorem B1728479 : Blo 1020604 1728479 := bstep (se 1 (by rfl) ⟨1296359, by rfl⟩ : syracuseStep 1728479 = 2592719) B2592719
theorem B1532123 : Blo 1020604 1532123 := bstep (se 1 (by rfl) ⟨1149092, by rfl⟩ : syracuseStep 1532123 = 2298185) B2298185
theorem B1532135 : Blo 1020604 1532135 := bstep (se 1 (by rfl) ⟨1149101, by rfl⟩ : syracuseStep 1532135 = 2298203) B2298203
theorem B1728823 : Blo 1020604 1728823 := bstep (se 1 (by rfl) ⟨1296617, by rfl⟩ : syracuseStep 1728823 = 2593235) B2593235
theorem B1106303 : Blo 1020604 1106303 := bstep (se 1 (by rfl) ⟨829727, by rfl⟩ : syracuseStep 1106303 = 1659455) B1659455
theorem B1532297 : Blo 1020604 1532297 := bstep (se 2 (by rfl) ⟨574611, by rfl⟩ : syracuseStep 1532297 = 1149223) B1149223
theorem B159572429 : Blo 1020604 159572429 := bstep (se 3 (by rfl) ⟨29919830, by rfl⟩ : syracuseStep 159572429 = 59839661) B59839661
theorem B1532393 : Blo 1020604 1532393 := bstep (se 2 (by rfl) ⟨574647, by rfl⟩ : syracuseStep 1532393 = 1149295) B1149295
theorem B1532519 : Blo 1020604 1532519 := bstep (se 1 (by rfl) ⟨1149389, by rfl⟩ : syracuseStep 1532519 = 2298779) B2298779
theorem B2908801 : Blo 1020604 2908801 := bstep (se 2 (by rfl) ⟨1090800, by rfl⟩ : syracuseStep 2908801 = 2181601) B2181601
theorem B2908847 : Blo 1020604 2908847 := bstep (se 1 (by rfl) ⟨2181635, by rfl⟩ : syracuseStep 2908847 = 4363271) B4363271
theorem B1532651 : Blo 1020604 1532651 := bstep (se 1 (by rfl) ⟨1149488, by rfl⟩ : syracuseStep 1532651 = 2298977) B2298977
theorem B1532681 : Blo 1020604 1532681 := bstep (se 2 (by rfl) ⟨574755, by rfl⟩ : syracuseStep 1532681 = 1149511) B1149511
theorem B1532783 : Blo 1020604 1532783 := bstep (se 1 (by rfl) ⟨1149587, by rfl⟩ : syracuseStep 1532783 = 2299175) B2299175
theorem B1533035 : Blo 1020604 1533035 := bstep (se 1 (by rfl) ⟨1149776, by rfl⟩ : syracuseStep 1533035 = 2299553) B2299553
theorem B4908221 : Blo 1020604 4908221 := bstep (se 3 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 4908221 = 1840583) B1840583
theorem B1533275 : Blo 1020604 1533275 := bstep (se 1 (by rfl) ⟨1149956, by rfl⟩ : syracuseStep 1533275 = 2299913) B2299913
theorem B1533551 : Blo 1020604 1533551 := bstep (se 1 (by rfl) ⟨1150163, by rfl⟩ : syracuseStep 1533551 = 2300327) B2300327
theorem B1533623 : Blo 1020604 1533623 := bstep (se 1 (by rfl) ⟨1150217, by rfl⟩ : syracuseStep 1533623 = 2300435) B2300435
theorem B1533659 : Blo 1020604 1533659 := bstep (se 1 (by rfl) ⟨1150244, by rfl⟩ : syracuseStep 1533659 = 2300489) B2300489
theorem B1533833 : Blo 1020604 1533833 := bstep (se 2 (by rfl) ⟨575187, by rfl⟩ : syracuseStep 1533833 = 1150375) B1150375
theorem B1533935 : Blo 1020604 1533935 := bstep (se 1 (by rfl) ⟨1150451, by rfl⟩ : syracuseStep 1533935 = 2300903) B2300903
theorem B1534187 : Blo 1020604 1534187 := bstep (se 1 (by rfl) ⟨1150640, by rfl⟩ : syracuseStep 1534187 = 2301281) B2301281
theorem B1534247 : Blo 1020604 1534247 := bstep (se 1 (by rfl) ⟨1150685, by rfl⟩ : syracuseStep 1534247 = 2301371) B2301371
theorem B1534331 : Blo 1020604 1534331 := bstep (se 1 (by rfl) ⟨1150748, by rfl⟩ : syracuseStep 1534331 = 2301497) B2301497
theorem B3107297 : Blo 1020604 3107297 := bstep (se 2 (by rfl) ⟨1165236, by rfl⟩ : syracuseStep 3107297 = 2330473) B2330473
theorem B1534601 : Blo 1020604 1534601 := bstep (se 2 (by rfl) ⟨575475, by rfl⟩ : syracuseStep 1534601 = 1150951) B1150951
theorem B1534775 : Blo 1020604 1534775 := bstep (se 1 (by rfl) ⟨1151081, by rfl⟩ : syracuseStep 1534775 = 2302163) B2302163
theorem B1534811 : Blo 1020604 1534811 := bstep (se 1 (by rfl) ⟨1151108, by rfl⟩ : syracuseStep 1534811 = 2302217) B2302217
theorem B1534955 : Blo 1020604 1534955 := bstep (se 1 (by rfl) ⟨1151216, by rfl⟩ : syracuseStep 1534955 = 2302433) B2302433
theorem B1535159 : Blo 1020604 1535159 := bstep (se 1 (by rfl) ⟨1151369, by rfl⟩ : syracuseStep 1535159 = 2302739) B2302739
theorem B1535399 : Blo 1020604 1535399 := bstep (se 1 (by rfl) ⟨1151549, by rfl⟩ : syracuseStep 1535399 = 2303099) B2303099
theorem B15756743 : Blo 1020604 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B1535483 : Blo 1020604 1535483 := bstep (se 1 (by rfl) ⟨1151612, by rfl⟩ : syracuseStep 1535483 = 2303225) B2303225
theorem B1535579 : Blo 1020604 1535579 := bstep (se 1 (by rfl) ⟨1151684, by rfl⟩ : syracuseStep 1535579 = 2303369) B2303369
theorem B6221407 : Blo 1020604 6221407 := bstep (se 1 (by rfl) ⟨4666055, by rfl⟩ : syracuseStep 6221407 = 9332111) B9332111
theorem B1535663 : Blo 1020604 1535663 := bstep (se 1 (by rfl) ⟨1151747, by rfl⟩ : syracuseStep 1535663 = 2303495) B2303495
theorem B1535783 : Blo 1020604 1535783 := bstep (se 1 (by rfl) ⟨1151837, by rfl⟩ : syracuseStep 1535783 = 2303675) B2303675
theorem B2912105 : Blo 1020604 2912105 := bstep (se 2 (by rfl) ⟨1092039, by rfl⟩ : syracuseStep 2912105 = 2184079) B2184079
theorem B1535867 : Blo 1020604 1535867 := bstep (se 1 (by rfl) ⟨1151900, by rfl⟩ : syracuseStep 1535867 = 2303801) B2303801
theorem B7368671 : Blo 1020604 7368671 := bstep (se 1 (by rfl) ⟨5526503, by rfl⟩ : syracuseStep 7368671 = 11053007) B11053007
theorem B12415169 : Blo 1020604 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B1536287 : Blo 1020604 1536287 := bstep (se 1 (by rfl) ⟨1152215, by rfl⟩ : syracuseStep 1536287 = 2304431) B2304431
theorem B1536311 : Blo 1020604 1536311 := bstep (se 1 (by rfl) ⟨1152233, by rfl⟩ : syracuseStep 1536311 = 2304467) B2304467
theorem B1536383 : Blo 1020604 1536383 := bstep (se 1 (by rfl) ⟨1152287, by rfl⟩ : syracuseStep 1536383 = 2304575) B2304575
theorem B1536455 : Blo 1020604 1536455 := bstep (se 1 (by rfl) ⟨1152341, by rfl⟩ : syracuseStep 1536455 = 2304683) B2304683
theorem B3273479 : Blo 1020604 3273479 := bstep (se 1 (by rfl) ⟨2455109, by rfl⟩ : syracuseStep 3273479 = 4910219) B4910219
theorem B1536809 : Blo 1020604 1536809 := bstep (se 2 (by rfl) ⟨576303, by rfl⟩ : syracuseStep 1536809 = 1152607) B1152607
theorem B1536815 : Blo 1020604 1536815 := bstep (se 1 (by rfl) ⟨1152611, by rfl⟩ : syracuseStep 1536815 = 2305223) B2305223
theorem B1864615 : Blo 1020604 1864615 := bstep (se 1 (by rfl) ⟨1398461, by rfl⟩ : syracuseStep 1864615 = 2796923) B2796923
theorem B5240531 : Blo 1020604 5240531 := bstep (se 1 (by rfl) ⟨3930398, by rfl⟩ : syracuseStep 5240531 = 7860797) B7860797
theorem B2586431 : Blo 1020604 2586431 := bstep (se 1 (by rfl) ⟨1939823, by rfl⟩ : syracuseStep 2586431 = 3879647) B3879647
theorem B2586887 : Blo 1020604 2586887 := bstep (se 1 (by rfl) ⟨1940165, by rfl⟩ : syracuseStep 2586887 = 3880331) B3880331
theorem B2914633 : Blo 1020604 2914633 := bstep (se 2 (by rfl) ⟨1092987, by rfl⟩ : syracuseStep 2914633 = 2185975) B2185975
theorem B7764335 : Blo 1020604 7764335 := bstep (se 1 (by rfl) ⟨5823251, by rfl⟩ : syracuseStep 7764335 = 11646503) B11646503
theorem B6552647 : Blo 1020604 6552647 := bstep (se 1 (by rfl) ⟨4914485, by rfl⟩ : syracuseStep 6552647 = 9828971) B9828971
theorem B2915453 : Blo 1020604 2915453 := bstep (se 3 (by rfl) ⟨546647, by rfl⟩ : syracuseStep 2915453 = 1093295) B1093295
theorem B2588071 : Blo 1020604 2588071 := bstep (se 1 (by rfl) ⟨1941053, by rfl⟩ : syracuseStep 2588071 = 3882107) B3882107
theorem B4914599 : Blo 1020604 4914599 := bstep (se 1 (by rfl) ⟨3685949, by rfl⟩ : syracuseStep 4914599 = 7371899) B7371899
theorem B13106933 : Blo 1020604 13106933 := bstep (se 5 (by rfl) ⟨614387, by rfl⟩ : syracuseStep 13106933 = 1228775) B1228775
theorem B5538095 : Blo 1020604 5538095 := bstep (se 1 (by rfl) ⟨4153571, by rfl⟩ : syracuseStep 5538095 = 8307143) B8307143
theorem B2916719 : Blo 1020604 2916719 := bstep (se 1 (by rfl) ⟨2187539, by rfl⟩ : syracuseStep 2916719 = 4375079) B4375079
theorem B2457983 : Blo 1020604 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B11043317 : Blo 1020604 11043317 := bstep (se 5 (by rfl) ⟨517655, by rfl⟩ : syracuseStep 11043317 = 1035311) B1035311
theorem B2589803 : Blo 1020604 2589803 := bstep (se 1 (by rfl) ⟨1942352, by rfl⟩ : syracuseStep 2589803 = 3884705) B3884705
theorem B2590177 : Blo 1020604 2590177 := bstep (se 2 (by rfl) ⟨971316, by rfl⟩ : syracuseStep 2590177 = 1942633) B1942633
theorem B9438727 : Blo 1020604 9438727 := bstep (se 1 (by rfl) ⟨7079045, by rfl⟩ : syracuseStep 9438727 = 14158091) B14158091
theorem B1148863 : Blo 1020604 1148863 := bstep (se 1 (by rfl) ⟨861647, by rfl⟩ : syracuseStep 1148863 = 1723295) B1723295
theorem B8751077 : Blo 1020604 8751077 := bstep (se 4 (by rfl) ⟨820413, by rfl⟩ : syracuseStep 8751077 = 1640827) B1640827
theorem B3115169 : Blo 1020604 3115169 := bstep (se 2 (by rfl) ⟨1168188, by rfl⟩ : syracuseStep 3115169 = 2336377) B2336377
theorem B1149151 : Blo 1020604 1149151 := bstep (se 1 (by rfl) ⟨861863, by rfl⟩ : syracuseStep 1149151 = 1723727) B1723727
theorem B12618059 : Blo 1020604 12618059 := bstep (se 1 (by rfl) ⟨9463544, by rfl⟩ : syracuseStep 12618059 = 18927089) B18927089
theorem B2459983 : Blo 1020604 2459983 := bstep (se 1 (by rfl) ⟨1844987, by rfl⟩ : syracuseStep 2459983 = 3689975) B3689975
theorem B2328959 : Blo 1020604 2328959 := bstep (se 1 (by rfl) ⟨1746719, by rfl⟩ : syracuseStep 2328959 = 3493439) B3493439
theorem B5179787 : Blo 1020604 5179787 := bstep (se 1 (by rfl) ⟨3884840, by rfl⟩ : syracuseStep 5179787 = 7769681) B7769681
theorem B6228389 : Blo 1020604 6228389 := bstep (se 4 (by rfl) ⟨583911, by rfl⟩ : syracuseStep 6228389 = 1167823) B1167823
theorem B2296457 : Blo 1020604 2296457 := bstep (se 2 (by rfl) ⟨861171, by rfl⟩ : syracuseStep 2296457 = 1722343) B1722343
theorem B2493089 : Blo 1020604 2493089 := bstep (se 2 (by rfl) ⟨934908, by rfl⟩ : syracuseStep 2493089 = 1869817) B1869817
theorem B9833197 : Blo 1020604 9833197 := bstep (se 3 (by rfl) ⟨1843724, by rfl⟩ : syracuseStep 9833197 = 3687449) B3687449
theorem B4360999 : Blo 1020604 4360999 := bstep (se 1 (by rfl) ⟨3270749, by rfl⟩ : syracuseStep 4360999 = 6541499) B6541499
theorem B37882691 : Blo 1020604 37882691 := bstep (se 1 (by rfl) ⟨28412018, by rfl⟩ : syracuseStep 37882691 = 56824037) B56824037
theorem B2296745 : Blo 1020604 2296745 := bstep (se 2 (by rfl) ⟨861279, by rfl⟩ : syracuseStep 2296745 = 1722559) B1722559
theorem B9341999 : Blo 1020604 9341999 := bstep (se 1 (by rfl) ⟨7006499, by rfl⟩ : syracuseStep 9341999 = 14012999) B14012999
theorem B1150015 : Blo 1020604 1150015 := bstep (se 1 (by rfl) ⟨862511, by rfl⟩ : syracuseStep 1150015 = 1725023) B1725023
theorem B2624575 : Blo 1020604 2624575 := bstep (se 1 (by rfl) ⟨1968431, by rfl⟩ : syracuseStep 2624575 = 3936863) B3936863
theorem B4361323 : Blo 1020604 4361323 := bstep (se 1 (by rfl) ⟨3270992, by rfl⟩ : syracuseStep 4361323 = 6541985) B6541985
theorem B7769195 : Blo 1020604 7769195 := bstep (se 1 (by rfl) ⟨5826896, by rfl⟩ : syracuseStep 7769195 = 11653793) B11653793
theorem B3738811 : Blo 1020604 3738811 := bstep (se 1 (by rfl) ⟨2804108, by rfl⟩ : syracuseStep 3738811 = 5608217) B5608217
theorem B2592121 : Blo 1020604 2592121 := bstep (se 2 (by rfl) ⟨972045, by rfl⟩ : syracuseStep 2592121 = 1944091) B1944091
theorem B11636297 : Blo 1020604 11636297 := bstep (se 2 (by rfl) ⟨4363611, by rfl⟩ : syracuseStep 11636297 = 8727223) B8727223
theorem B2297447 : Blo 1020604 2297447 := bstep (se 1 (by rfl) ⟨1723085, by rfl⟩ : syracuseStep 2297447 = 3446171) B3446171
theorem B9834119 : Blo 1020604 9834119 := bstep (se 1 (by rfl) ⟨7375589, by rfl⟩ : syracuseStep 9834119 = 14751179) B14751179
theorem B4919213 : Blo 1020604 4919213 := bstep (se 3 (by rfl) ⟨922352, by rfl⟩ : syracuseStep 4919213 = 1844705) B1844705
theorem B5181407 : Blo 1020604 5181407 := bstep (se 1 (by rfl) ⟨3886055, by rfl⟩ : syracuseStep 5181407 = 7772111) B7772111
theorem B5541871 : Blo 1020604 5541871 := bstep (se 1 (by rfl) ⟨4156403, by rfl⟩ : syracuseStep 5541871 = 8312807) B8312807
theorem B11800565 : Blo 1020604 11800565 := bstep (se 5 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 11800565 = 1106303) B1106303
theorem B1839199 : Blo 1020604 1839199 := bstep (se 1 (by rfl) ⟨1379399, by rfl⟩ : syracuseStep 1839199 = 2758799) B2758799
theorem B2297951 : Blo 1020604 2297951 := bstep (se 1 (by rfl) ⟨1723463, by rfl⟩ : syracuseStep 2297951 = 3446927) B3446927
theorem B1151131 : Blo 1020604 1151131 := bstep (se 1 (by rfl) ⟨863348, by rfl⟩ : syracuseStep 1151131 = 1726697) B1726697
theorem B1020667 : Blo 1020604 1020667 := bstep (se 1 (by rfl) ⟨765500, by rfl⟩ : syracuseStep 1020667 = 1531001) B1531001
theorem B8295209 : Blo 1020604 8295209 := bstep (se 2 (by rfl) ⟨3110703, by rfl⟩ : syracuseStep 8295209 = 6221407) B6221407
theorem B8721209 : Blo 1020604 8721209 := bstep (se 2 (by rfl) ⟨3270453, by rfl⟩ : syracuseStep 8721209 = 6540907) B6540907
theorem B1020735 : Blo 1020604 1020735 := bstep (se 1 (by rfl) ⟨765551, by rfl⟩ : syracuseStep 1020735 = 1531103) B1531103
theorem B1938259 : Blo 1020604 1938259 := bstep (se 1 (by rfl) ⟨1453694, by rfl⟩ : syracuseStep 1938259 = 2907389) B2907389
theorem B2298707 : Blo 1020604 2298707 := bstep (se 1 (by rfl) ⟨1724030, by rfl⟩ : syracuseStep 2298707 = 3448061) B3448061
theorem B1020763 : Blo 1020604 1020763 := bstep (se 1 (by rfl) ⟨765572, by rfl⟩ : syracuseStep 1020763 = 1531145) B1531145
theorem B1020831 : Blo 1020604 1020831 := bstep (se 1 (by rfl) ⟨765623, by rfl⟩ : syracuseStep 1020831 = 1531247) B1531247
theorem B1020911 : Blo 1020604 1020911 := bstep (se 1 (by rfl) ⟨765683, by rfl⟩ : syracuseStep 1020911 = 1531367) B1531367
theorem B11637755 : Blo 1020604 11637755 := bstep (se 1 (by rfl) ⟨8728316, by rfl⟩ : syracuseStep 11637755 = 17456633) B17456633
theorem B1020999 : Blo 1020604 1020999 := bstep (se 1 (by rfl) ⟨765749, by rfl⟩ : syracuseStep 1020999 = 1531499) B1531499
theorem B1021083 : Blo 1020604 1021083 := bstep (se 1 (by rfl) ⟨765812, by rfl⟩ : syracuseStep 1021083 = 1531625) B1531625
theorem B1938593 : Blo 1020604 1938593 := bstep (se 2 (by rfl) ⟨726972, by rfl⟩ : syracuseStep 1938593 = 1453945) B1453945
theorem B1021179 : Blo 1020604 1021179 := bstep (se 1 (by rfl) ⟨765884, by rfl⟩ : syracuseStep 1021179 = 1531769) B1531769
theorem B1021247 : Blo 1020604 1021247 := bstep (se 1 (by rfl) ⟨765935, by rfl⟩ : syracuseStep 1021247 = 1531871) B1531871
theorem B1152319 : Blo 1020604 1152319 := bstep (se 1 (by rfl) ⟨864239, by rfl⟩ : syracuseStep 1152319 = 1728479) B1728479
theorem B2299247 : Blo 1020604 2299247 := bstep (se 1 (by rfl) ⟨1724435, by rfl⟩ : syracuseStep 2299247 = 3448871) B3448871
theorem B1021415 : Blo 1020604 1021415 := bstep (se 1 (by rfl) ⟨766061, by rfl⟩ : syracuseStep 1021415 = 1532123) B1532123
theorem B1021423 : Blo 1020604 1021423 := bstep (se 1 (by rfl) ⟨766067, by rfl⟩ : syracuseStep 1021423 = 1532135) B1532135
theorem B1021531 : Blo 1020604 1021531 := bstep (se 1 (by rfl) ⟨766148, by rfl⟩ : syracuseStep 1021531 = 1532297) B1532297
theorem B1021595 : Blo 1020604 1021595 := bstep (se 1 (by rfl) ⟨766196, by rfl⟩ : syracuseStep 1021595 = 1532393) B1532393
theorem B1021679 : Blo 1020604 1021679 := bstep (se 1 (by rfl) ⟨766259, by rfl⟩ : syracuseStep 1021679 = 1532519) B1532519
theorem B1939231 : Blo 1020604 1939231 := bstep (se 1 (by rfl) ⟨1454423, by rfl⟩ : syracuseStep 1939231 = 2908847) B2908847
theorem B2299679 : Blo 1020604 2299679 := bstep (se 1 (by rfl) ⟨1724759, by rfl⟩ : syracuseStep 2299679 = 3449519) B3449519
theorem B1021767 : Blo 1020604 1021767 := bstep (se 1 (by rfl) ⟨766325, by rfl⟩ : syracuseStep 1021767 = 1532651) B1532651
theorem B1021787 : Blo 1020604 1021787 := bstep (se 1 (by rfl) ⟨766340, by rfl⟩ : syracuseStep 1021787 = 1532681) B1532681
theorem B9115537 : Blo 1020604 9115537 := bstep (se 2 (by rfl) ⟨3418326, by rfl⟩ : syracuseStep 9115537 = 6836653) B6836653
theorem B1021855 : Blo 1020604 1021855 := bstep (se 1 (by rfl) ⟨766391, by rfl⟩ : syracuseStep 1021855 = 1532783) B1532783
theorem B2299895 : Blo 1020604 2299895 := bstep (se 1 (by rfl) ⟨1724921, by rfl⟩ : syracuseStep 2299895 = 3449843) B3449843
theorem B1022023 : Blo 1020604 1022023 := bstep (se 1 (by rfl) ⟨766517, by rfl⟩ : syracuseStep 1022023 = 1533035) B1533035
theorem B1022183 : Blo 1020604 1022183 := bstep (se 1 (by rfl) ⟨766637, by rfl⟩ : syracuseStep 1022183 = 1533275) B1533275
theorem B2300255 : Blo 1020604 2300255 := bstep (se 1 (by rfl) ⟨1725191, by rfl⟩ : syracuseStep 2300255 = 3450383) B3450383
theorem B1022367 : Blo 1020604 1022367 := bstep (se 1 (by rfl) ⟨766775, by rfl⟩ : syracuseStep 1022367 = 1533551) B1533551
theorem B1022415 : Blo 1020604 1022415 := bstep (se 1 (by rfl) ⟨766811, by rfl⟩ : syracuseStep 1022415 = 1533623) B1533623
theorem B1022439 : Blo 1020604 1022439 := bstep (se 1 (by rfl) ⟨766829, by rfl⟩ : syracuseStep 1022439 = 1533659) B1533659
theorem B1939945 : Blo 1020604 1939945 := bstep (se 2 (by rfl) ⟨727479, by rfl⟩ : syracuseStep 1939945 = 1454959) B1454959
theorem B1022555 : Blo 1020604 1022555 := bstep (se 1 (by rfl) ⟨766916, by rfl⟩ : syracuseStep 1022555 = 1533833) B1533833
theorem B1022623 : Blo 1020604 1022623 := bstep (se 1 (by rfl) ⟨766967, by rfl⟩ : syracuseStep 1022623 = 1533935) B1533935
theorem B1022791 : Blo 1020604 1022791 := bstep (se 1 (by rfl) ⟨767093, by rfl⟩ : syracuseStep 1022791 = 1534187) B1534187
theorem B1022831 : Blo 1020604 1022831 := bstep (se 1 (by rfl) ⟨767123, by rfl⟩ : syracuseStep 1022831 = 1534247) B1534247
theorem B2300795 : Blo 1020604 2300795 := bstep (se 1 (by rfl) ⟨1725596, by rfl⟩ : syracuseStep 2300795 = 3451193) B3451193
theorem B1022887 : Blo 1020604 1022887 := bstep (se 1 (by rfl) ⟨767165, by rfl⟩ : syracuseStep 1022887 = 1534331) B1534331
theorem B2071531 : Blo 1020604 2071531 := bstep (se 1 (by rfl) ⟨1553648, by rfl⟩ : syracuseStep 2071531 = 3107297) B3107297
theorem B2300975 : Blo 1020604 2300975 := bstep (se 1 (by rfl) ⟨1725731, by rfl⟩ : syracuseStep 2300975 = 3451463) B3451463
theorem B1023067 : Blo 1020604 1023067 := bstep (se 1 (by rfl) ⟨767300, by rfl⟩ : syracuseStep 1023067 = 1534601) B1534601
theorem B1023183 : Blo 1020604 1023183 := bstep (se 1 (by rfl) ⟨767387, by rfl⟩ : syracuseStep 1023183 = 1534775) B1534775
theorem B1023207 : Blo 1020604 1023207 := bstep (se 1 (by rfl) ⟨767405, by rfl⟩ : syracuseStep 1023207 = 1534811) B1534811
theorem B1023303 : Blo 1020604 1023303 := bstep (se 1 (by rfl) ⟨767477, by rfl⟩ : syracuseStep 1023303 = 1534955) B1534955
theorem B1023439 : Blo 1020604 1023439 := bstep (se 1 (by rfl) ⟨767579, by rfl⟩ : syracuseStep 1023439 = 1535159) B1535159
theorem B1023599 : Blo 1020604 1023599 := bstep (se 1 (by rfl) ⟨767699, by rfl⟩ : syracuseStep 1023599 = 1535399) B1535399
theorem B1023655 : Blo 1020604 1023655 := bstep (se 1 (by rfl) ⟨767741, by rfl⟩ : syracuseStep 1023655 = 1535483) B1535483
theorem B2301659 : Blo 1020604 2301659 := bstep (se 1 (by rfl) ⟨1726244, by rfl⟩ : syracuseStep 2301659 = 3452489) B3452489
theorem B1023719 : Blo 1020604 1023719 := bstep (se 1 (by rfl) ⟨767789, by rfl⟩ : syracuseStep 1023719 = 1535579) B1535579
theorem B1023775 : Blo 1020604 1023775 := bstep (se 1 (by rfl) ⟨767831, by rfl⟩ : syracuseStep 1023775 = 1535663) B1535663
theorem B1023855 : Blo 1020604 1023855 := bstep (se 1 (by rfl) ⟨767891, by rfl⟩ : syracuseStep 1023855 = 1535783) B1535783
theorem B1941403 : Blo 1020604 1941403 := bstep (se 1 (by rfl) ⟨1456052, by rfl⟩ : syracuseStep 1941403 = 2912105) B2912105
theorem B1023911 : Blo 1020604 1023911 := bstep (se 1 (by rfl) ⟨767933, by rfl⟩ : syracuseStep 1023911 = 1535867) B1535867
theorem B2301929 : Blo 1020604 2301929 := bstep (se 2 (by rfl) ⟨863223, by rfl⟩ : syracuseStep 2301929 = 1726447) B1726447
theorem B4661387 : Blo 1020604 4661387 := bstep (se 1 (by rfl) ⟨3496040, by rfl⟩ : syracuseStep 4661387 = 6992081) B6992081
theorem B1024191 : Blo 1020604 1024191 := bstep (se 1 (by rfl) ⟨768143, by rfl⟩ : syracuseStep 1024191 = 1536287) B1536287
theorem B1024207 : Blo 1020604 1024207 := bstep (se 1 (by rfl) ⟨768155, by rfl⟩ : syracuseStep 1024207 = 1536311) B1536311
theorem B1024255 : Blo 1020604 1024255 := bstep (se 1 (by rfl) ⟨768191, by rfl⟩ : syracuseStep 1024255 = 1536383) B1536383
theorem B1024303 : Blo 1020604 1024303 := bstep (se 1 (by rfl) ⟨768227, by rfl⟩ : syracuseStep 1024303 = 1536455) B1536455
theorem B7774541 : Blo 1020604 7774541 := bstep (se 3 (by rfl) ⟨1457726, by rfl⟩ : syracuseStep 7774541 = 2915453) B2915453
theorem B8724833 : Blo 1020604 8724833 := bstep (se 2 (by rfl) ⟨3271812, by rfl⟩ : syracuseStep 8724833 = 6543625) B6543625
theorem B1024539 : Blo 1020604 1024539 := bstep (se 1 (by rfl) ⟨768404, by rfl⟩ : syracuseStep 1024539 = 1536809) B1536809
theorem B1024543 : Blo 1020604 1024543 := bstep (se 1 (by rfl) ⟨768407, by rfl⟩ : syracuseStep 1024543 = 1536815) B1536815
theorem B2302631 : Blo 1020604 2302631 := bstep (se 1 (by rfl) ⟨1726973, by rfl⟩ : syracuseStep 2302631 = 3453947) B3453947
theorem B2761435 : Blo 1020604 2761435 := bstep (se 1 (by rfl) ⟨2071076, by rfl⟩ : syracuseStep 2761435 = 4142153) B4142153
theorem B2302775 : Blo 1020604 2302775 := bstep (se 1 (by rfl) ⟨1727081, by rfl⟩ : syracuseStep 2302775 = 3454163) B3454163
theorem B5186429 : Blo 1020604 5186429 := bstep (se 3 (by rfl) ⟨972455, by rfl⟩ : syracuseStep 5186429 = 1944911) B1944911
theorem B2302955 : Blo 1020604 2302955 := bstep (se 1 (by rfl) ⟨1727216, by rfl⟩ : syracuseStep 2302955 = 3454433) B3454433
theorem B2303387 : Blo 1020604 2303387 := bstep (se 1 (by rfl) ⟨1727540, by rfl⟩ : syracuseStep 2303387 = 3455081) B3455081
theorem B3450761 : Blo 1020604 3450761 := bstep (se 2 (by rfl) ⟨1294035, by rfl⟩ : syracuseStep 3450761 = 2588071) B2588071
theorem B2303963 : Blo 1020604 2303963 := bstep (se 1 (by rfl) ⟨1727972, by rfl⟩ : syracuseStep 2303963 = 3455945) B3455945
theorem B17704927 : Blo 1020604 17704927 := bstep (se 1 (by rfl) ⟨13278695, by rfl⟩ : syracuseStep 17704927 = 26557391) B26557391
theorem B4368431 : Blo 1020604 4368431 := bstep (se 1 (by rfl) ⟨3276323, by rfl⟩ : syracuseStep 4368431 = 6552647) B6552647
theorem B2304143 : Blo 1020604 2304143 := bstep (se 1 (by rfl) ⟨1728107, by rfl⟩ : syracuseStep 2304143 = 3456215) B3456215
theorem B2304233 : Blo 1020604 2304233 := bstep (se 2 (by rfl) ⟨864087, by rfl⟩ : syracuseStep 2304233 = 1728175) B1728175
theorem B2304503 : Blo 1020604 2304503 := bstep (se 1 (by rfl) ⟨1728377, by rfl⟩ : syracuseStep 2304503 = 3456755) B3456755
theorem B7776971 : Blo 1020604 7776971 := bstep (se 1 (by rfl) ⟨5832728, by rfl⟩ : syracuseStep 7776971 = 11665457) B11665457
theorem B19639259 : Blo 1020604 19639259 := bstep (se 1 (by rfl) ⟨14729444, by rfl⟩ : syracuseStep 19639259 = 29458889) B29458889
theorem B2305097 : Blo 1020604 2305097 := bstep (se 2 (by rfl) ⟨864411, by rfl⟩ : syracuseStep 2305097 = 1728823) B1728823
theorem B3878401 : Blo 1020604 3878401 := bstep (se 2 (by rfl) ⟨1454400, by rfl⟩ : syracuseStep 3878401 = 2908801) B2908801
theorem B1093223 : Blo 1020604 1093223 := bstep (se 1 (by rfl) ⟨819917, by rfl⟩ : syracuseStep 1093223 = 1639835) B1639835
theorem B13119083 : Blo 1020604 13119083 := bstep (se 1 (by rfl) ⟨9839312, by rfl⟩ : syracuseStep 13119083 = 19678625) B19678625
theorem B4370105 : Blo 1020604 4370105 := bstep (se 2 (by rfl) ⟨1638789, by rfl⟩ : syracuseStep 4370105 = 3277579) B3277579
theorem B9842579 : Blo 1020604 9842579 := bstep (se 1 (by rfl) ⟨7381934, by rfl⟩ : syracuseStep 9842579 = 14763869) B14763869
theorem B5517767 : Blo 1020604 5517767 := bstep (se 1 (by rfl) ⟨4138325, by rfl⟩ : syracuseStep 5517767 = 8276651) B8276651
theorem B1455175 : Blo 1020604 1455175 := bstep (se 1 (by rfl) ⟨1091381, by rfl⟩ : syracuseStep 1455175 = 2182763) B2182763
theorem B7779401 : Blo 1020604 7779401 := bstep (se 2 (by rfl) ⟨2917275, by rfl⟩ : syracuseStep 7779401 = 5834551) B5834551
theorem B3454217 : Blo 1020604 3454217 := bstep (se 2 (by rfl) ⟨1295331, by rfl⟩ : syracuseStep 3454217 = 2590663) B2590663
theorem B3880619 : Blo 1020604 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B3454703 : Blo 1020604 3454703 := bstep (se 1 (by rfl) ⟨2591027, by rfl⟩ : syracuseStep 3454703 = 5182055) B5182055
theorem B12433277 : Blo 1020604 12433277 := bstep (se 3 (by rfl) ⟨2331239, by rfl⟩ : syracuseStep 12433277 = 4662479) B4662479
theorem B4372481 : Blo 1020604 4372481 := bstep (se 2 (by rfl) ⟨1639680, by rfl⟩ : syracuseStep 4372481 = 3279361) B3279361
theorem B5519411 : Blo 1020604 5519411 := bstep (se 1 (by rfl) ⟨4139558, by rfl⟩ : syracuseStep 5519411 = 8279117) B8279117
theorem B3455675 : Blo 1020604 3455675 := bstep (se 1 (by rfl) ⟨2591756, by rfl⟩ : syracuseStep 3455675 = 5183513) B5183513
theorem B17447885 : Blo 1020604 17447885 := bstep (se 3 (by rfl) ⟨3271478, by rfl⟩ : syracuseStep 17447885 = 6542957) B6542957
theorem B1293403 : Blo 1020604 1293403 := bstep (se 1 (by rfl) ⟨970052, by rfl⟩ : syracuseStep 1293403 = 1940105) B1940105
theorem B9846269 : Blo 1020604 9846269 := bstep (se 3 (by rfl) ⟨1846175, by rfl⟩ : syracuseStep 9846269 = 3692351) B3692351
theorem B5815871 : Blo 1020604 5815871 := bstep (se 1 (by rfl) ⟨4361903, by rfl⟩ : syracuseStep 5815871 = 8723807) B8723807
theorem B79806167 : Blo 1020604 79806167 := bstep (se 1 (by rfl) ⟨59854625, by rfl⟩ : syracuseStep 79806167 = 119709251) B119709251
theorem B4374719 : Blo 1020604 4374719 := bstep (se 1 (by rfl) ⟨3281039, by rfl⟩ : syracuseStep 4374719 = 6562079) B6562079
theorem B1229035 : Blo 1020604 1229035 := bstep (se 1 (by rfl) ⟨921776, by rfl⟩ : syracuseStep 1229035 = 1843553) B1843553
theorem B3883261 : Blo 1020604 3883261 := bstep (se 3 (by rfl) ⟨728111, by rfl⟩ : syracuseStep 3883261 = 1456223) B1456223
theorem B106381619 : Blo 1020604 106381619 := bstep (se 1 (by rfl) ⟨79786214, by rfl⟩ : syracuseStep 106381619 = 159572429) B159572429
theorem B7750241 : Blo 1020604 7750241 := bstep (se 2 (by rfl) ⟨2906340, by rfl⟩ : syracuseStep 7750241 = 5812681) B5812681
theorem B11650877 : Blo 1020604 11650877 := bstep (se 3 (by rfl) ⟨2184539, by rfl⟩ : syracuseStep 11650877 = 4369079) B4369079
theorem B4376393 : Blo 1020604 4376393 := bstep (se 2 (by rfl) ⟨1641147, by rfl⟩ : syracuseStep 4376393 = 3282295) B3282295
theorem B1296415 : Blo 1020604 1296415 := bstep (se 1 (by rfl) ⟨972311, by rfl⟩ : syracuseStep 1296415 = 1944623) B1944623
theorem B5818513 : Blo 1020604 5818513 := bstep (se 2 (by rfl) ⟨2181942, by rfl⟩ : syracuseStep 5818513 = 4363885) B4363885
theorem B10504495 : Blo 1020604 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B8276779 : Blo 1020604 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B3886177 : Blo 1020604 3886177 := bstep (se 2 (by rfl) ⟨1457316, by rfl⟩ : syracuseStep 3886177 = 2914633) B2914633
theorem B2182319 : Blo 1020604 2182319 := bstep (se 1 (by rfl) ⟨1636739, by rfl⟩ : syracuseStep 2182319 = 3273479) B3273479
theorem B9096425 : Blo 1020604 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B7359905 : Blo 1020604 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B3493687 : Blo 1020604 3493687 := bstep (se 1 (by rfl) ⟨2620265, by rfl⟩ : syracuseStep 3493687 = 5240531) B5240531
theorem B1724287 : Blo 1020604 1724287 := bstep (se 1 (by rfl) ⟨1293215, by rfl⟩ : syracuseStep 1724287 = 2586431) B2586431
theorem B6213671 : Blo 1020604 6213671 := bstep (se 1 (by rfl) ⟨4660253, by rfl⟩ : syracuseStep 6213671 = 9320507) B9320507
theorem B10506341 : Blo 1020604 10506341 := bstep (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) B1969939
theorem B1724591 : Blo 1020604 1724591 := bstep (se 1 (by rfl) ⟨1293443, by rfl⟩ : syracuseStep 1724591 = 2586887) B2586887
theorem B12439889 : Blo 1020604 12439889 := bstep (se 2 (by rfl) ⟨4664958, by rfl⟩ : syracuseStep 12439889 = 9329917) B9329917
theorem B169988813 : Blo 1020604 169988813 := bstep (se 3 (by rfl) ⟨31872902, by rfl⟩ : syracuseStep 169988813 = 63745805) B63745805
theorem B8737955 : Blo 1020604 8737955 := bstep (se 1 (by rfl) ⟨6553466, by rfl⟩ : syracuseStep 8737955 = 13106933) B13106933
theorem B4905107 : Blo 1020604 4905107 := bstep (se 1 (by rfl) ⟨3678830, by rfl⟩ : syracuseStep 4905107 = 7357661) B7357661
theorem B1726751 : Blo 1020604 1726751 := bstep (se 1 (by rfl) ⟨1295063, by rfl⟩ : syracuseStep 1726751 = 2590127) B2590127
theorem B1726879 : Blo 1020604 1726879 := bstep (se 1 (by rfl) ⟨1295159, by rfl⟩ : syracuseStep 1726879 = 2590319) B2590319
theorem B2185633 : Blo 1020604 2185633 := bstep (se 2 (by rfl) ⟨819612, by rfl⟩ : syracuseStep 2185633 = 1639225) B1639225
theorem B13097807 : Blo 1020604 13097807 := bstep (se 1 (by rfl) ⟨9823355, by rfl⟩ : syracuseStep 13097807 = 19646711) B19646711
theorem B4906433 : Blo 1020604 4906433 := bstep (se 2 (by rfl) ⟨1839912, by rfl⟩ : syracuseStep 4906433 = 3679825) B3679825
theorem B9461281 : Blo 1020604 9461281 := bstep (se 2 (by rfl) ⟨3547980, by rfl⟩ : syracuseStep 9461281 = 7095961) B7095961
theorem B1728121 : Blo 1020604 1728121 := bstep (se 2 (by rfl) ⟨648045, by rfl⟩ : syracuseStep 1728121 = 1296091) B1296091
theorem B1531559 : Blo 1020604 1531559 := bstep (se 1 (by rfl) ⟨1148669, by rfl⟩ : syracuseStep 1531559 = 2297339) B2297339
theorem B1531679 : Blo 1020604 1531679 := bstep (se 1 (by rfl) ⟨1148759, by rfl⟩ : syracuseStep 1531679 = 2297519) B2297519
theorem B1532111 : Blo 1020604 1532111 := bstep (se 1 (by rfl) ⟨1149083, by rfl⟩ : syracuseStep 1532111 = 2298167) B2298167
theorem B1532159 : Blo 1020604 1532159 := bstep (se 1 (by rfl) ⟨1149119, by rfl⟩ : syracuseStep 1532159 = 2298239) B2298239
theorem B11821385 : Blo 1020604 11821385 := bstep (se 2 (by rfl) ⟨4433019, by rfl⟩ : syracuseStep 11821385 = 8866039) B8866039
theorem B6218291 : Blo 1020604 6218291 := bstep (se 1 (by rfl) ⟨4663718, by rfl⟩ : syracuseStep 6218291 = 9327437) B9327437
theorem B20964395 : Blo 1020604 20964395 := bstep (se 1 (by rfl) ⟨15723296, by rfl⟩ : syracuseStep 20964395 = 31446593) B31446593
theorem B1532975 : Blo 1020604 1532975 := bstep (se 1 (by rfl) ⟨1149731, by rfl⟩ : syracuseStep 1532975 = 2299463) B2299463
theorem B1533095 : Blo 1020604 1533095 := bstep (se 1 (by rfl) ⟨1149821, by rfl⟩ : syracuseStep 1533095 = 2299643) B2299643
theorem B1533467 : Blo 1020604 1533467 := bstep (se 1 (by rfl) ⟨1150100, by rfl⟩ : syracuseStep 1533467 = 2300201) B2300201
theorem B1533851 : Blo 1020604 1533851 := bstep (se 1 (by rfl) ⟨1150388, by rfl⟩ : syracuseStep 1533851 = 2300777) B2300777
theorem B3270557 : Blo 1020604 3270557 := bstep (se 3 (by rfl) ⟨613229, by rfl⟩ : syracuseStep 3270557 = 1226459) B1226459
theorem B1533887 : Blo 1020604 1533887 := bstep (se 1 (by rfl) ⟨1150415, by rfl⟩ : syracuseStep 1533887 = 2300831) B2300831
theorem B2910305 : Blo 1020604 2910305 := bstep (se 2 (by rfl) ⟨1091364, by rfl⟩ : syracuseStep 2910305 = 2182729) B2182729
theorem B1534073 : Blo 1020604 1534073 := bstep (se 2 (by rfl) ⟨575277, by rfl⟩ : syracuseStep 1534073 = 1150555) B1150555
theorem B1108351 : Blo 1020604 1108351 := bstep (se 1 (by rfl) ⟨831263, by rfl⟩ : syracuseStep 1108351 = 1662527) B1662527
theorem B1534457 : Blo 1020604 1534457 := bstep (se 2 (by rfl) ⟨575421, by rfl⟩ : syracuseStep 1534457 = 1150843) B1150843
theorem B1534511 : Blo 1020604 1534511 := bstep (se 1 (by rfl) ⟨1150883, by rfl⟩ : syracuseStep 1534511 = 2301767) B2301767
theorem B2452447 : Blo 1020604 2452447 := bstep (se 1 (by rfl) ⟨1839335, by rfl⟩ : syracuseStep 2452447 = 3678671) B3678671
theorem B1534943 : Blo 1020604 1534943 := bstep (se 1 (by rfl) ⟨1151207, by rfl⟩ : syracuseStep 1534943 = 2302415) B2302415
theorem B1535387 : Blo 1020604 1535387 := bstep (se 1 (by rfl) ⟨1151540, by rfl⟩ : syracuseStep 1535387 = 2303081) B2303081
theorem B3272147 : Blo 1020604 3272147 := bstep (se 1 (by rfl) ⟨2454110, by rfl⟩ : syracuseStep 3272147 = 4908221) B4908221
theorem B7368185 : Blo 1020604 7368185 := bstep (se 2 (by rfl) ⟨2763069, by rfl⟩ : syracuseStep 7368185 = 5526139) B5526139
theorem B17461007 : Blo 1020604 17461007 := bstep (se 1 (by rfl) ⟨13095755, by rfl⟩ : syracuseStep 17461007 = 26191511) B26191511
theorem B1535807 : Blo 1020604 1535807 := bstep (se 1 (by rfl) ⟨1151855, by rfl⟩ : syracuseStep 1535807 = 2303711) B2303711
theorem B2486153 : Blo 1020604 2486153 := bstep (se 2 (by rfl) ⟨932307, by rfl⟩ : syracuseStep 2486153 = 1864615) B1864615
theorem B2912219 : Blo 1020604 2912219 := bstep (se 1 (by rfl) ⟨2184164, by rfl⟩ : syracuseStep 2912219 = 4368329) B4368329
theorem B1535993 : Blo 1020604 1535993 := bstep (se 2 (by rfl) ⟨575997, by rfl⟩ : syracuseStep 1535993 = 1151995) B1151995
theorem B2584649 : Blo 1020604 2584649 := bstep (se 2 (by rfl) ⟨969243, by rfl⟩ : syracuseStep 2584649 = 1938487) B1938487
theorem B1536233 : Blo 1020604 1536233 := bstep (se 2 (by rfl) ⟨576087, by rfl⟩ : syracuseStep 1536233 = 1152175) B1152175
theorem B2912537 : Blo 1020604 2912537 := bstep (se 2 (by rfl) ⟨1092201, by rfl⟩ : syracuseStep 2912537 = 2184403) B2184403
theorem B1536359 : Blo 1020604 1536359 := bstep (se 1 (by rfl) ⟨1152269, by rfl⟩ : syracuseStep 1536359 = 2304539) B2304539
theorem B11629007 : Blo 1020604 11629007 := bstep (se 1 (by rfl) ⟨8721755, by rfl⟩ : syracuseStep 11629007 = 17443511) B17443511
theorem B7762391 : Blo 1020604 7762391 := bstep (se 1 (by rfl) ⟨5821793, by rfl⟩ : syracuseStep 7762391 = 11643587) B11643587
theorem B1536905 : Blo 1020604 1536905 := bstep (se 2 (by rfl) ⟨576339, by rfl⟩ : syracuseStep 1536905 = 1152679) B1152679
theorem B2585783 : Blo 1020604 2585783 := bstep (se 1 (by rfl) ⟨1939337, by rfl⟩ : syracuseStep 2585783 = 3878675) B3878675
theorem B4912447 : Blo 1020604 4912447 := bstep (se 1 (by rfl) ⟨3684335, by rfl⟩ : syracuseStep 4912447 = 7368671) B7368671
theorem B26965865 : Blo 1020604 26965865 := bstep (se 2 (by rfl) ⟨10112199, by rfl⟩ : syracuseStep 26965865 = 20224399) B20224399
theorem B7763849 : Blo 1020604 7763849 := bstep (se 2 (by rfl) ⟨2911443, by rfl⟩ : syracuseStep 7763849 = 5822887) B5822887
theorem B13105597 : Blo 1020604 13105597 := bstep (se 3 (by rfl) ⟨2457299, by rfl⟩ : syracuseStep 13105597 = 4914599) B4914599
theorem B2587241 : Blo 1020604 2587241 := bstep (se 2 (by rfl) ⟨970215, by rfl⟩ : syracuseStep 2587241 = 1940431) B1940431
theorem B3111529 : Blo 1020604 3111529 := bstep (se 2 (by rfl) ⟨1166823, by rfl⟩ : syracuseStep 3111529 = 2333647) B2333647
theorem B8289107 : Blo 1020604 8289107 := bstep (se 1 (by rfl) ⟨6216830, by rfl⟩ : syracuseStep 8289107 = 12433661) B12433661
theorem B5176223 : Blo 1020604 5176223 := bstep (se 1 (by rfl) ⟨3882167, by rfl⟩ : syracuseStep 5176223 = 7764335) B7764335
theorem B4914121 : Blo 1020604 4914121 := bstep (se 2 (by rfl) ⟨1842795, by rfl⟩ : syracuseStep 4914121 = 3685591) B3685591
theorem B2456801 : Blo 1020604 2456801 := bstep (se 2 (by rfl) ⟨921300, by rfl⟩ : syracuseStep 2456801 = 1842601) B1842601
theorem B31489829 : Blo 1020604 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B5537575 : Blo 1020604 5537575 := bstep (se 1 (by rfl) ⟨4153181, by rfl⟩ : syracuseStep 5537575 = 8306363) B8306363
theorem B2916479 : Blo 1020604 2916479 := bstep (se 1 (by rfl) ⟨2187359, by rfl⟩ : syracuseStep 2916479 = 4374719) B4374719
theorem B1638713 : Blo 1020604 1638713 := bstep (se 2 (by rfl) ⟨614517, by rfl⟩ : syracuseStep 1638713 = 1229035) B1229035
theorem B5177681 : Blo 1020604 5177681 := bstep (se 2 (by rfl) ⟨1941630, by rfl⟩ : syracuseStep 5177681 = 3883261) B3883261
theorem B7766765 : Blo 1020604 7766765 := bstep (se 3 (by rfl) ⟨1456268, by rfl⟩ : syracuseStep 7766765 = 2912537) B2912537
theorem B6554621 : Blo 1020604 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B14714045 : Blo 1020604 14714045 := bstep (se 3 (by rfl) ⟨2758883, by rfl⟩ : syracuseStep 14714045 = 5517767) B5517767
theorem B7767251 : Blo 1020604 7767251 := bstep (se 1 (by rfl) ⟨5825438, by rfl⟩ : syracuseStep 7767251 = 11650877) B11650877
theorem B2917595 : Blo 1020604 2917595 := bstep (se 1 (by rfl) ⟨2188196, by rfl⟩ : syracuseStep 2917595 = 4376393) B4376393
theorem B5834051 : Blo 1020604 5834051 := bstep (se 1 (by rfl) ⟨4375538, by rfl⟩ : syracuseStep 5834051 = 8751077) B8751077
theorem B12584969 : Blo 1020604 12584969 := bstep (se 2 (by rfl) ⟨4719363, by rfl⟩ : syracuseStep 12584969 = 9438727) B9438727
theorem B6227999 : Blo 1020604 6227999 := bstep (se 1 (by rfl) ⟨4670999, by rfl⟩ : syracuseStep 6227999 = 9341999) B9341999
theorem B5179463 : Blo 1020604 5179463 := bstep (se 1 (by rfl) ⟨3884597, by rfl⟩ : syracuseStep 5179463 = 7769195) B7769195
theorem B6064283 : Blo 1020604 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B6556079 : Blo 1020604 6556079 := bstep (se 1 (by rfl) ⟨4917059, by rfl⟩ : syracuseStep 6556079 = 9834119) B9834119
theorem B3279475 : Blo 1020604 3279475 := bstep (se 1 (by rfl) ⟨2459606, by rfl⟩ : syracuseStep 3279475 = 4919213) B4919213
theorem B7867043 : Blo 1020604 7867043 := bstep (se 1 (by rfl) ⟨5900282, by rfl⟩ : syracuseStep 7867043 = 11800565) B11800565
theorem B1149727 : Blo 1020604 1149727 := bstep (se 1 (by rfl) ⟨862295, by rfl⟩ : syracuseStep 1149727 = 1724591) B1724591
theorem B8293259 : Blo 1020604 8293259 := bstep (se 1 (by rfl) ⟨6219944, by rfl⟩ : syracuseStep 8293259 = 12439889) B12439889
theorem B3279977 : Blo 1020604 3279977 := bstep (se 2 (by rfl) ⟨1229991, by rfl⟩ : syracuseStep 3279977 = 2459983) B2459983
theorem B1477801 : Blo 1020604 1477801 := bstep (se 2 (by rfl) ⟨554175, by rfl⟩ : syracuseStep 1477801 = 1108351) B1108351
theorem B13110929 : Blo 1020604 13110929 := bstep (se 2 (by rfl) ⟨4916598, by rfl⟩ : syracuseStep 13110929 = 9833197) B9833197
theorem B5181569 : Blo 1020604 5181569 := bstep (se 2 (by rfl) ⟨1943088, by rfl⟩ : syracuseStep 5181569 = 3886177) B3886177
theorem B1151167 : Blo 1020604 1151167 := bstep (se 1 (by rfl) ⟨863375, by rfl⟩ : syracuseStep 1151167 = 1726751) B1726751
theorem B4985081 : Blo 1020604 4985081 := bstep (se 2 (by rfl) ⟨1869405, by rfl⟩ : syracuseStep 4985081 = 3738811) B3738811
theorem B4658249 : Blo 1020604 4658249 := bstep (se 2 (by rfl) ⟨1746843, by rfl⟩ : syracuseStep 4658249 = 3493687) B3493687
theorem B1021039 : Blo 1020604 1021039 := bstep (se 1 (by rfl) ⟨765779, by rfl⟩ : syracuseStep 1021039 = 1531559) B1531559
theorem B13079717 : Blo 1020604 13079717 := bstep (se 4 (by rfl) ⟨1226223, by rfl⟩ : syracuseStep 13079717 = 2452447) B2452447
theorem B2299049 : Blo 1020604 2299049 := bstep (se 2 (by rfl) ⟨862143, by rfl⟩ : syracuseStep 2299049 = 1724287) B1724287
theorem B1021119 : Blo 1020604 1021119 := bstep (se 1 (by rfl) ⟨765839, by rfl⟩ : syracuseStep 1021119 = 1531679) B1531679
theorem B1021407 : Blo 1020604 1021407 := bstep (se 1 (by rfl) ⟨766055, by rfl⟩ : syracuseStep 1021407 = 1532111) B1532111
theorem B1021439 : Blo 1020604 1021439 := bstep (se 1 (by rfl) ⟨766079, by rfl⟩ : syracuseStep 1021439 = 1532159) B1532159
theorem B5183027 : Blo 1020604 5183027 := bstep (se 1 (by rfl) ⟨3887270, by rfl⟩ : syracuseStep 5183027 = 7774541) B7774541
theorem B1021983 : Blo 1020604 1021983 := bstep (se 1 (by rfl) ⟨766487, by rfl⟩ : syracuseStep 1021983 = 1532975) B1532975
theorem B1022063 : Blo 1020604 1022063 := bstep (se 1 (by rfl) ⟨766547, by rfl⟩ : syracuseStep 1022063 = 1533095) B1533095
theorem B1022311 : Blo 1020604 1022311 := bstep (se 1 (by rfl) ⟨766733, by rfl⟩ : syracuseStep 1022311 = 1533467) B1533467
theorem B2300507 : Blo 1020604 2300507 := bstep (se 1 (by rfl) ⟨1725380, by rfl⟩ : syracuseStep 2300507 = 3450761) B3450761
theorem B1022567 : Blo 1020604 1022567 := bstep (se 1 (by rfl) ⟨766925, by rfl⟩ : syracuseStep 1022567 = 1533851) B1533851
theorem B1022591 : Blo 1020604 1022591 := bstep (se 1 (by rfl) ⟨766943, by rfl⟩ : syracuseStep 1022591 = 1533887) B1533887
theorem B1940203 : Blo 1020604 1940203 := bstep (se 1 (by rfl) ⟨1455152, by rfl⟩ : syracuseStep 1940203 = 2910305) B2910305
theorem B1022715 : Blo 1020604 1022715 := bstep (se 1 (by rfl) ⟨767036, by rfl⟩ : syracuseStep 1022715 = 1534073) B1534073
theorem B1022971 : Blo 1020604 1022971 := bstep (se 1 (by rfl) ⟨767228, by rfl⟩ : syracuseStep 1022971 = 1534457) B1534457
theorem B1023007 : Blo 1020604 1023007 := bstep (se 1 (by rfl) ⟨767255, by rfl⟩ : syracuseStep 1023007 = 1534511) B1534511
theorem B5184647 : Blo 1020604 5184647 := bstep (se 1 (by rfl) ⟨3888485, by rfl⟩ : syracuseStep 5184647 = 7776971) B7776971
theorem B1023295 : Blo 1020604 1023295 := bstep (se 1 (by rfl) ⟨767471, by rfl⟩ : syracuseStep 1023295 = 1534943) B1534943
theorem B1023591 : Blo 1020604 1023591 := bstep (se 1 (by rfl) ⟨767693, by rfl⟩ : syracuseStep 1023591 = 1535387) B1535387
theorem B11640671 : Blo 1020604 11640671 := bstep (se 1 (by rfl) ⟨8730503, by rfl⟩ : syracuseStep 11640671 = 17461007) B17461007
theorem B1023871 : Blo 1020604 1023871 := bstep (se 1 (by rfl) ⟨767903, by rfl⟩ : syracuseStep 1023871 = 1535807) B1535807
theorem B6561719 : Blo 1020604 6561719 := bstep (se 1 (by rfl) ⟨4921289, by rfl⟩ : syracuseStep 6561719 = 9842579) B9842579
theorem B1941479 : Blo 1020604 1941479 := bstep (se 1 (by rfl) ⟨1456109, by rfl⟩ : syracuseStep 1941479 = 2912219) B2912219
theorem B1023995 : Blo 1020604 1023995 := bstep (se 1 (by rfl) ⟨767996, by rfl⟩ : syracuseStep 1023995 = 1535993) B1535993
theorem B1024155 : Blo 1020604 1024155 := bstep (se 1 (by rfl) ⟨768116, by rfl⟩ : syracuseStep 1024155 = 1536233) B1536233
theorem B1024239 : Blo 1020604 1024239 := bstep (se 1 (by rfl) ⟨768179, by rfl⟩ : syracuseStep 1024239 = 1536359) B1536359
theorem B2302505 : Blo 1020604 2302505 := bstep (se 2 (by rfl) ⟨863439, by rfl⟩ : syracuseStep 2302505 = 1726879) B1726879
theorem B17474129 : Blo 1020604 17474129 := bstep (se 2 (by rfl) ⟨6552798, by rfl⟩ : syracuseStep 17474129 = 13105597) B13105597
theorem B1024603 : Blo 1020604 1024603 := bstep (se 1 (by rfl) ⟨768452, by rfl⟩ : syracuseStep 1024603 = 1536905) B1536905
theorem B5186267 : Blo 1020604 5186267 := bstep (se 1 (by rfl) ⟨3889700, by rfl⟩ : syracuseStep 5186267 = 7779401) B7779401
theorem B2302811 : Blo 1020604 2302811 := bstep (se 1 (by rfl) ⟨1727108, by rfl⟩ : syracuseStep 2302811 = 3454217) B3454217
theorem B2303135 : Blo 1020604 2303135 := bstep (se 1 (by rfl) ⟨1727351, by rfl⟩ : syracuseStep 2303135 = 3454703) B3454703
theorem B2762041 : Blo 1020604 2762041 := bstep (se 2 (by rfl) ⟨1035765, by rfl⟩ : syracuseStep 2762041 = 2071531) B2071531
theorem B3679607 : Blo 1020604 3679607 := bstep (se 1 (by rfl) ⟨2759705, by rfl⟩ : syracuseStep 3679607 = 5519411) B5519411
theorem B2303783 : Blo 1020604 2303783 := bstep (se 1 (by rfl) ⟨1727837, by rfl⟩ : syracuseStep 2303783 = 3455675) B3455675
theorem B3450815 : Blo 1020604 3450815 := bstep (se 1 (by rfl) ⟨2588111, by rfl⟩ : syracuseStep 3450815 = 5176223) B5176223
theorem B2304161 : Blo 1020604 2304161 := bstep (se 2 (by rfl) ⟨864060, by rfl⟩ : syracuseStep 2304161 = 1728121) B1728121
theorem B6564179 : Blo 1020604 6564179 := bstep (se 1 (by rfl) ⟨4923134, by rfl⟩ : syracuseStep 6564179 = 9846269) B9846269
theorem B3877247 : Blo 1020604 3877247 := bstep (se 1 (by rfl) ⟨2907935, by rfl⟩ : syracuseStep 3877247 = 5815871) B5815871
theorem B7383433 : Blo 1020604 7383433 := bstep (se 2 (by rfl) ⟨2768787, by rfl⟩ : syracuseStep 7383433 = 5537575) B5537575
theorem B70921079 : Blo 1020604 70921079 := bstep (se 1 (by rfl) ⟨53190809, by rfl⟩ : syracuseStep 70921079 = 106381619) B106381619
theorem B1944479 : Blo 1020604 1944479 := bstep (se 1 (by rfl) ⟨1458359, by rfl⟩ : syracuseStep 1944479 = 2916719) B2916719
theorem B2076779 : Blo 1020604 2076779 := bstep (se 1 (by rfl) ⟨1557584, by rfl⟩ : syracuseStep 2076779 = 3115169) B3115169
theorem B3453191 : Blo 1020604 3453191 := bstep (se 1 (by rfl) ⟨2589893, by rfl⟩ : syracuseStep 3453191 = 5179787) B5179787
theorem B3453569 : Blo 1020604 3453569 := bstep (se 2 (by rfl) ⟨1295088, by rfl⟩ : syracuseStep 3453569 = 2590177) B2590177
theorem B1454879 : Blo 1020604 1454879 := bstep (se 1 (by rfl) ⟨1091159, by rfl⟩ : syracuseStep 1454879 = 2182319) B2182319
theorem B23606569 : Blo 1020604 23606569 := bstep (se 2 (by rfl) ⟨8852463, by rfl⟩ : syracuseStep 23606569 = 17704927) B17704927
theorem B3454271 : Blo 1020604 3454271 := bstep (se 1 (by rfl) ⟨2590703, by rfl⟩ : syracuseStep 3454271 = 5181407) B5181407
theorem B4142447 : Blo 1020604 4142447 := bstep (se 1 (by rfl) ⟨3106835, by rfl⟩ : syracuseStep 4142447 = 6213671) B6213671
theorem B14005993 : Blo 1020604 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B113325875 : Blo 1020604 113325875 := bstep (se 1 (by rfl) ⟨84994406, by rfl⟩ : syracuseStep 113325875 = 169988813) B169988813
theorem B5814139 : Blo 1020604 5814139 := bstep (se 1 (by rfl) ⟨4360604, by rfl⟩ : syracuseStep 5814139 = 8721209) B8721209
theorem B5814665 : Blo 1020604 5814665 := bstep (se 2 (by rfl) ⟨2180499, by rfl⟩ : syracuseStep 5814665 = 4360999) B4360999
theorem B14727653 : Blo 1020604 14727653 := bstep (se 4 (by rfl) ⟨1380717, by rfl⟩ : syracuseStep 14727653 = 2761435) B2761435
theorem B5815097 : Blo 1020604 5815097 := bstep (se 2 (by rfl) ⟨2180661, by rfl⟩ : syracuseStep 5815097 = 4361323) B4361323
theorem B3456161 : Blo 1020604 3456161 := bstep (se 2 (by rfl) ⟨1296060, by rfl⟩ : syracuseStep 3456161 = 2592121) B2592121
theorem B8731871 : Blo 1020604 8731871 := bstep (se 1 (by rfl) ⟨6548903, by rfl⟩ : syracuseStep 8731871 = 13097807) B13097807
theorem B7389161 : Blo 1020604 7389161 := bstep (se 2 (by rfl) ⟨2770935, by rfl⟩ : syracuseStep 7389161 = 5541871) B5541871
theorem B7880923 : Blo 1020604 7880923 := bstep (se 1 (by rfl) ⟨5910692, by rfl⟩ : syracuseStep 7880923 = 11821385) B11821385
theorem B5816555 : Blo 1020604 5816555 := bstep (se 1 (by rfl) ⟨4362416, by rfl⟩ : syracuseStep 5816555 = 8724833) B8724833
theorem B4145527 : Blo 1020604 4145527 := bstep (se 1 (by rfl) ⟨3109145, by rfl⟩ : syracuseStep 4145527 = 6218291) B6218291
theorem B3457619 : Blo 1020604 3457619 := bstep (se 1 (by rfl) ⟨2593214, by rfl⟩ : syracuseStep 3457619 = 5186429) B5186429
theorem B13976263 : Blo 1020604 13976263 := bstep (se 1 (by rfl) ⟨10482197, by rfl⟩ : syracuseStep 13976263 = 20964395) B20964395
theorem B6210557 : Blo 1020604 6210557 := bstep (se 3 (by rfl) ⟨1164479, by rfl⟩ : syracuseStep 6210557 = 2328959) B2328959
theorem B2180371 : Blo 1020604 2180371 := bstep (se 1 (by rfl) ⟨1635278, by rfl⟩ : syracuseStep 2180371 = 3270557) B3270557
theorem B13092839 : Blo 1020604 13092839 := bstep (se 1 (by rfl) ⟨9819629, by rfl⟩ : syracuseStep 13092839 = 19639259) B19639259
theorem B2181431 : Blo 1020604 2181431 := bstep (se 1 (by rfl) ⟨1636073, by rfl⟩ : syracuseStep 2181431 = 3272147) B3272147
theorem B1657435 : Blo 1020604 1657435 := bstep (se 1 (by rfl) ⟨1243076, by rfl⟩ : syracuseStep 1657435 = 2486153) B2486153
theorem B1723099 : Blo 1020604 1723099 := bstep (se 1 (by rfl) ⟨1292324, by rfl⟩ : syracuseStep 1723099 = 2584649) B2584649
theorem B7752671 : Blo 1020604 7752671 := bstep (se 1 (by rfl) ⟨5814503, by rfl⟩ : syracuseStep 7752671 = 11629007) B11629007
theorem B1723855 : Blo 1020604 1723855 := bstep (se 1 (by rfl) ⟨1292891, by rfl⟩ : syracuseStep 1723855 = 2585783) B2585783
theorem B4148705 : Blo 1020604 4148705 := bstep (se 2 (by rfl) ⟨1555764, by rfl⟩ : syracuseStep 4148705 = 3111529) B3111529
theorem B17977243 : Blo 1020604 17977243 := bstep (se 1 (by rfl) ⟨13482932, by rfl⟩ : syracuseStep 17977243 = 26965865) B26965865
theorem B1724537 : Blo 1020604 1724537 := bstep (se 2 (by rfl) ⟨646701, by rfl⟩ : syracuseStep 1724537 = 1293403) B1293403
theorem B1724827 : Blo 1020604 1724827 := bstep (se 1 (by rfl) ⟨1293620, by rfl⟩ : syracuseStep 1724827 = 2587241) B2587241
theorem B5526071 : Blo 1020604 5526071 := bstep (se 1 (by rfl) ⟨4144553, by rfl⟩ : syracuseStep 5526071 = 8289107) B8289107
theorem B53204111 : Blo 1020604 53204111 := bstep (se 1 (by rfl) ⟨39903083, by rfl⟩ : syracuseStep 53204111 = 79806167) B79806167
theorem B20993219 : Blo 1020604 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B3692063 : Blo 1020604 3692063 := bstep (se 1 (by rfl) ⟨2769047, by rfl⟩ : syracuseStep 3692063 = 5538095) B5538095
theorem B5166827 : Blo 1020604 5166827 := bstep (se 1 (by rfl) ⟨3875120, by rfl⟩ : syracuseStep 5166827 = 7750241) B7750241
theorem B1726535 : Blo 1020604 1726535 := bstep (se 1 (by rfl) ⟨1294901, by rfl⟩ : syracuseStep 1726535 = 2589803) B2589803
theorem B29448845 : Blo 1020604 29448845 := bstep (se 3 (by rfl) ⟨5521658, by rfl⟩ : syracuseStep 29448845 = 11043317) B11043317
theorem B4152259 : Blo 1020604 4152259 := bstep (se 1 (by rfl) ⟨3114194, by rfl⟩ : syracuseStep 4152259 = 6228389) B6228389
theorem B1530971 : Blo 1020604 1530971 := bstep (se 1 (by rfl) ⟨1148228, by rfl⟩ : syracuseStep 1530971 = 2296457) B2296457
theorem B1662059 : Blo 1020604 1662059 := bstep (se 1 (by rfl) ⟨1246544, by rfl⟩ : syracuseStep 1662059 = 2493089) B2493089
theorem B25255127 : Blo 1020604 25255127 := bstep (se 1 (by rfl) ⟨18941345, by rfl⟩ : syracuseStep 25255127 = 37882691) B37882691
theorem B1531163 : Blo 1020604 1531163 := bstep (se 1 (by rfl) ⟨1148372, by rfl⟩ : syracuseStep 1531163 = 2296745) B2296745
theorem B11656709 : Blo 1020604 11656709 := bstep (se 4 (by rfl) ⟨1092816, by rfl⟩ : syracuseStep 11656709 = 2185633) B2185633
theorem B4906603 : Blo 1020604 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B7757531 : Blo 1020604 7757531 := bstep (se 1 (by rfl) ⟨5818148, by rfl⟩ : syracuseStep 7757531 = 11636297) B11636297
theorem B1531631 : Blo 1020604 1531631 := bstep (se 1 (by rfl) ⟨1148723, by rfl⟩ : syracuseStep 1531631 = 2297447) B2297447
theorem B1531817 : Blo 1020604 1531817 := bstep (se 2 (by rfl) ⟨574431, by rfl⟩ : syracuseStep 1531817 = 1148863) B1148863
theorem B1728553 : Blo 1020604 1728553 := bstep (se 2 (by rfl) ⟨648207, by rfl⟩ : syracuseStep 1728553 = 1296415) B1296415
theorem B1531967 : Blo 1020604 1531967 := bstep (se 1 (by rfl) ⟨1148975, by rfl⟩ : syracuseStep 1531967 = 2297951) B2297951
theorem B7004227 : Blo 1020604 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B7758017 : Blo 1020604 7758017 := bstep (se 2 (by rfl) ⟨2909256, by rfl⟩ : syracuseStep 7758017 = 5818513) B5818513
theorem B1532201 : Blo 1020604 1532201 := bstep (se 2 (by rfl) ⟨574575, by rfl⟩ : syracuseStep 1532201 = 1149151) B1149151
theorem B5169581 : Blo 1020604 5169581 := bstep (se 3 (by rfl) ⟨969296, by rfl⟩ : syracuseStep 5169581 = 1938593) B1938593
theorem B5530139 : Blo 1020604 5530139 := bstep (se 1 (by rfl) ⟨4147604, by rfl⟩ : syracuseStep 5530139 = 8295209) B8295209
theorem B1532471 : Blo 1020604 1532471 := bstep (se 1 (by rfl) ⟨1149353, by rfl⟩ : syracuseStep 1532471 = 2298707) B2298707
theorem B7758503 : Blo 1020604 7758503 := bstep (se 1 (by rfl) ⟨5818877, by rfl⟩ : syracuseStep 7758503 = 11637755) B11637755
theorem B5825303 : Blo 1020604 5825303 := bstep (se 1 (by rfl) ⟨4368977, by rfl⟩ : syracuseStep 5825303 = 8737955) B8737955
theorem B1532831 : Blo 1020604 1532831 := bstep (se 1 (by rfl) ⟨1149623, by rfl⟩ : syracuseStep 1532831 = 2299247) B2299247
theorem B11035705 : Blo 1020604 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B1533119 : Blo 1020604 1533119 := bstep (se 1 (by rfl) ⟨1149839, by rfl⟩ : syracuseStep 1533119 = 2299679) B2299679
theorem B1533263 : Blo 1020604 1533263 := bstep (se 1 (by rfl) ⟨1149947, by rfl⟩ : syracuseStep 1533263 = 2299895) B2299895
theorem B1533353 : Blo 1020604 1533353 := bstep (se 2 (by rfl) ⟨575007, by rfl⟩ : syracuseStep 1533353 = 1150015) B1150015
theorem B3499433 : Blo 1020604 3499433 := bstep (se 2 (by rfl) ⟨1312287, by rfl⟩ : syracuseStep 3499433 = 2624575) B2624575
theorem B3270071 : Blo 1020604 3270071 := bstep (se 1 (by rfl) ⟨2452553, by rfl⟩ : syracuseStep 3270071 = 4905107) B4905107
theorem B1533503 : Blo 1020604 1533503 := bstep (se 1 (by rfl) ⟨1150127, by rfl⟩ : syracuseStep 1533503 = 2300255) B2300255
theorem B1533863 : Blo 1020604 1533863 := bstep (se 1 (by rfl) ⟨1150397, by rfl⟩ : syracuseStep 1533863 = 2300795) B2300795
theorem B5171201 : Blo 1020604 5171201 := bstep (se 2 (by rfl) ⟨1939200, by rfl⟩ : syracuseStep 5171201 = 3878401) B3878401
theorem B1533983 : Blo 1020604 1533983 := bstep (se 1 (by rfl) ⟨1150487, by rfl⟩ : syracuseStep 1533983 = 2300975) B2300975
theorem B3270955 : Blo 1020604 3270955 := bstep (se 1 (by rfl) ⟨2453216, by rfl⟩ : syracuseStep 3270955 = 4906433) B4906433
theorem B1534439 : Blo 1020604 1534439 := bstep (se 1 (by rfl) ⟨1150829, by rfl⟩ : syracuseStep 1534439 = 2301659) B2301659
theorem B1534619 : Blo 1020604 1534619 := bstep (se 1 (by rfl) ⟨1150964, by rfl⟩ : syracuseStep 1534619 = 2301929) B2301929
theorem B3107591 : Blo 1020604 3107591 := bstep (se 1 (by rfl) ⟨2330693, by rfl⟩ : syracuseStep 3107591 = 4661387) B4661387
theorem B2452265 : Blo 1020604 2452265 := bstep (se 2 (by rfl) ⟨919599, by rfl⟩ : syracuseStep 2452265 = 1839199) B1839199
theorem B1534841 : Blo 1020604 1534841 := bstep (se 2 (by rfl) ⟨575565, by rfl⟩ : syracuseStep 1534841 = 1151131) B1151131
theorem B7760933 : Blo 1020604 7760933 := bstep (se 4 (by rfl) ⟨727587, by rfl⟩ : syracuseStep 7760933 = 1455175) B1455175
theorem B1535087 : Blo 1020604 1535087 := bstep (se 1 (by rfl) ⟨1151315, by rfl⟩ : syracuseStep 1535087 = 2302631) B2302631
theorem B1535183 : Blo 1020604 1535183 := bstep (se 1 (by rfl) ⟨1151387, by rfl⟩ : syracuseStep 1535183 = 2302775) B2302775
theorem B1535303 : Blo 1020604 1535303 := bstep (se 1 (by rfl) ⟨1151477, by rfl⟩ : syracuseStep 1535303 = 2302955) B2302955
theorem B33648157 : Blo 1020604 33648157 := bstep (se 3 (by rfl) ⟨6309029, by rfl⟩ : syracuseStep 33648157 = 12618059) B12618059
theorem B1535591 : Blo 1020604 1535591 := bstep (se 1 (by rfl) ⟨1151693, by rfl⟩ : syracuseStep 1535591 = 2303387) B2303387
theorem B2584345 : Blo 1020604 2584345 := bstep (se 2 (by rfl) ⟨969129, by rfl⟩ : syracuseStep 2584345 = 1938259) B1938259
theorem B1535975 : Blo 1020604 1535975 := bstep (se 1 (by rfl) ⟨1151981, by rfl⟩ : syracuseStep 1535975 = 2303963) B2303963
theorem B2912287 : Blo 1020604 2912287 := bstep (se 1 (by rfl) ⟨2184215, by rfl⟩ : syracuseStep 2912287 = 4368431) B4368431
theorem B1536095 : Blo 1020604 1536095 := bstep (se 1 (by rfl) ⟨1152071, by rfl⟩ : syracuseStep 1536095 = 2304143) B2304143
theorem B1536155 : Blo 1020604 1536155 := bstep (se 1 (by rfl) ⟨1152116, by rfl⟩ : syracuseStep 1536155 = 2304233) B2304233
theorem B1536335 : Blo 1020604 1536335 := bstep (se 1 (by rfl) ⟨1152251, by rfl⟩ : syracuseStep 1536335 = 2304503) B2304503
theorem B6549929 : Blo 1020604 6549929 := bstep (se 2 (by rfl) ⟨2456223, by rfl⟩ : syracuseStep 6549929 = 4912447) B4912447
theorem B1536425 : Blo 1020604 1536425 := bstep (se 2 (by rfl) ⟨576159, by rfl⟩ : syracuseStep 1536425 = 1152319) B1152319
theorem B1536731 : Blo 1020604 1536731 := bstep (se 1 (by rfl) ⟨1152548, by rfl⟩ : syracuseStep 1536731 = 2305097) B2305097
theorem B4912123 : Blo 1020604 4912123 := bstep (se 1 (by rfl) ⟨3684092, by rfl⟩ : syracuseStep 4912123 = 7368185) B7368185
theorem B2585641 : Blo 1020604 2585641 := bstep (se 2 (by rfl) ⟨969615, by rfl⟩ : syracuseStep 2585641 = 1939231) B1939231
theorem B8746055 : Blo 1020604 8746055 := bstep (se 1 (by rfl) ⟨6559541, by rfl⟩ : syracuseStep 8746055 = 13119083) B13119083
theorem B2913403 : Blo 1020604 2913403 := bstep (se 1 (by rfl) ⟨2185052, by rfl⟩ : syracuseStep 2913403 = 4370105) B4370105
theorem B12154049 : Blo 1020604 12154049 := bstep (se 2 (by rfl) ⟨4557768, by rfl⟩ : syracuseStep 12154049 = 9115537) B9115537
theorem B5174927 : Blo 1020604 5174927 := bstep (se 1 (by rfl) ⟨3881195, by rfl⟩ : syracuseStep 5174927 = 7762391) B7762391
theorem B2586593 : Blo 1020604 2586593 := bstep (se 2 (by rfl) ⟨969972, by rfl⟩ : syracuseStep 2586593 = 1939945) B1939945
theorem B2587079 : Blo 1020604 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B8288851 : Blo 1020604 8288851 := bstep (se 1 (by rfl) ⟨6216638, by rfl⟩ : syracuseStep 8288851 = 12433277) B12433277
theorem B5175899 : Blo 1020604 5175899 := bstep (se 1 (by rfl) ⟨3881924, by rfl⟩ : syracuseStep 5175899 = 7763849) B7763849
theorem B6552161 : Blo 1020604 6552161 := bstep (se 2 (by rfl) ⟨2457060, by rfl⟩ : syracuseStep 6552161 = 4914121) B4914121
theorem B2914987 : Blo 1020604 2914987 := bstep (se 1 (by rfl) ⟨2186240, by rfl⟩ : syracuseStep 2914987 = 4372481) B4372481
theorem B2915261 : Blo 1020604 2915261 := bstep (se 3 (by rfl) ⟨546611, by rfl⟩ : syracuseStep 2915261 = 1093223) B1093223
theorem B11631923 : Blo 1020604 11631923 := bstep (se 1 (by rfl) ⟨8723942, by rfl⟩ : syracuseStep 11631923 = 17447885) B17447885
theorem B12615041 : Blo 1020604 12615041 := bstep (se 2 (by rfl) ⟨4730640, by rfl⟩ : syracuseStep 12615041 = 9461281) B9461281
theorem B1637867 : Blo 1020604 1637867 := bstep (se 1 (by rfl) ⟨1228400, by rfl⟩ : syracuseStep 1637867 = 2456801) B2456801
theorem B2588537 : Blo 1020604 2588537 := bstep (se 2 (by rfl) ⟨970701, by rfl⟩ : syracuseStep 2588537 = 1941403) B1941403
theorem B9338969 : Blo 1020604 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B5538077 : Blo 1020604 5538077 := bstep (se 3 (by rfl) ⟨1038389, by rfl⟩ : syracuseStep 5538077 = 2076779) B2076779
theorem B5177843 : Blo 1020604 5177843 := bstep (se 1 (by rfl) ⟨3883382, by rfl⟩ : syracuseStep 5177843 = 7766765) B7766765
theorem B5178167 : Blo 1020604 5178167 := bstep (se 1 (by rfl) ⟨3883625, by rfl⟩ : syracuseStep 5178167 = 7767251) B7767251
theorem B8389979 : Blo 1020604 8389979 := bstep (se 1 (by rfl) ⟨6292484, by rfl⟩ : syracuseStep 8389979 = 12584969) B12584969
theorem B14714273 : Blo 1020604 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B5244695 : Blo 1020604 5244695 := bstep (se 1 (by rfl) ⟨3933521, by rfl⟩ : syracuseStep 5244695 = 7867043) B7867043
theorem B1149691 : Blo 1020604 1149691 := bstep (se 1 (by rfl) ⟨862268, by rfl⟩ : syracuseStep 1149691 = 1724537) B1724537
theorem B4361273 : Blo 1020604 4361273 := bstep (se 2 (by rfl) ⟨1635477, by rfl⟩ : syracuseStep 4361273 = 3270955) B3270955
theorem B8719811 : Blo 1020604 8719811 := bstep (se 1 (by rfl) ⟨6539858, by rfl⟩ : syracuseStep 8719811 = 13079717) B13079717
theorem B13995479 : Blo 1020604 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B2297465 : Blo 1020604 2297465 := bstep (se 2 (by rfl) ⟨861549, by rfl⟩ : syracuseStep 2297465 = 1723099) B1723099
theorem B2461375 : Blo 1020604 2461375 := bstep (se 1 (by rfl) ⟨1846031, by rfl⟩ : syracuseStep 2461375 = 3692063) B3692063
theorem B3444551 : Blo 1020604 3444551 := bstep (se 1 (by rfl) ⟨2583413, by rfl⟩ : syracuseStep 3444551 = 5166827) B5166827
theorem B1151023 : Blo 1020604 1151023 := bstep (se 1 (by rfl) ⟨863267, by rfl⟩ : syracuseStep 1151023 = 1726535) B1726535
theorem B1970401 : Blo 1020604 1970401 := bstep (se 2 (by rfl) ⟨738900, by rfl⟩ : syracuseStep 1970401 = 1477801) B1477801
theorem B19632563 : Blo 1020604 19632563 := bstep (se 1 (by rfl) ⟨14724422, by rfl⟩ : syracuseStep 19632563 = 29448845) B29448845
theorem B2298473 : Blo 1020604 2298473 := bstep (se 2 (by rfl) ⟨861927, by rfl⟩ : syracuseStep 2298473 = 1723855) B1723855
theorem B44864209 : Blo 1020604 44864209 := bstep (se 2 (by rfl) ⟨16824078, by rfl⟩ : syracuseStep 44864209 = 33648157) B33648157
theorem B1020647 : Blo 1020604 1020647 := bstep (se 1 (by rfl) ⟨765485, by rfl⟩ : syracuseStep 1020647 = 1530971) B1530971
theorem B1020775 : Blo 1020604 1020775 := bstep (se 1 (by rfl) ⟨765581, by rfl⟩ : syracuseStep 1020775 = 1531163) B1531163
theorem B7771139 : Blo 1020604 7771139 := bstep (se 1 (by rfl) ⟨5828354, by rfl⟩ : syracuseStep 7771139 = 11656709) B11656709
theorem B3445793 : Blo 1020604 3445793 := bstep (se 2 (by rfl) ⟨1292172, by rfl⟩ : syracuseStep 3445793 = 2584345) B2584345
theorem B1021087 : Blo 1020604 1021087 := bstep (se 1 (by rfl) ⟨765815, by rfl⟩ : syracuseStep 1021087 = 1531631) B1531631
theorem B1021211 : Blo 1020604 1021211 := bstep (se 1 (by rfl) ⟨765908, by rfl⟩ : syracuseStep 1021211 = 1531817) B1531817
theorem B1021311 : Blo 1020604 1021311 := bstep (se 1 (by rfl) ⟨765983, by rfl⟩ : syracuseStep 1021311 = 1531967) B1531967
theorem B1021467 : Blo 1020604 1021467 := bstep (se 1 (by rfl) ⟨766100, by rfl⟩ : syracuseStep 1021467 = 1532201) B1532201
theorem B3446387 : Blo 1020604 3446387 := bstep (se 1 (by rfl) ⟨2584790, by rfl⟩ : syracuseStep 3446387 = 5169581) B5169581
theorem B1021647 : Blo 1020604 1021647 := bstep (se 1 (by rfl) ⟨766235, by rfl⟩ : syracuseStep 1021647 = 1532471) B1532471
theorem B2299769 : Blo 1020604 2299769 := bstep (se 2 (by rfl) ⟨862413, by rfl⟩ : syracuseStep 2299769 = 1724827) B1724827
theorem B1021887 : Blo 1020604 1021887 := bstep (se 1 (by rfl) ⟨766415, by rfl⟩ : syracuseStep 1021887 = 1532831) B1532831
theorem B1022079 : Blo 1020604 1022079 := bstep (se 1 (by rfl) ⟨766559, by rfl⟩ : syracuseStep 1022079 = 1533119) B1533119
theorem B1022175 : Blo 1020604 1022175 := bstep (se 1 (by rfl) ⟨766631, by rfl⟩ : syracuseStep 1022175 = 1533263) B1533263
theorem B1022235 : Blo 1020604 1022235 := bstep (se 1 (by rfl) ⟨766676, by rfl⟩ : syracuseStep 1022235 = 1533353) B1533353
theorem B2332955 : Blo 1020604 2332955 := bstep (se 1 (by rfl) ⟨1749716, by rfl⟩ : syracuseStep 2332955 = 3499433) B3499433
theorem B1022335 : Blo 1020604 1022335 := bstep (se 1 (by rfl) ⟨766751, by rfl⟩ : syracuseStep 1022335 = 1533503) B1533503
theorem B1022575 : Blo 1020604 1022575 := bstep (se 1 (by rfl) ⟨766931, by rfl⟩ : syracuseStep 1022575 = 1533863) B1533863
theorem B2300543 : Blo 1020604 2300543 := bstep (se 1 (by rfl) ⟨1725407, by rfl⟩ : syracuseStep 2300543 = 3450815) B3450815
theorem B3447467 : Blo 1020604 3447467 := bstep (se 1 (by rfl) ⟨2585600, by rfl⟩ : syracuseStep 3447467 = 5171201) B5171201
theorem B1022655 : Blo 1020604 1022655 := bstep (se 1 (by rfl) ⟨766991, by rfl⟩ : syracuseStep 1022655 = 1533983) B1533983
theorem B3447521 : Blo 1020604 3447521 := bstep (se 2 (by rfl) ⟨1292820, by rfl⟩ : syracuseStep 3447521 = 2585641) B2585641
theorem B1022959 : Blo 1020604 1022959 := bstep (se 1 (by rfl) ⟨767219, by rfl⟩ : syracuseStep 1022959 = 1534439) B1534439
theorem B1023079 : Blo 1020604 1023079 := bstep (se 1 (by rfl) ⟨767309, by rfl⟩ : syracuseStep 1023079 = 1534619) B1534619
theorem B2071727 : Blo 1020604 2071727 := bstep (se 1 (by rfl) ⟨1553795, by rfl⟩ : syracuseStep 2071727 = 3107591) B3107591
theorem B1023227 : Blo 1020604 1023227 := bstep (se 1 (by rfl) ⟨767420, by rfl⟩ : syracuseStep 1023227 = 1534841) B1534841
theorem B1023391 : Blo 1020604 1023391 := bstep (se 1 (by rfl) ⟨767543, by rfl⟩ : syracuseStep 1023391 = 1535087) B1535087
theorem B1023455 : Blo 1020604 1023455 := bstep (se 1 (by rfl) ⟨767591, by rfl⟩ : syracuseStep 1023455 = 1535183) B1535183
theorem B1023535 : Blo 1020604 1023535 := bstep (se 1 (by rfl) ⟨767651, by rfl⟩ : syracuseStep 1023535 = 1535303) B1535303
theorem B1023727 : Blo 1020604 1023727 := bstep (se 1 (by rfl) ⟨767795, by rfl⟩ : syracuseStep 1023727 = 1535591) B1535591
theorem B1023983 : Blo 1020604 1023983 := bstep (se 1 (by rfl) ⟨767987, by rfl⟩ : syracuseStep 1023983 = 1535975) B1535975
theorem B1024063 : Blo 1020604 1024063 := bstep (se 1 (by rfl) ⟨768047, by rfl⟩ : syracuseStep 1024063 = 1536095) B1536095
theorem B1024103 : Blo 1020604 1024103 := bstep (se 1 (by rfl) ⟨768077, by rfl⟩ : syracuseStep 1024103 = 1536155) B1536155
theorem B2302127 : Blo 1020604 2302127 := bstep (se 1 (by rfl) ⟨1726595, by rfl⟩ : syracuseStep 2302127 = 3453191) B3453191
theorem B1024223 : Blo 1020604 1024223 := bstep (se 1 (by rfl) ⟨768167, by rfl⟩ : syracuseStep 1024223 = 1536335) B1536335
theorem B4366619 : Blo 1020604 4366619 := bstep (se 1 (by rfl) ⟨3274964, by rfl⟩ : syracuseStep 4366619 = 6549929) B6549929
theorem B4432157 : Blo 1020604 4432157 := bstep (se 3 (by rfl) ⟨831029, by rfl⟩ : syracuseStep 4432157 = 1662059) B1662059
theorem B1024283 : Blo 1020604 1024283 := bstep (se 1 (by rfl) ⟨768212, by rfl⟩ : syracuseStep 1024283 = 1536425) B1536425
theorem B2302379 : Blo 1020604 2302379 := bstep (se 1 (by rfl) ⟨1726784, by rfl⟩ : syracuseStep 2302379 = 3453569) B3453569
theorem B1024487 : Blo 1020604 1024487 := bstep (se 1 (by rfl) ⟨768365, by rfl⟩ : syracuseStep 1024487 = 1536731) B1536731
theorem B11051801 : Blo 1020604 11051801 := bstep (se 2 (by rfl) ⟨4144425, by rfl⟩ : syracuseStep 11051801 = 8288851) B8288851
theorem B8102699 : Blo 1020604 8102699 := bstep (se 1 (by rfl) ⟨6077024, by rfl⟩ : syracuseStep 8102699 = 12154049) B12154049
theorem B2302847 : Blo 1020604 2302847 := bstep (se 1 (by rfl) ⟨1727135, by rfl⟩ : syracuseStep 2302847 = 3454271) B3454271
theorem B2761631 : Blo 1020604 2761631 := bstep (se 1 (by rfl) ⟨2071223, by rfl⟩ : syracuseStep 2761631 = 4142447) B4142447
theorem B3449951 : Blo 1020604 3449951 := bstep (se 1 (by rfl) ⟨2587463, by rfl⟩ : syracuseStep 3449951 = 5174927) B5174927
theorem B4367645 : Blo 1020604 4367645 := bstep (se 3 (by rfl) ⟨818933, by rfl⟩ : syracuseStep 4367645 = 1637867) B1637867
theorem B3876443 : Blo 1020604 3876443 := bstep (se 1 (by rfl) ⟨2907332, by rfl⟩ : syracuseStep 3876443 = 5814665) B5814665
theorem B3450599 : Blo 1020604 3450599 := bstep (se 1 (by rfl) ⟨2587949, by rfl⟩ : syracuseStep 3450599 = 5175899) B5175899
theorem B4368107 : Blo 1020604 4368107 := bstep (se 1 (by rfl) ⟨3276080, by rfl⟩ : syracuseStep 4368107 = 6552161) B6552161
theorem B3876731 : Blo 1020604 3876731 := bstep (se 1 (by rfl) ⟨2907548, by rfl⟩ : syracuseStep 3876731 = 5815097) B5815097
theorem B1943507 : Blo 1020604 1943507 := bstep (se 1 (by rfl) ⟨1457630, by rfl⟩ : syracuseStep 1943507 = 2915261) B2915261
theorem B2304107 : Blo 1020604 2304107 := bstep (se 1 (by rfl) ⟨1728080, by rfl⟩ : syracuseStep 2304107 = 3456161) B3456161
theorem B4926107 : Blo 1020604 4926107 := bstep (se 1 (by rfl) ⟨3694580, by rfl⟩ : syracuseStep 4926107 = 7389161) B7389161
theorem B2304737 : Blo 1020604 2304737 := bstep (se 2 (by rfl) ⟨864276, by rfl⟩ : syracuseStep 2304737 = 1728553) B1728553
theorem B1944319 : Blo 1020604 1944319 := bstep (se 1 (by rfl) ⟨1458239, by rfl⟩ : syracuseStep 1944319 = 2916479) B2916479
theorem B3877703 : Blo 1020604 3877703 := bstep (se 1 (by rfl) ⟨2908277, by rfl⟩ : syracuseStep 3877703 = 5816555) B5816555
theorem B1092475 : Blo 1020604 1092475 := bstep (se 1 (by rfl) ⟨819356, by rfl⟩ : syracuseStep 1092475 = 1638713) B1638713
theorem B3451787 : Blo 1020604 3451787 := bstep (se 1 (by rfl) ⟨2588840, by rfl⟩ : syracuseStep 3451787 = 5177681) B5177681
theorem B2305079 : Blo 1020604 2305079 := bstep (se 1 (by rfl) ⟨1728809, by rfl⟩ : syracuseStep 2305079 = 3457619) B3457619
theorem B4140371 : Blo 1020604 4140371 := bstep (se 1 (by rfl) ⟨3105278, by rfl⟩ : syracuseStep 4140371 = 6210557) B6210557
theorem B4369747 : Blo 1020604 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B9809363 : Blo 1020604 9809363 := bstep (se 1 (by rfl) ⟨7357022, by rfl⟩ : syracuseStep 9809363 = 14714045) B14714045
theorem B1945063 : Blo 1020604 1945063 := bstep (se 1 (by rfl) ⟨1458797, by rfl⟩ : syracuseStep 1945063 = 2917595) B2917595
theorem B8728559 : Blo 1020604 8728559 := bstep (se 1 (by rfl) ⟨6546419, by rfl⟩ : syracuseStep 8728559 = 13092839) B13092839
theorem B3452975 : Blo 1020604 3452975 := bstep (se 1 (by rfl) ⟨2589731, by rfl⟩ : syracuseStep 3452975 = 5179463) B5179463
theorem B4042855 : Blo 1020604 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B1454287 : Blo 1020604 1454287 := bstep (se 1 (by rfl) ⟨1090715, by rfl⟩ : syracuseStep 1454287 = 2181431) B2181431
theorem B3682721 : Blo 1020604 3682721 := bstep (se 2 (by rfl) ⟨1381020, by rfl⟩ : syracuseStep 3682721 = 2762041) B2762041
theorem B3879677 : Blo 1020604 3879677 := bstep (se 3 (by rfl) ⟨727439, by rfl⟩ : syracuseStep 3879677 = 1454879) B1454879
theorem B3454379 : Blo 1020604 3454379 := bstep (se 1 (by rfl) ⟨2590784, by rfl⟩ : syracuseStep 3454379 = 5181569) B5181569
theorem B3323387 : Blo 1020604 3323387 := bstep (se 1 (by rfl) ⟨2492540, by rfl⟩ : syracuseStep 3323387 = 4985081) B4985081
theorem B3684047 : Blo 1020604 3684047 := bstep (se 1 (by rfl) ⟨2763035, by rfl⟩ : syracuseStep 3684047 = 5526071) B5526071
theorem B9844577 : Blo 1020604 9844577 := bstep (se 2 (by rfl) ⟨3691716, by rfl⟩ : syracuseStep 9844577 = 7383433) B7383433
theorem B35469407 : Blo 1020604 35469407 := bstep (se 1 (by rfl) ⟨26602055, by rfl⟩ : syracuseStep 35469407 = 53204111) B53204111
theorem B2209913 : Blo 1020604 2209913 := bstep (se 2 (by rfl) ⟨828717, by rfl⟩ : syracuseStep 2209913 = 1657435) B1657435
theorem B4372633 : Blo 1020604 4372633 := bstep (se 2 (by rfl) ⟨1639737, by rfl⟩ : syracuseStep 4372633 = 3279475) B3279475
theorem B9812285 : Blo 1020604 9812285 := bstep (se 3 (by rfl) ⟨1839803, by rfl⟩ : syracuseStep 9812285 = 3679607) B3679607
theorem B3455351 : Blo 1020604 3455351 := bstep (se 1 (by rfl) ⟨2591513, by rfl⟩ : syracuseStep 3455351 = 5183027) B5183027
theorem B3456431 : Blo 1020604 3456431 := bstep (se 1 (by rfl) ⟨2592323, by rfl⟩ : syracuseStep 3456431 = 5184647) B5184647
theorem B23969657 : Blo 1020604 23969657 := bstep (se 2 (by rfl) ⟨8988621, by rfl⟩ : syracuseStep 23969657 = 17977243) B17977243
theorem B4374479 : Blo 1020604 4374479 := bstep (se 1 (by rfl) ⟨3280859, by rfl⟩ : syracuseStep 4374479 = 6561719) B6561719
theorem B1294319 : Blo 1020604 1294319 := bstep (se 1 (by rfl) ⟨970739, by rfl⟩ : syracuseStep 1294319 = 1941479) B1941479
theorem B3883049 : Blo 1020604 3883049 := bstep (se 2 (by rfl) ⟨1456143, by rfl⟩ : syracuseStep 3883049 = 2912287) B2912287
theorem B3686759 : Blo 1020604 3686759 := bstep (se 1 (by rfl) ⟨2765069, by rfl⟩ : syracuseStep 3686759 = 5530139) B5530139
theorem B11649419 : Blo 1020604 11649419 := bstep (se 1 (by rfl) ⟨8737064, by rfl⟩ : syracuseStep 11649419 = 17474129) B17474129
theorem B3457511 : Blo 1020604 3457511 := bstep (se 1 (by rfl) ⟨2593133, by rfl⟩ : syracuseStep 3457511 = 5186267) B5186267
theorem B3883535 : Blo 1020604 3883535 := bstep (se 1 (by rfl) ⟨2912651, by rfl⟩ : syracuseStep 3883535 = 5825303) B5825303
theorem B2180047 : Blo 1020604 2180047 := bstep (se 1 (by rfl) ⟨1635035, by rfl⟩ : syracuseStep 2180047 = 3270071) B3270071
theorem B17482877 : Blo 1020604 17482877 := bstep (se 3 (by rfl) ⟨3278039, by rfl⟩ : syracuseStep 17482877 = 6556079) B6556079
theorem B3884537 : Blo 1020604 3884537 := bstep (se 2 (by rfl) ⟨1456701, by rfl⟩ : syracuseStep 3884537 = 2913403) B2913403
theorem B4376119 : Blo 1020604 4376119 := bstep (se 1 (by rfl) ⟨3282089, by rfl⟩ : syracuseStep 4376119 = 6564179) B6564179
theorem B31475425 : Blo 1020604 31475425 := bstep (se 2 (by rfl) ⟨11803284, by rfl⟩ : syracuseStep 31475425 = 23606569) B23606569
theorem B1296319 : Blo 1020604 1296319 := bstep (se 1 (by rfl) ⟨972239, by rfl⟩ : syracuseStep 1296319 = 1944479) B1944479
theorem B7752185 : Blo 1020604 7752185 := bstep (se 2 (by rfl) ⟨2907069, by rfl⟩ : syracuseStep 7752185 = 5814139) B5814139
theorem B3886649 : Blo 1020604 3886649 := bstep (se 2 (by rfl) ⟨1457493, by rfl⟩ : syracuseStep 3886649 = 2914987) B2914987
theorem B33640109 : Blo 1020604 33640109 := bstep (se 3 (by rfl) ⟨6307520, by rfl⟩ : syracuseStep 33640109 = 12615041) B12615041
theorem B75550583 : Blo 1020604 75550583 := bstep (se 1 (by rfl) ⟨56662937, by rfl⟩ : syracuseStep 75550583 = 113325875) B113325875
theorem B11063213 : Blo 1020604 11063213 := bstep (se 3 (by rfl) ⟨2074352, by rfl⟩ : syracuseStep 11063213 = 4148705) B4148705
theorem B1724395 : Blo 1020604 1724395 := bstep (se 1 (by rfl) ⟨1293296, by rfl⟩ : syracuseStep 1724395 = 2586593) B2586593
theorem B1724719 : Blo 1020604 1724719 := bstep (se 1 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 1724719 = 2587079) B2587079
theorem B9818435 : Blo 1020604 9818435 := bstep (se 1 (by rfl) ⟨7363826, by rfl⟩ : syracuseStep 9818435 = 14727653) B14727653
theorem B6542137 : Blo 1020604 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B5821247 : Blo 1020604 5821247 := bstep (se 1 (by rfl) ⟨4365935, by rfl⟩ : syracuseStep 5821247 = 8731871) B8731871
theorem B7754615 : Blo 1020604 7754615 := bstep (se 1 (by rfl) ⟨5815961, by rfl⟩ : syracuseStep 7754615 = 11631923) B11631923
theorem B1725691 : Blo 1020604 1725691 := bstep (se 1 (by rfl) ⟨1294268, by rfl⟩ : syracuseStep 1725691 = 2588537) B2588537
theorem B10507897 : Blo 1020604 10507897 := bstep (se 2 (by rfl) ⟨3940461, by rfl⟩ : syracuseStep 10507897 = 7880923) B7880923
theorem B5527369 : Blo 1020604 5527369 := bstep (se 2 (by rfl) ⟨2072763, by rfl⟩ : syracuseStep 5527369 = 4145527) B4145527
theorem B3889367 : Blo 1020604 3889367 := bstep (se 1 (by rfl) ⟨2917025, by rfl⟩ : syracuseStep 3889367 = 5834051) B5834051
theorem B18635017 : Blo 1020604 18635017 := bstep (se 2 (by rfl) ⟨6988131, by rfl⟩ : syracuseStep 18635017 = 13976263) B13976263
theorem B4151999 : Blo 1020604 4151999 := bstep (se 1 (by rfl) ⟨3113999, by rfl⟩ : syracuseStep 4151999 = 6227999) B6227999
theorem B2907161 : Blo 1020604 2907161 := bstep (se 2 (by rfl) ⟨1090185, by rfl⟩ : syracuseStep 2907161 = 2180371) B2180371
theorem B5528839 : Blo 1020604 5528839 := bstep (se 1 (by rfl) ⟨4146629, by rfl⟩ : syracuseStep 5528839 = 8293259) B8293259
theorem B5168447 : Blo 1020604 5168447 := bstep (se 1 (by rfl) ⟨3876335, by rfl⟩ : syracuseStep 5168447 = 7752671) B7752671
theorem B2186651 : Blo 1020604 2186651 := bstep (se 1 (by rfl) ⟨1639988, by rfl⟩ : syracuseStep 2186651 = 3279977) B3279977
theorem B8740619 : Blo 1020604 8740619 := bstep (se 1 (by rfl) ⟨6555464, by rfl⟩ : syracuseStep 8740619 = 13110929) B13110929
theorem B3105499 : Blo 1020604 3105499 := bstep (se 1 (by rfl) ⟨2329124, by rfl⟩ : syracuseStep 3105499 = 4658249) B4658249
theorem B1532699 : Blo 1020604 1532699 := bstep (se 1 (by rfl) ⟨1149524, by rfl⟩ : syracuseStep 1532699 = 2299049) B2299049
theorem B1532969 : Blo 1020604 1532969 := bstep (se 2 (by rfl) ⟨574863, by rfl⟩ : syracuseStep 1532969 = 1149727) B1149727
theorem B1533671 : Blo 1020604 1533671 := bstep (se 1 (by rfl) ⟨1150253, by rfl⟩ : syracuseStep 1533671 = 2300507) B2300507
theorem B16836751 : Blo 1020604 16836751 := bstep (se 1 (by rfl) ⟨12627563, by rfl⟩ : syracuseStep 16836751 = 25255127) B25255127
theorem B5171687 : Blo 1020604 5171687 := bstep (se 1 (by rfl) ⟨3878765, by rfl⟩ : syracuseStep 5171687 = 7757531) B7757531
theorem B7760447 : Blo 1020604 7760447 := bstep (se 1 (by rfl) ⟨5820335, by rfl⟩ : syracuseStep 7760447 = 11640671) B11640671
theorem B5172011 : Blo 1020604 5172011 := bstep (se 1 (by rfl) ⟨3879008, by rfl⟩ : syracuseStep 5172011 = 7758017) B7758017
theorem B1534889 : Blo 1020604 1534889 := bstep (se 2 (by rfl) ⟨575583, by rfl⟩ : syracuseStep 1534889 = 1151167) B1151167
theorem B1535003 : Blo 1020604 1535003 := bstep (se 1 (by rfl) ⟨1151252, by rfl⟩ : syracuseStep 1535003 = 2302505) B2302505
theorem B5172335 : Blo 1020604 5172335 := bstep (se 1 (by rfl) ⟨3879251, by rfl⟩ : syracuseStep 5172335 = 7758503) B7758503
theorem B1535207 : Blo 1020604 1535207 := bstep (se 1 (by rfl) ⟨1151405, by rfl⟩ : syracuseStep 1535207 = 2302811) B2302811
theorem B1535423 : Blo 1020604 1535423 := bstep (se 1 (by rfl) ⟨1151567, by rfl⟩ : syracuseStep 1535423 = 2303135) B2303135
theorem B1535855 : Blo 1020604 1535855 := bstep (se 1 (by rfl) ⟨1151891, by rfl⟩ : syracuseStep 1535855 = 2303783) B2303783
theorem B6549497 : Blo 1020604 6549497 := bstep (se 2 (by rfl) ⟨2456061, by rfl⟩ : syracuseStep 6549497 = 4912123) B4912123
theorem B1536107 : Blo 1020604 1536107 := bstep (se 1 (by rfl) ⟨1152080, by rfl⟩ : syracuseStep 1536107 = 2304161) B2304161
theorem B2584831 : Blo 1020604 2584831 := bstep (se 1 (by rfl) ⟨1938623, by rfl⟩ : syracuseStep 2584831 = 3877247) B3877247
theorem B1634843 : Blo 1020604 1634843 := bstep (se 1 (by rfl) ⟨1226132, by rfl⟩ : syracuseStep 1634843 = 2452265) B2452265
theorem B47280719 : Blo 1020604 47280719 := bstep (se 1 (by rfl) ⟨35460539, by rfl⟩ : syracuseStep 47280719 = 70921079) B70921079
theorem B5173955 : Blo 1020604 5173955 := bstep (se 1 (by rfl) ⟨3880466, by rfl⟩ : syracuseStep 5173955 = 7760933) B7760933
theorem B18674657 : Blo 1020604 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B5830703 : Blo 1020604 5830703 := bstep (se 1 (by rfl) ⟨4373027, by rfl⟩ : syracuseStep 5830703 = 8746055) B8746055
theorem B2586937 : Blo 1020604 2586937 := bstep (se 2 (by rfl) ⟨970101, by rfl⟩ : syracuseStep 2586937 = 1940203) B1940203
theorem B5536345 : Blo 1020604 5536345 := bstep (se 2 (by rfl) ⟨2076129, by rfl⟩ : syracuseStep 5536345 = 4152259) B4152259
theorem B2588699 : Blo 1020604 2588699 := bstep (se 1 (by rfl) ⟨1941524, by rfl⟩ : syracuseStep 2588699 = 3883049) B3883049
theorem B6225979 : Blo 1020604 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B2457839 : Blo 1020604 2457839 := bstep (se 1 (by rfl) ⟨1843379, by rfl⟩ : syracuseStep 2457839 = 3686759) B3686759
theorem B7766279 : Blo 1020604 7766279 := bstep (se 1 (by rfl) ⟨5824709, by rfl⟩ : syracuseStep 7766279 = 11649419) B11649419
theorem B2589023 : Blo 1020604 2589023 := bstep (se 1 (by rfl) ⟨1941767, by rfl⟩ : syracuseStep 2589023 = 3883535) B3883535
theorem B2589691 : Blo 1020604 2589691 := bstep (se 1 (by rfl) ⟨1942268, by rfl⟩ : syracuseStep 2589691 = 3884537) B3884537
theorem B4359581 : Blo 1020604 4359581 := bstep (se 3 (by rfl) ⟨817421, by rfl⟩ : syracuseStep 4359581 = 1634843) B1634843
theorem B5834825 : Blo 1020604 5834825 := bstep (se 2 (by rfl) ⟨2188059, by rfl⟩ : syracuseStep 5834825 = 4376119) B4376119
theorem B2591099 : Blo 1020604 2591099 := bstep (se 1 (by rfl) ⟨1943324, by rfl⟩ : syracuseStep 2591099 = 3886649) B3886649
theorem B2296367 : Blo 1020604 2296367 := bstep (se 1 (by rfl) ⟨1722275, by rfl⟩ : syracuseStep 2296367 = 3444551) B3444551
theorem B50367055 : Blo 1020604 50367055 := bstep (se 1 (by rfl) ⟨37775291, by rfl⟩ : syracuseStep 50367055 = 75550583) B75550583
theorem B7375475 : Blo 1020604 7375475 := bstep (se 1 (by rfl) ⟨5531606, by rfl⟩ : syracuseStep 7375475 = 11063213) B11063213
theorem B22449001 : Blo 1020604 22449001 := bstep (se 2 (by rfl) ⟨8418375, by rfl⟩ : syracuseStep 22449001 = 16836751) B16836751
theorem B5180759 : Blo 1020604 5180759 := bstep (se 1 (by rfl) ⟨3885569, by rfl⟩ : syracuseStep 5180759 = 7771139) B7771139
theorem B2297195 : Blo 1020604 2297195 := bstep (se 1 (by rfl) ⟨1722896, by rfl⟩ : syracuseStep 2297195 = 3445793) B3445793
theorem B2592425 : Blo 1020604 2592425 := bstep (se 2 (by rfl) ⟨972159, by rfl⟩ : syracuseStep 2592425 = 1944319) B1944319
theorem B2297591 : Blo 1020604 2297591 := bstep (se 1 (by rfl) ⟨1723193, by rfl⟩ : syracuseStep 2297591 = 3446387) B3446387
theorem B2592911 : Blo 1020604 2592911 := bstep (se 1 (by rfl) ⟨1944683, by rfl⟩ : syracuseStep 2592911 = 3889367) B3889367
theorem B2298311 : Blo 1020604 2298311 := bstep (se 1 (by rfl) ⟨1723733, by rfl⟩ : syracuseStep 2298311 = 3447467) B3447467
theorem B2298347 : Blo 1020604 2298347 := bstep (se 1 (by rfl) ⟨1723760, by rfl⟩ : syracuseStep 2298347 = 3447521) B3447521
theorem B2593417 : Blo 1020604 2593417 := bstep (se 2 (by rfl) ⟨972531, by rfl⟩ : syracuseStep 2593417 = 1945063) B1945063
theorem B1938107 : Blo 1020604 1938107 := bstep (se 1 (by rfl) ⟨1453580, by rfl⟩ : syracuseStep 1938107 = 2907161) B2907161
theorem B1381151 : Blo 1020604 1381151 := bstep (se 1 (by rfl) ⟨1035863, by rfl⟩ : syracuseStep 1381151 = 2071727) B2071727
theorem B3445631 : Blo 1020604 3445631 := bstep (se 1 (by rfl) ⟨2584223, by rfl⟩ : syracuseStep 3445631 = 5168447) B5168447
theorem B3281833 : Blo 1020604 3281833 := bstep (se 2 (by rfl) ⟨1230687, by rfl⟩ : syracuseStep 3281833 = 2461375) B2461375
theorem B2299193 : Blo 1020604 2299193 := bstep (se 2 (by rfl) ⟨862197, by rfl⟩ : syracuseStep 2299193 = 1724395) B1724395
theorem B2954771 : Blo 1020604 2954771 := bstep (se 1 (by rfl) ⟨2216078, by rfl⟩ : syracuseStep 2954771 = 4432157) B4432157
theorem B1939049 : Blo 1020604 1939049 := bstep (se 2 (by rfl) ⟨727143, by rfl⟩ : syracuseStep 1939049 = 1454287) B1454287
theorem B2627201 : Blo 1020604 2627201 := bstep (se 2 (by rfl) ⟨985200, by rfl⟩ : syracuseStep 2627201 = 1970401) B1970401
theorem B3446441 : Blo 1020604 3446441 := bstep (se 2 (by rfl) ⟨1292415, by rfl⟩ : syracuseStep 3446441 = 2584831) B2584831
theorem B2299625 : Blo 1020604 2299625 := bstep (se 2 (by rfl) ⟨862359, by rfl⟩ : syracuseStep 2299625 = 1724719) B1724719
theorem B1021799 : Blo 1020604 1021799 := bstep (se 1 (by rfl) ⟨766349, by rfl⟩ : syracuseStep 1021799 = 1532699) B1532699
theorem B1841087 : Blo 1020604 1841087 := bstep (se 1 (by rfl) ⟨1380815, by rfl⟩ : syracuseStep 1841087 = 2761631) B2761631
theorem B1021979 : Blo 1020604 1021979 := bstep (se 1 (by rfl) ⟨766484, by rfl⟩ : syracuseStep 1021979 = 1532969) B1532969
theorem B2299967 : Blo 1020604 2299967 := bstep (se 1 (by rfl) ⟨1724975, by rfl⟩ : syracuseStep 2299967 = 3449951) B3449951
theorem B8722849 : Blo 1020604 8722849 := bstep (se 2 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 8722849 = 6542137) B6542137
theorem B2300399 : Blo 1020604 2300399 := bstep (se 1 (by rfl) ⟨1725299, by rfl⟩ : syracuseStep 2300399 = 3450599) B3450599
theorem B1022447 : Blo 1020604 1022447 := bstep (se 1 (by rfl) ⟨766835, by rfl⟩ : syracuseStep 1022447 = 1533671) B1533671
theorem B3447791 : Blo 1020604 3447791 := bstep (se 1 (by rfl) ⟨2585843, by rfl⟩ : syracuseStep 3447791 = 5171687) B5171687
theorem B2300921 : Blo 1020604 2300921 := bstep (se 2 (by rfl) ⟨862845, by rfl⟩ : syracuseStep 2300921 = 1725691) B1725691
theorem B3284071 : Blo 1020604 3284071 := bstep (se 1 (by rfl) ⟨2463053, by rfl⟩ : syracuseStep 3284071 = 4926107) B4926107
theorem B3448007 : Blo 1020604 3448007 := bstep (se 1 (by rfl) ⟨2586005, by rfl⟩ : syracuseStep 3448007 = 5172011) B5172011
theorem B2301191 : Blo 1020604 2301191 := bstep (se 1 (by rfl) ⟨1725893, by rfl⟩ : syracuseStep 2301191 = 3451787) B3451787
theorem B1023259 : Blo 1020604 1023259 := bstep (se 1 (by rfl) ⟨767444, by rfl⟩ : syracuseStep 1023259 = 1534889) B1534889
theorem B1023335 : Blo 1020604 1023335 := bstep (se 1 (by rfl) ⟨767501, by rfl⟩ : syracuseStep 1023335 = 1535003) B1535003
theorem B3448223 : Blo 1020604 3448223 := bstep (se 1 (by rfl) ⟨2586167, by rfl⟩ : syracuseStep 3448223 = 5172335) B5172335
theorem B1023471 : Blo 1020604 1023471 := bstep (se 1 (by rfl) ⟨767603, by rfl⟩ : syracuseStep 1023471 = 1535207) B1535207
theorem B2760247 : Blo 1020604 2760247 := bstep (se 1 (by rfl) ⟨2070185, by rfl⟩ : syracuseStep 2760247 = 4140371) B4140371
theorem B1023615 : Blo 1020604 1023615 := bstep (se 1 (by rfl) ⟨767711, by rfl⟩ : syracuseStep 1023615 = 1535423) B1535423
theorem B1023903 : Blo 1020604 1023903 := bstep (se 1 (by rfl) ⟨767927, by rfl⟩ : syracuseStep 1023903 = 1535855) B1535855
theorem B4366331 : Blo 1020604 4366331 := bstep (se 1 (by rfl) ⟨3274748, by rfl⟩ : syracuseStep 4366331 = 6549497) B6549497
theorem B2301983 : Blo 1020604 2301983 := bstep (se 1 (by rfl) ⟨1726487, by rfl⟩ : syracuseStep 2301983 = 3452975) B3452975
theorem B1024071 : Blo 1020604 1024071 := bstep (se 1 (by rfl) ⟨768053, by rfl⟩ : syracuseStep 1024071 = 1536107) B1536107
theorem B24846689 : Blo 1020604 24846689 := bstep (se 2 (by rfl) ⟨9317508, by rfl⟩ : syracuseStep 24846689 = 18635017) B18635017
theorem B3449249 : Blo 1020604 3449249 := bstep (se 2 (by rfl) ⟨1293468, by rfl⟩ : syracuseStep 3449249 = 2586937) B2586937
theorem B3449303 : Blo 1020604 3449303 := bstep (se 1 (by rfl) ⟨2586977, by rfl⟩ : syracuseStep 3449303 = 5173955) B5173955
theorem B56042117 : Blo 1020604 56042117 := bstep (se 4 (by rfl) ⟨5253948, by rfl⟩ : syracuseStep 56042117 = 10507897) B10507897
theorem B7381793 : Blo 1020604 7381793 := bstep (se 2 (by rfl) ⟨2768172, by rfl⟩ : syracuseStep 7381793 = 5536345) B5536345
theorem B2302919 : Blo 1020604 2302919 := bstep (se 1 (by rfl) ⟨1727189, by rfl⟩ : syracuseStep 2302919 = 3454379) B3454379
theorem B6563051 : Blo 1020604 6563051 := bstep (se 1 (by rfl) ⟨4922288, by rfl⟩ : syracuseStep 6563051 = 9844577) B9844577
theorem B2303567 : Blo 1020604 2303567 := bstep (se 1 (by rfl) ⟨1727675, by rfl⟩ : syracuseStep 2303567 = 3455351) B3455351
theorem B2304287 : Blo 1020604 2304287 := bstep (se 1 (by rfl) ⟨1728215, by rfl⟩ : syracuseStep 2304287 = 3456431) B3456431
theorem B3451517 : Blo 1020604 3451517 := bstep (se 3 (by rfl) ⟨647159, by rfl⟩ : syracuseStep 3451517 = 1294319) B1294319
theorem B2305007 : Blo 1020604 2305007 := bstep (se 1 (by rfl) ⟨1728755, by rfl⟩ : syracuseStep 2305007 = 3457511) B3457511
theorem B3451895 : Blo 1020604 3451895 := bstep (se 1 (by rfl) ⟨2588921, by rfl⟩ : syracuseStep 3451895 = 5177843) B5177843
theorem B3452111 : Blo 1020604 3452111 := bstep (se 1 (by rfl) ⟨2589083, by rfl⟩ : syracuseStep 3452111 = 5178167) B5178167
theorem B9809515 : Blo 1020604 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B4140665 : Blo 1020604 4140665 := bstep (se 2 (by rfl) ⟨1552749, by rfl⟩ : syracuseStep 4140665 = 3105499) B3105499
theorem B5813207 : Blo 1020604 5813207 := bstep (se 1 (by rfl) ⟨4359905, by rfl⟩ : syracuseStep 5813207 = 8719811) B8719811
theorem B22426739 : Blo 1020604 22426739 := bstep (se 1 (by rfl) ⟨16820054, by rfl⟩ : syracuseStep 22426739 = 33640109) B33640109
theorem B13088375 : Blo 1020604 13088375 := bstep (se 1 (by rfl) ⟨9816281, by rfl⟩ : syracuseStep 13088375 = 19632563) B19632563
theorem B3880831 : Blo 1020604 3880831 := bstep (se 1 (by rfl) ⟨2910623, by rfl⟩ : syracuseStep 3880831 = 5821247) B5821247
theorem B1456633 : Blo 1020604 1456633 := bstep (se 2 (by rfl) ⟨546237, by rfl⟩ : syracuseStep 1456633 = 1092475) B1092475
theorem B8862365 : Blo 1020604 8862365 := bstep (se 3 (by rfl) ⟨1661693, by rfl⟩ : syracuseStep 8862365 = 3323387) B3323387
theorem B1555303 : Blo 1020604 1555303 := bstep (se 1 (by rfl) ⟨1166477, by rfl⟩ : syracuseStep 1555303 = 2332955) B2332955
theorem B1457767 : Blo 1020604 1457767 := bstep (se 1 (by rfl) ⟨1093325, by rfl⟩ : syracuseStep 1457767 = 2186651) B2186651
theorem B5390473 : Blo 1020604 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B59818945 : Blo 1020604 59818945 := bstep (se 2 (by rfl) ⟨22432104, by rfl⟩ : syracuseStep 59818945 = 44864209) B44864209
theorem B1295671 : Blo 1020604 1295671 := bstep (se 1 (by rfl) ⟨971753, by rfl⟩ : syracuseStep 1295671 = 1943507) B1943507
theorem B6539575 : Blo 1020604 6539575 := bstep (se 1 (by rfl) ⟨4904681, by rfl⟩ : syracuseStep 6539575 = 9809363) B9809363
theorem B5819039 : Blo 1020604 5819039 := bstep (se 1 (by rfl) ⟨4364279, by rfl⟩ : syracuseStep 5819039 = 8728559) B8728559
theorem B3887135 : Blo 1020604 3887135 := bstep (se 1 (by rfl) ⟨2915351, by rfl⟩ : syracuseStep 3887135 = 5830703) B5830703
theorem B23646271 : Blo 1020604 23646271 := bstep (se 1 (by rfl) ⟨17734703, by rfl⟩ : syracuseStep 23646271 = 35469407) B35469407
theorem B6541523 : Blo 1020604 6541523 := bstep (se 1 (by rfl) ⟨4906142, by rfl⟩ : syracuseStep 6541523 = 9812285) B9812285
theorem B15979771 : Blo 1020604 15979771 := bstep (se 1 (by rfl) ⟨11984828, by rfl⟩ : syracuseStep 15979771 = 23969657) B23969657
theorem B3692051 : Blo 1020604 3692051 := bstep (se 1 (by rfl) ⟨2769038, by rfl⟩ : syracuseStep 3692051 = 5538077) B5538077
theorem B11655251 : Blo 1020604 11655251 := bstep (se 1 (by rfl) ⟨8741438, by rfl⟩ : syracuseStep 11655251 = 17482877) B17482877
theorem B5593319 : Blo 1020604 5593319 := bstep (se 1 (by rfl) ⟨4194989, by rfl⟩ : syracuseStep 5593319 = 8389979) B8389979
theorem B3496463 : Blo 1020604 3496463 := bstep (se 1 (by rfl) ⟨2622347, by rfl⟩ : syracuseStep 3496463 = 5244695) B5244695
theorem B2906729 : Blo 1020604 2906729 := bstep (se 2 (by rfl) ⟨1090023, by rfl⟩ : syracuseStep 2906729 = 2180047) B2180047
theorem B126081917 : Blo 1020604 126081917 := bstep (se 3 (by rfl) ⟨23640359, by rfl⟩ : syracuseStep 126081917 = 47280719) B47280719
theorem B5168123 : Blo 1020604 5168123 := bstep (se 1 (by rfl) ⟨3876092, by rfl⟩ : syracuseStep 5168123 = 7752185) B7752185
theorem B2907515 : Blo 1020604 2907515 := bstep (se 1 (by rfl) ⟨2180636, by rfl⟩ : syracuseStep 2907515 = 4361273) B4361273
theorem B41967233 : Blo 1020604 41967233 := bstep (se 2 (by rfl) ⟨15737712, by rfl⟩ : syracuseStep 41967233 = 31475425) B31475425
theorem B9330319 : Blo 1020604 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B1531643 : Blo 1020604 1531643 := bstep (se 1 (by rfl) ⟨1148732, by rfl⟩ : syracuseStep 1531643 = 2297465) B2297465
theorem B1728425 : Blo 1020604 1728425 := bstep (se 2 (by rfl) ⟨648159, by rfl⟩ : syracuseStep 1728425 = 1296319) B1296319
theorem B6545623 : Blo 1020604 6545623 := bstep (se 1 (by rfl) ⟨4909217, by rfl⟩ : syracuseStep 6545623 = 9818435) B9818435
theorem B1532315 : Blo 1020604 1532315 := bstep (se 1 (by rfl) ⟨1149236, by rfl⟩ : syracuseStep 1532315 = 2298473) B2298473
theorem B5169743 : Blo 1020604 5169743 := bstep (se 1 (by rfl) ⟨3877307, by rfl⟩ : syracuseStep 5169743 = 7754615) B7754615
theorem B1532921 : Blo 1020604 1532921 := bstep (se 2 (by rfl) ⟨574845, by rfl⟩ : syracuseStep 1532921 = 1149691) B1149691
theorem B1533179 : Blo 1020604 1533179 := bstep (se 1 (by rfl) ⟨1149884, by rfl⟩ : syracuseStep 1533179 = 2299769) B2299769
theorem B1533695 : Blo 1020604 1533695 := bstep (se 1 (by rfl) ⟨1150271, by rfl⟩ : syracuseStep 1533695 = 2300543) B2300543
theorem B5826329 : Blo 1020604 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B9824125 : Blo 1020604 9824125 := bstep (se 3 (by rfl) ⟨1842023, by rfl⟩ : syracuseStep 9824125 = 3684047) B3684047
theorem B5827079 : Blo 1020604 5827079 := bstep (se 1 (by rfl) ⟨4370309, by rfl⟩ : syracuseStep 5827079 = 8740619) B8740619
theorem B1534697 : Blo 1020604 1534697 := bstep (se 2 (by rfl) ⟨575511, by rfl⟩ : syracuseStep 1534697 = 1151023) B1151023
theorem B1534751 : Blo 1020604 1534751 := bstep (se 1 (by rfl) ⟨1151063, by rfl⟩ : syracuseStep 1534751 = 2302127) B2302127
theorem B2911079 : Blo 1020604 2911079 := bstep (se 1 (by rfl) ⟨2183309, by rfl⟩ : syracuseStep 2911079 = 4366619) B4366619
theorem B1534919 : Blo 1020604 1534919 := bstep (se 1 (by rfl) ⟨1151189, by rfl⟩ : syracuseStep 1534919 = 2302379) B2302379
theorem B7367867 : Blo 1020604 7367867 := bstep (se 1 (by rfl) ⟨5525900, by rfl⟩ : syracuseStep 7367867 = 11051801) B11051801
theorem B5401799 : Blo 1020604 5401799 := bstep (se 1 (by rfl) ⟨4051349, by rfl⟩ : syracuseStep 5401799 = 8102699) B8102699
theorem B1535231 : Blo 1020604 1535231 := bstep (se 1 (by rfl) ⟨1151423, by rfl⟩ : syracuseStep 1535231 = 2302847) B2302847
theorem B2911763 : Blo 1020604 2911763 := bstep (se 1 (by rfl) ⟨2183822, by rfl⟩ : syracuseStep 2911763 = 4367645) B4367645
theorem B2584295 : Blo 1020604 2584295 := bstep (se 1 (by rfl) ⟨1938221, by rfl⟩ : syracuseStep 2584295 = 3876443) B3876443
theorem B2912071 : Blo 1020604 2912071 := bstep (se 1 (by rfl) ⟨2184053, by rfl⟩ : syracuseStep 2912071 = 4368107) B4368107
theorem B2584487 : Blo 1020604 2584487 := bstep (se 1 (by rfl) ⟨1938365, by rfl⟩ : syracuseStep 2584487 = 3876731) B3876731
theorem B1536071 : Blo 1020604 1536071 := bstep (se 1 (by rfl) ⟨1152053, by rfl⟩ : syracuseStep 1536071 = 2304107) B2304107
theorem B5173631 : Blo 1020604 5173631 := bstep (se 1 (by rfl) ⟨3880223, by rfl⟩ : syracuseStep 5173631 = 7760447) B7760447
theorem B1536491 : Blo 1020604 1536491 := bstep (se 1 (by rfl) ⟨1152368, by rfl⟩ : syracuseStep 1536491 = 2304737) B2304737
theorem B11071997 : Blo 1020604 11071997 := bstep (se 3 (by rfl) ⟨2075999, by rfl⟩ : syracuseStep 11071997 = 4151999) B4151999
theorem B2585135 : Blo 1020604 2585135 := bstep (se 1 (by rfl) ⟨1938851, by rfl⟩ : syracuseStep 2585135 = 3877703) B3877703
theorem B1536719 : Blo 1020604 1536719 := bstep (se 1 (by rfl) ⟨1152539, by rfl⟩ : syracuseStep 1536719 = 2305079) B2305079
theorem B7369825 : Blo 1020604 7369825 := bstep (se 2 (by rfl) ⟨2763684, by rfl⟩ : syracuseStep 7369825 = 5527369) B5527369
theorem B5830177 : Blo 1020604 5830177 := bstep (se 2 (by rfl) ⟨2186316, by rfl⟩ : syracuseStep 5830177 = 4372633) B4372633
theorem B2455147 : Blo 1020604 2455147 := bstep (se 1 (by rfl) ⟨1841360, by rfl⟩ : syracuseStep 2455147 = 3682721) B3682721
theorem B2586451 : Blo 1020604 2586451 := bstep (se 1 (by rfl) ⟨1939838, by rfl⟩ : syracuseStep 2586451 = 3879677) B3879677
theorem B12449771 : Blo 1020604 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B1473275 : Blo 1020604 1473275 := bstep (se 1 (by rfl) ⟨1104956, by rfl⟩ : syracuseStep 1473275 = 2209913) B2209913
theorem B7371785 : Blo 1020604 7371785 := bstep (se 2 (by rfl) ⟨2764419, by rfl⟩ : syracuseStep 7371785 = 5528839) B5528839
theorem B2916319 : Blo 1020604 2916319 := bstep (se 1 (by rfl) ⟨2187239, by rfl⟩ : syracuseStep 2916319 = 4374479) B4374479
theorem B1638559 : Blo 1020604 1638559 := bstep (se 1 (by rfl) ⟨1228919, by rfl⟩ : syracuseStep 1638559 = 2457839) B2457839
theorem B5177519 : Blo 1020604 5177519 := bstep (se 1 (by rfl) ⟨3883139, by rfl⟩ : syracuseStep 5177519 = 7766279) B7766279
theorem B79758593 : Blo 1020604 79758593 := bstep (se 2 (by rfl) ⟨29909472, by rfl⟩ : syracuseStep 79758593 = 59818945) B59818945
theorem B7768709 : Blo 1020604 7768709 := bstep (se 4 (by rfl) ⟨728316, by rfl⟩ : syracuseStep 7768709 = 1456633) B1456633
theorem B2591423 : Blo 1020604 2591423 := bstep (se 1 (by rfl) ⟨1943567, by rfl⟩ : syracuseStep 2591423 = 3887135) B3887135
theorem B4361015 : Blo 1020604 4361015 := bstep (se 1 (by rfl) ⟨3270761, by rfl⟩ : syracuseStep 4361015 = 6541523) B6541523
theorem B8719433 : Blo 1020604 8719433 := bstep (se 2 (by rfl) ⟨3269787, by rfl⟩ : syracuseStep 8719433 = 6539575) B6539575
theorem B2297087 : Blo 1020604 2297087 := bstep (se 1 (by rfl) ⟨1722815, by rfl⟩ : syracuseStep 2297087 = 3445631) B3445631
theorem B1969847 : Blo 1020604 1969847 := bstep (se 1 (by rfl) ⟨1477385, by rfl⟩ : syracuseStep 1969847 = 2954771) B2954771
theorem B2461367 : Blo 1020604 2461367 := bstep (se 1 (by rfl) ⟨1846025, by rfl⟩ : syracuseStep 2461367 = 3692051) B3692051
theorem B2297627 : Blo 1020604 2297627 := bstep (se 1 (by rfl) ⟨1723220, by rfl⟩ : syracuseStep 2297627 = 3446441) B3446441
theorem B7770167 : Blo 1020604 7770167 := bstep (se 1 (by rfl) ⟨5827625, by rfl⟩ : syracuseStep 7770167 = 11655251) B11655251
theorem B2330975 : Blo 1020604 2330975 := bstep (se 1 (by rfl) ⟨1748231, by rfl⟩ : syracuseStep 2330975 = 3496463) B3496463
theorem B1937819 : Blo 1020604 1937819 := bstep (se 1 (by rfl) ⟨1453364, by rfl⟩ : syracuseStep 1937819 = 2906729) B2906729
theorem B84054611 : Blo 1020604 84054611 := bstep (se 1 (by rfl) ⟨63040958, by rfl⟩ : syracuseStep 84054611 = 126081917) B126081917
theorem B2298527 : Blo 1020604 2298527 := bstep (se 1 (by rfl) ⟨1723895, by rfl⟩ : syracuseStep 2298527 = 3447791) B3447791
theorem B3445415 : Blo 1020604 3445415 := bstep (se 1 (by rfl) ⟨2584061, by rfl⟩ : syracuseStep 3445415 = 5168123) B5168123
theorem B2298671 : Blo 1020604 2298671 := bstep (se 1 (by rfl) ⟨1724003, by rfl⟩ : syracuseStep 2298671 = 3448007) B3448007
theorem B13079353 : Blo 1020604 13079353 := bstep (se 2 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 13079353 = 9809515) B9809515
theorem B1938343 : Blo 1020604 1938343 := bstep (se 1 (by rfl) ⟨1453757, by rfl⟩ : syracuseStep 1938343 = 2907515) B2907515
theorem B2298815 : Blo 1020604 2298815 := bstep (se 1 (by rfl) ⟨1724111, by rfl⟩ : syracuseStep 2298815 = 3448223) B3448223
theorem B1021095 : Blo 1020604 1021095 := bstep (se 1 (by rfl) ⟨765821, by rfl⟩ : syracuseStep 1021095 = 1531643) B1531643
theorem B1152283 : Blo 1020604 1152283 := bstep (se 1 (by rfl) ⟨864212, by rfl⟩ : syracuseStep 1152283 = 1728425) B1728425
theorem B31528361 : Blo 1020604 31528361 := bstep (se 2 (by rfl) ⟨11823135, by rfl⟩ : syracuseStep 31528361 = 23646271) B23646271
theorem B1021543 : Blo 1020604 1021543 := bstep (se 1 (by rfl) ⟨766157, by rfl⟩ : syracuseStep 1021543 = 1532315) B1532315
theorem B2299499 : Blo 1020604 2299499 := bstep (se 1 (by rfl) ⟨1724624, by rfl⟩ : syracuseStep 2299499 = 3449249) B3449249
theorem B2299535 : Blo 1020604 2299535 := bstep (se 1 (by rfl) ⟨1724651, by rfl⟩ : syracuseStep 2299535 = 3449303) B3449303
theorem B3446495 : Blo 1020604 3446495 := bstep (se 1 (by rfl) ⟨2584871, by rfl⟩ : syracuseStep 3446495 = 5169743) B5169743
theorem B37361411 : Blo 1020604 37361411 := bstep (se 1 (by rfl) ⟨28021058, by rfl⟩ : syracuseStep 37361411 = 56042117) B56042117
theorem B4921195 : Blo 1020604 4921195 := bstep (se 1 (by rfl) ⟨3690896, by rfl⟩ : syracuseStep 4921195 = 7381793) B7381793
theorem B1021947 : Blo 1020604 1021947 := bstep (se 1 (by rfl) ⟨766460, by rfl⟩ : syracuseStep 1021947 = 1532921) B1532921
theorem B1022119 : Blo 1020604 1022119 := bstep (se 1 (by rfl) ⟨766589, by rfl⟩ : syracuseStep 1022119 = 1533179) B1533179
theorem B1022463 : Blo 1020604 1022463 := bstep (se 1 (by rfl) ⟨766847, by rfl⟩ : syracuseStep 1022463 = 1533695) B1533695
theorem B19667933 : Blo 1020604 19667933 := bstep (se 3 (by rfl) ⟨3687737, by rfl⟩ : syracuseStep 19667933 = 7375475) B7375475
theorem B23632973 : Blo 1020604 23632973 := bstep (se 3 (by rfl) ⟨4431182, by rfl⟩ : syracuseStep 23632973 = 8862365) B8862365
theorem B2301011 : Blo 1020604 2301011 := bstep (se 1 (by rfl) ⟨1725758, by rfl⟩ : syracuseStep 2301011 = 3451517) B3451517
theorem B1023131 : Blo 1020604 1023131 := bstep (se 1 (by rfl) ⟨767348, by rfl⟩ : syracuseStep 1023131 = 1534697) B1534697
theorem B1023167 : Blo 1020604 1023167 := bstep (se 1 (by rfl) ⟨767375, by rfl⟩ : syracuseStep 1023167 = 1534751) B1534751
theorem B1023279 : Blo 1020604 1023279 := bstep (se 1 (by rfl) ⟨767459, by rfl⟩ : syracuseStep 1023279 = 1534919) B1534919
theorem B2301263 : Blo 1020604 2301263 := bstep (se 1 (by rfl) ⟨1725947, by rfl⟩ : syracuseStep 2301263 = 3451895) B3451895
theorem B7773569 : Blo 1020604 7773569 := bstep (se 2 (by rfl) ⟨2915088, by rfl⟩ : syracuseStep 7773569 = 5830177) B5830177
theorem B2301407 : Blo 1020604 2301407 := bstep (se 1 (by rfl) ⟨1726055, by rfl⟩ : syracuseStep 2301407 = 3452111) B3452111
theorem B1023487 : Blo 1020604 1023487 := bstep (se 1 (by rfl) ⟨767615, by rfl⟩ : syracuseStep 1023487 = 1535231) B1535231
theorem B1941175 : Blo 1020604 1941175 := bstep (se 1 (by rfl) ⟨1455881, by rfl⟩ : syracuseStep 1941175 = 2911763) B2911763
theorem B2760443 : Blo 1020604 2760443 := bstep (se 1 (by rfl) ⟨2070332, by rfl⟩ : syracuseStep 2760443 = 4140665) B4140665
theorem B3448601 : Blo 1020604 3448601 := bstep (se 2 (by rfl) ⟨1293225, by rfl⟩ : syracuseStep 3448601 = 2586451) B2586451
theorem B1024047 : Blo 1020604 1024047 := bstep (se 1 (by rfl) ⟨768035, by rfl⟩ : syracuseStep 1024047 = 1536071) B1536071
theorem B3449087 : Blo 1020604 3449087 := bstep (se 1 (by rfl) ⟨2586815, by rfl⟩ : syracuseStep 3449087 = 5173631) B5173631
theorem B1024327 : Blo 1020604 1024327 := bstep (se 1 (by rfl) ⟨768245, by rfl⟩ : syracuseStep 1024327 = 1536491) B1536491
theorem B7381331 : Blo 1020604 7381331 := bstep (se 1 (by rfl) ⟨5535998, by rfl⟩ : syracuseStep 7381331 = 11071997) B11071997
theorem B1024479 : Blo 1020604 1024479 := bstep (se 1 (by rfl) ⟨768359, by rfl⟩ : syracuseStep 1024479 = 1536719) B1536719
theorem B3875471 : Blo 1020604 3875471 := bstep (se 1 (by rfl) ⟨2906603, by rfl⟩ : syracuseStep 3875471 = 5813207) B5813207
theorem B14951159 : Blo 1020604 14951159 := bstep (se 1 (by rfl) ⟨11213369, by rfl⟩ : syracuseStep 14951159 = 22426739) B22426739
theorem B8725583 : Blo 1020604 8725583 := bstep (se 1 (by rfl) ⟨6544187, by rfl⟩ : syracuseStep 8725583 = 13088375) B13088375
theorem B2073737 : Blo 1020604 2073737 := bstep (se 2 (by rfl) ⟨777651, by rfl⟩ : syracuseStep 2073737 = 1555303) B1555303
theorem B8299847 : Blo 1020604 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B3680329 : Blo 1020604 3680329 := bstep (se 2 (by rfl) ⟨1380123, by rfl⟩ : syracuseStep 3680329 = 2760247) B2760247
theorem B1943689 : Blo 1020604 1943689 := bstep (se 2 (by rfl) ⟨728883, by rfl⟩ : syracuseStep 1943689 = 1457767) B1457767
theorem B8301305 : Blo 1020604 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B7187297 : Blo 1020604 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B8727497 : Blo 1020604 8727497 := bstep (se 2 (by rfl) ⟨3272811, by rfl⟩ : syracuseStep 8727497 = 6545623) B6545623
theorem B3452921 : Blo 1020604 3452921 := bstep (se 2 (by rfl) ⟨1294845, by rfl⟩ : syracuseStep 3452921 = 2589691) B2589691
theorem B3879359 : Blo 1020604 3879359 := bstep (se 1 (by rfl) ⟨2909519, by rfl⟩ : syracuseStep 3879359 = 5819039) B5819039
theorem B3683069 : Blo 1020604 3683069 := bstep (se 3 (by rfl) ⟨690575, by rfl⟩ : syracuseStep 3683069 = 1381151) B1381151
theorem B3453839 : Blo 1020604 3453839 := bstep (se 1 (by rfl) ⟨2590379, by rfl⟩ : syracuseStep 3453839 = 5180759) B5180759
theorem B67156073 : Blo 1020604 67156073 := bstep (se 2 (by rfl) ⟨25183527, by rfl⟩ : syracuseStep 67156073 = 50367055) B50367055
theorem B1292699 : Blo 1020604 1292699 := bstep (se 1 (by rfl) ⟨969524, by rfl⟩ : syracuseStep 1292699 = 1939049) B1939049
theorem B1751467 : Blo 1020604 1751467 := bstep (se 1 (by rfl) ⟨1313600, by rfl⟩ : syracuseStep 1751467 = 2627201) B2627201
theorem B29932001 : Blo 1020604 29932001 := bstep (se 2 (by rfl) ⟨11224500, by rfl⟩ : syracuseStep 29932001 = 22449001) B22449001
theorem B3882761 : Blo 1020604 3882761 := bstep (se 2 (by rfl) ⟨1456035, by rfl⟩ : syracuseStep 3882761 = 2912071) B2912071
theorem B16564459 : Blo 1020604 16564459 := bstep (se 1 (by rfl) ⟨12423344, by rfl⟩ : syracuseStep 16564459 = 24846689) B24846689
theorem B17515045 : Blo 1020604 17515045 := bstep (se 4 (by rfl) ⟨1642035, by rfl⟩ : syracuseStep 17515045 = 3284071) B3284071
theorem B4375367 : Blo 1020604 4375367 := bstep (se 1 (by rfl) ⟨3281525, by rfl⟩ : syracuseStep 4375367 = 6563051) B6563051
theorem B3457889 : Blo 1020604 3457889 := bstep (se 2 (by rfl) ⟨1296708, by rfl⟩ : syracuseStep 3457889 = 2593417) B2593417
theorem B3884219 : Blo 1020604 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B4375777 : Blo 1020604 4375777 := bstep (se 2 (by rfl) ⟨1640916, by rfl⟩ : syracuseStep 4375777 = 3281833) B3281833
theorem B3884719 : Blo 1020604 3884719 := bstep (se 1 (by rfl) ⟨2913539, by rfl⟩ : syracuseStep 3884719 = 5827079) B5827079
theorem B1722863 : Blo 1020604 1722863 := bstep (se 1 (by rfl) ⟨1292147, by rfl⟩ : syracuseStep 1722863 = 2584295) B2584295
theorem B1722991 : Blo 1020604 1722991 := bstep (se 1 (by rfl) ⟨1292243, by rfl⟩ : syracuseStep 1722991 = 2584487) B2584487
theorem B1723423 : Blo 1020604 1723423 := bstep (se 1 (by rfl) ⟨1292567, by rfl⟩ : syracuseStep 1723423 = 2585135) B2585135
theorem B49761701 : Blo 1020604 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B3888425 : Blo 1020604 3888425 := bstep (se 2 (by rfl) ⟨1458159, by rfl⟩ : syracuseStep 3888425 = 2916319) B2916319
theorem B1725799 : Blo 1020604 1725799 := bstep (se 1 (by rfl) ⟨1294349, by rfl⟩ : syracuseStep 1725799 = 2588699) B2588699
theorem B1726015 : Blo 1020604 1726015 := bstep (se 1 (by rfl) ⟨1294511, by rfl⟩ : syracuseStep 1726015 = 2589023) B2589023
theorem B2906387 : Blo 1020604 2906387 := bstep (se 1 (by rfl) ⟨2179790, by rfl⟩ : syracuseStep 2906387 = 4359581) B4359581
theorem B3889883 : Blo 1020604 3889883 := bstep (se 1 (by rfl) ⟨2917412, by rfl⟩ : syracuseStep 3889883 = 5834825) B5834825
theorem B1727399 : Blo 1020604 1727399 := bstep (se 1 (by rfl) ⟨1295549, by rfl⟩ : syracuseStep 1727399 = 2591099) B2591099
theorem B1530911 : Blo 1020604 1530911 := bstep (se 1 (by rfl) ⟨1148183, by rfl⟩ : syracuseStep 1530911 = 2296367) B2296367
theorem B1727561 : Blo 1020604 1727561 := bstep (se 2 (by rfl) ⟨647835, by rfl⟩ : syracuseStep 1727561 = 1295671) B1295671
theorem B5168285 : Blo 1020604 5168285 := bstep (se 3 (by rfl) ⟨969053, by rfl⟩ : syracuseStep 5168285 = 1938107) B1938107
theorem B1531463 : Blo 1020604 1531463 := bstep (se 1 (by rfl) ⟨1148597, by rfl⟩ : syracuseStep 1531463 = 2297195) B2297195
theorem B1728283 : Blo 1020604 1728283 := bstep (se 1 (by rfl) ⟨1296212, by rfl⟩ : syracuseStep 1728283 = 2592425) B2592425
theorem B1531727 : Blo 1020604 1531727 := bstep (se 1 (by rfl) ⟨1148795, by rfl⟩ : syracuseStep 1531727 = 2297591) B2297591
theorem B13098833 : Blo 1020604 13098833 := bstep (se 2 (by rfl) ⟨4912062, by rfl⟩ : syracuseStep 13098833 = 9824125) B9824125
theorem B1728607 : Blo 1020604 1728607 := bstep (se 1 (by rfl) ⟨1296455, by rfl⟩ : syracuseStep 1728607 = 2592911) B2592911
theorem B1532207 : Blo 1020604 1532207 := bstep (se 1 (by rfl) ⟨1149155, by rfl⟩ : syracuseStep 1532207 = 2298311) B2298311
theorem B1532231 : Blo 1020604 1532231 := bstep (se 1 (by rfl) ⟨1149173, by rfl⟩ : syracuseStep 1532231 = 2298347) B2298347
theorem B1532795 : Blo 1020604 1532795 := bstep (se 1 (by rfl) ⟨1149596, by rfl⟩ : syracuseStep 1532795 = 2299193) B2299193
theorem B1533083 : Blo 1020604 1533083 := bstep (se 1 (by rfl) ⟨1149812, by rfl⟩ : syracuseStep 1533083 = 2299625) B2299625
theorem B1533311 : Blo 1020604 1533311 := bstep (se 1 (by rfl) ⟨1149983, by rfl⟩ : syracuseStep 1533311 = 2299967) B2299967
theorem B3728879 : Blo 1020604 3728879 := bstep (se 1 (by rfl) ⟨2796659, by rfl⟩ : syracuseStep 3728879 = 5593319) B5593319
theorem B1533599 : Blo 1020604 1533599 := bstep (se 1 (by rfl) ⟨1150199, by rfl⟩ : syracuseStep 1533599 = 2300399) B2300399
theorem B1533947 : Blo 1020604 1533947 := bstep (se 1 (by rfl) ⟨1150460, by rfl⟩ : syracuseStep 1533947 = 2300921) B2300921
theorem B1534127 : Blo 1020604 1534127 := bstep (se 1 (by rfl) ⟨1150595, by rfl⟩ : syracuseStep 1534127 = 2301191) B2301191
theorem B27978155 : Blo 1020604 27978155 := bstep (se 1 (by rfl) ⟨20983616, by rfl⟩ : syracuseStep 27978155 = 41967233) B41967233
theorem B4909565 : Blo 1020604 4909565 := bstep (se 3 (by rfl) ⟨920543, by rfl⟩ : syracuseStep 4909565 = 1841087) B1841087
theorem B2910887 : Blo 1020604 2910887 := bstep (se 1 (by rfl) ⟨2183165, by rfl⟩ : syracuseStep 2910887 = 4366331) B4366331
theorem B1534655 : Blo 1020604 1534655 := bstep (se 1 (by rfl) ⟨1150991, by rfl⟩ : syracuseStep 1534655 = 2301983) B2301983
theorem B1535279 : Blo 1020604 1535279 := bstep (se 1 (by rfl) ⟨1151459, by rfl⟩ : syracuseStep 1535279 = 2302919) B2302919
theorem B1535711 : Blo 1020604 1535711 := bstep (se 1 (by rfl) ⟨1151783, by rfl⟩ : syracuseStep 1535711 = 2303567) B2303567
theorem B85225445 : Blo 1020604 85225445 := bstep (se 4 (by rfl) ⟨7989885, by rfl⟩ : syracuseStep 85225445 = 15979771) B15979771
theorem B9826433 : Blo 1020604 9826433 := bstep (se 2 (by rfl) ⟨3684912, by rfl⟩ : syracuseStep 9826433 = 7369825) B7369825
theorem B1536191 : Blo 1020604 1536191 := bstep (se 1 (by rfl) ⟨1152143, by rfl⟩ : syracuseStep 1536191 = 2304287) B2304287
theorem B3928733 : Blo 1020604 3928733 := bstep (se 3 (by rfl) ⟨736637, by rfl⟩ : syracuseStep 3928733 = 1473275) B1473275
theorem B1536671 : Blo 1020604 1536671 := bstep (se 1 (by rfl) ⟨1152503, by rfl⟩ : syracuseStep 1536671 = 2305007) B2305007
theorem B4911911 : Blo 1020604 4911911 := bstep (se 1 (by rfl) ⟨3683933, by rfl⟩ : syracuseStep 4911911 = 7367867) B7367867
theorem B3601199 : Blo 1020604 3601199 := bstep (se 1 (by rfl) ⟨2700899, by rfl⟩ : syracuseStep 3601199 = 5401799) B5401799
theorem B3273529 : Blo 1020604 3273529 := bstep (se 2 (by rfl) ⟨1227573, by rfl⟩ : syracuseStep 3273529 = 2455147) B2455147
theorem B7762877 : Blo 1020604 7762877 := bstep (se 3 (by rfl) ⟨1455539, by rfl⟩ : syracuseStep 7762877 = 2911079) B2911079
theorem B5174441 : Blo 1020604 5174441 := bstep (se 2 (by rfl) ⟨1940415, by rfl⟩ : syracuseStep 5174441 = 3880831) B3880831
theorem B11630465 : Blo 1020604 11630465 := bstep (se 2 (by rfl) ⟨4361424, by rfl⟩ : syracuseStep 11630465 = 8722849) B8722849
theorem B4914523 : Blo 1020604 4914523 := bstep (se 1 (by rfl) ⟨3685892, by rfl⟩ : syracuseStep 4914523 = 7371785) B7371785
theorem B22085945 : Blo 1020604 22085945 := bstep (se 2 (by rfl) ⟨8282229, by rfl⟩ : syracuseStep 22085945 = 16564459) B16564459
theorem B2916911 : Blo 1020604 2916911 := bstep (se 1 (by rfl) ⟨2187683, by rfl⟩ : syracuseStep 2916911 = 4375367) B4375367
theorem B2589479 : Blo 1020604 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B5834369 : Blo 1020604 5834369 := bstep (se 2 (by rfl) ⟨2187888, by rfl⟩ : syracuseStep 5834369 = 4375777) B4375777
theorem B1148575 : Blo 1020604 1148575 := bstep (se 1 (by rfl) ⟨861431, by rfl⟩ : syracuseStep 1148575 = 1722863) B1722863
theorem B5179139 : Blo 1020604 5179139 := bstep (se 1 (by rfl) ⟨3884354, by rfl⟩ : syracuseStep 5179139 = 7768709) B7768709
theorem B5179625 : Blo 1020604 5179625 := bstep (se 2 (by rfl) ⟨1942359, by rfl⟩ : syracuseStep 5179625 = 3884719) B3884719
theorem B1313231 : Blo 1020604 1313231 := bstep (se 1 (by rfl) ⟨984923, by rfl⟩ : syracuseStep 1313231 = 1969847) B1969847
theorem B1640911 : Blo 1020604 1640911 := bstep (se 1 (by rfl) ⟨1230683, by rfl⟩ : syracuseStep 1640911 = 2461367) B2461367
theorem B5180111 : Blo 1020604 5180111 := bstep (se 1 (by rfl) ⟨3885083, by rfl⟩ : syracuseStep 5180111 = 7770167) B7770167
theorem B2591585 : Blo 1020604 2591585 := bstep (se 2 (by rfl) ⟨971844, by rfl⟩ : syracuseStep 2591585 = 1943689) B1943689
theorem B2296943 : Blo 1020604 2296943 := bstep (se 1 (by rfl) ⟨1722707, by rfl⟩ : syracuseStep 2296943 = 3445415) B3445415
theorem B2297321 : Blo 1020604 2297321 := bstep (se 2 (by rfl) ⟨861495, by rfl⟩ : syracuseStep 2297321 = 1722991) B1722991
theorem B2592283 : Blo 1020604 2592283 := bstep (se 1 (by rfl) ⟨1944212, by rfl⟩ : syracuseStep 2592283 = 3888425) B3888425
theorem B2297663 : Blo 1020604 2297663 := bstep (se 1 (by rfl) ⟨1723247, by rfl⟩ : syracuseStep 2297663 = 3446495) B3446495
theorem B24907607 : Blo 1020604 24907607 := bstep (se 1 (by rfl) ⟨18680705, by rfl⟩ : syracuseStep 24907607 = 37361411) B37361411
theorem B2297897 : Blo 1020604 2297897 := bstep (se 2 (by rfl) ⟨861711, by rfl⟩ : syracuseStep 2297897 = 1723423) B1723423
theorem B1937591 : Blo 1020604 1937591 := bstep (se 1 (by rfl) ⟨1453193, by rfl⟩ : syracuseStep 1937591 = 2906387) B2906387
theorem B2593255 : Blo 1020604 2593255 := bstep (se 1 (by rfl) ⟨1944941, by rfl⟩ : syracuseStep 2593255 = 3889883) B3889883
theorem B1151599 : Blo 1020604 1151599 := bstep (se 1 (by rfl) ⟨863699, by rfl⟩ : syracuseStep 1151599 = 1727399) B1727399
theorem B13111955 : Blo 1020604 13111955 := bstep (se 1 (by rfl) ⟨9833966, by rfl⟩ : syracuseStep 13111955 = 19667933) B19667933
theorem B1020607 : Blo 1020604 1020607 := bstep (se 1 (by rfl) ⟨765455, by rfl⟩ : syracuseStep 1020607 = 1530911) B1530911
theorem B1151707 : Blo 1020604 1151707 := bstep (se 1 (by rfl) ⟨863780, by rfl⟩ : syracuseStep 1151707 = 1727561) B1727561
theorem B3445523 : Blo 1020604 3445523 := bstep (se 1 (by rfl) ⟨2584142, by rfl⟩ : syracuseStep 3445523 = 5168285) B5168285
theorem B5182379 : Blo 1020604 5182379 := bstep (se 1 (by rfl) ⟨3886784, by rfl⟩ : syracuseStep 5182379 = 7773569) B7773569
theorem B1020975 : Blo 1020604 1020975 := bstep (se 1 (by rfl) ⟨765731, by rfl⟩ : syracuseStep 1020975 = 1531463) B1531463
theorem B1840295 : Blo 1020604 1840295 := bstep (se 1 (by rfl) ⟨1380221, by rfl⟩ : syracuseStep 1840295 = 2760443) B2760443
theorem B2299067 : Blo 1020604 2299067 := bstep (se 1 (by rfl) ⟨1724300, by rfl⟩ : syracuseStep 2299067 = 3448601) B3448601
theorem B1021151 : Blo 1020604 1021151 := bstep (se 1 (by rfl) ⟨765863, by rfl⟩ : syracuseStep 1021151 = 1531727) B1531727
theorem B2299391 : Blo 1020604 2299391 := bstep (se 1 (by rfl) ⟨1724543, by rfl⟩ : syracuseStep 2299391 = 3449087) B3449087
theorem B1021471 : Blo 1020604 1021471 := bstep (se 1 (by rfl) ⟨766103, by rfl⟩ : syracuseStep 1021471 = 1532207) B1532207
theorem B1021487 : Blo 1020604 1021487 := bstep (se 1 (by rfl) ⟨766115, by rfl⟩ : syracuseStep 1021487 = 1532231) B1532231
theorem B4920887 : Blo 1020604 4920887 := bstep (se 1 (by rfl) ⟨3690665, by rfl⟩ : syracuseStep 4920887 = 7381331) B7381331
theorem B9967439 : Blo 1020604 9967439 := bstep (se 1 (by rfl) ⟨7475579, by rfl⟩ : syracuseStep 9967439 = 14951159) B14951159
theorem B1021863 : Blo 1020604 1021863 := bstep (se 1 (by rfl) ⟨766397, by rfl⟩ : syracuseStep 1021863 = 1532795) B1532795
theorem B1382491 : Blo 1020604 1382491 := bstep (se 1 (by rfl) ⟨1036868, by rfl⟩ : syracuseStep 1382491 = 2073737) B2073737
theorem B1022055 : Blo 1020604 1022055 := bstep (se 1 (by rfl) ⟨766541, by rfl⟩ : syracuseStep 1022055 = 1533083) B1533083
theorem B1022207 : Blo 1020604 1022207 := bstep (se 1 (by rfl) ⟨766655, by rfl⟩ : syracuseStep 1022207 = 1533311) B1533311
theorem B3447197 : Blo 1020604 3447197 := bstep (se 3 (by rfl) ⟨646349, by rfl⟩ : syracuseStep 3447197 = 1292699) B1292699
theorem B17439137 : Blo 1020604 17439137 := bstep (se 2 (by rfl) ⟨6539676, by rfl⟩ : syracuseStep 17439137 = 13079353) B13079353
theorem B4364705 : Blo 1020604 4364705 := bstep (se 2 (by rfl) ⟨1636764, by rfl⟩ : syracuseStep 4364705 = 3273529) B3273529
theorem B1022399 : Blo 1020604 1022399 := bstep (se 1 (by rfl) ⟨766799, by rfl⟩ : syracuseStep 1022399 = 1533599) B1533599
theorem B1022631 : Blo 1020604 1022631 := bstep (se 1 (by rfl) ⟨766973, by rfl⟩ : syracuseStep 1022631 = 1533947) B1533947
theorem B1022751 : Blo 1020604 1022751 := bstep (se 1 (by rfl) ⟨767063, by rfl⟩ : syracuseStep 1022751 = 1534127) B1534127
theorem B18652103 : Blo 1020604 18652103 := bstep (se 1 (by rfl) ⟨13989077, by rfl⟩ : syracuseStep 18652103 = 27978155) B27978155
theorem B1940591 : Blo 1020604 1940591 := bstep (se 1 (by rfl) ⟨1455443, by rfl⟩ : syracuseStep 1940591 = 2910887) B2910887
theorem B1023103 : Blo 1020604 1023103 := bstep (se 1 (by rfl) ⟨767327, by rfl⟩ : syracuseStep 1023103 = 1534655) B1534655
theorem B2301065 : Blo 1020604 2301065 := bstep (se 2 (by rfl) ⟨862899, by rfl⟩ : syracuseStep 2301065 = 1725799) B1725799
theorem B2301353 : Blo 1020604 2301353 := bstep (se 2 (by rfl) ⟨863007, by rfl⟩ : syracuseStep 2301353 = 1726015) B1726015
theorem B1023519 : Blo 1020604 1023519 := bstep (se 1 (by rfl) ⟨767639, by rfl⟩ : syracuseStep 1023519 = 1535279) B1535279
theorem B6561593 : Blo 1020604 6561593 := bstep (se 2 (by rfl) ⟨2460597, by rfl⟩ : syracuseStep 6561593 = 4921195) B4921195
theorem B1023807 : Blo 1020604 1023807 := bstep (se 1 (by rfl) ⟨767855, by rfl⟩ : syracuseStep 1023807 = 1535711) B1535711
theorem B2301947 : Blo 1020604 2301947 := bstep (se 1 (by rfl) ⟨1726460, by rfl⟩ : syracuseStep 2301947 = 3452921) B3452921
theorem B1024127 : Blo 1020604 1024127 := bstep (se 1 (by rfl) ⟨768095, by rfl⟩ : syracuseStep 1024127 = 1536191) B1536191
theorem B1024447 : Blo 1020604 1024447 := bstep (se 1 (by rfl) ⟨768335, by rfl⟩ : syracuseStep 1024447 = 1536671) B1536671
theorem B2400799 : Blo 1020604 2400799 := bstep (se 1 (by rfl) ⟨1800599, by rfl⟩ : syracuseStep 2400799 = 3601199) B3601199
theorem B2335289 : Blo 1020604 2335289 := bstep (se 2 (by rfl) ⟨875733, by rfl⟩ : syracuseStep 2335289 = 1751467) B1751467
theorem B2302559 : Blo 1020604 2302559 := bstep (se 1 (by rfl) ⟨1726919, by rfl⟩ : syracuseStep 2302559 = 3453839) B3453839
theorem B3449627 : Blo 1020604 3449627 := bstep (se 1 (by rfl) ⟨2587220, by rfl⟩ : syracuseStep 3449627 = 5174441) B5174441
theorem B44770715 : Blo 1020604 44770715 := bstep (se 1 (by rfl) ⟨33578036, by rfl⟩ : syracuseStep 44770715 = 67156073) B67156073
theorem B2304377 : Blo 1020604 2304377 := bstep (se 2 (by rfl) ⟨864141, by rfl⟩ : syracuseStep 2304377 = 1728283) B1728283
theorem B3451679 : Blo 1020604 3451679 := bstep (se 1 (by rfl) ⟨2588759, by rfl⟩ : syracuseStep 3451679 = 5177519) B5177519
theorem B2304809 : Blo 1020604 2304809 := bstep (se 2 (by rfl) ⟨864303, by rfl⟩ : syracuseStep 2304809 = 1728607) B1728607
theorem B2305259 : Blo 1020604 2305259 := bstep (se 1 (by rfl) ⟨1728944, by rfl⟩ : syracuseStep 2305259 = 3457889) B3457889
theorem B224145629 : Blo 1020604 224145629 := bstep (se 3 (by rfl) ⟨42027305, by rfl⟩ : syracuseStep 224145629 = 84054611) B84054611
theorem B5812955 : Blo 1020604 5812955 := bstep (se 1 (by rfl) ⟨4359716, by rfl⟩ : syracuseStep 5812955 = 8719433) B8719433
theorem B33174467 : Blo 1020604 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B1291879 : Blo 1020604 1291879 := bstep (se 1 (by rfl) ⟨968909, by rfl⟩ : syracuseStep 1291879 = 1937819) B1937819
theorem B21018907 : Blo 1020604 21018907 := bstep (se 1 (by rfl) ⟨15764180, by rfl⟩ : syracuseStep 21018907 = 31528361) B31528361
theorem B8732555 : Blo 1020604 8732555 := bstep (se 1 (by rfl) ⟨6549416, by rfl⟩ : syracuseStep 8732555 = 13098833) B13098833
theorem B5817055 : Blo 1020604 5817055 := bstep (se 1 (by rfl) ⟨4362791, by rfl⟩ : syracuseStep 5817055 = 8725583) B8725583
theorem B5818331 : Blo 1020604 5818331 := bstep (se 1 (by rfl) ⟨4363748, by rfl⟩ : syracuseStep 5818331 = 8727497) B8727497
theorem B22136813 : Blo 1020604 22136813 := bstep (se 3 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 22136813 = 8301305) B8301305
theorem B76664501 : Blo 1020604 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B7753643 : Blo 1020604 7753643 := bstep (se 1 (by rfl) ⟨5815232, by rfl⟩ : syracuseStep 7753643 = 11630465) B11630465
theorem B2184745 : Blo 1020604 2184745 := bstep (se 2 (by rfl) ⟨819279, by rfl⟩ : syracuseStep 2184745 = 1638559) B1638559
theorem B53172395 : Blo 1020604 53172395 := bstep (se 1 (by rfl) ⟨39879296, by rfl⟩ : syracuseStep 53172395 = 79758593) B79758593
theorem B6215933 : Blo 1020604 6215933 := bstep (se 3 (by rfl) ⟨1165487, by rfl⟩ : syracuseStep 6215933 = 2330975) B2330975
theorem B1727615 : Blo 1020604 1727615 := bstep (se 1 (by rfl) ⟨1295711, by rfl⟩ : syracuseStep 1727615 = 2591423) B2591423
theorem B2907343 : Blo 1020604 2907343 := bstep (se 1 (by rfl) ⟨2180507, by rfl⟩ : syracuseStep 2907343 = 4361015) B4361015
theorem B1531391 : Blo 1020604 1531391 := bstep (se 1 (by rfl) ⟨1148543, by rfl⟩ : syracuseStep 1531391 = 2297087) B2297087
theorem B1531751 : Blo 1020604 1531751 := bstep (se 1 (by rfl) ⟨1148813, by rfl⟩ : syracuseStep 1531751 = 2297627) B2297627
theorem B4907105 : Blo 1020604 4907105 := bstep (se 2 (by rfl) ⟨1840164, by rfl⟩ : syracuseStep 4907105 = 3680329) B3680329
theorem B93413573 : Blo 1020604 93413573 := bstep (se 4 (by rfl) ⟨8757522, by rfl⟩ : syracuseStep 93413573 = 17515045) B17515045
theorem B1532351 : Blo 1020604 1532351 := bstep (se 1 (by rfl) ⟨1149263, by rfl⟩ : syracuseStep 1532351 = 2298527) B2298527
theorem B1532447 : Blo 1020604 1532447 := bstep (se 1 (by rfl) ⟨1149335, by rfl⟩ : syracuseStep 1532447 = 2298671) B2298671
theorem B1532543 : Blo 1020604 1532543 := bstep (se 1 (by rfl) ⟨1149407, by rfl⟩ : syracuseStep 1532543 = 2298815) B2298815
theorem B1532999 : Blo 1020604 1532999 := bstep (se 1 (by rfl) ⟨1149749, by rfl⟩ : syracuseStep 1532999 = 2299499) B2299499
theorem B1533023 : Blo 1020604 1533023 := bstep (se 1 (by rfl) ⟨1149767, by rfl⟩ : syracuseStep 1533023 = 2299535) B2299535
theorem B15755315 : Blo 1020604 15755315 := bstep (se 1 (by rfl) ⟨11816486, by rfl⟩ : syracuseStep 15755315 = 23632973) B23632973
theorem B1534007 : Blo 1020604 1534007 := bstep (se 1 (by rfl) ⟨1150505, by rfl⟩ : syracuseStep 1534007 = 2301011) B2301011
theorem B1534175 : Blo 1020604 1534175 := bstep (se 1 (by rfl) ⟨1150631, by rfl⟩ : syracuseStep 1534175 = 2301263) B2301263
theorem B1534271 : Blo 1020604 1534271 := bstep (se 1 (by rfl) ⟨1150703, by rfl⟩ : syracuseStep 1534271 = 2301407) B2301407
theorem B2583647 : Blo 1020604 2583647 := bstep (se 1 (by rfl) ⟨1937735, by rfl⟩ : syracuseStep 2583647 = 3875471) B3875471
theorem B5533231 : Blo 1020604 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B2485919 : Blo 1020604 2485919 := bstep (se 1 (by rfl) ⟨1864439, by rfl⟩ : syracuseStep 2485919 = 3728879) B3728879
theorem B2584457 : Blo 1020604 2584457 := bstep (se 2 (by rfl) ⟨969171, by rfl⟩ : syracuseStep 2584457 = 1938343) B1938343
theorem B3273043 : Blo 1020604 3273043 := bstep (se 1 (by rfl) ⟨2454782, by rfl⟩ : syracuseStep 3273043 = 4909565) B4909565
theorem B1536377 : Blo 1020604 1536377 := bstep (se 2 (by rfl) ⟨576141, by rfl⟩ : syracuseStep 1536377 = 1152283) B1152283
theorem B56816963 : Blo 1020604 56816963 := bstep (se 1 (by rfl) ⟨42612722, by rfl⟩ : syracuseStep 56816963 = 85225445) B85225445
theorem B6550955 : Blo 1020604 6550955 := bstep (se 1 (by rfl) ⟨4913216, by rfl⟩ : syracuseStep 6550955 = 9826433) B9826433
theorem B2586239 : Blo 1020604 2586239 := bstep (se 1 (by rfl) ⟨1939679, by rfl⟩ : syracuseStep 2586239 = 3879359) B3879359
theorem B2619155 : Blo 1020604 2619155 := bstep (se 1 (by rfl) ⟨1964366, by rfl⟩ : syracuseStep 2619155 = 3928733) B3928733
theorem B2455379 : Blo 1020604 2455379 := bstep (se 1 (by rfl) ⟨1841534, by rfl⟩ : syracuseStep 2455379 = 3683069) B3683069
theorem B3274607 : Blo 1020604 3274607 := bstep (se 1 (by rfl) ⟨2455955, by rfl⟩ : syracuseStep 3274607 = 4911911) B4911911
theorem B5175251 : Blo 1020604 5175251 := bstep (se 1 (by rfl) ⟨3881438, by rfl⟩ : syracuseStep 5175251 = 7762877) B7762877
theorem B19954667 : Blo 1020604 19954667 := bstep (se 1 (by rfl) ⟨14966000, by rfl⟩ : syracuseStep 19954667 = 29932001) B29932001
theorem B6552697 : Blo 1020604 6552697 := bstep (se 2 (by rfl) ⟨2457261, by rfl⟩ : syracuseStep 6552697 = 4914523) B4914523
theorem B2588233 : Blo 1020604 2588233 := bstep (se 2 (by rfl) ⟨970587, by rfl⟩ : syracuseStep 2588233 = 1941175) B1941175
theorem B2588507 : Blo 1020604 2588507 := bstep (se 1 (by rfl) ⟨1941380, by rfl⟩ : syracuseStep 2588507 = 3882761) B3882761
theorem B6227437 : Blo 1020604 6227437 := bstep (se 3 (by rfl) ⟨1167644, by rfl⟩ : syracuseStep 6227437 = 2335289) B2335289
theorem B2297015 : Blo 1020604 2297015 := bstep (se 1 (by rfl) ⟨1722761, by rfl⟩ : syracuseStep 2297015 = 3445523) B3445523
theorem B3280591 : Blo 1020604 3280591 := bstep (se 1 (by rfl) ⟨2460443, by rfl⟩ : syracuseStep 3280591 = 4920887) B4920887
theorem B2298131 : Blo 1020604 2298131 := bstep (se 1 (by rfl) ⟨1723598, by rfl⟩ : syracuseStep 2298131 = 3447197) B3447197
theorem B6984413 : Blo 1020604 6984413 := bstep (se 3 (by rfl) ⟨1309577, by rfl⟩ : syracuseStep 6984413 = 2619155) B2619155
theorem B7377641 : Blo 1020604 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B1151743 : Blo 1020604 1151743 := bstep (se 1 (by rfl) ⟨863807, by rfl⟩ : syracuseStep 1151743 = 1727615) B1727615
theorem B1020927 : Blo 1020604 1020927 := bstep (se 1 (by rfl) ⟨765695, by rfl⟩ : syracuseStep 1020927 = 1531391) B1531391
theorem B1021167 : Blo 1020604 1021167 := bstep (se 1 (by rfl) ⟨765875, by rfl⟩ : syracuseStep 1021167 = 1531751) B1531751
theorem B42014173 : Blo 1020604 42014173 := bstep (se 3 (by rfl) ⟨7877657, by rfl⟩ : syracuseStep 42014173 = 15755315) B15755315
theorem B1021567 : Blo 1020604 1021567 := bstep (se 1 (by rfl) ⟨766175, by rfl⟩ : syracuseStep 1021567 = 1532351) B1532351
theorem B1021631 : Blo 1020604 1021631 := bstep (se 1 (by rfl) ⟨766223, by rfl⟩ : syracuseStep 1021631 = 1532447) B1532447
theorem B1021695 : Blo 1020604 1021695 := bstep (se 1 (by rfl) ⟨766271, by rfl⟩ : syracuseStep 1021695 = 1532543) B1532543
theorem B4364057 : Blo 1020604 4364057 := bstep (se 2 (by rfl) ⟨1636521, by rfl⟩ : syracuseStep 4364057 = 3273043) B3273043
theorem B2299751 : Blo 1020604 2299751 := bstep (se 1 (by rfl) ⟨1724813, by rfl⟩ : syracuseStep 2299751 = 3449627) B3449627
theorem B1021999 : Blo 1020604 1021999 := bstep (se 1 (by rfl) ⟨766499, by rfl⟩ : syracuseStep 1021999 = 1532999) B1532999
theorem B1022015 : Blo 1020604 1022015 := bstep (se 1 (by rfl) ⟨766511, by rfl⟩ : syracuseStep 1022015 = 1533023) B1533023
theorem B11639213 : Blo 1020604 11639213 := bstep (se 3 (by rfl) ⟨2182352, by rfl⟩ : syracuseStep 11639213 = 4364705) B4364705
theorem B1022671 : Blo 1020604 1022671 := bstep (se 1 (by rfl) ⟨767003, by rfl⟩ : syracuseStep 1022671 = 1534007) B1534007
theorem B1022783 : Blo 1020604 1022783 := bstep (se 1 (by rfl) ⟨767087, by rfl⟩ : syracuseStep 1022783 = 1534175) B1534175
theorem B1022847 : Blo 1020604 1022847 := bstep (se 1 (by rfl) ⟨767135, by rfl⟩ : syracuseStep 1022847 = 1534271) B1534271
theorem B2301119 : Blo 1020604 2301119 := bstep (se 1 (by rfl) ⟨1725839, by rfl⟩ : syracuseStep 2301119 = 3451679) B3451679
theorem B1843321 : Blo 1020604 1843321 := bstep (se 2 (by rfl) ⟨691245, by rfl⟩ : syracuseStep 1843321 = 1382491) B1382491
theorem B149430419 : Blo 1020604 149430419 := bstep (se 1 (by rfl) ⟨112072814, by rfl⟩ : syracuseStep 149430419 = 224145629) B224145629
theorem B1024251 : Blo 1020604 1024251 := bstep (se 1 (by rfl) ⟨768188, by rfl⟩ : syracuseStep 1024251 = 1536377) B1536377
theorem B28025209 : Blo 1020604 28025209 := bstep (se 2 (by rfl) ⟨10509453, by rfl⟩ : syracuseStep 28025209 = 21018907) B21018907
theorem B3875303 : Blo 1020604 3875303 := bstep (se 1 (by rfl) ⟨2906477, by rfl⟩ : syracuseStep 3875303 = 5812955) B5812955
theorem B4367303 : Blo 1020604 4367303 := bstep (se 1 (by rfl) ⟨3275477, by rfl⟩ : syracuseStep 4367303 = 6550955) B6550955
theorem B3450167 : Blo 1020604 3450167 := bstep (se 1 (by rfl) ⟨2587625, by rfl⟩ : syracuseStep 3450167 = 5175251) B5175251
theorem B3876457 : Blo 1020604 3876457 := bstep (se 2 (by rfl) ⟨1453671, by rfl⟩ : syracuseStep 3876457 = 2907343) B2907343
theorem B3450977 : Blo 1020604 3450977 := bstep (se 2 (by rfl) ⟨1294116, by rfl⟩ : syracuseStep 3450977 = 2588233) B2588233
theorem B14723963 : Blo 1020604 14723963 := bstep (se 1 (by rfl) ⟨11042972, by rfl⟩ : syracuseStep 14723963 = 22085945) B22085945
theorem B3452759 : Blo 1020604 3452759 := bstep (se 1 (by rfl) ⟨2589569, by rfl⟩ : syracuseStep 3452759 = 5179139) B5179139
theorem B3878887 : Blo 1020604 3878887 := bstep (se 1 (by rfl) ⟨2909165, by rfl⟩ : syracuseStep 3878887 = 5818331) B5818331
theorem B14757875 : Blo 1020604 14757875 := bstep (se 1 (by rfl) ⟨11068406, by rfl⟩ : syracuseStep 14757875 = 22136813) B22136813
theorem B7778429 : Blo 1020604 7778429 := bstep (se 3 (by rfl) ⟨1458455, by rfl⟩ : syracuseStep 7778429 = 2916911) B2916911
theorem B3453083 : Blo 1020604 3453083 := bstep (se 1 (by rfl) ⟨2589812, by rfl⟩ : syracuseStep 3453083 = 5179625) B5179625
theorem B3453407 : Blo 1020604 3453407 := bstep (se 1 (by rfl) ⟨2590055, by rfl⟩ : syracuseStep 3453407 = 5180111) B5180111
theorem B1291727 : Blo 1020604 1291727 := bstep (se 1 (by rfl) ⟨968795, by rfl⟩ : syracuseStep 1291727 = 1937591) B1937591
theorem B3454919 : Blo 1020604 3454919 := bstep (se 1 (by rfl) ⟨2591189, by rfl⟩ : syracuseStep 3454919 = 5182379) B5182379
theorem B1226863 : Blo 1020604 1226863 := bstep (se 1 (by rfl) ⟨920147, by rfl⟩ : syracuseStep 1226863 = 1840295) B1840295
theorem B4143955 : Blo 1020604 4143955 := bstep (se 1 (by rfl) ⟨3107966, by rfl⟩ : syracuseStep 4143955 = 6215933) B6215933
theorem B12434735 : Blo 1020604 12434735 := bstep (se 1 (by rfl) ⟨9326051, by rfl⟩ : syracuseStep 12434735 = 18652103) B18652103
theorem B3456377 : Blo 1020604 3456377 := bstep (se 2 (by rfl) ⟨1296141, by rfl⟩ : syracuseStep 3456377 = 2592283) B2592283
theorem B1293727 : Blo 1020604 1293727 := bstep (se 1 (by rfl) ⟨970295, by rfl⟩ : syracuseStep 1293727 = 1940591) B1940591
theorem B4374395 : Blo 1020604 4374395 := bstep (se 1 (by rfl) ⟨3280796, by rfl⟩ : syracuseStep 4374395 = 6561593) B6561593
theorem B62275715 : Blo 1020604 62275715 := bstep (se 1 (by rfl) ⟨46706786, by rfl⟩ : syracuseStep 62275715 = 93413573) B93413573
theorem B3457673 : Blo 1020604 3457673 := bstep (se 2 (by rfl) ⟨1296627, by rfl⟩ : syracuseStep 3457673 = 2593255) B2593255
theorem B1722431 : Blo 1020604 1722431 := bstep (se 1 (by rfl) ⟨1291823, by rfl⟩ : syracuseStep 1722431 = 2583647) B2583647
theorem B1722505 : Blo 1020604 1722505 := bstep (se 2 (by rfl) ⟨645939, by rfl⟩ : syracuseStep 1722505 = 1291879) B1291879
theorem B1657279 : Blo 1020604 1657279 := bstep (se 1 (by rfl) ⟨1242959, by rfl⟩ : syracuseStep 1657279 = 2485919) B2485919
theorem B1722971 : Blo 1020604 1722971 := bstep (se 1 (by rfl) ⟨1292228, by rfl⟩ : syracuseStep 1722971 = 2584457) B2584457
theorem B1724159 : Blo 1020604 1724159 := bstep (se 1 (by rfl) ⟨1293119, by rfl⟩ : syracuseStep 1724159 = 2586239) B2586239
theorem B2183071 : Blo 1020604 2183071 := bstep (se 1 (by rfl) ⟨1637303, by rfl⟩ : syracuseStep 2183071 = 3274607) B3274607
theorem B8736929 : Blo 1020604 8736929 := bstep (se 2 (by rfl) ⟨3276348, by rfl⟩ : syracuseStep 8736929 = 6552697) B6552697
theorem B1725671 : Blo 1020604 1725671 := bstep (se 1 (by rfl) ⟨1294253, by rfl⟩ : syracuseStep 1725671 = 2588507) B2588507
theorem B5821703 : Blo 1020604 5821703 := bstep (se 1 (by rfl) ⟨4366277, by rfl⟩ : syracuseStep 5821703 = 8732555) B8732555
theorem B1726319 : Blo 1020604 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B3201065 : Blo 1020604 3201065 := bstep (se 2 (by rfl) ⟨1200399, by rfl⟩ : syracuseStep 3201065 = 2400799) B2400799
theorem B7756073 : Blo 1020604 7756073 := bstep (se 2 (by rfl) ⟨2908527, by rfl⟩ : syracuseStep 7756073 = 5817055) B5817055
theorem B3889579 : Blo 1020604 3889579 := bstep (se 1 (by rfl) ⟨2917184, by rfl⟩ : syracuseStep 3889579 = 5834369) B5834369
theorem B1727723 : Blo 1020604 1727723 := bstep (se 1 (by rfl) ⟨1295792, by rfl⟩ : syracuseStep 1727723 = 2591585) B2591585
theorem B1531295 : Blo 1020604 1531295 := bstep (se 1 (by rfl) ⟨1148471, by rfl⟩ : syracuseStep 1531295 = 2296943) B2296943
theorem B1531433 : Blo 1020604 1531433 := bstep (se 2 (by rfl) ⟨574287, by rfl⟩ : syracuseStep 1531433 = 1148575) B1148575
theorem B1531547 : Blo 1020604 1531547 := bstep (se 1 (by rfl) ⟨1148660, by rfl⟩ : syracuseStep 1531547 = 2297321) B2297321
theorem B51109667 : Blo 1020604 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B1531775 : Blo 1020604 1531775 := bstep (se 1 (by rfl) ⟨1148831, by rfl⟩ : syracuseStep 1531775 = 2297663) B2297663
theorem B16605071 : Blo 1020604 16605071 := bstep (se 1 (by rfl) ⟨12453803, by rfl⟩ : syracuseStep 16605071 = 24907607) B24907607
theorem B5169095 : Blo 1020604 5169095 := bstep (se 1 (by rfl) ⟨3876821, by rfl⟩ : syracuseStep 5169095 = 7753643) B7753643
theorem B1531931 : Blo 1020604 1531931 := bstep (se 1 (by rfl) ⟨1148948, by rfl⟩ : syracuseStep 1531931 = 2297897) B2297897
theorem B8741303 : Blo 1020604 8741303 := bstep (se 1 (by rfl) ⟨6555977, by rfl⟩ : syracuseStep 8741303 = 13111955) B13111955
theorem B2187881 : Blo 1020604 2187881 := bstep (se 2 (by rfl) ⟨820455, by rfl⟩ : syracuseStep 2187881 = 1640911) B1640911
theorem B1532711 : Blo 1020604 1532711 := bstep (se 1 (by rfl) ⟨1149533, by rfl⟩ : syracuseStep 1532711 = 2299067) B2299067
theorem B1532927 : Blo 1020604 1532927 := bstep (se 1 (by rfl) ⟨1149695, by rfl⟩ : syracuseStep 1532927 = 2299391) B2299391
theorem B6644959 : Blo 1020604 6644959 := bstep (se 1 (by rfl) ⟨4983719, by rfl⟩ : syracuseStep 6644959 = 9967439) B9967439
theorem B35448263 : Blo 1020604 35448263 := bstep (se 1 (by rfl) ⟨26586197, by rfl⟩ : syracuseStep 35448263 = 53172395) B53172395
theorem B11626091 : Blo 1020604 11626091 := bstep (se 1 (by rfl) ⟨8719568, by rfl⟩ : syracuseStep 11626091 = 17439137) B17439137
theorem B1534043 : Blo 1020604 1534043 := bstep (se 1 (by rfl) ⟨1150532, by rfl⟩ : syracuseStep 1534043 = 2301065) B2301065
theorem B1534235 : Blo 1020604 1534235 := bstep (se 1 (by rfl) ⟨1150676, by rfl⟩ : syracuseStep 1534235 = 2301353) B2301353
theorem B1534631 : Blo 1020604 1534631 := bstep (se 1 (by rfl) ⟨1150973, by rfl⟩ : syracuseStep 1534631 = 2301947) B2301947
theorem B3271403 : Blo 1020604 3271403 := bstep (se 1 (by rfl) ⟨2453552, by rfl⟩ : syracuseStep 3271403 = 4907105) B4907105
theorem B1535039 : Blo 1020604 1535039 := bstep (se 1 (by rfl) ⟨1151279, by rfl⟩ : syracuseStep 1535039 = 2302559) B2302559
theorem B1535465 : Blo 1020604 1535465 := bstep (se 2 (by rfl) ⟨575799, by rfl⟩ : syracuseStep 1535465 = 1151599) B1151599
theorem B29847143 : Blo 1020604 29847143 := bstep (se 1 (by rfl) ⟨22385357, by rfl⟩ : syracuseStep 29847143 = 44770715) B44770715
theorem B1535609 : Blo 1020604 1535609 := bstep (se 2 (by rfl) ⟨575853, by rfl⟩ : syracuseStep 1535609 = 1151707) B1151707
theorem B3501949 : Blo 1020604 3501949 := bstep (se 3 (by rfl) ⟨656615, by rfl⟩ : syracuseStep 3501949 = 1313231) B1313231
theorem B1536251 : Blo 1020604 1536251 := bstep (se 1 (by rfl) ⟨1152188, by rfl⟩ : syracuseStep 1536251 = 2304377) B2304377
theorem B1536539 : Blo 1020604 1536539 := bstep (se 1 (by rfl) ⟨1152404, by rfl⟩ : syracuseStep 1536539 = 2304809) B2304809
theorem B2912993 : Blo 1020604 2912993 := bstep (se 2 (by rfl) ⟨1092372, by rfl⟩ : syracuseStep 2912993 = 2184745) B2184745
theorem B1536839 : Blo 1020604 1536839 := bstep (se 1 (by rfl) ⟨1152629, by rfl⟩ : syracuseStep 1536839 = 2305259) B2305259
theorem B22116311 : Blo 1020604 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B37877975 : Blo 1020604 37877975 := bstep (se 1 (by rfl) ⟨28408481, by rfl⟩ : syracuseStep 37877975 = 56816963) B56816963
theorem B1636919 : Blo 1020604 1636919 := bstep (se 1 (by rfl) ⟨1227689, by rfl⟩ : syracuseStep 1636919 = 2455379) B2455379
theorem B13303111 : Blo 1020604 13303111 := bstep (se 1 (by rfl) ⟨9977333, by rfl⟩ : syracuseStep 13303111 = 19954667) B19954667
theorem B41517143 : Blo 1020604 41517143 := bstep (se 1 (by rfl) ⟨31137857, by rfl⟩ : syracuseStep 41517143 = 62275715) B62275715
theorem B2457761 : Blo 1020604 2457761 := bstep (se 2 (by rfl) ⟨921660, by rfl⟩ : syracuseStep 2457761 = 1843321) B1843321
theorem B1148287 : Blo 1020604 1148287 := bstep (se 1 (by rfl) ⟨861215, by rfl⟩ : syracuseStep 1148287 = 1722431) B1722431
theorem B1148647 : Blo 1020604 1148647 := bstep (se 1 (by rfl) ⟨861485, by rfl⟩ : syracuseStep 1148647 = 1722971) B1722971
theorem B1149439 : Blo 1020604 1149439 := bstep (se 1 (by rfl) ⟨862079, by rfl⟩ : syracuseStep 1149439 = 1724159) B1724159
theorem B2296673 : Blo 1020604 2296673 := bstep (se 2 (by rfl) ⟨861252, by rfl⟩ : syracuseStep 2296673 = 1722505) B1722505
theorem B4656275 : Blo 1020604 4656275 := bstep (se 1 (by rfl) ⟨3492206, by rfl⟩ : syracuseStep 4656275 = 6984413) B6984413
theorem B4918427 : Blo 1020604 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B1150447 : Blo 1020604 1150447 := bstep (se 1 (by rfl) ⟨862835, by rfl⟩ : syracuseStep 1150447 = 1725671) B1725671
theorem B3444605 : Blo 1020604 3444605 := bstep (se 3 (by rfl) ⟨645863, by rfl⟩ : syracuseStep 3444605 = 1291727) B1291727
theorem B1150879 : Blo 1020604 1150879 := bstep (se 1 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 1150879 = 1726319) B1726319
theorem B2134043 : Blo 1020604 2134043 := bstep (se 1 (by rfl) ⟨1600532, by rfl⟩ : syracuseStep 2134043 = 3201065) B3201065
theorem B1151815 : Blo 1020604 1151815 := bstep (se 1 (by rfl) ⟨863861, by rfl⟩ : syracuseStep 1151815 = 1727723) B1727723
theorem B1020863 : Blo 1020604 1020863 := bstep (se 1 (by rfl) ⟨765647, by rfl⟩ : syracuseStep 1020863 = 1531295) B1531295
theorem B1020955 : Blo 1020604 1020955 := bstep (se 1 (by rfl) ⟨765716, by rfl⟩ : syracuseStep 1020955 = 1531433) B1531433
theorem B1021031 : Blo 1020604 1021031 := bstep (se 1 (by rfl) ⟨765773, by rfl⟩ : syracuseStep 1021031 = 1531547) B1531547
theorem B1021183 : Blo 1020604 1021183 := bstep (se 1 (by rfl) ⟨765887, by rfl⟩ : syracuseStep 1021183 = 1531775) B1531775
theorem B3446063 : Blo 1020604 3446063 := bstep (se 1 (by rfl) ⟨2584547, by rfl⟩ : syracuseStep 3446063 = 5169095) B5169095
theorem B1021287 : Blo 1020604 1021287 := bstep (se 1 (by rfl) ⟨765965, by rfl⟩ : syracuseStep 1021287 = 1531931) B1531931
theorem B99620279 : Blo 1020604 99620279 := bstep (se 1 (by rfl) ⟨74715209, by rfl⟩ : syracuseStep 99620279 = 149430419) B149430419
theorem B1021807 : Blo 1020604 1021807 := bstep (se 1 (by rfl) ⟨766355, by rfl⟩ : syracuseStep 1021807 = 1532711) B1532711
theorem B1021951 : Blo 1020604 1021951 := bstep (se 1 (by rfl) ⟨766463, by rfl⟩ : syracuseStep 1021951 = 1532927) B1532927
theorem B2300111 : Blo 1020604 2300111 := bstep (se 1 (by rfl) ⟨1725083, by rfl⟩ : syracuseStep 2300111 = 3450167) B3450167
theorem B23632175 : Blo 1020604 23632175 := bstep (se 1 (by rfl) ⟨17724131, by rfl⟩ : syracuseStep 23632175 = 35448263) B35448263
theorem B1022695 : Blo 1020604 1022695 := bstep (se 1 (by rfl) ⟨767021, by rfl⟩ : syracuseStep 1022695 = 1534043) B1534043
theorem B2300651 : Blo 1020604 2300651 := bstep (se 1 (by rfl) ⟨1725488, by rfl⟩ : syracuseStep 2300651 = 3450977) B3450977
theorem B1022823 : Blo 1020604 1022823 := bstep (se 1 (by rfl) ⟨767117, by rfl⟩ : syracuseStep 1022823 = 1534235) B1534235
theorem B1023087 : Blo 1020604 1023087 := bstep (se 1 (by rfl) ⟨767315, by rfl⟩ : syracuseStep 1023087 = 1534631) B1534631
theorem B1023359 : Blo 1020604 1023359 := bstep (se 1 (by rfl) ⟨767519, by rfl⟩ : syracuseStep 1023359 = 1535039) B1535039
theorem B1023643 : Blo 1020604 1023643 := bstep (se 1 (by rfl) ⟨767732, by rfl⟩ : syracuseStep 1023643 = 1535465) B1535465
theorem B1023739 : Blo 1020604 1023739 := bstep (se 1 (by rfl) ⟨767804, by rfl⟩ : syracuseStep 1023739 = 1535609) B1535609
theorem B2301839 : Blo 1020604 2301839 := bstep (se 1 (by rfl) ⟨1726379, by rfl⟩ : syracuseStep 2301839 = 3452759) B3452759
theorem B9838583 : Blo 1020604 9838583 := bstep (se 1 (by rfl) ⟨7378937, by rfl⟩ : syracuseStep 9838583 = 14757875) B14757875
theorem B5185619 : Blo 1020604 5185619 := bstep (se 1 (by rfl) ⟨3889214, by rfl⟩ : syracuseStep 5185619 = 7778429) B7778429
theorem B2302055 : Blo 1020604 2302055 := bstep (se 1 (by rfl) ⟨1726541, by rfl⟩ : syracuseStep 2302055 = 3453083) B3453083
theorem B1024167 : Blo 1020604 1024167 := bstep (se 1 (by rfl) ⟨768125, by rfl⟩ : syracuseStep 1024167 = 1536251) B1536251
theorem B2302271 : Blo 1020604 2302271 := bstep (se 1 (by rfl) ⟨1726703, by rfl⟩ : syracuseStep 2302271 = 3453407) B3453407
theorem B1024359 : Blo 1020604 1024359 := bstep (se 1 (by rfl) ⟨768269, by rfl⟩ : syracuseStep 1024359 = 1536539) B1536539
theorem B1941995 : Blo 1020604 1941995 := bstep (se 1 (by rfl) ⟨1456496, by rfl⟩ : syracuseStep 1941995 = 2912993) B2912993
theorem B1024559 : Blo 1020604 1024559 := bstep (se 1 (by rfl) ⟨768419, by rfl⟩ : syracuseStep 1024559 = 1536839) B1536839
theorem B5186105 : Blo 1020604 5186105 := bstep (se 2 (by rfl) ⟨1944789, by rfl⟩ : syracuseStep 5186105 = 3889579) B3889579
theorem B2303279 : Blo 1020604 2303279 := bstep (se 1 (by rfl) ⟨1727459, by rfl⟩ : syracuseStep 2303279 = 3454919) B3454919
theorem B1091279 : Blo 1020604 1091279 := bstep (se 1 (by rfl) ⟨818459, by rfl⟩ : syracuseStep 1091279 = 1636919) B1636919
theorem B17737481 : Blo 1020604 17737481 := bstep (se 2 (by rfl) ⟨6651555, by rfl⟩ : syracuseStep 17737481 = 13303111) B13303111
theorem B2304251 : Blo 1020604 2304251 := bstep (se 1 (by rfl) ⟨1728188, by rfl⟩ : syracuseStep 2304251 = 3456377) B3456377
theorem B2305115 : Blo 1020604 2305115 := bstep (se 1 (by rfl) ⟨1728836, by rfl⟩ : syracuseStep 2305115 = 3457673) B3457673
theorem B149467781 : Blo 1020604 149467781 := bstep (se 4 (by rfl) ⟨14012604, by rfl⟩ : syracuseStep 149467781 = 28025209) B28025209
theorem B8303249 : Blo 1020604 8303249 := bstep (se 2 (by rfl) ⟨3113718, by rfl⟩ : syracuseStep 8303249 = 6227437) B6227437
theorem B3881135 : Blo 1020604 3881135 := bstep (se 1 (by rfl) ⟨2910851, by rfl⟩ : syracuseStep 3881135 = 5821703) B5821703
theorem B4374121 : Blo 1020604 4374121 := bstep (se 2 (by rfl) ⟨1640295, by rfl⟩ : syracuseStep 4374121 = 3280591) B3280591
theorem B4669265 : Blo 1020604 4669265 := bstep (se 2 (by rfl) ⟨1750974, by rfl⟩ : syracuseStep 4669265 = 3501949) B3501949
theorem B1458587 : Blo 1020604 1458587 := bstep (se 1 (by rfl) ⟨1093940, by rfl⟩ : syracuseStep 1458587 = 2187881) B2187881
theorem B7750727 : Blo 1020604 7750727 := bstep (se 1 (by rfl) ⟨5813045, by rfl⟩ : syracuseStep 7750727 = 11626091) B11626091
theorem B35439781 : Blo 1020604 35439781 := bstep (se 4 (by rfl) ⟨3322479, by rfl⟩ : syracuseStep 35439781 = 6644959) B6644959
theorem B2180935 : Blo 1020604 2180935 := bstep (se 1 (by rfl) ⟨1635701, by rfl⟩ : syracuseStep 2180935 = 3271403) B3271403
theorem B9815975 : Blo 1020604 9815975 := bstep (se 1 (by rfl) ⟨7361981, by rfl⟩ : syracuseStep 9815975 = 14723963) B14723963
theorem B56018897 : Blo 1020604 56018897 := bstep (se 2 (by rfl) ⟨21007086, by rfl⟩ : syracuseStep 56018897 = 42014173) B42014173
theorem B5525273 : Blo 1020604 5525273 := bstep (se 2 (by rfl) ⟨2071977, by rfl⟩ : syracuseStep 5525273 = 4143955) B4143955
theorem B25251983 : Blo 1020604 25251983 := bstep (se 1 (by rfl) ⟨18938987, by rfl⟩ : syracuseStep 25251983 = 37877975) B37877975
theorem B1724969 : Blo 1020604 1724969 := bstep (se 2 (by rfl) ⟨646863, by rfl⟩ : syracuseStep 1724969 = 1293727) B1293727
theorem B1531343 : Blo 1020604 1531343 := bstep (se 1 (by rfl) ⟨1148507, by rfl⟩ : syracuseStep 1531343 = 2297015) B2297015
theorem B5168609 : Blo 1020604 5168609 := bstep (se 2 (by rfl) ⟨1938228, by rfl⟩ : syracuseStep 5168609 = 3876457) B3876457
theorem B8838821 : Blo 1020604 8838821 := bstep (se 4 (by rfl) ⟨828639, by rfl⟩ : syracuseStep 8838821 = 1657279) B1657279
theorem B5824619 : Blo 1020604 5824619 := bstep (se 1 (by rfl) ⟨4368464, by rfl⟩ : syracuseStep 5824619 = 8736929) B8736929
theorem B1532087 : Blo 1020604 1532087 := bstep (se 1 (by rfl) ⟨1149065, by rfl⟩ : syracuseStep 1532087 = 2298131) B2298131
theorem B2909371 : Blo 1020604 2909371 := bstep (se 1 (by rfl) ⟨2182028, by rfl⟩ : syracuseStep 2909371 = 4364057) B4364057
theorem B1533167 : Blo 1020604 1533167 := bstep (se 1 (by rfl) ⟨1149875, by rfl⟩ : syracuseStep 1533167 = 2299751) B2299751
theorem B5170715 : Blo 1020604 5170715 := bstep (se 1 (by rfl) ⟨3878036, by rfl⟩ : syracuseStep 5170715 = 7756073) B7756073
theorem B7759475 : Blo 1020604 7759475 := bstep (se 1 (by rfl) ⟨5819606, by rfl⟩ : syracuseStep 7759475 = 11639213) B11639213
theorem B1534079 : Blo 1020604 1534079 := bstep (se 1 (by rfl) ⟨1150559, by rfl⟩ : syracuseStep 1534079 = 2301119) B2301119
theorem B34073111 : Blo 1020604 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B2910761 : Blo 1020604 2910761 := bstep (se 2 (by rfl) ⟨1091535, by rfl⟩ : syracuseStep 2910761 = 2183071) B2183071
theorem B11070047 : Blo 1020604 11070047 := bstep (se 1 (by rfl) ⟨8302535, by rfl⟩ : syracuseStep 11070047 = 16605071) B16605071
theorem B5171849 : Blo 1020604 5171849 := bstep (se 2 (by rfl) ⟨1939443, by rfl⟩ : syracuseStep 5171849 = 3878887) B3878887
theorem B5827535 : Blo 1020604 5827535 := bstep (se 1 (by rfl) ⟨4370651, by rfl⟩ : syracuseStep 5827535 = 8741303) B8741303
theorem B2583535 : Blo 1020604 2583535 := bstep (se 1 (by rfl) ⟨1937651, by rfl⟩ : syracuseStep 2583535 = 3875303) B3875303
theorem B2911535 : Blo 1020604 2911535 := bstep (se 1 (by rfl) ⟨2183651, by rfl⟩ : syracuseStep 2911535 = 4367303) B4367303
theorem B1535657 : Blo 1020604 1535657 := bstep (se 2 (by rfl) ⟨575871, by rfl⟩ : syracuseStep 1535657 = 1151743) B1151743
theorem B1635817 : Blo 1020604 1635817 := bstep (se 2 (by rfl) ⟨613431, by rfl⟩ : syracuseStep 1635817 = 1226863) B1226863
theorem B33159293 : Blo 1020604 33159293 := bstep (se 3 (by rfl) ⟨6217367, by rfl⟩ : syracuseStep 33159293 = 12434735) B12434735
theorem B14744207 : Blo 1020604 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B79592381 : Blo 1020604 79592381 := bstep (se 3 (by rfl) ⟨14923571, by rfl⟩ : syracuseStep 79592381 = 29847143) B29847143
theorem B2916263 : Blo 1020604 2916263 := bstep (se 1 (by rfl) ⟨2187197, by rfl⟩ : syracuseStep 2916263 = 4374395) B4374395
theorem B6554029 : Blo 1020604 6554029 := bstep (se 3 (by rfl) ⟨1228880, by rfl⟩ : syracuseStep 6554029 = 2457761) B2457761
theorem B5178653 : Blo 1020604 5178653 := bstep (se 3 (by rfl) ⟨970997, by rfl⟩ : syracuseStep 5178653 = 1941995) B1941995
theorem B47253041 : Blo 1020604 47253041 := bstep (se 2 (by rfl) ⟨17719890, by rfl⟩ : syracuseStep 47253041 = 35439781) B35439781
theorem B3278951 : Blo 1020604 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B2296403 : Blo 1020604 2296403 := bstep (se 1 (by rfl) ⟨1722302, by rfl⟩ : syracuseStep 2296403 = 3444605) B3444605
theorem B1149979 : Blo 1020604 1149979 := bstep (se 1 (by rfl) ⟨862484, by rfl⟩ : syracuseStep 1149979 = 1724969) B1724969
theorem B2297375 : Blo 1020604 2297375 := bstep (se 1 (by rfl) ⟨1723031, by rfl⟩ : syracuseStep 2297375 = 3446063) B3446063
theorem B3444713 : Blo 1020604 3444713 := bstep (se 2 (by rfl) ⟨1291767, by rfl⟩ : syracuseStep 3444713 = 2583535) B2583535
theorem B1020895 : Blo 1020604 1020895 := bstep (se 1 (by rfl) ⟨765671, by rfl⟩ : syracuseStep 1020895 = 1531343) B1531343
theorem B3445739 : Blo 1020604 3445739 := bstep (se 1 (by rfl) ⟨2584304, by rfl⟩ : syracuseStep 3445739 = 5168609) B5168609
theorem B6559055 : Blo 1020604 6559055 := bstep (se 1 (by rfl) ⟨4919291, by rfl⟩ : syracuseStep 6559055 = 9838583) B9838583
theorem B1021391 : Blo 1020604 1021391 := bstep (se 1 (by rfl) ⟨766043, by rfl⟩ : syracuseStep 1021391 = 1532087) B1532087
theorem B1022111 : Blo 1020604 1022111 := bstep (se 1 (by rfl) ⟨766583, by rfl⟩ : syracuseStep 1022111 = 1533167) B1533167
theorem B3447143 : Blo 1020604 3447143 := bstep (se 1 (by rfl) ⟨2585357, by rfl⟩ : syracuseStep 3447143 = 5170715) B5170715
theorem B1022719 : Blo 1020604 1022719 := bstep (se 1 (by rfl) ⟨767039, by rfl⟩ : syracuseStep 1022719 = 1534079) B1534079
theorem B22715407 : Blo 1020604 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B1940507 : Blo 1020604 1940507 := bstep (se 1 (by rfl) ⟨1455380, by rfl⟩ : syracuseStep 1940507 = 2910761) B2910761
theorem B3447899 : Blo 1020604 3447899 := bstep (se 1 (by rfl) ⟨2585924, by rfl⟩ : syracuseStep 3447899 = 5171849) B5171849
theorem B1941023 : Blo 1020604 1941023 := bstep (se 1 (by rfl) ⟨1455767, by rfl⟩ : syracuseStep 1941023 = 2911535) B2911535
theorem B1023771 : Blo 1020604 1023771 := bstep (se 1 (by rfl) ⟨767828, by rfl⟩ : syracuseStep 1023771 = 1535657) B1535657
theorem B23570189 : Blo 1020604 23570189 := bstep (se 3 (by rfl) ⟨4419410, by rfl⟩ : syracuseStep 23570189 = 8838821) B8838821
theorem B53061587 : Blo 1020604 53061587 := bstep (se 1 (by rfl) ⟨39796190, by rfl⟩ : syracuseStep 53061587 = 79592381) B79592381
theorem B1944175 : Blo 1020604 1944175 := bstep (se 1 (by rfl) ⟨1458131, by rfl⟩ : syracuseStep 1944175 = 2916263) B2916263
theorem B3879161 : Blo 1020604 3879161 := bstep (se 2 (by rfl) ⟨1454685, by rfl⟩ : syracuseStep 3879161 = 2909371) B2909371
theorem B1422695 : Blo 1020604 1422695 := bstep (se 1 (by rfl) ⟨1067021, by rfl⟩ : syracuseStep 1422695 = 2134043) B2134043
theorem B3457079 : Blo 1020604 3457079 := bstep (se 1 (by rfl) ⟨2592809, by rfl⟩ : syracuseStep 3457079 = 5185619) B5185619
theorem B3883079 : Blo 1020604 3883079 := bstep (se 1 (by rfl) ⟨2912309, by rfl⟩ : syracuseStep 3883079 = 5824619) B5824619
theorem B3457403 : Blo 1020604 3457403 := bstep (se 1 (by rfl) ⟨2593052, by rfl⟩ : syracuseStep 3457403 = 5186105) B5186105
theorem B3885023 : Blo 1020604 3885023 := bstep (se 1 (by rfl) ⟨2913767, by rfl⟩ : syracuseStep 3885023 = 5827535) B5827535
theorem B2181089 : Blo 1020604 2181089 := bstep (se 2 (by rfl) ⟨817908, by rfl⟩ : syracuseStep 2181089 = 1635817) B1635817
theorem B22106195 : Blo 1020604 22106195 := bstep (se 1 (by rfl) ⟨16579646, by rfl⟩ : syracuseStep 22106195 = 33159293) B33159293
theorem B14734061 : Blo 1020604 14734061 := bstep (se 3 (by rfl) ⟨2762636, by rfl⟩ : syracuseStep 14734061 = 5525273) B5525273
theorem B27678095 : Blo 1020604 27678095 := bstep (se 1 (by rfl) ⟨20758571, by rfl⟩ : syracuseStep 27678095 = 41517143) B41517143
theorem B5167151 : Blo 1020604 5167151 := bstep (se 1 (by rfl) ⟨3875363, by rfl⟩ : syracuseStep 5167151 = 7750727) B7750727
theorem B3889565 : Blo 1020604 3889565 := bstep (se 3 (by rfl) ⟨729293, by rfl⟩ : syracuseStep 3889565 = 1458587) B1458587
theorem B6543983 : Blo 1020604 6543983 := bstep (se 1 (by rfl) ⟨4907987, by rfl⟩ : syracuseStep 6543983 = 9815975) B9815975
theorem B37345931 : Blo 1020604 37345931 := bstep (se 1 (by rfl) ⟨28009448, by rfl⟩ : syracuseStep 37345931 = 56018897) B56018897
theorem B1531049 : Blo 1020604 1531049 := bstep (se 2 (by rfl) ⟨574143, by rfl⟩ : syracuseStep 1531049 = 1148287) B1148287
theorem B1531115 : Blo 1020604 1531115 := bstep (se 1 (by rfl) ⟨1148336, by rfl⟩ : syracuseStep 1531115 = 2296673) B2296673
theorem B3104183 : Blo 1020604 3104183 := bstep (se 1 (by rfl) ⟨2328137, by rfl⟩ : syracuseStep 3104183 = 4656275) B4656275
theorem B1531529 : Blo 1020604 1531529 := bstep (se 2 (by rfl) ⟨574323, by rfl⟩ : syracuseStep 1531529 = 1148647) B1148647
theorem B2907913 : Blo 1020604 2907913 := bstep (se 2 (by rfl) ⟨1090467, by rfl⟩ : syracuseStep 2907913 = 2180935) B2180935
theorem B16834655 : Blo 1020604 16834655 := bstep (se 1 (by rfl) ⟨12625991, by rfl⟩ : syracuseStep 16834655 = 25251983) B25251983
theorem B1532585 : Blo 1020604 1532585 := bstep (se 2 (by rfl) ⟨574719, by rfl⟩ : syracuseStep 1532585 = 1149439) B1149439
theorem B66413519 : Blo 1020604 66413519 := bstep (se 1 (by rfl) ⟨49810139, by rfl⟩ : syracuseStep 66413519 = 99620279) B99620279
theorem B1533407 : Blo 1020604 1533407 := bstep (se 1 (by rfl) ⟨1150055, by rfl⟩ : syracuseStep 1533407 = 2300111) B2300111
theorem B15754783 : Blo 1020604 15754783 := bstep (se 1 (by rfl) ⟨11816087, by rfl⟩ : syracuseStep 15754783 = 23632175) B23632175
theorem B1533767 : Blo 1020604 1533767 := bstep (se 1 (by rfl) ⟨1150325, by rfl⟩ : syracuseStep 1533767 = 2300651) B2300651
theorem B2910077 : Blo 1020604 2910077 := bstep (se 3 (by rfl) ⟨545639, by rfl⟩ : syracuseStep 2910077 = 1091279) B1091279
theorem B1533929 : Blo 1020604 1533929 := bstep (se 2 (by rfl) ⟨575223, by rfl⟩ : syracuseStep 1533929 = 1150447) B1150447
theorem B1534505 : Blo 1020604 1534505 := bstep (se 2 (by rfl) ⟨575439, by rfl⟩ : syracuseStep 1534505 = 1150879) B1150879
theorem B1534559 : Blo 1020604 1534559 := bstep (se 1 (by rfl) ⟨1150919, by rfl⟩ : syracuseStep 1534559 = 2301839) B2301839
theorem B1534703 : Blo 1020604 1534703 := bstep (se 1 (by rfl) ⟨1151027, by rfl⟩ : syracuseStep 1534703 = 2302055) B2302055
theorem B1534847 : Blo 1020604 1534847 := bstep (se 1 (by rfl) ⟨1151135, by rfl⟩ : syracuseStep 1534847 = 2302271) B2302271
theorem B1535519 : Blo 1020604 1535519 := bstep (se 1 (by rfl) ⟨1151639, by rfl⟩ : syracuseStep 1535519 = 2303279) B2303279
theorem B5172983 : Blo 1020604 5172983 := bstep (se 1 (by rfl) ⟨3879737, by rfl⟩ : syracuseStep 5172983 = 7759475) B7759475
theorem B1535753 : Blo 1020604 1535753 := bstep (se 2 (by rfl) ⟨575907, by rfl⟩ : syracuseStep 1535753 = 1151815) B1151815
theorem B11824987 : Blo 1020604 11824987 := bstep (se 1 (by rfl) ⟨8868740, by rfl⟩ : syracuseStep 11824987 = 17737481) B17737481
theorem B1536167 : Blo 1020604 1536167 := bstep (se 1 (by rfl) ⟨1152125, by rfl⟩ : syracuseStep 1536167 = 2304251) B2304251
theorem B29520125 : Blo 1020604 29520125 := bstep (se 3 (by rfl) ⟨5535023, by rfl⟩ : syracuseStep 29520125 = 11070047) B11070047
theorem B1536743 : Blo 1020604 1536743 := bstep (se 1 (by rfl) ⟨1152557, by rfl⟩ : syracuseStep 1536743 = 2305115) B2305115
theorem B99645187 : Blo 1020604 99645187 := bstep (se 1 (by rfl) ⟨74733890, by rfl⟩ : syracuseStep 99645187 = 149467781) B149467781
theorem B5535499 : Blo 1020604 5535499 := bstep (se 1 (by rfl) ⟨4151624, by rfl⟩ : syracuseStep 5535499 = 8303249) B8303249
theorem B2587423 : Blo 1020604 2587423 := bstep (se 1 (by rfl) ⟨1940567, by rfl⟩ : syracuseStep 2587423 = 3881135) B3881135
theorem B9829471 : Blo 1020604 9829471 := bstep (se 1 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 9829471 = 14744207) B14744207
theorem B5832161 : Blo 1020604 5832161 := bstep (se 2 (by rfl) ⟨2187060, by rfl⟩ : syracuseStep 5832161 = 4374121) B4374121
theorem B3112843 : Blo 1020604 3112843 := bstep (se 1 (by rfl) ⟨2334632, by rfl⟩ : syracuseStep 3112843 = 4669265) B4669265
theorem B2588719 : Blo 1020604 2588719 := bstep (se 1 (by rfl) ⟨1941539, by rfl⟩ : syracuseStep 2588719 = 3883079) B3883079
theorem B44892413 : Blo 1020604 44892413 := bstep (se 3 (by rfl) ⟨8417327, by rfl⟩ : syracuseStep 44892413 = 16834655) B16834655
theorem B2590015 : Blo 1020604 2590015 := bstep (se 1 (by rfl) ⟨1942511, by rfl⟩ : syracuseStep 2590015 = 3885023) B3885023
theorem B21006377 : Blo 1020604 21006377 := bstep (se 2 (by rfl) ⟨7877391, by rfl⟩ : syracuseStep 21006377 = 15754783) B15754783
theorem B2296475 : Blo 1020604 2296475 := bstep (se 1 (by rfl) ⟨1722356, by rfl⟩ : syracuseStep 2296475 = 3444713) B3444713
theorem B2297159 : Blo 1020604 2297159 := bstep (se 1 (by rfl) ⟨1722869, by rfl⟩ : syracuseStep 2297159 = 3445739) B3445739
theorem B2592233 : Blo 1020604 2592233 := bstep (se 2 (by rfl) ⟨972087, by rfl⟩ : syracuseStep 2592233 = 1944175) B1944175
theorem B18452063 : Blo 1020604 18452063 := bstep (se 1 (by rfl) ⟨13839047, by rfl⟩ : syracuseStep 18452063 = 27678095) B27678095
theorem B3444767 : Blo 1020604 3444767 := bstep (se 1 (by rfl) ⟨2583575, by rfl⟩ : syracuseStep 3444767 = 5167151) B5167151
theorem B2298095 : Blo 1020604 2298095 := bstep (se 1 (by rfl) ⟨1723571, by rfl⟩ : syracuseStep 2298095 = 3447143) B3447143
theorem B2593043 : Blo 1020604 2593043 := bstep (se 1 (by rfl) ⟨1944782, by rfl⟩ : syracuseStep 2593043 = 3889565) B3889565
theorem B4362655 : Blo 1020604 4362655 := bstep (se 1 (by rfl) ⟨3271991, by rfl⟩ : syracuseStep 4362655 = 6543983) B6543983
theorem B2298599 : Blo 1020604 2298599 := bstep (se 1 (by rfl) ⟨1723949, by rfl⟩ : syracuseStep 2298599 = 3447899) B3447899
theorem B1020699 : Blo 1020604 1020699 := bstep (se 1 (by rfl) ⟨765524, by rfl⟩ : syracuseStep 1020699 = 1531049) B1531049
theorem B1020743 : Blo 1020604 1020743 := bstep (se 1 (by rfl) ⟨765557, by rfl⟩ : syracuseStep 1020743 = 1531115) B1531115
theorem B2069455 : Blo 1020604 2069455 := bstep (se 1 (by rfl) ⟨1552091, by rfl⟩ : syracuseStep 2069455 = 3104183) B3104183
theorem B1021019 : Blo 1020604 1021019 := bstep (se 1 (by rfl) ⟨765764, by rfl⟩ : syracuseStep 1021019 = 1531529) B1531529
theorem B15766649 : Blo 1020604 15766649 := bstep (se 2 (by rfl) ⟨5912493, by rfl⟩ : syracuseStep 15766649 = 11824987) B11824987
theorem B1021723 : Blo 1020604 1021723 := bstep (se 1 (by rfl) ⟨766292, by rfl⟩ : syracuseStep 1021723 = 1532585) B1532585
theorem B44275679 : Blo 1020604 44275679 := bstep (se 1 (by rfl) ⟨33206759, by rfl⟩ : syracuseStep 44275679 = 66413519) B66413519
theorem B1022271 : Blo 1020604 1022271 := bstep (se 1 (by rfl) ⟨766703, by rfl⟩ : syracuseStep 1022271 = 1533407) B1533407
theorem B1022511 : Blo 1020604 1022511 := bstep (se 1 (by rfl) ⟨766883, by rfl⟩ : syracuseStep 1022511 = 1533767) B1533767
theorem B1940051 : Blo 1020604 1940051 := bstep (se 1 (by rfl) ⟨1455038, by rfl⟩ : syracuseStep 1940051 = 2910077) B2910077
theorem B1022619 : Blo 1020604 1022619 := bstep (se 1 (by rfl) ⟨766964, by rfl⟩ : syracuseStep 1022619 = 1533929) B1533929
theorem B1023003 : Blo 1020604 1023003 := bstep (se 1 (by rfl) ⟨767252, by rfl⟩ : syracuseStep 1023003 = 1534505) B1534505
theorem B1023039 : Blo 1020604 1023039 := bstep (se 1 (by rfl) ⟨767279, by rfl⟩ : syracuseStep 1023039 = 1534559) B1534559
theorem B1023135 : Blo 1020604 1023135 := bstep (se 1 (by rfl) ⟨767351, by rfl⟩ : syracuseStep 1023135 = 1534703) B1534703
theorem B1023231 : Blo 1020604 1023231 := bstep (se 1 (by rfl) ⟨767423, by rfl⟩ : syracuseStep 1023231 = 1534847) B1534847
theorem B7380665 : Blo 1020604 7380665 := bstep (se 2 (by rfl) ⟨2767749, by rfl⟩ : syracuseStep 7380665 = 5535499) B5535499
theorem B1023679 : Blo 1020604 1023679 := bstep (se 1 (by rfl) ⟨767759, by rfl⟩ : syracuseStep 1023679 = 1535519) B1535519
theorem B3448655 : Blo 1020604 3448655 := bstep (se 1 (by rfl) ⟨2586491, by rfl⟩ : syracuseStep 3448655 = 5172983) B5172983
theorem B1023835 : Blo 1020604 1023835 := bstep (se 1 (by rfl) ⟨767876, by rfl⟩ : syracuseStep 1023835 = 1535753) B1535753
theorem B1024111 : Blo 1020604 1024111 := bstep (se 1 (by rfl) ⟨768083, by rfl⟩ : syracuseStep 1024111 = 1536167) B1536167
theorem B1024495 : Blo 1020604 1024495 := bstep (se 1 (by rfl) ⟨768371, by rfl⟩ : syracuseStep 1024495 = 1536743) B1536743
theorem B3449897 : Blo 1020604 3449897 := bstep (se 2 (by rfl) ⟨1293711, by rfl⟩ : syracuseStep 3449897 = 2587423) B2587423
theorem B30287209 : Blo 1020604 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B3877217 : Blo 1020604 3877217 := bstep (se 2 (by rfl) ⟨1453956, by rfl⟩ : syracuseStep 3877217 = 2907913) B2907913
theorem B2304719 : Blo 1020604 2304719 := bstep (se 1 (by rfl) ⟨1728539, by rfl⟩ : syracuseStep 2304719 = 3457079) B3457079
theorem B2304935 : Blo 1020604 2304935 := bstep (se 1 (by rfl) ⟨1728701, by rfl⟩ : syracuseStep 2304935 = 3457403) B3457403
theorem B3452435 : Blo 1020604 3452435 := bstep (se 1 (by rfl) ⟨2589326, by rfl⟩ : syracuseStep 3452435 = 5178653) B5178653
theorem B31502027 : Blo 1020604 31502027 := bstep (se 1 (by rfl) ⟨23626520, by rfl⟩ : syracuseStep 31502027 = 47253041) B47253041
theorem B1454059 : Blo 1020604 1454059 := bstep (se 1 (by rfl) ⟨1090544, by rfl⟩ : syracuseStep 1454059 = 2181089) B2181089
theorem B4372703 : Blo 1020604 4372703 := bstep (se 1 (by rfl) ⟨3279527, by rfl⟩ : syracuseStep 4372703 = 6559055) B6559055
theorem B1293671 : Blo 1020604 1293671 := bstep (se 1 (by rfl) ⟨970253, by rfl⟩ : syracuseStep 1293671 = 1940507) B1940507
theorem B15713459 : Blo 1020604 15713459 := bstep (se 1 (by rfl) ⟨11785094, by rfl⟩ : syracuseStep 15713459 = 23570189) B23570189
theorem B35374391 : Blo 1020604 35374391 := bstep (se 1 (by rfl) ⟨26530793, by rfl⟩ : syracuseStep 35374391 = 53061587) B53061587
theorem B132860249 : Blo 1020604 132860249 := bstep (se 2 (by rfl) ⟨49822593, by rfl⟩ : syracuseStep 132860249 = 99645187) B99645187
theorem B19680083 : Blo 1020604 19680083 := bstep (se 1 (by rfl) ⟨14760062, by rfl⟩ : syracuseStep 19680083 = 29520125) B29520125
theorem B3888107 : Blo 1020604 3888107 := bstep (se 1 (by rfl) ⟨2916080, by rfl⟩ : syracuseStep 3888107 = 5832161) B5832161
theorem B4150457 : Blo 1020604 4150457 := bstep (se 2 (by rfl) ⟨1556421, by rfl⟩ : syracuseStep 4150457 = 3112843) B3112843
theorem B8738705 : Blo 1020604 8738705 := bstep (se 2 (by rfl) ⟨3277014, by rfl⟩ : syracuseStep 8738705 = 6554029) B6554029
theorem B2185967 : Blo 1020604 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B1530935 : Blo 1020604 1530935 := bstep (se 1 (by rfl) ⟨1148201, by rfl⟩ : syracuseStep 1530935 = 2296403) B2296403
theorem B1531583 : Blo 1020604 1531583 := bstep (se 1 (by rfl) ⟨1148687, by rfl⟩ : syracuseStep 1531583 = 2297375) B2297375
theorem B14737463 : Blo 1020604 14737463 := bstep (se 1 (by rfl) ⟨11053097, by rfl⟩ : syracuseStep 14737463 = 22106195) B22106195
theorem B9822707 : Blo 1020604 9822707 := bstep (se 1 (by rfl) ⟨7367030, by rfl⟩ : syracuseStep 9822707 = 14734061) B14734061
theorem B3793853 : Blo 1020604 3793853 := bstep (se 3 (by rfl) ⟨711347, by rfl⟩ : syracuseStep 3793853 = 1422695) B1422695
theorem B1533305 : Blo 1020604 1533305 := bstep (se 2 (by rfl) ⟨574989, by rfl⟩ : syracuseStep 1533305 = 1149979) B1149979
theorem B24897287 : Blo 1020604 24897287 := bstep (se 1 (by rfl) ⟨18672965, by rfl⟩ : syracuseStep 24897287 = 37345931) B37345931
theorem B2586107 : Blo 1020604 2586107 := bstep (se 1 (by rfl) ⟨1939580, by rfl⟩ : syracuseStep 2586107 = 3879161) B3879161
theorem B5176061 : Blo 1020604 5176061 := bstep (se 3 (by rfl) ⟨970511, by rfl⟩ : syracuseStep 5176061 = 1941023) B1941023
theorem B13105961 : Blo 1020604 13105961 := bstep (se 2 (by rfl) ⟨4914735, by rfl⟩ : syracuseStep 13105961 = 9829471) B9829471
theorem B88573499 : Blo 1020604 88573499 := bstep (se 1 (by rfl) ⟨66430124, by rfl⟩ : syracuseStep 88573499 = 132860249) B132860249
theorem B2296511 : Blo 1020604 2296511 := bstep (se 1 (by rfl) ⟨1722383, by rfl⟩ : syracuseStep 2296511 = 3444767) B3444767
theorem B2592071 : Blo 1020604 2592071 := bstep (se 1 (by rfl) ⟨1944053, by rfl⟩ : syracuseStep 2592071 = 3888107) B3888107
theorem B1020623 : Blo 1020604 1020623 := bstep (se 1 (by rfl) ⟨765467, by rfl⟩ : syracuseStep 1020623 = 1530935) B1530935
theorem B4920443 : Blo 1020604 4920443 := bstep (se 1 (by rfl) ⟨3690332, by rfl⟩ : syracuseStep 4920443 = 7380665) B7380665
theorem B1021055 : Blo 1020604 1021055 := bstep (se 1 (by rfl) ⟨765791, by rfl⟩ : syracuseStep 1021055 = 1531583) B1531583
theorem B2299103 : Blo 1020604 2299103 := bstep (se 1 (by rfl) ⟨1724327, by rfl⟩ : syracuseStep 2299103 = 3448655) B3448655
theorem B1938745 : Blo 1020604 1938745 := bstep (se 2 (by rfl) ⟨727029, by rfl⟩ : syracuseStep 1938745 = 1454059) B1454059
theorem B2529235 : Blo 1020604 2529235 := bstep (se 1 (by rfl) ⟨1896926, by rfl⟩ : syracuseStep 2529235 = 3793853) B3793853
theorem B2299931 : Blo 1020604 2299931 := bstep (se 1 (by rfl) ⟨1724948, by rfl⟩ : syracuseStep 2299931 = 3449897) B3449897
theorem B1022203 : Blo 1020604 1022203 := bstep (se 1 (by rfl) ⟨766652, by rfl⟩ : syracuseStep 1022203 = 1533305) B1533305
theorem B2759273 : Blo 1020604 2759273 := bstep (se 2 (by rfl) ⟨1034727, by rfl⟩ : syracuseStep 2759273 = 2069455) B2069455
theorem B2301623 : Blo 1020604 2301623 := bstep (se 1 (by rfl) ⟨1726217, by rfl⟩ : syracuseStep 2301623 = 3452435) B3452435
theorem B3449789 : Blo 1020604 3449789 := bstep (se 3 (by rfl) ⟨646835, by rfl⟩ : syracuseStep 3449789 = 1293671) B1293671
theorem B3450707 : Blo 1020604 3450707 := bstep (se 1 (by rfl) ⟨2588030, by rfl⟩ : syracuseStep 3450707 = 5176061) B5176061
theorem B3451625 : Blo 1020604 3451625 := bstep (se 2 (by rfl) ⟨1294359, by rfl⟩ : syracuseStep 3451625 = 2588719) B2588719
theorem B29928275 : Blo 1020604 29928275 := bstep (se 1 (by rfl) ⟨22446206, by rfl⟩ : syracuseStep 29928275 = 44892413) B44892413
theorem B14004251 : Blo 1020604 14004251 := bstep (se 1 (by rfl) ⟨10503188, by rfl⟩ : syracuseStep 14004251 = 21006377) B21006377
theorem B3453353 : Blo 1020604 3453353 := bstep (se 2 (by rfl) ⟨1295007, by rfl⟩ : syracuseStep 3453353 = 2590015) B2590015
theorem B40382945 : Blo 1020604 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B13120055 : Blo 1020604 13120055 := bstep (se 1 (by rfl) ⟨9840041, by rfl⟩ : syracuseStep 13120055 = 19680083) B19680083
theorem B12301375 : Blo 1020604 12301375 := bstep (se 1 (by rfl) ⟨9226031, by rfl⟩ : syracuseStep 12301375 = 18452063) B18452063
theorem B2766971 : Blo 1020604 2766971 := bstep (se 1 (by rfl) ⟨2075228, by rfl⟩ : syracuseStep 2766971 = 4150457) B4150457
theorem B5816873 : Blo 1020604 5816873 := bstep (se 2 (by rfl) ⟨2181327, by rfl⟩ : syracuseStep 5816873 = 4362655) B4362655
theorem B16598191 : Blo 1020604 16598191 := bstep (se 1 (by rfl) ⟨12448643, by rfl⟩ : syracuseStep 16598191 = 24897287) B24897287
theorem B1724071 : Blo 1020604 1724071 := bstep (se 1 (by rfl) ⟨1293053, by rfl⟩ : syracuseStep 1724071 = 2586107) B2586107
theorem B8737307 : Blo 1020604 8737307 := bstep (se 1 (by rfl) ⟨6552980, by rfl⟩ : syracuseStep 8737307 = 13105961) B13105961
theorem B10475639 : Blo 1020604 10475639 := bstep (se 1 (by rfl) ⟨7856729, by rfl⟩ : syracuseStep 10475639 = 15713459) B15713459
theorem B23582927 : Blo 1020604 23582927 := bstep (se 1 (by rfl) ⟨17687195, by rfl⟩ : syracuseStep 23582927 = 35374391) B35374391
theorem B1530983 : Blo 1020604 1530983 := bstep (se 1 (by rfl) ⟨1148237, by rfl⟩ : syracuseStep 1530983 = 2296475) B2296475
theorem B1531439 : Blo 1020604 1531439 := bstep (se 1 (by rfl) ⟨1148579, by rfl⟩ : syracuseStep 1531439 = 2297159) B2297159
theorem B1728155 : Blo 1020604 1728155 := bstep (se 1 (by rfl) ⟨1296116, by rfl⟩ : syracuseStep 1728155 = 2592233) B2592233
theorem B1532063 : Blo 1020604 1532063 := bstep (se 1 (by rfl) ⟨1149047, by rfl⟩ : syracuseStep 1532063 = 2298095) B2298095
theorem B1728695 : Blo 1020604 1728695 := bstep (se 1 (by rfl) ⟨1296521, by rfl⟩ : syracuseStep 1728695 = 2593043) B2593043
theorem B1532399 : Blo 1020604 1532399 := bstep (se 1 (by rfl) ⟨1149299, by rfl⟩ : syracuseStep 1532399 = 2298599) B2298599
theorem B10511099 : Blo 1020604 10511099 := bstep (se 1 (by rfl) ⟨7883324, by rfl⟩ : syracuseStep 10511099 = 15766649) B15766649
theorem B5825803 : Blo 1020604 5825803 := bstep (se 1 (by rfl) ⟨4369352, by rfl⟩ : syracuseStep 5825803 = 8738705) B8738705
theorem B29517119 : Blo 1020604 29517119 := bstep (se 1 (by rfl) ⟨22137839, by rfl⟩ : syracuseStep 29517119 = 44275679) B44275679
theorem B9824975 : Blo 1020604 9824975 := bstep (se 1 (by rfl) ⟨7368731, by rfl⟩ : syracuseStep 9824975 = 14737463) B14737463
theorem B6548471 : Blo 1020604 6548471 := bstep (se 1 (by rfl) ⟨4911353, by rfl⟩ : syracuseStep 6548471 = 9822707) B9822707
theorem B5173469 : Blo 1020604 5173469 := bstep (se 3 (by rfl) ⟨970025, by rfl⟩ : syracuseStep 5173469 = 1940051) B1940051
theorem B2584811 : Blo 1020604 2584811 := bstep (se 1 (by rfl) ⟨1938608, by rfl⟩ : syracuseStep 2584811 = 3877217) B3877217
theorem B1536479 : Blo 1020604 1536479 := bstep (se 1 (by rfl) ⟨1152359, by rfl⟩ : syracuseStep 1536479 = 2304719) B2304719
theorem B1536623 : Blo 1020604 1536623 := bstep (se 1 (by rfl) ⟨1152467, by rfl⟩ : syracuseStep 1536623 = 2304935) B2304935
theorem B5829245 : Blo 1020604 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B21001351 : Blo 1020604 21001351 := bstep (se 1 (by rfl) ⟨15751013, by rfl⟩ : syracuseStep 21001351 = 31502027) B31502027
theorem B2915135 : Blo 1020604 2915135 := bstep (se 1 (by rfl) ⟨2186351, by rfl⟩ : syracuseStep 2915135 = 4372703) B4372703
theorem B59048999 : Blo 1020604 59048999 := bstep (se 1 (by rfl) ⟨44286749, by rfl⟩ : syracuseStep 59048999 = 88573499) B88573499
theorem B7767737 : Blo 1020604 7767737 := bstep (se 2 (by rfl) ⟨2912901, by rfl⟩ : syracuseStep 7767737 = 5825803) B5825803
theorem B3280295 : Blo 1020604 3280295 := bstep (se 1 (by rfl) ⟨2460221, by rfl⟩ : syracuseStep 3280295 = 4920443) B4920443
theorem B6983759 : Blo 1020604 6983759 := bstep (se 1 (by rfl) ⟨5237819, by rfl⟩ : syracuseStep 6983759 = 10475639) B10475639
theorem B1839515 : Blo 1020604 1839515 := bstep (se 1 (by rfl) ⟨1379636, by rfl⟩ : syracuseStep 1839515 = 2759273) B2759273
theorem B1020655 : Blo 1020604 1020655 := bstep (se 1 (by rfl) ⟨765491, by rfl⟩ : syracuseStep 1020655 = 1530983) B1530983
theorem B2298761 : Blo 1020604 2298761 := bstep (se 2 (by rfl) ⟨862035, by rfl⟩ : syracuseStep 2298761 = 1724071) B1724071
theorem B1020959 : Blo 1020604 1020959 := bstep (se 1 (by rfl) ⟨765719, by rfl⟩ : syracuseStep 1020959 = 1531439) B1531439
theorem B1152103 : Blo 1020604 1152103 := bstep (se 1 (by rfl) ⟨864077, by rfl⟩ : syracuseStep 1152103 = 1728155) B1728155
theorem B1021375 : Blo 1020604 1021375 := bstep (se 1 (by rfl) ⟨766031, by rfl⟩ : syracuseStep 1021375 = 1532063) B1532063
theorem B1152463 : Blo 1020604 1152463 := bstep (se 1 (by rfl) ⟨864347, by rfl⟩ : syracuseStep 1152463 = 1728695) B1728695
theorem B7378589 : Blo 1020604 7378589 := bstep (se 3 (by rfl) ⟨1383485, by rfl⟩ : syracuseStep 7378589 = 2766971) B2766971
theorem B1021599 : Blo 1020604 1021599 := bstep (se 1 (by rfl) ⟨766199, by rfl⟩ : syracuseStep 1021599 = 1532399) B1532399
theorem B2299859 : Blo 1020604 2299859 := bstep (se 1 (by rfl) ⟨1724894, by rfl⟩ : syracuseStep 2299859 = 3449789) B3449789
theorem B2300471 : Blo 1020604 2300471 := bstep (se 1 (by rfl) ⟨1725353, by rfl⟩ : syracuseStep 2300471 = 3450707) B3450707
theorem B2301083 : Blo 1020604 2301083 := bstep (se 1 (by rfl) ⟨1725812, by rfl⟩ : syracuseStep 2301083 = 3451625) B3451625
theorem B4365647 : Blo 1020604 4365647 := bstep (se 1 (by rfl) ⟨3274235, by rfl⟩ : syracuseStep 4365647 = 6548471) B6548471
theorem B3448979 : Blo 1020604 3448979 := bstep (se 1 (by rfl) ⟨2586734, by rfl⟩ : syracuseStep 3448979 = 5173469) B5173469
theorem B2302235 : Blo 1020604 2302235 := bstep (se 1 (by rfl) ⟨1726676, by rfl⟩ : syracuseStep 2302235 = 3453353) B3453353
theorem B1024319 : Blo 1020604 1024319 := bstep (se 1 (by rfl) ⟨768239, by rfl⟩ : syracuseStep 1024319 = 1536479) B1536479
theorem B1024415 : Blo 1020604 1024415 := bstep (se 1 (by rfl) ⟨768311, by rfl⟩ : syracuseStep 1024415 = 1536623) B1536623
theorem B1943423 : Blo 1020604 1943423 := bstep (se 1 (by rfl) ⟨1457567, by rfl⟩ : syracuseStep 1943423 = 2915135) B2915135
theorem B3877915 : Blo 1020604 3877915 := bstep (se 1 (by rfl) ⟨2908436, by rfl⟩ : syracuseStep 3877915 = 5816873) B5816873
theorem B22130921 : Blo 1020604 22130921 := bstep (se 2 (by rfl) ⟨8299095, by rfl⟩ : syracuseStep 22130921 = 16598191) B16598191
theorem B19678079 : Blo 1020604 19678079 := bstep (se 1 (by rfl) ⟨14758559, by rfl⟩ : syracuseStep 19678079 = 29517119) B29517119
theorem B16401833 : Blo 1020604 16401833 := bstep (se 2 (by rfl) ⟨6150687, by rfl⟩ : syracuseStep 16401833 = 12301375) B12301375
theorem B28001801 : Blo 1020604 28001801 := bstep (se 2 (by rfl) ⟨10500675, by rfl⟩ : syracuseStep 28001801 = 21001351) B21001351
theorem B1723207 : Blo 1020604 1723207 := bstep (se 1 (by rfl) ⟨1292405, by rfl⟩ : syracuseStep 1723207 = 2584811) B2584811
theorem B26921963 : Blo 1020604 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B3886163 : Blo 1020604 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B1531007 : Blo 1020604 1531007 := bstep (se 1 (by rfl) ⟨1148255, by rfl⟩ : syracuseStep 1531007 = 2296511) B2296511
theorem B1728047 : Blo 1020604 1728047 := bstep (se 1 (by rfl) ⟨1296035, by rfl⟩ : syracuseStep 1728047 = 2592071) B2592071
theorem B5824871 : Blo 1020604 5824871 := bstep (se 1 (by rfl) ⟨4368653, by rfl⟩ : syracuseStep 5824871 = 8737307) B8737307
theorem B1532735 : Blo 1020604 1532735 := bstep (se 1 (by rfl) ⟨1149551, by rfl⟩ : syracuseStep 1532735 = 2299103) B2299103
theorem B1533287 : Blo 1020604 1533287 := bstep (se 1 (by rfl) ⟨1149965, by rfl⟩ : syracuseStep 1533287 = 2299931) B2299931
theorem B15721951 : Blo 1020604 15721951 := bstep (se 1 (by rfl) ⟨11791463, by rfl⟩ : syracuseStep 15721951 = 23582927) B23582927
theorem B1534415 : Blo 1020604 1534415 := bstep (se 1 (by rfl) ⟨1150811, by rfl⟩ : syracuseStep 1534415 = 2301623) B2301623
theorem B7007399 : Blo 1020604 7007399 := bstep (se 1 (by rfl) ⟨5255549, by rfl⟩ : syracuseStep 7007399 = 10511099) B10511099
theorem B2584993 : Blo 1020604 2584993 := bstep (se 2 (by rfl) ⟨969372, by rfl⟩ : syracuseStep 2584993 = 1938745) B1938745
theorem B6549983 : Blo 1020604 6549983 := bstep (se 1 (by rfl) ⟨4912487, by rfl⟩ : syracuseStep 6549983 = 9824975) B9824975
theorem B19952183 : Blo 1020604 19952183 := bstep (se 1 (by rfl) ⟨14964137, by rfl⟩ : syracuseStep 19952183 = 29928275) B29928275
theorem B3372313 : Blo 1020604 3372313 := bstep (se 2 (by rfl) ⟨1264617, by rfl⟩ : syracuseStep 3372313 = 2529235) B2529235
theorem B9336167 : Blo 1020604 9336167 := bstep (se 1 (by rfl) ⟨7002125, by rfl⟩ : syracuseStep 9336167 = 14004251) B14004251
theorem B8746703 : Blo 1020604 8746703 := bstep (se 1 (by rfl) ⟨6560027, by rfl⟩ : syracuseStep 8746703 = 13120055) B13120055
theorem B5178491 : Blo 1020604 5178491 := bstep (se 1 (by rfl) ⟨3883868, by rfl⟩ : syracuseStep 5178491 = 7767737) B7767737
theorem B2590775 : Blo 1020604 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B4655839 : Blo 1020604 4655839 := bstep (se 1 (by rfl) ⟨3491879, by rfl⟩ : syracuseStep 4655839 = 6983759) B6983759
theorem B2297609 : Blo 1020604 2297609 := bstep (se 2 (by rfl) ⟨861603, by rfl⟩ : syracuseStep 2297609 = 1723207) B1723207
theorem B4919059 : Blo 1020604 4919059 := bstep (se 1 (by rfl) ⟨3689294, by rfl⟩ : syracuseStep 4919059 = 7378589) B7378589
theorem B174952885 : Blo 1020604 174952885 := bstep (se 5 (by rfl) ⟨8200916, by rfl⟩ : syracuseStep 174952885 = 16401833) B16401833
theorem B1020671 : Blo 1020604 1020671 := bstep (se 1 (by rfl) ⟨765503, by rfl⟩ : syracuseStep 1020671 = 1531007) B1531007
theorem B1152031 : Blo 1020604 1152031 := bstep (se 1 (by rfl) ⟨864023, by rfl⟩ : syracuseStep 1152031 = 1728047) B1728047
theorem B2299319 : Blo 1020604 2299319 := bstep (se 1 (by rfl) ⟨1724489, by rfl⟩ : syracuseStep 2299319 = 3448979) B3448979
theorem B1021823 : Blo 1020604 1021823 := bstep (se 1 (by rfl) ⟨766367, by rfl⟩ : syracuseStep 1021823 = 1532735) B1532735
theorem B3446657 : Blo 1020604 3446657 := bstep (se 2 (by rfl) ⟨1292496, by rfl⟩ : syracuseStep 3446657 = 2584993) B2584993
theorem B1022191 : Blo 1020604 1022191 := bstep (se 1 (by rfl) ⟨766643, by rfl⟩ : syracuseStep 1022191 = 1533287) B1533287
theorem B1022943 : Blo 1020604 1022943 := bstep (se 1 (by rfl) ⟨767207, by rfl⟩ : syracuseStep 1022943 = 1534415) B1534415
theorem B4496417 : Blo 1020604 4496417 := bstep (se 2 (by rfl) ⟨1686156, by rfl⟩ : syracuseStep 4496417 = 3372313) B3372313
theorem B14753947 : Blo 1020604 14753947 := bstep (se 1 (by rfl) ⟨11065460, by rfl⟩ : syracuseStep 14753947 = 22130921) B22130921
theorem B4366655 : Blo 1020604 4366655 := bstep (se 1 (by rfl) ⟨3274991, by rfl⟩ : syracuseStep 4366655 = 6549983) B6549983
theorem B13118719 : Blo 1020604 13118719 := bstep (se 1 (by rfl) ⟨9839039, by rfl⟩ : syracuseStep 13118719 = 19678079) B19678079
theorem B39365999 : Blo 1020604 39365999 := bstep (se 1 (by rfl) ⟨29524499, by rfl⟩ : syracuseStep 39365999 = 59048999) B59048999
theorem B3883247 : Blo 1020604 3883247 := bstep (se 1 (by rfl) ⟨2912435, by rfl⟩ : syracuseStep 3883247 = 5824871) B5824871
theorem B1295615 : Blo 1020604 1295615 := bstep (se 1 (by rfl) ⟨971711, by rfl⟩ : syracuseStep 1295615 = 1943423) B1943423
theorem B4671599 : Blo 1020604 4671599 := bstep (se 1 (by rfl) ⟨3503699, by rfl⟩ : syracuseStep 4671599 = 7007399) B7007399
theorem B18667867 : Blo 1020604 18667867 := bstep (se 1 (by rfl) ⟨14000900, by rfl⟩ : syracuseStep 18667867 = 28001801) B28001801
theorem B4905373 : Blo 1020604 4905373 := bstep (se 3 (by rfl) ⟨919757, by rfl⟩ : syracuseStep 4905373 = 1839515) B1839515
theorem B20962601 : Blo 1020604 20962601 := bstep (se 2 (by rfl) ⟨7860975, by rfl⟩ : syracuseStep 20962601 = 15721951) B15721951
theorem B17947975 : Blo 1020604 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B1532507 : Blo 1020604 1532507 := bstep (se 1 (by rfl) ⟨1149380, by rfl⟩ : syracuseStep 1532507 = 2298761) B2298761
theorem B1533239 : Blo 1020604 1533239 := bstep (se 1 (by rfl) ⟨1149929, by rfl⟩ : syracuseStep 1533239 = 2299859) B2299859
theorem B5170553 : Blo 1020604 5170553 := bstep (se 2 (by rfl) ⟨1938957, by rfl⟩ : syracuseStep 5170553 = 3877915) B3877915
theorem B1533647 : Blo 1020604 1533647 := bstep (se 1 (by rfl) ⟨1150235, by rfl⟩ : syracuseStep 1533647 = 2300471) B2300471
theorem B1534055 : Blo 1020604 1534055 := bstep (se 1 (by rfl) ⟨1150541, by rfl⟩ : syracuseStep 1534055 = 2301083) B2301083
theorem B2910431 : Blo 1020604 2910431 := bstep (se 1 (by rfl) ⟨2182823, by rfl⟩ : syracuseStep 2910431 = 4365647) B4365647
theorem B1534823 : Blo 1020604 1534823 := bstep (se 1 (by rfl) ⟨1151117, by rfl⟩ : syracuseStep 1534823 = 2302235) B2302235
theorem B1536137 : Blo 1020604 1536137 := bstep (se 2 (by rfl) ⟨576051, by rfl⟩ : syracuseStep 1536137 = 1152103) B1152103
theorem B1536617 : Blo 1020604 1536617 := bstep (se 2 (by rfl) ⟨576231, by rfl⟩ : syracuseStep 1536617 = 1152463) B1152463
theorem B13301455 : Blo 1020604 13301455 := bstep (se 1 (by rfl) ⟨9976091, by rfl⟩ : syracuseStep 13301455 = 19952183) B19952183
theorem B6224111 : Blo 1020604 6224111 := bstep (se 1 (by rfl) ⟨4668083, by rfl⟩ : syracuseStep 6224111 = 9336167) B9336167
theorem B8747453 : Blo 1020604 8747453 := bstep (se 3 (by rfl) ⟨1640147, by rfl⟩ : syracuseStep 8747453 = 3280295) B3280295
theorem B5831135 : Blo 1020604 5831135 := bstep (se 1 (by rfl) ⟨4373351, by rfl⟩ : syracuseStep 5831135 = 8746703) B8746703
theorem B2588831 : Blo 1020604 2588831 := bstep (se 1 (by rfl) ⟨1941623, by rfl⟩ : syracuseStep 2588831 = 3883247) B3883247
theorem B2297771 : Blo 1020604 2297771 := bstep (se 1 (by rfl) ⟨1723328, by rfl⟩ : syracuseStep 2297771 = 3446657) B3446657
theorem B6558745 : Blo 1020604 6558745 := bstep (se 2 (by rfl) ⟨2459529, by rfl⟩ : syracuseStep 6558745 = 4919059) B4919059
theorem B12457597 : Blo 1020604 12457597 := bstep (se 3 (by rfl) ⟨2335799, by rfl⟩ : syracuseStep 12457597 = 4671599) B4671599
theorem B1021671 : Blo 1020604 1021671 := bstep (se 1 (by rfl) ⟨766253, by rfl⟩ : syracuseStep 1021671 = 1532507) B1532507
theorem B1022159 : Blo 1020604 1022159 := bstep (se 1 (by rfl) ⟨766619, by rfl⟩ : syracuseStep 1022159 = 1533239) B1533239
theorem B3447035 : Blo 1020604 3447035 := bstep (se 1 (by rfl) ⟨2585276, by rfl⟩ : syracuseStep 3447035 = 5170553) B5170553
theorem B1022431 : Blo 1020604 1022431 := bstep (se 1 (by rfl) ⟨766823, by rfl⟩ : syracuseStep 1022431 = 1533647) B1533647
theorem B1022703 : Blo 1020604 1022703 := bstep (se 1 (by rfl) ⟨767027, by rfl⟩ : syracuseStep 1022703 = 1534055) B1534055
theorem B1940287 : Blo 1020604 1940287 := bstep (se 1 (by rfl) ⟨1455215, by rfl⟩ : syracuseStep 1940287 = 2910431) B2910431
theorem B1023215 : Blo 1020604 1023215 := bstep (se 1 (by rfl) ⟨767411, by rfl⟩ : syracuseStep 1023215 = 1534823) B1534823
theorem B17735273 : Blo 1020604 17735273 := bstep (se 2 (by rfl) ⟨6650727, by rfl⟩ : syracuseStep 17735273 = 13301455) B13301455
theorem B1024091 : Blo 1020604 1024091 := bstep (se 1 (by rfl) ⟨768068, by rfl⟩ : syracuseStep 1024091 = 1536137) B1536137
theorem B1024411 : Blo 1020604 1024411 := bstep (se 1 (by rfl) ⟨768308, by rfl⟩ : syracuseStep 1024411 = 1536617) B1536617
theorem B23930633 : Blo 1020604 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B19671929 : Blo 1020604 19671929 := bstep (se 2 (by rfl) ⟨7376973, by rfl⟩ : syracuseStep 19671929 = 14753947) B14753947
theorem B3452327 : Blo 1020604 3452327 := bstep (se 1 (by rfl) ⟨2589245, by rfl⟩ : syracuseStep 3452327 = 5178491) B5178491
theorem B3454973 : Blo 1020604 3454973 := bstep (se 3 (by rfl) ⟨647807, by rfl⟩ : syracuseStep 3454973 = 1295615) B1295615
theorem B6207785 : Blo 1020604 6207785 := bstep (se 2 (by rfl) ⟨2327919, by rfl⟩ : syracuseStep 6207785 = 4655839) B4655839
theorem B2997611 : Blo 1020604 2997611 := bstep (se 1 (by rfl) ⟨2248208, by rfl⟩ : syracuseStep 2997611 = 4496417) B4496417
theorem B13975067 : Blo 1020604 13975067 := bstep (se 1 (by rfl) ⟨10481300, by rfl⟩ : syracuseStep 13975067 = 20962601) B20962601
theorem B24890489 : Blo 1020604 24890489 := bstep (se 2 (by rfl) ⟨9333933, by rfl⟩ : syracuseStep 24890489 = 18667867) B18667867
theorem B6540497 : Blo 1020604 6540497 := bstep (se 2 (by rfl) ⟨2452686, by rfl⟩ : syracuseStep 6540497 = 4905373) B4905373
theorem B4149407 : Blo 1020604 4149407 := bstep (se 1 (by rfl) ⟨3112055, by rfl⟩ : syracuseStep 4149407 = 6224111) B6224111
theorem B3887423 : Blo 1020604 3887423 := bstep (se 1 (by rfl) ⟨2915567, by rfl⟩ : syracuseStep 3887423 = 5831135) B5831135
theorem B1727183 : Blo 1020604 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B1531739 : Blo 1020604 1531739 := bstep (se 1 (by rfl) ⟨1148804, by rfl⟩ : syracuseStep 1531739 = 2297609) B2297609
theorem B1532879 : Blo 1020604 1532879 := bstep (se 1 (by rfl) ⟨1149659, by rfl⟩ : syracuseStep 1532879 = 2299319) B2299319
theorem B17491625 : Blo 1020604 17491625 := bstep (se 2 (by rfl) ⟨6559359, by rfl⟩ : syracuseStep 17491625 = 13118719) B13118719
theorem B2911103 : Blo 1020604 2911103 := bstep (se 1 (by rfl) ⟨2183327, by rfl⟩ : syracuseStep 2911103 = 4366655) B4366655
theorem B233270513 : Blo 1020604 233270513 := bstep (se 2 (by rfl) ⟨87476442, by rfl⟩ : syracuseStep 233270513 = 174952885) B174952885
theorem B1536041 : Blo 1020604 1536041 := bstep (se 2 (by rfl) ⟨576015, by rfl⟩ : syracuseStep 1536041 = 1152031) B1152031
theorem B26243999 : Blo 1020604 26243999 := bstep (se 1 (by rfl) ⟨19682999, by rfl⟩ : syracuseStep 26243999 = 39365999) B39365999
theorem B5831635 : Blo 1020604 5831635 := bstep (se 1 (by rfl) ⟨4373726, by rfl⟩ : syracuseStep 5831635 = 8747453) B8747453
theorem B4360331 : Blo 1020604 4360331 := bstep (se 1 (by rfl) ⟨3270248, by rfl⟩ : syracuseStep 4360331 = 6540497) B6540497
theorem B2591615 : Blo 1020604 2591615 := bstep (se 1 (by rfl) ⟨1943711, by rfl⟩ : syracuseStep 2591615 = 3887423) B3887423
theorem B2298023 : Blo 1020604 2298023 := bstep (se 1 (by rfl) ⟨1723517, by rfl⟩ : syracuseStep 2298023 = 3447035) B3447035
theorem B1151455 : Blo 1020604 1151455 := bstep (se 1 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 1151455 = 1727183) B1727183
theorem B1021159 : Blo 1020604 1021159 := bstep (se 1 (by rfl) ⟨765869, by rfl⟩ : syracuseStep 1021159 = 1531739) B1531739
theorem B1021919 : Blo 1020604 1021919 := bstep (se 1 (by rfl) ⟨766439, by rfl⟩ : syracuseStep 1021919 = 1532879) B1532879
theorem B13114619 : Blo 1020604 13114619 := bstep (se 1 (by rfl) ⟨9835964, by rfl⟩ : syracuseStep 13114619 = 19671929) B19671929
theorem B1940735 : Blo 1020604 1940735 := bstep (se 1 (by rfl) ⟨1455551, by rfl⟩ : syracuseStep 1940735 = 2911103) B2911103
theorem B2301551 : Blo 1020604 2301551 := bstep (se 1 (by rfl) ⟨1726163, by rfl⟩ : syracuseStep 2301551 = 3452327) B3452327
theorem B1024027 : Blo 1020604 1024027 := bstep (se 1 (by rfl) ⟨768020, by rfl⟩ : syracuseStep 1024027 = 1536041) B1536041
theorem B7775513 : Blo 1020604 7775513 := bstep (se 2 (by rfl) ⟨2915817, by rfl⟩ : syracuseStep 7775513 = 5831635) B5831635
theorem B2303315 : Blo 1020604 2303315 := bstep (se 1 (by rfl) ⟨1727486, by rfl⟩ : syracuseStep 2303315 = 3454973) B3454973
theorem B4138523 : Blo 1020604 4138523 := bstep (se 1 (by rfl) ⟨3103892, by rfl⟩ : syracuseStep 4138523 = 6207785) B6207785
theorem B9316711 : Blo 1020604 9316711 := bstep (se 1 (by rfl) ⟨6987533, by rfl⟩ : syracuseStep 9316711 = 13975067) B13975067
theorem B16593659 : Blo 1020604 16593659 := bstep (se 1 (by rfl) ⟨12445244, by rfl⟩ : syracuseStep 16593659 = 24890489) B24890489
theorem B2766271 : Blo 1020604 2766271 := bstep (se 1 (by rfl) ⟨2074703, by rfl⟩ : syracuseStep 2766271 = 4149407) B4149407
theorem B1725887 : Blo 1020604 1725887 := bstep (se 1 (by rfl) ⟨1294415, by rfl⟩ : syracuseStep 1725887 = 2588831) B2588831
theorem B1531847 : Blo 1020604 1531847 := bstep (se 1 (by rfl) ⟨1148885, by rfl⟩ : syracuseStep 1531847 = 2297771) B2297771
theorem B11823515 : Blo 1020604 11823515 := bstep (se 1 (by rfl) ⟨8867636, by rfl⟩ : syracuseStep 11823515 = 17735273) B17735273
theorem B11661083 : Blo 1020604 11661083 := bstep (se 1 (by rfl) ⟨8745812, by rfl⟩ : syracuseStep 11661083 = 17491625) B17491625
theorem B15953755 : Blo 1020604 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B8744993 : Blo 1020604 8744993 := bstep (se 2 (by rfl) ⟨3279372, by rfl⟩ : syracuseStep 8744993 = 6558745) B6558745
theorem B155513675 : Blo 1020604 155513675 := bstep (se 1 (by rfl) ⟨116635256, by rfl⟩ : syracuseStep 155513675 = 233270513) B233270513
theorem B16610129 : Blo 1020604 16610129 := bstep (se 2 (by rfl) ⟨6228798, by rfl⟩ : syracuseStep 16610129 = 12457597) B12457597
theorem B17495999 : Blo 1020604 17495999 := bstep (se 1 (by rfl) ⟨13121999, by rfl⟩ : syracuseStep 17495999 = 26243999) B26243999
theorem B2587049 : Blo 1020604 2587049 := bstep (se 2 (by rfl) ⟨970143, by rfl⟩ : syracuseStep 2587049 = 1940287) B1940287
theorem B1998407 : Blo 1020604 1998407 := bstep (se 1 (by rfl) ⟨1498805, by rfl⟩ : syracuseStep 1998407 = 2997611) B2997611
theorem B12422281 : Blo 1020604 12422281 := bstep (se 2 (by rfl) ⟨4658355, by rfl⟩ : syracuseStep 12422281 = 9316711) B9316711
theorem B1150591 : Blo 1020604 1150591 := bstep (se 1 (by rfl) ⟨862943, by rfl⟩ : syracuseStep 1150591 = 1725887) B1725887
theorem B21271673 : Blo 1020604 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B1021231 : Blo 1020604 1021231 := bstep (se 1 (by rfl) ⟨765923, by rfl⟩ : syracuseStep 1021231 = 1531847) B1531847
theorem B5183675 : Blo 1020604 5183675 := bstep (se 1 (by rfl) ⟨3887756, by rfl⟩ : syracuseStep 5183675 = 7775513) B7775513
theorem B2759015 : Blo 1020604 2759015 := bstep (se 1 (by rfl) ⟨2069261, by rfl⟩ : syracuseStep 2759015 = 4138523) B4138523
theorem B7774055 : Blo 1020604 7774055 := bstep (se 1 (by rfl) ⟨5830541, by rfl⟩ : syracuseStep 7774055 = 11661083) B11661083
theorem B1293823 : Blo 1020604 1293823 := bstep (se 1 (by rfl) ⟨970367, by rfl⟩ : syracuseStep 1293823 = 1940735) B1940735
theorem B7882343 : Blo 1020604 7882343 := bstep (se 1 (by rfl) ⟨5911757, by rfl⟩ : syracuseStep 7882343 = 11823515) B11823515
theorem B3688361 : Blo 1020604 3688361 := bstep (se 2 (by rfl) ⟨1383135, by rfl⟩ : syracuseStep 3688361 = 2766271) B2766271
theorem B11062439 : Blo 1020604 11062439 := bstep (se 1 (by rfl) ⟨8296829, by rfl⟩ : syracuseStep 11062439 = 16593659) B16593659
theorem B1724699 : Blo 1020604 1724699 := bstep (se 1 (by rfl) ⟨1293524, by rfl⟩ : syracuseStep 1724699 = 2587049) B2587049
theorem B1332271 : Blo 1020604 1332271 := bstep (se 1 (by rfl) ⟨999203, by rfl⟩ : syracuseStep 1332271 = 1998407) B1998407
theorem B1727743 : Blo 1020604 1727743 := bstep (se 1 (by rfl) ⟨1295807, by rfl⟩ : syracuseStep 1727743 = 2591615) B2591615
theorem B1532015 : Blo 1020604 1532015 := bstep (se 1 (by rfl) ⟨1149011, by rfl⟩ : syracuseStep 1532015 = 2298023) B2298023
theorem B8743079 : Blo 1020604 8743079 := bstep (se 1 (by rfl) ⟨6557309, by rfl⟩ : syracuseStep 8743079 = 13114619) B13114619
theorem B1534367 : Blo 1020604 1534367 := bstep (se 1 (by rfl) ⟨1150775, by rfl⟩ : syracuseStep 1534367 = 2301551) B2301551
theorem B11627549 : Blo 1020604 11627549 := bstep (se 3 (by rfl) ⟨2180165, by rfl⟩ : syracuseStep 11627549 = 4360331) B4360331
theorem B1535273 : Blo 1020604 1535273 := bstep (se 2 (by rfl) ⟨575727, by rfl⟩ : syracuseStep 1535273 = 1151455) B1151455
theorem B1535543 : Blo 1020604 1535543 := bstep (se 1 (by rfl) ⟨1151657, by rfl⟩ : syracuseStep 1535543 = 2303315) B2303315
theorem B5829995 : Blo 1020604 5829995 := bstep (se 1 (by rfl) ⟨4372496, by rfl⟩ : syracuseStep 5829995 = 8744993) B8744993
theorem B103675783 : Blo 1020604 103675783 := bstep (se 1 (by rfl) ⟨77756837, by rfl⟩ : syracuseStep 103675783 = 155513675) B155513675
theorem B11073419 : Blo 1020604 11073419 := bstep (se 1 (by rfl) ⟨8305064, by rfl⟩ : syracuseStep 11073419 = 16610129) B16610129
theorem B11663999 : Blo 1020604 11663999 := bstep (se 1 (by rfl) ⟨8747999, by rfl⟩ : syracuseStep 11663999 = 17495999) B17495999
theorem B2458907 : Blo 1020604 2458907 := bstep (se 1 (by rfl) ⟨1844180, by rfl⟩ : syracuseStep 2458907 = 3688361) B3688361
theorem B7374959 : Blo 1020604 7374959 := bstep (se 1 (by rfl) ⟨5531219, by rfl⟩ : syracuseStep 7374959 = 11062439) B11062439
theorem B1149799 : Blo 1020604 1149799 := bstep (se 1 (by rfl) ⟨862349, by rfl⟩ : syracuseStep 1149799 = 1724699) B1724699
theorem B56724461 : Blo 1020604 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B1839343 : Blo 1020604 1839343 := bstep (se 1 (by rfl) ⟨1379507, by rfl⟩ : syracuseStep 1839343 = 2759015) B2759015
theorem B5182703 : Blo 1020604 5182703 := bstep (se 1 (by rfl) ⟨3887027, by rfl⟩ : syracuseStep 5182703 = 7774055) B7774055
theorem B1021343 : Blo 1020604 1021343 := bstep (se 1 (by rfl) ⟨766007, by rfl⟩ : syracuseStep 1021343 = 1532015) B1532015
theorem B1776361 : Blo 1020604 1776361 := bstep (se 2 (by rfl) ⟨666135, by rfl⟩ : syracuseStep 1776361 = 1332271) B1332271
theorem B1022911 : Blo 1020604 1022911 := bstep (se 1 (by rfl) ⟨767183, by rfl⟩ : syracuseStep 1022911 = 1534367) B1534367
theorem B1023515 : Blo 1020604 1023515 := bstep (se 1 (by rfl) ⟨767636, by rfl⟩ : syracuseStep 1023515 = 1535273) B1535273
theorem B1023695 : Blo 1020604 1023695 := bstep (se 1 (by rfl) ⟨767771, by rfl⟩ : syracuseStep 1023695 = 1535543) B1535543
theorem B7382279 : Blo 1020604 7382279 := bstep (se 1 (by rfl) ⟨5536709, by rfl⟩ : syracuseStep 7382279 = 11073419) B11073419
theorem B2303657 : Blo 1020604 2303657 := bstep (se 2 (by rfl) ⟨863871, by rfl⟩ : syracuseStep 2303657 = 1727743) B1727743
theorem B7775999 : Blo 1020604 7775999 := bstep (se 1 (by rfl) ⟨5831999, by rfl⟩ : syracuseStep 7775999 = 11663999) B11663999
theorem B5254895 : Blo 1020604 5254895 := bstep (se 1 (by rfl) ⟨3941171, by rfl⟩ : syracuseStep 5254895 = 7882343) B7882343
theorem B3455783 : Blo 1020604 3455783 := bstep (se 1 (by rfl) ⟨2591837, by rfl⟩ : syracuseStep 3455783 = 5183675) B5183675
theorem B16563041 : Blo 1020604 16563041 := bstep (se 2 (by rfl) ⟨6211140, by rfl⟩ : syracuseStep 16563041 = 12422281) B12422281
theorem B7751699 : Blo 1020604 7751699 := bstep (se 1 (by rfl) ⟨5813774, by rfl⟩ : syracuseStep 7751699 = 11627549) B11627549
theorem B138234377 : Blo 1020604 138234377 := bstep (se 2 (by rfl) ⟨51837891, by rfl⟩ : syracuseStep 138234377 = 103675783) B103675783
theorem B3886663 : Blo 1020604 3886663 := bstep (se 1 (by rfl) ⟨2914997, by rfl⟩ : syracuseStep 3886663 = 5829995) B5829995
theorem B1725097 : Blo 1020604 1725097 := bstep (se 2 (by rfl) ⟨646911, by rfl⟩ : syracuseStep 1725097 = 1293823) B1293823
theorem B1534121 : Blo 1020604 1534121 := bstep (se 2 (by rfl) ⟨575295, by rfl⟩ : syracuseStep 1534121 = 1150591) B1150591
theorem B5828719 : Blo 1020604 5828719 := bstep (se 1 (by rfl) ⟨4371539, by rfl⟩ : syracuseStep 5828719 = 8743079) B8743079
theorem B1639271 : Blo 1020604 1639271 := bstep (se 1 (by rfl) ⟨1229453, by rfl⟩ : syracuseStep 1639271 = 2458907) B2458907
theorem B4916639 : Blo 1020604 4916639 := bstep (se 1 (by rfl) ⟨3687479, by rfl⟩ : syracuseStep 4916639 = 7374959) B7374959
theorem B37816307 : Blo 1020604 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B5182217 : Blo 1020604 5182217 := bstep (se 2 (by rfl) ⟨1943331, by rfl⟩ : syracuseStep 5182217 = 3886663) B3886663
theorem B7771625 : Blo 1020604 7771625 := bstep (se 2 (by rfl) ⟨2914359, by rfl⟩ : syracuseStep 7771625 = 5828719) B5828719
theorem B2300129 : Blo 1020604 2300129 := bstep (se 2 (by rfl) ⟨862548, by rfl⟩ : syracuseStep 2300129 = 1725097) B1725097
theorem B5183999 : Blo 1020604 5183999 := bstep (se 1 (by rfl) ⟨3887999, by rfl⟩ : syracuseStep 5183999 = 7775999) B7775999
theorem B1022747 : Blo 1020604 1022747 := bstep (se 1 (by rfl) ⟨767060, by rfl⟩ : syracuseStep 1022747 = 1534121) B1534121
theorem B2368481 : Blo 1020604 2368481 := bstep (se 2 (by rfl) ⟨888180, by rfl⟩ : syracuseStep 2368481 = 1776361) B1776361
theorem B2303855 : Blo 1020604 2303855 := bstep (se 1 (by rfl) ⟨1727891, by rfl⟩ : syracuseStep 2303855 = 3455783) B3455783
theorem B92156251 : Blo 1020604 92156251 := bstep (se 1 (by rfl) ⟨69117188, by rfl⟩ : syracuseStep 92156251 = 138234377) B138234377
theorem B3455135 : Blo 1020604 3455135 := bstep (se 1 (by rfl) ⟨2591351, by rfl⟩ : syracuseStep 3455135 = 5182703) B5182703
theorem B5167799 : Blo 1020604 5167799 := bstep (se 1 (by rfl) ⟨3875849, by rfl⟩ : syracuseStep 5167799 = 7751699) B7751699
theorem B19686077 : Blo 1020604 19686077 := bstep (se 3 (by rfl) ⟨3691139, by rfl⟩ : syracuseStep 19686077 = 7382279) B7382279
theorem B1533065 : Blo 1020604 1533065 := bstep (se 2 (by rfl) ⟨574899, by rfl⟩ : syracuseStep 1533065 = 1149799) B1149799
theorem B2452457 : Blo 1020604 2452457 := bstep (se 2 (by rfl) ⟨919671, by rfl⟩ : syracuseStep 2452457 = 1839343) B1839343
theorem B1535771 : Blo 1020604 1535771 := bstep (se 1 (by rfl) ⟨1151828, by rfl⟩ : syracuseStep 1535771 = 2303657) B2303657
theorem B3503263 : Blo 1020604 3503263 := bstep (se 1 (by rfl) ⟨2627447, by rfl⟩ : syracuseStep 3503263 = 5254895) B5254895
theorem B11042027 : Blo 1020604 11042027 := bstep (se 1 (by rfl) ⟨8281520, by rfl⟩ : syracuseStep 11042027 = 16563041) B16563041
theorem B3277759 : Blo 1020604 3277759 := bstep (se 1 (by rfl) ⟨2458319, by rfl⟩ : syracuseStep 3277759 = 4916639) B4916639
theorem B5181083 : Blo 1020604 5181083 := bstep (se 1 (by rfl) ⟨3885812, by rfl⟩ : syracuseStep 5181083 = 7771625) B7771625
theorem B3445199 : Blo 1020604 3445199 := bstep (se 1 (by rfl) ⟨2583899, by rfl⟩ : syracuseStep 3445199 = 5167799) B5167799
theorem B1022043 : Blo 1020604 1022043 := bstep (se 1 (by rfl) ⟨766532, by rfl⟩ : syracuseStep 1022043 = 1533065) B1533065
theorem B1023847 : Blo 1020604 1023847 := bstep (se 1 (by rfl) ⟨767885, by rfl⟩ : syracuseStep 1023847 = 1535771) B1535771
theorem B2303423 : Blo 1020604 2303423 := bstep (se 1 (by rfl) ⟨1727567, by rfl⟩ : syracuseStep 2303423 = 3455135) B3455135
theorem B1092847 : Blo 1020604 1092847 := bstep (se 1 (by rfl) ⟨819635, by rfl⟩ : syracuseStep 1092847 = 1639271) B1639271
theorem B25210871 : Blo 1020604 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B3454811 : Blo 1020604 3454811 := bstep (se 1 (by rfl) ⟨2591108, by rfl⟩ : syracuseStep 3454811 = 5182217) B5182217
theorem B3455999 : Blo 1020604 3455999 := bstep (se 1 (by rfl) ⟨2591999, by rfl⟩ : syracuseStep 3455999 = 5183999) B5183999
theorem B13124051 : Blo 1020604 13124051 := bstep (se 1 (by rfl) ⟨9843038, by rfl⟩ : syracuseStep 13124051 = 19686077) B19686077
theorem B4671017 : Blo 1020604 4671017 := bstep (se 2 (by rfl) ⟨1751631, by rfl⟩ : syracuseStep 4671017 = 3503263) B3503263
theorem B7361351 : Blo 1020604 7361351 := bstep (se 1 (by rfl) ⟨5521013, by rfl⟩ : syracuseStep 7361351 = 11042027) B11042027
theorem B1533419 : Blo 1020604 1533419 := bstep (se 1 (by rfl) ⟨1150064, by rfl⟩ : syracuseStep 1533419 = 2300129) B2300129
theorem B122875001 : Blo 1020604 122875001 := bstep (se 2 (by rfl) ⟨46078125, by rfl⟩ : syracuseStep 122875001 = 92156251) B92156251
theorem B1535903 : Blo 1020604 1535903 := bstep (se 1 (by rfl) ⟨1151927, by rfl⟩ : syracuseStep 1535903 = 2303855) B2303855
theorem B1634971 : Blo 1020604 1634971 := bstep (se 1 (by rfl) ⟨1226228, by rfl⟩ : syracuseStep 1634971 = 2452457) B2452457
theorem B25263797 : Blo 1020604 25263797 := bstep (se 5 (by rfl) ⟨1184240, by rfl⟩ : syracuseStep 25263797 = 2368481) B2368481
theorem B8749367 : Blo 1020604 8749367 := bstep (se 1 (by rfl) ⟨6562025, by rfl⟩ : syracuseStep 8749367 = 13124051) B13124051
theorem B3114011 : Blo 1020604 3114011 := bstep (se 1 (by rfl) ⟨2335508, by rfl⟩ : syracuseStep 3114011 = 4671017) B4671017
theorem B2296799 : Blo 1020604 2296799 := bstep (se 1 (by rfl) ⟨1722599, by rfl⟩ : syracuseStep 2296799 = 3445199) B3445199
theorem B1022279 : Blo 1020604 1022279 := bstep (se 1 (by rfl) ⟨766709, by rfl⟩ : syracuseStep 1022279 = 1533419) B1533419
theorem B1023935 : Blo 1020604 1023935 := bstep (se 1 (by rfl) ⟨767951, by rfl⟩ : syracuseStep 1023935 = 1535903) B1535903
theorem B2303207 : Blo 1020604 2303207 := bstep (se 1 (by rfl) ⟨1727405, by rfl⟩ : syracuseStep 2303207 = 3454811) B3454811
theorem B2303999 : Blo 1020604 2303999 := bstep (se 1 (by rfl) ⟨1727999, by rfl⟩ : syracuseStep 2303999 = 3455999) B3455999
theorem B4370345 : Blo 1020604 4370345 := bstep (se 2 (by rfl) ⟨1638879, by rfl⟩ : syracuseStep 4370345 = 3277759) B3277759
theorem B3454055 : Blo 1020604 3454055 := bstep (se 1 (by rfl) ⟨2590541, by rfl⟩ : syracuseStep 3454055 = 5181083) B5181083
theorem B1457129 : Blo 1020604 1457129 := bstep (se 2 (by rfl) ⟨546423, by rfl⟩ : syracuseStep 1457129 = 1092847) B1092847
theorem B2179961 : Blo 1020604 2179961 := bstep (se 2 (by rfl) ⟨817485, by rfl⟩ : syracuseStep 2179961 = 1634971) B1634971
theorem B4907567 : Blo 1020604 4907567 := bstep (se 1 (by rfl) ⟨3680675, by rfl⟩ : syracuseStep 4907567 = 7361351) B7361351
theorem B1535615 : Blo 1020604 1535615 := bstep (se 1 (by rfl) ⟨1151711, by rfl⟩ : syracuseStep 1535615 = 2303423) B2303423
theorem B81916667 : Blo 1020604 81916667 := bstep (se 1 (by rfl) ⟨61437500, by rfl⟩ : syracuseStep 81916667 = 122875001) B122875001
theorem B16807247 : Blo 1020604 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B67370125 : Blo 1020604 67370125 := bstep (se 3 (by rfl) ⟨12631898, by rfl⟩ : syracuseStep 67370125 = 25263797) B25263797
theorem B5832911 : Blo 1020604 5832911 := bstep (se 1 (by rfl) ⟨4374683, by rfl⟩ : syracuseStep 5832911 = 8749367) B8749367
theorem B1023743 : Blo 1020604 1023743 := bstep (se 1 (by rfl) ⟨767807, by rfl⟩ : syracuseStep 1023743 = 1535615) B1535615
theorem B2302703 : Blo 1020604 2302703 := bstep (se 1 (by rfl) ⟨1727027, by rfl⟩ : syracuseStep 2302703 = 3454055) B3454055
theorem B89826833 : Blo 1020604 89826833 := bstep (se 2 (by rfl) ⟨33685062, by rfl⟩ : syracuseStep 89826833 = 67370125) B67370125
theorem B1453307 : Blo 1020604 1453307 := bstep (se 1 (by rfl) ⟨1089980, by rfl⟩ : syracuseStep 1453307 = 2179961) B2179961
theorem B8304029 : Blo 1020604 8304029 := bstep (se 3 (by rfl) ⟨1557005, by rfl⟩ : syracuseStep 8304029 = 3114011) B3114011
theorem B3885677 : Blo 1020604 3885677 := bstep (se 3 (by rfl) ⟨728564, by rfl⟩ : syracuseStep 3885677 = 1457129) B1457129
theorem B54611111 : Blo 1020604 54611111 := bstep (se 1 (by rfl) ⟨40958333, by rfl⟩ : syracuseStep 54611111 = 81916667) B81916667
theorem B1531199 : Blo 1020604 1531199 := bstep (se 1 (by rfl) ⟨1148399, by rfl⟩ : syracuseStep 1531199 = 2296799) B2296799
theorem B3271711 : Blo 1020604 3271711 := bstep (se 1 (by rfl) ⟨2453783, by rfl⟩ : syracuseStep 3271711 = 4907567) B4907567
theorem B1535471 : Blo 1020604 1535471 := bstep (se 1 (by rfl) ⟨1151603, by rfl⟩ : syracuseStep 1535471 = 2303207) B2303207
theorem B1535999 : Blo 1020604 1535999 := bstep (se 1 (by rfl) ⟨1151999, by rfl⟩ : syracuseStep 1535999 = 2303999) B2303999
theorem B2913563 : Blo 1020604 2913563 := bstep (se 1 (by rfl) ⟨2185172, by rfl⟩ : syracuseStep 2913563 = 4370345) B4370345
theorem B11204831 : Blo 1020604 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B2590451 : Blo 1020604 2590451 := bstep (se 1 (by rfl) ⟨1942838, by rfl⟩ : syracuseStep 2590451 = 3885677) B3885677
theorem B36407407 : Blo 1020604 36407407 := bstep (se 1 (by rfl) ⟨27305555, by rfl⟩ : syracuseStep 36407407 = 54611111) B54611111
theorem B4362281 : Blo 1020604 4362281 := bstep (se 2 (by rfl) ⟨1635855, by rfl⟩ : syracuseStep 4362281 = 3271711) B3271711
theorem B1020799 : Blo 1020604 1020799 := bstep (se 1 (by rfl) ⟨765599, by rfl⟩ : syracuseStep 1020799 = 1531199) B1531199
theorem B1023647 : Blo 1020604 1023647 := bstep (se 1 (by rfl) ⟨767735, by rfl⟩ : syracuseStep 1023647 = 1535471) B1535471
theorem B1023999 : Blo 1020604 1023999 := bstep (se 1 (by rfl) ⟨767999, by rfl⟩ : syracuseStep 1023999 = 1535999) B1535999
theorem B3875485 : Blo 1020604 3875485 := bstep (se 3 (by rfl) ⟨726653, by rfl⟩ : syracuseStep 3875485 = 1453307) B1453307
theorem B1942375 : Blo 1020604 1942375 := bstep (se 1 (by rfl) ⟨1456781, by rfl⟩ : syracuseStep 1942375 = 2913563) B2913563
theorem B59884555 : Blo 1020604 59884555 := bstep (se 1 (by rfl) ⟨44913416, by rfl⟩ : syracuseStep 59884555 = 89826833) B89826833
theorem B3888607 : Blo 1020604 3888607 := bstep (se 1 (by rfl) ⟨2916455, by rfl⟩ : syracuseStep 3888607 = 5832911) B5832911
theorem B1535135 : Blo 1020604 1535135 := bstep (se 1 (by rfl) ⟨1151351, by rfl⟩ : syracuseStep 1535135 = 2302703) B2302703
theorem B5536019 : Blo 1020604 5536019 := bstep (se 1 (by rfl) ⟨4152014, by rfl⟩ : syracuseStep 5536019 = 8304029) B8304029
theorem B7469887 : Blo 1020604 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B2589833 : Blo 1020604 2589833 := bstep (se 2 (by rfl) ⟨971187, by rfl⟩ : syracuseStep 2589833 = 1942375) B1942375
theorem B5184809 : Blo 1020604 5184809 := bstep (se 2 (by rfl) ⟨1944303, by rfl⟩ : syracuseStep 5184809 = 3888607) B3888607
theorem B1023423 : Blo 1020604 1023423 := bstep (se 1 (by rfl) ⟨767567, by rfl⟩ : syracuseStep 1023423 = 1535135) B1535135
theorem B48543209 : Blo 1020604 48543209 := bstep (se 2 (by rfl) ⟨18203703, by rfl⟩ : syracuseStep 48543209 = 36407407) B36407407
theorem B3690679 : Blo 1020604 3690679 := bstep (se 1 (by rfl) ⟨2768009, by rfl⟩ : syracuseStep 3690679 = 5536019) B5536019
theorem B5167313 : Blo 1020604 5167313 := bstep (se 2 (by rfl) ⟨1937742, by rfl⟩ : syracuseStep 5167313 = 3875485) B3875485
theorem B1726967 : Blo 1020604 1726967 := bstep (se 1 (by rfl) ⟨1295225, by rfl⟩ : syracuseStep 1726967 = 2590451) B2590451
theorem B79846073 : Blo 1020604 79846073 := bstep (se 2 (by rfl) ⟨29942277, by rfl⟩ : syracuseStep 79846073 = 59884555) B59884555
theorem B2908187 : Blo 1020604 2908187 := bstep (se 1 (by rfl) ⟨2181140, by rfl⟩ : syracuseStep 2908187 = 4362281) B4362281
theorem B9959849 : Blo 1020604 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B3444875 : Blo 1020604 3444875 := bstep (se 1 (by rfl) ⟨2583656, by rfl⟩ : syracuseStep 3444875 = 5167313) B5167313
theorem B1151311 : Blo 1020604 1151311 := bstep (se 1 (by rfl) ⟨863483, by rfl⟩ : syracuseStep 1151311 = 1726967) B1726967
theorem B1938791 : Blo 1020604 1938791 := bstep (se 1 (by rfl) ⟨1454093, by rfl⟩ : syracuseStep 1938791 = 2908187) B2908187
theorem B4920905 : Blo 1020604 4920905 := bstep (se 2 (by rfl) ⟨1845339, by rfl⟩ : syracuseStep 4920905 = 3690679) B3690679
theorem B53230715 : Blo 1020604 53230715 := bstep (se 1 (by rfl) ⟨39923036, by rfl⟩ : syracuseStep 53230715 = 79846073) B79846073
theorem B3456539 : Blo 1020604 3456539 := bstep (se 1 (by rfl) ⟨2592404, by rfl⟩ : syracuseStep 3456539 = 5184809) B5184809
theorem B32362139 : Blo 1020604 32362139 := bstep (se 1 (by rfl) ⟨24271604, by rfl⟩ : syracuseStep 32362139 = 48543209) B48543209
theorem B6639899 : Blo 1020604 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B1726555 : Blo 1020604 1726555 := bstep (se 1 (by rfl) ⟨1294916, by rfl⟩ : syracuseStep 1726555 = 2589833) B2589833
theorem B2296583 : Blo 1020604 2296583 := bstep (se 1 (by rfl) ⟨1722437, by rfl⟩ : syracuseStep 2296583 = 3444875) B3444875
theorem B3280603 : Blo 1020604 3280603 := bstep (se 1 (by rfl) ⟨2460452, by rfl⟩ : syracuseStep 3280603 = 4920905) B4920905
theorem B2302073 : Blo 1020604 2302073 := bstep (se 2 (by rfl) ⟨863277, by rfl⟩ : syracuseStep 2302073 = 1726555) B1726555
theorem B2304359 : Blo 1020604 2304359 := bstep (se 1 (by rfl) ⟨1728269, by rfl⟩ : syracuseStep 2304359 = 3456539) B3456539
theorem B17706397 : Blo 1020604 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B21574759 : Blo 1020604 21574759 := bstep (se 1 (by rfl) ⟨16181069, by rfl⟩ : syracuseStep 21574759 = 32362139) B32362139
theorem B1292527 : Blo 1020604 1292527 := bstep (se 1 (by rfl) ⟨969395, by rfl⟩ : syracuseStep 1292527 = 1938791) B1938791
theorem B1535081 : Blo 1020604 1535081 := bstep (se 2 (by rfl) ⟨575655, by rfl⟩ : syracuseStep 1535081 = 1151311) B1151311
theorem B35487143 : Blo 1020604 35487143 := bstep (se 1 (by rfl) ⟨26615357, by rfl⟩ : syracuseStep 35487143 = 53230715) B53230715
theorem B1023387 : Blo 1020604 1023387 := bstep (se 1 (by rfl) ⟨767540, by rfl⟩ : syracuseStep 1023387 = 1535081) B1535081
theorem B23608529 : Blo 1020604 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B4374137 : Blo 1020604 4374137 := bstep (se 2 (by rfl) ⟨1640301, by rfl⟩ : syracuseStep 4374137 = 3280603) B3280603
theorem B1723369 : Blo 1020604 1723369 := bstep (se 2 (by rfl) ⟨646263, by rfl⟩ : syracuseStep 1723369 = 1292527) B1292527
theorem B1531055 : Blo 1020604 1531055 := bstep (se 1 (by rfl) ⟨1148291, by rfl⟩ : syracuseStep 1531055 = 2296583) B2296583
theorem B1534715 : Blo 1020604 1534715 := bstep (se 1 (by rfl) ⟨1151036, by rfl⟩ : syracuseStep 1534715 = 2302073) B2302073
theorem B28766345 : Blo 1020604 28766345 := bstep (se 2 (by rfl) ⟨10787379, by rfl⟩ : syracuseStep 28766345 = 21574759) B21574759
theorem B1536239 : Blo 1020604 1536239 := bstep (se 1 (by rfl) ⟨1152179, by rfl⟩ : syracuseStep 1536239 = 2304359) B2304359
theorem B23658095 : Blo 1020604 23658095 := bstep (se 1 (by rfl) ⟨17743571, by rfl⟩ : syracuseStep 23658095 = 35487143) B35487143
theorem B76710253 : Blo 1020604 76710253 := bstep (se 3 (by rfl) ⟨14383172, by rfl⟩ : syracuseStep 76710253 = 28766345) B28766345
theorem B2297825 : Blo 1020604 2297825 := bstep (se 2 (by rfl) ⟨861684, by rfl⟩ : syracuseStep 2297825 = 1723369) B1723369
theorem B1020703 : Blo 1020604 1020703 := bstep (se 1 (by rfl) ⟨765527, by rfl⟩ : syracuseStep 1020703 = 1531055) B1531055
theorem B1023143 : Blo 1020604 1023143 := bstep (se 1 (by rfl) ⟨767357, by rfl⟩ : syracuseStep 1023143 = 1534715) B1534715
theorem B1024159 : Blo 1020604 1024159 := bstep (se 1 (by rfl) ⟨768119, by rfl⟩ : syracuseStep 1024159 = 1536239) B1536239
theorem B63088253 : Blo 1020604 63088253 := bstep (se 3 (by rfl) ⟨11829047, by rfl⟩ : syracuseStep 63088253 = 23658095) B23658095
theorem B15739019 : Blo 1020604 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B2916091 : Blo 1020604 2916091 := bstep (se 1 (by rfl) ⟨2187068, by rfl⟩ : syracuseStep 2916091 = 4374137) B4374137
theorem B10492679 : Blo 1020604 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B102280337 : Blo 1020604 102280337 := bstep (se 2 (by rfl) ⟨38355126, by rfl⟩ : syracuseStep 102280337 = 76710253) B76710253
theorem B42058835 : Blo 1020604 42058835 := bstep (se 1 (by rfl) ⟨31544126, by rfl⟩ : syracuseStep 42058835 = 63088253) B63088253
theorem B3888121 : Blo 1020604 3888121 := bstep (se 2 (by rfl) ⟨1458045, by rfl⟩ : syracuseStep 3888121 = 2916091) B2916091
theorem B1531883 : Blo 1020604 1531883 := bstep (se 1 (by rfl) ⟨1148912, by rfl⟩ : syracuseStep 1531883 = 2297825) B2297825
theorem B1021255 : Blo 1020604 1021255 := bstep (se 1 (by rfl) ⟨765941, by rfl⟩ : syracuseStep 1021255 = 1531883) B1531883
theorem B5184161 : Blo 1020604 5184161 := bstep (se 2 (by rfl) ⟨1944060, by rfl⟩ : syracuseStep 5184161 = 3888121) B3888121
theorem B6995119 : Blo 1020604 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B28039223 : Blo 1020604 28039223 := bstep (se 1 (by rfl) ⟨21029417, by rfl⟩ : syracuseStep 28039223 = 42058835) B42058835
theorem B68186891 : Blo 1020604 68186891 := bstep (se 1 (by rfl) ⟨51140168, by rfl⟩ : syracuseStep 68186891 = 102280337) B102280337
theorem B181831709 : Blo 1020604 181831709 := bstep (se 3 (by rfl) ⟨34093445, by rfl⟩ : syracuseStep 181831709 = 68186891) B68186891
theorem B3456107 : Blo 1020604 3456107 := bstep (se 1 (by rfl) ⟨2592080, by rfl⟩ : syracuseStep 3456107 = 5184161) B5184161
theorem B9326825 : Blo 1020604 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B74771261 : Blo 1020604 74771261 := bstep (se 3 (by rfl) ⟨14019611, by rfl⟩ : syracuseStep 74771261 = 28039223) B28039223
theorem B49847507 : Blo 1020604 49847507 := bstep (se 1 (by rfl) ⟨37385630, by rfl⟩ : syracuseStep 49847507 = 74771261) B74771261
theorem B2304071 : Blo 1020604 2304071 := bstep (se 1 (by rfl) ⟨1728053, by rfl⟩ : syracuseStep 2304071 = 3456107) B3456107
theorem B121221139 : Blo 1020604 121221139 := bstep (se 1 (by rfl) ⟨90915854, by rfl⟩ : syracuseStep 121221139 = 181831709) B181831709
theorem B6217883 : Blo 1020604 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B33231671 : Blo 1020604 33231671 := bstep (se 1 (by rfl) ⟨24923753, by rfl⟩ : syracuseStep 33231671 = 49847507) B49847507
theorem B161628185 : Blo 1020604 161628185 := bstep (se 2 (by rfl) ⟨60610569, by rfl⟩ : syracuseStep 161628185 = 121221139) B121221139
theorem B4145255 : Blo 1020604 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B1536047 : Blo 1020604 1536047 := bstep (se 1 (by rfl) ⟨1152035, by rfl⟩ : syracuseStep 1536047 = 2304071) B2304071
theorem B22154447 : Blo 1020604 22154447 := bstep (se 1 (by rfl) ⟨16615835, by rfl⟩ : syracuseStep 22154447 = 33231671) B33231671
theorem B1024031 : Blo 1020604 1024031 := bstep (se 1 (by rfl) ⟨768023, by rfl⟩ : syracuseStep 1024031 = 1536047) B1536047
theorem B107752123 : Blo 1020604 107752123 := bstep (se 1 (by rfl) ⟨80814092, by rfl⟩ : syracuseStep 107752123 = 161628185) B161628185
theorem B2763503 : Blo 1020604 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B1842335 : Blo 1020604 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B143669497 : Blo 1020604 143669497 := bstep (se 2 (by rfl) ⟨53876061, by rfl⟩ : syracuseStep 143669497 = 107752123) B107752123
theorem B14769631 : Blo 1020604 14769631 := bstep (se 1 (by rfl) ⟨11077223, by rfl⟩ : syracuseStep 14769631 = 22154447) B22154447
theorem B1228223 : Blo 1020604 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B191559329 : Blo 1020604 191559329 := bstep (se 2 (by rfl) ⟨71834748, by rfl⟩ : syracuseStep 191559329 = 143669497) B143669497
theorem B19692841 : Blo 1020604 19692841 := bstep (se 2 (by rfl) ⟨7384815, by rfl⟩ : syracuseStep 19692841 = 14769631) B14769631
theorem B127706219 : Blo 1020604 127706219 := bstep (se 1 (by rfl) ⟨95779664, by rfl⟩ : syracuseStep 127706219 = 191559329) B191559329
theorem B26257121 : Blo 1020604 26257121 := bstep (se 2 (by rfl) ⟨9846420, by rfl⟩ : syracuseStep 26257121 = 19692841) B19692841
theorem B3275261 : Blo 1020604 3275261 := bstep (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) B1228223
theorem B85137479 : Blo 1020604 85137479 := bstep (se 1 (by rfl) ⟨63853109, by rfl⟩ : syracuseStep 85137479 = 127706219) B127706219
theorem B17504747 : Blo 1020604 17504747 := bstep (se 1 (by rfl) ⟨13128560, by rfl⟩ : syracuseStep 17504747 = 26257121) B26257121
theorem B2183507 : Blo 1020604 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B56758319 : Blo 1020604 56758319 := bstep (se 1 (by rfl) ⟨42568739, by rfl⟩ : syracuseStep 56758319 = 85137479) B85137479
theorem B11669831 : Blo 1020604 11669831 := bstep (se 1 (by rfl) ⟨8752373, by rfl⟩ : syracuseStep 11669831 = 17504747) B17504747
theorem B1455671 : Blo 1020604 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B7779887 : Blo 1020604 7779887 := bstep (se 1 (by rfl) ⟨5834915, by rfl⟩ : syracuseStep 7779887 = 11669831) B11669831
theorem B3881789 : Blo 1020604 3881789 := bstep (se 3 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 3881789 = 1455671) B1455671
theorem B37838879 : Blo 1020604 37838879 := bstep (se 1 (by rfl) ⟨28379159, by rfl⟩ : syracuseStep 37838879 = 56758319) B56758319
theorem B5186591 : Blo 1020604 5186591 := bstep (se 1 (by rfl) ⟨3889943, by rfl⟩ : syracuseStep 5186591 = 7779887) B7779887
theorem B25225919 : Blo 1020604 25225919 := bstep (se 1 (by rfl) ⟨18919439, by rfl⟩ : syracuseStep 25225919 = 37838879) B37838879
theorem B2587859 : Blo 1020604 2587859 := bstep (se 1 (by rfl) ⟨1940894, by rfl⟩ : syracuseStep 2587859 = 3881789) B3881789
theorem B16817279 : Blo 1020604 16817279 := bstep (se 1 (by rfl) ⟨12612959, by rfl⟩ : syracuseStep 16817279 = 25225919) B25225919
theorem B3457727 : Blo 1020604 3457727 := bstep (se 1 (by rfl) ⟨2593295, by rfl⟩ : syracuseStep 3457727 = 5186591) B5186591
theorem B1725239 : Blo 1020604 1725239 := bstep (se 1 (by rfl) ⟨1293929, by rfl⟩ : syracuseStep 1725239 = 2587859) B2587859
theorem B1150159 : Blo 1020604 1150159 := bstep (se 1 (by rfl) ⟨862619, by rfl⟩ : syracuseStep 1150159 = 1725239) B1725239
theorem B2305151 : Blo 1020604 2305151 := bstep (se 1 (by rfl) ⟨1728863, by rfl⟩ : syracuseStep 2305151 = 3457727) B3457727
theorem B44846077 : Blo 1020604 44846077 := bstep (se 3 (by rfl) ⟨8408639, by rfl⟩ : syracuseStep 44846077 = 16817279) B16817279
theorem B59794769 : Blo 1020604 59794769 := bstep (se 2 (by rfl) ⟨22423038, by rfl⟩ : syracuseStep 59794769 = 44846077) B44846077
theorem B1533545 : Blo 1020604 1533545 := bstep (se 2 (by rfl) ⟨575079, by rfl⟩ : syracuseStep 1533545 = 1150159) B1150159
theorem B1536767 : Blo 1020604 1536767 := bstep (se 1 (by rfl) ⟨1152575, by rfl⟩ : syracuseStep 1536767 = 2305151) B2305151
theorem B1022363 : Blo 1020604 1022363 := bstep (se 1 (by rfl) ⟨766772, by rfl⟩ : syracuseStep 1022363 = 1533545) B1533545
theorem B1024511 : Blo 1020604 1024511 := bstep (se 1 (by rfl) ⟨768383, by rfl⟩ : syracuseStep 1024511 = 1536767) B1536767
theorem B39863179 : Blo 1020604 39863179 := bstep (se 1 (by rfl) ⟨29897384, by rfl⟩ : syracuseStep 39863179 = 59794769) B59794769
theorem B53150905 : Blo 1020604 53150905 := bstep (se 2 (by rfl) ⟨19931589, by rfl⟩ : syracuseStep 53150905 = 39863179) B39863179
theorem B70867873 : Blo 1020604 70867873 := bstep (se 2 (by rfl) ⟨26575452, by rfl⟩ : syracuseStep 70867873 = 53150905) B53150905
theorem B94490497 : Blo 1020604 94490497 := bstep (se 2 (by rfl) ⟨35433936, by rfl⟩ : syracuseStep 94490497 = 70867873) B70867873
theorem B125987329 : Blo 1020604 125987329 := bstep (se 2 (by rfl) ⟨47245248, by rfl⟩ : syracuseStep 125987329 = 94490497) B94490497
theorem B167983105 : Blo 1020604 167983105 := bstep (se 2 (by rfl) ⟨62993664, by rfl⟩ : syracuseStep 167983105 = 125987329) B125987329
theorem B223977473 : Blo 1020604 223977473 := bstep (se 2 (by rfl) ⟨83991552, by rfl⟩ : syracuseStep 223977473 = 167983105) B167983105
theorem B149318315 : Blo 1020604 149318315 := bstep (se 1 (by rfl) ⟨111988736, by rfl⟩ : syracuseStep 149318315 = 223977473) B223977473
theorem B99545543 : Blo 1020604 99545543 := bstep (se 1 (by rfl) ⟨74659157, by rfl⟩ : syracuseStep 99545543 = 149318315) B149318315
theorem B66363695 : Blo 1020604 66363695 := bstep (se 1 (by rfl) ⟨49772771, by rfl⟩ : syracuseStep 66363695 = 99545543) B99545543
theorem B44242463 : Blo 1020604 44242463 := bstep (se 1 (by rfl) ⟨33181847, by rfl⟩ : syracuseStep 44242463 = 66363695) B66363695
theorem B29494975 : Blo 1020604 29494975 := bstep (se 1 (by rfl) ⟨22121231, by rfl⟩ : syracuseStep 29494975 = 44242463) B44242463
theorem B39326633 : Blo 1020604 39326633 := bstep (se 2 (by rfl) ⟨14747487, by rfl⟩ : syracuseStep 39326633 = 29494975) B29494975
theorem B26217755 : Blo 1020604 26217755 := bstep (se 1 (by rfl) ⟨19663316, by rfl⟩ : syracuseStep 26217755 = 39326633) B39326633
theorem B17478503 : Blo 1020604 17478503 := bstep (se 1 (by rfl) ⟨13108877, by rfl⟩ : syracuseStep 17478503 = 26217755) B26217755
theorem B11652335 : Blo 1020604 11652335 := bstep (se 1 (by rfl) ⟨8739251, by rfl⟩ : syracuseStep 11652335 = 17478503) B17478503
theorem B7768223 : Blo 1020604 7768223 := bstep (se 1 (by rfl) ⟨5826167, by rfl⟩ : syracuseStep 7768223 = 11652335) B11652335
theorem B5178815 : Blo 1020604 5178815 := bstep (se 1 (by rfl) ⟨3884111, by rfl⟩ : syracuseStep 5178815 = 7768223) B7768223
theorem B3452543 : Blo 1020604 3452543 := bstep (se 1 (by rfl) ⟨2589407, by rfl⟩ : syracuseStep 3452543 = 5178815) B5178815
theorem B2301695 : Blo 1020604 2301695 := bstep (se 1 (by rfl) ⟨1726271, by rfl⟩ : syracuseStep 2301695 = 3452543) B3452543
theorem B1534463 : Blo 1020604 1534463 := bstep (se 1 (by rfl) ⟨1150847, by rfl⟩ : syracuseStep 1534463 = 2301695) B2301695
theorem B1022975 : Blo 1020604 1022975 := bstep (se 1 (by rfl) ⟨767231, by rfl⟩ : syracuseStep 1022975 = 1534463) B1534463

theorem C0 (j : ℕ) (h1 : 255151 ≤ j) (h2 : j ≤ 255850) : Blo 1020604 (4 * j + 3) := by
  interval_cases j
  · exact B1020607
  · exact B1020611
  · exact B1020615
  · exact B1020619
  · exact B1020623
  · exact B1020627
  · exact B1020631
  · exact B1020635
  · exact B1020639
  · exact B1020643
  · exact B1020647
  · exact B1020651
  · exact B1020655
  · exact B1020659
  · exact B1020663
  · exact B1020667
  · exact B1020671
  · exact B1020675
  · exact B1020679
  · exact B1020683
  · exact B1020687
  · exact B1020691
  · exact B1020695
  · exact B1020699
  · exact B1020703
  · exact B1020707
  · exact B1020711
  · exact B1020715
  · exact B1020719
  · exact B1020723
  · exact B1020727
  · exact B1020731
  · exact B1020735
  · exact B1020739
  · exact B1020743
  · exact B1020747
  · exact B1020751
  · exact B1020755
  · exact B1020759
  · exact B1020763
  · exact B1020767
  · exact B1020771
  · exact B1020775
  · exact B1020779
  · exact B1020783
  · exact B1020787
  · exact B1020791
  · exact B1020795
  · exact B1020799
  · exact B1020803
  · exact B1020807
  · exact B1020811
  · exact B1020815
  · exact B1020819
  · exact B1020823
  · exact B1020827
  · exact B1020831
  · exact B1020835
  · exact B1020839
  · exact B1020843
  · exact B1020847
  · exact B1020851
  · exact B1020855
  · exact B1020859
  · exact B1020863
  · exact B1020867
  · exact B1020871
  · exact B1020875
  · exact B1020879
  · exact B1020883
  · exact B1020887
  · exact B1020891
  · exact B1020895
  · exact B1020899
  · exact B1020903
  · exact B1020907
  · exact B1020911
  · exact B1020915
  · exact B1020919
  · exact B1020923
  · exact B1020927
  · exact B1020931
  · exact B1020935
  · exact B1020939
  · exact B1020943
  · exact B1020947
  · exact B1020951
  · exact B1020955
  · exact B1020959
  · exact B1020963
  · exact B1020967
  · exact B1020971
  · exact B1020975
  · exact B1020979
  · exact B1020983
  · exact B1020987
  · exact B1020991
  · exact B1020995
  · exact B1020999
  · exact B1021003
  · exact B1021007
  · exact B1021011
  · exact B1021015
  · exact B1021019
  · exact B1021023
  · exact B1021027
  · exact B1021031
  · exact B1021035
  · exact B1021039
  · exact B1021043
  · exact B1021047
  · exact B1021051
  · exact B1021055
  · exact B1021059
  · exact B1021063
  · exact B1021067
  · exact B1021071
  · exact B1021075
  · exact B1021079
  · exact B1021083
  · exact B1021087
  · exact B1021091
  · exact B1021095
  · exact B1021099
  · exact B1021103
  · exact B1021107
  · exact B1021111
  · exact B1021115
  · exact B1021119
  · exact B1021123
  · exact B1021127
  · exact B1021131
  · exact B1021135
  · exact B1021139
  · exact B1021143
  · exact B1021147
  · exact B1021151
  · exact B1021155
  · exact B1021159
  · exact B1021163
  · exact B1021167
  · exact B1021171
  · exact B1021175
  · exact B1021179
  · exact B1021183
  · exact B1021187
  · exact B1021191
  · exact B1021195
  · exact B1021199
  · exact B1021203
  · exact B1021207
  · exact B1021211
  · exact B1021215
  · exact B1021219
  · exact B1021223
  · exact B1021227
  · exact B1021231
  · exact B1021235
  · exact B1021239
  · exact B1021243
  · exact B1021247
  · exact B1021251
  · exact B1021255
  · exact B1021259
  · exact B1021263
  · exact B1021267
  · exact B1021271
  · exact B1021275
  · exact B1021279
  · exact B1021283
  · exact B1021287
  · exact B1021291
  · exact B1021295
  · exact B1021299
  · exact B1021303
  · exact B1021307
  · exact B1021311
  · exact B1021315
  · exact B1021319
  · exact B1021323
  · exact B1021327
  · exact B1021331
  · exact B1021335
  · exact B1021339
  · exact B1021343
  · exact B1021347
  · exact B1021351
  · exact B1021355
  · exact B1021359
  · exact B1021363
  · exact B1021367
  · exact B1021371
  · exact B1021375
  · exact B1021379
  · exact B1021383
  · exact B1021387
  · exact B1021391
  · exact B1021395
  · exact B1021399
  · exact B1021403
  · exact B1021407
  · exact B1021411
  · exact B1021415
  · exact B1021419
  · exact B1021423
  · exact B1021427
  · exact B1021431
  · exact B1021435
  · exact B1021439
  · exact B1021443
  · exact B1021447
  · exact B1021451
  · exact B1021455
  · exact B1021459
  · exact B1021463
  · exact B1021467
  · exact B1021471
  · exact B1021475
  · exact B1021479
  · exact B1021483
  · exact B1021487
  · exact B1021491
  · exact B1021495
  · exact B1021499
  · exact B1021503
  · exact B1021507
  · exact B1021511
  · exact B1021515
  · exact B1021519
  · exact B1021523
  · exact B1021527
  · exact B1021531
  · exact B1021535
  · exact B1021539
  · exact B1021543
  · exact B1021547
  · exact B1021551
  · exact B1021555
  · exact B1021559
  · exact B1021563
  · exact B1021567
  · exact B1021571
  · exact B1021575
  · exact B1021579
  · exact B1021583
  · exact B1021587
  · exact B1021591
  · exact B1021595
  · exact B1021599
  · exact B1021603
  · exact B1021607
  · exact B1021611
  · exact B1021615
  · exact B1021619
  · exact B1021623
  · exact B1021627
  · exact B1021631
  · exact B1021635
  · exact B1021639
  · exact B1021643
  · exact B1021647
  · exact B1021651
  · exact B1021655
  · exact B1021659
  · exact B1021663
  · exact B1021667
  · exact B1021671
  · exact B1021675
  · exact B1021679
  · exact B1021683
  · exact B1021687
  · exact B1021691
  · exact B1021695
  · exact B1021699
  · exact B1021703
  · exact B1021707
  · exact B1021711
  · exact B1021715
  · exact B1021719
  · exact B1021723
  · exact B1021727
  · exact B1021731
  · exact B1021735
  · exact B1021739
  · exact B1021743
  · exact B1021747
  · exact B1021751
  · exact B1021755
  · exact B1021759
  · exact B1021763
  · exact B1021767
  · exact B1021771
  · exact B1021775
  · exact B1021779
  · exact B1021783
  · exact B1021787
  · exact B1021791
  · exact B1021795
  · exact B1021799
  · exact B1021803
  · exact B1021807
  · exact B1021811
  · exact B1021815
  · exact B1021819
  · exact B1021823
  · exact B1021827
  · exact B1021831
  · exact B1021835
  · exact B1021839
  · exact B1021843
  · exact B1021847
  · exact B1021851
  · exact B1021855
  · exact B1021859
  · exact B1021863
  · exact B1021867
  · exact B1021871
  · exact B1021875
  · exact B1021879
  · exact B1021883
  · exact B1021887
  · exact B1021891
  · exact B1021895
  · exact B1021899
  · exact B1021903
  · exact B1021907
  · exact B1021911
  · exact B1021915
  · exact B1021919
  · exact B1021923
  · exact B1021927
  · exact B1021931
  · exact B1021935
  · exact B1021939
  · exact B1021943
  · exact B1021947
  · exact B1021951
  · exact B1021955
  · exact B1021959
  · exact B1021963
  · exact B1021967
  · exact B1021971
  · exact B1021975
  · exact B1021979
  · exact B1021983
  · exact B1021987
  · exact B1021991
  · exact B1021995
  · exact B1021999
  · exact B1022003
  · exact B1022007
  · exact B1022011
  · exact B1022015
  · exact B1022019
  · exact B1022023
  · exact B1022027
  · exact B1022031
  · exact B1022035
  · exact B1022039
  · exact B1022043
  · exact B1022047
  · exact B1022051
  · exact B1022055
  · exact B1022059
  · exact B1022063
  · exact B1022067
  · exact B1022071
  · exact B1022075
  · exact B1022079
  · exact B1022083
  · exact B1022087
  · exact B1022091
  · exact B1022095
  · exact B1022099
  · exact B1022103
  · exact B1022107
  · exact B1022111
  · exact B1022115
  · exact B1022119
  · exact B1022123
  · exact B1022127
  · exact B1022131
  · exact B1022135
  · exact B1022139
  · exact B1022143
  · exact B1022147
  · exact B1022151
  · exact B1022155
  · exact B1022159
  · exact B1022163
  · exact B1022167
  · exact B1022171
  · exact B1022175
  · exact B1022179
  · exact B1022183
  · exact B1022187
  · exact B1022191
  · exact B1022195
  · exact B1022199
  · exact B1022203
  · exact B1022207
  · exact B1022211
  · exact B1022215
  · exact B1022219
  · exact B1022223
  · exact B1022227
  · exact B1022231
  · exact B1022235
  · exact B1022239
  · exact B1022243
  · exact B1022247
  · exact B1022251
  · exact B1022255
  · exact B1022259
  · exact B1022263
  · exact B1022267
  · exact B1022271
  · exact B1022275
  · exact B1022279
  · exact B1022283
  · exact B1022287
  · exact B1022291
  · exact B1022295
  · exact B1022299
  · exact B1022303
  · exact B1022307
  · exact B1022311
  · exact B1022315
  · exact B1022319
  · exact B1022323
  · exact B1022327
  · exact B1022331
  · exact B1022335
  · exact B1022339
  · exact B1022343
  · exact B1022347
  · exact B1022351
  · exact B1022355
  · exact B1022359
  · exact B1022363
  · exact B1022367
  · exact B1022371
  · exact B1022375
  · exact B1022379
  · exact B1022383
  · exact B1022387
  · exact B1022391
  · exact B1022395
  · exact B1022399
  · exact B1022403
  · exact B1022407
  · exact B1022411
  · exact B1022415
  · exact B1022419
  · exact B1022423
  · exact B1022427
  · exact B1022431
  · exact B1022435
  · exact B1022439
  · exact B1022443
  · exact B1022447
  · exact B1022451
  · exact B1022455
  · exact B1022459
  · exact B1022463
  · exact B1022467
  · exact B1022471
  · exact B1022475
  · exact B1022479
  · exact B1022483
  · exact B1022487
  · exact B1022491
  · exact B1022495
  · exact B1022499
  · exact B1022503
  · exact B1022507
  · exact B1022511
  · exact B1022515
  · exact B1022519
  · exact B1022523
  · exact B1022527
  · exact B1022531
  · exact B1022535
  · exact B1022539
  · exact B1022543
  · exact B1022547
  · exact B1022551
  · exact B1022555
  · exact B1022559
  · exact B1022563
  · exact B1022567
  · exact B1022571
  · exact B1022575
  · exact B1022579
  · exact B1022583
  · exact B1022587
  · exact B1022591
  · exact B1022595
  · exact B1022599
  · exact B1022603
  · exact B1022607
  · exact B1022611
  · exact B1022615
  · exact B1022619
  · exact B1022623
  · exact B1022627
  · exact B1022631
  · exact B1022635
  · exact B1022639
  · exact B1022643
  · exact B1022647
  · exact B1022651
  · exact B1022655
  · exact B1022659
  · exact B1022663
  · exact B1022667
  · exact B1022671
  · exact B1022675
  · exact B1022679
  · exact B1022683
  · exact B1022687
  · exact B1022691
  · exact B1022695
  · exact B1022699
  · exact B1022703
  · exact B1022707
  · exact B1022711
  · exact B1022715
  · exact B1022719
  · exact B1022723
  · exact B1022727
  · exact B1022731
  · exact B1022735
  · exact B1022739
  · exact B1022743
  · exact B1022747
  · exact B1022751
  · exact B1022755
  · exact B1022759
  · exact B1022763
  · exact B1022767
  · exact B1022771
  · exact B1022775
  · exact B1022779
  · exact B1022783
  · exact B1022787
  · exact B1022791
  · exact B1022795
  · exact B1022799
  · exact B1022803
  · exact B1022807
  · exact B1022811
  · exact B1022815
  · exact B1022819
  · exact B1022823
  · exact B1022827
  · exact B1022831
  · exact B1022835
  · exact B1022839
  · exact B1022843
  · exact B1022847
  · exact B1022851
  · exact B1022855
  · exact B1022859
  · exact B1022863
  · exact B1022867
  · exact B1022871
  · exact B1022875
  · exact B1022879
  · exact B1022883
  · exact B1022887
  · exact B1022891
  · exact B1022895
  · exact B1022899
  · exact B1022903
  · exact B1022907
  · exact B1022911
  · exact B1022915
  · exact B1022919
  · exact B1022923
  · exact B1022927
  · exact B1022931
  · exact B1022935
  · exact B1022939
  · exact B1022943
  · exact B1022947
  · exact B1022951
  · exact B1022955
  · exact B1022959
  · exact B1022963
  · exact B1022967
  · exact B1022971
  · exact B1022975
  · exact B1022979
  · exact B1022983
  · exact B1022987
  · exact B1022991
  · exact B1022995
  · exact B1022999
  · exact B1023003
  · exact B1023007
  · exact B1023011
  · exact B1023015
  · exact B1023019
  · exact B1023023
  · exact B1023027
  · exact B1023031
  · exact B1023035
  · exact B1023039
  · exact B1023043
  · exact B1023047
  · exact B1023051
  · exact B1023055
  · exact B1023059
  · exact B1023063
  · exact B1023067
  · exact B1023071
  · exact B1023075
  · exact B1023079
  · exact B1023083
  · exact B1023087
  · exact B1023091
  · exact B1023095
  · exact B1023099
  · exact B1023103
  · exact B1023107
  · exact B1023111
  · exact B1023115
  · exact B1023119
  · exact B1023123
  · exact B1023127
  · exact B1023131
  · exact B1023135
  · exact B1023139
  · exact B1023143
  · exact B1023147
  · exact B1023151
  · exact B1023155
  · exact B1023159
  · exact B1023163
  · exact B1023167
  · exact B1023171
  · exact B1023175
  · exact B1023179
  · exact B1023183
  · exact B1023187
  · exact B1023191
  · exact B1023195
  · exact B1023199
  · exact B1023203
  · exact B1023207
  · exact B1023211
  · exact B1023215
  · exact B1023219
  · exact B1023223
  · exact B1023227
  · exact B1023231
  · exact B1023235
  · exact B1023239
  · exact B1023243
  · exact B1023247
  · exact B1023251
  · exact B1023255
  · exact B1023259
  · exact B1023263
  · exact B1023267
  · exact B1023271
  · exact B1023275
  · exact B1023279
  · exact B1023283
  · exact B1023287
  · exact B1023291
  · exact B1023295
  · exact B1023299
  · exact B1023303
  · exact B1023307
  · exact B1023311
  · exact B1023315
  · exact B1023319
  · exact B1023323
  · exact B1023327
  · exact B1023331
  · exact B1023335
  · exact B1023339
  · exact B1023343
  · exact B1023347
  · exact B1023351
  · exact B1023355
  · exact B1023359
  · exact B1023363
  · exact B1023367
  · exact B1023371
  · exact B1023375
  · exact B1023379
  · exact B1023383
  · exact B1023387
  · exact B1023391
  · exact B1023395
  · exact B1023399
  · exact B1023403

theorem C1 (j : ℕ) (h1 : 255851 ≤ j) (h2 : j ≤ 256150) : Blo 1020604 (4 * j + 3) := by
  interval_cases j
  · exact B1023407
  · exact B1023411
  · exact B1023415
  · exact B1023419
  · exact B1023423
  · exact B1023427
  · exact B1023431
  · exact B1023435
  · exact B1023439
  · exact B1023443
  · exact B1023447
  · exact B1023451
  · exact B1023455
  · exact B1023459
  · exact B1023463
  · exact B1023467
  · exact B1023471
  · exact B1023475
  · exact B1023479
  · exact B1023483
  · exact B1023487
  · exact B1023491
  · exact B1023495
  · exact B1023499
  · exact B1023503
  · exact B1023507
  · exact B1023511
  · exact B1023515
  · exact B1023519
  · exact B1023523
  · exact B1023527
  · exact B1023531
  · exact B1023535
  · exact B1023539
  · exact B1023543
  · exact B1023547
  · exact B1023551
  · exact B1023555
  · exact B1023559
  · exact B1023563
  · exact B1023567
  · exact B1023571
  · exact B1023575
  · exact B1023579
  · exact B1023583
  · exact B1023587
  · exact B1023591
  · exact B1023595
  · exact B1023599
  · exact B1023603
  · exact B1023607
  · exact B1023611
  · exact B1023615
  · exact B1023619
  · exact B1023623
  · exact B1023627
  · exact B1023631
  · exact B1023635
  · exact B1023639
  · exact B1023643
  · exact B1023647
  · exact B1023651
  · exact B1023655
  · exact B1023659
  · exact B1023663
  · exact B1023667
  · exact B1023671
  · exact B1023675
  · exact B1023679
  · exact B1023683
  · exact B1023687
  · exact B1023691
  · exact B1023695
  · exact B1023699
  · exact B1023703
  · exact B1023707
  · exact B1023711
  · exact B1023715
  · exact B1023719
  · exact B1023723
  · exact B1023727
  · exact B1023731
  · exact B1023735
  · exact B1023739
  · exact B1023743
  · exact B1023747
  · exact B1023751
  · exact B1023755
  · exact B1023759
  · exact B1023763
  · exact B1023767
  · exact B1023771
  · exact B1023775
  · exact B1023779
  · exact B1023783
  · exact B1023787
  · exact B1023791
  · exact B1023795
  · exact B1023799
  · exact B1023803
  · exact B1023807
  · exact B1023811
  · exact B1023815
  · exact B1023819
  · exact B1023823
  · exact B1023827
  · exact B1023831
  · exact B1023835
  · exact B1023839
  · exact B1023843
  · exact B1023847
  · exact B1023851
  · exact B1023855
  · exact B1023859
  · exact B1023863
  · exact B1023867
  · exact B1023871
  · exact B1023875
  · exact B1023879
  · exact B1023883
  · exact B1023887
  · exact B1023891
  · exact B1023895
  · exact B1023899
  · exact B1023903
  · exact B1023907
  · exact B1023911
  · exact B1023915
  · exact B1023919
  · exact B1023923
  · exact B1023927
  · exact B1023931
  · exact B1023935
  · exact B1023939
  · exact B1023943
  · exact B1023947
  · exact B1023951
  · exact B1023955
  · exact B1023959
  · exact B1023963
  · exact B1023967
  · exact B1023971
  · exact B1023975
  · exact B1023979
  · exact B1023983
  · exact B1023987
  · exact B1023991
  · exact B1023995
  · exact B1023999
  · exact B1024003
  · exact B1024007
  · exact B1024011
  · exact B1024015
  · exact B1024019
  · exact B1024023
  · exact B1024027
  · exact B1024031
  · exact B1024035
  · exact B1024039
  · exact B1024043
  · exact B1024047
  · exact B1024051
  · exact B1024055
  · exact B1024059
  · exact B1024063
  · exact B1024067
  · exact B1024071
  · exact B1024075
  · exact B1024079
  · exact B1024083
  · exact B1024087
  · exact B1024091
  · exact B1024095
  · exact B1024099
  · exact B1024103
  · exact B1024107
  · exact B1024111
  · exact B1024115
  · exact B1024119
  · exact B1024123
  · exact B1024127
  · exact B1024131
  · exact B1024135
  · exact B1024139
  · exact B1024143
  · exact B1024147
  · exact B1024151
  · exact B1024155
  · exact B1024159
  · exact B1024163
  · exact B1024167
  · exact B1024171
  · exact B1024175
  · exact B1024179
  · exact B1024183
  · exact B1024187
  · exact B1024191
  · exact B1024195
  · exact B1024199
  · exact B1024203
  · exact B1024207
  · exact B1024211
  · exact B1024215
  · exact B1024219
  · exact B1024223
  · exact B1024227
  · exact B1024231
  · exact B1024235
  · exact B1024239
  · exact B1024243
  · exact B1024247
  · exact B1024251
  · exact B1024255
  · exact B1024259
  · exact B1024263
  · exact B1024267
  · exact B1024271
  · exact B1024275
  · exact B1024279
  · exact B1024283
  · exact B1024287
  · exact B1024291
  · exact B1024295
  · exact B1024299
  · exact B1024303
  · exact B1024307
  · exact B1024311
  · exact B1024315
  · exact B1024319
  · exact B1024323
  · exact B1024327
  · exact B1024331
  · exact B1024335
  · exact B1024339
  · exact B1024343
  · exact B1024347
  · exact B1024351
  · exact B1024355
  · exact B1024359
  · exact B1024363
  · exact B1024367
  · exact B1024371
  · exact B1024375
  · exact B1024379
  · exact B1024383
  · exact B1024387
  · exact B1024391
  · exact B1024395
  · exact B1024399
  · exact B1024403
  · exact B1024407
  · exact B1024411
  · exact B1024415
  · exact B1024419
  · exact B1024423
  · exact B1024427
  · exact B1024431
  · exact B1024435
  · exact B1024439
  · exact B1024443
  · exact B1024447
  · exact B1024451
  · exact B1024455
  · exact B1024459
  · exact B1024463
  · exact B1024467
  · exact B1024471
  · exact B1024475
  · exact B1024479
  · exact B1024483
  · exact B1024487
  · exact B1024491
  · exact B1024495
  · exact B1024499
  · exact B1024503
  · exact B1024507
  · exact B1024511
  · exact B1024515
  · exact B1024519
  · exact B1024523
  · exact B1024527
  · exact B1024531
  · exact B1024535
  · exact B1024539
  · exact B1024543
  · exact B1024547
  · exact B1024551
  · exact B1024555
  · exact B1024559
  · exact B1024563
  · exact B1024567
  · exact B1024571
  · exact B1024575
  · exact B1024579
  · exact B1024583
  · exact B1024587
  · exact B1024591
  · exact B1024595
  · exact B1024599
  · exact B1024603

theorem solution (m : ℕ) (hlo : 1020604 ≤ m) (hhi : m ≤ 1024604) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 255151 ≤ j := by omega
    have hj2 : j ≤ 256150 := by omega
    have hb : Blo 1020604 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 255851 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
