-- Prove2me | solution 1 for syracuse_descends_range_539803_542803
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:32.453405+00:00
-- url     : https://prove2.me/submissions/18b6ff88-23f9-4fdf-a649-58e0ccb38574

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


theorem B811013 : Blo 539803 811013 := bbase (se 4 (by rfl) ⟨76032, by rfl⟩ : syracuseStep 811013 = 152065) (by norm_num)
theorem B2318341 : Blo 539803 2318341 := bbase (se 4 (by rfl) ⟨217344, by rfl⟩ : syracuseStep 2318341 = 434689) (by norm_num)
theorem B2318357 : Blo 539803 2318357 := bbase (se 6 (by rfl) ⟨54336, by rfl⟩ : syracuseStep 2318357 = 108673) (by norm_num)
theorem B811037 : Blo 539803 811037 := bbase (se 3 (by rfl) ⟨152069, by rfl⟩ : syracuseStep 811037 = 304139) (by norm_num)
theorem B548893 : Blo 539803 548893 := bbase (se 3 (by rfl) ⟨102917, by rfl⟩ : syracuseStep 548893 = 205835) (by norm_num)
theorem B1221173 : Blo 539803 1221173 := bbase (se 5 (by rfl) ⟨57242, by rfl⟩ : syracuseStep 1221173 = 114485) (by norm_num)
theorem B811061 : Blo 539803 811061 := bbase (se 5 (by rfl) ⟨38018, by rfl⟩ : syracuseStep 811061 = 76037) (by norm_num)
theorem B1220669 : Blo 539803 1220669 := bbase (se 3 (by rfl) ⟨228875, by rfl⟩ : syracuseStep 1220669 = 457751) (by norm_num)
theorem B811085 : Blo 539803 811085 := bbase (se 3 (by rfl) ⟨152078, by rfl⟩ : syracuseStep 811085 = 304157) (by norm_num)
theorem B811109 : Blo 539803 811109 := bbase (se 4 (by rfl) ⟨76041, by rfl⟩ : syracuseStep 811109 = 152083) (by norm_num)
theorem B1155181 : Blo 539803 1155181 := bbase (se 3 (by rfl) ⟨216596, by rfl⟩ : syracuseStep 1155181 = 433193) (by norm_num)
theorem B811133 : Blo 539803 811133 := bbase (se 3 (by rfl) ⟨152087, by rfl⟩ : syracuseStep 811133 = 304175) (by norm_num)
theorem B1220741 : Blo 539803 1220741 := bbase (se 4 (by rfl) ⟨114444, by rfl⟩ : syracuseStep 1220741 = 228889) (by norm_num)
theorem B811157 : Blo 539803 811157 := bbase (se 6 (by rfl) ⟨19011, by rfl⟩ : syracuseStep 811157 = 38023) (by norm_num)
theorem B876701 : Blo 539803 876701 := bbase (se 3 (by rfl) ⟨164381, by rfl⟩ : syracuseStep 876701 = 328763) (by norm_num)
theorem B1826981 : Blo 539803 1826981 := bbase (se 4 (by rfl) ⟨171279, by rfl⟩ : syracuseStep 1826981 = 342559) (by norm_num)
theorem B811181 : Blo 539803 811181 := bbase (se 3 (by rfl) ⟨152096, by rfl⟩ : syracuseStep 811181 = 304193) (by norm_num)
theorem B2056373 : Blo 539803 2056373 := bbase (se 5 (by rfl) ⟨96392, by rfl⟩ : syracuseStep 2056373 = 192785) (by norm_num)
theorem B811205 : Blo 539803 811205 := bbase (se 4 (by rfl) ⟨76050, by rfl⟩ : syracuseStep 811205 = 152101) (by norm_num)
theorem B975053 : Blo 539803 975053 := bbase (se 3 (by rfl) ⟨182822, by rfl⟩ : syracuseStep 975053 = 365645) (by norm_num)
theorem B2736341 : Blo 539803 2736341 := bbase (se 7 (by rfl) ⟨32066, by rfl⟩ : syracuseStep 2736341 = 64133) (by norm_num)
theorem B1540309 : Blo 539803 1540309 := bbase (se 7 (by rfl) ⟨18050, by rfl⟩ : syracuseStep 1540309 = 36101) (by norm_num)
theorem B811229 : Blo 539803 811229 := bbase (se 3 (by rfl) ⟨152105, by rfl⟩ : syracuseStep 811229 = 304211) (by norm_num)
theorem B811253 : Blo 539803 811253 := bbase (se 5 (by rfl) ⟨38027, by rfl⟩ : syracuseStep 811253 = 76055) (by norm_num)
theorem B811277 : Blo 539803 811277 := bbase (se 3 (by rfl) ⟨152114, by rfl⟩ : syracuseStep 811277 = 304229) (by norm_num)
theorem B1220885 : Blo 539803 1220885 := bbase (se 6 (by rfl) ⟨28614, by rfl⟩ : syracuseStep 1220885 = 57229) (by norm_num)
theorem B811301 : Blo 539803 811301 := bbase (se 4 (by rfl) ⟨76059, by rfl⟩ : syracuseStep 811301 = 152119) (by norm_num)
theorem B1368373 : Blo 539803 1368373 := bbase (se 5 (by rfl) ⟨64142, by rfl⟩ : syracuseStep 1368373 = 128285) (by norm_num)
theorem B868661 : Blo 539803 868661 := bbase (se 5 (by rfl) ⟨40718, by rfl⟩ : syracuseStep 868661 = 81437) (by norm_num)
theorem B811325 : Blo 539803 811325 := bbase (se 3 (by rfl) ⟨152123, by rfl⟩ : syracuseStep 811325 = 304247) (by norm_num)
theorem B549181 : Blo 539803 549181 := bbase (se 3 (by rfl) ⟨102971, by rfl⟩ : syracuseStep 549181 = 205943) (by norm_num)
theorem B811349 : Blo 539803 811349 := bbase (se 10 (by rfl) ⟨1188, by rfl⟩ : syracuseStep 811349 = 2377) (by norm_num)
theorem B1220957 : Blo 539803 1220957 := bbase (se 3 (by rfl) ⟨228929, by rfl⟩ : syracuseStep 1220957 = 457859) (by norm_num)
theorem B549217 : Blo 539803 549217 := bbase (se 2 (by rfl) ⟨205956, by rfl⟩ : syracuseStep 549217 = 411913) (by norm_num)
theorem B811373 : Blo 539803 811373 := bbase (se 3 (by rfl) ⟨152132, by rfl⟩ : syracuseStep 811373 = 304265) (by norm_num)
theorem B1466741 : Blo 539803 1466741 := bbase (se 5 (by rfl) ⟨68753, by rfl⟩ : syracuseStep 1466741 = 137507) (by norm_num)
theorem B811397 : Blo 539803 811397 := bbase (se 4 (by rfl) ⟨76068, by rfl⟩ : syracuseStep 811397 = 152137) (by norm_num)
theorem B1483157 : Blo 539803 1483157 := bbase (se 6 (by rfl) ⟨34761, by rfl⟩ : syracuseStep 1483157 = 69523) (by norm_num)
theorem B811421 : Blo 539803 811421 := bbase (se 3 (by rfl) ⟨152141, by rfl⟩ : syracuseStep 811421 = 304283) (by norm_num)
theorem B1368485 : Blo 539803 1368485 := bbase (se 4 (by rfl) ⟨128295, by rfl⟩ : syracuseStep 1368485 = 256591) (by norm_num)
theorem B1221029 : Blo 539803 1221029 := bbase (se 4 (by rfl) ⟨114471, by rfl⟩ : syracuseStep 1221029 = 228943) (by norm_num)
theorem B811445 : Blo 539803 811445 := bbase (se 5 (by rfl) ⟨38036, by rfl⟩ : syracuseStep 811445 = 76073) (by norm_num)
theorem B770485 : Blo 539803 770485 := bbase (se 5 (by rfl) ⟨36116, by rfl⟩ : syracuseStep 770485 = 72233) (by norm_num)
theorem B811469 : Blo 539803 811469 := bbase (se 3 (by rfl) ⟨152150, by rfl⟩ : syracuseStep 811469 = 304301) (by norm_num)
theorem B2056661 : Blo 539803 2056661 := bbase (se 7 (by rfl) ⟨24101, by rfl⟩ : syracuseStep 2056661 = 48203) (by norm_num)
theorem B1671637 : Blo 539803 1671637 := bbase (se 7 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 1671637 = 39179) (by norm_num)
theorem B811493 : Blo 539803 811493 := bbase (se 4 (by rfl) ⟨76077, by rfl⟩ : syracuseStep 811493 = 152155) (by norm_num)
theorem B1221101 : Blo 539803 1221101 := bbase (se 3 (by rfl) ⟨228956, by rfl⟩ : syracuseStep 1221101 = 457913) (by norm_num)
theorem B811517 : Blo 539803 811517 := bbase (se 3 (by rfl) ⟨152159, by rfl⟩ : syracuseStep 811517 = 304319) (by norm_num)
theorem B811541 : Blo 539803 811541 := bbase (se 6 (by rfl) ⟨19020, by rfl⟩ : syracuseStep 811541 = 38041) (by norm_num)
theorem B811565 : Blo 539803 811565 := bbase (se 3 (by rfl) ⟨152168, by rfl⟩ : syracuseStep 811565 = 304337) (by norm_num)
theorem B811589 : Blo 539803 811589 := bbase (se 4 (by rfl) ⟨76086, by rfl⟩ : syracuseStep 811589 = 152173) (by norm_num)
theorem B1827413 : Blo 539803 1827413 := bbase (se 8 (by rfl) ⟨10707, by rfl⟩ : syracuseStep 1827413 = 21415) (by norm_num)
theorem B811613 : Blo 539803 811613 := bbase (se 3 (by rfl) ⟨152177, by rfl⟩ : syracuseStep 811613 = 304355) (by norm_num)
theorem B1368677 : Blo 539803 1368677 := bbase (se 4 (by rfl) ⟨128313, by rfl⟩ : syracuseStep 1368677 = 256627) (by norm_num)
theorem B811637 : Blo 539803 811637 := bbase (se 5 (by rfl) ⟨38045, by rfl⟩ : syracuseStep 811637 = 76091) (by norm_num)
theorem B1221245 : Blo 539803 1221245 := bbase (se 3 (by rfl) ⟨228983, by rfl⟩ : syracuseStep 1221245 = 457967) (by norm_num)
theorem B811661 : Blo 539803 811661 := bbase (se 3 (by rfl) ⟨152186, by rfl⟩ : syracuseStep 811661 = 304373) (by norm_num)
theorem B811685 : Blo 539803 811685 := bbase (se 4 (by rfl) ⟨76095, by rfl⟩ : syracuseStep 811685 = 152191) (by norm_num)
theorem B811709 : Blo 539803 811709 := bbase (se 3 (by rfl) ⟨152195, by rfl⟩ : syracuseStep 811709 = 304391) (by norm_num)
theorem B811733 : Blo 539803 811733 := bbase (se 7 (by rfl) ⟨9512, by rfl⟩ : syracuseStep 811733 = 19025) (by norm_num)
theorem B811757 : Blo 539803 811757 := bbase (se 3 (by rfl) ⟨152204, by rfl⟩ : syracuseStep 811757 = 304409) (by norm_num)
theorem B811781 : Blo 539803 811781 := bbase (se 4 (by rfl) ⟨76104, by rfl⟩ : syracuseStep 811781 = 152209) (by norm_num)
theorem B811805 : Blo 539803 811805 := bbase (se 3 (by rfl) ⟨152213, by rfl⟩ : syracuseStep 811805 = 304427) (by norm_num)
theorem B1467173 : Blo 539803 1467173 := bbase (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) (by norm_num)
theorem B811829 : Blo 539803 811829 := bbase (se 5 (by rfl) ⟨38054, by rfl⟩ : syracuseStep 811829 = 76109) (by norm_num)
theorem B811853 : Blo 539803 811853 := bbase (se 3 (by rfl) ⟨152222, by rfl⟩ : syracuseStep 811853 = 304445) (by norm_num)
theorem B811877 : Blo 539803 811877 := bbase (se 4 (by rfl) ⟨76113, by rfl⟩ : syracuseStep 811877 = 152227) (by norm_num)
theorem B877429 : Blo 539803 877429 := bbase (se 5 (by rfl) ⟨41129, by rfl⟩ : syracuseStep 877429 = 82259) (by norm_num)
theorem B2474869 : Blo 539803 2474869 := bbase (se 5 (by rfl) ⟨116009, by rfl⟩ : syracuseStep 2474869 = 232019) (by norm_num)
theorem B811901 : Blo 539803 811901 := bbase (se 3 (by rfl) ⟨152231, by rfl⟩ : syracuseStep 811901 = 304463) (by norm_num)
theorem B811925 : Blo 539803 811925 := bbase (se 6 (by rfl) ⟨19029, by rfl⟩ : syracuseStep 811925 = 38059) (by norm_num)
theorem B1524629 : Blo 539803 1524629 := bbase (se 6 (by rfl) ⟨35733, by rfl⟩ : syracuseStep 1524629 = 71467) (by norm_num)
theorem B811949 : Blo 539803 811949 := bbase (se 3 (by rfl) ⟨152240, by rfl⟩ : syracuseStep 811949 = 304481) (by norm_num)
theorem B549817 : Blo 539803 549817 := bbase (se 2 (by rfl) ⟨206181, by rfl⟩ : syracuseStep 549817 = 412363) (by norm_num)
theorem B1369021 : Blo 539803 1369021 := bbase (se 3 (by rfl) ⟨256691, by rfl⟩ : syracuseStep 1369021 = 513383) (by norm_num)
theorem B1237949 : Blo 539803 1237949 := bbase (se 3 (by rfl) ⟨232115, by rfl⟩ : syracuseStep 1237949 = 464231) (by norm_num)
theorem B811973 : Blo 539803 811973 := bbase (se 4 (by rfl) ⟨76122, by rfl⟩ : syracuseStep 811973 = 152245) (by norm_num)
theorem B811997 : Blo 539803 811997 := bbase (se 3 (by rfl) ⟨152249, by rfl⟩ : syracuseStep 811997 = 304499) (by norm_num)
theorem B1156069 : Blo 539803 1156069 := bbase (se 4 (by rfl) ⟨108381, by rfl⟩ : syracuseStep 1156069 = 216763) (by norm_num)
theorem B812021 : Blo 539803 812021 := bbase (se 5 (by rfl) ⟨38063, by rfl⟩ : syracuseStep 812021 = 76127) (by norm_num)
theorem B771077 : Blo 539803 771077 := bbase (se 4 (by rfl) ⟨72288, by rfl⟩ : syracuseStep 771077 = 144577) (by norm_num)
theorem B1827845 : Blo 539803 1827845 := bbase (se 4 (by rfl) ⟨171360, by rfl⟩ : syracuseStep 1827845 = 342721) (by norm_num)
theorem B812045 : Blo 539803 812045 := bbase (se 3 (by rfl) ⟨152258, by rfl⟩ : syracuseStep 812045 = 304517) (by norm_num)
theorem B812069 : Blo 539803 812069 := bbase (se 4 (by rfl) ⟨76131, by rfl⟩ : syracuseStep 812069 = 152263) (by norm_num)
theorem B1369133 : Blo 539803 1369133 := bbase (se 3 (by rfl) ⟨256712, by rfl⟩ : syracuseStep 1369133 = 513425) (by norm_num)
theorem B812093 : Blo 539803 812093 := bbase (se 3 (by rfl) ⟨152267, by rfl⟩ : syracuseStep 812093 = 304535) (by norm_num)
theorem B607297 : Blo 539803 607297 := bbase (se 2 (by rfl) ⟨227736, by rfl⟩ : syracuseStep 607297 = 455473) (by norm_num)
theorem B730181 : Blo 539803 730181 := bbase (se 4 (by rfl) ⟨68454, by rfl⟩ : syracuseStep 730181 = 136909) (by norm_num)
theorem B2745413 : Blo 539803 2745413 := bbase (se 4 (by rfl) ⟨257382, by rfl⟩ : syracuseStep 2745413 = 514765) (by norm_num)
theorem B812117 : Blo 539803 812117 := bbase (se 8 (by rfl) ⟨4758, by rfl⟩ : syracuseStep 812117 = 9517) (by norm_num)
theorem B771157 : Blo 539803 771157 := bbase (se 8 (by rfl) ⟨4518, by rfl⟩ : syracuseStep 771157 = 9037) (by norm_num)
theorem B1156189 : Blo 539803 1156189 := bbase (se 3 (by rfl) ⟨216785, by rfl⟩ : syracuseStep 1156189 = 433571) (by norm_num)
theorem B607333 : Blo 539803 607333 := bbase (se 4 (by rfl) ⟨56937, by rfl⟩ : syracuseStep 607333 = 113875) (by norm_num)
theorem B812141 : Blo 539803 812141 := bbase (se 3 (by rfl) ⟨152276, by rfl⟩ : syracuseStep 812141 = 304553) (by norm_num)
theorem B1025149 : Blo 539803 1025149 := bbase (se 3 (by rfl) ⟨192215, by rfl⟩ : syracuseStep 1025149 = 384431) (by norm_num)
theorem B812165 : Blo 539803 812165 := bbase (se 4 (by rfl) ⟨76140, by rfl⟩ : syracuseStep 812165 = 152281) (by norm_num)
theorem B607369 : Blo 539803 607369 := bbase (se 2 (by rfl) ⟨227763, by rfl⟩ : syracuseStep 607369 = 455527) (by norm_num)
theorem B8316053 : Blo 539803 8316053 := bbase (se 6 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 8316053 = 389815) (by norm_num)
theorem B812189 : Blo 539803 812189 := bbase (se 3 (by rfl) ⟨152285, by rfl⟩ : syracuseStep 812189 = 304571) (by norm_num)
theorem B607405 : Blo 539803 607405 := bbase (se 3 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 607405 = 227777) (by norm_num)
theorem B812213 : Blo 539803 812213 := bbase (se 5 (by rfl) ⟨38072, by rfl⟩ : syracuseStep 812213 = 76145) (by norm_num)
theorem B812237 : Blo 539803 812237 := bbase (se 3 (by rfl) ⟨152294, by rfl⟩ : syracuseStep 812237 = 304589) (by norm_num)
theorem B771277 : Blo 539803 771277 := bbase (se 3 (by rfl) ⟨144614, by rfl⟩ : syracuseStep 771277 = 289229) (by norm_num)
theorem B607441 : Blo 539803 607441 := bbase (se 2 (by rfl) ⟨227790, by rfl⟩ : syracuseStep 607441 = 455581) (by norm_num)
theorem B812261 : Blo 539803 812261 := bbase (se 4 (by rfl) ⟨76149, by rfl⟩ : syracuseStep 812261 = 152299) (by norm_num)
theorem B1369325 : Blo 539803 1369325 := bbase (se 3 (by rfl) ⟨256748, by rfl⟩ : syracuseStep 1369325 = 513497) (by norm_num)
theorem B1303789 : Blo 539803 1303789 := bbase (se 3 (by rfl) ⟨244460, by rfl⟩ : syracuseStep 1303789 = 488921) (by norm_num)
theorem B607477 : Blo 539803 607477 := bbase (se 5 (by rfl) ⟨28475, by rfl⟩ : syracuseStep 607477 = 56951) (by norm_num)
theorem B812285 : Blo 539803 812285 := bbase (se 3 (by rfl) ⟨152303, by rfl⟩ : syracuseStep 812285 = 304607) (by norm_num)
theorem B1025293 : Blo 539803 1025293 := bbase (se 3 (by rfl) ⟨192242, by rfl⟩ : syracuseStep 1025293 = 384485) (by norm_num)
theorem B812309 : Blo 539803 812309 := bbase (se 6 (by rfl) ⟨19038, by rfl⟩ : syracuseStep 812309 = 38077) (by norm_num)
theorem B607513 : Blo 539803 607513 := bbase (se 2 (by rfl) ⟨227817, by rfl⟩ : syracuseStep 607513 = 455635) (by norm_num)
theorem B812333 : Blo 539803 812333 := bbase (se 3 (by rfl) ⟨152312, by rfl⟩ : syracuseStep 812333 = 304625) (by norm_num)
theorem B771373 : Blo 539803 771373 := bbase (se 3 (by rfl) ⟨144632, by rfl⟩ : syracuseStep 771373 = 289265) (by norm_num)
theorem B648497 : Blo 539803 648497 := bbase (se 2 (by rfl) ⟨243186, by rfl⟩ : syracuseStep 648497 = 486373) (by norm_num)
theorem B2770229 : Blo 539803 2770229 := bbase (se 5 (by rfl) ⟨129854, by rfl⟩ : syracuseStep 2770229 = 259709) (by norm_num)
theorem B607549 : Blo 539803 607549 := bbase (se 3 (by rfl) ⟨113915, by rfl⟩ : syracuseStep 607549 = 227831) (by norm_num)
theorem B812357 : Blo 539803 812357 := bbase (se 4 (by rfl) ⟨76158, by rfl⟩ : syracuseStep 812357 = 152317) (by norm_num)
theorem B1156445 : Blo 539803 1156445 := bbase (se 3 (by rfl) ⟨216833, by rfl⟩ : syracuseStep 1156445 = 433667) (by norm_num)
theorem B812381 : Blo 539803 812381 := bbase (se 3 (by rfl) ⟨152321, by rfl⟩ : syracuseStep 812381 = 304643) (by norm_num)
theorem B607585 : Blo 539803 607585 := bbase (se 2 (by rfl) ⟨227844, by rfl⟩ : syracuseStep 607585 = 455689) (by norm_num)
theorem B812405 : Blo 539803 812405 := bbase (se 5 (by rfl) ⟨38081, by rfl⟩ : syracuseStep 812405 = 76163) (by norm_num)
theorem B607621 : Blo 539803 607621 := bbase (se 4 (by rfl) ⟨56964, by rfl⟩ : syracuseStep 607621 = 113929) (by norm_num)
theorem B812429 : Blo 539803 812429 := bbase (se 3 (by rfl) ⟨152330, by rfl⟩ : syracuseStep 812429 = 304661) (by norm_num)
theorem B2598293 : Blo 539803 2598293 := bbase (se 6 (by rfl) ⟨60897, by rfl⟩ : syracuseStep 2598293 = 121795) (by norm_num)
theorem B1099165 : Blo 539803 1099165 := bbase (se 3 (by rfl) ⟨206093, by rfl⟩ : syracuseStep 1099165 = 412187) (by norm_num)
theorem B812453 : Blo 539803 812453 := bbase (se 4 (by rfl) ⟨76167, by rfl⟩ : syracuseStep 812453 = 152335) (by norm_num)
theorem B607657 : Blo 539803 607657 := bbase (se 2 (by rfl) ⟨227871, by rfl⟩ : syracuseStep 607657 = 455743) (by norm_num)
theorem B1025453 : Blo 539803 1025453 := bbase (se 3 (by rfl) ⟨192272, by rfl⟩ : syracuseStep 1025453 = 384545) (by norm_num)
theorem B1828277 : Blo 539803 1828277 := bbase (se 5 (by rfl) ⟨85700, by rfl⟩ : syracuseStep 1828277 = 171401) (by norm_num)
theorem B812477 : Blo 539803 812477 := bbase (se 3 (by rfl) ⟨152339, by rfl⟩ : syracuseStep 812477 = 304679) (by norm_num)
theorem B607693 : Blo 539803 607693 := bbase (se 3 (by rfl) ⟨113942, by rfl⟩ : syracuseStep 607693 = 227885) (by norm_num)
theorem B1459669 : Blo 539803 1459669 := bbase (se 7 (by rfl) ⟨17105, by rfl⟩ : syracuseStep 1459669 = 34211) (by norm_num)
theorem B812501 : Blo 539803 812501 := bbase (se 7 (by rfl) ⟨9521, by rfl⟩ : syracuseStep 812501 = 19043) (by norm_num)
theorem B2737637 : Blo 539803 2737637 := bbase (se 4 (by rfl) ⟨256653, by rfl⟩ : syracuseStep 2737637 = 513307) (by norm_num)
theorem B812525 : Blo 539803 812525 := bbase (se 3 (by rfl) ⟨152348, by rfl⟩ : syracuseStep 812525 = 304697) (by norm_num)
theorem B607729 : Blo 539803 607729 := bbase (se 2 (by rfl) ⟨227898, by rfl⟩ : syracuseStep 607729 = 455797) (by norm_num)
theorem B2598389 : Blo 539803 2598389 := bbase (se 5 (by rfl) ⟨121799, by rfl⟩ : syracuseStep 2598389 = 243599) (by norm_num)
theorem B812549 : Blo 539803 812549 := bbase (se 4 (by rfl) ⟨76176, by rfl⟩ : syracuseStep 812549 = 152353) (by norm_num)
theorem B607765 : Blo 539803 607765 := bbase (se 6 (by rfl) ⟨14244, by rfl⟩ : syracuseStep 607765 = 28489) (by norm_num)
theorem B812573 : Blo 539803 812573 := bbase (se 3 (by rfl) ⟨152357, by rfl⟩ : syracuseStep 812573 = 304715) (by norm_num)
theorem B812597 : Blo 539803 812597 := bbase (se 5 (by rfl) ⟨38090, by rfl⟩ : syracuseStep 812597 = 76181) (by norm_num)
theorem B607801 : Blo 539803 607801 := bbase (se 2 (by rfl) ⟨227925, by rfl⟩ : syracuseStep 607801 = 455851) (by norm_num)
theorem B1025597 : Blo 539803 1025597 := bbase (se 3 (by rfl) ⟨192299, by rfl⟩ : syracuseStep 1025597 = 384599) (by norm_num)
theorem B1369669 : Blo 539803 1369669 := bbase (se 4 (by rfl) ⟨128406, by rfl⟩ : syracuseStep 1369669 = 256813) (by norm_num)
theorem B812621 : Blo 539803 812621 := bbase (se 3 (by rfl) ⟨152366, by rfl⟩ : syracuseStep 812621 = 304733) (by norm_num)
theorem B5203541 : Blo 539803 5203541 := bbase (se 8 (by rfl) ⟨30489, by rfl⟩ : syracuseStep 5203541 = 60979) (by norm_num)
theorem B607837 : Blo 539803 607837 := bbase (se 3 (by rfl) ⟨113969, by rfl⟩ : syracuseStep 607837 = 227939) (by norm_num)
theorem B648805 : Blo 539803 648805 := bbase (se 4 (by rfl) ⟨60825, by rfl⟩ : syracuseStep 648805 = 121651) (by norm_num)
theorem B812645 : Blo 539803 812645 := bbase (se 4 (by rfl) ⟨76185, by rfl⟩ : syracuseStep 812645 = 152371) (by norm_num)
theorem B3892853 : Blo 539803 3892853 := bbase (se 5 (by rfl) ⟨182477, by rfl⟩ : syracuseStep 3892853 = 364955) (by norm_num)
theorem B2057845 : Blo 539803 2057845 := bbase (se 5 (by rfl) ⟨96461, by rfl⟩ : syracuseStep 2057845 = 192923) (by norm_num)
theorem B910973 : Blo 539803 910973 := bbase (se 3 (by rfl) ⟨170807, by rfl⟩ : syracuseStep 910973 = 341615) (by norm_num)
theorem B812669 : Blo 539803 812669 := bbase (se 3 (by rfl) ⟨152375, by rfl⟩ : syracuseStep 812669 = 304751) (by norm_num)
theorem B607873 : Blo 539803 607873 := bbase (se 2 (by rfl) ⟨227952, by rfl⟩ : syracuseStep 607873 = 455905) (by norm_num)
theorem B9242261 : Blo 539803 9242261 := bbase (se 6 (by rfl) ⟨216615, by rfl⟩ : syracuseStep 9242261 = 433231) (by norm_num)
theorem B812693 : Blo 539803 812693 := bbase (se 6 (by rfl) ⟨19047, by rfl⟩ : syracuseStep 812693 = 38095) (by norm_num)
theorem B820901 : Blo 539803 820901 := bbase (se 4 (by rfl) ⟨76959, by rfl⟩ : syracuseStep 820901 = 153919) (by norm_num)
theorem B607909 : Blo 539803 607909 := bbase (se 4 (by rfl) ⟨56991, by rfl⟩ : syracuseStep 607909 = 113983) (by norm_num)
theorem B812717 : Blo 539803 812717 := bbase (se 3 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 812717 = 304769) (by norm_num)
theorem B4635893 : Blo 539803 4635893 := bbase (se 5 (by rfl) ⟨217307, by rfl⟩ : syracuseStep 4635893 = 434615) (by norm_num)
theorem B1369781 : Blo 539803 1369781 := bbase (se 5 (by rfl) ⟨64208, by rfl⟩ : syracuseStep 1369781 = 128417) (by norm_num)
theorem B976573 : Blo 539803 976573 := bbase (se 3 (by rfl) ⟨183107, by rfl⟩ : syracuseStep 976573 = 366215) (by norm_num)
theorem B812741 : Blo 539803 812741 := bbase (se 4 (by rfl) ⟨76194, by rfl⟩ : syracuseStep 812741 = 152389) (by norm_num)
theorem B648905 : Blo 539803 648905 := bbase (se 2 (by rfl) ⟨243339, by rfl⟩ : syracuseStep 648905 = 486679) (by norm_num)
theorem B607945 : Blo 539803 607945 := bbase (se 2 (by rfl) ⟨227979, by rfl⟩ : syracuseStep 607945 = 455959) (by norm_num)
theorem B812765 : Blo 539803 812765 := bbase (se 3 (by rfl) ⟨152393, by rfl⟩ : syracuseStep 812765 = 304787) (by norm_num)
theorem B607981 : Blo 539803 607981 := bbase (se 3 (by rfl) ⟨113996, by rfl⟩ : syracuseStep 607981 = 227993) (by norm_num)
theorem B812789 : Blo 539803 812789 := bbase (se 5 (by rfl) ⟨38099, by rfl⟩ : syracuseStep 812789 = 76199) (by norm_num)
theorem B1189621 : Blo 539803 1189621 := bbase (se 5 (by rfl) ⟨55763, by rfl⟩ : syracuseStep 1189621 = 111527) (by norm_num)
theorem B911101 : Blo 539803 911101 := bbase (se 3 (by rfl) ⟨170831, by rfl⟩ : syracuseStep 911101 = 341663) (by norm_num)
theorem B812813 : Blo 539803 812813 := bbase (se 3 (by rfl) ⟨152402, by rfl⟩ : syracuseStep 812813 = 304805) (by norm_num)
theorem B608017 : Blo 539803 608017 := bbase (se 2 (by rfl) ⟨228006, by rfl⟩ : syracuseStep 608017 = 456013) (by norm_num)
theorem B771869 : Blo 539803 771869 := bbase (se 3 (by rfl) ⟨144725, by rfl⟩ : syracuseStep 771869 = 289451) (by norm_num)
theorem B812837 : Blo 539803 812837 := bbase (se 4 (by rfl) ⟨76203, by rfl⟩ : syracuseStep 812837 = 152407) (by norm_num)
theorem B608053 : Blo 539803 608053 := bbase (se 5 (by rfl) ⟨28502, by rfl⟩ : syracuseStep 608053 = 57005) (by norm_num)
theorem B812861 : Blo 539803 812861 := bbase (se 3 (by rfl) ⟨152411, by rfl⟩ : syracuseStep 812861 = 304823) (by norm_num)
theorem B911189 : Blo 539803 911189 := bbase (se 9 (by rfl) ⟨2669, by rfl⟩ : syracuseStep 911189 = 5339) (by norm_num)
theorem B812885 : Blo 539803 812885 := bbase (se 9 (by rfl) ⟨2381, by rfl⟩ : syracuseStep 812885 = 4763) (by norm_num)
theorem B608089 : Blo 539803 608089 := bbase (se 2 (by rfl) ⟨228033, by rfl⟩ : syracuseStep 608089 = 456067) (by norm_num)
theorem B1025885 : Blo 539803 1025885 := bbase (se 3 (by rfl) ⟨192353, by rfl⟩ : syracuseStep 1025885 = 384707) (by norm_num)
theorem B1828709 : Blo 539803 1828709 := bbase (se 4 (by rfl) ⟨171441, by rfl⟩ : syracuseStep 1828709 = 342883) (by norm_num)
theorem B812909 : Blo 539803 812909 := bbase (se 3 (by rfl) ⟨152420, by rfl⟩ : syracuseStep 812909 = 304841) (by norm_num)
theorem B1369973 : Blo 539803 1369973 := bbase (se 5 (by rfl) ⟨64217, by rfl⟩ : syracuseStep 1369973 = 128435) (by norm_num)
theorem B608125 : Blo 539803 608125 := bbase (se 3 (by rfl) ⟨114023, by rfl⟩ : syracuseStep 608125 = 228047) (by norm_num)
theorem B812933 : Blo 539803 812933 := bbase (se 4 (by rfl) ⟨76212, by rfl⟩ : syracuseStep 812933 = 152425) (by norm_num)
theorem B812957 : Blo 539803 812957 := bbase (se 3 (by rfl) ⟨152429, by rfl⟩ : syracuseStep 812957 = 304859) (by norm_num)
theorem B608161 : Blo 539803 608161 := bbase (se 2 (by rfl) ⟨228060, by rfl⟩ : syracuseStep 608161 = 456121) (by norm_num)
theorem B2058149 : Blo 539803 2058149 := bbase (se 4 (by rfl) ⟨192951, by rfl⟩ : syracuseStep 2058149 = 385903) (by norm_num)
theorem B812981 : Blo 539803 812981 := bbase (se 5 (by rfl) ⟨38108, by rfl⟩ : syracuseStep 812981 = 76217) (by norm_num)
theorem B608197 : Blo 539803 608197 := bbase (se 4 (by rfl) ⟨57018, by rfl⟩ : syracuseStep 608197 = 114037) (by norm_num)
theorem B813005 : Blo 539803 813005 := bbase (se 3 (by rfl) ⟨152438, by rfl⟩ : syracuseStep 813005 = 304877) (by norm_num)
theorem B911317 : Blo 539803 911317 := bbase (se 7 (by rfl) ⟨10679, by rfl⟩ : syracuseStep 911317 = 21359) (by norm_num)
theorem B813029 : Blo 539803 813029 := bbase (se 4 (by rfl) ⟨76221, by rfl⟩ : syracuseStep 813029 = 152443) (by norm_num)
theorem B608233 : Blo 539803 608233 := bbase (se 2 (by rfl) ⟨228087, by rfl⟩ : syracuseStep 608233 = 456175) (by norm_num)
theorem B1026037 : Blo 539803 1026037 := bbase (se 5 (by rfl) ⟨48095, by rfl⟩ : syracuseStep 1026037 = 96191) (by norm_num)
theorem B813053 : Blo 539803 813053 := bbase (se 3 (by rfl) ⟨152447, by rfl⟩ : syracuseStep 813053 = 304895) (by norm_num)
theorem B608269 : Blo 539803 608269 := bbase (se 3 (by rfl) ⟨114050, by rfl⟩ : syracuseStep 608269 = 228101) (by norm_num)
theorem B2050069 : Blo 539803 2050069 := bbase (se 6 (by rfl) ⟨48048, by rfl⟩ : syracuseStep 2050069 = 96097) (by norm_num)
theorem B3467285 : Blo 539803 3467285 := bbase (se 6 (by rfl) ⟨81264, by rfl⟩ : syracuseStep 3467285 = 162529) (by norm_num)
theorem B6252565 : Blo 539803 6252565 := bbase (se 6 (by rfl) ⟨146544, by rfl⟩ : syracuseStep 6252565 = 293089) (by norm_num)
theorem B813077 : Blo 539803 813077 := bbase (se 6 (by rfl) ⟨19056, by rfl⟩ : syracuseStep 813077 = 38113) (by norm_num)
theorem B1173541 : Blo 539803 1173541 := bbase (se 4 (by rfl) ⟨110019, by rfl⟩ : syracuseStep 1173541 = 220039) (by norm_num)
theorem B911405 : Blo 539803 911405 := bbase (se 3 (by rfl) ⟨170888, by rfl⟩ : syracuseStep 911405 = 341777) (by norm_num)
theorem B813101 : Blo 539803 813101 := bbase (se 3 (by rfl) ⟨152456, by rfl⟩ : syracuseStep 813101 = 304913) (by norm_num)
theorem B608305 : Blo 539803 608305 := bbase (se 2 (by rfl) ⟨228114, by rfl⟩ : syracuseStep 608305 = 456229) (by norm_num)
theorem B813125 : Blo 539803 813125 := bbase (se 4 (by rfl) ⟨76230, by rfl⟩ : syracuseStep 813125 = 152461) (by norm_num)
theorem B608341 : Blo 539803 608341 := bbase (se 8 (by rfl) ⟨3564, by rfl⟩ : syracuseStep 608341 = 7129) (by norm_num)
theorem B649309 : Blo 539803 649309 := bbase (se 3 (by rfl) ⟨121745, by rfl⟩ : syracuseStep 649309 = 243491) (by norm_num)
theorem B813149 : Blo 539803 813149 := bbase (se 3 (by rfl) ⟨152465, by rfl⟩ : syracuseStep 813149 = 304931) (by norm_num)
theorem B813173 : Blo 539803 813173 := bbase (se 5 (by rfl) ⟨38117, by rfl⟩ : syracuseStep 813173 = 76235) (by norm_num)
theorem B608377 : Blo 539803 608377 := bbase (se 2 (by rfl) ⟨228141, by rfl⟩ : syracuseStep 608377 = 456283) (by norm_num)
theorem B813197 : Blo 539803 813197 := bbase (se 3 (by rfl) ⟨152474, by rfl⟩ : syracuseStep 813197 = 304949) (by norm_num)
theorem B1214621 : Blo 539803 1214621 := bbase (se 3 (by rfl) ⟨227741, by rfl⟩ : syracuseStep 1214621 = 455483) (by norm_num)
theorem B608413 : Blo 539803 608413 := bbase (se 3 (by rfl) ⟨114077, by rfl⟩ : syracuseStep 608413 = 228155) (by norm_num)
theorem B813221 : Blo 539803 813221 := bbase (se 4 (by rfl) ⟨76239, by rfl⟩ : syracuseStep 813221 = 152479) (by norm_num)
theorem B911533 : Blo 539803 911533 := bbase (se 3 (by rfl) ⟨170912, by rfl⟩ : syracuseStep 911533 = 341825) (by norm_num)
theorem B813245 : Blo 539803 813245 := bbase (se 3 (by rfl) ⟨152483, by rfl⟩ : syracuseStep 813245 = 304967) (by norm_num)
theorem B608449 : Blo 539803 608449 := bbase (se 2 (by rfl) ⟨228168, by rfl⟩ : syracuseStep 608449 = 456337) (by norm_num)
theorem B1370317 : Blo 539803 1370317 := bbase (se 3 (by rfl) ⟨256934, by rfl⟩ : syracuseStep 1370317 = 513869) (by norm_num)
theorem B1157333 : Blo 539803 1157333 := bbase (se 7 (by rfl) ⟨13562, by rfl⟩ : syracuseStep 1157333 = 27125) (by norm_num)
theorem B813269 : Blo 539803 813269 := bbase (se 7 (by rfl) ⟨9530, by rfl⟩ : syracuseStep 813269 = 19061) (by norm_num)
theorem B1214693 : Blo 539803 1214693 := bbase (se 4 (by rfl) ⟨113877, by rfl⟩ : syracuseStep 1214693 = 227755) (by norm_num)
theorem B608485 : Blo 539803 608485 := bbase (se 4 (by rfl) ⟨57045, by rfl⟩ : syracuseStep 608485 = 114091) (by norm_num)
theorem B813293 : Blo 539803 813293 := bbase (se 3 (by rfl) ⟨152492, by rfl⟩ : syracuseStep 813293 = 304985) (by norm_num)
theorem B911621 : Blo 539803 911621 := bbase (se 4 (by rfl) ⟨85464, by rfl⟩ : syracuseStep 911621 = 170929) (by norm_num)
theorem B813317 : Blo 539803 813317 := bbase (se 4 (by rfl) ⟨76248, by rfl⟩ : syracuseStep 813317 = 152497) (by norm_num)
theorem B608521 : Blo 539803 608521 := bbase (se 2 (by rfl) ⟨228195, by rfl⟩ : syracuseStep 608521 = 456391) (by norm_num)
theorem B1829141 : Blo 539803 1829141 := bbase (se 6 (by rfl) ⟨42870, by rfl⟩ : syracuseStep 1829141 = 85741) (by norm_num)
theorem B813341 : Blo 539803 813341 := bbase (se 3 (by rfl) ⟨152501, by rfl⟩ : syracuseStep 813341 = 305003) (by norm_num)
theorem B1026341 : Blo 539803 1026341 := bbase (se 4 (by rfl) ⟨96219, by rfl⟩ : syracuseStep 1026341 = 192439) (by norm_num)
theorem B1214765 : Blo 539803 1214765 := bbase (se 3 (by rfl) ⟨227768, by rfl⟩ : syracuseStep 1214765 = 455537) (by norm_num)
theorem B608557 : Blo 539803 608557 := bbase (se 3 (by rfl) ⟨114104, by rfl⟩ : syracuseStep 608557 = 228209) (by norm_num)
theorem B813365 : Blo 539803 813365 := bbase (se 5 (by rfl) ⟨38126, by rfl⟩ : syracuseStep 813365 = 76253) (by norm_num)
theorem B1370429 : Blo 539803 1370429 := bbase (se 3 (by rfl) ⟨256955, by rfl⟩ : syracuseStep 1370429 = 513911) (by norm_num)
theorem B2050373 : Blo 539803 2050373 := bbase (se 4 (by rfl) ⟨192222, by rfl⟩ : syracuseStep 2050373 = 384445) (by norm_num)
theorem B772421 : Blo 539803 772421 := bbase (se 4 (by rfl) ⟨72414, by rfl⟩ : syracuseStep 772421 = 144829) (by norm_num)
theorem B813389 : Blo 539803 813389 := bbase (se 3 (by rfl) ⟨152510, by rfl⟩ : syracuseStep 813389 = 305021) (by norm_num)
theorem B608593 : Blo 539803 608593 := bbase (se 2 (by rfl) ⟨228222, by rfl⟩ : syracuseStep 608593 = 456445) (by norm_num)
theorem B2746709 : Blo 539803 2746709 := bbase (se 10 (by rfl) ⟨4023, by rfl⟩ : syracuseStep 2746709 = 8047) (by norm_num)
theorem B2312549 : Blo 539803 2312549 := bbase (se 4 (by rfl) ⟨216801, by rfl⟩ : syracuseStep 2312549 = 433603) (by norm_num)
theorem B813413 : Blo 539803 813413 := bbase (se 4 (by rfl) ⟨76257, by rfl⟩ : syracuseStep 813413 = 152515) (by norm_num)
theorem B1214837 : Blo 539803 1214837 := bbase (se 5 (by rfl) ⟨56945, by rfl⟩ : syracuseStep 1214837 = 113891) (by norm_num)
theorem B2107765 : Blo 539803 2107765 := bbase (se 5 (by rfl) ⟨98801, by rfl⟩ : syracuseStep 2107765 = 197603) (by norm_num)
theorem B4385141 : Blo 539803 4385141 := bbase (se 5 (by rfl) ⟨205553, by rfl⟩ : syracuseStep 4385141 = 411107) (by norm_num)
theorem B608629 : Blo 539803 608629 := bbase (se 5 (by rfl) ⟨28529, by rfl⟩ : syracuseStep 608629 = 57059) (by norm_num)
theorem B616829 : Blo 539803 616829 := bbase (se 3 (by rfl) ⟨115655, by rfl⟩ : syracuseStep 616829 = 231311) (by norm_num)
theorem B813437 : Blo 539803 813437 := bbase (se 3 (by rfl) ⟨152519, by rfl⟩ : syracuseStep 813437 = 305039) (by norm_num)
theorem B911749 : Blo 539803 911749 := bbase (se 4 (by rfl) ⟨85476, by rfl⟩ : syracuseStep 911749 = 170953) (by norm_num)
theorem B1730965 : Blo 539803 1730965 := bbase (se 6 (by rfl) ⟨40569, by rfl⟩ : syracuseStep 1730965 = 81139) (by norm_num)
theorem B813461 : Blo 539803 813461 := bbase (se 6 (by rfl) ⟨19065, by rfl⟩ : syracuseStep 813461 = 38131) (by norm_num)
theorem B608665 : Blo 539803 608665 := bbase (se 2 (by rfl) ⟨228249, by rfl⟩ : syracuseStep 608665 = 456499) (by norm_num)
theorem B731549 : Blo 539803 731549 := bbase (se 3 (by rfl) ⟨137165, by rfl⟩ : syracuseStep 731549 = 274331) (by norm_num)
theorem B813485 : Blo 539803 813485 := bbase (se 3 (by rfl) ⟨152528, by rfl⟩ : syracuseStep 813485 = 305057) (by norm_num)
theorem B2574773 : Blo 539803 2574773 := bbase (se 5 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 2574773 = 241385) (by norm_num)
theorem B1321397 : Blo 539803 1321397 := bbase (se 5 (by rfl) ⟨61940, by rfl⟩ : syracuseStep 1321397 = 123881) (by norm_num)
theorem B1214909 : Blo 539803 1214909 := bbase (se 3 (by rfl) ⟨227795, by rfl⟩ : syracuseStep 1214909 = 455591) (by norm_num)
theorem B608701 : Blo 539803 608701 := bbase (se 3 (by rfl) ⟨114131, by rfl⟩ : syracuseStep 608701 = 228263) (by norm_num)
theorem B1157573 : Blo 539803 1157573 := bbase (se 4 (by rfl) ⟨108522, by rfl⟩ : syracuseStep 1157573 = 217045) (by norm_num)
theorem B813509 : Blo 539803 813509 := bbase (se 4 (by rfl) ⟨76266, by rfl⟩ : syracuseStep 813509 = 152533) (by norm_num)
theorem B977365 : Blo 539803 977365 := bbase (se 7 (by rfl) ⟨11453, by rfl⟩ : syracuseStep 977365 = 22907) (by norm_num)
theorem B3090869 : Blo 539803 3090869 := bbase (se 5 (by rfl) ⟨144884, by rfl⟩ : syracuseStep 3090869 = 289769) (by norm_num)
theorem B911837 : Blo 539803 911837 := bbase (se 3 (by rfl) ⟨170969, by rfl⟩ : syracuseStep 911837 = 341939) (by norm_num)
theorem B649693 : Blo 539803 649693 := bbase (se 3 (by rfl) ⟨121817, by rfl⟩ : syracuseStep 649693 = 243635) (by norm_num)
theorem B813533 : Blo 539803 813533 := bbase (se 3 (by rfl) ⟨152537, by rfl⟩ : syracuseStep 813533 = 305075) (by norm_num)
theorem B608737 : Blo 539803 608737 := bbase (se 2 (by rfl) ⟨228276, by rfl⟩ : syracuseStep 608737 = 456553) (by norm_num)
theorem B813557 : Blo 539803 813557 := bbase (se 5 (by rfl) ⟨38135, by rfl⟩ : syracuseStep 813557 = 76271) (by norm_num)
theorem B1370621 : Blo 539803 1370621 := bbase (se 3 (by rfl) ⟨256991, by rfl⟩ : syracuseStep 1370621 = 513983) (by norm_num)
theorem B1214981 : Blo 539803 1214981 := bbase (se 4 (by rfl) ⟨113904, by rfl⟩ : syracuseStep 1214981 = 227809) (by norm_num)
theorem B608773 : Blo 539803 608773 := bbase (se 4 (by rfl) ⟨57072, by rfl⟩ : syracuseStep 608773 = 114145) (by norm_num)
theorem B813581 : Blo 539803 813581 := bbase (se 3 (by rfl) ⟨152546, by rfl⟩ : syracuseStep 813581 = 305093) (by norm_num)
theorem B6162965 : Blo 539803 6162965 := bbase (se 6 (by rfl) ⟨144444, by rfl⟩ : syracuseStep 6162965 = 288889) (by norm_num)
theorem B813605 : Blo 539803 813605 := bbase (se 4 (by rfl) ⟨76275, by rfl⟩ : syracuseStep 813605 = 152551) (by norm_num)
theorem B608809 : Blo 539803 608809 := bbase (se 2 (by rfl) ⟨228303, by rfl⟩ : syracuseStep 608809 = 456607) (by norm_num)
theorem B3082805 : Blo 539803 3082805 := bbase (se 5 (by rfl) ⟨144506, by rfl⟩ : syracuseStep 3082805 = 289013) (by norm_num)
theorem B813629 : Blo 539803 813629 := bbase (se 3 (by rfl) ⟨152555, by rfl⟩ : syracuseStep 813629 = 305111) (by norm_num)
theorem B1215053 : Blo 539803 1215053 := bbase (se 3 (by rfl) ⟨227822, by rfl⟩ : syracuseStep 1215053 = 455645) (by norm_num)
theorem B608845 : Blo 539803 608845 := bbase (se 3 (by rfl) ⟨114158, by rfl⟩ : syracuseStep 608845 = 228317) (by norm_num)
theorem B813653 : Blo 539803 813653 := bbase (se 8 (by rfl) ⟨4767, by rfl⟩ : syracuseStep 813653 = 9535) (by norm_num)
theorem B911965 : Blo 539803 911965 := bbase (se 3 (by rfl) ⟨170993, by rfl⟩ : syracuseStep 911965 = 341987) (by norm_num)
theorem B813677 : Blo 539803 813677 := bbase (se 3 (by rfl) ⟨152564, by rfl⟩ : syracuseStep 813677 = 305129) (by norm_num)
theorem B608881 : Blo 539803 608881 := bbase (se 2 (by rfl) ⟨228330, by rfl⟩ : syracuseStep 608881 = 456661) (by norm_num)
theorem B813701 : Blo 539803 813701 := bbase (se 4 (by rfl) ⟨76284, by rfl⟩ : syracuseStep 813701 = 152569) (by norm_num)
theorem B1215125 : Blo 539803 1215125 := bbase (se 6 (by rfl) ⟨28479, by rfl⟩ : syracuseStep 1215125 = 56959) (by norm_num)
theorem B608917 : Blo 539803 608917 := bbase (se 6 (by rfl) ⟨14271, by rfl⟩ : syracuseStep 608917 = 28543) (by norm_num)
theorem B813725 : Blo 539803 813725 := bbase (se 3 (by rfl) ⟨152573, by rfl⟩ : syracuseStep 813725 = 305147) (by norm_num)
theorem B912053 : Blo 539803 912053 := bbase (se 5 (by rfl) ⟨42752, by rfl⟩ : syracuseStep 912053 = 85505) (by norm_num)
theorem B813749 : Blo 539803 813749 := bbase (se 5 (by rfl) ⟨38144, by rfl⟩ : syracuseStep 813749 = 76289) (by norm_num)
theorem B608953 : Blo 539803 608953 := bbase (se 2 (by rfl) ⟨228357, by rfl⟩ : syracuseStep 608953 = 456715) (by norm_num)
theorem B1829573 : Blo 539803 1829573 := bbase (se 4 (by rfl) ⟨171522, by rfl⟩ : syracuseStep 1829573 = 343045) (by norm_num)
theorem B813773 : Blo 539803 813773 := bbase (se 3 (by rfl) ⟨152582, by rfl⟩ : syracuseStep 813773 = 305165) (by norm_num)
theorem B3517141 : Blo 539803 3517141 := bbase (se 7 (by rfl) ⟨41216, by rfl⟩ : syracuseStep 3517141 = 82433) (by norm_num)
theorem B1215197 : Blo 539803 1215197 := bbase (se 3 (by rfl) ⟨227849, by rfl⟩ : syracuseStep 1215197 = 455699) (by norm_num)
theorem B608989 : Blo 539803 608989 := bbase (se 3 (by rfl) ⟨114185, by rfl⟩ : syracuseStep 608989 = 228371) (by norm_num)
theorem B813797 : Blo 539803 813797 := bbase (se 4 (by rfl) ⟨76293, by rfl⟩ : syracuseStep 813797 = 152587) (by norm_num)
theorem B2738933 : Blo 539803 2738933 := bbase (se 5 (by rfl) ⟨128387, by rfl⟩ : syracuseStep 2738933 = 256775) (by norm_num)
theorem B813821 : Blo 539803 813821 := bbase (se 3 (by rfl) ⟨152591, by rfl⟩ : syracuseStep 813821 = 305183) (by norm_num)
theorem B609025 : Blo 539803 609025 := bbase (se 2 (by rfl) ⟨228384, by rfl⟩ : syracuseStep 609025 = 456769) (by norm_num)
theorem B813845 : Blo 539803 813845 := bbase (se 6 (by rfl) ⟨19074, by rfl⟩ : syracuseStep 813845 = 38149) (by norm_num)
theorem B1215269 : Blo 539803 1215269 := bbase (se 4 (by rfl) ⟨113931, by rfl⟩ : syracuseStep 1215269 = 227863) (by norm_num)
theorem B609061 : Blo 539803 609061 := bbase (se 4 (by rfl) ⟨57099, by rfl⟩ : syracuseStep 609061 = 114199) (by norm_num)
theorem B658217 : Blo 539803 658217 := bbase (se 2 (by rfl) ⟨246831, by rfl⟩ : syracuseStep 658217 = 493663) (by norm_num)
theorem B813869 : Blo 539803 813869 := bbase (se 3 (by rfl) ⟨152600, by rfl⟩ : syracuseStep 813869 = 305201) (by norm_num)
theorem B912181 : Blo 539803 912181 := bbase (se 5 (by rfl) ⟨42758, by rfl⟩ : syracuseStep 912181 = 85517) (by norm_num)
theorem B813893 : Blo 539803 813893 := bbase (se 4 (by rfl) ⟨76302, by rfl⟩ : syracuseStep 813893 = 152605) (by norm_num)
theorem B609097 : Blo 539803 609097 := bbase (se 2 (by rfl) ⟨228411, by rfl⟩ : syracuseStep 609097 = 456823) (by norm_num)
theorem B977741 : Blo 539803 977741 := bbase (se 3 (by rfl) ⟨183326, by rfl⟩ : syracuseStep 977741 = 366653) (by norm_num)
theorem B1370965 : Blo 539803 1370965 := bbase (se 9 (by rfl) ⟨4016, by rfl⟩ : syracuseStep 1370965 = 8033) (by norm_num)
theorem B813917 : Blo 539803 813917 := bbase (se 3 (by rfl) ⟨152609, by rfl⟩ : syracuseStep 813917 = 305219) (by norm_num)
theorem B1215341 : Blo 539803 1215341 := bbase (se 3 (by rfl) ⟨227876, by rfl⟩ : syracuseStep 1215341 = 455753) (by norm_num)
theorem B609133 : Blo 539803 609133 := bbase (se 3 (by rfl) ⟨114212, by rfl⟩ : syracuseStep 609133 = 228425) (by norm_num)
theorem B813941 : Blo 539803 813941 := bbase (se 5 (by rfl) ⟨38153, by rfl⟩ : syracuseStep 813941 = 76307) (by norm_num)
theorem B732029 : Blo 539803 732029 := bbase (se 3 (by rfl) ⟨137255, by rfl⟩ : syracuseStep 732029 = 274511) (by norm_num)
theorem B912269 : Blo 539803 912269 := bbase (se 3 (by rfl) ⟨171050, by rfl⟩ : syracuseStep 912269 = 342101) (by norm_num)
theorem B813965 : Blo 539803 813965 := bbase (se 3 (by rfl) ⟨152618, by rfl⟩ : syracuseStep 813965 = 305237) (by norm_num)
theorem B609169 : Blo 539803 609169 := bbase (se 2 (by rfl) ⟨228438, by rfl⟩ : syracuseStep 609169 = 456877) (by norm_num)
theorem B1297301 : Blo 539803 1297301 := bbase (se 6 (by rfl) ⟨30405, by rfl⟩ : syracuseStep 1297301 = 60811) (by norm_num)
theorem B813989 : Blo 539803 813989 := bbase (se 4 (by rfl) ⟨76311, by rfl⟩ : syracuseStep 813989 = 152623) (by norm_num)
theorem B1215413 : Blo 539803 1215413 := bbase (se 5 (by rfl) ⟨56972, by rfl⟩ : syracuseStep 1215413 = 113945) (by norm_num)
theorem B609205 : Blo 539803 609205 := bbase (se 5 (by rfl) ⟨28556, by rfl⟩ : syracuseStep 609205 = 57113) (by norm_num)
theorem B1158077 : Blo 539803 1158077 := bbase (se 3 (by rfl) ⟨217139, by rfl⟩ : syracuseStep 1158077 = 434279) (by norm_num)
theorem B814013 : Blo 539803 814013 := bbase (se 3 (by rfl) ⟨152627, by rfl⟩ : syracuseStep 814013 = 305255) (by norm_num)
theorem B1371077 : Blo 539803 1371077 := bbase (se 4 (by rfl) ⟨128538, by rfl⟩ : syracuseStep 1371077 = 257077) (by norm_num)
theorem B1158085 : Blo 539803 1158085 := bbase (se 4 (by rfl) ⟨108570, by rfl⟩ : syracuseStep 1158085 = 217141) (by norm_num)
theorem B3959765 : Blo 539803 3959765 := bbase (se 7 (by rfl) ⟨46403, by rfl⟩ : syracuseStep 3959765 = 92807) (by norm_num)
theorem B609241 : Blo 539803 609241 := bbase (se 2 (by rfl) ⟨228465, by rfl⟩ : syracuseStep 609241 = 456931) (by norm_num)
theorem B814061 : Blo 539803 814061 := bbase (se 3 (by rfl) ⟨152636, by rfl⟩ : syracuseStep 814061 = 305273) (by norm_num)
theorem B576497 : Blo 539803 576497 := bbase (se 2 (by rfl) ⟨216186, by rfl⟩ : syracuseStep 576497 = 432373) (by norm_num)
theorem B1543157 : Blo 539803 1543157 := bbase (se 5 (by rfl) ⟨72335, by rfl⟩ : syracuseStep 1543157 = 144671) (by norm_num)
theorem B1215485 : Blo 539803 1215485 := bbase (se 3 (by rfl) ⟨227903, by rfl⟩ : syracuseStep 1215485 = 455807) (by norm_num)
theorem B609277 : Blo 539803 609277 := bbase (se 3 (by rfl) ⟨114239, by rfl⟩ : syracuseStep 609277 = 228479) (by norm_num)
theorem B814085 : Blo 539803 814085 := bbase (se 4 (by rfl) ⟨76320, by rfl⟩ : syracuseStep 814085 = 152641) (by norm_num)
theorem B658441 : Blo 539803 658441 := bbase (se 2 (by rfl) ⟨246915, by rfl⟩ : syracuseStep 658441 = 493831) (by norm_num)
theorem B912397 : Blo 539803 912397 := bbase (se 3 (by rfl) ⟨171074, by rfl⟩ : syracuseStep 912397 = 342149) (by norm_num)
theorem B1027093 : Blo 539803 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B814109 : Blo 539803 814109 := bbase (se 3 (by rfl) ⟨152645, by rfl⟩ : syracuseStep 814109 = 305291) (by norm_num)
theorem B609313 : Blo 539803 609313 := bbase (se 2 (by rfl) ⟨228492, by rfl⟩ : syracuseStep 609313 = 456985) (by norm_num)
theorem B814133 : Blo 539803 814133 := bbase (se 5 (by rfl) ⟨38162, by rfl⟩ : syracuseStep 814133 = 76325) (by norm_num)
theorem B1215557 : Blo 539803 1215557 := bbase (se 4 (by rfl) ⟨113958, by rfl⟩ : syracuseStep 1215557 = 227917) (by norm_num)
theorem B609349 : Blo 539803 609349 := bbase (se 4 (by rfl) ⟨57126, by rfl⟩ : syracuseStep 609349 = 114253) (by norm_num)
theorem B814157 : Blo 539803 814157 := bbase (se 3 (by rfl) ⟨152654, by rfl⟩ : syracuseStep 814157 = 305309) (by norm_num)
theorem B912485 : Blo 539803 912485 := bbase (se 4 (by rfl) ⟨85545, by rfl⟩ : syracuseStep 912485 = 171091) (by norm_num)
theorem B814181 : Blo 539803 814181 := bbase (se 4 (by rfl) ⟨76329, by rfl⟩ : syracuseStep 814181 = 152659) (by norm_num)
theorem B609385 : Blo 539803 609385 := bbase (se 2 (by rfl) ⟨228519, by rfl⟩ : syracuseStep 609385 = 457039) (by norm_num)
theorem B625781 : Blo 539803 625781 := bbase (se 5 (by rfl) ⟨29333, by rfl⟩ : syracuseStep 625781 = 58667) (by norm_num)
theorem B1952885 : Blo 539803 1952885 := bbase (se 5 (by rfl) ⟨91541, by rfl⟩ : syracuseStep 1952885 = 183083) (by norm_num)
theorem B1830005 : Blo 539803 1830005 := bbase (se 5 (by rfl) ⟨85781, by rfl⟩ : syracuseStep 1830005 = 171563) (by norm_num)
theorem B814205 : Blo 539803 814205 := bbase (se 3 (by rfl) ⟨152663, by rfl⟩ : syracuseStep 814205 = 305327) (by norm_num)
theorem B1297541 : Blo 539803 1297541 := bbase (se 4 (by rfl) ⟨121644, by rfl⟩ : syracuseStep 1297541 = 243289) (by norm_num)
theorem B1371269 : Blo 539803 1371269 := bbase (se 4 (by rfl) ⟨128556, by rfl⟩ : syracuseStep 1371269 = 257113) (by norm_num)
theorem B1215629 : Blo 539803 1215629 := bbase (se 3 (by rfl) ⟨227930, by rfl⟩ : syracuseStep 1215629 = 455861) (by norm_num)
theorem B609421 : Blo 539803 609421 := bbase (se 3 (by rfl) ⟨114266, by rfl⟩ : syracuseStep 609421 = 228533) (by norm_num)
theorem B1027237 : Blo 539803 1027237 := bbase (se 4 (by rfl) ⟨96303, by rfl⟩ : syracuseStep 1027237 = 192607) (by norm_num)
theorem B609457 : Blo 539803 609457 := bbase (se 2 (by rfl) ⟨228546, by rfl⟩ : syracuseStep 609457 = 457093) (by norm_num)
theorem B1215701 : Blo 539803 1215701 := bbase (se 7 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 1215701 = 28493) (by norm_num)
theorem B1731797 : Blo 539803 1731797 := bbase (se 7 (by rfl) ⟨20294, by rfl⟩ : syracuseStep 1731797 = 40589) (by norm_num)
theorem B609493 : Blo 539803 609493 := bbase (se 7 (by rfl) ⟨7142, by rfl⟩ : syracuseStep 609493 = 14285) (by norm_num)
theorem B912613 : Blo 539803 912613 := bbase (se 4 (by rfl) ⟨85557, by rfl⟩ : syracuseStep 912613 = 171115) (by norm_num)
theorem B683245 : Blo 539803 683245 := bbase (se 3 (by rfl) ⟨128108, by rfl⟩ : syracuseStep 683245 = 256217) (by norm_num)
theorem B609529 : Blo 539803 609529 := bbase (se 2 (by rfl) ⟨228573, by rfl⟩ : syracuseStep 609529 = 457147) (by norm_num)
theorem B642325 : Blo 539803 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B1215773 : Blo 539803 1215773 := bbase (se 3 (by rfl) ⟨227957, by rfl⟩ : syracuseStep 1215773 = 455915) (by norm_num)
theorem B609565 : Blo 539803 609565 := bbase (se 3 (by rfl) ⟨114293, by rfl⟩ : syracuseStep 609565 = 228587) (by norm_num)
theorem B650549 : Blo 539803 650549 := bbase (se 5 (by rfl) ⟨30494, by rfl⟩ : syracuseStep 650549 = 60989) (by norm_num)
theorem B912701 : Blo 539803 912701 := bbase (se 3 (by rfl) ⟨171131, by rfl⟩ : syracuseStep 912701 = 342263) (by norm_num)
theorem B609601 : Blo 539803 609601 := bbase (se 2 (by rfl) ⟨228600, by rfl⟩ : syracuseStep 609601 = 457201) (by norm_num)
theorem B1027397 : Blo 539803 1027397 := bbase (se 4 (by rfl) ⟨96318, by rfl⟩ : syracuseStep 1027397 = 192637) (by norm_num)
theorem B6663509 : Blo 539803 6663509 := bbase (se 11 (by rfl) ⟨4880, by rfl⟩ : syracuseStep 6663509 = 9761) (by norm_num)
theorem B1215845 : Blo 539803 1215845 := bbase (se 4 (by rfl) ⟨113985, by rfl⟩ : syracuseStep 1215845 = 227971) (by norm_num)
theorem B609637 : Blo 539803 609637 := bbase (se 4 (by rfl) ⟨57153, by rfl⟩ : syracuseStep 609637 = 114307) (by norm_num)
theorem B2600309 : Blo 539803 2600309 := bbase (se 5 (by rfl) ⟨121889, by rfl⟩ : syracuseStep 2600309 = 243779) (by norm_num)
theorem B609673 : Blo 539803 609673 := bbase (se 2 (by rfl) ⟨228627, by rfl⟩ : syracuseStep 609673 = 457255) (by norm_num)
theorem B1174925 : Blo 539803 1174925 := bbase (se 3 (by rfl) ⟨220298, by rfl⟩ : syracuseStep 1174925 = 440597) (by norm_num)
theorem B7925141 : Blo 539803 7925141 := bbase (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) (by norm_num)
theorem B683417 : Blo 539803 683417 := bbase (se 2 (by rfl) ⟨256281, by rfl⟩ : syracuseStep 683417 = 512563) (by norm_num)
theorem B576941 : Blo 539803 576941 := bbase (se 3 (by rfl) ⟨108176, by rfl⟩ : syracuseStep 576941 = 216353) (by norm_num)
theorem B1215917 : Blo 539803 1215917 := bbase (se 3 (by rfl) ⟨227984, by rfl⟩ : syracuseStep 1215917 = 455969) (by norm_num)
theorem B609709 : Blo 539803 609709 := bbase (se 3 (by rfl) ⟨114320, by rfl⟩ : syracuseStep 609709 = 228641) (by norm_num)
theorem B1043885 : Blo 539803 1043885 := bbase (se 3 (by rfl) ⟨195728, by rfl⟩ : syracuseStep 1043885 = 391457) (by norm_num)
theorem B912829 : Blo 539803 912829 := bbase (se 3 (by rfl) ⟨171155, by rfl⟩ : syracuseStep 912829 = 342311) (by norm_num)
theorem B683473 : Blo 539803 683473 := bbase (se 2 (by rfl) ⟨256302, by rfl⟩ : syracuseStep 683473 = 512605) (by norm_num)
theorem B609745 : Blo 539803 609745 := bbase (se 2 (by rfl) ⟨228654, by rfl⟩ : syracuseStep 609745 = 457309) (by norm_num)
theorem B1027541 : Blo 539803 1027541 := bbase (se 7 (by rfl) ⟨12041, by rfl⟩ : syracuseStep 1027541 = 24083) (by norm_num)
theorem B1371613 : Blo 539803 1371613 := bbase (se 3 (by rfl) ⟨257177, by rfl⟩ : syracuseStep 1371613 = 514355) (by norm_num)
theorem B577001 : Blo 539803 577001 := bbase (se 2 (by rfl) ⟨216375, by rfl⟩ : syracuseStep 577001 = 432751) (by norm_num)
theorem B1215989 : Blo 539803 1215989 := bbase (se 5 (by rfl) ⟨56999, by rfl⟩ : syracuseStep 1215989 = 113999) (by norm_num)
theorem B609781 : Blo 539803 609781 := bbase (se 5 (by rfl) ⟨28583, by rfl⟩ : syracuseStep 609781 = 57167) (by norm_num)
theorem B1232381 : Blo 539803 1232381 := bbase (se 3 (by rfl) ⟨231071, by rfl⟩ : syracuseStep 1232381 = 462143) (by norm_num)
theorem B1822229 : Blo 539803 1822229 := bbase (se 6 (by rfl) ⟨42708, by rfl⟩ : syracuseStep 1822229 = 85417) (by norm_num)
theorem B912917 : Blo 539803 912917 := bbase (se 6 (by rfl) ⟨21396, by rfl⟩ : syracuseStep 912917 = 42793) (by norm_num)
theorem B609817 : Blo 539803 609817 := bbase (se 2 (by rfl) ⟨228681, by rfl⟩ : syracuseStep 609817 = 457363) (by norm_num)
theorem B1830437 : Blo 539803 1830437 := bbase (se 4 (by rfl) ⟨171603, by rfl⟩ : syracuseStep 1830437 = 343207) (by norm_num)
theorem B683569 : Blo 539803 683569 := bbase (se 2 (by rfl) ⟨256338, by rfl⟩ : syracuseStep 683569 = 512677) (by norm_num)
theorem B4574773 : Blo 539803 4574773 := bbase (se 5 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 4574773 = 428885) (by norm_num)
theorem B1216061 : Blo 539803 1216061 := bbase (se 3 (by rfl) ⟨228011, by rfl⟩ : syracuseStep 1216061 = 456023) (by norm_num)
theorem B609853 : Blo 539803 609853 := bbase (se 3 (by rfl) ⟨114347, by rfl⟩ : syracuseStep 609853 = 228695) (by norm_num)
theorem B1371725 : Blo 539803 1371725 := bbase (se 3 (by rfl) ⟨257198, by rfl⟩ : syracuseStep 1371725 = 514397) (by norm_num)
theorem B609889 : Blo 539803 609889 := bbase (se 2 (by rfl) ⟨228708, by rfl⟩ : syracuseStep 609889 = 457417) (by norm_num)
theorem B577129 : Blo 539803 577129 := bbase (se 2 (by rfl) ⟨216423, by rfl⟩ : syracuseStep 577129 = 432847) (by norm_num)
theorem B650857 : Blo 539803 650857 := bbase (se 2 (by rfl) ⟨244071, by rfl⟩ : syracuseStep 650857 = 488143) (by norm_num)
theorem B1216133 : Blo 539803 1216133 := bbase (se 4 (by rfl) ⟨114012, by rfl⟩ : syracuseStep 1216133 = 228025) (by norm_num)
theorem B609925 : Blo 539803 609925 := bbase (se 4 (by rfl) ⟨57180, by rfl⟩ : syracuseStep 609925 = 114361) (by norm_num)
theorem B913045 : Blo 539803 913045 := bbase (se 6 (by rfl) ⟨21399, by rfl⟩ : syracuseStep 913045 = 42799) (by norm_num)
theorem B1068701 : Blo 539803 1068701 := bbase (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) (by norm_num)
theorem B609961 : Blo 539803 609961 := bbase (se 2 (by rfl) ⟨228735, by rfl⟩ : syracuseStep 609961 = 457471) (by norm_num)
theorem B1044149 : Blo 539803 1044149 := bbase (se 5 (by rfl) ⟨48944, by rfl⟩ : syracuseStep 1044149 = 97889) (by norm_num)
theorem B1216205 : Blo 539803 1216205 := bbase (se 3 (by rfl) ⟨228038, by rfl⟩ : syracuseStep 1216205 = 456077) (by norm_num)
theorem B609997 : Blo 539803 609997 := bbase (se 3 (by rfl) ⟨114374, by rfl⟩ : syracuseStep 609997 = 228749) (by norm_num)
theorem B683741 : Blo 539803 683741 := bbase (se 3 (by rfl) ⟨128201, by rfl⟩ : syracuseStep 683741 = 256403) (by norm_num)
theorem B913133 : Blo 539803 913133 := bbase (se 3 (by rfl) ⟨171212, by rfl⟩ : syracuseStep 913133 = 342425) (by norm_num)
theorem B610033 : Blo 539803 610033 := bbase (se 2 (by rfl) ⟨228762, by rfl⟩ : syracuseStep 610033 = 457525) (by norm_num)
theorem B1027829 : Blo 539803 1027829 := bbase (se 5 (by rfl) ⟨48179, by rfl⟩ : syracuseStep 1027829 = 96359) (by norm_num)
theorem B1371917 : Blo 539803 1371917 := bbase (se 3 (by rfl) ⟨257234, by rfl⟩ : syracuseStep 1371917 = 514469) (by norm_num)
theorem B683797 : Blo 539803 683797 := bbase (se 6 (by rfl) ⟨16026, by rfl⟩ : syracuseStep 683797 = 32053) (by norm_num)
theorem B1216277 : Blo 539803 1216277 := bbase (se 6 (by rfl) ⟨28506, by rfl⟩ : syracuseStep 1216277 = 57013) (by norm_num)
theorem B610069 : Blo 539803 610069 := bbase (se 6 (by rfl) ⟨14298, by rfl⟩ : syracuseStep 610069 = 28597) (by norm_num)
theorem B610105 : Blo 539803 610105 := bbase (se 2 (by rfl) ⟨228789, by rfl⟩ : syracuseStep 610105 = 457579) (by norm_num)
theorem B651073 : Blo 539803 651073 := bbase (se 2 (by rfl) ⟨244152, by rfl⟩ : syracuseStep 651073 = 488305) (by norm_num)
theorem B1216349 : Blo 539803 1216349 := bbase (se 3 (by rfl) ⟨228065, by rfl⟩ : syracuseStep 1216349 = 456131) (by norm_num)
theorem B610141 : Blo 539803 610141 := bbase (se 3 (by rfl) ⟨114401, by rfl⟩ : syracuseStep 610141 = 228803) (by norm_num)
theorem B913261 : Blo 539803 913261 := bbase (se 3 (by rfl) ⟨171236, by rfl⟩ : syracuseStep 913261 = 342473) (by norm_num)
theorem B683893 : Blo 539803 683893 := bbase (se 5 (by rfl) ⟨32057, by rfl⟩ : syracuseStep 683893 = 64115) (by norm_num)
theorem B610177 : Blo 539803 610177 := bbase (se 2 (by rfl) ⟨228816, by rfl⟩ : syracuseStep 610177 = 457633) (by norm_num)
theorem B1027981 : Blo 539803 1027981 := bbase (se 3 (by rfl) ⟨192746, by rfl⟩ : syracuseStep 1027981 = 385493) (by norm_num)
theorem B9891733 : Blo 539803 9891733 := bbase (se 6 (by rfl) ⟨231837, by rfl⟩ : syracuseStep 9891733 = 463675) (by norm_num)
theorem B1216421 : Blo 539803 1216421 := bbase (se 4 (by rfl) ⟨114039, by rfl⟩ : syracuseStep 1216421 = 228079) (by norm_num)
theorem B610213 : Blo 539803 610213 := bbase (se 4 (by rfl) ⟨57207, by rfl⟩ : syracuseStep 610213 = 114415) (by norm_num)
theorem B1822661 : Blo 539803 1822661 := bbase (se 4 (by rfl) ⟨170874, by rfl⟩ : syracuseStep 1822661 = 341749) (by norm_num)
theorem B913349 : Blo 539803 913349 := bbase (se 4 (by rfl) ⟨85626, by rfl⟩ : syracuseStep 913349 = 171253) (by norm_num)
theorem B610249 : Blo 539803 610249 := bbase (se 2 (by rfl) ⟨228843, by rfl⟩ : syracuseStep 610249 = 457687) (by norm_num)
theorem B1830869 : Blo 539803 1830869 := bbase (se 7 (by rfl) ⟨21455, by rfl⟩ : syracuseStep 1830869 = 42911) (by norm_num)
theorem B2060261 : Blo 539803 2060261 := bbase (se 4 (by rfl) ⟨193149, by rfl⟩ : syracuseStep 2060261 = 386299) (by norm_num)
theorem B1216493 : Blo 539803 1216493 := bbase (se 3 (by rfl) ⟨228092, by rfl⟩ : syracuseStep 1216493 = 456185) (by norm_num)
theorem B610285 : Blo 539803 610285 := bbase (se 3 (by rfl) ⟨114428, by rfl⟩ : syracuseStep 610285 = 228857) (by norm_num)
theorem B2740229 : Blo 539803 2740229 := bbase (se 4 (by rfl) ⟨256896, by rfl⟩ : syracuseStep 2740229 = 513793) (by norm_num)
theorem B610321 : Blo 539803 610321 := bbase (se 2 (by rfl) ⟨228870, by rfl⟩ : syracuseStep 610321 = 457741) (by norm_num)
theorem B684065 : Blo 539803 684065 := bbase (se 2 (by rfl) ⟨256524, by rfl⟩ : syracuseStep 684065 = 513049) (by norm_num)
theorem B577573 : Blo 539803 577573 := bbase (se 4 (by rfl) ⟨54147, by rfl⟩ : syracuseStep 577573 = 108295) (by norm_num)
theorem B1159213 : Blo 539803 1159213 := bbase (se 3 (by rfl) ⟨217352, by rfl⟩ : syracuseStep 1159213 = 434705) (by norm_num)
theorem B1216565 : Blo 539803 1216565 := bbase (se 5 (by rfl) ⟨57026, by rfl⟩ : syracuseStep 1216565 = 114053) (by norm_num)
theorem B610357 : Blo 539803 610357 := bbase (se 5 (by rfl) ⟨28610, by rfl⟩ : syracuseStep 610357 = 57221) (by norm_num)
theorem B913477 : Blo 539803 913477 := bbase (se 4 (by rfl) ⟨85638, by rfl⟩ : syracuseStep 913477 = 171277) (by norm_num)
theorem B2314325 : Blo 539803 2314325 := bbase (se 8 (by rfl) ⟨13560, by rfl⟩ : syracuseStep 2314325 = 27121) (by norm_num)
theorem B684121 : Blo 539803 684121 := bbase (se 2 (by rfl) ⟨256545, by rfl⟩ : syracuseStep 684121 = 513091) (by norm_num)
theorem B610393 : Blo 539803 610393 := bbase (se 2 (by rfl) ⟨228897, by rfl⟩ : syracuseStep 610393 = 457795) (by norm_num)
theorem B1372261 : Blo 539803 1372261 := bbase (se 4 (by rfl) ⟨128649, by rfl⟩ : syracuseStep 1372261 = 257299) (by norm_num)
theorem B3461237 : Blo 539803 3461237 := bbase (se 5 (by rfl) ⟨162245, by rfl⟩ : syracuseStep 3461237 = 324491) (by norm_num)
theorem B1216637 : Blo 539803 1216637 := bbase (se 3 (by rfl) ⟨228119, by rfl⟩ : syracuseStep 1216637 = 456239) (by norm_num)
theorem B610429 : Blo 539803 610429 := bbase (se 3 (by rfl) ⟨114455, by rfl⟩ : syracuseStep 610429 = 228911) (by norm_num)
theorem B1544341 : Blo 539803 1544341 := bbase (se 6 (by rfl) ⟨36195, by rfl⟩ : syracuseStep 1544341 = 72391) (by norm_num)
theorem B577693 : Blo 539803 577693 := bbase (se 3 (by rfl) ⟨108317, by rfl⟩ : syracuseStep 577693 = 216635) (by norm_num)
theorem B913565 : Blo 539803 913565 := bbase (se 3 (by rfl) ⟨171293, by rfl⟩ : syracuseStep 913565 = 342587) (by norm_num)
theorem B610465 : Blo 539803 610465 := bbase (se 2 (by rfl) ⟨228924, by rfl⟩ : syracuseStep 610465 = 457849) (by norm_num)
theorem B684217 : Blo 539803 684217 := bbase (se 2 (by rfl) ⟨256581, by rfl⟩ : syracuseStep 684217 = 513163) (by norm_num)
theorem B1028285 : Blo 539803 1028285 := bbase (se 3 (by rfl) ⟨192803, by rfl⟩ : syracuseStep 1028285 = 385607) (by norm_num)
theorem B1216709 : Blo 539803 1216709 := bbase (se 4 (by rfl) ⟨114066, by rfl⟩ : syracuseStep 1216709 = 228133) (by norm_num)
theorem B610501 : Blo 539803 610501 := bbase (se 4 (by rfl) ⟨57234, by rfl⟩ : syracuseStep 610501 = 114469) (by norm_num)
theorem B1372373 : Blo 539803 1372373 := bbase (se 7 (by rfl) ⟨16082, by rfl⟩ : syracuseStep 1372373 = 32165) (by norm_num)
theorem B610537 : Blo 539803 610537 := bbase (se 2 (by rfl) ⟨228951, by rfl⟩ : syracuseStep 610537 = 457903) (by norm_num)
theorem B618745 : Blo 539803 618745 := bbase (se 2 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 618745 = 464059) (by norm_num)
theorem B2060549 : Blo 539803 2060549 := bbase (se 4 (by rfl) ⟨193176, by rfl⟩ : syracuseStep 2060549 = 386353) (by norm_num)
theorem B1216781 : Blo 539803 1216781 := bbase (se 3 (by rfl) ⟨228146, by rfl⟩ : syracuseStep 1216781 = 456293) (by norm_num)
theorem B610573 : Blo 539803 610573 := bbase (se 3 (by rfl) ⟨114482, by rfl⟩ : syracuseStep 610573 = 228965) (by norm_num)
theorem B913693 : Blo 539803 913693 := bbase (se 3 (by rfl) ⟨171317, by rfl⟩ : syracuseStep 913693 = 342635) (by norm_num)
theorem B610609 : Blo 539803 610609 := bbase (se 2 (by rfl) ⟨228978, by rfl⟩ : syracuseStep 610609 = 457957) (by norm_num)
theorem B1544501 : Blo 539803 1544501 := bbase (se 5 (by rfl) ⟨72398, by rfl⟩ : syracuseStep 1544501 = 144797) (by norm_num)
theorem B2314565 : Blo 539803 2314565 := bbase (se 4 (by rfl) ⟨216990, by rfl⟩ : syracuseStep 2314565 = 433981) (by norm_num)
theorem B1216853 : Blo 539803 1216853 := bbase (se 10 (by rfl) ⟨1782, by rfl⟩ : syracuseStep 1216853 = 3565) (by norm_num)
theorem B610645 : Blo 539803 610645 := bbase (se 10 (by rfl) ⟨894, by rfl⟩ : syracuseStep 610645 = 1789) (by norm_num)
theorem B684389 : Blo 539803 684389 := bbase (se 4 (by rfl) ⟨64161, by rfl⟩ : syracuseStep 684389 = 128323) (by norm_num)
theorem B1823093 : Blo 539803 1823093 := bbase (se 5 (by rfl) ⟨85457, by rfl⟩ : syracuseStep 1823093 = 170915) (by norm_num)
theorem B913781 : Blo 539803 913781 := bbase (se 5 (by rfl) ⟨42833, by rfl⟩ : syracuseStep 913781 = 85667) (by norm_num)
theorem B2052485 : Blo 539803 2052485 := bbase (se 4 (by rfl) ⟨192420, by rfl⟩ : syracuseStep 2052485 = 384841) (by norm_num)
theorem B1831301 : Blo 539803 1831301 := bbase (se 4 (by rfl) ⟨171684, by rfl⟩ : syracuseStep 1831301 = 343369) (by norm_num)
theorem B1372565 : Blo 539803 1372565 := bbase (se 6 (by rfl) ⟨32169, by rfl⟩ : syracuseStep 1372565 = 64339) (by norm_num)
theorem B577945 : Blo 539803 577945 := bbase (se 2 (by rfl) ⟨216729, by rfl⟩ : syracuseStep 577945 = 433459) (by norm_num)
theorem B651673 : Blo 539803 651673 := bbase (se 2 (by rfl) ⟨244377, by rfl⟩ : syracuseStep 651673 = 488755) (by norm_num)
theorem B684445 : Blo 539803 684445 := bbase (se 3 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 684445 = 256667) (by norm_num)
theorem B1216925 : Blo 539803 1216925 := bbase (se 3 (by rfl) ⟨228173, by rfl⟩ : syracuseStep 1216925 = 456347) (by norm_num)
theorem B577949 : Blo 539803 577949 := bbase (se 3 (by rfl) ⟨108365, by rfl⟩ : syracuseStep 577949 = 216731) (by norm_num)
theorem B2347429 : Blo 539803 2347429 := bbase (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) (by norm_num)
theorem B2306501 : Blo 539803 2306501 := bbase (se 4 (by rfl) ⟨216234, by rfl⟩ : syracuseStep 2306501 = 432469) (by norm_num)
theorem B831973 : Blo 539803 831973 := bbase (se 4 (by rfl) ⟨77997, by rfl⟩ : syracuseStep 831973 = 155995) (by norm_num)
theorem B1216997 : Blo 539803 1216997 := bbase (se 4 (by rfl) ⟨114093, by rfl⟩ : syracuseStep 1216997 = 228187) (by norm_num)
theorem B913909 : Blo 539803 913909 := bbase (se 5 (by rfl) ⟨42839, by rfl⟩ : syracuseStep 913909 = 85679) (by norm_num)
theorem B684541 : Blo 539803 684541 := bbase (se 3 (by rfl) ⟨128351, by rfl⟩ : syracuseStep 684541 = 256703) (by norm_num)
theorem B1544741 : Blo 539803 1544741 := bbase (se 4 (by rfl) ⟨144819, by rfl⟩ : syracuseStep 1544741 = 289639) (by norm_num)
theorem B1217069 : Blo 539803 1217069 := bbase (se 3 (by rfl) ⟨228200, by rfl⟩ : syracuseStep 1217069 = 456401) (by norm_num)
theorem B1561141 : Blo 539803 1561141 := bbase (se 5 (by rfl) ⟨73178, by rfl⟩ : syracuseStep 1561141 = 146357) (by norm_num)
theorem B913997 : Blo 539803 913997 := bbase (se 3 (by rfl) ⟨171374, by rfl⟩ : syracuseStep 913997 = 342749) (by norm_num)
theorem B586321 : Blo 539803 586321 := bbase (se 2 (by rfl) ⟨219870, by rfl⟩ : syracuseStep 586321 = 439741) (by norm_num)
theorem B1217141 : Blo 539803 1217141 := bbase (se 5 (by rfl) ⟨57053, by rfl⟩ : syracuseStep 1217141 = 114107) (by norm_num)
theorem B1249933 : Blo 539803 1249933 := bbase (se 3 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 1249933 = 468725) (by norm_num)
theorem B2052773 : Blo 539803 2052773 := bbase (se 4 (by rfl) ⟨192447, by rfl⟩ : syracuseStep 2052773 = 384895) (by norm_num)
theorem B1389221 : Blo 539803 1389221 := bbase (se 4 (by rfl) ⟨130239, by rfl⟩ : syracuseStep 1389221 = 260479) (by norm_num)
theorem B684713 : Blo 539803 684713 := bbase (se 2 (by rfl) ⟨256767, by rfl⟩ : syracuseStep 684713 = 513535) (by norm_num)
theorem B5083829 : Blo 539803 5083829 := bbase (se 5 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 5083829 = 476609) (by norm_num)
theorem B1217213 : Blo 539803 1217213 := bbase (se 3 (by rfl) ⟨228227, by rfl⟩ : syracuseStep 1217213 = 456455) (by norm_num)
theorem B914125 : Blo 539803 914125 := bbase (se 3 (by rfl) ⟨171398, by rfl⟩ : syracuseStep 914125 = 342797) (by norm_num)
theorem B684769 : Blo 539803 684769 := bbase (se 2 (by rfl) ⟨256788, by rfl⟩ : syracuseStep 684769 = 513577) (by norm_num)
theorem B1544933 : Blo 539803 1544933 := bbase (se 4 (by rfl) ⟨144837, by rfl⟩ : syracuseStep 1544933 = 289675) (by norm_num)
theorem B1372909 : Blo 539803 1372909 := bbase (se 3 (by rfl) ⟨257420, by rfl⟩ : syracuseStep 1372909 = 514841) (by norm_num)
theorem B1217285 : Blo 539803 1217285 := bbase (se 4 (by rfl) ⟨114120, by rfl⟩ : syracuseStep 1217285 = 228241) (by norm_num)
theorem B2601733 : Blo 539803 2601733 := bbase (se 4 (by rfl) ⟨243912, by rfl⟩ : syracuseStep 2601733 = 487825) (by norm_num)
theorem B1823525 : Blo 539803 1823525 := bbase (se 4 (by rfl) ⟨170955, by rfl⟩ : syracuseStep 1823525 = 341911) (by norm_num)
theorem B914213 : Blo 539803 914213 := bbase (se 4 (by rfl) ⟨85707, by rfl⟩ : syracuseStep 914213 = 171415) (by norm_num)
theorem B1299253 : Blo 539803 1299253 := bbase (se 5 (by rfl) ⟨60902, by rfl⟩ : syracuseStep 1299253 = 121805) (by norm_num)
theorem B1831733 : Blo 539803 1831733 := bbase (se 5 (by rfl) ⟨85862, by rfl⟩ : syracuseStep 1831733 = 171725) (by norm_num)
theorem B684865 : Blo 539803 684865 := bbase (se 2 (by rfl) ⟨256824, by rfl⟩ : syracuseStep 684865 = 513649) (by norm_num)
theorem B1217357 : Blo 539803 1217357 := bbase (se 3 (by rfl) ⟨228254, by rfl⟩ : syracuseStep 1217357 = 456509) (by norm_num)
theorem B1373021 : Blo 539803 1373021 := bbase (se 3 (by rfl) ⟨257441, by rfl⟩ : syracuseStep 1373021 = 514883) (by norm_num)
theorem B5198741 : Blo 539803 5198741 := bbase (se 6 (by rfl) ⟨121845, by rfl⟩ : syracuseStep 5198741 = 243691) (by norm_num)
theorem B1217429 : Blo 539803 1217429 := bbase (se 6 (by rfl) ⟨28533, by rfl⟩ : syracuseStep 1217429 = 57067) (by norm_num)
theorem B865181 : Blo 539803 865181 := bbase (se 3 (by rfl) ⟨162221, by rfl⟩ : syracuseStep 865181 = 324443) (by norm_num)
theorem B914341 : Blo 539803 914341 := bbase (se 4 (by rfl) ⟨85719, by rfl⟩ : syracuseStep 914341 = 171439) (by norm_num)
theorem B1029037 : Blo 539803 1029037 := bbase (se 3 (by rfl) ⟨192944, by rfl⟩ : syracuseStep 1029037 = 385889) (by norm_num)
theorem B578513 : Blo 539803 578513 := bbase (se 2 (by rfl) ⟨216942, by rfl⟩ : syracuseStep 578513 = 433885) (by norm_num)
theorem B1217501 : Blo 539803 1217501 := bbase (se 3 (by rfl) ⟨228281, by rfl⟩ : syracuseStep 1217501 = 456563) (by norm_num)
theorem B685037 : Blo 539803 685037 := bbase (se 3 (by rfl) ⟨128444, by rfl⟩ : syracuseStep 685037 = 256889) (by norm_num)
theorem B832501 : Blo 539803 832501 := bbase (se 5 (by rfl) ⟨39023, by rfl⟩ : syracuseStep 832501 = 78047) (by norm_num)
theorem B914429 : Blo 539803 914429 := bbase (se 3 (by rfl) ⟨171455, by rfl⟩ : syracuseStep 914429 = 342911) (by norm_num)
theorem B1373213 : Blo 539803 1373213 := bbase (se 3 (by rfl) ⟨257477, by rfl⟩ : syracuseStep 1373213 = 514955) (by norm_num)
theorem B1217573 : Blo 539803 1217573 := bbase (se 4 (by rfl) ⟨114147, by rfl⟩ : syracuseStep 1217573 = 228295) (by norm_num)
theorem B1733669 : Blo 539803 1733669 := bbase (se 4 (by rfl) ⟨162531, by rfl⟩ : syracuseStep 1733669 = 325063) (by norm_num)
theorem B685093 : Blo 539803 685093 := bbase (se 4 (by rfl) ⟨64227, by rfl⟩ : syracuseStep 685093 = 128455) (by norm_num)
theorem B1029181 : Blo 539803 1029181 := bbase (se 3 (by rfl) ⟨192971, by rfl⟩ : syracuseStep 1029181 = 385943) (by norm_num)
theorem B1217645 : Blo 539803 1217645 := bbase (se 3 (by rfl) ⟨228308, by rfl⟩ : syracuseStep 1217645 = 456617) (by norm_num)
theorem B914557 : Blo 539803 914557 := bbase (se 3 (by rfl) ⟨171479, by rfl⟩ : syracuseStep 914557 = 342959) (by norm_num)
theorem B685189 : Blo 539803 685189 := bbase (se 4 (by rfl) ⟨64236, by rfl⟩ : syracuseStep 685189 = 128473) (by norm_num)
theorem B1234061 : Blo 539803 1234061 := bbase (se 3 (by rfl) ⟨231386, by rfl⟩ : syracuseStep 1234061 = 462773) (by norm_num)
theorem B578701 : Blo 539803 578701 := bbase (se 3 (by rfl) ⟨108506, by rfl⟩ : syracuseStep 578701 = 217013) (by norm_num)
theorem B1217717 : Blo 539803 1217717 := bbase (se 5 (by rfl) ⟨57080, by rfl⟩ : syracuseStep 1217717 = 114161) (by norm_num)
theorem B1823957 : Blo 539803 1823957 := bbase (se 7 (by rfl) ⟨21374, by rfl⟩ : syracuseStep 1823957 = 42749) (by norm_num)
theorem B914645 : Blo 539803 914645 := bbase (se 7 (by rfl) ⟨10718, by rfl⟩ : syracuseStep 914645 = 21437) (by norm_num)
theorem B1029341 : Blo 539803 1029341 := bbase (se 3 (by rfl) ⟨193001, by rfl⟩ : syracuseStep 1029341 = 386003) (by norm_num)
theorem B1217789 : Blo 539803 1217789 := bbase (se 3 (by rfl) ⟨228335, by rfl⟩ : syracuseStep 1217789 = 456671) (by norm_num)
theorem B2741525 : Blo 539803 2741525 := bbase (se 6 (by rfl) ⟨64254, by rfl⟩ : syracuseStep 2741525 = 128509) (by norm_num)
theorem B685361 : Blo 539803 685361 := bbase (se 2 (by rfl) ⟨257010, by rfl⟩ : syracuseStep 685361 = 514021) (by norm_num)
theorem B1217861 : Blo 539803 1217861 := bbase (se 4 (by rfl) ⟨114174, by rfl⟩ : syracuseStep 1217861 = 228349) (by norm_num)
theorem B25335125 : Blo 539803 25335125 := bbase (se 14 (by rfl) ⟨2319, by rfl⟩ : syracuseStep 25335125 = 4639) (by norm_num)
theorem B914773 : Blo 539803 914773 := bbase (se 13 (by rfl) ⟨167, by rfl⟩ : syracuseStep 914773 = 335) (by norm_num)
theorem B865637 : Blo 539803 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B685417 : Blo 539803 685417 := bbase (se 2 (by rfl) ⟨257031, by rfl⟩ : syracuseStep 685417 = 514063) (by norm_num)
theorem B1029485 : Blo 539803 1029485 := bbase (se 3 (by rfl) ⟨193028, by rfl⟩ : syracuseStep 1029485 = 386057) (by norm_num)
theorem B4117877 : Blo 539803 4117877 := bbase (se 5 (by rfl) ⟨193025, by rfl⟩ : syracuseStep 4117877 = 386051) (by norm_num)
theorem B1373557 : Blo 539803 1373557 := bbase (se 5 (by rfl) ⟨64385, by rfl⟩ : syracuseStep 1373557 = 128771) (by norm_num)
theorem B1217933 : Blo 539803 1217933 := bbase (se 3 (by rfl) ⟨228362, by rfl⟩ : syracuseStep 1217933 = 456725) (by norm_num)
theorem B914861 : Blo 539803 914861 := bbase (se 3 (by rfl) ⟨171536, by rfl⟩ : syracuseStep 914861 = 343073) (by norm_num)
theorem B685513 : Blo 539803 685513 := bbase (se 2 (by rfl) ⟨257067, by rfl⟩ : syracuseStep 685513 = 514135) (by norm_num)
theorem B1095125 : Blo 539803 1095125 := bbase (se 7 (by rfl) ⟨12833, by rfl⟩ : syracuseStep 1095125 = 25667) (by norm_num)
theorem B1218005 : Blo 539803 1218005 := bbase (se 7 (by rfl) ⟨14273, by rfl⟩ : syracuseStep 1218005 = 28547) (by norm_num)
theorem B1373669 : Blo 539803 1373669 := bbase (se 4 (by rfl) ⟨128781, by rfl⟩ : syracuseStep 1373669 = 257563) (by norm_num)
theorem B1218077 : Blo 539803 1218077 := bbase (se 3 (by rfl) ⟨228389, by rfl⟩ : syracuseStep 1218077 = 456779) (by norm_num)
theorem B914989 : Blo 539803 914989 := bbase (se 3 (by rfl) ⟨171560, by rfl⟩ : syracuseStep 914989 = 343121) (by norm_num)
theorem B1644101 : Blo 539803 1644101 := bbase (se 4 (by rfl) ⟨154134, by rfl⟩ : syracuseStep 1644101 = 308269) (by norm_num)
theorem B824909 : Blo 539803 824909 := bbase (se 3 (by rfl) ⟨154670, by rfl⟩ : syracuseStep 824909 = 309341) (by norm_num)
theorem B1218149 : Blo 539803 1218149 := bbase (se 4 (by rfl) ⟨114201, by rfl⟩ : syracuseStep 1218149 = 228403) (by norm_num)
theorem B685685 : Blo 539803 685685 := bbase (se 5 (by rfl) ⟨32141, by rfl⟩ : syracuseStep 685685 = 64283) (by norm_num)
theorem B1824389 : Blo 539803 1824389 := bbase (se 4 (by rfl) ⟨171036, by rfl⟩ : syracuseStep 1824389 = 342073) (by norm_num)
theorem B915077 : Blo 539803 915077 := bbase (se 4 (by rfl) ⟨85788, by rfl⟩ : syracuseStep 915077 = 171577) (by norm_num)
theorem B1029773 : Blo 539803 1029773 := bbase (se 3 (by rfl) ⟨193082, by rfl⟩ : syracuseStep 1029773 = 386165) (by norm_num)
theorem B1373861 : Blo 539803 1373861 := bbase (se 4 (by rfl) ⟨128799, by rfl⟩ : syracuseStep 1373861 = 257599) (by norm_num)
theorem B1218221 : Blo 539803 1218221 := bbase (se 3 (by rfl) ⟨228416, by rfl⟩ : syracuseStep 1218221 = 456833) (by norm_num)
theorem B685741 : Blo 539803 685741 := bbase (se 3 (by rfl) ⟨128576, by rfl⟩ : syracuseStep 685741 = 257153) (by norm_num)
theorem B2733749 : Blo 539803 2733749 := bbase (se 5 (by rfl) ⟨128144, by rfl⟩ : syracuseStep 2733749 = 256289) (by norm_num)
theorem B1947349 : Blo 539803 1947349 := bbase (se 7 (by rfl) ⟨22820, by rfl⟩ : syracuseStep 1947349 = 45641) (by norm_num)
theorem B1218293 : Blo 539803 1218293 := bbase (se 5 (by rfl) ⟨57107, by rfl⟩ : syracuseStep 1218293 = 114215) (by norm_num)
theorem B915205 : Blo 539803 915205 := bbase (se 4 (by rfl) ⟨85800, by rfl⟩ : syracuseStep 915205 = 171601) (by norm_num)
theorem B685837 : Blo 539803 685837 := bbase (se 3 (by rfl) ⟨128594, by rfl⟩ : syracuseStep 685837 = 257189) (by norm_num)
theorem B4110101 : Blo 539803 4110101 := bbase (se 6 (by rfl) ⟨96330, by rfl⟩ : syracuseStep 4110101 = 192661) (by norm_num)
theorem B1029925 : Blo 539803 1029925 := bbase (se 4 (by rfl) ⟨96555, by rfl⟩ : syracuseStep 1029925 = 193111) (by norm_num)
theorem B1218365 : Blo 539803 1218365 := bbase (se 3 (by rfl) ⟨228443, by rfl⟩ : syracuseStep 1218365 = 456887) (by norm_num)
theorem B2053957 : Blo 539803 2053957 := bbase (se 4 (by rfl) ⟨192558, by rfl⟩ : syracuseStep 2053957 = 385117) (by norm_num)
theorem B915293 : Blo 539803 915293 := bbase (se 3 (by rfl) ⟨171617, by rfl⟩ : syracuseStep 915293 = 343235) (by norm_num)
theorem B1218437 : Blo 539803 1218437 := bbase (se 4 (by rfl) ⟨114228, by rfl⟩ : syracuseStep 1218437 = 228457) (by norm_num)
theorem B686009 : Blo 539803 686009 := bbase (se 2 (by rfl) ⟨257253, by rfl⟩ : syracuseStep 686009 = 514507) (by norm_num)
theorem B579521 : Blo 539803 579521 := bbase (se 2 (by rfl) ⟨217320, by rfl⟩ : syracuseStep 579521 = 434641) (by norm_num)
theorem B1218509 : Blo 539803 1218509 := bbase (se 3 (by rfl) ⟨228470, by rfl⟩ : syracuseStep 1218509 = 456941) (by norm_num)
theorem B915421 : Blo 539803 915421 := bbase (se 3 (by rfl) ⟨171641, by rfl⟩ : syracuseStep 915421 = 343283) (by norm_num)
theorem B686065 : Blo 539803 686065 := bbase (se 2 (by rfl) ⟨257274, by rfl⟩ : syracuseStep 686065 = 514549) (by norm_num)
theorem B694261 : Blo 539803 694261 := bbase (se 5 (by rfl) ⟨32543, by rfl⟩ : syracuseStep 694261 = 65087) (by norm_num)
theorem B1153045 : Blo 539803 1153045 := bbase (se 6 (by rfl) ⟨27024, by rfl⟩ : syracuseStep 1153045 = 54049) (by norm_num)
theorem B1218581 : Blo 539803 1218581 := bbase (se 6 (by rfl) ⟨28560, by rfl⟩ : syracuseStep 1218581 = 57121) (by norm_num)
theorem B1824821 : Blo 539803 1824821 := bbase (se 5 (by rfl) ⟨85538, by rfl⟩ : syracuseStep 1824821 = 171077) (by norm_num)
theorem B915509 : Blo 539803 915509 := bbase (se 5 (by rfl) ⟨42914, by rfl⟩ : syracuseStep 915509 = 85829) (by norm_num)
theorem B686161 : Blo 539803 686161 := bbase (se 2 (by rfl) ⟨257310, by rfl⟩ : syracuseStep 686161 = 514621) (by norm_num)
theorem B2922581 : Blo 539803 2922581 := bbase (se 8 (by rfl) ⟨17124, by rfl⟩ : syracuseStep 2922581 = 34249) (by norm_num)
theorem B2193493 : Blo 539803 2193493 := bbase (se 8 (by rfl) ⟨12852, by rfl⟩ : syracuseStep 2193493 = 25705) (by norm_num)
theorem B1030229 : Blo 539803 1030229 := bbase (se 8 (by rfl) ⟨6036, by rfl⟩ : syracuseStep 1030229 = 12073) (by norm_num)
theorem B1218653 : Blo 539803 1218653 := bbase (se 3 (by rfl) ⟨228497, by rfl⟩ : syracuseStep 1218653 = 456995) (by norm_num)
theorem B2054261 : Blo 539803 2054261 := bbase (se 5 (by rfl) ⟨96293, by rfl⟩ : syracuseStep 2054261 = 192587) (by norm_num)
theorem B1218725 : Blo 539803 1218725 := bbase (se 4 (by rfl) ⟨114255, by rfl⟩ : syracuseStep 1218725 = 228511) (by norm_num)
theorem B4102325 : Blo 539803 4102325 := bbase (se 5 (by rfl) ⟨192296, by rfl⟩ : syracuseStep 4102325 = 384593) (by norm_num)
theorem B2308277 : Blo 539803 2308277 := bbase (se 5 (by rfl) ⟨108200, by rfl⟩ : syracuseStep 2308277 = 216401) (by norm_num)
theorem B4397237 : Blo 539803 4397237 := bbase (se 5 (by rfl) ⟨206120, by rfl⟩ : syracuseStep 4397237 = 412241) (by norm_num)
theorem B915637 : Blo 539803 915637 := bbase (se 5 (by rfl) ⟨42920, by rfl⟩ : syracuseStep 915637 = 85841) (by norm_num)
theorem B1317077 : Blo 539803 1317077 := bbase (se 7 (by rfl) ⟨15434, by rfl⟩ : syracuseStep 1317077 = 30869) (by norm_num)
theorem B1300693 : Blo 539803 1300693 := bbase (se 7 (by rfl) ⟨15242, by rfl⟩ : syracuseStep 1300693 = 30485) (by norm_num)
theorem B1218797 : Blo 539803 1218797 := bbase (se 3 (by rfl) ⟨228524, by rfl⟩ : syracuseStep 1218797 = 457049) (by norm_num)
theorem B686333 : Blo 539803 686333 := bbase (se 3 (by rfl) ⟨128687, by rfl⟩ : syracuseStep 686333 = 257375) (by norm_num)
theorem B1220813 : Blo 539803 1220813 := bbase (se 3 (by rfl) ⟨228902, by rfl⟩ : syracuseStep 1220813 = 457805) (by norm_num)
theorem B915725 : Blo 539803 915725 := bbase (se 3 (by rfl) ⟨171698, by rfl⟩ : syracuseStep 915725 = 343397) (by norm_num)
theorem B1218869 : Blo 539803 1218869 := bbase (se 5 (by rfl) ⟨57134, by rfl⟩ : syracuseStep 1218869 = 114269) (by norm_num)
theorem B686389 : Blo 539803 686389 := bbase (se 5 (by rfl) ⟨32174, by rfl⟩ : syracuseStep 686389 = 64349) (by norm_num)
theorem B866629 : Blo 539803 866629 := bbase (se 4 (by rfl) ⟨81246, by rfl⟩ : syracuseStep 866629 = 162493) (by norm_num)
theorem B10377557 : Blo 539803 10377557 := bbase (se 10 (by rfl) ⟨15201, by rfl⟩ : syracuseStep 10377557 = 30403) (by norm_num)
theorem B989525 : Blo 539803 989525 := bbase (se 10 (by rfl) ⟨1449, by rfl⟩ : syracuseStep 989525 = 2899) (by norm_num)
theorem B1759573 : Blo 539803 1759573 := bbase (se 10 (by rfl) ⟨2577, by rfl⟩ : syracuseStep 1759573 = 5155) (by norm_num)
theorem B2783573 : Blo 539803 2783573 := bbase (se 10 (by rfl) ⟨4077, by rfl⟩ : syracuseStep 2783573 = 8155) (by norm_num)
theorem B1218941 : Blo 539803 1218941 := bbase (se 3 (by rfl) ⟨228551, by rfl⟩ : syracuseStep 1218941 = 457103) (by norm_num)
theorem B915853 : Blo 539803 915853 := bbase (se 3 (by rfl) ⟨171722, by rfl⟩ : syracuseStep 915853 = 343445) (by norm_num)
theorem B1538453 : Blo 539803 1538453 := bbase (se 6 (by rfl) ⟨36057, by rfl⟩ : syracuseStep 1538453 = 72115) (by norm_num)
theorem B686485 : Blo 539803 686485 := bbase (se 6 (by rfl) ⟨16089, by rfl⟩ : syracuseStep 686485 = 32179) (by norm_num)
theorem B1366429 : Blo 539803 1366429 := bbase (se 3 (by rfl) ⟨256205, by rfl⟩ : syracuseStep 1366429 = 512411) (by norm_num)
theorem B1219013 : Blo 539803 1219013 := bbase (se 4 (by rfl) ⟨114282, by rfl⟩ : syracuseStep 1219013 = 228565) (by norm_num)
theorem B1825253 : Blo 539803 1825253 := bbase (se 4 (by rfl) ⟨171117, by rfl⟩ : syracuseStep 1825253 = 342235) (by norm_num)
theorem B915941 : Blo 539803 915941 := bbase (se 4 (by rfl) ⟨85869, by rfl⟩ : syracuseStep 915941 = 171739) (by norm_num)
theorem B1153541 : Blo 539803 1153541 := bbase (se 4 (by rfl) ⟨108144, by rfl⟩ : syracuseStep 1153541 = 216289) (by norm_num)
theorem B1366541 : Blo 539803 1366541 := bbase (se 3 (by rfl) ⟨256226, by rfl⟩ : syracuseStep 1366541 = 512453) (by norm_num)
theorem B1219085 : Blo 539803 1219085 := bbase (se 3 (by rfl) ⟨228578, by rfl⟩ : syracuseStep 1219085 = 457157) (by norm_num)
theorem B4946453 : Blo 539803 4946453 := bbase (se 6 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 4946453 = 231865) (by norm_num)
theorem B1096229 : Blo 539803 1096229 := bbase (se 4 (by rfl) ⟨102771, by rfl⟩ : syracuseStep 1096229 = 205543) (by norm_num)
theorem B2742821 : Blo 539803 2742821 := bbase (se 4 (by rfl) ⟨257139, by rfl⟩ : syracuseStep 2742821 = 514279) (by norm_num)
theorem B2316853 : Blo 539803 2316853 := bbase (se 5 (by rfl) ⟨108602, by rfl⟩ : syracuseStep 2316853 = 217205) (by norm_num)
theorem B686657 : Blo 539803 686657 := bbase (se 2 (by rfl) ⟨257496, by rfl⟩ : syracuseStep 686657 = 514993) (by norm_num)
theorem B1219157 : Blo 539803 1219157 := bbase (se 8 (by rfl) ⟨7143, by rfl⟩ : syracuseStep 1219157 = 14287) (by norm_num)
theorem B2775653 : Blo 539803 2775653 := bbase (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) (by norm_num)
theorem B686713 : Blo 539803 686713 := bbase (se 2 (by rfl) ⟨257517, by rfl⟩ : syracuseStep 686713 = 515035) (by norm_num)
theorem B547465 : Blo 539803 547465 := bbase (se 2 (by rfl) ⟨205299, by rfl⟩ : syracuseStep 547465 = 410599) (by norm_num)
theorem B948893 : Blo 539803 948893 := bbase (se 3 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 948893 = 355835) (by norm_num)
theorem B1219229 : Blo 539803 1219229 := bbase (se 3 (by rfl) ⟨228605, by rfl⟩ : syracuseStep 1219229 = 457211) (by norm_num)
theorem B768685 : Blo 539803 768685 := bbase (se 3 (by rfl) ⟨144128, by rfl⟩ : syracuseStep 768685 = 288257) (by norm_num)
theorem B1366733 : Blo 539803 1366733 := bbase (se 3 (by rfl) ⟨256262, by rfl⟩ : syracuseStep 1366733 = 512525) (by norm_num)
theorem B686809 : Blo 539803 686809 := bbase (se 2 (by rfl) ⟨257553, by rfl⟩ : syracuseStep 686809 = 515107) (by norm_num)
theorem B1219301 : Blo 539803 1219301 := bbase (se 4 (by rfl) ⟨114309, by rfl⟩ : syracuseStep 1219301 = 228619) (by norm_num)
theorem B809717 : Blo 539803 809717 := bbase (se 5 (by rfl) ⟨37955, by rfl⟩ : syracuseStep 809717 = 75911) (by norm_num)
theorem B809741 : Blo 539803 809741 := bbase (se 3 (by rfl) ⟨151826, by rfl⟩ : syracuseStep 809741 = 303653) (by norm_num)
theorem B809765 : Blo 539803 809765 := bbase (se 4 (by rfl) ⟨75915, by rfl⟩ : syracuseStep 809765 = 151831) (by norm_num)
theorem B1219373 : Blo 539803 1219373 := bbase (se 3 (by rfl) ⟨228632, by rfl⟩ : syracuseStep 1219373 = 457265) (by norm_num)
theorem B809789 : Blo 539803 809789 := bbase (se 3 (by rfl) ⟨151835, by rfl⟩ : syracuseStep 809789 = 303671) (by norm_num)
theorem B1301309 : Blo 539803 1301309 := bbase (se 3 (by rfl) ⟨243995, by rfl⟩ : syracuseStep 1301309 = 487991) (by norm_num)
theorem B809813 : Blo 539803 809813 := bbase (se 9 (by rfl) ⟨2372, by rfl⟩ : syracuseStep 809813 = 4745) (by norm_num)
theorem B809837 : Blo 539803 809837 := bbase (se 3 (by rfl) ⟨151844, by rfl⟩ : syracuseStep 809837 = 303689) (by norm_num)
theorem B760693 : Blo 539803 760693 := bbase (se 5 (by rfl) ⟨35657, by rfl⟩ : syracuseStep 760693 = 71315) (by norm_num)
theorem B1219445 : Blo 539803 1219445 := bbase (se 5 (by rfl) ⟨57161, by rfl⟩ : syracuseStep 1219445 = 114323) (by norm_num)
theorem B809861 : Blo 539803 809861 := bbase (se 4 (by rfl) ⟨75924, by rfl⟩ : syracuseStep 809861 = 151849) (by norm_num)
theorem B686981 : Blo 539803 686981 := bbase (se 4 (by rfl) ⟨64404, by rfl⟩ : syracuseStep 686981 = 128809) (by norm_num)
theorem B1825685 : Blo 539803 1825685 := bbase (se 6 (by rfl) ⟨42789, by rfl⟩ : syracuseStep 1825685 = 85579) (by norm_num)
theorem B809885 : Blo 539803 809885 := bbase (se 3 (by rfl) ⟨151853, by rfl⟩ : syracuseStep 809885 = 303707) (by norm_num)
theorem B547741 : Blo 539803 547741 := bbase (se 3 (by rfl) ⟨102701, by rfl⟩ : syracuseStep 547741 = 205403) (by norm_num)
theorem B809909 : Blo 539803 809909 := bbase (se 5 (by rfl) ⟨37964, by rfl⟩ : syracuseStep 809909 = 75929) (by norm_num)
theorem B1219517 : Blo 539803 1219517 := bbase (se 3 (by rfl) ⟨228659, by rfl⟩ : syracuseStep 1219517 = 457319) (by norm_num)
theorem B2735045 : Blo 539803 2735045 := bbase (se 4 (by rfl) ⟨256410, by rfl⟩ : syracuseStep 2735045 = 512821) (by norm_num)
theorem B940997 : Blo 539803 940997 := bbase (se 4 (by rfl) ⟨88218, by rfl⟩ : syracuseStep 940997 = 176437) (by norm_num)
theorem B809933 : Blo 539803 809933 := bbase (se 3 (by rfl) ⟨151862, by rfl⟩ : syracuseStep 809933 = 303725) (by norm_num)
theorem B867277 : Blo 539803 867277 := bbase (se 3 (by rfl) ⟨162614, by rfl⟩ : syracuseStep 867277 = 325229) (by norm_num)
theorem B809957 : Blo 539803 809957 := bbase (se 4 (by rfl) ⟨75933, by rfl⟩ : syracuseStep 809957 = 151867) (by norm_num)
theorem B809981 : Blo 539803 809981 := bbase (se 3 (by rfl) ⟨151871, by rfl⟩ : syracuseStep 809981 = 303743) (by norm_num)
theorem B1301501 : Blo 539803 1301501 := bbase (se 3 (by rfl) ⟨244031, by rfl⟩ : syracuseStep 1301501 = 488063) (by norm_num)
theorem B1219589 : Blo 539803 1219589 := bbase (se 4 (by rfl) ⟨114336, by rfl⟩ : syracuseStep 1219589 = 228673) (by norm_num)
theorem B810005 : Blo 539803 810005 := bbase (se 6 (by rfl) ⟨18984, by rfl⟩ : syracuseStep 810005 = 37969) (by norm_num)
theorem B1367077 : Blo 539803 1367077 := bbase (se 4 (by rfl) ⟨128163, by rfl⟩ : syracuseStep 1367077 = 256327) (by norm_num)
theorem B769061 : Blo 539803 769061 := bbase (se 4 (by rfl) ⟨72099, by rfl⟩ : syracuseStep 769061 = 144199) (by norm_num)
theorem B810029 : Blo 539803 810029 := bbase (se 3 (by rfl) ⟨151880, by rfl⟩ : syracuseStep 810029 = 303761) (by norm_num)
theorem B1539125 : Blo 539803 1539125 := bbase (se 5 (by rfl) ⟨72146, by rfl⟩ : syracuseStep 1539125 = 144293) (by norm_num)
theorem B1170485 : Blo 539803 1170485 := bbase (se 5 (by rfl) ⟨54866, by rfl⟩ : syracuseStep 1170485 = 109733) (by norm_num)
theorem B810053 : Blo 539803 810053 := bbase (se 4 (by rfl) ⟨75942, by rfl⟩ : syracuseStep 810053 = 151885) (by norm_num)
theorem B1219661 : Blo 539803 1219661 := bbase (se 3 (by rfl) ⟨228686, by rfl⟩ : syracuseStep 1219661 = 457373) (by norm_num)
theorem B810077 : Blo 539803 810077 := bbase (se 3 (by rfl) ⟨151889, by rfl⟩ : syracuseStep 810077 = 303779) (by norm_num)
theorem B2227301 : Blo 539803 2227301 := bbase (se 4 (by rfl) ⟨208809, by rfl⟩ : syracuseStep 2227301 = 417619) (by norm_num)
theorem B810101 : Blo 539803 810101 := bbase (se 5 (by rfl) ⟨37973, by rfl⟩ : syracuseStep 810101 = 75947) (by norm_num)
theorem B810125 : Blo 539803 810125 := bbase (se 3 (by rfl) ⟨151898, by rfl⟩ : syracuseStep 810125 = 303797) (by norm_num)
theorem B1367189 : Blo 539803 1367189 := bbase (se 6 (by rfl) ⟨32043, by rfl⟩ : syracuseStep 1367189 = 64087) (by norm_num)
theorem B1219733 : Blo 539803 1219733 := bbase (se 6 (by rfl) ⟨28587, by rfl⟩ : syracuseStep 1219733 = 57175) (by norm_num)
theorem B810149 : Blo 539803 810149 := bbase (se 4 (by rfl) ⟨75951, by rfl⟩ : syracuseStep 810149 = 151903) (by norm_num)
theorem B810173 : Blo 539803 810173 := bbase (se 3 (by rfl) ⟨151907, by rfl⟩ : syracuseStep 810173 = 303815) (by norm_num)
theorem B810197 : Blo 539803 810197 := bbase (se 7 (by rfl) ⟨9494, by rfl⟩ : syracuseStep 810197 = 18989) (by norm_num)
theorem B1219805 : Blo 539803 1219805 := bbase (se 3 (by rfl) ⟨228713, by rfl⟩ : syracuseStep 1219805 = 457427) (by norm_num)
theorem B1465573 : Blo 539803 1465573 := bbase (se 4 (by rfl) ⟨137397, by rfl⟩ : syracuseStep 1465573 = 274795) (by norm_num)
theorem B810221 : Blo 539803 810221 := bbase (se 3 (by rfl) ⟨151916, by rfl⟩ : syracuseStep 810221 = 303833) (by norm_num)
theorem B810245 : Blo 539803 810245 := bbase (se 4 (by rfl) ⟨75960, by rfl⟩ : syracuseStep 810245 = 151921) (by norm_num)
theorem B810269 : Blo 539803 810269 := bbase (se 3 (by rfl) ⟨151925, by rfl⟩ : syracuseStep 810269 = 303851) (by norm_num)
theorem B1301789 : Blo 539803 1301789 := bbase (se 3 (by rfl) ⟨244085, by rfl⟩ : syracuseStep 1301789 = 488171) (by norm_num)
theorem B1219877 : Blo 539803 1219877 := bbase (se 4 (by rfl) ⟨114363, by rfl⟩ : syracuseStep 1219877 = 228727) (by norm_num)
theorem B810293 : Blo 539803 810293 := bbase (se 5 (by rfl) ⟨37982, by rfl⟩ : syracuseStep 810293 = 75965) (by norm_num)
theorem B1826117 : Blo 539803 1826117 := bbase (se 4 (by rfl) ⟨171198, by rfl⟩ : syracuseStep 1826117 = 342397) (by norm_num)
theorem B810317 : Blo 539803 810317 := bbase (se 3 (by rfl) ⟨151934, by rfl⟩ : syracuseStep 810317 = 303869) (by norm_num)
theorem B1367381 : Blo 539803 1367381 := bbase (se 11 (by rfl) ⟨1001, by rfl⟩ : syracuseStep 1367381 = 2003) (by norm_num)
theorem B925013 : Blo 539803 925013 := bbase (se 11 (by rfl) ⟨677, by rfl⟩ : syracuseStep 925013 = 1355) (by norm_num)
theorem B7142741 : Blo 539803 7142741 := bbase (se 11 (by rfl) ⟨5231, by rfl⟩ : syracuseStep 7142741 = 10463) (by norm_num)
theorem B810341 : Blo 539803 810341 := bbase (se 4 (by rfl) ⟨75969, by rfl⟩ : syracuseStep 810341 = 151939) (by norm_num)
theorem B1219949 : Blo 539803 1219949 := bbase (se 3 (by rfl) ⟨228740, by rfl⟩ : syracuseStep 1219949 = 457481) (by norm_num)
theorem B810365 : Blo 539803 810365 := bbase (se 3 (by rfl) ⟨151943, by rfl⟩ : syracuseStep 810365 = 303887) (by norm_num)
theorem B1154429 : Blo 539803 1154429 := bbase (se 3 (by rfl) ⟨216455, by rfl⟩ : syracuseStep 1154429 = 432911) (by norm_num)
theorem B810389 : Blo 539803 810389 := bbase (se 6 (by rfl) ⟨18993, by rfl⟩ : syracuseStep 810389 = 37987) (by norm_num)
theorem B1850789 : Blo 539803 1850789 := bbase (se 4 (by rfl) ⟨173511, by rfl⟩ : syracuseStep 1850789 = 347023) (by norm_num)
theorem B810413 : Blo 539803 810413 := bbase (se 3 (by rfl) ⟨151952, by rfl⟩ : syracuseStep 810413 = 303905) (by norm_num)
theorem B1220021 : Blo 539803 1220021 := bbase (se 5 (by rfl) ⟨57188, by rfl⟩ : syracuseStep 1220021 = 114377) (by norm_num)
theorem B810437 : Blo 539803 810437 := bbase (se 4 (by rfl) ⟨75978, by rfl⟩ : syracuseStep 810437 = 151957) (by norm_num)
theorem B810461 : Blo 539803 810461 := bbase (se 3 (by rfl) ⟨151961, by rfl⟩ : syracuseStep 810461 = 303923) (by norm_num)
theorem B1539557 : Blo 539803 1539557 := bbase (se 4 (by rfl) ⟨144333, by rfl⟩ : syracuseStep 1539557 = 288667) (by norm_num)
theorem B810485 : Blo 539803 810485 := bbase (se 5 (by rfl) ⟨37991, by rfl⟩ : syracuseStep 810485 = 75983) (by norm_num)
theorem B1154549 : Blo 539803 1154549 := bbase (se 5 (by rfl) ⟨54119, by rfl⟩ : syracuseStep 1154549 = 108239) (by norm_num)
theorem B1220093 : Blo 539803 1220093 := bbase (se 3 (by rfl) ⟨228767, by rfl⟩ : syracuseStep 1220093 = 457535) (by norm_num)
theorem B810509 : Blo 539803 810509 := bbase (se 3 (by rfl) ⟨151970, by rfl⟩ : syracuseStep 810509 = 303941) (by norm_num)
theorem B810533 : Blo 539803 810533 := bbase (se 4 (by rfl) ⟨75987, by rfl⟩ : syracuseStep 810533 = 151975) (by norm_num)
theorem B810557 : Blo 539803 810557 := bbase (se 3 (by rfl) ⟨151979, by rfl⟩ : syracuseStep 810557 = 303959) (by norm_num)
theorem B1236541 : Blo 539803 1236541 := bbase (se 3 (by rfl) ⟨231851, by rfl⟩ : syracuseStep 1236541 = 463703) (by norm_num)
theorem B1220165 : Blo 539803 1220165 := bbase (se 4 (by rfl) ⟨114390, by rfl⟩ : syracuseStep 1220165 = 228781) (by norm_num)
theorem B810581 : Blo 539803 810581 := bbase (se 8 (by rfl) ⟨4749, by rfl⟩ : syracuseStep 810581 = 9499) (by norm_num)
theorem B810605 : Blo 539803 810605 := bbase (se 3 (by rfl) ⟨151988, by rfl⟩ : syracuseStep 810605 = 303977) (by norm_num)
theorem B810629 : Blo 539803 810629 := bbase (se 4 (by rfl) ⟨75996, by rfl⟩ : syracuseStep 810629 = 151993) (by norm_num)
theorem B814037 : Blo 539803 814037 := bbase (se 7 (by rfl) ⟨9539, by rfl⟩ : syracuseStep 814037 = 19079) (by norm_num)
theorem B1220237 : Blo 539803 1220237 := bbase (se 3 (by rfl) ⟨228794, by rfl⟩ : syracuseStep 1220237 = 457589) (by norm_num)
theorem B810653 : Blo 539803 810653 := bbase (se 3 (by rfl) ⟨151997, by rfl⟩ : syracuseStep 810653 = 303995) (by norm_num)
theorem B1367725 : Blo 539803 1367725 := bbase (se 3 (by rfl) ⟨256448, by rfl⟩ : syracuseStep 1367725 = 512897) (by norm_num)
theorem B810677 : Blo 539803 810677 := bbase (se 5 (by rfl) ⟨38000, by rfl⟩ : syracuseStep 810677 = 76001) (by norm_num)
theorem B3473077 : Blo 539803 3473077 := bbase (se 5 (by rfl) ⟨162800, by rfl⟩ : syracuseStep 3473077 = 325601) (by norm_num)
theorem B810701 : Blo 539803 810701 := bbase (se 3 (by rfl) ⟨152006, by rfl⟩ : syracuseStep 810701 = 304013) (by norm_num)
theorem B1220309 : Blo 539803 1220309 := bbase (se 7 (by rfl) ⟨14300, by rfl⟩ : syracuseStep 1220309 = 28601) (by norm_num)
theorem B810725 : Blo 539803 810725 := bbase (se 4 (by rfl) ⟨76005, by rfl⟩ : syracuseStep 810725 = 152011) (by norm_num)
theorem B1097453 : Blo 539803 1097453 := bbase (se 3 (by rfl) ⟨205772, by rfl⟩ : syracuseStep 1097453 = 411545) (by norm_num)
theorem B1826549 : Blo 539803 1826549 := bbase (se 5 (by rfl) ⟨85619, by rfl⟩ : syracuseStep 1826549 = 171239) (by norm_num)
theorem B1736437 : Blo 539803 1736437 := bbase (se 5 (by rfl) ⟨81395, by rfl⟩ : syracuseStep 1736437 = 162791) (by norm_num)
theorem B810749 : Blo 539803 810749 := bbase (se 3 (by rfl) ⟨152015, by rfl⟩ : syracuseStep 810749 = 304031) (by norm_num)
theorem B974597 : Blo 539803 974597 := bbase (se 4 (by rfl) ⟨91368, by rfl⟩ : syracuseStep 974597 = 182737) (by norm_num)
theorem B548617 : Blo 539803 548617 := bbase (se 2 (by rfl) ⟨205731, by rfl⟩ : syracuseStep 548617 = 411463) (by norm_num)
theorem B2629397 : Blo 539803 2629397 := bbase (se 6 (by rfl) ⟨61626, by rfl⟩ : syracuseStep 2629397 = 123253) (by norm_num)
theorem B810773 : Blo 539803 810773 := bbase (se 6 (by rfl) ⟨19002, by rfl⟩ : syracuseStep 810773 = 38005) (by norm_num)
theorem B1367837 : Blo 539803 1367837 := bbase (se 3 (by rfl) ⟨256469, by rfl⟩ : syracuseStep 1367837 = 512939) (by norm_num)
theorem B1220381 : Blo 539803 1220381 := bbase (se 3 (by rfl) ⟨228821, by rfl⟩ : syracuseStep 1220381 = 457643) (by norm_num)
theorem B810797 : Blo 539803 810797 := bbase (se 3 (by rfl) ⟨152024, by rfl⟩ : syracuseStep 810797 = 304049) (by norm_num)
theorem B2817845 : Blo 539803 2817845 := bbase (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) (by norm_num)
theorem B2744117 : Blo 539803 2744117 := bbase (se 5 (by rfl) ⟨128630, by rfl⟩ : syracuseStep 2744117 = 257261) (by norm_num)
theorem B810821 : Blo 539803 810821 := bbase (se 4 (by rfl) ⟨76014, by rfl⟩ : syracuseStep 810821 = 152029) (by norm_num)
theorem B810845 : Blo 539803 810845 := bbase (se 3 (by rfl) ⟨152033, by rfl⟩ : syracuseStep 810845 = 304067) (by norm_num)
theorem B1220453 : Blo 539803 1220453 := bbase (se 4 (by rfl) ⟨114417, by rfl⟩ : syracuseStep 1220453 = 228835) (by norm_num)
theorem B868205 : Blo 539803 868205 := bbase (se 3 (by rfl) ⟨162788, by rfl⟩ : syracuseStep 868205 = 325577) (by norm_num)
theorem B810869 : Blo 539803 810869 := bbase (se 5 (by rfl) ⟨38009, by rfl⟩ : syracuseStep 810869 = 76019) (by norm_num)
theorem B1056629 : Blo 539803 1056629 := bbase (se 5 (by rfl) ⟨49529, by rfl⟩ : syracuseStep 1056629 = 99059) (by norm_num)
theorem B810893 : Blo 539803 810893 := bbase (se 3 (by rfl) ⟨152042, by rfl⟩ : syracuseStep 810893 = 304085) (by norm_num)
theorem B3899285 : Blo 539803 3899285 := bbase (se 6 (by rfl) ⟨91389, by rfl⟩ : syracuseStep 3899285 = 182779) (by norm_num)
theorem B810917 : Blo 539803 810917 := bbase (se 4 (by rfl) ⟨76023, by rfl⟩ : syracuseStep 810917 = 152047) (by norm_num)
theorem B1220525 : Blo 539803 1220525 := bbase (se 3 (by rfl) ⟨228848, by rfl⟩ : syracuseStep 1220525 = 457697) (by norm_num)
theorem B3694517 : Blo 539803 3694517 := bbase (se 5 (by rfl) ⟨173180, by rfl⟩ : syracuseStep 3694517 = 346361) (by norm_num)
theorem B810941 : Blo 539803 810941 := bbase (se 3 (by rfl) ⟨152051, by rfl⟩ : syracuseStep 810941 = 304103) (by norm_num)
theorem B810965 : Blo 539803 810965 := bbase (se 7 (by rfl) ⟨9503, by rfl⟩ : syracuseStep 810965 = 19007) (by norm_num)
theorem B1368029 : Blo 539803 1368029 := bbase (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) (by norm_num)
theorem B810989 : Blo 539803 810989 := bbase (se 3 (by rfl) ⟨152060, by rfl⟩ : syracuseStep 810989 = 304121) (by norm_num)
theorem B1220597 : Blo 539803 1220597 := bbase (se 5 (by rfl) ⟨57215, by rfl⟩ : syracuseStep 1220597 = 114431) (by norm_num)
theorem B540675 : Blo 539803 540675 := bstep (se 1 (by rfl) ⟨405506, by rfl⟩ : syracuseStep 540675 = 811013) B811013
theorem B1826819 : Blo 539803 1826819 := bstep (se 1 (by rfl) ⟨1370114, by rfl⟩ : syracuseStep 1826819 = 2740229) B2740229
theorem B2056205 : Blo 539803 2056205 := bstep (se 3 (by rfl) ⟨385538, by rfl⟩ : syracuseStep 2056205 = 771077) B771077
theorem B811025 : Blo 539803 811025 := bstep (se 2 (by rfl) ⟨304134, by rfl⟩ : syracuseStep 811025 = 608269) B608269
theorem B540691 : Blo 539803 540691 := bstep (se 1 (by rfl) ⟨405518, by rfl⟩ : syracuseStep 540691 = 811037) B811037
theorem B811043 : Blo 539803 811043 := bstep (se 1 (by rfl) ⟨608282, by rfl⟩ : syracuseStep 811043 = 1216565) B1216565
theorem B540707 : Blo 539803 540707 := bstep (se 1 (by rfl) ⟨405530, by rfl⟩ : syracuseStep 540707 = 811061) B811061
theorem B1564721 : Blo 539803 1564721 := bstep (se 2 (by rfl) ⟨586770, by rfl⟩ : syracuseStep 1564721 = 1173541) B1173541
theorem B540723 : Blo 539803 540723 := bstep (se 1 (by rfl) ⟨405542, by rfl⟩ : syracuseStep 540723 = 811085) B811085
theorem B10395701 : Blo 539803 10395701 := bstep (se 5 (by rfl) ⟨487298, by rfl⟩ : syracuseStep 10395701 = 974597) B974597
theorem B811073 : Blo 539803 811073 := bstep (se 2 (by rfl) ⟨304152, by rfl⟩ : syracuseStep 811073 = 608305) B608305
theorem B540739 : Blo 539803 540739 := bstep (se 1 (by rfl) ⟨405554, by rfl⟩ : syracuseStep 540739 = 811109) B811109
theorem B811091 : Blo 539803 811091 := bstep (se 1 (by rfl) ⟨608318, by rfl⟩ : syracuseStep 811091 = 1216637) B1216637
theorem B540755 : Blo 539803 540755 := bstep (se 1 (by rfl) ⟨405566, by rfl⟩ : syracuseStep 540755 = 811133) B811133
theorem B540771 : Blo 539803 540771 := bstep (se 1 (by rfl) ⟨405578, by rfl⟩ : syracuseStep 540771 = 811157) B811157
theorem B811121 : Blo 539803 811121 := bstep (se 2 (by rfl) ⟨304170, by rfl⟩ : syracuseStep 811121 = 608341) B608341
theorem B2924657 : Blo 539803 2924657 := bstep (se 2 (by rfl) ⟨1096746, by rfl⟩ : syracuseStep 2924657 = 2193493) B2193493
theorem B540787 : Blo 539803 540787 := bstep (se 1 (by rfl) ⟨405590, by rfl⟩ : syracuseStep 540787 = 811181) B811181
theorem B811139 : Blo 539803 811139 := bstep (se 1 (by rfl) ⟨608354, by rfl⟩ : syracuseStep 811139 = 1216709) B1216709
theorem B540803 : Blo 539803 540803 := bstep (se 1 (by rfl) ⟨405602, by rfl⟩ : syracuseStep 540803 = 811205) B811205
theorem B1540241 : Blo 539803 1540241 := bstep (se 2 (by rfl) ⟨577590, by rfl⟩ : syracuseStep 1540241 = 1155181) B1155181
theorem B540819 : Blo 539803 540819 := bstep (se 1 (by rfl) ⟨405614, by rfl⟩ : syracuseStep 540819 = 811229) B811229
theorem B811169 : Blo 539803 811169 := bstep (se 2 (by rfl) ⟨304188, by rfl⟩ : syracuseStep 811169 = 608377) B608377
theorem B540835 : Blo 539803 540835 := bstep (se 1 (by rfl) ⟨405626, by rfl⟩ : syracuseStep 540835 = 811253) B811253
theorem B811187 : Blo 539803 811187 := bstep (se 1 (by rfl) ⟨608390, by rfl⟩ : syracuseStep 811187 = 1216781) B1216781
theorem B540851 : Blo 539803 540851 := bstep (se 1 (by rfl) ⟨405638, by rfl⟩ : syracuseStep 540851 = 811277) B811277
theorem B540867 : Blo 539803 540867 := bstep (se 1 (by rfl) ⟨405650, by rfl⟩ : syracuseStep 540867 = 811301) B811301
theorem B3080389 : Blo 539803 3080389 := bstep (se 4 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 3080389 = 577573) B577573
theorem B811217 : Blo 539803 811217 := bstep (se 2 (by rfl) ⟨304206, by rfl⟩ : syracuseStep 811217 = 608413) B608413
theorem B770257 : Blo 539803 770257 := bstep (se 2 (by rfl) ⟨288846, by rfl⟩ : syracuseStep 770257 = 577693) B577693
theorem B540883 : Blo 539803 540883 := bstep (se 1 (by rfl) ⟨405662, by rfl⟩ : syracuseStep 540883 = 811325) B811325
theorem B811235 : Blo 539803 811235 := bstep (se 1 (by rfl) ⟨608426, by rfl⟩ : syracuseStep 811235 = 1216853) B1216853
theorem B540899 : Blo 539803 540899 := bstep (se 1 (by rfl) ⟨405674, by rfl⟩ : syracuseStep 540899 = 811349) B811349
theorem B1220849 : Blo 539803 1220849 := bstep (se 2 (by rfl) ⟨457818, by rfl⟩ : syracuseStep 1220849 = 915637) B915637
theorem B540915 : Blo 539803 540915 := bstep (se 1 (by rfl) ⟨405686, by rfl⟩ : syracuseStep 540915 = 811373) B811373
theorem B811265 : Blo 539803 811265 := bstep (se 2 (by rfl) ⟨304224, by rfl⟩ : syracuseStep 811265 = 608449) B608449
theorem B1368323 : Blo 539803 1368323 := bstep (se 1 (by rfl) ⟨1026242, by rfl⟩ : syracuseStep 1368323 = 2052485) B2052485
theorem B540931 : Blo 539803 540931 := bstep (se 1 (by rfl) ⟨405698, by rfl⟩ : syracuseStep 540931 = 811397) B811397
theorem B1220867 : Blo 539803 1220867 := bstep (se 1 (by rfl) ⟨915650, by rfl⟩ : syracuseStep 1220867 = 1831301) B1831301
theorem B1827089 : Blo 539803 1827089 := bstep (se 2 (by rfl) ⟨685158, by rfl⟩ : syracuseStep 1827089 = 1370317) B1370317
theorem B811283 : Blo 539803 811283 := bstep (se 1 (by rfl) ⟨608462, by rfl⟩ : syracuseStep 811283 = 1216925) B1216925
theorem B540947 : Blo 539803 540947 := bstep (se 1 (by rfl) ⟨405710, by rfl⟩ : syracuseStep 540947 = 811421) B811421
theorem B26665237 : Blo 539803 26665237 := bstep (se 6 (by rfl) ⟨624966, by rfl⟩ : syracuseStep 26665237 = 1249933) B1249933
theorem B540963 : Blo 539803 540963 := bstep (se 1 (by rfl) ⟨405722, by rfl⟩ : syracuseStep 540963 = 811445) B811445
theorem B811313 : Blo 539803 811313 := bstep (se 2 (by rfl) ⟨304242, by rfl⟩ : syracuseStep 811313 = 608485) B608485
theorem B540979 : Blo 539803 540979 := bstep (se 1 (by rfl) ⟨405734, by rfl⟩ : syracuseStep 540979 = 811469) B811469
theorem B811331 : Blo 539803 811331 := bstep (se 1 (by rfl) ⟨608498, by rfl⟩ : syracuseStep 811331 = 1216997) B1216997
theorem B540995 : Blo 539803 540995 := bstep (se 1 (by rfl) ⟨405746, by rfl⟩ : syracuseStep 540995 = 811493) B811493
theorem B541011 : Blo 539803 541011 := bstep (se 1 (by rfl) ⟨405758, by rfl⟩ : syracuseStep 541011 = 811517) B811517
theorem B811361 : Blo 539803 811361 := bstep (se 2 (by rfl) ⟨304260, by rfl⟩ : syracuseStep 811361 = 608521) B608521
theorem B541027 : Blo 539803 541027 := bstep (se 1 (by rfl) ⟨405770, by rfl⟩ : syracuseStep 541027 = 811541) B811541
theorem B811379 : Blo 539803 811379 := bstep (se 1 (by rfl) ⟨608534, by rfl⟩ : syracuseStep 811379 = 1217069) B1217069
theorem B541043 : Blo 539803 541043 := bstep (se 1 (by rfl) ⟨405782, by rfl⟩ : syracuseStep 541043 = 811565) B811565
theorem B541059 : Blo 539803 541059 := bstep (se 1 (by rfl) ⟨405794, by rfl⟩ : syracuseStep 541059 = 811589) B811589
theorem B811409 : Blo 539803 811409 := bstep (se 2 (by rfl) ⟨304278, by rfl⟩ : syracuseStep 811409 = 608557) B608557
theorem B541075 : Blo 539803 541075 := bstep (se 1 (by rfl) ⟨405806, by rfl⟩ : syracuseStep 541075 = 811613) B811613
theorem B811427 : Blo 539803 811427 := bstep (se 1 (by rfl) ⟨608570, by rfl⟩ : syracuseStep 811427 = 1217141) B1217141
theorem B541091 : Blo 539803 541091 := bstep (se 1 (by rfl) ⟨405818, by rfl⟩ : syracuseStep 541091 = 811637) B811637
theorem B541107 : Blo 539803 541107 := bstep (se 1 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 541107 = 811661) B811661
theorem B811457 : Blo 539803 811457 := bstep (se 2 (by rfl) ⟨304296, by rfl⟩ : syracuseStep 811457 = 608593) B608593
theorem B1368515 : Blo 539803 1368515 := bstep (se 1 (by rfl) ⟨1026386, by rfl⟩ : syracuseStep 1368515 = 2052773) B2052773
theorem B541123 : Blo 539803 541123 := bstep (se 1 (by rfl) ⟨405842, by rfl⟩ : syracuseStep 541123 = 811685) B811685
theorem B926147 : Blo 539803 926147 := bstep (se 1 (by rfl) ⟨694610, by rfl⟩ : syracuseStep 926147 = 1389221) B1389221
theorem B811475 : Blo 539803 811475 := bstep (se 1 (by rfl) ⟨608606, by rfl⟩ : syracuseStep 811475 = 1217213) B1217213
theorem B541139 : Blo 539803 541139 := bstep (se 1 (by rfl) ⟨405854, by rfl⟩ : syracuseStep 541139 = 811709) B811709
theorem B541155 : Blo 539803 541155 := bstep (se 1 (by rfl) ⟨405866, by rfl⟩ : syracuseStep 541155 = 811733) B811733
theorem B811505 : Blo 539803 811505 := bstep (se 2 (by rfl) ⟨304314, by rfl⟩ : syracuseStep 811505 = 608629) B608629
theorem B541171 : Blo 539803 541171 := bstep (se 1 (by rfl) ⟨405878, by rfl⟩ : syracuseStep 541171 = 811757) B811757
theorem B811523 : Blo 539803 811523 := bstep (se 1 (by rfl) ⟨608642, by rfl⟩ : syracuseStep 811523 = 1217285) B1217285
theorem B541187 : Blo 539803 541187 := bstep (se 1 (by rfl) ⟨405890, by rfl⟩ : syracuseStep 541187 = 811781) B811781
theorem B1221137 : Blo 539803 1221137 := bstep (se 2 (by rfl) ⟨457926, by rfl⟩ : syracuseStep 1221137 = 915853) B915853
theorem B541203 : Blo 539803 541203 := bstep (se 1 (by rfl) ⟨405902, by rfl⟩ : syracuseStep 541203 = 811805) B811805
theorem B811553 : Blo 539803 811553 := bstep (se 2 (by rfl) ⟨304332, by rfl⟩ : syracuseStep 811553 = 608665) B608665
theorem B541219 : Blo 539803 541219 := bstep (se 1 (by rfl) ⟨405914, by rfl⟩ : syracuseStep 541219 = 811829) B811829
theorem B868897 : Blo 539803 868897 := bstep (se 2 (by rfl) ⟨325836, by rfl⟩ : syracuseStep 868897 = 651673) B651673
theorem B1221155 : Blo 539803 1221155 := bstep (se 1 (by rfl) ⟨915866, by rfl⟩ : syracuseStep 1221155 = 1831733) B1831733
theorem B811571 : Blo 539803 811571 := bstep (se 1 (by rfl) ⟨608678, by rfl⟩ : syracuseStep 811571 = 1217357) B1217357
theorem B12485173 : Blo 539803 12485173 := bstep (se 5 (by rfl) ⟨585242, by rfl⟩ : syracuseStep 12485173 = 1170485) B1170485
theorem B541235 : Blo 539803 541235 := bstep (se 1 (by rfl) ⟨405926, by rfl⟩ : syracuseStep 541235 = 811853) B811853
theorem B3129905 : Blo 539803 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B541251 : Blo 539803 541251 := bstep (se 1 (by rfl) ⟨405938, by rfl⟩ : syracuseStep 541251 = 811877) B811877
theorem B811601 : Blo 539803 811601 := bstep (se 2 (by rfl) ⟨304350, by rfl⟩ : syracuseStep 811601 = 608701) B608701
theorem B541267 : Blo 539803 541267 := bstep (se 1 (by rfl) ⟨405950, by rfl⟩ : syracuseStep 541267 = 811901) B811901
theorem B3465827 : Blo 539803 3465827 := bstep (se 1 (by rfl) ⟨2599370, by rfl⟩ : syracuseStep 3465827 = 5198741) B5198741
theorem B811619 : Blo 539803 811619 := bstep (se 1 (by rfl) ⟨608714, by rfl⟩ : syracuseStep 811619 = 1217429) B1217429
theorem B541283 : Blo 539803 541283 := bstep (se 1 (by rfl) ⟨405962, by rfl⟩ : syracuseStep 541283 = 811925) B811925
theorem B2228849 : Blo 539803 2228849 := bstep (se 2 (by rfl) ⟨835818, by rfl⟩ : syracuseStep 2228849 = 1671637) B1671637
theorem B541299 : Blo 539803 541299 := bstep (se 1 (by rfl) ⟨405974, by rfl⟩ : syracuseStep 541299 = 811949) B811949
theorem B811649 : Blo 539803 811649 := bstep (se 2 (by rfl) ⟨304368, by rfl⟩ : syracuseStep 811649 = 608737) B608737
theorem B541315 : Blo 539803 541315 := bstep (se 1 (by rfl) ⟨405986, by rfl⟩ : syracuseStep 541315 = 811973) B811973
theorem B811667 : Blo 539803 811667 := bstep (se 1 (by rfl) ⟨608750, by rfl⟩ : syracuseStep 811667 = 1217501) B1217501
theorem B541331 : Blo 539803 541331 := bstep (se 1 (by rfl) ⟨405998, by rfl⟩ : syracuseStep 541331 = 811997) B811997
theorem B541347 : Blo 539803 541347 := bstep (se 1 (by rfl) ⟨406010, by rfl⟩ : syracuseStep 541347 = 812021) B812021
theorem B811697 : Blo 539803 811697 := bstep (se 2 (by rfl) ⟨304386, by rfl⟩ : syracuseStep 811697 = 608773) B608773
theorem B541363 : Blo 539803 541363 := bstep (se 1 (by rfl) ⟨406022, by rfl⟩ : syracuseStep 541363 = 812045) B812045
theorem B811715 : Blo 539803 811715 := bstep (se 1 (by rfl) ⟨608786, by rfl⟩ : syracuseStep 811715 = 1217573) B1217573
theorem B1155779 : Blo 539803 1155779 := bstep (se 1 (by rfl) ⟨866834, by rfl⟩ : syracuseStep 1155779 = 1733669) B1733669
theorem B541379 : Blo 539803 541379 := bstep (se 1 (by rfl) ⟨406034, by rfl⟩ : syracuseStep 541379 = 812069) B812069
theorem B541395 : Blo 539803 541395 := bstep (se 1 (by rfl) ⟨406046, by rfl⟩ : syracuseStep 541395 = 812093) B812093
theorem B811745 : Blo 539803 811745 := bstep (se 2 (by rfl) ⟨304404, by rfl⟩ : syracuseStep 811745 = 608809) B608809
theorem B541411 : Blo 539803 541411 := bstep (se 1 (by rfl) ⟨406058, by rfl⟩ : syracuseStep 541411 = 812117) B812117
theorem B2081521 : Blo 539803 2081521 := bstep (se 2 (by rfl) ⟨780570, by rfl⟩ : syracuseStep 2081521 = 1561141) B1561141
theorem B811763 : Blo 539803 811763 := bstep (se 1 (by rfl) ⟨608822, by rfl⟩ : syracuseStep 811763 = 1217645) B1217645
theorem B541427 : Blo 539803 541427 := bstep (se 1 (by rfl) ⟨406070, by rfl⟩ : syracuseStep 541427 = 812141) B812141
theorem B3089137 : Blo 539803 3089137 := bstep (se 2 (by rfl) ⟨1158426, by rfl⟩ : syracuseStep 3089137 = 2316853) B2316853
theorem B541443 : Blo 539803 541443 := bstep (se 1 (by rfl) ⟨406082, by rfl⟩ : syracuseStep 541443 = 812165) B812165
theorem B811793 : Blo 539803 811793 := bstep (se 2 (by rfl) ⟨304422, by rfl⟩ : syracuseStep 811793 = 608845) B608845
theorem B541459 : Blo 539803 541459 := bstep (se 1 (by rfl) ⟨406094, by rfl⟩ : syracuseStep 541459 = 812189) B812189
theorem B811811 : Blo 539803 811811 := bstep (se 1 (by rfl) ⟨608858, by rfl⟩ : syracuseStep 811811 = 1217717) B1217717
theorem B541475 : Blo 539803 541475 := bstep (se 1 (by rfl) ⟨406106, by rfl⟩ : syracuseStep 541475 = 812213) B812213
theorem B1729325 : Blo 539803 1729325 := bstep (se 3 (by rfl) ⟨324248, by rfl⟩ : syracuseStep 1729325 = 648497) B648497
theorem B1827629 : Blo 539803 1827629 := bstep (se 3 (by rfl) ⟨342680, by rfl⟩ : syracuseStep 1827629 = 685361) B685361
theorem B541491 : Blo 539803 541491 := bstep (se 1 (by rfl) ⟨406118, by rfl⟩ : syracuseStep 541491 = 812237) B812237
theorem B811841 : Blo 539803 811841 := bstep (se 2 (by rfl) ⟨304440, by rfl⟩ : syracuseStep 811841 = 608881) B608881
theorem B541507 : Blo 539803 541507 := bstep (se 1 (by rfl) ⟨406130, by rfl⟩ : syracuseStep 541507 = 812261) B812261
theorem B811859 : Blo 539803 811859 := bstep (se 1 (by rfl) ⟨608894, by rfl⟩ : syracuseStep 811859 = 1217789) B1217789
theorem B541523 : Blo 539803 541523 := bstep (se 1 (by rfl) ⟨406142, by rfl⟩ : syracuseStep 541523 = 812285) B812285
theorem B729953 : Blo 539803 729953 := bstep (se 2 (by rfl) ⟨273732, by rfl⟩ : syracuseStep 729953 = 547465) B547465
theorem B1827683 : Blo 539803 1827683 := bstep (se 1 (by rfl) ⟨1370762, by rfl⟩ : syracuseStep 1827683 = 2741525) B2741525
theorem B541539 : Blo 539803 541539 := bstep (se 1 (by rfl) ⟨406154, by rfl⟩ : syracuseStep 541539 = 812309) B812309
theorem B811889 : Blo 539803 811889 := bstep (se 2 (by rfl) ⟨304458, by rfl⟩ : syracuseStep 811889 = 608917) B608917
theorem B541555 : Blo 539803 541555 := bstep (se 1 (by rfl) ⟨406166, by rfl⟩ : syracuseStep 541555 = 812333) B812333
theorem B811907 : Blo 539803 811907 := bstep (se 1 (by rfl) ⟨608930, by rfl⟩ : syracuseStep 811907 = 1217861) B1217861
theorem B541571 : Blo 539803 541571 := bstep (se 1 (by rfl) ⟨406178, by rfl⟩ : syracuseStep 541571 = 812357) B812357
theorem B1024913 : Blo 539803 1024913 := bstep (se 2 (by rfl) ⟨384342, by rfl⟩ : syracuseStep 1024913 = 768685) B768685
theorem B770963 : Blo 539803 770963 := bstep (se 1 (by rfl) ⟨578222, by rfl⟩ : syracuseStep 770963 = 1156445) B1156445
theorem B541587 : Blo 539803 541587 := bstep (se 1 (by rfl) ⟨406190, by rfl⟩ : syracuseStep 541587 = 812381) B812381
theorem B811937 : Blo 539803 811937 := bstep (se 2 (by rfl) ⟨304476, by rfl⟩ : syracuseStep 811937 = 608953) B608953
theorem B541603 : Blo 539803 541603 := bstep (se 1 (by rfl) ⟨406202, by rfl⟩ : syracuseStep 541603 = 812405) B812405
theorem B2745251 : Blo 539803 2745251 := bstep (se 1 (by rfl) ⟨2058938, by rfl⟩ : syracuseStep 2745251 = 4117877) B4117877
theorem B811955 : Blo 539803 811955 := bstep (se 1 (by rfl) ⟨608966, by rfl⟩ : syracuseStep 811955 = 1217933) B1217933
theorem B541619 : Blo 539803 541619 := bstep (se 1 (by rfl) ⟨406214, by rfl⟩ : syracuseStep 541619 = 812429) B812429
theorem B541635 : Blo 539803 541635 := bstep (se 1 (by rfl) ⟨406226, by rfl⟩ : syracuseStep 541635 = 812453) B812453
theorem B811985 : Blo 539803 811985 := bstep (se 2 (by rfl) ⟨304494, by rfl⟩ : syracuseStep 811985 = 608989) B608989
theorem B541651 : Blo 539803 541651 := bstep (se 1 (by rfl) ⟨406238, by rfl⟩ : syracuseStep 541651 = 812477) B812477
theorem B812003 : Blo 539803 812003 := bstep (se 1 (by rfl) ⟨609002, by rfl⟩ : syracuseStep 812003 = 1218005) B1218005
theorem B541667 : Blo 539803 541667 := bstep (se 1 (by rfl) ⟨406250, by rfl⟩ : syracuseStep 541667 = 812501) B812501
theorem B541683 : Blo 539803 541683 := bstep (se 1 (by rfl) ⟨406262, by rfl⟩ : syracuseStep 541683 = 812525) B812525
theorem B812033 : Blo 539803 812033 := bstep (se 2 (by rfl) ⟨304512, by rfl⟩ : syracuseStep 812033 = 609025) B609025
theorem B541699 : Blo 539803 541699 := bstep (se 1 (by rfl) ⟨406274, by rfl⟩ : syracuseStep 541699 = 812549) B812549
theorem B812051 : Blo 539803 812051 := bstep (se 1 (by rfl) ⟨609038, by rfl⟩ : syracuseStep 812051 = 1218077) B1218077
theorem B541715 : Blo 539803 541715 := bstep (se 1 (by rfl) ⟨406286, by rfl⟩ : syracuseStep 541715 = 812573) B812573
theorem B541731 : Blo 539803 541731 := bstep (se 1 (by rfl) ⟨406298, by rfl⟩ : syracuseStep 541731 = 812597) B812597
theorem B812081 : Blo 539803 812081 := bstep (se 2 (by rfl) ⟨304530, by rfl⟩ : syracuseStep 812081 = 609061) B609061
theorem B541747 : Blo 539803 541747 := bstep (se 1 (by rfl) ⟨406310, by rfl⟩ : syracuseStep 541747 = 812621) B812621
theorem B812099 : Blo 539803 812099 := bstep (se 1 (by rfl) ⟨609074, by rfl⟩ : syracuseStep 812099 = 1218149) B1218149
theorem B541763 : Blo 539803 541763 := bstep (se 1 (by rfl) ⟨406322, by rfl⟩ : syracuseStep 541763 = 812645) B812645
theorem B1541197 : Blo 539803 1541197 := bstep (se 3 (by rfl) ⟨288974, by rfl⟩ : syracuseStep 1541197 = 577949) B577949
theorem B1950797 : Blo 539803 1950797 := bstep (se 3 (by rfl) ⟨365774, by rfl⟩ : syracuseStep 1950797 = 731549) B731549
theorem B607315 : Blo 539803 607315 := bstep (se 1 (by rfl) ⟨455486, by rfl⟩ : syracuseStep 607315 = 910973) B910973
theorem B541779 : Blo 539803 541779 := bstep (se 1 (by rfl) ⟨406334, by rfl⟩ : syracuseStep 541779 = 812669) B812669
theorem B812129 : Blo 539803 812129 := bstep (se 2 (by rfl) ⟨304548, by rfl⟩ : syracuseStep 812129 = 609097) B609097
theorem B6161507 : Blo 539803 6161507 := bstep (se 1 (by rfl) ⟨4621130, by rfl⟩ : syracuseStep 6161507 = 9242261) B9242261
theorem B541795 : Blo 539803 541795 := bstep (se 1 (by rfl) ⟨406346, by rfl⟩ : syracuseStep 541795 = 812693) B812693
theorem B1827953 : Blo 539803 1827953 := bstep (se 2 (by rfl) ⟨685482, by rfl⟩ : syracuseStep 1827953 = 1370965) B1370965
theorem B812147 : Blo 539803 812147 := bstep (se 1 (by rfl) ⟨609110, by rfl⟩ : syracuseStep 812147 = 1218221) B1218221
theorem B541811 : Blo 539803 541811 := bstep (se 1 (by rfl) ⟨406358, by rfl⟩ : syracuseStep 541811 = 812717) B812717
theorem B541827 : Blo 539803 541827 := bstep (se 1 (by rfl) ⟨406370, by rfl⟩ : syracuseStep 541827 = 812741) B812741
theorem B812177 : Blo 539803 812177 := bstep (se 2 (by rfl) ⟨304566, by rfl⟩ : syracuseStep 812177 = 609133) B609133
theorem B541843 : Blo 539803 541843 := bstep (se 1 (by rfl) ⟨406382, by rfl⟩ : syracuseStep 541843 = 812765) B812765
theorem B812195 : Blo 539803 812195 := bstep (se 1 (by rfl) ⟨609146, by rfl⟩ : syracuseStep 812195 = 1218293) B1218293
theorem B541859 : Blo 539803 541859 := bstep (se 1 (by rfl) ⟨406394, by rfl⟩ : syracuseStep 541859 = 812789) B812789
theorem B541875 : Blo 539803 541875 := bstep (se 1 (by rfl) ⟨406406, by rfl⟩ : syracuseStep 541875 = 812813) B812813
theorem B812225 : Blo 539803 812225 := bstep (se 2 (by rfl) ⟨304584, by rfl⟩ : syracuseStep 812225 = 609169) B609169
theorem B541891 : Blo 539803 541891 := bstep (se 1 (by rfl) ⟨406418, by rfl⟩ : syracuseStep 541891 = 812837) B812837
theorem B812243 : Blo 539803 812243 := bstep (se 1 (by rfl) ⟨609182, by rfl⟩ : syracuseStep 812243 = 1218365) B1218365
theorem B541907 : Blo 539803 541907 := bstep (se 1 (by rfl) ⟨406430, by rfl⟩ : syracuseStep 541907 = 812861) B812861
theorem B607459 : Blo 539803 607459 := bstep (se 1 (by rfl) ⟨455594, by rfl⟩ : syracuseStep 607459 = 911189) B911189
theorem B541923 : Blo 539803 541923 := bstep (se 1 (by rfl) ⟨406442, by rfl⟩ : syracuseStep 541923 = 812885) B812885
theorem B812273 : Blo 539803 812273 := bstep (se 2 (by rfl) ⟨304602, by rfl⟩ : syracuseStep 812273 = 609205) B609205
theorem B541939 : Blo 539803 541939 := bstep (se 1 (by rfl) ⟨406454, by rfl⟩ : syracuseStep 541939 = 812909) B812909
theorem B812291 : Blo 539803 812291 := bstep (se 1 (by rfl) ⟨609218, by rfl⟩ : syracuseStep 812291 = 1218437) B1218437
theorem B541955 : Blo 539803 541955 := bstep (se 1 (by rfl) ⟨406466, by rfl⟩ : syracuseStep 541955 = 812933) B812933
theorem B1156369 : Blo 539803 1156369 := bstep (se 2 (by rfl) ⟨433638, by rfl⟩ : syracuseStep 1156369 = 867277) B867277
theorem B541971 : Blo 539803 541971 := bstep (se 1 (by rfl) ⟨406478, by rfl⟩ : syracuseStep 541971 = 812957) B812957
theorem B812321 : Blo 539803 812321 := bstep (se 2 (by rfl) ⟨304620, by rfl⟩ : syracuseStep 812321 = 609241) B609241
theorem B541987 : Blo 539803 541987 := bstep (se 1 (by rfl) ⟨406490, by rfl⟩ : syracuseStep 541987 = 812981) B812981
theorem B1541425 : Blo 539803 1541425 := bstep (se 2 (by rfl) ⟨578034, by rfl⟩ : syracuseStep 1541425 = 1156069) B1156069
theorem B812339 : Blo 539803 812339 := bstep (se 1 (by rfl) ⟨609254, by rfl⟩ : syracuseStep 812339 = 1218509) B1218509
theorem B542003 : Blo 539803 542003 := bstep (se 1 (by rfl) ⟨406502, by rfl⟩ : syracuseStep 542003 = 813005) B813005
theorem B7808309 : Blo 539803 7808309 := bstep (se 5 (by rfl) ⟨366014, by rfl⟩ : syracuseStep 7808309 = 732029) B732029
theorem B542019 : Blo 539803 542019 := bstep (se 1 (by rfl) ⟨406514, by rfl⟩ : syracuseStep 542019 = 813029) B813029
theorem B812369 : Blo 539803 812369 := bstep (se 2 (by rfl) ⟨304638, by rfl⟩ : syracuseStep 812369 = 609277) B609277
theorem B542035 : Blo 539803 542035 := bstep (se 1 (by rfl) ⟨406526, by rfl⟩ : syracuseStep 542035 = 813053) B813053
theorem B877921 : Blo 539803 877921 := bstep (se 2 (by rfl) ⟨329220, by rfl⟩ : syracuseStep 877921 = 658441) B658441
theorem B2311523 : Blo 539803 2311523 := bstep (se 1 (by rfl) ⟨1733642, by rfl⟩ : syracuseStep 2311523 = 3467285) B3467285
theorem B812387 : Blo 539803 812387 := bstep (se 1 (by rfl) ⟨609290, by rfl⟩ : syracuseStep 812387 = 1218581) B1218581
theorem B542051 : Blo 539803 542051 := bstep (se 1 (by rfl) ⟨406538, by rfl⟩ : syracuseStep 542051 = 813077) B813077
theorem B1369457 : Blo 539803 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B607603 : Blo 539803 607603 := bstep (se 1 (by rfl) ⟨455702, by rfl⟩ : syracuseStep 607603 = 911405) B911405
theorem B542067 : Blo 539803 542067 := bstep (se 1 (by rfl) ⟨406550, by rfl⟩ : syracuseStep 542067 = 813101) B813101
theorem B812417 : Blo 539803 812417 := bstep (se 2 (by rfl) ⟨304656, by rfl⟩ : syracuseStep 812417 = 609313) B609313
theorem B542083 : Blo 539803 542083 := bstep (se 1 (by rfl) ⟨406562, by rfl⟩ : syracuseStep 542083 = 813125) B813125
theorem B812435 : Blo 539803 812435 := bstep (se 1 (by rfl) ⟨609326, by rfl⟩ : syracuseStep 812435 = 1218653) B1218653
theorem B542099 : Blo 539803 542099 := bstep (se 1 (by rfl) ⟨406574, by rfl⟩ : syracuseStep 542099 = 813149) B813149
theorem B1369507 : Blo 539803 1369507 := bstep (se 1 (by rfl) ⟨1027130, by rfl⟩ : syracuseStep 1369507 = 2054261) B2054261
theorem B542115 : Blo 539803 542115 := bstep (se 1 (by rfl) ⟨406586, by rfl⟩ : syracuseStep 542115 = 813173) B813173
theorem B812465 : Blo 539803 812465 := bstep (se 2 (by rfl) ⟨304674, by rfl⟩ : syracuseStep 812465 = 609349) B609349
theorem B542131 : Blo 539803 542131 := bstep (se 1 (by rfl) ⟨406598, by rfl⟩ : syracuseStep 542131 = 813197) B813197
theorem B812483 : Blo 539803 812483 := bstep (se 1 (by rfl) ⟨609362, by rfl⟩ : syracuseStep 812483 = 1218725) B1218725
theorem B542147 : Blo 539803 542147 := bstep (se 1 (by rfl) ⟨406610, by rfl⟩ : syracuseStep 542147 = 813221) B813221
theorem B1541585 : Blo 539803 1541585 := bstep (se 2 (by rfl) ⟨578094, by rfl⟩ : syracuseStep 1541585 = 1156189) B1156189
theorem B542163 : Blo 539803 542163 := bstep (se 1 (by rfl) ⟨406622, by rfl⟩ : syracuseStep 542163 = 813245) B813245
theorem B812513 : Blo 539803 812513 := bstep (se 2 (by rfl) ⟨304692, by rfl⟩ : syracuseStep 812513 = 609385) B609385
theorem B878051 : Blo 539803 878051 := bstep (se 1 (by rfl) ⟨658538, by rfl⟩ : syracuseStep 878051 = 1317077) B1317077
theorem B542179 : Blo 539803 542179 := bstep (se 1 (by rfl) ⟨406634, by rfl⟩ : syracuseStep 542179 = 813269) B813269
theorem B812531 : Blo 539803 812531 := bstep (se 1 (by rfl) ⟨609398, by rfl⟩ : syracuseStep 812531 = 1218797) B1218797
theorem B542195 : Blo 539803 542195 := bstep (se 1 (by rfl) ⟨406646, by rfl⟩ : syracuseStep 542195 = 813293) B813293
theorem B607747 : Blo 539803 607747 := bstep (se 1 (by rfl) ⟨455810, by rfl⟩ : syracuseStep 607747 = 911621) B911621
theorem B542211 : Blo 539803 542211 := bstep (se 1 (by rfl) ⟨406658, by rfl⟩ : syracuseStep 542211 = 813317) B813317
theorem B812561 : Blo 539803 812561 := bstep (se 2 (by rfl) ⟨304710, by rfl⟩ : syracuseStep 812561 = 609421) B609421
theorem B771601 : Blo 539803 771601 := bstep (se 2 (by rfl) ⟨289350, by rfl⟩ : syracuseStep 771601 = 578701) B578701
theorem B542227 : Blo 539803 542227 := bstep (se 1 (by rfl) ⟨406670, by rfl⟩ : syracuseStep 542227 = 813341) B813341
theorem B812579 : Blo 539803 812579 := bstep (se 1 (by rfl) ⟨609434, by rfl⟩ : syracuseStep 812579 = 1218869) B1218869
theorem B542243 : Blo 539803 542243 := bstep (se 1 (by rfl) ⟨406682, by rfl⟩ : syracuseStep 542243 = 813365) B813365
theorem B1369649 : Blo 539803 1369649 := bstep (se 2 (by rfl) ⟨513618, by rfl⟩ : syracuseStep 1369649 = 1027237) B1027237
theorem B542259 : Blo 539803 542259 := bstep (se 1 (by rfl) ⟨406694, by rfl⟩ : syracuseStep 542259 = 813389) B813389
theorem B812609 : Blo 539803 812609 := bstep (se 2 (by rfl) ⟨304728, by rfl⟩ : syracuseStep 812609 = 609457) B609457
theorem B1541699 : Blo 539803 1541699 := bstep (se 1 (by rfl) ⟨1156274, by rfl⟩ : syracuseStep 1541699 = 2312549) B2312549
theorem B542275 : Blo 539803 542275 := bstep (se 1 (by rfl) ⟨406706, by rfl⟩ : syracuseStep 542275 = 813413) B813413
theorem B4113989 : Blo 539803 4113989 := bstep (se 4 (by rfl) ⟨385686, by rfl⟩ : syracuseStep 4113989 = 771373) B771373
theorem B812627 : Blo 539803 812627 := bstep (se 1 (by rfl) ⟨609470, by rfl⟩ : syracuseStep 812627 = 1218941) B1218941
theorem B542291 : Blo 539803 542291 := bstep (se 1 (by rfl) ⟨406718, by rfl⟩ : syracuseStep 542291 = 813437) B813437
theorem B1025635 : Blo 539803 1025635 := bstep (se 1 (by rfl) ⟨769226, by rfl⟩ : syracuseStep 1025635 = 1538453) B1538453
theorem B542307 : Blo 539803 542307 := bstep (se 1 (by rfl) ⟨406730, by rfl⟩ : syracuseStep 542307 = 813461) B813461
theorem B812657 : Blo 539803 812657 := bstep (se 2 (by rfl) ⟨304746, by rfl⟩ : syracuseStep 812657 = 609493) B609493
theorem B542323 : Blo 539803 542323 := bstep (se 1 (by rfl) ⟨406742, by rfl⟩ : syracuseStep 542323 = 813485) B813485
theorem B812675 : Blo 539803 812675 := bstep (se 1 (by rfl) ⟨609506, by rfl⟩ : syracuseStep 812675 = 1219013) B1219013
theorem B771715 : Blo 539803 771715 := bstep (se 1 (by rfl) ⟨578786, by rfl⟩ : syracuseStep 771715 = 1157573) B1157573
theorem B542339 : Blo 539803 542339 := bstep (se 1 (by rfl) ⟨406754, by rfl⟩ : syracuseStep 542339 = 813509) B813509
theorem B1828493 : Blo 539803 1828493 := bstep (se 3 (by rfl) ⟨342842, by rfl⟩ : syracuseStep 1828493 = 685685) B685685
theorem B910993 : Blo 539803 910993 := bstep (se 2 (by rfl) ⟨341622, by rfl⟩ : syracuseStep 910993 = 683245) B683245
theorem B607891 : Blo 539803 607891 := bstep (se 1 (by rfl) ⟨455918, by rfl⟩ : syracuseStep 607891 = 911837) B911837
theorem B542355 : Blo 539803 542355 := bstep (se 1 (by rfl) ⟨406766, by rfl⟩ : syracuseStep 542355 = 813533) B813533
theorem B812705 : Blo 539803 812705 := bstep (se 2 (by rfl) ⟨304764, by rfl⟩ : syracuseStep 812705 = 609529) B609529
theorem B542371 : Blo 539803 542371 := bstep (se 1 (by rfl) ⟨406778, by rfl⟩ : syracuseStep 542371 = 813557) B813557
theorem B911027 : Blo 539803 911027 := bstep (se 1 (by rfl) ⟨683270, by rfl⟩ : syracuseStep 911027 = 1366541) B1366541
theorem B812723 : Blo 539803 812723 := bstep (se 1 (by rfl) ⟨609542, by rfl⟩ : syracuseStep 812723 = 1219085) B1219085
theorem B542387 : Blo 539803 542387 := bstep (se 1 (by rfl) ⟨406790, by rfl⟩ : syracuseStep 542387 = 813581) B813581
theorem B730819 : Blo 539803 730819 := bstep (se 1 (by rfl) ⟨548114, by rfl⟩ : syracuseStep 730819 = 1096229) B1096229
theorem B1828547 : Blo 539803 1828547 := bstep (se 1 (by rfl) ⟨1371410, by rfl⟩ : syracuseStep 1828547 = 2742821) B2742821
theorem B4622021 : Blo 539803 4622021 := bstep (se 4 (by rfl) ⟨433314, by rfl⟩ : syracuseStep 4622021 = 866629) B866629
theorem B542403 : Blo 539803 542403 := bstep (se 1 (by rfl) ⟨406802, by rfl⟩ : syracuseStep 542403 = 813605) B813605
theorem B812753 : Blo 539803 812753 := bstep (se 2 (by rfl) ⟨304782, by rfl⟩ : syracuseStep 812753 = 609565) B609565
theorem B2746061 : Blo 539803 2746061 := bstep (se 3 (by rfl) ⟨514886, by rfl⟩ : syracuseStep 2746061 = 1029773) B1029773
theorem B542419 : Blo 539803 542419 := bstep (se 1 (by rfl) ⟨406814, by rfl⟩ : syracuseStep 542419 = 813629) B813629
theorem B812771 : Blo 539803 812771 := bstep (se 1 (by rfl) ⟨609578, by rfl⟩ : syracuseStep 812771 = 1219157) B1219157
theorem B542435 : Blo 539803 542435 := bstep (se 1 (by rfl) ⟨406826, by rfl⟩ : syracuseStep 542435 = 813653) B813653
theorem B542451 : Blo 539803 542451 := bstep (se 1 (by rfl) ⟨406838, by rfl⟩ : syracuseStep 542451 = 813677) B813677
theorem B812801 : Blo 539803 812801 := bstep (se 2 (by rfl) ⟨304800, by rfl⟩ : syracuseStep 812801 = 609601) B609601
theorem B542467 : Blo 539803 542467 := bstep (se 1 (by rfl) ⟨406850, by rfl⟩ : syracuseStep 542467 = 813701) B813701
theorem B2189069 : Blo 539803 2189069 := bstep (se 3 (by rfl) ⟨410450, by rfl⟩ : syracuseStep 2189069 = 820901) B820901
theorem B812819 : Blo 539803 812819 := bstep (se 1 (by rfl) ⟨609614, by rfl⟩ : syracuseStep 812819 = 1219229) B1219229
theorem B542483 : Blo 539803 542483 := bstep (se 1 (by rfl) ⟨406862, by rfl⟩ : syracuseStep 542483 = 813725) B813725
theorem B608035 : Blo 539803 608035 := bstep (se 1 (by rfl) ⟨456026, by rfl⟩ : syracuseStep 608035 = 912053) B912053
theorem B542499 : Blo 539803 542499 := bstep (se 1 (by rfl) ⟨406874, by rfl⟩ : syracuseStep 542499 = 813749) B813749
theorem B812849 : Blo 539803 812849 := bstep (se 2 (by rfl) ⟨304818, by rfl⟩ : syracuseStep 812849 = 609637) B609637
theorem B911155 : Blo 539803 911155 := bstep (se 1 (by rfl) ⟨683366, by rfl⟩ : syracuseStep 911155 = 1366733) B1366733
theorem B542515 : Blo 539803 542515 := bstep (se 1 (by rfl) ⟨406886, by rfl⟩ : syracuseStep 542515 = 813773) B813773
theorem B812867 : Blo 539803 812867 := bstep (se 1 (by rfl) ⟨609650, by rfl⟩ : syracuseStep 812867 = 1219301) B1219301
theorem B542531 : Blo 539803 542531 := bstep (se 1 (by rfl) ⟨406898, by rfl⟩ : syracuseStep 542531 = 813797) B813797
theorem B542547 : Blo 539803 542547 := bstep (se 1 (by rfl) ⟨406910, by rfl⟩ : syracuseStep 542547 = 813821) B813821
theorem B812897 : Blo 539803 812897 := bstep (se 2 (by rfl) ⟨304836, by rfl⟩ : syracuseStep 812897 = 609673) B609673
theorem B542563 : Blo 539803 542563 := bstep (se 1 (by rfl) ⟨406922, by rfl⟩ : syracuseStep 542563 = 813845) B813845
theorem B1730413 : Blo 539803 1730413 := bstep (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) B648905
theorem B812915 : Blo 539803 812915 := bstep (se 1 (by rfl) ⟨609686, by rfl⟩ : syracuseStep 812915 = 1219373) B1219373
theorem B542579 : Blo 539803 542579 := bstep (se 1 (by rfl) ⟨406934, by rfl⟩ : syracuseStep 542579 = 813869) B813869
theorem B542595 : Blo 539803 542595 := bstep (se 1 (by rfl) ⟨406946, by rfl⟩ : syracuseStep 542595 = 813893) B813893
theorem B812945 : Blo 539803 812945 := bstep (se 2 (by rfl) ⟨304854, by rfl⟩ : syracuseStep 812945 = 609709) B609709
theorem B542611 : Blo 539803 542611 := bstep (se 1 (by rfl) ⟨406958, by rfl⟩ : syracuseStep 542611 = 813917) B813917
theorem B812963 : Blo 539803 812963 := bstep (se 1 (by rfl) ⟨609722, by rfl⟩ : syracuseStep 812963 = 1219445) B1219445
theorem B542627 : Blo 539803 542627 := bstep (se 1 (by rfl) ⟨406970, by rfl⟩ : syracuseStep 542627 = 813941) B813941
theorem B608179 : Blo 539803 608179 := bstep (se 1 (by rfl) ⟨456134, by rfl⟩ : syracuseStep 608179 = 912269) B912269
theorem B542643 : Blo 539803 542643 := bstep (se 1 (by rfl) ⟨406982, by rfl⟩ : syracuseStep 542643 = 813965) B813965
theorem B911297 : Blo 539803 911297 := bstep (se 2 (by rfl) ⟨341736, by rfl⟩ : syracuseStep 911297 = 683473) B683473
theorem B812993 : Blo 539803 812993 := bstep (se 2 (by rfl) ⟨304872, by rfl⟩ : syracuseStep 812993 = 609745) B609745
theorem B542659 : Blo 539803 542659 := bstep (se 1 (by rfl) ⟨406994, by rfl⟩ : syracuseStep 542659 = 813989) B813989
theorem B11241413 : Blo 539803 11241413 := bstep (se 4 (by rfl) ⟨1053882, by rfl⟩ : syracuseStep 11241413 = 2107765) B2107765
theorem B1828817 : Blo 539803 1828817 := bstep (se 2 (by rfl) ⟨685806, by rfl⟩ : syracuseStep 1828817 = 1371613) B1371613
theorem B813011 : Blo 539803 813011 := bstep (se 1 (by rfl) ⟨609758, by rfl⟩ : syracuseStep 813011 = 1219517) B1219517
theorem B542675 : Blo 539803 542675 := bstep (se 1 (by rfl) ⟨407006, by rfl⟩ : syracuseStep 542675 = 814013) B814013
theorem B2639843 : Blo 539803 2639843 := bstep (se 1 (by rfl) ⟨1979882, by rfl⟩ : syracuseStep 2639843 = 3959765) B3959765
theorem B542691 : Blo 539803 542691 := bstep (se 1 (by rfl) ⟨407018, by rfl⟩ : syracuseStep 542691 = 814037) B814037
theorem B813041 : Blo 539803 813041 := bstep (se 2 (by rfl) ⟨304890, by rfl⟩ : syracuseStep 813041 = 609781) B609781
theorem B542707 : Blo 539803 542707 := bstep (se 1 (by rfl) ⟨407030, by rfl⟩ : syracuseStep 542707 = 814061) B814061
theorem B813059 : Blo 539803 813059 := bstep (se 1 (by rfl) ⟨609794, by rfl⟩ : syracuseStep 813059 = 1219589) B1219589
theorem B542723 : Blo 539803 542723 := bstep (se 1 (by rfl) ⟨407042, by rfl⟩ : syracuseStep 542723 = 814085) B814085
theorem B542739 : Blo 539803 542739 := bstep (se 1 (by rfl) ⟨407054, by rfl⟩ : syracuseStep 542739 = 814109) B814109
theorem B813089 : Blo 539803 813089 := bstep (se 2 (by rfl) ⟨304908, by rfl⟩ : syracuseStep 813089 = 609817) B609817
theorem B1026083 : Blo 539803 1026083 := bstep (se 1 (by rfl) ⟨769562, by rfl⟩ : syracuseStep 1026083 = 1539125) B1539125
theorem B542755 : Blo 539803 542755 := bstep (se 1 (by rfl) ⟨407066, by rfl⟩ : syracuseStep 542755 = 814133) B814133
theorem B813107 : Blo 539803 813107 := bstep (se 1 (by rfl) ⟨609830, by rfl⟩ : syracuseStep 813107 = 1219661) B1219661
theorem B542771 : Blo 539803 542771 := bstep (se 1 (by rfl) ⟨407078, by rfl⟩ : syracuseStep 542771 = 814157) B814157
theorem B911425 : Blo 539803 911425 := bstep (se 2 (by rfl) ⟨341784, by rfl⟩ : syracuseStep 911425 = 683569) B683569
theorem B608323 : Blo 539803 608323 := bstep (se 1 (by rfl) ⟨456242, by rfl⟩ : syracuseStep 608323 = 912485) B912485
theorem B1484867 : Blo 539803 1484867 := bstep (se 1 (by rfl) ⟨1113650, by rfl⟩ : syracuseStep 1484867 = 2227301) B2227301
theorem B542787 : Blo 539803 542787 := bstep (se 1 (by rfl) ⟨407090, by rfl⟩ : syracuseStep 542787 = 814181) B814181
theorem B2058317 : Blo 539803 2058317 := bstep (se 3 (by rfl) ⟨385934, by rfl⟩ : syracuseStep 2058317 = 771869) B771869
theorem B813137 : Blo 539803 813137 := bstep (se 2 (by rfl) ⟨304926, by rfl⟩ : syracuseStep 813137 = 609853) B609853
theorem B1648721 : Blo 539803 1648721 := bstep (se 2 (by rfl) ⟨618270, by rfl⟩ : syracuseStep 1648721 = 1236541) B1236541
theorem B542803 : Blo 539803 542803 := bstep (se 1 (by rfl) ⟨407102, by rfl⟩ : syracuseStep 542803 = 814205) B814205
theorem B911459 : Blo 539803 911459 := bstep (se 1 (by rfl) ⟨683594, by rfl⟩ : syracuseStep 911459 = 1367189) B1367189
theorem B813155 : Blo 539803 813155 := bstep (se 1 (by rfl) ⟨609866, by rfl⟩ : syracuseStep 813155 = 1219733) B1219733
theorem B1755245 : Blo 539803 1755245 := bstep (se 3 (by rfl) ⟨329108, by rfl⟩ : syracuseStep 1755245 = 658217) B658217
theorem B813185 : Blo 539803 813185 := bstep (se 2 (by rfl) ⟨304944, by rfl⟩ : syracuseStep 813185 = 609889) B609889
theorem B3082373 : Blo 539803 3082373 := bstep (se 4 (by rfl) ⟨288972, by rfl⟩ : syracuseStep 3082373 = 577945) B577945
theorem B813203 : Blo 539803 813203 := bstep (se 1 (by rfl) ⟨609902, by rfl⟩ : syracuseStep 813203 = 1219805) B1219805
theorem B3090595 : Blo 539803 3090595 := bstep (se 1 (by rfl) ⟨2317946, by rfl⟩ : syracuseStep 3090595 = 4635893) B4635893
theorem B813233 : Blo 539803 813233 := bstep (se 2 (by rfl) ⟨304962, by rfl⟩ : syracuseStep 813233 = 609925) B609925
theorem B813251 : Blo 539803 813251 := bstep (se 1 (by rfl) ⟨609938, by rfl⟩ : syracuseStep 813251 = 1219877) B1219877
theorem B608467 : Blo 539803 608467 := bstep (se 1 (by rfl) ⟨456350, by rfl⟩ : syracuseStep 608467 = 912701) B912701
theorem B26699989 : Blo 539803 26699989 := bstep (se 7 (by rfl) ⟨312890, by rfl⟩ : syracuseStep 26699989 = 625781) B625781
theorem B813281 : Blo 539803 813281 := bstep (se 2 (by rfl) ⟨304980, by rfl⟩ : syracuseStep 813281 = 609961) B609961
theorem B911587 : Blo 539803 911587 := bstep (se 1 (by rfl) ⟨683690, by rfl⟩ : syracuseStep 911587 = 1367381) B1367381
theorem B4442339 : Blo 539803 4442339 := bstep (se 1 (by rfl) ⟨3331754, by rfl⟩ : syracuseStep 4442339 = 6663509) B6663509
theorem B616675 : Blo 539803 616675 := bstep (se 1 (by rfl) ⟨462506, by rfl⟩ : syracuseStep 616675 = 925013) B925013
theorem B4761827 : Blo 539803 4761827 := bstep (se 1 (by rfl) ⟨3571370, by rfl⟩ : syracuseStep 4761827 = 7142741) B7142741
theorem B4630769 : Blo 539803 4630769 := bstep (se 2 (by rfl) ⟨1736538, by rfl⟩ : syracuseStep 4630769 = 3473077) B3473077
theorem B813299 : Blo 539803 813299 := bstep (se 1 (by rfl) ⟨609974, by rfl⟩ : syracuseStep 813299 = 1219949) B1219949
theorem B813329 : Blo 539803 813329 := bstep (se 2 (by rfl) ⟨304998, by rfl⟩ : syracuseStep 813329 = 609997) B609997
theorem B813347 : Blo 539803 813347 := bstep (se 1 (by rfl) ⟨610010, by rfl⟩ : syracuseStep 813347 = 1220021) B1220021
theorem B813377 : Blo 539803 813377 := bstep (se 2 (by rfl) ⟨305016, by rfl⟩ : syracuseStep 813377 = 610033) B610033
theorem B1026371 : Blo 539803 1026371 := bstep (se 1 (by rfl) ⟨769778, by rfl⟩ : syracuseStep 1026371 = 1539557) B1539557
theorem B1214801 : Blo 539803 1214801 := bstep (se 2 (by rfl) ⟨455550, by rfl⟩ : syracuseStep 1214801 = 911101) B911101
theorem B821587 : Blo 539803 821587 := bstep (se 1 (by rfl) ⟨616190, by rfl⟩ : syracuseStep 821587 = 1232381) B1232381
theorem B813395 : Blo 539803 813395 := bstep (se 1 (by rfl) ⟨610046, by rfl⟩ : syracuseStep 813395 = 1220093) B1220093
theorem B731489 : Blo 539803 731489 := bstep (se 2 (by rfl) ⟨274308, by rfl⟩ : syracuseStep 731489 = 548617) B548617
theorem B1214819 : Blo 539803 1214819 := bstep (se 1 (by rfl) ⟨911114, by rfl⟩ : syracuseStep 1214819 = 1822229) B1822229
theorem B608611 : Blo 539803 608611 := bstep (se 1 (by rfl) ⟨456458, by rfl⟩ : syracuseStep 608611 = 912917) B912917
theorem B911729 : Blo 539803 911729 := bstep (se 2 (by rfl) ⟨341898, by rfl⟩ : syracuseStep 911729 = 683797) B683797
theorem B813425 : Blo 539803 813425 := bstep (se 2 (by rfl) ⟨305034, by rfl⟩ : syracuseStep 813425 = 610069) B610069
theorem B813443 : Blo 539803 813443 := bstep (se 1 (by rfl) ⟨610082, by rfl⟩ : syracuseStep 813443 = 1220165) B1220165
theorem B3459469 : Blo 539803 3459469 := bstep (se 3 (by rfl) ⟨648650, by rfl⟩ : syracuseStep 3459469 = 1297301) B1297301
theorem B4065677 : Blo 539803 4065677 := bstep (se 3 (by rfl) ⟨762314, by rfl⟩ : syracuseStep 4065677 = 1524629) B1524629
theorem B813473 : Blo 539803 813473 := bstep (se 2 (by rfl) ⟨305052, by rfl⟩ : syracuseStep 813473 = 610105) B610105
theorem B2738609 : Blo 539803 2738609 := bstep (se 2 (by rfl) ⟨1026978, by rfl⟩ : syracuseStep 2738609 = 2053957) B2053957
theorem B813491 : Blo 539803 813491 := bstep (se 1 (by rfl) ⟨610118, by rfl⟩ : syracuseStep 813491 = 1220237) B1220237
theorem B5212613 : Blo 539803 5212613 := bstep (se 4 (by rfl) ⟨488682, by rfl⟩ : syracuseStep 5212613 = 977365) B977365
theorem B813521 : Blo 539803 813521 := bstep (se 2 (by rfl) ⟨305070, by rfl⟩ : syracuseStep 813521 = 610141) B610141
theorem B813539 : Blo 539803 813539 := bstep (se 1 (by rfl) ⟨610154, by rfl⟩ : syracuseStep 813539 = 1220309) B1220309
theorem B1829357 : Blo 539803 1829357 := bstep (se 3 (by rfl) ⟨343004, by rfl⟩ : syracuseStep 1829357 = 686009) B686009
theorem B911857 : Blo 539803 911857 := bstep (se 2 (by rfl) ⟨341946, by rfl⟩ : syracuseStep 911857 = 683893) B683893
theorem B608755 : Blo 539803 608755 := bstep (se 1 (by rfl) ⟨456566, by rfl⟩ : syracuseStep 608755 = 913133) B913133
theorem B731635 : Blo 539803 731635 := bstep (se 1 (by rfl) ⟨548726, by rfl⟩ : syracuseStep 731635 = 1097453) B1097453
theorem B813569 : Blo 539803 813569 := bstep (se 2 (by rfl) ⟨305088, by rfl⟩ : syracuseStep 813569 = 610177) B610177
theorem B2509325 : Blo 539803 2509325 := bstep (se 3 (by rfl) ⟨470498, by rfl⟩ : syracuseStep 2509325 = 940997) B940997
theorem B1370641 : Blo 539803 1370641 := bstep (se 2 (by rfl) ⟨513990, by rfl⟩ : syracuseStep 1370641 = 1027981) B1027981
theorem B911891 : Blo 539803 911891 := bstep (se 1 (by rfl) ⟨683918, by rfl⟩ : syracuseStep 911891 = 1367837) B1367837
theorem B813587 : Blo 539803 813587 := bstep (se 1 (by rfl) ⟨610190, by rfl⟩ : syracuseStep 813587 = 1220381) B1220381
theorem B1878563 : Blo 539803 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B1829411 : Blo 539803 1829411 := bstep (se 1 (by rfl) ⟨1372058, by rfl⟩ : syracuseStep 1829411 = 2744117) B2744117
theorem B1542701 : Blo 539803 1542701 := bstep (se 3 (by rfl) ⟨289256, by rfl⟩ : syracuseStep 1542701 = 578513) B578513
theorem B813617 : Blo 539803 813617 := bstep (se 2 (by rfl) ⟨305106, by rfl⟩ : syracuseStep 813617 = 610213) B610213
theorem B813635 : Blo 539803 813635 := bstep (se 1 (by rfl) ⟨610226, by rfl⟩ : syracuseStep 813635 = 1220453) B1220453
theorem B813665 : Blo 539803 813665 := bstep (se 2 (by rfl) ⟨305124, by rfl⟩ : syracuseStep 813665 = 610249) B610249
theorem B2599523 : Blo 539803 2599523 := bstep (se 1 (by rfl) ⟨1949642, by rfl⟩ : syracuseStep 2599523 = 3899285) B3899285
theorem B1215089 : Blo 539803 1215089 := bstep (se 2 (by rfl) ⟨455658, by rfl⟩ : syracuseStep 1215089 = 911317) B911317
theorem B813683 : Blo 539803 813683 := bstep (se 1 (by rfl) ⟨610262, by rfl⟩ : syracuseStep 813683 = 1220525) B1220525
theorem B1215107 : Blo 539803 1215107 := bstep (se 1 (by rfl) ⟨911330, by rfl⟩ : syracuseStep 1215107 = 1822661) B1822661
theorem B608899 : Blo 539803 608899 := bstep (se 1 (by rfl) ⟨456674, by rfl⟩ : syracuseStep 608899 = 913349) B913349
theorem B813713 : Blo 539803 813713 := bstep (se 2 (by rfl) ⟨305142, by rfl⟩ : syracuseStep 813713 = 610285) B610285
theorem B912019 : Blo 539803 912019 := bstep (se 1 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 912019 = 1368029) B1368029
theorem B813731 : Blo 539803 813731 := bstep (se 1 (by rfl) ⟨610298, by rfl⟩ : syracuseStep 813731 = 1220597) B1220597
theorem B3091121 : Blo 539803 3091121 := bstep (se 2 (by rfl) ⟨1159170, by rfl⟩ : syracuseStep 3091121 = 2318341) B2318341
theorem B813761 : Blo 539803 813761 := bstep (se 2 (by rfl) ⟨305160, by rfl⟩ : syracuseStep 813761 = 610321) B610321
theorem B731857 : Blo 539803 731857 := bstep (se 2 (by rfl) ⟨274446, by rfl⟩ : syracuseStep 731857 = 548893) B548893
theorem B813779 : Blo 539803 813779 := bstep (se 1 (by rfl) ⟨610334, by rfl⟩ : syracuseStep 813779 = 1220669) B1220669
theorem B1542883 : Blo 539803 1542883 := bstep (se 1 (by rfl) ⟨1157162, by rfl⟩ : syracuseStep 1542883 = 2314325) B2314325
theorem B813809 : Blo 539803 813809 := bstep (se 2 (by rfl) ⟨305178, by rfl⟩ : syracuseStep 813809 = 610357) B610357
theorem B813827 : Blo 539803 813827 := bstep (se 1 (by rfl) ⟨610370, by rfl⟩ : syracuseStep 813827 = 1220741) B1220741
theorem B2050829 : Blo 539803 2050829 := bstep (se 3 (by rfl) ⟨384530, by rfl⟩ : syracuseStep 2050829 = 769061) B769061
theorem B609043 : Blo 539803 609043 := bstep (se 1 (by rfl) ⟨456782, by rfl⟩ : syracuseStep 609043 = 913565) B913565
theorem B912161 : Blo 539803 912161 := bstep (se 2 (by rfl) ⟨342060, by rfl⟩ : syracuseStep 912161 = 684121) B684121
theorem B813857 : Blo 539803 813857 := bstep (se 2 (by rfl) ⟨305196, by rfl⟩ : syracuseStep 813857 = 610393) B610393
theorem B1370915 : Blo 539803 1370915 := bstep (se 1 (by rfl) ⟨1028186, by rfl⟩ : syracuseStep 1370915 = 2056373) B2056373
theorem B1829681 : Blo 539803 1829681 := bstep (se 2 (by rfl) ⟨686130, by rfl⟩ : syracuseStep 1829681 = 1372261) B1372261
theorem B650035 : Blo 539803 650035 := bstep (se 1 (by rfl) ⟨487526, by rfl⟩ : syracuseStep 650035 = 975053) B975053
theorem B813875 : Blo 539803 813875 := bstep (se 1 (by rfl) ⟨610406, by rfl⟩ : syracuseStep 813875 = 1220813) B1220813
theorem B813905 : Blo 539803 813905 := bstep (se 2 (by rfl) ⟨305214, by rfl⟩ : syracuseStep 813905 = 610429) B610429
theorem B813923 : Blo 539803 813923 := bstep (se 1 (by rfl) ⟨610442, by rfl⟩ : syracuseStep 813923 = 1220885) B1220885
theorem B2059121 : Blo 539803 2059121 := bstep (se 2 (by rfl) ⟨772170, by rfl⟩ : syracuseStep 2059121 = 1544341) B1544341
theorem B813953 : Blo 539803 813953 := bstep (se 2 (by rfl) ⟨305232, by rfl⟩ : syracuseStep 813953 = 610465) B610465
theorem B1543043 : Blo 539803 1543043 := bstep (se 1 (by rfl) ⟨1157282, by rfl⟩ : syracuseStep 1543043 = 2314565) B2314565
theorem B1215377 : Blo 539803 1215377 := bstep (se 2 (by rfl) ⟨455766, by rfl⟩ : syracuseStep 1215377 = 911533) B911533
theorem B813971 : Blo 539803 813971 := bstep (se 1 (by rfl) ⟨610478, by rfl⟩ : syracuseStep 813971 = 1220957) B1220957
theorem B912289 : Blo 539803 912289 := bstep (se 2 (by rfl) ⟨342108, by rfl⟩ : syracuseStep 912289 = 684217) B684217
theorem B1215395 : Blo 539803 1215395 := bstep (se 1 (by rfl) ⟨911546, by rfl⟩ : syracuseStep 1215395 = 1823093) B1823093
theorem B609187 : Blo 539803 609187 := bstep (se 1 (by rfl) ⟨456890, by rfl⟩ : syracuseStep 609187 = 913781) B913781
theorem B977827 : Blo 539803 977827 := bstep (se 1 (by rfl) ⟨733370, by rfl⟩ : syracuseStep 977827 = 1466741) B1466741
theorem B814001 : Blo 539803 814001 := bstep (se 2 (by rfl) ⟨305250, by rfl⟩ : syracuseStep 814001 = 610501) B610501
theorem B912323 : Blo 539803 912323 := bstep (se 1 (by rfl) ⟨684242, by rfl⟩ : syracuseStep 912323 = 1368485) B1368485
theorem B814019 : Blo 539803 814019 := bstep (se 1 (by rfl) ⟨610514, by rfl⟩ : syracuseStep 814019 = 1221029) B1221029
theorem B814049 : Blo 539803 814049 := bstep (se 2 (by rfl) ⟨305268, by rfl⟩ : syracuseStep 814049 = 610537) B610537
theorem B1371107 : Blo 539803 1371107 := bstep (se 1 (by rfl) ⟨1028330, by rfl⟩ : syracuseStep 1371107 = 2056661) B2056661
theorem B814067 : Blo 539803 814067 := bstep (se 1 (by rfl) ⟨610550, by rfl⟩ : syracuseStep 814067 = 1221101) B1221101
theorem B814097 : Blo 539803 814097 := bstep (se 2 (by rfl) ⟨305286, by rfl⟩ : syracuseStep 814097 = 610573) B610573
theorem B814115 : Blo 539803 814115 := bstep (se 1 (by rfl) ⟨610586, by rfl⟩ : syracuseStep 814115 = 1221173) B1221173
theorem B609331 : Blo 539803 609331 := bstep (se 1 (by rfl) ⟨456998, by rfl⟩ : syracuseStep 609331 = 913997) B913997
theorem B814145 : Blo 539803 814145 := bstep (se 2 (by rfl) ⟨305304, by rfl⟩ : syracuseStep 814145 = 610609) B610609
theorem B912451 : Blo 539803 912451 := bstep (se 1 (by rfl) ⟨684338, by rfl⟩ : syracuseStep 912451 = 1368677) B1368677
theorem B2337869 : Blo 539803 2337869 := bstep (se 3 (by rfl) ⟨438350, by rfl⟩ : syracuseStep 2337869 = 876701) B876701
theorem B732241 : Blo 539803 732241 := bstep (se 2 (by rfl) ⟨274590, by rfl⟩ : syracuseStep 732241 = 549181) B549181
theorem B814163 : Blo 539803 814163 := bstep (se 1 (by rfl) ⟨610622, by rfl⟩ : syracuseStep 814163 = 1221245) B1221245
theorem B2346097 : Blo 539803 2346097 := bstep (se 2 (by rfl) ⟨879786, by rfl⟩ : syracuseStep 2346097 = 1759573) B1759573
theorem B814193 : Blo 539803 814193 := bstep (se 2 (by rfl) ⟨305322, by rfl⟩ : syracuseStep 814193 = 610645) B610645
theorem B732289 : Blo 539803 732289 := bstep (se 2 (by rfl) ⟨274608, by rfl⟩ : syracuseStep 732289 = 549217) B549217
theorem B1215665 : Blo 539803 1215665 := bstep (se 2 (by rfl) ⟨455874, by rfl⟩ : syracuseStep 1215665 = 911749) B911749
theorem B1215683 : Blo 539803 1215683 := bstep (se 1 (by rfl) ⟨911762, by rfl⟩ : syracuseStep 1215683 = 1823525) B1823525
theorem B609475 : Blo 539803 609475 := bstep (se 1 (by rfl) ⟨457106, by rfl⟩ : syracuseStep 609475 = 914213) B914213
theorem B1821905 : Blo 539803 1821905 := bstep (se 2 (by rfl) ⟨683214, by rfl⟩ : syracuseStep 1821905 = 1366429) B1366429
theorem B912593 : Blo 539803 912593 := bstep (se 2 (by rfl) ⟨342222, by rfl⟩ : syracuseStep 912593 = 684445) B684445
theorem B1027313 : Blo 539803 1027313 := bstep (se 2 (by rfl) ⟨385242, by rfl⟩ : syracuseStep 1027313 = 770485) B770485
theorem B1109297 : Blo 539803 1109297 := bstep (se 2 (by rfl) ⟨415986, by rfl⟩ : syracuseStep 1109297 = 831973) B831973
theorem B1830221 : Blo 539803 1830221 := bstep (se 3 (by rfl) ⟨343166, by rfl⟩ : syracuseStep 1830221 = 686333) B686333
theorem B912721 : Blo 539803 912721 := bstep (se 2 (by rfl) ⟨342270, by rfl⟩ : syracuseStep 912721 = 684541) B684541
theorem B609619 : Blo 539803 609619 := bstep (se 1 (by rfl) ⟨457214, by rfl⟩ : syracuseStep 609619 = 914429) B914429
theorem B912755 : Blo 539803 912755 := bstep (se 1 (by rfl) ⟨684566, by rfl⟩ : syracuseStep 912755 = 1369133) B1369133
theorem B1830275 : Blo 539803 1830275 := bstep (se 1 (by rfl) ⟨1372706, by rfl⟩ : syracuseStep 1830275 = 2745413) B2745413
theorem B822707 : Blo 539803 822707 := bstep (se 1 (by rfl) ⟨617030, by rfl⟩ : syracuseStep 822707 = 1234061) B1234061
theorem B1215953 : Blo 539803 1215953 := bstep (se 2 (by rfl) ⟨455982, by rfl⟩ : syracuseStep 1215953 = 911965) B911965
theorem B1215971 : Blo 539803 1215971 := bstep (se 1 (by rfl) ⟨911978, by rfl⟩ : syracuseStep 1215971 = 1823957) B1823957
theorem B609763 : Blo 539803 609763 := bstep (se 1 (by rfl) ⟨457322, by rfl⟩ : syracuseStep 609763 = 914645) B914645
theorem B912883 : Blo 539803 912883 := bstep (se 1 (by rfl) ⟨684662, by rfl⟩ : syracuseStep 912883 = 1369325) B1369325
theorem B2059789 : Blo 539803 2059789 := bstep (se 3 (by rfl) ⟨386210, by rfl⟩ : syracuseStep 2059789 = 772421) B772421
theorem B1846819 : Blo 539803 1846819 := bstep (se 1 (by rfl) ⟨1385114, by rfl⟩ : syracuseStep 1846819 = 2770229) B2770229
theorem B577091 : Blo 539803 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B1732195 : Blo 539803 1732195 := bstep (se 1 (by rfl) ⟨1299146, by rfl⟩ : syracuseStep 1732195 = 2598293) B2598293
theorem B4689521 : Blo 539803 4689521 := bstep (se 2 (by rfl) ⟨1758570, by rfl⟩ : syracuseStep 4689521 = 3517141) B3517141
theorem B683635 : Blo 539803 683635 := bstep (se 1 (by rfl) ⟨512726, by rfl⟩ : syracuseStep 683635 = 1025453) B1025453
theorem B609907 : Blo 539803 609907 := bstep (se 1 (by rfl) ⟨457430, by rfl⟩ : syracuseStep 609907 = 914861) B914861
theorem B913025 : Blo 539803 913025 := bstep (se 2 (by rfl) ⟨342384, by rfl⟩ : syracuseStep 913025 = 684769) B684769
theorem B6934157 : Blo 539803 6934157 := bstep (se 3 (by rfl) ⟨1300154, by rfl⟩ : syracuseStep 6934157 = 2600309) B2600309
theorem B1830545 : Blo 539803 1830545 := bstep (se 2 (by rfl) ⟨686454, by rfl⟩ : syracuseStep 1830545 = 1372909) B1372909
theorem B1732259 : Blo 539803 1732259 := bstep (se 1 (by rfl) ⟨1299194, by rfl⟩ : syracuseStep 1732259 = 2598389) B2598389
theorem B3468977 : Blo 539803 3468977 := bstep (se 2 (by rfl) ⟨1300866, by rfl⟩ : syracuseStep 3468977 = 2601733) B2601733
theorem B683731 : Blo 539803 683731 := bstep (se 1 (by rfl) ⟨512798, by rfl⟩ : syracuseStep 683731 = 1025597) B1025597
theorem B3469027 : Blo 539803 3469027 := bstep (se 1 (by rfl) ⟨2601770, by rfl⟩ : syracuseStep 3469027 = 5203541) B5203541
theorem B1822445 : Blo 539803 1822445 := bstep (se 3 (by rfl) ⟨341708, by rfl⟩ : syracuseStep 1822445 = 683417) B683417
theorem B1216241 : Blo 539803 1216241 := bstep (se 2 (by rfl) ⟨456090, by rfl⟩ : syracuseStep 1216241 = 912181) B912181
theorem B1732337 : Blo 539803 1732337 := bstep (se 2 (by rfl) ⟨649626, by rfl⟩ : syracuseStep 1732337 = 1299253) B1299253
theorem B913153 : Blo 539803 913153 := bstep (se 2 (by rfl) ⟨342432, by rfl⟩ : syracuseStep 913153 = 684865) B684865
theorem B1216259 : Blo 539803 1216259 := bstep (se 1 (by rfl) ⟨912194, by rfl⟩ : syracuseStep 1216259 = 1824389) B1824389
theorem B610051 : Blo 539803 610051 := bstep (se 1 (by rfl) ⟨457538, by rfl⟩ : syracuseStep 610051 = 915077) B915077
theorem B4935437 : Blo 539803 4935437 := bstep (se 3 (by rfl) ⟨925394, by rfl⟩ : syracuseStep 4935437 = 1850789) B1850789
theorem B1822499 : Blo 539803 1822499 := bstep (se 1 (by rfl) ⟨1366874, by rfl⟩ : syracuseStep 1822499 = 2733749) B2733749
theorem B913187 : Blo 539803 913187 := bstep (se 1 (by rfl) ⟨684890, by rfl⟩ : syracuseStep 913187 = 1369781) B1369781
theorem B2740067 : Blo 539803 2740067 := bstep (se 1 (by rfl) ⟨2055050, by rfl⟩ : syracuseStep 2740067 = 4110101) B4110101
theorem B2920333 : Blo 539803 2920333 := bstep (se 3 (by rfl) ⟨547562, by rfl⟩ : syracuseStep 2920333 = 1095125) B1095125
theorem B1372049 : Blo 539803 1372049 := bstep (se 2 (by rfl) ⟨514518, by rfl⟩ : syracuseStep 1372049 = 1029037) B1029037
theorem B610195 : Blo 539803 610195 := bstep (se 1 (by rfl) ⟨457646, by rfl⟩ : syracuseStep 610195 = 915293) B915293
theorem B913315 : Blo 539803 913315 := bstep (se 1 (by rfl) ⟨684986, by rfl⟩ : syracuseStep 913315 = 1369973) B1369973
theorem B1544113 : Blo 539803 1544113 := bstep (se 2 (by rfl) ⟨579042, by rfl⟩ : syracuseStep 1544113 = 1158085) B1158085
theorem B1372099 : Blo 539803 1372099 := bstep (se 1 (by rfl) ⟨1029074, by rfl⟩ : syracuseStep 1372099 = 2058149) B2058149
theorem B1216529 : Blo 539803 1216529 := bstep (se 2 (by rfl) ⟨456198, by rfl⟩ : syracuseStep 1216529 = 912397) B912397
theorem B1216547 : Blo 539803 1216547 := bstep (se 1 (by rfl) ⟨912410, by rfl⟩ : syracuseStep 1216547 = 1824821) B1824821
theorem B610339 : Blo 539803 610339 := bstep (se 1 (by rfl) ⟨457754, by rfl⟩ : syracuseStep 610339 = 915509) B915509
theorem B1822769 : Blo 539803 1822769 := bstep (se 2 (by rfl) ⟨683538, by rfl⟩ : syracuseStep 1822769 = 1367077) B1367077
theorem B913457 : Blo 539803 913457 := bstep (se 2 (by rfl) ⟨342546, by rfl⟩ : syracuseStep 913457 = 685093) B685093
theorem B1372241 : Blo 539803 1372241 := bstep (se 2 (by rfl) ⟨514590, by rfl⟩ : syracuseStep 1372241 = 1029181) B1029181
theorem B1028209 : Blo 539803 1028209 := bstep (se 2 (by rfl) ⟨385578, by rfl⟩ : syracuseStep 1028209 = 771157) B771157
theorem B1831085 : Blo 539803 1831085 := bstep (se 3 (by rfl) ⟨343328, by rfl⟩ : syracuseStep 1831085 = 686657) B686657
theorem B913585 : Blo 539803 913585 := bstep (se 2 (by rfl) ⟨342594, by rfl⟩ : syracuseStep 913585 = 685189) B685189
theorem B610483 : Blo 539803 610483 := bstep (se 1 (by rfl) ⟨457862, by rfl⟩ : syracuseStep 610483 = 915725) B915725
theorem B684227 : Blo 539803 684227 := bstep (se 1 (by rfl) ⟨513170, by rfl⟩ : syracuseStep 684227 = 1026341) B1026341
theorem B2199757 : Blo 539803 2199757 := bstep (se 3 (by rfl) ⟨412454, by rfl⟩ : syracuseStep 2199757 = 824909) B824909
theorem B913619 : Blo 539803 913619 := bstep (se 1 (by rfl) ⟨685214, by rfl⟩ : syracuseStep 913619 = 1370429) B1370429
theorem B6918371 : Blo 539803 6918371 := bstep (se 1 (by rfl) ⟨5188778, by rfl⟩ : syracuseStep 6918371 = 10377557) B10377557
theorem B659683 : Blo 539803 659683 := bstep (se 1 (by rfl) ⟨494762, by rfl⟩ : syracuseStep 659683 = 989525) B989525
theorem B1855715 : Blo 539803 1855715 := bstep (se 1 (by rfl) ⟨1391786, by rfl⟩ : syracuseStep 1855715 = 2783573) B2783573
theorem B1831139 : Blo 539803 1831139 := bstep (se 1 (by rfl) ⟨1373354, by rfl⟩ : syracuseStep 1831139 = 2746709) B2746709
theorem B1028369 : Blo 539803 1028369 := bstep (se 2 (by rfl) ⟨385638, by rfl⟩ : syracuseStep 1028369 = 771277) B771277
theorem B1716515 : Blo 539803 1716515 := bstep (se 1 (by rfl) ⟨1287386, by rfl⟩ : syracuseStep 1716515 = 2574773) B2574773
theorem B880931 : Blo 539803 880931 := bstep (se 1 (by rfl) ⟨660698, by rfl⟩ : syracuseStep 880931 = 1321397) B1321397
theorem B2060579 : Blo 539803 2060579 := bstep (se 1 (by rfl) ⟨1545434, by rfl⟩ : syracuseStep 2060579 = 3090869) B3090869
theorem B1216817 : Blo 539803 1216817 := bstep (se 2 (by rfl) ⟨456306, by rfl⟩ : syracuseStep 1216817 = 912613) B912613
theorem B1954097 : Blo 539803 1954097 := bstep (se 2 (by rfl) ⟨732786, by rfl⟩ : syracuseStep 1954097 = 1465573) B1465573
theorem B1216835 : Blo 539803 1216835 := bstep (se 1 (by rfl) ⟨912626, by rfl⟩ : syracuseStep 1216835 = 1825253) B1825253
theorem B610627 : Blo 539803 610627 := bstep (se 1 (by rfl) ⟨457970, by rfl⟩ : syracuseStep 610627 = 915941) B915941
theorem B913747 : Blo 539803 913747 := bstep (se 1 (by rfl) ⟨685310, by rfl⟩ : syracuseStep 913747 = 1370621) B1370621
theorem B4108643 : Blo 539803 4108643 := bstep (se 1 (by rfl) ⟨3081482, by rfl⟩ : syracuseStep 4108643 = 6162965) B6162965
theorem B3297635 : Blo 539803 3297635 := bstep (se 1 (by rfl) ⟨2473226, by rfl⟩ : syracuseStep 3297635 = 4946453) B4946453
theorem B856433 : Blo 539803 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B913889 : Blo 539803 913889 := bstep (se 2 (by rfl) ⟨342708, by rfl⟩ : syracuseStep 913889 = 685417) B685417
theorem B1831409 : Blo 539803 1831409 := bstep (se 2 (by rfl) ⟨686778, by rfl⟩ : syracuseStep 1831409 = 1373557) B1373557
theorem B651827 : Blo 539803 651827 := bstep (se 1 (by rfl) ⟨488870, by rfl⟩ : syracuseStep 651827 = 977741) B977741
theorem B1823309 : Blo 539803 1823309 := bstep (se 3 (by rfl) ⟨341870, by rfl⟩ : syracuseStep 1823309 = 683741) B683741
theorem B1217105 : Blo 539803 1217105 := bstep (se 2 (by rfl) ⟨456414, by rfl⟩ : syracuseStep 1217105 = 912829) B912829
theorem B914017 : Blo 539803 914017 := bstep (se 2 (by rfl) ⟨342756, by rfl⟩ : syracuseStep 914017 = 685513) B685513
theorem B1217123 : Blo 539803 1217123 := bstep (se 1 (by rfl) ⟨912842, by rfl⟩ : syracuseStep 1217123 = 1825685) B1825685
theorem B1946225 : Blo 539803 1946225 := bstep (se 2 (by rfl) ⟨729834, by rfl⟩ : syracuseStep 1946225 = 1459669) B1459669
theorem B1823363 : Blo 539803 1823363 := bstep (se 1 (by rfl) ⟨1367522, by rfl⟩ : syracuseStep 1823363 = 2735045) B2735045
theorem B914051 : Blo 539803 914051 := bstep (se 1 (by rfl) ⟨685538, by rfl⟩ : syracuseStep 914051 = 1371077) B1371077
theorem B2740877 : Blo 539803 2740877 := bstep (se 3 (by rfl) ⟨513914, by rfl⟩ : syracuseStep 2740877 = 1027829) B1027829
theorem B1028771 : Blo 539803 1028771 := bstep (se 1 (by rfl) ⟨771578, by rfl⟩ : syracuseStep 1028771 = 1543157) B1543157
theorem B6099697 : Blo 539803 6099697 := bstep (se 2 (by rfl) ⟨2287386, by rfl⟩ : syracuseStep 6099697 = 4574773) B4574773
theorem B865027 : Blo 539803 865027 := bstep (se 1 (by rfl) ⟨648770, by rfl⟩ : syracuseStep 865027 = 1297541) B1297541
theorem B914179 : Blo 539803 914179 := bstep (se 1 (by rfl) ⟨685634, by rfl⟩ : syracuseStep 914179 = 1371269) B1371269
theorem B3912461 : Blo 539803 3912461 := bstep (se 3 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 3912461 = 1467173) B1467173
theorem B865073 : Blo 539803 865073 := bstep (se 2 (by rfl) ⟨324402, by rfl⟩ : syracuseStep 865073 = 648805) B648805
theorem B2921285 : Blo 539803 2921285 := bstep (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) B547741
theorem B1217393 : Blo 539803 1217393 := bstep (se 2 (by rfl) ⟨456522, by rfl⟩ : syracuseStep 1217393 = 913045) B913045
theorem B1217411 : Blo 539803 1217411 := bstep (se 1 (by rfl) ⟨913058, by rfl⟩ : syracuseStep 1217411 = 1826117) B1826117
theorem B684931 : Blo 539803 684931 := bstep (se 1 (by rfl) ⟨513698, by rfl⟩ : syracuseStep 684931 = 1027397) B1027397
theorem B1823633 : Blo 539803 1823633 := bstep (se 2 (by rfl) ⟨683862, by rfl⟩ : syracuseStep 1823633 = 1367725) B1367725
theorem B914321 : Blo 539803 914321 := bstep (se 2 (by rfl) ⟨342870, by rfl⟩ : syracuseStep 914321 = 685741) B685741
theorem B783283 : Blo 539803 783283 := bstep (se 1 (by rfl) ⟨587462, by rfl⟩ : syracuseStep 783283 = 1174925) B1174925
theorem B2315213 : Blo 539803 2315213 := bstep (se 3 (by rfl) ⟨434102, by rfl⟩ : syracuseStep 2315213 = 868205) B868205
theorem B685027 : Blo 539803 685027 := bstep (se 1 (by rfl) ⟨513770, by rfl⟩ : syracuseStep 685027 = 1027541) B1027541
theorem B2315249 : Blo 539803 2315249 := bstep (se 2 (by rfl) ⟨868218, by rfl⟩ : syracuseStep 2315249 = 1736437) B1736437
theorem B1586161 : Blo 539803 1586161 := bstep (se 2 (by rfl) ⟨594810, by rfl⟩ : syracuseStep 1586161 = 1189621) B1189621
theorem B1831949 : Blo 539803 1831949 := bstep (se 3 (by rfl) ⟨343490, by rfl⟩ : syracuseStep 1831949 = 686981) B686981
theorem B914449 : Blo 539803 914449 := bstep (se 2 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 914449 = 685837) B685837
theorem B1373233 : Blo 539803 1373233 := bstep (se 2 (by rfl) ⟨514962, by rfl⟩ : syracuseStep 1373233 = 1029925) B1029925
theorem B914483 : Blo 539803 914483 := bstep (se 1 (by rfl) ⟨685862, by rfl⟩ : syracuseStep 914483 = 1371725) B1371725
theorem B2307149 : Blo 539803 2307149 := bstep (se 3 (by rfl) ⟨432590, by rfl⟩ : syracuseStep 2307149 = 865181) B865181
theorem B1217681 : Blo 539803 1217681 := bstep (se 2 (by rfl) ⟨456630, by rfl⟩ : syracuseStep 1217681 = 913261) B913261
theorem B1217699 : Blo 539803 1217699 := bstep (se 1 (by rfl) ⟨913274, by rfl⟩ : syracuseStep 1217699 = 1826549) B1826549
theorem B1545389 : Blo 539803 1545389 := bstep (se 3 (by rfl) ⟨289760, by rfl⟩ : syracuseStep 1545389 = 579521) B579521
theorem B914611 : Blo 539803 914611 := bstep (se 1 (by rfl) ⟨685958, by rfl⟩ : syracuseStep 914611 = 1371917) B1371917
theorem B1738385 : Blo 539803 1738385 := bstep (se 2 (by rfl) ⟨651894, by rfl⟩ : syracuseStep 1738385 = 1303789) B1303789
theorem B2463011 : Blo 539803 2463011 := bstep (se 1 (by rfl) ⟨1847258, by rfl⟩ : syracuseStep 2463011 = 3694517) B3694517
theorem B1537325 : Blo 539803 1537325 := bstep (se 3 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 1537325 = 576497) B576497
theorem B914753 : Blo 539803 914753 := bstep (se 2 (by rfl) ⟨343032, by rfl⟩ : syracuseStep 914753 = 686065) B686065
theorem B1373507 : Blo 539803 1373507 := bstep (se 1 (by rfl) ⟨1030130, by rfl⟩ : syracuseStep 1373507 = 2060261) B2060261
theorem B1545571 : Blo 539803 1545571 := bstep (se 1 (by rfl) ⟨1159178, by rfl⟩ : syracuseStep 1545571 = 2318357) B2318357
theorem B1537393 : Blo 539803 1537393 := bstep (se 2 (by rfl) ⟨576522, by rfl⟩ : syracuseStep 1537393 = 1153045) B1153045
theorem B2733425 : Blo 539803 2733425 := bstep (se 2 (by rfl) ⟨1025034, by rfl⟩ : syracuseStep 2733425 = 2050069) B2050069
theorem B8336753 : Blo 539803 8336753 := bstep (se 2 (by rfl) ⟨3126282, by rfl⟩ : syracuseStep 8336753 = 6252565) B6252565
theorem B1545617 : Blo 539803 1545617 := bstep (se 2 (by rfl) ⟨579606, by rfl⟩ : syracuseStep 1545617 = 1159213) B1159213
theorem B2307491 : Blo 539803 2307491 := bstep (se 1 (by rfl) ⟨1730618, by rfl⟩ : syracuseStep 2307491 = 3461237) B3461237
theorem B1824173 : Blo 539803 1824173 := bstep (se 3 (by rfl) ⟨342032, by rfl⟩ : syracuseStep 1824173 = 684065) B684065
theorem B1217969 : Blo 539803 1217969 := bstep (se 2 (by rfl) ⟨456738, by rfl⟩ : syracuseStep 1217969 = 913477) B913477
theorem B914881 : Blo 539803 914881 := bstep (se 2 (by rfl) ⟨343080, by rfl⟩ : syracuseStep 914881 = 686161) B686161
theorem B1217987 : Blo 539803 1217987 := bstep (se 1 (by rfl) ⟨913490, by rfl⟩ : syracuseStep 1217987 = 1826981) B1826981
theorem B865745 : Blo 539803 865745 := bstep (se 2 (by rfl) ⟨324654, by rfl⟩ : syracuseStep 865745 = 649309) B649309
theorem B685523 : Blo 539803 685523 := bstep (se 1 (by rfl) ⟨514142, by rfl⟩ : syracuseStep 685523 = 1028285) B1028285
theorem B1824227 : Blo 539803 1824227 := bstep (se 1 (by rfl) ⟨1368170, by rfl⟩ : syracuseStep 1824227 = 2736341) B2736341
theorem B914915 : Blo 539803 914915 := bstep (se 1 (by rfl) ⟨686186, by rfl⟩ : syracuseStep 914915 = 1372373) B1372373
theorem B1373699 : Blo 539803 1373699 := bstep (se 1 (by rfl) ⟨1030274, by rfl⟩ : syracuseStep 1373699 = 2060549) B2060549
theorem B1947149 : Blo 539803 1947149 := bstep (se 3 (by rfl) ⟨365090, by rfl⟩ : syracuseStep 1947149 = 730181) B730181
theorem B579107 : Blo 539803 579107 := bstep (se 1 (by rfl) ⟨434330, by rfl⟩ : syracuseStep 579107 = 868661) B868661
theorem B1029667 : Blo 539803 1029667 := bstep (se 1 (by rfl) ⟨772250, by rfl⟩ : syracuseStep 1029667 = 1544501) B1544501
theorem B988771 : Blo 539803 988771 := bstep (se 1 (by rfl) ⟨741578, by rfl⟩ : syracuseStep 988771 = 1483157) B1483157
theorem B915043 : Blo 539803 915043 := bstep (se 1 (by rfl) ⟨686282, by rfl⟩ : syracuseStep 915043 = 1372565) B1372565
theorem B2053745 : Blo 539803 2053745 := bstep (se 2 (by rfl) ⟨770154, by rfl⟩ : syracuseStep 2053745 = 1540309) B1540309
theorem B1734257 : Blo 539803 1734257 := bstep (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) B1300693
theorem B1537667 : Blo 539803 1537667 := bstep (se 1 (by rfl) ⟨1153250, by rfl⟩ : syracuseStep 1537667 = 2306501) B2306501
theorem B824993 : Blo 539803 824993 := bstep (se 2 (by rfl) ⟨309372, by rfl⟩ : syracuseStep 824993 = 618745) B618745
theorem B1029827 : Blo 539803 1029827 := bstep (se 1 (by rfl) ⟨772370, by rfl⟩ : syracuseStep 1029827 = 1544741) B1544741
theorem B1218257 : Blo 539803 1218257 := bstep (se 2 (by rfl) ⟨456846, by rfl⟩ : syracuseStep 1218257 = 913693) B913693
theorem B1218275 : Blo 539803 1218275 := bstep (se 1 (by rfl) ⟨913706, by rfl⟩ : syracuseStep 1218275 = 1827413) B1827413
theorem B1824497 : Blo 539803 1824497 := bstep (se 2 (by rfl) ⟨684186, by rfl⟩ : syracuseStep 1824497 = 1368373) B1368373
theorem B915185 : Blo 539803 915185 := bstep (se 2 (by rfl) ⟨343194, by rfl⟩ : syracuseStep 915185 = 686389) B686389
theorem B3127045 : Blo 539803 3127045 := bstep (se 4 (by rfl) ⟨293160, by rfl⟩ : syracuseStep 3127045 = 586321) B586321
theorem B3389219 : Blo 539803 3389219 := bstep (se 1 (by rfl) ⟨2541914, by rfl⟩ : syracuseStep 3389219 = 5083829) B5083829
theorem B2307953 : Blo 539803 2307953 := bstep (se 2 (by rfl) ⟨865482, by rfl⟩ : syracuseStep 2307953 = 1730965) B1730965
theorem B915313 : Blo 539803 915313 := bstep (se 2 (by rfl) ⟨343242, by rfl⟩ : syracuseStep 915313 = 686485) B686485
theorem B3086221 : Blo 539803 3086221 := bstep (se 3 (by rfl) ⟨578666, by rfl⟩ : syracuseStep 3086221 = 1157333) B1157333
theorem B915347 : Blo 539803 915347 := bstep (se 1 (by rfl) ⟨686510, by rfl⟩ : syracuseStep 915347 = 1373021) B1373021
theorem B866257 : Blo 539803 866257 := bstep (se 2 (by rfl) ⟨324846, by rfl⟩ : syracuseStep 866257 = 649693) B649693
theorem B825299 : Blo 539803 825299 := bstep (se 1 (by rfl) ⟨618974, by rfl⟩ : syracuseStep 825299 = 1237949) B1237949
theorem B1218545 : Blo 539803 1218545 := bstep (se 2 (by rfl) ⟨456954, by rfl⟩ : syracuseStep 1218545 = 913909) B913909
theorem B1218563 : Blo 539803 1218563 := bstep (se 1 (by rfl) ⟨913922, by rfl⟩ : syracuseStep 1218563 = 1827845) B1827845
theorem B915475 : Blo 539803 915475 := bstep (se 1 (by rfl) ⟨686606, by rfl⟩ : syracuseStep 915475 = 1373213) B1373213
theorem B3471437 : Blo 539803 3471437 := bstep (se 3 (by rfl) ⟨650894, by rfl⟩ : syracuseStep 3471437 = 1301789) B1301789
theorem B5544035 : Blo 539803 5544035 := bstep (se 1 (by rfl) ⟨4158026, by rfl⟩ : syracuseStep 5544035 = 8316053) B8316053
theorem B1734797 : Blo 539803 1734797 := bstep (se 3 (by rfl) ⟨325274, by rfl⟩ : syracuseStep 1734797 = 650549) B650549
theorem B686227 : Blo 539803 686227 := bstep (se 1 (by rfl) ⟨514670, by rfl⟩ : syracuseStep 686227 = 1029341) B1029341
theorem B915617 : Blo 539803 915617 := bstep (se 2 (by rfl) ⟨343356, by rfl⟩ : syracuseStep 915617 = 686713) B686713
theorem B16890083 : Blo 539803 16890083 := bstep (se 1 (by rfl) ⟨12667562, by rfl⟩ : syracuseStep 16890083 = 25335125) B25335125
theorem B686323 : Blo 539803 686323 := bstep (se 1 (by rfl) ⟨514742, by rfl⟩ : syracuseStep 686323 = 1029485) B1029485
theorem B1825037 : Blo 539803 1825037 := bstep (se 3 (by rfl) ⟨342194, by rfl⟩ : syracuseStep 1825037 = 684389) B684389
theorem B1218833 : Blo 539803 1218833 := bstep (se 2 (by rfl) ⟨457062, by rfl⟩ : syracuseStep 1218833 = 914125) B914125
theorem B915745 : Blo 539803 915745 := bstep (se 2 (by rfl) ⟨343404, by rfl⟩ : syracuseStep 915745 = 686809) B686809
theorem B1218851 : Blo 539803 1218851 := bstep (se 1 (by rfl) ⟨914138, by rfl⟩ : syracuseStep 1218851 = 1828277) B1828277
theorem B1825091 : Blo 539803 1825091 := bstep (se 1 (by rfl) ⟨1368818, by rfl⟩ : syracuseStep 1825091 = 2737637) B2737637
theorem B915779 : Blo 539803 915779 := bstep (se 1 (by rfl) ⟨686834, by rfl⟩ : syracuseStep 915779 = 1373669) B1373669
theorem B1644877 : Blo 539803 1644877 := bstep (se 3 (by rfl) ⟨308414, by rfl⟩ : syracuseStep 1644877 = 616829) B616829
theorem B1096067 : Blo 539803 1096067 := bstep (se 1 (by rfl) ⟨822050, by rfl⟩ : syracuseStep 1096067 = 1644101) B1644101
theorem B2595235 : Blo 539803 2595235 := bstep (se 1 (by rfl) ⟨1946426, by rfl⟩ : syracuseStep 2595235 = 3892853) B3892853
theorem B915907 : Blo 539803 915907 := bstep (se 1 (by rfl) ⟨686930, by rfl⟩ : syracuseStep 915907 = 1373861) B1373861
theorem B1538509 : Blo 539803 1538509 := bstep (se 3 (by rfl) ⟨288470, by rfl⟩ : syracuseStep 1538509 = 576941) B576941
theorem B2783693 : Blo 539803 2783693 := bstep (se 3 (by rfl) ⟨521942, by rfl⟩ : syracuseStep 2783693 = 1043885) B1043885
theorem B1169905 : Blo 539803 1169905 := bstep (se 2 (by rfl) ⟨438714, by rfl⟩ : syracuseStep 1169905 = 877429) B877429
theorem B1014257 : Blo 539803 1014257 := bstep (se 2 (by rfl) ⟨380346, by rfl⟩ : syracuseStep 1014257 = 760693) B760693
theorem B3299825 : Blo 539803 3299825 := bstep (se 2 (by rfl) ⟨1237434, by rfl⟩ : syracuseStep 3299825 = 2474869) B2474869
theorem B1219121 : Blo 539803 1219121 := bstep (se 2 (by rfl) ⟨457170, by rfl⟩ : syracuseStep 1219121 = 914341) B914341
theorem B1219139 : Blo 539803 1219139 := bstep (se 1 (by rfl) ⟨914354, by rfl⟩ : syracuseStep 1219139 = 1828709) B1828709
theorem B1825361 : Blo 539803 1825361 := bstep (se 2 (by rfl) ⟨684510, by rfl⟩ : syracuseStep 1825361 = 1369021) B1369021
theorem B1538669 : Blo 539803 1538669 := bstep (se 3 (by rfl) ⟨288500, by rfl⟩ : syracuseStep 1538669 = 577001) B577001
theorem B1948387 : Blo 539803 1948387 := bstep (se 1 (by rfl) ⟨1461290, by rfl⟩ : syracuseStep 1948387 = 2922581) B2922581
theorem B686819 : Blo 539803 686819 := bstep (se 1 (by rfl) ⟨515114, by rfl⟩ : syracuseStep 686819 = 1030229) B1030229
theorem B809729 : Blo 539803 809729 := bstep (se 2 (by rfl) ⟨303648, by rfl⟩ : syracuseStep 809729 = 607297) B607297
theorem B809747 : Blo 539803 809747 := bstep (se 1 (by rfl) ⟨607310, by rfl⟩ : syracuseStep 809747 = 1214621) B1214621
theorem B2734883 : Blo 539803 2734883 := bstep (se 1 (by rfl) ⟨2051162, by rfl⟩ : syracuseStep 2734883 = 4102325) B4102325
theorem B1538851 : Blo 539803 1538851 := bstep (se 1 (by rfl) ⟨1154138, by rfl⟩ : syracuseStep 1538851 = 2308277) B2308277
theorem B2931491 : Blo 539803 2931491 := bstep (se 1 (by rfl) ⟨2198618, by rfl⟩ : syracuseStep 2931491 = 4397237) B4397237
theorem B809777 : Blo 539803 809777 := bstep (se 2 (by rfl) ⟨303666, by rfl⟩ : syracuseStep 809777 = 607333) B607333
theorem B809795 : Blo 539803 809795 := bstep (se 1 (by rfl) ⟨607346, by rfl⟩ : syracuseStep 809795 = 1214693) B1214693
theorem B1366865 : Blo 539803 1366865 := bstep (se 2 (by rfl) ⟨512574, by rfl⟩ : syracuseStep 1366865 = 1025149) B1025149
theorem B1219409 : Blo 539803 1219409 := bstep (se 2 (by rfl) ⟨457278, by rfl⟩ : syracuseStep 1219409 = 914557) B914557
theorem B809825 : Blo 539803 809825 := bstep (se 2 (by rfl) ⟨303684, by rfl⟩ : syracuseStep 809825 = 607369) B607369
theorem B1219427 : Blo 539803 1219427 := bstep (se 1 (by rfl) ⟨914570, by rfl⟩ : syracuseStep 1219427 = 1829141) B1829141
theorem B809843 : Blo 539803 809843 := bstep (se 1 (by rfl) ⟨607382, by rfl⟩ : syracuseStep 809843 = 1214765) B1214765
theorem B1366915 : Blo 539803 1366915 := bstep (se 1 (by rfl) ⟨1025186, by rfl⟩ : syracuseStep 1366915 = 2050373) B2050373
theorem B809873 : Blo 539803 809873 := bstep (se 2 (by rfl) ⟨303702, by rfl⟩ : syracuseStep 809873 = 607405) B607405
theorem B809891 : Blo 539803 809891 := bstep (se 1 (by rfl) ⟨607418, by rfl⟩ : syracuseStep 809891 = 1214837) B1214837
theorem B2923427 : Blo 539803 2923427 := bstep (se 1 (by rfl) ⟨2192570, by rfl⟩ : syracuseStep 2923427 = 4385141) B4385141
theorem B809921 : Blo 539803 809921 := bstep (se 2 (by rfl) ⟨303720, by rfl⟩ : syracuseStep 809921 = 607441) B607441
theorem B809939 : Blo 539803 809939 := bstep (se 1 (by rfl) ⟨607454, by rfl⟩ : syracuseStep 809939 = 1214909) B1214909
theorem B809969 : Blo 539803 809969 := bstep (se 2 (by rfl) ⟨303738, by rfl⟩ : syracuseStep 809969 = 607477) B607477
theorem B809987 : Blo 539803 809987 := bstep (se 1 (by rfl) ⟨607490, by rfl⟩ : syracuseStep 809987 = 1214981) B1214981
theorem B769027 : Blo 539803 769027 := bstep (se 1 (by rfl) ⟨576770, by rfl⟩ : syracuseStep 769027 = 1153541) B1153541
theorem B1367057 : Blo 539803 1367057 := bstep (se 2 (by rfl) ⟨512646, by rfl⟩ : syracuseStep 1367057 = 1025293) B1025293
theorem B810017 : Blo 539803 810017 := bstep (se 2 (by rfl) ⟨303756, by rfl⟩ : syracuseStep 810017 = 607513) B607513
theorem B2055203 : Blo 539803 2055203 := bstep (se 1 (by rfl) ⟨1541402, by rfl⟩ : syracuseStep 2055203 = 3082805) B3082805
theorem B810035 : Blo 539803 810035 := bstep (se 1 (by rfl) ⟨607526, by rfl⟩ : syracuseStep 810035 = 1215053) B1215053
theorem B1850435 : Blo 539803 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B2530381 : Blo 539803 2530381 := bstep (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) B948893
theorem B2849869 : Blo 539803 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B810065 : Blo 539803 810065 := bstep (se 2 (by rfl) ⟨303774, by rfl⟩ : syracuseStep 810065 = 607549) B607549
theorem B810083 : Blo 539803 810083 := bstep (se 1 (by rfl) ⟨607562, by rfl⟩ : syracuseStep 810083 = 1215125) B1215125
theorem B1825901 : Blo 539803 1825901 := bstep (se 3 (by rfl) ⟨342356, by rfl⟩ : syracuseStep 1825901 = 684713) B684713
theorem B1219697 : Blo 539803 1219697 := bstep (se 2 (by rfl) ⟨457386, by rfl⟩ : syracuseStep 1219697 = 914773) B914773
theorem B810113 : Blo 539803 810113 := bstep (se 2 (by rfl) ⟨303792, by rfl⟩ : syracuseStep 810113 = 607585) B607585
theorem B1219715 : Blo 539803 1219715 := bstep (se 1 (by rfl) ⟨914786, by rfl⟩ : syracuseStep 1219715 = 1829573) B1829573
theorem B2784397 : Blo 539803 2784397 := bstep (se 3 (by rfl) ⟨522074, by rfl⟩ : syracuseStep 2784397 = 1044149) B1044149
theorem B810131 : Blo 539803 810131 := bstep (se 1 (by rfl) ⟨607598, by rfl⟩ : syracuseStep 810131 = 1215197) B1215197
theorem B539811 : Blo 539803 539811 := bstep (se 1 (by rfl) ⟨404858, by rfl⟩ : syracuseStep 539811 = 809717) B809717
theorem B1825955 : Blo 539803 1825955 := bstep (se 1 (by rfl) ⟨1369466, by rfl⟩ : syracuseStep 1825955 = 2738933) B2738933
theorem B810161 : Blo 539803 810161 := bstep (se 2 (by rfl) ⟨303810, by rfl⟩ : syracuseStep 810161 = 607621) B607621
theorem B539827 : Blo 539803 539827 := bstep (se 1 (by rfl) ⟨404870, by rfl⟩ : syracuseStep 539827 = 809741) B809741
theorem B539843 : Blo 539803 539843 := bstep (se 1 (by rfl) ⟨404882, by rfl⟩ : syracuseStep 539843 = 809765) B809765
theorem B810179 : Blo 539803 810179 := bstep (se 1 (by rfl) ⟨607634, by rfl⟩ : syracuseStep 810179 = 1215269) B1215269
theorem B539859 : Blo 539803 539859 := bstep (se 1 (by rfl) ⟨404894, by rfl⟩ : syracuseStep 539859 = 809789) B809789
theorem B867539 : Blo 539803 867539 := bstep (se 1 (by rfl) ⟨650654, by rfl⟩ : syracuseStep 867539 = 1301309) B1301309
theorem B1465553 : Blo 539803 1465553 := bstep (se 2 (by rfl) ⟨549582, by rfl⟩ : syracuseStep 1465553 = 1099165) B1099165
theorem B810209 : Blo 539803 810209 := bstep (se 2 (by rfl) ⟨303828, by rfl⟩ : syracuseStep 810209 = 607657) B607657
theorem B539875 : Blo 539803 539875 := bstep (se 1 (by rfl) ⟨404906, by rfl⟩ : syracuseStep 539875 = 809813) B809813
theorem B539891 : Blo 539803 539891 := bstep (se 1 (by rfl) ⟨404918, by rfl⟩ : syracuseStep 539891 = 809837) B809837
theorem B810227 : Blo 539803 810227 := bstep (se 1 (by rfl) ⟨607670, by rfl⟩ : syracuseStep 810227 = 1215341) B1215341
theorem B539907 : Blo 539803 539907 := bstep (se 1 (by rfl) ⟨404930, by rfl⟩ : syracuseStep 539907 = 809861) B809861
theorem B4119821 : Blo 539803 4119821 := bstep (se 3 (by rfl) ⟨772466, by rfl⟩ : syracuseStep 4119821 = 1544933) B1544933
theorem B810257 : Blo 539803 810257 := bstep (se 2 (by rfl) ⟨303846, by rfl⟩ : syracuseStep 810257 = 607693) B607693
theorem B539923 : Blo 539803 539923 := bstep (se 1 (by rfl) ⟨404942, by rfl⟩ : syracuseStep 539923 = 809885) B809885
theorem B539939 : Blo 539803 539939 := bstep (se 1 (by rfl) ⟨404954, by rfl⟩ : syracuseStep 539939 = 809909) B809909
theorem B810275 : Blo 539803 810275 := bstep (se 1 (by rfl) ⟨607706, by rfl⟩ : syracuseStep 810275 = 1215413) B1215413
theorem B539955 : Blo 539803 539955 := bstep (se 1 (by rfl) ⟨404966, by rfl⟩ : syracuseStep 539955 = 809933) B809933
theorem B810305 : Blo 539803 810305 := bstep (se 2 (by rfl) ⟨303864, by rfl⟩ : syracuseStep 810305 = 607729) B607729
theorem B539971 : Blo 539803 539971 := bstep (se 1 (by rfl) ⟨404978, by rfl⟩ : syracuseStep 539971 = 809957) B809957
theorem B539987 : Blo 539803 539987 := bstep (se 1 (by rfl) ⟨404990, by rfl⟩ : syracuseStep 539987 = 809981) B809981
theorem B810323 : Blo 539803 810323 := bstep (se 1 (by rfl) ⟨607742, by rfl⟩ : syracuseStep 810323 = 1215485) B1215485
theorem B867667 : Blo 539803 867667 := bstep (se 1 (by rfl) ⟨650750, by rfl⟩ : syracuseStep 867667 = 1301501) B1301501
theorem B540003 : Blo 539803 540003 := bstep (se 1 (by rfl) ⟨405002, by rfl⟩ : syracuseStep 540003 = 810005) B810005
theorem B810353 : Blo 539803 810353 := bstep (se 2 (by rfl) ⟨303882, by rfl⟩ : syracuseStep 810353 = 607765) B607765
theorem B540019 : Blo 539803 540019 := bstep (se 1 (by rfl) ⟨405014, by rfl⟩ : syracuseStep 540019 = 810029) B810029
theorem B540035 : Blo 539803 540035 := bstep (se 1 (by rfl) ⟨405026, by rfl⟩ : syracuseStep 540035 = 810053) B810053
theorem B810371 : Blo 539803 810371 := bstep (se 1 (by rfl) ⟨607778, by rfl⟩ : syracuseStep 810371 = 1215557) B1215557
theorem B1219985 : Blo 539803 1219985 := bstep (se 2 (by rfl) ⟨457494, by rfl⟩ : syracuseStep 1219985 = 914989) B914989
theorem B540051 : Blo 539803 540051 := bstep (se 1 (by rfl) ⟨405038, by rfl⟩ : syracuseStep 540051 = 810077) B810077
theorem B810401 : Blo 539803 810401 := bstep (se 2 (by rfl) ⟨303900, by rfl⟩ : syracuseStep 810401 = 607801) B607801
theorem B540067 : Blo 539803 540067 := bstep (se 1 (by rfl) ⟨405050, by rfl⟩ : syracuseStep 540067 = 810101) B810101
theorem B1301923 : Blo 539803 1301923 := bstep (se 1 (by rfl) ⟨976442, by rfl⟩ : syracuseStep 1301923 = 1952885) B1952885
theorem B1220003 : Blo 539803 1220003 := bstep (se 1 (by rfl) ⟨915002, by rfl⟩ : syracuseStep 1220003 = 1830005) B1830005
theorem B1826225 : Blo 539803 1826225 := bstep (se 2 (by rfl) ⟨684834, by rfl⟩ : syracuseStep 1826225 = 1369669) B1369669
theorem B540083 : Blo 539803 540083 := bstep (se 1 (by rfl) ⟨405062, by rfl⟩ : syracuseStep 540083 = 810125) B810125
theorem B810419 : Blo 539803 810419 := bstep (se 1 (by rfl) ⟨607814, by rfl⟩ : syracuseStep 810419 = 1215629) B1215629
theorem B540099 : Blo 539803 540099 := bstep (se 1 (by rfl) ⟨405074, by rfl⟩ : syracuseStep 540099 = 810149) B810149
theorem B810449 : Blo 539803 810449 := bstep (se 2 (by rfl) ⟨303918, by rfl⟩ : syracuseStep 810449 = 607837) B607837
theorem B540115 : Blo 539803 540115 := bstep (se 1 (by rfl) ⟨405086, by rfl⟩ : syracuseStep 540115 = 810173) B810173
theorem B769505 : Blo 539803 769505 := bstep (se 2 (by rfl) ⟨288564, by rfl⟩ : syracuseStep 769505 = 577129) B577129
theorem B867809 : Blo 539803 867809 := bstep (se 2 (by rfl) ⟨325428, by rfl⟩ : syracuseStep 867809 = 650857) B650857
theorem B540131 : Blo 539803 540131 := bstep (se 1 (by rfl) ⟨405098, by rfl⟩ : syracuseStep 540131 = 810197) B810197
theorem B810467 : Blo 539803 810467 := bstep (se 1 (by rfl) ⟨607850, by rfl⟩ : syracuseStep 810467 = 1215701) B1215701
theorem B1154531 : Blo 539803 1154531 := bstep (se 1 (by rfl) ⟨865898, by rfl⟩ : syracuseStep 1154531 = 1731797) B1731797
theorem B2743793 : Blo 539803 2743793 := bstep (se 2 (by rfl) ⟨1028922, by rfl⟩ : syracuseStep 2743793 = 2057845) B2057845
theorem B540147 : Blo 539803 540147 := bstep (se 1 (by rfl) ⟨405110, by rfl⟩ : syracuseStep 540147 = 810221) B810221
theorem B810497 : Blo 539803 810497 := bstep (se 2 (by rfl) ⟨303936, by rfl⟩ : syracuseStep 810497 = 607873) B607873
theorem B540163 : Blo 539803 540163 := bstep (se 1 (by rfl) ⟨405122, by rfl⟩ : syracuseStep 540163 = 810245) B810245
theorem B540179 : Blo 539803 540179 := bstep (se 1 (by rfl) ⟨405134, by rfl⟩ : syracuseStep 540179 = 810269) B810269
theorem B810515 : Blo 539803 810515 := bstep (se 1 (by rfl) ⟨607886, by rfl⟩ : syracuseStep 810515 = 1215773) B1215773
theorem B540195 : Blo 539803 540195 := bstep (se 1 (by rfl) ⟨405146, by rfl⟩ : syracuseStep 540195 = 810293) B810293
theorem B810545 : Blo 539803 810545 := bstep (se 2 (by rfl) ⟨303954, by rfl⟩ : syracuseStep 810545 = 607909) B607909
theorem B540211 : Blo 539803 540211 := bstep (se 1 (by rfl) ⟨405158, by rfl⟩ : syracuseStep 540211 = 810317) B810317
theorem B540227 : Blo 539803 540227 := bstep (se 1 (by rfl) ⟨405170, by rfl⟩ : syracuseStep 540227 = 810341) B810341
theorem B810563 : Blo 539803 810563 := bstep (se 1 (by rfl) ⟨607922, by rfl⟩ : syracuseStep 810563 = 1215845) B1215845
theorem B2735693 : Blo 539803 2735693 := bstep (se 3 (by rfl) ⟨512942, by rfl⟩ : syracuseStep 2735693 = 1025885) B1025885
theorem B1302097 : Blo 539803 1302097 := bstep (se 2 (by rfl) ⟨488286, by rfl⟩ : syracuseStep 1302097 = 976573) B976573
theorem B540243 : Blo 539803 540243 := bstep (se 1 (by rfl) ⟨405182, by rfl⟩ : syracuseStep 540243 = 810365) B810365
theorem B769619 : Blo 539803 769619 := bstep (se 1 (by rfl) ⟨577214, by rfl⟩ : syracuseStep 769619 = 1154429) B1154429
theorem B810593 : Blo 539803 810593 := bstep (se 2 (by rfl) ⟨303972, by rfl⟩ : syracuseStep 810593 = 607945) B607945
theorem B540259 : Blo 539803 540259 := bstep (se 1 (by rfl) ⟨405194, by rfl⟩ : syracuseStep 540259 = 810389) B810389
theorem B5283427 : Blo 539803 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B2596465 : Blo 539803 2596465 := bstep (se 2 (by rfl) ⟨973674, by rfl⟩ : syracuseStep 2596465 = 1947349) B1947349
theorem B540275 : Blo 539803 540275 := bstep (se 1 (by rfl) ⟨405206, by rfl⟩ : syracuseStep 540275 = 810413) B810413
theorem B810611 : Blo 539803 810611 := bstep (se 1 (by rfl) ⟨607958, by rfl⟩ : syracuseStep 810611 = 1215917) B1215917
theorem B540291 : Blo 539803 540291 := bstep (se 1 (by rfl) ⟨405218, by rfl⟩ : syracuseStep 540291 = 810437) B810437
theorem B2932357 : Blo 539803 2932357 := bstep (se 4 (by rfl) ⟨274908, by rfl⟩ : syracuseStep 2932357 = 549817) B549817
theorem B2817677 : Blo 539803 2817677 := bstep (se 3 (by rfl) ⟨528314, by rfl⟩ : syracuseStep 2817677 = 1056629) B1056629
theorem B810641 : Blo 539803 810641 := bstep (se 2 (by rfl) ⟨303990, by rfl⟩ : syracuseStep 810641 = 607981) B607981
theorem B540307 : Blo 539803 540307 := bstep (se 1 (by rfl) ⟨405230, by rfl⟩ : syracuseStep 540307 = 810461) B810461
theorem B540323 : Blo 539803 540323 := bstep (se 1 (by rfl) ⟨405242, by rfl⟩ : syracuseStep 540323 = 810485) B810485
theorem B810659 : Blo 539803 810659 := bstep (se 1 (by rfl) ⟨607994, by rfl⟩ : syracuseStep 810659 = 1215989) B1215989
theorem B769699 : Blo 539803 769699 := bstep (se 1 (by rfl) ⟨577274, by rfl⟩ : syracuseStep 769699 = 1154549) B1154549
theorem B540339 : Blo 539803 540339 := bstep (se 1 (by rfl) ⟨405254, by rfl⟩ : syracuseStep 540339 = 810509) B810509
theorem B1220273 : Blo 539803 1220273 := bstep (se 2 (by rfl) ⟨457602, by rfl⟩ : syracuseStep 1220273 = 915205) B915205
theorem B810689 : Blo 539803 810689 := bstep (se 2 (by rfl) ⟨304008, by rfl⟩ : syracuseStep 810689 = 608017) B608017
theorem B540355 : Blo 539803 540355 := bstep (se 1 (by rfl) ⟨405266, by rfl⟩ : syracuseStep 540355 = 810533) B810533
theorem B1220291 : Blo 539803 1220291 := bstep (se 1 (by rfl) ⟨915218, by rfl⟩ : syracuseStep 1220291 = 1830437) B1830437
theorem B810707 : Blo 539803 810707 := bstep (se 1 (by rfl) ⟨608030, by rfl⟩ : syracuseStep 810707 = 1216061) B1216061
theorem B540371 : Blo 539803 540371 := bstep (se 1 (by rfl) ⟨405278, by rfl⟩ : syracuseStep 540371 = 810557) B810557
theorem B540387 : Blo 539803 540387 := bstep (se 1 (by rfl) ⟨405290, by rfl⟩ : syracuseStep 540387 = 810581) B810581
theorem B810737 : Blo 539803 810737 := bstep (se 2 (by rfl) ⟨304026, by rfl⟩ : syracuseStep 810737 = 608053) B608053
theorem B540403 : Blo 539803 540403 := bstep (se 1 (by rfl) ⟨405302, by rfl⟩ : syracuseStep 540403 = 810605) B810605
theorem B868097 : Blo 539803 868097 := bstep (se 2 (by rfl) ⟨325536, by rfl⟩ : syracuseStep 868097 = 651073) B651073
theorem B540419 : Blo 539803 540419 := bstep (se 1 (by rfl) ⟨405314, by rfl⟩ : syracuseStep 540419 = 810629) B810629
theorem B810755 : Blo 539803 810755 := bstep (se 1 (by rfl) ⟨608066, by rfl⟩ : syracuseStep 810755 = 1216133) B1216133
theorem B540435 : Blo 539803 540435 := bstep (se 1 (by rfl) ⟨405326, by rfl⟩ : syracuseStep 540435 = 810653) B810653
theorem B810785 : Blo 539803 810785 := bstep (se 2 (by rfl) ⟨304044, by rfl⟩ : syracuseStep 810785 = 608089) B608089
theorem B540451 : Blo 539803 540451 := bstep (se 1 (by rfl) ⟨405338, by rfl⟩ : syracuseStep 540451 = 810677) B810677
theorem B540467 : Blo 539803 540467 := bstep (se 1 (by rfl) ⟨405350, by rfl⟩ : syracuseStep 540467 = 810701) B810701
theorem B810803 : Blo 539803 810803 := bstep (se 1 (by rfl) ⟨608102, by rfl⟩ : syracuseStep 810803 = 1216205) B1216205
theorem B540483 : Blo 539803 540483 := bstep (se 1 (by rfl) ⟨405362, by rfl⟩ : syracuseStep 540483 = 810725) B810725
theorem B3088205 : Blo 539803 3088205 := bstep (se 3 (by rfl) ⟨579038, by rfl⟩ : syracuseStep 3088205 = 1158077) B1158077
theorem B810833 : Blo 539803 810833 := bstep (se 2 (by rfl) ⟨304062, by rfl⟩ : syracuseStep 810833 = 608125) B608125
theorem B540499 : Blo 539803 540499 := bstep (se 1 (by rfl) ⟨405374, by rfl⟩ : syracuseStep 540499 = 810749) B810749
theorem B1752931 : Blo 539803 1752931 := bstep (se 1 (by rfl) ⟨1314698, by rfl⟩ : syracuseStep 1752931 = 2629397) B2629397
theorem B540515 : Blo 539803 540515 := bstep (se 1 (by rfl) ⟨405386, by rfl⟩ : syracuseStep 540515 = 810773) B810773
theorem B810851 : Blo 539803 810851 := bstep (se 1 (by rfl) ⟨608138, by rfl⟩ : syracuseStep 810851 = 1216277) B1216277
theorem B13188977 : Blo 539803 13188977 := bstep (se 2 (by rfl) ⟨4945866, by rfl⟩ : syracuseStep 13188977 = 9891733) B9891733
theorem B540531 : Blo 539803 540531 := bstep (se 1 (by rfl) ⟨405398, by rfl⟩ : syracuseStep 540531 = 810797) B810797
theorem B810881 : Blo 539803 810881 := bstep (se 2 (by rfl) ⟨304080, by rfl⟩ : syracuseStep 810881 = 608161) B608161
theorem B540547 : Blo 539803 540547 := bstep (se 1 (by rfl) ⟨405410, by rfl⟩ : syracuseStep 540547 = 810821) B810821
theorem B540563 : Blo 539803 540563 := bstep (se 1 (by rfl) ⟨405422, by rfl⟩ : syracuseStep 540563 = 810845) B810845
theorem B810899 : Blo 539803 810899 := bstep (se 1 (by rfl) ⟨608174, by rfl⟩ : syracuseStep 810899 = 1216349) B1216349
theorem B540579 : Blo 539803 540579 := bstep (se 1 (by rfl) ⟨405434, by rfl⟩ : syracuseStep 540579 = 810869) B810869
theorem B810929 : Blo 539803 810929 := bstep (se 2 (by rfl) ⟨304098, by rfl⟩ : syracuseStep 810929 = 608197) B608197
theorem B540595 : Blo 539803 540595 := bstep (se 1 (by rfl) ⟨405446, by rfl⟩ : syracuseStep 540595 = 810893) B810893
theorem B540611 : Blo 539803 540611 := bstep (se 1 (by rfl) ⟨405458, by rfl⟩ : syracuseStep 540611 = 810917) B810917
theorem B810947 : Blo 539803 810947 := bstep (se 1 (by rfl) ⟨608210, by rfl⟩ : syracuseStep 810947 = 1216421) B1216421
theorem B4440005 : Blo 539803 4440005 := bstep (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) B832501
theorem B3702725 : Blo 539803 3702725 := bstep (se 4 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 3702725 = 694261) B694261
theorem B1826765 : Blo 539803 1826765 := bstep (se 3 (by rfl) ⟨342518, by rfl⟩ : syracuseStep 1826765 = 685037) B685037
theorem B1220561 : Blo 539803 1220561 := bstep (se 2 (by rfl) ⟨457710, by rfl⟩ : syracuseStep 1220561 = 915421) B915421
theorem B540627 : Blo 539803 540627 := bstep (se 1 (by rfl) ⟨405470, by rfl⟩ : syracuseStep 540627 = 810941) B810941
theorem B810977 : Blo 539803 810977 := bstep (se 2 (by rfl) ⟨304116, by rfl⟩ : syracuseStep 810977 = 608233) B608233
theorem B540643 : Blo 539803 540643 := bstep (se 1 (by rfl) ⟨405482, by rfl⟩ : syracuseStep 540643 = 810965) B810965
theorem B1220579 : Blo 539803 1220579 := bstep (se 1 (by rfl) ⟨915434, by rfl⟩ : syracuseStep 1220579 = 1830869) B1830869
theorem B1368049 : Blo 539803 1368049 := bstep (se 2 (by rfl) ⟨513018, by rfl⟩ : syracuseStep 1368049 = 1026037) B1026037
theorem B540659 : Blo 539803 540659 := bstep (se 1 (by rfl) ⟨405494, by rfl⟩ : syracuseStep 540659 = 810989) B810989
theorem B810995 : Blo 539803 810995 := bstep (se 1 (by rfl) ⟨608246, by rfl⟩ : syracuseStep 810995 = 1216493) B1216493
theorem B811019 : Blo 539803 811019 := bstep (se 1 (by rfl) ⟨608264, by rfl⟩ : syracuseStep 811019 = 1216529) B1216529
theorem B540683 : Blo 539803 540683 := bstep (se 1 (by rfl) ⟨405512, by rfl⟩ : syracuseStep 540683 = 811025) B811025
theorem B811031 : Blo 539803 811031 := bstep (se 1 (by rfl) ⟨608273, by rfl⟩ : syracuseStep 811031 = 1216547) B1216547
theorem B540695 : Blo 539803 540695 := bstep (se 1 (by rfl) ⟨405521, by rfl⟩ : syracuseStep 540695 = 811043) B811043
theorem B1220633 : Blo 539803 1220633 := bstep (se 2 (by rfl) ⟨457737, by rfl⟩ : syracuseStep 1220633 = 915475) B915475
theorem B6930467 : Blo 539803 6930467 := bstep (se 1 (by rfl) ⟨5197850, by rfl⟩ : syracuseStep 6930467 = 10395701) B10395701
theorem B540715 : Blo 539803 540715 := bstep (se 1 (by rfl) ⟨405536, by rfl⟩ : syracuseStep 540715 = 811073) B811073
theorem B540727 : Blo 539803 540727 := bstep (se 1 (by rfl) ⟨405545, by rfl⟩ : syracuseStep 540727 = 811091) B811091
theorem B540747 : Blo 539803 540747 := bstep (se 1 (by rfl) ⟨405560, by rfl⟩ : syracuseStep 540747 = 811121) B811121
theorem B1949771 : Blo 539803 1949771 := bstep (se 1 (by rfl) ⟨1462328, by rfl⟩ : syracuseStep 1949771 = 2924657) B2924657
theorem B540759 : Blo 539803 540759 := bstep (se 1 (by rfl) ⟨405569, by rfl⟩ : syracuseStep 540759 = 811139) B811139
theorem B811097 : Blo 539803 811097 := bstep (se 2 (by rfl) ⟨304161, by rfl⟩ : syracuseStep 811097 = 608323) B608323
theorem B540779 : Blo 539803 540779 := bstep (se 1 (by rfl) ⟨405584, by rfl⟩ : syracuseStep 540779 = 811169) B811169
theorem B1220723 : Blo 539803 1220723 := bstep (se 1 (by rfl) ⟨915542, by rfl⟩ : syracuseStep 1220723 = 1831085) B1831085
theorem B540791 : Blo 539803 540791 := bstep (se 1 (by rfl) ⟨405593, by rfl⟩ : syracuseStep 540791 = 811187) B811187
theorem B540811 : Blo 539803 540811 := bstep (se 1 (by rfl) ⟨405608, by rfl⟩ : syracuseStep 540811 = 811217) B811217
theorem B4612247 : Blo 539803 4612247 := bstep (se 1 (by rfl) ⟨3459185, by rfl⟩ : syracuseStep 4612247 = 6918371) B6918371
theorem B540823 : Blo 539803 540823 := bstep (se 1 (by rfl) ⟨405617, by rfl⟩ : syracuseStep 540823 = 811235) B811235
theorem B1220759 : Blo 539803 1220759 := bstep (se 1 (by rfl) ⟨915569, by rfl⟩ : syracuseStep 1220759 = 1831139) B1831139
theorem B540843 : Blo 539803 540843 := bstep (se 1 (by rfl) ⟨405632, by rfl⟩ : syracuseStep 540843 = 811265) B811265
theorem B540855 : Blo 539803 540855 := bstep (se 1 (by rfl) ⟨405641, by rfl⟩ : syracuseStep 540855 = 811283) B811283
theorem B811211 : Blo 539803 811211 := bstep (se 1 (by rfl) ⟨608408, by rfl⟩ : syracuseStep 811211 = 1216817) B1216817
theorem B540875 : Blo 539803 540875 := bstep (se 1 (by rfl) ⟨405656, by rfl⟩ : syracuseStep 540875 = 811313) B811313
theorem B6234317 : Blo 539803 6234317 := bstep (se 3 (by rfl) ⟨1168934, by rfl⟩ : syracuseStep 6234317 = 2337869) B2337869
theorem B1302731 : Blo 539803 1302731 := bstep (se 1 (by rfl) ⟨977048, by rfl⟩ : syracuseStep 1302731 = 1954097) B1954097
theorem B811223 : Blo 539803 811223 := bstep (se 1 (by rfl) ⟨608417, by rfl⟩ : syracuseStep 811223 = 1216835) B1216835
theorem B540887 : Blo 539803 540887 := bstep (se 1 (by rfl) ⟨405665, by rfl⟩ : syracuseStep 540887 = 811331) B811331
theorem B540907 : Blo 539803 540907 := bstep (se 1 (by rfl) ⟨405680, by rfl⟩ : syracuseStep 540907 = 811361) B811361
theorem B540919 : Blo 539803 540919 := bstep (se 1 (by rfl) ⟨405689, by rfl⟩ : syracuseStep 540919 = 811379) B811379
theorem B540939 : Blo 539803 540939 := bstep (se 1 (by rfl) ⟨405704, by rfl⟩ : syracuseStep 540939 = 811409) B811409
theorem B2933009 : Blo 539803 2933009 := bstep (se 2 (by rfl) ⟨1099878, by rfl⟩ : syracuseStep 2933009 = 2199757) B2199757
theorem B540951 : Blo 539803 540951 := bstep (se 1 (by rfl) ⟨405713, by rfl⟩ : syracuseStep 540951 = 811427) B811427
theorem B811289 : Blo 539803 811289 := bstep (se 2 (by rfl) ⟨304233, by rfl⟩ : syracuseStep 811289 = 608467) B608467
theorem B540971 : Blo 539803 540971 := bstep (se 1 (by rfl) ⟨405728, by rfl⟩ : syracuseStep 540971 = 811457) B811457
theorem B540983 : Blo 539803 540983 := bstep (se 1 (by rfl) ⟨405737, by rfl⟩ : syracuseStep 540983 = 811475) B811475
theorem B541003 : Blo 539803 541003 := bstep (se 1 (by rfl) ⟨405752, by rfl⟩ : syracuseStep 541003 = 811505) B811505
theorem B1220939 : Blo 539803 1220939 := bstep (se 1 (by rfl) ⟨915704, by rfl⟩ : syracuseStep 1220939 = 1831409) B1831409
theorem B541015 : Blo 539803 541015 := bstep (se 1 (by rfl) ⟨405761, by rfl⟩ : syracuseStep 541015 = 811523) B811523
theorem B541035 : Blo 539803 541035 := bstep (se 1 (by rfl) ⟨405776, by rfl⟩ : syracuseStep 541035 = 811553) B811553
theorem B35553649 : Blo 539803 35553649 := bstep (se 2 (by rfl) ⟨13332618, by rfl⟩ : syracuseStep 35553649 = 26665237) B26665237
theorem B541047 : Blo 539803 541047 := bstep (se 1 (by rfl) ⟨405785, by rfl⟩ : syracuseStep 541047 = 811571) B811571
theorem B1220993 : Blo 539803 1220993 := bstep (se 2 (by rfl) ⟨457872, by rfl⟩ : syracuseStep 1220993 = 915745) B915745
theorem B811403 : Blo 539803 811403 := bstep (se 1 (by rfl) ⟨608552, by rfl⟩ : syracuseStep 811403 = 1217105) B1217105
theorem B541067 : Blo 539803 541067 := bstep (se 1 (by rfl) ⟨405800, by rfl⟩ : syracuseStep 541067 = 811601) B811601
theorem B2310551 : Blo 539803 2310551 := bstep (se 1 (by rfl) ⟨1732913, by rfl⟩ : syracuseStep 2310551 = 3465827) B3465827
theorem B811415 : Blo 539803 811415 := bstep (se 1 (by rfl) ⟨608561, by rfl⟩ : syracuseStep 811415 = 1217123) B1217123
theorem B541079 : Blo 539803 541079 := bstep (se 1 (by rfl) ⟨405809, by rfl⟩ : syracuseStep 541079 = 811619) B811619
theorem B541099 : Blo 539803 541099 := bstep (se 1 (by rfl) ⟨405824, by rfl⟩ : syracuseStep 541099 = 811649) B811649
theorem B1827251 : Blo 539803 1827251 := bstep (se 1 (by rfl) ⟨1370438, by rfl⟩ : syracuseStep 1827251 = 2740877) B2740877
theorem B541111 : Blo 539803 541111 := bstep (se 1 (by rfl) ⟨405833, by rfl⟩ : syracuseStep 541111 = 811667) B811667
theorem B541131 : Blo 539803 541131 := bstep (se 1 (by rfl) ⟨405848, by rfl⟩ : syracuseStep 541131 = 811697) B811697
theorem B811481 : Blo 539803 811481 := bstep (se 2 (by rfl) ⟨304305, by rfl⟩ : syracuseStep 811481 = 608611) B608611
theorem B541143 : Blo 539803 541143 := bstep (se 1 (by rfl) ⟨405857, by rfl⟩ : syracuseStep 541143 = 811715) B811715
theorem B770519 : Blo 539803 770519 := bstep (se 1 (by rfl) ⟨577889, by rfl⟩ : syracuseStep 770519 = 1155779) B1155779
theorem B541163 : Blo 539803 541163 := bstep (se 1 (by rfl) ⟨405872, by rfl⟩ : syracuseStep 541163 = 811745) B811745
theorem B541175 : Blo 539803 541175 := bstep (se 1 (by rfl) ⟨405881, by rfl⟩ : syracuseStep 541175 = 811763) B811763
theorem B541195 : Blo 539803 541195 := bstep (se 1 (by rfl) ⟨405896, by rfl⟩ : syracuseStep 541195 = 811793) B811793
theorem B4612625 : Blo 539803 4612625 := bstep (se 2 (by rfl) ⟨1729734, by rfl⟩ : syracuseStep 4612625 = 3459469) B3459469
theorem B541207 : Blo 539803 541207 := bstep (se 1 (by rfl) ⟨405905, by rfl⟩ : syracuseStep 541207 = 811811) B811811
theorem B541227 : Blo 539803 541227 := bstep (se 1 (by rfl) ⟨405920, by rfl⟩ : syracuseStep 541227 = 811841) B811841
theorem B541239 : Blo 539803 541239 := bstep (se 1 (by rfl) ⟨405929, by rfl⟩ : syracuseStep 541239 = 811859) B811859
theorem B811595 : Blo 539803 811595 := bstep (se 1 (by rfl) ⟨608696, by rfl⟩ : syracuseStep 811595 = 1217393) B1217393
theorem B541259 : Blo 539803 541259 := bstep (se 1 (by rfl) ⟨405944, by rfl⟩ : syracuseStep 541259 = 811889) B811889
theorem B811607 : Blo 539803 811607 := bstep (se 1 (by rfl) ⟨608705, by rfl⟩ : syracuseStep 811607 = 1217411) B1217411
theorem B541271 : Blo 539803 541271 := bstep (se 1 (by rfl) ⟨405953, by rfl⟩ : syracuseStep 541271 = 811907) B811907
theorem B1221209 : Blo 539803 1221209 := bstep (se 2 (by rfl) ⟨457953, by rfl⟩ : syracuseStep 1221209 = 915907) B915907
theorem B4948573 : Blo 539803 4948573 := bstep (se 3 (by rfl) ⟨927857, by rfl⟩ : syracuseStep 4948573 = 1855715) B1855715
theorem B541291 : Blo 539803 541291 := bstep (se 1 (by rfl) ⟨405968, by rfl⟩ : syracuseStep 541291 = 811937) B811937
theorem B541303 : Blo 539803 541303 := bstep (se 1 (by rfl) ⟨405977, by rfl⟩ : syracuseStep 541303 = 811955) B811955
theorem B541323 : Blo 539803 541323 := bstep (se 1 (by rfl) ⟨405992, by rfl⟩ : syracuseStep 541323 = 811985) B811985
theorem B541335 : Blo 539803 541335 := bstep (se 1 (by rfl) ⟨406001, by rfl⟩ : syracuseStep 541335 = 812003) B812003
theorem B811673 : Blo 539803 811673 := bstep (se 2 (by rfl) ⟨304377, by rfl⟩ : syracuseStep 811673 = 608755) B608755
theorem B541355 : Blo 539803 541355 := bstep (se 1 (by rfl) ⟨406016, by rfl⟩ : syracuseStep 541355 = 812033) B812033
theorem B1221299 : Blo 539803 1221299 := bstep (se 1 (by rfl) ⟨915974, by rfl⟩ : syracuseStep 1221299 = 1831949) B1831949
theorem B541367 : Blo 539803 541367 := bstep (se 1 (by rfl) ⟨406025, by rfl⟩ : syracuseStep 541367 = 812051) B812051
theorem B1827521 : Blo 539803 1827521 := bstep (se 2 (by rfl) ⟨685320, by rfl⟩ : syracuseStep 1827521 = 1370641) B1370641
theorem B541387 : Blo 539803 541387 := bstep (se 1 (by rfl) ⟨406040, by rfl⟩ : syracuseStep 541387 = 812081) B812081
theorem B541399 : Blo 539803 541399 := bstep (se 1 (by rfl) ⟨406049, by rfl⟩ : syracuseStep 541399 = 812099) B812099
theorem B541419 : Blo 539803 541419 := bstep (se 1 (by rfl) ⟨406064, by rfl⟩ : syracuseStep 541419 = 812129) B812129
theorem B16646897 : Blo 539803 16646897 := bstep (se 2 (by rfl) ⟨6242586, by rfl⟩ : syracuseStep 16646897 = 12485173) B12485173
theorem B541431 : Blo 539803 541431 := bstep (se 1 (by rfl) ⟨406073, by rfl⟩ : syracuseStep 541431 = 812147) B812147
theorem B811787 : Blo 539803 811787 := bstep (se 1 (by rfl) ⟨608840, by rfl⟩ : syracuseStep 811787 = 1217681) B1217681
theorem B541451 : Blo 539803 541451 := bstep (se 1 (by rfl) ⟨406088, by rfl⟩ : syracuseStep 541451 = 812177) B812177
theorem B811799 : Blo 539803 811799 := bstep (se 1 (by rfl) ⟨608849, by rfl⟩ : syracuseStep 811799 = 1217699) B1217699
theorem B541463 : Blo 539803 541463 := bstep (se 1 (by rfl) ⟨406097, by rfl⟩ : syracuseStep 541463 = 812195) B812195
theorem B541483 : Blo 539803 541483 := bstep (se 1 (by rfl) ⟨406112, by rfl⟩ : syracuseStep 541483 = 812225) B812225
theorem B541495 : Blo 539803 541495 := bstep (se 1 (by rfl) ⟨406121, by rfl⟩ : syracuseStep 541495 = 812243) B812243
theorem B541515 : Blo 539803 541515 := bstep (se 1 (by rfl) ⟨406136, by rfl⟩ : syracuseStep 541515 = 812273) B812273
theorem B541527 : Blo 539803 541527 := bstep (se 1 (by rfl) ⟨406145, by rfl⟩ : syracuseStep 541527 = 812291) B812291
theorem B811865 : Blo 539803 811865 := bstep (se 2 (by rfl) ⟨304449, by rfl⟩ : syracuseStep 811865 = 608899) B608899
theorem B2736989 : Blo 539803 2736989 := bstep (se 3 (by rfl) ⟨513185, by rfl⟩ : syracuseStep 2736989 = 1026371) B1026371
theorem B541547 : Blo 539803 541547 := bstep (se 1 (by rfl) ⟨406160, by rfl⟩ : syracuseStep 541547 = 812321) B812321
theorem B1024883 : Blo 539803 1024883 := bstep (se 1 (by rfl) ⟨768662, by rfl⟩ : syracuseStep 1024883 = 1537325) B1537325
theorem B541559 : Blo 539803 541559 := bstep (se 1 (by rfl) ⟨406169, by rfl⟩ : syracuseStep 541559 = 812339) B812339
theorem B541579 : Blo 539803 541579 := bstep (se 1 (by rfl) ⟨406184, by rfl⟩ : syracuseStep 541579 = 812369) B812369
theorem B1541015 : Blo 539803 1541015 := bstep (se 1 (by rfl) ⟨1155761, by rfl⟩ : syracuseStep 1541015 = 2311523) B2311523
theorem B541591 : Blo 539803 541591 := bstep (se 1 (by rfl) ⟨406193, by rfl⟩ : syracuseStep 541591 = 812387) B812387
theorem B541611 : Blo 539803 541611 := bstep (se 1 (by rfl) ⟨406208, by rfl⟩ : syracuseStep 541611 = 812417) B812417
theorem B1950637 : Blo 539803 1950637 := bstep (se 3 (by rfl) ⟨365744, by rfl⟩ : syracuseStep 1950637 = 731489) B731489
theorem B541623 : Blo 539803 541623 := bstep (se 1 (by rfl) ⟨406217, by rfl⟩ : syracuseStep 541623 = 812435) B812435
theorem B975809 : Blo 539803 975809 := bstep (se 2 (by rfl) ⟨365928, by rfl⟩ : syracuseStep 975809 = 731857) B731857
theorem B811979 : Blo 539803 811979 := bstep (se 1 (by rfl) ⟨608984, by rfl⟩ : syracuseStep 811979 = 1217969) B1217969
theorem B541643 : Blo 539803 541643 := bstep (se 1 (by rfl) ⟨406232, by rfl⟩ : syracuseStep 541643 = 812465) B812465
theorem B811991 : Blo 539803 811991 := bstep (se 1 (by rfl) ⟨608993, by rfl⟩ : syracuseStep 811991 = 1217987) B1217987
theorem B541655 : Blo 539803 541655 := bstep (se 1 (by rfl) ⟨406241, by rfl⟩ : syracuseStep 541655 = 812483) B812483
theorem B2597849 : Blo 539803 2597849 := bstep (se 2 (by rfl) ⟨974193, by rfl⟩ : syracuseStep 2597849 = 1948387) B1948387
theorem B2057177 : Blo 539803 2057177 := bstep (se 2 (by rfl) ⟨771441, by rfl⟩ : syracuseStep 2057177 = 1542883) B1542883
theorem B541675 : Blo 539803 541675 := bstep (se 1 (by rfl) ⟨406256, by rfl⟩ : syracuseStep 541675 = 812513) B812513
theorem B541687 : Blo 539803 541687 := bstep (se 1 (by rfl) ⟨406265, by rfl⟩ : syracuseStep 541687 = 812531) B812531
theorem B541707 : Blo 539803 541707 := bstep (se 1 (by rfl) ⟨406280, by rfl⟩ : syracuseStep 541707 = 812561) B812561
theorem B541719 : Blo 539803 541719 := bstep (se 1 (by rfl) ⟨406289, by rfl⟩ : syracuseStep 541719 = 812579) B812579
theorem B812057 : Blo 539803 812057 := bstep (se 2 (by rfl) ⟨304521, by rfl⟩ : syracuseStep 812057 = 609043) B609043
theorem B541739 : Blo 539803 541739 := bstep (se 1 (by rfl) ⟨406304, by rfl⟩ : syracuseStep 541739 = 812609) B812609
theorem B541751 : Blo 539803 541751 := bstep (se 1 (by rfl) ⟨406313, by rfl⟩ : syracuseStep 541751 = 812627) B812627
theorem B1369163 : Blo 539803 1369163 := bstep (se 1 (by rfl) ⟨1026872, by rfl⟩ : syracuseStep 1369163 = 2053745) B2053745
theorem B541771 : Blo 539803 541771 := bstep (se 1 (by rfl) ⟨406328, by rfl⟩ : syracuseStep 541771 = 812657) B812657
theorem B1025111 : Blo 539803 1025111 := bstep (se 1 (by rfl) ⟨768833, by rfl⟩ : syracuseStep 1025111 = 1537667) B1537667
theorem B541783 : Blo 539803 541783 := bstep (se 1 (by rfl) ⟨406337, by rfl⟩ : syracuseStep 541783 = 812675) B812675
theorem B541803 : Blo 539803 541803 := bstep (se 1 (by rfl) ⟨406352, by rfl⟩ : syracuseStep 541803 = 812705) B812705
theorem B549995 : Blo 539803 549995 := bstep (se 1 (by rfl) ⟨412496, by rfl⟩ : syracuseStep 549995 = 824993) B824993
theorem B607351 : Blo 539803 607351 := bstep (se 1 (by rfl) ⟨455513, by rfl⟩ : syracuseStep 607351 = 911027) B911027
theorem B541815 : Blo 539803 541815 := bstep (se 1 (by rfl) ⟨406361, by rfl⟩ : syracuseStep 541815 = 812723) B812723
theorem B3081347 : Blo 539803 3081347 := bstep (se 1 (by rfl) ⟨2311010, by rfl⟩ : syracuseStep 3081347 = 4622021) B4622021
theorem B812171 : Blo 539803 812171 := bstep (se 1 (by rfl) ⟨609128, by rfl⟩ : syracuseStep 812171 = 1218257) B1218257
theorem B541835 : Blo 539803 541835 := bstep (se 1 (by rfl) ⟨406376, by rfl⟩ : syracuseStep 541835 = 812753) B812753
theorem B812183 : Blo 539803 812183 := bstep (se 1 (by rfl) ⟨609137, by rfl⟩ : syracuseStep 812183 = 1218275) B1218275
theorem B541847 : Blo 539803 541847 := bstep (se 1 (by rfl) ⟨406385, by rfl⟩ : syracuseStep 541847 = 812771) B812771
theorem B541867 : Blo 539803 541867 := bstep (se 1 (by rfl) ⟨406400, by rfl⟩ : syracuseStep 541867 = 812801) B812801
theorem B1459379 : Blo 539803 1459379 := bstep (se 1 (by rfl) ⟨1094534, by rfl⟩ : syracuseStep 1459379 = 2189069) B2189069
theorem B541879 : Blo 539803 541879 := bstep (se 1 (by rfl) ⟨406409, by rfl⟩ : syracuseStep 541879 = 812819) B812819
theorem B541899 : Blo 539803 541899 := bstep (se 1 (by rfl) ⟨406424, by rfl⟩ : syracuseStep 541899 = 812849) B812849
theorem B541911 : Blo 539803 541911 := bstep (se 1 (by rfl) ⟨406433, by rfl⟩ : syracuseStep 541911 = 812867) B812867
theorem B812249 : Blo 539803 812249 := bstep (se 2 (by rfl) ⟨304593, by rfl⟩ : syracuseStep 812249 = 609187) B609187
theorem B1303769 : Blo 539803 1303769 := bstep (se 2 (by rfl) ⟨488913, by rfl⟩ : syracuseStep 1303769 = 977827) B977827
theorem B1828061 : Blo 539803 1828061 := bstep (se 3 (by rfl) ⟨342761, by rfl⟩ : syracuseStep 1828061 = 685523) B685523
theorem B541931 : Blo 539803 541931 := bstep (se 1 (by rfl) ⟨406448, by rfl⟩ : syracuseStep 541931 = 812897) B812897
theorem B541943 : Blo 539803 541943 := bstep (se 1 (by rfl) ⟨406457, by rfl⟩ : syracuseStep 541943 = 812915) B812915
theorem B32531717 : Blo 539803 32531717 := bstep (se 4 (by rfl) ⟨3049848, by rfl⟩ : syracuseStep 32531717 = 6099697) B6099697
theorem B11101445 : Blo 539803 11101445 := bstep (se 4 (by rfl) ⟨1040760, by rfl⟩ : syracuseStep 11101445 = 2081521) B2081521
theorem B541963 : Blo 539803 541963 := bstep (se 1 (by rfl) ⟨406472, by rfl⟩ : syracuseStep 541963 = 812945) B812945
theorem B541975 : Blo 539803 541975 := bstep (se 1 (by rfl) ⟨406481, by rfl⟩ : syracuseStep 541975 = 812963) B812963
theorem B607531 : Blo 539803 607531 := bstep (se 1 (by rfl) ⟨455648, by rfl⟩ : syracuseStep 607531 = 911297) B911297
theorem B541995 : Blo 539803 541995 := bstep (se 1 (by rfl) ⟨406496, by rfl⟩ : syracuseStep 541995 = 812993) B812993
theorem B542007 : Blo 539803 542007 := bstep (se 1 (by rfl) ⟨406505, by rfl⟩ : syracuseStep 542007 = 813011) B813011
theorem B550199 : Blo 539803 550199 := bstep (se 1 (by rfl) ⟨412649, by rfl⟩ : syracuseStep 550199 = 825299) B825299
theorem B2114881 : Blo 539803 2114881 := bstep (se 2 (by rfl) ⟨793080, by rfl⟩ : syracuseStep 2114881 = 1586161) B1586161
theorem B812363 : Blo 539803 812363 := bstep (se 1 (by rfl) ⟨609272, by rfl⟩ : syracuseStep 812363 = 1218545) B1218545
theorem B542027 : Blo 539803 542027 := bstep (se 1 (by rfl) ⟨406520, by rfl⟩ : syracuseStep 542027 = 813041) B813041
theorem B812375 : Blo 539803 812375 := bstep (se 1 (by rfl) ⟨609281, by rfl⟩ : syracuseStep 812375 = 1218563) B1218563
theorem B542039 : Blo 539803 542039 := bstep (se 1 (by rfl) ⟨406529, by rfl⟩ : syracuseStep 542039 = 813059) B813059
theorem B1025369 : Blo 539803 1025369 := bstep (se 2 (by rfl) ⟨384513, by rfl⟩ : syracuseStep 1025369 = 769027) B769027
theorem B542059 : Blo 539803 542059 := bstep (se 1 (by rfl) ⟨406544, by rfl⟩ : syracuseStep 542059 = 813089) B813089
theorem B542071 : Blo 539803 542071 := bstep (se 1 (by rfl) ⟨406553, by rfl⟩ : syracuseStep 542071 = 813107) B813107
theorem B542091 : Blo 539803 542091 := bstep (se 1 (by rfl) ⟨406568, by rfl⟩ : syracuseStep 542091 = 813137) B813137
theorem B607639 : Blo 539803 607639 := bstep (se 1 (by rfl) ⟨455729, by rfl⟩ : syracuseStep 607639 = 911459) B911459
theorem B3696023 : Blo 539803 3696023 := bstep (se 1 (by rfl) ⟨2772017, by rfl⟩ : syracuseStep 3696023 = 5544035) B5544035
theorem B812441 : Blo 539803 812441 := bstep (se 2 (by rfl) ⟨304665, by rfl⟩ : syracuseStep 812441 = 609331) B609331
theorem B542103 : Blo 539803 542103 := bstep (se 1 (by rfl) ⟨406577, by rfl⟩ : syracuseStep 542103 = 813155) B813155
theorem B542123 : Blo 539803 542123 := bstep (se 1 (by rfl) ⟨406592, by rfl⟩ : syracuseStep 542123 = 813185) B813185
theorem B1156531 : Blo 539803 1156531 := bstep (se 1 (by rfl) ⟨867398, by rfl⟩ : syracuseStep 1156531 = 1734797) B1734797
theorem B542135 : Blo 539803 542135 := bstep (se 1 (by rfl) ⟨406601, by rfl⟩ : syracuseStep 542135 = 813203) B813203
theorem B976321 : Blo 539803 976321 := bstep (se 2 (by rfl) ⟨366120, by rfl⟩ : syracuseStep 976321 = 732241) B732241
theorem B542155 : Blo 539803 542155 := bstep (se 1 (by rfl) ⟨406616, by rfl⟩ : syracuseStep 542155 = 813233) B813233
theorem B542167 : Blo 539803 542167 := bstep (se 1 (by rfl) ⟨406625, by rfl⟩ : syracuseStep 542167 = 813251) B813251
theorem B1738205 : Blo 539803 1738205 := bstep (se 3 (by rfl) ⟨325913, by rfl⟩ : syracuseStep 1738205 = 651827) B651827
theorem B542187 : Blo 539803 542187 := bstep (se 1 (by rfl) ⟨406640, by rfl⟩ : syracuseStep 542187 = 813281) B813281
theorem B542199 : Blo 539803 542199 := bstep (se 1 (by rfl) ⟨406649, by rfl⟩ : syracuseStep 542199 = 813299) B813299
theorem B976385 : Blo 539803 976385 := bstep (se 2 (by rfl) ⟨366144, by rfl⟩ : syracuseStep 976385 = 732289) B732289
theorem B812555 : Blo 539803 812555 := bstep (se 1 (by rfl) ⟨609416, by rfl⟩ : syracuseStep 812555 = 1218833) B1218833
theorem B542219 : Blo 539803 542219 := bstep (se 1 (by rfl) ⟨406664, by rfl⟩ : syracuseStep 542219 = 813329) B813329
theorem B3712529 : Blo 539803 3712529 := bstep (se 2 (by rfl) ⟨1392198, by rfl⟩ : syracuseStep 3712529 = 2784397) B2784397
theorem B812567 : Blo 539803 812567 := bstep (se 1 (by rfl) ⟨609425, by rfl⟩ : syracuseStep 812567 = 1218851) B1218851
theorem B542231 : Blo 539803 542231 := bstep (se 1 (by rfl) ⟨406673, by rfl⟩ : syracuseStep 542231 = 813347) B813347
theorem B542251 : Blo 539803 542251 := bstep (se 1 (by rfl) ⟨406688, by rfl⟩ : syracuseStep 542251 = 813377) B813377
theorem B542263 : Blo 539803 542263 := bstep (se 1 (by rfl) ⟨406697, by rfl⟩ : syracuseStep 542263 = 813395) B813395
theorem B607819 : Blo 539803 607819 := bstep (se 1 (by rfl) ⟨455864, by rfl⟩ : syracuseStep 607819 = 911729) B911729
theorem B542283 : Blo 539803 542283 := bstep (se 1 (by rfl) ⟨406712, by rfl⟩ : syracuseStep 542283 = 813425) B813425
theorem B730711 : Blo 539803 730711 := bstep (se 1 (by rfl) ⟨548033, by rfl⟩ : syracuseStep 730711 = 1096067) B1096067
theorem B812633 : Blo 539803 812633 := bstep (se 2 (by rfl) ⟨304737, by rfl⟩ : syracuseStep 812633 = 609475) B609475
theorem B542295 : Blo 539803 542295 := bstep (se 1 (by rfl) ⟨406721, by rfl⟩ : syracuseStep 542295 = 813443) B813443
theorem B542315 : Blo 539803 542315 := bstep (se 1 (by rfl) ⟨406736, by rfl⟩ : syracuseStep 542315 = 813473) B813473
theorem B542327 : Blo 539803 542327 := bstep (se 1 (by rfl) ⟨406745, by rfl⟩ : syracuseStep 542327 = 813491) B813491
theorem B3475075 : Blo 539803 3475075 := bstep (se 1 (by rfl) ⟨2606306, by rfl⟩ : syracuseStep 3475075 = 5212613) B5212613
theorem B542347 : Blo 539803 542347 := bstep (se 1 (by rfl) ⟨406760, by rfl⟩ : syracuseStep 542347 = 813521) B813521
theorem B542359 : Blo 539803 542359 := bstep (se 1 (by rfl) ⟨406769, by rfl⟩ : syracuseStep 542359 = 813539) B813539
theorem B542379 : Blo 539803 542379 := bstep (se 1 (by rfl) ⟨406784, by rfl⟩ : syracuseStep 542379 = 813569) B813569
theorem B607927 : Blo 539803 607927 := bstep (se 1 (by rfl) ⟨455945, by rfl⟩ : syracuseStep 607927 = 911891) B911891
theorem B542391 : Blo 539803 542391 := bstep (se 1 (by rfl) ⟨406793, by rfl⟩ : syracuseStep 542391 = 813587) B813587
theorem B1672883 : Blo 539803 1672883 := bstep (se 1 (by rfl) ⟨1254662, by rfl⟩ : syracuseStep 1672883 = 2509325) B2509325
theorem B1541825 : Blo 539803 1541825 := bstep (se 2 (by rfl) ⟨578184, by rfl⟩ : syracuseStep 1541825 = 1156369) B1156369
theorem B812747 : Blo 539803 812747 := bstep (se 1 (by rfl) ⟨609560, by rfl⟩ : syracuseStep 812747 = 1219121) B1219121
theorem B7513805 : Blo 539803 7513805 := bstep (se 3 (by rfl) ⟨1408838, by rfl⟩ : syracuseStep 7513805 = 2817677) B2817677
theorem B542411 : Blo 539803 542411 := bstep (se 1 (by rfl) ⟨406808, by rfl⟩ : syracuseStep 542411 = 813617) B813617
theorem B812759 : Blo 539803 812759 := bstep (se 1 (by rfl) ⟨609569, by rfl⟩ : syracuseStep 812759 = 1219139) B1219139
theorem B542423 : Blo 539803 542423 := bstep (se 1 (by rfl) ⟨406817, by rfl⟩ : syracuseStep 542423 = 813635) B813635
theorem B542443 : Blo 539803 542443 := bstep (se 1 (by rfl) ⟨406832, by rfl⟩ : syracuseStep 542443 = 813665) B813665
theorem B1025779 : Blo 539803 1025779 := bstep (se 1 (by rfl) ⟨769334, by rfl⟩ : syracuseStep 1025779 = 1538669) B1538669
theorem B542455 : Blo 539803 542455 := bstep (se 1 (by rfl) ⟨406841, by rfl⟩ : syracuseStep 542455 = 813683) B813683
theorem B542475 : Blo 539803 542475 := bstep (se 1 (by rfl) ⟨406856, by rfl⟩ : syracuseStep 542475 = 813713) B813713
theorem B542487 : Blo 539803 542487 := bstep (se 1 (by rfl) ⟨406865, by rfl⟩ : syracuseStep 542487 = 813731) B813731
theorem B1156889 : Blo 539803 1156889 := bstep (se 2 (by rfl) ⟨433833, by rfl⟩ : syracuseStep 1156889 = 867667) B867667
theorem B812825 : Blo 539803 812825 := bstep (se 2 (by rfl) ⟨304809, by rfl⟩ : syracuseStep 812825 = 609619) B609619
theorem B542507 : Blo 539803 542507 := bstep (se 1 (by rfl) ⟨406880, by rfl⟩ : syracuseStep 542507 = 813761) B813761
theorem B542519 : Blo 539803 542519 := bstep (se 1 (by rfl) ⟨406889, by rfl⟩ : syracuseStep 542519 = 813779) B813779
theorem B2049857 : Blo 539803 2049857 := bstep (se 2 (by rfl) ⟨768696, by rfl⟩ : syracuseStep 2049857 = 1537393) B1537393
theorem B542539 : Blo 539803 542539 := bstep (se 1 (by rfl) ⟨406904, by rfl⟩ : syracuseStep 542539 = 813809) B813809
theorem B542551 : Blo 539803 542551 := bstep (se 1 (by rfl) ⟨406913, by rfl⟩ : syracuseStep 542551 = 813827) B813827
theorem B9348965 : Blo 539803 9348965 := bstep (se 4 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 9348965 = 1752931) B1752931
theorem B608107 : Blo 539803 608107 := bstep (se 1 (by rfl) ⟨456080, by rfl⟩ : syracuseStep 608107 = 912161) B912161
theorem B542571 : Blo 539803 542571 := bstep (se 1 (by rfl) ⟨406928, by rfl⟩ : syracuseStep 542571 = 813857) B813857
theorem B542583 : Blo 539803 542583 := bstep (se 1 (by rfl) ⟨406937, by rfl⟩ : syracuseStep 542583 = 813875) B813875
theorem B911243 : Blo 539803 911243 := bstep (se 1 (by rfl) ⟨683432, by rfl⟩ : syracuseStep 911243 = 1366865) B1366865
theorem B812939 : Blo 539803 812939 := bstep (se 1 (by rfl) ⟨609704, by rfl⟩ : syracuseStep 812939 = 1219409) B1219409
theorem B542603 : Blo 539803 542603 := bstep (se 1 (by rfl) ⟨406952, by rfl⟩ : syracuseStep 542603 = 813905) B813905
theorem B812951 : Blo 539803 812951 := bstep (se 1 (by rfl) ⟨609713, by rfl⟩ : syracuseStep 812951 = 1219427) B1219427
theorem B542615 : Blo 539803 542615 := bstep (se 1 (by rfl) ⟨406961, by rfl⟩ : syracuseStep 542615 = 813923) B813923
theorem B542635 : Blo 539803 542635 := bstep (se 1 (by rfl) ⟨406976, by rfl⟩ : syracuseStep 542635 = 813953) B813953
theorem B542647 : Blo 539803 542647 := bstep (se 1 (by rfl) ⟨406985, by rfl⟩ : syracuseStep 542647 = 813971) B813971
theorem B542667 : Blo 539803 542667 := bstep (se 1 (by rfl) ⟨407000, by rfl⟩ : syracuseStep 542667 = 814001) B814001
theorem B608215 : Blo 539803 608215 := bstep (se 1 (by rfl) ⟨456161, by rfl⟩ : syracuseStep 608215 = 912323) B912323
theorem B542679 : Blo 539803 542679 := bstep (se 1 (by rfl) ⟨407009, by rfl⟩ : syracuseStep 542679 = 814019) B814019
theorem B813017 : Blo 539803 813017 := bstep (se 2 (by rfl) ⟨304881, by rfl⟩ : syracuseStep 813017 = 609763) B609763
theorem B542699 : Blo 539803 542699 := bstep (se 1 (by rfl) ⟨407024, by rfl⟩ : syracuseStep 542699 = 814049) B814049
theorem B542711 : Blo 539803 542711 := bstep (se 1 (by rfl) ⟨407033, by rfl⟩ : syracuseStep 542711 = 814067) B814067
theorem B911371 : Blo 539803 911371 := bstep (se 1 (by rfl) ⟨683528, by rfl⟩ : syracuseStep 911371 = 1367057) B1367057
theorem B542731 : Blo 539803 542731 := bstep (se 1 (by rfl) ⟨407048, by rfl⟩ : syracuseStep 542731 = 814097) B814097
theorem B2746385 : Blo 539803 2746385 := bstep (se 2 (by rfl) ⟨1029894, by rfl⟩ : syracuseStep 2746385 = 2059789) B2059789
theorem B1370135 : Blo 539803 1370135 := bstep (se 1 (by rfl) ⟨1027601, by rfl⟩ : syracuseStep 1370135 = 2055203) B2055203
theorem B542743 : Blo 539803 542743 := bstep (se 1 (by rfl) ⟨407057, by rfl⟩ : syracuseStep 542743 = 814115) B814115
theorem B542763 : Blo 539803 542763 := bstep (se 1 (by rfl) ⟨407072, by rfl⟩ : syracuseStep 542763 = 814145) B814145
theorem B542775 : Blo 539803 542775 := bstep (se 1 (by rfl) ⟨407081, by rfl⟩ : syracuseStep 542775 = 814163) B814163
theorem B813131 : Blo 539803 813131 := bstep (se 1 (by rfl) ⟨609848, by rfl⟩ : syracuseStep 813131 = 1219697) B1219697
theorem B542795 : Blo 539803 542795 := bstep (se 1 (by rfl) ⟨407096, by rfl⟩ : syracuseStep 542795 = 814193) B814193
theorem B813143 : Blo 539803 813143 := bstep (se 1 (by rfl) ⟨609857, by rfl⟩ : syracuseStep 813143 = 1219715) B1219715
theorem B7817309 : Blo 539803 7817309 := bstep (se 3 (by rfl) ⟨1465745, by rfl⟩ : syracuseStep 7817309 = 2931491) B2931491
theorem B1214603 : Blo 539803 1214603 := bstep (se 1 (by rfl) ⟨910952, by rfl⟩ : syracuseStep 1214603 = 1821905) B1821905
theorem B608395 : Blo 539803 608395 := bstep (se 1 (by rfl) ⟨456296, by rfl⟩ : syracuseStep 608395 = 912593) B912593
theorem B977035 : Blo 539803 977035 := bstep (se 1 (by rfl) ⟨732776, by rfl⟩ : syracuseStep 977035 = 1465553) B1465553
theorem B911513 : Blo 539803 911513 := bstep (se 2 (by rfl) ⟨341817, by rfl⟩ : syracuseStep 911513 = 683635) B683635
theorem B813209 : Blo 539803 813209 := bstep (se 2 (by rfl) ⟨304953, by rfl⟩ : syracuseStep 813209 = 609907) B609907
theorem B3909809 : Blo 539803 3909809 := bstep (se 2 (by rfl) ⟨1466178, by rfl⟩ : syracuseStep 3909809 = 2932357) B2932357
theorem B2746547 : Blo 539803 2746547 := bstep (se 1 (by rfl) ⟨2059910, by rfl⟩ : syracuseStep 2746547 = 4119821) B4119821
theorem B1214657 : Blo 539803 1214657 := bstep (se 2 (by rfl) ⟨455496, by rfl⟩ : syracuseStep 1214657 = 910993) B910993
theorem B739531 : Blo 539803 739531 := bstep (se 1 (by rfl) ⟨554648, by rfl⟩ : syracuseStep 739531 = 1109297) B1109297
theorem B1026265 : Blo 539803 1026265 := bstep (se 2 (by rfl) ⟨384849, by rfl⟩ : syracuseStep 1026265 = 769699) B769699
theorem B608503 : Blo 539803 608503 := bstep (se 1 (by rfl) ⟨456377, by rfl⟩ : syracuseStep 608503 = 912755) B912755
theorem B813323 : Blo 539803 813323 := bstep (se 1 (by rfl) ⟨609992, by rfl⟩ : syracuseStep 813323 = 1219985) B1219985
theorem B813335 : Blo 539803 813335 := bstep (se 1 (by rfl) ⟨610001, by rfl⟩ : syracuseStep 813335 = 1220003) B1220003
theorem B911641 : Blo 539803 911641 := bstep (se 2 (by rfl) ⟨341865, by rfl⟩ : syracuseStep 911641 = 683731) B683731
theorem B1829195 : Blo 539803 1829195 := bstep (se 1 (by rfl) ⟨1371896, by rfl⟩ : syracuseStep 1829195 = 2743793) B2743793
theorem B813401 : Blo 539803 813401 := bstep (se 2 (by rfl) ⟨305025, by rfl⟩ : syracuseStep 813401 = 610051) B610051
theorem B1214873 : Blo 539803 1214873 := bstep (se 2 (by rfl) ⟨455577, by rfl⟩ : syracuseStep 1214873 = 911155) B911155
theorem B608683 : Blo 539803 608683 := bstep (se 1 (by rfl) ⟨456512, by rfl⟩ : syracuseStep 608683 = 913025) B913025
theorem B4622771 : Blo 539803 4622771 := bstep (se 1 (by rfl) ⟨3467078, by rfl⟩ : syracuseStep 4622771 = 6934157) B6934157
theorem B2312651 : Blo 539803 2312651 := bstep (se 1 (by rfl) ⟨1734488, by rfl⟩ : syracuseStep 2312651 = 3468977) B3468977
theorem B813515 : Blo 539803 813515 := bstep (se 1 (by rfl) ⟨610136, by rfl⟩ : syracuseStep 813515 = 1220273) B1220273
theorem B813527 : Blo 539803 813527 := bstep (se 1 (by rfl) ⟨610145, by rfl⟩ : syracuseStep 813527 = 1220291) B1220291
theorem B1214963 : Blo 539803 1214963 := bstep (se 1 (by rfl) ⟨911222, by rfl⟩ : syracuseStep 1214963 = 1822445) B1822445
theorem B3893777 : Blo 539803 3893777 := bstep (se 2 (by rfl) ⟨1460166, by rfl⟩ : syracuseStep 3893777 = 2920333) B2920333
theorem B4114961 : Blo 539803 4114961 := bstep (se 2 (by rfl) ⟨1543110, by rfl⟩ : syracuseStep 4114961 = 3086221) B3086221
theorem B1214999 : Blo 539803 1214999 := bstep (se 1 (by rfl) ⟨911249, by rfl⟩ : syracuseStep 1214999 = 1822499) B1822499
theorem B608791 : Blo 539803 608791 := bstep (se 1 (by rfl) ⟨456593, by rfl⟩ : syracuseStep 608791 = 913187) B913187
theorem B813593 : Blo 539803 813593 := bstep (se 2 (by rfl) ⟨305097, by rfl⟩ : syracuseStep 813593 = 610195) B610195
theorem B2058803 : Blo 539803 2058803 := bstep (se 1 (by rfl) ⟨1544102, by rfl⟩ : syracuseStep 2058803 = 3088205) B3088205
theorem B2058817 : Blo 539803 2058817 := bstep (se 2 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 2058817 = 1544113) B1544113
theorem B8792651 : Blo 539803 8792651 := bstep (se 1 (by rfl) ⟨6594488, by rfl⟩ : syracuseStep 8792651 = 13188977) B13188977
theorem B1829465 : Blo 539803 1829465 := bstep (se 2 (by rfl) ⟨686049, by rfl⟩ : syracuseStep 1829465 = 1372099) B1372099
theorem B3902053 : Blo 539803 3902053 := bstep (se 4 (by rfl) ⟨365817, by rfl⟩ : syracuseStep 3902053 = 731635) B731635
theorem B2960003 : Blo 539803 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B2468483 : Blo 539803 2468483 := bstep (se 1 (by rfl) ⟨1851362, by rfl⟩ : syracuseStep 2468483 = 3702725) B3702725
theorem B813707 : Blo 539803 813707 := bstep (se 1 (by rfl) ⟨610280, by rfl⟩ : syracuseStep 813707 = 1220561) B1220561
theorem B813719 : Blo 539803 813719 := bstep (se 1 (by rfl) ⟨610289, by rfl⟩ : syracuseStep 813719 = 1220579) B1220579
theorem B1370803 : Blo 539803 1370803 := bstep (se 1 (by rfl) ⟨1028102, by rfl⟩ : syracuseStep 1370803 = 2056205) B2056205
theorem B1215179 : Blo 539803 1215179 := bstep (se 1 (by rfl) ⟨911384, by rfl⟩ : syracuseStep 1215179 = 1822769) B1822769
theorem B608971 : Blo 539803 608971 := bstep (se 1 (by rfl) ⟨456728, by rfl⟩ : syracuseStep 608971 = 913457) B913457
theorem B1043147 : Blo 539803 1043147 := bstep (se 1 (by rfl) ⟨782360, by rfl⟩ : syracuseStep 1043147 = 1564721) B1564721
theorem B813785 : Blo 539803 813785 := bstep (se 2 (by rfl) ⟨305169, by rfl⟩ : syracuseStep 813785 = 610339) B610339
theorem B1215233 : Blo 539803 1215233 := bstep (se 2 (by rfl) ⟨455712, by rfl⟩ : syracuseStep 1215233 = 911425) B911425
theorem B1026827 : Blo 539803 1026827 := bstep (se 1 (by rfl) ⟨770120, by rfl⟩ : syracuseStep 1026827 = 1540241) B1540241
theorem B609079 : Blo 539803 609079 := bstep (se 1 (by rfl) ⟨456809, by rfl⟩ : syracuseStep 609079 = 913619) B913619
theorem B1370945 : Blo 539803 1370945 := bstep (se 2 (by rfl) ⟨514104, by rfl⟩ : syracuseStep 1370945 = 1028209) B1028209
theorem B813899 : Blo 539803 813899 := bstep (se 1 (by rfl) ⟨610424, by rfl⟩ : syracuseStep 813899 = 1220849) B1220849
theorem B912215 : Blo 539803 912215 := bstep (se 1 (by rfl) ⟨684161, by rfl⟩ : syracuseStep 912215 = 1368323) B1368323
theorem B813911 : Blo 539803 813911 := bstep (se 1 (by rfl) ⟨610433, by rfl⟩ : syracuseStep 813911 = 1220867) B1220867
theorem B9849701 : Blo 539803 9849701 := bstep (se 4 (by rfl) ⟨923409, by rfl⟩ : syracuseStep 9849701 = 1846819) B1846819
theorem B2739095 : Blo 539803 2739095 := bstep (se 1 (by rfl) ⟨2054321, by rfl⟩ : syracuseStep 2739095 = 4108643) B4108643
theorem B2198423 : Blo 539803 2198423 := bstep (se 1 (by rfl) ⟨1648817, by rfl⟩ : syracuseStep 2198423 = 3297635) B3297635
theorem B813977 : Blo 539803 813977 := bstep (se 2 (by rfl) ⟨305241, by rfl⟩ : syracuseStep 813977 = 610483) B610483
theorem B4107185 : Blo 539803 4107185 := bstep (se 2 (by rfl) ⟨1540194, by rfl⟩ : syracuseStep 4107185 = 3080389) B3080389
theorem B1027009 : Blo 539803 1027009 := bstep (se 2 (by rfl) ⟨385128, by rfl⟩ : syracuseStep 1027009 = 770257) B770257
theorem B912343 : Blo 539803 912343 := bstep (se 1 (by rfl) ⟨684257, by rfl⟩ : syracuseStep 912343 = 1368515) B1368515
theorem B617431 : Blo 539803 617431 := bstep (se 1 (by rfl) ⟨463073, by rfl⟩ : syracuseStep 617431 = 926147) B926147
theorem B1215449 : Blo 539803 1215449 := bstep (se 2 (by rfl) ⟨455793, by rfl⟩ : syracuseStep 1215449 = 911587) B911587
theorem B822233 : Blo 539803 822233 := bstep (se 2 (by rfl) ⟨308337, by rfl⟩ : syracuseStep 822233 = 616675) B616675
theorem B609259 : Blo 539803 609259 := bstep (se 1 (by rfl) ⟨456944, by rfl⟩ : syracuseStep 609259 = 913889) B913889
theorem B814091 : Blo 539803 814091 := bstep (se 1 (by rfl) ⟨610568, by rfl⟩ : syracuseStep 814091 = 1221137) B1221137
theorem B814103 : Blo 539803 814103 := bstep (se 1 (by rfl) ⟨610577, by rfl⟩ : syracuseStep 814103 = 1221155) B1221155
theorem B1215539 : Blo 539803 1215539 := bstep (se 1 (by rfl) ⟨911654, by rfl⟩ : syracuseStep 1215539 = 1823309) B1823309
theorem B15199301 : Blo 539803 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B1485899 : Blo 539803 1485899 := bstep (se 1 (by rfl) ⟨1114424, by rfl⟩ : syracuseStep 1485899 = 2228849) B2228849
theorem B1215575 : Blo 539803 1215575 := bstep (se 1 (by rfl) ⟨911681, by rfl⟩ : syracuseStep 1215575 = 1823363) B1823363
theorem B609367 : Blo 539803 609367 := bstep (se 1 (by rfl) ⟨457025, by rfl⟩ : syracuseStep 609367 = 914051) B914051
theorem B814169 : Blo 539803 814169 := bstep (se 2 (by rfl) ⟨305313, by rfl⟩ : syracuseStep 814169 = 610627) B610627
theorem B2608307 : Blo 539803 2608307 := bstep (se 1 (by rfl) ⟨1956230, by rfl⟩ : syracuseStep 2608307 = 3912461) B3912461
theorem B576715 : Blo 539803 576715 := bstep (se 1 (by rfl) ⟨432536, by rfl⟩ : syracuseStep 576715 = 865073) B865073
theorem B3460313 : Blo 539803 3460313 := bstep (se 2 (by rfl) ⟨1297617, by rfl⟩ : syracuseStep 3460313 = 2595235) B2595235
theorem B1215755 : Blo 539803 1215755 := bstep (se 1 (by rfl) ⟨911816, by rfl⟩ : syracuseStep 1215755 = 1823633) B1823633
theorem B609547 : Blo 539803 609547 := bstep (se 1 (by rfl) ⟨457160, by rfl⟩ : syracuseStep 609547 = 914321) B914321
theorem B2051345 : Blo 539803 2051345 := bstep (se 2 (by rfl) ⟨769254, by rfl⟩ : syracuseStep 2051345 = 1538509) B1538509
theorem B1830167 : Blo 539803 1830167 := bstep (se 1 (by rfl) ⟨1372625, by rfl⟩ : syracuseStep 1830167 = 2745251) B2745251
theorem B1543475 : Blo 539803 1543475 := bstep (se 1 (by rfl) ⟨1157606, by rfl⟩ : syracuseStep 1543475 = 2315213) B2315213
theorem B1215809 : Blo 539803 1215809 := bstep (se 2 (by rfl) ⟨455928, by rfl⟩ : syracuseStep 1215809 = 911857) B911857
theorem B1559873 : Blo 539803 1559873 := bstep (se 2 (by rfl) ⟨584952, by rfl⟩ : syracuseStep 1559873 = 1169905) B1169905
theorem B1543499 : Blo 539803 1543499 := bstep (se 1 (by rfl) ⟨1157624, by rfl⟩ : syracuseStep 1543499 = 2315249) B2315249
theorem B609655 : Blo 539803 609655 := bstep (se 1 (by rfl) ⟨457241, by rfl⟩ : syracuseStep 609655 = 914483) B914483
theorem B4107671 : Blo 539803 4107671 := bstep (se 1 (by rfl) ⟨3080753, by rfl⟩ : syracuseStep 4107671 = 6161507) B6161507
theorem B1642007 : Blo 539803 1642007 := bstep (se 1 (by rfl) ⟨1231505, by rfl⟩ : syracuseStep 1642007 = 2463011) B2463011
theorem B1216025 : Blo 539803 1216025 := bstep (se 2 (by rfl) ⟨456009, by rfl⟩ : syracuseStep 1216025 = 912019) B912019
theorem B5205539 : Blo 539803 5205539 := bstep (se 1 (by rfl) ⟨3904154, by rfl⟩ : syracuseStep 5205539 = 7808309) B7808309
theorem B609835 : Blo 539803 609835 := bstep (se 1 (by rfl) ⟨457376, by rfl⟩ : syracuseStep 609835 = 914753) B914753
theorem B1822283 : Blo 539803 1822283 := bstep (se 1 (by rfl) ⟨1366712, by rfl⟩ : syracuseStep 1822283 = 2733425) B2733425
theorem B912971 : Blo 539803 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B5557835 : Blo 539803 5557835 := bstep (se 1 (by rfl) ⟨4168376, by rfl⟩ : syracuseStep 5557835 = 8336753) B8336753
theorem B1216115 : Blo 539803 1216115 := bstep (se 1 (by rfl) ⟨912086, by rfl⟩ : syracuseStep 1216115 = 1824173) B1824173
theorem B577163 : Blo 539803 577163 := bstep (se 1 (by rfl) ⟨432872, by rfl⟩ : syracuseStep 577163 = 865745) B865745
theorem B1027723 : Blo 539803 1027723 := bstep (se 1 (by rfl) ⟨770792, by rfl⟩ : syracuseStep 1027723 = 1541585) B1541585
theorem B1216151 : Blo 539803 1216151 := bstep (se 1 (by rfl) ⟨912113, by rfl⟩ : syracuseStep 1216151 = 1824227) B1824227
theorem B609943 : Blo 539803 609943 := bstep (se 1 (by rfl) ⟨457457, by rfl⟩ : syracuseStep 609943 = 914915) B914915
theorem B1298099 : Blo 539803 1298099 := bstep (se 1 (by rfl) ⟨973574, by rfl⟩ : syracuseStep 1298099 = 1947149) B1947149
theorem B7786165 : Blo 539803 7786165 := bstep (se 5 (by rfl) ⟨364976, by rfl⟩ : syracuseStep 7786165 = 729953) B729953
theorem B913099 : Blo 539803 913099 := bstep (se 1 (by rfl) ⟨684824, by rfl⟩ : syracuseStep 913099 = 1369649) B1369649
theorem B1027799 : Blo 539803 1027799 := bstep (se 1 (by rfl) ⟨770849, by rfl⟩ : syracuseStep 1027799 = 1541699) B1541699
theorem B2051801 : Blo 539803 2051801 := bstep (se 2 (by rfl) ⟨769425, by rfl⟩ : syracuseStep 2051801 = 1538851) B1538851
theorem B1158923 : Blo 539803 1158923 := bstep (se 1 (by rfl) ⟨869192, by rfl⟩ : syracuseStep 1158923 = 1738385) B1738385
theorem B1830707 : Blo 539803 1830707 := bstep (se 1 (by rfl) ⟨1373030, by rfl⟩ : syracuseStep 1830707 = 2746061) B2746061
theorem B1216331 : Blo 539803 1216331 := bstep (se 1 (by rfl) ⟨912248, by rfl⟩ : syracuseStep 1216331 = 1824497) B1824497
theorem B610123 : Blo 539803 610123 := bstep (se 1 (by rfl) ⟨457592, by rfl⟩ : syracuseStep 610123 = 915185) B915185
theorem B1822553 : Blo 539803 1822553 := bstep (se 2 (by rfl) ⟨683457, by rfl⟩ : syracuseStep 1822553 = 1366915) B1366915
theorem B913241 : Blo 539803 913241 := bstep (se 2 (by rfl) ⟨342465, by rfl⟩ : syracuseStep 913241 = 684931) B684931
theorem B3518309 : Blo 539803 3518309 := bstep (se 4 (by rfl) ⟨329841, by rfl⟩ : syracuseStep 3518309 = 659683) B659683
theorem B1216385 : Blo 539803 1216385 := bstep (se 2 (by rfl) ⟨456144, by rfl⟩ : syracuseStep 1216385 = 912289) B912289
theorem B1044377 : Blo 539803 1044377 := bstep (se 2 (by rfl) ⟨391641, by rfl⟩ : syracuseStep 1044377 = 783283) B783283
theorem B2052013 : Blo 539803 2052013 := bstep (se 3 (by rfl) ⟨384752, by rfl⟩ : syracuseStep 2052013 = 769505) B769505
theorem B610231 : Blo 539803 610231 := bstep (se 1 (by rfl) ⟨457673, by rfl⟩ : syracuseStep 610231 = 915347) B915347
theorem B913369 : Blo 539803 913369 := bstep (se 2 (by rfl) ⟨342513, by rfl⟩ : syracuseStep 913369 = 685027) B685027
theorem B684055 : Blo 539803 684055 := bstep (se 1 (by rfl) ⟨513041, by rfl⟩ : syracuseStep 684055 = 1026083) B1026083
theorem B2314291 : Blo 539803 2314291 := bstep (se 1 (by rfl) ⟨1735718, by rfl⟩ : syracuseStep 2314291 = 3471437) B3471437
theorem B1372211 : Blo 539803 1372211 := bstep (se 1 (by rfl) ⟨1029158, by rfl⟩ : syracuseStep 1372211 = 2058317) B2058317
theorem B1830977 : Blo 539803 1830977 := bstep (se 2 (by rfl) ⟨686616, by rfl⟩ : syracuseStep 1830977 = 1373233) B1373233
theorem B1216601 : Blo 539803 1216601 := bstep (se 2 (by rfl) ⟨456225, by rfl⟩ : syracuseStep 1216601 = 912451) B912451
theorem B5009501 : Blo 539803 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B1544285 : Blo 539803 1544285 := bstep (se 3 (by rfl) ⟨289553, by rfl⟩ : syracuseStep 1544285 = 579107) B579107
theorem B610411 : Blo 539803 610411 := bstep (se 1 (by rfl) ⟨457808, by rfl⟩ : syracuseStep 610411 = 915617) B915617
theorem B2961559 : Blo 539803 2961559 := bstep (se 1 (by rfl) ⟨2221169, by rfl⟩ : syracuseStep 2961559 = 4442339) B4442339
theorem B11260055 : Blo 539803 11260055 := bstep (se 1 (by rfl) ⟨8445041, by rfl⟩ : syracuseStep 11260055 = 16890083) B16890083
theorem B3174551 : Blo 539803 3174551 := bstep (se 1 (by rfl) ⟨2380913, by rfl⟩ : syracuseStep 3174551 = 4761827) B4761827
theorem B1216691 : Blo 539803 1216691 := bstep (se 1 (by rfl) ⟨912518, by rfl⟩ : syracuseStep 1216691 = 1825037) B1825037
theorem B1216727 : Blo 539803 1216727 := bstep (se 1 (by rfl) ⟨912545, by rfl⟩ : syracuseStep 1216727 = 1825091) B1825091
theorem B2052317 : Blo 539803 2052317 := bstep (se 3 (by rfl) ⟨384809, by rfl⟩ : syracuseStep 2052317 = 769619) B769619
theorem B610519 : Blo 539803 610519 := bstep (se 1 (by rfl) ⟨457889, by rfl⟩ : syracuseStep 610519 = 915779) B915779
theorem B5189933 : Blo 539803 5189933 := bstep (se 3 (by rfl) ⟨973112, by rfl⟩ : syracuseStep 5189933 = 1946225) B1946225
theorem B4624685 : Blo 539803 4624685 := bstep (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) B1734257
theorem B1855795 : Blo 539803 1855795 := bstep (se 1 (by rfl) ⟨1391846, by rfl⟩ : syracuseStep 1855795 = 2783693) B2783693
theorem B676171 : Blo 539803 676171 := bstep (se 1 (by rfl) ⟨507128, by rfl⟩ : syracuseStep 676171 = 1014257) B1014257
theorem B2199883 : Blo 539803 2199883 := bstep (se 1 (by rfl) ⟨1649912, by rfl⟩ : syracuseStep 2199883 = 3299825) B3299825
theorem B1028467 : Blo 539803 1028467 := bstep (se 1 (by rfl) ⟨771350, by rfl⟩ : syracuseStep 1028467 = 1542701) B1542701
theorem B1216907 : Blo 539803 1216907 := bstep (se 1 (by rfl) ⟨912680, by rfl⟩ : syracuseStep 1216907 = 1825361) B1825361
theorem B1733015 : Blo 539803 1733015 := bstep (se 1 (by rfl) ⟨1299761, by rfl⟩ : syracuseStep 1733015 = 2599523) B2599523
theorem B1216961 : Blo 539803 1216961 := bstep (se 2 (by rfl) ⟨456360, by rfl⟩ : syracuseStep 1216961 = 912721) B912721
theorem B2060747 : Blo 539803 2060747 := bstep (se 1 (by rfl) ⟨1545560, by rfl⟩ : syracuseStep 2060747 = 3091121) B3091121
theorem B2060761 : Blo 539803 2060761 := bstep (se 2 (by rfl) ⟨772785, by rfl⟩ : syracuseStep 2060761 = 1545571) B1545571
theorem B4682245 : Blo 539803 4682245 := bstep (se 4 (by rfl) ⟨438960, by rfl⟩ : syracuseStep 4682245 = 877921) B877921
theorem B1823255 : Blo 539803 1823255 := bstep (se 1 (by rfl) ⟨1367441, by rfl⟩ : syracuseStep 1823255 = 2734883) B2734883
theorem B913943 : Blo 539803 913943 := bstep (se 1 (by rfl) ⟨685457, by rfl⟩ : syracuseStep 913943 = 1370915) B1370915
theorem B1372747 : Blo 539803 1372747 := bstep (se 1 (by rfl) ⟨1029560, by rfl⟩ : syracuseStep 1372747 = 2059121) B2059121
theorem B1028695 : Blo 539803 1028695 := bstep (se 1 (by rfl) ⟨771521, by rfl⟩ : syracuseStep 1028695 = 1543043) B1543043
theorem B1831517 : Blo 539803 1831517 := bstep (se 3 (by rfl) ⟨343409, by rfl⟩ : syracuseStep 1831517 = 686819) B686819
theorem B914071 : Blo 539803 914071 := bstep (se 1 (by rfl) ⟨685553, by rfl⟩ : syracuseStep 914071 = 1371107) B1371107
theorem B1217177 : Blo 539803 1217177 := bstep (se 2 (by rfl) ⟨456441, by rfl⟩ : syracuseStep 1217177 = 912883) B912883
theorem B2314925 : Blo 539803 2314925 := bstep (se 3 (by rfl) ⟨434048, by rfl⟩ : syracuseStep 2314925 = 868097) B868097
theorem B1028801 : Blo 539803 1028801 := bstep (se 2 (by rfl) ⟨385800, by rfl⟩ : syracuseStep 1028801 = 771601) B771601
theorem B1233623 : Blo 539803 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B1372889 : Blo 539803 1372889 := bstep (se 2 (by rfl) ⟨514833, by rfl⟩ : syracuseStep 1372889 = 1029667) B1029667
theorem B1217267 : Blo 539803 1217267 := bstep (se 1 (by rfl) ⟨912950, by rfl⟩ : syracuseStep 1217267 = 1825901) B1825901
theorem B1217303 : Blo 539803 1217303 := bstep (se 1 (by rfl) ⟨912977, by rfl⟩ : syracuseStep 1217303 = 1825955) B1825955
theorem B578359 : Blo 539803 578359 := bstep (se 1 (by rfl) ⟨433769, by rfl⟩ : syracuseStep 578359 = 867539) B867539
theorem B3461953 : Blo 539803 3461953 := bstep (se 2 (by rfl) ⟨1298232, by rfl⟩ : syracuseStep 3461953 = 2596465) B2596465
theorem B684875 : Blo 539803 684875 := bstep (se 1 (by rfl) ⟨513656, by rfl⟩ : syracuseStep 684875 = 1027313) B1027313
theorem B1028953 : Blo 539803 1028953 := bstep (se 2 (by rfl) ⟨385857, by rfl⟩ : syracuseStep 1028953 = 771715) B771715
theorem B6943589 : Blo 539803 6943589 := bstep (se 4 (by rfl) ⟨650961, by rfl⟩ : syracuseStep 6943589 = 1301923) B1301923
theorem B1217483 : Blo 539803 1217483 := bstep (se 1 (by rfl) ⟨913112, by rfl⟩ : syracuseStep 1217483 = 1826225) B1826225
theorem B4625369 : Blo 539803 4625369 := bstep (se 2 (by rfl) ⟨1734513, by rfl⟩ : syracuseStep 4625369 = 3469027) B3469027
theorem B578539 : Blo 539803 578539 := bstep (se 1 (by rfl) ⟨433904, by rfl⟩ : syracuseStep 578539 = 867809) B867809
theorem B1217537 : Blo 539803 1217537 := bstep (se 2 (by rfl) ⟨456576, by rfl⟩ : syracuseStep 1217537 = 913153) B913153
theorem B2733101 : Blo 539803 2733101 := bstep (se 3 (by rfl) ⟨512456, by rfl⟩ : syracuseStep 2733101 = 1024913) B1024913
theorem B1823795 : Blo 539803 1823795 := bstep (se 1 (by rfl) ⟨1367846, by rfl⟩ : syracuseStep 1823795 = 2735693) B2735693
theorem B3126347 : Blo 539803 3126347 := bstep (se 1 (by rfl) ⟨2344760, by rfl⟩ : syracuseStep 3126347 = 4689521) B4689521
theorem B2307217 : Blo 539803 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B3290291 : Blo 539803 3290291 := bstep (se 1 (by rfl) ⟨2467718, by rfl⟩ : syracuseStep 3290291 = 4935437) B4935437
theorem B1217753 : Blo 539803 1217753 := bstep (se 2 (by rfl) ⟨456657, by rfl⟩ : syracuseStep 1217753 = 913315) B913315
theorem B914699 : Blo 539803 914699 := bstep (se 1 (by rfl) ⟨686024, by rfl⟩ : syracuseStep 914699 = 1372049) B1372049
theorem B1217843 : Blo 539803 1217843 := bstep (se 1 (by rfl) ⟨913382, by rfl⟩ : syracuseStep 1217843 = 1826765) B1826765
theorem B1824065 : Blo 539803 1824065 := bstep (se 2 (by rfl) ⟨684024, by rfl⟩ : syracuseStep 1824065 = 1368049) B1368049
theorem B1217879 : Blo 539803 1217879 := bstep (se 1 (by rfl) ⟨913409, by rfl⟩ : syracuseStep 1217879 = 1826819) B1826819
theorem B914827 : Blo 539803 914827 := bstep (se 1 (by rfl) ⟨686120, by rfl⟩ : syracuseStep 914827 = 1372241) B1372241
theorem B4634117 : Blo 539803 4634117 := bstep (se 4 (by rfl) ⟨434448, by rfl⟩ : syracuseStep 4634117 = 868897) B868897
theorem B1218059 : Blo 539803 1218059 := bstep (se 1 (by rfl) ⟨913544, by rfl⟩ : syracuseStep 1218059 = 1827089) B1827089
theorem B685579 : Blo 539803 685579 := bstep (se 1 (by rfl) ⟨514184, by rfl⟩ : syracuseStep 685579 = 1028369) B1028369
theorem B1144343 : Blo 539803 1144343 := bstep (se 1 (by rfl) ⟨858257, by rfl⟩ : syracuseStep 1144343 = 1716515) B1716515
theorem B587287 : Blo 539803 587287 := bstep (se 1 (by rfl) ⟨440465, by rfl⟩ : syracuseStep 587287 = 880931) B880931
theorem B914969 : Blo 539803 914969 := bstep (se 2 (by rfl) ⟨343113, by rfl⟩ : syracuseStep 914969 = 686227) B686227
theorem B1373719 : Blo 539803 1373719 := bstep (se 1 (by rfl) ⟨1030289, by rfl⟩ : syracuseStep 1373719 = 2060579) B2060579
theorem B4396589 : Blo 539803 4396589 := bstep (se 3 (by rfl) ⟨824360, by rfl⟩ : syracuseStep 4396589 = 1648721) B1648721
theorem B1218113 : Blo 539803 1218113 := bstep (se 2 (by rfl) ⟨456792, by rfl⟩ : syracuseStep 1218113 = 913585) B913585
theorem B35599985 : Blo 539803 35599985 := bstep (se 2 (by rfl) ⟨13349994, by rfl⟩ : syracuseStep 35599985 = 26699989) B26699989
theorem B915097 : Blo 539803 915097 := bstep (se 2 (by rfl) ⟨343161, by rfl⟩ : syracuseStep 915097 = 686323) B686323
theorem B2086603 : Blo 539803 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B2193169 : Blo 539803 2193169 := bstep (se 2 (by rfl) ⟨822438, by rfl⟩ : syracuseStep 2193169 = 1644877) B1644877
theorem B685847 : Blo 539803 685847 := bstep (se 1 (by rfl) ⟨514385, by rfl⟩ : syracuseStep 685847 = 1028771) B1028771
theorem B1095449 : Blo 539803 1095449 := bstep (se 2 (by rfl) ⟨410793, by rfl⟩ : syracuseStep 1095449 = 821587) B821587
theorem B1218329 : Blo 539803 1218329 := bstep (se 2 (by rfl) ⟨456873, by rfl⟩ : syracuseStep 1218329 = 913747) B913747
theorem B1824605 : Blo 539803 1824605 := bstep (se 3 (by rfl) ⟨342113, by rfl⟩ : syracuseStep 1824605 = 684227) B684227
theorem B1152883 : Blo 539803 1152883 := bstep (se 1 (by rfl) ⟨864662, by rfl⟩ : syracuseStep 1152883 = 1729325) B1729325
theorem B1218419 : Blo 539803 1218419 := bstep (se 1 (by rfl) ⟨913814, by rfl⟩ : syracuseStep 1218419 = 1827629) B1827629
theorem B1218455 : Blo 539803 1218455 := bstep (se 1 (by rfl) ⟨913841, by rfl⟩ : syracuseStep 1218455 = 1827683) B1827683
theorem B1538099 : Blo 539803 1538099 := bstep (se 1 (by rfl) ⟨1153574, by rfl⟩ : syracuseStep 1538099 = 2307149) B2307149
theorem B1300531 : Blo 539803 1300531 := bstep (se 1 (by rfl) ⟨975398, by rfl⟩ : syracuseStep 1300531 = 1950797) B1950797
theorem B1218635 : Blo 539803 1218635 := bstep (se 1 (by rfl) ⟨913976, by rfl⟩ : syracuseStep 1218635 = 1827953) B1827953
theorem B1030259 : Blo 539803 1030259 := bstep (se 1 (by rfl) ⟨772694, by rfl⟩ : syracuseStep 1030259 = 1545389) B1545389
theorem B1218689 : Blo 539803 1218689 := bstep (se 2 (by rfl) ⟨457008, by rfl⟩ : syracuseStep 1218689 = 914017) B914017
theorem B915671 : Blo 539803 915671 := bstep (se 1 (by rfl) ⟨686753, by rfl⟩ : syracuseStep 915671 = 1373507) B1373507
theorem B1030411 : Blo 539803 1030411 := bstep (se 1 (by rfl) ⟨772808, by rfl⟩ : syracuseStep 1030411 = 1545617) B1545617
theorem B1538327 : Blo 539803 1538327 := bstep (se 1 (by rfl) ⟨1153745, by rfl⟩ : syracuseStep 1538327 = 2307491) B2307491
theorem B2283821 : Blo 539803 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B4118849 : Blo 539803 4118849 := bstep (se 2 (by rfl) ⟨1544568, by rfl⟩ : syracuseStep 4118849 = 3089137) B3089137
theorem B1153369 : Blo 539803 1153369 := bstep (se 2 (by rfl) ⟨432513, by rfl⟩ : syracuseStep 1153369 = 865027) B865027
theorem B1218905 : Blo 539803 1218905 := bstep (se 2 (by rfl) ⟨457089, by rfl⟩ : syracuseStep 1218905 = 914179) B914179
theorem B915799 : Blo 539803 915799 := bstep (se 1 (by rfl) ⟨686849, by rfl⟩ : syracuseStep 915799 = 1373699) B1373699
theorem B2742659 : Blo 539803 2742659 := bstep (se 1 (by rfl) ⟨2056994, by rfl⟩ : syracuseStep 2742659 = 4113989) B4113989
theorem B866713 : Blo 539803 866713 := bstep (se 2 (by rfl) ⟨325017, by rfl⟩ : syracuseStep 866713 = 650035) B650035
theorem B1218995 : Blo 539803 1218995 := bstep (se 1 (by rfl) ⟨914246, by rfl⟩ : syracuseStep 1218995 = 1828493) B1828493
theorem B1219031 : Blo 539803 1219031 := bstep (se 1 (by rfl) ⟨914273, by rfl⟩ : syracuseStep 1219031 = 1828547) B1828547
theorem B686551 : Blo 539803 686551 := bstep (se 1 (by rfl) ⟨514913, by rfl⟩ : syracuseStep 686551 = 1029827) B1029827
theorem B2259479 : Blo 539803 2259479 := bstep (se 1 (by rfl) ⟨1694609, by rfl⟩ : syracuseStep 2259479 = 3389219) B3389219
theorem B1538635 : Blo 539803 1538635 := bstep (se 1 (by rfl) ⟨1153976, by rfl⟩ : syracuseStep 1538635 = 2307953) B2307953
theorem B3078749 : Blo 539803 3078749 := bstep (se 3 (by rfl) ⟨577265, by rfl⟩ : syracuseStep 3078749 = 1154531) B1154531
theorem B2341469 : Blo 539803 2341469 := bstep (se 3 (by rfl) ⟨439025, by rfl⟩ : syracuseStep 2341469 = 878051) B878051
theorem B7494275 : Blo 539803 7494275 := bstep (se 1 (by rfl) ⟨5620706, by rfl⟩ : syracuseStep 7494275 = 11241413) B11241413
theorem B1219211 : Blo 539803 1219211 := bstep (se 1 (by rfl) ⟨914408, by rfl⟩ : syracuseStep 1219211 = 1828817) B1828817
theorem B1759895 : Blo 539803 1759895 := bstep (se 1 (by rfl) ⟨1319921, by rfl⟩ : syracuseStep 1759895 = 2639843) B2639843
theorem B1219265 : Blo 539803 1219265 := bstep (se 2 (by rfl) ⟨457224, by rfl⟩ : syracuseStep 1219265 = 914449) B914449
theorem B989911 : Blo 539803 989911 := bstep (se 1 (by rfl) ⟨742433, by rfl⟩ : syracuseStep 989911 = 1484867) B1484867
theorem B1170163 : Blo 539803 1170163 := bstep (se 1 (by rfl) ⟨877622, by rfl⟩ : syracuseStep 1170163 = 1755245) B1755245
theorem B2054915 : Blo 539803 2054915 := bstep (se 1 (by rfl) ⟨1541186, by rfl⟩ : syracuseStep 2054915 = 3082373) B3082373
theorem B3373841 : Blo 539803 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B2054929 : Blo 539803 2054929 := bstep (se 2 (by rfl) ⟨770598, by rfl⟩ : syracuseStep 2054929 = 1541197) B1541197
theorem B809753 : Blo 539803 809753 := bstep (se 2 (by rfl) ⟨303657, by rfl⟩ : syracuseStep 809753 = 607315) B607315
theorem B3128129 : Blo 539803 3128129 := bstep (se 2 (by rfl) ⟨1173048, by rfl⟩ : syracuseStep 3128129 = 2346097) B2346097
theorem B4120793 : Blo 539803 4120793 := bstep (se 2 (by rfl) ⟨1545297, by rfl⟩ : syracuseStep 4120793 = 3090595) B3090595
theorem B3087179 : Blo 539803 3087179 := bstep (se 1 (by rfl) ⟨2315384, by rfl⟩ : syracuseStep 3087179 = 4630769) B4630769
theorem B1538909 : Blo 539803 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B809867 : Blo 539803 809867 := bstep (se 1 (by rfl) ⟨607400, by rfl⟩ : syracuseStep 809867 = 1214801) B1214801
theorem B809879 : Blo 539803 809879 := bstep (se 1 (by rfl) ⟨607409, by rfl⟩ : syracuseStep 809879 = 1214819) B1214819
theorem B1219481 : Blo 539803 1219481 := bstep (se 2 (by rfl) ⟨457305, by rfl⟩ : syracuseStep 1219481 = 914611) B914611
theorem B2710451 : Blo 539803 2710451 := bstep (se 1 (by rfl) ⟨2032838, by rfl⟩ : syracuseStep 2710451 = 4065677) B4065677
theorem B1825739 : Blo 539803 1825739 := bstep (se 1 (by rfl) ⟨1369304, by rfl⟩ : syracuseStep 1825739 = 2738609) B2738609
theorem B809945 : Blo 539803 809945 := bstep (se 2 (by rfl) ⟨303729, by rfl⟩ : syracuseStep 809945 = 607459) B607459
theorem B1219571 : Blo 539803 1219571 := bstep (se 1 (by rfl) ⟨914678, by rfl⟩ : syracuseStep 1219571 = 1829357) B1829357
theorem B1219607 : Blo 539803 1219607 := bstep (se 1 (by rfl) ⟨914705, by rfl⟩ : syracuseStep 1219607 = 1829411) B1829411
theorem B2055233 : Blo 539803 2055233 := bstep (se 2 (by rfl) ⟨770712, by rfl⟩ : syracuseStep 2055233 = 1541425) B1541425
theorem B810059 : Blo 539803 810059 := bstep (se 1 (by rfl) ⟨607544, by rfl⟩ : syracuseStep 810059 = 1215089) B1215089
theorem B810071 : Blo 539803 810071 := bstep (se 1 (by rfl) ⟨607553, by rfl⟩ : syracuseStep 810071 = 1215107) B1215107
theorem B810137 : Blo 539803 810137 := bstep (se 2 (by rfl) ⟨303801, by rfl⟩ : syracuseStep 810137 = 607603) B607603
theorem B539819 : Blo 539803 539819 := bstep (se 1 (by rfl) ⟨404864, by rfl⟩ : syracuseStep 539819 = 809729) B809729
theorem B1367219 : Blo 539803 1367219 := bstep (se 1 (by rfl) ⟨1025414, by rfl⟩ : syracuseStep 1367219 = 2050829) B2050829
theorem B539831 : Blo 539803 539831 := bstep (se 1 (by rfl) ⟨404873, by rfl⟩ : syracuseStep 539831 = 809747) B809747
theorem B539851 : Blo 539803 539851 := bstep (se 1 (by rfl) ⟨404888, by rfl⟩ : syracuseStep 539851 = 809777) B809777
theorem B1219787 : Blo 539803 1219787 := bstep (se 1 (by rfl) ⟨914840, by rfl⟩ : syracuseStep 1219787 = 1829681) B1829681
theorem B539863 : Blo 539803 539863 := bstep (se 1 (by rfl) ⟨404897, by rfl⟩ : syracuseStep 539863 = 809795) B809795
theorem B1826009 : Blo 539803 1826009 := bstep (se 2 (by rfl) ⟨684753, by rfl⟩ : syracuseStep 1826009 = 1369507) B1369507
theorem B539883 : Blo 539803 539883 := bstep (se 1 (by rfl) ⟨404912, by rfl⟩ : syracuseStep 539883 = 809825) B809825
theorem B539895 : Blo 539803 539895 := bstep (se 1 (by rfl) ⟨404921, by rfl⟩ : syracuseStep 539895 = 809843) B809843
theorem B1219841 : Blo 539803 1219841 := bstep (se 2 (by rfl) ⟨457440, by rfl⟩ : syracuseStep 1219841 = 914881) B914881
theorem B539915 : Blo 539803 539915 := bstep (se 1 (by rfl) ⟨404936, by rfl⟩ : syracuseStep 539915 = 809873) B809873
theorem B810251 : Blo 539803 810251 := bstep (se 1 (by rfl) ⟨607688, by rfl⟩ : syracuseStep 810251 = 1215377) B1215377
theorem B539927 : Blo 539803 539927 := bstep (se 1 (by rfl) ⟨404945, by rfl⟩ : syracuseStep 539927 = 809891) B809891
theorem B810263 : Blo 539803 810263 := bstep (se 1 (by rfl) ⟨607697, by rfl⟩ : syracuseStep 810263 = 1215395) B1215395
theorem B1948951 : Blo 539803 1948951 := bstep (se 1 (by rfl) ⟨1461713, by rfl⟩ : syracuseStep 1948951 = 2923427) B2923427
theorem B539947 : Blo 539803 539947 := bstep (se 1 (by rfl) ⟨404960, by rfl⟩ : syracuseStep 539947 = 809921) B809921
theorem B539959 : Blo 539803 539959 := bstep (se 1 (by rfl) ⟨404969, by rfl⟩ : syracuseStep 539959 = 809939) B809939
theorem B539979 : Blo 539803 539979 := bstep (se 1 (by rfl) ⟨404984, by rfl⟩ : syracuseStep 539979 = 809969) B809969
theorem B539991 : Blo 539803 539991 := bstep (se 1 (by rfl) ⟨404993, by rfl⟩ : syracuseStep 539991 = 809987) B809987
theorem B810329 : Blo 539803 810329 := bstep (se 2 (by rfl) ⟨303873, by rfl⟩ : syracuseStep 810329 = 607747) B607747
theorem B540011 : Blo 539803 540011 := bstep (se 1 (by rfl) ⟨405008, by rfl⟩ : syracuseStep 540011 = 810017) B810017
theorem B540023 : Blo 539803 540023 := bstep (se 1 (by rfl) ⟨405017, by rfl⟩ : syracuseStep 540023 = 810035) B810035
theorem B540043 : Blo 539803 540043 := bstep (se 1 (by rfl) ⟨405032, by rfl⟩ : syracuseStep 540043 = 810065) B810065
theorem B540055 : Blo 539803 540055 := bstep (se 1 (by rfl) ⟨405041, by rfl⟩ : syracuseStep 540055 = 810083) B810083
theorem B540075 : Blo 539803 540075 := bstep (se 1 (by rfl) ⟨405056, by rfl⟩ : syracuseStep 540075 = 810113) B810113
theorem B540087 : Blo 539803 540087 := bstep (se 1 (by rfl) ⟨405065, by rfl⟩ : syracuseStep 540087 = 810131) B810131
theorem B1736129 : Blo 539803 1736129 := bstep (se 2 (by rfl) ⟨651048, by rfl⟩ : syracuseStep 1736129 = 1302097) B1302097
theorem B540107 : Blo 539803 540107 := bstep (se 1 (by rfl) ⟨405080, by rfl⟩ : syracuseStep 540107 = 810161) B810161
theorem B810443 : Blo 539803 810443 := bstep (se 1 (by rfl) ⟨607832, by rfl⟩ : syracuseStep 810443 = 1215665) B1215665
theorem B540119 : Blo 539803 540119 := bstep (se 1 (by rfl) ⟨405089, by rfl⟩ : syracuseStep 540119 = 810179) B810179
theorem B810455 : Blo 539803 810455 := bstep (se 1 (by rfl) ⟨607841, by rfl⟩ : syracuseStep 810455 = 1215683) B1215683
theorem B1367513 : Blo 539803 1367513 := bstep (se 2 (by rfl) ⟨512817, by rfl⟩ : syracuseStep 1367513 = 1025635) B1025635
theorem B2309593 : Blo 539803 2309593 := bstep (se 2 (by rfl) ⟨866097, by rfl⟩ : syracuseStep 2309593 = 1732195) B1732195
theorem B1318361 : Blo 539803 1318361 := bstep (se 2 (by rfl) ⟨494385, by rfl⟩ : syracuseStep 1318361 = 988771) B988771
theorem B1220057 : Blo 539803 1220057 := bstep (se 2 (by rfl) ⟨457521, by rfl⟩ : syracuseStep 1220057 = 915043) B915043
theorem B7044569 : Blo 539803 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B540139 : Blo 539803 540139 := bstep (se 1 (by rfl) ⟨405104, by rfl⟩ : syracuseStep 540139 = 810209) B810209
theorem B540151 : Blo 539803 540151 := bstep (se 1 (by rfl) ⟨405113, by rfl⟩ : syracuseStep 540151 = 810227) B810227
theorem B540171 : Blo 539803 540171 := bstep (se 1 (by rfl) ⟨405128, by rfl⟩ : syracuseStep 540171 = 810257) B810257
theorem B7790093 : Blo 539803 7790093 := bstep (se 3 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 7790093 = 2921285) B2921285
theorem B540183 : Blo 539803 540183 := bstep (se 1 (by rfl) ⟨405137, by rfl⟩ : syracuseStep 540183 = 810275) B810275
theorem B810521 : Blo 539803 810521 := bstep (se 2 (by rfl) ⟨303945, by rfl⟩ : syracuseStep 810521 = 607891) B607891
theorem B540203 : Blo 539803 540203 := bstep (se 1 (by rfl) ⟨405152, by rfl⟩ : syracuseStep 540203 = 810305) B810305
theorem B1220147 : Blo 539803 1220147 := bstep (se 1 (by rfl) ⟨915110, by rfl⟩ : syracuseStep 1220147 = 1830221) B1830221
theorem B540215 : Blo 539803 540215 := bstep (se 1 (by rfl) ⟨405161, by rfl⟩ : syracuseStep 540215 = 810323) B810323
theorem B540235 : Blo 539803 540235 := bstep (se 1 (by rfl) ⟨405176, by rfl⟩ : syracuseStep 540235 = 810353) B810353
theorem B540247 : Blo 539803 540247 := bstep (se 1 (by rfl) ⟨405185, by rfl⟩ : syracuseStep 540247 = 810371) B810371
theorem B974425 : Blo 539803 974425 := bstep (se 2 (by rfl) ⟨365409, by rfl⟩ : syracuseStep 974425 = 730819) B730819
theorem B1220183 : Blo 539803 1220183 := bstep (se 1 (by rfl) ⟨915137, by rfl⟩ : syracuseStep 1220183 = 1830275) B1830275
theorem B540267 : Blo 539803 540267 := bstep (se 1 (by rfl) ⟨405200, by rfl⟩ : syracuseStep 540267 = 810401) B810401
theorem B540279 : Blo 539803 540279 := bstep (se 1 (by rfl) ⟨405209, by rfl⟩ : syracuseStep 540279 = 810419) B810419
theorem B548471 : Blo 539803 548471 := bstep (se 1 (by rfl) ⟨411353, by rfl⟩ : syracuseStep 548471 = 822707) B822707
theorem B540299 : Blo 539803 540299 := bstep (se 1 (by rfl) ⟨405224, by rfl⟩ : syracuseStep 540299 = 810449) B810449
theorem B810635 : Blo 539803 810635 := bstep (se 1 (by rfl) ⟨607976, by rfl⟩ : syracuseStep 810635 = 1215953) B1215953
theorem B540311 : Blo 539803 540311 := bstep (se 1 (by rfl) ⟨405233, by rfl⟩ : syracuseStep 540311 = 810467) B810467
theorem B810647 : Blo 539803 810647 := bstep (se 1 (by rfl) ⟨607985, by rfl⟩ : syracuseStep 810647 = 1215971) B1215971
theorem B540331 : Blo 539803 540331 := bstep (se 1 (by rfl) ⟨405248, by rfl⟩ : syracuseStep 540331 = 810497) B810497
theorem B4169393 : Blo 539803 4169393 := bstep (se 2 (by rfl) ⟨1563522, by rfl⟩ : syracuseStep 4169393 = 3127045) B3127045
theorem B540343 : Blo 539803 540343 := bstep (se 1 (by rfl) ⟨405257, by rfl⟩ : syracuseStep 540343 = 810515) B810515
theorem B540363 : Blo 539803 540363 := bstep (se 1 (by rfl) ⟨405272, by rfl⟩ : syracuseStep 540363 = 810545) B810545
theorem B540375 : Blo 539803 540375 := bstep (se 1 (by rfl) ⟨405281, by rfl⟩ : syracuseStep 540375 = 810563) B810563
theorem B810713 : Blo 539803 810713 := bstep (se 2 (by rfl) ⟨304017, by rfl⟩ : syracuseStep 810713 = 608035) B608035
theorem B2055901 : Blo 539803 2055901 := bstep (se 3 (by rfl) ⟨385481, by rfl⟩ : syracuseStep 2055901 = 770963) B770963
theorem B540395 : Blo 539803 540395 := bstep (se 1 (by rfl) ⟨405296, by rfl⟩ : syracuseStep 540395 = 810593) B810593
theorem B540407 : Blo 539803 540407 := bstep (se 1 (by rfl) ⟨405305, by rfl⟩ : syracuseStep 540407 = 810611) B810611
theorem B4620037 : Blo 539803 4620037 := bstep (se 4 (by rfl) ⟨433128, by rfl⟩ : syracuseStep 4620037 = 866257) B866257
theorem B540427 : Blo 539803 540427 := bstep (se 1 (by rfl) ⟨405320, by rfl⟩ : syracuseStep 540427 = 810641) B810641
theorem B1220363 : Blo 539803 1220363 := bstep (se 1 (by rfl) ⟨915272, by rfl⟩ : syracuseStep 1220363 = 1830545) B1830545
theorem B540439 : Blo 539803 540439 := bstep (se 1 (by rfl) ⟨405329, by rfl⟩ : syracuseStep 540439 = 810659) B810659
theorem B1154839 : Blo 539803 1154839 := bstep (se 1 (by rfl) ⟨866129, by rfl⟩ : syracuseStep 1154839 = 1732259) B1732259
theorem B540459 : Blo 539803 540459 := bstep (se 1 (by rfl) ⟨405344, by rfl⟩ : syracuseStep 540459 = 810689) B810689
theorem B540471 : Blo 539803 540471 := bstep (se 1 (by rfl) ⟨405353, by rfl⟩ : syracuseStep 540471 = 810707) B810707
theorem B1220417 : Blo 539803 1220417 := bstep (se 2 (by rfl) ⟨457656, by rfl⟩ : syracuseStep 1220417 = 915313) B915313
theorem B540491 : Blo 539803 540491 := bstep (se 1 (by rfl) ⟨405368, by rfl⟩ : syracuseStep 540491 = 810737) B810737
theorem B810827 : Blo 539803 810827 := bstep (se 1 (by rfl) ⟨608120, by rfl⟩ : syracuseStep 810827 = 1216241) B1216241
theorem B1154891 : Blo 539803 1154891 := bstep (se 1 (by rfl) ⟨866168, by rfl⟩ : syracuseStep 1154891 = 1732337) B1732337
theorem B540503 : Blo 539803 540503 := bstep (se 1 (by rfl) ⟨405377, by rfl⟩ : syracuseStep 540503 = 810755) B810755
theorem B810839 : Blo 539803 810839 := bstep (se 1 (by rfl) ⟨608129, by rfl⟩ : syracuseStep 810839 = 1216259) B1216259
theorem B540523 : Blo 539803 540523 := bstep (se 1 (by rfl) ⟨405392, by rfl⟩ : syracuseStep 540523 = 810785) B810785
theorem B540535 : Blo 539803 540535 := bstep (se 1 (by rfl) ⟨405401, by rfl⟩ : syracuseStep 540535 = 810803) B810803
theorem B540555 : Blo 539803 540555 := bstep (se 1 (by rfl) ⟨405416, by rfl⟩ : syracuseStep 540555 = 810833) B810833
theorem B540567 : Blo 539803 540567 := bstep (se 1 (by rfl) ⟨405425, by rfl⟩ : syracuseStep 540567 = 810851) B810851
theorem B1826711 : Blo 539803 1826711 := bstep (se 1 (by rfl) ⟨1370033, by rfl⟩ : syracuseStep 1826711 = 2740067) B2740067
theorem B810905 : Blo 539803 810905 := bstep (se 2 (by rfl) ⟨304089, by rfl⟩ : syracuseStep 810905 = 608179) B608179
theorem B540587 : Blo 539803 540587 := bstep (se 1 (by rfl) ⟨405440, by rfl⟩ : syracuseStep 540587 = 810881) B810881
theorem B540599 : Blo 539803 540599 := bstep (se 1 (by rfl) ⟨405449, by rfl⟩ : syracuseStep 540599 = 810899) B810899
theorem B540619 : Blo 539803 540619 := bstep (se 1 (by rfl) ⟨405464, by rfl⟩ : syracuseStep 540619 = 810929) B810929
theorem B540631 : Blo 539803 540631 := bstep (se 1 (by rfl) ⟨405473, by rfl⟩ : syracuseStep 540631 = 810947) B810947
theorem B540651 : Blo 539803 540651 := bstep (se 1 (by rfl) ⟨405488, by rfl⟩ : syracuseStep 540651 = 810977) B810977
theorem B540663 : Blo 539803 540663 := bstep (se 1 (by rfl) ⟨405497, by rfl⟩ : syracuseStep 540663 = 810995) B810995
theorem B540679 : Blo 539803 540679 := bstep (se 1 (by rfl) ⟨405509, by rfl⟩ : syracuseStep 540679 = 811019) B811019
theorem B540687 : Blo 539803 540687 := bstep (se 1 (by rfl) ⟨405515, by rfl⟩ : syracuseStep 540687 = 811031) B811031
theorem B4620311 : Blo 539803 4620311 := bstep (se 1 (by rfl) ⟨3465233, by rfl⟩ : syracuseStep 4620311 = 6930467) B6930467
theorem B1220651 : Blo 539803 1220651 := bstep (se 1 (by rfl) ⟨915488, by rfl⟩ : syracuseStep 1220651 = 1830977) B1830977
theorem B811067 : Blo 539803 811067 := bstep (se 1 (by rfl) ⟨608300, by rfl⟩ : syracuseStep 811067 = 1216601) B1216601
theorem B540731 : Blo 539803 540731 := bstep (se 1 (by rfl) ⟨405548, by rfl⟩ : syracuseStep 540731 = 811097) B811097
theorem B811127 : Blo 539803 811127 := bstep (se 1 (by rfl) ⟨608345, by rfl⟩ : syracuseStep 811127 = 1216691) B1216691
theorem B540807 : Blo 539803 540807 := bstep (se 1 (by rfl) ⟨405605, by rfl⟩ : syracuseStep 540807 = 811211) B811211
theorem B868487 : Blo 539803 868487 := bstep (se 1 (by rfl) ⟨651365, by rfl⟩ : syracuseStep 868487 = 1302731) B1302731
theorem B811151 : Blo 539803 811151 := bstep (se 1 (by rfl) ⟨608363, by rfl⟩ : syracuseStep 811151 = 1216727) B1216727
theorem B540815 : Blo 539803 540815 := bstep (se 1 (by rfl) ⟨405611, by rfl⟩ : syracuseStep 540815 = 811223) B811223
theorem B1368211 : Blo 539803 1368211 := bstep (se 1 (by rfl) ⟨1026158, by rfl⟩ : syracuseStep 1368211 = 2052317) B2052317
theorem B811193 : Blo 539803 811193 := bstep (se 2 (by rfl) ⟨304197, by rfl⟩ : syracuseStep 811193 = 608395) B608395
theorem B1302713 : Blo 539803 1302713 := bstep (se 2 (by rfl) ⟨488517, by rfl⟩ : syracuseStep 1302713 = 977035) B977035
theorem B540859 : Blo 539803 540859 := bstep (se 1 (by rfl) ⟨405644, by rfl⟩ : syracuseStep 540859 = 811289) B811289
theorem B3948745 : Blo 539803 3948745 := bstep (se 2 (by rfl) ⟨1480779, by rfl⟩ : syracuseStep 3948745 = 2961559) B2961559
theorem B811271 : Blo 539803 811271 := bstep (se 1 (by rfl) ⟨608453, by rfl⟩ : syracuseStep 811271 = 1216907) B1216907
theorem B540935 : Blo 539803 540935 := bstep (se 1 (by rfl) ⟨405701, by rfl⟩ : syracuseStep 540935 = 811403) B811403
theorem B1540367 : Blo 539803 1540367 := bstep (se 1 (by rfl) ⟨1155275, by rfl⟩ : syracuseStep 1540367 = 2310551) B2310551
theorem B540943 : Blo 539803 540943 := bstep (se 1 (by rfl) ⟨405707, by rfl⟩ : syracuseStep 540943 = 811415) B811415
theorem B1368353 : Blo 539803 1368353 := bstep (se 2 (by rfl) ⟨513132, by rfl⟩ : syracuseStep 1368353 = 1026265) B1026265
theorem B811307 : Blo 539803 811307 := bstep (se 1 (by rfl) ⟨608480, by rfl⟩ : syracuseStep 811307 = 1216961) B1216961
theorem B540987 : Blo 539803 540987 := bstep (se 1 (by rfl) ⟨405740, by rfl⟩ : syracuseStep 540987 = 811481) B811481
theorem B811337 : Blo 539803 811337 := bstep (se 2 (by rfl) ⟨304251, by rfl⟩ : syracuseStep 811337 = 608503) B608503
theorem B541063 : Blo 539803 541063 := bstep (se 1 (by rfl) ⟨405797, by rfl⟩ : syracuseStep 541063 = 811595) B811595
theorem B541071 : Blo 539803 541071 := bstep (se 1 (by rfl) ⟨405803, by rfl⟩ : syracuseStep 541071 = 811607) B811607
theorem B1221011 : Blo 539803 1221011 := bstep (se 1 (by rfl) ⟨915758, by rfl⟩ : syracuseStep 1221011 = 1831517) B1831517
theorem B2474393 : Blo 539803 2474393 := bstep (se 2 (by rfl) ⟨927897, by rfl⟩ : syracuseStep 2474393 = 1855795) B1855795
theorem B2933177 : Blo 539803 2933177 := bstep (se 2 (by rfl) ⟨1099941, by rfl⟩ : syracuseStep 2933177 = 2199883) B2199883
theorem B811451 : Blo 539803 811451 := bstep (se 1 (by rfl) ⟨608588, by rfl⟩ : syracuseStep 811451 = 1217177) B1217177
theorem B541115 : Blo 539803 541115 := bstep (se 1 (by rfl) ⟨405836, by rfl⟩ : syracuseStep 541115 = 811673) B811673
theorem B1221065 : Blo 539803 1221065 := bstep (se 2 (by rfl) ⟨457899, by rfl⟩ : syracuseStep 1221065 = 915799) B915799
theorem B811511 : Blo 539803 811511 := bstep (se 1 (by rfl) ⟨608633, by rfl⟩ : syracuseStep 811511 = 1217267) B1217267
theorem B541191 : Blo 539803 541191 := bstep (se 1 (by rfl) ⟨405893, by rfl⟩ : syracuseStep 541191 = 811787) B811787
theorem B811535 : Blo 539803 811535 := bstep (se 1 (by rfl) ⟨608651, by rfl⟩ : syracuseStep 811535 = 1217303) B1217303
theorem B541199 : Blo 539803 541199 := bstep (se 1 (by rfl) ⟨405899, by rfl⟩ : syracuseStep 541199 = 811799) B811799
theorem B1155617 : Blo 539803 1155617 := bstep (se 2 (by rfl) ⟨433356, by rfl⟩ : syracuseStep 1155617 = 866713) B866713
theorem B811577 : Blo 539803 811577 := bstep (se 2 (by rfl) ⟨304341, by rfl⟩ : syracuseStep 811577 = 608683) B608683
theorem B541243 : Blo 539803 541243 := bstep (se 1 (by rfl) ⟨405932, by rfl⟩ : syracuseStep 541243 = 811865) B811865
theorem B4629059 : Blo 539803 4629059 := bstep (se 1 (by rfl) ⟨3471794, by rfl⟩ : syracuseStep 4629059 = 6943589) B6943589
theorem B811655 : Blo 539803 811655 := bstep (se 1 (by rfl) ⟨608741, by rfl⟩ : syracuseStep 811655 = 1217483) B1217483
theorem B541319 : Blo 539803 541319 := bstep (se 1 (by rfl) ⟨405989, by rfl⟩ : syracuseStep 541319 = 811979) B811979
theorem B541327 : Blo 539803 541327 := bstep (se 1 (by rfl) ⟨405995, by rfl⟩ : syracuseStep 541327 = 811991) B811991
theorem B811691 : Blo 539803 811691 := bstep (se 1 (by rfl) ⟨608768, by rfl⟩ : syracuseStep 811691 = 1217537) B1217537
theorem B6242993 : Blo 539803 6242993 := bstep (se 2 (by rfl) ⟨2341122, by rfl⟩ : syracuseStep 6242993 = 4682245) B4682245
theorem B541371 : Blo 539803 541371 := bstep (se 1 (by rfl) ⟨406028, by rfl⟩ : syracuseStep 541371 = 812057) B812057
theorem B811721 : Blo 539803 811721 := bstep (se 2 (by rfl) ⟨304395, by rfl⟩ : syracuseStep 811721 = 608791) B608791
theorem B2745089 : Blo 539803 2745089 := bstep (se 2 (by rfl) ⟨1029408, by rfl⟩ : syracuseStep 2745089 = 2058817) B2058817
theorem B541447 : Blo 539803 541447 := bstep (se 1 (by rfl) ⟨406085, by rfl⟩ : syracuseStep 541447 = 812171) B812171
theorem B541455 : Blo 539803 541455 := bstep (se 1 (by rfl) ⟨406091, by rfl⟩ : syracuseStep 541455 = 812183) B812183
theorem B5202737 : Blo 539803 5202737 := bstep (se 2 (by rfl) ⟨1951026, by rfl⟩ : syracuseStep 5202737 = 3902053) B3902053
theorem B811835 : Blo 539803 811835 := bstep (se 1 (by rfl) ⟨608876, by rfl⟩ : syracuseStep 811835 = 1217753) B1217753
theorem B541499 : Blo 539803 541499 := bstep (se 1 (by rfl) ⟨406124, by rfl⟩ : syracuseStep 541499 = 812249) B812249
theorem B869179 : Blo 539803 869179 := bstep (se 1 (by rfl) ⟨651884, by rfl⟩ : syracuseStep 869179 = 1303769) B1303769
theorem B1467197 : Blo 539803 1467197 := bstep (se 3 (by rfl) ⟨275099, by rfl⟩ : syracuseStep 1467197 = 550199) B550199
theorem B811895 : Blo 539803 811895 := bstep (se 1 (by rfl) ⟨608921, by rfl⟩ : syracuseStep 811895 = 1217843) B1217843
theorem B541575 : Blo 539803 541575 := bstep (se 1 (by rfl) ⟨406181, by rfl⟩ : syracuseStep 541575 = 812363) B812363
theorem B811919 : Blo 539803 811919 := bstep (se 1 (by rfl) ⟨608939, by rfl⟩ : syracuseStep 811919 = 1217879) B1217879
theorem B541583 : Blo 539803 541583 := bstep (se 1 (by rfl) ⟨406187, by rfl⟩ : syracuseStep 541583 = 812375) B812375
theorem B1827737 : Blo 539803 1827737 := bstep (se 2 (by rfl) ⟨685401, by rfl⟩ : syracuseStep 1827737 = 1370803) B1370803
theorem B811961 : Blo 539803 811961 := bstep (se 2 (by rfl) ⟨304485, by rfl⟩ : syracuseStep 811961 = 608971) B608971
theorem B541627 : Blo 539803 541627 := bstep (se 1 (by rfl) ⟨406220, by rfl⟩ : syracuseStep 541627 = 812441) B812441
theorem B3089411 : Blo 539803 3089411 := bstep (se 1 (by rfl) ⟨2317058, by rfl⟩ : syracuseStep 3089411 = 4634117) B4634117
theorem B812039 : Blo 539803 812039 := bstep (se 1 (by rfl) ⟨609029, by rfl⟩ : syracuseStep 812039 = 1218059) B1218059
theorem B541703 : Blo 539803 541703 := bstep (se 1 (by rfl) ⟨406277, by rfl⟩ : syracuseStep 541703 = 812555) B812555
theorem B2475019 : Blo 539803 2475019 := bstep (se 1 (by rfl) ⟨1856264, by rfl⟩ : syracuseStep 2475019 = 3712529) B3712529
theorem B541711 : Blo 539803 541711 := bstep (se 1 (by rfl) ⟨406283, by rfl⟩ : syracuseStep 541711 = 812567) B812567
theorem B762895 : Blo 539803 762895 := bstep (se 1 (by rfl) ⟨572171, by rfl⟩ : syracuseStep 762895 = 1144343) B1144343
theorem B812075 : Blo 539803 812075 := bstep (se 1 (by rfl) ⟨609056, by rfl⟩ : syracuseStep 812075 = 1218113) B1218113
theorem B4621373 : Blo 539803 4621373 := bstep (se 3 (by rfl) ⟨866507, by rfl⟩ : syracuseStep 4621373 = 1733015) B1733015
theorem B541755 : Blo 539803 541755 := bstep (se 1 (by rfl) ⟨406316, by rfl⟩ : syracuseStep 541755 = 812633) B812633
theorem B812105 : Blo 539803 812105 := bstep (se 2 (by rfl) ⟨304539, by rfl⟩ : syracuseStep 812105 = 609079) B609079
theorem B23733323 : Blo 539803 23733323 := bstep (se 1 (by rfl) ⟨17799992, by rfl⟩ : syracuseStep 23733323 = 35599985) B35599985
theorem B5866613 : Blo 539803 5866613 := bstep (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) B549995
theorem B1115255 : Blo 539803 1115255 := bstep (se 1 (by rfl) ⟨836441, by rfl⟩ : syracuseStep 1115255 = 1672883) B1672883
theorem B541831 : Blo 539803 541831 := bstep (se 1 (by rfl) ⟨406373, by rfl⟩ : syracuseStep 541831 = 812747) B812747
theorem B541839 : Blo 539803 541839 := bstep (se 1 (by rfl) ⟨406379, by rfl⟩ : syracuseStep 541839 = 812759) B812759
theorem B812219 : Blo 539803 812219 := bstep (se 1 (by rfl) ⟨609164, by rfl⟩ : syracuseStep 812219 = 1218329) B1218329
theorem B541883 : Blo 539803 541883 := bstep (se 1 (by rfl) ⟨406412, by rfl⟩ : syracuseStep 541883 = 812825) B812825
theorem B812279 : Blo 539803 812279 := bstep (se 1 (by rfl) ⟨609209, by rfl⟩ : syracuseStep 812279 = 1218419) B1218419
theorem B1369345 : Blo 539803 1369345 := bstep (se 2 (by rfl) ⟨513504, by rfl⟩ : syracuseStep 1369345 = 1027009) B1027009
theorem B607495 : Blo 539803 607495 := bstep (se 1 (by rfl) ⟨455621, by rfl⟩ : syracuseStep 607495 = 911243) B911243
theorem B541959 : Blo 539803 541959 := bstep (se 1 (by rfl) ⟨406469, by rfl⟩ : syracuseStep 541959 = 812939) B812939
theorem B812303 : Blo 539803 812303 := bstep (se 1 (by rfl) ⟨609227, by rfl⟩ : syracuseStep 812303 = 1218455) B1218455
theorem B541967 : Blo 539803 541967 := bstep (se 1 (by rfl) ⟨406475, by rfl⟩ : syracuseStep 541967 = 812951) B812951
theorem B812345 : Blo 539803 812345 := bstep (se 2 (by rfl) ⟨304629, by rfl⟩ : syracuseStep 812345 = 609259) B609259
theorem B771385 : Blo 539803 771385 := bstep (se 2 (by rfl) ⟨289269, by rfl⟩ : syracuseStep 771385 = 578539) B578539
theorem B542011 : Blo 539803 542011 := bstep (se 1 (by rfl) ⟨406508, by rfl⟩ : syracuseStep 542011 = 813017) B813017
theorem B1025399 : Blo 539803 1025399 := bstep (se 1 (by rfl) ⟨769049, by rfl⟩ : syracuseStep 1025399 = 1538099) B1538099
theorem B812423 : Blo 539803 812423 := bstep (se 1 (by rfl) ⟨609317, by rfl⟩ : syracuseStep 812423 = 1218635) B1218635
theorem B542087 : Blo 539803 542087 := bstep (se 1 (by rfl) ⟨406565, by rfl⟩ : syracuseStep 542087 = 813131) B813131
theorem B542095 : Blo 539803 542095 := bstep (se 1 (by rfl) ⟨406571, by rfl⟩ : syracuseStep 542095 = 813143) B813143
theorem B5211539 : Blo 539803 5211539 := bstep (se 1 (by rfl) ⟨3908654, by rfl⟩ : syracuseStep 5211539 = 7817309) B7817309
theorem B812459 : Blo 539803 812459 := bstep (se 1 (by rfl) ⟨609344, by rfl⟩ : syracuseStep 812459 = 1218689) B1218689
theorem B607675 : Blo 539803 607675 := bstep (se 1 (by rfl) ⟨455756, by rfl⟩ : syracuseStep 607675 = 911513) B911513
theorem B542139 : Blo 539803 542139 := bstep (se 1 (by rfl) ⟨406604, by rfl⟩ : syracuseStep 542139 = 813209) B813209
theorem B812489 : Blo 539803 812489 := bstep (se 2 (by rfl) ⟨304683, by rfl⟩ : syracuseStep 812489 = 609367) B609367
theorem B2606539 : Blo 539803 2606539 := bstep (se 1 (by rfl) ⟨1954904, by rfl⟩ : syracuseStep 2606539 = 3909809) B3909809
theorem B542215 : Blo 539803 542215 := bstep (se 1 (by rfl) ⟨406661, by rfl⟩ : syracuseStep 542215 = 813323) B813323
theorem B1025551 : Blo 539803 1025551 := bstep (se 1 (by rfl) ⟨769163, by rfl⟩ : syracuseStep 1025551 = 1538327) B1538327
theorem B542223 : Blo 539803 542223 := bstep (se 1 (by rfl) ⟨406667, by rfl⟩ : syracuseStep 542223 = 813335) B813335
theorem B23447069 : Blo 539803 23447069 := bstep (se 3 (by rfl) ⟨4396325, by rfl⟩ : syracuseStep 23447069 = 8792651) B8792651
theorem B2745899 : Blo 539803 2745899 := bstep (se 1 (by rfl) ⟨2059424, by rfl⟩ : syracuseStep 2745899 = 4118849) B4118849
theorem B812603 : Blo 539803 812603 := bstep (se 1 (by rfl) ⟨609452, by rfl⟩ : syracuseStep 812603 = 1218905) B1218905
theorem B542267 : Blo 539803 542267 := bstep (se 1 (by rfl) ⟨406700, by rfl⟩ : syracuseStep 542267 = 813401) B813401
theorem B1828439 : Blo 539803 1828439 := bstep (se 1 (by rfl) ⟨1371329, by rfl⟩ : syracuseStep 1828439 = 2742659) B2742659
theorem B3081847 : Blo 539803 3081847 := bstep (se 1 (by rfl) ⟨2311385, by rfl⟩ : syracuseStep 3081847 = 4622771) B4622771
theorem B812663 : Blo 539803 812663 := bstep (se 1 (by rfl) ⟨609497, by rfl⟩ : syracuseStep 812663 = 1218995) B1218995
theorem B1541767 : Blo 539803 1541767 := bstep (se 1 (by rfl) ⟨1156325, by rfl⟩ : syracuseStep 1541767 = 2312651) B2312651
theorem B542343 : Blo 539803 542343 := bstep (se 1 (by rfl) ⟨406757, by rfl⟩ : syracuseStep 542343 = 813515) B813515
theorem B812687 : Blo 539803 812687 := bstep (se 1 (by rfl) ⟨609515, by rfl⟩ : syracuseStep 812687 = 1219031) B1219031
theorem B542351 : Blo 539803 542351 := bstep (se 1 (by rfl) ⟨406763, by rfl⟩ : syracuseStep 542351 = 813527) B813527
theorem B812729 : Blo 539803 812729 := bstep (se 2 (by rfl) ⟨304773, by rfl⟩ : syracuseStep 812729 = 609547) B609547
theorem B542395 : Blo 539803 542395 := bstep (se 1 (by rfl) ⟨406796, by rfl⟩ : syracuseStep 542395 = 813593) B813593
theorem B2598601 : Blo 539803 2598601 := bstep (se 2 (by rfl) ⟨974475, by rfl⟩ : syracuseStep 2598601 = 1948951) B1948951
theorem B3606245 : Blo 539803 3606245 := bstep (se 4 (by rfl) ⟨338085, by rfl⟩ : syracuseStep 3606245 = 676171) B676171
theorem B812807 : Blo 539803 812807 := bstep (se 1 (by rfl) ⟨609605, by rfl⟩ : syracuseStep 812807 = 1219211) B1219211
theorem B542471 : Blo 539803 542471 := bstep (se 1 (by rfl) ⟨406853, by rfl⟩ : syracuseStep 542471 = 813707) B813707
theorem B1173263 : Blo 539803 1173263 := bstep (se 1 (by rfl) ⟨879947, by rfl⟩ : syracuseStep 1173263 = 1759895) B1759895
theorem B542479 : Blo 539803 542479 := bstep (se 1 (by rfl) ⟨406859, by rfl⟩ : syracuseStep 542479 = 813719) B813719
theorem B812843 : Blo 539803 812843 := bstep (se 1 (by rfl) ⟨609632, by rfl⟩ : syracuseStep 812843 = 1219265) B1219265
theorem B542523 : Blo 539803 542523 := bstep (se 1 (by rfl) ⟨406892, by rfl⟩ : syracuseStep 542523 = 813785) B813785
theorem B812873 : Blo 539803 812873 := bstep (se 2 (by rfl) ⟨304827, by rfl⟩ : syracuseStep 812873 = 609655) B609655
theorem B1369943 : Blo 539803 1369943 := bstep (se 1 (by rfl) ⟨1027457, by rfl⟩ : syracuseStep 1369943 = 2054915) B2054915
theorem B2058119 : Blo 539803 2058119 := bstep (se 1 (by rfl) ⟨1543589, by rfl⟩ : syracuseStep 2058119 = 3087179) B3087179
theorem B608143 : Blo 539803 608143 := bstep (se 1 (by rfl) ⟨456107, by rfl⟩ : syracuseStep 608143 = 912215) B912215
theorem B1025939 : Blo 539803 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B542607 : Blo 539803 542607 := bstep (se 1 (by rfl) ⟨406955, by rfl⟩ : syracuseStep 542607 = 813911) B813911
theorem B1542041 : Blo 539803 1542041 := bstep (se 2 (by rfl) ⟨578265, by rfl⟩ : syracuseStep 1542041 = 1156531) B1156531
theorem B812987 : Blo 539803 812987 := bstep (se 1 (by rfl) ⟨609740, by rfl⟩ : syracuseStep 812987 = 1219481) B1219481
theorem B542651 : Blo 539803 542651 := bstep (se 1 (by rfl) ⟨406988, by rfl⟩ : syracuseStep 542651 = 813977) B813977
theorem B2738123 : Blo 539803 2738123 := bstep (se 1 (by rfl) ⟨2053592, by rfl⟩ : syracuseStep 2738123 = 4107185) B4107185
theorem B542599 : Blo 539803 542599 := bstep (se 1 (by rfl) ⟨406949, by rfl⟩ : syracuseStep 542599 = 813899) B813899
theorem B813047 : Blo 539803 813047 := bstep (se 1 (by rfl) ⟨609785, by rfl⟩ : syracuseStep 813047 = 1219571) B1219571
theorem B542727 : Blo 539803 542727 := bstep (se 1 (by rfl) ⟨407045, by rfl⟩ : syracuseStep 542727 = 814091) B814091
theorem B813071 : Blo 539803 813071 := bstep (se 1 (by rfl) ⟨609803, by rfl⟩ : syracuseStep 813071 = 1219607) B1219607
theorem B542735 : Blo 539803 542735 := bstep (se 1 (by rfl) ⟨407051, by rfl⟩ : syracuseStep 542735 = 814103) B814103
theorem B1370155 : Blo 539803 1370155 := bstep (se 1 (by rfl) ⟨1027616, by rfl⟩ : syracuseStep 1370155 = 2055233) B2055233
theorem B813113 : Blo 539803 813113 := bstep (se 2 (by rfl) ⟨304917, by rfl⟩ : syracuseStep 813113 = 609835) B609835
theorem B542779 : Blo 539803 542779 := bstep (se 1 (by rfl) ⟨407084, by rfl⟩ : syracuseStep 542779 = 814169) B814169
theorem B1828925 : Blo 539803 1828925 := bstep (se 3 (by rfl) ⟨342923, by rfl⟩ : syracuseStep 1828925 = 685847) B685847
theorem B911479 : Blo 539803 911479 := bstep (se 1 (by rfl) ⟨683609, by rfl⟩ : syracuseStep 911479 = 1367219) B1367219
theorem B1738871 : Blo 539803 1738871 := bstep (se 1 (by rfl) ⟨1304153, by rfl⟩ : syracuseStep 1738871 = 2608307) B2608307
theorem B813191 : Blo 539803 813191 := bstep (se 1 (by rfl) ⟨609893, by rfl⟩ : syracuseStep 813191 = 1219787) B1219787
theorem B813227 : Blo 539803 813227 := bstep (se 1 (by rfl) ⟨609920, by rfl⟩ : syracuseStep 813227 = 1219841) B1219841
theorem B1370297 : Blo 539803 1370297 := bstep (se 2 (by rfl) ⟨513861, by rfl⟩ : syracuseStep 1370297 = 1027723) B1027723
theorem B813257 : Blo 539803 813257 := bstep (se 2 (by rfl) ⟨304971, by rfl⟩ : syracuseStep 813257 = 609943) B609943
theorem B10381553 : Blo 539803 10381553 := bstep (se 2 (by rfl) ⟨3893082, by rfl⟩ : syracuseStep 10381553 = 7786165) B7786165
theorem B2738447 : Blo 539803 2738447 := bstep (se 1 (by rfl) ⟨2053835, by rfl⟩ : syracuseStep 2738447 = 4107671) B4107671
theorem B1157419 : Blo 539803 1157419 := bstep (se 1 (by rfl) ⟨868064, by rfl⟩ : syracuseStep 1157419 = 1736129) B1736129
theorem B911675 : Blo 539803 911675 := bstep (se 1 (by rfl) ⟨683756, by rfl⟩ : syracuseStep 911675 = 1367513) B1367513
theorem B813371 : Blo 539803 813371 := bstep (se 1 (by rfl) ⟨610028, by rfl⟩ : syracuseStep 813371 = 1220057) B1220057
theorem B4696379 : Blo 539803 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B813431 : Blo 539803 813431 := bstep (se 1 (by rfl) ⟨610073, by rfl⟩ : syracuseStep 813431 = 1220147) B1220147
theorem B1214855 : Blo 539803 1214855 := bstep (se 1 (by rfl) ⟨911141, by rfl⟩ : syracuseStep 1214855 = 1822283) B1822283
theorem B608647 : Blo 539803 608647 := bstep (se 1 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 608647 = 912971) B912971
theorem B3705223 : Blo 539803 3705223 := bstep (se 1 (by rfl) ⟨2778917, by rfl⟩ : syracuseStep 3705223 = 5557835) B5557835
theorem B813455 : Blo 539803 813455 := bstep (se 1 (by rfl) ⟨610091, by rfl⟩ : syracuseStep 813455 = 1220183) B1220183
theorem B813497 : Blo 539803 813497 := bstep (se 2 (by rfl) ⟨305061, by rfl⟩ : syracuseStep 813497 = 610123) B610123
theorem B2779595 : Blo 539803 2779595 := bstep (se 1 (by rfl) ⟨2084696, by rfl⟩ : syracuseStep 2779595 = 4169393) B4169393
theorem B813575 : Blo 539803 813575 := bstep (se 1 (by rfl) ⟨610181, by rfl⟩ : syracuseStep 813575 = 1220363) B1220363
theorem B772615 : Blo 539803 772615 := bstep (se 1 (by rfl) ⟨579461, by rfl⟩ : syracuseStep 772615 = 1158923) B1158923
theorem B813611 : Blo 539803 813611 := bstep (se 1 (by rfl) ⟨610208, by rfl⟩ : syracuseStep 813611 = 1220417) B1220417
theorem B1215035 : Blo 539803 1215035 := bstep (se 1 (by rfl) ⟨911276, by rfl⟩ : syracuseStep 1215035 = 1822553) B1822553
theorem B608827 : Blo 539803 608827 := bstep (se 1 (by rfl) ⟨456620, by rfl⟩ : syracuseStep 608827 = 913241) B913241
theorem B2345539 : Blo 539803 2345539 := bstep (se 1 (by rfl) ⟨1759154, by rfl⟩ : syracuseStep 2345539 = 3518309) B3518309
theorem B813641 : Blo 539803 813641 := bstep (se 2 (by rfl) ⟨305115, by rfl⟩ : syracuseStep 813641 = 610231) B610231
theorem B1215161 : Blo 539803 1215161 := bstep (se 2 (by rfl) ⟨455685, by rfl⟩ : syracuseStep 1215161 = 911371) B911371
theorem B813755 : Blo 539803 813755 := bstep (se 1 (by rfl) ⟨610316, by rfl⟩ : syracuseStep 813755 = 1220633) B1220633
theorem B912073 : Blo 539803 912073 := bstep (se 2 (by rfl) ⟨342027, by rfl⟩ : syracuseStep 912073 = 684055) B684055
theorem B813815 : Blo 539803 813815 := bstep (se 1 (by rfl) ⟨610361, by rfl⟩ : syracuseStep 813815 = 1220723) B1220723
theorem B3074831 : Blo 539803 3074831 := bstep (se 1 (by rfl) ⟨2306123, by rfl⟩ : syracuseStep 3074831 = 4612247) B4612247
theorem B7506703 : Blo 539803 7506703 := bstep (se 1 (by rfl) ⟨5630027, by rfl⟩ : syracuseStep 7506703 = 11260055) B11260055
theorem B2116367 : Blo 539803 2116367 := bstep (se 1 (by rfl) ⟨1587275, by rfl⟩ : syracuseStep 2116367 = 3174551) B3174551
theorem B813839 : Blo 539803 813839 := bstep (se 1 (by rfl) ⟨610379, by rfl⟩ : syracuseStep 813839 = 1220759) B1220759
theorem B4156211 : Blo 539803 4156211 := bstep (se 1 (by rfl) ⟨3117158, by rfl⟩ : syracuseStep 4156211 = 6234317) B6234317
theorem B813881 : Blo 539803 813881 := bstep (se 2 (by rfl) ⟨305205, by rfl⟩ : syracuseStep 813881 = 610411) B610411
theorem B2747195 : Blo 539803 2747195 := bstep (se 1 (by rfl) ⟨2060396, by rfl⟩ : syracuseStep 2747195 = 4120793) B4120793
theorem B3459955 : Blo 539803 3459955 := bstep (se 1 (by rfl) ⟨2594966, by rfl⟩ : syracuseStep 3459955 = 5189933) B5189933
theorem B3083123 : Blo 539803 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B813959 : Blo 539803 813959 := bstep (se 1 (by rfl) ⟨610469, by rfl⟩ : syracuseStep 813959 = 1220939) B1220939
theorem B813995 : Blo 539803 813995 := bstep (se 1 (by rfl) ⟨610496, by rfl⟩ : syracuseStep 813995 = 1220993) B1220993
theorem B986041 : Blo 539803 986041 := bstep (se 2 (by rfl) ⟨369765, by rfl⟩ : syracuseStep 986041 = 739531) B739531
theorem B814025 : Blo 539803 814025 := bstep (se 2 (by rfl) ⟨305259, by rfl⟩ : syracuseStep 814025 = 610519) B610519
theorem B2747357 : Blo 539803 2747357 := bstep (se 3 (by rfl) ⟨515129, by rfl⟩ : syracuseStep 2747357 = 1030259) B1030259
theorem B3075083 : Blo 539803 3075083 := bstep (se 1 (by rfl) ⟨2306312, by rfl⟩ : syracuseStep 3075083 = 4612625) B4612625
theorem B1215503 : Blo 539803 1215503 := bstep (se 1 (by rfl) ⟨911627, by rfl⟩ : syracuseStep 1215503 = 1823255) B1823255
theorem B609295 : Blo 539803 609295 := bstep (se 1 (by rfl) ⟨456971, by rfl⟩ : syracuseStep 609295 = 913943) B913943
theorem B1215521 : Blo 539803 1215521 := bstep (se 2 (by rfl) ⟨455820, by rfl⟩ : syracuseStep 1215521 = 911641) B911641
theorem B814139 : Blo 539803 814139 := bstep (se 1 (by rfl) ⟨610604, by rfl⟩ : syracuseStep 814139 = 1221209) B1221209
theorem B1543283 : Blo 539803 1543283 := bstep (se 1 (by rfl) ⟨1157462, by rfl⟩ : syracuseStep 1543283 = 2314925) B2314925
theorem B814199 : Blo 539803 814199 := bstep (se 1 (by rfl) ⟨610649, by rfl⟩ : syracuseStep 814199 = 1221299) B1221299
theorem B822415 : Blo 539803 822415 := bstep (se 1 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 822415 = 1233623) B1233623
theorem B1371289 : Blo 539803 1371289 := bstep (se 2 (by rfl) ⟨514233, by rfl⟩ : syracuseStep 1371289 = 1028467) B1028467
theorem B683255 : Blo 539803 683255 := bstep (se 1 (by rfl) ⟨512441, by rfl⟩ : syracuseStep 683255 = 1024883) B1024883
theorem B1027343 : Blo 539803 1027343 := bstep (se 1 (by rfl) ⟨770507, by rfl⟩ : syracuseStep 1027343 = 1541015) B1541015
theorem B2747681 : Blo 539803 2747681 := bstep (se 2 (by rfl) ⟨1030380, by rfl⟩ : syracuseStep 2747681 = 2060761) B2060761
theorem B650539 : Blo 539803 650539 := bstep (se 1 (by rfl) ⟨487904, by rfl⟩ : syracuseStep 650539 = 975809) B975809
theorem B1731899 : Blo 539803 1731899 := bstep (se 1 (by rfl) ⟨1298924, by rfl⟩ : syracuseStep 1731899 = 2597849) B2597849
theorem B3083579 : Blo 539803 3083579 := bstep (se 1 (by rfl) ⟨2312684, by rfl⟩ : syracuseStep 3083579 = 4625369) B4625369
theorem B1371451 : Blo 539803 1371451 := bstep (se 1 (by rfl) ⟨1028588, by rfl⟩ : syracuseStep 1371451 = 2057177) B2057177
theorem B1822067 : Blo 539803 1822067 := bstep (se 1 (by rfl) ⟨1366550, by rfl⟩ : syracuseStep 1822067 = 2733101) B2733101
theorem B1215863 : Blo 539803 1215863 := bstep (se 1 (by rfl) ⟨911897, by rfl⟩ : syracuseStep 1215863 = 1823795) B1823795
theorem B912775 : Blo 539803 912775 := bstep (se 1 (by rfl) ⟨684581, by rfl⟩ : syracuseStep 912775 = 1369163) B1369163
theorem B2084231 : Blo 539803 2084231 := bstep (se 1 (by rfl) ⟨1563173, by rfl⟩ : syracuseStep 2084231 = 3126347) B3126347
theorem B683407 : Blo 539803 683407 := bstep (se 1 (by rfl) ⟨512555, by rfl⟩ : syracuseStep 683407 = 1025111) B1025111
theorem B2051513 : Blo 539803 2051513 := bstep (se 2 (by rfl) ⟨769317, by rfl⟩ : syracuseStep 2051513 = 1538635) B1538635
theorem B1830329 : Blo 539803 1830329 := bstep (se 2 (by rfl) ⟨686373, by rfl⟩ : syracuseStep 1830329 = 1372747) B1372747
theorem B1371593 : Blo 539803 1371593 := bstep (se 2 (by rfl) ⟨514347, by rfl⟩ : syracuseStep 1371593 = 1028695) B1028695
theorem B6598097 : Blo 539803 6598097 := bstep (se 2 (by rfl) ⟨2474286, by rfl⟩ : syracuseStep 6598097 = 4948573) B4948573
theorem B4115933 : Blo 539803 4115933 := bstep (se 3 (by rfl) ⟨771737, by rfl⟩ : syracuseStep 4115933 = 1543475) B1543475
theorem B7400963 : Blo 539803 7400963 := bstep (se 1 (by rfl) ⟨5550722, by rfl⟩ : syracuseStep 7400963 = 11101445) B11101445
theorem B609799 : Blo 539803 609799 := bstep (se 1 (by rfl) ⟨457349, by rfl⟩ : syracuseStep 609799 = 914699) B914699
theorem B1216043 : Blo 539803 1216043 := bstep (se 1 (by rfl) ⟨912032, by rfl⟩ : syracuseStep 1216043 = 1824065) B1824065
theorem B683579 : Blo 539803 683579 := bstep (se 1 (by rfl) ⟨512684, by rfl⟩ : syracuseStep 683579 = 1025369) B1025369
theorem B1158803 : Blo 539803 1158803 := bstep (se 1 (by rfl) ⟨869102, by rfl⟩ : syracuseStep 1158803 = 1738205) B1738205
theorem B1560217 : Blo 539803 1560217 := bstep (se 2 (by rfl) ⟨585081, by rfl⟩ : syracuseStep 1560217 = 1170163) B1170163
theorem B650923 : Blo 539803 650923 := bstep (se 1 (by rfl) ⟨488192, by rfl⟩ : syracuseStep 650923 = 976385) B976385
theorem B609979 : Blo 539803 609979 := bstep (se 1 (by rfl) ⟨457484, by rfl⟩ : syracuseStep 609979 = 914969) B914969
theorem B2739905 : Blo 539803 2739905 := bstep (se 2 (by rfl) ⟨1027464, by rfl⟩ : syracuseStep 2739905 = 2054929) B2054929
theorem B11128549 : Blo 539803 11128549 := bstep (se 4 (by rfl) ⟨1043301, by rfl⟩ : syracuseStep 11128549 = 2086603) B2086603
theorem B4615937 : Blo 539803 4615937 := bstep (se 2 (by rfl) ⟨1730976, by rfl⟩ : syracuseStep 4615937 = 3461953) B3461953
theorem B1371937 : Blo 539803 1371937 := bstep (se 2 (by rfl) ⟨514476, by rfl⟩ : syracuseStep 1371937 = 1028953) B1028953
theorem B5279525 : Blo 539803 5279525 := bstep (se 4 (by rfl) ⟨494955, by rfl⟩ : syracuseStep 5279525 = 989911) B989911
theorem B1027883 : Blo 539803 1027883 := bstep (se 1 (by rfl) ⟨770912, by rfl⟩ : syracuseStep 1027883 = 1541825) B1541825
theorem B5009203 : Blo 539803 5009203 := bstep (se 1 (by rfl) ⟨3756902, by rfl⟩ : syracuseStep 5009203 = 7513805) B7513805
theorem B2600849 : Blo 539803 2600849 := bstep (se 2 (by rfl) ⟨975318, by rfl⟩ : syracuseStep 2600849 = 1950637) B1950637
theorem B1216403 : Blo 539803 1216403 := bstep (se 1 (by rfl) ⟨912302, by rfl⟩ : syracuseStep 1216403 = 1824605) B1824605
theorem B1216457 : Blo 539803 1216457 := bstep (se 2 (by rfl) ⟨456171, by rfl⟩ : syracuseStep 1216457 = 912343) B912343
theorem B823241 : Blo 539803 823241 := bstep (se 2 (by rfl) ⟨308715, by rfl⟩ : syracuseStep 823241 = 617431) B617431
theorem B1830923 : Blo 539803 1830923 := bstep (se 1 (by rfl) ⟨1373192, by rfl⟩ : syracuseStep 1830923 = 2746385) B2746385
theorem B913423 : Blo 539803 913423 := bstep (se 1 (by rfl) ⟨685067, by rfl⟩ : syracuseStep 913423 = 1370135) B1370135
theorem B45117461 : Blo 539803 45117461 := bstep (se 6 (by rfl) ⟨1057440, by rfl⟩ : syracuseStep 45117461 = 2114881) B2114881
theorem B1831031 : Blo 539803 1831031 := bstep (se 1 (by rfl) ⟨1373273, by rfl⟩ : syracuseStep 1831031 = 2746547) B2746547
theorem B610447 : Blo 539803 610447 := bstep (se 1 (by rfl) ⟨457835, by rfl⟩ : syracuseStep 610447 = 915671) B915671
theorem B3076289 : Blo 539803 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B3084581 : Blo 539803 3084581 := bstep (se 4 (by rfl) ⟨289179, by rfl⟩ : syracuseStep 3084581 = 578359) B578359
theorem B1462589 : Blo 539803 1462589 := bstep (se 3 (by rfl) ⟨274235, by rfl⟩ : syracuseStep 1462589 = 548471) B548471
theorem B1372535 : Blo 539803 1372535 := bstep (se 1 (by rfl) ⟨1029401, by rfl⟩ : syracuseStep 1372535 = 2058803) B2058803
theorem B2052499 : Blo 539803 2052499 := bstep (se 1 (by rfl) ⟨1539374, by rfl⟩ : syracuseStep 2052499 = 3078749) B3078749
theorem B1560979 : Blo 539803 1560979 := bstep (se 1 (by rfl) ⟨1170734, by rfl⟩ : syracuseStep 1560979 = 2341469) B2341469
theorem B684551 : Blo 539803 684551 := bstep (se 1 (by rfl) ⟨513413, by rfl⟩ : syracuseStep 684551 = 1026827) B1026827
theorem B2249227 : Blo 539803 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B913963 : Blo 539803 913963 := bstep (se 1 (by rfl) ⟨685472, by rfl⟩ : syracuseStep 913963 = 1370945) B1370945
theorem B2085419 : Blo 539803 2085419 := bstep (se 1 (by rfl) ⟨1564064, by rfl⟩ : syracuseStep 2085419 = 3128129) B3128129
theorem B6566467 : Blo 539803 6566467 := bstep (se 1 (by rfl) ⟨4924850, by rfl⟩ : syracuseStep 6566467 = 9849701) B9849701
theorem B1806967 : Blo 539803 1806967 := bstep (se 1 (by rfl) ⟨1355225, by rfl⟩ : syracuseStep 1806967 = 2710451) B2710451
theorem B1217159 : Blo 539803 1217159 := bstep (se 1 (by rfl) ⟨912869, by rfl⟩ : syracuseStep 1217159 = 1825739) B1825739
theorem B914105 : Blo 539803 914105 := bstep (se 2 (by rfl) ⟨342789, by rfl⟩ : syracuseStep 914105 = 685579) B685579
theorem B783049 : Blo 539803 783049 := bstep (se 2 (by rfl) ⟨293643, by rfl⟩ : syracuseStep 783049 = 587287) B587287
theorem B1831625 : Blo 539803 1831625 := bstep (se 2 (by rfl) ⟨686859, by rfl⟩ : syracuseStep 1831625 = 1373719) B1373719
theorem B2921197 : Blo 539803 2921197 := bstep (se 3 (by rfl) ⟨547724, by rfl⟩ : syracuseStep 2921197 = 1095449) B1095449
theorem B3085037 : Blo 539803 3085037 := bstep (se 3 (by rfl) ⟨578444, by rfl⟩ : syracuseStep 3085037 = 1156889) B1156889
theorem B1299233 : Blo 539803 1299233 := bstep (se 2 (by rfl) ⟨487212, by rfl⟩ : syracuseStep 1299233 = 974425) B974425
theorem B2306875 : Blo 539803 2306875 := bstep (se 1 (by rfl) ⟨1730156, by rfl⟩ : syracuseStep 2306875 = 3460313) B3460313
theorem B1217339 : Blo 539803 1217339 := bstep (se 1 (by rfl) ⟨913004, by rfl⟩ : syracuseStep 1217339 = 1826009) B1826009
theorem B4633433 : Blo 539803 4633433 := bstep (se 2 (by rfl) ⟨1737537, by rfl⟩ : syracuseStep 4633433 = 3475075) B3475075
theorem B1028999 : Blo 539803 1028999 := bstep (se 1 (by rfl) ⟨771749, by rfl⟩ : syracuseStep 1028999 = 1543499) B1543499
theorem B14062517 : Blo 539803 14062517 := bstep (se 5 (by rfl) ⟨659180, by rfl⟩ : syracuseStep 14062517 = 1318361) B1318361
theorem B1217465 : Blo 539803 1217465 := bstep (se 2 (by rfl) ⟨456549, by rfl⟩ : syracuseStep 1217465 = 913099) B913099
theorem B2741201 : Blo 539803 2741201 := bstep (se 2 (by rfl) ⟨1027950, by rfl⟩ : syracuseStep 2741201 = 2055901) B2055901
theorem B1094671 : Blo 539803 1094671 := bstep (se 1 (by rfl) ⟨821003, by rfl⟩ : syracuseStep 1094671 = 1642007) B1642007
theorem B3470359 : Blo 539803 3470359 := bstep (se 1 (by rfl) ⟨2602769, by rfl⟩ : syracuseStep 3470359 = 5205539) B5205539
theorem B865399 : Blo 539803 865399 := bstep (se 1 (by rfl) ⟨649049, by rfl⟩ : syracuseStep 865399 = 1298099) B1298099
theorem B685199 : Blo 539803 685199 := bstep (se 1 (by rfl) ⟨513899, by rfl⟩ : syracuseStep 685199 = 1027799) B1027799
theorem B1537177 : Blo 539803 1537177 := bstep (se 2 (by rfl) ⟨576441, by rfl⟩ : syracuseStep 1537177 = 1152883) B1152883
theorem B1217807 : Blo 539803 1217807 := bstep (se 1 (by rfl) ⟨913355, by rfl⟩ : syracuseStep 1217807 = 1826711) B1826711
theorem B1217825 : Blo 539803 1217825 := bstep (se 2 (by rfl) ⟨456684, by rfl⟩ : syracuseStep 1217825 = 913369) B913369
theorem B914807 : Blo 539803 914807 := bstep (se 1 (by rfl) ⟨686105, by rfl⟩ : syracuseStep 914807 = 1372211) B1372211
theorem B3339667 : Blo 539803 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B1029523 : Blo 539803 1029523 := bstep (se 1 (by rfl) ⟨772142, by rfl⟩ : syracuseStep 1029523 = 1544285) B1544285
theorem B1734041 : Blo 539803 1734041 := bstep (se 2 (by rfl) ⟨650265, by rfl⟩ : syracuseStep 1734041 = 1300531) B1300531
theorem B3085721 : Blo 539803 3085721 := bstep (se 2 (by rfl) ⟨1157145, by rfl⟩ : syracuseStep 3085721 = 2314291) B2314291
theorem B1955339 : Blo 539803 1955339 := bstep (se 1 (by rfl) ⟨1466504, by rfl⟩ : syracuseStep 1955339 = 2933009) B2933009
theorem B5199389 : Blo 539803 5199389 := bstep (se 3 (by rfl) ⟨974885, by rfl⟩ : syracuseStep 5199389 = 1949771) B1949771
theorem B1218167 : Blo 539803 1218167 := bstep (se 1 (by rfl) ⟨913625, by rfl⟩ : syracuseStep 1218167 = 1827251) B1827251
theorem B1373831 : Blo 539803 1373831 := bstep (se 1 (by rfl) ⟨1030373, by rfl⟩ : syracuseStep 1373831 = 2060747) B2060747
theorem B1373881 : Blo 539803 1373881 := bstep (se 2 (by rfl) ⟨515205, by rfl⟩ : syracuseStep 1373881 = 1030411) B1030411
theorem B1218347 : Blo 539803 1218347 := bstep (se 1 (by rfl) ⟨913760, by rfl⟩ : syracuseStep 1218347 = 1827521) B1827521
theorem B915259 : Blo 539803 915259 := bstep (se 1 (by rfl) ⟨686444, by rfl⟩ : syracuseStep 915259 = 1372889) B1372889
theorem B47404865 : Blo 539803 47404865 := bstep (se 2 (by rfl) ⟨17776824, by rfl⟩ : syracuseStep 47404865 = 35553649) B35553649
theorem B11097931 : Blo 539803 11097931 := bstep (se 1 (by rfl) ⟨8323448, by rfl⟩ : syracuseStep 11097931 = 16646897) B16646897
theorem B1824659 : Blo 539803 1824659 := bstep (se 1 (by rfl) ⟨1368494, by rfl⟩ : syracuseStep 1824659 = 2736989) B2736989
theorem B915401 : Blo 539803 915401 := bstep (se 2 (by rfl) ⟨343275, by rfl⟩ : syracuseStep 915401 = 686551) B686551
theorem B86751245 : Blo 539803 86751245 := bstep (se 3 (by rfl) ⟨16265858, by rfl⟩ : syracuseStep 86751245 = 32531717) B32531717
theorem B2054231 : Blo 539803 2054231 := bstep (se 1 (by rfl) ⟨1540673, by rfl⟩ : syracuseStep 2054231 = 3081347) B3081347
theorem B972919 : Blo 539803 972919 := bstep (se 1 (by rfl) ⟨729689, by rfl⟩ : syracuseStep 972919 = 1459379) B1459379
theorem B2193527 : Blo 539803 2193527 := bstep (se 1 (by rfl) ⟨1645145, by rfl⟩ : syracuseStep 2193527 = 3290291) B3290291
theorem B1218707 : Blo 539803 1218707 := bstep (se 1 (by rfl) ⟨914030, by rfl⟩ : syracuseStep 1218707 = 1828061) B1828061
theorem B1218761 : Blo 539803 1218761 := bstep (se 2 (by rfl) ⟨457035, by rfl⟩ : syracuseStep 1218761 = 914071) B914071
theorem B2464015 : Blo 539803 2464015 := bstep (se 1 (by rfl) ⟨1848011, by rfl⟩ : syracuseStep 2464015 = 3696023) B3696023
theorem B2931059 : Blo 539803 2931059 := bstep (se 1 (by rfl) ⟨2198294, by rfl⟩ : syracuseStep 2931059 = 4396589) B4396589
theorem B1366571 : Blo 539803 1366571 := bstep (se 1 (by rfl) ⟨1024928, by rfl⟩ : syracuseStep 1366571 = 2049857) B2049857
theorem B2054717 : Blo 539803 2054717 := bstep (se 3 (by rfl) ⟨385259, by rfl⟩ : syracuseStep 2054717 = 770519) B770519
theorem B6232643 : Blo 539803 6232643 := bstep (se 1 (by rfl) ⟨4674482, by rfl⟩ : syracuseStep 6232643 = 9348965) B9348965
theorem B809735 : Blo 539803 809735 := bstep (se 1 (by rfl) ⟨607301, by rfl⟩ : syracuseStep 809735 = 1214603) B1214603
theorem B809771 : Blo 539803 809771 := bstep (se 1 (by rfl) ⟨607328, by rfl⟩ : syracuseStep 809771 = 1214657) B1214657
theorem B809801 : Blo 539803 809801 := bstep (se 2 (by rfl) ⟨303675, by rfl⟩ : syracuseStep 809801 = 607351) B607351
theorem B1522547 : Blo 539803 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B1219463 : Blo 539803 1219463 := bstep (se 1 (by rfl) ⟨914597, by rfl⟩ : syracuseStep 1219463 = 1829195) B1829195
theorem B11140021 : Blo 539803 11140021 := bstep (se 5 (by rfl) ⟨522188, by rfl⟩ : syracuseStep 11140021 = 1044377) B1044377
theorem B768953 : Blo 539803 768953 := bstep (se 2 (by rfl) ⟨288357, by rfl⟩ : syracuseStep 768953 = 576715) B576715
theorem B809915 : Blo 539803 809915 := bstep (se 1 (by rfl) ⟨607436, by rfl⟩ : syracuseStep 809915 = 1214873) B1214873
theorem B809975 : Blo 539803 809975 := bstep (se 1 (by rfl) ⟨607481, by rfl⟩ : syracuseStep 809975 = 1214963) B1214963
theorem B2595851 : Blo 539803 2595851 := bstep (se 1 (by rfl) ⟨1946888, by rfl⟩ : syracuseStep 2595851 = 3893777) B3893777
theorem B2743307 : Blo 539803 2743307 := bstep (se 1 (by rfl) ⟨2057480, by rfl⟩ : syracuseStep 2743307 = 4114961) B4114961
theorem B809999 : Blo 539803 809999 := bstep (se 1 (by rfl) ⟨607499, by rfl⟩ : syracuseStep 809999 = 1214999) B1214999
theorem B1506319 : Blo 539803 1506319 := bstep (se 1 (by rfl) ⟨1129739, by rfl⟩ : syracuseStep 1506319 = 2259479) B2259479
theorem B1539101 : Blo 539803 1539101 := bstep (se 3 (by rfl) ⟨288581, by rfl⟩ : syracuseStep 1539101 = 577163) B577163
theorem B810041 : Blo 539803 810041 := bstep (se 2 (by rfl) ⟨303765, by rfl⟩ : syracuseStep 810041 = 607531) B607531
theorem B1219643 : Blo 539803 1219643 := bstep (se 1 (by rfl) ⟨914732, by rfl⟩ : syracuseStep 1219643 = 1829465) B1829465
theorem B1973335 : Blo 539803 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B4996183 : Blo 539803 4996183 := bstep (se 1 (by rfl) ⟨3747137, by rfl⟩ : syracuseStep 4996183 = 7494275) B7494275
theorem B1645655 : Blo 539803 1645655 := bstep (se 1 (by rfl) ⟨1234241, by rfl⟩ : syracuseStep 1645655 = 2468483) B2468483
theorem B6151301 : Blo 539803 6151301 := bstep (se 4 (by rfl) ⟨576684, by rfl⟩ : syracuseStep 6151301 = 1153369) B1153369
theorem B810119 : Blo 539803 810119 := bstep (se 1 (by rfl) ⟨607589, by rfl⟩ : syracuseStep 810119 = 1215179) B1215179
theorem B695431 : Blo 539803 695431 := bstep (se 1 (by rfl) ⟨521573, by rfl⟩ : syracuseStep 695431 = 1043147) B1043147
theorem B810155 : Blo 539803 810155 := bstep (se 1 (by rfl) ⟨607616, by rfl⟩ : syracuseStep 810155 = 1215233) B1215233
theorem B2743469 : Blo 539803 2743469 := bstep (se 3 (by rfl) ⟨514400, by rfl⟩ : syracuseStep 2743469 = 1028801) B1028801
theorem B1219769 : Blo 539803 1219769 := bstep (se 2 (by rfl) ⟨457413, by rfl⟩ : syracuseStep 1219769 = 914827) B914827
theorem B539835 : Blo 539803 539835 := bstep (se 1 (by rfl) ⟨404876, by rfl⟩ : syracuseStep 539835 = 809753) B809753
theorem B810185 : Blo 539803 810185 := bstep (se 2 (by rfl) ⟨303819, by rfl⟩ : syracuseStep 810185 = 607639) B607639
theorem B1301761 : Blo 539803 1301761 := bstep (se 2 (by rfl) ⟨488160, by rfl⟩ : syracuseStep 1301761 = 976321) B976321
theorem B539911 : Blo 539803 539911 := bstep (se 1 (by rfl) ⟨404933, by rfl⟩ : syracuseStep 539911 = 809867) B809867
theorem B539919 : Blo 539803 539919 := bstep (se 1 (by rfl) ⟨404939, by rfl⟩ : syracuseStep 539919 = 809879) B809879
theorem B1826063 : Blo 539803 1826063 := bstep (se 1 (by rfl) ⟨1369547, by rfl⟩ : syracuseStep 1826063 = 2739095) B2739095
theorem B1465615 : Blo 539803 1465615 := bstep (se 1 (by rfl) ⟨1099211, by rfl⟩ : syracuseStep 1465615 = 2198423) B2198423
theorem B3079457 : Blo 539803 3079457 := bstep (se 2 (by rfl) ⟨1154796, by rfl⟩ : syracuseStep 3079457 = 2309593) B2309593
theorem B539963 : Blo 539803 539963 := bstep (se 1 (by rfl) ⟨404972, by rfl⟩ : syracuseStep 539963 = 809945) B809945
theorem B810299 : Blo 539803 810299 := bstep (se 1 (by rfl) ⟨607724, by rfl⟩ : syracuseStep 810299 = 1215449) B1215449
theorem B548155 : Blo 539803 548155 := bstep (se 1 (by rfl) ⟨411116, by rfl⟩ : syracuseStep 548155 = 822233) B822233
theorem B810359 : Blo 539803 810359 := bstep (se 1 (by rfl) ⟨607769, by rfl⟩ : syracuseStep 810359 = 1215539) B1215539
theorem B10132867 : Blo 539803 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B540039 : Blo 539803 540039 := bstep (se 1 (by rfl) ⟨405029, by rfl⟩ : syracuseStep 540039 = 810059) B810059
theorem B990599 : Blo 539803 990599 := bstep (se 1 (by rfl) ⟨742949, by rfl⟩ : syracuseStep 990599 = 1485899) B1485899
theorem B540047 : Blo 539803 540047 := bstep (se 1 (by rfl) ⟨405035, by rfl⟩ : syracuseStep 540047 = 810071) B810071
theorem B810383 : Blo 539803 810383 := bstep (se 1 (by rfl) ⟨607787, by rfl⟩ : syracuseStep 810383 = 1215575) B1215575
theorem B810425 : Blo 539803 810425 := bstep (se 2 (by rfl) ⟨303909, by rfl⟩ : syracuseStep 810425 = 607819) B607819
theorem B540091 : Blo 539803 540091 := bstep (se 1 (by rfl) ⟨405068, by rfl⟩ : syracuseStep 540091 = 810137) B810137
theorem B974281 : Blo 539803 974281 := bstep (se 2 (by rfl) ⟨365355, by rfl⟩ : syracuseStep 974281 = 730711) B730711
theorem B540167 : Blo 539803 540167 := bstep (se 1 (by rfl) ⟨405125, by rfl⟩ : syracuseStep 540167 = 810251) B810251
theorem B810503 : Blo 539803 810503 := bstep (se 1 (by rfl) ⟨607877, by rfl⟩ : syracuseStep 810503 = 1215755) B1215755
theorem B1367563 : Blo 539803 1367563 := bstep (se 1 (by rfl) ⟨1025672, by rfl⟩ : syracuseStep 1367563 = 2051345) B2051345
theorem B540175 : Blo 539803 540175 := bstep (se 1 (by rfl) ⟨405131, by rfl⟩ : syracuseStep 540175 = 810263) B810263
theorem B1220111 : Blo 539803 1220111 := bstep (se 1 (by rfl) ⟨915083, by rfl⟩ : syracuseStep 1220111 = 1830167) B1830167
theorem B1826333 : Blo 539803 1826333 := bstep (se 3 (by rfl) ⟨342437, by rfl⟩ : syracuseStep 1826333 = 684875) B684875
theorem B1220129 : Blo 539803 1220129 := bstep (se 2 (by rfl) ⟨457548, by rfl⟩ : syracuseStep 1220129 = 915097) B915097
theorem B810539 : Blo 539803 810539 := bstep (se 1 (by rfl) ⟨607904, by rfl⟩ : syracuseStep 810539 = 1215809) B1215809
theorem B1039915 : Blo 539803 1039915 := bstep (se 1 (by rfl) ⟨779936, by rfl⟩ : syracuseStep 1039915 = 1559873) B1559873
theorem B540219 : Blo 539803 540219 := bstep (se 1 (by rfl) ⟨405164, by rfl⟩ : syracuseStep 540219 = 810329) B810329
theorem B810569 : Blo 539803 810569 := bstep (se 2 (by rfl) ⟨303963, by rfl⟩ : syracuseStep 810569 = 607927) B607927
theorem B540295 : Blo 539803 540295 := bstep (se 1 (by rfl) ⟨405221, by rfl⟩ : syracuseStep 540295 = 810443) B810443
theorem B540303 : Blo 539803 540303 := bstep (se 1 (by rfl) ⟨405227, by rfl⟩ : syracuseStep 540303 = 810455) B810455
theorem B1367705 : Blo 539803 1367705 := bstep (se 2 (by rfl) ⟨512889, by rfl⟩ : syracuseStep 1367705 = 1025779) B1025779
theorem B6160049 : Blo 539803 6160049 := bstep (se 2 (by rfl) ⟨2310018, by rfl⟩ : syracuseStep 6160049 = 4620037) B4620037
theorem B5193395 : Blo 539803 5193395 := bstep (se 1 (by rfl) ⟨3895046, by rfl⟩ : syracuseStep 5193395 = 7790093) B7790093
theorem B540347 : Blo 539803 540347 := bstep (se 1 (by rfl) ⟨405260, by rfl⟩ : syracuseStep 540347 = 810521) B810521
theorem B810683 : Blo 539803 810683 := bstep (se 1 (by rfl) ⟨608012, by rfl⟩ : syracuseStep 810683 = 1216025) B1216025
theorem B2924225 : Blo 539803 2924225 := bstep (se 2 (by rfl) ⟨1096584, by rfl⟩ : syracuseStep 2924225 = 2193169) B2193169
theorem B1539785 : Blo 539803 1539785 := bstep (se 2 (by rfl) ⟨577419, by rfl⟩ : syracuseStep 1539785 = 1154839) B1154839
theorem B810743 : Blo 539803 810743 := bstep (se 1 (by rfl) ⟨608057, by rfl⟩ : syracuseStep 810743 = 1216115) B1216115
theorem B540423 : Blo 539803 540423 := bstep (se 1 (by rfl) ⟨405317, by rfl⟩ : syracuseStep 540423 = 810635) B810635
theorem B540431 : Blo 539803 540431 := bstep (se 1 (by rfl) ⟨405323, by rfl⟩ : syracuseStep 540431 = 810647) B810647
theorem B810767 : Blo 539803 810767 := bstep (se 1 (by rfl) ⟨608075, by rfl⟩ : syracuseStep 810767 = 1216151) B1216151
theorem B810809 : Blo 539803 810809 := bstep (se 2 (by rfl) ⟨304053, by rfl⟩ : syracuseStep 810809 = 608107) B608107
theorem B1367867 : Blo 539803 1367867 := bstep (se 1 (by rfl) ⟨1025900, by rfl⟩ : syracuseStep 1367867 = 2051801) B2051801
theorem B540475 : Blo 539803 540475 := bstep (se 1 (by rfl) ⟨405356, by rfl⟩ : syracuseStep 540475 = 810713) B810713
theorem B1220471 : Blo 539803 1220471 := bstep (se 1 (by rfl) ⟨915353, by rfl⟩ : syracuseStep 1220471 = 1830707) B1830707
theorem B540551 : Blo 539803 540551 := bstep (se 1 (by rfl) ⟨405413, by rfl⟩ : syracuseStep 540551 = 810827) B810827
theorem B810887 : Blo 539803 810887 := bstep (se 1 (by rfl) ⟨608165, by rfl⟩ : syracuseStep 810887 = 1216331) B1216331
theorem B769927 : Blo 539803 769927 := bstep (se 1 (by rfl) ⟨577445, by rfl⟩ : syracuseStep 769927 = 1154891) B1154891
theorem B540559 : Blo 539803 540559 := bstep (se 1 (by rfl) ⟨405419, by rfl⟩ : syracuseStep 540559 = 810839) B810839
theorem B2736017 : Blo 539803 2736017 := bstep (se 2 (by rfl) ⟨1026006, by rfl⟩ : syracuseStep 2736017 = 2052013) B2052013
theorem B810923 : Blo 539803 810923 := bstep (se 1 (by rfl) ⟨608192, by rfl⟩ : syracuseStep 810923 = 1216385) B1216385
theorem B540603 : Blo 539803 540603 := bstep (se 1 (by rfl) ⟨405452, by rfl⟩ : syracuseStep 540603 = 810905) B810905
theorem B810953 : Blo 539803 810953 := bstep (se 2 (by rfl) ⟨304107, by rfl⟩ : syracuseStep 810953 = 608215) B608215
theorem B1220615 : Blo 539803 1220615 := bstep (se 1 (by rfl) ⟨915461, by rfl⟩ : syracuseStep 1220615 = 1830923) B1830923
theorem B3080207 : Blo 539803 3080207 := bstep (se 1 (by rfl) ⟨2310155, by rfl⟩ : syracuseStep 3080207 = 4620311) B4620311
theorem B540711 : Blo 539803 540711 := bstep (se 1 (by rfl) ⟨405533, by rfl⟩ : syracuseStep 540711 = 811067) B811067
theorem B1826873 : Blo 539803 1826873 := bstep (se 2 (by rfl) ⟨685077, by rfl⟩ : syracuseStep 1826873 = 1370155) B1370155
theorem B4104269 : Blo 539803 4104269 := bstep (se 3 (by rfl) ⟨769550, by rfl⟩ : syracuseStep 4104269 = 1539101) B1539101
theorem B540751 : Blo 539803 540751 := bstep (se 1 (by rfl) ⟨405563, by rfl⟩ : syracuseStep 540751 = 811127) B811127
theorem B1220687 : Blo 539803 1220687 := bstep (se 1 (by rfl) ⟨915515, by rfl⟩ : syracuseStep 1220687 = 1831031) B1831031
theorem B540767 : Blo 539803 540767 := bstep (se 1 (by rfl) ⟨405575, by rfl⟩ : syracuseStep 540767 = 811151) B811151
theorem B540795 : Blo 539803 540795 := bstep (se 1 (by rfl) ⟨405596, by rfl⟩ : syracuseStep 540795 = 811193) B811193
theorem B868475 : Blo 539803 868475 := bstep (se 1 (by rfl) ⟨651356, by rfl⟩ : syracuseStep 868475 = 1302713) B1302713
theorem B540847 : Blo 539803 540847 := bstep (se 1 (by rfl) ⟨405635, by rfl⟩ : syracuseStep 540847 = 811271) B811271
theorem B2056387 : Blo 539803 2056387 := bstep (se 1 (by rfl) ⟨1542290, by rfl⟩ : syracuseStep 2056387 = 3084581) B3084581
theorem B540871 : Blo 539803 540871 := bstep (se 1 (by rfl) ⟨405653, by rfl⟩ : syracuseStep 540871 = 811307) B811307
theorem B975059 : Blo 539803 975059 := bstep (se 1 (by rfl) ⟨731294, by rfl⟩ : syracuseStep 975059 = 1462589) B1462589
theorem B540891 : Blo 539803 540891 := bstep (se 1 (by rfl) ⟨405668, by rfl⟩ : syracuseStep 540891 = 811337) B811337
theorem B540967 : Blo 539803 540967 := bstep (se 1 (by rfl) ⟨405725, by rfl⟩ : syracuseStep 540967 = 811451) B811451
theorem B5849405 : Blo 539803 5849405 := bstep (se 3 (by rfl) ⟨1096763, by rfl⟩ : syracuseStep 5849405 = 2193527) B2193527
theorem B2974013 : Blo 539803 2974013 := bstep (se 3 (by rfl) ⟨557627, by rfl⟩ : syracuseStep 2974013 = 1115255) B1115255
theorem B541007 : Blo 539803 541007 := bstep (se 1 (by rfl) ⟨405755, by rfl⟩ : syracuseStep 541007 = 811511) B811511
theorem B541023 : Blo 539803 541023 := bstep (se 1 (by rfl) ⟨405767, by rfl⟩ : syracuseStep 541023 = 811535) B811535
theorem B3285353 : Blo 539803 3285353 := bstep (se 2 (by rfl) ⟨1232007, by rfl⟩ : syracuseStep 3285353 = 2464015) B2464015
theorem B770411 : Blo 539803 770411 := bstep (se 1 (by rfl) ⟨577808, by rfl⟩ : syracuseStep 770411 = 1155617) B1155617
theorem B541051 : Blo 539803 541051 := bstep (se 1 (by rfl) ⟨405788, by rfl⟩ : syracuseStep 541051 = 811577) B811577
theorem B1827197 : Blo 539803 1827197 := bstep (se 3 (by rfl) ⟨342599, by rfl⟩ : syracuseStep 1827197 = 685199) B685199
theorem B811439 : Blo 539803 811439 := bstep (se 1 (by rfl) ⟨608579, by rfl⟩ : syracuseStep 811439 = 1217159) B1217159
theorem B541103 : Blo 539803 541103 := bstep (se 1 (by rfl) ⟨405827, by rfl⟩ : syracuseStep 541103 = 811655) B811655
theorem B541127 : Blo 539803 541127 := bstep (se 1 (by rfl) ⟨405845, by rfl⟩ : syracuseStep 541127 = 811691) B811691
theorem B4161995 : Blo 539803 4161995 := bstep (se 1 (by rfl) ⟨3121496, by rfl⟩ : syracuseStep 4161995 = 6242993) B6242993
theorem B541147 : Blo 539803 541147 := bstep (se 1 (by rfl) ⟨405860, by rfl⟩ : syracuseStep 541147 = 811721) B811721
theorem B1221083 : Blo 539803 1221083 := bstep (se 1 (by rfl) ⟨915812, by rfl⟩ : syracuseStep 1221083 = 1831625) B1831625
theorem B2056691 : Blo 539803 2056691 := bstep (se 1 (by rfl) ⟨1542518, by rfl⟩ : syracuseStep 2056691 = 3085037) B3085037
theorem B811529 : Blo 539803 811529 := bstep (se 2 (by rfl) ⟨304323, by rfl⟩ : syracuseStep 811529 = 608647) B608647
theorem B4940297 : Blo 539803 4940297 := bstep (se 2 (by rfl) ⟨1852611, by rfl⟩ : syracuseStep 4940297 = 3705223) B3705223
theorem B2736665 : Blo 539803 2736665 := bstep (se 2 (by rfl) ⟨1026249, by rfl⟩ : syracuseStep 2736665 = 2052499) B2052499
theorem B2081305 : Blo 539803 2081305 := bstep (se 2 (by rfl) ⟨780489, by rfl⟩ : syracuseStep 2081305 = 1560979) B1560979
theorem B811559 : Blo 539803 811559 := bstep (se 1 (by rfl) ⟨608669, by rfl⟩ : syracuseStep 811559 = 1217339) B1217339
theorem B541223 : Blo 539803 541223 := bstep (se 1 (by rfl) ⟨405917, by rfl⟩ : syracuseStep 541223 = 811835) B811835
theorem B3088955 : Blo 539803 3088955 := bstep (se 1 (by rfl) ⟨2316716, by rfl⟩ : syracuseStep 3088955 = 4633433) B4633433
theorem B541263 : Blo 539803 541263 := bstep (se 1 (by rfl) ⟨405947, by rfl⟩ : syracuseStep 541263 = 811895) B811895
theorem B541279 : Blo 539803 541279 := bstep (se 1 (by rfl) ⟨405959, by rfl⟩ : syracuseStep 541279 = 811919) B811919
theorem B811643 : Blo 539803 811643 := bstep (se 1 (by rfl) ⟨608732, by rfl⟩ : syracuseStep 811643 = 1217465) B1217465
theorem B541307 : Blo 539803 541307 := bstep (se 1 (by rfl) ⟨405980, by rfl⟩ : syracuseStep 541307 = 811961) B811961
theorem B1827467 : Blo 539803 1827467 := bstep (se 1 (by rfl) ⟨1370600, by rfl⟩ : syracuseStep 1827467 = 2741201) B2741201
theorem B541359 : Blo 539803 541359 := bstep (se 1 (by rfl) ⟨406019, by rfl⟩ : syracuseStep 541359 = 812039) B812039
theorem B541383 : Blo 539803 541383 := bstep (se 1 (by rfl) ⟨406037, by rfl⟩ : syracuseStep 541383 = 812075) B812075
theorem B3080915 : Blo 539803 3080915 := bstep (se 1 (by rfl) ⟨2310686, by rfl⟩ : syracuseStep 3080915 = 4621373) B4621373
theorem B541403 : Blo 539803 541403 := bstep (se 1 (by rfl) ⟨406052, by rfl⟩ : syracuseStep 541403 = 812105) B812105
theorem B811769 : Blo 539803 811769 := bstep (se 2 (by rfl) ⟨304413, by rfl⟩ : syracuseStep 811769 = 608827) B608827
theorem B541479 : Blo 539803 541479 := bstep (se 1 (by rfl) ⟨406109, by rfl⟩ : syracuseStep 541479 = 812219) B812219
theorem B541519 : Blo 539803 541519 := bstep (se 1 (by rfl) ⟨406139, by rfl⟩ : syracuseStep 541519 = 812279) B812279
theorem B811871 : Blo 539803 811871 := bstep (se 1 (by rfl) ⟨608903, by rfl⟩ : syracuseStep 811871 = 1217807) B1217807
theorem B541535 : Blo 539803 541535 := bstep (se 1 (by rfl) ⟨406151, by rfl⟩ : syracuseStep 541535 = 812303) B812303
theorem B811883 : Blo 539803 811883 := bstep (se 1 (by rfl) ⟨608912, by rfl⟩ : syracuseStep 811883 = 1217825) B1217825
theorem B541563 : Blo 539803 541563 := bstep (se 1 (by rfl) ⟨406172, by rfl⟩ : syracuseStep 541563 = 812345) B812345
theorem B541615 : Blo 539803 541615 := bstep (se 1 (by rfl) ⟨406211, by rfl⟩ : syracuseStep 541615 = 812423) B812423
theorem B3474359 : Blo 539803 3474359 := bstep (se 1 (by rfl) ⟨2605769, by rfl⟩ : syracuseStep 3474359 = 5211539) B5211539
theorem B1156027 : Blo 539803 1156027 := bstep (se 1 (by rfl) ⟨867020, by rfl⟩ : syracuseStep 1156027 = 1734041) B1734041
theorem B2057147 : Blo 539803 2057147 := bstep (se 1 (by rfl) ⟨1542860, by rfl⟩ : syracuseStep 2057147 = 3085721) B3085721
theorem B541639 : Blo 539803 541639 := bstep (se 1 (by rfl) ⟨406229, by rfl⟩ : syracuseStep 541639 = 812459) B812459
theorem B541659 : Blo 539803 541659 := bstep (se 1 (by rfl) ⟨406244, by rfl⟩ : syracuseStep 541659 = 812489) B812489
theorem B1303559 : Blo 539803 1303559 := bstep (se 1 (by rfl) ⟨977669, by rfl⟩ : syracuseStep 1303559 = 1955339) B1955339
theorem B3466259 : Blo 539803 3466259 := bstep (se 1 (by rfl) ⟨2599694, by rfl⟩ : syracuseStep 3466259 = 5199389) B5199389
theorem B15631379 : Blo 539803 15631379 := bstep (se 1 (by rfl) ⟨11723534, by rfl⟩ : syracuseStep 15631379 = 23447069) B23447069
theorem B541735 : Blo 539803 541735 := bstep (se 1 (by rfl) ⟨406301, by rfl⟩ : syracuseStep 541735 = 812603) B812603
theorem B812111 : Blo 539803 812111 := bstep (se 1 (by rfl) ⟨609083, by rfl⟩ : syracuseStep 812111 = 1218167) B1218167
theorem B541775 : Blo 539803 541775 := bstep (se 1 (by rfl) ⟨406331, by rfl⟩ : syracuseStep 541775 = 812663) B812663
theorem B541791 : Blo 539803 541791 := bstep (se 1 (by rfl) ⟨406343, by rfl⟩ : syracuseStep 541791 = 812687) B812687
theorem B541819 : Blo 539803 541819 := bstep (se 1 (by rfl) ⟨406364, by rfl⟩ : syracuseStep 541819 = 812729) B812729
theorem B4613273 : Blo 539803 4613273 := bstep (se 2 (by rfl) ⟨1729977, by rfl⟩ : syracuseStep 4613273 = 3459955) B3459955
theorem B541871 : Blo 539803 541871 := bstep (se 1 (by rfl) ⟨406403, by rfl⟩ : syracuseStep 541871 = 812807) B812807
theorem B812231 : Blo 539803 812231 := bstep (se 1 (by rfl) ⟨609173, by rfl⟩ : syracuseStep 812231 = 1218347) B1218347
theorem B541895 : Blo 539803 541895 := bstep (se 1 (by rfl) ⟨406421, by rfl⟩ : syracuseStep 541895 = 812843) B812843
theorem B541915 : Blo 539803 541915 := bstep (se 1 (by rfl) ⟨406436, by rfl⟩ : syracuseStep 541915 = 812873) B812873
theorem B541991 : Blo 539803 541991 := bstep (se 1 (by rfl) ⟨406493, by rfl⟩ : syracuseStep 541991 = 812987) B812987
theorem B542031 : Blo 539803 542031 := bstep (se 1 (by rfl) ⟨406523, by rfl⟩ : syracuseStep 542031 = 813047) B813047
theorem B542047 : Blo 539803 542047 := bstep (se 1 (by rfl) ⟨406535, by rfl⟩ : syracuseStep 542047 = 813071) B813071
theorem B1459561 : Blo 539803 1459561 := bstep (se 2 (by rfl) ⟨547335, by rfl⟩ : syracuseStep 1459561 = 1094671) B1094671
theorem B812393 : Blo 539803 812393 := bstep (se 2 (by rfl) ⟨304647, by rfl⟩ : syracuseStep 812393 = 609295) B609295
theorem B1017193 : Blo 539803 1017193 := bstep (se 2 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 1017193 = 762895) B762895
theorem B542075 : Blo 539803 542075 := bstep (se 1 (by rfl) ⟨406556, by rfl⟩ : syracuseStep 542075 = 813113) B813113
theorem B1369487 : Blo 539803 1369487 := bstep (se 1 (by rfl) ⟨1027115, by rfl⟩ : syracuseStep 1369487 = 2054231) B2054231
theorem B542127 : Blo 539803 542127 := bstep (se 1 (by rfl) ⟨406595, by rfl⟩ : syracuseStep 542127 = 813191) B813191
theorem B812471 : Blo 539803 812471 := bstep (se 1 (by rfl) ⟨609353, by rfl⟩ : syracuseStep 812471 = 1218707) B1218707
theorem B542151 : Blo 539803 542151 := bstep (se 1 (by rfl) ⟨406613, by rfl⟩ : syracuseStep 542151 = 813227) B813227
theorem B2631113 : Blo 539803 2631113 := bstep (se 2 (by rfl) ⟨986667, by rfl⟩ : syracuseStep 2631113 = 1973335) B1973335
theorem B6661577 : Blo 539803 6661577 := bstep (se 2 (by rfl) ⟨2498091, by rfl⟩ : syracuseStep 6661577 = 4996183) B4996183
theorem B812507 : Blo 539803 812507 := bstep (se 1 (by rfl) ⟨609380, by rfl⟩ : syracuseStep 812507 = 1218761) B1218761
theorem B542171 : Blo 539803 542171 := bstep (se 1 (by rfl) ⟨406628, by rfl⟩ : syracuseStep 542171 = 813257) B813257
theorem B2049569 : Blo 539803 2049569 := bstep (se 2 (by rfl) ⟨768588, by rfl⟩ : syracuseStep 2049569 = 1537177) B1537177
theorem B1828385 : Blo 539803 1828385 := bstep (se 2 (by rfl) ⟨685644, by rfl⟩ : syracuseStep 1828385 = 1371289) B1371289
theorem B607783 : Blo 539803 607783 := bstep (se 1 (by rfl) ⟨455837, by rfl⟩ : syracuseStep 607783 = 911675) B911675
theorem B542247 : Blo 539803 542247 := bstep (se 1 (by rfl) ⟨406685, by rfl⟩ : syracuseStep 542247 = 813371) B813371
theorem B3130919 : Blo 539803 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B542287 : Blo 539803 542287 := bstep (se 1 (by rfl) ⟨406715, by rfl⟩ : syracuseStep 542287 = 813431) B813431
theorem B542303 : Blo 539803 542303 := bstep (se 1 (by rfl) ⟨406727, by rfl⟩ : syracuseStep 542303 = 813455) B813455
theorem B542331 : Blo 539803 542331 := bstep (se 1 (by rfl) ⟨406748, by rfl⟩ : syracuseStep 542331 = 813497) B813497
theorem B1853063 : Blo 539803 1853063 := bstep (se 1 (by rfl) ⟨1389797, by rfl⟩ : syracuseStep 1853063 = 2779595) B2779595
theorem B542383 : Blo 539803 542383 := bstep (se 1 (by rfl) ⟨406787, by rfl⟩ : syracuseStep 542383 = 813575) B813575
theorem B911047 : Blo 539803 911047 := bstep (se 1 (by rfl) ⟨683285, by rfl⟩ : syracuseStep 911047 = 1366571) B1366571
theorem B542407 : Blo 539803 542407 := bstep (se 1 (by rfl) ⟨406805, by rfl⟩ : syracuseStep 542407 = 813611) B813611
theorem B1369811 : Blo 539803 1369811 := bstep (se 1 (by rfl) ⟨1027358, by rfl⟩ : syracuseStep 1369811 = 2054717) B2054717
theorem B4155095 : Blo 539803 4155095 := bstep (se 1 (by rfl) ⟨3116321, by rfl⟩ : syracuseStep 4155095 = 6232643) B6232643
theorem B542427 : Blo 539803 542427 := bstep (se 1 (by rfl) ⟨406820, by rfl⟩ : syracuseStep 542427 = 813641) B813641
theorem B730873 : Blo 539803 730873 := bstep (se 2 (by rfl) ⟨274077, by rfl⟩ : syracuseStep 730873 = 548155) B548155
theorem B1828601 : Blo 539803 1828601 := bstep (se 2 (by rfl) ⟨685725, by rfl⟩ : syracuseStep 1828601 = 1371451) B1371451
theorem B542503 : Blo 539803 542503 := bstep (se 1 (by rfl) ⟨406877, by rfl⟩ : syracuseStep 542503 = 813755) B813755
theorem B542543 : Blo 539803 542543 := bstep (se 1 (by rfl) ⟨406907, by rfl⟩ : syracuseStep 542543 = 813815) B813815
theorem B13510489 : Blo 539803 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B2049887 : Blo 539803 2049887 := bstep (se 1 (by rfl) ⟨1537415, by rfl⟩ : syracuseStep 2049887 = 3074831) B3074831
theorem B1410911 : Blo 539803 1410911 := bstep (se 1 (by rfl) ⟨1058183, by rfl⟩ : syracuseStep 1410911 = 2116367) B2116367
theorem B542559 : Blo 539803 542559 := bstep (se 1 (by rfl) ⟨406919, by rfl⟩ : syracuseStep 542559 = 813839) B813839
theorem B911209 : Blo 539803 911209 := bstep (se 2 (by rfl) ⟨341703, by rfl⟩ : syracuseStep 911209 = 683407) B683407
theorem B2770807 : Blo 539803 2770807 := bstep (se 1 (by rfl) ⟨2078105, by rfl⟩ : syracuseStep 2770807 = 4156211) B4156211
theorem B542587 : Blo 539803 542587 := bstep (se 1 (by rfl) ⟨406940, by rfl⟩ : syracuseStep 542587 = 813881) B813881
theorem B812975 : Blo 539803 812975 := bstep (se 1 (by rfl) ⟨609731, by rfl⟩ : syracuseStep 812975 = 1219463) B1219463
theorem B542639 : Blo 539803 542639 := bstep (se 1 (by rfl) ⟨406979, by rfl⟩ : syracuseStep 542639 = 813959) B813959
theorem B3475385 : Blo 539803 3475385 := bstep (se 2 (by rfl) ⟨1303269, by rfl⟩ : syracuseStep 3475385 = 2606539) B2606539
theorem B542663 : Blo 539803 542663 := bstep (se 1 (by rfl) ⟨406997, by rfl⟩ : syracuseStep 542663 = 813995) B813995
theorem B542683 : Blo 539803 542683 := bstep (se 1 (by rfl) ⟨407012, by rfl⟩ : syracuseStep 542683 = 814025) B814025
theorem B2050055 : Blo 539803 2050055 := bstep (se 1 (by rfl) ⟨1537541, by rfl⟩ : syracuseStep 2050055 = 3075083) B3075083
theorem B1730567 : Blo 539803 1730567 := bstep (se 1 (by rfl) ⟨1297925, by rfl⟩ : syracuseStep 1730567 = 2595851) B2595851
theorem B1828871 : Blo 539803 1828871 := bstep (se 1 (by rfl) ⟨1371653, by rfl⟩ : syracuseStep 1828871 = 2743307) B2743307
theorem B813065 : Blo 539803 813065 := bstep (se 2 (by rfl) ⟨304899, by rfl⟩ : syracuseStep 813065 = 609799) B609799
theorem B813095 : Blo 539803 813095 := bstep (se 1 (by rfl) ⟨609821, by rfl⟩ : syracuseStep 813095 = 1219643) B1219643
theorem B542759 : Blo 539803 542759 := bstep (se 1 (by rfl) ⟨407069, by rfl⟩ : syracuseStep 542759 = 814139) B814139
theorem B1386553 : Blo 539803 1386553 := bstep (se 2 (by rfl) ⟨519957, by rfl⟩ : syracuseStep 1386553 = 1039915) B1039915
theorem B542799 : Blo 539803 542799 := bstep (se 1 (by rfl) ⟨407099, by rfl⟩ : syracuseStep 542799 = 814199) B814199
theorem B1828979 : Blo 539803 1828979 := bstep (se 1 (by rfl) ⟨1371734, by rfl⟩ : syracuseStep 1828979 = 2743469) B2743469
theorem B813179 : Blo 539803 813179 := bstep (se 1 (by rfl) ⟨609884, by rfl⟩ : syracuseStep 813179 = 1219769) B1219769
theorem B126412973 : Blo 539803 126412973 := bstep (se 3 (by rfl) ⟨23702432, by rfl⟩ : syracuseStep 126412973 = 47404865) B47404865
theorem B1214711 : Blo 539803 1214711 := bstep (se 1 (by rfl) ⟨911033, by rfl⟩ : syracuseStep 1214711 = 1822067) B1822067
theorem B813305 : Blo 539803 813305 := bstep (se 2 (by rfl) ⟨304989, by rfl⟩ : syracuseStep 813305 = 609979) B609979
theorem B14838065 : Blo 539803 14838065 := bstep (se 2 (by rfl) ⟨5564274, by rfl⟩ : syracuseStep 14838065 = 11128549) B11128549
theorem B4933975 : Blo 539803 4933975 := bstep (se 1 (by rfl) ⟨3700481, by rfl⟩ : syracuseStep 4933975 = 7400963) B7400963
theorem B813407 : Blo 539803 813407 := bstep (se 1 (by rfl) ⟨610055, by rfl⟩ : syracuseStep 813407 = 1220111) B1220111
theorem B813419 : Blo 539803 813419 := bstep (se 1 (by rfl) ⟨610064, by rfl⟩ : syracuseStep 813419 = 1220129) B1220129
theorem B1829249 : Blo 539803 1829249 := bstep (se 2 (by rfl) ⟨685968, by rfl⟩ : syracuseStep 1829249 = 1371937) B1371937
theorem B6678937 : Blo 539803 6678937 := bstep (se 2 (by rfl) ⟨2504601, by rfl⟩ : syracuseStep 6678937 = 5009203) B5009203
theorem B772535 : Blo 539803 772535 := bstep (se 1 (by rfl) ⟨579401, by rfl⟩ : syracuseStep 772535 = 1158803) B1158803
theorem B14797241 : Blo 539803 14797241 := bstep (se 2 (by rfl) ⟨5548965, by rfl⟩ : syracuseStep 14797241 = 11097931) B11097931
theorem B911803 : Blo 539803 911803 := bstep (se 1 (by rfl) ⟨683852, by rfl⟩ : syracuseStep 911803 = 1367705) B1367705
theorem B4106699 : Blo 539803 4106699 := bstep (se 1 (by rfl) ⟨3080024, by rfl⟩ : syracuseStep 4106699 = 6160049) B6160049
theorem B1026523 : Blo 539803 1026523 := bstep (se 1 (by rfl) ⟨769892, by rfl⟩ : syracuseStep 1026523 = 1539785) B1539785
theorem B2050541 : Blo 539803 2050541 := bstep (se 3 (by rfl) ⟨384476, by rfl⟩ : syracuseStep 2050541 = 768953) B768953
theorem B1026569 : Blo 539803 1026569 := bstep (se 2 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 1026569 = 769927) B769927
theorem B911911 : Blo 539803 911911 := bstep (se 1 (by rfl) ⟨683933, by rfl⟩ : syracuseStep 911911 = 1367867) B1367867
theorem B813647 : Blo 539803 813647 := bstep (se 1 (by rfl) ⟨610235, by rfl⟩ : syracuseStep 813647 = 1220471) B1220471
theorem B813767 : Blo 539803 813767 := bstep (se 1 (by rfl) ⟨610325, by rfl⟩ : syracuseStep 813767 = 1220651) B1220651
theorem B11995877 : Blo 539803 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B13200101 : Blo 539803 13200101 := bstep (se 4 (by rfl) ⟨1237509, by rfl⟩ : syracuseStep 13200101 = 2475019) B2475019
theorem B2050859 : Blo 539803 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B1297225 : Blo 539803 1297225 := bstep (se 2 (by rfl) ⟨486459, by rfl⟩ : syracuseStep 1297225 = 972919) B972919
theorem B1215305 : Blo 539803 1215305 := bstep (se 2 (by rfl) ⟨455739, by rfl⟩ : syracuseStep 1215305 = 911479) B911479
theorem B1026911 : Blo 539803 1026911 := bstep (se 1 (by rfl) ⟨770183, by rfl⟩ : syracuseStep 1026911 = 1540367) B1540367
theorem B813929 : Blo 539803 813929 := bstep (se 2 (by rfl) ⟨305223, by rfl⟩ : syracuseStep 813929 = 610447) B610447
theorem B912235 : Blo 539803 912235 := bstep (se 1 (by rfl) ⟨684176, by rfl⟩ : syracuseStep 912235 = 1368353) B1368353
theorem B814007 : Blo 539803 814007 := bstep (se 1 (by rfl) ⟨610505, by rfl⟩ : syracuseStep 814007 = 1221011) B1221011
theorem B814043 : Blo 539803 814043 := bstep (se 1 (by rfl) ⟨610532, by rfl⟩ : syracuseStep 814043 = 1221065) B1221065
theorem B1543225 : Blo 539803 1543225 := bstep (se 2 (by rfl) ⟨578709, by rfl⟩ : syracuseStep 1543225 = 1157419) B1157419
theorem B609403 : Blo 539803 609403 := bstep (se 1 (by rfl) ⟨457052, by rfl⟩ : syracuseStep 609403 = 914105) B914105
theorem B1830059 : Blo 539803 1830059 := bstep (se 1 (by rfl) ⟨1372544, by rfl⟩ : syracuseStep 1830059 = 2745089) B2745089
theorem B3468491 : Blo 539803 3468491 := bstep (se 1 (by rfl) ⟨2601368, by rfl⟩ : syracuseStep 3468491 = 5202737) B5202737
theorem B978131 : Blo 539803 978131 := bstep (se 1 (by rfl) ⟨733598, by rfl⟩ : syracuseStep 978131 = 1467197) B1467197
theorem B9375011 : Blo 539803 9375011 := bstep (se 1 (by rfl) ⟨7031258, by rfl⟩ : syracuseStep 9375011 = 14062517) B14062517
theorem B9637157 : Blo 539803 9637157 := bstep (se 4 (by rfl) ⟨903483, by rfl⟩ : syracuseStep 9637157 = 1806967) B1806967
theorem B1822013 : Blo 539803 1822013 := bstep (se 3 (by rfl) ⟨341627, by rfl⟩ : syracuseStep 1822013 = 683255) B683255
theorem B2059607 : Blo 539803 2059607 := bstep (se 1 (by rfl) ⟨1544705, by rfl⟩ : syracuseStep 2059607 = 3089411) B3089411
theorem B2739581 : Blo 539803 2739581 := bstep (se 3 (by rfl) ⟨513671, by rfl⟩ : syracuseStep 2739581 = 1027343) B1027343
theorem B15822215 : Blo 539803 15822215 := bstep (se 1 (by rfl) ⟨11866661, by rfl⟩ : syracuseStep 15822215 = 23733323) B23733323
theorem B3911075 : Blo 539803 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B609871 : Blo 539803 609871 := bstep (se 1 (by rfl) ⟨457403, by rfl⟩ : syracuseStep 609871 = 914807) B914807
theorem B1216097 : Blo 539803 1216097 := bstep (se 2 (by rfl) ⟨456036, by rfl⟩ : syracuseStep 1216097 = 912073) B912073
theorem B1044065 : Blo 539803 1044065 := bstep (se 2 (by rfl) ⟨391524, by rfl⟩ : syracuseStep 1044065 = 783049) B783049
theorem B3894929 : Blo 539803 3894929 := bstep (se 2 (by rfl) ⟨1460598, by rfl⟩ : syracuseStep 3894929 = 2921197) B2921197
theorem B1830599 : Blo 539803 1830599 := bstep (se 1 (by rfl) ⟨1372949, by rfl⟩ : syracuseStep 1830599 = 2745899) B2745899
theorem B6598381 : Blo 539803 6598381 := bstep (se 3 (by rfl) ⟨1237196, by rfl⟩ : syracuseStep 6598381 = 2474393) B2474393
theorem B3075833 : Blo 539803 3075833 := bstep (se 2 (by rfl) ⟨1153437, by rfl⟩ : syracuseStep 3075833 = 2306875) B2306875
theorem B1158905 : Blo 539803 1158905 := bstep (se 2 (by rfl) ⟨434589, by rfl⟩ : syracuseStep 1158905 = 869179) B869179
theorem B2404163 : Blo 539803 2404163 := bstep (se 1 (by rfl) ⟨1803122, by rfl⟩ : syracuseStep 2404163 = 3606245) B3606245
theorem B913295 : Blo 539803 913295 := bstep (se 1 (by rfl) ⟨684971, by rfl⟩ : syracuseStep 913295 = 1369943) B1369943
theorem B1314721 : Blo 539803 1314721 := bstep (se 2 (by rfl) ⟨493020, by rfl⟩ : syracuseStep 1314721 = 986041) B986041
theorem B1372079 : Blo 539803 1372079 := bstep (se 1 (by rfl) ⟨1029059, by rfl⟩ : syracuseStep 1372079 = 2058119) B2058119
theorem B683959 : Blo 539803 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B1216439 : Blo 539803 1216439 := bstep (se 1 (by rfl) ⟨912329, by rfl⟩ : syracuseStep 1216439 = 1824659) B1824659
theorem B1028027 : Blo 539803 1028027 := bstep (se 1 (by rfl) ⟨771020, by rfl⟩ : syracuseStep 1028027 = 1542041) B1542041
theorem B610267 : Blo 539803 610267 := bstep (se 1 (by rfl) ⟨457700, by rfl⟩ : syracuseStep 610267 = 915401) B915401
theorem B1159247 : Blo 539803 1159247 := bstep (se 1 (by rfl) ⟨869435, by rfl⟩ : syracuseStep 1159247 = 1738871) B1738871
theorem B913531 : Blo 539803 913531 := bstep (se 1 (by rfl) ⟨685148, by rfl⟩ : syracuseStep 913531 = 1370297) B1370297
theorem B1822877 : Blo 539803 1822877 := bstep (se 3 (by rfl) ⟨341789, by rfl⟩ : syracuseStep 1822877 = 683579) B683579
theorem B1954039 : Blo 539803 1954039 := bstep (se 1 (by rfl) ⟨1465529, by rfl⟩ : syracuseStep 1954039 = 2931059) B2931059
theorem B1954153 : Blo 539803 1954153 := bstep (se 2 (by rfl) ⟨732807, by rfl⟩ : syracuseStep 1954153 = 1465615) B1465615
theorem B1028513 : Blo 539803 1028513 := bstep (se 2 (by rfl) ⟨385692, by rfl⟩ : syracuseStep 1028513 = 771385) B771385
theorem B4398731 : Blo 539803 4398731 := bstep (se 1 (by rfl) ⟨3299048, by rfl⟩ : syracuseStep 4398731 = 6598097) B6598097
theorem B1217033 : Blo 539803 1217033 := bstep (se 2 (by rfl) ⟨456387, by rfl⟩ : syracuseStep 1217033 = 912775) B912775
theorem B4452889 : Blo 539803 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B1372697 : Blo 539803 1372697 := bstep (se 2 (by rfl) ⟨514761, by rfl⟩ : syracuseStep 1372697 = 1029523) B1029523
theorem B1831463 : Blo 539803 1831463 := bstep (se 1 (by rfl) ⟨1373597, by rfl⟩ : syracuseStep 1831463 = 2747195) B2747195
theorem B1299041 : Blo 539803 1299041 := bstep (se 2 (by rfl) ⟨487140, by rfl⟩ : syracuseStep 1299041 = 974281) B974281
theorem B1831571 : Blo 539803 1831571 := bstep (se 1 (by rfl) ⟨1373678, by rfl⟩ : syracuseStep 1831571 = 2747357) B2747357
theorem B1823417 : Blo 539803 1823417 := bstep (se 2 (by rfl) ⟨683781, by rfl⟩ : syracuseStep 1823417 = 1367563) B1367563
theorem B1028855 : Blo 539803 1028855 := bstep (se 1 (by rfl) ⟨771641, by rfl⟩ : syracuseStep 1028855 = 1543283) B1543283
theorem B4100867 : Blo 539803 4100867 := bstep (se 1 (by rfl) ⟨3075650, by rfl⟩ : syracuseStep 4100867 = 6151301) B6151301
theorem B4109129 : Blo 539803 4109129 := bstep (se 2 (by rfl) ⟨1540923, by rfl⟩ : syracuseStep 4109129 = 3081847) B3081847
theorem B1217375 : Blo 539803 1217375 := bstep (se 1 (by rfl) ⟨913031, by rfl⟩ : syracuseStep 1217375 = 1826063) B1826063
theorem B2052971 : Blo 539803 2052971 := bstep (se 1 (by rfl) ⟨1539728, by rfl⟩ : syracuseStep 2052971 = 3079457) B3079457
theorem B1831787 : Blo 539803 1831787 := bstep (se 1 (by rfl) ⟨1373840, by rfl⟩ : syracuseStep 1831787 = 2747681) B2747681
theorem B1831841 : Blo 539803 1831841 := bstep (se 2 (by rfl) ⟨686940, by rfl⟩ : syracuseStep 1831841 = 1373881) B1373881
theorem B1389487 : Blo 539803 1389487 := bstep (se 1 (by rfl) ⟨1042115, by rfl⟩ : syracuseStep 1389487 = 2084231) B2084231
theorem B59413445 : Blo 539803 59413445 := bstep (se 4 (by rfl) ⟨5570010, by rfl⟩ : syracuseStep 59413445 = 11140021) B11140021
theorem B914395 : Blo 539803 914395 := bstep (se 1 (by rfl) ⟨685796, by rfl⟩ : syracuseStep 914395 = 1371593) B1371593
theorem B1217555 : Blo 539803 1217555 := bstep (se 1 (by rfl) ⟨913166, by rfl⟩ : syracuseStep 1217555 = 1826333) B1826333
theorem B3462263 : Blo 539803 3462263 := bstep (se 1 (by rfl) ⟨2596697, by rfl⟩ : syracuseStep 3462263 = 5193395) B5193395
theorem B3077291 : Blo 539803 3077291 := bstep (se 1 (by rfl) ⟨2307968, by rfl⟩ : syracuseStep 3077291 = 4615937) B4615937
theorem B3519683 : Blo 539803 3519683 := bstep (se 1 (by rfl) ⟨2639762, by rfl⟩ : syracuseStep 3519683 = 5279525) B5279525
theorem B685255 : Blo 539803 685255 := bstep (se 1 (by rfl) ⟨513941, by rfl⟩ : syracuseStep 685255 = 1027883) B1027883
theorem B1824011 : Blo 539803 1824011 := bstep (se 1 (by rfl) ⟨1368008, by rfl⟩ : syracuseStep 1824011 = 2736017) B2736017
theorem B1733899 : Blo 539803 1733899 := bstep (se 1 (by rfl) ⟨1300424, by rfl⟩ : syracuseStep 1733899 = 2600849) B2600849
theorem B30078307 : Blo 539803 30078307 := bstep (se 1 (by rfl) ⟨22558730, by rfl⟩ : syracuseStep 30078307 = 45117461) B45117461
theorem B1217897 : Blo 539803 1217897 := bstep (se 2 (by rfl) ⟨456711, by rfl⟩ : syracuseStep 1217897 = 913423) B913423
theorem B8033701 : Blo 539803 8033701 := bstep (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) B1506319
theorem B1824281 : Blo 539803 1824281 := bstep (se 2 (by rfl) ⟨684105, by rfl⟩ : syracuseStep 1824281 = 1368211) B1368211
theorem B4388413 : Blo 539803 4388413 := bstep (se 3 (by rfl) ⟨822827, by rfl⟩ : syracuseStep 4388413 = 1645655) B1645655
theorem B915023 : Blo 539803 915023 := bstep (se 1 (by rfl) ⟨686267, by rfl⟩ : syracuseStep 915023 = 1372535) B1372535
theorem B5264993 : Blo 539803 5264993 := bstep (se 2 (by rfl) ⟨1974372, by rfl⟩ : syracuseStep 5264993 = 3948745) B3948745
theorem B2315965 : Blo 539803 2315965 := bstep (se 3 (by rfl) ⟨434243, by rfl⟩ : syracuseStep 2315965 = 868487) B868487
theorem B1390279 : Blo 539803 1390279 := bstep (se 1 (by rfl) ⟨1042709, by rfl⟩ : syracuseStep 1390279 = 2085419) B2085419
theorem B3086039 : Blo 539803 3086039 := bstep (se 1 (by rfl) ⟨2314529, by rfl⟩ : syracuseStep 3086039 = 4629059) B4629059
theorem B866155 : Blo 539803 866155 := bstep (se 1 (by rfl) ⟨649616, by rfl⟩ : syracuseStep 866155 = 1299233) B1299233
theorem B685999 : Blo 539803 685999 := bstep (se 1 (by rfl) ⟨514499, by rfl⟩ : syracuseStep 685999 = 1028999) B1028999
theorem B1218491 : Blo 539803 1218491 := bstep (se 1 (by rfl) ⟨913868, by rfl⟩ : syracuseStep 1218491 = 1827737) B1827737
theorem B1030153 : Blo 539803 1030153 := bstep (se 2 (by rfl) ⟨386307, by rfl⟩ : syracuseStep 1030153 = 772615) B772615
theorem B3708965 : Blo 539803 3708965 := bstep (se 4 (by rfl) ⟨347715, by rfl⟩ : syracuseStep 3708965 = 695431) B695431
theorem B1218617 : Blo 539803 1218617 := bstep (se 2 (by rfl) ⟨456981, by rfl⟩ : syracuseStep 1218617 = 913963) B913963
theorem B8755289 : Blo 539803 8755289 := bstep (se 2 (by rfl) ⟨3283233, by rfl⟩ : syracuseStep 8755289 = 6566467) B6566467
theorem B3127385 : Blo 539803 3127385 := bstep (se 2 (by rfl) ⟨1172769, by rfl⟩ : syracuseStep 3127385 = 2345539) B2345539
theorem B4618397 : Blo 539803 4618397 := bstep (se 3 (by rfl) ⟨865949, by rfl⟩ : syracuseStep 4618397 = 1731899) B1731899
theorem B3471589 : Blo 539803 3471589 := bstep (se 4 (by rfl) ⟨325461, by rfl⟩ : syracuseStep 3471589 = 650923) B650923
theorem B2734397 : Blo 539803 2734397 := bstep (se 3 (by rfl) ⟨512699, by rfl⟩ : syracuseStep 2734397 = 1025399) B1025399
theorem B10008937 : Blo 539803 10008937 := bstep (se 2 (by rfl) ⟨3753351, by rfl⟩ : syracuseStep 10008937 = 7506703) B7506703
theorem B1218959 : Blo 539803 1218959 := bstep (se 1 (by rfl) ⟨914219, by rfl⟩ : syracuseStep 1218959 = 1828439) B1828439
theorem B915887 : Blo 539803 915887 := bstep (se 1 (by rfl) ⟨686915, by rfl⟩ : syracuseStep 915887 = 1373831) B1373831
theorem B7821805 : Blo 539803 7821805 := bstep (se 3 (by rfl) ⟨1466588, by rfl⟩ : syracuseStep 7821805 = 2933177) B2933177
theorem B1825415 : Blo 539803 1825415 := bstep (se 1 (by rfl) ⟨1369061, by rfl⟩ : syracuseStep 1825415 = 2738123) B2738123
theorem B57834163 : Blo 539803 57834163 := bstep (se 1 (by rfl) ⟨43375622, by rfl⟩ : syracuseStep 57834163 = 86751245) B86751245
theorem B1825469 : Blo 539803 1825469 := bstep (se 3 (by rfl) ⟨342275, by rfl⟩ : syracuseStep 1825469 = 684551) B684551
theorem B4627145 : Blo 539803 4627145 := bstep (se 2 (by rfl) ⟨1735179, by rfl⟩ : syracuseStep 4627145 = 3470359) B3470359
theorem B1219283 : Blo 539803 1219283 := bstep (se 1 (by rfl) ⟨914462, by rfl⟩ : syracuseStep 1219283 = 1828925) B1828925
theorem B10566389 : Blo 539803 10566389 := bstep (se 5 (by rfl) ⟨495299, by rfl⟩ : syracuseStep 10566389 = 990599) B990599
theorem B1153865 : Blo 539803 1153865 := bstep (se 2 (by rfl) ⟨432699, by rfl⟩ : syracuseStep 1153865 = 865399) B865399
theorem B6921035 : Blo 539803 6921035 := bstep (se 1 (by rfl) ⟨5190776, by rfl⟩ : syracuseStep 6921035 = 10381553) B10381553
theorem B1825631 : Blo 539803 1825631 := bstep (se 1 (by rfl) ⟨1369223, by rfl⟩ : syracuseStep 1825631 = 2738447) B2738447
theorem B1096553 : Blo 539803 1096553 := bstep (se 2 (by rfl) ⟨411207, by rfl⟩ : syracuseStep 1096553 = 822415) B822415
theorem B809903 : Blo 539803 809903 := bstep (se 1 (by rfl) ⟨607427, by rfl⟩ : syracuseStep 809903 = 1214855) B1214855
theorem B1825793 : Blo 539803 1825793 := bstep (se 2 (by rfl) ⟨684672, by rfl⟩ : syracuseStep 1825793 = 1369345) B1369345
theorem B1735681 : Blo 539803 1735681 := bstep (se 2 (by rfl) ⟨650880, by rfl⟩ : syracuseStep 1735681 = 1301761) B1301761
theorem B809993 : Blo 539803 809993 := bstep (se 2 (by rfl) ⟨303747, by rfl⟩ : syracuseStep 809993 = 607495) B607495
theorem B810023 : Blo 539803 810023 := bstep (se 1 (by rfl) ⟨607517, by rfl⟩ : syracuseStep 810023 = 1215035) B1215035
theorem B867385 : Blo 539803 867385 := bstep (se 2 (by rfl) ⟨325269, by rfl⟩ : syracuseStep 867385 = 650539) B650539
theorem B810107 : Blo 539803 810107 := bstep (se 1 (by rfl) ⟨607580, by rfl⟩ : syracuseStep 810107 = 1215161) B1215161
theorem B539823 : Blo 539803 539823 := bstep (se 1 (by rfl) ⟨404867, by rfl⟩ : syracuseStep 539823 = 809735) B809735
theorem B539847 : Blo 539803 539847 := bstep (se 1 (by rfl) ⟨404885, by rfl⟩ : syracuseStep 539847 = 809771) B809771
theorem B539867 : Blo 539803 539867 := bstep (se 1 (by rfl) ⟨404900, by rfl⟩ : syracuseStep 539867 = 809801) B809801
theorem B1015031 : Blo 539803 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B810233 : Blo 539803 810233 := bstep (se 2 (by rfl) ⟨303837, by rfl⟩ : syracuseStep 810233 = 607675) B607675
theorem B2055415 : Blo 539803 2055415 := bstep (se 1 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 2055415 = 3083123) B3083123
theorem B539943 : Blo 539803 539943 := bstep (se 1 (by rfl) ⟨404957, by rfl⟩ : syracuseStep 539943 = 809915) B809915
theorem B539983 : Blo 539803 539983 := bstep (se 1 (by rfl) ⟨404987, by rfl⟩ : syracuseStep 539983 = 809975) B809975
theorem B539999 : Blo 539803 539999 := bstep (se 1 (by rfl) ⟨404999, by rfl⟩ : syracuseStep 539999 = 809999) B809999
theorem B810335 : Blo 539803 810335 := bstep (se 1 (by rfl) ⟨607751, by rfl⟩ : syracuseStep 810335 = 1215503) B1215503
theorem B1367401 : Blo 539803 1367401 := bstep (se 2 (by rfl) ⟨512775, by rfl⟩ : syracuseStep 1367401 = 1025551) B1025551
theorem B810347 : Blo 539803 810347 := bstep (se 1 (by rfl) ⟨607760, by rfl⟩ : syracuseStep 810347 = 1215521) B1215521
theorem B540027 : Blo 539803 540027 := bstep (se 1 (by rfl) ⟨405020, by rfl⟩ : syracuseStep 540027 = 810041) B810041
theorem B3128701 : Blo 539803 3128701 := bstep (se 3 (by rfl) ⟨586631, by rfl⟩ : syracuseStep 3128701 = 1173263) B1173263
theorem B540079 : Blo 539803 540079 := bstep (se 1 (by rfl) ⟨405059, by rfl⟩ : syracuseStep 540079 = 810119) B810119
theorem B540103 : Blo 539803 540103 := bstep (se 1 (by rfl) ⟨405077, by rfl⟩ : syracuseStep 540103 = 810155) B810155
theorem B540123 : Blo 539803 540123 := bstep (se 1 (by rfl) ⟨405092, by rfl⟩ : syracuseStep 540123 = 810185) B810185
theorem B2055689 : Blo 539803 2055689 := bstep (se 2 (by rfl) ⟨770883, by rfl⟩ : syracuseStep 2055689 = 1541767) B1541767
theorem B2080289 : Blo 539803 2080289 := bstep (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) B1560217
theorem B540199 : Blo 539803 540199 := bstep (se 1 (by rfl) ⟨405149, by rfl⟩ : syracuseStep 540199 = 810299) B810299
theorem B2055719 : Blo 539803 2055719 := bstep (se 1 (by rfl) ⟨1541789, by rfl⟩ : syracuseStep 2055719 = 3083579) B3083579
theorem B540239 : Blo 539803 540239 := bstep (se 1 (by rfl) ⟨405179, by rfl⟩ : syracuseStep 540239 = 810359) B810359
theorem B810575 : Blo 539803 810575 := bstep (se 1 (by rfl) ⟨607931, by rfl⟩ : syracuseStep 810575 = 1215863) B1215863
theorem B540255 : Blo 539803 540255 := bstep (se 1 (by rfl) ⟨405191, by rfl⟩ : syracuseStep 540255 = 810383) B810383
theorem B3464801 : Blo 539803 3464801 := bstep (se 2 (by rfl) ⟨1299300, by rfl⟩ : syracuseStep 3464801 = 2598601) B2598601
theorem B540283 : Blo 539803 540283 := bstep (se 1 (by rfl) ⟨405212, by rfl⟩ : syracuseStep 540283 = 810425) B810425
theorem B1367675 : Blo 539803 1367675 := bstep (se 1 (by rfl) ⟨1025756, by rfl⟩ : syracuseStep 1367675 = 2051513) B2051513
theorem B1220219 : Blo 539803 1220219 := bstep (se 1 (by rfl) ⟨915164, by rfl⟩ : syracuseStep 1220219 = 1830329) B1830329
theorem B2743955 : Blo 539803 2743955 := bstep (se 1 (by rfl) ⟨2057966, by rfl⟩ : syracuseStep 2743955 = 4115933) B4115933
theorem B540335 : Blo 539803 540335 := bstep (se 1 (by rfl) ⟨405251, by rfl⟩ : syracuseStep 540335 = 810503) B810503
theorem B540359 : Blo 539803 540359 := bstep (se 1 (by rfl) ⟨405269, by rfl⟩ : syracuseStep 540359 = 810539) B810539
theorem B810695 : Blo 539803 810695 := bstep (se 1 (by rfl) ⟨608021, by rfl⟩ : syracuseStep 810695 = 1216043) B1216043
theorem B540379 : Blo 539803 540379 := bstep (se 1 (by rfl) ⟨405284, by rfl⟩ : syracuseStep 540379 = 810569) B810569
theorem B1220345 : Blo 539803 1220345 := bstep (se 2 (by rfl) ⟨457629, by rfl⟩ : syracuseStep 1220345 = 915259) B915259
theorem B540455 : Blo 539803 540455 := bstep (se 1 (by rfl) ⟨405341, by rfl⟩ : syracuseStep 540455 = 810683) B810683
theorem B1949483 : Blo 539803 1949483 := bstep (se 1 (by rfl) ⟨1462112, by rfl⟩ : syracuseStep 1949483 = 2924225) B2924225
theorem B1826603 : Blo 539803 1826603 := bstep (se 1 (by rfl) ⟨1369952, by rfl⟩ : syracuseStep 1826603 = 2739905) B2739905
theorem B540495 : Blo 539803 540495 := bstep (se 1 (by rfl) ⟨405371, by rfl⟩ : syracuseStep 540495 = 810743) B810743
theorem B540511 : Blo 539803 540511 := bstep (se 1 (by rfl) ⟨405383, by rfl⟩ : syracuseStep 540511 = 810767) B810767
theorem B810857 : Blo 539803 810857 := bstep (se 2 (by rfl) ⟨304071, by rfl⟩ : syracuseStep 810857 = 608143) B608143
theorem B2195309 : Blo 539803 2195309 := bstep (se 3 (by rfl) ⟨411620, by rfl⟩ : syracuseStep 2195309 = 823241) B823241
theorem B540539 : Blo 539803 540539 := bstep (se 1 (by rfl) ⟨405404, by rfl⟩ : syracuseStep 540539 = 810809) B810809
theorem B540591 : Blo 539803 540591 := bstep (se 1 (by rfl) ⟨405443, by rfl⟩ : syracuseStep 540591 = 810887) B810887
theorem B810935 : Blo 539803 810935 := bstep (se 1 (by rfl) ⟨608201, by rfl⟩ : syracuseStep 810935 = 1216403) B1216403
theorem B540615 : Blo 539803 540615 := bstep (se 1 (by rfl) ⟨405461, by rfl⟩ : syracuseStep 540615 = 810923) B810923
theorem B540635 : Blo 539803 540635 := bstep (se 1 (by rfl) ⟨405476, by rfl⟩ : syracuseStep 540635 = 810953) B810953
theorem B810971 : Blo 539803 810971 := bstep (se 1 (by rfl) ⟨608228, by rfl⟩ : syracuseStep 810971 = 1216457) B1216457
theorem B2736179 : Blo 539803 2736179 := bstep (se 1 (by rfl) ⟨2052134, by rfl⟩ : syracuseStep 2736179 = 4104269) B4104269
theorem B3899603 : Blo 539803 3899603 := bstep (se 1 (by rfl) ⟨2924702, by rfl⟩ : syracuseStep 3899603 = 5849405) B5849405
theorem B540959 : Blo 539803 540959 := bstep (se 1 (by rfl) ⟨405719, by rfl⟩ : syracuseStep 540959 = 811439) B811439
theorem B4628785 : Blo 539803 4628785 := bstep (se 2 (by rfl) ⟨1735794, by rfl⟩ : syracuseStep 4628785 = 3471589) B3471589
theorem B2605385 : Blo 539803 2605385 := bstep (se 2 (by rfl) ⟨977019, by rfl⟩ : syracuseStep 2605385 = 1954039) B1954039
theorem B811355 : Blo 539803 811355 := bstep (se 1 (by rfl) ⟨608516, by rfl⟩ : syracuseStep 811355 = 1217033) B1217033
theorem B541019 : Blo 539803 541019 := bstep (se 1 (by rfl) ⟨405764, by rfl⟩ : syracuseStep 541019 = 811529) B811529
theorem B3293531 : Blo 539803 3293531 := bstep (se 1 (by rfl) ⟨2470148, by rfl⟩ : syracuseStep 3293531 = 4940297) B4940297
theorem B541039 : Blo 539803 541039 := bstep (se 1 (by rfl) ⟨405779, by rfl⟩ : syracuseStep 541039 = 811559) B811559
theorem B1220975 : Blo 539803 1220975 := bstep (se 1 (by rfl) ⟨915731, by rfl⟩ : syracuseStep 1220975 = 1831463) B1831463
theorem B541095 : Blo 539803 541095 := bstep (se 1 (by rfl) ⟨405821, by rfl⟩ : syracuseStep 541095 = 811643) B811643
theorem B1221047 : Blo 539803 1221047 := bstep (se 1 (by rfl) ⟨915785, by rfl⟩ : syracuseStep 1221047 = 1831571) B1831571
theorem B6578633 : Blo 539803 6578633 := bstep (se 2 (by rfl) ⟨2466987, by rfl⟩ : syracuseStep 6578633 = 4933975) B4933975
theorem B13345249 : Blo 539803 13345249 := bstep (se 2 (by rfl) ⟨5004468, by rfl⟩ : syracuseStep 13345249 = 10008937) B10008937
theorem B2605537 : Blo 539803 2605537 := bstep (se 2 (by rfl) ⟨977076, by rfl⟩ : syracuseStep 2605537 = 1954153) B1954153
theorem B541179 : Blo 539803 541179 := bstep (se 1 (by rfl) ⟨405884, by rfl⟩ : syracuseStep 541179 = 811769) B811769
theorem B8905249 : Blo 539803 8905249 := bstep (se 2 (by rfl) ⟨3339468, by rfl⟩ : syracuseStep 8905249 = 6678937) B6678937
theorem B811583 : Blo 539803 811583 := bstep (se 1 (by rfl) ⟨608687, by rfl⟩ : syracuseStep 811583 = 1217375) B1217375
theorem B541247 : Blo 539803 541247 := bstep (se 1 (by rfl) ⟨405935, by rfl⟩ : syracuseStep 541247 = 811871) B811871
theorem B1368647 : Blo 539803 1368647 := bstep (se 1 (by rfl) ⟨1026485, by rfl⟩ : syracuseStep 1368647 = 2052971) B2052971
theorem B541255 : Blo 539803 541255 := bstep (se 1 (by rfl) ⟨405941, by rfl⟩ : syracuseStep 541255 = 811883) B811883
theorem B1221191 : Blo 539803 1221191 := bstep (se 1 (by rfl) ⟨915893, by rfl⟩ : syracuseStep 1221191 = 1831787) B1831787
theorem B1221227 : Blo 539803 1221227 := bstep (se 1 (by rfl) ⟨915920, by rfl⟩ : syracuseStep 1221227 = 1831841) B1831841
theorem B1368697 : Blo 539803 1368697 := bstep (se 2 (by rfl) ⟨513261, by rfl⟩ : syracuseStep 1368697 = 1026523) B1026523
theorem B39608963 : Blo 539803 39608963 := bstep (se 1 (by rfl) ⟨29706722, by rfl⟩ : syracuseStep 39608963 = 59413445) B59413445
theorem B10429073 : Blo 539803 10429073 := bstep (se 2 (by rfl) ⟨3910902, by rfl⟩ : syracuseStep 10429073 = 7821805) B7821805
theorem B869039 : Blo 539803 869039 := bstep (se 1 (by rfl) ⟨651779, by rfl⟩ : syracuseStep 869039 = 1303559) B1303559
theorem B2310839 : Blo 539803 2310839 := bstep (se 1 (by rfl) ⟨1733129, by rfl⟩ : syracuseStep 2310839 = 3466259) B3466259
theorem B811703 : Blo 539803 811703 := bstep (se 1 (by rfl) ⟨608777, by rfl⟩ : syracuseStep 811703 = 1217555) B1217555
theorem B10420919 : Blo 539803 10420919 := bstep (se 1 (by rfl) ⟨7815689, by rfl⟩ : syracuseStep 10420919 = 15631379) B15631379
theorem B541407 : Blo 539803 541407 := bstep (se 1 (by rfl) ⟨406055, by rfl⟩ : syracuseStep 541407 = 812111) B812111
theorem B541487 : Blo 539803 541487 := bstep (se 1 (by rfl) ⟨406115, by rfl⟩ : syracuseStep 541487 = 812231) B812231
theorem B77112217 : Blo 539803 77112217 := bstep (se 2 (by rfl) ⟨28917081, by rfl⟩ : syracuseStep 77112217 = 57834163) B57834163
theorem B811931 : Blo 539803 811931 := bstep (se 1 (by rfl) ⟨608948, by rfl⟩ : syracuseStep 811931 = 1217897) B1217897
theorem B541595 : Blo 539803 541595 := bstep (se 1 (by rfl) ⟨406196, by rfl⟩ : syracuseStep 541595 = 812393) B812393
theorem B541647 : Blo 539803 541647 := bstep (se 1 (by rfl) ⟨406235, by rfl⟩ : syracuseStep 541647 = 812471) B812471
theorem B1754075 : Blo 539803 1754075 := bstep (se 1 (by rfl) ⟨1315556, by rfl⟩ : syracuseStep 1754075 = 2631113) B2631113
theorem B4441051 : Blo 539803 4441051 := bstep (se 1 (by rfl) ⟨3330788, by rfl⟩ : syracuseStep 4441051 = 6661577) B6661577
theorem B541671 : Blo 539803 541671 := bstep (se 1 (by rfl) ⟨406253, by rfl⟩ : syracuseStep 541671 = 812507) B812507
theorem B1729633 : Blo 539803 1729633 := bstep (se 2 (by rfl) ⟨648612, by rfl⟩ : syracuseStep 1729633 = 1297225) B1297225
theorem B2057359 : Blo 539803 2057359 := bstep (se 1 (by rfl) ⟨1543019, by rfl⟩ : syracuseStep 2057359 = 3086039) B3086039
theorem B1852649 : Blo 539803 1852649 := bstep (se 2 (by rfl) ⟨694743, by rfl⟩ : syracuseStep 1852649 = 1389487) B1389487
theorem B1541369 : Blo 539803 1541369 := bstep (se 2 (by rfl) ⟨578013, by rfl⟩ : syracuseStep 1541369 = 1156027) B1156027
theorem B541983 : Blo 539803 541983 := bstep (se 1 (by rfl) ⟨406487, by rfl⟩ : syracuseStep 541983 = 812975) B812975
theorem B812327 : Blo 539803 812327 := bstep (se 1 (by rfl) ⟨609245, by rfl⟩ : syracuseStep 812327 = 1218491) B1218491
theorem B542043 : Blo 539803 542043 := bstep (se 1 (by rfl) ⟨406532, by rfl⟩ : syracuseStep 542043 = 813065) B813065
theorem B542063 : Blo 539803 542063 := bstep (se 1 (by rfl) ⟨406547, by rfl⟩ : syracuseStep 542063 = 813095) B813095
theorem B812411 : Blo 539803 812411 := bstep (se 1 (by rfl) ⟨609308, by rfl⟩ : syracuseStep 812411 = 1218617) B1218617
theorem B1156513 : Blo 539803 1156513 := bstep (se 2 (by rfl) ⟨433692, by rfl⟩ : syracuseStep 1156513 = 867385) B867385
theorem B2057633 : Blo 539803 2057633 := bstep (se 2 (by rfl) ⟨771612, by rfl⟩ : syracuseStep 2057633 = 1543225) B1543225
theorem B5547437 : Blo 539803 5547437 := bstep (se 3 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 5547437 = 2080289) B2080289
theorem B542119 : Blo 539803 542119 := bstep (se 1 (by rfl) ⟨406589, by rfl⟩ : syracuseStep 542119 = 813179) B813179
theorem B812537 : Blo 539803 812537 := bstep (se 2 (by rfl) ⟨304701, by rfl⟩ : syracuseStep 812537 = 609403) B609403
theorem B542203 : Blo 539803 542203 := bstep (se 1 (by rfl) ⟨406652, by rfl⟩ : syracuseStep 542203 = 813305) B813305
theorem B542271 : Blo 539803 542271 := bstep (se 1 (by rfl) ⟨406703, by rfl⟩ : syracuseStep 542271 = 813407) B813407
theorem B542279 : Blo 539803 542279 := bstep (se 1 (by rfl) ⟨406709, by rfl⟩ : syracuseStep 542279 = 813419) B813419
theorem B812639 : Blo 539803 812639 := bstep (se 1 (by rfl) ⟨609479, by rfl⟩ : syracuseStep 812639 = 1218959) B1218959
theorem B9864827 : Blo 539803 9864827 := bstep (se 1 (by rfl) ⟨7398620, by rfl⟩ : syracuseStep 9864827 = 14797241) B14797241
theorem B2737799 : Blo 539803 2737799 := bstep (se 1 (by rfl) ⟨2053349, by rfl⟩ : syracuseStep 2737799 = 4106699) B4106699
theorem B2311865 : Blo 539803 2311865 := bstep (se 2 (by rfl) ⟨866949, by rfl⟩ : syracuseStep 2311865 = 1733899) B1733899
theorem B542431 : Blo 539803 542431 := bstep (se 1 (by rfl) ⟨406823, by rfl⟩ : syracuseStep 542431 = 813647) B813647
theorem B542511 : Blo 539803 542511 := bstep (se 1 (by rfl) ⟨406883, by rfl⟩ : syracuseStep 542511 = 813767) B813767
theorem B812855 : Blo 539803 812855 := bstep (se 1 (by rfl) ⟨609641, by rfl⟩ : syracuseStep 812855 = 1219283) B1219283
theorem B7997251 : Blo 539803 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B8800067 : Blo 539803 8800067 := bstep (se 1 (by rfl) ⟨6600050, by rfl⟩ : syracuseStep 8800067 = 13200101) B13200101
theorem B4171601 : Blo 539803 4171601 := bstep (se 2 (by rfl) ⟨1564350, by rfl⟩ : syracuseStep 4171601 = 3128701) B3128701
theorem B4614023 : Blo 539803 4614023 := bstep (se 1 (by rfl) ⟨3460517, by rfl⟩ : syracuseStep 4614023 = 6921035) B6921035
theorem B731035 : Blo 539803 731035 := bstep (se 1 (by rfl) ⟨548276, by rfl⟩ : syracuseStep 731035 = 1096553) B1096553
theorem B542619 : Blo 539803 542619 := bstep (se 1 (by rfl) ⟨406964, by rfl⟩ : syracuseStep 542619 = 813929) B813929
theorem B542671 : Blo 539803 542671 := bstep (se 1 (by rfl) ⟨407003, by rfl⟩ : syracuseStep 542671 = 814007) B814007
theorem B542695 : Blo 539803 542695 := bstep (se 1 (by rfl) ⟨407021, by rfl⟩ : syracuseStep 542695 = 814043) B814043
theorem B3090413 : Blo 539803 3090413 := bstep (se 3 (by rfl) ⟨579452, by rfl⟩ : syracuseStep 3090413 = 1158905) B1158905
theorem B5851217 : Blo 539803 5851217 := bstep (se 2 (by rfl) ⟨2194206, by rfl⟩ : syracuseStep 5851217 = 4388413) B4388413
theorem B813161 : Blo 539803 813161 := bstep (se 2 (by rfl) ⟨304935, by rfl⟩ : syracuseStep 813161 = 609871) B609871
theorem B2312327 : Blo 539803 2312327 := bstep (se 1 (by rfl) ⟨1734245, by rfl⟩ : syracuseStep 2312327 = 3468491) B3468491
theorem B6424771 : Blo 539803 6424771 := bstep (se 1 (by rfl) ⟨4818578, by rfl⟩ : syracuseStep 6424771 = 9637157) B9637157
theorem B1214675 : Blo 539803 1214675 := bstep (se 1 (by rfl) ⟨911006, by rfl⟩ : syracuseStep 1214675 = 1822013) B1822013
theorem B1214729 : Blo 539803 1214729 := bstep (se 2 (by rfl) ⟨455523, by rfl⟩ : syracuseStep 1214729 = 911047) B911047
theorem B1853705 : Blo 539803 1853705 := bstep (se 2 (by rfl) ⟨695139, by rfl⟩ : syracuseStep 1853705 = 1390279) B1390279
theorem B2607383 : Blo 539803 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B1370459 : Blo 539803 1370459 := bstep (se 1 (by rfl) ⟨1027844, by rfl⟩ : syracuseStep 1370459 = 2055689) B2055689
theorem B1370479 : Blo 539803 1370479 := bstep (se 1 (by rfl) ⟨1027859, by rfl⟩ : syracuseStep 1370479 = 2055719) B2055719
theorem B911783 : Blo 539803 911783 := bstep (se 1 (by rfl) ⟨683837, by rfl⟩ : syracuseStep 911783 = 1367675) B1367675
theorem B813479 : Blo 539803 813479 := bstep (se 1 (by rfl) ⟨610109, by rfl⟩ : syracuseStep 813479 = 1220219) B1220219
theorem B1829303 : Blo 539803 1829303 := bstep (se 1 (by rfl) ⟨1371977, by rfl⟩ : syracuseStep 1829303 = 2743955) B2743955
theorem B1214945 : Blo 539803 1214945 := bstep (se 2 (by rfl) ⟨455604, by rfl⟩ : syracuseStep 1214945 = 911209) B911209
theorem B2050555 : Blo 539803 2050555 := bstep (se 1 (by rfl) ⟨1537916, by rfl⟩ : syracuseStep 2050555 = 3075833) B3075833
theorem B813563 : Blo 539803 813563 := bstep (se 1 (by rfl) ⟨610172, by rfl⟩ : syracuseStep 813563 = 1220345) B1220345
theorem B911945 : Blo 539803 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B608863 : Blo 539803 608863 := bstep (se 1 (by rfl) ⟨456647, by rfl⟩ : syracuseStep 608863 = 913295) B913295
theorem B813689 : Blo 539803 813689 := bstep (se 2 (by rfl) ⟨305133, by rfl⟩ : syracuseStep 813689 = 610267) B610267
theorem B813743 : Blo 539803 813743 := bstep (se 1 (by rfl) ⟨610307, by rfl⟩ : syracuseStep 813743 = 1220615) B1220615
theorem B813791 : Blo 539803 813791 := bstep (se 1 (by rfl) ⟨610343, by rfl⟩ : syracuseStep 813791 = 1220687) B1220687
theorem B772831 : Blo 539803 772831 := bstep (se 1 (by rfl) ⟨579623, by rfl⟩ : syracuseStep 772831 = 1159247) B1159247
theorem B1215251 : Blo 539803 1215251 := bstep (se 1 (by rfl) ⟨911438, by rfl⟩ : syracuseStep 1215251 = 1822877) B1822877
theorem B650039 : Blo 539803 650039 := bstep (se 1 (by rfl) ⟨487529, by rfl⟩ : syracuseStep 650039 = 975059) B975059
theorem B2190235 : Blo 539803 2190235 := bstep (se 1 (by rfl) ⟨1642676, by rfl⟩ : syracuseStep 2190235 = 3285353) B3285353
theorem B814055 : Blo 539803 814055 := bstep (se 1 (by rfl) ⟨610541, by rfl⟩ : syracuseStep 814055 = 1221083) B1221083
theorem B1371127 : Blo 539803 1371127 := bstep (se 1 (by rfl) ⟨1028345, by rfl⟩ : syracuseStep 1371127 = 2056691) B2056691
theorem B2059303 : Blo 539803 2059303 := bstep (se 1 (by rfl) ⟨1544477, by rfl⟩ : syracuseStep 2059303 = 3088955) B3088955
theorem B1215611 : Blo 539803 1215611 := bstep (se 1 (by rfl) ⟨911708, by rfl⟩ : syracuseStep 1215611 = 1823417) B1823417
theorem B2739419 : Blo 539803 2739419 := bstep (se 1 (by rfl) ⟨2054564, by rfl⟩ : syracuseStep 2739419 = 4109129) B4109129
theorem B1215737 : Blo 539803 1215737 := bstep (se 2 (by rfl) ⟨455901, by rfl⟩ : syracuseStep 1215737 = 911803) B911803
theorem B1371431 : Blo 539803 1371431 := bstep (se 1 (by rfl) ⟨1028573, by rfl⟩ : syracuseStep 1371431 = 2057147) B2057147
theorem B1215881 : Blo 539803 1215881 := bstep (se 2 (by rfl) ⟨455955, by rfl⟩ : syracuseStep 1215881 = 911911) B911911
theorem B3075515 : Blo 539803 3075515 := bstep (se 1 (by rfl) ⟨2306636, by rfl⟩ : syracuseStep 3075515 = 4613273) B4613273
theorem B2051527 : Blo 539803 2051527 := bstep (se 1 (by rfl) ⟨1538645, by rfl⟩ : syracuseStep 2051527 = 3077291) B3077291
theorem B2346455 : Blo 539803 2346455 := bstep (se 1 (by rfl) ⟨1759841, by rfl⟩ : syracuseStep 2346455 = 3519683) B3519683
theorem B1216007 : Blo 539803 1216007 := bstep (se 1 (by rfl) ⟨912005, by rfl⟩ : syracuseStep 1216007 = 1824011) B1824011
theorem B912991 : Blo 539803 912991 := bstep (se 1 (by rfl) ⟨684743, by rfl⟩ : syracuseStep 912991 = 1369487) B1369487
theorem B1216187 : Blo 539803 1216187 := bstep (se 1 (by rfl) ⟨912140, by rfl⟩ : syracuseStep 1216187 = 1824281) B1824281
theorem B610015 : Blo 539803 610015 := bstep (se 1 (by rfl) ⟨457511, by rfl⟩ : syracuseStep 610015 = 915023) B915023
theorem B3509995 : Blo 539803 3509995 := bstep (se 1 (by rfl) ⟨2632496, by rfl⟩ : syracuseStep 3509995 = 5264993) B5264993
theorem B913207 : Blo 539803 913207 := bstep (se 1 (by rfl) ⟨684905, by rfl⟩ : syracuseStep 913207 = 1369811) B1369811
theorem B1216313 : Blo 539803 1216313 := bstep (se 2 (by rfl) ⟨456117, by rfl⟩ : syracuseStep 1216313 = 912235) B912235
theorem B2060093 : Blo 539803 2060093 := bstep (se 3 (by rfl) ⟨386267, by rfl⟩ : syracuseStep 2060093 = 772535) B772535
theorem B2314241 : Blo 539803 2314241 := bstep (se 2 (by rfl) ⟨867840, by rfl⟩ : syracuseStep 2314241 = 1735681) B1735681
theorem B5836859 : Blo 539803 5836859 := bstep (se 1 (by rfl) ⟨4377644, by rfl⟩ : syracuseStep 5836859 = 8755289) B8755289
theorem B2084923 : Blo 539803 2084923 := bstep (se 1 (by rfl) ⟨1563692, by rfl⟩ : syracuseStep 2084923 = 3127385) B3127385
theorem B84275315 : Blo 539803 84275315 := bstep (se 1 (by rfl) ⟨63206486, by rfl⟩ : syracuseStep 84275315 = 126412973) B126412973
theorem B9892043 : Blo 539803 9892043 := bstep (se 1 (by rfl) ⟨7419032, by rfl⟩ : syracuseStep 9892043 = 14838065) B14838065
theorem B1822931 : Blo 539803 1822931 := bstep (se 1 (by rfl) ⟨1367198, by rfl⟩ : syracuseStep 1822931 = 2734397) B2734397
theorem B913673 : Blo 539803 913673 := bstep (se 2 (by rfl) ⟨342627, by rfl⟩ : syracuseStep 913673 = 685255) B685255
theorem B610591 : Blo 539803 610591 := bstep (se 1 (by rfl) ⟨457943, by rfl⟩ : syracuseStep 610591 = 915887) B915887
theorem B2740553 : Blo 539803 2740553 := bstep (se 2 (by rfl) ⟨1027707, by rfl⟩ : syracuseStep 2740553 = 2055415) B2055415
theorem B684379 : Blo 539803 684379 := bstep (se 1 (by rfl) ⟨513284, by rfl⟩ : syracuseStep 684379 = 1026569) B1026569
theorem B1216943 : Blo 539803 1216943 := bstep (se 1 (by rfl) ⟨912707, by rfl⟩ : syracuseStep 1216943 = 1825415) B1825415
theorem B1216979 : Blo 539803 1216979 := bstep (se 1 (by rfl) ⟨912734, by rfl⟩ : syracuseStep 1216979 = 1825469) B1825469
theorem B40104409 : Blo 539803 40104409 := bstep (se 2 (by rfl) ⟨15039153, by rfl⟩ : syracuseStep 40104409 = 30078307) B30078307
theorem B3084763 : Blo 539803 3084763 := bstep (se 1 (by rfl) ⟨2313572, by rfl⟩ : syracuseStep 3084763 = 4627145) B4627145
theorem B1946081 : Blo 539803 1946081 := bstep (se 2 (by rfl) ⟨729780, by rfl⟩ : syracuseStep 1946081 = 1459561) B1459561
theorem B1823201 : Blo 539803 1823201 := bstep (se 2 (by rfl) ⟨683700, by rfl⟩ : syracuseStep 1823201 = 1367401) B1367401
theorem B1356257 : Blo 539803 1356257 := bstep (se 2 (by rfl) ⟨508596, by rfl⟩ : syracuseStep 1356257 = 1017193) B1017193
theorem B10711601 : Blo 539803 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B11080253 : Blo 539803 11080253 := bstep (se 3 (by rfl) ⟨2077547, by rfl⟩ : syracuseStep 11080253 = 4155095) B4155095
theorem B684607 : Blo 539803 684607 := bstep (se 1 (by rfl) ⟨513455, by rfl⟩ : syracuseStep 684607 = 1026911) B1026911
theorem B1217087 : Blo 539803 1217087 := bstep (se 1 (by rfl) ⟨912815, by rfl⟩ : syracuseStep 1217087 = 1825631) B1825631
theorem B1217195 : Blo 539803 1217195 := bstep (se 1 (by rfl) ⟨912896, by rfl⟩ : syracuseStep 1217195 = 1825793) B1825793
theorem B652087 : Blo 539803 652087 := bstep (se 1 (by rfl) ⟨489065, by rfl⟩ : syracuseStep 652087 = 978131) B978131
theorem B676687 : Blo 539803 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B3076973 : Blo 539803 3076973 := bstep (se 3 (by rfl) ⟨576932, by rfl⟩ : syracuseStep 3076973 = 1153865) B1153865
theorem B1373071 : Blo 539803 1373071 := bstep (se 1 (by rfl) ⟨1029803, by rfl⟩ : syracuseStep 1373071 = 2059607) B2059607
theorem B10548143 : Blo 539803 10548143 := bstep (se 1 (by rfl) ⟨7911107, by rfl⟩ : syracuseStep 10548143 = 15822215) B15822215
theorem B1299655 : Blo 539803 1299655 := bstep (se 1 (by rfl) ⟨974741, by rfl⟩ : syracuseStep 1299655 = 1949483) B1949483
theorem B1217735 : Blo 539803 1217735 := bstep (se 1 (by rfl) ⟨913301, by rfl⟩ : syracuseStep 1217735 = 1826603) B1826603
theorem B1602775 : Blo 539803 1602775 := bstep (se 1 (by rfl) ⟨1202081, by rfl⟩ : syracuseStep 1602775 = 2404163) B2404163
theorem B914665 : Blo 539803 914665 := bstep (se 2 (by rfl) ⟨342999, by rfl⟩ : syracuseStep 914665 = 685999) B685999
theorem B1463539 : Blo 539803 1463539 := bstep (se 1 (by rfl) ⟨1097654, by rfl⟩ : syracuseStep 1463539 = 2195309) B2195309
theorem B914719 : Blo 539803 914719 := bstep (se 1 (by rfl) ⟨686039, by rfl⟩ : syracuseStep 914719 = 1372079) B1372079
theorem B685351 : Blo 539803 685351 := bstep (se 1 (by rfl) ⟨514013, by rfl⟩ : syracuseStep 685351 = 1028027) B1028027
theorem B2053471 : Blo 539803 2053471 := bstep (se 1 (by rfl) ⟨1540103, by rfl⟩ : syracuseStep 2053471 = 3080207) B3080207
theorem B1373537 : Blo 539803 1373537 := bstep (se 2 (by rfl) ⟨515076, by rfl⟩ : syracuseStep 1373537 = 1030153) B1030153
theorem B1217915 : Blo 539803 1217915 := bstep (se 1 (by rfl) ⟨913436, by rfl⟩ : syracuseStep 1217915 = 1826873) B1826873
theorem B1848737 : Blo 539803 1848737 := bstep (se 2 (by rfl) ⟨693276, by rfl⟩ : syracuseStep 1848737 = 1386553) B1386553
theorem B578983 : Blo 539803 578983 := bstep (se 1 (by rfl) ⟨434237, by rfl⟩ : syracuseStep 578983 = 868475) B868475
theorem B1218041 : Blo 539803 1218041 := bstep (se 2 (by rfl) ⟨456765, by rfl⟩ : syracuseStep 1218041 = 913531) B913531
theorem B1982675 : Blo 539803 1982675 := bstep (se 1 (by rfl) ⟨1487006, by rfl⟩ : syracuseStep 1982675 = 2974013) B2974013
theorem B1218131 : Blo 539803 1218131 := bstep (se 1 (by rfl) ⟨913598, by rfl⟩ : syracuseStep 1218131 = 1827197) B1827197
theorem B2741849 : Blo 539803 2741849 := bstep (se 2 (by rfl) ⟨1028193, by rfl⟩ : syracuseStep 2741849 = 2056387) B2056387
theorem B685675 : Blo 539803 685675 := bstep (se 1 (by rfl) ⟨514256, by rfl⟩ : syracuseStep 685675 = 1028513) B1028513
theorem B2774663 : Blo 539803 2774663 := bstep (se 1 (by rfl) ⟨2080997, by rfl⟩ : syracuseStep 2774663 = 4161995) B4161995
theorem B1824443 : Blo 539803 1824443 := bstep (se 1 (by rfl) ⟨1368332, by rfl⟩ : syracuseStep 1824443 = 2736665) B2736665
theorem B915131 : Blo 539803 915131 := bstep (se 1 (by rfl) ⟨686348, by rfl⟩ : syracuseStep 915131 = 1372697) B1372697
theorem B866027 : Blo 539803 866027 := bstep (se 1 (by rfl) ⟨649520, by rfl⟩ : syracuseStep 866027 = 1299041) B1299041
theorem B1218311 : Blo 539803 1218311 := bstep (se 1 (by rfl) ⟨913733, by rfl⟩ : syracuseStep 1218311 = 1827467) B1827467
theorem B2053943 : Blo 539803 2053943 := bstep (se 1 (by rfl) ⟨1540457, by rfl⟩ : syracuseStep 2053943 = 3080915) B3080915
theorem B685903 : Blo 539803 685903 := bstep (se 1 (by rfl) ⟨514427, by rfl⟩ : syracuseStep 685903 = 1028855) B1028855
theorem B2733911 : Blo 539803 2733911 := bstep (se 1 (by rfl) ⟨2050433, by rfl⟩ : syracuseStep 2733911 = 4100867) B4100867
theorem B2316239 : Blo 539803 2316239 := bstep (se 1 (by rfl) ⟨1737179, by rfl⟩ : syracuseStep 2316239 = 3474359) B3474359
theorem B2775073 : Blo 539803 2775073 := bstep (se 2 (by rfl) ⟨1040652, by rfl⟩ : syracuseStep 2775073 = 2081305) B2081305
theorem B5937185 : Blo 539803 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B2308175 : Blo 539803 2308175 := bstep (se 1 (by rfl) ⟨1731131, by rfl⟩ : syracuseStep 2308175 = 3462263) B3462263
theorem B2054429 : Blo 539803 2054429 := bstep (se 3 (by rfl) ⟨385205, by rfl⟩ : syracuseStep 2054429 = 770411) B770411
theorem B1366379 : Blo 539803 1366379 := bstep (se 1 (by rfl) ⟨1024784, by rfl⟩ : syracuseStep 1366379 = 2049569) B2049569
theorem B1218923 : Blo 539803 1218923 := bstep (se 1 (by rfl) ⟨914192, by rfl⟩ : syracuseStep 1218923 = 1828385) B1828385
theorem B2087279 : Blo 539803 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B1235375 : Blo 539803 1235375 := bstep (se 1 (by rfl) ⟨926531, by rfl⟩ : syracuseStep 1235375 = 1853063) B1853063
theorem B1219067 : Blo 539803 1219067 := bstep (se 1 (by rfl) ⟨914300, by rfl⟩ : syracuseStep 1219067 = 1828601) B1828601
theorem B1366591 : Blo 539803 1366591 := bstep (se 1 (by rfl) ⟨1024943, by rfl⟩ : syracuseStep 1366591 = 2049887) B2049887
theorem B940607 : Blo 539803 940607 := bstep (se 1 (by rfl) ⟨705455, by rfl⟩ : syracuseStep 940607 = 1410911) B1410911
theorem B1219193 : Blo 539803 1219193 := bstep (se 2 (by rfl) ⟨457197, by rfl⟩ : syracuseStep 1219193 = 914395) B914395
theorem B2316923 : Blo 539803 2316923 := bstep (se 1 (by rfl) ⟨1737692, by rfl⟩ : syracuseStep 2316923 = 3475385) B3475385
theorem B1366703 : Blo 539803 1366703 := bstep (se 1 (by rfl) ⟨1025027, by rfl⟩ : syracuseStep 1366703 = 2050055) B2050055
theorem B1153711 : Blo 539803 1153711 := bstep (se 1 (by rfl) ⟨865283, by rfl⟩ : syracuseStep 1153711 = 1730567) B1730567
theorem B1219247 : Blo 539803 1219247 := bstep (se 1 (by rfl) ⟨914435, by rfl⟩ : syracuseStep 1219247 = 1828871) B1828871
theorem B2472643 : Blo 539803 2472643 := bstep (se 1 (by rfl) ⟨1854482, by rfl⟩ : syracuseStep 2472643 = 3708965) B3708965
theorem B1219319 : Blo 539803 1219319 := bstep (se 1 (by rfl) ⟨914489, by rfl⟩ : syracuseStep 1219319 = 1828979) B1828979
theorem B3078931 : Blo 539803 3078931 := bstep (se 1 (by rfl) ⟨2309198, by rfl⟩ : syracuseStep 3078931 = 4618397) B4618397
theorem B809807 : Blo 539803 809807 := bstep (se 1 (by rfl) ⟨607355, by rfl⟩ : syracuseStep 809807 = 1214711) B1214711
theorem B1219499 : Blo 539803 1219499 := bstep (se 1 (by rfl) ⟨914624, by rfl⟩ : syracuseStep 1219499 = 1829249) B1829249
theorem B1367027 : Blo 539803 1367027 := bstep (se 1 (by rfl) ⟨1025270, by rfl⟩ : syracuseStep 1367027 = 2050541) B2050541
theorem B7044259 : Blo 539803 7044259 := bstep (se 1 (by rfl) ⟨5283194, by rfl⟩ : syracuseStep 7044259 = 10566389) B10566389
theorem B1367239 : Blo 539803 1367239 := bstep (se 1 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 1367239 = 2050859) B2050859
theorem B810203 : Blo 539803 810203 := bstep (se 1 (by rfl) ⟨607652, by rfl⟩ : syracuseStep 810203 = 1215305) B1215305
theorem B539935 : Blo 539803 539935 := bstep (se 1 (by rfl) ⟨404951, by rfl⟩ : syracuseStep 539935 = 809903) B809903
theorem B539995 : Blo 539803 539995 := bstep (se 1 (by rfl) ⟨404996, by rfl⟩ : syracuseStep 539995 = 809993) B809993
theorem B540015 : Blo 539803 540015 := bstep (se 1 (by rfl) ⟨405011, by rfl⟩ : syracuseStep 540015 = 810023) B810023
theorem B810377 : Blo 539803 810377 := bstep (se 2 (by rfl) ⟨303891, by rfl⟩ : syracuseStep 810377 = 607783) B607783
theorem B540071 : Blo 539803 540071 := bstep (se 1 (by rfl) ⟨405053, by rfl⟩ : syracuseStep 540071 = 810107) B810107
theorem B1220039 : Blo 539803 1220039 := bstep (se 1 (by rfl) ⟨915029, by rfl⟩ : syracuseStep 1220039 = 1830059) B1830059
theorem B540155 : Blo 539803 540155 := bstep (se 1 (by rfl) ⟨405116, by rfl⟩ : syracuseStep 540155 = 810233) B810233
theorem B6250007 : Blo 539803 6250007 := bstep (se 1 (by rfl) ⟨4687505, by rfl⟩ : syracuseStep 6250007 = 9375011) B9375011
theorem B540223 : Blo 539803 540223 := bstep (se 1 (by rfl) ⟨405167, by rfl⟩ : syracuseStep 540223 = 810335) B810335
theorem B540231 : Blo 539803 540231 := bstep (se 1 (by rfl) ⟨405173, by rfl⟩ : syracuseStep 540231 = 810347) B810347
theorem B1826387 : Blo 539803 1826387 := bstep (se 1 (by rfl) ⟨1369790, by rfl⟩ : syracuseStep 1826387 = 2739581) B2739581
theorem B3087953 : Blo 539803 3087953 := bstep (se 2 (by rfl) ⟨1157982, by rfl⟩ : syracuseStep 3087953 = 2315965) B2315965
theorem B8797841 : Blo 539803 8797841 := bstep (se 2 (by rfl) ⟨3299190, by rfl⟩ : syracuseStep 8797841 = 6598381) B6598381
theorem B974497 : Blo 539803 974497 := bstep (se 2 (by rfl) ⟨365436, by rfl⟩ : syracuseStep 974497 = 730873) B730873
theorem B540383 : Blo 539803 540383 := bstep (se 1 (by rfl) ⟨405287, by rfl⟩ : syracuseStep 540383 = 810575) B810575
theorem B810731 : Blo 539803 810731 := bstep (se 1 (by rfl) ⟨608048, by rfl⟩ : syracuseStep 810731 = 1216097) B1216097
theorem B2309867 : Blo 539803 2309867 := bstep (se 1 (by rfl) ⟨1732400, by rfl⟩ : syracuseStep 2309867 = 3464801) B3464801
theorem B696043 : Blo 539803 696043 := bstep (se 1 (by rfl) ⟨522032, by rfl⟩ : syracuseStep 696043 = 1044065) B1044065
theorem B2932487 : Blo 539803 2932487 := bstep (se 1 (by rfl) ⟨2199365, by rfl⟩ : syracuseStep 2932487 = 4398731) B4398731
theorem B2596619 : Blo 539803 2596619 := bstep (se 1 (by rfl) ⟨1947464, by rfl⟩ : syracuseStep 2596619 = 3894929) B3894929
theorem B18013985 : Blo 539803 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B540463 : Blo 539803 540463 := bstep (se 1 (by rfl) ⟨405347, by rfl⟩ : syracuseStep 540463 = 810695) B810695
theorem B1220399 : Blo 539803 1220399 := bstep (se 1 (by rfl) ⟨915299, by rfl⟩ : syracuseStep 1220399 = 1830599) B1830599
theorem B1154873 : Blo 539803 1154873 := bstep (se 2 (by rfl) ⟨433077, by rfl⟩ : syracuseStep 1154873 = 866155) B866155
theorem B3694409 : Blo 539803 3694409 := bstep (se 2 (by rfl) ⟨1385403, by rfl⟩ : syracuseStep 3694409 = 2770807) B2770807
theorem B1752961 : Blo 539803 1752961 := bstep (se 2 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 1752961 = 1314721) B1314721
theorem B540571 : Blo 539803 540571 := bstep (se 1 (by rfl) ⟨405428, by rfl⟩ : syracuseStep 540571 = 810857) B810857
theorem B540623 : Blo 539803 540623 := bstep (se 1 (by rfl) ⟨405467, by rfl⟩ : syracuseStep 540623 = 810935) B810935
theorem B810959 : Blo 539803 810959 := bstep (se 1 (by rfl) ⟨608219, by rfl⟩ : syracuseStep 810959 = 1216439) B1216439
theorem B540647 : Blo 539803 540647 := bstep (se 1 (by rfl) ⟨405485, by rfl⟩ : syracuseStep 540647 = 810971) B810971
theorem B3891239 : Blo 539803 3891239 := bstep (se 1 (by rfl) ⟨2918429, by rfl⟩ : syracuseStep 3891239 = 5836859) B5836859
theorem B6594695 : Blo 539803 6594695 := bstep (se 1 (by rfl) ⟨4946021, by rfl⟩ : syracuseStep 6594695 = 9892043) B9892043
theorem B1827035 : Blo 539803 1827035 := bstep (se 1 (by rfl) ⟨1370276, by rfl⟩ : syracuseStep 1827035 = 2740553) B2740553
theorem B1736923 : Blo 539803 1736923 := bstep (se 1 (by rfl) ⟨1302692, by rfl⟩ : syracuseStep 1736923 = 2605385) B2605385
theorem B540903 : Blo 539803 540903 := bstep (se 1 (by rfl) ⟨405677, by rfl⟩ : syracuseStep 540903 = 811355) B811355
theorem B2195687 : Blo 539803 2195687 := bstep (se 1 (by rfl) ⟨1646765, by rfl⟩ : syracuseStep 2195687 = 3293531) B3293531
theorem B811295 : Blo 539803 811295 := bstep (se 1 (by rfl) ⟨608471, by rfl⟩ : syracuseStep 811295 = 1216943) B1216943
theorem B811319 : Blo 539803 811319 := bstep (se 1 (by rfl) ⟨608489, by rfl⟩ : syracuseStep 811319 = 1216979) B1216979
theorem B811391 : Blo 539803 811391 := bstep (se 1 (by rfl) ⟨608543, by rfl⟩ : syracuseStep 811391 = 1217087) B1217087
theorem B541055 : Blo 539803 541055 := bstep (se 1 (by rfl) ⟨405791, by rfl⟩ : syracuseStep 541055 = 811583) B811583
theorem B811463 : Blo 539803 811463 := bstep (se 1 (by rfl) ⟨608597, by rfl⟩ : syracuseStep 811463 = 1217195) B1217195
theorem B1540559 : Blo 539803 1540559 := bstep (se 1 (by rfl) ⟨1155419, by rfl⟩ : syracuseStep 1540559 = 2310839) B2310839
theorem B541135 : Blo 539803 541135 := bstep (se 1 (by rfl) ⟨405851, by rfl⟩ : syracuseStep 541135 = 811703) B811703
theorem B6947279 : Blo 539803 6947279 := bstep (se 1 (by rfl) ⟨5210459, by rfl⟩ : syracuseStep 6947279 = 10420919) B10420919
theorem B1827305 : Blo 539803 1827305 := bstep (se 2 (by rfl) ⟨685239, by rfl⟩ : syracuseStep 1827305 = 1370479) B1370479
theorem B541287 : Blo 539803 541287 := bstep (se 1 (by rfl) ⟨405965, by rfl⟩ : syracuseStep 541287 = 811931) B811931
theorem B4113017 : Blo 539803 4113017 := bstep (se 2 (by rfl) ⟨1542381, by rfl⟩ : syracuseStep 4113017 = 3084763) B3084763
theorem B17793665 : Blo 539803 17793665 := bstep (se 2 (by rfl) ⟨6672624, by rfl⟩ : syracuseStep 17793665 = 13345249) B13345249
theorem B811817 : Blo 539803 811817 := bstep (se 2 (by rfl) ⟨304431, by rfl⟩ : syracuseStep 811817 = 608863) B608863
theorem B811823 : Blo 539803 811823 := bstep (se 1 (by rfl) ⟨608867, by rfl⟩ : syracuseStep 811823 = 1217735) B1217735
theorem B541551 : Blo 539803 541551 := bstep (se 1 (by rfl) ⟨406163, by rfl⟩ : syracuseStep 541551 = 812327) B812327
theorem B811943 : Blo 539803 811943 := bstep (se 1 (by rfl) ⟨608957, by rfl⟩ : syracuseStep 811943 = 1217915) B1217915
theorem B541607 : Blo 539803 541607 := bstep (se 1 (by rfl) ⟨406205, by rfl⟩ : syracuseStep 541607 = 812411) B812411
theorem B812027 : Blo 539803 812027 := bstep (se 1 (by rfl) ⟨609020, by rfl⟩ : syracuseStep 812027 = 1218041) B1218041
theorem B541691 : Blo 539803 541691 := bstep (se 1 (by rfl) ⟨406268, by rfl⟩ : syracuseStep 541691 = 812537) B812537
theorem B4105241 : Blo 539803 4105241 := bstep (se 2 (by rfl) ⟨1539465, by rfl⟩ : syracuseStep 4105241 = 3078931) B3078931
theorem B6931493 : Blo 539803 6931493 := bstep (se 4 (by rfl) ⟨649827, by rfl⟩ : syracuseStep 6931493 = 1299655) B1299655
theorem B812087 : Blo 539803 812087 := bstep (se 1 (by rfl) ⟨609065, by rfl⟩ : syracuseStep 812087 = 1218131) B1218131
theorem B1827899 : Blo 539803 1827899 := bstep (se 1 (by rfl) ⟨1370924, by rfl⟩ : syracuseStep 1827899 = 2741849) B2741849
theorem B541759 : Blo 539803 541759 := bstep (se 1 (by rfl) ⟨406319, by rfl⟩ : syracuseStep 541759 = 812639) B812639
theorem B902249 : Blo 539803 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B1541243 : Blo 539803 1541243 := bstep (se 1 (by rfl) ⟨1155932, by rfl⟩ : syracuseStep 1541243 = 2311865) B2311865
theorem B4121765 : Blo 539803 4121765 := bstep (se 4 (by rfl) ⟨386415, by rfl⟩ : syracuseStep 4121765 = 772831) B772831
theorem B812207 : Blo 539803 812207 := bstep (se 1 (by rfl) ⟨609155, by rfl⟩ : syracuseStep 812207 = 1218311) B1218311
theorem B1369295 : Blo 539803 1369295 := bstep (se 1 (by rfl) ⟨1026971, by rfl⟩ : syracuseStep 1369295 = 2053943) B2053943
theorem B541903 : Blo 539803 541903 := bstep (se 1 (by rfl) ⟨406427, by rfl⟩ : syracuseStep 541903 = 812855) B812855
theorem B5866711 : Blo 539803 5866711 := bstep (se 1 (by rfl) ⟨4400033, by rfl⟩ : syracuseStep 5866711 = 8800067) B8800067
theorem B3712229 : Blo 539803 3712229 := bstep (se 4 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 3712229 = 696043) B696043
theorem B1828169 : Blo 539803 1828169 := bstep (se 2 (by rfl) ⟨685563, by rfl⟩ : syracuseStep 1828169 = 1371127) B1371127
theorem B2745737 : Blo 539803 2745737 := bstep (se 2 (by rfl) ⟨1029651, by rfl⟩ : syracuseStep 2745737 = 2059303) B2059303
theorem B3900811 : Blo 539803 3900811 := bstep (se 1 (by rfl) ⟨2925608, by rfl⟩ : syracuseStep 3900811 = 5851217) B5851217
theorem B542107 : Blo 539803 542107 := bstep (se 1 (by rfl) ⟨406580, by rfl⟩ : syracuseStep 542107 = 813161) B813161
theorem B1541551 : Blo 539803 1541551 := bstep (se 1 (by rfl) ⟨1156163, by rfl⟩ : syracuseStep 1541551 = 2312327) B2312327
theorem B1369619 : Blo 539803 1369619 := bstep (se 1 (by rfl) ⟨1027214, by rfl⟩ : syracuseStep 1369619 = 2054429) B2054429
theorem B910919 : Blo 539803 910919 := bstep (se 1 (by rfl) ⟨683189, by rfl⟩ : syracuseStep 910919 = 1366379) B1366379
theorem B812615 : Blo 539803 812615 := bstep (se 1 (by rfl) ⟨609461, by rfl⟩ : syracuseStep 812615 = 1218923) B1218923
theorem B607855 : Blo 539803 607855 := bstep (se 1 (by rfl) ⟨455891, by rfl⟩ : syracuseStep 607855 = 911783) B911783
theorem B542319 : Blo 539803 542319 := bstep (se 1 (by rfl) ⟨406739, by rfl⟩ : syracuseStep 542319 = 813479) B813479
theorem B1951385 : Blo 539803 1951385 := bstep (se 2 (by rfl) ⟨731769, by rfl⟩ : syracuseStep 1951385 = 1463539) B1463539
theorem B812711 : Blo 539803 812711 := bstep (se 1 (by rfl) ⟨609533, by rfl⟩ : syracuseStep 812711 = 1219067) B1219067
theorem B542375 : Blo 539803 542375 := bstep (se 1 (by rfl) ⟨406781, by rfl⟩ : syracuseStep 542375 = 813563) B813563
theorem B607963 : Blo 539803 607963 := bstep (se 1 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 607963 = 911945) B911945
theorem B812795 : Blo 539803 812795 := bstep (se 1 (by rfl) ⟨609596, by rfl⟩ : syracuseStep 812795 = 1219193) B1219193
theorem B542459 : Blo 539803 542459 := bstep (se 1 (by rfl) ⟨406844, by rfl⟩ : syracuseStep 542459 = 813689) B813689
theorem B911135 : Blo 539803 911135 := bstep (se 1 (by rfl) ⟨683351, by rfl⟩ : syracuseStep 911135 = 1366703) B1366703
theorem B812831 : Blo 539803 812831 := bstep (se 1 (by rfl) ⟨609623, by rfl⟩ : syracuseStep 812831 = 1219247) B1219247
theorem B542495 : Blo 539803 542495 := bstep (se 1 (by rfl) ⟨406871, by rfl⟩ : syracuseStep 542495 = 813743) B813743
theorem B2737961 : Blo 539803 2737961 := bstep (se 2 (by rfl) ⟨1026735, by rfl⟩ : syracuseStep 2737961 = 2053471) B2053471
theorem B542527 : Blo 539803 542527 := bstep (se 1 (by rfl) ⟨406895, by rfl⟩ : syracuseStep 542527 = 813791) B813791
theorem B812879 : Blo 539803 812879 := bstep (se 1 (by rfl) ⟨609659, by rfl⟩ : syracuseStep 812879 = 1219319) B1219319
theorem B1542017 : Blo 539803 1542017 := bstep (se 2 (by rfl) ⟨578256, by rfl⟩ : syracuseStep 1542017 = 1156513) B1156513
theorem B771977 : Blo 539803 771977 := bstep (se 2 (by rfl) ⟨289491, by rfl⟩ : syracuseStep 771977 = 578983) B578983
theorem B812999 : Blo 539803 812999 := bstep (se 1 (by rfl) ⟨609749, by rfl⟩ : syracuseStep 812999 = 1219499) B1219499
theorem B542703 : Blo 539803 542703 := bstep (se 1 (by rfl) ⟨407027, by rfl⟩ : syracuseStep 542703 = 814055) B814055
theorem B911351 : Blo 539803 911351 := bstep (se 1 (by rfl) ⟨683513, by rfl⟩ : syracuseStep 911351 = 1367027) B1367027
theorem B2050343 : Blo 539803 2050343 := bstep (se 1 (by rfl) ⟨1537757, by rfl⟩ : syracuseStep 2050343 = 3075515) B3075515
theorem B813353 : Blo 539803 813353 := bstep (se 2 (by rfl) ⟨305007, by rfl⟩ : syracuseStep 813353 = 610015) B610015
theorem B813359 : Blo 539803 813359 := bstep (se 1 (by rfl) ⟨610019, by rfl⟩ : syracuseStep 813359 = 1220039) B1220039
theorem B4679993 : Blo 539803 4679993 := bstep (se 2 (by rfl) ⟨1754997, by rfl⟩ : syracuseStep 4679993 = 3509995) B3509995
theorem B2058635 : Blo 539803 2058635 := bstep (se 1 (by rfl) ⟨1543976, by rfl⟩ : syracuseStep 2058635 = 3087953) B3087953
theorem B23685605 : Blo 539803 23685605 := bstep (se 4 (by rfl) ⟨2220525, by rfl⟩ : syracuseStep 23685605 = 4441051) B4441051
theorem B2337281 : Blo 539803 2337281 := bstep (se 2 (by rfl) ⟨876480, by rfl⟩ : syracuseStep 2337281 = 1752961) B1752961
theorem B1731079 : Blo 539803 1731079 := bstep (se 1 (by rfl) ⟨1298309, by rfl⟩ : syracuseStep 1731079 = 2596619) B2596619
theorem B13896197 : Blo 539803 13896197 := bstep (se 4 (by rfl) ⟨1302768, by rfl⟩ : syracuseStep 13896197 = 2605537) B2605537
theorem B813599 : Blo 539803 813599 := bstep (se 1 (by rfl) ⟨610199, by rfl⟩ : syracuseStep 813599 = 1220399) B1220399
theorem B1542827 : Blo 539803 1542827 := bstep (se 1 (by rfl) ⟨1157120, by rfl⟩ : syracuseStep 1542827 = 2314241) B2314241
theorem B56183543 : Blo 539803 56183543 := bstep (se 1 (by rfl) ⟨42137657, by rfl⟩ : syracuseStep 56183543 = 84275315) B84275315
theorem B1215287 : Blo 539803 1215287 := bstep (se 1 (by rfl) ⟨911465, by rfl⟩ : syracuseStep 1215287 = 1822931) B1822931
theorem B2599735 : Blo 539803 2599735 := bstep (se 1 (by rfl) ⟨1949801, by rfl⟩ : syracuseStep 2599735 = 3899603) B3899603
theorem B609115 : Blo 539803 609115 := bstep (se 1 (by rfl) ⟨456836, by rfl⟩ : syracuseStep 609115 = 913673) B913673
theorem B813983 : Blo 539803 813983 := bstep (se 1 (by rfl) ⟨610487, by rfl⟩ : syracuseStep 813983 = 1220975) B1220975
theorem B814031 : Blo 539803 814031 := bstep (se 1 (by rfl) ⟨610523, by rfl⟩ : syracuseStep 814031 = 1221047) B1221047
theorem B4385755 : Blo 539803 4385755 := bstep (se 1 (by rfl) ⟨3289316, by rfl⟩ : syracuseStep 4385755 = 6578633) B6578633
theorem B11119589 : Blo 539803 11119589 := bstep (se 4 (by rfl) ⟨1042461, by rfl⟩ : syracuseStep 11119589 = 2084923) B2084923
theorem B1297387 : Blo 539803 1297387 := bstep (se 1 (by rfl) ⟨973040, by rfl⟩ : syracuseStep 1297387 = 1946081) B1946081
theorem B1215467 : Blo 539803 1215467 := bstep (se 1 (by rfl) ⟨911600, by rfl⟩ : syracuseStep 1215467 = 1823201) B1823201
theorem B904171 : Blo 539803 904171 := bstep (se 1 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 904171 = 1356257) B1356257
theorem B814121 : Blo 539803 814121 := bstep (se 2 (by rfl) ⟨305295, by rfl⟩ : syracuseStep 814121 = 610591) B610591
theorem B912431 : Blo 539803 912431 := bstep (se 1 (by rfl) ⟨684323, by rfl⟩ : syracuseStep 912431 = 1368647) B1368647
theorem B814127 : Blo 539803 814127 := bstep (se 1 (by rfl) ⟨610595, by rfl⟩ : syracuseStep 814127 = 1221191) B1221191
theorem B6171713 : Blo 539803 6171713 := bstep (se 2 (by rfl) ⟨2314392, by rfl⟩ : syracuseStep 6171713 = 4628785) B4628785
theorem B814151 : Blo 539803 814151 := bstep (se 1 (by rfl) ⟨610613, by rfl⟩ : syracuseStep 814151 = 1221227) B1221227
theorem B26405975 : Blo 539803 26405975 := bstep (se 1 (by rfl) ⟨19804481, by rfl⟩ : syracuseStep 26405975 = 39608963) B39608963
theorem B912505 : Blo 539803 912505 := bstep (se 2 (by rfl) ⟨342189, by rfl⟩ : syracuseStep 912505 = 684379) B684379
theorem B5287133 : Blo 539803 5287133 := bstep (se 3 (by rfl) ⟨991337, by rfl⟩ : syracuseStep 5287133 = 1982675) B1982675
theorem B2051315 : Blo 539803 2051315 := bstep (se 1 (by rfl) ⟨1538486, by rfl⟩ : syracuseStep 2051315 = 3076973) B3076973
theorem B7032095 : Blo 539803 7032095 := bstep (se 1 (by rfl) ⟨5274071, by rfl⟩ : syracuseStep 7032095 = 10548143) B10548143
theorem B53472545 : Blo 539803 53472545 := bstep (se 2 (by rfl) ⟨20052204, by rfl⟩ : syracuseStep 53472545 = 40104409) B40104409
theorem B4943213 : Blo 539803 4943213 := bstep (se 3 (by rfl) ⟨926852, by rfl⟩ : syracuseStep 4943213 = 1853705) B1853705
theorem B11873665 : Blo 539803 11873665 := bstep (se 2 (by rfl) ⟨4452624, by rfl⟩ : syracuseStep 11873665 = 8905249) B8905249
theorem B1822121 : Blo 539803 1822121 := bstep (se 2 (by rfl) ⟨683295, by rfl⟩ : syracuseStep 1822121 = 1366591) B1366591
theorem B912809 : Blo 539803 912809 := bstep (se 2 (by rfl) ⟨342303, by rfl⟩ : syracuseStep 912809 = 684607) B684607
theorem B1027579 : Blo 539803 1027579 := bstep (se 1 (by rfl) ⟨770684, by rfl⟩ : syracuseStep 1027579 = 1541369) B1541369
theorem B3296857 : Blo 539803 3296857 := bstep (se 2 (by rfl) ⟨1236321, by rfl⟩ : syracuseStep 3296857 = 2472643) B2472643
theorem B1232491 : Blo 539803 1232491 := bstep (se 1 (by rfl) ⟨924368, by rfl⟩ : syracuseStep 1232491 = 1848737) B1848737
theorem B1371755 : Blo 539803 1371755 := bstep (se 1 (by rfl) ⟨1028816, by rfl⟩ : syracuseStep 1371755 = 2057633) B2057633
theorem B3698291 : Blo 539803 3698291 := bstep (se 1 (by rfl) ⟨2773718, by rfl⟩ : syracuseStep 3698291 = 5547437) B5547437
theorem B1216295 : Blo 539803 1216295 := bstep (se 1 (by rfl) ⟨912221, by rfl⟩ : syracuseStep 1216295 = 1824443) B1824443
theorem B610087 : Blo 539803 610087 := bstep (se 1 (by rfl) ⟨457565, by rfl⟩ : syracuseStep 610087 = 915131) B915131
theorem B577351 : Blo 539803 577351 := bstep (se 1 (by rfl) ⟨433013, by rfl⟩ : syracuseStep 577351 = 866027) B866027
theorem B1830761 : Blo 539803 1830761 := bstep (se 2 (by rfl) ⟨686535, by rfl⟩ : syracuseStep 1830761 = 1373071) B1373071
theorem B2920313 : Blo 539803 2920313 := bstep (se 2 (by rfl) ⟨1095117, by rfl⟩ : syracuseStep 2920313 = 2190235) B2190235
theorem B2781067 : Blo 539803 2781067 := bstep (se 1 (by rfl) ⟨2085800, by rfl⟩ : syracuseStep 2781067 = 4171601) B4171601
theorem B1822607 : Blo 539803 1822607 := bstep (se 1 (by rfl) ⟨1366955, by rfl⟩ : syracuseStep 1822607 = 2733911) B2733911
theorem B3076015 : Blo 539803 3076015 := bstep (se 1 (by rfl) ⟨2307011, by rfl⟩ : syracuseStep 3076015 = 4614023) B4614023
theorem B1544159 : Blo 539803 1544159 := bstep (se 1 (by rfl) ⟨1158119, by rfl⟩ : syracuseStep 1544159 = 2316239) B2316239
theorem B2060275 : Blo 539803 2060275 := bstep (se 1 (by rfl) ⟨1545206, by rfl⟩ : syracuseStep 2060275 = 3090413) B3090413
theorem B2306177 : Blo 539803 2306177 := bstep (se 2 (by rfl) ⟨864816, by rfl⟩ : syracuseStep 2306177 = 1729633) B1729633
theorem B9392345 : Blo 539803 9392345 := bstep (se 2 (by rfl) ⟨3522129, by rfl⟩ : syracuseStep 9392345 = 7044259) B7044259
theorem B913639 : Blo 539803 913639 := bstep (se 1 (by rfl) ⟨685229, by rfl⟩ : syracuseStep 913639 = 1370459) B1370459
theorem B1822985 : Blo 539803 1822985 := bstep (se 2 (by rfl) ⟨683619, by rfl⟩ : syracuseStep 1822985 = 1367239) B1367239
theorem B823583 : Blo 539803 823583 := bstep (se 1 (by rfl) ⟨617687, by rfl⟩ : syracuseStep 823583 = 1235375) B1235375
theorem B627071 : Blo 539803 627071 := bstep (se 1 (by rfl) ⟨470303, by rfl⟩ : syracuseStep 627071 = 940607) B940607
theorem B913801 : Blo 539803 913801 := bstep (se 2 (by rfl) ⟨342675, by rfl⟩ : syracuseStep 913801 = 685351) B685351
theorem B1544615 : Blo 539803 1544615 := bstep (se 1 (by rfl) ⟨1158461, by rfl⟩ : syracuseStep 1544615 = 2316923) B2316923
theorem B1738255 : Blo 539803 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B1217321 : Blo 539803 1217321 := bstep (se 2 (by rfl) ⟨456495, by rfl⟩ : syracuseStep 1217321 = 912991) B912991
theorem B1733437 : Blo 539803 1733437 := bstep (se 3 (by rfl) ⟨325019, by rfl⟩ : syracuseStep 1733437 = 650039) B650039
theorem B914233 : Blo 539803 914233 := bstep (se 2 (by rfl) ⟨342837, by rfl⟩ : syracuseStep 914233 = 685675) B685675
theorem B914287 : Blo 539803 914287 := bstep (se 1 (by rfl) ⟨685715, by rfl⟩ : syracuseStep 914287 = 1371431) B1371431
theorem B1299329 : Blo 539803 1299329 := bstep (se 2 (by rfl) ⟨487248, by rfl⟩ : syracuseStep 1299329 = 974497) B974497
theorem B4166671 : Blo 539803 4166671 := bstep (se 1 (by rfl) ⟨3125003, by rfl⟩ : syracuseStep 4166671 = 6250007) B6250007
theorem B1217591 : Blo 539803 1217591 := bstep (se 1 (by rfl) ⟨913193, by rfl⟩ : syracuseStep 1217591 = 1826387) B1826387
theorem B1217609 : Blo 539803 1217609 := bstep (se 2 (by rfl) ⟨456603, by rfl⟩ : syracuseStep 1217609 = 913207) B913207
theorem B10663001 : Blo 539803 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B914537 : Blo 539803 914537 := bstep (se 2 (by rfl) ⟨342951, by rfl⟩ : syracuseStep 914537 = 685903) B685903
theorem B1954991 : Blo 539803 1954991 := bstep (se 1 (by rfl) ⟨1466243, by rfl⟩ : syracuseStep 1954991 = 2932487) B2932487
theorem B1373395 : Blo 539803 1373395 := bstep (se 1 (by rfl) ⟨1030046, by rfl⟩ : syracuseStep 1373395 = 2060093) B2060093
theorem B2462939 : Blo 539803 2462939 := bstep (se 1 (by rfl) ⟨1847204, by rfl⟩ : syracuseStep 2462939 = 3694409) B3694409
theorem B1824119 : Blo 539803 1824119 := bstep (se 1 (by rfl) ⟨1368089, by rfl⟩ : syracuseStep 1824119 = 2736179) B2736179
theorem B3700097 : Blo 539803 3700097 := bstep (se 2 (by rfl) ⟨1387536, by rfl⟩ : syracuseStep 3700097 = 2775073) B2775073
theorem B15832493 : Blo 539803 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B8566361 : Blo 539803 8566361 := bstep (se 2 (by rfl) ⟨3212385, by rfl⟩ : syracuseStep 8566361 = 6424771) B6424771
theorem B7141067 : Blo 539803 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B6952715 : Blo 539803 6952715 := bstep (se 1 (by rfl) ⟨5214536, by rfl⟩ : syracuseStep 6952715 = 10429073) B10429073
theorem B579359 : Blo 539803 579359 := bstep (se 1 (by rfl) ⟨434519, by rfl⟩ : syracuseStep 579359 = 869039) B869039
theorem B1169383 : Blo 539803 1169383 := bstep (se 1 (by rfl) ⟨877037, by rfl⟩ : syracuseStep 1169383 = 1754075) B1754075
theorem B2734073 : Blo 539803 2734073 := bstep (se 2 (by rfl) ⟨1025277, by rfl⟩ : syracuseStep 2734073 = 2050555) B2050555
theorem B1235099 : Blo 539803 1235099 := bstep (se 1 (by rfl) ⟨926324, by rfl⟩ : syracuseStep 1235099 = 1852649) B1852649
theorem B1824929 : Blo 539803 1824929 := bstep (se 2 (by rfl) ⟨684348, by rfl⟩ : syracuseStep 1824929 = 1368697) B1368697
theorem B1538281 : Blo 539803 1538281 := bstep (se 2 (by rfl) ⟨576855, by rfl⟩ : syracuseStep 1538281 = 1153711) B1153711
theorem B915691 : Blo 539803 915691 := bstep (se 1 (by rfl) ⟨686768, by rfl⟩ : syracuseStep 915691 = 1373537) B1373537
theorem B6576551 : Blo 539803 6576551 := bstep (se 1 (by rfl) ⟨4932413, by rfl⟩ : syracuseStep 6576551 = 9864827) B9864827
theorem B1849775 : Blo 539803 1849775 := bstep (se 1 (by rfl) ⟨1387331, by rfl⟩ : syracuseStep 1849775 = 2774663) B2774663
theorem B1825199 : Blo 539803 1825199 := bstep (se 1 (by rfl) ⟨1368899, by rfl⟩ : syracuseStep 1825199 = 2737799) B2737799
theorem B102816289 : Blo 539803 102816289 := bstep (se 2 (by rfl) ⟨38556108, by rfl⟩ : syracuseStep 102816289 = 77112217) B77112217
theorem B1538783 : Blo 539803 1538783 := bstep (se 1 (by rfl) ⟨1154087, by rfl⟩ : syracuseStep 1538783 = 2308175) B2308175
theorem B809783 : Blo 539803 809783 := bstep (se 1 (by rfl) ⟨607337, by rfl⟩ : syracuseStep 809783 = 1214675) B1214675
theorem B29547341 : Blo 539803 29547341 := bstep (se 3 (by rfl) ⟨5540126, by rfl⟩ : syracuseStep 29547341 = 11080253) B11080253
theorem B809819 : Blo 539803 809819 := bstep (se 1 (by rfl) ⟨607364, by rfl⟩ : syracuseStep 809819 = 1214729) B1214729
theorem B2743145 : Blo 539803 2743145 := bstep (se 2 (by rfl) ⟨1028679, by rfl⟩ : syracuseStep 2743145 = 2057359) B2057359
theorem B1391519 : Blo 539803 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B2137033 : Blo 539803 2137033 := bstep (se 2 (by rfl) ⟨801387, by rfl⟩ : syracuseStep 2137033 = 1602775) B1602775
theorem B1219535 : Blo 539803 1219535 := bstep (se 1 (by rfl) ⟨914651, by rfl⟩ : syracuseStep 1219535 = 1829303) B1829303
theorem B1219553 : Blo 539803 1219553 := bstep (se 2 (by rfl) ⟨457332, by rfl⟩ : syracuseStep 1219553 = 914665) B914665
theorem B809963 : Blo 539803 809963 := bstep (se 1 (by rfl) ⟨607472, by rfl⟩ : syracuseStep 809963 = 1214945) B1214945
theorem B1219625 : Blo 539803 1219625 := bstep (se 2 (by rfl) ⟨457359, by rfl⟩ : syracuseStep 1219625 = 914719) B914719
theorem B810167 : Blo 539803 810167 := bstep (se 1 (by rfl) ⟨607625, by rfl⟩ : syracuseStep 810167 = 1215251) B1215251
theorem B539871 : Blo 539803 539871 := bstep (se 1 (by rfl) ⟨404903, by rfl⟩ : syracuseStep 539871 = 809807) B809807
theorem B2735369 : Blo 539803 2735369 := bstep (se 2 (by rfl) ⟨1025763, by rfl⟩ : syracuseStep 2735369 = 2051527) B2051527
theorem B810407 : Blo 539803 810407 := bstep (se 1 (by rfl) ⟨607805, by rfl⟩ : syracuseStep 810407 = 1215611) B1215611
theorem B540135 : Blo 539803 540135 := bstep (se 1 (by rfl) ⟨405101, by rfl⟩ : syracuseStep 540135 = 810203) B810203
theorem B3898853 : Blo 539803 3898853 := bstep (se 4 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 3898853 = 731035) B731035
theorem B1826279 : Blo 539803 1826279 := bstep (se 1 (by rfl) ⟨1369709, by rfl⟩ : syracuseStep 1826279 = 2739419) B2739419
theorem B810491 : Blo 539803 810491 := bstep (se 1 (by rfl) ⟨607868, by rfl⟩ : syracuseStep 810491 = 1215737) B1215737
theorem B540251 : Blo 539803 540251 := bstep (se 1 (by rfl) ⟨405188, by rfl⟩ : syracuseStep 540251 = 810377) B810377
theorem B810587 : Blo 539803 810587 := bstep (se 1 (by rfl) ⟨607940, by rfl⟩ : syracuseStep 810587 = 1215881) B1215881
theorem B1564303 : Blo 539803 1564303 := bstep (se 1 (by rfl) ⟨1173227, by rfl⟩ : syracuseStep 1564303 = 2346455) B2346455
theorem B810671 : Blo 539803 810671 := bstep (se 1 (by rfl) ⟨608003, by rfl⟩ : syracuseStep 810671 = 1216007) B1216007
theorem B5865227 : Blo 539803 5865227 := bstep (se 1 (by rfl) ⟨4398920, by rfl⟩ : syracuseStep 5865227 = 8797841) B8797841
theorem B810791 : Blo 539803 810791 := bstep (se 1 (by rfl) ⟨608093, by rfl⟩ : syracuseStep 810791 = 1216187) B1216187
theorem B540487 : Blo 539803 540487 := bstep (se 1 (by rfl) ⟨405365, by rfl⟩ : syracuseStep 540487 = 810731) B810731
theorem B1539911 : Blo 539803 1539911 := bstep (se 1 (by rfl) ⟨1154933, by rfl⟩ : syracuseStep 1539911 = 2309867) B2309867
theorem B12009323 : Blo 539803 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B810875 : Blo 539803 810875 := bstep (se 1 (by rfl) ⟨608156, by rfl⟩ : syracuseStep 810875 = 1216313) B1216313
theorem B769915 : Blo 539803 769915 := bstep (se 1 (by rfl) ⟨577436, by rfl⟩ : syracuseStep 769915 = 1154873) B1154873
theorem B869449 : Blo 539803 869449 := bstep (se 2 (by rfl) ⟨326043, by rfl⟩ : syracuseStep 869449 = 652087) B652087
theorem B540639 : Blo 539803 540639 := bstep (se 1 (by rfl) ⟨405479, by rfl⟩ : syracuseStep 540639 = 810959) B810959
theorem B540863 : Blo 539803 540863 := bstep (se 1 (by rfl) ⟨405647, by rfl⟩ : syracuseStep 540863 = 811295) B811295
theorem B549055 : Blo 539803 549055 := bstep (se 1 (by rfl) ⟨411791, by rfl⟩ : syracuseStep 549055 = 823583) B823583
theorem B540879 : Blo 539803 540879 := bstep (se 1 (by rfl) ⟨405659, by rfl⟩ : syracuseStep 540879 = 811319) B811319
theorem B540927 : Blo 539803 540927 := bstep (se 1 (by rfl) ⟨405695, by rfl⟩ : syracuseStep 540927 = 811391) B811391
theorem B540975 : Blo 539803 540975 := bstep (se 1 (by rfl) ⟨405731, by rfl⟩ : syracuseStep 540975 = 811463) B811463
theorem B1220921 : Blo 539803 1220921 := bstep (se 2 (by rfl) ⟨457845, by rfl⟩ : syracuseStep 1220921 = 915691) B915691
theorem B3293597 : Blo 539803 3293597 := bstep (se 3 (by rfl) ⟨617549, by rfl⟩ : syracuseStep 3293597 = 1235099) B1235099
theorem B11862443 : Blo 539803 11862443 := bstep (se 1 (by rfl) ⟨8896832, by rfl⟩ : syracuseStep 11862443 = 17793665) B17793665
theorem B811547 : Blo 539803 811547 := bstep (se 1 (by rfl) ⟨608660, by rfl⟩ : syracuseStep 811547 = 1217321) B1217321
theorem B541211 : Blo 539803 541211 := bstep (se 1 (by rfl) ⟨405908, by rfl⟩ : syracuseStep 541211 = 811817) B811817
theorem B541215 : Blo 539803 541215 := bstep (se 1 (by rfl) ⟨405911, by rfl⟩ : syracuseStep 541215 = 811823) B811823
theorem B14099021 : Blo 539803 14099021 := bstep (se 3 (by rfl) ⟨2643566, by rfl⟩ : syracuseStep 14099021 = 5287133) B5287133
theorem B541295 : Blo 539803 541295 := bstep (se 1 (by rfl) ⟨405971, by rfl⟩ : syracuseStep 541295 = 811943) B811943
theorem B541351 : Blo 539803 541351 := bstep (se 1 (by rfl) ⟨406013, by rfl⟩ : syracuseStep 541351 = 812027) B812027
theorem B2736827 : Blo 539803 2736827 := bstep (se 1 (by rfl) ⟨2052620, by rfl⟩ : syracuseStep 2736827 = 4105241) B4105241
theorem B4620995 : Blo 539803 4620995 := bstep (se 1 (by rfl) ⟨3465746, by rfl⟩ : syracuseStep 4620995 = 6931493) B6931493
theorem B811727 : Blo 539803 811727 := bstep (se 1 (by rfl) ⟨608795, by rfl⟩ : syracuseStep 811727 = 1217591) B1217591
theorem B541391 : Blo 539803 541391 := bstep (se 1 (by rfl) ⟨406043, by rfl⟩ : syracuseStep 541391 = 812087) B812087
theorem B811739 : Blo 539803 811739 := bstep (se 1 (by rfl) ⟨608804, by rfl⟩ : syracuseStep 811739 = 1217609) B1217609
theorem B541471 : Blo 539803 541471 := bstep (se 1 (by rfl) ⟨406103, by rfl⟩ : syracuseStep 541471 = 812207) B812207
theorem B1303327 : Blo 539803 1303327 := bstep (se 1 (by rfl) ⟨977495, by rfl⟩ : syracuseStep 1303327 = 1954991) B1954991
theorem B2474819 : Blo 539803 2474819 := bstep (se 1 (by rfl) ⟨1856114, by rfl⟩ : syracuseStep 2474819 = 3712229) B3712229
theorem B2466731 : Blo 539803 2466731 := bstep (se 1 (by rfl) ⟨1850048, by rfl⟩ : syracuseStep 2466731 = 3700097) B3700097
theorem B607279 : Blo 539803 607279 := bstep (se 1 (by rfl) ⟨455459, by rfl⟩ : syracuseStep 607279 = 910919) B910919
theorem B541743 : Blo 539803 541743 := bstep (se 1 (by rfl) ⟨406307, by rfl⟩ : syracuseStep 541743 = 812615) B812615
theorem B5710907 : Blo 539803 5710907 := bstep (se 1 (by rfl) ⟨4283180, by rfl⟩ : syracuseStep 5710907 = 8566361) B8566361
theorem B3466313 : Blo 539803 3466313 := bstep (se 2 (by rfl) ⟨1299867, by rfl⟩ : syracuseStep 3466313 = 2599735) B2599735
theorem B2311249 : Blo 539803 2311249 := bstep (se 2 (by rfl) ⟨866718, by rfl⟩ : syracuseStep 2311249 = 1733437) B1733437
theorem B541807 : Blo 539803 541807 := bstep (se 1 (by rfl) ⟨406355, by rfl⟩ : syracuseStep 541807 = 812711) B812711
theorem B812153 : Blo 539803 812153 := bstep (se 2 (by rfl) ⟨304557, by rfl⟩ : syracuseStep 812153 = 609115) B609115
theorem B4932733 : Blo 539803 4932733 := bstep (se 3 (by rfl) ⟨924887, by rfl⟩ : syracuseStep 4932733 = 1849775) B1849775
theorem B4760711 : Blo 539803 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B541863 : Blo 539803 541863 := bstep (se 1 (by rfl) ⟨406397, by rfl⟩ : syracuseStep 541863 = 812795) B812795
theorem B607423 : Blo 539803 607423 := bstep (se 1 (by rfl) ⟨455567, by rfl⟩ : syracuseStep 607423 = 911135) B911135
theorem B541887 : Blo 539803 541887 := bstep (se 1 (by rfl) ⟨406415, by rfl⟩ : syracuseStep 541887 = 812831) B812831
theorem B541919 : Blo 539803 541919 := bstep (se 1 (by rfl) ⟨406439, by rfl⟩ : syracuseStep 541919 = 812879) B812879
theorem B541999 : Blo 539803 541999 := bstep (se 1 (by rfl) ⟨406499, by rfl⟩ : syracuseStep 541999 = 812999) B812999
theorem B1729849 : Blo 539803 1729849 := bstep (se 2 (by rfl) ⟨648693, by rfl⟩ : syracuseStep 1729849 = 1297387) B1297387
theorem B1205561 : Blo 539803 1205561 := bstep (se 2 (by rfl) ⟨452085, by rfl⟩ : syracuseStep 1205561 = 904171) B904171
theorem B607567 : Blo 539803 607567 := bstep (se 1 (by rfl) ⟨455675, by rfl⟩ : syracuseStep 607567 = 911351) B911351
theorem B5555561 : Blo 539803 5555561 := bstep (se 2 (by rfl) ⟨2083335, by rfl⟩ : syracuseStep 5555561 = 4166671) B4166671
theorem B542235 : Blo 539803 542235 := bstep (se 1 (by rfl) ⟨406676, by rfl⟩ : syracuseStep 542235 = 813353) B813353
theorem B542239 : Blo 539803 542239 := bstep (se 1 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 542239 = 813359) B813359
theorem B4384367 : Blo 539803 4384367 := bstep (se 1 (by rfl) ⟨3288275, by rfl⟩ : syracuseStep 4384367 = 6576551) B6576551
theorem B1558187 : Blo 539803 1558187 := bstep (se 1 (by rfl) ⟨1168640, by rfl⟩ : syracuseStep 1558187 = 2337281) B2337281
theorem B542399 : Blo 539803 542399 := bstep (se 1 (by rfl) ⟨406799, by rfl⟩ : syracuseStep 542399 = 813599) B813599
theorem B5203693 : Blo 539803 5203693 := bstep (se 3 (by rfl) ⟨975692, by rfl⟩ : syracuseStep 5203693 = 1951385) B1951385
theorem B1025855 : Blo 539803 1025855 := bstep (se 1 (by rfl) ⟨769391, by rfl⟩ : syracuseStep 1025855 = 1538783) B1538783
theorem B37455695 : Blo 539803 37455695 := bstep (se 1 (by rfl) ⟨28091771, by rfl⟩ : syracuseStep 37455695 = 56183543) B56183543
theorem B1828763 : Blo 539803 1828763 := bstep (se 1 (by rfl) ⟨1371572, by rfl⟩ : syracuseStep 1828763 = 2743145) B2743145
theorem B927679 : Blo 539803 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B542655 : Blo 539803 542655 := bstep (se 1 (by rfl) ⟨406991, by rfl⟩ : syracuseStep 542655 = 813983) B813983
theorem B813023 : Blo 539803 813023 := bstep (se 1 (by rfl) ⟨609767, by rfl⟩ : syracuseStep 813023 = 1219535) B1219535
theorem B542687 : Blo 539803 542687 := bstep (se 1 (by rfl) ⟨407015, by rfl⟩ : syracuseStep 542687 = 814031) B814031
theorem B4106213 : Blo 539803 4106213 := bstep (se 4 (by rfl) ⟨384957, by rfl⟩ : syracuseStep 4106213 = 769915) B769915
theorem B813035 : Blo 539803 813035 := bstep (se 1 (by rfl) ⟨609776, by rfl⟩ : syracuseStep 813035 = 1219553) B1219553
theorem B1370105 : Blo 539803 1370105 := bstep (se 2 (by rfl) ⟨513789, by rfl⟩ : syracuseStep 1370105 = 1027579) B1027579
theorem B813083 : Blo 539803 813083 := bstep (se 1 (by rfl) ⟨609812, by rfl⟩ : syracuseStep 813083 = 1219625) B1219625
theorem B542747 : Blo 539803 542747 := bstep (se 1 (by rfl) ⟨407060, by rfl⟩ : syracuseStep 542747 = 814121) B814121
theorem B608287 : Blo 539803 608287 := bstep (se 1 (by rfl) ⟨456215, by rfl⟩ : syracuseStep 608287 = 912431) B912431
theorem B542751 : Blo 539803 542751 := bstep (se 1 (by rfl) ⟨407063, by rfl⟩ : syracuseStep 542751 = 814127) B814127
theorem B4114475 : Blo 539803 4114475 := bstep (se 1 (by rfl) ⟨3085856, by rfl⟩ : syracuseStep 4114475 = 6171713) B6171713
theorem B542767 : Blo 539803 542767 := bstep (se 1 (by rfl) ⟨407075, by rfl⟩ : syracuseStep 542767 = 814151) B814151
theorem B4688063 : Blo 539803 4688063 := bstep (se 1 (by rfl) ⟨3516047, by rfl⟩ : syracuseStep 4688063 = 7032095) B7032095
theorem B3295475 : Blo 539803 3295475 := bstep (se 1 (by rfl) ⟨2471606, by rfl⟩ : syracuseStep 3295475 = 4943213) B4943213
theorem B1214747 : Blo 539803 1214747 := bstep (se 1 (by rfl) ⟨911060, by rfl⟩ : syracuseStep 1214747 = 1822121) B1822121
theorem B608539 : Blo 539803 608539 := bstep (se 1 (by rfl) ⟨456404, by rfl⟩ : syracuseStep 608539 = 912809) B912809
theorem B2599235 : Blo 539803 2599235 := bstep (se 1 (by rfl) ⟨1949426, by rfl⟩ : syracuseStep 2599235 = 3898853) B3898853
theorem B2058605 : Blo 539803 2058605 := bstep (se 3 (by rfl) ⟨385988, by rfl⟩ : syracuseStep 2058605 = 771977) B771977
theorem B813449 : Blo 539803 813449 := bstep (se 2 (by rfl) ⟨305043, by rfl⟩ : syracuseStep 813449 = 610087) B610087
theorem B3910151 : Blo 539803 3910151 := bstep (se 1 (by rfl) ⟨2932613, by rfl⟩ : syracuseStep 3910151 = 5865227) B5865227
theorem B1026607 : Blo 539803 1026607 := bstep (se 1 (by rfl) ⟨769955, by rfl⟩ : syracuseStep 1026607 = 1539911) B1539911
theorem B8006215 : Blo 539803 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B1215071 : Blo 539803 1215071 := bstep (se 1 (by rfl) ⟨911303, by rfl⟩ : syracuseStep 1215071 = 1822607) B1822607
theorem B1559177 : Blo 539803 1559177 := bstep (se 2 (by rfl) ⟨584691, by rfl⟩ : syracuseStep 1559177 = 1169383) B1169383
theorem B2747033 : Blo 539803 2747033 := bstep (se 2 (by rfl) ⟨1030137, by rfl⟩ : syracuseStep 2747033 = 2060275) B2060275
theorem B6261563 : Blo 539803 6261563 := bstep (se 1 (by rfl) ⟨4696172, by rfl⟩ : syracuseStep 6261563 = 9392345) B9392345
theorem B1215323 : Blo 539803 1215323 := bstep (se 1 (by rfl) ⟨911492, by rfl⟩ : syracuseStep 1215323 = 1822985) B1822985
theorem B4631519 : Blo 539803 4631519 := bstep (se 1 (by rfl) ⟨3473639, by rfl⟩ : syracuseStep 4631519 = 6947279) B6947279
theorem B2051041 : Blo 539803 2051041 := bstep (se 2 (by rfl) ⟨769140, by rfl⟩ : syracuseStep 2051041 = 1538281) B1538281
theorem B137088385 : Blo 539803 137088385 := bstep (se 2 (by rfl) ⟨51408144, by rfl⟩ : syracuseStep 137088385 = 102816289) B102816289
theorem B601499 : Blo 539803 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B609691 : Blo 539803 609691 := bstep (se 1 (by rfl) ⟨457268, by rfl⟩ : syracuseStep 609691 = 914537) B914537
theorem B1027495 : Blo 539803 1027495 := bstep (se 1 (by rfl) ⟨770621, by rfl⟩ : syracuseStep 1027495 = 1541243) B1541243
theorem B2747843 : Blo 539803 2747843 := bstep (se 1 (by rfl) ⟨2060882, by rfl⟩ : syracuseStep 2747843 = 4121765) B4121765
theorem B912863 : Blo 539803 912863 := bstep (se 1 (by rfl) ⟨684647, by rfl⟩ : syracuseStep 912863 = 1369295) B1369295
theorem B1641959 : Blo 539803 1641959 := bstep (se 1 (by rfl) ⟨1231469, by rfl⟩ : syracuseStep 1641959 = 2462939) B2462939
theorem B1216079 : Blo 539803 1216079 := bstep (se 1 (by rfl) ⟨912059, by rfl⟩ : syracuseStep 1216079 = 1824119) B1824119
theorem B1830491 : Blo 539803 1830491 := bstep (se 1 (by rfl) ⟨1372868, by rfl⟩ : syracuseStep 1830491 = 2745737) B2745737
theorem B10554995 : Blo 539803 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B913079 : Blo 539803 913079 := bstep (se 1 (by rfl) ⟨684809, by rfl⟩ : syracuseStep 913079 = 1369619) B1369619
theorem B31289125 : Blo 539803 31289125 := bstep (se 4 (by rfl) ⟨2933355, by rfl⟩ : syracuseStep 31289125 = 5866711) B5866711
theorem B4108157 : Blo 539803 4108157 := bstep (se 3 (by rfl) ⟨770279, by rfl⟩ : syracuseStep 4108157 = 1540559) B1540559
theorem B6688757 : Blo 539803 6688757 := bstep (se 5 (by rfl) ⟨313535, by rfl⟩ : syracuseStep 6688757 = 627071) B627071
theorem B1822715 : Blo 539803 1822715 := bstep (se 1 (by rfl) ⟨1367036, by rfl⟩ : syracuseStep 1822715 = 2734073) B2734073
theorem B1159265 : Blo 539803 1159265 := bstep (se 2 (by rfl) ⟨434724, by rfl⟩ : syracuseStep 1159265 = 869449) B869449
theorem B1216619 : Blo 539803 1216619 := bstep (se 1 (by rfl) ⟨912464, by rfl⟩ : syracuseStep 1216619 = 1824929) B1824929
theorem B1216673 : Blo 539803 1216673 := bstep (se 2 (by rfl) ⟨456252, by rfl⟩ : syracuseStep 1216673 = 912505) B912505
theorem B1372423 : Blo 539803 1372423 := bstep (se 1 (by rfl) ⟨1029317, by rfl⟩ : syracuseStep 1372423 = 2058635) B2058635
theorem B1831193 : Blo 539803 1831193 := bstep (se 2 (by rfl) ⟨686697, by rfl⟩ : syracuseStep 1831193 = 1373395) B1373395
theorem B1216799 : Blo 539803 1216799 := bstep (se 1 (by rfl) ⟨912599, by rfl⟩ : syracuseStep 1216799 = 1825199) B1825199
theorem B15790403 : Blo 539803 15790403 := bstep (se 1 (by rfl) ⟨11842802, by rfl⟩ : syracuseStep 15790403 = 23685605) B23685605
theorem B1028551 : Blo 539803 1028551 := bstep (se 1 (by rfl) ⟨771413, by rfl⟩ : syracuseStep 1028551 = 1542827) B1542827
theorem B15831553 : Blo 539803 15831553 := bstep (se 2 (by rfl) ⟨5936832, by rfl⟩ : syracuseStep 15831553 = 11873665) B11873665
theorem B19698227 : Blo 539803 19698227 := bstep (se 1 (by rfl) ⟨14773670, by rfl⟩ : syracuseStep 19698227 = 29547341) B29547341
theorem B1544957 : Blo 539803 1544957 := bstep (se 3 (by rfl) ⟨289679, by rfl⟩ : syracuseStep 1544957 = 579359) B579359
theorem B4395809 : Blo 539803 4395809 := bstep (se 2 (by rfl) ⟨1648428, by rfl⟩ : syracuseStep 4395809 = 3296857) B3296857
theorem B1643321 : Blo 539803 1643321 := bstep (se 2 (by rfl) ⟨616245, by rfl⟩ : syracuseStep 1643321 = 1232491) B1232491
theorem B1823579 : Blo 539803 1823579 := bstep (se 1 (by rfl) ⟨1367684, by rfl⟩ : syracuseStep 1823579 = 2735369) B2735369
theorem B35648363 : Blo 539803 35648363 := bstep (se 1 (by rfl) ⟨26736272, by rfl⟩ : syracuseStep 35648363 = 53472545) B53472545
theorem B1217519 : Blo 539803 1217519 := bstep (se 1 (by rfl) ⟨913139, by rfl⟩ : syracuseStep 1217519 = 1826279) B1826279
theorem B914503 : Blo 539803 914503 := bstep (se 1 (by rfl) ⟨685877, by rfl⟩ : syracuseStep 914503 = 1371755) B1371755
theorem B3708089 : Blo 539803 3708089 := bstep (se 2 (by rfl) ⟨1390533, by rfl⟩ : syracuseStep 3708089 = 2781067) B2781067
theorem B4101353 : Blo 539803 4101353 := bstep (se 2 (by rfl) ⟨1538007, by rfl⟩ : syracuseStep 4101353 = 3076015) B3076015
theorem B1946875 : Blo 539803 1946875 := bstep (se 1 (by rfl) ⟨1460156, by rfl⟩ : syracuseStep 1946875 = 2920313) B2920313
theorem B1029439 : Blo 539803 1029439 := bstep (se 1 (by rfl) ⟨772079, by rfl⟩ : syracuseStep 1029439 = 1544159) B1544159
theorem B2594159 : Blo 539803 2594159 := bstep (se 1 (by rfl) ⟨1945619, by rfl⟩ : syracuseStep 2594159 = 3891239) B3891239
theorem B1537451 : Blo 539803 1537451 := bstep (se 1 (by rfl) ⟨1153088, by rfl⟩ : syracuseStep 1537451 = 2306177) B2306177
theorem B4396463 : Blo 539803 4396463 := bstep (se 1 (by rfl) ⟨3297347, by rfl⟩ : syracuseStep 4396463 = 6594695) B6594695
theorem B1218023 : Blo 539803 1218023 := bstep (se 1 (by rfl) ⟨913517, by rfl⟩ : syracuseStep 1218023 = 1827035) B1827035
theorem B1463791 : Blo 539803 1463791 := bstep (se 1 (by rfl) ⟨1097843, by rfl⟩ : syracuseStep 1463791 = 2195687) B2195687
theorem B1029743 : Blo 539803 1029743 := bstep (se 1 (by rfl) ⟨772307, by rfl⟩ : syracuseStep 1029743 = 1544615) B1544615
theorem B2315897 : Blo 539803 2315897 := bstep (se 2 (by rfl) ⟨868461, by rfl⟩ : syracuseStep 2315897 = 1736923) B1736923
theorem B1218185 : Blo 539803 1218185 := bstep (se 2 (by rfl) ⟨456819, by rfl⟩ : syracuseStep 1218185 = 913639) B913639
theorem B1218203 : Blo 539803 1218203 := bstep (se 1 (by rfl) ⟨913652, by rfl⟩ : syracuseStep 1218203 = 1827305) B1827305
theorem B2742011 : Blo 539803 2742011 := bstep (se 1 (by rfl) ⟨2056508, by rfl⟩ : syracuseStep 2742011 = 4113017) B4113017
theorem B1218401 : Blo 539803 1218401 := bstep (se 2 (by rfl) ⟨456900, by rfl⟩ : syracuseStep 1218401 = 913801) B913801
theorem B866219 : Blo 539803 866219 := bstep (se 1 (by rfl) ⟨649664, by rfl⟩ : syracuseStep 866219 = 1299329) B1299329
theorem B2308105 : Blo 539803 2308105 := bstep (se 2 (by rfl) ⟨865539, by rfl⟩ : syracuseStep 2308105 = 1731079) B1731079
theorem B1218599 : Blo 539803 1218599 := bstep (se 1 (by rfl) ⟨913949, by rfl⟩ : syracuseStep 1218599 = 1827899) B1827899
theorem B7108667 : Blo 539803 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B1218779 : Blo 539803 1218779 := bstep (se 1 (by rfl) ⟨914084, by rfl⟩ : syracuseStep 1218779 = 1828169) B1828169
theorem B1218977 : Blo 539803 1218977 := bstep (se 2 (by rfl) ⟨457116, by rfl⟩ : syracuseStep 1218977 = 914233) B914233
theorem B1219049 : Blo 539803 1219049 := bstep (se 2 (by rfl) ⟨457143, by rfl⟩ : syracuseStep 1219049 = 914287) B914287
theorem B4635143 : Blo 539803 4635143 := bstep (se 1 (by rfl) ⟨3476357, by rfl⟩ : syracuseStep 4635143 = 6952715) B6952715
theorem B1825307 : Blo 539803 1825307 := bstep (se 1 (by rfl) ⟨1368980, by rfl⟩ : syracuseStep 1825307 = 2737961) B2737961
theorem B133487189 : Blo 539803 133487189 := bstep (se 8 (by rfl) ⟨782151, by rfl⟩ : syracuseStep 133487189 = 1564303) B1564303
theorem B2849377 : Blo 539803 2849377 := bstep (se 2 (by rfl) ⟨1068516, by rfl⟩ : syracuseStep 2849377 = 2137033) B2137033
theorem B5847673 : Blo 539803 5847673 := bstep (se 2 (by rfl) ⟨2192877, by rfl⟩ : syracuseStep 5847673 = 4385755) B4385755
theorem B1366895 : Blo 539803 1366895 := bstep (se 1 (by rfl) ⟨1025171, by rfl⟩ : syracuseStep 1366895 = 2050343) B2050343
theorem B3119995 : Blo 539803 3119995 := bstep (se 1 (by rfl) ⟨2339996, by rfl⟩ : syracuseStep 3119995 = 4679993) B4679993
theorem B9264131 : Blo 539803 9264131 := bstep (se 1 (by rfl) ⟨6948098, by rfl⟩ : syracuseStep 9264131 = 13896197) B13896197
theorem B3079205 : Blo 539803 3079205 := bstep (se 4 (by rfl) ⟨288675, by rfl⟩ : syracuseStep 3079205 = 577351) B577351
theorem B5201081 : Blo 539803 5201081 := bstep (se 2 (by rfl) ⟨1950405, by rfl⟩ : syracuseStep 5201081 = 3900811) B3900811
theorem B539855 : Blo 539803 539855 := bstep (se 1 (by rfl) ⟨404891, by rfl⟩ : syracuseStep 539855 = 809783) B809783
theorem B810191 : Blo 539803 810191 := bstep (se 1 (by rfl) ⟨607643, by rfl⟩ : syracuseStep 810191 = 1215287) B1215287
theorem B539879 : Blo 539803 539879 := bstep (se 1 (by rfl) ⟨404909, by rfl⟩ : syracuseStep 539879 = 809819) B809819
theorem B2055401 : Blo 539803 2055401 := bstep (se 2 (by rfl) ⟨770775, by rfl⟩ : syracuseStep 2055401 = 1541551) B1541551
theorem B7413059 : Blo 539803 7413059 := bstep (se 1 (by rfl) ⟨5559794, by rfl⟩ : syracuseStep 7413059 = 11119589) B11119589
theorem B539975 : Blo 539803 539975 := bstep (se 1 (by rfl) ⟨404981, by rfl⟩ : syracuseStep 539975 = 809963) B809963
theorem B810311 : Blo 539803 810311 := bstep (se 1 (by rfl) ⟨607733, by rfl⟩ : syracuseStep 810311 = 1215467) B1215467
theorem B2317673 : Blo 539803 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B17603983 : Blo 539803 17603983 := bstep (se 1 (by rfl) ⟨13202987, by rfl⟩ : syracuseStep 17603983 = 26405975) B26405975
theorem B540111 : Blo 539803 540111 := bstep (se 1 (by rfl) ⟨405083, by rfl⟩ : syracuseStep 540111 = 810167) B810167
theorem B810473 : Blo 539803 810473 := bstep (se 2 (by rfl) ⟨303927, by rfl⟩ : syracuseStep 810473 = 607855) B607855
theorem B1367543 : Blo 539803 1367543 := bstep (se 1 (by rfl) ⟨1025657, by rfl⟩ : syracuseStep 1367543 = 2051315) B2051315
theorem B540271 : Blo 539803 540271 := bstep (se 1 (by rfl) ⟨405203, by rfl⟩ : syracuseStep 540271 = 810407) B810407
theorem B810617 : Blo 539803 810617 := bstep (se 2 (by rfl) ⟨303981, by rfl⟩ : syracuseStep 810617 = 607963) B607963
theorem B540327 : Blo 539803 540327 := bstep (se 1 (by rfl) ⟨405245, by rfl⟩ : syracuseStep 540327 = 810491) B810491
theorem B4112045 : Blo 539803 4112045 := bstep (se 3 (by rfl) ⟨771008, by rfl⟩ : syracuseStep 4112045 = 1542017) B1542017
theorem B540391 : Blo 539803 540391 := bstep (se 1 (by rfl) ⟨405293, by rfl⟩ : syracuseStep 540391 = 810587) B810587
theorem B2465527 : Blo 539803 2465527 := bstep (se 1 (by rfl) ⟨1849145, by rfl⟩ : syracuseStep 2465527 = 3698291) B3698291
theorem B540447 : Blo 539803 540447 := bstep (se 1 (by rfl) ⟨405335, by rfl⟩ : syracuseStep 540447 = 810671) B810671
theorem B540527 : Blo 539803 540527 := bstep (se 1 (by rfl) ⟨405395, by rfl⟩ : syracuseStep 540527 = 810791) B810791
theorem B810863 : Blo 539803 810863 := bstep (se 1 (by rfl) ⟨608147, by rfl⟩ : syracuseStep 810863 = 1216295) B1216295
theorem B1220507 : Blo 539803 1220507 := bstep (se 1 (by rfl) ⟨915380, by rfl⟩ : syracuseStep 1220507 = 1830761) B1830761
theorem B540583 : Blo 539803 540583 := bstep (se 1 (by rfl) ⟨405437, by rfl⟩ : syracuseStep 540583 = 810875) B810875
theorem B2924552213 : Blo 539803 2924552213 := bstep (se 6 (by rfl) ⟨68544192, by rfl⟩ : syracuseStep 2924552213 = 137088385) B137088385
theorem B811049 : Blo 539803 811049 := bstep (se 2 (by rfl) ⟨304143, by rfl⟩ : syracuseStep 811049 = 608287) B608287
theorem B811079 : Blo 539803 811079 := bstep (se 1 (by rfl) ⟨608309, by rfl⟩ : syracuseStep 811079 = 1216619) B1216619
theorem B811115 : Blo 539803 811115 := bstep (se 1 (by rfl) ⟨608336, by rfl⟩ : syracuseStep 811115 = 1216673) B1216673
theorem B1220795 : Blo 539803 1220795 := bstep (se 1 (by rfl) ⟨915596, by rfl⟩ : syracuseStep 1220795 = 1831193) B1831193
theorem B811199 : Blo 539803 811199 := bstep (se 1 (by rfl) ⟨608399, by rfl⟩ : syracuseStep 811199 = 1216799) B1216799
theorem B10526935 : Blo 539803 10526935 := bstep (se 1 (by rfl) ⟨7895201, by rfl⟩ : syracuseStep 10526935 = 15790403) B15790403
theorem B2195731 : Blo 539803 2195731 := bstep (se 1 (by rfl) ⟨1646798, by rfl⟩ : syracuseStep 2195731 = 3293597) B3293597
theorem B541031 : Blo 539803 541031 := bstep (se 1 (by rfl) ⟨405773, by rfl⟩ : syracuseStep 541031 = 811547) B811547
theorem B13132151 : Blo 539803 13132151 := bstep (se 1 (by rfl) ⟨9849113, by rfl⟩ : syracuseStep 13132151 = 19698227) B19698227
theorem B811385 : Blo 539803 811385 := bstep (se 2 (by rfl) ⟨304269, by rfl⟩ : syracuseStep 811385 = 608539) B608539
theorem B3080663 : Blo 539803 3080663 := bstep (se 1 (by rfl) ⟨2310497, by rfl⟩ : syracuseStep 3080663 = 4620995) B4620995
theorem B541151 : Blo 539803 541151 := bstep (se 1 (by rfl) ⟨405863, by rfl⟩ : syracuseStep 541151 = 811727) B811727
theorem B541159 : Blo 539803 541159 := bstep (se 1 (by rfl) ⟨405869, by rfl⟩ : syracuseStep 541159 = 811739) B811739
theorem B23765575 : Blo 539803 23765575 := bstep (se 1 (by rfl) ⟨17824181, by rfl⟩ : syracuseStep 23765575 = 35648363) B35648363
theorem B811679 : Blo 539803 811679 := bstep (se 1 (by rfl) ⟨608759, by rfl⟩ : syracuseStep 811679 = 1217519) B1217519
theorem B2310875 : Blo 539803 2310875 := bstep (se 1 (by rfl) ⟨1733156, by rfl⟩ : syracuseStep 2310875 = 3466313) B3466313
theorem B1368809 : Blo 539803 1368809 := bstep (se 2 (by rfl) ⟨513303, by rfl⟩ : syracuseStep 1368809 = 1026607) B1026607
theorem B541435 : Blo 539803 541435 := bstep (se 1 (by rfl) ⟨406076, by rfl⟩ : syracuseStep 541435 = 812153) B812153
theorem B10674953 : Blo 539803 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B19768157 : Blo 539803 19768157 := bstep (se 3 (by rfl) ⟨3706529, by rfl⟩ : syracuseStep 19768157 = 7413059) B7413059
theorem B1729439 : Blo 539803 1729439 := bstep (se 1 (by rfl) ⟨1297079, by rfl⟩ : syracuseStep 1729439 = 2594159) B2594159
theorem B1024967 : Blo 539803 1024967 := bstep (se 1 (by rfl) ⟨768725, by rfl⟩ : syracuseStep 1024967 = 1537451) B1537451
theorem B812015 : Blo 539803 812015 := bstep (se 1 (by rfl) ⟨609011, by rfl⟩ : syracuseStep 812015 = 1218023) B1218023
theorem B1737769 : Blo 539803 1737769 := bstep (se 2 (by rfl) ⟨651663, by rfl⟩ : syracuseStep 1737769 = 1303327) B1303327
theorem B812123 : Blo 539803 812123 := bstep (se 1 (by rfl) ⟨609092, by rfl⟩ : syracuseStep 812123 = 1218185) B1218185
theorem B812135 : Blo 539803 812135 := bstep (se 1 (by rfl) ⟨609101, by rfl⟩ : syracuseStep 812135 = 1218203) B1218203
theorem B1828007 : Blo 539803 1828007 := bstep (se 1 (by rfl) ⟨1371005, by rfl⟩ : syracuseStep 1828007 = 2742011) B2742011
theorem B24970463 : Blo 539803 24970463 := bstep (se 1 (by rfl) ⟨18727847, by rfl⟩ : syracuseStep 24970463 = 37455695) B37455695
theorem B812267 : Blo 539803 812267 := bstep (se 1 (by rfl) ⟨609200, by rfl⟩ : syracuseStep 812267 = 1218401) B1218401
theorem B542015 : Blo 539803 542015 := bstep (se 1 (by rfl) ⟨406511, by rfl⟩ : syracuseStep 542015 = 813023) B813023
theorem B2737475 : Blo 539803 2737475 := bstep (se 1 (by rfl) ⟨2053106, by rfl⟩ : syracuseStep 2737475 = 4106213) B4106213
theorem B542023 : Blo 539803 542023 := bstep (se 1 (by rfl) ⟨406517, by rfl⟩ : syracuseStep 542023 = 813035) B813035
theorem B542055 : Blo 539803 542055 := bstep (se 1 (by rfl) ⟨406541, by rfl⟩ : syracuseStep 542055 = 813083) B813083
theorem B812399 : Blo 539803 812399 := bstep (se 1 (by rfl) ⟨609299, by rfl⟩ : syracuseStep 812399 = 1218599) B1218599
theorem B3081665 : Blo 539803 3081665 := bstep (se 2 (by rfl) ⟨1155624, by rfl⟩ : syracuseStep 3081665 = 2311249) B2311249
theorem B812519 : Blo 539803 812519 := bstep (se 1 (by rfl) ⟨609389, by rfl⟩ : syracuseStep 812519 = 1218779) B1218779
theorem B2196983 : Blo 539803 2196983 := bstep (se 1 (by rfl) ⟨1647737, by rfl⟩ : syracuseStep 2196983 = 3295475) B3295475
theorem B542299 : Blo 539803 542299 := bstep (se 1 (by rfl) ⟨406724, by rfl⟩ : syracuseStep 542299 = 813449) B813449
theorem B812651 : Blo 539803 812651 := bstep (se 1 (by rfl) ⟨609488, by rfl⟩ : syracuseStep 812651 = 1218977) B1218977
theorem B812699 : Blo 539803 812699 := bstep (se 1 (by rfl) ⟨609524, by rfl⟩ : syracuseStep 812699 = 1219049) B1219049
theorem B3090095 : Blo 539803 3090095 := bstep (se 1 (by rfl) ⟨2317571, by rfl⟩ : syracuseStep 3090095 = 4635143) B4635143
theorem B88991459 : Blo 539803 88991459 := bstep (se 1 (by rfl) ⟨66743594, by rfl⟩ : syracuseStep 88991459 = 133487189) B133487189
theorem B23471977 : Blo 539803 23471977 := bstep (se 2 (by rfl) ⟨8801991, by rfl⟩ : syracuseStep 23471977 = 17603983) B17603983
theorem B812921 : Blo 539803 812921 := bstep (se 2 (by rfl) ⟨304845, by rfl⟩ : syracuseStep 812921 = 609691) B609691
theorem B1369993 : Blo 539803 1369993 := bstep (se 2 (by rfl) ⟨513747, by rfl⟩ : syracuseStep 1369993 = 1027495) B1027495
theorem B911263 : Blo 539803 911263 := bstep (se 1 (by rfl) ⟨683447, by rfl⟩ : syracuseStep 911263 = 1366895) B1366895
theorem B1951721 : Blo 539803 1951721 := bstep (se 2 (by rfl) ⟨731895, by rfl⟩ : syracuseStep 1951721 = 1463791) B1463791
theorem B3467387 : Blo 539803 3467387 := bstep (se 1 (by rfl) ⟨2600540, by rfl⟩ : syracuseStep 3467387 = 5201081) B5201081
theorem B1370267 : Blo 539803 1370267 := bstep (se 1 (by rfl) ⟨1027700, by rfl⟩ : syracuseStep 1370267 = 2055401) B2055401
theorem B608575 : Blo 539803 608575 := bstep (se 1 (by rfl) ⟨456431, by rfl⟩ : syracuseStep 608575 = 912863) B912863
theorem B3287369 : Blo 539803 3287369 := bstep (se 2 (by rfl) ⟨1232763, by rfl⟩ : syracuseStep 3287369 = 2465527) B2465527
theorem B911695 : Blo 539803 911695 := bstep (se 1 (by rfl) ⟨683771, by rfl⟩ : syracuseStep 911695 = 1367543) B1367543
theorem B608719 : Blo 539803 608719 := bstep (se 1 (by rfl) ⟨456539, by rfl⟩ : syracuseStep 608719 = 913079) B913079
theorem B2738771 : Blo 539803 2738771 := bstep (se 1 (by rfl) ⟨2054078, by rfl⟩ : syracuseStep 2738771 = 4108157) B4108157
theorem B813671 : Blo 539803 813671 := bstep (se 1 (by rfl) ⟨610253, by rfl⟩ : syracuseStep 813671 = 1220507) B1220507
theorem B17836685 : Blo 539803 17836685 := bstep (se 3 (by rfl) ⟨3344378, by rfl⟩ : syracuseStep 17836685 = 6688757) B6688757
theorem B1215143 : Blo 539803 1215143 := bstep (se 1 (by rfl) ⟨911357, by rfl⟩ : syracuseStep 1215143 = 1822715) B1822715
theorem B772843 : Blo 539803 772843 := bstep (se 1 (by rfl) ⟨579632, by rfl⟩ : syracuseStep 772843 = 1159265) B1159265
theorem B813947 : Blo 539803 813947 := bstep (se 1 (by rfl) ⟨610460, by rfl⟩ : syracuseStep 813947 = 1220921) B1220921
theorem B732073 : Blo 539803 732073 := bstep (se 2 (by rfl) ⟨274527, by rfl⟩ : syracuseStep 732073 = 549055) B549055
theorem B7908295 : Blo 539803 7908295 := bstep (se 1 (by rfl) ⟨5931221, by rfl⟩ : syracuseStep 7908295 = 11862443) B11862443
theorem B1829897 : Blo 539803 1829897 := bstep (se 2 (by rfl) ⟨686211, by rfl⟩ : syracuseStep 1829897 = 1372423) B1372423
theorem B9399347 : Blo 539803 9399347 := bstep (se 1 (by rfl) ⟨7049510, by rfl⟩ : syracuseStep 9399347 = 14099021) B14099021
theorem B1649879 : Blo 539803 1649879 := bstep (se 1 (by rfl) ⟨1237409, by rfl⟩ : syracuseStep 1649879 = 2474819) B2474819
theorem B1215719 : Blo 539803 1215719 := bstep (se 1 (by rfl) ⟨911789, by rfl⟩ : syracuseStep 1215719 = 1823579) B1823579
theorem B1371401 : Blo 539803 1371401 := bstep (se 2 (by rfl) ⟨514275, by rfl⟩ : syracuseStep 1371401 = 1028551) B1028551
theorem B3173807 : Blo 539803 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B3214829 : Blo 539803 3214829 := bstep (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) B1205561
theorem B14814829 : Blo 539803 14814829 := bstep (se 3 (by rfl) ⟨2777780, by rfl⟩ : syracuseStep 14814829 = 5555561) B5555561
theorem B6180461 : Blo 539803 6180461 := bstep (se 3 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 6180461 = 2317673) B2317673
theorem B1543931 : Blo 539803 1543931 := bstep (se 1 (by rfl) ⟨1157948, by rfl⟩ : syracuseStep 1543931 = 2315897) B2315897
theorem B683903 : Blo 539803 683903 := bstep (se 1 (by rfl) ⟨512927, by rfl⟩ : syracuseStep 683903 = 1025855) B1025855
theorem B913403 : Blo 539803 913403 := bstep (se 1 (by rfl) ⟨685052, by rfl⟩ : syracuseStep 913403 = 1370105) B1370105
theorem B4739111 : Blo 539803 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B3125375 : Blo 539803 3125375 := bstep (se 1 (by rfl) ⟨2344031, by rfl⟩ : syracuseStep 3125375 = 4688063) B4688063
theorem B1732823 : Blo 539803 1732823 := bstep (se 1 (by rfl) ⟨1299617, by rfl⟩ : syracuseStep 1732823 = 2599235) B2599235
theorem B1372403 : Blo 539803 1372403 := bstep (se 1 (by rfl) ⟨1029302, by rfl⟩ : syracuseStep 1372403 = 2058605) B2058605
theorem B1216871 : Blo 539803 1216871 := bstep (se 1 (by rfl) ⟨912653, by rfl⟩ : syracuseStep 1216871 = 1825307) B1825307
theorem B2306465 : Blo 539803 2306465 := bstep (se 2 (by rfl) ⟨864924, by rfl⟩ : syracuseStep 2306465 = 1729849) B1729849
theorem B1372585 : Blo 539803 1372585 := bstep (se 2 (by rfl) ⟨514719, by rfl⟩ : syracuseStep 1372585 = 1029439) B1029439
theorem B1831355 : Blo 539803 1831355 := bstep (se 1 (by rfl) ⟨1373516, by rfl⟩ : syracuseStep 1831355 = 2747033) B2747033
theorem B4174375 : Blo 539803 4174375 := bstep (se 1 (by rfl) ⟨3130781, by rfl⟩ : syracuseStep 4174375 = 6261563) B6261563
theorem B2052803 : Blo 539803 2052803 := bstep (se 1 (by rfl) ⟨1539602, by rfl⟩ : syracuseStep 2052803 = 3079205) B3079205
theorem B1831895 : Blo 539803 1831895 := bstep (se 1 (by rfl) ⟨1373921, by rfl⟩ : syracuseStep 1831895 = 2747843) B2747843
theorem B1094639 : Blo 539803 1094639 := bstep (se 1 (by rfl) ⟨820979, by rfl⟩ : syracuseStep 1094639 = 1641959) B1641959
theorem B41718833 : Blo 539803 41718833 := bstep (se 2 (by rfl) ⟨15644562, by rfl⟩ : syracuseStep 41718833 = 31289125) B31289125
theorem B2741363 : Blo 539803 2741363 := bstep (se 1 (by rfl) ⟨2056022, by rfl⟩ : syracuseStep 2741363 = 4112045) B4112045
theorem B3077473 : Blo 539803 3077473 := bstep (se 2 (by rfl) ⟨1154052, by rfl⟩ : syracuseStep 3077473 = 2308105) B2308105
theorem B1824551 : Blo 539803 1824551 := bstep (se 1 (by rfl) ⟨1368413, by rfl⟩ : syracuseStep 1824551 = 2736827) B2736827
theorem B1029971 : Blo 539803 1029971 := bstep (se 1 (by rfl) ⟨772478, by rfl⟩ : syracuseStep 1029971 = 1544957) B1544957
theorem B2930539 : Blo 539803 2930539 := bstep (se 1 (by rfl) ⟨2197904, by rfl⟩ : syracuseStep 2930539 = 4395809) B4395809
theorem B1095547 : Blo 539803 1095547 := bstep (se 1 (by rfl) ⟨821660, by rfl⟩ : syracuseStep 1095547 = 1643321) B1643321
theorem B21108737 : Blo 539803 21108737 := bstep (se 2 (by rfl) ⟨7915776, by rfl⟩ : syracuseStep 21108737 = 15831553) B15831553
theorem B3807271 : Blo 539803 3807271 := bstep (se 1 (by rfl) ⟨2855453, by rfl⟩ : syracuseStep 3807271 = 5710907) B5710907
theorem B2472059 : Blo 539803 2472059 := bstep (se 1 (by rfl) ⟨1854044, by rfl⟩ : syracuseStep 2472059 = 3708089) B3708089
theorem B3799169 : Blo 539803 3799169 := bstep (se 2 (by rfl) ⟨1424688, by rfl⟩ : syracuseStep 3799169 = 2849377) B2849377
theorem B2734235 : Blo 539803 2734235 := bstep (se 1 (by rfl) ⟨2050676, by rfl⟩ : syracuseStep 2734235 = 4101353) B4101353
theorem B7796897 : Blo 539803 7796897 := bstep (se 2 (by rfl) ⟨2923836, by rfl⟩ : syracuseStep 7796897 = 5847673) B5847673
theorem B2930975 : Blo 539803 2930975 := bstep (se 1 (by rfl) ⟨2198231, by rfl⟩ : syracuseStep 2930975 = 4396463) B4396463
theorem B1603997 : Blo 539803 1603997 := bstep (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) B601499
theorem B2922911 : Blo 539803 2922911 := bstep (se 1 (by rfl) ⟨2192183, by rfl⟩ : syracuseStep 2922911 = 4384367) B4384367
theorem B686495 : Blo 539803 686495 := bstep (se 1 (by rfl) ⟨514871, by rfl⟩ : syracuseStep 686495 = 1029743) B1029743
theorem B1038791 : Blo 539803 1038791 := bstep (se 1 (by rfl) ⟨779093, by rfl⟩ : syracuseStep 1038791 = 1558187) B1558187
theorem B4159993 : Blo 539803 4159993 := bstep (se 2 (by rfl) ⟨1559997, by rfl⟩ : syracuseStep 4159993 = 3119995) B3119995
theorem B1219175 : Blo 539803 1219175 := bstep (se 1 (by rfl) ⟨914381, by rfl⟩ : syracuseStep 1219175 = 1828763) B1828763
theorem B2734721 : Blo 539803 2734721 := bstep (se 2 (by rfl) ⟨1025520, by rfl⟩ : syracuseStep 2734721 = 2051041) B2051041
theorem B10427069 : Blo 539803 10427069 := bstep (se 3 (by rfl) ⟨1955075, by rfl⟩ : syracuseStep 10427069 = 3910151) B3910151
theorem B2742983 : Blo 539803 2742983 := bstep (se 1 (by rfl) ⟨2057237, by rfl⟩ : syracuseStep 2742983 = 4114475) B4114475
theorem B809705 : Blo 539803 809705 := bstep (se 2 (by rfl) ⟨303639, by rfl⟩ : syracuseStep 809705 = 607279) B607279
theorem B1219337 : Blo 539803 1219337 := bstep (se 2 (by rfl) ⟨457251, by rfl⟩ : syracuseStep 1219337 = 914503) B914503
theorem B6576977 : Blo 539803 6576977 := bstep (se 2 (by rfl) ⟨2466366, by rfl⟩ : syracuseStep 6576977 = 4932733) B4932733
theorem B809831 : Blo 539803 809831 := bstep (se 1 (by rfl) ⟨607373, by rfl⟩ : syracuseStep 809831 = 1214747) B1214747
theorem B809897 : Blo 539803 809897 := bstep (se 2 (by rfl) ⟨303711, by rfl⟩ : syracuseStep 809897 = 607423) B607423
theorem B28146653 : Blo 539803 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B2595833 : Blo 539803 2595833 := bstep (se 2 (by rfl) ⟨973437, by rfl⟩ : syracuseStep 2595833 = 1946875) B1946875
theorem B810047 : Blo 539803 810047 := bstep (se 1 (by rfl) ⟨607535, by rfl⟩ : syracuseStep 810047 = 1215071) B1215071
theorem B1039451 : Blo 539803 1039451 := bstep (se 1 (by rfl) ⟨779588, by rfl⟩ : syracuseStep 1039451 = 1559177) B1559177
theorem B810089 : Blo 539803 810089 := bstep (se 2 (by rfl) ⟨303783, by rfl⟩ : syracuseStep 810089 = 607567) B607567
theorem B810215 : Blo 539803 810215 := bstep (se 1 (by rfl) ⟨607661, by rfl⟩ : syracuseStep 810215 = 1215323) B1215323
theorem B3087679 : Blo 539803 3087679 := bstep (se 1 (by rfl) ⟨2315759, by rfl⟩ : syracuseStep 3087679 = 4631519) B4631519
theorem B6176087 : Blo 539803 6176087 := bstep (se 1 (by rfl) ⟨4632065, by rfl⟩ : syracuseStep 6176087 = 9264131) B9264131
theorem B540127 : Blo 539803 540127 := bstep (se 1 (by rfl) ⟨405095, by rfl⟩ : syracuseStep 540127 = 810191) B810191
theorem B540207 : Blo 539803 540207 := bstep (se 1 (by rfl) ⟨405155, by rfl⟩ : syracuseStep 540207 = 810311) B810311
theorem B6938257 : Blo 539803 6938257 := bstep (se 2 (by rfl) ⟨2601846, by rfl⟩ : syracuseStep 6938257 = 5203693) B5203693
theorem B540315 : Blo 539803 540315 := bstep (se 1 (by rfl) ⟨405236, by rfl⟩ : syracuseStep 540315 = 810473) B810473
theorem B810719 : Blo 539803 810719 := bstep (se 1 (by rfl) ⟨608039, by rfl⟩ : syracuseStep 810719 = 1216079) B1216079
theorem B1220327 : Blo 539803 1220327 := bstep (se 1 (by rfl) ⟨915245, by rfl⟩ : syracuseStep 1220327 = 1830491) B1830491
theorem B540411 : Blo 539803 540411 := bstep (se 1 (by rfl) ⟨405308, by rfl⟩ : syracuseStep 540411 = 810617) B810617
theorem B2309917 : Blo 539803 2309917 := bstep (se 3 (by rfl) ⟨433109, by rfl⟩ : syracuseStep 2309917 = 866219) B866219
theorem B6577949 : Blo 539803 6577949 := bstep (se 3 (by rfl) ⟨1233365, by rfl⟩ : syracuseStep 6577949 = 2466731) B2466731
theorem B540575 : Blo 539803 540575 := bstep (se 1 (by rfl) ⟨405431, by rfl⟩ : syracuseStep 540575 = 810863) B810863
theorem B1236905 : Blo 539803 1236905 := bstep (se 2 (by rfl) ⟨463839, by rfl⟩ : syracuseStep 1236905 = 927679) B927679
theorem B540699 : Blo 539803 540699 := bstep (se 1 (by rfl) ⟨405524, by rfl⟩ : syracuseStep 540699 = 811049) B811049
theorem B540719 : Blo 539803 540719 := bstep (se 1 (by rfl) ⟨405539, by rfl⟩ : syracuseStep 540719 = 811079) B811079
theorem B540743 : Blo 539803 540743 := bstep (se 1 (by rfl) ⟨405557, by rfl⟩ : syracuseStep 540743 = 811115) B811115
theorem B540799 : Blo 539803 540799 := bstep (se 1 (by rfl) ⟨405599, by rfl⟩ : syracuseStep 540799 = 811199) B811199
theorem B1155215 : Blo 539803 1155215 := bstep (se 1 (by rfl) ⟨866411, by rfl⟩ : syracuseStep 1155215 = 1732823) B1732823
theorem B811247 : Blo 539803 811247 := bstep (se 1 (by rfl) ⟨608435, by rfl⟩ : syracuseStep 811247 = 1216871) B1216871
theorem B540923 : Blo 539803 540923 := bstep (se 1 (by rfl) ⟨405692, by rfl⟩ : syracuseStep 540923 = 811385) B811385
theorem B1220903 : Blo 539803 1220903 := bstep (se 1 (by rfl) ⟨915677, by rfl⟩ : syracuseStep 1220903 = 1831355) B1831355
theorem B811433 : Blo 539803 811433 := bstep (se 2 (by rfl) ⟨304287, by rfl⟩ : syracuseStep 811433 = 608575) B608575
theorem B541119 : Blo 539803 541119 := bstep (se 1 (by rfl) ⟨405839, by rfl⟩ : syracuseStep 541119 = 811679) B811679
theorem B1368535 : Blo 539803 1368535 := bstep (se 1 (by rfl) ⟨1026401, by rfl⟩ : syracuseStep 1368535 = 2052803) B2052803
theorem B1540583 : Blo 539803 1540583 := bstep (se 1 (by rfl) ⟨1155437, by rfl⟩ : syracuseStep 1540583 = 2310875) B2310875
theorem B811625 : Blo 539803 811625 := bstep (se 2 (by rfl) ⟨304359, by rfl⟩ : syracuseStep 811625 = 608719) B608719
theorem B1221263 : Blo 539803 1221263 := bstep (se 1 (by rfl) ⟨915947, by rfl⟩ : syracuseStep 1221263 = 1831895) B1831895
theorem B541343 : Blo 539803 541343 := bstep (se 1 (by rfl) ⟨406007, by rfl⟩ : syracuseStep 541343 = 812015) B812015
theorem B5546657 : Blo 539803 5546657 := bstep (se 2 (by rfl) ⟨2079996, by rfl⟩ : syracuseStep 5546657 = 4159993) B4159993
theorem B27812555 : Blo 539803 27812555 := bstep (se 1 (by rfl) ⟨20859416, by rfl⟩ : syracuseStep 27812555 = 41718833) B41718833
theorem B541415 : Blo 539803 541415 := bstep (se 1 (by rfl) ⟨406061, by rfl⟩ : syracuseStep 541415 = 812123) B812123
theorem B541423 : Blo 539803 541423 := bstep (se 1 (by rfl) ⟨406067, by rfl⟩ : syracuseStep 541423 = 812135) B812135
theorem B1827575 : Blo 539803 1827575 := bstep (se 1 (by rfl) ⟨1370681, by rfl⟩ : syracuseStep 1827575 = 2741363) B2741363
theorem B31687433 : Blo 539803 31687433 := bstep (se 2 (by rfl) ⟨11882787, by rfl⟩ : syracuseStep 31687433 = 23765575) B23765575
theorem B16646975 : Blo 539803 16646975 := bstep (se 1 (by rfl) ⟨12485231, by rfl⟩ : syracuseStep 16646975 = 24970463) B24970463
theorem B541511 : Blo 539803 541511 := bstep (se 1 (by rfl) ⟨406133, by rfl⟩ : syracuseStep 541511 = 812267) B812267
theorem B541599 : Blo 539803 541599 := bstep (se 1 (by rfl) ⟨406199, by rfl⟩ : syracuseStep 541599 = 812399) B812399
theorem B541679 : Blo 539803 541679 := bstep (se 1 (by rfl) ⟨406259, by rfl⟩ : syracuseStep 541679 = 812519) B812519
theorem B541767 : Blo 539803 541767 := bstep (se 1 (by rfl) ⟨406325, by rfl⟩ : syracuseStep 541767 = 812651) B812651
theorem B541799 : Blo 539803 541799 := bstep (se 1 (by rfl) ⟨406349, by rfl⟩ : syracuseStep 541799 = 812699) B812699
theorem B8463485 : Blo 539803 8463485 := bstep (se 3 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 8463485 = 3173807) B3173807
theorem B59327639 : Blo 539803 59327639 := bstep (se 1 (by rfl) ⟨44495729, by rfl⟩ : syracuseStep 59327639 = 88991459) B88991459
theorem B2770109 : Blo 539803 2770109 := bstep (se 3 (by rfl) ⟨519395, by rfl⟩ : syracuseStep 2770109 = 1038791) B1038791
theorem B976097 : Blo 539803 976097 := bstep (se 2 (by rfl) ⟨366036, by rfl⟩ : syracuseStep 976097 = 732073) B732073
theorem B541947 : Blo 539803 541947 := bstep (se 1 (by rfl) ⟨406460, by rfl⟩ : syracuseStep 541947 = 812921) B812921
theorem B10544393 : Blo 539803 10544393 := bstep (se 2 (by rfl) ⟨3954147, by rfl⟩ : syracuseStep 10544393 = 7908295) B7908295
theorem B2311591 : Blo 539803 2311591 := bstep (se 1 (by rfl) ⟨1733693, by rfl⟩ : syracuseStep 2311591 = 3467387) B3467387
theorem B1648039 : Blo 539803 1648039 := bstep (se 1 (by rfl) ⟨1236029, by rfl⟩ : syracuseStep 1648039 = 2472059) B2472059
theorem B2532779 : Blo 539803 2532779 := bstep (se 1 (by rfl) ⟨1899584, by rfl⟩ : syracuseStep 2532779 = 3799169) B3799169
theorem B812783 : Blo 539803 812783 := bstep (se 1 (by rfl) ⟨609587, by rfl⟩ : syracuseStep 812783 = 1219175) B1219175
theorem B542447 : Blo 539803 542447 := bstep (se 1 (by rfl) ⟨406835, by rfl⟩ : syracuseStep 542447 = 813671) B813671
theorem B1828655 : Blo 539803 1828655 := bstep (se 1 (by rfl) ⟨1371491, by rfl⟩ : syracuseStep 1828655 = 2742983) B2742983
theorem B812891 : Blo 539803 812891 := bstep (se 1 (by rfl) ⟨609668, by rfl⟩ : syracuseStep 812891 = 1219337) B1219337
theorem B4384651 : Blo 539803 4384651 := bstep (se 1 (by rfl) ⟨3288488, by rfl⟩ : syracuseStep 4384651 = 6576977) B6576977
theorem B542631 : Blo 539803 542631 := bstep (se 1 (by rfl) ⟨406973, by rfl⟩ : syracuseStep 542631 = 813947) B813947
theorem B1730555 : Blo 539803 1730555 := bstep (se 1 (by rfl) ⟨1297916, by rfl⟩ : syracuseStep 1730555 = 2595833) B2595833
theorem B17541197 : Blo 539803 17541197 := bstep (se 3 (by rfl) ⟨3288974, by rfl⟩ : syracuseStep 17541197 = 6577949) B6577949
theorem B1099919 : Blo 539803 1099919 := bstep (se 1 (by rfl) ⟨824939, by rfl⟩ : syracuseStep 1099919 = 1649879) B1649879
theorem B19753105 : Blo 539803 19753105 := bstep (se 2 (by rfl) ⟨7407414, by rfl⟩ : syracuseStep 19753105 = 14814829) B14814829
theorem B9251009 : Blo 539803 9251009 := bstep (se 2 (by rfl) ⟨3469128, by rfl⟩ : syracuseStep 9251009 = 6938257) B6938257
theorem B31295969 : Blo 539803 31295969 := bstep (se 2 (by rfl) ⟨11735988, by rfl⟩ : syracuseStep 31295969 = 23471977) B23471977
theorem B813551 : Blo 539803 813551 := bstep (se 1 (by rfl) ⟨610163, by rfl⟩ : syracuseStep 813551 = 1220327) B1220327
theorem B1460729 : Blo 539803 1460729 := bstep (se 2 (by rfl) ⟨547773, by rfl⟩ : syracuseStep 1460729 = 1095547) B1095547
theorem B1215017 : Blo 539803 1215017 := bstep (se 2 (by rfl) ⟨455631, by rfl⟩ : syracuseStep 1215017 = 911263) B911263
theorem B2919037 : Blo 539803 2919037 := bstep (se 3 (by rfl) ⟨547319, by rfl⟩ : syracuseStep 2919037 = 1094639) B1094639
theorem B608935 : Blo 539803 608935 := bstep (se 1 (by rfl) ⟨456701, by rfl⟩ : syracuseStep 608935 = 913403) B913403
theorem B2083583 : Blo 539803 2083583 := bstep (se 1 (by rfl) ⟨1562687, by rfl⟩ : syracuseStep 2083583 = 3125375) B3125375
theorem B813863 : Blo 539803 813863 := bstep (se 1 (by rfl) ⟨610397, by rfl⟩ : syracuseStep 813863 = 1220795) B1220795
theorem B2771869 : Blo 539803 2771869 := bstep (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) B1039451
theorem B14035913 : Blo 539803 14035913 := bstep (se 2 (by rfl) ⟨5263467, by rfl⟩ : syracuseStep 14035913 = 10526935) B10526935
theorem B1215593 : Blo 539803 1215593 := bstep (se 2 (by rfl) ⟨455847, by rfl⟩ : syracuseStep 1215593 = 911695) B911695
theorem B912539 : Blo 539803 912539 := bstep (se 1 (by rfl) ⟨684404, by rfl⟩ : syracuseStep 912539 = 1368809) B1368809
theorem B1830113 : Blo 539803 1830113 := bstep (se 2 (by rfl) ⟨686292, by rfl⟩ : syracuseStep 1830113 = 1372585) B1372585
theorem B683311 : Blo 539803 683311 := bstep (se 1 (by rfl) ⟨512483, by rfl⟩ : syracuseStep 683311 = 1024967) B1024967
theorem B5565833 : Blo 539803 5565833 := bstep (se 2 (by rfl) ⟨2087187, by rfl⟩ : syracuseStep 5565833 = 4174375) B4174375
theorem B1830653 : Blo 539803 1830653 := bstep (se 3 (by rfl) ⟨343247, by rfl⟩ : syracuseStep 1830653 = 686495) B686495
theorem B2060063 : Blo 539803 2060063 := bstep (se 1 (by rfl) ⟨1545047, by rfl⟩ : syracuseStep 2060063 = 3090095) B3090095
theorem B1216367 : Blo 539803 1216367 := bstep (se 1 (by rfl) ⟨912275, by rfl⟩ : syracuseStep 1216367 = 1824551) B1824551
theorem B11710565 : Blo 539803 11710565 := bstep (se 4 (by rfl) ⟨1097865, by rfl⟩ : syracuseStep 11710565 = 2195731) B2195731
theorem B1822823 : Blo 539803 1822823 := bstep (se 1 (by rfl) ⟨1367117, by rfl⟩ : syracuseStep 1822823 = 2734235) B2734235
theorem B913511 : Blo 539803 913511 := bstep (se 1 (by rfl) ⟨685133, by rfl⟩ : syracuseStep 913511 = 1370267) B1370267
theorem B5197931 : Blo 539803 5197931 := bstep (se 1 (by rfl) ⟨3898448, by rfl⟩ : syracuseStep 5197931 = 7796897) B7796897
theorem B1953983 : Blo 539803 1953983 := bstep (se 1 (by rfl) ⟨1465487, by rfl⟩ : syracuseStep 1953983 = 2930975) B2930975
theorem B2191579 : Blo 539803 2191579 := bstep (se 1 (by rfl) ⟨1643684, by rfl⟩ : syracuseStep 2191579 = 3287369) B3287369
theorem B1069331 : Blo 539803 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B4116905 : Blo 539803 4116905 := bstep (se 2 (by rfl) ⟨1543839, by rfl⟩ : syracuseStep 4116905 = 3087679) B3087679
theorem B1823147 : Blo 539803 1823147 := bstep (se 1 (by rfl) ⟨1367360, by rfl⟩ : syracuseStep 1823147 = 2734721) B2734721
theorem B11891123 : Blo 539803 11891123 := bstep (se 1 (by rfl) ⟨8918342, by rfl⟩ : syracuseStep 11891123 = 17836685) B17836685
theorem B6951379 : Blo 539803 6951379 := bstep (se 1 (by rfl) ⟨5213534, by rfl⟩ : syracuseStep 6951379 = 10427069) B10427069
theorem B18764435 : Blo 539803 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B914267 : Blo 539803 914267 := bstep (se 1 (by rfl) ⟨685700, by rfl⟩ : syracuseStep 914267 = 1371401) B1371401
theorem B4117391 : Blo 539803 4117391 := bstep (se 1 (by rfl) ⟨3088043, by rfl⟩ : syracuseStep 4117391 = 6176087) B6176087
theorem B2143219 : Blo 539803 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B1823741 : Blo 539803 1823741 := bstep (se 3 (by rfl) ⟨341951, by rfl⟩ : syracuseStep 1823741 = 683903) B683903
theorem B1029287 : Blo 539803 1029287 := bstep (se 1 (by rfl) ⟨771965, by rfl⟩ : syracuseStep 1029287 = 1543931) B1543931
theorem B824603 : Blo 539803 824603 := bstep (se 1 (by rfl) ⟨618452, by rfl⟩ : syracuseStep 824603 = 1236905) B1236905
theorem B1949701475 : Blo 539803 1949701475 := bstep (se 1 (by rfl) ⟨1462276106, by rfl⟩ : syracuseStep 1949701475 = 2924552213) B2924552213
theorem B3159407 : Blo 539803 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B5076361 : Blo 539803 5076361 := bstep (se 2 (by rfl) ⟨1903635, by rfl⟩ : syracuseStep 5076361 = 3807271) B3807271
theorem B914935 : Blo 539803 914935 := bstep (se 1 (by rfl) ⟨686201, by rfl⟩ : syracuseStep 914935 = 1372403) B1372403
theorem B8754767 : Blo 539803 8754767 := bstep (se 1 (by rfl) ⟨6566075, by rfl⟩ : syracuseStep 8754767 = 13132151) B13132151
theorem B1537643 : Blo 539803 1537643 := bstep (se 1 (by rfl) ⟨1153232, by rfl⟩ : syracuseStep 1537643 = 2306465) B2306465
theorem B2053775 : Blo 539803 2053775 := bstep (se 1 (by rfl) ⟨1540331, by rfl⟩ : syracuseStep 2053775 = 3080663) B3080663
theorem B7116635 : Blo 539803 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B13178771 : Blo 539803 13178771 := bstep (se 1 (by rfl) ⟨9884078, by rfl⟩ : syracuseStep 13178771 = 19768157) B19768157
theorem B1152959 : Blo 539803 1152959 := bstep (se 1 (by rfl) ⟨864719, by rfl⟩ : syracuseStep 1152959 = 1729439) B1729439
theorem B1218671 : Blo 539803 1218671 := bstep (se 1 (by rfl) ⟨914003, by rfl⟩ : syracuseStep 1218671 = 1828007) B1828007
theorem B1824983 : Blo 539803 1824983 := bstep (se 1 (by rfl) ⟨1368737, by rfl⟩ : syracuseStep 1824983 = 2737475) B2737475
theorem B2054443 : Blo 539803 2054443 := bstep (se 1 (by rfl) ⟨1540832, by rfl⟩ : syracuseStep 2054443 = 3081665) B3081665
theorem B1030457 : Blo 539803 1030457 := bstep (se 2 (by rfl) ⟨386421, by rfl⟩ : syracuseStep 1030457 = 772843) B772843
theorem B1464655 : Blo 539803 1464655 := bstep (se 1 (by rfl) ⟨1098491, by rfl⟩ : syracuseStep 1464655 = 2196983) B2196983
theorem B686647 : Blo 539803 686647 := bstep (se 1 (by rfl) ⟨514985, by rfl⟩ : syracuseStep 686647 = 1029971) B1029971
theorem B1301147 : Blo 539803 1301147 := bstep (se 1 (by rfl) ⟨975860, by rfl⟩ : syracuseStep 1301147 = 1951721) B1951721
theorem B14072491 : Blo 539803 14072491 := bstep (se 1 (by rfl) ⟨10554368, by rfl⟩ : syracuseStep 14072491 = 21108737) B21108737
theorem B2317025 : Blo 539803 2317025 := bstep (se 2 (by rfl) ⟨868884, by rfl⟩ : syracuseStep 2317025 = 1737769) B1737769
theorem B1948607 : Blo 539803 1948607 := bstep (se 1 (by rfl) ⟨1461455, by rfl⟩ : syracuseStep 1948607 = 2922911) B2922911
theorem B1825847 : Blo 539803 1825847 := bstep (se 1 (by rfl) ⟨1369385, by rfl⟩ : syracuseStep 1825847 = 2738771) B2738771
theorem B810095 : Blo 539803 810095 := bstep (se 1 (by rfl) ⟨607571, by rfl⟩ : syracuseStep 810095 = 1215143) B1215143
theorem B4103297 : Blo 539803 4103297 := bstep (se 2 (by rfl) ⟨1538736, by rfl⟩ : syracuseStep 4103297 = 3077473) B3077473
theorem B539803 : Blo 539803 539803 := bstep (se 1 (by rfl) ⟨404852, by rfl⟩ : syracuseStep 539803 = 809705) B809705
theorem B539887 : Blo 539803 539887 := bstep (se 1 (by rfl) ⟨404915, by rfl⟩ : syracuseStep 539887 = 809831) B809831
theorem B539931 : Blo 539803 539931 := bstep (se 1 (by rfl) ⟨404948, by rfl⟩ : syracuseStep 539931 = 809897) B809897
theorem B1219931 : Blo 539803 1219931 := bstep (se 1 (by rfl) ⟨914948, by rfl⟩ : syracuseStep 1219931 = 1829897) B1829897
theorem B6266231 : Blo 539803 6266231 := bstep (se 1 (by rfl) ⟨4699673, by rfl⟩ : syracuseStep 6266231 = 9399347) B9399347
theorem B540031 : Blo 539803 540031 := bstep (se 1 (by rfl) ⟨405023, by rfl⟩ : syracuseStep 540031 = 810047) B810047
theorem B540059 : Blo 539803 540059 := bstep (se 1 (by rfl) ⟨405044, by rfl⟩ : syracuseStep 540059 = 810089) B810089
theorem B540143 : Blo 539803 540143 := bstep (se 1 (by rfl) ⟨405107, by rfl⟩ : syracuseStep 540143 = 810215) B810215
theorem B810479 : Blo 539803 810479 := bstep (se 1 (by rfl) ⟨607859, by rfl⟩ : syracuseStep 810479 = 1215719) B1215719
theorem B3079889 : Blo 539803 3079889 := bstep (se 2 (by rfl) ⟨1154958, by rfl⟩ : syracuseStep 3079889 = 2309917) B2309917
theorem B4120307 : Blo 539803 4120307 := bstep (se 1 (by rfl) ⟨3090230, by rfl⟩ : syracuseStep 4120307 = 6180461) B6180461
theorem B3907385 : Blo 539803 3907385 := bstep (se 2 (by rfl) ⟨1465269, by rfl⟩ : syracuseStep 3907385 = 2930539) B2930539
theorem B540479 : Blo 539803 540479 := bstep (se 1 (by rfl) ⟨405359, by rfl⟩ : syracuseStep 540479 = 810719) B810719
theorem B1826657 : Blo 539803 1826657 := bstep (se 2 (by rfl) ⟨684996, by rfl⟩ : syracuseStep 1826657 = 1369993) B1369993
theorem B7807043 : Blo 539803 7807043 := bstep (se 1 (by rfl) ⟨5855282, by rfl⟩ : syracuseStep 7807043 = 11710565) B11710565
theorem B3465287 : Blo 539803 3465287 := bstep (se 1 (by rfl) ⟨2598965, by rfl⟩ : syracuseStep 3465287 = 5197931) B5197931
theorem B770143 : Blo 539803 770143 := bstep (se 1 (by rfl) ⟨577607, by rfl⟩ : syracuseStep 770143 = 1155215) B1155215
theorem B1302655 : Blo 539803 1302655 := bstep (se 1 (by rfl) ⟨976991, by rfl⟩ : syracuseStep 1302655 = 1953983) B1953983
theorem B540831 : Blo 539803 540831 := bstep (se 1 (by rfl) ⟨405623, by rfl⟩ : syracuseStep 540831 = 811247) B811247
theorem B26337473 : Blo 539803 26337473 := bstep (se 2 (by rfl) ⟨9876552, by rfl⟩ : syracuseStep 26337473 = 19753105) B19753105
theorem B540955 : Blo 539803 540955 := bstep (se 1 (by rfl) ⟨405716, by rfl⟩ : syracuseStep 540955 = 811433) B811433
theorem B2744603 : Blo 539803 2744603 := bstep (se 1 (by rfl) ⟨2058452, by rfl⟩ : syracuseStep 2744603 = 4116905) B4116905
theorem B22569293 : Blo 539803 22569293 := bstep (se 3 (by rfl) ⟨4231742, by rfl⟩ : syracuseStep 22569293 = 8463485) B8463485
theorem B2933117 : Blo 539803 2933117 := bstep (se 3 (by rfl) ⟨549959, by rfl⟩ : syracuseStep 2933117 = 1099919) B1099919
theorem B541083 : Blo 539803 541083 := bstep (se 1 (by rfl) ⟨405812, by rfl⟩ : syracuseStep 541083 = 811625) B811625
theorem B12509623 : Blo 539803 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B2744765 : Blo 539803 2744765 := bstep (se 3 (by rfl) ⟨514643, by rfl⟩ : syracuseStep 2744765 = 1029287) B1029287
theorem B2744927 : Blo 539803 2744927 := bstep (se 1 (by rfl) ⟨2058695, by rfl⟩ : syracuseStep 2744927 = 4117391) B4117391
theorem B2851549 : Blo 539803 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B39551759 : Blo 539803 39551759 := bstep (se 1 (by rfl) ⟨29663819, by rfl⟩ : syracuseStep 39551759 = 59327639) B59327639
theorem B3892049 : Blo 539803 3892049 := bstep (se 2 (by rfl) ⟨1459518, by rfl⟩ : syracuseStep 3892049 = 2919037) B2919037
theorem B7029595 : Blo 539803 7029595 := bstep (se 1 (by rfl) ⟨5272196, by rfl⟩ : syracuseStep 7029595 = 10544393) B10544393
theorem B811913 : Blo 539803 811913 := bstep (se 2 (by rfl) ⟨304467, by rfl⟩ : syracuseStep 811913 = 608935) B608935
theorem B2106271 : Blo 539803 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B1688519 : Blo 539803 1688519 := bstep (se 1 (by rfl) ⟨1266389, by rfl⟩ : syracuseStep 1688519 = 2532779) B2532779
theorem B1369183 : Blo 539803 1369183 := bstep (se 1 (by rfl) ⟨1026887, by rfl⟩ : syracuseStep 1369183 = 2053775) B2053775
theorem B541855 : Blo 539803 541855 := bstep (se 1 (by rfl) ⟨406391, by rfl⟩ : syracuseStep 541855 = 812783) B812783
theorem B3695825 : Blo 539803 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B4744423 : Blo 539803 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B541927 : Blo 539803 541927 := bstep (se 1 (by rfl) ⟨406445, by rfl⟩ : syracuseStep 541927 = 812891) B812891
theorem B812447 : Blo 539803 812447 := bstep (se 1 (by rfl) ⟨609335, by rfl⟩ : syracuseStep 812447 = 1218671) B1218671
theorem B542367 : Blo 539803 542367 := bstep (se 1 (by rfl) ⟨406775, by rfl⟩ : syracuseStep 542367 = 813551) B813551
theorem B911081 : Blo 539803 911081 := bstep (se 2 (by rfl) ⟨341655, by rfl⟩ : syracuseStep 911081 = 683311) B683311
theorem B6768481 : Blo 539803 6768481 := bstep (se 2 (by rfl) ⟨2538180, by rfl⟩ : syracuseStep 6768481 = 5076361) B5076361
theorem B542575 : Blo 539803 542575 := bstep (se 1 (by rfl) ⟨406931, by rfl⟩ : syracuseStep 542575 = 813863) B813863
theorem B3082121 : Blo 539803 3082121 := bstep (se 2 (by rfl) ⟨1155795, by rfl⟩ : syracuseStep 3082121 = 2311591) B2311591
theorem B2197385 : Blo 539803 2197385 := bstep (se 2 (by rfl) ⟨824019, by rfl⟩ : syracuseStep 2197385 = 1648039) B1648039
theorem B9357275 : Blo 539803 9357275 := bstep (se 1 (by rfl) ⟨7017956, by rfl⟩ : syracuseStep 9357275 = 14035913) B14035913
theorem B5556221 : Blo 539803 5556221 := bstep (se 3 (by rfl) ⟨1041791, by rfl⟩ : syracuseStep 5556221 = 2083583) B2083583
theorem B608359 : Blo 539803 608359 := bstep (se 1 (by rfl) ⟨456269, by rfl⟩ : syracuseStep 608359 = 912539) B912539
theorem B813287 : Blo 539803 813287 := bstep (se 1 (by rfl) ⟨609965, by rfl⟩ : syracuseStep 813287 = 1219931) B1219931
theorem B2746871 : Blo 539803 2746871 := bstep (se 1 (by rfl) ⟨2060153, by rfl⟩ : syracuseStep 2746871 = 4120307) B4120307
theorem B3074557 : Blo 539803 3074557 := bstep (se 3 (by rfl) ⟨576479, by rfl⟩ : syracuseStep 3074557 = 1152959) B1152959
theorem B1215215 : Blo 539803 1215215 := bstep (se 1 (by rfl) ⟨911411, by rfl⟩ : syracuseStep 1215215 = 1822823) B1822823
theorem B609007 : Blo 539803 609007 := bstep (se 1 (by rfl) ⟨456755, by rfl⟩ : syracuseStep 609007 = 913511) B913511
theorem B813935 : Blo 539803 813935 := bstep (se 1 (by rfl) ⟨610451, by rfl⟩ : syracuseStep 813935 = 1220903) B1220903
theorem B1215431 : Blo 539803 1215431 := bstep (se 1 (by rfl) ⟨911573, by rfl⟩ : syracuseStep 1215431 = 1823147) B1823147
theorem B1027055 : Blo 539803 1027055 := bstep (se 1 (by rfl) ⟨770291, by rfl⟩ : syracuseStep 1027055 = 1540583) B1540583
theorem B2739257 : Blo 539803 2739257 := bstep (se 2 (by rfl) ⟨1027221, by rfl⟩ : syracuseStep 2739257 = 2054443) B2054443
theorem B814175 : Blo 539803 814175 := bstep (se 1 (by rfl) ⟨610631, by rfl⟩ : syracuseStep 814175 = 1221263) B1221263
theorem B1952873 : Blo 539803 1952873 := bstep (se 2 (by rfl) ⟨732327, by rfl⟩ : syracuseStep 1952873 = 1464655) B1464655
theorem B18541703 : Blo 539803 18541703 := bstep (se 1 (by rfl) ⟨13906277, by rfl⟩ : syracuseStep 18541703 = 27812555) B27812555
theorem B609511 : Blo 539803 609511 := bstep (se 1 (by rfl) ⟨457133, by rfl⟩ : syracuseStep 609511 = 914267) B914267
theorem B9268505 : Blo 539803 9268505 := bstep (se 2 (by rfl) ⟨3475689, by rfl⟩ : syracuseStep 9268505 = 6951379) B6951379
theorem B1215827 : Blo 539803 1215827 := bstep (se 1 (by rfl) ⟨911870, by rfl⟩ : syracuseStep 1215827 = 1823741) B1823741
theorem B1846739 : Blo 539803 1846739 := bstep (se 1 (by rfl) ⟨1385054, by rfl⟩ : syracuseStep 1846739 = 2770109) B2770109
theorem B18763321 : Blo 539803 18763321 := bstep (se 2 (by rfl) ⟨7036245, by rfl⟩ : syracuseStep 18763321 = 14072491) B14072491
theorem B5199203933 : Blo 539803 5199203933 := bstep (se 3 (by rfl) ⟨974850737, by rfl⟩ : syracuseStep 5199203933 = 1949701475) B1949701475
theorem B5836511 : Blo 539803 5836511 := bstep (se 1 (by rfl) ⟨4377383, by rfl⟩ : syracuseStep 5836511 = 8754767) B8754767
theorem B8785847 : Blo 539803 8785847 := bstep (se 1 (by rfl) ⟨6589385, by rfl⟩ : syracuseStep 8785847 = 13178771) B13178771
theorem B11694131 : Blo 539803 11694131 := bstep (se 1 (by rfl) ⟨8770598, by rfl⟩ : syracuseStep 11694131 = 17541197) B17541197
theorem B1216655 : Blo 539803 1216655 := bstep (se 1 (by rfl) ⟨912491, by rfl⟩ : syracuseStep 1216655 = 1824983) B1824983
theorem B4100381 : Blo 539803 4100381 := bstep (se 3 (by rfl) ⟨768821, by rfl⟩ : syracuseStep 4100381 = 1537643) B1537643
theorem B14791085 : Blo 539803 14791085 := bstep (se 3 (by rfl) ⟨2773328, by rfl⟩ : syracuseStep 14791085 = 5546657) B5546657
theorem B1544683 : Blo 539803 1544683 := bstep (se 1 (by rfl) ⟨1158512, by rfl⟩ : syracuseStep 1544683 = 2317025) B2317025
theorem B1299071 : Blo 539803 1299071 := bstep (se 1 (by rfl) ⟨974303, by rfl⟩ : syracuseStep 1299071 = 1948607) B1948607
theorem B1217231 : Blo 539803 1217231 := bstep (se 1 (by rfl) ⟨912923, by rfl⟩ : syracuseStep 1217231 = 1825847) B1825847
theorem B2053259 : Blo 539803 2053259 := bstep (se 1 (by rfl) ⟨1539944, by rfl⟩ : syracuseStep 2053259 = 3079889) B3079889
theorem B5846201 : Blo 539803 5846201 := bstep (se 2 (by rfl) ⟨2192325, by rfl⟩ : syracuseStep 5846201 = 4384651) B4384651
theorem B1373375 : Blo 539803 1373375 := bstep (se 1 (by rfl) ⟨1030031, by rfl⟩ : syracuseStep 1373375 = 2060063) B2060063
theorem B1217771 : Blo 539803 1217771 := bstep (se 1 (by rfl) ⟨913328, by rfl⟩ : syracuseStep 1217771 = 1826657) B1826657
theorem B4177487 : Blo 539803 4177487 := bstep (se 1 (by rfl) ⟨3133115, by rfl⟩ : syracuseStep 4177487 = 6266231) B6266231
theorem B8795765 : Blo 539803 8795765 := bstep (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) B824603
theorem B7927415 : Blo 539803 7927415 := bstep (se 1 (by rfl) ⟨5945561, by rfl⟩ : syracuseStep 7927415 = 11891123) B11891123
theorem B1218383 : Blo 539803 1218383 := bstep (se 1 (by rfl) ⟨913787, by rfl⟩ : syracuseStep 1218383 = 1827575) B1827575
theorem B21124955 : Blo 539803 21124955 := bstep (se 1 (by rfl) ⟨15843716, by rfl⟩ : syracuseStep 21124955 = 31687433) B31687433
theorem B11097983 : Blo 539803 11097983 := bstep (se 1 (by rfl) ⟨8323487, by rfl⟩ : syracuseStep 11097983 = 16646975) B16646975
theorem B2602925 : Blo 539803 2602925 := bstep (se 3 (by rfl) ⟨488048, by rfl⟩ : syracuseStep 2602925 = 976097) B976097
theorem B1824713 : Blo 539803 1824713 := bstep (se 2 (by rfl) ⟨684267, by rfl⟩ : syracuseStep 1824713 = 1368535) B1368535
theorem B915529 : Blo 539803 915529 := bstep (se 2 (by rfl) ⟨343323, by rfl⟩ : syracuseStep 915529 = 686647) B686647
theorem B11688421 : Blo 539803 11688421 := bstep (se 4 (by rfl) ⟨1095789, by rfl⟩ : syracuseStep 11688421 = 2191579) B2191579
theorem B1219103 : Blo 539803 1219103 := bstep (se 1 (by rfl) ⟨914327, by rfl⟩ : syracuseStep 1219103 = 1828655) B1828655
theorem B2857625 : Blo 539803 2857625 := bstep (se 2 (by rfl) ⟨1071609, by rfl⟩ : syracuseStep 2857625 = 2143219) B2143219
theorem B1153703 : Blo 539803 1153703 := bstep (se 1 (by rfl) ⟨865277, by rfl⟩ : syracuseStep 1153703 = 1730555) B1730555
theorem B6167339 : Blo 539803 6167339 := bstep (se 1 (by rfl) ⟨4625504, by rfl⟩ : syracuseStep 6167339 = 9251009) B9251009
theorem B686971 : Blo 539803 686971 := bstep (se 1 (by rfl) ⟨515228, by rfl⟩ : syracuseStep 686971 = 1030457) B1030457
theorem B20863979 : Blo 539803 20863979 := bstep (se 1 (by rfl) ⟨15647984, by rfl⟩ : syracuseStep 20863979 = 31295969) B31295969
theorem B973819 : Blo 539803 973819 := bstep (se 1 (by rfl) ⟨730364, by rfl⟩ : syracuseStep 973819 = 1460729) B1460729
theorem B810011 : Blo 539803 810011 := bstep (se 1 (by rfl) ⟨607508, by rfl⟩ : syracuseStep 810011 = 1215017) B1215017
theorem B867431 : Blo 539803 867431 := bstep (se 1 (by rfl) ⟨650573, by rfl⟩ : syracuseStep 867431 = 1301147) B1301147
theorem B1219913 : Blo 539803 1219913 := bstep (se 2 (by rfl) ⟨457467, by rfl⟩ : syracuseStep 1219913 = 914935) B914935
theorem B810395 : Blo 539803 810395 := bstep (se 1 (by rfl) ⟨607796, by rfl⟩ : syracuseStep 810395 = 1215593) B1215593
theorem B540063 : Blo 539803 540063 := bstep (se 1 (by rfl) ⟨405047, by rfl⟩ : syracuseStep 540063 = 810095) B810095
theorem B2735531 : Blo 539803 2735531 := bstep (se 1 (by rfl) ⟨2051648, by rfl⟩ : syracuseStep 2735531 = 4103297) B4103297
theorem B1220075 : Blo 539803 1220075 := bstep (se 1 (by rfl) ⟨915056, by rfl⟩ : syracuseStep 1220075 = 1830113) B1830113
theorem B3710555 : Blo 539803 3710555 := bstep (se 1 (by rfl) ⟨2782916, by rfl⟩ : syracuseStep 3710555 = 5565833) B5565833
theorem B540319 : Blo 539803 540319 := bstep (se 1 (by rfl) ⟨405239, by rfl⟩ : syracuseStep 540319 = 810479) B810479
theorem B1220435 : Blo 539803 1220435 := bstep (se 1 (by rfl) ⟨915326, by rfl⟩ : syracuseStep 1220435 = 1830653) B1830653
theorem B2604923 : Blo 539803 2604923 := bstep (se 1 (by rfl) ⟨1953692, by rfl⟩ : syracuseStep 2604923 = 3907385) B3907385
theorem B810911 : Blo 539803 810911 := bstep (se 1 (by rfl) ⟨608183, by rfl⟩ : syracuseStep 810911 = 1216367) B1216367
theorem B2310191 : Blo 539803 2310191 := bstep (se 1 (by rfl) ⟨1732643, by rfl⟩ : syracuseStep 2310191 = 3465287) B3465287
theorem B811103 : Blo 539803 811103 := bstep (se 1 (by rfl) ⟨608327, by rfl⟩ : syracuseStep 811103 = 1216655) B1216655
theorem B1220705 : Blo 539803 1220705 := bstep (se 2 (by rfl) ⟨457764, by rfl⟩ : syracuseStep 1220705 = 915529) B915529
theorem B811145 : Blo 539803 811145 := bstep (se 2 (by rfl) ⟨304179, by rfl⟩ : syracuseStep 811145 = 608359) B608359
theorem B1736873 : Blo 539803 1736873 := bstep (se 2 (by rfl) ⟨651327, by rfl⟩ : syracuseStep 1736873 = 1302655) B1302655
theorem B811487 : Blo 539803 811487 := bstep (se 1 (by rfl) ⟨608615, by rfl⟩ : syracuseStep 811487 = 1217231) B1217231
theorem B9855533 : Blo 539803 9855533 := bstep (se 3 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 9855533 = 3695825) B3695825
theorem B541275 : Blo 539803 541275 := bstep (se 1 (by rfl) ⟨405956, by rfl⟩ : syracuseStep 541275 = 811913) B811913
theorem B1368839 : Blo 539803 1368839 := bstep (se 1 (by rfl) ⟨1026629, by rfl⟩ : syracuseStep 1368839 = 2053259) B2053259
theorem B811847 : Blo 539803 811847 := bstep (se 1 (by rfl) ⟨608885, by rfl⟩ : syracuseStep 811847 = 1217771) B1217771
theorem B541631 : Blo 539803 541631 := bstep (se 1 (by rfl) ⟨406223, by rfl⟩ : syracuseStep 541631 = 812447) B812447
theorem B812009 : Blo 539803 812009 := bstep (se 2 (by rfl) ⟨304503, by rfl⟩ : syracuseStep 812009 = 609007) B609007
theorem B607387 : Blo 539803 607387 := bstep (se 1 (by rfl) ⟨455540, by rfl⟩ : syracuseStep 607387 = 911081) B911081
theorem B4924637 : Blo 539803 4924637 := bstep (se 3 (by rfl) ⟨923369, by rfl⟩ : syracuseStep 4924637 = 1846739) B1846739
theorem B812255 : Blo 539803 812255 := bstep (se 1 (by rfl) ⟨609191, by rfl⟩ : syracuseStep 812255 = 1218383) B1218383
theorem B14083303 : Blo 539803 14083303 := bstep (se 1 (by rfl) ⟨10562477, by rfl⟩ : syracuseStep 14083303 = 21124955) B21124955
theorem B3704147 : Blo 539803 3704147 := bstep (se 1 (by rfl) ⟨2778110, by rfl⟩ : syracuseStep 3704147 = 5556221) B5556221
theorem B542191 : Blo 539803 542191 := bstep (se 1 (by rfl) ⟨406643, by rfl⟩ : syracuseStep 542191 = 813287) B813287
theorem B6325897 : Blo 539803 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B812681 : Blo 539803 812681 := bstep (se 2 (by rfl) ⟨304755, by rfl⟩ : syracuseStep 812681 = 609511) B609511
theorem B812735 : Blo 539803 812735 := bstep (se 1 (by rfl) ⟨609551, by rfl⟩ : syracuseStep 812735 = 1219103) B1219103
theorem B542623 : Blo 539803 542623 := bstep (se 1 (by rfl) ⟨406967, by rfl⟩ : syracuseStep 542623 = 813935) B813935
theorem B542783 : Blo 539803 542783 := bstep (se 1 (by rfl) ⟨407087, by rfl⟩ : syracuseStep 542783 = 814175) B814175
theorem B6179003 : Blo 539803 6179003 := bstep (se 1 (by rfl) ⟨4634252, by rfl⟩ : syracuseStep 6179003 = 9268505) B9268505
theorem B813275 : Blo 539803 813275 := bstep (se 1 (by rfl) ⟨609956, by rfl⟩ : syracuseStep 813275 = 1219913) B1219913
theorem B66717989 : Blo 539803 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B813383 : Blo 539803 813383 := bstep (se 1 (by rfl) ⟨610037, by rfl⟩ : syracuseStep 813383 = 1220075) B1220075
theorem B3466135955 : Blo 539803 3466135955 := bstep (se 1 (by rfl) ⟨2599601966, by rfl⟩ : syracuseStep 3466135955 = 5199203933) B5199203933
theorem B813623 : Blo 539803 813623 := bstep (se 1 (by rfl) ⟨610217, by rfl⟩ : syracuseStep 813623 = 1220435) B1220435
theorem B5204695 : Blo 539803 5204695 := bstep (se 1 (by rfl) ⟨3903521, by rfl⟩ : syracuseStep 5204695 = 7807043) B7807043
theorem B1026857 : Blo 539803 1026857 := bstep (se 2 (by rfl) ⟨385071, by rfl⟩ : syracuseStep 1026857 = 770143) B770143
theorem B17558315 : Blo 539803 17558315 := bstep (se 1 (by rfl) ⟨13168736, by rfl⟩ : syracuseStep 17558315 = 26337473) B26337473
theorem B1829735 : Blo 539803 1829735 := bstep (se 1 (by rfl) ⟨1372301, by rfl⟩ : syracuseStep 1829735 = 2744603) B2744603
theorem B1829843 : Blo 539803 1829843 := bstep (se 1 (by rfl) ⟨1372382, by rfl⟩ : syracuseStep 1829843 = 2744765) B2744765
theorem B1829951 : Blo 539803 1829951 := bstep (se 1 (by rfl) ⟨1372463, by rfl⟩ : syracuseStep 1829951 = 2744927) B2744927
theorem B1125679 : Blo 539803 1125679 := bstep (se 1 (by rfl) ⟨844259, by rfl⟩ : syracuseStep 1125679 = 1688519) B1688519
theorem B15584561 : Blo 539803 15584561 := bstep (se 2 (by rfl) ⟨5844210, by rfl⟩ : syracuseStep 15584561 = 11688421) B11688421
theorem B2059577 : Blo 539803 2059577 := bstep (se 2 (by rfl) ⟨772341, by rfl⟩ : syracuseStep 2059577 = 1544683) B1544683
theorem B4099409 : Blo 539803 4099409 := bstep (se 2 (by rfl) ⟨1537278, by rfl⟩ : syracuseStep 4099409 = 3074557) B3074557
theorem B1216475 : Blo 539803 1216475 := bstep (se 1 (by rfl) ⟨912356, by rfl⟩ : syracuseStep 1216475 = 1824713) B1824713
theorem B6238183 : Blo 539803 6238183 := bstep (se 1 (by rfl) ⟨4678637, by rfl⟩ : syracuseStep 6238183 = 9357275) B9357275
theorem B1298425 : Blo 539803 1298425 := bstep (se 2 (by rfl) ⟨486909, by rfl⟩ : syracuseStep 1298425 = 973819) B973819
theorem B1831247 : Blo 539803 1831247 := bstep (se 1 (by rfl) ⟨1373435, by rfl⟩ : syracuseStep 1831247 = 2746871) B2746871
theorem B1905083 : Blo 539803 1905083 := bstep (se 1 (by rfl) ⟨1428812, by rfl⟩ : syracuseStep 1905083 = 2857625) B2857625
theorem B3076541 : Blo 539803 3076541 := bstep (se 3 (by rfl) ⟨576851, by rfl⟩ : syracuseStep 3076541 = 1153703) B1153703
theorem B37491173 : Blo 539803 37491173 := bstep (se 4 (by rfl) ⟨3514797, by rfl⟩ : syracuseStep 37491173 = 7029595) B7029595
theorem B684703 : Blo 539803 684703 := bstep (se 1 (by rfl) ⟨513527, by rfl⟩ : syracuseStep 684703 = 1027055) B1027055
theorem B578287 : Blo 539803 578287 := bstep (se 1 (by rfl) ⟨433715, by rfl⟩ : syracuseStep 578287 = 867431) B867431
theorem B1823687 : Blo 539803 1823687 := bstep (se 1 (by rfl) ⟨1367765, by rfl⟩ : syracuseStep 1823687 = 2735531) B2735531
theorem B29594621 : Blo 539803 29594621 := bstep (se 3 (by rfl) ⟨5548991, by rfl⟩ : syracuseStep 29594621 = 11097983) B11097983
theorem B9024641 : Blo 539803 9024641 := bstep (se 2 (by rfl) ⟨3384240, by rfl⟩ : syracuseStep 9024641 = 6768481) B6768481
theorem B7796087 : Blo 539803 7796087 := bstep (se 1 (by rfl) ⟨5847065, by rfl⟩ : syracuseStep 7796087 = 11694131) B11694131
theorem B2733587 : Blo 539803 2733587 := bstep (se 1 (by rfl) ⟨2050190, by rfl⟩ : syracuseStep 2733587 = 4100381) B4100381
theorem B15046195 : Blo 539803 15046195 := bstep (se 1 (by rfl) ⟨11284646, by rfl⟩ : syracuseStep 15046195 = 22569293) B22569293
theorem B1955411 : Blo 539803 1955411 := bstep (se 1 (by rfl) ⟨1466558, by rfl⟩ : syracuseStep 1955411 = 2933117) B2933117
theorem B9860723 : Blo 539803 9860723 := bstep (se 1 (by rfl) ⟨7395542, by rfl⟩ : syracuseStep 9860723 = 14791085) B14791085
theorem B866047 : Blo 539803 866047 := bstep (se 1 (by rfl) ⟨649535, by rfl⟩ : syracuseStep 866047 = 1299071) B1299071
theorem B26367839 : Blo 539803 26367839 := bstep (se 1 (by rfl) ⟨19775879, by rfl⟩ : syracuseStep 26367839 = 39551759) B39551759
theorem B2594699 : Blo 539803 2594699 := bstep (se 1 (by rfl) ⟨1946024, by rfl⟩ : syracuseStep 2594699 = 3892049) B3892049
theorem B3897467 : Blo 539803 3897467 := bstep (se 1 (by rfl) ⟨2923100, by rfl⟩ : syracuseStep 3897467 = 5846201) B5846201
theorem B915583 : Blo 539803 915583 := bstep (se 1 (by rfl) ⟨686687, by rfl⟩ : syracuseStep 915583 = 1373375) B1373375
theorem B5863843 : Blo 539803 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B915961 : Blo 539803 915961 := bstep (se 2 (by rfl) ⟨343485, by rfl⟩ : syracuseStep 915961 = 686971) B686971
theorem B2808361 : Blo 539803 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B2054747 : Blo 539803 2054747 := bstep (se 1 (by rfl) ⟨1541060, by rfl⟩ : syracuseStep 2054747 = 3082121) B3082121
theorem B1464923 : Blo 539803 1464923 := bstep (se 1 (by rfl) ⟨1098692, by rfl⟩ : syracuseStep 1464923 = 2197385) B2197385
theorem B1735283 : Blo 539803 1735283 := bstep (se 1 (by rfl) ⟨1301462, by rfl⟩ : syracuseStep 1735283 = 2602925) B2602925
theorem B5284943 : Blo 539803 5284943 := bstep (se 1 (by rfl) ⟨3963707, by rfl⟩ : syracuseStep 5284943 = 7927415) B7927415
theorem B1825577 : Blo 539803 1825577 := bstep (se 2 (by rfl) ⟨684591, by rfl⟩ : syracuseStep 1825577 = 1369183) B1369183
theorem B810143 : Blo 539803 810143 := bstep (se 1 (by rfl) ⟨607607, by rfl⟩ : syracuseStep 810143 = 1215215) B1215215
theorem B4111559 : Blo 539803 4111559 := bstep (se 1 (by rfl) ⟨3083669, by rfl⟩ : syracuseStep 4111559 = 6167339) B6167339
theorem B60833045 : Blo 539803 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B810287 : Blo 539803 810287 := bstep (se 1 (by rfl) ⟨607715, by rfl⟩ : syracuseStep 810287 = 1215431) B1215431
theorem B13909319 : Blo 539803 13909319 := bstep (se 1 (by rfl) ⟨10431989, by rfl⟩ : syracuseStep 13909319 = 20863979) B20863979
theorem B540007 : Blo 539803 540007 := bstep (se 1 (by rfl) ⟨405005, by rfl⟩ : syracuseStep 540007 = 810011) B810011
theorem B1826171 : Blo 539803 1826171 := bstep (se 1 (by rfl) ⟨1369628, by rfl⟩ : syracuseStep 1826171 = 2739257) B2739257
theorem B1301915 : Blo 539803 1301915 := bstep (se 1 (by rfl) ⟨976436, by rfl⟩ : syracuseStep 1301915 = 1952873) B1952873
theorem B25017761 : Blo 539803 25017761 := bstep (se 2 (by rfl) ⟨9381660, by rfl⟩ : syracuseStep 25017761 = 18763321) B18763321
theorem B12361135 : Blo 539803 12361135 := bstep (se 1 (by rfl) ⟨9270851, by rfl⟩ : syracuseStep 12361135 = 18541703) B18541703
theorem B810551 : Blo 539803 810551 := bstep (se 1 (by rfl) ⟨607913, by rfl⟩ : syracuseStep 810551 = 1215827) B1215827
theorem B540263 : Blo 539803 540263 := bstep (se 1 (by rfl) ⟨405197, by rfl⟩ : syracuseStep 540263 = 810395) B810395
theorem B2784991 : Blo 539803 2784991 := bstep (se 1 (by rfl) ⟨2088743, by rfl⟩ : syracuseStep 2784991 = 4177487) B4177487
theorem B2473703 : Blo 539803 2473703 := bstep (se 1 (by rfl) ⟨1855277, by rfl⟩ : syracuseStep 2473703 = 3710555) B3710555
theorem B3891007 : Blo 539803 3891007 := bstep (se 1 (by rfl) ⟨2918255, by rfl⟩ : syracuseStep 3891007 = 5836511) B5836511
theorem B1736615 : Blo 539803 1736615 := bstep (se 1 (by rfl) ⟨1302461, by rfl⟩ : syracuseStep 1736615 = 2604923) B2604923
theorem B540607 : Blo 539803 540607 := bstep (se 1 (by rfl) ⟨405455, by rfl⟩ : syracuseStep 540607 = 810911) B810911
theorem B5857231 : Blo 539803 5857231 := bstep (se 1 (by rfl) ⟨4392923, by rfl⟩ : syracuseStep 5857231 = 8785847) B8785847
theorem B1540127 : Blo 539803 1540127 := bstep (se 1 (by rfl) ⟨1155095, by rfl⟩ : syracuseStep 1540127 = 2310191) B2310191
theorem B540735 : Blo 539803 540735 := bstep (se 1 (by rfl) ⟨405551, by rfl⟩ : syracuseStep 540735 = 811103) B811103
theorem B540763 : Blo 539803 540763 := bstep (se 1 (by rfl) ⟨405572, by rfl⟩ : syracuseStep 540763 = 811145) B811145
theorem B1220777 : Blo 539803 1220777 := bstep (se 2 (by rfl) ⟨457791, by rfl⟩ : syracuseStep 1220777 = 915583) B915583
theorem B1220831 : Blo 539803 1220831 := bstep (se 1 (by rfl) ⟨915623, by rfl⟩ : syracuseStep 1220831 = 1831247) B1831247
theorem B1270055 : Blo 539803 1270055 := bstep (se 1 (by rfl) ⟨952541, by rfl⟩ : syracuseStep 1270055 = 1905083) B1905083
theorem B540991 : Blo 539803 540991 := bstep (se 1 (by rfl) ⟨405743, by rfl⟩ : syracuseStep 540991 = 811487) B811487
theorem B24994115 : Blo 539803 24994115 := bstep (se 1 (by rfl) ⟨18745586, by rfl⟩ : syracuseStep 24994115 = 37491173) B37491173
theorem B541231 : Blo 539803 541231 := bstep (se 1 (by rfl) ⟨405923, by rfl⟩ : syracuseStep 541231 = 811847) B811847
theorem B541339 : Blo 539803 541339 := bstep (se 1 (by rfl) ⟨406004, by rfl⟩ : syracuseStep 541339 = 812009) B812009
theorem B1221281 : Blo 539803 1221281 := bstep (se 2 (by rfl) ⟨457980, by rfl⟩ : syracuseStep 1221281 = 915961) B915961
theorem B3523295 : Blo 539803 3523295 := bstep (se 1 (by rfl) ⟨2642471, by rfl⟩ : syracuseStep 3523295 = 5284943) B5284943
theorem B3744481 : Blo 539803 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B541503 : Blo 539803 541503 := bstep (se 1 (by rfl) ⟨406127, by rfl⟩ : syracuseStep 541503 = 812255) B812255
theorem B6939593 : Blo 539803 6939593 := bstep (se 2 (by rfl) ⟨2602347, by rfl⟩ : syracuseStep 6939593 = 5204695) B5204695
theorem B771049 : Blo 539803 771049 := bstep (se 2 (by rfl) ⟨289143, by rfl⟩ : syracuseStep 771049 = 578287) B578287
theorem B1303607 : Blo 539803 1303607 := bstep (se 1 (by rfl) ⟨977705, by rfl⟩ : syracuseStep 1303607 = 1955411) B1955411
theorem B541787 : Blo 539803 541787 := bstep (se 1 (by rfl) ⟨406340, by rfl⟩ : syracuseStep 541787 = 812681) B812681
theorem B541823 : Blo 539803 541823 := bstep (se 1 (by rfl) ⟨406367, by rfl⟩ : syracuseStep 541823 = 812735) B812735
theorem B1729799 : Blo 539803 1729799 := bstep (se 1 (by rfl) ⟨1297349, by rfl⟩ : syracuseStep 1729799 = 2594699) B2594699
theorem B2598311 : Blo 539803 2598311 := bstep (se 1 (by rfl) ⟨1948733, by rfl⟩ : syracuseStep 2598311 = 3897467) B3897467
theorem B26281421 : Blo 539803 26281421 := bstep (se 3 (by rfl) ⟨4927766, by rfl⟩ : syracuseStep 26281421 = 9855533) B9855533
theorem B542183 : Blo 539803 542183 := bstep (se 1 (by rfl) ⟨406637, by rfl⟩ : syracuseStep 542183 = 813275) B813275
theorem B542255 : Blo 539803 542255 := bstep (se 1 (by rfl) ⟨406691, by rfl⟩ : syracuseStep 542255 = 813383) B813383
theorem B18777737 : Blo 539803 18777737 := bstep (se 2 (by rfl) ⟨7041651, by rfl⟩ : syracuseStep 18777737 = 14083303) B14083303
theorem B542415 : Blo 539803 542415 := bstep (se 1 (by rfl) ⟨406811, by rfl⟩ : syracuseStep 542415 = 813623) B813623
theorem B1369831 : Blo 539803 1369831 := bstep (se 1 (by rfl) ⟨1027373, by rfl⟩ : syracuseStep 1369831 = 2054747) B2054747
theorem B1500905 : Blo 539803 1500905 := bstep (se 2 (by rfl) ⟨562839, by rfl⟩ : syracuseStep 1500905 = 1125679) B1125679
theorem B1156855 : Blo 539803 1156855 := bstep (se 1 (by rfl) ⟨867641, by rfl⟩ : syracuseStep 1156855 = 1735283) B1735283
theorem B2738285 : Blo 539803 2738285 := bstep (se 3 (by rfl) ⟨513428, by rfl⟩ : syracuseStep 2738285 = 1026857) B1026857
theorem B10389707 : Blo 539803 10389707 := bstep (se 1 (by rfl) ⟨7792280, by rfl⟩ : syracuseStep 10389707 = 15584561) B15584561
theorem B3713321 : Blo 539803 3713321 := bstep (se 2 (by rfl) ⟨1392495, by rfl⟩ : syracuseStep 3713321 = 2784991) B2784991
theorem B5188009 : Blo 539803 5188009 := bstep (se 2 (by rfl) ⟨1945503, by rfl⟩ : syracuseStep 5188009 = 3891007) B3891007
theorem B1649135 : Blo 539803 1649135 := bstep (se 1 (by rfl) ⟨1236851, by rfl⟩ : syracuseStep 1649135 = 2473703) B2473703
theorem B7809641 : Blo 539803 7809641 := bstep (se 2 (by rfl) ⟨2928615, by rfl⟩ : syracuseStep 7809641 = 5857231) B5857231
theorem B1157743 : Blo 539803 1157743 := bstep (se 1 (by rfl) ⟨868307, by rfl⟩ : syracuseStep 1157743 = 1736615) B1736615
theorem B8317577 : Blo 539803 8317577 := bstep (se 2 (by rfl) ⟨3119091, by rfl⟩ : syracuseStep 8317577 = 6238183) B6238183
theorem B1731233 : Blo 539803 1731233 := bstep (se 2 (by rfl) ⟨649212, by rfl⟩ : syracuseStep 1731233 = 1298425) B1298425
theorem B813803 : Blo 539803 813803 := bstep (se 1 (by rfl) ⟨610352, by rfl⟩ : syracuseStep 813803 = 1220705) B1220705
theorem B1157915 : Blo 539803 1157915 := bstep (se 1 (by rfl) ⟨868436, by rfl⟩ : syracuseStep 1157915 = 1736873) B1736873
theorem B2051027 : Blo 539803 2051027 := bstep (se 1 (by rfl) ⟨1538270, by rfl⟩ : syracuseStep 2051027 = 3076541) B3076541
theorem B912559 : Blo 539803 912559 := bstep (se 1 (by rfl) ⟨684419, by rfl⟩ : syracuseStep 912559 = 1368839) B1368839
theorem B7818457 : Blo 539803 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B1215791 : Blo 539803 1215791 := bstep (se 1 (by rfl) ⟨911843, by rfl⟩ : syracuseStep 1215791 = 1823687) B1823687
theorem B19729747 : Blo 539803 19729747 := bstep (se 1 (by rfl) ⟨14797310, by rfl⟩ : syracuseStep 19729747 = 29594621) B29594621
theorem B6016427 : Blo 539803 6016427 := bstep (se 1 (by rfl) ⟨4512320, by rfl⟩ : syracuseStep 6016427 = 9024641) B9024641
theorem B912937 : Blo 539803 912937 := bstep (se 2 (by rfl) ⟨342351, by rfl⟩ : syracuseStep 912937 = 684703) B684703
theorem B2469431 : Blo 539803 2469431 := bstep (se 1 (by rfl) ⟨1852073, by rfl⟩ : syracuseStep 2469431 = 3704147) B3704147
theorem B5197391 : Blo 539803 5197391 := bstep (se 1 (by rfl) ⟨3898043, by rfl⟩ : syracuseStep 5197391 = 7796087) B7796087
theorem B1822391 : Blo 539803 1822391 := bstep (se 1 (by rfl) ⟨1366793, by rfl⟩ : syracuseStep 1822391 = 2733587) B2733587
theorem B6573815 : Blo 539803 6573815 := bstep (se 1 (by rfl) ⟨4930361, by rfl⟩ : syracuseStep 6573815 = 9860723) B9860723
theorem B44478659 : Blo 539803 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B1217051 : Blo 539803 1217051 := bstep (se 1 (by rfl) ⟨912788, by rfl⟩ : syracuseStep 1217051 = 1825577) B1825577
theorem B2741039 : Blo 539803 2741039 := bstep (se 1 (by rfl) ⟨2055779, by rfl⟩ : syracuseStep 2741039 = 4111559) B4111559
theorem B8434529 : Blo 539803 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B40555363 : Blo 539803 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B1373051 : Blo 539803 1373051 := bstep (se 1 (by rfl) ⟨1029788, by rfl⟩ : syracuseStep 1373051 = 2059577) B2059577
theorem B2732939 : Blo 539803 2732939 := bstep (se 1 (by rfl) ⟨2049704, by rfl⟩ : syracuseStep 2732939 = 4099409) B4099409
theorem B1217447 : Blo 539803 1217447 := bstep (se 1 (by rfl) ⟨913085, by rfl⟩ : syracuseStep 1217447 = 1826171) B1826171
theorem B3283091 : Blo 539803 3283091 := bstep (se 1 (by rfl) ⟨2462318, by rfl⟩ : syracuseStep 3283091 = 4924637) B4924637
theorem B17578559 : Blo 539803 17578559 := bstep (se 1 (by rfl) ⟨13183919, by rfl⟩ : syracuseStep 17578559 = 26367839) B26367839
theorem B4119335 : Blo 539803 4119335 := bstep (se 1 (by rfl) ⟨3089501, by rfl⟩ : syracuseStep 4119335 = 6179003) B6179003
theorem B809849 : Blo 539803 809849 := bstep (se 2 (by rfl) ⟨303693, by rfl⟩ : syracuseStep 809849 = 607387) B607387
theorem B3906461 : Blo 539803 3906461 := bstep (se 3 (by rfl) ⟨732461, by rfl⟩ : syracuseStep 3906461 = 1464923) B1464923
theorem B2310757303 : Blo 539803 2310757303 := bstep (se 1 (by rfl) ⟨1733067977, by rfl⟩ : syracuseStep 2310757303 = 3466135955) B3466135955
theorem B11705543 : Blo 539803 11705543 := bstep (se 1 (by rfl) ⟨8779157, by rfl⟩ : syracuseStep 11705543 = 17558315) B17558315
theorem B16481513 : Blo 539803 16481513 := bstep (se 2 (by rfl) ⟨6180567, by rfl⟩ : syracuseStep 16481513 = 12361135) B12361135
theorem B1219823 : Blo 539803 1219823 := bstep (se 1 (by rfl) ⟨914867, by rfl⟩ : syracuseStep 1219823 = 1829735) B1829735
theorem B1219895 : Blo 539803 1219895 := bstep (se 1 (by rfl) ⟨914921, by rfl⟩ : syracuseStep 1219895 = 1829843) B1829843
theorem B1219967 : Blo 539803 1219967 := bstep (se 1 (by rfl) ⟨914975, by rfl⟩ : syracuseStep 1219967 = 1829951) B1829951
theorem B20061593 : Blo 539803 20061593 := bstep (se 2 (by rfl) ⟨7523097, by rfl⟩ : syracuseStep 20061593 = 15046195) B15046195
theorem B540095 : Blo 539803 540095 := bstep (se 1 (by rfl) ⟨405071, by rfl⟩ : syracuseStep 540095 = 810143) B810143
theorem B540191 : Blo 539803 540191 := bstep (se 1 (by rfl) ⟨405143, by rfl⟩ : syracuseStep 540191 = 810287) B810287
theorem B9272879 : Blo 539803 9272879 := bstep (se 1 (by rfl) ⟨6954659, by rfl⟩ : syracuseStep 9272879 = 13909319) B13909319
theorem B16678507 : Blo 539803 16678507 := bstep (se 1 (by rfl) ⟨12508880, by rfl⟩ : syracuseStep 16678507 = 25017761) B25017761
theorem B867943 : Blo 539803 867943 := bstep (se 1 (by rfl) ⟨650957, by rfl⟩ : syracuseStep 867943 = 1301915) B1301915
theorem B1154729 : Blo 539803 1154729 := bstep (se 2 (by rfl) ⟨433023, by rfl⟩ : syracuseStep 1154729 = 866047) B866047
theorem B540367 : Blo 539803 540367 := bstep (se 1 (by rfl) ⟨405275, by rfl⟩ : syracuseStep 540367 = 810551) B810551
theorem B810983 : Blo 539803 810983 := bstep (se 1 (by rfl) ⟨608237, by rfl⟩ : syracuseStep 810983 = 1216475) B1216475
theorem B16662743 : Blo 539803 16662743 := bstep (se 1 (by rfl) ⟨12497057, by rfl⟩ : syracuseStep 16662743 = 24994115) B24994115
theorem B811367 : Blo 539803 811367 := bstep (se 1 (by rfl) ⟨608525, by rfl⟩ : syracuseStep 811367 = 1217051) B1217051
theorem B1827359 : Blo 539803 1827359 := bstep (se 1 (by rfl) ⟨1370519, by rfl⟩ : syracuseStep 1827359 = 2741039) B2741039
theorem B43950701 : Blo 539803 43950701 := bstep (se 3 (by rfl) ⟨8240756, by rfl⟩ : syracuseStep 43950701 = 16481513) B16481513
theorem B811631 : Blo 539803 811631 := bstep (se 1 (by rfl) ⟨608723, by rfl⟩ : syracuseStep 811631 = 1217447) B1217447
theorem B869071 : Blo 539803 869071 := bstep (se 1 (by rfl) ⟨651803, by rfl⟩ : syracuseStep 869071 = 1303607) B1303607
theorem B12518491 : Blo 539803 12518491 := bstep (se 1 (by rfl) ⟨9388868, by rfl⟩ : syracuseStep 12518491 = 18777737) B18777737
theorem B1000603 : Blo 539803 1000603 := bstep (se 1 (by rfl) ⟨750452, by rfl⟩ : syracuseStep 1000603 = 1500905) B1500905
theorem B2188727 : Blo 539803 2188727 := bstep (se 1 (by rfl) ⟨1641545, by rfl⟩ : syracuseStep 2188727 = 3283091) B3283091
theorem B1099423 : Blo 539803 1099423 := bstep (se 1 (by rfl) ⟨824567, by rfl⟩ : syracuseStep 1099423 = 1649135) B1649135
theorem B542535 : Blo 539803 542535 := bstep (se 1 (by rfl) ⟨406901, by rfl⟩ : syracuseStep 542535 = 813803) B813803
theorem B771943 : Blo 539803 771943 := bstep (se 1 (by rfl) ⟨578957, by rfl⟩ : syracuseStep 771943 = 1157915) B1157915
theorem B2746223 : Blo 539803 2746223 := bstep (se 1 (by rfl) ⟨2059667, by rfl⟩ : syracuseStep 2746223 = 4119335) B4119335
theorem B1157257 : Blo 539803 1157257 := bstep (se 2 (by rfl) ⟨433971, by rfl⟩ : syracuseStep 1157257 = 867943) B867943
theorem B813215 : Blo 539803 813215 := bstep (se 1 (by rfl) ⟨609911, by rfl⟩ : syracuseStep 813215 = 1219823) B1219823
theorem B813263 : Blo 539803 813263 := bstep (se 1 (by rfl) ⟨609947, by rfl⟩ : syracuseStep 813263 = 1219895) B1219895
theorem B813311 : Blo 539803 813311 := bstep (se 1 (by rfl) ⟨609983, by rfl⟩ : syracuseStep 813311 = 1219967) B1219967
theorem B1542473 : Blo 539803 1542473 := bstep (se 2 (by rfl) ⟨578427, by rfl⟩ : syracuseStep 1542473 = 1156855) B1156855
theorem B1214927 : Blo 539803 1214927 := bstep (se 1 (by rfl) ⟨911195, by rfl⟩ : syracuseStep 1214927 = 1822391) B1822391
theorem B1026751 : Blo 539803 1026751 := bstep (se 1 (by rfl) ⟨770063, by rfl⟩ : syracuseStep 1026751 = 1540127) B1540127
theorem B813851 : Blo 539803 813851 := bstep (se 1 (by rfl) ⟨610388, by rfl⟩ : syracuseStep 813851 = 1220777) B1220777
theorem B813887 : Blo 539803 813887 := bstep (se 1 (by rfl) ⟨610415, by rfl⟩ : syracuseStep 813887 = 1220831) B1220831
theorem B846703 : Blo 539803 846703 := bstep (se 1 (by rfl) ⟨635027, by rfl⟩ : syracuseStep 846703 = 1270055) B1270055
theorem B9395453 : Blo 539803 9395453 := bstep (se 3 (by rfl) ⟨1761647, by rfl⟩ : syracuseStep 9395453 = 3523295) B3523295
theorem B814187 : Blo 539803 814187 := bstep (se 1 (by rfl) ⟨610640, by rfl⟩ : syracuseStep 814187 = 1221281) B1221281
theorem B6917345 : Blo 539803 6917345 := bstep (se 2 (by rfl) ⟨2594004, by rfl⟩ : syracuseStep 6917345 = 5188009) B5188009
theorem B5623019 : Blo 539803 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B1821959 : Blo 539803 1821959 := bstep (se 1 (by rfl) ⟨1366469, by rfl⟩ : syracuseStep 1821959 = 2732939) B2732939
theorem B1732207 : Blo 539803 1732207 := bstep (se 1 (by rfl) ⟨1299155, by rfl⟩ : syracuseStep 1732207 = 2598311) B2598311
theorem B4992641 : Blo 539803 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B1028065 : Blo 539803 1028065 := bstep (se 2 (by rfl) ⟨385524, by rfl⟩ : syracuseStep 1028065 = 771049) B771049
theorem B6926471 : Blo 539803 6926471 := bstep (se 1 (by rfl) ⟨5194853, by rfl⟩ : syracuseStep 6926471 = 10389707) B10389707
theorem B1216745 : Blo 539803 1216745 := bstep (se 2 (by rfl) ⟨456279, by rfl⟩ : syracuseStep 1216745 = 912559) B912559
theorem B10424609 : Blo 539803 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B22180205 : Blo 539803 22180205 := bstep (se 3 (by rfl) ⟨4158788, by rfl⟩ : syracuseStep 22180205 = 8317577) B8317577
theorem B11719039 : Blo 539803 11719039 := bstep (se 1 (by rfl) ⟨8789279, by rfl⟩ : syracuseStep 11719039 = 17578559) B17578559
theorem B5206427 : Blo 539803 5206427 := bstep (se 1 (by rfl) ⟨3904820, by rfl⟩ : syracuseStep 5206427 = 7809641) B7809641
theorem B4616621 : Blo 539803 4616621 := bstep (se 3 (by rfl) ⟨865616, by rfl⟩ : syracuseStep 4616621 = 1731233) B1731233
theorem B1217249 : Blo 539803 1217249 := bstep (se 2 (by rfl) ⟨456468, by rfl⟩ : syracuseStep 1217249 = 912937) B912937
theorem B7803695 : Blo 539803 7803695 := bstep (se 1 (by rfl) ⟨5852771, by rfl⟩ : syracuseStep 7803695 = 11705543) B11705543
theorem B22238009 : Blo 539803 22238009 := bstep (se 2 (by rfl) ⟨8339253, by rfl⟩ : syracuseStep 22238009 = 16678507) B16678507
theorem B13374395 : Blo 539803 13374395 := bstep (se 1 (by rfl) ⟨10030796, by rfl⟩ : syracuseStep 13374395 = 20061593) B20061593
theorem B4010951 : Blo 539803 4010951 := bstep (se 1 (by rfl) ⟨3008213, by rfl⟩ : syracuseStep 4010951 = 6016427) B6016427
theorem B6181919 : Blo 539803 6181919 := bstep (se 1 (by rfl) ⟨4636439, by rfl⟩ : syracuseStep 6181919 = 9272879) B9272879
theorem B29652439 : Blo 539803 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B6174629 : Blo 539803 6174629 := bstep (se 4 (by rfl) ⟨578871, by rfl⟩ : syracuseStep 6174629 = 1157743) B1157743
theorem B915367 : Blo 539803 915367 := bstep (se 1 (by rfl) ⟨686525, by rfl⟩ : syracuseStep 915367 = 1373051) B1373051
theorem B4626395 : Blo 539803 4626395 := bstep (se 1 (by rfl) ⟨3469796, by rfl⟩ : syracuseStep 4626395 = 6939593) B6939593
theorem B9902189 : Blo 539803 9902189 := bstep (se 3 (by rfl) ⟨1856660, by rfl⟩ : syracuseStep 9902189 = 3713321) B3713321
theorem B1153199 : Blo 539803 1153199 := bstep (se 1 (by rfl) ⟨864899, by rfl⟩ : syracuseStep 1153199 = 1729799) B1729799
theorem B17520947 : Blo 539803 17520947 := bstep (se 1 (by rfl) ⟨13140710, by rfl⟩ : syracuseStep 17520947 = 26281421) B26281421
theorem B54073817 : Blo 539803 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B3081009737 : Blo 539803 3081009737 := bstep (se 2 (by rfl) ⟨1155378651, by rfl⟩ : syracuseStep 3081009737 = 2310757303) B2310757303
theorem B1825523 : Blo 539803 1825523 := bstep (se 1 (by rfl) ⟨1369142, by rfl⟩ : syracuseStep 1825523 = 2738285) B2738285
theorem B105225317 : Blo 539803 105225317 := bstep (se 4 (by rfl) ⟨9864873, by rfl⟩ : syracuseStep 105225317 = 19729747) B19729747
theorem B539899 : Blo 539803 539899 := bstep (se 1 (by rfl) ⟨404924, by rfl⟩ : syracuseStep 539899 = 809849) B809849
theorem B2604307 : Blo 539803 2604307 := bstep (se 1 (by rfl) ⟨1953230, by rfl⟩ : syracuseStep 2604307 = 3906461) B3906461
theorem B1367351 : Blo 539803 1367351 := bstep (se 1 (by rfl) ⟨1025513, by rfl⟩ : syracuseStep 1367351 = 2051027) B2051027
theorem B810527 : Blo 539803 810527 := bstep (se 1 (by rfl) ⟨607895, by rfl⟩ : syracuseStep 810527 = 1215791) B1215791
theorem B1826441 : Blo 539803 1826441 := bstep (se 2 (by rfl) ⟨684915, by rfl⟩ : syracuseStep 1826441 = 1369831) B1369831
theorem B1646287 : Blo 539803 1646287 := bstep (se 1 (by rfl) ⟨1234715, by rfl⟩ : syracuseStep 1646287 = 2469431) B2469431
theorem B3464927 : Blo 539803 3464927 := bstep (se 1 (by rfl) ⟨2598695, by rfl⟩ : syracuseStep 3464927 = 5197391) B5197391
theorem B769819 : Blo 539803 769819 := bstep (se 1 (by rfl) ⟨577364, by rfl⟩ : syracuseStep 769819 = 1154729) B1154729
theorem B4382543 : Blo 539803 4382543 := bstep (se 1 (by rfl) ⟨3286907, by rfl⟩ : syracuseStep 4382543 = 6573815) B6573815
theorem B540655 : Blo 539803 540655 := bstep (se 1 (by rfl) ⟨405491, by rfl⟩ : syracuseStep 540655 = 810983) B810983
theorem B11108495 : Blo 539803 11108495 := bstep (se 1 (by rfl) ⟨8331371, by rfl⟩ : syracuseStep 11108495 = 16662743) B16662743
theorem B811163 : Blo 539803 811163 := bstep (se 1 (by rfl) ⟨608372, by rfl⟩ : syracuseStep 811163 = 1216745) B1216745
theorem B540911 : Blo 539803 540911 := bstep (se 1 (by rfl) ⟨405683, by rfl⟩ : syracuseStep 540911 = 811367) B811367
theorem B14786803 : Blo 539803 14786803 := bstep (se 1 (by rfl) ⟨11090102, by rfl⟩ : syracuseStep 14786803 = 22180205) B22180205
theorem B541087 : Blo 539803 541087 := bstep (se 1 (by rfl) ⟨405815, by rfl⟩ : syracuseStep 541087 = 811631) B811631
theorem B811499 : Blo 539803 811499 := bstep (se 1 (by rfl) ⟨608624, by rfl⟩ : syracuseStep 811499 = 1217249) B1217249
theorem B5202463 : Blo 539803 5202463 := bstep (se 1 (by rfl) ⟨3901847, by rfl⟩ : syracuseStep 5202463 = 7803695) B7803695
theorem B4121279 : Blo 539803 4121279 := bstep (se 1 (by rfl) ⟨3090959, by rfl⟩ : syracuseStep 4121279 = 6181919) B6181919
theorem B1369001 : Blo 539803 1369001 := bstep (se 2 (by rfl) ⟨513375, by rfl⟩ : syracuseStep 1369001 = 1026751) B1026751
theorem B1459151 : Blo 539803 1459151 := bstep (se 1 (by rfl) ⟨1094363, by rfl⟩ : syracuseStep 1459151 = 2188727) B2188727
theorem B542143 : Blo 539803 542143 := bstep (se 1 (by rfl) ⟨406607, by rfl⟩ : syracuseStep 542143 = 813215) B813215
theorem B542175 : Blo 539803 542175 := bstep (se 1 (by rfl) ⟨406631, by rfl⟩ : syracuseStep 542175 = 813263) B813263
theorem B542207 : Blo 539803 542207 := bstep (se 1 (by rfl) ⟨406655, by rfl⟩ : syracuseStep 542207 = 813311) B813311
theorem B542567 : Blo 539803 542567 := bstep (se 1 (by rfl) ⟨406925, by rfl⟩ : syracuseStep 542567 = 813851) B813851
theorem B542591 : Blo 539803 542591 := bstep (se 1 (by rfl) ⟨406943, by rfl⟩ : syracuseStep 542591 = 813887) B813887
theorem B4515749 : Blo 539803 4515749 := bstep (se 4 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 4515749 = 846703) B846703
theorem B39536585 : Blo 539803 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B70150211 : Blo 539803 70150211 := bstep (se 1 (by rfl) ⟨52612658, by rfl⟩ : syracuseStep 70150211 = 105225317) B105225317
theorem B542791 : Blo 539803 542791 := bstep (se 1 (by rfl) ⟨407093, by rfl⟩ : syracuseStep 542791 = 814187) B814187
theorem B1214639 : Blo 539803 1214639 := bstep (se 1 (by rfl) ⟨910979, by rfl⟩ : syracuseStep 1214639 = 1821959) B1821959
theorem B911567 : Blo 539803 911567 := bstep (se 1 (by rfl) ⟨683675, by rfl⟩ : syracuseStep 911567 = 1367351) B1367351
theorem B1026425 : Blo 539803 1026425 := bstep (se 2 (by rfl) ⟨384909, by rfl⟩ : syracuseStep 1026425 = 769819) B769819
theorem B3328427 : Blo 539803 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B1370753 : Blo 539803 1370753 := bstep (se 2 (by rfl) ⟨514032, by rfl⟩ : syracuseStep 1370753 = 1028065) B1028065
theorem B1543009 : Blo 539803 1543009 := bstep (se 2 (by rfl) ⟨578628, by rfl⟩ : syracuseStep 1543009 = 1157257) B1157257
theorem B6949739 : Blo 539803 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B15625385 : Blo 539803 15625385 := bstep (se 2 (by rfl) ⟨5859519, by rfl⟩ : syracuseStep 15625385 = 11719039) B11719039
theorem B8916263 : Blo 539803 8916263 := bstep (se 1 (by rfl) ⟨6687197, by rfl⟩ : syracuseStep 8916263 = 13374395) B13374395
theorem B2673967 : Blo 539803 2673967 := bstep (se 1 (by rfl) ⟨2005475, by rfl⟩ : syracuseStep 2673967 = 4010951) B4010951
theorem B5336549 : Blo 539803 5336549 := bstep (se 4 (by rfl) ⟨500301, by rfl⟩ : syracuseStep 5336549 = 1000603) B1000603
theorem B1158761 : Blo 539803 1158761 := bstep (se 2 (by rfl) ⟨434535, by rfl⟩ : syracuseStep 1158761 = 869071) B869071
theorem B1830815 : Blo 539803 1830815 := bstep (se 1 (by rfl) ⟨1373111, by rfl⟩ : syracuseStep 1830815 = 2746223) B2746223
theorem B4116419 : Blo 539803 4116419 := bstep (se 1 (by rfl) ⟨3087314, by rfl⟩ : syracuseStep 4116419 = 6174629) B6174629
theorem B3084263 : Blo 539803 3084263 := bstep (se 1 (by rfl) ⟨2313197, by rfl⟩ : syracuseStep 3084263 = 4626395) B4626395
theorem B16691321 : Blo 539803 16691321 := bstep (se 2 (by rfl) ⟨6259245, by rfl⟩ : syracuseStep 16691321 = 12518491) B12518491
theorem B1028315 : Blo 539803 1028315 := bstep (se 1 (by rfl) ⟨771236, by rfl⟩ : syracuseStep 1028315 = 1542473) B1542473
theorem B36049211 : Blo 539803 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B1217015 : Blo 539803 1217015 := bstep (se 1 (by rfl) ⟨912761, by rfl⟩ : syracuseStep 1217015 = 1825523) B1825523
theorem B3748679 : Blo 539803 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B6263635 : Blo 539803 6263635 := bstep (se 1 (by rfl) ⟨4697726, by rfl⟩ : syracuseStep 6263635 = 9395453) B9395453
theorem B11686781 : Blo 539803 11686781 := bstep (se 3 (by rfl) ⟨2191271, by rfl⟩ : syracuseStep 11686781 = 4382543) B4382543
theorem B1217627 : Blo 539803 1217627 := bstep (se 1 (by rfl) ⟨913220, by rfl⟩ : syracuseStep 1217627 = 1826441) B1826441
theorem B1029257 : Blo 539803 1029257 := bstep (se 2 (by rfl) ⟨385971, by rfl⟩ : syracuseStep 1029257 = 771943) B771943
theorem B4617647 : Blo 539803 4617647 := bstep (se 1 (by rfl) ⟨3463235, by rfl⟩ : syracuseStep 4617647 = 6926471) B6926471
theorem B3470951 : Blo 539803 3470951 := bstep (se 1 (by rfl) ⟨2603213, by rfl⟩ : syracuseStep 3470951 = 5206427) B5206427
theorem B3077747 : Blo 539803 3077747 := bstep (se 1 (by rfl) ⟨2308310, by rfl⟩ : syracuseStep 3077747 = 4616621) B4616621
theorem B1218239 : Blo 539803 1218239 := bstep (se 1 (by rfl) ⟨913679, by rfl⟩ : syracuseStep 1218239 = 1827359) B1827359
theorem B29300467 : Blo 539803 29300467 := bstep (se 1 (by rfl) ⟨21975350, by rfl⟩ : syracuseStep 29300467 = 43950701) B43950701
theorem B14825339 : Blo 539803 14825339 := bstep (se 1 (by rfl) ⟨11119004, by rfl⟩ : syracuseStep 14825339 = 22238009) B22238009
theorem B5863589 : Blo 539803 5863589 := bstep (se 4 (by rfl) ⟨549711, by rfl⟩ : syracuseStep 5863589 = 1099423) B1099423
theorem B8780197 : Blo 539803 8780197 := bstep (se 4 (by rfl) ⟨823143, by rfl⟩ : syracuseStep 8780197 = 1646287) B1646287
theorem B6601459 : Blo 539803 6601459 := bstep (se 1 (by rfl) ⟨4951094, by rfl⟩ : syracuseStep 6601459 = 9902189) B9902189
theorem B768799 : Blo 539803 768799 := bstep (se 1 (by rfl) ⟨576599, by rfl⟩ : syracuseStep 768799 = 1153199) B1153199
theorem B8216025965 : Blo 539803 8216025965 := bstep (se 3 (by rfl) ⟨1540504868, by rfl⟩ : syracuseStep 8216025965 = 3081009737) B3081009737
theorem B11680631 : Blo 539803 11680631 := bstep (se 1 (by rfl) ⟨8760473, by rfl⟩ : syracuseStep 11680631 = 17520947) B17520947
theorem B809951 : Blo 539803 809951 := bstep (se 1 (by rfl) ⟨607463, by rfl⟩ : syracuseStep 809951 = 1214927) B1214927
theorem B3472409 : Blo 539803 3472409 := bstep (se 2 (by rfl) ⟨1302153, by rfl⟩ : syracuseStep 3472409 = 2604307) B2604307
theorem B2309609 : Blo 539803 2309609 := bstep (se 2 (by rfl) ⟨866103, by rfl⟩ : syracuseStep 2309609 = 1732207) B1732207
theorem B4611563 : Blo 539803 4611563 := bstep (se 1 (by rfl) ⟨3458672, by rfl⟩ : syracuseStep 4611563 = 6917345) B6917345
theorem B540351 : Blo 539803 540351 := bstep (se 1 (by rfl) ⟨405263, by rfl⟩ : syracuseStep 540351 = 810527) B810527
theorem B2309951 : Blo 539803 2309951 := bstep (se 1 (by rfl) ⟨1732463, by rfl⟩ : syracuseStep 2309951 = 3464927) B3464927
theorem B1220489 : Blo 539803 1220489 := bstep (se 2 (by rfl) ⟨457683, by rfl⟩ : syracuseStep 1220489 = 915367) B915367
theorem B7405663 : Blo 539803 7405663 := bstep (se 1 (by rfl) ⟨5554247, by rfl⟩ : syracuseStep 7405663 = 11108495) B11108495
theorem B540775 : Blo 539803 540775 := bstep (se 1 (by rfl) ⟨405581, by rfl⟩ : syracuseStep 540775 = 811163) B811163
theorem B540999 : Blo 539803 540999 := bstep (se 1 (by rfl) ⟨405749, by rfl⟩ : syracuseStep 540999 = 811499) B811499
theorem B811343 : Blo 539803 811343 := bstep (se 1 (by rfl) ⟨608507, by rfl⟩ : syracuseStep 811343 = 1217015) B1217015
theorem B2499119 : Blo 539803 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B11706929 : Blo 539803 11706929 := bstep (se 2 (by rfl) ⟨4390098, by rfl⟩ : syracuseStep 11706929 = 8780197) B8780197
theorem B7791187 : Blo 539803 7791187 := bstep (se 1 (by rfl) ⟨5843390, by rfl⟩ : syracuseStep 7791187 = 11686781) B11686781
theorem B811751 : Blo 539803 811751 := bstep (se 1 (by rfl) ⟨608813, by rfl⟩ : syracuseStep 811751 = 1217627) B1217627
theorem B1025065 : Blo 539803 1025065 := bstep (se 2 (by rfl) ⟨384399, by rfl⟩ : syracuseStep 1025065 = 768799) B768799
theorem B812159 : Blo 539803 812159 := bstep (se 1 (by rfl) ⟨609119, by rfl⟩ : syracuseStep 812159 = 1218239) B1218239
theorem B2057345 : Blo 539803 2057345 := bstep (se 2 (by rfl) ⟨771504, by rfl⟩ : syracuseStep 2057345 = 1543009) B1543009
theorem B3909059 : Blo 539803 3909059 := bstep (se 1 (by rfl) ⟨2931794, by rfl⟩ : syracuseStep 3909059 = 5863589) B5863589
theorem B607711 : Blo 539803 607711 := bstep (se 1 (by rfl) ⟨455783, by rfl⟩ : syracuseStep 607711 = 911567) B911567
theorem B3565289 : Blo 539803 3565289 := bstep (se 2 (by rfl) ⟨1336983, by rfl⟩ : syracuseStep 3565289 = 2673967) B2673967
theorem B3557699 : Blo 539803 3557699 := bstep (se 1 (by rfl) ⟨2668274, by rfl⟩ : syracuseStep 3557699 = 5336549) B5336549
theorem B3074375 : Blo 539803 3074375 := bstep (se 1 (by rfl) ⟨2305781, by rfl⟩ : syracuseStep 3074375 = 4611563) B4611563
theorem B772507 : Blo 539803 772507 := bstep (se 1 (by rfl) ⟨579380, by rfl⟩ : syracuseStep 772507 = 1158761) B1158761
theorem B813659 : Blo 539803 813659 := bstep (se 1 (by rfl) ⟨610244, by rfl⟩ : syracuseStep 813659 = 1220489) B1220489
theorem B9259757 : Blo 539803 9259757 := bstep (se 3 (by rfl) ⟨1736204, by rfl⟩ : syracuseStep 9259757 = 3472409) B3472409
theorem B11127547 : Blo 539803 11127547 := bstep (se 1 (by rfl) ⟨8345660, by rfl⟩ : syracuseStep 11127547 = 16691321) B16691321
theorem B2747519 : Blo 539803 2747519 := bstep (se 1 (by rfl) ⟨2060639, by rfl⟩ : syracuseStep 2747519 = 4121279) B4121279
theorem B912667 : Blo 539803 912667 := bstep (se 1 (by rfl) ⟨684500, by rfl⟩ : syracuseStep 912667 = 1369001) B1369001
theorem B8801945 : Blo 539803 8801945 := bstep (se 2 (by rfl) ⟨3300729, by rfl⟩ : syracuseStep 8801945 = 6601459) B6601459
theorem B2313967 : Blo 539803 2313967 := bstep (se 1 (by rfl) ⟨1735475, by rfl⟩ : syracuseStep 2313967 = 3470951) B3470951
theorem B2051831 : Blo 539803 2051831 := bstep (se 1 (by rfl) ⟨1538873, by rfl⟩ : syracuseStep 2051831 = 3077747) B3077747
theorem B8351513 : Blo 539803 8351513 := bstep (se 2 (by rfl) ⟨3131817, by rfl⟩ : syracuseStep 8351513 = 6263635) B6263635
theorem B9883559 : Blo 539803 9883559 := bstep (se 1 (by rfl) ⟨7412669, by rfl⟩ : syracuseStep 9883559 = 14825339) B14825339
theorem B3010499 : Blo 539803 3010499 := bstep (se 1 (by rfl) ⟨2257874, by rfl⟩ : syracuseStep 3010499 = 4515749) B4515749
theorem B26357723 : Blo 539803 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B684283 : Blo 539803 684283 := bstep (se 1 (by rfl) ⟨513212, by rfl⟩ : syracuseStep 684283 = 1026425) B1026425
theorem B913835 : Blo 539803 913835 := bstep (se 1 (by rfl) ⟨685376, by rfl⟩ : syracuseStep 913835 = 1370753) B1370753
theorem B4633159 : Blo 539803 4633159 := bstep (se 1 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 4633159 = 6949739) B6949739
theorem B7787087 : Blo 539803 7787087 := bstep (se 1 (by rfl) ⟨5840315, by rfl⟩ : syracuseStep 7787087 = 11680631) B11680631
theorem B10416923 : Blo 539803 10416923 := bstep (se 1 (by rfl) ⟨7812692, by rfl⟩ : syracuseStep 10416923 = 15625385) B15625385
theorem B5944175 : Blo 539803 5944175 := bstep (se 1 (by rfl) ⟨4458131, by rfl⟩ : syracuseStep 5944175 = 8916263) B8916263
theorem B24032807 : Blo 539803 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B19715737 : Blo 539803 19715737 := bstep (se 2 (by rfl) ⟨7393401, by rfl⟩ : syracuseStep 19715737 = 14786803) B14786803
theorem B2742173 : Blo 539803 2742173 := bstep (se 3 (by rfl) ⟨514157, by rfl⟩ : syracuseStep 2742173 = 1028315) B1028315
theorem B972767 : Blo 539803 972767 := bstep (se 1 (by rfl) ⟨729575, by rfl⟩ : syracuseStep 972767 = 1459151) B1459151
theorem B6936617 : Blo 539803 6936617 := bstep (se 2 (by rfl) ⟨2601231, by rfl⟩ : syracuseStep 6936617 = 5202463) B5202463
theorem B686171 : Blo 539803 686171 := bstep (se 1 (by rfl) ⟨514628, by rfl⟩ : syracuseStep 686171 = 1029257) B1029257
theorem B3078431 : Blo 539803 3078431 := bstep (se 1 (by rfl) ⟨2308823, by rfl⟩ : syracuseStep 3078431 = 4617647) B4617647
theorem B46766807 : Blo 539803 46766807 := bstep (se 1 (by rfl) ⟨35075105, by rfl⟩ : syracuseStep 46766807 = 70150211) B70150211
theorem B809759 : Blo 539803 809759 := bstep (se 1 (by rfl) ⟨607319, by rfl⟩ : syracuseStep 809759 = 1214639) B1214639
theorem B2218951 : Blo 539803 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B5477350643 : Blo 539803 5477350643 := bstep (se 1 (by rfl) ⟨4108012982, by rfl⟩ : syracuseStep 5477350643 = 8216025965) B8216025965
theorem B539967 : Blo 539803 539967 := bstep (se 1 (by rfl) ⟨404975, by rfl⟩ : syracuseStep 539967 = 809951) B809951
theorem B39067289 : Blo 539803 39067289 := bstep (se 2 (by rfl) ⟨14650233, by rfl⟩ : syracuseStep 39067289 = 29300467) B29300467
theorem B1539739 : Blo 539803 1539739 := bstep (se 1 (by rfl) ⟨1154804, by rfl⟩ : syracuseStep 1539739 = 2309609) B2309609
theorem B1539967 : Blo 539803 1539967 := bstep (se 1 (by rfl) ⟨1154975, by rfl⟩ : syracuseStep 1539967 = 2309951) B2309951
theorem B1220543 : Blo 539803 1220543 := bstep (se 1 (by rfl) ⟨915407, by rfl⟩ : syracuseStep 1220543 = 1830815) B1830815
theorem B2744279 : Blo 539803 2744279 := bstep (se 1 (by rfl) ⟨2058209, by rfl⟩ : syracuseStep 2744279 = 4116419) B4116419
theorem B2056175 : Blo 539803 2056175 := bstep (se 1 (by rfl) ⟨1542131, by rfl⟩ : syracuseStep 2056175 = 3084263) B3084263
theorem B540895 : Blo 539803 540895 := bstep (se 1 (by rfl) ⟨405671, by rfl⟩ : syracuseStep 540895 = 811343) B811343
theorem B541167 : Blo 539803 541167 := bstep (se 1 (by rfl) ⟨405875, by rfl⟩ : syracuseStep 541167 = 811751) B811751
theorem B541439 : Blo 539803 541439 := bstep (se 1 (by rfl) ⟨406079, by rfl⟩ : syracuseStep 541439 = 812159) B812159
theorem B6177545 : Blo 539803 6177545 := bstep (se 2 (by rfl) ⟨2316579, by rfl⟩ : syracuseStep 6177545 = 4633159) B4633159
theorem B10388249 : Blo 539803 10388249 := bstep (se 2 (by rfl) ⟨3895593, by rfl⟩ : syracuseStep 10388249 = 7791187) B7791187
theorem B2606039 : Blo 539803 2606039 := bstep (se 1 (by rfl) ⟨1954529, by rfl⟩ : syracuseStep 2606039 = 3909059) B3909059
theorem B14836729 : Blo 539803 14836729 := bstep (se 2 (by rfl) ⟨5563773, by rfl⟩ : syracuseStep 14836729 = 11127547) B11127547
theorem B2376859 : Blo 539803 2376859 := bstep (se 1 (by rfl) ⟨1782644, by rfl⟩ : syracuseStep 2376859 = 3565289) B3565289
theorem B2958601 : Blo 539803 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B1828115 : Blo 539803 1828115 := bstep (se 1 (by rfl) ⟨1371086, by rfl⟩ : syracuseStep 1828115 = 2742173) B2742173
theorem B2049583 : Blo 539803 2049583 := bstep (se 1 (by rfl) ⟨1537187, by rfl⟩ : syracuseStep 2049583 = 3074375) B3074375
theorem B542439 : Blo 539803 542439 := bstep (se 1 (by rfl) ⟨406829, by rfl⟩ : syracuseStep 542439 = 813659) B813659
theorem B26044859 : Blo 539803 26044859 := bstep (se 1 (by rfl) ⟨19533644, by rfl⟩ : syracuseStep 26044859 = 39067289) B39067289
theorem B5867963 : Blo 539803 5867963 := bstep (se 1 (by rfl) ⟨4400972, by rfl⟩ : syracuseStep 5867963 = 8801945) B8801945
theorem B6589039 : Blo 539803 6589039 := bstep (se 1 (by rfl) ⟨4941779, by rfl⟩ : syracuseStep 6589039 = 9883559) B9883559
theorem B813695 : Blo 539803 813695 := bstep (se 1 (by rfl) ⟨610271, by rfl⟩ : syracuseStep 813695 = 1220543) B1220543
theorem B1829519 : Blo 539803 1829519 := bstep (se 1 (by rfl) ⟨1372139, by rfl⟩ : syracuseStep 1829519 = 2744279) B2744279
theorem B1370783 : Blo 539803 1370783 := bstep (se 1 (by rfl) ⟨1028087, by rfl⟩ : syracuseStep 1370783 = 2056175) B2056175
theorem B9874217 : Blo 539803 9874217 := bstep (se 2 (by rfl) ⟨3702831, by rfl⟩ : syracuseStep 9874217 = 7405663) B7405663
theorem B1829789 : Blo 539803 1829789 := bstep (se 3 (by rfl) ⟨343085, by rfl⟩ : syracuseStep 1829789 = 686171) B686171
theorem B609223 : Blo 539803 609223 := bstep (se 1 (by rfl) ⟨456917, by rfl⟩ : syracuseStep 609223 = 913835) B913835
theorem B912377 : Blo 539803 912377 := bstep (se 2 (by rfl) ⟨342141, by rfl⟩ : syracuseStep 912377 = 684283) B684283
theorem B1666079 : Blo 539803 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B1371563 : Blo 539803 1371563 := bstep (se 1 (by rfl) ⟨1028672, by rfl⟩ : syracuseStep 1371563 = 2057345) B2057345
theorem B4624411 : Blo 539803 4624411 := bstep (se 1 (by rfl) ⟨3468308, by rfl⟩ : syracuseStep 4624411 = 6936617) B6936617
theorem B2052287 : Blo 539803 2052287 := bstep (se 1 (by rfl) ⟨1539215, by rfl⟩ : syracuseStep 2052287 = 3078431) B3078431
theorem B2371799 : Blo 539803 2371799 := bstep (se 1 (by rfl) ⟨1778849, by rfl⟩ : syracuseStep 2371799 = 3557699) B3557699
theorem B1216889 : Blo 539803 1216889 := bstep (se 2 (by rfl) ⟨456333, by rfl⟩ : syracuseStep 1216889 = 912667) B912667
theorem B6173171 : Blo 539803 6173171 := bstep (se 1 (by rfl) ⟨4629878, by rfl⟩ : syracuseStep 6173171 = 9259757) B9259757
theorem B1831679 : Blo 539803 1831679 := bstep (se 1 (by rfl) ⟨1373759, by rfl⟩ : syracuseStep 1831679 = 2747519) B2747519
theorem B2052985 : Blo 539803 2052985 := bstep (se 2 (by rfl) ⟨769869, by rfl⟩ : syracuseStep 2052985 = 1539739) B1539739
theorem B3085289 : Blo 539803 3085289 := bstep (se 2 (by rfl) ⟨1156983, by rfl⟩ : syracuseStep 3085289 = 2313967) B2313967
theorem B2053289 : Blo 539803 2053289 := bstep (se 2 (by rfl) ⟨769983, by rfl⟩ : syracuseStep 2053289 = 1539967) B1539967
theorem B5567675 : Blo 539803 5567675 := bstep (se 1 (by rfl) ⟨4175756, by rfl⟩ : syracuseStep 5567675 = 8351513) B8351513
theorem B2594045 : Blo 539803 2594045 := bstep (se 3 (by rfl) ⟨486383, by rfl⟩ : syracuseStep 2594045 = 972767) B972767
theorem B7804619 : Blo 539803 7804619 := bstep (se 1 (by rfl) ⟨5853464, by rfl⟩ : syracuseStep 7804619 = 11706929) B11706929
theorem B5191391 : Blo 539803 5191391 := bstep (se 1 (by rfl) ⟨3893543, by rfl⟩ : syracuseStep 5191391 = 7787087) B7787087
theorem B6944615 : Blo 539803 6944615 := bstep (se 1 (by rfl) ⟨5208461, by rfl⟩ : syracuseStep 6944615 = 10416923) B10416923
theorem B1030009 : Blo 539803 1030009 := bstep (se 2 (by rfl) ⟨386253, by rfl⟩ : syracuseStep 1030009 = 772507) B772507
theorem B3962783 : Blo 539803 3962783 := bstep (se 1 (by rfl) ⟨2972087, by rfl⟩ : syracuseStep 3962783 = 5944175) B5944175
theorem B16021871 : Blo 539803 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B1366753 : Blo 539803 1366753 := bstep (se 2 (by rfl) ⟨512532, by rfl⟩ : syracuseStep 1366753 = 1025065) B1025065
theorem B31177871 : Blo 539803 31177871 := bstep (se 1 (by rfl) ⟨23383403, by rfl⟩ : syracuseStep 31177871 = 46766807) B46766807
theorem B539839 : Blo 539803 539839 := bstep (se 1 (by rfl) ⟨404879, by rfl⟩ : syracuseStep 539839 = 809759) B809759
theorem B810281 : Blo 539803 810281 := bstep (se 2 (by rfl) ⟨303855, by rfl⟩ : syracuseStep 810281 = 607711) B607711
theorem B3651567095 : Blo 539803 3651567095 := bstep (se 1 (by rfl) ⟨2738675321, by rfl⟩ : syracuseStep 3651567095 = 5477350643) B5477350643
theorem B26287649 : Blo 539803 26287649 := bstep (se 2 (by rfl) ⟨9857868, by rfl⟩ : syracuseStep 26287649 = 19715737) B19715737
theorem B1367887 : Blo 539803 1367887 := bstep (se 1 (by rfl) ⟨1025915, by rfl⟩ : syracuseStep 1367887 = 2051831) B2051831
theorem B2006999 : Blo 539803 2006999 := bstep (se 1 (by rfl) ⟨1505249, by rfl⟩ : syracuseStep 2006999 = 3010499) B3010499
theorem B17571815 : Blo 539803 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B1368191 : Blo 539803 1368191 := bstep (se 1 (by rfl) ⟨1026143, by rfl⟩ : syracuseStep 1368191 = 2052287) B2052287
theorem B811259 : Blo 539803 811259 := bstep (se 1 (by rfl) ⟨608444, by rfl⟩ : syracuseStep 811259 = 1216889) B1216889
theorem B1221119 : Blo 539803 1221119 := bstep (se 1 (by rfl) ⟨915839, by rfl⟩ : syracuseStep 1221119 = 1831679) B1831679
theorem B6324797 : Blo 539803 6324797 := bstep (se 3 (by rfl) ⟨1185899, by rfl⟩ : syracuseStep 6324797 = 2371799) B2371799
theorem B1737359 : Blo 539803 1737359 := bstep (se 1 (by rfl) ⟨1303019, by rfl⟩ : syracuseStep 1737359 = 2606039) B2606039
theorem B2056859 : Blo 539803 2056859 := bstep (se 1 (by rfl) ⟨1542644, by rfl⟩ : syracuseStep 2056859 = 3085289) B3085289
theorem B1368859 : Blo 539803 1368859 := bstep (se 1 (by rfl) ⟨1026644, by rfl⟩ : syracuseStep 1368859 = 2053289) B2053289
theorem B1729363 : Blo 539803 1729363 := bstep (se 1 (by rfl) ⟨1297022, by rfl⟩ : syracuseStep 1729363 = 2594045) B2594045
theorem B5203079 : Blo 539803 5203079 := bstep (se 1 (by rfl) ⟨3902309, by rfl⟩ : syracuseStep 5203079 = 7804619) B7804619
theorem B69452957 : Blo 539803 69452957 := bstep (se 3 (by rfl) ⟨13022429, by rfl⟩ : syracuseStep 69452957 = 26044859) B26044859
theorem B2737313 : Blo 539803 2737313 := bstep (se 2 (by rfl) ⟨1026492, by rfl⟩ : syracuseStep 2737313 = 2052985) B2052985
theorem B4629743 : Blo 539803 4629743 := bstep (se 1 (by rfl) ⟨3472307, by rfl⟩ : syracuseStep 4629743 = 6944615) B6944615
theorem B812297 : Blo 539803 812297 := bstep (se 2 (by rfl) ⟨304611, by rfl⟩ : syracuseStep 812297 = 609223) B609223
theorem B542463 : Blo 539803 542463 := bstep (se 1 (by rfl) ⟨406847, by rfl⟩ : syracuseStep 542463 = 813695) B813695
theorem B608251 : Blo 539803 608251 := bstep (se 1 (by rfl) ⟨456188, by rfl⟩ : syracuseStep 608251 = 912377) B912377
theorem B20785247 : Blo 539803 20785247 := bstep (se 1 (by rfl) ⟨15588935, by rfl⟩ : syracuseStep 20785247 = 31177871) B31177871
theorem B2434378063 : Blo 539803 2434378063 := bstep (se 1 (by rfl) ⟨1825783547, by rfl⟩ : syracuseStep 2434378063 = 3651567095) B3651567095
theorem B17525099 : Blo 539803 17525099 := bstep (se 1 (by rfl) ⟨13143824, by rfl⟩ : syracuseStep 17525099 = 26287649) B26287649
theorem B1337999 : Blo 539803 1337999 := bstep (se 1 (by rfl) ⟨1003499, by rfl⟩ : syracuseStep 1337999 = 2006999) B2006999
theorem B4115447 : Blo 539803 4115447 := bstep (se 1 (by rfl) ⟨3086585, by rfl⟩ : syracuseStep 4115447 = 6173171) B6173171
theorem B14847133 : Blo 539803 14847133 := bstep (se 3 (by rfl) ⟨2783837, by rfl⟩ : syracuseStep 14847133 = 5567675) B5567675
theorem B6925499 : Blo 539803 6925499 := bstep (se 1 (by rfl) ⟨5194124, by rfl⟩ : syracuseStep 6925499 = 10388249) B10388249
theorem B8785385 : Blo 539803 8785385 := bstep (se 2 (by rfl) ⟨3294519, by rfl⟩ : syracuseStep 8785385 = 6589039) B6589039
theorem B1822337 : Blo 539803 1822337 := bstep (se 2 (by rfl) ⟨683376, by rfl⟩ : syracuseStep 1822337 = 1366753) B1366753
theorem B2641855 : Blo 539803 2641855 := bstep (se 1 (by rfl) ⟨1981391, by rfl⟩ : syracuseStep 2641855 = 3962783) B3962783
theorem B3911975 : Blo 539803 3911975 := bstep (se 1 (by rfl) ⟨2933981, by rfl⟩ : syracuseStep 3911975 = 5867963) B5867963
theorem B3944801 : Blo 539803 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B913855 : Blo 539803 913855 := bstep (se 1 (by rfl) ⟨685391, by rfl⟩ : syracuseStep 913855 = 1370783) B1370783
theorem B6582811 : Blo 539803 6582811 := bstep (se 1 (by rfl) ⟨4937108, by rfl⟩ : syracuseStep 6582811 = 9874217) B9874217
theorem B1110719 : Blo 539803 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B2732777 : Blo 539803 2732777 := bstep (se 2 (by rfl) ⟨1024791, by rfl⟩ : syracuseStep 2732777 = 2049583) B2049583
theorem B914375 : Blo 539803 914375 := bstep (se 1 (by rfl) ⟨685781, by rfl⟩ : syracuseStep 914375 = 1371563) B1371563
theorem B1823849 : Blo 539803 1823849 := bstep (se 2 (by rfl) ⟨683943, by rfl⟩ : syracuseStep 1823849 = 1367887) B1367887
theorem B1373345 : Blo 539803 1373345 := bstep (se 2 (by rfl) ⟨515004, by rfl⟩ : syracuseStep 1373345 = 1030009) B1030009
theorem B6165881 : Blo 539803 6165881 := bstep (se 2 (by rfl) ⟨2312205, by rfl⟩ : syracuseStep 6165881 = 4624411) B4624411
theorem B4118363 : Blo 539803 4118363 := bstep (se 1 (by rfl) ⟨3088772, by rfl⟩ : syracuseStep 4118363 = 6177545) B6177545
theorem B1218743 : Blo 539803 1218743 := bstep (se 1 (by rfl) ⟨914057, by rfl⟩ : syracuseStep 1218743 = 1828115) B1828115
theorem B19782305 : Blo 539803 19782305 := bstep (se 2 (by rfl) ⟨7418364, by rfl⟩ : syracuseStep 19782305 = 14836729) B14836729
theorem B3169145 : Blo 539803 3169145 := bstep (se 2 (by rfl) ⟨1188429, by rfl⟩ : syracuseStep 3169145 = 2376859) B2376859
theorem B10681247 : Blo 539803 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B1219679 : Blo 539803 1219679 := bstep (se 1 (by rfl) ⟨914759, by rfl⟩ : syracuseStep 1219679 = 1829519) B1829519
theorem B13843709 : Blo 539803 13843709 := bstep (se 3 (by rfl) ⟨2595695, by rfl⟩ : syracuseStep 13843709 = 5191391) B5191391
theorem B1219859 : Blo 539803 1219859 := bstep (se 1 (by rfl) ⟨914894, by rfl⟩ : syracuseStep 1219859 = 1829789) B1829789
theorem B540187 : Blo 539803 540187 := bstep (se 1 (by rfl) ⟨405140, by rfl⟩ : syracuseStep 540187 = 810281) B810281
theorem B11714543 : Blo 539803 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B540839 : Blo 539803 540839 := bstep (se 1 (by rfl) ⟨405629, by rfl⟩ : syracuseStep 540839 = 811259) B811259
theorem B46301971 : Blo 539803 46301971 := bstep (se 1 (by rfl) ⟨34726478, by rfl⟩ : syracuseStep 46301971 = 69452957) B69452957
theorem B541531 : Blo 539803 541531 := bstep (se 1 (by rfl) ⟨406148, by rfl⟩ : syracuseStep 541531 = 812297) B812297
theorem B10519469 : Blo 539803 10519469 := bstep (se 3 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 10519469 = 3944801) B3944801
theorem B812495 : Blo 539803 812495 := bstep (se 1 (by rfl) ⟨609371, by rfl⟩ : syracuseStep 812495 = 1218743) B1218743
theorem B11683399 : Blo 539803 11683399 := bstep (se 1 (by rfl) ⟨8762549, by rfl⟩ : syracuseStep 11683399 = 17525099) B17525099
theorem B2745575 : Blo 539803 2745575 := bstep (se 1 (by rfl) ⟨2059181, by rfl⟩ : syracuseStep 2745575 = 4118363) B4118363
theorem B7120831 : Blo 539803 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B813119 : Blo 539803 813119 := bstep (se 1 (by rfl) ⟨609839, by rfl⟩ : syracuseStep 813119 = 1219679) B1219679
theorem B813239 : Blo 539803 813239 := bstep (se 1 (by rfl) ⟨609929, by rfl⟩ : syracuseStep 813239 = 1219859) B1219859
theorem B1214891 : Blo 539803 1214891 := bstep (se 1 (by rfl) ⟨911168, by rfl⟩ : syracuseStep 1214891 = 1822337) B1822337
theorem B7809695 : Blo 539803 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B912127 : Blo 539803 912127 := bstep (se 1 (by rfl) ⟨684095, by rfl⟩ : syracuseStep 912127 = 1368191) B1368191
theorem B2607983 : Blo 539803 2607983 := bstep (se 1 (by rfl) ⟨1955987, by rfl⟩ : syracuseStep 2607983 = 3911975) B3911975
theorem B814079 : Blo 539803 814079 := bstep (se 1 (by rfl) ⟨610559, by rfl⟩ : syracuseStep 814079 = 1221119) B1221119
theorem B1158239 : Blo 539803 1158239 := bstep (se 1 (by rfl) ⟨868679, by rfl⟩ : syracuseStep 1158239 = 1737359) B1737359
theorem B1371239 : Blo 539803 1371239 := bstep (se 1 (by rfl) ⟨1028429, by rfl⟩ : syracuseStep 1371239 = 2056859) B2056859
theorem B3245837417 : Blo 539803 3245837417 := bstep (se 2 (by rfl) ⟨1217189031, by rfl⟩ : syracuseStep 3245837417 = 2434378063) B2434378063
theorem B1821851 : Blo 539803 1821851 := bstep (se 1 (by rfl) ⟨1366388, by rfl⟩ : syracuseStep 1821851 = 2732777) B2732777
theorem B609583 : Blo 539803 609583 := bstep (se 1 (by rfl) ⟨457187, by rfl⟩ : syracuseStep 609583 = 914375) B914375
theorem B8777081 : Blo 539803 8777081 := bstep (se 2 (by rfl) ⟨3291405, by rfl⟩ : syracuseStep 8777081 = 6582811) B6582811
theorem B1215899 : Blo 539803 1215899 := bstep (se 1 (by rfl) ⟨911924, by rfl⟩ : syracuseStep 1215899 = 1823849) B1823849
theorem B3468719 : Blo 539803 3468719 := bstep (se 1 (by rfl) ⟨2601539, by rfl⟩ : syracuseStep 3468719 = 5203079) B5203079
theorem B2305817 : Blo 539803 2305817 := bstep (se 2 (by rfl) ⟨864681, by rfl⟩ : syracuseStep 2305817 = 1729363) B1729363
theorem B13856831 : Blo 539803 13856831 := bstep (se 1 (by rfl) ⟨10392623, by rfl⟩ : syracuseStep 13856831 = 20785247) B20785247
theorem B19796177 : Blo 539803 19796177 := bstep (se 2 (by rfl) ⟨7423566, by rfl⟩ : syracuseStep 19796177 = 14847133) B14847133
theorem B3567997 : Blo 539803 3567997 := bstep (se 3 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 3567997 = 1337999) B1337999
theorem B2961917 : Blo 539803 2961917 := bstep (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) B1110719
theorem B4616999 : Blo 539803 4616999 := bstep (se 1 (by rfl) ⟨3462749, by rfl⟩ : syracuseStep 4616999 = 6925499) B6925499
theorem B9229139 : Blo 539803 9229139 := bstep (se 1 (by rfl) ⟨6921854, by rfl⟩ : syracuseStep 9229139 = 13843709) B13843709
theorem B4216531 : Blo 539803 4216531 := bstep (se 1 (by rfl) ⟨3162398, by rfl⟩ : syracuseStep 4216531 = 6324797) B6324797
theorem B1218473 : Blo 539803 1218473 := bstep (se 2 (by rfl) ⟨456927, by rfl⟩ : syracuseStep 1218473 = 913855) B913855
theorem B1824875 : Blo 539803 1824875 := bstep (se 1 (by rfl) ⟨1368656, by rfl⟩ : syracuseStep 1824875 = 2737313) B2737313
theorem B915563 : Blo 539803 915563 := bstep (se 1 (by rfl) ⟨686672, by rfl⟩ : syracuseStep 915563 = 1373345) B1373345
theorem B3086495 : Blo 539803 3086495 := bstep (se 1 (by rfl) ⟨2314871, by rfl⟩ : syracuseStep 3086495 = 4629743) B4629743
theorem B4110587 : Blo 539803 4110587 := bstep (se 1 (by rfl) ⟨3082940, by rfl⟩ : syracuseStep 4110587 = 6165881) B6165881
theorem B1825145 : Blo 539803 1825145 := bstep (se 2 (by rfl) ⟨684429, by rfl⟩ : syracuseStep 1825145 = 1368859) B1368859
theorem B13188203 : Blo 539803 13188203 := bstep (se 1 (by rfl) ⟨9891152, by rfl⟩ : syracuseStep 13188203 = 19782305) B19782305
theorem B2112763 : Blo 539803 2112763 := bstep (se 1 (by rfl) ⟨1584572, by rfl⟩ : syracuseStep 2112763 = 3169145) B3169145
theorem B2743631 : Blo 539803 2743631 := bstep (se 1 (by rfl) ⟨2057723, by rfl⟩ : syracuseStep 2743631 = 4115447) B4115447
theorem B5856923 : Blo 539803 5856923 := bstep (se 1 (by rfl) ⟨4392692, by rfl⟩ : syracuseStep 5856923 = 8785385) B8785385
theorem B3522473 : Blo 539803 3522473 := bstep (se 2 (by rfl) ⟨1320927, by rfl⟩ : syracuseStep 3522473 = 2641855) B2641855
theorem B811001 : Blo 539803 811001 := bstep (se 2 (by rfl) ⟨304125, by rfl⟩ : syracuseStep 811001 = 608251) B608251
theorem B3088637 : Blo 539803 3088637 := bstep (se 3 (by rfl) ⟨579119, by rfl⟩ : syracuseStep 3088637 = 1158239) B1158239
theorem B1974611 : Blo 539803 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B6152759 : Blo 539803 6152759 := bstep (se 1 (by rfl) ⟨4614569, by rfl⟩ : syracuseStep 6152759 = 9229139) B9229139
theorem B7012979 : Blo 539803 7012979 := bstep (se 1 (by rfl) ⟨5259734, by rfl⟩ : syracuseStep 7012979 = 10519469) B10519469
theorem B541663 : Blo 539803 541663 := bstep (se 1 (by rfl) ⟨406247, by rfl⟩ : syracuseStep 541663 = 812495) B812495
theorem B61735961 : Blo 539803 61735961 := bstep (se 2 (by rfl) ⟨23150985, by rfl⟩ : syracuseStep 61735961 = 46301971) B46301971
theorem B812315 : Blo 539803 812315 := bstep (se 1 (by rfl) ⟨609236, by rfl⟩ : syracuseStep 812315 = 1218473) B1218473
theorem B542079 : Blo 539803 542079 := bstep (se 1 (by rfl) ⟨406559, by rfl⟩ : syracuseStep 542079 = 813119) B813119
theorem B2057663 : Blo 539803 2057663 := bstep (se 1 (by rfl) ⟨1543247, by rfl⟩ : syracuseStep 2057663 = 3086495) B3086495
theorem B542159 : Blo 539803 542159 := bstep (se 1 (by rfl) ⟨406619, by rfl⟩ : syracuseStep 542159 = 813239) B813239
theorem B812777 : Blo 539803 812777 := bstep (se 2 (by rfl) ⟨304791, by rfl⟩ : syracuseStep 812777 = 609583) B609583
theorem B1738655 : Blo 539803 1738655 := bstep (se 1 (by rfl) ⟨1303991, by rfl⟩ : syracuseStep 1738655 = 2607983) B2607983
theorem B542719 : Blo 539803 542719 := bstep (se 1 (by rfl) ⟨407039, by rfl⟩ : syracuseStep 542719 = 814079) B814079
theorem B8792135 : Blo 539803 8792135 := bstep (se 1 (by rfl) ⟨6594101, by rfl⟩ : syracuseStep 8792135 = 13188203) B13188203
theorem B1214567 : Blo 539803 1214567 := bstep (se 1 (by rfl) ⟨910925, by rfl⟩ : syracuseStep 1214567 = 1821851) B1821851
theorem B1829087 : Blo 539803 1829087 := bstep (se 1 (by rfl) ⟨1371815, by rfl⟩ : syracuseStep 1829087 = 2743631) B2743631
theorem B5851387 : Blo 539803 5851387 := bstep (se 1 (by rfl) ⟨4388540, by rfl⟩ : syracuseStep 5851387 = 8777081) B8777081
theorem B5622041 : Blo 539803 5622041 := bstep (se 2 (by rfl) ⟨2108265, by rfl⟩ : syracuseStep 5622041 = 4216531) B4216531
theorem B2312479 : Blo 539803 2312479 := bstep (se 1 (by rfl) ⟨1734359, by rfl⟩ : syracuseStep 2312479 = 3468719) B3468719
theorem B1830383 : Blo 539803 1830383 := bstep (se 1 (by rfl) ⟨1372787, by rfl⟩ : syracuseStep 1830383 = 2745575) B2745575
theorem B1216169 : Blo 539803 1216169 := bstep (se 2 (by rfl) ⟨456063, by rfl⟩ : syracuseStep 1216169 = 912127) B912127
theorem B1216583 : Blo 539803 1216583 := bstep (se 1 (by rfl) ⟨912437, by rfl⟩ : syracuseStep 1216583 = 1824875) B1824875
theorem B610375 : Blo 539803 610375 := bstep (se 1 (by rfl) ⟨457781, by rfl⟩ : syracuseStep 610375 = 915563) B915563
theorem B2740391 : Blo 539803 2740391 := bstep (se 1 (by rfl) ⟨2055293, by rfl⟩ : syracuseStep 2740391 = 4110587) B4110587
theorem B1216763 : Blo 539803 1216763 := bstep (se 1 (by rfl) ⟨912572, by rfl⟩ : syracuseStep 1216763 = 1825145) B1825145
theorem B5206463 : Blo 539803 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B914159 : Blo 539803 914159 := bstep (se 1 (by rfl) ⟨685619, by rfl⟩ : syracuseStep 914159 = 1371239) B1371239
theorem B15577865 : Blo 539803 15577865 := bstep (se 2 (by rfl) ⟨5841699, by rfl⟩ : syracuseStep 15577865 = 11683399) B11683399
theorem B3904615 : Blo 539803 3904615 := bstep (se 1 (by rfl) ⟨2928461, by rfl⟩ : syracuseStep 3904615 = 5856923) B5856923
theorem B1537211 : Blo 539803 1537211 := bstep (se 1 (by rfl) ⟨1152908, by rfl⟩ : syracuseStep 1537211 = 2305817) B2305817
theorem B2348315 : Blo 539803 2348315 := bstep (se 1 (by rfl) ⟨1761236, by rfl⟩ : syracuseStep 2348315 = 3522473) B3522473
theorem B9237887 : Blo 539803 9237887 := bstep (se 1 (by rfl) ⟨6928415, by rfl⟩ : syracuseStep 9237887 = 13856831) B13856831
theorem B52789805 : Blo 539803 52789805 := bstep (se 3 (by rfl) ⟨9898088, by rfl⟩ : syracuseStep 52789805 = 19796177) B19796177
theorem B4757329 : Blo 539803 4757329 := bstep (se 2 (by rfl) ⟨1783998, by rfl⟩ : syracuseStep 4757329 = 3567997) B3567997
theorem B3077999 : Blo 539803 3077999 := bstep (se 1 (by rfl) ⟨2308499, by rfl⟩ : syracuseStep 3077999 = 4616999) B4616999
theorem B809927 : Blo 539803 809927 := bstep (se 1 (by rfl) ⟨607445, by rfl⟩ : syracuseStep 809927 = 1214891) B1214891
theorem B2817017 : Blo 539803 2817017 := bstep (se 2 (by rfl) ⟨1056381, by rfl⟩ : syracuseStep 2817017 = 2112763) B2112763
theorem B2163891611 : Blo 539803 2163891611 := bstep (se 1 (by rfl) ⟨1622918708, by rfl⟩ : syracuseStep 2163891611 = 3245837417) B3245837417
theorem B810599 : Blo 539803 810599 := bstep (se 1 (by rfl) ⟨607949, by rfl⟩ : syracuseStep 810599 = 1215899) B1215899
theorem B9494441 : Blo 539803 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B540667 : Blo 539803 540667 := bstep (se 1 (by rfl) ⟨405500, by rfl⟩ : syracuseStep 540667 = 811001) B811001
theorem B811055 : Blo 539803 811055 := bstep (se 1 (by rfl) ⟨608291, by rfl⟩ : syracuseStep 811055 = 1216583) B1216583
theorem B1826927 : Blo 539803 1826927 := bstep (se 1 (by rfl) ⟨1370195, by rfl⟩ : syracuseStep 1826927 = 2740391) B2740391
theorem B811175 : Blo 539803 811175 := bstep (se 1 (by rfl) ⟨608381, by rfl⟩ : syracuseStep 811175 = 1216763) B1216763
theorem B35193203 : Blo 539803 35193203 := bstep (se 1 (by rfl) ⟨26394902, by rfl⟩ : syracuseStep 35193203 = 52789805) B52789805
theorem B20824613 : Blo 539803 20824613 := bstep (se 4 (by rfl) ⟨1952307, by rfl⟩ : syracuseStep 20824613 = 3904615) B3904615
theorem B41157307 : Blo 539803 41157307 := bstep (se 1 (by rfl) ⟨30867980, by rfl⟩ : syracuseStep 41157307 = 61735961) B61735961
theorem B1024807 : Blo 539803 1024807 := bstep (se 1 (by rfl) ⟨768605, by rfl⟩ : syracuseStep 1024807 = 1537211) B1537211
theorem B541543 : Blo 539803 541543 := bstep (se 1 (by rfl) ⟨406157, by rfl⟩ : syracuseStep 541543 = 812315) B812315
theorem B1565543 : Blo 539803 1565543 := bstep (se 1 (by rfl) ⟨1174157, by rfl⟩ : syracuseStep 1565543 = 2348315) B2348315
theorem B541851 : Blo 539803 541851 := bstep (se 1 (by rfl) ⟨406388, by rfl⟩ : syracuseStep 541851 = 812777) B812777
theorem B1878011 : Blo 539803 1878011 := bstep (se 1 (by rfl) ⟨1408508, by rfl⟩ : syracuseStep 1878011 = 2817017) B2817017
theorem B6343105 : Blo 539803 6343105 := bstep (se 2 (by rfl) ⟨2378664, by rfl⟩ : syracuseStep 6343105 = 4757329) B4757329
theorem B813833 : Blo 539803 813833 := bstep (se 2 (by rfl) ⟨305187, by rfl⟩ : syracuseStep 813833 = 610375) B610375
theorem B2059091 : Blo 539803 2059091 := bstep (se 1 (by rfl) ⟨1544318, by rfl⟩ : syracuseStep 2059091 = 3088637) B3088637
theorem B7801849 : Blo 539803 7801849 := bstep (se 2 (by rfl) ⟨2925693, by rfl⟩ : syracuseStep 7801849 = 5851387) B5851387
theorem B3083305 : Blo 539803 3083305 := bstep (se 2 (by rfl) ⟨1156239, by rfl⟩ : syracuseStep 3083305 = 2312479) B2312479
theorem B609439 : Blo 539803 609439 := bstep (se 1 (by rfl) ⟨457079, by rfl⟩ : syracuseStep 609439 = 914159) B914159
theorem B1371775 : Blo 539803 1371775 := bstep (se 1 (by rfl) ⟨1028831, by rfl⟩ : syracuseStep 1371775 = 2057663) B2057663
theorem B2051999 : Blo 539803 2051999 := bstep (se 1 (by rfl) ⟨1538999, by rfl⟩ : syracuseStep 2051999 = 3077999) B3077999
theorem B1159103 : Blo 539803 1159103 := bstep (se 1 (by rfl) ⟨869327, by rfl⟩ : syracuseStep 1159103 = 1738655) B1738655
theorem B5861423 : Blo 539803 5861423 := bstep (se 1 (by rfl) ⟨4396067, by rfl⟩ : syracuseStep 5861423 = 8792135) B8792135
theorem B3748027 : Blo 539803 3748027 := bstep (se 1 (by rfl) ⟨2811020, by rfl⟩ : syracuseStep 3748027 = 5622041) B5622041
theorem B6329627 : Blo 539803 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B1316407 : Blo 539803 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B3470975 : Blo 539803 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B4101839 : Blo 539803 4101839 := bstep (se 1 (by rfl) ⟨3076379, by rfl⟩ : syracuseStep 4101839 = 6152759) B6152759
theorem B4675319 : Blo 539803 4675319 := bstep (se 1 (by rfl) ⟨3506489, by rfl⟩ : syracuseStep 4675319 = 7012979) B7012979
theorem B10385243 : Blo 539803 10385243 := bstep (se 1 (by rfl) ⟨7788932, by rfl⟩ : syracuseStep 10385243 = 15577865) B15577865
theorem B6158591 : Blo 539803 6158591 := bstep (se 1 (by rfl) ⟨4618943, by rfl⟩ : syracuseStep 6158591 = 9237887) B9237887
theorem B809711 : Blo 539803 809711 := bstep (se 1 (by rfl) ⟨607283, by rfl⟩ : syracuseStep 809711 = 1214567) B1214567
theorem B1219391 : Blo 539803 1219391 := bstep (se 1 (by rfl) ⟨914543, by rfl⟩ : syracuseStep 1219391 = 1829087) B1829087
theorem B539951 : Blo 539803 539951 := bstep (se 1 (by rfl) ⟨404963, by rfl⟩ : syracuseStep 539951 = 809927) B809927
theorem B1442594407 : Blo 539803 1442594407 := bstep (se 1 (by rfl) ⟨1081945805, by rfl⟩ : syracuseStep 1442594407 = 2163891611) B2163891611
theorem B1220255 : Blo 539803 1220255 := bstep (se 1 (by rfl) ⟨915191, by rfl⟩ : syracuseStep 1220255 = 1830383) B1830383
theorem B540399 : Blo 539803 540399 := bstep (se 1 (by rfl) ⟨405299, by rfl⟩ : syracuseStep 540399 = 810599) B810599
theorem B810779 : Blo 539803 810779 := bstep (se 1 (by rfl) ⟨608084, by rfl⟩ : syracuseStep 810779 = 1216169) B1216169
theorem B540703 : Blo 539803 540703 := bstep (se 1 (by rfl) ⟨405527, by rfl⟩ : syracuseStep 540703 = 811055) B811055
theorem B3907615 : Blo 539803 3907615 := bstep (se 1 (by rfl) ⟨2930711, by rfl⟩ : syracuseStep 3907615 = 5861423) B5861423
theorem B540783 : Blo 539803 540783 := bstep (se 1 (by rfl) ⟨405587, by rfl⟩ : syracuseStep 540783 = 811175) B811175
theorem B4997369 : Blo 539803 4997369 := bstep (se 2 (by rfl) ⟨1874013, by rfl⟩ : syracuseStep 4997369 = 3748027) B3748027
theorem B23462135 : Blo 539803 23462135 := bstep (se 1 (by rfl) ⟨17596601, by rfl⟩ : syracuseStep 23462135 = 35193203) B35193203
theorem B4219751 : Blo 539803 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B6923495 : Blo 539803 6923495 := bstep (se 1 (by rfl) ⟨5192621, by rfl⟩ : syracuseStep 6923495 = 10385243) B10385243
theorem B4105727 : Blo 539803 4105727 := bstep (se 1 (by rfl) ⟨3079295, by rfl⟩ : syracuseStep 4105727 = 6158591) B6158591
theorem B812585 : Blo 539803 812585 := bstep (se 2 (by rfl) ⟨304719, by rfl⟩ : syracuseStep 812585 = 609439) B609439
theorem B542555 : Blo 539803 542555 := bstep (se 1 (by rfl) ⟨406916, by rfl⟩ : syracuseStep 542555 = 813833) B813833
theorem B812927 : Blo 539803 812927 := bstep (se 1 (by rfl) ⟨609695, by rfl⟩ : syracuseStep 812927 = 1219391) B1219391
theorem B1755209 : Blo 539803 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B1923459209 : Blo 539803 1923459209 := bstep (se 2 (by rfl) ⟨721297203, by rfl⟩ : syracuseStep 1923459209 = 1442594407) B1442594407
theorem B1829033 : Blo 539803 1829033 := bstep (se 2 (by rfl) ⟨685887, by rfl⟩ : syracuseStep 1829033 = 1371775) B1371775
theorem B813503 : Blo 539803 813503 := bstep (se 1 (by rfl) ⟨610127, by rfl⟩ : syracuseStep 813503 = 1220255) B1220255
theorem B772735 : Blo 539803 772735 := bstep (se 1 (by rfl) ⟨579551, by rfl⟩ : syracuseStep 772735 = 1159103) B1159103
theorem B1043695 : Blo 539803 1043695 := bstep (se 1 (by rfl) ⟨782771, by rfl⟩ : syracuseStep 1043695 = 1565543) B1565543
theorem B8457473 : Blo 539803 8457473 := bstep (se 2 (by rfl) ⟨3171552, by rfl⟩ : syracuseStep 8457473 = 6343105) B6343105
theorem B2313983 : Blo 539803 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B3116879 : Blo 539803 3116879 := bstep (se 1 (by rfl) ⟨2337659, by rfl⟩ : syracuseStep 3116879 = 4675319) B4675319
theorem B1372727 : Blo 539803 1372727 := bstep (se 1 (by rfl) ⟨1029545, by rfl⟩ : syracuseStep 1372727 = 2059091) B2059091
theorem B1217951 : Blo 539803 1217951 := bstep (se 1 (by rfl) ⟨913463, by rfl⟩ : syracuseStep 1217951 = 1826927) B1826927
theorem B13883075 : Blo 539803 13883075 := bstep (se 1 (by rfl) ⟨10412306, by rfl⟩ : syracuseStep 13883075 = 20824613) B20824613
theorem B54876409 : Blo 539803 54876409 := bstep (se 2 (by rfl) ⟨20578653, by rfl⟩ : syracuseStep 54876409 = 41157307) B41157307
theorem B1366409 : Blo 539803 1366409 := bstep (se 2 (by rfl) ⟨512403, by rfl⟩ : syracuseStep 1366409 = 1024807) B1024807
theorem B2734559 : Blo 539803 2734559 := bstep (se 1 (by rfl) ⟨2050919, by rfl⟩ : syracuseStep 2734559 = 4101839) B4101839
theorem B10402465 : Blo 539803 10402465 := bstep (se 2 (by rfl) ⟨3900924, by rfl⟩ : syracuseStep 10402465 = 7801849) B7801849
theorem B1252007 : Blo 539803 1252007 := bstep (se 1 (by rfl) ⟨939005, by rfl⟩ : syracuseStep 1252007 = 1878011) B1878011
theorem B4111073 : Blo 539803 4111073 := bstep (se 2 (by rfl) ⟨1541652, by rfl⟩ : syracuseStep 4111073 = 3083305) B3083305
theorem B539807 : Blo 539803 539807 := bstep (se 1 (by rfl) ⟨404855, by rfl⟩ : syracuseStep 539807 = 809711) B809711
theorem B540519 : Blo 539803 540519 := bstep (se 1 (by rfl) ⟨405389, by rfl⟩ : syracuseStep 540519 = 810779) B810779
theorem B1367999 : Blo 539803 1367999 := bstep (se 1 (by rfl) ⟨1025999, by rfl⟩ : syracuseStep 1367999 = 2051999) B2051999
theorem B5210153 : Blo 539803 5210153 := bstep (se 2 (by rfl) ⟨1953807, by rfl⟩ : syracuseStep 5210153 = 3907615) B3907615
theorem B22553261 : Blo 539803 22553261 := bstep (se 3 (by rfl) ⟨4228736, by rfl⟩ : syracuseStep 22553261 = 8457473) B8457473
theorem B13869953 : Blo 539803 13869953 := bstep (se 2 (by rfl) ⟨5201232, by rfl⟩ : syracuseStep 13869953 = 10402465) B10402465
theorem B811967 : Blo 539803 811967 := bstep (se 1 (by rfl) ⟨608975, by rfl⟩ : syracuseStep 811967 = 1217951) B1217951
theorem B2737151 : Blo 539803 2737151 := bstep (se 1 (by rfl) ⟨2052863, by rfl⟩ : syracuseStep 2737151 = 4105727) B4105727
theorem B541723 : Blo 539803 541723 := bstep (se 1 (by rfl) ⟨406292, by rfl⟩ : syracuseStep 541723 = 812585) B812585
theorem B541951 : Blo 539803 541951 := bstep (se 1 (by rfl) ⟨406463, by rfl⟩ : syracuseStep 541951 = 812927) B812927
theorem B910939 : Blo 539803 910939 := bstep (se 1 (by rfl) ⟨683204, by rfl⟩ : syracuseStep 910939 = 1366409) B1366409
theorem B542335 : Blo 539803 542335 := bstep (se 1 (by rfl) ⟨406751, by rfl⟩ : syracuseStep 542335 = 813503) B813503
theorem B1542655 : Blo 539803 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B911999 : Blo 539803 911999 := bstep (se 1 (by rfl) ⟨683999, by rfl⟩ : syracuseStep 911999 = 1367999) B1367999
theorem B15641423 : Blo 539803 15641423 := bstep (se 1 (by rfl) ⟨11731067, by rfl⟩ : syracuseStep 15641423 = 23462135) B23462135
theorem B4680557 : Blo 539803 4680557 := bstep (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) B1755209
theorem B4615663 : Blo 539803 4615663 := bstep (se 1 (by rfl) ⟨3461747, by rfl⟩ : syracuseStep 4615663 = 6923495) B6923495
theorem B1282306139 : Blo 539803 1282306139 := bstep (se 1 (by rfl) ⟨961729604, by rfl⟩ : syracuseStep 1282306139 = 1923459209) B1923459209
theorem B1823039 : Blo 539803 1823039 := bstep (se 1 (by rfl) ⟨1367279, by rfl⟩ : syracuseStep 1823039 = 2734559) B2734559
theorem B2740715 : Blo 539803 2740715 := bstep (se 1 (by rfl) ⟨2055536, by rfl⟩ : syracuseStep 2740715 = 4111073) B4111073
theorem B2077919 : Blo 539803 2077919 := bstep (se 1 (by rfl) ⟨1558439, by rfl⟩ : syracuseStep 2077919 = 3116879) B3116879
theorem B3331579 : Blo 539803 3331579 := bstep (se 1 (by rfl) ⟨2498684, by rfl⟩ : syracuseStep 3331579 = 4997369) B4997369
theorem B915151 : Blo 539803 915151 := bstep (se 1 (by rfl) ⟨686363, by rfl⟩ : syracuseStep 915151 = 1372727) B1372727
theorem B1030313 : Blo 539803 1030313 := bstep (se 2 (by rfl) ⟨386367, by rfl⟩ : syracuseStep 1030313 = 772735) B772735
theorem B9255383 : Blo 539803 9255383 := bstep (se 1 (by rfl) ⟨6941537, by rfl⟩ : syracuseStep 9255383 = 13883075) B13883075
theorem B292674181 : Blo 539803 292674181 := bstep (se 4 (by rfl) ⟨27438204, by rfl⟩ : syracuseStep 292674181 = 54876409) B54876409
theorem B1219355 : Blo 539803 1219355 := bstep (se 1 (by rfl) ⟨914516, by rfl⟩ : syracuseStep 1219355 = 1829033) B1829033
theorem B180042709 : Blo 539803 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B1391593 : Blo 539803 1391593 := bstep (se 2 (by rfl) ⟨521847, by rfl⟩ : syracuseStep 1391593 = 1043695) B1043695
theorem B834671 : Blo 539803 834671 := bstep (se 1 (by rfl) ⟨626003, by rfl⟩ : syracuseStep 834671 = 1252007) B1252007
theorem B3473435 : Blo 539803 3473435 := bstep (se 1 (by rfl) ⟨2605076, by rfl⟩ : syracuseStep 3473435 = 5210153) B5210153
theorem B1827143 : Blo 539803 1827143 := bstep (se 1 (by rfl) ⟨1370357, by rfl⟩ : syracuseStep 1827143 = 2740715) B2740715
theorem B541311 : Blo 539803 541311 := bstep (se 1 (by rfl) ⟨405983, by rfl⟩ : syracuseStep 541311 = 811967) B811967
theorem B2056873 : Blo 539803 2056873 := bstep (se 2 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 2056873 = 1542655) B1542655
theorem B1385279 : Blo 539803 1385279 := bstep (se 1 (by rfl) ⟨1038959, by rfl⟩ : syracuseStep 1385279 = 2077919) B2077919
theorem B6170255 : Blo 539803 6170255 := bstep (se 1 (by rfl) ⟨4627691, by rfl⟩ : syracuseStep 6170255 = 9255383) B9255383
theorem B607999 : Blo 539803 607999 := bstep (se 1 (by rfl) ⟨455999, by rfl⟩ : syracuseStep 607999 = 911999) B911999
theorem B812903 : Blo 539803 812903 := bstep (se 1 (by rfl) ⟨609677, by rfl⟩ : syracuseStep 812903 = 1219355) B1219355
theorem B6154217 : Blo 539803 6154217 := bstep (se 2 (by rfl) ⟨2307831, by rfl⟩ : syracuseStep 6154217 = 4615663) B4615663
theorem B4442105 : Blo 539803 4442105 := bstep (se 2 (by rfl) ⟨1665789, by rfl⟩ : syracuseStep 4442105 = 3331579) B3331579
theorem B1214585 : Blo 539803 1214585 := bstep (se 2 (by rfl) ⟨455469, by rfl⟩ : syracuseStep 1214585 = 910939) B910939
theorem B854870759 : Blo 539803 854870759 := bstep (se 1 (by rfl) ⟨641153069, by rfl⟩ : syracuseStep 854870759 = 1282306139) B1282306139
theorem B1215359 : Blo 539803 1215359 := bstep (se 1 (by rfl) ⟨911519, by rfl⟩ : syracuseStep 1215359 = 1823039) B1823039
theorem B15035507 : Blo 539803 15035507 := bstep (se 1 (by rfl) ⟨11276630, by rfl⟩ : syracuseStep 15035507 = 22553261) B22553261
theorem B1855457 : Blo 539803 1855457 := bstep (se 2 (by rfl) ⟨695796, by rfl⟩ : syracuseStep 1855457 = 1391593) B1391593
theorem B9246635 : Blo 539803 9246635 := bstep (se 1 (by rfl) ⟨6934976, by rfl⟩ : syracuseStep 9246635 = 13869953) B13869953
theorem B1824767 : Blo 539803 1824767 := bstep (se 1 (by rfl) ⟨1368575, by rfl⟩ : syracuseStep 1824767 = 2737151) B2737151
theorem B390232241 : Blo 539803 390232241 := bstep (se 2 (by rfl) ⟨146337090, by rfl⟩ : syracuseStep 390232241 = 292674181) B292674181
theorem B240056945 : Blo 539803 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B686875 : Blo 539803 686875 := bstep (se 1 (by rfl) ⟨515156, by rfl⟩ : syracuseStep 686875 = 1030313) B1030313
theorem B10427615 : Blo 539803 10427615 := bstep (se 1 (by rfl) ⟨7820711, by rfl⟩ : syracuseStep 10427615 = 15641423) B15641423
theorem B3120371 : Blo 539803 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B556447 : Blo 539803 556447 := bstep (se 1 (by rfl) ⟨417335, by rfl⟩ : syracuseStep 556447 = 834671) B834671
theorem B1220201 : Blo 539803 1220201 := bstep (se 2 (by rfl) ⟨457575, by rfl⟩ : syracuseStep 1220201 = 915151) B915151
theorem B11870869 : Blo 539803 11870869 := bstep (se 6 (by rfl) ⟨278223, by rfl⟩ : syracuseStep 11870869 = 556447) B556447
theorem B4113503 : Blo 539803 4113503 := bstep (se 1 (by rfl) ⟨3085127, by rfl⟩ : syracuseStep 4113503 = 6170255) B6170255
theorem B541935 : Blo 539803 541935 := bstep (se 1 (by rfl) ⟨406451, by rfl⟩ : syracuseStep 541935 = 812903) B812903
theorem B260154827 : Blo 539803 260154827 := bstep (se 1 (by rfl) ⟨195116120, by rfl⟩ : syracuseStep 260154827 = 390232241) B390232241
theorem B813467 : Blo 539803 813467 := bstep (se 1 (by rfl) ⟨610100, by rfl⟩ : syracuseStep 813467 = 1220201) B1220201
theorem B6164423 : Blo 539803 6164423 := bstep (se 1 (by rfl) ⟨4623317, by rfl⟩ : syracuseStep 6164423 = 9246635) B9246635
theorem B2961403 : Blo 539803 2961403 := bstep (se 1 (by rfl) ⟨2221052, by rfl⟩ : syracuseStep 2961403 = 4442105) B4442105
theorem B1216511 : Blo 539803 1216511 := bstep (se 1 (by rfl) ⟨912383, by rfl⟩ : syracuseStep 1216511 = 1824767) B1824767
theorem B569913839 : Blo 539803 569913839 := bstep (se 1 (by rfl) ⟨427435379, by rfl⟩ : syracuseStep 569913839 = 854870759) B854870759
theorem B10023671 : Blo 539803 10023671 := bstep (se 1 (by rfl) ⟨7517753, by rfl⟩ : syracuseStep 10023671 = 15035507) B15035507
theorem B6951743 : Blo 539803 6951743 := bstep (se 1 (by rfl) ⟨5213807, by rfl⟩ : syracuseStep 6951743 = 10427615) B10427615
theorem B2315623 : Blo 539803 2315623 := bstep (se 1 (by rfl) ⟨1736717, by rfl⟩ : syracuseStep 2315623 = 3473435) B3473435
theorem B1218095 : Blo 539803 1218095 := bstep (se 1 (by rfl) ⟨913571, by rfl⟩ : syracuseStep 1218095 = 1827143) B1827143
theorem B923519 : Blo 539803 923519 := bstep (se 1 (by rfl) ⟨692639, by rfl⟩ : syracuseStep 923519 = 1385279) B1385279
theorem B2742497 : Blo 539803 2742497 := bstep (se 2 (by rfl) ⟨1028436, by rfl⟩ : syracuseStep 2742497 = 2056873) B2056873
theorem B915833 : Blo 539803 915833 := bstep (se 2 (by rfl) ⟨343437, by rfl⟩ : syracuseStep 915833 = 686875) B686875
theorem B4102811 : Blo 539803 4102811 := bstep (se 1 (by rfl) ⟨3077108, by rfl⟩ : syracuseStep 4102811 = 6154217) B6154217
theorem B809723 : Blo 539803 809723 := bstep (se 1 (by rfl) ⟨607292, by rfl⟩ : syracuseStep 809723 = 1214585) B1214585
theorem B160037963 : Blo 539803 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B810239 : Blo 539803 810239 := bstep (se 1 (by rfl) ⟨607679, by rfl⟩ : syracuseStep 810239 = 1215359) B1215359
theorem B2080247 : Blo 539803 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B810665 : Blo 539803 810665 := bstep (se 2 (by rfl) ⟨303999, by rfl⟩ : syracuseStep 810665 = 607999) B607999
theorem B1236971 : Blo 539803 1236971 := bstep (se 1 (by rfl) ⟨927728, by rfl⟩ : syracuseStep 1236971 = 1855457) B1855457
theorem B811007 : Blo 539803 811007 := bstep (se 1 (by rfl) ⟨608255, by rfl⟩ : syracuseStep 811007 = 1216511) B1216511
theorem B15827825 : Blo 539803 15827825 := bstep (se 2 (by rfl) ⟨5935434, by rfl⟩ : syracuseStep 15827825 = 11870869) B11870869
theorem B812063 : Blo 539803 812063 := bstep (se 1 (by rfl) ⟨609047, by rfl⟩ : syracuseStep 812063 = 1218095) B1218095
theorem B5547325 : Blo 539803 5547325 := bstep (se 3 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 5547325 = 2080247) B2080247
theorem B1828331 : Blo 539803 1828331 := bstep (se 1 (by rfl) ⟨1371248, by rfl⟩ : syracuseStep 1828331 = 2742497) B2742497
theorem B542311 : Blo 539803 542311 := bstep (se 1 (by rfl) ⟨406733, by rfl⟩ : syracuseStep 542311 = 813467) B813467
theorem B173436551 : Blo 539803 173436551 := bstep (se 1 (by rfl) ⟨130077413, by rfl⟩ : syracuseStep 173436551 = 260154827) B260154827
theorem B610555 : Blo 539803 610555 := bstep (se 1 (by rfl) ⟨457916, by rfl⟩ : syracuseStep 610555 = 915833) B915833
theorem B2462717 : Blo 539803 2462717 := bstep (se 3 (by rfl) ⟨461759, by rfl⟩ : syracuseStep 2462717 = 923519) B923519
theorem B3298589 : Blo 539803 3298589 := bstep (se 3 (by rfl) ⟨618485, by rfl⟩ : syracuseStep 3298589 = 1236971) B1236971
theorem B4109615 : Blo 539803 4109615 := bstep (se 1 (by rfl) ⟨3082211, by rfl⟩ : syracuseStep 4109615 = 6164423) B6164423
theorem B379942559 : Blo 539803 379942559 := bstep (se 1 (by rfl) ⟨284956919, by rfl⟩ : syracuseStep 379942559 = 569913839) B569913839
theorem B6682447 : Blo 539803 6682447 := bstep (se 1 (by rfl) ⟨5011835, by rfl⟩ : syracuseStep 6682447 = 10023671) B10023671
theorem B4634495 : Blo 539803 4634495 := bstep (se 1 (by rfl) ⟨3475871, by rfl⟩ : syracuseStep 4634495 = 6951743) B6951743
theorem B2742335 : Blo 539803 2742335 := bstep (se 1 (by rfl) ⟨2056751, by rfl⟩ : syracuseStep 2742335 = 4113503) B4113503
theorem B2735207 : Blo 539803 2735207 := bstep (se 1 (by rfl) ⟨2051405, by rfl⟩ : syracuseStep 2735207 = 4102811) B4102811
theorem B3087497 : Blo 539803 3087497 := bstep (se 2 (by rfl) ⟨1157811, by rfl⟩ : syracuseStep 3087497 = 2315623) B2315623
theorem B539815 : Blo 539803 539815 := bstep (se 1 (by rfl) ⟨404861, by rfl⟩ : syracuseStep 539815 = 809723) B809723
theorem B106691975 : Blo 539803 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B540159 : Blo 539803 540159 := bstep (se 1 (by rfl) ⟨405119, by rfl⟩ : syracuseStep 540159 = 810239) B810239
theorem B540443 : Blo 539803 540443 := bstep (se 1 (by rfl) ⟨405332, by rfl⟩ : syracuseStep 540443 = 810665) B810665
theorem B15794149 : Blo 539803 15794149 := bstep (se 4 (by rfl) ⟨1480701, by rfl⟩ : syracuseStep 15794149 = 2961403) B2961403
theorem B10551883 : Blo 539803 10551883 := bstep (se 1 (by rfl) ⟨7913912, by rfl⟩ : syracuseStep 10551883 = 15827825) B15827825
theorem B541375 : Blo 539803 541375 := bstep (se 1 (by rfl) ⟨406031, by rfl⟩ : syracuseStep 541375 = 812063) B812063
theorem B3089663 : Blo 539803 3089663 := bstep (se 1 (by rfl) ⟨2317247, by rfl⟩ : syracuseStep 3089663 = 4634495) B4634495
theorem B1828223 : Blo 539803 1828223 := bstep (se 1 (by rfl) ⟨1371167, by rfl⟩ : syracuseStep 1828223 = 2742335) B2742335
theorem B2058331 : Blo 539803 2058331 := bstep (se 1 (by rfl) ⟨1543748, by rfl⟩ : syracuseStep 2058331 = 3087497) B3087497
theorem B115624367 : Blo 539803 115624367 := bstep (se 1 (by rfl) ⟨86718275, by rfl⟩ : syracuseStep 115624367 = 173436551) B173436551
theorem B814073 : Blo 539803 814073 := bstep (se 2 (by rfl) ⟨305277, by rfl⟩ : syracuseStep 814073 = 610555) B610555
theorem B1641811 : Blo 539803 1641811 := bstep (se 1 (by rfl) ⟨1231358, by rfl⟩ : syracuseStep 1641811 = 2462717) B2462717
theorem B2199059 : Blo 539803 2199059 := bstep (se 1 (by rfl) ⟨1649294, by rfl⟩ : syracuseStep 2199059 = 3298589) B3298589
theorem B2739743 : Blo 539803 2739743 := bstep (se 1 (by rfl) ⟨2054807, by rfl⟩ : syracuseStep 2739743 = 4109615) B4109615
theorem B1823471 : Blo 539803 1823471 := bstep (se 1 (by rfl) ⟨1367603, by rfl⟩ : syracuseStep 1823471 = 2735207) B2735207
theorem B71127983 : Blo 539803 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B8909929 : Blo 539803 8909929 := bstep (se 2 (by rfl) ⟨3341223, by rfl⟩ : syracuseStep 8909929 = 6682447) B6682447
theorem B21058865 : Blo 539803 21058865 := bstep (se 2 (by rfl) ⟨7897074, by rfl⟩ : syracuseStep 21058865 = 15794149) B15794149
theorem B1218887 : Blo 539803 1218887 := bstep (se 1 (by rfl) ⟨914165, by rfl⟩ : syracuseStep 1218887 = 1828331) B1828331
theorem B253295039 : Blo 539803 253295039 := bstep (se 1 (by rfl) ⟨189971279, by rfl⟩ : syracuseStep 253295039 = 379942559) B379942559
theorem B7396433 : Blo 539803 7396433 := bstep (se 2 (by rfl) ⟨2773662, by rfl⟩ : syracuseStep 7396433 = 5547325) B5547325
theorem B540671 : Blo 539803 540671 := bstep (se 1 (by rfl) ⟨405503, by rfl⟩ : syracuseStep 540671 = 811007) B811007
theorem B2744441 : Blo 539803 2744441 := bstep (se 2 (by rfl) ⟨1029165, by rfl⟩ : syracuseStep 2744441 = 2058331) B2058331
theorem B11879905 : Blo 539803 11879905 := bstep (se 2 (by rfl) ⟨4454964, by rfl⟩ : syracuseStep 11879905 = 8909929) B8909929
theorem B812591 : Blo 539803 812591 := bstep (se 1 (by rfl) ⟨609443, by rfl⟩ : syracuseStep 812591 = 1218887) B1218887
theorem B168863359 : Blo 539803 168863359 := bstep (se 1 (by rfl) ⟨126647519, by rfl⟩ : syracuseStep 168863359 = 253295039) B253295039
theorem B2189081 : Blo 539803 2189081 := bstep (se 2 (by rfl) ⟨820905, by rfl⟩ : syracuseStep 2189081 = 1641811) B1641811
theorem B542715 : Blo 539803 542715 := bstep (se 1 (by rfl) ⟨407036, by rfl⟩ : syracuseStep 542715 = 814073) B814073
theorem B1215647 : Blo 539803 1215647 := bstep (se 1 (by rfl) ⟨911735, by rfl⟩ : syracuseStep 1215647 = 1823471) B1823471
theorem B47418655 : Blo 539803 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B14069177 : Blo 539803 14069177 := bstep (se 2 (by rfl) ⟨5275941, by rfl⟩ : syracuseStep 14069177 = 10551883) B10551883
theorem B2059775 : Blo 539803 2059775 := bstep (se 1 (by rfl) ⟨1544831, by rfl⟩ : syracuseStep 2059775 = 3089663) B3089663
theorem B77082911 : Blo 539803 77082911 := bstep (se 1 (by rfl) ⟨57812183, by rfl⟩ : syracuseStep 77082911 = 115624367) B115624367
theorem B14039243 : Blo 539803 14039243 := bstep (se 1 (by rfl) ⟨10529432, by rfl⟩ : syracuseStep 14039243 = 21058865) B21058865
theorem B1218815 : Blo 539803 1218815 := bstep (se 1 (by rfl) ⟨914111, by rfl⟩ : syracuseStep 1218815 = 1828223) B1828223
theorem B4930955 : Blo 539803 4930955 := bstep (se 1 (by rfl) ⟨3698216, by rfl⟩ : syracuseStep 4930955 = 7396433) B7396433
theorem B1466039 : Blo 539803 1466039 := bstep (se 1 (by rfl) ⟨1099529, by rfl⟩ : syracuseStep 1466039 = 2199059) B2199059
theorem B1826495 : Blo 539803 1826495 := bstep (se 1 (by rfl) ⟨1369871, by rfl⟩ : syracuseStep 1826495 = 2739743) B2739743
theorem B51388607 : Blo 539803 51388607 := bstep (se 1 (by rfl) ⟨38541455, by rfl⟩ : syracuseStep 51388607 = 77082911) B77082911
theorem B541727 : Blo 539803 541727 := bstep (se 1 (by rfl) ⟨406295, by rfl⟩ : syracuseStep 541727 = 812591) B812591
theorem B1459387 : Blo 539803 1459387 := bstep (se 1 (by rfl) ⟨1094540, by rfl⟩ : syracuseStep 1459387 = 2189081) B2189081
theorem B812543 : Blo 539803 812543 := bstep (se 1 (by rfl) ⟨609407, by rfl⟩ : syracuseStep 812543 = 1218815) B1218815
theorem B225151145 : Blo 539803 225151145 := bstep (se 2 (by rfl) ⟨84431679, by rfl⟩ : syracuseStep 225151145 = 168863359) B168863359
theorem B3287303 : Blo 539803 3287303 := bstep (se 1 (by rfl) ⟨2465477, by rfl⟩ : syracuseStep 3287303 = 4930955) B4930955
theorem B977359 : Blo 539803 977359 := bstep (se 1 (by rfl) ⟨733019, by rfl⟩ : syracuseStep 977359 = 1466039) B1466039
theorem B1829627 : Blo 539803 1829627 := bstep (se 1 (by rfl) ⟨1372220, by rfl⟩ : syracuseStep 1829627 = 2744441) B2744441
theorem B9359495 : Blo 539803 9359495 := bstep (se 1 (by rfl) ⟨7019621, by rfl⟩ : syracuseStep 9359495 = 14039243) B14039243
theorem B15839873 : Blo 539803 15839873 := bstep (se 2 (by rfl) ⟨5939952, by rfl⟩ : syracuseStep 15839873 = 11879905) B11879905
theorem B1373183 : Blo 539803 1373183 := bstep (se 1 (by rfl) ⟨1029887, by rfl⟩ : syracuseStep 1373183 = 2059775) B2059775
theorem B1217663 : Blo 539803 1217663 := bstep (se 1 (by rfl) ⟨913247, by rfl⟩ : syracuseStep 1217663 = 1826495) B1826495
theorem B63224873 : Blo 539803 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B810431 : Blo 539803 810431 := bstep (se 1 (by rfl) ⟨607823, by rfl⟩ : syracuseStep 810431 = 1215647) B1215647
theorem B9379451 : Blo 539803 9379451 := bstep (se 1 (by rfl) ⟨7034588, by rfl⟩ : syracuseStep 9379451 = 14069177) B14069177
theorem B34259071 : Blo 539803 34259071 := bstep (se 1 (by rfl) ⟨25694303, by rfl⟩ : syracuseStep 34259071 = 51388607) B51388607
theorem B10559915 : Blo 539803 10559915 := bstep (se 1 (by rfl) ⟨7919936, by rfl⟩ : syracuseStep 10559915 = 15839873) B15839873
theorem B1303145 : Blo 539803 1303145 := bstep (se 2 (by rfl) ⟨488679, by rfl⟩ : syracuseStep 1303145 = 977359) B977359
theorem B811775 : Blo 539803 811775 := bstep (se 1 (by rfl) ⟨608831, by rfl⟩ : syracuseStep 811775 = 1217663) B1217663
theorem B7783397 : Blo 539803 7783397 := bstep (se 4 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 7783397 = 1459387) B1459387
theorem B541695 : Blo 539803 541695 := bstep (se 1 (by rfl) ⟨406271, by rfl⟩ : syracuseStep 541695 = 812543) B812543
theorem B42149915 : Blo 539803 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B6252967 : Blo 539803 6252967 := bstep (se 1 (by rfl) ⟨4689725, by rfl⟩ : syracuseStep 6252967 = 9379451) B9379451
theorem B2191535 : Blo 539803 2191535 := bstep (se 1 (by rfl) ⟨1643651, by rfl⟩ : syracuseStep 2191535 = 3287303) B3287303
theorem B2401612213 : Blo 539803 2401612213 := bstep (se 5 (by rfl) ⟨112575572, by rfl⟩ : syracuseStep 2401612213 = 225151145) B225151145
theorem B6239663 : Blo 539803 6239663 := bstep (se 1 (by rfl) ⟨4679747, by rfl⟩ : syracuseStep 6239663 = 9359495) B9359495
theorem B915455 : Blo 539803 915455 := bstep (se 1 (by rfl) ⟨686591, by rfl⟩ : syracuseStep 915455 = 1373183) B1373183
theorem B1219751 : Blo 539803 1219751 := bstep (se 1 (by rfl) ⟨914813, by rfl⟩ : syracuseStep 1219751 = 1829627) B1829627
theorem B540287 : Blo 539803 540287 := bstep (se 1 (by rfl) ⟨405215, by rfl⟩ : syracuseStep 540287 = 810431) B810431
theorem B45678761 : Blo 539803 45678761 := bstep (se 2 (by rfl) ⟨17129535, by rfl⟩ : syracuseStep 45678761 = 34259071) B34259071
theorem B868763 : Blo 539803 868763 := bstep (se 1 (by rfl) ⟨651572, by rfl⟩ : syracuseStep 868763 = 1303145) B1303145
theorem B541183 : Blo 539803 541183 := bstep (se 1 (by rfl) ⟨405887, by rfl⟩ : syracuseStep 541183 = 811775) B811775
theorem B28099943 : Blo 539803 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B813167 : Blo 539803 813167 := bstep (se 1 (by rfl) ⟨609875, by rfl⟩ : syracuseStep 813167 = 1219751) B1219751
theorem B1461023 : Blo 539803 1461023 := bstep (se 1 (by rfl) ⟨1095767, by rfl⟩ : syracuseStep 1461023 = 2191535) B2191535
theorem B7039943 : Blo 539803 7039943 := bstep (se 1 (by rfl) ⟨5279957, by rfl⟩ : syracuseStep 7039943 = 10559915) B10559915
theorem B3202149617 : Blo 539803 3202149617 := bstep (se 2 (by rfl) ⟨1200806106, by rfl⟩ : syracuseStep 3202149617 = 2401612213) B2401612213
theorem B5188931 : Blo 539803 5188931 := bstep (se 1 (by rfl) ⟨3891698, by rfl⟩ : syracuseStep 5188931 = 7783397) B7783397
theorem B610303 : Blo 539803 610303 := bstep (se 1 (by rfl) ⟨457727, by rfl⟩ : syracuseStep 610303 = 915455) B915455
theorem B8337289 : Blo 539803 8337289 := bstep (se 2 (by rfl) ⟨3126483, by rfl⟩ : syracuseStep 8337289 = 6252967) B6252967
theorem B4159775 : Blo 539803 4159775 := bstep (se 1 (by rfl) ⟨3119831, by rfl⟩ : syracuseStep 4159775 = 6239663) B6239663
theorem B542111 : Blo 539803 542111 := bstep (se 1 (by rfl) ⟨406583, by rfl⟩ : syracuseStep 542111 = 813167) B813167
theorem B3459287 : Blo 539803 3459287 := bstep (se 1 (by rfl) ⟨2594465, by rfl⟩ : syracuseStep 3459287 = 5188931) B5188931
theorem B813737 : Blo 539803 813737 := bstep (se 2 (by rfl) ⟨305151, by rfl⟩ : syracuseStep 813737 = 610303) B610303
theorem B30452507 : Blo 539803 30452507 := bstep (se 1 (by rfl) ⟨22839380, by rfl⟩ : syracuseStep 30452507 = 45678761) B45678761
theorem B2773183 : Blo 539803 2773183 := bstep (se 1 (by rfl) ⟨2079887, by rfl⟩ : syracuseStep 2773183 = 4159775) B4159775
theorem B2134766411 : Blo 539803 2134766411 := bstep (se 1 (by rfl) ⟨1601074808, by rfl⟩ : syracuseStep 2134766411 = 3202149617) B3202149617
theorem B18733295 : Blo 539803 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B2316701 : Blo 539803 2316701 := bstep (se 3 (by rfl) ⟨434381, by rfl⟩ : syracuseStep 2316701 = 868763) B868763
theorem B974015 : Blo 539803 974015 := bstep (se 1 (by rfl) ⟨730511, by rfl⟩ : syracuseStep 974015 = 1461023) B1461023
theorem B4693295 : Blo 539803 4693295 := bstep (se 1 (by rfl) ⟨3519971, by rfl⟩ : syracuseStep 4693295 = 7039943) B7039943
theorem B11116385 : Blo 539803 11116385 := bstep (se 2 (by rfl) ⟨4168644, by rfl⟩ : syracuseStep 11116385 = 8337289) B8337289
theorem B9224765 : Blo 539803 9224765 := bstep (se 3 (by rfl) ⟨1729643, by rfl⟩ : syracuseStep 9224765 = 3459287) B3459287
theorem B49955453 : Blo 539803 49955453 := bstep (se 3 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 49955453 = 18733295) B18733295
theorem B542491 : Blo 539803 542491 := bstep (se 1 (by rfl) ⟨406868, by rfl⟩ : syracuseStep 542491 = 813737) B813737
theorem B20301671 : Blo 539803 20301671 := bstep (se 1 (by rfl) ⟨15226253, by rfl⟩ : syracuseStep 20301671 = 30452507) B30452507
theorem B649343 : Blo 539803 649343 := bstep (se 1 (by rfl) ⟨487007, by rfl⟩ : syracuseStep 649343 = 974015) B974015
theorem B3697577 : Blo 539803 3697577 := bstep (se 2 (by rfl) ⟨1386591, by rfl⟩ : syracuseStep 3697577 = 2773183) B2773183
theorem B1544467 : Blo 539803 1544467 := bstep (se 1 (by rfl) ⟨1158350, by rfl⟩ : syracuseStep 1544467 = 2316701) B2316701
theorem B7410923 : Blo 539803 7410923 := bstep (se 1 (by rfl) ⟨5558192, by rfl⟩ : syracuseStep 7410923 = 11116385) B11116385
theorem B1423177607 : Blo 539803 1423177607 := bstep (se 1 (by rfl) ⟨1067383205, by rfl⟩ : syracuseStep 1423177607 = 2134766411) B2134766411
theorem B3128863 : Blo 539803 3128863 := bstep (se 1 (by rfl) ⟨2346647, by rfl⟩ : syracuseStep 3128863 = 4693295) B4693295
theorem B4940615 : Blo 539803 4940615 := bstep (se 1 (by rfl) ⟨3705461, by rfl⟩ : syracuseStep 4940615 = 7410923) B7410923
theorem B13534447 : Blo 539803 13534447 := bstep (se 1 (by rfl) ⟨10150835, by rfl⟩ : syracuseStep 13534447 = 20301671) B20301671
theorem B4171817 : Blo 539803 4171817 := bstep (se 2 (by rfl) ⟨1564431, by rfl⟩ : syracuseStep 4171817 = 3128863) B3128863
theorem B1731581 : Blo 539803 1731581 := bstep (se 3 (by rfl) ⟨324671, by rfl⟩ : syracuseStep 1731581 = 649343) B649343
theorem B2059289 : Blo 539803 2059289 := bstep (se 2 (by rfl) ⟨772233, by rfl⟩ : syracuseStep 2059289 = 1544467) B1544467
theorem B33303635 : Blo 539803 33303635 := bstep (se 1 (by rfl) ⟨24977726, by rfl⟩ : syracuseStep 33303635 = 49955453) B49955453
theorem B948785071 : Blo 539803 948785071 := bstep (se 1 (by rfl) ⟨711588803, by rfl⟩ : syracuseStep 948785071 = 1423177607) B1423177607
theorem B6149843 : Blo 539803 6149843 := bstep (se 1 (by rfl) ⟨4612382, by rfl⟩ : syracuseStep 6149843 = 9224765) B9224765
theorem B2465051 : Blo 539803 2465051 := bstep (se 1 (by rfl) ⟨1848788, by rfl⟩ : syracuseStep 2465051 = 3697577) B3697577
theorem B22202423 : Blo 539803 22202423 := bstep (se 1 (by rfl) ⟨16651817, by rfl⟩ : syracuseStep 22202423 = 33303635) B33303635
theorem B6573469 : Blo 539803 6573469 := bstep (se 3 (by rfl) ⟨1232525, by rfl⟩ : syracuseStep 6573469 = 2465051) B2465051
theorem B4099895 : Blo 539803 4099895 := bstep (se 1 (by rfl) ⟨3074921, by rfl⟩ : syracuseStep 4099895 = 6149843) B6149843
theorem B2781211 : Blo 539803 2781211 := bstep (se 1 (by rfl) ⟨2085908, by rfl⟩ : syracuseStep 2781211 = 4171817) B4171817
theorem B1372859 : Blo 539803 1372859 := bstep (se 1 (by rfl) ⟨1029644, by rfl⟩ : syracuseStep 1372859 = 2059289) B2059289
theorem B1265046761 : Blo 539803 1265046761 := bstep (se 2 (by rfl) ⟨474392535, by rfl⟩ : syracuseStep 1265046761 = 948785071) B948785071
theorem B18045929 : Blo 539803 18045929 := bstep (se 2 (by rfl) ⟨6767223, by rfl⟩ : syracuseStep 18045929 = 13534447) B13534447
theorem B3293743 : Blo 539803 3293743 := bstep (se 1 (by rfl) ⟨2470307, by rfl⟩ : syracuseStep 3293743 = 4940615) B4940615
theorem B1154387 : Blo 539803 1154387 := bstep (se 1 (by rfl) ⟨865790, by rfl⟩ : syracuseStep 1154387 = 1731581) B1731581
theorem B4391657 : Blo 539803 4391657 := bstep (se 2 (by rfl) ⟨1646871, by rfl⟩ : syracuseStep 4391657 = 3293743) B3293743
theorem B12030619 : Blo 539803 12030619 := bstep (se 1 (by rfl) ⟨9022964, by rfl⟩ : syracuseStep 12030619 = 18045929) B18045929
theorem B2733263 : Blo 539803 2733263 := bstep (se 1 (by rfl) ⟨2049947, by rfl⟩ : syracuseStep 2733263 = 4099895) B4099895
theorem B3708281 : Blo 539803 3708281 := bstep (se 2 (by rfl) ⟨1390605, by rfl⟩ : syracuseStep 3708281 = 2781211) B2781211
theorem B915239 : Blo 539803 915239 := bstep (se 1 (by rfl) ⟨686429, by rfl⟩ : syracuseStep 915239 = 1372859) B1372859
theorem B843364507 : Blo 539803 843364507 := bstep (se 1 (by rfl) ⟨632523380, by rfl⟩ : syracuseStep 843364507 = 1265046761) B1265046761
theorem B14801615 : Blo 539803 14801615 := bstep (se 1 (by rfl) ⟨11101211, by rfl⟩ : syracuseStep 14801615 = 22202423) B22202423
theorem B8764625 : Blo 539803 8764625 := bstep (se 2 (by rfl) ⟨3286734, by rfl⟩ : syracuseStep 8764625 = 6573469) B6573469
theorem B769591 : Blo 539803 769591 := bstep (se 1 (by rfl) ⟨577193, by rfl⟩ : syracuseStep 769591 = 1154387) B1154387
theorem B23372333 : Blo 539803 23372333 := bstep (se 3 (by rfl) ⟨4382312, by rfl⟩ : syracuseStep 23372333 = 8764625) B8764625
theorem B16040825 : Blo 539803 16040825 := bstep (se 2 (by rfl) ⟨6015309, by rfl⟩ : syracuseStep 16040825 = 12030619) B12030619
theorem B9888749 : Blo 539803 9888749 := bstep (se 3 (by rfl) ⟨1854140, by rfl⟩ : syracuseStep 9888749 = 3708281) B3708281
theorem B1026121 : Blo 539803 1026121 := bstep (se 2 (by rfl) ⟨384795, by rfl⟩ : syracuseStep 1026121 = 769591) B769591
theorem B1124486009 : Blo 539803 1124486009 := bstep (se 2 (by rfl) ⟨421682253, by rfl⟩ : syracuseStep 1124486009 = 843364507) B843364507
theorem B2927771 : Blo 539803 2927771 := bstep (se 1 (by rfl) ⟨2195828, by rfl⟩ : syracuseStep 2927771 = 4391657) B4391657
theorem B1822175 : Blo 539803 1822175 := bstep (se 1 (by rfl) ⟨1366631, by rfl⟩ : syracuseStep 1822175 = 2733263) B2733263
theorem B610159 : Blo 539803 610159 := bstep (se 1 (by rfl) ⟨457619, by rfl⟩ : syracuseStep 610159 = 915239) B915239
theorem B9867743 : Blo 539803 9867743 := bstep (se 1 (by rfl) ⟨7400807, by rfl⟩ : syracuseStep 9867743 = 14801615) B14801615
theorem B1368161 : Blo 539803 1368161 := bstep (se 2 (by rfl) ⟨513060, by rfl⟩ : syracuseStep 1368161 = 1026121) B1026121
theorem B6578495 : Blo 539803 6578495 := bstep (se 1 (by rfl) ⟨4933871, by rfl⟩ : syracuseStep 6578495 = 9867743) B9867743
theorem B15581555 : Blo 539803 15581555 := bstep (se 1 (by rfl) ⟨11686166, by rfl⟩ : syracuseStep 15581555 = 23372333) B23372333
theorem B1951847 : Blo 539803 1951847 := bstep (se 1 (by rfl) ⟨1463885, by rfl⟩ : syracuseStep 1951847 = 2927771) B2927771
theorem B1214783 : Blo 539803 1214783 := bstep (se 1 (by rfl) ⟨911087, by rfl⟩ : syracuseStep 1214783 = 1822175) B1822175
theorem B813545 : Blo 539803 813545 := bstep (se 2 (by rfl) ⟨305079, by rfl⟩ : syracuseStep 813545 = 610159) B610159
theorem B10693883 : Blo 539803 10693883 := bstep (se 1 (by rfl) ⟨8020412, by rfl⟩ : syracuseStep 10693883 = 16040825) B16040825
theorem B6592499 : Blo 539803 6592499 := bstep (se 1 (by rfl) ⟨4944374, by rfl⟩ : syracuseStep 6592499 = 9888749) B9888749
theorem B749657339 : Blo 539803 749657339 := bstep (se 1 (by rfl) ⟨562243004, by rfl⟩ : syracuseStep 749657339 = 1124486009) B1124486009
theorem B10387703 : Blo 539803 10387703 := bstep (se 1 (by rfl) ⟨7790777, by rfl⟩ : syracuseStep 10387703 = 15581555) B15581555
theorem B542363 : Blo 539803 542363 := bstep (se 1 (by rfl) ⟨406772, by rfl⟩ : syracuseStep 542363 = 813545) B813545
theorem B499771559 : Blo 539803 499771559 := bstep (se 1 (by rfl) ⟨374828669, by rfl⟩ : syracuseStep 499771559 = 749657339) B749657339
theorem B7129255 : Blo 539803 7129255 := bstep (se 1 (by rfl) ⟨5346941, by rfl⟩ : syracuseStep 7129255 = 10693883) B10693883
theorem B912107 : Blo 539803 912107 := bstep (se 1 (by rfl) ⟨684080, by rfl⟩ : syracuseStep 912107 = 1368161) B1368161
theorem B4385663 : Blo 539803 4385663 := bstep (se 1 (by rfl) ⟨3289247, by rfl⟩ : syracuseStep 4385663 = 6578495) B6578495
theorem B4394999 : Blo 539803 4394999 := bstep (se 1 (by rfl) ⟨3296249, by rfl⟩ : syracuseStep 4394999 = 6592499) B6592499
theorem B1301231 : Blo 539803 1301231 := bstep (se 1 (by rfl) ⟨975923, by rfl⟩ : syracuseStep 1301231 = 1951847) B1951847
theorem B809855 : Blo 539803 809855 := bstep (se 1 (by rfl) ⟨607391, by rfl⟩ : syracuseStep 809855 = 1214783) B1214783
theorem B608071 : Blo 539803 608071 := bstep (se 1 (by rfl) ⟨456053, by rfl⟩ : syracuseStep 608071 = 912107) B912107
theorem B6925135 : Blo 539803 6925135 := bstep (se 1 (by rfl) ⟨5193851, by rfl⟩ : syracuseStep 6925135 = 10387703) B10387703
theorem B9505673 : Blo 539803 9505673 := bstep (se 2 (by rfl) ⟨3564627, by rfl⟩ : syracuseStep 9505673 = 7129255) B7129255
theorem B333181039 : Blo 539803 333181039 := bstep (se 1 (by rfl) ⟨249885779, by rfl⟩ : syracuseStep 333181039 = 499771559) B499771559
theorem B3469949 : Blo 539803 3469949 := bstep (se 3 (by rfl) ⟨650615, by rfl⟩ : syracuseStep 3469949 = 1301231) B1301231
theorem B11719997 : Blo 539803 11719997 := bstep (se 3 (by rfl) ⟨2197499, by rfl⟩ : syracuseStep 11719997 = 4394999) B4394999
theorem B539903 : Blo 539803 539903 := bstep (se 1 (by rfl) ⟨404927, by rfl⟩ : syracuseStep 539903 = 809855) B809855
theorem B2923775 : Blo 539803 2923775 := bstep (se 1 (by rfl) ⟨2192831, by rfl⟩ : syracuseStep 2923775 = 4385663) B4385663
theorem B9233513 : Blo 539803 9233513 := bstep (se 2 (by rfl) ⟨3462567, by rfl⟩ : syracuseStep 9233513 = 6925135) B6925135
theorem B2313299 : Blo 539803 2313299 := bstep (se 1 (by rfl) ⟨1734974, by rfl⟩ : syracuseStep 2313299 = 3469949) B3469949
theorem B6337115 : Blo 539803 6337115 := bstep (se 1 (by rfl) ⟨4752836, by rfl⟩ : syracuseStep 6337115 = 9505673) B9505673
theorem B444241385 : Blo 539803 444241385 := bstep (se 2 (by rfl) ⟨166590519, by rfl⟩ : syracuseStep 444241385 = 333181039) B333181039
theorem B7813331 : Blo 539803 7813331 := bstep (se 1 (by rfl) ⟨5859998, by rfl⟩ : syracuseStep 7813331 = 11719997) B11719997
theorem B1949183 : Blo 539803 1949183 := bstep (se 1 (by rfl) ⟨1461887, by rfl⟩ : syracuseStep 1949183 = 2923775) B2923775
theorem B810761 : Blo 539803 810761 := bstep (se 2 (by rfl) ⟨304035, by rfl⟩ : syracuseStep 810761 = 608071) B608071
theorem B6168797 : Blo 539803 6168797 := bstep (se 3 (by rfl) ⟨1156649, by rfl⟩ : syracuseStep 6168797 = 2313299) B2313299
theorem B6155675 : Blo 539803 6155675 := bstep (se 1 (by rfl) ⟨4616756, by rfl⟩ : syracuseStep 6155675 = 9233513) B9233513
theorem B296160923 : Blo 539803 296160923 := bstep (se 1 (by rfl) ⟨222120692, by rfl⟩ : syracuseStep 296160923 = 444241385) B444241385
theorem B1299455 : Blo 539803 1299455 := bstep (se 1 (by rfl) ⟨974591, by rfl⟩ : syracuseStep 1299455 = 1949183) B1949183
theorem B4224743 : Blo 539803 4224743 := bstep (se 1 (by rfl) ⟨3168557, by rfl⟩ : syracuseStep 4224743 = 6337115) B6337115
theorem B5208887 : Blo 539803 5208887 := bstep (se 1 (by rfl) ⟨3906665, by rfl⟩ : syracuseStep 5208887 = 7813331) B7813331
theorem B540507 : Blo 539803 540507 := bstep (se 1 (by rfl) ⟨405380, by rfl⟩ : syracuseStep 540507 = 810761) B810761
theorem B4112531 : Blo 539803 4112531 := bstep (se 1 (by rfl) ⟨3084398, by rfl⟩ : syracuseStep 4112531 = 6168797) B6168797
theorem B197440615 : Blo 539803 197440615 := bstep (se 1 (by rfl) ⟨148080461, by rfl⟩ : syracuseStep 197440615 = 296160923) B296160923
theorem B866303 : Blo 539803 866303 := bstep (se 1 (by rfl) ⟨649727, by rfl⟩ : syracuseStep 866303 = 1299455) B1299455
theorem B2816495 : Blo 539803 2816495 := bstep (se 1 (by rfl) ⟨2112371, by rfl⟩ : syracuseStep 2816495 = 4224743) B4224743
theorem B3472591 : Blo 539803 3472591 := bstep (se 1 (by rfl) ⟨2604443, by rfl⟩ : syracuseStep 3472591 = 5208887) B5208887
theorem B4103783 : Blo 539803 4103783 := bstep (se 1 (by rfl) ⟨3077837, by rfl⟩ : syracuseStep 4103783 = 6155675) B6155675
theorem B4630121 : Blo 539803 4630121 := bstep (se 2 (by rfl) ⟨1736295, by rfl⟩ : syracuseStep 4630121 = 3472591) B3472591
theorem B1877663 : Blo 539803 1877663 := bstep (se 1 (by rfl) ⟨1408247, by rfl⟩ : syracuseStep 1877663 = 2816495) B2816495
theorem B577535 : Blo 539803 577535 := bstep (se 1 (by rfl) ⟨433151, by rfl⟩ : syracuseStep 577535 = 866303) B866303
theorem B263254153 : Blo 539803 263254153 := bstep (se 2 (by rfl) ⟨98720307, by rfl⟩ : syracuseStep 263254153 = 197440615) B197440615
theorem B2741687 : Blo 539803 2741687 := bstep (se 1 (by rfl) ⟨2056265, by rfl⟩ : syracuseStep 2741687 = 4112531) B4112531
theorem B2735855 : Blo 539803 2735855 := bstep (se 1 (by rfl) ⟨2051891, by rfl⟩ : syracuseStep 2735855 = 4103783) B4103783
theorem B1827791 : Blo 539803 1827791 := bstep (se 1 (by rfl) ⟨1370843, by rfl⟩ : syracuseStep 1827791 = 2741687) B2741687
theorem B351005537 : Blo 539803 351005537 := bstep (se 2 (by rfl) ⟨131627076, by rfl⟩ : syracuseStep 351005537 = 263254153) B263254153
theorem B1823903 : Blo 539803 1823903 := bstep (se 1 (by rfl) ⟨1367927, by rfl⟩ : syracuseStep 1823903 = 2735855) B2735855
theorem B3086747 : Blo 539803 3086747 := bstep (se 1 (by rfl) ⟨2315060, by rfl⟩ : syracuseStep 3086747 = 4630121) B4630121
theorem B1251775 : Blo 539803 1251775 := bstep (se 1 (by rfl) ⟨938831, by rfl⟩ : syracuseStep 1251775 = 1877663) B1877663
theorem B1540093 : Blo 539803 1540093 := bstep (se 3 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 1540093 = 577535) B577535
theorem B2057831 : Blo 539803 2057831 := bstep (se 1 (by rfl) ⟨1543373, by rfl⟩ : syracuseStep 2057831 = 3086747) B3086747
theorem B1215935 : Blo 539803 1215935 := bstep (se 1 (by rfl) ⟨911951, by rfl⟩ : syracuseStep 1215935 = 1823903) B1823903
theorem B2053457 : Blo 539803 2053457 := bstep (se 2 (by rfl) ⟨770046, by rfl⟩ : syracuseStep 2053457 = 1540093) B1540093
theorem B1669033 : Blo 539803 1669033 := bstep (se 2 (by rfl) ⟨625887, by rfl⟩ : syracuseStep 1669033 = 1251775) B1251775
theorem B1218527 : Blo 539803 1218527 := bstep (se 1 (by rfl) ⟨913895, by rfl⟩ : syracuseStep 1218527 = 1827791) B1827791
theorem B234003691 : Blo 539803 234003691 := bstep (se 1 (by rfl) ⟨175502768, by rfl⟩ : syracuseStep 234003691 = 351005537) B351005537
theorem B1368971 : Blo 539803 1368971 := bstep (se 1 (by rfl) ⟨1026728, by rfl⟩ : syracuseStep 1368971 = 2053457) B2053457
theorem B812351 : Blo 539803 812351 := bstep (se 1 (by rfl) ⟨609263, by rfl⟩ : syracuseStep 812351 = 1218527) B1218527
theorem B1371887 : Blo 539803 1371887 := bstep (se 1 (by rfl) ⟨1028915, by rfl⟩ : syracuseStep 1371887 = 2057831) B2057831
theorem B312004921 : Blo 539803 312004921 := bstep (se 2 (by rfl) ⟨117001845, by rfl⟩ : syracuseStep 312004921 = 234003691) B234003691
theorem B2225377 : Blo 539803 2225377 := bstep (se 2 (by rfl) ⟨834516, by rfl⟩ : syracuseStep 2225377 = 1669033) B1669033
theorem B810623 : Blo 539803 810623 := bstep (se 1 (by rfl) ⟨607967, by rfl⟩ : syracuseStep 810623 = 1215935) B1215935
theorem B416006561 : Blo 539803 416006561 := bstep (se 2 (by rfl) ⟨156002460, by rfl⟩ : syracuseStep 416006561 = 312004921) B312004921
theorem B541567 : Blo 539803 541567 := bstep (se 1 (by rfl) ⟨406175, by rfl⟩ : syracuseStep 541567 = 812351) B812351
theorem B912647 : Blo 539803 912647 := bstep (se 1 (by rfl) ⟨684485, by rfl⟩ : syracuseStep 912647 = 1368971) B1368971
theorem B914591 : Blo 539803 914591 := bstep (se 1 (by rfl) ⟨685943, by rfl⟩ : syracuseStep 914591 = 1371887) B1371887
theorem B11868677 : Blo 539803 11868677 := bstep (se 4 (by rfl) ⟨1112688, by rfl⟩ : syracuseStep 11868677 = 2225377) B2225377
theorem B540415 : Blo 539803 540415 := bstep (se 1 (by rfl) ⟨405311, by rfl⟩ : syracuseStep 540415 = 810623) B810623
theorem B608431 : Blo 539803 608431 := bstep (se 1 (by rfl) ⟨456323, by rfl⟩ : syracuseStep 608431 = 912647) B912647
theorem B609727 : Blo 539803 609727 := bstep (se 1 (by rfl) ⟨457295, by rfl⟩ : syracuseStep 609727 = 914591) B914591
theorem B1109350829 : Blo 539803 1109350829 := bstep (se 3 (by rfl) ⟨208003280, by rfl⟩ : syracuseStep 1109350829 = 416006561) B416006561
theorem B7912451 : Blo 539803 7912451 := bstep (se 1 (by rfl) ⟨5934338, by rfl⟩ : syracuseStep 7912451 = 11868677) B11868677
theorem B811241 : Blo 539803 811241 := bstep (se 2 (by rfl) ⟨304215, by rfl⟩ : syracuseStep 811241 = 608431) B608431
theorem B739567219 : Blo 539803 739567219 := bstep (se 1 (by rfl) ⟨554675414, by rfl⟩ : syracuseStep 739567219 = 1109350829) B1109350829
theorem B812969 : Blo 539803 812969 := bstep (se 2 (by rfl) ⟨304863, by rfl⟩ : syracuseStep 812969 = 609727) B609727
theorem B21099869 : Blo 539803 21099869 := bstep (se 3 (by rfl) ⟨3956225, by rfl⟩ : syracuseStep 21099869 = 7912451) B7912451
theorem B540827 : Blo 539803 540827 := bstep (se 1 (by rfl) ⟨405620, by rfl⟩ : syracuseStep 540827 = 811241) B811241
theorem B14066579 : Blo 539803 14066579 := bstep (se 1 (by rfl) ⟨10549934, by rfl⟩ : syracuseStep 14066579 = 21099869) B21099869
theorem B541979 : Blo 539803 541979 := bstep (se 1 (by rfl) ⟨406484, by rfl⟩ : syracuseStep 541979 = 812969) B812969
theorem B986089625 : Blo 539803 986089625 := bstep (se 2 (by rfl) ⟨369783609, by rfl⟩ : syracuseStep 986089625 = 739567219) B739567219
theorem B657393083 : Blo 539803 657393083 := bstep (se 1 (by rfl) ⟨493044812, by rfl⟩ : syracuseStep 657393083 = 986089625) B986089625
theorem B37510877 : Blo 539803 37510877 := bstep (se 3 (by rfl) ⟨7033289, by rfl⟩ : syracuseStep 37510877 = 14066579) B14066579
theorem B100029005 : Blo 539803 100029005 := bstep (se 3 (by rfl) ⟨18755438, by rfl⟩ : syracuseStep 100029005 = 37510877) B37510877
theorem B438262055 : Blo 539803 438262055 := bstep (se 1 (by rfl) ⟨328696541, by rfl⟩ : syracuseStep 438262055 = 657393083) B657393083
theorem B66686003 : Blo 539803 66686003 := bstep (se 1 (by rfl) ⟨50014502, by rfl⟩ : syracuseStep 66686003 = 100029005) B100029005
theorem B292174703 : Blo 539803 292174703 := bstep (se 1 (by rfl) ⟨219131027, by rfl⟩ : syracuseStep 292174703 = 438262055) B438262055
theorem B194783135 : Blo 539803 194783135 := bstep (se 1 (by rfl) ⟨146087351, by rfl⟩ : syracuseStep 194783135 = 292174703) B292174703
theorem B44457335 : Blo 539803 44457335 := bstep (se 1 (by rfl) ⟨33343001, by rfl⟩ : syracuseStep 44457335 = 66686003) B66686003
theorem B29638223 : Blo 539803 29638223 := bstep (se 1 (by rfl) ⟨22228667, by rfl⟩ : syracuseStep 29638223 = 44457335) B44457335
theorem B519421693 : Blo 539803 519421693 := bstep (se 3 (by rfl) ⟨97391567, by rfl⟩ : syracuseStep 519421693 = 194783135) B194783135
theorem B692562257 : Blo 539803 692562257 := bstep (se 2 (by rfl) ⟨259710846, by rfl⟩ : syracuseStep 692562257 = 519421693) B519421693
theorem B19758815 : Blo 539803 19758815 := bstep (se 1 (by rfl) ⟨14819111, by rfl⟩ : syracuseStep 19758815 = 29638223) B29638223
theorem B461708171 : Blo 539803 461708171 := bstep (se 1 (by rfl) ⟨346281128, by rfl⟩ : syracuseStep 461708171 = 692562257) B692562257
theorem B13172543 : Blo 539803 13172543 := bstep (se 1 (by rfl) ⟨9879407, by rfl⟩ : syracuseStep 13172543 = 19758815) B19758815
theorem B307805447 : Blo 539803 307805447 := bstep (se 1 (by rfl) ⟨230854085, by rfl⟩ : syracuseStep 307805447 = 461708171) B461708171
theorem B8781695 : Blo 539803 8781695 := bstep (se 1 (by rfl) ⟨6586271, by rfl⟩ : syracuseStep 8781695 = 13172543) B13172543
theorem B205203631 : Blo 539803 205203631 := bstep (se 1 (by rfl) ⟨153902723, by rfl⟩ : syracuseStep 205203631 = 307805447) B307805447
theorem B5854463 : Blo 539803 5854463 := bstep (se 1 (by rfl) ⟨4390847, by rfl⟩ : syracuseStep 5854463 = 8781695) B8781695
theorem B273604841 : Blo 539803 273604841 := bstep (se 2 (by rfl) ⟨102601815, by rfl⟩ : syracuseStep 273604841 = 205203631) B205203631
theorem B3902975 : Blo 539803 3902975 := bstep (se 1 (by rfl) ⟨2927231, by rfl⟩ : syracuseStep 3902975 = 5854463) B5854463
theorem B182403227 : Blo 539803 182403227 := bstep (se 1 (by rfl) ⟨136802420, by rfl⟩ : syracuseStep 182403227 = 273604841) B273604841
theorem B2601983 : Blo 539803 2601983 := bstep (se 1 (by rfl) ⟨1951487, by rfl⟩ : syracuseStep 2601983 = 3902975) B3902975
theorem B121602151 : Blo 539803 121602151 := bstep (se 1 (by rfl) ⟨91201613, by rfl⟩ : syracuseStep 121602151 = 182403227) B182403227
theorem B6938621 : Blo 539803 6938621 := bstep (se 3 (by rfl) ⟨1300991, by rfl⟩ : syracuseStep 6938621 = 2601983) B2601983
theorem B648544805 : Blo 539803 648544805 := bstep (se 4 (by rfl) ⟨60801075, by rfl⟩ : syracuseStep 648544805 = 121602151) B121602151
theorem B4625747 : Blo 539803 4625747 := bstep (se 1 (by rfl) ⟨3469310, by rfl⟩ : syracuseStep 4625747 = 6938621) B6938621
theorem B3083831 : Blo 539803 3083831 := bstep (se 1 (by rfl) ⟨2312873, by rfl⟩ : syracuseStep 3083831 = 4625747) B4625747
theorem B432363203 : Blo 539803 432363203 := bstep (se 1 (by rfl) ⟨324272402, by rfl⟩ : syracuseStep 432363203 = 648544805) B648544805
theorem B288242135 : Blo 539803 288242135 := bstep (se 1 (by rfl) ⟨216181601, by rfl⟩ : syracuseStep 288242135 = 432363203) B432363203
theorem B2055887 : Blo 539803 2055887 := bstep (se 1 (by rfl) ⟨1541915, by rfl⟩ : syracuseStep 2055887 = 3083831) B3083831
theorem B192161423 : Blo 539803 192161423 := bstep (se 1 (by rfl) ⟨144121067, by rfl⟩ : syracuseStep 192161423 = 288242135) B288242135
theorem B1370591 : Blo 539803 1370591 := bstep (se 1 (by rfl) ⟨1027943, by rfl⟩ : syracuseStep 1370591 = 2055887) B2055887
theorem B128107615 : Blo 539803 128107615 := bstep (se 1 (by rfl) ⟨96080711, by rfl⟩ : syracuseStep 128107615 = 192161423) B192161423
theorem B913727 : Blo 539803 913727 := bstep (se 1 (by rfl) ⟨685295, by rfl⟩ : syracuseStep 913727 = 1370591) B1370591
theorem B609151 : Blo 539803 609151 := bstep (se 1 (by rfl) ⟨456863, by rfl⟩ : syracuseStep 609151 = 913727) B913727
theorem B170810153 : Blo 539803 170810153 := bstep (se 2 (by rfl) ⟨64053807, by rfl⟩ : syracuseStep 170810153 = 128107615) B128107615
theorem B812201 : Blo 539803 812201 := bstep (se 2 (by rfl) ⟨304575, by rfl⟩ : syracuseStep 812201 = 609151) B609151
theorem B113873435 : Blo 539803 113873435 := bstep (se 1 (by rfl) ⟨85405076, by rfl⟩ : syracuseStep 113873435 = 170810153) B170810153
theorem B75915623 : Blo 539803 75915623 := bstep (se 1 (by rfl) ⟨56936717, by rfl⟩ : syracuseStep 75915623 = 113873435) B113873435
theorem B541467 : Blo 539803 541467 := bstep (se 1 (by rfl) ⟨406100, by rfl⟩ : syracuseStep 541467 = 812201) B812201
theorem B50610415 : Blo 539803 50610415 := bstep (se 1 (by rfl) ⟨37957811, by rfl⟩ : syracuseStep 50610415 = 75915623) B75915623
theorem B67480553 : Blo 539803 67480553 := bstep (se 2 (by rfl) ⟨25305207, by rfl⟩ : syracuseStep 67480553 = 50610415) B50610415
theorem B44987035 : Blo 539803 44987035 := bstep (se 1 (by rfl) ⟨33740276, by rfl⟩ : syracuseStep 44987035 = 67480553) B67480553
theorem B59982713 : Blo 539803 59982713 := bstep (se 2 (by rfl) ⟨22493517, by rfl⟩ : syracuseStep 59982713 = 44987035) B44987035
theorem B39988475 : Blo 539803 39988475 := bstep (se 1 (by rfl) ⟨29991356, by rfl⟩ : syracuseStep 39988475 = 59982713) B59982713
theorem B26658983 : Blo 539803 26658983 := bstep (se 1 (by rfl) ⟨19994237, by rfl⟩ : syracuseStep 26658983 = 39988475) B39988475
theorem B71090621 : Blo 539803 71090621 := bstep (se 3 (by rfl) ⟨13329491, by rfl⟩ : syracuseStep 71090621 = 26658983) B26658983
theorem B47393747 : Blo 539803 47393747 := bstep (se 1 (by rfl) ⟨35545310, by rfl⟩ : syracuseStep 47393747 = 71090621) B71090621
theorem B31595831 : Blo 539803 31595831 := bstep (se 1 (by rfl) ⟨23696873, by rfl⟩ : syracuseStep 31595831 = 47393747) B47393747
theorem B21063887 : Blo 539803 21063887 := bstep (se 1 (by rfl) ⟨15797915, by rfl⟩ : syracuseStep 21063887 = 31595831) B31595831
theorem B14042591 : Blo 539803 14042591 := bstep (se 1 (by rfl) ⟨10531943, by rfl⟩ : syracuseStep 14042591 = 21063887) B21063887
theorem B9361727 : Blo 539803 9361727 := bstep (se 1 (by rfl) ⟨7021295, by rfl⟩ : syracuseStep 9361727 = 14042591) B14042591
theorem B6241151 : Blo 539803 6241151 := bstep (se 1 (by rfl) ⟨4680863, by rfl⟩ : syracuseStep 6241151 = 9361727) B9361727
theorem B4160767 : Blo 539803 4160767 := bstep (se 1 (by rfl) ⟨3120575, by rfl⟩ : syracuseStep 4160767 = 6241151) B6241151
theorem B5547689 : Blo 539803 5547689 := bstep (se 2 (by rfl) ⟨2080383, by rfl⟩ : syracuseStep 5547689 = 4160767) B4160767
theorem B3698459 : Blo 539803 3698459 := bstep (se 1 (by rfl) ⟨2773844, by rfl⟩ : syracuseStep 3698459 = 5547689) B5547689
theorem B2465639 : Blo 539803 2465639 := bstep (se 1 (by rfl) ⟨1849229, by rfl⟩ : syracuseStep 2465639 = 3698459) B3698459
theorem B1643759 : Blo 539803 1643759 := bstep (se 1 (by rfl) ⟨1232819, by rfl⟩ : syracuseStep 1643759 = 2465639) B2465639
theorem B1095839 : Blo 539803 1095839 := bstep (se 1 (by rfl) ⟨821879, by rfl⟩ : syracuseStep 1095839 = 1643759) B1643759
theorem B730559 : Blo 539803 730559 := bstep (se 1 (by rfl) ⟨547919, by rfl⟩ : syracuseStep 730559 = 1095839) B1095839
theorem B1948157 : Blo 539803 1948157 := bstep (se 3 (by rfl) ⟨365279, by rfl⟩ : syracuseStep 1948157 = 730559) B730559
theorem B1298771 : Blo 539803 1298771 := bstep (se 1 (by rfl) ⟨974078, by rfl⟩ : syracuseStep 1298771 = 1948157) B1948157
theorem B865847 : Blo 539803 865847 := bstep (se 1 (by rfl) ⟨649385, by rfl⟩ : syracuseStep 865847 = 1298771) B1298771
theorem B2308925 : Blo 539803 2308925 := bstep (se 3 (by rfl) ⟨432923, by rfl⟩ : syracuseStep 2308925 = 865847) B865847
theorem B6157133 : Blo 539803 6157133 := bstep (se 3 (by rfl) ⟨1154462, by rfl⟩ : syracuseStep 6157133 = 2308925) B2308925
theorem B4104755 : Blo 539803 4104755 := bstep (se 1 (by rfl) ⟨3078566, by rfl⟩ : syracuseStep 4104755 = 6157133) B6157133
theorem B2736503 : Blo 539803 2736503 := bstep (se 1 (by rfl) ⟨2052377, by rfl⟩ : syracuseStep 2736503 = 4104755) B4104755
theorem B1824335 : Blo 539803 1824335 := bstep (se 1 (by rfl) ⟨1368251, by rfl⟩ : syracuseStep 1824335 = 2736503) B2736503
theorem B1216223 : Blo 539803 1216223 := bstep (se 1 (by rfl) ⟨912167, by rfl⟩ : syracuseStep 1216223 = 1824335) B1824335
theorem B810815 : Blo 539803 810815 := bstep (se 1 (by rfl) ⟨608111, by rfl⟩ : syracuseStep 810815 = 1216223) B1216223
theorem B540543 : Blo 539803 540543 := bstep (se 1 (by rfl) ⟨405407, by rfl⟩ : syracuseStep 540543 = 810815) B810815

theorem C0 (j : ℕ) (h1 : 134950 ≤ j) (h2 : j ≤ 135649) : Blo 539803 (4 * j + 3) := by
  interval_cases j
  · exact B539803
  · exact B539807
  · exact B539811
  · exact B539815
  · exact B539819
  · exact B539823
  · exact B539827
  · exact B539831
  · exact B539835
  · exact B539839
  · exact B539843
  · exact B539847
  · exact B539851
  · exact B539855
  · exact B539859
  · exact B539863
  · exact B539867
  · exact B539871
  · exact B539875
  · exact B539879
  · exact B539883
  · exact B539887
  · exact B539891
  · exact B539895
  · exact B539899
  · exact B539903
  · exact B539907
  · exact B539911
  · exact B539915
  · exact B539919
  · exact B539923
  · exact B539927
  · exact B539931
  · exact B539935
  · exact B539939
  · exact B539943
  · exact B539947
  · exact B539951
  · exact B539955
  · exact B539959
  · exact B539963
  · exact B539967
  · exact B539971
  · exact B539975
  · exact B539979
  · exact B539983
  · exact B539987
  · exact B539991
  · exact B539995
  · exact B539999
  · exact B540003
  · exact B540007
  · exact B540011
  · exact B540015
  · exact B540019
  · exact B540023
  · exact B540027
  · exact B540031
  · exact B540035
  · exact B540039
  · exact B540043
  · exact B540047
  · exact B540051
  · exact B540055
  · exact B540059
  · exact B540063
  · exact B540067
  · exact B540071
  · exact B540075
  · exact B540079
  · exact B540083
  · exact B540087
  · exact B540091
  · exact B540095
  · exact B540099
  · exact B540103
  · exact B540107
  · exact B540111
  · exact B540115
  · exact B540119
  · exact B540123
  · exact B540127
  · exact B540131
  · exact B540135
  · exact B540139
  · exact B540143
  · exact B540147
  · exact B540151
  · exact B540155
  · exact B540159
  · exact B540163
  · exact B540167
  · exact B540171
  · exact B540175
  · exact B540179
  · exact B540183
  · exact B540187
  · exact B540191
  · exact B540195
  · exact B540199
  · exact B540203
  · exact B540207
  · exact B540211
  · exact B540215
  · exact B540219
  · exact B540223
  · exact B540227
  · exact B540231
  · exact B540235
  · exact B540239
  · exact B540243
  · exact B540247
  · exact B540251
  · exact B540255
  · exact B540259
  · exact B540263
  · exact B540267
  · exact B540271
  · exact B540275
  · exact B540279
  · exact B540283
  · exact B540287
  · exact B540291
  · exact B540295
  · exact B540299
  · exact B540303
  · exact B540307
  · exact B540311
  · exact B540315
  · exact B540319
  · exact B540323
  · exact B540327
  · exact B540331
  · exact B540335
  · exact B540339
  · exact B540343
  · exact B540347
  · exact B540351
  · exact B540355
  · exact B540359
  · exact B540363
  · exact B540367
  · exact B540371
  · exact B540375
  · exact B540379
  · exact B540383
  · exact B540387
  · exact B540391
  · exact B540395
  · exact B540399
  · exact B540403
  · exact B540407
  · exact B540411
  · exact B540415
  · exact B540419
  · exact B540423
  · exact B540427
  · exact B540431
  · exact B540435
  · exact B540439
  · exact B540443
  · exact B540447
  · exact B540451
  · exact B540455
  · exact B540459
  · exact B540463
  · exact B540467
  · exact B540471
  · exact B540475
  · exact B540479
  · exact B540483
  · exact B540487
  · exact B540491
  · exact B540495
  · exact B540499
  · exact B540503
  · exact B540507
  · exact B540511
  · exact B540515
  · exact B540519
  · exact B540523
  · exact B540527
  · exact B540531
  · exact B540535
  · exact B540539
  · exact B540543
  · exact B540547
  · exact B540551
  · exact B540555
  · exact B540559
  · exact B540563
  · exact B540567
  · exact B540571
  · exact B540575
  · exact B540579
  · exact B540583
  · exact B540587
  · exact B540591
  · exact B540595
  · exact B540599
  · exact B540603
  · exact B540607
  · exact B540611
  · exact B540615
  · exact B540619
  · exact B540623
  · exact B540627
  · exact B540631
  · exact B540635
  · exact B540639
  · exact B540643
  · exact B540647
  · exact B540651
  · exact B540655
  · exact B540659
  · exact B540663
  · exact B540667
  · exact B540671
  · exact B540675
  · exact B540679
  · exact B540683
  · exact B540687
  · exact B540691
  · exact B540695
  · exact B540699
  · exact B540703
  · exact B540707
  · exact B540711
  · exact B540715
  · exact B540719
  · exact B540723
  · exact B540727
  · exact B540731
  · exact B540735
  · exact B540739
  · exact B540743
  · exact B540747
  · exact B540751
  · exact B540755
  · exact B540759
  · exact B540763
  · exact B540767
  · exact B540771
  · exact B540775
  · exact B540779
  · exact B540783
  · exact B540787
  · exact B540791
  · exact B540795
  · exact B540799
  · exact B540803
  · exact B540807
  · exact B540811
  · exact B540815
  · exact B540819
  · exact B540823
  · exact B540827
  · exact B540831
  · exact B540835
  · exact B540839
  · exact B540843
  · exact B540847
  · exact B540851
  · exact B540855
  · exact B540859
  · exact B540863
  · exact B540867
  · exact B540871
  · exact B540875
  · exact B540879
  · exact B540883
  · exact B540887
  · exact B540891
  · exact B540895
  · exact B540899
  · exact B540903
  · exact B540907
  · exact B540911
  · exact B540915
  · exact B540919
  · exact B540923
  · exact B540927
  · exact B540931
  · exact B540935
  · exact B540939
  · exact B540943
  · exact B540947
  · exact B540951
  · exact B540955
  · exact B540959
  · exact B540963
  · exact B540967
  · exact B540971
  · exact B540975
  · exact B540979
  · exact B540983
  · exact B540987
  · exact B540991
  · exact B540995
  · exact B540999
  · exact B541003
  · exact B541007
  · exact B541011
  · exact B541015
  · exact B541019
  · exact B541023
  · exact B541027
  · exact B541031
  · exact B541035
  · exact B541039
  · exact B541043
  · exact B541047
  · exact B541051
  · exact B541055
  · exact B541059
  · exact B541063
  · exact B541067
  · exact B541071
  · exact B541075
  · exact B541079
  · exact B541083
  · exact B541087
  · exact B541091
  · exact B541095
  · exact B541099
  · exact B541103
  · exact B541107
  · exact B541111
  · exact B541115
  · exact B541119
  · exact B541123
  · exact B541127
  · exact B541131
  · exact B541135
  · exact B541139
  · exact B541143
  · exact B541147
  · exact B541151
  · exact B541155
  · exact B541159
  · exact B541163
  · exact B541167
  · exact B541171
  · exact B541175
  · exact B541179
  · exact B541183
  · exact B541187
  · exact B541191
  · exact B541195
  · exact B541199
  · exact B541203
  · exact B541207
  · exact B541211
  · exact B541215
  · exact B541219
  · exact B541223
  · exact B541227
  · exact B541231
  · exact B541235
  · exact B541239
  · exact B541243
  · exact B541247
  · exact B541251
  · exact B541255
  · exact B541259
  · exact B541263
  · exact B541267
  · exact B541271
  · exact B541275
  · exact B541279
  · exact B541283
  · exact B541287
  · exact B541291
  · exact B541295
  · exact B541299
  · exact B541303
  · exact B541307
  · exact B541311
  · exact B541315
  · exact B541319
  · exact B541323
  · exact B541327
  · exact B541331
  · exact B541335
  · exact B541339
  · exact B541343
  · exact B541347
  · exact B541351
  · exact B541355
  · exact B541359
  · exact B541363
  · exact B541367
  · exact B541371
  · exact B541375
  · exact B541379
  · exact B541383
  · exact B541387
  · exact B541391
  · exact B541395
  · exact B541399
  · exact B541403
  · exact B541407
  · exact B541411
  · exact B541415
  · exact B541419
  · exact B541423
  · exact B541427
  · exact B541431
  · exact B541435
  · exact B541439
  · exact B541443
  · exact B541447
  · exact B541451
  · exact B541455
  · exact B541459
  · exact B541463
  · exact B541467
  · exact B541471
  · exact B541475
  · exact B541479
  · exact B541483
  · exact B541487
  · exact B541491
  · exact B541495
  · exact B541499
  · exact B541503
  · exact B541507
  · exact B541511
  · exact B541515
  · exact B541519
  · exact B541523
  · exact B541527
  · exact B541531
  · exact B541535
  · exact B541539
  · exact B541543
  · exact B541547
  · exact B541551
  · exact B541555
  · exact B541559
  · exact B541563
  · exact B541567
  · exact B541571
  · exact B541575
  · exact B541579
  · exact B541583
  · exact B541587
  · exact B541591
  · exact B541595
  · exact B541599
  · exact B541603
  · exact B541607
  · exact B541611
  · exact B541615
  · exact B541619
  · exact B541623
  · exact B541627
  · exact B541631
  · exact B541635
  · exact B541639
  · exact B541643
  · exact B541647
  · exact B541651
  · exact B541655
  · exact B541659
  · exact B541663
  · exact B541667
  · exact B541671
  · exact B541675
  · exact B541679
  · exact B541683
  · exact B541687
  · exact B541691
  · exact B541695
  · exact B541699
  · exact B541703
  · exact B541707
  · exact B541711
  · exact B541715
  · exact B541719
  · exact B541723
  · exact B541727
  · exact B541731
  · exact B541735
  · exact B541739
  · exact B541743
  · exact B541747
  · exact B541751
  · exact B541755
  · exact B541759
  · exact B541763
  · exact B541767
  · exact B541771
  · exact B541775
  · exact B541779
  · exact B541783
  · exact B541787
  · exact B541791
  · exact B541795
  · exact B541799
  · exact B541803
  · exact B541807
  · exact B541811
  · exact B541815
  · exact B541819
  · exact B541823
  · exact B541827
  · exact B541831
  · exact B541835
  · exact B541839
  · exact B541843
  · exact B541847
  · exact B541851
  · exact B541855
  · exact B541859
  · exact B541863
  · exact B541867
  · exact B541871
  · exact B541875
  · exact B541879
  · exact B541883
  · exact B541887
  · exact B541891
  · exact B541895
  · exact B541899
  · exact B541903
  · exact B541907
  · exact B541911
  · exact B541915
  · exact B541919
  · exact B541923
  · exact B541927
  · exact B541931
  · exact B541935
  · exact B541939
  · exact B541943
  · exact B541947
  · exact B541951
  · exact B541955
  · exact B541959
  · exact B541963
  · exact B541967
  · exact B541971
  · exact B541975
  · exact B541979
  · exact B541983
  · exact B541987
  · exact B541991
  · exact B541995
  · exact B541999
  · exact B542003
  · exact B542007
  · exact B542011
  · exact B542015
  · exact B542019
  · exact B542023
  · exact B542027
  · exact B542031
  · exact B542035
  · exact B542039
  · exact B542043
  · exact B542047
  · exact B542051
  · exact B542055
  · exact B542059
  · exact B542063
  · exact B542067
  · exact B542071
  · exact B542075
  · exact B542079
  · exact B542083
  · exact B542087
  · exact B542091
  · exact B542095
  · exact B542099
  · exact B542103
  · exact B542107
  · exact B542111
  · exact B542115
  · exact B542119
  · exact B542123
  · exact B542127
  · exact B542131
  · exact B542135
  · exact B542139
  · exact B542143
  · exact B542147
  · exact B542151
  · exact B542155
  · exact B542159
  · exact B542163
  · exact B542167
  · exact B542171
  · exact B542175
  · exact B542179
  · exact B542183
  · exact B542187
  · exact B542191
  · exact B542195
  · exact B542199
  · exact B542203
  · exact B542207
  · exact B542211
  · exact B542215
  · exact B542219
  · exact B542223
  · exact B542227
  · exact B542231
  · exact B542235
  · exact B542239
  · exact B542243
  · exact B542247
  · exact B542251
  · exact B542255
  · exact B542259
  · exact B542263
  · exact B542267
  · exact B542271
  · exact B542275
  · exact B542279
  · exact B542283
  · exact B542287
  · exact B542291
  · exact B542295
  · exact B542299
  · exact B542303
  · exact B542307
  · exact B542311
  · exact B542315
  · exact B542319
  · exact B542323
  · exact B542327
  · exact B542331
  · exact B542335
  · exact B542339
  · exact B542343
  · exact B542347
  · exact B542351
  · exact B542355
  · exact B542359
  · exact B542363
  · exact B542367
  · exact B542371
  · exact B542375
  · exact B542379
  · exact B542383
  · exact B542387
  · exact B542391
  · exact B542395
  · exact B542399
  · exact B542403
  · exact B542407
  · exact B542411
  · exact B542415
  · exact B542419
  · exact B542423
  · exact B542427
  · exact B542431
  · exact B542435
  · exact B542439
  · exact B542443
  · exact B542447
  · exact B542451
  · exact B542455
  · exact B542459
  · exact B542463
  · exact B542467
  · exact B542471
  · exact B542475
  · exact B542479
  · exact B542483
  · exact B542487
  · exact B542491
  · exact B542495
  · exact B542499
  · exact B542503
  · exact B542507
  · exact B542511
  · exact B542515
  · exact B542519
  · exact B542523
  · exact B542527
  · exact B542531
  · exact B542535
  · exact B542539
  · exact B542543
  · exact B542547
  · exact B542551
  · exact B542555
  · exact B542559
  · exact B542563
  · exact B542567
  · exact B542571
  · exact B542575
  · exact B542579
  · exact B542583
  · exact B542587
  · exact B542591
  · exact B542595
  · exact B542599

theorem C1 (j : ℕ) (h1 : 135650 ≤ j) (h2 : j ≤ 135700) : Blo 539803 (4 * j + 3) := by
  interval_cases j
  · exact B542603
  · exact B542607
  · exact B542611
  · exact B542615
  · exact B542619
  · exact B542623
  · exact B542627
  · exact B542631
  · exact B542635
  · exact B542639
  · exact B542643
  · exact B542647
  · exact B542651
  · exact B542655
  · exact B542659
  · exact B542663
  · exact B542667
  · exact B542671
  · exact B542675
  · exact B542679
  · exact B542683
  · exact B542687
  · exact B542691
  · exact B542695
  · exact B542699
  · exact B542703
  · exact B542707
  · exact B542711
  · exact B542715
  · exact B542719
  · exact B542723
  · exact B542727
  · exact B542731
  · exact B542735
  · exact B542739
  · exact B542743
  · exact B542747
  · exact B542751
  · exact B542755
  · exact B542759
  · exact B542763
  · exact B542767
  · exact B542771
  · exact B542775
  · exact B542779
  · exact B542783
  · exact B542787
  · exact B542791
  · exact B542795
  · exact B542799
  · exact B542803

theorem solution (m : ℕ) (hlo : 539803 ≤ m) (hhi : m ≤ 542803) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 134950 ≤ j := by omega
    have hj2 : j ≤ 135700 := by omega
    have hb : Blo 539803 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 135650 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
