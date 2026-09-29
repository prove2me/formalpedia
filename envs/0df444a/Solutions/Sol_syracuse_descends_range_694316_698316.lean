-- Prove2me | solution 1 for syracuse_descends_range_694316_698316
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:57.986424+00:00
-- url     : https://prove2.me/submissions/ef14fede-044f-4cf5-9fba-5f830c066f36

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


theorem B917509 : Blo 694316 917509 := bbase (se 4 (by rfl) ⟨86016, by rfl⟩ : syracuseStep 917509 = 172033) (by norm_num)
theorem B753725 : Blo 694316 753725 := bbase (se 3 (by rfl) ⟨141323, by rfl⟩ : syracuseStep 753725 = 282647) (by norm_num)
theorem B2228485 : Blo 694316 2228485 := bbase (se 4 (by rfl) ⟨208920, by rfl⟩ : syracuseStep 2228485 = 417841) (by norm_num)
theorem B5374421 : Blo 694316 5374421 := bbase (se 7 (by rfl) ⟨62981, by rfl⟩ : syracuseStep 5374421 = 125963) (by norm_num)
theorem B1409501 : Blo 694316 1409501 := bbase (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) (by norm_num)
theorem B1671749 : Blo 694316 1671749 := bbase (se 4 (by rfl) ⟨156726, by rfl⟩ : syracuseStep 1671749 = 313453) (by norm_num)
theorem B1114717 : Blo 694316 1114717 := bbase (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) (by norm_num)
theorem B3572437 : Blo 694316 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B1671941 : Blo 694316 1671941 := bbase (se 4 (by rfl) ⟨156744, by rfl⟩ : syracuseStep 1671941 = 313489) (by norm_num)
theorem B5276501 : Blo 694316 5276501 := bbase (se 9 (by rfl) ⟨15458, by rfl⟩ : syracuseStep 5276501 = 30917) (by norm_num)
theorem B3343189 : Blo 694316 3343189 := bbase (se 9 (by rfl) ⟨9794, by rfl⟩ : syracuseStep 3343189 = 19589) (by norm_num)
theorem B1115165 : Blo 694316 1115165 := bbase (se 3 (by rfl) ⟨209093, by rfl⟩ : syracuseStep 1115165 = 418187) (by norm_num)
theorem B1115365 : Blo 694316 1115365 := bbase (se 4 (by rfl) ⟨104565, by rfl⟩ : syracuseStep 1115365 = 209131) (by norm_num)
theorem B4818197 : Blo 694316 4818197 := bbase (se 6 (by rfl) ⟨112926, by rfl⟩ : syracuseStep 4818197 = 225853) (by norm_num)
theorem B3179989 : Blo 694316 3179989 := bbase (se 7 (by rfl) ⟨37265, by rfl⟩ : syracuseStep 3179989 = 74531) (by norm_num)
theorem B1115621 : Blo 694316 1115621 := bbase (se 4 (by rfl) ⟨104589, by rfl⟩ : syracuseStep 1115621 = 209179) (by norm_num)
theorem B2819765 : Blo 694316 2819765 := bbase (se 5 (by rfl) ⟨132176, by rfl⟩ : syracuseStep 2819765 = 264353) (by norm_num)
theorem B5965589 : Blo 694316 5965589 := bbase (se 6 (by rfl) ⟨139818, by rfl⟩ : syracuseStep 5965589 = 279637) (by norm_num)
theorem B755489 : Blo 694316 755489 := bbase (se 2 (by rfl) ⟨283308, by rfl⟩ : syracuseStep 755489 = 566617) (by norm_num)
theorem B2819909 : Blo 694316 2819909 := bbase (se 4 (by rfl) ⟨264366, by rfl⟩ : syracuseStep 2819909 = 528733) (by norm_num)
theorem B2066485 : Blo 694316 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B1935461 : Blo 694316 1935461 := bbase (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) (by norm_num)
theorem B1411253 : Blo 694316 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B1149149 : Blo 694316 1149149 := bbase (se 3 (by rfl) ⟨215465, by rfl⟩ : syracuseStep 1149149 = 430931) (by norm_num)
theorem B723421 : Blo 694316 723421 := bbase (se 3 (by rfl) ⟨135641, by rfl⟩ : syracuseStep 723421 = 271283) (by norm_num)
theorem B1116749 : Blo 694316 1116749 := bbase (se 3 (by rfl) ⟨209390, by rfl⟩ : syracuseStep 1116749 = 418781) (by norm_num)
theorem B1411789 : Blo 694316 1411789 := bbase (se 3 (by rfl) ⟨264710, by rfl⟩ : syracuseStep 1411789 = 529421) (by norm_num)
theorem B1411901 : Blo 694316 1411901 := bbase (se 3 (by rfl) ⟨264731, by rfl⟩ : syracuseStep 1411901 = 529463) (by norm_num)
theorem B1674229 : Blo 694316 1674229 := bbase (se 5 (by rfl) ⟨78479, by rfl⟩ : syracuseStep 1674229 = 156959) (by norm_num)
theorem B5016629 : Blo 694316 5016629 := bbase (se 5 (by rfl) ⟨235154, by rfl⟩ : syracuseStep 5016629 = 470309) (by norm_num)
theorem B1117261 : Blo 694316 1117261 := bbase (se 3 (by rfl) ⟨209486, by rfl⟩ : syracuseStep 1117261 = 418973) (by norm_num)
theorem B2821205 : Blo 694316 2821205 := bbase (se 8 (by rfl) ⟨16530, by rfl⟩ : syracuseStep 2821205 = 33061) (by norm_num)
theorem B4820309 : Blo 694316 4820309 := bbase (se 11 (by rfl) ⟨3530, by rfl⟩ : syracuseStep 4820309 = 7061) (by norm_num)
theorem B2035109 : Blo 694316 2035109 := bbase (se 4 (by rfl) ⟨190791, by rfl⟩ : syracuseStep 2035109 = 381583) (by norm_num)
theorem B4754933 : Blo 694316 4754933 := bbase (se 5 (by rfl) ⟨222887, by rfl⟩ : syracuseStep 4754933 = 445775) (by norm_num)
theorem B1117805 : Blo 694316 1117805 := bbase (se 3 (by rfl) ⟨209588, by rfl⟩ : syracuseStep 1117805 = 419177) (by norm_num)
theorem B1674893 : Blo 694316 1674893 := bbase (se 3 (by rfl) ⟨314042, by rfl⟩ : syracuseStep 1674893 = 628085) (by norm_num)
theorem B11308693 : Blo 694316 11308693 := bbase (se 6 (by rfl) ⟨265047, by rfl⟩ : syracuseStep 11308693 = 530095) (by norm_num)
theorem B1740629 : Blo 694316 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B1118357 : Blo 694316 1118357 := bbase (se 6 (by rfl) ⟨26211, by rfl⟩ : syracuseStep 1118357 = 52423) (by norm_num)
theorem B1118389 : Blo 694316 1118389 := bbase (se 5 (by rfl) ⟨52424, by rfl⟩ : syracuseStep 1118389 = 104849) (by norm_num)
theorem B3969269 : Blo 694316 3969269 := bbase (se 5 (by rfl) ⟨186059, by rfl⟩ : syracuseStep 3969269 = 372119) (by norm_num)
theorem B4297045 : Blo 694316 4297045 := bbase (se 10 (by rfl) ⟨6294, by rfl⟩ : syracuseStep 4297045 = 12589) (by norm_num)
theorem B2232677 : Blo 694316 2232677 := bbase (se 4 (by rfl) ⟨209313, by rfl⟩ : syracuseStep 2232677 = 418627) (by norm_num)
theorem B1905061 : Blo 694316 1905061 := bbase (se 4 (by rfl) ⟨178599, by rfl⟩ : syracuseStep 1905061 = 357199) (by norm_num)
theorem B5345909 : Blo 694316 5345909 := bbase (se 5 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 5345909 = 501179) (by norm_num)
theorem B3347189 : Blo 694316 3347189 := bbase (se 5 (by rfl) ⟨156899, by rfl⟩ : syracuseStep 3347189 = 313799) (by norm_num)
theorem B1676285 : Blo 694316 1676285 := bbase (se 3 (by rfl) ⟨314303, by rfl⟩ : syracuseStep 1676285 = 628607) (by norm_num)
theorem B3347477 : Blo 694316 3347477 := bbase (se 6 (by rfl) ⟨78456, by rfl⟩ : syracuseStep 3347477 = 156913) (by norm_num)
theorem B1676381 : Blo 694316 1676381 := bbase (se 3 (by rfl) ⟨314321, by rfl⟩ : syracuseStep 1676381 = 628643) (by norm_num)
theorem B791905 : Blo 694316 791905 := bbase (se 2 (by rfl) ⟨296964, by rfl⟩ : syracuseStep 791905 = 593929) (by norm_num)
theorem B792001 : Blo 694316 792001 := bbase (se 2 (by rfl) ⟨297000, by rfl⟩ : syracuseStep 792001 = 594001) (by norm_num)
theorem B5936885 : Blo 694316 5936885 := bbase (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) (by norm_num)
theorem B988957 : Blo 694316 988957 := bbase (se 3 (by rfl) ⟨185429, by rfl⟩ : syracuseStep 988957 = 370859) (by norm_num)
theorem B7935893 : Blo 694316 7935893 := bbase (se 6 (by rfl) ⟨185997, by rfl⟩ : syracuseStep 7935893 = 371995) (by norm_num)
theorem B9050069 : Blo 694316 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B792913 : Blo 694316 792913 := bbase (se 2 (by rfl) ⟨297342, by rfl⟩ : syracuseStep 792913 = 594685) (by norm_num)
theorem B3578309 : Blo 694316 3578309 := bbase (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) (by norm_num)
theorem B1251845 : Blo 694316 1251845 := bbase (se 4 (by rfl) ⟨117360, by rfl⟩ : syracuseStep 1251845 = 234721) (by norm_num)
theorem B989749 : Blo 694316 989749 := bbase (se 5 (by rfl) ⟨46394, by rfl⟩ : syracuseStep 989749 = 92789) (by norm_num)
theorem B11901653 : Blo 694316 11901653 := bbase (se 7 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 11901653 = 278945) (by norm_num)
theorem B990085 : Blo 694316 990085 := bbase (se 4 (by rfl) ⟨92820, by rfl⟩ : syracuseStep 990085 = 185641) (by norm_num)
theorem B990301 : Blo 694316 990301 := bbase (se 3 (by rfl) ⟨185681, by rfl⟩ : syracuseStep 990301 = 371363) (by norm_num)
theorem B859229 : Blo 694316 859229 := bbase (se 3 (by rfl) ⟨161105, by rfl⟩ : syracuseStep 859229 = 322211) (by norm_num)
theorem B2235509 : Blo 694316 2235509 := bbase (se 5 (by rfl) ⟨104789, by rfl⟩ : syracuseStep 2235509 = 209579) (by norm_num)
theorem B2170037 : Blo 694316 2170037 := bbase (se 5 (by rfl) ⟨101720, by rfl⟩ : syracuseStep 2170037 = 203441) (by norm_num)
theorem B2792789 : Blo 694316 2792789 := bbase (se 11 (by rfl) ⟨2045, by rfl⟩ : syracuseStep 2792789 = 4091) (by norm_num)
theorem B990677 : Blo 694316 990677 := bbase (se 7 (by rfl) ⟨11609, by rfl⟩ : syracuseStep 990677 = 23219) (by norm_num)
theorem B892453 : Blo 694316 892453 := bbase (se 4 (by rfl) ⟨83667, by rfl⟩ : syracuseStep 892453 = 167335) (by norm_num)
theorem B2203301 : Blo 694316 2203301 := bbase (se 4 (by rfl) ⟨206559, by rfl⟩ : syracuseStep 2203301 = 413119) (by norm_num)
theorem B1318693 : Blo 694316 1318693 := bbase (se 4 (by rfl) ⟨123627, by rfl⟩ : syracuseStep 1318693 = 247255) (by norm_num)
theorem B794413 : Blo 694316 794413 := bbase (se 3 (by rfl) ⟨148952, by rfl⟩ : syracuseStep 794413 = 297905) (by norm_num)
theorem B892849 : Blo 694316 892849 := bbase (se 2 (by rfl) ⟨334818, by rfl⟩ : syracuseStep 892849 = 669637) (by norm_num)
theorem B1318837 : Blo 694316 1318837 := bbase (se 5 (by rfl) ⟨61820, by rfl⟩ : syracuseStep 1318837 = 123641) (by norm_num)
theorem B2236405 : Blo 694316 2236405 := bbase (se 5 (by rfl) ⟨104831, by rfl⟩ : syracuseStep 2236405 = 209663) (by norm_num)
theorem B1318997 : Blo 694316 1318997 := bbase (se 8 (by rfl) ⟨7728, by rfl⟩ : syracuseStep 1318997 = 15457) (by norm_num)
theorem B1482941 : Blo 694316 1482941 := bbase (se 3 (by rfl) ⟨278051, by rfl⟩ : syracuseStep 1482941 = 556103) (by norm_num)
theorem B1319141 : Blo 694316 1319141 := bbase (se 4 (by rfl) ⟨123669, by rfl⟩ : syracuseStep 1319141 = 247339) (by norm_num)
theorem B5284277 : Blo 694316 5284277 := bbase (se 5 (by rfl) ⟨247700, by rfl⟩ : syracuseStep 5284277 = 495401) (by norm_num)
theorem B1319429 : Blo 694316 1319429 := bbase (se 4 (by rfl) ⟨123696, by rfl⟩ : syracuseStep 1319429 = 247393) (by norm_num)
theorem B1188445 : Blo 694316 1188445 := bbase (se 3 (by rfl) ⟨222833, by rfl⟩ : syracuseStep 1188445 = 445667) (by norm_num)
theorem B2040437 : Blo 694316 2040437 := bbase (se 5 (by rfl) ⟨95645, by rfl⟩ : syracuseStep 2040437 = 191291) (by norm_num)
theorem B795253 : Blo 694316 795253 := bbase (se 5 (by rfl) ⟨37277, by rfl⟩ : syracuseStep 795253 = 74555) (by norm_num)
theorem B1319581 : Blo 694316 1319581 := bbase (se 3 (by rfl) ⟨247421, by rfl⟩ : syracuseStep 1319581 = 494843) (by norm_num)
theorem B3515237 : Blo 694316 3515237 := bbase (se 4 (by rfl) ⟨329553, by rfl⟩ : syracuseStep 3515237 = 659107) (by norm_num)
theorem B1057637 : Blo 694316 1057637 := bbase (se 4 (by rfl) ⟨99153, by rfl⟩ : syracuseStep 1057637 = 198307) (by norm_num)
theorem B992101 : Blo 694316 992101 := bbase (se 4 (by rfl) ⟨93009, by rfl⟩ : syracuseStep 992101 = 186019) (by norm_num)
theorem B1254325 : Blo 694316 1254325 := bbase (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) (by norm_num)
theorem B1319885 : Blo 694316 1319885 := bbase (se 3 (by rfl) ⟨247478, by rfl⟩ : syracuseStep 1319885 = 494957) (by norm_num)
theorem B893921 : Blo 694316 893921 := bbase (se 2 (by rfl) ⟨335220, by rfl⟩ : syracuseStep 893921 = 670441) (by norm_num)
theorem B6038549 : Blo 694316 6038549 := bbase (se 6 (by rfl) ⟨141528, by rfl⟩ : syracuseStep 6038549 = 283057) (by norm_num)
theorem B1483829 : Blo 694316 1483829 := bbase (se 5 (by rfl) ⟨69554, by rfl⟩ : syracuseStep 1483829 = 139109) (by norm_num)
theorem B1909973 : Blo 694316 1909973 := bbase (se 7 (by rfl) ⟨22382, by rfl⟩ : syracuseStep 1909973 = 44765) (by norm_num)
theorem B1484077 : Blo 694316 1484077 := bbase (se 3 (by rfl) ⟨278264, by rfl⟩ : syracuseStep 1484077 = 556529) (by norm_num)
theorem B4760981 : Blo 694316 4760981 := bbase (se 6 (by rfl) ⟨111585, by rfl⟩ : syracuseStep 4760981 = 223171) (by norm_num)
theorem B992693 : Blo 694316 992693 := bbase (se 5 (by rfl) ⟨46532, by rfl⟩ : syracuseStep 992693 = 93065) (by norm_num)
theorem B1058269 : Blo 694316 1058269 := bbase (se 3 (by rfl) ⟨198425, by rfl⟩ : syracuseStep 1058269 = 396851) (by norm_num)
theorem B992773 : Blo 694316 992773 := bbase (se 4 (by rfl) ⟨93072, by rfl⟩ : syracuseStep 992773 = 186145) (by norm_num)
theorem B992893 : Blo 694316 992893 := bbase (se 3 (by rfl) ⟨186167, by rfl⟩ : syracuseStep 992893 = 372335) (by norm_num)
theorem B1320637 : Blo 694316 1320637 := bbase (se 3 (by rfl) ⟨247619, by rfl⟩ : syracuseStep 1320637 = 495239) (by norm_num)
theorem B3352261 : Blo 694316 3352261 := bbase (se 4 (by rfl) ⟨314274, by rfl⟩ : syracuseStep 3352261 = 628549) (by norm_num)
theorem B992989 : Blo 694316 992989 := bbase (se 3 (by rfl) ⟨186185, by rfl⟩ : syracuseStep 992989 = 372371) (by norm_num)
theorem B1484581 : Blo 694316 1484581 := bbase (se 4 (by rfl) ⟨139179, by rfl⟩ : syracuseStep 1484581 = 278359) (by norm_num)
theorem B1320781 : Blo 694316 1320781 := bbase (se 3 (by rfl) ⟨247646, by rfl⟩ : syracuseStep 1320781 = 495293) (by norm_num)
theorem B1320941 : Blo 694316 1320941 := bbase (se 3 (by rfl) ⟨247676, by rfl⟩ : syracuseStep 1320941 = 495353) (by norm_num)
theorem B3516533 : Blo 694316 3516533 := bbase (se 5 (by rfl) ⟨164837, by rfl⟩ : syracuseStep 3516533 = 329675) (by norm_num)
theorem B6367349 : Blo 694316 6367349 := bbase (se 5 (by rfl) ⟨298469, by rfl⟩ : syracuseStep 6367349 = 596939) (by norm_num)
theorem B1321085 : Blo 694316 1321085 := bbase (se 3 (by rfl) ⟨247703, by rfl⟩ : syracuseStep 1321085 = 495407) (by norm_num)
theorem B993485 : Blo 694316 993485 := bbase (se 3 (by rfl) ⟨186278, by rfl⟩ : syracuseStep 993485 = 372557) (by norm_num)
theorem B1321373 : Blo 694316 1321373 := bbase (se 3 (by rfl) ⟨247757, by rfl⟩ : syracuseStep 1321373 = 495515) (by norm_num)
theorem B4467221 : Blo 694316 4467221 := bbase (se 6 (by rfl) ⟨104700, by rfl⟩ : syracuseStep 4467221 = 209401) (by norm_num)
theorem B1321525 : Blo 694316 1321525 := bbase (se 5 (by rfl) ⟨61946, by rfl⟩ : syracuseStep 1321525 = 123893) (by norm_num)
theorem B1485469 : Blo 694316 1485469 := bbase (se 3 (by rfl) ⟨278525, by rfl⟩ : syracuseStep 1485469 = 557051) (by norm_num)
theorem B1059485 : Blo 694316 1059485 := bbase (se 3 (by rfl) ⟨198653, by rfl⟩ : syracuseStep 1059485 = 397307) (by norm_num)
theorem B994037 : Blo 694316 994037 := bbase (se 5 (by rfl) ⟨46595, by rfl⟩ : syracuseStep 994037 = 93191) (by norm_num)
theorem B1321829 : Blo 694316 1321829 := bbase (se 4 (by rfl) ⟨123921, by rfl⟩ : syracuseStep 1321829 = 247843) (by norm_num)
theorem B1190909 : Blo 694316 1190909 := bbase (se 3 (by rfl) ⟨223295, by rfl⟩ : syracuseStep 1190909 = 446591) (by norm_num)
theorem B1485965 : Blo 694316 1485965 := bbase (se 3 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 1485965 = 557237) (by norm_num)
theorem B1977493 : Blo 694316 1977493 := bbase (se 6 (by rfl) ⟨46347, by rfl⟩ : syracuseStep 1977493 = 92695) (by norm_num)
theorem B2829509 : Blo 694316 2829509 := bbase (se 4 (by rfl) ⟨265266, by rfl⟩ : syracuseStep 2829509 = 530533) (by norm_num)
theorem B3517829 : Blo 694316 3517829 := bbase (se 4 (by rfl) ⟨329796, by rfl⟩ : syracuseStep 3517829 = 659593) (by norm_num)
theorem B1322581 : Blo 694316 1322581 := bbase (se 8 (by rfl) ⟨7749, by rfl⟩ : syracuseStep 1322581 = 15499) (by norm_num)
theorem B1322725 : Blo 694316 1322725 := bbase (se 4 (by rfl) ⟨124005, by rfl⟩ : syracuseStep 1322725 = 248011) (by norm_num)
theorem B1257229 : Blo 694316 1257229 := bbase (se 3 (by rfl) ⟨235730, by rfl⟩ : syracuseStep 1257229 = 471461) (by norm_num)
theorem B1322885 : Blo 694316 1322885 := bbase (se 4 (by rfl) ⟨124020, by rfl⟩ : syracuseStep 1322885 = 248041) (by norm_num)
theorem B1486853 : Blo 694316 1486853 := bbase (se 4 (by rfl) ⟨139392, by rfl⟩ : syracuseStep 1486853 = 278785) (by norm_num)
theorem B1323029 : Blo 694316 1323029 := bbase (se 6 (by rfl) ⟨31008, by rfl⟩ : syracuseStep 1323029 = 62017) (by norm_num)
theorem B1486973 : Blo 694316 1486973 := bbase (se 3 (by rfl) ⟨278807, by rfl⟩ : syracuseStep 1486973 = 557615) (by norm_num)
theorem B1585325 : Blo 694316 1585325 := bbase (se 3 (by rfl) ⟨297248, by rfl⟩ : syracuseStep 1585325 = 594497) (by norm_num)
theorem B1978597 : Blo 694316 1978597 := bbase (se 4 (by rfl) ⟨185493, by rfl⟩ : syracuseStep 1978597 = 370987) (by norm_num)
theorem B1323317 : Blo 694316 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B1585469 : Blo 694316 1585469 := bbase (se 3 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 1585469 = 594551) (by norm_num)
theorem B1323469 : Blo 694316 1323469 := bbase (se 3 (by rfl) ⟨248150, by rfl⟩ : syracuseStep 1323469 = 496301) (by norm_num)
theorem B3519125 : Blo 694316 3519125 := bbase (se 6 (by rfl) ⟨82479, by rfl⟩ : syracuseStep 3519125 = 164959) (by norm_num)
theorem B1585909 : Blo 694316 1585909 := bbase (se 5 (by rfl) ⟨74339, by rfl⟩ : syracuseStep 1585909 = 148679) (by norm_num)
theorem B1487605 : Blo 694316 1487605 := bbase (se 5 (by rfl) ⟨69731, by rfl⟩ : syracuseStep 1487605 = 139463) (by norm_num)
theorem B1323773 : Blo 694316 1323773 := bbase (se 3 (by rfl) ⟨248207, by rfl⟩ : syracuseStep 1323773 = 496415) (by norm_num)
theorem B8926037 : Blo 694316 8926037 := bbase (se 9 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 8926037 = 52301) (by norm_num)
theorem B1258325 : Blo 694316 1258325 := bbase (se 9 (by rfl) ⟨3686, by rfl⟩ : syracuseStep 1258325 = 7373) (by norm_num)
theorem B1324525 : Blo 694316 1324525 := bbase (se 3 (by rfl) ⟨248348, by rfl⟩ : syracuseStep 1324525 = 496697) (by norm_num)
theorem B1488493 : Blo 694316 1488493 := bbase (se 3 (by rfl) ⟨279092, by rfl⟩ : syracuseStep 1488493 = 558185) (by norm_num)
theorem B1324669 : Blo 694316 1324669 := bbase (se 3 (by rfl) ⟨248375, by rfl⟩ : syracuseStep 1324669 = 496751) (by norm_num)
theorem B6698645 : Blo 694316 6698645 := bbase (se 6 (by rfl) ⟨156999, by rfl⟩ : syracuseStep 6698645 = 313999) (by norm_num)
theorem B1980101 : Blo 694316 1980101 := bbase (se 4 (by rfl) ⟨185634, by rfl⟩ : syracuseStep 1980101 = 371269) (by norm_num)
theorem B1586893 : Blo 694316 1586893 := bbase (se 3 (by rfl) ⟨297542, by rfl⟩ : syracuseStep 1586893 = 595085) (by norm_num)
theorem B1488613 : Blo 694316 1488613 := bbase (se 4 (by rfl) ⟨139557, by rfl⟩ : syracuseStep 1488613 = 279115) (by norm_num)
theorem B1324829 : Blo 694316 1324829 := bbase (se 3 (by rfl) ⟨248405, by rfl⟩ : syracuseStep 1324829 = 496811) (by norm_num)
theorem B3520421 : Blo 694316 3520421 := bbase (se 4 (by rfl) ⟨330039, by rfl⟩ : syracuseStep 3520421 = 660079) (by norm_num)
theorem B1324973 : Blo 694316 1324973 := bbase (se 3 (by rfl) ⟨248432, by rfl⟩ : syracuseStep 1324973 = 496865) (by norm_num)
theorem B1488869 : Blo 694316 1488869 := bbase (se 4 (by rfl) ⟨139581, by rfl⟩ : syracuseStep 1488869 = 279163) (by norm_num)
theorem B1587221 : Blo 694316 1587221 := bbase (se 6 (by rfl) ⟨37200, by rfl⟩ : syracuseStep 1587221 = 74401) (by norm_num)
theorem B1325261 : Blo 694316 1325261 := bbase (se 3 (by rfl) ⟨248486, by rfl⟩ : syracuseStep 1325261 = 496973) (by norm_num)
theorem B1325413 : Blo 694316 1325413 := bbase (se 4 (by rfl) ⟨124257, by rfl⟩ : syracuseStep 1325413 = 248515) (by norm_num)
theorem B1587725 : Blo 694316 1587725 := bbase (se 3 (by rfl) ⟨297698, by rfl⟩ : syracuseStep 1587725 = 595397) (by norm_num)
theorem B1784413 : Blo 694316 1784413 := bbase (se 3 (by rfl) ⟨334577, by rfl⟩ : syracuseStep 1784413 = 669155) (by norm_num)
theorem B834221 : Blo 694316 834221 := bbase (se 3 (by rfl) ⟨156416, by rfl⟩ : syracuseStep 834221 = 312833) (by norm_num)
theorem B834337 : Blo 694316 834337 := bbase (se 2 (by rfl) ⟨312876, by rfl⟩ : syracuseStep 834337 = 625753) (by norm_num)
theorem B7519061 : Blo 694316 7519061 := bbase (se 9 (by rfl) ⟨22028, by rfl⟩ : syracuseStep 7519061 = 44057) (by norm_num)
theorem B1489757 : Blo 694316 1489757 := bbase (se 3 (by rfl) ⟨279329, by rfl⟩ : syracuseStep 1489757 = 558659) (by norm_num)
theorem B834409 : Blo 694316 834409 := bbase (se 2 (by rfl) ⟨312903, by rfl⟩ : syracuseStep 834409 = 625807) (by norm_num)
theorem B834529 : Blo 694316 834529 := bbase (se 2 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 834529 = 625897) (by norm_num)
theorem B1489997 : Blo 694316 1489997 := bbase (se 3 (by rfl) ⟨279374, by rfl⟩ : syracuseStep 1489997 = 558749) (by norm_num)
theorem B3521717 : Blo 694316 3521717 := bbase (se 5 (by rfl) ⟨165080, by rfl⟩ : syracuseStep 3521717 = 330161) (by norm_num)
theorem B1981685 : Blo 694316 1981685 := bbase (se 5 (by rfl) ⟨92891, by rfl⟩ : syracuseStep 1981685 = 185783) (by norm_num)
theorem B834913 : Blo 694316 834913 := bbase (se 2 (by rfl) ⟨313092, by rfl⟩ : syracuseStep 834913 = 626185) (by norm_num)
theorem B2637157 : Blo 694316 2637157 := bbase (se 4 (by rfl) ⟨247233, by rfl⟩ : syracuseStep 2637157 = 494467) (by norm_num)
theorem B1490501 : Blo 694316 1490501 := bbase (se 4 (by rfl) ⟨139734, by rfl⟩ : syracuseStep 1490501 = 279469) (by norm_num)
theorem B1490509 : Blo 694316 1490509 := bbase (se 3 (by rfl) ⟨279470, by rfl⟩ : syracuseStep 1490509 = 558941) (by norm_num)
theorem B2637461 : Blo 694316 2637461 := bbase (se 6 (by rfl) ⟨61815, by rfl⟩ : syracuseStep 2637461 = 123631) (by norm_num)
theorem B2506469 : Blo 694316 2506469 := bbase (se 4 (by rfl) ⟨234981, by rfl⟩ : syracuseStep 2506469 = 469963) (by norm_num)
theorem B1884005 : Blo 694316 1884005 := bbase (se 4 (by rfl) ⟨176625, by rfl⟩ : syracuseStep 1884005 = 353251) (by norm_num)
theorem B1982357 : Blo 694316 1982357 := bbase (se 6 (by rfl) ⟨46461, by rfl⟩ : syracuseStep 1982357 = 92923) (by norm_num)
theorem B2015189 : Blo 694316 2015189 := bbase (se 7 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 2015189 = 47231) (by norm_num)
theorem B835601 : Blo 694316 835601 := bbase (se 2 (by rfl) ⟨313350, by rfl⟩ : syracuseStep 835601 = 626701) (by norm_num)
theorem B5292053 : Blo 694316 5292053 := bbase (se 6 (by rfl) ⟨124032, by rfl⟩ : syracuseStep 5292053 = 248065) (by norm_num)
theorem B704629 : Blo 694316 704629 := bbase (se 5 (by rfl) ⟨33029, by rfl⟩ : syracuseStep 704629 = 66059) (by norm_num)
theorem B5652661 : Blo 694316 5652661 := bbase (se 5 (by rfl) ⟨264968, by rfl⟩ : syracuseStep 5652661 = 529937) (by norm_num)
theorem B5095669 : Blo 694316 5095669 := bbase (se 5 (by rfl) ⟨238859, by rfl⟩ : syracuseStep 5095669 = 477719) (by norm_num)
theorem B1982789 : Blo 694316 1982789 := bbase (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) (by norm_num)
theorem B1130917 : Blo 694316 1130917 := bbase (se 4 (by rfl) ⟨106023, by rfl⟩ : syracuseStep 1130917 = 212047) (by norm_num)
theorem B3523013 : Blo 694316 3523013 := bbase (se 4 (by rfl) ⟨330282, by rfl⟩ : syracuseStep 3523013 = 660565) (by norm_num)
theorem B1786445 : Blo 694316 1786445 := bbase (se 3 (by rfl) ⟨334958, by rfl⟩ : syracuseStep 1786445 = 669917) (by norm_num)
theorem B836201 : Blo 694316 836201 := bbase (se 2 (by rfl) ⟨313575, by rfl⟩ : syracuseStep 836201 = 627151) (by norm_num)
theorem B2507381 : Blo 694316 2507381 := bbase (se 5 (by rfl) ⟨117533, by rfl⟩ : syracuseStep 2507381 = 235067) (by norm_num)
theorem B2343653 : Blo 694316 2343653 := bbase (se 4 (by rfl) ⟨219717, by rfl⟩ : syracuseStep 2343653 = 439435) (by norm_num)
theorem B1590085 : Blo 694316 1590085 := bbase (se 4 (by rfl) ⟨149070, by rfl⟩ : syracuseStep 1590085 = 298141) (by norm_num)
theorem B836509 : Blo 694316 836509 := bbase (se 3 (by rfl) ⟨156845, by rfl⟩ : syracuseStep 836509 = 313691) (by norm_num)
theorem B836605 : Blo 694316 836605 := bbase (se 3 (by rfl) ⟨156863, by rfl⟩ : syracuseStep 836605 = 313727) (by norm_num)
theorem B836653 : Blo 694316 836653 := bbase (se 3 (by rfl) ⟨156872, by rfl⟩ : syracuseStep 836653 = 313745) (by norm_num)
theorem B1983541 : Blo 694316 1983541 := bbase (se 5 (by rfl) ⟨92978, by rfl⟩ : syracuseStep 1983541 = 185957) (by norm_num)
theorem B2344085 : Blo 694316 2344085 := bbase (se 6 (by rfl) ⟨54939, by rfl⟩ : syracuseStep 2344085 = 109879) (by norm_num)
theorem B705853 : Blo 694316 705853 := bbase (se 3 (by rfl) ⟨132347, by rfl⟩ : syracuseStep 705853 = 264695) (by norm_num)
theorem B2115077 : Blo 694316 2115077 := bbase (se 4 (by rfl) ⟨198288, by rfl⟩ : syracuseStep 2115077 = 396577) (by norm_num)
theorem B2344517 : Blo 694316 2344517 := bbase (se 4 (by rfl) ⟨219798, by rfl⟩ : syracuseStep 2344517 = 439597) (by norm_num)
theorem B1361485 : Blo 694316 1361485 := bbase (se 3 (by rfl) ⟨255278, by rfl⟩ : syracuseStep 1361485 = 510557) (by norm_num)
theorem B2639573 : Blo 694316 2639573 := bbase (se 7 (by rfl) ⟨30932, by rfl⟩ : syracuseStep 2639573 = 61865) (by norm_num)
theorem B3524309 : Blo 694316 3524309 := bbase (se 7 (by rfl) ⟨41300, by rfl⟩ : syracuseStep 3524309 = 82601) (by norm_num)
theorem B2967349 : Blo 694316 2967349 := bbase (se 5 (by rfl) ⟨139094, by rfl⟩ : syracuseStep 2967349 = 278189) (by norm_num)
theorem B706469 : Blo 694316 706469 := bbase (se 4 (by rfl) ⟨66231, by rfl⟩ : syracuseStep 706469 = 132463) (by norm_num)
theorem B2344949 : Blo 694316 2344949 := bbase (se 5 (by rfl) ⟨109919, by rfl⟩ : syracuseStep 2344949 = 219839) (by norm_num)
theorem B2639861 : Blo 694316 2639861 := bbase (se 5 (by rfl) ⟨123743, by rfl⟩ : syracuseStep 2639861 = 247487) (by norm_num)
theorem B2672645 : Blo 694316 2672645 := bbase (se 4 (by rfl) ⟨250560, by rfl⟩ : syracuseStep 2672645 = 501121) (by norm_num)
theorem B2377765 : Blo 694316 2377765 := bbase (se 4 (by rfl) ⟨222915, by rfl⟩ : syracuseStep 2377765 = 445831) (by norm_num)
theorem B837869 : Blo 694316 837869 := bbase (se 3 (by rfl) ⟨157100, by rfl⟩ : syracuseStep 837869 = 314201) (by norm_num)
theorem B8472917 : Blo 694316 8472917 := bbase (se 10 (by rfl) ⟨12411, by rfl⟩ : syracuseStep 8472917 = 24823) (by norm_num)
theorem B838037 : Blo 694316 838037 := bbase (se 6 (by rfl) ⟨19641, by rfl⟩ : syracuseStep 838037 = 39283) (by norm_num)
theorem B1591709 : Blo 694316 1591709 := bbase (se 3 (by rfl) ⟨298445, by rfl⟩ : syracuseStep 1591709 = 596891) (by norm_num)
theorem B2345381 : Blo 694316 2345381 := bbase (se 4 (by rfl) ⟨219879, by rfl⟩ : syracuseStep 2345381 = 439759) (by norm_num)
theorem B838345 : Blo 694316 838345 := bbase (se 2 (by rfl) ⟨314379, by rfl⟩ : syracuseStep 838345 = 628759) (by norm_num)
theorem B2345813 : Blo 694316 2345813 := bbase (se 9 (by rfl) ⟨6872, by rfl⟩ : syracuseStep 2345813 = 13745) (by norm_num)
theorem B838561 : Blo 694316 838561 := bbase (se 2 (by rfl) ⟨314460, by rfl⟩ : syracuseStep 838561 = 628921) (by norm_num)
theorem B3525605 : Blo 694316 3525605 := bbase (se 4 (by rfl) ⟨330525, by rfl⟩ : syracuseStep 3525605 = 661051) (by norm_num)
theorem B707621 : Blo 694316 707621 := bbase (se 4 (by rfl) ⟨66339, by rfl⟩ : syracuseStep 707621 = 132679) (by norm_num)
theorem B2641045 : Blo 694316 2641045 := bbase (se 6 (by rfl) ⟨61899, by rfl⟩ : syracuseStep 2641045 = 123799) (by norm_num)
theorem B838873 : Blo 694316 838873 := bbase (se 2 (by rfl) ⟨314577, by rfl⟩ : syracuseStep 838873 = 629155) (by norm_num)
theorem B2346245 : Blo 694316 2346245 := bbase (se 4 (by rfl) ⟨219960, by rfl⟩ : syracuseStep 2346245 = 439921) (by norm_num)
theorem B2641349 : Blo 694316 2641349 := bbase (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) (by norm_num)
theorem B2346677 : Blo 694316 2346677 := bbase (se 5 (by rfl) ⟨110000, by rfl⟩ : syracuseStep 2346677 = 220001) (by norm_num)
theorem B1986389 : Blo 694316 1986389 := bbase (se 9 (by rfl) ⟨5819, by rfl⟩ : syracuseStep 1986389 = 11639) (by norm_num)
theorem B1789885 : Blo 694316 1789885 := bbase (se 3 (by rfl) ⟨335603, by rfl⟩ : syracuseStep 1789885 = 671207) (by norm_num)
theorem B2347109 : Blo 694316 2347109 := bbase (se 4 (by rfl) ⟨220041, by rfl⟩ : syracuseStep 2347109 = 440083) (by norm_num)
theorem B3526901 : Blo 694316 3526901 := bbase (se 5 (by rfl) ⟨165323, by rfl⟩ : syracuseStep 3526901 = 330647) (by norm_num)
theorem B741641 : Blo 694316 741641 := bbase (se 2 (by rfl) ⟨278115, by rfl⟩ : syracuseStep 741641 = 556231) (by norm_num)
theorem B938413 : Blo 694316 938413 := bbase (se 3 (by rfl) ⟨175952, by rfl⟩ : syracuseStep 938413 = 351905) (by norm_num)
theorem B741889 : Blo 694316 741889 := bbase (se 2 (by rfl) ⟨278208, by rfl⟩ : syracuseStep 741889 = 556417) (by norm_num)
theorem B2347541 : Blo 694316 2347541 := bbase (se 6 (by rfl) ⟨55020, by rfl⟩ : syracuseStep 2347541 = 110041) (by norm_num)
theorem B1757821 : Blo 694316 1757821 := bbase (se 3 (by rfl) ⟨329591, by rfl⟩ : syracuseStep 1757821 = 659183) (by norm_num)
theorem B2970341 : Blo 694316 2970341 := bbase (se 4 (by rfl) ⟨278469, by rfl⟩ : syracuseStep 2970341 = 556939) (by norm_num)
theorem B1430245 : Blo 694316 1430245 := bbase (se 4 (by rfl) ⟨134085, by rfl⟩ : syracuseStep 1430245 = 268171) (by norm_num)
theorem B1757933 : Blo 694316 1757933 := bbase (se 3 (by rfl) ⟨329612, by rfl⟩ : syracuseStep 1757933 = 659225) (by norm_num)
theorem B3756917 : Blo 694316 3756917 := bbase (se 5 (by rfl) ⟨176105, by rfl⟩ : syracuseStep 3756917 = 352211) (by norm_num)
theorem B1758125 : Blo 694316 1758125 := bbase (se 3 (by rfl) ⟨329648, by rfl⟩ : syracuseStep 1758125 = 659297) (by norm_num)
theorem B742333 : Blo 694316 742333 := bbase (se 3 (by rfl) ⟨139187, by rfl⟩ : syracuseStep 742333 = 278375) (by norm_num)
theorem B2347973 : Blo 694316 2347973 := bbase (se 4 (by rfl) ⟨220122, by rfl⟩ : syracuseStep 2347973 = 440245) (by norm_num)
theorem B1987573 : Blo 694316 1987573 := bbase (se 5 (by rfl) ⟨93167, by rfl⟩ : syracuseStep 1987573 = 186335) (by norm_num)
theorem B742393 : Blo 694316 742393 := bbase (se 2 (by rfl) ⟨278397, by rfl⟩ : syracuseStep 742393 = 556795) (by norm_num)
theorem B1791085 : Blo 694316 1791085 := bbase (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) (by norm_num)
theorem B1987733 : Blo 694316 1987733 := bbase (se 6 (by rfl) ⟨46587, by rfl⟩ : syracuseStep 1987733 = 93175) (by norm_num)
theorem B1758469 : Blo 694316 1758469 := bbase (se 4 (by rfl) ⟨164856, by rfl⟩ : syracuseStep 1758469 = 329713) (by norm_num)
theorem B742709 : Blo 694316 742709 := bbase (se 5 (by rfl) ⟨34814, by rfl⟩ : syracuseStep 742709 = 69629) (by norm_num)
theorem B1758581 : Blo 694316 1758581 := bbase (se 5 (by rfl) ⟨82433, by rfl⟩ : syracuseStep 1758581 = 164867) (by norm_num)
theorem B2348405 : Blo 694316 2348405 := bbase (se 5 (by rfl) ⟨110081, by rfl⟩ : syracuseStep 2348405 = 220163) (by norm_num)
theorem B1987973 : Blo 694316 1987973 := bbase (se 4 (by rfl) ⟨186372, by rfl⟩ : syracuseStep 1987973 = 372745) (by norm_num)
theorem B1005037 : Blo 694316 1005037 := bbase (se 3 (by rfl) ⟨188444, by rfl⟩ : syracuseStep 1005037 = 376889) (by norm_num)
theorem B2643461 : Blo 694316 2643461 := bbase (se 4 (by rfl) ⟨247824, by rfl⟩ : syracuseStep 2643461 = 495649) (by norm_num)
theorem B3528197 : Blo 694316 3528197 := bbase (se 4 (by rfl) ⟨330768, by rfl⟩ : syracuseStep 3528197 = 661537) (by norm_num)
theorem B1758773 : Blo 694316 1758773 := bbase (se 5 (by rfl) ⟨82442, by rfl⟩ : syracuseStep 1758773 = 164885) (by norm_num)
theorem B2512453 : Blo 694316 2512453 := bbase (se 4 (by rfl) ⟨235542, by rfl⟩ : syracuseStep 2512453 = 471085) (by norm_num)
theorem B1988165 : Blo 694316 1988165 := bbase (se 4 (by rfl) ⟨186390, by rfl⟩ : syracuseStep 1988165 = 372781) (by norm_num)
theorem B1562237 : Blo 694316 1562237 := bbase (se 3 (by rfl) ⟨292919, by rfl⟩ : syracuseStep 1562237 = 585839) (by norm_num)
theorem B1562309 : Blo 694316 1562309 := bbase (se 4 (by rfl) ⟨146466, by rfl⟩ : syracuseStep 1562309 = 292933) (by norm_num)
theorem B2971349 : Blo 694316 2971349 := bbase (se 7 (by rfl) ⟨34820, by rfl⟩ : syracuseStep 2971349 = 69641) (by norm_num)
theorem B2512613 : Blo 694316 2512613 := bbase (se 4 (by rfl) ⟨235557, by rfl⟩ : syracuseStep 2512613 = 471115) (by norm_num)
theorem B743153 : Blo 694316 743153 := bbase (se 2 (by rfl) ⟨278682, by rfl⟩ : syracuseStep 743153 = 557365) (by norm_num)
theorem B1562381 : Blo 694316 1562381 := bbase (se 3 (by rfl) ⟨292946, by rfl⟩ : syracuseStep 1562381 = 585893) (by norm_num)
theorem B2348837 : Blo 694316 2348837 := bbase (se 4 (by rfl) ⟨220203, by rfl⟩ : syracuseStep 2348837 = 440407) (by norm_num)
theorem B2643749 : Blo 694316 2643749 := bbase (se 4 (by rfl) ⟨247851, by rfl⟩ : syracuseStep 2643749 = 495703) (by norm_num)
theorem B743213 : Blo 694316 743213 := bbase (se 3 (by rfl) ⟨139352, by rfl⟩ : syracuseStep 743213 = 278705) (by norm_num)
theorem B1562453 : Blo 694316 1562453 := bbase (se 9 (by rfl) ⟨4577, by rfl⟩ : syracuseStep 1562453 = 9155) (by norm_num)
theorem B1759117 : Blo 694316 1759117 := bbase (se 3 (by rfl) ⟨329834, by rfl⟩ : syracuseStep 1759117 = 659669) (by norm_num)
theorem B1562525 : Blo 694316 1562525 := bbase (se 3 (by rfl) ⟨292973, by rfl⟩ : syracuseStep 1562525 = 585947) (by norm_num)
theorem B743341 : Blo 694316 743341 := bbase (se 3 (by rfl) ⟨139376, by rfl⟩ : syracuseStep 743341 = 278753) (by norm_num)
theorem B1562597 : Blo 694316 1562597 := bbase (se 4 (by rfl) ⟨146493, by rfl⟩ : syracuseStep 1562597 = 292987) (by norm_num)
theorem B1759229 : Blo 694316 1759229 := bbase (se 3 (by rfl) ⟨329855, by rfl⟩ : syracuseStep 1759229 = 659711) (by norm_num)
theorem B1562669 : Blo 694316 1562669 := bbase (se 3 (by rfl) ⟨293000, by rfl⟩ : syracuseStep 1562669 = 586001) (by norm_num)
theorem B5363765 : Blo 694316 5363765 := bbase (se 5 (by rfl) ⟨251426, by rfl⟩ : syracuseStep 5363765 = 502853) (by norm_num)
theorem B1562741 : Blo 694316 1562741 := bbase (se 5 (by rfl) ⟨73253, by rfl⟩ : syracuseStep 1562741 = 146507) (by norm_num)
theorem B1562813 : Blo 694316 1562813 := bbase (se 3 (by rfl) ⟨293027, by rfl⟩ : syracuseStep 1562813 = 586055) (by norm_num)
theorem B1759421 : Blo 694316 1759421 := bbase (se 3 (by rfl) ⟨329891, by rfl⟩ : syracuseStep 1759421 = 659783) (by norm_num)
theorem B2349269 : Blo 694316 2349269 := bbase (se 7 (by rfl) ⟨27530, by rfl⟩ : syracuseStep 2349269 = 55061) (by norm_num)
theorem B1562885 : Blo 694316 1562885 := bbase (se 4 (by rfl) ⟨146520, by rfl⟩ : syracuseStep 1562885 = 293041) (by norm_num)
theorem B1562957 : Blo 694316 1562957 := bbase (se 3 (by rfl) ⟨293054, by rfl⟩ : syracuseStep 1562957 = 586109) (by norm_num)
theorem B743785 : Blo 694316 743785 := bbase (se 2 (by rfl) ⟨278919, by rfl⟩ : syracuseStep 743785 = 557839) (by norm_num)
theorem B1563029 : Blo 694316 1563029 := bbase (se 6 (by rfl) ⟨36633, by rfl⟩ : syracuseStep 1563029 = 73267) (by norm_num)
theorem B1563101 : Blo 694316 1563101 := bbase (se 3 (by rfl) ⟨293081, by rfl⟩ : syracuseStep 1563101 = 586163) (by norm_num)
theorem B743905 : Blo 694316 743905 := bbase (se 2 (by rfl) ⟨278964, by rfl⟩ : syracuseStep 743905 = 557929) (by norm_num)
theorem B3955189 : Blo 694316 3955189 := bbase (se 5 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 3955189 = 370799) (by norm_num)
theorem B4512277 : Blo 694316 4512277 := bbase (se 6 (by rfl) ⟨105756, by rfl⟩ : syracuseStep 4512277 = 211513) (by norm_num)
theorem B1759765 : Blo 694316 1759765 := bbase (se 6 (by rfl) ⟨41244, by rfl⟩ : syracuseStep 1759765 = 82489) (by norm_num)
theorem B1563173 : Blo 694316 1563173 := bbase (se 4 (by rfl) ⟨146547, by rfl⟩ : syracuseStep 1563173 = 293095) (by norm_num)
theorem B1563245 : Blo 694316 1563245 := bbase (se 3 (by rfl) ⟨293108, by rfl⟩ : syracuseStep 1563245 = 586217) (by norm_num)
theorem B1759877 : Blo 694316 1759877 := bbase (se 4 (by rfl) ⟨164988, by rfl⟩ : syracuseStep 1759877 = 329977) (by norm_num)
theorem B2349701 : Blo 694316 2349701 := bbase (se 4 (by rfl) ⟨220284, by rfl⟩ : syracuseStep 2349701 = 440569) (by norm_num)
theorem B1071773 : Blo 694316 1071773 := bbase (se 3 (by rfl) ⟨200957, by rfl⟩ : syracuseStep 1071773 = 401915) (by norm_num)
theorem B1563317 : Blo 694316 1563317 := bbase (se 5 (by rfl) ⟨73280, by rfl⟩ : syracuseStep 1563317 = 146561) (by norm_num)
theorem B744157 : Blo 694316 744157 := bbase (se 3 (by rfl) ⟨139529, by rfl⟩ : syracuseStep 744157 = 279059) (by norm_num)
theorem B744161 : Blo 694316 744161 := bbase (se 2 (by rfl) ⟨279060, by rfl⟩ : syracuseStep 744161 = 558121) (by norm_num)
theorem B1563389 : Blo 694316 1563389 := bbase (se 3 (by rfl) ⟨293135, by rfl⟩ : syracuseStep 1563389 = 586271) (by norm_num)
theorem B3529493 : Blo 694316 3529493 := bbase (se 6 (by rfl) ⟨82722, by rfl⟩ : syracuseStep 3529493 = 165445) (by norm_num)
theorem B2448181 : Blo 694316 2448181 := bbase (se 5 (by rfl) ⟨114758, by rfl⟩ : syracuseStep 2448181 = 229517) (by norm_num)
theorem B1563461 : Blo 694316 1563461 := bbase (se 4 (by rfl) ⟨146574, by rfl⟩ : syracuseStep 1563461 = 293149) (by norm_num)
theorem B1760069 : Blo 694316 1760069 := bbase (se 4 (by rfl) ⟨165006, by rfl⟩ : syracuseStep 1760069 = 330013) (by norm_num)
theorem B1563533 : Blo 694316 1563533 := bbase (se 3 (by rfl) ⟨293162, by rfl⟩ : syracuseStep 1563533 = 586325) (by norm_num)
theorem B2644933 : Blo 694316 2644933 := bbase (se 4 (by rfl) ⟨247962, by rfl⟩ : syracuseStep 2644933 = 495925) (by norm_num)
theorem B1563605 : Blo 694316 1563605 := bbase (se 7 (by rfl) ⟨18323, by rfl⟩ : syracuseStep 1563605 = 36647) (by norm_num)
theorem B1006597 : Blo 694316 1006597 := bbase (se 4 (by rfl) ⟨94368, by rfl⟩ : syracuseStep 1006597 = 188737) (by norm_num)
theorem B1563677 : Blo 694316 1563677 := bbase (se 3 (by rfl) ⟨293189, by rfl⟩ : syracuseStep 1563677 = 586379) (by norm_num)
theorem B2350133 : Blo 694316 2350133 := bbase (se 5 (by rfl) ⟨110162, by rfl⟩ : syracuseStep 2350133 = 220325) (by norm_num)
theorem B1563749 : Blo 694316 1563749 := bbase (se 4 (by rfl) ⟨146601, by rfl⟩ : syracuseStep 1563749 = 293203) (by norm_num)
theorem B1760413 : Blo 694316 1760413 := bbase (se 3 (by rfl) ⟨330077, by rfl⟩ : syracuseStep 1760413 = 660155) (by norm_num)
theorem B1563821 : Blo 694316 1563821 := bbase (se 3 (by rfl) ⟨293216, by rfl⟩ : syracuseStep 1563821 = 586433) (by norm_num)
theorem B1563893 : Blo 694316 1563893 := bbase (se 5 (by rfl) ⟨73307, by rfl⟩ : syracuseStep 1563893 = 146615) (by norm_num)
theorem B2645237 : Blo 694316 2645237 := bbase (se 5 (by rfl) ⟨123995, by rfl⟩ : syracuseStep 2645237 = 247991) (by norm_num)
theorem B1760525 : Blo 694316 1760525 := bbase (se 3 (by rfl) ⟨330098, by rfl⟩ : syracuseStep 1760525 = 660197) (by norm_num)
theorem B744725 : Blo 694316 744725 := bbase (se 6 (by rfl) ⟨17454, by rfl⟩ : syracuseStep 744725 = 34909) (by norm_num)
theorem B3398933 : Blo 694316 3398933 := bbase (se 6 (by rfl) ⟨79662, by rfl⟩ : syracuseStep 3398933 = 159325) (by norm_num)
theorem B1563965 : Blo 694316 1563965 := bbase (se 3 (by rfl) ⟨293243, by rfl⟩ : syracuseStep 1563965 = 586487) (by norm_num)
theorem B1564037 : Blo 694316 1564037 := bbase (se 4 (by rfl) ⟨146628, by rfl⟩ : syracuseStep 1564037 = 293257) (by norm_num)
theorem B2973125 : Blo 694316 2973125 := bbase (se 4 (by rfl) ⟨278730, by rfl⟩ : syracuseStep 2973125 = 557461) (by norm_num)
theorem B1564109 : Blo 694316 1564109 := bbase (se 3 (by rfl) ⟨293270, by rfl⟩ : syracuseStep 1564109 = 586541) (by norm_num)
theorem B1760717 : Blo 694316 1760717 := bbase (se 3 (by rfl) ⟨330134, by rfl⟩ : syracuseStep 1760717 = 660269) (by norm_num)
theorem B744913 : Blo 694316 744913 := bbase (se 2 (by rfl) ⟨279342, by rfl⟩ : syracuseStep 744913 = 558685) (by norm_num)
theorem B2350565 : Blo 694316 2350565 := bbase (se 4 (by rfl) ⟨220365, by rfl⟩ : syracuseStep 2350565 = 440731) (by norm_num)
theorem B941581 : Blo 694316 941581 := bbase (se 3 (by rfl) ⟨176546, by rfl⟩ : syracuseStep 941581 = 353093) (by norm_num)
theorem B1564181 : Blo 694316 1564181 := bbase (se 6 (by rfl) ⟨36660, by rfl⟩ : syracuseStep 1564181 = 73321) (by norm_num)
theorem B1564253 : Blo 694316 1564253 := bbase (se 3 (by rfl) ⟨293297, by rfl⟩ : syracuseStep 1564253 = 586595) (by norm_num)
theorem B5299829 : Blo 694316 5299829 := bbase (se 5 (by rfl) ⟨248429, by rfl⟩ : syracuseStep 5299829 = 496859) (by norm_num)
theorem B13721237 : Blo 694316 13721237 := bbase (se 6 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 13721237 = 643183) (by norm_num)
theorem B1564325 : Blo 694316 1564325 := bbase (se 4 (by rfl) ⟨146655, by rfl⟩ : syracuseStep 1564325 = 293311) (by norm_num)
theorem B1564397 : Blo 694316 1564397 := bbase (se 3 (by rfl) ⟨293324, by rfl⟩ : syracuseStep 1564397 = 586649) (by norm_num)
theorem B1761061 : Blo 694316 1761061 := bbase (se 4 (by rfl) ⟨165099, by rfl⟩ : syracuseStep 1761061 = 330199) (by norm_num)
theorem B1564469 : Blo 694316 1564469 := bbase (se 5 (by rfl) ⟨73334, by rfl⟩ : syracuseStep 1564469 = 146669) (by norm_num)
theorem B2514773 : Blo 694316 2514773 := bbase (se 9 (by rfl) ⟨7367, by rfl⟩ : syracuseStep 2514773 = 14735) (by norm_num)
theorem B1564541 : Blo 694316 1564541 := bbase (se 3 (by rfl) ⟨293351, by rfl⟩ : syracuseStep 1564541 = 586703) (by norm_num)
theorem B1761173 : Blo 694316 1761173 := bbase (se 6 (by rfl) ⟨41277, by rfl⟩ : syracuseStep 1761173 = 82555) (by norm_num)
theorem B2350997 : Blo 694316 2350997 := bbase (se 6 (by rfl) ⟨55101, by rfl⟩ : syracuseStep 2350997 = 110203) (by norm_num)
theorem B3170245 : Blo 694316 3170245 := bbase (se 4 (by rfl) ⟨297210, by rfl⟩ : syracuseStep 3170245 = 594421) (by norm_num)
theorem B1564613 : Blo 694316 1564613 := bbase (se 4 (by rfl) ⟨146682, by rfl⟩ : syracuseStep 1564613 = 293365) (by norm_num)
theorem B1564685 : Blo 694316 1564685 := bbase (se 3 (by rfl) ⟨293378, by rfl⟩ : syracuseStep 1564685 = 586757) (by norm_num)
theorem B3530789 : Blo 694316 3530789 := bbase (se 4 (by rfl) ⟨331011, by rfl⟩ : syracuseStep 3530789 = 662023) (by norm_num)
theorem B1564757 : Blo 694316 1564757 := bbase (se 8 (by rfl) ⟨9168, by rfl⟩ : syracuseStep 1564757 = 18337) (by norm_num)
theorem B1761365 : Blo 694316 1761365 := bbase (se 8 (by rfl) ⟨10320, by rfl⟩ : syracuseStep 1761365 = 20641) (by norm_num)
theorem B1564829 : Blo 694316 1564829 := bbase (se 3 (by rfl) ⟨293405, by rfl⟩ : syracuseStep 1564829 = 586811) (by norm_num)
theorem B8904917 : Blo 694316 8904917 := bbase (se 7 (by rfl) ⟨104354, by rfl⟩ : syracuseStep 8904917 = 208709) (by norm_num)
theorem B1171685 : Blo 694316 1171685 := bbase (se 4 (by rfl) ⟨109845, by rfl⟩ : syracuseStep 1171685 = 219691) (by norm_num)
theorem B1564901 : Blo 694316 1564901 := bbase (se 4 (by rfl) ⟨146709, by rfl⟩ : syracuseStep 1564901 = 293419) (by norm_num)
theorem B942349 : Blo 694316 942349 := bbase (se 3 (by rfl) ⟨176690, by rfl⟩ : syracuseStep 942349 = 353381) (by norm_num)
theorem B1564973 : Blo 694316 1564973 := bbase (se 3 (by rfl) ⟨293432, by rfl⟩ : syracuseStep 1564973 = 586865) (by norm_num)
theorem B2351429 : Blo 694316 2351429 := bbase (se 4 (by rfl) ⟨220446, by rfl⟩ : syracuseStep 2351429 = 440893) (by norm_num)
theorem B1171813 : Blo 694316 1171813 := bbase (se 4 (by rfl) ⟨109857, by rfl⟩ : syracuseStep 1171813 = 219715) (by norm_num)
theorem B1565045 : Blo 694316 1565045 := bbase (se 5 (by rfl) ⟨73361, by rfl⟩ : syracuseStep 1565045 = 146723) (by norm_num)
theorem B1761709 : Blo 694316 1761709 := bbase (se 3 (by rfl) ⟨330320, by rfl⟩ : syracuseStep 1761709 = 660641) (by norm_num)
theorem B3957173 : Blo 694316 3957173 := bbase (se 5 (by rfl) ⟨185492, by rfl⟩ : syracuseStep 3957173 = 370985) (by norm_num)
theorem B1171901 : Blo 694316 1171901 := bbase (se 3 (by rfl) ⟨219731, by rfl⟩ : syracuseStep 1171901 = 439463) (by norm_num)
theorem B1565117 : Blo 694316 1565117 := bbase (se 3 (by rfl) ⟨293459, by rfl⟩ : syracuseStep 1565117 = 586919) (by norm_num)
theorem B1565189 : Blo 694316 1565189 := bbase (se 4 (by rfl) ⟨146736, by rfl⟩ : syracuseStep 1565189 = 293473) (by norm_num)
theorem B1761821 : Blo 694316 1761821 := bbase (se 3 (by rfl) ⟨330341, by rfl⟩ : syracuseStep 1761821 = 660683) (by norm_num)
theorem B1172029 : Blo 694316 1172029 := bbase (se 3 (by rfl) ⟨219755, by rfl⟩ : syracuseStep 1172029 = 439511) (by norm_num)
theorem B1565261 : Blo 694316 1565261 := bbase (se 3 (by rfl) ⟨293486, by rfl⟩ : syracuseStep 1565261 = 586973) (by norm_num)
theorem B1172117 : Blo 694316 1172117 := bbase (se 6 (by rfl) ⟨27471, by rfl⟩ : syracuseStep 1172117 = 54943) (by norm_num)
theorem B1565333 : Blo 694316 1565333 := bbase (se 6 (by rfl) ⟨36687, by rfl⟩ : syracuseStep 1565333 = 73375) (by norm_num)
theorem B8938133 : Blo 694316 8938133 := bbase (se 6 (by rfl) ⟨209487, by rfl⟩ : syracuseStep 8938133 = 418975) (by norm_num)
theorem B1565405 : Blo 694316 1565405 := bbase (se 3 (by rfl) ⟨293513, by rfl⟩ : syracuseStep 1565405 = 587027) (by norm_num)
theorem B1762013 : Blo 694316 1762013 := bbase (se 3 (by rfl) ⟨330377, by rfl⟩ : syracuseStep 1762013 = 660755) (by norm_num)
theorem B2351861 : Blo 694316 2351861 := bbase (se 5 (by rfl) ⟨110243, by rfl⟩ : syracuseStep 2351861 = 220487) (by norm_num)
theorem B2286341 : Blo 694316 2286341 := bbase (se 4 (by rfl) ⟨214344, by rfl⟩ : syracuseStep 2286341 = 428689) (by norm_num)
theorem B1172245 : Blo 694316 1172245 := bbase (se 6 (by rfl) ⟨27474, by rfl⟩ : syracuseStep 1172245 = 54949) (by norm_num)
theorem B1565477 : Blo 694316 1565477 := bbase (se 4 (by rfl) ⟨146763, by rfl⟩ : syracuseStep 1565477 = 293527) (by norm_num)
theorem B1336109 : Blo 694316 1336109 := bbase (se 3 (by rfl) ⟨250520, by rfl⟩ : syracuseStep 1336109 = 501041) (by norm_num)
theorem B4449077 : Blo 694316 4449077 := bbase (se 5 (by rfl) ⟨208550, by rfl⟩ : syracuseStep 4449077 = 417101) (by norm_num)
theorem B1172333 : Blo 694316 1172333 := bbase (se 3 (by rfl) ⟨219812, by rfl⟩ : syracuseStep 1172333 = 439625) (by norm_num)
theorem B1565549 : Blo 694316 1565549 := bbase (se 3 (by rfl) ⟨293540, by rfl⟩ : syracuseStep 1565549 = 587081) (by norm_num)
theorem B942997 : Blo 694316 942997 := bbase (se 6 (by rfl) ⟨22101, by rfl⟩ : syracuseStep 942997 = 44203) (by norm_num)
theorem B1565621 : Blo 694316 1565621 := bbase (se 5 (by rfl) ⟨73388, by rfl⟩ : syracuseStep 1565621 = 146777) (by norm_num)
theorem B1172461 : Blo 694316 1172461 := bbase (se 3 (by rfl) ⟨219836, by rfl⟩ : syracuseStep 1172461 = 439673) (by norm_num)
theorem B1565693 : Blo 694316 1565693 := bbase (se 3 (by rfl) ⟨293567, by rfl⟩ : syracuseStep 1565693 = 587135) (by norm_num)
theorem B1762357 : Blo 694316 1762357 := bbase (se 5 (by rfl) ⟨82610, by rfl⟩ : syracuseStep 1762357 = 165221) (by norm_num)
theorem B1172549 : Blo 694316 1172549 := bbase (se 4 (by rfl) ⟨109926, by rfl⟩ : syracuseStep 1172549 = 219853) (by norm_num)
theorem B1565765 : Blo 694316 1565765 := bbase (se 4 (by rfl) ⟨146790, by rfl⟩ : syracuseStep 1565765 = 293581) (by norm_num)
theorem B1041485 : Blo 694316 1041485 := bbase (se 3 (by rfl) ⟨195278, by rfl⟩ : syracuseStep 1041485 = 390557) (by norm_num)
theorem B1041509 : Blo 694316 1041509 := bbase (se 4 (by rfl) ⟨97641, by rfl⟩ : syracuseStep 1041509 = 195283) (by norm_num)
theorem B1041533 : Blo 694316 1041533 := bbase (se 3 (by rfl) ⟨195287, by rfl⟩ : syracuseStep 1041533 = 390575) (by norm_num)
theorem B1565837 : Blo 694316 1565837 := bbase (se 3 (by rfl) ⟨293594, by rfl⟩ : syracuseStep 1565837 = 587189) (by norm_num)
theorem B1041557 : Blo 694316 1041557 := bbase (se 6 (by rfl) ⟨24411, by rfl⟩ : syracuseStep 1041557 = 48823) (by norm_num)
theorem B1762469 : Blo 694316 1762469 := bbase (se 4 (by rfl) ⟨165231, by rfl⟩ : syracuseStep 1762469 = 330463) (by norm_num)
theorem B2352293 : Blo 694316 2352293 := bbase (se 4 (by rfl) ⟨220527, by rfl⟩ : syracuseStep 2352293 = 441055) (by norm_num)
theorem B1041581 : Blo 694316 1041581 := bbase (se 3 (by rfl) ⟨195296, by rfl⟩ : syracuseStep 1041581 = 390593) (by norm_num)
theorem B1041605 : Blo 694316 1041605 := bbase (se 4 (by rfl) ⟨97650, by rfl⟩ : syracuseStep 1041605 = 195301) (by norm_num)
theorem B1172677 : Blo 694316 1172677 := bbase (se 4 (by rfl) ⟨109938, by rfl⟩ : syracuseStep 1172677 = 219877) (by norm_num)
theorem B1565909 : Blo 694316 1565909 := bbase (se 7 (by rfl) ⟨18350, by rfl⟩ : syracuseStep 1565909 = 36701) (by norm_num)
theorem B1041629 : Blo 694316 1041629 := bbase (se 3 (by rfl) ⟨195305, by rfl⟩ : syracuseStep 1041629 = 390611) (by norm_num)
theorem B1041653 : Blo 694316 1041653 := bbase (se 5 (by rfl) ⟨48827, by rfl⟩ : syracuseStep 1041653 = 97655) (by norm_num)
theorem B1041677 : Blo 694316 1041677 := bbase (se 3 (by rfl) ⟨195314, by rfl⟩ : syracuseStep 1041677 = 390629) (by norm_num)
theorem B1172765 : Blo 694316 1172765 := bbase (se 3 (by rfl) ⟨219893, by rfl⟩ : syracuseStep 1172765 = 439787) (by norm_num)
theorem B1565981 : Blo 694316 1565981 := bbase (se 3 (by rfl) ⟨293621, by rfl⟩ : syracuseStep 1565981 = 587243) (by norm_num)
theorem B1041701 : Blo 694316 1041701 := bbase (se 4 (by rfl) ⟨97659, by rfl⟩ : syracuseStep 1041701 = 195319) (by norm_num)
theorem B2647349 : Blo 694316 2647349 := bbase (se 5 (by rfl) ⟨124094, by rfl⟩ : syracuseStep 2647349 = 248189) (by norm_num)
theorem B3532085 : Blo 694316 3532085 := bbase (se 5 (by rfl) ⟨165566, by rfl⟩ : syracuseStep 3532085 = 331133) (by norm_num)
theorem B1041725 : Blo 694316 1041725 := bbase (se 3 (by rfl) ⟨195323, by rfl⟩ : syracuseStep 1041725 = 390647) (by norm_num)
theorem B1041749 : Blo 694316 1041749 := bbase (se 12 (by rfl) ⟨381, by rfl⟩ : syracuseStep 1041749 = 763) (by norm_num)
theorem B1566053 : Blo 694316 1566053 := bbase (se 4 (by rfl) ⟨146817, by rfl⟩ : syracuseStep 1566053 = 293635) (by norm_num)
theorem B1762661 : Blo 694316 1762661 := bbase (se 4 (by rfl) ⟨165249, by rfl⟩ : syracuseStep 1762661 = 330499) (by norm_num)
theorem B1041773 : Blo 694316 1041773 := bbase (se 3 (by rfl) ⟨195332, by rfl⟩ : syracuseStep 1041773 = 390665) (by norm_num)
theorem B1041797 : Blo 694316 1041797 := bbase (se 4 (by rfl) ⟨97668, by rfl⟩ : syracuseStep 1041797 = 195337) (by norm_num)
theorem B1041821 : Blo 694316 1041821 := bbase (se 3 (by rfl) ⟨195341, by rfl⟩ : syracuseStep 1041821 = 390683) (by norm_num)
theorem B1172893 : Blo 694316 1172893 := bbase (se 3 (by rfl) ⟨219917, by rfl⟩ : syracuseStep 1172893 = 439835) (by norm_num)
theorem B1566125 : Blo 694316 1566125 := bbase (se 3 (by rfl) ⟨293648, by rfl⟩ : syracuseStep 1566125 = 587297) (by norm_num)
theorem B1041845 : Blo 694316 1041845 := bbase (se 5 (by rfl) ⟨48836, by rfl⟩ : syracuseStep 1041845 = 97673) (by norm_num)
theorem B5662133 : Blo 694316 5662133 := bbase (se 5 (by rfl) ⟨265412, by rfl⟩ : syracuseStep 5662133 = 530825) (by norm_num)
theorem B714169 : Blo 694316 714169 := bbase (se 2 (by rfl) ⟨267813, by rfl⟩ : syracuseStep 714169 = 535627) (by norm_num)
theorem B1041869 : Blo 694316 1041869 := bbase (se 3 (by rfl) ⟨195350, by rfl⟩ : syracuseStep 1041869 = 390701) (by norm_num)
theorem B1041893 : Blo 694316 1041893 := bbase (se 4 (by rfl) ⟨97677, by rfl⟩ : syracuseStep 1041893 = 195355) (by norm_num)
theorem B1172981 : Blo 694316 1172981 := bbase (se 5 (by rfl) ⟨54983, by rfl⟩ : syracuseStep 1172981 = 109967) (by norm_num)
theorem B1566197 : Blo 694316 1566197 := bbase (se 5 (by rfl) ⟨73415, by rfl⟩ : syracuseStep 1566197 = 146831) (by norm_num)
theorem B1041917 : Blo 694316 1041917 := bbase (se 3 (by rfl) ⟨195359, by rfl⟩ : syracuseStep 1041917 = 390719) (by norm_num)
theorem B1041941 : Blo 694316 1041941 := bbase (se 6 (by rfl) ⟨24420, by rfl⟩ : syracuseStep 1041941 = 48841) (by norm_num)
theorem B1041965 : Blo 694316 1041965 := bbase (se 3 (by rfl) ⟨195368, by rfl⟩ : syracuseStep 1041965 = 390737) (by norm_num)
theorem B1566269 : Blo 694316 1566269 := bbase (se 3 (by rfl) ⟨293675, by rfl⟩ : syracuseStep 1566269 = 587351) (by norm_num)
theorem B1041989 : Blo 694316 1041989 := bbase (se 4 (by rfl) ⟨97686, by rfl⟩ : syracuseStep 1041989 = 195373) (by norm_num)
theorem B2352725 : Blo 694316 2352725 := bbase (se 8 (by rfl) ⟨13785, by rfl⟩ : syracuseStep 2352725 = 27571) (by norm_num)
theorem B2647637 : Blo 694316 2647637 := bbase (se 8 (by rfl) ⟨15513, by rfl⟩ : syracuseStep 2647637 = 31027) (by norm_num)
theorem B1042013 : Blo 694316 1042013 := bbase (se 3 (by rfl) ⟨195377, by rfl⟩ : syracuseStep 1042013 = 390755) (by norm_num)
theorem B1042037 : Blo 694316 1042037 := bbase (se 5 (by rfl) ⟨48845, by rfl⟩ : syracuseStep 1042037 = 97691) (by norm_num)
theorem B1173109 : Blo 694316 1173109 := bbase (se 5 (by rfl) ⟨54989, by rfl⟩ : syracuseStep 1173109 = 109979) (by norm_num)
theorem B1566341 : Blo 694316 1566341 := bbase (se 4 (by rfl) ⟨146844, by rfl⟩ : syracuseStep 1566341 = 293689) (by norm_num)
theorem B1042061 : Blo 694316 1042061 := bbase (se 3 (by rfl) ⟨195386, by rfl⟩ : syracuseStep 1042061 = 390773) (by norm_num)
theorem B1042085 : Blo 694316 1042085 := bbase (se 4 (by rfl) ⟨97695, by rfl⟩ : syracuseStep 1042085 = 195391) (by norm_num)
theorem B1042109 : Blo 694316 1042109 := bbase (se 3 (by rfl) ⟨195395, by rfl⟩ : syracuseStep 1042109 = 390791) (by norm_num)
theorem B1763005 : Blo 694316 1763005 := bbase (se 3 (by rfl) ⟨330563, by rfl⟩ : syracuseStep 1763005 = 661127) (by norm_num)
theorem B1173197 : Blo 694316 1173197 := bbase (se 3 (by rfl) ⟨219974, by rfl⟩ : syracuseStep 1173197 = 439949) (by norm_num)
theorem B1566413 : Blo 694316 1566413 := bbase (se 3 (by rfl) ⟨293702, by rfl⟩ : syracuseStep 1566413 = 587405) (by norm_num)
theorem B1042133 : Blo 694316 1042133 := bbase (se 7 (by rfl) ⟨12212, by rfl⟩ : syracuseStep 1042133 = 24425) (by norm_num)
theorem B20113109 : Blo 694316 20113109 := bbase (se 7 (by rfl) ⟨235700, by rfl⟩ : syracuseStep 20113109 = 471401) (by norm_num)
theorem B1042157 : Blo 694316 1042157 := bbase (se 3 (by rfl) ⟨195404, by rfl⟩ : syracuseStep 1042157 = 390809) (by norm_num)
theorem B1042181 : Blo 694316 1042181 := bbase (se 4 (by rfl) ⟨97704, by rfl⟩ : syracuseStep 1042181 = 195409) (by norm_num)
theorem B1566485 : Blo 694316 1566485 := bbase (se 6 (by rfl) ⟨36714, by rfl⟩ : syracuseStep 1566485 = 73429) (by norm_num)
theorem B1042205 : Blo 694316 1042205 := bbase (se 3 (by rfl) ⟨195413, by rfl⟩ : syracuseStep 1042205 = 390827) (by norm_num)
theorem B1763117 : Blo 694316 1763117 := bbase (se 3 (by rfl) ⟨330584, by rfl⟩ : syracuseStep 1763117 = 661169) (by norm_num)
theorem B1042229 : Blo 694316 1042229 := bbase (se 5 (by rfl) ⟨48854, by rfl⟩ : syracuseStep 1042229 = 97709) (by norm_num)
theorem B1042253 : Blo 694316 1042253 := bbase (se 3 (by rfl) ⟨195422, by rfl⟩ : syracuseStep 1042253 = 390845) (by norm_num)
theorem B1173325 : Blo 694316 1173325 := bbase (se 3 (by rfl) ⟨219998, by rfl⟩ : syracuseStep 1173325 = 439997) (by norm_num)
theorem B1566557 : Blo 694316 1566557 := bbase (se 3 (by rfl) ⟨293729, by rfl⟩ : syracuseStep 1566557 = 587459) (by norm_num)
theorem B1042277 : Blo 694316 1042277 := bbase (se 4 (by rfl) ⟨97713, by rfl⟩ : syracuseStep 1042277 = 195427) (by norm_num)
theorem B1632101 : Blo 694316 1632101 := bbase (se 4 (by rfl) ⟨153009, by rfl⟩ : syracuseStep 1632101 = 306019) (by norm_num)
theorem B1042301 : Blo 694316 1042301 := bbase (se 3 (by rfl) ⟨195431, by rfl⟩ : syracuseStep 1042301 = 390863) (by norm_num)
theorem B1042325 : Blo 694316 1042325 := bbase (se 6 (by rfl) ⟨24429, by rfl⟩ : syracuseStep 1042325 = 48859) (by norm_num)
theorem B1173413 : Blo 694316 1173413 := bbase (se 4 (by rfl) ⟨110007, by rfl⟩ : syracuseStep 1173413 = 220015) (by norm_num)
theorem B1566629 : Blo 694316 1566629 := bbase (se 4 (by rfl) ⟨146871, by rfl⟩ : syracuseStep 1566629 = 293743) (by norm_num)
theorem B1042349 : Blo 694316 1042349 := bbase (se 3 (by rfl) ⟨195440, by rfl⟩ : syracuseStep 1042349 = 390881) (by norm_num)
theorem B1042373 : Blo 694316 1042373 := bbase (se 4 (by rfl) ⟨97722, by rfl⟩ : syracuseStep 1042373 = 195445) (by norm_num)
theorem B1042397 : Blo 694316 1042397 := bbase (se 3 (by rfl) ⟨195449, by rfl⟩ : syracuseStep 1042397 = 390899) (by norm_num)
theorem B1566701 : Blo 694316 1566701 := bbase (se 3 (by rfl) ⟨293756, by rfl⟩ : syracuseStep 1566701 = 587513) (by norm_num)
theorem B1763309 : Blo 694316 1763309 := bbase (se 3 (by rfl) ⟨330620, by rfl⟩ : syracuseStep 1763309 = 661241) (by norm_num)
theorem B1042421 : Blo 694316 1042421 := bbase (se 5 (by rfl) ⟨48863, by rfl⟩ : syracuseStep 1042421 = 97727) (by norm_num)
theorem B2353157 : Blo 694316 2353157 := bbase (se 4 (by rfl) ⟨220608, by rfl⟩ : syracuseStep 2353157 = 441217) (by norm_num)
theorem B1042445 : Blo 694316 1042445 := bbase (se 3 (by rfl) ⟨195458, by rfl⟩ : syracuseStep 1042445 = 390917) (by norm_num)
theorem B1042469 : Blo 694316 1042469 := bbase (se 4 (by rfl) ⟨97731, by rfl⟩ : syracuseStep 1042469 = 195463) (by norm_num)
theorem B1173541 : Blo 694316 1173541 := bbase (se 4 (by rfl) ⟨110019, by rfl⟩ : syracuseStep 1173541 = 220039) (by norm_num)
theorem B1566773 : Blo 694316 1566773 := bbase (se 5 (by rfl) ⟨73442, by rfl⟩ : syracuseStep 1566773 = 146885) (by norm_num)
theorem B1042493 : Blo 694316 1042493 := bbase (se 3 (by rfl) ⟨195467, by rfl⟩ : syracuseStep 1042493 = 390935) (by norm_num)
theorem B1042517 : Blo 694316 1042517 := bbase (se 8 (by rfl) ⟨6108, by rfl⟩ : syracuseStep 1042517 = 12217) (by norm_num)
theorem B1042541 : Blo 694316 1042541 := bbase (se 3 (by rfl) ⟨195476, by rfl⟩ : syracuseStep 1042541 = 390953) (by norm_num)
theorem B1173629 : Blo 694316 1173629 := bbase (se 3 (by rfl) ⟨220055, by rfl⟩ : syracuseStep 1173629 = 440111) (by norm_num)
theorem B1566845 : Blo 694316 1566845 := bbase (se 3 (by rfl) ⟨293783, by rfl⟩ : syracuseStep 1566845 = 587567) (by norm_num)
theorem B1042565 : Blo 694316 1042565 := bbase (se 4 (by rfl) ⟨97740, by rfl⟩ : syracuseStep 1042565 = 195481) (by norm_num)
theorem B1042589 : Blo 694316 1042589 := bbase (se 3 (by rfl) ⟨195485, by rfl⟩ : syracuseStep 1042589 = 390971) (by norm_num)
theorem B1271965 : Blo 694316 1271965 := bbase (se 3 (by rfl) ⟨238493, by rfl⟩ : syracuseStep 1271965 = 476987) (by norm_num)
theorem B1042613 : Blo 694316 1042613 := bbase (se 5 (by rfl) ⟨48872, by rfl⟩ : syracuseStep 1042613 = 97745) (by norm_num)
theorem B878789 : Blo 694316 878789 := bbase (se 4 (by rfl) ⟨82386, by rfl⟩ : syracuseStep 878789 = 164773) (by norm_num)
theorem B1566917 : Blo 694316 1566917 := bbase (se 4 (by rfl) ⟨146898, by rfl⟩ : syracuseStep 1566917 = 293797) (by norm_num)
theorem B1042637 : Blo 694316 1042637 := bbase (se 3 (by rfl) ⟨195494, by rfl⟩ : syracuseStep 1042637 = 390989) (by norm_num)
theorem B1042661 : Blo 694316 1042661 := bbase (se 4 (by rfl) ⟨97749, by rfl⟩ : syracuseStep 1042661 = 195499) (by norm_num)
theorem B878845 : Blo 694316 878845 := bbase (se 3 (by rfl) ⟨164783, by rfl⟩ : syracuseStep 878845 = 329567) (by norm_num)
theorem B1042685 : Blo 694316 1042685 := bbase (se 3 (by rfl) ⟨195503, by rfl⟩ : syracuseStep 1042685 = 391007) (by norm_num)
theorem B1173757 : Blo 694316 1173757 := bbase (se 3 (by rfl) ⟨220079, by rfl⟩ : syracuseStep 1173757 = 440159) (by norm_num)
theorem B1566989 : Blo 694316 1566989 := bbase (se 3 (by rfl) ⟨293810, by rfl⟩ : syracuseStep 1566989 = 587621) (by norm_num)
theorem B1042709 : Blo 694316 1042709 := bbase (se 6 (by rfl) ⟨24438, by rfl⟩ : syracuseStep 1042709 = 48877) (by norm_num)
theorem B1042733 : Blo 694316 1042733 := bbase (se 3 (by rfl) ⟨195512, by rfl⟩ : syracuseStep 1042733 = 391025) (by norm_num)
theorem B1042757 : Blo 694316 1042757 := bbase (se 4 (by rfl) ⟨97758, by rfl⟩ : syracuseStep 1042757 = 195517) (by norm_num)
theorem B1763653 : Blo 694316 1763653 := bbase (se 4 (by rfl) ⟨165342, by rfl⟩ : syracuseStep 1763653 = 330685) (by norm_num)
theorem B1173845 : Blo 694316 1173845 := bbase (se 10 (by rfl) ⟨1719, by rfl⟩ : syracuseStep 1173845 = 3439) (by norm_num)
theorem B1567061 : Blo 694316 1567061 := bbase (se 10 (by rfl) ⟨2295, by rfl⟩ : syracuseStep 1567061 = 4591) (by norm_num)
theorem B878941 : Blo 694316 878941 := bbase (se 3 (by rfl) ⟨164801, by rfl⟩ : syracuseStep 878941 = 329603) (by norm_num)
theorem B1042781 : Blo 694316 1042781 := bbase (se 3 (by rfl) ⟨195521, by rfl⟩ : syracuseStep 1042781 = 391043) (by norm_num)
theorem B1042805 : Blo 694316 1042805 := bbase (se 5 (by rfl) ⟨48881, by rfl⟩ : syracuseStep 1042805 = 97763) (by norm_num)
theorem B1042829 : Blo 694316 1042829 := bbase (se 3 (by rfl) ⟨195530, by rfl⟩ : syracuseStep 1042829 = 391061) (by norm_num)
theorem B1567133 : Blo 694316 1567133 := bbase (se 3 (by rfl) ⟨293837, by rfl⟩ : syracuseStep 1567133 = 587675) (by norm_num)
theorem B1042853 : Blo 694316 1042853 := bbase (se 4 (by rfl) ⟨97767, by rfl⟩ : syracuseStep 1042853 = 195535) (by norm_num)
theorem B1763765 : Blo 694316 1763765 := bbase (se 5 (by rfl) ⟨82676, by rfl⟩ : syracuseStep 1763765 = 165353) (by norm_num)
theorem B2353589 : Blo 694316 2353589 := bbase (se 5 (by rfl) ⟨110324, by rfl⟩ : syracuseStep 2353589 = 220649) (by norm_num)
theorem B1042877 : Blo 694316 1042877 := bbase (se 3 (by rfl) ⟨195539, by rfl⟩ : syracuseStep 1042877 = 391079) (by norm_num)
theorem B1042901 : Blo 694316 1042901 := bbase (se 7 (by rfl) ⟨12221, by rfl⟩ : syracuseStep 1042901 = 24443) (by norm_num)
theorem B1173973 : Blo 694316 1173973 := bbase (se 7 (by rfl) ⟨13757, by rfl⟩ : syracuseStep 1173973 = 27515) (by norm_num)
theorem B1567205 : Blo 694316 1567205 := bbase (se 4 (by rfl) ⟨146925, by rfl⟩ : syracuseStep 1567205 = 293851) (by norm_num)
theorem B1042925 : Blo 694316 1042925 := bbase (se 3 (by rfl) ⟨195548, by rfl⟩ : syracuseStep 1042925 = 391097) (by norm_num)
theorem B1042949 : Blo 694316 1042949 := bbase (se 4 (by rfl) ⟨97776, by rfl⟩ : syracuseStep 1042949 = 195553) (by norm_num)
theorem B879113 : Blo 694316 879113 := bbase (se 2 (by rfl) ⟨329667, by rfl⟩ : syracuseStep 879113 = 659335) (by norm_num)
theorem B1042973 : Blo 694316 1042973 := bbase (se 3 (by rfl) ⟨195557, by rfl⟩ : syracuseStep 1042973 = 391115) (by norm_num)
theorem B1174061 : Blo 694316 1174061 := bbase (se 3 (by rfl) ⟨220136, by rfl⟩ : syracuseStep 1174061 = 440273) (by norm_num)
theorem B1567277 : Blo 694316 1567277 := bbase (se 3 (by rfl) ⟨293864, by rfl⟩ : syracuseStep 1567277 = 587729) (by norm_num)
theorem B1042997 : Blo 694316 1042997 := bbase (se 5 (by rfl) ⟨48890, by rfl⟩ : syracuseStep 1042997 = 97781) (by norm_num)
theorem B879169 : Blo 694316 879169 := bbase (se 2 (by rfl) ⟨329688, by rfl⟩ : syracuseStep 879169 = 659377) (by norm_num)
theorem B3533381 : Blo 694316 3533381 := bbase (se 4 (by rfl) ⟨331254, by rfl⟩ : syracuseStep 3533381 = 662509) (by norm_num)
theorem B1043021 : Blo 694316 1043021 := bbase (se 3 (by rfl) ⟨195566, by rfl⟩ : syracuseStep 1043021 = 391133) (by norm_num)
theorem B3959381 : Blo 694316 3959381 := bbase (se 8 (by rfl) ⟨23199, by rfl⟩ : syracuseStep 3959381 = 46399) (by norm_num)
theorem B1043045 : Blo 694316 1043045 := bbase (se 4 (by rfl) ⟨97785, by rfl⟩ : syracuseStep 1043045 = 195571) (by norm_num)
theorem B1567349 : Blo 694316 1567349 := bbase (se 5 (by rfl) ⟨73469, by rfl⟩ : syracuseStep 1567349 = 146939) (by norm_num)
theorem B1763957 : Blo 694316 1763957 := bbase (se 5 (by rfl) ⟨82685, by rfl⟩ : syracuseStep 1763957 = 165371) (by norm_num)
theorem B1043069 : Blo 694316 1043069 := bbase (se 3 (by rfl) ⟨195575, by rfl⟩ : syracuseStep 1043069 = 391151) (by norm_num)
theorem B1043093 : Blo 694316 1043093 := bbase (se 6 (by rfl) ⟨24447, by rfl⟩ : syracuseStep 1043093 = 48895) (by norm_num)
theorem B879265 : Blo 694316 879265 := bbase (se 2 (by rfl) ⟨329724, by rfl⟩ : syracuseStep 879265 = 659449) (by norm_num)
theorem B1043117 : Blo 694316 1043117 := bbase (se 3 (by rfl) ⟨195584, by rfl⟩ : syracuseStep 1043117 = 391169) (by norm_num)
theorem B1174189 : Blo 694316 1174189 := bbase (se 3 (by rfl) ⟨220160, by rfl⟩ : syracuseStep 1174189 = 440321) (by norm_num)
theorem B1567421 : Blo 694316 1567421 := bbase (se 3 (by rfl) ⟨293891, by rfl⟩ : syracuseStep 1567421 = 587783) (by norm_num)
theorem B1043141 : Blo 694316 1043141 := bbase (se 4 (by rfl) ⟨97794, by rfl⟩ : syracuseStep 1043141 = 195589) (by norm_num)
theorem B1043165 : Blo 694316 1043165 := bbase (se 3 (by rfl) ⟨195593, by rfl⟩ : syracuseStep 1043165 = 391187) (by norm_num)
theorem B1043189 : Blo 694316 1043189 := bbase (se 5 (by rfl) ⟨48899, by rfl⟩ : syracuseStep 1043189 = 97799) (by norm_num)
theorem B2648821 : Blo 694316 2648821 := bbase (se 5 (by rfl) ⟨124163, by rfl⟩ : syracuseStep 2648821 = 248327) (by norm_num)
theorem B1174277 : Blo 694316 1174277 := bbase (se 4 (by rfl) ⟨110088, by rfl⟩ : syracuseStep 1174277 = 220177) (by norm_num)
theorem B1567493 : Blo 694316 1567493 := bbase (se 4 (by rfl) ⟨146952, by rfl⟩ : syracuseStep 1567493 = 293905) (by norm_num)
theorem B1043213 : Blo 694316 1043213 := bbase (se 3 (by rfl) ⟨195602, by rfl⟩ : syracuseStep 1043213 = 391205) (by norm_num)
theorem B846617 : Blo 694316 846617 := bbase (se 2 (by rfl) ⟨317481, by rfl⟩ : syracuseStep 846617 = 634963) (by norm_num)
theorem B1043237 : Blo 694316 1043237 := bbase (se 4 (by rfl) ⟨97803, by rfl⟩ : syracuseStep 1043237 = 195607) (by norm_num)
theorem B1043261 : Blo 694316 1043261 := bbase (se 3 (by rfl) ⟨195611, by rfl⟩ : syracuseStep 1043261 = 391223) (by norm_num)
theorem B3566405 : Blo 694316 3566405 := bbase (se 4 (by rfl) ⟨334350, by rfl⟩ : syracuseStep 3566405 = 668701) (by norm_num)
theorem B879437 : Blo 694316 879437 := bbase (se 3 (by rfl) ⟨164894, by rfl⟩ : syracuseStep 879437 = 329789) (by norm_num)
theorem B1567565 : Blo 694316 1567565 := bbase (se 3 (by rfl) ⟨293918, by rfl⟩ : syracuseStep 1567565 = 587837) (by norm_num)
theorem B781141 : Blo 694316 781141 := bbase (se 9 (by rfl) ⟨2288, by rfl⟩ : syracuseStep 781141 = 4577) (by norm_num)
theorem B1043285 : Blo 694316 1043285 := bbase (se 9 (by rfl) ⟨3056, by rfl⟩ : syracuseStep 1043285 = 6113) (by norm_num)
theorem B2354021 : Blo 694316 2354021 := bbase (se 4 (by rfl) ⟨220689, by rfl⟩ : syracuseStep 2354021 = 441379) (by norm_num)
theorem B1043309 : Blo 694316 1043309 := bbase (se 3 (by rfl) ⟨195620, by rfl⟩ : syracuseStep 1043309 = 391241) (by norm_num)
theorem B5368693 : Blo 694316 5368693 := bbase (se 5 (by rfl) ⟨251657, by rfl⟩ : syracuseStep 5368693 = 503315) (by norm_num)
theorem B781177 : Blo 694316 781177 := bbase (se 2 (by rfl) ⟨292941, by rfl⟩ : syracuseStep 781177 = 585883) (by norm_num)
theorem B879493 : Blo 694316 879493 := bbase (se 4 (by rfl) ⟨82452, by rfl⟩ : syracuseStep 879493 = 164905) (by norm_num)
theorem B1043333 : Blo 694316 1043333 := bbase (se 4 (by rfl) ⟨97812, by rfl⟩ : syracuseStep 1043333 = 195625) (by norm_num)
theorem B1174405 : Blo 694316 1174405 := bbase (se 4 (by rfl) ⟨110100, by rfl⟩ : syracuseStep 1174405 = 220201) (by norm_num)
theorem B1567637 : Blo 694316 1567637 := bbase (se 6 (by rfl) ⟨36741, by rfl⟩ : syracuseStep 1567637 = 73483) (by norm_num)
theorem B781213 : Blo 694316 781213 := bbase (se 3 (by rfl) ⟨146477, by rfl⟩ : syracuseStep 781213 = 292955) (by norm_num)
theorem B1043357 : Blo 694316 1043357 := bbase (se 3 (by rfl) ⟨195629, by rfl⟩ : syracuseStep 1043357 = 391259) (by norm_num)
theorem B1043381 : Blo 694316 1043381 := bbase (se 5 (by rfl) ⟨48908, by rfl⟩ : syracuseStep 1043381 = 97817) (by norm_num)
theorem B781249 : Blo 694316 781249 := bbase (se 2 (by rfl) ⟨292968, by rfl⟩ : syracuseStep 781249 = 585937) (by norm_num)
theorem B1043405 : Blo 694316 1043405 := bbase (se 3 (by rfl) ⟨195638, by rfl⟩ : syracuseStep 1043405 = 391277) (by norm_num)
theorem B1764301 : Blo 694316 1764301 := bbase (se 3 (by rfl) ⟨330806, by rfl⟩ : syracuseStep 1764301 = 661613) (by norm_num)
theorem B1174493 : Blo 694316 1174493 := bbase (se 3 (by rfl) ⟨220217, by rfl⟩ : syracuseStep 1174493 = 440435) (by norm_num)
theorem B1567709 : Blo 694316 1567709 := bbase (se 3 (by rfl) ⟨293945, by rfl⟩ : syracuseStep 1567709 = 587891) (by norm_num)
theorem B781285 : Blo 694316 781285 := bbase (se 4 (by rfl) ⟨73245, by rfl⟩ : syracuseStep 781285 = 146491) (by norm_num)
theorem B879589 : Blo 694316 879589 := bbase (se 4 (by rfl) ⟨82461, by rfl⟩ : syracuseStep 879589 = 164923) (by norm_num)
theorem B1043429 : Blo 694316 1043429 := bbase (se 4 (by rfl) ⟨97821, by rfl⟩ : syracuseStep 1043429 = 195643) (by norm_num)
theorem B1043453 : Blo 694316 1043453 := bbase (se 3 (by rfl) ⟨195647, by rfl⟩ : syracuseStep 1043453 = 391295) (by norm_num)
theorem B781321 : Blo 694316 781321 := bbase (se 2 (by rfl) ⟨292995, by rfl⟩ : syracuseStep 781321 = 585991) (by norm_num)
theorem B1043477 : Blo 694316 1043477 := bbase (se 6 (by rfl) ⟨24456, by rfl⟩ : syracuseStep 1043477 = 48913) (by norm_num)
theorem B1567781 : Blo 694316 1567781 := bbase (se 4 (by rfl) ⟨146979, by rfl⟩ : syracuseStep 1567781 = 293959) (by norm_num)
theorem B2649125 : Blo 694316 2649125 := bbase (se 4 (by rfl) ⟨248355, by rfl⟩ : syracuseStep 2649125 = 496711) (by norm_num)
theorem B781357 : Blo 694316 781357 := bbase (se 3 (by rfl) ⟨146504, by rfl⟩ : syracuseStep 781357 = 293009) (by norm_num)
theorem B1043501 : Blo 694316 1043501 := bbase (se 3 (by rfl) ⟨195656, by rfl⟩ : syracuseStep 1043501 = 391313) (by norm_num)
theorem B1764413 : Blo 694316 1764413 := bbase (se 3 (by rfl) ⟨330827, by rfl⟩ : syracuseStep 1764413 = 661655) (by norm_num)
theorem B1043525 : Blo 694316 1043525 := bbase (se 4 (by rfl) ⟨97830, by rfl⟩ : syracuseStep 1043525 = 195661) (by norm_num)
theorem B781393 : Blo 694316 781393 := bbase (se 2 (by rfl) ⟨293022, by rfl⟩ : syracuseStep 781393 = 586045) (by norm_num)
theorem B1043549 : Blo 694316 1043549 := bbase (se 3 (by rfl) ⟨195665, by rfl⟩ : syracuseStep 1043549 = 391331) (by norm_num)
theorem B1174621 : Blo 694316 1174621 := bbase (se 3 (by rfl) ⟨220241, by rfl⟩ : syracuseStep 1174621 = 440483) (by norm_num)
theorem B1567853 : Blo 694316 1567853 := bbase (se 3 (by rfl) ⟨293972, by rfl⟩ : syracuseStep 1567853 = 587945) (by norm_num)
theorem B781429 : Blo 694316 781429 := bbase (se 5 (by rfl) ⟨36629, by rfl⟩ : syracuseStep 781429 = 73259) (by norm_num)
theorem B1043573 : Blo 694316 1043573 := bbase (se 5 (by rfl) ⟨48917, by rfl⟩ : syracuseStep 1043573 = 97835) (by norm_num)
theorem B1043597 : Blo 694316 1043597 := bbase (se 3 (by rfl) ⟨195674, by rfl⟩ : syracuseStep 1043597 = 391349) (by norm_num)
theorem B879761 : Blo 694316 879761 := bbase (se 2 (by rfl) ⟨329910, by rfl⟩ : syracuseStep 879761 = 659821) (by norm_num)
theorem B781465 : Blo 694316 781465 := bbase (se 2 (by rfl) ⟨293049, by rfl⟩ : syracuseStep 781465 = 586099) (by norm_num)
theorem B1043621 : Blo 694316 1043621 := bbase (se 4 (by rfl) ⟨97839, by rfl⟩ : syracuseStep 1043621 = 195679) (by norm_num)
theorem B1174709 : Blo 694316 1174709 := bbase (se 5 (by rfl) ⟨55064, by rfl⟩ : syracuseStep 1174709 = 110129) (by norm_num)
theorem B1567925 : Blo 694316 1567925 := bbase (se 5 (by rfl) ⟨73496, by rfl⟩ : syracuseStep 1567925 = 146993) (by norm_num)
theorem B781501 : Blo 694316 781501 := bbase (se 3 (by rfl) ⟨146531, by rfl⟩ : syracuseStep 781501 = 293063) (by norm_num)
theorem B1043645 : Blo 694316 1043645 := bbase (se 3 (by rfl) ⟨195683, by rfl⟩ : syracuseStep 1043645 = 391367) (by norm_num)
theorem B879817 : Blo 694316 879817 := bbase (se 2 (by rfl) ⟨329931, by rfl⟩ : syracuseStep 879817 = 659863) (by norm_num)
theorem B1043669 : Blo 694316 1043669 := bbase (se 7 (by rfl) ⟨12230, by rfl⟩ : syracuseStep 1043669 = 24461) (by norm_num)
theorem B781537 : Blo 694316 781537 := bbase (se 2 (by rfl) ⟨293076, by rfl⟩ : syracuseStep 781537 = 586153) (by norm_num)
theorem B1043693 : Blo 694316 1043693 := bbase (se 3 (by rfl) ⟨195692, by rfl⟩ : syracuseStep 1043693 = 391385) (by norm_num)
theorem B1567997 : Blo 694316 1567997 := bbase (se 3 (by rfl) ⟨293999, by rfl⟩ : syracuseStep 1567997 = 587999) (by norm_num)
theorem B1764605 : Blo 694316 1764605 := bbase (se 3 (by rfl) ⟨330863, by rfl⟩ : syracuseStep 1764605 = 661727) (by norm_num)
theorem B781573 : Blo 694316 781573 := bbase (se 4 (by rfl) ⟨73272, by rfl⟩ : syracuseStep 781573 = 146545) (by norm_num)
theorem B1043717 : Blo 694316 1043717 := bbase (se 4 (by rfl) ⟨97848, by rfl⟩ : syracuseStep 1043717 = 195697) (by norm_num)
theorem B2354453 : Blo 694316 2354453 := bbase (se 6 (by rfl) ⟨55182, by rfl⟩ : syracuseStep 2354453 = 110365) (by norm_num)
theorem B1043741 : Blo 694316 1043741 := bbase (se 3 (by rfl) ⟨195701, by rfl⟩ : syracuseStep 1043741 = 391403) (by norm_num)
theorem B781609 : Blo 694316 781609 := bbase (se 2 (by rfl) ⟨293103, by rfl⟩ : syracuseStep 781609 = 586207) (by norm_num)
theorem B879913 : Blo 694316 879913 := bbase (se 2 (by rfl) ⟨329967, by rfl⟩ : syracuseStep 879913 = 659935) (by norm_num)
theorem B1043765 : Blo 694316 1043765 := bbase (se 5 (by rfl) ⟨48926, by rfl⟩ : syracuseStep 1043765 = 97853) (by norm_num)
theorem B1174837 : Blo 694316 1174837 := bbase (se 5 (by rfl) ⟨55070, by rfl⟩ : syracuseStep 1174837 = 110141) (by norm_num)
theorem B1568069 : Blo 694316 1568069 := bbase (se 4 (by rfl) ⟨147006, by rfl⟩ : syracuseStep 1568069 = 294013) (by norm_num)
theorem B781645 : Blo 694316 781645 := bbase (se 3 (by rfl) ⟨146558, by rfl⟩ : syracuseStep 781645 = 293117) (by norm_num)
theorem B1043789 : Blo 694316 1043789 := bbase (se 3 (by rfl) ⟨195710, by rfl⟩ : syracuseStep 1043789 = 391421) (by norm_num)
theorem B1043813 : Blo 694316 1043813 := bbase (se 4 (by rfl) ⟨97857, by rfl⟩ : syracuseStep 1043813 = 195715) (by norm_num)
theorem B781681 : Blo 694316 781681 := bbase (se 2 (by rfl) ⟨293130, by rfl⟩ : syracuseStep 781681 = 586261) (by norm_num)
theorem B1043837 : Blo 694316 1043837 := bbase (se 3 (by rfl) ⟨195719, by rfl⟩ : syracuseStep 1043837 = 391439) (by norm_num)
theorem B1174925 : Blo 694316 1174925 := bbase (se 3 (by rfl) ⟨220298, by rfl⟩ : syracuseStep 1174925 = 440597) (by norm_num)
theorem B1568141 : Blo 694316 1568141 := bbase (se 3 (by rfl) ⟨294026, by rfl⟩ : syracuseStep 1568141 = 588053) (by norm_num)
theorem B781717 : Blo 694316 781717 := bbase (se 6 (by rfl) ⟨18321, by rfl⟩ : syracuseStep 781717 = 36643) (by norm_num)
theorem B1043861 : Blo 694316 1043861 := bbase (se 6 (by rfl) ⟨24465, by rfl⟩ : syracuseStep 1043861 = 48931) (by norm_num)
theorem B1043885 : Blo 694316 1043885 := bbase (se 3 (by rfl) ⟨195728, by rfl⟩ : syracuseStep 1043885 = 391457) (by norm_num)
theorem B781753 : Blo 694316 781753 := bbase (se 2 (by rfl) ⟨293157, by rfl⟩ : syracuseStep 781753 = 586315) (by norm_num)
theorem B1043909 : Blo 694316 1043909 := bbase (se 4 (by rfl) ⟨97866, by rfl⟩ : syracuseStep 1043909 = 195733) (by norm_num)
theorem B880085 : Blo 694316 880085 := bbase (se 7 (by rfl) ⟨10313, by rfl⟩ : syracuseStep 880085 = 20627) (by norm_num)
theorem B1568213 : Blo 694316 1568213 := bbase (se 7 (by rfl) ⟨18377, by rfl⟩ : syracuseStep 1568213 = 36755) (by norm_num)
theorem B781789 : Blo 694316 781789 := bbase (se 3 (by rfl) ⟨146585, by rfl⟩ : syracuseStep 781789 = 293171) (by norm_num)
theorem B1043933 : Blo 694316 1043933 := bbase (se 3 (by rfl) ⟨195737, by rfl⟩ : syracuseStep 1043933 = 391475) (by norm_num)
theorem B1043957 : Blo 694316 1043957 := bbase (se 5 (by rfl) ⟨48935, by rfl⟩ : syracuseStep 1043957 = 97871) (by norm_num)
theorem B781825 : Blo 694316 781825 := bbase (se 2 (by rfl) ⟨293184, by rfl⟩ : syracuseStep 781825 = 586369) (by norm_num)
theorem B880141 : Blo 694316 880141 := bbase (se 3 (by rfl) ⟨165026, by rfl⟩ : syracuseStep 880141 = 330053) (by norm_num)
theorem B1043981 : Blo 694316 1043981 := bbase (se 3 (by rfl) ⟨195746, by rfl⟩ : syracuseStep 1043981 = 391493) (by norm_num)
theorem B1175053 : Blo 694316 1175053 := bbase (se 3 (by rfl) ⟨220322, by rfl⟩ : syracuseStep 1175053 = 440645) (by norm_num)
theorem B1568285 : Blo 694316 1568285 := bbase (se 3 (by rfl) ⟨294053, by rfl⟩ : syracuseStep 1568285 = 588107) (by norm_num)
theorem B781861 : Blo 694316 781861 := bbase (se 4 (by rfl) ⟨73299, by rfl⟩ : syracuseStep 781861 = 146599) (by norm_num)
theorem B1044005 : Blo 694316 1044005 := bbase (se 4 (by rfl) ⟨97875, by rfl⟩ : syracuseStep 1044005 = 195751) (by norm_num)
theorem B1044029 : Blo 694316 1044029 := bbase (se 3 (by rfl) ⟨195755, by rfl⟩ : syracuseStep 1044029 = 391511) (by norm_num)
theorem B781897 : Blo 694316 781897 := bbase (se 2 (by rfl) ⟨293211, by rfl⟩ : syracuseStep 781897 = 586423) (by norm_num)
theorem B1044053 : Blo 694316 1044053 := bbase (se 8 (by rfl) ⟨6117, by rfl⟩ : syracuseStep 1044053 = 12235) (by norm_num)
theorem B1764949 : Blo 694316 1764949 := bbase (se 8 (by rfl) ⟨10341, by rfl⟩ : syracuseStep 1764949 = 20683) (by norm_num)
theorem B1175141 : Blo 694316 1175141 := bbase (se 4 (by rfl) ⟨110169, by rfl⟩ : syracuseStep 1175141 = 220339) (by norm_num)
theorem B1568357 : Blo 694316 1568357 := bbase (se 4 (by rfl) ⟨147033, by rfl⟩ : syracuseStep 1568357 = 294067) (by norm_num)
theorem B781933 : Blo 694316 781933 := bbase (se 3 (by rfl) ⟨146612, by rfl⟩ : syracuseStep 781933 = 293225) (by norm_num)
theorem B880237 : Blo 694316 880237 := bbase (se 3 (by rfl) ⟨165044, by rfl⟩ : syracuseStep 880237 = 330089) (by norm_num)
theorem B1044077 : Blo 694316 1044077 := bbase (se 3 (by rfl) ⟨195764, by rfl⟩ : syracuseStep 1044077 = 391529) (by norm_num)
theorem B3174005 : Blo 694316 3174005 := bbase (se 5 (by rfl) ⟨148781, by rfl⟩ : syracuseStep 3174005 = 297563) (by norm_num)
theorem B2977397 : Blo 694316 2977397 := bbase (se 5 (by rfl) ⟨139565, by rfl⟩ : syracuseStep 2977397 = 279131) (by norm_num)
theorem B1044101 : Blo 694316 1044101 := bbase (se 4 (by rfl) ⟨97884, by rfl⟩ : syracuseStep 1044101 = 195769) (by norm_num)
theorem B781969 : Blo 694316 781969 := bbase (se 2 (by rfl) ⟨293238, by rfl⟩ : syracuseStep 781969 = 586477) (by norm_num)
theorem B1044125 : Blo 694316 1044125 := bbase (se 3 (by rfl) ⟨195773, by rfl⟩ : syracuseStep 1044125 = 391547) (by norm_num)
theorem B1568429 : Blo 694316 1568429 := bbase (se 3 (by rfl) ⟨294080, by rfl⟩ : syracuseStep 1568429 = 588161) (by norm_num)
theorem B782005 : Blo 694316 782005 := bbase (se 5 (by rfl) ⟨36656, by rfl⟩ : syracuseStep 782005 = 73313) (by norm_num)
theorem B1044149 : Blo 694316 1044149 := bbase (se 5 (by rfl) ⟨48944, by rfl⟩ : syracuseStep 1044149 = 97889) (by norm_num)
theorem B1765061 : Blo 694316 1765061 := bbase (se 4 (by rfl) ⟨165474, by rfl⟩ : syracuseStep 1765061 = 330949) (by norm_num)
theorem B2354885 : Blo 694316 2354885 := bbase (se 4 (by rfl) ⟨220770, by rfl⟩ : syracuseStep 2354885 = 441541) (by norm_num)
theorem B1044173 : Blo 694316 1044173 := bbase (se 3 (by rfl) ⟨195782, by rfl⟩ : syracuseStep 1044173 = 391565) (by norm_num)
theorem B782041 : Blo 694316 782041 := bbase (se 2 (by rfl) ⟨293265, by rfl⟩ : syracuseStep 782041 = 586531) (by norm_num)
theorem B1044197 : Blo 694316 1044197 := bbase (se 4 (by rfl) ⟨97893, by rfl⟩ : syracuseStep 1044197 = 195787) (by norm_num)
theorem B1175269 : Blo 694316 1175269 := bbase (se 4 (by rfl) ⟨110181, by rfl⟩ : syracuseStep 1175269 = 220363) (by norm_num)
theorem B1568501 : Blo 694316 1568501 := bbase (se 5 (by rfl) ⟨73523, by rfl⟩ : syracuseStep 1568501 = 147047) (by norm_num)
theorem B782077 : Blo 694316 782077 := bbase (se 3 (by rfl) ⟨146639, by rfl⟩ : syracuseStep 782077 = 293279) (by norm_num)
theorem B1044221 : Blo 694316 1044221 := bbase (se 3 (by rfl) ⟨195791, by rfl⟩ : syracuseStep 1044221 = 391583) (by norm_num)
theorem B1044245 : Blo 694316 1044245 := bbase (se 6 (by rfl) ⟨24474, by rfl⟩ : syracuseStep 1044245 = 48949) (by norm_num)
theorem B880409 : Blo 694316 880409 := bbase (se 2 (by rfl) ⟨330153, by rfl⟩ : syracuseStep 880409 = 660307) (by norm_num)
theorem B782113 : Blo 694316 782113 := bbase (se 2 (by rfl) ⟨293292, by rfl⟩ : syracuseStep 782113 = 586585) (by norm_num)
theorem B1044269 : Blo 694316 1044269 := bbase (se 3 (by rfl) ⟨195800, by rfl⟩ : syracuseStep 1044269 = 391601) (by norm_num)
theorem B1175357 : Blo 694316 1175357 := bbase (se 3 (by rfl) ⟨220379, by rfl⟩ : syracuseStep 1175357 = 440759) (by norm_num)
theorem B1568573 : Blo 694316 1568573 := bbase (se 3 (by rfl) ⟨294107, by rfl⟩ : syracuseStep 1568573 = 588215) (by norm_num)
theorem B782149 : Blo 694316 782149 := bbase (se 4 (by rfl) ⟨73326, by rfl⟩ : syracuseStep 782149 = 146653) (by norm_num)
theorem B1044293 : Blo 694316 1044293 := bbase (se 4 (by rfl) ⟨97902, by rfl⟩ : syracuseStep 1044293 = 195805) (by norm_num)
theorem B880465 : Blo 694316 880465 := bbase (se 2 (by rfl) ⟨330174, by rfl⟩ : syracuseStep 880465 = 660349) (by norm_num)
theorem B3534677 : Blo 694316 3534677 := bbase (se 9 (by rfl) ⟨10355, by rfl⟩ : syracuseStep 3534677 = 20711) (by norm_num)
theorem B1044317 : Blo 694316 1044317 := bbase (se 3 (by rfl) ⟨195809, by rfl⟩ : syracuseStep 1044317 = 391619) (by norm_num)
theorem B782185 : Blo 694316 782185 := bbase (se 2 (by rfl) ⟨293319, by rfl⟩ : syracuseStep 782185 = 586639) (by norm_num)
theorem B1044341 : Blo 694316 1044341 := bbase (se 5 (by rfl) ⟨48953, by rfl⟩ : syracuseStep 1044341 = 97907) (by norm_num)
theorem B1568645 : Blo 694316 1568645 := bbase (se 4 (by rfl) ⟨147060, by rfl⟩ : syracuseStep 1568645 = 294121) (by norm_num)
theorem B1765253 : Blo 694316 1765253 := bbase (se 4 (by rfl) ⟨165492, by rfl⟩ : syracuseStep 1765253 = 330985) (by norm_num)
theorem B782221 : Blo 694316 782221 := bbase (se 3 (by rfl) ⟨146666, by rfl⟩ : syracuseStep 782221 = 293333) (by norm_num)
theorem B1044365 : Blo 694316 1044365 := bbase (se 3 (by rfl) ⟨195818, by rfl⟩ : syracuseStep 1044365 = 391637) (by norm_num)
theorem B1044389 : Blo 694316 1044389 := bbase (se 4 (by rfl) ⟨97911, by rfl⟩ : syracuseStep 1044389 = 195823) (by norm_num)
theorem B782257 : Blo 694316 782257 := bbase (se 2 (by rfl) ⟨293346, by rfl⟩ : syracuseStep 782257 = 586693) (by norm_num)
theorem B880561 : Blo 694316 880561 := bbase (se 2 (by rfl) ⟨330210, by rfl⟩ : syracuseStep 880561 = 660421) (by norm_num)
theorem B1044413 : Blo 694316 1044413 := bbase (se 3 (by rfl) ⟨195827, by rfl⟩ : syracuseStep 1044413 = 391655) (by norm_num)
theorem B1175485 : Blo 694316 1175485 := bbase (se 3 (by rfl) ⟨220403, by rfl⟩ : syracuseStep 1175485 = 440807) (by norm_num)
theorem B1568717 : Blo 694316 1568717 := bbase (se 3 (by rfl) ⟨294134, by rfl⟩ : syracuseStep 1568717 = 588269) (by norm_num)
theorem B782293 : Blo 694316 782293 := bbase (se 7 (by rfl) ⟨9167, by rfl⟩ : syracuseStep 782293 = 18335) (by norm_num)
theorem B1044437 : Blo 694316 1044437 := bbase (se 7 (by rfl) ⟨12239, by rfl⟩ : syracuseStep 1044437 = 24479) (by norm_num)
theorem B1044461 : Blo 694316 1044461 := bbase (se 3 (by rfl) ⟨195836, by rfl⟩ : syracuseStep 1044461 = 391673) (by norm_num)
theorem B782329 : Blo 694316 782329 := bbase (se 2 (by rfl) ⟨293373, by rfl⟩ : syracuseStep 782329 = 586747) (by norm_num)
theorem B1044485 : Blo 694316 1044485 := bbase (se 4 (by rfl) ⟨97920, by rfl⟩ : syracuseStep 1044485 = 195841) (by norm_num)
theorem B1175573 : Blo 694316 1175573 := bbase (se 6 (by rfl) ⟨27552, by rfl⟩ : syracuseStep 1175573 = 55105) (by norm_num)
theorem B1568789 : Blo 694316 1568789 := bbase (se 6 (by rfl) ⟨36768, by rfl⟩ : syracuseStep 1568789 = 73537) (by norm_num)
theorem B782365 : Blo 694316 782365 := bbase (se 3 (by rfl) ⟨146693, by rfl⟩ : syracuseStep 782365 = 293387) (by norm_num)
theorem B1044509 : Blo 694316 1044509 := bbase (se 3 (by rfl) ⟨195845, by rfl⟩ : syracuseStep 1044509 = 391691) (by norm_num)
theorem B4223029 : Blo 694316 4223029 := bbase (se 5 (by rfl) ⟨197954, by rfl⟩ : syracuseStep 4223029 = 395909) (by norm_num)
theorem B1044533 : Blo 694316 1044533 := bbase (se 5 (by rfl) ⟨48962, by rfl⟩ : syracuseStep 1044533 = 97925) (by norm_num)
theorem B782401 : Blo 694316 782401 := bbase (se 2 (by rfl) ⟨293400, by rfl⟩ : syracuseStep 782401 = 586801) (by norm_num)
theorem B1044557 : Blo 694316 1044557 := bbase (se 3 (by rfl) ⟨195854, by rfl⟩ : syracuseStep 1044557 = 391709) (by norm_num)
theorem B880733 : Blo 694316 880733 := bbase (se 3 (by rfl) ⟨165137, by rfl⟩ : syracuseStep 880733 = 330275) (by norm_num)
theorem B1568861 : Blo 694316 1568861 := bbase (se 3 (by rfl) ⟨294161, by rfl⟩ : syracuseStep 1568861 = 588323) (by norm_num)
theorem B782437 : Blo 694316 782437 := bbase (se 4 (by rfl) ⟨73353, by rfl⟩ : syracuseStep 782437 = 146707) (by norm_num)
theorem B1044581 : Blo 694316 1044581 := bbase (se 4 (by rfl) ⟨97929, by rfl⟩ : syracuseStep 1044581 = 195859) (by norm_num)
theorem B2355317 : Blo 694316 2355317 := bbase (se 5 (by rfl) ⟨110405, by rfl⟩ : syracuseStep 2355317 = 220811) (by norm_num)
theorem B1044605 : Blo 694316 1044605 := bbase (se 3 (by rfl) ⟨195863, by rfl⟩ : syracuseStep 1044605 = 391727) (by norm_num)
theorem B782473 : Blo 694316 782473 := bbase (se 2 (by rfl) ⟨293427, by rfl⟩ : syracuseStep 782473 = 586855) (by norm_num)
theorem B880789 : Blo 694316 880789 := bbase (se 6 (by rfl) ⟨20643, by rfl⟩ : syracuseStep 880789 = 41287) (by norm_num)
theorem B1044629 : Blo 694316 1044629 := bbase (se 6 (by rfl) ⟨24483, by rfl⟩ : syracuseStep 1044629 = 48967) (by norm_num)
theorem B1175701 : Blo 694316 1175701 := bbase (se 6 (by rfl) ⟨27555, by rfl⟩ : syracuseStep 1175701 = 55111) (by norm_num)
theorem B1568933 : Blo 694316 1568933 := bbase (se 4 (by rfl) ⟨147087, by rfl⟩ : syracuseStep 1568933 = 294175) (by norm_num)
theorem B782509 : Blo 694316 782509 := bbase (se 3 (by rfl) ⟨146720, by rfl⟩ : syracuseStep 782509 = 293441) (by norm_num)
theorem B1044653 : Blo 694316 1044653 := bbase (se 3 (by rfl) ⟨195872, by rfl⟩ : syracuseStep 1044653 = 391745) (by norm_num)
theorem B1044677 : Blo 694316 1044677 := bbase (se 4 (by rfl) ⟨97938, by rfl⟩ : syracuseStep 1044677 = 195877) (by norm_num)
theorem B782545 : Blo 694316 782545 := bbase (se 2 (by rfl) ⟨293454, by rfl⟩ : syracuseStep 782545 = 586909) (by norm_num)
theorem B1044701 : Blo 694316 1044701 := bbase (se 3 (by rfl) ⟨195881, by rfl⟩ : syracuseStep 1044701 = 391763) (by norm_num)
theorem B1765597 : Blo 694316 1765597 := bbase (se 3 (by rfl) ⟨331049, by rfl⟩ : syracuseStep 1765597 = 662099) (by norm_num)
theorem B1503469 : Blo 694316 1503469 := bbase (se 3 (by rfl) ⟨281900, by rfl⟩ : syracuseStep 1503469 = 563801) (by norm_num)
theorem B1175789 : Blo 694316 1175789 := bbase (se 3 (by rfl) ⟨220460, by rfl⟩ : syracuseStep 1175789 = 440921) (by norm_num)
theorem B1569005 : Blo 694316 1569005 := bbase (se 3 (by rfl) ⟨294188, by rfl⟩ : syracuseStep 1569005 = 588377) (by norm_num)
theorem B782581 : Blo 694316 782581 := bbase (se 5 (by rfl) ⟨36683, by rfl⟩ : syracuseStep 782581 = 73367) (by norm_num)
theorem B880885 : Blo 694316 880885 := bbase (se 5 (by rfl) ⟨41291, by rfl⟩ : syracuseStep 880885 = 82583) (by norm_num)
theorem B1044725 : Blo 694316 1044725 := bbase (se 5 (by rfl) ⟨48971, by rfl⟩ : syracuseStep 1044725 = 97943) (by norm_num)
theorem B1044749 : Blo 694316 1044749 := bbase (se 3 (by rfl) ⟨195890, by rfl⟩ : syracuseStep 1044749 = 391781) (by norm_num)
theorem B782617 : Blo 694316 782617 := bbase (se 2 (by rfl) ⟨293481, by rfl⟩ : syracuseStep 782617 = 586963) (by norm_num)
theorem B1044773 : Blo 694316 1044773 := bbase (se 4 (by rfl) ⟨97947, by rfl⟩ : syracuseStep 1044773 = 195895) (by norm_num)
theorem B1569077 : Blo 694316 1569077 := bbase (se 5 (by rfl) ⟨73550, by rfl⟩ : syracuseStep 1569077 = 147101) (by norm_num)
theorem B782653 : Blo 694316 782653 := bbase (se 3 (by rfl) ⟨146747, by rfl⟩ : syracuseStep 782653 = 293495) (by norm_num)
theorem B1044797 : Blo 694316 1044797 := bbase (se 3 (by rfl) ⟨195899, by rfl⟩ : syracuseStep 1044797 = 391799) (by norm_num)
theorem B1765709 : Blo 694316 1765709 := bbase (se 3 (by rfl) ⟨331070, by rfl⟩ : syracuseStep 1765709 = 662141) (by norm_num)
theorem B1044821 : Blo 694316 1044821 := bbase (se 10 (by rfl) ⟨1530, by rfl⟩ : syracuseStep 1044821 = 3061) (by norm_num)
theorem B48329045 : Blo 694316 48329045 := bbase (se 10 (by rfl) ⟨70794, by rfl⟩ : syracuseStep 48329045 = 141589) (by norm_num)
theorem B782689 : Blo 694316 782689 := bbase (se 2 (by rfl) ⟨293508, by rfl⟩ : syracuseStep 782689 = 587017) (by norm_num)
theorem B1044845 : Blo 694316 1044845 := bbase (se 3 (by rfl) ⟨195908, by rfl⟩ : syracuseStep 1044845 = 391817) (by norm_num)
theorem B1175917 : Blo 694316 1175917 := bbase (se 3 (by rfl) ⟨220484, by rfl⟩ : syracuseStep 1175917 = 440969) (by norm_num)
theorem B1569149 : Blo 694316 1569149 := bbase (se 3 (by rfl) ⟨294215, by rfl⟩ : syracuseStep 1569149 = 588431) (by norm_num)
theorem B782725 : Blo 694316 782725 := bbase (se 4 (by rfl) ⟨73380, by rfl⟩ : syracuseStep 782725 = 146761) (by norm_num)
theorem B1044869 : Blo 694316 1044869 := bbase (se 4 (by rfl) ⟨97956, by rfl⟩ : syracuseStep 1044869 = 195913) (by norm_num)
theorem B717193 : Blo 694316 717193 := bbase (se 2 (by rfl) ⟨268947, by rfl⟩ : syracuseStep 717193 = 537895) (by norm_num)
theorem B1044893 : Blo 694316 1044893 := bbase (se 3 (by rfl) ⟨195917, by rfl⟩ : syracuseStep 1044893 = 391835) (by norm_num)
theorem B881057 : Blo 694316 881057 := bbase (se 2 (by rfl) ⟨330396, by rfl⟩ : syracuseStep 881057 = 660793) (by norm_num)
theorem B782761 : Blo 694316 782761 := bbase (se 2 (by rfl) ⟨293535, by rfl⟩ : syracuseStep 782761 = 587071) (by norm_num)
theorem B1044917 : Blo 694316 1044917 := bbase (se 5 (by rfl) ⟨48980, by rfl⟩ : syracuseStep 1044917 = 97961) (by norm_num)
theorem B1176005 : Blo 694316 1176005 := bbase (se 4 (by rfl) ⟨110250, by rfl⟩ : syracuseStep 1176005 = 220501) (by norm_num)
theorem B1569221 : Blo 694316 1569221 := bbase (se 4 (by rfl) ⟨147114, by rfl⟩ : syracuseStep 1569221 = 294229) (by norm_num)
theorem B782797 : Blo 694316 782797 := bbase (se 3 (by rfl) ⟨146774, by rfl⟩ : syracuseStep 782797 = 293549) (by norm_num)
theorem B1044941 : Blo 694316 1044941 := bbase (se 3 (by rfl) ⟨195926, by rfl⟩ : syracuseStep 1044941 = 391853) (by norm_num)
theorem B881113 : Blo 694316 881113 := bbase (se 2 (by rfl) ⟨330417, by rfl⟩ : syracuseStep 881113 = 660835) (by norm_num)
theorem B1044965 : Blo 694316 1044965 := bbase (se 4 (by rfl) ⟨97965, by rfl⟩ : syracuseStep 1044965 = 195931) (by norm_num)
theorem B782833 : Blo 694316 782833 := bbase (se 2 (by rfl) ⟨293562, by rfl⟩ : syracuseStep 782833 = 587125) (by norm_num)
theorem B1044989 : Blo 694316 1044989 := bbase (se 3 (by rfl) ⟨195935, by rfl⟩ : syracuseStep 1044989 = 391871) (by norm_num)
theorem B1569293 : Blo 694316 1569293 := bbase (se 3 (by rfl) ⟨294242, by rfl⟩ : syracuseStep 1569293 = 588485) (by norm_num)
theorem B1765901 : Blo 694316 1765901 := bbase (se 3 (by rfl) ⟨331106, by rfl⟩ : syracuseStep 1765901 = 662213) (by norm_num)
theorem B782869 : Blo 694316 782869 := bbase (se 6 (by rfl) ⟨18348, by rfl⟩ : syracuseStep 782869 = 36697) (by norm_num)
theorem B1045013 : Blo 694316 1045013 := bbase (se 6 (by rfl) ⟨24492, by rfl⟩ : syracuseStep 1045013 = 48985) (by norm_num)
theorem B2355749 : Blo 694316 2355749 := bbase (se 4 (by rfl) ⟨220851, by rfl⟩ : syracuseStep 2355749 = 441703) (by norm_num)
theorem B1045037 : Blo 694316 1045037 := bbase (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) (by norm_num)
theorem B782905 : Blo 694316 782905 := bbase (se 2 (by rfl) ⟨293589, by rfl⟩ : syracuseStep 782905 = 587179) (by norm_num)
theorem B881209 : Blo 694316 881209 := bbase (se 2 (by rfl) ⟨330453, by rfl⟩ : syracuseStep 881209 = 660907) (by norm_num)
theorem B1045061 : Blo 694316 1045061 := bbase (se 4 (by rfl) ⟨97974, by rfl⟩ : syracuseStep 1045061 = 195949) (by norm_num)
theorem B1176133 : Blo 694316 1176133 := bbase (se 4 (by rfl) ⟨110262, by rfl⟩ : syracuseStep 1176133 = 220525) (by norm_num)
theorem B1569365 : Blo 694316 1569365 := bbase (se 8 (by rfl) ⟨9195, by rfl⟩ : syracuseStep 1569365 = 18391) (by norm_num)
theorem B782941 : Blo 694316 782941 := bbase (se 3 (by rfl) ⟨146801, by rfl⟩ : syracuseStep 782941 = 293603) (by norm_num)
theorem B1045085 : Blo 694316 1045085 := bbase (se 3 (by rfl) ⟨195953, by rfl⟩ : syracuseStep 1045085 = 391907) (by norm_num)
theorem B1045109 : Blo 694316 1045109 := bbase (se 5 (by rfl) ⟨48989, by rfl⟩ : syracuseStep 1045109 = 97979) (by norm_num)
theorem B782977 : Blo 694316 782977 := bbase (se 2 (by rfl) ⟨293616, by rfl⟩ : syracuseStep 782977 = 587233) (by norm_num)
theorem B1045133 : Blo 694316 1045133 := bbase (se 3 (by rfl) ⟨195962, by rfl⟩ : syracuseStep 1045133 = 391925) (by norm_num)
theorem B1176221 : Blo 694316 1176221 := bbase (se 3 (by rfl) ⟨220541, by rfl⟩ : syracuseStep 1176221 = 441083) (by norm_num)
theorem B1569437 : Blo 694316 1569437 := bbase (se 3 (by rfl) ⟨294269, by rfl⟩ : syracuseStep 1569437 = 588539) (by norm_num)
theorem B783013 : Blo 694316 783013 := bbase (se 4 (by rfl) ⟨73407, by rfl⟩ : syracuseStep 783013 = 146815) (by norm_num)
theorem B1045157 : Blo 694316 1045157 := bbase (se 4 (by rfl) ⟨97983, by rfl⟩ : syracuseStep 1045157 = 195967) (by norm_num)
theorem B1045181 : Blo 694316 1045181 := bbase (se 3 (by rfl) ⟨195971, by rfl⟩ : syracuseStep 1045181 = 391943) (by norm_num)
theorem B783049 : Blo 694316 783049 := bbase (se 2 (by rfl) ⟨293643, by rfl⟩ : syracuseStep 783049 = 587287) (by norm_num)
theorem B1045205 : Blo 694316 1045205 := bbase (se 7 (by rfl) ⟨12248, by rfl⟩ : syracuseStep 1045205 = 24497) (by norm_num)
theorem B881381 : Blo 694316 881381 := bbase (se 4 (by rfl) ⟨82629, by rfl⟩ : syracuseStep 881381 = 165259) (by norm_num)
theorem B1569509 : Blo 694316 1569509 := bbase (se 4 (by rfl) ⟨147141, by rfl⟩ : syracuseStep 1569509 = 294283) (by norm_num)
theorem B783085 : Blo 694316 783085 := bbase (se 3 (by rfl) ⟨146828, by rfl⟩ : syracuseStep 783085 = 293657) (by norm_num)
theorem B1045229 : Blo 694316 1045229 := bbase (se 3 (by rfl) ⟨195980, by rfl⟩ : syracuseStep 1045229 = 391961) (by norm_num)
theorem B3764981 : Blo 694316 3764981 := bbase (se 5 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 3764981 = 352967) (by norm_num)
theorem B1045253 : Blo 694316 1045253 := bbase (se 4 (by rfl) ⟨97992, by rfl⟩ : syracuseStep 1045253 = 195985) (by norm_num)
theorem B783121 : Blo 694316 783121 := bbase (se 2 (by rfl) ⟨293670, by rfl⟩ : syracuseStep 783121 = 587341) (by norm_num)
theorem B881437 : Blo 694316 881437 := bbase (se 3 (by rfl) ⟨165269, by rfl⟩ : syracuseStep 881437 = 330539) (by norm_num)
theorem B1045277 : Blo 694316 1045277 := bbase (se 3 (by rfl) ⟨195989, by rfl⟩ : syracuseStep 1045277 = 391979) (by norm_num)
theorem B1176349 : Blo 694316 1176349 := bbase (se 3 (by rfl) ⟨220565, by rfl⟩ : syracuseStep 1176349 = 441131) (by norm_num)
theorem B1569581 : Blo 694316 1569581 := bbase (se 3 (by rfl) ⟨294296, by rfl⟩ : syracuseStep 1569581 = 588593) (by norm_num)
theorem B783157 : Blo 694316 783157 := bbase (se 5 (by rfl) ⟨36710, by rfl⟩ : syracuseStep 783157 = 73421) (by norm_num)
theorem B1045301 : Blo 694316 1045301 := bbase (se 5 (by rfl) ⟨48998, by rfl⟩ : syracuseStep 1045301 = 97997) (by norm_num)
theorem B1045325 : Blo 694316 1045325 := bbase (se 3 (by rfl) ⟨195998, by rfl⟩ : syracuseStep 1045325 = 391997) (by norm_num)
theorem B783193 : Blo 694316 783193 := bbase (se 2 (by rfl) ⟨293697, by rfl⟩ : syracuseStep 783193 = 587395) (by norm_num)
theorem B1045349 : Blo 694316 1045349 := bbase (se 4 (by rfl) ⟨98001, by rfl⟩ : syracuseStep 1045349 = 196003) (by norm_num)
theorem B1766245 : Blo 694316 1766245 := bbase (se 4 (by rfl) ⟨165585, by rfl⟩ : syracuseStep 1766245 = 331171) (by norm_num)
theorem B1176437 : Blo 694316 1176437 := bbase (se 5 (by rfl) ⟨55145, by rfl⟩ : syracuseStep 1176437 = 110291) (by norm_num)
theorem B1569653 : Blo 694316 1569653 := bbase (se 5 (by rfl) ⟨73577, by rfl⟩ : syracuseStep 1569653 = 147155) (by norm_num)
theorem B783229 : Blo 694316 783229 := bbase (se 3 (by rfl) ⟨146855, by rfl⟩ : syracuseStep 783229 = 293711) (by norm_num)
theorem B881533 : Blo 694316 881533 := bbase (se 3 (by rfl) ⟨165287, by rfl⟩ : syracuseStep 881533 = 330575) (by norm_num)
theorem B1045373 : Blo 694316 1045373 := bbase (se 3 (by rfl) ⟨196007, by rfl⟩ : syracuseStep 1045373 = 392015) (by norm_num)
theorem B1045397 : Blo 694316 1045397 := bbase (se 6 (by rfl) ⟨24501, by rfl⟩ : syracuseStep 1045397 = 49003) (by norm_num)
theorem B783265 : Blo 694316 783265 := bbase (se 2 (by rfl) ⟨293724, by rfl⟩ : syracuseStep 783265 = 587449) (by norm_num)
theorem B1045421 : Blo 694316 1045421 := bbase (se 3 (by rfl) ⟨196016, by rfl⟩ : syracuseStep 1045421 = 392033) (by norm_num)
theorem B1569725 : Blo 694316 1569725 := bbase (se 3 (by rfl) ⟨294323, by rfl⟩ : syracuseStep 1569725 = 588647) (by norm_num)
theorem B783301 : Blo 694316 783301 := bbase (se 4 (by rfl) ⟨73434, by rfl⟩ : syracuseStep 783301 = 146869) (by norm_num)
theorem B1045445 : Blo 694316 1045445 := bbase (se 4 (by rfl) ⟨98010, by rfl⟩ : syracuseStep 1045445 = 196021) (by norm_num)
theorem B1766357 : Blo 694316 1766357 := bbase (se 7 (by rfl) ⟨20699, by rfl⟩ : syracuseStep 1766357 = 41399) (by norm_num)
theorem B2356181 : Blo 694316 2356181 := bbase (se 7 (by rfl) ⟨27611, by rfl⟩ : syracuseStep 2356181 = 55223) (by norm_num)
theorem B1045469 : Blo 694316 1045469 := bbase (se 3 (by rfl) ⟨196025, by rfl⟩ : syracuseStep 1045469 = 392051) (by norm_num)
theorem B783337 : Blo 694316 783337 := bbase (se 2 (by rfl) ⟨293751, by rfl⟩ : syracuseStep 783337 = 587503) (by norm_num)
theorem B1045493 : Blo 694316 1045493 := bbase (se 5 (by rfl) ⟨49007, by rfl⟩ : syracuseStep 1045493 = 98015) (by norm_num)
theorem B1176565 : Blo 694316 1176565 := bbase (se 5 (by rfl) ⟨55151, by rfl⟩ : syracuseStep 1176565 = 110303) (by norm_num)
theorem B3339269 : Blo 694316 3339269 := bbase (se 4 (by rfl) ⟨313056, by rfl⟩ : syracuseStep 3339269 = 626113) (by norm_num)
theorem B1569797 : Blo 694316 1569797 := bbase (se 4 (by rfl) ⟨147168, by rfl⟩ : syracuseStep 1569797 = 294337) (by norm_num)
theorem B783373 : Blo 694316 783373 := bbase (se 3 (by rfl) ⟨146882, by rfl⟩ : syracuseStep 783373 = 293765) (by norm_num)
theorem B1045517 : Blo 694316 1045517 := bbase (se 3 (by rfl) ⟨196034, by rfl⟩ : syracuseStep 1045517 = 392069) (by norm_num)
theorem B1045541 : Blo 694316 1045541 := bbase (se 4 (by rfl) ⟨98019, by rfl⟩ : syracuseStep 1045541 = 196039) (by norm_num)
theorem B881705 : Blo 694316 881705 := bbase (se 2 (by rfl) ⟨330639, by rfl⟩ : syracuseStep 881705 = 661279) (by norm_num)
theorem B783409 : Blo 694316 783409 := bbase (se 2 (by rfl) ⟨293778, by rfl⟩ : syracuseStep 783409 = 587557) (by norm_num)
theorem B1045565 : Blo 694316 1045565 := bbase (se 3 (by rfl) ⟨196043, by rfl⟩ : syracuseStep 1045565 = 392087) (by norm_num)
theorem B1176653 : Blo 694316 1176653 := bbase (se 3 (by rfl) ⟨220622, by rfl⟩ : syracuseStep 1176653 = 441245) (by norm_num)
theorem B1569869 : Blo 694316 1569869 := bbase (se 3 (by rfl) ⟨294350, by rfl⟩ : syracuseStep 1569869 = 588701) (by norm_num)
theorem B783445 : Blo 694316 783445 := bbase (se 8 (by rfl) ⟨4590, by rfl⟩ : syracuseStep 783445 = 9181) (by norm_num)
theorem B1045589 : Blo 694316 1045589 := bbase (se 8 (by rfl) ⟨6126, by rfl⟩ : syracuseStep 1045589 = 12253) (by norm_num)
theorem B881761 : Blo 694316 881761 := bbase (se 2 (by rfl) ⟨330660, by rfl⟩ : syracuseStep 881761 = 661321) (by norm_num)
theorem B2651237 : Blo 694316 2651237 := bbase (se 4 (by rfl) ⟨248553, by rfl⟩ : syracuseStep 2651237 = 497107) (by norm_num)
theorem B1045613 : Blo 694316 1045613 := bbase (se 3 (by rfl) ⟨196052, by rfl⟩ : syracuseStep 1045613 = 392105) (by norm_num)
theorem B783481 : Blo 694316 783481 := bbase (se 2 (by rfl) ⟨293805, by rfl⟩ : syracuseStep 783481 = 587611) (by norm_num)
theorem B1045637 : Blo 694316 1045637 := bbase (se 4 (by rfl) ⟨98028, by rfl⟩ : syracuseStep 1045637 = 196057) (by norm_num)
theorem B1569941 : Blo 694316 1569941 := bbase (se 6 (by rfl) ⟨36795, by rfl⟩ : syracuseStep 1569941 = 73591) (by norm_num)
theorem B1766549 : Blo 694316 1766549 := bbase (se 6 (by rfl) ⟨41403, by rfl⟩ : syracuseStep 1766549 = 82807) (by norm_num)
theorem B783517 : Blo 694316 783517 := bbase (se 3 (by rfl) ⟨146909, by rfl⟩ : syracuseStep 783517 = 293819) (by norm_num)
theorem B1045661 : Blo 694316 1045661 := bbase (se 3 (by rfl) ⟨196061, by rfl⟩ : syracuseStep 1045661 = 392123) (by norm_num)
theorem B2225333 : Blo 694316 2225333 := bbase (se 5 (by rfl) ⟨104312, by rfl⟩ : syracuseStep 2225333 = 208625) (by norm_num)
theorem B1045685 : Blo 694316 1045685 := bbase (se 5 (by rfl) ⟨49016, by rfl⟩ : syracuseStep 1045685 = 98033) (by norm_num)
theorem B783553 : Blo 694316 783553 := bbase (se 2 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 783553 = 587665) (by norm_num)
theorem B881857 : Blo 694316 881857 := bbase (se 2 (by rfl) ⟨330696, by rfl⟩ : syracuseStep 881857 = 661393) (by norm_num)
theorem B1045709 : Blo 694316 1045709 := bbase (se 3 (by rfl) ⟨196070, by rfl⟩ : syracuseStep 1045709 = 392141) (by norm_num)
theorem B1176781 : Blo 694316 1176781 := bbase (se 3 (by rfl) ⟨220646, by rfl⟩ : syracuseStep 1176781 = 441293) (by norm_num)
theorem B1570013 : Blo 694316 1570013 := bbase (se 3 (by rfl) ⟨294377, by rfl⟩ : syracuseStep 1570013 = 588755) (by norm_num)
theorem B783589 : Blo 694316 783589 := bbase (se 4 (by rfl) ⟨73461, by rfl⟩ : syracuseStep 783589 = 146923) (by norm_num)
theorem B1045733 : Blo 694316 1045733 := bbase (se 4 (by rfl) ⟨98037, by rfl⟩ : syracuseStep 1045733 = 196075) (by norm_num)
theorem B1045757 : Blo 694316 1045757 := bbase (se 3 (by rfl) ⟨196079, by rfl⟩ : syracuseStep 1045757 = 392159) (by norm_num)
theorem B783625 : Blo 694316 783625 := bbase (se 2 (by rfl) ⟨293859, by rfl⟩ : syracuseStep 783625 = 587719) (by norm_num)
theorem B1045781 : Blo 694316 1045781 := bbase (se 6 (by rfl) ⟨24510, by rfl⟩ : syracuseStep 1045781 = 49021) (by norm_num)
theorem B1176869 : Blo 694316 1176869 := bbase (se 4 (by rfl) ⟨110331, by rfl⟩ : syracuseStep 1176869 = 220663) (by norm_num)
theorem B1570085 : Blo 694316 1570085 := bbase (se 4 (by rfl) ⟨147195, by rfl⟩ : syracuseStep 1570085 = 294391) (by norm_num)
theorem B783661 : Blo 694316 783661 := bbase (se 3 (by rfl) ⟨146936, by rfl⟩ : syracuseStep 783661 = 293873) (by norm_num)
theorem B1045805 : Blo 694316 1045805 := bbase (se 3 (by rfl) ⟨196088, by rfl⟩ : syracuseStep 1045805 = 392177) (by norm_num)
theorem B1045829 : Blo 694316 1045829 := bbase (se 4 (by rfl) ⟨98046, by rfl⟩ : syracuseStep 1045829 = 196093) (by norm_num)
theorem B783697 : Blo 694316 783697 := bbase (se 2 (by rfl) ⟨293886, by rfl⟩ : syracuseStep 783697 = 587773) (by norm_num)
theorem B1045853 : Blo 694316 1045853 := bbase (se 3 (by rfl) ⟨196097, by rfl⟩ : syracuseStep 1045853 = 392195) (by norm_num)
theorem B2979173 : Blo 694316 2979173 := bbase (se 4 (by rfl) ⟨279297, by rfl⟩ : syracuseStep 2979173 = 558595) (by norm_num)
theorem B882029 : Blo 694316 882029 := bbase (se 3 (by rfl) ⟨165380, by rfl⟩ : syracuseStep 882029 = 330761) (by norm_num)
theorem B1570157 : Blo 694316 1570157 := bbase (se 3 (by rfl) ⟨294404, by rfl⟩ : syracuseStep 1570157 = 588809) (by norm_num)
theorem B783733 : Blo 694316 783733 := bbase (se 5 (by rfl) ⟨36737, by rfl⟩ : syracuseStep 783733 = 73475) (by norm_num)
theorem B1045877 : Blo 694316 1045877 := bbase (se 5 (by rfl) ⟨49025, by rfl⟩ : syracuseStep 1045877 = 98051) (by norm_num)
theorem B2356613 : Blo 694316 2356613 := bbase (se 4 (by rfl) ⟨220932, by rfl⟩ : syracuseStep 2356613 = 441865) (by norm_num)
theorem B1045901 : Blo 694316 1045901 := bbase (se 3 (by rfl) ⟨196106, by rfl⟩ : syracuseStep 1045901 = 392213) (by norm_num)
theorem B783769 : Blo 694316 783769 := bbase (se 2 (by rfl) ⟨293913, by rfl⟩ : syracuseStep 783769 = 587827) (by norm_num)
theorem B882085 : Blo 694316 882085 := bbase (se 4 (by rfl) ⟨82695, by rfl⟩ : syracuseStep 882085 = 165391) (by norm_num)
theorem B1045925 : Blo 694316 1045925 := bbase (se 4 (by rfl) ⟨98055, by rfl⟩ : syracuseStep 1045925 = 196111) (by norm_num)
theorem B1176997 : Blo 694316 1176997 := bbase (se 4 (by rfl) ⟨110343, by rfl⟩ : syracuseStep 1176997 = 220687) (by norm_num)
theorem B1570229 : Blo 694316 1570229 := bbase (se 5 (by rfl) ⟨73604, by rfl⟩ : syracuseStep 1570229 = 147209) (by norm_num)
theorem B783805 : Blo 694316 783805 := bbase (se 3 (by rfl) ⟨146963, by rfl⟩ : syracuseStep 783805 = 293927) (by norm_num)
theorem B1045949 : Blo 694316 1045949 := bbase (se 3 (by rfl) ⟨196115, by rfl⟩ : syracuseStep 1045949 = 392231) (by norm_num)
theorem B1045973 : Blo 694316 1045973 := bbase (se 7 (by rfl) ⟨12257, by rfl⟩ : syracuseStep 1045973 = 24515) (by norm_num)
theorem B783841 : Blo 694316 783841 := bbase (se 2 (by rfl) ⟨293940, by rfl⟩ : syracuseStep 783841 = 587881) (by norm_num)
theorem B1045997 : Blo 694316 1045997 := bbase (se 3 (by rfl) ⟨196124, by rfl⟩ : syracuseStep 1045997 = 392249) (by norm_num)
theorem B1766893 : Blo 694316 1766893 := bbase (se 3 (by rfl) ⟨331292, by rfl⟩ : syracuseStep 1766893 = 662585) (by norm_num)
theorem B1177085 : Blo 694316 1177085 := bbase (se 3 (by rfl) ⟨220703, by rfl⟩ : syracuseStep 1177085 = 441407) (by norm_num)
theorem B1570301 : Blo 694316 1570301 := bbase (se 3 (by rfl) ⟨294431, by rfl⟩ : syracuseStep 1570301 = 588863) (by norm_num)
theorem B783877 : Blo 694316 783877 := bbase (se 4 (by rfl) ⟨73488, by rfl⟩ : syracuseStep 783877 = 146977) (by norm_num)
theorem B882181 : Blo 694316 882181 := bbase (se 4 (by rfl) ⟨82704, by rfl⟩ : syracuseStep 882181 = 165409) (by norm_num)
theorem B1046021 : Blo 694316 1046021 := bbase (se 4 (by rfl) ⟨98064, by rfl⟩ : syracuseStep 1046021 = 196129) (by norm_num)
theorem B1046045 : Blo 694316 1046045 := bbase (se 3 (by rfl) ⟨196133, by rfl⟩ : syracuseStep 1046045 = 392267) (by norm_num)
theorem B783913 : Blo 694316 783913 := bbase (se 2 (by rfl) ⟨293967, by rfl⟩ : syracuseStep 783913 = 587935) (by norm_num)
theorem B1046069 : Blo 694316 1046069 := bbase (se 5 (by rfl) ⟨49034, by rfl⟩ : syracuseStep 1046069 = 98069) (by norm_num)
theorem B1570373 : Blo 694316 1570373 := bbase (se 4 (by rfl) ⟨147222, by rfl⟩ : syracuseStep 1570373 = 294445) (by norm_num)
theorem B783949 : Blo 694316 783949 := bbase (se 3 (by rfl) ⟨146990, by rfl⟩ : syracuseStep 783949 = 293981) (by norm_num)
theorem B1046093 : Blo 694316 1046093 := bbase (se 3 (by rfl) ⟨196142, by rfl⟩ : syracuseStep 1046093 = 392285) (by norm_num)
theorem B2979413 : Blo 694316 2979413 := bbase (se 8 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 2979413 = 34915) (by norm_num)
theorem B1767005 : Blo 694316 1767005 := bbase (se 3 (by rfl) ⟨331313, by rfl⟩ : syracuseStep 1767005 = 662627) (by norm_num)
theorem B1046117 : Blo 694316 1046117 := bbase (se 4 (by rfl) ⟨98073, by rfl⟩ : syracuseStep 1046117 = 196147) (by norm_num)
theorem B783985 : Blo 694316 783985 := bbase (se 2 (by rfl) ⟨293994, by rfl⟩ : syracuseStep 783985 = 587989) (by norm_num)
theorem B1046141 : Blo 694316 1046141 := bbase (se 3 (by rfl) ⟨196151, by rfl⟩ : syracuseStep 1046141 = 392303) (by norm_num)
theorem B1177213 : Blo 694316 1177213 := bbase (se 3 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 1177213 = 441455) (by norm_num)
theorem B1570445 : Blo 694316 1570445 := bbase (se 3 (by rfl) ⟨294458, by rfl⟩ : syracuseStep 1570445 = 588917) (by norm_num)
theorem B784021 : Blo 694316 784021 := bbase (se 6 (by rfl) ⟨18375, by rfl⟩ : syracuseStep 784021 = 36751) (by norm_num)
theorem B1046165 : Blo 694316 1046165 := bbase (se 6 (by rfl) ⟨24519, by rfl⟩ : syracuseStep 1046165 = 49039) (by norm_num)
theorem B1046189 : Blo 694316 1046189 := bbase (se 3 (by rfl) ⟨196160, by rfl⟩ : syracuseStep 1046189 = 392321) (by norm_num)
theorem B882353 : Blo 694316 882353 := bbase (se 2 (by rfl) ⟨330882, by rfl⟩ : syracuseStep 882353 = 661765) (by norm_num)
theorem B5732021 : Blo 694316 5732021 := bbase (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) (by norm_num)
theorem B784057 : Blo 694316 784057 := bbase (se 2 (by rfl) ⟨294021, by rfl⟩ : syracuseStep 784057 = 588043) (by norm_num)
theorem B1046213 : Blo 694316 1046213 := bbase (se 4 (by rfl) ⟨98082, by rfl⟩ : syracuseStep 1046213 = 196165) (by norm_num)
theorem B1177301 : Blo 694316 1177301 := bbase (se 7 (by rfl) ⟨13796, by rfl⟩ : syracuseStep 1177301 = 27593) (by norm_num)
theorem B1570517 : Blo 694316 1570517 := bbase (se 7 (by rfl) ⟨18404, by rfl⟩ : syracuseStep 1570517 = 36809) (by norm_num)
theorem B784093 : Blo 694316 784093 := bbase (se 3 (by rfl) ⟨147017, by rfl⟩ : syracuseStep 784093 = 294035) (by norm_num)
theorem B1046237 : Blo 694316 1046237 := bbase (se 3 (by rfl) ⟨196169, by rfl⟩ : syracuseStep 1046237 = 392339) (by norm_num)
theorem B882409 : Blo 694316 882409 := bbase (se 2 (by rfl) ⟨330903, by rfl⟩ : syracuseStep 882409 = 661807) (by norm_num)
theorem B1046261 : Blo 694316 1046261 := bbase (se 5 (by rfl) ⟨49043, by rfl⟩ : syracuseStep 1046261 = 98087) (by norm_num)
theorem B784129 : Blo 694316 784129 := bbase (se 2 (by rfl) ⟨294048, by rfl⟩ : syracuseStep 784129 = 588097) (by norm_num)
theorem B1046285 : Blo 694316 1046285 := bbase (se 3 (by rfl) ⟨196178, by rfl⟩ : syracuseStep 1046285 = 392357) (by norm_num)
theorem B1570589 : Blo 694316 1570589 := bbase (se 3 (by rfl) ⟨294485, by rfl⟩ : syracuseStep 1570589 = 588971) (by norm_num)
theorem B1767197 : Blo 694316 1767197 := bbase (se 3 (by rfl) ⟨331349, by rfl⟩ : syracuseStep 1767197 = 662699) (by norm_num)
theorem B784165 : Blo 694316 784165 := bbase (se 4 (by rfl) ⟨73515, by rfl⟩ : syracuseStep 784165 = 147031) (by norm_num)
theorem B1046309 : Blo 694316 1046309 := bbase (se 4 (by rfl) ⟨98091, by rfl⟩ : syracuseStep 1046309 = 196183) (by norm_num)
theorem B1046333 : Blo 694316 1046333 := bbase (se 3 (by rfl) ⟨196187, by rfl⟩ : syracuseStep 1046333 = 392375) (by norm_num)
theorem B784201 : Blo 694316 784201 := bbase (se 2 (by rfl) ⟨294075, by rfl⟩ : syracuseStep 784201 = 588151) (by norm_num)
theorem B882505 : Blo 694316 882505 := bbase (se 2 (by rfl) ⟨330939, by rfl⟩ : syracuseStep 882505 = 661879) (by norm_num)
theorem B1046357 : Blo 694316 1046357 := bbase (se 9 (by rfl) ⟨3065, by rfl⟩ : syracuseStep 1046357 = 6131) (by norm_num)
theorem B1177429 : Blo 694316 1177429 := bbase (se 9 (by rfl) ⟨3449, by rfl⟩ : syracuseStep 1177429 = 6899) (by norm_num)
theorem B1570661 : Blo 694316 1570661 := bbase (se 4 (by rfl) ⟨147249, by rfl⟩ : syracuseStep 1570661 = 294499) (by norm_num)
theorem B784237 : Blo 694316 784237 := bbase (se 3 (by rfl) ⟨147044, by rfl⟩ : syracuseStep 784237 = 294089) (by norm_num)
theorem B1046381 : Blo 694316 1046381 := bbase (se 3 (by rfl) ⟨196196, by rfl⟩ : syracuseStep 1046381 = 392393) (by norm_num)
theorem B849773 : Blo 694316 849773 := bbase (se 3 (by rfl) ⟨159332, by rfl⟩ : syracuseStep 849773 = 318665) (by norm_num)
theorem B1046405 : Blo 694316 1046405 := bbase (se 4 (by rfl) ⟨98100, by rfl⟩ : syracuseStep 1046405 = 196201) (by norm_num)
theorem B784273 : Blo 694316 784273 := bbase (se 2 (by rfl) ⟨294102, by rfl⟩ : syracuseStep 784273 = 588205) (by norm_num)
theorem B1046429 : Blo 694316 1046429 := bbase (se 3 (by rfl) ⟨196205, by rfl⟩ : syracuseStep 1046429 = 392411) (by norm_num)
theorem B1177517 : Blo 694316 1177517 := bbase (se 3 (by rfl) ⟨220784, by rfl⟩ : syracuseStep 1177517 = 441569) (by norm_num)
theorem B1570733 : Blo 694316 1570733 := bbase (se 3 (by rfl) ⟨294512, by rfl⟩ : syracuseStep 1570733 = 589025) (by norm_num)
theorem B784309 : Blo 694316 784309 := bbase (se 5 (by rfl) ⟨36764, by rfl⟩ : syracuseStep 784309 = 73529) (by norm_num)
theorem B1046453 : Blo 694316 1046453 := bbase (se 5 (by rfl) ⟨49052, by rfl⟩ : syracuseStep 1046453 = 98105) (by norm_num)
theorem B1341389 : Blo 694316 1341389 := bbase (se 3 (by rfl) ⟨251510, by rfl⟩ : syracuseStep 1341389 = 503021) (by norm_num)
theorem B1046477 : Blo 694316 1046477 := bbase (se 3 (by rfl) ⟨196214, by rfl⟩ : syracuseStep 1046477 = 392429) (by norm_num)
theorem B784345 : Blo 694316 784345 := bbase (se 2 (by rfl) ⟨294129, by rfl⟩ : syracuseStep 784345 = 588259) (by norm_num)
theorem B1046501 : Blo 694316 1046501 := bbase (se 4 (by rfl) ⟨98109, by rfl⟩ : syracuseStep 1046501 = 196219) (by norm_num)
theorem B882677 : Blo 694316 882677 := bbase (se 5 (by rfl) ⟨41375, by rfl⟩ : syracuseStep 882677 = 82751) (by norm_num)
theorem B1570805 : Blo 694316 1570805 := bbase (se 5 (by rfl) ⟨73631, by rfl⟩ : syracuseStep 1570805 = 147263) (by norm_num)
theorem B784381 : Blo 694316 784381 := bbase (se 3 (by rfl) ⟨147071, by rfl⟩ : syracuseStep 784381 = 294143) (by norm_num)
theorem B1046525 : Blo 694316 1046525 := bbase (se 3 (by rfl) ⟨196223, by rfl⟩ : syracuseStep 1046525 = 392447) (by norm_num)
theorem B1046549 : Blo 694316 1046549 := bbase (se 6 (by rfl) ⟨24528, by rfl⟩ : syracuseStep 1046549 = 49057) (by norm_num)
theorem B784417 : Blo 694316 784417 := bbase (se 2 (by rfl) ⟨294156, by rfl⟩ : syracuseStep 784417 = 588313) (by norm_num)
theorem B882733 : Blo 694316 882733 := bbase (se 3 (by rfl) ⟨165512, by rfl⟩ : syracuseStep 882733 = 331025) (by norm_num)
theorem B1046573 : Blo 694316 1046573 := bbase (se 3 (by rfl) ⟨196232, by rfl⟩ : syracuseStep 1046573 = 392465) (by norm_num)
theorem B1177645 : Blo 694316 1177645 := bbase (se 3 (by rfl) ⟨220808, by rfl⟩ : syracuseStep 1177645 = 441617) (by norm_num)
theorem B1570877 : Blo 694316 1570877 := bbase (se 3 (by rfl) ⟨294539, by rfl⟩ : syracuseStep 1570877 = 589079) (by norm_num)
theorem B784453 : Blo 694316 784453 := bbase (se 4 (by rfl) ⟨73542, by rfl⟩ : syracuseStep 784453 = 147085) (by norm_num)
theorem B1046597 : Blo 694316 1046597 := bbase (se 4 (by rfl) ⟨98118, by rfl⟩ : syracuseStep 1046597 = 196237) (by norm_num)
theorem B1046621 : Blo 694316 1046621 := bbase (se 3 (by rfl) ⟨196241, by rfl⟩ : syracuseStep 1046621 = 392483) (by norm_num)
theorem B784489 : Blo 694316 784489 := bbase (se 2 (by rfl) ⟨294183, by rfl⟩ : syracuseStep 784489 = 588367) (by norm_num)
theorem B1046645 : Blo 694316 1046645 := bbase (se 5 (by rfl) ⟨49061, by rfl⟩ : syracuseStep 1046645 = 98123) (by norm_num)
theorem B1767541 : Blo 694316 1767541 := bbase (se 5 (by rfl) ⟨82853, by rfl⟩ : syracuseStep 1767541 = 165707) (by norm_num)
theorem B1177733 : Blo 694316 1177733 := bbase (se 4 (by rfl) ⟨110412, by rfl⟩ : syracuseStep 1177733 = 220825) (by norm_num)
theorem B1570949 : Blo 694316 1570949 := bbase (se 4 (by rfl) ⟨147276, by rfl⟩ : syracuseStep 1570949 = 294553) (by norm_num)
theorem B784525 : Blo 694316 784525 := bbase (se 3 (by rfl) ⟨147098, by rfl⟩ : syracuseStep 784525 = 294197) (by norm_num)
theorem B882829 : Blo 694316 882829 := bbase (se 3 (by rfl) ⟨165530, by rfl⟩ : syracuseStep 882829 = 331061) (by norm_num)
theorem B1046669 : Blo 694316 1046669 := bbase (se 3 (by rfl) ⟨196250, by rfl⟩ : syracuseStep 1046669 = 392501) (by norm_num)
theorem B1046693 : Blo 694316 1046693 := bbase (se 4 (by rfl) ⟨98127, by rfl⟩ : syracuseStep 1046693 = 196255) (by norm_num)
theorem B784561 : Blo 694316 784561 := bbase (se 2 (by rfl) ⟨294210, by rfl⟩ : syracuseStep 784561 = 588421) (by norm_num)
theorem B1046717 : Blo 694316 1046717 := bbase (se 3 (by rfl) ⟨196259, by rfl⟩ : syracuseStep 1046717 = 392519) (by norm_num)
theorem B1571021 : Blo 694316 1571021 := bbase (se 3 (by rfl) ⟨294566, by rfl⟩ : syracuseStep 1571021 = 589133) (by norm_num)
theorem B784597 : Blo 694316 784597 := bbase (se 7 (by rfl) ⟨9194, by rfl⟩ : syracuseStep 784597 = 18389) (by norm_num)
theorem B1046741 : Blo 694316 1046741 := bbase (se 7 (by rfl) ⟨12266, by rfl⟩ : syracuseStep 1046741 = 24533) (by norm_num)
theorem B1046765 : Blo 694316 1046765 := bbase (se 3 (by rfl) ⟨196268, by rfl⟩ : syracuseStep 1046765 = 392537) (by norm_num)
theorem B784633 : Blo 694316 784633 := bbase (se 2 (by rfl) ⟨294237, by rfl⟩ : syracuseStep 784633 = 588475) (by norm_num)
theorem B1046789 : Blo 694316 1046789 := bbase (se 4 (by rfl) ⟨98136, by rfl⟩ : syracuseStep 1046789 = 196273) (by norm_num)
theorem B1177861 : Blo 694316 1177861 := bbase (se 4 (by rfl) ⟨110424, by rfl⟩ : syracuseStep 1177861 = 220849) (by norm_num)
theorem B1571093 : Blo 694316 1571093 := bbase (se 6 (by rfl) ⟨36822, by rfl⟩ : syracuseStep 1571093 = 73645) (by norm_num)
theorem B784669 : Blo 694316 784669 := bbase (se 3 (by rfl) ⟨147125, by rfl⟩ : syracuseStep 784669 = 294251) (by norm_num)
theorem B1046813 : Blo 694316 1046813 := bbase (se 3 (by rfl) ⟨196277, by rfl⟩ : syracuseStep 1046813 = 392555) (by norm_num)
theorem B1046837 : Blo 694316 1046837 := bbase (se 5 (by rfl) ⟨49070, by rfl⟩ : syracuseStep 1046837 = 98141) (by norm_num)
theorem B883001 : Blo 694316 883001 := bbase (se 2 (by rfl) ⟨331125, by rfl⟩ : syracuseStep 883001 = 662251) (by norm_num)
theorem B784705 : Blo 694316 784705 := bbase (se 2 (by rfl) ⟨294264, by rfl⟩ : syracuseStep 784705 = 588529) (by norm_num)
theorem B1046861 : Blo 694316 1046861 := bbase (se 3 (by rfl) ⟨196286, by rfl⟩ : syracuseStep 1046861 = 392573) (by norm_num)
theorem B1177949 : Blo 694316 1177949 := bbase (se 3 (by rfl) ⟨220865, by rfl⟩ : syracuseStep 1177949 = 441731) (by norm_num)
theorem B1571165 : Blo 694316 1571165 := bbase (se 3 (by rfl) ⟨294593, by rfl⟩ : syracuseStep 1571165 = 589187) (by norm_num)
theorem B784741 : Blo 694316 784741 := bbase (se 4 (by rfl) ⟨73569, by rfl⟩ : syracuseStep 784741 = 147139) (by norm_num)
theorem B1046885 : Blo 694316 1046885 := bbase (se 4 (by rfl) ⟨98145, by rfl⟩ : syracuseStep 1046885 = 196291) (by norm_num)
theorem B883057 : Blo 694316 883057 := bbase (se 2 (by rfl) ⟨331146, by rfl⟩ : syracuseStep 883057 = 662293) (by norm_num)
theorem B1046909 : Blo 694316 1046909 := bbase (se 3 (by rfl) ⟨196295, by rfl⟩ : syracuseStep 1046909 = 392591) (by norm_num)
theorem B784777 : Blo 694316 784777 := bbase (se 2 (by rfl) ⟨294291, by rfl⟩ : syracuseStep 784777 = 588583) (by norm_num)
theorem B1046933 : Blo 694316 1046933 := bbase (se 6 (by rfl) ⟨24537, by rfl⟩ : syracuseStep 1046933 = 49075) (by norm_num)
theorem B784813 : Blo 694316 784813 := bbase (se 3 (by rfl) ⟨147152, by rfl⟩ : syracuseStep 784813 = 294305) (by norm_num)
theorem B1046957 : Blo 694316 1046957 := bbase (se 3 (by rfl) ⟨196304, by rfl⟩ : syracuseStep 1046957 = 392609) (by norm_num)
theorem B6355381 : Blo 694316 6355381 := bbase (se 5 (by rfl) ⟨297908, by rfl⟩ : syracuseStep 6355381 = 595817) (by norm_num)
theorem B2226629 : Blo 694316 2226629 := bbase (se 4 (by rfl) ⟨208746, by rfl⟩ : syracuseStep 2226629 = 417493) (by norm_num)
theorem B1046981 : Blo 694316 1046981 := bbase (se 4 (by rfl) ⟨98154, by rfl⟩ : syracuseStep 1046981 = 196309) (by norm_num)
theorem B784849 : Blo 694316 784849 := bbase (se 2 (by rfl) ⟨294318, by rfl⟩ : syracuseStep 784849 = 588637) (by norm_num)
theorem B883153 : Blo 694316 883153 := bbase (se 2 (by rfl) ⟨331182, by rfl⟩ : syracuseStep 883153 = 662365) (by norm_num)
theorem B1047005 : Blo 694316 1047005 := bbase (se 3 (by rfl) ⟨196313, by rfl⟩ : syracuseStep 1047005 = 392627) (by norm_num)
theorem B1178077 : Blo 694316 1178077 := bbase (se 3 (by rfl) ⟨220889, by rfl⟩ : syracuseStep 1178077 = 441779) (by norm_num)
theorem B784885 : Blo 694316 784885 := bbase (se 5 (by rfl) ⟨36791, by rfl⟩ : syracuseStep 784885 = 73583) (by norm_num)
theorem B1047029 : Blo 694316 1047029 := bbase (se 5 (by rfl) ⟨49079, by rfl⟩ : syracuseStep 1047029 = 98159) (by norm_num)
theorem B1047053 : Blo 694316 1047053 := bbase (se 3 (by rfl) ⟨196322, by rfl⟩ : syracuseStep 1047053 = 392645) (by norm_num)
theorem B784921 : Blo 694316 784921 := bbase (se 2 (by rfl) ⟨294345, by rfl⟩ : syracuseStep 784921 = 588691) (by norm_num)
theorem B1047077 : Blo 694316 1047077 := bbase (se 4 (by rfl) ⟨98163, by rfl⟩ : syracuseStep 1047077 = 196327) (by norm_num)
theorem B1178165 : Blo 694316 1178165 := bbase (se 5 (by rfl) ⟨55226, by rfl⟩ : syracuseStep 1178165 = 110453) (by norm_num)
theorem B784957 : Blo 694316 784957 := bbase (se 3 (by rfl) ⟨147179, by rfl⟩ : syracuseStep 784957 = 294359) (by norm_num)
theorem B1047101 : Blo 694316 1047101 := bbase (se 3 (by rfl) ⟨196331, by rfl⟩ : syracuseStep 1047101 = 392663) (by norm_num)
theorem B1047125 : Blo 694316 1047125 := bbase (se 8 (by rfl) ⟨6135, by rfl⟩ : syracuseStep 1047125 = 12271) (by norm_num)
theorem B784993 : Blo 694316 784993 := bbase (se 2 (by rfl) ⟨294372, by rfl⟩ : syracuseStep 784993 = 588745) (by norm_num)
theorem B1047149 : Blo 694316 1047149 := bbase (se 3 (by rfl) ⟨196340, by rfl⟩ : syracuseStep 1047149 = 392681) (by norm_num)
theorem B883325 : Blo 694316 883325 := bbase (se 3 (by rfl) ⟨165623, by rfl⟩ : syracuseStep 883325 = 331247) (by norm_num)
theorem B785029 : Blo 694316 785029 := bbase (se 4 (by rfl) ⟨73596, by rfl⟩ : syracuseStep 785029 = 147193) (by norm_num)
theorem B1047173 : Blo 694316 1047173 := bbase (se 4 (by rfl) ⟨98172, by rfl⟩ : syracuseStep 1047173 = 196345) (by norm_num)
theorem B1047197 : Blo 694316 1047197 := bbase (se 3 (by rfl) ⟨196349, by rfl⟩ : syracuseStep 1047197 = 392699) (by norm_num)
theorem B785065 : Blo 694316 785065 := bbase (se 2 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 785065 = 588799) (by norm_num)
theorem B883381 : Blo 694316 883381 := bbase (se 5 (by rfl) ⟨41408, by rfl⟩ : syracuseStep 883381 = 82817) (by norm_num)
theorem B1047221 : Blo 694316 1047221 := bbase (se 5 (by rfl) ⟨49088, by rfl⟩ : syracuseStep 1047221 = 98177) (by norm_num)
theorem B1178293 : Blo 694316 1178293 := bbase (se 5 (by rfl) ⟨55232, by rfl⟩ : syracuseStep 1178293 = 110465) (by norm_num)
theorem B785101 : Blo 694316 785101 := bbase (se 3 (by rfl) ⟨147206, by rfl⟩ : syracuseStep 785101 = 294413) (by norm_num)
theorem B1047245 : Blo 694316 1047245 := bbase (se 3 (by rfl) ⟨196358, by rfl⟩ : syracuseStep 1047245 = 392717) (by norm_num)
theorem B1407701 : Blo 694316 1407701 := bbase (se 7 (by rfl) ⟨16496, by rfl⟩ : syracuseStep 1407701 = 32993) (by norm_num)
theorem B4455125 : Blo 694316 4455125 := bbase (se 7 (by rfl) ⟨52208, by rfl⟩ : syracuseStep 4455125 = 104417) (by norm_num)
theorem B1047269 : Blo 694316 1047269 := bbase (se 4 (by rfl) ⟨98181, by rfl⟩ : syracuseStep 1047269 = 196363) (by norm_num)
theorem B785137 : Blo 694316 785137 := bbase (se 2 (by rfl) ⟨294426, by rfl⟩ : syracuseStep 785137 = 588853) (by norm_num)
theorem B6683381 : Blo 694316 6683381 := bbase (se 5 (by rfl) ⟨313283, by rfl⟩ : syracuseStep 6683381 = 626567) (by norm_num)
theorem B1047293 : Blo 694316 1047293 := bbase (se 3 (by rfl) ⟨196367, by rfl⟩ : syracuseStep 1047293 = 392735) (by norm_num)
theorem B1178381 : Blo 694316 1178381 := bbase (se 3 (by rfl) ⟨220946, by rfl⟩ : syracuseStep 1178381 = 441893) (by norm_num)
theorem B785173 : Blo 694316 785173 := bbase (se 6 (by rfl) ⟨18402, by rfl⟩ : syracuseStep 785173 = 36805) (by norm_num)
theorem B883477 : Blo 694316 883477 := bbase (se 6 (by rfl) ⟨20706, by rfl⟩ : syracuseStep 883477 = 41413) (by norm_num)
theorem B1047317 : Blo 694316 1047317 := bbase (se 6 (by rfl) ⟨24546, by rfl⟩ : syracuseStep 1047317 = 49093) (by norm_num)
theorem B1047341 : Blo 694316 1047341 := bbase (se 3 (by rfl) ⟨196376, by rfl⟩ : syracuseStep 1047341 = 392753) (by norm_num)
theorem B785209 : Blo 694316 785209 := bbase (se 2 (by rfl) ⟨294453, by rfl⟩ : syracuseStep 785209 = 588907) (by norm_num)
theorem B1047365 : Blo 694316 1047365 := bbase (se 4 (by rfl) ⟨98190, by rfl⟩ : syracuseStep 1047365 = 196381) (by norm_num)
theorem B4225877 : Blo 694316 4225877 := bbase (se 9 (by rfl) ⟨12380, by rfl⟩ : syracuseStep 4225877 = 24761) (by norm_num)
theorem B785245 : Blo 694316 785245 := bbase (se 3 (by rfl) ⟨147233, by rfl⟩ : syracuseStep 785245 = 294467) (by norm_num)
theorem B1047389 : Blo 694316 1047389 := bbase (se 3 (by rfl) ⟨196385, by rfl⟩ : syracuseStep 1047389 = 392771) (by norm_num)
theorem B1047413 : Blo 694316 1047413 := bbase (se 5 (by rfl) ⟨49097, by rfl⟩ : syracuseStep 1047413 = 98195) (by norm_num)
theorem B785281 : Blo 694316 785281 := bbase (se 2 (by rfl) ⟨294480, by rfl⟩ : syracuseStep 785281 = 588961) (by norm_num)
theorem B1047437 : Blo 694316 1047437 := bbase (se 3 (by rfl) ⟨196394, by rfl⟩ : syracuseStep 1047437 = 392789) (by norm_num)
theorem B1506205 : Blo 694316 1506205 := bbase (se 3 (by rfl) ⟨282413, by rfl⟩ : syracuseStep 1506205 = 564827) (by norm_num)
theorem B785317 : Blo 694316 785317 := bbase (se 4 (by rfl) ⟨73623, by rfl⟩ : syracuseStep 785317 = 147247) (by norm_num)
theorem B1047461 : Blo 694316 1047461 := bbase (se 4 (by rfl) ⟨98199, by rfl⟩ : syracuseStep 1047461 = 196399) (by norm_num)
theorem B883649 : Blo 694316 883649 := bbase (se 2 (by rfl) ⟨331368, by rfl⟩ : syracuseStep 883649 = 662737) (by norm_num)
theorem B785353 : Blo 694316 785353 := bbase (se 2 (by rfl) ⟨294507, by rfl⟩ : syracuseStep 785353 = 589015) (by norm_num)
theorem B785389 : Blo 694316 785389 := bbase (se 3 (by rfl) ⟨147260, by rfl⟩ : syracuseStep 785389 = 294521) (by norm_num)
theorem B1113077 : Blo 694316 1113077 := bbase (se 5 (by rfl) ⟨52175, by rfl⟩ : syracuseStep 1113077 = 104351) (by norm_num)
theorem B883705 : Blo 694316 883705 := bbase (se 2 (by rfl) ⟨331389, by rfl⟩ : syracuseStep 883705 = 662779) (by norm_num)
theorem B785425 : Blo 694316 785425 := bbase (se 2 (by rfl) ⟨294534, by rfl⟩ : syracuseStep 785425 = 589069) (by norm_num)
theorem B785461 : Blo 694316 785461 := bbase (se 5 (by rfl) ⟨36818, by rfl⟩ : syracuseStep 785461 = 73637) (by norm_num)
theorem B785497 : Blo 694316 785497 := bbase (se 2 (by rfl) ⟨294561, by rfl⟩ : syracuseStep 785497 = 589123) (by norm_num)
theorem B883801 : Blo 694316 883801 := bbase (se 2 (by rfl) ⟨331425, by rfl⟩ : syracuseStep 883801 = 662851) (by norm_num)
theorem B785533 : Blo 694316 785533 := bbase (se 3 (by rfl) ⟨147287, by rfl⟩ : syracuseStep 785533 = 294575) (by norm_num)
theorem B785569 : Blo 694316 785569 := bbase (se 2 (by rfl) ⟨294588, by rfl⟩ : syracuseStep 785569 = 589177) (by norm_num)
theorem B785605 : Blo 694316 785605 := bbase (se 4 (by rfl) ⟨73650, by rfl⟩ : syracuseStep 785605 = 147301) (by norm_num)
theorem B1670557 : Blo 694316 1670557 := bbase (se 3 (by rfl) ⟨313229, by rfl⟩ : syracuseStep 1670557 = 626459) (by norm_num)
theorem B1113725 : Blo 694316 1113725 := bbase (se 3 (by rfl) ⟨208823, by rfl⟩ : syracuseStep 1113725 = 417647) (by norm_num)
theorem B2981701 : Blo 694316 2981701 := bbase (se 4 (by rfl) ⟨279534, by rfl⟩ : syracuseStep 2981701 = 559069) (by norm_num)
theorem B1343405 : Blo 694316 1343405 := bbase (se 3 (by rfl) ⟨251888, by rfl⟩ : syracuseStep 1343405 = 503777) (by norm_num)
theorem B2228269 : Blo 694316 2228269 := bstep (se 3 (by rfl) ⟨417800, by rfl⟩ : syracuseStep 2228269 = 835601) B835601
theorem B28508213 : Blo 694316 28508213 := bstep (se 5 (by rfl) ⟨1336322, by rfl⟩ : syracuseStep 28508213 = 2672645) B2672645
theorem B7536881 : Blo 694316 7536881 := bstep (se 2 (by rfl) ⟨2826330, by rfl⟩ : syracuseStep 7536881 = 5652661) B5652661
theorem B1114499 : Blo 694316 1114499 := bstep (se 1 (by rfl) ⟨835874, by rfl⟩ : syracuseStep 1114499 = 1671749) B1671749
theorem B1671587 : Blo 694316 1671587 := bstep (se 1 (by rfl) ⟨1253690, by rfl⟩ : syracuseStep 1671587 = 2507381) B2507381
theorem B1507889 : Blo 694316 1507889 := bstep (se 2 (by rfl) ⟨565458, by rfl⟩ : syracuseStep 1507889 = 1130917) B1130917
theorem B3212131 : Blo 694316 3212131 := bstep (se 1 (by rfl) ⟨2409098, by rfl⟩ : syracuseStep 3212131 = 4818197) B4818197
theorem B4457585 : Blo 694316 4457585 := bstep (se 2 (by rfl) ⟨1671594, by rfl⟩ : syracuseStep 4457585 = 3343189) B3343189
theorem B1115345 : Blo 694316 1115345 := bstep (se 2 (by rfl) ⟨418254, by rfl⟩ : syracuseStep 1115345 = 836509) B836509
theorem B1672433 : Blo 694316 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B1115473 : Blo 694316 1115473 := bstep (se 2 (by rfl) ⟨418302, by rfl⟩ : syracuseStep 1115473 = 836605) B836605
theorem B1115537 : Blo 694316 1115537 := bstep (se 2 (by rfl) ⟨418326, by rfl⟩ : syracuseStep 1115537 = 836653) B836653
theorem B2229869 : Blo 694316 2229869 := bstep (se 3 (by rfl) ⟨418100, by rfl⟩ : syracuseStep 2229869 = 836201) B836201
theorem B5441165 : Blo 694316 5441165 := bstep (se 3 (by rfl) ⟨1020218, by rfl⟩ : syracuseStep 5441165 = 2040437) B2040437
theorem B3966853 : Blo 694316 3966853 := bstep (se 4 (by rfl) ⟨371892, by rfl⟩ : syracuseStep 3966853 = 743785) B743785
theorem B952225 : Blo 694316 952225 := bstep (se 2 (by rfl) ⟨357084, by rfl⟩ : syracuseStep 952225 = 714169) B714169
theorem B1411025 : Blo 694316 1411025 := bstep (se 2 (by rfl) ⟨529134, by rfl⟩ : syracuseStep 1411025 = 1058269) B1058269
theorem B4458509 : Blo 694316 4458509 := bstep (se 3 (by rfl) ⟨835970, by rfl⟩ : syracuseStep 4458509 = 1671941) B1671941
theorem B3344419 : Blo 694316 3344419 := bstep (se 1 (by rfl) ⟨2508314, by rfl⟩ : syracuseStep 3344419 = 5016629) B5016629
theorem B3213539 : Blo 694316 3213539 := bstep (se 1 (by rfl) ⟨2410154, by rfl⟩ : syracuseStep 3213539 = 4820309) B4820309
theorem B2820365 : Blo 694316 2820365 := bstep (se 3 (by rfl) ⟨528818, by rfl⟩ : syracuseStep 2820365 = 1057637) B1057637
theorem B1116595 : Blo 694316 1116595 := bstep (se 1 (by rfl) ⟨837446, by rfl⟩ : syracuseStep 1116595 = 1674893) B1674893
theorem B2755313 : Blo 694316 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B5934221 : Blo 694316 5934221 := bstep (se 3 (by rfl) ⟨1112666, by rfl⟩ : syracuseStep 5934221 = 2225333) B2225333
theorem B2231459 : Blo 694316 2231459 := bstep (se 1 (by rfl) ⟨1673594, by rfl⟩ : syracuseStep 2231459 = 3347189) B3347189
theorem B1117523 : Blo 694316 1117523 := bstep (se 1 (by rfl) ⟨838142, by rfl⟩ : syracuseStep 1117523 = 1676285) B1676285
theorem B2231651 : Blo 694316 2231651 := bstep (se 1 (by rfl) ⟨1673738, by rfl⟩ : syracuseStep 2231651 = 3347477) B3347477
theorem B1117793 : Blo 694316 1117793 := bstep (se 2 (by rfl) ⟨419172, by rfl⟩ : syracuseStep 1117793 = 838345) B838345
theorem B1675075 : Blo 694316 1675075 := bstep (se 1 (by rfl) ⟨1256306, by rfl⟩ : syracuseStep 1675075 = 2512613) B2512613
theorem B3968837 : Blo 694316 3968837 := bstep (se 4 (by rfl) ⟨372078, by rfl⟩ : syracuseStep 3968837 = 744157) B744157
theorem B1118081 : Blo 694316 1118081 := bstep (se 2 (by rfl) ⟨419280, by rfl⟩ : syracuseStep 1118081 = 838561) B838561
theorem B6033379 : Blo 694316 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B2232305 : Blo 694316 2232305 := bstep (se 2 (by rfl) ⟨837114, by rfl⟩ : syracuseStep 2232305 = 1674229) B1674229
theorem B5640205 : Blo 694316 5640205 := bstep (se 3 (by rfl) ⟨1057538, by rfl⟩ : syracuseStep 5640205 = 2115077) B2115077
theorem B3575843 : Blo 694316 3575843 := bstep (se 1 (by rfl) ⟨2681882, by rfl⟩ : syracuseStep 3575843 = 5363765) B5363765
theorem B1118497 : Blo 694316 1118497 := bstep (se 2 (by rfl) ⟨419436, by rfl⟩ : syracuseStep 1118497 = 838873) B838873
theorem B7934435 : Blo 694316 7934435 := bstep (se 1 (by rfl) ⟨5950826, by rfl⟩ : syracuseStep 7934435 = 11901653) B11901653
theorem B15078257 : Blo 694316 15078257 := bstep (se 2 (by rfl) ⟨5654346, by rfl⟩ : syracuseStep 15078257 = 11308693) B11308693
theorem B2266061 : Blo 694316 2266061 := bstep (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) B849773
theorem B1676305 : Blo 694316 1676305 := bstep (se 2 (by rfl) ⟨628614, by rfl⟩ : syracuseStep 1676305 = 1257229) B1257229
theorem B9147491 : Blo 694316 9147491 := bstep (se 1 (by rfl) ⟨6860618, by rfl⟩ : syracuseStep 9147491 = 13721237) B13721237
theorem B988627 : Blo 694316 988627 := bstep (se 1 (by rfl) ⟨741470, by rfl⟩ : syracuseStep 988627 = 1482941) B1482941
theorem B5936611 : Blo 694316 5936611 := bstep (se 1 (by rfl) ⟨4452458, by rfl⟩ : syracuseStep 5936611 = 8904917) B8904917
theorem B2004625 : Blo 694316 2004625 := bstep (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) B1503469
theorem B956257 : Blo 694316 956257 := bstep (se 2 (by rfl) ⟨358596, by rfl⟩ : syracuseStep 956257 = 717193) B717193
theorem B1251217 : Blo 694316 1251217 := bstep (se 2 (by rfl) ⟨469206, by rfl⟩ : syracuseStep 1251217 = 938413) B938413
theorem B2234317 : Blo 694316 2234317 := bstep (se 3 (by rfl) ⟨418934, by rfl⟩ : syracuseStep 2234317 = 837869) B837869
theorem B989185 : Blo 694316 989185 := bstep (se 2 (by rfl) ⟨370944, by rfl⟩ : syracuseStep 989185 = 741889) B741889
theorem B989219 : Blo 694316 989219 := bstep (se 1 (by rfl) ⟨741914, by rfl⟩ : syracuseStep 989219 = 1483829) B1483829
theorem B694323 : Blo 694316 694323 := bstep (se 1 (by rfl) ⟨520742, by rfl⟩ : syracuseStep 694323 = 1041485) B1041485
theorem B694339 : Blo 694316 694339 := bstep (se 1 (by rfl) ⟨520754, by rfl⟩ : syracuseStep 694339 = 1041509) B1041509
theorem B694355 : Blo 694316 694355 := bstep (se 1 (by rfl) ⟨520766, by rfl⟩ : syracuseStep 694355 = 1041533) B1041533
theorem B694371 : Blo 694316 694371 := bstep (se 1 (by rfl) ⟨520778, by rfl⟩ : syracuseStep 694371 = 1041557) B1041557
theorem B694387 : Blo 694316 694387 := bstep (se 1 (by rfl) ⟨520790, by rfl⟩ : syracuseStep 694387 = 1041581) B1041581
theorem B694403 : Blo 694316 694403 := bstep (se 1 (by rfl) ⟨520802, by rfl⟩ : syracuseStep 694403 = 1041605) B1041605
theorem B694419 : Blo 694316 694419 := bstep (se 1 (by rfl) ⟨520814, by rfl⟩ : syracuseStep 694419 = 1041629) B1041629
theorem B694435 : Blo 694316 694435 := bstep (se 1 (by rfl) ⟨520826, by rfl⟩ : syracuseStep 694435 = 1041653) B1041653
theorem B694451 : Blo 694316 694451 := bstep (se 1 (by rfl) ⟨520838, by rfl⟩ : syracuseStep 694451 = 1041677) B1041677
theorem B694467 : Blo 694316 694467 := bstep (se 1 (by rfl) ⟨520850, by rfl⟩ : syracuseStep 694467 = 1041701) B1041701
theorem B694483 : Blo 694316 694483 := bstep (se 1 (by rfl) ⟨520862, by rfl⟩ : syracuseStep 694483 = 1041725) B1041725
theorem B694499 : Blo 694316 694499 := bstep (se 1 (by rfl) ⟨520874, by rfl⟩ : syracuseStep 694499 = 1041749) B1041749
theorem B694515 : Blo 694316 694515 := bstep (se 1 (by rfl) ⟨520886, by rfl⟩ : syracuseStep 694515 = 1041773) B1041773
theorem B694531 : Blo 694316 694531 := bstep (se 1 (by rfl) ⟨520898, by rfl⟩ : syracuseStep 694531 = 1041797) B1041797
theorem B694547 : Blo 694316 694547 := bstep (se 1 (by rfl) ⟨520910, by rfl⟩ : syracuseStep 694547 = 1041821) B1041821
theorem B694563 : Blo 694316 694563 := bstep (se 1 (by rfl) ⟨520922, by rfl⟩ : syracuseStep 694563 = 1041845) B1041845
theorem B3774755 : Blo 694316 3774755 := bstep (se 1 (by rfl) ⟨2831066, by rfl⟩ : syracuseStep 3774755 = 5662133) B5662133
theorem B1906993 : Blo 694316 1906993 := bstep (se 2 (by rfl) ⟨715122, by rfl⟩ : syracuseStep 1906993 = 1430245) B1430245
theorem B694579 : Blo 694316 694579 := bstep (se 1 (by rfl) ⟨520934, by rfl⟩ : syracuseStep 694579 = 1041869) B1041869
theorem B694595 : Blo 694316 694595 := bstep (se 1 (by rfl) ⟨520946, by rfl⟩ : syracuseStep 694595 = 1041893) B1041893
theorem B694611 : Blo 694316 694611 := bstep (se 1 (by rfl) ⟨520958, by rfl⟩ : syracuseStep 694611 = 1041917) B1041917
theorem B694627 : Blo 694316 694627 := bstep (se 1 (by rfl) ⟨520970, by rfl⟩ : syracuseStep 694627 = 1041941) B1041941
theorem B694643 : Blo 694316 694643 := bstep (se 1 (by rfl) ⟨520982, by rfl⟩ : syracuseStep 694643 = 1041965) B1041965
theorem B694659 : Blo 694316 694659 := bstep (se 1 (by rfl) ⟨520994, by rfl⟩ : syracuseStep 694659 = 1041989) B1041989
theorem B2234765 : Blo 694316 2234765 := bstep (se 3 (by rfl) ⟨419018, by rfl⟩ : syracuseStep 2234765 = 838037) B838037
theorem B694675 : Blo 694316 694675 := bstep (se 1 (by rfl) ⟨521006, by rfl⟩ : syracuseStep 694675 = 1042013) B1042013
theorem B694691 : Blo 694316 694691 := bstep (se 1 (by rfl) ⟨521018, by rfl⟩ : syracuseStep 694691 = 1042037) B1042037
theorem B694707 : Blo 694316 694707 := bstep (se 1 (by rfl) ⟨521030, by rfl⟩ : syracuseStep 694707 = 1042061) B1042061
theorem B694723 : Blo 694316 694723 := bstep (se 1 (by rfl) ⟨521042, by rfl⟩ : syracuseStep 694723 = 1042085) B1042085
theorem B694739 : Blo 694316 694739 := bstep (se 1 (by rfl) ⟨521054, by rfl⟩ : syracuseStep 694739 = 1042109) B1042109
theorem B694755 : Blo 694316 694755 := bstep (se 1 (by rfl) ⟨521066, by rfl⟩ : syracuseStep 694755 = 1042133) B1042133
theorem B13408739 : Blo 694316 13408739 := bstep (se 1 (by rfl) ⟨10056554, by rfl⟩ : syracuseStep 13408739 = 20113109) B20113109
theorem B694771 : Blo 694316 694771 := bstep (se 1 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 694771 = 1042157) B1042157
theorem B694787 : Blo 694316 694787 := bstep (se 1 (by rfl) ⟨521090, by rfl⟩ : syracuseStep 694787 = 1042181) B1042181
theorem B694803 : Blo 694316 694803 := bstep (se 1 (by rfl) ⟨521102, by rfl⟩ : syracuseStep 694803 = 1042205) B1042205
theorem B694819 : Blo 694316 694819 := bstep (se 1 (by rfl) ⟨521114, by rfl⟩ : syracuseStep 694819 = 1042229) B1042229
theorem B694835 : Blo 694316 694835 := bstep (se 1 (by rfl) ⟨521126, by rfl⟩ : syracuseStep 694835 = 1042253) B1042253
theorem B694851 : Blo 694316 694851 := bstep (se 1 (by rfl) ⟨521138, by rfl⟩ : syracuseStep 694851 = 1042277) B1042277
theorem B989777 : Blo 694316 989777 := bstep (se 2 (by rfl) ⟨371166, by rfl⟩ : syracuseStep 989777 = 742333) B742333
theorem B694867 : Blo 694316 694867 := bstep (se 1 (by rfl) ⟨521150, by rfl⟩ : syracuseStep 694867 = 1042301) B1042301
theorem B694883 : Blo 694316 694883 := bstep (se 1 (by rfl) ⟨521162, by rfl⟩ : syracuseStep 694883 = 1042325) B1042325
theorem B694899 : Blo 694316 694899 := bstep (se 1 (by rfl) ⟨521174, by rfl⟩ : syracuseStep 694899 = 1042349) B1042349
theorem B694915 : Blo 694316 694915 := bstep (se 1 (by rfl) ⟨521186, by rfl⟩ : syracuseStep 694915 = 1042373) B1042373
theorem B694931 : Blo 694316 694931 := bstep (se 1 (by rfl) ⟨521198, by rfl⟩ : syracuseStep 694931 = 1042397) B1042397
theorem B989857 : Blo 694316 989857 := bstep (se 2 (by rfl) ⟨371196, by rfl⟩ : syracuseStep 989857 = 742393) B742393
theorem B694947 : Blo 694316 694947 := bstep (se 1 (by rfl) ⟨521210, by rfl⟩ : syracuseStep 694947 = 1042421) B1042421
theorem B694963 : Blo 694316 694963 := bstep (se 1 (by rfl) ⟨521222, by rfl⟩ : syracuseStep 694963 = 1042445) B1042445
theorem B694979 : Blo 694316 694979 := bstep (se 1 (by rfl) ⟨521234, by rfl⟩ : syracuseStep 694979 = 1042469) B1042469
theorem B694995 : Blo 694316 694995 := bstep (se 1 (by rfl) ⟨521246, by rfl⟩ : syracuseStep 694995 = 1042493) B1042493
theorem B695011 : Blo 694316 695011 := bstep (se 1 (by rfl) ⟨521258, by rfl⟩ : syracuseStep 695011 = 1042517) B1042517
theorem B695027 : Blo 694316 695027 := bstep (se 1 (by rfl) ⟨521270, by rfl⟩ : syracuseStep 695027 = 1042541) B1042541
theorem B695043 : Blo 694316 695043 := bstep (se 1 (by rfl) ⟨521282, by rfl⟩ : syracuseStep 695043 = 1042565) B1042565
theorem B695059 : Blo 694316 695059 := bstep (se 1 (by rfl) ⟨521294, by rfl⟩ : syracuseStep 695059 = 1042589) B1042589
theorem B695075 : Blo 694316 695075 := bstep (se 1 (by rfl) ⟨521306, by rfl⟩ : syracuseStep 695075 = 1042613) B1042613
theorem B695091 : Blo 694316 695091 := bstep (se 1 (by rfl) ⟨521318, by rfl⟩ : syracuseStep 695091 = 1042637) B1042637
theorem B695107 : Blo 694316 695107 := bstep (se 1 (by rfl) ⟨521330, by rfl⟩ : syracuseStep 695107 = 1042661) B1042661
theorem B695123 : Blo 694316 695123 := bstep (se 1 (by rfl) ⟨521342, by rfl⟩ : syracuseStep 695123 = 1042685) B1042685
theorem B695139 : Blo 694316 695139 := bstep (se 1 (by rfl) ⟨521354, by rfl⟩ : syracuseStep 695139 = 1042709) B1042709
theorem B695155 : Blo 694316 695155 := bstep (se 1 (by rfl) ⟨521366, by rfl⟩ : syracuseStep 695155 = 1042733) B1042733
theorem B695171 : Blo 694316 695171 := bstep (se 1 (by rfl) ⟨521378, by rfl⟩ : syracuseStep 695171 = 1042757) B1042757
theorem B695187 : Blo 694316 695187 := bstep (se 1 (by rfl) ⟨521390, by rfl⟩ : syracuseStep 695187 = 1042781) B1042781
theorem B695203 : Blo 694316 695203 := bstep (se 1 (by rfl) ⟨521402, by rfl⟩ : syracuseStep 695203 = 1042805) B1042805
theorem B695219 : Blo 694316 695219 := bstep (se 1 (by rfl) ⟨521414, by rfl⟩ : syracuseStep 695219 = 1042829) B1042829
theorem B695235 : Blo 694316 695235 := bstep (se 1 (by rfl) ⟨521426, by rfl⟩ : syracuseStep 695235 = 1042853) B1042853
theorem B695251 : Blo 694316 695251 := bstep (se 1 (by rfl) ⟨521438, by rfl⟩ : syracuseStep 695251 = 1042877) B1042877
theorem B695267 : Blo 694316 695267 := bstep (se 1 (by rfl) ⟨521450, by rfl⟩ : syracuseStep 695267 = 1042901) B1042901
theorem B695283 : Blo 694316 695283 := bstep (se 1 (by rfl) ⟨521462, by rfl⟩ : syracuseStep 695283 = 1042925) B1042925
theorem B695299 : Blo 694316 695299 := bstep (se 1 (by rfl) ⟨521474, by rfl⟩ : syracuseStep 695299 = 1042949) B1042949
theorem B695315 : Blo 694316 695315 := bstep (se 1 (by rfl) ⟨521486, by rfl⟩ : syracuseStep 695315 = 1042973) B1042973
theorem B695331 : Blo 694316 695331 := bstep (se 1 (by rfl) ⟨521498, by rfl⟩ : syracuseStep 695331 = 1042997) B1042997
theorem B695347 : Blo 694316 695347 := bstep (se 1 (by rfl) ⟨521510, by rfl⟩ : syracuseStep 695347 = 1043021) B1043021
theorem B695363 : Blo 694316 695363 := bstep (se 1 (by rfl) ⟨521522, by rfl⟩ : syracuseStep 695363 = 1043045) B1043045
theorem B2825293 : Blo 694316 2825293 := bstep (se 3 (by rfl) ⟨529742, by rfl⟩ : syracuseStep 2825293 = 1059485) B1059485
theorem B695379 : Blo 694316 695379 := bstep (se 1 (by rfl) ⟨521534, by rfl⟩ : syracuseStep 695379 = 1043069) B1043069
theorem B695395 : Blo 694316 695395 := bstep (se 1 (by rfl) ⟨521546, by rfl⟩ : syracuseStep 695395 = 1043093) B1043093
theorem B695411 : Blo 694316 695411 := bstep (se 1 (by rfl) ⟨521558, by rfl⟩ : syracuseStep 695411 = 1043117) B1043117
theorem B1055873 : Blo 694316 1055873 := bstep (se 2 (by rfl) ⟨395952, by rfl⟩ : syracuseStep 1055873 = 791905) B791905
theorem B695427 : Blo 694316 695427 := bstep (se 1 (by rfl) ⟨521570, by rfl⟩ : syracuseStep 695427 = 1043141) B1043141
theorem B695443 : Blo 694316 695443 := bstep (se 1 (by rfl) ⟨521582, by rfl⟩ : syracuseStep 695443 = 1043165) B1043165
theorem B695459 : Blo 694316 695459 := bstep (se 1 (by rfl) ⟨521594, by rfl⟩ : syracuseStep 695459 = 1043189) B1043189
theorem B695475 : Blo 694316 695475 := bstep (se 1 (by rfl) ⟨521606, by rfl⟩ : syracuseStep 695475 = 1043213) B1043213
theorem B695491 : Blo 694316 695491 := bstep (se 1 (by rfl) ⟨521618, by rfl⟩ : syracuseStep 695491 = 1043237) B1043237
theorem B695507 : Blo 694316 695507 := bstep (se 1 (by rfl) ⟨521630, by rfl⟩ : syracuseStep 695507 = 1043261) B1043261
theorem B695523 : Blo 694316 695523 := bstep (se 1 (by rfl) ⟨521642, by rfl⟩ : syracuseStep 695523 = 1043285) B1043285
theorem B695539 : Blo 694316 695539 := bstep (se 1 (by rfl) ⟨521654, by rfl⟩ : syracuseStep 695539 = 1043309) B1043309
theorem B1056001 : Blo 694316 1056001 := bstep (se 2 (by rfl) ⟨396000, by rfl⟩ : syracuseStep 1056001 = 792001) B792001
theorem B695555 : Blo 694316 695555 := bstep (se 1 (by rfl) ⟨521666, by rfl⟩ : syracuseStep 695555 = 1043333) B1043333
theorem B695571 : Blo 694316 695571 := bstep (se 1 (by rfl) ⟨521678, by rfl⟩ : syracuseStep 695571 = 1043357) B1043357
theorem B695587 : Blo 694316 695587 := bstep (se 1 (by rfl) ⟨521690, by rfl⟩ : syracuseStep 695587 = 1043381) B1043381
theorem B695603 : Blo 694316 695603 := bstep (se 1 (by rfl) ⟨521702, by rfl⟩ : syracuseStep 695603 = 1043405) B1043405
theorem B695619 : Blo 694316 695619 := bstep (se 1 (by rfl) ⟨521714, by rfl⟩ : syracuseStep 695619 = 1043429) B1043429
theorem B695635 : Blo 694316 695635 := bstep (se 1 (by rfl) ⟨521726, by rfl⟩ : syracuseStep 695635 = 1043453) B1043453
theorem B695651 : Blo 694316 695651 := bstep (se 1 (by rfl) ⟨521738, by rfl⟩ : syracuseStep 695651 = 1043477) B1043477
theorem B695667 : Blo 694316 695667 := bstep (se 1 (by rfl) ⟨521750, by rfl⟩ : syracuseStep 695667 = 1043501) B1043501
theorem B695683 : Blo 694316 695683 := bstep (se 1 (by rfl) ⟨521762, by rfl⟩ : syracuseStep 695683 = 1043525) B1043525
theorem B695699 : Blo 694316 695699 := bstep (se 1 (by rfl) ⟨521774, by rfl⟩ : syracuseStep 695699 = 1043549) B1043549
theorem B695715 : Blo 694316 695715 := bstep (se 1 (by rfl) ⟨521786, by rfl⟩ : syracuseStep 695715 = 1043573) B1043573
theorem B3349937 : Blo 694316 3349937 := bstep (se 2 (by rfl) ⟨1256226, by rfl⟩ : syracuseStep 3349937 = 2512453) B2512453
theorem B695731 : Blo 694316 695731 := bstep (se 1 (by rfl) ⟨521798, by rfl⟩ : syracuseStep 695731 = 1043597) B1043597
theorem B990643 : Blo 694316 990643 := bstep (se 1 (by rfl) ⟨742982, by rfl⟩ : syracuseStep 990643 = 1485965) B1485965
theorem B695747 : Blo 694316 695747 := bstep (se 1 (by rfl) ⟨521810, by rfl⟩ : syracuseStep 695747 = 1043621) B1043621
theorem B695763 : Blo 694316 695763 := bstep (se 1 (by rfl) ⟨521822, by rfl⟩ : syracuseStep 695763 = 1043645) B1043645
theorem B695779 : Blo 694316 695779 := bstep (se 1 (by rfl) ⟨521834, by rfl⟩ : syracuseStep 695779 = 1043669) B1043669
theorem B695795 : Blo 694316 695795 := bstep (se 1 (by rfl) ⟨521846, by rfl⟩ : syracuseStep 695795 = 1043693) B1043693
theorem B695811 : Blo 694316 695811 := bstep (se 1 (by rfl) ⟨521858, by rfl⟩ : syracuseStep 695811 = 1043717) B1043717
theorem B695827 : Blo 694316 695827 := bstep (se 1 (by rfl) ⟨521870, by rfl⟩ : syracuseStep 695827 = 1043741) B1043741
theorem B695843 : Blo 694316 695843 := bstep (se 1 (by rfl) ⟨521882, by rfl⟩ : syracuseStep 695843 = 1043765) B1043765
theorem B695859 : Blo 694316 695859 := bstep (se 1 (by rfl) ⟨521894, by rfl⟩ : syracuseStep 695859 = 1043789) B1043789
theorem B695875 : Blo 694316 695875 := bstep (se 1 (by rfl) ⟨521906, by rfl⟩ : syracuseStep 695875 = 1043813) B1043813
theorem B3972685 : Blo 694316 3972685 := bstep (se 3 (by rfl) ⟨744878, by rfl⟩ : syracuseStep 3972685 = 1489757) B1489757
theorem B695891 : Blo 694316 695891 := bstep (se 1 (by rfl) ⟨521918, by rfl⟩ : syracuseStep 695891 = 1043837) B1043837
theorem B695907 : Blo 694316 695907 := bstep (se 1 (by rfl) ⟨521930, by rfl⟩ : syracuseStep 695907 = 1043861) B1043861
theorem B695923 : Blo 694316 695923 := bstep (se 1 (by rfl) ⟨521942, by rfl⟩ : syracuseStep 695923 = 1043885) B1043885
theorem B695939 : Blo 694316 695939 := bstep (se 1 (by rfl) ⟨521954, by rfl⟩ : syracuseStep 695939 = 1043909) B1043909
theorem B695955 : Blo 694316 695955 := bstep (se 1 (by rfl) ⟨521966, by rfl⟩ : syracuseStep 695955 = 1043933) B1043933
theorem B695971 : Blo 694316 695971 := bstep (se 1 (by rfl) ⟨521978, by rfl⟩ : syracuseStep 695971 = 1043957) B1043957
theorem B695987 : Blo 694316 695987 := bstep (se 1 (by rfl) ⟨521990, by rfl⟩ : syracuseStep 695987 = 1043981) B1043981
theorem B696003 : Blo 694316 696003 := bstep (se 1 (by rfl) ⟨522002, by rfl⟩ : syracuseStep 696003 = 1044005) B1044005
theorem B1318609 : Blo 694316 1318609 := bstep (se 2 (by rfl) ⟨494478, by rfl⟩ : syracuseStep 1318609 = 988957) B988957
theorem B696019 : Blo 694316 696019 := bstep (se 1 (by rfl) ⟨522014, by rfl⟩ : syracuseStep 696019 = 1044029) B1044029
theorem B696035 : Blo 694316 696035 := bstep (se 1 (by rfl) ⟨522026, by rfl⟩ : syracuseStep 696035 = 1044053) B1044053
theorem B696051 : Blo 694316 696051 := bstep (se 1 (by rfl) ⟨522038, by rfl⟩ : syracuseStep 696051 = 1044077) B1044077
theorem B696067 : Blo 694316 696067 := bstep (se 1 (by rfl) ⟨522050, by rfl⟩ : syracuseStep 696067 = 1044101) B1044101
theorem B696083 : Blo 694316 696083 := bstep (se 1 (by rfl) ⟨522062, by rfl⟩ : syracuseStep 696083 = 1044125) B1044125
theorem B696099 : Blo 694316 696099 := bstep (se 1 (by rfl) ⟨522074, by rfl⟩ : syracuseStep 696099 = 1044149) B1044149
theorem B696115 : Blo 694316 696115 := bstep (se 1 (by rfl) ⟨522086, by rfl⟩ : syracuseStep 696115 = 1044173) B1044173
theorem B696131 : Blo 694316 696131 := bstep (se 1 (by rfl) ⟨522098, by rfl⟩ : syracuseStep 696131 = 1044197) B1044197
theorem B696147 : Blo 694316 696147 := bstep (se 1 (by rfl) ⟨522110, by rfl⟩ : syracuseStep 696147 = 1044221) B1044221
theorem B696163 : Blo 694316 696163 := bstep (se 1 (by rfl) ⟨522122, by rfl⟩ : syracuseStep 696163 = 1044245) B1044245
theorem B696179 : Blo 694316 696179 := bstep (se 1 (by rfl) ⟨522134, by rfl⟩ : syracuseStep 696179 = 1044269) B1044269
theorem B696195 : Blo 694316 696195 := bstep (se 1 (by rfl) ⟨522146, by rfl⟩ : syracuseStep 696195 = 1044293) B1044293
theorem B991121 : Blo 694316 991121 := bstep (se 2 (by rfl) ⟨371670, by rfl⟩ : syracuseStep 991121 = 743341) B743341
theorem B696211 : Blo 694316 696211 := bstep (se 1 (by rfl) ⟨522158, by rfl⟩ : syracuseStep 696211 = 1044317) B1044317
theorem B696227 : Blo 694316 696227 := bstep (se 1 (by rfl) ⟨522170, by rfl⟩ : syracuseStep 696227 = 1044341) B1044341
theorem B696243 : Blo 694316 696243 := bstep (se 1 (by rfl) ⟨522182, by rfl⟩ : syracuseStep 696243 = 1044365) B1044365
theorem B696259 : Blo 694316 696259 := bstep (se 1 (by rfl) ⟨522194, by rfl⟩ : syracuseStep 696259 = 1044389) B1044389
theorem B696275 : Blo 694316 696275 := bstep (se 1 (by rfl) ⟨522206, by rfl⟩ : syracuseStep 696275 = 1044413) B1044413
theorem B696291 : Blo 694316 696291 := bstep (se 1 (by rfl) ⟨522218, by rfl⟩ : syracuseStep 696291 = 1044437) B1044437
theorem B696307 : Blo 694316 696307 := bstep (se 1 (by rfl) ⟨522230, by rfl⟩ : syracuseStep 696307 = 1044461) B1044461
theorem B991235 : Blo 694316 991235 := bstep (se 1 (by rfl) ⟨743426, by rfl⟩ : syracuseStep 991235 = 1486853) B1486853
theorem B696323 : Blo 694316 696323 := bstep (se 1 (by rfl) ⟨522242, by rfl⟩ : syracuseStep 696323 = 1044485) B1044485
theorem B696339 : Blo 694316 696339 := bstep (se 1 (by rfl) ⟨522254, by rfl⟩ : syracuseStep 696339 = 1044509) B1044509
theorem B696355 : Blo 694316 696355 := bstep (se 1 (by rfl) ⟨522266, by rfl⟩ : syracuseStep 696355 = 1044533) B1044533
theorem B696371 : Blo 694316 696371 := bstep (se 1 (by rfl) ⟨522278, by rfl⟩ : syracuseStep 696371 = 1044557) B1044557
theorem B696387 : Blo 694316 696387 := bstep (se 1 (by rfl) ⟨522290, by rfl⟩ : syracuseStep 696387 = 1044581) B1044581
theorem B991315 : Blo 694316 991315 := bstep (se 1 (by rfl) ⟨743486, by rfl⟩ : syracuseStep 991315 = 1486973) B1486973
theorem B696403 : Blo 694316 696403 := bstep (se 1 (by rfl) ⟨522302, by rfl⟩ : syracuseStep 696403 = 1044605) B1044605
theorem B696419 : Blo 694316 696419 := bstep (se 1 (by rfl) ⟨522314, by rfl⟩ : syracuseStep 696419 = 1044629) B1044629
theorem B1056883 : Blo 694316 1056883 := bstep (se 1 (by rfl) ⟨792662, by rfl⟩ : syracuseStep 1056883 = 1585325) B1585325
theorem B696435 : Blo 694316 696435 := bstep (se 1 (by rfl) ⟨522326, by rfl⟩ : syracuseStep 696435 = 1044653) B1044653
theorem B696451 : Blo 694316 696451 := bstep (se 1 (by rfl) ⟨522338, by rfl⟩ : syracuseStep 696451 = 1044677) B1044677
theorem B696467 : Blo 694316 696467 := bstep (se 1 (by rfl) ⟨522350, by rfl⟩ : syracuseStep 696467 = 1044701) B1044701
theorem B696483 : Blo 694316 696483 := bstep (se 1 (by rfl) ⟨522362, by rfl⟩ : syracuseStep 696483 = 1044725) B1044725
theorem B696499 : Blo 694316 696499 := bstep (se 1 (by rfl) ⟨522374, by rfl⟩ : syracuseStep 696499 = 1044749) B1044749
theorem B696515 : Blo 694316 696515 := bstep (se 1 (by rfl) ⟨522386, by rfl⟩ : syracuseStep 696515 = 1044773) B1044773
theorem B1056979 : Blo 694316 1056979 := bstep (se 1 (by rfl) ⟨792734, by rfl⟩ : syracuseStep 1056979 = 1585469) B1585469
theorem B696531 : Blo 694316 696531 := bstep (se 1 (by rfl) ⟨522398, by rfl⟩ : syracuseStep 696531 = 1044797) B1044797
theorem B696547 : Blo 694316 696547 := bstep (se 1 (by rfl) ⟨522410, by rfl⟩ : syracuseStep 696547 = 1044821) B1044821
theorem B32219363 : Blo 694316 32219363 := bstep (se 1 (by rfl) ⟨24164522, by rfl⟩ : syracuseStep 32219363 = 48329045) B48329045
theorem B696563 : Blo 694316 696563 := bstep (se 1 (by rfl) ⟨522422, by rfl⟩ : syracuseStep 696563 = 1044845) B1044845
theorem B696579 : Blo 694316 696579 := bstep (se 1 (by rfl) ⟨522434, by rfl⟩ : syracuseStep 696579 = 1044869) B1044869
theorem B696595 : Blo 694316 696595 := bstep (se 1 (by rfl) ⟨522446, by rfl⟩ : syracuseStep 696595 = 1044893) B1044893
theorem B696611 : Blo 694316 696611 := bstep (se 1 (by rfl) ⟨522458, by rfl⟩ : syracuseStep 696611 = 1044917) B1044917
theorem B696627 : Blo 694316 696627 := bstep (se 1 (by rfl) ⟨522470, by rfl⟩ : syracuseStep 696627 = 1044941) B1044941
theorem B696643 : Blo 694316 696643 := bstep (se 1 (by rfl) ⟨522482, by rfl⟩ : syracuseStep 696643 = 1044965) B1044965
theorem B696659 : Blo 694316 696659 := bstep (se 1 (by rfl) ⟨522494, by rfl⟩ : syracuseStep 696659 = 1044989) B1044989
theorem B696675 : Blo 694316 696675 := bstep (se 1 (by rfl) ⟨522506, by rfl⟩ : syracuseStep 696675 = 1045013) B1045013
theorem B696691 : Blo 694316 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B696707 : Blo 694316 696707 := bstep (se 1 (by rfl) ⟨522530, by rfl⟩ : syracuseStep 696707 = 1045061) B1045061
theorem B696723 : Blo 694316 696723 := bstep (se 1 (by rfl) ⟨522542, by rfl⟩ : syracuseStep 696723 = 1045085) B1045085
theorem B696739 : Blo 694316 696739 := bstep (se 1 (by rfl) ⟨522554, by rfl⟩ : syracuseStep 696739 = 1045109) B1045109
theorem B696755 : Blo 694316 696755 := bstep (se 1 (by rfl) ⟨522566, by rfl⟩ : syracuseStep 696755 = 1045133) B1045133
theorem B1057217 : Blo 694316 1057217 := bstep (se 2 (by rfl) ⟨396456, by rfl⟩ : syracuseStep 1057217 = 792913) B792913
theorem B696771 : Blo 694316 696771 := bstep (se 1 (by rfl) ⟨522578, by rfl⟩ : syracuseStep 696771 = 1045157) B1045157
theorem B696787 : Blo 694316 696787 := bstep (se 1 (by rfl) ⟨522590, by rfl⟩ : syracuseStep 696787 = 1045181) B1045181
theorem B696803 : Blo 694316 696803 := bstep (se 1 (by rfl) ⟨522602, by rfl⟩ : syracuseStep 696803 = 1045205) B1045205
theorem B696819 : Blo 694316 696819 := bstep (se 1 (by rfl) ⟨522614, by rfl⟩ : syracuseStep 696819 = 1045229) B1045229
theorem B696835 : Blo 694316 696835 := bstep (se 1 (by rfl) ⟨522626, by rfl⟩ : syracuseStep 696835 = 1045253) B1045253
theorem B696851 : Blo 694316 696851 := bstep (se 1 (by rfl) ⟨522638, by rfl⟩ : syracuseStep 696851 = 1045277) B1045277
theorem B696867 : Blo 694316 696867 := bstep (se 1 (by rfl) ⟨522650, by rfl⟩ : syracuseStep 696867 = 1045301) B1045301
theorem B696883 : Blo 694316 696883 := bstep (se 1 (by rfl) ⟨522662, by rfl⟩ : syracuseStep 696883 = 1045325) B1045325
theorem B696899 : Blo 694316 696899 := bstep (se 1 (by rfl) ⟨522674, by rfl⟩ : syracuseStep 696899 = 1045349) B1045349
theorem B696915 : Blo 694316 696915 := bstep (se 1 (by rfl) ⟨522686, by rfl⟩ : syracuseStep 696915 = 1045373) B1045373
theorem B696931 : Blo 694316 696931 := bstep (se 1 (by rfl) ⟨522698, by rfl⟩ : syracuseStep 696931 = 1045397) B1045397
theorem B696947 : Blo 694316 696947 := bstep (se 1 (by rfl) ⟨522710, by rfl⟩ : syracuseStep 696947 = 1045421) B1045421
theorem B991873 : Blo 694316 991873 := bstep (se 2 (by rfl) ⟨371952, by rfl⟩ : syracuseStep 991873 = 743905) B743905
theorem B696963 : Blo 694316 696963 := bstep (se 1 (by rfl) ⟨522722, by rfl⟩ : syracuseStep 696963 = 1045445) B1045445
theorem B696979 : Blo 694316 696979 := bstep (se 1 (by rfl) ⟨522734, by rfl⟩ : syracuseStep 696979 = 1045469) B1045469
theorem B696995 : Blo 694316 696995 := bstep (se 1 (by rfl) ⟨522746, by rfl⟩ : syracuseStep 696995 = 1045493) B1045493
theorem B697011 : Blo 694316 697011 := bstep (se 1 (by rfl) ⟨522758, by rfl⟩ : syracuseStep 697011 = 1045517) B1045517
theorem B697027 : Blo 694316 697027 := bstep (se 1 (by rfl) ⟨522770, by rfl⟩ : syracuseStep 697027 = 1045541) B1045541
theorem B697043 : Blo 694316 697043 := bstep (se 1 (by rfl) ⟨522782, by rfl⟩ : syracuseStep 697043 = 1045565) B1045565
theorem B697059 : Blo 694316 697059 := bstep (se 1 (by rfl) ⟨522794, by rfl⟩ : syracuseStep 697059 = 1045589) B1045589
theorem B1319665 : Blo 694316 1319665 := bstep (se 2 (by rfl) ⟨494874, by rfl⟩ : syracuseStep 1319665 = 989749) B989749
theorem B697075 : Blo 694316 697075 := bstep (se 1 (by rfl) ⟨522806, by rfl⟩ : syracuseStep 697075 = 1045613) B1045613
theorem B697091 : Blo 694316 697091 := bstep (se 1 (by rfl) ⟨522818, by rfl⟩ : syracuseStep 697091 = 1045637) B1045637
theorem B697107 : Blo 694316 697107 := bstep (se 1 (by rfl) ⟨522830, by rfl⟩ : syracuseStep 697107 = 1045661) B1045661
theorem B697123 : Blo 694316 697123 := bstep (se 1 (by rfl) ⟨522842, by rfl⟩ : syracuseStep 697123 = 1045685) B1045685
theorem B697139 : Blo 694316 697139 := bstep (se 1 (by rfl) ⟨522854, by rfl⟩ : syracuseStep 697139 = 1045709) B1045709
theorem B697155 : Blo 694316 697155 := bstep (se 1 (by rfl) ⟨522866, by rfl⟩ : syracuseStep 697155 = 1045733) B1045733
theorem B697171 : Blo 694316 697171 := bstep (se 1 (by rfl) ⟨522878, by rfl⟩ : syracuseStep 697171 = 1045757) B1045757
theorem B697187 : Blo 694316 697187 := bstep (se 1 (by rfl) ⟨522890, by rfl⟩ : syracuseStep 697187 = 1045781) B1045781
theorem B697203 : Blo 694316 697203 := bstep (se 1 (by rfl) ⟨522902, by rfl⟩ : syracuseStep 697203 = 1045805) B1045805
theorem B697219 : Blo 694316 697219 := bstep (se 1 (by rfl) ⟨522914, by rfl⟩ : syracuseStep 697219 = 1045829) B1045829
theorem B697235 : Blo 694316 697235 := bstep (se 1 (by rfl) ⟨522926, by rfl⟩ : syracuseStep 697235 = 1045853) B1045853
theorem B697251 : Blo 694316 697251 := bstep (se 1 (by rfl) ⟨522938, by rfl⟩ : syracuseStep 697251 = 1045877) B1045877
theorem B697267 : Blo 694316 697267 := bstep (se 1 (by rfl) ⟨522950, by rfl⟩ : syracuseStep 697267 = 1045901) B1045901
theorem B697283 : Blo 694316 697283 := bstep (se 1 (by rfl) ⟨522962, by rfl⟩ : syracuseStep 697283 = 1045925) B1045925
theorem B697299 : Blo 694316 697299 := bstep (se 1 (by rfl) ⟨522974, by rfl⟩ : syracuseStep 697299 = 1045949) B1045949
theorem B697315 : Blo 694316 697315 := bstep (se 1 (by rfl) ⟨522986, by rfl⟩ : syracuseStep 697315 = 1045973) B1045973
theorem B697331 : Blo 694316 697331 := bstep (se 1 (by rfl) ⟨522998, by rfl⟩ : syracuseStep 697331 = 1045997) B1045997
theorem B697347 : Blo 694316 697347 := bstep (se 1 (by rfl) ⟨523010, by rfl⟩ : syracuseStep 697347 = 1046021) B1046021
theorem B697363 : Blo 694316 697363 := bstep (se 1 (by rfl) ⟨523022, by rfl⟩ : syracuseStep 697363 = 1046045) B1046045
theorem B697379 : Blo 694316 697379 := bstep (se 1 (by rfl) ⟨523034, by rfl⟩ : syracuseStep 697379 = 1046069) B1046069
theorem B697395 : Blo 694316 697395 := bstep (se 1 (by rfl) ⟨523046, by rfl⟩ : syracuseStep 697395 = 1046093) B1046093
theorem B17409077 : Blo 694316 17409077 := bstep (se 5 (by rfl) ⟨816050, by rfl⟩ : syracuseStep 17409077 = 1632101) B1632101
theorem B697411 : Blo 694316 697411 := bstep (se 1 (by rfl) ⟨523058, by rfl⟩ : syracuseStep 697411 = 1046117) B1046117
theorem B697427 : Blo 694316 697427 := bstep (se 1 (by rfl) ⟨523070, by rfl⟩ : syracuseStep 697427 = 1046141) B1046141
theorem B4465763 : Blo 694316 4465763 := bstep (se 1 (by rfl) ⟨3349322, by rfl⟩ : syracuseStep 4465763 = 6698645) B6698645
theorem B697443 : Blo 694316 697443 := bstep (se 1 (by rfl) ⟨523082, by rfl⟩ : syracuseStep 697443 = 1046165) B1046165
theorem B697459 : Blo 694316 697459 := bstep (se 1 (by rfl) ⟨523094, by rfl⟩ : syracuseStep 697459 = 1046189) B1046189
theorem B1320067 : Blo 694316 1320067 := bstep (se 1 (by rfl) ⟨990050, by rfl⟩ : syracuseStep 1320067 = 1980101) B1980101
theorem B697475 : Blo 694316 697475 := bstep (se 1 (by rfl) ⟨523106, by rfl⟩ : syracuseStep 697475 = 1046213) B1046213
theorem B697491 : Blo 694316 697491 := bstep (se 1 (by rfl) ⟨523118, by rfl⟩ : syracuseStep 697491 = 1046237) B1046237
theorem B697507 : Blo 694316 697507 := bstep (se 1 (by rfl) ⟨523130, by rfl⟩ : syracuseStep 697507 = 1046261) B1046261
theorem B1320113 : Blo 694316 1320113 := bstep (se 2 (by rfl) ⟨495042, by rfl⟩ : syracuseStep 1320113 = 990085) B990085
theorem B697523 : Blo 694316 697523 := bstep (se 1 (by rfl) ⟨523142, by rfl⟩ : syracuseStep 697523 = 1046285) B1046285
theorem B697539 : Blo 694316 697539 := bstep (se 1 (by rfl) ⟨523154, by rfl⟩ : syracuseStep 697539 = 1046309) B1046309
theorem B2008273 : Blo 694316 2008273 := bstep (se 2 (by rfl) ⟨753102, by rfl⟩ : syracuseStep 2008273 = 1506205) B1506205
theorem B697555 : Blo 694316 697555 := bstep (se 1 (by rfl) ⟨523166, by rfl⟩ : syracuseStep 697555 = 1046333) B1046333
theorem B697571 : Blo 694316 697571 := bstep (se 1 (by rfl) ⟨523178, by rfl⟩ : syracuseStep 697571 = 1046357) B1046357
theorem B697587 : Blo 694316 697587 := bstep (se 1 (by rfl) ⟨523190, by rfl⟩ : syracuseStep 697587 = 1046381) B1046381
theorem B697603 : Blo 694316 697603 := bstep (se 1 (by rfl) ⟨523202, by rfl⟩ : syracuseStep 697603 = 1046405) B1046405
theorem B697619 : Blo 694316 697619 := bstep (se 1 (by rfl) ⟨523214, by rfl⟩ : syracuseStep 697619 = 1046429) B1046429
theorem B697635 : Blo 694316 697635 := bstep (se 1 (by rfl) ⟨523226, by rfl⟩ : syracuseStep 697635 = 1046453) B1046453
theorem B894259 : Blo 694316 894259 := bstep (se 1 (by rfl) ⟨670694, by rfl⟩ : syracuseStep 894259 = 1341389) B1341389
theorem B697651 : Blo 694316 697651 := bstep (se 1 (by rfl) ⟨523238, by rfl⟩ : syracuseStep 697651 = 1046477) B1046477
theorem B992579 : Blo 694316 992579 := bstep (se 1 (by rfl) ⟨744434, by rfl⟩ : syracuseStep 992579 = 1488869) B1488869
theorem B697667 : Blo 694316 697667 := bstep (se 1 (by rfl) ⟨523250, by rfl⟩ : syracuseStep 697667 = 1046501) B1046501
theorem B697683 : Blo 694316 697683 := bstep (se 1 (by rfl) ⟨523262, by rfl⟩ : syracuseStep 697683 = 1046525) B1046525
theorem B1058147 : Blo 694316 1058147 := bstep (se 1 (by rfl) ⟨793610, by rfl⟩ : syracuseStep 1058147 = 1587221) B1587221
theorem B697699 : Blo 694316 697699 := bstep (se 1 (by rfl) ⟨523274, by rfl⟩ : syracuseStep 697699 = 1046549) B1046549
theorem B697715 : Blo 694316 697715 := bstep (se 1 (by rfl) ⟨523286, by rfl⟩ : syracuseStep 697715 = 1046573) B1046573
theorem B697731 : Blo 694316 697731 := bstep (se 1 (by rfl) ⟨523298, by rfl⟩ : syracuseStep 697731 = 1046597) B1046597
theorem B697747 : Blo 694316 697747 := bstep (se 1 (by rfl) ⟨523310, by rfl⟩ : syracuseStep 697747 = 1046621) B1046621
theorem B697763 : Blo 694316 697763 := bstep (se 1 (by rfl) ⟨523322, by rfl⟩ : syracuseStep 697763 = 1046645) B1046645
theorem B697779 : Blo 694316 697779 := bstep (se 1 (by rfl) ⟨523334, by rfl⟩ : syracuseStep 697779 = 1046669) B1046669
theorem B697795 : Blo 694316 697795 := bstep (se 1 (by rfl) ⟨523346, by rfl⟩ : syracuseStep 697795 = 1046693) B1046693
theorem B1320401 : Blo 694316 1320401 := bstep (se 2 (by rfl) ⟨495150, by rfl⟩ : syracuseStep 1320401 = 990301) B990301
theorem B697811 : Blo 694316 697811 := bstep (se 1 (by rfl) ⟨523358, by rfl⟩ : syracuseStep 697811 = 1046717) B1046717
theorem B697827 : Blo 694316 697827 := bstep (se 1 (by rfl) ⟨523370, by rfl⟩ : syracuseStep 697827 = 1046741) B1046741
theorem B697843 : Blo 694316 697843 := bstep (se 1 (by rfl) ⟨523382, by rfl⟩ : syracuseStep 697843 = 1046765) B1046765
theorem B697859 : Blo 694316 697859 := bstep (se 1 (by rfl) ⟨523394, by rfl⟩ : syracuseStep 697859 = 1046789) B1046789
theorem B3974669 : Blo 694316 3974669 := bstep (se 3 (by rfl) ⟨745250, by rfl⟩ : syracuseStep 3974669 = 1490501) B1490501
theorem B697875 : Blo 694316 697875 := bstep (se 1 (by rfl) ⟨523406, by rfl⟩ : syracuseStep 697875 = 1046813) B1046813
theorem B697891 : Blo 694316 697891 := bstep (se 1 (by rfl) ⟨523418, by rfl⟩ : syracuseStep 697891 = 1046837) B1046837
theorem B697907 : Blo 694316 697907 := bstep (se 1 (by rfl) ⟨523430, by rfl⟩ : syracuseStep 697907 = 1046861) B1046861
theorem B697923 : Blo 694316 697923 := bstep (se 1 (by rfl) ⟨523442, by rfl⟩ : syracuseStep 697923 = 1046885) B1046885
theorem B4236869 : Blo 694316 4236869 := bstep (se 4 (by rfl) ⟨397206, by rfl⟩ : syracuseStep 4236869 = 794413) B794413
theorem B697939 : Blo 694316 697939 := bstep (se 1 (by rfl) ⟨523454, by rfl⟩ : syracuseStep 697939 = 1046909) B1046909
theorem B697955 : Blo 694316 697955 := bstep (se 1 (by rfl) ⟨523466, by rfl⟩ : syracuseStep 697955 = 1046933) B1046933
theorem B697971 : Blo 694316 697971 := bstep (se 1 (by rfl) ⟨523478, by rfl⟩ : syracuseStep 697971 = 1046957) B1046957
theorem B1484419 : Blo 694316 1484419 := bstep (se 1 (by rfl) ⟨1113314, by rfl⟩ : syracuseStep 1484419 = 2226629) B2226629
theorem B697987 : Blo 694316 697987 := bstep (se 1 (by rfl) ⟨523490, by rfl⟩ : syracuseStep 697987 = 1046981) B1046981
theorem B698003 : Blo 694316 698003 := bstep (se 1 (by rfl) ⟨523502, by rfl⟩ : syracuseStep 698003 = 1047005) B1047005
theorem B698019 : Blo 694316 698019 := bstep (se 1 (by rfl) ⟨523514, by rfl⟩ : syracuseStep 698019 = 1047029) B1047029
theorem B1058483 : Blo 694316 1058483 := bstep (se 1 (by rfl) ⟨793862, by rfl⟩ : syracuseStep 1058483 = 1587725) B1587725
theorem B698035 : Blo 694316 698035 := bstep (se 1 (by rfl) ⟨523526, by rfl⟩ : syracuseStep 698035 = 1047053) B1047053
theorem B698051 : Blo 694316 698051 := bstep (se 1 (by rfl) ⟨523538, by rfl⟩ : syracuseStep 698051 = 1047077) B1047077
theorem B698067 : Blo 694316 698067 := bstep (se 1 (by rfl) ⟨523550, by rfl⟩ : syracuseStep 698067 = 1047101) B1047101
theorem B698083 : Blo 694316 698083 := bstep (se 1 (by rfl) ⟨523562, by rfl⟩ : syracuseStep 698083 = 1047125) B1047125
theorem B698099 : Blo 694316 698099 := bstep (se 1 (by rfl) ⟨523574, by rfl⟩ : syracuseStep 698099 = 1047149) B1047149
theorem B698115 : Blo 694316 698115 := bstep (se 1 (by rfl) ⟨523586, by rfl⟩ : syracuseStep 698115 = 1047173) B1047173
theorem B698131 : Blo 694316 698131 := bstep (se 1 (by rfl) ⟨523598, by rfl⟩ : syracuseStep 698131 = 1047197) B1047197
theorem B698147 : Blo 694316 698147 := bstep (se 1 (by rfl) ⟨523610, by rfl⟩ : syracuseStep 698147 = 1047221) B1047221
theorem B3516209 : Blo 694316 3516209 := bstep (se 2 (by rfl) ⟨1318578, by rfl⟩ : syracuseStep 3516209 = 2637157) B2637157
theorem B698163 : Blo 694316 698163 := bstep (se 1 (by rfl) ⟨523622, by rfl⟩ : syracuseStep 698163 = 1047245) B1047245
theorem B698179 : Blo 694316 698179 := bstep (se 1 (by rfl) ⟨523634, by rfl⟩ : syracuseStep 698179 = 1047269) B1047269
theorem B698195 : Blo 694316 698195 := bstep (se 1 (by rfl) ⟨523646, by rfl⟩ : syracuseStep 698195 = 1047293) B1047293
theorem B698211 : Blo 694316 698211 := bstep (se 1 (by rfl) ⟨523658, by rfl⟩ : syracuseStep 698211 = 1047317) B1047317
theorem B698227 : Blo 694316 698227 := bstep (se 1 (by rfl) ⟨523670, by rfl⟩ : syracuseStep 698227 = 1047341) B1047341
theorem B698243 : Blo 694316 698243 := bstep (se 1 (by rfl) ⟨523682, by rfl⟩ : syracuseStep 698243 = 1047365) B1047365
theorem B698259 : Blo 694316 698259 := bstep (se 1 (by rfl) ⟨523694, by rfl⟩ : syracuseStep 698259 = 1047389) B1047389
theorem B698275 : Blo 694316 698275 := bstep (se 1 (by rfl) ⟨523706, by rfl⟩ : syracuseStep 698275 = 1047413) B1047413
theorem B698291 : Blo 694316 698291 := bstep (se 1 (by rfl) ⟨523718, by rfl⟩ : syracuseStep 698291 = 1047437) B1047437
theorem B993217 : Blo 694316 993217 := bstep (se 2 (by rfl) ⟨372456, by rfl⟩ : syracuseStep 993217 = 744913) B744913
theorem B698307 : Blo 694316 698307 := bstep (se 1 (by rfl) ⟨523730, by rfl⟩ : syracuseStep 698307 = 1047461) B1047461
theorem B1255441 : Blo 694316 1255441 := bstep (se 2 (by rfl) ⟨470790, by rfl⟩ : syracuseStep 1255441 = 941581) B941581
theorem B1189937 : Blo 694316 1189937 := bstep (se 2 (by rfl) ⟨446226, by rfl⟩ : syracuseStep 1189937 = 892453) B892453
theorem B993331 : Blo 694316 993331 := bstep (se 1 (by rfl) ⟨744998, by rfl⟩ : syracuseStep 993331 = 1489997) B1489997
theorem B1321123 : Blo 694316 1321123 := bstep (se 1 (by rfl) ⟨990842, by rfl⟩ : syracuseStep 1321123 = 1981685) B1981685
theorem B3975601 : Blo 694316 3975601 := bstep (se 2 (by rfl) ⟨1490850, by rfl⟩ : syracuseStep 3975601 = 2981701) B2981701
theorem B3582413 : Blo 694316 3582413 := bstep (se 3 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 3582413 = 1343405) B1343405
theorem B1190465 : Blo 694316 1190465 := bstep (se 2 (by rfl) ⟨446424, by rfl⟩ : syracuseStep 1190465 = 892849) B892849
theorem B1256003 : Blo 694316 1256003 := bstep (se 1 (by rfl) ⟨942002, by rfl⟩ : syracuseStep 1256003 = 1884005) B1884005
theorem B1321571 : Blo 694316 1321571 := bstep (se 1 (by rfl) ⟨991178, by rfl⟩ : syracuseStep 1321571 = 1982357) B1982357
theorem B1223345 : Blo 694316 1223345 := bstep (se 2 (by rfl) ⟨458754, by rfl⟩ : syracuseStep 1223345 = 917509) B917509
theorem B2009933 : Blo 694316 2009933 := bstep (se 3 (by rfl) ⟨376862, by rfl⟩ : syracuseStep 2009933 = 753725) B753725
theorem B1321859 : Blo 694316 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B3582947 : Blo 694316 3582947 := bstep (se 1 (by rfl) ⟨2687210, by rfl⟩ : syracuseStep 3582947 = 5374421) B5374421
theorem B6794225 : Blo 694316 6794225 := bstep (se 2 (by rfl) ⟨2547834, by rfl⟩ : syracuseStep 6794225 = 5095669) B5095669
theorem B1256465 : Blo 694316 1256465 := bstep (se 2 (by rfl) ⟨471174, by rfl⟩ : syracuseStep 1256465 = 942349) B942349
theorem B1190963 : Blo 694316 1190963 := bstep (se 1 (by rfl) ⟨893222, by rfl⟩ : syracuseStep 1190963 = 1786445) B1786445
theorem B3517667 : Blo 694316 3517667 := bstep (se 1 (by rfl) ⟨2638250, by rfl⟩ : syracuseStep 3517667 = 5276501) B5276501
theorem B1977709 : Blo 694316 1977709 := bstep (se 3 (by rfl) ⟨370820, by rfl⟩ : syracuseStep 1977709 = 741641) B741641
theorem B1584593 : Blo 694316 1584593 := bstep (se 2 (by rfl) ⟨594222, by rfl⟩ : syracuseStep 1584593 = 1188445) B1188445
theorem B1486289 : Blo 694316 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B1060337 : Blo 694316 1060337 := bstep (se 2 (by rfl) ⟨397626, by rfl⟩ : syracuseStep 1060337 = 795253) B795253
theorem B4763249 : Blo 694316 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B1879843 : Blo 694316 1879843 := bstep (se 1 (by rfl) ⟨1409882, by rfl⟩ : syracuseStep 1879843 = 2819765) B2819765
theorem B1322801 : Blo 694316 1322801 := bstep (se 2 (by rfl) ⟨496050, by rfl⟩ : syracuseStep 1322801 = 992101) B992101
theorem B3977059 : Blo 694316 3977059 := bstep (se 1 (by rfl) ⟨2982794, by rfl⟩ : syracuseStep 3977059 = 5965589) B5965589
theorem B1257329 : Blo 694316 1257329 := bstep (se 2 (by rfl) ⟨471498, by rfl⟩ : syracuseStep 1257329 = 942997) B942997
theorem B1879939 : Blo 694316 1879939 := bstep (se 1 (by rfl) ⟨1409954, by rfl⟩ : syracuseStep 1879939 = 2819909) B2819909
theorem B3518477 : Blo 694316 3518477 := bstep (se 3 (by rfl) ⟨659714, by rfl⟩ : syracuseStep 3518477 = 1319429) B1319429
theorem B766099 : Blo 694316 766099 := bstep (se 1 (by rfl) ⟨574574, by rfl⟩ : syracuseStep 766099 = 1149149) B1149149
theorem B5648611 : Blo 694316 5648611 := bstep (se 1 (by rfl) ⟨4236458, by rfl⟩ : syracuseStep 5648611 = 8472917) B8472917
theorem B1487153 : Blo 694316 1487153 := bstep (se 2 (by rfl) ⟨557682, by rfl⟩ : syracuseStep 1487153 = 1115365) B1115365
theorem B1978769 : Blo 694316 1978769 := bstep (se 2 (by rfl) ⟨742038, by rfl⟩ : syracuseStep 1978769 = 1484077) B1484077
theorem B4239985 : Blo 694316 4239985 := bstep (se 2 (by rfl) ⟨1589994, by rfl⟩ : syracuseStep 4239985 = 3179989) B3179989
theorem B10039949 : Blo 694316 10039949 := bstep (se 3 (by rfl) ⟨1882490, by rfl⟩ : syracuseStep 10039949 = 3764981) B3764981
theorem B1323697 : Blo 694316 1323697 := bstep (se 2 (by rfl) ⟨496386, by rfl⟩ : syracuseStep 1323697 = 992773) B992773
theorem B1880803 : Blo 694316 1880803 := bstep (se 1 (by rfl) ⟨1410602, by rfl⟩ : syracuseStep 1880803 = 2821205) B2821205
theorem B1815313 : Blo 694316 1815313 := bstep (se 2 (by rfl) ⟨680742, by rfl⟩ : syracuseStep 1815313 = 1361485) B1361485
theorem B1323857 : Blo 694316 1323857 := bstep (se 2 (by rfl) ⟨496446, by rfl⟩ : syracuseStep 1323857 = 992893) B992893
theorem B4469681 : Blo 694316 4469681 := bstep (se 2 (by rfl) ⟨1676130, by rfl⟩ : syracuseStep 4469681 = 3352261) B3352261
theorem B1979441 : Blo 694316 1979441 := bstep (se 2 (by rfl) ⟨742290, by rfl⟩ : syracuseStep 1979441 = 1484581) B1484581
theorem B1324259 : Blo 694316 1324259 := bstep (se 1 (by rfl) ⟨993194, by rfl⟩ : syracuseStep 1324259 = 1986389) B1986389
theorem B1488451 : Blo 694316 1488451 := bstep (se 1 (by rfl) ⟨1116338, by rfl⟩ : syracuseStep 1488451 = 2232677) B2232677
theorem B4470349 : Blo 694316 4470349 := bstep (se 3 (by rfl) ⟨838190, by rfl⟩ : syracuseStep 4470349 = 1676381) B1676381
theorem B1980227 : Blo 694316 1980227 := bstep (se 1 (by rfl) ⟨1485170, by rfl⟩ : syracuseStep 1980227 = 2970341) B2970341
theorem B2504611 : Blo 694316 2504611 := bstep (se 1 (by rfl) ⟨1878458, by rfl⟩ : syracuseStep 2504611 = 3756917) B3756917
theorem B964561 : Blo 694316 964561 := bstep (se 2 (by rfl) ⟨361710, by rfl⟩ : syracuseStep 964561 = 723421) B723421
theorem B1325155 : Blo 694316 1325155 := bstep (se 1 (by rfl) ⟨993866, by rfl⟩ : syracuseStep 1325155 = 1987733) B1987733
theorem B1980557 : Blo 694316 1980557 := bstep (se 3 (by rfl) ⟨371354, by rfl⟩ : syracuseStep 1980557 = 742709) B742709
theorem B1980625 : Blo 694316 1980625 := bstep (se 2 (by rfl) ⟨742734, by rfl⟩ : syracuseStep 1980625 = 1485469) B1485469
theorem B1325315 : Blo 694316 1325315 := bstep (se 1 (by rfl) ⟨993986, by rfl⟩ : syracuseStep 1325315 = 1987973) B1987973
theorem B1882385 : Blo 694316 1882385 := bstep (se 2 (by rfl) ⟨705894, by rfl⟩ : syracuseStep 1882385 = 1411789) B1411789
theorem B1980899 : Blo 694316 1980899 := bstep (se 1 (by rfl) ⟨1485674, by rfl⟩ : syracuseStep 1980899 = 2971349) B2971349
theorem B7158257 : Blo 694316 7158257 := bstep (se 2 (by rfl) ⟨2684346, by rfl⟩ : syracuseStep 7158257 = 5368693) B5368693
theorem B5290595 : Blo 694316 5290595 := bstep (se 1 (by rfl) ⟨3967946, by rfl⟩ : syracuseStep 5290595 = 7935893) B7935893
theorem B1489681 : Blo 694316 1489681 := bstep (se 2 (by rfl) ⟨558630, by rfl⟩ : syracuseStep 1489681 = 1117261) B1117261
theorem B2636657 : Blo 694316 2636657 := bstep (se 2 (by rfl) ⟨988746, by rfl⟩ : syracuseStep 2636657 = 1977493) B1977493
theorem B3521393 : Blo 694316 3521393 := bstep (se 2 (by rfl) ⟨1320522, by rfl⟩ : syracuseStep 3521393 = 2641045) B2641045
theorem B834563 : Blo 694316 834563 := bstep (se 1 (by rfl) ⟨625922, by rfl⟩ : syracuseStep 834563 = 1251845) B1251845
theorem B1981741 : Blo 694316 1981741 := bstep (se 3 (by rfl) ⟨371576, by rfl⟩ : syracuseStep 1981741 = 743153) B743153
theorem B1490339 : Blo 694316 1490339 := bstep (se 1 (by rfl) ⟨1117754, by rfl⟩ : syracuseStep 1490339 = 2235509) B2235509
theorem B2014637 : Blo 694316 2014637 := bstep (se 3 (by rfl) ⟨377744, by rfl⟩ : syracuseStep 2014637 = 755489) B755489
theorem B1981901 : Blo 694316 1981901 := bstep (se 3 (by rfl) ⟨371606, by rfl⟩ : syracuseStep 1981901 = 743213) B743213
theorem B1982083 : Blo 694316 1982083 := bstep (se 1 (by rfl) ⟨1486562, by rfl⟩ : syracuseStep 1982083 = 2973125) B2973125
theorem B1883917 : Blo 694316 1883917 := bstep (se 3 (by rfl) ⟨353234, by rfl⟩ : syracuseStep 1883917 = 706469) B706469
theorem B1491185 : Blo 694316 1491185 := bstep (se 2 (by rfl) ⟨559194, by rfl⟩ : syracuseStep 1491185 = 1118389) B1118389
theorem B5161229 : Blo 694316 5161229 := bstep (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) B1935461
theorem B2638115 : Blo 694316 2638115 := bstep (se 1 (by rfl) ⟨1978586, by rfl⟩ : syracuseStep 2638115 = 3957173) B3957173
theorem B3522851 : Blo 694316 3522851 := bstep (se 1 (by rfl) ⟨2642138, by rfl⟩ : syracuseStep 3522851 = 5284277) B5284277
theorem B2638129 : Blo 694316 2638129 := bstep (se 2 (by rfl) ⟨989298, by rfl⟩ : syracuseStep 2638129 = 1978597) B1978597
theorem B1524227 : Blo 694316 1524227 := bstep (se 1 (by rfl) ⟨1143170, by rfl⟩ : syracuseStep 1524227 = 2286341) B2286341
theorem B2343437 : Blo 694316 2343437 := bstep (se 3 (by rfl) ⟨439394, by rfl⟩ : syracuseStep 2343437 = 878789) B878789
theorem B2966051 : Blo 694316 2966051 := bstep (se 1 (by rfl) ⟨2224538, by rfl⟩ : syracuseStep 2966051 = 4449077) B4449077
theorem B2540081 : Blo 694316 2540081 := bstep (se 2 (by rfl) ⟨952530, by rfl⟩ : syracuseStep 2540081 = 1905061) B1905061
theorem B2343491 : Blo 694316 2343491 := bstep (se 1 (by rfl) ⟨1757618, by rfl⟩ : syracuseStep 2343491 = 3515237) B3515237
theorem B2343761 : Blo 694316 2343761 := bstep (se 2 (by rfl) ⟨878910, by rfl⟩ : syracuseStep 2343761 = 1757821) B1757821
theorem B2114545 : Blo 694316 2114545 := bstep (se 2 (by rfl) ⟨792954, by rfl⟩ : syracuseStep 2114545 = 1585909) B1585909
theorem B1983473 : Blo 694316 1983473 := bstep (se 2 (by rfl) ⟨743802, by rfl⟩ : syracuseStep 1983473 = 1487605) B1487605
theorem B3523661 : Blo 694316 3523661 := bstep (se 3 (by rfl) ⟨660686, by rfl⟩ : syracuseStep 3523661 = 1321373) B1321373
theorem B4244557 : Blo 694316 4244557 := bstep (se 3 (by rfl) ⟨795854, by rfl⟩ : syracuseStep 4244557 = 1591709) B1591709
theorem B2344301 : Blo 694316 2344301 := bstep (se 3 (by rfl) ⟨439556, by rfl⟩ : syracuseStep 2344301 = 879113) B879113
theorem B2344355 : Blo 694316 2344355 := bstep (se 1 (by rfl) ⟨1758266, by rfl⟩ : syracuseStep 2344355 = 3516533) B3516533
theorem B4244899 : Blo 694316 4244899 := bstep (se 1 (by rfl) ⟨3183674, by rfl⟩ : syracuseStep 4244899 = 6367349) B6367349
theorem B2344625 : Blo 694316 2344625 := bstep (se 2 (by rfl) ⟨879234, by rfl⟩ : syracuseStep 2344625 = 1758469) B1758469
theorem B2639587 : Blo 694316 2639587 := bstep (se 1 (by rfl) ⟨1979690, by rfl⟩ : syracuseStep 2639587 = 3959381) B3959381
theorem B2377603 : Blo 694316 2377603 := bstep (se 1 (by rfl) ⟨1783202, by rfl⟩ : syracuseStep 2377603 = 3566405) B3566405
theorem B1984429 : Blo 694316 1984429 := bstep (se 3 (by rfl) ⟨372080, by rfl⟩ : syracuseStep 1984429 = 744161) B744161
theorem B1886339 : Blo 694316 1886339 := bstep (se 1 (by rfl) ⟨1414754, by rfl⟩ : syracuseStep 1886339 = 2829509) B2829509
theorem B1984657 : Blo 694316 1984657 := bstep (se 2 (by rfl) ⟨744246, by rfl⟩ : syracuseStep 1984657 = 1488493) B1488493
theorem B2345165 : Blo 694316 2345165 := bstep (se 3 (by rfl) ⟨439718, by rfl⟩ : syracuseStep 2345165 = 879437) B879437
theorem B2345219 : Blo 694316 2345219 := bstep (se 1 (by rfl) ⟨1758914, by rfl⟩ : syracuseStep 2345219 = 3517829) B3517829
theorem B2115857 : Blo 694316 2115857 := bstep (se 2 (by rfl) ⟨793446, by rfl⟩ : syracuseStep 2115857 = 1586893) B1586893
theorem B1984817 : Blo 694316 1984817 := bstep (se 2 (by rfl) ⟨744306, by rfl⟩ : syracuseStep 1984817 = 1488613) B1488613
theorem B2116003 : Blo 694316 2116003 := bstep (se 1 (by rfl) ⟨1587002, by rfl⟩ : syracuseStep 2116003 = 3174005) B3174005
theorem B1984931 : Blo 694316 1984931 := bstep (se 1 (by rfl) ⟨1488698, by rfl⟩ : syracuseStep 1984931 = 2977397) B2977397
theorem B2345489 : Blo 694316 2345489 := bstep (se 2 (by rfl) ⟨879558, by rfl⟩ : syracuseStep 2345489 = 1759117) B1759117
theorem B5360197 : Blo 694316 5360197 := bstep (se 4 (by rfl) ⟨502518, by rfl⟩ : syracuseStep 5360197 = 1005037) B1005037
theorem B1886989 : Blo 694316 1886989 := bstep (se 3 (by rfl) ⟨353810, by rfl⟩ : syracuseStep 1886989 = 707621) B707621
theorem B2346029 : Blo 694316 2346029 := bstep (se 3 (by rfl) ⟨439880, by rfl⟩ : syracuseStep 2346029 = 879761) B879761
theorem B2346083 : Blo 694316 2346083 := bstep (se 1 (by rfl) ⟨1759562, by rfl⟩ : syracuseStep 2346083 = 3519125) B3519125
theorem B5786765 : Blo 694316 5786765 := bstep (se 3 (by rfl) ⟨1085018, by rfl⟩ : syracuseStep 5786765 = 2170037) B2170037
theorem B5950691 : Blo 694316 5950691 := bstep (se 1 (by rfl) ⟨4463018, by rfl⟩ : syracuseStep 5950691 = 8926037) B8926037
theorem B838883 : Blo 694316 838883 := bstep (se 1 (by rfl) ⟨629162, by rfl⟩ : syracuseStep 838883 = 1258325) B1258325
theorem B8473841 : Blo 694316 8473841 := bstep (se 2 (by rfl) ⟨3177690, by rfl⟩ : syracuseStep 8473841 = 6355381) B6355381
theorem B6016369 : Blo 694316 6016369 := bstep (se 2 (by rfl) ⟨2256138, by rfl⟩ : syracuseStep 6016369 = 4512277) B4512277
theorem B2346353 : Blo 694316 2346353 := bstep (se 2 (by rfl) ⟨879882, by rfl⟩ : syracuseStep 2346353 = 1759765) B1759765
theorem B1985933 : Blo 694316 1985933 := bstep (se 3 (by rfl) ⟨372362, by rfl⟩ : syracuseStep 1985933 = 744725) B744725
theorem B9063821 : Blo 694316 9063821 := bstep (se 3 (by rfl) ⟨1699466, by rfl⟩ : syracuseStep 9063821 = 3398933) B3398933
theorem B2379217 : Blo 694316 2379217 := bstep (se 2 (by rfl) ⟨892206, by rfl⟩ : syracuseStep 2379217 = 1784413) B1784413
theorem B1986115 : Blo 694316 1986115 := bstep (se 1 (by rfl) ⟨1489586, by rfl⟩ : syracuseStep 1986115 = 2979173) B2979173
theorem B1986275 : Blo 694316 1986275 := bstep (se 1 (by rfl) ⟨1489706, by rfl⟩ : syracuseStep 1986275 = 2979413) B2979413
theorem B3264241 : Blo 694316 3264241 := bstep (se 2 (by rfl) ⟨1224090, by rfl⟩ : syracuseStep 3264241 = 2448181) B2448181
theorem B5426957 : Blo 694316 5426957 := bstep (se 3 (by rfl) ⟨1017554, by rfl⟩ : syracuseStep 5426957 = 2035109) B2035109
theorem B3821347 : Blo 694316 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B5295941 : Blo 694316 5295941 := bstep (se 4 (by rfl) ⟨496494, by rfl⟩ : syracuseStep 5295941 = 992989) B992989
theorem B2346893 : Blo 694316 2346893 := bstep (se 3 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 2346893 = 880085) B880085
theorem B2641805 : Blo 694316 2641805 := bstep (se 3 (by rfl) ⟨495338, by rfl⟩ : syracuseStep 2641805 = 990677) B990677
theorem B3526577 : Blo 694316 3526577 := bstep (se 2 (by rfl) ⟨1322466, by rfl⟩ : syracuseStep 3526577 = 2644933) B2644933
theorem B2346947 : Blo 694316 2346947 := bstep (se 1 (by rfl) ⟨1760210, by rfl⟩ : syracuseStep 2346947 = 3520421) B3520421
theorem B2347217 : Blo 694316 2347217 := bstep (se 2 (by rfl) ⟨880206, by rfl⟩ : syracuseStep 2347217 = 1760413) B1760413
theorem B938467 : Blo 694316 938467 := bstep (se 1 (by rfl) ⟨703850, by rfl⟩ : syracuseStep 938467 = 1407701) B1407701
theorem B2970083 : Blo 694316 2970083 := bstep (se 1 (by rfl) ⟨2227562, by rfl⟩ : syracuseStep 2970083 = 4455125) B4455125
theorem B742051 : Blo 694316 742051 := bstep (se 1 (by rfl) ⟨556538, by rfl⟩ : syracuseStep 742051 = 1113077) B1113077
theorem B2347757 : Blo 694316 2347757 := bstep (se 3 (by rfl) ⟨440204, by rfl⟩ : syracuseStep 2347757 = 880409) B880409
theorem B1987345 : Blo 694316 1987345 := bstep (se 2 (by rfl) ⟨745254, by rfl⟩ : syracuseStep 1987345 = 1490509) B1490509
theorem B2347811 : Blo 694316 2347811 := bstep (se 1 (by rfl) ⟨1760858, by rfl⟩ : syracuseStep 2347811 = 3521717) B3521717
theorem B4641677 : Blo 694316 4641677 := bstep (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) B1740629
theorem B6706061 : Blo 694316 6706061 := bstep (se 3 (by rfl) ⟨1257386, by rfl⟩ : syracuseStep 6706061 = 2514773) B2514773
theorem B1758257 : Blo 694316 1758257 := bstep (se 2 (by rfl) ⟨659346, by rfl⟩ : syracuseStep 1758257 = 1318693) B1318693
theorem B2348081 : Blo 694316 2348081 := bstep (se 2 (by rfl) ⟨880530, by rfl⟩ : syracuseStep 2348081 = 1761061) B1761061
theorem B742483 : Blo 694316 742483 := bstep (se 1 (by rfl) ⟨556862, by rfl⟩ : syracuseStep 742483 = 1113725) B1113725
theorem B1758307 : Blo 694316 1758307 := bstep (se 1 (by rfl) ⟨1318730, by rfl⟩ : syracuseStep 1758307 = 2637461) B2637461
theorem B1758449 : Blo 694316 1758449 := bstep (se 2 (by rfl) ⟨659418, by rfl⟩ : syracuseStep 1758449 = 1318837) B1318837
theorem B3528035 : Blo 694316 3528035 := bstep (se 1 (by rfl) ⟨2646026, by rfl⟩ : syracuseStep 3528035 = 5292053) B5292053
theorem B939505 : Blo 694316 939505 := bstep (se 2 (by rfl) ⟨352314, by rfl⟩ : syracuseStep 939505 = 704629) B704629
theorem B2348621 : Blo 694316 2348621 := bstep (se 3 (by rfl) ⟨440366, by rfl⟩ : syracuseStep 2348621 = 880733) B880733
theorem B2348675 : Blo 694316 2348675 := bstep (se 1 (by rfl) ⟨1761506, by rfl⟩ : syracuseStep 2348675 = 3523013) B3523013
theorem B2971313 : Blo 694316 2971313 := bstep (se 2 (by rfl) ⟨1114242, by rfl⟩ : syracuseStep 2971313 = 2228485) B2228485
theorem B1562417 : Blo 694316 1562417 := bstep (se 2 (by rfl) ⟨585906, by rfl⟩ : syracuseStep 1562417 = 1171813) B1171813
theorem B1562435 : Blo 694316 1562435 := bstep (se 1 (by rfl) ⟨1171826, by rfl⟩ : syracuseStep 1562435 = 2343653) B2343653
theorem B2348945 : Blo 694316 2348945 := bstep (se 2 (by rfl) ⟨880854, by rfl⟩ : syracuseStep 2348945 = 1761709) B1761709
theorem B1562705 : Blo 694316 1562705 := bstep (se 2 (by rfl) ⟨586014, by rfl⟩ : syracuseStep 1562705 = 1172029) B1172029
theorem B1562723 : Blo 694316 1562723 := bstep (se 1 (by rfl) ⟨1172042, by rfl⟩ : syracuseStep 1562723 = 2344085) B2344085
theorem B3528845 : Blo 694316 3528845 := bstep (se 3 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 3528845 = 1323317) B1323317
theorem B1759441 : Blo 694316 1759441 := bstep (se 2 (by rfl) ⟨659790, by rfl⟩ : syracuseStep 1759441 = 1319581) B1319581
theorem B743747 : Blo 694316 743747 := bstep (se 1 (by rfl) ⟨557810, by rfl⟩ : syracuseStep 743747 = 1115621) B1115621
theorem B1562993 : Blo 694316 1562993 := bstep (se 2 (by rfl) ⟨586122, by rfl⟩ : syracuseStep 1562993 = 1172245) B1172245
theorem B1563011 : Blo 694316 1563011 := bstep (se 1 (by rfl) ⟨1172258, by rfl⟩ : syracuseStep 1563011 = 2344517) B2344517
theorem B2349485 : Blo 694316 2349485 := bstep (se 3 (by rfl) ⟨440528, by rfl⟩ : syracuseStep 2349485 = 881057) B881057
theorem B2120113 : Blo 694316 2120113 := bstep (se 2 (by rfl) ⟨795042, by rfl⟩ : syracuseStep 2120113 = 1590085) B1590085
theorem B1759715 : Blo 694316 1759715 := bstep (se 1 (by rfl) ⟨1319786, by rfl⟩ : syracuseStep 1759715 = 2639573) B2639573
theorem B2349539 : Blo 694316 2349539 := bstep (se 1 (by rfl) ⟨1762154, by rfl⟩ : syracuseStep 2349539 = 3524309) B3524309
theorem B3758669 : Blo 694316 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B1563281 : Blo 694316 1563281 := bstep (se 2 (by rfl) ⟨586230, by rfl⟩ : syracuseStep 1563281 = 1172461) B1172461
theorem B1563299 : Blo 694316 1563299 := bstep (se 1 (by rfl) ⟨1172474, by rfl⟩ : syracuseStep 1563299 = 2344949) B2344949
theorem B1759907 : Blo 694316 1759907 := bstep (se 1 (by rfl) ⟨1319930, by rfl⟩ : syracuseStep 1759907 = 2639861) B2639861
theorem B2349809 : Blo 694316 2349809 := bstep (se 2 (by rfl) ⟨881178, by rfl⟩ : syracuseStep 2349809 = 1762357) B1762357
theorem B2644721 : Blo 694316 2644721 := bstep (se 2 (by rfl) ⟨991770, by rfl⟩ : syracuseStep 2644721 = 1983541) B1983541
theorem B940835 : Blo 694316 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B1563569 : Blo 694316 1563569 := bstep (se 2 (by rfl) ⟨586338, by rfl⟩ : syracuseStep 1563569 = 1172677) B1172677
theorem B1563587 : Blo 694316 1563587 := bstep (se 1 (by rfl) ⟨1172690, by rfl⟩ : syracuseStep 1563587 = 2345381) B2345381
theorem B744499 : Blo 694316 744499 := bstep (se 1 (by rfl) ⟨558374, by rfl⟩ : syracuseStep 744499 = 1116749) B1116749
theorem B1563857 : Blo 694316 1563857 := bstep (se 2 (by rfl) ⟨586446, by rfl⟩ : syracuseStep 1563857 = 1172893) B1172893
theorem B941267 : Blo 694316 941267 := bstep (se 1 (by rfl) ⟨705950, by rfl⟩ : syracuseStep 941267 = 1411901) B1411901
theorem B1563875 : Blo 694316 1563875 := bstep (se 1 (by rfl) ⟨1172906, by rfl⟩ : syracuseStep 1563875 = 2345813) B2345813
theorem B2350349 : Blo 694316 2350349 := bstep (se 3 (by rfl) ⟨440690, by rfl⟩ : syracuseStep 2350349 = 881381) B881381
theorem B2350403 : Blo 694316 2350403 := bstep (se 1 (by rfl) ⟨1762802, by rfl⟩ : syracuseStep 2350403 = 3525605) B3525605
theorem B3562957 : Blo 694316 3562957 := bstep (se 3 (by rfl) ⟨668054, by rfl⟩ : syracuseStep 3562957 = 1336109) B1336109
theorem B1564145 : Blo 694316 1564145 := bstep (se 2 (by rfl) ⟨586554, by rfl⟩ : syracuseStep 1564145 = 1173109) B1173109
theorem B1564163 : Blo 694316 1564163 := bstep (se 1 (by rfl) ⟨1173122, by rfl⟩ : syracuseStep 1564163 = 2346245) B2346245
theorem B1760849 : Blo 694316 1760849 := bstep (se 2 (by rfl) ⟨660318, by rfl⟩ : syracuseStep 1760849 = 1320637) B1320637
theorem B2350673 : Blo 694316 2350673 := bstep (se 2 (by rfl) ⟨881502, by rfl⟩ : syracuseStep 2350673 = 1763005) B1763005
theorem B1760899 : Blo 694316 1760899 := bstep (se 1 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 1760899 = 2641349) B2641349
theorem B3169955 : Blo 694316 3169955 := bstep (se 1 (by rfl) ⟨2377466, by rfl⟩ : syracuseStep 3169955 = 4754933) B4754933
theorem B3956465 : Blo 694316 3956465 := bstep (se 2 (by rfl) ⟨1483674, by rfl⟩ : syracuseStep 3956465 = 2967349) B2967349
theorem B1564433 : Blo 694316 1564433 := bstep (se 2 (by rfl) ⟨586662, by rfl⟩ : syracuseStep 1564433 = 1173325) B1173325
theorem B1761041 : Blo 694316 1761041 := bstep (se 2 (by rfl) ⟨660390, by rfl⟩ : syracuseStep 1761041 = 1320781) B1320781
theorem B1564451 : Blo 694316 1564451 := bstep (se 1 (by rfl) ⟨1173338, by rfl⟩ : syracuseStep 1564451 = 2346677) B2346677
theorem B2383789 : Blo 694316 2383789 := bstep (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) B893921
theorem B3170353 : Blo 694316 3170353 := bstep (se 2 (by rfl) ⟨1188882, by rfl⟩ : syracuseStep 3170353 = 2377765) B2377765
theorem B1564721 : Blo 694316 1564721 := bstep (se 2 (by rfl) ⟨586770, by rfl⟩ : syracuseStep 1564721 = 1173541) B1173541
theorem B1564739 : Blo 694316 1564739 := bstep (se 1 (by rfl) ⟨1173554, by rfl⟩ : syracuseStep 1564739 = 2347109) B2347109
theorem B2973773 : Blo 694316 2973773 := bstep (se 3 (by rfl) ⟨557582, by rfl⟩ : syracuseStep 2973773 = 1115165) B1115165
theorem B745571 : Blo 694316 745571 := bstep (se 1 (by rfl) ⟨559178, by rfl⟩ : syracuseStep 745571 = 1118357) B1118357
theorem B2351213 : Blo 694316 2351213 := bstep (se 3 (by rfl) ⟨440852, by rfl⟩ : syracuseStep 2351213 = 881705) B881705
theorem B2351267 : Blo 694316 2351267 := bstep (se 1 (by rfl) ⟨1763450, by rfl⟩ : syracuseStep 2351267 = 3526901) B3526901
theorem B2646179 : Blo 694316 2646179 := bstep (se 1 (by rfl) ⟨1984634, by rfl⟩ : syracuseStep 2646179 = 3969269) B3969269
theorem B1695953 : Blo 694316 1695953 := bstep (se 2 (by rfl) ⟨635982, by rfl⟩ : syracuseStep 1695953 = 1271965) B1271965
theorem B1171793 : Blo 694316 1171793 := bstep (se 2 (by rfl) ⟨439422, by rfl⟩ : syracuseStep 1171793 = 878845) B878845
theorem B1565009 : Blo 694316 1565009 := bstep (se 2 (by rfl) ⟨586878, by rfl⟩ : syracuseStep 1565009 = 1173757) B1173757
theorem B1565027 : Blo 694316 1565027 := bstep (se 1 (by rfl) ⟨1173770, by rfl⟩ : syracuseStep 1565027 = 2347541) B2347541
theorem B3563939 : Blo 694316 3563939 := bstep (se 1 (by rfl) ⟨2672954, by rfl⟩ : syracuseStep 3563939 = 5345909) B5345909
theorem B2351537 : Blo 694316 2351537 := bstep (se 2 (by rfl) ⟨881826, by rfl⟩ : syracuseStep 2351537 = 1763653) B1763653
theorem B1171921 : Blo 694316 1171921 := bstep (se 2 (by rfl) ⟨439470, by rfl⟩ : syracuseStep 1171921 = 878941) B878941
theorem B1171955 : Blo 694316 1171955 := bstep (se 1 (by rfl) ⟨878966, by rfl⟩ : syracuseStep 1171955 = 1757933) B1757933
theorem B1565297 : Blo 694316 1565297 := bstep (se 2 (by rfl) ⟨586986, by rfl⟩ : syracuseStep 1565297 = 1173973) B1173973
theorem B1172083 : Blo 694316 1172083 := bstep (se 1 (by rfl) ⟨879062, by rfl⟩ : syracuseStep 1172083 = 1758125) B1758125
theorem B1565315 : Blo 694316 1565315 := bstep (se 1 (by rfl) ⟨1173986, by rfl⟩ : syracuseStep 1565315 = 2347973) B2347973
theorem B1762033 : Blo 694316 1762033 := bstep (se 2 (by rfl) ⟨660762, by rfl⟩ : syracuseStep 1762033 = 1321525) B1321525
theorem B1172225 : Blo 694316 1172225 := bstep (se 2 (by rfl) ⟨439584, by rfl⟩ : syracuseStep 1172225 = 879169) B879169
theorem B1172353 : Blo 694316 1172353 := bstep (se 2 (by rfl) ⟨439632, by rfl⟩ : syracuseStep 1172353 = 879265) B879265
theorem B1565585 : Blo 694316 1565585 := bstep (se 2 (by rfl) ⟨587094, by rfl⟩ : syracuseStep 1565585 = 1174189) B1174189
theorem B1172387 : Blo 694316 1172387 := bstep (se 1 (by rfl) ⟨879290, by rfl⟩ : syracuseStep 1172387 = 1758581) B1758581
theorem B1565603 : Blo 694316 1565603 := bstep (se 1 (by rfl) ⟨1174202, by rfl⟩ : syracuseStep 1565603 = 2348405) B2348405
theorem B2352077 : Blo 694316 2352077 := bstep (se 3 (by rfl) ⟨441014, by rfl⟩ : syracuseStep 2352077 = 882029) B882029
theorem B3531761 : Blo 694316 3531761 := bstep (se 2 (by rfl) ⟨1324410, by rfl⟩ : syracuseStep 3531761 = 2648821) B2648821
theorem B1762307 : Blo 694316 1762307 := bstep (se 1 (by rfl) ⟨1321730, by rfl⟩ : syracuseStep 1762307 = 2643461) B2643461
theorem B2352131 : Blo 694316 2352131 := bstep (se 1 (by rfl) ⟨1764098, by rfl⟩ : syracuseStep 2352131 = 3528197) B3528197
theorem B1172515 : Blo 694316 1172515 := bstep (se 1 (by rfl) ⟨879386, by rfl⟩ : syracuseStep 1172515 = 1758773) B1758773
theorem B1041491 : Blo 694316 1041491 := bstep (se 1 (by rfl) ⟨781118, by rfl⟩ : syracuseStep 1041491 = 1562237) B1562237
theorem B1041521 : Blo 694316 1041521 := bstep (se 2 (by rfl) ⟨390570, by rfl⟩ : syracuseStep 1041521 = 781141) B781141
theorem B1041539 : Blo 694316 1041539 := bstep (se 1 (by rfl) ⟨781154, by rfl⟩ : syracuseStep 1041539 = 1562309) B1562309
theorem B2647181 : Blo 694316 2647181 := bstep (se 3 (by rfl) ⟨496346, by rfl⟩ : syracuseStep 2647181 = 992693) B992693
theorem B1041569 : Blo 694316 1041569 := bstep (se 2 (by rfl) ⟨390588, by rfl⟩ : syracuseStep 1041569 = 781177) B781177
theorem B3957923 : Blo 694316 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B1172657 : Blo 694316 1172657 := bstep (se 2 (by rfl) ⟨439746, by rfl⟩ : syracuseStep 1172657 = 879493) B879493
theorem B1565873 : Blo 694316 1565873 := bstep (se 2 (by rfl) ⟨587202, by rfl⟩ : syracuseStep 1565873 = 1174405) B1174405
theorem B1041587 : Blo 694316 1041587 := bstep (se 1 (by rfl) ⟨781190, by rfl⟩ : syracuseStep 1041587 = 1562381) B1562381
theorem B1565891 : Blo 694316 1565891 := bstep (se 1 (by rfl) ⟨1174418, by rfl⟩ : syracuseStep 1565891 = 2348837) B2348837
theorem B1762499 : Blo 694316 1762499 := bstep (se 1 (by rfl) ⟨1321874, by rfl⟩ : syracuseStep 1762499 = 2643749) B2643749
theorem B1041617 : Blo 694316 1041617 := bstep (se 2 (by rfl) ⟨390606, by rfl⟩ : syracuseStep 1041617 = 781213) B781213
theorem B36660437 : Blo 694316 36660437 := bstep (se 7 (by rfl) ⟨429614, by rfl⟩ : syracuseStep 36660437 = 859229) B859229
theorem B1041635 : Blo 694316 1041635 := bstep (se 1 (by rfl) ⟨781226, by rfl⟩ : syracuseStep 1041635 = 1562453) B1562453
theorem B1041665 : Blo 694316 1041665 := bstep (se 2 (by rfl) ⟨390624, by rfl⟩ : syracuseStep 1041665 = 781249) B781249
theorem B2352401 : Blo 694316 2352401 := bstep (se 2 (by rfl) ⟨882150, by rfl⟩ : syracuseStep 2352401 = 1764301) B1764301
theorem B1041683 : Blo 694316 1041683 := bstep (se 1 (by rfl) ⟨781262, by rfl⟩ : syracuseStep 1041683 = 1562525) B1562525
theorem B1041713 : Blo 694316 1041713 := bstep (se 2 (by rfl) ⟨390642, by rfl⟩ : syracuseStep 1041713 = 781285) B781285
theorem B1172785 : Blo 694316 1172785 := bstep (se 2 (by rfl) ⟨439794, by rfl⟩ : syracuseStep 1172785 = 879589) B879589
theorem B1041731 : Blo 694316 1041731 := bstep (se 1 (by rfl) ⟨781298, by rfl⟩ : syracuseStep 1041731 = 1562597) B1562597
theorem B1172819 : Blo 694316 1172819 := bstep (se 1 (by rfl) ⟨879614, by rfl⟩ : syracuseStep 1172819 = 1759229) B1759229
theorem B1041761 : Blo 694316 1041761 := bstep (se 2 (by rfl) ⟨390660, by rfl⟩ : syracuseStep 1041761 = 781321) B781321
theorem B1041779 : Blo 694316 1041779 := bstep (se 1 (by rfl) ⟨781334, by rfl⟩ : syracuseStep 1041779 = 1562669) B1562669
theorem B1041809 : Blo 694316 1041809 := bstep (se 2 (by rfl) ⟨390678, by rfl⟩ : syracuseStep 1041809 = 781357) B781357
theorem B1041827 : Blo 694316 1041827 := bstep (se 1 (by rfl) ⟨781370, by rfl⟩ : syracuseStep 1041827 = 1562741) B1562741
theorem B1041857 : Blo 694316 1041857 := bstep (se 2 (by rfl) ⟨390696, by rfl⟩ : syracuseStep 1041857 = 781393) B781393
theorem B1566161 : Blo 694316 1566161 := bstep (se 2 (by rfl) ⟨587310, by rfl⟩ : syracuseStep 1566161 = 1174621) B1174621
theorem B1041875 : Blo 694316 1041875 := bstep (se 1 (by rfl) ⟨781406, by rfl⟩ : syracuseStep 1041875 = 1562813) B1562813
theorem B1172947 : Blo 694316 1172947 := bstep (se 1 (by rfl) ⟨879710, by rfl⟩ : syracuseStep 1172947 = 1759421) B1759421
theorem B1566179 : Blo 694316 1566179 := bstep (se 1 (by rfl) ⟨1174634, by rfl⟩ : syracuseStep 1566179 = 2349269) B2349269
theorem B1041905 : Blo 694316 1041905 := bstep (se 2 (by rfl) ⟨390714, by rfl⟩ : syracuseStep 1041905 = 781429) B781429
theorem B1041923 : Blo 694316 1041923 := bstep (se 1 (by rfl) ⟨781442, by rfl⟩ : syracuseStep 1041923 = 1562885) B1562885
theorem B5301773 : Blo 694316 5301773 := bstep (se 3 (by rfl) ⟨994082, by rfl⟩ : syracuseStep 5301773 = 1988165) B1988165
theorem B1041953 : Blo 694316 1041953 := bstep (se 2 (by rfl) ⟨390732, by rfl⟩ : syracuseStep 1041953 = 781465) B781465
theorem B1041971 : Blo 694316 1041971 := bstep (se 1 (by rfl) ⟨781478, by rfl⟩ : syracuseStep 1041971 = 1562957) B1562957
theorem B1042001 : Blo 694316 1042001 := bstep (se 2 (by rfl) ⟨390750, by rfl⟩ : syracuseStep 1042001 = 781501) B781501
theorem B1173089 : Blo 694316 1173089 := bstep (se 2 (by rfl) ⟨439908, by rfl⟩ : syracuseStep 1173089 = 879817) B879817
theorem B1042019 : Blo 694316 1042019 := bstep (se 1 (by rfl) ⟨781514, by rfl⟩ : syracuseStep 1042019 = 1563029) B1563029
theorem B1042049 : Blo 694316 1042049 := bstep (se 2 (by rfl) ⟨390768, by rfl⟩ : syracuseStep 1042049 = 781537) B781537
theorem B2385539 : Blo 694316 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B1042067 : Blo 694316 1042067 := bstep (se 1 (by rfl) ⟨781550, by rfl⟩ : syracuseStep 1042067 = 1563101) B1563101
theorem B1042097 : Blo 694316 1042097 := bstep (se 2 (by rfl) ⟨390786, by rfl⟩ : syracuseStep 1042097 = 781573) B781573
theorem B1042115 : Blo 694316 1042115 := bstep (se 1 (by rfl) ⟨781586, by rfl⟩ : syracuseStep 1042115 = 1563173) B1563173
theorem B1042145 : Blo 694316 1042145 := bstep (se 2 (by rfl) ⟨390804, by rfl⟩ : syracuseStep 1042145 = 781609) B781609
theorem B1173217 : Blo 694316 1173217 := bstep (se 2 (by rfl) ⟨439956, by rfl⟩ : syracuseStep 1173217 = 879913) B879913
theorem B1566449 : Blo 694316 1566449 := bstep (se 2 (by rfl) ⟨587418, by rfl⟩ : syracuseStep 1566449 = 1174837) B1174837
theorem B1042163 : Blo 694316 1042163 := bstep (se 1 (by rfl) ⟨781622, by rfl⟩ : syracuseStep 1042163 = 1563245) B1563245
theorem B1173251 : Blo 694316 1173251 := bstep (se 1 (by rfl) ⟨879938, by rfl⟩ : syracuseStep 1173251 = 1759877) B1759877
theorem B1566467 : Blo 694316 1566467 := bstep (se 1 (by rfl) ⟨1174850, by rfl⟩ : syracuseStep 1566467 = 2349701) B2349701
theorem B1042193 : Blo 694316 1042193 := bstep (se 2 (by rfl) ⟨390822, by rfl⟩ : syracuseStep 1042193 = 781645) B781645
theorem B714515 : Blo 694316 714515 := bstep (se 1 (by rfl) ⟨535886, by rfl⟩ : syracuseStep 714515 = 1071773) B1071773
theorem B1042211 : Blo 694316 1042211 := bstep (se 1 (by rfl) ⟨781658, by rfl⟩ : syracuseStep 1042211 = 1563317) B1563317
theorem B2352941 : Blo 694316 2352941 := bstep (se 3 (by rfl) ⟨441176, by rfl⟩ : syracuseStep 2352941 = 882353) B882353
theorem B1042241 : Blo 694316 1042241 := bstep (se 2 (by rfl) ⟨390840, by rfl⟩ : syracuseStep 1042241 = 781681) B781681
theorem B1042259 : Blo 694316 1042259 := bstep (se 1 (by rfl) ⟨781694, by rfl⟩ : syracuseStep 1042259 = 1563389) B1563389
theorem B2352995 : Blo 694316 2352995 := bstep (se 1 (by rfl) ⟨1764746, by rfl⟩ : syracuseStep 2352995 = 3529493) B3529493
theorem B1042289 : Blo 694316 1042289 := bstep (se 2 (by rfl) ⟨390858, by rfl⟩ : syracuseStep 1042289 = 781717) B781717
theorem B1042307 : Blo 694316 1042307 := bstep (se 1 (by rfl) ⟨781730, by rfl⟩ : syracuseStep 1042307 = 1563461) B1563461
theorem B1173379 : Blo 694316 1173379 := bstep (se 1 (by rfl) ⟨880034, by rfl⟩ : syracuseStep 1173379 = 1760069) B1760069
theorem B1042337 : Blo 694316 1042337 := bstep (se 2 (by rfl) ⟨390876, by rfl⟩ : syracuseStep 1042337 = 781753) B781753
theorem B1042355 : Blo 694316 1042355 := bstep (se 1 (by rfl) ⟨781766, by rfl⟩ : syracuseStep 1042355 = 1563533) B1563533
theorem B1042385 : Blo 694316 1042385 := bstep (se 2 (by rfl) ⟨390894, by rfl⟩ : syracuseStep 1042385 = 781789) B781789
theorem B1042403 : Blo 694316 1042403 := bstep (se 1 (by rfl) ⟨781802, by rfl⟩ : syracuseStep 1042403 = 1563605) B1563605
theorem B1042433 : Blo 694316 1042433 := bstep (se 2 (by rfl) ⟨390912, by rfl⟩ : syracuseStep 1042433 = 781825) B781825
theorem B1173521 : Blo 694316 1173521 := bstep (se 2 (by rfl) ⟨440070, by rfl⟩ : syracuseStep 1173521 = 880141) B880141
theorem B1566737 : Blo 694316 1566737 := bstep (se 2 (by rfl) ⟨587526, by rfl⟩ : syracuseStep 1566737 = 1175053) B1175053
theorem B1042451 : Blo 694316 1042451 := bstep (se 1 (by rfl) ⟨781838, by rfl⟩ : syracuseStep 1042451 = 1563677) B1563677
theorem B1566755 : Blo 694316 1566755 := bstep (se 1 (by rfl) ⟨1175066, by rfl⟩ : syracuseStep 1566755 = 2350133) B2350133
theorem B1042481 : Blo 694316 1042481 := bstep (se 2 (by rfl) ⟨390930, by rfl⟩ : syracuseStep 1042481 = 781861) B781861
theorem B1042499 : Blo 694316 1042499 := bstep (se 1 (by rfl) ⟨781874, by rfl⟩ : syracuseStep 1042499 = 1563749) B1563749
theorem B1042529 : Blo 694316 1042529 := bstep (se 2 (by rfl) ⟨390948, by rfl⟩ : syracuseStep 1042529 = 781897) B781897
theorem B1763441 : Blo 694316 1763441 := bstep (se 2 (by rfl) ⟨661290, by rfl⟩ : syracuseStep 1763441 = 1322581) B1322581
theorem B2353265 : Blo 694316 2353265 := bstep (se 2 (by rfl) ⟨882474, by rfl⟩ : syracuseStep 2353265 = 1764949) B1764949
theorem B1042547 : Blo 694316 1042547 := bstep (se 1 (by rfl) ⟨781910, by rfl⟩ : syracuseStep 1042547 = 1563821) B1563821
theorem B1042577 : Blo 694316 1042577 := bstep (se 2 (by rfl) ⟨390966, by rfl⟩ : syracuseStep 1042577 = 781933) B781933
theorem B1173649 : Blo 694316 1173649 := bstep (se 2 (by rfl) ⟨440118, by rfl⟩ : syracuseStep 1173649 = 880237) B880237
theorem B1042595 : Blo 694316 1042595 := bstep (se 1 (by rfl) ⟨781946, by rfl⟩ : syracuseStep 1042595 = 1563893) B1563893
theorem B1763491 : Blo 694316 1763491 := bstep (se 1 (by rfl) ⟨1322618, by rfl⟩ : syracuseStep 1763491 = 2645237) B2645237
theorem B1173683 : Blo 694316 1173683 := bstep (se 1 (by rfl) ⟨880262, by rfl⟩ : syracuseStep 1173683 = 1760525) B1760525
theorem B1042625 : Blo 694316 1042625 := bstep (se 2 (by rfl) ⟨390984, by rfl⟩ : syracuseStep 1042625 = 781969) B781969
theorem B1042643 : Blo 694316 1042643 := bstep (se 1 (by rfl) ⟨781982, by rfl⟩ : syracuseStep 1042643 = 1563965) B1563965
theorem B1861859 : Blo 694316 1861859 := bstep (se 1 (by rfl) ⟨1396394, by rfl⟩ : syracuseStep 1861859 = 2792789) B2792789
theorem B1042673 : Blo 694316 1042673 := bstep (se 2 (by rfl) ⟨391002, by rfl⟩ : syracuseStep 1042673 = 782005) B782005
theorem B1042691 : Blo 694316 1042691 := bstep (se 1 (by rfl) ⟨782018, by rfl⟩ : syracuseStep 1042691 = 1564037) B1564037
theorem B1042721 : Blo 694316 1042721 := bstep (se 2 (by rfl) ⟨391020, by rfl⟩ : syracuseStep 1042721 = 782041) B782041
theorem B1567025 : Blo 694316 1567025 := bstep (se 2 (by rfl) ⟨587634, by rfl⟩ : syracuseStep 1567025 = 1175269) B1175269
theorem B1763633 : Blo 694316 1763633 := bstep (se 2 (by rfl) ⟨661362, by rfl⟩ : syracuseStep 1763633 = 1322725) B1322725
theorem B1042739 : Blo 694316 1042739 := bstep (se 1 (by rfl) ⟨782054, by rfl⟩ : syracuseStep 1042739 = 1564109) B1564109
theorem B1173811 : Blo 694316 1173811 := bstep (se 1 (by rfl) ⟨880358, by rfl⟩ : syracuseStep 1173811 = 1760717) B1760717
theorem B1567043 : Blo 694316 1567043 := bstep (se 1 (by rfl) ⟨1175282, by rfl⟩ : syracuseStep 1567043 = 2350565) B2350565
theorem B1042769 : Blo 694316 1042769 := bstep (se 2 (by rfl) ⟨391038, by rfl⟩ : syracuseStep 1042769 = 782077) B782077
theorem B1042787 : Blo 694316 1042787 := bstep (se 1 (by rfl) ⟨782090, by rfl⟩ : syracuseStep 1042787 = 1564181) B1564181
theorem B1042817 : Blo 694316 1042817 := bstep (se 2 (by rfl) ⟨391056, by rfl⟩ : syracuseStep 1042817 = 782113) B782113
theorem B1042835 : Blo 694316 1042835 := bstep (se 1 (by rfl) ⟨782126, by rfl⟩ : syracuseStep 1042835 = 1564253) B1564253
theorem B3533219 : Blo 694316 3533219 := bstep (se 1 (by rfl) ⟨2649914, by rfl⟩ : syracuseStep 3533219 = 5299829) B5299829
theorem B1042865 : Blo 694316 1042865 := bstep (se 2 (by rfl) ⟨391074, by rfl⟩ : syracuseStep 1042865 = 782149) B782149
theorem B1173953 : Blo 694316 1173953 := bstep (se 2 (by rfl) ⟨440232, by rfl⟩ : syracuseStep 1173953 = 880465) B880465
theorem B1042883 : Blo 694316 1042883 := bstep (se 1 (by rfl) ⟨782162, by rfl⟩ : syracuseStep 1042883 = 1564325) B1564325
theorem B1468867 : Blo 694316 1468867 := bstep (se 1 (by rfl) ⟨1101650, by rfl⟩ : syracuseStep 1468867 = 2203301) B2203301
theorem B1042913 : Blo 694316 1042913 := bstep (se 2 (by rfl) ⟨391092, by rfl⟩ : syracuseStep 1042913 = 782185) B782185
theorem B1042931 : Blo 694316 1042931 := bstep (se 1 (by rfl) ⟨782198, by rfl⟩ : syracuseStep 1042931 = 1564397) B1564397
theorem B1042961 : Blo 694316 1042961 := bstep (se 2 (by rfl) ⟨391110, by rfl⟩ : syracuseStep 1042961 = 782221) B782221
theorem B1042979 : Blo 694316 1042979 := bstep (se 1 (by rfl) ⟨782234, by rfl⟩ : syracuseStep 1042979 = 1564469) B1564469
theorem B1043009 : Blo 694316 1043009 := bstep (se 2 (by rfl) ⟨391128, by rfl⟩ : syracuseStep 1043009 = 782257) B782257
theorem B1174081 : Blo 694316 1174081 := bstep (se 2 (by rfl) ⟨440280, by rfl⟩ : syracuseStep 1174081 = 880561) B880561
theorem B1567313 : Blo 694316 1567313 := bstep (se 2 (by rfl) ⟨587742, by rfl⟩ : syracuseStep 1567313 = 1175485) B1175485
theorem B2386513 : Blo 694316 2386513 := bstep (se 2 (by rfl) ⟨894942, by rfl⟩ : syracuseStep 2386513 = 1789885) B1789885
theorem B1043027 : Blo 694316 1043027 := bstep (se 1 (by rfl) ⟨782270, by rfl⟩ : syracuseStep 1043027 = 1564541) B1564541
theorem B1174115 : Blo 694316 1174115 := bstep (se 1 (by rfl) ⟨880586, by rfl⟩ : syracuseStep 1174115 = 1761173) B1761173
theorem B1567331 : Blo 694316 1567331 := bstep (se 1 (by rfl) ⟨1175498, by rfl⟩ : syracuseStep 1567331 = 2350997) B2350997
theorem B1043057 : Blo 694316 1043057 := bstep (se 2 (by rfl) ⟨391146, by rfl⟩ : syracuseStep 1043057 = 782293) B782293
theorem B1043075 : Blo 694316 1043075 := bstep (se 1 (by rfl) ⟨782306, by rfl⟩ : syracuseStep 1043075 = 1564613) B1564613
theorem B2353805 : Blo 694316 2353805 := bstep (se 3 (by rfl) ⟨441338, by rfl⟩ : syracuseStep 2353805 = 882677) B882677
theorem B1043105 : Blo 694316 1043105 := bstep (se 2 (by rfl) ⟨391164, by rfl⟩ : syracuseStep 1043105 = 782329) B782329
theorem B1043123 : Blo 694316 1043123 := bstep (se 1 (by rfl) ⟨782342, by rfl⟩ : syracuseStep 1043123 = 1564685) B1564685
theorem B2353859 : Blo 694316 2353859 := bstep (se 1 (by rfl) ⟨1765394, by rfl⟩ : syracuseStep 2353859 = 3530789) B3530789
theorem B5368517 : Blo 694316 5368517 := bstep (se 4 (by rfl) ⟨503298, by rfl⟩ : syracuseStep 5368517 = 1006597) B1006597
theorem B1043153 : Blo 694316 1043153 := bstep (se 2 (by rfl) ⟨391182, by rfl⟩ : syracuseStep 1043153 = 782365) B782365
theorem B879331 : Blo 694316 879331 := bstep (se 1 (by rfl) ⟨659498, by rfl⟩ : syracuseStep 879331 = 1318997) B1318997
theorem B1043171 : Blo 694316 1043171 := bstep (se 1 (by rfl) ⟨782378, by rfl⟩ : syracuseStep 1043171 = 1564757) B1564757
theorem B1174243 : Blo 694316 1174243 := bstep (se 1 (by rfl) ⟨880682, by rfl⟩ : syracuseStep 1174243 = 1761365) B1761365
theorem B5630705 : Blo 694316 5630705 := bstep (se 2 (by rfl) ⟨2111514, by rfl⟩ : syracuseStep 5630705 = 4223029) B4223029
theorem B1043201 : Blo 694316 1043201 := bstep (se 2 (by rfl) ⟨391200, by rfl⟩ : syracuseStep 1043201 = 782401) B782401
theorem B1043219 : Blo 694316 1043219 := bstep (se 1 (by rfl) ⟨782414, by rfl⟩ : syracuseStep 1043219 = 1564829) B1564829
theorem B1043249 : Blo 694316 1043249 := bstep (se 2 (by rfl) ⟨391218, by rfl⟩ : syracuseStep 1043249 = 782437) B782437
theorem B781123 : Blo 694316 781123 := bstep (se 1 (by rfl) ⟨585842, by rfl⟩ : syracuseStep 781123 = 1171685) B1171685
theorem B879427 : Blo 694316 879427 := bstep (se 1 (by rfl) ⟨659570, by rfl⟩ : syracuseStep 879427 = 1319141) B1319141
theorem B1043267 : Blo 694316 1043267 := bstep (se 1 (by rfl) ⟨782450, by rfl⟩ : syracuseStep 1043267 = 1564901) B1564901
theorem B1043297 : Blo 694316 1043297 := bstep (se 2 (by rfl) ⟨391236, by rfl⟩ : syracuseStep 1043297 = 782473) B782473
theorem B1174385 : Blo 694316 1174385 := bstep (se 2 (by rfl) ⟨440394, by rfl⟩ : syracuseStep 1174385 = 880789) B880789
theorem B1567601 : Blo 694316 1567601 := bstep (se 2 (by rfl) ⟨587850, by rfl⟩ : syracuseStep 1567601 = 1175701) B1175701
theorem B1043315 : Blo 694316 1043315 := bstep (se 1 (by rfl) ⟨782486, by rfl⟩ : syracuseStep 1043315 = 1564973) B1564973
theorem B1567619 : Blo 694316 1567619 := bstep (se 1 (by rfl) ⟨1175714, by rfl⟩ : syracuseStep 1567619 = 2351429) B2351429
theorem B1043345 : Blo 694316 1043345 := bstep (se 2 (by rfl) ⟨391254, by rfl⟩ : syracuseStep 1043345 = 782509) B782509
theorem B1043363 : Blo 694316 1043363 := bstep (se 1 (by rfl) ⟨782522, by rfl⟩ : syracuseStep 1043363 = 1565045) B1565045
theorem B1043393 : Blo 694316 1043393 := bstep (se 2 (by rfl) ⟨391272, by rfl⟩ : syracuseStep 1043393 = 782545) B782545
theorem B2354129 : Blo 694316 2354129 := bstep (se 2 (by rfl) ⟨882798, by rfl⟩ : syracuseStep 2354129 = 1765597) B1765597
theorem B781267 : Blo 694316 781267 := bstep (se 1 (by rfl) ⟨585950, by rfl⟩ : syracuseStep 781267 = 1171901) B1171901
theorem B1043411 : Blo 694316 1043411 := bstep (se 1 (by rfl) ⟨782558, by rfl⟩ : syracuseStep 1043411 = 1565117) B1565117
theorem B1043441 : Blo 694316 1043441 := bstep (se 2 (by rfl) ⟨391290, by rfl⟩ : syracuseStep 1043441 = 782581) B782581
theorem B1174513 : Blo 694316 1174513 := bstep (se 2 (by rfl) ⟨440442, by rfl⟩ : syracuseStep 1174513 = 880885) B880885
theorem B1043459 : Blo 694316 1043459 := bstep (se 1 (by rfl) ⟨782594, by rfl⟩ : syracuseStep 1043459 = 1565189) B1565189
theorem B1174547 : Blo 694316 1174547 := bstep (se 1 (by rfl) ⟨880910, by rfl⟩ : syracuseStep 1174547 = 1761821) B1761821
theorem B1043489 : Blo 694316 1043489 := bstep (se 2 (by rfl) ⟨391308, by rfl⟩ : syracuseStep 1043489 = 782617) B782617
theorem B1043507 : Blo 694316 1043507 := bstep (se 1 (by rfl) ⟨782630, by rfl⟩ : syracuseStep 1043507 = 1565261) B1565261
theorem B1043537 : Blo 694316 1043537 := bstep (se 2 (by rfl) ⟨391326, by rfl⟩ : syracuseStep 1043537 = 782653) B782653
theorem B781411 : Blo 694316 781411 := bstep (se 1 (by rfl) ⟨586058, by rfl⟩ : syracuseStep 781411 = 1172117) B1172117
theorem B1043555 : Blo 694316 1043555 := bstep (se 1 (by rfl) ⟨782666, by rfl⟩ : syracuseStep 1043555 = 1565333) B1565333
theorem B5958755 : Blo 694316 5958755 := bstep (se 1 (by rfl) ⟨4469066, by rfl⟩ : syracuseStep 5958755 = 8938133) B8938133
theorem B5729393 : Blo 694316 5729393 := bstep (se 2 (by rfl) ⟨2148522, by rfl⟩ : syracuseStep 5729393 = 4297045) B4297045
theorem B1043585 : Blo 694316 1043585 := bstep (se 2 (by rfl) ⟨391344, by rfl⟩ : syracuseStep 1043585 = 782689) B782689
theorem B1567889 : Blo 694316 1567889 := bstep (se 2 (by rfl) ⟨587958, by rfl⟩ : syracuseStep 1567889 = 1175917) B1175917
theorem B1043603 : Blo 694316 1043603 := bstep (se 1 (by rfl) ⟨782702, by rfl⟩ : syracuseStep 1043603 = 1565405) B1565405
theorem B1174675 : Blo 694316 1174675 := bstep (se 1 (by rfl) ⟨881006, by rfl⟩ : syracuseStep 1174675 = 1762013) B1762013
theorem B1567907 : Blo 694316 1567907 := bstep (se 1 (by rfl) ⟨1175930, by rfl⟩ : syracuseStep 1567907 = 2351861) B2351861
theorem B1043633 : Blo 694316 1043633 := bstep (se 2 (by rfl) ⟨391362, by rfl⟩ : syracuseStep 1043633 = 782725) B782725
theorem B1043651 : Blo 694316 1043651 := bstep (se 1 (by rfl) ⟨782738, by rfl⟩ : syracuseStep 1043651 = 1565477) B1565477
theorem B2649293 : Blo 694316 2649293 := bstep (se 3 (by rfl) ⟨496742, by rfl⟩ : syracuseStep 2649293 = 993485) B993485
theorem B3534029 : Blo 694316 3534029 := bstep (se 3 (by rfl) ⟨662630, by rfl⟩ : syracuseStep 3534029 = 1325261) B1325261
theorem B1043681 : Blo 694316 1043681 := bstep (se 2 (by rfl) ⟨391380, by rfl⟩ : syracuseStep 1043681 = 782761) B782761
theorem B781555 : Blo 694316 781555 := bstep (se 1 (by rfl) ⟨586166, by rfl⟩ : syracuseStep 781555 = 1172333) B1172333
theorem B1043699 : Blo 694316 1043699 := bstep (se 1 (by rfl) ⟨782774, by rfl⟩ : syracuseStep 1043699 = 1565549) B1565549
theorem B1043729 : Blo 694316 1043729 := bstep (se 2 (by rfl) ⟨391398, by rfl⟩ : syracuseStep 1043729 = 782797) B782797
theorem B1764625 : Blo 694316 1764625 := bstep (se 2 (by rfl) ⟨661734, by rfl⟩ : syracuseStep 1764625 = 1323469) B1323469
theorem B1174817 : Blo 694316 1174817 := bstep (se 2 (by rfl) ⟨440556, by rfl⟩ : syracuseStep 1174817 = 881113) B881113
theorem B1043747 : Blo 694316 1043747 := bstep (se 1 (by rfl) ⟨782810, by rfl⟩ : syracuseStep 1043747 = 1565621) B1565621
theorem B879923 : Blo 694316 879923 := bstep (se 1 (by rfl) ⟨659942, by rfl⟩ : syracuseStep 879923 = 1319885) B1319885
theorem B1043777 : Blo 694316 1043777 := bstep (se 2 (by rfl) ⟨391416, by rfl⟩ : syracuseStep 1043777 = 782833) B782833
theorem B1043795 : Blo 694316 1043795 := bstep (se 1 (by rfl) ⟨782846, by rfl⟩ : syracuseStep 1043795 = 1565693) B1565693
theorem B4025699 : Blo 694316 4025699 := bstep (se 1 (by rfl) ⟨3019274, by rfl⟩ : syracuseStep 4025699 = 6038549) B6038549
theorem B1043825 : Blo 694316 1043825 := bstep (se 2 (by rfl) ⟨391434, by rfl⟩ : syracuseStep 1043825 = 782869) B782869
theorem B781699 : Blo 694316 781699 := bstep (se 1 (by rfl) ⟨586274, by rfl⟩ : syracuseStep 781699 = 1172549) B1172549
theorem B1043843 : Blo 694316 1043843 := bstep (se 1 (by rfl) ⟨782882, by rfl⟩ : syracuseStep 1043843 = 1565765) B1565765
theorem B1043873 : Blo 694316 1043873 := bstep (se 2 (by rfl) ⟨391452, by rfl⟩ : syracuseStep 1043873 = 782905) B782905
theorem B1174945 : Blo 694316 1174945 := bstep (se 2 (by rfl) ⟨440604, by rfl⟩ : syracuseStep 1174945 = 881209) B881209
theorem B1568177 : Blo 694316 1568177 := bstep (se 2 (by rfl) ⟨588066, by rfl⟩ : syracuseStep 1568177 = 1176133) B1176133
theorem B1043891 : Blo 694316 1043891 := bstep (se 1 (by rfl) ⟨782918, by rfl⟩ : syracuseStep 1043891 = 1565837) B1565837
theorem B1174979 : Blo 694316 1174979 := bstep (se 1 (by rfl) ⟨881234, by rfl⟩ : syracuseStep 1174979 = 1762469) B1762469
theorem B1568195 : Blo 694316 1568195 := bstep (se 1 (by rfl) ⟨1176146, by rfl⟩ : syracuseStep 1568195 = 2352293) B2352293
theorem B1043921 : Blo 694316 1043921 := bstep (se 2 (by rfl) ⟨391470, by rfl⟩ : syracuseStep 1043921 = 782941) B782941
theorem B1043939 : Blo 694316 1043939 := bstep (se 1 (by rfl) ⟨782954, by rfl⟩ : syracuseStep 1043939 = 1565909) B1565909
theorem B1273315 : Blo 694316 1273315 := bstep (se 1 (by rfl) ⟨954986, by rfl⟩ : syracuseStep 1273315 = 1909973) B1909973
theorem B2354669 : Blo 694316 2354669 := bstep (se 3 (by rfl) ⟨441500, by rfl⟩ : syracuseStep 2354669 = 883001) B883001
theorem B1043969 : Blo 694316 1043969 := bstep (se 2 (by rfl) ⟨391488, by rfl⟩ : syracuseStep 1043969 = 782977) B782977
theorem B781843 : Blo 694316 781843 := bstep (se 1 (by rfl) ⟨586382, by rfl⟩ : syracuseStep 781843 = 1172765) B1172765
theorem B1043987 : Blo 694316 1043987 := bstep (se 1 (by rfl) ⟨782990, by rfl⟩ : syracuseStep 1043987 = 1565981) B1565981
theorem B1764899 : Blo 694316 1764899 := bstep (se 1 (by rfl) ⟨1323674, by rfl⟩ : syracuseStep 1764899 = 2647349) B2647349
theorem B2354723 : Blo 694316 2354723 := bstep (se 1 (by rfl) ⟨1766042, by rfl⟩ : syracuseStep 2354723 = 3532085) B3532085
theorem B1044017 : Blo 694316 1044017 := bstep (se 2 (by rfl) ⟨391506, by rfl⟩ : syracuseStep 1044017 = 783013) B783013
theorem B1044035 : Blo 694316 1044035 := bstep (se 1 (by rfl) ⟨783026, by rfl⟩ : syracuseStep 1044035 = 1566053) B1566053
theorem B1175107 : Blo 694316 1175107 := bstep (se 1 (by rfl) ⟨881330, by rfl⟩ : syracuseStep 1175107 = 1762661) B1762661
theorem B1044065 : Blo 694316 1044065 := bstep (se 2 (by rfl) ⟨391524, by rfl⟩ : syracuseStep 1044065 = 783049) B783049
theorem B3173987 : Blo 694316 3173987 := bstep (se 1 (by rfl) ⟨2380490, by rfl⟩ : syracuseStep 3173987 = 4760981) B4760981
theorem B1044083 : Blo 694316 1044083 := bstep (se 1 (by rfl) ⟨783062, by rfl⟩ : syracuseStep 1044083 = 1566125) B1566125
theorem B1044113 : Blo 694316 1044113 := bstep (se 2 (by rfl) ⟨391542, by rfl⟩ : syracuseStep 1044113 = 783085) B783085
theorem B781987 : Blo 694316 781987 := bstep (se 1 (by rfl) ⟨586490, by rfl⟩ : syracuseStep 781987 = 1172981) B1172981
theorem B1044131 : Blo 694316 1044131 := bstep (se 1 (by rfl) ⟨783098, by rfl⟩ : syracuseStep 1044131 = 1566197) B1566197
theorem B1044161 : Blo 694316 1044161 := bstep (se 2 (by rfl) ⟨391560, by rfl⟩ : syracuseStep 1044161 = 783121) B783121
theorem B1175249 : Blo 694316 1175249 := bstep (se 2 (by rfl) ⟨440718, by rfl⟩ : syracuseStep 1175249 = 881437) B881437
theorem B1568465 : Blo 694316 1568465 := bstep (se 2 (by rfl) ⟨588174, by rfl⟩ : syracuseStep 1568465 = 1176349) B1176349
theorem B1044179 : Blo 694316 1044179 := bstep (se 1 (by rfl) ⟨783134, by rfl⟩ : syracuseStep 1044179 = 1566269) B1566269
theorem B1568483 : Blo 694316 1568483 := bstep (se 1 (by rfl) ⟨1176362, by rfl⟩ : syracuseStep 1568483 = 2352725) B2352725
theorem B1765091 : Blo 694316 1765091 := bstep (se 1 (by rfl) ⟨1323818, by rfl⟩ : syracuseStep 1765091 = 2647637) B2647637
theorem B1044209 : Blo 694316 1044209 := bstep (se 2 (by rfl) ⟨391578, by rfl⟩ : syracuseStep 1044209 = 783157) B783157
theorem B1044227 : Blo 694316 1044227 := bstep (se 1 (by rfl) ⟨783170, by rfl⟩ : syracuseStep 1044227 = 1566341) B1566341
theorem B1044257 : Blo 694316 1044257 := bstep (se 2 (by rfl) ⟨391596, by rfl⟩ : syracuseStep 1044257 = 783193) B783193
theorem B2354993 : Blo 694316 2354993 := bstep (se 2 (by rfl) ⟨883122, by rfl⟩ : syracuseStep 2354993 = 1766245) B1766245
theorem B782131 : Blo 694316 782131 := bstep (se 1 (by rfl) ⟨586598, by rfl⟩ : syracuseStep 782131 = 1173197) B1173197
theorem B1044275 : Blo 694316 1044275 := bstep (se 1 (by rfl) ⟨783206, by rfl⟩ : syracuseStep 1044275 = 1566413) B1566413
theorem B1044305 : Blo 694316 1044305 := bstep (se 2 (by rfl) ⟨391614, by rfl⟩ : syracuseStep 1044305 = 783229) B783229
theorem B1175377 : Blo 694316 1175377 := bstep (se 2 (by rfl) ⟨440766, by rfl⟩ : syracuseStep 1175377 = 881533) B881533
theorem B1044323 : Blo 694316 1044323 := bstep (se 1 (by rfl) ⟨783242, by rfl⟩ : syracuseStep 1044323 = 1566485) B1566485
theorem B1175411 : Blo 694316 1175411 := bstep (se 1 (by rfl) ⟨881558, by rfl⟩ : syracuseStep 1175411 = 1763117) B1763117
theorem B1044353 : Blo 694316 1044353 := bstep (se 2 (by rfl) ⟨391632, by rfl⟩ : syracuseStep 1044353 = 783265) B783265
theorem B1044371 : Blo 694316 1044371 := bstep (se 1 (by rfl) ⟨783278, by rfl⟩ : syracuseStep 1044371 = 1566557) B1566557
theorem B1044401 : Blo 694316 1044401 := bstep (se 2 (by rfl) ⟨391650, by rfl⟩ : syracuseStep 1044401 = 783301) B783301
theorem B782275 : Blo 694316 782275 := bstep (se 1 (by rfl) ⟨586706, by rfl⟩ : syracuseStep 782275 = 1173413) B1173413
theorem B1044419 : Blo 694316 1044419 := bstep (se 1 (by rfl) ⟨783314, by rfl⟩ : syracuseStep 1044419 = 1566629) B1566629
theorem B1044449 : Blo 694316 1044449 := bstep (se 2 (by rfl) ⟨391668, by rfl⟩ : syracuseStep 1044449 = 783337) B783337
theorem B1568753 : Blo 694316 1568753 := bstep (se 2 (by rfl) ⟨588282, by rfl⟩ : syracuseStep 1568753 = 1176565) B1176565
theorem B2650097 : Blo 694316 2650097 := bstep (se 2 (by rfl) ⟨993786, by rfl⟩ : syracuseStep 2650097 = 1987573) B1987573
theorem B880627 : Blo 694316 880627 := bstep (se 1 (by rfl) ⟨660470, by rfl⟩ : syracuseStep 880627 = 1320941) B1320941
theorem B1044467 : Blo 694316 1044467 := bstep (se 1 (by rfl) ⟨783350, by rfl⟩ : syracuseStep 1044467 = 1566701) B1566701
theorem B1175539 : Blo 694316 1175539 := bstep (se 1 (by rfl) ⟨881654, by rfl⟩ : syracuseStep 1175539 = 1763309) B1763309
theorem B1568771 : Blo 694316 1568771 := bstep (se 1 (by rfl) ⟨1176578, by rfl⟩ : syracuseStep 1568771 = 2353157) B2353157
theorem B1044497 : Blo 694316 1044497 := bstep (se 2 (by rfl) ⟨391686, by rfl⟩ : syracuseStep 1044497 = 783373) B783373
theorem B1044515 : Blo 694316 1044515 := bstep (se 1 (by rfl) ⟨783386, by rfl⟩ : syracuseStep 1044515 = 1566773) B1566773
theorem B1044545 : Blo 694316 1044545 := bstep (se 2 (by rfl) ⟨391704, by rfl⟩ : syracuseStep 1044545 = 783409) B783409
theorem B782419 : Blo 694316 782419 := bstep (se 1 (by rfl) ⟨586814, by rfl⟩ : syracuseStep 782419 = 1173629) B1173629
theorem B880723 : Blo 694316 880723 := bstep (se 1 (by rfl) ⟨660542, by rfl⟩ : syracuseStep 880723 = 1321085) B1321085
theorem B1044563 : Blo 694316 1044563 := bstep (se 1 (by rfl) ⟨783422, by rfl⟩ : syracuseStep 1044563 = 1566845) B1566845
theorem B1044593 : Blo 694316 1044593 := bstep (se 2 (by rfl) ⟨391722, by rfl⟩ : syracuseStep 1044593 = 783445) B783445
theorem B1175681 : Blo 694316 1175681 := bstep (se 2 (by rfl) ⟨440880, by rfl⟩ : syracuseStep 1175681 = 881761) B881761
theorem B1044611 : Blo 694316 1044611 := bstep (se 1 (by rfl) ⟨783458, by rfl⟩ : syracuseStep 1044611 = 1566917) B1566917
theorem B2388113 : Blo 694316 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B1044641 : Blo 694316 1044641 := bstep (se 2 (by rfl) ⟨391740, by rfl⟩ : syracuseStep 1044641 = 783481) B783481
theorem B1044659 : Blo 694316 1044659 := bstep (se 1 (by rfl) ⟨783494, by rfl⟩ : syracuseStep 1044659 = 1566989) B1566989
theorem B1044689 : Blo 694316 1044689 := bstep (se 2 (by rfl) ⟨391758, by rfl⟩ : syracuseStep 1044689 = 783517) B783517
theorem B782563 : Blo 694316 782563 := bstep (se 1 (by rfl) ⟨586922, by rfl⟩ : syracuseStep 782563 = 1173845) B1173845
theorem B1044707 : Blo 694316 1044707 := bstep (se 1 (by rfl) ⟨783530, by rfl⟩ : syracuseStep 1044707 = 1567061) B1567061
theorem B1044737 : Blo 694316 1044737 := bstep (se 2 (by rfl) ⟨391776, by rfl⟩ : syracuseStep 1044737 = 783553) B783553
theorem B1175809 : Blo 694316 1175809 := bstep (se 2 (by rfl) ⟨440928, by rfl⟩ : syracuseStep 1175809 = 881857) B881857
theorem B1569041 : Blo 694316 1569041 := bstep (se 2 (by rfl) ⟨588390, by rfl⟩ : syracuseStep 1569041 = 1176781) B1176781
theorem B1044755 : Blo 694316 1044755 := bstep (se 1 (by rfl) ⟨783566, by rfl⟩ : syracuseStep 1044755 = 1567133) B1567133
theorem B1175843 : Blo 694316 1175843 := bstep (se 1 (by rfl) ⟨881882, by rfl⟩ : syracuseStep 1175843 = 1763765) B1763765
theorem B1569059 : Blo 694316 1569059 := bstep (se 1 (by rfl) ⟨1176794, by rfl⟩ : syracuseStep 1569059 = 2353589) B2353589
theorem B1044785 : Blo 694316 1044785 := bstep (se 2 (by rfl) ⟨391794, by rfl⟩ : syracuseStep 1044785 = 783589) B783589
theorem B1044803 : Blo 694316 1044803 := bstep (se 1 (by rfl) ⟨783602, by rfl⟩ : syracuseStep 1044803 = 1567205) B1567205
theorem B3764549 : Blo 694316 3764549 := bstep (se 4 (by rfl) ⟨352926, by rfl⟩ : syracuseStep 3764549 = 705853) B705853
theorem B2355533 : Blo 694316 2355533 := bstep (se 3 (by rfl) ⟨441662, by rfl⟩ : syracuseStep 2355533 = 883325) B883325
theorem B1044833 : Blo 694316 1044833 := bstep (se 2 (by rfl) ⟨391812, by rfl⟩ : syracuseStep 1044833 = 783625) B783625
theorem B2978147 : Blo 694316 2978147 := bstep (se 1 (by rfl) ⟨2233610, by rfl⟩ : syracuseStep 2978147 = 4467221) B4467221
theorem B782707 : Blo 694316 782707 := bstep (se 1 (by rfl) ⟨587030, by rfl⟩ : syracuseStep 782707 = 1174061) B1174061
theorem B1044851 : Blo 694316 1044851 := bstep (se 1 (by rfl) ⟨783638, by rfl⟩ : syracuseStep 1044851 = 1567277) B1567277
theorem B2355587 : Blo 694316 2355587 := bstep (se 1 (by rfl) ⟨1766690, by rfl⟩ : syracuseStep 2355587 = 3533381) B3533381
theorem B1044881 : Blo 694316 1044881 := bstep (se 2 (by rfl) ⟨391830, by rfl⟩ : syracuseStep 1044881 = 783661) B783661
theorem B1175971 : Blo 694316 1175971 := bstep (se 1 (by rfl) ⟨881978, by rfl⟩ : syracuseStep 1175971 = 1763957) B1763957
theorem B1044899 : Blo 694316 1044899 := bstep (se 1 (by rfl) ⟨783674, by rfl⟩ : syracuseStep 1044899 = 1567349) B1567349
theorem B1044929 : Blo 694316 1044929 := bstep (se 2 (by rfl) ⟨391848, by rfl⟩ : syracuseStep 1044929 = 783697) B783697
theorem B2224589 : Blo 694316 2224589 := bstep (se 3 (by rfl) ⟨417110, by rfl⟩ : syracuseStep 2224589 = 834221) B834221
theorem B1044947 : Blo 694316 1044947 := bstep (se 1 (by rfl) ⟨783710, by rfl⟩ : syracuseStep 1044947 = 1567421) B1567421
theorem B1044977 : Blo 694316 1044977 := bstep (se 2 (by rfl) ⟨391866, by rfl⟩ : syracuseStep 1044977 = 783733) B783733
theorem B782851 : Blo 694316 782851 := bstep (se 1 (by rfl) ⟨587138, by rfl⟩ : syracuseStep 782851 = 1174277) B1174277
theorem B1044995 : Blo 694316 1044995 := bstep (se 1 (by rfl) ⟨783746, by rfl⟩ : syracuseStep 1044995 = 1567493) B1567493
theorem B4452869 : Blo 694316 4452869 := bstep (se 4 (by rfl) ⟨417456, by rfl⟩ : syracuseStep 4452869 = 834913) B834913
theorem B1045025 : Blo 694316 1045025 := bstep (se 2 (by rfl) ⟨391884, by rfl⟩ : syracuseStep 1045025 = 783769) B783769
theorem B1176113 : Blo 694316 1176113 := bstep (se 2 (by rfl) ⟨441042, by rfl⟩ : syracuseStep 1176113 = 882085) B882085
theorem B1569329 : Blo 694316 1569329 := bstep (se 2 (by rfl) ⟨588498, by rfl⟩ : syracuseStep 1569329 = 1176997) B1176997
theorem B1045043 : Blo 694316 1045043 := bstep (se 1 (by rfl) ⟨783782, by rfl⟩ : syracuseStep 1045043 = 1567565) B1567565
theorem B881219 : Blo 694316 881219 := bstep (se 1 (by rfl) ⟨660914, by rfl⟩ : syracuseStep 881219 = 1321829) B1321829
theorem B1569347 : Blo 694316 1569347 := bstep (se 1 (by rfl) ⟨1177010, by rfl⟩ : syracuseStep 1569347 = 2354021) B2354021
theorem B1045073 : Blo 694316 1045073 := bstep (se 2 (by rfl) ⟨391902, by rfl⟩ : syracuseStep 1045073 = 783805) B783805
theorem B1045091 : Blo 694316 1045091 := bstep (se 1 (by rfl) ⟨783818, by rfl⟩ : syracuseStep 1045091 = 1567637) B1567637
theorem B1045121 : Blo 694316 1045121 := bstep (se 2 (by rfl) ⟨391920, by rfl⟩ : syracuseStep 1045121 = 783841) B783841
theorem B2650765 : Blo 694316 2650765 := bstep (se 3 (by rfl) ⟨497018, by rfl⟩ : syracuseStep 2650765 = 994037) B994037
theorem B1766033 : Blo 694316 1766033 := bstep (se 2 (by rfl) ⟨662262, by rfl⟩ : syracuseStep 1766033 = 1324525) B1324525
theorem B2355857 : Blo 694316 2355857 := bstep (se 2 (by rfl) ⟨883446, by rfl⟩ : syracuseStep 2355857 = 1766893) B1766893
theorem B782995 : Blo 694316 782995 := bstep (se 1 (by rfl) ⟨587246, by rfl⟩ : syracuseStep 782995 = 1174493) B1174493
theorem B1045139 : Blo 694316 1045139 := bstep (se 1 (by rfl) ⟨783854, by rfl⟩ : syracuseStep 1045139 = 1567709) B1567709
theorem B1045169 : Blo 694316 1045169 := bstep (se 2 (by rfl) ⟨391938, by rfl⟩ : syracuseStep 1045169 = 783877) B783877
theorem B1176241 : Blo 694316 1176241 := bstep (se 2 (by rfl) ⟨441090, by rfl⟩ : syracuseStep 1176241 = 882181) B882181
theorem B1045187 : Blo 694316 1045187 := bstep (se 1 (by rfl) ⟨783890, by rfl⟩ : syracuseStep 1045187 = 1567781) B1567781
theorem B1766083 : Blo 694316 1766083 := bstep (se 1 (by rfl) ⟨1324562, by rfl⟩ : syracuseStep 1766083 = 2649125) B2649125
theorem B1176275 : Blo 694316 1176275 := bstep (se 1 (by rfl) ⟨882206, by rfl⟩ : syracuseStep 1176275 = 1764413) B1764413
theorem B1045217 : Blo 694316 1045217 := bstep (se 2 (by rfl) ⟨391956, by rfl⟩ : syracuseStep 1045217 = 783913) B783913
theorem B2257645 : Blo 694316 2257645 := bstep (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) B846617
theorem B1045235 : Blo 694316 1045235 := bstep (se 1 (by rfl) ⟨783926, by rfl⟩ : syracuseStep 1045235 = 1567853) B1567853
theorem B1045265 : Blo 694316 1045265 := bstep (se 2 (by rfl) ⟨391974, by rfl⟩ : syracuseStep 1045265 = 783949) B783949
theorem B783139 : Blo 694316 783139 := bstep (se 1 (by rfl) ⟨587354, by rfl⟩ : syracuseStep 783139 = 1174709) B1174709
theorem B1045283 : Blo 694316 1045283 := bstep (se 1 (by rfl) ⟨783962, by rfl⟩ : syracuseStep 1045283 = 1567925) B1567925
theorem B1045313 : Blo 694316 1045313 := bstep (se 2 (by rfl) ⟨391992, by rfl⟩ : syracuseStep 1045313 = 783985) B783985
theorem B1569617 : Blo 694316 1569617 := bstep (se 2 (by rfl) ⟨588606, by rfl⟩ : syracuseStep 1569617 = 1177213) B1177213
theorem B1766225 : Blo 694316 1766225 := bstep (se 2 (by rfl) ⟨662334, by rfl⟩ : syracuseStep 1766225 = 1324669) B1324669
theorem B1045331 : Blo 694316 1045331 := bstep (se 1 (by rfl) ⟨783998, by rfl⟩ : syracuseStep 1045331 = 1567997) B1567997
theorem B1176403 : Blo 694316 1176403 := bstep (se 1 (by rfl) ⟨882302, by rfl⟩ : syracuseStep 1176403 = 1764605) B1764605
theorem B1569635 : Blo 694316 1569635 := bstep (se 1 (by rfl) ⟨1177226, by rfl⟩ : syracuseStep 1569635 = 2354453) B2354453
theorem B1045361 : Blo 694316 1045361 := bstep (se 2 (by rfl) ⟨392010, by rfl⟩ : syracuseStep 1045361 = 784021) B784021
theorem B1045379 : Blo 694316 1045379 := bstep (se 1 (by rfl) ⟨784034, by rfl⟩ : syracuseStep 1045379 = 1568069) B1568069
theorem B1045409 : Blo 694316 1045409 := bstep (se 2 (by rfl) ⟨392028, by rfl⟩ : syracuseStep 1045409 = 784057) B784057
theorem B783283 : Blo 694316 783283 := bstep (se 1 (by rfl) ⟨587462, by rfl⟩ : syracuseStep 783283 = 1174925) B1174925
theorem B1045427 : Blo 694316 1045427 := bstep (se 1 (by rfl) ⟨784070, by rfl⟩ : syracuseStep 1045427 = 1568141) B1568141
theorem B1045457 : Blo 694316 1045457 := bstep (se 2 (by rfl) ⟨392046, by rfl⟩ : syracuseStep 1045457 = 784093) B784093
theorem B1176545 : Blo 694316 1176545 := bstep (se 2 (by rfl) ⟨441204, by rfl⟩ : syracuseStep 1176545 = 882409) B882409
theorem B1045475 : Blo 694316 1045475 := bstep (se 1 (by rfl) ⟨784106, by rfl⟩ : syracuseStep 1045475 = 1568213) B1568213
theorem B1045505 : Blo 694316 1045505 := bstep (se 2 (by rfl) ⟨392064, by rfl⟩ : syracuseStep 1045505 = 784129) B784129
theorem B1045523 : Blo 694316 1045523 := bstep (se 1 (by rfl) ⟨784142, by rfl⟩ : syracuseStep 1045523 = 1568285) B1568285
theorem B1045553 : Blo 694316 1045553 := bstep (se 2 (by rfl) ⟨392082, by rfl⟩ : syracuseStep 1045553 = 784165) B784165
theorem B783427 : Blo 694316 783427 := bstep (se 1 (by rfl) ⟨587570, by rfl⟩ : syracuseStep 783427 = 1175141) B1175141
theorem B1045571 : Blo 694316 1045571 := bstep (se 1 (by rfl) ⟨784178, by rfl⟩ : syracuseStep 1045571 = 1568357) B1568357
theorem B1045601 : Blo 694316 1045601 := bstep (se 2 (by rfl) ⟨392100, by rfl⟩ : syracuseStep 1045601 = 784201) B784201
theorem B1176673 : Blo 694316 1176673 := bstep (se 2 (by rfl) ⟨441252, by rfl⟩ : syracuseStep 1176673 = 882505) B882505
theorem B1569905 : Blo 694316 1569905 := bstep (se 2 (by rfl) ⟨588714, by rfl⟩ : syracuseStep 1569905 = 1177429) B1177429
theorem B1045619 : Blo 694316 1045619 := bstep (se 1 (by rfl) ⟨784214, by rfl⟩ : syracuseStep 1045619 = 1568429) B1568429
theorem B1176707 : Blo 694316 1176707 := bstep (se 1 (by rfl) ⟨882530, by rfl⟩ : syracuseStep 1176707 = 1765061) B1765061
theorem B1569923 : Blo 694316 1569923 := bstep (se 1 (by rfl) ⟨1177442, by rfl⟩ : syracuseStep 1569923 = 2354885) B2354885
theorem B1045649 : Blo 694316 1045649 := bstep (se 2 (by rfl) ⟨392118, by rfl⟩ : syracuseStep 1045649 = 784237) B784237
theorem B1045667 : Blo 694316 1045667 := bstep (se 1 (by rfl) ⟨784250, by rfl⟩ : syracuseStep 1045667 = 1568501) B1568501
theorem B2356397 : Blo 694316 2356397 := bstep (se 3 (by rfl) ⟨441824, by rfl⟩ : syracuseStep 2356397 = 883649) B883649
theorem B1045697 : Blo 694316 1045697 := bstep (se 2 (by rfl) ⟨392136, by rfl⟩ : syracuseStep 1045697 = 784273) B784273
theorem B783571 : Blo 694316 783571 := bstep (se 1 (by rfl) ⟨587678, by rfl⟩ : syracuseStep 783571 = 1175357) B1175357
theorem B1045715 : Blo 694316 1045715 := bstep (se 1 (by rfl) ⟨784286, by rfl⟩ : syracuseStep 1045715 = 1568573) B1568573
theorem B2356451 : Blo 694316 2356451 := bstep (se 1 (by rfl) ⟨1767338, by rfl⟩ : syracuseStep 2356451 = 3534677) B3534677
theorem B1045745 : Blo 694316 1045745 := bstep (se 2 (by rfl) ⟨392154, by rfl⟩ : syracuseStep 1045745 = 784309) B784309
theorem B881923 : Blo 694316 881923 := bstep (se 1 (by rfl) ⟨661442, by rfl⟩ : syracuseStep 881923 = 1322885) B1322885
theorem B1045763 : Blo 694316 1045763 := bstep (se 1 (by rfl) ⟨784322, by rfl⟩ : syracuseStep 1045763 = 1568645) B1568645
theorem B1176835 : Blo 694316 1176835 := bstep (se 1 (by rfl) ⟨882626, by rfl⟩ : syracuseStep 1176835 = 1765253) B1765253
theorem B1045793 : Blo 694316 1045793 := bstep (se 2 (by rfl) ⟨392172, by rfl⟩ : syracuseStep 1045793 = 784345) B784345
theorem B1045811 : Blo 694316 1045811 := bstep (se 1 (by rfl) ⟨784358, by rfl⟩ : syracuseStep 1045811 = 1568717) B1568717
theorem B3175757 : Blo 694316 3175757 := bstep (se 3 (by rfl) ⟨595454, by rfl⟩ : syracuseStep 3175757 = 1190909) B1190909
theorem B1045841 : Blo 694316 1045841 := bstep (se 2 (by rfl) ⟨392190, by rfl⟩ : syracuseStep 1045841 = 784381) B784381
theorem B783715 : Blo 694316 783715 := bstep (se 1 (by rfl) ⟨587786, by rfl⟩ : syracuseStep 783715 = 1175573) B1175573
theorem B882019 : Blo 694316 882019 := bstep (se 1 (by rfl) ⟨661514, by rfl⟩ : syracuseStep 882019 = 1323029) B1323029
theorem B1045859 : Blo 694316 1045859 := bstep (se 1 (by rfl) ⟨784394, by rfl⟩ : syracuseStep 1045859 = 1568789) B1568789
theorem B1045889 : Blo 694316 1045889 := bstep (se 2 (by rfl) ⟨392208, by rfl⟩ : syracuseStep 1045889 = 784417) B784417
theorem B1176977 : Blo 694316 1176977 := bstep (se 2 (by rfl) ⟨441366, by rfl⟩ : syracuseStep 1176977 = 882733) B882733
theorem B1570193 : Blo 694316 1570193 := bstep (se 2 (by rfl) ⟨588822, by rfl⟩ : syracuseStep 1570193 = 1177645) B1177645
theorem B1045907 : Blo 694316 1045907 := bstep (se 1 (by rfl) ⟨784430, by rfl⟩ : syracuseStep 1045907 = 1568861) B1568861
theorem B1570211 : Blo 694316 1570211 := bstep (se 1 (by rfl) ⟨1177658, by rfl⟩ : syracuseStep 1570211 = 2355317) B2355317
theorem B1045937 : Blo 694316 1045937 := bstep (se 2 (by rfl) ⟨392226, by rfl⟩ : syracuseStep 1045937 = 784453) B784453
theorem B1045955 : Blo 694316 1045955 := bstep (se 1 (by rfl) ⟨784466, by rfl⟩ : syracuseStep 1045955 = 1568933) B1568933
theorem B1045985 : Blo 694316 1045985 := bstep (se 2 (by rfl) ⟨392244, by rfl⟩ : syracuseStep 1045985 = 784489) B784489
theorem B2356721 : Blo 694316 2356721 := bstep (se 2 (by rfl) ⟨883770, by rfl⟩ : syracuseStep 2356721 = 1767541) B1767541
theorem B783859 : Blo 694316 783859 := bstep (se 1 (by rfl) ⟨587894, by rfl⟩ : syracuseStep 783859 = 1175789) B1175789
theorem B1046003 : Blo 694316 1046003 := bstep (se 1 (by rfl) ⟨784502, by rfl⟩ : syracuseStep 1046003 = 1569005) B1569005
theorem B1046033 : Blo 694316 1046033 := bstep (se 2 (by rfl) ⟨392262, by rfl⟩ : syracuseStep 1046033 = 784525) B784525
theorem B1177105 : Blo 694316 1177105 := bstep (se 2 (by rfl) ⟨441414, by rfl⟩ : syracuseStep 1177105 = 882829) B882829
theorem B1046051 : Blo 694316 1046051 := bstep (se 1 (by rfl) ⟨784538, by rfl⟩ : syracuseStep 1046051 = 1569077) B1569077
theorem B1177139 : Blo 694316 1177139 := bstep (se 1 (by rfl) ⟨882854, by rfl⟩ : syracuseStep 1177139 = 1765709) B1765709
theorem B1046081 : Blo 694316 1046081 := bstep (se 2 (by rfl) ⟨392280, by rfl⟩ : syracuseStep 1046081 = 784561) B784561
theorem B1046099 : Blo 694316 1046099 := bstep (se 1 (by rfl) ⟨784574, by rfl⟩ : syracuseStep 1046099 = 1569149) B1569149
theorem B1046129 : Blo 694316 1046129 := bstep (se 2 (by rfl) ⟨392298, by rfl⟩ : syracuseStep 1046129 = 784597) B784597
theorem B784003 : Blo 694316 784003 := bstep (se 1 (by rfl) ⟨588002, by rfl⟩ : syracuseStep 784003 = 1176005) B1176005
theorem B1046147 : Blo 694316 1046147 := bstep (se 1 (by rfl) ⟨784610, by rfl⟩ : syracuseStep 1046147 = 1569221) B1569221
theorem B1046177 : Blo 694316 1046177 := bstep (se 2 (by rfl) ⟨392316, by rfl⟩ : syracuseStep 1046177 = 784633) B784633
theorem B1570481 : Blo 694316 1570481 := bstep (se 2 (by rfl) ⟨588930, by rfl⟩ : syracuseStep 1570481 = 1177861) B1177861
theorem B1046195 : Blo 694316 1046195 := bstep (se 1 (by rfl) ⟨784646, by rfl⟩ : syracuseStep 1046195 = 1569293) B1569293
theorem B1177267 : Blo 694316 1177267 := bstep (se 1 (by rfl) ⟨882950, by rfl⟩ : syracuseStep 1177267 = 1765901) B1765901
theorem B1570499 : Blo 694316 1570499 := bstep (se 1 (by rfl) ⟨1177874, by rfl⟩ : syracuseStep 1570499 = 2355749) B2355749
theorem B1046225 : Blo 694316 1046225 := bstep (se 2 (by rfl) ⟨392334, by rfl⟩ : syracuseStep 1046225 = 784669) B784669
theorem B1046243 : Blo 694316 1046243 := bstep (se 1 (by rfl) ⟨784682, by rfl⟩ : syracuseStep 1046243 = 1569365) B1569365
theorem B1046273 : Blo 694316 1046273 := bstep (se 2 (by rfl) ⟨392352, by rfl⟩ : syracuseStep 1046273 = 784705) B784705
theorem B784147 : Blo 694316 784147 := bstep (se 1 (by rfl) ⟨588110, by rfl⟩ : syracuseStep 784147 = 1176221) B1176221
theorem B1046291 : Blo 694316 1046291 := bstep (se 1 (by rfl) ⟨784718, by rfl⟩ : syracuseStep 1046291 = 1569437) B1569437
theorem B1046321 : Blo 694316 1046321 := bstep (se 2 (by rfl) ⟨392370, by rfl⟩ : syracuseStep 1046321 = 784741) B784741
theorem B1767217 : Blo 694316 1767217 := bstep (se 2 (by rfl) ⟨662706, by rfl⟩ : syracuseStep 1767217 = 1325413) B1325413
theorem B1177409 : Blo 694316 1177409 := bstep (se 2 (by rfl) ⟨441528, by rfl⟩ : syracuseStep 1177409 = 883057) B883057
theorem B1046339 : Blo 694316 1046339 := bstep (se 1 (by rfl) ⟨784754, by rfl⟩ : syracuseStep 1046339 = 1569509) B1569509
theorem B882515 : Blo 694316 882515 := bstep (se 1 (by rfl) ⟨661886, by rfl⟩ : syracuseStep 882515 = 1323773) B1323773
theorem B1046369 : Blo 694316 1046369 := bstep (se 2 (by rfl) ⟨392388, by rfl⟩ : syracuseStep 1046369 = 784777) B784777
theorem B1046387 : Blo 694316 1046387 := bstep (se 1 (by rfl) ⟨784790, by rfl⟩ : syracuseStep 1046387 = 1569581) B1569581
theorem B1046417 : Blo 694316 1046417 := bstep (se 2 (by rfl) ⟨392406, by rfl⟩ : syracuseStep 1046417 = 784813) B784813
theorem B784291 : Blo 694316 784291 := bstep (se 1 (by rfl) ⟨588218, by rfl⟩ : syracuseStep 784291 = 1176437) B1176437
theorem B1046435 : Blo 694316 1046435 := bstep (se 1 (by rfl) ⟨784826, by rfl⟩ : syracuseStep 1046435 = 1569653) B1569653
theorem B1046465 : Blo 694316 1046465 := bstep (se 2 (by rfl) ⟨392424, by rfl⟩ : syracuseStep 1046465 = 784849) B784849
theorem B1177537 : Blo 694316 1177537 := bstep (se 2 (by rfl) ⟨441576, by rfl⟩ : syracuseStep 1177537 = 883153) B883153
theorem B1570769 : Blo 694316 1570769 := bstep (se 2 (by rfl) ⟨589038, by rfl⟩ : syracuseStep 1570769 = 1178077) B1178077
theorem B1046483 : Blo 694316 1046483 := bstep (se 1 (by rfl) ⟨784862, by rfl⟩ : syracuseStep 1046483 = 1569725) B1569725
theorem B1177571 : Blo 694316 1177571 := bstep (se 1 (by rfl) ⟨883178, by rfl⟩ : syracuseStep 1177571 = 1766357) B1766357
theorem B1570787 : Blo 694316 1570787 := bstep (se 1 (by rfl) ⟨1178090, by rfl⟩ : syracuseStep 1570787 = 2356181) B2356181
theorem B5273585 : Blo 694316 5273585 := bstep (se 2 (by rfl) ⟨1977594, by rfl⟩ : syracuseStep 5273585 = 3955189) B3955189
theorem B1046513 : Blo 694316 1046513 := bstep (se 2 (by rfl) ⟨392442, by rfl⟩ : syracuseStep 1046513 = 784885) B784885
theorem B2226179 : Blo 694316 2226179 := bstep (se 1 (by rfl) ⟨1669634, by rfl⟩ : syracuseStep 2226179 = 3339269) B3339269
theorem B1046531 : Blo 694316 1046531 := bstep (se 1 (by rfl) ⟨784898, by rfl⟩ : syracuseStep 1046531 = 1569797) B1569797
theorem B1046561 : Blo 694316 1046561 := bstep (se 2 (by rfl) ⟨392460, by rfl⟩ : syracuseStep 1046561 = 784921) B784921
theorem B784435 : Blo 694316 784435 := bstep (se 1 (by rfl) ⟨588326, by rfl⟩ : syracuseStep 784435 = 1176653) B1176653
theorem B1046579 : Blo 694316 1046579 := bstep (se 1 (by rfl) ⟨784934, by rfl⟩ : syracuseStep 1046579 = 1569869) B1569869
theorem B1767491 : Blo 694316 1767491 := bstep (se 1 (by rfl) ⟨1325618, by rfl⟩ : syracuseStep 1767491 = 2651237) B2651237
theorem B1046609 : Blo 694316 1046609 := bstep (se 2 (by rfl) ⟨392478, by rfl⟩ : syracuseStep 1046609 = 784957) B784957
theorem B1046627 : Blo 694316 1046627 := bstep (se 1 (by rfl) ⟨784970, by rfl⟩ : syracuseStep 1046627 = 1569941) B1569941
theorem B1177699 : Blo 694316 1177699 := bstep (se 1 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 1177699 = 1766549) B1766549
theorem B1046657 : Blo 694316 1046657 := bstep (se 2 (by rfl) ⟨392496, by rfl⟩ : syracuseStep 1046657 = 784993) B784993
theorem B1046675 : Blo 694316 1046675 := bstep (se 1 (by rfl) ⟨785006, by rfl⟩ : syracuseStep 1046675 = 1570013) B1570013
theorem B1046705 : Blo 694316 1046705 := bstep (se 2 (by rfl) ⟨392514, by rfl⟩ : syracuseStep 1046705 = 785029) B785029
theorem B784579 : Blo 694316 784579 := bstep (se 1 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 784579 = 1176869) B1176869
theorem B1046723 : Blo 694316 1046723 := bstep (se 1 (by rfl) ⟨785042, by rfl⟩ : syracuseStep 1046723 = 1570085) B1570085
theorem B1046753 : Blo 694316 1046753 := bstep (se 2 (by rfl) ⟨392532, by rfl⟩ : syracuseStep 1046753 = 785065) B785065
theorem B1177841 : Blo 694316 1177841 := bstep (se 2 (by rfl) ⟨441690, by rfl⟩ : syracuseStep 1177841 = 883381) B883381
theorem B1571057 : Blo 694316 1571057 := bstep (se 2 (by rfl) ⟨589146, by rfl⟩ : syracuseStep 1571057 = 1178293) B1178293
theorem B1046771 : Blo 694316 1046771 := bstep (se 1 (by rfl) ⟨785078, by rfl⟩ : syracuseStep 1046771 = 1570157) B1570157
theorem B1571075 : Blo 694316 1571075 := bstep (se 1 (by rfl) ⟨1178306, by rfl⟩ : syracuseStep 1571075 = 2356613) B2356613
theorem B1046801 : Blo 694316 1046801 := bstep (se 2 (by rfl) ⟨392550, by rfl⟩ : syracuseStep 1046801 = 785101) B785101
theorem B1046819 : Blo 694316 1046819 := bstep (se 1 (by rfl) ⟨785114, by rfl⟩ : syracuseStep 1046819 = 1570229) B1570229
theorem B1046849 : Blo 694316 1046849 := bstep (se 2 (by rfl) ⟨392568, by rfl⟩ : syracuseStep 1046849 = 785137) B785137
theorem B784723 : Blo 694316 784723 := bstep (se 1 (by rfl) ⟨588542, by rfl⟩ : syracuseStep 784723 = 1177085) B1177085
theorem B1046867 : Blo 694316 1046867 := bstep (se 1 (by rfl) ⟨785150, by rfl⟩ : syracuseStep 1046867 = 1570301) B1570301
theorem B1046897 : Blo 694316 1046897 := bstep (se 2 (by rfl) ⟨392586, by rfl⟩ : syracuseStep 1046897 = 785173) B785173
theorem B1177969 : Blo 694316 1177969 := bstep (se 2 (by rfl) ⟨441738, by rfl⟩ : syracuseStep 1177969 = 883477) B883477
theorem B1112449 : Blo 694316 1112449 := bstep (se 2 (by rfl) ⟨417168, by rfl⟩ : syracuseStep 1112449 = 834337) B834337
theorem B1046915 : Blo 694316 1046915 := bstep (se 1 (by rfl) ⟨785186, by rfl⟩ : syracuseStep 1046915 = 1570373) B1570373
theorem B1178003 : Blo 694316 1178003 := bstep (se 1 (by rfl) ⟨883502, by rfl⟩ : syracuseStep 1178003 = 1767005) B1767005
theorem B1046945 : Blo 694316 1046945 := bstep (se 2 (by rfl) ⟨392604, by rfl⟩ : syracuseStep 1046945 = 785209) B785209
theorem B1046963 : Blo 694316 1046963 := bstep (se 1 (by rfl) ⟨785222, by rfl⟩ : syracuseStep 1046963 = 1570445) B1570445
theorem B1046993 : Blo 694316 1046993 := bstep (se 2 (by rfl) ⟨392622, by rfl⟩ : syracuseStep 1046993 = 785245) B785245
theorem B1112545 : Blo 694316 1112545 := bstep (se 2 (by rfl) ⟨417204, by rfl⟩ : syracuseStep 1112545 = 834409) B834409
theorem B784867 : Blo 694316 784867 := bstep (se 1 (by rfl) ⟨588650, by rfl⟩ : syracuseStep 784867 = 1177301) B1177301
theorem B1047011 : Blo 694316 1047011 := bstep (se 1 (by rfl) ⟨785258, by rfl⟩ : syracuseStep 1047011 = 1570517) B1570517
theorem B1047041 : Blo 694316 1047041 := bstep (se 2 (by rfl) ⟨392640, by rfl⟩ : syracuseStep 1047041 = 785281) B785281
theorem B883219 : Blo 694316 883219 := bstep (se 1 (by rfl) ⟨662414, by rfl⟩ : syracuseStep 883219 = 1324829) B1324829
theorem B1047059 : Blo 694316 1047059 := bstep (se 1 (by rfl) ⟨785294, by rfl⟩ : syracuseStep 1047059 = 1570589) B1570589
theorem B1178131 : Blo 694316 1178131 := bstep (se 1 (by rfl) ⟨883598, by rfl⟩ : syracuseStep 1178131 = 1767197) B1767197
theorem B1047089 : Blo 694316 1047089 := bstep (se 2 (by rfl) ⟨392658, by rfl⟩ : syracuseStep 1047089 = 785317) B785317
theorem B1047107 : Blo 694316 1047107 := bstep (se 1 (by rfl) ⟨785330, by rfl⟩ : syracuseStep 1047107 = 1570661) B1570661
theorem B1047137 : Blo 694316 1047137 := bstep (se 2 (by rfl) ⟨392676, by rfl⟩ : syracuseStep 1047137 = 785353) B785353
theorem B785011 : Blo 694316 785011 := bstep (se 1 (by rfl) ⟨588758, by rfl⟩ : syracuseStep 785011 = 1177517) B1177517
theorem B883315 : Blo 694316 883315 := bstep (se 1 (by rfl) ⟨662486, by rfl⟩ : syracuseStep 883315 = 1324973) B1324973
theorem B1047155 : Blo 694316 1047155 := bstep (se 1 (by rfl) ⟨785366, by rfl⟩ : syracuseStep 1047155 = 1570733) B1570733
theorem B1112705 : Blo 694316 1112705 := bstep (se 2 (by rfl) ⟨417264, by rfl⟩ : syracuseStep 1112705 = 834529) B834529
theorem B1047185 : Blo 694316 1047185 := bstep (se 2 (by rfl) ⟨392694, by rfl⟩ : syracuseStep 1047185 = 785389) B785389
theorem B1178273 : Blo 694316 1178273 := bstep (se 2 (by rfl) ⟨441852, by rfl⟩ : syracuseStep 1178273 = 883705) B883705
theorem B1047203 : Blo 694316 1047203 := bstep (se 1 (by rfl) ⟨785402, by rfl⟩ : syracuseStep 1047203 = 1570805) B1570805
theorem B1047233 : Blo 694316 1047233 := bstep (se 2 (by rfl) ⟨392712, by rfl⟩ : syracuseStep 1047233 = 785425) B785425
theorem B1047251 : Blo 694316 1047251 := bstep (se 1 (by rfl) ⟨785438, by rfl⟩ : syracuseStep 1047251 = 1570877) B1570877
theorem B1047281 : Blo 694316 1047281 := bstep (se 2 (by rfl) ⟨392730, by rfl⟩ : syracuseStep 1047281 = 785461) B785461
theorem B785155 : Blo 694316 785155 := bstep (se 1 (by rfl) ⟨588866, by rfl⟩ : syracuseStep 785155 = 1177733) B1177733
theorem B1047299 : Blo 694316 1047299 := bstep (se 1 (by rfl) ⟨785474, by rfl⟩ : syracuseStep 1047299 = 1570949) B1570949
theorem B1047329 : Blo 694316 1047329 := bstep (se 2 (by rfl) ⟨392748, by rfl⟩ : syracuseStep 1047329 = 785497) B785497
theorem B1178401 : Blo 694316 1178401 := bstep (se 2 (by rfl) ⟨441900, by rfl⟩ : syracuseStep 1178401 = 883801) B883801
theorem B1047347 : Blo 694316 1047347 := bstep (se 1 (by rfl) ⟨785510, by rfl⟩ : syracuseStep 1047347 = 1571021) B1571021
theorem B1047377 : Blo 694316 1047377 := bstep (se 2 (by rfl) ⟨392766, by rfl⟩ : syracuseStep 1047377 = 785533) B785533
theorem B1047395 : Blo 694316 1047395 := bstep (se 1 (by rfl) ⟨785546, by rfl⟩ : syracuseStep 1047395 = 1571093) B1571093
theorem B1047425 : Blo 694316 1047425 := bstep (se 2 (by rfl) ⟨392784, by rfl⟩ : syracuseStep 1047425 = 785569) B785569
theorem B785299 : Blo 694316 785299 := bstep (se 1 (by rfl) ⟨588974, by rfl⟩ : syracuseStep 785299 = 1177949) B1177949
theorem B1047443 : Blo 694316 1047443 := bstep (se 1 (by rfl) ⟨785582, by rfl⟩ : syracuseStep 1047443 = 1571165) B1571165
theorem B1047473 : Blo 694316 1047473 := bstep (se 2 (by rfl) ⟨392802, by rfl⟩ : syracuseStep 1047473 = 785605) B785605
theorem B2980813 : Blo 694316 2980813 := bstep (se 3 (by rfl) ⟨558902, by rfl⟩ : syracuseStep 2980813 = 1117805) B1117805
theorem B785443 : Blo 694316 785443 := bstep (se 1 (by rfl) ⟨589082, by rfl⟩ : syracuseStep 785443 = 1178165) B1178165
theorem B4455587 : Blo 694316 4455587 := bstep (se 1 (by rfl) ⟨3341690, by rfl⟩ : syracuseStep 4455587 = 6683381) B6683381
theorem B785587 : Blo 694316 785587 := bstep (se 1 (by rfl) ⟨589190, by rfl⟩ : syracuseStep 785587 = 1178381) B1178381
theorem B2227409 : Blo 694316 2227409 := bstep (se 2 (by rfl) ⟨835278, by rfl⟩ : syracuseStep 2227409 = 1670557) B1670557
theorem B2817251 : Blo 694316 2817251 := bstep (se 1 (by rfl) ⟨2112938, by rfl⟩ : syracuseStep 2817251 = 4225877) B4225877
theorem B5012707 : Blo 694316 5012707 := bstep (se 1 (by rfl) ⟨3759530, by rfl⟩ : syracuseStep 5012707 = 7519061) B7519061
theorem B6683917 : Blo 694316 6683917 := bstep (se 3 (by rfl) ⟨1253234, by rfl⟩ : syracuseStep 6683917 = 2506469) B2506469
theorem B4226993 : Blo 694316 4226993 := bstep (se 2 (by rfl) ⟨1585122, by rfl⟩ : syracuseStep 4226993 = 3170245) B3170245
theorem B1343459 : Blo 694316 1343459 := bstep (se 1 (by rfl) ⟨1007594, by rfl⟩ : syracuseStep 1343459 = 2015189) B2015189
theorem B2981873 : Blo 694316 2981873 := bstep (se 2 (by rfl) ⟨1118202, by rfl⟩ : syracuseStep 2981873 = 2236405) B2236405
theorem B19005475 : Blo 694316 19005475 := bstep (se 1 (by rfl) ⟨14254106, by rfl⟩ : syracuseStep 19005475 = 28508213) B28508213
theorem B4227137 : Blo 694316 4227137 := bstep (se 2 (by rfl) ⟨1585176, by rfl⟩ : syracuseStep 4227137 = 3170353) B3170353
theorem B1409177 : Blo 694316 1409177 := bstep (se 2 (by rfl) ⟨528441, by rfl⟩ : syracuseStep 1409177 = 1056883) B1056883
theorem B3440819 : Blo 694316 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B7930061 : Blo 694316 7930061 := bstep (se 3 (by rfl) ⟨1486886, by rfl⟩ : syracuseStep 7930061 = 2973773) B2973773
theorem B1114391 : Blo 694316 1114391 := bstep (se 1 (by rfl) ⟨835793, by rfl⟩ : syracuseStep 1114391 = 1671587) B1671587
theorem B1114955 : Blo 694316 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B9503837 : Blo 694316 9503837 := bstep (se 3 (by rfl) ⟨1781969, by rfl⟩ : syracuseStep 9503837 = 3563939) B3563939
theorem B5637221 : Blo 694316 5637221 := bstep (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) B1056979
theorem B2819245 : Blo 694316 2819245 := bstep (se 3 (by rfl) ⟨528608, by rfl⟩ : syracuseStep 2819245 = 1057217) B1057217
theorem B5932237 : Blo 694316 5932237 := bstep (se 3 (by rfl) ⟨1112294, by rfl⟩ : syracuseStep 5932237 = 2224589) B2224589
theorem B2819393 : Blo 694316 2819393 := bstep (se 2 (by rfl) ⟨1057272, by rfl⟩ : syracuseStep 2819393 = 2114545) B2114545
theorem B1410571 : Blo 694316 1410571 := bstep (se 1 (by rfl) ⟨1057928, by rfl⟩ : syracuseStep 1410571 = 2115857) B2115857
theorem B1836875 : Blo 694316 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B3967127 : Blo 694316 3967127 := bstep (se 1 (by rfl) ⟨2975345, by rfl⟩ : syracuseStep 3967127 = 5950691) B5950691
theorem B11307269 : Blo 694316 11307269 := bstep (se 4 (by rfl) ⟨1060056, by rfl⟩ : syracuseStep 11307269 = 2120113) B2120113
theorem B5933573 : Blo 694316 5933573 := bstep (se 4 (by rfl) ⟨556272, by rfl⟩ : syracuseStep 5933573 = 1112545) B1112545
theorem B1673921 : Blo 694316 1673921 := bstep (se 2 (by rfl) ⟨627720, by rfl⟩ : syracuseStep 1673921 = 1255441) B1255441
theorem B4459225 : Blo 694316 4459225 := bstep (se 2 (by rfl) ⟨1672209, by rfl⟩ : syracuseStep 4459225 = 3344419) B3344419
theorem B2821337 : Blo 694316 2821337 := bstep (se 2 (by rfl) ⟨1058001, by rfl⟩ : syracuseStep 2821337 = 2116003) B2116003
theorem B6098327 : Blo 694316 6098327 := bstep (se 1 (by rfl) ⟨4573745, by rfl⟩ : syracuseStep 6098327 = 9147491) B9147491
theorem B7146929 : Blo 694316 7146929 := bstep (se 2 (by rfl) ⟨2680098, by rfl⟩ : syracuseStep 7146929 = 5360197) B5360197
theorem B3182017 : Blo 694316 3182017 := bstep (se 2 (by rfl) ⟨1193256, by rfl⟩ : syracuseStep 3182017 = 2386513) B2386513
theorem B10030949 : Blo 694316 10030949 := bstep (se 4 (by rfl) ⟨940401, by rfl⟩ : syracuseStep 10030949 = 1880803) B1880803
theorem B1905373 : Blo 694316 1905373 := bstep (se 3 (by rfl) ⟨357257, by rfl⟩ : syracuseStep 1905373 = 714515) B714515
theorem B2233433 : Blo 694316 2233433 := bstep (se 2 (by rfl) ⟨837537, by rfl⟩ : syracuseStep 2233433 = 1675075) B1675075
theorem B16258421 : Blo 694316 16258421 := bstep (se 5 (by rfl) ⟨762113, by rfl⟩ : syracuseStep 16258421 = 1524227) B1524227
theorem B1021465 : Blo 694316 1021465 := bstep (se 2 (by rfl) ⟨383049, by rfl⟩ : syracuseStep 1021465 = 766099) B766099
theorem B1251289 : Blo 694316 1251289 := bstep (se 2 (by rfl) ⟨469233, by rfl⟩ : syracuseStep 1251289 = 938467) B938467
theorem B11606051 : Blo 694316 11606051 := bstep (se 1 (by rfl) ⟨8704538, by rfl⟩ : syracuseStep 11606051 = 17409077) B17409077
theorem B694327 : Blo 694316 694327 := bstep (se 1 (by rfl) ⟨520745, by rfl⟩ : syracuseStep 694327 = 1041491) B1041491
theorem B694347 : Blo 694316 694347 := bstep (se 1 (by rfl) ⟨520760, by rfl⟩ : syracuseStep 694347 = 1041521) B1041521
theorem B694359 : Blo 694316 694359 := bstep (se 1 (by rfl) ⟨520769, by rfl⟩ : syracuseStep 694359 = 1041539) B1041539
theorem B694379 : Blo 694316 694379 := bstep (se 1 (by rfl) ⟨520784, by rfl⟩ : syracuseStep 694379 = 1041569) B1041569
theorem B694391 : Blo 694316 694391 := bstep (se 1 (by rfl) ⟨520793, by rfl⟩ : syracuseStep 694391 = 1041587) B1041587
theorem B694411 : Blo 694316 694411 := bstep (se 1 (by rfl) ⟨520808, by rfl⟩ : syracuseStep 694411 = 1041617) B1041617
theorem B694423 : Blo 694316 694423 := bstep (se 1 (by rfl) ⟨520817, by rfl⟩ : syracuseStep 694423 = 1041635) B1041635
theorem B694443 : Blo 694316 694443 := bstep (se 1 (by rfl) ⟨520832, by rfl⟩ : syracuseStep 694443 = 1041665) B1041665
theorem B694455 : Blo 694316 694455 := bstep (se 1 (by rfl) ⟨520841, by rfl⟩ : syracuseStep 694455 = 1041683) B1041683
theorem B694475 : Blo 694316 694475 := bstep (se 1 (by rfl) ⟨520856, by rfl⟩ : syracuseStep 694475 = 1041713) B1041713
theorem B694487 : Blo 694316 694487 := bstep (se 1 (by rfl) ⟨520865, by rfl⟩ : syracuseStep 694487 = 1041731) B1041731
theorem B694507 : Blo 694316 694507 := bstep (se 1 (by rfl) ⟨520880, by rfl⟩ : syracuseStep 694507 = 1041761) B1041761
theorem B694519 : Blo 694316 694519 := bstep (se 1 (by rfl) ⟨520889, by rfl⟩ : syracuseStep 694519 = 1041779) B1041779
theorem B694539 : Blo 694316 694539 := bstep (se 1 (by rfl) ⟨520904, by rfl⟩ : syracuseStep 694539 = 1041809) B1041809
theorem B694551 : Blo 694316 694551 := bstep (se 1 (by rfl) ⟨520913, by rfl⟩ : syracuseStep 694551 = 1041827) B1041827
theorem B694571 : Blo 694316 694571 := bstep (se 1 (by rfl) ⟨520928, by rfl⟩ : syracuseStep 694571 = 1041857) B1041857
theorem B694583 : Blo 694316 694583 := bstep (se 1 (by rfl) ⟨520937, by rfl⟩ : syracuseStep 694583 = 1041875) B1041875
theorem B694603 : Blo 694316 694603 := bstep (se 1 (by rfl) ⟨520952, by rfl⟩ : syracuseStep 694603 = 1041905) B1041905
theorem B694615 : Blo 694316 694615 := bstep (se 1 (by rfl) ⟨520961, by rfl⟩ : syracuseStep 694615 = 1041923) B1041923
theorem B694635 : Blo 694316 694635 := bstep (se 1 (by rfl) ⟨520976, by rfl⟩ : syracuseStep 694635 = 1041953) B1041953
theorem B694647 : Blo 694316 694647 := bstep (se 1 (by rfl) ⟨520985, by rfl⟩ : syracuseStep 694647 = 1041971) B1041971
theorem B2824579 : Blo 694316 2824579 := bstep (se 1 (by rfl) ⟨2118434, by rfl⟩ : syracuseStep 2824579 = 4236869) B4236869
theorem B694667 : Blo 694316 694667 := bstep (se 1 (by rfl) ⟨521000, by rfl⟩ : syracuseStep 694667 = 1042001) B1042001
theorem B694679 : Blo 694316 694679 := bstep (se 1 (by rfl) ⟨521009, by rfl⟩ : syracuseStep 694679 = 1042019) B1042019
theorem B694699 : Blo 694316 694699 := bstep (se 1 (by rfl) ⟨521024, by rfl⟩ : syracuseStep 694699 = 1042049) B1042049
theorem B694711 : Blo 694316 694711 := bstep (se 1 (by rfl) ⟨521033, by rfl⟩ : syracuseStep 694711 = 1042067) B1042067
theorem B694731 : Blo 694316 694731 := bstep (se 1 (by rfl) ⟨521048, by rfl⟩ : syracuseStep 694731 = 1042097) B1042097
theorem B694743 : Blo 694316 694743 := bstep (se 1 (by rfl) ⟨521057, by rfl⟩ : syracuseStep 694743 = 1042115) B1042115
theorem B694763 : Blo 694316 694763 := bstep (se 1 (by rfl) ⟨521072, by rfl⟩ : syracuseStep 694763 = 1042145) B1042145
theorem B694775 : Blo 694316 694775 := bstep (se 1 (by rfl) ⟨521081, by rfl⟩ : syracuseStep 694775 = 1042163) B1042163
theorem B694795 : Blo 694316 694795 := bstep (se 1 (by rfl) ⟨521096, by rfl⟩ : syracuseStep 694795 = 1042193) B1042193
theorem B694807 : Blo 694316 694807 := bstep (se 1 (by rfl) ⟨521105, by rfl⟩ : syracuseStep 694807 = 1042211) B1042211
theorem B694827 : Blo 694316 694827 := bstep (se 1 (by rfl) ⟨521120, by rfl⟩ : syracuseStep 694827 = 1042241) B1042241
theorem B694839 : Blo 694316 694839 := bstep (se 1 (by rfl) ⟨521129, by rfl⟩ : syracuseStep 694839 = 1042259) B1042259
theorem B694859 : Blo 694316 694859 := bstep (se 1 (by rfl) ⟨521144, by rfl⟩ : syracuseStep 694859 = 1042289) B1042289
theorem B694871 : Blo 694316 694871 := bstep (se 1 (by rfl) ⟨521153, by rfl⟩ : syracuseStep 694871 = 1042307) B1042307
theorem B694891 : Blo 694316 694891 := bstep (se 1 (by rfl) ⟨521168, by rfl⟩ : syracuseStep 694891 = 1042337) B1042337
theorem B694903 : Blo 694316 694903 := bstep (se 1 (by rfl) ⟨521177, by rfl⟩ : syracuseStep 694903 = 1042355) B1042355
theorem B694923 : Blo 694316 694923 := bstep (se 1 (by rfl) ⟨521192, by rfl⟩ : syracuseStep 694923 = 1042385) B1042385
theorem B694935 : Blo 694316 694935 := bstep (se 1 (by rfl) ⟨521201, by rfl⟩ : syracuseStep 694935 = 1042403) B1042403
theorem B694955 : Blo 694316 694955 := bstep (se 1 (by rfl) ⟨521216, by rfl⟩ : syracuseStep 694955 = 1042433) B1042433
theorem B694967 : Blo 694316 694967 := bstep (se 1 (by rfl) ⟨521225, by rfl⟩ : syracuseStep 694967 = 1042451) B1042451
theorem B2235073 : Blo 694316 2235073 := bstep (se 2 (by rfl) ⟨838152, by rfl⟩ : syracuseStep 2235073 = 1676305) B1676305
theorem B694987 : Blo 694316 694987 := bstep (se 1 (by rfl) ⟨521240, by rfl⟩ : syracuseStep 694987 = 1042481) B1042481
theorem B694999 : Blo 694316 694999 := bstep (se 1 (by rfl) ⟨521249, by rfl⟩ : syracuseStep 694999 = 1042499) B1042499
theorem B695019 : Blo 694316 695019 := bstep (se 1 (by rfl) ⟨521264, by rfl⟩ : syracuseStep 695019 = 1042529) B1042529
theorem B695031 : Blo 694316 695031 := bstep (se 1 (by rfl) ⟨521273, by rfl⟩ : syracuseStep 695031 = 1042547) B1042547
theorem B695051 : Blo 694316 695051 := bstep (se 1 (by rfl) ⟨521288, by rfl⟩ : syracuseStep 695051 = 1042577) B1042577
theorem B695063 : Blo 694316 695063 := bstep (se 1 (by rfl) ⟨521297, by rfl⟩ : syracuseStep 695063 = 1042595) B1042595
theorem B989977 : Blo 694316 989977 := bstep (se 2 (by rfl) ⟨371241, by rfl⟩ : syracuseStep 989977 = 742483) B742483
theorem B695083 : Blo 694316 695083 := bstep (se 1 (by rfl) ⟨521312, by rfl⟩ : syracuseStep 695083 = 1042625) B1042625
theorem B695095 : Blo 694316 695095 := bstep (se 1 (by rfl) ⟨521321, by rfl⟩ : syracuseStep 695095 = 1042643) B1042643
theorem B695115 : Blo 694316 695115 := bstep (se 1 (by rfl) ⟨521336, by rfl⟩ : syracuseStep 695115 = 1042673) B1042673
theorem B695127 : Blo 694316 695127 := bstep (se 1 (by rfl) ⟨521345, by rfl⟩ : syracuseStep 695127 = 1042691) B1042691
theorem B695147 : Blo 694316 695147 := bstep (se 1 (by rfl) ⟨521360, by rfl⟩ : syracuseStep 695147 = 1042721) B1042721
theorem B695159 : Blo 694316 695159 := bstep (se 1 (by rfl) ⟨521369, by rfl⟩ : syracuseStep 695159 = 1042739) B1042739
theorem B695179 : Blo 694316 695179 := bstep (se 1 (by rfl) ⟨521384, by rfl⟩ : syracuseStep 695179 = 1042769) B1042769
theorem B695191 : Blo 694316 695191 := bstep (se 1 (by rfl) ⟨521393, by rfl⟩ : syracuseStep 695191 = 1042787) B1042787
theorem B695211 : Blo 694316 695211 := bstep (se 1 (by rfl) ⟨521408, by rfl⟩ : syracuseStep 695211 = 1042817) B1042817
theorem B695223 : Blo 694316 695223 := bstep (se 1 (by rfl) ⟨521417, by rfl⟩ : syracuseStep 695223 = 1042835) B1042835
theorem B695243 : Blo 694316 695243 := bstep (se 1 (by rfl) ⟨521432, by rfl⟩ : syracuseStep 695243 = 1042865) B1042865
theorem B695255 : Blo 694316 695255 := bstep (se 1 (by rfl) ⟨521441, by rfl⟩ : syracuseStep 695255 = 1042883) B1042883
theorem B695275 : Blo 694316 695275 := bstep (se 1 (by rfl) ⟨521456, by rfl⟩ : syracuseStep 695275 = 1042913) B1042913
theorem B695287 : Blo 694316 695287 := bstep (se 1 (by rfl) ⟨521465, by rfl⟩ : syracuseStep 695287 = 1042931) B1042931
theorem B695307 : Blo 694316 695307 := bstep (se 1 (by rfl) ⟨521480, by rfl⟩ : syracuseStep 695307 = 1042961) B1042961
theorem B695319 : Blo 694316 695319 := bstep (se 1 (by rfl) ⟨521489, by rfl⟩ : syracuseStep 695319 = 1042979) B1042979
theorem B695339 : Blo 694316 695339 := bstep (se 1 (by rfl) ⟨521504, by rfl⟩ : syracuseStep 695339 = 1043009) B1043009
theorem B793643 : Blo 694316 793643 := bstep (se 1 (by rfl) ⟨595232, by rfl⟩ : syracuseStep 793643 = 1190465) B1190465
theorem B695351 : Blo 694316 695351 := bstep (se 1 (by rfl) ⟨521513, by rfl⟩ : syracuseStep 695351 = 1043027) B1043027
theorem B695371 : Blo 694316 695371 := bstep (se 1 (by rfl) ⟨521528, by rfl⟩ : syracuseStep 695371 = 1043057) B1043057
theorem B695383 : Blo 694316 695383 := bstep (se 1 (by rfl) ⟨521537, by rfl⟩ : syracuseStep 695383 = 1043075) B1043075
theorem B695403 : Blo 694316 695403 := bstep (se 1 (by rfl) ⟨521552, by rfl⟩ : syracuseStep 695403 = 1043105) B1043105
theorem B695415 : Blo 694316 695415 := bstep (se 1 (by rfl) ⟨521561, by rfl⟩ : syracuseStep 695415 = 1043123) B1043123
theorem B3579011 : Blo 694316 3579011 := bstep (se 1 (by rfl) ⟨2684258, by rfl⟩ : syracuseStep 3579011 = 5368517) B5368517
theorem B695435 : Blo 694316 695435 := bstep (se 1 (by rfl) ⟨521576, by rfl⟩ : syracuseStep 695435 = 1043153) B1043153
theorem B695447 : Blo 694316 695447 := bstep (se 1 (by rfl) ⟨521585, by rfl⟩ : syracuseStep 695447 = 1043171) B1043171
theorem B695467 : Blo 694316 695467 := bstep (se 1 (by rfl) ⟨521600, by rfl⟩ : syracuseStep 695467 = 1043201) B1043201
theorem B695479 : Blo 694316 695479 := bstep (se 1 (by rfl) ⟨521609, by rfl⟩ : syracuseStep 695479 = 1043219) B1043219
theorem B695499 : Blo 694316 695499 := bstep (se 1 (by rfl) ⟨521624, by rfl⟩ : syracuseStep 695499 = 1043249) B1043249
theorem B695511 : Blo 694316 695511 := bstep (se 1 (by rfl) ⟨521633, by rfl⟩ : syracuseStep 695511 = 1043267) B1043267
theorem B695531 : Blo 694316 695531 := bstep (se 1 (by rfl) ⟨521648, by rfl⟩ : syracuseStep 695531 = 1043297) B1043297
theorem B695543 : Blo 694316 695543 := bstep (se 1 (by rfl) ⟨521657, by rfl⟩ : syracuseStep 695543 = 1043315) B1043315
theorem B695563 : Blo 694316 695563 := bstep (se 1 (by rfl) ⟨521672, by rfl⟩ : syracuseStep 695563 = 1043345) B1043345
theorem B695575 : Blo 694316 695575 := bstep (se 1 (by rfl) ⟨521681, by rfl⟩ : syracuseStep 695575 = 1043363) B1043363
theorem B1318169 : Blo 694316 1318169 := bstep (se 2 (by rfl) ⟨494313, by rfl⟩ : syracuseStep 1318169 = 988627) B988627
theorem B695595 : Blo 694316 695595 := bstep (se 1 (by rfl) ⟨521696, by rfl⟩ : syracuseStep 695595 = 1043393) B1043393
theorem B695607 : Blo 694316 695607 := bstep (se 1 (by rfl) ⟨521705, by rfl⟩ : syracuseStep 695607 = 1043411) B1043411
theorem B1252673 : Blo 694316 1252673 := bstep (se 2 (by rfl) ⟨469752, by rfl⟩ : syracuseStep 1252673 = 939505) B939505
theorem B695627 : Blo 694316 695627 := bstep (se 1 (by rfl) ⟨521720, by rfl⟩ : syracuseStep 695627 = 1043441) B1043441
theorem B4529483 : Blo 694316 4529483 := bstep (se 1 (by rfl) ⟨3397112, by rfl⟩ : syracuseStep 4529483 = 6794225) B6794225
theorem B695639 : Blo 694316 695639 := bstep (se 1 (by rfl) ⟨521729, by rfl⟩ : syracuseStep 695639 = 1043459) B1043459
theorem B695659 : Blo 694316 695659 := bstep (se 1 (by rfl) ⟨521744, by rfl⟩ : syracuseStep 695659 = 1043489) B1043489
theorem B695671 : Blo 694316 695671 := bstep (se 1 (by rfl) ⟨521753, by rfl⟩ : syracuseStep 695671 = 1043507) B1043507
theorem B695691 : Blo 694316 695691 := bstep (se 1 (by rfl) ⟨521768, by rfl⟩ : syracuseStep 695691 = 1043537) B1043537
theorem B695703 : Blo 694316 695703 := bstep (se 1 (by rfl) ⟨521777, by rfl⟩ : syracuseStep 695703 = 1043555) B1043555
theorem B3972503 : Blo 694316 3972503 := bstep (se 1 (by rfl) ⟨2979377, by rfl⟩ : syracuseStep 3972503 = 5958755) B5958755
theorem B695723 : Blo 694316 695723 := bstep (se 1 (by rfl) ⟨521792, by rfl⟩ : syracuseStep 695723 = 1043585) B1043585
theorem B695735 : Blo 694316 695735 := bstep (se 1 (by rfl) ⟨521801, by rfl⟩ : syracuseStep 695735 = 1043603) B1043603
theorem B695755 : Blo 694316 695755 := bstep (se 1 (by rfl) ⟨521816, by rfl⟩ : syracuseStep 695755 = 1043633) B1043633
theorem B695767 : Blo 694316 695767 := bstep (se 1 (by rfl) ⟨521825, by rfl⟩ : syracuseStep 695767 = 1043651) B1043651
theorem B695787 : Blo 694316 695787 := bstep (se 1 (by rfl) ⟨521840, by rfl⟩ : syracuseStep 695787 = 1043681) B1043681
theorem B695799 : Blo 694316 695799 := bstep (se 1 (by rfl) ⟨521849, by rfl⟩ : syracuseStep 695799 = 1043699) B1043699
theorem B695819 : Blo 694316 695819 := bstep (se 1 (by rfl) ⟨521864, by rfl⟩ : syracuseStep 695819 = 1043729) B1043729
theorem B695831 : Blo 694316 695831 := bstep (se 1 (by rfl) ⟨521873, by rfl⟩ : syracuseStep 695831 = 1043747) B1043747
theorem B695851 : Blo 694316 695851 := bstep (se 1 (by rfl) ⟨521888, by rfl⟩ : syracuseStep 695851 = 1043777) B1043777
theorem B695863 : Blo 694316 695863 := bstep (se 1 (by rfl) ⟨521897, by rfl⟩ : syracuseStep 695863 = 1043795) B1043795
theorem B695883 : Blo 694316 695883 := bstep (se 1 (by rfl) ⟨521912, by rfl⟩ : syracuseStep 695883 = 1043825) B1043825
theorem B695895 : Blo 694316 695895 := bstep (se 1 (by rfl) ⟨521921, by rfl⟩ : syracuseStep 695895 = 1043843) B1043843
theorem B695915 : Blo 694316 695915 := bstep (se 1 (by rfl) ⟨521936, by rfl⟩ : syracuseStep 695915 = 1043873) B1043873
theorem B695927 : Blo 694316 695927 := bstep (se 1 (by rfl) ⟨521945, by rfl⟩ : syracuseStep 695927 = 1043891) B1043891
theorem B1056395 : Blo 694316 1056395 := bstep (se 1 (by rfl) ⟨792296, by rfl⟩ : syracuseStep 1056395 = 1584593) B1584593
theorem B695947 : Blo 694316 695947 := bstep (se 1 (by rfl) ⟨521960, by rfl⟩ : syracuseStep 695947 = 1043921) B1043921
theorem B695959 : Blo 694316 695959 := bstep (se 1 (by rfl) ⟨521969, by rfl⟩ : syracuseStep 695959 = 1043939) B1043939
theorem B695979 : Blo 694316 695979 := bstep (se 1 (by rfl) ⟨521984, by rfl⟩ : syracuseStep 695979 = 1043969) B1043969
theorem B695991 : Blo 694316 695991 := bstep (se 1 (by rfl) ⟨521993, by rfl⟩ : syracuseStep 695991 = 1043987) B1043987
theorem B696011 : Blo 694316 696011 := bstep (se 1 (by rfl) ⟨522008, by rfl⟩ : syracuseStep 696011 = 1044017) B1044017
theorem B696023 : Blo 694316 696023 := bstep (se 1 (by rfl) ⟨522017, by rfl⟩ : syracuseStep 696023 = 1044035) B1044035
theorem B696043 : Blo 694316 696043 := bstep (se 1 (by rfl) ⟨522032, by rfl⟩ : syracuseStep 696043 = 1044065) B1044065
theorem B696055 : Blo 694316 696055 := bstep (se 1 (by rfl) ⟨522041, by rfl⟩ : syracuseStep 696055 = 1044083) B1044083
theorem B696075 : Blo 694316 696075 := bstep (se 1 (by rfl) ⟨522056, by rfl⟩ : syracuseStep 696075 = 1044113) B1044113
theorem B696087 : Blo 694316 696087 := bstep (se 1 (by rfl) ⟨522065, by rfl⟩ : syracuseStep 696087 = 1044131) B1044131
theorem B696107 : Blo 694316 696107 := bstep (se 1 (by rfl) ⟨522080, by rfl⟩ : syracuseStep 696107 = 1044161) B1044161
theorem B696119 : Blo 694316 696119 := bstep (se 1 (by rfl) ⟨522089, by rfl⟩ : syracuseStep 696119 = 1044179) B1044179
theorem B696139 : Blo 694316 696139 := bstep (se 1 (by rfl) ⟨522104, by rfl⟩ : syracuseStep 696139 = 1044209) B1044209
theorem B696151 : Blo 694316 696151 := bstep (se 1 (by rfl) ⟨522113, by rfl⟩ : syracuseStep 696151 = 1044227) B1044227
theorem B696171 : Blo 694316 696171 := bstep (se 1 (by rfl) ⟨522128, by rfl⟩ : syracuseStep 696171 = 1044257) B1044257
theorem B696183 : Blo 694316 696183 := bstep (se 1 (by rfl) ⟨522137, by rfl⟩ : syracuseStep 696183 = 1044275) B1044275
theorem B696203 : Blo 694316 696203 := bstep (se 1 (by rfl) ⟨522152, by rfl⟩ : syracuseStep 696203 = 1044305) B1044305
theorem B696215 : Blo 694316 696215 := bstep (se 1 (by rfl) ⟨522161, by rfl⟩ : syracuseStep 696215 = 1044323) B1044323
theorem B696235 : Blo 694316 696235 := bstep (se 1 (by rfl) ⟨522176, by rfl⟩ : syracuseStep 696235 = 1044353) B1044353
theorem B696247 : Blo 694316 696247 := bstep (se 1 (by rfl) ⟨522185, by rfl⟩ : syracuseStep 696247 = 1044371) B1044371
theorem B1286081 : Blo 694316 1286081 := bstep (se 2 (by rfl) ⟨482280, by rfl⟩ : syracuseStep 1286081 = 964561) B964561
theorem B696267 : Blo 694316 696267 := bstep (se 1 (by rfl) ⟨522200, by rfl⟩ : syracuseStep 696267 = 1044401) B1044401
theorem B696279 : Blo 694316 696279 := bstep (se 1 (by rfl) ⟨522209, by rfl⟩ : syracuseStep 696279 = 1044419) B1044419
theorem B696299 : Blo 694316 696299 := bstep (se 1 (by rfl) ⟨522224, by rfl⟩ : syracuseStep 696299 = 1044449) B1044449
theorem B696311 : Blo 694316 696311 := bstep (se 1 (by rfl) ⟨522233, by rfl⟩ : syracuseStep 696311 = 1044467) B1044467
theorem B1318913 : Blo 694316 1318913 := bstep (se 2 (by rfl) ⟨494592, by rfl⟩ : syracuseStep 1318913 = 989185) B989185
theorem B696331 : Blo 694316 696331 := bstep (se 1 (by rfl) ⟨522248, by rfl⟩ : syracuseStep 696331 = 1044497) B1044497
theorem B696343 : Blo 694316 696343 := bstep (se 1 (by rfl) ⟨522257, by rfl⟩ : syracuseStep 696343 = 1044515) B1044515
theorem B696363 : Blo 694316 696363 := bstep (se 1 (by rfl) ⟨522272, by rfl⟩ : syracuseStep 696363 = 1044545) B1044545
theorem B696375 : Blo 694316 696375 := bstep (se 1 (by rfl) ⟨522281, by rfl⟩ : syracuseStep 696375 = 1044563) B1044563
theorem B696395 : Blo 694316 696395 := bstep (se 1 (by rfl) ⟨522296, by rfl⟩ : syracuseStep 696395 = 1044593) B1044593
theorem B696407 : Blo 694316 696407 := bstep (se 1 (by rfl) ⟨522305, by rfl⟩ : syracuseStep 696407 = 1044611) B1044611
theorem B696427 : Blo 694316 696427 := bstep (se 1 (by rfl) ⟨522320, by rfl⟩ : syracuseStep 696427 = 1044641) B1044641
theorem B696439 : Blo 694316 696439 := bstep (se 1 (by rfl) ⟨522329, by rfl⟩ : syracuseStep 696439 = 1044659) B1044659
theorem B696459 : Blo 694316 696459 := bstep (se 1 (by rfl) ⟨522344, by rfl⟩ : syracuseStep 696459 = 1044689) B1044689
theorem B696471 : Blo 694316 696471 := bstep (se 1 (by rfl) ⟨522353, by rfl⟩ : syracuseStep 696471 = 1044707) B1044707
theorem B696491 : Blo 694316 696491 := bstep (se 1 (by rfl) ⟨522368, by rfl⟩ : syracuseStep 696491 = 1044737) B1044737
theorem B696503 : Blo 694316 696503 := bstep (se 1 (by rfl) ⟨522377, by rfl⟩ : syracuseStep 696503 = 1044755) B1044755
theorem B991435 : Blo 694316 991435 := bstep (se 1 (by rfl) ⟨743576, by rfl⟩ : syracuseStep 991435 = 1487153) B1487153
theorem B696523 : Blo 694316 696523 := bstep (se 1 (by rfl) ⟨522392, by rfl⟩ : syracuseStep 696523 = 1044785) B1044785
theorem B696535 : Blo 694316 696535 := bstep (se 1 (by rfl) ⟨522401, by rfl⟩ : syracuseStep 696535 = 1044803) B1044803
theorem B696555 : Blo 694316 696555 := bstep (se 1 (by rfl) ⟨522416, by rfl⟩ : syracuseStep 696555 = 1044833) B1044833
theorem B696567 : Blo 694316 696567 := bstep (se 1 (by rfl) ⟨522425, by rfl⟩ : syracuseStep 696567 = 1044851) B1044851
theorem B1319179 : Blo 694316 1319179 := bstep (se 1 (by rfl) ⟨989384, by rfl⟩ : syracuseStep 1319179 = 1978769) B1978769
theorem B696587 : Blo 694316 696587 := bstep (se 1 (by rfl) ⟨522440, by rfl⟩ : syracuseStep 696587 = 1044881) B1044881
theorem B696599 : Blo 694316 696599 := bstep (se 1 (by rfl) ⟨522449, by rfl⟩ : syracuseStep 696599 = 1044899) B1044899
theorem B696619 : Blo 694316 696619 := bstep (se 1 (by rfl) ⟨522464, by rfl⟩ : syracuseStep 696619 = 1044929) B1044929
theorem B696631 : Blo 694316 696631 := bstep (se 1 (by rfl) ⟨522473, by rfl⟩ : syracuseStep 696631 = 1044947) B1044947
theorem B696651 : Blo 694316 696651 := bstep (se 1 (by rfl) ⟨522488, by rfl⟩ : syracuseStep 696651 = 1044977) B1044977
theorem B696663 : Blo 694316 696663 := bstep (se 1 (by rfl) ⟨522497, by rfl⟩ : syracuseStep 696663 = 1044995) B1044995
theorem B696683 : Blo 694316 696683 := bstep (se 1 (by rfl) ⟨522512, by rfl⟩ : syracuseStep 696683 = 1045025) B1045025
theorem B696695 : Blo 694316 696695 := bstep (se 1 (by rfl) ⟨522521, by rfl⟩ : syracuseStep 696695 = 1045043) B1045043
theorem B696715 : Blo 694316 696715 := bstep (se 1 (by rfl) ⟨522536, by rfl⟩ : syracuseStep 696715 = 1045073) B1045073
theorem B696727 : Blo 694316 696727 := bstep (se 1 (by rfl) ⟨522545, by rfl⟩ : syracuseStep 696727 = 1045091) B1045091
theorem B696747 : Blo 694316 696747 := bstep (se 1 (by rfl) ⟨522560, by rfl⟩ : syracuseStep 696747 = 1045121) B1045121
theorem B6693299 : Blo 694316 6693299 := bstep (se 1 (by rfl) ⟨5019974, by rfl⟩ : syracuseStep 6693299 = 10039949) B10039949
theorem B696759 : Blo 694316 696759 := bstep (se 1 (by rfl) ⟨522569, by rfl⟩ : syracuseStep 696759 = 1045139) B1045139
theorem B696779 : Blo 694316 696779 := bstep (se 1 (by rfl) ⟨522584, by rfl⟩ : syracuseStep 696779 = 1045169) B1045169
theorem B696791 : Blo 694316 696791 := bstep (se 1 (by rfl) ⟨522593, by rfl⟩ : syracuseStep 696791 = 1045187) B1045187
theorem B696811 : Blo 694316 696811 := bstep (se 1 (by rfl) ⟨522608, by rfl⟩ : syracuseStep 696811 = 1045217) B1045217
theorem B696823 : Blo 694316 696823 := bstep (se 1 (by rfl) ⟨522617, by rfl⟩ : syracuseStep 696823 = 1045235) B1045235
theorem B1483265 : Blo 694316 1483265 := bstep (se 2 (by rfl) ⟨556224, by rfl⟩ : syracuseStep 1483265 = 1112449) B1112449
theorem B696843 : Blo 694316 696843 := bstep (se 1 (by rfl) ⟨522632, by rfl⟩ : syracuseStep 696843 = 1045265) B1045265
theorem B696855 : Blo 694316 696855 := bstep (se 1 (by rfl) ⟨522641, by rfl⟩ : syracuseStep 696855 = 1045283) B1045283
theorem B696875 : Blo 694316 696875 := bstep (se 1 (by rfl) ⟨522656, by rfl⟩ : syracuseStep 696875 = 1045313) B1045313
theorem B696887 : Blo 694316 696887 := bstep (se 1 (by rfl) ⟨522665, by rfl⟩ : syracuseStep 696887 = 1045331) B1045331
theorem B696907 : Blo 694316 696907 := bstep (se 1 (by rfl) ⟨522680, by rfl⟩ : syracuseStep 696907 = 1045361) B1045361
theorem B696919 : Blo 694316 696919 := bstep (se 1 (by rfl) ⟨522689, by rfl⟩ : syracuseStep 696919 = 1045379) B1045379
theorem B2237021 : Blo 694316 2237021 := bstep (se 3 (by rfl) ⟨419441, by rfl⟩ : syracuseStep 2237021 = 838883) B838883
theorem B696939 : Blo 694316 696939 := bstep (se 1 (by rfl) ⟨522704, by rfl⟩ : syracuseStep 696939 = 1045409) B1045409
theorem B696951 : Blo 694316 696951 := bstep (se 1 (by rfl) ⟨522713, by rfl⟩ : syracuseStep 696951 = 1045427) B1045427
theorem B696971 : Blo 694316 696971 := bstep (se 1 (by rfl) ⟨522728, by rfl⟩ : syracuseStep 696971 = 1045457) B1045457
theorem B696983 : Blo 694316 696983 := bstep (se 1 (by rfl) ⟨522737, by rfl⟩ : syracuseStep 696983 = 1045475) B1045475
theorem B697003 : Blo 694316 697003 := bstep (se 1 (by rfl) ⟨522752, by rfl⟩ : syracuseStep 697003 = 1045505) B1045505
theorem B697015 : Blo 694316 697015 := bstep (se 1 (by rfl) ⟨522761, by rfl⟩ : syracuseStep 697015 = 1045523) B1045523
theorem B1319627 : Blo 694316 1319627 := bstep (se 1 (by rfl) ⟨989720, by rfl⟩ : syracuseStep 1319627 = 1979441) B1979441
theorem B697035 : Blo 694316 697035 := bstep (se 1 (by rfl) ⟨522776, by rfl⟩ : syracuseStep 697035 = 1045553) B1045553
theorem B697047 : Blo 694316 697047 := bstep (se 1 (by rfl) ⟨522785, by rfl⟩ : syracuseStep 697047 = 1045571) B1045571
theorem B697067 : Blo 694316 697067 := bstep (se 1 (by rfl) ⟨522800, by rfl⟩ : syracuseStep 697067 = 1045601) B1045601
theorem B697079 : Blo 694316 697079 := bstep (se 1 (by rfl) ⟨522809, by rfl⟩ : syracuseStep 697079 = 1045619) B1045619
theorem B697099 : Blo 694316 697099 := bstep (se 1 (by rfl) ⟨522824, by rfl⟩ : syracuseStep 697099 = 1045649) B1045649
theorem B697111 : Blo 694316 697111 := bstep (se 1 (by rfl) ⟨522833, by rfl⟩ : syracuseStep 697111 = 1045667) B1045667
theorem B697131 : Blo 694316 697131 := bstep (se 1 (by rfl) ⟨522848, by rfl⟩ : syracuseStep 697131 = 1045697) B1045697
theorem B21439285 : Blo 694316 21439285 := bstep (se 5 (by rfl) ⟨1004966, by rfl⟩ : syracuseStep 21439285 = 2009933) B2009933
theorem B697143 : Blo 694316 697143 := bstep (se 1 (by rfl) ⟨522857, by rfl⟩ : syracuseStep 697143 = 1045715) B1045715
theorem B697163 : Blo 694316 697163 := bstep (se 1 (by rfl) ⟨522872, by rfl⟩ : syracuseStep 697163 = 1045745) B1045745
theorem B697175 : Blo 694316 697175 := bstep (se 1 (by rfl) ⟨522881, by rfl⟩ : syracuseStep 697175 = 1045763) B1045763
theorem B697195 : Blo 694316 697195 := bstep (se 1 (by rfl) ⟨522896, by rfl⟩ : syracuseStep 697195 = 1045793) B1045793
theorem B697207 : Blo 694316 697207 := bstep (se 1 (by rfl) ⟨522905, by rfl⟩ : syracuseStep 697207 = 1045811) B1045811
theorem B1319809 : Blo 694316 1319809 := bstep (se 2 (by rfl) ⟨494928, by rfl⟩ : syracuseStep 1319809 = 989857) B989857
theorem B697227 : Blo 694316 697227 := bstep (se 1 (by rfl) ⟨522920, by rfl⟩ : syracuseStep 697227 = 1045841) B1045841
theorem B697239 : Blo 694316 697239 := bstep (se 1 (by rfl) ⟨522929, by rfl⟩ : syracuseStep 697239 = 1045859) B1045859
theorem B697259 : Blo 694316 697259 := bstep (se 1 (by rfl) ⟨522944, by rfl⟩ : syracuseStep 697259 = 1045889) B1045889
theorem B697271 : Blo 694316 697271 := bstep (se 1 (by rfl) ⟨522953, by rfl⟩ : syracuseStep 697271 = 1045907) B1045907
theorem B697291 : Blo 694316 697291 := bstep (se 1 (by rfl) ⟨522968, by rfl⟩ : syracuseStep 697291 = 1045937) B1045937
theorem B697303 : Blo 694316 697303 := bstep (se 1 (by rfl) ⟨522977, by rfl⟩ : syracuseStep 697303 = 1045955) B1045955
theorem B697323 : Blo 694316 697323 := bstep (se 1 (by rfl) ⟨522992, by rfl⟩ : syracuseStep 697323 = 1045985) B1045985
theorem B697335 : Blo 694316 697335 := bstep (se 1 (by rfl) ⟨523001, by rfl⟩ : syracuseStep 697335 = 1046003) B1046003
theorem B697355 : Blo 694316 697355 := bstep (se 1 (by rfl) ⟨523016, by rfl⟩ : syracuseStep 697355 = 1046033) B1046033
theorem B697367 : Blo 694316 697367 := bstep (se 1 (by rfl) ⟨523025, by rfl⟩ : syracuseStep 697367 = 1046051) B1046051
theorem B697387 : Blo 694316 697387 := bstep (se 1 (by rfl) ⟨523040, by rfl⟩ : syracuseStep 697387 = 1046081) B1046081
theorem B697399 : Blo 694316 697399 := bstep (se 1 (by rfl) ⟨523049, by rfl⟩ : syracuseStep 697399 = 1046099) B1046099
theorem B697419 : Blo 694316 697419 := bstep (se 1 (by rfl) ⟨523064, by rfl⟩ : syracuseStep 697419 = 1046129) B1046129
theorem B697431 : Blo 694316 697431 := bstep (se 1 (by rfl) ⟨523073, by rfl⟩ : syracuseStep 697431 = 1046147) B1046147
theorem B697451 : Blo 694316 697451 := bstep (se 1 (by rfl) ⟨523088, by rfl⟩ : syracuseStep 697451 = 1046177) B1046177
theorem B697463 : Blo 694316 697463 := bstep (se 1 (by rfl) ⟨523097, by rfl⟩ : syracuseStep 697463 = 1046195) B1046195
theorem B697483 : Blo 694316 697483 := bstep (se 1 (by rfl) ⟨523112, by rfl⟩ : syracuseStep 697483 = 1046225) B1046225
theorem B697495 : Blo 694316 697495 := bstep (se 1 (by rfl) ⟨523121, by rfl⟩ : syracuseStep 697495 = 1046243) B1046243
theorem B697515 : Blo 694316 697515 := bstep (se 1 (by rfl) ⟨523136, by rfl⟩ : syracuseStep 697515 = 1046273) B1046273
theorem B697527 : Blo 694316 697527 := bstep (se 1 (by rfl) ⟨523145, by rfl⟩ : syracuseStep 697527 = 1046291) B1046291
theorem B697547 : Blo 694316 697547 := bstep (se 1 (by rfl) ⟨523160, by rfl⟩ : syracuseStep 697547 = 1046321) B1046321
theorem B1320151 : Blo 694316 1320151 := bstep (se 1 (by rfl) ⟨990113, by rfl⟩ : syracuseStep 1320151 = 1980227) B1980227
theorem B697559 : Blo 694316 697559 := bstep (se 1 (by rfl) ⟨523169, by rfl⟩ : syracuseStep 697559 = 1046339) B1046339
theorem B697579 : Blo 694316 697579 := bstep (se 1 (by rfl) ⟨523184, by rfl⟩ : syracuseStep 697579 = 1046369) B1046369
theorem B697591 : Blo 694316 697591 := bstep (se 1 (by rfl) ⟨523193, by rfl⟩ : syracuseStep 697591 = 1046387) B1046387
theorem B697611 : Blo 694316 697611 := bstep (se 1 (by rfl) ⟨523208, by rfl⟩ : syracuseStep 697611 = 1046417) B1046417
theorem B3974417 : Blo 694316 3974417 := bstep (se 2 (by rfl) ⟨1490406, by rfl⟩ : syracuseStep 3974417 = 2980813) B2980813
theorem B697623 : Blo 694316 697623 := bstep (se 1 (by rfl) ⟨523217, by rfl⟩ : syracuseStep 697623 = 1046435) B1046435
theorem B697643 : Blo 694316 697643 := bstep (se 1 (by rfl) ⟨523232, by rfl⟩ : syracuseStep 697643 = 1046465) B1046465
theorem B697655 : Blo 694316 697655 := bstep (se 1 (by rfl) ⟨523241, by rfl⟩ : syracuseStep 697655 = 1046483) B1046483
theorem B3515723 : Blo 694316 3515723 := bstep (se 1 (by rfl) ⟨2636792, by rfl⟩ : syracuseStep 3515723 = 5273585) B5273585
theorem B697675 : Blo 694316 697675 := bstep (se 1 (by rfl) ⟨523256, by rfl⟩ : syracuseStep 697675 = 1046513) B1046513
theorem B1484119 : Blo 694316 1484119 := bstep (se 1 (by rfl) ⟨1113089, by rfl⟩ : syracuseStep 1484119 = 2226179) B2226179
theorem B697687 : Blo 694316 697687 := bstep (se 1 (by rfl) ⟨523265, by rfl⟩ : syracuseStep 697687 = 1046531) B1046531
theorem B697707 : Blo 694316 697707 := bstep (se 1 (by rfl) ⟨523280, by rfl⟩ : syracuseStep 697707 = 1046561) B1046561
theorem B697719 : Blo 694316 697719 := bstep (se 1 (by rfl) ⟨523289, by rfl⟩ : syracuseStep 697719 = 1046579) B1046579
theorem B697739 : Blo 694316 697739 := bstep (se 1 (by rfl) ⟨523304, by rfl⟩ : syracuseStep 697739 = 1046609) B1046609
theorem B697751 : Blo 694316 697751 := bstep (se 1 (by rfl) ⟨523313, by rfl⟩ : syracuseStep 697751 = 1046627) B1046627
theorem B992665 : Blo 694316 992665 := bstep (se 2 (by rfl) ⟨372249, by rfl⟩ : syracuseStep 992665 = 744499) B744499
theorem B697771 : Blo 694316 697771 := bstep (se 1 (by rfl) ⟨523328, by rfl⟩ : syracuseStep 697771 = 1046657) B1046657
theorem B1320371 : Blo 694316 1320371 := bstep (se 1 (by rfl) ⟨990278, by rfl⟩ : syracuseStep 1320371 = 1980557) B1980557
theorem B697783 : Blo 694316 697783 := bstep (se 1 (by rfl) ⟨523337, by rfl⟩ : syracuseStep 697783 = 1046675) B1046675
theorem B697803 : Blo 694316 697803 := bstep (se 1 (by rfl) ⟨523352, by rfl⟩ : syracuseStep 697803 = 1046705) B1046705
theorem B697815 : Blo 694316 697815 := bstep (se 1 (by rfl) ⟨523361, by rfl⟩ : syracuseStep 697815 = 1046723) B1046723
theorem B697835 : Blo 694316 697835 := bstep (se 1 (by rfl) ⟨523376, by rfl⟩ : syracuseStep 697835 = 1046753) B1046753
theorem B697847 : Blo 694316 697847 := bstep (se 1 (by rfl) ⟨523385, by rfl⟩ : syracuseStep 697847 = 1046771) B1046771
theorem B1254923 : Blo 694316 1254923 := bstep (se 1 (by rfl) ⟨941192, by rfl⟩ : syracuseStep 1254923 = 1882385) B1882385
theorem B697867 : Blo 694316 697867 := bstep (se 1 (by rfl) ⟨523400, by rfl⟩ : syracuseStep 697867 = 1046801) B1046801
theorem B697879 : Blo 694316 697879 := bstep (se 1 (by rfl) ⟨523409, by rfl⟩ : syracuseStep 697879 = 1046819) B1046819
theorem B697899 : Blo 694316 697899 := bstep (se 1 (by rfl) ⟨523424, by rfl⟩ : syracuseStep 697899 = 1046849) B1046849
theorem B697911 : Blo 694316 697911 := bstep (se 1 (by rfl) ⟨523433, by rfl⟩ : syracuseStep 697911 = 1046867) B1046867
theorem B697931 : Blo 694316 697931 := bstep (se 1 (by rfl) ⟨523448, by rfl⟩ : syracuseStep 697931 = 1046897) B1046897
theorem B697943 : Blo 694316 697943 := bstep (se 1 (by rfl) ⟨523457, by rfl⟩ : syracuseStep 697943 = 1046915) B1046915
theorem B697963 : Blo 694316 697963 := bstep (se 1 (by rfl) ⟨523472, by rfl⟩ : syracuseStep 697963 = 1046945) B1046945
theorem B697975 : Blo 694316 697975 := bstep (se 1 (by rfl) ⟨523481, by rfl⟩ : syracuseStep 697975 = 1046963) B1046963
theorem B697995 : Blo 694316 697995 := bstep (se 1 (by rfl) ⟨523496, by rfl⟩ : syracuseStep 697995 = 1046993) B1046993
theorem B1320599 : Blo 694316 1320599 := bstep (se 1 (by rfl) ⟨990449, by rfl⟩ : syracuseStep 1320599 = 1980899) B1980899
theorem B698007 : Blo 694316 698007 := bstep (se 1 (by rfl) ⟨523505, by rfl⟩ : syracuseStep 698007 = 1047011) B1047011
theorem B698027 : Blo 694316 698027 := bstep (se 1 (by rfl) ⟨523520, by rfl⟩ : syracuseStep 698027 = 1047041) B1047041
theorem B698039 : Blo 694316 698039 := bstep (se 1 (by rfl) ⟨523529, by rfl⟩ : syracuseStep 698039 = 1047059) B1047059
theorem B698059 : Blo 694316 698059 := bstep (se 1 (by rfl) ⟨523544, by rfl⟩ : syracuseStep 698059 = 1047089) B1047089
theorem B698071 : Blo 694316 698071 := bstep (se 1 (by rfl) ⟨523553, by rfl⟩ : syracuseStep 698071 = 1047107) B1047107
theorem B698091 : Blo 694316 698091 := bstep (se 1 (by rfl) ⟨523568, by rfl⟩ : syracuseStep 698091 = 1047137) B1047137
theorem B698103 : Blo 694316 698103 := bstep (se 1 (by rfl) ⟨523577, by rfl⟩ : syracuseStep 698103 = 1047155) B1047155
theorem B698123 : Blo 694316 698123 := bstep (se 1 (by rfl) ⟨523592, by rfl⟩ : syracuseStep 698123 = 1047185) B1047185
theorem B698135 : Blo 694316 698135 := bstep (se 1 (by rfl) ⟨523601, by rfl⟩ : syracuseStep 698135 = 1047203) B1047203
theorem B698155 : Blo 694316 698155 := bstep (se 1 (by rfl) ⟨523616, by rfl⟩ : syracuseStep 698155 = 1047233) B1047233
theorem B698167 : Blo 694316 698167 := bstep (se 1 (by rfl) ⟨523625, by rfl⟩ : syracuseStep 698167 = 1047251) B1047251
theorem B698187 : Blo 694316 698187 := bstep (se 1 (by rfl) ⟨523640, by rfl⟩ : syracuseStep 698187 = 1047281) B1047281
theorem B698199 : Blo 694316 698199 := bstep (se 1 (by rfl) ⟨523649, by rfl⟩ : syracuseStep 698199 = 1047299) B1047299
theorem B698219 : Blo 694316 698219 := bstep (se 1 (by rfl) ⟨523664, by rfl⟩ : syracuseStep 698219 = 1047329) B1047329
theorem B698231 : Blo 694316 698231 := bstep (se 1 (by rfl) ⟨523673, by rfl⟩ : syracuseStep 698231 = 1047347) B1047347
theorem B698251 : Blo 694316 698251 := bstep (se 1 (by rfl) ⟨523688, by rfl⟩ : syracuseStep 698251 = 1047377) B1047377
theorem B698263 : Blo 694316 698263 := bstep (se 1 (by rfl) ⟨523697, by rfl⟩ : syracuseStep 698263 = 1047395) B1047395
theorem B1320857 : Blo 694316 1320857 := bstep (se 2 (by rfl) ⟨495321, by rfl⟩ : syracuseStep 1320857 = 990643) B990643
theorem B698283 : Blo 694316 698283 := bstep (se 1 (by rfl) ⟨523712, by rfl⟩ : syracuseStep 698283 = 1047425) B1047425
theorem B698295 : Blo 694316 698295 := bstep (se 1 (by rfl) ⟨523721, by rfl⟩ : syracuseStep 698295 = 1047443) B1047443
theorem B698315 : Blo 694316 698315 := bstep (se 1 (by rfl) ⟨523736, by rfl⟩ : syracuseStep 698315 = 1047473) B1047473
theorem B1484939 : Blo 694316 1484939 := bstep (se 1 (by rfl) ⟨1113704, by rfl⟩ : syracuseStep 1484939 = 2227409) B2227409
theorem B1878167 : Blo 694316 1878167 := bstep (se 1 (by rfl) ⟨1408625, by rfl⟩ : syracuseStep 1878167 = 2817251) B2817251
theorem B15050933 : Blo 694316 15050933 := bstep (se 5 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 15050933 = 1411025) B1411025
theorem B993559 : Blo 694316 993559 := bstep (se 1 (by rfl) ⟨745169, by rfl⟩ : syracuseStep 993559 = 1490339) B1490339
theorem B3352877 : Blo 694316 3352877 := bstep (se 3 (by rfl) ⟨628664, by rfl⟩ : syracuseStep 3352877 = 1257329) B1257329
theorem B1321267 : Blo 694316 1321267 := bstep (se 1 (by rfl) ⟨990950, by rfl⟩ : syracuseStep 1321267 = 1981901) B1981901
theorem B895639 : Blo 694316 895639 := bstep (se 1 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 895639 = 1343459) B1343459
theorem B1321753 : Blo 694316 1321753 := bstep (se 2 (by rfl) ⟨495657, by rfl⟩ : syracuseStep 1321753 = 991315) B991315
theorem B5024587 : Blo 694316 5024587 := bstep (se 1 (by rfl) ⟨3768440, by rfl⟩ : syracuseStep 5024587 = 7536881) B7536881
theorem B994123 : Blo 694316 994123 := bstep (se 1 (by rfl) ⟨745592, by rfl⟩ : syracuseStep 994123 = 1491185) B1491185
theorem B1977367 : Blo 694316 1977367 := bstep (se 1 (by rfl) ⟨1483025, by rfl⟩ : syracuseStep 1977367 = 2966051) B2966051
theorem B3517505 : Blo 694316 3517505 := bstep (se 2 (by rfl) ⟨1319064, by rfl⟩ : syracuseStep 3517505 = 2638129) B2638129
theorem B1322315 : Blo 694316 1322315 := bstep (se 1 (by rfl) ⟨991736, by rfl⟩ : syracuseStep 1322315 = 1983473) B1983473
theorem B1322497 : Blo 694316 1322497 := bstep (se 2 (by rfl) ⟨495936, by rfl⟩ : syracuseStep 1322497 = 991873) B991873
theorem B7941725 : Blo 694316 7941725 := bstep (se 3 (by rfl) ⟨1489073, by rfl⟩ : syracuseStep 7941725 = 2978147) B2978147
theorem B2142359 : Blo 694316 2142359 := bstep (se 1 (by rfl) ⟨1606769, by rfl⟩ : syracuseStep 2142359 = 3213539) B3213539
theorem B1880243 : Blo 694316 1880243 := bstep (se 1 (by rfl) ⟨1410182, by rfl⟩ : syracuseStep 1880243 = 2820365) B2820365
theorem B1323211 : Blo 694316 1323211 := bstep (se 1 (by rfl) ⟨992408, by rfl⟩ : syracuseStep 1323211 = 1984817) B1984817
theorem B10170629 : Blo 694316 10170629 := bstep (se 4 (by rfl) ⟨953496, by rfl⟩ : syracuseStep 10170629 = 1906993) B1906993
theorem B1323287 : Blo 694316 1323287 := bstep (se 1 (by rfl) ⟨992465, by rfl⟩ : syracuseStep 1323287 = 1984931) B1984931
theorem B1487297 : Blo 694316 1487297 := bstep (se 2 (by rfl) ⟨557736, by rfl⟩ : syracuseStep 1487297 = 1115473) B1115473
theorem B1487639 : Blo 694316 1487639 := bstep (se 1 (by rfl) ⟨1115729, by rfl⟩ : syracuseStep 1487639 = 2231459) B2231459
theorem B5649227 : Blo 694316 5649227 := bstep (se 1 (by rfl) ⟨4236920, by rfl⟩ : syracuseStep 5649227 = 8473841) B8473841
theorem B1979225 : Blo 694316 1979225 := bstep (se 2 (by rfl) ⟨742209, by rfl⟩ : syracuseStep 1979225 = 1484419) B1484419
theorem B1323955 : Blo 694316 1323955 := bstep (se 1 (by rfl) ⟨992966, by rfl⟩ : syracuseStep 1323955 = 1985933) B1985933
theorem B6042547 : Blo 694316 6042547 := bstep (se 1 (by rfl) ⟨4531910, by rfl⟩ : syracuseStep 6042547 = 9063821) B9063821
theorem B3519449 : Blo 694316 3519449 := bstep (se 2 (by rfl) ⟨1319793, by rfl⟩ : syracuseStep 3519449 = 2639587) B2639587
theorem B1324183 : Blo 694316 1324183 := bstep (se 1 (by rfl) ⟨993137, by rfl⟩ : syracuseStep 1324183 = 1986275) B1986275
theorem B5289137 : Blo 694316 5289137 := bstep (se 2 (by rfl) ⟨1983426, by rfl⟩ : syracuseStep 5289137 = 3966853) B3966853
theorem B1324289 : Blo 694316 1324289 := bstep (se 2 (by rfl) ⟨496608, by rfl⟩ : syracuseStep 1324289 = 993217) B993217
theorem B1488203 : Blo 694316 1488203 := bstep (se 1 (by rfl) ⟨1116152, by rfl⟩ : syracuseStep 1488203 = 2232305) B2232305
theorem B1324441 : Blo 694316 1324441 := bstep (se 2 (by rfl) ⟨496665, by rfl⟩ : syracuseStep 1324441 = 993331) B993331
theorem B1980055 : Blo 694316 1980055 := bstep (se 1 (by rfl) ⟨1485041, by rfl⟩ : syracuseStep 1980055 = 2970083) B2970083
theorem B5289623 : Blo 694316 5289623 := bstep (se 1 (by rfl) ⟨3967217, by rfl⟩ : syracuseStep 5289623 = 7934435) B7934435
theorem B1488793 : Blo 694316 1488793 := bstep (se 2 (by rfl) ⟨558297, by rfl⟩ : syracuseStep 1488793 = 1116595) B1116595
theorem B3094451 : Blo 694316 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B4470707 : Blo 694316 4470707 := bstep (se 1 (by rfl) ⟨3353030, by rfl⟩ : syracuseStep 4470707 = 6706061) B6706061
theorem B1980875 : Blo 694316 1980875 := bstep (se 1 (by rfl) ⟨1485656, by rfl⟩ : syracuseStep 1980875 = 2971313) B2971313
theorem B3521069 : Blo 694316 3521069 := bstep (se 3 (by rfl) ⟨660200, by rfl⟩ : syracuseStep 3521069 = 1320401) B1320401
theorem B1489843 : Blo 694316 1489843 := bstep (se 1 (by rfl) ⟨1117382, by rfl⟩ : syracuseStep 1489843 = 2234765) B2234765
theorem B5946317 : Blo 694316 5946317 := bstep (se 3 (by rfl) ⟨1114934, by rfl⟩ : syracuseStep 5946317 = 2229869) B2229869
theorem B2505779 : Blo 694316 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B2636945 : Blo 694316 2636945 := bstep (se 2 (by rfl) ⟨988854, by rfl⟩ : syracuseStep 2636945 = 1977709) B1977709
theorem B2506457 : Blo 694316 2506457 := bstep (se 2 (by rfl) ⟨939921, by rfl⟩ : syracuseStep 2506457 = 1879843) B1879843
theorem B2113303 : Blo 694316 2113303 := bstep (se 1 (by rfl) ⟨1584977, by rfl⟩ : syracuseStep 2113303 = 3169955) B3169955
theorem B2637643 : Blo 694316 2637643 := bstep (se 1 (by rfl) ⟨1978232, by rfl⟩ : syracuseStep 2637643 = 3956465) B3956465
theorem B2506585 : Blo 694316 2506585 := bstep (se 2 (by rfl) ⟨939969, by rfl⟩ : syracuseStep 2506585 = 1879939) B1879939
theorem B8044505 : Blo 694316 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B7520273 : Blo 694316 7520273 := bstep (se 2 (by rfl) ⟨2820102, by rfl⟩ : syracuseStep 7520273 = 5640205) B5640205
theorem B2637917 : Blo 694316 2637917 := bstep (se 3 (by rfl) ⟨494609, by rfl⟩ : syracuseStep 2637917 = 989219) B989219
theorem B1130635 : Blo 694316 1130635 := bstep (se 1 (by rfl) ⟨847976, by rfl⟩ : syracuseStep 1130635 = 1695953) B1695953
theorem B21479575 : Blo 694316 21479575 := bstep (se 1 (by rfl) ⟨16109681, by rfl⟩ : syracuseStep 21479575 = 32219363) B32219363
theorem B5030237 : Blo 694316 5030237 := bstep (se 3 (by rfl) ⟨943169, by rfl⟩ : syracuseStep 5030237 = 1886339) B1886339
theorem B1491329 : Blo 694316 1491329 := bstep (se 2 (by rfl) ⟨559248, by rfl⟩ : syracuseStep 1491329 = 1118497) B1118497
theorem B2638615 : Blo 694316 2638615 := bstep (se 1 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 2638615 = 3957923) B3957923
theorem B5653313 : Blo 694316 5653313 := bstep (se 2 (by rfl) ⟨2119992, by rfl⟩ : syracuseStep 5653313 = 4239985) B4239985
theorem B1983325 : Blo 694316 1983325 := bstep (se 3 (by rfl) ⟨371873, by rfl⟩ : syracuseStep 1983325 = 743747) B743747
theorem B705431 : Blo 694316 705431 := bstep (se 1 (by rfl) ⟨529073, by rfl⟩ : syracuseStep 705431 = 1058147) B1058147
theorem B1590359 : Blo 694316 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B705655 : Blo 694316 705655 := bstep (se 1 (by rfl) ⟨529241, by rfl⟩ : syracuseStep 705655 = 1058483) B1058483
theorem B2344139 : Blo 694316 2344139 := bstep (se 1 (by rfl) ⟨1758104, by rfl⟩ : syracuseStep 2344139 = 3516209) B3516209
theorem B2344409 : Blo 694316 2344409 := bstep (se 2 (by rfl) ⟨879153, by rfl⟩ : syracuseStep 2344409 = 1758307) B1758307
theorem B2639405 : Blo 694316 2639405 := bstep (se 3 (by rfl) ⟨494888, by rfl⟩ : syracuseStep 2639405 = 989777) B989777
theorem B4769381 : Blo 694316 4769381 := bstep (se 4 (by rfl) ⟨447129, by rfl⟩ : syracuseStep 4769381 = 894259) B894259
theorem B837335 : Blo 694316 837335 := bstep (se 1 (by rfl) ⟨628001, by rfl⟩ : syracuseStep 837335 = 1256003) B1256003
theorem B3753803 : Blo 694316 3753803 := bstep (se 1 (by rfl) ⟨2815352, by rfl⟩ : syracuseStep 3753803 = 5630705) B5630705
theorem B7915481 : Blo 694316 7915481 := bstep (se 2 (by rfl) ⟨2968305, by rfl⟩ : syracuseStep 7915481 = 5936611) B5936611
theorem B837643 : Blo 694316 837643 := bstep (se 1 (by rfl) ⟨628232, by rfl⟩ : syracuseStep 837643 = 1256465) B1256465
theorem B20400149 : Blo 694316 20400149 := bstep (se 6 (by rfl) ⟨478128, by rfl⟩ : syracuseStep 20400149 = 956257) B956257
theorem B3819595 : Blo 694316 3819595 := bstep (se 1 (by rfl) ⟨2864696, by rfl⟩ : syracuseStep 3819595 = 5729393) B5729393
theorem B1984601 : Blo 694316 1984601 := bstep (se 2 (by rfl) ⟨744225, by rfl⟩ : syracuseStep 1984601 = 1488451) B1488451
theorem B2508893 : Blo 694316 2508893 := bstep (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) B940835
theorem B2345111 : Blo 694316 2345111 := bstep (se 1 (by rfl) ⟨1758833, by rfl⟩ : syracuseStep 2345111 = 3517667) B3517667
theorem B2672833 : Blo 694316 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B706891 : Blo 694316 706891 := bstep (se 1 (by rfl) ⟨530168, by rfl⟩ : syracuseStep 706891 = 1060337) B1060337
theorem B3524957 : Blo 694316 3524957 := bstep (se 3 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 3524957 = 1321859) B1321859
theorem B2115991 : Blo 694316 2115991 := bstep (se 1 (by rfl) ⟨1586993, by rfl⟩ : syracuseStep 2115991 = 3173987) B3173987
theorem B2345651 : Blo 694316 2345651 := bstep (se 1 (by rfl) ⟨1759238, by rfl⟩ : syracuseStep 2345651 = 3518477) B3518477
theorem B1592075 : Blo 694316 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B2509699 : Blo 694316 2509699 := bstep (se 1 (by rfl) ⟨1882274, by rfl⟩ : syracuseStep 2509699 = 3764549) B3764549
theorem B2345921 : Blo 694316 2345921 := bstep (se 2 (by rfl) ⟨879720, by rfl⟩ : syracuseStep 2345921 = 1759441) B1759441
theorem B2640833 : Blo 694316 2640833 := bstep (se 2 (by rfl) ⟨990312, by rfl⟩ : syracuseStep 2640833 = 1980625) B1980625
theorem B2968579 : Blo 694316 2968579 := bstep (se 1 (by rfl) ⟨2226434, by rfl⟩ : syracuseStep 2968579 = 4452869) B4452869
theorem B2510045 : Blo 694316 2510045 := bstep (se 3 (by rfl) ⟨470633, by rfl⟩ : syracuseStep 2510045 = 941267) B941267
theorem B2346461 : Blo 694316 2346461 := bstep (se 3 (by rfl) ⟨439961, by rfl⟩ : syracuseStep 2346461 = 879923) B879923
theorem B2117171 : Blo 694316 2117171 := bstep (se 1 (by rfl) ⟨1587878, by rfl⟩ : syracuseStep 2117171 = 3175757) B3175757
theorem B5951069 : Blo 694316 5951069 := bstep (se 3 (by rfl) ⟨1115825, by rfl⟩ : syracuseStep 5951069 = 2231651) B2231651
theorem B1986241 : Blo 694316 1986241 := bstep (se 2 (by rfl) ⟨744840, by rfl⟩ : syracuseStep 1986241 = 1489681) B1489681
theorem B8933165 : Blo 694316 8933165 := bstep (se 3 (by rfl) ⟨1674968, by rfl⟩ : syracuseStep 8933165 = 3349937) B3349937
theorem B10047557 : Blo 694316 10047557 := bstep (se 4 (by rfl) ⟨941958, by rfl⟩ : syracuseStep 10047557 = 1883917) B1883917
theorem B4772171 : Blo 694316 4772171 := bstep (se 1 (by rfl) ⟨3579128, by rfl⟩ : syracuseStep 4772171 = 7158257) B7158257
theorem B2642321 : Blo 694316 2642321 := bstep (se 2 (by rfl) ⟨990870, by rfl⟩ : syracuseStep 2642321 = 1981741) B1981741
theorem B3527063 : Blo 694316 3527063 := bstep (se 1 (by rfl) ⟨2645297, by rfl⟩ : syracuseStep 3527063 = 5290595) B5290595
theorem B741803 : Blo 694316 741803 := bstep (se 1 (by rfl) ⟨556352, by rfl⟩ : syracuseStep 741803 = 1112705) B1112705
theorem B1757771 : Blo 694316 1757771 := bstep (se 1 (by rfl) ⟨1318328, by rfl⟩ : syracuseStep 1757771 = 2636657) B2636657
theorem B2347595 : Blo 694316 2347595 := bstep (se 1 (by rfl) ⟨1760696, by rfl⟩ : syracuseStep 2347595 = 3521393) B3521393
theorem B14471885 : Blo 694316 14471885 := bstep (se 3 (by rfl) ⟨2713478, by rfl⟩ : syracuseStep 14471885 = 5426957) B5426957
theorem B5296913 : Blo 694316 5296913 := bstep (se 2 (by rfl) ⟨1986342, by rfl⟩ : syracuseStep 5296913 = 3972685) B3972685
theorem B2970391 : Blo 694316 2970391 := bstep (se 1 (by rfl) ⟨2227793, by rfl⟩ : syracuseStep 2970391 = 4455587) B4455587
theorem B24171317 : Blo 694316 24171317 := bstep (se 5 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 24171317 = 2266061) B2266061
theorem B2347865 : Blo 694316 2347865 := bstep (se 2 (by rfl) ⟨880449, by rfl⟩ : syracuseStep 2347865 = 1760899) B1760899
theorem B2642777 : Blo 694316 2642777 := bstep (se 2 (by rfl) ⟨991041, by rfl⟩ : syracuseStep 2642777 = 1982083) B1982083
theorem B1758145 : Blo 694316 1758145 := bstep (se 2 (by rfl) ⟨659304, by rfl⟩ : syracuseStep 1758145 = 1318609) B1318609
theorem B2642989 : Blo 694316 2642989 := bstep (se 3 (by rfl) ⟨495560, by rfl⟩ : syracuseStep 2642989 = 991121) B991121
theorem B1987915 : Blo 694316 1987915 := bstep (se 1 (by rfl) ⟨1490936, by rfl⟩ : syracuseStep 1987915 = 2981873) B2981873
theorem B2643293 : Blo 694316 2643293 := bstep (se 3 (by rfl) ⟨495617, by rfl⟩ : syracuseStep 2643293 = 991235) B991235
theorem B2971025 : Blo 694316 2971025 := bstep (se 2 (by rfl) ⟨1114134, by rfl⟩ : syracuseStep 2971025 = 2228269) B2228269
theorem B1758743 : Blo 694316 1758743 := bstep (se 1 (by rfl) ⟨1319057, by rfl⟩ : syracuseStep 1758743 = 2638115) B2638115
theorem B2348567 : Blo 694316 2348567 := bstep (se 1 (by rfl) ⟨1761425, by rfl⟩ : syracuseStep 2348567 = 3522851) B3522851
theorem B1988189 : Blo 694316 1988189 := bstep (se 3 (by rfl) ⟨372785, by rfl⟩ : syracuseStep 1988189 = 745571) B745571
theorem B1562291 : Blo 694316 1562291 := bstep (se 1 (by rfl) ⟨1171718, by rfl⟩ : syracuseStep 1562291 = 2343437) B2343437
theorem B1005259 : Blo 694316 1005259 := bstep (se 1 (by rfl) ⟨753944, by rfl⟩ : syracuseStep 1005259 = 1507889) B1507889
theorem B1562327 : Blo 694316 1562327 := bstep (se 1 (by rfl) ⟨1171745, by rfl⟩ : syracuseStep 1562327 = 2343491) B2343491
theorem B1562507 : Blo 694316 1562507 := bstep (se 1 (by rfl) ⟨1171880, by rfl⟩ : syracuseStep 1562507 = 2343761) B2343761
theorem B1562561 : Blo 694316 1562561 := bstep (se 2 (by rfl) ⟨585960, by rfl⟩ : syracuseStep 1562561 = 1171921) B1171921
theorem B2349107 : Blo 694316 2349107 := bstep (se 1 (by rfl) ⟨1761830, by rfl⟩ : syracuseStep 2349107 = 3523661) B3523661
theorem B2971723 : Blo 694316 2971723 := bstep (se 1 (by rfl) ⟨2228792, by rfl⟩ : syracuseStep 2971723 = 4457585) B4457585
theorem B743563 : Blo 694316 743563 := bstep (se 1 (by rfl) ⟨557672, by rfl⟩ : syracuseStep 743563 = 1115345) B1115345
theorem B1562777 : Blo 694316 1562777 := bstep (se 2 (by rfl) ⟨586041, by rfl⟩ : syracuseStep 1562777 = 1172083) B1172083
theorem B1562867 : Blo 694316 1562867 := bstep (se 1 (by rfl) ⟨1172150, by rfl⟩ : syracuseStep 1562867 = 2344301) B2344301
theorem B1562903 : Blo 694316 1562903 := bstep (se 1 (by rfl) ⟨1172177, by rfl⟩ : syracuseStep 1562903 = 2344355) B2344355
theorem B1759553 : Blo 694316 1759553 := bstep (se 2 (by rfl) ⟨659832, by rfl⟩ : syracuseStep 1759553 = 1319665) B1319665
theorem B2349377 : Blo 694316 2349377 := bstep (se 2 (by rfl) ⟨881016, by rfl⟩ : syracuseStep 2349377 = 1762033) B1762033
theorem B2971997 : Blo 694316 2971997 := bstep (se 3 (by rfl) ⟨557249, by rfl⟩ : syracuseStep 2971997 = 1114499) B1114499
theorem B3627443 : Blo 694316 3627443 := bstep (se 1 (by rfl) ⟨2720582, by rfl⟩ : syracuseStep 3627443 = 5441165) B5441165
theorem B1563083 : Blo 694316 1563083 := bstep (se 1 (by rfl) ⟨1172312, by rfl⟩ : syracuseStep 1563083 = 2344625) B2344625
theorem B4282841 : Blo 694316 4282841 := bstep (se 2 (by rfl) ⟨1606065, by rfl⟩ : syracuseStep 4282841 = 3212131) B3212131
theorem B1563137 : Blo 694316 1563137 := bstep (se 2 (by rfl) ⟨586176, by rfl⟩ : syracuseStep 1563137 = 1172353) B1172353
theorem B2972339 : Blo 694316 2972339 := bstep (se 1 (by rfl) ⟨2229254, by rfl⟩ : syracuseStep 2972339 = 4458509) B4458509
theorem B1563353 : Blo 694316 1563353 := bstep (se 2 (by rfl) ⟨586257, by rfl⟩ : syracuseStep 1563353 = 1172515) B1172515
theorem B5659409 : Blo 694316 5659409 := bstep (se 2 (by rfl) ⟨2122278, by rfl⟩ : syracuseStep 5659409 = 4244557) B4244557
theorem B6773549 : Blo 694316 6773549 := bstep (se 3 (by rfl) ⟨1270040, by rfl⟩ : syracuseStep 6773549 = 2540081) B2540081
theorem B1563443 : Blo 694316 1563443 := bstep (se 1 (by rfl) ⟨1172582, by rfl⟩ : syracuseStep 1563443 = 2345165) B2345165
theorem B1563479 : Blo 694316 1563479 := bstep (se 1 (by rfl) ⟨1172609, by rfl⟩ : syracuseStep 1563479 = 2345219) B2345219
theorem B1760089 : Blo 694316 1760089 := bstep (se 2 (by rfl) ⟨660033, by rfl⟩ : syracuseStep 1760089 = 1320067) B1320067
theorem B2349917 : Blo 694316 2349917 := bstep (se 3 (by rfl) ⟨440609, by rfl⟩ : syracuseStep 2349917 = 881219) B881219
theorem B2677697 : Blo 694316 2677697 := bstep (se 2 (by rfl) ⟨1004136, by rfl⟩ : syracuseStep 2677697 = 2008273) B2008273
theorem B1563659 : Blo 694316 1563659 := bstep (se 1 (by rfl) ⟨1172744, by rfl⟩ : syracuseStep 1563659 = 2345489) B2345489
theorem B1563713 : Blo 694316 1563713 := bstep (se 2 (by rfl) ⟨586392, by rfl⟩ : syracuseStep 1563713 = 1172785) B1172785
theorem B5659865 : Blo 694316 5659865 := bstep (se 2 (by rfl) ⟨2122449, by rfl⟩ : syracuseStep 5659865 = 4244899) B4244899
theorem B1563929 : Blo 694316 1563929 := bstep (se 2 (by rfl) ⟨586473, by rfl⟩ : syracuseStep 1563929 = 1172947) B1172947
theorem B1564019 : Blo 694316 1564019 := bstep (se 1 (by rfl) ⟨1173014, by rfl⟩ : syracuseStep 1564019 = 2346029) B2346029
theorem B1564055 : Blo 694316 1564055 := bstep (se 1 (by rfl) ⟨1173041, by rfl⟩ : syracuseStep 1564055 = 2346083) B2346083
theorem B3857843 : Blo 694316 3857843 := bstep (se 1 (by rfl) ⟨2893382, by rfl⟩ : syracuseStep 3857843 = 5786765) B5786765
theorem B3956147 : Blo 694316 3956147 := bstep (se 1 (by rfl) ⟨2967110, by rfl⟩ : syracuseStep 3956147 = 5934221) B5934221
theorem B1564235 : Blo 694316 1564235 := bstep (se 1 (by rfl) ⟨1173176, by rfl⟩ : syracuseStep 1564235 = 2346353) B2346353
theorem B1564289 : Blo 694316 1564289 := bstep (se 2 (by rfl) ⟨586608, by rfl⟩ : syracuseStep 1564289 = 1173217) B1173217
theorem B745195 : Blo 694316 745195 := bstep (se 1 (by rfl) ⟨558896, by rfl⟩ : syracuseStep 745195 = 1117793) B1117793
theorem B11919149 : Blo 694316 11919149 := bstep (se 3 (by rfl) ⟨2234840, by rfl⟩ : syracuseStep 11919149 = 4469681) B4469681
theorem B3170137 : Blo 694316 3170137 := bstep (se 2 (by rfl) ⟨1188801, by rfl⟩ : syracuseStep 3170137 = 2377603) B2377603
theorem B1564505 : Blo 694316 1564505 := bstep (se 2 (by rfl) ⟨586689, by rfl⟩ : syracuseStep 1564505 = 1173379) B1173379
theorem B2645891 : Blo 694316 2645891 := bstep (se 1 (by rfl) ⟨1984418, by rfl⟩ : syracuseStep 2645891 = 3968837) B3968837
theorem B3530627 : Blo 694316 3530627 := bstep (se 1 (by rfl) ⟨2647970, by rfl⟩ : syracuseStep 3530627 = 5295941) B5295941
theorem B2645905 : Blo 694316 2645905 := bstep (se 2 (by rfl) ⟨992214, by rfl⟩ : syracuseStep 2645905 = 1984429) B1984429
theorem B1564595 : Blo 694316 1564595 := bstep (se 1 (by rfl) ⟨1173446, by rfl⟩ : syracuseStep 1564595 = 2346893) B2346893
theorem B1761203 : Blo 694316 1761203 := bstep (se 1 (by rfl) ⟨1320902, by rfl⟩ : syracuseStep 1761203 = 2641805) B2641805
theorem B2351051 : Blo 694316 2351051 := bstep (se 1 (by rfl) ⟨1763288, by rfl⟩ : syracuseStep 2351051 = 3526577) B3526577
theorem B1564631 : Blo 694316 1564631 := bstep (se 1 (by rfl) ⟨1173473, by rfl⟩ : syracuseStep 1564631 = 2346947) B2346947
theorem B2383895 : Blo 694316 2383895 := bstep (se 1 (by rfl) ⟨1787921, by rfl⟩ : syracuseStep 2383895 = 3575843) B3575843
theorem B1564811 : Blo 694316 1564811 := bstep (se 1 (by rfl) ⟨1173608, by rfl⟩ : syracuseStep 1564811 = 2347217) B2347217
theorem B1564865 : Blo 694316 1564865 := bstep (se 2 (by rfl) ⟨586824, by rfl⟩ : syracuseStep 1564865 = 1173649) B1173649
theorem B2646209 : Blo 694316 2646209 := bstep (se 2 (by rfl) ⟨992328, by rfl⟩ : syracuseStep 2646209 = 1984657) B1984657
theorem B1761497 : Blo 694316 1761497 := bstep (se 2 (by rfl) ⟨660561, by rfl⟩ : syracuseStep 1761497 = 1321123) B1321123
theorem B2351321 : Blo 694316 2351321 := bstep (se 2 (by rfl) ⟨881745, by rfl⟩ : syracuseStep 2351321 = 1763491) B1763491
theorem B1565081 : Blo 694316 1565081 := bstep (se 2 (by rfl) ⟨586905, by rfl⟩ : syracuseStep 1565081 = 1173811) B1173811
theorem B1565171 : Blo 694316 1565171 := bstep (se 1 (by rfl) ⟨1173878, by rfl⟩ : syracuseStep 1565171 = 2347757) B2347757
theorem B1565207 : Blo 694316 1565207 := bstep (se 1 (by rfl) ⟨1173905, by rfl⟩ : syracuseStep 1565207 = 2347811) B2347811
theorem B5300801 : Blo 694316 5300801 := bstep (se 2 (by rfl) ⟨1987800, by rfl⟩ : syracuseStep 5300801 = 3975601) B3975601
theorem B10052171 : Blo 694316 10052171 := bstep (se 1 (by rfl) ⟨7539128, by rfl⟩ : syracuseStep 10052171 = 15078257) B15078257
theorem B1958489 : Blo 694316 1958489 := bstep (se 2 (by rfl) ⟨734433, by rfl⟩ : syracuseStep 1958489 = 1468867) B1468867
theorem B1172171 : Blo 694316 1172171 := bstep (se 1 (by rfl) ⟨879128, by rfl⟩ : syracuseStep 1172171 = 1758257) B1758257
theorem B1565387 : Blo 694316 1565387 := bstep (se 1 (by rfl) ⟨1174040, by rfl⟩ : syracuseStep 1565387 = 2348081) B2348081
theorem B1565441 : Blo 694316 1565441 := bstep (se 2 (by rfl) ⟨587040, by rfl⟩ : syracuseStep 1565441 = 1174081) B1174081
theorem B1172299 : Blo 694316 1172299 := bstep (se 1 (by rfl) ⟨879224, by rfl⟩ : syracuseStep 1172299 = 1758449) B1758449
theorem B2646877 : Blo 694316 2646877 := bstep (se 3 (by rfl) ⟨496289, by rfl⟩ : syracuseStep 2646877 = 992579) B992579
theorem B3957605 : Blo 694316 3957605 := bstep (se 4 (by rfl) ⟨371025, by rfl⟩ : syracuseStep 3957605 = 742051) B742051
theorem B2352023 : Blo 694316 2352023 := bstep (se 1 (by rfl) ⟨1764017, by rfl⟩ : syracuseStep 2352023 = 3528035) B3528035
theorem B1172441 : Blo 694316 1172441 := bstep (se 2 (by rfl) ⟨439665, by rfl⟩ : syracuseStep 1172441 = 879331) B879331
theorem B1565657 : Blo 694316 1565657 := bstep (se 2 (by rfl) ⟨587121, by rfl⟩ : syracuseStep 1565657 = 1174243) B1174243
theorem B2515985 : Blo 694316 2515985 := bstep (se 2 (by rfl) ⟨943494, by rfl⟩ : syracuseStep 2515985 = 1886989) B1886989
theorem B2974765 : Blo 694316 2974765 := bstep (se 3 (by rfl) ⟨557768, by rfl⟩ : syracuseStep 2974765 = 1115537) B1115537
theorem B1565747 : Blo 694316 1565747 := bstep (se 1 (by rfl) ⟨1174310, by rfl⟩ : syracuseStep 1565747 = 2348621) B2348621
theorem B1565783 : Blo 694316 1565783 := bstep (se 1 (by rfl) ⟨1174337, by rfl⟩ : syracuseStep 1565783 = 2348675) B2348675
theorem B1041497 : Blo 694316 1041497 := bstep (se 2 (by rfl) ⟨390561, by rfl⟩ : syracuseStep 1041497 = 781123) B781123
theorem B1172569 : Blo 694316 1172569 := bstep (se 2 (by rfl) ⟨439713, by rfl⟩ : syracuseStep 1172569 = 879427) B879427
theorem B1041611 : Blo 694316 1041611 := bstep (se 1 (by rfl) ⟨781208, by rfl⟩ : syracuseStep 1041611 = 1562417) B1562417
theorem B1041623 : Blo 694316 1041623 := bstep (se 1 (by rfl) ⟨781217, by rfl⟩ : syracuseStep 1041623 = 1562435) B1562435
theorem B1565963 : Blo 694316 1565963 := bstep (se 1 (by rfl) ⟨1174472, by rfl⟩ : syracuseStep 1565963 = 2348945) B2348945
theorem B1041689 : Blo 694316 1041689 := bstep (se 2 (by rfl) ⟨390633, by rfl⟩ : syracuseStep 1041689 = 781267) B781267
theorem B1566017 : Blo 694316 1566017 := bstep (se 2 (by rfl) ⟨587256, by rfl⟩ : syracuseStep 1566017 = 1174513) B1174513
theorem B1041803 : Blo 694316 1041803 := bstep (se 1 (by rfl) ⟨781352, by rfl⟩ : syracuseStep 1041803 = 1562705) B1562705
theorem B1041815 : Blo 694316 1041815 := bstep (se 1 (by rfl) ⟨781361, by rfl⟩ : syracuseStep 1041815 = 1562723) B1562723
theorem B2352563 : Blo 694316 2352563 := bstep (se 1 (by rfl) ⟨1764422, by rfl⟩ : syracuseStep 2352563 = 3528845) B3528845
theorem B1041881 : Blo 694316 1041881 := bstep (se 2 (by rfl) ⟨390705, by rfl⟩ : syracuseStep 1041881 = 781411) B781411
theorem B2516503 : Blo 694316 2516503 := bstep (se 1 (by rfl) ⟨1887377, by rfl⟩ : syracuseStep 2516503 = 3774755) B3774755
theorem B1566233 : Blo 694316 1566233 := bstep (se 2 (by rfl) ⟨587337, by rfl⟩ : syracuseStep 1566233 = 1174675) B1174675
theorem B1041995 : Blo 694316 1041995 := bstep (se 1 (by rfl) ⟨781496, by rfl⟩ : syracuseStep 1041995 = 1562993) B1562993
theorem B1042007 : Blo 694316 1042007 := bstep (se 1 (by rfl) ⟨781505, by rfl⟩ : syracuseStep 1042007 = 1563011) B1563011
theorem B1566323 : Blo 694316 1566323 := bstep (se 1 (by rfl) ⟨1174742, by rfl⟩ : syracuseStep 1566323 = 2349485) B2349485
theorem B1173143 : Blo 694316 1173143 := bstep (se 1 (by rfl) ⟨879857, by rfl⟩ : syracuseStep 1173143 = 1759715) B1759715
theorem B1566359 : Blo 694316 1566359 := bstep (se 1 (by rfl) ⟨1174769, by rfl⟩ : syracuseStep 1566359 = 2349539) B2349539
theorem B1042073 : Blo 694316 1042073 := bstep (se 2 (by rfl) ⟨390777, by rfl⟩ : syracuseStep 1042073 = 781555) B781555
theorem B8939159 : Blo 694316 8939159 := bstep (se 1 (by rfl) ⟨6704369, by rfl⟩ : syracuseStep 8939159 = 13408739) B13408739
theorem B2352833 : Blo 694316 2352833 := bstep (se 2 (by rfl) ⟨882312, by rfl⟩ : syracuseStep 2352833 = 1764625) B1764625
theorem B1042187 : Blo 694316 1042187 := bstep (se 1 (by rfl) ⟨781640, by rfl⟩ : syracuseStep 1042187 = 1563281) B1563281
theorem B1042199 : Blo 694316 1042199 := bstep (se 1 (by rfl) ⟨781649, by rfl⟩ : syracuseStep 1042199 = 1563299) B1563299
theorem B1173271 : Blo 694316 1173271 := bstep (se 1 (by rfl) ⟨879953, by rfl⟩ : syracuseStep 1173271 = 1759907) B1759907
theorem B21489461 : Blo 694316 21489461 := bstep (se 5 (by rfl) ⟨1007318, by rfl⟩ : syracuseStep 21489461 = 2014637) B2014637
theorem B8021825 : Blo 694316 8021825 := bstep (se 2 (by rfl) ⟨3008184, by rfl⟩ : syracuseStep 8021825 = 6016369) B6016369
theorem B1566539 : Blo 694316 1566539 := bstep (se 1 (by rfl) ⟨1174904, by rfl⟩ : syracuseStep 1566539 = 2349809) B2349809
theorem B1763147 : Blo 694316 1763147 := bstep (se 1 (by rfl) ⟨1322360, by rfl⟩ : syracuseStep 1763147 = 2644721) B2644721
theorem B1042265 : Blo 694316 1042265 := bstep (se 2 (by rfl) ⟨390849, by rfl⟩ : syracuseStep 1042265 = 781699) B781699
theorem B1566593 : Blo 694316 1566593 := bstep (se 2 (by rfl) ⟨587472, by rfl⟩ : syracuseStep 1566593 = 1174945) B1174945
theorem B3172289 : Blo 694316 3172289 := bstep (se 2 (by rfl) ⟨1189608, by rfl⟩ : syracuseStep 3172289 = 2379217) B2379217
theorem B1042379 : Blo 694316 1042379 := bstep (se 1 (by rfl) ⟨781784, by rfl⟩ : syracuseStep 1042379 = 1563569) B1563569
theorem B1042391 : Blo 694316 1042391 := bstep (se 1 (by rfl) ⟨781793, by rfl⟩ : syracuseStep 1042391 = 1563587) B1563587
theorem B1697753 : Blo 694316 1697753 := bstep (se 2 (by rfl) ⟨636657, by rfl⟩ : syracuseStep 1697753 = 1273315) B1273315
theorem B1042457 : Blo 694316 1042457 := bstep (se 2 (by rfl) ⟨390921, by rfl⟩ : syracuseStep 1042457 = 781843) B781843
theorem B1566809 : Blo 694316 1566809 := bstep (se 2 (by rfl) ⟨587553, by rfl⟩ : syracuseStep 1566809 = 1175107) B1175107
theorem B2648153 : Blo 694316 2648153 := bstep (se 2 (by rfl) ⟨993057, by rfl⟩ : syracuseStep 2648153 = 1986115) B1986115
theorem B1042571 : Blo 694316 1042571 := bstep (se 1 (by rfl) ⟨781928, by rfl⟩ : syracuseStep 1042571 = 1563857) B1563857
theorem B1042583 : Blo 694316 1042583 := bstep (se 1 (by rfl) ⟨781937, by rfl⟩ : syracuseStep 1042583 = 1563875) B1563875
theorem B1566899 : Blo 694316 1566899 := bstep (se 1 (by rfl) ⟨1175174, by rfl⟩ : syracuseStep 1566899 = 2350349) B2350349
theorem B1566935 : Blo 694316 1566935 := bstep (se 1 (by rfl) ⟨1175201, by rfl⟩ : syracuseStep 1566935 = 2350403) B2350403
theorem B1042649 : Blo 694316 1042649 := bstep (se 2 (by rfl) ⟨390993, by rfl⟩ : syracuseStep 1042649 = 781987) B781987
theorem B2353373 : Blo 694316 2353373 := bstep (se 3 (by rfl) ⟨441257, by rfl⟩ : syracuseStep 2353373 = 882515) B882515
theorem B4352321 : Blo 694316 4352321 := bstep (se 2 (by rfl) ⟨1632120, by rfl⟩ : syracuseStep 4352321 = 3264241) B3264241
theorem B1042763 : Blo 694316 1042763 := bstep (se 1 (by rfl) ⟨782072, by rfl⟩ : syracuseStep 1042763 = 1564145) B1564145
theorem B1042775 : Blo 694316 1042775 := bstep (se 1 (by rfl) ⟨782081, by rfl⟩ : syracuseStep 1042775 = 1564163) B1564163
theorem B1173899 : Blo 694316 1173899 := bstep (se 1 (by rfl) ⟨880424, by rfl⟩ : syracuseStep 1173899 = 1760849) B1760849
theorem B1567115 : Blo 694316 1567115 := bstep (se 1 (by rfl) ⟨1175336, by rfl⟩ : syracuseStep 1567115 = 2350673) B2350673
theorem B1042841 : Blo 694316 1042841 := bstep (se 2 (by rfl) ⟨391065, by rfl⟩ : syracuseStep 1042841 = 782131) B782131
theorem B1567169 : Blo 694316 1567169 := bstep (se 2 (by rfl) ⟨587688, by rfl⟩ : syracuseStep 1567169 = 1175377) B1175377
theorem B5302745 : Blo 694316 5302745 := bstep (se 2 (by rfl) ⟨1988529, by rfl⟩ : syracuseStep 5302745 = 3977059) B3977059
theorem B1042955 : Blo 694316 1042955 := bstep (se 1 (by rfl) ⟨782216, by rfl⟩ : syracuseStep 1042955 = 1564433) B1564433
theorem B1174027 : Blo 694316 1174027 := bstep (se 1 (by rfl) ⟨880520, by rfl⟩ : syracuseStep 1174027 = 1761041) B1761041
theorem B1042967 : Blo 694316 1042967 := bstep (se 1 (by rfl) ⟨782225, by rfl⟩ : syracuseStep 1042967 = 1564451) B1564451
theorem B1043033 : Blo 694316 1043033 := bstep (se 2 (by rfl) ⟨391137, by rfl⟩ : syracuseStep 1043033 = 782275) B782275
theorem B1174169 : Blo 694316 1174169 := bstep (se 2 (by rfl) ⟨440313, by rfl⟩ : syracuseStep 1174169 = 880627) B880627
theorem B1567385 : Blo 694316 1567385 := bstep (se 2 (by rfl) ⟨587769, by rfl⟩ : syracuseStep 1567385 = 1175539) B1175539
theorem B1043147 : Blo 694316 1043147 := bstep (se 1 (by rfl) ⟨782360, by rfl⟩ : syracuseStep 1043147 = 1564721) B1564721
theorem B1043159 : Blo 694316 1043159 := bstep (se 1 (by rfl) ⟨782369, by rfl⟩ : syracuseStep 1043159 = 1564739) B1564739
theorem B1567475 : Blo 694316 1567475 := bstep (se 1 (by rfl) ⟨1175606, by rfl⟩ : syracuseStep 1567475 = 2351213) B2351213
theorem B1567511 : Blo 694316 1567511 := bstep (se 1 (by rfl) ⟨1175633, by rfl⟩ : syracuseStep 1567511 = 2351267) B2351267
theorem B1764119 : Blo 694316 1764119 := bstep (se 1 (by rfl) ⟨1323089, by rfl⟩ : syracuseStep 1764119 = 2646179) B2646179
theorem B1043225 : Blo 694316 1043225 := bstep (se 2 (by rfl) ⟨391209, by rfl⟩ : syracuseStep 1043225 = 782419) B782419
theorem B1174297 : Blo 694316 1174297 := bstep (se 2 (by rfl) ⟨440361, by rfl⟩ : syracuseStep 1174297 = 880723) B880723
theorem B3173165 : Blo 694316 3173165 := bstep (se 3 (by rfl) ⟨594968, by rfl⟩ : syracuseStep 3173165 = 1189937) B1189937
theorem B781195 : Blo 694316 781195 := bstep (se 1 (by rfl) ⟨585896, by rfl⟩ : syracuseStep 781195 = 1171793) B1171793
theorem B1043339 : Blo 694316 1043339 := bstep (se 1 (by rfl) ⟨782504, by rfl⟩ : syracuseStep 1043339 = 1565009) B1565009
theorem B1043351 : Blo 694316 1043351 := bstep (se 1 (by rfl) ⟨782513, by rfl⟩ : syracuseStep 1043351 = 1565027) B1565027
theorem B1567691 : Blo 694316 1567691 := bstep (se 1 (by rfl) ⟨1175768, by rfl⟩ : syracuseStep 1567691 = 2351537) B2351537
theorem B1043417 : Blo 694316 1043417 := bstep (se 2 (by rfl) ⟨391281, by rfl⟩ : syracuseStep 1043417 = 782563) B782563
theorem B7531481 : Blo 694316 7531481 := bstep (se 2 (by rfl) ⟨2824305, by rfl⟩ : syracuseStep 7531481 = 5648611) B5648611
theorem B781303 : Blo 694316 781303 := bstep (se 1 (by rfl) ⟨585977, by rfl⟩ : syracuseStep 781303 = 1171955) B1171955
theorem B1567745 : Blo 694316 1567745 := bstep (se 2 (by rfl) ⟨587904, by rfl⟩ : syracuseStep 1567745 = 1175809) B1175809
theorem B1043531 : Blo 694316 1043531 := bstep (se 1 (by rfl) ⟨782648, by rfl⟩ : syracuseStep 1043531 = 1565297) B1565297
theorem B1043543 : Blo 694316 1043543 := bstep (se 1 (by rfl) ⟨782657, by rfl⟩ : syracuseStep 1043543 = 1565315) B1565315
theorem B1043609 : Blo 694316 1043609 := bstep (se 2 (by rfl) ⟨391353, by rfl⟩ : syracuseStep 1043609 = 782707) B782707
theorem B781483 : Blo 694316 781483 := bstep (se 1 (by rfl) ⟨586112, by rfl⟩ : syracuseStep 781483 = 1172225) B1172225
theorem B1567961 : Blo 694316 1567961 := bstep (se 2 (by rfl) ⟨587985, by rfl⟩ : syracuseStep 1567961 = 1175971) B1175971
theorem B1043723 : Blo 694316 1043723 := bstep (se 1 (by rfl) ⟨782792, by rfl⟩ : syracuseStep 1043723 = 1565585) B1565585
theorem B781591 : Blo 694316 781591 := bstep (se 1 (by rfl) ⟨586193, by rfl⟩ : syracuseStep 781591 = 1172387) B1172387
theorem B1043735 : Blo 694316 1043735 := bstep (se 1 (by rfl) ⟨782801, by rfl⟩ : syracuseStep 1043735 = 1565603) B1565603
theorem B1568051 : Blo 694316 1568051 := bstep (se 1 (by rfl) ⟨1176038, by rfl⟩ : syracuseStep 1568051 = 2352077) B2352077
theorem B2354507 : Blo 694316 2354507 := bstep (se 1 (by rfl) ⟨1765880, by rfl⟩ : syracuseStep 2354507 = 3531761) B3531761
theorem B1174871 : Blo 694316 1174871 := bstep (se 1 (by rfl) ⟨881153, by rfl⟩ : syracuseStep 1174871 = 1762307) B1762307
theorem B1568087 : Blo 694316 1568087 := bstep (se 1 (by rfl) ⟨1176065, by rfl⟩ : syracuseStep 1568087 = 2352131) B2352131
theorem B1043801 : Blo 694316 1043801 := bstep (se 2 (by rfl) ⟨391425, by rfl⟩ : syracuseStep 1043801 = 782851) B782851
theorem B2977175 : Blo 694316 2977175 := bstep (se 1 (by rfl) ⟨2232881, by rfl⟩ : syracuseStep 2977175 = 4465763) B4465763
theorem B1764787 : Blo 694316 1764787 := bstep (se 1 (by rfl) ⟨1323590, by rfl⟩ : syracuseStep 1764787 = 2647181) B2647181
theorem B781771 : Blo 694316 781771 := bstep (se 1 (by rfl) ⟨586328, by rfl⟩ : syracuseStep 781771 = 1172657) B1172657
theorem B880075 : Blo 694316 880075 := bstep (se 1 (by rfl) ⟨660056, by rfl⟩ : syracuseStep 880075 = 1320113) B1320113
theorem B1043915 : Blo 694316 1043915 := bstep (se 1 (by rfl) ⟨782936, by rfl⟩ : syracuseStep 1043915 = 1565873) B1565873
theorem B1043927 : Blo 694316 1043927 := bstep (se 1 (by rfl) ⟨782945, by rfl⟩ : syracuseStep 1043927 = 1565891) B1565891
theorem B1174999 : Blo 694316 1174999 := bstep (se 1 (by rfl) ⟨881249, by rfl⟩ : syracuseStep 1174999 = 1762499) B1762499
theorem B24440291 : Blo 694316 24440291 := bstep (se 1 (by rfl) ⟨18330218, by rfl⟩ : syracuseStep 24440291 = 36660437) B36660437
theorem B1568267 : Blo 694316 1568267 := bstep (se 1 (by rfl) ⟨1176200, by rfl⟩ : syracuseStep 1568267 = 2352401) B2352401
theorem B3534353 : Blo 694316 3534353 := bstep (se 2 (by rfl) ⟨1325382, by rfl⟩ : syracuseStep 3534353 = 2650765) B2650765
theorem B1043993 : Blo 694316 1043993 := bstep (se 2 (by rfl) ⟨391497, by rfl⟩ : syracuseStep 1043993 = 782995) B782995
theorem B781879 : Blo 694316 781879 := bstep (se 1 (by rfl) ⟨586409, by rfl⟩ : syracuseStep 781879 = 1172819) B1172819
theorem B1568321 : Blo 694316 1568321 := bstep (se 2 (by rfl) ⟨588120, by rfl⟩ : syracuseStep 1568321 = 1176241) B1176241
theorem B1764929 : Blo 694316 1764929 := bstep (se 2 (by rfl) ⟨661848, by rfl⟩ : syracuseStep 1764929 = 1323697) B1323697
theorem B2354777 : Blo 694316 2354777 := bstep (se 2 (by rfl) ⟨883041, by rfl⟩ : syracuseStep 2354777 = 1766083) B1766083
theorem B1044107 : Blo 694316 1044107 := bstep (se 1 (by rfl) ⟨783080, by rfl⟩ : syracuseStep 1044107 = 1566161) B1566161
theorem B3010193 : Blo 694316 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B1044119 : Blo 694316 1044119 := bstep (se 1 (by rfl) ⟨783089, by rfl⟩ : syracuseStep 1044119 = 1566179) B1566179
theorem B2649779 : Blo 694316 2649779 := bstep (se 1 (by rfl) ⟨1987334, by rfl⟩ : syracuseStep 2649779 = 3974669) B3974669
theorem B3534515 : Blo 694316 3534515 := bstep (se 1 (by rfl) ⟨2650886, by rfl⟩ : syracuseStep 3534515 = 5301773) B5301773
theorem B2649793 : Blo 694316 2649793 := bstep (se 2 (by rfl) ⟨993672, by rfl⟩ : syracuseStep 2649793 = 1987345) B1987345
theorem B2420417 : Blo 694316 2420417 := bstep (se 2 (by rfl) ⟨907656, by rfl⟩ : syracuseStep 2420417 = 1815313) B1815313
theorem B1044185 : Blo 694316 1044185 := bstep (se 2 (by rfl) ⟨391569, by rfl⟩ : syracuseStep 1044185 = 783139) B783139
theorem B782059 : Blo 694316 782059 := bstep (se 1 (by rfl) ⟨586544, by rfl⟩ : syracuseStep 782059 = 1173089) B1173089
theorem B1568537 : Blo 694316 1568537 := bstep (se 2 (by rfl) ⟨588201, by rfl⟩ : syracuseStep 1568537 = 1176403) B1176403
theorem B1044299 : Blo 694316 1044299 := bstep (se 1 (by rfl) ⟨783224, by rfl⟩ : syracuseStep 1044299 = 1566449) B1566449
theorem B782167 : Blo 694316 782167 := bstep (se 1 (by rfl) ⟨586625, by rfl⟩ : syracuseStep 782167 = 1173251) B1173251
theorem B1044311 : Blo 694316 1044311 := bstep (se 1 (by rfl) ⟨783233, by rfl⟩ : syracuseStep 1044311 = 1566467) B1566467
theorem B1568627 : Blo 694316 1568627 := bstep (se 1 (by rfl) ⟨1176470, by rfl⟩ : syracuseStep 1568627 = 2352941) B2352941
theorem B1568663 : Blo 694316 1568663 := bstep (se 1 (by rfl) ⟨1176497, by rfl⟩ : syracuseStep 1568663 = 2352995) B2352995
theorem B1044377 : Blo 694316 1044377 := bstep (se 2 (by rfl) ⟨391641, by rfl⟩ : syracuseStep 1044377 = 783283) B783283
theorem B782347 : Blo 694316 782347 := bstep (se 1 (by rfl) ⟨586760, by rfl⟩ : syracuseStep 782347 = 1173521) B1173521
theorem B1044491 : Blo 694316 1044491 := bstep (se 1 (by rfl) ⟨783368, by rfl⟩ : syracuseStep 1044491 = 1566737) B1566737
theorem B1044503 : Blo 694316 1044503 := bstep (se 1 (by rfl) ⟨783377, by rfl⟩ : syracuseStep 1044503 = 1566755) B1566755
theorem B1175627 : Blo 694316 1175627 := bstep (se 1 (by rfl) ⟨881720, by rfl⟩ : syracuseStep 1175627 = 1763441) B1763441
theorem B1568843 : Blo 694316 1568843 := bstep (se 1 (by rfl) ⟨1176632, by rfl⟩ : syracuseStep 1568843 = 2353265) B2353265
theorem B1044569 : Blo 694316 1044569 := bstep (se 2 (by rfl) ⟨391713, by rfl⟩ : syracuseStep 1044569 = 783427) B783427
theorem B782455 : Blo 694316 782455 := bstep (se 1 (by rfl) ⟨586841, by rfl⟩ : syracuseStep 782455 = 1173683) B1173683
theorem B1568897 : Blo 694316 1568897 := bstep (se 2 (by rfl) ⟨588336, by rfl⟩ : syracuseStep 1568897 = 1176673) B1176673
theorem B1241239 : Blo 694316 1241239 := bstep (se 1 (by rfl) ⟨930929, by rfl⟩ : syracuseStep 1241239 = 1861859) B1861859
theorem B1044683 : Blo 694316 1044683 := bstep (se 1 (by rfl) ⟨783512, by rfl⟩ : syracuseStep 1044683 = 1567025) B1567025
theorem B1175755 : Blo 694316 1175755 := bstep (se 1 (by rfl) ⟨881816, by rfl⟩ : syracuseStep 1175755 = 1763633) B1763633
theorem B1044695 : Blo 694316 1044695 := bstep (se 1 (by rfl) ⟨783521, by rfl⟩ : syracuseStep 1044695 = 1567043) B1567043
theorem B2355479 : Blo 694316 2355479 := bstep (se 1 (by rfl) ⟨1766609, by rfl⟩ : syracuseStep 2355479 = 3533219) B3533219
theorem B1044761 : Blo 694316 1044761 := bstep (se 2 (by rfl) ⟨391785, by rfl⟩ : syracuseStep 1044761 = 783571) B783571
theorem B782635 : Blo 694316 782635 := bstep (se 1 (by rfl) ⟨586976, by rfl⟩ : syracuseStep 782635 = 1173953) B1173953
theorem B2388275 : Blo 694316 2388275 := bstep (se 1 (by rfl) ⟨1791206, by rfl⟩ : syracuseStep 2388275 = 3582413) B3582413
theorem B1175897 : Blo 694316 1175897 := bstep (se 2 (by rfl) ⟨440961, by rfl⟩ : syracuseStep 1175897 = 881923) B881923
theorem B1569113 : Blo 694316 1569113 := bstep (se 2 (by rfl) ⟨588417, by rfl⟩ : syracuseStep 1569113 = 1176835) B1176835
theorem B1044875 : Blo 694316 1044875 := bstep (se 1 (by rfl) ⟨783656, by rfl⟩ : syracuseStep 1044875 = 1567313) B1567313
theorem B782743 : Blo 694316 782743 := bstep (se 1 (by rfl) ⟨587057, by rfl⟩ : syracuseStep 782743 = 1174115) B1174115
theorem B881047 : Blo 694316 881047 := bstep (se 1 (by rfl) ⟨660785, by rfl⟩ : syracuseStep 881047 = 1321571) B1321571
theorem B1044887 : Blo 694316 1044887 := bstep (se 1 (by rfl) ⟨783665, by rfl⟩ : syracuseStep 1044887 = 1567331) B1567331
theorem B1569203 : Blo 694316 1569203 := bstep (se 1 (by rfl) ⟨1176902, by rfl⟩ : syracuseStep 1569203 = 2353805) B2353805
theorem B815563 : Blo 694316 815563 := bstep (se 1 (by rfl) ⟨611672, by rfl⟩ : syracuseStep 815563 = 1223345) B1223345
theorem B1569239 : Blo 694316 1569239 := bstep (se 1 (by rfl) ⟨1176929, by rfl⟩ : syracuseStep 1569239 = 2353859) B2353859
theorem B1044953 : Blo 694316 1044953 := bstep (se 2 (by rfl) ⟨391857, by rfl⟩ : syracuseStep 1044953 = 783715) B783715
theorem B1176025 : Blo 694316 1176025 := bstep (se 2 (by rfl) ⟨441009, by rfl⟩ : syracuseStep 1176025 = 882019) B882019
theorem B782923 : Blo 694316 782923 := bstep (se 1 (by rfl) ⟨587192, by rfl⟩ : syracuseStep 782923 = 1174385) B1174385
theorem B1045067 : Blo 694316 1045067 := bstep (se 1 (by rfl) ⟨783800, by rfl⟩ : syracuseStep 1045067 = 1567601) B1567601
theorem B1045079 : Blo 694316 1045079 := bstep (se 1 (by rfl) ⟨783809, by rfl⟩ : syracuseStep 1045079 = 1567619) B1567619
theorem B1569419 : Blo 694316 1569419 := bstep (se 1 (by rfl) ⟨1177064, by rfl⟩ : syracuseStep 1569419 = 2354129) B2354129
theorem B2388631 : Blo 694316 2388631 := bstep (se 1 (by rfl) ⟨1791473, by rfl⟩ : syracuseStep 2388631 = 3582947) B3582947
theorem B1045145 : Blo 694316 1045145 := bstep (se 2 (by rfl) ⟨391929, by rfl⟩ : syracuseStep 1045145 = 783859) B783859
theorem B783031 : Blo 694316 783031 := bstep (se 1 (by rfl) ⟨587273, by rfl⟩ : syracuseStep 783031 = 1174547) B1174547
theorem B1569473 : Blo 694316 1569473 := bstep (se 2 (by rfl) ⟨588552, by rfl⟩ : syracuseStep 1569473 = 1177105) B1177105
theorem B1045259 : Blo 694316 1045259 := bstep (se 1 (by rfl) ⟨783944, by rfl⟩ : syracuseStep 1045259 = 1567889) B1567889
theorem B5960465 : Blo 694316 5960465 := bstep (se 2 (by rfl) ⟨2235174, by rfl⟩ : syracuseStep 5960465 = 4470349) B4470349
theorem B1045271 : Blo 694316 1045271 := bstep (se 1 (by rfl) ⟨783953, by rfl⟩ : syracuseStep 1045271 = 1567907) B1567907
theorem B1766195 : Blo 694316 1766195 := bstep (se 1 (by rfl) ⟨1324646, by rfl⟩ : syracuseStep 1766195 = 2649293) B2649293
theorem B2356019 : Blo 694316 2356019 := bstep (se 1 (by rfl) ⟨1767014, by rfl⟩ : syracuseStep 2356019 = 3534029) B3534029
theorem B1045337 : Blo 694316 1045337 := bstep (se 2 (by rfl) ⟨392001, by rfl⟩ : syracuseStep 1045337 = 784003) B784003
theorem B783211 : Blo 694316 783211 := bstep (se 1 (by rfl) ⟨587408, by rfl⟩ : syracuseStep 783211 = 1174817) B1174817
theorem B2683799 : Blo 694316 2683799 := bstep (se 1 (by rfl) ⟨2012849, by rfl⟩ : syracuseStep 2683799 = 4025699) B4025699
theorem B1569689 : Blo 694316 1569689 := bstep (se 2 (by rfl) ⟨588633, by rfl⟩ : syracuseStep 1569689 = 1177267) B1177267
theorem B1045451 : Blo 694316 1045451 := bstep (se 1 (by rfl) ⟨784088, by rfl⟩ : syracuseStep 1045451 = 1568177) B1568177
theorem B783319 : Blo 694316 783319 := bstep (se 1 (by rfl) ⟨587489, by rfl⟩ : syracuseStep 783319 = 1174979) B1174979
theorem B1045463 : Blo 694316 1045463 := bstep (se 1 (by rfl) ⟨784097, by rfl⟩ : syracuseStep 1045463 = 1568195) B1568195
theorem B1569779 : Blo 694316 1569779 := bstep (se 1 (by rfl) ⟨1177334, by rfl⟩ : syracuseStep 1569779 = 2354669) B2354669
theorem B1176599 : Blo 694316 1176599 := bstep (se 1 (by rfl) ⟨882449, by rfl⟩ : syracuseStep 1176599 = 1764899) B1764899
theorem B1569815 : Blo 694316 1569815 := bstep (se 1 (by rfl) ⟨1177361, by rfl⟩ : syracuseStep 1569815 = 2354723) B2354723
theorem B1045529 : Blo 694316 1045529 := bstep (se 2 (by rfl) ⟨392073, by rfl⟩ : syracuseStep 1045529 = 784147) B784147
theorem B2356289 : Blo 694316 2356289 := bstep (se 2 (by rfl) ⟨883608, by rfl⟩ : syracuseStep 2356289 = 1767217) B1767217
theorem B3175499 : Blo 694316 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B783499 : Blo 694316 783499 := bstep (se 1 (by rfl) ⟨587624, by rfl⟩ : syracuseStep 783499 = 1175249) B1175249
theorem B1045643 : Blo 694316 1045643 := bstep (se 1 (by rfl) ⟨784232, by rfl⟩ : syracuseStep 1045643 = 1568465) B1568465
theorem B1045655 : Blo 694316 1045655 := bstep (se 1 (by rfl) ⟨784241, by rfl⟩ : syracuseStep 1045655 = 1568483) B1568483
theorem B1176727 : Blo 694316 1176727 := bstep (se 1 (by rfl) ⟨882545, by rfl⟩ : syracuseStep 1176727 = 1765091) B1765091
theorem B1668289 : Blo 694316 1668289 := bstep (se 2 (by rfl) ⟨625608, by rfl⟩ : syracuseStep 1668289 = 1251217) B1251217
theorem B881867 : Blo 694316 881867 := bstep (se 1 (by rfl) ⟨661400, by rfl⟩ : syracuseStep 881867 = 1322801) B1322801
theorem B1569995 : Blo 694316 1569995 := bstep (se 1 (by rfl) ⟨1177496, by rfl⟩ : syracuseStep 1569995 = 2354993) B2354993
theorem B3339481 : Blo 694316 3339481 := bstep (se 2 (by rfl) ⟨1252305, by rfl⟩ : syracuseStep 3339481 = 2504611) B2504611
theorem B1045721 : Blo 694316 1045721 := bstep (se 2 (by rfl) ⟨392145, by rfl⟩ : syracuseStep 1045721 = 784291) B784291
theorem B783607 : Blo 694316 783607 := bstep (se 1 (by rfl) ⟨587705, by rfl⟩ : syracuseStep 783607 = 1175411) B1175411
theorem B1570049 : Blo 694316 1570049 := bstep (se 2 (by rfl) ⟨588768, by rfl⟩ : syracuseStep 1570049 = 1177537) B1177537
theorem B2979089 : Blo 694316 2979089 := bstep (se 2 (by rfl) ⟨1117158, by rfl⟩ : syracuseStep 2979089 = 2234317) B2234317
theorem B1045835 : Blo 694316 1045835 := bstep (se 1 (by rfl) ⟨784376, by rfl⟩ : syracuseStep 1045835 = 1568753) B1568753
theorem B1766731 : Blo 694316 1766731 := bstep (se 1 (by rfl) ⟨1325048, by rfl⟩ : syracuseStep 1766731 = 2650097) B2650097
theorem B1045847 : Blo 694316 1045847 := bstep (se 1 (by rfl) ⟨784385, by rfl⟩ : syracuseStep 1045847 = 1568771) B1568771
theorem B2225501 : Blo 694316 2225501 := bstep (se 3 (by rfl) ⟨417281, by rfl⟩ : syracuseStep 2225501 = 834563) B834563
theorem B1045913 : Blo 694316 1045913 := bstep (se 2 (by rfl) ⟨392217, by rfl⟩ : syracuseStep 1045913 = 784435) B784435
theorem B783787 : Blo 694316 783787 := bstep (se 1 (by rfl) ⟨587840, by rfl⟩ : syracuseStep 783787 = 1175681) B1175681
theorem B1570265 : Blo 694316 1570265 := bstep (se 2 (by rfl) ⟨588849, by rfl⟩ : syracuseStep 1570265 = 1177699) B1177699
theorem B1766873 : Blo 694316 1766873 := bstep (se 2 (by rfl) ⟨662577, by rfl⟩ : syracuseStep 1766873 = 1325155) B1325155
theorem B3175901 : Blo 694316 3175901 := bstep (se 3 (by rfl) ⟨595481, by rfl⟩ : syracuseStep 3175901 = 1190963) B1190963
theorem B1046027 : Blo 694316 1046027 := bstep (se 1 (by rfl) ⟨784520, by rfl⟩ : syracuseStep 1046027 = 1569041) B1569041
theorem B783895 : Blo 694316 783895 := bstep (se 1 (by rfl) ⟨587921, by rfl⟩ : syracuseStep 783895 = 1175843) B1175843
theorem B1046039 : Blo 694316 1046039 := bstep (se 1 (by rfl) ⟨784529, by rfl⟩ : syracuseStep 1046039 = 1569059) B1569059
theorem B1570355 : Blo 694316 1570355 := bstep (se 1 (by rfl) ⟨1177766, by rfl⟩ : syracuseStep 1570355 = 2355533) B2355533
theorem B1570391 : Blo 694316 1570391 := bstep (se 1 (by rfl) ⟨1177793, by rfl⟩ : syracuseStep 1570391 = 2355587) B2355587
theorem B1046105 : Blo 694316 1046105 := bstep (se 2 (by rfl) ⟨392289, by rfl⟩ : syracuseStep 1046105 = 784579) B784579
theorem B2815661 : Blo 694316 2815661 := bstep (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) B1055873
theorem B784075 : Blo 694316 784075 := bstep (se 1 (by rfl) ⟨588056, by rfl⟩ : syracuseStep 784075 = 1176113) B1176113
theorem B1046219 : Blo 694316 1046219 := bstep (se 1 (by rfl) ⟨784664, by rfl⟩ : syracuseStep 1046219 = 1569329) B1569329
theorem B1046231 : Blo 694316 1046231 := bstep (se 1 (by rfl) ⟨784673, by rfl⟩ : syracuseStep 1046231 = 1569347) B1569347
theorem B1177355 : Blo 694316 1177355 := bstep (se 1 (by rfl) ⟨883016, by rfl⟩ : syracuseStep 1177355 = 1766033) B1766033
theorem B1570571 : Blo 694316 1570571 := bstep (se 1 (by rfl) ⟨1177928, by rfl⟩ : syracuseStep 1570571 = 2355857) B2355857
theorem B1046297 : Blo 694316 1046297 := bstep (se 2 (by rfl) ⟨392361, by rfl⟩ : syracuseStep 1046297 = 784723) B784723
theorem B784183 : Blo 694316 784183 := bstep (se 1 (by rfl) ⟨588137, by rfl⟩ : syracuseStep 784183 = 1176275) B1176275
theorem B1570625 : Blo 694316 1570625 := bstep (se 2 (by rfl) ⟨588984, by rfl⟩ : syracuseStep 1570625 = 1177969) B1177969
theorem B882571 : Blo 694316 882571 := bstep (se 1 (by rfl) ⟨661928, by rfl⟩ : syracuseStep 882571 = 1323857) B1323857
theorem B1046411 : Blo 694316 1046411 := bstep (se 1 (by rfl) ⟨784808, by rfl⟩ : syracuseStep 1046411 = 1569617) B1569617
theorem B1177483 : Blo 694316 1177483 := bstep (se 1 (by rfl) ⟨883112, by rfl⟩ : syracuseStep 1177483 = 1766225) B1766225
theorem B1046423 : Blo 694316 1046423 := bstep (se 1 (by rfl) ⟨784817, by rfl⟩ : syracuseStep 1046423 = 1569635) B1569635
theorem B1046489 : Blo 694316 1046489 := bstep (se 2 (by rfl) ⟨392433, by rfl⟩ : syracuseStep 1046489 = 784867) B784867
theorem B784363 : Blo 694316 784363 := bstep (se 1 (by rfl) ⟨588272, by rfl⟩ : syracuseStep 784363 = 1176545) B1176545
theorem B1177625 : Blo 694316 1177625 := bstep (se 2 (by rfl) ⟨441609, by rfl⟩ : syracuseStep 1177625 = 883219) B883219
theorem B1570841 : Blo 694316 1570841 := bstep (se 2 (by rfl) ⟨589065, by rfl⟩ : syracuseStep 1570841 = 1178131) B1178131
theorem B1046603 : Blo 694316 1046603 := bstep (se 1 (by rfl) ⟨784952, by rfl⟩ : syracuseStep 1046603 = 1569905) B1569905
theorem B784471 : Blo 694316 784471 := bstep (se 1 (by rfl) ⟨588353, by rfl⟩ : syracuseStep 784471 = 1176707) B1176707
theorem B1046615 : Blo 694316 1046615 := bstep (se 1 (by rfl) ⟨784961, by rfl⟩ : syracuseStep 1046615 = 1569923) B1569923
theorem B1570931 : Blo 694316 1570931 := bstep (se 1 (by rfl) ⟨1178198, by rfl⟩ : syracuseStep 1570931 = 2356397) B2356397
theorem B882839 : Blo 694316 882839 := bstep (se 1 (by rfl) ⟨662129, by rfl⟩ : syracuseStep 882839 = 1324259) B1324259
theorem B1570967 : Blo 694316 1570967 := bstep (se 1 (by rfl) ⟨1178225, by rfl⟩ : syracuseStep 1570967 = 2356451) B2356451
theorem B1046681 : Blo 694316 1046681 := bstep (se 2 (by rfl) ⟨392505, by rfl⟩ : syracuseStep 1046681 = 785011) B785011
theorem B1177753 : Blo 694316 1177753 := bstep (se 2 (by rfl) ⟨441657, by rfl⟩ : syracuseStep 1177753 = 883315) B883315
theorem B2980061 : Blo 694316 2980061 := bstep (se 3 (by rfl) ⟨558761, by rfl⟩ : syracuseStep 2980061 = 1117523) B1117523
theorem B784651 : Blo 694316 784651 := bstep (se 1 (by rfl) ⟨588488, by rfl⟩ : syracuseStep 784651 = 1176977) B1176977
theorem B1046795 : Blo 694316 1046795 := bstep (se 1 (by rfl) ⟨785096, by rfl⟩ : syracuseStep 1046795 = 1570193) B1570193
theorem B1046807 : Blo 694316 1046807 := bstep (se 1 (by rfl) ⟨785105, by rfl⟩ : syracuseStep 1046807 = 1570211) B1570211
theorem B1571147 : Blo 694316 1571147 := bstep (se 1 (by rfl) ⟨1178360, by rfl⟩ : syracuseStep 1571147 = 2356721) B2356721
theorem B1046873 : Blo 694316 1046873 := bstep (se 2 (by rfl) ⟨392577, by rfl⟩ : syracuseStep 1046873 = 785155) B785155
theorem B784759 : Blo 694316 784759 := bstep (se 1 (by rfl) ⟨588569, by rfl⟩ : syracuseStep 784759 = 1177139) B1177139
theorem B1571201 : Blo 694316 1571201 := bstep (se 2 (by rfl) ⟨589200, by rfl⟩ : syracuseStep 1571201 = 1178401) B1178401
theorem B1046987 : Blo 694316 1046987 := bstep (se 1 (by rfl) ⟨785240, by rfl⟩ : syracuseStep 1046987 = 1570481) B1570481
theorem B1046999 : Blo 694316 1046999 := bstep (se 1 (by rfl) ⟨785249, by rfl⟩ : syracuseStep 1046999 = 1570499) B1570499
theorem B1047065 : Blo 694316 1047065 := bstep (se 2 (by rfl) ⟨392649, by rfl⟩ : syracuseStep 1047065 = 785299) B785299
theorem B784939 : Blo 694316 784939 := bstep (se 1 (by rfl) ⟨588704, by rfl⟩ : syracuseStep 784939 = 1177409) B1177409
theorem B3963437 : Blo 694316 3963437 := bstep (se 3 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 3963437 = 1486289) B1486289
theorem B1047179 : Blo 694316 1047179 := bstep (se 1 (by rfl) ⟨785384, by rfl⟩ : syracuseStep 1047179 = 1570769) B1570769
theorem B785047 : Blo 694316 785047 := bstep (se 1 (by rfl) ⟨588785, by rfl⟩ : syracuseStep 785047 = 1177571) B1177571
theorem B1047191 : Blo 694316 1047191 := bstep (se 1 (by rfl) ⟨785393, by rfl⟩ : syracuseStep 1047191 = 1570787) B1570787
theorem B1178327 : Blo 694316 1178327 := bstep (se 1 (by rfl) ⟨883745, by rfl⟩ : syracuseStep 1178327 = 1767491) B1767491
theorem B1047257 : Blo 694316 1047257 := bstep (se 2 (by rfl) ⟨392721, by rfl⟩ : syracuseStep 1047257 = 785443) B785443
theorem B3767057 : Blo 694316 3767057 := bstep (se 2 (by rfl) ⟨1412646, by rfl⟩ : syracuseStep 3767057 = 2825293) B2825293
theorem B785227 : Blo 694316 785227 := bstep (se 1 (by rfl) ⟨588920, by rfl⟩ : syracuseStep 785227 = 1177841) B1177841
theorem B1047371 : Blo 694316 1047371 := bstep (se 1 (by rfl) ⟨785528, by rfl⟩ : syracuseStep 1047371 = 1571057) B1571057
theorem B883543 : Blo 694316 883543 := bstep (se 1 (by rfl) ⟨662657, by rfl⟩ : syracuseStep 883543 = 1325315) B1325315
theorem B1047383 : Blo 694316 1047383 := bstep (se 1 (by rfl) ⟨785537, by rfl⟩ : syracuseStep 1047383 = 1571075) B1571075
theorem B20380517 : Blo 694316 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B1047449 : Blo 694316 1047449 := bstep (se 2 (by rfl) ⟨392793, by rfl⟩ : syracuseStep 1047449 = 785587) B785587
theorem B785335 : Blo 694316 785335 := bstep (se 1 (by rfl) ⟨589001, by rfl⟩ : syracuseStep 785335 = 1178003) B1178003
theorem B6683609 : Blo 694316 6683609 := bstep (se 2 (by rfl) ⟨2506353, by rfl⟩ : syracuseStep 6683609 = 5012707) B5012707
theorem B1408001 : Blo 694316 1408001 := bstep (se 2 (by rfl) ⟨528000, by rfl⟩ : syracuseStep 1408001 = 1056001) B1056001
theorem B8911889 : Blo 694316 8911889 := bstep (se 2 (by rfl) ⟨3341958, by rfl⟩ : syracuseStep 8911889 = 6683917) B6683917
theorem B785515 : Blo 694316 785515 := bstep (se 1 (by rfl) ⟨589136, by rfl⟩ : syracuseStep 785515 = 1178273) B1178273
theorem B4750609 : Blo 694316 4750609 := bstep (se 2 (by rfl) ⟨1781478, by rfl⟩ : syracuseStep 4750609 = 3562957) B3562957
theorem B5078533 : Blo 694316 5078533 := bstep (se 4 (by rfl) ⟨476112, by rfl⟩ : syracuseStep 5078533 = 952225) B952225
theorem B2981549 : Blo 694316 2981549 := bstep (se 3 (by rfl) ⟨559040, by rfl⟩ : syracuseStep 2981549 = 1118081) B1118081
theorem B3178385 : Blo 694316 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B2817995 : Blo 694316 2817995 := bstep (se 1 (by rfl) ⟨2113496, by rfl⟩ : syracuseStep 2817995 = 4226993) B4226993
theorem B5013515 : Blo 694316 5013515 := bstep (se 1 (by rfl) ⟨3760136, by rfl⟩ : syracuseStep 5013515 = 7520273) B7520273
theorem B2818091 : Blo 694316 2818091 := bstep (se 1 (by rfl) ⟨2113568, by rfl⟩ : syracuseStep 2818091 = 4227137) B4227137
theorem B2293879 : Blo 694316 2293879 := bstep (se 1 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 2293879 = 3440819) B3440819
theorem B1507513 : Blo 694316 1507513 := bstep (se 2 (by rfl) ⟨565317, by rfl⟩ : syracuseStep 1507513 = 1130635) B1130635
theorem B28639433 : Blo 694316 28639433 := bstep (se 2 (by rfl) ⟨10739787, by rfl⟩ : syracuseStep 28639433 = 21479575) B21479575
theorem B3768875 : Blo 694316 3768875 := bstep (se 1 (by rfl) ⟨2826656, by rfl⟩ : syracuseStep 3768875 = 5653313) B5653313
theorem B3965669 : Blo 694316 3965669 := bstep (se 4 (by rfl) ⟨371781, by rfl⟩ : syracuseStep 3965669 = 743563) B743563
theorem B3179587 : Blo 694316 3179587 := bstep (se 1 (by rfl) ⟨2384690, by rfl⟩ : syracuseStep 3179587 = 4769381) B4769381
theorem B5276987 : Blo 694316 5276987 := bstep (se 1 (by rfl) ⟨3957740, by rfl⟩ : syracuseStep 5276987 = 7915481) B7915481
theorem B13600099 : Blo 694316 13600099 := bstep (se 1 (by rfl) ⟨10200074, by rfl⟩ : syracuseStep 13600099 = 20400149) B20400149
theorem B3966353 : Blo 694316 3966353 := bstep (se 2 (by rfl) ⟨1487382, by rfl⟩ : syracuseStep 3966353 = 2974765) B2974765
theorem B1672595 : Blo 694316 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B7538179 : Blo 694316 7538179 := bstep (se 1 (by rfl) ⟨5653634, by rfl⟩ : syracuseStep 7538179 = 11307269) B11307269
theorem B1115947 : Blo 694316 1115947 := bstep (se 1 (by rfl) ⟨836960, by rfl⟩ : syracuseStep 1115947 = 1673921) B1673921
theorem B1673363 : Blo 694316 1673363 := bstep (se 1 (by rfl) ⟨1255022, by rfl⟩ : syracuseStep 1673363 = 2510045) B2510045
theorem B4065551 : Blo 694316 4065551 := bstep (se 1 (by rfl) ⟨3049163, by rfl⟩ : syracuseStep 4065551 = 6098327) B6098327
theorem B1411447 : Blo 694316 1411447 := bstep (se 1 (by rfl) ⟨1058585, by rfl⟩ : syracuseStep 1411447 = 2117171) B2117171
theorem B3967379 : Blo 694316 3967379 := bstep (se 1 (by rfl) ⟨2975534, by rfl⟩ : syracuseStep 3967379 = 5951069) B5951069
theorem B6687299 : Blo 694316 6687299 := bstep (se 1 (by rfl) ⟨5015474, by rfl⟩ : syracuseStep 6687299 = 10030949) B10030949
theorem B1116857 : Blo 694316 1116857 := bstep (se 2 (by rfl) ⟨418821, by rfl⟩ : syracuseStep 1116857 = 837643) B837643
theorem B3181447 : Blo 694316 3181447 := bstep (se 1 (by rfl) ⟨2386085, by rfl⟩ : syracuseStep 3181447 = 4772171) B4772171
theorem B19106965 : Blo 694316 19106965 := bstep (se 6 (by rfl) ⟨447819, by rfl⟩ : syracuseStep 19106965 = 895639) B895639
theorem B2821321 : Blo 694316 2821321 := bstep (se 2 (by rfl) ⟨1057995, by rfl⟩ : syracuseStep 2821321 = 2115991) B2115991
theorem B3346265 : Blo 694316 3346265 := bstep (se 2 (by rfl) ⟨1254849, by rfl⟩ : syracuseStep 3346265 = 2509699) B2509699
theorem B7737367 : Blo 694316 7737367 := bstep (se 1 (by rfl) ⟨5803025, by rfl⟩ : syracuseStep 7737367 = 11606051) B11606051
theorem B2232893 : Blo 694316 2232893 := bstep (se 3 (by rfl) ⟨418667, by rfl⟩ : syracuseStep 2232893 = 837335) B837335
theorem B3773243 : Blo 694316 3773243 := bstep (se 1 (by rfl) ⟨2829932, by rfl⟩ : syracuseStep 3773243 = 5659865) B5659865
theorem B3019655 : Blo 694316 3019655 := bstep (se 1 (by rfl) ⟨2264741, by rfl⟩ : syracuseStep 3019655 = 4529483) B4529483
theorem B8459437 : Blo 694316 8459437 := bstep (se 3 (by rfl) ⟨1586144, by rfl⟩ : syracuseStep 8459437 = 3172289) B3172289
theorem B4527341 : Blo 694316 4527341 := bstep (se 3 (by rfl) ⟨848876, by rfl⟩ : syracuseStep 4527341 = 1697753) B1697753
theorem B4462199 : Blo 694316 4462199 := bstep (se 1 (by rfl) ⟨3346649, by rfl⟩ : syracuseStep 4462199 = 6693299) B6693299
theorem B988843 : Blo 694316 988843 := bstep (se 1 (by rfl) ⟨741632, by rfl⟩ : syracuseStep 988843 = 1483265) B1483265
theorem B1087417 : Blo 694316 1087417 := bstep (se 2 (by rfl) ⟨407781, by rfl⟩ : syracuseStep 1087417 = 815563) B815563
theorem B1677323 : Blo 694316 1677323 := bstep (se 1 (by rfl) ⟨1257992, by rfl⟩ : syracuseStep 1677323 = 2515985) B2515985
theorem B694331 : Blo 694316 694331 := bstep (se 1 (by rfl) ⟨520748, by rfl⟩ : syracuseStep 694331 = 1041497) B1041497
theorem B694407 : Blo 694316 694407 := bstep (se 1 (by rfl) ⟨520805, by rfl⟩ : syracuseStep 694407 = 1041611) B1041611
theorem B694415 : Blo 694316 694415 := bstep (se 1 (by rfl) ⟨520811, by rfl⟩ : syracuseStep 694415 = 1041623) B1041623
theorem B694459 : Blo 694316 694459 := bstep (se 1 (by rfl) ⟨520844, by rfl⟩ : syracuseStep 694459 = 1041689) B1041689
theorem B3184841 : Blo 694316 3184841 := bstep (se 2 (by rfl) ⟨1194315, by rfl⟩ : syracuseStep 3184841 = 2388631) B2388631
theorem B694535 : Blo 694316 694535 := bstep (se 1 (by rfl) ⟨520901, by rfl⟩ : syracuseStep 694535 = 1041803) B1041803
theorem B694543 : Blo 694316 694543 := bstep (se 1 (by rfl) ⟨520907, by rfl⟩ : syracuseStep 694543 = 1041815) B1041815
theorem B694587 : Blo 694316 694587 := bstep (se 1 (by rfl) ⟨520940, by rfl⟩ : syracuseStep 694587 = 1041881) B1041881
theorem B694663 : Blo 694316 694663 := bstep (se 1 (by rfl) ⟨520997, by rfl⟩ : syracuseStep 694663 = 1041995) B1041995
theorem B694671 : Blo 694316 694671 := bstep (se 1 (by rfl) ⟨521003, by rfl⟩ : syracuseStep 694671 = 1042007) B1042007
theorem B694715 : Blo 694316 694715 := bstep (se 1 (by rfl) ⟨521036, by rfl⟩ : syracuseStep 694715 = 1042073) B1042073
theorem B694791 : Blo 694316 694791 := bstep (se 1 (by rfl) ⟨521093, by rfl⟩ : syracuseStep 694791 = 1042187) B1042187
theorem B694799 : Blo 694316 694799 := bstep (se 1 (by rfl) ⟨521099, by rfl⟩ : syracuseStep 694799 = 1042199) B1042199
theorem B5282333 : Blo 694316 5282333 := bstep (se 3 (by rfl) ⟨990437, by rfl⟩ : syracuseStep 5282333 = 1980875) B1980875
theorem B14326307 : Blo 694316 14326307 := bstep (se 1 (by rfl) ⟨10744730, by rfl⟩ : syracuseStep 14326307 = 21489461) B21489461
theorem B5347883 : Blo 694316 5347883 := bstep (se 1 (by rfl) ⟨4010912, by rfl⟩ : syracuseStep 5347883 = 8021825) B8021825
theorem B694843 : Blo 694316 694843 := bstep (se 1 (by rfl) ⟨521132, by rfl⟩ : syracuseStep 694843 = 1042265) B1042265
theorem B694919 : Blo 694316 694919 := bstep (se 1 (by rfl) ⟨521189, by rfl⟩ : syracuseStep 694919 = 1042379) B1042379
theorem B694927 : Blo 694316 694927 := bstep (se 1 (by rfl) ⟨521195, by rfl⟩ : syracuseStep 694927 = 1042391) B1042391
theorem B694971 : Blo 694316 694971 := bstep (se 1 (by rfl) ⟨521228, by rfl⟩ : syracuseStep 694971 = 1042457) B1042457
theorem B695047 : Blo 694316 695047 := bstep (se 1 (by rfl) ⟨521285, by rfl⟩ : syracuseStep 695047 = 1042571) B1042571
theorem B1252111 : Blo 694316 1252111 := bstep (se 1 (by rfl) ⟨939083, by rfl⟩ : syracuseStep 1252111 = 1878167) B1878167
theorem B695055 : Blo 694316 695055 := bstep (se 1 (by rfl) ⟨521291, by rfl⟩ : syracuseStep 695055 = 1042583) B1042583
theorem B10033955 : Blo 694316 10033955 := bstep (se 1 (by rfl) ⟨7525466, by rfl⟩ : syracuseStep 10033955 = 15050933) B15050933
theorem B695099 : Blo 694316 695099 := bstep (se 1 (by rfl) ⟨521324, by rfl⟩ : syracuseStep 695099 = 1042649) B1042649
theorem B2235251 : Blo 694316 2235251 := bstep (se 1 (by rfl) ⟨1676438, by rfl⟩ : syracuseStep 2235251 = 3352877) B3352877
theorem B695175 : Blo 694316 695175 := bstep (se 1 (by rfl) ⟨521381, by rfl⟩ : syracuseStep 695175 = 1042763) B1042763
theorem B695183 : Blo 694316 695183 := bstep (se 1 (by rfl) ⟨521387, by rfl⟩ : syracuseStep 695183 = 1042775) B1042775
theorem B695227 : Blo 694316 695227 := bstep (se 1 (by rfl) ⟨521420, by rfl⟩ : syracuseStep 695227 = 1042841) B1042841
theorem B695303 : Blo 694316 695303 := bstep (se 1 (by rfl) ⟨521477, by rfl⟩ : syracuseStep 695303 = 1042955) B1042955
theorem B695311 : Blo 694316 695311 := bstep (se 1 (by rfl) ⟨521483, by rfl⟩ : syracuseStep 695311 = 1042967) B1042967
theorem B695355 : Blo 694316 695355 := bstep (se 1 (by rfl) ⟨521516, by rfl⟩ : syracuseStep 695355 = 1043033) B1043033
theorem B695431 : Blo 694316 695431 := bstep (se 1 (by rfl) ⟨521573, by rfl⟩ : syracuseStep 695431 = 1043147) B1043147
theorem B695439 : Blo 694316 695439 := bstep (se 1 (by rfl) ⟨521579, by rfl⟩ : syracuseStep 695439 = 1043159) B1043159
theorem B695483 : Blo 694316 695483 := bstep (se 1 (by rfl) ⟨521612, by rfl⟩ : syracuseStep 695483 = 1043225) B1043225
theorem B695559 : Blo 694316 695559 := bstep (se 1 (by rfl) ⟨521669, by rfl⟩ : syracuseStep 695559 = 1043339) B1043339
theorem B695567 : Blo 694316 695567 := bstep (se 1 (by rfl) ⟨521675, by rfl⟩ : syracuseStep 695567 = 1043351) B1043351
theorem B695611 : Blo 694316 695611 := bstep (se 1 (by rfl) ⟨521708, by rfl⟩ : syracuseStep 695611 = 1043417) B1043417
theorem B5020987 : Blo 694316 5020987 := bstep (se 1 (by rfl) ⟨3765740, by rfl⟩ : syracuseStep 5020987 = 7531481) B7531481
theorem B695687 : Blo 694316 695687 := bstep (se 1 (by rfl) ⟨521765, by rfl⟩ : syracuseStep 695687 = 1043531) B1043531
theorem B695695 : Blo 694316 695695 := bstep (se 1 (by rfl) ⟨521771, by rfl⟩ : syracuseStep 695695 = 1043543) B1043543
theorem B695739 : Blo 694316 695739 := bstep (se 1 (by rfl) ⟨521804, by rfl⟩ : syracuseStep 695739 = 1043609) B1043609
theorem B18062797 : Blo 694316 18062797 := bstep (se 3 (by rfl) ⟨3386774, by rfl⟩ : syracuseStep 18062797 = 6773549) B6773549
theorem B695815 : Blo 694316 695815 := bstep (se 1 (by rfl) ⟨521861, by rfl⟩ : syracuseStep 695815 = 1043723) B1043723
theorem B695823 : Blo 694316 695823 := bstep (se 1 (by rfl) ⟨521867, by rfl⟩ : syracuseStep 695823 = 1043735) B1043735
theorem B695867 : Blo 694316 695867 := bstep (se 1 (by rfl) ⟨521900, by rfl⟩ : syracuseStep 695867 = 1043801) B1043801
theorem B695943 : Blo 694316 695943 := bstep (se 1 (by rfl) ⟨521957, by rfl⟩ : syracuseStep 695943 = 1043915) B1043915
theorem B695951 : Blo 694316 695951 := bstep (se 1 (by rfl) ⟨521963, by rfl⟩ : syracuseStep 695951 = 1043927) B1043927
theorem B16293527 : Blo 694316 16293527 := bstep (se 1 (by rfl) ⟨12220145, by rfl⟩ : syracuseStep 16293527 = 24440291) B24440291
theorem B695995 : Blo 694316 695995 := bstep (se 1 (by rfl) ⟨521996, by rfl⟩ : syracuseStep 695995 = 1043993) B1043993
theorem B696071 : Blo 694316 696071 := bstep (se 1 (by rfl) ⟨522053, by rfl⟩ : syracuseStep 696071 = 1044107) B1044107
theorem B2006795 : Blo 694316 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B696079 : Blo 694316 696079 := bstep (se 1 (by rfl) ⟨522059, by rfl⟩ : syracuseStep 696079 = 1044119) B1044119
theorem B1613611 : Blo 694316 1613611 := bstep (se 1 (by rfl) ⟨1210208, by rfl⟩ : syracuseStep 1613611 = 2420417) B2420417
theorem B696123 : Blo 694316 696123 := bstep (se 1 (by rfl) ⟨522092, by rfl⟩ : syracuseStep 696123 = 1044185) B1044185
theorem B696199 : Blo 694316 696199 := bstep (se 1 (by rfl) ⟨522149, by rfl⟩ : syracuseStep 696199 = 1044299) B1044299
theorem B696207 : Blo 694316 696207 := bstep (se 1 (by rfl) ⟨522155, by rfl⟩ : syracuseStep 696207 = 1044311) B1044311
theorem B696251 : Blo 694316 696251 := bstep (se 1 (by rfl) ⟨522188, by rfl⟩ : syracuseStep 696251 = 1044377) B1044377
theorem B696327 : Blo 694316 696327 := bstep (se 1 (by rfl) ⟨522245, by rfl⟩ : syracuseStep 696327 = 1044491) B1044491
theorem B696335 : Blo 694316 696335 := bstep (se 1 (by rfl) ⟨522251, by rfl⟩ : syracuseStep 696335 = 1044503) B1044503
theorem B696379 : Blo 694316 696379 := bstep (se 1 (by rfl) ⟨522284, by rfl⟩ : syracuseStep 696379 = 1044569) B1044569
theorem B1253495 : Blo 694316 1253495 := bstep (se 1 (by rfl) ⟨940121, by rfl⟩ : syracuseStep 1253495 = 1880243) B1880243
theorem B696455 : Blo 694316 696455 := bstep (se 1 (by rfl) ⟨522341, by rfl⟩ : syracuseStep 696455 = 1044683) B1044683
theorem B696463 : Blo 694316 696463 := bstep (se 1 (by rfl) ⟨522347, by rfl⟩ : syracuseStep 696463 = 1044695) B1044695
theorem B696507 : Blo 694316 696507 := bstep (se 1 (by rfl) ⟨522380, by rfl⟩ : syracuseStep 696507 = 1044761) B1044761
theorem B696583 : Blo 694316 696583 := bstep (se 1 (by rfl) ⟨522437, by rfl⟩ : syracuseStep 696583 = 1044875) B1044875
theorem B696591 : Blo 694316 696591 := bstep (se 1 (by rfl) ⟨522443, by rfl⟩ : syracuseStep 696591 = 1044887) B1044887
theorem B991531 : Blo 694316 991531 := bstep (se 1 (by rfl) ⟨743648, by rfl⟩ : syracuseStep 991531 = 1487297) B1487297
theorem B696635 : Blo 694316 696635 := bstep (se 1 (by rfl) ⟨522476, by rfl⟩ : syracuseStep 696635 = 1044953) B1044953
theorem B696711 : Blo 694316 696711 := bstep (se 1 (by rfl) ⟨522533, by rfl⟩ : syracuseStep 696711 = 1045067) B1045067
theorem B696719 : Blo 694316 696719 := bstep (se 1 (by rfl) ⟨522539, by rfl⟩ : syracuseStep 696719 = 1045079) B1045079
theorem B696763 : Blo 694316 696763 := bstep (se 1 (by rfl) ⟨522572, by rfl⟩ : syracuseStep 696763 = 1045145) B1045145
theorem B696839 : Blo 694316 696839 := bstep (se 1 (by rfl) ⟨522629, by rfl⟩ : syracuseStep 696839 = 1045259) B1045259
theorem B3973643 : Blo 694316 3973643 := bstep (se 1 (by rfl) ⟨2980232, by rfl⟩ : syracuseStep 3973643 = 5960465) B5960465
theorem B991759 : Blo 694316 991759 := bstep (se 1 (by rfl) ⟨743819, by rfl⟩ : syracuseStep 991759 = 1487639) B1487639
theorem B696847 : Blo 694316 696847 := bstep (se 1 (by rfl) ⟨522635, by rfl⟩ : syracuseStep 696847 = 1045271) B1045271
theorem B1319483 : Blo 694316 1319483 := bstep (se 1 (by rfl) ⟨989612, by rfl⟩ : syracuseStep 1319483 = 1979225) B1979225
theorem B696891 : Blo 694316 696891 := bstep (se 1 (by rfl) ⟨522668, by rfl⟩ : syracuseStep 696891 = 1045337) B1045337
theorem B696967 : Blo 694316 696967 := bstep (se 1 (by rfl) ⟨522725, by rfl⟩ : syracuseStep 696967 = 1045451) B1045451
theorem B696975 : Blo 694316 696975 := bstep (se 1 (by rfl) ⟨522731, by rfl⟩ : syracuseStep 696975 = 1045463) B1045463
theorem B697019 : Blo 694316 697019 := bstep (se 1 (by rfl) ⟨522764, by rfl⟩ : syracuseStep 697019 = 1045529) B1045529
theorem B697095 : Blo 694316 697095 := bstep (se 1 (by rfl) ⟨522821, by rfl⟩ : syracuseStep 697095 = 1045643) B1045643
theorem B697103 : Blo 694316 697103 := bstep (se 1 (by rfl) ⟨522827, by rfl⟩ : syracuseStep 697103 = 1045655) B1045655
theorem B697147 : Blo 694316 697147 := bstep (se 1 (by rfl) ⟨522860, by rfl⟩ : syracuseStep 697147 = 1045721) B1045721
theorem B992135 : Blo 694316 992135 := bstep (se 1 (by rfl) ⟨744101, by rfl⟩ : syracuseStep 992135 = 1488203) B1488203
theorem B697223 : Blo 694316 697223 := bstep (se 1 (by rfl) ⟨522917, by rfl⟩ : syracuseStep 697223 = 1045835) B1045835
theorem B697231 : Blo 694316 697231 := bstep (se 1 (by rfl) ⟨522923, by rfl⟩ : syracuseStep 697231 = 1045847) B1045847
theorem B1483667 : Blo 694316 1483667 := bstep (se 1 (by rfl) ⟨1112750, by rfl⟩ : syracuseStep 1483667 = 2225501) B2225501
theorem B697275 : Blo 694316 697275 := bstep (se 1 (by rfl) ⟨522956, by rfl⟩ : syracuseStep 697275 = 1045913) B1045913
theorem B697351 : Blo 694316 697351 := bstep (se 1 (by rfl) ⟨523013, by rfl⟩ : syracuseStep 697351 = 1046027) B1046027
theorem B697359 : Blo 694316 697359 := bstep (se 1 (by rfl) ⟨523019, by rfl⟩ : syracuseStep 697359 = 1046039) B1046039
theorem B1319969 : Blo 694316 1319969 := bstep (se 2 (by rfl) ⟨494988, by rfl⟩ : syracuseStep 1319969 = 989977) B989977
theorem B697403 : Blo 694316 697403 := bstep (se 1 (by rfl) ⟨523052, by rfl⟩ : syracuseStep 697403 = 1046105) B1046105
theorem B1877107 : Blo 694316 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B697479 : Blo 694316 697479 := bstep (se 1 (by rfl) ⟨523109, by rfl⟩ : syracuseStep 697479 = 1046219) B1046219
theorem B697487 : Blo 694316 697487 := bstep (se 1 (by rfl) ⟨523115, by rfl⟩ : syracuseStep 697487 = 1046231) B1046231
theorem B697531 : Blo 694316 697531 := bstep (se 1 (by rfl) ⟨523148, by rfl⟩ : syracuseStep 697531 = 1046297) B1046297
theorem B697607 : Blo 694316 697607 := bstep (se 1 (by rfl) ⟨523205, by rfl⟩ : syracuseStep 697607 = 1046411) B1046411
theorem B697615 : Blo 694316 697615 := bstep (se 1 (by rfl) ⟨523211, by rfl⟩ : syracuseStep 697615 = 1046423) B1046423
theorem B697659 : Blo 694316 697659 := bstep (se 1 (by rfl) ⟨523244, by rfl⟩ : syracuseStep 697659 = 1046489) B1046489
theorem B697735 : Blo 694316 697735 := bstep (se 1 (by rfl) ⟨523301, by rfl⟩ : syracuseStep 697735 = 1046603) B1046603
theorem B697743 : Blo 694316 697743 := bstep (se 1 (by rfl) ⟨523307, by rfl⟩ : syracuseStep 697743 = 1046615) B1046615
theorem B697787 : Blo 694316 697787 := bstep (se 1 (by rfl) ⟨523340, by rfl⟩ : syracuseStep 697787 = 1046681) B1046681
theorem B697863 : Blo 694316 697863 := bstep (se 1 (by rfl) ⟨523397, by rfl⟩ : syracuseStep 697863 = 1046795) B1046795
theorem B697871 : Blo 694316 697871 := bstep (se 1 (by rfl) ⟨523403, by rfl⟩ : syracuseStep 697871 = 1046807) B1046807
theorem B697915 : Blo 694316 697915 := bstep (se 1 (by rfl) ⟨523436, by rfl⟩ : syracuseStep 697915 = 1046873) B1046873
theorem B697991 : Blo 694316 697991 := bstep (se 1 (by rfl) ⟨523493, by rfl⟩ : syracuseStep 697991 = 1046987) B1046987
theorem B697999 : Blo 694316 697999 := bstep (se 1 (by rfl) ⟨523499, by rfl⟩ : syracuseStep 697999 = 1046999) B1046999
theorem B698043 : Blo 694316 698043 := bstep (se 1 (by rfl) ⟨523532, by rfl⟩ : syracuseStep 698043 = 1047065) B1047065
theorem B6334145 : Blo 694316 6334145 := bstep (se 2 (by rfl) ⟨2375304, by rfl⟩ : syracuseStep 6334145 = 4750609) B4750609
theorem B698119 : Blo 694316 698119 := bstep (se 1 (by rfl) ⟨523589, by rfl⟩ : syracuseStep 698119 = 1047179) B1047179
theorem B698127 : Blo 694316 698127 := bstep (se 1 (by rfl) ⟨523595, by rfl⟩ : syracuseStep 698127 = 1047191) B1047191
theorem B698171 : Blo 694316 698171 := bstep (se 1 (by rfl) ⟨523628, by rfl⟩ : syracuseStep 698171 = 1047257) B1047257
theorem B698247 : Blo 694316 698247 := bstep (se 1 (by rfl) ⟨523685, by rfl⟩ : syracuseStep 698247 = 1047371) B1047371
theorem B698255 : Blo 694316 698255 := bstep (se 1 (by rfl) ⟨523691, by rfl⟩ : syracuseStep 698255 = 1047383) B1047383
theorem B698299 : Blo 694316 698299 := bstep (se 1 (by rfl) ⟨523724, by rfl⟩ : syracuseStep 698299 = 1047449) B1047449
theorem B5941259 : Blo 694316 5941259 := bstep (se 1 (by rfl) ⟨4455944, by rfl⟩ : syracuseStep 5941259 = 8911889) B8911889
theorem B993593 : Blo 694316 993593 := bstep (se 2 (by rfl) ⟨372597, by rfl⟩ : syracuseStep 993593 = 745195) B745195
theorem B3516857 : Blo 694316 3516857 := bstep (se 2 (by rfl) ⟨1318821, by rfl⟩ : syracuseStep 3516857 = 2637643) B2637643
theorem B7514653 : Blo 694316 7514653 := bstep (se 3 (by rfl) ⟨1408997, by rfl⟩ : syracuseStep 7514653 = 2817995) B2817995
theorem B25340633 : Blo 694316 25340633 := bstep (se 2 (by rfl) ⟨9502737, by rfl⟩ : syracuseStep 25340633 = 19005475) B19005475
theorem B5286707 : Blo 694316 5286707 := bstep (se 1 (by rfl) ⟨3965030, by rfl⟩ : syracuseStep 5286707 = 7930061) B7930061
theorem B3353491 : Blo 694316 3353491 := bstep (se 1 (by rfl) ⟨2515118, by rfl⟩ : syracuseStep 3353491 = 5030237) B5030237
theorem B1321913 : Blo 694316 1321913 := bstep (se 2 (by rfl) ⟨495717, by rfl⟩ : syracuseStep 1321913 = 991435) B991435
theorem B6335891 : Blo 694316 6335891 := bstep (se 1 (by rfl) ⟨4751918, by rfl⟩ : syracuseStep 6335891 = 9503837) B9503837
theorem B1879595 : Blo 694316 1879595 := bstep (se 1 (by rfl) ⟨1409696, by rfl⟩ : syracuseStep 1879595 = 2819393) B2819393
theorem B3976877 : Blo 694316 3976877 := bstep (se 3 (by rfl) ⟨745664, by rfl⟩ : syracuseStep 3976877 = 1491329) B1491329
theorem B3518153 : Blo 694316 3518153 := bstep (se 2 (by rfl) ⟨1319307, by rfl⟩ : syracuseStep 3518153 = 2638615) B2638615
theorem B1323067 : Blo 694316 1323067 := bstep (se 1 (by rfl) ⟨992300, by rfl⟩ : syracuseStep 1323067 = 1984601) B1984601
theorem B7909649 : Blo 694316 7909649 := bstep (se 2 (by rfl) ⟨2966118, by rfl⟩ : syracuseStep 7909649 = 5932237) B5932237
theorem B1978825 : Blo 694316 1978825 := bstep (se 2 (by rfl) ⟨742059, by rfl⟩ : syracuseStep 1978825 = 1484119) B1484119
theorem B1323553 : Blo 694316 1323553 := bstep (se 2 (by rfl) ⟨496332, by rfl⟩ : syracuseStep 1323553 = 992665) B992665
theorem B1880761 : Blo 694316 1880761 := bstep (se 2 (by rfl) ⟨705285, by rfl⟩ : syracuseStep 1880761 = 1410571) B1410571
theorem B3355337 : Blo 694316 3355337 := bstep (se 2 (by rfl) ⟨1258251, by rfl⟩ : syracuseStep 3355337 = 2516503) B2516503
theorem B1880891 : Blo 694316 1880891 := bstep (se 1 (by rfl) ⟨1410668, by rfl⟩ : syracuseStep 1880891 = 2821337) B2821337
theorem B4764619 : Blo 694316 4764619 := bstep (se 1 (by rfl) ⟨3573464, by rfl⟩ : syracuseStep 4764619 = 7146929) B7146929
theorem B1881149 : Blo 694316 1881149 := bstep (se 3 (by rfl) ⟨352715, by rfl⟩ : syracuseStep 1881149 = 705431) B705431
theorem B6698371 : Blo 694316 6698371 := bstep (se 1 (by rfl) ⟨5023778, by rfl⟩ : syracuseStep 6698371 = 10047557) B10047557
theorem B5092793 : Blo 694316 5092793 := bstep (se 2 (by rfl) ⟨1909797, by rfl⟩ : syracuseStep 5092793 = 3819595) B3819595
theorem B1324745 : Blo 694316 1324745 := bstep (se 2 (by rfl) ⟨496779, by rfl⟩ : syracuseStep 1324745 = 993559) B993559
theorem B9647923 : Blo 694316 9647923 := bstep (se 1 (by rfl) ⟨7235942, by rfl⟩ : syracuseStep 9647923 = 14471885) B14471885
theorem B1488955 : Blo 694316 1488955 := bstep (se 1 (by rfl) ⟨1116716, by rfl⟩ : syracuseStep 1488955 = 2233433) B2233433
theorem B1980683 : Blo 694316 1980683 := bstep (se 1 (by rfl) ⟨1485512, by rfl⟩ : syracuseStep 1980683 = 2971025) B2971025
theorem B5945633 : Blo 694316 5945633 := bstep (se 2 (by rfl) ⟨2229612, by rfl⟩ : syracuseStep 5945633 = 4459225) B4459225
theorem B1325459 : Blo 694316 1325459 := bstep (se 1 (by rfl) ⟨994094, by rfl⟩ : syracuseStep 1325459 = 1988189) B1988189
theorem B6699449 : Blo 694316 6699449 := bstep (se 2 (by rfl) ⟨2512293, by rfl⟩ : syracuseStep 6699449 = 5024587) B5024587
theorem B1325497 : Blo 694316 1325497 := bstep (se 2 (by rfl) ⟨497061, by rfl⟩ : syracuseStep 1325497 = 994123) B994123
theorem B2636489 : Blo 694316 2636489 := bstep (se 2 (by rfl) ⟨988683, by rfl⟩ : syracuseStep 2636489 = 1977367) B1977367
theorem B1981331 : Blo 694316 1981331 := bstep (se 1 (by rfl) ⟨1485998, by rfl⟩ : syracuseStep 1981331 = 2971997) B2971997
theorem B114342853 : Blo 694316 114342853 := bstep (se 4 (by rfl) ⟨10719642, by rfl⟩ : syracuseStep 114342853 = 21439285) B21439285
theorem B7912565 : Blo 694316 7912565 := bstep (se 5 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 7912565 = 741803) B741803
theorem B1981559 : Blo 694316 1981559 := bstep (se 1 (by rfl) ⟨1486169, by rfl⟩ : syracuseStep 1981559 = 2972339) B2972339
theorem B4242689 : Blo 694316 4242689 := bstep (se 2 (by rfl) ⟨1591008, by rfl⟩ : syracuseStep 4242689 = 3182017) B3182017
theorem B1785131 : Blo 694316 1785131 := bstep (se 1 (by rfl) ⟨1338848, by rfl⟩ : syracuseStep 1785131 = 2677697) B2677697
theorem B10010141 : Blo 694316 10010141 := bstep (se 3 (by rfl) ⟨1876901, by rfl⟩ : syracuseStep 10010141 = 3753803) B3753803
theorem B4898333 : Blo 694316 4898333 := bstep (se 3 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 4898333 = 1836875) B1836875
theorem B835115 : Blo 694316 835115 := bstep (se 1 (by rfl) ⟨626336, by rfl⟩ : syracuseStep 835115 = 1252673) B1252673
theorem B2571895 : Blo 694316 2571895 := bstep (se 1 (by rfl) ⟨1928921, by rfl⟩ : syracuseStep 2571895 = 3857843) B3857843
theorem B2637431 : Blo 694316 2637431 := bstep (se 1 (by rfl) ⟨1978073, by rfl⟩ : syracuseStep 2637431 = 3956147) B3956147
theorem B7946099 : Blo 694316 7946099 := bstep (se 1 (by rfl) ⟨5959574, by rfl⟩ : syracuseStep 7946099 = 11919149) B11919149
theorem B1589263 : Blo 694316 1589263 := bstep (se 1 (by rfl) ⟨1191947, by rfl⟩ : syracuseStep 1589263 = 2383895) B2383895
theorem B1654985 : Blo 694316 1654985 := bstep (se 2 (by rfl) ⟨620619, by rfl⟩ : syracuseStep 1654985 = 1241239) B1241239
theorem B6701447 : Blo 694316 6701447 := bstep (se 1 (by rfl) ⟨5026085, by rfl⟩ : syracuseStep 6701447 = 10052171) B10052171
theorem B1491347 : Blo 694316 1491347 := bstep (se 1 (by rfl) ⟨1118510, by rfl⟩ : syracuseStep 1491347 = 2237021) B2237021
theorem B2638403 : Blo 694316 2638403 := bstep (se 1 (by rfl) ⟨1978802, by rfl⟩ : syracuseStep 2638403 = 3957605) B3957605
theorem B2343815 : Blo 694316 2343815 := bstep (se 1 (by rfl) ⟨1757861, by rfl⟩ : syracuseStep 2343815 = 3515723) B3515723
theorem B2540497 : Blo 694316 2540497 := bstep (se 2 (by rfl) ⟨952686, by rfl⟩ : syracuseStep 2540497 = 1905373) B1905373
theorem B836615 : Blo 694316 836615 := bstep (se 1 (by rfl) ⟨627461, by rfl⟩ : syracuseStep 836615 = 1254923) B1254923
theorem B11420909 : Blo 694316 11420909 := bstep (se 3 (by rfl) ⟨2141420, by rfl⟩ : syracuseStep 11420909 = 4282841) B4282841
theorem B2344193 : Blo 694316 2344193 := bstep (se 2 (by rfl) ⟨879072, by rfl⟩ : syracuseStep 2344193 = 1758145) B1758145
theorem B3523985 : Blo 694316 3523985 := bstep (se 2 (by rfl) ⟨1321494, by rfl⟩ : syracuseStep 3523985 = 2642989) B2642989
theorem B2901547 : Blo 694316 2901547 := bstep (se 1 (by rfl) ⟨2176160, by rfl⟩ : syracuseStep 2901547 = 4352321) B4352321
theorem B2115443 : Blo 694316 2115443 := bstep (se 1 (by rfl) ⟨1586582, by rfl⟩ : syracuseStep 2115443 = 3173165) B3173165
theorem B4245533 : Blo 694316 4245533 := bstep (se 3 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 4245533 = 1592075) B1592075
theorem B1361953 : Blo 694316 1361953 := bstep (se 2 (by rfl) ⟨510732, by rfl⟩ : syracuseStep 1361953 = 1021465) B1021465
theorem B2345003 : Blo 694316 2345003 := bstep (se 1 (by rfl) ⟨1758752, by rfl⟩ : syracuseStep 2345003 = 3517505) B3517505
theorem B15091757 : Blo 694316 15091757 := bstep (se 3 (by rfl) ⟨2829704, by rfl⟩ : syracuseStep 15091757 = 5659409) B5659409
theorem B2640073 : Blo 694316 2640073 := bstep (se 2 (by rfl) ⟨990027, by rfl⟩ : syracuseStep 2640073 = 1980055) B1980055
theorem B1984783 : Blo 694316 1984783 := bstep (se 1 (by rfl) ⟨1488587, by rfl⟩ : syracuseStep 1984783 = 2977175) B2977175
theorem B5294483 : Blo 694316 5294483 := bstep (se 1 (by rfl) ⟨3970862, by rfl⟩ : syracuseStep 5294483 = 7941725) B7941725
theorem B1985057 : Blo 694316 1985057 := bstep (se 2 (by rfl) ⟨744396, by rfl⟩ : syracuseStep 1985057 = 1488793) B1488793
theorem B3754669 : Blo 694316 3754669 := bstep (se 3 (by rfl) ⟨704000, by rfl⟩ : syracuseStep 3754669 = 1408001) B1408001
theorem B1428239 : Blo 694316 1428239 := bstep (se 1 (by rfl) ⟨1071179, by rfl⟩ : syracuseStep 1428239 = 2142359) B2142359
theorem B2116381 : Blo 694316 2116381 := bstep (se 3 (by rfl) ⟨396821, by rfl⟩ : syracuseStep 2116381 = 793643) B793643
theorem B1592183 : Blo 694316 1592183 := bstep (se 1 (by rfl) ⟨1194137, by rfl⟩ : syracuseStep 1592183 = 2388275) B2388275
theorem B1789199 : Blo 694316 1789199 := bstep (se 1 (by rfl) ⟨1341899, by rfl⟩ : syracuseStep 1789199 = 2683799) B2683799
theorem B2346299 : Blo 694316 2346299 := bstep (se 1 (by rfl) ⟨1759724, by rfl⟩ : syracuseStep 2346299 = 3519449) B3519449
theorem B2116999 : Blo 694316 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B3526091 : Blo 694316 3526091 := bstep (se 1 (by rfl) ⟨2644568, by rfl⟩ : syracuseStep 3526091 = 5289137) B5289137
theorem B1986059 : Blo 694316 1986059 := bstep (se 1 (by rfl) ⟨1489544, by rfl⟩ : syracuseStep 1986059 = 2979089) B2979089
theorem B2117267 : Blo 694316 2117267 := bstep (se 1 (by rfl) ⟨1587950, by rfl⟩ : syracuseStep 2117267 = 3175901) B3175901
theorem B3526415 : Blo 694316 3526415 := bstep (se 1 (by rfl) ⟨2644811, by rfl⟩ : syracuseStep 3526415 = 5289623) B5289623
theorem B2346785 : Blo 694316 2346785 := bstep (se 2 (by rfl) ⟨880044, by rfl⟩ : syracuseStep 2346785 = 1760089) B1760089
theorem B1986457 : Blo 694316 1986457 := bstep (se 2 (by rfl) ⟨744921, by rfl⟩ : syracuseStep 1986457 = 1489843) B1489843
theorem B1986707 : Blo 694316 1986707 := bstep (se 1 (by rfl) ⟨1490030, by rfl⟩ : syracuseStep 1986707 = 2980061) B2980061
theorem B2347379 : Blo 694316 2347379 := bstep (se 1 (by rfl) ⟨1760534, by rfl⟩ : syracuseStep 2347379 = 3521069) B3521069
theorem B2642291 : Blo 694316 2642291 := bstep (se 1 (by rfl) ⟨1981718, by rfl⟩ : syracuseStep 2642291 = 3963437) B3963437
theorem B2511371 : Blo 694316 2511371 := bstep (se 1 (by rfl) ⟨1883528, by rfl⟩ : syracuseStep 2511371 = 3767057) B3767057
theorem B13587011 : Blo 694316 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B6771377 : Blo 694316 6771377 := bstep (se 2 (by rfl) ⟨2539266, by rfl⟩ : syracuseStep 6771377 = 5078533) B5078533
theorem B13718197 : Blo 694316 13718197 := bstep (se 5 (by rfl) ⟨643040, by rfl⟩ : syracuseStep 13718197 = 1286081) B1286081
theorem B1757963 : Blo 694316 1757963 := bstep (se 1 (by rfl) ⟨1318472, by rfl⟩ : syracuseStep 1757963 = 2636945) B2636945
theorem B1987699 : Blo 694316 1987699 := bstep (se 1 (by rfl) ⟨1490774, by rfl⟩ : syracuseStep 1987699 = 2981549) B2981549
theorem B3527873 : Blo 694316 3527873 := bstep (se 2 (by rfl) ⟨1322952, by rfl⟩ : syracuseStep 3527873 = 2645905) B2645905
theorem B2118923 : Blo 694316 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B5363003 : Blo 694316 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B1758611 : Blo 694316 1758611 := bstep (se 1 (by rfl) ⟨1318958, by rfl⟩ : syracuseStep 1758611 = 2637917) B2637917
theorem B939451 : Blo 694316 939451 := bstep (se 1 (by rfl) ⟨704588, by rfl⟩ : syracuseStep 939451 = 1409177) B1409177
theorem B742927 : Blo 694316 742927 := bstep (se 1 (by rfl) ⟨557195, by rfl⟩ : syracuseStep 742927 = 1114391) B1114391
theorem B1758905 : Blo 694316 1758905 := bstep (se 2 (by rfl) ⟨659589, by rfl⟩ : syracuseStep 1758905 = 1319179) B1319179
theorem B743303 : Blo 694316 743303 := bstep (se 1 (by rfl) ⟨557477, by rfl⟩ : syracuseStep 743303 = 1114955) B1114955
theorem B3758147 : Blo 694316 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B1562759 : Blo 694316 1562759 := bstep (se 1 (by rfl) ⟨1172069, by rfl⟩ : syracuseStep 1562759 = 2344139) B2344139
theorem B16963829 : Blo 694316 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B1562939 : Blo 694316 1562939 := bstep (se 1 (by rfl) ⟨1172204, by rfl⟩ : syracuseStep 1562939 = 2344409) B2344409
theorem B1759603 : Blo 694316 1759603 := bstep (se 1 (by rfl) ⟨1319702, by rfl⟩ : syracuseStep 1759603 = 2639405) B2639405
theorem B1563065 : Blo 694316 1563065 := bstep (se 2 (by rfl) ⟨586149, by rfl⟩ : syracuseStep 1563065 = 1172299) B1172299
theorem B2644433 : Blo 694316 2644433 := bstep (se 2 (by rfl) ⟨991662, by rfl⟩ : syracuseStep 2644433 = 1983325) B1983325
theorem B3529169 : Blo 694316 3529169 := bstep (se 2 (by rfl) ⟨1323438, by rfl⟩ : syracuseStep 3529169 = 2646877) B2646877
theorem B1759745 : Blo 694316 1759745 := bstep (se 2 (by rfl) ⟨659904, by rfl⟩ : syracuseStep 1759745 = 1319809) B1319809
theorem B1563407 : Blo 694316 1563407 := bstep (se 1 (by rfl) ⟨1172555, by rfl⟩ : syracuseStep 1563407 = 2345111) B2345111
theorem B2644751 : Blo 694316 2644751 := bstep (se 1 (by rfl) ⟨1983563, by rfl⟩ : syracuseStep 2644751 = 3967127) B3967127
theorem B1563425 : Blo 694316 1563425 := bstep (se 2 (by rfl) ⟨586284, by rfl⟩ : syracuseStep 1563425 = 1172569) B1172569
theorem B3758993 : Blo 694316 3758993 := bstep (se 2 (by rfl) ⟨1409622, by rfl⟩ : syracuseStep 3758993 = 2819245) B2819245
theorem B2349971 : Blo 694316 2349971 := bstep (se 1 (by rfl) ⟨1762478, by rfl⟩ : syracuseStep 2349971 = 3524957) B3524957
theorem B1760201 : Blo 694316 1760201 := bstep (se 2 (by rfl) ⟨660075, by rfl⟩ : syracuseStep 1760201 = 1320151) B1320151
theorem B3955715 : Blo 694316 3955715 := bstep (se 1 (by rfl) ⟨2966786, by rfl⟩ : syracuseStep 3955715 = 5933573) B5933573
theorem B1563767 : Blo 694316 1563767 := bstep (se 1 (by rfl) ⟨1172825, by rfl⟩ : syracuseStep 1563767 = 2345651) B2345651
theorem B1563947 : Blo 694316 1563947 := bstep (se 1 (by rfl) ⟨1172960, by rfl⟩ : syracuseStep 1563947 = 2345921) B2345921
theorem B1760555 : Blo 694316 1760555 := bstep (se 1 (by rfl) ⟨1320416, by rfl⟩ : syracuseStep 1760555 = 2640833) B2640833
theorem B1564307 : Blo 694316 1564307 := bstep (se 1 (by rfl) ⟨1173230, by rfl⟩ : syracuseStep 1564307 = 2346461) B2346461
theorem B1564361 : Blo 694316 1564361 := bstep (se 2 (by rfl) ⟨586635, by rfl⟩ : syracuseStep 1564361 = 1173271) B1173271
theorem B5955443 : Blo 694316 5955443 := bstep (se 1 (by rfl) ⟨4466582, by rfl⟩ : syracuseStep 5955443 = 8933165) B8933165
theorem B3563777 : Blo 694316 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B1761547 : Blo 694316 1761547 := bstep (se 1 (by rfl) ⟨1321160, by rfl⟩ : syracuseStep 1761547 = 2642321) B2642321
theorem B2351375 : Blo 694316 2351375 := bstep (se 1 (by rfl) ⟨1763531, by rfl⟩ : syracuseStep 2351375 = 3527063) B3527063
theorem B1171847 : Blo 694316 1171847 := bstep (se 1 (by rfl) ⟨878885, by rfl⟩ : syracuseStep 1171847 = 1757771) B1757771
theorem B1565063 : Blo 694316 1565063 := bstep (se 1 (by rfl) ⟨1173797, by rfl⟩ : syracuseStep 1565063 = 2347595) B2347595
theorem B1761689 : Blo 694316 1761689 := bstep (se 2 (by rfl) ⟨660633, by rfl⟩ : syracuseStep 1761689 = 1321267) B1321267
theorem B942521 : Blo 694316 942521 := bstep (se 2 (by rfl) ⟨353445, by rfl⟩ : syracuseStep 942521 = 706891) B706891
theorem B3531275 : Blo 694316 3531275 := bstep (se 1 (by rfl) ⟨2648456, by rfl⟩ : syracuseStep 3531275 = 5296913) B5296913
theorem B2351645 : Blo 694316 2351645 := bstep (se 3 (by rfl) ⟨440933, by rfl⟩ : syracuseStep 2351645 = 881867) B881867
theorem B16114211 : Blo 694316 16114211 := bstep (se 1 (by rfl) ⟨12085658, by rfl⟩ : syracuseStep 16114211 = 24171317) B24171317
theorem B1565243 : Blo 694316 1565243 := bstep (se 1 (by rfl) ⟨1173932, by rfl⟩ : syracuseStep 1565243 = 2347865) B2347865
theorem B1761851 : Blo 694316 1761851 := bstep (se 1 (by rfl) ⟨1321388, by rfl⟩ : syracuseStep 1761851 = 2642777) B2642777
theorem B3531437 : Blo 694316 3531437 := bstep (se 3 (by rfl) ⟨662144, by rfl⟩ : syracuseStep 3531437 = 1324289) B1324289
theorem B1565369 : Blo 694316 1565369 := bstep (se 2 (by rfl) ⟨587013, by rfl⟩ : syracuseStep 1565369 = 1174027) B1174027
theorem B1762195 : Blo 694316 1762195 := bstep (se 1 (by rfl) ⟨1321646, by rfl⟩ : syracuseStep 1762195 = 2643293) B2643293
theorem B10838947 : Blo 694316 10838947 := bstep (se 1 (by rfl) ⟨8129210, by rfl⟩ : syracuseStep 10838947 = 16258421) B16258421
theorem B1172495 : Blo 694316 1172495 := bstep (se 1 (by rfl) ⟨879371, by rfl⟩ : syracuseStep 1172495 = 1758743) B1758743
theorem B1565711 : Blo 694316 1565711 := bstep (se 1 (by rfl) ⟨1174283, by rfl⟩ : syracuseStep 1565711 = 2348567) B2348567
theorem B1565729 : Blo 694316 1565729 := bstep (se 2 (by rfl) ⟨587148, by rfl⟩ : syracuseStep 1565729 = 1174297) B1174297
theorem B1762337 : Blo 694316 1762337 := bstep (se 2 (by rfl) ⟨660876, by rfl⟩ : syracuseStep 1762337 = 1321753) B1321753
theorem B1041527 : Blo 694316 1041527 := bstep (se 1 (by rfl) ⟨781145, by rfl⟩ : syracuseStep 1041527 = 1562291) B1562291
theorem B1041551 : Blo 694316 1041551 := bstep (se 1 (by rfl) ⟨781163, by rfl⟩ : syracuseStep 1041551 = 1562327) B1562327
theorem B1041593 : Blo 694316 1041593 := bstep (se 2 (by rfl) ⟨390597, by rfl⟩ : syracuseStep 1041593 = 781195) B781195
theorem B1041671 : Blo 694316 1041671 := bstep (se 1 (by rfl) ⟨781253, by rfl⟩ : syracuseStep 1041671 = 1562507) B1562507
theorem B1041707 : Blo 694316 1041707 := bstep (se 1 (by rfl) ⟨781280, by rfl⟩ : syracuseStep 1041707 = 1562561) B1562561
theorem B1041737 : Blo 694316 1041737 := bstep (se 2 (by rfl) ⟨390651, by rfl⟩ : syracuseStep 1041737 = 781303) B781303
theorem B3958105 : Blo 694316 3958105 := bstep (se 2 (by rfl) ⟨1484289, by rfl⟩ : syracuseStep 3958105 = 2968579) B2968579
theorem B1566071 : Blo 694316 1566071 := bstep (se 1 (by rfl) ⟨1174553, by rfl⟩ : syracuseStep 1566071 = 2349107) B2349107
theorem B1041851 : Blo 694316 1041851 := bstep (se 1 (by rfl) ⟨781388, by rfl⟩ : syracuseStep 1041851 = 1562777) B1562777
theorem B1041911 : Blo 694316 1041911 := bstep (se 1 (by rfl) ⟨781433, by rfl⟩ : syracuseStep 1041911 = 1562867) B1562867
theorem B1041935 : Blo 694316 1041935 := bstep (se 1 (by rfl) ⟨781451, by rfl⟩ : syracuseStep 1041935 = 1562903) B1562903
theorem B1173035 : Blo 694316 1173035 := bstep (se 1 (by rfl) ⟨879776, by rfl⟩ : syracuseStep 1173035 = 1759553) B1759553
theorem B1566251 : Blo 694316 1566251 := bstep (se 1 (by rfl) ⟨1174688, by rfl⟩ : syracuseStep 1566251 = 2349377) B2349377
theorem B1041977 : Blo 694316 1041977 := bstep (se 2 (by rfl) ⟨390741, by rfl⟩ : syracuseStep 1041977 = 781483) B781483
theorem B2418295 : Blo 694316 2418295 := bstep (se 1 (by rfl) ⟨1813721, by rfl⟩ : syracuseStep 2418295 = 3627443) B3627443
theorem B1042055 : Blo 694316 1042055 := bstep (se 1 (by rfl) ⟨781541, by rfl⟩ : syracuseStep 1042055 = 1563083) B1563083
theorem B1042091 : Blo 694316 1042091 := bstep (se 1 (by rfl) ⟨781568, by rfl⟩ : syracuseStep 1042091 = 1563137) B1563137
theorem B1042121 : Blo 694316 1042121 := bstep (se 2 (by rfl) ⟨390795, by rfl⟩ : syracuseStep 1042121 = 781591) B781591
theorem B1042235 : Blo 694316 1042235 := bstep (se 1 (by rfl) ⟨781676, by rfl⟩ : syracuseStep 1042235 = 1563353) B1563353
theorem B1042295 : Blo 694316 1042295 := bstep (se 1 (by rfl) ⟨781721, by rfl⟩ : syracuseStep 1042295 = 1563443) B1563443
theorem B1042319 : Blo 694316 1042319 := bstep (se 1 (by rfl) ⟨781739, by rfl⟩ : syracuseStep 1042319 = 1563479) B1563479
theorem B1566611 : Blo 694316 1566611 := bstep (se 1 (by rfl) ⟨1174958, by rfl⟩ : syracuseStep 1566611 = 2349917) B2349917
theorem B2353049 : Blo 694316 2353049 := bstep (se 2 (by rfl) ⟨882393, by rfl⟩ : syracuseStep 2353049 = 1764787) B1764787
theorem B1042361 : Blo 694316 1042361 := bstep (se 2 (by rfl) ⟨390885, by rfl⟩ : syracuseStep 1042361 = 781771) B781771
theorem B1173433 : Blo 694316 1173433 := bstep (se 2 (by rfl) ⟨440037, by rfl⟩ : syracuseStep 1173433 = 880075) B880075
theorem B1566665 : Blo 694316 1566665 := bstep (se 2 (by rfl) ⟨587499, by rfl⟩ : syracuseStep 1566665 = 1174999) B1174999
theorem B1763329 : Blo 694316 1763329 := bstep (se 2 (by rfl) ⟨661248, by rfl⟩ : syracuseStep 1763329 = 1322497) B1322497
theorem B1042439 : Blo 694316 1042439 := bstep (se 1 (by rfl) ⟨781829, by rfl⟩ : syracuseStep 1042439 = 1563659) B1563659
theorem B1042475 : Blo 694316 1042475 := bstep (se 1 (by rfl) ⟨781856, by rfl⟩ : syracuseStep 1042475 = 1563713) B1563713
theorem B1042505 : Blo 694316 1042505 := bstep (se 2 (by rfl) ⟨390939, by rfl⟩ : syracuseStep 1042505 = 781879) B781879
theorem B2386007 : Blo 694316 2386007 := bstep (se 1 (by rfl) ⟨1789505, by rfl⟩ : syracuseStep 2386007 = 3579011) B3579011
theorem B878779 : Blo 694316 878779 := bstep (se 1 (by rfl) ⟨659084, by rfl⟩ : syracuseStep 878779 = 1318169) B1318169
theorem B1042619 : Blo 694316 1042619 := bstep (se 1 (by rfl) ⟨781964, by rfl⟩ : syracuseStep 1042619 = 1563929) B1563929
theorem B1042679 : Blo 694316 1042679 := bstep (se 1 (by rfl) ⟨782009, by rfl⟩ : syracuseStep 1042679 = 1564019) B1564019
theorem B2648321 : Blo 694316 2648321 := bstep (se 2 (by rfl) ⟨993120, by rfl⟩ : syracuseStep 2648321 = 1986241) B1986241
theorem B3533057 : Blo 694316 3533057 := bstep (se 2 (by rfl) ⟨1324896, by rfl⟩ : syracuseStep 3533057 = 2649793) B2649793
theorem B1042703 : Blo 694316 1042703 := bstep (se 1 (by rfl) ⟨782027, by rfl⟩ : syracuseStep 1042703 = 1564055) B1564055
theorem B2648335 : Blo 694316 2648335 := bstep (se 1 (by rfl) ⟨1986251, by rfl⟩ : syracuseStep 2648335 = 3972503) B3972503
theorem B1042745 : Blo 694316 1042745 := bstep (se 2 (by rfl) ⟨391029, by rfl⟩ : syracuseStep 1042745 = 782059) B782059
theorem B1042823 : Blo 694316 1042823 := bstep (se 1 (by rfl) ⟨782117, by rfl⟩ : syracuseStep 1042823 = 1564235) B1564235
theorem B1042859 : Blo 694316 1042859 := bstep (se 1 (by rfl) ⟨782144, by rfl⟩ : syracuseStep 1042859 = 1564289) B1564289
theorem B1042889 : Blo 694316 1042889 := bstep (se 2 (by rfl) ⟨391083, by rfl⟩ : syracuseStep 1042889 = 782167) B782167
theorem B1043003 : Blo 694316 1043003 := bstep (se 1 (by rfl) ⟨782252, by rfl⟩ : syracuseStep 1043003 = 1564505) B1564505
theorem B1763927 : Blo 694316 1763927 := bstep (se 1 (by rfl) ⟨1322945, by rfl⟩ : syracuseStep 1763927 = 2645891) B2645891
theorem B2353751 : Blo 694316 2353751 := bstep (se 1 (by rfl) ⟨1765313, by rfl⟩ : syracuseStep 2353751 = 3530627) B3530627
theorem B1043063 : Blo 694316 1043063 := bstep (se 1 (by rfl) ⟨782297, by rfl⟩ : syracuseStep 1043063 = 1564595) B1564595
theorem B1174135 : Blo 694316 1174135 := bstep (se 1 (by rfl) ⟨880601, by rfl⟩ : syracuseStep 1174135 = 1761203) B1761203
theorem B1567367 : Blo 694316 1567367 := bstep (se 1 (by rfl) ⟨1175525, by rfl⟩ : syracuseStep 1567367 = 2351051) B2351051
theorem B1043087 : Blo 694316 1043087 := bstep (se 1 (by rfl) ⟨782315, by rfl⟩ : syracuseStep 1043087 = 1564631) B1564631
theorem B879275 : Blo 694316 879275 := bstep (se 1 (by rfl) ⟨659456, by rfl⟩ : syracuseStep 879275 = 1318913) B1318913
theorem B1043129 : Blo 694316 1043129 := bstep (se 2 (by rfl) ⟨391173, by rfl⟩ : syracuseStep 1043129 = 782347) B782347
theorem B1043207 : Blo 694316 1043207 := bstep (se 1 (by rfl) ⟨782405, by rfl⟩ : syracuseStep 1043207 = 1564811) B1564811
theorem B1043243 : Blo 694316 1043243 := bstep (se 1 (by rfl) ⟨782432, by rfl⟩ : syracuseStep 1043243 = 1564865) B1564865
theorem B1764139 : Blo 694316 1764139 := bstep (se 1 (by rfl) ⟨1323104, by rfl⟩ : syracuseStep 1764139 = 2646209) B2646209
theorem B1174331 : Blo 694316 1174331 := bstep (se 1 (by rfl) ⟨880748, by rfl⟩ : syracuseStep 1174331 = 1761497) B1761497
theorem B1567547 : Blo 694316 1567547 := bstep (se 1 (by rfl) ⟨1175660, by rfl⟩ : syracuseStep 1567547 = 2351321) B2351321
theorem B1043273 : Blo 694316 1043273 := bstep (se 2 (by rfl) ⟨391227, by rfl⟩ : syracuseStep 1043273 = 782455) B782455
theorem B1567673 : Blo 694316 1567673 := bstep (se 2 (by rfl) ⟨587877, by rfl⟩ : syracuseStep 1567673 = 1175755) B1175755
theorem B1764281 : Blo 694316 1764281 := bstep (se 2 (by rfl) ⟨661605, by rfl⟩ : syracuseStep 1764281 = 1323211) B1323211
theorem B1043387 : Blo 694316 1043387 := bstep (se 1 (by rfl) ⟨782540, by rfl⟩ : syracuseStep 1043387 = 1565081) B1565081
theorem B1043447 : Blo 694316 1043447 := bstep (se 1 (by rfl) ⟨782585, by rfl⟩ : syracuseStep 1043447 = 1565171) B1565171
theorem B1043471 : Blo 694316 1043471 := bstep (se 1 (by rfl) ⟨782603, by rfl⟩ : syracuseStep 1043471 = 1565207) B1565207
theorem B3959837 : Blo 694316 3959837 := bstep (se 3 (by rfl) ⟨742469, by rfl⟩ : syracuseStep 3959837 = 1484939) B1484939
theorem B3533867 : Blo 694316 3533867 := bstep (se 1 (by rfl) ⟨2650400, by rfl⟩ : syracuseStep 3533867 = 5300801) B5300801
theorem B1043513 : Blo 694316 1043513 := bstep (se 2 (by rfl) ⟨391317, by rfl⟩ : syracuseStep 1043513 = 782635) B782635
theorem B1305659 : Blo 694316 1305659 := bstep (se 1 (by rfl) ⟨979244, by rfl⟩ : syracuseStep 1305659 = 1958489) B1958489
theorem B2354237 : Blo 694316 2354237 := bstep (se 3 (by rfl) ⟨441419, by rfl⟩ : syracuseStep 2354237 = 882839) B882839
theorem B781447 : Blo 694316 781447 := bstep (se 1 (by rfl) ⟨586085, by rfl⟩ : syracuseStep 781447 = 1172171) B1172171
theorem B879751 : Blo 694316 879751 := bstep (se 1 (by rfl) ⟨659813, by rfl⟩ : syracuseStep 879751 = 1319627) B1319627
theorem B1043591 : Blo 694316 1043591 := bstep (se 1 (by rfl) ⟨782693, by rfl⟩ : syracuseStep 1043591 = 1565387) B1565387
theorem B1043627 : Blo 694316 1043627 := bstep (se 1 (by rfl) ⟨782720, by rfl⟩ : syracuseStep 1043627 = 1565441) B1565441
theorem B1043657 : Blo 694316 1043657 := bstep (se 2 (by rfl) ⟨391371, by rfl⟩ : syracuseStep 1043657 = 782743) B782743
theorem B1174729 : Blo 694316 1174729 := bstep (se 2 (by rfl) ⟨440523, by rfl⟩ : syracuseStep 1174729 = 881047) B881047
theorem B1568015 : Blo 694316 1568015 := bstep (se 1 (by rfl) ⟨1176011, by rfl⟩ : syracuseStep 1568015 = 2352023) B2352023
theorem B1568033 : Blo 694316 1568033 := bstep (se 2 (by rfl) ⟨588012, by rfl⟩ : syracuseStep 1568033 = 1176025) B1176025
theorem B3763493 : Blo 694316 3763493 := bstep (se 4 (by rfl) ⟨352827, by rfl⟩ : syracuseStep 3763493 = 705655) B705655
theorem B781627 : Blo 694316 781627 := bstep (se 1 (by rfl) ⟨586220, by rfl⟩ : syracuseStep 781627 = 1172441) B1172441
theorem B1043771 : Blo 694316 1043771 := bstep (se 1 (by rfl) ⟨782828, by rfl⟩ : syracuseStep 1043771 = 1565657) B1565657
theorem B1043831 : Blo 694316 1043831 := bstep (se 1 (by rfl) ⟨782873, by rfl⟩ : syracuseStep 1043831 = 1565747) B1565747
theorem B1043855 : Blo 694316 1043855 := bstep (se 1 (by rfl) ⟨782891, by rfl⟩ : syracuseStep 1043855 = 1565783) B1565783
theorem B1043897 : Blo 694316 1043897 := bstep (se 2 (by rfl) ⟨391461, by rfl⟩ : syracuseStep 1043897 = 782923) B782923
theorem B1043975 : Blo 694316 1043975 := bstep (se 1 (by rfl) ⟨782981, by rfl⟩ : syracuseStep 1043975 = 1565963) B1565963
theorem B2649611 : Blo 694316 2649611 := bstep (se 1 (by rfl) ⟨1987208, by rfl⟩ : syracuseStep 2649611 = 3974417) B3974417
theorem B1044011 : Blo 694316 1044011 := bstep (se 1 (by rfl) ⟨783008, by rfl⟩ : syracuseStep 1044011 = 1566017) B1566017
theorem B1044041 : Blo 694316 1044041 := bstep (se 2 (by rfl) ⟨391515, by rfl⟩ : syracuseStep 1044041 = 783031) B783031
theorem B880247 : Blo 694316 880247 := bstep (se 1 (by rfl) ⟨660185, by rfl⟩ : syracuseStep 880247 = 1320371) B1320371
theorem B1568375 : Blo 694316 1568375 := bstep (se 1 (by rfl) ⟨1176281, by rfl⟩ : syracuseStep 1568375 = 2352563) B2352563
theorem B1044155 : Blo 694316 1044155 := bstep (se 1 (by rfl) ⟨783116, by rfl⟩ : syracuseStep 1044155 = 1566233) B1566233
theorem B3960521 : Blo 694316 3960521 := bstep (se 2 (by rfl) ⟨1485195, by rfl⟩ : syracuseStep 3960521 = 2970391) B2970391
theorem B1044215 : Blo 694316 1044215 := bstep (se 1 (by rfl) ⟨783161, by rfl⟩ : syracuseStep 1044215 = 1566323) B1566323
theorem B782095 : Blo 694316 782095 := bstep (se 1 (by rfl) ⟨586571, by rfl⟩ : syracuseStep 782095 = 1173143) B1173143
theorem B880399 : Blo 694316 880399 := bstep (se 1 (by rfl) ⟨660299, by rfl⟩ : syracuseStep 880399 = 1320599) B1320599
theorem B1044239 : Blo 694316 1044239 := bstep (se 1 (by rfl) ⟨783179, by rfl⟩ : syracuseStep 1044239 = 1566359) B1566359
theorem B5959439 : Blo 694316 5959439 := bstep (se 1 (by rfl) ⟨4469579, by rfl⟩ : syracuseStep 5959439 = 8939159) B8939159
theorem B1568555 : Blo 694316 1568555 := bstep (se 1 (by rfl) ⟨1176416, by rfl⟩ : syracuseStep 1568555 = 2352833) B2352833
theorem B1044281 : Blo 694316 1044281 := bstep (se 2 (by rfl) ⟨391605, by rfl⟩ : syracuseStep 1044281 = 783211) B783211
theorem B1044359 : Blo 694316 1044359 := bstep (se 1 (by rfl) ⟨783269, by rfl⟩ : syracuseStep 1044359 = 1566539) B1566539
theorem B1175431 : Blo 694316 1175431 := bstep (se 1 (by rfl) ⟨881573, by rfl⟩ : syracuseStep 1175431 = 1763147) B1763147
theorem B1765273 : Blo 694316 1765273 := bstep (se 2 (by rfl) ⟨661977, by rfl⟩ : syracuseStep 1765273 = 1323955) B1323955
theorem B8056729 : Blo 694316 8056729 := bstep (se 2 (by rfl) ⟨3021273, by rfl⟩ : syracuseStep 8056729 = 6042547) B6042547
theorem B1044395 : Blo 694316 1044395 := bstep (se 1 (by rfl) ⟨783296, by rfl⟩ : syracuseStep 1044395 = 1566593) B1566593
theorem B880571 : Blo 694316 880571 := bstep (se 1 (by rfl) ⟨660428, by rfl⟩ : syracuseStep 880571 = 1320857) B1320857
theorem B1044425 : Blo 694316 1044425 := bstep (se 2 (by rfl) ⟨391659, by rfl⟩ : syracuseStep 1044425 = 783319) B783319
theorem B1044539 : Blo 694316 1044539 := bstep (se 1 (by rfl) ⟨783404, by rfl⟩ : syracuseStep 1044539 = 1566809) B1566809
theorem B1765435 : Blo 694316 1765435 := bstep (se 1 (by rfl) ⟨1324076, by rfl⟩ : syracuseStep 1765435 = 2648153) B2648153
theorem B1044599 : Blo 694316 1044599 := bstep (se 1 (by rfl) ⟨783449, by rfl⟩ : syracuseStep 1044599 = 1566899) B1566899
theorem B1044623 : Blo 694316 1044623 := bstep (se 1 (by rfl) ⟨783467, by rfl⟩ : syracuseStep 1044623 = 1566935) B1566935
theorem B1568915 : Blo 694316 1568915 := bstep (se 1 (by rfl) ⟨1176686, by rfl⟩ : syracuseStep 1568915 = 2353373) B2353373
theorem B1044665 : Blo 694316 1044665 := bstep (se 2 (by rfl) ⟨391749, by rfl⟩ : syracuseStep 1044665 = 783499) B783499
theorem B1568969 : Blo 694316 1568969 := bstep (se 2 (by rfl) ⟨588363, by rfl⟩ : syracuseStep 1568969 = 1176727) B1176727
theorem B1765577 : Blo 694316 1765577 := bstep (se 2 (by rfl) ⟨662091, by rfl⟩ : syracuseStep 1765577 = 1324183) B1324183
theorem B2224385 : Blo 694316 2224385 := bstep (se 2 (by rfl) ⟨834144, by rfl⟩ : syracuseStep 2224385 = 1668289) B1668289
theorem B782599 : Blo 694316 782599 := bstep (se 1 (by rfl) ⟨586949, by rfl⟩ : syracuseStep 782599 = 1173899) B1173899
theorem B1044743 : Blo 694316 1044743 := bstep (se 1 (by rfl) ⟨783557, by rfl⟩ : syracuseStep 1044743 = 1567115) B1567115
theorem B4452641 : Blo 694316 4452641 := bstep (se 2 (by rfl) ⟨1669740, by rfl⟩ : syracuseStep 4452641 = 3339481) B3339481
theorem B1044779 : Blo 694316 1044779 := bstep (se 1 (by rfl) ⟨783584, by rfl⟩ : syracuseStep 1044779 = 1567169) B1567169
theorem B3535163 : Blo 694316 3535163 := bstep (se 1 (by rfl) ⟨2651372, by rfl⟩ : syracuseStep 3535163 = 5302745) B5302745
theorem B1044809 : Blo 694316 1044809 := bstep (se 2 (by rfl) ⟨391803, by rfl⟩ : syracuseStep 1044809 = 783607) B783607
theorem B2355641 : Blo 694316 2355641 := bstep (se 2 (by rfl) ⟨883365, by rfl⟩ : syracuseStep 2355641 = 1766731) B1766731
theorem B2650553 : Blo 694316 2650553 := bstep (se 2 (by rfl) ⟨993957, by rfl⟩ : syracuseStep 2650553 = 1987915) B1987915
theorem B782779 : Blo 694316 782779 := bstep (se 1 (by rfl) ⟨587084, by rfl⟩ : syracuseStep 782779 = 1174169) B1174169
theorem B1044923 : Blo 694316 1044923 := bstep (se 1 (by rfl) ⟨783692, by rfl⟩ : syracuseStep 1044923 = 1567385) B1567385
theorem B1044983 : Blo 694316 1044983 := bstep (se 1 (by rfl) ⟨783737, by rfl⟩ : syracuseStep 1044983 = 1567475) B1567475
theorem B1045007 : Blo 694316 1045007 := bstep (se 1 (by rfl) ⟨783755, by rfl⟩ : syracuseStep 1045007 = 1567511) B1567511
theorem B1176079 : Blo 694316 1176079 := bstep (se 1 (by rfl) ⟨882059, by rfl⟩ : syracuseStep 1176079 = 1764119) B1764119
theorem B1765921 : Blo 694316 1765921 := bstep (se 2 (by rfl) ⟨662220, by rfl⟩ : syracuseStep 1765921 = 1324441) B1324441
theorem B1045049 : Blo 694316 1045049 := bstep (se 2 (by rfl) ⟨391893, by rfl⟩ : syracuseStep 1045049 = 783787) B783787
theorem B1045127 : Blo 694316 1045127 := bstep (se 1 (by rfl) ⟨783845, by rfl⟩ : syracuseStep 1045127 = 1567691) B1567691
theorem B1045163 : Blo 694316 1045163 := bstep (se 1 (by rfl) ⟨783872, by rfl⟩ : syracuseStep 1045163 = 1567745) B1567745
theorem B1045193 : Blo 694316 1045193 := bstep (se 2 (by rfl) ⟨391947, by rfl⟩ : syracuseStep 1045193 = 783895) B783895
theorem B1045307 : Blo 694316 1045307 := bstep (se 1 (by rfl) ⟨783980, by rfl⟩ : syracuseStep 1045307 = 1567961) B1567961
theorem B1045367 : Blo 694316 1045367 := bstep (se 1 (by rfl) ⟨784025, by rfl⟩ : syracuseStep 1045367 = 1568051) B1568051
theorem B881543 : Blo 694316 881543 := bstep (se 1 (by rfl) ⟨661157, by rfl⟩ : syracuseStep 881543 = 1322315) B1322315
theorem B1569671 : Blo 694316 1569671 := bstep (se 1 (by rfl) ⟨1177253, by rfl⟩ : syracuseStep 1569671 = 2354507) B2354507
theorem B783247 : Blo 694316 783247 := bstep (se 1 (by rfl) ⟨587435, by rfl⟩ : syracuseStep 783247 = 1174871) B1174871
theorem B1045391 : Blo 694316 1045391 := bstep (se 1 (by rfl) ⟨784043, by rfl⟩ : syracuseStep 1045391 = 1568087) B1568087
theorem B1340345 : Blo 694316 1340345 := bstep (se 2 (by rfl) ⟨502629, by rfl⟩ : syracuseStep 1340345 = 1005259) B1005259
theorem B1045433 : Blo 694316 1045433 := bstep (se 2 (by rfl) ⟨392037, by rfl⟩ : syracuseStep 1045433 = 784075) B784075
theorem B1045511 : Blo 694316 1045511 := bstep (se 1 (by rfl) ⟨784133, by rfl⟩ : syracuseStep 1045511 = 1568267) B1568267
theorem B2356235 : Blo 694316 2356235 := bstep (se 1 (by rfl) ⟨1767176, by rfl⟩ : syracuseStep 2356235 = 3534353) B3534353
theorem B1045547 : Blo 694316 1045547 := bstep (se 1 (by rfl) ⟨784160, by rfl⟩ : syracuseStep 1045547 = 1568321) B1568321
theorem B1176619 : Blo 694316 1176619 := bstep (se 1 (by rfl) ⟨882464, by rfl⟩ : syracuseStep 1176619 = 1764929) B1764929
theorem B1569851 : Blo 694316 1569851 := bstep (se 1 (by rfl) ⟨1177388, by rfl⟩ : syracuseStep 1569851 = 2354777) B2354777
theorem B1045577 : Blo 694316 1045577 := bstep (se 2 (by rfl) ⟨392091, by rfl⟩ : syracuseStep 1045577 = 784183) B784183
theorem B1766519 : Blo 694316 1766519 := bstep (se 1 (by rfl) ⟨1324889, by rfl⟩ : syracuseStep 1766519 = 2649779) B2649779
theorem B2356343 : Blo 694316 2356343 := bstep (se 1 (by rfl) ⟨1767257, by rfl⟩ : syracuseStep 2356343 = 3534515) B3534515
theorem B1176761 : Blo 694316 1176761 := bstep (se 2 (by rfl) ⟨441285, by rfl⟩ : syracuseStep 1176761 = 882571) B882571
theorem B1569977 : Blo 694316 1569977 := bstep (se 2 (by rfl) ⟨588741, by rfl⟩ : syracuseStep 1569977 = 1177483) B1177483
theorem B1045691 : Blo 694316 1045691 := bstep (se 1 (by rfl) ⟨784268, by rfl⟩ : syracuseStep 1045691 = 1568537) B1568537
theorem B1045751 : Blo 694316 1045751 := bstep (se 1 (by rfl) ⟨784313, by rfl⟩ : syracuseStep 1045751 = 1568627) B1568627
theorem B1045775 : Blo 694316 1045775 := bstep (se 1 (by rfl) ⟨784331, by rfl⟩ : syracuseStep 1045775 = 1568663) B1568663
theorem B1668385 : Blo 694316 1668385 := bstep (se 2 (by rfl) ⟨625644, by rfl⟩ : syracuseStep 1668385 = 1251289) B1251289
theorem B1045817 : Blo 694316 1045817 := bstep (se 2 (by rfl) ⟨392181, by rfl⟩ : syracuseStep 1045817 = 784363) B784363
theorem B783751 : Blo 694316 783751 := bstep (se 1 (by rfl) ⟨587813, by rfl⟩ : syracuseStep 783751 = 1175627) B1175627
theorem B1045895 : Blo 694316 1045895 := bstep (se 1 (by rfl) ⟨784421, by rfl⟩ : syracuseStep 1045895 = 1568843) B1568843
theorem B1045931 : Blo 694316 1045931 := bstep (se 1 (by rfl) ⟨784448, by rfl⟩ : syracuseStep 1045931 = 1568897) B1568897
theorem B3962297 : Blo 694316 3962297 := bstep (se 2 (by rfl) ⟨1485861, by rfl⟩ : syracuseStep 3962297 = 2971723) B2971723
theorem B1045961 : Blo 694316 1045961 := bstep (se 2 (by rfl) ⟨392235, by rfl⟩ : syracuseStep 1045961 = 784471) B784471
theorem B6780419 : Blo 694316 6780419 := bstep (se 1 (by rfl) ⟨5085314, by rfl⟩ : syracuseStep 6780419 = 10170629) B10170629
theorem B882191 : Blo 694316 882191 := bstep (se 1 (by rfl) ⟨661643, by rfl⟩ : syracuseStep 882191 = 1323287) B1323287
theorem B1570319 : Blo 694316 1570319 := bstep (se 1 (by rfl) ⟨1177739, by rfl⟩ : syracuseStep 1570319 = 2355479) B2355479
theorem B1570337 : Blo 694316 1570337 := bstep (se 2 (by rfl) ⟨588876, by rfl⟩ : syracuseStep 1570337 = 1177753) B1177753
theorem B783931 : Blo 694316 783931 := bstep (se 1 (by rfl) ⟨587948, by rfl⟩ : syracuseStep 783931 = 1175897) B1175897
theorem B1046075 : Blo 694316 1046075 := bstep (se 1 (by rfl) ⟨784556, by rfl⟩ : syracuseStep 1046075 = 1569113) B1569113
theorem B1046135 : Blo 694316 1046135 := bstep (se 1 (by rfl) ⟨784601, by rfl⟩ : syracuseStep 1046135 = 1569203) B1569203
theorem B1046159 : Blo 694316 1046159 := bstep (se 1 (by rfl) ⟨784619, by rfl⟩ : syracuseStep 1046159 = 1569239) B1569239
theorem B1046201 : Blo 694316 1046201 := bstep (se 2 (by rfl) ⟨392325, by rfl⟩ : syracuseStep 1046201 = 784651) B784651
theorem B1046279 : Blo 694316 1046279 := bstep (se 1 (by rfl) ⟨784709, by rfl⟩ : syracuseStep 1046279 = 1569419) B1569419
theorem B1046315 : Blo 694316 1046315 := bstep (se 1 (by rfl) ⟨784736, by rfl⟩ : syracuseStep 1046315 = 1569473) B1569473
theorem B1046345 : Blo 694316 1046345 := bstep (se 2 (by rfl) ⟨392379, by rfl⟩ : syracuseStep 1046345 = 784759) B784759
theorem B3766105 : Blo 694316 3766105 := bstep (se 2 (by rfl) ⟨1412289, by rfl⟩ : syracuseStep 3766105 = 2824579) B2824579
theorem B1177463 : Blo 694316 1177463 := bstep (se 1 (by rfl) ⟨883097, by rfl⟩ : syracuseStep 1177463 = 1766195) B1766195
theorem B1570679 : Blo 694316 1570679 := bstep (se 1 (by rfl) ⟨1178009, by rfl⟩ : syracuseStep 1570679 = 2356019) B2356019
theorem B3766151 : Blo 694316 3766151 := bstep (se 1 (by rfl) ⟨2824613, by rfl⟩ : syracuseStep 3766151 = 5649227) B5649227
theorem B1046459 : Blo 694316 1046459 := bstep (se 1 (by rfl) ⟨784844, by rfl⟩ : syracuseStep 1046459 = 1569689) B1569689
theorem B1046519 : Blo 694316 1046519 := bstep (se 1 (by rfl) ⟨784889, by rfl⟩ : syracuseStep 1046519 = 1569779) B1569779
theorem B784399 : Blo 694316 784399 := bstep (se 1 (by rfl) ⟨588299, by rfl⟩ : syracuseStep 784399 = 1176599) B1176599
theorem B1046543 : Blo 694316 1046543 := bstep (se 1 (by rfl) ⟨784907, by rfl⟩ : syracuseStep 1046543 = 1569815) B1569815
theorem B1570859 : Blo 694316 1570859 := bstep (se 1 (by rfl) ⟨1178144, by rfl⟩ : syracuseStep 1570859 = 2356289) B2356289
theorem B1046585 : Blo 694316 1046585 := bstep (se 2 (by rfl) ⟨392469, by rfl⟩ : syracuseStep 1046585 = 784939) B784939
theorem B1046663 : Blo 694316 1046663 := bstep (se 1 (by rfl) ⟨784997, by rfl⟩ : syracuseStep 1046663 = 1569995) B1569995
theorem B1046699 : Blo 694316 1046699 := bstep (se 1 (by rfl) ⟨785024, by rfl⟩ : syracuseStep 1046699 = 1570049) B1570049
theorem B1046729 : Blo 694316 1046729 := bstep (se 2 (by rfl) ⟨392523, by rfl⟩ : syracuseStep 1046729 = 785047) B785047
theorem B2980097 : Blo 694316 2980097 := bstep (se 2 (by rfl) ⟨1117536, by rfl⟩ : syracuseStep 2980097 = 2235073) B2235073
theorem B1046843 : Blo 694316 1046843 := bstep (se 1 (by rfl) ⟨785132, by rfl⟩ : syracuseStep 1046843 = 1570265) B1570265
theorem B1177915 : Blo 694316 1177915 := bstep (se 1 (by rfl) ⟨883436, by rfl⟩ : syracuseStep 1177915 = 1766873) B1766873
theorem B1046903 : Blo 694316 1046903 := bstep (se 1 (by rfl) ⟨785177, by rfl⟩ : syracuseStep 1046903 = 1570355) B1570355
theorem B1046927 : Blo 694316 1046927 := bstep (se 1 (by rfl) ⟨785195, by rfl⟩ : syracuseStep 1046927 = 1570391) B1570391
theorem B1046969 : Blo 694316 1046969 := bstep (se 2 (by rfl) ⟨392613, by rfl⟩ : syracuseStep 1046969 = 785227) B785227
theorem B1178057 : Blo 694316 1178057 := bstep (se 2 (by rfl) ⟨441771, by rfl⟩ : syracuseStep 1178057 = 883543) B883543
theorem B784903 : Blo 694316 784903 := bstep (se 1 (by rfl) ⟨588677, by rfl⟩ : syracuseStep 784903 = 1177355) B1177355
theorem B1047047 : Blo 694316 1047047 := bstep (se 1 (by rfl) ⟨785285, by rfl⟩ : syracuseStep 1047047 = 1570571) B1570571
theorem B1047083 : Blo 694316 1047083 := bstep (se 1 (by rfl) ⟨785312, by rfl⟩ : syracuseStep 1047083 = 1570625) B1570625
theorem B1047113 : Blo 694316 1047113 := bstep (se 2 (by rfl) ⟨392667, by rfl⟩ : syracuseStep 1047113 = 785335) B785335
theorem B2062967 : Blo 694316 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B2980471 : Blo 694316 2980471 := bstep (se 1 (by rfl) ⟨2235353, by rfl⟩ : syracuseStep 2980471 = 4470707) B4470707
theorem B785083 : Blo 694316 785083 := bstep (se 1 (by rfl) ⟨588812, by rfl⟩ : syracuseStep 785083 = 1177625) B1177625
theorem B1047227 : Blo 694316 1047227 := bstep (se 1 (by rfl) ⟨785420, by rfl⟩ : syracuseStep 1047227 = 1570841) B1570841
theorem B1047287 : Blo 694316 1047287 := bstep (se 1 (by rfl) ⟨785465, by rfl⟩ : syracuseStep 1047287 = 1570931) B1570931
theorem B1047311 : Blo 694316 1047311 := bstep (se 1 (by rfl) ⟨785483, by rfl⟩ : syracuseStep 1047311 = 1570967) B1570967
theorem B1047353 : Blo 694316 1047353 := bstep (se 2 (by rfl) ⟨392757, by rfl⟩ : syracuseStep 1047353 = 785515) B785515
theorem B1047431 : Blo 694316 1047431 := bstep (se 1 (by rfl) ⟨785573, by rfl⟩ : syracuseStep 1047431 = 1571147) B1571147
theorem B1047467 : Blo 694316 1047467 := bstep (se 1 (by rfl) ⟨785600, by rfl⟩ : syracuseStep 1047467 = 1571201) B1571201
theorem B2817053 : Blo 694316 2817053 := bstep (se 3 (by rfl) ⟨528197, by rfl⟩ : syracuseStep 2817053 = 1056395) B1056395
theorem B785551 : Blo 694316 785551 := bstep (se 1 (by rfl) ⟨589163, by rfl⟩ : syracuseStep 785551 = 1178327) B1178327
theorem B3964211 : Blo 694316 3964211 := bstep (se 1 (by rfl) ⟨2973158, by rfl⟩ : syracuseStep 3964211 = 5946317) B5946317
theorem B4455739 : Blo 694316 4455739 := bstep (se 1 (by rfl) ⟨3341804, by rfl⟩ : syracuseStep 4455739 = 6683609) B6683609
theorem B1670519 : Blo 694316 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B2817737 : Blo 694316 2817737 := bstep (se 2 (by rfl) ⟨1056651, by rfl⟩ : syracuseStep 2817737 = 2113303) B2113303
theorem B4226849 : Blo 694316 4226849 := bstep (se 2 (by rfl) ⟨1585068, by rfl⟩ : syracuseStep 4226849 = 3170137) B3170137
theorem B3342113 : Blo 694316 3342113 := bstep (se 2 (by rfl) ⟨1253292, by rfl⟩ : syracuseStep 3342113 = 2506585) B2506585
theorem B1670971 : Blo 694316 1670971 := bstep (se 1 (by rfl) ⟨1253228, by rfl⟩ : syracuseStep 1670971 = 2506457) B2506457
theorem B13369373 : Blo 694316 13369373 := bstep (se 3 (by rfl) ⟨2506757, by rfl⟩ : syracuseStep 13369373 = 5013515) B5013515
theorem B3342653 : Blo 694316 3342653 := bstep (se 3 (by rfl) ⟨626747, by rfl⟩ : syracuseStep 3342653 = 1253495) B1253495
theorem B9503405 : Blo 694316 9503405 := bstep (se 3 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 9503405 = 3563777) B3563777
theorem B1115063 : Blo 694316 1115063 := bstep (se 1 (by rfl) ⟨836297, by rfl⟩ : syracuseStep 1115063 = 1672595) B1672595
theorem B14451929 : Blo 694316 14451929 := bstep (se 2 (by rfl) ⟨5419473, by rfl⟩ : syracuseStep 14451929 = 10838947) B10838947
theorem B1410295 : Blo 694316 1410295 := bstep (se 1 (by rfl) ⟨1057721, by rfl⟩ : syracuseStep 1410295 = 2115443) B2115443
theorem B10061171 : Blo 694316 10061171 := bstep (se 1 (by rfl) ⟨7545878, by rfl⟩ : syracuseStep 10061171 = 15091757) B15091757
theorem B1115575 : Blo 694316 1115575 := bstep (se 1 (by rfl) ⟨836681, by rfl⟩ : syracuseStep 1115575 = 1673363) B1673363
theorem B5277473 : Blo 694316 5277473 := bstep (se 2 (by rfl) ⟨1979052, by rfl⟩ : syracuseStep 5277473 = 3958105) B3958105
theorem B952159 : Blo 694316 952159 := bstep (se 1 (by rfl) ⟨714119, by rfl⟩ : syracuseStep 952159 = 1428239) B1428239
theorem B3868729 : Blo 694316 3868729 := bstep (se 2 (by rfl) ⟨1450773, by rfl⟩ : syracuseStep 3868729 = 2901547) B2901547
theorem B1411511 : Blo 694316 1411511 := bstep (se 1 (by rfl) ⟨1058633, by rfl⟩ : syracuseStep 1411511 = 2117267) B2117267
theorem B3574253 : Blo 694316 3574253 := bstep (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) B1340345
theorem B2230843 : Blo 694316 2230843 := bstep (se 1 (by rfl) ⟨1673132, by rfl⟩ : syracuseStep 2230843 = 3346265) B3346265
theorem B2230973 : Blo 694316 2230973 := bstep (se 3 (by rfl) ⟨418307, by rfl⟩ : syracuseStep 2230973 = 836615) B836615
theorem B3018227 : Blo 694316 3018227 := bstep (se 1 (by rfl) ⟨2263670, by rfl⟩ : syracuseStep 3018227 = 4527341) B4527341
theorem B1412615 : Blo 694316 1412615 := bstep (se 1 (by rfl) ⟨1059461, by rfl⟩ : syracuseStep 1412615 = 2118923) B2118923
theorem B3575335 : Blo 694316 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B2821841 : Blo 694316 2821841 := bstep (se 2 (by rfl) ⟨1058190, by rfl⟩ : syracuseStep 2821841 = 2116381) B2116381
theorem B1118215 : Blo 694316 1118215 := bstep (se 1 (by rfl) ⟨838661, by rfl⟩ : syracuseStep 1118215 = 1677323) B1677323
theorem B11309219 : Blo 694316 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B6689303 : Blo 694316 6689303 := bstep (se 1 (by rfl) ⟨5016977, by rfl⟩ : syracuseStep 6689303 = 10033955) B10033955
theorem B3970295 : Blo 694316 3970295 := bstep (se 1 (by rfl) ⟨2977721, by rfl⟩ : syracuseStep 3970295 = 5955443) B5955443
theorem B989111 : Blo 694316 989111 := bstep (se 1 (by rfl) ⟨741833, by rfl⟩ : syracuseStep 989111 = 1483667) B1483667
theorem B694351 : Blo 694316 694351 := bstep (se 1 (by rfl) ⟨520763, by rfl⟩ : syracuseStep 694351 = 1041527) B1041527
theorem B694367 : Blo 694316 694367 := bstep (se 1 (by rfl) ⟨520775, by rfl⟩ : syracuseStep 694367 = 1041551) B1041551
theorem B694395 : Blo 694316 694395 := bstep (se 1 (by rfl) ⟨520796, by rfl⟩ : syracuseStep 694395 = 1041593) B1041593
theorem B694447 : Blo 694316 694447 := bstep (se 1 (by rfl) ⟨520835, by rfl⟩ : syracuseStep 694447 = 1041671) B1041671
theorem B694471 : Blo 694316 694471 := bstep (se 1 (by rfl) ⟨520853, by rfl⟩ : syracuseStep 694471 = 1041707) B1041707
theorem B694491 : Blo 694316 694491 := bstep (se 1 (by rfl) ⟨520868, by rfl⟩ : syracuseStep 694491 = 1041737) B1041737
theorem B18290929 : Blo 694316 18290929 := bstep (se 2 (by rfl) ⟨6859098, by rfl⟩ : syracuseStep 18290929 = 13718197) B13718197
theorem B694567 : Blo 694316 694567 := bstep (se 1 (by rfl) ⟨520925, by rfl⟩ : syracuseStep 694567 = 1041851) B1041851
theorem B694607 : Blo 694316 694607 := bstep (se 1 (by rfl) ⟨520955, by rfl⟩ : syracuseStep 694607 = 1041911) B1041911
theorem B694623 : Blo 694316 694623 := bstep (se 1 (by rfl) ⟨520967, by rfl⟩ : syracuseStep 694623 = 1041935) B1041935
theorem B694651 : Blo 694316 694651 := bstep (se 1 (by rfl) ⟨520988, by rfl⟩ : syracuseStep 694651 = 1041977) B1041977
theorem B694703 : Blo 694316 694703 := bstep (se 1 (by rfl) ⟨521027, by rfl⟩ : syracuseStep 694703 = 1042055) B1042055
theorem B694727 : Blo 694316 694727 := bstep (se 1 (by rfl) ⟨521045, by rfl⟩ : syracuseStep 694727 = 1042091) B1042091
theorem B694747 : Blo 694316 694747 := bstep (se 1 (by rfl) ⟨521060, by rfl⟩ : syracuseStep 694747 = 1042121) B1042121
theorem B694823 : Blo 694316 694823 := bstep (se 1 (by rfl) ⟨521117, by rfl⟩ : syracuseStep 694823 = 1042235) B1042235
theorem B694863 : Blo 694316 694863 := bstep (se 1 (by rfl) ⟨521147, by rfl⟩ : syracuseStep 694863 = 1042295) B1042295
theorem B694879 : Blo 694316 694879 := bstep (se 1 (by rfl) ⟨521159, by rfl⟩ : syracuseStep 694879 = 1042319) B1042319
theorem B694907 : Blo 694316 694907 := bstep (se 1 (by rfl) ⟨521180, by rfl⟩ : syracuseStep 694907 = 1042361) B1042361
theorem B694959 : Blo 694316 694959 := bstep (se 1 (by rfl) ⟨521219, by rfl⟩ : syracuseStep 694959 = 1042439) B1042439
theorem B694983 : Blo 694316 694983 := bstep (se 1 (by rfl) ⟨521237, by rfl⟩ : syracuseStep 694983 = 1042475) B1042475
theorem B695003 : Blo 694316 695003 := bstep (se 1 (by rfl) ⟨521252, by rfl⟩ : syracuseStep 695003 = 1042505) B1042505
theorem B695079 : Blo 694316 695079 := bstep (se 1 (by rfl) ⟨521309, by rfl⟩ : syracuseStep 695079 = 1042619) B1042619
theorem B695119 : Blo 694316 695119 := bstep (se 1 (by rfl) ⟨521339, by rfl⟩ : syracuseStep 695119 = 1042679) B1042679
theorem B17832797 : Blo 694316 17832797 := bstep (se 3 (by rfl) ⟨3343649, by rfl⟩ : syracuseStep 17832797 = 6687299) B6687299
theorem B695135 : Blo 694316 695135 := bstep (se 1 (by rfl) ⟨521351, by rfl⟩ : syracuseStep 695135 = 1042703) B1042703
theorem B695163 : Blo 694316 695163 := bstep (se 1 (by rfl) ⟨521372, by rfl⟩ : syracuseStep 695163 = 1042745) B1042745
theorem B11279249 : Blo 694316 11279249 := bstep (se 2 (by rfl) ⟨4229718, by rfl⟩ : syracuseStep 11279249 = 8459437) B8459437
theorem B695215 : Blo 694316 695215 := bstep (se 1 (by rfl) ⟨521411, by rfl⟩ : syracuseStep 695215 = 1042823) B1042823
theorem B695239 : Blo 694316 695239 := bstep (se 1 (by rfl) ⟨521429, by rfl⟩ : syracuseStep 695239 = 1042859) B1042859
theorem B695259 : Blo 694316 695259 := bstep (se 1 (by rfl) ⟨521444, by rfl⟩ : syracuseStep 695259 = 1042889) B1042889
theorem B695335 : Blo 694316 695335 := bstep (se 1 (by rfl) ⟨521501, by rfl⟩ : syracuseStep 695335 = 1043003) B1043003
theorem B695375 : Blo 694316 695375 := bstep (se 1 (by rfl) ⟨521531, by rfl⟩ : syracuseStep 695375 = 1043063) B1043063
theorem B695391 : Blo 694316 695391 := bstep (se 1 (by rfl) ⟨521543, by rfl⟩ : syracuseStep 695391 = 1043087) B1043087
theorem B695419 : Blo 694316 695419 := bstep (se 1 (by rfl) ⟨521564, by rfl⟩ : syracuseStep 695419 = 1043129) B1043129
theorem B695471 : Blo 694316 695471 := bstep (se 1 (by rfl) ⟨521603, by rfl⟩ : syracuseStep 695471 = 1043207) B1043207
theorem B695495 : Blo 694316 695495 := bstep (se 1 (by rfl) ⟨521621, by rfl⟩ : syracuseStep 695495 = 1043243) B1043243
theorem B695515 : Blo 694316 695515 := bstep (se 1 (by rfl) ⟨521636, by rfl⟩ : syracuseStep 695515 = 1043273) B1043273
theorem B1252601 : Blo 694316 1252601 := bstep (se 2 (by rfl) ⟨469725, by rfl⟩ : syracuseStep 1252601 = 939451) B939451
theorem B695591 : Blo 694316 695591 := bstep (se 1 (by rfl) ⟨521693, by rfl⟩ : syracuseStep 695591 = 1043387) B1043387
theorem B695631 : Blo 694316 695631 := bstep (se 1 (by rfl) ⟨521723, by rfl⟩ : syracuseStep 695631 = 1043447) B1043447
theorem B695647 : Blo 694316 695647 := bstep (se 1 (by rfl) ⟨521735, by rfl⟩ : syracuseStep 695647 = 1043471) B1043471
theorem B990569 : Blo 694316 990569 := bstep (se 2 (by rfl) ⟨371463, by rfl⟩ : syracuseStep 990569 = 742927) B742927
theorem B695675 : Blo 694316 695675 := bstep (se 1 (by rfl) ⟨521756, by rfl⟩ : syracuseStep 695675 = 1043513) B1043513
theorem B695727 : Blo 694316 695727 := bstep (se 1 (by rfl) ⟨521795, by rfl⟩ : syracuseStep 695727 = 1043591) B1043591
theorem B695751 : Blo 694316 695751 := bstep (se 1 (by rfl) ⟨521813, by rfl⟩ : syracuseStep 695751 = 1043627) B1043627
theorem B695771 : Blo 694316 695771 := bstep (se 1 (by rfl) ⟨521828, by rfl⟩ : syracuseStep 695771 = 1043657) B1043657
theorem B695847 : Blo 694316 695847 := bstep (se 1 (by rfl) ⟨521885, by rfl⟩ : syracuseStep 695847 = 1043771) B1043771
theorem B1318457 : Blo 694316 1318457 := bstep (se 2 (by rfl) ⟨494421, by rfl⟩ : syracuseStep 1318457 = 988843) B988843
theorem B695887 : Blo 694316 695887 := bstep (se 1 (by rfl) ⟨521915, by rfl⟩ : syracuseStep 695887 = 1043831) B1043831
theorem B695903 : Blo 694316 695903 := bstep (se 1 (by rfl) ⟨521927, by rfl⟩ : syracuseStep 695903 = 1043855) B1043855
theorem B695931 : Blo 694316 695931 := bstep (se 1 (by rfl) ⟨521948, by rfl⟩ : syracuseStep 695931 = 1043897) B1043897
theorem B695983 : Blo 694316 695983 := bstep (se 1 (by rfl) ⟨521987, by rfl⟩ : syracuseStep 695983 = 1043975) B1043975
theorem B1253063 : Blo 694316 1253063 := bstep (se 1 (by rfl) ⟨939797, by rfl⟩ : syracuseStep 1253063 = 1879595) B1879595
theorem B696007 : Blo 694316 696007 := bstep (se 1 (by rfl) ⟨522005, by rfl⟩ : syracuseStep 696007 = 1044011) B1044011
theorem B696027 : Blo 694316 696027 := bstep (se 1 (by rfl) ⟨522020, by rfl⟩ : syracuseStep 696027 = 1044041) B1044041
theorem B5021473 : Blo 694316 5021473 := bstep (se 2 (by rfl) ⟨1883052, by rfl⟩ : syracuseStep 5021473 = 3766105) B3766105
theorem B696103 : Blo 694316 696103 := bstep (se 1 (by rfl) ⟨522077, by rfl⟩ : syracuseStep 696103 = 1044155) B1044155
theorem B696143 : Blo 694316 696143 := bstep (se 1 (by rfl) ⟨522107, by rfl⟩ : syracuseStep 696143 = 1044215) B1044215
theorem B696159 : Blo 694316 696159 := bstep (se 1 (by rfl) ⟨522119, by rfl⟩ : syracuseStep 696159 = 1044239) B1044239
theorem B3972959 : Blo 694316 3972959 := bstep (se 1 (by rfl) ⟨2979719, by rfl⟩ : syracuseStep 3972959 = 5959439) B5959439
theorem B696187 : Blo 694316 696187 := bstep (se 1 (by rfl) ⟨522140, by rfl⟩ : syracuseStep 696187 = 1044281) B1044281
theorem B696239 : Blo 694316 696239 := bstep (se 1 (by rfl) ⟨522179, by rfl⟩ : syracuseStep 696239 = 1044359) B1044359
theorem B696263 : Blo 694316 696263 := bstep (se 1 (by rfl) ⟨522197, by rfl⟩ : syracuseStep 696263 = 1044395) B1044395
theorem B696283 : Blo 694316 696283 := bstep (se 1 (by rfl) ⟨522212, by rfl⟩ : syracuseStep 696283 = 1044425) B1044425
theorem B696359 : Blo 694316 696359 := bstep (se 1 (by rfl) ⟨522269, by rfl⟩ : syracuseStep 696359 = 1044539) B1044539
theorem B696399 : Blo 694316 696399 := bstep (se 1 (by rfl) ⟨522299, by rfl⟩ : syracuseStep 696399 = 1044599) B1044599
theorem B696415 : Blo 694316 696415 := bstep (se 1 (by rfl) ⟨522311, by rfl⟩ : syracuseStep 696415 = 1044623) B1044623
theorem B696443 : Blo 694316 696443 := bstep (se 1 (by rfl) ⟨522332, by rfl⟩ : syracuseStep 696443 = 1044665) B1044665
theorem B1482923 : Blo 694316 1482923 := bstep (se 1 (by rfl) ⟨1112192, by rfl⟩ : syracuseStep 1482923 = 2224385) B2224385
theorem B696495 : Blo 694316 696495 := bstep (se 1 (by rfl) ⟨522371, by rfl⟩ : syracuseStep 696495 = 1044743) B1044743
theorem B696519 : Blo 694316 696519 := bstep (se 1 (by rfl) ⟨522389, by rfl⟩ : syracuseStep 696519 = 1044779) B1044779
theorem B696539 : Blo 694316 696539 := bstep (se 1 (by rfl) ⟨522404, by rfl⟩ : syracuseStep 696539 = 1044809) B1044809
theorem B696615 : Blo 694316 696615 := bstep (se 1 (by rfl) ⟨522461, by rfl⟩ : syracuseStep 696615 = 1044923) B1044923
theorem B696655 : Blo 694316 696655 := bstep (se 1 (by rfl) ⟨522491, by rfl⟩ : syracuseStep 696655 = 1044983) B1044983
theorem B696671 : Blo 694316 696671 := bstep (se 1 (by rfl) ⟨522503, by rfl⟩ : syracuseStep 696671 = 1045007) B1045007
theorem B696699 : Blo 694316 696699 := bstep (se 1 (by rfl) ⟨522524, by rfl⟩ : syracuseStep 696699 = 1045049) B1045049
theorem B696751 : Blo 694316 696751 := bstep (se 1 (by rfl) ⟨522563, by rfl⟩ : syracuseStep 696751 = 1045127) B1045127
theorem B696775 : Blo 694316 696775 := bstep (se 1 (by rfl) ⟨522581, by rfl⟩ : syracuseStep 696775 = 1045163) B1045163
theorem B696795 : Blo 694316 696795 := bstep (se 1 (by rfl) ⟨522596, by rfl⟩ : syracuseStep 696795 = 1045193) B1045193
theorem B2236891 : Blo 694316 2236891 := bstep (se 1 (by rfl) ⟨1677668, by rfl⟩ : syracuseStep 2236891 = 3355337) B3355337
theorem B1253927 : Blo 694316 1253927 := bstep (se 1 (by rfl) ⟨940445, by rfl⟩ : syracuseStep 1253927 = 1880891) B1880891
theorem B696871 : Blo 694316 696871 := bstep (se 1 (by rfl) ⟨522653, by rfl⟩ : syracuseStep 696871 = 1045307) B1045307
theorem B696911 : Blo 694316 696911 := bstep (se 1 (by rfl) ⟨522683, by rfl⟩ : syracuseStep 696911 = 1045367) B1045367
theorem B696927 : Blo 694316 696927 := bstep (se 1 (by rfl) ⟨522695, by rfl⟩ : syracuseStep 696927 = 1045391) B1045391
theorem B696955 : Blo 694316 696955 := bstep (se 1 (by rfl) ⟨522716, by rfl⟩ : syracuseStep 696955 = 1045433) B1045433
theorem B697007 : Blo 694316 697007 := bstep (se 1 (by rfl) ⟨522755, by rfl⟩ : syracuseStep 697007 = 1045511) B1045511
theorem B697031 : Blo 694316 697031 := bstep (se 1 (by rfl) ⟨522773, by rfl⟩ : syracuseStep 697031 = 1045547) B1045547
theorem B697051 : Blo 694316 697051 := bstep (se 1 (by rfl) ⟨522788, by rfl⟩ : syracuseStep 697051 = 1045577) B1045577
theorem B697127 : Blo 694316 697127 := bstep (se 1 (by rfl) ⟨522845, by rfl⟩ : syracuseStep 697127 = 1045691) B1045691
theorem B3973961 : Blo 694316 3973961 := bstep (se 2 (by rfl) ⟨1490235, by rfl⟩ : syracuseStep 3973961 = 2980471) B2980471
theorem B697167 : Blo 694316 697167 := bstep (se 1 (by rfl) ⟨522875, by rfl⟩ : syracuseStep 697167 = 1045751) B1045751
theorem B697183 : Blo 694316 697183 := bstep (se 1 (by rfl) ⟨522887, by rfl⟩ : syracuseStep 697183 = 1045775) B1045775
theorem B697211 : Blo 694316 697211 := bstep (se 1 (by rfl) ⟨522908, by rfl⟩ : syracuseStep 697211 = 1045817) B1045817
theorem B697263 : Blo 694316 697263 := bstep (se 1 (by rfl) ⟨522947, by rfl⟩ : syracuseStep 697263 = 1045895) B1045895
theorem B697287 : Blo 694316 697287 := bstep (se 1 (by rfl) ⟨522965, by rfl⟩ : syracuseStep 697287 = 1045931) B1045931
theorem B697307 : Blo 694316 697307 := bstep (se 1 (by rfl) ⟨522980, by rfl⟩ : syracuseStep 697307 = 1045961) B1045961
theorem B697383 : Blo 694316 697383 := bstep (se 1 (by rfl) ⟨523037, by rfl⟩ : syracuseStep 697383 = 1046075) B1046075
theorem B697423 : Blo 694316 697423 := bstep (se 1 (by rfl) ⟨523067, by rfl⟩ : syracuseStep 697423 = 1046135) B1046135
theorem B697439 : Blo 694316 697439 := bstep (se 1 (by rfl) ⟨523079, by rfl⟩ : syracuseStep 697439 = 1046159) B1046159
theorem B697467 : Blo 694316 697467 := bstep (se 1 (by rfl) ⟨523100, by rfl⟩ : syracuseStep 697467 = 1046201) B1046201
theorem B697519 : Blo 694316 697519 := bstep (se 1 (by rfl) ⟨523139, by rfl⟩ : syracuseStep 697519 = 1046279) B1046279
theorem B697543 : Blo 694316 697543 := bstep (se 1 (by rfl) ⟨523157, by rfl⟩ : syracuseStep 697543 = 1046315) B1046315
theorem B697563 : Blo 694316 697563 := bstep (se 1 (by rfl) ⟨523172, by rfl⟩ : syracuseStep 697563 = 1046345) B1046345
theorem B697639 : Blo 694316 697639 := bstep (se 1 (by rfl) ⟨523229, by rfl⟩ : syracuseStep 697639 = 1046459) B1046459
theorem B697679 : Blo 694316 697679 := bstep (se 1 (by rfl) ⟨523259, by rfl⟩ : syracuseStep 697679 = 1046519) B1046519
theorem B697695 : Blo 694316 697695 := bstep (se 1 (by rfl) ⟨523271, by rfl⟩ : syracuseStep 697695 = 1046543) B1046543
theorem B697723 : Blo 694316 697723 := bstep (se 1 (by rfl) ⟨523292, by rfl⟩ : syracuseStep 697723 = 1046585) B1046585
theorem B697775 : Blo 694316 697775 := bstep (se 1 (by rfl) ⟨523331, by rfl⟩ : syracuseStep 697775 = 1046663) B1046663
theorem B697799 : Blo 694316 697799 := bstep (se 1 (by rfl) ⟨523349, by rfl⟩ : syracuseStep 697799 = 1046699) B1046699
theorem B697819 : Blo 694316 697819 := bstep (se 1 (by rfl) ⟨523364, by rfl⟩ : syracuseStep 697819 = 1046729) B1046729
theorem B1320455 : Blo 694316 1320455 := bstep (se 1 (by rfl) ⟨990341, by rfl⟩ : syracuseStep 1320455 = 1980683) B1980683
theorem B697895 : Blo 694316 697895 := bstep (se 1 (by rfl) ⟨523421, by rfl⟩ : syracuseStep 697895 = 1046843) B1046843
theorem B697935 : Blo 694316 697935 := bstep (se 1 (by rfl) ⟨523451, by rfl⟩ : syracuseStep 697935 = 1046903) B1046903
theorem B697951 : Blo 694316 697951 := bstep (se 1 (by rfl) ⟨523463, by rfl⟩ : syracuseStep 697951 = 1046927) B1046927
theorem B4466299 : Blo 694316 4466299 := bstep (se 1 (by rfl) ⟨3349724, by rfl⟩ : syracuseStep 4466299 = 6699449) B6699449
theorem B697979 : Blo 694316 697979 := bstep (se 1 (by rfl) ⟨523484, by rfl⟩ : syracuseStep 697979 = 1046969) B1046969
theorem B698031 : Blo 694316 698031 := bstep (se 1 (by rfl) ⟨523523, by rfl⟩ : syracuseStep 698031 = 1047047) B1047047
theorem B698055 : Blo 694316 698055 := bstep (se 1 (by rfl) ⟨523541, by rfl⟩ : syracuseStep 698055 = 1047083) B1047083
theorem B698075 : Blo 694316 698075 := bstep (se 1 (by rfl) ⟨523556, by rfl⟩ : syracuseStep 698075 = 1047113) B1047113
theorem B5940985 : Blo 694316 5940985 := bstep (se 2 (by rfl) ⟨2227869, by rfl⟩ : syracuseStep 5940985 = 4455739) B4455739
theorem B6694649 : Blo 694316 6694649 := bstep (se 2 (by rfl) ⟨2510493, by rfl⟩ : syracuseStep 6694649 = 5020987) B5020987
theorem B698151 : Blo 694316 698151 := bstep (se 1 (by rfl) ⟨523613, by rfl⟩ : syracuseStep 698151 = 1047227) B1047227
theorem B698191 : Blo 694316 698191 := bstep (se 1 (by rfl) ⟨523643, by rfl⟩ : syracuseStep 698191 = 1047287) B1047287
theorem B698207 : Blo 694316 698207 := bstep (se 1 (by rfl) ⟨523655, by rfl⟩ : syracuseStep 698207 = 1047311) B1047311
theorem B698235 : Blo 694316 698235 := bstep (se 1 (by rfl) ⟨523676, by rfl⟩ : syracuseStep 698235 = 1047353) B1047353
theorem B698287 : Blo 694316 698287 := bstep (se 1 (by rfl) ⟨523715, by rfl⟩ : syracuseStep 698287 = 1047431) B1047431
theorem B1320887 : Blo 694316 1320887 := bstep (se 1 (by rfl) ⟨990665, by rfl⟩ : syracuseStep 1320887 = 1981331) B1981331
theorem B698311 : Blo 694316 698311 := bstep (se 1 (by rfl) ⟨523733, by rfl⟩ : syracuseStep 698311 = 1047467) B1047467
theorem B1878035 : Blo 694316 1878035 := bstep (se 1 (by rfl) ⟨1408526, by rfl⟩ : syracuseStep 1878035 = 2817053) B2817053
theorem B5351453 : Blo 694316 5351453 := bstep (se 3 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 5351453 = 2006795) B2006795
theorem B1321039 : Blo 694316 1321039 := bstep (se 1 (by rfl) ⟨990779, by rfl⟩ : syracuseStep 1321039 = 1981559) B1981559
theorem B2828459 : Blo 694316 2828459 := bstep (se 1 (by rfl) ⟨2121344, by rfl⟩ : syracuseStep 2828459 = 4242689) B4242689
theorem B1190087 : Blo 694316 1190087 := bstep (se 1 (by rfl) ⟨892565, by rfl⟩ : syracuseStep 1190087 = 1785131) B1785131
theorem B1878491 : Blo 694316 1878491 := bstep (se 1 (by rfl) ⟨1408868, by rfl⟩ : syracuseStep 1878491 = 2817737) B2817737
theorem B7514909 : Blo 694316 7514909 := bstep (se 3 (by rfl) ⟨1409045, by rfl⟩ : syracuseStep 7514909 = 2818091) B2818091
theorem B3058505 : Blo 694316 3058505 := bstep (se 2 (by rfl) ⟨1146939, by rfl⟩ : syracuseStep 3058505 = 2293879) B2293879
theorem B2010017 : Blo 694316 2010017 := bstep (se 2 (by rfl) ⟨753756, by rfl⟩ : syracuseStep 2010017 = 1507513) B1507513
theorem B4467631 : Blo 694316 4467631 := bstep (se 1 (by rfl) ⟨3350723, by rfl⟩ : syracuseStep 4467631 = 6701447) B6701447
theorem B994231 : Blo 694316 994231 := bstep (se 1 (by rfl) ⟨745673, by rfl⟩ : syracuseStep 994231 = 1491347) B1491347
theorem B20065589 : Blo 694316 20065589 := bstep (se 5 (by rfl) ⟨940574, by rfl⟩ : syracuseStep 20065589 = 1881149) B1881149
theorem B1322345 : Blo 694316 1322345 := bstep (se 2 (by rfl) ⟨495879, by rfl⟩ : syracuseStep 1322345 = 991759) B991759
theorem B7613939 : Blo 694316 7613939 := bstep (se 1 (by rfl) ⟨5710454, by rfl⟩ : syracuseStep 7613939 = 11420909) B11420909
theorem B3517991 : Blo 694316 3517991 := bstep (se 1 (by rfl) ⟨2638493, by rfl⟩ : syracuseStep 3517991 = 5276987) B5276987
theorem B3387329 : Blo 694316 3387329 := bstep (se 2 (by rfl) ⟨1270248, by rfl⟩ : syracuseStep 3387329 = 2540497) B2540497
theorem B2830355 : Blo 694316 2830355 := bstep (se 1 (by rfl) ⟨2122766, by rfl⟩ : syracuseStep 2830355 = 4245533) B4245533
theorem B6696989 : Blo 694316 6696989 := bstep (se 3 (by rfl) ⟨1255685, by rfl⟩ : syracuseStep 6696989 = 2511371) B2511371
theorem B4239449 : Blo 694316 4239449 := bstep (se 2 (by rfl) ⟨1589793, by rfl⟩ : syracuseStep 4239449 = 3179587) B3179587
theorem B2502809 : Blo 694316 2502809 := bstep (se 2 (by rfl) ⟨938553, by rfl⟩ : syracuseStep 2502809 = 1877107) B1877107
theorem B5288165 : Blo 694316 5288165 := bstep (se 4 (by rfl) ⟨495765, by rfl⟩ : syracuseStep 5288165 = 991531) B991531
theorem B1323371 : Blo 694316 1323371 := bstep (se 1 (by rfl) ⟨992528, by rfl⟩ : syracuseStep 1323371 = 1985057) B1985057
theorem B18133465 : Blo 694316 18133465 := bstep (se 2 (by rfl) ⟨6800049, by rfl⟩ : syracuseStep 18133465 = 13600099) B13600099
theorem B3224393 : Blo 694316 3224393 := bstep (se 2 (by rfl) ⟨1209147, by rfl⟩ : syracuseStep 3224393 = 2418295) B2418295
theorem B1192799 : Blo 694316 1192799 := bstep (se 1 (by rfl) ⟨894599, by rfl⟩ : syracuseStep 1192799 = 1789199) B1789199
theorem B1324039 : Blo 694316 1324039 := bstep (se 1 (by rfl) ⟨993029, by rfl⟩ : syracuseStep 1324039 = 1986059) B1986059
theorem B3520097 : Blo 694316 3520097 := bstep (se 2 (by rfl) ⟨1320036, by rfl⟩ : syracuseStep 3520097 = 2640073) B2640073
theorem B9058007 : Blo 694316 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B1881929 : Blo 694316 1881929 := bstep (se 2 (by rfl) ⟨705723, by rfl⟩ : syracuseStep 1881929 = 1411447) B1411447
theorem B2013103 : Blo 694316 2013103 := bstep (se 1 (by rfl) ⟨1509827, by rfl⟩ : syracuseStep 2013103 = 3019655) B3019655
theorem B4241929 : Blo 694316 4241929 := bstep (se 2 (by rfl) ⟨1590723, by rfl⟩ : syracuseStep 4241929 = 3181447) B3181447
theorem B2505431 : Blo 694316 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B25475953 : Blo 694316 25475953 := bstep (se 2 (by rfl) ⟨9553482, by rfl⟩ : syracuseStep 25475953 = 19106965) B19106965
theorem B3521555 : Blo 694316 3521555 := bstep (se 1 (by rfl) ⟨2641166, by rfl⟩ : syracuseStep 3521555 = 5282333) B5282333
theorem B9550871 : Blo 694316 9550871 := bstep (se 1 (by rfl) ⟨7163153, by rfl⟩ : syracuseStep 9550871 = 14326307) B14326307
theorem B1490167 : Blo 694316 1490167 := bstep (se 1 (by rfl) ⟨1117625, by rfl⟩ : syracuseStep 1490167 = 2235251) B2235251
theorem B2505995 : Blo 694316 2505995 := bstep (se 1 (by rfl) ⟨1879496, by rfl⟩ : syracuseStep 2505995 = 3758993) B3758993
theorem B2637143 : Blo 694316 2637143 := bstep (se 1 (by rfl) ⟨1977857, by rfl⟩ : syracuseStep 2637143 = 3955715) B3955715
theorem B1982141 : Blo 694316 1982141 := bstep (se 3 (by rfl) ⟨371651, by rfl⟩ : syracuseStep 1982141 = 743303) B743303
theorem B10862351 : Blo 694316 10862351 := bstep (se 1 (by rfl) ⟨8146763, by rfl⟩ : syracuseStep 10862351 = 16293527) B16293527
theorem B2638433 : Blo 694316 2638433 := bstep (se 2 (by rfl) ⟨989412, by rfl⟩ : syracuseStep 2638433 = 1978825) B1978825
theorem B2507681 : Blo 694316 2507681 := bstep (se 2 (by rfl) ⟨940380, by rfl⟩ : syracuseStep 2507681 = 1880761) B1880761
theorem B1590671 : Blo 694316 1590671 := bstep (se 1 (by rfl) ⟨1193003, by rfl⟩ : syracuseStep 1590671 = 2386007) B2386007
theorem B2344571 : Blo 694316 2344571 := bstep (se 1 (by rfl) ⟨1758428, by rfl⟩ : syracuseStep 2344571 = 3516857) B3516857
theorem B2344733 : Blo 694316 2344733 := bstep (se 3 (by rfl) ⟨439637, by rfl⟩ : syracuseStep 2344733 = 879275) B879275
theorem B16893755 : Blo 694316 16893755 := bstep (se 1 (by rfl) ⟨12670316, by rfl⟩ : syracuseStep 16893755 = 25340633) B25340633
theorem B8931161 : Blo 694316 8931161 := bstep (se 2 (by rfl) ⟨3349185, by rfl⟩ : syracuseStep 8931161 = 6698371) B6698371
theorem B3524471 : Blo 694316 3524471 := bstep (se 1 (by rfl) ⟨2643353, by rfl⟩ : syracuseStep 3524471 = 5286707) B5286707
theorem B2639891 : Blo 694316 2639891 := bstep (se 1 (by rfl) ⟨1979918, by rfl⟩ : syracuseStep 2639891 = 3959837) B3959837
theorem B11290661 : Blo 694316 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B870439 : Blo 694316 870439 := bstep (se 1 (by rfl) ⟨652829, by rfl⟩ : syracuseStep 870439 = 1305659) B1305659
theorem B2508995 : Blo 694316 2508995 := bstep (se 1 (by rfl) ⟨1881746, by rfl⟩ : syracuseStep 2508995 = 3763493) B3763493
theorem B4245821 : Blo 694316 4245821 := bstep (se 3 (by rfl) ⟨796091, by rfl⟩ : syracuseStep 4245821 = 1592183) B1592183
theorem B12863897 : Blo 694316 12863897 := bstep (se 2 (by rfl) ⟨4823961, by rfl⟩ : syracuseStep 12863897 = 9647923) B9647923
theorem B2345435 : Blo 694316 2345435 := bstep (se 1 (by rfl) ⟨1759076, by rfl⟩ : syracuseStep 2345435 = 3518153) B3518153
theorem B2640347 : Blo 694316 2640347 := bstep (se 1 (by rfl) ⟨1980260, by rfl⟩ : syracuseStep 2640347 = 3960521) B3960521
theorem B1985273 : Blo 694316 1985273 := bstep (se 2 (by rfl) ⟨744477, by rfl⟩ : syracuseStep 1985273 = 1488955) B1488955
theorem B2968427 : Blo 694316 2968427 := bstep (se 1 (by rfl) ⟨2226320, by rfl⟩ : syracuseStep 2968427 = 4452641) B4452641
theorem B2346137 : Blo 694316 2346137 := bstep (se 2 (by rfl) ⟨879801, by rfl⟩ : syracuseStep 2346137 = 1759603) B1759603
theorem B13716773 : Blo 694316 13716773 := bstep (se 4 (by rfl) ⟨1285947, by rfl⟩ : syracuseStep 13716773 = 2571895) B2571895
theorem B2641531 : Blo 694316 2641531 := bstep (se 1 (by rfl) ⟨1981148, by rfl⟩ : syracuseStep 2641531 = 3962297) B3962297
theorem B3395195 : Blo 694316 3395195 := bstep (se 1 (by rfl) ⟨2546396, by rfl⟩ : syracuseStep 3395195 = 5092793) B5092793
theorem B2510767 : Blo 694316 2510767 := bstep (se 1 (by rfl) ⟨1883075, by rfl⟩ : syracuseStep 2510767 = 3766151) B3766151
theorem B152457137 : Blo 694316 152457137 := bstep (se 2 (by rfl) ⟨57171426, by rfl⟩ : syracuseStep 152457137 = 114342853) B114342853
theorem B13062221 : Blo 694316 13062221 := bstep (se 3 (by rfl) ⟨2449166, by rfl⟩ : syracuseStep 13062221 = 4898333) B4898333
theorem B1986731 : Blo 694316 1986731 := bstep (se 1 (by rfl) ⟨1490048, by rfl⟩ : syracuseStep 1986731 = 2980097) B2980097
theorem B5951717 : Blo 694316 5951717 := bstep (se 4 (by rfl) ⟨557973, by rfl⟩ : syracuseStep 5951717 = 1115947) B1115947
theorem B2347325 : Blo 694316 2347325 := bstep (se 3 (by rfl) ⟨440123, by rfl⟩ : syracuseStep 2347325 = 880247) B880247
theorem B1757659 : Blo 694316 1757659 := bstep (se 1 (by rfl) ⟨1318244, by rfl⟩ : syracuseStep 1757659 = 2636489) B2636489
theorem B2642807 : Blo 694316 2642807 := bstep (se 1 (by rfl) ⟨1982105, by rfl⟩ : syracuseStep 2642807 = 3964211) B3964211
theorem B6673427 : Blo 694316 6673427 := bstep (se 1 (by rfl) ⟨5005070, by rfl⟩ : syracuseStep 6673427 = 10010141) B10010141
theorem B2151481 : Blo 694316 2151481 := bstep (se 2 (by rfl) ⟨806805, by rfl⟩ : syracuseStep 2151481 = 1613611) B1613611
theorem B1758287 : Blo 694316 1758287 := bstep (se 1 (by rfl) ⟨1318715, by rfl⟩ : syracuseStep 1758287 = 2637431) B2637431
theorem B2348189 : Blo 694316 2348189 := bstep (se 3 (by rfl) ⟨440285, by rfl⟩ : syracuseStep 2348189 = 880571) B880571
theorem B5297399 : Blo 694316 5297399 := bstep (se 1 (by rfl) ⟨3973049, by rfl⟩ : syracuseStep 5297399 = 7946099) B7946099
theorem B1103323 : Blo 694316 1103323 := bstep (se 1 (by rfl) ⟨827492, by rfl⟩ : syracuseStep 1103323 = 1654985) B1654985
theorem B19092955 : Blo 694316 19092955 := bstep (se 1 (by rfl) ⟨14319716, by rfl⟩ : syracuseStep 19092955 = 28639433) B28639433
theorem B7263749 : Blo 694316 7263749 := bstep (se 4 (by rfl) ⟨680976, by rfl⟩ : syracuseStep 7263749 = 1361953) B1361953
theorem B33904277 : Blo 694316 33904277 := bstep (se 6 (by rfl) ⟨794631, by rfl⟩ : syracuseStep 33904277 = 1589263) B1589263
theorem B2348729 : Blo 694316 2348729 := bstep (se 2 (by rfl) ⟨880773, by rfl⟩ : syracuseStep 2348729 = 1761547) B1761547
theorem B2512583 : Blo 694316 2512583 := bstep (se 1 (by rfl) ⟨1884437, by rfl⟩ : syracuseStep 2512583 = 3768875) B3768875
theorem B1758935 : Blo 694316 1758935 := bstep (se 1 (by rfl) ⟨1319201, by rfl⟩ : syracuseStep 1758935 = 2638403) B2638403
theorem B5297885 : Blo 694316 5297885 := bstep (se 3 (by rfl) ⟨993353, by rfl⟩ : syracuseStep 5297885 = 1986707) B1986707
theorem B2643779 : Blo 694316 2643779 := bstep (se 1 (by rfl) ⟨1982834, by rfl⟩ : syracuseStep 2643779 = 3965669) B3965669
theorem B1562543 : Blo 694316 1562543 := bstep (se 1 (by rfl) ⟨1171907, by rfl⟩ : syracuseStep 1562543 = 2343815) B2343815
theorem B1562795 : Blo 694316 1562795 := bstep (se 1 (by rfl) ⟨1172096, by rfl⟩ : syracuseStep 1562795 = 2344193) B2344193
theorem B2349323 : Blo 694316 2349323 := bstep (se 1 (by rfl) ⟨1761992, by rfl⟩ : syracuseStep 2349323 = 3523985) B3523985
theorem B2644235 : Blo 694316 2644235 := bstep (se 1 (by rfl) ⟨1983176, by rfl⟩ : syracuseStep 2644235 = 3966353) B3966353
theorem B2349593 : Blo 694316 2349593 := bstep (se 2 (by rfl) ⟨881097, by rfl⟩ : syracuseStep 2349593 = 1762195) B1762195
theorem B1563335 : Blo 694316 1563335 := bstep (se 1 (by rfl) ⟨1172501, by rfl⟩ : syracuseStep 1563335 = 2345003) B2345003
theorem B5954381 : Blo 694316 5954381 := bstep (se 3 (by rfl) ⟨1116446, by rfl⟩ : syracuseStep 5954381 = 2232893) B2232893
theorem B2710367 : Blo 694316 2710367 := bstep (se 1 (by rfl) ⟨2032775, by rfl⟩ : syracuseStep 2710367 = 4065551) B4065551
theorem B2644919 : Blo 694316 2644919 := bstep (se 1 (by rfl) ⟨1983689, by rfl⟩ : syracuseStep 2644919 = 3967379) B3967379
theorem B3529655 : Blo 694316 3529655 := bstep (se 1 (by rfl) ⟨2647241, by rfl⟩ : syracuseStep 3529655 = 5294483) B5294483
theorem B744571 : Blo 694316 744571 := bstep (se 1 (by rfl) ⟨558428, by rfl⟩ : syracuseStep 744571 = 1116857) B1116857
theorem B10050905 : Blo 694316 10050905 := bstep (se 2 (by rfl) ⟨3769089, by rfl⟩ : syracuseStep 10050905 = 7538179) B7538179
theorem B1564199 : Blo 694316 1564199 := bstep (se 1 (by rfl) ⟨1173149, by rfl⟩ : syracuseStep 1564199 = 2346299) B2346299
theorem B2350727 : Blo 694316 2350727 := bstep (se 1 (by rfl) ⟨1763045, by rfl⟩ : syracuseStep 2350727 = 3526091) B3526091
theorem B2350781 : Blo 694316 2350781 := bstep (se 3 (by rfl) ⟨440771, by rfl⟩ : syracuseStep 2350781 = 881543) B881543
theorem B2645693 : Blo 694316 2645693 := bstep (se 3 (by rfl) ⟨496067, by rfl⟩ : syracuseStep 2645693 = 992135) B992135
theorem B2350943 : Blo 694316 2350943 := bstep (se 1 (by rfl) ⟨1763207, by rfl⟩ : syracuseStep 2350943 = 3526415) B3526415
theorem B1564523 : Blo 694316 1564523 := bstep (se 1 (by rfl) ⟨1173392, by rfl⟩ : syracuseStep 1564523 = 2346785) B2346785
theorem B1564577 : Blo 694316 1564577 := bstep (se 2 (by rfl) ⟨586716, by rfl⟩ : syracuseStep 1564577 = 1173433) B1173433
theorem B2351105 : Blo 694316 2351105 := bstep (se 2 (by rfl) ⟨881664, by rfl⟩ : syracuseStep 2351105 = 1763329) B1763329
theorem B1564919 : Blo 694316 1564919 := bstep (se 1 (by rfl) ⟨1173689, by rfl⟩ : syracuseStep 1564919 = 2347379) B2347379
theorem B1761527 : Blo 694316 1761527 := bstep (se 1 (by rfl) ⟨1321145, by rfl⟩ : syracuseStep 1761527 = 2642291) B2642291
theorem B1171705 : Blo 694316 1171705 := bstep (se 2 (by rfl) ⟨439389, by rfl⟩ : syracuseStep 1171705 = 878779) B878779
theorem B2646377 : Blo 694316 2646377 := bstep (se 2 (by rfl) ⟨992391, by rfl⟩ : syracuseStep 2646377 = 1984783) B1984783
theorem B3531113 : Blo 694316 3531113 := bstep (se 2 (by rfl) ⟨1324167, by rfl⟩ : syracuseStep 3531113 = 2648335) B2648335
theorem B4514251 : Blo 694316 4514251 := bstep (se 1 (by rfl) ⟨3385688, by rfl⟩ : syracuseStep 4514251 = 6771377) B6771377
theorem B1171975 : Blo 694316 1171975 := bstep (se 1 (by rfl) ⟨878981, by rfl⟩ : syracuseStep 1171975 = 1757963) B1757963
theorem B2515495 : Blo 694316 2515495 := bstep (se 1 (by rfl) ⟨1886621, by rfl⟩ : syracuseStep 2515495 = 3773243) B3773243
theorem B10019537 : Blo 694316 10019537 := bstep (se 2 (by rfl) ⟨3757326, by rfl⟩ : syracuseStep 10019537 = 7514653) B7514653
theorem B2351915 : Blo 694316 2351915 := bstep (se 1 (by rfl) ⟨1763936, by rfl⟩ : syracuseStep 2351915 = 3527873) B3527873
theorem B1565513 : Blo 694316 1565513 := bstep (se 2 (by rfl) ⟨587067, by rfl⟩ : syracuseStep 1565513 = 1174135) B1174135
theorem B5006225 : Blo 694316 5006225 := bstep (se 2 (by rfl) ⟨1877334, by rfl⟩ : syracuseStep 5006225 = 3754669) B3754669
theorem B1172407 : Blo 694316 1172407 := bstep (se 1 (by rfl) ⟨879305, by rfl⟩ : syracuseStep 1172407 = 1758611) B1758611
theorem B2352185 : Blo 694316 2352185 := bstep (se 2 (by rfl) ⟨882069, by rfl⟩ : syracuseStep 2352185 = 1764139) B1764139
theorem B2974799 : Blo 694316 2974799 := bstep (se 1 (by rfl) ⟨2231099, by rfl⟩ : syracuseStep 2974799 = 4462199) B4462199
theorem B1172603 : Blo 694316 1172603 := bstep (se 1 (by rfl) ⟨879452, by rfl⟩ : syracuseStep 1172603 = 1758905) B1758905
theorem B1860989 : Blo 694316 1860989 := bstep (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) B697871
theorem B2352509 : Blo 694316 2352509 := bstep (se 3 (by rfl) ⟨441095, by rfl⟩ : syracuseStep 2352509 = 882191) B882191
theorem B1041839 : Blo 694316 1041839 := bstep (se 1 (by rfl) ⟨781379, by rfl⟩ : syracuseStep 1041839 = 1562759) B1562759
theorem B2123227 : Blo 694316 2123227 := bstep (se 1 (by rfl) ⟨1592420, by rfl⟩ : syracuseStep 2123227 = 3184841) B3184841
theorem B1041929 : Blo 694316 1041929 := bstep (se 2 (by rfl) ⟨390723, by rfl⟩ : syracuseStep 1041929 = 781447) B781447
theorem B1173001 : Blo 694316 1173001 := bstep (se 2 (by rfl) ⟨439875, by rfl⟩ : syracuseStep 1173001 = 879751) B879751
theorem B1041959 : Blo 694316 1041959 := bstep (se 1 (by rfl) ⟨781469, by rfl⟩ : syracuseStep 1041959 = 1562939) B1562939
theorem B3761761 : Blo 694316 3761761 := bstep (se 2 (by rfl) ⟨1410660, by rfl⟩ : syracuseStep 3761761 = 2821321) B2821321
theorem B1566305 : Blo 694316 1566305 := bstep (se 2 (by rfl) ⟨587364, by rfl⟩ : syracuseStep 1566305 = 1174729) B1174729
theorem B1042043 : Blo 694316 1042043 := bstep (se 1 (by rfl) ⟨781532, by rfl⟩ : syracuseStep 1042043 = 1563065) B1563065
theorem B1762955 : Blo 694316 1762955 := bstep (se 1 (by rfl) ⟨1322216, by rfl⟩ : syracuseStep 1762955 = 2644433) B2644433
theorem B2352779 : Blo 694316 2352779 := bstep (se 1 (by rfl) ⟨1764584, by rfl⟩ : syracuseStep 2352779 = 3529169) B3529169
theorem B1173163 : Blo 694316 1173163 := bstep (se 1 (by rfl) ⟨879872, by rfl⟩ : syracuseStep 1173163 = 1759745) B1759745
theorem B3565255 : Blo 694316 3565255 := bstep (se 1 (by rfl) ⟨2673941, by rfl⟩ : syracuseStep 3565255 = 5347883) B5347883
theorem B1042169 : Blo 694316 1042169 := bstep (se 2 (by rfl) ⟨390813, by rfl⟩ : syracuseStep 1042169 = 781627) B781627
theorem B1042271 : Blo 694316 1042271 := bstep (se 1 (by rfl) ⟨781703, by rfl⟩ : syracuseStep 1042271 = 1563407) B1563407
theorem B1763167 : Blo 694316 1763167 := bstep (se 1 (by rfl) ⟨1322375, by rfl⟩ : syracuseStep 1763167 = 2644751) B2644751
theorem B1042283 : Blo 694316 1042283 := bstep (se 1 (by rfl) ⟨781712, by rfl⟩ : syracuseStep 1042283 = 1563425) B1563425
theorem B10053557 : Blo 694316 10053557 := bstep (se 5 (by rfl) ⟨471260, by rfl⟩ : syracuseStep 10053557 = 942521) B942521
theorem B1566647 : Blo 694316 1566647 := bstep (se 1 (by rfl) ⟨1174985, by rfl⟩ : syracuseStep 1566647 = 2349971) B2349971
theorem B1173467 : Blo 694316 1173467 := bstep (se 1 (by rfl) ⟨880100, by rfl⟩ : syracuseStep 1173467 = 1760201) B1760201
theorem B1042511 : Blo 694316 1042511 := bstep (se 1 (by rfl) ⟨781883, by rfl⟩ : syracuseStep 1042511 = 1563767) B1563767
theorem B17885285 : Blo 694316 17885285 := bstep (se 4 (by rfl) ⟨1676745, by rfl⟩ : syracuseStep 17885285 = 3353491) B3353491
theorem B1042631 : Blo 694316 1042631 := bstep (se 1 (by rfl) ⟨781973, by rfl⟩ : syracuseStep 1042631 = 1563947) B1563947
theorem B1173703 : Blo 694316 1173703 := bstep (se 1 (by rfl) ⟨880277, by rfl⟩ : syracuseStep 1173703 = 1760555) B1760555
theorem B1042793 : Blo 694316 1042793 := bstep (se 2 (by rfl) ⟨391047, by rfl⟩ : syracuseStep 1042793 = 782095) B782095
theorem B1173865 : Blo 694316 1173865 := bstep (se 2 (by rfl) ⟨440199, by rfl⟩ : syracuseStep 1173865 = 880399) B880399
theorem B1042871 : Blo 694316 1042871 := bstep (se 1 (by rfl) ⟨782153, by rfl⟩ : syracuseStep 1042871 = 1564307) B1564307
theorem B1042907 : Blo 694316 1042907 := bstep (se 1 (by rfl) ⟨782180, by rfl⟩ : syracuseStep 1042907 = 1564361) B1564361
theorem B1567241 : Blo 694316 1567241 := bstep (se 2 (by rfl) ⟨587715, by rfl⟩ : syracuseStep 1567241 = 1175431) B1175431
theorem B2353697 : Blo 694316 2353697 := bstep (se 2 (by rfl) ⟨882636, by rfl⟩ : syracuseStep 2353697 = 1765273) B1765273
theorem B2648609 : Blo 694316 2648609 := bstep (se 2 (by rfl) ⟨993228, by rfl⟩ : syracuseStep 2648609 = 1986457) B1986457
theorem B10742305 : Blo 694316 10742305 := bstep (se 2 (by rfl) ⟨4028364, by rfl⟩ : syracuseStep 10742305 = 8056729) B8056729
theorem B10316489 : Blo 694316 10316489 := bstep (se 2 (by rfl) ⟨3868683, by rfl⟩ : syracuseStep 10316489 = 7737367) B7737367
theorem B1764089 : Blo 694316 1764089 := bstep (se 2 (by rfl) ⟨661533, by rfl⟩ : syracuseStep 1764089 = 1323067) B1323067
theorem B2353913 : Blo 694316 2353913 := bstep (se 2 (by rfl) ⟨882717, by rfl⟩ : syracuseStep 2353913 = 1765435) B1765435
theorem B1567583 : Blo 694316 1567583 := bstep (se 1 (by rfl) ⟨1175687, by rfl⟩ : syracuseStep 1567583 = 2351375) B2351375
theorem B781231 : Blo 694316 781231 := bstep (se 1 (by rfl) ⟨585923, by rfl⟩ : syracuseStep 781231 = 1171847) B1171847
theorem B1043375 : Blo 694316 1043375 := bstep (se 1 (by rfl) ⟨782531, by rfl⟩ : syracuseStep 1043375 = 1565063) B1565063
theorem B1174459 : Blo 694316 1174459 := bstep (se 1 (by rfl) ⟨880844, by rfl⟩ : syracuseStep 1174459 = 1761689) B1761689
theorem B2354183 : Blo 694316 2354183 := bstep (se 1 (by rfl) ⟨1765637, by rfl⟩ : syracuseStep 2354183 = 3531275) B3531275
theorem B2649095 : Blo 694316 2649095 := bstep (se 1 (by rfl) ⟨1986821, by rfl⟩ : syracuseStep 2649095 = 3973643) B3973643
theorem B1043465 : Blo 694316 1043465 := bstep (se 2 (by rfl) ⟨391299, by rfl⟩ : syracuseStep 1043465 = 782599) B782599
theorem B1567763 : Blo 694316 1567763 := bstep (se 1 (by rfl) ⟨1175822, by rfl⟩ : syracuseStep 1567763 = 2351645) B2351645
theorem B10742807 : Blo 694316 10742807 := bstep (se 1 (by rfl) ⟨8057105, by rfl⟩ : syracuseStep 10742807 = 16114211) B16114211
theorem B879655 : Blo 694316 879655 := bstep (se 1 (by rfl) ⟨659741, by rfl⟩ : syracuseStep 879655 = 1319483) B1319483
theorem B1043495 : Blo 694316 1043495 := bstep (se 1 (by rfl) ⟨782621, by rfl⟩ : syracuseStep 1043495 = 1565243) B1565243
theorem B1174567 : Blo 694316 1174567 := bstep (se 1 (by rfl) ⟨880925, by rfl⟩ : syracuseStep 1174567 = 1761851) B1761851
theorem B2354291 : Blo 694316 2354291 := bstep (se 1 (by rfl) ⟨1765718, by rfl⟩ : syracuseStep 2354291 = 3531437) B3531437
theorem B8907893 : Blo 694316 8907893 := bstep (se 5 (by rfl) ⟨417557, by rfl⟩ : syracuseStep 8907893 = 835115) B835115
theorem B1043579 : Blo 694316 1043579 := bstep (se 1 (by rfl) ⟨782684, by rfl⟩ : syracuseStep 1043579 = 1565369) B1565369
theorem B1043705 : Blo 694316 1043705 := bstep (se 2 (by rfl) ⟨391389, by rfl⟩ : syracuseStep 1043705 = 782779) B782779
theorem B781663 : Blo 694316 781663 := bstep (se 1 (by rfl) ⟨586247, by rfl⟩ : syracuseStep 781663 = 1172495) B1172495
theorem B1043807 : Blo 694316 1043807 := bstep (se 1 (by rfl) ⟨782855, by rfl⟩ : syracuseStep 1043807 = 1565711) B1565711
theorem B1568105 : Blo 694316 1568105 := bstep (se 2 (by rfl) ⟨588039, by rfl⟩ : syracuseStep 1568105 = 1176079) B1176079
theorem B879979 : Blo 694316 879979 := bstep (se 1 (by rfl) ⟨659984, by rfl⟩ : syracuseStep 879979 = 1319969) B1319969
theorem B1043819 : Blo 694316 1043819 := bstep (se 1 (by rfl) ⟨782864, by rfl⟩ : syracuseStep 1043819 = 1565729) B1565729
theorem B1174891 : Blo 694316 1174891 := bstep (se 1 (by rfl) ⟨881168, by rfl⟩ : syracuseStep 1174891 = 1762337) B1762337
theorem B1764737 : Blo 694316 1764737 := bstep (se 2 (by rfl) ⟨661776, by rfl⟩ : syracuseStep 1764737 = 1323553) B1323553
theorem B2354561 : Blo 694316 2354561 := bstep (se 2 (by rfl) ⟨882960, by rfl⟩ : syracuseStep 2354561 = 1765921) B1765921
theorem B2649581 : Blo 694316 2649581 := bstep (se 3 (by rfl) ⟨496796, by rfl⟩ : syracuseStep 2649581 = 993593) B993593
theorem B1044047 : Blo 694316 1044047 := bstep (se 1 (by rfl) ⟨783035, by rfl⟩ : syracuseStep 1044047 = 1566071) B1566071
theorem B782023 : Blo 694316 782023 := bstep (se 1 (by rfl) ⟨586517, by rfl⟩ : syracuseStep 782023 = 1173035) B1173035
theorem B1044167 : Blo 694316 1044167 := bstep (se 1 (by rfl) ⟨783125, by rfl⟩ : syracuseStep 1044167 = 1566251) B1566251
theorem B4222763 : Blo 694316 4222763 := bstep (se 1 (by rfl) ⟨3167072, by rfl⟩ : syracuseStep 4222763 = 6334145) B6334145
theorem B1044329 : Blo 694316 1044329 := bstep (se 2 (by rfl) ⟨391623, by rfl⟩ : syracuseStep 1044329 = 783247) B783247
theorem B1044407 : Blo 694316 1044407 := bstep (se 1 (by rfl) ⟨783305, by rfl⟩ : syracuseStep 1044407 = 1566611) B1566611
theorem B6352825 : Blo 694316 6352825 := bstep (se 2 (by rfl) ⟨2382309, by rfl⟩ : syracuseStep 6352825 = 4764619) B4764619
theorem B1568699 : Blo 694316 1568699 := bstep (se 1 (by rfl) ⟨1176524, by rfl⟩ : syracuseStep 1568699 = 2353049) B2353049
theorem B1044443 : Blo 694316 1044443 := bstep (se 1 (by rfl) ⟨783332, by rfl⟩ : syracuseStep 1044443 = 1566665) B1566665
theorem B3960839 : Blo 694316 3960839 := bstep (se 1 (by rfl) ⟨2970629, by rfl⟩ : syracuseStep 3960839 = 5941259) B5941259
theorem B1568825 : Blo 694316 1568825 := bstep (se 2 (by rfl) ⟨588309, by rfl⟩ : syracuseStep 1568825 = 1176619) B1176619
theorem B2650265 : Blo 694316 2650265 := bstep (se 2 (by rfl) ⟨993849, by rfl⟩ : syracuseStep 2650265 = 1987699) B1987699
theorem B1765547 : Blo 694316 1765547 := bstep (se 1 (by rfl) ⟨1324160, by rfl⟩ : syracuseStep 1765547 = 2648321) B2648321
theorem B2355371 : Blo 694316 2355371 := bstep (se 1 (by rfl) ⟨1766528, by rfl⟩ : syracuseStep 2355371 = 3533057) B3533057
theorem B5501245 : Blo 694316 5501245 := bstep (se 3 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 5501245 = 2062967) B2062967
theorem B2224513 : Blo 694316 2224513 := bstep (se 2 (by rfl) ⟨834192, by rfl⟩ : syracuseStep 2224513 = 1668385) B1668385
theorem B1175951 : Blo 694316 1175951 := bstep (se 1 (by rfl) ⟨881963, by rfl⟩ : syracuseStep 1175951 = 1763927) B1763927
theorem B1569167 : Blo 694316 1569167 := bstep (se 1 (by rfl) ⟨1176875, by rfl⟩ : syracuseStep 1569167 = 2353751) B2353751
theorem B1044911 : Blo 694316 1044911 := bstep (se 1 (by rfl) ⟨783683, by rfl⟩ : syracuseStep 1044911 = 1567367) B1567367
theorem B1045001 : Blo 694316 1045001 := bstep (se 2 (by rfl) ⟨391875, by rfl⟩ : syracuseStep 1045001 = 783751) B783751
theorem B782887 : Blo 694316 782887 := bstep (se 1 (by rfl) ⟨587165, by rfl⟩ : syracuseStep 782887 = 1174331) B1174331
theorem B1045031 : Blo 694316 1045031 := bstep (se 1 (by rfl) ⟨783773, by rfl⟩ : syracuseStep 1045031 = 1567547) B1567547
theorem B881275 : Blo 694316 881275 := bstep (se 1 (by rfl) ⟨660956, by rfl⟩ : syracuseStep 881275 = 1321913) B1321913
theorem B1045115 : Blo 694316 1045115 := bstep (se 1 (by rfl) ⟨783836, by rfl⟩ : syracuseStep 1045115 = 1567673) B1567673
theorem B1176187 : Blo 694316 1176187 := bstep (se 1 (by rfl) ⟨882140, by rfl⟩ : syracuseStep 1176187 = 1764281) B1764281
theorem B2355911 : Blo 694316 2355911 := bstep (se 1 (by rfl) ⟨1766933, by rfl⟩ : syracuseStep 2355911 = 3533867) B3533867
theorem B1569491 : Blo 694316 1569491 := bstep (se 1 (by rfl) ⟨1177118, by rfl⟩ : syracuseStep 1569491 = 2354237) B2354237
theorem B1045241 : Blo 694316 1045241 := bstep (se 2 (by rfl) ⟨391965, by rfl⟩ : syracuseStep 1045241 = 783931) B783931
theorem B1045343 : Blo 694316 1045343 := bstep (se 1 (by rfl) ⟨784007, by rfl⟩ : syracuseStep 1045343 = 1568015) B1568015
theorem B1045355 : Blo 694316 1045355 := bstep (se 1 (by rfl) ⟨784016, by rfl⟩ : syracuseStep 1045355 = 1568033) B1568033
theorem B4223927 : Blo 694316 4223927 := bstep (se 1 (by rfl) ⟨3167945, by rfl⟩ : syracuseStep 4223927 = 6335891) B6335891
theorem B1766407 : Blo 694316 1766407 := bstep (se 1 (by rfl) ⟨1324805, by rfl⟩ : syracuseStep 1766407 = 2649611) B2649611
theorem B1045583 : Blo 694316 1045583 := bstep (se 1 (by rfl) ⟨784187, by rfl⟩ : syracuseStep 1045583 = 1568375) B1568375
theorem B2651251 : Blo 694316 2651251 := bstep (se 1 (by rfl) ⟨1988438, by rfl⟩ : syracuseStep 2651251 = 3976877) B3976877
theorem B1045703 : Blo 694316 1045703 := bstep (se 1 (by rfl) ⟨784277, by rfl⟩ : syracuseStep 1045703 = 1568555) B1568555
theorem B1045865 : Blo 694316 1045865 := bstep (se 2 (by rfl) ⟨392199, by rfl⟩ : syracuseStep 1045865 = 784399) B784399
theorem B1045943 : Blo 694316 1045943 := bstep (se 1 (by rfl) ⟨784457, by rfl⟩ : syracuseStep 1045943 = 1568915) B1568915
theorem B1045979 : Blo 694316 1045979 := bstep (se 1 (by rfl) ⟨784484, by rfl⟩ : syracuseStep 1045979 = 1568969) B1568969
theorem B1177051 : Blo 694316 1177051 := bstep (se 1 (by rfl) ⟨882788, by rfl⟩ : syracuseStep 1177051 = 1765577) B1765577
theorem B5273099 : Blo 694316 5273099 := bstep (se 1 (by rfl) ⟨3954824, by rfl⟩ : syracuseStep 5273099 = 7909649) B7909649
theorem B2356775 : Blo 694316 2356775 := bstep (se 1 (by rfl) ⟨1767581, by rfl⟩ : syracuseStep 2356775 = 3535163) B3535163
theorem B1570427 : Blo 694316 1570427 := bstep (se 1 (by rfl) ⟨1177820, by rfl⟩ : syracuseStep 1570427 = 2355641) B2355641
theorem B1767035 : Blo 694316 1767035 := bstep (se 1 (by rfl) ⟨1325276, by rfl⟩ : syracuseStep 1767035 = 2650553) B2650553
theorem B1570553 : Blo 694316 1570553 := bstep (se 2 (by rfl) ⟨588957, by rfl⟩ : syracuseStep 1570553 = 1177915) B1177915
theorem B1767329 : Blo 694316 1767329 := bstep (se 2 (by rfl) ⟨662748, by rfl⟩ : syracuseStep 1767329 = 1325497) B1325497
theorem B1046447 : Blo 694316 1046447 := bstep (se 1 (by rfl) ⟨784835, by rfl⟩ : syracuseStep 1046447 = 1569671) B1569671
theorem B1570823 : Blo 694316 1570823 := bstep (se 1 (by rfl) ⟨1178117, by rfl⟩ : syracuseStep 1570823 = 2356235) B2356235
theorem B1046537 : Blo 694316 1046537 := bstep (se 2 (by rfl) ⟨392451, by rfl⟩ : syracuseStep 1046537 = 784903) B784903
theorem B1046567 : Blo 694316 1046567 := bstep (se 1 (by rfl) ⟨784925, by rfl⟩ : syracuseStep 1046567 = 1569851) B1569851
theorem B1177679 : Blo 694316 1177679 := bstep (se 1 (by rfl) ⟨883259, by rfl⟩ : syracuseStep 1177679 = 1766519) B1766519
theorem B1570895 : Blo 694316 1570895 := bstep (se 1 (by rfl) ⟨1178171, by rfl⟩ : syracuseStep 1570895 = 2356343) B2356343
theorem B784507 : Blo 694316 784507 := bstep (se 1 (by rfl) ⟨588380, by rfl⟩ : syracuseStep 784507 = 1176761) B1176761
theorem B1046651 : Blo 694316 1046651 := bstep (se 1 (by rfl) ⟨784988, by rfl⟩ : syracuseStep 1046651 = 1569977) B1569977
theorem B1046777 : Blo 694316 1046777 := bstep (se 2 (by rfl) ⟨392541, by rfl⟩ : syracuseStep 1046777 = 785083) B785083
theorem B4520279 : Blo 694316 4520279 := bstep (se 1 (by rfl) ⟨3390209, by rfl⟩ : syracuseStep 4520279 = 6780419) B6780419
theorem B1046879 : Blo 694316 1046879 := bstep (se 1 (by rfl) ⟨785159, by rfl⟩ : syracuseStep 1046879 = 1570319) B1570319
theorem B1669481 : Blo 694316 1669481 := bstep (se 2 (by rfl) ⟨626055, by rfl⟩ : syracuseStep 1669481 = 1252111) B1252111
theorem B1046891 : Blo 694316 1046891 := bstep (se 1 (by rfl) ⟨785168, by rfl⟩ : syracuseStep 1046891 = 1570337) B1570337
theorem B883163 : Blo 694316 883163 := bstep (se 1 (by rfl) ⟨662372, by rfl⟩ : syracuseStep 883163 = 1324745) B1324745
theorem B784975 : Blo 694316 784975 := bstep (se 1 (by rfl) ⟨588731, by rfl⟩ : syracuseStep 784975 = 1177463) B1177463
theorem B1047119 : Blo 694316 1047119 := bstep (se 1 (by rfl) ⟨785339, by rfl⟩ : syracuseStep 1047119 = 1570679) B1570679
theorem B1047239 : Blo 694316 1047239 := bstep (se 1 (by rfl) ⟨785429, by rfl⟩ : syracuseStep 1047239 = 1570859) B1570859
theorem B1047401 : Blo 694316 1047401 := bstep (se 2 (by rfl) ⟨392775, by rfl⟩ : syracuseStep 1047401 = 785551) B785551
theorem B3963755 : Blo 694316 3963755 := bstep (se 1 (by rfl) ⟨2972816, by rfl⟩ : syracuseStep 3963755 = 5945633) B5945633
theorem B883639 : Blo 694316 883639 := bstep (se 1 (by rfl) ⟨662729, by rfl⟩ : syracuseStep 883639 = 1325459) B1325459
theorem B785371 : Blo 694316 785371 := bstep (se 1 (by rfl) ⟨589028, by rfl⟩ : syracuseStep 785371 = 1178057) B1178057
theorem B24083729 : Blo 694316 24083729 := bstep (se 2 (by rfl) ⟨9031398, by rfl⟩ : syracuseStep 24083729 = 18062797) B18062797
theorem B5275043 : Blo 694316 5275043 := bstep (se 1 (by rfl) ⟨3956282, by rfl⟩ : syracuseStep 5275043 = 7912565) B7912565
theorem B1113679 : Blo 694316 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B5799557 : Blo 694316 5799557 := bstep (se 4 (by rfl) ⟨543708, by rfl⟩ : syracuseStep 5799557 = 1087417) B1087417
theorem B2227961 : Blo 694316 2227961 := bstep (se 2 (by rfl) ⟨835485, by rfl⟩ : syracuseStep 2227961 = 1670971) B1670971
theorem B2817899 : Blo 694316 2817899 := bstep (se 1 (by rfl) ⟨2113424, by rfl⟩ : syracuseStep 2817899 = 4226849) B4226849
theorem B2228075 : Blo 694316 2228075 := bstep (se 1 (by rfl) ⟨1671056, by rfl⟩ : syracuseStep 2228075 = 3342113) B3342113
theorem B8912915 : Blo 694316 8912915 := bstep (se 1 (by rfl) ⟨6684686, by rfl⟩ : syracuseStep 8912915 = 13369373) B13369373
theorem B5963813 : Blo 694316 5963813 := bstep (se 4 (by rfl) ⟨559107, by rfl⟩ : syracuseStep 5963813 = 1118215) B1118215
theorem B2228435 : Blo 694316 2228435 := bstep (se 1 (by rfl) ⟨1671326, by rfl⟩ : syracuseStep 2228435 = 3342653) B3342653
theorem B1671787 : Blo 694316 1671787 := bstep (se 1 (by rfl) ⟨1253840, by rfl⟩ : syracuseStep 1671787 = 2507681) B2507681
theorem B2982521 : Blo 694316 2982521 := bstep (se 2 (by rfl) ⟨1118445, by rfl⟩ : syracuseStep 2982521 = 2236891) B2236891
theorem B9634619 : Blo 694316 9634619 := bstep (se 1 (by rfl) ⟨7225964, by rfl⟩ : syracuseStep 9634619 = 14451929) B14451929
theorem B3343805 : Blo 694316 3343805 := bstep (se 3 (by rfl) ⟨626963, by rfl⟩ : syracuseStep 3343805 = 1253927) B1253927
theorem B1672663 : Blo 694316 1672663 := bstep (se 1 (by rfl) ⟨1254497, by rfl⟩ : syracuseStep 1672663 = 2508995) B2508995
theorem B5015681 : Blo 694316 5015681 := bstep (se 2 (by rfl) ⟨1880880, by rfl⟩ : syracuseStep 5015681 = 3761761) B3761761
theorem B9144515 : Blo 694316 9144515 := bstep (se 1 (by rfl) ⟨6858386, by rfl⟩ : syracuseStep 9144515 = 13716773) B13716773
theorem B4753673 : Blo 694316 4753673 := bstep (se 2 (by rfl) ⟨1782627, by rfl⟩ : syracuseStep 4753673 = 3565255) B3565255
theorem B2263463 : Blo 694316 2263463 := bstep (se 1 (by rfl) ⟨1697597, by rfl⟩ : syracuseStep 2263463 = 3395195) B3395195
theorem B7539479 : Blo 694316 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B3967811 : Blo 694316 3967811 := bstep (se 1 (by rfl) ⟨2975858, by rfl⟩ : syracuseStep 3967811 = 5951717) B5951717
theorem B4459535 : Blo 694316 4459535 := bstep (se 1 (by rfl) ⟨3344651, by rfl⟩ : syracuseStep 4459535 = 6689303) B6689303
theorem B14323073 : Blo 694316 14323073 := bstep (se 2 (by rfl) ⟨5371152, by rfl⟩ : syracuseStep 14323073 = 10742305) B10742305
theorem B1675055 : Blo 694316 1675055 := bstep (se 1 (by rfl) ⟨1256291, by rfl⟩ : syracuseStep 1675055 = 2512583) B2512583
theorem B3969587 : Blo 694316 3969587 := bstep (se 1 (by rfl) ⟨2977190, by rfl⟩ : syracuseStep 3969587 = 5954381) B5954381
theorem B24154685 : Blo 694316 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B1806911 : Blo 694316 1806911 := bstep (se 1 (by rfl) ⟨1355183, by rfl⟩ : syracuseStep 1806911 = 2710367) B2710367
theorem B3347689 : Blo 694316 3347689 := bstep (se 2 (by rfl) ⟨1255383, by rfl⟩ : syracuseStep 3347689 = 2510767) B2510767
theorem B988615 : Blo 694316 988615 := bstep (se 1 (by rfl) ⟨741461, by rfl⟩ : syracuseStep 988615 = 1482923) B1482923
theorem B3971045 : Blo 694316 3971045 := bstep (se 4 (by rfl) ⟨372285, by rfl⟩ : syracuseStep 3971045 = 744571) B744571
theorem B694559 : Blo 694316 694559 := bstep (se 1 (by rfl) ⟨520919, by rfl⟩ : syracuseStep 694559 = 1041839) B1041839
theorem B694619 : Blo 694316 694619 := bstep (se 1 (by rfl) ⟨520964, by rfl⟩ : syracuseStep 694619 = 1041929) B1041929
theorem B694639 : Blo 694316 694639 := bstep (se 1 (by rfl) ⟨520979, by rfl⟩ : syracuseStep 694639 = 1041959) B1041959
theorem B694695 : Blo 694316 694695 := bstep (se 1 (by rfl) ⟨521021, by rfl⟩ : syracuseStep 694695 = 1042043) B1042043
theorem B694779 : Blo 694316 694779 := bstep (se 1 (by rfl) ⟨521084, by rfl⟩ : syracuseStep 694779 = 1042169) B1042169
theorem B4463099 : Blo 694316 4463099 := bstep (se 1 (by rfl) ⟨3347324, by rfl⟩ : syracuseStep 4463099 = 6694649) B6694649
theorem B694847 : Blo 694316 694847 := bstep (se 1 (by rfl) ⟨521135, by rfl⟩ : syracuseStep 694847 = 1042271) B1042271
theorem B694855 : Blo 694316 694855 := bstep (se 1 (by rfl) ⟨521141, by rfl⟩ : syracuseStep 694855 = 1042283) B1042283
theorem B695007 : Blo 694316 695007 := bstep (se 1 (by rfl) ⟨521255, by rfl⟩ : syracuseStep 695007 = 1042511) B1042511
theorem B695087 : Blo 694316 695087 := bstep (se 1 (by rfl) ⟨521315, by rfl⟩ : syracuseStep 695087 = 1042631) B1042631
theorem B793391 : Blo 694316 793391 := bstep (se 1 (by rfl) ⟨595043, by rfl⟩ : syracuseStep 793391 = 1190087) B1190087
theorem B695195 : Blo 694316 695195 := bstep (se 1 (by rfl) ⟨521396, by rfl⟩ : syracuseStep 695195 = 1042793) B1042793
theorem B695247 : Blo 694316 695247 := bstep (se 1 (by rfl) ⟨521435, by rfl⟩ : syracuseStep 695247 = 1042871) B1042871
theorem B695271 : Blo 694316 695271 := bstep (se 1 (by rfl) ⟨521453, by rfl⟩ : syracuseStep 695271 = 1042907) B1042907
theorem B2039003 : Blo 694316 2039003 := bstep (se 1 (by rfl) ⟨1529252, by rfl⟩ : syracuseStep 2039003 = 3058505) B3058505
theorem B695583 : Blo 694316 695583 := bstep (se 1 (by rfl) ⟨521687, by rfl⟩ : syracuseStep 695583 = 1043375) B1043375
theorem B695643 : Blo 694316 695643 := bstep (se 1 (by rfl) ⟨521732, by rfl⟩ : syracuseStep 695643 = 1043465) B1043465
theorem B695663 : Blo 694316 695663 := bstep (se 1 (by rfl) ⟨521747, by rfl⟩ : syracuseStep 695663 = 1043495) B1043495
theorem B5938595 : Blo 694316 5938595 := bstep (se 1 (by rfl) ⟨4453946, by rfl⟩ : syracuseStep 5938595 = 8907893) B8907893
theorem B695719 : Blo 694316 695719 := bstep (se 1 (by rfl) ⟨521789, by rfl⟩ : syracuseStep 695719 = 1043579) B1043579
theorem B110042549 : Blo 694316 110042549 := bstep (se 5 (by rfl) ⟨5158244, by rfl⟩ : syracuseStep 110042549 = 10316489) B10316489
theorem B695803 : Blo 694316 695803 := bstep (se 1 (by rfl) ⟨521852, by rfl⟩ : syracuseStep 695803 = 1043705) B1043705
theorem B13377059 : Blo 694316 13377059 := bstep (se 1 (by rfl) ⟨10032794, by rfl⟩ : syracuseStep 13377059 = 20065589) B20065589
theorem B695871 : Blo 694316 695871 := bstep (se 1 (by rfl) ⟨521903, by rfl⟩ : syracuseStep 695871 = 1043807) B1043807
theorem B695879 : Blo 694316 695879 := bstep (se 1 (by rfl) ⟨521909, by rfl⟩ : syracuseStep 695879 = 1043819) B1043819
theorem B696031 : Blo 694316 696031 := bstep (se 1 (by rfl) ⟨522023, by rfl⟩ : syracuseStep 696031 = 1044047) B1044047
theorem B696111 : Blo 694316 696111 := bstep (se 1 (by rfl) ⟨522083, by rfl⟩ : syracuseStep 696111 = 1044167) B1044167
theorem B696219 : Blo 694316 696219 := bstep (se 1 (by rfl) ⟨522164, by rfl⟩ : syracuseStep 696219 = 1044329) B1044329
theorem B696271 : Blo 694316 696271 := bstep (se 1 (by rfl) ⟨522203, by rfl⟩ : syracuseStep 696271 = 1044407) B1044407
theorem B696295 : Blo 694316 696295 := bstep (se 1 (by rfl) ⟨522221, by rfl⟩ : syracuseStep 696295 = 1044443) B1044443
theorem B4464659 : Blo 694316 4464659 := bstep (se 1 (by rfl) ⟨3348494, by rfl⟩ : syracuseStep 4464659 = 6696989) B6696989
theorem B2826299 : Blo 694316 2826299 := bstep (se 1 (by rfl) ⟨2119724, by rfl⟩ : syracuseStep 2826299 = 4239449) B4239449
theorem B696607 : Blo 694316 696607 := bstep (se 1 (by rfl) ⟨522455, by rfl⟩ : syracuseStep 696607 = 1044911) B1044911
theorem B24387905 : Blo 694316 24387905 := bstep (se 2 (by rfl) ⟨9145464, by rfl⟩ : syracuseStep 24387905 = 18290929) B18290929
theorem B696667 : Blo 694316 696667 := bstep (se 1 (by rfl) ⟨522500, by rfl⟩ : syracuseStep 696667 = 1045001) B1045001
theorem B696687 : Blo 694316 696687 := bstep (se 1 (by rfl) ⟨522515, by rfl⟩ : syracuseStep 696687 = 1045031) B1045031
theorem B696743 : Blo 694316 696743 := bstep (se 1 (by rfl) ⟨522557, by rfl⟩ : syracuseStep 696743 = 1045115) B1045115
theorem B696827 : Blo 694316 696827 := bstep (se 1 (by rfl) ⟨522620, by rfl⟩ : syracuseStep 696827 = 1045241) B1045241
theorem B696895 : Blo 694316 696895 := bstep (se 1 (by rfl) ⟨522671, by rfl⟩ : syracuseStep 696895 = 1045343) B1045343
theorem B795199 : Blo 694316 795199 := bstep (se 1 (by rfl) ⟨596399, by rfl⟩ : syracuseStep 795199 = 1192799) B1192799
theorem B696903 : Blo 694316 696903 := bstep (se 1 (by rfl) ⟨522677, by rfl⟩ : syracuseStep 696903 = 1045355) B1045355
theorem B697055 : Blo 694316 697055 := bstep (se 1 (by rfl) ⟨522791, by rfl⟩ : syracuseStep 697055 = 1045583) B1045583
theorem B697135 : Blo 694316 697135 := bstep (se 1 (by rfl) ⟨522851, by rfl⟩ : syracuseStep 697135 = 1045703) B1045703
theorem B697243 : Blo 694316 697243 := bstep (se 1 (by rfl) ⟨522932, by rfl⟩ : syracuseStep 697243 = 1045865) B1045865
theorem B697295 : Blo 694316 697295 := bstep (se 1 (by rfl) ⟨522971, by rfl⟩ : syracuseStep 697295 = 1045943) B1045943
theorem B697319 : Blo 694316 697319 := bstep (se 1 (by rfl) ⟨522989, by rfl⟩ : syracuseStep 697319 = 1045979) B1045979
theorem B3515399 : Blo 694316 3515399 := bstep (se 1 (by rfl) ⟨2636549, by rfl⟩ : syracuseStep 3515399 = 5273099) B5273099
theorem B1254619 : Blo 694316 1254619 := bstep (se 1 (by rfl) ⟨940964, by rfl⟩ : syracuseStep 1254619 = 1881929) B1881929
theorem B697631 : Blo 694316 697631 := bstep (se 1 (by rfl) ⟨523223, by rfl⟩ : syracuseStep 697631 = 1046447) B1046447
theorem B697691 : Blo 694316 697691 := bstep (se 1 (by rfl) ⟨523268, by rfl⟩ : syracuseStep 697691 = 1046537) B1046537
theorem B697711 : Blo 694316 697711 := bstep (se 1 (by rfl) ⟨523283, by rfl⟩ : syracuseStep 697711 = 1046567) B1046567
theorem B697767 : Blo 694316 697767 := bstep (se 1 (by rfl) ⟨523325, by rfl⟩ : syracuseStep 697767 = 1046651) B1046651
theorem B3515885 : Blo 694316 3515885 := bstep (se 3 (by rfl) ⟨659228, by rfl⟩ : syracuseStep 3515885 = 1318457) B1318457
theorem B697851 : Blo 694316 697851 := bstep (se 1 (by rfl) ⟨523388, by rfl⟩ : syracuseStep 697851 = 1046777) B1046777
theorem B697919 : Blo 694316 697919 := bstep (se 1 (by rfl) ⟨523439, by rfl⟩ : syracuseStep 697919 = 1046879) B1046879
theorem B697927 : Blo 694316 697927 := bstep (se 1 (by rfl) ⟨523445, by rfl⟩ : syracuseStep 697927 = 1046891) B1046891
theorem B698079 : Blo 694316 698079 := bstep (se 1 (by rfl) ⟨523559, by rfl⟩ : syracuseStep 698079 = 1047119) B1047119
theorem B698159 : Blo 694316 698159 := bstep (se 1 (by rfl) ⟨523619, by rfl⟩ : syracuseStep 698159 = 1047239) B1047239
theorem B698267 : Blo 694316 698267 := bstep (se 1 (by rfl) ⟨523700, by rfl⟩ : syracuseStep 698267 = 1047401) B1047401
theorem B6367247 : Blo 694316 6367247 := bstep (se 1 (by rfl) ⟨4775435, by rfl⟩ : syracuseStep 6367247 = 9550871) B9550871
theorem B1484905 : Blo 694316 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B3516695 : Blo 694316 3516695 := bstep (se 1 (by rfl) ⟨2637521, by rfl⟩ : syracuseStep 3516695 = 5275043) B5275043
theorem B6695297 : Blo 694316 6695297 := bstep (se 2 (by rfl) ⟨2510736, by rfl⟩ : syracuseStep 6695297 = 5021473) B5021473
theorem B1321427 : Blo 694316 1321427 := bstep (se 1 (by rfl) ⟨991070, by rfl⟩ : syracuseStep 1321427 = 1982141) B1982141
theorem B1485307 : Blo 694316 1485307 := bstep (se 1 (by rfl) ⟨1113980, by rfl⟩ : syracuseStep 1485307 = 2227961) B2227961
theorem B1878599 : Blo 694316 1878599 := bstep (se 1 (by rfl) ⟨1408949, by rfl⟩ : syracuseStep 1878599 = 2817899) B2817899
theorem B1485383 : Blo 694316 1485383 := bstep (se 1 (by rfl) ⟨1114037, by rfl⟩ : syracuseStep 1485383 = 2228075) B2228075
theorem B20032373 : Blo 694316 20032373 := bstep (se 5 (by rfl) ⟨939017, by rfl⟩ : syracuseStep 20032373 = 1878035) B1878035
theorem B6335603 : Blo 694316 6335603 := bstep (se 1 (by rfl) ⟨4751702, by rfl⟩ : syracuseStep 6335603 = 9503405) B9503405
theorem B3353993 : Blo 694316 3353993 := bstep (se 2 (by rfl) ⟨1257747, by rfl⟩ : syracuseStep 3353993 = 2515495) B2515495
theorem B1060447 : Blo 694316 1060447 := bstep (se 1 (by rfl) ⟨795335, by rfl⟩ : syracuseStep 1060447 = 1590671) B1590671
theorem B3518315 : Blo 694316 3518315 := bstep (se 1 (by rfl) ⟨2638736, by rfl⟩ : syracuseStep 3518315 = 5277473) B5277473
theorem B2830547 : Blo 694316 2830547 := bstep (se 1 (by rfl) ⟨2122910, by rfl⟩ : syracuseStep 2830547 = 4245821) B4245821
theorem B1880393 : Blo 694316 1880393 := bstep (se 2 (by rfl) ⟨705147, by rfl⟩ : syracuseStep 1880393 = 1410295) B1410295
theorem B1487315 : Blo 694316 1487315 := bstep (se 1 (by rfl) ⟨1115486, by rfl⟩ : syracuseStep 1487315 = 2230973) B2230973
theorem B1323515 : Blo 694316 1323515 := bstep (se 1 (by rfl) ⟨992636, by rfl⟩ : syracuseStep 1323515 = 1985273) B1985273
theorem B1978951 : Blo 694316 1978951 := bstep (se 1 (by rfl) ⟨1484213, by rfl⟩ : syracuseStep 1978951 = 2968427) B2968427
theorem B2830969 : Blo 694316 2830969 := bstep (se 2 (by rfl) ⟨1061613, by rfl⟩ : syracuseStep 2830969 = 2123227) B2123227
theorem B1881227 : Blo 694316 1881227 := bstep (se 1 (by rfl) ⟨1410920, by rfl⟩ : syracuseStep 1881227 = 2821841) B2821841
theorem B1160585 : Blo 694316 1160585 := bstep (se 2 (by rfl) ⟨435219, by rfl⟩ : syracuseStep 1160585 = 870439) B870439
theorem B1324487 : Blo 694316 1324487 := bstep (se 1 (by rfl) ⟨993365, by rfl⟩ : syracuseStep 1324487 = 1986731) B1986731
theorem B4962637 : Blo 694316 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B1325641 : Blo 694316 1325641 := bstep (se 2 (by rfl) ⟨497115, by rfl⟩ : syracuseStep 1325641 = 994231) B994231
theorem B7519499 : Blo 694316 7519499 := bstep (se 1 (by rfl) ⟨5639624, by rfl⟩ : syracuseStep 7519499 = 11279249) B11279249
theorem B4767113 : Blo 694316 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B3522041 : Blo 694316 3522041 := bstep (se 2 (by rfl) ⟨1320765, by rfl⟩ : syracuseStep 3522041 = 2641531) B2641531
theorem B835067 : Blo 694316 835067 := bstep (se 1 (by rfl) ⟨626300, by rfl⟩ : syracuseStep 835067 = 1252601) B1252601
theorem B6700603 : Blo 694316 6700603 := bstep (se 1 (by rfl) ⟨5025452, by rfl⟩ : syracuseStep 6700603 = 10050905) B10050905
theorem B835375 : Blo 694316 835375 := bstep (se 1 (by rfl) ⟨626531, by rfl⟩ : syracuseStep 835375 = 1253063) B1253063
theorem B2637629 : Blo 694316 2637629 := bstep (se 3 (by rfl) ⟨494555, by rfl⟩ : syracuseStep 2637629 = 989111) B989111
theorem B3522365 : Blo 694316 3522365 := bstep (se 3 (by rfl) ⟨660443, by rfl⟩ : syracuseStep 3522365 = 1320887) B1320887
theorem B8470433 : Blo 694316 8470433 := bstep (se 2 (by rfl) ⟨3176412, by rfl⟩ : syracuseStep 8470433 = 6352825) B6352825
theorem B2966017 : Blo 694316 2966017 := bstep (se 2 (by rfl) ⟨1112256, by rfl⟩ : syracuseStep 2966017 = 2224513) B2224513
theorem B2343545 : Blo 694316 2343545 := bstep (se 2 (by rfl) ⟨878829, by rfl⟩ : syracuseStep 2343545 = 1757659) B1757659
theorem B1983199 : Blo 694316 1983199 := bstep (se 1 (by rfl) ⟨1487399, by rfl⟩ : syracuseStep 1983199 = 2974799) B2974799
theorem B6702371 : Blo 694316 6702371 := bstep (se 1 (by rfl) ⟨5026778, by rfl⟩ : syracuseStep 6702371 = 10053557) B10053557
theorem B7947557 : Blo 694316 7947557 := bstep (se 4 (by rfl) ⟨745083, by rfl⟩ : syracuseStep 7947557 = 1490167) B1490167
theorem B2868641 : Blo 694316 2868641 := bstep (se 2 (by rfl) ⟨1075740, by rfl⟩ : syracuseStep 2868641 = 2151481) B2151481
theorem B1885639 : Blo 694316 1885639 := bstep (se 1 (by rfl) ⟨1414229, by rfl⟩ : syracuseStep 1885639 = 2828459) B2828459
theorem B7161871 : Blo 694316 7161871 := bstep (se 1 (by rfl) ⟨5371403, by rfl⟩ : syracuseStep 7161871 = 10742807) B10742807
theorem B5949733 : Blo 694316 5949733 := bstep (se 4 (by rfl) ⟨557787, by rfl⟩ : syracuseStep 5949733 = 1115575) B1115575
theorem B2345327 : Blo 694316 2345327 := bstep (se 1 (by rfl) ⟨1758995, by rfl⟩ : syracuseStep 2345327 = 3517991) B3517991
theorem B2640559 : Blo 694316 2640559 := bstep (se 1 (by rfl) ⟨1980419, by rfl⟩ : syracuseStep 2640559 = 3960839) B3960839
theorem B1886903 : Blo 694316 1886903 := bstep (se 1 (by rfl) ⟨1415177, by rfl⟩ : syracuseStep 1886903 = 2830355) B2830355
theorem B3525443 : Blo 694316 3525443 := bstep (se 1 (by rfl) ⟨2644082, by rfl⟩ : syracuseStep 3525443 = 5288165) B5288165
theorem B2149595 : Blo 694316 2149595 := bstep (se 1 (by rfl) ⟨1612196, by rfl⟩ : syracuseStep 2149595 = 3224393) B3224393
theorem B5655905 : Blo 694316 5655905 := bstep (se 2 (by rfl) ⟨2120964, by rfl⟩ : syracuseStep 5655905 = 4241929) B4241929
theorem B2641517 : Blo 694316 2641517 := bstep (se 3 (by rfl) ⟨495284, by rfl⟩ : syracuseStep 2641517 = 990569) B990569
theorem B3526253 : Blo 694316 3526253 := bstep (se 3 (by rfl) ⟨661172, by rfl⟩ : syracuseStep 3526253 = 1322345) B1322345
theorem B2346731 : Blo 694316 2346731 := bstep (se 1 (by rfl) ⟨1760048, by rfl⟩ : syracuseStep 2346731 = 3520097) B3520097
theorem B33967937 : Blo 694316 33967937 := bstep (se 2 (by rfl) ⟨12737976, by rfl⟩ : syracuseStep 33967937 = 25475953) B25475953
theorem B8048605 : Blo 694316 8048605 := bstep (se 3 (by rfl) ⟨1509113, by rfl⟩ : syracuseStep 8048605 = 3018227) B3018227
theorem B2642503 : Blo 694316 2642503 := bstep (se 1 (by rfl) ⟨1981877, by rfl⟩ : syracuseStep 2642503 = 3963755) B3963755
theorem B2347703 : Blo 694316 2347703 := bstep (se 1 (by rfl) ⟨1760777, by rfl⟩ : syracuseStep 2347703 = 3521555) B3521555
theorem B1758095 : Blo 694316 1758095 := bstep (se 1 (by rfl) ⟨1318571, by rfl⟩ : syracuseStep 1758095 = 2637143) B2637143
theorem B20633221 : Blo 694316 20633221 := bstep (se 4 (by rfl) ⟨1934364, by rfl⟩ : syracuseStep 20633221 = 3868729) B3868729
theorem B1562273 : Blo 694316 1562273 := bstep (se 2 (by rfl) ⟨585852, by rfl⟩ : syracuseStep 1562273 = 1171705) B1171705
theorem B1758955 : Blo 694316 1758955 := bstep (se 1 (by rfl) ⟨1319216, by rfl⟩ : syracuseStep 1758955 = 2638433) B2638433
theorem B6019001 : Blo 694316 6019001 := bstep (se 2 (by rfl) ⟨2257125, by rfl⟩ : syracuseStep 6019001 = 4514251) B4514251
theorem B743375 : Blo 694316 743375 := bstep (se 1 (by rfl) ⟨557531, by rfl⟩ : syracuseStep 743375 = 1115063) B1115063
theorem B1562633 : Blo 694316 1562633 := bstep (se 2 (by rfl) ⟨585987, by rfl⟩ : syracuseStep 1562633 = 1171975) B1171975
theorem B6707447 : Blo 694316 6707447 := bstep (se 1 (by rfl) ⟨5030585, by rfl⟩ : syracuseStep 6707447 = 10061171) B10061171
theorem B1563047 : Blo 694316 1563047 := bstep (se 1 (by rfl) ⟨1172285, by rfl⟩ : syracuseStep 1563047 = 2344571) B2344571
theorem B1563155 : Blo 694316 1563155 := bstep (se 1 (by rfl) ⟨1172366, by rfl⟩ : syracuseStep 1563155 = 2344733) B2344733
theorem B11262503 : Blo 694316 11262503 := bstep (se 1 (by rfl) ⟨8446877, by rfl⟩ : syracuseStep 11262503 = 16893755) B16893755
theorem B5954107 : Blo 694316 5954107 := bstep (se 1 (by rfl) ⟨4465580, by rfl⟩ : syracuseStep 5954107 = 8931161) B8931161
theorem B1563209 : Blo 694316 1563209 := bstep (se 2 (by rfl) ⟨586203, by rfl⟩ : syracuseStep 1563209 = 1172407) B1172407
theorem B2349647 : Blo 694316 2349647 := bstep (se 1 (by rfl) ⟨1762235, by rfl⟩ : syracuseStep 2349647 = 3524471) B3524471
theorem B1759927 : Blo 694316 1759927 := bstep (se 1 (by rfl) ⟨1319945, by rfl⟩ : syracuseStep 1759927 = 2639891) B2639891
theorem B7527107 : Blo 694316 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B8575931 : Blo 694316 8575931 := bstep (se 1 (by rfl) ⟨6431948, by rfl⟩ : syracuseStep 8575931 = 12863897) B12863897
theorem B1563623 : Blo 694316 1563623 := bstep (se 1 (by rfl) ⟨1172717, by rfl⟩ : syracuseStep 1563623 = 2345435) B2345435
theorem B1760231 : Blo 694316 1760231 := bstep (se 1 (by rfl) ⟨1320173, by rfl⟩ : syracuseStep 1760231 = 2640347) B2640347
theorem B1564001 : Blo 694316 1564001 := bstep (se 2 (by rfl) ⟨586500, by rfl⟩ : syracuseStep 1564001 = 1173001) B1173001
theorem B1564091 : Blo 694316 1564091 := bstep (se 1 (by rfl) ⟨1173068, by rfl⟩ : syracuseStep 1564091 = 2346137) B2346137
theorem B5955065 : Blo 694316 5955065 := bstep (se 2 (by rfl) ⟨2233149, by rfl⟩ : syracuseStep 5955065 = 4466299) B4466299
theorem B1564217 : Blo 694316 1564217 := bstep (se 2 (by rfl) ⟨586581, by rfl⟩ : syracuseStep 1564217 = 1173163) B1173163
theorem B7921313 : Blo 694316 7921313 := bstep (se 2 (by rfl) ⟨2970492, by rfl⟩ : syracuseStep 7921313 = 5940985) B5940985
theorem B941743 : Blo 694316 941743 := bstep (se 1 (by rfl) ⟨706307, by rfl⟩ : syracuseStep 941743 = 1412615) B1412615
theorem B1269545 : Blo 694316 1269545 := bstep (se 2 (by rfl) ⟨476079, by rfl⟩ : syracuseStep 1269545 = 952159) B952159
theorem B2350889 : Blo 694316 2350889 := bstep (se 2 (by rfl) ⟨881583, by rfl⟩ : syracuseStep 2350889 = 1763167) B1763167
theorem B101638091 : Blo 694316 101638091 := bstep (se 1 (by rfl) ⟨76228568, by rfl⟩ : syracuseStep 101638091 = 152457137) B152457137
theorem B8708147 : Blo 694316 8708147 := bstep (se 1 (by rfl) ⟨6531110, by rfl⟩ : syracuseStep 8708147 = 13062221) B13062221
theorem B1761385 : Blo 694316 1761385 := bstep (se 2 (by rfl) ⟨660519, by rfl⟩ : syracuseStep 1761385 = 1321039) B1321039
theorem B1564883 : Blo 694316 1564883 := bstep (se 1 (by rfl) ⟨1173662, by rfl⟩ : syracuseStep 1564883 = 2347325) B2347325
theorem B1564937 : Blo 694316 1564937 := bstep (se 2 (by rfl) ⟨586851, by rfl⟩ : syracuseStep 1564937 = 1173703) B1173703
theorem B1565153 : Blo 694316 1565153 := bstep (se 2 (by rfl) ⟨586932, by rfl⟩ : syracuseStep 1565153 = 1173865) B1173865
theorem B1761871 : Blo 694316 1761871 := bstep (se 1 (by rfl) ⟨1321403, by rfl⟩ : syracuseStep 1761871 = 2642807) B2642807
theorem B4448951 : Blo 694316 4448951 := bstep (se 1 (by rfl) ⟨3336713, by rfl⟩ : syracuseStep 4448951 = 6673427) B6673427
theorem B1172191 : Blo 694316 1172191 := bstep (se 1 (by rfl) ⟨879143, by rfl⟩ : syracuseStep 1172191 = 1758287) B1758287
theorem B2974457 : Blo 694316 2974457 := bstep (se 2 (by rfl) ⟨1115421, by rfl⟩ : syracuseStep 2974457 = 2230843) B2230843
theorem B1565459 : Blo 694316 1565459 := bstep (se 1 (by rfl) ⟨1174094, by rfl⟩ : syracuseStep 1565459 = 2348189) B2348189
theorem B2646863 : Blo 694316 2646863 := bstep (se 1 (by rfl) ⟨1985147, by rfl⟩ : syracuseStep 2646863 = 3970295) B3970295
theorem B3531599 : Blo 694316 3531599 := bstep (se 1 (by rfl) ⟨2648699, by rfl⟩ : syracuseStep 3531599 = 5297399) B5297399
theorem B4842499 : Blo 694316 4842499 := bstep (se 1 (by rfl) ⟨3631874, by rfl⟩ : syracuseStep 4842499 = 7263749) B7263749
theorem B22602851 : Blo 694316 22602851 := bstep (se 1 (by rfl) ⟨16952138, by rfl⟩ : syracuseStep 22602851 = 33904277) B33904277
theorem B1565819 : Blo 694316 1565819 := bstep (se 1 (by rfl) ⟨1174364, by rfl⟩ : syracuseStep 1565819 = 2348729) B2348729
theorem B1172623 : Blo 694316 1172623 := bstep (se 1 (by rfl) ⟨879467, by rfl⟩ : syracuseStep 1172623 = 1758935) B1758935
theorem B3531923 : Blo 694316 3531923 := bstep (se 1 (by rfl) ⟨2648942, by rfl⟩ : syracuseStep 3531923 = 5297885) B5297885
theorem B1762519 : Blo 694316 1762519 := bstep (se 1 (by rfl) ⟨1321889, by rfl⟩ : syracuseStep 1762519 = 2643779) B2643779
theorem B1041641 : Blo 694316 1041641 := bstep (se 2 (by rfl) ⟨390615, by rfl⟩ : syracuseStep 1041641 = 781231) B781231
theorem B5956841 : Blo 694316 5956841 := bstep (se 2 (by rfl) ⟨2233815, by rfl⟩ : syracuseStep 5956841 = 4467631) B4467631
theorem B1565945 : Blo 694316 1565945 := bstep (se 2 (by rfl) ⟨587229, by rfl⟩ : syracuseStep 1565945 = 1174459) B1174459
theorem B1041695 : Blo 694316 1041695 := bstep (se 1 (by rfl) ⟨781271, by rfl⟩ : syracuseStep 1041695 = 1562543) B1562543
theorem B1172873 : Blo 694316 1172873 := bstep (se 2 (by rfl) ⟨439827, by rfl⟩ : syracuseStep 1172873 = 879655) B879655
theorem B1566089 : Blo 694316 1566089 := bstep (se 2 (by rfl) ⟨587283, by rfl⟩ : syracuseStep 1566089 = 1174567) B1174567
theorem B1041863 : Blo 694316 1041863 := bstep (se 1 (by rfl) ⟨781397, by rfl⟩ : syracuseStep 1041863 = 1562795) B1562795
theorem B1566215 : Blo 694316 1566215 := bstep (se 1 (by rfl) ⟨1174661, by rfl⟩ : syracuseStep 1566215 = 2349323) B2349323
theorem B1762823 : Blo 694316 1762823 := bstep (se 1 (by rfl) ⟨1322117, by rfl⟩ : syracuseStep 1762823 = 2644235) B2644235
theorem B1566395 : Blo 694316 1566395 := bstep (se 1 (by rfl) ⟨1174796, by rfl⟩ : syracuseStep 1566395 = 2349593) B2349593
theorem B1042217 : Blo 694316 1042217 := bstep (se 2 (by rfl) ⟨390831, by rfl⟩ : syracuseStep 1042217 = 781663) B781663
theorem B1042223 : Blo 694316 1042223 := bstep (se 1 (by rfl) ⟨781667, by rfl⟩ : syracuseStep 1042223 = 1563335) B1563335
theorem B1173305 : Blo 694316 1173305 := bstep (se 2 (by rfl) ⟨439989, by rfl⟩ : syracuseStep 1173305 = 879979) B879979
theorem B1566521 : Blo 694316 1566521 := bstep (se 2 (by rfl) ⟨587445, by rfl⟩ : syracuseStep 1566521 = 1174891) B1174891
theorem B11888531 : Blo 694316 11888531 := bstep (se 1 (by rfl) ⟨8916398, by rfl⟩ : syracuseStep 11888531 = 17832797) B17832797
theorem B1763279 : Blo 694316 1763279 := bstep (se 1 (by rfl) ⟨1322459, by rfl⟩ : syracuseStep 1763279 = 2644919) B2644919
theorem B2353103 : Blo 694316 2353103 := bstep (se 1 (by rfl) ⟨1764827, by rfl⟩ : syracuseStep 2353103 = 3529655) B3529655
theorem B1042697 : Blo 694316 1042697 := bstep (se 2 (by rfl) ⟨391011, by rfl⟩ : syracuseStep 1042697 = 782023) B782023
theorem B1042799 : Blo 694316 1042799 := bstep (se 1 (by rfl) ⟨782099, by rfl⟩ : syracuseStep 1042799 = 1564199) B1564199
theorem B1567151 : Blo 694316 1567151 := bstep (se 1 (by rfl) ⟨1175363, by rfl⟩ : syracuseStep 1567151 = 2350727) B2350727
theorem B1567187 : Blo 694316 1567187 := bstep (se 1 (by rfl) ⟨1175390, by rfl⟩ : syracuseStep 1567187 = 2350781) B2350781
theorem B1763795 : Blo 694316 1763795 := bstep (se 1 (by rfl) ⟨1322846, by rfl⟩ : syracuseStep 1763795 = 2645693) B2645693
theorem B1567295 : Blo 694316 1567295 := bstep (se 1 (by rfl) ⟨1175471, by rfl⟩ : syracuseStep 1567295 = 2350943) B2350943
theorem B2648639 : Blo 694316 2648639 := bstep (se 1 (by rfl) ⟨1986479, by rfl⟩ : syracuseStep 2648639 = 3972959) B3972959
theorem B1043015 : Blo 694316 1043015 := bstep (se 1 (by rfl) ⟨782261, by rfl⟩ : syracuseStep 1043015 = 1564523) B1564523
theorem B1043051 : Blo 694316 1043051 := bstep (se 1 (by rfl) ⟨782288, by rfl⟩ : syracuseStep 1043051 = 1564577) B1564577
theorem B1567403 : Blo 694316 1567403 := bstep (se 1 (by rfl) ⟨1175552, by rfl⟩ : syracuseStep 1567403 = 2351105) B2351105
theorem B1043279 : Blo 694316 1043279 := bstep (se 1 (by rfl) ⟨782459, by rfl⟩ : syracuseStep 1043279 = 1564919) B1564919
theorem B1174351 : Blo 694316 1174351 := bstep (se 1 (by rfl) ⟨880763, by rfl⟩ : syracuseStep 1174351 = 1761527) B1761527
theorem B1764251 : Blo 694316 1764251 := bstep (se 1 (by rfl) ⟨1323188, by rfl⟩ : syracuseStep 1764251 = 2646377) B2646377
theorem B2354075 : Blo 694316 2354075 := bstep (se 1 (by rfl) ⟨1765556, by rfl⟩ : syracuseStep 2354075 = 3531113) B3531113
theorem B7334993 : Blo 694316 7334993 := bstep (se 2 (by rfl) ⟨2750622, by rfl⟩ : syracuseStep 7334993 = 5501245) B5501245
theorem B6679691 : Blo 694316 6679691 := bstep (se 1 (by rfl) ⟨5009768, by rfl⟩ : syracuseStep 6679691 = 10019537) B10019537
theorem B1567943 : Blo 694316 1567943 := bstep (se 1 (by rfl) ⟨1175957, by rfl⟩ : syracuseStep 1567943 = 2351915) B2351915
theorem B1043675 : Blo 694316 1043675 := bstep (se 1 (by rfl) ⟨782756, by rfl⟩ : syracuseStep 1043675 = 1565513) B1565513
theorem B2649307 : Blo 694316 2649307 := bstep (se 1 (by rfl) ⟨1986980, by rfl⟩ : syracuseStep 2649307 = 3973961) B3973961
theorem B3337483 : Blo 694316 3337483 := bstep (se 1 (by rfl) ⟨2503112, by rfl⟩ : syracuseStep 3337483 = 5006225) B5006225
theorem B24177953 : Blo 694316 24177953 := bstep (se 2 (by rfl) ⟨9066732, by rfl⟩ : syracuseStep 24177953 = 18133465) B18133465
theorem B1568123 : Blo 694316 1568123 := bstep (se 1 (by rfl) ⟨1176092, by rfl⟩ : syracuseStep 1568123 = 2352185) B2352185
theorem B1043849 : Blo 694316 1043849 := bstep (se 2 (by rfl) ⟨391443, by rfl⟩ : syracuseStep 1043849 = 782887) B782887
theorem B781735 : Blo 694316 781735 := bstep (se 1 (by rfl) ⟨586301, by rfl⟩ : syracuseStep 781735 = 1172603) B1172603
theorem B1175033 : Blo 694316 1175033 := bstep (se 2 (by rfl) ⟨440637, by rfl⟩ : syracuseStep 1175033 = 881275) B881275
theorem B1568249 : Blo 694316 1568249 := bstep (se 2 (by rfl) ⟨588093, by rfl⟩ : syracuseStep 1568249 = 1176187) B1176187
theorem B1568339 : Blo 694316 1568339 := bstep (se 1 (by rfl) ⟨1176254, by rfl⟩ : syracuseStep 1568339 = 2352509) B2352509
theorem B880303 : Blo 694316 880303 := bstep (se 1 (by rfl) ⟨660227, by rfl⟩ : syracuseStep 880303 = 1320455) B1320455
theorem B1044203 : Blo 694316 1044203 := bstep (se 1 (by rfl) ⟨783152, by rfl⟩ : syracuseStep 1044203 = 1566305) B1566305
theorem B1175303 : Blo 694316 1175303 := bstep (se 1 (by rfl) ⟨881477, by rfl⟩ : syracuseStep 1175303 = 1762955) B1762955
theorem B1568519 : Blo 694316 1568519 := bstep (se 1 (by rfl) ⟨1176389, by rfl⟩ : syracuseStep 1568519 = 2352779) B2352779
theorem B3764029 : Blo 694316 3764029 := bstep (se 3 (by rfl) ⟨705755, by rfl⟩ : syracuseStep 3764029 = 1411511) B1411511
theorem B5009309 : Blo 694316 5009309 := bstep (se 3 (by rfl) ⟨939245, by rfl⟩ : syracuseStep 5009309 = 1878491) B1878491
theorem B2355101 : Blo 694316 2355101 := bstep (se 3 (by rfl) ⟨441581, by rfl⟩ : syracuseStep 2355101 = 883163) B883163
theorem B9531341 : Blo 694316 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B1044431 : Blo 694316 1044431 := bstep (se 1 (by rfl) ⟨783323, by rfl⟩ : syracuseStep 1044431 = 1566647) B1566647
theorem B782311 : Blo 694316 782311 := bstep (se 1 (by rfl) ⟨586733, by rfl⟩ : syracuseStep 782311 = 1173467) B1173467
theorem B1765385 : Blo 694316 1765385 := bstep (se 2 (by rfl) ⟨662019, by rfl⟩ : syracuseStep 1765385 = 1324039) B1324039
theorem B2355209 : Blo 694316 2355209 := bstep (se 2 (by rfl) ⟨883203, by rfl⟩ : syracuseStep 2355209 = 1766407) B1766407
theorem B3567635 : Blo 694316 3567635 := bstep (se 1 (by rfl) ⟨2675726, by rfl⟩ : syracuseStep 3567635 = 5351453) B5351453
theorem B11923523 : Blo 694316 11923523 := bstep (se 1 (by rfl) ⟨8942642, by rfl⟩ : syracuseStep 11923523 = 17885285) B17885285
theorem B3535001 : Blo 694316 3535001 := bstep (se 2 (by rfl) ⟨1325625, by rfl⟩ : syracuseStep 3535001 = 2651251) B2651251
theorem B1044827 : Blo 694316 1044827 := bstep (se 1 (by rfl) ⟨783620, by rfl⟩ : syracuseStep 1044827 = 1567241) B1567241
theorem B1569131 : Blo 694316 1569131 := bstep (se 1 (by rfl) ⟨1176848, by rfl⟩ : syracuseStep 1569131 = 2353697) B2353697
theorem B1765739 : Blo 694316 1765739 := bstep (se 1 (by rfl) ⟨1324304, by rfl⟩ : syracuseStep 1765739 = 2648609) B2648609
theorem B1176059 : Blo 694316 1176059 := bstep (se 1 (by rfl) ⟨882044, by rfl⟩ : syracuseStep 1176059 = 1764089) B1764089
theorem B1569275 : Blo 694316 1569275 := bstep (se 1 (by rfl) ⟨1176956, by rfl⟩ : syracuseStep 1569275 = 2353913) B2353913
theorem B5009939 : Blo 694316 5009939 := bstep (se 1 (by rfl) ⟨3757454, by rfl⟩ : syracuseStep 5009939 = 7514909) B7514909
theorem B6681149 : Blo 694316 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B1045055 : Blo 694316 1045055 := bstep (se 1 (by rfl) ⟨783791, by rfl⟩ : syracuseStep 1045055 = 1567583) B1567583
theorem B1340011 : Blo 694316 1340011 := bstep (se 1 (by rfl) ⟨1005008, by rfl⟩ : syracuseStep 1340011 = 2010017) B2010017
theorem B1471097 : Blo 694316 1471097 := bstep (se 2 (by rfl) ⟨551661, by rfl⟩ : syracuseStep 1471097 = 1103323) B1103323
theorem B1569401 : Blo 694316 1569401 := bstep (se 2 (by rfl) ⟨588525, by rfl⟩ : syracuseStep 1569401 = 1177051) B1177051
theorem B25457273 : Blo 694316 25457273 := bstep (se 2 (by rfl) ⟨9546477, by rfl⟩ : syracuseStep 25457273 = 19092955) B19092955
theorem B1569455 : Blo 694316 1569455 := bstep (se 1 (by rfl) ⟨1177091, by rfl⟩ : syracuseStep 1569455 = 2354183) B2354183
theorem B1766063 : Blo 694316 1766063 := bstep (se 1 (by rfl) ⟨1324547, by rfl⟩ : syracuseStep 1766063 = 2649095) B2649095
theorem B1045175 : Blo 694316 1045175 := bstep (se 1 (by rfl) ⟨783881, by rfl⟩ : syracuseStep 1045175 = 1567763) B1567763
theorem B1569527 : Blo 694316 1569527 := bstep (se 1 (by rfl) ⟨1177145, by rfl⟩ : syracuseStep 1569527 = 2354291) B2354291
theorem B1045403 : Blo 694316 1045403 := bstep (se 1 (by rfl) ⟨784052, by rfl⟩ : syracuseStep 1045403 = 1568105) B1568105
theorem B1176491 : Blo 694316 1176491 := bstep (se 1 (by rfl) ⟨882368, by rfl⟩ : syracuseStep 1176491 = 1764737) B1764737
theorem B1569707 : Blo 694316 1569707 := bstep (se 1 (by rfl) ⟨1177280, by rfl⟩ : syracuseStep 1569707 = 2354561) B2354561
theorem B1766387 : Blo 694316 1766387 := bstep (se 1 (by rfl) ⟨1324790, by rfl⟩ : syracuseStep 1766387 = 2649581) B2649581
theorem B5075959 : Blo 694316 5075959 := bstep (se 1 (by rfl) ⟨3806969, by rfl⟩ : syracuseStep 5075959 = 7613939) B7613939
theorem B2815175 : Blo 694316 2815175 := bstep (se 1 (by rfl) ⟨2111381, by rfl⟩ : syracuseStep 2815175 = 4222763) B4222763
theorem B2684137 : Blo 694316 2684137 := bstep (se 2 (by rfl) ⟨1006551, by rfl⟩ : syracuseStep 2684137 = 2013103) B2013103
theorem B1045799 : Blo 694316 1045799 := bstep (se 1 (by rfl) ⟨784349, by rfl⟩ : syracuseStep 1045799 = 1568699) B1568699
theorem B2258219 : Blo 694316 2258219 := bstep (se 1 (by rfl) ⟨1693664, by rfl⟩ : syracuseStep 2258219 = 3387329) B3387329
theorem B1045883 : Blo 694316 1045883 := bstep (se 1 (by rfl) ⟨784412, by rfl⟩ : syracuseStep 1045883 = 1568825) B1568825
theorem B1668539 : Blo 694316 1668539 := bstep (se 1 (by rfl) ⟨1251404, by rfl⟩ : syracuseStep 1668539 = 2502809) B2502809
theorem B1766843 : Blo 694316 1766843 := bstep (se 1 (by rfl) ⟨1325132, by rfl⟩ : syracuseStep 1766843 = 2650265) B2650265
theorem B1177031 : Blo 694316 1177031 := bstep (se 1 (by rfl) ⟨882773, by rfl⟩ : syracuseStep 1177031 = 1765547) B1765547
theorem B1570247 : Blo 694316 1570247 := bstep (se 1 (by rfl) ⟨1177685, by rfl⟩ : syracuseStep 1570247 = 2355371) B2355371
theorem B1046009 : Blo 694316 1046009 := bstep (se 2 (by rfl) ⟨392253, by rfl⟩ : syracuseStep 1046009 = 784507) B784507
theorem B882247 : Blo 694316 882247 := bstep (se 1 (by rfl) ⟨661685, by rfl⟩ : syracuseStep 882247 = 1323371) B1323371
theorem B783967 : Blo 694316 783967 := bstep (se 1 (by rfl) ⟨587975, by rfl⟩ : syracuseStep 783967 = 1175951) B1175951
theorem B1046111 : Blo 694316 1046111 := bstep (se 1 (by rfl) ⟨784583, by rfl⟩ : syracuseStep 1046111 = 1569167) B1569167
theorem B1570607 : Blo 694316 1570607 := bstep (se 1 (by rfl) ⟨1177955, by rfl⟩ : syracuseStep 1570607 = 2355911) B2355911
theorem B1046327 : Blo 694316 1046327 := bstep (se 1 (by rfl) ⟨784745, by rfl⟩ : syracuseStep 1046327 = 1569491) B1569491
theorem B2815951 : Blo 694316 2815951 := bstep (se 1 (by rfl) ⟨2111963, by rfl⟩ : syracuseStep 2815951 = 4223927) B4223927
theorem B1046633 : Blo 694316 1046633 := bstep (se 2 (by rfl) ⟨392487, by rfl⟩ : syracuseStep 1046633 = 784975) B784975
theorem B1571183 : Blo 694316 1571183 := bstep (se 1 (by rfl) ⟨1178387, by rfl⟩ : syracuseStep 1571183 = 2356775) B2356775
theorem B1046951 : Blo 694316 1046951 := bstep (se 1 (by rfl) ⟨785213, by rfl⟩ : syracuseStep 1046951 = 1570427) B1570427
theorem B1178023 : Blo 694316 1178023 := bstep (se 1 (by rfl) ⟨883517, by rfl⟩ : syracuseStep 1178023 = 1767035) B1767035
theorem B1047035 : Blo 694316 1047035 := bstep (se 1 (by rfl) ⟨785276, by rfl⟩ : syracuseStep 1047035 = 1570553) B1570553
theorem B1178185 : Blo 694316 1178185 := bstep (se 2 (by rfl) ⟨441819, by rfl⟩ : syracuseStep 1178185 = 883639) B883639
theorem B1178219 : Blo 694316 1178219 := bstep (se 1 (by rfl) ⟨883664, by rfl⟩ : syracuseStep 1178219 = 1767329) B1767329
theorem B1047161 : Blo 694316 1047161 := bstep (se 2 (by rfl) ⟨392685, by rfl⟩ : syracuseStep 1047161 = 785371) B785371
theorem B1047215 : Blo 694316 1047215 := bstep (se 1 (by rfl) ⟨785411, by rfl⟩ : syracuseStep 1047215 = 1570823) B1570823
theorem B785119 : Blo 694316 785119 := bstep (se 1 (by rfl) ⟨588839, by rfl⟩ : syracuseStep 785119 = 1177679) B1177679
theorem B1047263 : Blo 694316 1047263 := bstep (se 1 (by rfl) ⟨785447, by rfl⟩ : syracuseStep 1047263 = 1570895) B1570895
theorem B3013519 : Blo 694316 3013519 := bstep (se 1 (by rfl) ⟨2260139, by rfl⟩ : syracuseStep 3013519 = 4520279) B4520279
theorem B1112987 : Blo 694316 1112987 := bstep (se 1 (by rfl) ⟨834740, by rfl⟩ : syracuseStep 1112987 = 1669481) B1669481
theorem B15465485 : Blo 694316 15465485 := bstep (se 3 (by rfl) ⟨2899778, by rfl⟩ : syracuseStep 15465485 = 5799557) B5799557
theorem B1670663 : Blo 694316 1670663 := bstep (se 1 (by rfl) ⟨1252997, by rfl⟩ : syracuseStep 1670663 = 2505995) B2505995
theorem B16055819 : Blo 694316 16055819 := bstep (se 1 (by rfl) ⟨12041864, by rfl⟩ : syracuseStep 16055819 = 24083729) B24083729
theorem B7241567 : Blo 694316 7241567 := bstep (se 1 (by rfl) ⟨5431175, by rfl⟩ : syracuseStep 7241567 = 10862351) B10862351
theorem B7536797 : Blo 694316 7536797 := bstep (se 3 (by rfl) ⟨1413149, by rfl⟩ : syracuseStep 7536797 = 2826299) B2826299
theorem B6423079 : Blo 694316 6423079 := bstep (se 1 (by rfl) ⟨4817309, by rfl⟩ : syracuseStep 6423079 = 9634619) B9634619
theorem B2229049 : Blo 694316 2229049 := bstep (se 2 (by rfl) ⟨835893, by rfl⟩ : syracuseStep 2229049 = 1671787) B1671787
theorem B5014381 : Blo 694316 5014381 := bstep (se 3 (by rfl) ⟨940196, by rfl⟩ : syracuseStep 5014381 = 1880393) B1880393
theorem B2229203 : Blo 694316 2229203 := bstep (se 1 (by rfl) ⟨1671902, by rfl⟩ : syracuseStep 2229203 = 3343805) B3343805
theorem B6456665 : Blo 694316 6456665 := bstep (se 2 (by rfl) ⟨2421249, by rfl⟩ : syracuseStep 6456665 = 4842499) B4842499
theorem B3343787 : Blo 694316 3343787 := bstep (se 1 (by rfl) ⟨2507840, by rfl⟩ : syracuseStep 3343787 = 5015681) B5015681
theorem B6096343 : Blo 694316 6096343 := bstep (se 1 (by rfl) ⟨4572257, by rfl⟩ : syracuseStep 6096343 = 9144515) B9144515
theorem B1508975 : Blo 694316 1508975 := bstep (se 1 (by rfl) ⟨1131731, by rfl⟩ : syracuseStep 1508975 = 2263463) B2263463
theorem B1672825 : Blo 694316 1672825 := bstep (se 2 (by rfl) ⟨627309, by rfl⟩ : syracuseStep 1672825 = 1254619) B1254619
theorem B2230217 : Blo 694316 2230217 := bstep (se 2 (by rfl) ⟨836331, by rfl⟩ : syracuseStep 2230217 = 1672663) B1672663
theorem B3770603 : Blo 694316 3770603 := bstep (se 1 (by rfl) ⟨2827952, by rfl⟩ : syracuseStep 3770603 = 5655905) B5655905
theorem B1116703 : Blo 694316 1116703 := bstep (se 1 (by rfl) ⟨837527, by rfl⟩ : syracuseStep 1116703 = 1675055) B1675055
theorem B22645291 : Blo 694316 22645291 := bstep (se 1 (by rfl) ⟨16983968, by rfl⟩ : syracuseStep 22645291 = 33967937) B33967937
theorem B7932977 : Blo 694316 7932977 := bstep (se 2 (by rfl) ⟨2974866, by rfl⟩ : syracuseStep 7932977 = 5949733) B5949733
theorem B1413929 : Blo 694316 1413929 := bstep (se 2 (by rfl) ⟨530223, by rfl⟩ : syracuseStep 1413929 = 1060447) B1060447
theorem B3970043 : Blo 694316 3970043 := bstep (se 1 (by rfl) ⟨2977532, by rfl⟩ : syracuseStep 3970043 = 5955065) B5955065
theorem B8918039 : Blo 694316 8918039 := bstep (se 1 (by rfl) ⟨6688529, by rfl⟩ : syracuseStep 8918039 = 13377059) B13377059
theorem B5018705 : Blo 694316 5018705 := bstep (se 2 (by rfl) ⟨1882014, by rfl⟩ : syracuseStep 5018705 = 3764029) B3764029
theorem B5280875 : Blo 694316 5280875 := bstep (se 1 (by rfl) ⟨3960656, by rfl⟩ : syracuseStep 5280875 = 7921313) B7921313
theorem B5805431 : Blo 694316 5805431 := bstep (se 1 (by rfl) ⟨4354073, by rfl⟩ : syracuseStep 5805431 = 8708147) B8708147
theorem B16258603 : Blo 694316 16258603 := bstep (se 1 (by rfl) ⟨12193952, by rfl⟩ : syracuseStep 16258603 = 24387905) B24387905
theorem B694427 : Blo 694316 694427 := bstep (se 1 (by rfl) ⟨520820, by rfl⟩ : syracuseStep 694427 = 1041641) B1041641
theorem B3971227 : Blo 694316 3971227 := bstep (se 1 (by rfl) ⟨2978420, by rfl⟩ : syracuseStep 3971227 = 5956841) B5956841
theorem B694463 : Blo 694316 694463 := bstep (se 1 (by rfl) ⟨520847, by rfl⟩ : syracuseStep 694463 = 1041695) B1041695
theorem B694575 : Blo 694316 694575 := bstep (se 1 (by rfl) ⟨520931, by rfl⟩ : syracuseStep 694575 = 1041863) B1041863
theorem B694811 : Blo 694316 694811 := bstep (se 1 (by rfl) ⟨521108, by rfl⟩ : syracuseStep 694811 = 1042217) B1042217
theorem B694815 : Blo 694316 694815 := bstep (se 1 (by rfl) ⟨521111, by rfl⟩ : syracuseStep 694815 = 1042223) B1042223
theorem B695131 : Blo 694316 695131 := bstep (se 1 (by rfl) ⟨521348, by rfl⟩ : syracuseStep 695131 = 1042697) B1042697
theorem B695199 : Blo 694316 695199 := bstep (se 1 (by rfl) ⟨521399, by rfl⟩ : syracuseStep 695199 = 1042799) B1042799
theorem B4463531 : Blo 694316 4463531 := bstep (se 1 (by rfl) ⟨3347648, by rfl⟩ : syracuseStep 4463531 = 6695297) B6695297
theorem B4463585 : Blo 694316 4463585 := bstep (se 2 (by rfl) ⟨1673844, by rfl⟩ : syracuseStep 4463585 = 3347689) B3347689
theorem B3578849 : Blo 694316 3578849 := bstep (se 2 (by rfl) ⟨1342068, by rfl⟩ : syracuseStep 3578849 = 2684137) B2684137
theorem B695343 : Blo 694316 695343 := bstep (se 1 (by rfl) ⟨521507, by rfl⟩ : syracuseStep 695343 = 1043015) B1043015
theorem B695367 : Blo 694316 695367 := bstep (se 1 (by rfl) ⟨521525, by rfl⟩ : syracuseStep 695367 = 1043051) B1043051
theorem B695519 : Blo 694316 695519 := bstep (se 1 (by rfl) ⟨521639, by rfl⟩ : syracuseStep 695519 = 1043279) B1043279
theorem B695783 : Blo 694316 695783 := bstep (se 1 (by rfl) ⟨521837, by rfl⟩ : syracuseStep 695783 = 1043675) B1043675
theorem B695899 : Blo 694316 695899 := bstep (se 1 (by rfl) ⟨521924, by rfl⟩ : syracuseStep 695899 = 1043849) B1043849
theorem B2235995 : Blo 694316 2235995 := bstep (se 1 (by rfl) ⟨1676996, by rfl⟩ : syracuseStep 2235995 = 3353993) B3353993
theorem B696135 : Blo 694316 696135 := bstep (se 1 (by rfl) ⟨522101, by rfl⟩ : syracuseStep 696135 = 1044203) B1044203
theorem B696287 : Blo 694316 696287 := bstep (se 1 (by rfl) ⟨522215, by rfl⟩ : syracuseStep 696287 = 1044431) B1044431
theorem B696551 : Blo 694316 696551 := bstep (se 1 (by rfl) ⟨522413, by rfl⟩ : syracuseStep 696551 = 1044827) B1044827
theorem B991543 : Blo 694316 991543 := bstep (se 1 (by rfl) ⟨743657, by rfl⟩ : syracuseStep 991543 = 1487315) B1487315
theorem B696703 : Blo 694316 696703 := bstep (se 1 (by rfl) ⟨522527, by rfl⟩ : syracuseStep 696703 = 1045055) B1045055
theorem B13541813 : Blo 694316 13541813 := bstep (se 5 (by rfl) ⟨634772, by rfl⟩ : syracuseStep 13541813 = 1269545) B1269545
theorem B696783 : Blo 694316 696783 := bstep (se 1 (by rfl) ⟨522587, by rfl⟩ : syracuseStep 696783 = 1045175) B1045175
theorem B696935 : Blo 694316 696935 := bstep (se 1 (by rfl) ⟨522701, by rfl⟩ : syracuseStep 696935 = 1045403) B1045403
theorem B7938809 : Blo 694316 7938809 := bstep (se 2 (by rfl) ⟨2977053, by rfl⟩ : syracuseStep 7938809 = 5954107) B5954107
theorem B1254151 : Blo 694316 1254151 := bstep (se 1 (by rfl) ⟨940613, by rfl⟩ : syracuseStep 1254151 = 1881227) B1881227
theorem B1876783 : Blo 694316 1876783 := bstep (se 1 (by rfl) ⟨1407587, by rfl⟩ : syracuseStep 1876783 = 2815175) B2815175
theorem B697199 : Blo 694316 697199 := bstep (se 1 (by rfl) ⟨522899, by rfl⟩ : syracuseStep 697199 = 1045799) B1045799
theorem B697255 : Blo 694316 697255 := bstep (se 1 (by rfl) ⟨522941, by rfl⟩ : syracuseStep 697255 = 1045883) B1045883
theorem B697339 : Blo 694316 697339 := bstep (se 1 (by rfl) ⟨523004, by rfl⟩ : syracuseStep 697339 = 1046009) B1046009
theorem B697407 : Blo 694316 697407 := bstep (se 1 (by rfl) ⟨523055, by rfl⟩ : syracuseStep 697407 = 1046111) B1046111
theorem B697551 : Blo 694316 697551 := bstep (se 1 (by rfl) ⟨523163, by rfl⟩ : syracuseStep 697551 = 1046327) B1046327
theorem B697755 : Blo 694316 697755 := bstep (se 1 (by rfl) ⟨523316, by rfl⟩ : syracuseStep 697755 = 1046633) B1046633
theorem B697967 : Blo 694316 697967 := bstep (se 1 (by rfl) ⟨523475, by rfl⟩ : syracuseStep 697967 = 1046951) B1046951
theorem B698023 : Blo 694316 698023 := bstep (se 1 (by rfl) ⟨523517, by rfl⟩ : syracuseStep 698023 = 1047035) B1047035
theorem B698107 : Blo 694316 698107 := bstep (se 1 (by rfl) ⟨523580, by rfl⟩ : syracuseStep 698107 = 1047161) B1047161
theorem B698143 : Blo 694316 698143 := bstep (se 1 (by rfl) ⟨523607, by rfl⟩ : syracuseStep 698143 = 1047215) B1047215
theorem B698175 : Blo 694316 698175 := bstep (se 1 (by rfl) ⟨523631, by rfl⟩ : syracuseStep 698175 = 1047263) B1047263
theorem B1255657 : Blo 694316 1255657 := bstep (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) B941743
theorem B19310845 : Blo 694316 19310845 := bstep (se 3 (by rfl) ⟨3620783, by rfl⟩ : syracuseStep 19310845 = 7241567) B7241567
theorem B5646955 : Blo 694316 5646955 := bstep (se 1 (by rfl) ⟨4235216, by rfl⟩ : syracuseStep 5646955 = 8470433) B8470433
theorem B5941943 : Blo 694316 5941943 := bstep (se 1 (by rfl) ⟨4456457, by rfl⟩ : syracuseStep 5941943 = 8912915) B8912915
theorem B3975875 : Blo 694316 3975875 := bstep (se 1 (by rfl) ⟨2981906, by rfl⟩ : syracuseStep 3975875 = 5963813) B5963813
theorem B1485623 : Blo 694316 1485623 := bstep (se 1 (by rfl) ⟨1114217, by rfl⟩ : syracuseStep 1485623 = 2228435) B2228435
theorem B1060265 : Blo 694316 1060265 := bstep (se 2 (by rfl) ⟨397599, by rfl⟩ : syracuseStep 1060265 = 795199) B795199
theorem B4468247 : Blo 694316 4468247 := bstep (se 1 (by rfl) ⟨3351185, by rfl⟩ : syracuseStep 4468247 = 6702371) B6702371
theorem B1912427 : Blo 694316 1912427 := bstep (se 1 (by rfl) ⟨1434320, by rfl⟩ : syracuseStep 1912427 = 2868641) B2868641
theorem B1257935 : Blo 694316 1257935 := bstep (se 1 (by rfl) ⟨943451, by rfl⟩ : syracuseStep 1257935 = 1886903) B1886903
theorem B5026319 : Blo 694316 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B9549161 : Blo 694316 9549161 := bstep (se 2 (by rfl) ⟨3580935, by rfl⟩ : syracuseStep 9549161 = 7161871) B7161871
theorem B1979873 : Blo 694316 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B16103123 : Blo 694316 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B1980409 : Blo 694316 1980409 := bstep (se 2 (by rfl) ⟨742653, by rfl⟩ : syracuseStep 1980409 = 1485307) B1485307
theorem B3520745 : Blo 694316 3520745 := bstep (se 2 (by rfl) ⟨1320279, by rfl⟩ : syracuseStep 3520745 = 2640559) B2640559
theorem B4012667 : Blo 694316 4012667 := bstep (se 1 (by rfl) ⟨3009500, by rfl⟩ : syracuseStep 4012667 = 6019001) B6019001
theorem B152779445 : Blo 694316 152779445 := bstep (se 5 (by rfl) ⟨7161536, by rfl⟩ : syracuseStep 152779445 = 14323073) B14323073
theorem B4471631 : Blo 694316 4471631 := bstep (se 1 (by rfl) ⟨3353723, by rfl⟩ : syracuseStep 4471631 = 6707447) B6707447
theorem B5717287 : Blo 694316 5717287 := bstep (se 1 (by rfl) ⟨4287965, by rfl⟩ : syracuseStep 5717287 = 8575931) B8575931
theorem B1359335 : Blo 694316 1359335 := bstep (se 1 (by rfl) ⟨1019501, by rfl⟩ : syracuseStep 1359335 = 2039003) B2039003
theorem B1982333 : Blo 694316 1982333 := bstep (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) B743375
theorem B10731473 : Blo 694316 10731473 := bstep (se 2 (by rfl) ⟨4024302, by rfl⟩ : syracuseStep 10731473 = 8048605) B8048605
theorem B2965967 : Blo 694316 2965967 := bstep (se 1 (by rfl) ⟨2224475, by rfl⟩ : syracuseStep 2965967 = 4448951) B4448951
theorem B1982971 : Blo 694316 1982971 := bstep (se 1 (by rfl) ⟨1487228, by rfl⟩ : syracuseStep 1982971 = 2974457) B2974457
theorem B2343599 : Blo 694316 2343599 := bstep (se 1 (by rfl) ⟨1757699, by rfl⟩ : syracuseStep 2343599 = 3515399) B3515399
theorem B2638601 : Blo 694316 2638601 := bstep (se 2 (by rfl) ⟨989475, by rfl⟩ : syracuseStep 2638601 = 1978951) B1978951
theorem B3523337 : Blo 694316 3523337 := bstep (se 2 (by rfl) ⟨1321251, by rfl⟩ : syracuseStep 3523337 = 2642503) B2642503
theorem B1786681 : Blo 694316 1786681 := bstep (se 2 (by rfl) ⟨670005, by rfl⟩ : syracuseStep 1786681 = 1340011) B1340011
theorem B2343923 : Blo 694316 2343923 := bstep (se 1 (by rfl) ⟨1757942, by rfl⟩ : syracuseStep 2343923 = 3515885) B3515885
theorem B6767945 : Blo 694316 6767945 := bstep (se 2 (by rfl) ⟨2537979, by rfl⟩ : syracuseStep 6767945 = 5075959) B5075959
theorem B4244831 : Blo 694316 4244831 := bstep (se 1 (by rfl) ⟨3183623, by rfl⟩ : syracuseStep 4244831 = 6367247) B6367247
theorem B30033341 : Blo 694316 30033341 := bstep (se 3 (by rfl) ⟨5631251, by rfl⟩ : syracuseStep 30033341 = 11262503) B11262503
theorem B2344463 : Blo 694316 2344463 := bstep (se 1 (by rfl) ⟨1758347, by rfl⟩ : syracuseStep 2344463 = 3516695) B3516695
theorem B20072285 : Blo 694316 20072285 := bstep (se 3 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 20072285 = 7527107) B7527107
theorem B13354915 : Blo 694316 13354915 := bstep (se 1 (by rfl) ⟨10016186, by rfl⟩ : syracuseStep 13354915 = 20032373) B20032373
theorem B2115709 : Blo 694316 2115709 := bstep (se 3 (by rfl) ⟨396695, by rfl⟩ : syracuseStep 2115709 = 793391) B793391
theorem B27510961 : Blo 694316 27510961 := bstep (se 2 (by rfl) ⟨10316610, by rfl⟩ : syracuseStep 27510961 = 20633221) B20633221
theorem B2345273 : Blo 694316 2345273 := bstep (se 2 (by rfl) ⟨879477, by rfl⟩ : syracuseStep 2345273 = 1758955) B1758955
theorem B2967965 : Blo 694316 2967965 := bstep (se 3 (by rfl) ⟨556493, by rfl⟩ : syracuseStep 2967965 = 1112987) B1112987
theorem B2345543 : Blo 694316 2345543 := bstep (se 1 (by rfl) ⟨1759157, by rfl⟩ : syracuseStep 2345543 = 3518315) B3518315
theorem B3754601 : Blo 694316 3754601 := bstep (se 2 (by rfl) ⟨1407975, by rfl⟩ : syracuseStep 3754601 = 2815951) B2815951
theorem B2378423 : Blo 694316 2378423 := bstep (se 1 (by rfl) ⟨1783817, by rfl⟩ : syracuseStep 2378423 = 3567635) B3567635
theorem B7949015 : Blo 694316 7949015 := bstep (se 1 (by rfl) ⟨5961761, by rfl⟩ : syracuseStep 7949015 = 11923523) B11923523
theorem B1887031 : Blo 694316 1887031 := bstep (se 1 (by rfl) ⟨1415273, by rfl⟩ : syracuseStep 1887031 = 2830547) B2830547
theorem B2346569 : Blo 694316 2346569 := bstep (se 2 (by rfl) ⟨879963, by rfl⟩ : syracuseStep 2346569 = 1759927) B1759927
theorem B773723 : Blo 694316 773723 := bstep (se 1 (by rfl) ⟨580292, by rfl⟩ : syracuseStep 773723 = 1160585) B1160585
theorem B4018025 : Blo 694316 4018025 := bstep (se 2 (by rfl) ⟨1506759, by rfl⟩ : syracuseStep 4018025 = 3013519) B3013519
theorem B10310323 : Blo 694316 10310323 := bstep (se 1 (by rfl) ⟨7732742, by rfl⟩ : syracuseStep 10310323 = 15465485) B15465485
theorem B8934137 : Blo 694316 8934137 := bstep (se 2 (by rfl) ⟨3350301, by rfl⟩ : syracuseStep 8934137 = 6700603) B6700603
theorem B2348027 : Blo 694316 2348027 := bstep (se 1 (by rfl) ⟨1761020, by rfl⟩ : syracuseStep 2348027 = 3522041) B3522041
theorem B10703879 : Blo 694316 10703879 := bstep (se 1 (by rfl) ⟨8027909, by rfl⟩ : syracuseStep 10703879 = 16055819) B16055819
theorem B1758419 : Blo 694316 1758419 := bstep (se 1 (by rfl) ⟨1318814, by rfl⟩ : syracuseStep 1758419 = 2637629) B2637629
theorem B2348243 : Blo 694316 2348243 := bstep (se 1 (by rfl) ⟨1761182, by rfl⟩ : syracuseStep 2348243 = 3522365) B3522365
theorem B2348513 : Blo 694316 2348513 := bstep (se 2 (by rfl) ⟨880692, by rfl⟩ : syracuseStep 2348513 = 1761385) B1761385
theorem B1562363 : Blo 694316 1562363 := bstep (se 1 (by rfl) ⟨1171772, by rfl⟩ : syracuseStep 1562363 = 2343545) B2343545
theorem B3954689 : Blo 694316 3954689 := bstep (se 2 (by rfl) ⟨1483008, by rfl⟩ : syracuseStep 3954689 = 2966017) B2966017
theorem B2349161 : Blo 694316 2349161 := bstep (se 2 (by rfl) ⟨880935, by rfl⟩ : syracuseStep 2349161 = 1761871) B1761871
theorem B5298371 : Blo 694316 5298371 := bstep (se 1 (by rfl) ⟨3973778, by rfl⟩ : syracuseStep 5298371 = 7947557) B7947557
theorem B1562921 : Blo 694316 1562921 := bstep (se 2 (by rfl) ⟨586095, by rfl⟩ : syracuseStep 1562921 = 1172191) B1172191
theorem B2644265 : Blo 694316 2644265 := bstep (se 2 (by rfl) ⟨991599, by rfl⟩ : syracuseStep 2644265 = 1983199) B1983199
theorem B3169115 : Blo 694316 3169115 := bstep (se 1 (by rfl) ⟨2376836, by rfl⟩ : syracuseStep 3169115 = 4753673) B4753673
theorem B1563497 : Blo 694316 1563497 := bstep (se 2 (by rfl) ⟨586311, by rfl⟩ : syracuseStep 1563497 = 1172623) B1172623
theorem B1563551 : Blo 694316 1563551 := bstep (se 1 (by rfl) ⟨1172663, by rfl⟩ : syracuseStep 1563551 = 2345327) B2345327
theorem B2350025 : Blo 694316 2350025 := bstep (se 2 (by rfl) ⟨881259, by rfl⟩ : syracuseStep 2350025 = 1762519) B1762519
theorem B7953389 : Blo 694316 7953389 := bstep (se 3 (by rfl) ⟨1491260, by rfl⟩ : syracuseStep 7953389 = 2982521) B2982521
theorem B2350295 : Blo 694316 2350295 := bstep (se 1 (by rfl) ⟨1762721, by rfl⟩ : syracuseStep 2350295 = 3525443) B3525443
theorem B2645207 : Blo 694316 2645207 := bstep (se 1 (by rfl) ⟨1983905, by rfl⟩ : syracuseStep 2645207 = 3967811) B3967811
theorem B2514185 : Blo 694316 2514185 := bstep (se 2 (by rfl) ⟨942819, by rfl⟩ : syracuseStep 2514185 = 1885639) B1885639
theorem B2973023 : Blo 694316 2973023 := bstep (se 1 (by rfl) ⟨2229767, by rfl⟩ : syracuseStep 2973023 = 4459535) B4459535
theorem B1433063 : Blo 694316 1433063 := bstep (se 1 (by rfl) ⟨1074797, by rfl⟩ : syracuseStep 1433063 = 2149595) B2149595
theorem B1761011 : Blo 694316 1761011 := bstep (se 1 (by rfl) ⟨1320758, by rfl⟩ : syracuseStep 1761011 = 2641517) B2641517
theorem B2350835 : Blo 694316 2350835 := bstep (se 1 (by rfl) ⟨1763126, by rfl⟩ : syracuseStep 2350835 = 3526253) B3526253
theorem B1564487 : Blo 694316 1564487 := bstep (se 1 (by rfl) ⟨1173365, by rfl⟩ : syracuseStep 1564487 = 2346731) B2346731
theorem B2646391 : Blo 694316 2646391 := bstep (se 1 (by rfl) ⟨1984793, by rfl⟩ : syracuseStep 2646391 = 3969587) B3969587
theorem B1204607 : Blo 694316 1204607 := bstep (se 1 (by rfl) ⟨903455, by rfl⟩ : syracuseStep 1204607 = 1806911) B1806911
theorem B1565135 : Blo 694316 1565135 := bstep (se 1 (by rfl) ⟨1173851, by rfl⟩ : syracuseStep 1565135 = 2347703) B2347703
theorem B1172063 : Blo 694316 1172063 := bstep (se 1 (by rfl) ⟨879047, by rfl⟩ : syracuseStep 1172063 = 1758095) B1758095
theorem B15098501 : Blo 694316 15098501 := bstep (se 4 (by rfl) ⟨1415484, by rfl⟩ : syracuseStep 15098501 = 2830969) B2830969
theorem B1565801 : Blo 694316 1565801 := bstep (se 2 (by rfl) ⟨587175, by rfl⟩ : syracuseStep 1565801 = 1174351) B1174351
theorem B1041515 : Blo 694316 1041515 := bstep (se 1 (by rfl) ⟨781136, by rfl⟩ : syracuseStep 1041515 = 1562273) B1562273
theorem B4449437 : Blo 694316 4449437 := bstep (se 3 (by rfl) ⟨834269, by rfl⟩ : syracuseStep 4449437 = 1668539) B1668539
theorem B2647363 : Blo 694316 2647363 := bstep (se 1 (by rfl) ⟨1985522, by rfl⟩ : syracuseStep 2647363 = 3971045) B3971045
theorem B1041755 : Blo 694316 1041755 := bstep (se 1 (by rfl) ⟨781316, by rfl⟩ : syracuseStep 1041755 = 1562633) B1562633
theorem B1042031 : Blo 694316 1042031 := bstep (se 1 (by rfl) ⟨781523, by rfl⟩ : syracuseStep 1042031 = 1563047) B1563047
theorem B3532409 : Blo 694316 3532409 := bstep (se 2 (by rfl) ⟨1324653, by rfl⟩ : syracuseStep 3532409 = 2649307) B2649307
theorem B2975399 : Blo 694316 2975399 := bstep (se 1 (by rfl) ⟨2231549, by rfl⟩ : syracuseStep 2975399 = 4463099) B4463099
theorem B1042103 : Blo 694316 1042103 := bstep (se 1 (by rfl) ⟨781577, by rfl⟩ : syracuseStep 1042103 = 1563155) B1563155
theorem B4449977 : Blo 694316 4449977 := bstep (se 2 (by rfl) ⟨1668741, by rfl⟩ : syracuseStep 4449977 = 3337483) B3337483
theorem B1042139 : Blo 694316 1042139 := bstep (se 1 (by rfl) ⟨781604, by rfl⟩ : syracuseStep 1042139 = 1563209) B1563209
theorem B1566431 : Blo 694316 1566431 := bstep (se 1 (by rfl) ⟨1174823, by rfl⟩ : syracuseStep 1566431 = 2349647) B2349647
theorem B1042313 : Blo 694316 1042313 := bstep (se 2 (by rfl) ⟨390867, by rfl⟩ : syracuseStep 1042313 = 781735) B781735
theorem B1042415 : Blo 694316 1042415 := bstep (se 1 (by rfl) ⟨781811, by rfl⟩ : syracuseStep 1042415 = 1563623) B1563623
theorem B1173487 : Blo 694316 1173487 := bstep (se 1 (by rfl) ⟨880115, by rfl⟩ : syracuseStep 1173487 = 1760231) B1760231
theorem B1173737 : Blo 694316 1173737 := bstep (se 2 (by rfl) ⟨440151, by rfl⟩ : syracuseStep 1173737 = 880303) B880303
theorem B1042667 : Blo 694316 1042667 := bstep (se 1 (by rfl) ⟨782000, by rfl⟩ : syracuseStep 1042667 = 1564001) B1564001
theorem B3959063 : Blo 694316 3959063 := bstep (se 1 (by rfl) ⟨2969297, by rfl⟩ : syracuseStep 3959063 = 5938595) B5938595
theorem B73361699 : Blo 694316 73361699 := bstep (se 1 (by rfl) ⟨55021274, by rfl⟩ : syracuseStep 73361699 = 110042549) B110042549
theorem B1042727 : Blo 694316 1042727 := bstep (se 1 (by rfl) ⟨782045, by rfl⟩ : syracuseStep 1042727 = 1564091) B1564091
theorem B1042811 : Blo 694316 1042811 := bstep (se 1 (by rfl) ⟨782108, by rfl⟩ : syracuseStep 1042811 = 1564217) B1564217
theorem B1567259 : Blo 694316 1567259 := bstep (se 1 (by rfl) ⟨1175444, by rfl⟩ : syracuseStep 1567259 = 2350889) B2350889
theorem B67758727 : Blo 694316 67758727 := bstep (se 1 (by rfl) ⟨50819045, by rfl⟩ : syracuseStep 67758727 = 101638091) B101638091
theorem B1043081 : Blo 694316 1043081 := bstep (se 2 (by rfl) ⟨391155, by rfl⟩ : syracuseStep 1043081 = 782311) B782311
theorem B2976439 : Blo 694316 2976439 := bstep (se 1 (by rfl) ⟨2232329, by rfl⟩ : syracuseStep 2976439 = 4464659) B4464659
theorem B1043255 : Blo 694316 1043255 := bstep (se 1 (by rfl) ⟨782441, by rfl⟩ : syracuseStep 1043255 = 1564883) B1564883
theorem B1043291 : Blo 694316 1043291 := bstep (se 1 (by rfl) ⟨782468, by rfl⟩ : syracuseStep 1043291 = 1564937) B1564937
theorem B1043435 : Blo 694316 1043435 := bstep (se 1 (by rfl) ⟨782576, by rfl⟩ : syracuseStep 1043435 = 1565153) B1565153
theorem B1043639 : Blo 694316 1043639 := bstep (se 1 (by rfl) ⟨782729, by rfl⟩ : syracuseStep 1043639 = 1565459) B1565459
theorem B1764575 : Blo 694316 1764575 := bstep (se 1 (by rfl) ⟨1323431, by rfl⟩ : syracuseStep 1764575 = 2646863) B2646863
theorem B2354399 : Blo 694316 2354399 := bstep (se 1 (by rfl) ⟨1765799, by rfl⟩ : syracuseStep 2354399 = 3531599) B3531599
theorem B15068567 : Blo 694316 15068567 := bstep (se 1 (by rfl) ⟨11301425, by rfl⟩ : syracuseStep 15068567 = 22602851) B22602851
theorem B1043879 : Blo 694316 1043879 := bstep (se 1 (by rfl) ⟨782909, by rfl⟩ : syracuseStep 1043879 = 1565819) B1565819
theorem B2354615 : Blo 694316 2354615 := bstep (se 1 (by rfl) ⟨1765961, by rfl⟩ : syracuseStep 2354615 = 3531923) B3531923
theorem B1043963 : Blo 694316 1043963 := bstep (se 1 (by rfl) ⟨782972, by rfl⟩ : syracuseStep 1043963 = 1565945) B1565945
theorem B781915 : Blo 694316 781915 := bstep (se 1 (by rfl) ⟨586436, by rfl⟩ : syracuseStep 781915 = 1172873) B1172873
theorem B1044059 : Blo 694316 1044059 := bstep (se 1 (by rfl) ⟨783044, by rfl⟩ : syracuseStep 1044059 = 1566089) B1566089
theorem B1044143 : Blo 694316 1044143 := bstep (se 1 (by rfl) ⟨783107, by rfl⟩ : syracuseStep 1044143 = 1566215) B1566215
theorem B1175215 : Blo 694316 1175215 := bstep (se 1 (by rfl) ⟨881411, by rfl⟩ : syracuseStep 1175215 = 1762823) B1762823
theorem B1044263 : Blo 694316 1044263 := bstep (se 1 (by rfl) ⟨783197, by rfl⟩ : syracuseStep 1044263 = 1566395) B1566395
theorem B782203 : Blo 694316 782203 := bstep (se 1 (by rfl) ⟨586652, by rfl⟩ : syracuseStep 782203 = 1173305) B1173305
theorem B1044347 : Blo 694316 1044347 := bstep (se 1 (by rfl) ⟨783260, by rfl⟩ : syracuseStep 1044347 = 1566521) B1566521
theorem B7925687 : Blo 694316 7925687 := bstep (se 1 (by rfl) ⟨5944265, by rfl⟩ : syracuseStep 7925687 = 11888531) B11888531
theorem B1175519 : Blo 694316 1175519 := bstep (se 1 (by rfl) ⟨881639, by rfl⟩ : syracuseStep 1175519 = 1763279) B1763279
theorem B1568735 : Blo 694316 1568735 := bstep (se 1 (by rfl) ⟨1176551, by rfl⟩ : syracuseStep 1568735 = 2353103) B2353103
theorem B5009597 : Blo 694316 5009597 := bstep (se 3 (by rfl) ⟨939299, by rfl⟩ : syracuseStep 5009597 = 1878599) B1878599
theorem B3961021 : Blo 694316 3961021 := bstep (se 3 (by rfl) ⟨742691, by rfl⟩ : syracuseStep 3961021 = 1485383) B1485383
theorem B1044767 : Blo 694316 1044767 := bstep (se 1 (by rfl) ⟨783575, by rfl⟩ : syracuseStep 1044767 = 1567151) B1567151
theorem B880951 : Blo 694316 880951 := bstep (se 1 (by rfl) ⟨660713, by rfl⟩ : syracuseStep 880951 = 1321427) B1321427
theorem B1044791 : Blo 694316 1044791 := bstep (se 1 (by rfl) ⟨783593, by rfl⟩ : syracuseStep 1044791 = 1567187) B1567187
theorem B1175863 : Blo 694316 1175863 := bstep (se 1 (by rfl) ⟨881897, by rfl⟩ : syracuseStep 1175863 = 1763795) B1763795
theorem B1044863 : Blo 694316 1044863 := bstep (se 1 (by rfl) ⟨783647, by rfl⟩ : syracuseStep 1044863 = 1567295) B1567295
theorem B1765759 : Blo 694316 1765759 := bstep (se 1 (by rfl) ⟨1324319, by rfl⟩ : syracuseStep 1765759 = 2648639) B2648639
theorem B1044935 : Blo 694316 1044935 := bstep (se 1 (by rfl) ⟨783701, by rfl⟩ : syracuseStep 1044935 = 1567403) B1567403
theorem B1176167 : Blo 694316 1176167 := bstep (se 1 (by rfl) ⟨882125, by rfl⟩ : syracuseStep 1176167 = 1764251) B1764251
theorem B1569383 : Blo 694316 1569383 := bstep (se 1 (by rfl) ⟨1177037, by rfl⟩ : syracuseStep 1569383 = 2354075) B2354075
theorem B4223735 : Blo 694316 4223735 := bstep (se 1 (by rfl) ⟨3167801, by rfl⟩ : syracuseStep 4223735 = 6335603) B6335603
theorem B4453127 : Blo 694316 4453127 := bstep (se 1 (by rfl) ⟨3339845, by rfl⟩ : syracuseStep 4453127 = 6679691) B6679691
theorem B1176329 : Blo 694316 1176329 := bstep (se 2 (by rfl) ⟨441123, by rfl⟩ : syracuseStep 1176329 = 882247) B882247
theorem B1045289 : Blo 694316 1045289 := bstep (se 2 (by rfl) ⟨391983, by rfl⟩ : syracuseStep 1045289 = 783967) B783967
theorem B1045295 : Blo 694316 1045295 := bstep (se 1 (by rfl) ⟨783971, by rfl⟩ : syracuseStep 1045295 = 1567943) B1567943
theorem B16118635 : Blo 694316 16118635 := bstep (se 1 (by rfl) ⟨12088976, by rfl⟩ : syracuseStep 16118635 = 24177953) B24177953
theorem B1045415 : Blo 694316 1045415 := bstep (se 1 (by rfl) ⟨784061, by rfl⟩ : syracuseStep 1045415 = 1568123) B1568123
theorem B783355 : Blo 694316 783355 := bstep (se 1 (by rfl) ⟨587516, by rfl⟩ : syracuseStep 783355 = 1175033) B1175033
theorem B1045499 : Blo 694316 1045499 := bstep (se 1 (by rfl) ⟨784124, by rfl⟩ : syracuseStep 1045499 = 1568249) B1568249
theorem B5272613 : Blo 694316 5272613 := bstep (se 4 (by rfl) ⟨494307, by rfl⟩ : syracuseStep 5272613 = 988615) B988615
theorem B1045559 : Blo 694316 1045559 := bstep (se 1 (by rfl) ⟨784169, by rfl⟩ : syracuseStep 1045559 = 1568339) B1568339
theorem B783535 : Blo 694316 783535 := bstep (se 1 (by rfl) ⟨587651, by rfl⟩ : syracuseStep 783535 = 1175303) B1175303
theorem B1045679 : Blo 694316 1045679 := bstep (se 1 (by rfl) ⟨784259, by rfl⟩ : syracuseStep 1045679 = 1568519) B1568519
theorem B3339539 : Blo 694316 3339539 := bstep (se 1 (by rfl) ⟨2504654, by rfl⟩ : syracuseStep 3339539 = 5009309) B5009309
theorem B1570067 : Blo 694316 1570067 := bstep (se 1 (by rfl) ⟨1177550, by rfl⟩ : syracuseStep 1570067 = 2355101) B2355101
theorem B6354227 : Blo 694316 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B1176923 : Blo 694316 1176923 := bstep (se 1 (by rfl) ⟨882692, by rfl⟩ : syracuseStep 1176923 = 1765385) B1765385
theorem B1570139 : Blo 694316 1570139 := bstep (se 1 (by rfl) ⟨1177604, by rfl⟩ : syracuseStep 1570139 = 2355209) B2355209
theorem B2356667 : Blo 694316 2356667 := bstep (se 1 (by rfl) ⟨1767500, by rfl⟩ : syracuseStep 2356667 = 3535001) B3535001
theorem B19559981 : Blo 694316 19559981 := bstep (se 3 (by rfl) ⟨3667496, by rfl⟩ : syracuseStep 19559981 = 7334993) B7334993
theorem B1046087 : Blo 694316 1046087 := bstep (se 1 (by rfl) ⟨784565, by rfl⟩ : syracuseStep 1046087 = 1569131) B1569131
theorem B1177159 : Blo 694316 1177159 := bstep (se 1 (by rfl) ⟨882869, by rfl⟩ : syracuseStep 1177159 = 1765739) B1765739
theorem B784039 : Blo 694316 784039 := bstep (se 1 (by rfl) ⟨588029, by rfl⟩ : syracuseStep 784039 = 1176059) B1176059
theorem B882343 : Blo 694316 882343 := bstep (se 1 (by rfl) ⟨661757, by rfl⟩ : syracuseStep 882343 = 1323515) B1323515
theorem B1046183 : Blo 694316 1046183 := bstep (se 1 (by rfl) ⟨784637, by rfl⟩ : syracuseStep 1046183 = 1569275) B1569275
theorem B3339959 : Blo 694316 3339959 := bstep (se 1 (by rfl) ⟨2504969, by rfl⟩ : syracuseStep 3339959 = 5009939) B5009939
theorem B4454099 : Blo 694316 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B980731 : Blo 694316 980731 := bstep (se 1 (by rfl) ⟨735548, by rfl⟩ : syracuseStep 980731 = 1471097) B1471097
theorem B1046267 : Blo 694316 1046267 := bstep (se 1 (by rfl) ⟨784700, by rfl⟩ : syracuseStep 1046267 = 1569401) B1569401
theorem B16971515 : Blo 694316 16971515 := bstep (se 1 (by rfl) ⟨12728636, by rfl⟩ : syracuseStep 16971515 = 25457273) B25457273
theorem B6616849 : Blo 694316 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B1046303 : Blo 694316 1046303 := bstep (se 1 (by rfl) ⟨784727, by rfl⟩ : syracuseStep 1046303 = 1569455) B1569455
theorem B1177375 : Blo 694316 1177375 := bstep (se 1 (by rfl) ⟨883031, by rfl⟩ : syracuseStep 1177375 = 1766063) B1766063
theorem B1046351 : Blo 694316 1046351 := bstep (se 1 (by rfl) ⟨784763, by rfl⟩ : syracuseStep 1046351 = 1569527) B1569527
theorem B1570697 : Blo 694316 1570697 := bstep (se 2 (by rfl) ⟨589011, by rfl⟩ : syracuseStep 1570697 = 1178023) B1178023
theorem B784327 : Blo 694316 784327 := bstep (se 1 (by rfl) ⟨588245, by rfl⟩ : syracuseStep 784327 = 1176491) B1176491
theorem B1046471 : Blo 694316 1046471 := bstep (se 1 (by rfl) ⟨784853, by rfl⟩ : syracuseStep 1046471 = 1569707) B1569707
theorem B1177591 : Blo 694316 1177591 := bstep (se 1 (by rfl) ⟨883193, by rfl⟩ : syracuseStep 1177591 = 1766387) B1766387
theorem B1570913 : Blo 694316 1570913 := bstep (se 2 (by rfl) ⟨589092, by rfl⟩ : syracuseStep 1570913 = 1178185) B1178185
theorem B1767521 : Blo 694316 1767521 := bstep (se 2 (by rfl) ⟨662820, by rfl⟩ : syracuseStep 1767521 = 1325641) B1325641
theorem B1505479 : Blo 694316 1505479 := bstep (se 1 (by rfl) ⟨1129109, by rfl⟩ : syracuseStep 1505479 = 2258219) B2258219
theorem B1177895 : Blo 694316 1177895 := bstep (se 1 (by rfl) ⟨883421, by rfl⟩ : syracuseStep 1177895 = 1766843) B1766843
theorem B1046825 : Blo 694316 1046825 := bstep (se 2 (by rfl) ⟨392559, by rfl⟩ : syracuseStep 1046825 = 785119) B785119
theorem B784687 : Blo 694316 784687 := bstep (se 1 (by rfl) ⟨588515, by rfl⟩ : syracuseStep 784687 = 1177031) B1177031
theorem B882991 : Blo 694316 882991 := bstep (se 1 (by rfl) ⟨662243, by rfl⟩ : syracuseStep 882991 = 1324487) B1324487
theorem B1046831 : Blo 694316 1046831 := bstep (se 1 (by rfl) ⟨785123, by rfl⟩ : syracuseStep 1046831 = 1570247) B1570247
theorem B12712301 : Blo 694316 12712301 := bstep (se 3 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 12712301 = 4767113) B4767113
theorem B1047071 : Blo 694316 1047071 := bstep (se 1 (by rfl) ⟨785303, by rfl⟩ : syracuseStep 1047071 = 1570607) B1570607
theorem B2226845 : Blo 694316 2226845 := bstep (se 3 (by rfl) ⟨417533, by rfl⟩ : syracuseStep 2226845 = 835067) B835067
theorem B4455101 : Blo 694316 4455101 := bstep (se 3 (by rfl) ⟨835331, by rfl⟩ : syracuseStep 4455101 = 1670663) B1670663
theorem B1047455 : Blo 694316 1047455 := bstep (se 1 (by rfl) ⟨785591, by rfl⟩ : syracuseStep 1047455 = 1571183) B1571183
theorem B785479 : Blo 694316 785479 := bstep (se 1 (by rfl) ⟨589109, by rfl⟩ : syracuseStep 785479 = 1178219) B1178219
theorem B5012999 : Blo 694316 5012999 := bstep (se 1 (by rfl) ⟨3759749, by rfl⟩ : syracuseStep 5012999 = 7519499) B7519499
theorem B1113833 : Blo 694316 1113833 := bstep (se 2 (by rfl) ⟨417687, by rfl⟩ : syracuseStep 1113833 = 835375) B835375
theorem B2229191 : Blo 694316 2229191 := bstep (se 1 (by rfl) ⟨1671893, by rfl⟩ : syracuseStep 2229191 = 3343787) B3343787
theorem B20022227 : Blo 694316 20022227 := bstep (se 1 (by rfl) ⟨15016670, by rfl⟩ : syracuseStep 20022227 = 30033341) B30033341
theorem B1672201 : Blo 694316 1672201 := bstep (se 2 (by rfl) ⟨627075, by rfl⟩ : syracuseStep 1672201 = 1254151) B1254151
theorem B6685841 : Blo 694316 6685841 := bstep (se 2 (by rfl) ⟨2507190, by rfl⟩ : syracuseStep 6685841 = 5014381) B5014381
theorem B8128457 : Blo 694316 8128457 := bstep (se 2 (by rfl) ⟨3048171, by rfl⟩ : syracuseStep 8128457 = 6096343) B6096343
theorem B2230433 : Blo 694316 2230433 := bstep (se 2 (by rfl) ⟨836412, by rfl⟩ : syracuseStep 2230433 = 1672825) B1672825
theorem B1674209 : Blo 694316 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B3345803 : Blo 694316 3345803 := bstep (se 1 (by rfl) ⟨2509352, by rfl⟩ : syracuseStep 3345803 = 5018705) B5018705
theorem B90344969 : Blo 694316 90344969 := bstep (se 2 (by rfl) ⟨33879363, by rfl⟩ : syracuseStep 90344969 = 67758727) B67758727
theorem B3968585 : Blo 694316 3968585 := bstep (se 2 (by rfl) ⟨1488219, by rfl⟩ : syracuseStep 3968585 = 2976439) B2976439
theorem B3870287 : Blo 694316 3870287 := bstep (se 1 (by rfl) ⟨2902715, by rfl⟩ : syracuseStep 3870287 = 5805431) B5805431
theorem B1676123 : Blo 694316 1676123 := bstep (se 1 (by rfl) ⟨1257092, by rfl⟩ : syracuseStep 1676123 = 2514185) B2514185
theorem B5281361 : Blo 694316 5281361 := bstep (se 2 (by rfl) ⟨1980510, by rfl⟩ : syracuseStep 5281361 = 3961021) B3961021
theorem B10065667 : Blo 694316 10065667 := bstep (se 1 (by rfl) ⟨7549250, by rfl⟩ : syracuseStep 10065667 = 15098501) B15098501
theorem B694343 : Blo 694316 694343 := bstep (se 1 (by rfl) ⟨520757, by rfl⟩ : syracuseStep 694343 = 1041515) B1041515
theorem B694503 : Blo 694316 694503 := bstep (se 1 (by rfl) ⟨520877, by rfl⟩ : syracuseStep 694503 = 1041755) B1041755
theorem B694687 : Blo 694316 694687 := bstep (se 1 (by rfl) ⟨521015, by rfl⟩ : syracuseStep 694687 = 1042031) B1042031
theorem B694735 : Blo 694316 694735 := bstep (se 1 (by rfl) ⟨521051, by rfl⟩ : syracuseStep 694735 = 1042103) B1042103
theorem B694759 : Blo 694316 694759 := bstep (se 1 (by rfl) ⟨521069, by rfl⟩ : syracuseStep 694759 = 1042139) B1042139
theorem B694875 : Blo 694316 694875 := bstep (se 1 (by rfl) ⟨521156, by rfl⟩ : syracuseStep 694875 = 1042313) B1042313
theorem B694943 : Blo 694316 694943 := bstep (se 1 (by rfl) ⟨521207, by rfl⟩ : syracuseStep 694943 = 1042415) B1042415
theorem B695111 : Blo 694316 695111 := bstep (se 1 (by rfl) ⟨521333, by rfl⟩ : syracuseStep 695111 = 1042667) B1042667
theorem B695151 : Blo 694316 695151 := bstep (se 1 (by rfl) ⟨521363, by rfl⟩ : syracuseStep 695151 = 1042727) B1042727
theorem B695207 : Blo 694316 695207 := bstep (se 1 (by rfl) ⟨521405, by rfl⟩ : syracuseStep 695207 = 1042811) B1042811
theorem B695387 : Blo 694316 695387 := bstep (se 1 (by rfl) ⟨521540, by rfl⟩ : syracuseStep 695387 = 1043081) B1043081
theorem B695503 : Blo 694316 695503 := bstep (se 1 (by rfl) ⟨521627, by rfl⟩ : syracuseStep 695503 = 1043255) B1043255
theorem B990415 : Blo 694316 990415 := bstep (se 1 (by rfl) ⟨742811, by rfl⟩ : syracuseStep 990415 = 1485623) B1485623
theorem B695527 : Blo 694316 695527 := bstep (se 1 (by rfl) ⟨521645, by rfl⟩ : syracuseStep 695527 = 1043291) B1043291
theorem B695623 : Blo 694316 695623 := bstep (se 1 (by rfl) ⟨521717, by rfl⟩ : syracuseStep 695623 = 1043435) B1043435
theorem B695759 : Blo 694316 695759 := bstep (se 1 (by rfl) ⟨521819, by rfl⟩ : syracuseStep 695759 = 1043639) B1043639
theorem B695919 : Blo 694316 695919 := bstep (se 1 (by rfl) ⟨521939, by rfl⟩ : syracuseStep 695919 = 1043879) B1043879
theorem B695975 : Blo 694316 695975 := bstep (se 1 (by rfl) ⟨521981, by rfl⟩ : syracuseStep 695975 = 1043963) B1043963
theorem B8822465 : Blo 694316 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B696039 : Blo 694316 696039 := bstep (se 1 (by rfl) ⟨522029, by rfl⟩ : syracuseStep 696039 = 1044059) B1044059
theorem B696095 : Blo 694316 696095 := bstep (se 1 (by rfl) ⟨522071, by rfl⟩ : syracuseStep 696095 = 1044143) B1044143
theorem B696175 : Blo 694316 696175 := bstep (se 1 (by rfl) ⟨522131, by rfl⟩ : syracuseStep 696175 = 1044263) B1044263
theorem B696231 : Blo 694316 696231 := bstep (se 1 (by rfl) ⟨522173, by rfl⟩ : syracuseStep 696231 = 1044347) B1044347
theorem B5283791 : Blo 694316 5283791 := bstep (se 1 (by rfl) ⟨3962843, by rfl⟩ : syracuseStep 5283791 = 7925687) B7925687
theorem B696511 : Blo 694316 696511 := bstep (se 1 (by rfl) ⟨522383, by rfl⟩ : syracuseStep 696511 = 1044767) B1044767
theorem B696527 : Blo 694316 696527 := bstep (se 1 (by rfl) ⟨522395, by rfl⟩ : syracuseStep 696527 = 1044791) B1044791
theorem B696575 : Blo 694316 696575 := bstep (se 1 (by rfl) ⟨522431, by rfl⟩ : syracuseStep 696575 = 1044863) B1044863
theorem B2007305 : Blo 694316 2007305 := bstep (se 2 (by rfl) ⟨752739, by rfl⟩ : syracuseStep 2007305 = 1505479) B1505479
theorem B696623 : Blo 694316 696623 := bstep (se 1 (by rfl) ⟨522467, by rfl⟩ : syracuseStep 696623 = 1044935) B1044935
theorem B3350879 : Blo 694316 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B696859 : Blo 694316 696859 := bstep (se 1 (by rfl) ⟨522644, by rfl⟩ : syracuseStep 696859 = 1045289) B1045289
theorem B696863 : Blo 694316 696863 := bstep (se 1 (by rfl) ⟨522647, by rfl⟩ : syracuseStep 696863 = 1045295) B1045295
theorem B696943 : Blo 694316 696943 := bstep (se 1 (by rfl) ⟨522707, by rfl⟩ : syracuseStep 696943 = 1045415) B1045415
theorem B696999 : Blo 694316 696999 := bstep (se 1 (by rfl) ⟨522749, by rfl⟩ : syracuseStep 696999 = 1045499) B1045499
theorem B3515075 : Blo 694316 3515075 := bstep (se 1 (by rfl) ⟨2636306, by rfl⟩ : syracuseStep 3515075 = 5272613) B5272613
theorem B697039 : Blo 694316 697039 := bstep (se 1 (by rfl) ⟨522779, by rfl⟩ : syracuseStep 697039 = 1045559) B1045559
theorem B697119 : Blo 694316 697119 := bstep (se 1 (by rfl) ⟨522839, by rfl⟩ : syracuseStep 697119 = 1045679) B1045679
theorem B4236151 : Blo 694316 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B6366107 : Blo 694316 6366107 := bstep (se 1 (by rfl) ⟨4774580, by rfl⟩ : syracuseStep 6366107 = 9549161) B9549161
theorem B1319915 : Blo 694316 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B697391 : Blo 694316 697391 := bstep (se 1 (by rfl) ⟨523043, by rfl⟩ : syracuseStep 697391 = 1046087) B1046087
theorem B697455 : Blo 694316 697455 := bstep (se 1 (by rfl) ⟨523091, by rfl⟩ : syracuseStep 697455 = 1046183) B1046183
theorem B697511 : Blo 694316 697511 := bstep (se 1 (by rfl) ⟨523133, by rfl⟩ : syracuseStep 697511 = 1046267) B1046267
theorem B11314343 : Blo 694316 11314343 := bstep (se 1 (by rfl) ⟨8485757, by rfl⟩ : syracuseStep 11314343 = 16971515) B16971515
theorem B697535 : Blo 694316 697535 := bstep (se 1 (by rfl) ⟨523151, by rfl⟩ : syracuseStep 697535 = 1046303) B1046303
theorem B697567 : Blo 694316 697567 := bstep (se 1 (by rfl) ⟨523175, by rfl⟩ : syracuseStep 697567 = 1046351) B1046351
theorem B697647 : Blo 694316 697647 := bstep (se 1 (by rfl) ⟨523235, by rfl⟩ : syracuseStep 697647 = 1046471) B1046471
theorem B697883 : Blo 694316 697883 := bstep (se 1 (by rfl) ⟨523412, by rfl⟩ : syracuseStep 697883 = 1046825) B1046825
theorem B697887 : Blo 694316 697887 := bstep (se 1 (by rfl) ⟨523415, by rfl⟩ : syracuseStep 697887 = 1046831) B1046831
theorem B698047 : Blo 694316 698047 := bstep (se 1 (by rfl) ⟨523535, by rfl⟩ : syracuseStep 698047 = 1047071) B1047071
theorem B1484563 : Blo 694316 1484563 := bstep (se 1 (by rfl) ⟨1113422, by rfl⟩ : syracuseStep 1484563 = 2226845) B2226845
theorem B101852963 : Blo 694316 101852963 := bstep (se 1 (by rfl) ⟨76389722, by rfl⟩ : syracuseStep 101852963 = 152779445) B152779445
theorem B698303 : Blo 694316 698303 := bstep (se 1 (by rfl) ⟨523727, by rfl⟩ : syracuseStep 698303 = 1047455) B1047455
theorem B5286221 : Blo 694316 5286221 := bstep (se 3 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 5286221 = 1982333) B1982333
theorem B7154315 : Blo 694316 7154315 := bstep (se 1 (by rfl) ⟨5365736, by rfl⟩ : syracuseStep 7154315 = 10731473) B10731473
theorem B5024531 : Blo 694316 5024531 := bstep (se 1 (by rfl) ⟨3768398, by rfl⟩ : syracuseStep 5024531 = 7536797) B7536797
theorem B1977311 : Blo 694316 1977311 := bstep (se 1 (by rfl) ⟨1482983, by rfl⟩ : syracuseStep 1977311 = 2965967) B2965967
theorem B1322057 : Blo 694316 1322057 := bstep (se 2 (by rfl) ⟨495771, by rfl⟩ : syracuseStep 1322057 = 991543) B991543
theorem B1486135 : Blo 694316 1486135 := bstep (se 1 (by rfl) ⟨1114601, by rfl⟩ : syracuseStep 1486135 = 2229203) B2229203
theorem B11283781 : Blo 694316 11283781 := bstep (se 4 (by rfl) ⟨1057854, by rfl⟩ : syracuseStep 11283781 = 2115709) B2115709
theorem B8564105 : Blo 694316 8564105 := bstep (se 2 (by rfl) ⟨3211539, by rfl⟩ : syracuseStep 8564105 = 6423079) B6423079
theorem B2829887 : Blo 694316 2829887 := bstep (se 1 (by rfl) ⟨2122415, by rfl⟩ : syracuseStep 2829887 = 4244831) B4244831
theorem B2502377 : Blo 694316 2502377 := bstep (se 2 (by rfl) ⟨938391, by rfl⟩ : syracuseStep 2502377 = 1876783) B1876783
theorem B3354493 : Blo 694316 3354493 := bstep (se 3 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 3354493 = 1257935) B1257935
theorem B13381523 : Blo 694316 13381523 := bstep (se 1 (by rfl) ⟨10036142, by rfl⟩ : syracuseStep 13381523 = 20072285) B20072285
theorem B1486811 : Blo 694316 1486811 := bstep (se 1 (by rfl) ⟨1115108, by rfl⟩ : syracuseStep 1486811 = 2230217) B2230217
theorem B1978643 : Blo 694316 1978643 := bstep (se 1 (by rfl) ⟨1483982, by rfl⟩ : syracuseStep 1978643 = 2967965) B2967965
theorem B2503067 : Blo 694316 2503067 := bstep (se 1 (by rfl) ⟨1877300, by rfl⟩ : syracuseStep 2503067 = 3754601) B3754601
theorem B5288651 : Blo 694316 5288651 := bstep (se 1 (by rfl) ⟨3966488, by rfl⟩ : syracuseStep 5288651 = 7932977) B7932977
theorem B17806553 : Blo 694316 17806553 := bstep (se 2 (by rfl) ⟨6677457, by rfl⟩ : syracuseStep 17806553 = 13354915) B13354915
theorem B36681281 : Blo 694316 36681281 := bstep (se 2 (by rfl) ⟨13755480, by rfl⟩ : syracuseStep 36681281 = 27510961) B27510961
theorem B5945359 : Blo 694316 5945359 := bstep (se 1 (by rfl) ⟨4459019, by rfl⟩ : syracuseStep 5945359 = 8918039) B8918039
theorem B1488937 : Blo 694316 1488937 := bstep (se 2 (by rfl) ⟨558351, by rfl⟩ : syracuseStep 1488937 = 1116703) B1116703
theorem B30193721 : Blo 694316 30193721 := bstep (se 2 (by rfl) ⟨11322645, by rfl⟩ : syracuseStep 30193721 = 22645291) B22645291
theorem B3520583 : Blo 694316 3520583 := bstep (se 1 (by rfl) ⟨2640437, by rfl⟩ : syracuseStep 3520583 = 5280875) B5280875
theorem B17217773 : Blo 694316 17217773 := bstep (se 3 (by rfl) ⟨3228332, by rfl⟩ : syracuseStep 17217773 = 6456665) B6456665
theorem B2636459 : Blo 694316 2636459 := bstep (se 1 (by rfl) ⟨1977344, by rfl⟩ : syracuseStep 2636459 = 3954689) B3954689
theorem B2112743 : Blo 694316 2112743 := bstep (se 1 (by rfl) ⟨1584557, by rfl⟩ : syracuseStep 2112743 = 3169115) B3169115
theorem B1982015 : Blo 694316 1982015 := bstep (se 1 (by rfl) ⟨1486511, by rfl⟩ : syracuseStep 1982015 = 2973023) B2973023
theorem B1490663 : Blo 694316 1490663 := bstep (se 1 (by rfl) ⟨1117997, by rfl⟩ : syracuseStep 1490663 = 2235995) B2235995
theorem B803071 : Blo 694316 803071 := bstep (se 1 (by rfl) ⟨602303, by rfl⟩ : syracuseStep 803071 = 1204607) B1204607
theorem B9027875 : Blo 694316 9027875 := bstep (se 1 (by rfl) ⟨6770906, by rfl⟩ : syracuseStep 9027875 = 13541813) B13541813
theorem B5292539 : Blo 694316 5292539 := bstep (se 1 (by rfl) ⟨3969404, by rfl⟩ : syracuseStep 5292539 = 7938809) B7938809
theorem B2966291 : Blo 694316 2966291 := bstep (se 1 (by rfl) ⟨2224718, by rfl⟩ : syracuseStep 2966291 = 4449437) B4449437
theorem B13747097 : Blo 694316 13747097 := bstep (se 2 (by rfl) ⟨5155161, by rfl⟩ : syracuseStep 13747097 = 10310323) B10310323
theorem B1983599 : Blo 694316 1983599 := bstep (se 1 (by rfl) ⟨1487699, by rfl⟩ : syracuseStep 1983599 = 2975399) B2975399
theorem B2966651 : Blo 694316 2966651 := bstep (se 1 (by rfl) ⟨2224988, by rfl⟩ : syracuseStep 2966651 = 4449977) B4449977
theorem B2639375 : Blo 694316 2639375 := bstep (se 1 (by rfl) ⟨1979531, by rfl⟩ : syracuseStep 2639375 = 3959063) B3959063
theorem B48907799 : Blo 694316 48907799 := bstep (se 1 (by rfl) ⟨36680849, by rfl⟩ : syracuseStep 48907799 = 73361699) B73361699
theorem B30492197 : Blo 694316 30492197 := bstep (se 4 (by rfl) ⟨2858643, by rfl⟩ : syracuseStep 30492197 = 5717287) B5717287
theorem B6342461 : Blo 694316 6342461 := bstep (se 3 (by rfl) ⟨1189211, by rfl⟩ : syracuseStep 6342461 = 2378423) B2378423
theorem B21678137 : Blo 694316 21678137 := bstep (se 2 (by rfl) ⟨8129301, by rfl⟩ : syracuseStep 21678137 = 16258603) B16258603
theorem B10045711 : Blo 694316 10045711 := bstep (se 1 (by rfl) ⟨7534283, by rfl⟩ : syracuseStep 10045711 = 15068567) B15068567
theorem B706843 : Blo 694316 706843 := bstep (se 1 (by rfl) ⟨530132, by rfl⟩ : syracuseStep 706843 = 1060265) B1060265
theorem B2640545 : Blo 694316 2640545 := bstep (se 2 (by rfl) ⟨990204, by rfl⟩ : syracuseStep 2640545 = 1980409) B1980409
theorem B5294969 : Blo 694316 5294969 := bstep (se 2 (by rfl) ⟨1985613, by rfl⟩ : syracuseStep 5294969 = 3971227) B3971227
theorem B2968751 : Blo 694316 2968751 := bstep (se 1 (by rfl) ⟨2226563, by rfl⟩ : syracuseStep 2968751 = 4453127) B4453127
theorem B2969399 : Blo 694316 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B10735415 : Blo 694316 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B3821501 : Blo 694316 3821501 := bstep (se 3 (by rfl) ⟨716531, by rfl⟩ : syracuseStep 3821501 = 1433063) B1433063
theorem B5230565 : Blo 694316 5230565 := bstep (se 4 (by rfl) ⟨490365, by rfl⟩ : syracuseStep 5230565 = 980731) B980731
theorem B2347163 : Blo 694316 2347163 := bstep (se 1 (by rfl) ⟨1760372, by rfl⟩ : syracuseStep 2347163 = 3520745) B3520745
theorem B8474867 : Blo 694316 8474867 := bstep (se 1 (by rfl) ⟨6356150, by rfl⟩ : syracuseStep 8474867 = 12712301) B12712301
theorem B2675111 : Blo 694316 2675111 := bstep (se 1 (by rfl) ⟨2006333, by rfl⟩ : syracuseStep 2675111 = 4012667) B4012667
theorem B2970067 : Blo 694316 2970067 := bstep (se 1 (by rfl) ⟨2227550, by rfl⟩ : syracuseStep 2970067 = 4455101) B4455101
theorem B906223 : Blo 694316 906223 := bstep (se 1 (by rfl) ⟨679667, by rfl⟩ : syracuseStep 906223 = 1359335) B1359335
theorem B742555 : Blo 694316 742555 := bstep (se 1 (by rfl) ⟨556916, by rfl⟩ : syracuseStep 742555 = 1113833) B1113833
theorem B1562399 : Blo 694316 1562399 := bstep (se 1 (by rfl) ⟨1171799, by rfl⟩ : syracuseStep 1562399 = 2343599) B2343599
theorem B3528521 : Blo 694316 3528521 := bstep (se 2 (by rfl) ⟨1323195, by rfl⟩ : syracuseStep 3528521 = 2646391) B2646391
theorem B1759067 : Blo 694316 1759067 := bstep (se 1 (by rfl) ⟨1319300, by rfl⟩ : syracuseStep 1759067 = 2638601) B2638601
theorem B2348891 : Blo 694316 2348891 := bstep (se 1 (by rfl) ⟨1761668, by rfl⟩ : syracuseStep 2348891 = 3523337) B3523337
theorem B1562615 : Blo 694316 1562615 := bstep (se 1 (by rfl) ⟨1171961, by rfl⟩ : syracuseStep 1562615 = 2343923) B2343923
theorem B2643961 : Blo 694316 2643961 := bstep (se 2 (by rfl) ⟨991485, by rfl⟩ : syracuseStep 2643961 = 1982971) B1982971
theorem B4511963 : Blo 694316 4511963 := bstep (se 1 (by rfl) ⟨3383972, by rfl⟩ : syracuseStep 4511963 = 6767945) B6767945
theorem B1562975 : Blo 694316 1562975 := bstep (se 1 (by rfl) ⟨1172231, by rfl⟩ : syracuseStep 1562975 = 2344463) B2344463
theorem B1005983 : Blo 694316 1005983 := bstep (se 1 (by rfl) ⟨754487, by rfl⟩ : syracuseStep 1005983 = 1508975) B1508975
theorem B2972065 : Blo 694316 2972065 := bstep (se 2 (by rfl) ⟨1114524, by rfl⟩ : syracuseStep 2972065 = 2229049) B2229049
theorem B2513735 : Blo 694316 2513735 := bstep (se 1 (by rfl) ⟨1885301, by rfl⟩ : syracuseStep 2513735 = 3770603) B3770603
theorem B1563515 : Blo 694316 1563515 := bstep (se 1 (by rfl) ⟨1172636, by rfl⟩ : syracuseStep 1563515 = 2345273) B2345273
theorem B1563695 : Blo 694316 1563695 := bstep (se 1 (by rfl) ⟨1172771, by rfl⟩ : syracuseStep 1563695 = 2345543) B2345543
theorem B3529817 : Blo 694316 3529817 := bstep (se 2 (by rfl) ⟨1323681, by rfl⟩ : syracuseStep 3529817 = 2647363) B2647363
theorem B5299343 : Blo 694316 5299343 := bstep (se 1 (by rfl) ⟨3974507, by rfl⟩ : syracuseStep 5299343 = 7949015) B7949015
theorem B1564379 : Blo 694316 1564379 := bstep (se 1 (by rfl) ⟨1173284, by rfl⟩ : syracuseStep 1564379 = 2346569) B2346569
theorem B2678683 : Blo 694316 2678683 := bstep (se 1 (by rfl) ⟨2009012, by rfl⟩ : syracuseStep 2678683 = 4018025) B4018025
theorem B1564649 : Blo 694316 1564649 := bstep (se 2 (by rfl) ⟨586743, by rfl⟩ : syracuseStep 1564649 = 1173487) B1173487
theorem B25747793 : Blo 694316 25747793 := bstep (se 2 (by rfl) ⟨9655422, by rfl⟩ : syracuseStep 25747793 = 19310845) B19310845
theorem B5956091 : Blo 694316 5956091 := bstep (se 1 (by rfl) ⟨4467068, by rfl⟩ : syracuseStep 5956091 = 8934137) B8934137
theorem B942619 : Blo 694316 942619 := bstep (se 1 (by rfl) ⟨706964, by rfl⟩ : syracuseStep 942619 = 1413929) B1413929
theorem B1565351 : Blo 694316 1565351 := bstep (se 1 (by rfl) ⟨1174013, by rfl⟩ : syracuseStep 1565351 = 2348027) B2348027
theorem B2646695 : Blo 694316 2646695 := bstep (se 1 (by rfl) ⟨1985021, by rfl⟩ : syracuseStep 2646695 = 3970043) B3970043
theorem B7135919 : Blo 694316 7135919 := bstep (se 1 (by rfl) ⟨5351939, by rfl⟩ : syracuseStep 7135919 = 10703879) B10703879
theorem B1172279 : Blo 694316 1172279 := bstep (se 1 (by rfl) ⟨879209, by rfl⟩ : syracuseStep 1172279 = 1758419) B1758419
theorem B1565495 : Blo 694316 1565495 := bstep (se 1 (by rfl) ⟨1174121, by rfl⟩ : syracuseStep 1565495 = 2348243) B2348243
theorem B7529273 : Blo 694316 7529273 := bstep (se 2 (by rfl) ⟨2823477, by rfl⟩ : syracuseStep 7529273 = 5646955) B5646955
theorem B1565675 : Blo 694316 1565675 := bstep (se 1 (by rfl) ⟨1174256, by rfl⟩ : syracuseStep 1565675 = 2348513) B2348513
theorem B2516041 : Blo 694316 2516041 := bstep (se 2 (by rfl) ⟨943515, by rfl⟩ : syracuseStep 2516041 = 1887031) B1887031
theorem B1041575 : Blo 694316 1041575 := bstep (se 1 (by rfl) ⟨781181, by rfl⟩ : syracuseStep 1041575 = 1562363) B1562363
theorem B1566107 : Blo 694316 1566107 := bstep (se 1 (by rfl) ⟨1174580, by rfl⟩ : syracuseStep 1566107 = 2349161) B2349161
theorem B52159949 : Blo 694316 52159949 := bstep (se 3 (by rfl) ⟨9779990, by rfl⟩ : syracuseStep 52159949 = 19559981) B19559981
theorem B3532247 : Blo 694316 3532247 := bstep (se 1 (by rfl) ⟨2649185, by rfl⟩ : syracuseStep 3532247 = 5298371) B5298371
theorem B1041947 : Blo 694316 1041947 := bstep (se 1 (by rfl) ⟨781460, by rfl⟩ : syracuseStep 1041947 = 1562921) B1562921
theorem B1762843 : Blo 694316 1762843 := bstep (se 1 (by rfl) ⟨1322132, by rfl⟩ : syracuseStep 1762843 = 2644265) B2644265
theorem B9528965 : Blo 694316 9528965 := bstep (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) B1786681
theorem B8906557 : Blo 694316 8906557 := bstep (se 3 (by rfl) ⟨1669979, by rfl⟩ : syracuseStep 8906557 = 3339959) B3339959
theorem B1042331 : Blo 694316 1042331 := bstep (se 1 (by rfl) ⟨781748, by rfl⟩ : syracuseStep 1042331 = 1563497) B1563497
theorem B1042367 : Blo 694316 1042367 := bstep (se 1 (by rfl) ⟨781775, by rfl⟩ : syracuseStep 1042367 = 1563551) B1563551
theorem B2975687 : Blo 694316 2975687 := bstep (se 1 (by rfl) ⟨2231765, by rfl⟩ : syracuseStep 2975687 = 4463531) B4463531
theorem B1566683 : Blo 694316 1566683 := bstep (se 1 (by rfl) ⟨1175012, by rfl⟩ : syracuseStep 1566683 = 2350025) B2350025
theorem B2975723 : Blo 694316 2975723 := bstep (se 1 (by rfl) ⟨2231792, by rfl⟩ : syracuseStep 2975723 = 4463585) B4463585
theorem B2385899 : Blo 694316 2385899 := bstep (se 1 (by rfl) ⟨1789424, by rfl⟩ : syracuseStep 2385899 = 3578849) B3578849
theorem B5302259 : Blo 694316 5302259 := bstep (se 1 (by rfl) ⟨3976694, by rfl⟩ : syracuseStep 5302259 = 7953389) B7953389
theorem B1042553 : Blo 694316 1042553 := bstep (se 2 (by rfl) ⟨390957, by rfl⟩ : syracuseStep 1042553 = 781915) B781915
theorem B1566863 : Blo 694316 1566863 := bstep (se 1 (by rfl) ⟨1175147, by rfl⟩ : syracuseStep 1566863 = 2350295) B2350295
theorem B1763471 : Blo 694316 1763471 := bstep (se 1 (by rfl) ⟨1322603, by rfl⟩ : syracuseStep 1763471 = 2645207) B2645207
theorem B1566953 : Blo 694316 1566953 := bstep (se 2 (by rfl) ⟨587607, by rfl⟩ : syracuseStep 1566953 = 1175215) B1175215
theorem B1174007 : Blo 694316 1174007 := bstep (se 1 (by rfl) ⟨880505, by rfl⟩ : syracuseStep 1174007 = 1761011) B1761011
theorem B1567223 : Blo 694316 1567223 := bstep (se 1 (by rfl) ⟨1175417, by rfl⟩ : syracuseStep 1567223 = 2350835) B2350835
theorem B1042937 : Blo 694316 1042937 := bstep (se 2 (by rfl) ⟨391101, by rfl⟩ : syracuseStep 1042937 = 782203) B782203
theorem B1042991 : Blo 694316 1042991 := bstep (se 1 (by rfl) ⟨782243, by rfl⟩ : syracuseStep 1042991 = 1564487) B1564487
theorem B1043423 : Blo 694316 1043423 := bstep (se 1 (by rfl) ⟨782567, by rfl⟩ : syracuseStep 1043423 = 1565135) B1565135
theorem B781375 : Blo 694316 781375 := bstep (se 1 (by rfl) ⟨586031, by rfl⟩ : syracuseStep 781375 = 1172063) B1172063
theorem B1174601 : Blo 694316 1174601 := bstep (se 2 (by rfl) ⟨440475, by rfl⟩ : syracuseStep 1174601 = 880951) B880951
theorem B1567817 : Blo 694316 1567817 := bstep (se 2 (by rfl) ⟨587931, by rfl⟩ : syracuseStep 1567817 = 1175863) B1175863
theorem B2354345 : Blo 694316 2354345 := bstep (se 2 (by rfl) ⟨882879, by rfl⟩ : syracuseStep 2354345 = 1765759) B1765759
theorem B1043867 : Blo 694316 1043867 := bstep (se 1 (by rfl) ⟨782900, by rfl⟩ : syracuseStep 1043867 = 1565801) B1565801
theorem B2354939 : Blo 694316 2354939 := bstep (se 1 (by rfl) ⟨1766204, by rfl⟩ : syracuseStep 2354939 = 3532409) B3532409
theorem B21491513 : Blo 694316 21491513 := bstep (se 2 (by rfl) ⟨8059317, by rfl⟩ : syracuseStep 21491513 = 16118635) B16118635
theorem B1044287 : Blo 694316 1044287 := bstep (se 1 (by rfl) ⟨783215, by rfl⟩ : syracuseStep 1044287 = 1566431) B1566431
theorem B1044473 : Blo 694316 1044473 := bstep (se 2 (by rfl) ⟨391677, by rfl⟩ : syracuseStep 1044473 = 783355) B783355
theorem B782491 : Blo 694316 782491 := bstep (se 1 (by rfl) ⟨586868, by rfl⟩ : syracuseStep 782491 = 1173737) B1173737
theorem B1044713 : Blo 694316 1044713 := bstep (se 2 (by rfl) ⟨391767, by rfl⟩ : syracuseStep 1044713 = 783535) B783535
theorem B1044839 : Blo 694316 1044839 := bstep (se 1 (by rfl) ⟨783629, by rfl⟩ : syracuseStep 1044839 = 1567259) B1567259
theorem B3961295 : Blo 694316 3961295 := bstep (se 1 (by rfl) ⟨2970971, by rfl⟩ : syracuseStep 3961295 = 5941943) B5941943
theorem B2650583 : Blo 694316 2650583 := bstep (se 1 (by rfl) ⟨1987937, by rfl⟩ : syracuseStep 2650583 = 3975875) B3975875
theorem B1569545 : Blo 694316 1569545 := bstep (se 2 (by rfl) ⟨588579, by rfl⟩ : syracuseStep 1569545 = 1177159) B1177159
theorem B1176383 : Blo 694316 1176383 := bstep (se 1 (by rfl) ⟨882287, by rfl⟩ : syracuseStep 1176383 = 1764575) B1764575
theorem B1569599 : Blo 694316 1569599 := bstep (se 1 (by rfl) ⟨1177199, by rfl⟩ : syracuseStep 1569599 = 2354399) B2354399
theorem B1045385 : Blo 694316 1045385 := bstep (se 2 (by rfl) ⟨392019, by rfl⟩ : syracuseStep 1045385 = 784039) B784039
theorem B1176457 : Blo 694316 1176457 := bstep (se 2 (by rfl) ⟨441171, by rfl⟩ : syracuseStep 1176457 = 882343) B882343
theorem B1569743 : Blo 694316 1569743 := bstep (se 1 (by rfl) ⟨1177307, by rfl⟩ : syracuseStep 1569743 = 2354615) B2354615
theorem B2978831 : Blo 694316 2978831 := bstep (se 1 (by rfl) ⟨2234123, by rfl⟩ : syracuseStep 2978831 = 4468247) B4468247
theorem B1569833 : Blo 694316 1569833 := bstep (se 2 (by rfl) ⟨588687, by rfl⟩ : syracuseStep 1569833 = 1177375) B1177375
theorem B1274951 : Blo 694316 1274951 := bstep (se 1 (by rfl) ⟨956213, by rfl⟩ : syracuseStep 1274951 = 1912427) B1912427
theorem B1045769 : Blo 694316 1045769 := bstep (se 2 (by rfl) ⟨392163, by rfl⟩ : syracuseStep 1045769 = 784327) B784327
theorem B783679 : Blo 694316 783679 := bstep (se 1 (by rfl) ⟨587759, by rfl⟩ : syracuseStep 783679 = 1175519) B1175519
theorem B1045823 : Blo 694316 1045823 := bstep (se 1 (by rfl) ⟨784367, by rfl⟩ : syracuseStep 1045823 = 1568735) B1568735
theorem B1570121 : Blo 694316 1570121 := bstep (se 2 (by rfl) ⟨588795, by rfl⟩ : syracuseStep 1570121 = 1177591) B1177591
theorem B3339731 : Blo 694316 3339731 := bstep (se 1 (by rfl) ⟨2504798, by rfl⟩ : syracuseStep 3339731 = 5009597) B5009597
theorem B1046249 : Blo 694316 1046249 := bstep (se 2 (by rfl) ⟨392343, by rfl⟩ : syracuseStep 1046249 = 784687) B784687
theorem B1177321 : Blo 694316 1177321 := bstep (se 2 (by rfl) ⟨441495, by rfl⟩ : syracuseStep 1177321 = 882991) B882991
theorem B784111 : Blo 694316 784111 := bstep (se 1 (by rfl) ⟨588083, by rfl⟩ : syracuseStep 784111 = 1176167) B1176167
theorem B1046255 : Blo 694316 1046255 := bstep (se 1 (by rfl) ⟨784691, by rfl⟩ : syracuseStep 1046255 = 1569383) B1569383
theorem B2815823 : Blo 694316 2815823 := bstep (se 1 (by rfl) ⟨2111867, by rfl⟩ : syracuseStep 2815823 = 4223735) B4223735
theorem B784219 : Blo 694316 784219 := bstep (se 1 (by rfl) ⟨588164, by rfl⟩ : syracuseStep 784219 = 1176329) B1176329
theorem B2226359 : Blo 694316 2226359 := bstep (se 1 (by rfl) ⟨1669769, by rfl⟩ : syracuseStep 2226359 = 3339539) B3339539
theorem B1046711 : Blo 694316 1046711 := bstep (se 1 (by rfl) ⟨785033, by rfl⟩ : syracuseStep 1046711 = 1570067) B1570067
theorem B784615 : Blo 694316 784615 := bstep (se 1 (by rfl) ⟨588461, by rfl⟩ : syracuseStep 784615 = 1176923) B1176923
theorem B1046759 : Blo 694316 1046759 := bstep (se 1 (by rfl) ⟨785069, by rfl⟩ : syracuseStep 1046759 = 1570139) B1570139
theorem B1571111 : Blo 694316 1571111 := bstep (se 1 (by rfl) ⟨1178333, by rfl⟩ : syracuseStep 1571111 = 2356667) B2356667
theorem B1047131 : Blo 694316 1047131 := bstep (se 1 (by rfl) ⟨785348, by rfl⟩ : syracuseStep 1047131 = 1570697) B1570697
theorem B1047275 : Blo 694316 1047275 := bstep (se 1 (by rfl) ⟨785456, by rfl⟩ : syracuseStep 1047275 = 1570913) B1570913
theorem B1178347 : Blo 694316 1178347 := bstep (se 1 (by rfl) ⟨883760, by rfl⟩ : syracuseStep 1178347 = 1767521) B1767521
theorem B1047305 : Blo 694316 1047305 := bstep (se 2 (by rfl) ⟨392739, by rfl⟩ : syracuseStep 1047305 = 785479) B785479
theorem B785263 : Blo 694316 785263 := bstep (se 1 (by rfl) ⟨588947, by rfl⟩ : syracuseStep 785263 = 1177895) B1177895
theorem B2063261 : Blo 694316 2063261 := bstep (se 3 (by rfl) ⟨386861, by rfl⟩ : syracuseStep 2063261 = 773723) B773723
theorem B2981087 : Blo 694316 2981087 := bstep (se 1 (by rfl) ⟨2235815, by rfl⟩ : syracuseStep 2981087 = 4471631) B4471631
theorem B3341999 : Blo 694316 3341999 := bstep (se 1 (by rfl) ⟨2506499, by rfl⟩ : syracuseStep 3341999 = 5012999) B5012999
theorem B4457227 : Blo 694316 4457227 := bstep (se 1 (by rfl) ⟨3342920, by rfl⟩ : syracuseStep 4457227 = 6685841) B6685841
theorem B32605199 : Blo 694316 32605199 := bstep (se 1 (by rfl) ⟨24453899, by rfl⟩ : syracuseStep 32605199 = 48907799) B48907799
theorem B4228307 : Blo 694316 4228307 := bstep (se 1 (by rfl) ⟨3171230, by rfl⟩ : syracuseStep 4228307 = 6342461) B6342461
theorem B2229601 : Blo 694316 2229601 := bstep (se 2 (by rfl) ⟨836100, by rfl⟩ : syracuseStep 2229601 = 1672201) B1672201
theorem B14452091 : Blo 694316 14452091 := bstep (se 1 (by rfl) ⟨10839068, by rfl⟩ : syracuseStep 14452091 = 21678137) B21678137
theorem B2230535 : Blo 694316 2230535 := bstep (se 1 (by rfl) ⟨1672901, by rfl⟩ : syracuseStep 2230535 = 3345803) B3345803
theorem B60229979 : Blo 694316 60229979 := bstep (se 1 (by rfl) ⟨45172484, by rfl⟩ : syracuseStep 60229979 = 90344969) B90344969
theorem B1117415 : Blo 694316 1117415 := bstep (se 1 (by rfl) ⟨838061, by rfl⟩ : syracuseStep 1117415 = 1676123) B1676123
theorem B15045041 : Blo 694316 15045041 := bstep (se 2 (by rfl) ⟨5641890, by rfl⟩ : syracuseStep 15045041 = 11283781) B11283781
theorem B1675823 : Blo 694316 1675823 := bstep (se 1 (by rfl) ⟨1256867, by rfl⟩ : syracuseStep 1675823 = 2513735) B2513735
theorem B7508861 : Blo 694316 7508861 := bstep (se 3 (by rfl) ⟨1407911, by rfl⟩ : syracuseStep 7508861 = 2815823) B2815823
theorem B2233919 : Blo 694316 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B3970727 : Blo 694316 3970727 := bstep (se 1 (by rfl) ⟨2978045, by rfl⟩ : syracuseStep 3970727 = 5956091) B5956091
theorem B5019515 : Blo 694316 5019515 := bstep (se 1 (by rfl) ⟨3764636, by rfl⟩ : syracuseStep 5019515 = 7529273) B7529273
theorem B694383 : Blo 694316 694383 := bstep (se 1 (by rfl) ⟨520787, by rfl⟩ : syracuseStep 694383 = 1041575) B1041575
theorem B7542895 : Blo 694316 7542895 := bstep (se 1 (by rfl) ⟨5657171, by rfl⟩ : syracuseStep 7542895 = 11314343) B11314343
theorem B34773299 : Blo 694316 34773299 := bstep (se 1 (by rfl) ⟨26079974, by rfl⟩ : syracuseStep 34773299 = 52159949) B52159949
theorem B694631 : Blo 694316 694631 := bstep (se 1 (by rfl) ⟨520973, by rfl⟩ : syracuseStep 694631 = 1041947) B1041947
theorem B67901975 : Blo 694316 67901975 := bstep (se 1 (by rfl) ⟨50926481, by rfl⟩ : syracuseStep 67901975 = 101852963) B101852963
theorem B694887 : Blo 694316 694887 := bstep (se 1 (by rfl) ⟨521165, by rfl⟩ : syracuseStep 694887 = 1042331) B1042331
theorem B694911 : Blo 694316 694911 := bstep (se 1 (by rfl) ⟨521183, by rfl⟩ : syracuseStep 694911 = 1042367) B1042367
theorem B695035 : Blo 694316 695035 := bstep (se 1 (by rfl) ⟨521276, by rfl⟩ : syracuseStep 695035 = 1042553) B1042553
theorem B990073 : Blo 694316 990073 := bstep (se 2 (by rfl) ⟨371277, by rfl⟩ : syracuseStep 990073 = 742555) B742555
theorem B695291 : Blo 694316 695291 := bstep (se 1 (by rfl) ⟨521468, by rfl⟩ : syracuseStep 695291 = 1042937) B1042937
theorem B695327 : Blo 694316 695327 := bstep (se 1 (by rfl) ⟨521495, by rfl⟩ : syracuseStep 695327 = 1042991) B1042991
theorem B3349687 : Blo 694316 3349687 := bstep (se 1 (by rfl) ⟨2512265, by rfl⟩ : syracuseStep 3349687 = 5024531) B5024531
theorem B1318207 : Blo 694316 1318207 := bstep (se 1 (by rfl) ⟨988655, by rfl⟩ : syracuseStep 1318207 = 1977311) B1977311
theorem B695615 : Blo 694316 695615 := bstep (se 1 (by rfl) ⟨521711, by rfl⟩ : syracuseStep 695615 = 1043423) B1043423
theorem B5709403 : Blo 694316 5709403 := bstep (se 1 (by rfl) ⟨4282052, by rfl⟩ : syracuseStep 5709403 = 8564105) B8564105
theorem B695911 : Blo 694316 695911 := bstep (se 1 (by rfl) ⟨521933, by rfl⟩ : syracuseStep 695911 = 1043867) B1043867
theorem B14327675 : Blo 694316 14327675 := bstep (se 1 (by rfl) ⟨10745756, by rfl⟩ : syracuseStep 14327675 = 21491513) B21491513
theorem B696191 : Blo 694316 696191 := bstep (se 1 (by rfl) ⟨522143, by rfl⟩ : syracuseStep 696191 = 1044287) B1044287
theorem B4464557 : Blo 694316 4464557 := bstep (se 3 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 4464557 = 1674209) B1674209
theorem B8921015 : Blo 694316 8921015 := bstep (se 1 (by rfl) ⟨6690761, by rfl⟩ : syracuseStep 8921015 = 13381523) B13381523
theorem B991207 : Blo 694316 991207 := bstep (se 1 (by rfl) ⟨743405, by rfl⟩ : syracuseStep 991207 = 1486811) B1486811
theorem B696315 : Blo 694316 696315 := bstep (se 1 (by rfl) ⟨522236, by rfl⟩ : syracuseStep 696315 = 1044473) B1044473
theorem B696475 : Blo 694316 696475 := bstep (se 1 (by rfl) ⟨522356, by rfl⟩ : syracuseStep 696475 = 1044713) B1044713
theorem B1319095 : Blo 694316 1319095 := bstep (se 1 (by rfl) ⟨989321, by rfl⟩ : syracuseStep 1319095 = 1978643) B1978643
theorem B696559 : Blo 694316 696559 := bstep (se 1 (by rfl) ⟨522419, by rfl⟩ : syracuseStep 696559 = 1044839) B1044839
theorem B696923 : Blo 694316 696923 := bstep (se 1 (by rfl) ⟨522692, by rfl⟩ : syracuseStep 696923 = 1045385) B1045385
theorem B11871035 : Blo 694316 11871035 := bstep (se 1 (by rfl) ⟨8903276, by rfl⟩ : syracuseStep 11871035 = 17806553) B17806553
theorem B697179 : Blo 694316 697179 := bstep (se 1 (by rfl) ⟨522884, by rfl⟩ : syracuseStep 697179 = 1045769) B1045769
theorem B697215 : Blo 694316 697215 := bstep (se 1 (by rfl) ⟨522911, by rfl⟩ : syracuseStep 697215 = 1045823) B1045823
theorem B24454187 : Blo 694316 24454187 := bstep (se 1 (by rfl) ⟨18340640, by rfl⟩ : syracuseStep 24454187 = 36681281) B36681281
theorem B697499 : Blo 694316 697499 := bstep (se 1 (by rfl) ⟨523124, by rfl⟩ : syracuseStep 697499 = 1046249) B1046249
theorem B697503 : Blo 694316 697503 := bstep (se 1 (by rfl) ⟨523127, by rfl⟩ : syracuseStep 697503 = 1046255) B1046255
theorem B20129147 : Blo 694316 20129147 := bstep (se 1 (by rfl) ⟨15096860, by rfl⟩ : syracuseStep 20129147 = 30193721) B30193721
theorem B1484239 : Blo 694316 1484239 := bstep (se 1 (by rfl) ⟨1113179, by rfl⟩ : syracuseStep 1484239 = 2226359) B2226359
theorem B697807 : Blo 694316 697807 := bstep (se 1 (by rfl) ⟨523355, by rfl⟩ : syracuseStep 697807 = 1046711) B1046711
theorem B697839 : Blo 694316 697839 := bstep (se 1 (by rfl) ⟨523379, by rfl⟩ : syracuseStep 697839 = 1046759) B1046759
theorem B11478515 : Blo 694316 11478515 := bstep (se 1 (by rfl) ⟨8608886, by rfl⟩ : syracuseStep 11478515 = 17217773) B17217773
theorem B1320553 : Blo 694316 1320553 := bstep (se 2 (by rfl) ⟨495207, by rfl⟩ : syracuseStep 1320553 = 990415) B990415
theorem B698087 : Blo 694316 698087 := bstep (se 1 (by rfl) ⟨523565, by rfl⟩ : syracuseStep 698087 = 1047131) B1047131
theorem B698183 : Blo 694316 698183 := bstep (se 1 (by rfl) ⟨523637, by rfl⟩ : syracuseStep 698183 = 1047275) B1047275
theorem B698203 : Blo 694316 698203 := bstep (se 1 (by rfl) ⟨523652, by rfl⟩ : syracuseStep 698203 = 1047305) B1047305
theorem B3975101 : Blo 694316 3975101 := bstep (se 3 (by rfl) ⟨745331, by rfl⟩ : syracuseStep 3975101 = 1490663) B1490663
theorem B1321343 : Blo 694316 1321343 := bstep (se 1 (by rfl) ⟨991007, by rfl⟩ : syracuseStep 1321343 = 1982015) B1982015
theorem B1977527 : Blo 694316 1977527 := bstep (se 1 (by rfl) ⟨1483145, by rfl⟩ : syracuseStep 1977527 = 2966291) B2966291
theorem B1486127 : Blo 694316 1486127 := bstep (se 1 (by rfl) ⟨1114595, by rfl⟩ : syracuseStep 1486127 = 2229191) B2229191
theorem B13348151 : Blo 694316 13348151 := bstep (se 1 (by rfl) ⟨10011113, by rfl⟩ : syracuseStep 13348151 = 20022227) B20022227
theorem B1256825 : Blo 694316 1256825 := bstep (se 2 (by rfl) ⟨471309, by rfl⟩ : syracuseStep 1256825 = 942619) B942619
theorem B1322399 : Blo 694316 1322399 := bstep (se 1 (by rfl) ⟨991799, by rfl⟩ : syracuseStep 1322399 = 1983599) B1983599
theorem B1977767 : Blo 694316 1977767 := bstep (se 1 (by rfl) ⟨1483325, by rfl⟩ : syracuseStep 1977767 = 2966651) B2966651
theorem B20328131 : Blo 694316 20328131 := bstep (se 1 (by rfl) ⟨15246098, by rfl⟩ : syracuseStep 20328131 = 30492197) B30492197
theorem B5648201 : Blo 694316 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B5418971 : Blo 694316 5418971 := bstep (se 1 (by rfl) ⟨4064228, by rfl⟩ : syracuseStep 5418971 = 8128457) B8128457
theorem B1486955 : Blo 694316 1486955 := bstep (se 1 (by rfl) ⟨1115216, by rfl⟩ : syracuseStep 1486955 = 2230433) B2230433
theorem B1979167 : Blo 694316 1979167 := bstep (se 1 (by rfl) ⟨1484375, by rfl⟩ : syracuseStep 1979167 = 2968751) B2968751
theorem B1979417 : Blo 694316 1979417 := bstep (se 2 (by rfl) ⟨742281, by rfl⟩ : syracuseStep 1979417 = 1484563) B1484563
theorem B11875409 : Blo 694316 11875409 := bstep (se 2 (by rfl) ⟨4453278, by rfl⟩ : syracuseStep 11875409 = 8906557) B8906557
theorem B7156943 : Blo 694316 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B3519773 : Blo 694316 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B3487043 : Blo 694316 3487043 := bstep (se 1 (by rfl) ⟨2615282, by rfl⟩ : syracuseStep 3487043 = 5230565) B5230565
theorem B5649911 : Blo 694316 5649911 := bstep (se 1 (by rfl) ⟨4237433, by rfl⟩ : syracuseStep 5649911 = 8474867) B8474867
theorem B3520907 : Blo 694316 3520907 := bstep (se 1 (by rfl) ⟨2640680, by rfl⟩ : syracuseStep 3520907 = 5281361) B5281361
theorem B10730485 : Blo 694316 10730485 := bstep (se 5 (by rfl) ⟨502991, by rfl⟩ : syracuseStep 10730485 = 1005983) B1005983
theorem B1981513 : Blo 694316 1981513 := bstep (se 2 (by rfl) ⟨743067, by rfl⟩ : syracuseStep 1981513 = 1486135) B1486135
theorem B5881643 : Blo 694316 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B4472657 : Blo 694316 4472657 := bstep (se 2 (by rfl) ⟨1677246, by rfl⟩ : syracuseStep 4472657 = 3354493) B3354493
theorem B3522527 : Blo 694316 3522527 := bstep (se 1 (by rfl) ⟨2641895, by rfl⟩ : syracuseStep 3522527 = 5283791) B5283791
theorem B13418885 : Blo 694316 13418885 := bstep (se 4 (by rfl) ⟨1258020, by rfl⟩ : syracuseStep 13418885 = 2516041) B2516041
theorem B2343383 : Blo 694316 2343383 := bstep (se 1 (by rfl) ⟨1757537, by rfl⟩ : syracuseStep 2343383 = 3515075) B3515075
theorem B4244071 : Blo 694316 4244071 := bstep (se 1 (by rfl) ⟨3183053, by rfl⟩ : syracuseStep 4244071 = 6366107) B6366107
theorem B1983791 : Blo 694316 1983791 := bstep (se 1 (by rfl) ⟨1487843, by rfl⟩ : syracuseStep 1983791 = 2975687) B2975687
theorem B1983815 : Blo 694316 1983815 := bstep (se 1 (by rfl) ⟨1487861, by rfl⟩ : syracuseStep 1983815 = 2975723) B2975723
theorem B1590599 : Blo 694316 1590599 := bstep (se 1 (by rfl) ⟨1192949, by rfl⟩ : syracuseStep 1590599 = 2385899) B2385899
theorem B3524147 : Blo 694316 3524147 := bstep (se 1 (by rfl) ⟨2643110, by rfl⟩ : syracuseStep 3524147 = 5286221) B5286221
theorem B4769543 : Blo 694316 4769543 := bstep (se 1 (by rfl) ⟨3577157, by rfl⟩ : syracuseStep 4769543 = 7154315) B7154315
theorem B13420889 : Blo 694316 13420889 := bstep (se 2 (by rfl) ⟨5032833, by rfl⟩ : syracuseStep 13420889 = 10065667) B10065667
theorem B1886591 : Blo 694316 1886591 := bstep (se 1 (by rfl) ⟨1414943, by rfl⟩ : syracuseStep 1886591 = 2829887) B2829887
theorem B3525281 : Blo 694316 3525281 := bstep (se 2 (by rfl) ⟨1321980, by rfl⟩ : syracuseStep 3525281 = 2643961) B2643961
theorem B1985249 : Blo 694316 1985249 := bstep (se 2 (by rfl) ⟨744468, by rfl⟩ : syracuseStep 1985249 = 1488937) B1488937
theorem B2640863 : Blo 694316 2640863 := bstep (se 1 (by rfl) ⟨1980647, by rfl⟩ : syracuseStep 2640863 = 3961295) B3961295
theorem B3525767 : Blo 694316 3525767 := bstep (se 1 (by rfl) ⟨2644325, by rfl⟩ : syracuseStep 3525767 = 5288651) B5288651
theorem B1985887 : Blo 694316 1985887 := bstep (se 1 (by rfl) ⟨1489415, by rfl⟩ : syracuseStep 1985887 = 2978831) B2978831
theorem B2347055 : Blo 694316 2347055 := bstep (se 1 (by rfl) ⟨1760291, by rfl⟩ : syracuseStep 2347055 = 3520583) B3520583
theorem B1757639 : Blo 694316 1757639 := bstep (se 1 (by rfl) ⟨1318229, by rfl⟩ : syracuseStep 1757639 = 2636459) B2636459
theorem B7918397 : Blo 694316 7918397 := bstep (se 3 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 7918397 = 2969399) B2969399
theorem B1987391 : Blo 694316 1987391 := bstep (se 1 (by rfl) ⟨1490543, by rfl⟩ : syracuseStep 1987391 = 2981087) B2981087
theorem B6018583 : Blo 694316 6018583 := bstep (se 1 (by rfl) ⟨4513937, by rfl⟩ : syracuseStep 6018583 = 9027875) B9027875
theorem B3528359 : Blo 694316 3528359 := bstep (se 1 (by rfl) ⟨2646269, by rfl⟩ : syracuseStep 3528359 = 5292539) B5292539
theorem B1070761 : Blo 694316 1070761 := bstep (se 2 (by rfl) ⟨401535, by rfl⟩ : syracuseStep 1070761 = 803071) B803071
theorem B9164731 : Blo 694316 9164731 := bstep (se 1 (by rfl) ⟨6873548, by rfl⟩ : syracuseStep 9164731 = 13747097) B13747097
theorem B1759583 : Blo 694316 1759583 := bstep (se 1 (by rfl) ⟨1319687, by rfl⟩ : syracuseStep 1759583 = 2639375) B2639375
theorem B6674845 : Blo 694316 6674845 := bstep (se 3 (by rfl) ⟨1251533, by rfl⟩ : syracuseStep 6674845 = 2503067) B2503067
theorem B7133629 : Blo 694316 7133629 := bstep (se 3 (by rfl) ⟨1337555, by rfl⟩ : syracuseStep 7133629 = 2675111) B2675111
theorem B1760363 : Blo 694316 1760363 := bstep (se 1 (by rfl) ⟨1320272, by rfl⟩ : syracuseStep 1760363 = 2640545) B2640545
theorem B3529979 : Blo 694316 3529979 := bstep (se 1 (by rfl) ⟨2647484, by rfl⟩ : syracuseStep 3529979 = 5294969) B5294969
theorem B2350457 : Blo 694316 2350457 := bstep (se 2 (by rfl) ⟨881421, by rfl⟩ : syracuseStep 2350457 = 1762843) B1762843
theorem B2645723 : Blo 694316 2645723 := bstep (se 1 (by rfl) ⟨1984292, by rfl⟩ : syracuseStep 2645723 = 3968585) B3968585
theorem B2580191 : Blo 694316 2580191 := bstep (se 1 (by rfl) ⟨1935143, by rfl⟩ : syracuseStep 2580191 = 3870287) B3870287
theorem B2547667 : Blo 694316 2547667 := bstep (se 1 (by rfl) ⟨1910750, by rfl⟩ : syracuseStep 2547667 = 3821501) B3821501
theorem B1564775 : Blo 694316 1564775 := bstep (se 1 (by rfl) ⟨1173581, by rfl⟩ : syracuseStep 1564775 = 2347163) B2347163
theorem B13394281 : Blo 694316 13394281 := bstep (se 2 (by rfl) ⟨5022855, by rfl⟩ : syracuseStep 13394281 = 10045711) B10045711
theorem B942457 : Blo 694316 942457 := bstep (se 2 (by rfl) ⟨353421, by rfl⟩ : syracuseStep 942457 = 706843) B706843
theorem B1041599 : Blo 694316 1041599 := bstep (se 1 (by rfl) ⟨781199, by rfl⟩ : syracuseStep 1041599 = 1562399) B1562399
theorem B2352347 : Blo 694316 2352347 := bstep (se 1 (by rfl) ⟨1764260, by rfl⟩ : syracuseStep 2352347 = 3528521) B3528521
theorem B1172711 : Blo 694316 1172711 := bstep (se 1 (by rfl) ⟨879533, by rfl⟩ : syracuseStep 1172711 = 1759067) B1759067
theorem B1565927 : Blo 694316 1565927 := bstep (se 1 (by rfl) ⟨1174445, by rfl⟩ : syracuseStep 1565927 = 2348891) B2348891
theorem B1041743 : Blo 694316 1041743 := bstep (se 1 (by rfl) ⟨781307, by rfl⟩ : syracuseStep 1041743 = 1562615) B1562615
theorem B1041833 : Blo 694316 1041833 := bstep (se 2 (by rfl) ⟨390687, by rfl⟩ : syracuseStep 1041833 = 781375) B781375
theorem B3007975 : Blo 694316 3007975 := bstep (se 1 (by rfl) ⟨2255981, by rfl⟩ : syracuseStep 3007975 = 4511963) B4511963
theorem B1041983 : Blo 694316 1041983 := bstep (se 1 (by rfl) ⟨781487, by rfl⟩ : syracuseStep 1041983 = 1562975) B1562975
theorem B1042343 : Blo 694316 1042343 := bstep (se 1 (by rfl) ⟨781757, by rfl⟩ : syracuseStep 1042343 = 1563515) B1563515
theorem B1042463 : Blo 694316 1042463 := bstep (se 1 (by rfl) ⟨781847, by rfl⟩ : syracuseStep 1042463 = 1563695) B1563695
theorem B2353211 : Blo 694316 2353211 := bstep (se 1 (by rfl) ⟨1764908, by rfl⟩ : syracuseStep 2353211 = 3529817) B3529817
theorem B3532895 : Blo 694316 3532895 := bstep (se 1 (by rfl) ⟨2649671, by rfl⟩ : syracuseStep 3532895 = 5299343) B5299343
theorem B1042919 : Blo 694316 1042919 := bstep (se 1 (by rfl) ⟨782189, by rfl⟩ : syracuseStep 1042919 = 1564379) B1564379
theorem B1043099 : Blo 694316 1043099 := bstep (se 1 (by rfl) ⟨782324, by rfl⟩ : syracuseStep 1043099 = 1564649) B1564649
theorem B1338203 : Blo 694316 1338203 := bstep (se 1 (by rfl) ⟨1003652, by rfl⟩ : syracuseStep 1338203 = 2007305) B2007305
theorem B1043321 : Blo 694316 1043321 := bstep (se 2 (by rfl) ⟨391245, by rfl⟩ : syracuseStep 1043321 = 782491) B782491
theorem B17165195 : Blo 694316 17165195 := bstep (se 1 (by rfl) ⟨12873896, by rfl⟩ : syracuseStep 17165195 = 25747793) B25747793
theorem B1043567 : Blo 694316 1043567 := bstep (se 1 (by rfl) ⟨782675, by rfl⟩ : syracuseStep 1043567 = 1565351) B1565351
theorem B1764463 : Blo 694316 1764463 := bstep (se 1 (by rfl) ⟨1323347, by rfl⟩ : syracuseStep 1764463 = 2646695) B2646695
theorem B781519 : Blo 694316 781519 := bstep (se 1 (by rfl) ⟨586139, by rfl⟩ : syracuseStep 781519 = 1172279) B1172279
theorem B1043663 : Blo 694316 1043663 := bstep (se 1 (by rfl) ⟨782747, by rfl⟩ : syracuseStep 1043663 = 1565495) B1565495
theorem B3960089 : Blo 694316 3960089 := bstep (se 2 (by rfl) ⟨1485033, by rfl⟩ : syracuseStep 3960089 = 2970067) B2970067
theorem B1043783 : Blo 694316 1043783 := bstep (se 1 (by rfl) ⟨782837, by rfl⟩ : syracuseStep 1043783 = 1565675) B1565675
theorem B1044071 : Blo 694316 1044071 := bstep (se 1 (by rfl) ⟨783053, by rfl⟩ : syracuseStep 1044071 = 1566107) B1566107
theorem B2354831 : Blo 694316 2354831 := bstep (se 1 (by rfl) ⟨1766123, by rfl⟩ : syracuseStep 2354831 = 3532247) B3532247
theorem B6352643 : Blo 694316 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B1568609 : Blo 694316 1568609 := bstep (se 2 (by rfl) ⟨588228, by rfl⟩ : syracuseStep 1568609 = 1176457) B1176457
theorem B1044455 : Blo 694316 1044455 := bstep (se 1 (by rfl) ⟨783341, by rfl⟩ : syracuseStep 1044455 = 1566683) B1566683
theorem B1208297 : Blo 694316 1208297 := bstep (se 2 (by rfl) ⟨453111, by rfl⟩ : syracuseStep 1208297 = 906223) B906223
theorem B3534839 : Blo 694316 3534839 := bstep (se 1 (by rfl) ⟨2651129, by rfl⟩ : syracuseStep 3534839 = 5302259) B5302259
theorem B1044575 : Blo 694316 1044575 := bstep (se 1 (by rfl) ⟨783431, by rfl⟩ : syracuseStep 1044575 = 1566863) B1566863
theorem B1175647 : Blo 694316 1175647 := bstep (se 1 (by rfl) ⟨881735, by rfl⟩ : syracuseStep 1175647 = 1763471) B1763471
theorem B1044635 : Blo 694316 1044635 := bstep (se 1 (by rfl) ⟨783476, by rfl⟩ : syracuseStep 1044635 = 1566953) B1566953
theorem B782671 : Blo 694316 782671 := bstep (se 1 (by rfl) ⟨587003, by rfl⟩ : syracuseStep 782671 = 1174007) B1174007
theorem B1044815 : Blo 694316 1044815 := bstep (se 1 (by rfl) ⟨783611, by rfl⟩ : syracuseStep 1044815 = 1567223) B1567223
theorem B1044905 : Blo 694316 1044905 := bstep (se 2 (by rfl) ⟨391839, by rfl⟩ : syracuseStep 1044905 = 783679) B783679
theorem B76116469 : Blo 694316 76116469 := bstep (se 5 (by rfl) ⟨3567959, by rfl⟩ : syracuseStep 76116469 = 7135919) B7135919
theorem B783067 : Blo 694316 783067 := bstep (se 1 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 783067 = 1174601) B1174601
theorem B881371 : Blo 694316 881371 := bstep (se 1 (by rfl) ⟨661028, by rfl⟩ : syracuseStep 881371 = 1322057) B1322057
theorem B1045211 : Blo 694316 1045211 := bstep (se 1 (by rfl) ⟨783908, by rfl⟩ : syracuseStep 1045211 = 1567817) B1567817
theorem B1569563 : Blo 694316 1569563 := bstep (se 1 (by rfl) ⟨1177172, by rfl⟩ : syracuseStep 1569563 = 2354345) B2354345
theorem B1569761 : Blo 694316 1569761 := bstep (se 2 (by rfl) ⟨588660, by rfl⟩ : syracuseStep 1569761 = 1177321) B1177321
theorem B1045481 : Blo 694316 1045481 := bstep (se 2 (by rfl) ⟨392055, by rfl⟩ : syracuseStep 1045481 = 784111) B784111
theorem B1045625 : Blo 694316 1045625 := bstep (se 2 (by rfl) ⟨392109, by rfl⟩ : syracuseStep 1045625 = 784219) B784219
theorem B1668251 : Blo 694316 1668251 := bstep (se 1 (by rfl) ⟨1251188, by rfl⟩ : syracuseStep 1668251 = 2502377) B2502377
theorem B1569959 : Blo 694316 1569959 := bstep (se 1 (by rfl) ⟨1177469, by rfl⟩ : syracuseStep 1569959 = 2354939) B2354939
theorem B7927145 : Blo 694316 7927145 := bstep (se 2 (by rfl) ⟨2972679, by rfl⟩ : syracuseStep 7927145 = 5945359) B5945359
theorem B1046153 : Blo 694316 1046153 := bstep (se 2 (by rfl) ⟨392307, by rfl⟩ : syracuseStep 1046153 = 784615) B784615
theorem B1767055 : Blo 694316 1767055 := bstep (se 1 (by rfl) ⟨1325291, by rfl⟩ : syracuseStep 1767055 = 2650583) B2650583
theorem B1046363 : Blo 694316 1046363 := bstep (se 1 (by rfl) ⟨784772, by rfl⟩ : syracuseStep 1046363 = 1569545) B1569545
theorem B784255 : Blo 694316 784255 := bstep (se 1 (by rfl) ⟨588191, by rfl⟩ : syracuseStep 784255 = 1176383) B1176383
theorem B1046399 : Blo 694316 1046399 := bstep (se 1 (by rfl) ⟨784799, by rfl⟩ : syracuseStep 1046399 = 1569599) B1569599
theorem B3962753 : Blo 694316 3962753 := bstep (se 2 (by rfl) ⟨1486032, by rfl⟩ : syracuseStep 3962753 = 2972065) B2972065
theorem B1046495 : Blo 694316 1046495 := bstep (se 1 (by rfl) ⟨784871, by rfl⟩ : syracuseStep 1046495 = 1569743) B1569743
theorem B1046555 : Blo 694316 1046555 := bstep (se 1 (by rfl) ⟨784916, by rfl⟩ : syracuseStep 1046555 = 1569833) B1569833
theorem B849967 : Blo 694316 849967 := bstep (se 1 (by rfl) ⟨637475, by rfl⟩ : syracuseStep 849967 = 1274951) B1274951
theorem B1046747 : Blo 694316 1046747 := bstep (se 1 (by rfl) ⟨785060, by rfl⟩ : syracuseStep 1046747 = 1570121) B1570121
theorem B2226487 : Blo 694316 2226487 := bstep (se 1 (by rfl) ⟨1669865, by rfl⟩ : syracuseStep 2226487 = 3339731) B3339731
theorem B1571129 : Blo 694316 1571129 := bstep (se 2 (by rfl) ⟨589173, by rfl⟩ : syracuseStep 1571129 = 1178347) B1178347
theorem B1047017 : Blo 694316 1047017 := bstep (se 2 (by rfl) ⟨392631, by rfl⟩ : syracuseStep 1047017 = 785263) B785263
theorem B1047407 : Blo 694316 1047407 := bstep (se 1 (by rfl) ⟨785555, by rfl⟩ : syracuseStep 1047407 = 1571111) B1571111
theorem B1375507 : Blo 694316 1375507 := bstep (se 1 (by rfl) ⟨1031630, by rfl⟩ : syracuseStep 1375507 = 2063261) B2063261
theorem B1408495 : Blo 694316 1408495 := bstep (se 1 (by rfl) ⟨1056371, by rfl⟩ : syracuseStep 1408495 = 2112743) B2112743
theorem B2227999 : Blo 694316 2227999 := bstep (se 1 (by rfl) ⟨1670999, by rfl⟩ : syracuseStep 2227999 = 3341999) B3341999
theorem B3571577 : Blo 694316 3571577 := bstep (se 2 (by rfl) ⟨1339341, by rfl⟩ : syracuseStep 3571577 = 2678683) B2678683
theorem B8945923 : Blo 694316 8945923 := bstep (se 1 (by rfl) ⟨6709442, by rfl⟩ : syracuseStep 8945923 = 13418885) B13418885
theorem B3965213 : Blo 694316 3965213 := bstep (se 3 (by rfl) ⟨743477, by rfl⟩ : syracuseStep 3965213 = 1486955) B1486955
theorem B17859041 : Blo 694316 17859041 := bstep (se 2 (by rfl) ⟨6697140, by rfl⟩ : syracuseStep 17859041 = 13394281) B13394281
theorem B2818871 : Blo 694316 2818871 := bstep (se 1 (by rfl) ⟨2114153, by rfl⟩ : syracuseStep 2818871 = 4228307) B4228307
theorem B9634727 : Blo 694316 9634727 := bstep (se 1 (by rfl) ⟨7226045, by rfl⟩ : syracuseStep 9634727 = 14452091) B14452091
theorem B3179695 : Blo 694316 3179695 := bstep (se 1 (by rfl) ⟨2384771, by rfl⟩ : syracuseStep 3179695 = 4769543) B4769543
theorem B8947259 : Blo 694316 8947259 := bstep (se 1 (by rfl) ⟨6710444, by rfl⟩ : syracuseStep 8947259 = 13420889) B13420889
theorem B5278445 : Blo 694316 5278445 := bstep (se 3 (by rfl) ⟨989708, by rfl⟩ : syracuseStep 5278445 = 1979417) B1979417
theorem B10030027 : Blo 694316 10030027 := bstep (se 1 (by rfl) ⟨7522520, by rfl⟩ : syracuseStep 10030027 = 15045041) B15045041
theorem B5278931 : Blo 694316 5278931 := bstep (se 1 (by rfl) ⟨3959198, by rfl⟩ : syracuseStep 5278931 = 7918397) B7918397
theorem B3346343 : Blo 694316 3346343 := bstep (se 1 (by rfl) ⟨2509757, by rfl⟩ : syracuseStep 3346343 = 5019515) B5019515
theorem B30609373 : Blo 694316 30609373 := bstep (se 3 (by rfl) ⟨5739257, by rfl⟩ : syracuseStep 30609373 = 11478515) B11478515
theorem B5280389 : Blo 694316 5280389 := bstep (se 4 (by rfl) ⟨495036, by rfl⟩ : syracuseStep 5280389 = 990073) B990073
theorem B101488625 : Blo 694316 101488625 := bstep (se 2 (by rfl) ⟨38058234, by rfl⟩ : syracuseStep 101488625 = 76116469) B76116469
theorem B694399 : Blo 694316 694399 := bstep (se 1 (by rfl) ⟨520799, by rfl⟩ : syracuseStep 694399 = 1041599) B1041599
theorem B694495 : Blo 694316 694495 := bstep (se 1 (by rfl) ⟨520871, by rfl⟩ : syracuseStep 694495 = 1041743) B1041743
theorem B694555 : Blo 694316 694555 := bstep (se 1 (by rfl) ⟨520916, by rfl⟩ : syracuseStep 694555 = 1041833) B1041833
theorem B694655 : Blo 694316 694655 := bstep (se 1 (by rfl) ⟨520991, by rfl⟩ : syracuseStep 694655 = 1041983) B1041983
theorem B694895 : Blo 694316 694895 := bstep (se 1 (by rfl) ⟨521171, by rfl⟩ : syracuseStep 694895 = 1042343) B1042343
theorem B694975 : Blo 694316 694975 := bstep (se 1 (by rfl) ⟨521231, by rfl⟩ : syracuseStep 694975 = 1042463) B1042463
theorem B695279 : Blo 694316 695279 := bstep (se 1 (by rfl) ⟨521459, by rfl⟩ : syracuseStep 695279 = 1042919) B1042919
theorem B695399 : Blo 694316 695399 := bstep (se 1 (by rfl) ⟨521549, by rfl⟩ : syracuseStep 695399 = 1043099) B1043099
theorem B892135 : Blo 694316 892135 := bstep (se 1 (by rfl) ⟨669101, by rfl⟩ : syracuseStep 892135 = 1338203) B1338203
theorem B695547 : Blo 694316 695547 := bstep (se 1 (by rfl) ⟨521660, by rfl⟩ : syracuseStep 695547 = 1043321) B1043321
theorem B11443463 : Blo 694316 11443463 := bstep (se 1 (by rfl) ⟨8582597, by rfl⟩ : syracuseStep 11443463 = 17165195) B17165195
theorem B695711 : Blo 694316 695711 := bstep (se 1 (by rfl) ⟨521783, by rfl⟩ : syracuseStep 695711 = 1043567) B1043567
theorem B1318351 : Blo 694316 1318351 := bstep (se 1 (by rfl) ⟨988763, by rfl⟩ : syracuseStep 1318351 = 1977527) B1977527
theorem B695775 : Blo 694316 695775 := bstep (se 1 (by rfl) ⟨521831, by rfl⟩ : syracuseStep 695775 = 1043663) B1043663
theorem B695855 : Blo 694316 695855 := bstep (se 1 (by rfl) ⟨521891, by rfl⟩ : syracuseStep 695855 = 1043783) B1043783
theorem B1318511 : Blo 694316 1318511 := bstep (se 1 (by rfl) ⟨988883, by rfl⟩ : syracuseStep 1318511 = 1977767) B1977767
theorem B696047 : Blo 694316 696047 := bstep (se 1 (by rfl) ⟨522035, by rfl⟩ : syracuseStep 696047 = 1044071) B1044071
theorem B4235095 : Blo 694316 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B3612647 : Blo 694316 3612647 := bstep (se 1 (by rfl) ⟨2709485, by rfl⟩ : syracuseStep 3612647 = 5418971) B5418971
theorem B696303 : Blo 694316 696303 := bstep (se 1 (by rfl) ⟨522227, by rfl⟩ : syracuseStep 696303 = 1044455) B1044455
theorem B696383 : Blo 694316 696383 := bstep (se 1 (by rfl) ⟨522287, by rfl⟩ : syracuseStep 696383 = 1044575) B1044575
theorem B696423 : Blo 694316 696423 := bstep (se 1 (by rfl) ⟨522317, by rfl⟩ : syracuseStep 696423 = 1044635) B1044635
theorem B696543 : Blo 694316 696543 := bstep (se 1 (by rfl) ⟨522407, by rfl⟩ : syracuseStep 696543 = 1044815) B1044815
theorem B696603 : Blo 694316 696603 := bstep (se 1 (by rfl) ⟨522452, by rfl⟩ : syracuseStep 696603 = 1044905) B1044905
theorem B696807 : Blo 694316 696807 := bstep (se 1 (by rfl) ⟨522605, by rfl⟩ : syracuseStep 696807 = 1045211) B1045211
theorem B9511505 : Blo 694316 9511505 := bstep (se 2 (by rfl) ⟨3566814, by rfl⟩ : syracuseStep 9511505 = 7133629) B7133629
theorem B696987 : Blo 694316 696987 := bstep (se 1 (by rfl) ⟨522740, by rfl⟩ : syracuseStep 696987 = 1045481) B1045481
theorem B697083 : Blo 694316 697083 := bstep (se 1 (by rfl) ⟨522812, by rfl⟩ : syracuseStep 697083 = 1045625) B1045625
theorem B5284763 : Blo 694316 5284763 := bstep (se 1 (by rfl) ⟨3963572, by rfl⟩ : syracuseStep 5284763 = 7927145) B7927145
theorem B697435 : Blo 694316 697435 := bstep (se 1 (by rfl) ⟨523076, by rfl⟩ : syracuseStep 697435 = 1046153) B1046153
theorem B697575 : Blo 694316 697575 := bstep (se 1 (by rfl) ⟨523181, by rfl⟩ : syracuseStep 697575 = 1046363) B1046363
theorem B697599 : Blo 694316 697599 := bstep (se 1 (by rfl) ⟨523199, by rfl⟩ : syracuseStep 697599 = 1046399) B1046399
theorem B697663 : Blo 694316 697663 := bstep (se 1 (by rfl) ⟨523247, by rfl⟩ : syracuseStep 697663 = 1046495) B1046495
theorem B697703 : Blo 694316 697703 := bstep (se 1 (by rfl) ⟨523277, by rfl⟩ : syracuseStep 697703 = 1046555) B1046555
theorem B697831 : Blo 694316 697831 := bstep (se 1 (by rfl) ⟨523373, by rfl⟩ : syracuseStep 697831 = 1046747) B1046747
theorem B4466249 : Blo 694316 4466249 := bstep (se 2 (by rfl) ⟨1674843, by rfl⟩ : syracuseStep 4466249 = 3349687) B3349687
theorem B698011 : Blo 694316 698011 := bstep (se 1 (by rfl) ⟨523508, by rfl⟩ : syracuseStep 698011 = 1047017) B1047017
theorem B54208349 : Blo 694316 54208349 := bstep (se 3 (by rfl) ⟨10164065, by rfl⟩ : syracuseStep 54208349 = 20328131) B20328131
theorem B698271 : Blo 694316 698271 := bstep (se 1 (by rfl) ⟨523703, by rfl⟩ : syracuseStep 698271 = 1047407) B1047407
theorem B1877993 : Blo 694316 1877993 := bstep (se 2 (by rfl) ⟨704247, by rfl⟩ : syracuseStep 1877993 = 1408495) B1408495
theorem B7612537 : Blo 694316 7612537 := bstep (se 2 (by rfl) ⟨2854701, by rfl⟩ : syracuseStep 7612537 = 5709403) B5709403
theorem B1321609 : Blo 694316 1321609 := bstep (se 2 (by rfl) ⟨495603, by rfl⟩ : syracuseStep 1321609 = 991207) B991207
theorem B4533157 : Blo 694316 4533157 := bstep (se 4 (by rfl) ⟨424983, by rfl⟩ : syracuseStep 4533157 = 849967) B849967
theorem B1256609 : Blo 694316 1256609 := bstep (se 2 (by rfl) ⟨471228, by rfl⟩ : syracuseStep 1256609 = 942457) B942457
theorem B21736799 : Blo 694316 21736799 := bstep (se 1 (by rfl) ⟨16302599, by rfl⟩ : syracuseStep 21736799 = 32605199) B32605199
theorem B1322543 : Blo 694316 1322543 := bstep (se 1 (by rfl) ⟨991907, by rfl⟩ : syracuseStep 1322543 = 1983815) B1983815
theorem B1060399 : Blo 694316 1060399 := bstep (se 1 (by rfl) ⟨795299, by rfl⟩ : syracuseStep 1060399 = 1590599) B1590599
theorem B5942969 : Blo 694316 5942969 := bstep (se 2 (by rfl) ⟨2228613, by rfl⟩ : syracuseStep 5942969 = 4457227) B4457227
theorem B4468861 : Blo 694316 4468861 := bstep (se 3 (by rfl) ⟨837911, by rfl⟩ : syracuseStep 4468861 = 1675823) B1675823
theorem B40153319 : Blo 694316 40153319 := bstep (se 1 (by rfl) ⟨30114989, by rfl⟩ : syracuseStep 40153319 = 60229979) B60229979
theorem B1257727 : Blo 694316 1257727 := bstep (se 1 (by rfl) ⟨943295, by rfl⟩ : syracuseStep 1257727 = 1886591) B1886591
theorem B1978985 : Blo 694316 1978985 := bstep (se 2 (by rfl) ⟨742119, by rfl⟩ : syracuseStep 1978985 = 1484239) B1484239
theorem B4010633 : Blo 694316 4010633 := bstep (se 2 (by rfl) ⟨1503987, by rfl⟩ : syracuseStep 4010633 = 3007975) B3007975
theorem B1324927 : Blo 694316 1324927 := bstep (se 1 (by rfl) ⟨993695, by rfl⟩ : syracuseStep 1324927 = 1987391) B1987391
theorem B5290109 : Blo 694316 5290109 := bstep (se 3 (by rfl) ⟨991895, by rfl⟩ : syracuseStep 5290109 = 1983791) B1983791
theorem B1489279 : Blo 694316 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B23182199 : Blo 694316 23182199 := bstep (se 1 (by rfl) ⟨17386649, by rfl⟩ : syracuseStep 23182199 = 34773299) B34773299
theorem B45267983 : Blo 694316 45267983 := bstep (se 1 (by rfl) ⟨33950987, by rfl⟩ : syracuseStep 45267983 = 67901975) B67901975
theorem B1720127 : Blo 694316 1720127 := bstep (se 1 (by rfl) ⟨1290095, by rfl⟩ : syracuseStep 1720127 = 2580191) B2580191
theorem B9551783 : Blo 694316 9551783 := bstep (se 1 (by rfl) ⟨7163837, by rfl⟩ : syracuseStep 9551783 = 14327675) B14327675
theorem B5947343 : Blo 694316 5947343 := bstep (se 1 (by rfl) ⟨4460507, by rfl⟩ : syracuseStep 5947343 = 8921015) B8921015
theorem B7914023 : Blo 694316 7914023 := bstep (se 1 (by rfl) ⟨5935517, by rfl⟩ : syracuseStep 7914023 = 11871035) B11871035
theorem B5948093 : Blo 694316 5948093 := bstep (se 3 (by rfl) ⟨1115267, by rfl⟩ : syracuseStep 5948093 = 2230535) B2230535
theorem B16302791 : Blo 694316 16302791 := bstep (se 1 (by rfl) ⟨12227093, by rfl⟩ : syracuseStep 16302791 = 24454187) B24454187
theorem B13419431 : Blo 694316 13419431 := bstep (se 1 (by rfl) ⟨10064573, by rfl⟩ : syracuseStep 13419431 = 20129147) B20129147
theorem B2638889 : Blo 694316 2638889 := bstep (se 2 (by rfl) ⟨989583, by rfl⟩ : syracuseStep 2638889 = 1979167) B1979167
theorem B5293997 : Blo 694316 5293997 := bstep (se 3 (by rfl) ⟨992624, by rfl⟩ : syracuseStep 5293997 = 1985249) B1985249
theorem B2640059 : Blo 694316 2640059 := bstep (se 1 (by rfl) ⟨1980044, by rfl⟩ : syracuseStep 2640059 = 3960089) B3960089
theorem B8898767 : Blo 694316 8898767 := bstep (se 1 (by rfl) ⟨6674075, by rfl⟩ : syracuseStep 8898767 = 13348151) B13348151
theorem B1427681 : Blo 694316 1427681 := bstep (se 2 (by rfl) ⟨535380, by rfl⟩ : syracuseStep 1427681 = 1070761) B1070761
theorem B837883 : Blo 694316 837883 := bstep (se 1 (by rfl) ⟨628412, by rfl⟩ : syracuseStep 837883 = 1256825) B1256825
theorem B805531 : Blo 694316 805531 := bstep (se 1 (by rfl) ⟨604148, by rfl⟩ : syracuseStep 805531 = 1208297) B1208297
theorem B2968649 : Blo 694316 2968649 := bstep (se 2 (by rfl) ⟨1113243, by rfl⟩ : syracuseStep 2968649 = 2226487) B2226487
theorem B8899793 : Blo 694316 8899793 := bstep (se 2 (by rfl) ⟨3337422, by rfl⟩ : syracuseStep 8899793 = 6674845) B6674845
theorem B7916939 : Blo 694316 7916939 := bstep (se 1 (by rfl) ⟨5937704, by rfl⟩ : syracuseStep 7916939 = 11875409) B11875409
theorem B4771295 : Blo 694316 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B2346515 : Blo 694316 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B2641835 : Blo 694316 2641835 := bstep (se 1 (by rfl) ⟨1981376, by rfl⟩ : syracuseStep 2641835 = 3962753) B3962753
theorem B14307313 : Blo 694316 14307313 := bstep (se 2 (by rfl) ⟨5365242, by rfl⟩ : syracuseStep 14307313 = 10730485) B10730485
theorem B2642017 : Blo 694316 2642017 := bstep (se 2 (by rfl) ⟨990756, by rfl⟩ : syracuseStep 2642017 = 1981513) B1981513
theorem B2347271 : Blo 694316 2347271 := bstep (se 1 (by rfl) ⟨1760453, by rfl⟩ : syracuseStep 2347271 = 3520907) B3520907
theorem B1757609 : Blo 694316 1757609 := bstep (se 2 (by rfl) ⟨659103, by rfl⟩ : syracuseStep 1757609 = 1318207) B1318207
theorem B2970665 : Blo 694316 2970665 := bstep (se 2 (by rfl) ⟨1113999, by rfl⟩ : syracuseStep 2970665 = 2227999) B2227999
theorem B3921095 : Blo 694316 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B2381051 : Blo 694316 2381051 := bstep (se 1 (by rfl) ⟨1785788, by rfl⟩ : syracuseStep 2381051 = 3571577) B3571577
theorem B3396889 : Blo 694316 3396889 := bstep (se 2 (by rfl) ⟨1273833, by rfl⟩ : syracuseStep 3396889 = 2547667) B2547667
theorem B2348351 : Blo 694316 2348351 := bstep (se 1 (by rfl) ⟨1761263, by rfl⟩ : syracuseStep 2348351 = 3522527) B3522527
theorem B1758793 : Blo 694316 1758793 := bstep (se 2 (by rfl) ⟨659547, by rfl⟩ : syracuseStep 1758793 = 1319095) B1319095
theorem B1562255 : Blo 694316 1562255 := bstep (se 1 (by rfl) ⟨1171691, by rfl⟩ : syracuseStep 1562255 = 2343383) B2343383
theorem B5658761 : Blo 694316 5658761 := bstep (se 2 (by rfl) ⟨2122035, by rfl⟩ : syracuseStep 5658761 = 4244071) B4244071
theorem B2349431 : Blo 694316 2349431 := bstep (se 1 (by rfl) ⟨1762073, by rfl⟩ : syracuseStep 2349431 = 3524147) B3524147
theorem B2350187 : Blo 694316 2350187 := bstep (se 1 (by rfl) ⟨1762640, by rfl⟩ : syracuseStep 2350187 = 3525281) B3525281
theorem B2972801 : Blo 694316 2972801 := bstep (se 2 (by rfl) ⟨1114800, by rfl⟩ : syracuseStep 2972801 = 2229601) B2229601
theorem B1760575 : Blo 694316 1760575 := bstep (se 1 (by rfl) ⟨1320431, by rfl⟩ : syracuseStep 1760575 = 2640863) B2640863
theorem B2350511 : Blo 694316 2350511 := bstep (se 1 (by rfl) ⟨1762883, by rfl⟩ : syracuseStep 2350511 = 3525767) B3525767
theorem B1760737 : Blo 694316 1760737 := bstep (se 2 (by rfl) ⟨660276, by rfl⟩ : syracuseStep 1760737 = 1320553) B1320553
theorem B1564703 : Blo 694316 1564703 := bstep (se 1 (by rfl) ⟨1173527, by rfl⟩ : syracuseStep 1564703 = 2347055) B2347055
theorem B1171759 : Blo 694316 1171759 := bstep (se 1 (by rfl) ⟨878819, by rfl⟩ : syracuseStep 1171759 = 1757639) B1757639
theorem B5005907 : Blo 694316 5005907 := bstep (se 1 (by rfl) ⟨3754430, by rfl⟩ : syracuseStep 5005907 = 7508861) B7508861
theorem B2352239 : Blo 694316 2352239 := bstep (se 1 (by rfl) ⟨1764179, by rfl⟩ : syracuseStep 2352239 = 3528359) B3528359
theorem B2647151 : Blo 694316 2647151 := bstep (se 1 (by rfl) ⟨1985363, by rfl⟩ : syracuseStep 2647151 = 3970727) B3970727
theorem B2352617 : Blo 694316 2352617 := bstep (se 2 (by rfl) ⟨882231, by rfl⟩ : syracuseStep 2352617 = 1764463) B1764463
theorem B1173055 : Blo 694316 1173055 := bstep (se 1 (by rfl) ⟨879791, by rfl⟩ : syracuseStep 1173055 = 1759583) B1759583
theorem B1042025 : Blo 694316 1042025 := bstep (se 2 (by rfl) ⟨390759, by rfl⟩ : syracuseStep 1042025 = 781519) B781519
theorem B2647849 : Blo 694316 2647849 := bstep (se 2 (by rfl) ⟨992943, by rfl⟩ : syracuseStep 2647849 = 1985887) B1985887
theorem B1173575 : Blo 694316 1173575 := bstep (se 1 (by rfl) ⟨880181, by rfl⟩ : syracuseStep 1173575 = 1760363) B1760363
theorem B2353319 : Blo 694316 2353319 := bstep (se 1 (by rfl) ⟨1764989, by rfl⟩ : syracuseStep 2353319 = 3529979) B3529979
theorem B1566971 : Blo 694316 1566971 := bstep (se 1 (by rfl) ⟨1175228, by rfl⟩ : syracuseStep 1566971 = 2350457) B2350457
theorem B1763815 : Blo 694316 1763815 := bstep (se 1 (by rfl) ⟨1322861, by rfl⟩ : syracuseStep 1763815 = 2645723) B2645723
theorem B2976371 : Blo 694316 2976371 := bstep (se 1 (by rfl) ⟨2232278, by rfl⟩ : syracuseStep 2976371 = 4464557) B4464557
theorem B1043183 : Blo 694316 1043183 := bstep (se 1 (by rfl) ⟨782387, by rfl⟩ : syracuseStep 1043183 = 1564775) B1564775
theorem B1567529 : Blo 694316 1567529 := bstep (se 2 (by rfl) ⟨587823, by rfl⟩ : syracuseStep 1567529 = 1175647) B1175647
theorem B1043561 : Blo 694316 1043561 := bstep (se 2 (by rfl) ⟨391335, by rfl⟩ : syracuseStep 1043561 = 782671) B782671
theorem B1568231 : Blo 694316 1568231 := bstep (se 1 (by rfl) ⟨1176173, by rfl⟩ : syracuseStep 1568231 = 2352347) B2352347
theorem B781807 : Blo 694316 781807 := bstep (se 1 (by rfl) ⟨586355, by rfl⟩ : syracuseStep 781807 = 1172711) B1172711
theorem B1043951 : Blo 694316 1043951 := bstep (se 1 (by rfl) ⟨782963, by rfl⟩ : syracuseStep 1043951 = 1565927) B1565927
theorem B1044089 : Blo 694316 1044089 := bstep (se 2 (by rfl) ⟨391533, by rfl⟩ : syracuseStep 1044089 = 783067) B783067
theorem B1175161 : Blo 694316 1175161 := bstep (se 2 (by rfl) ⟨440685, by rfl⟩ : syracuseStep 1175161 = 881371) B881371
theorem B2650067 : Blo 694316 2650067 := bstep (se 1 (by rfl) ⟨1987550, by rfl⟩ : syracuseStep 2650067 = 3975101) B3975101
theorem B1568807 : Blo 694316 1568807 := bstep (se 1 (by rfl) ⟨1176605, by rfl⟩ : syracuseStep 1568807 = 2353211) B2353211
theorem B2355263 : Blo 694316 2355263 := bstep (se 1 (by rfl) ⟨1766447, by rfl⟩ : syracuseStep 2355263 = 3532895) B3532895
theorem B7336037 : Blo 694316 7336037 := bstep (se 4 (by rfl) ⟨687753, by rfl⟩ : syracuseStep 7336037 = 1375507) B1375507
theorem B880895 : Blo 694316 880895 := bstep (se 1 (by rfl) ⟨660671, by rfl⟩ : syracuseStep 880895 = 1321343) B1321343
theorem B8024777 : Blo 694316 8024777 := bstep (se 2 (by rfl) ⟨3009291, by rfl⟩ : syracuseStep 8024777 = 6018583) B6018583
theorem B2356073 : Blo 694316 2356073 := bstep (se 2 (by rfl) ⟨883527, by rfl⟩ : syracuseStep 2356073 = 1767055) B1767055
theorem B881599 : Blo 694316 881599 := bstep (se 1 (by rfl) ⟨661199, by rfl⟩ : syracuseStep 881599 = 1322399) B1322399
theorem B1569887 : Blo 694316 1569887 := bstep (se 1 (by rfl) ⟨1177415, by rfl⟩ : syracuseStep 1569887 = 2354831) B2354831
theorem B1045673 : Blo 694316 1045673 := bstep (se 2 (by rfl) ⟨392127, by rfl⟩ : syracuseStep 1045673 = 784255) B784255
theorem B3765467 : Blo 694316 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B1045739 : Blo 694316 1045739 := bstep (se 1 (by rfl) ⟨784304, by rfl⟩ : syracuseStep 1045739 = 1568609) B1568609
theorem B12219641 : Blo 694316 12219641 := bstep (se 2 (by rfl) ⟨4582365, by rfl⟩ : syracuseStep 12219641 = 9164731) B9164731
theorem B2356559 : Blo 694316 2356559 := bstep (se 1 (by rfl) ⟨1767419, by rfl⟩ : syracuseStep 2356559 = 3534839) B3534839
theorem B10057193 : Blo 694316 10057193 := bstep (se 2 (by rfl) ⟨3771447, by rfl⟩ : syracuseStep 10057193 = 7542895) B7542895
theorem B1046375 : Blo 694316 1046375 := bstep (se 1 (by rfl) ⟨784781, by rfl⟩ : syracuseStep 1046375 = 1569563) B1569563
theorem B2979773 : Blo 694316 2979773 := bstep (se 3 (by rfl) ⟨558707, by rfl⟩ : syracuseStep 2979773 = 1117415) B1117415
theorem B1046507 : Blo 694316 1046507 := bstep (se 1 (by rfl) ⟨784880, by rfl⟩ : syracuseStep 1046507 = 1569761) B1569761
theorem B1112167 : Blo 694316 1112167 := bstep (se 1 (by rfl) ⟨834125, by rfl⟩ : syracuseStep 1112167 = 1668251) B1668251
theorem B1046639 : Blo 694316 1046639 := bstep (se 1 (by rfl) ⟨784979, by rfl⟩ : syracuseStep 1046639 = 1569959) B1569959
theorem B3963005 : Blo 694316 3963005 := bstep (se 3 (by rfl) ⟨743063, by rfl⟩ : syracuseStep 3963005 = 1486127) B1486127
theorem B2324695 : Blo 694316 2324695 := bstep (se 1 (by rfl) ⟨1743521, by rfl⟩ : syracuseStep 2324695 = 3487043) B3487043
theorem B3766607 : Blo 694316 3766607 := bstep (se 1 (by rfl) ⟨2824955, by rfl⟩ : syracuseStep 3766607 = 5649911) B5649911
theorem B1047419 : Blo 694316 1047419 := bstep (se 1 (by rfl) ⟨785564, by rfl⟩ : syracuseStep 1047419 = 1571129) B1571129
theorem B2981771 : Blo 694316 2981771 := bstep (se 1 (by rfl) ⟨2236328, by rfl⟩ : syracuseStep 2981771 = 4472657) B4472657
theorem B11927897 : Blo 694316 11927897 := bstep (se 2 (by rfl) ⟨4472961, by rfl⟩ : syracuseStep 11927897 = 8945923) B8945923
theorem B5276015 : Blo 694316 5276015 := bstep (se 1 (by rfl) ⟨3957011, by rfl⟩ : syracuseStep 5276015 = 7914023) B7914023
theorem B3965395 : Blo 694316 3965395 := bstep (se 1 (by rfl) ⟨2974046, by rfl⟩ : syracuseStep 3965395 = 5948093) B5948093
theorem B6423151 : Blo 694316 6423151 := bstep (se 1 (by rfl) ⟨4817363, by rfl⟩ : syracuseStep 6423151 = 9634727) B9634727
theorem B8946287 : Blo 694316 8946287 := bstep (se 1 (by rfl) ⟨6709715, by rfl⟩ : syracuseStep 8946287 = 13419431) B13419431
theorem B5964839 : Blo 694316 5964839 := bstep (se 1 (by rfl) ⟨4473629, by rfl⟩ : syracuseStep 5964839 = 8947259) B8947259
theorem B5932511 : Blo 694316 5932511 := bstep (se 1 (by rfl) ⟨4449383, by rfl⟩ : syracuseStep 5932511 = 8898767) B8898767
theorem B951787 : Blo 694316 951787 := bstep (se 1 (by rfl) ⟨713840, by rfl⟩ : syracuseStep 951787 = 1427681) B1427681
theorem B5933195 : Blo 694316 5933195 := bstep (se 1 (by rfl) ⟨4449896, by rfl⟩ : syracuseStep 5933195 = 8899793) B8899793
theorem B5277959 : Blo 694316 5277959 := bstep (se 1 (by rfl) ⟨3958469, by rfl⟩ : syracuseStep 5277959 = 7916939) B7916939
theorem B3180863 : Blo 694316 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B2230895 : Blo 694316 2230895 := bstep (se 1 (by rfl) ⟨1673171, by rfl⟩ : syracuseStep 2230895 = 3346343) B3346343
theorem B10456253 : Blo 694316 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B13373369 : Blo 694316 13373369 := bstep (se 2 (by rfl) ⟨5015013, by rfl⟩ : syracuseStep 13373369 = 10030027) B10030027
theorem B3772507 : Blo 694316 3772507 := bstep (se 1 (by rfl) ⟨2829380, by rfl⟩ : syracuseStep 3772507 = 5658761) B5658761
theorem B1413865 : Blo 694316 1413865 := bstep (se 2 (by rfl) ⟨530199, by rfl⟩ : syracuseStep 1413865 = 1060399) B1060399
theorem B19076417 : Blo 694316 19076417 := bstep (se 2 (by rfl) ⟨7153656, by rfl⟩ : syracuseStep 19076417 = 14307313) B14307313
theorem B1676969 : Blo 694316 1676969 := bstep (se 2 (by rfl) ⟨628863, by rfl⟩ : syracuseStep 1676969 = 1257727) B1257727
theorem B694683 : Blo 694316 694683 := bstep (se 1 (by rfl) ⟨521012, by rfl⟩ : syracuseStep 694683 = 1042025) B1042025
theorem B1251995 : Blo 694316 1251995 := bstep (se 1 (by rfl) ⟨938996, by rfl⟩ : syracuseStep 1251995 = 1877993) B1877993
theorem B695455 : Blo 694316 695455 := bstep (se 1 (by rfl) ⟨521591, by rfl⟩ : syracuseStep 695455 = 1043183) B1043183
theorem B695707 : Blo 694316 695707 := bstep (se 1 (by rfl) ⟨521780, by rfl⟩ : syracuseStep 695707 = 1043561) B1043561
theorem B14491199 : Blo 694316 14491199 := bstep (se 1 (by rfl) ⟨10868399, by rfl⟩ : syracuseStep 14491199 = 21736799) B21736799
theorem B695967 : Blo 694316 695967 := bstep (se 1 (by rfl) ⟨521975, by rfl⟩ : syracuseStep 695967 = 1043951) B1043951
theorem B696059 : Blo 694316 696059 := bstep (se 1 (by rfl) ⟨522044, by rfl⟩ : syracuseStep 696059 = 1044089) B1044089
theorem B4890691 : Blo 694316 4890691 := bstep (se 1 (by rfl) ⟨3668018, by rfl⟩ : syracuseStep 4890691 = 7336037) B7336037
theorem B1482889 : Blo 694316 1482889 := bstep (se 2 (by rfl) ⟨556083, by rfl⟩ : syracuseStep 1482889 = 1112167) B1112167
theorem B1319323 : Blo 694316 1319323 := bstep (se 1 (by rfl) ⟨989492, by rfl⟩ : syracuseStep 1319323 = 1978985) B1978985
theorem B5349851 : Blo 694316 5349851 := bstep (se 1 (by rfl) ⟨4012388, by rfl⟩ : syracuseStep 5349851 = 8024777) B8024777
theorem B697115 : Blo 694316 697115 := bstep (se 1 (by rfl) ⟨522836, by rfl⟩ : syracuseStep 697115 = 1045673) B1045673
theorem B697159 : Blo 694316 697159 := bstep (se 1 (by rfl) ⟨522869, by rfl⟩ : syracuseStep 697159 = 1045739) B1045739
theorem B697583 : Blo 694316 697583 := bstep (se 1 (by rfl) ⟨523187, by rfl⟩ : syracuseStep 697583 = 1046375) B1046375
theorem B697671 : Blo 694316 697671 := bstep (se 1 (by rfl) ⟨523253, by rfl⟩ : syracuseStep 697671 = 1046507) B1046507
theorem B697759 : Blo 694316 697759 := bstep (se 1 (by rfl) ⟨523319, by rfl⟩ : syracuseStep 697759 = 1046639) B1046639
theorem B1189513 : Blo 694316 1189513 := bstep (se 2 (by rfl) ⟨446067, by rfl⟩ : syracuseStep 1189513 = 892135) B892135
theorem B698279 : Blo 694316 698279 := bstep (se 1 (by rfl) ⟨523709, by rfl⟩ : syracuseStep 698279 = 1047419) B1047419
theorem B25471421 : Blo 694316 25471421 := bstep (se 3 (by rfl) ⟨4775891, by rfl⟩ : syracuseStep 25471421 = 9551783) B9551783
theorem B5646793 : Blo 694316 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B11906027 : Blo 694316 11906027 := bstep (se 1 (by rfl) ⟨8929520, by rfl⟩ : syracuseStep 11906027 = 17859041) B17859041
theorem B1879247 : Blo 694316 1879247 := bstep (se 1 (by rfl) ⟨1409435, by rfl⟩ : syracuseStep 1879247 = 2818871) B2818871
theorem B4468709 : Blo 694316 4468709 := bstep (se 4 (by rfl) ⟨418941, by rfl⟩ : syracuseStep 4468709 = 837883) B837883
theorem B4239593 : Blo 694316 4239593 := bstep (se 2 (by rfl) ⟨1589847, by rfl⟩ : syracuseStep 4239593 = 3179695) B3179695
theorem B3518963 : Blo 694316 3518963 := bstep (se 1 (by rfl) ⟨2639222, by rfl⟩ : syracuseStep 3518963 = 5278445) B5278445
theorem B1979099 : Blo 694316 1979099 := bstep (se 1 (by rfl) ⟨1484324, by rfl⟩ : syracuseStep 1979099 = 2968649) B2968649
theorem B3519287 : Blo 694316 3519287 := bstep (se 1 (by rfl) ⟨2639465, by rfl⟩ : syracuseStep 3519287 = 5278931) B5278931
theorem B3520259 : Blo 694316 3520259 := bstep (se 1 (by rfl) ⟨2640194, by rfl⟩ : syracuseStep 3520259 = 5280389) B5280389
theorem B10041245 : Blo 694316 10041245 := bstep (se 3 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 10041245 = 3765467) B3765467
theorem B1980443 : Blo 694316 1980443 := bstep (se 1 (by rfl) ⟨1485332, by rfl⟩ : syracuseStep 1980443 = 2970665) B2970665
theorem B1587367 : Blo 694316 1587367 := bstep (se 1 (by rfl) ⟨1190525, by rfl⟩ : syracuseStep 1587367 = 2381051) B2381051
theorem B1981867 : Blo 694316 1981867 := bstep (se 1 (by rfl) ⟨1486400, by rfl⟩ : syracuseStep 1981867 = 2972801) B2972801
theorem B40812497 : Blo 694316 40812497 := bstep (se 2 (by rfl) ⟨15304686, by rfl⟩ : syracuseStep 40812497 = 30609373) B30609373
theorem B3522689 : Blo 694316 3522689 := bstep (se 2 (by rfl) ⟨1321008, by rfl⟩ : syracuseStep 3522689 = 2642017) B2642017
theorem B6341003 : Blo 694316 6341003 := bstep (se 1 (by rfl) ⟨4755752, by rfl⟩ : syracuseStep 6341003 = 9511505) B9511505
theorem B3523175 : Blo 694316 3523175 := bstep (se 1 (by rfl) ⟨2642381, by rfl⟩ : syracuseStep 3523175 = 5284763) B5284763
theorem B1984247 : Blo 694316 1984247 := bstep (se 1 (by rfl) ⟨1488185, by rfl⟩ : syracuseStep 1984247 = 2976371) B2976371
theorem B2345057 : Blo 694316 2345057 := bstep (se 2 (by rfl) ⟨879396, by rfl⟩ : syracuseStep 2345057 = 1758793) B1758793
theorem B837739 : Blo 694316 837739 := bstep (se 1 (by rfl) ⟨628304, by rfl⟩ : syracuseStep 837739 = 1256609) B1256609
theorem B3099593 : Blo 694316 3099593 := bstep (se 2 (by rfl) ⟨1162347, by rfl⟩ : syracuseStep 3099593 = 2324695) B2324695
theorem B2673755 : Blo 694316 2673755 := bstep (se 1 (by rfl) ⟨2005316, by rfl⟩ : syracuseStep 2673755 = 4010633) B4010633
theorem B1985705 : Blo 694316 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B8146427 : Blo 694316 8146427 := bstep (se 1 (by rfl) ⟨6109820, by rfl⟩ : syracuseStep 8146427 = 12219641) B12219641
theorem B6704795 : Blo 694316 6704795 := bstep (se 1 (by rfl) ⟨5028596, by rfl⟩ : syracuseStep 6704795 = 10057193) B10057193
theorem B1986515 : Blo 694316 1986515 := bstep (se 1 (by rfl) ⟨1489886, by rfl⟩ : syracuseStep 1986515 = 2979773) B2979773
theorem B2642003 : Blo 694316 2642003 := bstep (se 1 (by rfl) ⟨1981502, by rfl⟩ : syracuseStep 2642003 = 3963005) B3963005
theorem B3526739 : Blo 694316 3526739 := bstep (se 1 (by rfl) ⟨2645054, by rfl⟩ : syracuseStep 3526739 = 5290109) B5290109
theorem B2511071 : Blo 694316 2511071 := bstep (se 1 (by rfl) ⟨1883303, by rfl⟩ : syracuseStep 2511071 = 3766607) B3766607
theorem B2347433 : Blo 694316 2347433 := bstep (se 2 (by rfl) ⟨880287, by rfl⟩ : syracuseStep 2347433 = 1760575) B1760575
theorem B15454799 : Blo 694316 15454799 := bstep (se 1 (by rfl) ⟨11591099, by rfl⟩ : syracuseStep 15454799 = 23182199) B23182199
theorem B1757801 : Blo 694316 1757801 := bstep (se 2 (by rfl) ⟨659175, by rfl⟩ : syracuseStep 1757801 = 1318351) B1318351
theorem B2347649 : Blo 694316 2347649 := bstep (se 2 (by rfl) ⟨880368, by rfl⟩ : syracuseStep 2347649 = 1760737) B1760737
theorem B1987847 : Blo 694316 1987847 := bstep (se 1 (by rfl) ⟨1490885, by rfl⟩ : syracuseStep 1987847 = 2981771) B2981771
theorem B2643475 : Blo 694316 2643475 := bstep (se 1 (by rfl) ⟨1982606, by rfl⟩ : syracuseStep 2643475 = 3965213) B3965213
theorem B1562345 : Blo 694316 1562345 := bstep (se 2 (by rfl) ⟨585879, by rfl⟩ : syracuseStep 1562345 = 1171759) B1171759
theorem B10868527 : Blo 694316 10868527 := bstep (se 1 (by rfl) ⟨8151395, by rfl⟩ : syracuseStep 10868527 = 16302791) B16302791
theorem B2349053 : Blo 694316 2349053 := bstep (se 3 (by rfl) ⟨440447, by rfl⟩ : syracuseStep 2349053 = 880895) B880895
theorem B1759259 : Blo 694316 1759259 := bstep (se 1 (by rfl) ⟨1319444, by rfl⟩ : syracuseStep 1759259 = 2638889) B2638889
theorem B3529331 : Blo 694316 3529331 := bstep (se 1 (by rfl) ⟨2646998, by rfl⟩ : syracuseStep 3529331 = 5293997) B5293997
theorem B1760039 : Blo 694316 1760039 := bstep (se 1 (by rfl) ⟨1320029, by rfl⟩ : syracuseStep 1760039 = 2640059) B2640059
theorem B1564073 : Blo 694316 1564073 := bstep (se 2 (by rfl) ⟨586527, by rfl⟩ : syracuseStep 1564073 = 1173055) B1173055
theorem B1564343 : Blo 694316 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B3530465 : Blo 694316 3530465 := bstep (se 2 (by rfl) ⟨1323924, by rfl⟩ : syracuseStep 3530465 = 2647849) B2647849
theorem B1761223 : Blo 694316 1761223 := bstep (se 1 (by rfl) ⟨1320917, by rfl⟩ : syracuseStep 1761223 = 2641835) B2641835
theorem B10150049 : Blo 694316 10150049 := bstep (se 2 (by rfl) ⟨3806268, by rfl⟩ : syracuseStep 10150049 = 7612537) B7612537
theorem B1564847 : Blo 694316 1564847 := bstep (se 1 (by rfl) ⟨1173635, by rfl⟩ : syracuseStep 1564847 = 2347271) B2347271
theorem B1171739 : Blo 694316 1171739 := bstep (se 1 (by rfl) ⟨878804, by rfl⟩ : syracuseStep 1171739 = 1757609) B1757609
theorem B2351753 : Blo 694316 2351753 := bstep (se 2 (by rfl) ⟨881907, by rfl⟩ : syracuseStep 2351753 = 1763815) B1763815
theorem B1762145 : Blo 694316 1762145 := bstep (se 2 (by rfl) ⟨660804, by rfl⟩ : syracuseStep 1762145 = 1321609) B1321609
theorem B1074041 : Blo 694316 1074041 := bstep (se 2 (by rfl) ⟨402765, by rfl⟩ : syracuseStep 1074041 = 805531) B805531
theorem B1565567 : Blo 694316 1565567 := bstep (se 1 (by rfl) ⟨1174175, by rfl⟩ : syracuseStep 1565567 = 2348351) B2348351
theorem B1041503 : Blo 694316 1041503 := bstep (se 1 (by rfl) ⟨781127, by rfl⟩ : syracuseStep 1041503 = 1562255) B1562255
theorem B67659083 : Blo 694316 67659083 := bstep (se 1 (by rfl) ⟨50744312, by rfl⟩ : syracuseStep 67659083 = 101488625) B101488625
theorem B1566287 : Blo 694316 1566287 := bstep (se 1 (by rfl) ⟨1174715, by rfl⟩ : syracuseStep 1566287 = 2349431) B2349431
theorem B1042409 : Blo 694316 1042409 := bstep (se 2 (by rfl) ⟨390903, by rfl⟩ : syracuseStep 1042409 = 781807) B781807
theorem B1566791 : Blo 694316 1566791 := bstep (se 1 (by rfl) ⟨1175093, by rfl⟩ : syracuseStep 1566791 = 2350187) B2350187
theorem B1566881 : Blo 694316 1566881 := bstep (se 2 (by rfl) ⟨587580, by rfl⟩ : syracuseStep 1566881 = 1175161) B1175161
theorem B7628975 : Blo 694316 7628975 := bstep (se 1 (by rfl) ⟨5721731, by rfl⟩ : syracuseStep 7628975 = 11443463) B11443463
theorem B24176837 : Blo 694316 24176837 := bstep (se 4 (by rfl) ⟨2266578, by rfl⟩ : syracuseStep 24176837 = 4533157) B4533157
theorem B1567007 : Blo 694316 1567007 := bstep (se 1 (by rfl) ⟨1175255, by rfl⟩ : syracuseStep 1567007 = 2350511) B2350511
theorem B879007 : Blo 694316 879007 := bstep (se 1 (by rfl) ⟨659255, by rfl⟩ : syracuseStep 879007 = 1318511) B1318511
theorem B1043135 : Blo 694316 1043135 := bstep (se 1 (by rfl) ⟨782351, by rfl⟩ : syracuseStep 1043135 = 1564703) B1564703
theorem B5958481 : Blo 694316 5958481 := bstep (se 2 (by rfl) ⟨2234430, by rfl⟩ : syracuseStep 5958481 = 4468861) B4468861
theorem B3337271 : Blo 694316 3337271 := bstep (se 1 (by rfl) ⟨2502953, by rfl⟩ : syracuseStep 3337271 = 5005907) B5005907
theorem B1568159 : Blo 694316 1568159 := bstep (se 1 (by rfl) ⟨1176119, by rfl⟩ : syracuseStep 1568159 = 2352239) B2352239
theorem B1764767 : Blo 694316 1764767 := bstep (se 1 (by rfl) ⟨1323575, by rfl⟩ : syracuseStep 1764767 = 2647151) B2647151
theorem B1568411 : Blo 694316 1568411 := bstep (se 1 (by rfl) ⟨1176308, by rfl⟩ : syracuseStep 1568411 = 2352617) B2352617
theorem B2977499 : Blo 694316 2977499 := bstep (se 1 (by rfl) ⟨2233124, by rfl⟩ : syracuseStep 2977499 = 4466249) B4466249
theorem B36138899 : Blo 694316 36138899 := bstep (se 1 (by rfl) ⟨27104174, by rfl⟩ : syracuseStep 36138899 = 54208349) B54208349
theorem B1175465 : Blo 694316 1175465 := bstep (se 2 (by rfl) ⟨440799, by rfl⟩ : syracuseStep 1175465 = 881599) B881599
theorem B782383 : Blo 694316 782383 := bstep (se 1 (by rfl) ⟨586787, by rfl⟩ : syracuseStep 782383 = 1173575) B1173575
theorem B1568879 : Blo 694316 1568879 := bstep (se 1 (by rfl) ⟨1176659, by rfl⟩ : syracuseStep 1568879 = 2353319) B2353319
theorem B18116741 : Blo 694316 18116741 := bstep (se 4 (by rfl) ⟨1698444, by rfl⟩ : syracuseStep 18116741 = 3396889) B3396889
theorem B1044647 : Blo 694316 1044647 := bstep (se 1 (by rfl) ⟨783485, by rfl⟩ : syracuseStep 1044647 = 1566971) B1566971
theorem B1045019 : Blo 694316 1045019 := bstep (se 1 (by rfl) ⟨783764, by rfl⟩ : syracuseStep 1045019 = 1567529) B1567529
theorem B1045487 : Blo 694316 1045487 := bstep (se 1 (by rfl) ⟨784115, by rfl⟩ : syracuseStep 1045487 = 1568231) B1568231
theorem B881695 : Blo 694316 881695 := bstep (se 1 (by rfl) ⟨661271, by rfl⟩ : syracuseStep 881695 = 1322543) B1322543
theorem B3961979 : Blo 694316 3961979 := bstep (se 1 (by rfl) ⟨2971484, by rfl⟩ : syracuseStep 3961979 = 5942969) B5942969
theorem B1766569 : Blo 694316 1766569 := bstep (se 2 (by rfl) ⟨662463, by rfl⟩ : syracuseStep 1766569 = 1324927) B1324927
theorem B1766711 : Blo 694316 1766711 := bstep (se 1 (by rfl) ⟨1325033, by rfl⟩ : syracuseStep 1766711 = 2650067) B2650067
theorem B1045871 : Blo 694316 1045871 := bstep (se 1 (by rfl) ⟨784403, by rfl⟩ : syracuseStep 1045871 = 1568807) B1568807
theorem B1570175 : Blo 694316 1570175 := bstep (se 1 (by rfl) ⟨1177631, by rfl⟩ : syracuseStep 1570175 = 2355263) B2355263
theorem B26768879 : Blo 694316 26768879 := bstep (se 1 (by rfl) ⟨20076659, by rfl⟩ : syracuseStep 26768879 = 40153319) B40153319
theorem B1570715 : Blo 694316 1570715 := bstep (se 1 (by rfl) ⟨1178036, by rfl⟩ : syracuseStep 1570715 = 2356073) B2356073
theorem B1046591 : Blo 694316 1046591 := bstep (se 1 (by rfl) ⟨784943, by rfl⟩ : syracuseStep 1046591 = 1569887) B1569887
theorem B1571039 : Blo 694316 1571039 := bstep (se 1 (by rfl) ⟨1178279, by rfl⟩ : syracuseStep 1571039 = 2356559) B2356559
theorem B30178655 : Blo 694316 30178655 := bstep (se 1 (by rfl) ⟨22633991, by rfl⟩ : syracuseStep 30178655 = 45267983) B45267983
theorem B4587005 : Blo 694316 4587005 := bstep (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) B1720127
theorem B9633725 : Blo 694316 9633725 := bstep (se 3 (by rfl) ⟨1806323, by rfl⟩ : syracuseStep 9633725 = 3612647) B3612647
theorem B3964895 : Blo 694316 3964895 := bstep (se 1 (by rfl) ⟨2973671, by rfl⟩ : syracuseStep 3964895 = 5947343) B5947343
theorem B4227335 : Blo 694316 4227335 := bstep (se 1 (by rfl) ⟨3170501, by rfl⟩ : syracuseStep 4227335 = 6341003) B6341003
theorem B26083685 : Blo 694316 26083685 := bstep (se 4 (by rfl) ⟨2445345, by rfl⟩ : syracuseStep 26083685 = 4890691) B4890691
theorem B5964191 : Blo 694316 5964191 := bstep (se 1 (by rfl) ⟨4473143, by rfl⟩ : syracuseStep 5964191 = 8946287) B8946287
theorem B2066395 : Blo 694316 2066395 := bstep (se 1 (by rfl) ⟨1549796, by rfl⟩ : syracuseStep 2066395 = 3099593) B3099593
theorem B8915579 : Blo 694316 8915579 := bstep (se 1 (by rfl) ⟨6686684, by rfl⟩ : syracuseStep 8915579 = 13373369) B13373369
theorem B1116985 : Blo 694316 1116985 := bstep (se 2 (by rfl) ⟨418869, by rfl⟩ : syracuseStep 1116985 = 837739) B837739
theorem B1674047 : Blo 694316 1674047 := bstep (se 1 (by rfl) ⟨1255535, by rfl⟩ : syracuseStep 1674047 = 2511071) B2511071
theorem B12717611 : Blo 694316 12717611 := bstep (se 1 (by rfl) ⟨9538208, by rfl⟩ : syracuseStep 12717611 = 19076417) B19076417
theorem B1117979 : Blo 694316 1117979 := bstep (se 1 (by rfl) ⟨838484, by rfl⟩ : syracuseStep 1117979 = 1676969) B1676969
theorem B694335 : Blo 694316 694335 := bstep (se 1 (by rfl) ⟨520751, by rfl⟩ : syracuseStep 694335 = 1041503) B1041503
theorem B694939 : Blo 694316 694939 := bstep (se 1 (by rfl) ⟨521204, by rfl⟩ : syracuseStep 694939 = 1042409) B1042409
theorem B5085983 : Blo 694316 5085983 := bstep (se 1 (by rfl) ⟨3814487, by rfl⟩ : syracuseStep 5085983 = 7628975) B7628975
theorem B16980947 : Blo 694316 16980947 := bstep (se 1 (by rfl) ⟨12735710, by rfl⟩ : syracuseStep 16980947 = 25471421) B25471421
theorem B695423 : Blo 694316 695423 := bstep (se 1 (by rfl) ⟨521567, by rfl⟩ : syracuseStep 695423 = 1043135) B1043135
theorem B7937351 : Blo 694316 7937351 := bstep (se 1 (by rfl) ⟨5953013, by rfl⟩ : syracuseStep 7937351 = 11906027) B11906027
theorem B1252831 : Blo 694316 1252831 := bstep (se 1 (by rfl) ⟨939623, by rfl⟩ : syracuseStep 1252831 = 1879247) B1879247
theorem B14491369 : Blo 694316 14491369 := bstep (se 2 (by rfl) ⟨5434263, by rfl⟩ : syracuseStep 14491369 = 10868527) B10868527
theorem B696431 : Blo 694316 696431 := bstep (se 1 (by rfl) ⟨522323, by rfl⟩ : syracuseStep 696431 = 1044647) B1044647
theorem B2826395 : Blo 694316 2826395 := bstep (se 1 (by rfl) ⟨2119796, by rfl⟩ : syracuseStep 2826395 = 4239593) B4239593
theorem B696679 : Blo 694316 696679 := bstep (se 1 (by rfl) ⟨522509, by rfl⟩ : syracuseStep 696679 = 1045019) B1045019
theorem B1319399 : Blo 694316 1319399 := bstep (se 1 (by rfl) ⟨989549, by rfl⟩ : syracuseStep 1319399 = 1979099) B1979099
theorem B696991 : Blo 694316 696991 := bstep (se 1 (by rfl) ⟨522743, by rfl⟩ : syracuseStep 696991 = 1045487) B1045487
theorem B697247 : Blo 694316 697247 := bstep (se 1 (by rfl) ⟨522935, by rfl⟩ : syracuseStep 697247 = 1045871) B1045871
theorem B6694163 : Blo 694316 6694163 := bstep (se 1 (by rfl) ⟨5020622, by rfl⟩ : syracuseStep 6694163 = 10041245) B10041245
theorem B1320295 : Blo 694316 1320295 := bstep (se 1 (by rfl) ⟨990221, by rfl⟩ : syracuseStep 1320295 = 1980443) B1980443
theorem B697727 : Blo 694316 697727 := bstep (se 1 (by rfl) ⟨523295, by rfl⟩ : syracuseStep 697727 = 1046591) B1046591
theorem B3058003 : Blo 694316 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B27208331 : Blo 694316 27208331 := bstep (se 1 (by rfl) ⟨20406248, by rfl⟩ : syracuseStep 27208331 = 40812497) B40812497
theorem B1977185 : Blo 694316 1977185 := bstep (se 2 (by rfl) ⟨741444, by rfl⟩ : syracuseStep 1977185 = 1482889) B1482889
theorem B3517343 : Blo 694316 3517343 := bstep (se 1 (by rfl) ⟨2638007, by rfl⟩ : syracuseStep 3517343 = 5276015) B5276015
theorem B48311309 : Blo 694316 48311309 := bstep (se 3 (by rfl) ⟨9058370, by rfl⟩ : syracuseStep 48311309 = 18116741) B18116741
theorem B5287193 : Blo 694316 5287193 := bstep (se 2 (by rfl) ⟨1982697, by rfl⟩ : syracuseStep 5287193 = 3965395) B3965395
theorem B3976559 : Blo 694316 3976559 := bstep (se 1 (by rfl) ⟨2982419, by rfl⟩ : syracuseStep 3976559 = 5964839) B5964839
theorem B8564201 : Blo 694316 8564201 := bstep (se 2 (by rfl) ⟨3211575, by rfl⟩ : syracuseStep 8564201 = 6423151) B6423151
theorem B1322831 : Blo 694316 1322831 := bstep (se 1 (by rfl) ⟨992123, by rfl⟩ : syracuseStep 1322831 = 1984247) B1984247
theorem B3518639 : Blo 694316 3518639 := bstep (se 1 (by rfl) ⟨2638979, by rfl⟩ : syracuseStep 3518639 = 5277959) B5277959
theorem B1487263 : Blo 694316 1487263 := bstep (se 1 (by rfl) ⟨1115447, by rfl⟩ : syracuseStep 1487263 = 2230895) B2230895
theorem B1782503 : Blo 694316 1782503 := bstep (se 1 (by rfl) ⟨1336877, by rfl⟩ : syracuseStep 1782503 = 2673755) B2673755
theorem B1323803 : Blo 694316 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B1586017 : Blo 694316 1586017 := bstep (se 2 (by rfl) ⟨594756, by rfl⟩ : syracuseStep 1586017 = 1189513) B1189513
theorem B4469863 : Blo 694316 4469863 := bstep (se 1 (by rfl) ⟨3352397, by rfl⟩ : syracuseStep 4469863 = 6704795) B6704795
theorem B1324343 : Blo 694316 1324343 := bstep (se 1 (by rfl) ⟨993257, by rfl⟩ : syracuseStep 1324343 = 1986515) B1986515
theorem B10303199 : Blo 694316 10303199 := bstep (se 1 (by rfl) ⟨7727399, by rfl⟩ : syracuseStep 10303199 = 15454799) B15454799
theorem B1325231 : Blo 694316 1325231 := bstep (se 1 (by rfl) ⟨993923, by rfl⟩ : syracuseStep 1325231 = 1987847) B1987847
theorem B7944641 : Blo 694316 7944641 := bstep (se 2 (by rfl) ⟨2979240, by rfl⟩ : syracuseStep 7944641 = 5958481) B5958481
theorem B6766699 : Blo 694316 6766699 := bstep (se 1 (by rfl) ⟨5075024, by rfl⟩ : syracuseStep 6766699 = 10150049) B10150049
theorem B5030009 : Blo 694316 5030009 := bstep (se 2 (by rfl) ⟨1886253, by rfl⟩ : syracuseStep 5030009 = 3772507) B3772507
theorem B64471565 : Blo 694316 64471565 := bstep (se 3 (by rfl) ⟨12088418, by rfl⟩ : syracuseStep 64471565 = 24176837) B24176837
theorem B45106055 : Blo 694316 45106055 := bstep (se 1 (by rfl) ⟨33829541, by rfl⟩ : syracuseStep 45106055 = 67659083) B67659083
theorem B1885153 : Blo 694316 1885153 := bstep (se 2 (by rfl) ⟨706932, by rfl⟩ : syracuseStep 1885153 = 1413865) B1413865
theorem B3524633 : Blo 694316 3524633 := bstep (se 2 (by rfl) ⟨1321737, by rfl⟩ : syracuseStep 3524633 = 2643475) B2643475
theorem B1984999 : Blo 694316 1984999 := bstep (se 1 (by rfl) ⟨1488749, by rfl⟩ : syracuseStep 1984999 = 2977499) B2977499
theorem B2116489 : Blo 694316 2116489 := bstep (se 2 (by rfl) ⟨793683, by rfl⟩ : syracuseStep 2116489 = 1587367) B1587367
theorem B2345975 : Blo 694316 2345975 := bstep (se 1 (by rfl) ⟨1759481, by rfl⟩ : syracuseStep 2345975 = 3518963) B3518963
theorem B2346191 : Blo 694316 2346191 := bstep (se 1 (by rfl) ⟨1759643, by rfl⟩ : syracuseStep 2346191 = 3519287) B3519287
theorem B2641319 : Blo 694316 2641319 := bstep (se 1 (by rfl) ⟨1980989, by rfl⟩ : syracuseStep 2641319 = 3961979) B3961979
theorem B17845919 : Blo 694316 17845919 := bstep (se 1 (by rfl) ⟨13384439, by rfl⟩ : syracuseStep 17845919 = 26768879) B26768879
theorem B2346839 : Blo 694316 2346839 := bstep (se 1 (by rfl) ⟨1760129, by rfl⟩ : syracuseStep 2346839 = 3520259) B3520259
theorem B2642489 : Blo 694316 2642489 := bstep (se 2 (by rfl) ⟨990933, by rfl⟩ : syracuseStep 2642489 = 1981867) B1981867
theorem B2348297 : Blo 694316 2348297 := bstep (se 2 (by rfl) ⟨880611, by rfl⟩ : syracuseStep 2348297 = 1761223) B1761223
theorem B2643263 : Blo 694316 2643263 := bstep (se 1 (by rfl) ⟨1982447, by rfl⟩ : syracuseStep 2643263 = 3964895) B3964895
theorem B2348459 : Blo 694316 2348459 := bstep (se 1 (by rfl) ⟨1761344, by rfl⟩ : syracuseStep 2348459 = 3522689) B3522689
theorem B7951931 : Blo 694316 7951931 := bstep (se 1 (by rfl) ⟨5963948, by rfl⟩ : syracuseStep 7951931 = 11927897) B11927897
theorem B2348783 : Blo 694316 2348783 := bstep (se 1 (by rfl) ⟨1761587, by rfl⟩ : syracuseStep 2348783 = 3523175) B3523175
theorem B1759097 : Blo 694316 1759097 := bstep (se 2 (by rfl) ⟨659661, by rfl⟩ : syracuseStep 1759097 = 1319323) B1319323
theorem B3955007 : Blo 694316 3955007 := bstep (se 1 (by rfl) ⟨2966255, by rfl⟩ : syracuseStep 3955007 = 5932511) B5932511
theorem B1563371 : Blo 694316 1563371 := bstep (se 1 (by rfl) ⟨1172528, by rfl⟩ : syracuseStep 1563371 = 2345057) B2345057
theorem B3955463 : Blo 694316 3955463 := bstep (se 1 (by rfl) ⟨2966597, by rfl⟩ : syracuseStep 3955463 = 5933195) B5933195
theorem B2120575 : Blo 694316 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B1269049 : Blo 694316 1269049 := bstep (se 2 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 1269049 = 951787) B951787
theorem B6970835 : Blo 694316 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B1761335 : Blo 694316 1761335 := bstep (se 1 (by rfl) ⟨1321001, by rfl⟩ : syracuseStep 1761335 = 2642003) B2642003
theorem B2351159 : Blo 694316 2351159 := bstep (se 1 (by rfl) ⟨1763369, by rfl⟩ : syracuseStep 2351159 = 3526739) B3526739
theorem B1564955 : Blo 694316 1564955 := bstep (se 1 (by rfl) ⟨1173716, by rfl⟩ : syracuseStep 1564955 = 2347433) B2347433
theorem B1171867 : Blo 694316 1171867 := bstep (se 1 (by rfl) ⟨878900, by rfl⟩ : syracuseStep 1171867 = 1757801) B1757801
theorem B1565099 : Blo 694316 1565099 := bstep (se 1 (by rfl) ⟨1173824, by rfl⟩ : syracuseStep 1565099 = 2347649) B2347649
theorem B1172009 : Blo 694316 1172009 := bstep (se 2 (by rfl) ⟨439503, by rfl⟩ : syracuseStep 1172009 = 879007) B879007
theorem B7529057 : Blo 694316 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B1041563 : Blo 694316 1041563 := bstep (se 1 (by rfl) ⟨781172, by rfl⟩ : syracuseStep 1041563 = 1562345) B1562345
theorem B1566035 : Blo 694316 1566035 := bstep (se 1 (by rfl) ⟨1174526, by rfl⟩ : syracuseStep 1566035 = 2349053) B2349053
theorem B1172839 : Blo 694316 1172839 := bstep (se 1 (by rfl) ⟨879629, by rfl⟩ : syracuseStep 1172839 = 1759259) B1759259
theorem B2352887 : Blo 694316 2352887 := bstep (se 1 (by rfl) ⟨1764665, by rfl⟩ : syracuseStep 2352887 = 3529331) B3529331
theorem B1173359 : Blo 694316 1173359 := bstep (se 1 (by rfl) ⟨880019, by rfl⟩ : syracuseStep 1173359 = 1760039) B1760039
theorem B1042715 : Blo 694316 1042715 := bstep (se 1 (by rfl) ⟨782036, by rfl⟩ : syracuseStep 1042715 = 1564073) B1564073
theorem B9660799 : Blo 694316 9660799 := bstep (se 1 (by rfl) ⟨7245599, by rfl⟩ : syracuseStep 9660799 = 14491199) B14491199
theorem B1042895 : Blo 694316 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B2353643 : Blo 694316 2353643 := bstep (se 1 (by rfl) ⟨1765232, by rfl⟩ : syracuseStep 2353643 = 3530465) B3530465
theorem B1043177 : Blo 694316 1043177 := bstep (se 2 (by rfl) ⟨391191, by rfl⟩ : syracuseStep 1043177 = 782383) B782383
theorem B1043231 : Blo 694316 1043231 := bstep (se 1 (by rfl) ⟨782423, by rfl⟩ : syracuseStep 1043231 = 1564847) B1564847
theorem B781159 : Blo 694316 781159 := bstep (se 1 (by rfl) ⟨585869, by rfl⟩ : syracuseStep 781159 = 1171739) B1171739
theorem B3566567 : Blo 694316 3566567 := bstep (se 1 (by rfl) ⟨2674925, by rfl⟩ : syracuseStep 3566567 = 5349851) B5349851
theorem B1567835 : Blo 694316 1567835 := bstep (se 1 (by rfl) ⟨1175876, by rfl⟩ : syracuseStep 1567835 = 2351753) B2351753
theorem B1174763 : Blo 694316 1174763 := bstep (se 1 (by rfl) ⟨881072, by rfl⟩ : syracuseStep 1174763 = 1762145) B1762145
theorem B716027 : Blo 694316 716027 := bstep (se 1 (by rfl) ⟨537020, by rfl⟩ : syracuseStep 716027 = 1074041) B1074041
theorem B1043711 : Blo 694316 1043711 := bstep (se 1 (by rfl) ⟨782783, by rfl⟩ : syracuseStep 1043711 = 1565567) B1565567
theorem B1044191 : Blo 694316 1044191 := bstep (se 1 (by rfl) ⟨783143, by rfl⟩ : syracuseStep 1044191 = 1566287) B1566287
theorem B1175593 : Blo 694316 1175593 := bstep (se 2 (by rfl) ⟨440847, by rfl⟩ : syracuseStep 1175593 = 881695) B881695
theorem B1044527 : Blo 694316 1044527 := bstep (se 1 (by rfl) ⟨783395, by rfl⟩ : syracuseStep 1044527 = 1566791) B1566791
theorem B1044587 : Blo 694316 1044587 := bstep (se 1 (by rfl) ⟨783440, by rfl⟩ : syracuseStep 1044587 = 1566881) B1566881
theorem B1044671 : Blo 694316 1044671 := bstep (se 1 (by rfl) ⟨783503, by rfl⟩ : syracuseStep 1044671 = 1567007) B1567007
theorem B2355425 : Blo 694316 2355425 := bstep (se 2 (by rfl) ⟨883284, by rfl⟩ : syracuseStep 2355425 = 1766569) B1766569
theorem B3338653 : Blo 694316 3338653 := bstep (se 3 (by rfl) ⟨625997, by rfl⟩ : syracuseStep 3338653 = 1251995) B1251995
theorem B2224847 : Blo 694316 2224847 := bstep (se 1 (by rfl) ⟨1668635, by rfl⟩ : syracuseStep 2224847 = 3337271) B3337271
theorem B1045439 : Blo 694316 1045439 := bstep (se 1 (by rfl) ⟨784079, by rfl⟩ : syracuseStep 1045439 = 1568159) B1568159
theorem B1176511 : Blo 694316 1176511 := bstep (se 1 (by rfl) ⟨882383, by rfl⟩ : syracuseStep 1176511 = 1764767) B1764767
theorem B1045607 : Blo 694316 1045607 := bstep (se 1 (by rfl) ⟨784205, by rfl⟩ : syracuseStep 1045607 = 1568411) B1568411
theorem B783643 : Blo 694316 783643 := bstep (se 1 (by rfl) ⟨587732, by rfl⟩ : syracuseStep 783643 = 1175465) B1175465
theorem B2979139 : Blo 694316 2979139 := bstep (se 1 (by rfl) ⟨2234354, by rfl⟩ : syracuseStep 2979139 = 4468709) B4468709
theorem B1045919 : Blo 694316 1045919 := bstep (se 1 (by rfl) ⟨784439, by rfl⟩ : syracuseStep 1045919 = 1568879) B1568879
theorem B1177807 : Blo 694316 1177807 := bstep (se 1 (by rfl) ⟨883355, by rfl⟩ : syracuseStep 1177807 = 1766711) B1766711
theorem B1046783 : Blo 694316 1046783 := bstep (se 1 (by rfl) ⟨785087, by rfl⟩ : syracuseStep 1046783 = 1570175) B1570175
theorem B1047143 : Blo 694316 1047143 := bstep (se 1 (by rfl) ⟨785357, by rfl⟩ : syracuseStep 1047143 = 1570715) B1570715
theorem B21723805 : Blo 694316 21723805 := bstep (se 3 (by rfl) ⟨4073213, by rfl⟩ : syracuseStep 21723805 = 8146427) B8146427
theorem B1047359 : Blo 694316 1047359 := bstep (se 1 (by rfl) ⟨785519, by rfl⟩ : syracuseStep 1047359 = 1571039) B1571039
theorem B20119103 : Blo 694316 20119103 := bstep (se 1 (by rfl) ⟨15089327, by rfl⟩ : syracuseStep 20119103 = 30178655) B30178655
theorem B96370397 : Blo 694316 96370397 := bstep (se 3 (by rfl) ⟨18069449, by rfl⟩ : syracuseStep 96370397 = 36138899) B36138899
theorem B6422483 : Blo 694316 6422483 := bstep (se 1 (by rfl) ⟨4816862, by rfl⟩ : syracuseStep 6422483 = 9633725) B9633725
theorem B2818223 : Blo 694316 2818223 := bstep (se 1 (by rfl) ⟨2113667, by rfl⟩ : syracuseStep 2818223 = 4227335) B4227335
theorem B1116031 : Blo 694316 1116031 := bstep (se 1 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 1116031 = 1674047) B1674047
theorem B11897279 : Blo 694316 11897279 := bstep (se 1 (by rfl) ⟨8922959, by rfl⟩ : syracuseStep 11897279 = 17845919) B17845919
theorem B2755193 : Blo 694316 2755193 := bstep (se 2 (by rfl) ⟨1033197, by rfl⟩ : syracuseStep 2755193 = 2066395) B2066395
theorem B12881065 : Blo 694316 12881065 := bstep (se 2 (by rfl) ⟨4830399, by rfl⟩ : syracuseStep 12881065 = 9660799) B9660799
theorem B2821985 : Blo 694316 2821985 := bstep (se 2 (by rfl) ⟨1058244, by rfl⟩ : syracuseStep 2821985 = 2116489) B2116489
theorem B5019371 : Blo 694316 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B694375 : Blo 694316 694375 := bstep (se 1 (by rfl) ⟨520781, by rfl⟩ : syracuseStep 694375 = 1041563) B1041563
theorem B4462775 : Blo 694316 4462775 := bstep (se 1 (by rfl) ⟨3347081, by rfl⟩ : syracuseStep 4462775 = 6694163) B6694163
theorem B695143 : Blo 694316 695143 := bstep (se 1 (by rfl) ⟨521357, by rfl⟩ : syracuseStep 695143 = 1042715) B1042715
theorem B695263 : Blo 694316 695263 := bstep (se 1 (by rfl) ⟨521447, by rfl⟩ : syracuseStep 695263 = 1042895) B1042895
theorem B3972185 : Blo 694316 3972185 := bstep (se 2 (by rfl) ⟨1489569, by rfl⟩ : syracuseStep 3972185 = 2979139) B2979139
theorem B695451 : Blo 694316 695451 := bstep (se 1 (by rfl) ⟨521588, by rfl⟩ : syracuseStep 695451 = 1043177) B1043177
theorem B695487 : Blo 694316 695487 := bstep (se 1 (by rfl) ⟨521615, by rfl⟩ : syracuseStep 695487 = 1043231) B1043231
theorem B1318123 : Blo 694316 1318123 := bstep (se 1 (by rfl) ⟨988592, by rfl⟩ : syracuseStep 1318123 = 1977185) B1977185
theorem B695807 : Blo 694316 695807 := bstep (se 1 (by rfl) ⟨521855, by rfl⟩ : syracuseStep 695807 = 1043711) B1043711
theorem B5709467 : Blo 694316 5709467 := bstep (se 1 (by rfl) ⟨4282100, by rfl⟩ : syracuseStep 5709467 = 8564201) B8564201
theorem B696127 : Blo 694316 696127 := bstep (se 1 (by rfl) ⟨522095, by rfl⟩ : syracuseStep 696127 = 1044191) B1044191
theorem B696351 : Blo 694316 696351 := bstep (se 1 (by rfl) ⟨522263, by rfl⟩ : syracuseStep 696351 = 1044527) B1044527
theorem B696391 : Blo 694316 696391 := bstep (se 1 (by rfl) ⟨522293, by rfl⟩ : syracuseStep 696391 = 1044587) B1044587
theorem B696447 : Blo 694316 696447 := bstep (se 1 (by rfl) ⟨522335, by rfl⟩ : syracuseStep 696447 = 1044671) B1044671
theorem B1483231 : Blo 694316 1483231 := bstep (se 1 (by rfl) ⟨1112423, by rfl⟩ : syracuseStep 1483231 = 2224847) B2224847
theorem B1188335 : Blo 694316 1188335 := bstep (se 1 (by rfl) ⟨891251, by rfl⟩ : syracuseStep 1188335 = 1782503) B1782503
theorem B696959 : Blo 694316 696959 := bstep (se 1 (by rfl) ⟨522719, by rfl⟩ : syracuseStep 696959 = 1045439) B1045439
theorem B1909405 : Blo 694316 1909405 := bstep (se 3 (by rfl) ⟨358013, by rfl⟩ : syracuseStep 1909405 = 716027) B716027
theorem B697071 : Blo 694316 697071 := bstep (se 1 (by rfl) ⟨522803, by rfl⟩ : syracuseStep 697071 = 1045607) B1045607
theorem B697279 : Blo 694316 697279 := bstep (se 1 (by rfl) ⟨522959, by rfl⟩ : syracuseStep 697279 = 1045919) B1045919
theorem B2827433 : Blo 694316 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B697855 : Blo 694316 697855 := bstep (se 1 (by rfl) ⟨523391, by rfl⟩ : syracuseStep 697855 = 1046783) B1046783
theorem B698095 : Blo 694316 698095 := bstep (se 1 (by rfl) ⟨523571, by rfl⟩ : syracuseStep 698095 = 1047143) B1047143
theorem B698239 : Blo 694316 698239 := bstep (se 1 (by rfl) ⟨523679, by rfl⟩ : syracuseStep 698239 = 1047359) B1047359
theorem B13412735 : Blo 694316 13412735 := bstep (se 1 (by rfl) ⟨10059551, by rfl⟩ : syracuseStep 13412735 = 20119103) B20119103
theorem B3353339 : Blo 694316 3353339 := bstep (se 1 (by rfl) ⟨2515004, by rfl⟩ : syracuseStep 3353339 = 5030009) B5030009
theorem B9022265 : Blo 694316 9022265 := bstep (se 2 (by rfl) ⟨3383349, by rfl⟩ : syracuseStep 9022265 = 6766699) B6766699
theorem B3976127 : Blo 694316 3976127 := bstep (se 1 (by rfl) ⟨2982095, by rfl⟩ : syracuseStep 3976127 = 5964191) B5964191
theorem B5943719 : Blo 694316 5943719 := bstep (se 1 (by rfl) ⟨4457789, by rfl⟩ : syracuseStep 5943719 = 8915579) B8915579
theorem B1489313 : Blo 694316 1489313 := bstep (se 2 (by rfl) ⟨558492, by rfl⟩ : syracuseStep 1489313 = 1116985) B1116985
theorem B2636671 : Blo 694316 2636671 := bstep (se 1 (by rfl) ⟨1977503, by rfl⟩ : syracuseStep 2636671 = 3955007) B3955007
theorem B2636975 : Blo 694316 2636975 := bstep (se 1 (by rfl) ⟨1977731, by rfl⟩ : syracuseStep 2636975 = 3955463) B3955463
theorem B3390655 : Blo 694316 3390655 := bstep (se 1 (by rfl) ⟨2542991, by rfl⟩ : syracuseStep 3390655 = 5085983) B5085983
theorem B11320631 : Blo 694316 11320631 := bstep (se 1 (by rfl) ⟨8490473, by rfl⟩ : syracuseStep 11320631 = 16980947) B16980947
theorem B5291567 : Blo 694316 5291567 := bstep (se 1 (by rfl) ⟨3968675, by rfl⟩ : syracuseStep 5291567 = 7937351) B7937351
theorem B1884263 : Blo 694316 1884263 := bstep (se 1 (by rfl) ⟨1413197, by rfl⟩ : syracuseStep 1884263 = 2826395) B2826395
theorem B1983017 : Blo 694316 1983017 := bstep (se 2 (by rfl) ⟨743631, by rfl⟩ : syracuseStep 1983017 = 1487263) B1487263
theorem B2114689 : Blo 694316 2114689 := bstep (se 2 (by rfl) ⟨793008, by rfl⟩ : syracuseStep 2114689 = 1586017) B1586017
theorem B18138887 : Blo 694316 18138887 := bstep (se 1 (by rfl) ⟨13604165, by rfl⟩ : syracuseStep 18138887 = 27208331) B27208331
theorem B2344895 : Blo 694316 2344895 := bstep (se 1 (by rfl) ⟨1758671, by rfl⟩ : syracuseStep 2344895 = 3517343) B3517343
theorem B2377711 : Blo 694316 2377711 := bstep (se 1 (by rfl) ⟨1783283, by rfl⟩ : syracuseStep 2377711 = 3566567) B3566567
theorem B3524795 : Blo 694316 3524795 := bstep (se 1 (by rfl) ⟨2643596, by rfl⟩ : syracuseStep 3524795 = 5287193) B5287193
theorem B2345759 : Blo 694316 2345759 := bstep (se 1 (by rfl) ⟨1759319, by rfl⟩ : syracuseStep 2345759 = 3518639) B3518639
theorem B6868799 : Blo 694316 6868799 := bstep (se 1 (by rfl) ⟨5151599, by rfl⟩ : syracuseStep 6868799 = 10303199) B10303199
theorem B5296427 : Blo 694316 5296427 := bstep (se 1 (by rfl) ⟨3972320, by rfl⟩ : syracuseStep 5296427 = 7944641) B7944641
theorem B1692065 : Blo 694316 1692065 := bstep (se 2 (by rfl) ⟨634524, by rfl⟩ : syracuseStep 1692065 = 1269049) B1269049
theorem B3527549 : Blo 694316 3527549 := bstep (se 3 (by rfl) ⟨661415, by rfl⟩ : syracuseStep 3527549 = 1322831) B1322831
theorem B19321825 : Blo 694316 19321825 := bstep (se 2 (by rfl) ⟨7245684, by rfl⟩ : syracuseStep 19321825 = 14491369) B14491369
theorem B64246931 : Blo 694316 64246931 := bstep (se 1 (by rfl) ⟨48185198, by rfl⟩ : syracuseStep 64246931 = 96370397) B96370397
theorem B4281655 : Blo 694316 4281655 := bstep (se 1 (by rfl) ⟨3211241, by rfl⟩ : syracuseStep 4281655 = 6422483) B6422483
theorem B42981043 : Blo 694316 42981043 := bstep (se 1 (by rfl) ⟨32235782, by rfl⟩ : syracuseStep 42981043 = 64471565) B64471565
theorem B1562489 : Blo 694316 1562489 := bstep (se 2 (by rfl) ⟨585933, by rfl⟩ : syracuseStep 1562489 = 1171867) B1171867
theorem B30070703 : Blo 694316 30070703 := bstep (se 1 (by rfl) ⟨22553027, by rfl⟩ : syracuseStep 30070703 = 45106055) B45106055
theorem B69556493 : Blo 694316 69556493 := bstep (se 3 (by rfl) ⟨13041842, by rfl⟩ : syracuseStep 69556493 = 26083685) B26083685
theorem B2513537 : Blo 694316 2513537 := bstep (se 2 (by rfl) ⟨942576, by rfl⟩ : syracuseStep 2513537 = 1885153) B1885153
theorem B2349755 : Blo 694316 2349755 := bstep (se 1 (by rfl) ⟨1762316, by rfl⟩ : syracuseStep 2349755 = 3524633) B3524633
theorem B16309349 : Blo 694316 16309349 := bstep (se 4 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 16309349 = 3058003) B3058003
theorem B1563785 : Blo 694316 1563785 := bstep (se 2 (by rfl) ⟨586419, by rfl⟩ : syracuseStep 1563785 = 1172839) B1172839
theorem B1760393 : Blo 694316 1760393 := bstep (se 2 (by rfl) ⟨660147, by rfl⟩ : syracuseStep 1760393 = 1320295) B1320295
theorem B1563983 : Blo 694316 1563983 := bstep (se 1 (by rfl) ⟨1172987, by rfl⟩ : syracuseStep 1563983 = 2345975) B2345975
theorem B3530141 : Blo 694316 3530141 := bstep (se 3 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 3530141 = 1323803) B1323803
theorem B1564127 : Blo 694316 1564127 := bstep (se 1 (by rfl) ⟨1173095, by rfl⟩ : syracuseStep 1564127 = 2346191) B2346191
theorem B1760879 : Blo 694316 1760879 := bstep (se 1 (by rfl) ⟨1320659, by rfl⟩ : syracuseStep 1760879 = 2641319) B2641319
theorem B8478407 : Blo 694316 8478407 := bstep (se 1 (by rfl) ⟨6358805, by rfl⟩ : syracuseStep 8478407 = 12717611) B12717611
theorem B745319 : Blo 694316 745319 := bstep (se 1 (by rfl) ⟨558989, by rfl⟩ : syracuseStep 745319 = 1117979) B1117979
theorem B1564559 : Blo 694316 1564559 := bstep (se 1 (by rfl) ⟨1173419, by rfl⟩ : syracuseStep 1564559 = 2346839) B2346839
theorem B1761659 : Blo 694316 1761659 := bstep (se 1 (by rfl) ⟨1321244, by rfl⟩ : syracuseStep 1761659 = 2642489) B2642489
theorem B2646665 : Blo 694316 2646665 := bstep (se 2 (by rfl) ⟨992499, by rfl⟩ : syracuseStep 2646665 = 1984999) B1984999
theorem B1565531 : Blo 694316 1565531 := bstep (se 1 (by rfl) ⟨1174148, by rfl⟩ : syracuseStep 1565531 = 2348297) B2348297
theorem B1762175 : Blo 694316 1762175 := bstep (se 1 (by rfl) ⟨1321631, by rfl⟩ : syracuseStep 1762175 = 2643263) B2643263
theorem B1565639 : Blo 694316 1565639 := bstep (se 1 (by rfl) ⟨1174229, by rfl⟩ : syracuseStep 1565639 = 2348459) B2348459
theorem B5301287 : Blo 694316 5301287 := bstep (se 1 (by rfl) ⟨3975965, by rfl⟩ : syracuseStep 5301287 = 7951931) B7951931
theorem B1041545 : Blo 694316 1041545 := bstep (se 2 (by rfl) ⟨390579, by rfl⟩ : syracuseStep 1041545 = 781159) B781159
theorem B1565855 : Blo 694316 1565855 := bstep (se 1 (by rfl) ⟨1174391, by rfl⟩ : syracuseStep 1565855 = 2348783) B2348783
theorem B1172731 : Blo 694316 1172731 := bstep (se 1 (by rfl) ⟨879548, by rfl⟩ : syracuseStep 1172731 = 1759097) B1759097
theorem B1042247 : Blo 694316 1042247 := bstep (se 1 (by rfl) ⟨781685, by rfl⟩ : syracuseStep 1042247 = 1563371) B1563371
theorem B4647223 : Blo 694316 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B1174223 : Blo 694316 1174223 := bstep (se 1 (by rfl) ⟨880667, by rfl⟩ : syracuseStep 1174223 = 1761335) B1761335
theorem B1567439 : Blo 694316 1567439 := bstep (se 1 (by rfl) ⟨1175579, by rfl⟩ : syracuseStep 1567439 = 2351159) B2351159
theorem B1567457 : Blo 694316 1567457 := bstep (se 2 (by rfl) ⟨587796, by rfl⟩ : syracuseStep 1567457 = 1175593) B1175593
theorem B1043303 : Blo 694316 1043303 := bstep (se 1 (by rfl) ⟨782477, by rfl⟩ : syracuseStep 1043303 = 1564955) B1564955
theorem B1043399 : Blo 694316 1043399 := bstep (se 1 (by rfl) ⟨782549, by rfl⟩ : syracuseStep 1043399 = 1565099) B1565099
theorem B879599 : Blo 694316 879599 := bstep (se 1 (by rfl) ⟨659699, by rfl⟩ : syracuseStep 879599 = 1319399) B1319399
theorem B781339 : Blo 694316 781339 := bstep (se 1 (by rfl) ⟨586004, by rfl⟩ : syracuseStep 781339 = 1172009) B1172009
theorem B4451537 : Blo 694316 4451537 := bstep (se 2 (by rfl) ⟨1669326, by rfl⟩ : syracuseStep 4451537 = 3338653) B3338653
theorem B1044023 : Blo 694316 1044023 := bstep (se 1 (by rfl) ⟨783017, by rfl⟩ : syracuseStep 1044023 = 1566035) B1566035
theorem B1568591 : Blo 694316 1568591 := bstep (se 1 (by rfl) ⟨1176443, by rfl⟩ : syracuseStep 1568591 = 2352887) B2352887
theorem B782239 : Blo 694316 782239 := bstep (se 1 (by rfl) ⟨586679, by rfl⟩ : syracuseStep 782239 = 1173359) B1173359
theorem B1568681 : Blo 694316 1568681 := bstep (se 2 (by rfl) ⟨588255, by rfl⟩ : syracuseStep 1568681 = 1176511) B1176511
theorem B5959817 : Blo 694316 5959817 := bstep (se 2 (by rfl) ⟨2234931, by rfl⟩ : syracuseStep 5959817 = 4469863) B4469863
theorem B1569095 : Blo 694316 1569095 := bstep (se 1 (by rfl) ⟨1176821, by rfl⟩ : syracuseStep 1569095 = 2353643) B2353643
theorem B1044857 : Blo 694316 1044857 := bstep (se 2 (by rfl) ⟨391821, by rfl⟩ : syracuseStep 1044857 = 783643) B783643
theorem B32207539 : Blo 694316 32207539 := bstep (se 1 (by rfl) ⟨24155654, by rfl⟩ : syracuseStep 32207539 = 48311309) B48311309
theorem B1045223 : Blo 694316 1045223 := bstep (se 1 (by rfl) ⟨783917, by rfl⟩ : syracuseStep 1045223 = 1567835) B1567835
theorem B783175 : Blo 694316 783175 := bstep (se 1 (by rfl) ⟨587381, by rfl⟩ : syracuseStep 783175 = 1174763) B1174763
theorem B2651039 : Blo 694316 2651039 := bstep (se 1 (by rfl) ⟨1988279, by rfl⟩ : syracuseStep 2651039 = 3976559) B3976559
theorem B1570283 : Blo 694316 1570283 := bstep (se 1 (by rfl) ⟨1177712, by rfl⟩ : syracuseStep 1570283 = 2355425) B2355425
theorem B1570409 : Blo 694316 1570409 := bstep (se 2 (by rfl) ⟨588903, by rfl⟩ : syracuseStep 1570409 = 1177807) B1177807
theorem B882895 : Blo 694316 882895 := bstep (se 1 (by rfl) ⟨662171, by rfl⟩ : syracuseStep 882895 = 1324343) B1324343
theorem B28965073 : Blo 694316 28965073 := bstep (se 2 (by rfl) ⟨10861902, by rfl⟩ : syracuseStep 28965073 = 21723805) B21723805
theorem B883487 : Blo 694316 883487 := bstep (se 1 (by rfl) ⟨662615, by rfl⟩ : syracuseStep 883487 = 1325231) B1325231
theorem B1670441 : Blo 694316 1670441 := bstep (se 2 (by rfl) ⟨626415, by rfl⟩ : syracuseStep 1670441 = 1252831) B1252831
theorem B12092591 : Blo 694316 12092591 := bstep (se 1 (by rfl) ⟨9069443, by rfl⟩ : syracuseStep 12092591 = 18138887) B18138887
theorem B2819585 : Blo 694316 2819585 := bstep (se 2 (by rfl) ⟨1057344, by rfl⟩ : syracuseStep 2819585 = 2114689) B2114689
theorem B7931519 : Blo 694316 7931519 := bstep (se 1 (by rfl) ⟨5948639, by rfl⟩ : syracuseStep 7931519 = 11897279) B11897279
theorem B42831287 : Blo 694316 42831287 := bstep (se 1 (by rfl) ⟨32123465, by rfl⟩ : syracuseStep 42831287 = 64246931) B64246931
theorem B3346247 : Blo 694316 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B17174753 : Blo 694316 17174753 := bstep (se 2 (by rfl) ⟨6440532, by rfl⟩ : syracuseStep 17174753 = 12881065) B12881065
theorem B1675691 : Blo 694316 1675691 := bstep (se 1 (by rfl) ⟨1256768, by rfl⟩ : syracuseStep 1675691 = 2513537) B2513537
theorem B694363 : Blo 694316 694363 := bstep (se 1 (by rfl) ⟨520772, by rfl⟩ : syracuseStep 694363 = 1041545) B1041545
theorem B3971501 : Blo 694316 3971501 := bstep (se 3 (by rfl) ⟨744656, by rfl⟩ : syracuseStep 3971501 = 1489313) B1489313
theorem B694831 : Blo 694316 694831 := bstep (se 1 (by rfl) ⟨521123, by rfl⟩ : syracuseStep 694831 = 1042247) B1042247
theorem B25762433 : Blo 694316 25762433 := bstep (se 2 (by rfl) ⟨9660912, by rfl⟩ : syracuseStep 25762433 = 19321825) B19321825
theorem B7347181 : Blo 694316 7347181 := bstep (se 3 (by rfl) ⟨1377596, by rfl⟩ : syracuseStep 7347181 = 2755193) B2755193
theorem B5708873 : Blo 694316 5708873 := bstep (se 2 (by rfl) ⟨2140827, by rfl⟩ : syracuseStep 5708873 = 4281655) B4281655
theorem B2235559 : Blo 694316 2235559 := bstep (se 1 (by rfl) ⟨1676669, by rfl⟩ : syracuseStep 2235559 = 3353339) B3353339
theorem B695535 : Blo 694316 695535 := bstep (se 1 (by rfl) ⟨521651, by rfl⟩ : syracuseStep 695535 = 1043303) B1043303
theorem B695599 : Blo 694316 695599 := bstep (se 1 (by rfl) ⟨521699, by rfl⟩ : syracuseStep 695599 = 1043399) B1043399
theorem B696015 : Blo 694316 696015 := bstep (se 1 (by rfl) ⟨522011, by rfl⟩ : syracuseStep 696015 = 1044023) B1044023
theorem B3973211 : Blo 694316 3973211 := bstep (se 1 (by rfl) ⟨2979908, by rfl⟩ : syracuseStep 3973211 = 5959817) B5959817
theorem B696571 : Blo 694316 696571 := bstep (se 1 (by rfl) ⟨522428, by rfl⟩ : syracuseStep 696571 = 1044857) B1044857
theorem B696815 : Blo 694316 696815 := bstep (se 1 (by rfl) ⟨522611, by rfl⟩ : syracuseStep 696815 = 1045223) B1045223
theorem B3515561 : Blo 694316 3515561 := bstep (se 2 (by rfl) ⟨1318335, by rfl⟩ : syracuseStep 3515561 = 2636671) B2636671
theorem B7547087 : Blo 694316 7547087 := bstep (se 1 (by rfl) ⟨5660315, by rfl⟩ : syracuseStep 7547087 = 11320631) B11320631
theorem B1878815 : Blo 694316 1878815 := bstep (se 1 (by rfl) ⟨1409111, by rfl⟩ : syracuseStep 1878815 = 2818223) B2818223
theorem B5024701 : Blo 694316 5024701 := bstep (se 3 (by rfl) ⟨942131, by rfl⟩ : syracuseStep 5024701 = 1884263) B1884263
theorem B1322011 : Blo 694316 1322011 := bstep (se 1 (by rfl) ⟨991508, by rfl⟩ : syracuseStep 1322011 = 1983017) B1983017
theorem B1977641 : Blo 694316 1977641 := bstep (se 2 (by rfl) ⟨741615, by rfl⟩ : syracuseStep 1977641 = 1483231) B1483231
theorem B24785189 : Blo 694316 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B1488041 : Blo 694316 1488041 := bstep (se 2 (by rfl) ⟨558015, by rfl⟩ : syracuseStep 1488041 = 1116031) B1116031
theorem B1881323 : Blo 694316 1881323 := bstep (se 1 (by rfl) ⟨1410992, by rfl⟩ : syracuseStep 1881323 = 2821985) B2821985
theorem B1128043 : Blo 694316 1128043 := bstep (se 1 (by rfl) ⟨846032, by rfl⟩ : syracuseStep 1128043 = 1692065) B1692065
theorem B5652271 : Blo 694316 5652271 := bstep (se 1 (by rfl) ⟨4239203, by rfl⟩ : syracuseStep 5652271 = 8478407) B8478407
theorem B185483981 : Blo 694316 185483981 := bstep (se 3 (by rfl) ⟨34778246, by rfl⟩ : syracuseStep 185483981 = 69556493) B69556493
theorem B1884955 : Blo 694316 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B42943385 : Blo 694316 42943385 := bstep (se 2 (by rfl) ⟨16103769, by rfl⟩ : syracuseStep 42943385 = 32207539) B32207539
theorem B6014843 : Blo 694316 6014843 := bstep (se 1 (by rfl) ⟨4511132, by rfl⟩ : syracuseStep 6014843 = 9022265) B9022265
theorem B2967691 : Blo 694316 2967691 := bstep (se 1 (by rfl) ⟨2225768, by rfl⟩ : syracuseStep 2967691 = 4451537) B4451537
theorem B2345597 : Blo 694316 2345597 := bstep (se 3 (by rfl) ⟨439799, by rfl⟩ : syracuseStep 2345597 = 879599) B879599
theorem B38620097 : Blo 694316 38620097 := bstep (se 2 (by rfl) ⟨14482536, by rfl⟩ : syracuseStep 38620097 = 28965073) B28965073
theorem B1757497 : Blo 694316 1757497 := bstep (se 2 (by rfl) ⟨659061, by rfl⟩ : syracuseStep 1757497 = 1318123) B1318123
theorem B15225245 : Blo 694316 15225245 := bstep (se 3 (by rfl) ⟨2854733, by rfl⟩ : syracuseStep 15225245 = 5709467) B5709467
theorem B1757983 : Blo 694316 1757983 := bstep (se 1 (by rfl) ⟨1318487, by rfl⟩ : syracuseStep 1757983 = 2636975) B2636975
theorem B1987517 : Blo 694316 1987517 := bstep (se 3 (by rfl) ⟨372659, by rfl⟩ : syracuseStep 1987517 = 745319) B745319
theorem B3527711 : Blo 694316 3527711 := bstep (se 1 (by rfl) ⟨2645783, by rfl⟩ : syracuseStep 3527711 = 5291567) B5291567
theorem B2545873 : Blo 694316 2545873 := bstep (se 2 (by rfl) ⟨954702, by rfl⟩ : syracuseStep 2545873 = 1909405) B1909405
theorem B3168893 : Blo 694316 3168893 := bstep (se 3 (by rfl) ⟨594167, by rfl⟩ : syracuseStep 3168893 = 1188335) B1188335
theorem B1563263 : Blo 694316 1563263 := bstep (se 1 (by rfl) ⟨1172447, by rfl⟩ : syracuseStep 1563263 = 2344895) B2344895
theorem B2349863 : Blo 694316 2349863 := bstep (se 1 (by rfl) ⟨1762397, by rfl⟩ : syracuseStep 2349863 = 3524795) B3524795
theorem B1563641 : Blo 694316 1563641 := bstep (se 2 (by rfl) ⟨586365, by rfl⟩ : syracuseStep 1563641 = 1172731) B1172731
theorem B1563839 : Blo 694316 1563839 := bstep (se 1 (by rfl) ⟨1172879, by rfl⟩ : syracuseStep 1563839 = 2345759) B2345759
theorem B4579199 : Blo 694316 4579199 := bstep (se 1 (by rfl) ⟨3434399, by rfl⟩ : syracuseStep 4579199 = 6868799) B6868799
theorem B3170281 : Blo 694316 3170281 := bstep (se 2 (by rfl) ⟨1188855, by rfl⟩ : syracuseStep 3170281 = 2377711) B2377711
theorem B3530951 : Blo 694316 3530951 := bstep (se 1 (by rfl) ⟨2648213, by rfl⟩ : syracuseStep 3530951 = 5296427) B5296427
theorem B2351699 : Blo 694316 2351699 := bstep (se 1 (by rfl) ⟨1763774, by rfl⟩ : syracuseStep 2351699 = 3527549) B3527549
theorem B1041659 : Blo 694316 1041659 := bstep (se 1 (by rfl) ⟨781244, by rfl⟩ : syracuseStep 1041659 = 1562489) B1562489
theorem B20047135 : Blo 694316 20047135 := bstep (se 1 (by rfl) ⟨15035351, by rfl⟩ : syracuseStep 20047135 = 30070703) B30070703
theorem B1041785 : Blo 694316 1041785 := bstep (se 2 (by rfl) ⟨390669, by rfl⟩ : syracuseStep 1041785 = 781339) B781339
theorem B2975183 : Blo 694316 2975183 := bstep (se 1 (by rfl) ⟨2231387, by rfl⟩ : syracuseStep 2975183 = 4462775) B4462775
theorem B1566503 : Blo 694316 1566503 := bstep (se 1 (by rfl) ⟨1174877, by rfl⟩ : syracuseStep 1566503 = 2349755) B2349755
theorem B2648123 : Blo 694316 2648123 := bstep (se 1 (by rfl) ⟨1986092, by rfl⟩ : syracuseStep 2648123 = 3972185) B3972185
theorem B10872899 : Blo 694316 10872899 := bstep (se 1 (by rfl) ⟨8154674, by rfl⟩ : syracuseStep 10872899 = 16309349) B16309349
theorem B1042523 : Blo 694316 1042523 := bstep (se 1 (by rfl) ⟨781892, by rfl⟩ : syracuseStep 1042523 = 1563785) B1563785
theorem B1173595 : Blo 694316 1173595 := bstep (se 1 (by rfl) ⟨880196, by rfl⟩ : syracuseStep 1173595 = 1760393) B1760393
theorem B1042655 : Blo 694316 1042655 := bstep (se 1 (by rfl) ⟨781991, by rfl⟩ : syracuseStep 1042655 = 1563983) B1563983
theorem B2353427 : Blo 694316 2353427 := bstep (se 1 (by rfl) ⟨1765070, by rfl⟩ : syracuseStep 2353427 = 3530141) B3530141
theorem B1042751 : Blo 694316 1042751 := bstep (se 1 (by rfl) ⟨782063, by rfl⟩ : syracuseStep 1042751 = 1564127) B1564127
theorem B1173919 : Blo 694316 1173919 := bstep (se 1 (by rfl) ⟨880439, by rfl⟩ : syracuseStep 1173919 = 1760879) B1760879
theorem B1042985 : Blo 694316 1042985 := bstep (se 2 (by rfl) ⟨391119, by rfl⟩ : syracuseStep 1042985 = 782239) B782239
theorem B1043039 : Blo 694316 1043039 := bstep (se 1 (by rfl) ⟨782279, by rfl⟩ : syracuseStep 1043039 = 1564559) B1564559
theorem B1174439 : Blo 694316 1174439 := bstep (se 1 (by rfl) ⟨880829, by rfl⟩ : syracuseStep 1174439 = 1761659) B1761659
theorem B1764443 : Blo 694316 1764443 := bstep (se 1 (by rfl) ⟨1323332, by rfl⟩ : syracuseStep 1764443 = 2646665) B2646665
theorem B1043687 : Blo 694316 1043687 := bstep (se 1 (by rfl) ⟨782765, by rfl⟩ : syracuseStep 1043687 = 1565531) B1565531
theorem B1174783 : Blo 694316 1174783 := bstep (se 1 (by rfl) ⟨881087, by rfl⟩ : syracuseStep 1174783 = 1762175) B1762175
theorem B1043759 : Blo 694316 1043759 := bstep (se 1 (by rfl) ⟨782819, by rfl⟩ : syracuseStep 1043759 = 1565639) B1565639
theorem B3534191 : Blo 694316 3534191 := bstep (se 1 (by rfl) ⟨2650643, by rfl⟩ : syracuseStep 3534191 = 5301287) B5301287
theorem B1043903 : Blo 694316 1043903 := bstep (se 1 (by rfl) ⟨782927, by rfl⟩ : syracuseStep 1043903 = 1565855) B1565855
theorem B1044233 : Blo 694316 1044233 := bstep (se 2 (by rfl) ⟨391587, by rfl⟩ : syracuseStep 1044233 = 783175) B783175
theorem B8941823 : Blo 694316 8941823 := bstep (se 1 (by rfl) ⟨6706367, by rfl⟩ : syracuseStep 8941823 = 13412735) B13412735
theorem B782815 : Blo 694316 782815 := bstep (se 1 (by rfl) ⟨587111, by rfl⟩ : syracuseStep 782815 = 1174223) B1174223
theorem B1044959 : Blo 694316 1044959 := bstep (se 1 (by rfl) ⟨783719, by rfl⟩ : syracuseStep 1044959 = 1567439) B1567439
theorem B1044971 : Blo 694316 1044971 := bstep (se 1 (by rfl) ⟨783728, by rfl⟩ : syracuseStep 1044971 = 1567457) B1567457
theorem B2650751 : Blo 694316 2650751 := bstep (se 1 (by rfl) ⟨1988063, by rfl⟩ : syracuseStep 2650751 = 3976127) B3976127
theorem B2355965 : Blo 694316 2355965 := bstep (se 3 (by rfl) ⟨441743, by rfl⟩ : syracuseStep 2355965 = 883487) B883487
theorem B57308057 : Blo 694316 57308057 := bstep (se 2 (by rfl) ⟨21490521, by rfl⟩ : syracuseStep 57308057 = 42981043) B42981043
theorem B1045727 : Blo 694316 1045727 := bstep (se 1 (by rfl) ⟨784295, by rfl⟩ : syracuseStep 1045727 = 1568591) B1568591
theorem B1045787 : Blo 694316 1045787 := bstep (se 1 (by rfl) ⟨784340, by rfl⟩ : syracuseStep 1045787 = 1568681) B1568681
theorem B1046063 : Blo 694316 1046063 := bstep (se 1 (by rfl) ⟨784547, by rfl⟩ : syracuseStep 1046063 = 1569095) B1569095
theorem B1177193 : Blo 694316 1177193 := bstep (se 2 (by rfl) ⟨441447, by rfl⟩ : syracuseStep 1177193 = 882895) B882895
theorem B3962479 : Blo 694316 3962479 := bstep (se 1 (by rfl) ⟨2971859, by rfl⟩ : syracuseStep 3962479 = 5943719) B5943719
theorem B1767359 : Blo 694316 1767359 := bstep (se 1 (by rfl) ⟨1325519, by rfl⟩ : syracuseStep 1767359 = 2651039) B2651039
theorem B4454509 : Blo 694316 4454509 := bstep (se 3 (by rfl) ⟨835220, by rfl⟩ : syracuseStep 4454509 = 1670441) B1670441
theorem B1046855 : Blo 694316 1046855 := bstep (se 1 (by rfl) ⟨785141, by rfl⟩ : syracuseStep 1046855 = 1570283) B1570283
theorem B1046939 : Blo 694316 1046939 := bstep (se 1 (by rfl) ⟨785204, by rfl⟩ : syracuseStep 1046939 = 1570409) B1570409
theorem B4520873 : Blo 694316 4520873 := bstep (se 2 (by rfl) ⟨1695327, by rfl⟩ : syracuseStep 4520873 = 3390655) B3390655
theorem B8061727 : Blo 694316 8061727 := bstep (se 1 (by rfl) ⟨6046295, by rfl⟩ : syracuseStep 8061727 = 12092591) B12092591
theorem B2230831 : Blo 694316 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B1117127 : Blo 694316 1117127 := bstep (se 1 (by rfl) ⟨837845, by rfl⟩ : syracuseStep 1117127 = 1675691) B1675691
theorem B3805915 : Blo 694316 3805915 := bstep (se 1 (by rfl) ⟨2854436, by rfl⟩ : syracuseStep 3805915 = 5708873) B5708873
theorem B3052799 : Blo 694316 3052799 := bstep (se 1 (by rfl) ⟨2289599, by rfl⟩ : syracuseStep 3052799 = 4579199) B4579199
theorem B694439 : Blo 694316 694439 := bstep (se 1 (by rfl) ⟨520829, by rfl⟩ : syracuseStep 694439 = 1041659) B1041659
theorem B694523 : Blo 694316 694523 := bstep (se 1 (by rfl) ⟨520892, by rfl⟩ : syracuseStep 694523 = 1041785) B1041785
theorem B7248599 : Blo 694316 7248599 := bstep (se 1 (by rfl) ⟨5436449, by rfl⟩ : syracuseStep 7248599 = 10872899) B10872899
theorem B695015 : Blo 694316 695015 := bstep (se 1 (by rfl) ⟨521261, by rfl⟩ : syracuseStep 695015 = 1042523) B1042523
theorem B695103 : Blo 694316 695103 := bstep (se 1 (by rfl) ⟨521327, by rfl⟩ : syracuseStep 695103 = 1042655) B1042655
theorem B695167 : Blo 694316 695167 := bstep (se 1 (by rfl) ⟨521375, by rfl⟩ : syracuseStep 695167 = 1042751) B1042751
theorem B695323 : Blo 694316 695323 := bstep (se 1 (by rfl) ⟨521492, by rfl⟩ : syracuseStep 695323 = 1042985) B1042985
theorem B695359 : Blo 694316 695359 := bstep (se 1 (by rfl) ⟨521519, by rfl⟩ : syracuseStep 695359 = 1043039) B1043039
theorem B5283305 : Blo 694316 5283305 := bstep (se 2 (by rfl) ⟨1981239, by rfl⟩ : syracuseStep 5283305 = 3962479) B3962479
theorem B695791 : Blo 694316 695791 := bstep (se 1 (by rfl) ⟨521843, by rfl⟩ : syracuseStep 695791 = 1043687) B1043687
theorem B1318427 : Blo 694316 1318427 := bstep (se 1 (by rfl) ⟨988820, by rfl⟩ : syracuseStep 1318427 = 1977641) B1977641
theorem B695839 : Blo 694316 695839 := bstep (se 1 (by rfl) ⟨521879, by rfl⟩ : syracuseStep 695839 = 1043759) B1043759
theorem B695935 : Blo 694316 695935 := bstep (se 1 (by rfl) ⟨521951, by rfl⟩ : syracuseStep 695935 = 1043903) B1043903
theorem B696155 : Blo 694316 696155 := bstep (se 1 (by rfl) ⟨522116, by rfl⟩ : syracuseStep 696155 = 1044233) B1044233
theorem B5939345 : Blo 694316 5939345 := bstep (se 2 (by rfl) ⟨2227254, by rfl⟩ : syracuseStep 5939345 = 4454509) B4454509
theorem B16523459 : Blo 694316 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B696639 : Blo 694316 696639 := bstep (se 1 (by rfl) ⟨522479, by rfl⟩ : syracuseStep 696639 = 1044959) B1044959
theorem B696647 : Blo 694316 696647 := bstep (se 1 (by rfl) ⟨522485, by rfl⟩ : syracuseStep 696647 = 1044971) B1044971
theorem B992027 : Blo 694316 992027 := bstep (se 1 (by rfl) ⟨744020, by rfl⟩ : syracuseStep 992027 = 1488041) B1488041
theorem B697151 : Blo 694316 697151 := bstep (se 1 (by rfl) ⟨522863, by rfl⟩ : syracuseStep 697151 = 1045727) B1045727
theorem B1254215 : Blo 694316 1254215 := bstep (se 1 (by rfl) ⟨940661, by rfl⟩ : syracuseStep 1254215 = 1881323) B1881323
theorem B697191 : Blo 694316 697191 := bstep (se 1 (by rfl) ⟨522893, by rfl⟩ : syracuseStep 697191 = 1045787) B1045787
theorem B697375 : Blo 694316 697375 := bstep (se 1 (by rfl) ⟨523031, by rfl⟩ : syracuseStep 697375 = 1046063) B1046063
theorem B697903 : Blo 694316 697903 := bstep (se 1 (by rfl) ⟨523427, by rfl⟩ : syracuseStep 697903 = 1046855) B1046855
theorem B697959 : Blo 694316 697959 := bstep (se 1 (by rfl) ⟨523469, by rfl⟩ : syracuseStep 697959 = 1046939) B1046939
theorem B1879723 : Blo 694316 1879723 := bstep (se 1 (by rfl) ⟨1409792, by rfl⟩ : syracuseStep 1879723 = 2819585) B2819585
theorem B5287679 : Blo 694316 5287679 := bstep (se 1 (by rfl) ⟨3965759, by rfl⟩ : syracuseStep 5287679 = 7931519) B7931519
theorem B13577989 : Blo 694316 13577989 := bstep (se 4 (by rfl) ⟨1272936, by rfl⟩ : syracuseStep 13577989 = 2545873) B2545873
theorem B4009895 : Blo 694316 4009895 := bstep (se 1 (by rfl) ⟨3007421, by rfl⟩ : syracuseStep 4009895 = 6014843) B6014843
theorem B28554191 : Blo 694316 28554191 := bstep (se 1 (by rfl) ⟨21415643, by rfl⟩ : syracuseStep 28554191 = 42831287) B42831287
theorem B11449835 : Blo 694316 11449835 := bstep (se 1 (by rfl) ⟨8587376, by rfl⟩ : syracuseStep 11449835 = 17174753) B17174753
theorem B1325011 : Blo 694316 1325011 := bstep (se 1 (by rfl) ⟨993758, by rfl⟩ : syracuseStep 1325011 = 1987517) B1987517
theorem B6699601 : Blo 694316 6699601 := bstep (se 2 (by rfl) ⟨2512350, by rfl⟩ : syracuseStep 6699601 = 5024701) B5024701
theorem B2343329 : Blo 694316 2343329 := bstep (se 2 (by rfl) ⟨878748, by rfl⟩ : syracuseStep 2343329 = 1757497) B1757497
theorem B2343707 : Blo 694316 2343707 := bstep (se 1 (by rfl) ⟨1757780, by rfl⟩ : syracuseStep 2343707 = 3515561) B3515561
theorem B1983455 : Blo 694316 1983455 := bstep (se 1 (by rfl) ⟨1487591, by rfl⟩ : syracuseStep 1983455 = 2975183) B2975183
theorem B2343977 : Blo 694316 2343977 := bstep (se 2 (by rfl) ⟨878991, by rfl⟩ : syracuseStep 2343977 = 1757983) B1757983
theorem B5031391 : Blo 694316 5031391 := bstep (se 1 (by rfl) ⟨3773543, by rfl⟩ : syracuseStep 5031391 = 7547087) B7547087
theorem B68699821 : Blo 694316 68699821 := bstep (se 3 (by rfl) ⟨12881216, by rfl⟩ : syracuseStep 68699821 = 25762433) B25762433
theorem B123655987 : Blo 694316 123655987 := bstep (se 1 (by rfl) ⟨92741990, by rfl⟩ : syracuseStep 123655987 = 185483981) B185483981
theorem B2513273 : Blo 694316 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B26729513 : Blo 694316 26729513 := bstep (se 2 (by rfl) ⟨10023567, by rfl⟩ : syracuseStep 26729513 = 20047135) B20047135
theorem B1563731 : Blo 694316 1563731 := bstep (se 1 (by rfl) ⟨1172798, by rfl⟩ : syracuseStep 1563731 = 2345597) B2345597
theorem B25746731 : Blo 694316 25746731 := bstep (se 1 (by rfl) ⟨19310048, by rfl⟩ : syracuseStep 25746731 = 38620097) B38620097
theorem B114515693 : Blo 694316 114515693 := bstep (se 3 (by rfl) ⟨21471692, by rfl⟩ : syracuseStep 114515693 = 42943385) B42943385
theorem B1564793 : Blo 694316 1564793 := bstep (se 2 (by rfl) ⟨586797, by rfl⟩ : syracuseStep 1564793 = 1173595) B1173595
theorem B3956921 : Blo 694316 3956921 := bstep (se 2 (by rfl) ⟨1483845, by rfl⟩ : syracuseStep 3956921 = 2967691) B2967691
theorem B10150163 : Blo 694316 10150163 := bstep (se 1 (by rfl) ⟨7612622, by rfl⟩ : syracuseStep 10150163 = 15225245) B15225245
theorem B1565225 : Blo 694316 1565225 := bstep (se 2 (by rfl) ⟨586959, by rfl⟩ : syracuseStep 1565225 = 1173919) B1173919
theorem B2351807 : Blo 694316 2351807 := bstep (se 1 (by rfl) ⟨1763855, by rfl⟩ : syracuseStep 2351807 = 3527711) B3527711
theorem B1762681 : Blo 694316 1762681 := bstep (se 2 (by rfl) ⟨661005, by rfl⟩ : syracuseStep 1762681 = 1322011) B1322011
theorem B2647667 : Blo 694316 2647667 := bstep (se 1 (by rfl) ⟨1985750, by rfl⟩ : syracuseStep 2647667 = 3971501) B3971501
theorem B1566377 : Blo 694316 1566377 := bstep (se 2 (by rfl) ⟨587391, by rfl⟩ : syracuseStep 1566377 = 1174783) B1174783
theorem B1042175 : Blo 694316 1042175 := bstep (se 1 (by rfl) ⟨781631, by rfl⟩ : syracuseStep 1042175 = 1563263) B1563263
theorem B1566575 : Blo 694316 1566575 := bstep (se 1 (by rfl) ⟨1174931, by rfl⟩ : syracuseStep 1566575 = 2349863) B2349863
theorem B1042427 : Blo 694316 1042427 := bstep (se 1 (by rfl) ⟨781820, by rfl⟩ : syracuseStep 1042427 = 1563641) B1563641
theorem B1042559 : Blo 694316 1042559 := bstep (se 1 (by rfl) ⟨781919, by rfl⟩ : syracuseStep 1042559 = 1563839) B1563839
theorem B2648807 : Blo 694316 2648807 := bstep (se 1 (by rfl) ⟨1986605, by rfl⟩ : syracuseStep 2648807 = 3973211) B3973211
theorem B2353967 : Blo 694316 2353967 := bstep (se 1 (by rfl) ⟨1765475, by rfl⟩ : syracuseStep 2353967 = 3530951) B3530951
theorem B1567799 : Blo 694316 1567799 := bstep (se 1 (by rfl) ⟨1175849, by rfl⟩ : syracuseStep 1567799 = 2351699) B2351699
theorem B1043753 : Blo 694316 1043753 := bstep (se 2 (by rfl) ⟨391407, by rfl⟩ : syracuseStep 1043753 = 782815) B782815
theorem B1044335 : Blo 694316 1044335 := bstep (se 1 (by rfl) ⟨783251, by rfl⟩ : syracuseStep 1044335 = 1566503) B1566503
theorem B1765415 : Blo 694316 1765415 := bstep (se 1 (by rfl) ⟨1324061, by rfl⟩ : syracuseStep 1765415 = 2648123) B2648123
theorem B1568951 : Blo 694316 1568951 := bstep (se 1 (by rfl) ⟨1176713, by rfl⟩ : syracuseStep 1568951 = 2353427) B2353427
theorem B8450381 : Blo 694316 8450381 := bstep (se 3 (by rfl) ⟨1584446, by rfl⟩ : syracuseStep 8450381 = 3168893) B3168893
theorem B782959 : Blo 694316 782959 := bstep (se 1 (by rfl) ⟨587219, by rfl⟩ : syracuseStep 782959 = 1174439) B1174439
theorem B1176295 : Blo 694316 1176295 := bstep (se 1 (by rfl) ⟨882221, by rfl⟩ : syracuseStep 1176295 = 1764443) B1764443
theorem B5010173 : Blo 694316 5010173 := bstep (se 3 (by rfl) ⟨939407, by rfl⟩ : syracuseStep 5010173 = 1878815) B1878815
theorem B1504057 : Blo 694316 1504057 := bstep (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) B1128043
theorem B2356127 : Blo 694316 2356127 := bstep (se 1 (by rfl) ⟨1767095, by rfl⟩ : syracuseStep 2356127 = 3534191) B3534191
theorem B12055661 : Blo 694316 12055661 := bstep (se 3 (by rfl) ⟨2260436, by rfl⟩ : syracuseStep 12055661 = 4520873) B4520873
theorem B5961215 : Blo 694316 5961215 := bstep (se 1 (by rfl) ⟨4470911, by rfl⟩ : syracuseStep 5961215 = 8941823) B8941823
theorem B1767167 : Blo 694316 1767167 := bstep (se 1 (by rfl) ⟨1325375, by rfl⟩ : syracuseStep 1767167 = 2650751) B2650751
theorem B1570643 : Blo 694316 1570643 := bstep (se 1 (by rfl) ⟨1177982, by rfl⟩ : syracuseStep 1570643 = 2355965) B2355965
theorem B38205371 : Blo 694316 38205371 := bstep (se 1 (by rfl) ⟨28654028, by rfl⟩ : syracuseStep 38205371 = 57308057) B57308057
theorem B784795 : Blo 694316 784795 := bstep (se 1 (by rfl) ⟨588596, by rfl⟩ : syracuseStep 784795 = 1177193) B1177193
theorem B1178239 : Blo 694316 1178239 := bstep (se 1 (by rfl) ⟨883679, by rfl⟩ : syracuseStep 1178239 = 1767359) B1767359
theorem B9796241 : Blo 694316 9796241 := bstep (se 2 (by rfl) ⟨3673590, by rfl⟩ : syracuseStep 9796241 = 7347181) B7347181
theorem B2980745 : Blo 694316 2980745 := bstep (se 2 (by rfl) ⟨1117779, by rfl⟩ : syracuseStep 2980745 = 2235559) B2235559
theorem B7536361 : Blo 694316 7536361 := bstep (se 2 (by rfl) ⟨2826135, by rfl⟩ : syracuseStep 7536361 = 5652271) B5652271
theorem B4227041 : Blo 694316 4227041 := bstep (se 2 (by rfl) ⟨1585140, by rfl⟩ : syracuseStep 4227041 = 3170281) B3170281
theorem B10748969 : Blo 694316 10748969 := bstep (se 2 (by rfl) ⟨4030863, by rfl⟩ : syracuseStep 10748969 = 8061727) B8061727
theorem B3344573 : Blo 694316 3344573 := bstep (se 3 (by rfl) ⟨627107, by rfl⟩ : syracuseStep 3344573 = 1254215) B1254215
theorem B2035199 : Blo 694316 2035199 := bstep (se 1 (by rfl) ⟨1526399, by rfl⟩ : syracuseStep 2035199 = 3052799) B3052799
theorem B26808245 : Blo 694316 26808245 := bstep (se 5 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 26808245 = 2513273) B2513273
theorem B11015639 : Blo 694316 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B2005409 : Blo 694316 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B694783 : Blo 694316 694783 := bstep (se 1 (by rfl) ⟨521087, by rfl⟩ : syracuseStep 694783 = 1042175) B1042175
theorem B694951 : Blo 694316 694951 := bstep (se 1 (by rfl) ⟨521213, by rfl⟩ : syracuseStep 694951 = 1042427) B1042427
theorem B695039 : Blo 694316 695039 := bstep (se 1 (by rfl) ⟨521279, by rfl⟩ : syracuseStep 695039 = 1042559) B1042559
theorem B695835 : Blo 694316 695835 := bstep (se 1 (by rfl) ⟨521876, by rfl⟩ : syracuseStep 695835 = 1043753) B1043753
theorem B696223 : Blo 694316 696223 := bstep (se 1 (by rfl) ⟨522167, by rfl⟩ : syracuseStep 696223 = 1044335) B1044335
theorem B8037107 : Blo 694316 8037107 := bstep (se 1 (by rfl) ⟨6027830, by rfl⟩ : syracuseStep 8037107 = 12055661) B12055661
theorem B3974143 : Blo 694316 3974143 := bstep (se 1 (by rfl) ⟨2980607, by rfl⟩ : syracuseStep 3974143 = 5961215) B5961215
theorem B25470247 : Blo 694316 25470247 := bstep (se 1 (by rfl) ⟨19102685, by rfl⟩ : syracuseStep 25470247 = 38205371) B38205371
theorem B6530827 : Blo 694316 6530827 := bstep (se 1 (by rfl) ⟨4898120, by rfl⟩ : syracuseStep 6530827 = 9796241) B9796241
theorem B1322303 : Blo 694316 1322303 := bstep (se 1 (by rfl) ⟨991727, by rfl⟩ : syracuseStep 1322303 = 1983455) B1983455
theorem B91599761 : Blo 694316 91599761 := bstep (se 2 (by rfl) ⟨34349910, by rfl⟩ : syracuseStep 91599761 = 68699821) B68699821
theorem B4832399 : Blo 694316 4832399 := bstep (se 1 (by rfl) ⟨3624299, by rfl⟩ : syracuseStep 4832399 = 7248599) B7248599
theorem B2506297 : Blo 694316 2506297 := bstep (se 2 (by rfl) ⟨939861, by rfl⟩ : syracuseStep 2506297 = 1879723) B1879723
theorem B3522203 : Blo 694316 3522203 := bstep (se 1 (by rfl) ⟨2641652, by rfl⟩ : syracuseStep 3522203 = 5283305) B5283305
theorem B18103985 : Blo 694316 18103985 := bstep (se 2 (by rfl) ⟨6788994, by rfl⟩ : syracuseStep 18103985 = 13577989) B13577989
theorem B2637947 : Blo 694316 2637947 := bstep (se 1 (by rfl) ⟨1978460, by rfl⟩ : syracuseStep 2637947 = 3956921) B3956921
theorem B6766775 : Blo 694316 6766775 := bstep (se 1 (by rfl) ⟨5075081, by rfl⟩ : syracuseStep 6766775 = 10150163) B10150163
theorem B164874649 : Blo 694316 164874649 := bstep (se 2 (by rfl) ⟨61827993, by rfl⟩ : syracuseStep 164874649 = 123655987) B123655987
theorem B3525119 : Blo 694316 3525119 := bstep (se 1 (by rfl) ⟨2643839, by rfl⟩ : syracuseStep 3525119 = 5287679) B5287679
theorem B2673263 : Blo 694316 2673263 := bstep (se 1 (by rfl) ⟨2004947, by rfl⟩ : syracuseStep 2673263 = 4009895) B4009895
theorem B8932801 : Blo 694316 8932801 := bstep (se 2 (by rfl) ⟨3349800, by rfl⟩ : syracuseStep 8932801 = 6699601) B6699601
theorem B1987163 : Blo 694316 1987163 := bstep (se 1 (by rfl) ⟨1490372, by rfl⟩ : syracuseStep 1987163 = 2980745) B2980745
theorem B10048481 : Blo 694316 10048481 := bstep (se 2 (by rfl) ⟨3768180, by rfl⟩ : syracuseStep 10048481 = 7536361) B7536361
theorem B1562219 : Blo 694316 1562219 := bstep (se 1 (by rfl) ⟨1171664, by rfl⟩ : syracuseStep 1562219 = 2343329) B2343329
theorem B1562471 : Blo 694316 1562471 := bstep (se 1 (by rfl) ⟨1171853, by rfl⟩ : syracuseStep 1562471 = 2343707) B2343707
theorem B1562651 : Blo 694316 1562651 := bstep (se 1 (by rfl) ⟨1171988, by rfl⟩ : syracuseStep 1562651 = 2343977) B2343977
theorem B2350241 : Blo 694316 2350241 := bstep (se 2 (by rfl) ⟨881340, by rfl⟩ : syracuseStep 2350241 = 1762681) B1762681
theorem B6708521 : Blo 694316 6708521 := bstep (se 2 (by rfl) ⟨2515695, by rfl⟩ : syracuseStep 6708521 = 5031391) B5031391
theorem B744751 : Blo 694316 744751 := bstep (se 1 (by rfl) ⟨558563, by rfl⟩ : syracuseStep 744751 = 1117127) B1117127
theorem B2645405 : Blo 694316 2645405 := bstep (se 3 (by rfl) ⟨496013, by rfl⟩ : syracuseStep 2645405 = 992027) B992027
theorem B2974441 : Blo 694316 2974441 := bstep (se 2 (by rfl) ⟨1115415, by rfl⟩ : syracuseStep 2974441 = 2230831) B2230831
theorem B17819675 : Blo 694316 17819675 := bstep (se 1 (by rfl) ⟨13364756, by rfl⟩ : syracuseStep 17819675 = 26729513) B26729513
theorem B1042487 : Blo 694316 1042487 := bstep (se 1 (by rfl) ⟨781865, by rfl⟩ : syracuseStep 1042487 = 1563731) B1563731
theorem B17164487 : Blo 694316 17164487 := bstep (se 1 (by rfl) ⟨12873365, by rfl⟩ : syracuseStep 17164487 = 25746731) B25746731
theorem B878951 : Blo 694316 878951 := bstep (se 1 (by rfl) ⟨659213, by rfl⟩ : syracuseStep 878951 = 1318427) B1318427
theorem B76343795 : Blo 694316 76343795 := bstep (se 1 (by rfl) ⟨57257846, by rfl⟩ : syracuseStep 76343795 = 114515693) B114515693
theorem B1043195 : Blo 694316 1043195 := bstep (se 1 (by rfl) ⟨782396, by rfl⟩ : syracuseStep 1043195 = 1564793) B1564793
theorem B3959563 : Blo 694316 3959563 := bstep (se 1 (by rfl) ⟨2969672, by rfl⟩ : syracuseStep 3959563 = 5939345) B5939345
theorem B1043483 : Blo 694316 1043483 := bstep (se 1 (by rfl) ⟨782612, by rfl⟩ : syracuseStep 1043483 = 1565225) B1565225
theorem B1567871 : Blo 694316 1567871 := bstep (se 1 (by rfl) ⟨1175903, by rfl⟩ : syracuseStep 1567871 = 2351807) B2351807
theorem B1043945 : Blo 694316 1043945 := bstep (se 2 (by rfl) ⟨391479, by rfl⟩ : syracuseStep 1043945 = 782959) B782959
theorem B5074553 : Blo 694316 5074553 := bstep (se 2 (by rfl) ⟨1902957, by rfl⟩ : syracuseStep 5074553 = 3805915) B3805915
theorem B1568393 : Blo 694316 1568393 := bstep (se 2 (by rfl) ⟨588147, by rfl⟩ : syracuseStep 1568393 = 1176295) B1176295
theorem B1765111 : Blo 694316 1765111 := bstep (se 1 (by rfl) ⟨1323833, by rfl⟩ : syracuseStep 1765111 = 2647667) B2647667
theorem B1044251 : Blo 694316 1044251 := bstep (se 1 (by rfl) ⟨783188, by rfl⟩ : syracuseStep 1044251 = 1566377) B1566377
theorem B1044383 : Blo 694316 1044383 := bstep (se 1 (by rfl) ⟨783287, by rfl⟩ : syracuseStep 1044383 = 1566575) B1566575
theorem B1765871 : Blo 694316 1765871 := bstep (se 1 (by rfl) ⟨1324403, by rfl⟩ : syracuseStep 1765871 = 2648807) B2648807
theorem B1569311 : Blo 694316 1569311 := bstep (se 1 (by rfl) ⟨1176983, by rfl⟩ : syracuseStep 1569311 = 2353967) B2353967
theorem B1045199 : Blo 694316 1045199 := bstep (se 1 (by rfl) ⟨783899, by rfl⟩ : syracuseStep 1045199 = 1567799) B1567799
theorem B1766681 : Blo 694316 1766681 := bstep (se 2 (by rfl) ⟨662505, by rfl⟩ : syracuseStep 1766681 = 1325011) B1325011
theorem B1176943 : Blo 694316 1176943 := bstep (se 1 (by rfl) ⟨882707, by rfl⟩ : syracuseStep 1176943 = 1765415) B1765415
theorem B1045967 : Blo 694316 1045967 := bstep (se 1 (by rfl) ⟨784475, by rfl⟩ : syracuseStep 1045967 = 1568951) B1568951
theorem B5633587 : Blo 694316 5633587 := bstep (se 1 (by rfl) ⟨4225190, by rfl⟩ : syracuseStep 5633587 = 8450381) B8450381
theorem B3340115 : Blo 694316 3340115 := bstep (se 1 (by rfl) ⟨2505086, by rfl⟩ : syracuseStep 3340115 = 5010173) B5010173
theorem B1046393 : Blo 694316 1046393 := bstep (se 2 (by rfl) ⟨392397, by rfl⟩ : syracuseStep 1046393 = 784795) B784795
theorem B1570751 : Blo 694316 1570751 := bstep (se 1 (by rfl) ⟨1178063, by rfl⟩ : syracuseStep 1570751 = 2356127) B2356127
theorem B19036127 : Blo 694316 19036127 := bstep (se 1 (by rfl) ⟨14277095, by rfl⟩ : syracuseStep 19036127 = 28554191) B28554191
theorem B1570985 : Blo 694316 1570985 := bstep (se 2 (by rfl) ⟨589119, by rfl⟩ : syracuseStep 1570985 = 1178239) B1178239
theorem B7633223 : Blo 694316 7633223 := bstep (se 1 (by rfl) ⟨5724917, by rfl⟩ : syracuseStep 7633223 = 11449835) B11449835
theorem B1178111 : Blo 694316 1178111 := bstep (se 1 (by rfl) ⟨883583, by rfl⟩ : syracuseStep 1178111 = 1767167) B1767167
theorem B1047095 : Blo 694316 1047095 := bstep (se 1 (by rfl) ⟨785321, by rfl⟩ : syracuseStep 1047095 = 1570643) B1570643
theorem B2818027 : Blo 694316 2818027 := bstep (se 1 (by rfl) ⟨2113520, by rfl⟩ : syracuseStep 2818027 = 4227041) B4227041
theorem B3965921 : Blo 694316 3965921 := bstep (se 2 (by rfl) ⟨1487220, by rfl⟩ : syracuseStep 3965921 = 2974441) B2974441
theorem B2229715 : Blo 694316 2229715 := bstep (se 1 (by rfl) ⟨1672286, by rfl⟩ : syracuseStep 2229715 = 3344573) B3344573
theorem B7343759 : Blo 694316 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B5279417 : Blo 694316 5279417 := bstep (se 2 (by rfl) ⟨1979781, by rfl⟩ : syracuseStep 5279417 = 3959563) B3959563
theorem B5347757 : Blo 694316 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B694991 : Blo 694316 694991 := bstep (se 1 (by rfl) ⟨521243, by rfl⟩ : syracuseStep 694991 = 1042487) B1042487
theorem B50895863 : Blo 694316 50895863 := bstep (se 1 (by rfl) ⟨38171897, by rfl⟩ : syracuseStep 50895863 = 76343795) B76343795
theorem B695463 : Blo 694316 695463 := bstep (se 1 (by rfl) ⟨521597, by rfl⟩ : syracuseStep 695463 = 1043195) B1043195
theorem B695655 : Blo 694316 695655 := bstep (se 1 (by rfl) ⟨521741, by rfl⟩ : syracuseStep 695655 = 1043483) B1043483
theorem B7511449 : Blo 694316 7511449 := bstep (se 2 (by rfl) ⟨2816793, by rfl⟩ : syracuseStep 7511449 = 5633587) B5633587
theorem B695963 : Blo 694316 695963 := bstep (se 1 (by rfl) ⟨521972, by rfl⟩ : syracuseStep 695963 = 1043945) B1043945
theorem B3383035 : Blo 694316 3383035 := bstep (se 1 (by rfl) ⟨2537276, by rfl⟩ : syracuseStep 3383035 = 5074553) B5074553
theorem B696167 : Blo 694316 696167 := bstep (se 1 (by rfl) ⟨522125, by rfl⟩ : syracuseStep 696167 = 1044251) B1044251
theorem B696255 : Blo 694316 696255 := bstep (se 1 (by rfl) ⟨522191, by rfl⟩ : syracuseStep 696255 = 1044383) B1044383
theorem B12886397 : Blo 694316 12886397 := bstep (se 3 (by rfl) ⟨2416199, by rfl⟩ : syracuseStep 12886397 = 4832399) B4832399
theorem B696799 : Blo 694316 696799 := bstep (se 1 (by rfl) ⟨522599, by rfl⟩ : syracuseStep 696799 = 1045199) B1045199
theorem B697311 : Blo 694316 697311 := bstep (se 1 (by rfl) ⟨522983, by rfl⟩ : syracuseStep 697311 = 1045967) B1045967
theorem B697595 : Blo 694316 697595 := bstep (se 1 (by rfl) ⟨523196, by rfl⟩ : syracuseStep 697595 = 1046393) B1046393
theorem B12690751 : Blo 694316 12690751 := bstep (se 1 (by rfl) ⟨9518063, by rfl⟩ : syracuseStep 12690751 = 19036127) B19036127
theorem B5088815 : Blo 694316 5088815 := bstep (se 1 (by rfl) ⟨3816611, by rfl⟩ : syracuseStep 5088815 = 7633223) B7633223
theorem B698063 : Blo 694316 698063 := bstep (se 1 (by rfl) ⟨523547, by rfl⟩ : syracuseStep 698063 = 1047095) B1047095
theorem B993001 : Blo 694316 993001 := bstep (se 2 (by rfl) ⟨372375, by rfl⟩ : syracuseStep 993001 = 744751) B744751
theorem B12069323 : Blo 694316 12069323 := bstep (se 1 (by rfl) ⟨9051992, by rfl⟩ : syracuseStep 12069323 = 18103985) B18103985
theorem B33960329 : Blo 694316 33960329 := bstep (se 2 (by rfl) ⟨12735123, by rfl⟩ : syracuseStep 33960329 = 25470247) B25470247
theorem B1782175 : Blo 694316 1782175 := bstep (se 1 (by rfl) ⟨1336631, by rfl⟩ : syracuseStep 1782175 = 2673263) B2673263
theorem B1356799 : Blo 694316 1356799 := bstep (se 1 (by rfl) ⟨1017599, by rfl⟩ : syracuseStep 1356799 = 2035199) B2035199
theorem B17872163 : Blo 694316 17872163 := bstep (se 1 (by rfl) ⟨13404122, by rfl⟩ : syracuseStep 17872163 = 26808245) B26808245
theorem B1324775 : Blo 694316 1324775 := bstep (se 1 (by rfl) ⟨993581, by rfl⟩ : syracuseStep 1324775 = 1987163) B1987163
theorem B6698987 : Blo 694316 6698987 := bstep (se 1 (by rfl) ⟨5024240, by rfl⟩ : syracuseStep 6698987 = 10048481) B10048481
theorem B11910401 : Blo 694316 11910401 := bstep (se 2 (by rfl) ⟨4466400, by rfl⟩ : syracuseStep 11910401 = 8932801) B8932801
theorem B4472347 : Blo 694316 4472347 := bstep (se 1 (by rfl) ⟨3354260, by rfl⟩ : syracuseStep 4472347 = 6708521) B6708521
theorem B5358071 : Blo 694316 5358071 := bstep (se 1 (by rfl) ⟨4018553, by rfl⟩ : syracuseStep 5358071 = 8037107) B8037107
theorem B2343869 : Blo 694316 2343869 := bstep (se 3 (by rfl) ⟨439475, by rfl⟩ : syracuseStep 2343869 = 878951) B878951
theorem B11879783 : Blo 694316 11879783 := bstep (se 1 (by rfl) ⟨8909837, by rfl⟩ : syracuseStep 11879783 = 17819675) B17819675
theorem B61066507 : Blo 694316 61066507 := bstep (se 1 (by rfl) ⟨45799880, by rfl⟩ : syracuseStep 61066507 = 91599761) B91599761
theorem B3526141 : Blo 694316 3526141 := bstep (se 3 (by rfl) ⟨661151, by rfl⟩ : syracuseStep 3526141 = 1322303) B1322303
theorem B2348135 : Blo 694316 2348135 := bstep (se 1 (by rfl) ⟨1761101, by rfl⟩ : syracuseStep 2348135 = 3522203) B3522203
theorem B3757369 : Blo 694316 3757369 := bstep (se 2 (by rfl) ⟨1409013, by rfl⟩ : syracuseStep 3757369 = 2818027) B2818027
theorem B1758631 : Blo 694316 1758631 := bstep (se 1 (by rfl) ⟨1318973, by rfl⟩ : syracuseStep 1758631 = 2637947) B2637947
theorem B4511183 : Blo 694316 4511183 := bstep (se 1 (by rfl) ⟨3383387, by rfl⟩ : syracuseStep 4511183 = 6766775) B6766775
theorem B7165979 : Blo 694316 7165979 := bstep (se 1 (by rfl) ⟨5374484, by rfl⟩ : syracuseStep 7165979 = 10748969) B10748969
theorem B5298857 : Blo 694316 5298857 := bstep (se 2 (by rfl) ⟨1987071, by rfl⟩ : syracuseStep 5298857 = 3974143) B3974143
theorem B2350079 : Blo 694316 2350079 := bstep (se 1 (by rfl) ⟨1762559, by rfl⟩ : syracuseStep 2350079 = 3525119) B3525119
theorem B8707769 : Blo 694316 8707769 := bstep (se 2 (by rfl) ⟨3265413, by rfl⟩ : syracuseStep 8707769 = 6530827) B6530827
theorem B219832865 : Blo 694316 219832865 := bstep (se 2 (by rfl) ⟨82437324, by rfl⟩ : syracuseStep 219832865 = 164874649) B164874649
theorem B1041479 : Blo 694316 1041479 := bstep (se 1 (by rfl) ⟨781109, by rfl⟩ : syracuseStep 1041479 = 1562219) B1562219
theorem B1041647 : Blo 694316 1041647 := bstep (se 1 (by rfl) ⟨781235, by rfl⟩ : syracuseStep 1041647 = 1562471) B1562471
theorem B1041767 : Blo 694316 1041767 := bstep (se 1 (by rfl) ⟨781325, by rfl⟩ : syracuseStep 1041767 = 1562651) B1562651
theorem B1566827 : Blo 694316 1566827 := bstep (se 1 (by rfl) ⟨1175120, by rfl⟩ : syracuseStep 1566827 = 2350241) B2350241
theorem B1763603 : Blo 694316 1763603 := bstep (se 1 (by rfl) ⟨1322702, by rfl⟩ : syracuseStep 1763603 = 2645405) B2645405
theorem B2353481 : Blo 694316 2353481 := bstep (se 2 (by rfl) ⟨882555, by rfl⟩ : syracuseStep 2353481 = 1765111) B1765111
theorem B45771965 : Blo 694316 45771965 := bstep (se 3 (by rfl) ⟨8582243, by rfl⟩ : syracuseStep 45771965 = 17164487) B17164487
theorem B1569257 : Blo 694316 1569257 := bstep (se 2 (by rfl) ⟨588471, by rfl⟩ : syracuseStep 1569257 = 1176943) B1176943
theorem B1045247 : Blo 694316 1045247 := bstep (se 1 (by rfl) ⟨783935, by rfl⟩ : syracuseStep 1045247 = 1567871) B1567871
theorem B1045595 : Blo 694316 1045595 := bstep (se 1 (by rfl) ⟨784196, by rfl⟩ : syracuseStep 1045595 = 1568393) B1568393
theorem B1177247 : Blo 694316 1177247 := bstep (se 1 (by rfl) ⟨882935, by rfl⟩ : syracuseStep 1177247 = 1765871) B1765871
theorem B1046207 : Blo 694316 1046207 := bstep (se 1 (by rfl) ⟨784655, by rfl⟩ : syracuseStep 1046207 = 1569311) B1569311
theorem B1177787 : Blo 694316 1177787 := bstep (se 1 (by rfl) ⟨883340, by rfl⟩ : syracuseStep 1177787 = 1766681) B1766681
theorem B2226743 : Blo 694316 2226743 := bstep (se 1 (by rfl) ⟨1670057, by rfl⟩ : syracuseStep 2226743 = 3340115) B3340115
theorem B1047167 : Blo 694316 1047167 := bstep (se 1 (by rfl) ⟨785375, by rfl⟩ : syracuseStep 1047167 = 1570751) B1570751
theorem B1047323 : Blo 694316 1047323 := bstep (se 1 (by rfl) ⟨785492, by rfl⟩ : syracuseStep 1047323 = 1570985) B1570985
theorem B785407 : Blo 694316 785407 := bstep (se 1 (by rfl) ⟨589055, by rfl⟩ : syracuseStep 785407 = 1178111) B1178111
theorem B3341729 : Blo 694316 3341729 := bstep (se 2 (by rfl) ⟨1253148, by rfl⟩ : syracuseStep 3341729 = 2506297) B2506297
theorem B3572047 : Blo 694316 3572047 := bstep (se 1 (by rfl) ⟨2679035, by rfl⟩ : syracuseStep 3572047 = 5358071) B5358071
theorem B5805179 : Blo 694316 5805179 := bstep (se 1 (by rfl) ⟨4353884, by rfl⟩ : syracuseStep 5805179 = 8707769) B8707769
theorem B8590931 : Blo 694316 8590931 := bstep (se 1 (by rfl) ⟨6443198, by rfl⟩ : syracuseStep 8590931 = 12886397) B12886397
theorem B694319 : Blo 694316 694319 := bstep (se 1 (by rfl) ⟨520739, by rfl⟩ : syracuseStep 694319 = 1041479) B1041479
theorem B694431 : Blo 694316 694431 := bstep (se 1 (by rfl) ⟨520823, by rfl⟩ : syracuseStep 694431 = 1041647) B1041647
theorem B694511 : Blo 694316 694511 := bstep (se 1 (by rfl) ⟨520883, by rfl⟩ : syracuseStep 694511 = 1041767) B1041767
theorem B1809065 : Blo 694316 1809065 := bstep (se 2 (by rfl) ⟨678399, by rfl⟩ : syracuseStep 1809065 = 1356799) B1356799
theorem B30514643 : Blo 694316 30514643 := bstep (se 1 (by rfl) ⟨22885982, by rfl⟩ : syracuseStep 30514643 = 45771965) B45771965
theorem B696831 : Blo 694316 696831 := bstep (se 1 (by rfl) ⟨522623, by rfl⟩ : syracuseStep 696831 = 1045247) B1045247
theorem B697063 : Blo 694316 697063 := bstep (se 1 (by rfl) ⟨522797, by rfl⟩ : syracuseStep 697063 = 1045595) B1045595
theorem B697471 : Blo 694316 697471 := bstep (se 1 (by rfl) ⟨523103, by rfl⟩ : syracuseStep 697471 = 1046207) B1046207
theorem B4465991 : Blo 694316 4465991 := bstep (se 1 (by rfl) ⟨3349493, by rfl⟩ : syracuseStep 4465991 = 6698987) B6698987
theorem B1484495 : Blo 694316 1484495 := bstep (se 1 (by rfl) ⟨1113371, by rfl⟩ : syracuseStep 1484495 = 2226743) B2226743
theorem B698111 : Blo 694316 698111 := bstep (se 1 (by rfl) ⟨523583, by rfl⟩ : syracuseStep 698111 = 1047167) B1047167
theorem B698215 : Blo 694316 698215 := bstep (se 1 (by rfl) ⟨523661, by rfl⟩ : syracuseStep 698215 = 1047323) B1047323
theorem B7940267 : Blo 694316 7940267 := bstep (se 1 (by rfl) ⟨5955200, by rfl⟩ : syracuseStep 7940267 = 11910401) B11910401
theorem B16921001 : Blo 694316 16921001 := bstep (se 2 (by rfl) ⟨6345375, by rfl⟩ : syracuseStep 16921001 = 12690751) B12690751
theorem B1324001 : Blo 694316 1324001 := bstep (se 2 (by rfl) ⟨496500, by rfl⟩ : syracuseStep 1324001 = 993001) B993001
theorem B4895839 : Blo 694316 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B3519611 : Blo 694316 3519611 := bstep (se 1 (by rfl) ⟨2639708, by rfl⟩ : syracuseStep 3519611 = 5279417) B5279417
theorem B33930575 : Blo 694316 33930575 := bstep (se 1 (by rfl) ⟨25447931, by rfl⟩ : syracuseStep 33930575 = 50895863) B50895863
theorem B4701521 : Blo 694316 4701521 := bstep (se 2 (by rfl) ⟨1763070, by rfl⟩ : syracuseStep 4701521 = 3526141) B3526141
theorem B48119285 : Blo 694316 48119285 := bstep (se 5 (by rfl) ⟨2255591, by rfl⟩ : syracuseStep 48119285 = 4511183) B4511183
theorem B146555243 : Blo 694316 146555243 := bstep (se 1 (by rfl) ⟨109916432, by rfl⟩ : syracuseStep 146555243 = 219832865) B219832865
theorem B2376233 : Blo 694316 2376233 := bstep (se 2 (by rfl) ⟨891087, by rfl⟩ : syracuseStep 2376233 = 1782175) B1782175
theorem B3392543 : Blo 694316 3392543 := bstep (se 1 (by rfl) ⟨2544407, by rfl⟩ : syracuseStep 3392543 = 5088815) B5088815
theorem B8046215 : Blo 694316 8046215 := bstep (se 1 (by rfl) ⟨6034661, by rfl⟩ : syracuseStep 8046215 = 12069323) B12069323
theorem B2344841 : Blo 694316 2344841 := bstep (se 2 (by rfl) ⟨879315, by rfl⟩ : syracuseStep 2344841 = 1758631) B1758631
theorem B11914775 : Blo 694316 11914775 := bstep (se 1 (by rfl) ⟨8936081, by rfl⟩ : syracuseStep 11914775 = 17872163) B17872163
theorem B18042853 : Blo 694316 18042853 := bstep (se 4 (by rfl) ⟨1691517, by rfl⟩ : syracuseStep 18042853 = 3383035) B3383035
theorem B10015265 : Blo 694316 10015265 := bstep (se 2 (by rfl) ⟨3755724, by rfl⟩ : syracuseStep 10015265 = 7511449) B7511449
theorem B1562579 : Blo 694316 1562579 := bstep (se 1 (by rfl) ⟨1171934, by rfl⟩ : syracuseStep 1562579 = 2343869) B2343869
theorem B2643947 : Blo 694316 2643947 := bstep (se 1 (by rfl) ⟨1982960, by rfl⟩ : syracuseStep 2643947 = 3965921) B3965921
theorem B7919855 : Blo 694316 7919855 := bstep (se 1 (by rfl) ⟨5939891, by rfl⟩ : syracuseStep 7919855 = 11879783) B11879783
theorem B2972953 : Blo 694316 2972953 := bstep (se 2 (by rfl) ⟨1114857, by rfl⟩ : syracuseStep 2972953 = 2229715) B2229715
theorem B1565423 : Blo 694316 1565423 := bstep (se 1 (by rfl) ⟨1174067, by rfl⟩ : syracuseStep 1565423 = 2348135) B2348135
theorem B4777319 : Blo 694316 4777319 := bstep (se 1 (by rfl) ⟨3582989, by rfl⟩ : syracuseStep 4777319 = 7165979) B7165979
theorem B3565171 : Blo 694316 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B81422009 : Blo 694316 81422009 := bstep (se 2 (by rfl) ⟨30533253, by rfl⟩ : syracuseStep 81422009 = 61066507) B61066507
theorem B3532571 : Blo 694316 3532571 := bstep (se 1 (by rfl) ⟨2649428, by rfl⟩ : syracuseStep 3532571 = 5298857) B5298857
theorem B3532733 : Blo 694316 3532733 := bstep (se 3 (by rfl) ⟨662387, by rfl⟩ : syracuseStep 3532733 = 1324775) B1324775
theorem B1566719 : Blo 694316 1566719 := bstep (se 1 (by rfl) ⟨1175039, by rfl⟩ : syracuseStep 1566719 = 2350079) B2350079
theorem B1044551 : Blo 694316 1044551 := bstep (se 1 (by rfl) ⟨783413, by rfl⟩ : syracuseStep 1044551 = 1566827) B1566827
theorem B1175735 : Blo 694316 1175735 := bstep (se 1 (by rfl) ⟨881801, by rfl⟩ : syracuseStep 1175735 = 1763603) B1763603
theorem B1568987 : Blo 694316 1568987 := bstep (se 1 (by rfl) ⟨1176740, by rfl⟩ : syracuseStep 1568987 = 2353481) B2353481
theorem B5009825 : Blo 694316 5009825 := bstep (se 2 (by rfl) ⟨1878684, by rfl⟩ : syracuseStep 5009825 = 3757369) B3757369
theorem B22640219 : Blo 694316 22640219 := bstep (se 1 (by rfl) ⟨16980164, by rfl⟩ : syracuseStep 22640219 = 33960329) B33960329
theorem B1046171 : Blo 694316 1046171 := bstep (se 1 (by rfl) ⟨784628, by rfl⟩ : syracuseStep 1046171 = 1569257) B1569257
theorem B784831 : Blo 694316 784831 := bstep (se 1 (by rfl) ⟨588623, by rfl⟩ : syracuseStep 784831 = 1177247) B1177247
theorem B1047209 : Blo 694316 1047209 := bstep (se 2 (by rfl) ⟨392703, by rfl⟩ : syracuseStep 1047209 = 785407) B785407
theorem B785191 : Blo 694316 785191 := bstep (se 1 (by rfl) ⟨588893, by rfl⟩ : syracuseStep 785191 = 1177787) B1177787
theorem B5963129 : Blo 694316 5963129 := bstep (se 2 (by rfl) ⟨2236173, by rfl⟩ : syracuseStep 5963129 = 4472347) B4472347
theorem B2227819 : Blo 694316 2227819 := bstep (se 1 (by rfl) ⟨1670864, by rfl⟩ : syracuseStep 2227819 = 3341729) B3341729
theorem B4753561 : Blo 694316 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B9046781 : Blo 694316 9046781 := bstep (se 3 (by rfl) ⟨1696271, by rfl⟩ : syracuseStep 9046781 = 3392543) B3392543
theorem B3870119 : Blo 694316 3870119 := bstep (se 1 (by rfl) ⟨2902589, by rfl⟩ : syracuseStep 3870119 = 5805179) B5805179
theorem B5279903 : Blo 694316 5279903 := bstep (se 1 (by rfl) ⟨3959927, by rfl⟩ : syracuseStep 5279903 = 7919855) B7919855
theorem B24057137 : Blo 694316 24057137 := bstep (se 2 (by rfl) ⟨9021426, by rfl⟩ : syracuseStep 24057137 = 18042853) B18042853
theorem B989663 : Blo 694316 989663 := bstep (se 1 (by rfl) ⟨742247, by rfl⟩ : syracuseStep 989663 = 1484495) B1484495
theorem B6527785 : Blo 694316 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B4824173 : Blo 694316 4824173 := bstep (se 3 (by rfl) ⟨904532, by rfl⟩ : syracuseStep 4824173 = 1809065) B1809065
theorem B696367 : Blo 694316 696367 := bstep (se 1 (by rfl) ⟨522275, by rfl⟩ : syracuseStep 696367 = 1044551) B1044551
theorem B11280667 : Blo 694316 11280667 := bstep (se 1 (by rfl) ⟨8460500, by rfl⟩ : syracuseStep 11280667 = 16921001) B16921001
theorem B697447 : Blo 694316 697447 := bstep (se 1 (by rfl) ⟨523085, by rfl⟩ : syracuseStep 697447 = 1046171) B1046171
theorem B698139 : Blo 694316 698139 := bstep (se 1 (by rfl) ⟨523604, by rfl⟩ : syracuseStep 698139 = 1047209) B1047209
theorem B22620383 : Blo 694316 22620383 := bstep (se 1 (by rfl) ⟨16965287, by rfl⟩ : syracuseStep 22620383 = 33930575) B33930575
theorem B3975419 : Blo 694316 3975419 := bstep (se 1 (by rfl) ⟨2981564, by rfl⟩ : syracuseStep 3975419 = 5963129) B5963129
theorem B1584155 : Blo 694316 1584155 := bstep (se 1 (by rfl) ⟨1188116, by rfl⟩ : syracuseStep 1584155 = 2376233) B2376233
theorem B4762729 : Blo 694316 4762729 := bstep (se 2 (by rfl) ⟨1786023, by rfl⟩ : syracuseStep 4762729 = 3572047) B3572047
theorem B7943183 : Blo 694316 7943183 := bstep (se 1 (by rfl) ⟨5957387, by rfl⟩ : syracuseStep 7943183 = 11914775) B11914775
theorem B54281339 : Blo 694316 54281339 := bstep (se 1 (by rfl) ⟨40711004, by rfl⟩ : syracuseStep 54281339 = 81422009) B81422009
theorem B5293511 : Blo 694316 5293511 := bstep (se 1 (by rfl) ⟨3970133, by rfl⟩ : syracuseStep 5293511 = 7940267) B7940267
theorem B2346407 : Blo 694316 2346407 := bstep (se 1 (by rfl) ⟨1759805, by rfl⟩ : syracuseStep 2346407 = 3519611) B3519611
theorem B12537389 : Blo 694316 12537389 := bstep (se 3 (by rfl) ⟨2350760, by rfl⟩ : syracuseStep 12537389 = 4701521) B4701521
theorem B15093479 : Blo 694316 15093479 := bstep (se 1 (by rfl) ⟨11320109, by rfl⟩ : syracuseStep 15093479 = 22640219) B22640219
theorem B2970425 : Blo 694316 2970425 := bstep (se 2 (by rfl) ⟨1113909, by rfl⟩ : syracuseStep 2970425 = 2227819) B2227819
theorem B97703495 : Blo 694316 97703495 := bstep (se 1 (by rfl) ⟨73277621, by rfl⟩ : syracuseStep 97703495 = 146555243) B146555243
theorem B5364143 : Blo 694316 5364143 := bstep (se 1 (by rfl) ⟨4023107, by rfl⟩ : syracuseStep 5364143 = 8046215) B8046215
theorem B1563227 : Blo 694316 1563227 := bstep (se 1 (by rfl) ⟨1172420, by rfl⟩ : syracuseStep 1563227 = 2344841) B2344841
theorem B6676843 : Blo 694316 6676843 := bstep (se 1 (by rfl) ⟨5007632, by rfl⟩ : syracuseStep 6676843 = 10015265) B10015265
theorem B12739517 : Blo 694316 12739517 := bstep (se 3 (by rfl) ⟨2388659, by rfl⟩ : syracuseStep 12739517 = 4777319) B4777319
theorem B5727287 : Blo 694316 5727287 := bstep (se 1 (by rfl) ⟨4295465, by rfl⟩ : syracuseStep 5727287 = 8590931) B8590931
theorem B1041719 : Blo 694316 1041719 := bstep (se 1 (by rfl) ⟨781289, by rfl⟩ : syracuseStep 1041719 = 1562579) B1562579
theorem B1762631 : Blo 694316 1762631 := bstep (se 1 (by rfl) ⟨1321973, by rfl⟩ : syracuseStep 1762631 = 2643947) B2643947
theorem B20343095 : Blo 694316 20343095 := bstep (se 1 (by rfl) ⟨15257321, by rfl⟩ : syracuseStep 20343095 = 30514643) B30514643
theorem B1043615 : Blo 694316 1043615 := bstep (se 1 (by rfl) ⟨782711, by rfl⟩ : syracuseStep 1043615 = 1565423) B1565423
theorem B2977327 : Blo 694316 2977327 := bstep (se 1 (by rfl) ⟨2232995, by rfl⟩ : syracuseStep 2977327 = 4465991) B4465991
theorem B2355047 : Blo 694316 2355047 := bstep (se 1 (by rfl) ⟨1766285, by rfl⟩ : syracuseStep 2355047 = 3532571) B3532571
theorem B2355155 : Blo 694316 2355155 := bstep (se 1 (by rfl) ⟨1766366, by rfl⟩ : syracuseStep 2355155 = 3532733) B3532733
theorem B1044479 : Blo 694316 1044479 := bstep (se 1 (by rfl) ⟨783359, by rfl⟩ : syracuseStep 1044479 = 1566719) B1566719
theorem B783823 : Blo 694316 783823 := bstep (se 1 (by rfl) ⟨587867, by rfl⟩ : syracuseStep 783823 = 1175735) B1175735
theorem B1045991 : Blo 694316 1045991 := bstep (se 1 (by rfl) ⟨784493, by rfl⟩ : syracuseStep 1045991 = 1568987) B1568987
theorem B3339883 : Blo 694316 3339883 := bstep (se 1 (by rfl) ⟨2504912, by rfl⟩ : syracuseStep 3339883 = 5009825) B5009825
theorem B1046441 : Blo 694316 1046441 := bstep (se 2 (by rfl) ⟨392415, by rfl⟩ : syracuseStep 1046441 = 784831) B784831
theorem B882667 : Blo 694316 882667 := bstep (se 1 (by rfl) ⟨662000, by rfl⟩ : syracuseStep 882667 = 1324001) B1324001
theorem B1046921 : Blo 694316 1046921 := bstep (se 2 (by rfl) ⟨392595, by rfl⟩ : syracuseStep 1046921 = 785191) B785191
theorem B128318093 : Blo 694316 128318093 := bstep (se 3 (by rfl) ⟨24059642, by rfl⟩ : syracuseStep 128318093 = 48119285) B48119285
theorem B3963937 : Blo 694316 3963937 := bstep (se 2 (by rfl) ⟨1486476, by rfl⟩ : syracuseStep 3963937 = 2972953) B2972953
theorem B15040889 : Blo 694316 15040889 := bstep (se 2 (by rfl) ⟨5640333, by rfl⟩ : syracuseStep 15040889 = 11280667) B11280667
theorem B6031187 : Blo 694316 6031187 := bstep (se 1 (by rfl) ⟨4523390, by rfl⟩ : syracuseStep 6031187 = 9046781) B9046781
theorem B10062319 : Blo 694316 10062319 := bstep (se 1 (by rfl) ⟨7546739, by rfl⟩ : syracuseStep 10062319 = 15093479) B15093479
theorem B3576095 : Blo 694316 3576095 := bstep (se 1 (by rfl) ⟨2682071, by rfl⟩ : syracuseStep 3576095 = 5364143) B5364143
theorem B3969769 : Blo 694316 3969769 := bstep (se 2 (by rfl) ⟨1488663, by rfl⟩ : syracuseStep 3969769 = 2977327) B2977327
theorem B3216115 : Blo 694316 3216115 := bstep (se 1 (by rfl) ⟨2412086, by rfl⟩ : syracuseStep 3216115 = 4824173) B4824173
theorem B25401221 : Blo 694316 25401221 := bstep (se 4 (by rfl) ⟨2381364, by rfl⟩ : syracuseStep 25401221 = 4762729) B4762729
theorem B8493011 : Blo 694316 8493011 := bstep (se 1 (by rfl) ⟨6369758, by rfl⟩ : syracuseStep 8493011 = 12739517) B12739517
theorem B694479 : Blo 694316 694479 := bstep (se 1 (by rfl) ⟨520859, by rfl⟩ : syracuseStep 694479 = 1041719) B1041719
theorem B15080255 : Blo 694316 15080255 := bstep (se 1 (by rfl) ⟨11310191, by rfl⟩ : syracuseStep 15080255 = 22620383) B22620383
theorem B695743 : Blo 694316 695743 := bstep (se 1 (by rfl) ⟨521807, by rfl⟩ : syracuseStep 695743 = 1043615) B1043615
theorem B696319 : Blo 694316 696319 := bstep (se 1 (by rfl) ⟨522239, by rfl⟩ : syracuseStep 696319 = 1044479) B1044479
theorem B697327 : Blo 694316 697327 := bstep (se 1 (by rfl) ⟨522995, by rfl⟩ : syracuseStep 697327 = 1045991) B1045991
theorem B697627 : Blo 694316 697627 := bstep (se 1 (by rfl) ⟨523220, by rfl⟩ : syracuseStep 697627 = 1046441) B1046441
theorem B5285249 : Blo 694316 5285249 := bstep (se 2 (by rfl) ⟨1981968, by rfl⟩ : syracuseStep 5285249 = 3963937) B3963937
theorem B33433037 : Blo 694316 33433037 := bstep (se 3 (by rfl) ⟨6268694, by rfl⟩ : syracuseStep 33433037 = 12537389) B12537389
theorem B697947 : Blo 694316 697947 := bstep (se 1 (by rfl) ⟨523460, by rfl⟩ : syracuseStep 697947 = 1046921) B1046921
theorem B36187559 : Blo 694316 36187559 := bstep (se 1 (by rfl) ⟨27140669, by rfl⟩ : syracuseStep 36187559 = 54281339) B54281339
theorem B3519935 : Blo 694316 3519935 := bstep (se 1 (by rfl) ⟨2639951, by rfl⟩ : syracuseStep 3519935 = 5279903) B5279903
theorem B6338081 : Blo 694316 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B1980283 : Blo 694316 1980283 := bstep (se 1 (by rfl) ⟨1485212, by rfl⟩ : syracuseStep 1980283 = 2970425) B2970425
theorem B16038091 : Blo 694316 16038091 := bstep (se 1 (by rfl) ⟨12028568, by rfl⟩ : syracuseStep 16038091 = 24057137) B24057137
theorem B3818191 : Blo 694316 3818191 := bstep (se 1 (by rfl) ⟨2863643, by rfl⟩ : syracuseStep 3818191 = 5727287) B5727287
theorem B2639101 : Blo 694316 2639101 := bstep (se 3 (by rfl) ⟨494831, by rfl⟩ : syracuseStep 2639101 = 989663) B989663
theorem B5295455 : Blo 694316 5295455 := bstep (se 1 (by rfl) ⟨3971591, by rfl⟩ : syracuseStep 5295455 = 7943183) B7943183
theorem B8703713 : Blo 694316 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B85545395 : Blo 694316 85545395 := bstep (se 1 (by rfl) ⟨64159046, by rfl⟩ : syracuseStep 85545395 = 128318093) B128318093
theorem B8902457 : Blo 694316 8902457 := bstep (se 2 (by rfl) ⟨3338421, by rfl⟩ : syracuseStep 8902457 = 6676843) B6676843
theorem B3529007 : Blo 694316 3529007 := bstep (se 1 (by rfl) ⟨2646755, by rfl⟩ : syracuseStep 3529007 = 5293511) B5293511
theorem B1564271 : Blo 694316 1564271 := bstep (se 1 (by rfl) ⟨1173203, by rfl⟩ : syracuseStep 1564271 = 2346407) B2346407
theorem B65135663 : Blo 694316 65135663 := bstep (se 1 (by rfl) ⟨48851747, by rfl⟩ : syracuseStep 65135663 = 97703495) B97703495
theorem B1042151 : Blo 694316 1042151 := bstep (se 1 (by rfl) ⟨781613, by rfl⟩ : syracuseStep 1042151 = 1563227) B1563227
theorem B1175087 : Blo 694316 1175087 := bstep (se 1 (by rfl) ⟨881315, by rfl⟩ : syracuseStep 1175087 = 1762631) B1762631
theorem B2650279 : Blo 694316 2650279 := bstep (se 1 (by rfl) ⟨1987709, by rfl⟩ : syracuseStep 2650279 = 3975419) B3975419
theorem B13562063 : Blo 694316 13562063 := bstep (se 1 (by rfl) ⟨10171547, by rfl⟩ : syracuseStep 13562063 = 20343095) B20343095
theorem B1045097 : Blo 694316 1045097 := bstep (se 2 (by rfl) ⟨391911, by rfl⟩ : syracuseStep 1045097 = 783823) B783823
theorem B4453177 : Blo 694316 4453177 := bstep (se 2 (by rfl) ⟨1669941, by rfl⟩ : syracuseStep 4453177 = 3339883) B3339883
theorem B1570031 : Blo 694316 1570031 := bstep (se 1 (by rfl) ⟨1177523, by rfl⟩ : syracuseStep 1570031 = 2355047) B2355047
theorem B1570103 : Blo 694316 1570103 := bstep (se 1 (by rfl) ⟨1177577, by rfl⟩ : syracuseStep 1570103 = 2355155) B2355155
theorem B1176889 : Blo 694316 1176889 := bstep (se 2 (by rfl) ⟨441333, by rfl⟩ : syracuseStep 1176889 = 882667) B882667
theorem B4224413 : Blo 694316 4224413 := bstep (se 3 (by rfl) ⟨792077, by rfl⟩ : syracuseStep 4224413 = 1584155) B1584155
theorem B10320317 : Blo 694316 10320317 := bstep (se 3 (by rfl) ⟨1935059, by rfl⟩ : syracuseStep 10320317 = 3870119) B3870119
theorem B10027259 : Blo 694316 10027259 := bstep (se 1 (by rfl) ⟨7520444, by rfl⟩ : syracuseStep 10027259 = 15040889) B15040889
theorem B5934971 : Blo 694316 5934971 := bstep (se 1 (by rfl) ⟨4451228, by rfl⟩ : syracuseStep 5934971 = 8902457) B8902457
theorem B43423775 : Blo 694316 43423775 := bstep (se 1 (by rfl) ⟨32567831, by rfl⟩ : syracuseStep 43423775 = 65135663) B65135663
theorem B22288691 : Blo 694316 22288691 := bstep (se 1 (by rfl) ⟨16716518, by rfl⟩ : syracuseStep 22288691 = 33433037) B33433037
theorem B5937569 : Blo 694316 5937569 := bstep (se 2 (by rfl) ⟨2226588, by rfl⟩ : syracuseStep 5937569 = 4453177) B4453177
theorem B694767 : Blo 694316 694767 := bstep (se 1 (by rfl) ⟨521075, by rfl⟩ : syracuseStep 694767 = 1042151) B1042151
theorem B24125039 : Blo 694316 24125039 := bstep (se 1 (by rfl) ⟨18093779, by rfl⟩ : syracuseStep 24125039 = 36187559) B36187559
theorem B696731 : Blo 694316 696731 := bstep (se 1 (by rfl) ⟨522548, by rfl⟩ : syracuseStep 696731 = 1045097) B1045097
theorem B23209901 : Blo 694316 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B5090921 : Blo 694316 5090921 := bstep (se 2 (by rfl) ⟨1909095, by rfl⟩ : syracuseStep 5090921 = 3818191) B3818191
theorem B3518801 : Blo 694316 3518801 := bstep (se 2 (by rfl) ⟨1319550, by rfl⟩ : syracuseStep 3518801 = 2639101) B2639101
theorem B57030263 : Blo 694316 57030263 := bstep (se 1 (by rfl) ⟨42772697, by rfl⟩ : syracuseStep 57030263 = 85545395) B85545395
theorem B13416425 : Blo 694316 13416425 := bstep (se 2 (by rfl) ⟨5031159, by rfl⟩ : syracuseStep 13416425 = 10062319) B10062319
theorem B3523499 : Blo 694316 3523499 := bstep (se 1 (by rfl) ⟨2642624, by rfl⟩ : syracuseStep 3523499 = 5285249) B5285249
theorem B5293025 : Blo 694316 5293025 := bstep (se 2 (by rfl) ⟨1984884, by rfl⟩ : syracuseStep 5293025 = 3969769) B3969769
theorem B2640377 : Blo 694316 2640377 := bstep (se 2 (by rfl) ⟨990141, by rfl⟩ : syracuseStep 2640377 = 1980283) B1980283
theorem B21384121 : Blo 694316 21384121 := bstep (se 2 (by rfl) ⟨8019045, by rfl⟩ : syracuseStep 21384121 = 16038091) B16038091
theorem B2346623 : Blo 694316 2346623 := bstep (se 1 (by rfl) ⟨1759967, by rfl⟩ : syracuseStep 2346623 = 3519935) B3519935
theorem B4020791 : Blo 694316 4020791 := bstep (se 1 (by rfl) ⟨3015593, by rfl⟩ : syracuseStep 4020791 = 6031187) B6031187
theorem B3530303 : Blo 694316 3530303 := bstep (se 1 (by rfl) ⟨2647727, by rfl⟩ : syracuseStep 3530303 = 5295455) B5295455
theorem B2384063 : Blo 694316 2384063 := bstep (se 1 (by rfl) ⟨1788047, by rfl⟩ : syracuseStep 2384063 = 3576095) B3576095
theorem B11265101 : Blo 694316 11265101 := bstep (se 3 (by rfl) ⟨2112206, by rfl⟩ : syracuseStep 11265101 = 4224413) B4224413
theorem B16934147 : Blo 694316 16934147 := bstep (se 1 (by rfl) ⟨12700610, by rfl⟩ : syracuseStep 16934147 = 25401221) B25401221
theorem B5662007 : Blo 694316 5662007 := bstep (se 1 (by rfl) ⟨4246505, by rfl⟩ : syracuseStep 5662007 = 8493011) B8493011
theorem B2352671 : Blo 694316 2352671 := bstep (se 1 (by rfl) ⟨1764503, by rfl⟩ : syracuseStep 2352671 = 3529007) B3529007
theorem B10053503 : Blo 694316 10053503 := bstep (se 1 (by rfl) ⟨7540127, by rfl⟩ : syracuseStep 10053503 = 15080255) B15080255
theorem B1042847 : Blo 694316 1042847 := bstep (se 1 (by rfl) ⟨782135, by rfl⟩ : syracuseStep 1042847 = 1564271) B1564271
theorem B3533705 : Blo 694316 3533705 := bstep (se 2 (by rfl) ⟨1325139, by rfl⟩ : syracuseStep 3533705 = 2650279) B2650279
theorem B4288153 : Blo 694316 4288153 := bstep (se 2 (by rfl) ⟨1608057, by rfl⟩ : syracuseStep 4288153 = 3216115) B3216115
theorem B1569185 : Blo 694316 1569185 := bstep (se 2 (by rfl) ⟨588444, by rfl⟩ : syracuseStep 1569185 = 1176889) B1176889
theorem B783391 : Blo 694316 783391 := bstep (se 1 (by rfl) ⟨587543, by rfl⟩ : syracuseStep 783391 = 1175087) B1175087
theorem B9041375 : Blo 694316 9041375 := bstep (se 1 (by rfl) ⟨6781031, by rfl⟩ : syracuseStep 9041375 = 13562063) B13562063
theorem B1046687 : Blo 694316 1046687 := bstep (se 1 (by rfl) ⟨785015, by rfl⟩ : syracuseStep 1046687 = 1570031) B1570031
theorem B1046735 : Blo 694316 1046735 := bstep (se 1 (by rfl) ⟨785051, by rfl⟩ : syracuseStep 1046735 = 1570103) B1570103
theorem B4225387 : Blo 694316 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B6880211 : Blo 694316 6880211 := bstep (se 1 (by rfl) ⟨5160158, by rfl⟩ : syracuseStep 6880211 = 10320317) B10320317
theorem B6684839 : Blo 694316 6684839 := bstep (se 1 (by rfl) ⟨5013629, by rfl⟩ : syracuseStep 6684839 = 10027259) B10027259
theorem B28512161 : Blo 694316 28512161 := bstep (se 2 (by rfl) ⟨10692060, by rfl⟩ : syracuseStep 28512161 = 21384121) B21384121
theorem B7510067 : Blo 694316 7510067 := bstep (se 1 (by rfl) ⟨5632550, by rfl⟩ : syracuseStep 7510067 = 11265101) B11265101
theorem B3774671 : Blo 694316 3774671 := bstep (se 1 (by rfl) ⟨2831003, by rfl⟩ : syracuseStep 3774671 = 5662007) B5662007
theorem B15473267 : Blo 694316 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B695231 : Blo 694316 695231 := bstep (se 1 (by rfl) ⟨521423, by rfl⟩ : syracuseStep 695231 = 1042847) B1042847
theorem B38020175 : Blo 694316 38020175 := bstep (se 1 (by rfl) ⟨28515131, by rfl⟩ : syracuseStep 38020175 = 57030263) B57030263
theorem B697791 : Blo 694316 697791 := bstep (se 1 (by rfl) ⟨523343, by rfl⟩ : syracuseStep 697791 = 1046687) B1046687
theorem B697823 : Blo 694316 697823 := bstep (se 1 (by rfl) ⟨523367, by rfl⟩ : syracuseStep 697823 = 1046735) B1046735
theorem B28949183 : Blo 694316 28949183 := bstep (se 1 (by rfl) ⟨21711887, by rfl⟩ : syracuseStep 28949183 = 43423775) B43423775
theorem B5717537 : Blo 694316 5717537 := bstep (se 2 (by rfl) ⟨2144076, by rfl⟩ : syracuseStep 5717537 = 4288153) B4288153
theorem B1589375 : Blo 694316 1589375 := bstep (se 1 (by rfl) ⟨1192031, by rfl⟩ : syracuseStep 1589375 = 2384063) B2384063
theorem B11289431 : Blo 694316 11289431 := bstep (se 1 (by rfl) ⟨8467073, by rfl⟩ : syracuseStep 11289431 = 16934147) B16934147
theorem B6702335 : Blo 694316 6702335 := bstep (se 1 (by rfl) ⟨5026751, by rfl⟩ : syracuseStep 6702335 = 10053503) B10053503
theorem B3393947 : Blo 694316 3393947 := bstep (se 1 (by rfl) ⟨2545460, by rfl⟩ : syracuseStep 3393947 = 5090921) B5090921
theorem B2345867 : Blo 694316 2345867 := bstep (se 1 (by rfl) ⟨1759400, by rfl⟩ : syracuseStep 2345867 = 3518801) B3518801
theorem B2348999 : Blo 694316 2348999 := bstep (se 1 (by rfl) ⟨1761749, by rfl⟩ : syracuseStep 2348999 = 3523499) B3523499
theorem B3528683 : Blo 694316 3528683 := bstep (se 1 (by rfl) ⟨2646512, by rfl⟩ : syracuseStep 3528683 = 5293025) B5293025
theorem B1760251 : Blo 694316 1760251 := bstep (se 1 (by rfl) ⟨1320188, by rfl⟩ : syracuseStep 1760251 = 2640377) B2640377
theorem B1564415 : Blo 694316 1564415 := bstep (se 1 (by rfl) ⟨1173311, by rfl⟩ : syracuseStep 1564415 = 2346623) B2346623
theorem B3956647 : Blo 694316 3956647 := bstep (se 1 (by rfl) ⟨2967485, by rfl⟩ : syracuseStep 3956647 = 5934971) B5934971
theorem B3958379 : Blo 694316 3958379 := bstep (se 1 (by rfl) ⟨2968784, by rfl⟩ : syracuseStep 3958379 = 5937569) B5937569
theorem B2353535 : Blo 694316 2353535 := bstep (se 1 (by rfl) ⟨1765151, by rfl⟩ : syracuseStep 2353535 = 3530303) B3530303
theorem B16083359 : Blo 694316 16083359 := bstep (se 1 (by rfl) ⟨12062519, by rfl⟩ : syracuseStep 16083359 = 24125039) B24125039
theorem B42888437 : Blo 694316 42888437 := bstep (se 5 (by rfl) ⟨2010395, by rfl⟩ : syracuseStep 42888437 = 4020791) B4020791
theorem B59436509 : Blo 694316 59436509 := bstep (se 3 (by rfl) ⟨11144345, by rfl⟩ : syracuseStep 59436509 = 22288691) B22288691
theorem B1568447 : Blo 694316 1568447 := bstep (se 1 (by rfl) ⟨1176335, by rfl⟩ : syracuseStep 1568447 = 2352671) B2352671
theorem B1044521 : Blo 694316 1044521 := bstep (se 2 (by rfl) ⟨391695, by rfl⟩ : syracuseStep 1044521 = 783391) B783391
theorem B2355803 : Blo 694316 2355803 := bstep (se 1 (by rfl) ⟨1766852, by rfl⟩ : syracuseStep 2355803 = 3533705) B3533705
theorem B1046123 : Blo 694316 1046123 := bstep (se 1 (by rfl) ⟨784592, by rfl⟩ : syracuseStep 1046123 = 1569185) B1569185
theorem B5633849 : Blo 694316 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B6027583 : Blo 694316 6027583 := bstep (se 1 (by rfl) ⟨4520687, by rfl⟩ : syracuseStep 6027583 = 9041375) B9041375
theorem B8944283 : Blo 694316 8944283 := bstep (se 1 (by rfl) ⟨6708212, by rfl⟩ : syracuseStep 8944283 = 13416425) B13416425
theorem B4586807 : Blo 694316 4586807 := bstep (se 1 (by rfl) ⟨3440105, by rfl⟩ : syracuseStep 4586807 = 6880211) B6880211
theorem B4456559 : Blo 694316 4456559 := bstep (se 1 (by rfl) ⟨3342419, by rfl⟩ : syracuseStep 4456559 = 6684839) B6684839
theorem B19008107 : Blo 694316 19008107 := bstep (se 1 (by rfl) ⟨14256080, by rfl⟩ : syracuseStep 19008107 = 28512161) B28512161
theorem B9050525 : Blo 694316 9050525 := bstep (se 3 (by rfl) ⟨1696973, by rfl⟩ : syracuseStep 9050525 = 3393947) B3393947
theorem B10722239 : Blo 694316 10722239 := bstep (se 1 (by rfl) ⟨8041679, by rfl⟩ : syracuseStep 10722239 = 16083359) B16083359
theorem B696347 : Blo 694316 696347 := bstep (se 1 (by rfl) ⟨522260, by rfl⟩ : syracuseStep 696347 = 1044521) B1044521
theorem B8036777 : Blo 694316 8036777 := bstep (se 2 (by rfl) ⟨3013791, by rfl⟩ : syracuseStep 8036777 = 6027583) B6027583
theorem B697415 : Blo 694316 697415 := bstep (se 1 (by rfl) ⟨523061, by rfl⟩ : syracuseStep 697415 = 1046123) B1046123
theorem B3057871 : Blo 694316 3057871 := bstep (se 1 (by rfl) ⟨2293403, by rfl⟩ : syracuseStep 3057871 = 4586807) B4586807
theorem B3811691 : Blo 694316 3811691 := bstep (se 1 (by rfl) ⟨2858768, by rfl⟩ : syracuseStep 3811691 = 5717537) B5717537
theorem B1059583 : Blo 694316 1059583 := bstep (se 1 (by rfl) ⟨794687, by rfl⟩ : syracuseStep 1059583 = 1589375) B1589375
theorem B4468223 : Blo 694316 4468223 := bstep (se 1 (by rfl) ⟨3351167, by rfl⟩ : syracuseStep 4468223 = 6702335) B6702335
theorem B25346783 : Blo 694316 25346783 := bstep (se 1 (by rfl) ⟨19010087, by rfl⟩ : syracuseStep 25346783 = 38020175) B38020175
theorem B2638919 : Blo 694316 2638919 := bstep (se 1 (by rfl) ⟨1979189, by rfl⟩ : syracuseStep 2638919 = 3958379) B3958379
theorem B28592291 : Blo 694316 28592291 := bstep (se 1 (by rfl) ⟨21444218, by rfl⟩ : syracuseStep 28592291 = 42888437) B42888437
theorem B3755899 : Blo 694316 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B2347001 : Blo 694316 2347001 := bstep (se 2 (by rfl) ⟨880125, by rfl⟩ : syracuseStep 2347001 = 1760251) B1760251
theorem B7526287 : Blo 694316 7526287 := bstep (se 1 (by rfl) ⟨5644715, by rfl⟩ : syracuseStep 7526287 = 11289431) B11289431
theorem B1563911 : Blo 694316 1563911 := bstep (se 1 (by rfl) ⟨1172933, by rfl⟩ : syracuseStep 1563911 = 2345867) B2345867
theorem B1565999 : Blo 694316 1565999 := bstep (se 1 (by rfl) ⟨1174499, by rfl⟩ : syracuseStep 1565999 = 2348999) B2348999
theorem B2352455 : Blo 694316 2352455 := bstep (se 1 (by rfl) ⟨1764341, by rfl⟩ : syracuseStep 2352455 = 3528683) B3528683
theorem B5006711 : Blo 694316 5006711 := bstep (se 1 (by rfl) ⟨3755033, by rfl⟩ : syracuseStep 5006711 = 7510067) B7510067
theorem B2516447 : Blo 694316 2516447 := bstep (se 1 (by rfl) ⟨1887335, by rfl⟩ : syracuseStep 2516447 = 3774671) B3774671
theorem B10315511 : Blo 694316 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B1042943 : Blo 694316 1042943 := bstep (se 1 (by rfl) ⟨782207, by rfl⟩ : syracuseStep 1042943 = 1564415) B1564415
theorem B1569023 : Blo 694316 1569023 := bstep (se 1 (by rfl) ⟨1176767, by rfl⟩ : syracuseStep 1569023 = 2353535) B2353535
theorem B1045631 : Blo 694316 1045631 := bstep (se 1 (by rfl) ⟨784223, by rfl⟩ : syracuseStep 1045631 = 1568447) B1568447
theorem B1570535 : Blo 694316 1570535 := bstep (se 1 (by rfl) ⟨1177901, by rfl⟩ : syracuseStep 1570535 = 2355803) B2355803
theorem B158497357 : Blo 694316 158497357 := bstep (se 3 (by rfl) ⟨29718254, by rfl⟩ : syracuseStep 158497357 = 59436509) B59436509
theorem B5962855 : Blo 694316 5962855 := bstep (se 1 (by rfl) ⟨4472141, by rfl⟩ : syracuseStep 5962855 = 8944283) B8944283
theorem B19299455 : Blo 694316 19299455 := bstep (se 1 (by rfl) ⟨14474591, by rfl⟩ : syracuseStep 19299455 = 28949183) B28949183
theorem B5275529 : Blo 694316 5275529 := bstep (se 2 (by rfl) ⟨1978323, by rfl⟩ : syracuseStep 5275529 = 3956647) B3956647
theorem B1412777 : Blo 694316 1412777 := bstep (se 2 (by rfl) ⟨529791, by rfl⟩ : syracuseStep 1412777 = 1059583) B1059583
theorem B6033683 : Blo 694316 6033683 := bstep (se 1 (by rfl) ⟨4525262, by rfl⟩ : syracuseStep 6033683 = 9050525) B9050525
theorem B7148159 : Blo 694316 7148159 := bstep (se 1 (by rfl) ⟨5361119, by rfl⟩ : syracuseStep 7148159 = 10722239) B10722239
theorem B1677631 : Blo 694316 1677631 := bstep (se 1 (by rfl) ⟨1258223, by rfl⟩ : syracuseStep 1677631 = 2516447) B2516447
theorem B695295 : Blo 694316 695295 := bstep (se 1 (by rfl) ⟨521471, by rfl⟩ : syracuseStep 695295 = 1042943) B1042943
theorem B10035049 : Blo 694316 10035049 := bstep (se 2 (by rfl) ⟨3763143, by rfl⟩ : syracuseStep 10035049 = 7526287) B7526287
theorem B697087 : Blo 694316 697087 := bstep (se 1 (by rfl) ⟨522815, by rfl⟩ : syracuseStep 697087 = 1045631) B1045631
theorem B211329809 : Blo 694316 211329809 := bstep (se 2 (by rfl) ⟨79248678, by rfl⟩ : syracuseStep 211329809 = 158497357) B158497357
theorem B3517019 : Blo 694316 3517019 := bstep (se 1 (by rfl) ⟨2637764, by rfl⟩ : syracuseStep 3517019 = 5275529) B5275529
theorem B4077161 : Blo 694316 4077161 := bstep (se 2 (by rfl) ⟨1528935, by rfl⟩ : syracuseStep 4077161 = 3057871) B3057871
theorem B5357851 : Blo 694316 5357851 := bstep (se 1 (by rfl) ⟨4018388, by rfl⟩ : syracuseStep 5357851 = 8036777) B8036777
theorem B2541127 : Blo 694316 2541127 := bstep (se 1 (by rfl) ⟨1905845, by rfl⟩ : syracuseStep 2541127 = 3811691) B3811691
theorem B7950473 : Blo 694316 7950473 := bstep (se 2 (by rfl) ⟨2981427, by rfl⟩ : syracuseStep 7950473 = 5962855) B5962855
theorem B12866303 : Blo 694316 12866303 := bstep (se 1 (by rfl) ⟨9649727, by rfl⟩ : syracuseStep 12866303 = 19299455) B19299455
theorem B11884157 : Blo 694316 11884157 := bstep (se 3 (by rfl) ⟨2228279, by rfl⟩ : syracuseStep 11884157 = 4456559) B4456559
theorem B16897855 : Blo 694316 16897855 := bstep (se 1 (by rfl) ⟨12673391, by rfl⟩ : syracuseStep 16897855 = 25346783) B25346783
theorem B1759279 : Blo 694316 1759279 := bstep (se 1 (by rfl) ⟨1319459, by rfl⟩ : syracuseStep 1759279 = 2638919) B2638919
theorem B19061527 : Blo 694316 19061527 := bstep (se 1 (by rfl) ⟨14296145, by rfl⟩ : syracuseStep 19061527 = 28592291) B28592291
theorem B12672071 : Blo 694316 12672071 := bstep (se 1 (by rfl) ⟨9504053, by rfl⟩ : syracuseStep 12672071 = 19008107) B19008107
theorem B1564667 : Blo 694316 1564667 := bstep (se 1 (by rfl) ⟨1173500, by rfl⟩ : syracuseStep 1564667 = 2347001) B2347001
theorem B1042607 : Blo 694316 1042607 := bstep (se 1 (by rfl) ⟨781955, by rfl⟩ : syracuseStep 1042607 = 1563911) B1563911
theorem B5007865 : Blo 694316 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B1043999 : Blo 694316 1043999 := bstep (se 1 (by rfl) ⟨782999, by rfl⟩ : syracuseStep 1043999 = 1565999) B1565999
theorem B1568303 : Blo 694316 1568303 := bstep (se 1 (by rfl) ⟨1176227, by rfl⟩ : syracuseStep 1568303 = 2352455) B2352455
theorem B3337807 : Blo 694316 3337807 := bstep (se 1 (by rfl) ⟨2503355, by rfl⟩ : syracuseStep 3337807 = 5006711) B5006711
theorem B6877007 : Blo 694316 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B2978815 : Blo 694316 2978815 := bstep (se 1 (by rfl) ⟨2234111, by rfl⟩ : syracuseStep 2978815 = 4468223) B4468223
theorem B1046015 : Blo 694316 1046015 := bstep (se 1 (by rfl) ⟨784511, by rfl⟩ : syracuseStep 1046015 = 1569023) B1569023
theorem B1047023 : Blo 694316 1047023 := bstep (se 1 (by rfl) ⟨785267, by rfl⟩ : syracuseStep 1047023 = 1570535) B1570535
theorem B114300821 : Blo 694316 114300821 := bstep (se 6 (by rfl) ⟨2678925, by rfl⟩ : syracuseStep 114300821 = 5357851) B5357851
theorem B3971753 : Blo 694316 3971753 := bstep (se 2 (by rfl) ⟨1489407, by rfl⟩ : syracuseStep 3971753 = 2978815) B2978815
theorem B695071 : Blo 694316 695071 := bstep (se 1 (by rfl) ⟨521303, by rfl⟩ : syracuseStep 695071 = 1042607) B1042607
theorem B695999 : Blo 694316 695999 := bstep (se 1 (by rfl) ⟨521999, by rfl⟩ : syracuseStep 695999 = 1043999) B1043999
theorem B2236841 : Blo 694316 2236841 := bstep (se 2 (by rfl) ⟨838815, by rfl⟩ : syracuseStep 2236841 = 1677631) B1677631
theorem B697343 : Blo 694316 697343 := bstep (se 1 (by rfl) ⟨523007, by rfl⟩ : syracuseStep 697343 = 1046015) B1046015
theorem B698015 : Blo 694316 698015 := bstep (se 1 (by rfl) ⟨523511, by rfl⟩ : syracuseStep 698015 = 1047023) B1047023
theorem B13380065 : Blo 694316 13380065 := bstep (se 2 (by rfl) ⟨5017524, by rfl⟩ : syracuseStep 13380065 = 10035049) B10035049
theorem B3388169 : Blo 694316 3388169 := bstep (se 2 (by rfl) ⟨1270563, by rfl⟩ : syracuseStep 3388169 = 2541127) B2541127
theorem B4765439 : Blo 694316 4765439 := bstep (se 1 (by rfl) ⟨3574079, by rfl⟩ : syracuseStep 4765439 = 7148159) B7148159
theorem B140886539 : Blo 694316 140886539 := bstep (se 1 (by rfl) ⟨105664904, by rfl⟩ : syracuseStep 140886539 = 211329809) B211329809
theorem B2344679 : Blo 694316 2344679 := bstep (se 1 (by rfl) ⟨1758509, by rfl⟩ : syracuseStep 2344679 = 3517019) B3517019
theorem B22530473 : Blo 694316 22530473 := bstep (se 2 (by rfl) ⟨8448927, by rfl⟩ : syracuseStep 22530473 = 16897855) B16897855
theorem B2345705 : Blo 694316 2345705 := bstep (se 2 (by rfl) ⟨879639, by rfl⟩ : syracuseStep 2345705 = 1759279) B1759279
theorem B25415369 : Blo 694316 25415369 := bstep (se 2 (by rfl) ⟨9530763, by rfl⟩ : syracuseStep 25415369 = 19061527) B19061527
theorem B941851 : Blo 694316 941851 := bstep (se 1 (by rfl) ⟨706388, by rfl⟩ : syracuseStep 941851 = 1412777) B1412777
theorem B5300315 : Blo 694316 5300315 := bstep (se 1 (by rfl) ⟨3975236, by rfl⟩ : syracuseStep 5300315 = 7950473) B7950473
theorem B4022455 : Blo 694316 4022455 := bstep (se 1 (by rfl) ⟨3016841, by rfl⟩ : syracuseStep 4022455 = 6033683) B6033683
theorem B8577535 : Blo 694316 8577535 := bstep (se 1 (by rfl) ⟨6433151, by rfl⟩ : syracuseStep 8577535 = 12866303) B12866303
theorem B6677153 : Blo 694316 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B7922771 : Blo 694316 7922771 := bstep (se 1 (by rfl) ⟨5942078, by rfl⟩ : syracuseStep 7922771 = 11884157) B11884157
theorem B8448047 : Blo 694316 8448047 := bstep (se 1 (by rfl) ⟨6336035, by rfl⟩ : syracuseStep 8448047 = 12672071) B12672071
theorem B4450409 : Blo 694316 4450409 := bstep (se 2 (by rfl) ⟨1668903, by rfl⟩ : syracuseStep 4450409 = 3337807) B3337807
theorem B1043111 : Blo 694316 1043111 := bstep (se 1 (by rfl) ⟨782333, by rfl⟩ : syracuseStep 1043111 = 1564667) B1564667
theorem B1045535 : Blo 694316 1045535 := bstep (se 1 (by rfl) ⟨784151, by rfl⟩ : syracuseStep 1045535 = 1568303) B1568303
theorem B4584671 : Blo 694316 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B2718107 : Blo 694316 2718107 := bstep (se 1 (by rfl) ⟨2038580, by rfl⟩ : syracuseStep 2718107 = 4077161) B4077161
theorem B11436713 : Blo 694316 11436713 := bstep (se 2 (by rfl) ⟨4288767, by rfl⟩ : syracuseStep 11436713 = 8577535) B8577535
theorem B16943579 : Blo 694316 16943579 := bstep (se 1 (by rfl) ⟨12707684, by rfl⟩ : syracuseStep 16943579 = 25415369) B25415369
theorem B5281847 : Blo 694316 5281847 := bstep (se 1 (by rfl) ⟨3961385, by rfl⟩ : syracuseStep 5281847 = 7922771) B7922771
theorem B8920043 : Blo 694316 8920043 := bstep (se 1 (by rfl) ⟨6690032, by rfl⟩ : syracuseStep 8920043 = 13380065) B13380065
theorem B695407 : Blo 694316 695407 := bstep (se 1 (by rfl) ⟨521555, by rfl⟩ : syracuseStep 695407 = 1043111) B1043111
theorem B697023 : Blo 694316 697023 := bstep (se 1 (by rfl) ⟨522767, by rfl⟩ : syracuseStep 697023 = 1045535) B1045535
theorem B3056447 : Blo 694316 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B5023205 : Blo 694316 5023205 := bstep (se 4 (by rfl) ⟨470925, by rfl⟩ : syracuseStep 5023205 = 941851) B941851
theorem B1812071 : Blo 694316 1812071 := bstep (se 1 (by rfl) ⟨1359053, by rfl⟩ : syracuseStep 1812071 = 2718107) B2718107
theorem B93924359 : Blo 694316 93924359 := bstep (se 1 (by rfl) ⟨70443269, by rfl⟩ : syracuseStep 93924359 = 140886539) B140886539
theorem B15020315 : Blo 694316 15020315 := bstep (se 1 (by rfl) ⟨11265236, by rfl⟩ : syracuseStep 15020315 = 22530473) B22530473
theorem B76200547 : Blo 694316 76200547 := bstep (se 1 (by rfl) ⟨57150410, by rfl⟩ : syracuseStep 76200547 = 114300821) B114300821
theorem B1491227 : Blo 694316 1491227 := bstep (se 1 (by rfl) ⟨1118420, by rfl⟩ : syracuseStep 1491227 = 2236841) B2236841
theorem B2966939 : Blo 694316 2966939 := bstep (se 1 (by rfl) ⟨2225204, by rfl⟩ : syracuseStep 2966939 = 4450409) B4450409
theorem B5363273 : Blo 694316 5363273 := bstep (se 2 (by rfl) ⟨2011227, by rfl⟩ : syracuseStep 5363273 = 4022455) B4022455
theorem B1563119 : Blo 694316 1563119 := bstep (se 1 (by rfl) ⟨1172339, by rfl⟩ : syracuseStep 1563119 = 2344679) B2344679
theorem B1563803 : Blo 694316 1563803 := bstep (se 1 (by rfl) ⟨1172852, by rfl⟩ : syracuseStep 1563803 = 2345705) B2345705
theorem B2647835 : Blo 694316 2647835 := bstep (se 1 (by rfl) ⟨1985876, by rfl⟩ : syracuseStep 2647835 = 3971753) B3971753
theorem B12707837 : Blo 694316 12707837 := bstep (se 3 (by rfl) ⟨2382719, by rfl⟩ : syracuseStep 12707837 = 4765439) B4765439
theorem B3533543 : Blo 694316 3533543 := bstep (se 1 (by rfl) ⟨2650157, by rfl⟩ : syracuseStep 3533543 = 5300315) B5300315
theorem B4451435 : Blo 694316 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B5632031 : Blo 694316 5632031 := bstep (se 1 (by rfl) ⟨4224023, by rfl⟩ : syracuseStep 5632031 = 8448047) B8448047
theorem B2258779 : Blo 694316 2258779 := bstep (se 1 (by rfl) ⟨1694084, by rfl⟩ : syracuseStep 2258779 = 3388169) B3388169
theorem B3575515 : Blo 694316 3575515 := bstep (se 1 (by rfl) ⟨2681636, by rfl⟩ : syracuseStep 3575515 = 5363273) B5363273
theorem B2037631 : Blo 694316 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B3348803 : Blo 694316 3348803 := bstep (se 1 (by rfl) ⟨2511602, by rfl⟩ : syracuseStep 3348803 = 5023205) B5023205
theorem B994151 : Blo 694316 994151 := bstep (se 1 (by rfl) ⟨745613, by rfl⟩ : syracuseStep 994151 = 1491227) B1491227
theorem B1977959 : Blo 694316 1977959 := bstep (se 1 (by rfl) ⟨1483469, by rfl⟩ : syracuseStep 1977959 = 2966939) B2966939
theorem B3521231 : Blo 694316 3521231 := bstep (se 1 (by rfl) ⟨2640923, by rfl⟩ : syracuseStep 3521231 = 5281847) B5281847
theorem B5946695 : Blo 694316 5946695 := bstep (se 1 (by rfl) ⟨4460021, by rfl⟩ : syracuseStep 5946695 = 8920043) B8920043
theorem B8471891 : Blo 694316 8471891 := bstep (se 1 (by rfl) ⟨6353918, by rfl⟩ : syracuseStep 8471891 = 12707837) B12707837
theorem B2967623 : Blo 694316 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B3754687 : Blo 694316 3754687 := bstep (se 1 (by rfl) ⟨2816015, by rfl⟩ : syracuseStep 3754687 = 5632031) B5632031
theorem B10013543 : Blo 694316 10013543 := bstep (se 1 (by rfl) ⟨7510157, by rfl⟩ : syracuseStep 10013543 = 15020315) B15020315
theorem B101600729 : Blo 694316 101600729 := bstep (se 2 (by rfl) ⟨38100273, by rfl⟩ : syracuseStep 101600729 = 76200547) B76200547
theorem B7624475 : Blo 694316 7624475 := bstep (se 1 (by rfl) ⟨5718356, by rfl⟩ : syracuseStep 7624475 = 11436713) B11436713
theorem B11295719 : Blo 694316 11295719 := bstep (se 1 (by rfl) ⟨8471789, by rfl⟩ : syracuseStep 11295719 = 16943579) B16943579
theorem B1042079 : Blo 694316 1042079 := bstep (se 1 (by rfl) ⟨781559, by rfl⟩ : syracuseStep 1042079 = 1563119) B1563119
theorem B1042535 : Blo 694316 1042535 := bstep (se 1 (by rfl) ⟨781901, by rfl⟩ : syracuseStep 1042535 = 1563803) B1563803
theorem B1208047 : Blo 694316 1208047 := bstep (se 1 (by rfl) ⟨906035, by rfl⟩ : syracuseStep 1208047 = 1812071) B1812071
theorem B1765223 : Blo 694316 1765223 := bstep (se 1 (by rfl) ⟨1323917, by rfl⟩ : syracuseStep 1765223 = 2647835) B2647835
theorem B2355695 : Blo 694316 2355695 := bstep (se 1 (by rfl) ⟨1766771, by rfl⟩ : syracuseStep 2355695 = 3533543) B3533543
theorem B62616239 : Blo 694316 62616239 := bstep (se 1 (by rfl) ⟨46962179, by rfl⟩ : syracuseStep 62616239 = 93924359) B93924359
theorem B3011705 : Blo 694316 3011705 := bstep (se 2 (by rfl) ⟨1129389, by rfl⟩ : syracuseStep 3011705 = 2258779) B2258779
theorem B67733819 : Blo 694316 67733819 := bstep (se 1 (by rfl) ⟨50800364, by rfl⟩ : syracuseStep 67733819 = 101600729) B101600729
theorem B5082983 : Blo 694316 5082983 := bstep (se 1 (by rfl) ⟨3812237, by rfl⟩ : syracuseStep 5082983 = 7624475) B7624475
theorem B2232535 : Blo 694316 2232535 := bstep (se 1 (by rfl) ⟨1674401, by rfl⟩ : syracuseStep 2232535 = 3348803) B3348803
theorem B1610729 : Blo 694316 1610729 := bstep (se 2 (by rfl) ⟨604023, by rfl⟩ : syracuseStep 1610729 = 1208047) B1208047
theorem B694719 : Blo 694316 694719 := bstep (se 1 (by rfl) ⟨521039, by rfl⟩ : syracuseStep 694719 = 1042079) B1042079
theorem B695023 : Blo 694316 695023 := bstep (se 1 (by rfl) ⟨521267, by rfl⟩ : syracuseStep 695023 = 1042535) B1042535
theorem B2007803 : Blo 694316 2007803 := bstep (se 1 (by rfl) ⟨1505852, by rfl⟩ : syracuseStep 2007803 = 3011705) B3011705
theorem B1978415 : Blo 694316 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B22591709 : Blo 694316 22591709 := bstep (se 3 (by rfl) ⟨4235945, by rfl⟩ : syracuseStep 22591709 = 8471891) B8471891
theorem B4767353 : Blo 694316 4767353 := bstep (se 2 (by rfl) ⟨1787757, by rfl⟩ : syracuseStep 4767353 = 3575515) B3575515
theorem B2347487 : Blo 694316 2347487 := bstep (se 1 (by rfl) ⟨1760615, by rfl⟩ : syracuseStep 2347487 = 3521231) B3521231
theorem B6675695 : Blo 694316 6675695 := bstep (se 1 (by rfl) ⟨5006771, by rfl⟩ : syracuseStep 6675695 = 10013543) B10013543
theorem B5006249 : Blo 694316 5006249 := bstep (se 2 (by rfl) ⟨1877343, by rfl⟩ : syracuseStep 5006249 = 3754687) B3754687
theorem B7530479 : Blo 694316 7530479 := bstep (se 1 (by rfl) ⟨5647859, by rfl⟩ : syracuseStep 7530479 = 11295719) B11295719
theorem B2651069 : Blo 694316 2651069 := bstep (se 3 (by rfl) ⟨497075, by rfl⟩ : syracuseStep 2651069 = 994151) B994151
theorem B2716841 : Blo 694316 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B1176815 : Blo 694316 1176815 := bstep (se 1 (by rfl) ⟨882611, by rfl⟩ : syracuseStep 1176815 = 1765223) B1765223
theorem B1570463 : Blo 694316 1570463 := bstep (se 1 (by rfl) ⟨1177847, by rfl⟩ : syracuseStep 1570463 = 2355695) B2355695
theorem B41744159 : Blo 694316 41744159 := bstep (se 1 (by rfl) ⟨31308119, by rfl⟩ : syracuseStep 41744159 = 62616239) B62616239
theorem B5274557 : Blo 694316 5274557 := bstep (se 3 (by rfl) ⟨988979, by rfl⟩ : syracuseStep 5274557 = 1977959) B1977959
theorem B3964463 : Blo 694316 3964463 := bstep (se 1 (by rfl) ⟨2973347, by rfl⟩ : syracuseStep 3964463 = 5946695) B5946695
theorem B45155879 : Blo 694316 45155879 := bstep (se 1 (by rfl) ⟨33866909, by rfl⟩ : syracuseStep 45155879 = 67733819) B67733819
theorem B7244909 : Blo 694316 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B5020319 : Blo 694316 5020319 := bstep (se 1 (by rfl) ⟨3765239, by rfl⟩ : syracuseStep 5020319 = 7530479) B7530479
theorem B1318943 : Blo 694316 1318943 := bstep (se 1 (by rfl) ⟨989207, by rfl⟩ : syracuseStep 1318943 = 1978415) B1978415
theorem B27829439 : Blo 694316 27829439 := bstep (se 1 (by rfl) ⟨20872079, by rfl⟩ : syracuseStep 27829439 = 41744159) B41744159
theorem B3516371 : Blo 694316 3516371 := bstep (se 1 (by rfl) ⟨2637278, by rfl⟩ : syracuseStep 3516371 = 5274557) B5274557
theorem B3388655 : Blo 694316 3388655 := bstep (se 1 (by rfl) ⟨2541491, by rfl⟩ : syracuseStep 3388655 = 5082983) B5082983
theorem B15061139 : Blo 694316 15061139 := bstep (se 1 (by rfl) ⟨11295854, by rfl⟩ : syracuseStep 15061139 = 22591709) B22591709
theorem B2642975 : Blo 694316 2642975 := bstep (se 1 (by rfl) ⟨1982231, by rfl⟩ : syracuseStep 2642975 = 3964463) B3964463
theorem B1564991 : Blo 694316 1564991 := bstep (se 1 (by rfl) ⟨1173743, by rfl⟩ : syracuseStep 1564991 = 2347487) B2347487
theorem B1073819 : Blo 694316 1073819 := bstep (se 1 (by rfl) ⟨805364, by rfl⟩ : syracuseStep 1073819 = 1610729) B1610729
theorem B4450463 : Blo 694316 4450463 := bstep (se 1 (by rfl) ⟨3337847, by rfl⟩ : syracuseStep 4450463 = 6675695) B6675695
theorem B2976713 : Blo 694316 2976713 := bstep (se 2 (by rfl) ⟨1116267, by rfl⟩ : syracuseStep 2976713 = 2232535) B2232535
theorem B1338535 : Blo 694316 1338535 := bstep (se 1 (by rfl) ⟨1003901, by rfl⟩ : syracuseStep 1338535 = 2007803) B2007803
theorem B3337499 : Blo 694316 3337499 := bstep (se 1 (by rfl) ⟨2503124, by rfl⟩ : syracuseStep 3337499 = 5006249) B5006249
theorem B1767379 : Blo 694316 1767379 := bstep (se 1 (by rfl) ⟨1325534, by rfl⟩ : syracuseStep 1767379 = 2651069) B2651069
theorem B784543 : Blo 694316 784543 := bstep (se 1 (by rfl) ⟨588407, by rfl⟩ : syracuseStep 784543 = 1176815) B1176815
theorem B1046975 : Blo 694316 1046975 := bstep (se 1 (by rfl) ⟨785231, by rfl⟩ : syracuseStep 1046975 = 1570463) B1570463
theorem B3178235 : Blo 694316 3178235 := bstep (se 1 (by rfl) ⟨2383676, by rfl⟩ : syracuseStep 3178235 = 4767353) B4767353
theorem B18552959 : Blo 694316 18552959 := bstep (se 1 (by rfl) ⟨13914719, by rfl⟩ : syracuseStep 18552959 = 27829439) B27829439
theorem B697983 : Blo 694316 697983 := bstep (se 1 (by rfl) ⟨523487, by rfl⟩ : syracuseStep 697983 = 1046975) B1046975
theorem B3517181 : Blo 694316 3517181 := bstep (se 3 (by rfl) ⟨659471, by rfl⟩ : syracuseStep 3517181 = 1318943) B1318943
theorem B4829939 : Blo 694316 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B10040759 : Blo 694316 10040759 := bstep (se 1 (by rfl) ⟨7530569, by rfl⟩ : syracuseStep 10040759 = 15061139) B15061139
theorem B1784713 : Blo 694316 1784713 := bstep (se 2 (by rfl) ⟨669267, by rfl⟩ : syracuseStep 1784713 = 1338535) B1338535
theorem B2344247 : Blo 694316 2344247 := bstep (se 1 (by rfl) ⟨1758185, by rfl⟩ : syracuseStep 2344247 = 3516371) B3516371
theorem B2966975 : Blo 694316 2966975 := bstep (se 1 (by rfl) ⟨2225231, by rfl⟩ : syracuseStep 2966975 = 4450463) B4450463
theorem B13387517 : Blo 694316 13387517 := bstep (se 3 (by rfl) ⟨2510159, by rfl⟩ : syracuseStep 13387517 = 5020319) B5020319
theorem B1984475 : Blo 694316 1984475 := bstep (se 1 (by rfl) ⟨1488356, by rfl⟩ : syracuseStep 1984475 = 2976713) B2976713
theorem B8475293 : Blo 694316 8475293 := bstep (se 3 (by rfl) ⟨1589117, by rfl⟩ : syracuseStep 8475293 = 3178235) B3178235
theorem B30103919 : Blo 694316 30103919 := bstep (se 1 (by rfl) ⟨22577939, by rfl⟩ : syracuseStep 30103919 = 45155879) B45155879
theorem B1761983 : Blo 694316 1761983 := bstep (se 1 (by rfl) ⟨1321487, by rfl⟩ : syracuseStep 1761983 = 2642975) B2642975
theorem B1043327 : Blo 694316 1043327 := bstep (se 1 (by rfl) ⟨782495, by rfl⟩ : syracuseStep 1043327 = 1564991) B1564991
theorem B715879 : Blo 694316 715879 := bstep (se 1 (by rfl) ⟨536909, by rfl⟩ : syracuseStep 715879 = 1073819) B1073819
theorem B2224999 : Blo 694316 2224999 := bstep (se 1 (by rfl) ⟨1668749, by rfl⟩ : syracuseStep 2224999 = 3337499) B3337499
theorem B2356505 : Blo 694316 2356505 := bstep (se 2 (by rfl) ⟨883689, by rfl⟩ : syracuseStep 2356505 = 1767379) B1767379
theorem B1046057 : Blo 694316 1046057 := bstep (se 2 (by rfl) ⟨392271, by rfl⟩ : syracuseStep 1046057 = 784543) B784543
theorem B2259103 : Blo 694316 2259103 := bstep (se 1 (by rfl) ⟨1694327, by rfl⟩ : syracuseStep 2259103 = 3388655) B3388655
theorem B954505 : Blo 694316 954505 := bstep (se 2 (by rfl) ⟨357939, by rfl⟩ : syracuseStep 954505 = 715879) B715879
theorem B11866661 : Blo 694316 11866661 := bstep (se 4 (by rfl) ⟨1112499, by rfl⟩ : syracuseStep 11866661 = 2224999) B2224999
theorem B695551 : Blo 694316 695551 := bstep (se 1 (by rfl) ⟨521663, by rfl⟩ : syracuseStep 695551 = 1043327) B1043327
theorem B3219959 : Blo 694316 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B6693839 : Blo 694316 6693839 := bstep (se 1 (by rfl) ⟨5020379, by rfl⟩ : syracuseStep 6693839 = 10040759) B10040759
theorem B697371 : Blo 694316 697371 := bstep (se 1 (by rfl) ⟨523028, by rfl⟩ : syracuseStep 697371 = 1046057) B1046057
theorem B1977983 : Blo 694316 1977983 := bstep (se 1 (by rfl) ⟨1483487, by rfl⟩ : syracuseStep 1977983 = 2966975) B2966975
theorem B8925011 : Blo 694316 8925011 := bstep (se 1 (by rfl) ⟨6693758, by rfl⟩ : syracuseStep 8925011 = 13387517) B13387517
theorem B1322983 : Blo 694316 1322983 := bstep (se 1 (by rfl) ⟨992237, by rfl⟩ : syracuseStep 1322983 = 1984475) B1984475
theorem B5650195 : Blo 694316 5650195 := bstep (se 1 (by rfl) ⟨4237646, by rfl⟩ : syracuseStep 5650195 = 8475293) B8475293
theorem B12368639 : Blo 694316 12368639 := bstep (se 1 (by rfl) ⟨9276479, by rfl⟩ : syracuseStep 12368639 = 18552959) B18552959
theorem B20069279 : Blo 694316 20069279 := bstep (se 1 (by rfl) ⟨15051959, by rfl⟩ : syracuseStep 20069279 = 30103919) B30103919
theorem B2344787 : Blo 694316 2344787 := bstep (se 1 (by rfl) ⟨1758590, by rfl⟩ : syracuseStep 2344787 = 3517181) B3517181
theorem B2379617 : Blo 694316 2379617 := bstep (se 2 (by rfl) ⟨892356, by rfl⟩ : syracuseStep 2379617 = 1784713) B1784713
theorem B1562831 : Blo 694316 1562831 := bstep (se 1 (by rfl) ⟨1172123, by rfl⟩ : syracuseStep 1562831 = 2344247) B2344247
theorem B1174655 : Blo 694316 1174655 := bstep (se 1 (by rfl) ⟨880991, by rfl⟩ : syracuseStep 1174655 = 1761983) B1761983
theorem B3012137 : Blo 694316 3012137 := bstep (se 2 (by rfl) ⟨1129551, by rfl⟩ : syracuseStep 3012137 = 2259103) B2259103
theorem B1571003 : Blo 694316 1571003 := bstep (se 1 (by rfl) ⟨1178252, by rfl⟩ : syracuseStep 1571003 = 2356505) B2356505
theorem B8586557 : Blo 694316 8586557 := bstep (se 3 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 8586557 = 3219959) B3219959
theorem B4462559 : Blo 694316 4462559 := bstep (se 1 (by rfl) ⟨3346919, by rfl⟩ : syracuseStep 4462559 = 6693839) B6693839
theorem B1318655 : Blo 694316 1318655 := bstep (se 1 (by rfl) ⟨988991, by rfl⟩ : syracuseStep 1318655 = 1977983) B1977983
theorem B2008091 : Blo 694316 2008091 := bstep (se 1 (by rfl) ⟨1506068, by rfl⟩ : syracuseStep 2008091 = 3012137) B3012137
theorem B13379519 : Blo 694316 13379519 := bstep (se 1 (by rfl) ⟨10034639, by rfl⟩ : syracuseStep 13379519 = 20069279) B20069279
theorem B1586411 : Blo 694316 1586411 := bstep (se 1 (by rfl) ⟨1189808, by rfl⟩ : syracuseStep 1586411 = 2379617) B2379617
theorem B7911107 : Blo 694316 7911107 := bstep (se 1 (by rfl) ⟨5933330, by rfl⟩ : syracuseStep 7911107 = 11866661) B11866661
theorem B32983037 : Blo 694316 32983037 := bstep (se 3 (by rfl) ⟨6184319, by rfl⟩ : syracuseStep 32983037 = 12368639) B12368639
theorem B5950007 : Blo 694316 5950007 := bstep (se 1 (by rfl) ⟨4462505, by rfl⟩ : syracuseStep 5950007 = 8925011) B8925011
theorem B1563191 : Blo 694316 1563191 := bstep (se 1 (by rfl) ⟨1172393, by rfl⟩ : syracuseStep 1563191 = 2344787) B2344787
theorem B1041887 : Blo 694316 1041887 := bstep (se 1 (by rfl) ⟨781415, by rfl⟩ : syracuseStep 1041887 = 1562831) B1562831
theorem B1763977 : Blo 694316 1763977 := bstep (se 2 (by rfl) ⟨661491, by rfl⟩ : syracuseStep 1763977 = 1322983) B1322983
theorem B1272673 : Blo 694316 1272673 := bstep (se 2 (by rfl) ⟨477252, by rfl⟩ : syracuseStep 1272673 = 954505) B954505
theorem B783103 : Blo 694316 783103 := bstep (se 1 (by rfl) ⟨587327, by rfl⟩ : syracuseStep 783103 = 1174655) B1174655
theorem B7533593 : Blo 694316 7533593 := bstep (se 2 (by rfl) ⟨2825097, by rfl⟩ : syracuseStep 7533593 = 5650195) B5650195
theorem B1047335 : Blo 694316 1047335 := bstep (se 1 (by rfl) ⟨785501, by rfl⟩ : syracuseStep 1047335 = 1571003) B1571003
theorem B21988691 : Blo 694316 21988691 := bstep (se 1 (by rfl) ⟨16491518, by rfl⟩ : syracuseStep 21988691 = 32983037) B32983037
theorem B3966671 : Blo 694316 3966671 := bstep (se 1 (by rfl) ⟨2975003, by rfl⟩ : syracuseStep 3966671 = 5950007) B5950007
theorem B694591 : Blo 694316 694591 := bstep (se 1 (by rfl) ⟨520943, by rfl⟩ : syracuseStep 694591 = 1041887) B1041887
theorem B8919679 : Blo 694316 8919679 := bstep (se 1 (by rfl) ⟨6689759, by rfl⟩ : syracuseStep 8919679 = 13379519) B13379519
theorem B5022395 : Blo 694316 5022395 := bstep (se 1 (by rfl) ⟨3766796, by rfl⟩ : syracuseStep 5022395 = 7533593) B7533593
theorem B1057607 : Blo 694316 1057607 := bstep (se 1 (by rfl) ⟨793205, by rfl⟩ : syracuseStep 1057607 = 1586411) B1586411
theorem B698223 : Blo 694316 698223 := bstep (se 1 (by rfl) ⟨523667, by rfl⟩ : syracuseStep 698223 = 1047335) B1047335
theorem B5724371 : Blo 694316 5724371 := bstep (se 1 (by rfl) ⟨4293278, by rfl⟩ : syracuseStep 5724371 = 8586557) B8586557
theorem B2351969 : Blo 694316 2351969 := bstep (se 2 (by rfl) ⟨881988, by rfl⟩ : syracuseStep 2351969 = 1763977) B1763977
theorem B1696897 : Blo 694316 1696897 := bstep (se 2 (by rfl) ⟨636336, by rfl⟩ : syracuseStep 1696897 = 1272673) B1272673
theorem B2975039 : Blo 694316 2975039 := bstep (se 1 (by rfl) ⟨2231279, by rfl⟩ : syracuseStep 2975039 = 4462559) B4462559
theorem B1042127 : Blo 694316 1042127 := bstep (se 1 (by rfl) ⟨781595, by rfl⟩ : syracuseStep 1042127 = 1563191) B1563191
theorem B879103 : Blo 694316 879103 := bstep (se 1 (by rfl) ⟨659327, by rfl⟩ : syracuseStep 879103 = 1318655) B1318655
theorem B1338727 : Blo 694316 1338727 := bstep (se 1 (by rfl) ⟨1004045, by rfl⟩ : syracuseStep 1338727 = 2008091) B2008091
theorem B1044137 : Blo 694316 1044137 := bstep (se 2 (by rfl) ⟨391551, by rfl⟩ : syracuseStep 1044137 = 783103) B783103
theorem B5274071 : Blo 694316 5274071 := bstep (se 1 (by rfl) ⟨3955553, by rfl⟩ : syracuseStep 5274071 = 7911107) B7911107
theorem B2262529 : Blo 694316 2262529 := bstep (se 2 (by rfl) ⟨848448, by rfl⟩ : syracuseStep 2262529 = 1696897) B1696897
theorem B3348263 : Blo 694316 3348263 := bstep (se 1 (by rfl) ⟨2511197, by rfl⟩ : syracuseStep 3348263 = 5022395) B5022395
theorem B694751 : Blo 694316 694751 := bstep (se 1 (by rfl) ⟨521063, by rfl⟩ : syracuseStep 694751 = 1042127) B1042127
theorem B696091 : Blo 694316 696091 := bstep (se 1 (by rfl) ⟨522068, by rfl⟩ : syracuseStep 696091 = 1044137) B1044137
theorem B3516047 : Blo 694316 3516047 := bstep (se 1 (by rfl) ⟨2637035, by rfl⟩ : syracuseStep 3516047 = 5274071) B5274071
theorem B14659127 : Blo 694316 14659127 := bstep (se 1 (by rfl) ⟨10994345, by rfl⟩ : syracuseStep 14659127 = 21988691) B21988691
theorem B3816247 : Blo 694316 3816247 := bstep (se 1 (by rfl) ⟨2862185, by rfl⟩ : syracuseStep 3816247 = 5724371) B5724371
theorem B1784969 : Blo 694316 1784969 := bstep (se 2 (by rfl) ⟨669363, by rfl⟩ : syracuseStep 1784969 = 1338727) B1338727
theorem B705071 : Blo 694316 705071 := bstep (se 1 (by rfl) ⟨528803, by rfl⟩ : syracuseStep 705071 = 1057607) B1057607
theorem B1983359 : Blo 694316 1983359 := bstep (se 1 (by rfl) ⟨1487519, by rfl⟩ : syracuseStep 1983359 = 2975039) B2975039
theorem B2644447 : Blo 694316 2644447 := bstep (se 1 (by rfl) ⟨1983335, by rfl⟩ : syracuseStep 2644447 = 3966671) B3966671
theorem B1172137 : Blo 694316 1172137 := bstep (se 2 (by rfl) ⟨439551, by rfl⟩ : syracuseStep 1172137 = 879103) B879103
theorem B1567979 : Blo 694316 1567979 := bstep (se 1 (by rfl) ⟨1175984, by rfl⟩ : syracuseStep 1567979 = 2351969) B2351969
theorem B11892905 : Blo 694316 11892905 := bstep (se 2 (by rfl) ⟨4459839, by rfl⟩ : syracuseStep 11892905 = 8919679) B8919679
theorem B3016705 : Blo 694316 3016705 := bstep (se 2 (by rfl) ⟨1131264, by rfl⟩ : syracuseStep 3016705 = 2262529) B2262529
theorem B9772751 : Blo 694316 9772751 := bstep (se 1 (by rfl) ⟨7329563, by rfl⟩ : syracuseStep 9772751 = 14659127) B14659127
theorem B5088329 : Blo 694316 5088329 := bstep (se 2 (by rfl) ⟨1908123, by rfl⟩ : syracuseStep 5088329 = 3816247) B3816247
theorem B1189979 : Blo 694316 1189979 := bstep (se 1 (by rfl) ⟨892484, by rfl⟩ : syracuseStep 1189979 = 1784969) B1784969
theorem B1322239 : Blo 694316 1322239 := bstep (se 1 (by rfl) ⟨991679, by rfl⟩ : syracuseStep 1322239 = 1983359) B1983359
theorem B1880189 : Blo 694316 1880189 := bstep (se 3 (by rfl) ⟨352535, by rfl⟩ : syracuseStep 1880189 = 705071) B705071
theorem B8928701 : Blo 694316 8928701 := bstep (se 3 (by rfl) ⟨1674131, by rfl⟩ : syracuseStep 8928701 = 3348263) B3348263
theorem B2344031 : Blo 694316 2344031 := bstep (se 1 (by rfl) ⟨1758023, by rfl⟩ : syracuseStep 2344031 = 3516047) B3516047
theorem B3525929 : Blo 694316 3525929 := bstep (se 2 (by rfl) ⟨1322223, by rfl⟩ : syracuseStep 3525929 = 2644447) B2644447
theorem B1562849 : Blo 694316 1562849 := bstep (se 2 (by rfl) ⟨586068, by rfl⟩ : syracuseStep 1562849 = 1172137) B1172137
theorem B1045319 : Blo 694316 1045319 := bstep (se 1 (by rfl) ⟨783989, by rfl⟩ : syracuseStep 1045319 = 1567979) B1567979
theorem B7928603 : Blo 694316 7928603 := bstep (se 1 (by rfl) ⟨5946452, by rfl⟩ : syracuseStep 7928603 = 11892905) B11892905
theorem B793319 : Blo 694316 793319 := bstep (se 1 (by rfl) ⟨594989, by rfl⟩ : syracuseStep 793319 = 1189979) B1189979
theorem B1253459 : Blo 694316 1253459 := bstep (se 1 (by rfl) ⟨940094, by rfl⟩ : syracuseStep 1253459 = 1880189) B1880189
theorem B696879 : Blo 694316 696879 := bstep (se 1 (by rfl) ⟨522659, by rfl⟩ : syracuseStep 696879 = 1045319) B1045319
theorem B5285735 : Blo 694316 5285735 := bstep (se 1 (by rfl) ⟨3964301, by rfl⟩ : syracuseStep 5285735 = 7928603) B7928603
theorem B26060669 : Blo 694316 26060669 := bstep (se 3 (by rfl) ⟨4886375, by rfl⟩ : syracuseStep 26060669 = 9772751) B9772751
theorem B3392219 : Blo 694316 3392219 := bstep (se 1 (by rfl) ⟨2544164, by rfl⟩ : syracuseStep 3392219 = 5088329) B5088329
theorem B5952467 : Blo 694316 5952467 := bstep (se 1 (by rfl) ⟨4464350, by rfl⟩ : syracuseStep 5952467 = 8928701) B8928701
theorem B1562687 : Blo 694316 1562687 := bstep (se 1 (by rfl) ⟨1172015, by rfl⟩ : syracuseStep 1562687 = 2344031) B2344031
theorem B2350619 : Blo 694316 2350619 := bstep (se 1 (by rfl) ⟨1762964, by rfl⟩ : syracuseStep 2350619 = 3525929) B3525929
theorem B4022273 : Blo 694316 4022273 := bstep (se 2 (by rfl) ⟨1508352, by rfl⟩ : syracuseStep 4022273 = 3016705) B3016705
theorem B1041899 : Blo 694316 1041899 := bstep (se 1 (by rfl) ⟨781424, by rfl⟩ : syracuseStep 1041899 = 1562849) B1562849
theorem B1762985 : Blo 694316 1762985 := bstep (se 2 (by rfl) ⟨661119, by rfl⟩ : syracuseStep 1762985 = 1322239) B1322239
theorem B2261479 : Blo 694316 2261479 := bstep (se 1 (by rfl) ⟨1696109, by rfl⟩ : syracuseStep 2261479 = 3392219) B3392219
theorem B3968311 : Blo 694316 3968311 := bstep (se 1 (by rfl) ⟨2976233, by rfl⟩ : syracuseStep 3968311 = 5952467) B5952467
theorem B694599 : Blo 694316 694599 := bstep (se 1 (by rfl) ⟨520949, by rfl⟩ : syracuseStep 694599 = 1041899) B1041899
theorem B17373779 : Blo 694316 17373779 := bstep (se 1 (by rfl) ⟨13030334, by rfl⟩ : syracuseStep 17373779 = 26060669) B26060669
theorem B835639 : Blo 694316 835639 := bstep (se 1 (by rfl) ⟨626729, by rfl⟩ : syracuseStep 835639 = 1253459) B1253459
theorem B3523823 : Blo 694316 3523823 := bstep (se 1 (by rfl) ⟨2642867, by rfl⟩ : syracuseStep 3523823 = 5285735) B5285735
theorem B2115517 : Blo 694316 2115517 := bstep (se 3 (by rfl) ⟨396659, by rfl⟩ : syracuseStep 2115517 = 793319) B793319
theorem B1041791 : Blo 694316 1041791 := bstep (se 1 (by rfl) ⟨781343, by rfl⟩ : syracuseStep 1041791 = 1562687) B1562687
theorem B1567079 : Blo 694316 1567079 := bstep (se 1 (by rfl) ⟨1175309, by rfl⟩ : syracuseStep 1567079 = 2350619) B2350619
theorem B2681515 : Blo 694316 2681515 := bstep (se 1 (by rfl) ⟨2011136, by rfl⟩ : syracuseStep 2681515 = 4022273) B4022273
theorem B1175323 : Blo 694316 1175323 := bstep (se 1 (by rfl) ⟨881492, by rfl⟩ : syracuseStep 1175323 = 1762985) B1762985
theorem B4456741 : Blo 694316 4456741 := bstep (se 4 (by rfl) ⟨417819, by rfl⟩ : syracuseStep 4456741 = 835639) B835639
theorem B3015305 : Blo 694316 3015305 := bstep (se 2 (by rfl) ⟨1130739, by rfl⟩ : syracuseStep 3015305 = 2261479) B2261479
theorem B2820689 : Blo 694316 2820689 := bstep (se 2 (by rfl) ⟨1057758, by rfl⟩ : syracuseStep 2820689 = 2115517) B2115517
theorem B3575353 : Blo 694316 3575353 := bstep (se 2 (by rfl) ⟨1340757, by rfl⟩ : syracuseStep 3575353 = 2681515) B2681515
theorem B694527 : Blo 694316 694527 := bstep (se 1 (by rfl) ⟨520895, by rfl⟩ : syracuseStep 694527 = 1041791) B1041791
theorem B11582519 : Blo 694316 11582519 := bstep (se 1 (by rfl) ⟨8686889, by rfl⟩ : syracuseStep 11582519 = 17373779) B17373779
theorem B5291081 : Blo 694316 5291081 := bstep (se 2 (by rfl) ⟨1984155, by rfl⟩ : syracuseStep 5291081 = 3968311) B3968311
theorem B2349215 : Blo 694316 2349215 := bstep (se 1 (by rfl) ⟨1761911, by rfl⟩ : syracuseStep 2349215 = 3523823) B3523823
theorem B1567097 : Blo 694316 1567097 := bstep (se 2 (by rfl) ⟨587661, by rfl⟩ : syracuseStep 1567097 = 1175323) B1175323
theorem B1044719 : Blo 694316 1044719 := bstep (se 1 (by rfl) ⟨783539, by rfl⟩ : syracuseStep 1044719 = 1567079) B1567079
theorem B696479 : Blo 694316 696479 := bstep (se 1 (by rfl) ⟨522359, by rfl⟩ : syracuseStep 696479 = 1044719) B1044719
theorem B5942321 : Blo 694316 5942321 := bstep (se 2 (by rfl) ⟨2228370, by rfl⟩ : syracuseStep 5942321 = 4456741) B4456741
theorem B2010203 : Blo 694316 2010203 := bstep (se 1 (by rfl) ⟨1507652, by rfl⟩ : syracuseStep 2010203 = 3015305) B3015305
theorem B123546869 : Blo 694316 123546869 := bstep (se 5 (by rfl) ⟨5791259, by rfl⟩ : syracuseStep 123546869 = 11582519) B11582519
theorem B1880459 : Blo 694316 1880459 := bstep (se 1 (by rfl) ⟨1410344, by rfl⟩ : syracuseStep 1880459 = 2820689) B2820689
theorem B4767137 : Blo 694316 4767137 := bstep (se 2 (by rfl) ⟨1787676, by rfl⟩ : syracuseStep 4767137 = 3575353) B3575353
theorem B3527387 : Blo 694316 3527387 := bstep (se 1 (by rfl) ⟨2645540, by rfl⟩ : syracuseStep 3527387 = 5291081) B5291081
theorem B1566143 : Blo 694316 1566143 := bstep (se 1 (by rfl) ⟨1174607, by rfl⟩ : syracuseStep 1566143 = 2349215) B2349215
theorem B1044731 : Blo 694316 1044731 := bstep (se 1 (by rfl) ⟨783548, by rfl⟩ : syracuseStep 1044731 = 1567097) B1567097
theorem B696487 : Blo 694316 696487 := bstep (se 1 (by rfl) ⟨522365, by rfl⟩ : syracuseStep 696487 = 1044731) B1044731
theorem B1253639 : Blo 694316 1253639 := bstep (se 1 (by rfl) ⟨940229, by rfl⟩ : syracuseStep 1253639 = 1880459) B1880459
theorem B82364579 : Blo 694316 82364579 := bstep (se 1 (by rfl) ⟨61773434, by rfl⟩ : syracuseStep 82364579 = 123546869) B123546869
theorem B2351591 : Blo 694316 2351591 := bstep (se 1 (by rfl) ⟨1763693, by rfl⟩ : syracuseStep 2351591 = 3527387) B3527387
theorem B1044095 : Blo 694316 1044095 := bstep (se 1 (by rfl) ⟨783071, by rfl⟩ : syracuseStep 1044095 = 1566143) B1566143
theorem B3961547 : Blo 694316 3961547 := bstep (se 1 (by rfl) ⟨2971160, by rfl⟩ : syracuseStep 3961547 = 5942321) B5942321
theorem B1340135 : Blo 694316 1340135 := bstep (se 1 (by rfl) ⟨1005101, by rfl⟩ : syracuseStep 1340135 = 2010203) B2010203
theorem B3178091 : Blo 694316 3178091 := bstep (se 1 (by rfl) ⟨2383568, by rfl⟩ : syracuseStep 3178091 = 4767137) B4767137
theorem B696063 : Blo 694316 696063 := bstep (se 1 (by rfl) ⟨522047, by rfl⟩ : syracuseStep 696063 = 1044095) B1044095
theorem B893423 : Blo 694316 893423 := bstep (se 1 (by rfl) ⟨670067, by rfl⟩ : syracuseStep 893423 = 1340135) B1340135
theorem B835759 : Blo 694316 835759 := bstep (se 1 (by rfl) ⟨626819, by rfl⟩ : syracuseStep 835759 = 1253639) B1253639
theorem B2641031 : Blo 694316 2641031 := bstep (se 1 (by rfl) ⟨1980773, by rfl⟩ : syracuseStep 2641031 = 3961547) B3961547
theorem B2118727 : Blo 694316 2118727 := bstep (se 1 (by rfl) ⟨1589045, by rfl⟩ : syracuseStep 2118727 = 3178091) B3178091
theorem B54909719 : Blo 694316 54909719 := bstep (se 1 (by rfl) ⟨41182289, by rfl⟩ : syracuseStep 54909719 = 82364579) B82364579
theorem B1567727 : Blo 694316 1567727 := bstep (se 1 (by rfl) ⟨1175795, by rfl⟩ : syracuseStep 1567727 = 2351591) B2351591
theorem B1114345 : Blo 694316 1114345 := bstep (se 2 (by rfl) ⟨417879, by rfl⟩ : syracuseStep 1114345 = 835759) B835759
theorem B36606479 : Blo 694316 36606479 := bstep (se 1 (by rfl) ⟨27454859, by rfl⟩ : syracuseStep 36606479 = 54909719) B54909719
theorem B2824969 : Blo 694316 2824969 := bstep (se 2 (by rfl) ⟨1059363, by rfl⟩ : syracuseStep 2824969 = 2118727) B2118727
theorem B2382461 : Blo 694316 2382461 := bstep (se 3 (by rfl) ⟨446711, by rfl⟩ : syracuseStep 2382461 = 893423) B893423
theorem B1760687 : Blo 694316 1760687 := bstep (se 1 (by rfl) ⟨1320515, by rfl⟩ : syracuseStep 1760687 = 2641031) B2641031
theorem B1045151 : Blo 694316 1045151 := bstep (se 1 (by rfl) ⟨783863, by rfl⟩ : syracuseStep 1045151 = 1567727) B1567727
theorem B97617277 : Blo 694316 97617277 := bstep (se 3 (by rfl) ⟨18303239, by rfl⟩ : syracuseStep 97617277 = 36606479) B36606479
theorem B696767 : Blo 694316 696767 := bstep (se 1 (by rfl) ⟨522575, by rfl⟩ : syracuseStep 696767 = 1045151) B1045151
theorem B1485793 : Blo 694316 1485793 := bstep (se 2 (by rfl) ⟨557172, by rfl⟩ : syracuseStep 1485793 = 1114345) B1114345
theorem B1588307 : Blo 694316 1588307 := bstep (se 1 (by rfl) ⟨1191230, by rfl⟩ : syracuseStep 1588307 = 2382461) B2382461
theorem B1173791 : Blo 694316 1173791 := bstep (se 1 (by rfl) ⟨880343, by rfl⟩ : syracuseStep 1173791 = 1760687) B1760687
theorem B3766625 : Blo 694316 3766625 := bstep (se 2 (by rfl) ⟨1412484, by rfl⟩ : syracuseStep 3766625 = 2824969) B2824969
theorem B520625477 : Blo 694316 520625477 := bstep (se 4 (by rfl) ⟨48808638, by rfl⟩ : syracuseStep 520625477 = 97617277) B97617277
theorem B4235485 : Blo 694316 4235485 := bstep (se 3 (by rfl) ⟨794153, by rfl⟩ : syracuseStep 4235485 = 1588307) B1588307
theorem B2511083 : Blo 694316 2511083 := bstep (se 1 (by rfl) ⟨1883312, by rfl⟩ : syracuseStep 2511083 = 3766625) B3766625
theorem B7924229 : Blo 694316 7924229 := bstep (se 4 (by rfl) ⟨742896, by rfl⟩ : syracuseStep 7924229 = 1485793) B1485793
theorem B782527 : Blo 694316 782527 := bstep (se 1 (by rfl) ⟨586895, by rfl⟩ : syracuseStep 782527 = 1173791) B1173791
theorem B1674055 : Blo 694316 1674055 := bstep (se 1 (by rfl) ⟨1255541, by rfl⟩ : syracuseStep 1674055 = 2511083) B2511083
theorem B347083651 : Blo 694316 347083651 := bstep (se 1 (by rfl) ⟨260312738, by rfl⟩ : syracuseStep 347083651 = 520625477) B520625477
theorem B5282819 : Blo 694316 5282819 := bstep (se 1 (by rfl) ⟨3962114, by rfl⟩ : syracuseStep 5282819 = 7924229) B7924229
theorem B5647313 : Blo 694316 5647313 := bstep (se 2 (by rfl) ⟨2117742, by rfl⟩ : syracuseStep 5647313 = 4235485) B4235485
theorem B1043369 : Blo 694316 1043369 := bstep (se 2 (by rfl) ⟨391263, by rfl⟩ : syracuseStep 1043369 = 782527) B782527
theorem B2232073 : Blo 694316 2232073 := bstep (se 2 (by rfl) ⟨837027, by rfl⟩ : syracuseStep 2232073 = 1674055) B1674055
theorem B695579 : Blo 694316 695579 := bstep (se 1 (by rfl) ⟨521684, by rfl⟩ : syracuseStep 695579 = 1043369) B1043369
theorem B3521879 : Blo 694316 3521879 := bstep (se 1 (by rfl) ⟨2641409, by rfl⟩ : syracuseStep 3521879 = 5282819) B5282819
theorem B462778201 : Blo 694316 462778201 := bstep (se 2 (by rfl) ⟨173541825, by rfl⟩ : syracuseStep 462778201 = 347083651) B347083651
theorem B3764875 : Blo 694316 3764875 := bstep (se 1 (by rfl) ⟨2823656, by rfl⟩ : syracuseStep 3764875 = 5647313) B5647313
theorem B5019833 : Blo 694316 5019833 := bstep (se 2 (by rfl) ⟨1882437, by rfl⟩ : syracuseStep 5019833 = 3764875) B3764875
theorem B617037601 : Blo 694316 617037601 := bstep (se 2 (by rfl) ⟨231389100, by rfl⟩ : syracuseStep 617037601 = 462778201) B462778201
theorem B2347919 : Blo 694316 2347919 := bstep (se 1 (by rfl) ⟨1760939, by rfl⟩ : syracuseStep 2347919 = 3521879) B3521879
theorem B2976097 : Blo 694316 2976097 := bstep (se 2 (by rfl) ⟨1116036, by rfl⟩ : syracuseStep 2976097 = 2232073) B2232073
theorem B3968129 : Blo 694316 3968129 := bstep (se 2 (by rfl) ⟨1488048, by rfl⟩ : syracuseStep 3968129 = 2976097) B2976097
theorem B3346555 : Blo 694316 3346555 := bstep (se 1 (by rfl) ⟨2509916, by rfl⟩ : syracuseStep 3346555 = 5019833) B5019833
theorem B822716801 : Blo 694316 822716801 := bstep (se 2 (by rfl) ⟨308518800, by rfl⟩ : syracuseStep 822716801 = 617037601) B617037601
theorem B1565279 : Blo 694316 1565279 := bstep (se 1 (by rfl) ⟨1173959, by rfl⟩ : syracuseStep 1565279 = 2347919) B2347919
theorem B4462073 : Blo 694316 4462073 := bstep (se 2 (by rfl) ⟨1673277, by rfl⟩ : syracuseStep 4462073 = 3346555) B3346555
theorem B548477867 : Blo 694316 548477867 := bstep (se 1 (by rfl) ⟨411358400, by rfl⟩ : syracuseStep 548477867 = 822716801) B822716801
theorem B2645419 : Blo 694316 2645419 := bstep (se 1 (by rfl) ⟨1984064, by rfl⟩ : syracuseStep 2645419 = 3968129) B3968129
theorem B1043519 : Blo 694316 1043519 := bstep (se 1 (by rfl) ⟨782639, by rfl⟩ : syracuseStep 1043519 = 1565279) B1565279
theorem B695679 : Blo 694316 695679 := bstep (se 1 (by rfl) ⟨521759, by rfl⟩ : syracuseStep 695679 = 1043519) B1043519
theorem B3527225 : Blo 694316 3527225 := bstep (se 2 (by rfl) ⟨1322709, by rfl⟩ : syracuseStep 3527225 = 2645419) B2645419
theorem B2974715 : Blo 694316 2974715 := bstep (se 1 (by rfl) ⟨2231036, by rfl⟩ : syracuseStep 2974715 = 4462073) B4462073
theorem B365651911 : Blo 694316 365651911 := bstep (se 1 (by rfl) ⟨274238933, by rfl⟩ : syracuseStep 365651911 = 548477867) B548477867
theorem B487535881 : Blo 694316 487535881 := bstep (se 2 (by rfl) ⟨182825955, by rfl⟩ : syracuseStep 487535881 = 365651911) B365651911
theorem B1983143 : Blo 694316 1983143 := bstep (se 1 (by rfl) ⟨1487357, by rfl⟩ : syracuseStep 1983143 = 2974715) B2974715
theorem B2351483 : Blo 694316 2351483 := bstep (se 1 (by rfl) ⟨1763612, by rfl⟩ : syracuseStep 2351483 = 3527225) B3527225
theorem B1322095 : Blo 694316 1322095 := bstep (se 1 (by rfl) ⟨991571, by rfl⟩ : syracuseStep 1322095 = 1983143) B1983143
theorem B1567655 : Blo 694316 1567655 := bstep (se 1 (by rfl) ⟨1175741, by rfl⟩ : syracuseStep 1567655 = 2351483) B2351483
theorem B650047841 : Blo 694316 650047841 := bstep (se 2 (by rfl) ⟨243767940, by rfl⟩ : syracuseStep 650047841 = 487535881) B487535881
theorem B433365227 : Blo 694316 433365227 := bstep (se 1 (by rfl) ⟨325023920, by rfl⟩ : syracuseStep 433365227 = 650047841) B650047841
theorem B1762793 : Blo 694316 1762793 := bstep (se 2 (by rfl) ⟨661047, by rfl⟩ : syracuseStep 1762793 = 1322095) B1322095
theorem B1045103 : Blo 694316 1045103 := bstep (se 1 (by rfl) ⟨783827, by rfl⟩ : syracuseStep 1045103 = 1567655) B1567655
theorem B696735 : Blo 694316 696735 := bstep (se 1 (by rfl) ⟨522551, by rfl⟩ : syracuseStep 696735 = 1045103) B1045103
theorem B288910151 : Blo 694316 288910151 := bstep (se 1 (by rfl) ⟨216682613, by rfl⟩ : syracuseStep 288910151 = 433365227) B433365227
theorem B1175195 : Blo 694316 1175195 := bstep (se 1 (by rfl) ⟨881396, by rfl⟩ : syracuseStep 1175195 = 1762793) B1762793
theorem B192606767 : Blo 694316 192606767 := bstep (se 1 (by rfl) ⟨144455075, by rfl⟩ : syracuseStep 192606767 = 288910151) B288910151
theorem B783463 : Blo 694316 783463 := bstep (se 1 (by rfl) ⟨587597, by rfl⟩ : syracuseStep 783463 = 1175195) B1175195
theorem B128404511 : Blo 694316 128404511 := bstep (se 1 (by rfl) ⟨96303383, by rfl⟩ : syracuseStep 128404511 = 192606767) B192606767
theorem B1044617 : Blo 694316 1044617 := bstep (se 2 (by rfl) ⟨391731, by rfl⟩ : syracuseStep 1044617 = 783463) B783463
theorem B696411 : Blo 694316 696411 := bstep (se 1 (by rfl) ⟨522308, by rfl⟩ : syracuseStep 696411 = 1044617) B1044617
theorem B85603007 : Blo 694316 85603007 := bstep (se 1 (by rfl) ⟨64202255, by rfl⟩ : syracuseStep 85603007 = 128404511) B128404511
theorem B57068671 : Blo 694316 57068671 := bstep (se 1 (by rfl) ⟨42801503, by rfl⟩ : syracuseStep 57068671 = 85603007) B85603007
theorem B76091561 : Blo 694316 76091561 := bstep (se 2 (by rfl) ⟨28534335, by rfl⟩ : syracuseStep 76091561 = 57068671) B57068671
theorem B50727707 : Blo 694316 50727707 := bstep (se 1 (by rfl) ⟨38045780, by rfl⟩ : syracuseStep 50727707 = 76091561) B76091561
theorem B33818471 : Blo 694316 33818471 := bstep (se 1 (by rfl) ⟨25363853, by rfl⟩ : syracuseStep 33818471 = 50727707) B50727707
theorem B22545647 : Blo 694316 22545647 := bstep (se 1 (by rfl) ⟨16909235, by rfl⟩ : syracuseStep 22545647 = 33818471) B33818471
theorem B15030431 : Blo 694316 15030431 := bstep (se 1 (by rfl) ⟨11272823, by rfl⟩ : syracuseStep 15030431 = 22545647) B22545647
theorem B10020287 : Blo 694316 10020287 := bstep (se 1 (by rfl) ⟨7515215, by rfl⟩ : syracuseStep 10020287 = 15030431) B15030431
theorem B6680191 : Blo 694316 6680191 := bstep (se 1 (by rfl) ⟨5010143, by rfl⟩ : syracuseStep 6680191 = 10020287) B10020287
theorem B8906921 : Blo 694316 8906921 := bstep (se 2 (by rfl) ⟨3340095, by rfl⟩ : syracuseStep 8906921 = 6680191) B6680191
theorem B5937947 : Blo 694316 5937947 := bstep (se 1 (by rfl) ⟨4453460, by rfl⟩ : syracuseStep 5937947 = 8906921) B8906921
theorem B3958631 : Blo 694316 3958631 := bstep (se 1 (by rfl) ⟨2968973, by rfl⟩ : syracuseStep 3958631 = 5937947) B5937947
theorem B2639087 : Blo 694316 2639087 := bstep (se 1 (by rfl) ⟨1979315, by rfl⟩ : syracuseStep 2639087 = 3958631) B3958631
theorem B1759391 : Blo 694316 1759391 := bstep (se 1 (by rfl) ⟨1319543, by rfl⟩ : syracuseStep 1759391 = 2639087) B2639087
theorem B1172927 : Blo 694316 1172927 := bstep (se 1 (by rfl) ⟨879695, by rfl⟩ : syracuseStep 1172927 = 1759391) B1759391
theorem B781951 : Blo 694316 781951 := bstep (se 1 (by rfl) ⟨586463, by rfl⟩ : syracuseStep 781951 = 1172927) B1172927
theorem B1042601 : Blo 694316 1042601 := bstep (se 2 (by rfl) ⟨390975, by rfl⟩ : syracuseStep 1042601 = 781951) B781951
theorem B695067 : Blo 694316 695067 := bstep (se 1 (by rfl) ⟨521300, by rfl⟩ : syracuseStep 695067 = 1042601) B1042601

theorem C0 (j : ℕ) (h1 : 173579 ≤ j) (h2 : j ≤ 174278) : Blo 694316 (4 * j + 3) := by
  interval_cases j
  · exact B694319
  · exact B694323
  · exact B694327
  · exact B694331
  · exact B694335
  · exact B694339
  · exact B694343
  · exact B694347
  · exact B694351
  · exact B694355
  · exact B694359
  · exact B694363
  · exact B694367
  · exact B694371
  · exact B694375
  · exact B694379
  · exact B694383
  · exact B694387
  · exact B694391
  · exact B694395
  · exact B694399
  · exact B694403
  · exact B694407
  · exact B694411
  · exact B694415
  · exact B694419
  · exact B694423
  · exact B694427
  · exact B694431
  · exact B694435
  · exact B694439
  · exact B694443
  · exact B694447
  · exact B694451
  · exact B694455
  · exact B694459
  · exact B694463
  · exact B694467
  · exact B694471
  · exact B694475
  · exact B694479
  · exact B694483
  · exact B694487
  · exact B694491
  · exact B694495
  · exact B694499
  · exact B694503
  · exact B694507
  · exact B694511
  · exact B694515
  · exact B694519
  · exact B694523
  · exact B694527
  · exact B694531
  · exact B694535
  · exact B694539
  · exact B694543
  · exact B694547
  · exact B694551
  · exact B694555
  · exact B694559
  · exact B694563
  · exact B694567
  · exact B694571
  · exact B694575
  · exact B694579
  · exact B694583
  · exact B694587
  · exact B694591
  · exact B694595
  · exact B694599
  · exact B694603
  · exact B694607
  · exact B694611
  · exact B694615
  · exact B694619
  · exact B694623
  · exact B694627
  · exact B694631
  · exact B694635
  · exact B694639
  · exact B694643
  · exact B694647
  · exact B694651
  · exact B694655
  · exact B694659
  · exact B694663
  · exact B694667
  · exact B694671
  · exact B694675
  · exact B694679
  · exact B694683
  · exact B694687
  · exact B694691
  · exact B694695
  · exact B694699
  · exact B694703
  · exact B694707
  · exact B694711
  · exact B694715
  · exact B694719
  · exact B694723
  · exact B694727
  · exact B694731
  · exact B694735
  · exact B694739
  · exact B694743
  · exact B694747
  · exact B694751
  · exact B694755
  · exact B694759
  · exact B694763
  · exact B694767
  · exact B694771
  · exact B694775
  · exact B694779
  · exact B694783
  · exact B694787
  · exact B694791
  · exact B694795
  · exact B694799
  · exact B694803
  · exact B694807
  · exact B694811
  · exact B694815
  · exact B694819
  · exact B694823
  · exact B694827
  · exact B694831
  · exact B694835
  · exact B694839
  · exact B694843
  · exact B694847
  · exact B694851
  · exact B694855
  · exact B694859
  · exact B694863
  · exact B694867
  · exact B694871
  · exact B694875
  · exact B694879
  · exact B694883
  · exact B694887
  · exact B694891
  · exact B694895
  · exact B694899
  · exact B694903
  · exact B694907
  · exact B694911
  · exact B694915
  · exact B694919
  · exact B694923
  · exact B694927
  · exact B694931
  · exact B694935
  · exact B694939
  · exact B694943
  · exact B694947
  · exact B694951
  · exact B694955
  · exact B694959
  · exact B694963
  · exact B694967
  · exact B694971
  · exact B694975
  · exact B694979
  · exact B694983
  · exact B694987
  · exact B694991
  · exact B694995
  · exact B694999
  · exact B695003
  · exact B695007
  · exact B695011
  · exact B695015
  · exact B695019
  · exact B695023
  · exact B695027
  · exact B695031
  · exact B695035
  · exact B695039
  · exact B695043
  · exact B695047
  · exact B695051
  · exact B695055
  · exact B695059
  · exact B695063
  · exact B695067
  · exact B695071
  · exact B695075
  · exact B695079
  · exact B695083
  · exact B695087
  · exact B695091
  · exact B695095
  · exact B695099
  · exact B695103
  · exact B695107
  · exact B695111
  · exact B695115
  · exact B695119
  · exact B695123
  · exact B695127
  · exact B695131
  · exact B695135
  · exact B695139
  · exact B695143
  · exact B695147
  · exact B695151
  · exact B695155
  · exact B695159
  · exact B695163
  · exact B695167
  · exact B695171
  · exact B695175
  · exact B695179
  · exact B695183
  · exact B695187
  · exact B695191
  · exact B695195
  · exact B695199
  · exact B695203
  · exact B695207
  · exact B695211
  · exact B695215
  · exact B695219
  · exact B695223
  · exact B695227
  · exact B695231
  · exact B695235
  · exact B695239
  · exact B695243
  · exact B695247
  · exact B695251
  · exact B695255
  · exact B695259
  · exact B695263
  · exact B695267
  · exact B695271
  · exact B695275
  · exact B695279
  · exact B695283
  · exact B695287
  · exact B695291
  · exact B695295
  · exact B695299
  · exact B695303
  · exact B695307
  · exact B695311
  · exact B695315
  · exact B695319
  · exact B695323
  · exact B695327
  · exact B695331
  · exact B695335
  · exact B695339
  · exact B695343
  · exact B695347
  · exact B695351
  · exact B695355
  · exact B695359
  · exact B695363
  · exact B695367
  · exact B695371
  · exact B695375
  · exact B695379
  · exact B695383
  · exact B695387
  · exact B695391
  · exact B695395
  · exact B695399
  · exact B695403
  · exact B695407
  · exact B695411
  · exact B695415
  · exact B695419
  · exact B695423
  · exact B695427
  · exact B695431
  · exact B695435
  · exact B695439
  · exact B695443
  · exact B695447
  · exact B695451
  · exact B695455
  · exact B695459
  · exact B695463
  · exact B695467
  · exact B695471
  · exact B695475
  · exact B695479
  · exact B695483
  · exact B695487
  · exact B695491
  · exact B695495
  · exact B695499
  · exact B695503
  · exact B695507
  · exact B695511
  · exact B695515
  · exact B695519
  · exact B695523
  · exact B695527
  · exact B695531
  · exact B695535
  · exact B695539
  · exact B695543
  · exact B695547
  · exact B695551
  · exact B695555
  · exact B695559
  · exact B695563
  · exact B695567
  · exact B695571
  · exact B695575
  · exact B695579
  · exact B695583
  · exact B695587
  · exact B695591
  · exact B695595
  · exact B695599
  · exact B695603
  · exact B695607
  · exact B695611
  · exact B695615
  · exact B695619
  · exact B695623
  · exact B695627
  · exact B695631
  · exact B695635
  · exact B695639
  · exact B695643
  · exact B695647
  · exact B695651
  · exact B695655
  · exact B695659
  · exact B695663
  · exact B695667
  · exact B695671
  · exact B695675
  · exact B695679
  · exact B695683
  · exact B695687
  · exact B695691
  · exact B695695
  · exact B695699
  · exact B695703
  · exact B695707
  · exact B695711
  · exact B695715
  · exact B695719
  · exact B695723
  · exact B695727
  · exact B695731
  · exact B695735
  · exact B695739
  · exact B695743
  · exact B695747
  · exact B695751
  · exact B695755
  · exact B695759
  · exact B695763
  · exact B695767
  · exact B695771
  · exact B695775
  · exact B695779
  · exact B695783
  · exact B695787
  · exact B695791
  · exact B695795
  · exact B695799
  · exact B695803
  · exact B695807
  · exact B695811
  · exact B695815
  · exact B695819
  · exact B695823
  · exact B695827
  · exact B695831
  · exact B695835
  · exact B695839
  · exact B695843
  · exact B695847
  · exact B695851
  · exact B695855
  · exact B695859
  · exact B695863
  · exact B695867
  · exact B695871
  · exact B695875
  · exact B695879
  · exact B695883
  · exact B695887
  · exact B695891
  · exact B695895
  · exact B695899
  · exact B695903
  · exact B695907
  · exact B695911
  · exact B695915
  · exact B695919
  · exact B695923
  · exact B695927
  · exact B695931
  · exact B695935
  · exact B695939
  · exact B695943
  · exact B695947
  · exact B695951
  · exact B695955
  · exact B695959
  · exact B695963
  · exact B695967
  · exact B695971
  · exact B695975
  · exact B695979
  · exact B695983
  · exact B695987
  · exact B695991
  · exact B695995
  · exact B695999
  · exact B696003
  · exact B696007
  · exact B696011
  · exact B696015
  · exact B696019
  · exact B696023
  · exact B696027
  · exact B696031
  · exact B696035
  · exact B696039
  · exact B696043
  · exact B696047
  · exact B696051
  · exact B696055
  · exact B696059
  · exact B696063
  · exact B696067
  · exact B696071
  · exact B696075
  · exact B696079
  · exact B696083
  · exact B696087
  · exact B696091
  · exact B696095
  · exact B696099
  · exact B696103
  · exact B696107
  · exact B696111
  · exact B696115
  · exact B696119
  · exact B696123
  · exact B696127
  · exact B696131
  · exact B696135
  · exact B696139
  · exact B696143
  · exact B696147
  · exact B696151
  · exact B696155
  · exact B696159
  · exact B696163
  · exact B696167
  · exact B696171
  · exact B696175
  · exact B696179
  · exact B696183
  · exact B696187
  · exact B696191
  · exact B696195
  · exact B696199
  · exact B696203
  · exact B696207
  · exact B696211
  · exact B696215
  · exact B696219
  · exact B696223
  · exact B696227
  · exact B696231
  · exact B696235
  · exact B696239
  · exact B696243
  · exact B696247
  · exact B696251
  · exact B696255
  · exact B696259
  · exact B696263
  · exact B696267
  · exact B696271
  · exact B696275
  · exact B696279
  · exact B696283
  · exact B696287
  · exact B696291
  · exact B696295
  · exact B696299
  · exact B696303
  · exact B696307
  · exact B696311
  · exact B696315
  · exact B696319
  · exact B696323
  · exact B696327
  · exact B696331
  · exact B696335
  · exact B696339
  · exact B696343
  · exact B696347
  · exact B696351
  · exact B696355
  · exact B696359
  · exact B696363
  · exact B696367
  · exact B696371
  · exact B696375
  · exact B696379
  · exact B696383
  · exact B696387
  · exact B696391
  · exact B696395
  · exact B696399
  · exact B696403
  · exact B696407
  · exact B696411
  · exact B696415
  · exact B696419
  · exact B696423
  · exact B696427
  · exact B696431
  · exact B696435
  · exact B696439
  · exact B696443
  · exact B696447
  · exact B696451
  · exact B696455
  · exact B696459
  · exact B696463
  · exact B696467
  · exact B696471
  · exact B696475
  · exact B696479
  · exact B696483
  · exact B696487
  · exact B696491
  · exact B696495
  · exact B696499
  · exact B696503
  · exact B696507
  · exact B696511
  · exact B696515
  · exact B696519
  · exact B696523
  · exact B696527
  · exact B696531
  · exact B696535
  · exact B696539
  · exact B696543
  · exact B696547
  · exact B696551
  · exact B696555
  · exact B696559
  · exact B696563
  · exact B696567
  · exact B696571
  · exact B696575
  · exact B696579
  · exact B696583
  · exact B696587
  · exact B696591
  · exact B696595
  · exact B696599
  · exact B696603
  · exact B696607
  · exact B696611
  · exact B696615
  · exact B696619
  · exact B696623
  · exact B696627
  · exact B696631
  · exact B696635
  · exact B696639
  · exact B696643
  · exact B696647
  · exact B696651
  · exact B696655
  · exact B696659
  · exact B696663
  · exact B696667
  · exact B696671
  · exact B696675
  · exact B696679
  · exact B696683
  · exact B696687
  · exact B696691
  · exact B696695
  · exact B696699
  · exact B696703
  · exact B696707
  · exact B696711
  · exact B696715
  · exact B696719
  · exact B696723
  · exact B696727
  · exact B696731
  · exact B696735
  · exact B696739
  · exact B696743
  · exact B696747
  · exact B696751
  · exact B696755
  · exact B696759
  · exact B696763
  · exact B696767
  · exact B696771
  · exact B696775
  · exact B696779
  · exact B696783
  · exact B696787
  · exact B696791
  · exact B696795
  · exact B696799
  · exact B696803
  · exact B696807
  · exact B696811
  · exact B696815
  · exact B696819
  · exact B696823
  · exact B696827
  · exact B696831
  · exact B696835
  · exact B696839
  · exact B696843
  · exact B696847
  · exact B696851
  · exact B696855
  · exact B696859
  · exact B696863
  · exact B696867
  · exact B696871
  · exact B696875
  · exact B696879
  · exact B696883
  · exact B696887
  · exact B696891
  · exact B696895
  · exact B696899
  · exact B696903
  · exact B696907
  · exact B696911
  · exact B696915
  · exact B696919
  · exact B696923
  · exact B696927
  · exact B696931
  · exact B696935
  · exact B696939
  · exact B696943
  · exact B696947
  · exact B696951
  · exact B696955
  · exact B696959
  · exact B696963
  · exact B696967
  · exact B696971
  · exact B696975
  · exact B696979
  · exact B696983
  · exact B696987
  · exact B696991
  · exact B696995
  · exact B696999
  · exact B697003
  · exact B697007
  · exact B697011
  · exact B697015
  · exact B697019
  · exact B697023
  · exact B697027
  · exact B697031
  · exact B697035
  · exact B697039
  · exact B697043
  · exact B697047
  · exact B697051
  · exact B697055
  · exact B697059
  · exact B697063
  · exact B697067
  · exact B697071
  · exact B697075
  · exact B697079
  · exact B697083
  · exact B697087
  · exact B697091
  · exact B697095
  · exact B697099
  · exact B697103
  · exact B697107
  · exact B697111
  · exact B697115

theorem C1 (j : ℕ) (h1 : 174279 ≤ j) (h2 : j ≤ 174578) : Blo 694316 (4 * j + 3) := by
  interval_cases j
  · exact B697119
  · exact B697123
  · exact B697127
  · exact B697131
  · exact B697135
  · exact B697139
  · exact B697143
  · exact B697147
  · exact B697151
  · exact B697155
  · exact B697159
  · exact B697163
  · exact B697167
  · exact B697171
  · exact B697175
  · exact B697179
  · exact B697183
  · exact B697187
  · exact B697191
  · exact B697195
  · exact B697199
  · exact B697203
  · exact B697207
  · exact B697211
  · exact B697215
  · exact B697219
  · exact B697223
  · exact B697227
  · exact B697231
  · exact B697235
  · exact B697239
  · exact B697243
  · exact B697247
  · exact B697251
  · exact B697255
  · exact B697259
  · exact B697263
  · exact B697267
  · exact B697271
  · exact B697275
  · exact B697279
  · exact B697283
  · exact B697287
  · exact B697291
  · exact B697295
  · exact B697299
  · exact B697303
  · exact B697307
  · exact B697311
  · exact B697315
  · exact B697319
  · exact B697323
  · exact B697327
  · exact B697331
  · exact B697335
  · exact B697339
  · exact B697343
  · exact B697347
  · exact B697351
  · exact B697355
  · exact B697359
  · exact B697363
  · exact B697367
  · exact B697371
  · exact B697375
  · exact B697379
  · exact B697383
  · exact B697387
  · exact B697391
  · exact B697395
  · exact B697399
  · exact B697403
  · exact B697407
  · exact B697411
  · exact B697415
  · exact B697419
  · exact B697423
  · exact B697427
  · exact B697431
  · exact B697435
  · exact B697439
  · exact B697443
  · exact B697447
  · exact B697451
  · exact B697455
  · exact B697459
  · exact B697463
  · exact B697467
  · exact B697471
  · exact B697475
  · exact B697479
  · exact B697483
  · exact B697487
  · exact B697491
  · exact B697495
  · exact B697499
  · exact B697503
  · exact B697507
  · exact B697511
  · exact B697515
  · exact B697519
  · exact B697523
  · exact B697527
  · exact B697531
  · exact B697535
  · exact B697539
  · exact B697543
  · exact B697547
  · exact B697551
  · exact B697555
  · exact B697559
  · exact B697563
  · exact B697567
  · exact B697571
  · exact B697575
  · exact B697579
  · exact B697583
  · exact B697587
  · exact B697591
  · exact B697595
  · exact B697599
  · exact B697603
  · exact B697607
  · exact B697611
  · exact B697615
  · exact B697619
  · exact B697623
  · exact B697627
  · exact B697631
  · exact B697635
  · exact B697639
  · exact B697643
  · exact B697647
  · exact B697651
  · exact B697655
  · exact B697659
  · exact B697663
  · exact B697667
  · exact B697671
  · exact B697675
  · exact B697679
  · exact B697683
  · exact B697687
  · exact B697691
  · exact B697695
  · exact B697699
  · exact B697703
  · exact B697707
  · exact B697711
  · exact B697715
  · exact B697719
  · exact B697723
  · exact B697727
  · exact B697731
  · exact B697735
  · exact B697739
  · exact B697743
  · exact B697747
  · exact B697751
  · exact B697755
  · exact B697759
  · exact B697763
  · exact B697767
  · exact B697771
  · exact B697775
  · exact B697779
  · exact B697783
  · exact B697787
  · exact B697791
  · exact B697795
  · exact B697799
  · exact B697803
  · exact B697807
  · exact B697811
  · exact B697815
  · exact B697819
  · exact B697823
  · exact B697827
  · exact B697831
  · exact B697835
  · exact B697839
  · exact B697843
  · exact B697847
  · exact B697851
  · exact B697855
  · exact B697859
  · exact B697863
  · exact B697867
  · exact B697871
  · exact B697875
  · exact B697879
  · exact B697883
  · exact B697887
  · exact B697891
  · exact B697895
  · exact B697899
  · exact B697903
  · exact B697907
  · exact B697911
  · exact B697915
  · exact B697919
  · exact B697923
  · exact B697927
  · exact B697931
  · exact B697935
  · exact B697939
  · exact B697943
  · exact B697947
  · exact B697951
  · exact B697955
  · exact B697959
  · exact B697963
  · exact B697967
  · exact B697971
  · exact B697975
  · exact B697979
  · exact B697983
  · exact B697987
  · exact B697991
  · exact B697995
  · exact B697999
  · exact B698003
  · exact B698007
  · exact B698011
  · exact B698015
  · exact B698019
  · exact B698023
  · exact B698027
  · exact B698031
  · exact B698035
  · exact B698039
  · exact B698043
  · exact B698047
  · exact B698051
  · exact B698055
  · exact B698059
  · exact B698063
  · exact B698067
  · exact B698071
  · exact B698075
  · exact B698079
  · exact B698083
  · exact B698087
  · exact B698091
  · exact B698095
  · exact B698099
  · exact B698103
  · exact B698107
  · exact B698111
  · exact B698115
  · exact B698119
  · exact B698123
  · exact B698127
  · exact B698131
  · exact B698135
  · exact B698139
  · exact B698143
  · exact B698147
  · exact B698151
  · exact B698155
  · exact B698159
  · exact B698163
  · exact B698167
  · exact B698171
  · exact B698175
  · exact B698179
  · exact B698183
  · exact B698187
  · exact B698191
  · exact B698195
  · exact B698199
  · exact B698203
  · exact B698207
  · exact B698211
  · exact B698215
  · exact B698219
  · exact B698223
  · exact B698227
  · exact B698231
  · exact B698235
  · exact B698239
  · exact B698243
  · exact B698247
  · exact B698251
  · exact B698255
  · exact B698259
  · exact B698263
  · exact B698267
  · exact B698271
  · exact B698275
  · exact B698279
  · exact B698283
  · exact B698287
  · exact B698291
  · exact B698295
  · exact B698299
  · exact B698303
  · exact B698307
  · exact B698311
  · exact B698315

theorem solution (m : ℕ) (hlo : 694316 ≤ m) (hhi : m ≤ 698316) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 173579 ≤ j := by omega
    have hj2 : j ≤ 174578 := by omega
    have hb : Blo 694316 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 174279 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
