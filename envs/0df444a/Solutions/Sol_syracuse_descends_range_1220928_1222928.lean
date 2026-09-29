-- Prove2me | solution 1 for syracuse_descends_range_1220928_1222928
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:57.583513+00:00
-- url     : https://prove2.me/submissions/672ec1e7-8ea1-4dee-bf81-542f5f05463d

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


theorem B9273365 : Blo 1220928 9273365 := bbase (se 6 (by rfl) ⟨217344, by rfl⟩ : syracuseStep 9273365 = 434689) (by norm_num)
theorem B2318357 : Blo 1220928 2318357 := bbase (se 6 (by rfl) ⟨54336, by rfl⟩ : syracuseStep 2318357 = 108673) (by norm_num)
theorem B6184997 : Blo 1220928 6184997 := bbase (se 4 (by rfl) ⟨579843, by rfl⟩ : syracuseStep 6184997 = 1159687) (by norm_num)
theorem B2785373 : Blo 1220928 2785373 := bbase (se 3 (by rfl) ⟨522257, by rfl⟩ : syracuseStep 2785373 = 1044515) (by norm_num)
theorem B1982581 : Blo 1220928 1982581 := bbase (se 5 (by rfl) ⟨92933, by rfl⟩ : syracuseStep 1982581 = 185867) (by norm_num)
theorem B6963317 : Blo 1220928 6963317 := bbase (se 5 (by rfl) ⟨326405, by rfl⟩ : syracuseStep 6963317 = 652811) (by norm_num)
theorem B2384005 : Blo 1220928 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B6955253 : Blo 1220928 6955253 := bbase (se 5 (by rfl) ⟨326027, by rfl⟩ : syracuseStep 6955253 = 652055) (by norm_num)
theorem B3916021 : Blo 1220928 3916021 := bbase (se 5 (by rfl) ⟨183563, by rfl⟩ : syracuseStep 3916021 = 367127) (by norm_num)
theorem B2351381 : Blo 1220928 2351381 := bbase (se 6 (by rfl) ⟨55110, by rfl⟩ : syracuseStep 2351381 = 110221) (by norm_num)
theorem B1958165 : Blo 1220928 1958165 := bbase (se 6 (by rfl) ⟨45894, by rfl⟩ : syracuseStep 1958165 = 91789) (by norm_num)
theorem B1696037 : Blo 1220928 1696037 := bbase (se 4 (by rfl) ⟨159003, by rfl⟩ : syracuseStep 1696037 = 318007) (by norm_num)
theorem B2318645 : Blo 1220928 2318645 := bbase (se 5 (by rfl) ⟨108686, by rfl⟩ : syracuseStep 2318645 = 217373) (by norm_num)
theorem B1958197 : Blo 1220928 1958197 := bbase (se 5 (by rfl) ⟨91790, by rfl⟩ : syracuseStep 1958197 = 183581) (by norm_num)
theorem B4120901 : Blo 1220928 4120901 := bbase (se 4 (by rfl) ⟨386334, by rfl⟩ : syracuseStep 4120901 = 772669) (by norm_num)
theorem B5218661 : Blo 1220928 5218661 := bbase (se 4 (by rfl) ⟨489249, by rfl⟩ : syracuseStep 5218661 = 978499) (by norm_num)
theorem B17629589 : Blo 1220928 17629589 := bbase (se 6 (by rfl) ⟨413193, by rfl⟩ : syracuseStep 17629589 = 826387) (by norm_num)
theorem B2318797 : Blo 1220928 2318797 := bbase (se 3 (by rfl) ⟨434774, by rfl⟩ : syracuseStep 2318797 = 869549) (by norm_num)
theorem B2089469 : Blo 1220928 2089469 := bbase (se 3 (by rfl) ⟨391775, by rfl⟩ : syracuseStep 2089469 = 783551) (by norm_num)
theorem B3482149 : Blo 1220928 3482149 := bbase (se 4 (by rfl) ⟨326451, by rfl⟩ : syracuseStep 3482149 = 652903) (by norm_num)
theorem B5218901 : Blo 1220928 5218901 := bbase (se 8 (by rfl) ⟨30579, by rfl⟩ : syracuseStep 5218901 = 61159) (by norm_num)
theorem B1983101 : Blo 1220928 1983101 := bbase (se 3 (by rfl) ⟨371831, by rfl⟩ : syracuseStep 1983101 = 743663) (by norm_num)
theorem B4121333 : Blo 1220928 4121333 := bbase (se 5 (by rfl) ⟨193187, by rfl⟩ : syracuseStep 4121333 = 386375) (by norm_num)
theorem B2319101 : Blo 1220928 2319101 := bbase (se 3 (by rfl) ⟨434831, by rfl⟩ : syracuseStep 2319101 = 869663) (by norm_num)
theorem B8356661 : Blo 1220928 8356661 := bbase (se 5 (by rfl) ⟨391718, by rfl⟩ : syracuseStep 8356661 = 783437) (by norm_num)
theorem B1590085 : Blo 1220928 1590085 := bbase (se 4 (by rfl) ⟨149070, by rfl⟩ : syracuseStep 1590085 = 298141) (by norm_num)
theorem B6783925 : Blo 1220928 6783925 := bbase (se 5 (by rfl) ⟨317996, by rfl⟩ : syracuseStep 6783925 = 635993) (by norm_num)
theorem B1983413 : Blo 1220928 1983413 := bbase (se 5 (by rfl) ⟨92972, by rfl⟩ : syracuseStep 1983413 = 185945) (by norm_num)
theorem B2786341 : Blo 1220928 2786341 := bbase (se 4 (by rfl) ⟨261219, by rfl⟩ : syracuseStep 2786341 = 522439) (by norm_num)
theorem B2786413 : Blo 1220928 2786413 := bbase (se 3 (by rfl) ⟨522452, by rfl⟩ : syracuseStep 2786413 = 1044905) (by norm_num)
theorem B1393777 : Blo 1220928 1393777 := bbase (se 2 (by rfl) ⟨522666, by rfl⟩ : syracuseStep 1393777 = 1045333) (by norm_num)
theorem B4121765 : Blo 1220928 4121765 := bbase (se 4 (by rfl) ⟨386415, by rfl⟩ : syracuseStep 4121765 = 772831) (by norm_num)
theorem B2933941 : Blo 1220928 2933941 := bbase (se 5 (by rfl) ⟨137528, by rfl⟩ : syracuseStep 2933941 = 275057) (by norm_num)
theorem B1254637 : Blo 1220928 1254637 := bbase (se 3 (by rfl) ⟨235244, by rfl⟩ : syracuseStep 1254637 = 470489) (by norm_num)
theorem B1983725 : Blo 1220928 1983725 := bbase (se 3 (by rfl) ⟨371948, by rfl⟩ : syracuseStep 1983725 = 743897) (by norm_num)
theorem B6964501 : Blo 1220928 6964501 := bbase (se 6 (by rfl) ⟨163230, by rfl⟩ : syracuseStep 6964501 = 326461) (by norm_num)
theorem B4638005 : Blo 1220928 4638005 := bbase (se 5 (by rfl) ⟨217406, by rfl⟩ : syracuseStep 4638005 = 434813) (by norm_num)
theorem B6186293 : Blo 1220928 6186293 := bbase (se 5 (by rfl) ⟨289982, by rfl⟩ : syracuseStep 6186293 = 579965) (by norm_num)
theorem B1467725 : Blo 1220928 1467725 := bbase (se 3 (by rfl) ⟨275198, by rfl⟩ : syracuseStep 1467725 = 550397) (by norm_num)
theorem B4294085 : Blo 1220928 4294085 := bbase (se 4 (by rfl) ⟨402570, by rfl⟩ : syracuseStep 4294085 = 805141) (by norm_num)
theorem B8365525 : Blo 1220928 8365525 := bbase (se 7 (by rfl) ⟨98033, by rfl⟩ : syracuseStep 8365525 = 196067) (by norm_num)
theorem B1304029 : Blo 1220928 1304029 := bbase (se 3 (by rfl) ⟨244505, by rfl⟩ : syracuseStep 1304029 = 489011) (by norm_num)
theorem B1304033 : Blo 1220928 1304033 := bbase (se 2 (by rfl) ⟨489012, by rfl⟩ : syracuseStep 1304033 = 978025) (by norm_num)
theorem B2319853 : Blo 1220928 2319853 := bbase (se 3 (by rfl) ⟨434972, by rfl⟩ : syracuseStep 2319853 = 869945) (by norm_num)
theorem B1467893 : Blo 1220928 1467893 := bbase (se 5 (by rfl) ⟨68807, by rfl⟩ : syracuseStep 1467893 = 137615) (by norm_num)
theorem B12895733 : Blo 1220928 12895733 := bbase (se 5 (by rfl) ⟨604487, by rfl⟩ : syracuseStep 12895733 = 1208975) (by norm_num)
theorem B4122197 : Blo 1220928 4122197 := bbase (se 8 (by rfl) ⟨24153, by rfl⟩ : syracuseStep 4122197 = 48307) (by norm_num)
theorem B4638293 : Blo 1220928 4638293 := bbase (se 8 (by rfl) ⟨27177, by rfl⟩ : syracuseStep 4638293 = 54355) (by norm_num)
theorem B2319997 : Blo 1220928 2319997 := bbase (se 3 (by rfl) ⟨434999, by rfl⟩ : syracuseStep 2319997 = 869999) (by norm_num)
theorem B15656597 : Blo 1220928 15656597 := bbase (se 6 (by rfl) ⟨366951, by rfl⟩ : syracuseStep 15656597 = 733903) (by norm_num)
theorem B1238689 : Blo 1220928 1238689 := bbase (se 2 (by rfl) ⟨464508, by rfl⟩ : syracuseStep 1238689 = 929017) (by norm_num)
theorem B1566373 : Blo 1220928 1566373 := bbase (se 4 (by rfl) ⟨146847, by rfl⟩ : syracuseStep 1566373 = 293695) (by norm_num)
theorem B1394401 : Blo 1220928 1394401 := bbase (se 2 (by rfl) ⟨522900, by rfl⟩ : syracuseStep 1394401 = 1045801) (by norm_num)
theorem B2320157 : Blo 1220928 2320157 := bbase (se 3 (by rfl) ⟨435029, by rfl⟩ : syracuseStep 2320157 = 870059) (by norm_num)
theorem B1468201 : Blo 1220928 1468201 := bbase (se 2 (by rfl) ⟨550575, by rfl⟩ : syracuseStep 1468201 = 1101151) (by norm_num)
theorem B2934605 : Blo 1220928 2934605 := bbase (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) (by norm_num)
theorem B1738597 : Blo 1220928 1738597 := bbase (se 4 (by rfl) ⟨162993, by rfl⟩ : syracuseStep 1738597 = 325987) (by norm_num)
theorem B1812325 : Blo 1220928 1812325 := bbase (se 4 (by rfl) ⟨169905, by rfl⟩ : syracuseStep 1812325 = 339811) (by norm_num)
theorem B2320301 : Blo 1220928 2320301 := bbase (se 3 (by rfl) ⟨435056, by rfl⟩ : syracuseStep 2320301 = 870113) (by norm_num)
theorem B2787269 : Blo 1220928 2787269 := bbase (se 4 (by rfl) ⟨261306, by rfl⟩ : syracuseStep 2787269 = 522613) (by norm_num)
theorem B5875685 : Blo 1220928 5875685 := bbase (se 4 (by rfl) ⟨550845, by rfl⟩ : syracuseStep 5875685 = 1101691) (by norm_num)
theorem B1468417 : Blo 1220928 1468417 := bbase (se 2 (by rfl) ⟨550656, by rfl⟩ : syracuseStep 1468417 = 1101313) (by norm_num)
theorem B4122629 : Blo 1220928 4122629 := bbase (se 4 (by rfl) ⟨386496, by rfl⟩ : syracuseStep 4122629 = 772993) (by norm_num)
theorem B19810325 : Blo 1220928 19810325 := bbase (se 6 (by rfl) ⟨464304, by rfl⟩ : syracuseStep 19810325 = 928609) (by norm_num)
theorem B1304597 : Blo 1220928 1304597 := bbase (se 6 (by rfl) ⟨30576, by rfl⟩ : syracuseStep 1304597 = 61153) (by norm_num)
theorem B4958293 : Blo 1220928 4958293 := bbase (se 8 (by rfl) ⟨29052, by rfl⟩ : syracuseStep 4958293 = 58105) (by norm_num)
theorem B5875877 : Blo 1220928 5875877 := bbase (se 4 (by rfl) ⟨550863, by rfl⟩ : syracuseStep 5875877 = 1101727) (by norm_num)
theorem B2320589 : Blo 1220928 2320589 := bbase (se 3 (by rfl) ⟨435110, by rfl⟩ : syracuseStep 2320589 = 870221) (by norm_num)
theorem B1304785 : Blo 1220928 1304785 := bbase (se 2 (by rfl) ⟨489294, by rfl⟩ : syracuseStep 1304785 = 978589) (by norm_num)
theorem B1566977 : Blo 1220928 1566977 := bbase (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) (by norm_num)
theorem B1468729 : Blo 1220928 1468729 := bbase (se 2 (by rfl) ⟨550773, by rfl⟩ : syracuseStep 1468729 = 1101547) (by norm_num)
theorem B3090757 : Blo 1220928 3090757 := bbase (se 4 (by rfl) ⟨289758, by rfl⟩ : syracuseStep 3090757 = 579517) (by norm_num)
theorem B11151701 : Blo 1220928 11151701 := bbase (se 10 (by rfl) ⟨16335, by rfl⟩ : syracuseStep 11151701 = 32671) (by norm_num)
theorem B44607829 : Blo 1220928 44607829 := bbase (se 10 (by rfl) ⟨65343, by rfl⟩ : syracuseStep 44607829 = 130687) (by norm_num)
theorem B2320741 : Blo 1220928 2320741 := bbase (se 4 (by rfl) ⟨217569, by rfl⟩ : syracuseStep 2320741 = 435139) (by norm_num)
theorem B3090869 : Blo 1220928 3090869 := bbase (se 5 (by rfl) ⟨144884, by rfl⟩ : syracuseStep 3090869 = 289769) (by norm_num)
theorem B1739189 : Blo 1220928 1739189 := bbase (se 5 (by rfl) ⟨81524, by rfl⟩ : syracuseStep 1739189 = 163049) (by norm_num)
theorem B4123061 : Blo 1220928 4123061 := bbase (se 5 (by rfl) ⟨193268, by rfl⟩ : syracuseStep 4123061 = 386537) (by norm_num)
theorem B1739269 : Blo 1220928 1739269 := bbase (se 4 (by rfl) ⟨163056, by rfl⟩ : syracuseStep 1739269 = 326113) (by norm_num)
theorem B2091541 : Blo 1220928 2091541 := bbase (se 6 (by rfl) ⟨49020, by rfl⟩ : syracuseStep 2091541 = 98041) (by norm_num)
theorem B1272349 : Blo 1220928 1272349 := bbase (se 3 (by rfl) ⟨238565, by rfl⟩ : syracuseStep 1272349 = 477131) (by norm_num)
theorem B6187589 : Blo 1220928 6187589 := bbase (se 4 (by rfl) ⟨580086, by rfl⟩ : syracuseStep 6187589 = 1160173) (by norm_num)
theorem B3091061 : Blo 1220928 3091061 := bbase (se 5 (by rfl) ⟨144893, by rfl⟩ : syracuseStep 3091061 = 289787) (by norm_num)
theorem B1739389 : Blo 1220928 1739389 := bbase (se 3 (by rfl) ⟨326135, by rfl⟩ : syracuseStep 1739389 = 652271) (by norm_num)
theorem B2321045 : Blo 1220928 2321045 := bbase (se 6 (by rfl) ⟨54399, by rfl⟩ : syracuseStep 2321045 = 108799) (by norm_num)
theorem B1739485 : Blo 1220928 1739485 := bbase (se 3 (by rfl) ⟨326153, by rfl⟩ : syracuseStep 1739485 = 652307) (by norm_num)
theorem B3304165 : Blo 1220928 3304165 := bbase (se 4 (by rfl) ⟨309765, by rfl⟩ : syracuseStep 3304165 = 619531) (by norm_num)
theorem B4639477 : Blo 1220928 4639477 := bbase (se 5 (by rfl) ⟨217475, by rfl⟩ : syracuseStep 4639477 = 434951) (by norm_num)
theorem B2747141 : Blo 1220928 2747141 := bbase (se 4 (by rfl) ⟨257544, by rfl⟩ : syracuseStep 2747141 = 515089) (by norm_num)
theorem B5221189 : Blo 1220928 5221189 := bbase (se 4 (by rfl) ⟨489486, by rfl⟩ : syracuseStep 5221189 = 978973) (by norm_num)
theorem B2747213 : Blo 1220928 2747213 := bbase (se 3 (by rfl) ⟨515102, by rfl⟩ : syracuseStep 2747213 = 1030205) (by norm_num)
theorem B4402021 : Blo 1220928 4402021 := bbase (se 4 (by rfl) ⟨412689, by rfl⟩ : syracuseStep 4402021 = 825379) (by norm_num)
theorem B4123493 : Blo 1220928 4123493 := bbase (se 4 (by rfl) ⟨386577, by rfl⟩ : syracuseStep 4123493 = 773155) (by norm_num)
theorem B2747285 : Blo 1220928 2747285 := bbase (se 6 (by rfl) ⟨64389, by rfl⟩ : syracuseStep 2747285 = 128779) (by norm_num)
theorem B3091405 : Blo 1220928 3091405 := bbase (se 3 (by rfl) ⟨579638, by rfl⟩ : syracuseStep 3091405 = 1159277) (by norm_num)
theorem B2747357 : Blo 1220928 2747357 := bbase (se 3 (by rfl) ⟨515129, by rfl⟩ : syracuseStep 2747357 = 1030259) (by norm_num)
theorem B4402181 : Blo 1220928 4402181 := bbase (se 4 (by rfl) ⟨412704, by rfl⟩ : syracuseStep 4402181 = 825409) (by norm_num)
theorem B1305605 : Blo 1220928 1305605 := bbase (se 4 (by rfl) ⟨122400, by rfl⟩ : syracuseStep 1305605 = 244801) (by norm_num)
theorem B7826453 : Blo 1220928 7826453 := bbase (se 6 (by rfl) ⟨183432, by rfl⟩ : syracuseStep 7826453 = 366865) (by norm_num)
theorem B2747429 : Blo 1220928 2747429 := bbase (se 4 (by rfl) ⟨257571, by rfl⟩ : syracuseStep 2747429 = 515143) (by norm_num)
theorem B4639781 : Blo 1220928 4639781 := bbase (se 4 (by rfl) ⟨434979, by rfl⟩ : syracuseStep 4639781 = 869959) (by norm_num)
theorem B3091517 : Blo 1220928 3091517 := bbase (se 3 (by rfl) ⟨579659, by rfl⟩ : syracuseStep 3091517 = 1159319) (by norm_num)
theorem B2747501 : Blo 1220928 2747501 := bbase (se 3 (by rfl) ⟨515156, by rfl⟩ : syracuseStep 2747501 = 1030313) (by norm_num)
theorem B2608237 : Blo 1220928 2608237 := bbase (se 3 (by rfl) ⟨489044, by rfl⟩ : syracuseStep 2608237 = 978089) (by norm_num)
theorem B2747573 : Blo 1220928 2747573 := bbase (se 5 (by rfl) ⟨128792, by rfl⟩ : syracuseStep 2747573 = 257585) (by norm_num)
theorem B2935997 : Blo 1220928 2935997 := bbase (se 3 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 2935997 = 1100999) (by norm_num)
theorem B1674437 : Blo 1220928 1674437 := bbase (se 4 (by rfl) ⟨156978, by rfl⟩ : syracuseStep 1674437 = 313957) (by norm_num)
theorem B1739981 : Blo 1220928 1739981 := bbase (se 3 (by rfl) ⟨326246, by rfl⟩ : syracuseStep 1739981 = 652493) (by norm_num)
theorem B11144405 : Blo 1220928 11144405 := bbase (se 7 (by rfl) ⟨130598, by rfl⟩ : syracuseStep 11144405 = 261197) (by norm_num)
theorem B2608357 : Blo 1220928 2608357 := bbase (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) (by norm_num)
theorem B2747645 : Blo 1220928 2747645 := bbase (se 3 (by rfl) ⟨515183, by rfl⟩ : syracuseStep 2747645 = 1030367) (by norm_num)
theorem B3091709 : Blo 1220928 3091709 := bbase (se 3 (by rfl) ⟨579695, by rfl⟩ : syracuseStep 3091709 = 1159391) (by norm_num)
theorem B4123925 : Blo 1220928 4123925 := bbase (se 6 (by rfl) ⟨96654, by rfl⟩ : syracuseStep 4123925 = 193309) (by norm_num)
theorem B2936093 : Blo 1220928 2936093 := bbase (se 3 (by rfl) ⟨550517, by rfl⟩ : syracuseStep 2936093 = 1101035) (by norm_num)
theorem B2747717 : Blo 1220928 2747717 := bbase (se 4 (by rfl) ⟨257598, by rfl⟩ : syracuseStep 2747717 = 515197) (by norm_num)
theorem B2747789 : Blo 1220928 2747789 := bbase (se 3 (by rfl) ⟨515210, by rfl⟩ : syracuseStep 2747789 = 1030421) (by norm_num)
theorem B2747861 : Blo 1220928 2747861 := bbase (se 7 (by rfl) ⟨32201, by rfl⟩ : syracuseStep 2747861 = 64403) (by norm_num)
theorem B2608613 : Blo 1220928 2608613 := bbase (se 4 (by rfl) ⟨244557, by rfl⟩ : syracuseStep 2608613 = 489115) (by norm_num)
theorem B2747933 : Blo 1220928 2747933 := bbase (se 3 (by rfl) ⟨515237, by rfl⟩ : syracuseStep 2747933 = 1030475) (by norm_num)
theorem B3092053 : Blo 1220928 3092053 := bbase (se 8 (by rfl) ⟨18117, by rfl⟩ : syracuseStep 3092053 = 36235) (by norm_num)
theorem B2748005 : Blo 1220928 2748005 := bbase (se 4 (by rfl) ⟨257625, by rfl⟩ : syracuseStep 2748005 = 515251) (by norm_num)
theorem B2748077 : Blo 1220928 2748077 := bbase (se 3 (by rfl) ⟨515264, by rfl⟩ : syracuseStep 2748077 = 1030529) (by norm_num)
theorem B3092165 : Blo 1220928 3092165 := bbase (se 4 (by rfl) ⟨289890, by rfl⟩ : syracuseStep 3092165 = 579781) (by norm_num)
theorem B4124357 : Blo 1220928 4124357 := bbase (se 4 (by rfl) ⟨386658, by rfl⟩ : syracuseStep 4124357 = 773317) (by norm_num)
theorem B2748149 : Blo 1220928 2748149 := bbase (se 5 (by rfl) ⟨128819, by rfl⟩ : syracuseStep 2748149 = 257639) (by norm_num)
theorem B1740533 : Blo 1220928 1740533 := bbase (se 5 (by rfl) ⟨81587, by rfl⟩ : syracuseStep 1740533 = 163175) (by norm_num)
theorem B1568533 : Blo 1220928 1568533 := bbase (se 6 (by rfl) ⟨36762, by rfl⟩ : syracuseStep 1568533 = 73525) (by norm_num)
theorem B2748221 : Blo 1220928 2748221 := bbase (se 3 (by rfl) ⟨515291, by rfl⟩ : syracuseStep 2748221 = 1030583) (by norm_num)
theorem B6188885 : Blo 1220928 6188885 := bbase (se 9 (by rfl) ⟨18131, by rfl⟩ : syracuseStep 6188885 = 36263) (by norm_num)
theorem B2748293 : Blo 1220928 2748293 := bbase (se 4 (by rfl) ⟨257652, by rfl⟩ : syracuseStep 2748293 = 515305) (by norm_num)
theorem B3092357 : Blo 1220928 3092357 := bbase (se 4 (by rfl) ⟨289908, by rfl⟩ : syracuseStep 3092357 = 579817) (by norm_num)
theorem B2748365 : Blo 1220928 2748365 := bbase (se 3 (by rfl) ⟨515318, by rfl⟩ : syracuseStep 2748365 = 1030637) (by norm_num)
theorem B35229653 : Blo 1220928 35229653 := bbase (se 7 (by rfl) ⟨412847, by rfl⟩ : syracuseStep 35229653 = 825695) (by norm_num)
theorem B2748437 : Blo 1220928 2748437 := bbase (se 6 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 2748437 = 128833) (by norm_num)
theorem B2510909 : Blo 1220928 2510909 := bbase (se 3 (by rfl) ⟨470795, by rfl⟩ : syracuseStep 2510909 = 941591) (by norm_num)
theorem B2748509 : Blo 1220928 2748509 := bbase (se 3 (by rfl) ⟨515345, by rfl⟩ : syracuseStep 2748509 = 1030691) (by norm_num)
theorem B4124789 : Blo 1220928 4124789 := bbase (se 5 (by rfl) ⟨193349, by rfl⟩ : syracuseStep 4124789 = 386699) (by norm_num)
theorem B2060437 : Blo 1220928 2060437 := bbase (se 6 (by rfl) ⟨48291, by rfl⟩ : syracuseStep 2060437 = 96583) (by norm_num)
theorem B2748581 : Blo 1220928 2748581 := bbase (se 4 (by rfl) ⟨257679, by rfl⟩ : syracuseStep 2748581 = 515359) (by norm_num)
theorem B4526293 : Blo 1220928 4526293 := bbase (se 7 (by rfl) ⟨53042, by rfl⟩ : syracuseStep 4526293 = 106085) (by norm_num)
theorem B3092701 : Blo 1220928 3092701 := bbase (se 3 (by rfl) ⟨579881, by rfl⟩ : syracuseStep 3092701 = 1159763) (by norm_num)
theorem B4182245 : Blo 1220928 4182245 := bbase (se 4 (by rfl) ⟨392085, by rfl⟩ : syracuseStep 4182245 = 784171) (by norm_num)
theorem B2060525 : Blo 1220928 2060525 := bbase (se 3 (by rfl) ⟨386348, by rfl⟩ : syracuseStep 2060525 = 772697) (by norm_num)
theorem B2748653 : Blo 1220928 2748653 := bbase (se 3 (by rfl) ⟨515372, by rfl⟩ : syracuseStep 2748653 = 1030745) (by norm_num)
theorem B6181109 : Blo 1220928 6181109 := bbase (se 5 (by rfl) ⟨289739, by rfl⟩ : syracuseStep 6181109 = 579479) (by norm_num)
theorem B5222677 : Blo 1220928 5222677 := bbase (se 6 (by rfl) ⟨122406, by rfl⟩ : syracuseStep 5222677 = 244813) (by norm_num)
theorem B5222693 : Blo 1220928 5222693 := bbase (se 4 (by rfl) ⟨489627, by rfl⟩ : syracuseStep 5222693 = 979255) (by norm_num)
theorem B2748725 : Blo 1220928 2748725 := bbase (se 5 (by rfl) ⟨128846, by rfl⟩ : syracuseStep 2748725 = 257693) (by norm_num)
theorem B3092813 : Blo 1220928 3092813 := bbase (se 3 (by rfl) ⟨579902, by rfl⟩ : syracuseStep 3092813 = 1159805) (by norm_num)
theorem B2609501 : Blo 1220928 2609501 := bbase (se 3 (by rfl) ⟨489281, by rfl⟩ : syracuseStep 2609501 = 978563) (by norm_num)
theorem B1651045 : Blo 1220928 1651045 := bbase (se 4 (by rfl) ⟨154785, by rfl⟩ : syracuseStep 1651045 = 309571) (by norm_num)
theorem B2060653 : Blo 1220928 2060653 := bbase (se 3 (by rfl) ⟨386372, by rfl⟩ : syracuseStep 2060653 = 772745) (by norm_num)
theorem B2748797 : Blo 1220928 2748797 := bbase (se 3 (by rfl) ⟨515399, by rfl⟩ : syracuseStep 2748797 = 1030799) (by norm_num)
theorem B1651109 : Blo 1220928 1651109 := bbase (se 4 (by rfl) ⟨154791, by rfl⟩ : syracuseStep 1651109 = 309583) (by norm_num)
theorem B2060741 : Blo 1220928 2060741 := bbase (se 4 (by rfl) ⟨193194, by rfl⟩ : syracuseStep 2060741 = 386389) (by norm_num)
theorem B2748869 : Blo 1220928 2748869 := bbase (se 4 (by rfl) ⟨257706, by rfl⟩ : syracuseStep 2748869 = 515413) (by norm_num)
theorem B1831397 : Blo 1220928 1831397 := bbase (se 4 (by rfl) ⟨171693, by rfl⟩ : syracuseStep 1831397 = 343387) (by norm_num)
theorem B1831421 : Blo 1220928 1831421 := bbase (se 3 (by rfl) ⟨343391, by rfl⟩ : syracuseStep 1831421 = 686783) (by norm_num)
theorem B2748941 : Blo 1220928 2748941 := bbase (se 3 (by rfl) ⟨515426, by rfl⟩ : syracuseStep 2748941 = 1030853) (by norm_num)
theorem B3093005 : Blo 1220928 3093005 := bbase (se 3 (by rfl) ⟨579938, by rfl⟩ : syracuseStep 3093005 = 1159877) (by norm_num)
theorem B1831445 : Blo 1220928 1831445 := bbase (se 6 (by rfl) ⟨42924, by rfl⟩ : syracuseStep 1831445 = 85849) (by norm_num)
theorem B21172757 : Blo 1220928 21172757 := bbase (se 6 (by rfl) ⟨496236, by rfl⟩ : syracuseStep 21172757 = 992473) (by norm_num)
theorem B4125221 : Blo 1220928 4125221 := bbase (se 4 (by rfl) ⟨386739, by rfl⟩ : syracuseStep 4125221 = 773479) (by norm_num)
theorem B1831469 : Blo 1220928 1831469 := bbase (se 3 (by rfl) ⟨343400, by rfl⟩ : syracuseStep 1831469 = 686801) (by norm_num)
theorem B1831493 : Blo 1220928 1831493 := bbase (se 4 (by rfl) ⟨171702, by rfl⟩ : syracuseStep 1831493 = 343405) (by norm_num)
theorem B2060869 : Blo 1220928 2060869 := bbase (se 4 (by rfl) ⟨193206, by rfl⟩ : syracuseStep 2060869 = 386413) (by norm_num)
theorem B2609741 : Blo 1220928 2609741 := bbase (se 3 (by rfl) ⟨489326, by rfl⟩ : syracuseStep 2609741 = 978653) (by norm_num)
theorem B2749013 : Blo 1220928 2749013 := bbase (se 8 (by rfl) ⟨16107, by rfl⟩ : syracuseStep 2749013 = 32215) (by norm_num)
theorem B1831517 : Blo 1220928 1831517 := bbase (se 3 (by rfl) ⟨343409, by rfl⟩ : syracuseStep 1831517 = 686819) (by norm_num)
theorem B3912293 : Blo 1220928 3912293 := bbase (se 4 (by rfl) ⟨366777, by rfl⟩ : syracuseStep 3912293 = 733555) (by norm_num)
theorem B1831541 : Blo 1220928 1831541 := bbase (se 5 (by rfl) ⟨85853, by rfl⟩ : syracuseStep 1831541 = 171707) (by norm_num)
theorem B1831565 : Blo 1220928 1831565 := bbase (se 3 (by rfl) ⟨343418, by rfl⟩ : syracuseStep 1831565 = 686837) (by norm_num)
theorem B2060957 : Blo 1220928 2060957 := bbase (se 3 (by rfl) ⟨386429, by rfl⟩ : syracuseStep 2060957 = 772859) (by norm_num)
theorem B2749085 : Blo 1220928 2749085 := bbase (se 3 (by rfl) ⟨515453, by rfl⟩ : syracuseStep 2749085 = 1030907) (by norm_num)
theorem B1831589 : Blo 1220928 1831589 := bbase (se 4 (by rfl) ⟨171711, by rfl⟩ : syracuseStep 1831589 = 343423) (by norm_num)
theorem B1831613 : Blo 1220928 1831613 := bbase (se 3 (by rfl) ⟨343427, by rfl⟩ : syracuseStep 1831613 = 686855) (by norm_num)
theorem B1831637 : Blo 1220928 1831637 := bbase (se 7 (by rfl) ⟨21464, by rfl⟩ : syracuseStep 1831637 = 42929) (by norm_num)
theorem B2749157 : Blo 1220928 2749157 := bbase (se 4 (by rfl) ⟨257733, by rfl⟩ : syracuseStep 2749157 = 515467) (by norm_num)
theorem B1831661 : Blo 1220928 1831661 := bbase (se 3 (by rfl) ⟨343436, by rfl⟩ : syracuseStep 1831661 = 686873) (by norm_num)
theorem B1831685 : Blo 1220928 1831685 := bbase (se 4 (by rfl) ⟨171720, by rfl⟩ : syracuseStep 1831685 = 343441) (by norm_num)
theorem B1831709 : Blo 1220928 1831709 := bbase (se 3 (by rfl) ⟨343445, by rfl⟩ : syracuseStep 1831709 = 686891) (by norm_num)
theorem B2061085 : Blo 1220928 2061085 := bbase (se 3 (by rfl) ⟨386453, by rfl⟩ : syracuseStep 2061085 = 772907) (by norm_num)
theorem B2749229 : Blo 1220928 2749229 := bbase (se 3 (by rfl) ⟨515480, by rfl⟩ : syracuseStep 2749229 = 1030961) (by norm_num)
theorem B1831733 : Blo 1220928 1831733 := bbase (se 5 (by rfl) ⟨85862, by rfl⟩ : syracuseStep 1831733 = 171725) (by norm_num)
theorem B1831757 : Blo 1220928 1831757 := bbase (se 3 (by rfl) ⟨343454, by rfl⟩ : syracuseStep 1831757 = 686909) (by norm_num)
theorem B1831781 : Blo 1220928 1831781 := bbase (se 4 (by rfl) ⟨171729, by rfl⟩ : syracuseStep 1831781 = 343459) (by norm_num)
theorem B3093349 : Blo 1220928 3093349 := bbase (se 4 (by rfl) ⟨290001, by rfl⟩ : syracuseStep 3093349 = 580003) (by norm_num)
theorem B2061173 : Blo 1220928 2061173 := bbase (se 5 (by rfl) ⟨96617, by rfl⟩ : syracuseStep 2061173 = 193235) (by norm_num)
theorem B2749301 : Blo 1220928 2749301 := bbase (se 5 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 2749301 = 257747) (by norm_num)
theorem B1831805 : Blo 1220928 1831805 := bbase (se 3 (by rfl) ⟨343463, by rfl⟩ : syracuseStep 1831805 = 686927) (by norm_num)
theorem B1831829 : Blo 1220928 1831829 := bbase (se 6 (by rfl) ⟨42933, by rfl⟩ : syracuseStep 1831829 = 85867) (by norm_num)
theorem B1831853 : Blo 1220928 1831853 := bbase (se 3 (by rfl) ⟨343472, by rfl⟩ : syracuseStep 1831853 = 686945) (by norm_num)
theorem B2749373 : Blo 1220928 2749373 := bbase (se 3 (by rfl) ⟨515507, by rfl⟩ : syracuseStep 2749373 = 1031015) (by norm_num)
theorem B1831877 : Blo 1220928 1831877 := bbase (se 4 (by rfl) ⟨171738, by rfl⟩ : syracuseStep 1831877 = 343477) (by norm_num)
theorem B12530645 : Blo 1220928 12530645 := bbase (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) (by norm_num)
theorem B3093461 : Blo 1220928 3093461 := bbase (se 7 (by rfl) ⟨36251, by rfl⟩ : syracuseStep 3093461 = 72503) (by norm_num)
theorem B4125653 : Blo 1220928 4125653 := bbase (se 7 (by rfl) ⟨48347, by rfl⟩ : syracuseStep 4125653 = 96695) (by norm_num)
theorem B1831901 : Blo 1220928 1831901 := bbase (se 3 (by rfl) ⟨343481, by rfl⟩ : syracuseStep 1831901 = 686963) (by norm_num)
theorem B1831925 : Blo 1220928 1831925 := bbase (se 5 (by rfl) ⟨85871, by rfl⟩ : syracuseStep 1831925 = 171743) (by norm_num)
theorem B2061301 : Blo 1220928 2061301 := bbase (se 5 (by rfl) ⟨96623, by rfl⟩ : syracuseStep 2061301 = 193247) (by norm_num)
theorem B2749445 : Blo 1220928 2749445 := bbase (se 4 (by rfl) ⟨257760, by rfl⟩ : syracuseStep 2749445 = 515521) (by norm_num)
theorem B1856525 : Blo 1220928 1856525 := bbase (se 3 (by rfl) ⟨348098, by rfl⟩ : syracuseStep 1856525 = 696197) (by norm_num)
theorem B1831949 : Blo 1220928 1831949 := bbase (se 3 (by rfl) ⟨343490, by rfl⟩ : syracuseStep 1831949 = 686981) (by norm_num)
theorem B1831973 : Blo 1220928 1831973 := bbase (se 4 (by rfl) ⟨171747, by rfl⟩ : syracuseStep 1831973 = 343495) (by norm_num)
theorem B1545257 : Blo 1220928 1545257 := bbase (se 2 (by rfl) ⟨579471, by rfl⟩ : syracuseStep 1545257 = 1158943) (by norm_num)
theorem B1831997 : Blo 1220928 1831997 := bbase (se 3 (by rfl) ⟨343499, by rfl⟩ : syracuseStep 1831997 = 686999) (by norm_num)
theorem B2610245 : Blo 1220928 2610245 := bbase (se 4 (by rfl) ⟨244710, by rfl⟩ : syracuseStep 2610245 = 489421) (by norm_num)
theorem B2061389 : Blo 1220928 2061389 := bbase (se 3 (by rfl) ⟨386510, by rfl⟩ : syracuseStep 2061389 = 773021) (by norm_num)
theorem B2749517 : Blo 1220928 2749517 := bbase (se 3 (by rfl) ⟨515534, by rfl⟩ : syracuseStep 2749517 = 1031069) (by norm_num)
theorem B2610253 : Blo 1220928 2610253 := bbase (se 3 (by rfl) ⟨489422, by rfl⟩ : syracuseStep 2610253 = 978845) (by norm_num)
theorem B1832021 : Blo 1220928 1832021 := bbase (se 8 (by rfl) ⟨10734, by rfl⟩ : syracuseStep 1832021 = 21469) (by norm_num)
theorem B1545313 : Blo 1220928 1545313 := bbase (se 2 (by rfl) ⟨579492, by rfl⟩ : syracuseStep 1545313 = 1158985) (by norm_num)
theorem B4641893 : Blo 1220928 4641893 := bbase (se 4 (by rfl) ⟨435177, by rfl⟩ : syracuseStep 4641893 = 870355) (by norm_num)
theorem B6190181 : Blo 1220928 6190181 := bbase (se 4 (by rfl) ⟨580329, by rfl⟩ : syracuseStep 6190181 = 1160659) (by norm_num)
theorem B1832045 : Blo 1220928 1832045 := bbase (se 3 (by rfl) ⟨343508, by rfl⟩ : syracuseStep 1832045 = 687017) (by norm_num)
theorem B4404341 : Blo 1220928 4404341 := bbase (se 5 (by rfl) ⟨206453, by rfl⟩ : syracuseStep 4404341 = 412907) (by norm_num)
theorem B1832069 : Blo 1220928 1832069 := bbase (se 4 (by rfl) ⟨171756, by rfl⟩ : syracuseStep 1832069 = 343513) (by norm_num)
theorem B2749589 : Blo 1220928 2749589 := bbase (se 6 (by rfl) ⟨64443, by rfl⟩ : syracuseStep 2749589 = 128887) (by norm_num)
theorem B3093653 : Blo 1220928 3093653 := bbase (se 6 (by rfl) ⟨72507, by rfl⟩ : syracuseStep 3093653 = 145015) (by norm_num)
theorem B1832093 : Blo 1220928 1832093 := bbase (se 3 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 1832093 = 687035) (by norm_num)
theorem B1832117 : Blo 1220928 1832117 := bbase (se 5 (by rfl) ⟨85880, by rfl⟩ : syracuseStep 1832117 = 171761) (by norm_num)
theorem B1545409 : Blo 1220928 1545409 := bbase (se 2 (by rfl) ⟨579528, by rfl⟩ : syracuseStep 1545409 = 1159057) (by norm_num)
theorem B1832141 : Blo 1220928 1832141 := bbase (se 3 (by rfl) ⟨343526, by rfl⟩ : syracuseStep 1832141 = 687053) (by norm_num)
theorem B2061517 : Blo 1220928 2061517 := bbase (se 3 (by rfl) ⟨386534, by rfl⟩ : syracuseStep 2061517 = 773069) (by norm_num)
theorem B2749661 : Blo 1220928 2749661 := bbase (se 3 (by rfl) ⟨515561, by rfl⟩ : syracuseStep 2749661 = 1031123) (by norm_num)
theorem B1832165 : Blo 1220928 1832165 := bbase (se 4 (by rfl) ⟨171765, by rfl⟩ : syracuseStep 1832165 = 343531) (by norm_num)
theorem B1832189 : Blo 1220928 1832189 := bbase (se 3 (by rfl) ⟨343535, by rfl⟩ : syracuseStep 1832189 = 687071) (by norm_num)
theorem B1832213 : Blo 1220928 1832213 := bbase (se 6 (by rfl) ⟨42942, by rfl⟩ : syracuseStep 1832213 = 85885) (by norm_num)
theorem B2061605 : Blo 1220928 2061605 := bbase (se 4 (by rfl) ⟨193275, by rfl⟩ : syracuseStep 2061605 = 386551) (by norm_num)
theorem B2749733 : Blo 1220928 2749733 := bbase (se 4 (by rfl) ⟨257787, by rfl⟩ : syracuseStep 2749733 = 515575) (by norm_num)
theorem B1832237 : Blo 1220928 1832237 := bbase (se 3 (by rfl) ⟨343544, by rfl⟩ : syracuseStep 1832237 = 687089) (by norm_num)
theorem B1832261 : Blo 1220928 1832261 := bbase (se 4 (by rfl) ⟨171774, by rfl⟩ : syracuseStep 1832261 = 343549) (by norm_num)
theorem B2938189 : Blo 1220928 2938189 := bbase (se 3 (by rfl) ⟨550910, by rfl⟩ : syracuseStep 2938189 = 1101821) (by norm_num)
theorem B1832285 : Blo 1220928 1832285 := bbase (se 3 (by rfl) ⟨343553, by rfl⟩ : syracuseStep 1832285 = 687107) (by norm_num)
theorem B1545581 : Blo 1220928 1545581 := bbase (se 3 (by rfl) ⟨289796, by rfl⟩ : syracuseStep 1545581 = 579593) (by norm_num)
theorem B2749805 : Blo 1220928 2749805 := bbase (se 3 (by rfl) ⟨515588, by rfl⟩ : syracuseStep 2749805 = 1031177) (by norm_num)
theorem B1373557 : Blo 1220928 1373557 := bbase (se 5 (by rfl) ⟨64385, by rfl⟩ : syracuseStep 1373557 = 128771) (by norm_num)
theorem B1832309 : Blo 1220928 1832309 := bbase (se 5 (by rfl) ⟨85889, by rfl⟩ : syracuseStep 1832309 = 171779) (by norm_num)
theorem B4126085 : Blo 1220928 4126085 := bbase (se 4 (by rfl) ⟨386820, by rfl⟩ : syracuseStep 4126085 = 773641) (by norm_num)
theorem B4642181 : Blo 1220928 4642181 := bbase (se 4 (by rfl) ⟨435204, by rfl⟩ : syracuseStep 4642181 = 870409) (by norm_num)
theorem B1832333 : Blo 1220928 1832333 := bbase (se 3 (by rfl) ⟨343562, by rfl⟩ : syracuseStep 1832333 = 687125) (by norm_num)
theorem B1373593 : Blo 1220928 1373593 := bbase (se 2 (by rfl) ⟨515097, by rfl⟩ : syracuseStep 1373593 = 1030195) (by norm_num)
theorem B1545637 : Blo 1220928 1545637 := bbase (se 4 (by rfl) ⟨144903, by rfl⟩ : syracuseStep 1545637 = 289807) (by norm_num)
theorem B1832357 : Blo 1220928 1832357 := bbase (se 4 (by rfl) ⟨171783, by rfl⟩ : syracuseStep 1832357 = 343567) (by norm_num)
theorem B2061733 : Blo 1220928 2061733 := bbase (se 4 (by rfl) ⟨193287, by rfl⟩ : syracuseStep 2061733 = 386575) (by norm_num)
theorem B2749877 : Blo 1220928 2749877 := bbase (se 5 (by rfl) ⟨128900, by rfl⟩ : syracuseStep 2749877 = 257801) (by norm_num)
theorem B1373629 : Blo 1220928 1373629 := bbase (se 3 (by rfl) ⟨257555, by rfl⟩ : syracuseStep 1373629 = 515111) (by norm_num)
theorem B1832381 : Blo 1220928 1832381 := bbase (se 3 (by rfl) ⟨343571, by rfl⟩ : syracuseStep 1832381 = 687143) (by norm_num)
theorem B1832405 : Blo 1220928 1832405 := bbase (se 7 (by rfl) ⟨21473, by rfl⟩ : syracuseStep 1832405 = 42947) (by norm_num)
theorem B1373665 : Blo 1220928 1373665 := bbase (se 2 (by rfl) ⟨515124, by rfl⟩ : syracuseStep 1373665 = 1030249) (by norm_num)
theorem B1832429 : Blo 1220928 1832429 := bbase (se 3 (by rfl) ⟨343580, by rfl⟩ : syracuseStep 1832429 = 687161) (by norm_num)
theorem B3093997 : Blo 1220928 3093997 := bbase (se 3 (by rfl) ⟨580124, by rfl⟩ : syracuseStep 3093997 = 1160249) (by norm_num)
theorem B2061821 : Blo 1220928 2061821 := bbase (se 3 (by rfl) ⟨386591, by rfl⟩ : syracuseStep 2061821 = 773183) (by norm_num)
theorem B2749949 : Blo 1220928 2749949 := bbase (se 3 (by rfl) ⟨515615, by rfl⟩ : syracuseStep 2749949 = 1031231) (by norm_num)
theorem B1373701 : Blo 1220928 1373701 := bbase (se 4 (by rfl) ⟨128784, by rfl⟩ : syracuseStep 1373701 = 257569) (by norm_num)
theorem B6182405 : Blo 1220928 6182405 := bbase (se 4 (by rfl) ⟨579600, by rfl⟩ : syracuseStep 6182405 = 1159201) (by norm_num)
theorem B1545733 : Blo 1220928 1545733 := bbase (se 4 (by rfl) ⟨144912, by rfl⟩ : syracuseStep 1545733 = 289825) (by norm_num)
theorem B1832453 : Blo 1220928 1832453 := bbase (se 4 (by rfl) ⟨171792, by rfl⟩ : syracuseStep 1832453 = 343585) (by norm_num)
theorem B1832477 : Blo 1220928 1832477 := bbase (se 3 (by rfl) ⟨343589, by rfl⟩ : syracuseStep 1832477 = 687179) (by norm_num)
theorem B1373737 : Blo 1220928 1373737 := bbase (se 2 (by rfl) ⟨515151, by rfl⟩ : syracuseStep 1373737 = 1030303) (by norm_num)
theorem B1832501 : Blo 1220928 1832501 := bbase (se 5 (by rfl) ⟨85898, by rfl⟩ : syracuseStep 1832501 = 171797) (by norm_num)
theorem B2750021 : Blo 1220928 2750021 := bbase (se 4 (by rfl) ⟨257814, by rfl⟩ : syracuseStep 2750021 = 515629) (by norm_num)
theorem B1373773 : Blo 1220928 1373773 := bbase (se 3 (by rfl) ⟨257582, by rfl⟩ : syracuseStep 1373773 = 515165) (by norm_num)
theorem B1832525 : Blo 1220928 1832525 := bbase (se 3 (by rfl) ⟨343598, by rfl⟩ : syracuseStep 1832525 = 687197) (by norm_num)
theorem B3094109 : Blo 1220928 3094109 := bbase (se 3 (by rfl) ⟨580145, by rfl⟩ : syracuseStep 3094109 = 1160291) (by norm_num)
theorem B1832549 : Blo 1220928 1832549 := bbase (se 4 (by rfl) ⟨171801, by rfl⟩ : syracuseStep 1832549 = 343603) (by norm_num)
theorem B1373809 : Blo 1220928 1373809 := bbase (se 2 (by rfl) ⟨515178, by rfl⟩ : syracuseStep 1373809 = 1030357) (by norm_num)
theorem B1832573 : Blo 1220928 1832573 := bbase (se 3 (by rfl) ⟨343607, by rfl⟩ : syracuseStep 1832573 = 687215) (by norm_num)
theorem B2061949 : Blo 1220928 2061949 := bbase (se 3 (by rfl) ⟨386615, by rfl⟩ : syracuseStep 2061949 = 773231) (by norm_num)
theorem B2750093 : Blo 1220928 2750093 := bbase (se 3 (by rfl) ⟨515642, by rfl⟩ : syracuseStep 2750093 = 1031285) (by norm_num)
theorem B1373845 : Blo 1220928 1373845 := bbase (se 6 (by rfl) ⟨32199, by rfl⟩ : syracuseStep 1373845 = 64399) (by norm_num)
theorem B1832597 : Blo 1220928 1832597 := bbase (se 6 (by rfl) ⟨42951, by rfl⟩ : syracuseStep 1832597 = 85903) (by norm_num)
theorem B1832621 : Blo 1220928 1832621 := bbase (se 3 (by rfl) ⟨343616, by rfl⟩ : syracuseStep 1832621 = 687233) (by norm_num)
theorem B1545905 : Blo 1220928 1545905 := bbase (se 2 (by rfl) ⟨579714, by rfl⟩ : syracuseStep 1545905 = 1159429) (by norm_num)
theorem B1373881 : Blo 1220928 1373881 := bbase (se 2 (by rfl) ⟨515205, by rfl⟩ : syracuseStep 1373881 = 1030411) (by norm_num)
theorem B1832645 : Blo 1220928 1832645 := bbase (se 4 (by rfl) ⟨171810, by rfl⟩ : syracuseStep 1832645 = 343621) (by norm_num)
theorem B2062037 : Blo 1220928 2062037 := bbase (se 7 (by rfl) ⟨24164, by rfl⟩ : syracuseStep 2062037 = 48329) (by norm_num)
theorem B2750165 : Blo 1220928 2750165 := bbase (se 7 (by rfl) ⟨32228, by rfl⟩ : syracuseStep 2750165 = 64457) (by norm_num)
theorem B1373917 : Blo 1220928 1373917 := bbase (se 3 (by rfl) ⟨257609, by rfl⟩ : syracuseStep 1373917 = 515219) (by norm_num)
theorem B1832669 : Blo 1220928 1832669 := bbase (se 3 (by rfl) ⟨343625, by rfl⟩ : syracuseStep 1832669 = 687251) (by norm_num)
theorem B1545961 : Blo 1220928 1545961 := bbase (se 2 (by rfl) ⟨579735, by rfl⟩ : syracuseStep 1545961 = 1159471) (by norm_num)
theorem B1832693 : Blo 1220928 1832693 := bbase (se 5 (by rfl) ⟨85907, by rfl⟩ : syracuseStep 1832693 = 171815) (by norm_num)
theorem B1373953 : Blo 1220928 1373953 := bbase (se 2 (by rfl) ⟨515232, by rfl⟩ : syracuseStep 1373953 = 1030465) (by norm_num)
theorem B1832717 : Blo 1220928 1832717 := bbase (se 3 (by rfl) ⟨343634, by rfl⟩ : syracuseStep 1832717 = 687269) (by norm_num)
theorem B2750237 : Blo 1220928 2750237 := bbase (se 3 (by rfl) ⟨515669, by rfl⟩ : syracuseStep 2750237 = 1031339) (by norm_num)
theorem B3094301 : Blo 1220928 3094301 := bbase (se 3 (by rfl) ⟨580181, by rfl⟩ : syracuseStep 3094301 = 1160363) (by norm_num)
theorem B1373989 : Blo 1220928 1373989 := bbase (se 4 (by rfl) ⟨128811, by rfl⟩ : syracuseStep 1373989 = 257623) (by norm_num)
theorem B1832741 : Blo 1220928 1832741 := bbase (se 4 (by rfl) ⟨171819, by rfl⟩ : syracuseStep 1832741 = 343639) (by norm_num)
theorem B4126517 : Blo 1220928 4126517 := bbase (se 5 (by rfl) ⟨193430, by rfl⟩ : syracuseStep 4126517 = 386861) (by norm_num)
theorem B1832765 : Blo 1220928 1832765 := bbase (se 3 (by rfl) ⟨343643, by rfl⟩ : syracuseStep 1832765 = 687287) (by norm_num)
theorem B1374025 : Blo 1220928 1374025 := bbase (se 2 (by rfl) ⟨515259, by rfl⟩ : syracuseStep 1374025 = 1030519) (by norm_num)
theorem B1546057 : Blo 1220928 1546057 := bbase (se 2 (by rfl) ⟨579771, by rfl⟩ : syracuseStep 1546057 = 1159543) (by norm_num)
theorem B3479381 : Blo 1220928 3479381 := bbase (se 9 (by rfl) ⟨10193, by rfl⟩ : syracuseStep 3479381 = 20387) (by norm_num)
theorem B1832789 : Blo 1220928 1832789 := bbase (se 9 (by rfl) ⟨5369, by rfl⟩ : syracuseStep 1832789 = 10739) (by norm_num)
theorem B2062165 : Blo 1220928 2062165 := bbase (se 9 (by rfl) ⟨6041, by rfl⟩ : syracuseStep 2062165 = 12083) (by norm_num)
theorem B2750309 : Blo 1220928 2750309 := bbase (se 4 (by rfl) ⟨257841, by rfl⟩ : syracuseStep 2750309 = 515683) (by norm_num)
theorem B1374061 : Blo 1220928 1374061 := bbase (se 3 (by rfl) ⟨257636, by rfl⟩ : syracuseStep 1374061 = 515273) (by norm_num)
theorem B1832813 : Blo 1220928 1832813 := bbase (se 3 (by rfl) ⟨343652, by rfl⟩ : syracuseStep 1832813 = 687305) (by norm_num)
theorem B1832837 : Blo 1220928 1832837 := bbase (se 4 (by rfl) ⟨171828, by rfl⟩ : syracuseStep 1832837 = 343657) (by norm_num)
theorem B1374097 : Blo 1220928 1374097 := bbase (se 2 (by rfl) ⟨515286, by rfl⟩ : syracuseStep 1374097 = 1030573) (by norm_num)
theorem B13907861 : Blo 1220928 13907861 := bbase (se 6 (by rfl) ⟨325965, by rfl⟩ : syracuseStep 13907861 = 651931) (by norm_num)
theorem B2381717 : Blo 1220928 2381717 := bbase (se 6 (by rfl) ⟨55821, by rfl⟩ : syracuseStep 2381717 = 111643) (by norm_num)
theorem B1832861 : Blo 1220928 1832861 := bbase (se 3 (by rfl) ⟨343661, by rfl⟩ : syracuseStep 1832861 = 687323) (by norm_num)
theorem B2062253 : Blo 1220928 2062253 := bbase (se 3 (by rfl) ⟨386672, by rfl⟩ : syracuseStep 2062253 = 773345) (by norm_num)
theorem B2750381 : Blo 1220928 2750381 := bbase (se 3 (by rfl) ⟨515696, by rfl⟩ : syracuseStep 2750381 = 1031393) (by norm_num)
theorem B1374133 : Blo 1220928 1374133 := bbase (se 5 (by rfl) ⟨64412, by rfl⟩ : syracuseStep 1374133 = 128825) (by norm_num)
theorem B1832885 : Blo 1220928 1832885 := bbase (se 5 (by rfl) ⟨85916, by rfl⟩ : syracuseStep 1832885 = 171833) (by norm_num)
theorem B1832909 : Blo 1220928 1832909 := bbase (se 3 (by rfl) ⟨343670, by rfl⟩ : syracuseStep 1832909 = 687341) (by norm_num)
theorem B1374169 : Blo 1220928 1374169 := bbase (se 2 (by rfl) ⟨515313, by rfl⟩ : syracuseStep 1374169 = 1030627) (by norm_num)
theorem B1832933 : Blo 1220928 1832933 := bbase (se 4 (by rfl) ⟨171837, by rfl⟩ : syracuseStep 1832933 = 343675) (by norm_num)
theorem B1546229 : Blo 1220928 1546229 := bbase (se 5 (by rfl) ⟨72479, by rfl⟩ : syracuseStep 1546229 = 144959) (by norm_num)
theorem B2750453 : Blo 1220928 2750453 := bbase (se 5 (by rfl) ⟨128927, by rfl⟩ : syracuseStep 2750453 = 257855) (by norm_num)
theorem B1374205 : Blo 1220928 1374205 := bbase (se 3 (by rfl) ⟨257663, by rfl⟩ : syracuseStep 1374205 = 515327) (by norm_num)
theorem B1832957 : Blo 1220928 1832957 := bbase (se 3 (by rfl) ⟨343679, by rfl⟩ : syracuseStep 1832957 = 687359) (by norm_num)
theorem B1832981 : Blo 1220928 1832981 := bbase (se 6 (by rfl) ⟨42960, by rfl⟩ : syracuseStep 1832981 = 85921) (by norm_num)
theorem B1374241 : Blo 1220928 1374241 := bbase (se 2 (by rfl) ⟨515340, by rfl⟩ : syracuseStep 1374241 = 1030681) (by norm_num)
theorem B1546285 : Blo 1220928 1546285 := bbase (se 3 (by rfl) ⟨289928, by rfl⟩ : syracuseStep 1546285 = 579857) (by norm_num)
theorem B1833005 : Blo 1220928 1833005 := bbase (se 3 (by rfl) ⟨343688, by rfl⟩ : syracuseStep 1833005 = 687377) (by norm_num)
theorem B2062381 : Blo 1220928 2062381 := bbase (se 3 (by rfl) ⟨386696, by rfl⟩ : syracuseStep 2062381 = 773393) (by norm_num)
theorem B2750525 : Blo 1220928 2750525 := bbase (se 3 (by rfl) ⟨515723, by rfl⟩ : syracuseStep 2750525 = 1031447) (by norm_num)
theorem B1374277 : Blo 1220928 1374277 := bbase (se 4 (by rfl) ⟨128838, by rfl⟩ : syracuseStep 1374277 = 257677) (by norm_num)
theorem B5871685 : Blo 1220928 5871685 := bbase (se 4 (by rfl) ⟨550470, by rfl⟩ : syracuseStep 5871685 = 1100941) (by norm_num)
theorem B1833029 : Blo 1220928 1833029 := bbase (se 4 (by rfl) ⟨171846, by rfl⟩ : syracuseStep 1833029 = 343693) (by norm_num)
theorem B1833053 : Blo 1220928 1833053 := bbase (se 3 (by rfl) ⟨343697, by rfl⟩ : syracuseStep 1833053 = 687395) (by norm_num)
theorem B1374313 : Blo 1220928 1374313 := bbase (se 2 (by rfl) ⟨515367, by rfl⟩ : syracuseStep 1374313 = 1030735) (by norm_num)
theorem B1833077 : Blo 1220928 1833077 := bbase (se 5 (by rfl) ⟨85925, by rfl⟩ : syracuseStep 1833077 = 171851) (by norm_num)
theorem B3094645 : Blo 1220928 3094645 := bbase (se 5 (by rfl) ⟨145061, by rfl⟩ : syracuseStep 3094645 = 290123) (by norm_num)
theorem B2062469 : Blo 1220928 2062469 := bbase (se 4 (by rfl) ⟨193356, by rfl⟩ : syracuseStep 2062469 = 386713) (by norm_num)
theorem B2750597 : Blo 1220928 2750597 := bbase (se 4 (by rfl) ⟨257868, by rfl⟩ : syracuseStep 2750597 = 515737) (by norm_num)
theorem B1374349 : Blo 1220928 1374349 := bbase (se 3 (by rfl) ⟨257690, by rfl⟩ : syracuseStep 1374349 = 515381) (by norm_num)
theorem B1546381 : Blo 1220928 1546381 := bbase (se 3 (by rfl) ⟨289946, by rfl⟩ : syracuseStep 1546381 = 579893) (by norm_num)
theorem B1833101 : Blo 1220928 1833101 := bbase (se 3 (by rfl) ⟨343706, by rfl⟩ : syracuseStep 1833101 = 687413) (by norm_num)
theorem B1833125 : Blo 1220928 1833125 := bbase (se 4 (by rfl) ⟨171855, by rfl⟩ : syracuseStep 1833125 = 343711) (by norm_num)
theorem B1374385 : Blo 1220928 1374385 := bbase (se 2 (by rfl) ⟨515394, by rfl⟩ : syracuseStep 1374385 = 1030789) (by norm_num)
theorem B2611381 : Blo 1220928 2611381 := bbase (se 5 (by rfl) ⟨122408, by rfl⟩ : syracuseStep 2611381 = 244817) (by norm_num)
theorem B1833149 : Blo 1220928 1833149 := bbase (se 3 (by rfl) ⟨343715, by rfl⟩ : syracuseStep 1833149 = 687431) (by norm_num)
theorem B2750669 : Blo 1220928 2750669 := bbase (se 3 (by rfl) ⟨515750, by rfl⟩ : syracuseStep 2750669 = 1031501) (by norm_num)
theorem B1374421 : Blo 1220928 1374421 := bbase (se 7 (by rfl) ⟨16106, by rfl⟩ : syracuseStep 1374421 = 32213) (by norm_num)
theorem B1833173 : Blo 1220928 1833173 := bbase (se 7 (by rfl) ⟨21482, by rfl⟩ : syracuseStep 1833173 = 42965) (by norm_num)
theorem B3094757 : Blo 1220928 3094757 := bbase (se 4 (by rfl) ⟨290133, by rfl⟩ : syracuseStep 3094757 = 580267) (by norm_num)
theorem B4126949 : Blo 1220928 4126949 := bbase (se 4 (by rfl) ⟨386901, by rfl⟩ : syracuseStep 4126949 = 773803) (by norm_num)
theorem B1833197 : Blo 1220928 1833197 := bbase (se 3 (by rfl) ⟨343724, by rfl⟩ : syracuseStep 1833197 = 687449) (by norm_num)
theorem B1374457 : Blo 1220928 1374457 := bbase (se 2 (by rfl) ⟨515421, by rfl⟩ : syracuseStep 1374457 = 1030843) (by norm_num)
theorem B1833221 : Blo 1220928 1833221 := bbase (se 4 (by rfl) ⟨171864, by rfl⟩ : syracuseStep 1833221 = 343729) (by norm_num)
theorem B2062597 : Blo 1220928 2062597 := bbase (se 4 (by rfl) ⟨193368, by rfl⟩ : syracuseStep 2062597 = 386737) (by norm_num)
theorem B2750741 : Blo 1220928 2750741 := bbase (se 6 (by rfl) ⟨64470, by rfl⟩ : syracuseStep 2750741 = 128941) (by norm_num)
theorem B1374493 : Blo 1220928 1374493 := bbase (se 3 (by rfl) ⟨257717, by rfl⟩ : syracuseStep 1374493 = 515435) (by norm_num)
theorem B1833245 : Blo 1220928 1833245 := bbase (se 3 (by rfl) ⟨343733, by rfl⟩ : syracuseStep 1833245 = 687467) (by norm_num)
theorem B1833269 : Blo 1220928 1833269 := bbase (se 5 (by rfl) ⟨85934, by rfl⟩ : syracuseStep 1833269 = 171869) (by norm_num)
theorem B1546553 : Blo 1220928 1546553 := bbase (se 2 (by rfl) ⟨579957, by rfl⟩ : syracuseStep 1546553 = 1159915) (by norm_num)
theorem B1374529 : Blo 1220928 1374529 := bbase (se 2 (by rfl) ⟨515448, by rfl⟩ : syracuseStep 1374529 = 1030897) (by norm_num)
theorem B1833293 : Blo 1220928 1833293 := bbase (se 3 (by rfl) ⟨343742, by rfl⟩ : syracuseStep 1833293 = 687485) (by norm_num)
theorem B2062685 : Blo 1220928 2062685 := bbase (se 3 (by rfl) ⟨386753, by rfl⟩ : syracuseStep 2062685 = 773507) (by norm_num)
theorem B2750813 : Blo 1220928 2750813 := bbase (se 3 (by rfl) ⟨515777, by rfl⟩ : syracuseStep 2750813 = 1031555) (by norm_num)
theorem B1374565 : Blo 1220928 1374565 := bbase (se 4 (by rfl) ⟨128865, by rfl⟩ : syracuseStep 1374565 = 257731) (by norm_num)
theorem B1833317 : Blo 1220928 1833317 := bbase (se 4 (by rfl) ⟨171873, by rfl⟩ : syracuseStep 1833317 = 343747) (by norm_num)
theorem B1546609 : Blo 1220928 1546609 := bbase (se 2 (by rfl) ⟨579978, by rfl⟩ : syracuseStep 1546609 = 1159957) (by norm_num)
theorem B1833341 : Blo 1220928 1833341 := bbase (se 3 (by rfl) ⟨343751, by rfl⟩ : syracuseStep 1833341 = 687503) (by norm_num)
theorem B1374601 : Blo 1220928 1374601 := bbase (se 2 (by rfl) ⟨515475, by rfl⟩ : syracuseStep 1374601 = 1030951) (by norm_num)
theorem B11737493 : Blo 1220928 11737493 := bbase (se 6 (by rfl) ⟨275097, by rfl⟩ : syracuseStep 11737493 = 550195) (by norm_num)
theorem B1833365 : Blo 1220928 1833365 := bbase (se 6 (by rfl) ⟨42969, by rfl⟩ : syracuseStep 1833365 = 85939) (by norm_num)
theorem B2202013 : Blo 1220928 2202013 := bbase (se 3 (by rfl) ⟨412877, by rfl⟩ : syracuseStep 2202013 = 825755) (by norm_num)
theorem B2750885 : Blo 1220928 2750885 := bbase (se 4 (by rfl) ⟨257895, by rfl⟩ : syracuseStep 2750885 = 515791) (by norm_num)
theorem B3094949 : Blo 1220928 3094949 := bbase (se 4 (by rfl) ⟨290151, by rfl⟩ : syracuseStep 3094949 = 580303) (by norm_num)
theorem B1374637 : Blo 1220928 1374637 := bbase (se 3 (by rfl) ⟨257744, by rfl⟩ : syracuseStep 1374637 = 515489) (by norm_num)
theorem B1833389 : Blo 1220928 1833389 := bbase (se 3 (by rfl) ⟨343760, by rfl⟩ : syracuseStep 1833389 = 687521) (by norm_num)
theorem B1833413 : Blo 1220928 1833413 := bbase (se 4 (by rfl) ⟨171882, by rfl⟩ : syracuseStep 1833413 = 343765) (by norm_num)
theorem B1374673 : Blo 1220928 1374673 := bbase (se 2 (by rfl) ⟨515502, by rfl⟩ : syracuseStep 1374673 = 1031005) (by norm_num)
theorem B1546705 : Blo 1220928 1546705 := bbase (se 2 (by rfl) ⟨580014, by rfl⟩ : syracuseStep 1546705 = 1160029) (by norm_num)
theorem B1833437 : Blo 1220928 1833437 := bbase (se 3 (by rfl) ⟨343769, by rfl⟩ : syracuseStep 1833437 = 687539) (by norm_num)
theorem B2062813 : Blo 1220928 2062813 := bbase (se 3 (by rfl) ⟨386777, by rfl⟩ : syracuseStep 2062813 = 773555) (by norm_num)
theorem B2750957 : Blo 1220928 2750957 := bbase (se 3 (by rfl) ⟨515804, by rfl⟩ : syracuseStep 2750957 = 1031609) (by norm_num)
theorem B1374709 : Blo 1220928 1374709 := bbase (se 5 (by rfl) ⟨64439, by rfl⟩ : syracuseStep 1374709 = 128879) (by norm_num)
theorem B1833461 : Blo 1220928 1833461 := bbase (se 5 (by rfl) ⟨85943, by rfl⟩ : syracuseStep 1833461 = 171887) (by norm_num)
theorem B1833485 : Blo 1220928 1833485 := bbase (se 3 (by rfl) ⟨343778, by rfl⟩ : syracuseStep 1833485 = 687557) (by norm_num)
theorem B1374745 : Blo 1220928 1374745 := bbase (se 2 (by rfl) ⟨515529, by rfl⟩ : syracuseStep 1374745 = 1031059) (by norm_num)
theorem B1833509 : Blo 1220928 1833509 := bbase (se 4 (by rfl) ⟨171891, by rfl⟩ : syracuseStep 1833509 = 343783) (by norm_num)
theorem B2611757 : Blo 1220928 2611757 := bbase (se 3 (by rfl) ⟨489704, by rfl⟩ : syracuseStep 2611757 = 979409) (by norm_num)
theorem B2062901 : Blo 1220928 2062901 := bbase (se 5 (by rfl) ⟨96698, by rfl⟩ : syracuseStep 2062901 = 193397) (by norm_num)
theorem B2751029 : Blo 1220928 2751029 := bbase (se 5 (by rfl) ⟨128954, by rfl⟩ : syracuseStep 2751029 = 257909) (by norm_num)
theorem B1374781 : Blo 1220928 1374781 := bbase (se 3 (by rfl) ⟨257771, by rfl⟩ : syracuseStep 1374781 = 515543) (by norm_num)
theorem B1833533 : Blo 1220928 1833533 := bbase (se 3 (by rfl) ⟨343787, by rfl⟩ : syracuseStep 1833533 = 687575) (by norm_num)
theorem B1833557 : Blo 1220928 1833557 := bbase (se 8 (by rfl) ⟨10743, by rfl⟩ : syracuseStep 1833557 = 21487) (by norm_num)
theorem B1374817 : Blo 1220928 1374817 := bbase (se 2 (by rfl) ⟨515556, by rfl⟩ : syracuseStep 1374817 = 1031113) (by norm_num)
theorem B1833581 : Blo 1220928 1833581 := bbase (se 3 (by rfl) ⟨343796, by rfl⟩ : syracuseStep 1833581 = 687593) (by norm_num)
theorem B5216885 : Blo 1220928 5216885 := bbase (se 5 (by rfl) ⟨244541, by rfl⟩ : syracuseStep 5216885 = 489083) (by norm_num)
theorem B1546877 : Blo 1220928 1546877 := bbase (se 3 (by rfl) ⟨290039, by rfl⟩ : syracuseStep 1546877 = 580079) (by norm_num)
theorem B2751101 : Blo 1220928 2751101 := bbase (se 3 (by rfl) ⟨515831, by rfl⟩ : syracuseStep 2751101 = 1031663) (by norm_num)
theorem B1374853 : Blo 1220928 1374853 := bbase (se 4 (by rfl) ⟨128892, by rfl⟩ : syracuseStep 1374853 = 257785) (by norm_num)
theorem B1833605 : Blo 1220928 1833605 := bbase (se 4 (by rfl) ⟨171900, by rfl⟩ : syracuseStep 1833605 = 343801) (by norm_num)
theorem B1432205 : Blo 1220928 1432205 := bbase (se 3 (by rfl) ⟨268538, by rfl⟩ : syracuseStep 1432205 = 537077) (by norm_num)
theorem B4127381 : Blo 1220928 4127381 := bbase (se 6 (by rfl) ⟨96735, by rfl⟩ : syracuseStep 4127381 = 193471) (by norm_num)
theorem B1833629 : Blo 1220928 1833629 := bbase (se 3 (by rfl) ⟨343805, by rfl⟩ : syracuseStep 1833629 = 687611) (by norm_num)
theorem B2120357 : Blo 1220928 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B1374889 : Blo 1220928 1374889 := bbase (se 2 (by rfl) ⟨515583, by rfl⟩ : syracuseStep 1374889 = 1031167) (by norm_num)
theorem B1546933 : Blo 1220928 1546933 := bbase (se 5 (by rfl) ⟨72512, by rfl⟩ : syracuseStep 1546933 = 145025) (by norm_num)
theorem B1833653 : Blo 1220928 1833653 := bbase (se 5 (by rfl) ⟨85952, by rfl⟩ : syracuseStep 1833653 = 171905) (by norm_num)
theorem B2063029 : Blo 1220928 2063029 := bbase (se 5 (by rfl) ⟨96704, by rfl⟩ : syracuseStep 2063029 = 193409) (by norm_num)
theorem B2751173 : Blo 1220928 2751173 := bbase (se 4 (by rfl) ⟨257922, by rfl⟩ : syracuseStep 2751173 = 515845) (by norm_num)
theorem B1956557 : Blo 1220928 1956557 := bbase (se 3 (by rfl) ⟨366854, by rfl⟩ : syracuseStep 1956557 = 733709) (by norm_num)
theorem B1374925 : Blo 1220928 1374925 := bbase (se 3 (by rfl) ⟨257798, by rfl⟩ : syracuseStep 1374925 = 515597) (by norm_num)
theorem B1833677 : Blo 1220928 1833677 := bbase (se 3 (by rfl) ⟨343814, by rfl⟩ : syracuseStep 1833677 = 687629) (by norm_num)
theorem B1833701 : Blo 1220928 1833701 := bbase (se 4 (by rfl) ⟨171909, by rfl⟩ : syracuseStep 1833701 = 343819) (by norm_num)
theorem B1374961 : Blo 1220928 1374961 := bbase (se 2 (by rfl) ⟨515610, by rfl⟩ : syracuseStep 1374961 = 1031221) (by norm_num)
theorem B1833725 : Blo 1220928 1833725 := bbase (se 3 (by rfl) ⟨343823, by rfl⟩ : syracuseStep 1833725 = 687647) (by norm_num)
theorem B3095293 : Blo 1220928 3095293 := bbase (se 3 (by rfl) ⟨580367, by rfl⟩ : syracuseStep 3095293 = 1160735) (by norm_num)
theorem B2063117 : Blo 1220928 2063117 := bbase (se 3 (by rfl) ⟨386834, by rfl⟩ : syracuseStep 2063117 = 773669) (by norm_num)
theorem B2751245 : Blo 1220928 2751245 := bbase (se 3 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 2751245 = 1031717) (by norm_num)
theorem B6183701 : Blo 1220928 6183701 := bbase (se 6 (by rfl) ⟨144930, by rfl⟩ : syracuseStep 6183701 = 289861) (by norm_num)
theorem B1374997 : Blo 1220928 1374997 := bbase (se 6 (by rfl) ⟨32226, by rfl⟩ : syracuseStep 1374997 = 64453) (by norm_num)
theorem B1547029 : Blo 1220928 1547029 := bbase (se 6 (by rfl) ⟨36258, by rfl⟩ : syracuseStep 1547029 = 72517) (by norm_num)
theorem B1833749 : Blo 1220928 1833749 := bbase (se 6 (by rfl) ⟨42978, by rfl⟩ : syracuseStep 1833749 = 85957) (by norm_num)
theorem B1833773 : Blo 1220928 1833773 := bbase (se 3 (by rfl) ⟨343832, by rfl⟩ : syracuseStep 1833773 = 687665) (by norm_num)
theorem B1375033 : Blo 1220928 1375033 := bbase (se 2 (by rfl) ⟨515637, by rfl⟩ : syracuseStep 1375033 = 1031275) (by norm_num)
theorem B1833797 : Blo 1220928 1833797 := bbase (se 4 (by rfl) ⟨171918, by rfl⟩ : syracuseStep 1833797 = 343837) (by norm_num)
theorem B2751317 : Blo 1220928 2751317 := bbase (se 9 (by rfl) ⟨8060, by rfl⟩ : syracuseStep 2751317 = 16121) (by norm_num)
theorem B1375069 : Blo 1220928 1375069 := bbase (se 3 (by rfl) ⟨257825, by rfl⟩ : syracuseStep 1375069 = 515651) (by norm_num)
theorem B1833821 : Blo 1220928 1833821 := bbase (se 3 (by rfl) ⟨343841, by rfl⟩ : syracuseStep 1833821 = 687683) (by norm_num)
theorem B3095405 : Blo 1220928 3095405 := bbase (se 3 (by rfl) ⟨580388, by rfl⟩ : syracuseStep 3095405 = 1160777) (by norm_num)
theorem B1833845 : Blo 1220928 1833845 := bbase (se 5 (by rfl) ⟨85961, by rfl⟩ : syracuseStep 1833845 = 171923) (by norm_num)
theorem B1375105 : Blo 1220928 1375105 := bbase (se 2 (by rfl) ⟨515664, by rfl⟩ : syracuseStep 1375105 = 1031329) (by norm_num)
theorem B5651333 : Blo 1220928 5651333 := bbase (se 4 (by rfl) ⟨529812, by rfl⟩ : syracuseStep 5651333 = 1059625) (by norm_num)
theorem B1833869 : Blo 1220928 1833869 := bbase (se 3 (by rfl) ⟨343850, by rfl⟩ : syracuseStep 1833869 = 687701) (by norm_num)
theorem B2063245 : Blo 1220928 2063245 := bbase (se 3 (by rfl) ⟨386858, by rfl⟩ : syracuseStep 2063245 = 773717) (by norm_num)
theorem B2751389 : Blo 1220928 2751389 := bbase (se 3 (by rfl) ⟨515885, by rfl⟩ : syracuseStep 2751389 = 1031771) (by norm_num)
theorem B1375141 : Blo 1220928 1375141 := bbase (se 4 (by rfl) ⟨128919, by rfl⟩ : syracuseStep 1375141 = 257839) (by norm_num)
theorem B1833893 : Blo 1220928 1833893 := bbase (se 4 (by rfl) ⟨171927, by rfl⟩ : syracuseStep 1833893 = 343855) (by norm_num)
theorem B11140021 : Blo 1220928 11140021 := bbase (se 5 (by rfl) ⟨522188, by rfl⟩ : syracuseStep 11140021 = 1044377) (by norm_num)
theorem B1833917 : Blo 1220928 1833917 := bbase (se 3 (by rfl) ⟨343859, by rfl⟩ : syracuseStep 1833917 = 687719) (by norm_num)
theorem B1547201 : Blo 1220928 1547201 := bbase (se 2 (by rfl) ⟨580200, by rfl⟩ : syracuseStep 1547201 = 1160401) (by norm_num)
theorem B1375177 : Blo 1220928 1375177 := bbase (se 2 (by rfl) ⟨515691, by rfl⟩ : syracuseStep 1375177 = 1031383) (by norm_num)
theorem B1833941 : Blo 1220928 1833941 := bbase (se 7 (by rfl) ⟨21491, by rfl⟩ : syracuseStep 1833941 = 42983) (by norm_num)
theorem B2063333 : Blo 1220928 2063333 := bbase (se 4 (by rfl) ⟨193437, by rfl⟩ : syracuseStep 2063333 = 386875) (by norm_num)
theorem B2751461 : Blo 1220928 2751461 := bbase (se 4 (by rfl) ⟨257949, by rfl⟩ : syracuseStep 2751461 = 515899) (by norm_num)
theorem B1375213 : Blo 1220928 1375213 := bbase (se 3 (by rfl) ⟨257852, by rfl⟩ : syracuseStep 1375213 = 515705) (by norm_num)
theorem B1833965 : Blo 1220928 1833965 := bbase (se 3 (by rfl) ⟨343868, by rfl⟩ : syracuseStep 1833965 = 687737) (by norm_num)
theorem B3480565 : Blo 1220928 3480565 := bbase (se 5 (by rfl) ⟨163151, by rfl⟩ : syracuseStep 3480565 = 326303) (by norm_num)
theorem B1547257 : Blo 1220928 1547257 := bbase (se 2 (by rfl) ⟨580221, by rfl⟩ : syracuseStep 1547257 = 1160443) (by norm_num)
theorem B1833989 : Blo 1220928 1833989 := bbase (se 4 (by rfl) ⟨171936, by rfl⟩ : syracuseStep 1833989 = 343873) (by norm_num)
theorem B1375249 : Blo 1220928 1375249 := bbase (se 2 (by rfl) ⟨515718, by rfl⟩ : syracuseStep 1375249 = 1031437) (by norm_num)
theorem B1834013 : Blo 1220928 1834013 := bbase (se 3 (by rfl) ⟨343877, by rfl⟩ : syracuseStep 1834013 = 687755) (by norm_num)
theorem B2751533 : Blo 1220928 2751533 := bbase (se 3 (by rfl) ⟨515912, by rfl⟩ : syracuseStep 2751533 = 1031825) (by norm_num)
theorem B1375285 : Blo 1220928 1375285 := bbase (se 5 (by rfl) ⟨64466, by rfl⟩ : syracuseStep 1375285 = 128933) (by norm_num)
theorem B1834037 : Blo 1220928 1834037 := bbase (se 5 (by rfl) ⟨85970, by rfl⟩ : syracuseStep 1834037 = 171941) (by norm_num)
theorem B1834061 : Blo 1220928 1834061 := bbase (se 3 (by rfl) ⟨343886, by rfl⟩ : syracuseStep 1834061 = 687773) (by norm_num)
theorem B1375321 : Blo 1220928 1375321 := bbase (se 2 (by rfl) ⟨515745, by rfl⟩ : syracuseStep 1375321 = 1031491) (by norm_num)
theorem B1547353 : Blo 1220928 1547353 := bbase (se 2 (by rfl) ⟨580257, by rfl⟩ : syracuseStep 1547353 = 1160515) (by norm_num)
theorem B1834085 : Blo 1220928 1834085 := bbase (se 4 (by rfl) ⟨171945, by rfl⟩ : syracuseStep 1834085 = 343891) (by norm_num)
theorem B2063461 : Blo 1220928 2063461 := bbase (se 4 (by rfl) ⟨193449, by rfl⟩ : syracuseStep 2063461 = 386899) (by norm_num)
theorem B1375357 : Blo 1220928 1375357 := bbase (se 3 (by rfl) ⟨257879, by rfl⟩ : syracuseStep 1375357 = 515759) (by norm_num)
theorem B1834109 : Blo 1220928 1834109 := bbase (se 3 (by rfl) ⟨343895, by rfl⟩ : syracuseStep 1834109 = 687791) (by norm_num)
theorem B3480725 : Blo 1220928 3480725 := bbase (se 6 (by rfl) ⟨81579, by rfl⟩ : syracuseStep 3480725 = 163159) (by norm_num)
theorem B1834133 : Blo 1220928 1834133 := bbase (se 6 (by rfl) ⟨42987, by rfl⟩ : syracuseStep 1834133 = 85975) (by norm_num)
theorem B1375393 : Blo 1220928 1375393 := bbase (se 2 (by rfl) ⟨515772, by rfl⟩ : syracuseStep 1375393 = 1031545) (by norm_num)
theorem B1834157 : Blo 1220928 1834157 := bbase (se 3 (by rfl) ⟨343904, by rfl⟩ : syracuseStep 1834157 = 687809) (by norm_num)
theorem B2063549 : Blo 1220928 2063549 := bbase (se 3 (by rfl) ⟨386915, by rfl⟩ : syracuseStep 2063549 = 773831) (by norm_num)
theorem B1375429 : Blo 1220928 1375429 := bbase (se 4 (by rfl) ⟨128946, by rfl⟩ : syracuseStep 1375429 = 257893) (by norm_num)
theorem B1834181 : Blo 1220928 1834181 := bbase (se 4 (by rfl) ⟨171954, by rfl⟩ : syracuseStep 1834181 = 343909) (by norm_num)
theorem B1957069 : Blo 1220928 1957069 := bbase (se 3 (by rfl) ⟨366950, by rfl⟩ : syracuseStep 1957069 = 733901) (by norm_num)
theorem B1834205 : Blo 1220928 1834205 := bbase (se 3 (by rfl) ⟨343913, by rfl⟩ : syracuseStep 1834205 = 687827) (by norm_num)
theorem B1375465 : Blo 1220928 1375465 := bbase (se 2 (by rfl) ⟨515799, by rfl⟩ : syracuseStep 1375465 = 1031599) (by norm_num)
theorem B4635893 : Blo 1220928 4635893 := bbase (se 5 (by rfl) ⟨217307, by rfl⟩ : syracuseStep 4635893 = 434615) (by norm_num)
theorem B1834229 : Blo 1220928 1834229 := bbase (se 5 (by rfl) ⟨85979, by rfl⟩ : syracuseStep 1834229 = 171959) (by norm_num)
theorem B1547525 : Blo 1220928 1547525 := bbase (se 4 (by rfl) ⟨145080, by rfl⟩ : syracuseStep 1547525 = 290161) (by norm_num)
theorem B1375501 : Blo 1220928 1375501 := bbase (se 3 (by rfl) ⟨257906, by rfl⟩ : syracuseStep 1375501 = 515813) (by norm_num)
theorem B1834253 : Blo 1220928 1834253 := bbase (se 3 (by rfl) ⟨343922, by rfl⟩ : syracuseStep 1834253 = 687845) (by norm_num)
theorem B1834277 : Blo 1220928 1834277 := bbase (se 4 (by rfl) ⟨171963, by rfl⟩ : syracuseStep 1834277 = 343927) (by norm_num)
theorem B1375537 : Blo 1220928 1375537 := bbase (se 2 (by rfl) ⟨515826, by rfl⟩ : syracuseStep 1375537 = 1031653) (by norm_num)
theorem B1547581 : Blo 1220928 1547581 := bbase (se 3 (by rfl) ⟨290171, by rfl⟩ : syracuseStep 1547581 = 580343) (by norm_num)
theorem B1834301 : Blo 1220928 1834301 := bbase (se 3 (by rfl) ⟨343931, by rfl⟩ : syracuseStep 1834301 = 687863) (by norm_num)
theorem B2063677 : Blo 1220928 2063677 := bbase (se 3 (by rfl) ⟨386939, by rfl⟩ : syracuseStep 2063677 = 773879) (by norm_num)
theorem B1375573 : Blo 1220928 1375573 := bbase (se 11 (by rfl) ⟨1007, by rfl⟩ : syracuseStep 1375573 = 2015) (by norm_num)
theorem B1834325 : Blo 1220928 1834325 := bbase (se 11 (by rfl) ⟨1343, by rfl⟩ : syracuseStep 1834325 = 2687) (by norm_num)
theorem B5954917 : Blo 1220928 5954917 := bbase (se 4 (by rfl) ⟨558273, by rfl⟩ : syracuseStep 5954917 = 1116547) (by norm_num)
theorem B1834349 : Blo 1220928 1834349 := bbase (se 3 (by rfl) ⟨343940, by rfl⟩ : syracuseStep 1834349 = 687881) (by norm_num)
theorem B3915125 : Blo 1220928 3915125 := bbase (se 5 (by rfl) ⟨183521, by rfl⟩ : syracuseStep 3915125 = 367043) (by norm_num)
theorem B1375609 : Blo 1220928 1375609 := bbase (se 2 (by rfl) ⟨515853, by rfl⟩ : syracuseStep 1375609 = 1031707) (by norm_num)
theorem B3480965 : Blo 1220928 3480965 := bbase (se 4 (by rfl) ⟨326340, by rfl⟩ : syracuseStep 3480965 = 652681) (by norm_num)
theorem B1834373 : Blo 1220928 1834373 := bbase (se 4 (by rfl) ⟨171972, by rfl⟩ : syracuseStep 1834373 = 343945) (by norm_num)
theorem B1375645 : Blo 1220928 1375645 := bbase (se 3 (by rfl) ⟨257933, by rfl⟩ : syracuseStep 1375645 = 515867) (by norm_num)
theorem B1547677 : Blo 1220928 1547677 := bbase (se 3 (by rfl) ⟨290189, by rfl⟩ : syracuseStep 1547677 = 580379) (by norm_num)
theorem B1375681 : Blo 1220928 1375681 := bbase (se 2 (by rfl) ⟨515880, by rfl⟩ : syracuseStep 1375681 = 1031761) (by norm_num)
theorem B2203109 : Blo 1220928 2203109 := bbase (se 4 (by rfl) ⟨206541, by rfl⟩ : syracuseStep 2203109 = 413083) (by norm_num)
theorem B1375717 : Blo 1220928 1375717 := bbase (se 4 (by rfl) ⟨128973, by rfl⟩ : syracuseStep 1375717 = 257947) (by norm_num)
theorem B1375753 : Blo 1220928 1375753 := bbase (se 2 (by rfl) ⟨515907, by rfl⟩ : syracuseStep 1375753 = 1031815) (by norm_num)
theorem B1859117 : Blo 1220928 1859117 := bbase (se 3 (by rfl) ⟨348584, by rfl⟩ : syracuseStep 1859117 = 697169) (by norm_num)
theorem B1375789 : Blo 1220928 1375789 := bbase (se 3 (by rfl) ⟨257960, by rfl⟩ : syracuseStep 1375789 = 515921) (by norm_num)
theorem B3481157 : Blo 1220928 3481157 := bbase (se 4 (by rfl) ⟨326358, by rfl⟩ : syracuseStep 3481157 = 652717) (by norm_num)
theorem B2317909 : Blo 1220928 2317909 := bbase (se 8 (by rfl) ⟨13581, by rfl⟩ : syracuseStep 2317909 = 27163) (by norm_num)
theorem B9281141 : Blo 1220928 9281141 := bbase (se 5 (by rfl) ⟨435053, by rfl⟩ : syracuseStep 9281141 = 870107) (by norm_num)
theorem B10051285 : Blo 1220928 10051285 := bbase (se 7 (by rfl) ⟨117788, by rfl⟩ : syracuseStep 10051285 = 235577) (by norm_num)
theorem B2318053 : Blo 1220928 2318053 := bbase (se 4 (by rfl) ⟨217317, by rfl⟩ : syracuseStep 2318053 = 434635) (by norm_num)
theorem B3301093 : Blo 1220928 3301093 := bbase (se 4 (by rfl) ⟨309477, by rfl⟩ : syracuseStep 3301093 = 618955) (by norm_num)
theorem B1957613 : Blo 1220928 1957613 := bbase (se 3 (by rfl) ⟨367052, by rfl⟩ : syracuseStep 1957613 = 734105) (by norm_num)
theorem B10444565 : Blo 1220928 10444565 := bbase (se 6 (by rfl) ⟨244794, by rfl⟩ : syracuseStep 10444565 = 489589) (by norm_num)
theorem B6610709 : Blo 1220928 6610709 := bbase (se 6 (by rfl) ⟨154938, by rfl⟩ : syracuseStep 6610709 = 309877) (by norm_num)
theorem B2785117 : Blo 1220928 2785117 := bbase (se 3 (by rfl) ⟨522209, by rfl⟩ : syracuseStep 2785117 = 1044419) (by norm_num)
theorem B1392485 : Blo 1220928 1392485 := bbase (se 4 (by rfl) ⟨130545, by rfl⟩ : syracuseStep 1392485 = 261091) (by norm_num)
theorem B2318213 : Blo 1220928 2318213 := bbase (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) (by norm_num)
theorem B2383781 : Blo 1220928 2383781 := bbase (se 4 (by rfl) ⟨223479, by rfl⟩ : syracuseStep 2383781 = 446959) (by norm_num)
theorem B1957889 : Blo 1220928 1957889 := bstep (se 2 (by rfl) ⟨734208, by rfl⟩ : syracuseStep 1957889 = 1468417) B1468417
theorem B3481613 : Blo 1220928 3481613 := bstep (se 3 (by rfl) ⟨652802, by rfl⟩ : syracuseStep 3481613 = 1305605) B1305605
theorem B4120685 : Blo 1220928 4120685 := bstep (se 3 (by rfl) ⟨772628, by rfl⟩ : syracuseStep 4120685 = 1545257) B1545257
theorem B6611057 : Blo 1220928 6611057 := bstep (se 2 (by rfl) ⟨2479146, by rfl⟩ : syracuseStep 6611057 = 4958293) B4958293
theorem B4120739 : Blo 1220928 4120739 := bstep (se 1 (by rfl) ⟨3090554, by rfl⟩ : syracuseStep 4120739 = 6181109) B6181109
theorem B4636835 : Blo 1220928 4636835 := bstep (se 1 (by rfl) ⟨3477626, by rfl⟩ : syracuseStep 4636835 = 6955253) B6955253
theorem B3178673 : Blo 1220928 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B3481795 : Blo 1220928 3481795 := bstep (se 1 (by rfl) ⟨2611346, by rfl⟩ : syracuseStep 3481795 = 5222693) B5222693
theorem B3481841 : Blo 1220928 3481841 := bstep (se 2 (by rfl) ⟨1305690, by rfl⟩ : syracuseStep 3481841 = 2611381) B2611381
theorem B1220931 : Blo 1220928 1220931 := bstep (se 1 (by rfl) ⟨915698, by rfl⟩ : syracuseStep 1220931 = 1831397) B1831397
theorem B1220947 : Blo 1220928 1220947 := bstep (se 1 (by rfl) ⟨915710, by rfl⟩ : syracuseStep 1220947 = 1831421) B1831421
theorem B1392979 : Blo 1220928 1392979 := bstep (se 1 (by rfl) ⟨1044734, by rfl⟩ : syracuseStep 1392979 = 2089469) B2089469
theorem B1220963 : Blo 1220928 1220963 := bstep (se 1 (by rfl) ⟨915722, by rfl⟩ : syracuseStep 1220963 = 1831445) B1831445
theorem B6963569 : Blo 1220928 6963569 := bstep (se 2 (by rfl) ⟨2611338, by rfl⟩ : syracuseStep 6963569 = 5222677) B5222677
theorem B1220979 : Blo 1220928 1220979 := bstep (se 1 (by rfl) ⟨915734, by rfl⟩ : syracuseStep 1220979 = 1831469) B1831469
theorem B1220995 : Blo 1220928 1220995 := bstep (se 1 (by rfl) ⟨915746, by rfl⟩ : syracuseStep 1220995 = 1831493) B1831493
theorem B1221011 : Blo 1220928 1221011 := bstep (se 1 (by rfl) ⟨915758, by rfl⟩ : syracuseStep 1221011 = 1831517) B1831517
theorem B1958305 : Blo 1220928 1958305 := bstep (se 2 (by rfl) ⟨734364, by rfl⟩ : syracuseStep 1958305 = 1468729) B1468729
theorem B1221027 : Blo 1220928 1221027 := bstep (se 1 (by rfl) ⟨915770, by rfl⟩ : syracuseStep 1221027 = 1831541) B1831541
theorem B4121009 : Blo 1220928 4121009 := bstep (se 2 (by rfl) ⟨1545378, by rfl⟩ : syracuseStep 4121009 = 3090757) B3090757
theorem B1221043 : Blo 1220928 1221043 := bstep (se 1 (by rfl) ⟨915782, by rfl⟩ : syracuseStep 1221043 = 1831565) B1831565
theorem B1221059 : Blo 1220928 1221059 := bstep (se 1 (by rfl) ⟨915794, by rfl⟩ : syracuseStep 1221059 = 1831589) B1831589
theorem B1221075 : Blo 1220928 1221075 := bstep (se 1 (by rfl) ⟨915806, by rfl⟩ : syracuseStep 1221075 = 1831613) B1831613
theorem B1221091 : Blo 1220928 1221091 := bstep (se 1 (by rfl) ⟨915818, by rfl⟩ : syracuseStep 1221091 = 1831637) B1831637
theorem B1221107 : Blo 1220928 1221107 := bstep (se 1 (by rfl) ⟨915830, by rfl⟩ : syracuseStep 1221107 = 1831661) B1831661
theorem B1221123 : Blo 1220928 1221123 := bstep (se 1 (by rfl) ⟨915842, by rfl⟩ : syracuseStep 1221123 = 1831685) B1831685
theorem B1221139 : Blo 1220928 1221139 := bstep (se 1 (by rfl) ⟨915854, by rfl⟩ : syracuseStep 1221139 = 1831709) B1831709
theorem B1221155 : Blo 1220928 1221155 := bstep (se 1 (by rfl) ⟨915866, by rfl⟩ : syracuseStep 1221155 = 1831733) B1831733
theorem B5571107 : Blo 1220928 5571107 := bstep (se 1 (by rfl) ⟨4178330, by rfl⟩ : syracuseStep 5571107 = 8356661) B8356661
theorem B1221171 : Blo 1220928 1221171 := bstep (se 1 (by rfl) ⟨915878, by rfl⟩ : syracuseStep 1221171 = 1831757) B1831757
theorem B1221187 : Blo 1220928 1221187 := bstep (se 1 (by rfl) ⟨915890, by rfl⟩ : syracuseStep 1221187 = 1831781) B1831781
theorem B1221203 : Blo 1220928 1221203 := bstep (se 1 (by rfl) ⟨915902, by rfl⟩ : syracuseStep 1221203 = 1831805) B1831805
theorem B1221219 : Blo 1220928 1221219 := bstep (se 1 (by rfl) ⟨915914, by rfl⟩ : syracuseStep 1221219 = 1831829) B1831829
theorem B1221235 : Blo 1220928 1221235 := bstep (se 1 (by rfl) ⟨915926, by rfl⟩ : syracuseStep 1221235 = 1831853) B1831853
theorem B1221251 : Blo 1220928 1221251 := bstep (se 1 (by rfl) ⟨915938, by rfl⟩ : syracuseStep 1221251 = 1831877) B1831877
theorem B1221267 : Blo 1220928 1221267 := bstep (se 1 (by rfl) ⟨915950, by rfl⟩ : syracuseStep 1221267 = 1831901) B1831901
theorem B1221283 : Blo 1220928 1221283 := bstep (se 1 (by rfl) ⟨915962, by rfl⟩ : syracuseStep 1221283 = 1831925) B1831925
theorem B2319025 : Blo 1220928 2319025 := bstep (se 2 (by rfl) ⟨869634, by rfl⟩ : syracuseStep 2319025 = 1739269) B1739269
theorem B1221299 : Blo 1220928 1221299 := bstep (se 1 (by rfl) ⟨915974, by rfl⟩ : syracuseStep 1221299 = 1831949) B1831949
theorem B1221315 : Blo 1220928 1221315 := bstep (se 1 (by rfl) ⟨915986, by rfl⟩ : syracuseStep 1221315 = 1831973) B1831973
theorem B1696465 : Blo 1220928 1696465 := bstep (se 2 (by rfl) ⟨636174, by rfl⟩ : syracuseStep 1696465 = 1272349) B1272349
theorem B1221331 : Blo 1220928 1221331 := bstep (se 1 (by rfl) ⟨915998, by rfl⟩ : syracuseStep 1221331 = 1831997) B1831997
theorem B1221347 : Blo 1220928 1221347 := bstep (se 1 (by rfl) ⟨916010, by rfl⟩ : syracuseStep 1221347 = 1832021) B1832021
theorem B1221363 : Blo 1220928 1221363 := bstep (se 1 (by rfl) ⟨916022, by rfl⟩ : syracuseStep 1221363 = 1832045) B1832045
theorem B1221379 : Blo 1220928 1221379 := bstep (se 1 (by rfl) ⟨916034, by rfl⟩ : syracuseStep 1221379 = 1832069) B1832069
theorem B1221395 : Blo 1220928 1221395 := bstep (se 1 (by rfl) ⟨916046, by rfl⟩ : syracuseStep 1221395 = 1832093) B1832093
theorem B1221411 : Blo 1220928 1221411 := bstep (se 1 (by rfl) ⟨916058, by rfl⟩ : syracuseStep 1221411 = 1832117) B1832117
theorem B1221427 : Blo 1220928 1221427 := bstep (se 1 (by rfl) ⟨916070, by rfl⟩ : syracuseStep 1221427 = 1832141) B1832141
theorem B1221443 : Blo 1220928 1221443 := bstep (se 1 (by rfl) ⟨916082, by rfl⟩ : syracuseStep 1221443 = 1832165) B1832165
theorem B2319185 : Blo 1220928 2319185 := bstep (se 2 (by rfl) ⟨869694, by rfl⟩ : syracuseStep 2319185 = 1739389) B1739389
theorem B1221459 : Blo 1220928 1221459 := bstep (se 1 (by rfl) ⟨916094, by rfl⟩ : syracuseStep 1221459 = 1832189) B1832189
theorem B1221475 : Blo 1220928 1221475 := bstep (se 1 (by rfl) ⟨916106, by rfl⟩ : syracuseStep 1221475 = 1832213) B1832213
theorem B1221491 : Blo 1220928 1221491 := bstep (se 1 (by rfl) ⟨916118, by rfl⟩ : syracuseStep 1221491 = 1832237) B1832237
theorem B1221507 : Blo 1220928 1221507 := bstep (se 1 (by rfl) ⟨916130, by rfl⟩ : syracuseStep 1221507 = 1832261) B1832261
theorem B1221523 : Blo 1220928 1221523 := bstep (se 1 (by rfl) ⟨916142, by rfl⟩ : syracuseStep 1221523 = 1832285) B1832285
theorem B1221539 : Blo 1220928 1221539 := bstep (se 1 (by rfl) ⟨916154, by rfl⟩ : syracuseStep 1221539 = 1832309) B1832309
theorem B1221555 : Blo 1220928 1221555 := bstep (se 1 (by rfl) ⟨916166, by rfl⟩ : syracuseStep 1221555 = 1832333) B1832333
theorem B1221571 : Blo 1220928 1221571 := bstep (se 1 (by rfl) ⟨916178, by rfl⟩ : syracuseStep 1221571 = 1832357) B1832357
theorem B4121549 : Blo 1220928 4121549 := bstep (se 3 (by rfl) ⟨772790, by rfl⟩ : syracuseStep 4121549 = 1545581) B1545581
theorem B1221587 : Blo 1220928 1221587 := bstep (se 1 (by rfl) ⟨916190, by rfl⟩ : syracuseStep 1221587 = 1832381) B1832381
theorem B1221603 : Blo 1220928 1221603 := bstep (se 1 (by rfl) ⟨916202, by rfl⟩ : syracuseStep 1221603 = 1832405) B1832405
theorem B6185969 : Blo 1220928 6185969 := bstep (se 2 (by rfl) ⟨2319738, by rfl⟩ : syracuseStep 6185969 = 4639477) B4639477
theorem B1221619 : Blo 1220928 1221619 := bstep (se 1 (by rfl) ⟨916214, by rfl⟩ : syracuseStep 1221619 = 1832429) B1832429
theorem B4121603 : Blo 1220928 4121603 := bstep (se 1 (by rfl) ⟨3091202, by rfl⟩ : syracuseStep 4121603 = 6182405) B6182405
theorem B1221635 : Blo 1220928 1221635 := bstep (se 1 (by rfl) ⟨916226, by rfl⟩ : syracuseStep 1221635 = 1832453) B1832453
theorem B1221651 : Blo 1220928 1221651 := bstep (se 1 (by rfl) ⟨916238, by rfl⟩ : syracuseStep 1221651 = 1832477) B1832477
theorem B1221667 : Blo 1220928 1221667 := bstep (se 1 (by rfl) ⟨916250, by rfl⟩ : syracuseStep 1221667 = 1832501) B1832501
theorem B1221683 : Blo 1220928 1221683 := bstep (se 1 (by rfl) ⟨916262, by rfl⟩ : syracuseStep 1221683 = 1832525) B1832525
theorem B1221699 : Blo 1220928 1221699 := bstep (se 1 (by rfl) ⟨916274, by rfl⟩ : syracuseStep 1221699 = 1832549) B1832549
theorem B1221715 : Blo 1220928 1221715 := bstep (se 1 (by rfl) ⟨916286, by rfl⟩ : syracuseStep 1221715 = 1832573) B1832573
theorem B1221731 : Blo 1220928 1221731 := bstep (se 1 (by rfl) ⟨916298, by rfl⟩ : syracuseStep 1221731 = 1832597) B1832597
theorem B10437731 : Blo 1220928 10437731 := bstep (se 1 (by rfl) ⟨7828298, by rfl⟩ : syracuseStep 10437731 = 15656597) B15656597
theorem B1221747 : Blo 1220928 1221747 := bstep (se 1 (by rfl) ⟨916310, by rfl⟩ : syracuseStep 1221747 = 1832621) B1832621
theorem B1221763 : Blo 1220928 1221763 := bstep (se 1 (by rfl) ⟨916322, by rfl⟩ : syracuseStep 1221763 = 1832645) B1832645
theorem B4637837 : Blo 1220928 4637837 := bstep (se 3 (by rfl) ⟨869594, by rfl⟩ : syracuseStep 4637837 = 1739189) B1739189
theorem B1221779 : Blo 1220928 1221779 := bstep (se 1 (by rfl) ⟨916334, by rfl⟩ : syracuseStep 1221779 = 1832669) B1832669
theorem B1221795 : Blo 1220928 1221795 := bstep (se 1 (by rfl) ⟨916346, by rfl⟩ : syracuseStep 1221795 = 1832693) B1832693
theorem B1221811 : Blo 1220928 1221811 := bstep (se 1 (by rfl) ⟨916358, by rfl⟩ : syracuseStep 1221811 = 1832717) B1832717
theorem B1221827 : Blo 1220928 1221827 := bstep (se 1 (by rfl) ⟨916370, by rfl⟩ : syracuseStep 1221827 = 1832741) B1832741
theorem B17605829 : Blo 1220928 17605829 := bstep (se 4 (by rfl) ⟨1650546, by rfl⟩ : syracuseStep 17605829 = 3301093) B3301093
theorem B1221843 : Blo 1220928 1221843 := bstep (se 1 (by rfl) ⟨916382, by rfl⟩ : syracuseStep 1221843 = 1832765) B1832765
theorem B2319587 : Blo 1220928 2319587 := bstep (se 1 (by rfl) ⟨1739690, by rfl⟩ : syracuseStep 2319587 = 3479381) B3479381
theorem B1221859 : Blo 1220928 1221859 := bstep (se 1 (by rfl) ⟨916394, by rfl⟩ : syracuseStep 1221859 = 1832789) B1832789
theorem B9045233 : Blo 1220928 9045233 := bstep (se 2 (by rfl) ⟨3391962, by rfl⟩ : syracuseStep 9045233 = 6783925) B6783925
theorem B1221875 : Blo 1220928 1221875 := bstep (se 1 (by rfl) ⟨916406, by rfl⟩ : syracuseStep 1221875 = 1832813) B1832813
theorem B1221891 : Blo 1220928 1221891 := bstep (se 1 (by rfl) ⟨916418, by rfl⟩ : syracuseStep 1221891 = 1832837) B1832837
theorem B4121873 : Blo 1220928 4121873 := bstep (se 2 (by rfl) ⟨1545702, by rfl⟩ : syracuseStep 4121873 = 3091405) B3091405
theorem B1221907 : Blo 1220928 1221907 := bstep (se 1 (by rfl) ⟨916430, by rfl⟩ : syracuseStep 1221907 = 1832861) B1832861
theorem B1221923 : Blo 1220928 1221923 := bstep (se 1 (by rfl) ⟨916442, by rfl⟩ : syracuseStep 1221923 = 1832885) B1832885
theorem B1221939 : Blo 1220928 1221939 := bstep (se 1 (by rfl) ⟨916454, by rfl⟩ : syracuseStep 1221939 = 1832909) B1832909
theorem B1221955 : Blo 1220928 1221955 := bstep (se 1 (by rfl) ⟨916466, by rfl⟩ : syracuseStep 1221955 = 1832933) B1832933
theorem B3917123 : Blo 1220928 3917123 := bstep (se 1 (by rfl) ⟨2937842, by rfl⟩ : syracuseStep 3917123 = 5875685) B5875685
theorem B1221971 : Blo 1220928 1221971 := bstep (se 1 (by rfl) ⟨916478, by rfl⟩ : syracuseStep 1221971 = 1832957) B1832957
theorem B13206883 : Blo 1220928 13206883 := bstep (se 1 (by rfl) ⟨9905162, by rfl⟩ : syracuseStep 13206883 = 19810325) B19810325
theorem B1221987 : Blo 1220928 1221987 := bstep (se 1 (by rfl) ⟨916490, by rfl⟩ : syracuseStep 1221987 = 1832981) B1832981
theorem B1222003 : Blo 1220928 1222003 := bstep (se 1 (by rfl) ⟨916502, by rfl⟩ : syracuseStep 1222003 = 1833005) B1833005
theorem B1222019 : Blo 1220928 1222019 := bstep (se 1 (by rfl) ⟨916514, by rfl⟩ : syracuseStep 1222019 = 1833029) B1833029
theorem B56460685 : Blo 1220928 56460685 := bstep (se 3 (by rfl) ⟨10586378, by rfl⟩ : syracuseStep 56460685 = 21172757) B21172757
theorem B1222035 : Blo 1220928 1222035 := bstep (se 1 (by rfl) ⟨916526, by rfl⟩ : syracuseStep 1222035 = 1833053) B1833053
theorem B1222051 : Blo 1220928 1222051 := bstep (se 1 (by rfl) ⟨916538, by rfl⟩ : syracuseStep 1222051 = 1833077) B1833077
theorem B1222067 : Blo 1220928 1222067 := bstep (se 1 (by rfl) ⟨916550, by rfl⟩ : syracuseStep 1222067 = 1833101) B1833101
theorem B1222083 : Blo 1220928 1222083 := bstep (se 1 (by rfl) ⟨916562, by rfl⟩ : syracuseStep 1222083 = 1833125) B1833125
theorem B3917251 : Blo 1220928 3917251 := bstep (se 1 (by rfl) ⟨2937938, by rfl⟩ : syracuseStep 3917251 = 5875877) B5875877
theorem B4957645 : Blo 1220928 4957645 := bstep (se 3 (by rfl) ⟨929558, by rfl⟩ : syracuseStep 4957645 = 1859117) B1859117
theorem B1222099 : Blo 1220928 1222099 := bstep (se 1 (by rfl) ⟨916574, by rfl⟩ : syracuseStep 1222099 = 1833149) B1833149
theorem B1222115 : Blo 1220928 1222115 := bstep (se 1 (by rfl) ⟨916586, by rfl⟩ : syracuseStep 1222115 = 1833173) B1833173
theorem B1222131 : Blo 1220928 1222131 := bstep (se 1 (by rfl) ⟨916598, by rfl⟩ : syracuseStep 1222131 = 1833197) B1833197
theorem B1222147 : Blo 1220928 1222147 := bstep (se 1 (by rfl) ⟨916610, by rfl⟩ : syracuseStep 1222147 = 1833221) B1833221
theorem B9283085 : Blo 1220928 9283085 := bstep (se 3 (by rfl) ⟨1740578, by rfl⟩ : syracuseStep 9283085 = 3481157) B3481157
theorem B1222163 : Blo 1220928 1222163 := bstep (se 1 (by rfl) ⟨916622, by rfl⟩ : syracuseStep 1222163 = 1833245) B1833245
theorem B1222179 : Blo 1220928 1222179 := bstep (se 1 (by rfl) ⟨916634, by rfl⟩ : syracuseStep 1222179 = 1833269) B1833269
theorem B1222195 : Blo 1220928 1222195 := bstep (se 1 (by rfl) ⟨916646, by rfl⟩ : syracuseStep 1222195 = 1833293) B1833293
theorem B1222211 : Blo 1220928 1222211 := bstep (se 1 (by rfl) ⟨916658, by rfl⟩ : syracuseStep 1222211 = 1833317) B1833317
theorem B1222227 : Blo 1220928 1222227 := bstep (se 1 (by rfl) ⟨916670, by rfl⟩ : syracuseStep 1222227 = 1833341) B1833341
theorem B7824995 : Blo 1220928 7824995 := bstep (se 1 (by rfl) ⟨5868746, by rfl⟩ : syracuseStep 7824995 = 11737493) B11737493
theorem B1222243 : Blo 1220928 1222243 := bstep (se 1 (by rfl) ⟨916682, by rfl⟩ : syracuseStep 1222243 = 1833365) B1833365
theorem B1222259 : Blo 1220928 1222259 := bstep (se 1 (by rfl) ⟨916694, by rfl⟩ : syracuseStep 1222259 = 1833389) B1833389
theorem B1222275 : Blo 1220928 1222275 := bstep (se 1 (by rfl) ⟨916706, by rfl⟩ : syracuseStep 1222275 = 1833413) B1833413
theorem B1672849 : Blo 1220928 1672849 := bstep (se 2 (by rfl) ⟨627318, by rfl⟩ : syracuseStep 1672849 = 1254637) B1254637
theorem B1222291 : Blo 1220928 1222291 := bstep (se 1 (by rfl) ⟨916718, by rfl⟩ : syracuseStep 1222291 = 1833437) B1833437
theorem B1222307 : Blo 1220928 1222307 := bstep (se 1 (by rfl) ⟨916730, by rfl⟩ : syracuseStep 1222307 = 1833461) B1833461
theorem B1222323 : Blo 1220928 1222323 := bstep (se 1 (by rfl) ⟨916742, by rfl⟩ : syracuseStep 1222323 = 1833485) B1833485
theorem B1222339 : Blo 1220928 1222339 := bstep (se 1 (by rfl) ⟨916754, by rfl⟩ : syracuseStep 1222339 = 1833509) B1833509
theorem B1222355 : Blo 1220928 1222355 := bstep (se 1 (by rfl) ⟨916766, by rfl⟩ : syracuseStep 1222355 = 1833533) B1833533
theorem B1222371 : Blo 1220928 1222371 := bstep (se 1 (by rfl) ⟨916778, by rfl⟩ : syracuseStep 1222371 = 1833557) B1833557
theorem B1222387 : Blo 1220928 1222387 := bstep (se 1 (by rfl) ⟨916790, by rfl⟩ : syracuseStep 1222387 = 1833581) B1833581
theorem B1222403 : Blo 1220928 1222403 := bstep (se 1 (by rfl) ⟨916802, by rfl⟩ : syracuseStep 1222403 = 1833605) B1833605
theorem B5654285 : Blo 1220928 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B3917585 : Blo 1220928 3917585 := bstep (se 2 (by rfl) ⟨1469094, by rfl⟩ : syracuseStep 3917585 = 2938189) B2938189
theorem B1222419 : Blo 1220928 1222419 := bstep (se 1 (by rfl) ⟨916814, by rfl⟩ : syracuseStep 1222419 = 1833629) B1833629
theorem B1222435 : Blo 1220928 1222435 := bstep (se 1 (by rfl) ⟨916826, by rfl⟩ : syracuseStep 1222435 = 1833653) B1833653
theorem B4122413 : Blo 1220928 4122413 := bstep (se 3 (by rfl) ⟨772952, by rfl⟩ : syracuseStep 4122413 = 1545905) B1545905
theorem B7939889 : Blo 1220928 7939889 := bstep (se 2 (by rfl) ⟨2977458, by rfl⟩ : syracuseStep 7939889 = 5954917) B5954917
theorem B1304371 : Blo 1220928 1304371 := bstep (se 1 (by rfl) ⟨978278, by rfl⟩ : syracuseStep 1304371 = 1956557) B1956557
theorem B1222451 : Blo 1220928 1222451 := bstep (se 1 (by rfl) ⟨916838, by rfl⟩ : syracuseStep 1222451 = 1833677) B1833677
theorem B1222467 : Blo 1220928 1222467 := bstep (se 1 (by rfl) ⟨916850, by rfl⟩ : syracuseStep 1222467 = 1833701) B1833701
theorem B1222483 : Blo 1220928 1222483 := bstep (se 1 (by rfl) ⟨916862, by rfl⟩ : syracuseStep 1222483 = 1833725) B1833725
theorem B4122467 : Blo 1220928 4122467 := bstep (se 1 (by rfl) ⟨3091850, by rfl⟩ : syracuseStep 4122467 = 6183701) B6183701
theorem B1222499 : Blo 1220928 1222499 := bstep (se 1 (by rfl) ⟨916874, by rfl⟩ : syracuseStep 1222499 = 1833749) B1833749
theorem B1222515 : Blo 1220928 1222515 := bstep (se 1 (by rfl) ⟨916886, by rfl⟩ : syracuseStep 1222515 = 1833773) B1833773
theorem B1222531 : Blo 1220928 1222531 := bstep (se 1 (by rfl) ⟨916898, by rfl⟩ : syracuseStep 1222531 = 1833797) B1833797
theorem B1222547 : Blo 1220928 1222547 := bstep (se 1 (by rfl) ⟨916910, by rfl⟩ : syracuseStep 1222547 = 1833821) B1833821
theorem B1222563 : Blo 1220928 1222563 := bstep (se 1 (by rfl) ⟨916922, by rfl⟩ : syracuseStep 1222563 = 1833845) B1833845
theorem B1222579 : Blo 1220928 1222579 := bstep (se 1 (by rfl) ⟨916934, by rfl⟩ : syracuseStep 1222579 = 1833869) B1833869
theorem B1222595 : Blo 1220928 1222595 := bstep (se 1 (by rfl) ⟨916946, by rfl⟩ : syracuseStep 1222595 = 1833893) B1833893
theorem B5220301 : Blo 1220928 5220301 := bstep (se 3 (by rfl) ⟨978806, by rfl⟩ : syracuseStep 5220301 = 1957613) B1957613
theorem B1222611 : Blo 1220928 1222611 := bstep (se 1 (by rfl) ⟨916958, by rfl⟩ : syracuseStep 1222611 = 1833917) B1833917
theorem B1222627 : Blo 1220928 1222627 := bstep (se 1 (by rfl) ⟨916970, by rfl⟩ : syracuseStep 1222627 = 1833941) B1833941
theorem B1222643 : Blo 1220928 1222643 := bstep (se 1 (by rfl) ⟨916982, by rfl⟩ : syracuseStep 1222643 = 1833965) B1833965
theorem B2934787 : Blo 1220928 2934787 := bstep (se 1 (by rfl) ⟨2201090, by rfl⟩ : syracuseStep 2934787 = 4402181) B4402181
theorem B1222659 : Blo 1220928 1222659 := bstep (se 1 (by rfl) ⟨916994, by rfl⟩ : syracuseStep 1222659 = 1833989) B1833989
theorem B1222675 : Blo 1220928 1222675 := bstep (se 1 (by rfl) ⟨917006, by rfl⟩ : syracuseStep 1222675 = 1834013) B1834013
theorem B1222691 : Blo 1220928 1222691 := bstep (se 1 (by rfl) ⟨917018, by rfl⟩ : syracuseStep 1222691 = 1834037) B1834037
theorem B1222707 : Blo 1220928 1222707 := bstep (se 1 (by rfl) ⟨917030, by rfl⟩ : syracuseStep 1222707 = 1834061) B1834061
theorem B17860661 : Blo 1220928 17860661 := bstep (se 5 (by rfl) ⟨837218, by rfl⟩ : syracuseStep 17860661 = 1674437) B1674437
theorem B1222723 : Blo 1220928 1222723 := bstep (se 1 (by rfl) ⟨917042, by rfl⟩ : syracuseStep 1222723 = 1834085) B1834085
theorem B1222739 : Blo 1220928 1222739 := bstep (se 1 (by rfl) ⟨917054, by rfl⟩ : syracuseStep 1222739 = 1834109) B1834109
theorem B2320483 : Blo 1220928 2320483 := bstep (se 1 (by rfl) ⟨1740362, by rfl⟩ : syracuseStep 2320483 = 3480725) B3480725
theorem B1222755 : Blo 1220928 1222755 := bstep (se 1 (by rfl) ⟨917066, by rfl⟩ : syracuseStep 1222755 = 1834133) B1834133
theorem B3090545 : Blo 1220928 3090545 := bstep (se 2 (by rfl) ⟨1158954, by rfl⟩ : syracuseStep 3090545 = 2317909) B2317909
theorem B4122737 : Blo 1220928 4122737 := bstep (se 2 (by rfl) ⟨1546026, by rfl⟩ : syracuseStep 4122737 = 3092053) B3092053
theorem B1222771 : Blo 1220928 1222771 := bstep (se 1 (by rfl) ⟨917078, by rfl⟩ : syracuseStep 1222771 = 1834157) B1834157
theorem B1222787 : Blo 1220928 1222787 := bstep (se 1 (by rfl) ⟨917090, by rfl⟩ : syracuseStep 1222787 = 1834181) B1834181
theorem B1222803 : Blo 1220928 1222803 := bstep (se 1 (by rfl) ⟨917102, by rfl⟩ : syracuseStep 1222803 = 1834205) B1834205
theorem B3090595 : Blo 1220928 3090595 := bstep (se 1 (by rfl) ⟨2317946, by rfl⟩ : syracuseStep 3090595 = 4635893) B4635893
theorem B1222819 : Blo 1220928 1222819 := bstep (se 1 (by rfl) ⟨917114, by rfl⟩ : syracuseStep 1222819 = 1834229) B1834229
theorem B1222835 : Blo 1220928 1222835 := bstep (se 1 (by rfl) ⟨917126, by rfl⟩ : syracuseStep 1222835 = 1834253) B1834253
theorem B1222851 : Blo 1220928 1222851 := bstep (se 1 (by rfl) ⟨917138, by rfl⟩ : syracuseStep 1222851 = 1834277) B1834277
theorem B1222867 : Blo 1220928 1222867 := bstep (se 1 (by rfl) ⟨917150, by rfl⟩ : syracuseStep 1222867 = 1834301) B1834301
theorem B1222883 : Blo 1220928 1222883 := bstep (se 1 (by rfl) ⟨917162, by rfl⟩ : syracuseStep 1222883 = 1834325) B1834325
theorem B1222899 : Blo 1220928 1222899 := bstep (se 1 (by rfl) ⟨917174, by rfl⟩ : syracuseStep 1222899 = 1834349) B1834349
theorem B2320643 : Blo 1220928 2320643 := bstep (se 1 (by rfl) ⟨1740482, by rfl⟩ : syracuseStep 2320643 = 3480965) B3480965
theorem B1222915 : Blo 1220928 1222915 := bstep (se 1 (by rfl) ⟨917186, by rfl⟩ : syracuseStep 1222915 = 1834373) B1834373
theorem B3713293 : Blo 1220928 3713293 := bstep (se 3 (by rfl) ⟨696242, by rfl⟩ : syracuseStep 3713293 = 1392485) B1392485
theorem B3090737 : Blo 1220928 3090737 := bstep (se 2 (by rfl) ⟨1159026, by rfl⟩ : syracuseStep 3090737 = 2318053) B2318053
theorem B1739075 : Blo 1220928 1739075 := bstep (se 1 (by rfl) ⟨1304306, by rfl⟩ : syracuseStep 1739075 = 2608613) B2608613
theorem B1468739 : Blo 1220928 1468739 := bstep (se 1 (by rfl) ⟨1101554, by rfl⟩ : syracuseStep 1468739 = 2203109) B2203109
theorem B2091377 : Blo 1220928 2091377 := bstep (se 2 (by rfl) ⟨784266, by rfl⟩ : syracuseStep 2091377 = 1568533) B1568533
theorem B6187427 : Blo 1220928 6187427 := bstep (se 1 (by rfl) ⟨4640570, by rfl⟩ : syracuseStep 6187427 = 9281141) B9281141
theorem B44616133 : Blo 1220928 44616133 := bstep (se 4 (by rfl) ⟨4182762, by rfl⟩ : syracuseStep 44616133 = 8365525) B8365525
theorem B3713489 : Blo 1220928 3713489 := bstep (se 2 (by rfl) ⟨1392558, by rfl⟩ : syracuseStep 3713489 = 2785117) B2785117
theorem B7432717 : Blo 1220928 7432717 := bstep (se 3 (by rfl) ⟨1393634, by rfl⟩ : syracuseStep 7432717 = 2787269) B2787269
theorem B4123277 : Blo 1220928 4123277 := bstep (se 3 (by rfl) ⟨773114, by rfl⟩ : syracuseStep 4123277 = 1546229) B1546229
theorem B16714421 : Blo 1220928 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B4123331 : Blo 1220928 4123331 := bstep (se 1 (by rfl) ⟨3092498, by rfl⟩ : syracuseStep 4123331 = 6184997) B6184997
theorem B4950733 : Blo 1220928 4950733 := bstep (se 3 (by rfl) ⟨928262, by rfl⟩ : syracuseStep 4950733 = 1856525) B1856525
theorem B1673939 : Blo 1220928 1673939 := bstep (se 1 (by rfl) ⟨1255454, by rfl⟩ : syracuseStep 1673939 = 2510909) B2510909
theorem B2788163 : Blo 1220928 2788163 := bstep (se 1 (by rfl) ⟨2091122, by rfl⟩ : syracuseStep 2788163 = 4182245) B4182245
theorem B1305443 : Blo 1220928 1305443 := bstep (se 1 (by rfl) ⟨979082, by rfl⟩ : syracuseStep 1305443 = 1958165) B1958165
theorem B2747249 : Blo 1220928 2747249 := bstep (se 2 (by rfl) ⟨1030218, by rfl⟩ : syracuseStep 2747249 = 2060437) B2060437
theorem B2747267 : Blo 1220928 2747267 := bstep (se 1 (by rfl) ⟨2060450, by rfl⟩ : syracuseStep 2747267 = 4120901) B4120901
theorem B1739713 : Blo 1220928 1739713 := bstep (se 2 (by rfl) ⟨652392, by rfl⟩ : syracuseStep 1739713 = 1304785) B1304785
theorem B4123601 : Blo 1220928 4123601 := bstep (se 2 (by rfl) ⟨1546350, by rfl⟩ : syracuseStep 4123601 = 3092701) B3092701
theorem B5221361 : Blo 1220928 5221361 := bstep (se 2 (by rfl) ⟨1958010, by rfl⟩ : syracuseStep 5221361 = 3916021) B3916021
theorem B1739827 : Blo 1220928 1739827 := bstep (se 1 (by rfl) ⟨1304870, by rfl⟩ : syracuseStep 1739827 = 2609741) B2609741
theorem B18091061 : Blo 1220928 18091061 := bstep (se 5 (by rfl) ⟨848018, by rfl⟩ : syracuseStep 18091061 = 1696037) B1696037
theorem B2608195 : Blo 1220928 2608195 := bstep (se 1 (by rfl) ⟨1956146, by rfl⟩ : syracuseStep 2608195 = 3912293) B3912293
theorem B59477105 : Blo 1220928 59477105 := bstep (se 2 (by rfl) ⟨22303914, by rfl⟩ : syracuseStep 59477105 = 44607829) B44607829
theorem B2747537 : Blo 1220928 2747537 := bstep (se 2 (by rfl) ⟨1030326, by rfl⟩ : syracuseStep 2747537 = 2060653) B2060653
theorem B2747555 : Blo 1220928 2747555 := bstep (se 1 (by rfl) ⟨2060666, by rfl⟩ : syracuseStep 2747555 = 4121333) B4121333
theorem B4639949 : Blo 1220928 4639949 := bstep (se 3 (by rfl) ⟨869990, by rfl⟩ : syracuseStep 4639949 = 1739981) B1739981
theorem B6188237 : Blo 1220928 6188237 := bstep (se 3 (by rfl) ⟨1160294, by rfl⟩ : syracuseStep 6188237 = 2320589) B2320589
theorem B2936017 : Blo 1220928 2936017 := bstep (se 2 (by rfl) ⟨1101006, by rfl⟩ : syracuseStep 2936017 = 2202013) B2202013
theorem B7433477 : Blo 1220928 7433477 := bstep (se 4 (by rfl) ⟨696888, by rfl⟩ : syracuseStep 7433477 = 1393777) B1393777
theorem B3091729 : Blo 1220928 3091729 := bstep (se 2 (by rfl) ⟨1159398, by rfl⟩ : syracuseStep 3091729 = 2318797) B2318797
theorem B2788721 : Blo 1220928 2788721 := bstep (se 2 (by rfl) ⟨1045770, by rfl⟩ : syracuseStep 2788721 = 2091541) B2091541
theorem B2747825 : Blo 1220928 2747825 := bstep (se 2 (by rfl) ⟨1030434, by rfl⟩ : syracuseStep 2747825 = 2060869) B2060869
theorem B2747843 : Blo 1220928 2747843 := bstep (se 1 (by rfl) ⟨2060882, by rfl⟩ : syracuseStep 2747843 = 4121765) B4121765
theorem B4124141 : Blo 1220928 4124141 := bstep (se 3 (by rfl) ⟨773276, by rfl⟩ : syracuseStep 4124141 = 1546553) B1546553
theorem B1322483 : Blo 1220928 1322483 := bstep (se 1 (by rfl) ⟨991862, by rfl⟩ : syracuseStep 1322483 = 1983725) B1983725
theorem B3092003 : Blo 1220928 3092003 := bstep (se 1 (by rfl) ⟨2319002, by rfl⟩ : syracuseStep 3092003 = 4638005) B4638005
theorem B4124195 : Blo 1220928 4124195 := bstep (se 1 (by rfl) ⟨3093146, by rfl⟩ : syracuseStep 4124195 = 6186293) B6186293
theorem B6958669 : Blo 1220928 6958669 := bstep (se 3 (by rfl) ⟨1304750, by rfl⟩ : syracuseStep 6958669 = 2609501) B2609501
theorem B2748113 : Blo 1220928 2748113 := bstep (se 2 (by rfl) ⟨1030542, by rfl⟩ : syracuseStep 2748113 = 2061085) B2061085
theorem B2748131 : Blo 1220928 2748131 := bstep (se 1 (by rfl) ⟨2061098, by rfl⟩ : syracuseStep 2748131 = 4122197) B4122197
theorem B3092195 : Blo 1220928 3092195 := bstep (se 1 (by rfl) ⟨2319146, by rfl⟩ : syracuseStep 3092195 = 4638293) B4638293
theorem B5869361 : Blo 1220928 5869361 := bstep (se 2 (by rfl) ⟨2201010, by rfl⟩ : syracuseStep 5869361 = 4402021) B4402021
theorem B4124465 : Blo 1220928 4124465 := bstep (se 2 (by rfl) ⟨1546674, by rfl⟩ : syracuseStep 4124465 = 3093349) B3093349
theorem B9277253 : Blo 1220928 9277253 := bstep (se 4 (by rfl) ⟨869742, by rfl⟩ : syracuseStep 9277253 = 1739485) B1739485
theorem B3477421 : Blo 1220928 3477421 := bstep (se 3 (by rfl) ⟨652016, by rfl⟩ : syracuseStep 3477421 = 1304033) B1304033
theorem B2748401 : Blo 1220928 2748401 := bstep (se 2 (by rfl) ⟨1030650, by rfl⟩ : syracuseStep 2748401 = 2061301) B2061301
theorem B4640753 : Blo 1220928 4640753 := bstep (se 2 (by rfl) ⟨1740282, by rfl⟩ : syracuseStep 4640753 = 3480565) B3480565
theorem B2748419 : Blo 1220928 2748419 := bstep (se 1 (by rfl) ⟨2061314, by rfl⟩ : syracuseStep 2748419 = 4122629) B4122629
theorem B3715121 : Blo 1220928 3715121 := bstep (se 2 (by rfl) ⟨1393170, by rfl⟩ : syracuseStep 3715121 = 2786341) B2786341
theorem B2060417 : Blo 1220928 2060417 := bstep (se 2 (by rfl) ⟨772656, by rfl⟩ : syracuseStep 2060417 = 1545313) B1545313
theorem B3477649 : Blo 1220928 3477649 := bstep (se 2 (by rfl) ⟨1304118, by rfl⟩ : syracuseStep 3477649 = 2608237) B2608237
theorem B3715217 : Blo 1220928 3715217 := bstep (se 2 (by rfl) ⟨1393206, by rfl⟩ : syracuseStep 3715217 = 2786413) B2786413
theorem B7434467 : Blo 1220928 7434467 := bstep (se 1 (by rfl) ⟨5575850, by rfl⟩ : syracuseStep 7434467 = 11151701) B11151701
theorem B3911921 : Blo 1220928 3911921 := bstep (se 2 (by rfl) ⟨1466970, by rfl⟩ : syracuseStep 3911921 = 2933941) B2933941
theorem B2060545 : Blo 1220928 2060545 := bstep (se 2 (by rfl) ⟨772704, by rfl⟩ : syracuseStep 2060545 = 1545409) B1545409
theorem B2748689 : Blo 1220928 2748689 := bstep (se 2 (by rfl) ⟨1030758, by rfl⟩ : syracuseStep 2748689 = 2061517) B2061517
theorem B2609425 : Blo 1220928 2609425 := bstep (se 2 (by rfl) ⟨978534, by rfl⟩ : syracuseStep 2609425 = 1957069) B1957069
theorem B2060579 : Blo 1220928 2060579 := bstep (se 1 (by rfl) ⟨1545434, by rfl⟩ : syracuseStep 2060579 = 3090869) B3090869
theorem B2748707 : Blo 1220928 2748707 := bstep (se 1 (by rfl) ⟨2061530, by rfl⟩ : syracuseStep 2748707 = 4123061) B4123061
theorem B3477809 : Blo 1220928 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B5288269 : Blo 1220928 5288269 := bstep (se 3 (by rfl) ⟨991550, by rfl⟩ : syracuseStep 5288269 = 1983101) B1983101
theorem B4125005 : Blo 1220928 4125005 := bstep (se 3 (by rfl) ⟨773438, by rfl⟩ : syracuseStep 4125005 = 1546877) B1546877
theorem B9286001 : Blo 1220928 9286001 := bstep (se 2 (by rfl) ⟨3482250, by rfl⟩ : syracuseStep 9286001 = 6964501) B6964501
theorem B1741171 : Blo 1220928 1741171 := bstep (se 1 (by rfl) ⟨1305878, by rfl⟩ : syracuseStep 1741171 = 2611757) B2611757
theorem B4125059 : Blo 1220928 4125059 := bstep (se 1 (by rfl) ⟨3093794, by rfl⟩ : syracuseStep 4125059 = 6187589) B6187589
theorem B2060707 : Blo 1220928 2060707 := bstep (se 1 (by rfl) ⟨1545530, by rfl⟩ : syracuseStep 2060707 = 3091061) B3091061
theorem B3477923 : Blo 1220928 3477923 := bstep (se 1 (by rfl) ⟨2608442, by rfl⟩ : syracuseStep 3477923 = 5216885) B5216885
theorem B1831409 : Blo 1220928 1831409 := bstep (se 2 (by rfl) ⟨686778, by rfl⟩ : syracuseStep 1831409 = 1373557) B1373557
theorem B1831427 : Blo 1220928 1831427 := bstep (se 1 (by rfl) ⟨1373570, by rfl⟩ : syracuseStep 1831427 = 2747141) B2747141
theorem B1831457 : Blo 1220928 1831457 := bstep (se 2 (by rfl) ⟨686796, by rfl⟩ : syracuseStep 1831457 = 1373593) B1373593
theorem B2060849 : Blo 1220928 2060849 := bstep (se 2 (by rfl) ⟨772818, by rfl⟩ : syracuseStep 2060849 = 1545637) B1545637
theorem B1831475 : Blo 1220928 1831475 := bstep (se 1 (by rfl) ⟨1373606, by rfl⟩ : syracuseStep 1831475 = 2747213) B2747213
theorem B2748977 : Blo 1220928 2748977 := bstep (se 2 (by rfl) ⟨1030866, by rfl⟩ : syracuseStep 2748977 = 2061733) B2061733
theorem B2748995 : Blo 1220928 2748995 := bstep (se 1 (by rfl) ⟨2061746, by rfl⟩ : syracuseStep 2748995 = 4123493) B4123493
theorem B1831505 : Blo 1220928 1831505 := bstep (se 2 (by rfl) ⟨686814, by rfl⟩ : syracuseStep 1831505 = 1373629) B1373629
theorem B1831523 : Blo 1220928 1831523 := bstep (se 1 (by rfl) ⟨1373642, by rfl⟩ : syracuseStep 1831523 = 2747285) B2747285
theorem B1831553 : Blo 1220928 1831553 := bstep (se 2 (by rfl) ⟨686832, by rfl⟩ : syracuseStep 1831553 = 1373665) B1373665
theorem B4641421 : Blo 1220928 4641421 := bstep (se 3 (by rfl) ⟨870266, by rfl⟩ : syracuseStep 4641421 = 1740533) B1740533
theorem B3093137 : Blo 1220928 3093137 := bstep (se 2 (by rfl) ⟨1159926, by rfl⟩ : syracuseStep 3093137 = 2319853) B2319853
theorem B4125329 : Blo 1220928 4125329 := bstep (se 2 (by rfl) ⟨1546998, by rfl⟩ : syracuseStep 4125329 = 3093997) B3093997
theorem B1831571 : Blo 1220928 1831571 := bstep (se 1 (by rfl) ⟨1373678, by rfl⟩ : syracuseStep 1831571 = 2747357) B2747357
theorem B1831601 : Blo 1220928 1831601 := bstep (se 2 (by rfl) ⟨686850, by rfl⟩ : syracuseStep 1831601 = 1373701) B1373701
theorem B2060977 : Blo 1220928 2060977 := bstep (se 2 (by rfl) ⟨772866, by rfl⟩ : syracuseStep 2060977 = 1545733) B1545733
theorem B1831619 : Blo 1220928 1831619 := bstep (se 1 (by rfl) ⟨1373714, by rfl⟩ : syracuseStep 1831619 = 2747429) B2747429
theorem B3093187 : Blo 1220928 3093187 := bstep (se 1 (by rfl) ⟨2319890, by rfl⟩ : syracuseStep 3093187 = 4639781) B4639781
theorem B2061011 : Blo 1220928 2061011 := bstep (se 1 (by rfl) ⟨1545758, by rfl⟩ : syracuseStep 2061011 = 3091517) B3091517
theorem B1831649 : Blo 1220928 1831649 := bstep (se 2 (by rfl) ⟨686868, by rfl⟩ : syracuseStep 1831649 = 1373737) B1373737
theorem B1831667 : Blo 1220928 1831667 := bstep (se 1 (by rfl) ⟨1373750, by rfl⟩ : syracuseStep 1831667 = 2747501) B2747501
theorem B1831697 : Blo 1220928 1831697 := bstep (se 2 (by rfl) ⟨686886, by rfl⟩ : syracuseStep 1831697 = 1373773) B1373773
theorem B1831715 : Blo 1220928 1831715 := bstep (se 1 (by rfl) ⟨1373786, by rfl⟩ : syracuseStep 1831715 = 2747573) B2747573
theorem B1831745 : Blo 1220928 1831745 := bstep (se 2 (by rfl) ⟨686904, by rfl⟩ : syracuseStep 1831745 = 1373809) B1373809
theorem B2749265 : Blo 1220928 2749265 := bstep (se 2 (by rfl) ⟨1030974, by rfl⟩ : syracuseStep 2749265 = 2061949) B2061949
theorem B3093329 : Blo 1220928 3093329 := bstep (se 2 (by rfl) ⟨1159998, by rfl⟩ : syracuseStep 3093329 = 2319997) B2319997
theorem B1831763 : Blo 1220928 1831763 := bstep (se 1 (by rfl) ⟨1373822, by rfl⟩ : syracuseStep 1831763 = 2747645) B2747645
theorem B2061139 : Blo 1220928 2061139 := bstep (se 1 (by rfl) ⟨1545854, by rfl⟩ : syracuseStep 2061139 = 3091709) B3091709
theorem B2749283 : Blo 1220928 2749283 := bstep (se 1 (by rfl) ⟨2061962, by rfl⟩ : syracuseStep 2749283 = 4123925) B4123925
theorem B1831793 : Blo 1220928 1831793 := bstep (se 2 (by rfl) ⟨686922, by rfl⟩ : syracuseStep 1831793 = 1373845) B1373845
theorem B1651585 : Blo 1220928 1651585 := bstep (se 2 (by rfl) ⟨619344, by rfl⟩ : syracuseStep 1651585 = 1238689) B1238689
theorem B1831811 : Blo 1220928 1831811 := bstep (se 1 (by rfl) ⟨1373858, by rfl⟩ : syracuseStep 1831811 = 2747717) B2747717
theorem B1831841 : Blo 1220928 1831841 := bstep (se 2 (by rfl) ⟨686940, by rfl⟩ : syracuseStep 1831841 = 1373881) B1373881
theorem B2610083 : Blo 1220928 2610083 := bstep (se 1 (by rfl) ⟨1957562, by rfl⟩ : syracuseStep 2610083 = 3915125) B3915125
theorem B1831859 : Blo 1220928 1831859 := bstep (se 1 (by rfl) ⟨1373894, by rfl⟩ : syracuseStep 1831859 = 2747789) B2747789
theorem B59413445 : Blo 1220928 59413445 := bstep (se 4 (by rfl) ⟨5570010, by rfl⟩ : syracuseStep 59413445 = 11140021) B11140021
theorem B1831889 : Blo 1220928 1831889 := bstep (se 2 (by rfl) ⟨686958, by rfl⟩ : syracuseStep 1831889 = 1373917) B1373917
theorem B2061281 : Blo 1220928 2061281 := bstep (se 2 (by rfl) ⟨772980, by rfl⟩ : syracuseStep 2061281 = 1545961) B1545961
theorem B1831907 : Blo 1220928 1831907 := bstep (se 1 (by rfl) ⟨1373930, by rfl⟩ : syracuseStep 1831907 = 2747861) B2747861
theorem B1831937 : Blo 1220928 1831937 := bstep (se 2 (by rfl) ⟨686976, by rfl⟩ : syracuseStep 1831937 = 1373953) B1373953
theorem B1831955 : Blo 1220928 1831955 := bstep (se 1 (by rfl) ⟨1373966, by rfl⟩ : syracuseStep 1831955 = 2747933) B2747933
theorem B1831985 : Blo 1220928 1831985 := bstep (se 2 (by rfl) ⟨686994, by rfl⟩ : syracuseStep 1831985 = 1373989) B1373989
theorem B1832003 : Blo 1220928 1832003 := bstep (se 1 (by rfl) ⟨1374002, by rfl⟩ : syracuseStep 1832003 = 2748005) B2748005
theorem B1832033 : Blo 1220928 1832033 := bstep (se 2 (by rfl) ⟨687012, by rfl⟩ : syracuseStep 1832033 = 1374025) B1374025
theorem B2061409 : Blo 1220928 2061409 := bstep (se 2 (by rfl) ⟨773028, by rfl⟩ : syracuseStep 2061409 = 1546057) B1546057
theorem B2749553 : Blo 1220928 2749553 := bstep (se 2 (by rfl) ⟨1031082, by rfl⟩ : syracuseStep 2749553 = 2062165) B2062165
theorem B1832051 : Blo 1220928 1832051 := bstep (se 1 (by rfl) ⟨1374038, by rfl⟩ : syracuseStep 1832051 = 2748077) B2748077
theorem B2061443 : Blo 1220928 2061443 := bstep (se 1 (by rfl) ⟨1546082, by rfl⟩ : syracuseStep 2061443 = 3092165) B3092165
theorem B2749571 : Blo 1220928 2749571 := bstep (se 1 (by rfl) ⟨2062178, by rfl⟩ : syracuseStep 2749571 = 4124357) B4124357
theorem B5289101 : Blo 1220928 5289101 := bstep (se 3 (by rfl) ⟨991706, by rfl⟩ : syracuseStep 5289101 = 1983413) B1983413
theorem B1832081 : Blo 1220928 1832081 := bstep (se 2 (by rfl) ⟨687030, by rfl⟩ : syracuseStep 1832081 = 1374061) B1374061
theorem B1832099 : Blo 1220928 1832099 := bstep (se 1 (by rfl) ⟨1374074, by rfl⟩ : syracuseStep 1832099 = 2748149) B2748149
theorem B4125869 : Blo 1220928 4125869 := bstep (se 3 (by rfl) ⟨773600, by rfl⟩ : syracuseStep 4125869 = 1547201) B1547201
theorem B1832129 : Blo 1220928 1832129 := bstep (se 2 (by rfl) ⟨687048, by rfl⟩ : syracuseStep 1832129 = 1374097) B1374097
theorem B1832147 : Blo 1220928 1832147 := bstep (se 1 (by rfl) ⟨1374110, by rfl⟩ : syracuseStep 1832147 = 2748221) B2748221
theorem B4125923 : Blo 1220928 4125923 := bstep (se 1 (by rfl) ⟨3094442, by rfl⟩ : syracuseStep 4125923 = 6188885) B6188885
theorem B1832177 : Blo 1220928 1832177 := bstep (se 2 (by rfl) ⟨687066, by rfl⟩ : syracuseStep 1832177 = 1374133) B1374133
theorem B1545475 : Blo 1220928 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B1832195 : Blo 1220928 1832195 := bstep (se 1 (by rfl) ⟨1374146, by rfl⟩ : syracuseStep 1832195 = 2748293) B2748293
theorem B2061571 : Blo 1220928 2061571 := bstep (se 1 (by rfl) ⟨1546178, by rfl⟩ : syracuseStep 2061571 = 3092357) B3092357
theorem B1832225 : Blo 1220928 1832225 := bstep (se 2 (by rfl) ⟨687084, by rfl⟩ : syracuseStep 1832225 = 1374169) B1374169
theorem B1832243 : Blo 1220928 1832243 := bstep (se 1 (by rfl) ⟨1374182, by rfl⟩ : syracuseStep 1832243 = 2748365) B2748365
theorem B1832273 : Blo 1220928 1832273 := bstep (se 2 (by rfl) ⟨687102, by rfl⟩ : syracuseStep 1832273 = 1374205) B1374205
theorem B6182243 : Blo 1220928 6182243 := bstep (se 1 (by rfl) ⟨4636682, by rfl⟩ : syracuseStep 6182243 = 9273365) B9273365
theorem B1545571 : Blo 1220928 1545571 := bstep (se 1 (by rfl) ⟨1159178, by rfl⟩ : syracuseStep 1545571 = 2318357) B2318357
theorem B1832291 : Blo 1220928 1832291 := bstep (se 1 (by rfl) ⟨1374218, by rfl⟩ : syracuseStep 1832291 = 2748437) B2748437
theorem B1832321 : Blo 1220928 1832321 := bstep (se 2 (by rfl) ⟨687120, by rfl⟩ : syracuseStep 1832321 = 1374241) B1374241
theorem B3478925 : Blo 1220928 3478925 := bstep (se 3 (by rfl) ⟨652298, by rfl⟩ : syracuseStep 3478925 = 1304597) B1304597
theorem B2061713 : Blo 1220928 2061713 := bstep (se 2 (by rfl) ⟨773142, by rfl⟩ : syracuseStep 2061713 = 1546285) B1546285
theorem B1856915 : Blo 1220928 1856915 := bstep (se 1 (by rfl) ⟨1392686, by rfl⟩ : syracuseStep 1856915 = 2785373) B2785373
theorem B1832339 : Blo 1220928 1832339 := bstep (se 1 (by rfl) ⟨1374254, by rfl⟩ : syracuseStep 1832339 = 2748509) B2748509
theorem B2749841 : Blo 1220928 2749841 := bstep (se 2 (by rfl) ⟨1031190, by rfl⟩ : syracuseStep 2749841 = 2062381) B2062381
theorem B2749859 : Blo 1220928 2749859 := bstep (se 1 (by rfl) ⟨2062394, by rfl⟩ : syracuseStep 2749859 = 4124789) B4124789
theorem B4642211 : Blo 1220928 4642211 := bstep (se 1 (by rfl) ⟨3481658, by rfl⟩ : syracuseStep 4642211 = 6963317) B6963317
theorem B1832369 : Blo 1220928 1832369 := bstep (se 2 (by rfl) ⟨687138, by rfl⟩ : syracuseStep 1832369 = 1374277) B1374277
theorem B7828913 : Blo 1220928 7828913 := bstep (se 2 (by rfl) ⟨2935842, by rfl⟩ : syracuseStep 7828913 = 5871685) B5871685
theorem B1832387 : Blo 1220928 1832387 := bstep (se 1 (by rfl) ⟨1374290, by rfl⟩ : syracuseStep 1832387 = 2748581) B2748581
theorem B1832417 : Blo 1220928 1832417 := bstep (se 2 (by rfl) ⟨687156, by rfl⟩ : syracuseStep 1832417 = 1374313) B1374313
theorem B4126193 : Blo 1220928 4126193 := bstep (se 2 (by rfl) ⟨1547322, by rfl⟩ : syracuseStep 4126193 = 3094645) B3094645
theorem B1373683 : Blo 1220928 1373683 := bstep (se 1 (by rfl) ⟨1030262, by rfl⟩ : syracuseStep 1373683 = 2060525) B2060525
theorem B1832435 : Blo 1220928 1832435 := bstep (se 1 (by rfl) ⟨1374326, by rfl⟩ : syracuseStep 1832435 = 2748653) B2748653
theorem B6960653 : Blo 1220928 6960653 := bstep (se 3 (by rfl) ⟨1305122, by rfl⟩ : syracuseStep 6960653 = 2610245) B2610245
theorem B1832465 : Blo 1220928 1832465 := bstep (se 2 (by rfl) ⟨687174, by rfl⟩ : syracuseStep 1832465 = 1374349) B1374349
theorem B2061841 : Blo 1220928 2061841 := bstep (se 2 (by rfl) ⟨773190, by rfl⟩ : syracuseStep 2061841 = 1546381) B1546381
theorem B1832483 : Blo 1220928 1832483 := bstep (se 1 (by rfl) ⟨1374362, by rfl⟩ : syracuseStep 1832483 = 2748725) B2748725
theorem B2061875 : Blo 1220928 2061875 := bstep (se 1 (by rfl) ⟨1546406, by rfl⟩ : syracuseStep 2061875 = 3092813) B3092813
theorem B25081397 : Blo 1220928 25081397 := bstep (se 5 (by rfl) ⟨1175690, by rfl⟩ : syracuseStep 25081397 = 2351381) B2351381
theorem B1832513 : Blo 1220928 1832513 := bstep (se 2 (by rfl) ⟨687192, by rfl⟩ : syracuseStep 1832513 = 1374385) B1374385
theorem B3479107 : Blo 1220928 3479107 := bstep (se 1 (by rfl) ⟨2609330, by rfl⟩ : syracuseStep 3479107 = 5218661) B5218661
theorem B1832531 : Blo 1220928 1832531 := bstep (se 1 (by rfl) ⟨1374398, by rfl⟩ : syracuseStep 1832531 = 2748797) B2748797
theorem B11753059 : Blo 1220928 11753059 := bstep (se 1 (by rfl) ⟨8814794, by rfl⟩ : syracuseStep 11753059 = 17629589) B17629589
theorem B1832561 : Blo 1220928 1832561 := bstep (se 2 (by rfl) ⟨687210, by rfl⟩ : syracuseStep 1832561 = 1374421) B1374421
theorem B6035057 : Blo 1220928 6035057 := bstep (se 2 (by rfl) ⟨2263146, by rfl⟩ : syracuseStep 6035057 = 4526293) B4526293
theorem B1373827 : Blo 1220928 1373827 := bstep (se 1 (by rfl) ⟨1030370, by rfl⟩ : syracuseStep 1373827 = 2060741) B2060741
theorem B1832579 : Blo 1220928 1832579 := bstep (se 1 (by rfl) ⟨1374434, by rfl⟩ : syracuseStep 1832579 = 2748869) B2748869
theorem B11744909 : Blo 1220928 11744909 := bstep (se 3 (by rfl) ⟨2202170, by rfl⟩ : syracuseStep 11744909 = 4404341) B4404341
theorem B1832609 : Blo 1220928 1832609 := bstep (se 2 (by rfl) ⟨687228, by rfl⟩ : syracuseStep 1832609 = 1374457) B1374457
theorem B2750129 : Blo 1220928 2750129 := bstep (se 2 (by rfl) ⟨1031298, by rfl⟩ : syracuseStep 2750129 = 2062597) B2062597
theorem B1832627 : Blo 1220928 1832627 := bstep (se 1 (by rfl) ⟨1374470, by rfl⟩ : syracuseStep 1832627 = 2748941) B2748941
theorem B2062003 : Blo 1220928 2062003 := bstep (se 1 (by rfl) ⟨1546502, by rfl⟩ : syracuseStep 2062003 = 3093005) B3093005
theorem B2750147 : Blo 1220928 2750147 := bstep (se 1 (by rfl) ⟨2062610, by rfl⟩ : syracuseStep 2750147 = 4125221) B4125221
theorem B1832657 : Blo 1220928 1832657 := bstep (se 2 (by rfl) ⟨687246, by rfl⟩ : syracuseStep 1832657 = 1374493) B1374493
theorem B1832675 : Blo 1220928 1832675 := bstep (se 1 (by rfl) ⟨1374506, by rfl⟩ : syracuseStep 1832675 = 2749013) B2749013
theorem B3479267 : Blo 1220928 3479267 := bstep (se 1 (by rfl) ⟨2609450, by rfl⟩ : syracuseStep 3479267 = 5218901) B5218901
theorem B2610929 : Blo 1220928 2610929 := bstep (se 2 (by rfl) ⟨979098, by rfl⟩ : syracuseStep 2610929 = 1958197) B1958197
theorem B1832705 : Blo 1220928 1832705 := bstep (se 2 (by rfl) ⟨687264, by rfl⟩ : syracuseStep 1832705 = 1374529) B1374529
theorem B1373971 : Blo 1220928 1373971 := bstep (se 1 (by rfl) ⟨1030478, by rfl⟩ : syracuseStep 1373971 = 2060957) B2060957
theorem B1832723 : Blo 1220928 1832723 := bstep (se 1 (by rfl) ⟨1374542, by rfl⟩ : syracuseStep 1832723 = 2749085) B2749085
theorem B2201393 : Blo 1220928 2201393 := bstep (se 2 (by rfl) ⟨825522, by rfl⟩ : syracuseStep 2201393 = 1651045) B1651045
theorem B1832753 : Blo 1220928 1832753 := bstep (se 2 (by rfl) ⟨687282, by rfl⟩ : syracuseStep 1832753 = 1374565) B1374565
theorem B3094321 : Blo 1220928 3094321 := bstep (se 2 (by rfl) ⟨1160370, by rfl⟩ : syracuseStep 3094321 = 2320741) B2320741
theorem B2062145 : Blo 1220928 2062145 := bstep (se 2 (by rfl) ⟨773304, by rfl⟩ : syracuseStep 2062145 = 1546609) B1546609
theorem B1832771 : Blo 1220928 1832771 := bstep (se 1 (by rfl) ⟨1374578, by rfl⟩ : syracuseStep 1832771 = 2749157) B2749157
theorem B1546067 : Blo 1220928 1546067 := bstep (se 1 (by rfl) ⟨1159550, by rfl⟩ : syracuseStep 1546067 = 2319101) B2319101
theorem B1832801 : Blo 1220928 1832801 := bstep (se 2 (by rfl) ⟨687300, by rfl⟩ : syracuseStep 1832801 = 1374601) B1374601
theorem B1832819 : Blo 1220928 1832819 := bstep (se 1 (by rfl) ⟨1374614, by rfl⟩ : syracuseStep 1832819 = 2749229) B2749229
theorem B29718413 : Blo 1220928 29718413 := bstep (se 3 (by rfl) ⟨5572202, by rfl⟩ : syracuseStep 29718413 = 11144405) B11144405
theorem B1832849 : Blo 1220928 1832849 := bstep (se 2 (by rfl) ⟨687318, by rfl⟩ : syracuseStep 1832849 = 1374637) B1374637
theorem B1374115 : Blo 1220928 1374115 := bstep (se 1 (by rfl) ⟨1030586, by rfl⟩ : syracuseStep 1374115 = 2061173) B2061173
theorem B1832867 : Blo 1220928 1832867 := bstep (se 1 (by rfl) ⟨1374650, by rfl⟩ : syracuseStep 1832867 = 2749301) B2749301
theorem B1832897 : Blo 1220928 1832897 := bstep (se 2 (by rfl) ⟨687336, by rfl⟩ : syracuseStep 1832897 = 1374673) B1374673
theorem B2062273 : Blo 1220928 2062273 := bstep (se 2 (by rfl) ⟨773352, by rfl⟩ : syracuseStep 2062273 = 1546705) B1546705
theorem B2750417 : Blo 1220928 2750417 := bstep (se 2 (by rfl) ⟨1031406, by rfl⟩ : syracuseStep 2750417 = 2062813) B2062813
theorem B1832915 : Blo 1220928 1832915 := bstep (se 1 (by rfl) ⟨1374686, by rfl⟩ : syracuseStep 1832915 = 2749373) B2749373
theorem B8353763 : Blo 1220928 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B2062307 : Blo 1220928 2062307 := bstep (se 1 (by rfl) ⟨1546730, by rfl⟩ : syracuseStep 2062307 = 3093461) B3093461
theorem B2750435 : Blo 1220928 2750435 := bstep (se 1 (by rfl) ⟨2062826, by rfl⟩ : syracuseStep 2750435 = 4125653) B4125653
theorem B1832945 : Blo 1220928 1832945 := bstep (se 2 (by rfl) ⟨687354, by rfl⟩ : syracuseStep 1832945 = 1374709) B1374709
theorem B1832963 : Blo 1220928 1832963 := bstep (se 1 (by rfl) ⟨1374722, by rfl⟩ : syracuseStep 1832963 = 2749445) B2749445
theorem B4126733 : Blo 1220928 4126733 := bstep (se 3 (by rfl) ⟨773762, by rfl⟩ : syracuseStep 4126733 = 1547525) B1547525
theorem B1832993 : Blo 1220928 1832993 := bstep (se 2 (by rfl) ⟨687372, by rfl⟩ : syracuseStep 1832993 = 1374745) B1374745
theorem B4642865 : Blo 1220928 4642865 := bstep (se 2 (by rfl) ⟨1741074, by rfl⟩ : syracuseStep 4642865 = 3482149) B3482149
theorem B1374259 : Blo 1220928 1374259 := bstep (se 1 (by rfl) ⟨1030694, by rfl⟩ : syracuseStep 1374259 = 2061389) B2061389
theorem B1833011 : Blo 1220928 1833011 := bstep (se 1 (by rfl) ⟨1374758, by rfl⟩ : syracuseStep 1833011 = 2749517) B2749517
theorem B3094595 : Blo 1220928 3094595 := bstep (se 1 (by rfl) ⟨2320946, by rfl⟩ : syracuseStep 3094595 = 4641893) B4641893
theorem B4126787 : Blo 1220928 4126787 := bstep (se 1 (by rfl) ⟨3095090, by rfl⟩ : syracuseStep 4126787 = 6190181) B6190181
theorem B7829581 : Blo 1220928 7829581 := bstep (se 3 (by rfl) ⟨1468046, by rfl⟩ : syracuseStep 7829581 = 2936093) B2936093
theorem B1833041 : Blo 1220928 1833041 := bstep (se 2 (by rfl) ⟨687390, by rfl⟩ : syracuseStep 1833041 = 1374781) B1374781
theorem B1833059 : Blo 1220928 1833059 := bstep (se 1 (by rfl) ⟨1374794, by rfl⟩ : syracuseStep 1833059 = 2749589) B2749589
theorem B2062435 : Blo 1220928 2062435 := bstep (se 1 (by rfl) ⟨1546826, by rfl⟩ : syracuseStep 2062435 = 3093653) B3093653
theorem B1833089 : Blo 1220928 1833089 := bstep (se 2 (by rfl) ⟨687408, by rfl⟩ : syracuseStep 1833089 = 1374817) B1374817
theorem B6183053 : Blo 1220928 6183053 := bstep (se 3 (by rfl) ⟨1159322, by rfl⟩ : syracuseStep 6183053 = 2318645) B2318645
theorem B1833107 : Blo 1220928 1833107 := bstep (se 1 (by rfl) ⟨1374830, by rfl⟩ : syracuseStep 1833107 = 2749661) B2749661
theorem B1833137 : Blo 1220928 1833137 := bstep (se 2 (by rfl) ⟨687426, by rfl⟩ : syracuseStep 1833137 = 1374853) B1374853
theorem B1374403 : Blo 1220928 1374403 := bstep (se 1 (by rfl) ⟨1030802, by rfl⟩ : syracuseStep 1374403 = 2061605) B2061605
theorem B1833155 : Blo 1220928 1833155 := bstep (se 1 (by rfl) ⟨1374866, by rfl⟩ : syracuseStep 1833155 = 2749733) B2749733
theorem B3913933 : Blo 1220928 3913933 := bstep (se 3 (by rfl) ⟨733862, by rfl⟩ : syracuseStep 3913933 = 1467725) B1467725
theorem B1833185 : Blo 1220928 1833185 := bstep (se 2 (by rfl) ⟨687444, by rfl⟩ : syracuseStep 1833185 = 1374889) B1374889
theorem B2062577 : Blo 1220928 2062577 := bstep (se 2 (by rfl) ⟨773466, by rfl⟩ : syracuseStep 2062577 = 1546933) B1546933
theorem B2750705 : Blo 1220928 2750705 := bstep (se 2 (by rfl) ⟨1031514, by rfl⟩ : syracuseStep 2750705 = 2063029) B2063029
theorem B1833203 : Blo 1220928 1833203 := bstep (se 1 (by rfl) ⟨1374902, by rfl⟩ : syracuseStep 1833203 = 2749805) B2749805
theorem B2750723 : Blo 1220928 2750723 := bstep (se 1 (by rfl) ⟨2063042, by rfl⟩ : syracuseStep 2750723 = 4126085) B4126085
theorem B3094787 : Blo 1220928 3094787 := bstep (se 1 (by rfl) ⟨2321090, by rfl⟩ : syracuseStep 3094787 = 4642181) B4642181
theorem B1833233 : Blo 1220928 1833233 := bstep (se 2 (by rfl) ⟨687462, by rfl⟩ : syracuseStep 1833233 = 1374925) B1374925
theorem B1833251 : Blo 1220928 1833251 := bstep (se 1 (by rfl) ⟨1374938, by rfl⟩ : syracuseStep 1833251 = 2749877) B2749877
theorem B4405553 : Blo 1220928 4405553 := bstep (se 2 (by rfl) ⟨1652082, by rfl⟩ : syracuseStep 4405553 = 3304165) B3304165
theorem B1833281 : Blo 1220928 1833281 := bstep (se 2 (by rfl) ⟨687480, by rfl⟩ : syracuseStep 1833281 = 1374961) B1374961
theorem B4127057 : Blo 1220928 4127057 := bstep (se 2 (by rfl) ⟨1547646, by rfl⟩ : syracuseStep 4127057 = 3095293) B3095293
theorem B1374547 : Blo 1220928 1374547 := bstep (se 1 (by rfl) ⟨1030910, by rfl⟩ : syracuseStep 1374547 = 2061821) B2061821
theorem B1833299 : Blo 1220928 1833299 := bstep (se 1 (by rfl) ⟨1374974, by rfl⟩ : syracuseStep 1833299 = 2749949) B2749949
theorem B1833329 : Blo 1220928 1833329 := bstep (se 2 (by rfl) ⟨687498, by rfl⟩ : syracuseStep 1833329 = 1374997) B1374997
theorem B2062705 : Blo 1220928 2062705 := bstep (se 2 (by rfl) ⟨773514, by rfl⟩ : syracuseStep 2062705 = 1547029) B1547029
theorem B1833347 : Blo 1220928 1833347 := bstep (se 1 (by rfl) ⟨1375010, by rfl⟩ : syracuseStep 1833347 = 2750021) B2750021
theorem B2062739 : Blo 1220928 2062739 := bstep (se 1 (by rfl) ⟨1547054, by rfl⟩ : syracuseStep 2062739 = 3094109) B3094109
theorem B1833377 : Blo 1220928 1833377 := bstep (se 2 (by rfl) ⟨687516, by rfl⟩ : syracuseStep 1833377 = 1375033) B1375033
theorem B6961585 : Blo 1220928 6961585 := bstep (se 2 (by rfl) ⟨2610594, by rfl⟩ : syracuseStep 6961585 = 5221189) B5221189
theorem B2120113 : Blo 1220928 2120113 := bstep (se 2 (by rfl) ⟨795042, by rfl⟩ : syracuseStep 2120113 = 1590085) B1590085
theorem B1833395 : Blo 1220928 1833395 := bstep (se 1 (by rfl) ⟨1375046, by rfl⟩ : syracuseStep 1833395 = 2750093) B2750093
theorem B1833425 : Blo 1220928 1833425 := bstep (se 2 (by rfl) ⟨687534, by rfl⟩ : syracuseStep 1833425 = 1375069) B1375069
theorem B1374691 : Blo 1220928 1374691 := bstep (se 1 (by rfl) ⟨1031018, by rfl⟩ : syracuseStep 1374691 = 2062037) B2062037
theorem B1833443 : Blo 1220928 1833443 := bstep (se 1 (by rfl) ⟨1375082, by rfl⟩ : syracuseStep 1833443 = 2750165) B2750165
theorem B1833473 : Blo 1220928 1833473 := bstep (se 2 (by rfl) ⟨687552, by rfl⟩ : syracuseStep 1833473 = 1375105) B1375105
theorem B11450893 : Blo 1220928 11450893 := bstep (se 3 (by rfl) ⟨2147042, by rfl⟩ : syracuseStep 11450893 = 4294085) B4294085
theorem B2750993 : Blo 1220928 2750993 := bstep (se 2 (by rfl) ⟨1031622, by rfl⟩ : syracuseStep 2750993 = 2063245) B2063245
theorem B1546771 : Blo 1220928 1546771 := bstep (se 1 (by rfl) ⟨1160078, by rfl⟩ : syracuseStep 1546771 = 2320157) B2320157
theorem B1833491 : Blo 1220928 1833491 := bstep (se 1 (by rfl) ⟨1375118, by rfl⟩ : syracuseStep 1833491 = 2750237) B2750237
theorem B2062867 : Blo 1220928 2062867 := bstep (se 1 (by rfl) ⟨1547150, by rfl⟩ : syracuseStep 2062867 = 3094301) B3094301
theorem B2751011 : Blo 1220928 2751011 := bstep (se 1 (by rfl) ⟨2063258, by rfl⟩ : syracuseStep 2751011 = 4126517) B4126517
theorem B1833521 : Blo 1220928 1833521 := bstep (se 2 (by rfl) ⟨687570, by rfl⟩ : syracuseStep 1833521 = 1375141) B1375141
theorem B1956403 : Blo 1220928 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B1833539 : Blo 1220928 1833539 := bstep (se 1 (by rfl) ⟨1375154, by rfl⟩ : syracuseStep 1833539 = 2750309) B2750309
theorem B1833569 : Blo 1220928 1833569 := bstep (se 2 (by rfl) ⟨687588, by rfl⟩ : syracuseStep 1833569 = 1375177) B1375177
theorem B9271907 : Blo 1220928 9271907 := bstep (se 1 (by rfl) ⟨6953930, by rfl⟩ : syracuseStep 9271907 = 13907861) B13907861
theorem B1587811 : Blo 1220928 1587811 := bstep (se 1 (by rfl) ⟨1190858, by rfl⟩ : syracuseStep 1587811 = 2381717) B2381717
theorem B1374835 : Blo 1220928 1374835 := bstep (se 1 (by rfl) ⟨1031126, by rfl⟩ : syracuseStep 1374835 = 2062253) B2062253
theorem B1546867 : Blo 1220928 1546867 := bstep (se 1 (by rfl) ⟨1160150, by rfl⟩ : syracuseStep 1546867 = 2320301) B2320301
theorem B1833587 : Blo 1220928 1833587 := bstep (se 1 (by rfl) ⟨1375190, by rfl⟩ : syracuseStep 1833587 = 2750381) B2750381
theorem B3914381 : Blo 1220928 3914381 := bstep (se 3 (by rfl) ⟨733946, by rfl⟩ : syracuseStep 3914381 = 1467893) B1467893
theorem B34388621 : Blo 1220928 34388621 := bstep (se 3 (by rfl) ⟨6447866, by rfl⟩ : syracuseStep 34388621 = 12895733) B12895733
theorem B1833617 : Blo 1220928 1833617 := bstep (se 2 (by rfl) ⟨687606, by rfl⟩ : syracuseStep 1833617 = 1375213) B1375213
theorem B2063009 : Blo 1220928 2063009 := bstep (se 2 (by rfl) ⟨773628, by rfl⟩ : syracuseStep 2063009 = 1547257) B1547257
theorem B1833635 : Blo 1220928 1833635 := bstep (se 1 (by rfl) ⟨1375226, by rfl⟩ : syracuseStep 1833635 = 2750453) B2750453
theorem B1833665 : Blo 1220928 1833665 := bstep (se 2 (by rfl) ⟨687624, by rfl⟩ : syracuseStep 1833665 = 1375249) B1375249
theorem B1833683 : Blo 1220928 1833683 := bstep (se 1 (by rfl) ⟨1375262, by rfl⟩ : syracuseStep 1833683 = 2750525) B2750525
theorem B1833713 : Blo 1220928 1833713 := bstep (se 2 (by rfl) ⟨687642, by rfl⟩ : syracuseStep 1833713 = 1375285) B1375285
theorem B1374979 : Blo 1220928 1374979 := bstep (se 1 (by rfl) ⟨1031234, by rfl⟩ : syracuseStep 1374979 = 2062469) B2062469
theorem B1833731 : Blo 1220928 1833731 := bstep (se 1 (by rfl) ⟨1375298, by rfl⟩ : syracuseStep 1833731 = 2750597) B2750597
theorem B3480337 : Blo 1220928 3480337 := bstep (se 2 (by rfl) ⟨1305126, by rfl⟩ : syracuseStep 3480337 = 2610253) B2610253
theorem B1833761 : Blo 1220928 1833761 := bstep (se 2 (by rfl) ⟨687660, by rfl⟩ : syracuseStep 1833761 = 1375321) B1375321
theorem B2063137 : Blo 1220928 2063137 := bstep (se 2 (by rfl) ⟨773676, by rfl⟩ : syracuseStep 2063137 = 1547353) B1547353
theorem B2751281 : Blo 1220928 2751281 := bstep (se 2 (by rfl) ⟨1031730, by rfl⟩ : syracuseStep 2751281 = 2063461) B2063461
theorem B1833779 : Blo 1220928 1833779 := bstep (se 1 (by rfl) ⟨1375334, by rfl⟩ : syracuseStep 1833779 = 2750669) B2750669
theorem B15276853 : Blo 1220928 15276853 := bstep (se 5 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 15276853 = 1432205) B1432205
theorem B2063171 : Blo 1220928 2063171 := bstep (se 1 (by rfl) ⟨1547378, by rfl⟩ : syracuseStep 2063171 = 3094757) B3094757
theorem B2751299 : Blo 1220928 2751299 := bstep (se 1 (by rfl) ⟨2063474, by rfl⟩ : syracuseStep 2751299 = 4126949) B4126949
theorem B1833809 : Blo 1220928 1833809 := bstep (se 2 (by rfl) ⟨687678, by rfl⟩ : syracuseStep 1833809 = 1375357) B1375357
theorem B1833827 : Blo 1220928 1833827 := bstep (se 1 (by rfl) ⟨1375370, by rfl⟩ : syracuseStep 1833827 = 2750741) B2750741
theorem B1833857 : Blo 1220928 1833857 := bstep (se 2 (by rfl) ⟨687696, by rfl⟩ : syracuseStep 1833857 = 1375393) B1375393
theorem B1375123 : Blo 1220928 1375123 := bstep (se 1 (by rfl) ⟨1031342, by rfl⟩ : syracuseStep 1375123 = 2062685) B2062685
theorem B1833875 : Blo 1220928 1833875 := bstep (se 1 (by rfl) ⟨1375406, by rfl⟩ : syracuseStep 1833875 = 2750813) B2750813
theorem B1833905 : Blo 1220928 1833905 := bstep (se 2 (by rfl) ⟨687714, by rfl⟩ : syracuseStep 1833905 = 1375429) B1375429
theorem B1833923 : Blo 1220928 1833923 := bstep (se 1 (by rfl) ⟨1375442, by rfl⟩ : syracuseStep 1833923 = 2750885) B2750885
theorem B2063299 : Blo 1220928 2063299 := bstep (se 1 (by rfl) ⟨1547474, by rfl⟩ : syracuseStep 2063299 = 3094949) B3094949
theorem B1833953 : Blo 1220928 1833953 := bstep (se 2 (by rfl) ⟨687732, by rfl⟩ : syracuseStep 1833953 = 1375465) B1375465
theorem B1833971 : Blo 1220928 1833971 := bstep (se 1 (by rfl) ⟨1375478, by rfl⟩ : syracuseStep 1833971 = 2750957) B2750957
theorem B1834001 : Blo 1220928 1834001 := bstep (se 2 (by rfl) ⟨687750, by rfl⟩ : syracuseStep 1834001 = 1375501) B1375501
theorem B1375267 : Blo 1220928 1375267 := bstep (se 1 (by rfl) ⟨1031450, by rfl⟩ : syracuseStep 1375267 = 2062901) B2062901
theorem B1834019 : Blo 1220928 1834019 := bstep (se 1 (by rfl) ⟨1375514, by rfl⟩ : syracuseStep 1834019 = 2751029) B2751029
theorem B17611829 : Blo 1220928 17611829 := bstep (se 5 (by rfl) ⟨825554, by rfl⟩ : syracuseStep 17611829 = 1651109) B1651109
theorem B25426997 : Blo 1220928 25426997 := bstep (se 5 (by rfl) ⟨1191890, by rfl⟩ : syracuseStep 25426997 = 2383781) B2383781
theorem B1834049 : Blo 1220928 1834049 := bstep (se 2 (by rfl) ⟨687768, by rfl⟩ : syracuseStep 1834049 = 1375537) B1375537
theorem B2063441 : Blo 1220928 2063441 := bstep (se 2 (by rfl) ⟨773790, by rfl⟩ : syracuseStep 2063441 = 1547581) B1547581
theorem B2751569 : Blo 1220928 2751569 := bstep (se 2 (by rfl) ⟨1031838, by rfl⟩ : syracuseStep 2751569 = 2063677) B2063677
theorem B1834067 : Blo 1220928 1834067 := bstep (se 1 (by rfl) ⟨1375550, by rfl⟩ : syracuseStep 1834067 = 2751101) B2751101
theorem B1547363 : Blo 1220928 1547363 := bstep (se 1 (by rfl) ⟨1160522, by rfl⟩ : syracuseStep 1547363 = 2321045) B2321045
theorem B2751587 : Blo 1220928 2751587 := bstep (se 1 (by rfl) ⟨2063690, by rfl⟩ : syracuseStep 2751587 = 4127381) B4127381
theorem B1834097 : Blo 1220928 1834097 := bstep (se 2 (by rfl) ⟨687786, by rfl⟩ : syracuseStep 1834097 = 1375573) B1375573
theorem B1834115 : Blo 1220928 1834115 := bstep (se 1 (by rfl) ⟨1375586, by rfl⟩ : syracuseStep 1834115 = 2751173) B2751173
theorem B1834145 : Blo 1220928 1834145 := bstep (se 2 (by rfl) ⟨687804, by rfl⟩ : syracuseStep 1834145 = 1375609) B1375609
theorem B1375411 : Blo 1220928 1375411 := bstep (se 1 (by rfl) ⟨1031558, by rfl⟩ : syracuseStep 1375411 = 2063117) B2063117
theorem B1834163 : Blo 1220928 1834163 := bstep (se 1 (by rfl) ⟨1375622, by rfl⟩ : syracuseStep 1834163 = 2751245) B2751245
theorem B1834193 : Blo 1220928 1834193 := bstep (se 2 (by rfl) ⟨687822, by rfl⟩ : syracuseStep 1834193 = 1375645) B1375645
theorem B2063569 : Blo 1220928 2063569 := bstep (se 2 (by rfl) ⟨773838, by rfl⟩ : syracuseStep 2063569 = 1547677) B1547677
theorem B1834211 : Blo 1220928 1834211 := bstep (se 1 (by rfl) ⟨1375658, by rfl⟩ : syracuseStep 1834211 = 2751317) B2751317
theorem B2063603 : Blo 1220928 2063603 := bstep (se 1 (by rfl) ⟨1547702, by rfl⟩ : syracuseStep 2063603 = 3095405) B3095405
theorem B1834241 : Blo 1220928 1834241 := bstep (se 2 (by rfl) ⟨687840, by rfl⟩ : syracuseStep 1834241 = 1375681) B1375681
theorem B3767555 : Blo 1220928 3767555 := bstep (se 1 (by rfl) ⟨2825666, by rfl⟩ : syracuseStep 3767555 = 5651333) B5651333
theorem B1834259 : Blo 1220928 1834259 := bstep (se 1 (by rfl) ⟨1375694, by rfl⟩ : syracuseStep 1834259 = 2751389) B2751389
theorem B1834289 : Blo 1220928 1834289 := bstep (se 2 (by rfl) ⟨687858, by rfl⟩ : syracuseStep 1834289 = 1375717) B1375717
theorem B1375555 : Blo 1220928 1375555 := bstep (se 1 (by rfl) ⟨1031666, by rfl⟩ : syracuseStep 1375555 = 2063333) B2063333
theorem B1834307 : Blo 1220928 1834307 := bstep (se 1 (by rfl) ⟨1375730, by rfl⟩ : syracuseStep 1834307 = 2751461) B2751461
theorem B1834337 : Blo 1220928 1834337 := bstep (se 2 (by rfl) ⟨687876, by rfl⟩ : syracuseStep 1834337 = 1375753) B1375753
theorem B5217635 : Blo 1220928 5217635 := bstep (se 1 (by rfl) ⟨3913226, by rfl⟩ : syracuseStep 5217635 = 7826453) B7826453
theorem B1834355 : Blo 1220928 1834355 := bstep (se 1 (by rfl) ⟨1375766, by rfl⟩ : syracuseStep 1834355 = 2751533) B2751533
theorem B1834385 : Blo 1220928 1834385 := bstep (se 2 (by rfl) ⟨687894, by rfl⟩ : syracuseStep 1834385 = 1375789) B1375789
theorem B1957331 : Blo 1220928 1957331 := bstep (se 1 (by rfl) ⟨1467998, by rfl⟩ : syracuseStep 1957331 = 2935997) B2935997
theorem B1375699 : Blo 1220928 1375699 := bstep (se 1 (by rfl) ⟨1031774, by rfl⟩ : syracuseStep 1375699 = 2063549) B2063549
theorem B2088497 : Blo 1220928 2088497 := bstep (se 2 (by rfl) ⟨783186, by rfl⟩ : syracuseStep 2088497 = 1566373) B1566373
theorem B13401713 : Blo 1220928 13401713 := bstep (se 2 (by rfl) ⟨5025642, by rfl⟩ : syracuseStep 13401713 = 10051285) B10051285
theorem B1859201 : Blo 1220928 1859201 := bstep (se 2 (by rfl) ⟨697200, by rfl⟩ : syracuseStep 1859201 = 1394401) B1394401
theorem B1957601 : Blo 1220928 1957601 := bstep (se 2 (by rfl) ⟨734100, by rfl⟩ : syracuseStep 1957601 = 1468201) B1468201
theorem B42295061 : Blo 1220928 42295061 := bstep (se 6 (by rfl) ⟨991290, by rfl⟩ : syracuseStep 42295061 = 1982581) B1982581
theorem B2318129 : Blo 1220928 2318129 := bstep (se 2 (by rfl) ⟨869298, by rfl⟩ : syracuseStep 2318129 = 1738597) B1738597
theorem B2416433 : Blo 1220928 2416433 := bstep (se 2 (by rfl) ⟨906162, by rfl⟩ : syracuseStep 2416433 = 1812325) B1812325
theorem B6954821 : Blo 1220928 6954821 := bstep (se 4 (by rfl) ⟨652014, by rfl⟩ : syracuseStep 6954821 = 1304029) B1304029
theorem B6963043 : Blo 1220928 6963043 := bstep (se 1 (by rfl) ⟨5222282, by rfl⟩ : syracuseStep 6963043 = 10444565) B10444565
theorem B4407139 : Blo 1220928 4407139 := bstep (se 1 (by rfl) ⟨3305354, by rfl⟩ : syracuseStep 4407139 = 6610709) B6610709
theorem B23486435 : Blo 1220928 23486435 := bstep (se 1 (by rfl) ⟨17614826, by rfl⟩ : syracuseStep 23486435 = 35229653) B35229653
theorem B4407371 : Blo 1220928 4407371 := bstep (se 1 (by rfl) ⟨3305528, by rfl⟩ : syracuseStep 4407371 = 6611057) B6611057
theorem B4956311 : Blo 1220928 4956311 := bstep (se 1 (by rfl) ⟨3717233, by rfl⟩ : syracuseStep 4956311 = 7434467) B7434467
theorem B4636865 : Blo 1220928 4636865 := bstep (se 2 (by rfl) ⟨1738824, by rfl⟩ : syracuseStep 4636865 = 3477649) B3477649
theorem B2318539 : Blo 1220928 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B4120793 : Blo 1220928 4120793 := bstep (se 2 (by rfl) ⟨1545297, by rfl⟩ : syracuseStep 4120793 = 3090595) B3090595
theorem B5218577 : Blo 1220928 5218577 := bstep (se 2 (by rfl) ⟨1956966, by rfl⟩ : syracuseStep 5218577 = 3913933) B3913933
theorem B2318615 : Blo 1220928 2318615 := bstep (se 1 (by rfl) ⟨1738961, by rfl⟩ : syracuseStep 2318615 = 3477923) B3477923
theorem B1220939 : Blo 1220928 1220939 := bstep (se 1 (by rfl) ⟨915704, by rfl⟩ : syracuseStep 1220939 = 1831409) B1831409
theorem B1220951 : Blo 1220928 1220951 := bstep (se 1 (by rfl) ⟨915713, by rfl⟩ : syracuseStep 1220951 = 1831427) B1831427
theorem B1220971 : Blo 1220928 1220971 := bstep (se 1 (by rfl) ⟨915728, by rfl⟩ : syracuseStep 1220971 = 1831457) B1831457
theorem B1220983 : Blo 1220928 1220983 := bstep (se 1 (by rfl) ⟨915737, by rfl⟩ : syracuseStep 1220983 = 1831475) B1831475
theorem B1221003 : Blo 1220928 1221003 := bstep (se 1 (by rfl) ⟨915752, by rfl⟩ : syracuseStep 1221003 = 1831505) B1831505
theorem B1221015 : Blo 1220928 1221015 := bstep (se 1 (by rfl) ⟨915761, by rfl⟩ : syracuseStep 1221015 = 1831523) B1831523
theorem B1221035 : Blo 1220928 1221035 := bstep (se 1 (by rfl) ⟨915776, by rfl⟩ : syracuseStep 1221035 = 1831553) B1831553
theorem B1221047 : Blo 1220928 1221047 := bstep (se 1 (by rfl) ⟨915785, by rfl⟩ : syracuseStep 1221047 = 1831571) B1831571
theorem B1221067 : Blo 1220928 1221067 := bstep (se 1 (by rfl) ⟨915800, by rfl⟩ : syracuseStep 1221067 = 1831601) B1831601
theorem B1221079 : Blo 1220928 1221079 := bstep (se 1 (by rfl) ⟨915809, by rfl⟩ : syracuseStep 1221079 = 1831619) B1831619
theorem B1221099 : Blo 1220928 1221099 := bstep (se 1 (by rfl) ⟨915824, by rfl⟩ : syracuseStep 1221099 = 1831649) B1831649
theorem B1221111 : Blo 1220928 1221111 := bstep (se 1 (by rfl) ⟨915833, by rfl⟩ : syracuseStep 1221111 = 1831667) B1831667
theorem B1221131 : Blo 1220928 1221131 := bstep (se 1 (by rfl) ⟨915848, by rfl⟩ : syracuseStep 1221131 = 1831697) B1831697
theorem B1221143 : Blo 1220928 1221143 := bstep (se 1 (by rfl) ⟨915857, by rfl⟩ : syracuseStep 1221143 = 1831715) B1831715
theorem B1221163 : Blo 1220928 1221163 := bstep (se 1 (by rfl) ⟨915872, by rfl⟩ : syracuseStep 1221163 = 1831745) B1831745
theorem B1221175 : Blo 1220928 1221175 := bstep (se 1 (by rfl) ⟨915881, by rfl⟩ : syracuseStep 1221175 = 1831763) B1831763
theorem B9282113 : Blo 1220928 9282113 := bstep (se 2 (by rfl) ⟨3480792, by rfl⟩ : syracuseStep 9282113 = 6961585) B6961585
theorem B1221195 : Blo 1220928 1221195 := bstep (se 1 (by rfl) ⟨915896, by rfl⟩ : syracuseStep 1221195 = 1831793) B1831793
theorem B1221207 : Blo 1220928 1221207 := bstep (se 1 (by rfl) ⟨915905, by rfl⟩ : syracuseStep 1221207 = 1831811) B1831811
theorem B1221227 : Blo 1220928 1221227 := bstep (se 1 (by rfl) ⟨915920, by rfl⟩ : syracuseStep 1221227 = 1831841) B1831841
theorem B1221239 : Blo 1220928 1221239 := bstep (se 1 (by rfl) ⟨915929, by rfl⟩ : syracuseStep 1221239 = 1831859) B1831859
theorem B39608963 : Blo 1220928 39608963 := bstep (se 1 (by rfl) ⟨29706722, by rfl⟩ : syracuseStep 39608963 = 59413445) B59413445
theorem B1221259 : Blo 1220928 1221259 := bstep (se 1 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 1221259 = 1831889) B1831889
theorem B1221271 : Blo 1220928 1221271 := bstep (se 1 (by rfl) ⟨915953, by rfl⟩ : syracuseStep 1221271 = 1831907) B1831907
theorem B1221291 : Blo 1220928 1221291 := bstep (se 1 (by rfl) ⟨915968, by rfl⟩ : syracuseStep 1221291 = 1831937) B1831937
theorem B1221303 : Blo 1220928 1221303 := bstep (se 1 (by rfl) ⟨915977, by rfl⟩ : syracuseStep 1221303 = 1831955) B1831955
theorem B1221323 : Blo 1220928 1221323 := bstep (se 1 (by rfl) ⟨915992, by rfl⟩ : syracuseStep 1221323 = 1831985) B1831985
theorem B1221335 : Blo 1220928 1221335 := bstep (se 1 (by rfl) ⟨916001, by rfl⟩ : syracuseStep 1221335 = 1832003) B1832003
theorem B1221355 : Blo 1220928 1221355 := bstep (se 1 (by rfl) ⟨916016, by rfl⟩ : syracuseStep 1221355 = 1832033) B1832033
theorem B1221367 : Blo 1220928 1221367 := bstep (se 1 (by rfl) ⟨916025, by rfl⟩ : syracuseStep 1221367 = 1832051) B1832051
theorem B1221387 : Blo 1220928 1221387 := bstep (se 1 (by rfl) ⟨916040, by rfl⟩ : syracuseStep 1221387 = 1832081) B1832081
theorem B1221399 : Blo 1220928 1221399 := bstep (se 1 (by rfl) ⟨916049, by rfl⟩ : syracuseStep 1221399 = 1832099) B1832099
theorem B1221419 : Blo 1220928 1221419 := bstep (se 1 (by rfl) ⟨916064, by rfl⟩ : syracuseStep 1221419 = 1832129) B1832129
theorem B1221431 : Blo 1220928 1221431 := bstep (se 1 (by rfl) ⟨916073, by rfl⟩ : syracuseStep 1221431 = 1832147) B1832147
theorem B6030155 : Blo 1220928 6030155 := bstep (se 1 (by rfl) ⟨4522616, by rfl⟩ : syracuseStep 6030155 = 9045233) B9045233
theorem B1221451 : Blo 1220928 1221451 := bstep (se 1 (by rfl) ⟨916088, by rfl⟩ : syracuseStep 1221451 = 1832177) B1832177
theorem B1221463 : Blo 1220928 1221463 := bstep (se 1 (by rfl) ⟨916097, by rfl⟩ : syracuseStep 1221463 = 1832195) B1832195
theorem B4637533 : Blo 1220928 4637533 := bstep (se 3 (by rfl) ⟨869537, by rfl⟩ : syracuseStep 4637533 = 1739075) B1739075
theorem B3916637 : Blo 1220928 3916637 := bstep (se 3 (by rfl) ⟨734369, by rfl⟩ : syracuseStep 3916637 = 1468739) B1468739
theorem B1221483 : Blo 1220928 1221483 := bstep (se 1 (by rfl) ⟨916112, by rfl⟩ : syracuseStep 1221483 = 1832225) B1832225
theorem B1221495 : Blo 1220928 1221495 := bstep (se 1 (by rfl) ⟨916121, by rfl⟩ : syracuseStep 1221495 = 1832243) B1832243
theorem B1221515 : Blo 1220928 1221515 := bstep (se 1 (by rfl) ⟨916136, by rfl⟩ : syracuseStep 1221515 = 1832273) B1832273
theorem B4121495 : Blo 1220928 4121495 := bstep (se 1 (by rfl) ⟨3091121, by rfl⟩ : syracuseStep 4121495 = 6182243) B6182243
theorem B1221527 : Blo 1220928 1221527 := bstep (se 1 (by rfl) ⟨916145, by rfl⟩ : syracuseStep 1221527 = 1832291) B1832291
theorem B1221547 : Blo 1220928 1221547 := bstep (se 1 (by rfl) ⟨916160, by rfl⟩ : syracuseStep 1221547 = 1832321) B1832321
theorem B2319283 : Blo 1220928 2319283 := bstep (se 1 (by rfl) ⟨1739462, by rfl⟩ : syracuseStep 2319283 = 3478925) B3478925
theorem B1237943 : Blo 1220928 1237943 := bstep (se 1 (by rfl) ⟨928457, by rfl⟩ : syracuseStep 1237943 = 1856915) B1856915
theorem B1221559 : Blo 1220928 1221559 := bstep (se 1 (by rfl) ⟨916169, by rfl⟩ : syracuseStep 1221559 = 1832339) B1832339
theorem B2261953 : Blo 1220928 2261953 := bstep (se 2 (by rfl) ⟨848232, by rfl⟩ : syracuseStep 2261953 = 1696465) B1696465
theorem B1221579 : Blo 1220928 1221579 := bstep (se 1 (by rfl) ⟨916184, by rfl⟩ : syracuseStep 1221579 = 1832369) B1832369
theorem B1221591 : Blo 1220928 1221591 := bstep (se 1 (by rfl) ⟨916193, by rfl⟩ : syracuseStep 1221591 = 1832387) B1832387
theorem B1221611 : Blo 1220928 1221611 := bstep (se 1 (by rfl) ⟨916208, by rfl⟩ : syracuseStep 1221611 = 1832417) B1832417
theorem B1221623 : Blo 1220928 1221623 := bstep (se 1 (by rfl) ⟨916217, by rfl⟩ : syracuseStep 1221623 = 1832435) B1832435
theorem B1221643 : Blo 1220928 1221643 := bstep (se 1 (by rfl) ⟨916232, by rfl⟩ : syracuseStep 1221643 = 1832465) B1832465
theorem B1221655 : Blo 1220928 1221655 := bstep (se 1 (by rfl) ⟨916241, by rfl⟩ : syracuseStep 1221655 = 1832483) B1832483
theorem B16720931 : Blo 1220928 16720931 := bstep (se 1 (by rfl) ⟨12540698, by rfl⟩ : syracuseStep 16720931 = 25081397) B25081397
theorem B1221675 : Blo 1220928 1221675 := bstep (se 1 (by rfl) ⟨916256, by rfl⟩ : syracuseStep 1221675 = 1832513) B1832513
theorem B1221687 : Blo 1220928 1221687 := bstep (se 1 (by rfl) ⟨916265, by rfl⟩ : syracuseStep 1221687 = 1832531) B1832531
theorem B1221707 : Blo 1220928 1221707 := bstep (se 1 (by rfl) ⟨916280, by rfl⟩ : syracuseStep 1221707 = 1832561) B1832561
theorem B4023371 : Blo 1220928 4023371 := bstep (se 1 (by rfl) ⟨3017528, by rfl⟩ : syracuseStep 4023371 = 6035057) B6035057
theorem B1221719 : Blo 1220928 1221719 := bstep (se 1 (by rfl) ⟨916289, by rfl⟩ : syracuseStep 1221719 = 1832579) B1832579
theorem B1221739 : Blo 1220928 1221739 := bstep (se 1 (by rfl) ⟨916304, by rfl⟩ : syracuseStep 1221739 = 1832609) B1832609
theorem B1221751 : Blo 1220928 1221751 := bstep (se 1 (by rfl) ⟨916313, by rfl⟩ : syracuseStep 1221751 = 1832627) B1832627
theorem B1221771 : Blo 1220928 1221771 := bstep (se 1 (by rfl) ⟨916328, by rfl⟩ : syracuseStep 1221771 = 1832657) B1832657
theorem B1221783 : Blo 1220928 1221783 := bstep (se 1 (by rfl) ⟨916337, by rfl⟩ : syracuseStep 1221783 = 1832675) B1832675
theorem B2319511 : Blo 1220928 2319511 := bstep (se 1 (by rfl) ⟨1739633, by rfl⟩ : syracuseStep 2319511 = 3479267) B3479267
theorem B1221803 : Blo 1220928 1221803 := bstep (se 1 (by rfl) ⟨916352, by rfl⟩ : syracuseStep 1221803 = 1832705) B1832705
theorem B3769523 : Blo 1220928 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B1221815 : Blo 1220928 1221815 := bstep (se 1 (by rfl) ⟨916361, by rfl⟩ : syracuseStep 1221815 = 1832723) B1832723
theorem B1467595 : Blo 1220928 1467595 := bstep (se 1 (by rfl) ⟨1100696, by rfl⟩ : syracuseStep 1467595 = 2201393) B2201393
theorem B1221835 : Blo 1220928 1221835 := bstep (se 1 (by rfl) ⟨916376, by rfl⟩ : syracuseStep 1221835 = 1832753) B1832753
theorem B5293259 : Blo 1220928 5293259 := bstep (se 1 (by rfl) ⟨3969944, by rfl⟩ : syracuseStep 5293259 = 7939889) B7939889
theorem B1221847 : Blo 1220928 1221847 := bstep (se 1 (by rfl) ⟨916385, by rfl⟩ : syracuseStep 1221847 = 1832771) B1832771
theorem B5219549 : Blo 1220928 5219549 := bstep (se 3 (by rfl) ⟨978665, by rfl⟩ : syracuseStep 5219549 = 1957331) B1957331
theorem B1221867 : Blo 1220928 1221867 := bstep (se 1 (by rfl) ⟨916400, by rfl⟩ : syracuseStep 1221867 = 1832801) B1832801
theorem B1221879 : Blo 1220928 1221879 := bstep (se 1 (by rfl) ⟨916409, by rfl⟩ : syracuseStep 1221879 = 1832819) B1832819
theorem B2319617 : Blo 1220928 2319617 := bstep (se 2 (by rfl) ⟨869856, by rfl⟩ : syracuseStep 2319617 = 1739713) B1739713
theorem B1221899 : Blo 1220928 1221899 := bstep (se 1 (by rfl) ⟨916424, by rfl⟩ : syracuseStep 1221899 = 1832849) B1832849
theorem B1221911 : Blo 1220928 1221911 := bstep (se 1 (by rfl) ⟨916433, by rfl⟩ : syracuseStep 1221911 = 1832867) B1832867
theorem B1221931 : Blo 1220928 1221931 := bstep (se 1 (by rfl) ⟨916448, by rfl⟩ : syracuseStep 1221931 = 1832897) B1832897
theorem B1221943 : Blo 1220928 1221943 := bstep (se 1 (by rfl) ⟨916457, by rfl⟩ : syracuseStep 1221943 = 1832915) B1832915
theorem B1221963 : Blo 1220928 1221963 := bstep (se 1 (by rfl) ⟨916472, by rfl⟩ : syracuseStep 1221963 = 1832945) B1832945
theorem B1221975 : Blo 1220928 1221975 := bstep (se 1 (by rfl) ⟨916481, by rfl⟩ : syracuseStep 1221975 = 1832963) B1832963
theorem B1221995 : Blo 1220928 1221995 := bstep (se 1 (by rfl) ⟨916496, by rfl⟩ : syracuseStep 1221995 = 1832993) B1832993
theorem B1222007 : Blo 1220928 1222007 := bstep (se 1 (by rfl) ⟨916505, by rfl⟩ : syracuseStep 1222007 = 1833011) B1833011
theorem B1222027 : Blo 1220928 1222027 := bstep (se 1 (by rfl) ⟨916520, by rfl⟩ : syracuseStep 1222027 = 1833041) B1833041
theorem B1222039 : Blo 1220928 1222039 := bstep (se 1 (by rfl) ⟨916529, by rfl⟩ : syracuseStep 1222039 = 1833059) B1833059
theorem B2319769 : Blo 1220928 2319769 := bstep (se 2 (by rfl) ⟨869913, by rfl⟩ : syracuseStep 2319769 = 1739827) B1739827
theorem B1222059 : Blo 1220928 1222059 := bstep (se 1 (by rfl) ⟨916544, by rfl⟩ : syracuseStep 1222059 = 1833089) B1833089
theorem B4122035 : Blo 1220928 4122035 := bstep (se 1 (by rfl) ⟨3091526, by rfl⟩ : syracuseStep 4122035 = 6183053) B6183053
theorem B1222071 : Blo 1220928 1222071 := bstep (se 1 (by rfl) ⟨916553, by rfl⟩ : syracuseStep 1222071 = 1833107) B1833107
theorem B1222091 : Blo 1220928 1222091 := bstep (se 1 (by rfl) ⟨916568, by rfl⟩ : syracuseStep 1222091 = 1833137) B1833137
theorem B1222103 : Blo 1220928 1222103 := bstep (se 1 (by rfl) ⟨916577, by rfl⟩ : syracuseStep 1222103 = 1833155) B1833155
theorem B1222123 : Blo 1220928 1222123 := bstep (se 1 (by rfl) ⟨916592, by rfl⟩ : syracuseStep 1222123 = 1833185) B1833185
theorem B1222135 : Blo 1220928 1222135 := bstep (se 1 (by rfl) ⟨916601, by rfl⟩ : syracuseStep 1222135 = 1833203) B1833203
theorem B1222155 : Blo 1220928 1222155 := bstep (se 1 (by rfl) ⟨916616, by rfl⟩ : syracuseStep 1222155 = 1833233) B1833233
theorem B1222167 : Blo 1220928 1222167 := bstep (se 1 (by rfl) ⟨916625, by rfl⟩ : syracuseStep 1222167 = 1833251) B1833251
theorem B1222187 : Blo 1220928 1222187 := bstep (se 1 (by rfl) ⟨916640, by rfl⟩ : syracuseStep 1222187 = 1833281) B1833281
theorem B1222199 : Blo 1220928 1222199 := bstep (se 1 (by rfl) ⟨916649, by rfl⟩ : syracuseStep 1222199 = 1833299) B1833299
theorem B1222219 : Blo 1220928 1222219 := bstep (se 1 (by rfl) ⟨916664, by rfl⟩ : syracuseStep 1222219 = 1833329) B1833329
theorem B1222231 : Blo 1220928 1222231 := bstep (se 1 (by rfl) ⟨916673, by rfl⟩ : syracuseStep 1222231 = 1833347) B1833347
theorem B1222251 : Blo 1220928 1222251 := bstep (se 1 (by rfl) ⟨916688, by rfl⟩ : syracuseStep 1222251 = 1833377) B1833377
theorem B1222263 : Blo 1220928 1222263 := bstep (se 1 (by rfl) ⟨916697, by rfl⟩ : syracuseStep 1222263 = 1833395) B1833395
theorem B2475659 : Blo 1220928 2475659 := bstep (se 1 (by rfl) ⟨1856744, by rfl⟩ : syracuseStep 2475659 = 3713489) B3713489
theorem B1222283 : Blo 1220928 1222283 := bstep (se 1 (by rfl) ⟨916712, by rfl⟩ : syracuseStep 1222283 = 1833425) B1833425
theorem B1222295 : Blo 1220928 1222295 := bstep (se 1 (by rfl) ⟨916721, by rfl⟩ : syracuseStep 1222295 = 1833443) B1833443
theorem B1222315 : Blo 1220928 1222315 := bstep (se 1 (by rfl) ⟨916736, by rfl⟩ : syracuseStep 1222315 = 1833473) B1833473
theorem B1222327 : Blo 1220928 1222327 := bstep (se 1 (by rfl) ⟨916745, by rfl⟩ : syracuseStep 1222327 = 1833491) B1833491
theorem B4122305 : Blo 1220928 4122305 := bstep (se 2 (by rfl) ⟨1545864, by rfl⟩ : syracuseStep 4122305 = 3091729) B3091729
theorem B1222347 : Blo 1220928 1222347 := bstep (se 1 (by rfl) ⟨916760, by rfl⟩ : syracuseStep 1222347 = 1833521) B1833521
theorem B1222359 : Blo 1220928 1222359 := bstep (se 1 (by rfl) ⟨916769, by rfl⟩ : syracuseStep 1222359 = 1833539) B1833539
theorem B1222379 : Blo 1220928 1222379 := bstep (se 1 (by rfl) ⟨916784, by rfl⟩ : syracuseStep 1222379 = 1833569) B1833569
theorem B1222391 : Blo 1220928 1222391 := bstep (se 1 (by rfl) ⟨916793, by rfl⟩ : syracuseStep 1222391 = 1833587) B1833587
theorem B1222411 : Blo 1220928 1222411 := bstep (se 1 (by rfl) ⟨916808, by rfl⟩ : syracuseStep 1222411 = 1833617) B1833617
theorem B1222423 : Blo 1220928 1222423 := bstep (se 1 (by rfl) ⟨916817, by rfl⟩ : syracuseStep 1222423 = 1833635) B1833635
theorem B11142947 : Blo 1220928 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B1222443 : Blo 1220928 1222443 := bstep (se 1 (by rfl) ⟨916832, by rfl⟩ : syracuseStep 1222443 = 1833665) B1833665
theorem B1222455 : Blo 1220928 1222455 := bstep (se 1 (by rfl) ⟨916841, by rfl⟩ : syracuseStep 1222455 = 1833683) B1833683
theorem B1222475 : Blo 1220928 1222475 := bstep (se 1 (by rfl) ⟨916856, by rfl⟩ : syracuseStep 1222475 = 1833713) B1833713
theorem B1222487 : Blo 1220928 1222487 := bstep (se 1 (by rfl) ⟨916865, by rfl⟩ : syracuseStep 1222487 = 1833731) B1833731
theorem B1222507 : Blo 1220928 1222507 := bstep (se 1 (by rfl) ⟨916880, by rfl⟩ : syracuseStep 1222507 = 1833761) B1833761
theorem B1222519 : Blo 1220928 1222519 := bstep (se 1 (by rfl) ⟨916889, by rfl⟩ : syracuseStep 1222519 = 1833779) B1833779
theorem B1222539 : Blo 1220928 1222539 := bstep (se 1 (by rfl) ⟨916904, by rfl⟩ : syracuseStep 1222539 = 1833809) B1833809
theorem B1222551 : Blo 1220928 1222551 := bstep (se 1 (by rfl) ⟨916913, by rfl⟩ : syracuseStep 1222551 = 1833827) B1833827
theorem B1222571 : Blo 1220928 1222571 := bstep (se 1 (by rfl) ⟨916928, by rfl⟩ : syracuseStep 1222571 = 1833857) B1833857
theorem B1222583 : Blo 1220928 1222583 := bstep (se 1 (by rfl) ⟨916937, by rfl⟩ : syracuseStep 1222583 = 1833875) B1833875
theorem B1222603 : Blo 1220928 1222603 := bstep (se 1 (by rfl) ⟨916952, by rfl⟩ : syracuseStep 1222603 = 1833905) B1833905
theorem B1222615 : Blo 1220928 1222615 := bstep (se 1 (by rfl) ⟨916961, by rfl⟩ : syracuseStep 1222615 = 1833923) B1833923
theorem B1222635 : Blo 1220928 1222635 := bstep (se 1 (by rfl) ⟨916976, by rfl⟩ : syracuseStep 1222635 = 1833953) B1833953
theorem B1222647 : Blo 1220928 1222647 := bstep (se 1 (by rfl) ⟨916985, by rfl⟩ : syracuseStep 1222647 = 1833971) B1833971
theorem B1222667 : Blo 1220928 1222667 := bstep (se 1 (by rfl) ⟨917000, by rfl⟩ : syracuseStep 1222667 = 1834001) B1834001
theorem B1222679 : Blo 1220928 1222679 := bstep (se 1 (by rfl) ⟨917009, by rfl⟩ : syracuseStep 1222679 = 1834019) B1834019
theorem B12060707 : Blo 1220928 12060707 := bstep (se 1 (by rfl) ⟨9045530, by rfl⟩ : syracuseStep 12060707 = 18091061) B18091061
theorem B11741219 : Blo 1220928 11741219 := bstep (se 1 (by rfl) ⟨8805914, by rfl⟩ : syracuseStep 11741219 = 17611829) B17611829
theorem B16951331 : Blo 1220928 16951331 := bstep (se 1 (by rfl) ⟨12713498, by rfl⟩ : syracuseStep 16951331 = 25426997) B25426997
theorem B1222699 : Blo 1220928 1222699 := bstep (se 1 (by rfl) ⟨917024, by rfl⟩ : syracuseStep 1222699 = 1834049) B1834049
theorem B1222711 : Blo 1220928 1222711 := bstep (se 1 (by rfl) ⟨917033, by rfl⟩ : syracuseStep 1222711 = 1834067) B1834067
theorem B39651403 : Blo 1220928 39651403 := bstep (se 1 (by rfl) ⟨29738552, by rfl⟩ : syracuseStep 39651403 = 59477105) B59477105
theorem B1222731 : Blo 1220928 1222731 := bstep (se 1 (by rfl) ⟨917048, by rfl⟩ : syracuseStep 1222731 = 1834097) B1834097
theorem B1222743 : Blo 1220928 1222743 := bstep (se 1 (by rfl) ⟨917057, by rfl⟩ : syracuseStep 1222743 = 1834115) B1834115
theorem B4638809 : Blo 1220928 4638809 := bstep (se 2 (by rfl) ⟨1739553, by rfl⟩ : syracuseStep 4638809 = 3479107) B3479107
theorem B1222763 : Blo 1220928 1222763 := bstep (se 1 (by rfl) ⟨917072, by rfl⟩ : syracuseStep 1222763 = 1834145) B1834145
theorem B1222775 : Blo 1220928 1222775 := bstep (se 1 (by rfl) ⟨917081, by rfl⟩ : syracuseStep 1222775 = 1834163) B1834163
theorem B1222795 : Blo 1220928 1222795 := bstep (se 1 (by rfl) ⟨917096, by rfl⟩ : syracuseStep 1222795 = 1834193) B1834193
theorem B1222807 : Blo 1220928 1222807 := bstep (se 1 (by rfl) ⟨917105, by rfl⟩ : syracuseStep 1222807 = 1834211) B1834211
theorem B1222827 : Blo 1220928 1222827 := bstep (se 1 (by rfl) ⟨917120, by rfl⟩ : syracuseStep 1222827 = 1834241) B1834241
theorem B1222839 : Blo 1220928 1222839 := bstep (se 1 (by rfl) ⟨917129, by rfl⟩ : syracuseStep 1222839 = 1834259) B1834259
theorem B2230465 : Blo 1220928 2230465 := bstep (se 2 (by rfl) ⟨836424, by rfl⟩ : syracuseStep 2230465 = 1672849) B1672849
theorem B1222859 : Blo 1220928 1222859 := bstep (se 1 (by rfl) ⟨917144, by rfl⟩ : syracuseStep 1222859 = 1834289) B1834289
theorem B1222871 : Blo 1220928 1222871 := bstep (se 1 (by rfl) ⟨917153, by rfl⟩ : syracuseStep 1222871 = 1834307) B1834307
theorem B4122845 : Blo 1220928 4122845 := bstep (se 3 (by rfl) ⟨773033, by rfl⟩ : syracuseStep 4122845 = 1546067) B1546067
theorem B1222891 : Blo 1220928 1222891 := bstep (se 1 (by rfl) ⟨917168, by rfl⟩ : syracuseStep 1222891 = 1834337) B1834337
theorem B1222903 : Blo 1220928 1222903 := bstep (se 1 (by rfl) ⟨917177, by rfl⟩ : syracuseStep 1222903 = 1834355) B1834355
theorem B11307269 : Blo 1220928 11307269 := bstep (se 4 (by rfl) ⟨1060056, by rfl⟩ : syracuseStep 11307269 = 2120113) B2120113
theorem B1222923 : Blo 1220928 1222923 := bstep (se 1 (by rfl) ⟨917192, by rfl⟩ : syracuseStep 1222923 = 1834385) B1834385
theorem B1739161 : Blo 1220928 1739161 := bstep (se 2 (by rfl) ⟨652185, by rfl⟩ : syracuseStep 1739161 = 1304371) B1304371
theorem B1239467 : Blo 1220928 1239467 := bstep (se 1 (by rfl) ⟨929600, by rfl⟩ : syracuseStep 1239467 = 1859201) B1859201
theorem B9284057 : Blo 1220928 9284057 := bstep (se 2 (by rfl) ⟨3481521, by rfl⟩ : syracuseStep 9284057 = 6963043) B6963043
theorem B5876185 : Blo 1220928 5876185 := bstep (se 2 (by rfl) ⟨2203569, by rfl⟩ : syracuseStep 5876185 = 4407139) B4407139
theorem B1305067 : Blo 1220928 1305067 := bstep (se 1 (by rfl) ⟨978800, by rfl⟩ : syracuseStep 1305067 = 1957601) B1957601
theorem B15657623 : Blo 1220928 15657623 := bstep (se 1 (by rfl) ⟨11743217, by rfl⟩ : syracuseStep 15657623 = 23486435) B23486435
theorem B5221037 : Blo 1220928 5221037 := bstep (se 3 (by rfl) ⟨978944, by rfl⟩ : syracuseStep 5221037 = 1957889) B1957889
theorem B2321075 : Blo 1220928 2321075 := bstep (se 1 (by rfl) ⟨1740806, by rfl⟩ : syracuseStep 2321075 = 3481613) B3481613
theorem B2476747 : Blo 1220928 2476747 := bstep (se 1 (by rfl) ⟨1857560, by rfl⟩ : syracuseStep 2476747 = 3715121) B3715121
theorem B2747123 : Blo 1220928 2747123 := bstep (se 1 (by rfl) ⟨2060342, by rfl⟩ : syracuseStep 2747123 = 4120685) B4120685
theorem B2476811 : Blo 1220928 2476811 := bstep (se 1 (by rfl) ⟨1857608, by rfl⟩ : syracuseStep 2476811 = 3715217) B3715217
theorem B10439441 : Blo 1220928 10439441 := bstep (se 2 (by rfl) ⟨3914790, by rfl⟩ : syracuseStep 10439441 = 7829581) B7829581
theorem B2747159 : Blo 1220928 2747159 := bstep (se 1 (by rfl) ⟨2060369, by rfl⟩ : syracuseStep 2747159 = 4120739) B4120739
theorem B3091223 : Blo 1220928 3091223 := bstep (se 1 (by rfl) ⟨2318417, by rfl⟩ : syracuseStep 3091223 = 4636835) B4636835
theorem B2607947 : Blo 1220928 2607947 := bstep (se 1 (by rfl) ⟨1955960, by rfl⟩ : syracuseStep 2607947 = 3911921) B3911921
theorem B2321227 : Blo 1220928 2321227 := bstep (se 1 (by rfl) ⟨1740920, by rfl⟩ : syracuseStep 2321227 = 3481841) B3481841
theorem B2747339 : Blo 1220928 2747339 := bstep (se 1 (by rfl) ⟨2060504, by rfl⟩ : syracuseStep 2747339 = 4121009) B4121009
theorem B2747393 : Blo 1220928 2747393 := bstep (se 2 (by rfl) ⟨1030272, by rfl⟩ : syracuseStep 2747393 = 2060545) B2060545
theorem B4951057 : Blo 1220928 4951057 := bstep (se 2 (by rfl) ⟨1856646, by rfl⟩ : syracuseStep 4951057 = 3713293) B3713293
theorem B3714071 : Blo 1220928 3714071 := bstep (se 1 (by rfl) ⟨2785553, by rfl⟩ : syracuseStep 3714071 = 5571107) B5571107
theorem B2321561 : Blo 1220928 2321561 := bstep (se 2 (by rfl) ⟨870585, by rfl⟩ : syracuseStep 2321561 = 1741171) B1741171
theorem B2747609 : Blo 1220928 2747609 := bstep (se 2 (by rfl) ⟨1030353, by rfl⟩ : syracuseStep 2747609 = 2060707) B2060707
theorem B1740055 : Blo 1220928 1740055 := bstep (se 1 (by rfl) ⟨1305041, by rfl⟩ : syracuseStep 1740055 = 2610083) B2610083
theorem B2747699 : Blo 1220928 2747699 := bstep (se 1 (by rfl) ⟨2060774, by rfl⟩ : syracuseStep 2747699 = 4121549) B4121549
theorem B4123979 : Blo 1220928 4123979 := bstep (se 1 (by rfl) ⟨3092984, by rfl⟩ : syracuseStep 4123979 = 6185969) B6185969
theorem B2747735 : Blo 1220928 2747735 := bstep (se 1 (by rfl) ⟨2060801, by rfl⟩ : syracuseStep 2747735 = 4121603) B4121603
theorem B6958487 : Blo 1220928 6958487 := bstep (se 1 (by rfl) ⟨5218865, by rfl⟩ : syracuseStep 6958487 = 10437731) B10437731
theorem B2608537 : Blo 1220928 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B3091891 : Blo 1220928 3091891 := bstep (se 1 (by rfl) ⟨2318918, by rfl⟩ : syracuseStep 3091891 = 4637837) B4637837
theorem B3526067 : Blo 1220928 3526067 := bstep (se 1 (by rfl) ⟨2644550, by rfl⟩ : syracuseStep 3526067 = 5289101) B5289101
theorem B2117081 : Blo 1220928 2117081 := bstep (se 2 (by rfl) ⟨793905, by rfl⟩ : syracuseStep 2117081 = 1587811) B1587811
theorem B2747915 : Blo 1220928 2747915 := bstep (se 1 (by rfl) ⟨2060936, by rfl⟩ : syracuseStep 2747915 = 4121873) B4121873
theorem B6188561 : Blo 1220928 6188561 := bstep (se 2 (by rfl) ⟨2320710, by rfl⟩ : syracuseStep 6188561 = 4641421) B4641421
theorem B2747969 : Blo 1220928 2747969 := bstep (se 2 (by rfl) ⟨1030488, by rfl⟩ : syracuseStep 2747969 = 2060977) B2060977
theorem B3092033 : Blo 1220928 3092033 := bstep (se 2 (by rfl) ⟨1159512, by rfl⟩ : syracuseStep 3092033 = 2319025) B2319025
theorem B4124249 : Blo 1220928 4124249 := bstep (se 2 (by rfl) ⟨1546593, by rfl⟩ : syracuseStep 4124249 = 3093187) B3093187
theorem B13913693 : Blo 1220928 13913693 := bstep (se 3 (by rfl) ⟨2608817, by rfl⟩ : syracuseStep 13913693 = 5217635) B5217635
theorem B4640435 : Blo 1220928 4640435 := bstep (se 1 (by rfl) ⟨3480326, by rfl⟩ : syracuseStep 4640435 = 6960653) B6960653
theorem B6188723 : Blo 1220928 6188723 := bstep (se 1 (by rfl) ⟨4641542, by rfl⟩ : syracuseStep 6188723 = 9283085) B9283085
theorem B4640449 : Blo 1220928 4640449 := bstep (se 2 (by rfl) ⟨1740168, by rfl⟩ : syracuseStep 4640449 = 3480337) B3480337
theorem B2748185 : Blo 1220928 2748185 := bstep (se 2 (by rfl) ⟨1030569, by rfl⟩ : syracuseStep 2748185 = 2061139) B2061139
theorem B20877101 : Blo 1220928 20877101 := bstep (se 3 (by rfl) ⟨3914456, by rfl⟩ : syracuseStep 20877101 = 7828913) B7828913
theorem B1740619 : Blo 1220928 1740619 := bstep (se 1 (by rfl) ⟨1305464, by rfl⟩ : syracuseStep 1740619 = 2610929) B2610929
theorem B2748275 : Blo 1220928 2748275 := bstep (se 1 (by rfl) ⟨2061206, by rfl⟩ : syracuseStep 2748275 = 4122413) B4122413
theorem B2748311 : Blo 1220928 2748311 := bstep (se 1 (by rfl) ⟨2061233, by rfl⟩ : syracuseStep 2748311 = 4122467) B4122467
theorem B19812275 : Blo 1220928 19812275 := bstep (se 1 (by rfl) ⟨14859206, by rfl⟩ : syracuseStep 19812275 = 29718413) B29718413
theorem B3526621 : Blo 1220928 3526621 := bstep (se 3 (by rfl) ⟨661241, by rfl⟩ : syracuseStep 3526621 = 1322483) B1322483
theorem B11907107 : Blo 1220928 11907107 := bstep (se 1 (by rfl) ⟨8930330, by rfl⟩ : syracuseStep 11907107 = 17860661) B17860661
theorem B2060363 : Blo 1220928 2060363 := bstep (se 1 (by rfl) ⟨1545272, by rfl⟩ : syracuseStep 2060363 = 3090545) B3090545
theorem B2748491 : Blo 1220928 2748491 := bstep (se 1 (by rfl) ⟨2061368, by rfl⟩ : syracuseStep 2748491 = 4122737) B4122737
theorem B3477593 : Blo 1220928 3477593 := bstep (se 2 (by rfl) ⟨1304097, by rfl⟩ : syracuseStep 3477593 = 2608195) B2608195
theorem B2748545 : Blo 1220928 2748545 := bstep (se 2 (by rfl) ⟨1030704, by rfl⟩ : syracuseStep 2748545 = 2061409) B2061409
theorem B2060491 : Blo 1220928 2060491 := bstep (se 1 (by rfl) ⟨1545368, by rfl⟩ : syracuseStep 2060491 = 3090737) B3090737
theorem B2937035 : Blo 1220928 2937035 := bstep (se 1 (by rfl) ⟨2202776, by rfl⟩ : syracuseStep 2937035 = 4405553) B4405553
theorem B4124951 : Blo 1220928 4124951 := bstep (se 1 (by rfl) ⟨3093713, by rfl⟩ : syracuseStep 4124951 = 6187427) B6187427
theorem B2060633 : Blo 1220928 2060633 := bstep (se 2 (by rfl) ⟨772737, by rfl⟩ : syracuseStep 2060633 = 1545475) B1545475
theorem B2748761 : Blo 1220928 2748761 := bstep (se 2 (by rfl) ⟨1030785, by rfl⟩ : syracuseStep 2748761 = 2061571) B2061571
theorem B6181271 : Blo 1220928 6181271 := bstep (se 1 (by rfl) ⟨4635953, by rfl⟩ : syracuseStep 6181271 = 9271907) B9271907
theorem B2748851 : Blo 1220928 2748851 := bstep (se 1 (by rfl) ⟨2061638, by rfl⟩ : syracuseStep 2748851 = 4123277) B4123277
theorem B2609587 : Blo 1220928 2609587 := bstep (se 1 (by rfl) ⟨1957190, by rfl⟩ : syracuseStep 2609587 = 3914381) B3914381
theorem B22925747 : Blo 1220928 22925747 := bstep (se 1 (by rfl) ⟨17194310, by rfl⟩ : syracuseStep 22925747 = 34388621) B34388621
theorem B2748887 : Blo 1220928 2748887 := bstep (se 1 (by rfl) ⟨2061665, by rfl⟩ : syracuseStep 2748887 = 4123331) B4123331
theorem B2060761 : Blo 1220928 2060761 := bstep (se 2 (by rfl) ⟨772785, by rfl⟩ : syracuseStep 2060761 = 1545571) B1545571
theorem B17609177 : Blo 1220928 17609177 := bstep (se 2 (by rfl) ⟨6603441, by rfl⟩ : syracuseStep 17609177 = 13206883) B13206883
theorem B75280913 : Blo 1220928 75280913 := bstep (se 2 (by rfl) ⟨28230342, by rfl⟩ : syracuseStep 75280913 = 56460685) B56460685
theorem B1831499 : Blo 1220928 1831499 := bstep (se 1 (by rfl) ⟨1373624, by rfl⟩ : syracuseStep 1831499 = 2747249) B2747249
theorem B1831511 : Blo 1220928 1831511 := bstep (se 1 (by rfl) ⟨1373633, by rfl⟩ : syracuseStep 1831511 = 2747267) B2747267
theorem B5223001 : Blo 1220928 5223001 := bstep (se 2 (by rfl) ⟨1958625, by rfl⟩ : syracuseStep 5223001 = 3917251) B3917251
theorem B2749067 : Blo 1220928 2749067 := bstep (se 1 (by rfl) ⟨2061800, by rfl⟩ : syracuseStep 2749067 = 4123601) B4123601
theorem B1831577 : Blo 1220928 1831577 := bstep (se 2 (by rfl) ⟨686841, by rfl⟩ : syracuseStep 1831577 = 1373683) B1373683
theorem B2749121 : Blo 1220928 2749121 := bstep (se 2 (by rfl) ⟨1030920, by rfl⟩ : syracuseStep 2749121 = 2061841) B2061841
theorem B1831691 : Blo 1220928 1831691 := bstep (se 1 (by rfl) ⟨1373768, by rfl⟩ : syracuseStep 1831691 = 2747537) B2747537
theorem B9278225 : Blo 1220928 9278225 := bstep (se 2 (by rfl) ⟨3479334, by rfl⟩ : syracuseStep 9278225 = 6958669) B6958669
theorem B1831703 : Blo 1220928 1831703 := bstep (se 1 (by rfl) ⟨1373777, by rfl⟩ : syracuseStep 1831703 = 2747555) B2747555
theorem B15651629 : Blo 1220928 15651629 := bstep (se 3 (by rfl) ⟨2934680, by rfl⟩ : syracuseStep 15651629 = 5869361) B5869361
theorem B6443821 : Blo 1220928 6443821 := bstep (se 3 (by rfl) ⟨1208216, by rfl⟩ : syracuseStep 6443821 = 2416433) B2416433
theorem B3093299 : Blo 1220928 3093299 := bstep (se 1 (by rfl) ⟨2319974, by rfl⟩ : syracuseStep 3093299 = 4639949) B4639949
theorem B4125491 : Blo 1220928 4125491 := bstep (se 1 (by rfl) ⟨3094118, by rfl⟩ : syracuseStep 4125491 = 6188237) B6188237
theorem B2511703 : Blo 1220928 2511703 := bstep (se 1 (by rfl) ⟨1883777, by rfl⟩ : syracuseStep 2511703 = 3767555) B3767555
theorem B1831769 : Blo 1220928 1831769 := bstep (se 2 (by rfl) ⟨686913, by rfl⟩ : syracuseStep 1831769 = 1373827) B1373827
theorem B2749337 : Blo 1220928 2749337 := bstep (se 2 (by rfl) ⟨1031001, by rfl⟩ : syracuseStep 2749337 = 2062003) B2062003
theorem B1831883 : Blo 1220928 1831883 := bstep (se 1 (by rfl) ⟨1373912, by rfl⟩ : syracuseStep 1831883 = 2747825) B2747825
theorem B1831895 : Blo 1220928 1831895 := bstep (se 1 (by rfl) ⟨1373921, by rfl⟩ : syracuseStep 1831895 = 2747843) B2747843
theorem B2749427 : Blo 1220928 2749427 := bstep (se 1 (by rfl) ⟨2062070, by rfl⟩ : syracuseStep 2749427 = 4124141) B4124141
theorem B2061335 : Blo 1220928 2061335 := bstep (se 1 (by rfl) ⟨1546001, by rfl⟩ : syracuseStep 2061335 = 3092003) B3092003
theorem B2749463 : Blo 1220928 2749463 := bstep (se 1 (by rfl) ⟨2062097, by rfl⟩ : syracuseStep 2749463 = 4124195) B4124195
theorem B1831961 : Blo 1220928 1831961 := bstep (se 2 (by rfl) ⟨686985, by rfl⟩ : syracuseStep 1831961 = 1373971) B1373971
theorem B4125761 : Blo 1220928 4125761 := bstep (se 2 (by rfl) ⟨1547160, by rfl⟩ : syracuseStep 4125761 = 3094321) B3094321
theorem B8934475 : Blo 1220928 8934475 := bstep (se 1 (by rfl) ⟨6700856, by rfl⟩ : syracuseStep 8934475 = 13401713) B13401713
theorem B1832075 : Blo 1220928 1832075 := bstep (se 1 (by rfl) ⟨1374056, by rfl⟩ : syracuseStep 1832075 = 2748113) B2748113
theorem B1832087 : Blo 1220928 1832087 := bstep (se 1 (by rfl) ⟨1374065, by rfl⟩ : syracuseStep 1832087 = 2748131) B2748131
theorem B2061463 : Blo 1220928 2061463 := bstep (se 1 (by rfl) ⟨1546097, by rfl⟩ : syracuseStep 2061463 = 3092195) B3092195
theorem B1545419 : Blo 1220928 1545419 := bstep (se 1 (by rfl) ⟨1159064, by rfl⟩ : syracuseStep 1545419 = 2318129) B2318129
theorem B2749643 : Blo 1220928 2749643 := bstep (se 1 (by rfl) ⟨2062232, by rfl⟩ : syracuseStep 2749643 = 4124465) B4124465
theorem B1832153 : Blo 1220928 1832153 := bstep (se 2 (by rfl) ⟨687057, by rfl⟩ : syracuseStep 1832153 = 1374115) B1374115
theorem B2749697 : Blo 1220928 2749697 := bstep (se 2 (by rfl) ⟨1031136, by rfl⟩ : syracuseStep 2749697 = 2062273) B2062273
theorem B6960401 : Blo 1220928 6960401 := bstep (se 2 (by rfl) ⟨2610150, by rfl⟩ : syracuseStep 6960401 = 5220301) B5220301
theorem B1832267 : Blo 1220928 1832267 := bstep (se 1 (by rfl) ⟨1374200, by rfl⟩ : syracuseStep 1832267 = 2748401) B2748401
theorem B3093835 : Blo 1220928 3093835 := bstep (se 1 (by rfl) ⟨2320376, by rfl⟩ : syracuseStep 3093835 = 4640753) B4640753
theorem B1832279 : Blo 1220928 1832279 := bstep (se 1 (by rfl) ⟨1374209, by rfl⟩ : syracuseStep 1832279 = 2748419) B2748419
theorem B3913049 : Blo 1220928 3913049 := bstep (se 2 (by rfl) ⟨1467393, by rfl⟩ : syracuseStep 3913049 = 2934787) B2934787
theorem B1832345 : Blo 1220928 1832345 := bstep (se 2 (by rfl) ⟨687129, by rfl⟩ : syracuseStep 1832345 = 1374259) B1374259
theorem B1373611 : Blo 1220928 1373611 := bstep (se 1 (by rfl) ⟨1030208, by rfl⟩ : syracuseStep 1373611 = 2060417) B2060417
theorem B2119115 : Blo 1220928 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B2749913 : Blo 1220928 2749913 := bstep (se 2 (by rfl) ⟨1031217, by rfl⟩ : syracuseStep 2749913 = 2062435) B2062435
theorem B3093977 : Blo 1220928 3093977 := bstep (se 2 (by rfl) ⟨1160241, by rfl⟩ : syracuseStep 3093977 = 2320483) B2320483
theorem B1832459 : Blo 1220928 1832459 := bstep (se 1 (by rfl) ⟨1374344, by rfl⟩ : syracuseStep 1832459 = 2748689) B2748689
theorem B1373719 : Blo 1220928 1373719 := bstep (se 1 (by rfl) ⟨1030289, by rfl⟩ : syracuseStep 1373719 = 2060579) B2060579
theorem B1832471 : Blo 1220928 1832471 := bstep (se 1 (by rfl) ⟨1374353, by rfl⟩ : syracuseStep 1832471 = 2748707) B2748707
theorem B2750003 : Blo 1220928 2750003 := bstep (se 1 (by rfl) ⟨2062502, by rfl⟩ : syracuseStep 2750003 = 4125005) B4125005
theorem B4642379 : Blo 1220928 4642379 := bstep (se 1 (by rfl) ⟨3481784, by rfl⟩ : syracuseStep 4642379 = 6963569) B6963569
theorem B6190667 : Blo 1220928 6190667 := bstep (se 1 (by rfl) ⟨4643000, by rfl⟩ : syracuseStep 6190667 = 9286001) B9286001
theorem B2750039 : Blo 1220928 2750039 := bstep (se 1 (by rfl) ⟨2062529, by rfl⟩ : syracuseStep 2750039 = 4125059) B4125059
theorem B1832537 : Blo 1220928 1832537 := bstep (se 2 (by rfl) ⟨687201, by rfl⟩ : syracuseStep 1832537 = 1374403) B1374403
theorem B4642393 : Blo 1220928 4642393 := bstep (se 2 (by rfl) ⟨1740897, by rfl⟩ : syracuseStep 4642393 = 3481795) B3481795
theorem B4126301 : Blo 1220928 4126301 := bstep (se 3 (by rfl) ⟨773681, by rfl⟩ : syracuseStep 4126301 = 1547363) B1547363
theorem B3479233 : Blo 1220928 3479233 := bstep (se 2 (by rfl) ⟨1304712, by rfl⟩ : syracuseStep 3479233 = 2609425) B2609425
theorem B1373899 : Blo 1220928 1373899 := bstep (se 1 (by rfl) ⟨1030424, by rfl⟩ : syracuseStep 1373899 = 2060849) B2060849
theorem B1832651 : Blo 1220928 1832651 := bstep (se 1 (by rfl) ⟨1374488, by rfl⟩ : syracuseStep 1832651 = 2748977) B2748977
theorem B1832663 : Blo 1220928 1832663 := bstep (se 1 (by rfl) ⟨1374497, by rfl⟩ : syracuseStep 1832663 = 2748995) B2748995
theorem B2062091 : Blo 1220928 2062091 := bstep (se 1 (by rfl) ⟨1546568, by rfl⟩ : syracuseStep 2062091 = 3093137) B3093137
theorem B2750219 : Blo 1220928 2750219 := bstep (se 1 (by rfl) ⟨2062664, by rfl⟩ : syracuseStep 2750219 = 4125329) B4125329
theorem B7051025 : Blo 1220928 7051025 := bstep (se 2 (by rfl) ⟨2644134, by rfl⟩ : syracuseStep 7051025 = 5288269) B5288269
theorem B1857305 : Blo 1220928 1857305 := bstep (se 2 (by rfl) ⟨696489, by rfl⟩ : syracuseStep 1857305 = 1392979) B1392979
theorem B1832729 : Blo 1220928 1832729 := bstep (se 2 (by rfl) ⟨687273, by rfl⟩ : syracuseStep 1832729 = 1374547) B1374547
theorem B1374007 : Blo 1220928 1374007 := bstep (se 1 (by rfl) ⟨1030505, by rfl⟩ : syracuseStep 1374007 = 2061011) B2061011
theorem B2750273 : Blo 1220928 2750273 := bstep (se 2 (by rfl) ⟨1031352, by rfl⟩ : syracuseStep 2750273 = 2062705) B2062705
theorem B2611073 : Blo 1220928 2611073 := bstep (se 2 (by rfl) ⟨979152, by rfl⟩ : syracuseStep 2611073 = 1958305) B1958305
theorem B1546123 : Blo 1220928 1546123 := bstep (se 1 (by rfl) ⟨1159592, by rfl⟩ : syracuseStep 1546123 = 2319185) B2319185
theorem B1832843 : Blo 1220928 1832843 := bstep (se 1 (by rfl) ⟨1374632, by rfl⟩ : syracuseStep 1832843 = 2749265) B2749265
theorem B2062219 : Blo 1220928 2062219 := bstep (se 1 (by rfl) ⟨1546664, by rfl⟩ : syracuseStep 2062219 = 3093329) B3093329
theorem B1832855 : Blo 1220928 1832855 := bstep (se 1 (by rfl) ⟨1374641, by rfl⟩ : syracuseStep 1832855 = 2749283) B2749283
theorem B59488177 : Blo 1220928 59488177 := bstep (se 2 (by rfl) ⟨22308066, by rfl⟩ : syracuseStep 59488177 = 44616133) B44616133
theorem B1832921 : Blo 1220928 1832921 := bstep (se 2 (by rfl) ⟨687345, by rfl⟩ : syracuseStep 1832921 = 1374691) B1374691
theorem B1374187 : Blo 1220928 1374187 := bstep (se 1 (by rfl) ⟨1030640, by rfl⟩ : syracuseStep 1374187 = 2061281) B2061281
theorem B15267857 : Blo 1220928 15267857 := bstep (se 2 (by rfl) ⟨5725446, by rfl⟩ : syracuseStep 15267857 = 11450893) B11450893
theorem B9910289 : Blo 1220928 9910289 := bstep (se 2 (by rfl) ⟨3716358, by rfl⟩ : syracuseStep 9910289 = 7432717) B7432717
theorem B2062361 : Blo 1220928 2062361 := bstep (se 2 (by rfl) ⟨773385, by rfl⟩ : syracuseStep 2062361 = 1546771) B1546771
theorem B2750489 : Blo 1220928 2750489 := bstep (se 2 (by rfl) ⟨1031433, by rfl⟩ : syracuseStep 2750489 = 2062867) B2062867
theorem B1833035 : Blo 1220928 1833035 := bstep (se 1 (by rfl) ⟨1374776, by rfl⟩ : syracuseStep 1833035 = 2749553) B2749553
theorem B1374295 : Blo 1220928 1374295 := bstep (se 1 (by rfl) ⟨1030721, by rfl⟩ : syracuseStep 1374295 = 2061443) B2061443
theorem B1833047 : Blo 1220928 1833047 := bstep (se 1 (by rfl) ⟨1374785, by rfl⟩ : syracuseStep 1833047 = 2749571) B2749571
theorem B2750579 : Blo 1220928 2750579 := bstep (se 1 (by rfl) ⟨2062934, by rfl⟩ : syracuseStep 2750579 = 4125869) B4125869
theorem B11737219 : Blo 1220928 11737219 := bstep (se 1 (by rfl) ⟨8802914, by rfl⟩ : syracuseStep 11737219 = 17605829) B17605829
theorem B1546391 : Blo 1220928 1546391 := bstep (se 1 (by rfl) ⟨1159793, by rfl⟩ : syracuseStep 1546391 = 2319587) B2319587
theorem B2750615 : Blo 1220928 2750615 := bstep (se 1 (by rfl) ⟨2062961, by rfl⟩ : syracuseStep 2750615 = 4125923) B4125923
theorem B1833113 : Blo 1220928 1833113 := bstep (se 2 (by rfl) ⟨687417, by rfl⟩ : syracuseStep 1833113 = 1374835) B1374835
theorem B2062489 : Blo 1220928 2062489 := bstep (se 2 (by rfl) ⟨773433, by rfl⟩ : syracuseStep 2062489 = 1546867) B1546867
theorem B2611415 : Blo 1220928 2611415 := bstep (se 1 (by rfl) ⟨1958561, by rfl⟩ : syracuseStep 2611415 = 3917123) B3917123
theorem B1374475 : Blo 1220928 1374475 := bstep (se 1 (by rfl) ⟨1030856, by rfl⟩ : syracuseStep 1374475 = 2061713) B2061713
theorem B1833227 : Blo 1220928 1833227 := bstep (se 1 (by rfl) ⟨1374920, by rfl⟩ : syracuseStep 1833227 = 2749841) B2749841
theorem B6600977 : Blo 1220928 6600977 := bstep (se 2 (by rfl) ⟨2475366, by rfl⟩ : syracuseStep 6600977 = 4950733) B4950733
theorem B1833239 : Blo 1220928 1833239 := bstep (se 1 (by rfl) ⟨1374929, by rfl⟩ : syracuseStep 1833239 = 2749859) B2749859
theorem B3094807 : Blo 1220928 3094807 := bstep (se 1 (by rfl) ⟨2321105, by rfl⟩ : syracuseStep 3094807 = 4642211) B4642211
theorem B5577005 : Blo 1220928 5577005 := bstep (se 3 (by rfl) ⟨1045688, by rfl⟩ : syracuseStep 5577005 = 2091377) B2091377
theorem B2750795 : Blo 1220928 2750795 := bstep (se 1 (by rfl) ⟨2063096, by rfl⟩ : syracuseStep 2750795 = 4126193) B4126193
theorem B1833305 : Blo 1220928 1833305 := bstep (se 2 (by rfl) ⟨687489, by rfl⟩ : syracuseStep 1833305 = 1374979) B1374979
theorem B1374583 : Blo 1220928 1374583 := bstep (se 1 (by rfl) ⟨1030937, by rfl⟩ : syracuseStep 1374583 = 2061875) B2061875
theorem B2750849 : Blo 1220928 2750849 := bstep (se 2 (by rfl) ⟨1031568, by rfl⟩ : syracuseStep 2750849 = 2063137) B2063137
theorem B5216663 : Blo 1220928 5216663 := bstep (se 1 (by rfl) ⟨3912497, by rfl⟩ : syracuseStep 5216663 = 7824995) B7824995
theorem B7829939 : Blo 1220928 7829939 := bstep (se 1 (by rfl) ⟨5872454, by rfl⟩ : syracuseStep 7829939 = 11744909) B11744909
theorem B1833419 : Blo 1220928 1833419 := bstep (se 1 (by rfl) ⟨1375064, by rfl⟩ : syracuseStep 1833419 = 2750129) B2750129
theorem B1833431 : Blo 1220928 1833431 := bstep (se 1 (by rfl) ⟨1375073, by rfl⟩ : syracuseStep 1833431 = 2750147) B2750147
theorem B2202113 : Blo 1220928 2202113 := bstep (se 2 (by rfl) ⟨825792, by rfl⟩ : syracuseStep 2202113 = 1651585) B1651585
theorem B2611723 : Blo 1220928 2611723 := bstep (se 1 (by rfl) ⟨1958792, by rfl⟩ : syracuseStep 2611723 = 3917585) B3917585
theorem B1833497 : Blo 1220928 1833497 := bstep (se 2 (by rfl) ⟨687561, by rfl⟩ : syracuseStep 1833497 = 1375123) B1375123
theorem B1374763 : Blo 1220928 1374763 := bstep (se 1 (by rfl) ⟨1031072, by rfl⟩ : syracuseStep 1374763 = 2062145) B2062145
theorem B2751065 : Blo 1220928 2751065 := bstep (se 2 (by rfl) ⟨1031649, by rfl⟩ : syracuseStep 2751065 = 2063299) B2063299
theorem B1833611 : Blo 1220928 1833611 := bstep (se 1 (by rfl) ⟨1375208, by rfl⟩ : syracuseStep 1833611 = 2750417) B2750417
theorem B5569175 : Blo 1220928 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B1374871 : Blo 1220928 1374871 := bstep (se 1 (by rfl) ⟨1031153, by rfl⟩ : syracuseStep 1374871 = 2062307) B2062307
theorem B1833623 : Blo 1220928 1833623 := bstep (se 1 (by rfl) ⟨1375217, by rfl⟩ : syracuseStep 1833623 = 2750435) B2750435
theorem B2751155 : Blo 1220928 2751155 := bstep (se 1 (by rfl) ⟨2063366, by rfl⟩ : syracuseStep 2751155 = 4126733) B4126733
theorem B3095243 : Blo 1220928 3095243 := bstep (se 1 (by rfl) ⟨2321432, by rfl⟩ : syracuseStep 3095243 = 4642865) B4642865
theorem B2063063 : Blo 1220928 2063063 := bstep (se 1 (by rfl) ⟨1547297, by rfl⟩ : syracuseStep 2063063 = 3094595) B3094595
theorem B2751191 : Blo 1220928 2751191 := bstep (se 1 (by rfl) ⟨2063393, by rfl⟩ : syracuseStep 2751191 = 4126787) B4126787
theorem B1833689 : Blo 1220928 1833689 := bstep (se 2 (by rfl) ⟨687633, by rfl⟩ : syracuseStep 1833689 = 1375267) B1375267
theorem B1375051 : Blo 1220928 1375051 := bstep (se 1 (by rfl) ⟨1031288, by rfl⟩ : syracuseStep 1375051 = 2062577) B2062577
theorem B1833803 : Blo 1220928 1833803 := bstep (se 1 (by rfl) ⟨1375352, by rfl⟩ : syracuseStep 1833803 = 2750705) B2750705
theorem B1547095 : Blo 1220928 1547095 := bstep (se 1 (by rfl) ⟨1160321, by rfl⟩ : syracuseStep 1547095 = 2320643) B2320643
theorem B1833815 : Blo 1220928 1833815 := bstep (se 1 (by rfl) ⟨1375361, by rfl⟩ : syracuseStep 1833815 = 2750723) B2750723
theorem B2063191 : Blo 1220928 2063191 := bstep (se 1 (by rfl) ⟨1547393, by rfl⟩ : syracuseStep 2063191 = 3094787) B3094787
theorem B2751371 : Blo 1220928 2751371 := bstep (se 1 (by rfl) ⟨2063528, by rfl⟩ : syracuseStep 2751371 = 4127057) B4127057
theorem B1833881 : Blo 1220928 1833881 := bstep (se 2 (by rfl) ⟨687705, by rfl⟩ : syracuseStep 1833881 = 1375411) B1375411
theorem B1375159 : Blo 1220928 1375159 := bstep (se 1 (by rfl) ⟨1031369, by rfl⟩ : syracuseStep 1375159 = 2062739) B2062739
theorem B3914689 : Blo 1220928 3914689 := bstep (se 2 (by rfl) ⟨1468008, by rfl⟩ : syracuseStep 3914689 = 2936017) B2936017
theorem B81476549 : Blo 1220928 81476549 := bstep (se 4 (by rfl) ⟨7638426, by rfl⟩ : syracuseStep 81476549 = 15276853) B15276853
theorem B2751425 : Blo 1220928 2751425 := bstep (se 2 (by rfl) ⟨1031784, by rfl⟩ : syracuseStep 2751425 = 2063569) B2063569
theorem B1833995 : Blo 1220928 1833995 := bstep (se 1 (by rfl) ⟨1375496, by rfl⟩ : syracuseStep 1833995 = 2750993) B2750993
theorem B1834007 : Blo 1220928 1834007 := bstep (se 1 (by rfl) ⟨1375505, by rfl⟩ : syracuseStep 1834007 = 2751011) B2751011
theorem B1834073 : Blo 1220928 1834073 := bstep (se 2 (by rfl) ⟨687777, by rfl⟩ : syracuseStep 1834073 = 1375555) B1375555
theorem B1375339 : Blo 1220928 1375339 := bstep (se 1 (by rfl) ⟨1031504, by rfl⟩ : syracuseStep 1375339 = 2063009) B2063009
theorem B1834187 : Blo 1220928 1834187 := bstep (se 1 (by rfl) ⟨1375640, by rfl⟩ : syracuseStep 1834187 = 2751281) B2751281
theorem B1858775 : Blo 1220928 1858775 := bstep (se 1 (by rfl) ⟨1394081, by rfl⟩ : syracuseStep 1858775 = 2788163) B2788163
theorem B1375447 : Blo 1220928 1375447 := bstep (se 1 (by rfl) ⟨1031585, by rfl⟩ : syracuseStep 1375447 = 2063171) B2063171
theorem B1834199 : Blo 1220928 1834199 := bstep (se 1 (by rfl) ⟨1375649, by rfl⟩ : syracuseStep 1834199 = 2751299) B2751299
theorem B4463837 : Blo 1220928 4463837 := bstep (se 3 (by rfl) ⟨836969, by rfl⟩ : syracuseStep 4463837 = 1673939) B1673939
theorem B6610193 : Blo 1220928 6610193 := bstep (se 2 (by rfl) ⟨2478822, by rfl⟩ : syracuseStep 6610193 = 4957645) B4957645
theorem B1834265 : Blo 1220928 1834265 := bstep (se 2 (by rfl) ⟨687849, by rfl⟩ : syracuseStep 1834265 = 1375699) B1375699
theorem B3480907 : Blo 1220928 3480907 := bstep (se 1 (by rfl) ⟨2610680, by rfl⟩ : syracuseStep 3480907 = 5221361) B5221361
theorem B1375627 : Blo 1220928 1375627 := bstep (se 1 (by rfl) ⟨1031720, by rfl⟩ : syracuseStep 1375627 = 2063441) B2063441
theorem B1834379 : Blo 1220928 1834379 := bstep (se 1 (by rfl) ⟨1375784, by rfl⟩ : syracuseStep 1834379 = 2751569) B2751569
theorem B1834391 : Blo 1220928 1834391 := bstep (se 1 (by rfl) ⟨1375793, by rfl⟩ : syracuseStep 1834391 = 2751587) B2751587
theorem B15670745 : Blo 1220928 15670745 := bstep (se 2 (by rfl) ⟨5876529, by rfl⟩ : syracuseStep 15670745 = 11753059) B11753059
theorem B1375735 : Blo 1220928 1375735 := bstep (se 1 (by rfl) ⟨1031801, by rfl⟩ : syracuseStep 1375735 = 2063603) B2063603
theorem B4955651 : Blo 1220928 4955651 := bstep (se 1 (by rfl) ⟨3716738, by rfl⟩ : syracuseStep 4955651 = 7433477) B7433477
theorem B1859147 : Blo 1220928 1859147 := bstep (se 1 (by rfl) ⟨1394360, by rfl⟩ : syracuseStep 1859147 = 2788721) B2788721
theorem B3481181 : Blo 1220928 3481181 := bstep (se 3 (by rfl) ⟨652721, by rfl⟩ : syracuseStep 3481181 = 1305443) B1305443
theorem B1392331 : Blo 1220928 1392331 := bstep (se 1 (by rfl) ⟨1044248, by rfl⟩ : syracuseStep 1392331 = 2088497) B2088497
theorem B28196707 : Blo 1220928 28196707 := bstep (se 1 (by rfl) ⟨21147530, by rfl⟩ : syracuseStep 28196707 = 42295061) B42295061
theorem B4636547 : Blo 1220928 4636547 := bstep (se 1 (by rfl) ⟨3477410, by rfl⟩ : syracuseStep 4636547 = 6954821) B6954821
theorem B6184835 : Blo 1220928 6184835 := bstep (se 1 (by rfl) ⟨4638626, by rfl⟩ : syracuseStep 6184835 = 9277253) B9277253
theorem B4636561 : Blo 1220928 4636561 := bstep (se 2 (by rfl) ⟨1738710, by rfl⟩ : syracuseStep 4636561 = 3477421) B3477421
theorem B7938071 : Blo 1220928 7938071 := bstep (se 1 (by rfl) ⟨5953553, by rfl⟩ : syracuseStep 7938071 = 11907107) B11907107
theorem B40714285 : Blo 1220928 40714285 := bstep (se 3 (by rfl) ⟨7633928, by rfl⟩ : syracuseStep 40714285 = 15267857) B15267857
theorem B2318395 : Blo 1220928 2318395 := bstep (se 1 (by rfl) ⟨1738796, by rfl⟩ : syracuseStep 2318395 = 3477593) B3477593
theorem B9904189 : Blo 1220928 9904189 := bstep (se 3 (by rfl) ⟨1857035, by rfl⟩ : syracuseStep 9904189 = 3714071) B3714071
theorem B44589149 : Blo 1220928 44589149 := bstep (se 3 (by rfl) ⟨8360465, by rfl⟩ : syracuseStep 44589149 = 16720931) B16720931
theorem B1958023 : Blo 1220928 1958023 := bstep (se 1 (by rfl) ⟨1468517, by rfl⟩ : syracuseStep 1958023 = 2937035) B2937035
theorem B2973953 : Blo 1220928 2973953 := bstep (se 2 (by rfl) ⟨1115232, by rfl⟩ : syracuseStep 2973953 = 2230465) B2230465
theorem B4120847 : Blo 1220928 4120847 := bstep (se 1 (by rfl) ⟨3090635, by rfl⟩ : syracuseStep 4120847 = 6181271) B6181271
theorem B11739451 : Blo 1220928 11739451 := bstep (se 1 (by rfl) ⟨8804588, by rfl⟩ : syracuseStep 11739451 = 17609177) B17609177
theorem B128647541 : Blo 1220928 128647541 := bstep (se 5 (by rfl) ⟨6030353, by rfl⟩ : syracuseStep 128647541 = 12060707) B12060707
theorem B1220999 : Blo 1220928 1220999 := bstep (se 1 (by rfl) ⟨915749, by rfl⟩ : syracuseStep 1220999 = 1831499) B1831499
theorem B1221007 : Blo 1220928 1221007 := bstep (se 1 (by rfl) ⟨915755, by rfl⟩ : syracuseStep 1221007 = 1831511) B1831511
theorem B1221051 : Blo 1220928 1221051 := bstep (se 1 (by rfl) ⟨915788, by rfl⟩ : syracuseStep 1221051 = 1831577) B1831577
theorem B1221127 : Blo 1220928 1221127 := bstep (se 1 (by rfl) ⟨915845, by rfl⟩ : syracuseStep 1221127 = 1831691) B1831691
theorem B6185483 : Blo 1220928 6185483 := bstep (se 1 (by rfl) ⟨4639112, by rfl⟩ : syracuseStep 6185483 = 9278225) B9278225
theorem B1221135 : Blo 1220928 1221135 := bstep (se 1 (by rfl) ⟨915851, by rfl⟩ : syracuseStep 1221135 = 1831703) B1831703
theorem B4121117 : Blo 1220928 4121117 := bstep (se 3 (by rfl) ⟨772709, by rfl⟩ : syracuseStep 4121117 = 1545419) B1545419
theorem B2318881 : Blo 1220928 2318881 := bstep (se 2 (by rfl) ⟨869580, by rfl⟩ : syracuseStep 2318881 = 1739161) B1739161
theorem B1221179 : Blo 1220928 1221179 := bstep (se 1 (by rfl) ⟨915884, by rfl⟩ : syracuseStep 1221179 = 1831769) B1831769
theorem B4956733 : Blo 1220928 4956733 := bstep (se 3 (by rfl) ⟨929387, by rfl⟩ : syracuseStep 4956733 = 1858775) B1858775
theorem B1221255 : Blo 1220928 1221255 := bstep (se 1 (by rfl) ⟨915941, by rfl⟩ : syracuseStep 1221255 = 1831883) B1831883
theorem B1221263 : Blo 1220928 1221263 := bstep (se 1 (by rfl) ⟨915947, by rfl⟩ : syracuseStep 1221263 = 1831895) B1831895
theorem B6185645 : Blo 1220928 6185645 := bstep (se 3 (by rfl) ⟨1159808, by rfl⟩ : syracuseStep 6185645 = 2319617) B2319617
theorem B3482297 : Blo 1220928 3482297 := bstep (se 2 (by rfl) ⟨1305861, by rfl⟩ : syracuseStep 3482297 = 2611723) B2611723
theorem B1221307 : Blo 1220928 1221307 := bstep (se 1 (by rfl) ⟨915980, by rfl⟩ : syracuseStep 1221307 = 1831961) B1831961
theorem B1221383 : Blo 1220928 1221383 := bstep (se 1 (by rfl) ⟨916037, by rfl⟩ : syracuseStep 1221383 = 1832075) B1832075
theorem B1221391 : Blo 1220928 1221391 := bstep (se 1 (by rfl) ⟨916043, by rfl⟩ : syracuseStep 1221391 = 1832087) B1832087
theorem B6964001 : Blo 1220928 6964001 := bstep (se 2 (by rfl) ⟨2611500, by rfl⟩ : syracuseStep 6964001 = 5223001) B5223001
theorem B1221435 : Blo 1220928 1221435 := bstep (se 1 (by rfl) ⟨916076, by rfl⟩ : syracuseStep 1221435 = 1832153) B1832153
theorem B1221511 : Blo 1220928 1221511 := bstep (se 1 (by rfl) ⟨916133, by rfl⟩ : syracuseStep 1221511 = 1832267) B1832267
theorem B1221519 : Blo 1220928 1221519 := bstep (se 1 (by rfl) ⟨916139, by rfl⟩ : syracuseStep 1221519 = 1832279) B1832279
theorem B3302329 : Blo 1220928 3302329 := bstep (se 2 (by rfl) ⟨1238373, by rfl⟩ : syracuseStep 3302329 = 2476747) B2476747
theorem B1221563 : Blo 1220928 1221563 := bstep (se 1 (by rfl) ⟨916172, by rfl⟩ : syracuseStep 1221563 = 1832345) B1832345
theorem B1221639 : Blo 1220928 1221639 := bstep (se 1 (by rfl) ⟨916229, by rfl⟩ : syracuseStep 1221639 = 1832459) B1832459
theorem B1221647 : Blo 1220928 1221647 := bstep (se 1 (by rfl) ⟨916235, by rfl⟩ : syracuseStep 1221647 = 1832471) B1832471
theorem B1221691 : Blo 1220928 1221691 := bstep (se 1 (by rfl) ⟨916268, by rfl⟩ : syracuseStep 1221691 = 1832537) B1832537
theorem B1221767 : Blo 1220928 1221767 := bstep (se 1 (by rfl) ⟨916325, by rfl⟩ : syracuseStep 1221767 = 1832651) B1832651
theorem B1221775 : Blo 1220928 1221775 := bstep (se 1 (by rfl) ⟨916331, by rfl⟩ : syracuseStep 1221775 = 1832663) B1832663
theorem B1238203 : Blo 1220928 1238203 := bstep (se 1 (by rfl) ⟨928652, by rfl⟩ : syracuseStep 1238203 = 1857305) B1857305
theorem B1221819 : Blo 1220928 1221819 := bstep (se 1 (by rfl) ⟨916364, by rfl⟩ : syracuseStep 1221819 = 1832729) B1832729
theorem B3015937 : Blo 1220928 3015937 := bstep (se 2 (by rfl) ⟨1130976, by rfl⟩ : syracuseStep 3015937 = 2261953) B2261953
theorem B5219585 : Blo 1220928 5219585 := bstep (se 2 (by rfl) ⟨1957344, by rfl⟩ : syracuseStep 5219585 = 3914689) B3914689
theorem B1221895 : Blo 1220928 1221895 := bstep (se 1 (by rfl) ⟨916421, by rfl⟩ : syracuseStep 1221895 = 1832843) B1832843
theorem B1221903 : Blo 1220928 1221903 := bstep (se 1 (by rfl) ⟨916427, by rfl⟩ : syracuseStep 1221903 = 1832855) B1832855
theorem B1221947 : Blo 1220928 1221947 := bstep (se 1 (by rfl) ⟨916460, by rfl⟩ : syracuseStep 1221947 = 1832921) B1832921
theorem B1222023 : Blo 1220928 1222023 := bstep (se 1 (by rfl) ⟨916517, by rfl⟩ : syracuseStep 1222023 = 1833035) B1833035
theorem B1222031 : Blo 1220928 1222031 := bstep (se 1 (by rfl) ⟨916523, by rfl⟩ : syracuseStep 1222031 = 1833047) B1833047
theorem B11912633 : Blo 1220928 11912633 := bstep (se 2 (by rfl) ⟨4467237, by rfl⟩ : syracuseStep 11912633 = 8934475) B8934475
theorem B1222075 : Blo 1220928 1222075 := bstep (se 1 (by rfl) ⟨916556, by rfl⟩ : syracuseStep 1222075 = 1833113) B1833113
theorem B7538179 : Blo 1220928 7538179 := bstep (se 1 (by rfl) ⟨5653634, by rfl⟩ : syracuseStep 7538179 = 11307269) B11307269
theorem B1222151 : Blo 1220928 1222151 := bstep (se 1 (by rfl) ⟨916613, by rfl⟩ : syracuseStep 1222151 = 1833227) B1833227
theorem B4400651 : Blo 1220928 4400651 := bstep (se 1 (by rfl) ⟨3300488, by rfl⟩ : syracuseStep 4400651 = 6600977) B6600977
theorem B1222159 : Blo 1220928 1222159 := bstep (se 1 (by rfl) ⟨916619, by rfl⟩ : syracuseStep 1222159 = 1833239) B1833239
theorem B1222203 : Blo 1220928 1222203 := bstep (se 1 (by rfl) ⟨916652, by rfl⟩ : syracuseStep 1222203 = 1833305) B1833305
theorem B5219959 : Blo 1220928 5219959 := bstep (se 1 (by rfl) ⟨3914969, by rfl⟩ : syracuseStep 5219959 = 7829939) B7829939
theorem B1222279 : Blo 1220928 1222279 := bstep (se 1 (by rfl) ⟨916709, by rfl⟩ : syracuseStep 1222279 = 1833419) B1833419
theorem B1222287 : Blo 1220928 1222287 := bstep (se 1 (by rfl) ⟨916715, by rfl⟩ : syracuseStep 1222287 = 1833431) B1833431
theorem B1222331 : Blo 1220928 1222331 := bstep (se 1 (by rfl) ⟨916748, by rfl⟩ : syracuseStep 1222331 = 1833497) B1833497
theorem B2320073 : Blo 1220928 2320073 := bstep (se 2 (by rfl) ⟨870027, by rfl⟩ : syracuseStep 2320073 = 1740055) B1740055
theorem B1222407 : Blo 1220928 1222407 := bstep (se 1 (by rfl) ⟨916805, by rfl⟩ : syracuseStep 1222407 = 1833611) B1833611
theorem B10438415 : Blo 1220928 10438415 := bstep (se 1 (by rfl) ⟨7828811, by rfl⟩ : syracuseStep 10438415 = 15657623) B15657623
theorem B1222415 : Blo 1220928 1222415 := bstep (se 1 (by rfl) ⟨916811, by rfl⟩ : syracuseStep 1222415 = 1833623) B1833623
theorem B1222459 : Blo 1220928 1222459 := bstep (se 1 (by rfl) ⟨916844, by rfl⟩ : syracuseStep 1222459 = 1833689) B1833689
theorem B1738631 : Blo 1220928 1738631 := bstep (se 1 (by rfl) ⟨1303973, by rfl⟩ : syracuseStep 1738631 = 2607947) B2607947
theorem B1222535 : Blo 1220928 1222535 := bstep (se 1 (by rfl) ⟨916901, by rfl⟩ : syracuseStep 1222535 = 1833803) B1833803
theorem B1222543 : Blo 1220928 1222543 := bstep (se 1 (by rfl) ⟨916907, by rfl⟩ : syracuseStep 1222543 = 1833815) B1833815
theorem B4122521 : Blo 1220928 4122521 := bstep (se 2 (by rfl) ⟨1545945, by rfl⟩ : syracuseStep 4122521 = 3091891) B3091891
theorem B1222587 : Blo 1220928 1222587 := bstep (se 1 (by rfl) ⟨916940, by rfl⟩ : syracuseStep 1222587 = 1833881) B1833881
theorem B1222663 : Blo 1220928 1222663 := bstep (se 1 (by rfl) ⟨916997, by rfl⟩ : syracuseStep 1222663 = 1833995) B1833995
theorem B1222671 : Blo 1220928 1222671 := bstep (se 1 (by rfl) ⟨917003, by rfl⟩ : syracuseStep 1222671 = 1834007) B1834007
theorem B1222715 : Blo 1220928 1222715 := bstep (se 1 (by rfl) ⟨917036, by rfl⟩ : syracuseStep 1222715 = 1834073) B1834073
theorem B1222791 : Blo 1220928 1222791 := bstep (se 1 (by rfl) ⟨917093, by rfl⟩ : syracuseStep 1222791 = 1834187) B1834187
theorem B1222799 : Blo 1220928 1222799 := bstep (se 1 (by rfl) ⟨917099, by rfl⟩ : syracuseStep 1222799 = 1834199) B1834199
theorem B2975891 : Blo 1220928 2975891 := bstep (se 1 (by rfl) ⟨2231918, by rfl⟩ : syracuseStep 2975891 = 4463837) B4463837
theorem B1222843 : Blo 1220928 1222843 := bstep (se 1 (by rfl) ⟨917132, by rfl⟩ : syracuseStep 1222843 = 1834265) B1834265
theorem B4638977 : Blo 1220928 4638977 := bstep (se 2 (by rfl) ⟨1739616, by rfl⟩ : syracuseStep 4638977 = 3479233) B3479233
theorem B6187265 : Blo 1220928 6187265 := bstep (se 2 (by rfl) ⟨2320224, by rfl⟩ : syracuseStep 6187265 = 4640449) B4640449
theorem B1222919 : Blo 1220928 1222919 := bstep (se 1 (by rfl) ⟨917189, by rfl⟩ : syracuseStep 1222919 = 1834379) B1834379
theorem B4638991 : Blo 1220928 4638991 := bstep (se 1 (by rfl) ⟨3479243, by rfl⟩ : syracuseStep 4638991 = 6958487) B6958487
theorem B1222927 : Blo 1220928 1222927 := bstep (se 1 (by rfl) ⟨917195, by rfl⟩ : syracuseStep 1222927 = 1834391) B1834391
theorem B1411387 : Blo 1220928 1411387 := bstep (se 1 (by rfl) ⟨1058540, by rfl⟩ : syracuseStep 1411387 = 2117081) B2117081
theorem B10447163 : Blo 1220928 10447163 := bstep (se 1 (by rfl) ⟨7835372, by rfl⟩ : syracuseStep 10447163 = 15670745) B15670745
theorem B3303767 : Blo 1220928 3303767 := bstep (se 1 (by rfl) ⟨2477825, by rfl⟩ : syracuseStep 3303767 = 4955651) B4955651
theorem B1239431 : Blo 1220928 1239431 := bstep (se 1 (by rfl) ⟨929573, by rfl⟩ : syracuseStep 1239431 = 1859147) B1859147
theorem B9275795 : Blo 1220928 9275795 := bstep (se 1 (by rfl) ⟨6956846, by rfl⟩ : syracuseStep 9275795 = 13913693) B13913693
theorem B2320787 : Blo 1220928 2320787 := bstep (se 1 (by rfl) ⟨1740590, by rfl⟩ : syracuseStep 2320787 = 3481181) B3481181
theorem B2320825 : Blo 1220928 2320825 := bstep (se 2 (by rfl) ⟨870309, by rfl⟩ : syracuseStep 2320825 = 1740619) B1740619
theorem B37595609 : Blo 1220928 37595609 := bstep (se 2 (by rfl) ⟨14098353, by rfl⟩ : syracuseStep 37595609 = 28196707) B28196707
theorem B79317569 : Blo 1220928 79317569 := bstep (se 2 (by rfl) ⟨29744088, by rfl⟩ : syracuseStep 79317569 = 59488177) B59488177
theorem B3091031 : Blo 1220928 3091031 := bstep (se 1 (by rfl) ⟨2318273, by rfl⟩ : syracuseStep 3091031 = 4636547) B4636547
theorem B4123223 : Blo 1220928 4123223 := bstep (se 1 (by rfl) ⟨3092417, by rfl⟩ : syracuseStep 4123223 = 6184835) B6184835
theorem B13208183 : Blo 1220928 13208183 := bstep (se 1 (by rfl) ⟨9906137, by rfl⟩ : syracuseStep 13208183 = 19812275) B19812275
theorem B3304207 : Blo 1220928 3304207 := bstep (se 1 (by rfl) ⟨2478155, by rfl⟩ : syracuseStep 3304207 = 4956311) B4956311
theorem B3091243 : Blo 1220928 3091243 := bstep (se 1 (by rfl) ⟨2318432, by rfl⟩ : syracuseStep 3091243 = 4636865) B4636865
theorem B2747195 : Blo 1220928 2747195 := bstep (se 1 (by rfl) ⟨2060396, by rfl⟩ : syracuseStep 2747195 = 4120793) B4120793
theorem B15649625 : Blo 1220928 15649625 := bstep (se 2 (by rfl) ⟨5868609, by rfl⟩ : syracuseStep 15649625 = 11737219) B11737219
theorem B2747321 : Blo 1220928 2747321 := bstep (se 2 (by rfl) ⟨1030245, by rfl⟩ : syracuseStep 2747321 = 2060491) B2060491
theorem B3091385 : Blo 1220928 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B50187275 : Blo 1220928 50187275 := bstep (se 1 (by rfl) ⟨37640456, by rfl⟩ : syracuseStep 50187275 = 75280913) B75280913
theorem B6188075 : Blo 1220928 6188075 := bstep (se 1 (by rfl) ⟨4641056, by rfl⟩ : syracuseStep 6188075 = 9282113) B9282113
theorem B4123709 : Blo 1220928 4123709 := bstep (se 3 (by rfl) ⟨773195, by rfl⟩ : syracuseStep 4123709 = 1546391) B1546391
theorem B26405975 : Blo 1220928 26405975 := bstep (se 1 (by rfl) ⟨19804481, by rfl⟩ : syracuseStep 26405975 = 39608963) B39608963
theorem B2747663 : Blo 1220928 2747663 := bstep (se 1 (by rfl) ⟨2060747, by rfl⟩ : syracuseStep 2747663 = 4121495) B4121495
theorem B2747681 : Blo 1220928 2747681 := bstep (se 2 (by rfl) ⟨1030380, by rfl⟩ : syracuseStep 2747681 = 2060761) B2060761
theorem B7834913 : Blo 1220928 7834913 := bstep (se 2 (by rfl) ⟨2938092, by rfl⟩ : syracuseStep 7834913 = 5876185) B5876185
theorem B1740089 : Blo 1220928 1740089 := bstep (se 2 (by rfl) ⟨652533, by rfl⟩ : syracuseStep 1740089 = 1305067) B1305067
theorem B2682247 : Blo 1220928 2682247 := bstep (se 1 (by rfl) ⟨2011685, by rfl⟩ : syracuseStep 2682247 = 4023371) B4023371
theorem B4640267 : Blo 1220928 4640267 := bstep (se 1 (by rfl) ⟨3480200, by rfl⟩ : syracuseStep 4640267 = 6960401) B6960401
theorem B2608699 : Blo 1220928 2608699 := bstep (se 1 (by rfl) ⟨1956524, by rfl⟩ : syracuseStep 2608699 = 3913049) B3913049
theorem B2748023 : Blo 1220928 2748023 := bstep (se 1 (by rfl) ⟨2061017, by rfl⟩ : syracuseStep 2748023 = 4122035) B4122035
theorem B1412743 : Blo 1220928 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B1650439 : Blo 1220928 1650439 := bstep (se 1 (by rfl) ⟨1237829, by rfl⟩ : syracuseStep 1650439 = 2475659) B2475659
theorem B2748203 : Blo 1220928 2748203 := bstep (se 1 (by rfl) ⟨2061152, by rfl⟩ : syracuseStep 2748203 = 4122305) B4122305
theorem B3092377 : Blo 1220928 3092377 := bstep (se 2 (by rfl) ⟨1159641, by rfl⟩ : syracuseStep 3092377 = 2319283) B2319283
theorem B6606859 : Blo 1220928 6606859 := bstep (se 1 (by rfl) ⟨4955144, by rfl⟩ : syracuseStep 6606859 = 9910289) B9910289
theorem B7827479 : Blo 1220928 7827479 := bstep (se 1 (by rfl) ⟨5870609, by rfl⟩ : syracuseStep 7827479 = 11741219) B11741219
theorem B11300887 : Blo 1220928 11300887 := bstep (se 1 (by rfl) ⟨8475665, by rfl⟩ : syracuseStep 11300887 = 16951331) B16951331
theorem B3092539 : Blo 1220928 3092539 := bstep (se 1 (by rfl) ⟨2319404, by rfl⟩ : syracuseStep 3092539 = 4638809) B4638809
theorem B1740943 : Blo 1220928 1740943 := bstep (se 1 (by rfl) ⟨1305707, by rfl⟩ : syracuseStep 1740943 = 2611415) B2611415
theorem B2748563 : Blo 1220928 2748563 := bstep (se 1 (by rfl) ⟨2061422, by rfl⟩ : syracuseStep 2748563 = 4122845) B4122845
theorem B2748617 : Blo 1220928 2748617 := bstep (se 2 (by rfl) ⟨1030731, by rfl⟩ : syracuseStep 2748617 = 2061463) B2061463
theorem B3092681 : Blo 1220928 3092681 := bstep (se 2 (by rfl) ⟨1159755, by rfl⟩ : syracuseStep 3092681 = 2319511) B2319511
theorem B3477775 : Blo 1220928 3477775 := bstep (se 1 (by rfl) ⟨2608331, by rfl⟩ : syracuseStep 3477775 = 5216663) B5216663
theorem B6189371 : Blo 1220928 6189371 := bstep (se 1 (by rfl) ⟨4642028, by rfl⟩ : syracuseStep 6189371 = 9284057) B9284057
theorem B4125113 : Blo 1220928 4125113 := bstep (se 2 (by rfl) ⟨1546917, by rfl⟩ : syracuseStep 4125113 = 3093835) B3093835
theorem B4641209 : Blo 1220928 4641209 := bstep (se 2 (by rfl) ⟨1740453, by rfl⟩ : syracuseStep 4641209 = 3480907) B3480907
theorem B6189533 : Blo 1220928 6189533 := bstep (se 3 (by rfl) ⟨1160537, by rfl⟩ : syracuseStep 6189533 = 2321075) B2321075
theorem B1831415 : Blo 1220928 1831415 := bstep (se 1 (by rfl) ⟨1373561, by rfl⟩ : syracuseStep 1831415 = 2747123) B2747123
theorem B1651207 : Blo 1220928 1651207 := bstep (se 1 (by rfl) ⟨1238405, by rfl⟩ : syracuseStep 1651207 = 2476811) B2476811
theorem B6959627 : Blo 1220928 6959627 := bstep (se 1 (by rfl) ⟨5219720, by rfl⟩ : syracuseStep 6959627 = 10439441) B10439441
theorem B1831439 : Blo 1220928 1831439 := bstep (se 1 (by rfl) ⟨1373579, by rfl⟩ : syracuseStep 1831439 = 2747159) B2747159
theorem B2060815 : Blo 1220928 2060815 := bstep (se 1 (by rfl) ⟨1545611, by rfl⟩ : syracuseStep 2060815 = 3091223) B3091223
theorem B3478049 : Blo 1220928 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B3093025 : Blo 1220928 3093025 := bstep (se 2 (by rfl) ⟨1159884, by rfl⟩ : syracuseStep 3093025 = 2319769) B2319769
theorem B1831481 : Blo 1220928 1831481 := bstep (se 2 (by rfl) ⟨686805, by rfl⟩ : syracuseStep 1831481 = 1373611) B1373611
theorem B54317699 : Blo 1220928 54317699 := bstep (se 1 (by rfl) ⟨40738274, by rfl⟩ : syracuseStep 54317699 = 81476549) B81476549
theorem B1831559 : Blo 1220928 1831559 := bstep (se 1 (by rfl) ⟨1373669, by rfl⟩ : syracuseStep 1831559 = 2747339) B2747339
theorem B1831595 : Blo 1220928 1831595 := bstep (se 1 (by rfl) ⟨1373696, by rfl⟩ : syracuseStep 1831595 = 2747393) B2747393
theorem B1831625 : Blo 1220928 1831625 := bstep (se 2 (by rfl) ⟨686859, by rfl⟩ : syracuseStep 1831625 = 1373719) B1373719
theorem B6189857 : Blo 1220928 6189857 := bstep (se 2 (by rfl) ⟨2321196, by rfl⟩ : syracuseStep 6189857 = 4642393) B4642393
theorem B1831739 : Blo 1220928 1831739 := bstep (se 1 (by rfl) ⟨1373804, by rfl⟩ : syracuseStep 1831739 = 2747609) B2747609
theorem B1831799 : Blo 1220928 1831799 := bstep (se 1 (by rfl) ⟨1373849, by rfl⟩ : syracuseStep 1831799 = 2747699) B2747699
theorem B2749319 : Blo 1220928 2749319 := bstep (se 1 (by rfl) ⟨2061989, by rfl⟩ : syracuseStep 2749319 = 4123979) B4123979
theorem B1831823 : Blo 1220928 1831823 := bstep (se 1 (by rfl) ⟨1373867, by rfl⟩ : syracuseStep 1831823 = 2747735) B2747735
theorem B1856441 : Blo 1220928 1856441 := bstep (se 2 (by rfl) ⟨696165, by rfl⟩ : syracuseStep 1856441 = 1392331) B1392331
theorem B1831865 : Blo 1220928 1831865 := bstep (se 2 (by rfl) ⟨686949, by rfl⟩ : syracuseStep 1831865 = 1373899) B1373899
theorem B1831943 : Blo 1220928 1831943 := bstep (se 1 (by rfl) ⟨1373957, by rfl⟩ : syracuseStep 1831943 = 2747915) B2747915
theorem B4125707 : Blo 1220928 4125707 := bstep (se 1 (by rfl) ⟨3094280, by rfl⟩ : syracuseStep 4125707 = 6188561) B6188561
theorem B1831979 : Blo 1220928 1831979 := bstep (se 1 (by rfl) ⟨1373984, by rfl⟩ : syracuseStep 1831979 = 2747969) B2747969
theorem B2061355 : Blo 1220928 2061355 := bstep (se 1 (by rfl) ⟨1546016, by rfl⟩ : syracuseStep 2061355 = 3092033) B3092033
theorem B2749499 : Blo 1220928 2749499 := bstep (se 1 (by rfl) ⟨2062124, by rfl⟩ : syracuseStep 2749499 = 4124249) B4124249
theorem B1832009 : Blo 1220928 1832009 := bstep (se 2 (by rfl) ⟨687003, by rfl⟩ : syracuseStep 1832009 = 1374007) B1374007
theorem B3093623 : Blo 1220928 3093623 := bstep (se 1 (by rfl) ⟨2320217, by rfl⟩ : syracuseStep 3093623 = 4640435) B4640435
theorem B4125815 : Blo 1220928 4125815 := bstep (se 1 (by rfl) ⟨3094361, by rfl⟩ : syracuseStep 4125815 = 6188723) B6188723
theorem B2061497 : Blo 1220928 2061497 := bstep (se 2 (by rfl) ⟨773061, by rfl⟩ : syracuseStep 2061497 = 1546123) B1546123
theorem B2749625 : Blo 1220928 2749625 := bstep (se 2 (by rfl) ⟨1031109, by rfl⟩ : syracuseStep 2749625 = 2062219) B2062219
theorem B1832123 : Blo 1220928 1832123 := bstep (se 1 (by rfl) ⟨1374092, by rfl⟩ : syracuseStep 1832123 = 2748185) B2748185
theorem B6182081 : Blo 1220928 6182081 := bstep (se 2 (by rfl) ⟨2318280, by rfl⟩ : syracuseStep 6182081 = 4636561) B4636561
theorem B1832183 : Blo 1220928 1832183 := bstep (se 1 (by rfl) ⟨1374137, by rfl⟩ : syracuseStep 1832183 = 2748275) B2748275
theorem B1832207 : Blo 1220928 1832207 := bstep (se 1 (by rfl) ⟨1374155, by rfl⟩ : syracuseStep 1832207 = 2748311) B2748311
theorem B1832249 : Blo 1220928 1832249 := bstep (se 2 (by rfl) ⟨687093, by rfl⟩ : syracuseStep 1832249 = 1374187) B1374187
theorem B1373575 : Blo 1220928 1373575 := bstep (se 1 (by rfl) ⟨1030181, by rfl⟩ : syracuseStep 1373575 = 2060363) B2060363
theorem B1832327 : Blo 1220928 1832327 := bstep (se 1 (by rfl) ⟨1374245, by rfl⟩ : syracuseStep 1832327 = 2748491) B2748491
theorem B2938247 : Blo 1220928 2938247 := bstep (se 1 (by rfl) ⟨2203685, by rfl⟩ : syracuseStep 2938247 = 4407371) B4407371
theorem B1832363 : Blo 1220928 1832363 := bstep (se 1 (by rfl) ⟨1374272, by rfl⟩ : syracuseStep 1832363 = 2748545) B2748545
theorem B52868537 : Blo 1220928 52868537 := bstep (se 2 (by rfl) ⟨19825701, by rfl⟩ : syracuseStep 52868537 = 39651403) B39651403
theorem B1832393 : Blo 1220928 1832393 := bstep (se 2 (by rfl) ⟨687147, by rfl⟩ : syracuseStep 1832393 = 1374295) B1374295
theorem B3479051 : Blo 1220928 3479051 := bstep (se 1 (by rfl) ⟨2609288, by rfl⟩ : syracuseStep 3479051 = 5218577) B5218577
theorem B1545743 : Blo 1220928 1545743 := bstep (se 1 (by rfl) ⟨1159307, by rfl⟩ : syracuseStep 1545743 = 2318615) B2318615
theorem B2749967 : Blo 1220928 2749967 := bstep (se 1 (by rfl) ⟨2062475, by rfl⟩ : syracuseStep 2749967 = 4124951) B4124951
theorem B2749985 : Blo 1220928 2749985 := bstep (se 2 (by rfl) ⟨1031244, by rfl⟩ : syracuseStep 2749985 = 2062489) B2062489
theorem B1373755 : Blo 1220928 1373755 := bstep (se 1 (by rfl) ⟨1030316, by rfl⟩ : syracuseStep 1373755 = 2060633) B2060633
theorem B1832507 : Blo 1220928 1832507 := bstep (se 1 (by rfl) ⟨1374380, by rfl⟩ : syracuseStep 1832507 = 2748761) B2748761
theorem B1832567 : Blo 1220928 1832567 := bstep (se 1 (by rfl) ⟨1374425, by rfl⟩ : syracuseStep 1832567 = 2748851) B2748851
theorem B15283831 : Blo 1220928 15283831 := bstep (se 1 (by rfl) ⟨11462873, by rfl⟩ : syracuseStep 15283831 = 22925747) B22925747
theorem B1832591 : Blo 1220928 1832591 := bstep (se 1 (by rfl) ⟨1374443, by rfl⟩ : syracuseStep 1832591 = 2748887) B2748887
theorem B1832633 : Blo 1220928 1832633 := bstep (se 2 (by rfl) ⟨687237, by rfl⟩ : syracuseStep 1832633 = 1374475) B1374475
theorem B4126409 : Blo 1220928 4126409 := bstep (se 2 (by rfl) ⟨1547403, by rfl⟩ : syracuseStep 4126409 = 3094807) B3094807
theorem B6190829 : Blo 1220928 6190829 := bstep (se 3 (by rfl) ⟨1160780, by rfl⟩ : syracuseStep 6190829 = 2321561) B2321561
theorem B1832711 : Blo 1220928 1832711 := bstep (se 1 (by rfl) ⟨1374533, by rfl⟩ : syracuseStep 1832711 = 2749067) B2749067
theorem B1832747 : Blo 1220928 1832747 := bstep (se 1 (by rfl) ⟨1374560, by rfl⟩ : syracuseStep 1832747 = 2749121) B2749121
theorem B1832777 : Blo 1220928 1832777 := bstep (se 2 (by rfl) ⟨687291, by rfl⟩ : syracuseStep 1832777 = 1374583) B1374583
theorem B10434419 : Blo 1220928 10434419 := bstep (se 1 (by rfl) ⟨7825814, by rfl⟩ : syracuseStep 10434419 = 15651629) B15651629
theorem B2062199 : Blo 1220928 2062199 := bstep (se 1 (by rfl) ⟨1546649, by rfl⟩ : syracuseStep 2062199 = 3093299) B3093299
theorem B2750327 : Blo 1220928 2750327 := bstep (se 1 (by rfl) ⟨2062745, by rfl⟩ : syracuseStep 2750327 = 4125491) B4125491
theorem B2611091 : Blo 1220928 2611091 := bstep (se 1 (by rfl) ⟨1958318, by rfl⟩ : syracuseStep 2611091 = 3916637) B3916637
theorem B3479449 : Blo 1220928 3479449 := bstep (se 2 (by rfl) ⟨1304793, by rfl⟩ : syracuseStep 3479449 = 2609587) B2609587
theorem B1832891 : Blo 1220928 1832891 := bstep (se 1 (by rfl) ⟨1374668, by rfl⟩ : syracuseStep 1832891 = 2749337) B2749337
theorem B1832951 : Blo 1220928 1832951 := bstep (se 1 (by rfl) ⟨1374713, by rfl⟩ : syracuseStep 1832951 = 2749427) B2749427
theorem B1374223 : Blo 1220928 1374223 := bstep (se 1 (by rfl) ⟨1030667, by rfl⟩ : syracuseStep 1374223 = 2061335) B2061335
theorem B1832975 : Blo 1220928 1832975 := bstep (se 1 (by rfl) ⟨1374731, by rfl⟩ : syracuseStep 1832975 = 2749463) B2749463
theorem B2750507 : Blo 1220928 2750507 := bstep (se 1 (by rfl) ⟨2062880, by rfl⟩ : syracuseStep 2750507 = 4125761) B4125761
theorem B1833017 : Blo 1220928 1833017 := bstep (se 2 (by rfl) ⟨687381, by rfl⟩ : syracuseStep 1833017 = 1374763) B1374763
theorem B2513015 : Blo 1220928 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B1833095 : Blo 1220928 1833095 := bstep (se 1 (by rfl) ⟨1374821, by rfl⟩ : syracuseStep 1833095 = 2749643) B2749643
theorem B3528839 : Blo 1220928 3528839 := bstep (se 1 (by rfl) ⟨2646629, by rfl⟩ : syracuseStep 3528839 = 5293259) B5293259
theorem B3479699 : Blo 1220928 3479699 := bstep (se 1 (by rfl) ⟨2609774, by rfl⟩ : syracuseStep 3479699 = 5219549) B5219549
theorem B1833131 : Blo 1220928 1833131 := bstep (se 1 (by rfl) ⟨1374848, by rfl⟩ : syracuseStep 1833131 = 2749697) B2749697
theorem B1833161 : Blo 1220928 1833161 := bstep (se 2 (by rfl) ⟨687435, by rfl⟩ : syracuseStep 1833161 = 1374871) B1374871
theorem B1833275 : Blo 1220928 1833275 := bstep (se 1 (by rfl) ⟨1374956, by rfl⟩ : syracuseStep 1833275 = 2749913) B2749913
theorem B2062651 : Blo 1220928 2062651 := bstep (se 1 (by rfl) ⟨1546988, by rfl⟩ : syracuseStep 2062651 = 3093977) B3093977
theorem B1833335 : Blo 1220928 1833335 := bstep (se 1 (by rfl) ⟨1375001, by rfl⟩ : syracuseStep 1833335 = 2750003) B2750003
theorem B3094919 : Blo 1220928 3094919 := bstep (se 1 (by rfl) ⟨2321189, by rfl⟩ : syracuseStep 3094919 = 4642379) B4642379
theorem B4127111 : Blo 1220928 4127111 := bstep (se 1 (by rfl) ⟨3095333, by rfl⟩ : syracuseStep 4127111 = 6190667) B6190667
theorem B1833359 : Blo 1220928 1833359 := bstep (se 1 (by rfl) ⟨1375019, by rfl⟩ : syracuseStep 1833359 = 2750039) B2750039
theorem B8591761 : Blo 1220928 8591761 := bstep (se 2 (by rfl) ⟨3221910, by rfl⟩ : syracuseStep 8591761 = 6443821) B6443821
theorem B2750867 : Blo 1220928 2750867 := bstep (se 1 (by rfl) ⟨2063150, by rfl⟩ : syracuseStep 2750867 = 4126301) B4126301
theorem B1833401 : Blo 1220928 1833401 := bstep (se 2 (by rfl) ⟨687525, by rfl⟩ : syracuseStep 1833401 = 1375051) B1375051
theorem B3094969 : Blo 1220928 3094969 := bstep (se 2 (by rfl) ⟨1160613, by rfl⟩ : syracuseStep 3094969 = 2321227) B2321227
theorem B3348937 : Blo 1220928 3348937 := bstep (se 2 (by rfl) ⟨1255851, by rfl⟩ : syracuseStep 3348937 = 2511703) B2511703
theorem B2062793 : Blo 1220928 2062793 := bstep (se 2 (by rfl) ⟨773547, by rfl⟩ : syracuseStep 2062793 = 1547095) B1547095
theorem B2750921 : Blo 1220928 2750921 := bstep (se 2 (by rfl) ⟨1031595, by rfl⟩ : syracuseStep 2750921 = 2063191) B2063191
theorem B6183377 : Blo 1220928 6183377 := bstep (se 2 (by rfl) ⟨2318766, by rfl⟩ : syracuseStep 6183377 = 4637533) B4637533
theorem B1374727 : Blo 1220928 1374727 := bstep (se 1 (by rfl) ⟨1031045, by rfl⟩ : syracuseStep 1374727 = 2062091) B2062091
theorem B1833479 : Blo 1220928 1833479 := bstep (se 1 (by rfl) ⟨1375109, by rfl⟩ : syracuseStep 1833479 = 2750219) B2750219
theorem B4700683 : Blo 1220928 4700683 := bstep (se 1 (by rfl) ⟨3525512, by rfl⟩ : syracuseStep 4700683 = 7051025) B7051025
theorem B7428631 : Blo 1220928 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B1833515 : Blo 1220928 1833515 := bstep (se 1 (by rfl) ⟨1375136, by rfl⟩ : syracuseStep 1833515 = 2750273) B2750273
theorem B1833545 : Blo 1220928 1833545 := bstep (se 2 (by rfl) ⟨687579, by rfl⟩ : syracuseStep 1833545 = 1375159) B1375159
theorem B5872301 : Blo 1220928 5872301 := bstep (se 3 (by rfl) ⟨1101056, by rfl⟩ : syracuseStep 5872301 = 2202113) B2202113
theorem B1374907 : Blo 1220928 1374907 := bstep (se 1 (by rfl) ⟨1031180, by rfl⟩ : syracuseStep 1374907 = 2062361) B2062361
theorem B1833659 : Blo 1220928 1833659 := bstep (se 1 (by rfl) ⟨1375244, by rfl⟩ : syracuseStep 1833659 = 2750489) B2750489
theorem B6601409 : Blo 1220928 6601409 := bstep (se 2 (by rfl) ⟨2475528, by rfl⟩ : syracuseStep 6601409 = 4951057) B4951057
theorem B1833719 : Blo 1220928 1833719 := bstep (se 1 (by rfl) ⟨1375289, by rfl⟩ : syracuseStep 1833719 = 2750579) B2750579
theorem B1833743 : Blo 1220928 1833743 := bstep (se 1 (by rfl) ⟨1375307, by rfl⟩ : syracuseStep 1833743 = 2750615) B2750615
theorem B1833785 : Blo 1220928 1833785 := bstep (se 2 (by rfl) ⟨687669, by rfl⟩ : syracuseStep 1833785 = 1375339) B1375339
theorem B3718003 : Blo 1220928 3718003 := bstep (se 1 (by rfl) ⟨2788502, by rfl⟩ : syracuseStep 3718003 = 5577005) B5577005
theorem B1833863 : Blo 1220928 1833863 := bstep (se 1 (by rfl) ⟨1375397, by rfl⟩ : syracuseStep 1833863 = 2750795) B2750795
theorem B1833899 : Blo 1220928 1833899 := bstep (se 1 (by rfl) ⟨1375424, by rfl⟩ : syracuseStep 1833899 = 2750849) B2750849
theorem B1956793 : Blo 1220928 1956793 := bstep (se 2 (by rfl) ⟨733797, by rfl⟩ : syracuseStep 1956793 = 1467595) B1467595
theorem B1833929 : Blo 1220928 1833929 := bstep (se 2 (by rfl) ⟨687723, by rfl⟩ : syracuseStep 1833929 = 1375447) B1375447
theorem B1834043 : Blo 1220928 1834043 := bstep (se 1 (by rfl) ⟨1375532, by rfl⟩ : syracuseStep 1834043 = 2751065) B2751065
theorem B14851133 : Blo 1220928 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B3480691 : Blo 1220928 3480691 := bstep (se 1 (by rfl) ⟨2610518, by rfl⟩ : syracuseStep 3480691 = 5221037) B5221037
theorem B13220981 : Blo 1220928 13220981 := bstep (se 5 (by rfl) ⟨619733, by rfl⟩ : syracuseStep 13220981 = 1239467) B1239467
theorem B1834103 : Blo 1220928 1834103 := bstep (se 1 (by rfl) ⟨1375577, by rfl⟩ : syracuseStep 1834103 = 2751155) B2751155
theorem B2063495 : Blo 1220928 2063495 := bstep (se 1 (by rfl) ⟨1547621, by rfl⟩ : syracuseStep 2063495 = 3095243) B3095243
theorem B1375375 : Blo 1220928 1375375 := bstep (se 1 (by rfl) ⟨1031531, by rfl⟩ : syracuseStep 1375375 = 2063063) B2063063
theorem B1834127 : Blo 1220928 1834127 := bstep (se 1 (by rfl) ⟨1375595, by rfl⟩ : syracuseStep 1834127 = 2751191) B2751191
theorem B1834169 : Blo 1220928 1834169 := bstep (se 2 (by rfl) ⟨687813, by rfl⟩ : syracuseStep 1834169 = 1375627) B1375627
theorem B1834247 : Blo 1220928 1834247 := bstep (se 1 (by rfl) ⟨1375685, by rfl⟩ : syracuseStep 1834247 = 2751371) B2751371
theorem B1834283 : Blo 1220928 1834283 := bstep (se 1 (by rfl) ⟨1375712, by rfl⟩ : syracuseStep 1834283 = 2751425) B2751425
theorem B1834313 : Blo 1220928 1834313 := bstep (se 2 (by rfl) ⟨687867, by rfl⟩ : syracuseStep 1834313 = 1375735) B1375735
theorem B4406795 : Blo 1220928 4406795 := bstep (se 1 (by rfl) ⟨3305096, by rfl⟩ : syracuseStep 4406795 = 6610193) B6610193
theorem B16080413 : Blo 1220928 16080413 := bstep (se 3 (by rfl) ⟨3015077, by rfl⟩ : syracuseStep 16080413 = 6030155) B6030155
theorem B2350711 : Blo 1220928 2350711 := bstep (se 1 (by rfl) ⟨1763033, by rfl⟩ : syracuseStep 2350711 = 3526067) B3526067
theorem B6962861 : Blo 1220928 6962861 := bstep (se 3 (by rfl) ⟨1305536, by rfl⟩ : syracuseStep 6962861 = 2611073) B2611073
theorem B3301181 : Blo 1220928 3301181 := bstep (se 3 (by rfl) ⟨618971, by rfl⟩ : syracuseStep 3301181 = 1237943) B1237943
theorem B18808645 : Blo 1220928 18808645 := bstep (se 4 (by rfl) ⟨1763310, by rfl⟩ : syracuseStep 18808645 = 3526621) B3526621
theorem B13918067 : Blo 1220928 13918067 := bstep (se 1 (by rfl) ⟨10438550, by rfl⟩ : syracuseStep 13918067 = 20877101) B20877101
theorem B5218319 : Blo 1220928 5218319 := bstep (se 1 (by rfl) ⟨3913739, by rfl⟩ : syracuseStep 5218319 = 7827479) B7827479
theorem B5292047 : Blo 1220928 5292047 := bstep (se 1 (by rfl) ⟨3969035, by rfl⟩ : syracuseStep 5292047 = 7938071) B7938071
theorem B13205585 : Blo 1220928 13205585 := bstep (se 2 (by rfl) ⟨4952094, by rfl⟩ : syracuseStep 13205585 = 9904189) B9904189
theorem B171524405 : Blo 1220928 171524405 := bstep (se 5 (by rfl) ⟨8040206, by rfl⟩ : syracuseStep 171524405 = 16080413) B16080413
theorem B26435909 : Blo 1220928 26435909 := bstep (se 4 (by rfl) ⟨2478366, by rfl⟩ : syracuseStep 26435909 = 4956733) B4956733
theorem B1220943 : Blo 1220928 1220943 := bstep (se 1 (by rfl) ⟨915707, by rfl⟩ : syracuseStep 1220943 = 1831415) B1831415
theorem B1220959 : Blo 1220928 1220959 := bstep (se 1 (by rfl) ⟨915719, by rfl⟩ : syracuseStep 1220959 = 1831439) B1831439
theorem B4637033 : Blo 1220928 4637033 := bstep (se 2 (by rfl) ⟨1738887, by rfl⟩ : syracuseStep 4637033 = 3477775) B3477775
theorem B6185321 : Blo 1220928 6185321 := bstep (se 2 (by rfl) ⟨2319495, by rfl⟩ : syracuseStep 6185321 = 4638991) B4638991
theorem B2318699 : Blo 1220928 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B1220987 : Blo 1220928 1220987 := bstep (se 1 (by rfl) ⟨915740, by rfl⟩ : syracuseStep 1220987 = 1831481) B1831481
theorem B1221039 : Blo 1220928 1221039 := bstep (se 1 (by rfl) ⟨915779, by rfl⟩ : syracuseStep 1221039 = 1831559) B1831559
theorem B1221063 : Blo 1220928 1221063 := bstep (se 1 (by rfl) ⟨915797, by rfl⟩ : syracuseStep 1221063 = 1831595) B1831595
theorem B1221083 : Blo 1220928 1221083 := bstep (se 1 (by rfl) ⟨915812, by rfl⟩ : syracuseStep 1221083 = 1831625) B1831625
theorem B1221159 : Blo 1220928 1221159 := bstep (se 1 (by rfl) ⟨915869, by rfl⟩ : syracuseStep 1221159 = 1831739) B1831739
theorem B1221199 : Blo 1220928 1221199 := bstep (se 1 (by rfl) ⟨915899, by rfl⟩ : syracuseStep 1221199 = 1831799) B1831799
theorem B1221215 : Blo 1220928 1221215 := bstep (se 1 (by rfl) ⟨915911, by rfl⟩ : syracuseStep 1221215 = 1831823) B1831823
theorem B4465249 : Blo 1220928 4465249 := bstep (se 2 (by rfl) ⟨1674468, by rfl⟩ : syracuseStep 4465249 = 3348937) B3348937
theorem B1237627 : Blo 1220928 1237627 := bstep (se 1 (by rfl) ⟨928220, by rfl⟩ : syracuseStep 1237627 = 1856441) B1856441
theorem B1221243 : Blo 1220928 1221243 := bstep (se 1 (by rfl) ⟨915932, by rfl⟩ : syracuseStep 1221243 = 1831865) B1831865
theorem B7930541 : Blo 1220928 7930541 := bstep (se 3 (by rfl) ⟨1486976, by rfl⟩ : syracuseStep 7930541 = 2973953) B2973953
theorem B1221295 : Blo 1220928 1221295 := bstep (se 1 (by rfl) ⟨915971, by rfl⟩ : syracuseStep 1221295 = 1831943) B1831943
theorem B1221319 : Blo 1220928 1221319 := bstep (se 1 (by rfl) ⟨915989, by rfl⟩ : syracuseStep 1221319 = 1831979) B1831979
theorem B9904841 : Blo 1220928 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B1221339 : Blo 1220928 1221339 := bstep (se 1 (by rfl) ⟨916004, by rfl⟩ : syracuseStep 1221339 = 1832009) B1832009
theorem B1221415 : Blo 1220928 1221415 := bstep (se 1 (by rfl) ⟨916061, by rfl⟩ : syracuseStep 1221415 = 1832123) B1832123
theorem B4121387 : Blo 1220928 4121387 := bstep (se 1 (by rfl) ⟨3091040, by rfl⟩ : syracuseStep 4121387 = 6182081) B6182081
theorem B1221455 : Blo 1220928 1221455 := bstep (se 1 (by rfl) ⟨916091, by rfl⟩ : syracuseStep 1221455 = 1832183) B1832183
theorem B1221471 : Blo 1220928 1221471 := bstep (se 1 (by rfl) ⟨916103, by rfl⟩ : syracuseStep 1221471 = 1832207) B1832207
theorem B1221499 : Blo 1220928 1221499 := bstep (se 1 (by rfl) ⟨916124, by rfl⟩ : syracuseStep 1221499 = 1832249) B1832249
theorem B1221551 : Blo 1220928 1221551 := bstep (se 1 (by rfl) ⟨916163, by rfl⟩ : syracuseStep 1221551 = 1832327) B1832327
theorem B1958831 : Blo 1220928 1958831 := bstep (se 1 (by rfl) ⟨1469123, by rfl⟩ : syracuseStep 1958831 = 2938247) B2938247
theorem B1221575 : Blo 1220928 1221575 := bstep (se 1 (by rfl) ⟨916181, by rfl⟩ : syracuseStep 1221575 = 1832363) B1832363
theorem B1221595 : Blo 1220928 1221595 := bstep (se 1 (by rfl) ⟨916196, by rfl⟩ : syracuseStep 1221595 = 1832393) B1832393
theorem B2933767 : Blo 1220928 2933767 := bstep (se 1 (by rfl) ⟨2200325, by rfl⟩ : syracuseStep 2933767 = 4400651) B4400651
theorem B2319367 : Blo 1220928 2319367 := bstep (se 1 (by rfl) ⟨1739525, by rfl⟩ : syracuseStep 2319367 = 3479051) B3479051
theorem B1221671 : Blo 1220928 1221671 := bstep (se 1 (by rfl) ⟨916253, by rfl⟩ : syracuseStep 1221671 = 1832507) B1832507
theorem B4121657 : Blo 1220928 4121657 := bstep (se 2 (by rfl) ⟨1545621, by rfl⟩ : syracuseStep 4121657 = 3091243) B3091243
theorem B1221711 : Blo 1220928 1221711 := bstep (se 1 (by rfl) ⟨916283, by rfl⟩ : syracuseStep 1221711 = 1832567) B1832567
theorem B1221727 : Blo 1220928 1221727 := bstep (se 1 (by rfl) ⟨916295, by rfl⟩ : syracuseStep 1221727 = 1832591) B1832591
theorem B1221755 : Blo 1220928 1221755 := bstep (se 1 (by rfl) ⟨916316, by rfl⟩ : syracuseStep 1221755 = 1832633) B1832633
theorem B4957337 : Blo 1220928 4957337 := bstep (se 2 (by rfl) ⟨1859001, by rfl⟩ : syracuseStep 4957337 = 3718003) B3718003
theorem B1221807 : Blo 1220928 1221807 := bstep (se 1 (by rfl) ⟨916355, by rfl⟩ : syracuseStep 1221807 = 1832711) B1832711
theorem B1221831 : Blo 1220928 1221831 := bstep (se 1 (by rfl) ⟨916373, by rfl⟩ : syracuseStep 1221831 = 1832747) B1832747
theorem B1221851 : Blo 1220928 1221851 := bstep (se 1 (by rfl) ⟨916388, by rfl⟩ : syracuseStep 1221851 = 1832777) B1832777
theorem B6956279 : Blo 1220928 6956279 := bstep (se 1 (by rfl) ⟨5217209, by rfl⟩ : syracuseStep 6956279 = 10434419) B10434419
theorem B1221927 : Blo 1220928 1221927 := bstep (se 1 (by rfl) ⟨916445, by rfl⟩ : syracuseStep 1221927 = 1832891) B1832891
theorem B1221967 : Blo 1220928 1221967 := bstep (se 1 (by rfl) ⟨916475, by rfl⟩ : syracuseStep 1221967 = 1832951) B1832951
theorem B1221983 : Blo 1220928 1221983 := bstep (se 1 (by rfl) ⟨916487, by rfl⟩ : syracuseStep 1221983 = 1832975) B1832975
theorem B1222011 : Blo 1220928 1222011 := bstep (se 1 (by rfl) ⟨916508, by rfl⟩ : syracuseStep 1222011 = 1833017) B1833017
theorem B4121981 : Blo 1220928 4121981 := bstep (se 3 (by rfl) ⟨772871, by rfl⟩ : syracuseStep 4121981 = 1545743) B1545743
theorem B1222063 : Blo 1220928 1222063 := bstep (se 1 (by rfl) ⟨916547, by rfl⟩ : syracuseStep 1222063 = 1833095) B1833095
theorem B2352559 : Blo 1220928 2352559 := bstep (se 1 (by rfl) ⟨1764419, by rfl⟩ : syracuseStep 2352559 = 3528839) B3528839
theorem B1222087 : Blo 1220928 1222087 := bstep (se 1 (by rfl) ⟨916565, by rfl⟩ : syracuseStep 1222087 = 1833131) B1833131
theorem B1222107 : Blo 1220928 1222107 := bstep (se 1 (by rfl) ⟨916580, by rfl⟩ : syracuseStep 1222107 = 1833161) B1833161
theorem B1222183 : Blo 1220928 1222183 := bstep (se 1 (by rfl) ⟨916637, by rfl⟩ : syracuseStep 1222183 = 1833275) B1833275
theorem B6964775 : Blo 1220928 6964775 := bstep (se 1 (by rfl) ⟨5223581, by rfl⟩ : syracuseStep 6964775 = 10447163) B10447163
theorem B1222223 : Blo 1220928 1222223 := bstep (se 1 (by rfl) ⟨916667, by rfl⟩ : syracuseStep 1222223 = 1833335) B1833335
theorem B1222239 : Blo 1220928 1222239 := bstep (se 1 (by rfl) ⟨916679, by rfl⟩ : syracuseStep 1222239 = 1833359) B1833359
theorem B1222267 : Blo 1220928 1222267 := bstep (se 1 (by rfl) ⟨916700, by rfl⟩ : syracuseStep 1222267 = 1833401) B1833401
theorem B4122251 : Blo 1220928 4122251 := bstep (se 1 (by rfl) ⟨3091688, by rfl⟩ : syracuseStep 4122251 = 6183377) B6183377
theorem B1222319 : Blo 1220928 1222319 := bstep (se 1 (by rfl) ⟨916739, by rfl⟩ : syracuseStep 1222319 = 1833479) B1833479
theorem B1222343 : Blo 1220928 1222343 := bstep (se 1 (by rfl) ⟨916757, by rfl⟩ : syracuseStep 1222343 = 1833515) B1833515
theorem B1222363 : Blo 1220928 1222363 := bstep (se 1 (by rfl) ⟨916772, by rfl⟩ : syracuseStep 1222363 = 1833545) B1833545
theorem B1222439 : Blo 1220928 1222439 := bstep (se 1 (by rfl) ⟨916829, by rfl⟩ : syracuseStep 1222439 = 1833659) B1833659
theorem B4400939 : Blo 1220928 4400939 := bstep (se 1 (by rfl) ⟨3300704, by rfl⟩ : syracuseStep 4400939 = 6601409) B6601409
theorem B1222479 : Blo 1220928 1222479 := bstep (se 1 (by rfl) ⟨916859, by rfl⟩ : syracuseStep 1222479 = 1833719) B1833719
theorem B1222495 : Blo 1220928 1222495 := bstep (se 1 (by rfl) ⟨916871, by rfl⟩ : syracuseStep 1222495 = 1833743) B1833743
theorem B1222523 : Blo 1220928 1222523 := bstep (se 1 (by rfl) ⟨916892, by rfl⟩ : syracuseStep 1222523 = 1833785) B1833785
theorem B1222575 : Blo 1220928 1222575 := bstep (se 1 (by rfl) ⟨916931, by rfl⟩ : syracuseStep 1222575 = 1833863) B1833863
theorem B1222599 : Blo 1220928 1222599 := bstep (se 1 (by rfl) ⟨916949, by rfl⟩ : syracuseStep 1222599 = 1833899) B1833899
theorem B1222619 : Blo 1220928 1222619 := bstep (se 1 (by rfl) ⟨916964, by rfl⟩ : syracuseStep 1222619 = 1833929) B1833929
theorem B33458183 : Blo 1220928 33458183 := bstep (se 1 (by rfl) ⟨25093637, by rfl⟩ : syracuseStep 33458183 = 50187275) B50187275
theorem B1222695 : Blo 1220928 1222695 := bstep (se 1 (by rfl) ⟨917021, by rfl⟩ : syracuseStep 1222695 = 1834043) B1834043
theorem B1222735 : Blo 1220928 1222735 := bstep (se 1 (by rfl) ⟨917051, by rfl⟩ : syracuseStep 1222735 = 1834103) B1834103
theorem B1222751 : Blo 1220928 1222751 := bstep (se 1 (by rfl) ⟨917063, by rfl⟩ : syracuseStep 1222751 = 1834127) B1834127
theorem B1222779 : Blo 1220928 1222779 := bstep (se 1 (by rfl) ⟨917084, by rfl⟩ : syracuseStep 1222779 = 1834169) B1834169
theorem B1222831 : Blo 1220928 1222831 := bstep (se 1 (by rfl) ⟨917123, by rfl⟩ : syracuseStep 1222831 = 1834247) B1834247
theorem B1222855 : Blo 1220928 1222855 := bstep (se 1 (by rfl) ⟨917141, by rfl⟩ : syracuseStep 1222855 = 1834283) B1834283
theorem B1222875 : Blo 1220928 1222875 := bstep (se 1 (by rfl) ⟨917156, by rfl⟩ : syracuseStep 1222875 = 1834313) B1834313
theorem B25078193 : Blo 1220928 25078193 := bstep (se 2 (by rfl) ⟨9404322, by rfl⟩ : syracuseStep 25078193 = 18808645) B18808645
theorem B4123169 : Blo 1220928 4123169 := bstep (se 2 (by rfl) ⟨1546188, by rfl⟩ : syracuseStep 4123169 = 3092377) B3092377
theorem B4639265 : Blo 1220928 4639265 := bstep (se 2 (by rfl) ⟨1739724, by rfl⟩ : syracuseStep 4639265 = 3479449) B3479449
theorem B8809145 : Blo 1220928 8809145 := bstep (se 2 (by rfl) ⟨3303429, by rfl⟩ : syracuseStep 8809145 = 6606859) B6606859
theorem B25070309 : Blo 1220928 25070309 := bstep (se 4 (by rfl) ⟨2350341, by rfl⟩ : syracuseStep 25070309 = 4700683) B4700683
theorem B3091193 : Blo 1220928 3091193 := bstep (se 2 (by rfl) ⟨1159197, by rfl⟩ : syracuseStep 3091193 = 2318395) B2318395
theorem B4123385 : Blo 1220928 4123385 := bstep (se 2 (by rfl) ⟨1546269, by rfl⟩ : syracuseStep 4123385 = 3092539) B3092539
theorem B60271397 : Blo 1220928 60271397 := bstep (se 4 (by rfl) ⟨5650443, by rfl⟩ : syracuseStep 60271397 = 11300887) B11300887
theorem B2747231 : Blo 1220928 2747231 := bstep (se 1 (by rfl) ⟨2060423, by rfl⟩ : syracuseStep 2747231 = 4120847) B4120847
theorem B85765027 : Blo 1220928 85765027 := bstep (se 1 (by rfl) ⟨64323770, by rfl⟩ : syracuseStep 85765027 = 128647541) B128647541
theorem B4123655 : Blo 1220928 4123655 := bstep (se 1 (by rfl) ⟨3092741, by rfl⟩ : syracuseStep 4123655 = 6185483) B6185483
theorem B4639751 : Blo 1220928 4639751 := bstep (se 1 (by rfl) ⟨3479813, by rfl⟩ : syracuseStep 4639751 = 6959627) B6959627
theorem B2747411 : Blo 1220928 2747411 := bstep (se 1 (by rfl) ⟨2060558, by rfl⟩ : syracuseStep 2747411 = 4121117) B4121117
theorem B36211799 : Blo 1220928 36211799 := bstep (se 1 (by rfl) ⟨27158849, by rfl⟩ : syracuseStep 36211799 = 54317699) B54317699
theorem B4123763 : Blo 1220928 4123763 := bstep (se 1 (by rfl) ⟨3092822, by rfl⟩ : syracuseStep 4123763 = 6185645) B6185645
theorem B2321531 : Blo 1220928 2321531 := bstep (se 1 (by rfl) ⟨1741148, by rfl⟩ : syracuseStep 2321531 = 3482297) B3482297
theorem B11455681 : Blo 1220928 11455681 := bstep (se 2 (by rfl) ⟨4295880, by rfl⟩ : syracuseStep 11455681 = 8591761) B8591761
theorem B12537125 : Blo 1220928 12537125 := bstep (se 4 (by rfl) ⟨1175355, by rfl⟩ : syracuseStep 12537125 = 2350711) B2350711
theorem B2747753 : Blo 1220928 2747753 := bstep (se 2 (by rfl) ⟨1030407, by rfl⟩ : syracuseStep 2747753 = 2060815) B2060815
theorem B3091841 : Blo 1220928 3091841 := bstep (se 2 (by rfl) ⟨1159440, by rfl⟩ : syracuseStep 3091841 = 2318881) B2318881
theorem B4124033 : Blo 1220928 4124033 := bstep (se 2 (by rfl) ⟨1546512, by rfl⟩ : syracuseStep 4124033 = 3093025) B3093025
theorem B9285029 : Blo 1220928 9285029 := bstep (se 4 (by rfl) ⟨870471, by rfl⟩ : syracuseStep 9285029 = 1740943) B1740943
theorem B4640237 : Blo 1220928 4640237 := bstep (se 3 (by rfl) ⟨870044, by rfl⟩ : syracuseStep 4640237 = 1740089) B1740089
theorem B35245691 : Blo 1220928 35245691 := bstep (se 1 (by rfl) ⟨26434268, by rfl⟩ : syracuseStep 35245691 = 52868537) B52868537
theorem B7941755 : Blo 1220928 7941755 := bstep (se 1 (by rfl) ⟨5956316, by rfl⟩ : syracuseStep 7941755 = 11912633) B11912633
theorem B6958943 : Blo 1220928 6958943 := bstep (se 1 (by rfl) ⟨5219207, by rfl⟩ : syracuseStep 6958943 = 10438415) B10438415
theorem B2609057 : Blo 1220928 2609057 := bstep (se 2 (by rfl) ⟨978396, by rfl⟩ : syracuseStep 2609057 = 1956793) B1956793
theorem B4403105 : Blo 1220928 4403105 := bstep (se 2 (by rfl) ⟨1651164, by rfl⟩ : syracuseStep 4403105 = 3302329) B3302329
theorem B1740727 : Blo 1220928 1740727 := bstep (se 1 (by rfl) ⟨1305545, by rfl⟩ : syracuseStep 1740727 = 2611091) B2611091
theorem B2748347 : Blo 1220928 2748347 := bstep (se 1 (by rfl) ⟨2061260, by rfl⟩ : syracuseStep 2748347 = 4122521) B4122521
theorem B8802341 : Blo 1220928 8802341 := bstep (se 4 (by rfl) ⟨825219, by rfl⟩ : syracuseStep 8802341 = 1650439) B1650439
theorem B2748473 : Blo 1220928 2748473 := bstep (se 2 (by rfl) ⟨1030677, by rfl⟩ : syracuseStep 2748473 = 2061355) B2061355
theorem B1675343 : Blo 1220928 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B4640921 : Blo 1220928 4640921 := bstep (se 2 (by rfl) ⟨1740345, by rfl⟩ : syracuseStep 4640921 = 3480691) B3480691
theorem B3092651 : Blo 1220928 3092651 := bstep (se 1 (by rfl) ⟨2319488, by rfl⟩ : syracuseStep 3092651 = 4638977) B4638977
theorem B4124843 : Blo 1220928 4124843 := bstep (se 1 (by rfl) ⟨3093632, by rfl⟩ : syracuseStep 4124843 = 6187265) B6187265
theorem B1650937 : Blo 1220928 1650937 := bstep (se 2 (by rfl) ⟨619101, by rfl⟩ : syracuseStep 1650937 = 1238203) B1238203
theorem B25063739 : Blo 1220928 25063739 := bstep (se 1 (by rfl) ⟨18797804, by rfl⟩ : syracuseStep 25063739 = 37595609) B37595609
theorem B2060687 : Blo 1220928 2060687 := bstep (se 1 (by rfl) ⟨1545515, by rfl⟩ : syracuseStep 2060687 = 3091031) B3091031
theorem B2748815 : Blo 1220928 2748815 := bstep (se 1 (by rfl) ⟨2061611, by rfl⟩ : syracuseStep 2748815 = 4123223) B4123223
theorem B1831433 : Blo 1220928 1831433 := bstep (se 2 (by rfl) ⟨686787, by rfl⟩ : syracuseStep 1831433 = 1373575) B1373575
theorem B3576329 : Blo 1220928 3576329 := bstep (se 2 (by rfl) ⟨1341123, by rfl⟩ : syracuseStep 3576329 = 2682247) B2682247
theorem B1831463 : Blo 1220928 1831463 := bstep (se 1 (by rfl) ⟨1373597, by rfl⟩ : syracuseStep 1831463 = 2747195) B2747195
theorem B10433083 : Blo 1220928 10433083 := bstep (se 1 (by rfl) ⟨7824812, by rfl⟩ : syracuseStep 10433083 = 15649625) B15649625
theorem B1831547 : Blo 1220928 1831547 := bstep (se 1 (by rfl) ⟨1373660, by rfl⟩ : syracuseStep 1831547 = 2747321) B2747321
theorem B2060923 : Blo 1220928 2060923 := bstep (se 1 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 2060923 = 3091385) B3091385
theorem B4125383 : Blo 1220928 4125383 := bstep (se 1 (by rfl) ⟨3094037, by rfl⟩ : syracuseStep 4125383 = 6188075) B6188075
theorem B9900755 : Blo 1220928 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B2749139 : Blo 1220928 2749139 := bstep (se 1 (by rfl) ⟨2061854, by rfl⟩ : syracuseStep 2749139 = 4123709) B4123709
theorem B1831673 : Blo 1220928 1831673 := bstep (se 2 (by rfl) ⟨686877, by rfl⟩ : syracuseStep 1831673 = 1373755) B1373755
theorem B3478265 : Blo 1220928 3478265 := bstep (se 2 (by rfl) ⟨1304349, by rfl⟩ : syracuseStep 3478265 = 2608699) B2608699
theorem B6959945 : Blo 1220928 6959945 := bstep (se 2 (by rfl) ⟨2609979, by rfl⟩ : syracuseStep 6959945 = 5219959) B5219959
theorem B20378441 : Blo 1220928 20378441 := bstep (se 2 (by rfl) ⟨7641915, by rfl⟩ : syracuseStep 20378441 = 15283831) B15283831
theorem B1831775 : Blo 1220928 1831775 := bstep (se 1 (by rfl) ⟨1373831, by rfl⟩ : syracuseStep 1831775 = 2747663) B2747663
theorem B1831787 : Blo 1220928 1831787 := bstep (se 1 (by rfl) ⟨1373840, by rfl⟩ : syracuseStep 1831787 = 2747681) B2747681
theorem B5223275 : Blo 1220928 5223275 := bstep (se 1 (by rfl) ⟨3917456, by rfl⟩ : syracuseStep 5223275 = 7834913) B7834913
theorem B3093511 : Blo 1220928 3093511 := bstep (se 1 (by rfl) ⟨2320133, by rfl⟩ : syracuseStep 3093511 = 4640267) B4640267
theorem B2937863 : Blo 1220928 2937863 := bstep (se 1 (by rfl) ⟨2203397, by rfl⟩ : syracuseStep 2937863 = 4406795) B4406795
theorem B1832015 : Blo 1220928 1832015 := bstep (se 1 (by rfl) ⟨1374011, by rfl⟩ : syracuseStep 1832015 = 2748023) B2748023
theorem B4641907 : Blo 1220928 4641907 := bstep (se 1 (by rfl) ⟨3481430, by rfl⟩ : syracuseStep 4641907 = 6962861) B6962861
theorem B1832135 : Blo 1220928 1832135 := bstep (se 1 (by rfl) ⟨1374101, by rfl⟩ : syracuseStep 1832135 = 2748203) B2748203
theorem B2200787 : Blo 1220928 2200787 := bstep (se 1 (by rfl) ⟨1650590, by rfl⟩ : syracuseStep 2200787 = 3301181) B3301181
theorem B9278711 : Blo 1220928 9278711 := bstep (se 1 (by rfl) ⟨6959033, by rfl⟩ : syracuseStep 9278711 = 13918067) B13918067
theorem B1832297 : Blo 1220928 1832297 := bstep (se 2 (by rfl) ⟨687111, by rfl⟩ : syracuseStep 1832297 = 1374223) B1374223
theorem B54285713 : Blo 1220928 54285713 := bstep (se 2 (by rfl) ⟨20357142, by rfl⟩ : syracuseStep 54285713 = 40714285) B40714285
theorem B29726099 : Blo 1220928 29726099 := bstep (se 1 (by rfl) ⟨22294574, by rfl⟩ : syracuseStep 29726099 = 44589149) B44589149
theorem B1832375 : Blo 1220928 1832375 := bstep (se 1 (by rfl) ⟨1374281, by rfl⟩ : syracuseStep 1832375 = 2748563) B2748563
theorem B1832411 : Blo 1220928 1832411 := bstep (se 1 (by rfl) ⟨1374308, by rfl⟩ : syracuseStep 1832411 = 2748617) B2748617
theorem B2061787 : Blo 1220928 2061787 := bstep (se 1 (by rfl) ⟨1546340, by rfl⟩ : syracuseStep 2061787 = 3092681) B3092681
theorem B4126247 : Blo 1220928 4126247 := bstep (se 1 (by rfl) ⟨3094685, by rfl⟩ : syracuseStep 4126247 = 6189371) B6189371
theorem B2750075 : Blo 1220928 2750075 := bstep (se 1 (by rfl) ⟨2062556, by rfl⟩ : syracuseStep 2750075 = 4125113) B4125113
theorem B3094139 : Blo 1220928 3094139 := bstep (se 1 (by rfl) ⟨2320604, by rfl⟩ : syracuseStep 3094139 = 4641209) B4641209
theorem B4126355 : Blo 1220928 4126355 := bstep (se 1 (by rfl) ⟨3094766, by rfl⟩ : syracuseStep 4126355 = 6189533) B6189533
theorem B9279197 : Blo 1220928 9279197 := bstep (se 3 (by rfl) ⟨1739849, by rfl⟩ : syracuseStep 9279197 = 3479699) B3479699
theorem B15652601 : Blo 1220928 15652601 := bstep (se 2 (by rfl) ⟨5869725, by rfl⟩ : syracuseStep 15652601 = 11739451) B11739451
theorem B2750201 : Blo 1220928 2750201 := bstep (se 2 (by rfl) ⟨1031325, by rfl⟩ : syracuseStep 2750201 = 2062651) B2062651
theorem B4126571 : Blo 1220928 4126571 := bstep (se 1 (by rfl) ⟨3094928, by rfl⟩ : syracuseStep 4126571 = 6189857) B6189857
theorem B4642667 : Blo 1220928 4642667 := bstep (se 1 (by rfl) ⟨3482000, by rfl⟩ : syracuseStep 4642667 = 6964001) B6964001
theorem B3094433 : Blo 1220928 3094433 := bstep (se 2 (by rfl) ⟨1160412, by rfl⟩ : syracuseStep 3094433 = 2320825) B2320825
theorem B4126625 : Blo 1220928 4126625 := bstep (se 2 (by rfl) ⟨1547484, by rfl⟩ : syracuseStep 4126625 = 3094969) B3094969
theorem B1832879 : Blo 1220928 1832879 := bstep (se 1 (by rfl) ⟨1374659, by rfl⟩ : syracuseStep 1832879 = 2749319) B2749319
theorem B2750471 : Blo 1220928 2750471 := bstep (se 1 (by rfl) ⟨2062853, by rfl⟩ : syracuseStep 2750471 = 4125707) B4125707
theorem B2201609 : Blo 1220928 2201609 := bstep (se 2 (by rfl) ⟨825603, by rfl⟩ : syracuseStep 2201609 = 1651207) B1651207
theorem B1832969 : Blo 1220928 1832969 := bstep (se 2 (by rfl) ⟨687363, by rfl⟩ : syracuseStep 1832969 = 1374727) B1374727
theorem B10442789 : Blo 1220928 10442789 := bstep (se 4 (by rfl) ⟨979011, by rfl⟩ : syracuseStep 10442789 = 1958023) B1958023
theorem B1832999 : Blo 1220928 1832999 := bstep (se 1 (by rfl) ⟨1374749, by rfl⟩ : syracuseStep 1832999 = 2749499) B2749499
theorem B2062415 : Blo 1220928 2062415 := bstep (se 1 (by rfl) ⟨1546811, by rfl⟩ : syracuseStep 2062415 = 3093623) B3093623
theorem B2750543 : Blo 1220928 2750543 := bstep (se 1 (by rfl) ⟨2062907, by rfl⟩ : syracuseStep 2750543 = 4125815) B4125815
theorem B1374331 : Blo 1220928 1374331 := bstep (se 1 (by rfl) ⟨1030748, by rfl⟩ : syracuseStep 1374331 = 2061497) B2061497
theorem B1833083 : Blo 1220928 1833083 := bstep (se 1 (by rfl) ⟨1374812, by rfl⟩ : syracuseStep 1833083 = 2749625) B2749625
theorem B3479723 : Blo 1220928 3479723 := bstep (se 1 (by rfl) ⟨2609792, by rfl⟩ : syracuseStep 3479723 = 5219585) B5219585
theorem B1833209 : Blo 1220928 1833209 := bstep (se 2 (by rfl) ⟨687453, by rfl⟩ : syracuseStep 1833209 = 1374907) B1374907
theorem B1833311 : Blo 1220928 1833311 := bstep (se 1 (by rfl) ⟨1374983, by rfl⟩ : syracuseStep 1833311 = 2749967) B2749967
theorem B4405609 : Blo 1220928 4405609 := bstep (se 2 (by rfl) ⟨1652103, by rfl⟩ : syracuseStep 4405609 = 3304207) B3304207
theorem B1833323 : Blo 1220928 1833323 := bstep (se 1 (by rfl) ⟨1374992, by rfl⟩ : syracuseStep 1833323 = 2749985) B2749985
theorem B1546715 : Blo 1220928 1546715 := bstep (se 1 (by rfl) ⟨1160036, by rfl⟩ : syracuseStep 1546715 = 2320073) B2320073
theorem B2750939 : Blo 1220928 2750939 := bstep (se 1 (by rfl) ⟨2063204, by rfl⟩ : syracuseStep 2750939 = 4126409) B4126409
theorem B4127219 : Blo 1220928 4127219 := bstep (se 1 (by rfl) ⟨3095414, by rfl⟩ : syracuseStep 4127219 = 6190829) B6190829
theorem B1374799 : Blo 1220928 1374799 := bstep (se 1 (by rfl) ⟨1031099, by rfl⟩ : syracuseStep 1374799 = 2062199) B2062199
theorem B1833551 : Blo 1220928 1833551 := bstep (se 1 (by rfl) ⟨1375163, by rfl⟩ : syracuseStep 1833551 = 2750327) B2750327
theorem B1833671 : Blo 1220928 1833671 := bstep (se 1 (by rfl) ⟨1375253, by rfl⟩ : syracuseStep 1833671 = 2750507) B2750507
theorem B13220597 : Blo 1220928 13220597 := bstep (se 5 (by rfl) ⟨619715, by rfl⟩ : syracuseStep 13220597 = 1239431) B1239431
theorem B1833833 : Blo 1220928 1833833 := bstep (se 2 (by rfl) ⟨687687, by rfl⟩ : syracuseStep 1833833 = 1375375) B1375375
theorem B31742837 : Blo 1220928 31742837 := bstep (se 5 (by rfl) ⟨1487945, by rfl⟩ : syracuseStep 31742837 = 2975891) B2975891
theorem B2202511 : Blo 1220928 2202511 := bstep (se 1 (by rfl) ⟨1651883, by rfl⟩ : syracuseStep 2202511 = 3303767) B3303767
theorem B2063279 : Blo 1220928 2063279 := bstep (se 1 (by rfl) ⟨1547459, by rfl⟩ : syracuseStep 2063279 = 3094919) B3094919
theorem B2751407 : Blo 1220928 2751407 := bstep (se 1 (by rfl) ⟨2063555, by rfl⟩ : syracuseStep 2751407 = 4127111) B4127111
theorem B6183863 : Blo 1220928 6183863 := bstep (se 1 (by rfl) ⟨4637897, by rfl⟩ : syracuseStep 6183863 = 9275795) B9275795
theorem B1547191 : Blo 1220928 1547191 := bstep (se 1 (by rfl) ⟨1160393, by rfl⟩ : syracuseStep 1547191 = 2320787) B2320787
theorem B1833911 : Blo 1220928 1833911 := bstep (se 1 (by rfl) ⟨1375433, by rfl⟩ : syracuseStep 1833911 = 2750867) B2750867
theorem B1375195 : Blo 1220928 1375195 := bstep (se 1 (by rfl) ⟨1031396, by rfl⟩ : syracuseStep 1375195 = 2062793) B2062793
theorem B1833947 : Blo 1220928 1833947 := bstep (se 1 (by rfl) ⟨1375460, by rfl⟩ : syracuseStep 1833947 = 2750921) B2750921
theorem B7527397 : Blo 1220928 7527397 := bstep (se 4 (by rfl) ⟨705693, by rfl⟩ : syracuseStep 7527397 = 1411387) B1411387
theorem B4021249 : Blo 1220928 4021249 := bstep (se 2 (by rfl) ⟨1507968, by rfl⟩ : syracuseStep 4021249 = 3015937) B3015937
theorem B52878379 : Blo 1220928 52878379 := bstep (se 1 (by rfl) ⟨39658784, by rfl⟩ : syracuseStep 52878379 = 79317569) B79317569
theorem B8805455 : Blo 1220928 8805455 := bstep (se 1 (by rfl) ⟨6604091, by rfl⟩ : syracuseStep 8805455 = 13208183) B13208183
theorem B3914867 : Blo 1220928 3914867 := bstep (se 1 (by rfl) ⟨2936150, by rfl⟩ : syracuseStep 3914867 = 5872301) B5872301
theorem B10050905 : Blo 1220928 10050905 := bstep (se 2 (by rfl) ⟨3769089, by rfl⟩ : syracuseStep 10050905 = 7538179) B7538179
theorem B17603983 : Blo 1220928 17603983 := bstep (se 1 (by rfl) ⟨13202987, by rfl⟩ : syracuseStep 17603983 = 26405975) B26405975
theorem B8813987 : Blo 1220928 8813987 := bstep (se 1 (by rfl) ⟨6610490, by rfl⟩ : syracuseStep 8813987 = 13220981) B13220981
theorem B1375663 : Blo 1220928 1375663 := bstep (se 1 (by rfl) ⟨1031747, by rfl⟩ : syracuseStep 1375663 = 2063495) B2063495
theorem B1883657 : Blo 1220928 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B4636349 : Blo 1220928 4636349 := bstep (se 3 (by rfl) ⟨869315, by rfl⟩ : syracuseStep 4636349 = 1738631) B1738631
theorem B1220955 : Blo 1220928 1220955 := bstep (se 1 (by rfl) ⟨915716, by rfl⟩ : syracuseStep 1220955 = 1831433) B1831433
theorem B2384219 : Blo 1220928 2384219 := bstep (se 1 (by rfl) ⟨1788164, by rfl⟩ : syracuseStep 2384219 = 3576329) B3576329
theorem B1220975 : Blo 1220928 1220975 := bstep (se 1 (by rfl) ⟨915731, by rfl⟩ : syracuseStep 1220975 = 1831463) B1831463
theorem B1221031 : Blo 1220928 1221031 := bstep (se 1 (by rfl) ⟨915773, by rfl⟩ : syracuseStep 1221031 = 1831547) B1831547
theorem B6603227 : Blo 1220928 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B1221115 : Blo 1220928 1221115 := bstep (se 1 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 1221115 = 1831673) B1831673
theorem B2318843 : Blo 1220928 2318843 := bstep (se 1 (by rfl) ⟨1739132, by rfl⟩ : syracuseStep 2318843 = 3478265) B3478265
theorem B23814661 : Blo 1220928 23814661 := bstep (se 4 (by rfl) ⟨2232624, by rfl⟩ : syracuseStep 23814661 = 4465249) B4465249
theorem B1221183 : Blo 1220928 1221183 := bstep (se 1 (by rfl) ⟨915887, by rfl⟩ : syracuseStep 1221183 = 1831775) B1831775
theorem B1221191 : Blo 1220928 1221191 := bstep (se 1 (by rfl) ⟨915893, by rfl⟩ : syracuseStep 1221191 = 1831787) B1831787
theorem B3482183 : Blo 1220928 3482183 := bstep (se 1 (by rfl) ⟨2611637, by rfl⟩ : syracuseStep 3482183 = 5223275) B5223275
theorem B1958575 : Blo 1220928 1958575 := bstep (se 1 (by rfl) ⟨1468931, by rfl⟩ : syracuseStep 1958575 = 2937863) B2937863
theorem B1221343 : Blo 1220928 1221343 := bstep (se 1 (by rfl) ⟨916007, by rfl⟩ : syracuseStep 1221343 = 1832015) B1832015
theorem B13910777 : Blo 1220928 13910777 := bstep (se 2 (by rfl) ⟨5216541, by rfl⟩ : syracuseStep 13910777 = 10433083) B10433083
theorem B1221423 : Blo 1220928 1221423 := bstep (se 1 (by rfl) ⟨916067, by rfl⟩ : syracuseStep 1221423 = 1832135) B1832135
theorem B1467191 : Blo 1220928 1467191 := bstep (se 1 (by rfl) ⟨1100393, by rfl⟩ : syracuseStep 1467191 = 2200787) B2200787
theorem B4637519 : Blo 1220928 4637519 := bstep (se 1 (by rfl) ⟨3478139, by rfl⟩ : syracuseStep 4637519 = 6956279) B6956279
theorem B6185807 : Blo 1220928 6185807 := bstep (se 1 (by rfl) ⟨4639355, by rfl⟩ : syracuseStep 6185807 = 9278711) B9278711
theorem B1221531 : Blo 1220928 1221531 := bstep (se 1 (by rfl) ⟨916148, by rfl⟩ : syracuseStep 1221531 = 1832297) B1832297
theorem B19817399 : Blo 1220928 19817399 := bstep (se 1 (by rfl) ⟨14863049, by rfl⟩ : syracuseStep 19817399 = 29726099) B29726099
theorem B1221583 : Blo 1220928 1221583 := bstep (se 1 (by rfl) ⟨916187, by rfl⟩ : syracuseStep 1221583 = 1832375) B1832375
theorem B1221607 : Blo 1220928 1221607 := bstep (se 1 (by rfl) ⟨916205, by rfl⟩ : syracuseStep 1221607 = 1832411) B1832411
theorem B6186131 : Blo 1220928 6186131 := bstep (se 1 (by rfl) ⟨4639598, by rfl⟩ : syracuseStep 6186131 = 9279197) B9279197
theorem B114353369 : Blo 1220928 114353369 := bstep (se 2 (by rfl) ⟨42882513, by rfl⟩ : syracuseStep 114353369 = 85765027) B85765027
theorem B1221919 : Blo 1220928 1221919 := bstep (se 1 (by rfl) ⟨916439, by rfl⟩ : syracuseStep 1221919 = 1832879) B1832879
theorem B10036529 : Blo 1220928 10036529 := bstep (se 2 (by rfl) ⟨3763698, by rfl⟩ : syracuseStep 10036529 = 7527397) B7527397
theorem B1467739 : Blo 1220928 1467739 := bstep (se 1 (by rfl) ⟨1100804, by rfl⟩ : syracuseStep 1467739 = 2201609) B2201609
theorem B1221979 : Blo 1220928 1221979 := bstep (se 1 (by rfl) ⟨916484, by rfl⟩ : syracuseStep 1221979 = 1832969) B1832969
theorem B1221999 : Blo 1220928 1221999 := bstep (se 1 (by rfl) ⟨916499, by rfl⟩ : syracuseStep 1221999 = 1832999) B1832999
theorem B1222055 : Blo 1220928 1222055 := bstep (se 1 (by rfl) ⟨916541, by rfl⟩ : syracuseStep 1222055 = 1833083) B1833083
theorem B2319815 : Blo 1220928 2319815 := bstep (se 1 (by rfl) ⟨1739861, by rfl⟩ : syracuseStep 2319815 = 3479723) B3479723
theorem B1222139 : Blo 1220928 1222139 := bstep (se 1 (by rfl) ⟨916604, by rfl⟩ : syracuseStep 1222139 = 1833209) B1833209
theorem B1222207 : Blo 1220928 1222207 := bstep (se 1 (by rfl) ⟨916655, by rfl⟩ : syracuseStep 1222207 = 1833311) B1833311
theorem B1222215 : Blo 1220928 1222215 := bstep (se 1 (by rfl) ⟨916661, by rfl⟩ : syracuseStep 1222215 = 1833323) B1833323
theorem B1222367 : Blo 1220928 1222367 := bstep (se 1 (by rfl) ⟨916775, by rfl⟩ : syracuseStep 1222367 = 1833551) B1833551
theorem B1222447 : Blo 1220928 1222447 := bstep (se 1 (by rfl) ⟨916835, by rfl⟩ : syracuseStep 1222447 = 1833671) B1833671
theorem B16713539 : Blo 1220928 16713539 := bstep (se 1 (by rfl) ⟨12535154, by rfl⟩ : syracuseStep 16713539 = 25070309) B25070309
theorem B23471977 : Blo 1220928 23471977 := bstep (se 2 (by rfl) ⟨8801991, by rfl⟩ : syracuseStep 23471977 = 17603983) B17603983
theorem B23496581 : Blo 1220928 23496581 := bstep (se 4 (by rfl) ⟨2202804, by rfl⟩ : syracuseStep 23496581 = 4405609) B4405609
theorem B1222555 : Blo 1220928 1222555 := bstep (se 1 (by rfl) ⟨916916, by rfl⟩ : syracuseStep 1222555 = 1833833) B1833833
theorem B21161891 : Blo 1220928 21161891 := bstep (se 1 (by rfl) ⟨15871418, by rfl⟩ : syracuseStep 21161891 = 31742837) B31742837
theorem B4122575 : Blo 1220928 4122575 := bstep (se 1 (by rfl) ⟨3091931, by rfl⟩ : syracuseStep 4122575 = 6183863) B6183863
theorem B1222607 : Blo 1220928 1222607 := bstep (se 1 (by rfl) ⟨916955, by rfl⟩ : syracuseStep 1222607 = 1833911) B1833911
theorem B1222631 : Blo 1220928 1222631 := bstep (se 1 (by rfl) ⟨916973, by rfl⟩ : syracuseStep 1222631 = 1833947) B1833947
theorem B8358083 : Blo 1220928 8358083 := bstep (se 1 (by rfl) ⟨6268562, by rfl⟩ : syracuseStep 8358083 = 12537125) B12537125
theorem B5875991 : Blo 1220928 5875991 := bstep (se 1 (by rfl) ⟨4406993, by rfl⟩ : syracuseStep 5875991 = 8813987) B8813987
theorem B1255771 : Blo 1220928 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B23497127 : Blo 1220928 23497127 := bstep (se 1 (by rfl) ⟨17622845, by rfl⟩ : syracuseStep 23497127 = 35245691) B35245691
theorem B5294503 : Blo 1220928 5294503 := bstep (se 1 (by rfl) ⟨3970877, by rfl⟩ : syracuseStep 5294503 = 7941755) B7941755
theorem B6957485 : Blo 1220928 6957485 := bstep (se 3 (by rfl) ⟨1304528, by rfl⟩ : syracuseStep 6957485 = 2609057) B2609057
theorem B3090899 : Blo 1220928 3090899 := bstep (se 1 (by rfl) ⟨2318174, by rfl⟩ : syracuseStep 3090899 = 4636349) B4636349
theorem B4639295 : Blo 1220928 4639295 := bstep (se 1 (by rfl) ⟨3479471, by rfl⟩ : syracuseStep 4639295 = 6958943) B6958943
theorem B2320969 : Blo 1220928 2320969 := bstep (se 2 (by rfl) ⟨870363, by rfl⟩ : syracuseStep 2320969 = 1740727) B1740727
theorem B2935403 : Blo 1220928 2935403 := bstep (se 1 (by rfl) ⟨2201552, by rfl⟩ : syracuseStep 2935403 = 4403105) B4403105
theorem B5868227 : Blo 1220928 5868227 := bstep (se 1 (by rfl) ⟨4401170, by rfl⟩ : syracuseStep 5868227 = 8802341) B8802341
theorem B4467581 : Blo 1220928 4467581 := bstep (se 3 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 4467581 = 1675343) B1675343
theorem B17623939 : Blo 1220928 17623939 := bstep (se 1 (by rfl) ⟨13217954, by rfl⟩ : syracuseStep 17623939 = 26435909) B26435909
theorem B3091355 : Blo 1220928 3091355 := bstep (se 1 (by rfl) ⟨2318516, by rfl⟩ : syracuseStep 3091355 = 4637033) B4637033
theorem B4123547 : Blo 1220928 4123547 := bstep (se 1 (by rfl) ⟨3092660, by rfl⟩ : syracuseStep 4123547 = 6185321) B6185321
theorem B5287027 : Blo 1220928 5287027 := bstep (se 1 (by rfl) ⟨3965270, by rfl⟩ : syracuseStep 5287027 = 7930541) B7930541
theorem B2747591 : Blo 1220928 2747591 := bstep (se 1 (by rfl) ⟨2060693, by rfl⟩ : syracuseStep 2747591 = 4121387) B4121387
theorem B4639963 : Blo 1220928 4639963 := bstep (se 1 (by rfl) ⟨3479972, by rfl⟩ : syracuseStep 4639963 = 6959945) B6959945
theorem B13585627 : Blo 1220928 13585627 := bstep (se 1 (by rfl) ⟨10189220, by rfl⟩ : syracuseStep 13585627 = 20378441) B20378441
theorem B1305887 : Blo 1220928 1305887 := bstep (se 1 (by rfl) ⟨979415, by rfl⟩ : syracuseStep 1305887 = 1958831) B1958831
theorem B2747771 : Blo 1220928 2747771 := bstep (se 1 (by rfl) ⟨2060828, by rfl⟩ : syracuseStep 2747771 = 4121657) B4121657
theorem B3304891 : Blo 1220928 3304891 := bstep (se 1 (by rfl) ⟨2478668, by rfl⟩ : syracuseStep 3304891 = 4957337) B4957337
theorem B1650169 : Blo 1220928 1650169 := bstep (se 2 (by rfl) ⟨618813, by rfl⟩ : syracuseStep 1650169 = 1237627) B1237627
theorem B2747897 : Blo 1220928 2747897 := bstep (se 2 (by rfl) ⟨1030461, by rfl⟩ : syracuseStep 2747897 = 2060923) B2060923
theorem B2747987 : Blo 1220928 2747987 := bstep (se 1 (by rfl) ⟨2060990, by rfl⟩ : syracuseStep 2747987 = 4121981) B4121981
theorem B2748167 : Blo 1220928 2748167 := bstep (se 1 (by rfl) ⟨2061125, by rfl⟩ : syracuseStep 2748167 = 4122251) B4122251
theorem B2936681 : Blo 1220928 2936681 := bstep (se 2 (by rfl) ⟨1101255, by rfl⟩ : syracuseStep 2936681 = 2202511) B2202511
theorem B4124573 : Blo 1220928 4124573 := bstep (se 3 (by rfl) ⟨773357, by rfl⟩ : syracuseStep 4124573 = 1546715) B1546715
theorem B5361665 : Blo 1220928 5361665 := bstep (se 2 (by rfl) ⟨2010624, by rfl⟩ : syracuseStep 5361665 = 4021249) B4021249
theorem B3911689 : Blo 1220928 3911689 := bstep (se 2 (by rfl) ⟨1466883, by rfl⟩ : syracuseStep 3911689 = 2933767) B2933767
theorem B3092489 : Blo 1220928 3092489 := bstep (se 2 (by rfl) ⟨1159683, by rfl⟩ : syracuseStep 3092489 = 2319367) B2319367
theorem B4124681 : Blo 1220928 4124681 := bstep (se 2 (by rfl) ⟨1546755, by rfl⟩ : syracuseStep 4124681 = 3093511) B3093511
theorem B70504505 : Blo 1220928 70504505 := bstep (se 2 (by rfl) ⟨26439189, by rfl⟩ : syracuseStep 70504505 = 52878379) B52878379
theorem B6189209 : Blo 1220928 6189209 := bstep (se 2 (by rfl) ⟨2320953, by rfl⟩ : syracuseStep 6189209 = 4641907) B4641907
theorem B15274241 : Blo 1220928 15274241 := bstep (se 2 (by rfl) ⟨5727840, by rfl⟩ : syracuseStep 15274241 = 11455681) B11455681
theorem B2748779 : Blo 1220928 2748779 := bstep (se 1 (by rfl) ⟨2061584, by rfl⟩ : syracuseStep 2748779 = 4123169) B4123169
theorem B3092843 : Blo 1220928 3092843 := bstep (se 1 (by rfl) ⟨2319632, by rfl⟩ : syracuseStep 3092843 = 4639265) B4639265
theorem B2748923 : Blo 1220928 2748923 := bstep (se 1 (by rfl) ⟨2061692, by rfl⟩ : syracuseStep 2748923 = 4123385) B4123385
theorem B2060795 : Blo 1220928 2060795 := bstep (se 1 (by rfl) ⟨1545596, by rfl⟩ : syracuseStep 2060795 = 3091193) B3091193
theorem B1831487 : Blo 1220928 1831487 := bstep (se 1 (by rfl) ⟨1373615, by rfl⟩ : syracuseStep 1831487 = 2747231) B2747231
theorem B2749049 : Blo 1220928 2749049 := bstep (se 2 (by rfl) ⟨1030893, by rfl⟩ : syracuseStep 2749049 = 2061787) B2061787
theorem B2749103 : Blo 1220928 2749103 := bstep (se 1 (by rfl) ⟨2061827, by rfl⟩ : syracuseStep 2749103 = 4123655) B4123655
theorem B3093167 : Blo 1220928 3093167 := bstep (se 1 (by rfl) ⟨2319875, by rfl⟩ : syracuseStep 3093167 = 4639751) B4639751
theorem B1831607 : Blo 1220928 1831607 := bstep (se 1 (by rfl) ⟨1373705, by rfl⟩ : syracuseStep 1831607 = 2747411) B2747411
theorem B5870303 : Blo 1220928 5870303 := bstep (se 1 (by rfl) ⟨4402727, by rfl⟩ : syracuseStep 5870303 = 8805455) B8805455
theorem B2749175 : Blo 1220928 2749175 := bstep (se 1 (by rfl) ⟨2061881, by rfl⟩ : syracuseStep 2749175 = 4123763) B4123763
theorem B2609911 : Blo 1220928 2609911 := bstep (se 1 (by rfl) ⟨1957433, by rfl⟩ : syracuseStep 2609911 = 3914867) B3914867
theorem B11735837 : Blo 1220928 11735837 := bstep (se 3 (by rfl) ⟨2200469, by rfl⟩ : syracuseStep 11735837 = 4400939) B4400939
theorem B1831835 : Blo 1220928 1831835 := bstep (se 1 (by rfl) ⟨1373876, by rfl⟩ : syracuseStep 1831835 = 2747753) B2747753
theorem B2061227 : Blo 1220928 2061227 := bstep (se 1 (by rfl) ⟨1545920, by rfl⟩ : syracuseStep 2061227 = 3091841) B3091841
theorem B2749355 : Blo 1220928 2749355 := bstep (se 1 (by rfl) ⟨2062016, by rfl⟩ : syracuseStep 2749355 = 4124033) B4124033
theorem B6190019 : Blo 1220928 6190019 := bstep (se 1 (by rfl) ⟨4642514, by rfl⟩ : syracuseStep 6190019 = 9285029) B9285029
theorem B3093491 : Blo 1220928 3093491 := bstep (se 1 (by rfl) ⟨2320118, by rfl⟩ : syracuseStep 3093491 = 4640237) B4640237
theorem B1832231 : Blo 1220928 1832231 := bstep (se 1 (by rfl) ⟨1374173, by rfl⟩ : syracuseStep 1832231 = 2748347) B2748347
theorem B3478879 : Blo 1220928 3478879 := bstep (se 1 (by rfl) ⟨2609159, by rfl⟩ : syracuseStep 3478879 = 5218319) B5218319
theorem B3528031 : Blo 1220928 3528031 := bstep (se 1 (by rfl) ⟨2646023, by rfl⟩ : syracuseStep 3528031 = 5292047) B5292047
theorem B1832315 : Blo 1220928 1832315 := bstep (se 1 (by rfl) ⟨1374236, by rfl⟩ : syracuseStep 1832315 = 2748473) B2748473
theorem B8803723 : Blo 1220928 8803723 := bstep (se 1 (by rfl) ⟨6602792, by rfl⟩ : syracuseStep 8803723 = 13205585) B13205585
theorem B3093947 : Blo 1220928 3093947 := bstep (se 1 (by rfl) ⟨2320460, by rfl⟩ : syracuseStep 3093947 = 4640921) B4640921
theorem B2061767 : Blo 1220928 2061767 := bstep (se 1 (by rfl) ⟨1546325, by rfl⟩ : syracuseStep 2061767 = 3092651) B3092651
theorem B2749895 : Blo 1220928 2749895 := bstep (se 1 (by rfl) ⟨2062421, by rfl⟩ : syracuseStep 2749895 = 4124843) B4124843
theorem B1832441 : Blo 1220928 1832441 := bstep (se 2 (by rfl) ⟨687165, by rfl⟩ : syracuseStep 1832441 = 1374331) B1374331
theorem B114349603 : Blo 1220928 114349603 := bstep (se 1 (by rfl) ⟨85762202, by rfl⟩ : syracuseStep 114349603 = 171524405) B171524405
theorem B16709159 : Blo 1220928 16709159 := bstep (se 1 (by rfl) ⟨12531869, by rfl⟩ : syracuseStep 16709159 = 25063739) B25063739
theorem B1545799 : Blo 1220928 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B1373791 : Blo 1220928 1373791 := bstep (se 1 (by rfl) ⟨1030343, by rfl⟩ : syracuseStep 1373791 = 2060687) B2060687
theorem B1832543 : Blo 1220928 1832543 := bstep (se 1 (by rfl) ⟨1374407, by rfl⟩ : syracuseStep 1832543 = 2748815) B2748815
theorem B2201249 : Blo 1220928 2201249 := bstep (se 2 (by rfl) ⟨825468, by rfl⟩ : syracuseStep 2201249 = 1650937) B1650937
theorem B2750255 : Blo 1220928 2750255 := bstep (se 1 (by rfl) ⟨2062691, by rfl⟩ : syracuseStep 2750255 = 4125383) B4125383
theorem B6600503 : Blo 1220928 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B1832759 : Blo 1220928 1832759 := bstep (se 1 (by rfl) ⟨1374569, by rfl⟩ : syracuseStep 1832759 = 2749139) B2749139
theorem B1833065 : Blo 1220928 1833065 := bstep (se 2 (by rfl) ⟨687399, by rfl⟩ : syracuseStep 1833065 = 1374799) B1374799
theorem B36190475 : Blo 1220928 36190475 := bstep (se 1 (by rfl) ⟨27142856, by rfl⟩ : syracuseStep 36190475 = 54285713) B54285713
theorem B2750831 : Blo 1220928 2750831 := bstep (se 1 (by rfl) ⟨2063123, by rfl⟩ : syracuseStep 2750831 = 4126247) B4126247
theorem B4643183 : Blo 1220928 4643183 := bstep (se 1 (by rfl) ⟨3482387, by rfl⟩ : syracuseStep 4643183 = 6964775) B6964775
theorem B1833383 : Blo 1220928 1833383 := bstep (se 1 (by rfl) ⟨1375037, by rfl⟩ : syracuseStep 1833383 = 2750075) B2750075
theorem B2062759 : Blo 1220928 2062759 := bstep (se 1 (by rfl) ⟨1547069, by rfl⟩ : syracuseStep 2062759 = 3094139) B3094139
theorem B2750903 : Blo 1220928 2750903 := bstep (se 1 (by rfl) ⟨2063177, by rfl⟩ : syracuseStep 2750903 = 4126355) B4126355
theorem B10435067 : Blo 1220928 10435067 := bstep (se 1 (by rfl) ⟨7826300, by rfl⟩ : syracuseStep 10435067 = 15652601) B15652601
theorem B1833467 : Blo 1220928 1833467 := bstep (se 1 (by rfl) ⟨1375100, by rfl⟩ : syracuseStep 1833467 = 2750201) B2750201
theorem B2751047 : Blo 1220928 2751047 := bstep (se 1 (by rfl) ⟨2063285, by rfl⟩ : syracuseStep 2751047 = 4126571) B4126571
theorem B3095111 : Blo 1220928 3095111 := bstep (se 1 (by rfl) ⟨2321333, by rfl⟩ : syracuseStep 3095111 = 4642667) B4642667
theorem B2062921 : Blo 1220928 2062921 := bstep (se 2 (by rfl) ⟨773595, by rfl⟩ : syracuseStep 2062921 = 1547191) B1547191
theorem B2062955 : Blo 1220928 2062955 := bstep (se 1 (by rfl) ⟨1547216, by rfl⟩ : syracuseStep 2062955 = 3094433) B3094433
theorem B2751083 : Blo 1220928 2751083 := bstep (se 1 (by rfl) ⟨2063312, by rfl⟩ : syracuseStep 2751083 = 4126625) B4126625
theorem B1833593 : Blo 1220928 1833593 := bstep (se 2 (by rfl) ⟨687597, by rfl⟩ : syracuseStep 1833593 = 1375195) B1375195
theorem B1833647 : Blo 1220928 1833647 := bstep (se 1 (by rfl) ⟨1375235, by rfl⟩ : syracuseStep 1833647 = 2750471) B2750471
theorem B22305455 : Blo 1220928 22305455 := bstep (se 1 (by rfl) ⟨16729091, by rfl⟩ : syracuseStep 22305455 = 33458183) B33458183
theorem B6961859 : Blo 1220928 6961859 := bstep (se 1 (by rfl) ⟨5221394, by rfl⟩ : syracuseStep 6961859 = 10442789) B10442789
theorem B1374943 : Blo 1220928 1374943 := bstep (se 1 (by rfl) ⟨1031207, by rfl⟩ : syracuseStep 1374943 = 2062415) B2062415
theorem B1833695 : Blo 1220928 1833695 := bstep (se 1 (by rfl) ⟨1375271, by rfl⟩ : syracuseStep 1833695 = 2750543) B2750543
theorem B16718795 : Blo 1220928 16718795 := bstep (se 1 (by rfl) ⟨12539096, by rfl⟩ : syracuseStep 16718795 = 25078193) B25078193
theorem B1833959 : Blo 1220928 1833959 := bstep (se 1 (by rfl) ⟨1375469, by rfl⟩ : syracuseStep 1833959 = 2750939) B2750939
theorem B2751479 : Blo 1220928 2751479 := bstep (se 1 (by rfl) ⟨2063609, by rfl⟩ : syracuseStep 2751479 = 4127219) B4127219
theorem B5872763 : Blo 1220928 5872763 := bstep (se 1 (by rfl) ⟨4404572, by rfl⟩ : syracuseStep 5872763 = 8809145) B8809145
theorem B8813731 : Blo 1220928 8813731 := bstep (se 1 (by rfl) ⟨6610298, by rfl⟩ : syracuseStep 8813731 = 13220597) B13220597
theorem B40180931 : Blo 1220928 40180931 := bstep (se 1 (by rfl) ⟨30135698, by rfl⟩ : syracuseStep 40180931 = 60271397) B60271397
theorem B3136745 : Blo 1220928 3136745 := bstep (se 2 (by rfl) ⟨1176279, by rfl⟩ : syracuseStep 3136745 = 2352559) B2352559
theorem B1834217 : Blo 1220928 1834217 := bstep (se 2 (by rfl) ⟨687831, by rfl⟩ : syracuseStep 1834217 = 1375663) B1375663
theorem B1375519 : Blo 1220928 1375519 := bstep (se 1 (by rfl) ⟨1031639, by rfl⟩ : syracuseStep 1375519 = 2063279) B2063279
theorem B1834271 : Blo 1220928 1834271 := bstep (se 1 (by rfl) ⟨1375703, by rfl⟩ : syracuseStep 1834271 = 2751407) B2751407
theorem B24141199 : Blo 1220928 24141199 := bstep (se 1 (by rfl) ⟨18105899, by rfl⟩ : syracuseStep 24141199 = 36211799) B36211799
theorem B1547687 : Blo 1220928 1547687 := bstep (se 1 (by rfl) ⟨1160765, by rfl⟩ : syracuseStep 1547687 = 2321531) B2321531
theorem B6700603 : Blo 1220928 6700603 := bstep (se 1 (by rfl) ⟨5025452, by rfl⟩ : syracuseStep 6700603 = 10050905) B10050905
theorem B10182827 : Blo 1220928 10182827 := bstep (se 1 (by rfl) ⟨7637120, by rfl⟩ : syracuseStep 10182827 = 15274241) B15274241
theorem B1220991 : Blo 1220928 1220991 := bstep (se 1 (by rfl) ⟨915743, by rfl⟩ : syracuseStep 1220991 = 1831487) B1831487
theorem B1221071 : Blo 1220928 1221071 := bstep (se 1 (by rfl) ⟨915803, by rfl⟩ : syracuseStep 1221071 = 1831607) B1831607
theorem B9273851 : Blo 1220928 9273851 := bstep (se 1 (by rfl) ⟨6955388, by rfl⟩ : syracuseStep 9273851 = 13910777) B13910777
theorem B7823891 : Blo 1220928 7823891 := bstep (se 1 (by rfl) ⟨5867918, by rfl⟩ : syracuseStep 7823891 = 11735837) B11735837
theorem B1221223 : Blo 1220928 1221223 := bstep (se 1 (by rfl) ⟨915917, by rfl⟩ : syracuseStep 1221223 = 1831835) B1831835
theorem B8364653 : Blo 1220928 8364653 := bstep (se 3 (by rfl) ⟨1568372, by rfl⟩ : syracuseStep 8364653 = 3136745) B3136745
theorem B31752881 : Blo 1220928 31752881 := bstep (se 2 (by rfl) ⟨11907330, by rfl⟩ : syracuseStep 31752881 = 23814661) B23814661
theorem B3482365 : Blo 1220928 3482365 := bstep (se 3 (by rfl) ⟨652943, by rfl⟩ : syracuseStep 3482365 = 1305887) B1305887
theorem B76235579 : Blo 1220928 76235579 := bstep (se 1 (by rfl) ⟨57176684, by rfl⟩ : syracuseStep 76235579 = 114353369) B114353369
theorem B1221487 : Blo 1220928 1221487 := bstep (se 1 (by rfl) ⟨916115, by rfl⟩ : syracuseStep 1221487 = 1832231) B1832231
theorem B6357917 : Blo 1220928 6357917 := bstep (se 3 (by rfl) ⟨1192109, by rfl⟩ : syracuseStep 6357917 = 2384219) B2384219
theorem B1221543 : Blo 1220928 1221543 := bstep (se 1 (by rfl) ⟨916157, by rfl⟩ : syracuseStep 1221543 = 1832315) B1832315
theorem B1221627 : Blo 1220928 1221627 := bstep (se 1 (by rfl) ⟨916220, by rfl⟩ : syracuseStep 1221627 = 1832441) B1832441
theorem B1221695 : Blo 1220928 1221695 := bstep (se 1 (by rfl) ⟨916271, by rfl⟩ : syracuseStep 1221695 = 1832543) B1832543
theorem B1467499 : Blo 1220928 1467499 := bstep (se 1 (by rfl) ⟨1100624, by rfl⟩ : syracuseStep 1467499 = 2201249) B2201249
theorem B4400335 : Blo 1220928 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B1221839 : Blo 1220928 1221839 := bstep (se 1 (by rfl) ⟨916379, by rfl⟩ : syracuseStep 1221839 = 1832759) B1832759
theorem B11142359 : Blo 1220928 11142359 := bstep (se 1 (by rfl) ⟨8356769, by rfl⟩ : syracuseStep 11142359 = 16713539) B16713539
theorem B15664387 : Blo 1220928 15664387 := bstep (se 1 (by rfl) ⟨11748290, by rfl⟩ : syracuseStep 15664387 = 23496581) B23496581
theorem B14107927 : Blo 1220928 14107927 := bstep (se 1 (by rfl) ⟨10580945, by rfl⟩ : syracuseStep 14107927 = 21161891) B21161891
theorem B13919525 : Blo 1220928 13919525 := bstep (se 4 (by rfl) ⟨1304955, by rfl⟩ : syracuseStep 13919525 = 2609911) B2609911
theorem B1222043 : Blo 1220928 1222043 := bstep (se 1 (by rfl) ⟨916532, by rfl⟩ : syracuseStep 1222043 = 1833065) B1833065
theorem B5572055 : Blo 1220928 5572055 := bstep (se 1 (by rfl) ⟨4179041, by rfl⟩ : syracuseStep 5572055 = 8358083) B8358083
theorem B24126983 : Blo 1220928 24126983 := bstep (se 1 (by rfl) ⟨18095237, by rfl⟩ : syracuseStep 24126983 = 36190475) B36190475
theorem B3917327 : Blo 1220928 3917327 := bstep (se 1 (by rfl) ⟨2937995, by rfl⟩ : syracuseStep 3917327 = 5875991) B5875991
theorem B1222255 : Blo 1220928 1222255 := bstep (se 1 (by rfl) ⟨916691, by rfl⟩ : syracuseStep 1222255 = 1833383) B1833383
theorem B15664751 : Blo 1220928 15664751 := bstep (se 1 (by rfl) ⟨11748563, by rfl⟩ : syracuseStep 15664751 = 23497127) B23497127
theorem B4638323 : Blo 1220928 4638323 := bstep (se 1 (by rfl) ⟨3478742, by rfl⟩ : syracuseStep 4638323 = 6957485) B6957485
theorem B6186617 : Blo 1220928 6186617 := bstep (se 2 (by rfl) ⟨2319981, by rfl⟩ : syracuseStep 6186617 = 4639963) B4639963
theorem B6956711 : Blo 1220928 6956711 := bstep (se 1 (by rfl) ⟨5217533, by rfl⟩ : syracuseStep 6956711 = 10435067) B10435067
theorem B1222311 : Blo 1220928 1222311 := bstep (se 1 (by rfl) ⟨916733, by rfl⟩ : syracuseStep 1222311 = 1833467) B1833467
theorem B1222395 : Blo 1220928 1222395 := bstep (se 1 (by rfl) ⟨916796, by rfl⟩ : syracuseStep 1222395 = 1833593) B1833593
theorem B1222431 : Blo 1220928 1222431 := bstep (se 1 (by rfl) ⟨916823, by rfl⟩ : syracuseStep 1222431 = 1833647) B1833647
theorem B14870303 : Blo 1220928 14870303 := bstep (se 1 (by rfl) ⟨11152727, by rfl⟩ : syracuseStep 14870303 = 22305455) B22305455
theorem B4638505 : Blo 1220928 4638505 := bstep (se 2 (by rfl) ⟨1739439, by rfl⟩ : syracuseStep 4638505 = 3478879) B3478879
theorem B4704041 : Blo 1220928 4704041 := bstep (se 2 (by rfl) ⟨1764015, by rfl⟩ : syracuseStep 4704041 = 3528031) B3528031
theorem B1222463 : Blo 1220928 1222463 := bstep (se 1 (by rfl) ⟨916847, by rfl⟩ : syracuseStep 1222463 = 1833695) B1833695
theorem B32188265 : Blo 1220928 32188265 := bstep (se 2 (by rfl) ⟨12070599, by rfl⟩ : syracuseStep 32188265 = 24141199) B24141199
theorem B1222639 : Blo 1220928 1222639 := bstep (se 1 (by rfl) ⟨916979, by rfl⟩ : syracuseStep 1222639 = 1833959) B1833959
theorem B1222811 : Blo 1220928 1222811 := bstep (se 1 (by rfl) ⟨917108, by rfl⟩ : syracuseStep 1222811 = 1834217) B1834217
theorem B1222847 : Blo 1220928 1222847 := bstep (se 1 (by rfl) ⟨917135, by rfl⟩ : syracuseStep 1222847 = 1834271) B1834271
theorem B31295969 : Blo 1220928 31295969 := bstep (se 2 (by rfl) ⟨11735988, by rfl⟩ : syracuseStep 31295969 = 23471977) B23471977
theorem B57191093 : Blo 1220928 57191093 := bstep (se 5 (by rfl) ⟨2680832, by rfl⟩ : syracuseStep 57191093 = 5361665) B5361665
theorem B4402151 : Blo 1220928 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B2321455 : Blo 1220928 2321455 := bstep (se 1 (by rfl) ⟨1741091, by rfl⟩ : syracuseStep 2321455 = 3482183) B3482183
theorem B1674361 : Blo 1220928 1674361 := bstep (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) B1255771
theorem B3091679 : Blo 1220928 3091679 := bstep (se 1 (by rfl) ⟨2318759, by rfl⟩ : syracuseStep 3091679 = 4637519) B4637519
theorem B4123871 : Blo 1220928 4123871 := bstep (se 1 (by rfl) ⟨3092903, by rfl⟩ : syracuseStep 4123871 = 6185807) B6185807
theorem B4124087 : Blo 1220928 4124087 := bstep (se 1 (by rfl) ⟨3093065, by rfl⟩ : syracuseStep 4124087 = 6186131) B6186131
theorem B23498585 : Blo 1220928 23498585 := bstep (se 2 (by rfl) ⟨8811969, by rfl⟩ : syracuseStep 23498585 = 17623939) B17623939
theorem B2748383 : Blo 1220928 2748383 := bstep (se 1 (by rfl) ⟨2061287, by rfl⟩ : syracuseStep 2748383 = 4122575) B4122575
theorem B7049369 : Blo 1220928 7049369 := bstep (se 2 (by rfl) ⟨2643513, by rfl⟩ : syracuseStep 7049369 = 5287027) B5287027
theorem B11751641 : Blo 1220928 11751641 := bstep (se 2 (by rfl) ⟨4406865, by rfl⟩ : syracuseStep 11751641 = 8813731) B8813731
theorem B2060599 : Blo 1220928 2060599 := bstep (se 1 (by rfl) ⟨1545449, by rfl⟩ : syracuseStep 2060599 = 3090899) B3090899
theorem B3092863 : Blo 1220928 3092863 := bstep (se 1 (by rfl) ⟨2319647, by rfl⟩ : syracuseStep 3092863 = 4639295) B4639295
theorem B3912151 : Blo 1220928 3912151 := bstep (se 1 (by rfl) ⟨2934113, by rfl⟩ : syracuseStep 3912151 = 5868227) B5868227
theorem B4641239 : Blo 1220928 4641239 := bstep (se 1 (by rfl) ⟨3480929, by rfl⟩ : syracuseStep 4641239 = 6961859) B6961859
theorem B7827941 : Blo 1220928 7827941 := bstep (se 4 (by rfl) ⟨733869, by rfl⟩ : syracuseStep 7827941 = 1467739) B1467739
theorem B2978387 : Blo 1220928 2978387 := bstep (se 1 (by rfl) ⟨2233790, by rfl⟩ : syracuseStep 2978387 = 4467581) B4467581
theorem B2060903 : Blo 1220928 2060903 := bstep (se 1 (by rfl) ⟨1545677, by rfl⟩ : syracuseStep 2060903 = 3091355) B3091355
theorem B2749031 : Blo 1220928 2749031 := bstep (se 1 (by rfl) ⟨2061773, by rfl⟩ : syracuseStep 2749031 = 4123547) B4123547
theorem B11145863 : Blo 1220928 11145863 := bstep (se 1 (by rfl) ⟨8359397, by rfl⟩ : syracuseStep 11145863 = 16718795) B16718795
theorem B2200225 : Blo 1220928 2200225 := bstep (se 2 (by rfl) ⟨825084, by rfl⟩ : syracuseStep 2200225 = 1650169) B1650169
theorem B152466137 : Blo 1220928 152466137 := bstep (se 2 (by rfl) ⟨57174801, by rfl⟩ : syracuseStep 152466137 = 114349603) B114349603
theorem B8934137 : Blo 1220928 8934137 := bstep (se 2 (by rfl) ⟨3350301, by rfl⟩ : syracuseStep 8934137 = 6700603) B6700603
theorem B2061065 : Blo 1220928 2061065 := bstep (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) B1545799
theorem B1831721 : Blo 1220928 1831721 := bstep (se 2 (by rfl) ⟨686895, by rfl⟩ : syracuseStep 1831721 = 1373791) B1373791
theorem B1831727 : Blo 1220928 1831727 := bstep (se 1 (by rfl) ⟨1373795, by rfl⟩ : syracuseStep 1831727 = 2747591) B2747591
theorem B3912509 : Blo 1220928 3912509 := bstep (se 3 (by rfl) ⟨733595, by rfl⟩ : syracuseStep 3912509 = 1467191) B1467191
theorem B1831847 : Blo 1220928 1831847 := bstep (se 1 (by rfl) ⟨1373885, by rfl⟩ : syracuseStep 1831847 = 2747771) B2747771
theorem B1831931 : Blo 1220928 1831931 := bstep (se 1 (by rfl) ⟨1373948, by rfl⟩ : syracuseStep 1831931 = 2747897) B2747897
theorem B1831991 : Blo 1220928 1831991 := bstep (se 1 (by rfl) ⟨1373993, by rfl⟩ : syracuseStep 1831991 = 2747987) B2747987
theorem B1832111 : Blo 1220928 1832111 := bstep (se 1 (by rfl) ⟨1374083, by rfl⟩ : syracuseStep 1832111 = 2748167) B2748167
theorem B2749715 : Blo 1220928 2749715 := bstep (se 1 (by rfl) ⟨2062286, by rfl⟩ : syracuseStep 2749715 = 4124573) B4124573
theorem B2061659 : Blo 1220928 2061659 := bstep (se 1 (by rfl) ⟨1546244, by rfl⟩ : syracuseStep 2061659 = 3092489) B3092489
theorem B2749787 : Blo 1220928 2749787 := bstep (se 1 (by rfl) ⟨2062340, by rfl⟩ : syracuseStep 2749787 = 4124681) B4124681
theorem B5215585 : Blo 1220928 5215585 := bstep (se 2 (by rfl) ⟨1955844, by rfl⟩ : syracuseStep 5215585 = 3911689) B3911689
theorem B47003003 : Blo 1220928 47003003 := bstep (se 1 (by rfl) ⟨35252252, by rfl⟩ : syracuseStep 47003003 = 70504505) B70504505
theorem B4126139 : Blo 1220928 4126139 := bstep (se 1 (by rfl) ⟨3094604, by rfl⟩ : syracuseStep 4126139 = 6189209) B6189209
theorem B1832519 : Blo 1220928 1832519 := bstep (se 1 (by rfl) ⟨1374389, by rfl⟩ : syracuseStep 1832519 = 2748779) B2748779
theorem B2061895 : Blo 1220928 2061895 := bstep (se 1 (by rfl) ⟨1546421, by rfl⟩ : syracuseStep 2061895 = 3092843) B3092843
theorem B1373863 : Blo 1220928 1373863 := bstep (se 1 (by rfl) ⟨1030397, by rfl⟩ : syracuseStep 1373863 = 2060795) B2060795
theorem B1545895 : Blo 1220928 1545895 := bstep (se 1 (by rfl) ⟨1159421, by rfl⟩ : syracuseStep 1545895 = 2318843) B2318843
theorem B1832615 : Blo 1220928 1832615 := bstep (se 1 (by rfl) ⟨1374461, by rfl⟩ : syracuseStep 1832615 = 2748923) B2748923
theorem B1832699 : Blo 1220928 1832699 := bstep (se 1 (by rfl) ⟨1374524, by rfl⟩ : syracuseStep 1832699 = 2749049) B2749049
theorem B1832735 : Blo 1220928 1832735 := bstep (se 1 (by rfl) ⟨1374551, by rfl⟩ : syracuseStep 1832735 = 2749103) B2749103
theorem B2062111 : Blo 1220928 2062111 := bstep (se 1 (by rfl) ⟨1546583, by rfl⟩ : syracuseStep 2062111 = 3093167) B3093167
theorem B3913535 : Blo 1220928 3913535 := bstep (se 1 (by rfl) ⟨2935151, by rfl⟩ : syracuseStep 3913535 = 5870303) B5870303
theorem B1832783 : Blo 1220928 1832783 := bstep (se 1 (by rfl) ⟨1374587, by rfl⟩ : syracuseStep 1832783 = 2749175) B2749175
theorem B2750345 : Blo 1220928 2750345 := bstep (se 2 (by rfl) ⟨1031379, by rfl⟩ : syracuseStep 2750345 = 2062759) B2062759
theorem B1374151 : Blo 1220928 1374151 := bstep (se 1 (by rfl) ⟨1030613, by rfl⟩ : syracuseStep 1374151 = 2061227) B2061227
theorem B1832903 : Blo 1220928 1832903 := bstep (se 1 (by rfl) ⟨1374677, by rfl⟩ : syracuseStep 1832903 = 2749355) B2749355
theorem B13211599 : Blo 1220928 13211599 := bstep (se 1 (by rfl) ⟨9908699, by rfl⟩ : syracuseStep 13211599 = 19817399) B19817399
theorem B4126679 : Blo 1220928 4126679 := bstep (se 1 (by rfl) ⟨3095009, by rfl⟩ : syracuseStep 4126679 = 6190019) B6190019
theorem B2062327 : Blo 1220928 2062327 := bstep (se 1 (by rfl) ⟨1546745, by rfl⟩ : syracuseStep 2062327 = 3093491) B3093491
theorem B2750561 : Blo 1220928 2750561 := bstep (se 2 (by rfl) ⟨1031460, by rfl⟩ : syracuseStep 2750561 = 2062921) B2062921
theorem B3094625 : Blo 1220928 3094625 := bstep (se 2 (by rfl) ⟨1160484, by rfl⟩ : syracuseStep 3094625 = 2320969) B2320969
theorem B6691019 : Blo 1220928 6691019 := bstep (se 1 (by rfl) ⟨5018264, by rfl⟩ : syracuseStep 6691019 = 10036529) B10036529
theorem B2611433 : Blo 1220928 2611433 := bstep (se 2 (by rfl) ⟨979287, by rfl⟩ : syracuseStep 2611433 = 1958575) B1958575
theorem B2062631 : Blo 1220928 2062631 := bstep (se 1 (by rfl) ⟨1546973, by rfl⟩ : syracuseStep 2062631 = 3093947) B3093947
theorem B1833257 : Blo 1220928 1833257 := bstep (se 2 (by rfl) ⟨687471, by rfl⟩ : syracuseStep 1833257 = 1374943) B1374943
theorem B1374511 : Blo 1220928 1374511 := bstep (se 1 (by rfl) ⟨1030883, by rfl⟩ : syracuseStep 1374511 = 2061767) B2061767
theorem B1546543 : Blo 1220928 1546543 := bstep (se 1 (by rfl) ⟨1159907, by rfl⟩ : syracuseStep 1546543 = 2319815) B2319815
theorem B1833263 : Blo 1220928 1833263 := bstep (se 1 (by rfl) ⟨1374947, by rfl⟩ : syracuseStep 1833263 = 2749895) B2749895
theorem B11139439 : Blo 1220928 11139439 := bstep (se 1 (by rfl) ⟨8354579, by rfl⟩ : syracuseStep 11139439 = 16709159) B16709159
theorem B4127165 : Blo 1220928 4127165 := bstep (se 3 (by rfl) ⟨773843, by rfl⟩ : syracuseStep 4127165 = 1547687) B1547687
theorem B72456677 : Blo 1220928 72456677 := bstep (se 4 (by rfl) ⟨6792813, by rfl⟩ : syracuseStep 72456677 = 13585627) B13585627
theorem B1833503 : Blo 1220928 1833503 := bstep (se 1 (by rfl) ⟨1375127, by rfl⟩ : syracuseStep 1833503 = 2750255) B2750255
theorem B1833887 : Blo 1220928 1833887 := bstep (se 1 (by rfl) ⟨1375415, by rfl⟩ : syracuseStep 1833887 = 2750831) B2750831
theorem B3095455 : Blo 1220928 3095455 := bstep (se 1 (by rfl) ⟨2321591, by rfl⟩ : syracuseStep 3095455 = 4643183) B4643183
theorem B1833935 : Blo 1220928 1833935 := bstep (se 1 (by rfl) ⟨1375451, by rfl⟩ : syracuseStep 1833935 = 2750903) B2750903
theorem B1834025 : Blo 1220928 1834025 := bstep (se 2 (by rfl) ⟨687759, by rfl⟩ : syracuseStep 1834025 = 1375519) B1375519
theorem B1834031 : Blo 1220928 1834031 := bstep (se 1 (by rfl) ⟨1375523, by rfl⟩ : syracuseStep 1834031 = 2751047) B2751047
theorem B2063407 : Blo 1220928 2063407 := bstep (se 1 (by rfl) ⟨1547555, by rfl⟩ : syracuseStep 2063407 = 3095111) B3095111
theorem B1956935 : Blo 1220928 1956935 := bstep (se 1 (by rfl) ⟨1467701, by rfl⟩ : syracuseStep 1956935 = 2935403) B2935403
theorem B1375303 : Blo 1220928 1375303 := bstep (se 1 (by rfl) ⟨1031477, by rfl⟩ : syracuseStep 1375303 = 2062955) B2062955
theorem B1834055 : Blo 1220928 1834055 := bstep (se 1 (by rfl) ⟨1375541, by rfl⟩ : syracuseStep 1834055 = 2751083) B2751083
theorem B11738297 : Blo 1220928 11738297 := bstep (se 2 (by rfl) ⟨4401861, by rfl⟩ : syracuseStep 11738297 = 8803723) B8803723
theorem B4406521 : Blo 1220928 4406521 := bstep (se 2 (by rfl) ⟨1652445, by rfl⟩ : syracuseStep 4406521 = 3304891) B3304891
theorem B1834319 : Blo 1220928 1834319 := bstep (se 1 (by rfl) ⟨1375739, by rfl⟩ : syracuseStep 1834319 = 2751479) B2751479
theorem B3915175 : Blo 1220928 3915175 := bstep (se 1 (by rfl) ⟨2936381, by rfl⟩ : syracuseStep 3915175 = 5872763) B5872763
theorem B26787287 : Blo 1220928 26787287 := bstep (se 1 (by rfl) ⟨20090465, by rfl⟩ : syracuseStep 26787287 = 40180931) B40180931
theorem B28237349 : Blo 1220928 28237349 := bstep (se 4 (by rfl) ⟨2647251, by rfl⟩ : syracuseStep 28237349 = 5294503) B5294503
theorem B1957787 : Blo 1220928 1957787 := bstep (se 1 (by rfl) ⟨1468340, by rfl⟩ : syracuseStep 1957787 = 2936681) B2936681
theorem B5218627 : Blo 1220928 5218627 := bstep (se 1 (by rfl) ⟨3913970, by rfl⟩ : syracuseStep 5218627 = 7827941) B7827941
theorem B7430575 : Blo 1220928 7430575 := bstep (se 1 (by rfl) ⟨5572931, by rfl⟩ : syracuseStep 7430575 = 11145863) B11145863
theorem B21168587 : Blo 1220928 21168587 := bstep (se 1 (by rfl) ⟨15876440, by rfl⟩ : syracuseStep 21168587 = 31752881) B31752881
theorem B14852585 : Blo 1220928 14852585 := bstep (se 2 (by rfl) ⟨5569719, by rfl⟩ : syracuseStep 14852585 = 11139439) B11139439
theorem B5956091 : Blo 1220928 5956091 := bstep (se 1 (by rfl) ⟨4467068, by rfl⟩ : syracuseStep 5956091 = 8934137) B8934137
theorem B1221147 : Blo 1220928 1221147 := bstep (se 1 (by rfl) ⟨915860, by rfl⟩ : syracuseStep 1221147 = 1831721) B1831721
theorem B17842717 : Blo 1220928 17842717 := bstep (se 3 (by rfl) ⟨3345509, by rfl⟩ : syracuseStep 17842717 = 6691019) B6691019
theorem B1221151 : Blo 1220928 1221151 := bstep (se 1 (by rfl) ⟨915863, by rfl⟩ : syracuseStep 1221151 = 1831727) B1831727
theorem B50823719 : Blo 1220928 50823719 := bstep (se 1 (by rfl) ⟨38117789, by rfl⟩ : syracuseStep 50823719 = 76235579) B76235579
theorem B1221231 : Blo 1220928 1221231 := bstep (se 1 (by rfl) ⟨915923, by rfl⟩ : syracuseStep 1221231 = 1831847) B1831847
theorem B1221287 : Blo 1220928 1221287 := bstep (se 1 (by rfl) ⟨915965, by rfl⟩ : syracuseStep 1221287 = 1831931) B1831931
theorem B1221327 : Blo 1220928 1221327 := bstep (se 1 (by rfl) ⟨915995, by rfl⟩ : syracuseStep 1221327 = 1831991) B1831991
theorem B1221407 : Blo 1220928 1221407 := bstep (se 1 (by rfl) ⟨916055, by rfl⟩ : syracuseStep 1221407 = 1832111) B1832111
theorem B2933633 : Blo 1220928 2933633 := bstep (se 2 (by rfl) ⟨1100112, by rfl⟩ : syracuseStep 2933633 = 2200225) B2200225
theorem B31335335 : Blo 1220928 31335335 := bstep (se 1 (by rfl) ⟨23501501, by rfl⟩ : syracuseStep 31335335 = 47003003) B47003003
theorem B1221679 : Blo 1220928 1221679 := bstep (se 1 (by rfl) ⟨916259, by rfl⟩ : syracuseStep 1221679 = 1832519) B1832519
theorem B4637807 : Blo 1220928 4637807 := bstep (se 1 (by rfl) ⟨3478355, by rfl⟩ : syracuseStep 4637807 = 6956711) B6956711
theorem B1221743 : Blo 1220928 1221743 := bstep (se 1 (by rfl) ⟨916307, by rfl⟩ : syracuseStep 1221743 = 1832615) B1832615
theorem B1221799 : Blo 1220928 1221799 := bstep (se 1 (by rfl) ⟨916349, by rfl⟩ : syracuseStep 1221799 = 1832699) B1832699
theorem B1221823 : Blo 1220928 1221823 := bstep (se 1 (by rfl) ⟨916367, by rfl⟩ : syracuseStep 1221823 = 1832735) B1832735
theorem B9913535 : Blo 1220928 9913535 := bstep (se 1 (by rfl) ⟨7435151, by rfl⟩ : syracuseStep 9913535 = 14870303) B14870303
theorem B1221855 : Blo 1220928 1221855 := bstep (se 1 (by rfl) ⟨916391, by rfl⟩ : syracuseStep 1221855 = 1832783) B1832783
theorem B1221935 : Blo 1220928 1221935 := bstep (se 1 (by rfl) ⟨916451, by rfl⟩ : syracuseStep 1221935 = 1832903) B1832903
theorem B10446205 : Blo 1220928 10446205 := bstep (se 3 (by rfl) ⟨1958663, by rfl⟩ : syracuseStep 10446205 = 3917327) B3917327
theorem B1222171 : Blo 1220928 1222171 := bstep (se 1 (by rfl) ⟨916628, by rfl⟩ : syracuseStep 1222171 = 1833257) B1833257
theorem B1222175 : Blo 1220928 1222175 := bstep (se 1 (by rfl) ⟨916631, by rfl⟩ : syracuseStep 1222175 = 1833263) B1833263
theorem B5867113 : Blo 1220928 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B5875361 : Blo 1220928 5875361 := bstep (se 2 (by rfl) ⟨2203260, by rfl⟩ : syracuseStep 5875361 = 4406521) B4406521
theorem B1222335 : Blo 1220928 1222335 := bstep (se 1 (by rfl) ⟨916751, by rfl⟩ : syracuseStep 1222335 = 1833503) B1833503
theorem B18810569 : Blo 1220928 18810569 := bstep (se 2 (by rfl) ⟨7053963, by rfl⟩ : syracuseStep 18810569 = 14107927) B14107927
theorem B38127395 : Blo 1220928 38127395 := bstep (se 1 (by rfl) ⟨28595546, by rfl⟩ : syracuseStep 38127395 = 57191093) B57191093
theorem B5220233 : Blo 1220928 5220233 := bstep (se 2 (by rfl) ⟨1957587, by rfl⟩ : syracuseStep 5220233 = 3915175) B3915175
theorem B1222591 : Blo 1220928 1222591 := bstep (se 1 (by rfl) ⟨916943, by rfl⟩ : syracuseStep 1222591 = 1833887) B1833887
theorem B1222623 : Blo 1220928 1222623 := bstep (se 1 (by rfl) ⟨916967, by rfl⟩ : syracuseStep 1222623 = 1833935) B1833935
theorem B2934767 : Blo 1220928 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B1222683 : Blo 1220928 1222683 := bstep (se 1 (by rfl) ⟨917012, by rfl⟩ : syracuseStep 1222683 = 1834025) B1834025
theorem B1222687 : Blo 1220928 1222687 := bstep (se 1 (by rfl) ⟨917015, by rfl⟩ : syracuseStep 1222687 = 1834031) B1834031
theorem B1304623 : Blo 1220928 1304623 := bstep (se 1 (by rfl) ⟨978467, by rfl⟩ : syracuseStep 1304623 = 1956935) B1956935
theorem B1222703 : Blo 1220928 1222703 := bstep (se 1 (by rfl) ⟨917027, by rfl⟩ : syracuseStep 1222703 = 1834055) B1834055
theorem B12544109 : Blo 1220928 12544109 := bstep (se 3 (by rfl) ⟨2352020, by rfl⟩ : syracuseStep 12544109 = 4704041) B4704041
theorem B7825531 : Blo 1220928 7825531 := bstep (se 1 (by rfl) ⟨5869148, by rfl⟩ : syracuseStep 7825531 = 11738297) B11738297
theorem B1222879 : Blo 1220928 1222879 := bstep (se 1 (by rfl) ⟨917159, by rfl⟩ : syracuseStep 1222879 = 1834319) B1834319
theorem B15665723 : Blo 1220928 15665723 := bstep (se 1 (by rfl) ⟨11749292, by rfl⟩ : syracuseStep 15665723 = 23498585) B23498585
theorem B1305191 : Blo 1220928 1305191 := bstep (se 1 (by rfl) ⟨978893, by rfl⟩ : syracuseStep 1305191 = 1957787) B1957787
theorem B17615465 : Blo 1220928 17615465 := bstep (se 2 (by rfl) ⟨6605799, by rfl⟩ : syracuseStep 17615465 = 13211599) B13211599
theorem B7834427 : Blo 1220928 7834427 := bstep (se 1 (by rfl) ⟨5875820, by rfl⟩ : syracuseStep 7834427 = 11751641) B11751641
theorem B1985591 : Blo 1220928 1985591 := bstep (se 1 (by rfl) ⟨1489193, by rfl⟩ : syracuseStep 1985591 = 2978387) B2978387
theorem B2747465 : Blo 1220928 2747465 := bstep (se 2 (by rfl) ⟨1030299, by rfl⟩ : syracuseStep 2747465 = 2060599) B2060599
theorem B4123817 : Blo 1220928 4123817 := bstep (se 2 (by rfl) ⟨1546431, by rfl⟩ : syracuseStep 4123817 = 3092863) B3092863
theorem B4238611 : Blo 1220928 4238611 := bstep (se 1 (by rfl) ⟨3178958, by rfl⟩ : syracuseStep 4238611 = 6357917) B6357917
theorem B3714703 : Blo 1220928 3714703 := bstep (se 1 (by rfl) ⟨2786027, by rfl⟩ : syracuseStep 3714703 = 5572055) B5572055
theorem B16084655 : Blo 1220928 16084655 := bstep (se 1 (by rfl) ⟨12063491, by rfl⟩ : syracuseStep 16084655 = 24126983) B24126983
theorem B3092215 : Blo 1220928 3092215 := bstep (se 1 (by rfl) ⟨2319161, by rfl⟩ : syracuseStep 3092215 = 4638323) B4638323
theorem B4124411 : Blo 1220928 4124411 := bstep (se 1 (by rfl) ⟨3093308, by rfl⟩ : syracuseStep 4124411 = 6186617) B6186617
theorem B2609023 : Blo 1220928 2609023 := bstep (se 1 (by rfl) ⟨1956767, by rfl⟩ : syracuseStep 2609023 = 3913535) B3913535
theorem B21458843 : Blo 1220928 21458843 := bstep (se 1 (by rfl) ⟨16094132, by rfl⟩ : syracuseStep 21458843 = 32188265) B32188265
theorem B1740955 : Blo 1220928 1740955 := bstep (se 1 (by rfl) ⟨1305716, by rfl⟩ : syracuseStep 1740955 = 2611433) B2611433
theorem B2232481 : Blo 1220928 2232481 := bstep (se 2 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 2232481 = 1674361) B1674361
theorem B48304451 : Blo 1220928 48304451 := bstep (se 1 (by rfl) ⟨36228338, by rfl⟩ : syracuseStep 48304451 = 72456677) B72456677
theorem B20885849 : Blo 1220928 20885849 := bstep (se 2 (by rfl) ⟨7832193, by rfl⟩ : syracuseStep 20885849 = 15664387) B15664387
theorem B2749193 : Blo 1220928 2749193 := bstep (se 2 (by rfl) ⟨1030947, by rfl⟩ : syracuseStep 2749193 = 2061895) B2061895
theorem B2061119 : Blo 1220928 2061119 := bstep (se 1 (by rfl) ⟨1545839, by rfl⟩ : syracuseStep 2061119 = 3091679) B3091679
theorem B2749247 : Blo 1220928 2749247 := bstep (se 1 (by rfl) ⟨2061935, by rfl⟩ : syracuseStep 2749247 = 4123871) B4123871
theorem B10433357 : Blo 1220928 10433357 := bstep (se 3 (by rfl) ⟨1956254, by rfl⟩ : syracuseStep 10433357 = 3912509) B3912509
theorem B1831817 : Blo 1220928 1831817 := bstep (se 2 (by rfl) ⟨686931, by rfl⟩ : syracuseStep 1831817 = 1373863) B1373863
theorem B2061193 : Blo 1220928 2061193 := bstep (se 2 (by rfl) ⟨772947, by rfl⟩ : syracuseStep 2061193 = 1545895) B1545895
theorem B2749391 : Blo 1220928 2749391 := bstep (se 1 (by rfl) ⟨2062043, by rfl⟩ : syracuseStep 2749391 = 4124087) B4124087
theorem B2749481 : Blo 1220928 2749481 := bstep (se 2 (by rfl) ⟨1031055, by rfl⟩ : syracuseStep 2749481 = 2062111) B2062111
theorem B1832201 : Blo 1220928 1832201 := bstep (se 2 (by rfl) ⟨687075, by rfl⟩ : syracuseStep 1832201 = 1374151) B1374151
theorem B1832255 : Blo 1220928 1832255 := bstep (se 1 (by rfl) ⟨1374191, by rfl⟩ : syracuseStep 1832255 = 2748383) B2748383
theorem B2749769 : Blo 1220928 2749769 := bstep (se 2 (by rfl) ⟨1031163, by rfl⟩ : syracuseStep 2749769 = 2062327) B2062327
theorem B4699579 : Blo 1220928 4699579 := bstep (se 1 (by rfl) ⟨3524684, by rfl⟩ : syracuseStep 4699579 = 7049369) B7049369
theorem B6788551 : Blo 1220928 6788551 := bstep (se 1 (by rfl) ⟨5091413, by rfl⟩ : syracuseStep 6788551 = 10182827) B10182827
theorem B3094159 : Blo 1220928 3094159 := bstep (se 1 (by rfl) ⟨2320619, by rfl⟩ : syracuseStep 3094159 = 4641239) B4641239
theorem B6182567 : Blo 1220928 6182567 := bstep (se 1 (by rfl) ⟨4636925, by rfl⟩ : syracuseStep 6182567 = 9273851) B9273851
theorem B5215927 : Blo 1220928 5215927 := bstep (se 1 (by rfl) ⟨3911945, by rfl⟩ : syracuseStep 5215927 = 7823891) B7823891
theorem B1832681 : Blo 1220928 1832681 := bstep (se 2 (by rfl) ⟨687255, by rfl⟩ : syracuseStep 1832681 = 1374511) B1374511
theorem B2062057 : Blo 1220928 2062057 := bstep (se 2 (by rfl) ⟨773271, by rfl⟩ : syracuseStep 2062057 = 1546543) B1546543
theorem B1373935 : Blo 1220928 1373935 := bstep (se 1 (by rfl) ⟨1030451, by rfl⟩ : syracuseStep 1373935 = 2060903) B2060903
theorem B1832687 : Blo 1220928 1832687 := bstep (se 1 (by rfl) ⟨1374515, by rfl⟩ : syracuseStep 1832687 = 2749031) B2749031
theorem B5576435 : Blo 1220928 5576435 := bstep (se 1 (by rfl) ⟨4182326, by rfl⟩ : syracuseStep 5576435 = 8364653) B8364653
theorem B101644091 : Blo 1220928 101644091 := bstep (se 1 (by rfl) ⟨76233068, by rfl⟩ : syracuseStep 101644091 = 152466137) B152466137
theorem B1374043 : Blo 1220928 1374043 := bstep (se 1 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 1374043 = 2061065) B2061065
theorem B5216201 : Blo 1220928 5216201 := bstep (se 2 (by rfl) ⟨1956075, by rfl⟩ : syracuseStep 5216201 = 3912151) B3912151
theorem B7428239 : Blo 1220928 7428239 := bstep (se 1 (by rfl) ⟨5571179, by rfl⟩ : syracuseStep 7428239 = 11142359) B11142359
theorem B1833143 : Blo 1220928 1833143 := bstep (se 1 (by rfl) ⟨1374857, by rfl⟩ : syracuseStep 1833143 = 2749715) B2749715
theorem B9279683 : Blo 1220928 9279683 := bstep (se 1 (by rfl) ⟨6959762, by rfl⟩ : syracuseStep 9279683 = 13919525) B13919525
theorem B1374439 : Blo 1220928 1374439 := bstep (se 1 (by rfl) ⟨1030829, by rfl⟩ : syracuseStep 1374439 = 2061659) B2061659
theorem B1833191 : Blo 1220928 1833191 := bstep (se 1 (by rfl) ⟨1374893, by rfl⟩ : syracuseStep 1833191 = 2749787) B2749787
theorem B2750759 : Blo 1220928 2750759 := bstep (se 1 (by rfl) ⟨2063069, by rfl⟩ : syracuseStep 2750759 = 4126139) B4126139
theorem B4643153 : Blo 1220928 4643153 := bstep (se 2 (by rfl) ⟨1741182, by rfl⟩ : syracuseStep 4643153 = 3482365) B3482365
theorem B10443167 : Blo 1220928 10443167 := bstep (se 1 (by rfl) ⟨7832375, by rfl⟩ : syracuseStep 10443167 = 15664751) B15664751
theorem B4127273 : Blo 1220928 4127273 := bstep (se 2 (by rfl) ⟨1547727, by rfl⟩ : syracuseStep 4127273 = 3095455) B3095455
theorem B1833563 : Blo 1220928 1833563 := bstep (se 1 (by rfl) ⟨1375172, by rfl⟩ : syracuseStep 1833563 = 2750345) B2750345
theorem B2751119 : Blo 1220928 2751119 := bstep (se 1 (by rfl) ⟨2063339, by rfl⟩ : syracuseStep 2751119 = 4126679) B4126679
theorem B2751209 : Blo 1220928 2751209 := bstep (se 2 (by rfl) ⟨1031703, by rfl⟩ : syracuseStep 2751209 = 2063407) B2063407
theorem B3095273 : Blo 1220928 3095273 := bstep (se 2 (by rfl) ⟨1160727, by rfl⟩ : syracuseStep 3095273 = 2321455) B2321455
theorem B1833707 : Blo 1220928 1833707 := bstep (se 1 (by rfl) ⟨1375280, by rfl⟩ : syracuseStep 1833707 = 2750561) B2750561
theorem B2063083 : Blo 1220928 2063083 := bstep (se 1 (by rfl) ⟨1547312, by rfl⟩ : syracuseStep 2063083 = 3094625) B3094625
theorem B1833737 : Blo 1220928 1833737 := bstep (se 2 (by rfl) ⟨687651, by rfl⟩ : syracuseStep 1833737 = 1375303) B1375303
theorem B1956665 : Blo 1220928 1956665 := bstep (se 2 (by rfl) ⟨733749, by rfl⟩ : syracuseStep 1956665 = 1467499) B1467499
theorem B1375087 : Blo 1220928 1375087 := bstep (se 1 (by rfl) ⟨1031315, by rfl⟩ : syracuseStep 1375087 = 2062631) B2062631
theorem B2751443 : Blo 1220928 2751443 := bstep (se 1 (by rfl) ⟨2063582, by rfl⟩ : syracuseStep 2751443 = 4127165) B4127165
theorem B20863979 : Blo 1220928 20863979 := bstep (se 1 (by rfl) ⟨15647984, by rfl⟩ : syracuseStep 20863979 = 31295969) B31295969
theorem B6954113 : Blo 1220928 6954113 := bstep (se 2 (by rfl) ⟨2607792, by rfl⟩ : syracuseStep 6954113 = 5215585) B5215585
theorem B17858191 : Blo 1220928 17858191 := bstep (se 1 (by rfl) ⟨13393643, by rfl⟩ : syracuseStep 17858191 = 26787287) B26787287
theorem B18824899 : Blo 1220928 18824899 := bstep (se 1 (by rfl) ⟨14118674, by rfl⟩ : syracuseStep 18824899 = 28237349) B28237349
theorem B6184673 : Blo 1220928 6184673 := bstep (se 2 (by rfl) ⟨2319252, by rfl⟩ : syracuseStep 6184673 = 4638505) B4638505
theorem B32202967 : Blo 1220928 32202967 := bstep (se 1 (by rfl) ⟨24152225, by rfl⟩ : syracuseStep 32202967 = 48304451) B48304451
theorem B33882479 : Blo 1220928 33882479 := bstep (se 1 (by rfl) ⟨25411859, by rfl⟩ : syracuseStep 33882479 = 50823719) B50823719
theorem B6955571 : Blo 1220928 6955571 := bstep (se 1 (by rfl) ⟨5216678, by rfl⟩ : syracuseStep 6955571 = 10433357) B10433357
theorem B1221211 : Blo 1220928 1221211 := bstep (se 1 (by rfl) ⟨915908, by rfl⟩ : syracuseStep 1221211 = 1831817) B1831817
theorem B20890223 : Blo 1220928 20890223 := bstep (se 1 (by rfl) ⟨15667667, by rfl⟩ : syracuseStep 20890223 = 31335335) B31335335
theorem B23790289 : Blo 1220928 23790289 := bstep (se 2 (by rfl) ⟨8921358, by rfl⟩ : syracuseStep 23790289 = 17842717) B17842717
theorem B1221467 : Blo 1220928 1221467 := bstep (se 1 (by rfl) ⟨916100, by rfl⟩ : syracuseStep 1221467 = 1832201) B1832201
theorem B1221503 : Blo 1220928 1221503 := bstep (se 1 (by rfl) ⟨916127, by rfl⟩ : syracuseStep 1221503 = 1832255) B1832255
theorem B3916907 : Blo 1220928 3916907 := bstep (se 1 (by rfl) ⟨2937680, by rfl⟩ : syracuseStep 3916907 = 5875361) B5875361
theorem B4121711 : Blo 1220928 4121711 := bstep (se 1 (by rfl) ⟨3091283, by rfl⟩ : syracuseStep 4121711 = 6182567) B6182567
theorem B1221787 : Blo 1220928 1221787 := bstep (se 1 (by rfl) ⟨916340, by rfl⟩ : syracuseStep 1221787 = 1832681) B1832681
theorem B1221791 : Blo 1220928 1221791 := bstep (se 1 (by rfl) ⟨916343, by rfl⟩ : syracuseStep 1221791 = 1832687) B1832687
theorem B1222095 : Blo 1220928 1222095 := bstep (se 1 (by rfl) ⟨916571, by rfl⟩ : syracuseStep 1222095 = 1833143) B1833143
theorem B6186455 : Blo 1220928 6186455 := bstep (se 1 (by rfl) ⟨4639841, by rfl⟩ : syracuseStep 6186455 = 9279683) B9279683
theorem B1222127 : Blo 1220928 1222127 := bstep (se 1 (by rfl) ⟨916595, by rfl⟩ : syracuseStep 1222127 = 1833191) B1833191
theorem B1222375 : Blo 1220928 1222375 := bstep (se 1 (by rfl) ⟨916781, by rfl⟩ : syracuseStep 1222375 = 1833563) B1833563
theorem B1222471 : Blo 1220928 1222471 := bstep (se 1 (by rfl) ⟨916853, by rfl⟩ : syracuseStep 1222471 = 1833707) B1833707
theorem B13928273 : Blo 1220928 13928273 := bstep (se 2 (by rfl) ⟨5223102, by rfl⟩ : syracuseStep 13928273 = 10446205) B10446205
theorem B1222491 : Blo 1220928 1222491 := bstep (se 1 (by rfl) ⟨916868, by rfl⟩ : syracuseStep 1222491 = 1833737) B1833737
theorem B1304443 : Blo 1220928 1304443 := bstep (se 1 (by rfl) ⟨978332, by rfl⟩ : syracuseStep 1304443 = 1956665) B1956665
theorem B101673053 : Blo 1220928 101673053 := bstep (se 3 (by rfl) ⟨19063697, by rfl⟩ : syracuseStep 101673053 = 38127395) B38127395
theorem B4122953 : Blo 1220928 4122953 := bstep (se 2 (by rfl) ⟨1546107, by rfl⟩ : syracuseStep 4122953 = 3092215) B3092215
theorem B4123115 : Blo 1220928 4123115 := bstep (se 1 (by rfl) ⟨3092336, by rfl⟩ : syracuseStep 4123115 = 6184673) B6184673
theorem B14305895 : Blo 1220928 14305895 := bstep (se 1 (by rfl) ⟨10729421, by rfl⟩ : syracuseStep 14305895 = 21458843) B21458843
theorem B1739497 : Blo 1220928 1739497 := bstep (se 2 (by rfl) ⟨652311, by rfl⟩ : syracuseStep 1739497 = 1304623) B1304623
theorem B5294909 : Blo 1220928 5294909 := bstep (se 3 (by rfl) ⟨992795, by rfl⟩ : syracuseStep 5294909 = 1985591) B1985591
theorem B2321273 : Blo 1220928 2321273 := bstep (se 2 (by rfl) ⟨870477, by rfl⟩ : syracuseStep 2321273 = 1740955) B1740955
theorem B2976641 : Blo 1220928 2976641 := bstep (se 2 (by rfl) ⟨1116240, by rfl⟩ : syracuseStep 2976641 = 2232481) B2232481
theorem B6958169 : Blo 1220928 6958169 := bstep (se 2 (by rfl) ⟨2609313, by rfl⟩ : syracuseStep 6958169 = 5218627) B5218627
theorem B9907433 : Blo 1220928 9907433 := bstep (se 2 (by rfl) ⟨3715287, by rfl⟩ : syracuseStep 9907433 = 7430575) B7430575
theorem B3091871 : Blo 1220928 3091871 := bstep (se 1 (by rfl) ⟨2318903, by rfl⟩ : syracuseStep 3091871 = 4637807) B4637807
theorem B19811749 : Blo 1220928 19811749 := bstep (se 4 (by rfl) ⟨1857351, by rfl⟩ : syracuseStep 19811749 = 3714703) B3714703
theorem B2748257 : Blo 1220928 2748257 := bstep (se 2 (by rfl) ⟨1030596, by rfl⟩ : syracuseStep 2748257 = 2061193) B2061193
theorem B3477467 : Blo 1220928 3477467 := bstep (se 1 (by rfl) ⟨2608100, by rfl⟩ : syracuseStep 3477467 = 5216201) B5216201
theorem B4952159 : Blo 1220928 4952159 := bstep (se 1 (by rfl) ⟨3714119, by rfl⟩ : syracuseStep 4952159 = 7428239) B7428239
theorem B22605925 : Blo 1220928 22605925 := bstep (se 4 (by rfl) ⟨2119305, by rfl⟩ : syracuseStep 22605925 = 4238611) B4238611
theorem B11743643 : Blo 1220928 11743643 := bstep (se 1 (by rfl) ⟨8807732, by rfl⟩ : syracuseStep 11743643 = 17615465) B17615465
theorem B5222951 : Blo 1220928 5222951 := bstep (se 1 (by rfl) ⟨3917213, by rfl⟩ : syracuseStep 5222951 = 7834427) B7834427
theorem B1831643 : Blo 1220928 1831643 := bstep (se 1 (by rfl) ⟨1373732, by rfl⟩ : syracuseStep 1831643 = 2747465) B2747465
theorem B2749211 : Blo 1220928 2749211 := bstep (se 1 (by rfl) ⟨2061908, by rfl⟩ : syracuseStep 2749211 = 4123817) B4123817
theorem B23810921 : Blo 1220928 23810921 := bstep (se 2 (by rfl) ⟨8929095, by rfl⟩ : syracuseStep 23810921 = 17858191) B17858191
theorem B4125545 : Blo 1220928 4125545 := bstep (se 2 (by rfl) ⟨1547079, by rfl⟩ : syracuseStep 4125545 = 3094159) B3094159
theorem B2749409 : Blo 1220928 2749409 := bstep (se 2 (by rfl) ⟨1031028, by rfl⟩ : syracuseStep 2749409 = 2062057) B2062057
theorem B1831913 : Blo 1220928 1831913 := bstep (se 2 (by rfl) ⟨686967, by rfl⟩ : syracuseStep 1831913 = 1373935) B1373935
theorem B1832057 : Blo 1220928 1832057 := bstep (se 2 (by rfl) ⟨687021, by rfl⟩ : syracuseStep 1832057 = 1374043) B1374043
theorem B2749607 : Blo 1220928 2749607 := bstep (se 1 (by rfl) ⟨2062205, by rfl⟩ : syracuseStep 2749607 = 4124411) B4124411
theorem B3478697 : Blo 1220928 3478697 := bstep (se 2 (by rfl) ⟨1304511, by rfl⟩ : syracuseStep 3478697 = 2609023) B2609023
theorem B10434041 : Blo 1220928 10434041 := bstep (se 2 (by rfl) ⟨3912765, by rfl⟩ : syracuseStep 10434041 = 7825531) B7825531
theorem B13923899 : Blo 1220928 13923899 := bstep (se 1 (by rfl) ⟨10442924, by rfl⟩ : syracuseStep 13923899 = 20885849) B20885849
theorem B14112391 : Blo 1220928 14112391 := bstep (se 1 (by rfl) ⟨10584293, by rfl⟩ : syracuseStep 14112391 = 21168587) B21168587
theorem B1832585 : Blo 1220928 1832585 := bstep (se 2 (by rfl) ⟨687219, by rfl⟩ : syracuseStep 1832585 = 1374439) B1374439
theorem B9901723 : Blo 1220928 9901723 := bstep (se 1 (by rfl) ⟨7426292, by rfl⟩ : syracuseStep 9901723 = 14852585) B14852585
theorem B3970727 : Blo 1220928 3970727 := bstep (se 1 (by rfl) ⟨2978045, by rfl⟩ : syracuseStep 3970727 = 5956091) B5956091
theorem B1832795 : Blo 1220928 1832795 := bstep (se 1 (by rfl) ⟨1374596, by rfl⟩ : syracuseStep 1832795 = 2749193) B2749193
theorem B1374079 : Blo 1220928 1374079 := bstep (se 1 (by rfl) ⟨1030559, by rfl⟩ : syracuseStep 1374079 = 2061119) B2061119
theorem B1832831 : Blo 1220928 1832831 := bstep (se 1 (by rfl) ⟨1374623, by rfl⟩ : syracuseStep 1832831 = 2749247) B2749247
theorem B1955755 : Blo 1220928 1955755 := bstep (se 1 (by rfl) ⟨1466816, by rfl⟩ : syracuseStep 1955755 = 2933633) B2933633
theorem B1832927 : Blo 1220928 1832927 := bstep (se 1 (by rfl) ⟨1374695, by rfl⟩ : syracuseStep 1832927 = 2749391) B2749391
theorem B1832987 : Blo 1220928 1832987 := bstep (se 1 (by rfl) ⟨1374740, by rfl⟩ : syracuseStep 1832987 = 2749481) B2749481
theorem B6609023 : Blo 1220928 6609023 := bstep (se 1 (by rfl) ⟨4956767, by rfl⟩ : syracuseStep 6609023 = 9913535) B9913535
theorem B1833179 : Blo 1220928 1833179 := bstep (se 1 (by rfl) ⟨1374884, by rfl⟩ : syracuseStep 1833179 = 2749769) B2749769
theorem B2750777 : Blo 1220928 2750777 := bstep (se 2 (by rfl) ⟨1031541, by rfl⟩ : syracuseStep 2750777 = 2063083) B2063083
theorem B12540379 : Blo 1220928 12540379 := bstep (se 1 (by rfl) ⟨9405284, by rfl⟩ : syracuseStep 12540379 = 18810569) B18810569
theorem B1833449 : Blo 1220928 1833449 := bstep (se 2 (by rfl) ⟨687543, by rfl⟩ : syracuseStep 1833449 = 1375087) B1375087
theorem B3717623 : Blo 1220928 3717623 := bstep (se 1 (by rfl) ⟨2788217, by rfl⟩ : syracuseStep 3717623 = 5576435) B5576435
theorem B67762727 : Blo 1220928 67762727 := bstep (se 1 (by rfl) ⟨50822045, by rfl⟩ : syracuseStep 67762727 = 101644091) B101644091
theorem B3480155 : Blo 1220928 3480155 := bstep (se 1 (by rfl) ⟨2610116, by rfl⟩ : syracuseStep 3480155 = 5220233) B5220233
theorem B1956511 : Blo 1220928 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B8362739 : Blo 1220928 8362739 := bstep (se 1 (by rfl) ⟨6272054, by rfl⟩ : syracuseStep 8362739 = 12544109) B12544109
theorem B1833839 : Blo 1220928 1833839 := bstep (se 1 (by rfl) ⟨1375379, by rfl⟩ : syracuseStep 1833839 = 2750759) B2750759
theorem B3095435 : Blo 1220928 3095435 := bstep (se 1 (by rfl) ⟨2321576, by rfl⟩ : syracuseStep 3095435 = 4643153) B4643153
theorem B3480509 : Blo 1220928 3480509 := bstep (se 3 (by rfl) ⟨652595, by rfl⟩ : syracuseStep 3480509 = 1305191) B1305191
theorem B6962111 : Blo 1220928 6962111 := bstep (se 1 (by rfl) ⟨5221583, by rfl⟩ : syracuseStep 6962111 = 10443167) B10443167
theorem B2751515 : Blo 1220928 2751515 := bstep (se 1 (by rfl) ⟨2063636, by rfl⟩ : syracuseStep 2751515 = 4127273) B4127273
theorem B10443815 : Blo 1220928 10443815 := bstep (se 1 (by rfl) ⟨7832861, by rfl⟩ : syracuseStep 10443815 = 15665723) B15665723
theorem B1834079 : Blo 1220928 1834079 := bstep (se 1 (by rfl) ⟨1375559, by rfl⟩ : syracuseStep 1834079 = 2751119) B2751119
theorem B1834139 : Blo 1220928 1834139 := bstep (se 1 (by rfl) ⟨1375604, by rfl⟩ : syracuseStep 1834139 = 2751209) B2751209
theorem B2063515 : Blo 1220928 2063515 := bstep (se 1 (by rfl) ⟨1547636, by rfl⟩ : syracuseStep 2063515 = 3095273) B3095273
theorem B6266105 : Blo 1220928 6266105 := bstep (se 2 (by rfl) ⟨2349789, by rfl⟩ : syracuseStep 6266105 = 4699579) B4699579
theorem B9051401 : Blo 1220928 9051401 := bstep (se 2 (by rfl) ⟨3394275, by rfl⟩ : syracuseStep 9051401 = 6788551) B6788551
theorem B1834295 : Blo 1220928 1834295 := bstep (se 1 (by rfl) ⟨1375721, by rfl⟩ : syracuseStep 1834295 = 2751443) B2751443
theorem B13909319 : Blo 1220928 13909319 := bstep (se 1 (by rfl) ⟨10431989, by rfl⟩ : syracuseStep 13909319 = 20863979) B20863979
theorem B4636075 : Blo 1220928 4636075 := bstep (se 1 (by rfl) ⟨3477056, by rfl⟩ : syracuseStep 4636075 = 6954113) B6954113
theorem B7822817 : Blo 1220928 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B6954569 : Blo 1220928 6954569 := bstep (se 2 (by rfl) ⟨2607963, by rfl⟩ : syracuseStep 6954569 = 5215927) B5215927
theorem B25099865 : Blo 1220928 25099865 := bstep (se 2 (by rfl) ⟨9412449, by rfl⟩ : syracuseStep 25099865 = 18824899) B18824899
theorem B10723103 : Blo 1220928 10723103 := bstep (se 1 (by rfl) ⟨8042327, by rfl⟩ : syracuseStep 10723103 = 16084655) B16084655
theorem B3301439 : Blo 1220928 3301439 := bstep (se 1 (by rfl) ⟨2476079, by rfl⟩ : syracuseStep 3301439 = 4952159) B4952159
theorem B3481967 : Blo 1220928 3481967 := bstep (se 1 (by rfl) ⟨2611475, by rfl⟩ : syracuseStep 3481967 = 5222951) B5222951
theorem B4637047 : Blo 1220928 4637047 := bstep (se 1 (by rfl) ⟨3477785, by rfl⟩ : syracuseStep 4637047 = 6955571) B6955571
theorem B13926815 : Blo 1220928 13926815 := bstep (se 1 (by rfl) ⟨10445111, by rfl⟩ : syracuseStep 13926815 = 20890223) B20890223
theorem B1221095 : Blo 1220928 1221095 := bstep (se 1 (by rfl) ⟨915821, by rfl⟩ : syracuseStep 1221095 = 1831643) B1831643
theorem B16720505 : Blo 1220928 16720505 := bstep (se 2 (by rfl) ⟨6270189, by rfl⟩ : syracuseStep 16720505 = 12540379) B12540379
theorem B1221275 : Blo 1220928 1221275 := bstep (se 1 (by rfl) ⟨915956, by rfl⟩ : syracuseStep 1221275 = 1831913) B1831913
theorem B1221371 : Blo 1220928 1221371 := bstep (se 1 (by rfl) ⟨916028, by rfl⟩ : syracuseStep 1221371 = 1832057) B1832057
theorem B2319131 : Blo 1220928 2319131 := bstep (se 1 (by rfl) ⟨1739348, by rfl⟩ : syracuseStep 2319131 = 3478697) B3478697
theorem B31720385 : Blo 1220928 31720385 := bstep (se 2 (by rfl) ⟨11895144, by rfl⟩ : syracuseStep 31720385 = 23790289) B23790289
theorem B2319329 : Blo 1220928 2319329 := bstep (se 2 (by rfl) ⟨869748, by rfl⟩ : syracuseStep 2319329 = 1739497) B1739497
theorem B6956027 : Blo 1220928 6956027 := bstep (se 1 (by rfl) ⟨5217020, by rfl⟩ : syracuseStep 6956027 = 10434041) B10434041
theorem B9282599 : Blo 1220928 9282599 := bstep (se 1 (by rfl) ⟨6961949, by rfl⟩ : syracuseStep 9282599 = 13923899) B13923899
theorem B1221723 : Blo 1220928 1221723 := bstep (se 1 (by rfl) ⟨916292, by rfl⟩ : syracuseStep 1221723 = 1832585) B1832585
theorem B2647151 : Blo 1220928 2647151 := bstep (se 1 (by rfl) ⟨1985363, by rfl⟩ : syracuseStep 2647151 = 3970727) B3970727
theorem B1221863 : Blo 1220928 1221863 := bstep (se 1 (by rfl) ⟨916397, by rfl⟩ : syracuseStep 1221863 = 1832795) B1832795
theorem B1221887 : Blo 1220928 1221887 := bstep (se 1 (by rfl) ⟨916415, by rfl⟩ : syracuseStep 1221887 = 1832831) B1832831
theorem B9913661 : Blo 1220928 9913661 := bstep (se 3 (by rfl) ⟨1858811, by rfl⟩ : syracuseStep 9913661 = 3717623) B3717623
theorem B1221951 : Blo 1220928 1221951 := bstep (se 1 (by rfl) ⟨916463, by rfl⟩ : syracuseStep 1221951 = 1832927) B1832927
theorem B1221991 : Blo 1220928 1221991 := bstep (se 1 (by rfl) ⟨916493, by rfl⟩ : syracuseStep 1221991 = 1832987) B1832987
theorem B67782035 : Blo 1220928 67782035 := bstep (se 1 (by rfl) ⟨50836526, by rfl⟩ : syracuseStep 67782035 = 101673053) B101673053
theorem B1222119 : Blo 1220928 1222119 := bstep (se 1 (by rfl) ⟨916589, by rfl⟩ : syracuseStep 1222119 = 1833179) B1833179
theorem B1222299 : Blo 1220928 1222299 := bstep (se 1 (by rfl) ⟨916724, by rfl⟩ : syracuseStep 1222299 = 1833449) B1833449
theorem B2320103 : Blo 1220928 2320103 := bstep (se 1 (by rfl) ⟨1740077, by rfl⟩ : syracuseStep 2320103 = 3480155) B3480155
theorem B9537263 : Blo 1220928 9537263 := bstep (se 1 (by rfl) ⟨7152947, by rfl⟩ : syracuseStep 9537263 = 14305895) B14305895
theorem B1222559 : Blo 1220928 1222559 := bstep (se 1 (by rfl) ⟨916919, by rfl⟩ : syracuseStep 1222559 = 1833839) B1833839
theorem B1984427 : Blo 1220928 1984427 := bstep (se 1 (by rfl) ⟨1488320, by rfl⟩ : syracuseStep 1984427 = 2976641) B2976641
theorem B2320339 : Blo 1220928 2320339 := bstep (se 1 (by rfl) ⟨1740254, by rfl⟩ : syracuseStep 2320339 = 3480509) B3480509
theorem B6957029 : Blo 1220928 6957029 := bstep (se 4 (by rfl) ⟨652221, by rfl⟩ : syracuseStep 6957029 = 1304443) B1304443
theorem B4638779 : Blo 1220928 4638779 := bstep (se 1 (by rfl) ⟨3479084, by rfl⟩ : syracuseStep 4638779 = 6958169) B6958169
theorem B1222719 : Blo 1220928 1222719 := bstep (se 1 (by rfl) ⟨917039, by rfl⟩ : syracuseStep 1222719 = 1834079) B1834079
theorem B1222759 : Blo 1220928 1222759 := bstep (se 1 (by rfl) ⟨917069, by rfl⟩ : syracuseStep 1222759 = 1834139) B1834139
theorem B6604955 : Blo 1220928 6604955 := bstep (se 1 (by rfl) ⟨4953716, by rfl⟩ : syracuseStep 6604955 = 9907433) B9907433
theorem B1222863 : Blo 1220928 1222863 := bstep (se 1 (by rfl) ⟨917147, by rfl⟩ : syracuseStep 1222863 = 1834295) B1834295
theorem B10430693 : Blo 1220928 10430693 := bstep (se 4 (by rfl) ⟨977877, by rfl⟩ : syracuseStep 10430693 = 1955755) B1955755
theorem B30141233 : Blo 1220928 30141233 := bstep (se 2 (by rfl) ⟨11302962, by rfl⟩ : syracuseStep 30141233 = 22605925) B22605925
theorem B22588319 : Blo 1220928 22588319 := bstep (se 1 (by rfl) ⟨16941239, by rfl⟩ : syracuseStep 22588319 = 33882479) B33882479
theorem B42937289 : Blo 1220928 42937289 := bstep (se 2 (by rfl) ⟨16101483, by rfl⟩ : syracuseStep 42937289 = 32202967) B32202967
theorem B2747807 : Blo 1220928 2747807 := bstep (se 1 (by rfl) ⟨2060855, by rfl⟩ : syracuseStep 2747807 = 4121711) B4121711
theorem B2608681 : Blo 1220928 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B4124303 : Blo 1220928 4124303 := bstep (se 1 (by rfl) ⟨3093227, by rfl⟩ : syracuseStep 4124303 = 6186455) B6186455
theorem B9285515 : Blo 1220928 9285515 := bstep (se 1 (by rfl) ⟨6964136, by rfl⟩ : syracuseStep 9285515 = 13928273) B13928273
theorem B2748635 : Blo 1220928 2748635 := bstep (se 1 (by rfl) ⟨2061476, by rfl⟩ : syracuseStep 2748635 = 4122953) B4122953
theorem B2748743 : Blo 1220928 2748743 := bstep (se 1 (by rfl) ⟨2061557, by rfl⟩ : syracuseStep 2748743 = 4123115) B4123115
theorem B45175151 : Blo 1220928 45175151 := bstep (se 1 (by rfl) ⟨33881363, by rfl⟩ : syracuseStep 45175151 = 67762727) B67762727
theorem B5575159 : Blo 1220928 5575159 := bstep (se 1 (by rfl) ⟨4181369, by rfl⟩ : syracuseStep 5575159 = 8362739) B8362739
theorem B26415665 : Blo 1220928 26415665 := bstep (se 2 (by rfl) ⟨9905874, by rfl⟩ : syracuseStep 26415665 = 19811749) B19811749
theorem B6181433 : Blo 1220928 6181433 := bstep (se 2 (by rfl) ⟨2318037, by rfl⟩ : syracuseStep 6181433 = 4636075) B4636075
theorem B4641407 : Blo 1220928 4641407 := bstep (se 1 (by rfl) ⟨3481055, by rfl⟩ : syracuseStep 4641407 = 6962111) B6962111
theorem B6034267 : Blo 1220928 6034267 := bstep (se 1 (by rfl) ⟨4525700, by rfl⟩ : syracuseStep 6034267 = 9051401) B9051401
theorem B13202297 : Blo 1220928 13202297 := bstep (se 2 (by rfl) ⟨4950861, by rfl⟩ : syracuseStep 13202297 = 9901723) B9901723
theorem B2061247 : Blo 1220928 2061247 := bstep (se 1 (by rfl) ⟨1545935, by rfl⟩ : syracuseStep 2061247 = 3091871) B3091871
theorem B5215211 : Blo 1220928 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B16733243 : Blo 1220928 16733243 := bstep (se 1 (by rfl) ⟨12549932, by rfl⟩ : syracuseStep 16733243 = 25099865) B25099865
theorem B1832105 : Blo 1220928 1832105 := bstep (se 2 (by rfl) ⟨687039, by rfl⟩ : syracuseStep 1832105 = 1374079) B1374079
theorem B7148735 : Blo 1220928 7148735 := bstep (se 1 (by rfl) ⟨5361551, by rfl⟩ : syracuseStep 7148735 = 10723103) B10723103
theorem B1832171 : Blo 1220928 1832171 := bstep (se 1 (by rfl) ⟨1374128, by rfl⟩ : syracuseStep 1832171 = 2748257) B2748257
theorem B7829095 : Blo 1220928 7829095 := bstep (se 1 (by rfl) ⟨5871821, by rfl⟩ : syracuseStep 7829095 = 11743643) B11743643
theorem B1832807 : Blo 1220928 1832807 := bstep (se 1 (by rfl) ⟨1374605, by rfl⟩ : syracuseStep 1832807 = 2749211) B2749211
theorem B15873947 : Blo 1220928 15873947 := bstep (se 1 (by rfl) ⟨11905460, by rfl⟩ : syracuseStep 15873947 = 23810921) B23810921
theorem B2750363 : Blo 1220928 2750363 := bstep (se 1 (by rfl) ⟨2062772, by rfl⟩ : syracuseStep 2750363 = 4125545) B4125545
theorem B1832939 : Blo 1220928 1832939 := bstep (se 1 (by rfl) ⟨1374704, by rfl⟩ : syracuseStep 1832939 = 2749409) B2749409
theorem B2611271 : Blo 1220928 2611271 := bstep (se 1 (by rfl) ⟨1958453, by rfl⟩ : syracuseStep 2611271 = 3916907) B3916907
theorem B1833071 : Blo 1220928 1833071 := bstep (se 1 (by rfl) ⟨1374803, by rfl⟩ : syracuseStep 1833071 = 2749607) B2749607
theorem B4406015 : Blo 1220928 4406015 := bstep (se 1 (by rfl) ⟨3304511, by rfl⟩ : syracuseStep 4406015 = 6609023) B6609023
theorem B2751353 : Blo 1220928 2751353 := bstep (se 2 (by rfl) ⟨1031757, by rfl⟩ : syracuseStep 2751353 = 2063515) B2063515
theorem B1833851 : Blo 1220928 1833851 := bstep (se 1 (by rfl) ⟨1375388, by rfl⟩ : syracuseStep 1833851 = 2750777) B2750777
theorem B3529939 : Blo 1220928 3529939 := bstep (se 1 (by rfl) ⟨2647454, by rfl⟩ : syracuseStep 3529939 = 5294909) B5294909
theorem B1547515 : Blo 1220928 1547515 := bstep (se 1 (by rfl) ⟨1160636, by rfl⟩ : syracuseStep 1547515 = 2321273) B2321273
theorem B2063623 : Blo 1220928 2063623 := bstep (se 1 (by rfl) ⟨1547717, by rfl⟩ : syracuseStep 2063623 = 3095435) B3095435
theorem B1834343 : Blo 1220928 1834343 := bstep (se 1 (by rfl) ⟨1375757, by rfl⟩ : syracuseStep 1834343 = 2751515) B2751515
theorem B6962543 : Blo 1220928 6962543 := bstep (se 1 (by rfl) ⟨5221907, by rfl⟩ : syracuseStep 6962543 = 10443815) B10443815
theorem B4177403 : Blo 1220928 4177403 := bstep (se 1 (by rfl) ⟨3133052, by rfl⟩ : syracuseStep 4177403 = 6266105) B6266105
theorem B18816521 : Blo 1220928 18816521 := bstep (se 2 (by rfl) ⟨7056195, by rfl⟩ : syracuseStep 18816521 = 14112391) B14112391
theorem B9272879 : Blo 1220928 9272879 := bstep (se 1 (by rfl) ⟨6954659, by rfl⟩ : syracuseStep 9272879 = 13909319) B13909319
theorem B4636379 : Blo 1220928 4636379 := bstep (se 1 (by rfl) ⟨3477284, by rfl⟩ : syracuseStep 4636379 = 6954569) B6954569
theorem B2318311 : Blo 1220928 2318311 := bstep (se 1 (by rfl) ⟨1738733, by rfl⟩ : syracuseStep 2318311 = 3477467) B3477467
theorem B4120955 : Blo 1220928 4120955 := bstep (se 1 (by rfl) ⟨3090716, by rfl⟩ : syracuseStep 4120955 = 6181433) B6181433
theorem B4637351 : Blo 1220928 4637351 := bstep (se 1 (by rfl) ⟨3478013, by rfl⟩ : syracuseStep 4637351 = 6956027) B6956027
theorem B1221403 : Blo 1220928 1221403 := bstep (se 1 (by rfl) ⟨916052, by rfl⟩ : syracuseStep 1221403 = 1832105) B1832105
theorem B1221447 : Blo 1220928 1221447 := bstep (se 1 (by rfl) ⟨916085, by rfl⟩ : syracuseStep 1221447 = 1832171) B1832171
theorem B45188023 : Blo 1220928 45188023 := bstep (se 1 (by rfl) ⟨33891017, by rfl⟩ : syracuseStep 45188023 = 67782035) B67782035
theorem B8045689 : Blo 1220928 8045689 := bstep (se 2 (by rfl) ⟨3017133, by rfl⟩ : syracuseStep 8045689 = 6034267) B6034267
theorem B6358175 : Blo 1220928 6358175 := bstep (se 1 (by rfl) ⟨4768631, by rfl⟩ : syracuseStep 6358175 = 9537263) B9537263
theorem B1221871 : Blo 1220928 1221871 := bstep (se 1 (by rfl) ⟨916403, by rfl⟩ : syracuseStep 1221871 = 1832807) B1832807
theorem B4638019 : Blo 1220928 4638019 := bstep (se 1 (by rfl) ⟨3478514, by rfl⟩ : syracuseStep 4638019 = 6957029) B6957029
theorem B1221959 : Blo 1220928 1221959 := bstep (se 1 (by rfl) ⟨916469, by rfl⟩ : syracuseStep 1221959 = 1832939) B1832939
theorem B50177389 : Blo 1220928 50177389 := bstep (se 3 (by rfl) ⟨9408260, by rfl⟩ : syracuseStep 50177389 = 18816521) B18816521
theorem B1222047 : Blo 1220928 1222047 := bstep (se 1 (by rfl) ⟨916535, by rfl⟩ : syracuseStep 1222047 = 1833071) B1833071
theorem B1222567 : Blo 1220928 1222567 := bstep (se 1 (by rfl) ⟨916925, by rfl⟩ : syracuseStep 1222567 = 1833851) B1833851
theorem B6186941 : Blo 1220928 6186941 := bstep (se 3 (by rfl) ⟨1160051, by rfl⟩ : syracuseStep 6186941 = 2320103) B2320103
theorem B15058879 : Blo 1220928 15058879 := bstep (se 1 (by rfl) ⟨11294159, by rfl⟩ : syracuseStep 15058879 = 22588319) B22588319
theorem B28624859 : Blo 1220928 28624859 := bstep (se 1 (by rfl) ⟨21468644, by rfl⟩ : syracuseStep 28624859 = 42937289) B42937289
theorem B10438793 : Blo 1220928 10438793 := bstep (se 2 (by rfl) ⟨3914547, by rfl⟩ : syracuseStep 10438793 = 7829095) B7829095
theorem B1222895 : Blo 1220928 1222895 := bstep (se 1 (by rfl) ⟨917171, by rfl⟩ : syracuseStep 1222895 = 1834343) B1834343
theorem B3090919 : Blo 1220928 3090919 := bstep (se 1 (by rfl) ⟨2318189, by rfl⟩ : syracuseStep 3090919 = 4636379) B4636379
theorem B3091081 : Blo 1220928 3091081 := bstep (se 2 (by rfl) ⟨1159155, by rfl⟩ : syracuseStep 3091081 = 2318311) B2318311
theorem B30116767 : Blo 1220928 30116767 := bstep (se 1 (by rfl) ⟨22587575, by rfl⟩ : syracuseStep 30116767 = 45175151) B45175151
theorem B2321311 : Blo 1220928 2321311 := bstep (se 1 (by rfl) ⟨1740983, by rfl⟩ : syracuseStep 2321311 = 3481967) B3481967
theorem B9284543 : Blo 1220928 9284543 := bstep (se 1 (by rfl) ⟨6963407, by rfl⟩ : syracuseStep 9284543 = 13926815) B13926815
theorem B8801531 : Blo 1220928 8801531 := bstep (se 1 (by rfl) ⟨6601148, by rfl⟩ : syracuseStep 8801531 = 13202297) B13202297
theorem B21146923 : Blo 1220928 21146923 := bstep (se 1 (by rfl) ⟨15860192, by rfl⟩ : syracuseStep 21146923 = 31720385) B31720385
theorem B3476807 : Blo 1220928 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B7433545 : Blo 1220928 7433545 := bstep (se 2 (by rfl) ⟨2787579, by rfl⟩ : syracuseStep 7433545 = 5575159) B5575159
theorem B6188399 : Blo 1220928 6188399 := bstep (se 1 (by rfl) ⟨4641299, by rfl⟩ : syracuseStep 6188399 = 9282599) B9282599
theorem B1764767 : Blo 1220928 1764767 := bstep (se 1 (by rfl) ⟨1323575, by rfl⟩ : syracuseStep 1764767 = 2647151) B2647151
theorem B2748329 : Blo 1220928 2748329 := bstep (se 2 (by rfl) ⟨1030623, by rfl⟩ : syracuseStep 2748329 = 2061247) B2061247
theorem B1322951 : Blo 1220928 1322951 := bstep (se 1 (by rfl) ⟨992213, by rfl⟩ : syracuseStep 1322951 = 1984427) B1984427
theorem B3092519 : Blo 1220928 3092519 := bstep (se 1 (by rfl) ⟨2319389, by rfl⟩ : syracuseStep 3092519 = 4638779) B4638779
theorem B1740847 : Blo 1220928 1740847 := bstep (se 1 (by rfl) ⟨1305635, by rfl⟩ : syracuseStep 1740847 = 2611271) B2611271
theorem B4403303 : Blo 1220928 4403303 := bstep (se 1 (by rfl) ⟨3302477, by rfl⟩ : syracuseStep 4403303 = 6604955) B6604955
theorem B4706585 : Blo 1220928 4706585 := bstep (se 2 (by rfl) ⟨1764969, by rfl⟩ : syracuseStep 4706585 = 3529939) B3529939
theorem B2937343 : Blo 1220928 2937343 := bstep (se 1 (by rfl) ⟨2203007, by rfl⟩ : syracuseStep 2937343 = 4406015) B4406015
theorem B3478241 : Blo 1220928 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B4641695 : Blo 1220928 4641695 := bstep (se 1 (by rfl) ⟨3481271, by rfl⟩ : syracuseStep 4641695 = 6962543) B6962543
theorem B1831871 : Blo 1220928 1831871 := bstep (se 1 (by rfl) ⟨1373903, by rfl⟩ : syracuseStep 1831871 = 2747807) B2747807
theorem B6181919 : Blo 1220928 6181919 := bstep (se 1 (by rfl) ⟨4636439, by rfl⟩ : syracuseStep 6181919 = 9272879) B9272879
theorem B2749535 : Blo 1220928 2749535 := bstep (se 1 (by rfl) ⟨2062151, by rfl⟩ : syracuseStep 2749535 = 4124303) B4124303
theorem B6190343 : Blo 1220928 6190343 := bstep (se 1 (by rfl) ⟨4642757, by rfl⟩ : syracuseStep 6190343 = 9285515) B9285515
theorem B3093785 : Blo 1220928 3093785 := bstep (se 2 (by rfl) ⟨1160169, by rfl⟩ : syracuseStep 3093785 = 2320339) B2320339
theorem B1832423 : Blo 1220928 1832423 := bstep (se 1 (by rfl) ⟨1374317, by rfl⟩ : syracuseStep 1832423 = 2748635) B2748635
theorem B8803837 : Blo 1220928 8803837 := bstep (se 3 (by rfl) ⟨1650719, by rfl⟩ : syracuseStep 8803837 = 3301439) B3301439
theorem B1832495 : Blo 1220928 1832495 := bstep (se 1 (by rfl) ⟨1374371, by rfl⟩ : syracuseStep 1832495 = 2748743) B2748743
theorem B17610443 : Blo 1220928 17610443 := bstep (se 1 (by rfl) ⟨13207832, by rfl⟩ : syracuseStep 17610443 = 26415665) B26415665
theorem B11147003 : Blo 1220928 11147003 := bstep (se 1 (by rfl) ⟨8360252, by rfl⟩ : syracuseStep 11147003 = 16720505) B16720505
theorem B3094271 : Blo 1220928 3094271 := bstep (se 1 (by rfl) ⟨2320703, by rfl⟩ : syracuseStep 3094271 = 4641407) B4641407
theorem B6182729 : Blo 1220928 6182729 := bstep (se 2 (by rfl) ⟨2318523, by rfl⟩ : syracuseStep 6182729 = 4637047) B4637047
theorem B1546219 : Blo 1220928 1546219 := bstep (se 1 (by rfl) ⟨1159664, by rfl⟩ : syracuseStep 1546219 = 2319329) B2319329
theorem B11155495 : Blo 1220928 11155495 := bstep (se 1 (by rfl) ⟨8366621, by rfl⟩ : syracuseStep 11155495 = 16733243) B16733243
theorem B4765823 : Blo 1220928 4765823 := bstep (se 1 (by rfl) ⟨3574367, by rfl⟩ : syracuseStep 4765823 = 7148735) B7148735
theorem B6609107 : Blo 1220928 6609107 := bstep (se 1 (by rfl) ⟨4956830, by rfl⟩ : syracuseStep 6609107 = 9913661) B9913661
theorem B10582631 : Blo 1220928 10582631 := bstep (se 1 (by rfl) ⟨7936973, by rfl⟩ : syracuseStep 10582631 = 15873947) B15873947
theorem B1833575 : Blo 1220928 1833575 := bstep (se 1 (by rfl) ⟨1375181, by rfl⟩ : syracuseStep 1833575 = 2750363) B2750363
theorem B6953795 : Blo 1220928 6953795 := bstep (se 1 (by rfl) ⟨5215346, by rfl⟩ : syracuseStep 6953795 = 10430693) B10430693
theorem B2063353 : Blo 1220928 2063353 := bstep (se 2 (by rfl) ⟨773757, by rfl⟩ : syracuseStep 2063353 = 1547515) B1547515
theorem B2751497 : Blo 1220928 2751497 := bstep (se 2 (by rfl) ⟨1031811, by rfl⟩ : syracuseStep 2751497 = 2063623) B2063623
theorem B20094155 : Blo 1220928 20094155 := bstep (se 1 (by rfl) ⟨15070616, by rfl⟩ : syracuseStep 20094155 = 30141233) B30141233
theorem B1834235 : Blo 1220928 1834235 := bstep (se 1 (by rfl) ⟨1375676, by rfl⟩ : syracuseStep 1834235 = 2751353) B2751353
theorem B6184349 : Blo 1220928 6184349 := bstep (se 3 (by rfl) ⟨1159565, by rfl⟩ : syracuseStep 6184349 = 2319131) B2319131
theorem B2784935 : Blo 1220928 2784935 := bstep (se 1 (by rfl) ⟨2088701, by rfl⟩ : syracuseStep 2784935 = 4177403) B4177403
theorem B3137723 : Blo 1220928 3137723 := bstep (se 1 (by rfl) ⟨2353292, by rfl⟩ : syracuseStep 3137723 = 4706585) B4706585
theorem B1221247 : Blo 1220928 1221247 := bstep (se 1 (by rfl) ⟨915935, by rfl⟩ : syracuseStep 1221247 = 1831871) B1831871
theorem B4121225 : Blo 1220928 4121225 := bstep (se 2 (by rfl) ⟨1545459, by rfl⟩ : syracuseStep 4121225 = 3090919) B3090919
theorem B3916457 : Blo 1220928 3916457 := bstep (se 2 (by rfl) ⟨1468671, by rfl⟩ : syracuseStep 3916457 = 2937343) B2937343
theorem B4121279 : Blo 1220928 4121279 := bstep (se 1 (by rfl) ⟨3090959, by rfl⟩ : syracuseStep 4121279 = 6181919) B6181919
theorem B4121441 : Blo 1220928 4121441 := bstep (se 2 (by rfl) ⟨1545540, by rfl⟩ : syracuseStep 4121441 = 3091081) B3091081
theorem B1221615 : Blo 1220928 1221615 := bstep (se 1 (by rfl) ⟨916211, by rfl⟩ : syracuseStep 1221615 = 1832423) B1832423
theorem B1221663 : Blo 1220928 1221663 := bstep (se 1 (by rfl) ⟨916247, by rfl⟩ : syracuseStep 1221663 = 1832495) B1832495
theorem B11740295 : Blo 1220928 11740295 := bstep (se 1 (by rfl) ⟨8805221, by rfl⟩ : syracuseStep 11740295 = 17610443) B17610443
theorem B7431335 : Blo 1220928 7431335 := bstep (se 1 (by rfl) ⟨5573501, by rfl⟩ : syracuseStep 7431335 = 11147003) B11147003
theorem B4121819 : Blo 1220928 4121819 := bstep (se 1 (by rfl) ⟨3091364, by rfl⟩ : syracuseStep 4121819 = 6182729) B6182729
theorem B7055087 : Blo 1220928 7055087 := bstep (se 1 (by rfl) ⟨5291315, by rfl⟩ : syracuseStep 7055087 = 10582631) B10582631
theorem B1222383 : Blo 1220928 1222383 := bstep (se 1 (by rfl) ⟨916787, by rfl⟩ : syracuseStep 1222383 = 1833575) B1833575
theorem B9275309 : Blo 1220928 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B13396103 : Blo 1220928 13396103 := bstep (se 1 (by rfl) ⟨10047077, by rfl⟩ : syracuseStep 13396103 = 20094155) B20094155
theorem B5867687 : Blo 1220928 5867687 := bstep (se 1 (by rfl) ⟨4400765, by rfl⟩ : syracuseStep 5867687 = 8801531) B8801531
theorem B1222823 : Blo 1220928 1222823 := bstep (se 1 (by rfl) ⟨917117, by rfl⟩ : syracuseStep 1222823 = 1834235) B1834235
theorem B4122899 : Blo 1220928 4122899 := bstep (se 1 (by rfl) ⟨3092174, by rfl⟩ : syracuseStep 4122899 = 6184349) B6184349
theorem B2321129 : Blo 1220928 2321129 := bstep (se 2 (by rfl) ⟨870423, by rfl⟩ : syracuseStep 2321129 = 1740847) B1740847
theorem B2935535 : Blo 1220928 2935535 := bstep (se 1 (by rfl) ⟨2201651, by rfl⟩ : syracuseStep 2935535 = 4403303) B4403303
theorem B2747303 : Blo 1220928 2747303 := bstep (se 1 (by rfl) ⟨2060477, by rfl⟩ : syracuseStep 2747303 = 4120955) B4120955
theorem B3091567 : Blo 1220928 3091567 := bstep (se 1 (by rfl) ⟨2318675, by rfl⟩ : syracuseStep 3091567 = 4637351) B4637351
theorem B4238783 : Blo 1220928 4238783 := bstep (se 1 (by rfl) ⟨3179087, by rfl⟩ : syracuseStep 4238783 = 6358175) B6358175
theorem B4706045 : Blo 1220928 4706045 := bstep (se 3 (by rfl) ⟨882383, by rfl⟩ : syracuseStep 4706045 = 1764767) B1764767
theorem B4124627 : Blo 1220928 4124627 := bstep (se 1 (by rfl) ⟨3093470, by rfl⟩ : syracuseStep 4124627 = 6186941) B6186941
theorem B19083239 : Blo 1220928 19083239 := bstep (se 1 (by rfl) ⟨14312429, by rfl⟩ : syracuseStep 19083239 = 28624859) B28624859
theorem B6959195 : Blo 1220928 6959195 := bstep (se 1 (by rfl) ⟨5219396, by rfl⟩ : syracuseStep 6959195 = 10438793) B10438793
theorem B10727585 : Blo 1220928 10727585 := bstep (se 2 (by rfl) ⟨4022844, by rfl⟩ : syracuseStep 10727585 = 8045689) B8045689
theorem B112783589 : Blo 1220928 112783589 := bstep (se 4 (by rfl) ⟨10573461, by rfl⟩ : syracuseStep 112783589 = 21146923) B21146923
theorem B6189695 : Blo 1220928 6189695 := bstep (se 1 (by rfl) ⟨4642271, by rfl⟩ : syracuseStep 6189695 = 9284543) B9284543
theorem B4125599 : Blo 1220928 4125599 := bstep (se 1 (by rfl) ⟨3094199, by rfl⟩ : syracuseStep 4125599 = 6188399) B6188399
theorem B1856623 : Blo 1220928 1856623 := bstep (se 1 (by rfl) ⟨1392467, by rfl⟩ : syracuseStep 1856623 = 2784935) B2784935
theorem B3527869 : Blo 1220928 3527869 := bstep (se 3 (by rfl) ⟨661475, by rfl⟩ : syracuseStep 3527869 = 1322951) B1322951
theorem B1832219 : Blo 1220928 1832219 := bstep (se 1 (by rfl) ⟨1374164, by rfl⟩ : syracuseStep 1832219 = 2748329) B2748329
theorem B2061625 : Blo 1220928 2061625 := bstep (se 2 (by rfl) ⟨773109, by rfl⟩ : syracuseStep 2061625 = 1546219) B1546219
theorem B2061679 : Blo 1220928 2061679 := bstep (se 1 (by rfl) ⟨1546259, by rfl⟩ : syracuseStep 2061679 = 3092519) B3092519
theorem B14873993 : Blo 1220928 14873993 := bstep (se 2 (by rfl) ⟨5577747, by rfl⟩ : syracuseStep 14873993 = 11155495) B11155495
theorem B3094463 : Blo 1220928 3094463 := bstep (se 1 (by rfl) ⟨2320847, by rfl⟩ : syracuseStep 3094463 = 4641695) B4641695
theorem B1833023 : Blo 1220928 1833023 := bstep (se 1 (by rfl) ⟨1374767, by rfl⟩ : syracuseStep 1833023 = 2749535) B2749535
theorem B4126895 : Blo 1220928 4126895 := bstep (se 1 (by rfl) ⟨3095171, by rfl⟩ : syracuseStep 4126895 = 6190343) B6190343
theorem B2062523 : Blo 1220928 2062523 := bstep (se 1 (by rfl) ⟨1546892, by rfl⟩ : syracuseStep 2062523 = 3093785) B3093785
theorem B2062847 : Blo 1220928 2062847 := bstep (se 1 (by rfl) ⟨1547135, by rfl⟩ : syracuseStep 2062847 = 3094271) B3094271
theorem B40155689 : Blo 1220928 40155689 := bstep (se 2 (by rfl) ⟨15058383, by rfl⟩ : syracuseStep 40155689 = 30116767) B30116767
theorem B3095081 : Blo 1220928 3095081 := bstep (se 2 (by rfl) ⟨1160655, by rfl⟩ : syracuseStep 3095081 = 2321311) B2321311
theorem B60250697 : Blo 1220928 60250697 := bstep (se 2 (by rfl) ⟨22594011, by rfl⟩ : syracuseStep 60250697 = 45188023) B45188023
theorem B2751137 : Blo 1220928 2751137 := bstep (se 2 (by rfl) ⟨1031676, by rfl⟩ : syracuseStep 2751137 = 2063353) B2063353
theorem B3177215 : Blo 1220928 3177215 := bstep (se 1 (by rfl) ⟨2382911, by rfl⟩ : syracuseStep 3177215 = 4765823) B4765823
theorem B4406071 : Blo 1220928 4406071 := bstep (se 1 (by rfl) ⟨3304553, by rfl⟩ : syracuseStep 4406071 = 6609107) B6609107
theorem B6184025 : Blo 1220928 6184025 := bstep (se 2 (by rfl) ⟨2319009, by rfl⟩ : syracuseStep 6184025 = 4638019) B4638019
theorem B9911393 : Blo 1220928 9911393 := bstep (se 2 (by rfl) ⟨3716772, by rfl⟩ : syracuseStep 9911393 = 7433545) B7433545
theorem B66903185 : Blo 1220928 66903185 := bstep (se 2 (by rfl) ⟨25088694, by rfl⟩ : syracuseStep 66903185 = 50177389) B50177389
theorem B4635863 : Blo 1220928 4635863 := bstep (se 1 (by rfl) ⟨3476897, by rfl⟩ : syracuseStep 4635863 = 6953795) B6953795
theorem B11738449 : Blo 1220928 11738449 := bstep (se 2 (by rfl) ⟨4401918, by rfl⟩ : syracuseStep 11738449 = 8803837) B8803837
theorem B1834331 : Blo 1220928 1834331 := bstep (se 1 (by rfl) ⟨1375748, by rfl⟩ : syracuseStep 1834331 = 2751497) B2751497
theorem B2317871 : Blo 1220928 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B80314021 : Blo 1220928 80314021 := bstep (se 4 (by rfl) ⟨7529439, by rfl⟩ : syracuseStep 80314021 = 15058879) B15058879
theorem B7151723 : Blo 1220928 7151723 := bstep (se 1 (by rfl) ⟨5363792, by rfl⟩ : syracuseStep 7151723 = 10727585) B10727585
theorem B15647165 : Blo 1220928 15647165 := bstep (se 3 (by rfl) ⟨2933843, by rfl⟩ : syracuseStep 15647165 = 5867687) B5867687
theorem B1221479 : Blo 1220928 1221479 := bstep (se 1 (by rfl) ⟨916109, by rfl⟩ : syracuseStep 1221479 = 1832219) B1832219
theorem B5874761 : Blo 1220928 5874761 := bstep (se 2 (by rfl) ⟨2203035, by rfl⟩ : syracuseStep 5874761 = 4406071) B4406071
theorem B1222015 : Blo 1220928 1222015 := bstep (se 1 (by rfl) ⟨916511, by rfl⟩ : syracuseStep 1222015 = 1833023) B1833023
theorem B8930735 : Blo 1220928 8930735 := bstep (se 1 (by rfl) ⟨6698051, by rfl⟩ : syracuseStep 8930735 = 13396103) B13396103
theorem B2475497 : Blo 1220928 2475497 := bstep (se 2 (by rfl) ⟨928311, by rfl⟩ : syracuseStep 2475497 = 1856623) B1856623
theorem B4122089 : Blo 1220928 4122089 := bstep (se 2 (by rfl) ⟨1545783, by rfl⟩ : syracuseStep 4122089 = 3091567) B3091567
theorem B4703825 : Blo 1220928 4703825 := bstep (se 2 (by rfl) ⟨1763934, by rfl⟩ : syracuseStep 4703825 = 3527869) B3527869
theorem B40167131 : Blo 1220928 40167131 := bstep (se 1 (by rfl) ⟨30125348, by rfl⟩ : syracuseStep 40167131 = 60250697) B60250697
theorem B4122683 : Blo 1220928 4122683 := bstep (se 1 (by rfl) ⟨3092012, by rfl⟩ : syracuseStep 4122683 = 6184025) B6184025
theorem B3090575 : Blo 1220928 3090575 := bstep (se 1 (by rfl) ⟨2317931, by rfl⟩ : syracuseStep 3090575 = 4635863) B4635863
theorem B1222887 : Blo 1220928 1222887 := bstep (se 1 (by rfl) ⟨917165, by rfl⟩ : syracuseStep 1222887 = 1834331) B1834331
theorem B4639463 : Blo 1220928 4639463 := bstep (se 1 (by rfl) ⟨3479597, by rfl⟩ : syracuseStep 4639463 = 6959195) B6959195
theorem B2091815 : Blo 1220928 2091815 := bstep (se 1 (by rfl) ⟨1568861, by rfl⟩ : syracuseStep 2091815 = 3137723) B3137723
theorem B75189059 : Blo 1220928 75189059 := bstep (se 1 (by rfl) ⟨56391794, by rfl⟩ : syracuseStep 75189059 = 112783589) B112783589
theorem B2747483 : Blo 1220928 2747483 := bstep (se 1 (by rfl) ⟨2060612, by rfl⟩ : syracuseStep 2747483 = 4121225) B4121225
theorem B2747519 : Blo 1220928 2747519 := bstep (se 1 (by rfl) ⟨2060639, by rfl⟩ : syracuseStep 2747519 = 4121279) B4121279
theorem B2747627 : Blo 1220928 2747627 := bstep (se 1 (by rfl) ⟨2060720, by rfl⟩ : syracuseStep 2747627 = 4121441) B4121441
theorem B7826863 : Blo 1220928 7826863 := bstep (se 1 (by rfl) ⟨5870147, by rfl⟩ : syracuseStep 7826863 = 11740295) B11740295
theorem B2747879 : Blo 1220928 2747879 := bstep (se 1 (by rfl) ⟨2060909, by rfl⟩ : syracuseStep 2747879 = 4121819) B4121819
theorem B9915995 : Blo 1220928 9915995 := bstep (se 1 (by rfl) ⟨7436996, by rfl⟩ : syracuseStep 9915995 = 14873993) B14873993
theorem B2748599 : Blo 1220928 2748599 := bstep (se 1 (by rfl) ⟨2061449, by rfl⟩ : syracuseStep 2748599 = 4122899) B4122899
theorem B2748833 : Blo 1220928 2748833 := bstep (se 2 (by rfl) ⟨1030812, by rfl⟩ : syracuseStep 2748833 = 2061625) B2061625
theorem B15651265 : Blo 1220928 15651265 := bstep (se 2 (by rfl) ⟨5869224, by rfl⟩ : syracuseStep 15651265 = 11738449) B11738449
theorem B2748905 : Blo 1220928 2748905 := bstep (se 2 (by rfl) ⟨1030839, by rfl⟩ : syracuseStep 2748905 = 2061679) B2061679
theorem B2118143 : Blo 1220928 2118143 := bstep (se 1 (by rfl) ⟨1588607, by rfl⟩ : syracuseStep 2118143 = 3177215) B3177215
theorem B1831535 : Blo 1220928 1831535 := bstep (se 1 (by rfl) ⟨1373651, by rfl⟩ : syracuseStep 1831535 = 2747303) B2747303
theorem B7828093 : Blo 1220928 7828093 := bstep (se 3 (by rfl) ⟨1467767, by rfl⟩ : syracuseStep 7828093 = 2935535) B2935535
theorem B18813565 : Blo 1220928 18813565 := bstep (se 3 (by rfl) ⟨3527543, by rfl⟩ : syracuseStep 18813565 = 7055087) B7055087
theorem B6607595 : Blo 1220928 6607595 := bstep (se 1 (by rfl) ⟨4955696, by rfl⟩ : syracuseStep 6607595 = 9911393) B9911393
theorem B44602123 : Blo 1220928 44602123 := bstep (se 1 (by rfl) ⟨33451592, by rfl⟩ : syracuseStep 44602123 = 66903185) B66903185
theorem B1545247 : Blo 1220928 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B2749751 : Blo 1220928 2749751 := bstep (se 1 (by rfl) ⟨2062313, by rfl⟩ : syracuseStep 2749751 = 4124627) B4124627
theorem B4126463 : Blo 1220928 4126463 := bstep (se 1 (by rfl) ⟨3094847, by rfl⟩ : syracuseStep 4126463 = 6189695) B6189695
theorem B2610971 : Blo 1220928 2610971 := bstep (se 1 (by rfl) ⟨1958228, by rfl⟩ : syracuseStep 2610971 = 3916457) B3916457
theorem B2750399 : Blo 1220928 2750399 := bstep (se 1 (by rfl) ⟨2062799, by rfl⟩ : syracuseStep 2750399 = 4125599) B4125599
theorem B4954223 : Blo 1220928 4954223 := bstep (se 1 (by rfl) ⟨3715667, by rfl⟩ : syracuseStep 4954223 = 7431335) B7431335
theorem B428341445 : Blo 1220928 428341445 := bstep (se 4 (by rfl) ⟨40157010, by rfl⟩ : syracuseStep 428341445 = 80314021) B80314021
theorem B6183539 : Blo 1220928 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B2062975 : Blo 1220928 2062975 := bstep (se 1 (by rfl) ⟨1547231, by rfl⟩ : syracuseStep 2062975 = 3094463) B3094463
theorem B2751263 : Blo 1220928 2751263 := bstep (se 1 (by rfl) ⟨2063447, by rfl⟩ : syracuseStep 2751263 = 4126895) B4126895
theorem B1375015 : Blo 1220928 1375015 := bstep (se 1 (by rfl) ⟨1031261, by rfl⟩ : syracuseStep 1375015 = 2062523) B2062523
theorem B1375231 : Blo 1220928 1375231 := bstep (se 1 (by rfl) ⟨1031423, by rfl⟩ : syracuseStep 1375231 = 2062847) B2062847
theorem B26770459 : Blo 1220928 26770459 := bstep (se 1 (by rfl) ⟨20077844, by rfl⟩ : syracuseStep 26770459 = 40155689) B40155689
theorem B2063387 : Blo 1220928 2063387 := bstep (se 1 (by rfl) ⟨1547540, by rfl⟩ : syracuseStep 2063387 = 3095081) B3095081
theorem B1834091 : Blo 1220928 1834091 := bstep (se 1 (by rfl) ⟨1375568, by rfl⟩ : syracuseStep 1834091 = 2751137) B2751137
theorem B1547419 : Blo 1220928 1547419 := bstep (se 1 (by rfl) ⟨1160564, by rfl⟩ : syracuseStep 1547419 = 2321129) B2321129
theorem B2825855 : Blo 1220928 2825855 := bstep (se 1 (by rfl) ⟨2119391, by rfl⟩ : syracuseStep 2825855 = 4238783) B4238783
theorem B3137363 : Blo 1220928 3137363 := bstep (se 1 (by rfl) ⟨2353022, by rfl⟩ : syracuseStep 3137363 = 4706045) B4706045
theorem B12722159 : Blo 1220928 12722159 := bstep (se 1 (by rfl) ⟨9541619, by rfl⟩ : syracuseStep 12722159 = 19083239) B19083239
theorem B4767815 : Blo 1220928 4767815 := bstep (se 1 (by rfl) ⟨3575861, by rfl⟩ : syracuseStep 4767815 = 7151723) B7151723
theorem B1221023 : Blo 1220928 1221023 := bstep (se 1 (by rfl) ⟨915767, by rfl⟩ : syracuseStep 1221023 = 1831535) B1831535
theorem B3916507 : Blo 1220928 3916507 := bstep (se 1 (by rfl) ⟨2937380, by rfl⟩ : syracuseStep 3916507 = 5874761) B5874761
theorem B10437457 : Blo 1220928 10437457 := bstep (se 2 (by rfl) ⟨3914046, by rfl⟩ : syracuseStep 10437457 = 7828093) B7828093
theorem B35693945 : Blo 1220928 35693945 := bstep (se 2 (by rfl) ⟨13385229, by rfl⟩ : syracuseStep 35693945 = 26770459) B26770459
theorem B3302815 : Blo 1220928 3302815 := bstep (se 1 (by rfl) ⟨2477111, by rfl⟩ : syracuseStep 3302815 = 4954223) B4954223
theorem B4122359 : Blo 1220928 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B1394543 : Blo 1220928 1394543 := bstep (se 1 (by rfl) ⟨1045907, by rfl⟩ : syracuseStep 1394543 = 2091815) B2091815
theorem B107112349 : Blo 1220928 107112349 := bstep (se 3 (by rfl) ⟨20083565, by rfl⟩ : syracuseStep 107112349 = 40167131) B40167131
theorem B1222727 : Blo 1220928 1222727 := bstep (se 1 (by rfl) ⟨917045, by rfl⟩ : syracuseStep 1222727 = 1834091) B1834091
theorem B2091575 : Blo 1220928 2091575 := bstep (se 1 (by rfl) ⟨1568681, by rfl⟩ : syracuseStep 2091575 = 3137363) B3137363
theorem B8481439 : Blo 1220928 8481439 := bstep (se 1 (by rfl) ⟨6361079, by rfl⟩ : syracuseStep 8481439 = 12722159) B12722159
theorem B10431443 : Blo 1220928 10431443 := bstep (se 1 (by rfl) ⟨7823582, by rfl⟩ : syracuseStep 10431443 = 15647165) B15647165
theorem B1412095 : Blo 1220928 1412095 := bstep (se 1 (by rfl) ⟨1059071, by rfl⟩ : syracuseStep 1412095 = 2118143) B2118143
theorem B20868353 : Blo 1220928 20868353 := bstep (se 2 (by rfl) ⟨7825632, by rfl⟩ : syracuseStep 20868353 = 15651265) B15651265
theorem B100339013 : Blo 1220928 100339013 := bstep (se 4 (by rfl) ⟨9406782, by rfl⟩ : syracuseStep 100339013 = 18813565) B18813565
theorem B1650331 : Blo 1220928 1650331 := bstep (se 1 (by rfl) ⟨1237748, by rfl⟩ : syracuseStep 1650331 = 2475497) B2475497
theorem B2748059 : Blo 1220928 2748059 := bstep (se 1 (by rfl) ⟨2061044, by rfl⟩ : syracuseStep 2748059 = 4122089) B4122089
theorem B59469497 : Blo 1220928 59469497 := bstep (se 2 (by rfl) ⟨22301061, by rfl⟩ : syracuseStep 59469497 = 44602123) B44602123
theorem B1740647 : Blo 1220928 1740647 := bstep (se 1 (by rfl) ⟨1305485, by rfl⟩ : syracuseStep 1740647 = 2610971) B2610971
theorem B2748455 : Blo 1220928 2748455 := bstep (se 1 (by rfl) ⟨2061341, by rfl⟩ : syracuseStep 2748455 = 4122683) B4122683
theorem B2060329 : Blo 1220928 2060329 := bstep (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) B1545247
theorem B2060383 : Blo 1220928 2060383 := bstep (se 1 (by rfl) ⟨1545287, by rfl⟩ : syracuseStep 2060383 = 3090575) B3090575
theorem B285560963 : Blo 1220928 285560963 := bstep (se 1 (by rfl) ⟨214170722, by rfl⟩ : syracuseStep 285560963 = 428341445) B428341445
theorem B3092975 : Blo 1220928 3092975 := bstep (se 1 (by rfl) ⟨2319731, by rfl⟩ : syracuseStep 3092975 = 4639463) B4639463
theorem B1831655 : Blo 1220928 1831655 := bstep (se 1 (by rfl) ⟨1373741, by rfl⟩ : syracuseStep 1831655 = 2747483) B2747483
theorem B1831679 : Blo 1220928 1831679 := bstep (se 1 (by rfl) ⟨1373759, by rfl⟩ : syracuseStep 1831679 = 2747519) B2747519
theorem B1831751 : Blo 1220928 1831751 := bstep (se 1 (by rfl) ⟨1373813, by rfl⟩ : syracuseStep 1831751 = 2747627) B2747627
theorem B1831919 : Blo 1220928 1831919 := bstep (se 1 (by rfl) ⟨1373939, by rfl⟩ : syracuseStep 1831919 = 2747879) B2747879
theorem B1832399 : Blo 1220928 1832399 := bstep (se 1 (by rfl) ⟨1374299, by rfl⟩ : syracuseStep 1832399 = 2748599) B2748599
theorem B1832555 : Blo 1220928 1832555 := bstep (se 1 (by rfl) ⟨1374416, by rfl⟩ : syracuseStep 1832555 = 2748833) B2748833
theorem B1832603 : Blo 1220928 1832603 := bstep (se 1 (by rfl) ⟨1374452, by rfl⟩ : syracuseStep 1832603 = 2748905) B2748905
theorem B4405063 : Blo 1220928 4405063 := bstep (se 1 (by rfl) ⟨3303797, by rfl⟩ : syracuseStep 4405063 = 6607595) B6607595
theorem B2750633 : Blo 1220928 2750633 := bstep (se 2 (by rfl) ⟨1031487, by rfl⟩ : syracuseStep 2750633 = 2062975) B2062975
theorem B1833167 : Blo 1220928 1833167 := bstep (se 1 (by rfl) ⟨1374875, by rfl⟩ : syracuseStep 1833167 = 2749751) B2749751
theorem B5953823 : Blo 1220928 5953823 := bstep (se 1 (by rfl) ⟨4465367, by rfl⟩ : syracuseStep 5953823 = 8930735) B8930735
theorem B1833353 : Blo 1220928 1833353 := bstep (se 2 (by rfl) ⟨687507, by rfl⟩ : syracuseStep 1833353 = 1375015) B1375015
theorem B3135883 : Blo 1220928 3135883 := bstep (se 1 (by rfl) ⟨2351912, by rfl⟩ : syracuseStep 3135883 = 4703825) B4703825
theorem B2750975 : Blo 1220928 2750975 := bstep (se 1 (by rfl) ⟨2063231, by rfl⟩ : syracuseStep 2750975 = 4126463) B4126463
theorem B1833599 : Blo 1220928 1833599 := bstep (se 1 (by rfl) ⟨1375199, by rfl⟩ : syracuseStep 1833599 = 2750399) B2750399
theorem B1833641 : Blo 1220928 1833641 := bstep (se 2 (by rfl) ⟨687615, by rfl⟩ : syracuseStep 1833641 = 1375231) B1375231
theorem B2063225 : Blo 1220928 2063225 := bstep (se 2 (by rfl) ⟨773709, by rfl⟩ : syracuseStep 2063225 = 1547419) B1547419
theorem B1834175 : Blo 1220928 1834175 := bstep (se 1 (by rfl) ⟨1375631, by rfl⟩ : syracuseStep 1834175 = 2751263) B2751263
theorem B50126039 : Blo 1220928 50126039 := bstep (se 1 (by rfl) ⟨37594529, by rfl⟩ : syracuseStep 50126039 = 75189059) B75189059
theorem B10435817 : Blo 1220928 10435817 := bstep (se 2 (by rfl) ⟨3913431, by rfl⟩ : syracuseStep 10435817 = 7826863) B7826863
theorem B1375591 : Blo 1220928 1375591 := bstep (se 1 (by rfl) ⟨1031693, by rfl⟩ : syracuseStep 1375591 = 2063387) B2063387
theorem B6610663 : Blo 1220928 6610663 := bstep (se 1 (by rfl) ⟨4957997, by rfl⟩ : syracuseStep 6610663 = 9915995) B9915995
theorem B1883903 : Blo 1220928 1883903 := bstep (se 1 (by rfl) ⟨1412927, by rfl⟩ : syracuseStep 1883903 = 2825855) B2825855
theorem B3178543 : Blo 1220928 3178543 := bstep (se 1 (by rfl) ⟨2383907, by rfl⟩ : syracuseStep 3178543 = 4767815) B4767815
theorem B190373975 : Blo 1220928 190373975 := bstep (se 1 (by rfl) ⟨142780481, by rfl⟩ : syracuseStep 190373975 = 285560963) B285560963
theorem B1221103 : Blo 1220928 1221103 := bstep (se 1 (by rfl) ⟨915827, by rfl⟩ : syracuseStep 1221103 = 1831655) B1831655
theorem B1221119 : Blo 1220928 1221119 := bstep (se 1 (by rfl) ⟨915839, by rfl⟩ : syracuseStep 1221119 = 1831679) B1831679
theorem B1221167 : Blo 1220928 1221167 := bstep (se 1 (by rfl) ⟨915875, by rfl⟩ : syracuseStep 1221167 = 1831751) B1831751
theorem B1221279 : Blo 1220928 1221279 := bstep (se 1 (by rfl) ⟨915959, by rfl⟩ : syracuseStep 1221279 = 1831919) B1831919
theorem B1221599 : Blo 1220928 1221599 := bstep (se 1 (by rfl) ⟨916199, by rfl⟩ : syracuseStep 1221599 = 1832399) B1832399
theorem B1221703 : Blo 1220928 1221703 := bstep (se 1 (by rfl) ⟨916277, by rfl⟩ : syracuseStep 1221703 = 1832555) B1832555
theorem B1221735 : Blo 1220928 1221735 := bstep (se 1 (by rfl) ⟨916301, by rfl⟩ : syracuseStep 1221735 = 1832603) B1832603
theorem B1222111 : Blo 1220928 1222111 := bstep (se 1 (by rfl) ⟨916583, by rfl⟩ : syracuseStep 1222111 = 1833167) B1833167
theorem B1222235 : Blo 1220928 1222235 := bstep (se 1 (by rfl) ⟨916676, by rfl⟩ : syracuseStep 1222235 = 1833353) B1833353
theorem B1394383 : Blo 1220928 1394383 := bstep (se 1 (by rfl) ⟨1045787, by rfl⟩ : syracuseStep 1394383 = 2091575) B2091575
theorem B1222399 : Blo 1220928 1222399 := bstep (se 1 (by rfl) ⟨916799, by rfl⟩ : syracuseStep 1222399 = 1833599) B1833599
theorem B1222427 : Blo 1220928 1222427 := bstep (se 1 (by rfl) ⟨916820, by rfl⟩ : syracuseStep 1222427 = 1833641) B1833641
theorem B5023741 : Blo 1220928 5023741 := bstep (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) B1883903
theorem B1222783 : Blo 1220928 1222783 := bstep (se 1 (by rfl) ⟨917087, by rfl⟩ : syracuseStep 1222783 = 1834175) B1834175
theorem B33417359 : Blo 1220928 33417359 := bstep (se 1 (by rfl) ⟨25063019, by rfl⟩ : syracuseStep 33417359 = 50126039) B50126039
theorem B6957211 : Blo 1220928 6957211 := bstep (se 1 (by rfl) ⟨5217908, by rfl⟩ : syracuseStep 6957211 = 10435817) B10435817
theorem B13912235 : Blo 1220928 13912235 := bstep (se 1 (by rfl) ⟨10434176, by rfl⟩ : syracuseStep 13912235 = 20868353) B20868353
theorem B2747105 : Blo 1220928 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B2747177 : Blo 1220928 2747177 := bstep (se 2 (by rfl) ⟨1030191, by rfl⟩ : syracuseStep 2747177 = 2060383) B2060383
theorem B4181177 : Blo 1220928 4181177 := bstep (se 2 (by rfl) ⟨1567941, by rfl⟩ : syracuseStep 4181177 = 3135883) B3135883
theorem B267570701 : Blo 1220928 267570701 := bstep (se 3 (by rfl) ⟨50169506, by rfl⟩ : syracuseStep 267570701 = 100339013) B100339013
theorem B11308585 : Blo 1220928 11308585 := bstep (se 2 (by rfl) ⟨4240719, by rfl⟩ : syracuseStep 11308585 = 8481439) B8481439
theorem B5222009 : Blo 1220928 5222009 := bstep (se 2 (by rfl) ⟨1958253, by rfl⟩ : syracuseStep 5222009 = 3916507) B3916507
theorem B2748239 : Blo 1220928 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B3969215 : Blo 1220928 3969215 := bstep (se 1 (by rfl) ⟨2976911, by rfl⟩ : syracuseStep 3969215 = 5953823) B5953823
theorem B4403753 : Blo 1220928 4403753 := bstep (se 2 (by rfl) ⟨1651407, by rfl⟩ : syracuseStep 4403753 = 3302815) B3302815
theorem B2200441 : Blo 1220928 2200441 := bstep (se 2 (by rfl) ⟨825165, by rfl⟩ : syracuseStep 2200441 = 1650331) B1650331
theorem B4641725 : Blo 1220928 4641725 := bstep (se 3 (by rfl) ⟨870323, by rfl⟩ : syracuseStep 4641725 = 1740647) B1740647
theorem B1832039 : Blo 1220928 1832039 := bstep (se 1 (by rfl) ⟨1374029, by rfl⟩ : syracuseStep 1832039 = 2748059) B2748059
theorem B39646331 : Blo 1220928 39646331 := bstep (se 1 (by rfl) ⟨29734748, by rfl⟩ : syracuseStep 39646331 = 59469497) B59469497
theorem B142816465 : Blo 1220928 142816465 := bstep (se 2 (by rfl) ⟨53556174, by rfl⟩ : syracuseStep 142816465 = 107112349) B107112349
theorem B1832303 : Blo 1220928 1832303 := bstep (se 1 (by rfl) ⟨1374227, by rfl⟩ : syracuseStep 1832303 = 2748455) B2748455
theorem B2061983 : Blo 1220928 2061983 := bstep (se 1 (by rfl) ⟨1546487, by rfl⟩ : syracuseStep 2061983 = 3092975) B3092975
theorem B23795963 : Blo 1220928 23795963 := bstep (se 1 (by rfl) ⟨17846972, by rfl⟩ : syracuseStep 23795963 = 35693945) B35693945
theorem B13916609 : Blo 1220928 13916609 := bstep (se 2 (by rfl) ⟨5218728, by rfl⟩ : syracuseStep 13916609 = 10437457) B10437457
theorem B35256869 : Blo 1220928 35256869 := bstep (se 4 (by rfl) ⟨3305331, by rfl⟩ : syracuseStep 35256869 = 6610663) B6610663
theorem B1882793 : Blo 1220928 1882793 := bstep (se 2 (by rfl) ⟨706047, by rfl⟩ : syracuseStep 1882793 = 1412095) B1412095
theorem B1833755 : Blo 1220928 1833755 := bstep (se 1 (by rfl) ⟨1375316, by rfl⟩ : syracuseStep 1833755 = 2750633) B2750633
theorem B1833983 : Blo 1220928 1833983 := bstep (se 1 (by rfl) ⟨1375487, by rfl⟩ : syracuseStep 1833983 = 2750975) B2750975
theorem B1834121 : Blo 1220928 1834121 := bstep (se 2 (by rfl) ⟨687795, by rfl⟩ : syracuseStep 1834121 = 1375591) B1375591
theorem B1375483 : Blo 1220928 1375483 := bstep (se 1 (by rfl) ⟨1031612, by rfl⟩ : syracuseStep 1375483 = 2063225) B2063225
theorem B6954295 : Blo 1220928 6954295 := bstep (se 1 (by rfl) ⟨5215721, by rfl⟩ : syracuseStep 6954295 = 10431443) B10431443
theorem B3718781 : Blo 1220928 3718781 := bstep (se 3 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 3718781 = 1394543) B1394543
theorem B5873417 : Blo 1220928 5873417 := bstep (se 2 (by rfl) ⟨2202531, by rfl⟩ : syracuseStep 5873417 = 4405063) B4405063
theorem B2646143 : Blo 1220928 2646143 := bstep (se 1 (by rfl) ⟨1984607, by rfl⟩ : syracuseStep 2646143 = 3969215) B3969215
theorem B11149805 : Blo 1220928 11149805 := bstep (se 3 (by rfl) ⟨2090588, by rfl⟩ : syracuseStep 11149805 = 4181177) B4181177
theorem B1221359 : Blo 1220928 1221359 := bstep (se 1 (by rfl) ⟨916019, by rfl⟩ : syracuseStep 1221359 = 1832039) B1832039
theorem B1221535 : Blo 1220928 1221535 := bstep (se 1 (by rfl) ⟨916151, by rfl⟩ : syracuseStep 1221535 = 1832303) B1832303
theorem B2933921 : Blo 1220928 2933921 := bstep (se 2 (by rfl) ⟨1100220, by rfl⟩ : syracuseStep 2933921 = 2200441) B2200441
theorem B9274823 : Blo 1220928 9274823 := bstep (se 1 (by rfl) ⟨6956117, by rfl⟩ : syracuseStep 9274823 = 13912235) B13912235
theorem B23504579 : Blo 1220928 23504579 := bstep (se 1 (by rfl) ⟨17628434, by rfl⟩ : syracuseStep 23504579 = 35256869) B35256869
theorem B1255195 : Blo 1220928 1255195 := bstep (se 1 (by rfl) ⟨941396, by rfl⟩ : syracuseStep 1255195 = 1882793) B1882793
theorem B1222503 : Blo 1220928 1222503 := bstep (se 1 (by rfl) ⟨916877, by rfl⟩ : syracuseStep 1222503 = 1833755) B1833755
theorem B1222655 : Blo 1220928 1222655 := bstep (se 1 (by rfl) ⟨916991, by rfl⟩ : syracuseStep 1222655 = 1833983) B1833983
theorem B1222747 : Blo 1220928 1222747 := bstep (se 1 (by rfl) ⟨917060, by rfl⟩ : syracuseStep 1222747 = 1834121) B1834121
theorem B4238057 : Blo 1220928 4238057 := bstep (se 2 (by rfl) ⟨1589271, by rfl⟩ : syracuseStep 4238057 = 3178543) B3178543
theorem B9276281 : Blo 1220928 9276281 := bstep (se 2 (by rfl) ⟨3478605, by rfl⟩ : syracuseStep 9276281 = 6957211) B6957211
theorem B2935835 : Blo 1220928 2935835 := bstep (se 1 (by rfl) ⟨2201876, by rfl⟩ : syracuseStep 2935835 = 4403753) B4403753
theorem B26430887 : Blo 1220928 26430887 := bstep (se 1 (by rfl) ⟨19823165, by rfl⟩ : syracuseStep 26430887 = 39646331) B39646331
theorem B761687813 : Blo 1220928 761687813 := bstep (se 4 (by rfl) ⟨71408232, by rfl⟩ : syracuseStep 761687813 = 142816465) B142816465
theorem B22278239 : Blo 1220928 22278239 := bstep (se 1 (by rfl) ⟨16708679, by rfl⟩ : syracuseStep 22278239 = 33417359) B33417359
theorem B15863975 : Blo 1220928 15863975 := bstep (se 1 (by rfl) ⟨11897981, by rfl⟩ : syracuseStep 15863975 = 23795963) B23795963
theorem B9277739 : Blo 1220928 9277739 := bstep (se 1 (by rfl) ⟨6958304, by rfl⟩ : syracuseStep 9277739 = 13916609) B13916609
theorem B1831403 : Blo 1220928 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B1831451 : Blo 1220928 1831451 := bstep (se 1 (by rfl) ⟨1373588, by rfl⟩ : syracuseStep 1831451 = 2747177) B2747177
theorem B15078113 : Blo 1220928 15078113 := bstep (se 2 (by rfl) ⟨5654292, by rfl⟩ : syracuseStep 15078113 = 11308585) B11308585
theorem B2479187 : Blo 1220928 2479187 := bstep (se 1 (by rfl) ⟨1859390, by rfl⟩ : syracuseStep 2479187 = 3718781) B3718781
theorem B1832159 : Blo 1220928 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B6698321 : Blo 1220928 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B126915983 : Blo 1220928 126915983 := bstep (se 1 (by rfl) ⟨95186987, by rfl⟩ : syracuseStep 126915983 = 190373975) B190373975
theorem B3094483 : Blo 1220928 3094483 := bstep (se 1 (by rfl) ⟨2320862, by rfl⟩ : syracuseStep 3094483 = 4641725) B4641725
theorem B1374655 : Blo 1220928 1374655 := bstep (se 1 (by rfl) ⟨1030991, by rfl⟩ : syracuseStep 1374655 = 2061983) B2061983
theorem B13925357 : Blo 1220928 13925357 := bstep (se 3 (by rfl) ⟨2611004, by rfl⟩ : syracuseStep 13925357 = 5222009) B5222009
theorem B1833977 : Blo 1220928 1833977 := bstep (se 2 (by rfl) ⟨687741, by rfl⟩ : syracuseStep 1833977 = 1375483) B1375483
theorem B9272393 : Blo 1220928 9272393 := bstep (se 2 (by rfl) ⟨3477147, by rfl⟩ : syracuseStep 9272393 = 6954295) B6954295
theorem B1859177 : Blo 1220928 1859177 := bstep (se 2 (by rfl) ⟨697191, by rfl⟩ : syracuseStep 1859177 = 1394383) B1394383
theorem B178380467 : Blo 1220928 178380467 := bstep (se 1 (by rfl) ⟨133785350, by rfl⟩ : syracuseStep 178380467 = 267570701) B267570701
theorem B3915611 : Blo 1220928 3915611 := bstep (se 1 (by rfl) ⟨2936708, by rfl⟩ : syracuseStep 3915611 = 5873417) B5873417
theorem B14852159 : Blo 1220928 14852159 := bstep (se 1 (by rfl) ⟨11139119, by rfl⟩ : syracuseStep 14852159 = 22278239) B22278239
theorem B10575983 : Blo 1220928 10575983 := bstep (se 1 (by rfl) ⟨7931987, by rfl⟩ : syracuseStep 10575983 = 15863975) B15863975
theorem B6185159 : Blo 1220928 6185159 := bstep (se 1 (by rfl) ⟨4638869, by rfl⟩ : syracuseStep 6185159 = 9277739) B9277739
theorem B6611165 : Blo 1220928 6611165 := bstep (se 3 (by rfl) ⟨1239593, by rfl⟩ : syracuseStep 6611165 = 2479187) B2479187
theorem B1220935 : Blo 1220928 1220935 := bstep (se 1 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 1220935 = 1831403) B1831403
theorem B1220967 : Blo 1220928 1220967 := bstep (se 1 (by rfl) ⟨915725, by rfl⟩ : syracuseStep 1220967 = 1831451) B1831451
theorem B7823789 : Blo 1220928 7823789 := bstep (se 3 (by rfl) ⟨1466960, by rfl⟩ : syracuseStep 7823789 = 2933921) B2933921
theorem B10052075 : Blo 1220928 10052075 := bstep (se 1 (by rfl) ⟨7539056, by rfl⟩ : syracuseStep 10052075 = 15078113) B15078113
theorem B1221439 : Blo 1220928 1221439 := bstep (se 1 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 1221439 = 1832159) B1832159
theorem B4465547 : Blo 1220928 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B6694373 : Blo 1220928 6694373 := bstep (se 4 (by rfl) ⟨627597, by rfl⟩ : syracuseStep 6694373 = 1255195) B1255195
theorem B9283571 : Blo 1220928 9283571 := bstep (se 1 (by rfl) ⟨6962678, by rfl⟩ : syracuseStep 9283571 = 13925357) B13925357
theorem B1222651 : Blo 1220928 1222651 := bstep (se 1 (by rfl) ⟨916988, by rfl⟩ : syracuseStep 1222651 = 1833977) B1833977
theorem B1239451 : Blo 1220928 1239451 := bstep (se 1 (by rfl) ⟨929588, by rfl⟩ : syracuseStep 1239451 = 1859177) B1859177
theorem B507791875 : Blo 1220928 507791875 := bstep (se 1 (by rfl) ⟨380843906, by rfl⟩ : syracuseStep 507791875 = 761687813) B761687813
theorem B7433203 : Blo 1220928 7433203 := bstep (se 1 (by rfl) ⟨5574902, by rfl⟩ : syracuseStep 7433203 = 11149805) B11149805
theorem B84610655 : Blo 1220928 84610655 := bstep (se 1 (by rfl) ⟨63457991, by rfl⟩ : syracuseStep 84610655 = 126915983) B126915983
theorem B28225525 : Blo 1220928 28225525 := bstep (se 5 (by rfl) ⟨1323071, by rfl⟩ : syracuseStep 28225525 = 2646143) B2646143
theorem B6181595 : Blo 1220928 6181595 := bstep (se 1 (by rfl) ⟨4636196, by rfl⟩ : syracuseStep 6181595 = 9272393) B9272393
theorem B118920311 : Blo 1220928 118920311 := bstep (se 1 (by rfl) ⟨89190233, by rfl⟩ : syracuseStep 118920311 = 178380467) B178380467
theorem B2610407 : Blo 1220928 2610407 := bstep (se 1 (by rfl) ⟨1957805, by rfl⟩ : syracuseStep 2610407 = 3915611) B3915611
theorem B4125977 : Blo 1220928 4125977 := bstep (se 2 (by rfl) ⟨1547241, by rfl⟩ : syracuseStep 4125977 = 3094483) B3094483
theorem B1832873 : Blo 1220928 1832873 := bstep (se 2 (by rfl) ⟨687327, by rfl⟩ : syracuseStep 1832873 = 1374655) B1374655
theorem B6183215 : Blo 1220928 6183215 := bstep (se 1 (by rfl) ⟨4637411, by rfl⟩ : syracuseStep 6183215 = 9274823) B9274823
theorem B15669719 : Blo 1220928 15669719 := bstep (se 1 (by rfl) ⟨11752289, by rfl⟩ : syracuseStep 15669719 = 23504579) B23504579
theorem B2825371 : Blo 1220928 2825371 := bstep (se 1 (by rfl) ⟨2119028, by rfl⟩ : syracuseStep 2825371 = 4238057) B4238057
theorem B6184187 : Blo 1220928 6184187 := bstep (se 1 (by rfl) ⟨4638140, by rfl⟩ : syracuseStep 6184187 = 9276281) B9276281
theorem B1957223 : Blo 1220928 1957223 := bstep (se 1 (by rfl) ⟨1467917, by rfl⟩ : syracuseStep 1957223 = 2935835) B2935835
theorem B17620591 : Blo 1220928 17620591 := bstep (se 1 (by rfl) ⟨13215443, by rfl⟩ : syracuseStep 17620591 = 26430887) B26430887
theorem B4407443 : Blo 1220928 4407443 := bstep (se 1 (by rfl) ⟨3305582, by rfl⟩ : syracuseStep 4407443 = 6611165) B6611165
theorem B6701383 : Blo 1220928 6701383 := bstep (se 1 (by rfl) ⟨5026037, by rfl⟩ : syracuseStep 6701383 = 10052075) B10052075
theorem B4121063 : Blo 1220928 4121063 := bstep (se 1 (by rfl) ⟨3090797, by rfl⟩ : syracuseStep 4121063 = 6181595) B6181595
theorem B5219261 : Blo 1220928 5219261 := bstep (se 3 (by rfl) ⟨978611, by rfl⟩ : syracuseStep 5219261 = 1957223) B1957223
theorem B17851661 : Blo 1220928 17851661 := bstep (se 3 (by rfl) ⟨3347186, by rfl⟩ : syracuseStep 17851661 = 6694373) B6694373
theorem B1221915 : Blo 1220928 1221915 := bstep (se 1 (by rfl) ⟨916436, by rfl⟩ : syracuseStep 1221915 = 1832873) B1832873
theorem B4122143 : Blo 1220928 4122143 := bstep (se 1 (by rfl) ⟨3091607, by rfl⟩ : syracuseStep 4122143 = 6183215) B6183215
theorem B10446479 : Blo 1220928 10446479 := bstep (se 1 (by rfl) ⟨7834859, by rfl⟩ : syracuseStep 10446479 = 15669719) B15669719
theorem B4122791 : Blo 1220928 4122791 := bstep (se 1 (by rfl) ⟨3092093, by rfl⟩ : syracuseStep 4122791 = 6184187) B6184187
theorem B4123439 : Blo 1220928 4123439 := bstep (se 1 (by rfl) ⟨3092579, by rfl⟩ : syracuseStep 4123439 = 6185159) B6185159
theorem B2977031 : Blo 1220928 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B677055833 : Blo 1220928 677055833 := bstep (se 2 (by rfl) ⟨253895937, by rfl⟩ : syracuseStep 677055833 = 507791875) B507791875
theorem B15068645 : Blo 1220928 15068645 := bstep (se 4 (by rfl) ⟨1412685, by rfl⟩ : syracuseStep 15068645 = 2825371) B2825371
theorem B6189047 : Blo 1220928 6189047 := bstep (se 1 (by rfl) ⟨4641785, by rfl⟩ : syracuseStep 6189047 = 9283571) B9283571
theorem B56407103 : Blo 1220928 56407103 := bstep (se 1 (by rfl) ⟨42305327, by rfl⟩ : syracuseStep 56407103 = 84610655) B84610655
theorem B9901439 : Blo 1220928 9901439 := bstep (se 1 (by rfl) ⟨7426079, by rfl⟩ : syracuseStep 9901439 = 14852159) B14852159
theorem B7050655 : Blo 1220928 7050655 := bstep (se 1 (by rfl) ⟨5287991, by rfl⟩ : syracuseStep 7050655 = 10575983) B10575983
theorem B5215859 : Blo 1220928 5215859 := bstep (se 1 (by rfl) ⟨3911894, by rfl⟩ : syracuseStep 5215859 = 7823789) B7823789
theorem B6961085 : Blo 1220928 6961085 := bstep (se 3 (by rfl) ⟨1305203, by rfl⟩ : syracuseStep 6961085 = 2610407) B2610407
theorem B79280207 : Blo 1220928 79280207 := bstep (se 1 (by rfl) ⟨59460155, by rfl⟩ : syracuseStep 79280207 = 118920311) B118920311
theorem B2750651 : Blo 1220928 2750651 := bstep (se 1 (by rfl) ⟨2062988, by rfl⟩ : syracuseStep 2750651 = 4125977) B4125977
theorem B9910937 : Blo 1220928 9910937 := bstep (se 2 (by rfl) ⟨3716601, by rfl⟩ : syracuseStep 9910937 = 7433203) B7433203
theorem B6610405 : Blo 1220928 6610405 := bstep (se 4 (by rfl) ⟨619725, by rfl⟩ : syracuseStep 6610405 = 1239451) B1239451
theorem B23494121 : Blo 1220928 23494121 := bstep (se 2 (by rfl) ⟨8810295, by rfl⟩ : syracuseStep 23494121 = 17620591) B17620591
theorem B37634033 : Blo 1220928 37634033 := bstep (se 2 (by rfl) ⟨14112762, by rfl⟩ : syracuseStep 37634033 = 28225525) B28225525
theorem B7938749 : Blo 1220928 7938749 := bstep (se 3 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 7938749 = 2977031) B2977031
theorem B6964319 : Blo 1220928 6964319 := bstep (se 1 (by rfl) ⟨5223239, by rfl⟩ : syracuseStep 6964319 = 10446479) B10446479
theorem B26429165 : Blo 1220928 26429165 := bstep (se 3 (by rfl) ⟨4955468, by rfl⟩ : syracuseStep 26429165 = 9910937) B9910937
theorem B10045763 : Blo 1220928 10045763 := bstep (se 1 (by rfl) ⟨7534322, by rfl⟩ : syracuseStep 10045763 = 15068645) B15068645
theorem B2747375 : Blo 1220928 2747375 := bstep (se 1 (by rfl) ⟨2060531, by rfl⟩ : syracuseStep 2747375 = 4121063) B4121063
theorem B37604735 : Blo 1220928 37604735 := bstep (se 1 (by rfl) ⟨28203551, by rfl⟩ : syracuseStep 37604735 = 56407103) B56407103
theorem B2748095 : Blo 1220928 2748095 := bstep (se 1 (by rfl) ⟨2061071, by rfl⟩ : syracuseStep 2748095 = 4122143) B4122143
theorem B3477239 : Blo 1220928 3477239 := bstep (se 1 (by rfl) ⟨2607929, by rfl⟩ : syracuseStep 3477239 = 5215859) B5215859
theorem B4640723 : Blo 1220928 4640723 := bstep (se 1 (by rfl) ⟨3480542, by rfl⟩ : syracuseStep 4640723 = 6961085) B6961085
theorem B2748527 : Blo 1220928 2748527 := bstep (se 1 (by rfl) ⟨2061395, by rfl⟩ : syracuseStep 2748527 = 4122791) B4122791
theorem B2748959 : Blo 1220928 2748959 := bstep (se 1 (by rfl) ⟨2061719, by rfl⟩ : syracuseStep 2748959 = 4123439) B4123439
theorem B9400873 : Blo 1220928 9400873 := bstep (se 2 (by rfl) ⟨3525327, by rfl⟩ : syracuseStep 9400873 = 7050655) B7050655
theorem B25089355 : Blo 1220928 25089355 := bstep (se 1 (by rfl) ⟨18817016, by rfl⟩ : syracuseStep 25089355 = 37634033) B37634033
theorem B4126031 : Blo 1220928 4126031 := bstep (se 1 (by rfl) ⟨3094523, by rfl⟩ : syracuseStep 4126031 = 6189047) B6189047
theorem B2938295 : Blo 1220928 2938295 := bstep (se 1 (by rfl) ⟨2203721, by rfl⟩ : syracuseStep 2938295 = 4407443) B4407443
theorem B8935177 : Blo 1220928 8935177 := bstep (se 2 (by rfl) ⟨3350691, by rfl⟩ : syracuseStep 8935177 = 6701383) B6701383
theorem B3479507 : Blo 1220928 3479507 := bstep (se 1 (by rfl) ⟨2609630, by rfl⟩ : syracuseStep 3479507 = 5219261) B5219261
theorem B11901107 : Blo 1220928 11901107 := bstep (se 1 (by rfl) ⟨8925830, by rfl⟩ : syracuseStep 11901107 = 17851661) B17851661
theorem B6600959 : Blo 1220928 6600959 := bstep (se 1 (by rfl) ⟨4950719, by rfl⟩ : syracuseStep 6600959 = 9901439) B9901439
theorem B52853471 : Blo 1220928 52853471 := bstep (se 1 (by rfl) ⟨39640103, by rfl⟩ : syracuseStep 52853471 = 79280207) B79280207
theorem B1833767 : Blo 1220928 1833767 := bstep (se 1 (by rfl) ⟨1375325, by rfl⟩ : syracuseStep 1833767 = 2750651) B2750651
theorem B8813873 : Blo 1220928 8813873 := bstep (se 2 (by rfl) ⟨3305202, by rfl⟩ : syracuseStep 8813873 = 6610405) B6610405
theorem B451370555 : Blo 1220928 451370555 := bstep (se 1 (by rfl) ⟨338527916, by rfl⟩ : syracuseStep 451370555 = 677055833) B677055833
theorem B15662747 : Blo 1220928 15662747 := bstep (se 1 (by rfl) ⟨11747060, by rfl⟩ : syracuseStep 15662747 = 23494121) B23494121
theorem B5292499 : Blo 1220928 5292499 := bstep (se 1 (by rfl) ⟨3969374, by rfl⟩ : syracuseStep 5292499 = 7938749) B7938749
theorem B12534497 : Blo 1220928 12534497 := bstep (se 2 (by rfl) ⟨4700436, by rfl⟩ : syracuseStep 12534497 = 9400873) B9400873
theorem B2319671 : Blo 1220928 2319671 := bstep (se 1 (by rfl) ⟨1739753, by rfl⟩ : syracuseStep 2319671 = 3479507) B3479507
theorem B4400639 : Blo 1220928 4400639 := bstep (se 1 (by rfl) ⟨3300479, by rfl⟩ : syracuseStep 4400639 = 6600959) B6600959
theorem B35235647 : Blo 1220928 35235647 := bstep (se 1 (by rfl) ⟨26426735, by rfl⟩ : syracuseStep 35235647 = 52853471) B52853471
theorem B1222511 : Blo 1220928 1222511 := bstep (se 1 (by rfl) ⟨916883, by rfl⟩ : syracuseStep 1222511 = 1833767) B1833767
theorem B5875915 : Blo 1220928 5875915 := bstep (se 1 (by rfl) ⟨4406936, by rfl⟩ : syracuseStep 5875915 = 8813873) B8813873
theorem B25069823 : Blo 1220928 25069823 := bstep (se 1 (by rfl) ⟨18802367, by rfl⟩ : syracuseStep 25069823 = 37604735) B37604735
theorem B11913569 : Blo 1220928 11913569 := bstep (se 2 (by rfl) ⟨4467588, by rfl⟩ : syracuseStep 11913569 = 8935177) B8935177
theorem B7835453 : Blo 1220928 7835453 := bstep (se 3 (by rfl) ⟨1469147, by rfl⟩ : syracuseStep 7835453 = 2938295) B2938295
theorem B7934071 : Blo 1220928 7934071 := bstep (se 1 (by rfl) ⟨5950553, by rfl⟩ : syracuseStep 7934071 = 11901107) B11901107
theorem B6697175 : Blo 1220928 6697175 := bstep (se 1 (by rfl) ⟨5022881, by rfl⟩ : syracuseStep 6697175 = 10045763) B10045763
theorem B33452473 : Blo 1220928 33452473 := bstep (se 2 (by rfl) ⟨12544677, by rfl⟩ : syracuseStep 33452473 = 25089355) B25089355
theorem B1831583 : Blo 1220928 1831583 := bstep (se 1 (by rfl) ⟨1373687, by rfl⟩ : syracuseStep 1831583 = 2747375) B2747375
theorem B300913703 : Blo 1220928 300913703 := bstep (se 1 (by rfl) ⟨225685277, by rfl⟩ : syracuseStep 300913703 = 451370555) B451370555
theorem B10441831 : Blo 1220928 10441831 := bstep (se 1 (by rfl) ⟨7831373, by rfl⟩ : syracuseStep 10441831 = 15662747) B15662747
theorem B1832063 : Blo 1220928 1832063 := bstep (se 1 (by rfl) ⟨1374047, by rfl⟩ : syracuseStep 1832063 = 2748095) B2748095
theorem B3093815 : Blo 1220928 3093815 := bstep (se 1 (by rfl) ⟨2320361, by rfl⟩ : syracuseStep 3093815 = 4640723) B4640723
theorem B1832351 : Blo 1220928 1832351 := bstep (se 1 (by rfl) ⟨1374263, by rfl⟩ : syracuseStep 1832351 = 2748527) B2748527
theorem B1832639 : Blo 1220928 1832639 := bstep (se 1 (by rfl) ⟨1374479, by rfl⟩ : syracuseStep 1832639 = 2748959) B2748959
theorem B4642879 : Blo 1220928 4642879 := bstep (se 1 (by rfl) ⟨3482159, by rfl⟩ : syracuseStep 4642879 = 6964319) B6964319
theorem B2750687 : Blo 1220928 2750687 := bstep (se 1 (by rfl) ⟨2063015, by rfl⟩ : syracuseStep 2750687 = 4126031) B4126031
theorem B17619443 : Blo 1220928 17619443 := bstep (se 1 (by rfl) ⟨13214582, by rfl⟩ : syracuseStep 17619443 = 26429165) B26429165
theorem B2318159 : Blo 1220928 2318159 := bstep (se 1 (by rfl) ⟨1738619, by rfl⟩ : syracuseStep 2318159 = 3477239) B3477239
theorem B1221055 : Blo 1220928 1221055 := bstep (se 1 (by rfl) ⟨915791, by rfl⟩ : syracuseStep 1221055 = 1831583) B1831583
theorem B8356331 : Blo 1220928 8356331 := bstep (se 1 (by rfl) ⟨6267248, by rfl⟩ : syracuseStep 8356331 = 12534497) B12534497
theorem B17859133 : Blo 1220928 17859133 := bstep (se 3 (by rfl) ⟨3348587, by rfl⟩ : syracuseStep 17859133 = 6697175) B6697175
theorem B1221375 : Blo 1220928 1221375 := bstep (se 1 (by rfl) ⟨916031, by rfl⟩ : syracuseStep 1221375 = 1832063) B1832063
theorem B1221567 : Blo 1220928 1221567 := bstep (se 1 (by rfl) ⟨916175, by rfl⟩ : syracuseStep 1221567 = 1832351) B1832351
theorem B2933759 : Blo 1220928 2933759 := bstep (se 1 (by rfl) ⟨2200319, by rfl⟩ : syracuseStep 2933759 = 4400639) B4400639
theorem B1221759 : Blo 1220928 1221759 := bstep (se 1 (by rfl) ⟨916319, by rfl⟩ : syracuseStep 1221759 = 1832639) B1832639
theorem B16713215 : Blo 1220928 16713215 := bstep (se 1 (by rfl) ⟨12534911, by rfl⟩ : syracuseStep 16713215 = 25069823) B25069823
theorem B10578761 : Blo 1220928 10578761 := bstep (se 2 (by rfl) ⟨3967035, by rfl⟩ : syracuseStep 10578761 = 7934071) B7934071
theorem B7834553 : Blo 1220928 7834553 := bstep (se 2 (by rfl) ⟨2937957, by rfl⟩ : syracuseStep 7834553 = 5875915) B5875915
theorem B7056665 : Blo 1220928 7056665 := bstep (se 2 (by rfl) ⟨2646249, by rfl⟩ : syracuseStep 7056665 = 5292499) B5292499
theorem B200609135 : Blo 1220928 200609135 := bstep (se 1 (by rfl) ⟨150456851, by rfl⟩ : syracuseStep 200609135 = 300913703) B300913703
theorem B23490431 : Blo 1220928 23490431 := bstep (se 1 (by rfl) ⟨17617823, by rfl⟩ : syracuseStep 23490431 = 35235647) B35235647
theorem B13922441 : Blo 1220928 13922441 := bstep (se 2 (by rfl) ⟨5220915, by rfl⟩ : syracuseStep 13922441 = 10441831) B10441831
theorem B7942379 : Blo 1220928 7942379 := bstep (se 1 (by rfl) ⟨5956784, by rfl⟩ : syracuseStep 7942379 = 11913569) B11913569
theorem B6181757 : Blo 1220928 6181757 := bstep (se 3 (by rfl) ⟨1159079, by rfl⟩ : syracuseStep 6181757 = 2318159) B2318159
theorem B5223635 : Blo 1220928 5223635 := bstep (se 1 (by rfl) ⟨3917726, by rfl⟩ : syracuseStep 5223635 = 7835453) B7835453
theorem B6190505 : Blo 1220928 6190505 := bstep (se 2 (by rfl) ⟨2321439, by rfl⟩ : syracuseStep 6190505 = 4642879) B4642879
theorem B44603297 : Blo 1220928 44603297 := bstep (se 2 (by rfl) ⟨16726236, by rfl⟩ : syracuseStep 44603297 = 33452473) B33452473
theorem B1546447 : Blo 1220928 1546447 := bstep (se 1 (by rfl) ⟨1159835, by rfl⟩ : syracuseStep 1546447 = 2319671) B2319671
theorem B2062543 : Blo 1220928 2062543 := bstep (se 1 (by rfl) ⟨1546907, by rfl⟩ : syracuseStep 2062543 = 3093815) B3093815
theorem B1833791 : Blo 1220928 1833791 := bstep (se 1 (by rfl) ⟨1375343, by rfl⟩ : syracuseStep 1833791 = 2750687) B2750687
theorem B11746295 : Blo 1220928 11746295 := bstep (se 1 (by rfl) ⟨8809721, by rfl⟩ : syracuseStep 11746295 = 17619443) B17619443
theorem B9281627 : Blo 1220928 9281627 := bstep (se 1 (by rfl) ⟨6961220, by rfl⟩ : syracuseStep 9281627 = 13922441) B13922441
theorem B4121171 : Blo 1220928 4121171 := bstep (se 1 (by rfl) ⟨3090878, by rfl⟩ : syracuseStep 4121171 = 6181757) B6181757
theorem B3482423 : Blo 1220928 3482423 := bstep (se 1 (by rfl) ⟨2611817, by rfl⟩ : syracuseStep 3482423 = 5223635) B5223635
theorem B11142143 : Blo 1220928 11142143 := bstep (se 1 (by rfl) ⟨8356607, by rfl⟩ : syracuseStep 11142143 = 16713215) B16713215
theorem B22283549 : Blo 1220928 22283549 := bstep (se 3 (by rfl) ⟨4178165, by rfl⟩ : syracuseStep 22283549 = 8356331) B8356331
theorem B1222527 : Blo 1220928 1222527 := bstep (se 1 (by rfl) ⟨916895, by rfl⟩ : syracuseStep 1222527 = 1833791) B1833791
theorem B4704443 : Blo 1220928 4704443 := bstep (se 1 (by rfl) ⟨3528332, by rfl⟩ : syracuseStep 4704443 = 7056665) B7056665
theorem B5223035 : Blo 1220928 5223035 := bstep (se 1 (by rfl) ⟨3917276, by rfl⟩ : syracuseStep 5223035 = 7834553) B7834553
theorem B133739423 : Blo 1220928 133739423 := bstep (se 1 (by rfl) ⟨100304567, by rfl⟩ : syracuseStep 133739423 = 200609135) B200609135
theorem B84718709 : Blo 1220928 84718709 := bstep (se 5 (by rfl) ⟨3971189, by rfl⟩ : syracuseStep 84718709 = 7942379) B7942379
theorem B15660287 : Blo 1220928 15660287 := bstep (se 1 (by rfl) ⟨11745215, by rfl⟩ : syracuseStep 15660287 = 23490431) B23490431
theorem B2061929 : Blo 1220928 2061929 := bstep (se 2 (by rfl) ⟨773223, by rfl⟩ : syracuseStep 2061929 = 1546447) B1546447
theorem B2750057 : Blo 1220928 2750057 := bstep (se 2 (by rfl) ⟨1031271, by rfl⟩ : syracuseStep 2750057 = 2062543) B2062543
theorem B1955839 : Blo 1220928 1955839 := bstep (se 1 (by rfl) ⟨1466879, by rfl⟩ : syracuseStep 1955839 = 2933759) B2933759
theorem B23812177 : Blo 1220928 23812177 := bstep (se 2 (by rfl) ⟨8929566, by rfl⟩ : syracuseStep 23812177 = 17859133) B17859133
theorem B4127003 : Blo 1220928 4127003 := bstep (se 1 (by rfl) ⟨3095252, by rfl⟩ : syracuseStep 4127003 = 6190505) B6190505
theorem B29735531 : Blo 1220928 29735531 := bstep (se 1 (by rfl) ⟨22301648, by rfl⟩ : syracuseStep 29735531 = 44603297) B44603297
theorem B7052507 : Blo 1220928 7052507 := bstep (se 1 (by rfl) ⟨5289380, by rfl⟩ : syracuseStep 7052507 = 10578761) B10578761
theorem B7830863 : Blo 1220928 7830863 := bstep (se 1 (by rfl) ⟨5873147, by rfl⟩ : syracuseStep 7830863 = 11746295) B11746295
theorem B3482023 : Blo 1220928 3482023 := bstep (se 1 (by rfl) ⟨2611517, by rfl⟩ : syracuseStep 3482023 = 5223035) B5223035
theorem B5220575 : Blo 1220928 5220575 := bstep (se 1 (by rfl) ⟨3915431, by rfl⟩ : syracuseStep 5220575 = 7830863) B7830863
theorem B2607785 : Blo 1220928 2607785 := bstep (se 2 (by rfl) ⟨977919, by rfl⟩ : syracuseStep 2607785 = 1955839) B1955839
theorem B6187751 : Blo 1220928 6187751 := bstep (se 1 (by rfl) ⟨4640813, by rfl⟩ : syracuseStep 6187751 = 9281627) B9281627
theorem B2747447 : Blo 1220928 2747447 := bstep (se 1 (by rfl) ⟨2060585, by rfl⟩ : syracuseStep 2747447 = 4121171) B4121171
theorem B2321615 : Blo 1220928 2321615 := bstep (se 1 (by rfl) ⟨1741211, by rfl⟩ : syracuseStep 2321615 = 3482423) B3482423
theorem B56479139 : Blo 1220928 56479139 := bstep (se 1 (by rfl) ⟨42359354, by rfl⟩ : syracuseStep 56479139 = 84718709) B84718709
theorem B10440191 : Blo 1220928 10440191 := bstep (se 1 (by rfl) ⟨7830143, by rfl⟩ : syracuseStep 10440191 = 15660287) B15660287
theorem B14855699 : Blo 1220928 14855699 := bstep (se 1 (by rfl) ⟨11141774, by rfl⟩ : syracuseStep 14855699 = 22283549) B22283549
theorem B31749569 : Blo 1220928 31749569 := bstep (se 2 (by rfl) ⟨11906088, by rfl⟩ : syracuseStep 31749569 = 23812177) B23812177
theorem B89159615 : Blo 1220928 89159615 := bstep (se 1 (by rfl) ⟨66869711, by rfl⟩ : syracuseStep 89159615 = 133739423) B133739423
theorem B7428095 : Blo 1220928 7428095 := bstep (se 1 (by rfl) ⟨5571071, by rfl⟩ : syracuseStep 7428095 = 11142143) B11142143
theorem B1374619 : Blo 1220928 1374619 := bstep (se 1 (by rfl) ⟨1030964, by rfl⟩ : syracuseStep 1374619 = 2061929) B2061929
theorem B1833371 : Blo 1220928 1833371 := bstep (se 1 (by rfl) ⟨1375028, by rfl⟩ : syracuseStep 1833371 = 2750057) B2750057
theorem B3136295 : Blo 1220928 3136295 := bstep (se 1 (by rfl) ⟨2352221, by rfl⟩ : syracuseStep 3136295 = 4704443) B4704443
theorem B2751335 : Blo 1220928 2751335 := bstep (se 1 (by rfl) ⟨2063501, by rfl⟩ : syracuseStep 2751335 = 4127003) B4127003
theorem B19823687 : Blo 1220928 19823687 := bstep (se 1 (by rfl) ⟨14867765, by rfl⟩ : syracuseStep 19823687 = 29735531) B29735531
theorem B4701671 : Blo 1220928 4701671 := bstep (se 1 (by rfl) ⟨3526253, by rfl⟩ : syracuseStep 4701671 = 7052507) B7052507
theorem B1222247 : Blo 1220928 1222247 := bstep (se 1 (by rfl) ⟨916685, by rfl⟩ : syracuseStep 1222247 = 1833371) B1833371
theorem B1738523 : Blo 1220928 1738523 := bstep (se 1 (by rfl) ⟨1303892, by rfl⟩ : syracuseStep 1738523 = 2607785) B2607785
theorem B2090863 : Blo 1220928 2090863 := bstep (se 1 (by rfl) ⟨1568147, by rfl⟩ : syracuseStep 2090863 = 3136295) B3136295
theorem B13215791 : Blo 1220928 13215791 := bstep (se 1 (by rfl) ⟨9911843, by rfl⟩ : syracuseStep 13215791 = 19823687) B19823687
theorem B37652759 : Blo 1220928 37652759 := bstep (se 1 (by rfl) ⟨28239569, by rfl⟩ : syracuseStep 37652759 = 56479139) B56479139
theorem B4952063 : Blo 1220928 4952063 := bstep (se 1 (by rfl) ⟨3714047, by rfl⟩ : syracuseStep 4952063 = 7428095) B7428095
theorem B4125167 : Blo 1220928 4125167 := bstep (se 1 (by rfl) ⟨3093875, by rfl⟩ : syracuseStep 4125167 = 6187751) B6187751
theorem B1831631 : Blo 1220928 1831631 := bstep (se 1 (by rfl) ⟨1373723, by rfl⟩ : syracuseStep 1831631 = 2747447) B2747447
theorem B3134447 : Blo 1220928 3134447 := bstep (se 1 (by rfl) ⟨2350835, by rfl⟩ : syracuseStep 3134447 = 4701671) B4701671
theorem B6960127 : Blo 1220928 6960127 := bstep (se 1 (by rfl) ⟨5220095, by rfl⟩ : syracuseStep 6960127 = 10440191) B10440191
theorem B1832825 : Blo 1220928 1832825 := bstep (se 2 (by rfl) ⟨687309, by rfl⟩ : syracuseStep 1832825 = 1374619) B1374619
theorem B4642697 : Blo 1220928 4642697 := bstep (se 2 (by rfl) ⟨1741011, by rfl⟩ : syracuseStep 4642697 = 3482023) B3482023
theorem B21166379 : Blo 1220928 21166379 := bstep (se 1 (by rfl) ⟨15874784, by rfl⟩ : syracuseStep 21166379 = 31749569) B31749569
theorem B59439743 : Blo 1220928 59439743 := bstep (se 1 (by rfl) ⟨44579807, by rfl⟩ : syracuseStep 59439743 = 89159615) B89159615
theorem B3480383 : Blo 1220928 3480383 := bstep (se 1 (by rfl) ⟨2610287, by rfl⟩ : syracuseStep 3480383 = 5220575) B5220575
theorem B1834223 : Blo 1220928 1834223 := bstep (se 1 (by rfl) ⟨1375667, by rfl⟩ : syracuseStep 1834223 = 2751335) B2751335
theorem B1547743 : Blo 1220928 1547743 := bstep (se 1 (by rfl) ⟨1160807, by rfl⟩ : syracuseStep 1547743 = 2321615) B2321615
theorem B9903799 : Blo 1220928 9903799 := bstep (se 1 (by rfl) ⟨7427849, by rfl⟩ : syracuseStep 9903799 = 14855699) B14855699
theorem B1221087 : Blo 1220928 1221087 := bstep (se 1 (by rfl) ⟨915815, by rfl⟩ : syracuseStep 1221087 = 1831631) B1831631
theorem B2089631 : Blo 1220928 2089631 := bstep (se 1 (by rfl) ⟨1567223, by rfl⟩ : syracuseStep 2089631 = 3134447) B3134447
theorem B1221883 : Blo 1220928 1221883 := bstep (se 1 (by rfl) ⟨916412, by rfl⟩ : syracuseStep 1221883 = 1832825) B1832825
theorem B25101839 : Blo 1220928 25101839 := bstep (se 1 (by rfl) ⟨18826379, by rfl⟩ : syracuseStep 25101839 = 37652759) B37652759
theorem B39626495 : Blo 1220928 39626495 := bstep (se 1 (by rfl) ⟨29719871, by rfl⟩ : syracuseStep 39626495 = 59439743) B59439743
theorem B2320255 : Blo 1220928 2320255 := bstep (se 1 (by rfl) ⟨1740191, by rfl⟩ : syracuseStep 2320255 = 3480383) B3480383
theorem B11151269 : Blo 1220928 11151269 := bstep (se 4 (by rfl) ⟨1045431, by rfl⟩ : syracuseStep 11151269 = 2090863) B2090863
theorem B1222815 : Blo 1220928 1222815 := bstep (se 1 (by rfl) ⟨917111, by rfl⟩ : syracuseStep 1222815 = 1834223) B1834223
theorem B8810527 : Blo 1220928 8810527 := bstep (se 1 (by rfl) ⟨6607895, by rfl⟩ : syracuseStep 8810527 = 13215791) B13215791
theorem B14110919 : Blo 1220928 14110919 := bstep (se 1 (by rfl) ⟨10583189, by rfl⟩ : syracuseStep 14110919 = 21166379) B21166379
theorem B2750111 : Blo 1220928 2750111 := bstep (se 1 (by rfl) ⟨2062583, by rfl⟩ : syracuseStep 2750111 = 4125167) B4125167
theorem B3095131 : Blo 1220928 3095131 := bstep (se 1 (by rfl) ⟨2321348, by rfl⟩ : syracuseStep 3095131 = 4642697) B4642697
theorem B9280169 : Blo 1220928 9280169 := bstep (se 2 (by rfl) ⟨3480063, by rfl⟩ : syracuseStep 9280169 = 6960127) B6960127
theorem B2063657 : Blo 1220928 2063657 := bstep (se 2 (by rfl) ⟨773871, by rfl⟩ : syracuseStep 2063657 = 1547743) B1547743
theorem B4636061 : Blo 1220928 4636061 := bstep (se 3 (by rfl) ⟨869261, by rfl⟩ : syracuseStep 4636061 = 1738523) B1738523
theorem B13205065 : Blo 1220928 13205065 := bstep (se 2 (by rfl) ⟨4951899, by rfl⟩ : syracuseStep 13205065 = 9903799) B9903799
theorem B13205501 : Blo 1220928 13205501 := bstep (se 3 (by rfl) ⟨2476031, by rfl⟩ : syracuseStep 13205501 = 4952063) B4952063
theorem B11747369 : Blo 1220928 11747369 := bstep (se 2 (by rfl) ⟨4405263, by rfl⟩ : syracuseStep 11747369 = 8810527) B8810527
theorem B1393087 : Blo 1220928 1393087 := bstep (se 1 (by rfl) ⟨1044815, by rfl⟩ : syracuseStep 1393087 = 2089631) B2089631
theorem B6186779 : Blo 1220928 6186779 := bstep (se 1 (by rfl) ⟨4640084, by rfl⟩ : syracuseStep 6186779 = 9280169) B9280169
theorem B17606753 : Blo 1220928 17606753 := bstep (se 2 (by rfl) ⟨6602532, by rfl⟩ : syracuseStep 17606753 = 13205065) B13205065
theorem B3090707 : Blo 1220928 3090707 := bstep (se 1 (by rfl) ⟨2318030, by rfl⟩ : syracuseStep 3090707 = 4636061) B4636061
theorem B9407279 : Blo 1220928 9407279 := bstep (se 1 (by rfl) ⟨7055459, by rfl⟩ : syracuseStep 9407279 = 14110919) B14110919
theorem B7434179 : Blo 1220928 7434179 := bstep (se 1 (by rfl) ⟨5575634, by rfl⟩ : syracuseStep 7434179 = 11151269) B11151269
theorem B3093673 : Blo 1220928 3093673 := bstep (se 2 (by rfl) ⟨1160127, by rfl⟩ : syracuseStep 3093673 = 2320255) B2320255
theorem B8803667 : Blo 1220928 8803667 := bstep (se 1 (by rfl) ⟨6602750, by rfl⟩ : syracuseStep 8803667 = 13205501) B13205501
theorem B4126841 : Blo 1220928 4126841 := bstep (se 2 (by rfl) ⟨1547565, by rfl⟩ : syracuseStep 4126841 = 3095131) B3095131
theorem B16734559 : Blo 1220928 16734559 := bstep (se 1 (by rfl) ⟨12550919, by rfl⟩ : syracuseStep 16734559 = 25101839) B25101839
theorem B1833407 : Blo 1220928 1833407 := bstep (se 1 (by rfl) ⟨1375055, by rfl⟩ : syracuseStep 1833407 = 2750111) B2750111
theorem B26417663 : Blo 1220928 26417663 := bstep (se 1 (by rfl) ⟨19813247, by rfl⟩ : syracuseStep 26417663 = 39626495) B39626495
theorem B1375771 : Blo 1220928 1375771 := bstep (se 1 (by rfl) ⟨1031828, by rfl⟩ : syracuseStep 1375771 = 2063657) B2063657
theorem B7831579 : Blo 1220928 7831579 := bstep (se 1 (by rfl) ⟨5873684, by rfl⟩ : syracuseStep 7831579 = 11747369) B11747369
theorem B1222271 : Blo 1220928 1222271 := bstep (se 1 (by rfl) ⟨916703, by rfl⟩ : syracuseStep 1222271 = 1833407) B1833407
theorem B5869111 : Blo 1220928 5869111 := bstep (se 1 (by rfl) ⟨4401833, by rfl⟩ : syracuseStep 5869111 = 8803667) B8803667
theorem B4124519 : Blo 1220928 4124519 := bstep (se 1 (by rfl) ⟨3093389, by rfl⟩ : syracuseStep 4124519 = 6186779) B6186779
theorem B2060471 : Blo 1220928 2060471 := bstep (se 1 (by rfl) ⟨1545353, by rfl⟩ : syracuseStep 2060471 = 3090707) B3090707
theorem B4124897 : Blo 1220928 4124897 := bstep (se 2 (by rfl) ⟨1546836, by rfl⟩ : syracuseStep 4124897 = 3093673) B3093673
theorem B6271519 : Blo 1220928 6271519 := bstep (se 1 (by rfl) ⟨4703639, by rfl⟩ : syracuseStep 6271519 = 9407279) B9407279
theorem B22312745 : Blo 1220928 22312745 := bstep (se 2 (by rfl) ⟨8367279, by rfl⟩ : syracuseStep 22312745 = 16734559) B16734559
theorem B1857449 : Blo 1220928 1857449 := bstep (se 2 (by rfl) ⟨696543, by rfl⟩ : syracuseStep 1857449 = 1393087) B1393087
theorem B11737835 : Blo 1220928 11737835 := bstep (se 1 (by rfl) ⟨8803376, by rfl⟩ : syracuseStep 11737835 = 17606753) B17606753
theorem B2751227 : Blo 1220928 2751227 := bstep (se 1 (by rfl) ⟨2063420, by rfl⟩ : syracuseStep 2751227 = 4126841) B4126841
theorem B17611775 : Blo 1220928 17611775 := bstep (se 1 (by rfl) ⟨13208831, by rfl⟩ : syracuseStep 17611775 = 26417663) B26417663
theorem B1834361 : Blo 1220928 1834361 := bstep (se 2 (by rfl) ⟨687885, by rfl⟩ : syracuseStep 1834361 = 1375771) B1375771
theorem B4956119 : Blo 1220928 4956119 := bstep (se 1 (by rfl) ⟨3717089, by rfl⟩ : syracuseStep 4956119 = 7434179) B7434179
theorem B7825223 : Blo 1220928 7825223 := bstep (se 1 (by rfl) ⟨5868917, by rfl⟩ : syracuseStep 7825223 = 11737835) B11737835
theorem B11741183 : Blo 1220928 11741183 := bstep (se 1 (by rfl) ⟨8805887, by rfl⟩ : syracuseStep 11741183 = 17611775) B17611775
theorem B7825481 : Blo 1220928 7825481 := bstep (se 2 (by rfl) ⟨2934555, by rfl⟩ : syracuseStep 7825481 = 5869111) B5869111
theorem B1222907 : Blo 1220928 1222907 := bstep (se 1 (by rfl) ⟨917180, by rfl⟩ : syracuseStep 1222907 = 1834361) B1834361
theorem B3304079 : Blo 1220928 3304079 := bstep (se 1 (by rfl) ⟨2478059, by rfl⟩ : syracuseStep 3304079 = 4956119) B4956119
theorem B4953197 : Blo 1220928 4953197 := bstep (se 3 (by rfl) ⟨928724, by rfl⟩ : syracuseStep 4953197 = 1857449) B1857449
theorem B2749679 : Blo 1220928 2749679 := bstep (se 1 (by rfl) ⟨2062259, by rfl⟩ : syracuseStep 2749679 = 4124519) B4124519
theorem B10442105 : Blo 1220928 10442105 := bstep (se 2 (by rfl) ⟨3915789, by rfl⟩ : syracuseStep 10442105 = 7831579) B7831579
theorem B1373647 : Blo 1220928 1373647 := bstep (se 1 (by rfl) ⟨1030235, by rfl⟩ : syracuseStep 1373647 = 2060471) B2060471
theorem B2749931 : Blo 1220928 2749931 := bstep (se 1 (by rfl) ⟨2062448, by rfl⟩ : syracuseStep 2749931 = 4124897) B4124897
theorem B8362025 : Blo 1220928 8362025 := bstep (se 2 (by rfl) ⟨3135759, by rfl⟩ : syracuseStep 8362025 = 6271519) B6271519
theorem B14875163 : Blo 1220928 14875163 := bstep (se 1 (by rfl) ⟨11156372, by rfl⟩ : syracuseStep 14875163 = 22312745) B22312745
theorem B1834151 : Blo 1220928 1834151 := bstep (se 1 (by rfl) ⟨1375613, by rfl⟩ : syracuseStep 1834151 = 2751227) B2751227
theorem B3302131 : Blo 1220928 3302131 := bstep (se 1 (by rfl) ⟨2476598, by rfl⟩ : syracuseStep 3302131 = 4953197) B4953197
theorem B1222767 : Blo 1220928 1222767 := bstep (se 1 (by rfl) ⟨917075, by rfl⟩ : syracuseStep 1222767 = 1834151) B1834151
theorem B7827455 : Blo 1220928 7827455 := bstep (se 1 (by rfl) ⟨5870591, by rfl⟩ : syracuseStep 7827455 = 11741183) B11741183
theorem B5574683 : Blo 1220928 5574683 := bstep (se 1 (by rfl) ⟨4181012, by rfl⟩ : syracuseStep 5574683 = 8362025) B8362025
theorem B9916775 : Blo 1220928 9916775 := bstep (se 1 (by rfl) ⟨7437581, by rfl⟩ : syracuseStep 9916775 = 14875163) B14875163
theorem B1831529 : Blo 1220928 1831529 := bstep (se 2 (by rfl) ⟨686823, by rfl⟩ : syracuseStep 1831529 = 1373647) B1373647
theorem B1833119 : Blo 1220928 1833119 := bstep (se 1 (by rfl) ⟨1374839, by rfl⟩ : syracuseStep 1833119 = 2749679) B2749679
theorem B6961403 : Blo 1220928 6961403 := bstep (se 1 (by rfl) ⟨5221052, by rfl⟩ : syracuseStep 6961403 = 10442105) B10442105
theorem B1833287 : Blo 1220928 1833287 := bstep (se 1 (by rfl) ⟨1374965, by rfl⟩ : syracuseStep 1833287 = 2749931) B2749931
theorem B5216815 : Blo 1220928 5216815 := bstep (se 1 (by rfl) ⟨3912611, by rfl⟩ : syracuseStep 5216815 = 7825223) B7825223
theorem B5216987 : Blo 1220928 5216987 := bstep (se 1 (by rfl) ⟨3912740, by rfl⟩ : syracuseStep 5216987 = 7825481) B7825481
theorem B2202719 : Blo 1220928 2202719 := bstep (se 1 (by rfl) ⟨1652039, by rfl⟩ : syracuseStep 2202719 = 3304079) B3304079
theorem B6611183 : Blo 1220928 6611183 := bstep (se 1 (by rfl) ⟨4958387, by rfl⟩ : syracuseStep 6611183 = 9916775) B9916775
theorem B5873917 : Blo 1220928 5873917 := bstep (se 3 (by rfl) ⟨1101359, by rfl⟩ : syracuseStep 5873917 = 2202719) B2202719
theorem B1221019 : Blo 1220928 1221019 := bstep (se 1 (by rfl) ⟨915764, by rfl⟩ : syracuseStep 1221019 = 1831529) B1831529
theorem B6955753 : Blo 1220928 6955753 := bstep (se 2 (by rfl) ⟨2608407, by rfl⟩ : syracuseStep 6955753 = 5216815) B5216815
theorem B1222079 : Blo 1220928 1222079 := bstep (se 1 (by rfl) ⟨916559, by rfl⟩ : syracuseStep 1222079 = 1833119) B1833119
theorem B1222191 : Blo 1220928 1222191 := bstep (se 1 (by rfl) ⟨916643, by rfl⟩ : syracuseStep 1222191 = 1833287) B1833287
theorem B4402841 : Blo 1220928 4402841 := bstep (se 2 (by rfl) ⟨1651065, by rfl⟩ : syracuseStep 4402841 = 3302131) B3302131
theorem B4640935 : Blo 1220928 4640935 := bstep (se 1 (by rfl) ⟨3480701, by rfl⟩ : syracuseStep 4640935 = 6961403) B6961403
theorem B3477991 : Blo 1220928 3477991 := bstep (se 1 (by rfl) ⟨2608493, by rfl⟩ : syracuseStep 3477991 = 5216987) B5216987
theorem B3716455 : Blo 1220928 3716455 := bstep (se 1 (by rfl) ⟨2787341, by rfl⟩ : syracuseStep 3716455 = 5574683) B5574683
theorem B5218303 : Blo 1220928 5218303 := bstep (se 1 (by rfl) ⟨3913727, by rfl⟩ : syracuseStep 5218303 = 7827455) B7827455
theorem B4407455 : Blo 1220928 4407455 := bstep (se 1 (by rfl) ⟨3305591, by rfl⟩ : syracuseStep 4407455 = 6611183) B6611183
theorem B7831889 : Blo 1220928 7831889 := bstep (se 2 (by rfl) ⟨2936958, by rfl⟩ : syracuseStep 7831889 = 5873917) B5873917
theorem B4637321 : Blo 1220928 4637321 := bstep (se 2 (by rfl) ⟨1738995, by rfl⟩ : syracuseStep 4637321 = 3477991) B3477991
theorem B9274337 : Blo 1220928 9274337 := bstep (se 2 (by rfl) ⟨3477876, by rfl⟩ : syracuseStep 9274337 = 6955753) B6955753
theorem B6957737 : Blo 1220928 6957737 := bstep (se 2 (by rfl) ⟨2609151, by rfl⟩ : syracuseStep 6957737 = 5218303) B5218303
theorem B6187913 : Blo 1220928 6187913 := bstep (se 2 (by rfl) ⟨2320467, by rfl⟩ : syracuseStep 6187913 = 4640935) B4640935
theorem B46963637 : Blo 1220928 46963637 := bstep (se 5 (by rfl) ⟨2201420, by rfl⟩ : syracuseStep 46963637 = 4402841) B4402841
theorem B4955273 : Blo 1220928 4955273 := bstep (se 2 (by rfl) ⟨1858227, by rfl⟩ : syracuseStep 4955273 = 3716455) B3716455
theorem B4638491 : Blo 1220928 4638491 := bstep (se 1 (by rfl) ⟨3478868, by rfl⟩ : syracuseStep 4638491 = 6957737) B6957737
theorem B3303515 : Blo 1220928 3303515 := bstep (se 1 (by rfl) ⟨2477636, by rfl⟩ : syracuseStep 3303515 = 4955273) B4955273
theorem B5221259 : Blo 1220928 5221259 := bstep (se 1 (by rfl) ⟨3915944, by rfl⟩ : syracuseStep 5221259 = 7831889) B7831889
theorem B3091547 : Blo 1220928 3091547 := bstep (se 1 (by rfl) ⟨2318660, by rfl⟩ : syracuseStep 3091547 = 4637321) B4637321
theorem B4125275 : Blo 1220928 4125275 := bstep (se 1 (by rfl) ⟨3093956, by rfl⟩ : syracuseStep 4125275 = 6187913) B6187913
theorem B2938303 : Blo 1220928 2938303 := bstep (se 1 (by rfl) ⟨2203727, by rfl⟩ : syracuseStep 2938303 = 4407455) B4407455
theorem B6182891 : Blo 1220928 6182891 := bstep (se 1 (by rfl) ⟨4637168, by rfl⟩ : syracuseStep 6182891 = 9274337) B9274337
theorem B31309091 : Blo 1220928 31309091 := bstep (se 1 (by rfl) ⟨23481818, by rfl⟩ : syracuseStep 31309091 = 46963637) B46963637
theorem B4121927 : Blo 1220928 4121927 := bstep (se 1 (by rfl) ⟨3091445, by rfl⟩ : syracuseStep 4121927 = 6182891) B6182891
theorem B3917737 : Blo 1220928 3917737 := bstep (se 2 (by rfl) ⟨1469151, by rfl⟩ : syracuseStep 3917737 = 2938303) B2938303
theorem B8809373 : Blo 1220928 8809373 := bstep (se 3 (by rfl) ⟨1651757, by rfl⟩ : syracuseStep 8809373 = 3303515) B3303515
theorem B3092327 : Blo 1220928 3092327 := bstep (se 1 (by rfl) ⟨2319245, by rfl⟩ : syracuseStep 3092327 = 4638491) B4638491
theorem B2061031 : Blo 1220928 2061031 := bstep (se 1 (by rfl) ⟨1545773, by rfl⟩ : syracuseStep 2061031 = 3091547) B3091547
theorem B2750183 : Blo 1220928 2750183 := bstep (se 1 (by rfl) ⟨2062637, by rfl⟩ : syracuseStep 2750183 = 4125275) B4125275
theorem B3480839 : Blo 1220928 3480839 := bstep (se 1 (by rfl) ⟨2610629, by rfl⟩ : syracuseStep 3480839 = 5221259) B5221259
theorem B20872727 : Blo 1220928 20872727 := bstep (se 1 (by rfl) ⟨15654545, by rfl⟩ : syracuseStep 20872727 = 31309091) B31309091
theorem B2320559 : Blo 1220928 2320559 := bstep (se 1 (by rfl) ⟨1740419, by rfl⟩ : syracuseStep 2320559 = 3480839) B3480839
theorem B2747951 : Blo 1220928 2747951 := bstep (se 1 (by rfl) ⟨2060963, by rfl⟩ : syracuseStep 2747951 = 4121927) B4121927
theorem B2748041 : Blo 1220928 2748041 := bstep (se 2 (by rfl) ⟨1030515, by rfl⟩ : syracuseStep 2748041 = 2061031) B2061031
theorem B20894597 : Blo 1220928 20894597 := bstep (se 4 (by rfl) ⟨1958868, by rfl⟩ : syracuseStep 20894597 = 3917737) B3917737
theorem B13915151 : Blo 1220928 13915151 := bstep (se 1 (by rfl) ⟨10436363, by rfl⟩ : syracuseStep 13915151 = 20872727) B20872727
theorem B2061551 : Blo 1220928 2061551 := bstep (se 1 (by rfl) ⟨1546163, by rfl⟩ : syracuseStep 2061551 = 3092327) B3092327
theorem B1833455 : Blo 1220928 1833455 := bstep (se 1 (by rfl) ⟨1375091, by rfl⟩ : syracuseStep 1833455 = 2750183) B2750183
theorem B5872915 : Blo 1220928 5872915 := bstep (se 1 (by rfl) ⟨4404686, by rfl⟩ : syracuseStep 5872915 = 8809373) B8809373
theorem B1222303 : Blo 1220928 1222303 := bstep (se 1 (by rfl) ⟨916727, by rfl⟩ : syracuseStep 1222303 = 1833455) B1833455
theorem B13929731 : Blo 1220928 13929731 := bstep (se 1 (by rfl) ⟨10447298, by rfl⟩ : syracuseStep 13929731 = 20894597) B20894597
theorem B9276767 : Blo 1220928 9276767 := bstep (se 1 (by rfl) ⟨6957575, by rfl⟩ : syracuseStep 9276767 = 13915151) B13915151
theorem B31322213 : Blo 1220928 31322213 := bstep (se 4 (by rfl) ⟨2936457, by rfl⟩ : syracuseStep 31322213 = 5872915) B5872915
theorem B1831967 : Blo 1220928 1831967 := bstep (se 1 (by rfl) ⟨1373975, by rfl⟩ : syracuseStep 1831967 = 2747951) B2747951
theorem B1832027 : Blo 1220928 1832027 := bstep (se 1 (by rfl) ⟨1374020, by rfl⟩ : syracuseStep 1832027 = 2748041) B2748041
theorem B1374367 : Blo 1220928 1374367 := bstep (se 1 (by rfl) ⟨1030775, by rfl⟩ : syracuseStep 1374367 = 2061551) B2061551
theorem B1547039 : Blo 1220928 1547039 := bstep (se 1 (by rfl) ⟨1160279, by rfl⟩ : syracuseStep 1547039 = 2320559) B2320559
theorem B20881475 : Blo 1220928 20881475 := bstep (se 1 (by rfl) ⟨15661106, by rfl⟩ : syracuseStep 20881475 = 31322213) B31322213
theorem B1221311 : Blo 1220928 1221311 := bstep (se 1 (by rfl) ⟨915983, by rfl⟩ : syracuseStep 1221311 = 1831967) B1831967
theorem B1221351 : Blo 1220928 1221351 := bstep (se 1 (by rfl) ⟨916013, by rfl⟩ : syracuseStep 1221351 = 1832027) B1832027
theorem B4125437 : Blo 1220928 4125437 := bstep (se 3 (by rfl) ⟨773519, by rfl⟩ : syracuseStep 4125437 = 1547039) B1547039
theorem B9286487 : Blo 1220928 9286487 := bstep (se 1 (by rfl) ⟨6964865, by rfl⟩ : syracuseStep 9286487 = 13929731) B13929731
theorem B1832489 : Blo 1220928 1832489 := bstep (se 2 (by rfl) ⟨687183, by rfl⟩ : syracuseStep 1832489 = 1374367) B1374367
theorem B6184511 : Blo 1220928 6184511 := bstep (se 1 (by rfl) ⟨4638383, by rfl⟩ : syracuseStep 6184511 = 9276767) B9276767
theorem B1221659 : Blo 1220928 1221659 := bstep (se 1 (by rfl) ⟨916244, by rfl⟩ : syracuseStep 1221659 = 1832489) B1832489
theorem B4123007 : Blo 1220928 4123007 := bstep (se 1 (by rfl) ⟨3092255, by rfl⟩ : syracuseStep 4123007 = 6184511) B6184511
theorem B13920983 : Blo 1220928 13920983 := bstep (se 1 (by rfl) ⟨10440737, by rfl⟩ : syracuseStep 13920983 = 20881475) B20881475
theorem B2750291 : Blo 1220928 2750291 := bstep (se 1 (by rfl) ⟨2062718, by rfl⟩ : syracuseStep 2750291 = 4125437) B4125437
theorem B6190991 : Blo 1220928 6190991 := bstep (se 1 (by rfl) ⟨4643243, by rfl⟩ : syracuseStep 6190991 = 9286487) B9286487
theorem B2748671 : Blo 1220928 2748671 := bstep (se 1 (by rfl) ⟨2061503, by rfl⟩ : syracuseStep 2748671 = 4123007) B4123007
theorem B1833527 : Blo 1220928 1833527 := bstep (se 1 (by rfl) ⟨1375145, by rfl⟩ : syracuseStep 1833527 = 2750291) B2750291
theorem B4127327 : Blo 1220928 4127327 := bstep (se 1 (by rfl) ⟨3095495, by rfl⟩ : syracuseStep 4127327 = 6190991) B6190991
theorem B9280655 : Blo 1220928 9280655 := bstep (se 1 (by rfl) ⟨6960491, by rfl⟩ : syracuseStep 9280655 = 13920983) B13920983
theorem B1222351 : Blo 1220928 1222351 := bstep (se 1 (by rfl) ⟨916763, by rfl⟩ : syracuseStep 1222351 = 1833527) B1833527
theorem B6187103 : Blo 1220928 6187103 := bstep (se 1 (by rfl) ⟨4640327, by rfl⟩ : syracuseStep 6187103 = 9280655) B9280655
theorem B1832447 : Blo 1220928 1832447 := bstep (se 1 (by rfl) ⟨1374335, by rfl⟩ : syracuseStep 1832447 = 2748671) B2748671
theorem B2751551 : Blo 1220928 2751551 := bstep (se 1 (by rfl) ⟨2063663, by rfl⟩ : syracuseStep 2751551 = 4127327) B4127327
theorem B1221631 : Blo 1220928 1221631 := bstep (se 1 (by rfl) ⟨916223, by rfl⟩ : syracuseStep 1221631 = 1832447) B1832447
theorem B4124735 : Blo 1220928 4124735 := bstep (se 1 (by rfl) ⟨3093551, by rfl⟩ : syracuseStep 4124735 = 6187103) B6187103
theorem B1834367 : Blo 1220928 1834367 := bstep (se 1 (by rfl) ⟨1375775, by rfl⟩ : syracuseStep 1834367 = 2751551) B2751551
theorem B1222911 : Blo 1220928 1222911 := bstep (se 1 (by rfl) ⟨917183, by rfl⟩ : syracuseStep 1222911 = 1834367) B1834367
theorem B2749823 : Blo 1220928 2749823 := bstep (se 1 (by rfl) ⟨2062367, by rfl⟩ : syracuseStep 2749823 = 4124735) B4124735
theorem B1833215 : Blo 1220928 1833215 := bstep (se 1 (by rfl) ⟨1374911, by rfl⟩ : syracuseStep 1833215 = 2749823) B2749823
theorem B1222143 : Blo 1220928 1222143 := bstep (se 1 (by rfl) ⟨916607, by rfl⟩ : syracuseStep 1222143 = 1833215) B1833215

theorem C0 (j : ℕ) (h1 : 305232 ≤ j) (h2 : j ≤ 305731) : Blo 1220928 (4 * j + 3) := by
  interval_cases j
  · exact B1220931
  · exact B1220935
  · exact B1220939
  · exact B1220943
  · exact B1220947
  · exact B1220951
  · exact B1220955
  · exact B1220959
  · exact B1220963
  · exact B1220967
  · exact B1220971
  · exact B1220975
  · exact B1220979
  · exact B1220983
  · exact B1220987
  · exact B1220991
  · exact B1220995
  · exact B1220999
  · exact B1221003
  · exact B1221007
  · exact B1221011
  · exact B1221015
  · exact B1221019
  · exact B1221023
  · exact B1221027
  · exact B1221031
  · exact B1221035
  · exact B1221039
  · exact B1221043
  · exact B1221047
  · exact B1221051
  · exact B1221055
  · exact B1221059
  · exact B1221063
  · exact B1221067
  · exact B1221071
  · exact B1221075
  · exact B1221079
  · exact B1221083
  · exact B1221087
  · exact B1221091
  · exact B1221095
  · exact B1221099
  · exact B1221103
  · exact B1221107
  · exact B1221111
  · exact B1221115
  · exact B1221119
  · exact B1221123
  · exact B1221127
  · exact B1221131
  · exact B1221135
  · exact B1221139
  · exact B1221143
  · exact B1221147
  · exact B1221151
  · exact B1221155
  · exact B1221159
  · exact B1221163
  · exact B1221167
  · exact B1221171
  · exact B1221175
  · exact B1221179
  · exact B1221183
  · exact B1221187
  · exact B1221191
  · exact B1221195
  · exact B1221199
  · exact B1221203
  · exact B1221207
  · exact B1221211
  · exact B1221215
  · exact B1221219
  · exact B1221223
  · exact B1221227
  · exact B1221231
  · exact B1221235
  · exact B1221239
  · exact B1221243
  · exact B1221247
  · exact B1221251
  · exact B1221255
  · exact B1221259
  · exact B1221263
  · exact B1221267
  · exact B1221271
  · exact B1221275
  · exact B1221279
  · exact B1221283
  · exact B1221287
  · exact B1221291
  · exact B1221295
  · exact B1221299
  · exact B1221303
  · exact B1221307
  · exact B1221311
  · exact B1221315
  · exact B1221319
  · exact B1221323
  · exact B1221327
  · exact B1221331
  · exact B1221335
  · exact B1221339
  · exact B1221343
  · exact B1221347
  · exact B1221351
  · exact B1221355
  · exact B1221359
  · exact B1221363
  · exact B1221367
  · exact B1221371
  · exact B1221375
  · exact B1221379
  · exact B1221383
  · exact B1221387
  · exact B1221391
  · exact B1221395
  · exact B1221399
  · exact B1221403
  · exact B1221407
  · exact B1221411
  · exact B1221415
  · exact B1221419
  · exact B1221423
  · exact B1221427
  · exact B1221431
  · exact B1221435
  · exact B1221439
  · exact B1221443
  · exact B1221447
  · exact B1221451
  · exact B1221455
  · exact B1221459
  · exact B1221463
  · exact B1221467
  · exact B1221471
  · exact B1221475
  · exact B1221479
  · exact B1221483
  · exact B1221487
  · exact B1221491
  · exact B1221495
  · exact B1221499
  · exact B1221503
  · exact B1221507
  · exact B1221511
  · exact B1221515
  · exact B1221519
  · exact B1221523
  · exact B1221527
  · exact B1221531
  · exact B1221535
  · exact B1221539
  · exact B1221543
  · exact B1221547
  · exact B1221551
  · exact B1221555
  · exact B1221559
  · exact B1221563
  · exact B1221567
  · exact B1221571
  · exact B1221575
  · exact B1221579
  · exact B1221583
  · exact B1221587
  · exact B1221591
  · exact B1221595
  · exact B1221599
  · exact B1221603
  · exact B1221607
  · exact B1221611
  · exact B1221615
  · exact B1221619
  · exact B1221623
  · exact B1221627
  · exact B1221631
  · exact B1221635
  · exact B1221639
  · exact B1221643
  · exact B1221647
  · exact B1221651
  · exact B1221655
  · exact B1221659
  · exact B1221663
  · exact B1221667
  · exact B1221671
  · exact B1221675
  · exact B1221679
  · exact B1221683
  · exact B1221687
  · exact B1221691
  · exact B1221695
  · exact B1221699
  · exact B1221703
  · exact B1221707
  · exact B1221711
  · exact B1221715
  · exact B1221719
  · exact B1221723
  · exact B1221727
  · exact B1221731
  · exact B1221735
  · exact B1221739
  · exact B1221743
  · exact B1221747
  · exact B1221751
  · exact B1221755
  · exact B1221759
  · exact B1221763
  · exact B1221767
  · exact B1221771
  · exact B1221775
  · exact B1221779
  · exact B1221783
  · exact B1221787
  · exact B1221791
  · exact B1221795
  · exact B1221799
  · exact B1221803
  · exact B1221807
  · exact B1221811
  · exact B1221815
  · exact B1221819
  · exact B1221823
  · exact B1221827
  · exact B1221831
  · exact B1221835
  · exact B1221839
  · exact B1221843
  · exact B1221847
  · exact B1221851
  · exact B1221855
  · exact B1221859
  · exact B1221863
  · exact B1221867
  · exact B1221871
  · exact B1221875
  · exact B1221879
  · exact B1221883
  · exact B1221887
  · exact B1221891
  · exact B1221895
  · exact B1221899
  · exact B1221903
  · exact B1221907
  · exact B1221911
  · exact B1221915
  · exact B1221919
  · exact B1221923
  · exact B1221927
  · exact B1221931
  · exact B1221935
  · exact B1221939
  · exact B1221943
  · exact B1221947
  · exact B1221951
  · exact B1221955
  · exact B1221959
  · exact B1221963
  · exact B1221967
  · exact B1221971
  · exact B1221975
  · exact B1221979
  · exact B1221983
  · exact B1221987
  · exact B1221991
  · exact B1221995
  · exact B1221999
  · exact B1222003
  · exact B1222007
  · exact B1222011
  · exact B1222015
  · exact B1222019
  · exact B1222023
  · exact B1222027
  · exact B1222031
  · exact B1222035
  · exact B1222039
  · exact B1222043
  · exact B1222047
  · exact B1222051
  · exact B1222055
  · exact B1222059
  · exact B1222063
  · exact B1222067
  · exact B1222071
  · exact B1222075
  · exact B1222079
  · exact B1222083
  · exact B1222087
  · exact B1222091
  · exact B1222095
  · exact B1222099
  · exact B1222103
  · exact B1222107
  · exact B1222111
  · exact B1222115
  · exact B1222119
  · exact B1222123
  · exact B1222127
  · exact B1222131
  · exact B1222135
  · exact B1222139
  · exact B1222143
  · exact B1222147
  · exact B1222151
  · exact B1222155
  · exact B1222159
  · exact B1222163
  · exact B1222167
  · exact B1222171
  · exact B1222175
  · exact B1222179
  · exact B1222183
  · exact B1222187
  · exact B1222191
  · exact B1222195
  · exact B1222199
  · exact B1222203
  · exact B1222207
  · exact B1222211
  · exact B1222215
  · exact B1222219
  · exact B1222223
  · exact B1222227
  · exact B1222231
  · exact B1222235
  · exact B1222239
  · exact B1222243
  · exact B1222247
  · exact B1222251
  · exact B1222255
  · exact B1222259
  · exact B1222263
  · exact B1222267
  · exact B1222271
  · exact B1222275
  · exact B1222279
  · exact B1222283
  · exact B1222287
  · exact B1222291
  · exact B1222295
  · exact B1222299
  · exact B1222303
  · exact B1222307
  · exact B1222311
  · exact B1222315
  · exact B1222319
  · exact B1222323
  · exact B1222327
  · exact B1222331
  · exact B1222335
  · exact B1222339
  · exact B1222343
  · exact B1222347
  · exact B1222351
  · exact B1222355
  · exact B1222359
  · exact B1222363
  · exact B1222367
  · exact B1222371
  · exact B1222375
  · exact B1222379
  · exact B1222383
  · exact B1222387
  · exact B1222391
  · exact B1222395
  · exact B1222399
  · exact B1222403
  · exact B1222407
  · exact B1222411
  · exact B1222415
  · exact B1222419
  · exact B1222423
  · exact B1222427
  · exact B1222431
  · exact B1222435
  · exact B1222439
  · exact B1222443
  · exact B1222447
  · exact B1222451
  · exact B1222455
  · exact B1222459
  · exact B1222463
  · exact B1222467
  · exact B1222471
  · exact B1222475
  · exact B1222479
  · exact B1222483
  · exact B1222487
  · exact B1222491
  · exact B1222495
  · exact B1222499
  · exact B1222503
  · exact B1222507
  · exact B1222511
  · exact B1222515
  · exact B1222519
  · exact B1222523
  · exact B1222527
  · exact B1222531
  · exact B1222535
  · exact B1222539
  · exact B1222543
  · exact B1222547
  · exact B1222551
  · exact B1222555
  · exact B1222559
  · exact B1222563
  · exact B1222567
  · exact B1222571
  · exact B1222575
  · exact B1222579
  · exact B1222583
  · exact B1222587
  · exact B1222591
  · exact B1222595
  · exact B1222599
  · exact B1222603
  · exact B1222607
  · exact B1222611
  · exact B1222615
  · exact B1222619
  · exact B1222623
  · exact B1222627
  · exact B1222631
  · exact B1222635
  · exact B1222639
  · exact B1222643
  · exact B1222647
  · exact B1222651
  · exact B1222655
  · exact B1222659
  · exact B1222663
  · exact B1222667
  · exact B1222671
  · exact B1222675
  · exact B1222679
  · exact B1222683
  · exact B1222687
  · exact B1222691
  · exact B1222695
  · exact B1222699
  · exact B1222703
  · exact B1222707
  · exact B1222711
  · exact B1222715
  · exact B1222719
  · exact B1222723
  · exact B1222727
  · exact B1222731
  · exact B1222735
  · exact B1222739
  · exact B1222743
  · exact B1222747
  · exact B1222751
  · exact B1222755
  · exact B1222759
  · exact B1222763
  · exact B1222767
  · exact B1222771
  · exact B1222775
  · exact B1222779
  · exact B1222783
  · exact B1222787
  · exact B1222791
  · exact B1222795
  · exact B1222799
  · exact B1222803
  · exact B1222807
  · exact B1222811
  · exact B1222815
  · exact B1222819
  · exact B1222823
  · exact B1222827
  · exact B1222831
  · exact B1222835
  · exact B1222839
  · exact B1222843
  · exact B1222847
  · exact B1222851
  · exact B1222855
  · exact B1222859
  · exact B1222863
  · exact B1222867
  · exact B1222871
  · exact B1222875
  · exact B1222879
  · exact B1222883
  · exact B1222887
  · exact B1222891
  · exact B1222895
  · exact B1222899
  · exact B1222903
  · exact B1222907
  · exact B1222911
  · exact B1222915
  · exact B1222919
  · exact B1222923
  · exact B1222927

theorem solution (m : ℕ) (hlo : 1220928 ≤ m) (hhi : m ≤ 1222928) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 305232 ≤ j := by omega
    have hj2 : j ≤ 305731 := by omega
    have hb : Blo 1220928 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
